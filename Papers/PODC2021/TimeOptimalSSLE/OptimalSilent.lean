import Papers.PODC2021.TimeOptimalSSLE.Model
import Mathlib.Order.Interval.Finset.Nat

/-!
# `Optimal-Silent-SSR` (Protocols 2–4): model, and the off-by-one in the recruitment guard

Section 4 of the paper: roles `Settled` (rank, children), `Unsettled` (errorcount) and
`Resetting` (leader bit, resetcount, delaytimer), with the reset subprotocol `Propagate-Reset`
(Protocol 2) and the binary-tree rank assignment (lines 8–12 of Protocol 3): a settled agent of
rank `r` with `c < 2` children recruits an unsettled agent as its child of rank `2r + c`.

## Interpretation of the pseudocode (see `differencies.md`)

* An interaction `(a, b)` (initiator, responder) applies, in this order: lines 1–4
  (`Propagate-Reset` and the leader election `L, L → L, F`), lines 5–7 (rank collision),
  lines 8–12 for `(i, j) = (a, b)` then `(b, a)`, lines 13–18 (errorcount countdown).
* `Propagate-Reset(a, b)` is written for a Resetting agent `a`; if only the responder is
  Resetting we call it with the two agents swapped.
* An agent brought into the Resetting role (line 2 of Protocol 2) gets `leader = L` ("all agents
  set themselves to L upon entering the Resetting role", Section 4).
* "`resetcount` just became 0" means: positive at the start of the interaction, `0` now. An agent
  brought in by line 2 therefore decrements its fresh `delaytimer = Dmax` (line 9).
* Line 10 ("`b.role ≠ Resetting`") is read as "the *other* agent is not Resetting".
* Decrements are truncated at `0`; triggered agents get `delaytimer = Dmax` (unused while
  propagating).

## The off-by-one

Line 9 of Protocol 3 only recruits when `2 · i.rank + i.children < n`. Since new ranks are only
created by `Reset` (rank `1`) and by recruitment (rank `2 · rank + children`), **no agent can ever
obtain rank `n`** unless it already had it: from any configuration without a settled agent of rank
`n` (e.g. all agents `Unsettled`) a correctly ranked configuration is never reachable
(`asWritten_never_ranked`), so the protocol as printed does not solve SSR for any `n ≥ 2`
(`asWritten_not_selfStabilizes`). Figure 1 (where rank 12 is assigned for `n = 12`) and the text
show that `2 · i.rank + i.children ≤ n` is intended; `Params.fixed = true` selects this guard.
-/

open Cslib.PopulationProtocol

set_option linter.unusedSectionVars false

namespace TimeOptimalSSLE.OptimalSilent

/-- Agent states of `Optimal-Silent-SSR`, by role. -/
inductive St
  /-- `Settled` with `rank ∈ {1, …, n}` and `children ∈ {0, 1, 2}`. -/
  | settled (rank children : ℕ)
  /-- `Unsettled` with `errorcount ∈ {0, …, Emax}`. -/
  | unsettled (errorcount : ℕ)
  /-- `Resetting` with `leader ∈ {L = true, F = false}`, `resetcount ∈ {0, …, Rmax}` and
  `delaytimer ∈ {0, …, Dmax}`. -/
  | resetting (leader : Bool) (resetcount delaytimer : ℕ)
  deriving DecidableEq

/-- Parameters: population size `n`, the constants `Rmax`, `Dmax`, `Emax`, and the variant of the
recruitment guard (`fixed = false`: `2·rank + children < n` as printed; `fixed = true`:
`2·rank + children ≤ n`). -/
structure Params where
  n : ℕ
  Rmax : ℕ
  Dmax : ℕ
  Emax : ℕ
  fixed : Bool

namespace St

/-- Whether the role is `Resetting`. -/
def isResetting : St → Bool
  | resetting .. => true
  | _ => false

/-- `resetcount`, with `0` for computing agents (Observation 3.1). -/
def rc : St → ℕ
  | resetting _ r _ => r
  | _ => 0

/-- The rank output (`0` = no rank). -/
def rankOut : St → ℕ
  | settled r _ => r
  | _ => 0

end St

open St

variable (p : Params)

/-- Protocol 4, `Reset(a)`. -/
def reset : St → St
  | resetting true _ _ => settled 1 0
  | resetting false _ _ => unsettled p.Emax
  | s => s

/-- Lines 5–11 of Protocol 2 for one agent: dormant agents set or decrement `delaytimer` and wake
up (`Reset`) when it reaches `0` or when the other agent is computing. -/
def dormantStep (wasPos otherComputing : Bool) : St → St
  | resetting l 0 dt =>
    let dt' := if wasPos then p.Dmax else dt - 1
    if dt' = 0 ∨ otherComputing = true then reset p (resetting l 0 dt') else resetting l 0 dt'
  | s => s

/-- Protocol 2, `Propagate-Reset(a, b)` for a Resetting agent `a`. -/
def propagateReset (a b : St) : St × St :=
  match a with
  | resetting la rca dta =>
    -- lines 1–2: bring `b` into the Resetting role
    let b1 := if 0 < rca ∧ b.isResetting = false then resetting true 0 p.Dmax else b
    -- lines 3–4: `resetcount ← max(a.resetcount - 1, b.resetcount - 1, 0)`
    let x2 : St × St := match b1 with
      | resetting lb rcb dtb =>
        (resetting la (max (rca - 1) (rcb - 1)) dta, resetting lb (max (rca - 1) (rcb - 1)) dtb)
      | _ => (a, b1)
    -- lines 5–11, first for `a`, then for `b`
    let a3 := dormantStep p (decide (0 < rca)) (!x2.2.isResetting) x2.1
    let b3 := dormantStep p (b.isResetting && decide (0 < b.rc)) (!a3.isResetting) x2.2
    (a3, b3)
  | _ => (a, b)

/-- Lines 3–4 of Protocol 3: `L, L → L, F` among Resetting agents. -/
def leaderElect : St × St → St × St
  | (resetting true ra da, resetting true rb db) => (resetting true ra da, resetting false rb db)
  | x => x

/-- A freshly triggered agent (lines 6–7 and 17–18 of Protocol 3). -/
def trig : St := resetting true p.Rmax p.Dmax

/-- Lines 5–7 of Protocol 3: a rank collision triggers a reset. -/
def collide : St × St → St × St
  | (settled ra ca, settled rb cb) =>
    if ra = rb then (trig p, trig p) else (settled ra ca, settled rb cb)
  | x => x

/-- The recruitment guard of line 9 (as printed: `<`; fixed: `≤`). -/
def guard (r c : ℕ) : Prop := if p.fixed then 2 * r + c ≤ p.n else 2 * r + c < p.n

instance (r c : ℕ) : Decidable (guard p r c) := by unfold guard; infer_instance

/-- Lines 9–12 of Protocol 3 for one ordered pair `(i, j)`. -/
def recruit : St → St → St × St
  | settled r c, unsettled e =>
    if c < 2 ∧ guard p r c then (settled r (c + 1), settled (2 * r + c) 0)
    else (settled r c, unsettled e)
  | i, j => (i, j)

/-- Decrement of `errorcount` (line 15). -/
def dec : St → St
  | unsettled e => unsettled (e - 1)
  | s => s

/-- `errorcount = 0` (line 16). -/
def expired : St → Bool
  | unsettled 0 => true
  | _ => false

/-- Lines 13–18 of Protocol 3. -/
def countdown (x : St × St) : St × St :=
  if expired (dec x.1) then (trig p, trig p)
  else if expired (dec x.2) then (trig p, trig p)
  else (dec x.1, dec x.2)

/-- One interaction of Protocol 3 (initiator `a`, responder `b`). -/
def δ (a b : St) : St × St :=
  let x1 : St × St :=
    if a.isResetting then propagateReset p a b
    else if b.isResetting then (propagateReset p b a).swap
    else (a, b)
  let x3 := collide p (leaderElect x1)
  let x4 := recruit p x3.1 x3.2
  let x5 := (recruit p x4.2 x4.1).swap
  countdown p x5

/-- `Optimal-Silent-SSR` as a (deterministic) population protocol. -/
def protocol : Protocol St := ⟨δ p⟩

variable {A : Type*} [DecidableEq A]

/-- Correctly ranked configurations: every agent is settled with a rank in `{1, …, n}`, and the
ranks are pairwise distinct (with `n` agents: a bijection onto `{1, …, n}`). -/
def Ranked (C : Config A St) : Prop :=
  (∀ a, 1 ≤ (C a).rankOut ∧ (C a).rankOut ≤ p.n) ∧ Function.Injective fun a => (C a).rankOut

/-! ### Correctly ranked configurations are silent -/

lemma δ_settled_ne {r r' c c' : ℕ} (h : r ≠ r') :
    δ p (settled r c) (settled r' c') = (settled r c, settled r' c') := by
  simp [δ, isResetting, leaderElect, collide, h, recruit, countdown, dec, expired]

lemma rankOut_eq_settled {s : St} (h : 1 ≤ s.rankOut) : ∃ c, s = settled s.rankOut c := by
  cases s with
  | settled r c => exact ⟨c, rfl⟩
  | unsettled e => simp [rankOut] at h
  | resetting l r d => simp [rankOut] at h

lemma Ranked.interact {C : Config A St} (hC : Ranked p C) {a b : A} (hab : a ≠ b) :
    (protocol p).interact C a b = C := by
  obtain ⟨ca, hca⟩ := rankOut_eq_settled (hC.1 a).1
  obtain ⟨cb, hcb⟩ := rankOut_eq_settled (hC.1 b).1
  have hne : (C a).rankOut ≠ (C b).rankOut := fun h => hab (hC.2 h)
  have hδ : (protocol p).δ (C a) (C b) = (C a, C b) := by
    simp only [protocol]; rw [hca, hcb, δ_settled_ne p hne]
  funext x
  by_cases hxa : x = a
  · subst hxa; rw [Protocol.interact_self_left, hδ]
  · by_cases hxb : x = b
    · subst hxb; rw [Protocol.interact_self_right _ _ hab, hδ]
    · rw [Protocol.interact_other _ _ hxa hxb]

/-- Correctly ranked configurations are silent (both variants). -/
theorem Ranked.reachable {C D : Config A St} (hC : Ranked p C) (h : (protocol p).Reachable C D) :
    D = C := by
  induction h with
  | refl => rfl
  | tail _ hst ih =>
    subst ih
    obtain ⟨a, b, hab, rfl⟩ := hst
    exact hC.interact p hab

/-! ### The printed guard: rank `n` is never created -/

/-- The state is not a settled agent of rank `n`. -/
def NoTop (s : St) : Prop := ∀ c, s ≠ settled p.n c

lemma noTop_trig : NoTop p (trig p) := by intro c; simp [trig]

lemma noTop_reset (hn : 2 ≤ p.n) (s : St) (hs : NoTop p s) : NoTop p (reset p s) := by
  intro c
  cases s with
  | resetting l r d => cases l <;> simp [reset]; omega
  | settled r c' => exact hs c
  | unsettled e => exact hs c

lemma noTop_dormantStep (hn : 2 ≤ p.n) (w o : Bool) (s : St) (hs : NoTop p s) :
    NoTop p (dormantStep p w o s) := by
  cases s with
  | resetting l r d =>
    cases r with
    | zero =>
      simp only [dormantStep]
      split_ifs <;> first
        | exact noTop_reset p hn _ (by intro c; simp)
        | (intro c; simp)
    | succ r => exact hs
  | settled r c' => exact hs
  | unsettled e => exact hs

lemma noTop_propagateReset (hn : 2 ≤ p.n) {a b : St} (ha : NoTop p a) (hb : NoTop p b) :
    NoTop p (propagateReset p a b).1 ∧ NoTop p (propagateReset p a b).2 := by
  cases a with
  | resetting la rca dta =>
    have key : ∀ x : St × St, NoTop p x.1 → NoTop p x.2 →
        NoTop p (dormantStep p (decide (0 < rca)) (!x.2.isResetting) x.1) ∧
        NoTop p (dormantStep p (b.isResetting && decide (0 < b.rc))
          (!(dormantStep p (decide (0 < rca)) (!x.2.isResetting) x.1).isResetting) x.2) :=
      fun x h1 h2 => ⟨noTop_dormantStep p hn _ _ _ h1, noTop_dormantStep p hn _ _ _ h2⟩
    refine key _ ?_ ?_
    · by_cases h : 0 < rca ∧ b.isResetting = false
      · simp only [h, and_self, ite_true]; intro c; simp
      · simp only [h, ite_false]
        split
        · intro c; simp
        · exact ha
    · by_cases h : 0 < rca ∧ b.isResetting = false
      · simp only [h, and_self, ite_true]; intro c; simp
      · simp only [h, ite_false]
        split
        · intro c; simp
        · exact hb
  | settled r c => exact ⟨ha, hb⟩
  | unsettled e => exact ⟨ha, hb⟩


lemma noTop_leaderElect {x : St × St} (h1 : NoTop p x.1) (h2 : NoTop p x.2) :
    NoTop p (leaderElect x).1 ∧ NoTop p (leaderElect x).2 := by
  rcases x with ⟨a, b⟩
  cases a with
  | resetting la ra da =>
    cases b with
    | resetting lb rb db =>
      cases la <;> cases lb <;> simp only [leaderElect] <;>
        exact ⟨fun c => by simp, fun c => by simp⟩
    | _ => simp only [leaderElect]; exact ⟨h1, h2⟩
  | _ => simp only [leaderElect]; exact ⟨h1, h2⟩

lemma noTop_collide {x : St × St} (h1 : NoTop p x.1) (h2 : NoTop p x.2) :
    NoTop p (collide p x).1 ∧ NoTop p (collide p x).2 := by
  rcases x with ⟨a, b⟩
  cases a with
  | settled ra ca =>
    cases b with
    | settled rb cb =>
      simp only [collide]
      split_ifs
      · exact ⟨noTop_trig p, noTop_trig p⟩
      · exact ⟨h1, h2⟩
    | _ => exact ⟨h1, h2⟩
  | _ => exact ⟨h1, h2⟩

lemma noTop_recruit (hp : p.fixed = false) {i j : St} (h1 : NoTop p i) (h2 : NoTop p j) :
    NoTop p (recruit p i j).1 ∧ NoTop p (recruit p i j).2 := by
  cases i with
  | settled r c =>
    cases j with
    | unsettled e =>
      simp only [recruit]
      split_ifs with h
      · refine ⟨fun c' hc => h1 c (by simp at hc ⊢; exact hc.1), fun c' hc => ?_⟩
        simp only [settled.injEq] at hc
        have := h.2
        simp only [guard, hp, Bool.false_eq_true, ite_false] at this
        omega
      · exact ⟨h1, h2⟩
    | _ => exact ⟨h1, h2⟩
  | _ => exact ⟨h1, h2⟩

lemma noTop_dec {s : St} (h : NoTop p s) : NoTop p (dec s) := by
  cases s with
  | unsettled e => intro c; simp [dec]
  | _ => exact h

lemma noTop_countdown {x : St × St} (h1 : NoTop p x.1) (h2 : NoTop p x.2) :
    NoTop p (countdown p x).1 ∧ NoTop p (countdown p x).2 := by
  simp only [countdown]
  split_ifs
  · exact ⟨noTop_trig p, noTop_trig p⟩
  · exact ⟨noTop_trig p, noTop_trig p⟩
  · exact ⟨noTop_dec p h1, noTop_dec p h2⟩

lemma noTop_δ (hn : 2 ≤ p.n) (hp : p.fixed = false) {a b : St} (ha : NoTop p a)
    (hb : NoTop p b) : NoTop p (δ p a b).1 ∧ NoTop p (δ p a b).2 := by
  have h1 : NoTop p (if a.isResetting then propagateReset p a b
      else if b.isResetting then (propagateReset p b a).swap else (a, b)).1 ∧
      NoTop p (if a.isResetting then propagateReset p a b
      else if b.isResetting then (propagateReset p b a).swap else (a, b)).2 := by
    split_ifs
    · exact noTop_propagateReset p hn ha hb
    · exact (noTop_propagateReset p hn hb ha).symm
    · exact ⟨ha, hb⟩
  obtain ⟨h2, h2'⟩ := noTop_leaderElect p h1.1 h1.2
  obtain ⟨h3, h3'⟩ := noTop_collide p h2 h2'
  obtain ⟨h4, h4'⟩ := noTop_recruit p hp h3 h3'
  obtain ⟨h5, h5'⟩ := noTop_recruit p hp h4' h4
  exact noTop_countdown p h5' h5

/-- **The printed protocol never creates rank `n`.** From a configuration with no settled agent
of rank `n`, no reachable configuration has one. -/
theorem asWritten_noTop_reachable (hn : 2 ≤ p.n) (hp : p.fixed = false) {C D : Config A St}
    (hC : ∀ a, NoTop p (C a)) (h : (protocol p).Reachable C D) : ∀ a, NoTop p (D a) :=
  Protocol.ClosedStates.reachable (P := protocol p) (H := {s | NoTop p s})
    (fun _ ha _ hb => noTop_δ p hn hp ha hb) hC h

/-- With `n` agents, a correctly ranked configuration contains an agent of rank `n`. -/
lemma Ranked.exists_top [Fintype A] (hA : Fintype.card A = p.n) (hn : 1 ≤ p.n) {C : Config A St}
    (hC : Ranked p C) : ∃ a, ¬ NoTop p (C a) := by
  classical
  have himg : Finset.univ.image (fun a => (C a).rankOut) = Finset.Icc 1 p.n := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hr
      obtain ⟨a, rfl⟩ := hr
      simpa using hC.1 a
    · rw [Finset.card_image_of_injective _ hC.2, Nat.card_Icc, Finset.card_univ, hA]; omega
  have : p.n ∈ Finset.univ.image (fun a => (C a).rankOut) := by rw [himg]; simp; omega
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at this
  obtain ⟨a, ha⟩ := this
  obtain ⟨c, hc⟩ := rankOut_eq_settled (s := C a) (by rw [ha]; omega)
  exact ⟨a, fun h => h c (by rw [hc, ha])⟩

/-- **Optimal-Silent-SSR as printed is incorrect.** For `n ≥ 2` and any parameters, from any
configuration without a settled agent of rank `n` (e.g. all agents `Unsettled`), no correctly
ranked configuration is ever reachable; hence it is reached with probability `0`. -/
theorem asWritten_never_ranked [Fintype A] (hA : Fintype.card A = p.n) (hn : 2 ≤ p.n)
    (hp : p.fixed = false) {C D : Config A St} (hC : ∀ a, NoTop p (C a))
    (h : (protocol p).Reachable C D) : ¬ Ranked p D := by
  intro hD
  obtain ⟨a, ha⟩ := hD.exists_top p hA (by omega)
  exact ha (asWritten_noTop_reachable p hn hp hC h a)

/-- In particular, `Optimal-Silent-SSR` with the printed guard does not solve self-stabilizing
ranking: from the all-`Unsettled` configuration, no ranked configuration is reachable. -/
theorem asWritten_not_selfStabilizes [Fintype A] (hA : Fintype.card A = p.n) (hn : 2 ≤ p.n)
    (hp : p.fixed = false) (e : ℕ) :
    ¬ ∃ D, (protocol p).Reachable (fun _ : A => unsettled e) D ∧ Ranked p D :=
  fun ⟨_, hD, hR⟩ => asWritten_never_ranked p hA hn hp (fun _ c => by simp) hD hR

end TimeOptimalSSLE.OptimalSilent
