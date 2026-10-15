import Papers.PODC2026.RankingOpinions.Circles
import Cslib.Computability.Distributed.PopulationProtocols.Schedules
import Cslib.Computability.Distributed.PopulationProtocols.Eventually
import Mathlib.Data.Fin.VecNotation

/-!
# Reporting ties (Section 4.1): `Circles_TieReport`

Breitkopf, Dallot, El-Hayek, Schmid, PODC 2026, Section 4.1 and Appendix 8.3 (Theorem 4.1).

Each agent additionally stores `tie_state ∈ {no_tie, tie, tie_spreader}` (initially `no_tie`),
updated after the Circles transition by three rules:
1. (tie detection) an agent `⟨i|i⟩` that decays into `⟨i|j⟩`, `i ≠ j`, goes to `tie_spreader`;
2. (tie spreading) an agent at `tie_spreader` sets to `tie` any encountered agent `⟨i|j⟩`, `i ≠ j`;
3. (tie correction) an agent `⟨i|i⟩` sets any encountered agent to `no_tie`.
Output: `out` if at `no_tie`, "tie" otherwise.

We parametrize two points:
* `onlyNoTie`: whether rule 2 only affects agents at `no_tie` (the paper's literal text: any agent;
  the paper's proof, "will set all other agents at no_tie to tie", suggests only `no_tie` ones);
* `selfReset`: our fix — an agent of the form `⟨i|i⟩` also resets *itself* to `no_tie`.

Results:
* `tieReport_counterexample_noTie`: for the paper's protocol (`selfReset = false`, either reading of
  rule 2) there is a weakly fair execution with a unique majority color in which an agent outputs
  "tie" forever (4 agents, 3 colors, input `0,0,1,2`). **Theorem 4.1 is false.**
* `tieReport_counterexample_tie` (ambiguity-dependent): with the literal rule 2 (`onlyNoTie = false`)
  *and* rule 2 applied in both directions simultaneously (each agent's update reads the partner's
  status after rule 1, before the partner's own rule-2 update), also the tie case fails (4 agents,
  2 colors, input `0,0,1,1`; two spreaders cancel each other). If one direction is applied first,
  no tie-case failure is found by model checking.
* `tieReport_fixed_correct`: with both `onlyNoTie` and `selfReset`, Theorem 4.1 holds.
-/

set_option linter.unusedSectionVars false

namespace RankingOpinions

open Finset Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

variable {k : ℕ}

/-- The values of `tie_state`. -/
inductive TS
  | noTie
  | tie
  | spreader
  deriving DecidableEq, Repr

instance : Fintype TS := ⟨{TS.noTie, TS.tie, TS.spreader}, by intro x; cases x <;> simp⟩

lemma card_TS : Fintype.card TS = 3 := rfl

/-- Variants of the tie-report rules (see the module docstring). -/
structure TRVariant where
  onlyNoTie : Bool
  selfReset : Bool

/-- Final `tie_state` of one agent after an interaction, given: whether it was diagonal before
(`dpx`) and is diagonal after the Circles transition (`dx`), its partner's analogous data, and the
two old tie states. (The rules are applied in order 1, 2, 3, conditions read the current values.) -/
def tsUpd (v : TRVariant) (dpx dx dpy dy : Bool) (tx ty : TS) : TS :=
  let tx1 := if dpx && !dx then TS.spreader else tx
  let ty1 := if dpy && !dy then TS.spreader else ty
  let tx2 := if ty1 = TS.spreader ∧ dx = false ∧ (v.onlyNoTie = false ∨ tx1 = TS.noTie)
    then TS.tie else tx1
  let tx3 := if dy then TS.noTie else tx2
  if v.selfReset && dx then TS.noTie else tx3

/-- States of `Circles_TieReport`: a Circles state and a tie state (`3k³` states). -/
abbrev TRState (k : ℕ) := CState k × TS

theorem card_TRState : Fintype.card (TRState k) = 3 * k ^ 3 := by
  rw [Fintype.card_prod, card_CState, card_TS, mul_comm]

/-- Is a braket diagonal (`⟨i|i⟩`)? -/
def isDiag (e : Braket k) : Bool := decide (e.1 = e.2)

/-- Transition function of `Circles_TieReport`. -/
def trδ (v : TRVariant) (p q : TRState k) : TRState k × TRState k :=
  let r := circlesδ p.1 q.1
  ((r.1, tsUpd v (isDiag p.1.1) (isDiag r.1.1) (isDiag q.1.1) (isDiag r.2.1) p.2 q.2),
   (r.2, tsUpd v (isDiag q.1.1) (isDiag r.2.1) (isDiag p.1.1) (isDiag r.1.1) q.2 p.2))

/-- The protocol `Circles_TieReport` (variant `v`). -/
def tieReport (k : ℕ) (v : TRVariant) : Protocol (TRState k) := ⟨trδ v⟩

/-- The paper's version (with the literal reading of rule 2). -/
def paperV : TRVariant := ⟨false, false⟩
/-- The fixed version. -/
def fixedV : TRVariant := ⟨true, true⟩

/-- Output: `some out` at `no_tie`, `none` ("tie") otherwise. -/
def trOutput (s : TRState k) : Option (Fin k) := if s.2 = TS.noTie then some s.1.2 else none

def trInit {A : Type*} (input : A → Fin k) : Config A (TRState k) :=
  fun a => (circlesInit input a, TS.noTie)

def trToCircles (v : TRVariant) : (tieReport k v).Hom (circles k) where
  f := Prod.fst
  map_fst _ _ := rfl
  map_snd _ _ := rfl

/-- Interactions in a configuration whose brakets `B` are stable: brakets do not change and the
tie states are updated by `tsUpd` with "diagonal before = diagonal after". -/
lemma tr_interact_stable {v : TRVariant} {A : Type*} [DecidableEq A] {B : Config A (Braket k)}
    (hB : Stable B) {C : Config A (TRState k)} (hC : ∀ y, (C y).1.1 = B y) {a b : A}
    (hab : a ≠ b) :
    (∀ y, ((tieReport k v).interact C a b y).1.1 = B y) ∧
    ((tieReport k v).interact C a b a).2 =
      tsUpd v (isDiag (B a)) (isDiag (B a)) (isDiag (B b)) (isDiag (B b)) (C a).2 (C b).2 ∧
    ((tieReport k v).interact C a b b).2 =
      tsUpd v (isDiag (B b)) (isDiag (B b)) (isDiag (B a)) (isDiag (B a)) (C b).2 (C a).2 ∧
    (∀ y, y ≠ a → y ≠ b → (tieReport k v).interact C a b y = C y) := by
  have hex : exch (C a).1.1 (C b).1.1 = (B a, B b) := by
    rw [exch, if_neg (by rw [hC, hC]; exact hB a b hab), hC, hC]
  have h1 : (circlesδ (C a).1 (C b).1).1.1 = B a := by
    simp only [circlesδ, hex]; split_ifs <;> rfl
  have h2 : (circlesδ (C a).1 (C b).1).2.1 = B b := by
    simp only [circlesδ, hex]; split_ifs <;> rfl
  refine ⟨fun y => ?_, ?_, ?_, fun y hya hyb => Protocol.interact_other _ _ hya hyb⟩
  · by_cases hya : y = a
    · subst hya; simp only [Protocol.interact_self_left, tieReport, trδ, h1]
    · by_cases hyb : y = b
      · subst hyb; simp only [Protocol.interact_self_right _ _ hab, tieReport, trδ, h2]
      · rw [Protocol.interact_other _ _ hya hyb, hC]
  · simp only [Protocol.interact_self_left, tieReport, trδ, h1, h2, hC]
  · simp only [Protocol.interact_self_right _ _ hab, tieReport, trδ, h1, h2, hC]

/-! ## The counterexamples -/

section Counterexample

/-- Input of the first counterexample: agents `0,1,2,3` with colors `0,0,1,2` (`k = 3`). -/
def cex1Input : Fin 4 → Fin 3 := ![0, 0, 1, 2]

/-- `0` is the unique majority color. -/
lemma cex1_majority : IsMajority cex1Input 0 := by unfold IsMajority inputCount; decide

/-- The schedule: `(1,2)`, `(0,3)`, `(0,2)`, then round robin over all ordered pairs. -/
def cex1Prefix : List (Fin 4 × Fin 4) := [(1, 2), (0, 3), (0, 2)]

def allPairs4 : List (Fin 4 × Fin 4) :=
  [(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2)]

def cexSched (pre : List (Fin 4 × Fin 4)) (t : ℕ) : Fin 4 × Fin 4 :=
  if h : t < pre.length then pre[t] else allPairs4[(t - pre.length) % 12]'(Nat.mod_lt _ (by decide))

lemma cexSched_ne (pre : List (Fin 4 × Fin 4)) (hpre : ∀ p ∈ pre, p.1 ≠ p.2) (t : ℕ) :
    (cexSched pre t).1 ≠ (cexSched pre t).2 := by
  unfold cexSched
  split_ifs with h
  · exact hpre _ (List.getElem_mem h)
  · have : ∀ i : Fin 12, (allPairs4[i.val]).1 ≠ (allPairs4[i.val]).2 := by decide
    exact this ⟨_, Nat.mod_lt _ (by decide)⟩

lemma cexSched_fair (v : TRVariant) (pre : List (Fin 4 × Fin 4)) (hpre : ∀ p ∈ pre, p.1 ≠ p.2)
    (C0 : Config (Fin 4) (TRState k)) :
    (Execution.ofSched (tieReport k v) C0 (cexSched pre) (cexSched_ne pre hpre)).WeaklyFair := by
  apply Execution.weaklyFair_of_cycle _ allPairs4 (by decide) pre.length
  · intro t
    show cexSched pre (pre.length + t) = _
    simp [cexSched]; rfl
  · decide

/-- The braket configuration reached after the prefix of the first counterexample. -/
def cex1Brakets : Config (Fin 4) (Braket 3) := ![(0, 0), (0, 1), (1, 2), (2, 0)]

lemma cex1_stable : Stable cex1Brakets := by
  unfold Stable; decide

/-- A configuration with stable brakets in which agent `x` is the only diagonal agent and is a
`tie_spreader` or at `tie`: in the paper's protocol (`selfReset = false`) agent `x` never
returns to `no_tie`. -/
lemma spreader_stays {v : TRVariant} (hv : v.selfReset = false) {A : Type*} [DecidableEq A]
    {B : Config A (Braket k)} (hB : Stable B) {x : A} (hx : isDiag (B x) = true)
    (hother : ∀ y, y ≠ x → isDiag (B y) = false) :
    (tieReport k v).Closed fun C => (∀ y, (C y).1.1 = B y) ∧ (C x).2 ≠ TS.noTie := by
  rintro C C' ⟨hC1, hC2⟩ ⟨a, b, hab, rfl⟩
  refine ⟨fun y => (tr_interact_stable hB hC1 hab).1 y, ?_⟩
  obtain ⟨-, ha, hb, ho⟩ := tr_interact_stable (v := v) hB hC1 hab
  have key : ∀ (w : TRVariant), w.selfReset = false → ∀ tx ty, tx ≠ TS.noTie →
      tsUpd w true true false false tx ty ≠ TS.noTie := by
    rintro ⟨o, s⟩ hs tx ty; simp only at hs; subst hs; cases o <;> cases tx <;> cases ty <;> decide
  by_cases hxa : x = a
  · subst hxa; rw [ha, hx, hother b (Ne.symm hab)]; exact key v hv _ _ hC2
  · by_cases hxb : x = b
    · subst hxb; rw [hb, hx, hother a hab]; exact key v hv _ _ hC2
    · rw [ho x hxa hxb]; exact hC2

lemma cex1_reach (o : Bool) :
    (∀ y, ((tieReport 3 ⟨o, false⟩).runSched (trInit cex1Input) (cexSched cex1Prefix) 3 y).1.1 =
      cex1Brakets y) ∧
    ((tieReport 3 ⟨o, false⟩).runSched (trInit cex1Input) (cexSched cex1Prefix) 3 0).2 ≠
      TS.noTie := by
  cases o <;> decide

/-- **Counterexample to Theorem 4.1 (no-tie case).** In the paper's `Circles_TieReport`
(`selfReset = false`, either reading of rule 2), with 4 agents of colors `0,0,1,2` (`k = 3`; color
`0` is the unique majority) there is a weakly fair execution in which agent `0` outputs "tie"
(`none`) at every time `t ≥ 3`. After the ket exchanges `(1,2)`, `(0,3)`, `(0,2)` the brakets are
stable, agent `0` is the unique agent of the form `⟨i|i⟩` and is not at `no_tie` (it is a
`tie_spreader` under the `onlyNoTie` reading, at `tie` under the literal one); only a *different*
diagonal agent could reset it. -/
theorem tieReport_counterexample_noTie (v : TRVariant) (hv : v.selfReset = false) :
    ∃ E : (tieReport 3 v).Execution (Fin 4), E.config 0 = trInit cex1Input ∧ E.WeaklyFair ∧
      IsMajority cex1Input 0 ∧ ∀ t ≥ 3, trOutput (E.config t 0) = none := by
  have hpre : ∀ p ∈ cex1Prefix, p.1 ≠ p.2 := by decide
  set E := Execution.ofSched (tieReport 3 v) (trInit cex1Input) (cexSched cex1Prefix)
    (cexSched_ne _ hpre)
  refine ⟨E, rfl, cexSched_fair v _ hpre _, cex1_majority, ?_⟩
  have hcl := spreader_stays (k := 3) (v := v) hv cex1_stable (x := 0) (by decide)
    (by decide)
  have h3 : (∀ y, (E.config 3 y).1.1 = cex1Brakets y) ∧ (E.config 3 0).2 ≠ TS.noTie := by
    obtain ⟨o, s⟩ := v
    simp only at hv; subst hv
    exact cex1_reach o
  intro t ht
  have := (hcl.execution E h3 t ht).2
  simp [trOutput, this]

/-- In a configuration with stable brakets, no diagonal agent and no `tie_spreader`, nothing
changes any more. -/
lemma frozen_closed {v : TRVariant} {A : Type*} [DecidableEq A] {B : Config A (Braket k)}
    (hB : Stable B) (hnd : ∀ y, isDiag (B y) = false) (τ : A → TS)
    (hτ : ∀ y, τ y ≠ TS.spreader) :
    (tieReport k v).Closed fun C => (∀ y, (C y).1.1 = B y) ∧ ∀ y, (C y).2 = τ y := by
  rintro C C' ⟨hC1, hC2⟩ ⟨a, b, hab, rfl⟩
  refine ⟨fun y => (tr_interact_stable hB hC1 hab).1 y, ?_⟩
  obtain ⟨-, ha, hb, ho⟩ := tr_interact_stable (v := v) hB hC1 hab
  have key : ∀ (w : TRVariant) tx ty, ty ≠ TS.spreader →
      tsUpd w false false false false tx ty = tx := by
    rintro ⟨o, s⟩ tx ty hty; cases o <;> cases s <;> cases tx <;> cases ty <;> simp_all <;> decide
  intro y
  by_cases hya : y = a
  · subst hya; rw [ha, hnd, hnd, hC2, hC2]; exact key v _ _ (hτ b)
  · by_cases hyb : y = b
    · subst hyb; rw [hb, hnd, hnd, hC2, hC2]; exact key v _ _ (hτ a)
    · rw [ho y hya hyb, hC2]

/-- Input of the second counterexample: colors `0,0,1,1` (`k = 2`), a tie. -/
def cex2Input : Fin 4 → Fin 2 := ![0, 0, 1, 1]

lemma cex2_tie : ¬ ∃ μ, IsMajority cex2Input μ := by unfold IsMajority inputCount; decide

def cex2Prefix : List (Fin 4 × Fin 4) := [(0, 2), (0, 1), (1, 2), (1, 3)]

def cex2Brakets : Config (Fin 4) (Braket 2) := ![(0, 1), (0, 1), (1, 0), (1, 0)]

def cex2TS : Fin 4 → TS := ![TS.noTie, TS.tie, TS.noTie, TS.tie]

lemma cex2_reach (s : Bool) :
    (∀ y, ((tieReport 2 ⟨false, s⟩).runSched (trInit cex2Input) (cexSched cex2Prefix) 4 y).1.1 =
      cex2Brakets y) ∧
    ∀ y, ((tieReport 2 ⟨false, s⟩).runSched (trInit cex2Input) (cexSched cex2Prefix) 4 y).2 =
      cex2TS y := by
  cases s <;> decide

/-- **Counterexample to Theorem 4.1 (tie case) — ambiguity-dependent.** Valid only for the literal
reading of rule 2 together with *simultaneous* application of rule 2 in both directions (`tsUpd`:
`tx2` reads the partner's `ty1`); with one direction applied first the tie case appears correct.
For the literal reading of rule 2 (a spreader
sets *every* non-diagonal agent, including other spreaders, to `tie`): with 4 agents of colors
`0,0,1,1` (a tie) there is a weakly fair execution in which agent `0` outputs a color (not "tie")
at every time `t ≥ 4`: two spreaders meet and turn each other into `tie`, after which no spreader
and no diagonal agent is left. -/
theorem tieReport_counterexample_tie (v : TRVariant) (hv : v.onlyNoTie = false) :
    ∃ E : (tieReport 2 v).Execution (Fin 4), E.config 0 = trInit cex2Input ∧ E.WeaklyFair ∧
      (¬ ∃ μ, IsMajority cex2Input μ) ∧ ∀ t ≥ 4, trOutput (E.config t 0) ≠ none := by
  have hpre : ∀ p ∈ cex2Prefix, p.1 ≠ p.2 := by decide
  set E := Execution.ofSched (tieReport 2 v) (trInit cex2Input) (cexSched cex2Prefix)
    (cexSched_ne _ hpre)
  refine ⟨E, rfl, cexSched_fair v _ hpre _, cex2_tie, ?_⟩
  have hcl := frozen_closed (k := 2) (v := v) (B := cex2Brakets) (by unfold Stable; decide)
    (by decide) cex2TS (by decide)
  have h4 : (∀ y, (E.config 4 y).1.1 = cex2Brakets y) ∧ ∀ y, (E.config 4 y).2 = cex2TS y := by
    obtain ⟨o, s⟩ := v
    simp only at hv; subst hv
    exact cex2_reach s
  intro t ht
  have := (hcl.execution E h4 t ht).2 0
  simp [trOutput, this, cex2TS]

end Counterexample

end RankingOpinions

/-! ## Correctness of the fixed protocol -/

namespace RankingOpinions

open Finset Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

variable {k : ℕ} {A : Type*} [DecidableEq A] [Fintype A]

/-- General description of one interaction of `Circles_TieReport`. -/
lemma tr_interact (v : TRVariant) (C : Config A (TRState k)) {a b : A} (hab : a ≠ b) :
    let C' := (tieReport k v).interact C a b
    C' a = ((circlesδ (C a).1 (C b).1).1, tsUpd v (isDiag (C a).1.1) (isDiag (C' a).1.1)
      (isDiag (C b).1.1) (isDiag (C' b).1.1) (C a).2 (C b).2) ∧
    C' b = ((circlesδ (C a).1 (C b).1).2, tsUpd v (isDiag (C b).1.1) (isDiag (C' b).1.1)
      (isDiag (C a).1.1) (isDiag (C' a).1.1) (C b).2 (C a).2) ∧
    ∀ y, y ≠ a → y ≠ b → C' y = C y := by
  refine ⟨?_, ?_, fun y hya hyb => Protocol.interact_other _ _ hya hyb⟩
  · simp only [Protocol.interact_self_left, Protocol.interact_self_right _ _ hab, tieReport, trδ]
  · simp only [Protocol.interact_self_left, Protocol.interact_self_right _ _ hab, tieReport, trδ]

/-- The update rule of the fixed protocol when brakets do not change (`d`: one of the two agents
is diagonal). -/
def tsStable (d : Bool) (tx ty : TS) : TS :=
  if d then TS.noTie else if ty = TS.spreader ∧ tx = TS.noTie then TS.tie else tx

lemma tsUpd_fixed_stable (dx dy : Bool) (tx ty : TS) :
    tsUpd fixedV dx dx dy dy tx ty = tsStable (dx || dy) tx ty := by
  cases dx <;> cases dy <;> cases tx <;> cases ty <;> decide

lemma tsStable_spreader (ty : TS) : tsStable false TS.spreader ty = TS.spreader := by
  cases ty <;> decide
lemma tsStable_ne_noTie {tx : TS} (ty : TS) (h : tx ≠ TS.noTie) : tsStable false tx ty ≠ TS.noTie := by
  cases tx <;> cases ty <;> simp_all <;> decide
lemma tsStable_meet_spreader (tx : TS) : tsStable false tx TS.spreader ≠ TS.noTie := by
  cases tx <;> decide
lemma tsStable_ne_spreader {tx : TS} (d : Bool) (ty : TS) (h : tx ≠ TS.spreader) :
    tsStable d tx ty ≠ TS.spreader := by
  cases d <;> cases tx <;> cases ty <;> simp_all <;> decide
lemma tsStable_noTie (d : Bool) {tx ty : TS} (hx : tx = TS.noTie) (hy : ty ≠ TS.spreader) :
    tsStable d tx ty = TS.noTie := by
  subst hx; cases d <;> cases ty <;> simp_all <;> decide

lemma tsUpd_fixed_spreader (dpx dpy : Bool) (ty : TS) :
    tsUpd fixedV dpx false dpy false TS.spreader ty = TS.spreader := by
  cases dpx <;> cases dpy <;> cases ty <;> decide

lemma tsUpd_fixed_decay (dpy : Bool) (tx ty : TS) :
    tsUpd fixedV true false dpy false tx ty = TS.spreader := by
  cases dpy <;> cases tx <;> cases ty <;> decide

variable (input : A → Fin k) (E : (tieReport k fixedV).Execution A)

/-- Invariant used for the tie case: there is always a diagonal agent or a `tie_spreader`. -/
lemma diag_or_spreader (h0 : E.config 0 = trInit input) (hne : Nonempty A) (t : ℕ) :
    (∃ y, isDiag (E.config t y).1.1 = true) ∨ ∃ y, (E.config t y).2 = TS.spreader := by
  induction t with
  | zero =>
    obtain ⟨y⟩ := hne
    left; exact ⟨y, by simp [h0, trInit, circlesInit, isDiag]⟩
  | succ t ih =>
    by_cases hd : ∃ y, isDiag (E.config (t + 1) y).1.1 = true
    · exact Or.inl hd
    right
    push Not at hd
    have hd' : ∀ y, isDiag (E.config (t + 1) y).1.1 = false := fun y => by simpa using hd y
    set a := (E.sched t).1; set b := (E.sched t).2
    have hab := E.sched_ne t
    obtain ⟨ha, hb, ho⟩ := tr_interact fixedV (E.config t) hab
    rw [← E.step t] at ha hb ho
    rcases ih with ⟨z, hz⟩ | ⟨z, hz⟩
    · -- the diagonal agent `z` decayed, hence it is in the interacting pair
      refine ⟨z, ?_⟩
      by_cases hza : z = a
      · subst hza; rw [ha]; simp only; rw [hz, hd', hd']; exact tsUpd_fixed_decay _ _ _
      · by_cases hzb : z = b
        · subst hzb; rw [hb]; simp only; rw [hz, hd', hd']; exact tsUpd_fixed_decay _ _ _
        · exfalso; have := hd' z; rw [ho z hza hzb, hz] at this; exact absurd this (by simp)
    · refine ⟨z, ?_⟩
      by_cases hza : z = a
      · subst hza; rw [ha]; simp only; rw [hz, hd', hd']; exact tsUpd_fixed_spreader _ _ _
      · by_cases hzb : z = b
        · subst hzb; rw [hb]; simp only; rw [hz, hd', hd']; exact tsUpd_fixed_spreader _ _ _
        · rw [ho z hza hzb, hz]

/-- **Theorem 4.1, fixed version** (`onlyNoTie` and `selfReset`). Under a weakly fair scheduler:
if there is a unique majority color `μ`, eventually all agents output `μ` forever; if there is a
tie (no unique majority color), eventually all agents report "tie" (`none`) forever. -/
theorem tieReport_fixed_correct (h0 : E.config 0 = trInit input) (hE : E.WeaklyFair) :
    (∀ μ, IsMajority input μ → ∃ T, ∀ t ≥ T, ∀ a, trOutput (E.config t a) = some μ) ∧
    ((¬ ∃ μ, IsMajority input μ) → ∃ T, ∀ t ≥ T, ∀ a, trOutput (E.config t a) = none) := by
  set E1 := E.map (trToCircles fixedV) with hE1
  have h01 : E1.config 0 = circlesInit input := by
    funext a; simp [E1, h0, trInit, trToCircles]
  set E2 := E1.map circlesToCore with hE2
  have h02 : E2.config 0 = initBrakets input := by
    funext a; simp [E2, E1, h0, trInit, circlesInit, initBrakets, trToCircles, circlesToCore]
  obtain ⟨T0, hT0, hS, -, hdiag⟩ := circlesCore_main E2 input h02 ((hE.map _).map _)
  set B := E2.config T0 with hB
  have hbr : ∀ t ≥ T0, ∀ y, (E.config t y).1.1 = B y := fun t ht y => congrFun (hT0 t ht) y
  obtain ⟨p1, p2, hp⟩ : ∃ p1 p2 : A, p1 ≠ p2 := ⟨_, _, E.sched_ne 0⟩
  have partner : ∀ x : A, ∃ y, y ≠ x := fun x =>
    if h : x = p1 then ⟨p2, h ▸ hp.symm⟩ else ⟨p1, Ne.symm h⟩
  -- the update of tie states after `T0`
  have tstep : ∀ t ≥ T0, ∀ x y, (E.sched t = (x, y) ∨ E.sched t = (y, x)) →
      (E.config (t + 1) x).2 =
        tsStable (isDiag (B x) || isDiag (B y)) (E.config t x).2 (E.config t y).2 := by
    intro t ht x y hs
    have hne := E.sched_ne t
    rcases hs with hs | hs <;> rw [hs] at hne <;> simp only at hne
    · obtain ⟨-, ha, -, -⟩ := tr_interact_stable (v := fixedV) hS (hbr t ht) hne
      rw [E.step t, hs]; simp only; rw [ha, tsUpd_fixed_stable]
    · obtain ⟨-, -, hb, -⟩ := tr_interact_stable (v := fixedV) hS (hbr t ht) hne
      rw [E.step t, hs]; simp only; rw [hb, tsUpd_fixed_stable, Bool.or_comm]
  have tother : ∀ t ≥ T0, ∀ x, x ≠ (E.sched t).1 → x ≠ (E.sched t).2 →
      (E.config (t + 1) x).2 = (E.config t x).2 := by
    intro t ht x h1 h2
    rw [E.step t, (tr_interact_stable (v := fixedV) hS (hbr t ht) (E.sched_ne t)).2.2.2 x h1 h2]
  -- a generic persistence principle: `Q` is preserved by every possible update
  have persist : ∀ (Q : TS → Prop) t, t ≥ T0 → ∀ x,
      (∀ y, (E.config (t + 1) x).2 =
        tsStable (isDiag (B x) || isDiag (B y)) (E.config t x).2 (E.config t y).2 →
        Q (E.config t x).2 → Q (E.config (t + 1) x).2) →
      Q (E.config t x).2 → Q (E.config (t + 1) x).2 := by
    intro Q t ht x hQ hx
    by_cases h1 : x = (E.sched t).1
    · exact hQ _ (tstep t ht x _ (Or.inl (by rw [h1]))) hx
    · by_cases h2 : x = (E.sched t).2
      · exact hQ _ (tstep t ht x _ (Or.inr (by rw [h2]))) hx
      · rw [tother t ht x h1 h2]; exact hx
  constructor
  · intro μ hμ
    have hBdiag : ∀ y, isDiag (B y) = true → (B y).1 = μ := by
      intro y hy
      have hy' : (B y).1 = (B y).2 := by simpa [isDiag] using hy
      have := (hdiag (B y).1).1 ⟨y, Prod.ext rfl hy'.symm⟩
      by_contra hne
      exact absurd (this.2 μ (Ne.symm hne)) (not_lt.2 (hμ.2 _ hne).le)
    obtain ⟨d, hd⟩ := (hdiag μ).2 hμ
    have hdd : isDiag (B d) = true := by simp [isDiag, hd]
    -- every agent can be reset to `no_tie` after any time
    have reachN : ∀ x, ∀ T' ≥ T0, ∃ t ≥ T', (E.config (t + 1) x).2 = TS.noTie := by
      intro x T' hT'
      obtain ⟨y, hyx, hy⟩ : ∃ y, y ≠ x ∧ (isDiag (B x) || isDiag (B y)) = true := by
        by_cases hx : isDiag (B x) = true
        · obtain ⟨y, hy⟩ := partner x; exact ⟨y, hy, by simp [hx]⟩
        · exact ⟨d, fun e => hx (e ▸ hdd), by simp [hdd]⟩
      obtain ⟨t, ht, hs⟩ := hE x y (Ne.symm hyx) T'
      exact ⟨t, ht, by rw [tstep t (by omega) x y hs, tsStable, if_pos hy]⟩
    -- no spreaders after some time
    obtain ⟨T1, hT1, hnS⟩ := eventually_all (P := fun t x => (E.config t x).2 ≠ TS.spreader) T0
      (fun t ht x hx => persist (· ≠ TS.spreader) t ht x
        (fun y e h => by rw [e]; exact tsStable_ne_spreader _ _ h) hx)
      (fun x => by
        obtain ⟨t, ht, h⟩ := reachN x T0 le_rfl
        exact ⟨t + 1, by omega, by rw [h]; decide⟩)
    -- all at `no_tie` after some time
    obtain ⟨T2, hT2, hN⟩ := eventually_all (P := fun t x => (E.config t x).2 = TS.noTie) T1
      (fun t ht x hx => persist (· = TS.noTie) t (by omega) x
        (fun y e h => by rw [e]; exact tsStable_noTie _ h (hnS t ht y)) hx)
      (fun x => by
        obtain ⟨t, ht, h⟩ := reachN x T1 hT1
        exact ⟨t + 1, by omega, h⟩)
    -- outputs `μ` (Circles part)
    obtain ⟨T3, hT3, -⟩ := (circles_correct input E1 h01 (hE.map _)).2 μ hμ
    refine ⟨T2 ⊔ T3, fun t ht a => ?_⟩
    have e1 := hN t (le_trans le_sup_left ht) a
    have e2 := hT3 t (le_trans le_sup_right ht) a
    simp only [E1, Execution.map_config, trToCircles, output] at e2
    simp [trOutput, e1, e2]
  · intro hno
    have hnd : ∀ y, isDiag (B y) = false := by
      intro y
      by_contra hy
      have hy' : (B y).1 = (B y).2 := by simpa [isDiag] using hy
      exact hno ⟨_, (hdiag (B y).1).1 ⟨y, Prod.ext rfl hy'.symm⟩⟩
    obtain ⟨s, hs⟩ : ∃ s, (E.config T0 s).2 = TS.spreader := by
      rcases diag_or_spreader input E h0 ⟨p1⟩ T0 with ⟨y, hy⟩ | h
      · rw [hbr T0 le_rfl, hnd] at hy; exact absurd hy (by simp)
      · exact h
    have hsS : ∀ t ≥ T0, (E.config t s).2 = TS.spreader := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => exact hs
      | succ t ht ih =>
        exact persist (· = TS.spreader) t ht s
          (fun y e h => by rw [e, hnd, hnd, h]; exact tsStable_spreader _) ih
    obtain ⟨T, -, hT⟩ := eventually_all (P := fun t x => (E.config t x).2 ≠ TS.noTie) T0
      (fun t ht x hx => persist (· ≠ TS.noTie) t ht x
        (fun y e h => by rw [e, hnd, hnd]; exact tsStable_ne_noTie _ h) hx)
      (fun x => by
        by_cases hxs : x = s
        · exact ⟨T0, le_rfl, by rw [hxs, hs]; decide⟩
        · obtain ⟨t, ht, hsch⟩ := hE x s hxs T0
          refine ⟨t + 1, by omega, ?_⟩
          rw [tstep t ht x s hsch, hnd, hnd, hsS t ht]
          exact tsStable_meet_spreader _)
    exact ⟨T, fun t ht a => by simp [trOutput, hT t ht a]⟩

end RankingOpinions
