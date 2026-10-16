import Papers.PODC2025.BAWithPredictions.Defs
import Cslib.Computability.Distributed.Byzantine.PartialSync.Omission

/-!
# Byzantine Agreement with Predictions — the message lower bound (Theorem 14)

Theorem 14 of [BDEG25] (Theorem 1 in the introduction): every deterministic synchronous Byzantine
agreement algorithm with predictions has an execution in which **the predictions are 100% correct**
and honest processes send `Ω(n + t²)` messages.

We work in CSLib's synchronous Byzantine model (`Cslib.Byzantine.PartialSync`, runs with
`gst = 0`, any delay bound `δ`; `δ = 0` is the lock-step model), with or without signatures.
Inputs are pairs `(value, prediction)`; the prediction type `Pr` is arbitrary and "correct
prediction" is an arbitrary predicate `Cor F p a` ("`a` is a correct prediction for `p` when `F`
is the faulty set"), of which we only assume that every honest process *has* a correct
prediction. For classification predictions `Cor F p a := a = correctPred F`
(`message_lower_bound_classification`).

The proofs are done in the **omission model** (`OmExec`), where the faulty set is only an
*admissible* set for a fixed execution; omission executions are Byzantine runs
(`OmExec.toRun`), so the bounds transfer.

* `t_sq_om`: `⌊t/2⌋ · ⌈t/2⌉` messages (Dolev–Reischuk with predictions).
* `n_om`: `⌈n/4⌉` messages in a fault-free execution.
* `message_lower_bound`: **Theorem 14**, `n + t² ≤ 8 · #messages + 1`.

## Differences with the paper's proof
The paper proves the bound for Byzantine *broadcast* and transfers it to agreement; we prove it
directly for Byzantine agreement (strong unanimity). The paper's choice of the faulty group
`B ⊆ S₀` assumes that a process that receives no messages eventually decides (needed for the
"without loss of generality `|S₀| ≥ ⌈(n-1)/2⌉`" step); this need not hold for processes that never
are isolated in an admissible execution. We instead split the processes according to whether
their *isolated* run (with a fixed input) decides `v₁`; both cases lead to a contradiction.
-/

set_option linter.unusedSectionVars false

namespace BAWithPredictions

open Finset Cslib.Byzantine.PartialSync

variable {P M S V Pr K : Type*} [Fintype P] [DecidableEq P]

/-- **Strong unanimity** for inputs `(value, prediction)`: if all honest processes have the same
value `w`, the decision is `w` (predictions are ignored). -/
def strongUnanimity (P V Pr : Type*) : ValidityProperty P (V × Pr) V :=
  fun c => {v | ∀ w : V, (∀ p x, c p = some x → x.1 = w) → v = w}

/-- All honest processes of `E` (faulty set `F`) have correct predictions. -/
def PredCorrect (Cor : Finset P → P → Pr → Prop) (inp : P → V × Pr) (F : Finset P) : Prop :=
  ∀ p ∉ F, Cor F p (inp p).2

namespace MsgLB

variable {A : Algorithm P M S (V × Pr) V} {t : ℕ}

/-- The omission execution in which every process of `B` is isolated: it receives only its own
messages. -/
def soloExec (x : P → V × Pr) (B : Finset P) : OmExec P (V × Pr) where
  inp := x
  ok _ q p := !(decide (p ∈ B ∧ q ≠ p))

omit [Fintype P] in
theorem soloExec_admits (x : P → V × Pr) (B : Finset P) : (soloExec x B).Admits A B := by
  intro τ q p h _
  simp only [soloExec, Bool.not_eq_false', decide_eq_true_eq] at h
  exact ⟨h.2, Or.inr h.1⟩

omit [Fintype P] in
/-- An isolated process behaves as in any other execution in which it is isolated with the same
input. -/
theorem soloExec_st {x y : P → V × Pr} {B C : Finset P} {p : P} (hpB : p ∈ B) (hpC : p ∈ C)
    (hxy : x p = y p) (τ : ℕ) : (soloExec x B).st A τ p = (soloExec y C).st A τ p := by
  refine OmExec.st_eq_of_inbox_eq (X := fun _ => {p}) (fun _ => le_rfl)
    (fun q hq => by rw [Set.mem_singleton_iff.mp hq]; exact hxy) (fun τ ih q hq => ?_) τ p rfl
  rw [Set.mem_singleton_iff.mp hq]
  funext r
  refine OmExec.inbox_congr ?_ fun hok => ?_
  · by_cases hr : r = p <;> simp [soloExec, hpB, hpC, hr]
  · by_cases hr : r = p
    · subst hr; exact ih r rfl
    · simp [soloExec, hpB, hr] at hok

/-- The decisions of `p` in isolation, with the reference input `x₀`. -/
def IsoDec (A : Algorithm P M S (V × Pr) V) (x₀ : V × Pr) (p : P) (v : V) : Prop :=
  (soloExec (fun _ => x₀) univ).Decides A p v

omit [Fintype P] in
theorem decides_solo_iff {x : P → V × Pr} {B : Finset P} {p : P} (hpB : p ∈ B) {x₀ : V × Pr}
    (hx : x p = x₀) [Fintype P] {v : V} : (soloExec x B).Decides A p v ↔ IsoDec A x₀ p v := by
  unfold IsoDec OmExec.Decides
  simp only [soloExec_st (A := A) hpB (mem_univ p) (y := fun _ => x₀) hx]

theorem conf_strongUnanimity {E : OmExec P (V × Pr)} {F : Finset P} {w u : V}
    (hw : ∀ p ∉ F, (E.inp p).1 = w) (hu : u ∈ strongUnanimity P V Pr (E.conf F)) : u = w := by
  refine hu w fun p y hy => ?_
  simp only [OmExec.conf] at hy
  split_ifs at hy with hp
  cases hy
  exact hw p hp

/-- The only consequence of validity used by the lower bounds: in every admissible execution whose
faulty set lies in `Q` and whose honest processes all have value `w`, honest processes can only
decide `w`. (Agreement with strong unanimity: `Q = univ`; broadcast: `Q` = all but the sender.) -/
def ValidOn (A : Algorithm P M S (V × Pr) V) (t : ℕ) (Q : Finset P) : Prop :=
  ∀ (E : OmExec P (V × Pr)) (F : Finset P) (w u : V), E.Admits A F → F.card ≤ t → F ⊆ Q →
    (∀ p ∉ F, (E.inp p).1 = w) → ∀ p ∉ F, E.Decides A p u → u = w

theorem validOn_strongUnanimity (hS : OmSolves t A (strongUnanimity P V Pr)) :
    ValidOn A t univ := fun E F _ _ hE hF _ hw p hp hu =>
  conf_strongUnanimity hw (hS.validity E F hE hF p hp _ hu)

/-- **Theorem 14, the `t²` part (omission model).** Some omission execution with an admissible
faulty set of size `≤ t` in which all honest processes have correct predictions has at least
`⌊t/2⌋ · ⌈t/2⌉` messages sent by honest processes. -/
theorem t_sq_om {val : ValidityProperty P (V × Pr) V} (hS : OmSolves t A val) {Q : Finset P}
    (hV : ValidOn A t Q) (hQ : t ≤ Q.card + 1) (htn : t < Fintype.card P)
    {v₀ v₁ : V} (hv : v₀ ≠ v₁) (a₀ : Pr) {Cor : Finset P → P → Pr → Prop}
    (hcor : ∀ F p, ∃ a, Cor F p a) :
    ∃ (E : OmExec P (V × Pr)) (F : Finset P), E.Admits A F ∧ F.card ≤ t ∧
      PredCorrect Cor E.inp F ∧ ∃ N, (t / 2) * ((t + 1) / 2) ≤ E.msgsUpTo A F N := by
  classical
  set x₀ : V × Pr := (v₀, a₀)
  -- the two classes
  obtain ⟨w, X, hXQ, hXcard, hX⟩ : ∃ (w : V) (X : Finset P), X ⊆ Q ∧ t / 2 ≤ X.card ∧
      ∀ p ∈ X, ¬ (IsoDec A x₀ p w ∧ ∀ u, IsoDec A x₀ p u → u = w) := by
    set X₁ := Q.filter fun p => ¬ IsoDec A x₀ p v₁
    set X₀ := Q.filter fun p => IsoDec A x₀ p v₁
    have hsum : X₁.card + X₀.card = Q.card := by
      rw [add_comm]; exact card_filter_add_card_filter_not _
    by_cases h1 : t / 2 ≤ X₁.card
    · refine ⟨v₁, X₁, filter_subset _ _, h1, fun p hp h => ?_⟩
      exact (mem_filter.mp hp).2 h.1
    · refine ⟨v₀, X₀, filter_subset _ _, by omega, fun p hp h => ?_⟩
      exact hv (h.2 v₁ (mem_filter.mp hp).2).symm
  obtain ⟨B, hBX, hBcard⟩ := exists_subset_card_eq hXcard
  set c : P → Pr := fun p => Classical.choose (hcor B p)
  set x : P → V × Pr := fun p => if p ∈ B then x₀ else (w, c p)
  set E := soloExec x B
  have hE : E.Admits A B := soloExec_admits x B
  have hBt : B.card ≤ t := by omega
  have hcorr : PredCorrect Cor E.inp B := by
    intro p hp
    simp only [E, soloExec, x, hp, ↓reduceIte]
    exact Classical.choose_spec (hcor B p)
  refine ⟨E, B, hE, hBt, hcorr, ?_⟩
  set σ := (t + 1) / 2
  set D := E.dropSenders A B
  by_cases hall : ∀ p ∈ B, σ ≤ (D p).card
  · obtain ⟨N, hN⟩ := OmExec.sum_card_dropSenders_le (A := A) (E := E) (subset_refl B)
    refine ⟨N, le_trans ?_ hN⟩
    rw [← hBcard]
    calc B.card * σ = ∑ _p ∈ B, σ := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ p ∈ B, (D p).card := sum_le_sum hall
  · exfalso
    push Not at hall
    obtain ⟨p, hpB, hpD⟩ := hall
    -- blame the senders to `p` instead of `p`
    obtain ⟨F', hF'⟩ : ∃ F', F' = B.erase p ∪ D p := ⟨_, rfl⟩
    have hE' : E.Admits A F' := by
      rw [hF']
      refine hE.swap fun τ r h1 _ => ?_
      simp only [E, soloExec, Bool.not_eq_false', decide_eq_true_eq] at h1
      exact h1.1
    have hF'card : F'.card ≤ t := by
      rw [hF']
      have := card_union_le (B.erase p) (D p)
      have := card_erase_of_mem hpB
      omega
    have hpF' : p ∉ F' := by
      simp only [hF', mem_union, mem_erase, not_or, not_and]
      exact ⟨fun h => absurd rfl h, OmExec.not_mem_dropSenders hpB⟩
    -- a process honest in both
    obtain ⟨q, hq⟩ : (univ \ (B ∪ D p)).Nonempty := by
      rw [← card_pos, card_sdiff_of_subset (subset_univ _), card_univ]
      have := card_union_le B (D p)
      omega
    simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or] at hq
    have hqF' : q ∉ F' := by
      simp only [hF', mem_union, mem_erase, not_or, not_and]
      exact ⟨fun _ h => hq.1 h, hq.2⟩
    have hval : ∀ r ∉ B, (E.inp r).1 = w := by
      intro r hr; simp [E, soloExec, x, hr]
    obtain ⟨u, hu⟩ := hS.termination E B hE hBt q hq.1
    have huw : u = w := hV E B w u hE hBt (hBX.trans hXQ) hval q hq.1 hu
    subst huw
    obtain ⟨u', hu'⟩ := hS.termination E F' hE' hF'card p hpF'
    have hdec : ∀ v, E.Decides A p v → v = u := fun v hv =>
      hS.agreement E F' hE' hF'card p hpF' q hqF' v u hv hu
    have hxp : x p = x₀ := by simp [x, hpB]
    refine hX p (hBX hpB) ⟨?_, fun v hv => hdec v ((decides_solo_iff hpB hxp).mpr hv)⟩
    rw [← decides_solo_iff hpB hxp, ← hdec u' hu']
    exact hu'

/-! ### The `n` part -/

/-- The fault-free execution with inputs `x`. -/
def ffE (x : P → V × Pr) : OmExec P (V × Pr) where
  inp := x
  ok _ _ _ := true

omit [Fintype P] in
theorem ffE_admits (x : P → V × Pr) : (ffE x).Admits A ∅ := by
  intro τ q p h; simp [ffE] at h

omit [Fintype P] in
theorem ffE_inbox (x : P → V × Pr) (τ : ℕ) (p q : P) :
    (ffE x).inbox A τ p q = A.send q ((ffE x).st A τ q) p := by
  simp [OmExec.inbox, ffE]

/-- The non-empty batches sent to other processes before time `N`. -/
def batches (A : Algorithm P M S (V × Pr) V) (E : OmExec P (V × Pr)) (N : ℕ) :
    Finset (ℕ × P × P) :=
  ((range N) ×ˢ (univ : Finset (P × P))).filter fun e =>
    e.2.1 ≠ e.2.2 ∧ A.send e.2.1 (E.st A e.1 e.2.1) e.2.2 ≠ []

theorem card_batches_le (E : OmExec P (V × Pr)) (N : ℕ) :
    (batches A E N).card ≤ E.msgsUpTo A ∅ N := by
  classical
  unfold batches OmExec.msgsUpTo
  rw [card_filter, sum_product]
  refine sum_le_sum fun τ _ => ?_
  rw [← univ_product_univ, sum_product]
  simp only [Finset.notMem_empty, not_false_eq_true, filter_true]
  refine sum_le_sum fun q _ => ?_
  rw [sum_filter]
  refine sum_le_sum fun p _ => ?_
  split_ifs with h1 h2 h2
  · exact List.length_pos_iff.mpr h1.2
  · exact absurd (Ne.symm h1.1) h2
  · exact Nat.zero_le _
  · exact le_rfl

/-- Processes that send or receive a message before time `N`. -/
def touched (A : Algorithm P M S (V × Pr) V) (E : OmExec P (V × Pr)) (N : ℕ) : Finset P :=
  (batches A E N).image (fun e => e.2.1) ∪ (batches A E N).image (fun e => e.2.2)

theorem card_touched_le (E : OmExec P (V × Pr)) (N : ℕ) :
    (touched A E N).card ≤ 2 * E.msgsUpTo A ∅ N := by
  have h1 := card_union_le ((batches A E N).image (fun e => e.2.1))
    ((batches A E N).image (fun e => e.2.2))
  have h2 := card_image_le (s := batches A E N) (f := fun e => e.2.1)
  have h3 := card_image_le (s := batches A E N) (f := fun e => e.2.2)
  have := card_batches_le (A := A) E N
  unfold touched
  omega

theorem mem_touched {E : OmExec P (V × Pr)} {N τ : ℕ} (hτ : τ < N) {z q : P} (hq : q ≠ z)
    (h : A.send z (E.st A τ z) q ≠ [] ∨ A.send q (E.st A τ q) z ≠ []) : z ∈ touched A E N := by
  unfold touched batches
  rcases h with h | h
  · refine mem_union_left _ (mem_image.mpr ⟨(τ, z, q), ?_, rfl⟩)
    simp [hτ, Ne.symm hq, h]
  · refine mem_union_right _ (mem_image.mpr ⟨(τ, q, z), ?_, rfl⟩)
    simp [hτ, hq, h]

theorem ffE_decides_eq {val : ValidityProperty P (V × Pr) V} {x : P → V × Pr} {w : V}
    (hS : OmSolves t A val) {Q : Finset P} (hV : ValidOn A t Q)
    (hx : ∀ p, (x p).1 = w) (p : P) : ∃ u, (ffE x).Decides A p u ∧ u = w := by
  obtain ⟨u, hu⟩ := hS.termination (ffE x) ∅ (ffE_admits x) (by simp) p (by simp)
  exact ⟨u, hu, hV (ffE x) ∅ w u (ffE_admits x) (by simp) (empty_subset _) (fun r _ => hx r) p
    (by simp) hu⟩

/-- **Theorem 14, the `n` part (omission model).** Some fault-free execution in which all
predictions are correct has at least `n / 4` messages. -/
theorem n_om {val : ValidityProperty P (V × Pr) V} (hS : OmSolves t A val) {Q : Finset P}
    (hV : ValidOn A t Q) (hn : 2 ≤ Fintype.card P)
    {v₀ v₁ : V} (hv : v₀ ≠ v₁) {Cor : Finset P → P → Pr → Prop}
    (hcor : ∀ F p, ∃ a, Cor F p a) :
    ∃ E : OmExec P (V × Pr), E.Admits A ∅ ∧ PredCorrect Cor E.inp ∅ ∧
      ∃ N, Fintype.card P ≤ 4 * E.msgsUpTo A ∅ N := by
  classical
  set c : P → Pr := fun p => Classical.choose (hcor ∅ p)
  have hc : ∀ p, Cor ∅ p (c p) := fun p => Classical.choose_spec (hcor ∅ p)
  set x₀ : P → V × Pr := fun p => (v₀, c p)
  set x₁ : P → V × Pr := fun p => (v₁, c p)
  set E₀ := ffE x₀
  set E₁ := ffE x₁
  by_cases hiso : ∃ z, ∀ τ, ∀ q, q ≠ z →
      A.send z (E₀.st A τ z) q = [] ∧ A.send q (E₀.st A τ q) z = [] ∧
      A.send z (E₁.st A τ z) q = [] ∧ A.send q (E₁.st A τ q) z = []
  · exfalso
    obtain ⟨z, hz⟩ := hiso
    set x' : P → V × Pr := fun p => if p = z then x₀ p else x₁ p
    set E' := ffE x'
    have key : ∀ τ, E'.st A τ z = E₀.st A τ z ∧ ∀ p, p ≠ z → E'.st A τ p = E₁.st A τ p := by
      intro τ
      induction τ with
      | zero =>
        refine ⟨by simp [E', E₀, ffE, x'], fun p hp => by simp [E', E₁, ffE, x', hp]⟩
      | succ τ ih =>
        refine ⟨?_, fun p hp => ?_⟩
        · rw [OmExec.st_succ, OmExec.st_succ, ih.1]
          congr 1
          funext q
          rw [ffE_inbox, ffE_inbox]
          by_cases hq : q = z
          · subst hq; rw [ih.1]
          · rw [ih.2 q hq, (hz τ q hq).2.2.2, (hz τ q hq).2.1]
        · rw [OmExec.st_succ, OmExec.st_succ, ih.2 p hp]
          congr 1
          funext q
          rw [ffE_inbox, ffE_inbox]
          by_cases hq : q = z
          · subst hq; rw [ih.1, (hz τ p hp).1, (hz τ p hp).2.2.1]
          · rw [ih.2 q hq]
    obtain ⟨p, hp⟩ := Fintype.exists_ne_of_one_lt_card (by omega) z
    obtain ⟨u₀, hu₀, rfl⟩ := ffE_decides_eq (w := v₀) hS hV (x := x₀) (fun _ => rfl) z
    obtain ⟨u₁, hu₁, rfl⟩ := ffE_decides_eq (w := v₁) hS hV (x := x₁) (fun _ => rfl) p
    have d₀ : E'.Decides A z u₀ := by
      obtain ⟨τ, h⟩ := hu₀; exact ⟨τ, by rw [(key τ).1]; exact h⟩
    have d₁ : E'.Decides A p u₁ := by
      obtain ⟨τ, h⟩ := hu₁; exact ⟨τ, by rw [(key τ).2 p hp]; exact h⟩
    exact hv (hS.agreement E' ∅ (ffE_admits x') (by simp) z (by simp) p (by simp) u₀ u₁ d₀ d₁)
  · push Not at hiso
    have hτ : ∀ z, ∃ τ, ∃ q, q ≠ z ∧
        ((A.send z (E₀.st A τ z) q ≠ [] ∨ A.send q (E₀.st A τ q) z ≠ []) ∨
         (A.send z (E₁.st A τ z) q ≠ [] ∨ A.send q (E₁.st A τ q) z ≠ [])) := by
      intro z
      obtain ⟨τ, q, hq, h⟩ := hiso z
      refine ⟨τ, q, hq, ?_⟩
      by_contra hc
      push Not at hc
      exact h hc.1.1 hc.1.2 hc.2.1 hc.2.2
    choose τz qz hqz hz using hτ
    set N := univ.sup τz + 1
    have hcov : (univ : Finset P) ⊆ touched A E₀ N ∪ touched A E₁ N := by
      intro z _
      have hlt : τz z < N := Nat.lt_succ_of_le (le_sup (f := τz) (mem_univ z))
      rcases hz z with h | h
      · exact mem_union_left _ (mem_touched hlt (hqz z) h)
      · exact mem_union_right _ (mem_touched hlt (hqz z) h)
    have h1 := card_le_card hcov
    have h2 := card_union_le (touched A E₀ N) (touched A E₁ N)
    have h3 := card_touched_le (A := A) E₀ N
    have h4 := card_touched_le (A := A) E₁ N
    rw [card_univ] at h1
    by_cases hm : E₁.msgsUpTo A ∅ N ≤ E₀.msgsUpTo A ∅ N
    · exact ⟨E₀, ffE_admits x₀, fun p _ => hc p, N, by omega⟩
    · exact ⟨E₁, ffE_admits x₁, fun p _ => hc p, N, by omega⟩

end MsgLB

end BAWithPredictions

namespace BAWithPredictions

open Finset Cslib.Byzantine.PartialSync MsgLB

variable {P M S V Pr K : Type*} [Fintype P] [DecidableEq P]
  {A : Algorithm P M S (V × Pr) V} {Au : Auth P M K} {t δ : ℕ}

/-- An omission execution with an admissible faulty set gives a Byzantine synchronous run with
the same faulty set, inputs and message count. -/
theorem exists_run_of_om (hU : A.Unforging Au) {E : OmExec P (V × Pr)} {F : Finset P}
    (hE : E.Admits A F) (hF : F.card ≤ t) {Cor : Finset P → P → Pr → Prop}
    (hc : PredCorrect Cor E.inp F) {N : ℕ} :
    ∃ R : Run P M (V × Pr), R.Valid t δ ∧ R.AuthValid Au A ∧ R.gst = 0 ∧
      PredCorrect Cor R.inp R.faulty ∧ R.msgsUpTo A N = E.msgsUpTo A F N :=
  ⟨E.toRun A F, OmExec.toRun_valid hF δ, OmExec.toRun_authValid hU hE, rfl, hc,
    OmExec.toRun_msgsUpTo hE N⟩

/-- **Theorem 14 of [BDEG25], `t²` part.** For every synchronous Byzantine agreement algorithm
with predictions (authenticated or not, any prediction type), there is an execution in which all
honest processes receive correct predictions and honest processes send at least
`⌊t/2⌋ · ⌈t/2⌉` messages. -/
theorem message_lower_bound_t (hU : A.Unforging Au)
    (hA : SolvesConsensusAuthSync Au t δ A (strongUnanimity P V Pr)) (htn : t < Fintype.card P)
    {v₀ v₁ : V} (hv : v₀ ≠ v₁) {Cor : Finset P → P → Pr → Prop} (hcor : ∀ F p, ∃ a, Cor F p a)
    [Nonempty P] :
    ∃ R : Run P M (V × Pr), R.Valid t δ ∧ R.AuthValid Au A ∧ R.gst = 0 ∧
      PredCorrect Cor R.inp R.faulty ∧ ∃ N, (t / 2) * ((t + 1) / 2) ≤ R.msgsUpTo A N := by
  obtain ⟨a₀, -⟩ := hcor ∅ (Classical.arbitrary P)
  obtain ⟨E, F, hE, hF, hc, N, hN⟩ := t_sq_om (hA.omSolves hU) (validOn_strongUnanimity (hA.omSolves hU))
    (by rw [card_univ]; omega) htn hv a₀ hcor
  obtain ⟨R, h1, h2, h3, h4, h5⟩ := exists_run_of_om (δ := δ) (N := N) hU hE hF hc
  exact ⟨R, h1, h2, h3, h4, N, h5 ▸ hN⟩

/-- **Theorem 14 of [BDEG25], `n` part.** With `n ≥ 2` processes, some execution with correct
predictions (indeed a fault-free one) has at least `n / 4` messages. -/
theorem message_lower_bound_n (hU : A.Unforging Au)
    (hA : SolvesConsensusAuthSync Au t δ A (strongUnanimity P V Pr)) (hn : 2 ≤ Fintype.card P)
    {v₀ v₁ : V} (hv : v₀ ≠ v₁) {Cor : Finset P → P → Pr → Prop} (hcor : ∀ F p, ∃ a, Cor F p a) :
    ∃ R : Run P M (V × Pr), R.Valid t δ ∧ R.AuthValid Au A ∧ R.gst = 0 ∧
      PredCorrect Cor R.inp R.faulty ∧ ∃ N, Fintype.card P ≤ 4 * R.msgsUpTo A N := by
  obtain ⟨E, hE, hc, N, hN⟩ := n_om (hA.omSolves hU) (validOn_strongUnanimity (hA.omSolves hU)) hn hv hcor
  obtain ⟨R, h1, h2, h3, h4, h5⟩ :=
    exists_run_of_om (δ := δ) (t := t) (N := N) hU hE (by simp) hc
  exact ⟨R, h1, h2, h3, h4, N, h5 ▸ hN⟩

theorem sq_le_four_mul (t : ℕ) : t ^ 2 ≤ 4 * ((t / 2) * ((t + 1) / 2)) + 1 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' t
  · have h1 : 2 * k / 2 = k := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    rw [h1, h2]; nlinarith
  · have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    rw [h1, h2]; nlinarith

/-- **Theorem 14 of [BDEG25]** (Theorem 1 of the introduction): for every deterministic
synchronous Byzantine agreement algorithm with predictions tolerating `t < n` Byzantine
processes (with or without signatures, for any prediction type in which every honest process has
a correct prediction), there is an execution in which **all honest processes receive correct
predictions** and honest processes send `Ω(n + t²)` messages: `n + t² ≤ 8 · #messages + 1`. -/
theorem message_lower_bound (hU : A.Unforging Au)
    (hA : SolvesConsensusAuthSync Au t δ A (strongUnanimity P V Pr))
    (hn : 2 ≤ Fintype.card P) (htn : t < Fintype.card P) {v₀ v₁ : V} (hv : v₀ ≠ v₁)
    {Cor : Finset P → P → Pr → Prop} (hcor : ∀ F p, ∃ a, Cor F p a) :
    ∃ R : Run P M (V × Pr), R.Valid t δ ∧ R.AuthValid Au A ∧ R.gst = 0 ∧
      PredCorrect Cor R.inp R.faulty ∧ ∃ N, Fintype.card P + t ^ 2 ≤ 8 * R.msgsUpTo A N + 1 := by
  have : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨R₁, a1, b1, c1, d1, N₁, e1⟩ := message_lower_bound_n hU hA hn hv hcor
  obtain ⟨R₂, a2, b2, c2, d2, N₂, e2⟩ := message_lower_bound_t hU hA htn hv hcor
  have := sq_le_four_mul t
  by_cases h : R₂.msgsUpTo A N₂ ≤ R₁.msgsUpTo A N₁
  · exact ⟨R₁, a1, b1, c1, d1, N₁, by omega⟩
  · exact ⟨R₂, a2, b2, c2, d2, N₂, by omega⟩

/-- **Theorem 14 for classification predictions** (the predictions of Section 3): there is an
execution in which every honest process receives the *correct* classification (`B = 0`) and
`n + t² ≤ 8 · #messages + 1`. Unauthenticated version. -/
theorem message_lower_bound_classification {A : Algorithm P M S (V × (P → Bool)) V}
    (hA : SolvesConsensusSync t δ A (strongUnanimity P V (P → Bool)))
    (hn : 2 ≤ Fintype.card P) (htn : t < Fintype.card P) {v₀ v₁ : V} (hv : v₀ ≠ v₁) :
    ∃ R : Run P M (V × (P → Bool)), R.Valid t δ ∧ R.gst = 0 ∧
      wrongBits R.faulty (fun i => (R.inp i).2) = 0 ∧
      ∃ N, Fintype.card P + t ^ 2 ≤ 8 * R.msgsUpTo A N + 1 := by
  obtain ⟨R, h1, -, h3, h4, N, h5⟩ := message_lower_bound (Cor := fun F _ a => a = correctPred F)
    A.unforging_none hA hn htn hv (fun F _ => ⟨_, rfl⟩)
  refine ⟨R, h1, h3, ?_, N, h5⟩
  unfold wrongBits
  refine sum_eq_zero fun i hi => ?_
  have := h4 i (by simpa using hi)
  simp only at this ⊢
  rw [this]
  exact wrongBitsOf_correctPred _

/-! ### Byzantine broadcast (the paper's formulation of Theorem 14) -/

/-- Validity of **Byzantine broadcast** with sender `s` (only the sender's value matters): if the
sender is honest, the decision is its value. -/
def bbValidity (s : P) : ValidityProperty P (V × Pr) V :=
  fun c => {v | ∀ x, c s = some x → v = x.1}

theorem validOn_bb {s : P} (hS : OmSolves t A (bbValidity s)) : ValidOn A t (univ.erase s) :=
  fun E F w u hE hF hFQ hw p hp hu => by
    have hs : s ∉ F := fun h => by simpa using hFQ h
    have := hS.validity E F hE hF p hp u hu (E.inp s) (by simp [OmExec.conf, hs])
    rw [this, hw s hs]

/-- **Theorem 14 of [BDEG25], as stated (Byzantine broadcast).** For every synchronous Byzantine
broadcast algorithm with predictions and sender `s` (with or without signatures), there is an
execution in which all honest processes have correct predictions and
`n + t² ≤ 8 · #messages + 1`. -/
theorem message_lower_bound_bb {s : P} (hU : A.Unforging Au)
    (hA : SolvesConsensusAuthSync Au t δ A (bbValidity s))
    (hn : 2 ≤ Fintype.card P) (htn : t < Fintype.card P) {v₀ v₁ : V} (hv : v₀ ≠ v₁)
    {Cor : Finset P → P → Pr → Prop} (hcor : ∀ F p, ∃ a, Cor F p a) :
    ∃ R : Run P M (V × Pr), R.Valid t δ ∧ R.AuthValid Au A ∧ R.gst = 0 ∧
      PredCorrect Cor R.inp R.faulty ∧ ∃ N, Fintype.card P + t ^ 2 ≤ 8 * R.msgsUpTo A N + 1 := by
  have hS := hA.omSolves hU
  have hV := validOn_bb hS
  obtain ⟨a₀, -⟩ := hcor ∅ s
  obtain ⟨E₁, hE₁, hc₁, N₁, e1⟩ := n_om hS hV hn hv hcor
  obtain ⟨E₂, F₂, hE₂, hF₂, hc₂, N₂, e2⟩ := t_sq_om hS hV
    (by rw [card_erase_of_mem (mem_univ s), card_univ]; omega) htn hv a₀ hcor
  obtain ⟨R₁, a1, b1, c1, d1, f1⟩ := exists_run_of_om (δ := δ) (t := t) (N := N₁) hU hE₁ (by simp) hc₁
  obtain ⟨R₂, a2, b2, c2, d2, f2⟩ := exists_run_of_om (δ := δ) (N := N₂) hU hE₂ hF₂ hc₂
  have := sq_le_four_mul t
  by_cases h : R₂.msgsUpTo A N₂ ≤ R₁.msgsUpTo A N₁
  · exact ⟨R₁, a1, b1, c1, d1, N₁, by omega⟩
  · exact ⟨R₂, a2, b2, c2, d2, N₂, by omega⟩

end BAWithPredictions
