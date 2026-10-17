import Papers.PODC2021.GoodCaseLatencyBB.PsyncLowerBound
import Papers.PODC2021.GoodCaseLatencyBB.SplitBrain
import Papers.PODC2021.GoodCaseLatencyBB.SmallCases

/-!
# Partially synchronous Byzantine broadcast is impossible for `n ∈ {2, 3}`, `f ≥ 1`

For `n = 2` or `n = 3` and `f ≥ 1`, no (authenticated) protocol solves partially synchronous
Byzantine broadcast (`IsPsyncBB`), by the classic partition arguments (runs with at most one
faulty process suffice):

* `n = 2`, `P = {s, p}`. Run `Rₐ`: `s` faulty and silent, `GST = 0`: by termination `p` commits
  some `w`. Run `R_b`: `p` faulty and silent, `s` has input `v ≠ w`: by validity `s` commits `v`.
  Run `R_c`: nobody faulty, `GST = T + 1` and the messages between `s` and `p` are delayed until
  `T + 1`: up to `T`, `p` behaves as in `Rₐ` and `s` as in `R_b`, so agreement fails.
* `n = 3`, `P = {s, p, q}`. `R₁`: `q` faulty and silent, `s` has input `a`: `p` commits `a`.
  `R₂`: `p` faulty and silent, `s` has input `b`: `q` commits `b`. `R₃`: `s` faulty, it replays
  its `R₁`-messages to `p` and its `R₂`-messages to `q` until `T`; messages between `p` and `q`
  are delayed until `T + 1 = GST`. Then `p` behaves as in `R₁` and `q` as in `R₂`.

Consequently Theorems 6 and 7 hold for all `n ≥ 2` (`theorem_6_all`, `theorem_7_all`); for
`n = 1` they are false (`theorem_7_false_one` in `SmallCases.lean`).
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K : Type*} [DecidableEq P]

section runs

variable {A : Algorithm P M S V V}

/-- Silent processes of a quiet run send nothing. -/
theorem quiet_out_nil {F : Finset P} {I : P → V} {q : P} (hq : q ∈ F) (τ : ℕ)
    (r : P) : (Run.quiet (M := M) F I).out A q τ r = [] :=
  Run.out_eq_nil_of_canonical A Run.quiet_canonical hq τ r

/-- Indistinguishability for a single process, batch by batch. -/
theorem st_eq_view {R R' : Run P M V} {x : P} {T : ℕ} (hinp : R.inp x = R'.inp x)
    (h : ∀ τ < T, (∀ σ ≤ τ, R.st A σ x = R'.st A σ x) → ∀ q, ∀ τ' ≤ τ,
      R.dlv A q τ' x τ = R'.dlv A q τ' x τ) :
    ∀ τ ≤ T, R.st A τ x = R'.st A τ x := fun τ hτ =>
  R.st_eq_of_inbox_eq A (ref := fun _ => R') (X := {x}) (by rintro p rfl; exact hinp)
    (by rintro τ hτ H p rfl; exact R.inbox_eq_of_dlv_eq A (h τ hτ (H p rfl))) τ hτ x rfl

theorem dlv_self_eq {R R' : Run P M V} {x : P} {τ τ' : ℕ} (hx : x ∉ R.faulty)
    (hx' : x ∉ R'.faulty) (hd : R.dl x τ' x = τ') (hd' : R'.dl x τ' x = τ') (hτ' : τ' ≤ τ)
    (hst : ∀ σ ≤ τ, R.st A σ x = R'.st A σ x) :
    R.dlv A x τ' x τ = R'.dlv A x τ' x τ := by
  simp only [Run.dlv, hd, hd', Run.out_of_correct A R hx, Run.out_of_correct A R' hx',
    hst τ' hτ']

end runs

variable [Fintype P] {A : Algorithm P M S V V} {Au : Auth P M K}

theorem three_cases (h3 : Fintype.card P = 3) {s p q x : P} (hps : p ≠ s) (hqs : q ≠ s)
    (hpq : p ≠ q) (hxs : x ≠ s) (hxp : x ≠ p) : x = q := by
  by_contra hxq
  have : ({x, p, q, s} : Finset P).card ≤ 3 := h3 ▸ card_le_univ _
  rw [card_insert_of_notMem (by simp [hxp, hxq, hxs]),
    card_insert_of_notMem (by simp [hpq, hps]), card_insert_of_notMem (by simp [hqs])] at this
  simp at this

/-- Partially synchronous BB is impossible for `n = 2` and `f ≥ 1` (for every algorithm: all
runs used are canonical, so unforgeability is not needed). -/
theorem psyncBB_impossible_two {s : P} {f D : ℕ} (hf : 1 ≤ f)
    (h2 : Fintype.card P = 2) {a b : V} (hab : a ≠ b) : ¬ IsPsyncBB Au A s f D := by
  intro hA
  obtain ⟨p, hps⟩ := Fintype.exists_ne_of_one_lt_card (by omega) s
  have hall : ∀ x, x ≠ s → x = p := fun x hx => two_cases h2 hx hps
  let Ra := Run.quiet (M := M) {s} (fun _ => a)
  obtain ⟨w, Ta, hTa⟩ := hA.termination Ra (Run.quiet_valid (by simpa using hf) _)
    Run.quiet_authValid p (by simp [Ra, Run.quiet, hps])
  obtain ⟨v, hvw⟩ : ∃ v, v ≠ w := by
    classical
    exact if h : a = w then ⟨b, fun e => hab (h.trans e.symm)⟩ else ⟨a, h⟩
  let I : P → V := Function.update (fun _ => a) s v
  let Rb := Run.quiet (M := M) {p} I
  obtain ⟨Tb, hTb⟩ := hA.validity Rb (Run.quiet_valid (by simpa using hf) _) Run.quiet_authValid
    rfl (by simp [Rb, Run.quiet, hps.symm]) s (by simp [Rb, Run.quiet, hps.symm])
  let T := max Ta Tb
  let Rc : Run P M V :=
    { faulty := ∅, inp := I, gst := T + 1, byz := fun _ _ _ => []
      dl := fun q τ r => if q = r then τ else max τ (T + 1) }
  have hRc : Rc.Valid f D :=
    ⟨by simp [Rc], fun q τ r _ _ => by simp only [Rc]; split_ifs <;> omega,
      fun q τ r _ _ => by simp only [Rc]; split_ifs <;> omega⟩
  have hp : ∀ τ ≤ T, Rc.st A τ p = Ra.st A τ p :=
    st_eq_view (by simp [Rc, I, Ra, Run.quiet, hps]) fun τ hτ hst q τ' hτ' => by
      by_cases hq : q = p
      · subst hq
        exact dlv_self_eq (by simp [Rc]) (by simp [Ra, Run.quiet, hps]) (by simp [Rc]) rfl hτ' hst
      · have hqs : q = s := by by_contra h; exact hq (hall q h)
        subst hqs
        rw [Run.dlv_eq_nil_of_ne _ _ (by simp only [Rc, Ne.symm hps, ite_false]; omega)]
        simp [Run.dlv, show Ra.out A q τ' p = [] from quiet_out_nil (mem_singleton_self _) _ _]
  have hs : ∀ τ ≤ T, Rc.st A τ s = Rb.st A τ s :=
    st_eq_view (by simp [Rc, Rb, Run.quiet]) fun τ hτ hst q τ' hτ' => by
      by_cases hq : q = s
      · subst hq
        exact dlv_self_eq (by simp [Rc]) (by simp [Rb, Run.quiet, hps.symm]) (by simp [Rc]) rfl
          hτ' hst
      · obtain rfl := hall q hq
        rw [Run.dlv_eq_nil_of_ne _ _ (by simp only [Rc, hps, ite_false]; omega)]
        simp [Run.dlv, show Rb.out A q τ' s = [] from quiet_out_nil (mem_singleton_self _) _ _]
  refine hvw (hA.agreement Rc hRc (Run.authValid_of_canonical fun _ _ _ _ => rfl) s
    (by simp [Rc]) p (by simp [Rc]) v w ⟨Tb, ?_⟩ ⟨Ta, ?_⟩)
  · rw [hs Tb (le_max_right _ _), hTb]; simp [Rb, Run.quiet, I]
  · rw [hp Ta (le_max_left _ _)]; exact hTa

/-- Partially synchronous BB is impossible for `n = 3` and `f ≥ 1`. -/
theorem psyncBB_impossible_three (hU : A.Unforging Au) {s : P} {f D : ℕ} (hf : 1 ≤ f)
    (h3 : Fintype.card P = 3) {a b : V} (hab : a ≠ b) : ¬ IsPsyncBB Au A s f D := by
  intro hA
  obtain ⟨p, q, hpq, hps, hqs⟩ := exists_three s (by omega)
  have hall : ∀ x, x ≠ s → x ≠ p → x = q := fun x hxs hxp => three_cases h3 hps hqs hpq hxs hxp
  let I0 : P → V := fun _ => a
  let R1 := Run.quiet (M := M) {q} I0
  obtain ⟨T1, hT1⟩ := hA.validity R1 (Run.quiet_valid (by simpa using hf) _) Run.quiet_authValid
    rfl (by simp [R1, Run.quiet, hqs.symm]) p (by simp [R1, Run.quiet, hpq])
  let R2 := Run.quiet (M := M) {p} (Function.update I0 s b)
  obtain ⟨T2, hT2⟩ := hA.validity R2 (Run.quiet_valid (by simpa using hf) _) Run.quiet_authValid
    rfl (by simp [R2, Run.quiet, hps.symm]) q (by simp [R2, Run.quiet, hpq.symm])
  let T := max T1 T2
  let R3 : Run P M V :=
    { faulty := {s}, inp := I0, gst := T + 1
      byz := fun _ τ r => if τ ≤ T then (if r = q then R2.out A s τ r else R1.out A s τ r)
        else []
      dl := fun x τ r => if x = s ∨ x = r then τ else max τ (T + 1) }
  have hR3 : R3.Valid f D :=
    ⟨by simpa [R3] using hf, fun q τ r _ _ => by simp only [R3]; split_ifs <;> omega,
      fun q τ r _ _ => by simp only [R3]; split_ifs <;> omega⟩
  have hs3 : s ∈ R3.faulty := mem_singleton_self _
  have hp3 : ∀ τ ≤ T, R3.st A τ p = R1.st A τ p :=
    st_eq_view rfl fun τ hτ hst y τ' hτ' => by
      by_cases hyp : y = p
      · subst hyp
        exact dlv_self_eq (by simp [R3, hps]) (by simp [R1, Run.quiet, hpq]) (by simp [R3]) rfl
          hτ' hst
      by_cases hys : y = s
      · subst hys
        simp only [Run.dlv, Run.out_of_faulty A R3 hs3]
        simp [R3, R1, Run.quiet, show τ' ≤ T by omega, hpq]
      · obtain rfl := hall y hys hyp
        rw [Run.dlv_eq_nil_of_ne _ _ (by simp only [R3, hys, hpq.symm, or_self, ite_false]; omega)]
        simp [Run.dlv, R1, quiet_out_nil (show y ∈ ({y} : Finset P) from mem_singleton_self _)]
  have hq3 : ∀ τ ≤ T, R3.st A τ q = R2.st A τ q :=
    st_eq_view (by simp [R3, R2, Run.quiet, I0, hqs]) fun τ hτ hst y τ' hτ' => by
      by_cases hyq : y = q
      · subst hyq
        exact dlv_self_eq (by simp [R3, hqs]) (by simp [R2, Run.quiet, hpq.symm]) (by simp [R3])
          rfl hτ' hst
      by_cases hys : y = s
      · subst hys
        simp only [Run.dlv, Run.out_of_faulty A R3 hs3]
        simp [R3, R2, Run.quiet, show τ' ≤ T by omega]
      · have hyp : y = p := by by_contra h; exact hyq (hall y hys h)
        subst hyp
        rw [Run.dlv_eq_nil_of_ne _ _ (by simp only [R3, hys, hpq, or_self, ite_false]; omega)]
        simp [Run.dlv, R2, quiet_out_nil (show y ∈ ({y} : Finset P) from mem_singleton_self _)]
  have hR3A : R3.AuthValid Au A := by
    intro y hy τ r _ m hm x hx
    obtain rfl : y = s := by simpa [R3] using hy
    simp only [R3] at hm
    split_ifs at hm with hτ hrq
    · refine Run.tokens_replay hU (Ri := R2) (R' := R3) (T := T) (fun z σ r hσ => ?_) τ hτ y r m
        hm x hx
      by_cases hzs : z = y
      · subst hzs; exact Or.inr (Or.inl ⟨hs3, by simp [R2, Run.quiet, hps.symm]⟩)
      by_cases hzp : z = p
      · subst hzp
        refine Or.inr (Or.inr fun m hm => ?_)
        rw [quiet_out_nil (mem_singleton_self _)] at hm; simp at hm
      · obtain rfl := hall z hzs hzp
        refine Or.inl ⟨by simp [R3, hzs], ?_⟩
        rw [Run.out_of_correct A R3 (by simp [R3, hzs]),
          Run.out_of_correct A R2 (by simp [R2, Run.quiet, hpq.symm]), hq3 σ hσ]
    · refine Run.tokens_replay hU (Ri := R1) (R' := R3) (T := T) (fun z σ r hσ => ?_) τ hτ y r m
        hm x hx
      by_cases hzs : z = y
      · subst hzs; exact Or.inr (Or.inl ⟨hs3, by simp [R1, Run.quiet, hqs.symm]⟩)
      by_cases hzp : z = p
      · subst hzp
        refine Or.inl ⟨by simp [R3, hzs], ?_⟩
        rw [Run.out_of_correct A R3 (by simp [R3, hzs]),
          Run.out_of_correct A R1 (by simp [R1, Run.quiet, hpq]), hp3 σ hσ]
      · obtain rfl := hall z hzs hzp
        refine Or.inr (Or.inr fun m hm => ?_)
        rw [quiet_out_nil (mem_singleton_self _)] at hm; simp at hm
    · simp at hm
  refine hab (hA.agreement R3 hR3 hR3A p (by simp [R3, hps]) q (by simp [R3, hqs]) a b
    ⟨T1, ?_⟩ ⟨T2, ?_⟩)
  · rw [hp3 T1 (le_max_left _ _), hT1]; rfl
  · rw [hq3 T2 (le_max_right _ _), hT2]; simp [R2, Run.quiet]

/-- **Partially synchronous Byzantine broadcast is impossible for `n ∈ {2, 3}`** (with `f ≥ 1`,
authenticated, any unforging algorithm, at least two values). -/
theorem psyncBB_impossible (hU : A.Unforging Au) {s : P} {f D : ℕ} (hf : 1 ≤ f)
    (h23 : Fintype.card P = 2 ∨ Fintype.card P = 3) {a b : V} (hab : a ≠ b) :
    ¬ IsPsyncBB Au A s f D := by
  rcases h23 with h | h
  · exact psyncBB_impossible_two (A := A) (Au := Au) hf h hab
  · exact psyncBB_impossible_three hU hf h hab

/-- **Theorem 6 of [ANRX21]** for all `n ≥ 2`, `f ≥ 1`: partially synchronous BB does not have
good-case latency of one round. (False for `n = 1`, see `theorem_7_false_one`.) -/
theorem theorem_6_all (hU : A.Unforging Au) {s : P} {f D : ℕ} (hD : 0 < D) (hf : 1 ≤ f)
    (h2 : 2 ≤ Fintype.card P) {a b : V} (hab : a ≠ b) (hA : IsPsyncBB Au A s f D) :
    ¬ PsyncGoodCaseRounds Au A s f D 1 := by
  by_cases h3 : 3 ≤ Fintype.card P
  · exact theorem_6_rounds hU hD hf h3 hab hA
  · exact absurd hA (psyncBB_impossible hU hf (by omega) hab)

/-- **Theorem 7 of [ANRX21]** for all `n ≥ 2`, `f ≥ 1` with `n ≤ 5f − 2`: partially synchronous
BB does not have good-case latency of two rounds. (False for `n = 1`, see
`theorem_7_false_one`.) -/
theorem theorem_7_all (hU : A.Unforging Au) {s : P} {f D : ℕ} (hD : 0 < D) (hf : 1 ≤ f)
    (h2 : 2 ≤ Fintype.card P) (hn : Fintype.card P ≤ 5 * f - 2) {a b : V} (hab : a ≠ b)
    (hA : IsPsyncBB Au A s f D) : ¬ PsyncGoodCaseRounds Au A s f D 2 := by
  by_cases h : 2 ≤ f ∧ 3 ≤ Fintype.card P
  · exact theorem_7 hU hD h.1 h.2 hn hab hA
  · exact absurd hA (psyncBB_impossible hU hf (by omega) hab)

end GoodCaseLatencyBB
