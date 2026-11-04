import Papers.PODC2012.DAPUniversalConstruction.Impossibility

/-!
# Theorem 5: the non-terminating `Search`

We assemble the infinite execution `α' = α₁ α₂ α₃ α₄ β₄² α₅ γ₅ α₆ γ₆ ⋯` of Section 4 (`exec`):
`q`'s appends interleaved with `p`'s `Search(0)`, where `p` only takes the steps of `βᵢⁱ⁻²`.
Each finite prefix is an execution (`run_exec`: the steps of `p` and of the next append commute,
since they do not contend), `p` never returns, and by `M_lt` it takes infinitely many steps. This
contradicts wait-freedom.

* `theorem_5_list` — Theorem 5 for the implementation of the list produced by the universal
  construction;
* `theorem_5` — Theorem 5: no feebly disjoint-access parallel universal construction (satisfying
  Assumption 3) is wait-free.
-/

set_option linter.unusedSectionVars false

namespace Podc.DAPUniversalConstruction

open Cslib.SharedMemory Impl

variable {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

section Exec

variable (I : Impl listSpec B P L) (p q : P)

/-- The steps of `p` and `q` after `p`'s invocation of `Search(0)`, up to `γ_{k+4}`:
`β₄² α₅ γ₅ ⋯ α_{k+4} γ_{k+4}` (paper indices). -/
noncomputable def rest : ℕ → List (Label P listSpec)
  | 0 => I.soloLabels p (Dc I p q 4) (M I p q 4)
  | k + 1 => rest k ++ (seg I q f₀ (k + 4) ++
      I.soloLabels p ((I.soloStep p)^[M I p q (k + 4)] (Dc I p q (k + 4 + 1)))
        (M I p q (k + 4 + 1) - M I p q (k + 4)))

/-- The prefix of the infinite execution `α'` ending with `γ_{k+4}`. -/
noncomputable def exec (k : ℕ) : List (Label P listSpec) :=
  pre I q f₀ 4 ++ .inv p (.search 0) :: rest I p q k

end Exec

variable {I : Impl listSpec B P L} {p q : P}
variable (hall : ∀ r o, I.allowed r o) (hOF : I.ObstructionFree)
  (hvo : ImplValueOblivious I LOp.append) (hlin : I.Linearizable) (hpq : p ≠ q)
include hall hOF hvo hlin hpq

omit hall hOF hvo hlin hpq in
lemma pending_of_le {D : Config listSpec B P L} {m m' : ℕ} (hmm : m ≤ m')
    (h : ((I.soloStep p)^[m'] D).pend p ≠ none) : ((I.soloStep p)^[m] D).pend p ≠ none := by
  intro hm
  apply h
  rw [show m' = (m' - m) + m by omega, Function.iterate_add_apply,
    iterate_soloStep_of_idle hm, hm]

omit hall hOF hvo hlin hpq in
lemma countP_soloLabels {D : Config listSpec B P L} {m : ℕ}
    (h : ((I.soloStep p)^[m] D).pend p ≠ none) :
    (I.soloLabels p D m).countP (Label.isTauOf p) = m := by
  rw [List.countP_eq_length.2 (fun ℓ hℓ => by rw [eq_tau_of_pending h ℓ hℓ]; simp),
    I.soloLabels_length p D m (fun j hj => pending_of_le hj.le h)]

/-- Each prefix of `α'` is an execution; it ends in the configuration reached by running
`α₁ ⋯ α_{k+4}` and then `β_{k+4}^{k+2}`. -/
lemma run_exec (k : ℕ) :
    I.run (exec I p q k) = some ((I.soloStep p)^[M I p q (k + 4)] (Dc I p q (k + 4))) := by
  induction k with
  | zero =>
    simp only [exec, rest]
    rw [run_append_of_eq I (run_pre (q := q) hall hOF f₀ 4).1, runFrom_cons,
      step_dcfg hall hOF p f₀ 4, Option.bind_some, runFrom_soloLabels]
  | succ k ih =>
    generalize hi : k + 4 = i at ih
    have hexec : exec I p q (k + 1) = exec I p q k ++ (seg I q f₀ i ++
        I.soloLabels p ((I.soloStep p)^[M I p q i] (Dc I p q (i + 1)))
          (M I p q (i + 1) - M I p q i)) := by
      subst hi; simp only [exec, rest, List.cons_append, List.append_assoc]
    rw [hexec, show k + 1 + 4 = i + 1 by omega, run_append_of_eq I ih]
    -- commute `β_i^{i-2}` (run from `C_i`) with the append `α_{i+1}`
    have hspec := blen_spec (exists_stop (p := p) (q := q) hOF
      (reachable_Dc (p := p) (q := q) hall hOF i) (i - 3))
    set α := Label.inv p (LOp.search 0) :: I.soloLabels p (Dc I p q i) (M I p q i) with hα
    have h1 : I.runFrom (cfg I q f₀ i) α = some ((I.soloStep p)^[M I p q i] (Dc I p q i)) := by
      rw [hα, runFrom_cons, step_dcfg hall hOF p f₀ i, Option.bind_some, runFrom_soloLabels]
    obtain ⟨h2, hβ, -⟩ := run_seg (q := q) hall hOF f₀ i
    have hαp : ∀ ℓ ∈ α, ℓ.proc = p := by
      intro ℓ hℓ
      rcases List.mem_cons.1 hℓ with rfl | hℓ
      · rfl
      · exact I.soloLabels_proc p _ _ ℓ hℓ
    have hacc : ∀ b ∈ I.accessed (cfg I q f₀ i) α,
        ∃ m < M I p q i, I.SoloAcc p b ((I.soloStep p)^[m] (Dc I p q i)) := by
      intro b hb
      rw [hα, accessed_cons_of_step (step_dcfg hall hOF p f₀ i), Set.mem_union,
        mem_accessed_soloLabels] at hb
      rcases hb with ⟨r, o, k, h, -⟩ | hb
      · cases h
      · exact hb
    have hwr : ∀ b ∈ I.written (cfg I q f₀ i) α,
        ∃ m < M I p q i, I.SoloWr p b ((I.soloStep p)^[m] (Dc I p q i)) := by
      intro b hb
      rw [hα, written_cons_of_step (step_dcfg hall hOF p f₀ i), Set.mem_union,
        mem_written_soloLabels] at hb
      rcases hb with ⟨r, o, k, h, -⟩ | hb
      · cases h
      · exact hb
    obtain ⟨D, hD1, hD2⟩ := runFrom_comm hpq hαp hβ h1 h2
      (fun b hb hbw => by
        obtain ⟨m, hm, hm'⟩ := hacc b hb
        exact hspec.2 m hm (Or.inl ⟨i, by omega, b, Or.inl ⟨hbw, hm'⟩⟩))
      (fun b hb hba => by
        obtain ⟨m, hm, hm'⟩ := hwr b hb
        exact hspec.2 m hm (Or.inl ⟨i, by omega, b, Or.inr ⟨hba, hm'⟩⟩))
    -- from `C_{i+1}`, `p` takes the same steps
    have hstab := blen_stable hall hOF hvo hpq (t := i - 3) (n := i) (n' := i + 1) (by omega)
      (by omega)
    have hsame : I.soloLabels p (Dc I p q i) (M I p q i) =
        I.soloLabels p (Dc I p q (i + 1)) (M I p q i) := (hstab.2 (M I p q i) le_rfl).2
    rw [hα, hsame, runFrom_cons, step_dcfg hall hOF p f₀ (i + 1), Option.bind_some,
      runFrom_soloLabels] at hD2
    cases hD2
    rw [runFrom_append_of_eq I hD1, runFrom_soloLabels, ← Function.iterate_add_apply,
      Nat.sub_add_cancel (M_mono hall hOF hvo hpq (by omega))]

/-- In `α'`, the only labels of `p` after its invocation are internal steps. -/
lemma rest_labels (k : ℕ) : ∀ ℓ ∈ rest I p q k, ℓ = .tau p ∨ ℓ.proc = q := by
  induction k with
  | zero =>
    intro ℓ hℓ
    exact Or.inl (eq_tau_of_pending (pending_bad hall hOF hvo hlin hpq (by omega)).1 ℓ hℓ)
  | succ k ih =>
    intro ℓ hℓ
    simp only [rest, List.mem_append] at hℓ
    rcases hℓ with hℓ | hℓ | hℓ
    · exact ih ℓ hℓ
    · exact Or.inr ((run_seg (q := q) hall hOF f₀ (k + 4)).2.1 ℓ hℓ)
    · left
      have hpend := (pending_bad hall hOF hvo hlin hpq (i := k + 4 + 1) (by omega)).1
      have hle := M_mono hall hOF hvo hpq (i := k + 4) (by omega)
      rw [show M I p q (k + 4 + 1) = M I p q (k + 4) + (M I p q (k + 4 + 1) - M I p q (k + 4))
        by omega] at hpend
      have hl := eq_tau_of_pending hpend
      rw [soloLabels_add] at hl
      exact hl ℓ (List.mem_append_right _ hℓ)

/-- `p` takes `M (k+4)` steps in the `k`-th prefix of `α'`. -/
lemma countP_rest (k : ℕ) : (rest I p q k).countP (Label.isTauOf p) = M I p q (k + 4) := by
  induction k with
  | zero => exact countP_soloLabels (pending_bad hall hOF hvo hlin hpq (by omega)).1
  | succ k ih =>
    simp only [rest, List.countP_append, ih]
    have hseg : (seg I q f₀ (k + 4)).countP (Label.isTauOf p) = 0 := by
      rw [List.countP_eq_zero]
      intro ℓ hℓ
      have := (run_seg (q := q) hall hOF f₀ (k + 4)).2.1 ℓ hℓ
      cases ℓ with
      | tau r =>
        simp only [Label.proc] at this; subst this
        simp [Label.isTauOf_tau, Ne.symm hpq]
      | _ => simp
    have hpend := (pending_bad hall hOF hvo hlin hpq (i := k + 4 + 1) (by omega)).1
    have hle := M_mono hall hOF hvo hpq (i := k + 4) (by omega)
    have hpend' : ((I.soloStep p)^[M I p q (k + 4 + 1) - M I p q (k + 4)]
        ((I.soloStep p)^[M I p q (k + 4)] (Dc I p q (k + 4 + 1)))).pend p ≠ none := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]; exact hpend
    rw [hseg, countP_soloLabels hpend', show k + 1 + 4 = k + 4 + 1 by omega]
    omega

/-- `M` is unbounded: `γⱼ` is nonempty for infinitely many `j`. -/
lemma M_unbounded (hdap : FeeblyDAP I listDataSet) (j : ℕ) : j ≤ M I p q (3 * j + 4) := by
  induction j with
  | zero => omega
  | succ j ih =>
    have := M_lt hall hOF hvo hlin hdap hpq (i := 3 * j + 4) (by omega)
    rw [show 3 * (j + 1) + 4 = 3 * j + 4 + 3 by omega]
    omega

omit hall hOF hvo hlin hpq in
/-- The execution of the first appends has no labels of `p`. -/
lemma pre_labels (hall : ∀ r o, I.allowed r o) (hOF : I.ObstructionFree) (hpq : p ≠ q) :
    ∀ ℓ ∈ pre I q f₀ 4, ℓ.proc ≠ p := fun ℓ h => by
  rw [(run_pre (q := q) hall hOF f₀ 4).2.2.2.1 ℓ h]; exact Ne.symm hpq

omit hall hOF hvo hlin hpq in
lemma length_exec (hall : ∀ r o, I.allowed r o) (hOF : I.ObstructionFree) (k : ℕ) :
    k ≤ (exec I p q k).length := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hseg : seg I q f₀ (k + 4) ≠ [] := by
      intro h
      have := (run_seg (q := q) hall hOF f₀ (k + 4)).2.2
      rw [h] at this; simp at this
    have : (exec I p q k).length + (seg I q f₀ (k + 4)).length ≤
        (exec I p q (k + 1)).length := by
      simp only [exec, rest, List.length_append, List.length_cons]; omega
    have h2 := List.length_pos_iff.2 hseg
    omega

end Podc.DAPUniversalConstruction

namespace Podc.DAPUniversalConstruction

open Cslib.SharedMemory Impl

variable {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

/-- **Theorem 5**, for the implementation of the singly-linked list produced by a universal
construction: if it is linearizable, feebly disjoint-access parallel (Definition 1) and satisfies
the value-obliviousness assumption for `Append` (Assumption 3), then it is not wait-free. More
precisely, in the execution `α'` a process `p` performing `Search(0)` takes infinitely many steps
without returning while `q` keeps appending. -/
theorem theorem_5_list (I : Impl listSpec B P L) {p q : P} (hpq : p ≠ q)
    (hall : ∀ r o, I.allowed r o) (hlin : I.Linearizable) (hdap : FeeblyDAP I listDataSet)
    (hvo : ImplValueOblivious I LOp.append) : ¬ I.WaitFree := by
  intro hwf
  have hOF := Impl.WaitFree.obstructionFree I hwf
  obtain ⟨e, he1, he2⟩ := I.exists_infExec_of_chain (exec I p q)
    (fun k => by
      have : exec I p q (k + 1) = exec I p q k ++ (seg I q f₀ (k + 4) ++
          I.soloLabels p ((I.soloStep p)^[M I p q (k + 4)] (Dc I p q (k + 4 + 1)))
            (M I p q (k + 4 + 1) - M I p q (k + 4))) := by
        simp only [exec, rest, List.cons_append, List.append_assoc]
      rw [this]; exact List.prefix_append _ _)
    (length_exec hall hOF) (fun k => ⟨_, run_exec hall hOF hvo hlin hpq k⟩)
  set n₀ := (pre I q f₀ 4).length + 1 with hn₀
  obtain ⟨N, hN⟩ := hwf e p n₀ (fun m hm hidle => by
    -- `p` has invoked `Search(0)` and not returned
    have hrun := he2 m m (length_exec hall hOF m)
    set α := (exec I p q m).take m with hα
    have hsplit : α = pre I q f₀ 4 ++ .inv p (.search 0) ::
        (rest I p q m).take (m - n₀) := by
      rw [hα, exec, List.take_append, List.take_of_length_le (by omega),
        show m - (pre I q f₀ 4).length = (m - n₀) + 1 by omega, List.take_succ_cons]
    have hR : ∀ ℓ ∈ (rest I p q m).take (m - n₀), ℓ.invOf p = none ∧ ℓ.retOf p = none := by
      intro ℓ hℓ
      rcases rest_labels hall hOF hvo hlin hpq m ℓ (List.mem_of_mem_take hℓ) with h | h
      · subst h; simp
      · exact ⟨Label.invOf_eq_none_of_proc_ne (by rw [h]; exact Ne.symm hpq),
          Label.retOf_eq_none_of_proc_ne (by rw [h]; exact Ne.symm hpq)⟩
    have hops : opsOf α p = [.search 0] := by
      rw [hsplit, opsOf_append, opsOf_eq_nil_of_proc_ne (pre_labels hall hOF hpq), opsOf_cons]
      simp only [Label.invOf_inv, List.nil_append]
      rw [show opsOf ((rest I p q m).take (m - n₀)) p = [] by
        simp only [opsOf, List.filterMap_eq_nil_iff]; exact fun ℓ h => (hR ℓ h).1]
      simp
    have hresps : respsOf α p = [] := by
      rw [hsplit, respsOf_append, respsOf_eq_nil_of_proc_ne (pre_labels hall hOF hpq),
        respsOf_cons]
      simp only [List.nil_append, Label.retOf_inv, Option.toList_none]
      simp only [respsOf, List.filterMap_eq_nil_iff]; exact fun ℓ h => (hR ℓ h).2
    have := I.run_idle_counts hrun hidle
    rw [hops, hresps] at this
    simp at this)
  -- but `p` takes a step after position `N`
  obtain ⟨k, hk⟩ : ∃ k, N < M I p q (k + 4) :=
    ⟨3 * (N + 1), by have := M_unbounded hall hOF hvo hlin hpq hdap (N + 1); omega⟩
  have hcount : (exec I p q k).countP (Label.isTauOf p) = M I p q (k + 4) := by
    rw [exec, List.countP_append, List.countP_cons, countP_rest hall hOF hvo hlin hpq,
      List.countP_eq_zero.2 (fun ℓ h => by
        have := pre_labels hall hOF hpq ℓ h
        cases ℓ <;> simp_all [Label.proc])]
    simp
  have hdrop : 0 < ((exec I p q k).drop N).countP (Label.isTauOf p) := by
    have h1 := List.countP_append (p := Label.isTauOf p) (l₁ := (exec I p q k).take N)
      (l₂ := (exec I p q k).drop N)
    rw [List.take_append_drop, hcount] at h1
    have h2 : ((exec I p q k).take N).countP (Label.isTauOf p) ≤ N :=
      (List.countP_le_length).trans (List.length_take_le _ _)
    omega
  obtain ⟨ℓ, hℓ, hτ⟩ := List.countP_pos_iff.1 hdrop
  obtain ⟨j, hj, hjℓ⟩ := List.getElem_of_mem hℓ
  rw [List.getElem_drop] at hjℓ
  have hlbl := he1 k (N + j) (by simp at hj; omega)
  rw [hjℓ, (Label.isTauOf_eq_true_iff).1 hτ] at hlbl
  exact hN (N + j) (by omega) hlbl

/-- **Theorem 5.** No feebly disjoint-access parallel universal construction is wait-free.
Here a universal construction is linearizable, lets every process invoke every operation, and
satisfies the value-obliviousness assumption (Assumption 3); there are at least two processes.

The hypotheses range over all `SeqDS`, whose data sets are arbitrary annotations rather than read
off sequential code; with degenerate annotations (e.g. all data sets empty) they are stronger
than the paper's. The faithful content is `theorem_5_list`, which only constrains the
implementation of the list, and from which this is derived. -/
theorem theorem_5 (U : UniversalConstruction P) (hP : ∃ p q : P, p ≠ q) (hall : U.AllowsAll)
    (hlin : U.Linearizable) (hvo : U.ValueObliviousAssumption) (hdap : U.FeeblyDAP) :
    ¬ U.WaitFree := by
  intro hwf
  obtain ⟨p, q, hpq⟩ := hP
  let _ := (U listDS).decι
  exact theorem_5_list (U listDS).impl hpq (hall listDS) (hlin listDS) (hdap listDS)
    (hvo listDS ℤ LOp.append append_valueOblivious) (hwf listDS)

end Podc.DAPUniversalConstruction
