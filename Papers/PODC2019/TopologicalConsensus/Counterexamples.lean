import Papers.PODC2019.TopologicalConsensus.Characterization

/-!
# Counterexamples to the "if" directions of Theorems 5.2 and 5.3

1. `CexUniform.theorem_5_2_false`: the paper's Theorem 5.2 ("uniform consensus is solvable iff
   `Σ` has a `d_u`-clopen partition with validity") is false, even for lock-step synchronous
   full-information models (`LockstepRecall` holds). Two processes that never communicate; the view
   of a process is (time, own input). Executions: `α` (inputs `0,0`), `β` (inputs `1,1`) and `δ`
   (inputs `0,1`) in which process `0` is disobedient from time `1` on (it suffers, say, an
   omission failure that it cannot observe). Since `d_u` only counts processes that are obedient in
   *both* executions, `d_u(α, δ) = 1/2`, and `{α}`, `{β, δ}` is a `d_u`-clopen partition with
   validity. But process `0` decides `0` in `α`, hence also in `δ` (same view), while process `1`
   decides `1` in `β`, hence also in `δ`: uniform agreement fails in `δ`.
   (The corrected distance `d_uc` of `Characterization.lean` has `d_uc(α, δ) = 0`.)

2. `CexAsync.theorem_5_3_false_async`: in the generic model of Section 3 (weak clocks only), both
   theorems are false. Two non-communicating, always obedient processes whose view is
   (own input, number of own steps); global time is not visible. In `α` (inputs `0,0`) and `β`
   (inputs `1,1`) both processes step at even times, in `δ` (inputs `0,1`) at odd times. All
   pairwise distances are `≥ 1/2`, so `Σ` is discrete and `{α, δ}`, `{β}` is a clopen partition with
   validity, but consensus is impossible: process `0` sees the same views in `α` and `δ` (only
   shifted in time), process `1` the same views in `β` and `δ`.
-/

namespace TopoConsensus

open Set Filter Topology

/-! ### Counterexample 1: Theorem 5.2 with disobedient processes -/

namespace CexUniform

/-- Configurations: (time, input of process 0, input of process 1, process 0 has failed). -/
abbrev Conf := ℕ × Bool × Bool × Bool

/-- The input vector of a configuration. -/
def inp (c : Conf) : Fin 2 → Bool := fun p => if p = 0 then c.2.1 else c.2.2.1

def α : ℕ → Conf := fun t => (t, false, false, false)
def β : ℕ → Conf := fun t => (t, true, true, false)
def δ : ℕ → Conf := fun t => (t, false, true, decide (1 ≤ t))

/-- The model: views are (time, own input); process 0 is disobedient in `δ` from time 1 on. -/
def M : Model (Fin 2) Conf Bool where
  indist p c d := c.1 = d.1 ∧ inp c p = inp d p
  indist_equiv p := ⟨fun _ => ⟨rfl, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
    fun h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩⟩
  Ob c := if c.2.2.2 then {1} else univ
  clock _ c := c.1
  input := inp
  adm := {α, β, δ}
  ob_anti := by
    intro γ hγ s t hst
    simp only [mem_insert_iff, mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl <;> simp only [α, β, δ]
    · exact le_rfl
    · exact le_rfl
    · by_cases ht : 1 ≤ t
      · simp [ht]
      · have : s = 0 := by omega
        have : t = 0 := by omega
        subst_vars; exact le_rfl
  ob_init := by
    intro γ hγ
    simp only [mem_insert_iff, mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl <;> simp [α, β, δ]
  ob_nonempty := by
    intro γ hγ
    refine ⟨1, mem_iInter.2 fun t => ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl <;> simp only [α, β, δ] <;> split_ifs <;> simp
  clock_le := by
    intro p γ hγ c t h
    simp only [mem_insert_iff, mem_singleton_iff] at hγ
    have h1 := h.1
    rcases hγ with rfl | rfl | rfl <;> exact le_of_eq h1
  clock_tendsto := by
    intro γ hγ p _
    simp only [mem_insert_iff, mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl <;> exact tendsto_id
  input_local := by
    intro p γ hγ γ' hγ' s t h
    simp only [mem_insert_iff, mem_singleton_iff] at hγ hγ'
    have h2 := h.2
    rcases hγ with rfl | rfl | rfl <;> rcases hγ' with rfl | rfl | rfl <;> exact h2
  init_unique := by
    intro γ hγ γ' hγ' h
    simp only [mem_insert_iff, mem_singleton_iff] at hγ hγ'
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    rcases hγ with rfl | rfl | rfl <;> rcases hγ' with rfl | rfl | rfl <;>
      simp_all [inp, α, β, δ]

theorem mem_adm {γ : ℕ → Conf} : γ ∈ M.adm ↔ γ = α ∨ γ = β ∨ γ = δ := by
  simp [M]

theorem lockstepRecall : M.LockstepRecall := by
  intro p γ hγ γ' hγ' s t h
  rw [mem_adm] at hγ hγ'
  have ht : s = t := by
    have := h.1
    rcases hγ with rfl | rfl | rfl <;> rcases hγ' with rfl | rfl | rfl <;> exact this
  subst ht
  refine ⟨rfl, fun u _ => ⟨?_, ?_⟩⟩
  · rcases hγ with rfl | rfl | rfl <;> rcases hγ' with rfl | rfl | rfl <;> rfl
  · have := h.2
    rcases hγ with rfl | rfl | rfl <;> rcases hγ' with rfl | rfl | rfl <;> exact this

/-- The labelling `{α} ↦ 0`, `{β, δ} ↦ 1`: the input of process 1. -/
def lab (γ : M.adm) : Bool := ((γ : ℕ → Conf) 0).2.2.1

theorem isOpen_lab (v : Bool) : IsOpen[M.τU] (lab ⁻¹' {v}) := by
  rw [Model.isOpen_τU_iff]
  rintro ⟨γ, hγ⟩ hv
  refine ⟨1, ?_⟩
  rintro ⟨γ', hγ'⟩ ⟨p, hok⟩
  simp only [mem_preimage, mem_singleton_iff] at hv ⊢
  rw [← hv]
  have h0 := hok 0 (by norm_num)
  have h1 := hok 1 le_rfl
  rw [mem_adm] at hγ hγ'
  rcases hγ with rfl | rfl | rfl <;> rcases hγ' with rfl | rfl | rfl <;> fin_cases p <;>
    simp_all [lab, Model.okP, M, inp, α, β, δ]

theorem valid_lab (γ : M.adm) (v : Bool) (hγ : M.Valent γ v) : lab γ = v := by
  obtain ⟨γ, hγ'⟩ := γ
  have h0 := hγ 0
  have h1 := hγ 1
  rw [mem_adm] at hγ'
  rcases hγ' with rfl | rfl | rfl <;> simp_all [lab, M, inp, α, β, δ]

theorem not_uniformSolvable : ¬ UniformSolvable M := by
  rintro ⟨A, hT, hUA, hV⟩
  have hα : α ∈ M.adm := mem_adm.2 (Or.inl rfl)
  have hβ : β ∈ M.adm := mem_adm.2 (Or.inr (Or.inl rfl))
  have hδ : δ ∈ M.adm := mem_adm.2 (Or.inr (Or.inr rfl))
  have hobe : ∀ γ, γ = α ∨ γ = β → ∀ p, p ∈ M.obe γ := by
    intro γ hγ p
    rw [Model.mem_obe]
    intro t
    rcases hγ with rfl | rfl <;> simp [M, α, β]
  -- process 0 decides 0 in α, hence in δ
  obtain ⟨w, t, hw⟩ := hT α hα 0 (hobe α (Or.inl rfl) 0)
  have hw0 : w = false := hV α hα false (fun p => by fin_cases p <;> rfl) 0
    (hobe α (Or.inl rfl) 0) w ⟨t, hw⟩
  subst hw0
  have hδ0 : A.dec 0 (δ t) = some false := by
    rw [← A.dec_indist 0 (α t) (δ t) ⟨rfl, rfl⟩, hw]
  -- process 1 decides 1 in β, hence in δ
  obtain ⟨w', t', hw'⟩ := hT β hβ 1 (hobe β (Or.inr rfl) 1)
  have hw1 : w' = true := hV β hβ true (fun p => by fin_cases p <;> rfl) 1
    (hobe β (Or.inr rfl) 1) w' ⟨t', hw'⟩
  subst hw1
  have hδ1 : A.dec 1 (δ t') = some true := by
    rw [← A.dec_indist 1 (β t') (δ t') ⟨rfl, rfl⟩, hw']
  exact absurd (hUA δ hδ 0 1 false true ⟨t, hδ0⟩ ⟨t', hδ1⟩) (by decide)

/-- **Theorem 5.2 ("if" direction) is false**: a lock-step synchronous full-information model
with a partition of `Σ` into `d_u`-clopen decision sets containing the valent executions, in
which uniform consensus is not solvable. -/
theorem theorem_5_2_false :
    ∃ M : Model (Fin 2) Conf Bool, M.LockstepRecall ∧
      (∃ lab : M.adm → Bool, (∀ v, IsClopen[M.τU] (lab ⁻¹' {v})) ∧
        ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v) ∧
      ¬ UniformSolvable M :=
  ⟨M, lockstepRecall, ⟨lab, @isClopen_fibers _ _ M.τU _ isOpen_lab, valid_lab⟩,
    not_uniformSolvable⟩

end CexUniform

/-! ### Counterexample 2: Theorems 5.2 and 5.3 in the asynchronous generic model -/

namespace CexAsync

/-- Configurations: (input of 0, input of 1, steps of 0, steps of 1). -/
abbrev Conf := Bool × Bool × ℕ × ℕ

def inp (c : Conf) : Fin 2 → Bool := fun p => if p = 0 then c.1 else c.2.1
def steps (c : Conf) : Fin 2 → ℕ := fun p => if p = 0 then c.2.2.1 else c.2.2.2

/-- Both processes step at even times. -/
def α : ℕ → Conf := fun t => (false, false, t / 2, t / 2)
def β : ℕ → Conf := fun t => (true, true, t / 2, t / 2)
/-- Both processes step at odd times. -/
def δ : ℕ → Conf := fun t => (false, true, (t + 1) / 2, (t + 1) / 2)

/-- The model: the view of `p` is (own input, own step count); everybody is always obedient. -/
def M : Model (Fin 2) Conf Bool where
  indist p c d := inp c p = inp d p ∧ steps c p = steps d p
  indist_equiv p := ⟨fun _ => ⟨rfl, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
    fun h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩⟩
  Ob _ := univ
  clock p c := steps c p
  input := inp
  adm := {α, β, δ}
  ob_anti := fun _ _ _ _ _ => le_rfl
  ob_init := fun _ _ => rfl
  ob_nonempty := fun _ _ => ⟨0, mem_iInter.2 fun _ => trivial⟩
  clock_le := by
    intro p γ hγ c t h
    rw [h.2]
    simp only [mem_insert_iff, mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl <;> fin_cases p <;> simp [steps, α, β, δ] <;> omega
  clock_tendsto := by
    intro γ hγ p _
    simp only [mem_insert_iff, mem_singleton_iff] at hγ
    refine tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun t ht => ?_⟩
    rcases hγ with rfl | rfl | rfl <;> fin_cases p <;> simp [steps, α, β, δ] <;> omega
  input_local := by
    intro p γ hγ γ' hγ' s t h
    simp only [mem_insert_iff, mem_singleton_iff] at hγ hγ'
    have h2 := h.1
    rcases hγ with rfl | rfl | rfl <;> rcases hγ' with rfl | rfl | rfl <;> exact h2
  init_unique := by
    intro γ hγ γ' hγ' h
    simp only [mem_insert_iff, mem_singleton_iff] at hγ hγ'
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    rcases hγ with rfl | rfl | rfl <;> rcases hγ' with rfl | rfl | rfl <;>
      simp_all [inp, α, β, δ]

theorem mem_adm {γ : ℕ → Conf} : γ ∈ M.adm ↔ γ = α ∨ γ = β ∨ γ = δ := by
  simp [M]

/-- The labelling `{α, δ} ↦ 0`, `{β} ↦ 1`: the input of process 0. -/
def lab (γ : M.adm) : Bool := ((γ : ℕ → Conf) 0).1

theorem isOpen_lab_τU (v : Bool) : IsOpen[M.τU] (lab ⁻¹' {v}) := by
  rw [Model.isOpen_τU_iff]
  rintro ⟨γ, hγ⟩ hv
  refine ⟨1, ?_⟩
  rintro ⟨γ', hγ'⟩ ⟨p, hok⟩
  simp only [mem_preimage, mem_singleton_iff] at hv ⊢
  rw [← hv]
  have h0 := hok 0 (by norm_num)
  have h1 := hok 1 le_rfl
  rw [mem_adm] at hγ hγ'
  rcases hγ with rfl | rfl | rfl <;> rcases hγ' with rfl | rfl | rfl <;> fin_cases p <;>
    simp_all [lab, Model.okP, M, inp, steps, α, β, δ] <;>
    exact absurd (hok 1 le_rfl) (by norm_num)

theorem isOpen_lab_τNU (v : Bool) : IsOpen[M.τNU] (lab ⁻¹' {v}) := by
  rw [Model.isOpen_τNU_iff]
  rintro ⟨γ, hγ⟩ hv
  refine ⟨1, ?_⟩
  rintro ⟨γ', hγ'⟩ ⟨p, -, hok⟩
  simp only [mem_preimage, mem_singleton_iff] at hv ⊢
  rw [← hv]
  have h0 := hok 0 (by norm_num)
  have h1 := hok 1 le_rfl
  rw [mem_adm] at hγ hγ'
  rcases hγ with rfl | rfl | rfl <;> rcases hγ' with rfl | rfl | rfl <;> fin_cases p <;>
    simp_all [lab, Model.okP, M, inp, steps, α, β, δ] <;>
    exact absurd (hok 1 le_rfl) (by norm_num)

theorem valid_lab (γ : M.adm) (v : Bool) (hγ : M.Valent γ v) : lab γ = v := by
  obtain ⟨γ, hγ'⟩ := γ
  have h0 := hγ 0
  have h1 := hγ 1
  rw [mem_adm] at hγ'
  rcases hγ' with rfl | rfl | rfl <;> simp_all [lab, M, inp, α, β, δ]

theorem not_nonUniformSolvable : ¬ NonUniformSolvable M := by
  rintro ⟨A, hT, hA, hV⟩
  have hα : α ∈ M.adm := mem_adm.2 (Or.inl rfl)
  have hβ : β ∈ M.adm := mem_adm.2 (Or.inr (Or.inl rfl))
  have hδ : δ ∈ M.adm := mem_adm.2 (Or.inr (Or.inr rfl))
  have hobe : ∀ γ p, p ∈ M.obe γ := fun γ p => (Model.mem_obe M).2 fun _ => trivial
  obtain ⟨w, t, hw⟩ := hT α hα 0 (hobe α 0)
  have hw0 : w = false := hV α hα false (fun p => by fin_cases p <;> rfl) 0 (hobe α 0) w ⟨t, hw⟩
  subst hw0
  -- process 0 has the same view at time `t` in `α` as at time `2 (t / 2)` in `δ`
  have hδ0 : A.dec 0 (δ (2 * (t / 2))) = some false := by
    rw [← A.dec_indist 0 (α t) (δ (2 * (t / 2))) ⟨rfl, by simp [steps, α, δ]; omega⟩, hw]
  obtain ⟨w', t', hw'⟩ := hT β hβ 1 (hobe β 1)
  have hw1 : w' = true := hV β hβ true (fun p => by fin_cases p <;> rfl) 1 (hobe β 1) w' ⟨t', hw'⟩
  subst hw1
  have hδ1 : A.dec 1 (δ (2 * (t' / 2))) = some true := by
    rw [← A.dec_indist 1 (β t') (δ (2 * (t' / 2))) ⟨rfl, by simp [steps, β, δ]; omega⟩, hw']
  exact absurd (hA δ hδ 0 (hobe δ 0) 1 (hobe δ 1) false true ⟨_, hδ0⟩ ⟨_, hδ1⟩) (by decide)

/-- **Theorems 5.2 and 5.3 ("if" directions) are false in the generic model of Section 3**: a
model satisfying all of Section 3's assumptions (weak clocks, no faults) with a partition of `Σ`
into decision sets that are clopen in both the uniform and the non-uniform topology and contain
the valent executions, in which neither non-uniform nor uniform consensus is solvable. -/
theorem theorem_5_3_false_async :
    ∃ M : Model (Fin 2) Conf Bool,
      (∃ lab : M.adm → Bool, (∀ v, IsClopen[M.τNU] (lab ⁻¹' {v})) ∧
        (∀ v, IsClopen[M.τU] (lab ⁻¹' {v})) ∧ ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v) ∧
      ¬ NonUniformSolvable M ∧ ¬ UniformSolvable M :=
  ⟨M, ⟨lab, @isClopen_fibers _ _ M.τNU _ isOpen_lab_τNU,
    @isClopen_fibers _ _ M.τU _ isOpen_lab_τU, valid_lab⟩,
    not_nonUniformSolvable, fun ⟨A, hA⟩ => not_nonUniformSolvable ⟨A, hA.toNonUniform⟩⟩

end CexAsync

end TopoConsensus
