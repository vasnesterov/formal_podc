import Papers.PODC2019.ComposableCRN.Basic

/-!
# Necessary conditions for oblivious computability

* Observation 2.1: obliviously-computable functions are nondecreasing.
* Lemma 4.1: the "contradiction sequence" criterion (via Dickson's lemma).
* `max` is not obliviously-computable (§1.2, §4).
* Observation 9.1: functions obliviously-computable without a leader are superadditive.

All results hold for the general `FunCRN` model; the distinctness of the input, output and
leader species is not used.
-/

set_option linter.unnecessarySeqFocus false

namespace Podc.ComposableCRN

open CRN

variable {ι : Type} [Fintype ι]

namespace FunCRN

variable {S : Type} [DecidableEq S] (C : FunCRN S ι)

/-- Core of Observation 2.1: an output-oblivious CRN stably computing `f` forces `f` to be
nondecreasing. -/
theorem monotone_of_stablyComputes (hO : C.OutputOblivious) {f : (ι → ℕ) → ℕ}
    (hf : C.StablyComputes f) : Monotone f := by
  intro a b hab
  obtain ⟨O, hO1, hO2, -⟩ := hf.exists a
  -- `I_b = I_a + I_{b-a}` reaches `O + I_{b-a}`
  have hb : b = a + (b - a) := by
    funext i; have : a i ≤ b i := hab i; simp only [Pi.add_apply, Pi.sub_apply]; omega
  have hreach : C.Reach (C.init b) (O + C.inputConf (b - a)) := by
    rw [hb, C.init_add]; simpa [← hb] using hO1.add (C.inputConf (b - a))
  obtain ⟨O', hO'1, hO'2, -⟩ := hf b _ hreach
  have := hO.reach_le hO'1
  simp only [Pi.add_apply] at this
  omega

end FunCRN

/-- Observation 2.1: an obliviously-computable function is nondecreasing. -/
theorem ObliviouslyComputable.monotone {f : (ι → ℕ) → ℕ} (h : ObliviouslyComputable f) :
    Monotone f := by
  obtain ⟨S, _, _, C, -, hO, hf⟩ := h
  exact C.monotone_of_stablyComputes hO hf

/-- Lemma 4.1: if there is a sequence `a₁, a₂, …` such that for all `i < j` some `Δᵢⱼ` satisfies
`f(aᵢ + Δᵢⱼ) - f(aᵢ) > f(aⱼ + Δᵢⱼ) - f(aⱼ)`, then `f` is not obliviously-computable.
(The paper asks the sequence to be increasing; this is not needed.) -/
theorem not_obliviouslyComputable_of_seq (f : (ι → ℕ) → ℕ) (a : ℕ → ι → ℕ)
    (Δ : ℕ → ℕ → ι → ℕ)
    (h : ∀ i j, i < j →
      (f (a j + Δ i j) : ℤ) - f (a j) < (f (a i + Δ i j) : ℤ) - f (a i)) :
    ¬ ObliviouslyComputable f := by
  rintro ⟨S, _, _, C, -, hO, hf⟩
  choose O hO1 hO2 _ using fun i => hf.exists (a i)
  -- Dickson's lemma
  obtain ⟨i, j, hij, hle⟩ := wellQuasiOrdered_le (α := S → ℕ) O
  set D := C.inputConf (Δ i j)
  -- from `I_{aᵢ+Δ}`: reach `Oᵢ + D`, then a correct configuration `O'`
  have hi : C.Reach (C.init (a i + Δ i j)) (O i + D) := by
    rw [C.init_add]; exact (hO1 i).add D
  obtain ⟨O', hO'1, hO'2, -⟩ := hf _ _ hi
  -- from `I_{aⱼ+Δ}`: reach `Oⱼ + D = (Oᵢ + D) + (Oⱼ - Oᵢ)`, then `O' + (Oⱼ - Oᵢ)`
  have hsplit : O j + D = (O i + D) + (O j - O i) := by
    funext s; have : O i s ≤ O j s := hle s; simp only [Pi.add_apply, Pi.sub_apply]; omega
  have hj : C.Reach (C.init (a j + Δ i j)) (O' + (O j - O i)) := by
    rw [C.init_add]
    exact ((hO1 j).add D).trans (hsplit ▸ hO'1.add (O j - O i))
  obtain ⟨O'', hO''1, hO''2, -⟩ := hf _ _ hj
  have h1 := hO.reach_le hO''1
  have h2 := h i j hij
  have h3 : O i C.Y ≤ O j C.Y := hle C.Y
  have h4 := hO2 i
  have h5 := hO2 j
  simp only [Pi.add_apply, Pi.sub_apply] at h1
  omega

/-- `max : ℕ² → ℕ` is semilinear and nondecreasing, but not obliviously-computable (§1.2, §4:
Lemma 4.1 with `aᵢ = (i, 0)`, `Δᵢⱼ = (0, j)`). -/
theorem max_not_obliviouslyComputable :
    ¬ ObliviouslyComputable (fun x : Fin 2 → ℕ => max (x 0) (x 1)) := by
  refine not_obliviouslyComputable_of_seq _ (fun i => ![i, 0]) (fun _ j => ![0, j]) ?_
  intro i j hij
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp; omega

/-- Observation 9.1: a function obliviously-computable by a leaderless CRN is superadditive. -/
theorem LeaderlessObliviouslyComputable.superadditive {f : (ι → ℕ) → ℕ}
    (h : LeaderlessObliviouslyComputable f) (x z : ι → ℕ) : f x + f z ≤ f (x + z) := by
  obtain ⟨S, _, _, C, hL, hO, hf⟩ := h
  have hinit : ∀ w, C.init w = C.inputConf w := fun w => by
    funext s; simp [FunCRN.init, FunCRN.leaderConf, hL]
  obtain ⟨Ox, hx1, hx2, -⟩ := hf.exists x
  obtain ⟨Oz, hz1, hz2, -⟩ := hf.exists z
  have hreach : C.Reach (C.init (x + z)) (Ox + Oz) := by
    rw [C.init_add, hinit x, hinit z] at *
    exact (hx1.add _).trans (hz1.add_left Ox)
  obtain ⟨O, hO1, hO2, -⟩ := hf _ _ hreach
  have := hO.reach_le hO1
  simp only [Pi.add_apply] at this
  omega

end Podc.ComposableCRN

namespace Podc.ComposableCRN

/-- `max : ℕ² → ℕ` is semilinear (§1.2): its graph is the union of the linear sets
`⟨((1,1),1), ((1,0),1)⟩` (where `x₀ ≥ x₁`) and `⟨((1,1),1), ((0,1),1)⟩` (where `x₁ ≥ x₀`). -/
theorem max_isSemilinearFun : IsSemilinearFun (fun x : Fin 2 → ℕ => max (x 0) (x 1)) := by
  set u : (Fin 2 → ℕ) × ℕ := (![1, 1], 1)
  set v : (Fin 2 → ℕ) × ℕ := (![1, 0], 1)
  set w : (Fin 2 → ℕ) × ℕ := (![0, 1], 1)
  have h : {p : (Fin 2 → ℕ) × ℕ | max (p.1 0) (p.1 1) = p.2} =
      (AddSubmonoid.closure {u, v} : Set _) ∪ (AddSubmonoid.closure {u, w} : Set _) := by
    ext ⟨x, c⟩
    simp only [Set.mem_ofPred_eq, Set.mem_union, SetLike.mem_coe, AddSubmonoid.mem_closure_pair]
    constructor
    · rintro rfl
      rcases le_total (x 1) (x 0) with h | h
      · refine .inl ⟨x 1, x 0 - x 1, ?_⟩
        simp only [u, v, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, Prod.mk.injEq]
        refine ⟨funext fun i => ?_, by omega⟩
        fin_cases i <;> simp <;> omega -- one case needs `omega`
      · refine .inr ⟨x 0, x 1 - x 0, ?_⟩
        simp only [u, w, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, Prod.mk.injEq]
        refine ⟨funext fun i => ?_, by omega⟩
        fin_cases i <;> simp <;> omega -- one case needs `omega`
    · rintro (⟨m, n, hmn⟩ | ⟨m, n, hmn⟩) <;>
      · simp only [u, v, w, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one,
          Prod.mk.injEq] at hmn
        obtain ⟨hx, rfl⟩ := hmn
        subst hx
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        simp
  rw [IsSemilinearFun, h]
  exact (IsLinearSet.closure_of_finite (by simp)).isSemilinearSet.union
    (IsLinearSet.closure_of_finite (by simp)).isSemilinearSet

end Podc.ComposableCRN
