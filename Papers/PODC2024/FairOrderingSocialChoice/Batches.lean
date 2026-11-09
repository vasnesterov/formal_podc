import Papers.PODC2024.FairOrderingSocialChoice.Defs

/-!
# Lemma 3.6: recovering batches from a minimal-batch-order-fair ordering

Lemma 3.6 of [Ramseyer–Goel] claims that the strongly connected components of the ordering graph
thresholded at `γ - δ` behave like "batches" of any `(γ, δ)`-minimal-batch-order-fair output:

1. if `γ n` replicas received `τ ≺ τ'`, then either `τ, τ'` are in the same component, or *all*
   transactions of the component of `τ` are output before *any* transaction of the component of `τ'`;
2. if moreover there is no chain `τ' = τ₁, …, τₖ = τ` of pairs each received in order by
   `(γ - 2δ) n` replicas, then all of the component of `τ` is output before all of the component
   of `τ'`.

Both parts are false (`lemma_3_6_false`): Definition 3.5 only constrains the relative order of the
endpoints of a `γ`-edge, not of the other members of their components. Counterexample with
`n = 6` replicas, transactions `a b c d` (`Fin 4`), `γ = 2/3` (threshold: 4 votes), `δ = 0`:

| replica | 1 | 2 | 3 | 4 | 5 | 6 |
|---------|---|---|---|---|---|---|
| order   | abcd | adbc | bcad | dbca | cabd | dcab |

Counts: `a≺b`, `b≺c`, `c≺a`, `a≺d`: 4 each; `b≺d`, `c≺d`: 3. The `γ`-graph is the triangle
`a → b → c → a` plus `a → d`, so its components are `{a, b, c}` and `{d}`. The output
`a, d, b, c` reverses only `c → a`, and outputs the chain `a → b → c` in order, so it is
exactly `γ`-minimal; but `d` (component of `d`) is output before `b` (component of `a`) although
`a → d` is a `γ`-edge between different components, and `d` has no out-edge at all.

What *is* true (`lemma_3_6_pairwise`): the endpoints of a `γ`-edge `τ → τ'` lying in different
components of the `(γ - 2δ)`-graph are output in order `τ` before `τ'`.
-/

namespace Podc.FairOrderingSocialChoice

open Cslib.SocialChoice Finset Relation

variable {ι X : Type*} [Fintype ι]

/-- `a` and `b` lie in the same strongly connected component of the ordering graph after dropping
all edges of weight below `θ`. -/
def SameSCC (T : Profile ι X) (θ : ℝ) (a b : X) : Prop :=
  ReflTransGen (AtLeast T θ) a b ∧ ReflTransGen (AtLeast T θ) b a

/-- Every transaction of the component of `a` is output before every transaction of the component
of `b` (components of the graph thresholded at `θ`). -/
def ComponentBefore (T : Profile ι X) (θ : ℝ) (out : Pref X) (a b : X) : Prop :=
  ∀ x y, SameSCC T θ a x → SameSCC T θ b y → out.P x y

/-- First claim of **Lemma 3.6** (components of the graph thresholded at `γ - δ`). -/
def Lemma36Part1 (T : Profile ι X) (γ δ : ℝ) (out : Pref X) : Prop :=
  ∀ a b, AtLeast T γ a b → SameSCC T (γ - δ) a b ∨ ComponentBefore T (γ - δ) out a b

/-- Second claim of **Lemma 3.6**: if `γ n` replicas receive `a ≺ b` and there is no chain from `b`
back to `a` of pairs each received in order by `(γ - 2δ) n` replicas, then the component of `a` is
output entirely before the component of `b`. -/
def Lemma36Part2 (T : Profile ι X) (γ δ : ℝ) (out : Pref X) : Prop :=
  ∀ a b, AtLeast T γ a b → ¬ ReflTransGen (AtLeast T (γ - 2 * δ)) b a →
    ComponentBefore T (γ - δ) out a b

/-- Lowering the threshold keeps an edge. -/
theorem AtLeast.mono {T : Profile ι X} {θ θ' : ℝ} (h : θ' ≤ θ) {a b : X} (hab : AtLeast T θ a b) :
    AtLeast T θ' a b :=
  le_trans (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)) hab

/-- `(γ, δ)`-minimal-batch-order-fairness gets weaker as `δ` grows. -/
theorem MinimalBatchFair.mono {T : Profile ι X} {γ δ δ' : ℝ} {out : Pref X}
    (h : MinimalBatchFair T γ δ out) (hδ : δ ≤ δ') : MinimalBatchFair T γ δ' out := by
  intro a b hab hba
  exact ReflTransGen.mono (fun x y hxy => ⟨hxy.1.mono (by linarith), hxy.2⟩) _ _ (h a b hab hba)

/-- The correct (pairwise) content of **Lemma 3.6**: if `γ n` replicas received `a ≺ b` and `a, b`
are not in the same component of the graph thresholded at `γ - 2δ` (in particular, if there is no
`(γ - 2δ)`-chain from `b` back to `a`), then `a` is output before `b`. -/
theorem lemma_3_6_pairwise {T : Profile ι X} {γ δ : ℝ} {out : Pref X}
    (h : MinimalBatchFair T γ δ out) (hδ : 0 ≤ δ) {a b : X} (hab : AtLeast T γ a b)
    (hscc : ¬ SameSCC T (γ - 2 * δ) a b) : out.P a b := by
  have hne : a ≠ b := by rintro rfl; exact hscc ⟨.refl, .refl⟩
  by_contra hn
  have hba := (out.not_P_iff hne).1 hn
  exact hscc ⟨.single (hab.mono (by linarith)), ReflTransGen.mono (fun _ _ h => h.1) _ _ (h a b hab hba)⟩

/-! ### The counterexample -/

/-- If voter ranks never tie on `a, b`, the count of `a ≺ b` is the number of voters ranking `a`
lower. -/
theorem count_ofRank (p : ι → X → ℕ) {a b : X} (h : ∀ i, p i a ≠ p i b) :
    count (fun i => Pref.ofRank (p i)) a b = #{i | p i a < p i b} := by
  classical
  unfold count
  congr 1; ext i; simp [Pref.ofRank_P_iff (h i)]

namespace Lemma36

/-- Ranks of `a b c d` (`0 1 2 3`) in the six votes `abcd, adbc, bcad, dbca, cabd, dcab`. -/
def rk : Fin 6 → Fin 4 → ℕ :=
  ![![0, 1, 2, 3], ![0, 2, 3, 1], ![2, 0, 1, 3], ![3, 1, 2, 0], ![1, 2, 0, 3], ![2, 3, 1, 0]]

/-- The true profile of the counterexample. -/
noncomputable def T : Profile (Fin 6) (Fin 4) := fun i => Pref.ofRank (rk i)

/-- The output `a, d, b, c`. -/
noncomputable def out : Pref (Fin 4) := Pref.ofRank ![0, 2, 3, 1]

theorem out_P_iff {x y : Fin 4} (hxy : x ≠ y) :
    out.P x y ↔ (![0, 2, 3, 1] : Fin 4 → ℕ) x < (![0, 2, 3, 1] : Fin 4 → ℕ) y :=
  Pref.ofRank_P_iff (by revert x y; decide)

theorem count_T {x y : Fin 4} (hxy : x ≠ y) : count T x y = #{i | rk i x < rk i y} :=
  count_ofRank rk fun i => by revert x y i; decide

/-- The edges with at least 4 votes: `a → b → c → a` and `a → d`. -/
def E (x y : Fin 4) : Prop := (x, y) ∈ ({(0, 1), (1, 2), (2, 0), (0, 3)} : Finset (Fin 4 × Fin 4))

instance : DecidableRel E := fun _ _ => by unfold E; infer_instance

/-- For thresholds `θ ∈ (1/2, 2/3]` (i.e. between 3 and 4 votes out of 6), the thresholded graph
is `E`. -/
theorem atLeast_iff {θ : ℝ} (h1 : 1 / 2 < θ) (h2 : θ ≤ 2 / 3) (x y : Fin 4) :
    AtLeast T θ x y ↔ E x y := by
  unfold AtLeast
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  by_cases hxy : x = y
  · subst hxy
    have : count T x x = 0 := by unfold count; simp [(T _).irrefl]
    rw [this, Nat.cast_zero]
    have hE : ¬ E x x := by clear this; revert x; decide
    simp only [hE, iff_false, not_le]
    linarith
  rw [count_T hxy]
  have key : 4 ≤ #{i | rk i x < rk i y} ↔ E x y := by revert x y; decide
  rw [← key]
  constructor
  · intro h
    by_contra hc
    have : (#{i | rk i x < rk i y} : ℝ) ≤ 3 := by exact_mod_cast (by omega : _ ≤ 3)
    linarith
  · intro h
    have : (4 : ℝ) ≤ #{i | rk i x < rk i y} := by exact_mod_cast h
    linarith

theorem minimalBatchFair : MinimalBatchFair T (2 / 3) 0 out := by
  intro x y hxy hyx
  rw [atLeast_iff (by norm_num) le_rfl] at hxy
  have hne : y ≠ x := by rintro rfl; exact out.irrefl _ hyx
  rw [out_P_iff hne] at hyx
  have hR : ∀ u v, E u v → (![0, 2, 3, 1] : Fin 4 → ℕ) u < (![0, 2, 3, 1] : Fin 4 → ℕ) v →
      AtLeast T (2 / 3 - 2 * 0) u v ∧ out.P u v := by
    intro u v huv hlt
    refine ⟨(atLeast_iff (by norm_num) (by norm_num) u v).2 huv, ?_⟩
    exact Pref.ofRank_P_of_lt hlt
  -- the only reversed edge is `c → a`; the chain `a → b → c` is output in order
  have : x = 2 ∧ y = 0 := by revert x y; decide
  obtain ⟨rfl, rfl⟩ := this
  exact .tail (.single (hR 0 1 (by decide) (by decide))) (hR 1 2 (by decide) (by decide))

/-- `d` has no out-edge, so nothing is reachable from `d` but `d` itself. -/
theorem reach_d {θ : ℝ} (h1 : 1 / 2 < θ) (h2 : θ ≤ 2 / 3) {y : Fin 4}
    (h : ReflTransGen (AtLeast T θ) 3 y) : y = 3 := by
  rcases h.cases_head with h | ⟨z, hz, -⟩
  · exact h.symm
  · rw [atLeast_iff h1 h2] at hz
    exact absurd hz (by revert z; decide)

theorem not_part1 {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1 / 6) : ¬ Lemma36Part1 T (2 / 3) δ out := by
  have hθ1 : 1 / 2 < 2 / 3 - δ := by linarith
  have hθ2 : 2 / 3 - δ ≤ 2 / 3 := by linarith
  have e := atLeast_iff hθ1 hθ2
  intro h
  rcases h 0 3 ((atLeast_iff (by norm_num) le_rfl 0 3).2 (by decide)) with h | h
  · exact absurd (reach_d hθ1 hθ2 h.2) (by decide)
  · have hab : SameSCC T (2 / 3 - δ) 0 1 :=
      ⟨.single ((e 0 1).2 (by decide)),
        .tail (.single ((e 1 2).2 (by decide))) ((e 2 0).2 (by decide))⟩
    have := h 1 3 hab ⟨.refl, .refl⟩
    rw [out_P_iff (by decide)] at this
    exact absurd this (by decide)

theorem not_part2 : ¬ Lemma36Part2 T (2 / 3) 0 out := by
  have e := atLeast_iff (θ := 2 / 3 - 0) (by norm_num) (by norm_num)
  intro h
  have := h 0 3 ((atLeast_iff (by norm_num) le_rfl 0 3).2 (by decide))
    (fun hp => absurd (reach_d (θ := 2 / 3 - 2 * 0) (by norm_num) (by norm_num) hp) (by decide))
    1 3 ⟨.single ((e 0 1).2 (by decide)),
        .tail (.single ((e 1 2).2 (by decide))) ((e 2 0).2 (by decide))⟩ ⟨.refl, .refl⟩
  rw [out_P_iff (by decide)] at this
  exact absurd this (by decide)

end Lemma36

/-- **Lemma 3.6** of [Ramseyer–Goel] is false: with `n = 6` replicas, four transactions, `γ = 2/3`
and `δ = 0`, there is an output satisfying `(γ, δ)`-minimal-batch-order-fairness (even exact
`γ`-minimality, Definition 3.3) for which both claims of the lemma fail. -/
theorem lemma_3_6_false :
    ∃ (T : Profile (Fin 6) (Fin 4)) (out : Pref (Fin 4)),
      MinimalBatchFair T (2 / 3) 0 out ∧ ¬ Lemma36Part1 T (2 / 3) 0 out ∧
        ¬ Lemma36Part2 T (2 / 3) 0 out :=
  ⟨Lemma36.T, Lemma36.out, Lemma36.minimalBatchFair, Lemma36.not_part1 le_rfl (by norm_num),
    Lemma36.not_part2⟩

/-- The first claim of **Lemma 3.6** also fails for every `δ ∈ [0, 1/6)` on the same instance
(the graph thresholded at `γ - δ` is unchanged, and fairness is monotone in `δ`). -/
theorem lemma_3_6_part1_false {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1 / 6) :
    ∃ (T : Profile (Fin 6) (Fin 4)) (out : Pref (Fin 4)),
      MinimalBatchFair T (2 / 3) δ out ∧ ¬ Lemma36Part1 T (2 / 3) δ out :=
  ⟨Lemma36.T, Lemma36.out, Lemma36.minimalBatchFair.mono h0, Lemma36.not_part1 h0 h1⟩

end Podc.FairOrderingSocialChoice
