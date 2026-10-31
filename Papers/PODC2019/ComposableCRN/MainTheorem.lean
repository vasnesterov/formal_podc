import Papers.PODC2019.ComposableCRN.QuiltAffine
import Papers.PODC2019.ComposableCRN.Composition
import Papers.PODC2019.ComposableCRN.Gadgets
import Papers.PODC2019.ComposableCRN.Impossibility

/-!
# Theorem 5.2: the sufficiency direction (Lemma 6.2), Observation 5.3

* `fixInput f i j` is the fixed-input restriction `f[x(i)→j]` (§5).
* `EventuallyMin f` is condition (ii) of Theorem 5.2.
* `observation_5_3`: fixed-input restrictions of obliviously-computable functions are
  obliviously-computable.
* `lemma_6_2`: conditions (i)–(iii) imply that `f` is obliviously-computable, via the paper's
  identity (1) `f x = min (f (x ∨ n), min_{i, j<n} (f[x(i)→j] x + 1{x(i)>j} · f (x ∨ n)))`
  and closure under composition.
* `theorem_5_2`: the characterization, assuming Theorem 7.1 (the necessity of (ii), not
  formalized) as a hypothesis.
-/

namespace Podc.ComposableCRN

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem ObliviouslyComputable.congr {f g : (ι → ℕ) → ℕ} (hf : ObliviouslyComputable f)
    (h : ∀ x, f x = g x) : ObliviouslyComputable g := by
  rwa [← funext h]

/-- The fixed-input restriction `f[x(i)→j]` (§5): `x ↦ f (x(1), …, j, …, x(d))`. -/
def fixInput (f : (ι → ℕ) → ℕ) (i : ι) (j : ℕ) : (ι → ℕ) → ℕ :=
  fun x => f (Function.update x i j)

/-- Condition (ii) of Theorem 5.2 ("eventually-min"): there are quilt-affine
`g₁, …, g_m : ℕ^d → ℤ` (`m ≥ 1`) and `n ∈ ℕ^d` with `f x = min_k g_k x` for all `x ≥ n`. -/
def EventuallyMin (f : (ι → ℕ) → ℕ) : Prop :=
  ∃ (m : ℕ) (g : Fin (m + 1) → (ι → ℕ) → ℤ) (n : ι → ℕ), (∀ k, IsQuiltAffine (g k)) ∧
    ∀ x, n ≤ x → (f x : ℤ) = Finset.univ.inf' Finset.univ_nonempty (fun k => g k x)

/-- Observation 5.3: every fixed-input restriction of an obliviously-computable function is
obliviously-computable. (The paper hard-codes the input with `L → j X_i' + L'`; we obtain it by
composing `f` with the constant `j` and the projections.) -/
theorem observation_5_3 {f : (ι → ℕ) → ℕ} (hf : ObliviouslyComputable f) (i : ι) (j : ℕ) :
    ObliviouslyComputable (fixInput f i j) := by
  have hu : ∀ k, ObliviouslyComputable
      (fun x : ι → ℕ => if k = i then j else x k) := fun k => by
    by_cases hk : k = i
    · simpa [hk] using obliviouslyComputable_const (ι := ι) j
    · simpa [hk] using obliviouslyComputable_proj k
  refine (hf.comp hu).congr fun x => ?_
  simp only [fixInput]
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

omit [DecidableEq ι] in
/-- Translation preserves quilt-affinity. -/
theorem IsQuiltAffine.translate {g : (ι → ℕ) → ℤ} (hg : IsQuiltAffine g) (c : ι → ℕ) :
    IsQuiltAffine (fun y => g (y + c)) := by
  obtain ⟨hmono, p, hp, grad, B, hgrad, hform⟩ := hg
  refine ⟨fun y y' h => hmono (add_le_add_left h c |>.trans_eq' (by abel) |>.trans_eq (by abel)),
    p, hp, grad, fun a => ∑ i, grad i * c i + B (a + fun i => (c i : ZMod p)), hgrad,
    fun y => ?_⟩
  rw [hform]
  simp only [Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  rw [add_assoc]
  rfl

/-- **Lemma 6.2** (the "⇐" direction of Theorem 5.2): if `f` is nondecreasing (i), eventually
the minimum of finitely many quilt-affine functions (ii), and all its fixed-input restrictions
are obliviously-computable (iii), then `f` is obliviously-computable. -/
theorem lemma_6_2 (f : (ι → ℕ) → ℕ) (hmono : Monotone f) (hmin : EventuallyMin f)
    (hfix : ∀ i j, ObliviouslyComputable (fixInput f i j)) : ObliviouslyComputable f := by
  obtain ⟨m, g, n, hg, hfg⟩ := hmin
  -- w.l.o.g. `n = (N, …, N)`
  set N := Finset.univ.sup n with hN
  have hnN : ∀ i, n i ≤ N := fun i => Finset.le_sup (f := n) (Finset.mem_univ i)
  have hfg' : ∀ x, (∀ i, N ≤ x i) → (f x : ℤ) = Finset.univ.inf' Finset.univ_nonempty
      (fun k => g k x) := fun x hx => hfg x fun i => (hnN i).trans (hx i)
  have hge : ∀ x, (∀ i, N ≤ x i) → ∀ k, (f x : ℤ) ≤ g k x := fun x hx k => by
    rw [hfg' x hx]; exact Finset.inf'_le _ (Finset.mem_univ k)
  let vee : (ι → ℕ) → ι → ℕ := fun x i => max (x i) N
  have hvee : ∀ x i, N ≤ vee x i := fun x i => le_max_right _ _
  -- `x ↦ g_k (x ∨ N)` is obliviously-computable: `g_k (· + N)` is quilt-affine and
  -- nonnegative (Lemma 6.1), composed with `(x - N)⁺`
  have hgk : ∀ k, ObliviouslyComputable (fun x => (g k (vee x)).toNat) := fun k => by
    let G : (ι → ℕ) → ℕ := fun y => (g k (y + fun _ => N)).toNat
    have hGnn : ∀ y, 0 ≤ g k (y + fun _ => N) := fun y =>
      (Int.natCast_nonneg _).trans (hge _ (fun i => by simp) k)
    have hG : ObliviouslyComputable G := by
      refine lemma_6_1 G ?_
      have : (fun y => ((G y : ℕ) : ℤ)) = fun y => g k (y + fun _ => N) := by
        funext y; exact Int.toNat_of_nonneg (hGnn y)
      rw [this]
      exact (hg k).translate _
    refine (hG.comp (fun i => obliviouslyComputable_sub_const i N)).congr fun x => ?_
    simp only [G]
    congr 3
    funext i
    simp only [Pi.add_apply, vee]
    omega
  -- `T₀ x = f (x ∨ N)`
  have hT0 : ObliviouslyComputable (fun x => f (vee x)) := by
    refine (obliviouslyComputable_min.comp hgk).congr fun x => ?_
    obtain ⟨k₀, -, hk₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun k => g k (vee x))
    rw [← hfg' _ (hvee x)] at hk₀
    apply le_antisymm
    · refine (Finset.inf'_le _ (Finset.mem_univ k₀)).trans ?_
      simp only [← hk₀, Int.toNat_natCast, le_refl]
    · refine Finset.le_inf' _ _ fun k _ => ?_
      have := hge _ (hvee x) k
      omega
  -- `T_{ij} x = f[x(i)→j] x + 1{x(i) > j} · f (x ∨ N)`
  have hT : ∀ (i : ι) (j : Fin N), ObliviouslyComputable
      (fun x => fixInput f i j x + if (j : ℕ) < x i then f (vee x) else 0) := fun i j => by
    have hu : ∀ k : Fin 3, ObliviouslyComputable
        (![fixInput f i j, fun x => f (vee x), fun x => x i] k) := by
      intro k; fin_cases k
      exacts [hfix i j, hT0, obliviouslyComputable_proj i]
    refine ((obliviouslyComputable_add_ite j).comp hu).congr fun x => ?_
    simp
  -- identity (1)
  let T : Option (ι × Fin N) → (ι → ℕ) → ℕ := fun o => match o with
    | none => fun x => f (vee x)
    | some (i, j) => fun x => fixInput f i j x + if (j : ℕ) < x i then f (vee x) else 0
  have hTo : ∀ o, ObliviouslyComputable (T o) := fun o => by
    rcases o with _ | ⟨i, j⟩
    exacts [hT0, hT i j]
  have hle_vee : ∀ x, x ≤ vee x := fun x i => le_max_left _ _
  refine (obliviouslyComputable_min.comp hTo).congr fun x => ?_
  apply le_antisymm
  · -- some term equals `f x`
    by_cases hx : ∀ i, N ≤ x i
    · have : vee x = x := funext fun i => max_eq_left (hx i)
      refine (Finset.inf'_le _ (Finset.mem_univ none)).trans ?_
      simp [T, this]
    · push Not at hx
      obtain ⟨i, hi⟩ := hx
      refine (Finset.inf'_le _ (Finset.mem_univ (some (i, ⟨x i, hi⟩)))).trans ?_
      simp [T, fixInput]
  · -- `f x` is below every term
    refine Finset.le_inf' _ _ fun o _ => ?_
    rcases o with _ | ⟨i, j⟩
    · exact hmono (hle_vee x)
    · simp only [T]
      split_ifs with hj
      · exact (hmono (hle_vee x)).trans (Nat.le_add_left _ _)
      · refine (hmono fun k => ?_).trans (Nat.le_add_right _ _)
        by_cases hk : k = i
        · subst hk; simp; omega
        · simp [hk]

/-- Theorem 7.1 (necessity of the eventually-min condition), as a proposition. The paper's proof
(§7, recession cones of the regions of a semilinear decomposition) is not formalized. -/
def Theorem71 : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → ℕ) → ℕ),
    ObliviouslyComputable f → EventuallyMin f

/-- **Theorem 5.2.** `f : ℕ^d → ℕ` is obliviously-computable iff (i) it is nondecreasing,
(ii) it is eventually the minimum of finitely many quilt-affine functions, and (iii) all its
fixed-input restrictions are obliviously-computable. "⇐" is `lemma_6_2`; "⇒" uses
Observation 2.1, Observation 5.3 and Theorem 7.1, the last taken as a hypothesis. -/
theorem theorem_5_2 (h71 : Theorem71) (f : (ι → ℕ) → ℕ) :
    ObliviouslyComputable f ↔
      Monotone f ∧ EventuallyMin f ∧ ∀ i j, ObliviouslyComputable (fixInput f i j) :=
  ⟨fun h => ⟨h.monotone, h71 ι f h, observation_5_3 h⟩,
    fun ⟨h1, h2, h3⟩ => lemma_6_2 f h1 h2 h3⟩

end Podc.ComposableCRN
