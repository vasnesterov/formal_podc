import Papers.PODC2014.LinearInDeltaLB.FreeTree
import Papers.PODC2014.LinearInDeltaLB.Defs
import Cslib.Foundations.Combinatorics.SimpleGraph.Ball

/-!
# ID-graphs carved out of the free-group tree

`idGraph R ψ` is the finite simple ID-graph obtained from a finite set `R ⊆ F_k` of nodes of the
Cayley tree by assigning identifiers `ψ : F_k → ℕ` (injective on `R`); its edges are the tree edges
`{w, w l}` inside `R`. These are the instances `ϕ(τ)` on which the ID-algorithm is run in Section 5.4.

Main facts: neighbourhoods and degrees (`neighborSet_idGraph`, `ncard_neighborSet_idGraph_le`),
finiteness, translation (`idGraph_translate`), and locality (`gAgree_idGraph_of_subset`): the
radius-`t` neighbourhood of `ψ w` only sees the nodes of `R` within tree distance `t` of `w`.
-/

namespace Podc.LinearInDeltaLB

open FreeGroup Pointwise

variable {k : ℕ}

/-- The ID-graph of `R ⊆ F_k` with identifiers `ψ`: tree edges inside `R`. -/
def idGraph (R : Set (FG k)) (ψ : FG k → ℕ) : SimpleGraph ℕ where
  Adj i j := i ≠ j ∧ ∃ w ∈ R, ∃ l, w * ltr l ∈ R ∧ ψ w = i ∧ ψ (w * ltr l) = j
  symm := ⟨fun _ _ ⟨hne, w, hw, l, hwl, h1, h2⟩ =>
    ⟨hne.symm, w * ltr l, hwl, linv l, by simpa using hw, h2, by simpa using h1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {R R' : Set (FG k)} {ψ ψ' : FG k → ℕ}

theorem idGraph_adj_iff (hψ : Set.InjOn ψ R) {w : FG k} (hw : w ∈ R) (j : ℕ) :
    (idGraph R ψ).Adj (ψ w) j ↔ ∃ l, w * ltr l ∈ R ∧ ψ (w * ltr l) = j := by
  constructor
  · rintro ⟨-, w', hw', l, hw'l, h1, h2⟩
    obtain rfl := hψ hw' hw h1
    exact ⟨l, hw'l, h2⟩
  · rintro ⟨l, hl, rfl⟩
    refine ⟨fun h => mul_ltr_ne_self w l (hψ hl hw h.symm), w, hw, l, hl, rfl, rfl⟩

theorem not_idGraph_adj (i j : ℕ) (hi : i ∉ ψ '' R) : ¬ (idGraph R ψ).Adj i j := by
  rintro ⟨-, w, hw, l, -, rfl, -⟩
  exact hi ⟨w, hw, rfl⟩

theorem neighborSet_idGraph (hψ : Set.InjOn ψ R) {w : FG k} (hw : w ∈ R) :
    (idGraph R ψ).neighborSet (ψ w) = (fun l => ψ (w * ltr l)) '' {l | w * ltr l ∈ R} := by
  ext j
  simp only [SimpleGraph.mem_neighborSet, idGraph_adj_iff hψ hw, Set.mem_image,
    Set.mem_ofPred_eq]

theorem injOn_letters (hψ : Set.InjOn ψ R) (w : FG k) :
    Set.InjOn (fun l => ψ (w * ltr l)) {l | w * ltr l ∈ R} :=
  fun _ ha _ hb h => mul_ltr_injective w (hψ ha hb h)

open Classical in
/-- Sums over the neighbours of `ψ w` are sums over the letters leading inside `R`. -/
theorem finsum_neighborSet_idGraph (hψ : Set.InjOn ψ R) {w : FG k} (hw : w ∈ R) (f : ℕ → ℝ) :
    ∑ᶠ u ∈ (idGraph R ψ).neighborSet (ψ w), f u =
      ∑ l ∈ Finset.univ.filter (fun l => w * ltr l ∈ R), f (ψ (w * ltr l)) := by
  rw [neighborSet_idGraph hψ hw, finsum_mem_image (injOn_letters hψ w)]
  rw [← finsum_mem_coe_finset]
  congr 1
  ext l
  simp

theorem neighborSet_idGraph_of_not_mem {i : ℕ} (hi : i ∉ ψ '' R) :
    (idGraph R ψ).neighborSet i = ∅ := by
  ext j; simp [not_idGraph_adj i j hi]

theorem ncard_neighborSet_idGraph_le (hψ : Set.InjOn ψ R) (i : ℕ) :
    ((idGraph R ψ).neighborSet i).ncard ≤ 2 * k := by
  by_cases hi : i ∈ ψ '' R
  · obtain ⟨w, hw, rfl⟩ := hi
    rw [neighborSet_idGraph hψ hw]
    calc _ ≤ ({l | w * ltr l ∈ R} : Set (Fin k × Bool)).ncard := Set.ncard_image_le (Set.toFinite _)
      _ ≤ (Set.univ : Set (Fin k × Bool)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = 2 * k := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]; simp [mul_comm]
  · rw [neighborSet_idGraph_of_not_mem hi]; simp

theorem edgeSet_idGraph_finite (hR : R.Finite) : (idGraph R ψ).edgeSet.Finite := by
  have : ((fun p : FG k × (Fin k × Bool) => s(ψ p.1, ψ (p.1 * ltr p.2))) ''
      (R ×ˢ Set.univ)).Finite := (hR.prod Set.finite_univ).image _
  refine this.subset ?_
  intro e he
  induction e using Sym2.ind with
  | _ i j =>
    obtain ⟨-, w, hw, l, -, rfl, rfl⟩ := he
    exact ⟨(w, l), ⟨hw, trivial⟩, rfl⟩

/-- Translation: the ID-graph of `w • X` labelled by `ψ` is the ID-graph of `X` labelled by
`ψ (w * ·)`. -/
theorem idGraph_translate (X : Set (FG k)) (ψ : FG k → ℕ) (w : FG k) :
    idGraph X (fun x => ψ (w * x)) = idGraph (w • X) ψ := by
  ext i j
  simp only [idGraph]
  constructor
  · rintro ⟨hne, x, hx, l, hxl, h1, h2⟩
    refine ⟨hne, w * x, Set.smul_mem_smul_set hx, l, ?_, h1, by rw [mul_assoc]; exact h2⟩
    rw [mul_assoc]; exact Set.smul_mem_smul_set hxl
  · rintro ⟨hne, x, hx, l, hxl, h1, h2⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hx hxl
    refine ⟨hne, w⁻¹ * x, hx, l, by rw [mul_assoc]; exact hxl, by simpa using h1, ?_⟩
    simpa [mul_assoc] using h2

theorem idGraph_congr (h : ∀ x ∈ R, ψ x = ψ' x) : idGraph R ψ = idGraph R ψ' := by
  ext i j
  simp only [idGraph]
  constructor
  · rintro ⟨hne, x, hx, l, hxl, h1, h2⟩
    exact ⟨hne, x, hx, l, hxl, (h x hx) ▸ h1, (h _ hxl) ▸ h2⟩
  · rintro ⟨hne, x, hx, l, hxl, h1, h2⟩
    exact ⟨hne, x, hx, l, hxl, (h x hx).symm ▸ h1, (h _ hxl).symm ▸ h2⟩

theorem idGraph_mono (hRR' : R ⊆ R') : idGraph R ψ ≤ idGraph R' ψ := by
  rintro i j ⟨hne, x, hx, l, hxl, h1, h2⟩
  exact ⟨hne, x, hRR' hx, l, hRR' hxl, h1, h2⟩

/-- Distances in an ID-graph dominate tree distances. -/
theorem norm_le_edist_idGraph (hψ : Set.InjOn ψ R) {w x : FG k} (hx : x ∈ R) :
    (norm (w⁻¹ * x) : ℕ∞) ≤ norm (w⁻¹ * Function.invFunOn ψ R (ψ w)) +
      (idGraph R ψ).edist (ψ w) (ψ x) := by
  classical
  let f : ℕ → ℕ := fun n => norm (w⁻¹ * Function.invFunOn ψ R n)
  have hf : ∀ n m, (idGraph R ψ).Adj n m → f m ≤ f n + 1 := by
    rintro n m ⟨-, y, hy, l, hyl, rfl, rfl⟩
    simp only [f, hψ.leftInvOn_invFunOn hy, hψ.leftInvOn_invFunOn hyl]
    rw [← mul_assoc]; exact norm_mul_ltr_le _ _
  have := SimpleGraph.le_add_edist_of_lipschitz (G := idGraph R ψ) hf (ψ w) (ψ x)
  simpa [f, hψ.leftInvOn_invFunOn hx] using this

/-- Locality of ID-graphs: if `R ⊆ R'` contains every node of `R'` within tree distance `t` of
`w`, then `idGraph R' ψ` and `idGraph R ψ` agree around `ψ w` up to radius `t`. -/
theorem gAgree_idGraph_of_subset {t : ℕ} (hRR' : R ⊆ R') (hψ : Set.InjOn ψ R') {w : FG k}
    (hw : w ∈ R) (hloc : ∀ x ∈ R', norm (w⁻¹ * x) ≤ t → x ∈ R) :
    Cslib.Local.GAgree (idGraph R' ψ) (idGraph R ψ) (ψ w) t := by
  intro i hi j
  by_cases hiR : i ∈ ψ '' R'
  · obtain ⟨x, hx, rfl⟩ := hiR
    have hd := norm_le_edist_idGraph (w := w) hψ hx
    rw [hψ.leftInvOn_invFunOn (hRR' hw), inv_mul_cancel, FreeGroup.norm_one,
      Nat.cast_zero, zero_add] at hd
    have hxt : norm (w⁻¹ * x) < t := by exact_mod_cast hd.trans_lt hi
    have hxR : x ∈ R := hloc x hx hxt.le
    rw [idGraph_adj_iff hψ hx, idGraph_adj_iff (hψ.mono hRR') hxR]
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨l, hloc _ hl ?_, rfl⟩
      have := norm_mul_ltr_le (w⁻¹ * x) l
      rw [mul_assoc] at this; omega
    · rintro ⟨l, hl, rfl⟩; exact ⟨l, hRR' hl, rfl⟩
  · have hiR2 : i ∉ ψ '' R := fun h => hiR (Set.image_mono hRR' h)
    simp [not_idGraph_adj i j hiR, not_idGraph_adj i j hiR2]

/-! ### Saturation -/

/-- `A` saturates `v` in `G`. -/
def Sat (A : IDAlg) (G : SimpleGraph ℕ) (v : ℕ) : Prop :=
  ∑ᶠ u ∈ G.neighborSet v, A G v u = 1

theorem sat_congr {A : IDAlg} {t : ℕ} (hA : A.HasRunTime t) (ht : 0 < t) {G G' : SimpleGraph ℕ}
    {v : ℕ} (h : Cslib.Local.GAgree G G' v t) : Sat A G v ↔ Sat A G' v := by
  unfold Sat
  rw [hA G G' v h, h.neighborSet_eq ht]

end Podc.LinearInDeltaLB
