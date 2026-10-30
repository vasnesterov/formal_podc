import Papers.PODC2025.RoundEfficientColoring.Matching
import Papers.PODC2025.RoundEfficientColoring.SetCover
import Podc.Foundations.Combinatorics.SimpleGraph.EdgeColoring.Vizing

/-!
# Algorithm 2: the local (communication-free) part of one party

Chang–Mishra–Nguyen–Salim, PODC 2025, Section 5, Algorithm 2 for `Δ ≥ 8`, lines 1–10, and the
local part of Lemma 5.4. A party with graph `X` (maximum degree `≤ Δ`) computes

* the remaining graph `R` and the deferred graph `D = X \ R` (lines 1–5): no edge of `R` joins two
  vertices of `R`-degree `≥ Δ - 1`; **Lemma 5.2**: `D` has maximum degree `≤ 2`; and every
  endpoint of a deferred edge has `X`-degree `≥ Δ - 1`;
* a matching `M ≤ R` covering every vertex of `R`-degree `Δ` (line 6, **Lemma 5.3**), given by an
  injective map `f` (`M = {s(u, f u) : deg_R u = Δ}`);
* a proper `(Δ - 1)`-edge colouring `col` of `R' = R \ M` by Fournier's theorem (line 10);
* the greedy colour cover `(cs, lvl)` of the vertices of `X`-degree `≤ Δ/2` by colours of its own
  palette missing in `col` (proof of **Lemma 5.4**).

All of this is bundled in `Plan Δ X`; `exists_plan` shows that a plan exists.
-/

set_option linter.unusedSectionVars false

namespace Podc.RoundEfficientColoring

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The matching `{s(u, f u) : top u}`. -/
def matchGraph (top : V → Prop) (f : V → V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => top u ∧ v = f u

/-- The local data of one party in Algorithm 2 (see the module docstring). -/
structure Plan (Δ : ℕ) (X : SimpleGraph V) where
  /-- The remaining graph after deferral. -/
  R : SimpleGraph V
  le : R ≤ X
  term : ∀ ⦃u v : V⦄, R.Adj u v →
    (R.neighborSet u).ncard + 1 < Δ ∨ (R.neighborSet v).ncard + 1 < Δ
  defer_le_two : ∀ v, ((X \ R).neighborSet v).ncard ≤ 2
  defer_deg : ∀ ⦃u v : V⦄, (X \ R).Adj u v → Δ ≤ (X.neighborSet u).ncard + 1
  /-- The `Δ`-perfect matching: `u ↦ f u` for vertices of `R`-degree `Δ`. -/
  f : V → V
  f_adj : ∀ u, (R.neighborSet u).ncard = Δ → R.Adj u (f u)
  f_inj : ∀ u u', (R.neighborSet u).ncard = Δ → (R.neighborSet u').ncard = Δ → f u = f u' → u = u'
  /-- The colouring of `R \ M` with the own palette `{0, …, Δ - 2}`. -/
  col : Sym2 V → ℕ
  col_proper : (R \ matchGraph (fun u => (R.neighborSet u).ncard = Δ) f).IsProperEdgeColoring col
    (Δ - 1)
  /-- The greedy colour cover of the vertices of degree `≤ Δ / 2`. -/
  cs : List ℕ
  lvl : V → ℕ
  cover : ∀ v, 2 * (X.neighborSet v).ncard ≤ Δ → lvl v < cs.length ∧ cs.getD (lvl v) 0 < Δ - 1 ∧
    (R \ matchGraph (fun u => (R.neighborSet u).ncard = Δ) f).EdgeColorMissing col v
      (cs.getD (lvl v) 0)
  lvl_zero : ∀ v, ¬ 2 * (X.neighborSet v).ncard ≤ Δ → lvl v = 0
  cs_lt : ∀ c ∈ cs, c < Δ - 1
  lvl_sum : ∑ v, lvl v ≤ 2 * Fintype.card V
  cs_len : cs = [] ∨ 3 ^ cs.length ≤ 2 ^ cs.length * (3 * Fintype.card V)

namespace Plan

variable {Δ : ℕ} {X : SimpleGraph V} (p : Plan Δ X)

/-- Vertices of `R`-degree `Δ`. -/
def top (u : V) : Prop := (p.R.neighborSet u).ncard = Δ

/-- The matching. -/
def M : SimpleGraph V := matchGraph p.top p.f

/-- The graph coloured with the own palette. -/
def R' : SimpleGraph V := p.R \ p.M

/-- The deferred graph. -/
def D : SimpleGraph V := X \ p.R

lemma col_proper' : p.R'.IsProperEdgeColoring p.col (Δ - 1) := p.col_proper

lemma cover' {v : V} (hv : 2 * (X.neighborSet v).ncard ≤ Δ) :
    p.lvl v < p.cs.length ∧ p.cs.getD (p.lvl v) 0 < Δ - 1 ∧
      p.R'.EdgeColorMissing p.col v (p.cs.getD (p.lvl v) 0) := p.cover v hv

variable [Finite V] (hX : ∀ v, (X.neighborSet v).ncard ≤ Δ)
include hX

lemma top_ncard {u : V} (hu : p.top u) : (X.neighborSet u).ncard = Δ :=
  le_antisymm (hX u) (hu ▸ ncard_neighborSet_le_of_le p.le u)

lemma not_top_f {u : V} (hu : p.top u) : (p.R.neighborSet (p.f u)).ncard + 1 < Δ := by
  rcases p.term (p.f_adj u hu) with h | h
  · unfold top at hu; omega
  · exact h

lemma M_adj {a b : V} : p.M.Adj a b ↔ (p.top a ∧ b = p.f a) ∨ (p.top b ∧ a = p.f b) := by
  unfold M matchGraph
  rw [fromRel_adj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    · have := p.f_adj a h1
      rw [← h2] at this
      exact p.R.irrefl this

lemma M_le_R : p.M ≤ p.R := by
  intro a b h
  rcases (p.M_adj hX).mp h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
  · exact p.f_adj a h1
  · exact (p.f_adj b h1).symm

lemma top_iff_ne_top {a b : V} (h : p.M.Adj a b) : (p.top a ∧ ¬ p.top b) ∨ (p.top b ∧ ¬ p.top a) := by
  rcases (p.M_adj hX).mp h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
  · exact Or.inl ⟨h1, fun h2 => by have := p.not_top_f hX h1; unfold top at h2; omega⟩
  · exact Or.inr ⟨h1, fun h2 => by have := p.not_top_f hX h1; unfold top at h2; omega⟩

/-- `M` is a matching. -/
lemma M_unique {x y y' : V} (h : p.M.Adj x y) (h' : p.M.Adj x y') : y = y' := by
  have hnt : ∀ {u : V}, p.top u → ¬ p.top (p.f u) := fun {u} hu hfu => by
    have := p.not_top_f hX hu; unfold top at hfu; omega
  rcases (p.M_adj hX).mp h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
  · rcases (p.M_adj hX).mp h' with ⟨h2, rfl⟩ | ⟨h2, hx⟩
    · rfl
    · exact absurd (hx ▸ h1) (hnt h2)
  · rcases (p.M_adj hX).mp h' with ⟨h2, rfl⟩ | ⟨h2, hx⟩
    · exact absurd h2 (hnt h1)
    · exact p.f_inj _ _ h1 h2 hx

lemma R'_le : p.R' ≤ p.R := sdiff_le

/-- Every edge of `X` is in exactly one of `R'`, `M`, `D`. -/
lemma trichotomy {a b : V} (h : X.Adj a b) : p.R'.Adj a b ∨ p.M.Adj a b ∨ p.D.Adj a b := by
  by_cases hR : p.R.Adj a b
  · by_cases hM : p.M.Adj a b
    · exact Or.inr (Or.inl hM)
    · exact Or.inl ((sdiff_adj _ _ _ _).mpr ⟨hR, hM⟩)
  · exact Or.inr (Or.inr ((sdiff_adj _ _ _ _).mpr ⟨h, hR⟩))

lemma R'_not_M {a b : V} (h : p.R'.Adj a b) : ¬ p.M.Adj a b := ((sdiff_adj _ _ _ _).mp h).2

lemma D_not_R {a b : V} (h : p.D.Adj a b) : ¬ p.R.Adj a b := ((sdiff_adj _ _ _ _).mp h).2

lemma D_not_R' {a b : V} (h : p.D.Adj a b) : ¬ p.R'.Adj a b := fun h' =>
  p.D_not_R hX h (p.R'_le hX h')

lemma D_not_M {a b : V} (h : p.D.Adj a b) : ¬ p.M.Adj a b := fun h' =>
  p.D_not_R hX h (p.M_le_R hX h')

lemma R'_le_X : p.R' ≤ X := (p.R'_le hX).trans p.le

lemma M_le_X : p.M ≤ X := (p.M_le_R hX).trans p.le

lemma D_le_X : p.D ≤ X := sdiff_le

lemma ncard_R'_le (v : V) : (p.R'.neighborSet v).ncard ≤ (X.neighborSet v).ncard :=
  ncard_neighborSet_le_of_le (p.R'_le_X hX) v

lemma D_deg {u v : V} (h : p.D.Adj u v) : Δ ≤ (X.neighborSet u).ncard + 1 := p.defer_deg h

lemma D_le_two (v : V) : (p.D.neighborSet v).ncard ≤ 2 := p.defer_le_two v

end Plan

/-! ### Existence of a plan -/

/-- Line 10 of Algorithm 2: Fournier's theorem applies to `R \ M`. -/
lemma exists_col [Finite V] {Δ : ℕ} {R : SimpleGraph V} (hR : ∀ v, (R.neighborSet v).ncard ≤ Δ)
    (hterm : ∀ ⦃u v : V⦄, R.Adj u v →
      (R.neighborSet u).ncard + 1 < Δ ∨ (R.neighborSet v).ncard + 1 < Δ)
    {f : V → V} (hf : ∀ u, (R.neighborSet u).ncard = Δ → R.Adj u (f u)) :
    ∃ col : Sym2 V → ℕ, SimpleGraph.IsProperEdgeColoring
      (R \ matchGraph (fun u => (R.neighborSet u).ncard = Δ) f) col (Δ - 1) := by
  set M := matchGraph (fun u => (R.neighborSet u).ncard = Δ) f
  have hMle : M ≤ R := by
    intro a b h
    rcases ((fromRel_adj _ _ _).mp h).2 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · exact hf a h1
    · exact (hf b h1).symm
  refine exists_isProperEdgeColoring_of_ncard_le _ _ (fun v => ?_) (fun u v huv => ?_)
  · -- a vertex of `R`-degree `Δ` loses its matching edge
    have hle := ncard_neighborSet_le_of_le (sdiff_le : R \ M ≤ R) v
    by_cases hv : (R.neighborSet v).ncard = Δ
    · have hfv := hf v hv
      have hsub : (R \ M).neighborSet v ⊆ R.neighborSet v \ {f v} := by
        intro w hw
        simp only [mem_neighborSet, sdiff_adj] at hw
        refine ⟨hw.1, fun hwf => hw.2 ?_⟩
        rw [Set.mem_singleton_iff.mp hwf]
        exact (fromRel_adj _ _ _).mpr ⟨hfv.ne, Or.inl ⟨hv, rfl⟩⟩
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_sdiff_singleton_of_mem (show f v ∈ R.neighborSet v from hfv)] at this
      omega
    · have := hR v; omega
  · have hR' : R.Adj u v := ((sdiff_adj _ _ _ _).mp huv).1
    have hu := ncard_neighborSet_le_of_le (sdiff_le : R \ M ≤ R) u
    have hv := ncard_neighborSet_le_of_le (sdiff_le : R \ M ≤ R) v
    rcases hterm hR' with h | h
    · left; omega
    · right; omega

/-- A plan exists for every graph of maximum degree `≤ Δ`, `Δ ≥ 8`. -/
theorem exists_plan {Δ : ℕ} (hΔ : 8 ≤ Δ) {X : SimpleGraph V}
    (hX : ∀ v, (X.neighborSet v).ncard ≤ Δ) : Nonempty (Plan Δ X) := by
  classical
  -- lines 1–5: deferral with threshold `Δ - 1`
  obtain ⟨R, hRX, hterm, hinv⟩ := exists_deferral X (Δ - 1)
  have hR : ∀ v, (R.neighborSet v).ncard ≤ Δ := fun v =>
    (ncard_neighborSet_le_of_le hRX v).trans (hX v)
  have hterm' : ∀ ⦃u v : V⦄, R.Adj u v →
      (R.neighborSet u).ncard + 1 < Δ ∨ (R.neighborSet v).ncard + 1 < Δ := fun u v h => by
    rcases hterm h with h | h
    · left; omega
    · right; omega
  have hD2 : ∀ v, ((X \ R).neighborSet v).ncard ≤ 2 := fun v => by
    rw [ncard_neighborSet_sdiff hRX]
    by_cases h : (R.neighborSet v).ncard < (X.neighborSet v).ncard
    · have := hinv v h; have := hX v; omega
    · omega
  have hDdeg : ∀ ⦃u v : V⦄, (X \ R).Adj u v → Δ ≤ (X.neighborSet u).ncard + 1 := fun u v h => by
    have hpos : 0 < ((X \ R).neighborSet u).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨v, h⟩
    rw [ncard_neighborSet_sdiff hRX] at hpos
    have := hinv u (by omega); omega
  -- line 6: the matching (Lemma 5.3)
  obtain ⟨f, hf, hfinj⟩ := lemma_5_3 R (k := Δ) (by omega) hR
  -- line 10: Fournier
  obtain ⟨col, hcol⟩ := exists_col hR hterm' hf
  set R' := R \ matchGraph (fun u => (R.neighborSet u).ncard = Δ) f
  -- Lemma 5.4: the greedy cover
  let avail : V → Finset ℕ := fun v => (range (Δ - 1)).filter fun j => R'.EdgeColorMissing col v j
  let U : Finset V := univ.filter fun v => 2 * (X.neighborSet v).ncard ≤ Δ
  have hthird : ∀ v ∈ U, Δ - 1 ≤ 3 * #(avail v) := by
    intro v hv
    have hv' : 2 * (X.neighborSet v).ncard ≤ Δ := (mem_filter.mp hv).2
    let img : Finset ℕ := (Set.toFinite (R'.neighborSet v)).toFinset.image fun w => col s(v, w)
    have himg : #img ≤ (X.neighborSet v).ncard := by
      calc #img ≤ #((Set.toFinite (R'.neighborSet v)).toFinset) := card_image_le
        _ = (R'.neighborSet v).ncard := (Set.ncard_eq_toFinset_card _ _).symm
        _ ≤ (R.neighborSet v).ncard := ncard_neighborSet_le_of_le sdiff_le v
        _ ≤ _ := ncard_neighborSet_le_of_le hRX v
    have hsub : range (Δ - 1) \ img ⊆ avail v := by
      intro j hj
      rw [mem_sdiff] at hj
      refine mem_filter.mpr ⟨hj.1, fun w hw he => hj.2 ?_⟩
      exact mem_image.mpr ⟨w, by simpa using hw, he⟩
    have h1 := card_le_card hsub
    have h2 : Δ - 1 - #img ≤ #(range (Δ - 1) \ img) := by
      have := le_card_sdiff img (range (Δ - 1)); simpa using this
    omega
  obtain ⟨cs, lvl, hcov, hout, hcs, hsum, hemp, hlen⟩ :=
    exists_greedy_cover (P := Δ - 1) (by omega) avail U (fun v _ => filter_subset _ _) hthird
  refine ⟨⟨R, hRX, hterm', hD2, hDdeg, f, hf, hfinj, col, hcol, cs, lvl, fun v hv => ?_,
    fun v hv => hout v (by simp only [U, mem_filter, mem_univ, true_and]; exact hv), hcs, ?_, ?_⟩⟩
  · have hvU : v ∈ U := by simp only [U, mem_filter, mem_univ, true_and]; exact hv
    obtain ⟨h1, h2⟩ := hcov v hvU
    exact ⟨h1, mem_range.mp (mem_filter.mp h2).1, (mem_filter.mp h2).2⟩
  · calc ∑ v, lvl v = ∑ v ∈ U, lvl v :=
          (Finset.sum_subset (subset_univ U) fun v _ hv => hout v hv).symm
      _ ≤ 2 * #U := hsum
      _ ≤ 2 * Fintype.card V := Nat.mul_le_mul_left _ (card_le_univ _)
  · rcases U.eq_empty_or_nonempty with hU | hU
    · exact Or.inl (hemp hU)
    · right
      exact (hlen hU).trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (card_le_univ _)))

end Podc.RoundEfficientColoring
