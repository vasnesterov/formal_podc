import Papers.PODC2016.BoundedGenusMDS.Lemma5

/-!
# The objects of the analysis in Section 3

For a dominating set `M` (the paper: a minimum one), an ordering `ord` of `M` with `M ∩ D` first,
and covering sets `C_m` (`m ∈ M \ D`), we define

* `star v` (`v ∉ M`): the first `m ∈ M` (w.r.t. `ord`) adjacent to `v`; the star of `m` is
  `leaves m = N_{E'}(m) = {v ∉ M : star v = m}` (the paper's inductively defined edge set `E'`);
* `C = ⋃_{m ∈ M \ D} C_m`;
* the paper's `Y` (`Ypaper`) and `Z`;
* our corrected `Y` (vertices outside `M ∪ C` with a neighbour outside `M ∪ C` in another star)
  and `YD` (the part of it seeing a star of `M ∩ D`).
-/

open Finset

namespace Podc.BoundedGenusMDS

open SimpleGraph (Depth1Model IsDepth1Minor Depth1DensityLE ExcludesKt3 depth1_of_cover_two)

open Classical

variable {V : Type} [Fintype V]

/-- The data fixed in Section 3 ("we fix `M` and `D` as in Lemma 5", "we fix an ordering of `M`
such that the vertices of `M ∩ D` are first", "for each `m ∈ M \ D`, we fix a set `C_m`"). -/
structure Setup (G : SimpleGraph V) (c : ℕ) where
  /-- The dominating set (the paper: a minimum dominating set). -/
  M : Finset V
  hM : G.IsDominatingSet (M : Set V)
  /-- The ordering `m₁, …, m_{|M|}` of `M`, as a rank function. -/
  ord : V → ℕ
  ord_inj : ∀ m ∈ M, ∀ m' ∈ M, ord m = ord m' → m = m'
  ord_D : ∀ m ∈ M, ∀ m' ∈ M, m ∈ phase1 G c → m' ∉ phase1 G c → ord m < ord m'
  /-- The covering sets `C_m`. -/
  Cm : V → Finset V
  Cm_spec : ∀ m ∈ M, m ∉ phase1 G c →
    m ∉ Cm m ∧ (Cm m).card ≤ 2 * c ∧ nbhd G m ⊆ cnbhd G (Cm m)

namespace Setup

variable {G : SimpleGraph V} {c : ℕ} (S : Setup G c)

/-- The set `D` of Phase 1. -/
noncomputable abbrev D (_S : Setup G c) : Finset V := phase1 G c

lemma exists_star (v : V) (hv : v ∉ S.M) :
    ∃ m ∈ S.M.filter (G.Adj v), ∀ m' ∈ S.M.filter (G.Adj v), S.ord m ≤ S.ord m' := by
  refine Finset.exists_min_image _ S.ord ?_
  rcases S.hM v with h | ⟨u, hu, h⟩
  · exact absurd (by simpa using h) hv
  · exact ⟨u, mem_filter.2 ⟨by simpa using hu, h⟩⟩

/-- `star v`: the first vertex of `M` adjacent to `v` (for `v ∉ M`); `v` itself otherwise. -/
noncomputable def star (v : V) : V :=
  if h : v ∉ S.M then (S.exists_star v h).choose else v

lemma star_spec {v : V} (hv : v ∉ S.M) :
    S.star v ∈ S.M ∧ G.Adj v (S.star v) ∧ ∀ m ∈ S.M, G.Adj v m → S.ord (S.star v) ≤ S.ord m := by
  have h := (S.exists_star v hv).choose_spec
  simp only [star, hv, not_false_eq_true, dite_true]
  rw [mem_filter] at h
  exact ⟨h.1.1, h.1.2, fun m hm hvm => h.2 m (mem_filter.2 ⟨hm, hvm⟩)⟩

lemma star_mem {v : V} (hv : v ∉ S.M) : S.star v ∈ S.M := (S.star_spec hv).1
lemma adj_star {v : V} (hv : v ∉ S.M) : G.Adj v (S.star v) := (S.star_spec hv).2.1
lemma ord_star_le {v m : V} (hv : v ∉ S.M) (hm : m ∈ S.M) (h : G.Adj v m) :
    S.ord (S.star v) ≤ S.ord m := (S.star_spec hv).2.2 m hm h

/-- `N_{E'}(m)`: the leaves of the star of `m`. -/
noncomputable def leaves (m : V) : Finset V := univ.filter fun v => v ∉ S.M ∧ S.star v = m

@[simp] lemma mem_leaves {m v : V} : v ∈ S.leaves m ↔ v ∉ S.M ∧ S.star v = m := by
  simp [leaves]

/-- `C = ⋃_{m ∈ M \ D} C_m`. -/
noncomputable def C : Finset V := (S.M \ S.D).biUnion S.Cm

lemma mem_C_of {m x : V} (hm : m ∈ S.M) (hmD : m ∉ S.D) (hx : x ∈ S.Cm m) : x ∈ S.C :=
  mem_biUnion.2 ⟨m, mem_sdiff.2 ⟨hm, hmD⟩, hx⟩

lemma card_C_le : S.C.card ≤ 2 * c * S.M.card := by
  calc S.C.card ≤ ∑ m ∈ S.M \ S.D, (S.Cm m).card := card_biUnion_le
    _ ≤ ∑ _m ∈ S.M \ S.D, 2 * c := sum_le_sum fun m hm => by
        rw [mem_sdiff] at hm; exact (S.Cm_spec m hm.1 hm.2).2.1
    _ = (S.M \ S.D).card * (2 * c) := by rw [sum_const, smul_eq_mul]
    _ ≤ S.M.card * (2 * c) := Nat.mul_le_mul_right _ (card_le_card sdiff_subset)
    _ = 2 * c * S.M.card := by ring

lemma card_MC_le : (S.M ∪ S.C).card ≤ (2 * c + 1) * S.M.card := by
  have := S.card_C_le
  calc (S.M ∪ S.C).card ≤ S.M.card + S.C.card := card_union_le _ _
    _ ≤ _ := by nlinarith

/-- For `m ∈ M \ D`, every leaf of `m` outside `C` is adjacent to some `c' ∈ C_m`. -/
lemma exists_Cm_adj {m u : V} (hm : m ∈ S.M) (hmD : m ∉ S.D) (hu : u ∈ S.leaves m)
    (huC : u ∉ S.C) : ∃ c' ∈ S.Cm m, G.Adj c' u := by
  rw [mem_leaves] at hu
  have hadj : u ∈ nbhd G m := by
    rw [mem_nbhd]; have := S.adj_star hu.1; rw [hu.2] at this; exact this.symm
  obtain ⟨c', hc', h⟩ := mem_cnbhd.1 ((S.Cm_spec m hm hmD).2.2 hadj)
  rcases h with rfl | h
  · exact absurd (S.mem_C_of hm hmD hc') huC
  · exact ⟨c', hc', h⟩

/-- The paper's `Y`: leaves of stars of `M \ D` adjacent to a leaf of another star. -/
noncomputable def Ypaper : Finset V :=
  univ.filter fun u => u ∉ S.M ∧ S.star u ∉ S.D ∧
    ∃ v, v ∉ S.M ∧ S.star v ≠ S.star u ∧ G.Adj u v

/-- The paper's `Z = {u ∈ N_{E'}(M \ D) : |N(u) ∩ (M ∪ C)| > 4c}`. -/
noncomputable def Z : Finset V :=
  univ.filter fun u => u ∉ S.M ∧ S.star u ∉ S.D ∧ 4 * c < (nbhd G u ∩ (S.M ∪ S.C)).card

/-- Corrected `Y`: leaves outside `C` of stars of `M \ D`, adjacent to a leaf outside `C` of
another star. -/
noncomputable def Y : Finset V :=
  univ.filter fun u => u ∉ S.M ∧ u ∉ S.C ∧ S.star u ∉ S.D ∧
    ∃ v, v ∉ S.M ∧ v ∉ S.C ∧ S.star v ≠ S.star u ∧ G.Adj u v

/-- The part of the corrected `Y` that sees (outside `C`) a star of `M ∩ D`. -/
noncomputable def YD : Finset V :=
  univ.filter fun u => u ∉ S.M ∧ u ∉ S.C ∧ S.star u ∉ S.D ∧
    ∃ v, v ∉ S.M ∧ v ∉ S.C ∧ S.star v ∈ S.D ∧ G.Adj u v

/-- `X a b`: leaves of `b` outside `C` with a neighbour among the leaves of `a` outside `C`. -/
noncomputable def X (a b : V) : Finset V :=
  (S.leaves b \ S.C).filter fun u => ∃ v ∈ S.leaves a \ S.C, G.Adj u v

end Setup

/-- A `Setup` exists for every dominating set `M`. -/
lemma Setup.exists_of_dominating {G : SimpleGraph V} {c : ℕ} {M : Finset V}
    (hM : G.IsDominatingSet (M : Set V)) : ∃ S : Setup G c, S.M = M := by
  let D := phase1 G c
  let e := Fintype.equivFin V
  let n := Fintype.card V
  let ord : V → ℕ := fun v => (if v ∈ D then 0 else n) + e v
  have hlt : ∀ v, (e v : ℕ) < n := fun v => (e v).2
  have hcov : ∀ m, m ∉ D → ∃ A : Finset V, m ∉ A ∧ A.card ≤ 2 * c ∧ nbhd G m ⊆ cnbhd G A :=
    fun m hm => by simpa [D, mem_phase1] using hm
  refine ⟨{ M := M, hM := hM, ord := ord, ord_inj := ?_, ord_D := ?_,
            Cm := fun m => if h : m ∉ D then (hcov m h).choose else ∅, Cm_spec := ?_ }, rfl⟩
  · intro m _ m' _ h
    have h1 := hlt m; have h2 := hlt m'
    simp only [ord] at h
    have : (e m : ℕ) = e m' := by split_ifs at h <;> omega
    exact e.injective (Fin.ext this)
  · intro m _ m' _ hm hm'
    have h1 := hlt m
    simp only [ord, show m ∈ D from hm, show m' ∉ D from hm', ite_true, ite_false]
    omega
  · intro m _ hm
    simp only [show m ∉ D from hm, not_false_eq_true, dite_true]
    exact (hcov m hm).choose_spec

end Podc.BoundedGenusMDS
