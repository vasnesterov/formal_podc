import Papers.PODC2016.BoundedGenusMDS.Lemma12
import Cslib.Computability.Distributed.Local.Locality

/-!
# The modified algorithm is a 6-round LOCAL algorithm

Nodes are identified with the elements of a linearly ordered type `V` (unique identifiers). With the
tie-break "smallest identifier among the candidates of maximal residual degree" (`domMin`), the
output of the modified Algorithm 1 is a deterministic function of the graph, and whether `v`
belongs to it depends only on the radius-6 view of `v` (`output_isLocal`, in the sense of CSLib's
`Cslib.Local.IsLocal`). Radii: membership in `D` needs radius 2, membership in `N[D]` radius 3, the
residual degree radius 4, the dominator radius 5, the output radius 6.

Theorem 13 states `O(g)` rounds; the algorithm in fact needs a constant number of rounds.
-/

open Finset Cslib.Local

namespace Podc.BoundedGenusMDS

open SimpleGraph (Depth1Model IsDepth1Minor Depth1DensityLE ExcludesKt3 depth1_of_cover_two)

open Classical

variable {V : Type} [Fintype V] [LinearOrder V] {G G' : SimpleGraph V} {c : ℕ}

/-- Candidates for the dominator of `u`: vertices of `N[u]` of maximal residual degree. -/
noncomputable def domCand (G : SimpleGraph V) (c : ℕ) (u : V) : Finset V :=
  (cnbhd G {u}).filter fun w => ∀ w' ∈ cnbhd G {u}, resDeg G (phase1 G c) w' ≤ resDeg G (phase1 G c) w

lemma domCand_nonempty (G : SimpleGraph V) (c : ℕ) (u : V) : (domCand G c u).Nonempty := by
  obtain ⟨w, hw, hmax⟩ := (cnbhd G {u}).exists_max_image (resDeg G (phase1 G c))
    ⟨u, by simp⟩
  exact ⟨w, mem_filter.2 ⟨hw, hmax⟩⟩

/-- The deterministic dominator: the smallest identifier among the candidates. -/
noncomputable def domMin (G : SimpleGraph V) (c : ℕ) (u : V) : V :=
  (domCand G c u).min' (domCand_nonempty G c u)

lemma isDominator_domMin (G : SimpleGraph V) (c : ℕ) :
    IsDominator G (phase1 G c) (domMin G c) := by
  intro v _
  have h := mem_filter.1 ((domCand G c v).min'_mem (domCand_nonempty G c v))
  exact ⟨h.1, h.2⟩

omit [LinearOrder V] in
lemma edist_le_one_of_mem_cnbhd {u v : V} (h : u ∈ cnbhd G {v}) : G.edist v u ≤ 1 := by
  rcases mem_cnbhd_singleton.1 h with rfl | h
  · simp
  · exact (SimpleGraph.edist_eq_one_iff_adj.2 h).le

omit [LinearOrder V] in
lemma cnbhd_singleton_congr {u : V} {R : ℕ} (h : GAgree G G' u R) (hR : 0 < R) :
    cnbhd G {u} = cnbhd G' {u} := by
  ext y; simp only [mem_cnbhd_singleton, h.adj_iff hR y]

omit [LinearOrder V] in
lemma mem_phase1_congr {v : V} (h : GAgree G G' v 2) : v ∈ phase1 G c ↔ v ∈ phase1 G' c := by
  have hN : nbhd G v = nbhd G' v := by ext y; simp only [mem_nbhd, h.adj_iff (by norm_num) y]
  have hcov : ∀ A : Finset V, nbhd G v ⊆ cnbhd G A ↔ nbhd G' v ⊆ cnbhd G' A := by
    intro A
    rw [← hN]
    refine forall₂_congr fun x hx => ?_
    rw [mem_nbhd] at hx
    have hx2 : G.edist v x < 2 := by
      rw [SimpleGraph.edist_eq_one_iff_adj.2 hx]; norm_num
    simp only [mem_cnbhd]
    refine exists_congr fun a => and_congr_right fun _ => or_congr_right ?_
    rw [G.adj_comm, G'.adj_comm]; exact h hx2 a
  simp only [mem_phase1]
  exact not_congr (exists_congr fun A => and_congr_right fun _ => and_congr_right fun _ => hcov A)

omit [LinearOrder V] in
lemma mem_cnbhd_phase1_congr {y : V} (h : GAgree G G' y 3) :
    y ∈ cnbhd G (phase1 G c) ↔ y ∈ cnbhd G' (phase1 G' c) := by
  simp only [mem_cnbhd]
  refine exists_congr fun a => ?_
  by_cases hya : y = a
  · subst hya
    simp only [true_or, and_true]
    exact mem_phase1_congr (h.mono_radius (by norm_num))
  · simp only [hya, false_or]
    have hadj : G.Adj a y ↔ G'.Adj a y := by
      rw [G.adj_comm, G'.adj_comm]; exact h.adj_iff (by norm_num) a
    constructor
    · rintro ⟨ha, hay⟩
      have hd : G.edist y a ≤ 1 := (SimpleGraph.edist_eq_one_iff_adj.2 hay.symm).le
      exact ⟨(mem_phase1_congr (h.mono hd (by norm_num))).1 ha, hadj.1 hay⟩
    · rintro ⟨ha, hay⟩
      have hd : G.edist y a ≤ 1 := (SimpleGraph.edist_eq_one_iff_adj.2 (hadj.2 hay).symm).le
      exact ⟨(mem_phase1_congr (h.mono hd (by norm_num))).2 ha, hadj.2 hay⟩

omit [LinearOrder V] in
lemma resDeg_congr {w : V} (h : GAgree G G' w 4) :
    resDeg G (phase1 G c) w = resDeg G' (phase1 G' c) w := by
  simp only [resDeg]
  rw [← cnbhd_singleton_congr h (by norm_num)]
  congr 1
  ext y
  simp only [mem_sdiff]
  refine and_congr_right fun hy => not_congr ?_
  exact mem_cnbhd_phase1_congr (h.mono (edist_le_one_of_mem_cnbhd hy) (by norm_num))

lemma domMin_congr {u : V} (h : GAgree G G' u 5) : domMin G c u = domMin G' c u := by
  have hN := cnbhd_singleton_congr h (by norm_num)
  have hres : ∀ w ∈ cnbhd G {u}, resDeg G (phase1 G c) w = resDeg G' (phase1 G' c) w :=
    fun w hw => resDeg_congr (h.mono (edist_le_one_of_mem_cnbhd hw) (by norm_num))
  have hcand : domCand G c u = domCand G' c u := by
    simp only [domCand]
    rw [← hN]
    refine filter_congr fun w hw => ?_
    rw [hres w hw]
    exact forall₂_congr fun w' hw' => by rw [hres w' hw']
  simp only [domMin, hcand]

lemma mem_output_domMin_iff {v : V} : v ∈ output G c (domMin G c) ↔
    v ∈ phase1 G c ∨ ∃ u ∈ cnbhd G {v}, u ∉ cnbhd G (phase1 G c) ∧ domMin G c u = v := by
  simp only [output, mem_union, mem_image, mem_sdiff, mem_univ, true_and]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, ?_, hu, rfl⟩
    have := ((isDominator_domMin G c) u hu).1
    rcases mem_cnbhd_singleton.1 this with h | h
    · rw [mem_cnbhd_singleton]; exact Or.inl h.symm
    · rw [mem_cnbhd_singleton]; exact Or.inr h.symm
  · rintro ⟨u, -, hu, rfl⟩; exact ⟨u, hu, rfl⟩

/-- **Locality.** With identifier tie-breaking, membership in the output of the modified
Algorithm 1 is determined by the radius-6 view: the algorithm runs in 6 rounds of the LOCAL
model (independently of `c`, `t` and the genus). -/
theorem output_isLocal (c : ℕ) :
    IsLocal 6 (fun (G : SimpleGraph V) (_ : V → Unit) v => v ∈ output G c (domMin G c)) := by
  intro G x G' x' v hv
  have h := hv.1
  simp only [eq_iff_iff]
  rw [mem_output_domMin_iff, mem_output_domMin_iff, ← cnbhd_singleton_congr h (by norm_num)]
  refine or_congr (mem_phase1_congr (h.mono_radius (by norm_num))) (exists_congr fun u => ?_)
  refine and_congr_right fun hu => ?_
  have hd := edist_le_one_of_mem_cnbhd hu
  rw [mem_cnbhd_phase1_congr (h.mono hd (by norm_num)), domMin_congr (h.mono hd (by norm_num))]

/-- **Lemma 12, deterministic LOCAL version.** The 6-round algorithm `output G c (domMin G c)` is
a `(6c²t + (2t+5)c + 4)`-approximation on graphs whose depth-1 minors have density `≤ c` and that
exclude `K_{t,3}` as a depth-1 minor. -/
theorem lemma_12_local {t : ℕ} (hc : Depth1DensityLE G c) (ht : ExcludesKt3 G t) :
    IsApprox G (6 * c ^ 2 * t + (2 * t + 5) * c + 4) (output G c (domMin G c)) :=
  lemma_12 hc ht (isDominator_domMin G c)

end Podc.BoundedGenusMDS
