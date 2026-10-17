import Papers.PODC2026.TreeAA.Spec
import Cslib.Foundations.Data.Finset.Quorum

/-!
# The combinatorial core of `TreeAA` (Lemmas 2, 6–11)

Spec-level statements: they talk about the *values* the honest parties hold (received gradecast
outputs, paths, RealAA outputs), not about protocols; `Protocol.lean` plugs them into the
lock-step model.

* `proj_mem_hull` — **Lemma 2** (projection of an input onto a root path that meets the hull).
* `exists_common_prefix` — the role of **Lemma 11**: a root path ending in the hull which is a
  common prefix of the root paths of all honest inputs (we take the hull vertex closest to the
  root instead of the longest common prefix; see `differencies.md`).
* `pathsFinder_spec` — **Lemma 10** (`PathsFinder` with `t < n/2`, gradecast as a spec).
* `fromPaths_spec`, `close_projIdx` — **Lemmas 6–9** (`TreeAAFromPaths`, RealAA as a spec).
-/

namespace TreeAA

open SimpleGraph

variable {P V : Type*} {T : SimpleGraph V} (hT : T.IsTree) [DecidableEq V]

include hT in
/-- **Lemma 2** (general form): let `K` be the vertex set of a path `P(a, b)` of the tree that
meets the hull of `S`, and `g ∈ K` a vertex of `K` closest to `v ∈ S` (the projection
`proj_P(v)`). Then `g` lies in the hull of `S`. -/
theorem lemma2 {S : Set V} {a b v g : V} (hv : v ∈ S) (hg : Btw T a g b)
    (hmin : ∀ k, Btw T a k b → T.dist v g ≤ T.dist v k) (hint : ∃ w, Btw T a w b ∧ w ∈ hull T S) :
    g ∈ hull T S := by
  obtain ⟨w, hw, hwS⟩ := hint
  exact hull_convex hT (subset_hull S hv) hwS
    (btw_of_isMin hT (convex_btw hT a b) hg hmin hw)

/-- **Lemma 2.** If the root path to `u` meets the hull of `S`, the projection of any `v ∈ S`
onto it lies in the hull. -/
theorem proj_mem_hull {S : Set V} {r u v : V} (hv : v ∈ S)
    (hint : ∃ w ∈ rpath hT r u, w ∈ hull T S) :
    (rpath hT r u).getD (projIdx T (rpath hT r u) v) v ∈ hull T S := by
  have hL : rpath hT r u ≠ [] := rpath_ne_nil hT r u
  have hi : projIdx T (rpath hT r u) v < (rpath hT r u).length := projIdx_lt hL v
  have hgL : (rpath hT r u).getD (projIdx T (rpath hT r u) v) v ∈ rpath hT r u := by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  obtain ⟨w, hwL, hwS⟩ := hint
  have hmin : ∀ k ∈ {w | Btw T r w u},
      T.dist v ((rpath hT r u).getD (projIdx T (rpath hT r u) v) v) ≤ T.dist v k := by
    intro k hk
    have hkL : k ∈ rpath hT r u := (mem_rpath hT).2 hk
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hkL
    exact projIdx_min hL v hj
  have hbtw := btw_of_isMin hT (convex_btw hT r u) ((mem_rpath hT).1 hgL) hmin
    ((mem_rpath hT).1 hwL)
  exact hull_convex hT (subset_hull S hv) hwS hbtw

/-- **Lemma 11** (in the form used by Lemma 10): for a nonempty vertex set `S` there is a vertex
`m` of its hull whose root path is a prefix of the root path of every vertex of `S`. (`m` is
the hull vertex closest to the root; the root path of `m` is the longest common prefix.) -/
theorem exists_common_prefix {S : Set V} (hS : S.Nonempty) (r : V) :
    ∃ m ∈ hull T S, ∀ s ∈ S, rpath hT r m <+: rpath hT r s := by
  classical
  have hex : ∃ n, ∃ k ∈ hull T S, T.dist r k = n :=
    ⟨_, hS.some, subset_hull S hS.some_mem, rfl⟩
  obtain ⟨m, hm, hmd⟩ := Nat.find_spec hex
  refine ⟨m, hm, fun s hs => ?_⟩
  have hmin : ∀ k ∈ hull T S, T.dist r m ≤ T.dist r k := fun k hk =>
    hmd ▸ Nat.find_min' hex ⟨k, hk, rfl⟩
  have := btw_of_isMin hT (convex_hull hT S) hm hmin (subset_hull S hs)
  exact rpath_prefix hT ((mem_rpath hT).2 this)

section PathsFinder

variable [Fintype P]

/-- **Lemma 10** (`PathsFinder`, spec level). Every honest party `p` has received, from every
sender `s`, a pair `d p s` (path, grade) such that honest senders' root paths arrive with grade 2
(integrity) and a grade-2 path received by an honest party is received by every honest party
with grade at least 1 (consistency). If `t < n/2`, the paths `P = lsp (n-t) (d p) 2` and
`Q = lsp (n-t) (d p) 1` satisfy the preconditions of `TreeAAFromPaths`: each `P` is a non-empty
root path meeting the hull of the honest inputs, and each `P` is a prefix of each `Q`. -/
theorem pathsFinder_spec (r : V) {t : ℕ} (ht : 2 * t < Fintype.card P) {H : Set P}
    (hH : Hᶜ.ncard ≤ t) (x : P → V) (d : P → P → List V × Fin 3)
    (hint : ∀ s ∈ H, ∀ p ∈ H, d p s = (rpath hT r (x s), 2))
    (hcons : ∀ p ∈ H, ∀ q ∈ H, ∀ s, (d p s).2 = 2 → (d q s).1 = (d p s).1 ∧ 1 ≤ (d q s).2) :
    (∀ p ∈ H, lsp (Fintype.card P - t) (d p) 2 ≠ [] ∧
        (∃ u, lsp (Fintype.card P - t) (d p) 2 = rpath hT r u) ∧
        ∃ w ∈ lsp (Fintype.card P - t) (d p) 2, w ∈ hull T (x '' H)) ∧
      (∀ p ∈ H, ∀ q ∈ H,
        lsp (Fintype.card P - t) (d p) 2 <+: lsp (Fintype.card P - t) (d q) 1) := by
  classical
  set k := Fintype.card P - t with hk
  have hk0 : 0 < k := by omega
  have hk2 : Fintype.card P < 2 * k := by omega
  have hHcard : k ≤ (Finset.univ.filter (· ∈ H)).card := by
    have := Finset.card_sub_le_card_filter_notMem_of_ncard_le (B := Hᶜ) hH
    simp only [Set.mem_compl_iff, not_not] at this
    convert this using 2
  have hHne : H.Nonempty := by
    obtain ⟨s, hs⟩ := Finset.card_pos.1 (lt_of_lt_of_le hk0 hHcard)
    exact ⟨s, (Finset.mem_filter.1 hs).2⟩
  obtain ⟨m, hm, hpre⟩ := exists_common_prefix hT (hHne.image x) r
  -- the root path of `m` is supported by all honest senders in every honest view
  have hsupp : ∀ p ∈ H, ∀ g : Fin 3, k ≤ (supporters (d p) g (rpath hT r m)).card := by
    intro p hp g
    refine hHcard.trans (Finset.card_le_card ?_)
    intro s hs
    have hsH := (Finset.mem_filter.1 hs).2
    rw [mem_supporters, hint s hsH p hp]
    exact ⟨Fin.le_last g, hpre _ ⟨s, hsH, rfl⟩⟩
  have hP : ∀ p ∈ H, rpath hT r m <+: lsp k (d p) 2 ∧
      k ≤ (supporters (d p) 2 (lsp k (d p) 2)).card := by
    intro p hp
    obtain ⟨hs, hl⟩ := lsp_spec hk0 (hsupp p hp 2)
    refine ⟨?_, hs⟩
    rcases prefix_or_prefix_of_supported hk2 (hsupp p hp 2) hs with h | h
    · exact h
    · rw [h.eq_of_length (le_antisymm h.length_le hl)]
  refine ⟨fun p hp => ?_, fun p hp q hq => ?_⟩
  · obtain ⟨hpre', hs⟩ := hP p hp
    have hne : lsp k (d p) 2 ≠ [] := by
      intro h; rw [h] at hpre'; exact rpath_ne_nil hT r m (List.prefix_nil.1 hpre')
    obtain ⟨s, hs1, hsH⟩ := Finset.exists_mem_notMem_of_ncard_le_of_lt hH
      (lt_of_lt_of_le (by omega) hs)
    rw [Set.notMem_compl_iff] at hsH
    rw [mem_supporters, hint s hsH p hp] at hs1
    refine ⟨hne, ⟨_, eq_rpath_of_prefix hT hs1.2 hne⟩, m, hpre'.subset (mem_rpath_self hT r m), hm⟩
  · obtain ⟨-, hs⟩ := hP p hp
    have hsub : supporters (d p) 2 (lsp k (d p) 2) ⊆ supporters (d q) 1 (lsp k (d p) 2) := by
      intro s hs'
      rw [mem_supporters] at hs' ⊢
      have h2 : (d p s).2 = 2 := le_antisymm (Fin.le_last _) hs'.1
      obtain ⟨he, hg⟩ := hcons p hp q hq s h2
      exact ⟨hg, he ▸ hs'.2⟩
    have hs' := hs.trans (Finset.card_le_card hsub)
    obtain ⟨hsQ, hlQ⟩ := lsp_spec hk0 hs'
    rcases prefix_or_prefix_of_supported hk2 hs' hsQ with h | h
    · exact h
    · rw [h.eq_of_length (le_antisymm h.length_le hlQ)]

end PathsFinder

section FromPaths

/-- **Lemmas 6–9** (`TreeAAFromPaths`, spec level). Assume every honest party holds a non-empty
root path `P` meeting the hull of the honest inputs and a path `Q`, every honest `P` being a
prefix of every honest `Q` (Lemma 6's hypotheses), and that the honest RealAA outputs `j` lie in
the range of the honest RealAA inputs (the projection indices) and are 1-close. Then the outputs
`Q[[j]]` are in the hull of the honest inputs and pairwise at distance at most one. -/
theorem fromPaths_spec (r : V) [Finite P] {H : Set P} (x : P → V) (Pp Qp : P → List V)
    (j : P → ℝ)
    (hP : ∀ p ∈ H, Pp p ≠ [] ∧ (∃ u, Pp p = rpath hT r u) ∧ ∃ w ∈ Pp p, w ∈ hull T (x '' H))
    (hPQ : ∀ p ∈ H, ∀ q ∈ H, Pp p <+: Qp q)
    (hval : ∀ p ∈ H, ∃ a ∈ H, ∃ b ∈ H,
      (projIdx T (Pp a) (x a) : ℝ) ≤ j p ∧ j p ≤ projIdx T (Pp b) (x b))
    (hagr : ∀ p ∈ H, ∀ q ∈ H, |j p - j q| ≤ 1) :
    (∀ p ∈ H, (Qp p).getD (rnd (j p)).toNat (x p) ∈ hull T (x '' H)) ∧
    (∀ p ∈ H, ∀ q ∈ H,
      T.dist ((Qp p).getD (rnd (j p)).toNat (x p)) ((Qp q).getD (rnd (j q)).toNat (x q)) ≤ 1) := by
  classical
  rcases H.eq_empty_or_nonempty with rfl | hHne
  · simp
  -- the longest honest path `L = P*`
  obtain ⟨pm, hpm, hmax⟩ := (H.toFinite.toFinset).exists_max_image (fun p => (Pp p).length)
    (by simpa using hHne)
  rw [Set.Finite.mem_toFinset] at hpm
  simp only [Set.Finite.mem_toFinset] at hmax
  obtain ⟨-, ⟨u, hu⟩, -⟩ := hP pm hpm
  set L := Pp pm with hLdef
  have hLpre : ∀ q ∈ H, Pp q <+: L := by
    intro q hq
    rcases List.prefix_or_prefix_of_prefix (hPQ q hq pm hpm) (hPQ pm hpm pm hpm) with h | h
    · exact h
    · have e : Pp pm = Pp q := h.eq_of_length (le_antisymm h.length_le (hmax q hq))
      rw [hLdef, e]
  -- projection indices and their vertices
  have hidx : ∀ q ∈ H, projIdx T (Pp q) (x q) < L.length := fun q hq =>
    lt_of_lt_of_le (projIdx_lt (hP q hq).1 (x q)) (hLpre q hq).length_le
  have hproj : ∀ q (hq : q ∈ H), L[projIdx T (Pp q) (x q)]'(hidx q hq) ∈ hull T (x '' H) := by
    intro q hq
    obtain ⟨hne, ⟨uq, huq⟩, hw⟩ := hP q hq
    have hi := projIdx_lt (G := T) hne (x q)
    have := proj_mem_hull hT (S := x '' H) ⟨q, hq, rfl⟩ (r := r) (u := uq) (huq ▸ hw)
    rw [← huq, List.getD_eq_getElem _ _ hi] at this
    rwa [← (hLpre q hq).getElem hi]
  -- the rounded outputs are indices of `L`
  have hk : ∀ p ∈ H, ∃ a ∈ H, ∃ b ∈ H, projIdx T (Pp a) (x a) ≤ (rnd (j p)).toNat ∧
      (rnd (j p)).toNat ≤ projIdx T (Pp b) (x b) := by
    intro p hp
    obtain ⟨a, ha, b, hb, h1, h2⟩ := hval p hp
    obtain ⟨h1', h2'⟩ := rnd_mem_Icc h1 h2
    exact ⟨a, ha, b, hb, by omega, by omega⟩
  have hkL : ∀ p ∈ H, (rnd (j p)).toNat < L.length := by
    intro p hp
    obtain ⟨a, ha, b, hb, -, h2⟩ := hk p hp
    exact lt_of_le_of_lt h2 (hidx b hb)
  have hout : ∀ p (hp : p ∈ H),
      (Qp p).getD (rnd (j p)).toNat (x p) = L[(rnd (j p)).toNat]'(hkL p hp) := by
    intro p hp
    have hLQ := hPQ pm hpm p hp
    rw [List.getD_eq_getElem _ _ (lt_of_lt_of_le (hkL p hp) hLQ.length_le), hLQ.getElem]
  refine ⟨fun p hp => ?_, fun p hp q hq => ?_⟩
  · rw [hout p hp]
    obtain ⟨a, ha, b, hb, h1, h2⟩ := hk p hp
    have hbtw : Btw T (L[projIdx T (Pp a) (x a)]'(hidx a ha)) (L[(rnd (j p)).toNat]'(hkL p hp))
        (L[projIdx T (Pp b) (x b)]'(hidx b hb)) := by
      have := btw_rpath_getElem hT r u h1 h2 (by rw [← hu]; exact hidx b hb)
      simpa only [← hu] using this
    exact hull_convex hT (hproj a ha) (hproj b hb) hbtw
  · rw [hout p hp, hout q hq]
    have hc := rnd_close (hagr p hp q hq)
    obtain ⟨a, ha, -, -, h1, -⟩ := hk p hp
    obtain ⟨a', ha', -, -, h1', -⟩ := hk q hq
    have hpos : 0 ≤ rnd (j p) := by
      obtain ⟨a, ha, b, hb, h1, h2⟩ := hval p hp
      have := (rnd_mem_Icc h1 h2).1; omega
    have hpos' : 0 ≤ rnd (j q) := by
      obtain ⟨a, ha, b, hb, h1, h2⟩ := hval q hq
      have := (rnd_mem_Icc h1 h2).1; omega
    have hchain : L.IsChain T.Adj := by rw [hu]; exact rpath_isChain hT r u
    rw [abs_le] at hc
    exact dist_getElem_le' hT.connected hchain _ _ (by omega) (by omega)

/-- The honest RealAA inputs of `TreeAAFromPaths` (projection indices on root paths) are
`D(T)`-close. -/
lemma close_projIdx (r : V) [Finite V] {H : Set P} (x : P → V) (Pp : P → List V)
    (hP : ∀ p ∈ H, Pp p ≠ [] ∧ ∃ u, Pp p = rpath hT r u) :
    Close (T.diam : ℝ) (fun p => (projIdx T (Pp p) (x p) : ℝ)) H := by
  have : Nonempty V := ⟨r⟩
  have hdiam : T.ediam ≠ ⊤ := connected_iff_ediam_ne_top.1 hT.connected
  have hb : ∀ p ∈ H, projIdx T (Pp p) (x p) ≤ T.diam := by
    intro p hp
    obtain ⟨hne, u, hu⟩ := hP p hp
    have h1 := projIdx_lt (G := T) hne (x p)
    rw [hu, length_rpath] at h1
    have h2 := dist_le_diam hdiam (u := r) (v := u)
    rw [hu]; omega
  intro p hp q hq
  have h1 := hb p hp
  have h2 := hb q hq
  rw [abs_le]
  constructor
  · have : (projIdx T (Pp q) (x q) : ℝ) ≤ T.diam := by exact_mod_cast h2
    have : (0 : ℝ) ≤ projIdx T (Pp p) (x p) := Nat.cast_nonneg _
    linarith
  · have : (projIdx T (Pp p) (x p) : ℝ) ≤ T.diam := by exact_mod_cast h1
    have : (0 : ℝ) ≤ projIdx T (Pp q) (x q) := Nat.cast_nonneg _
    linarith

end FromPaths

end TreeAA
