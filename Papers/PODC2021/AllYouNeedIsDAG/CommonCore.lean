import Papers.PODC2021.AllYouNeedIsDAG.Ordering

/-!
# DAG-Rider: the common core of a wave (Lemma 2)

Keidar, Kokoris-Kogias, Naor, Spiegelman, *All You Need is DAG*, PODC 2021 (arXiv:2102.08325v2),
Lemma 2: "Let `p_i` be a correct process that completes wave `w`. Then there is a set
`V ⊆ DAG_i[round(w,1)]` and a set `U ⊆ DAG_i[round(w,4)]` s.t. `|V| ≥ 2f+1`, `|U| ≥ 2f+1` and
`∀ v ∈ V, ∀ u ∈ U: strong_path(u, v)`."

The paper argues via the common-core abstraction. We prove a stronger, *robust* version that is
what the probabilistic argument (Claim 6, see `Coin.lean`) really needs:

* `core f C w E3` is the set of sources `s` such that the round-`(w,1)` vertex of `s` is strongly
  reached by at least `f + 1` of the round-`(w,3)` vertices with sources in `E3`. It only depends on
  the strong past of these round-`(w,3)` vertices (`core_congr`), so it is fixed as soon as
  `2f + 1` vertices of round `(w,3)` exist — before the coin of wave `w` is revealed.
* `core_card`: `|core| ≥ 2f + 1` (double counting, `n ≤ 3f + 1`).
* `sPath_of_mem_core`: **every** vertex of round `(w,4)` with `≥ 2f + 1` strong edges, created by
  anybody at any later time, strongly reaches all vertices of the core.
* `commit_of_mem_core`: if the coin of wave `w` lands in the core, the commit rule (line 36 of
  Algorithm 3) holds in every closed, valid local DAG with `2f + 1` vertices of round `(w,4)`.
* `lemma2`: the paper's Lemma 2.

Throughout, `n = |P| ≤ 3f + 1` (the paper has `n = 3f + 1`). The hypothesis `1 ≤ w` of the paper
is not needed (`wround w 1 ≥ 1` always holds).
-/

namespace DagRider

open Finset

variable {P : Type*} {B : Type*}

/-! ### Strong paths of length one and two -/

section Paths

variable {C : Content P B}

/-- The first edge of a strong path going down at least one round. -/
lemma sPath_iff_head {v u : Vtx P} (h : u.1 < v.1) :
    SPath C v u ↔ ∃ t ∈ C.strong v, 1 ≤ v.1 - 1 ∧ SPath C (v.1 - 1, t) u := by
  unfold SPath
  rw [Relation.ReflTransGen.cases_head_iff]
  constructor
  · rintro (rfl | ⟨x, ⟨e1, e2, e3⟩, hx⟩)
    · exact absurd h (lt_irrefl _)
    · refine ⟨x.2, e2, by omega, ?_⟩
      have : (v.1 - 1, x.2) = x := Prod.ext (by simp; omega) rfl
      rwa [this]
  · rintro ⟨t, ht, h1, hp⟩
    exact Or.inr ⟨(v.1 - 1, t), ⟨by simp; omega, ht, h1⟩, hp⟩

/-- A strong path of length one. -/
lemma sPath_succ_iff {r : ℕ} (hr : 1 ≤ r) (j s : P) :
    SPath C (r + 1, j) (r, s) ↔ s ∈ C.strong (r + 1, j) := by
  rw [sPath_iff_head (by simp)]
  simp only [Nat.add_sub_cancel]
  constructor
  · rintro ⟨t, ht, -, hp⟩
    rcases sPath_iff_tail.1 hp with h' | ⟨x, hx, e⟩
    · rw [Prod.mk.injEq] at h'; rwa [h'.2]
    · have := hx.round_le; have := e.1; simp at *; omega
  · intro hs
    exact ⟨s, hs, hr, SPath.refl _⟩

/-- A strong path of length two. -/
lemma sPath_succ_succ_iff {r : ℕ} (hr : 1 ≤ r) (k s : P) :
    SPath C (r + 2, k) (r, s) ↔ ∃ j ∈ C.strong (r + 2, k), s ∈ C.strong (r + 1, j) := by
  rw [sPath_iff_head (by simp)]
  simp only [show r + 2 - 1 = r + 1 by omega]
  constructor
  · rintro ⟨j, hj, -, hp⟩
    exact ⟨j, hj, (sPath_succ_iff hr j s).1 hp⟩
  · rintro ⟨j, hj, hs⟩
    exact ⟨j, hj, by omega, (sPath_succ_iff hr j s).2 hs⟩

/-- Strong reachability from `x` only depends on the strong edges of the vertices strongly
reachable from `x`. -/
lemma sPath_congr {C' : Content P B} {x : Vtx P}
    (h : ∀ v, SPath C x v → C.strong v = C'.strong v) (y : Vtx P) :
    SPath C x y ↔ SPath C' x y := by
  constructor
  · intro hp
    induction hp with
    | refl => exact SPath.refl _
    | tail hxa e ih =>
      refine Relation.ReflTransGen.tail ih ⟨e.1, ?_, e.2.2⟩
      rw [← h _ hxa]; exact e.2.1
  · intro hp
    induction hp with
    | refl => exact SPath.refl _
    | tail _ e ih =>
      refine Relation.ReflTransGen.tail ih ⟨e.1, ?_, e.2.2⟩
      rw [h _ ih]; exact e.2.1

end Paths

lemma wround_two (w : ℕ) : wround w 2 = wround w 1 + 1 := rfl
lemma wround_three (w : ℕ) : wround w 3 = wround w 1 + 2 := rfl
lemma wround_three' (w : ℕ) : wround w 3 = wround w 2 + 1 := rfl
lemma wround_four_succ (w : ℕ) : wround w 4 = wround w 3 + 1 := rfl
lemma one_le_wround_one (w : ℕ) : 1 ≤ wround w 1 := by unfold wround; omega

/-! ### The common core -/

variable [Fintype P] [DecidableEq P]

/-- The common core of wave `w` determined by the set `E3` of sources of round-`(w,3)` vertices:
the sources `s` whose round-`(w,1)` vertex is strongly reached by at least `f + 1` of the
round-`(w,3)` vertices with sources in `E3`. -/
def core (f : ℕ) (C : Content P B) (w : ℕ) (E3 : Finset P) : Finset P :=
  univ.filter (fun s => f + 1 ≤ (E3.filter (fun k => SPath C (wround w 3, k) (wround w 1, s))).card)

/-- **Size of the common core** (the counting step behind Lemma 2): if `n ≤ 3f + 1`, at least
`2f + 1` round-`(w,3)` vertices are given (sources `E3`), each with `≥ 2f + 1` strong edges, and
the round-`(w,2)` vertices they point to also have `≥ 2f + 1` strong edges each, then the core
has at least `2f + 1` elements. -/
theorem core_card {f : ℕ} (hn : Fintype.card P ≤ 3 * f + 1) (C : Content P B) (w : ℕ)
    {E3 : Finset P} (hE3 : 2 * f + 1 ≤ E3.card)
    (h3 : ∀ k ∈ E3, 2 * f + 1 ≤ (C.strong (wround w 3, k)).card)
    (h2 : ∀ k ∈ E3, ∀ j ∈ C.strong (wround w 3, k), 2 * f + 1 ≤ (C.strong (wround w 2, j)).card) :
    2 * f + 1 ≤ (core f C w E3).card := by
  by_contra hlt
  push Not at hlt
  -- in-degree of a round-`(w,2)` vertex `j` from `E3`
  let indeg : P → ℕ := fun j => (E3.filter (fun k => j ∈ C.strong (wround w 3, k))).card
  have hdeg : ∀ j, indeg j ≤ f := by
    intro j
    by_cases hne : (E3.filter (fun k => j ∈ C.strong (wround w 3, k))).Nonempty
    · obtain ⟨k, hk⟩ := hne
      rw [mem_filter] at hk
      have hj := h2 k hk.1 j hk.2
      -- `j` points to some `s` outside the core
      obtain ⟨s, hs, hsc⟩ : ∃ s ∈ C.strong (wround w 2, j), s ∉ core f C w E3 := by
        by_contra hall
        push Not at hall
        have := card_le_card hall
        omega
      have hsc' : ¬ f + 1 ≤ (E3.filter
          (fun k => SPath C (wround w 3, k) (wround w 1, s))).card := by
        simpa [core] using hsc
      have hsub : E3.filter (fun k => j ∈ C.strong (wround w 3, k)) ⊆
          E3.filter (fun k => SPath C (wround w 3, k) (wround w 1, s)) := by
        intro k' hk'
        rw [mem_filter] at hk' ⊢
        refine ⟨hk'.1, ?_⟩
        rw [wround_three, sPath_succ_succ_iff (one_le_wround_one w)]
        exact ⟨j, hk'.2, hs⟩
      show (E3.filter (fun k => j ∈ C.strong (wround w 3, k))).card ≤ f
      exact (card_le_card hsub).trans (by omega)
    · rw [not_nonempty_iff_eq_empty] at hne
      simp [indeg, hne]
  -- double counting of the strong edges from `E3` to round `(w,2)`
  have hdc : ∑ k ∈ E3, (C.strong (wround w 3, k)).card = ∑ j : P, indeg j := by
    have := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun k j => j ∈ C.strong (wround w 3, k)) (s := E3) (t := (univ : Finset P))
    simp only [bipartiteAbove, bipartiteBelow, filter_mem_eq_inter, univ_inter] at this
    exact this
  have hlow : E3.card * (2 * f + 1) ≤ ∑ k ∈ E3, (C.strong (wround w 3, k)).card := by
    rw [← smul_eq_mul, ← sum_const]
    exact sum_le_sum h3
  have hup : ∑ j : P, indeg j ≤ Fintype.card P * f := by
    calc ∑ j : P, indeg j ≤ ∑ _j : P, f := sum_le_sum (fun j _ => hdeg j)
      _ = Fintype.card P * f := by simp
  have h1 : (2 * f + 1) * (2 * f + 1) ≤ E3.card * (2 * f + 1) := Nat.mul_le_mul_right _ hE3
  have h4 : Fintype.card P * f ≤ (3 * f + 1) * f := Nat.mul_le_mul_right _ hn
  nlinarith

/-- **Robustness of the common core**: every vertex `u` of round `(w,4)` with at least `2f + 1`
strong edges — whoever creates it, and whenever — has a strong path to the round-`(w,1)` vertex
of every member of the core. -/
theorem sPath_of_mem_core {f : ℕ} (hn : Fintype.card P ≤ 3 * f + 1) (C : Content P B) (w : ℕ)
    (E3 : Finset P) {u : Vtx P} (hu : u.1 = wround w 4) (hu2 : 2 * f + 1 ≤ (C.strong u).card)
    {s : P} (hs : s ∈ core f C w E3) : SPath C u (wround w 1, s) := by
  have hs' : f + 1 ≤ (E3.filter (fun k => SPath C (wround w 3, k) (wround w 1, s))).card := by
    simpa [core] using hs
  obtain ⟨k, hk⟩ := inter_nonempty_of_card_lt_card_add_card (subset_univ (C.strong u))
    (subset_univ (E3.filter (fun k => SPath C (wround w 3, k) (wround w 1, s))))
    (by rw [card_univ]; omega)
  rw [mem_inter, mem_filter] at hk
  obtain ⟨hku, -, hkp⟩ := hk
  refine SPath.trans ?_ hkp
  have hu' : u = (wround w 3 + 1, u.2) := Prod.ext hu rfl
  rw [hu'] at hku ⊢
  exact (sPath_succ_iff (by unfold wround; omega) _ _).2 hku

/-- **The commit rule is met when the coin lands in the core**: in every closed, valid local DAG
with at least `2f + 1` vertices of round `(w,4)`, if `coin w ∈ core f C w E3` (for any `E3`), then
the leader of wave `w` is present and at least `2f + 1` round-`(w,4)` vertices strongly reach it
(the condition of line 36 of Algorithm 3). -/
theorem commit_of_mem_core {f : ℕ} (hn : Fintype.card P ≤ 3 * f + 1) (C : Content P B)
    (coin : ℕ → P) {D : Finset (Vtx P)} (hD : Closed C D) (hV : Valid f C D) (w : ℕ)
    (h4 : 2 * f + 1 ≤ (layer D (wround w 4)).card) (E3 : Finset P)
    (hcoin : coin w ∈ core f C w E3) :
    leader coin D w = some (wround w 1, coin w) ∧
      2 * f + 1 ≤ commitCount C D (wround w 1, coin w) w := by
  have hreach : ∀ u ∈ layer D (wround w 4), SPath C u (wround w 1, coin w) := by
    intro u hu
    rw [layer, mem_filter] at hu
    exact sPath_of_mem_core hn C w E3 hu.2 (hV u hu.1) hcoin
  obtain ⟨u, hu⟩ : (layer D (wround w 4)).Nonempty := card_pos.1 (by omega)
  have hmem : (wround w 1, coin w) ∈ D :=
    hD.mem_of_sPath (mem_filter.1 hu).1 (hreach u hu)
  refine ⟨by simp [leader, hmem], h4.trans (card_le_card ?_)⟩
  intro x hx
  have hx' := hx
  rw [layer, mem_filter] at hx'
  exact mem_filter.2 ⟨hx'.1, hx'.2, hreach x hx⟩

/-- The core only depends on the strong past of the round-`(w,3)` vertices with sources in `E3`:
it is determined as soon as these vertices exist (in particular, before the coin of wave `w` is
revealed, which requires `2f + 1` vertices of round `(w,4)`). -/
theorem core_congr (f : ℕ) {C C' : Content P B} (w : ℕ) (E3 : Finset P)
    (h : ∀ k ∈ E3, ∀ v, SPath C (wround w 3, k) v → C.strong v = C'.strong v) :
    core f C w E3 = core f C' w E3 := by
  unfold core
  refine filter_congr (fun s _ => ?_)
  rw [filter_congr (fun k hk => sPath_congr (h k hk) (wround w 1, s))]

/-- **Lemma 2 of the paper.** Let `D` be a closed, valid local DAG with at least `2f + 1` vertices
of round `(w,4)` (the process has completed wave `w`), and `n ≤ 3f + 1`. Then there are
`V ⊆ D[round(w,1)]` and `U ⊆ D[round(w,4)]` with `|V| ≥ 2f + 1`, `|U| ≥ 2f + 1`, and a strong
path from every `u ∈ U` to every `v ∈ V`. (`V` is the image of the core, `U` the whole layer.) -/
theorem lemma2 {f : ℕ} (hn : Fintype.card P ≤ 3 * f + 1) (C : Content P B)
    {D : Finset (Vtx P)} (hD : Closed C D) (hV : Valid f C D) (w : ℕ)
    (h4 : 2 * f + 1 ≤ (layer D (wround w 4)).card) :
    ∃ V ⊆ layer D (wround w 1), 2 * f + 1 ≤ V.card ∧
      ∃ U ⊆ layer D (wround w 4), 2 * f + 1 ≤ U.card ∧ ∀ v ∈ V, ∀ u ∈ U, SPath C u v := by
  set E3 := (layer D (wround w 3)).image Prod.snd with hE3def
  have hr3 : ∀ k, (wround w 3, k) ∈ D ↔ k ∈ E3 := by
    intro k
    simp only [hE3def, mem_image, layer, mem_filter]
    constructor
    · intro hk; exact ⟨_, ⟨hk, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hx3⟩, rfl⟩
      have : x = (wround w 3, x.2) := Prod.ext hx3 rfl
      rwa [← this]
  obtain ⟨u0, hu0⟩ : (layer D (wround w 4)).Nonempty := card_pos.1 (by omega)
  rw [layer, mem_filter] at hu0
  -- the strong edges of `u0` land in round `(w,3)` of `D`
  have hE3 : 2 * f + 1 ≤ E3.card := by
    refine (hV u0 hu0.1).trans (card_le_card (fun k hk => (hr3 k).1 ?_))
    refine hD _ hu0.1 _ (SEdge.edge ⟨by rw [hu0.2]; rfl, hk, by unfold wround; omega⟩)
  have h3 : ∀ k ∈ E3, 2 * f + 1 ≤ (C.strong (wround w 3, k)).card :=
    fun k hk => hV _ ((hr3 k).2 hk)
  have h2 : ∀ k ∈ E3, ∀ j ∈ C.strong (wround w 3, k),
      2 * f + 1 ≤ (C.strong (wround w 2, j)).card := by
    intro k hk j hj
    refine hV _ (hD _ ((hr3 k).2 hk) _ (SEdge.edge ⟨rfl, hj, by unfold wround; omega⟩))
  have hcore := core_card hn C w hE3 h3 h2
  refine ⟨(core f C w E3).image (fun s => (wround w 1, s)), ?_, ?_,
    layer D (wround w 4), subset_refl _, h4, ?_⟩
  · intro v hv
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hv
    rw [layer, mem_filter]
    exact ⟨hD.mem_of_sPath hu0.1 (sPath_of_mem_core hn C w E3 hu0.2 (hV u0 hu0.1) hs), rfl⟩
  · rwa [card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]
  · intro v hv u hu
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hv
    rw [layer, mem_filter] at hu
    exact sPath_of_mem_core hn C w E3 hu.2 (hV u hu.1) hs

end DagRider
