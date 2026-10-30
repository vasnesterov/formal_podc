import Papers.PODC2016.BoundedGenusMDS.Lemma12

/-!
# Counterexamples to Lemma 7, Corollary 8 and Lemma 11 (as stated)

All graphs here have a vertex cover `{p, q}` of size two, so every depth-1 minor `H` satisfies
`|E(H)| ≤ 2|V(H)|` and no depth-1 minor is `K_{3,3}` (`SimpleGraph.depth1_of_cover_two`). Both
graphs are planar, so they satisfy Assumption 6 with `c = 2`, `t = 3`.

* `G7 K` (Lemma 7.2, Corollary 8): `m_i – c' – u_k – m_j` for `k < K`, i.e. `K_{2,K}` on
  `{c', m_j} × {u_k}` plus the pendant edge `m_i c'`. `M = {m_i, m_j}` is a minimum dominating set,
  `D = ∅`, `N_{E'}(m_i) = {c'}`, `N_{E'}(m_j) = {u_k}`, and every `u_k` has the neighbour `c'` in the
  other star: `K` vertices of `N_j` see `N_i` (Lemma 7.2 claims `≤ 2ct = 12`), and `|Y| ≥ K`
  (Corollary 8 claims `≤ 6c²t|M| = 144`). With the ordering `m_j, m_i` the same graph violates
  Lemma 7.3 (`≤ 4ct = 24`) for `K = 25`.
* `G11 K` (Lemma 11): the book `K_{1,1,K}` on `m, x, u_k`. `M = {m}`, `D = ∅`, `C_m = {x}`,
  `dom ≡ x` is a valid dominator choice (ties between `m` and `x`), `Y = Z = ∅`, and all `K + 1`
  leaves of `m` have their dominator inside the star outside `Y ∪ Z` (Lemma 11 claims
  `≤ (2(t-1)+4)c|M| = 16`).
-/

open Finset

namespace Podc.BoundedGenusMDS

open SimpleGraph (Depth1Model IsDepth1Minor Depth1DensityLE ExcludesKt3 depth1_of_cover_two)

open Classical


/-! ### The graph `G7 K` (Lemma 7.2 and Corollary 8) -/

/-- Vertices of `G7 K`: `m_i`, `c'`, `m_j` and `u_k` (`k < K`). -/
inductive V7 (K : ℕ) where
  | mi | cp | mj | u (k : Fin K)
  deriving Fintype

/-- Edges of `G7 K`: `m_i c'`, `c' u_k`, `m_j u_k`. -/
def r7 {K : ℕ} : V7 K → V7 K → Prop
  | .mi, .cp => True
  | .cp, .u _ => True
  | .mj, .u _ => True
  | _, _ => False

/-- `G7 K = K_{2,K}` (sides `{c', m_j}`, `{u_k}`) plus the pendant edge `m_i c'`. -/
def G7 (K : ℕ) : SimpleGraph (V7 K) := SimpleGraph.fromRel r7

lemma G7_adj {K : ℕ} {x y : V7 K} : (G7 K).Adj x y ↔ x ≠ y ∧ (r7 x y ∨ r7 y x) := Iff.rfl

section G7

variable {K : ℕ}

@[simp] lemma G7_mi_cp : (G7 K).Adj .mi .cp := by simp [G7_adj, r7]
@[simp] lemma G7_cp_u (k : Fin K) : (G7 K).Adj .cp (.u k) := by simp [G7_adj, r7]
@[simp] lemma G7_mj_u (k : Fin K) : (G7 K).Adj .mj (.u k) := by simp [G7_adj, r7]

lemma G7_cover : ∀ x y : V7 K, (G7 K).Adj x y → x = .cp ∨ x = .mj ∨ y = .cp ∨ y = .mj := by
  intro x y h
  rw [G7_adj] at h
  rcases x with _ | _ | _ | k <;> rcases y with _ | _ | _ | k' <;> simp_all [r7]

lemma G7_phase1 : phase1 (G7 K) 2 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  rw [mem_phase1] at hv
  apply hv
  rcases v with _ | _ | _ | k
  · refine ⟨{.cp}, by simp, by simp, fun x hx => ?_⟩
    rw [mem_nbhd, G7_adj] at hx
    rw [mem_cnbhd]
    rcases x with _ | _ | _ | k <;> simp_all [r7]
  · refine ⟨{.mi, .mj}, by simp, by simp [card_insert_of_notMem], fun x hx => ?_⟩
    rw [mem_nbhd, G7_adj] at hx
    rw [mem_cnbhd]
    rcases x with _ | _ | _ | k <;> simp_all [r7]
  · refine ⟨{.cp}, by simp, by simp, fun x hx => ?_⟩
    rw [mem_nbhd, G7_adj] at hx
    rw [mem_cnbhd]
    rcases x with _ | _ | _ | k <;> simp_all [r7]
  · refine ⟨{.cp, .mj}, by simp, by simp [card_insert_of_notMem], fun x hx => ?_⟩
    rw [mem_nbhd, G7_adj] at hx
    rw [mem_cnbhd]
    rcases x with _ | _ | _ | k <;> simp_all [r7]

/-- `M = {m_i, m_j}` dominates `G7 K`. -/
lemma G7_dom : (G7 K).IsDominatingSet (({.mi, .mj} : Finset (V7 K)) : Set (V7 K)) := by
  intro v
  rcases v with _ | _ | _ | k
  · left; simp
  · right; exact ⟨.mi, by simp, (G7_mi_cp).symm⟩
  · left; simp
  · right; exact ⟨.mj, by simp, (G7_mj_u k).symm⟩

/-- `M = {m_i, m_j}` is a minimum dominating set of `G7 K`. -/
lemma G7_min (M' : Finset (V7 K)) (hM' : (G7 K).IsDominatingSet (M' : Set (V7 K))) :
    ({.mi, .mj} : Finset (V7 K)).card ≤ M'.card := by
  rw [card_insert_of_notMem (by simp), card_singleton]
  -- `m_i` is dominated by `m_i` or `c'`, `m_j` by `m_j` or some `u_k`
  have h1 : ∃ a ∈ M', a = .mi ∨ a = .cp := by
    rcases hM' .mi with h | ⟨a, ha, h⟩
    · exact ⟨_, h, Or.inl rfl⟩
    · refine ⟨a, ha, ?_⟩; rw [G7_adj] at h; rcases a with _ | _ | _ | k <;> simp_all [r7]
  have h2 : ∃ b ∈ M', b = .mj ∨ ∃ k, b = .u k := by
    rcases hM' .mj with h | ⟨b, hb, h⟩
    · exact ⟨_, h, Or.inl rfl⟩
    · refine ⟨b, hb, ?_⟩; rw [G7_adj] at h; rcases b with _ | _ | _ | k <;> simp_all [r7]
  obtain ⟨a, ha, ha'⟩ := h1
  obtain ⟨b, hb, hb'⟩ := h2
  have hab : a ≠ b := by
    rintro rfl; rcases ha' with rfl | rfl <;> rcases hb' with h | ⟨k, h⟩ <;> cases h
  exact one_lt_card.2 ⟨a, ha, b, hb, hab⟩

/-- The `Setup` of Section 3 for `G7 K`: ordering `m_i, m_j`, `C_{m_i} = C_{m_j} = {c'}`. -/
noncomputable def S7 (K : ℕ) : Setup (G7 K) 2 where
  M := {.mi, .mj}
  hM := G7_dom
  ord := fun v => if v = .mi then 0 else 1
  ord_inj := by intro m hm m' hm' h; simp at hm hm'; rcases hm with rfl | rfl <;>
    rcases hm' with rfl | rfl <;> simp_all
  ord_D := by intro m _ _ _ h; simp [G7_phase1] at h
  Cm := fun _ => {.cp}
  Cm_spec := by
    intro m hm _
    simp only [mem_insert, mem_singleton] at hm
    refine ⟨by rcases hm with rfl | rfl <;> simp, by simp, fun x hx => ?_⟩
    rw [mem_nbhd, G7_adj] at hx
    rw [mem_cnbhd]
    rcases hm with rfl | rfl <;> rcases x with _ | _ | _ | k <;> simp_all [r7]

lemma star7_u (S : Setup (G7 K) 2) (hS : S.M = {.mi, .mj}) (k : Fin K) :
    S.star (.u k) = .mj := by
  have hM : V7.u k ∉ S.M := by simp [hS]
  have h1 := S.star_mem hM
  have h2 := S.adj_star hM
  rw [hS] at h1
  simp only [mem_insert, mem_singleton] at h1
  rcases h1 with h | h
  · rw [h, G7_adj] at h2; simp [r7] at h2
  · exact h

lemma star7_cp (S : Setup (G7 K) 2) (hS : S.M = {.mi, .mj}) : S.star .cp = .mi := by
  have hM : V7.cp ∉ S.M := by simp [hS]
  have h1 := S.star_mem hM
  have h2 := S.adj_star hM
  rw [hS] at h1
  simp only [mem_insert, mem_singleton] at h1
  rcases h1 with h | h
  · exact h
  · rw [h, G7_adj] at h2; simp [r7] at h2

lemma S7_star_u (k : Fin K) : (S7 K).star (.u k) = .mj := star7_u _ rfl k

lemma S7_star_cp : (S7 K).star .cp = .mi := star7_cp _ rfl

/-- The same graph with the opposite ordering `m_j, m_i`. -/
noncomputable def S7' (K : ℕ) : Setup (G7 K) 2 :=
  { S7 K with
    ord := fun v => if v = .mj then 0 else 1
    ord_inj := by
      intro m hm m' hm' h
      simp only [S7, mem_insert, mem_singleton] at hm hm'
      rcases hm with rfl | rfl <;> rcases hm' with rfl | rfl <;> simp_all
    ord_D := by intro m _ _ _ h; simp [G7_phase1] at h }

lemma card_image_u : ((univ : Finset (Fin K)).image (V7.u : Fin K → V7 K)).card = K := by
  rw [card_image_of_injective _ (fun a b h => by cases h; rfl), card_univ, Fintype.card_fin]

end G7

/-- **Lemma 7, item 2, is false.** For `G7 13` (planar; all depth-1 minors have density `≤ 2`;
no `K_{3,3}` depth-1 minor; `M = {m_i, m_j}` a minimum dominating set; `m_i, m_j ∉ D`;
`ord m_i < ord m_j`), all `13` leaves of `m_j` have a neighbour among the leaves of `m_i`,
while the lemma claims at most `2ct = 12`. -/
theorem lemma_7_2_false :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (S : Setup G 2) (mi mj : V),
      Depth1DensityLE G 2 ∧ ExcludesKt3 G 3 ∧
      (∀ M' : Finset V, G.IsDominatingSet (M' : Set V) → S.M.card ≤ M'.card) ∧
      mi ∈ S.M ∧ mj ∈ S.M ∧ S.ord mi < S.ord mj ∧ mi ∉ S.D ∧ mj ∉ S.D ∧
      2 * 2 * 3 < ((S.leaves mj).filter fun u => ∃ v ∈ S.leaves mi, G.Adj u v).card := by
  refine ⟨V7 13, inferInstance, G7 13, S7 13, .mi, .mj, (depth1_of_cover_two G7_cover).1,
    (depth1_of_cover_two G7_cover).2, G7_min, by simp [S7], by simp [S7], by simp [S7],
    by simp [Setup.D, G7_phase1], by simp [Setup.D, G7_phase1], ?_⟩
  refine lt_of_lt_of_le (b := ((univ : Finset (Fin 13)).image V7.u).card)
    (by rw [card_image_u]; norm_num) (card_le_card fun x hx => ?_)
  obtain ⟨k, -, rfl⟩ := mem_image.1 hx
  simp only [mem_filter, Setup.mem_leaves, S7_star_u]
  refine ⟨by simp [S7], .cp, ⟨by simp [S7], S7_star_cp⟩, (G7_cp_u k).symm⟩

/-- **Lemma 7, item 3, is false.** For `G7 25` with the ordering `m_j, m_i` (so the paper's
`m_i` is our `m_j`), all `25` leaves of the first star have a neighbour among the leaves of the
second star, while the lemma claims at most `4ct = 24`. -/
theorem lemma_7_3_false :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (S : Setup G 2) (a b : V),
      Depth1DensityLE G 2 ∧ ExcludesKt3 G 3 ∧
      (∀ M' : Finset V, G.IsDominatingSet (M' : Set V) → S.M.card ≤ M'.card) ∧
      a ∈ S.M ∧ b ∈ S.M ∧ S.ord a < S.ord b ∧ a ∉ S.D ∧ b ∉ S.D ∧
      4 * 2 * 3 < ((S.leaves a).filter fun u => ∃ v ∈ S.leaves b, G.Adj u v).card := by
  refine ⟨V7 25, inferInstance, G7 25, S7' 25, .mj, .mi, (depth1_of_cover_two G7_cover).1,
    (depth1_of_cover_two G7_cover).2, G7_min, by simp [S7', S7], by simp [S7', S7],
    by simp [S7'], by simp [Setup.D, G7_phase1], by simp [Setup.D, G7_phase1], ?_⟩
  refine lt_of_lt_of_le (b := ((univ : Finset (Fin 25)).image V7.u).card)
    (by rw [card_image_u]; norm_num) (card_le_card fun x hx => ?_)
  obtain ⟨k, -, rfl⟩ := mem_image.1 hx
  simp only [mem_filter, Setup.mem_leaves, star7_u (S7' 25) rfl]
  exact ⟨⟨by simp [S7', S7], trivial⟩, .cp, ⟨by simp [S7', S7], star7_cp (S7' 25) rfl⟩,
    (G7_cp_u k).symm⟩

/-- **Corollary 8 is false.** For `G7 145` (same hypotheses as in `lemma_7_2_false`), the paper's
set `Y` contains all `145` vertices `u_k`, while the corollary claims `|Y| ≤ 6c²t|M| = 144`. -/
theorem corollary_8_false :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (S : Setup G 2),
      Depth1DensityLE G 2 ∧ ExcludesKt3 G 3 ∧
      (∀ M' : Finset V, G.IsDominatingSet (M' : Set V) → S.M.card ≤ M'.card) ∧
      6 * 2 ^ 2 * 3 * S.M.card < S.Ypaper.card := by
  refine ⟨V7 145, inferInstance, G7 145, S7 145, (depth1_of_cover_two G7_cover).1,
    (depth1_of_cover_two G7_cover).2, G7_min, ?_⟩
  have hM : (S7 145).M.card = 2 := by simp [S7]
  rw [hM]
  refine lt_of_lt_of_le (b := ((univ : Finset (Fin 145)).image V7.u).card)
    (by rw [card_image_u]; norm_num) (card_le_card fun x hx => ?_)
  obtain ⟨k, -, rfl⟩ := mem_image.1 hx
  simp only [Setup.Ypaper, mem_filter, mem_univ, true_and, S7_star_u]
  refine ⟨by simp [S7], by simp [Setup.D, G7_phase1], .cp, by simp [S7], ?_, (G7_cp_u k).symm⟩
  rw [S7_star_cp]; simp

/-! ### The book graph `G11 K` (Lemma 11) -/

/-- Vertices of the book `K_{1,1,K}`: the spine `m x` and the pages `u_k`. -/
inductive V11 (K : ℕ) where
  | m | x | u (k : Fin K)
  deriving Fintype

/-- Edges of the book: `m x`, `m u_k`, `x u_k`. -/
def r11 {K : ℕ} : V11 K → V11 K → Prop
  | .m, .x => True
  | .m, .u _ => True
  | .x, .u _ => True
  | _, _ => False

/-- The book graph `K_{1,1,K}`. -/
def G11 (K : ℕ) : SimpleGraph (V11 K) := SimpleGraph.fromRel r11

lemma G11_adj {K : ℕ} {a b : V11 K} : (G11 K).Adj a b ↔ a ≠ b ∧ (r11 a b ∨ r11 b a) := Iff.rfl

section G11

variable {K : ℕ}

lemma G11_cover : ∀ a b : V11 K, (G11 K).Adj a b → a = .m ∨ a = .x ∨ b = .m ∨ b = .x := by
  intro a b h
  rw [G11_adj] at h
  rcases a with _ | _ | k <;> rcases b with _ | _ | k' <;> simp_all [r11]

lemma G11_cnbhd_m : cnbhd (G11 K) {.m} = univ := by
  ext a; simp only [mem_cnbhd_singleton, mem_univ, iff_true, G11_adj]
  rcases a with _ | _ | k <;> simp [r11]

lemma G11_cnbhd_x : cnbhd (G11 K) {.x} = univ := by
  ext a; simp only [mem_cnbhd_singleton, mem_univ, iff_true, G11_adj]
  rcases a with _ | _ | k <;> simp [r11]

lemma G11_phase1 : phase1 (G11 K) 2 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  rw [mem_phase1] at hv
  apply hv
  rcases v with _ | _ | k
  · refine ⟨{.x}, by simp, by simp, fun a _ => ?_⟩
    rw [G11_cnbhd_x]; exact mem_univ _
  · refine ⟨{.m}, by simp, by simp, fun a _ => ?_⟩
    rw [G11_cnbhd_m]; exact mem_univ _
  · refine ⟨{.m}, by simp, by simp, fun a _ => ?_⟩
    rw [G11_cnbhd_m]; exact mem_univ _

/-- The `Setup` for the book: `M = {m}`, `C_m = {x}`. -/
noncomputable def S11 (K : ℕ) : Setup (G11 K) 2 where
  M := {.m}
  hM := by
    intro a
    rcases a with _ | _ | k
    · left; simp
    · right; exact ⟨.m, by simp, by simp [G11_adj, r11]⟩
    · right; exact ⟨.m, by simp, by simp [G11_adj, r11]⟩
  ord := fun _ => 0
  ord_inj := by intro a ha b hb _; simp at ha hb; rw [ha, hb]
  ord_D := by intro a _ _ _ h; simp [G11_phase1] at h
  Cm := fun _ => {.x}
  Cm_spec := by
    intro a ha _
    simp only [mem_singleton] at ha; subst ha
    refine ⟨by simp, by simp, fun b _ => ?_⟩
    rw [G11_cnbhd_x]; exact mem_univ _

lemma S11_star {a : V11 K} (ha : a ∉ (S11 K).M) : (S11 K).star a = .m := by
  have := (S11 K).star_mem ha
  simpa [S11] using this

/-- `dom ≡ x` is a valid choice of dominators (it ties with `m` for maximal residual degree). -/
lemma S11_isDominator : IsDominator (G11 K) (S11 K).D (fun _ => .x) := by
  intro v _
  refine ⟨?_, fun w _ => ?_⟩
  · rw [mem_cnbhd_singleton]
    rcases v with _ | _ | k
    · right; simp [G11_adj, r11]
    · left; rfl
    · right; simp [G11_adj, r11]
  · simp only [resDeg, G11_cnbhd_x]
    exact card_le_card fun y hy => mem_sdiff.2 ⟨mem_univ _, (mem_sdiff.1 hy).2⟩

end G11

/-- **Lemma 11 is false.** For the book `G11 17` (planar; all depth-1 minors have density `≤ 2`;
no `K_{3,3}` depth-1 minor; `M = {m}` a minimum dominating set; `D = ∅`; `C_m = {x}`; the valid
dominator choice `dom ≡ x`), all `18` leaves of `m` choose a dominator in their own star outside
`Y ∪ Z`, while the lemma claims at most `(2(t-1)+4)c|M| = 16` such vertices. -/
theorem lemma_11_false :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (S : Setup G 2) (dom : V → V),
      Depth1DensityLE G 2 ∧ ExcludesKt3 G 3 ∧
      (∀ M' : Finset V, G.IsDominatingSet (M' : Set V) → S.M.card ≤ M'.card) ∧
      IsDominator G S.D dom ∧
      (2 * (3 - 1) + 4) * 2 * S.M.card < ((S.M \ S.D).biUnion fun m => (S.leaves m).filter
        fun u => u ∈ S.R ∧ dom u ∈ S.leaves m \ (S.Ypaper ∪ S.Z)).card := by
  refine ⟨V11 17, inferInstance, G11 17, S11 17, fun _ => .x, (depth1_of_cover_two G11_cover).1,
    (depth1_of_cover_two G11_cover).2, ?_, S11_isDominator, ?_⟩
  · intro M' hM'
    rcases M'.eq_empty_or_nonempty with rfl | hne
    · rcases hM' .m with h | ⟨a, ha, -⟩ <;> simp at *
    · simpa [S11] using hne.card_pos
  · have hM : (S11 17).M.card = 1 := by simp [S11]
    rw [hM]
    have hcard : ((univ : Finset (Fin 17)).image (V11.u (K := 17))).card = 17 := by
      rw [card_image_of_injective _ (fun a b h => by cases h; rfl), card_univ, Fintype.card_fin]
    refine lt_of_lt_of_le (b := ((univ : Finset (Fin 17)).image (V11.u (K := 17))).card)
      (by rw [hcard]; norm_num) (card_le_card fun a ha => ?_)
    · obtain ⟨k, -, rfl⟩ := mem_image.1 ha
      have hxM : V11.x ∉ (S11 17).M := by simp [S11]
      refine mem_biUnion.2 ⟨.m, by simp [S11, Setup.D, G11_phase1], ?_⟩
      simp only [mem_filter, Setup.mem_leaves, Setup.R, mem_sdiff, mem_univ, true_and,
        mem_union, not_or]
      refine ⟨⟨by simp [S11], S11_star (by simp [S11])⟩, by simp [Setup.D, G11_phase1, cnbhd],
        ⟨hxM, S11_star hxM⟩, ?_, ?_⟩
      · simp only [Setup.Ypaper, mem_filter, mem_univ, true_and, not_and, not_exists]
        intro _ _ v hv hne _
        exact hne (by rw [S11_star hv, S11_star hxM])
      · simp only [Setup.Z, mem_filter, mem_univ, true_and, not_and, not_lt]
        intro _ _
        calc (nbhd (G11 17) .x ∩ ((S11 17).M ∪ (S11 17).C)).card
            ≤ ((S11 17).M ∪ (S11 17).C).card := card_le_card inter_subset_right
          _ ≤ (S11 17).M.card + (S11 17).C.card := card_union_le _ _
          _ ≤ 1 + 1 := by
              refine Nat.add_le_add (by simp [S11]) ?_
              simp only [Setup.C, S11]
              refine card_biUnion_le.trans ?_
              have h1 : ({V11.m} : Finset (V11 17)).card = 1 := card_singleton _
              have h2 : (({V11.m} : Finset (V11 17)) \ phase1 (G11 17) 2).card ≤ 1 :=
                (card_le_card sdiff_subset).trans h1.le
              simpa using h2
          _ ≤ 4 * 2 := by norm_num

end Podc.BoundedGenusMDS
