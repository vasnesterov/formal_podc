import Papers.PODC2026.LCLDefinitions.Theorem51

/-!
# Theorem 5.1 as stated is false

Theorem 5.1 of *It does not matter how you define locally checkable labelings* (Cruciani, Das,
Raevskaya, Suomela; PODC 2026) assumes edge-consistency only for pairs `v, v'` with
`v' ∈ gball_r(v)`, but concludes injectivity on `gball_r(v)`, whose gadgeted diameter is `2r`.
Two vertices of `gball_r(v)` that are at gadgeted distance `> r` from each other are never compared
by the hypothesis, so they may share a colour.

Counterexample: the base graph `K_{3,3}` (sides `{0,1,2}` and `{3,4,5}`) with the injective edge
colouring `x(i, 3 + j) = 3 i + j + 1` (a distance-`k` edge colouring for every `k`), `r = 1`, and the
colouring `χ` that is injective except that the original vertices `0` and `1` get the same colour.
Both lie in the `1`-gball of the original vertex `3`, but their gadgeted distance is `2`.
-/

namespace Podc.LCLDefinitions

open SimpleGraph

/-- `K_{3,3}`: vertices `0, 1, 2` and `3, 4, 5`; the edge `(i, j)` joins `i` and `3 + j` and is
expanded into `3 i + j + 1` A-gadgets. -/
abbrev K33 : Base where
  V := Fin 6
  E := Fin 3 × Fin 3
  src e := ⟨e.1.val, by omega⟩
  tgt e := ⟨3 + e.2.val, by omega⟩
  len e := 3 * e.1.val + e.2.val + 1

namespace K33

lemma isSimple : K33.IsSimple := by
  refine ⟨fun e h => ?_, fun e e' h => ?_⟩
  · have := congrArg Fin.val h; simp [K33] at this; omega
  · rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have a := congrArg Fin.val h1; have b := congrArg Fin.val h2
      simp [K33] at a b
      exact Prod.ext (Fin.ext a) (Fin.ext b)
    · have a := congrArg Fin.val h1; simp [K33] at a; omega

lemma isCubic : K33.IsCubic := by
  intro v
  rw [Set.ncard_eq_toFinset_card']
  revert v
  decide

lemma len_inj : Function.Injective K33.len := by
  intro e e' h
  simp only [K33] at h
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

/-- The colouring is a distance-`k` edge colouring for every `k` (it is injective). -/
lemma isDistEdgeColoring (k : ℕ) : K33.IsDistEdgeColoring k :=
  fun _ _ hne _ h => hne (len_inj h)

lemma len_pos (e : K33.E) : 0 < K33.len e := by simp [K33]

lemma not_adj_01 : ¬ K33.G0.Adj (0 : Fin 6) (1 : Fin 6) := by
  rintro ⟨-, e, ⟨-, h⟩ | ⟨-, h⟩⟩ <;> have := congrArg Fin.val h <;> simp [K33] at this <;> omega

end K33

namespace Base

variable {B : Base}

/-- Two distinct original vertices are never adjacent and have no common neighbour. -/
lemma orig_far {o o' : B.V} (hne : o ≠ o') (c : B.Vert)
    (h : (c = .orig o ∨ B.graph.Adj (.orig o) c)) (h' : c = .orig o' ∨ B.graph.Adj (.orig o') c) :
    False := by
  rcases h with rfl | h <;> rcases h' with h' | h'
  · exact hne (by injection h')
  · exact h'
  · rw [h'] at h; exact h
  · cases c with
    | orig _ => exact h
    | gad e k =>
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact hne (h1.trans h1'.symm)
      · have := len_pos_of k; omega
      · have := len_pos_of k; omega
      · exact hne (h1.trans h1'.symm)
where
  len_pos_of {e : B.E} (k : Fin (6 * B.len e)) : 0 < 6 * B.len e := Nat.lt_of_le_of_lt (Nat.zero_le _) k.isLt

open Classical in
/-- The colouring that identifies the colours of two original vertices `o₁, o₂` and is injective
otherwise. -/
noncomputable def merge (o1 o2 : B.V) (x : B.Vert) : B.Vert := if x = .orig o2 then .orig o1 else x

lemma merge_eq {o1 o2 : B.V} (hne : o1 ≠ o2) {x y : B.Vert} (h : merge o1 o2 x = merge o1 o2 y)
    (hxy : x ≠ y) : (x = .orig o1 ∧ y = .orig o2) ∨ (x = .orig o2 ∧ y = .orig o1) := by
  unfold merge at h
  split_ifs at h with h1 h2 h2
  · exact absurd (h1.trans h2.symm) hxy
  · exact Or.inr ⟨h1, h.symm⟩
  · exact Or.inl ⟨h, h2⟩
  · exact absurd h hxy

/-- Merging the colours of two distinct original vertices gives a distance-2 colouring. -/
lemma merge_dist2 {o1 o2 : B.V} (hne : o1 ≠ o2) : B.IsDist2Coloring (merge o1 o2) := by
  intro c a b ha hb hab h
  rcases merge_eq hne h hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact orig_far hne c (ha.imp Eq.symm Adj.symm) (hb.imp Eq.symm Adj.symm)
  · exact orig_far hne c (hb.imp Eq.symm Adj.symm) (ha.imp Eq.symm Adj.symm)

/-- If the two merged original vertices are at base distance `> r`, the merged colouring satisfies
condition 2 of Theorem 5.1 *as stated* (edge-consistency inside `r`-gballs). -/
lemma merge_consistentIn {o1 o2 : B.V} (hne : o1 ≠ o2) {r : ℕ} (hfar : (r : ℕ∞) < B.G0.edist o1 o2) :
    B.IsEdgeConsistentIn r (merge o1 o2) := by
  intro v u hvu v' hv' h
  by_cases hv : v' = v
  · subst hv; exact ⟨u, hvu, rfl⟩
  · exfalso
    rcases merge_eq hne h hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have := mem_gball_orig hv'
      rw [SimpleGraph.edist_comm] at this
      exact absurd hfar (not_lt.2 this)
    · exact absurd hfar (not_lt.2 (mem_gball_orig hv'))

open Classical in
/-- The colouring that gives `y` the colour of `x` and is injective otherwise. -/
noncomputable def mergeV (x y : B.Vert) (z : B.Vert) : B.Vert := if z = y then x else z

lemma mergeV_eq {x y : B.Vert} (hne : x ≠ y) {a b : B.Vert} (h : mergeV x y a = mergeV x y b)
    (hab : a ≠ b) : (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  unfold mergeV at h
  split_ifs at h with h1 h2 h2
  · exact absurd (h1.trans h2.symm) hab
  · exact Or.inr ⟨h1, h.symm⟩
  · exact Or.inl ⟨h, h2⟩
  · exact absurd h hab

lemma mergeV_dist2 {x y : B.Vert} (hne : x ≠ y)
    (hfar : ∀ c, (x = c ∨ B.graph.Adj c x) → (y = c ∨ B.graph.Adj c y) → False) :
    B.IsDist2Coloring (mergeV x y) := by
  intro c a b ha hb hab h
  rcases mergeV_eq hne h hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hfar c ha hb
  · exact hfar c hb ha

lemma mergeV_consistentIn {x y : B.Vert} (hne : x ≠ y) {r : ℕ} (h1 : y ∉ B.gball r x)
    (h2 : x ∉ B.gball r y) : B.IsEdgeConsistentIn r (mergeV x y) := by
  intro v u hvu v' hv' h
  by_cases hv : v' = v
  · subst hv; exact ⟨u, hvu, rfl⟩
  · exfalso
    rcases mergeV_eq hne h hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h2 hv'
    · exact h1 hv'

end Base

open Base

/-- Lemma 5.13 of the paper, as a statement about a colouring `χ` (under the hypotheses of
Theorem 5.1): the colour of an outer vertex `v` next to an original vertex `w` is unique in
`gball_r(w)`. -/
def Lemma513 (B : Base) (r : ℕ) (χ : B.Vert → B.Vert) : Prop :=
  ∀ w : B.V, ∀ v, B.graph.Adj (.orig w) v → ∀ v' ∈ B.gball r (.orig w), v' ≠ v → χ v' ≠ χ v

/-- **Lemma 5.13 as stated is false.** In the gadgeted `K_{3,3}` with `r = 1`, give the original
vertex `1` the colour of the outer vertex `v` of the expanded edge `{0, 3}` next to `3`. This is a
distance-2 colouring that is edge-consistent in every `1`-gball, but `1 ∈ gball_1(3)`. -/
theorem lemma_5_13_false :
    ∃ χ : K33.Vert → K33.Vert, K33.IsDist2Coloring χ ∧ K33.IsEdgeConsistentIn 1 χ ∧
      ¬ Lemma513 K33 1 χ := by
  set d : K33.Dir := ((0, 0), false)
  set v : K33.Vert := pos d 0
  set y : K33.Vert := .orig (1 : Fin 6)
  have hd0 : 0 < 6 * K33.len d.1 := by simp [d, K33]
  have hstart : start d = (3 : Fin 6) := by simp [d, start, K33]
  have hvy : v ≠ y := pos_ne_orig d hd0 _
  -- `gd2 1 v ≥ 3`
  have hfar : ¬ K33.gd2 y v ≤ 2 := by
    intro h
    have h1 := le_gd2 (pot (1 : Fin 6)) (pot_lip _) y v
    rw [show pot (B := K33) (1 : Fin 6) y = 0 from pot_self _, zero_add] at h1
    obtain ⟨m, hm⟩ := pos_eq_gad d hd0
    have h3 : (3 : ℕ∞) ≤ pot (B := K33) (1 : Fin 6) v := by
      rw [show v = pos d 0 from rfl, hm]
      simp only [pot]
      have a : (1 : ℕ∞) ≤ K33.G0.edist (1 : Fin 6) (K33.src d.1) :=
        Order.one_le_iff_ne_zero.2 (by rw [Ne, edist_eq_zero_iff]; simp [d, K33])
      have b : (1 : ℕ∞) ≤ K33.G0.edist (1 : Fin 6) (K33.tgt d.1) :=
        Order.one_le_iff_ne_zero.2 (by rw [Ne, edist_eq_zero_iff]; simp [d, K33])
      calc (3 : ℕ∞) = 2 * 1 + 1 := by norm_num
        _ ≤ _ := by gcongr; exact le_min a b
    have := h3.trans (h1.trans h)
    exact absurd this (by norm_num)
  refine ⟨mergeV v y, mergeV_dist2 hvy ?_, mergeV_consistentIn hvy ?_ ?_, ?_⟩
  · intro c hc hc'
    have hnot : ¬ K33.graph.Adj y v := by
      intro h
      rcases (adj_orig_pos d hd0 _).1 h with ⟨-, h⟩ | ⟨h, -⟩
      · rw [hstart] at h; exact absurd h (by decide)
      · simp [d, K33] at h
    rcases hc with rfl | hc <;> rcases hc' with hc' | hc'
    · exact hvy hc'.symm
    · exact hnot hc'.symm
    · subst hc'; exact hnot hc
    · obtain ⟨d', hs', hL', rfl⟩ := (adj_orig_iff _ c).1 hc'.symm
      obtain ⟨m, hm⟩ := pos_eq_gad d hd0
      obtain ⟨m', hm'⟩ := pos_eq_gad d' (k := 0) (by omega)
      have he : d'.1 = d.1 := by
        have := hc; rw [hm', show v = pos d 0 from rfl, hm] at this; exact this.1
      obtain ⟨e', b'⟩ := d'
      simp only at he
      subst he
      cases b' <;> simp [start, d, K33] at hs'
  · exact fun h => hfar (by rw [gd2_comm]; exact h)
  · exact hfar
  · intro hL
    refine hL (3 : Fin 6) v ?_ y ?_ hvy.symm (by simp [mergeV])
    · exact (adj_orig_pos d hd0 _).2 (Or.inl ⟨rfl, hstart.symm⟩)
    · have := gd2_start_stop (B := K33) ((1, 0), false) (K33.len_pos _)
      simpa [gball, start, stop, K33, y] using this

/-- **Theorem 5.1 as stated is false.** For the gadgeted `K_{3,3}` (3-regular, simple, with a
distance-`2r` edge colouring) and `r = 1`, the colouring `merge 0 1` is a distance-2 colouring and
is edge-consistent in every `1`-gball in the paper's sense, but it is not injective on the
`1`-gball of the original vertex `3`. -/
theorem theorem_5_1_false :
    K33.IsSimple ∧ K33.IsCubic ∧ (∀ e, 0 < K33.len e) ∧ K33.IsDistEdgeColoring (2 * 1) ∧
    ∃ χ : K33.Vert → K33.Vert, K33.IsDist2Coloring χ ∧ K33.IsEdgeConsistentIn 1 χ ∧
      ¬ K33.IsGDistOrigColoring 1 χ := by
  have hne : (0 : Fin 6) ≠ (1 : Fin 6) := by decide
  refine ⟨K33.isSimple, K33.isCubic, K33.len_pos, K33.isDistEdgeColoring _,
    merge (B := K33) (0 : Fin 6) (1 : Fin 6),
    merge_dist2 hne, merge_consistentIn hne ?_, ?_⟩
  · -- `0` and `1` are at distance `2` in `K_{3,3}`
    have h := (edist_le_one_iff_adj_or_eq (G := K33.G0) (u := (0 : Fin 6)) (v := (1 : Fin 6))).not.2
      (by rintro (h | h); exact K33.not_adj_01 h; exact hne h)
    simpa using h
  · intro hinj
    -- the expanded edges `(0, 0)` (from `0` to `3`) and `(1, 0)` (from `1` to `3`)
    have h0 : Vert.orig (B := K33) (0 : Fin 6) ∈ K33.gball 1 (.orig (3 : Fin 6)) := by
      have := gd2_start_stop (B := K33) ((0, 0), false) (K33.len_pos _)
      simpa [gball, start, stop, K33] using this
    have h1 : Vert.orig (B := K33) (1 : Fin 6) ∈ K33.gball 1 (.orig (3 : Fin 6)) := by
      have := gd2_start_stop (B := K33) ((1, 0), false) (K33.len_pos _)
      simpa [gball, start, stop, K33] using this
    have := hinj (3 : Fin 6) h0 h1 (by simp [merge])
    injection this with h
    exact hne h

end Podc.LCLDefinitions

namespace Podc.LCLDefinitions

/-- Non-vacuity of the repaired Theorem 5.1: its hypotheses hold for the gadgeted `K_{3,3}` with
any injective colouring, e.g. the identity. -/
theorem theorem_5_1_repaired_nonvacuous :
    K33.IsDist2Coloring (id : K33.Vert → K33.Vert) ∧ K33.IsEdgeConsistent (id : K33.Vert → K33.Vert) ∧
      K33.IsGDistOrigColoring 1 (id : K33.Vert → K33.Vert) := by
  have hD : K33.IsDist2Coloring (id : K33.Vert → K33.Vert) := fun _ _ _ _ _ hab h => hab h
  have hC : K33.IsEdgeConsistent (id : K33.Vert → K33.Vert) := by
    intro v u h v' hv
    simp only [id] at hv
    subst hv
    exact ⟨u, h, rfl⟩
  exact ⟨hD, hC, Base.theorem_5_1_repaired K33.len_pos (K33.isDistEdgeColoring _) hD hC⟩

end Podc.LCLDefinitions
