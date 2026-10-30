import Papers.PODC2026.LCLDefinitions.Rigidity

/-!
# Theorem 5.1, repaired

Theorem 5.1 of *It does not matter how you define locally checkable labelings* (Cruciani, Das,
Raevskaya, Suomela; PODC 2026) as stated is false (see `Counterexample.lean`). Here we prove it
with condition 2 (edge-consistency) required for *all* pairs of vertices instead of only for
`v' ∈ gball_r(v)`: `theorem_5_1_repaired`.

Ingredients: lower bounds for the gadgeted distance via a potential (`le_gd2`, `mem_gball_orig`,
`mem_gball_gad`), the rigidity results of `Rigidity.lean`, and the observation that an expanded
edge cannot be matched with itself read backwards (`not_match_rev`; at the middle of the edge two
adjacent or distance-2 vertices would get the same colour).
-/

namespace Podc.LCLDefinitions

namespace Base

variable {B : Base} {C : Type*} {χ : B.Vert → C}

open SimpleGraph

/-! ### Gadgeted distance -/

lemma walkWt_ge (f : B.Vert → ℕ∞) (hf : ∀ a b, B.graph.Adj a b → f b ≤ f a + B.wt a b)
    {a b : B.Vert} (p : B.graph.Walk a b) : f b ≤ f a + (B.walkWt p : ℕ∞) := by
  induction p with
  | nil => simp [walkWt]
  | cons h p ih =>
    simp only [walkWt, Nat.cast_add]
    calc _ ≤ _ := ih
      _ ≤ f _ + (B.wt _ _ : ℕ∞) + B.walkWt p := by gcongr; exact hf _ _ h
      _ = _ := by ring

/-- A `1`-Lipschitz potential (w.r.t. the doubled weights) bounds the gadgeted distance. -/
lemma le_gd2 (f : B.Vert → ℕ∞) (hf : ∀ a b, B.graph.Adj a b → f b ≤ f a + B.wt a b)
    (a b : B.Vert) : f b ≤ f a + B.gd2 a b := by
  unfold gd2
  rw [ENat.add_iInf]
  exact le_iInf fun p => walkWt_ge f hf p

/-- The potential `2 · dist_G(v, ·)` extended to gadget vertices. -/
noncomputable def pot (v : B.V) : B.Vert → ℕ∞
  | .orig o => 2 * B.G0.edist v o
  | .gad e _ => 2 * min (B.G0.edist v (B.src e)) (B.G0.edist v (B.tgt e)) + 1

lemma edist_src_le (v : B.V) (e : B.E) : B.G0.edist v (B.src e) ≤ B.G0.edist v (B.tgt e) + 1 := by
  by_cases h : B.src e = B.tgt e
  · rw [h]; exact le_self_add
  · have hadj : B.G0.Adj (B.tgt e) (B.src e) := ⟨Ne.symm h, e, Or.inr ⟨rfl, rfl⟩⟩
    calc _ ≤ B.G0.edist v (B.tgt e) + B.G0.edist (B.tgt e) (B.src e) := B.G0.edist_triangle
      _ = _ := by rw [edist_eq_one_iff_adj.2 hadj]

lemma edist_tgt_le (v : B.V) (e : B.E) : B.G0.edist v (B.tgt e) ≤ B.G0.edist v (B.src e) + 1 := by
  by_cases h : B.src e = B.tgt e
  · rw [h]; exact le_self_add
  · have hadj : B.G0.Adj (B.src e) (B.tgt e) := ⟨h, e, Or.inl ⟨rfl, rfl⟩⟩
    calc _ ≤ B.G0.edist v (B.src e) + B.G0.edist (B.src e) (B.tgt e) := B.G0.edist_triangle
      _ = _ := by rw [edist_eq_one_iff_adj.2 hadj]

lemma two_mul_le (x y : ℕ∞) (h : x ≤ y + 1) : 2 * x ≤ 2 * y + 1 + 1 := by
  calc 2 * x ≤ 2 * (y + 1) := by gcongr
    _ = _ := by ring

lemma pot_lip (v : B.V) : ∀ a b, B.graph.Adj a b → pot v b ≤ pot v a + B.wt a b := by
  have key : ∀ (o : B.V) (e : B.E), (o = B.src e ∨ o = B.tgt e) →
      pot v (.orig o) ≤ 2 * min (B.G0.edist v (B.src e)) (B.G0.edist v (B.tgt e)) + 1 + 1 ∧
      2 * min (B.G0.edist v (B.src e)) (B.G0.edist v (B.tgt e)) + 1 ≤ pot v (.orig o) + 1 := by
    intro o e ho
    simp only [pot]
    constructor
    · rcases min_choice (B.G0.edist v (B.src e)) (B.G0.edist v (B.tgt e)) with hm | hm <;>
        rw [hm] <;> rcases ho with rfl | rfl
      · exact le_self_add.trans (le_self_add)
      · exact two_mul_le _ _ (edist_tgt_le v e)
      · exact two_mul_le _ _ (edist_src_le v e)
      · exact le_self_add.trans (le_self_add)
    · gcongr
      rcases ho with rfl | rfl
      · exact min_le_left _ _
      · exact min_le_right _ _
  intro a b h
  cases a with
  | orig o =>
    cases b with
    | orig o' => exact absurd h id
    | gad e k =>
      have ho : o = B.src e ∨ o = B.tgt e := by
        rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact Or.inl h1
        · exact Or.inr h1
      simpa [wt, pot] using (key o e ho).2
  | gad e k =>
    cases b with
    | orig o =>
      have ho : o = B.src e ∨ o = B.tgt e := by
        rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact Or.inl h1
        · exact Or.inr h1
      simpa [wt, pot] using (key o e ho).1
    | gad e' k' =>
      obtain ⟨rfl, -⟩ := h
      simp [pot]

lemma pot_self (v : B.V) : pot v (.orig v) = 0 := by simp [pot]

/-- Original vertices of `gball_r(v)` are at distance `≤ r` from `v` in the base graph. -/
lemma mem_gball_orig {r : ℕ} {v o : B.V} (h : Vert.orig o ∈ B.gball r (.orig v)) :
    B.G0.edist v o ≤ r := by
  have h1 := le_gd2 (pot v) (pot_lip v) (.orig v) (.orig o)
  rw [pot_self, zero_add] at h1
  have h2 : (2 : ℕ∞) * B.G0.edist v o ≤ 2 * r := by
    simpa [pot] using h1.trans h
  have hne : B.G0.edist v o ≠ ⊤ := by
    intro ht; rw [ht] at h2; simp at h2
    exact absurd h2 (by exact_mod_cast (ENat.natCast_ne_top _))
  lift B.G0.edist v o to ℕ using hne with n hn
  have : 2 * n ≤ 2 * r := by exact_mod_cast h2
  exact_mod_cast (show n ≤ r by omega)

/-- Gadget vertices of `gball_r(v)` lie on expanded edges with an endpoint at distance `≤ r - 1`
from `v`. -/
lemma mem_gball_gad {r : ℕ} {v : B.V} {e : B.E} {k : Fin (6 * B.len e)}
    (h : Vert.gad e k ∈ B.gball r (.orig v)) :
    B.G0.edist v (B.src e) + 1 ≤ r ∨ B.G0.edist v (B.tgt e) + 1 ≤ r := by
  have h1 := le_gd2 (pot v) (pot_lip v) (.orig v) (.gad e k)
  rw [pot_self, zero_add] at h1
  have h2 : 2 * min (B.G0.edist v (B.src e)) (B.G0.edist v (B.tgt e)) + 1 ≤ (2 * r : ℕ∞) :=
    h1.trans h
  have hne : min (B.G0.edist v (B.src e)) (B.G0.edist v (B.tgt e)) ≠ ⊤ := by
    intro ht; rw [ht] at h2; simp at h2
    exact absurd h2 (by exact_mod_cast (ENat.natCast_ne_top _))
  rcases min_choice (B.G0.edist v (B.src e)) (B.G0.edist v (B.tgt e)) with hm | hm <;>
    rw [hm] at h2 hne
  · left
    lift B.G0.edist v (B.src e) to ℕ using hne with n hn
    have : 2 * n + 1 ≤ 2 * r := by exact_mod_cast h2
    exact_mod_cast (show n + 1 ≤ r by omega)
  · right
    lift B.G0.edist v (B.tgt e) to ℕ using hne with n hn
    have : 2 * n + 1 ≤ 2 * r := by exact_mod_cast h2
    exact_mod_cast (show n + 1 ≤ r by omega)

lemma wt_comm (a b : B.Vert) : B.wt a b = B.wt b a := by
  cases a <;> cases b <;> rfl

lemma walkWt_append {a b c : B.Vert} (p : B.graph.Walk a b) (q : B.graph.Walk b c) :
    B.walkWt (p.append q) = B.walkWt p + B.walkWt q := by
  induction p with
  | nil => simp [walkWt]
  | cons h p ih => simp [walkWt, ih]; ring

lemma walkWt_reverse {a b : B.Vert} (p : B.graph.Walk a b) : B.walkWt p.reverse = B.walkWt p := by
  induction p with
  | nil => simp [walkWt]
  | cons h p ih =>
    rw [Walk.reverse_cons, walkWt_append, ih]
    simp [walkWt, wt_comm]; ring

lemma gd2_comm (a b : B.Vert) : B.gd2 a b = B.gd2 b a := by
  apply le_antisymm
  · exact le_iInf fun p => (iInf_le _ p.reverse).trans (by rw [walkWt_reverse])
  · exact le_iInf fun p => (iInf_le _ p.reverse).trans (by rw [walkWt_reverse])

lemma gd2_le_walk {a b : B.Vert} (p : B.graph.Walk a b) : B.gd2 a b ≤ B.walkWt p := iInf_le _ p

/-- Walking from position `k` to the end of an expanded edge costs (doubled) weight `1`. -/
lemma exists_walk_to_stop (d : B.Dir) : ∀ n k, k + n + 1 = 6 * B.len d.1 →
    ∃ p : B.graph.Walk (pos d k) (.orig (stop d)), B.walkWt p = 1 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have h := adj_nextV d (k := k) (by omega)
    rw [nextV, if_pos (by omega)] at h
    refine ⟨Walk.cons h Walk.nil, ?_⟩
    obtain ⟨m, hm⟩ := pos_eq_gad d (k := k) (by omega)
    simp [walkWt, hm, wt]
  | succ n ih =>
    intro k hk
    obtain ⟨p, hp⟩ := ih (k + 1) (by omega)
    have h := adj_pp d (k := k) (k' := k + 1) (by omega) (by omega) (cadj_succ k)
    refine ⟨Walk.cons h p, ?_⟩
    obtain ⟨m, hm⟩ := pos_eq_gad d (k := k) (by omega)
    obtain ⟨m', hm'⟩ := pos_eq_gad d (k := k + 1) (by omega)
    simp only [walkWt, hp]
    rw [hm, hm']; simp [wt]

/-- The two ends of an expanded edge are at gadgeted distance `1`. -/
lemma gd2_start_stop (d : B.Dir) (hL : 0 < B.len d.1) :
    B.gd2 (.orig (start d)) (.orig (stop d)) ≤ 2 := by
  obtain ⟨p, hp⟩ := exists_walk_to_stop d (6 * B.len d.1 - 1) 0 (by omega)
  have h := (adj_orig_pos d (k := 0) (by omega) (start d)).2 (Or.inl ⟨rfl, rfl⟩)
  refine (gd2_le_walk (Walk.cons h p)).trans ?_
  simp [walkWt, hp, wt]

/-! ### An expanded edge is not matched with itself backwards -/

theorem not_match_rev (hD : B.IsDist2Coloring χ) (hC : B.IsEdgeConsistent χ) (d : B.Dir)
    (hL : 0 < B.len d.1) (hs : χ (.orig (start d)) = χ (.orig (stop d)))
    (h0 : χ (pos d 0) = χ (pos (rev d) 0)) : False := by
  obtain ⟨-, -, hm⟩ := rigid hD hC (d' := rev d) hL hL (by rwa [start_rev]) h0
  obtain ⟨m, hm' | hm'⟩ : ∃ m, B.len d.1 = 2 * m + 1 ∨ B.len d.1 = 2 * m + 2 :=
    ⟨(B.len d.1 - 1) / 2, by omega⟩
  · obtain ⟨-, -, h | h⟩ := hm m (by omega)
    · rw [pos_rev d (by omega), show 6 * B.len d.1 - 1 - (6 * m + 1) = 6 * m + 4 by omega] at h
      exact hD.ne_adj (adj_pp d (by omega) (by omega) (cadj_in m (by simp [InnerAdj]))) h.1
    · rw [pos_rev d (by omega), show 6 * B.len d.1 - 1 - (6 * m + 2) = 6 * m + 3 by omega] at h
      exact hD.ne_common (c := pos d (6 * m + 2))
        (adj_pp d (by omega) (by omega) (cadj_in m (by simp [InnerAdj])))
        (adj_pp d (by omega) (by omega) (cadj_in m (by simp [InnerAdj])))
        (by rw [Ne, pos_inj d (by omega) (by omega)]; omega) h.1
  · obtain ⟨-, h, -⟩ := hm m (by omega)
    rw [pos_rev d (by omega), show 6 * B.len d.1 - 1 - (6 * m + 5) = 6 * m + 5 + 1 by omega] at h
    exact hD.ne_adj (adj_pp d (by omega) (by omega) (cadj_succ _)) h

/-! ### Auxiliary facts -/

lemma gad_eq_pos_dir (e : B.E) (k : Fin (6 * B.len e)) (b : Bool) :
    ∃ k', k' < 6 * B.len e ∧ Vert.gad e k = pos (e, b) k' := by
  cases b
  · refine ⟨6 * B.len e - 1 - k.val, by omega, ?_⟩
    have := k.isLt
    simp only [pos, show 6 * B.len e - 1 - k.val < 6 * B.len e by omega, dite_true,
      Bool.false_eq_true, ite_false]
    congr 1; exact Fin.ext (by simp; omega)
  · exact ⟨k.val, k.isLt, by simp [pos, k.isLt]⟩

lemma edge_of_pos {d : B.Dir} {j : ℕ} (hj : j < 6 * B.len d.1) {e : B.E} {k : Fin (6 * B.len e)}
    (h : pos d j = Vert.gad e k) : e = d.1 := by
  obtain ⟨m, hm⟩ := pos_eq_gad d hj
  rw [hm] at h
  injection h with h1
  exact h1.symm

lemma dir_eq {d d' : B.Dir} (h : d.1 = d'.1) : d' = d ∨ d' = rev d := by
  obtain ⟨e, b⟩ := d
  obtain ⟨e', b'⟩ := d'
  simp only at h
  subst h
  cases b <;> cases b' <;> simp [rev]

lemma start_mem_ends (d : B.Dir) : start d ∈ B.ends d.1 := by
  unfold start ends; split_ifs <;> simp

lemma stop_mem_ends (d : B.Dir) : stop d ∈ B.ends d.1 := by
  unfold stop ends; split_ifs <;> simp

lemma exists_dir_of_adj {o p : B.V} (h : B.G0.Adj o p) : ∃ d : B.Dir, start d = o ∧ stop d = p := by
  obtain ⟨-, e, he | he⟩ := h
  · exact ⟨(e, true), by simp [start, he.1], by simp [stop, he.2]⟩
  · exact ⟨(e, false), by simp [start, he.2], by simp [stop, he.1]⟩

/-- A vertex `o ≠ v` at distance `≤ r` from `v` has a neighbour at distance `≤ r - 1`. -/
lemma exists_closer {v o : B.V} {r : ℕ} (hne : o ≠ v) (h : B.G0.edist v o ≤ r) :
    ∃ p, B.G0.Adj o p ∧ B.G0.edist v p + 1 ≤ r := by
  have hreach : B.G0.Reachable o v := by
    rw [← edist_ne_top_iff_reachable, edist_comm]
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top r) h
  obtain ⟨w, hw⟩ := hreach.exists_walk_length_eq_edist
  cases w with
  | nil => exact absurd rfl hne
  | cons hadj q =>
    refine ⟨_, hadj, ?_⟩
    rw [SimpleGraph.edist_comm] at h ⊢
    calc B.G0.edist _ v + 1 ≤ q.length + 1 := by gcongr; exact SimpleGraph.edist_le q
      _ = ((Walk.cons hadj q).length : ℕ∞) := by simp
      _ = B.G0.edist o v := hw
      _ ≤ r := h

lemma edist_add_le {p q v : B.V} {r : ℕ} (hp : B.G0.edist v p + 1 ≤ r) (hq : B.G0.edist v q ≤ r) :
    B.G0.edist p q + 1 ≤ (2 * r : ℕ) := by
  calc B.G0.edist p q + 1 ≤ B.G0.edist p v + B.G0.edist v q + 1 := by
        gcongr; exact B.G0.edist_triangle
    _ = (B.G0.edist v p + 1) + B.G0.edist v q := by rw [SimpleGraph.edist_comm (u := p)]; ring
    _ ≤ r + r := add_le_add hp hq
    _ = (2 * r : ℕ) := by push_cast; ring

/-- Two originals of `gball_r(v)` with the same colour coincide (the case `o₁ ≠ v`). -/
lemma orig_case (hpos : ∀ e, 0 < B.len e) {r : ℕ} (hx : B.IsDistEdgeColoring (2 * r))
    (hD : B.IsDist2Coloring χ) (hC : B.IsEdgeConsistent χ) {v o1 o2 : B.V} (h1 : o1 ≠ v)
    (hne : o1 ≠ o2) (e1 : B.G0.edist v o1 ≤ r) (e2 : B.G0.edist v o2 ≤ r)
    (hc : χ (.orig o1) = χ (.orig o2)) : False := by
  obtain ⟨p, hp, hpv⟩ := exists_closer h1 e1
  obtain ⟨d, rfl, rfl⟩ := exists_dir_of_adj hp
  have hL := hpos d.1
  obtain ⟨y, hy, hyc⟩ := hC.step hc.symm ((adj_orig_pos d (k := 0) (by omega) _).2 (Or.inl ⟨rfl, rfl⟩))
  obtain ⟨d', rfl, hL', rfl⟩ := (adj_orig_iff _ y).1 hy
  obtain ⟨hlen, -, -⟩ := rigid hD hC hL hL' hc hyc.symm
  have hedge : d.1 = d'.1 := by
    by_contra hdd
    exact hx d.1 d'.1 hdd ⟨stop d, stop_mem_ends d, start d', start_mem_ends d',
      edist_add_le hpv e2⟩ hlen
  obtain hdd | hdd := dir_eq hedge <;> subst d'
  · exact hne rfl
  · exact not_match_rev hD hC d hL (by rw [hc, start_rev]) hyc.symm

/-- **Theorem 5.1, repaired.** Let `gadget(G, x)` be a gadgeted graph whose colouring `x` (here
`len`) is a distance-`2r` edge colouring with positive values. If `χ` is a distance-2 colouring that
is edge-consistent (condition 2 of Theorem 5.1 required for *all* pairs of vertices, not only
inside `r`-gballs), then for every original vertex `v`, all vertices of `gball_r(v)` have distinct
colours. The base graph need not be simple or 3-regular. -/
theorem theorem_5_1_repaired (hpos : ∀ e, 0 < B.len e) {r : ℕ} (hx : B.IsDistEdgeColoring (2 * r))
    (hD : B.IsDist2Coloring χ) (hC : B.IsEdgeConsistent χ) : B.IsGDistOrigColoring r χ := by
  intro v a ha b hb hab
  by_contra hne
  cases a with
  | orig o1 =>
    cases b with
    | gad e k => exact orig_ne_gad hD hC o1 e k hab
    | orig o2 =>
      have hne' : o1 ≠ o2 := fun h => hne (by rw [h])
      have e1 := mem_gball_orig ha
      have e2 := mem_gball_orig hb
      by_cases h1 : o1 = v
      · subst h1
        exact orig_case hpos hx hD hC (Ne.symm hne') (Ne.symm hne') e2 e1 hab.symm
      · exact orig_case hpos hx hD hC h1 hne' e1 e2 hab
  | gad e k =>
    cases b with
    | orig o => exact orig_ne_gad hD hC o e k hab.symm
    | gad e' k' =>
      -- orient `e` from its endpoint closer to `v`
      obtain ⟨d, hd1, hp⟩ : ∃ d : B.Dir, d.1 = e ∧ B.G0.edist v (start d) + 1 ≤ r := by
        rcases mem_gball_gad ha with h | h
        · exact ⟨(e, true), rfl, by simpa [start] using h⟩
        · exact ⟨(e, false), rfl, by simpa [start] using h⟩
      subst hd1
      obtain ⟨ka, hka, hka'⟩ := gad_eq_pos_dir d.1 k d.2
      rw [show ((d.1, d.2) : B.Dir) = d from rfl] at hka'
      obtain ⟨d', hL', hs, h0, hbd⟩ := match_pos hD hC d ka hka _ (hab.symm.trans (by rw [hka']))
      obtain ⟨hlen, -, -⟩ := rigid hD hC (by omega) hL' hs.symm h0.symm
      have he' : e' = d'.1 := edge_of_pos (psi_lt d d' (by rw [← hlen]; exact hka)) hbd.symm
      subst he'
      obtain ⟨q, hqe, hq⟩ : ∃ q ∈ B.ends d'.1, B.G0.edist v q + 1 ≤ r := by
        rcases mem_gball_gad hb with h | h
        · exact ⟨_, by simp [ends], h⟩
        · exact ⟨_, by simp [ends], h⟩
      have hedge : d.1 = d'.1 := by
        by_contra hdd
        exact hx d.1 d'.1 hdd ⟨start d, start_mem_ends d, q, hqe,
          edist_add_le hp (le_trans le_self_add hq)⟩ hlen
      obtain hdd | hdd := dir_eq hedge <;> subst d'
      · -- matched with itself: positions `k` and `tau k` of one gadget, which are adjacent
        obtain ⟨p, s, hs6, rfl⟩ : ∃ p s, s < 6 ∧ ka = 6 * p + s :=
          ⟨ka / 6, ka % 6, by omega, by omega⟩
        obtain ⟨f, hf, -⟩ := psi_eq (χ := χ) d d (p := p) hs6
        rw [hf] at hbd
        rw [hka', hbd] at hab hne
        cases f
        · exact hne rfl
        · simp only [ite_true] at hab hne
          interval_cases s
          · exact hne (by simp [tau])
          · exact hD.ne_adj (adj_pp d (by omega) (by simp [tau]; omega)
              (cadj_in p (by simp [tau, InnerAdj]))) hab
          · exact hD.ne_adj (adj_pp d (by omega) (by simp [tau]; omega)
              (cadj_in p (by simp [tau, InnerAdj]))) hab
          · exact hD.ne_adj (adj_pp d (by omega) (by simp [tau]; omega)
              (cadj_in p (by simp [tau, InnerAdj]))) hab
          · exact hD.ne_adj (adj_pp d (by omega) (by simp [tau]; omega)
              (cadj_in p (by simp [tau, InnerAdj]))) hab
          · exact hne (by simp [tau])
      · exact not_match_rev hD hC d (by omega) (by rw [← hs, start_rev]) h0.symm

end Base

end Podc.LCLDefinitions
