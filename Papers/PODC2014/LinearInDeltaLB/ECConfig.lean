import Papers.PODC2014.LinearInDeltaLB.Defs

/-!
# Step 1 of [GHS14]: configurations inside the Cayley tree

The graphs `G_i`, `H_i` of Section 4 of [GHS14] are trees with loops (property (P3)). We represent
them inside the Cayley tree `Γ_k` of the free Coxeter group: a *configuration* `C : Cfg k` is a
finite colour system `C.T ⊆ G_k` (the tree part, rooted at the distinguished node `1`) together with
a loop assignment `C.L`; its graph is CSLib's `tGraph C.T C.L` (tree edges inside `C.T`, plus a
half-loop of colour `d` at `s` whenever `d ∈ C.L s` and `s d ∉ C.T`).

The unfold-and-mix construction of Section 4.3 becomes `mix c C D = C.T ∪ c · D.T`: the copy of
`D` is attached at the node `c` (= `gen c`), so the new colour-`c` edge is the Cayley edge `{1, c}`.
Unfolding `G` at its `c`-loop is `mix c C C`, which covers `C` (`view_mix_self`).

Main facts:
* `Cfg.restrict`: the configuration as a `ColouredGraph` on the finite type `C.T`, with the same
  views (`view_restrict`); so `ECAlg.SolvesLoopy` applies to it (`Cfg.fm_symm`, `Cfg.load_eq_one`).
* `mix_step_left`, `mix_step_right`, `mix_step_bridge`: the edges of `mix c C D`.
* `Cfg.Good.mix`: the mixed configuration is again good, with one more non-loop colour per node
  (this is (P2)).
* `ball_view_succ_of_step_eq`: the radius-`(r+1)` view is determined by the steps at the root and
  the radius-`r` views of the neighbours.
-/

namespace Podc.LinearInDeltaLB

open Cslib.ColourSystem FreeCox Pointwise

variable {k : ℕ}

/-! ### Restricting a coloured graph to a closed set of nodes -/

section Restrict

variable {α : Type*}

-- CSLib candidate
/-- The subgraph of `G` induced on a set `T` of nodes that is closed under steps. -/
def _root_.Cslib.ColourSystem.ColouredGraph.restrict (G : ColouredGraph k α) (T : Set α)
    (hT : ∀ a ∈ T, ∀ d b, G.step a d = some b → b ∈ T) : ColouredGraph k T where
  step a d := (G.step a.1 d).pmap (fun b hb => ⟨b, hT a.1 a.2 d b hb⟩) (fun _ h => h)
  symm a b d h := by
    obtain ⟨b', -, hb', rfl⟩ := Option.pmap_eq_some_iff.1 h
    have := G.symm _ _ _ hb'
    simp only [Option.pmap_eq_some_iff]
    exact ⟨a.1, this, this, rfl⟩

theorem _root_.Cslib.ColourSystem.ColouredGraph.restrict_step_map (G : ColouredGraph k α)
    (T : Set α) (hT : ∀ a ∈ T, ∀ d b, G.step a d = some b → b ∈ T) (a : T) (d : Fin k) :
    ((G.restrict T hT).step a d).map Subtype.val = G.step a.1 d := by
  simp [ColouredGraph.restrict, Option.map_pmap]

theorem _root_.Cslib.ColourSystem.ColouredGraph.view_restrict (G : ColouredGraph k α)
    (T : Set α) (hT : ∀ a ∈ T, ∀ d b, G.step a d = some b → b ∈ T) (a : T) :
    (G.restrict T hT).view a = G.view a.1 :=
  ((G.restrict T hT).view_map G Subtype.val
    (fun a d => (G.restrict_step_map T hT a d).symm) a).symm

theorem _root_.Cslib.ColourSystem.ColouredGraph.restrict_step_isSome (G : ColouredGraph k α)
    (T : Set α) (hT : ∀ a ∈ T, ∀ d b, G.step a d = some b → b ∈ T) (a : T) (d : Fin k) :
    ((G.restrict T hT).step a d).isSome = (G.step a.1 d).isSome := by
  simp [ColouredGraph.restrict]

end Restrict

/-! ### First letters -/

-- CSLib candidates (this section; `len_gen_mul_ne`, `startsWith_gen_mul_iff` are also duplicated in
-- `Papers/PODC2021/MISTreeLowerBounds/RoundElim.lean`)

theorem len_gen_mul_ne (c : Fin k) (x : FreeCox k) : len (gen c * x) ≠ len x := by
  have := len_mul_gen_ne x⁻¹ c
  rwa [← len_inv (x⁻¹ * gen c), mul_inv_rev, inv_gen, inv_inv, len_inv] at this

theorem startsWith_gen_mul_iff (c : Fin k) (x : FreeCox k) :
    startsWith c (gen c * x) ↔ ¬ startsWith c x := by
  unfold startsWith
  rw [← mul_assoc, gen_mul_gen, one_mul]
  have := len_gen_mul_ne c x
  omega

theorem len_gen_mul_of_not_startsWith {c : Fin k} {x : FreeCox k} (h : ¬ startsWith c x) :
    len (gen c * x) = len x + 1 := by
  unfold startsWith at h
  have := len_gen_mul_le x c
  have := len_gen_mul_ne c x
  omega

/-- In a colour system not containing `c`, no node starts with `c`. -/
theorem _root_.Cslib.ColourSystem.IsColourSystem.not_startsWith {T : Set (FreeCox k)}
    (hT : IsColourSystem T) {c : Fin k} (hc : gen c ∉ T) {x : FreeCox k} (hx : x ∈ T) :
    ¬ startsWith c x := by
  intro h
  apply hc
  refine hT.mem_of_isPre hx ?_
  unfold IsPre startsWith at *
  have := le_len_gen_mul x c
  rw [inv_gen, len_gen]
  omega

/-- Crossing from a node not starting with `c` to a node starting with `c` uses the edge `{1, c}`. -/
theorem eq_of_startsWith_mul_gen {c d : Fin k} {x : FreeCox k} (hx : ¬ startsWith c x)
    (hxd : startsWith c (x * gen d)) : d = c ∧ x = 1 := by
  obtain ⟨h1, h2 | h2⟩ := startsWith_mul_gen (c := c) (c' := d) (x := x) (by tauto)
  · exact ⟨h1, h2⟩
  · subst h2; simp at hx

/-! ### Configurations -/

/-- A configuration: a set `T ⊆ G_k` of nodes (tree part) and a loop assignment `L`. -/
@[ext] structure Cfg (k : ℕ) where
  /-- The nodes; the tree edges are the Cayley edges inside `T`. -/
  T : Set (FreeCox k)
  /-- `d ∈ L s`: node `s` carries a colour-`d` loop (if `s d ∉ T`). -/
  L : FreeCox k → Set (Fin k)

namespace Cfg

variable (C D : Cfg k)

/-- The coloured graph of a configuration. -/
noncomputable def graph : ColouredGraph k (FreeCox k) := tGraph C.T C.L

/-- The view of node `a` in the graph of `C`. -/
abbrev view (a : FreeCox k) : Set (FreeCox k) := C.graph.view a

open Classical in
/-- The colours that are *not* loops at `x`: tree edges and missing colours. -/
noncomputable def bad (x : FreeCox k) : Finset (Fin k) :=
  Finset.univ.filter fun d => x * gen d ∈ C.T ∨ d ∉ C.L x

/-- A good configuration at level `i`: a finite colour system in which every node has at most
`i + 1` non-loop colours, i.e. at least `k - 1 - i` loops (property (P2)). The graph is a tree with
loops by construction (property (P3)). -/
def Good (i : ℕ) : Prop :=
  IsColourSystem C.T ∧ C.T.Finite ∧ ∀ x ∈ C.T, (C.bad x).card ≤ i + 1

/-- Re-rooting at `g`: translate by `g⁻¹`. -/
def shift (g : FreeCox k) : Cfg k := ⟨g⁻¹ • C.T, fun x => C.L (g * x)⟩

/-- Mixing: `C` and a copy of `D` attached at the node `c`, joined by the Cayley edge `{1, c}`. -/
noncomputable def mix (c : Fin k) : Cfg k :=
  ⟨C.T ∪ gen c • D.T, fun x => if startsWith c x then D.L (gen c * x) else C.L x⟩

variable {C D}

theorem mem_bad {x : FreeCox k} {d : Fin k} : d ∈ C.bad x ↔ x * gen d ∈ C.T ∨ d ∉ C.L x := by
  classical simp [bad]

theorem graph_step_eq_some {s b : FreeCox k} {d : Fin k} (h : C.graph.step s d = some b) :
    s ∈ C.T ∧ ((s * gen d ∈ C.T ∧ b = s * gen d) ∨ (s * gen d ∉ C.T ∧ d ∈ C.L s ∧ b = s)) :=
  tGraph_step_eq_some h

theorem graph_step_mem {s b : FreeCox k} {d : Fin k} (h : C.graph.step s d = some b) : b ∈ C.T := by
  rcases graph_step_eq_some h with ⟨hs, ⟨h1, rfl⟩ | ⟨-, -, rfl⟩⟩ <;> assumption

theorem graph_step_of_not_mem {s : FreeCox k} (hs : s ∉ C.T) (d : Fin k) :
    C.graph.step s d = none := by
  simp [graph, tGraph, hs]

theorem graph_step_isSome {s : FreeCox k} {d : Fin k} (hs : s ∈ C.T) :
    (C.graph.step s d).isSome ↔ d ∉ C.bad s ∨ s * gen d ∈ C.T := by
  rw [graph, tGraph_step_isSome, mem_bad]; tauto

/-! #### Shifts -/

@[simp] theorem mem_shift_T {g x : FreeCox k} : x ∈ (C.shift g).T ↔ g * x ∈ C.T := by
  simp [shift, mem_inv_smul]

theorem shift_graph_step (g s : FreeCox k) (d : Fin k) :
    (C.shift g).graph.step (g⁻¹ * s) d = (C.graph.step s d).map (g⁻¹ * ·) := by
  have := tGraph_smul_step (T := C.T) (L := C.L) g⁻¹ s d
  simpa [graph, shift, inv_inv] using this

theorem view_shift (g a : FreeCox k) : (C.shift g).view (g⁻¹ * a) = C.view a := by
  have := view_tGraph_smul (T := C.T) (L := C.L) g⁻¹ a
  simpa [view, graph, shift, inv_inv] using this

theorem view_shift_one (g : FreeCox k) : (C.shift g).view 1 = C.view g := by
  simpa using view_shift (C := C) g g

theorem bad_shift (g x : FreeCox k) : (C.shift g).bad x = C.bad (g * x) := by
  ext d; simp [mem_bad, shift, mem_inv_smul, mul_assoc]

theorem Good.shift {i : ℕ} (h : C.Good i) {g : FreeCox k} (hg : g ∈ C.T) : (C.shift g).Good i :=
  ⟨h.1.inv_smul hg, h.2.1.smul_set, fun x hx => by
    rw [bad_shift]; exact h.2.2 _ (mem_shift_T.1 hx)⟩

/-! #### Mixing -/

variable {c : Fin k}

theorem mem_mix_T {x : FreeCox k} : x ∈ (C.mix D c).T ↔ x ∈ C.T ∨ gen c * x ∈ D.T := by
  simp [mix, mem_smul]

theorem mix_swap (C D : Cfg k) (c : Fin k) : C.mix D c = (D.mix C c).shift (gen c) := by
  ext x
  · simp only [mem_mix_T, mem_shift_T, ← mul_assoc, gen_mul_gen, one_mul]; tauto
  · simp only [mix, shift, startsWith_gen_mul_iff, ← mul_assoc, gen_mul_gen, one_mul]
    split_ifs <;> rfl

theorem mix_step_left (hC : IsColourSystem C.T) (hD : IsColourSystem D.T) (hcC : gen c ∉ C.T)
    (hcD : gen c ∉ D.T) {x : FreeCox k} (hx : x ∈ C.T) {d : Fin k} (hxd : ¬ (x = 1 ∧ d = c)) :
    (C.mix D c).graph.step x d = C.graph.step x d := by
  have hns := hC.not_startsWith hcC hx
  refine tGraph_step_congr ?_ ?_ ?_
  · simp [mem_mix_T, hx]
  · rw [mem_mix_T]
    refine ⟨fun h => h.resolve_right fun h' => ?_, Or.inl⟩
    have h1 := hD.not_startsWith hcD h'
    rw [startsWith_gen_mul_iff, not_not] at h1
    obtain ⟨rfl, rfl⟩ := eq_of_startsWith_mul_gen hns h1
    exact hxd ⟨rfl, rfl⟩
  · simp [mix, hns]

theorem mix_step_bridge (hC1 : (1 : FreeCox k) ∈ C.T) (hD1 : (1 : FreeCox k) ∈ D.T) :
    (C.mix D c).graph.step 1 c = some (gen c) := by
  have := tGraph_step_of_mem (T := (C.mix D c).T) (L := (C.mix D c).L) (s := 1) (c := c)
    (mem_mix_T.2 (Or.inl hC1)) (mem_mix_T.2 (Or.inr (by simpa using hD1)))
  simpa [graph] using this

theorem mix_step_right (hC : IsColourSystem C.T) (hD : IsColourSystem D.T) (hcC : gen c ∉ C.T)
    (hcD : gen c ∉ D.T) {t : FreeCox k} (ht : t ∈ D.T) {d : Fin k} (htd : ¬ (t = 1 ∧ d = c)) :
    (C.mix D c).graph.step (gen c * t) d = (D.graph.step t d).map (gen c * ·) := by
  rw [mix_swap C D c]
  have := shift_graph_step (C := D.mix C c) (gen c) t d
  rw [inv_gen] at this
  rw [this, mix_step_left hD hC hcD hcC ht htd]

theorem mix_step_bridge_right (hC1 : (1 : FreeCox k) ∈ C.T) (hD1 : (1 : FreeCox k) ∈ D.T) :
    (C.mix D c).graph.step (gen c) c = some 1 := by
  rw [mix_swap C D c]
  have := shift_graph_step (C := D.mix C c) (gen c) 1 c
  rw [inv_gen, mul_one, mix_step_bridge hD1 hC1] at this
  simpa using this

/-- Steps from a node of the left part do not depend on the right part. -/
theorem mix_step_left_eq {D' : Cfg k} (hC : IsColourSystem C.T) (hD : IsColourSystem D.T)
    (hD' : IsColourSystem D'.T) (hcC : gen c ∉ C.T) (hcD : gen c ∉ D.T) (hcD' : gen c ∉ D'.T)
    {x : FreeCox k} (hx : x ∈ C.T) (d : Fin k) :
    (C.mix D c).graph.step x d = (C.mix D' c).graph.step x d := by
  by_cases hxd : x = 1 ∧ d = c
  · obtain ⟨rfl, rfl⟩ := hxd
    rw [mix_step_bridge hx hD.one_mem, mix_step_bridge hx hD'.one_mem]
  · rw [mix_step_left hC hD hcC hcD hx hxd, mix_step_left hC hD' hcC hcD' hx hxd]

/-- Steps from a node of the right part do not depend on the left part. -/
theorem mix_step_right_eq {C' : Cfg k} (hC : IsColourSystem C.T) (hC' : IsColourSystem C'.T)
    (hD : IsColourSystem D.T) (hcC : gen c ∉ C.T) (hcC' : gen c ∉ C'.T) (hcD : gen c ∉ D.T)
    {t : FreeCox k} (ht : t ∈ D.T) (d : Fin k) :
    (C.mix D c).graph.step (gen c * t) d = (C'.mix D c).graph.step (gen c * t) d := by
  rw [mix_swap C D c, mix_swap C' D c]
  have h1 := shift_graph_step (C := D.mix C c) (gen c) t d
  have h2 := shift_graph_step (C := D.mix C' c) (gen c) t d
  rw [inv_gen] at h1 h2
  rw [h1, h2, mix_step_left_eq hD hC hC' hcD hcC hcC' ht d]

theorem card_bad_mix_left (hC : IsColourSystem C.T) (hD : IsColourSystem D.T) (hcC : gen c ∉ C.T)
    (hcD : gen c ∉ D.T) {x : FreeCox k} (hx : x ∈ C.T) :
    ((C.mix D c).bad x).card ≤ (C.bad x).card + 1 := by
  classical
  have hns := hC.not_startsWith hcC hx
  refine (Finset.card_le_card (s := (C.mix D c).bad x) (t := insert c (C.bad x)) ?_).trans
    (Finset.card_insert_le _ _)
  intro d hd
  rw [Finset.mem_insert, mem_bad]
  rw [mem_bad, mem_mix_T] at hd
  simp only [mix, hns, ite_false] at hd
  rcases hd with (h | h) | h
  · exact Or.inr (Or.inl h)
  · have h1 := hD.not_startsWith hcD h
    rw [startsWith_gen_mul_iff, not_not] at h1
    exact Or.inl (eq_of_startsWith_mul_gen hns h1).1
  · exact Or.inr (Or.inr h)

theorem isColourSystem_mix (hC : IsColourSystem C.T) (hD : IsColourSystem D.T)
    (hcD : gen c ∉ D.T) : IsColourSystem (C.mix D c).T := by
  refine ⟨mem_mix_T.2 (Or.inl hC.one_mem), fun x hx d hd => ?_⟩
  rcases mem_mix_T.1 hx with hx | ht
  · exact mem_mix_T.2 (Or.inl (hC.mul_gen_mem hx hd))
  · set t := gen c * x with ht_def
    have hxt : x = gen c * t := by rw [ht_def, ← mul_assoc, gen_mul_gen, one_mul]
    have hns := hD.not_startsWith hcD ht
    have hlx : len x = len t + 1 := by rw [hxt]; exact len_gen_mul_of_not_startsWith hns
    by_cases h1 : t = 1
    · have : x * gen d = 1 := by
        rw [← len_eq_zero]; rw [h1, len_one] at hlx; omega
      rw [this]; exact mem_mix_T.2 (Or.inl hC.one_mem)
    · refine mem_mix_T.2 (Or.inr ?_)
      have e : gen c * (x * gen d) = t * gen d := by rw [ht_def, mul_assoc]
      rw [e]
      refine hD.mul_gen_mem ht ?_
      by_contra hlt
      have h2 := len_mul_gen_of_not_lt hlt
      have h3 : ¬ startsWith c (t * gen d) := fun h => h1 (eq_of_startsWith_mul_gen hns h).2
      have h4 := len_gen_mul_of_not_startsWith h3
      have e' : gen c * (t * gen d) = x * gen d := by rw [← e, ← mul_assoc, gen_mul_gen, one_mul]
      rw [e'] at h4
      omega

theorem Good.mix {i : ℕ} (hC : C.Good i) (hD : D.Good i) (hcC : gen c ∉ C.T)
    (hcD : gen c ∉ D.T) : (C.mix D c).Good (i + 1) := by
  refine ⟨isColourSystem_mix hC.1 hD.1 hcD, hC.2.1.union hD.2.1.smul_set, fun x hx => ?_⟩
  by_cases hxC : x ∈ C.T
  · have := card_bad_mix_left (D := D) hC.1 hD.1 hcC hcD hxC
    have := hC.2.2 x hxC
    omega
  · have ht : gen c * x ∈ D.T := (mem_mix_T.1 hx).resolve_left hxC
    rw [mix_swap C D c, bad_shift]
    have := card_bad_mix_left (D := C) hD.1 hC.1 hcD hcC ht
    have := hD.2.2 _ ht
    omega

/-! #### Unfolding: `mix c C C` covers `C` -/

/-- The covering map `mix c C C → C`: fold the copy back. -/
def fold (c : Fin k) (a : FreeCox k) : FreeCox k := if startsWith c a then gen c * a else a

theorem fold_gen_mul (c : Fin k) (a : FreeCox k) : fold c (gen c * a) = fold c a := by
  unfold fold
  by_cases h : startsWith c a
  · have : ¬ startsWith c (gen c * a) := by rw [startsWith_gen_mul_iff]; exact not_not.2 h
    simp [h, this]
  · have : startsWith c (gen c * a) := by rw [startsWith_gen_mul_iff]; exact h
    simp [h, this, ← mul_assoc]

theorem mix_self_covering (hC : IsColourSystem C.T) (hcC : gen c ∉ C.T) (hL : c ∈ C.L 1)
    (a : FreeCox k) (d : Fin k) :
    C.graph.step (fold c a) d = ((C.mix C c).graph.step a d).map (fold c) := by
  have hleft : ∀ a ∈ C.T, ∀ d,
      C.graph.step (fold c a) d = ((C.mix C c).graph.step a d).map (fold c) := by
    intro a ha d
    have hns := hC.not_startsWith hcC ha
    have hfa : fold c a = a := by simp [fold, hns]
    rw [hfa]
    by_cases had : a = 1 ∧ d = c
    · obtain ⟨rfl, rfl⟩ := had
      rw [mix_step_bridge ha ha]
      have : fold d (gen d) = 1 := by simp [fold]
      rw [Option.map_some, this]
      exact tGraph_step_of_loop ha (by simpa using hcC) hL
    · rw [mix_step_left hC hC hcC hcC ha had]
      cases hb : C.graph.step a d with
      | none => rfl
      | some b =>
        have hbT := graph_step_mem hb
        simp [fold, hC.not_startsWith hcC hbT]
  by_cases ha : a ∈ C.T
  · exact hleft a ha d
  by_cases ht : gen c * a ∈ C.T
  · have e : (C.mix C c).graph.step a d =
        ((C.mix C c).graph.step (gen c * a) d).map (gen c * ·) := by
      conv_lhs => rw [mix_swap C C c]
      have := shift_graph_step (C := C.mix C c) (gen c) (gen c * a) d
      rwa [inv_gen, ← mul_assoc, gen_mul_gen, one_mul] at this
    rw [e, Option.map_map, ← fold_gen_mul c a, hleft _ ht d]
    congr 1
    funext b
    simp [fold_gen_mul]
  · have hn : (C.mix C c).graph.step a d = none :=
      graph_step_of_not_mem (by rw [mem_mix_T]; tauto) d
    rw [hn, Option.map_none]
    refine graph_step_of_not_mem ?_ d
    unfold fold
    split_ifs <;> assumption

theorem view_mix_self (hC : IsColourSystem C.T) (hcC : gen c ∉ C.T) (hL : c ∈ C.L 1)
    (a : FreeCox k) : (C.mix C c).view a = C.view (fold c a) :=
  (C.mix C c).graph.view_map C.graph (fold c) (fun a d => mix_self_covering hC hcC hL a d) a
    |>.symm

theorem view_mix_self_of_mem (hC : IsColourSystem C.T) (hcC : gen c ∉ C.T) (hL : c ∈ C.L 1)
    {a : FreeCox k} (ha : a ∈ C.T) : (C.mix C c).view a = C.view a := by
  rw [view_mix_self hC hcC hL]; simp [fold, hC.not_startsWith hcC ha]

theorem view_mix_self_gen (hC : IsColourSystem C.T) (hcC : gen c ∉ C.T) (hL : c ∈ C.L 1) :
    (C.mix C c).view (gen c) = C.view 1 := by
  rw [view_mix_self hC hcC hL]; simp [fold]

end Cfg

/-! ### Views grow one step at a time -/

-- CSLib candidate
theorem ball_view_zero {α : Type*} (G H : ColouredGraph k α) (a b : α) :
    ball (G.view a) 0 = ball (H.view b) 0 := by
  ext x
  simp only [mem_ball, Nat.le_zero, len_eq_zero]
  constructor <;> rintro ⟨-, rfl⟩ <;> exact ⟨ColouredGraph.one_mem_view _ _, rfl⟩

-- CSLib candidate
/-- The radius-`(r + 1)` view of `a` is determined by the steps at `a` and the radius-`r` views of
the neighbours of `a`. -/
theorem ball_view_succ_of_step_eq {α : Type*} (G H : ColouredGraph k α) (a : α) (r : ℕ)
    (hstep : ∀ d, G.step a d = H.step a d)
    (hnb : ∀ d b, G.step a d = some b → ball (G.view b) r = ball (H.view b) r) :
    ball (G.view a) (r + 1) = ball (H.view a) (r + 1) := by
  ext x
  simp only [mem_ball]
  refine and_congr_left fun hx => ?_
  by_cases hx1 : x = 1
  · subst hx1; simp [ColouredGraph.one_mem_view]
  obtain ⟨d, hd⟩ : ∃ d, startsWith d x := by
    rcases h : x.1.getLast? with _ | d
    · exact absurd (FreeCox.ext (by simpa using h)) hx1
    · exact ⟨d, (startsWith_iff d x).2 h⟩
  have hlen : len x = len (gen d * x) + 1 := by
    have := le_len_gen_mul x d; unfold startsWith at hd; omega
  set x' := gen d * x with hx'
  have hxx' : x = gen d * x' := by rw [hx', ← mul_assoc, gen_mul_gen, one_mul]
  have hpre : IsPre (gen d) x := by
    unfold IsPre; rw [inv_gen, len_gen, ← hx']; omega
  cases hG : G.step a d with
  | none =>
    have hH : H.step a d = none := by rw [← hstep, hG]
    have nG : x ∉ G.view a := fun h => by
      have := (G.isColourSystem_view a).mem_of_isPre h hpre
      simp [ColouredGraph.mem_view, hG] at this
    have nH : x ∉ H.view a := fun h => by
      have := (H.isColourSystem_view a).mem_of_isPre h hpre
      simp [ColouredGraph.mem_view, hH] at this
    exact iff_of_false nG nH
  | some b =>
    have hH : H.step a d = some b := by rw [← hstep, hG]
    have eG := G.view_inv_smul (x := gen d) (by rw [ColouredGraph.walk_gen]; exact hG)
    have eH := H.view_inv_smul (x := gen d) (by rw [ColouredGraph.walk_gen]; exact hH)
    have mG : x ∈ G.view a ↔ x' ∈ G.view b := by
      rw [← eG, mem_inv_smul, ← hxx']
    have mH : x ∈ H.view a ↔ x' ∈ H.view b := by
      rw [← eH, mem_inv_smul, ← hxx']
    rw [mG, mH]
    exact mem_iff_of_ball_eq (hnb d b hG) (by omega)

/-! ### Outputs of a solving algorithm on good configurations -/

namespace Cfg

variable {C : Cfg k} {i : ℕ}

theorem Good.exists_loop (hC : C.Good i) (hik : i + 1 < k) {x : FreeCox k} (hx : x ∈ C.T) :
    ∃ d, C.graph.step x d = some x := by
  classical
  have hcard : (C.bad x).card < (Finset.univ : Finset (Fin k)).card := by
    have := hC.2.2 x hx; simp; omega
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [mem_bad, not_or, not_not] at hd
  exact ⟨d, tGraph_step_of_loop hx hd.1 hd.2⟩

/-- The configuration as a coloured graph on the finite type of its nodes. -/
noncomputable def toGraph (C : Cfg k) : ColouredGraph k C.T :=
  C.graph.restrict C.T fun _ _ _ _ h => graph_step_mem h

theorem view_toGraph (a : C.T) : C.toGraph.view a = C.view a.1 :=
  C.graph.view_restrict _ _ a

theorem toGraph_step {x b : FreeCox k} {d : Fin k} (h : C.graph.step x d = some b) (hx : x ∈ C.T)
    (hb : b ∈ C.T) : C.toGraph.step ⟨x, hx⟩ d = some ⟨b, hb⟩ := by
  simp [toGraph, ColouredGraph.restrict, h]

theorem Good.finite (hC : C.Good i) : Finite C.T := Set.finite_coe_iff.2 hC.2.1

theorem Good.isLoopy (hC : C.Good i) (hik : i + 1 < k) : IsLoopy C.toGraph := by
  intro a
  obtain ⟨d, hd⟩ := hC.exists_loop hik a.2
  exact ⟨d, toGraph_step hd a.2 a.2⟩

theorem Good.isMaxFM {A : ECAlg k} (hA : A.SolvesLoopy) (hC : C.Good i) (hik : i + 1 < k) :
    IsMaxFM C.toGraph (fun a => A (C.view a.1)) := by
  have := hC.finite
  have h := hA C.T C.toGraph (hC.isLoopy hik)
  simpa [view_toGraph] using h

/-- Outputs of a solving algorithm are consistent on edges. -/
theorem Good.output_symm {A : ECAlg k} (hA : A.SolvesLoopy) (hC : C.Good i) (hik : i + 1 < k)
    {x b : FreeCox k} {d : Fin k} (h : C.graph.step x d = some b) :
    A (C.view x) d = A (C.view b) d := by
  have hx := (graph_step_eq_some h).1
  have hb := graph_step_mem h
  have hs := toGraph_step h hx hb
  exact (hC.isMaxFM hA hik).symm _ _ _ hs

/-- Lemma 2 of [GHS14]: on a loopy graph every node is saturated. -/
theorem Good.load_eq_one {A : ECAlg k} (hA : A.SolvesLoopy) (hC : C.Good i) (hik : i + 1 < k)
    {x : FreeCox k} (hx : x ∈ C.T) : load C.graph (fun a => A (C.view a)) x = 1 := by
  obtain ⟨d, hd⟩ := hC.exists_loop hik hx
  have hs := toGraph_step hd hx hx
  have h1 : load C.toGraph (fun a => A (C.view a.1)) ⟨x, hx⟩ = 1 := by
    have := (hC.isMaxFM hA hik).maximal _ _ _ hs; tauto
  rw [← h1]
  unfold load
  simp only [toGraph, ColouredGraph.restrict_step_isSome]

end Cfg

end Podc.LinearInDeltaLB
