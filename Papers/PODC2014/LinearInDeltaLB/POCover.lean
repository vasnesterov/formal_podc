import Papers.PODC2014.LinearInDeltaLB.FreeTree
import Papers.PODC2014.LinearInDeltaLB.Defs

/-!
# The PO-view of an EC-graph (Section 5.1)

The simulation EC ⇝ PO of Section 5.1 turns every edge `{u, v}` of colour `c` of an EC-graph into
the two directed edges `(u, v)` and `(v, u)` of colour `c`; a loop becomes a directed loop. The
universal cover of the resulting PO-graph, rooted at `a`, is the set `cover G a ⊆ F_k` of reduced
words that can be followed letter by letter from `a` (letters `c` and `c⁻¹` both follow the
`c`-edge). We prove that `poWalk` is a partial right action of `F_k` (`poWalk_mul`), so the cover
re-rooted at `w` is the cover of the endpoint of `w` (`inv_smul_cover`), that covers of loopy
graphs are loopy (`isLoopyF_cover`), that the cover only depends on the EC-view
(`cover_tGraph_view`), and that its radius-`t` ball only depends on the radius-`t` ball of the
view (`cover_view_inter_ballF`).
-/

namespace Podc.LinearInDeltaLB

open Cslib.ColourSystem FreeGroup Pointwise

variable {k : ℕ} {α : Type*} (G : ColouredGraph k α)

/-- Follow a word letter by letter (each letter `(c, b)` follows the `c`-edge). -/
def walkL : α → List (Fin k × Bool) → Option α
  | a, [] => some a
  | a, l :: L => (G.step a l.1).bind (fun b => walkL b L)

@[simp] theorem walkL_nil (a : α) : walkL G a [] = some a := rfl

@[simp] theorem walkL_cons (a : α) (l : Fin k × Bool) (L : List (Fin k × Bool)) :
    walkL G a (l :: L) = (G.step a l.1).bind (fun b => walkL G b L) := rfl

theorem walkL_append (a : α) (L₁ L₂ : List (Fin k × Bool)) :
    walkL G a (L₁ ++ L₂) = (walkL G a L₁).bind (walkL G · L₂) := by
  induction L₁ generalizing a with
  | nil => simp
  | cons l L ih =>
    simp only [List.cons_append, walkL_cons, ih]
    cases G.step a l.1 <;> simp

theorem walkL_red_step {L L' : List (Fin k × Bool)} (h : FreeGroup.Red.Step L L') {a b : α}
    (hw : walkL G a L = some b) : walkL G a L' = some b := by
  cases h with
  | @not L₁ L₂ x c =>
    rw [walkL_append] at hw ⊢
    obtain ⟨d, hd, hw⟩ := Option.bind_eq_some_iff.1 hw
    rw [hd, Option.bind_some]
    simp only [walkL_cons] at hw
    obtain ⟨e, he, hw⟩ := Option.bind_eq_some_iff.1 hw
    obtain ⟨f, hf, hw⟩ := Option.bind_eq_some_iff.1 hw
    have := G.symm _ _ _ he
    rw [this] at hf
    cases hf
    exact hw

theorem walkL_red {L L' : List (Fin k × Bool)} (h : FreeGroup.Red L L') {a b : α}
    (hw : walkL G a L = some b) : walkL G a L' = some b := by
  induction h with
  | refl => exact hw
  | tail _ h2 ih => exact walkL_red_step G h2 ih

theorem walkL_invRev {L : List (Fin k × Bool)} {a b : α} (h : walkL G a L = some b) :
    walkL G b (FreeGroup.invRev L) = some a := by
  induction L generalizing a with
  | nil => simp only [walkL_nil, Option.some.injEq] at h; subst h; rfl
  | cons l L ih =>
    rw [walkL_cons] at h
    obtain ⟨c, hc, hw⟩ := Option.bind_eq_some_iff.1 h
    rw [FreeGroup.invRev_cons, walkL_append, ih hw, Option.bind_some]
    simp [FreeGroup.invRev, G.symm _ _ _ hc]

/-- Follow the reduced word of `w` letter by letter. -/
def poWalk (a : α) (w : FG k) : Option α := walkL G a w.toWord

@[simp] theorem poWalk_one (a : α) : poWalk G a 1 = some a := by
  simp [poWalk]

@[simp] theorem poWalk_ltr (a : α) (l : Fin k × Bool) : poWalk G a (ltr l) = G.step a l.1 := by
  simp only [poWalk, toWord_ltr, walkL_cons, walkL_nil]
  cases G.step a l.1 <;> rfl

theorem poWalk_mul_of_some {a b e : α} {w u : FG k} (h1 : poWalk G a w = some b)
    (h2 : poWalk G b u = some e) : poWalk G a (w * u) = some e := by
  unfold poWalk at *
  rw [FreeGroup.toWord_mul]
  apply walkL_red G (FreeGroup.reduce.red)
  rw [walkL_append, h1, Option.bind_some, h2]

theorem poWalk_inv {a b : α} {w : FG k} (h : poWalk G a w = some b) : poWalk G b w⁻¹ = some a := by
  unfold poWalk at *
  rw [FreeGroup.toWord_inv]
  exact walkL_invRev G h

/-- `poWalk` is a partial right action of `F_k`. -/
theorem poWalk_mul {a b : α} {w : FG k} (h : poWalk G a w = some b) (u : FG k) :
    poWalk G a (w * u) = poWalk G b u := by
  cases hu : poWalk G b u with
  | some e => exact poWalk_mul_of_some G h hu
  | none =>
    cases hwu : poWalk G a (w * u) with
    | none => rfl
    | some e =>
      have := poWalk_mul_of_some G (poWalk_inv G h) hwu
      rw [inv_mul_cancel_left, hu] at this
      cases this

theorem poWalk_mul_ltr {a b : α} {w : FG k} (h : poWalk G a w = some b) (l : Fin k × Bool) :
    poWalk G a (w * ltr l) = G.step b l.1 := by
  rw [poWalk_mul G h, poWalk_ltr]

/-- The PO-view of `a`: the universal cover of the PO-graph of `G`, rooted at `a`. -/
def cover (a : α) : Set (FG k) := {w | (poWalk G a w).isSome}

theorem mem_cover {a : α} {w : FG k} : w ∈ cover G a ↔ ∃ b, poWalk G a w = some b := by
  simp [cover, Option.isSome_iff_exists]

theorem one_mem_cover (a : α) : (1 : FG k) ∈ cover G a := by simp [cover]

/-- Re-rooting the PO-view at `w` gives the PO-view of the endpoint of `w`. -/
theorem inv_smul_cover {a b : α} {w : FG k} (h : poWalk G a w = some b) :
    w⁻¹ • cover G a = cover G b := by
  ext u
  rw [Set.mem_inv_smul_set_iff]
  simp only [cover, Set.mem_ofPred_eq, smul_eq_mul, poWalk_mul G h]

theorem mul_ltr_mem_cover {a b : α} {w : FG k} (h : poWalk G a w = some b) (l : Fin k × Bool) :
    w * ltr l ∈ cover G a ↔ (G.step b l.1).isSome := by
  simp only [cover, Set.mem_ofPred_eq, poWalk_mul_ltr G h]

/-- A set `U ⊆ F_k` is loopy if every node `w ∈ U` has a neighbour `w l ∈ U` with the same
re-rooted view (`(w l)⁻¹ U = w⁻¹ U`): the lift of a loop of the factor graph. -/
def IsLoopyF (U : Set (FG k)) : Prop :=
  ∀ w ∈ U, ∃ l, w * ltr l ∈ U ∧ (w * ltr l)⁻¹ • U = w⁻¹ • U

theorem isLoopyF_cover (hG : IsLoopy G) (a : α) : IsLoopyF (cover G a) := by
  intro w hw
  obtain ⟨b, hb⟩ := (mem_cover G).1 hw
  obtain ⟨c, hc⟩ := hG b
  have h1 : poWalk G a (w * ltr (c, true)) = some b := by rw [poWalk_mul_ltr G hb]; exact hc
  refine ⟨(c, true), (mem_cover G).2 ⟨b, h1⟩, ?_⟩
  rw [inv_smul_cover G h1, inv_smul_cover G hb]

theorem IsLoopyF.inv_smul {U : Set (FG k)} (hU : IsLoopyF U) {w : FG k} (_hw : w ∈ U) :
    IsLoopyF (w⁻¹ • U) := by
  intro u hu
  rw [Set.mem_inv_smul_set_iff, smul_eq_mul] at hu
  obtain ⟨l, hl, he⟩ := hU _ hu
  refine ⟨l, ?_, ?_⟩
  · rw [Set.mem_inv_smul_set_iff, smul_eq_mul, ← mul_assoc]; exact hl
  · rw [smul_smul, smul_smul, ← mul_inv_rev, ← mul_inv_rev, ← mul_assoc, he]

/-! ### The PO-view only depends on the EC-view -/

theorem tGraph_step_view {a : α} {s : FreeCox k} {b : α} (hs : G.walk a s = some b) (c : Fin k) :
    (tGraph (G.view a) fun _ => ∅).step s c =
      if (G.step b c).isSome then some (s * FreeCox.gen c) else none := by
  have hsV : s ∈ G.view a := (G.mem_view).2 ⟨b, hs⟩
  have e : s * FreeCox.gen c ∈ G.view a ↔ (G.step b c).isSome := by
    rw [ColouredGraph.mem_view, G.walk_mul_gen hs, Option.isSome_iff_exists]
  by_cases h : (G.step b c).isSome
  · simp only [h, ↓reduceIte]; exact tGraph_step_of_mem hsV (e.2 h)
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
    exact tGraph_step_of_not_mem hsV (fun h' => h (e.1 h')) (by simp)

theorem walkL_tGraph_view {a : α} {s : FreeCox k} {b : α} (hs : G.walk a s = some b)
    (L : List (Fin k × Bool)) :
    (walkL (tGraph (G.view a) fun _ => ∅) s L).isSome = (walkL G b L).isSome := by
  induction L generalizing s b with
  | nil => rfl
  | cons l L ih =>
    simp only [walkL_cons]
    rw [tGraph_step_view G hs]
    by_cases h : (G.step b l.1).isSome
    · simp only [h, ↓reduceIte, Option.bind_some]
      obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 h
      rw [hb', Option.bind_some]
      exact ih (by rw [G.walk_mul_gen hs, hb'])
    · simp only [h, ↓reduceIte, Bool.false_eq_true, Option.bind_none]
      rw [Option.not_isSome_iff_eq_none] at h
      rw [h, Option.bind_none]; rfl

/-- The PO-view of `a` is the PO-view of the root of the EC-view `Γ_k(view a)`. -/
theorem cover_tGraph_view (a : α) : cover (tGraph (G.view a) fun _ => ∅) 1 = cover G a := by
  ext w
  simp only [cover, Set.mem_ofPred_eq, poWalk]
  rw [walkL_tGraph_view G (G.walk_one a) w.toWord]

/-- The radius-`t` ball of the PO-view of `Γ_k(V)` only depends on the radius-`t` ball of `V`. -/
theorem walkL_tGraph_congr {V V' : Set (FreeCox k)} {t : ℕ} (h : ball V t = ball V' t)
    (L : List (Fin k × Bool)) (s : FreeCox k) (hs : FreeCox.len s + L.length ≤ t) :
    walkL (tGraph V fun _ => ∅) s L = walkL (tGraph V' fun _ => ∅) s L := by
  induction L generalizing s with
  | nil => rfl
  | cons l L ih =>
    simp only [walkL_cons, List.length_cons] at hs ⊢
    have h1 : s ∈ V ↔ s ∈ V' := mem_iff_of_ball_eq h (by omega)
    have h2 : s * FreeCox.gen l.1 ∈ V ↔ s * FreeCox.gen l.1 ∈ V' :=
      mem_iff_of_ball_eq h (by have := FreeCox.len_mul_gen_le s l.1; omega)
    rw [← tGraph_step_congr h1 h2 Iff.rfl]
    cases hst : (tGraph V fun _ => ∅).step s l.1 with
    | none => rfl
    | some b =>
      simp only [Option.bind_some]
      rcases (tGraph_step_eq_some hst).2 with ⟨-, rfl⟩ | ⟨-, hL, -⟩
      · exact ih _ (by have := FreeCox.len_mul_gen_le s l.1; omega)
      · simp at hL

theorem cover_inter_ballF {V V' : Set (FreeCox k)} {t : ℕ} (h : ball V t = ball V' t) :
    cover (tGraph V fun _ => ∅) 1 ∩ ballF k t = cover (tGraph V' fun _ => ∅) 1 ∩ ballF k t := by
  ext w
  simp only [Set.mem_inter_iff, cover, Set.mem_ofPred_eq, mem_ballF, poWalk]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, h2⟩
  · rwa [← walkL_tGraph_congr h _ 1 (by simpa [FreeGroup.norm] using h2)]
  · rwa [walkL_tGraph_congr h _ 1 (by simpa [FreeGroup.norm] using h2)]

end Podc.LinearInDeltaLB
