import Papers.PODC2014.RandomizationTwoHop.Theorem2

/-!
# Walk languages: relabelling and truncation locality

Algorithm `A*` augments the labels by bit strings `b(v)` that are themselves functions of the
nodes' views. On walk languages this is `relabel f T`: every letter of a word is paired with `f`
of the sub-language at that position (`relabelWord`). For a 2-hop coloured graph, relabelling
the language of `v` by `f` gives the language of `v` in the graph relabelled by
`v ↦ (ℓ(v), f(L∞(v)))` (`lang_withLab_relabel`).

Truncation locality (`trunc_relabel_congr`): if `f` only looks at depth `d`, then the depth-`k`
truncation of `relabel f T` only depends on the depth-`d + k` truncation of `T`.
-/

namespace Podc.RandomizationTwoHop

open SimpleGraph

variable {L β : Type}

/-- Pair every letter of a word with `f` of the sub-language below that position. -/
def relabelWord (f : Set (List L) → β) : Set (List L) → List L → List (L × β)
  | _, [] => []
  | T, [a] => [(a, f T)]
  | T, a :: b :: w => (a, f T) :: relabelWord f (child T b) (b :: w)

/-- Relabel a language by `f`. -/
def relabel (f : Set (List L) → β) (T : Set (List L)) : Set (List (L × β)) :=
  relabelWord f T '' T

theorem length_relabelWord (f : Set (List L) → β) (T : Set (List L)) (w : List L) :
    (relabelWord f T w).length = w.length := by
  induction w generalizing T with
  | nil => rfl
  | cons a w ih =>
    cases w with
    | nil => rfl
    | cons b w => simp [relabelWord, ih]

theorem map_fst_relabelWord (f : Set (List L) → β) (T : Set (List L)) (w : List L) :
    (relabelWord f T w).map Prod.fst = w := by
  induction w generalizing T with
  | nil => rfl
  | cons a w ih =>
    cases w with
    | nil => rfl
    | cons b w => simp [relabelWord, ih]

theorem relabelWord_injective (f : Set (List L) → β) (T : Set (List L)) :
    Function.Injective (relabelWord f T) := fun w w' h => by
  rw [← map_fst_relabelWord f T w, ← map_fst_relabelWord f T w', h]

/-- Relabelling a 2-hop coloured graph by a function of the views. -/
theorem lang_withLab_relabel {X : LGraph L} (hX : X.TwoHop) (f : Set (List L) → β) (v : X.V) :
    ⟪X.withLab (fun v => (X.lab v, f (⟪X⟫ v)))⟫ v = relabel f (⟪X⟫ v) := by
  -- the word of a walk in the relabelled graph is the relabelled word
  have key : ∀ (v : X.V) (w : List L), InLang X.G X.lab v w →
      InLang X.G (fun v => (X.lab v, f (⟪X⟫ v))) v (relabelWord f (⟪X⟫ v) w) := by
    intro v w h
    induction h with
    | single v => exact InLang.single (G := X.G) (lG := fun v => (X.lab v, f (⟪X⟫ v))) v
    | @cons v u w hvu hw ih =>
      have h0 := InLang.head hw
      cases w with
      | nil => simp at h0
      | cons b w =>
        simp at h0; subst h0
        simp only [relabelWord]
        rw [child_lang hX hvu]
        exact InLang.cons hvu ih
  ext w'
  constructor
  · intro h
    change InLang X.G (fun v => (X.lab v, f (⟪X⟫ v))) v w' at h
    induction h with
    | single v => exact ⟨[X.lab v], InLang.single v, rfl⟩
    | @cons v u w hvu _ ih =>
      obtain ⟨w₀, hw₀, rfl⟩ := ih
      refine ⟨X.lab v :: w₀, InLang.cons hvu hw₀, ?_⟩
      have h0 := InLang.head hw₀
      cases w₀ with
      | nil => simp at h0
      | cons b w₀ =>
        simp at h0; subst h0
        simp only [relabelWord]
        rw [child_lang hX hvu]
  · rintro ⟨w, hw, rfl⟩
    exact key v w hw

/-- Relabelling commutes with truncation. -/
theorem trunc_relabel (f : Set (List L) → β) (k : ℕ) (T : Set (List L)) :
    trunc k (relabel f T) = relabelWord f T '' trunc k T := by
  ext w'
  simp only [trunc, relabel, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hl⟩
    exact ⟨w, ⟨hw, by rwa [length_relabelWord] at hl⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hl⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, by rwa [length_relabelWord]⟩

theorem trunc_child {m : ℕ} {T T' : Set (List L)} (h : trunc (m + 1) T = trunc (m + 1) T')
    (b : L) : trunc m (child T b) = trunc m (child T' b) := by
  ext w
  simp only [trunc, child, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hb, a, ha⟩, hl⟩
    have : a :: w ∈ trunc (m + 1) T := ⟨ha, by simp; omega⟩
    rw [h] at this
    exact ⟨⟨hb, a, this.1⟩, hl⟩
  · rintro ⟨⟨hb, a, ha⟩, hl⟩
    have : a :: w ∈ trunc (m + 1) T' := ⟨ha, by simp; omega⟩
    rw [← h] at this
    exact ⟨⟨hb, a, this.1⟩, hl⟩

/-- `f` only depends on the depth-`d` truncation. -/
def DepthLocal (d : ℕ) (f : Set (List L) → β) : Prop :=
  ∀ T T', trunc d T = trunc d T' → f T = f T'

theorem relabelWord_congr {d : ℕ} {f : Set (List L) → β} (hf : DepthLocal d f) :
    ∀ (w : List L) {T T' : Set (List L)},
      trunc (d + (w.length - 1)) T = trunc (d + (w.length - 1)) T' →
      relabelWord f T w = relabelWord f T' w
  | [], _, _, _ => rfl
  | [a], T, T', h => by
    simp only [relabelWord]; rw [hf T T' (trunc_eq_of_le (by simp) h)]
  | a :: b :: w, T, T', h => by
    simp only [relabelWord]
    rw [hf T T' (trunc_eq_of_le (by simp) h)]
    congr 1
    apply relabelWord_congr hf (b :: w)
    apply trunc_child
    simpa [Nat.add_assoc] using h

/-- **Truncation locality of relabelling.** -/
theorem trunc_relabel_congr {d k : ℕ} {f : Set (List L) → β} (hf : DepthLocal d f)
    {T T' : Set (List L)} (h : trunc (d + k) T = trunc (d + k) T') :
    trunc k (relabel f T) = trunc k (relabel f T') := by
  rw [trunc_relabel, trunc_relabel, trunc_eq_of_le (by omega) h]
  apply Set.image_congr
  rintro w ⟨-, hl⟩
  exact relabelWord_congr hf w (trunc_eq_of_le (by omega) h)

theorem DepthLocal.mono {d d' : ℕ} (hdd : d ≤ d') {f : Set (List L) → β} (hf : DepthLocal d f) :
    DepthLocal d' f := fun _ _ h => hf _ _ (trunc_eq_of_le hdd h)

end Podc.RandomizationTwoHop
