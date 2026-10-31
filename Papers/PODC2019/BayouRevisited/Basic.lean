import Papers.PODC2019.BayouRevisited.Model

/-!
# Basic lemmas about local runs, local views and valid executions
-/

namespace Podc.BayouRevisited.Impl

variable {n : ℕ} {Op Val : Type} (I : Impl n Op Val)

/-! ### Local runs -/

lemma foldl_lstep_snd (i : Fin n) (δ : List I.Input) (p : I.State × List (Eff I.Msg Val)) :
    ∃ X, (δ.foldl (I.lstep i) p).2 = p.2 ++ X ∧ X.length = δ.length := by
  induction δ generalizing p with
  | nil => exact ⟨[], by simp⟩
  | cons x δ ih =>
    obtain ⟨X, hX, hl⟩ := ih (I.lstep i p x)
    refine ⟨(I.step i p.2.length p.1 x).2 :: X, ?_, by simp [hl]⟩
    rw [List.foldl_cons, hX]
    simp [lstep]

lemma lrun_append (i : Fin n) (ℓ δ : List I.Input) :
    I.lrun i (ℓ ++ δ) = δ.foldl (I.lstep i) (I.lrun i ℓ) := by
  simp [lrun, List.foldl_append]

@[simp] lemma leffs_length (i : Fin n) (ℓ : List I.Input) : (I.leffs i ℓ).length = ℓ.length := by
  obtain ⟨X, hX, hl⟩ := I.foldl_lstep_snd i ℓ (I.init i, [])
  simp [leffs, lrun, hX, hl]

lemma leffs_append (i : Fin n) (ℓ δ : List I.Input) :
    ∃ X, I.leffs i (ℓ ++ δ) = I.leffs i ℓ ++ X ∧ X.length = δ.length := by
  rw [leffs, lrun_append]; exact I.foldl_lstep_snd i δ _

lemma leffs_prefix (i : Fin n) (ℓ δ : List I.Input) : I.leffs i ℓ <+: I.leffs i (ℓ ++ δ) := by
  obtain ⟨X, hX, -⟩ := I.leffs_append i ℓ δ
  rw [hX]; exact List.prefix_append _ _

lemma lstate_concat (i : Fin n) (ℓ : List I.Input) (x : I.Input) :
    I.lstate i (ℓ ++ [x]) = (I.stepAt i ℓ x).1 := by
  have := I.leffs_length i ℓ
  simp only [leffs] at this
  simp [lstate, lrun_append, lstep, stepAt, this]

lemma leffs_concat (i : Fin n) (ℓ : List I.Input) (x : I.Input) :
    I.leffs i (ℓ ++ [x]) = I.leffs i ℓ ++ [(I.stepAt i ℓ x).2] := by
  have := I.leffs_length i ℓ
  simp only [leffs] at this
  simp [leffs, lrun_append, lstep, stepAt, lstate, this]

@[simp] lemma leffs_nil (i : Fin n) : I.leffs i [] = [] := rfl

@[simp] lemma lstate_nil (i : Fin n) : I.lstate i [] = I.init i := rfl

lemma rbCasts_prefix (i : Fin n) (ℓ δ : List I.Input) :
    I.rbCasts i ℓ <+: I.rbCasts i (ℓ ++ δ) := by
  obtain ⟨X, hX, -⟩ := I.leffs_append i ℓ δ
  simp only [rbCasts, hX, List.flatMap_append]; exact List.prefix_append _ _

lemma tobCasts_prefix (i : Fin n) (ℓ δ : List I.Input) :
    I.tobCasts i ℓ <+: I.tobCasts i (ℓ ++ δ) := by
  obtain ⟨X, hX, -⟩ := I.leffs_append i ℓ δ
  simp only [tobCasts, hX, List.flatMap_append]; exact List.prefix_append _ _

lemma rbCasts_getElem?_append {i : Fin n} {ℓ : List I.Input} {k : ℕ} {m : I.Msg}
    (h : (I.rbCasts i ℓ)[k]? = some m) (δ : List I.Input) :
    (I.rbCasts i (ℓ ++ δ))[k]? = some m := by
  obtain ⟨Y, hY⟩ := I.rbCasts_prefix i ℓ δ
  rw [← hY, List.getElem?_append_left]; exact h
  exact (List.getElem?_eq_some_iff.1 h).1

lemma tobCasts_getElem?_append {i : Fin n} {ℓ : List I.Input} {k : ℕ} {m : I.Msg}
    (h : (I.tobCasts i ℓ)[k]? = some m) (δ : List I.Input) :
    (I.tobCasts i (ℓ ++ δ))[k]? = some m := by
  obtain ⟨Y, hY⟩ := I.tobCasts_prefix i ℓ δ
  rw [← hY, List.getElem?_append_left]; exact h
  exact (List.getElem?_eq_some_iff.1 h).1

lemma lresp_append {i : Fin n} {ℓ : List I.Input} {c : ℕ} {v : Val}
    (h : I.lresp i ℓ c = some v) (δ : List I.Input) : I.lresp i (ℓ ++ δ) c = some v := by
  obtain ⟨X, hX, -⟩ := I.leffs_append i ℓ δ
  have hc : c ≤ (I.leffs i ℓ).length := by
    by_contra hc
    simp only [lresp] at h
    rw [List.drop_eq_nil_of_le (by omega)] at h
    simp at h
  simp only [lresp, hX, List.drop_append_of_le_length hc, List.findSome?_append]
  simp only [lresp] at h
  rw [h]; rfl

/-! ### Local views of global executions -/

/-- The actions of replica `i` processing the local inputs `δ`. -/
def atR (i : Fin n) (δ : List I.Input) : List I.Act := δ.map fun x => (i, x)

@[simp] lemma loc_nil (i : Fin n) : I.loc i [] = [] := rfl

@[simp] lemma loc_append (i : Fin n) (P Q : List I.Act) :
    I.loc i (P ++ Q) = I.loc i P ++ I.loc i Q := by
  simp [loc, List.filterMap_append]

lemma loc_singleton (i j : Fin n) (x : I.Input) :
    I.loc i [(j, x)] = if j = i then [x] else [] := by
  by_cases h : j = i <;> simp [loc, h]

@[simp] lemma loc_atR_self (i : Fin n) (δ : List I.Input) : I.loc i (I.atR i δ) = δ := by
  induction δ with
  | nil => rfl
  | cons x δ ih =>
    simp only [atR, List.map_cons] at ih ⊢
    rw [show (i, x) :: List.map (fun x => (i, x)) δ = [(i, x)] ++ List.map (fun x => (i, x)) δ
      from rfl, loc_append, ih, loc_singleton, if_pos rfl]; rfl

lemma loc_atR_ne {i j : Fin n} (h : i ≠ j) (δ : List I.Input) : I.loc j (I.atR i δ) = [] := by
  simp [loc, atR, List.filterMap_eq_nil_iff, h]

lemma loc_atR (i j : Fin n) (δ : List I.Input) :
    I.loc j (I.atR i δ) = if i = j then δ else [] := by
  split_ifs with h
  · subst h; simp
  · exact I.loc_atR_ne h δ

@[simp] lemma atR_append (i : Fin n) (δ δ' : List I.Input) :
    I.atR i (δ ++ δ') = I.atR i δ ++ I.atR i δ' := by simp [atR]

@[simp] lemma atR_length (i : Fin n) (δ : List I.Input) : (I.atR i δ).length = δ.length := by
  simp [atR]

lemma atR_take (i : Fin n) (δ : List I.Input) (t : ℕ) :
    (I.atR i δ).take t = I.atR i (δ.take t) := by simp [atR, List.map_take]

lemma tobSeq_append (i : Fin n) (P Q : List I.Act) :
    I.tobSeq i (P ++ Q) = I.tobSeq i P ++ (I.loc i Q).filterMap LIn.tobId := by
  simp [tobSeq, List.filterMap_append]

/-! ### Valid executions -/

variable {I} {S : ACTSpec Op Val}

lemma valid_nil : I.Valid S [] := fun t h => absurd h (by simp)

lemma valid_append_iff {P Q : List I.Act} :
    I.Valid S (P ++ Q) ↔
      I.Valid S P ∧ ∀ t (h : t < Q.length), I.Enabled S (P ++ Q.take t) Q[t] := by
  constructor
  · intro hV
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have := hV t (by simp; omega)
      rwa [List.take_append_of_le_length ht.le, List.getElem_append_left ht] at this
    · have := hV (P.length + t) (by simp; omega)
      rw [List.take_append, List.take_of_length_le (by omega),
        List.getElem_append_right (by omega)] at this
      simpa using this
  · rintro ⟨hP, hQ⟩ t ht
    by_cases h : t < P.length
    · have := hP t h
      rwa [List.take_append_of_le_length h.le, List.getElem_append_left h]
    · have h' : t - P.length < Q.length := by simp at ht; omega
      have := hQ (t - P.length) h'
      rw [List.take_append, List.take_of_length_le (by omega), List.getElem_append_right (by omega)]
      exact this

lemma Valid.of_append {P Q : List I.Act} (h : I.Valid S (P ++ Q)) : I.Valid S P :=
  (valid_append_iff.1 h).1

lemma Valid.of_prefix {P Q : List I.Act} (h : I.Valid S Q) (hp : P <+: Q) : I.Valid S P := by
  obtain ⟨R, rfl⟩ := hp; exact h.of_append

lemma valid_concat {P : List I.Act} {a : I.Act} (hP : I.Valid S P) (ha : I.Enabled S P a) :
    I.Valid S (P ++ [a]) :=
  valid_append_iff.2 ⟨hP, fun t ht => by
    simp only [List.length_singleton, Nat.lt_one_iff] at ht; subst ht; simpa using ha⟩

lemma valid_atR {P : List I.Act} {i : Fin n} {δ : List I.Input} (hP : I.Valid S P)
    (hδ : ∀ t (h : t < δ.length), I.Enabled S (P ++ I.atR i (δ.take t)) (i, δ[t])) :
    I.Valid S (P ++ I.atR i δ) :=
  valid_append_iff.2 ⟨hP, fun t ht => by
    rw [atR_take]; simpa [atR] using hδ t (by simpa using ht)⟩

end Podc.BayouRevisited.Impl
