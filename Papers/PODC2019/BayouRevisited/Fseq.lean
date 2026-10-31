import Papers.PODC2019.BayouRevisited.Framework

/-!
# The append-only sequence `F_seq` (Figure 3)

`append(s)` returns `ok`; `read` returns the concatenation `s₁ · s₂ · … · sₙ` of the arguments of
the `append` events of the context, ordered by arbitration. The paper indexes the appends by
`rank(appends(E), ar, e) = i` for `1 ≤ i ≤ n`; since `rank` counts the *strict* predecessors it
is `0`-based, so we use `rank = i - 1` (that is, `i` ranges over `0, …, n-1`).
The alphabet `$ = {a, …, z}` is generalised to an arbitrary type `α`.
-/

namespace Podc.BayouRevisited

/-- Operations of `F_seq`. -/
inductive SeqOp (α : Type)
  | append (s : List α)
  | read
  deriving DecidableEq

/-- Return values of `F_seq`. -/
inductive SeqVal (α : Type)
  | ok
  | word (w : List α)
  deriving DecidableEq

variable {α : Type}

/-- The argument of an `append` (empty for `read`). -/
def SeqOp.arg : SeqOp α → List α
  | .append s => s
  | .read => []

/-- `appends(E) = {e ∈ E : ∃ v, op(e) = append(v)}`. -/
def appends {Ev : Type} (C : Context Ev (SeqOp α)) : Set Ev :=
  {e | e ∈ C.E ∧ ∃ s, C.op e = .append s}

/-- The argument of the append of rank `i` (or `[]` if there is none). -/
noncomputable def wordAt {Ev : Type} (C : Context Ev (SeqOp α)) (i : ℕ) : List α :=
  open Classical in
  if h : ∃ e ∈ appends C, rank (appends C) C.ar e = i then (C.op h.choose).arg else []

/-- The replicated data type `F_seq` of Figure 3. -/
noncomputable def Fseq : RDT (SeqOp α) (SeqVal α) := fun {_} op C =>
  match op with
  | .append _ => .ok
  | .read => .word ((List.range (appends C).ncard).flatMap (wordAt C))

/-- `lvlmap_seq`: both operations may be invoked with both levels (Section 6). -/
def lvlmapSeq : SeqOp α → Set Level := fun _ => Set.univ

/-- The ACT specification `(F_seq, lvlmap_seq)` of Theorem 5. -/
noncomputable def seqSpec (α : Type) : ACTSpec (SeqOp α) (SeqVal α) := ⟨Fseq, lvlmapSeq⟩

section lemmas

variable {Ev : Type} (C : Context Ev (SeqOp α))

lemma wordAt_of_rank {e : Ev} (he : e ∈ appends C) (i : ℕ) (hr : rank (appends C) C.ar e = i)
    (huniq : ∀ e' ∈ appends C, rank (appends C) C.ar e' = i → e' = e) :
    wordAt C i = (C.op e).arg := by
  classical
  have h : ∃ e ∈ appends C, rank (appends C) C.ar e = i := ⟨e, he, hr⟩
  rw [wordAt, dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  rw [huniq _ h1 h2]

lemma Fseq_read_empty (h : appends C = ∅) : Fseq .read C = .word [] := by
  simp [Fseq, h]

lemma Fseq_read_single {e : Ev} (h : appends C = {e}) (hirr : ¬ C.ar e e) :
    Fseq .read C = .word (C.op e).arg := by
  have hr : rank (appends C) C.ar e = 0 := by
    simp only [rank, h, Set.mem_singleton_iff]
    convert Set.ncard_empty Ev
    ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro rfl; exact hirr
  have hw : wordAt C 0 = (C.op e).arg :=
    wordAt_of_rank C (by simp [h]) 0 hr (by intro e' he' _; simpa [h] using he')
  simp [Fseq, h, hw]

lemma Fseq_read_pair {e₁ e₂ : Ev} (hne : e₁ ≠ e₂) (h : appends C = {e₁, e₂})
    (h12 : C.ar e₁ e₂) (h21 : ¬ C.ar e₂ e₁) (h1 : ¬ C.ar e₁ e₁) (h2 : ¬ C.ar e₂ e₂) :
    Fseq .read C = .word ((C.op e₁).arg ++ (C.op e₂).arg) := by
  have r1 : rank (appends C) C.ar e₁ = 0 := by
    simp only [rank, h]
    convert Set.ncard_empty Ev
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro (rfl | rfl) <;> assumption
  have r2 : rank (appends C) C.ar e₂ = 1 := by
    simp only [rank, h]
    convert Set.ncard_singleton e₁
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨rfl | rfl, hx⟩
      · rfl
      · exact absurd hx h2
    · rintro rfl; exact ⟨Or.inl rfl, h12⟩
  have hc : (appends C).ncard = 2 := by rw [h, Set.ncard_pair hne]
  have w0 : wordAt C 0 = (C.op e₁).arg :=
    wordAt_of_rank C (by simp [h]) 0 r1 (by
      intro e' he' hr; rw [h] at he'
      rcases he' with rfl | rfl
      · rfl
      · rw [r2] at hr; exact absurd hr one_ne_zero)
  have w1 : wordAt C 1 = (C.op e₂).arg :=
    wordAt_of_rank C (by simp [h]) 1 r2 (by
      intro e' he' hr; rw [h] at he'
      rcases he' with rfl | rfl
      · rw [r1] at hr; exact absurd hr zero_ne_one
      · rfl)
  simp only [Fseq, hc]
  simp [List.range_succ, w0, w1]

/-- `read` is a read-only operation of `F_seq`. -/
lemma Fseq_read_readOnly : RDT.IsReadOnly (Fseq (α := α)) .read := by
  intro Ev op' C e _ he
  cases op' with
  | append s => rfl
  | read =>
    have hA : appends { C with E := C.E \ {e} } = appends C := by
      ext x
      simp only [appends, Set.mem_diff, Set.mem_singleton_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨hx, _⟩, hs⟩; exact ⟨hx, hs⟩
      · rintro ⟨hx, s, hs⟩
        refine ⟨⟨hx, ?_⟩, s, hs⟩
        rintro rfl; rw [he] at hs; cases hs
    have hW : wordAt { C with E := C.E \ {e} } = wordAt C := by
      funext i; unfold wordAt; revert hA
      generalize appends { C with E := C.E \ {e} } = A
      rintro rfl; rfl
    simp only [Fseq, hW, hA]

open Classical in
/-- `F_seq` on a context with at most two appends `append [x]` and `append [y]`. -/
lemma Fseq_read_two {e₁ e₂ : Ev} {x y : α} (hne : e₁ ≠ e₂) (hA : appends C ⊆ {e₁, e₂})
    (ho₁ : C.op e₁ = .append [x]) (ho₂ : C.op e₂ = .append [y]) (hxy : x ≠ y)
    (htot : IsStrictTotal C.ar) :
    (Fseq .read C = .word [x, y] → e₁ ∈ appends C ∧ e₂ ∈ appends C ∧ C.ar e₁ e₂) ∧
    (Fseq .read C = .word [y] → e₂ ∈ appends C ∧ e₁ ∉ appends C) ∧
    (e₁ ∈ appends C → e₂ ∈ appends C →
      Fseq .read C = if C.ar e₁ e₂ then SeqVal.word [x, y] else SeqVal.word [y, x]) := by
  have hcases : appends C = {e₁, e₂} ∨ appends C = {e₁} ∨ appends C = {e₂} ∨ appends C = ∅ := by
    by_cases h1 : e₁ ∈ appends C <;> by_cases h2 : e₂ ∈ appends C
    · left; apply Set.Subset.antisymm hA; intro z hz; rcases hz with rfl | rfl <;> assumption
    · right; left; ext z; constructor
      · intro hz; rcases hA hz with rfl | rfl
        · rfl
        · exact absurd hz h2
      · rintro rfl; exact h1
    · right; right; left; ext z; constructor
      · intro hz; rcases hA hz with rfl | rfl
        · exact absurd hz h1
        · rfl
      · rintro rfl; exact h2
    · right; right; right; ext z; simp only [Set.mem_empty_iff_false, iff_false]
      intro hz; rcases hA hz with rfl | rfl <;> contradiction
  have hpair : appends C = {e₁, e₂} →
      Fseq .read C = if C.ar e₁ e₂ then SeqVal.word [x, y] else SeqVal.word [y, x] := by
    intro h
    split_ifs with h12
    · have h21 : ¬ C.ar e₂ e₁ := fun h21 => htot.irrefl _ (htot.trans _ _ _ h12 h21)
      rw [Fseq_read_pair C hne h h12 h21 (htot.irrefl _) (htot.irrefl _), ho₁, ho₂]; rfl
    · have h21 : C.ar e₂ e₁ := (htot.total _ _ hne).resolve_left h12
      rw [show ({e₁, e₂} : Set Ev) = {e₂, e₁} from Set.pair_comm _ _] at h
      rw [Fseq_read_pair C (Ne.symm hne) h h21 h12 (htot.irrefl _) (htot.irrefl _), ho₁, ho₂]; rfl
  have hxy' : ∀ (u v : List α), SeqVal.word u = SeqVal.word v → u = v := fun u v h => by
    cases h; rfl
  refine ⟨fun hv => ?_, fun hv => ?_, fun h1 h2 => hpair ?_⟩
  · rcases hcases with h | h | h | h
    · refine ⟨by rw [h]; simp, by rw [h]; simp, ?_⟩
      rw [hpair h] at hv
      split_ifs at hv with h12
      · exact h12
      · have := hxy' _ _ hv; simp [SeqOp.arg] at this; exact absurd this.1 (Ne.symm hxy)
    · rw [Fseq_read_single C h (htot.irrefl _), ho₁] at hv
      have := hxy' _ _ hv; simp [SeqOp.arg] at this
    · rw [Fseq_read_single C h (htot.irrefl _), ho₂] at hv
      have := hxy' _ _ hv; simp [SeqOp.arg] at this
    · rw [Fseq_read_empty C h] at hv; have := hxy' _ _ hv; simp [SeqOp.arg] at this
  · rcases hcases with h | h | h | h
    · rw [hpair h] at hv
      split_ifs at hv <;> (have := hxy' _ _ hv; simp [SeqOp.arg] at this)
    · rw [Fseq_read_single C h (htot.irrefl _), ho₁] at hv
      have := hxy' _ _ hv; simp [SeqOp.arg] at this; exact absurd this hxy
    · refine ⟨by rw [h]; simp, by rw [h]; simpa using hne⟩
    · rw [Fseq_read_empty C h] at hv; have := hxy' _ _ hv; simp [SeqOp.arg] at this
  · apply Set.Subset.antisymm hA; intro z hz; rcases hz with rfl | rfl <;> assumption

end lemmas

end Podc.BayouRevisited
