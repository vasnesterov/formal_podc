import Papers.PODC2014.WritableObjects.Algorithm
import Mathlib.Tactic.FinCases

/-!
# Lemma 4.8, part 1: the local queues of `recycle()` (Claims 4.9–4.13, 4.15)

Invariants of the local queue system `QS` of a process `p` (`QOK`):
all queues have length `2n+2` (Claim 4.11), `c_p[i]` is the number of occurrences of `i` in the
queues (Claim 4.12), and only indices owned by `p` occur in the queues and in `free_p`
(Claim 4.9).

The *hold* of an index (`Hold`) replaces the interval reasoning of Claims 4.15–4.17: number the
`updateQ` calls of `p` by *update times* `4r + o` (the update of queue `o` in the `r`-th
`recycle()`); an occurrence at position `j` of queue `o`, when `U o` updates of that queue have
been done, is dequeued at time `4 (U o + j) + o`. `Hold s U i γ` says that some occurrence of
`i` is dequeued at time `≥ γ`; then `i` is not added to `free_p` by updates at times `< γ`.
-/

namespace Podc.WritableObjects.WF

variable {n : ℕ}

/-- `x` if `p` owns it, else `⊥` (the value enqueued by `updateQ_p(·, x)`). -/
def ownF (p : Fin n) : Option (Idx n) → Option (Idx n)
  | some y => if y.1 = p then some y else none
  | none => none

lemma enq_q (p : Fin n) (o : Fin 4) (x : Option (Idx n)) (s : QS n) :
    (enq p o x s).q = Function.update s.q o (s.q o ++ [ownF p x]) := by
  unfold enq ownF; rcases x with _ | y
  · rfl
  · by_cases h : y.1 = p <;> simp [h]

lemma enq_cnt (p : Fin n) (o : Fin 4) (x : Option (Idx n)) (s : QS n) (i : Idx n) :
    (enq p o x s).cnt i = s.cnt i + if ownF p x = some i then 1 else 0 := by
  unfold enq ownF; rcases x with _ | y
  · simp
  · by_cases h : y.1 = p
    · by_cases hi : y = i
      · subst hi; simp [h]
      · simp [h, hi, Function.update_of_ne (Ne.symm hi)]
    · simp [h]

lemma enq_free (p : Fin n) (o : Fin 4) (x : Option (Idx n)) (s : QS n) :
    (enq p o x s).free = s.free := by
  unfold enq; rcases x with _ | y
  · rfl
  · by_cases h : y.1 = p <;> simp [h]

lemma deq_of_cons (o : Fin 4) (s : QS n) (a : Option (Idx n)) (rest : List (Option (Idx n)))
    (h : s.q o = a :: rest) :
    (deq o s).q = Function.update s.q o rest ∧
    (∀ i, (deq o s).cnt i = s.cnt i - if a = some i then 1 else 0) ∧
    (∀ i, i ∈ (deq o s).free ↔ i ∈ s.free ∨ (a = some i ∧ s.cnt i - 1 = 0)) := by
  unfold deq; rw [h]
  rcases a with _ | y
  · simp
  · refine ⟨rfl, fun i => ?_, fun i => ?_⟩
    · by_cases hi : y = i
      · subst hi; simp
      · simp [hi, Function.update_of_ne (Ne.symm hi)]
    · by_cases hc : s.cnt y - 1 = 0
      · simp only [hc, ite_true, Finset.mem_insert, Option.some.injEq]
        constructor
        · rintro (rfl | h); exacts [Or.inr ⟨rfl, hc⟩, Or.inl h]
        · rintro (h | ⟨rfl, _⟩); exacts [Or.inr h, Or.inl rfl]
      · simp only [hc, ite_false, Option.some.injEq]
        constructor
        · exact Or.inl
        · rintro (h | ⟨rfl, h⟩); exacts [h, absurd h hc]

/-- Number of occurrences of `i` in the four queues. -/
def occ (s : QS n) (i : Idx n) : ℕ :=
  (s.q 0).count (some i) + (s.q 1).count (some i) + (s.q 2).count (some i) +
    (s.q 3).count (some i)

/-- Invariants of the queue system of process `p` (Claims 4.9(a,b), 4.11, 4.12). -/
structure QOK (p : Fin n) (s : QS n) : Prop where
  len : ∀ o, (s.q o).length = 2 * n + 2
  cnt : ∀ i, s.cnt i = occ s i
  own : ∀ o x, some x ∈ s.q o → x.1 = p
  freeOwn : ∀ x ∈ s.free, x.1 = p

lemma occ_update (s : QS n) (o : Fin 4) (l : List (Option (Idx n))) (i : Idx n) :
    occ { s with q := Function.update s.q o l } i + (s.q o).count (some i) =
      occ s i + l.count (some i) := by
  unfold occ; fin_cases o <;> simp <;> omega

lemma QOK.erase {p : Fin n} {s : QS n} (h : QOK p s) (f : Idx n) :
    QOK p { s with free := s.free.erase f } :=
  ⟨h.len, h.cnt, h.own, fun x hx => h.freeOwn x (Finset.mem_of_mem_erase hx)⟩

lemma ownF_own {p : Fin n} {x : Option (Idx n)} {y : Idx n} (h : ownF p x = some y) :
    y.1 = p ∧ x = some y := by
  unfold ownF at h; rcases x with _ | z
  · simp at h
  · by_cases hz : z.1 = p <;> simp_all

/-- The result of `updateQ` on queue `o` (the queue is nonempty since it has length `2n+2`). -/
lemma upd_spec {p : Fin n} {s : QS n} (h : QOK p s) (o : Fin 4) (x : Option (Idx n)) :
    ∃ a rest, s.q o ++ [ownF p x] = a :: rest ∧
      (upd p o x s).q = Function.update s.q o rest ∧
      (∀ i, (upd p o x s).cnt i =
        s.cnt i + (if ownF p x = some i then 1 else 0) - (if a = some i then 1 else 0)) ∧
      (∀ i, i ∈ (upd p o x s).free ↔ i ∈ s.free ∨
        (a = some i ∧ s.cnt i + (if ownF p x = some i then 1 else 0) - 1 = 0)) := by
  have hl := h.len o
  obtain ⟨a, rest, har⟩ : ∃ a rest, s.q o ++ [ownF p x] = a :: rest := by
    cases hq : s.q o ++ [ownF p x] with
    | nil => simp at hq
    | cons a rest => exact ⟨a, rest, rfl⟩
  have hq : (enq p o x s).q o = a :: rest := by rw [enq_q]; simpa using har
  obtain ⟨h1, h2, h3⟩ := deq_of_cons o (enq p o x s) a rest hq
  refine ⟨a, rest, har, ?_, fun i => ?_, fun i => ?_⟩
  · unfold upd; rw [h1, enq_q]; simp
  · unfold upd; rw [h2, enq_cnt]
  · unfold upd; rw [h3, enq_free, enq_cnt]

lemma QOK.updQ {p : Fin n} {s : QS n} (h : QOK p s) (o : Fin 4) (x : Option (Idx n)) :
    QOK p (upd p o x s) := by
  obtain ⟨a, rest, har, hq, hc, hf⟩ := upd_spec h o x
  have hl := h.len o
  have hlen : rest.length = 2 * n + 2 := by
    have := congrArg List.length har; simp at this; omega
  refine ⟨fun o' => ?_, fun i => ?_, fun o' y hy => ?_, fun y hy => ?_⟩
  · rw [hq]; by_cases ho : o' = o
    · subst ho; simp [hlen]
    · simp [Function.update_of_ne ho, h.len]
  · rw [hc, h.cnt]
    have e1 := occ_update s o rest i
    have e2 : ((s.q o ++ [ownF p x]).count (some i)) = (a :: rest).count (some i) := by rw [har]
    simp only [List.count_append, List.count_cons] at e2
    have : occ (upd p o x s) i = occ { s with q := Function.update s.q o rest } i := by
      unfold occ; rw [hq]
    rw [this]
    by_cases ha : a = some i <;> by_cases hx : ownF p x = some i <;>
      simp_all [beq_iff_eq] <;> omega
  · rw [hq] at hy
    by_cases ho : o' = o
    · subst ho; simp only [Function.update_self] at hy
      have : some y ∈ s.q o' ++ [ownF p x] := by rw [har]; exact List.mem_cons_of_mem _ hy
      rcases List.mem_append.1 this with hy | hy
      · exact h.own o' y hy
      · exact (ownF_own (List.mem_singleton.1 hy).symm).1
    · exact h.own o' y (by simpa [Function.update_of_ne ho] using hy)
  · rcases (hf y).1 hy with hy | ⟨rfl, _⟩
    · exact h.freeOwn y hy
    · have : some y ∈ s.q o ++ [ownF p x] := by rw [har]; exact List.mem_cons_self
      rcases List.mem_append.1 this with hy | hy
      · exact h.own o y hy
      · exact (ownF_own (List.mem_singleton.1 hy).symm).1

/-! ## Holds -/

/-- Some occurrence of `i` in the queues is dequeued at an update time `≥ γ`, where `U o` is the
number of updates of queue `o` done so far. -/
def Hold (s : QS n) (U : Fin 4 → ℕ) (i : Idx n) (γ : ℕ) : Prop :=
  ∃ o j, (s.q o)[j]? = some (some i) ∧ γ ≤ 4 * (U o + j) + o

lemma Hold.mono {s : QS n} {U : Fin 4 → ℕ} {i : Idx n} {γ γ' : ℕ} (h : Hold s U i γ)
    (hγ : γ' ≤ γ) : Hold s U i γ' := by
  obtain ⟨o, j, h1, h2⟩ := h; exact ⟨o, j, h1, by omega⟩

lemma Hold.pos {s : QS n} {U : Fin 4 → ℕ} {i : Idx n} {γ : ℕ} (h : Hold s U i γ) :
    0 < occ s i := by
  obtain ⟨o, j, h1, -⟩ := h
  have hm : some i ∈ s.q o := List.mem_of_getElem? h1
  have : 0 < (s.q o).count (some i) := List.count_pos_iff.2 hm
  unfold occ; revert this; fin_cases o <;> intro this <;>
    (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at this ⊢; omega)

/-- An update of queue `o` at time `4 U o + o < γ` keeps a hold `≥ γ`. -/
lemma Hold.upd_lt {p : Fin n} {s : QS n} (hs : QOK p s) {U : Fin 4 → ℕ} {i : Idx n} {γ : ℕ}
    (h : Hold s U i γ) (o : Fin 4) (x : Option (Idx n)) (hlt : 4 * U o + o < γ) :
    Hold (upd p o x s) (Function.update U o (U o + 1)) i γ := by
  obtain ⟨a, rest, har, hq, -, -⟩ := upd_spec hs o x
  obtain ⟨o', j, h1, h2⟩ := h
  by_cases ho : o' = o
  · subst ho
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := by
      rcases j with _ | j'
      · omega
      · exact ⟨j', rfl⟩
    refine ⟨o', j', ?_, ?_⟩
    · rw [hq]; simp only [Function.update_self]
      have hlt' : j' + 1 < (s.q o').length := (List.getElem?_eq_some_iff.1 h1).1
      have : (s.q o' ++ [ownF p x])[j' + 1]? = some (some i) := by
        rw [List.getElem?_append_left hlt']; exact h1
      rw [har] at this; simpa using this
    · simp only [Function.update_self]; omega
  · refine ⟨o', j, ?_, ?_⟩
    · rw [hq, Function.update_of_ne ho]; exact h1
    · rw [Function.update_of_ne ho]; exact h2

/-- Enqueueing `i` (owned by `p`) at update time `u = 4 U o + o` gives a hold `u + 8n + 8`. -/
lemma Hold.upd_enq {p : Fin n} {s : QS n} (hs : QOK p s) {U : Fin 4 → ℕ} {i : Idx n}
    (o : Fin 4) (hi : i.1 = p) :
    Hold (upd p o (some i) s) (Function.update U o (U o + 1)) i (4 * U o + o + (8 * n + 8)) := by
  obtain ⟨a, rest, har, hq, -, -⟩ := upd_spec hs o (some i)
  have hl := hs.len o
  have hown : ownF p (some i) = some i := by simp [ownF, hi]
  refine ⟨o, 2 * n + 1, ?_, ?_⟩
  · rw [hq]; simp only [Function.update_self]
    have : (s.q o ++ [ownF p (some i)])[2 * n + 2]? = some (some i) := by
      rw [List.getElem?_append_right (by omega), hl, hown]; simp
    rw [har] at this; simpa using this
  · simp only [Function.update_self]; omega

/-- `i` is not added to `free_p` by an update at time `< γ` if it has a hold `≥ γ`. -/
lemma not_mem_free_upd_lt {p : Fin n} {s : QS n} (hs : QOK p s) {U : Fin 4 → ℕ} {i : Idx n}
    {γ : ℕ} (h : Hold s U i γ) (o : Fin 4) (x : Option (Idx n)) (hlt : 4 * U o + o < γ)
    (hf : i ∉ s.free) : i ∉ (upd p o x s).free := by
  have h' := h.upd_lt hs o x hlt
  have hpos := h'.pos
  have hc := (hs.updQ o x).cnt i
  obtain ⟨a, rest, har, hq, hcnt, hfree⟩ := upd_spec hs o x
  rw [hfree]; rintro (h1 | ⟨rfl, h2⟩)
  · exact hf h1
  · rw [hcnt] at hc; simp at hc; omega

/-- `i` is not added to `free_p` by an update that enqueues it. -/
lemma not_mem_free_upd_enq {p : Fin n} {s : QS n} (hs : QOK p s) {i : Idx n} (o : Fin 4)
    (hi : i.1 = p) (hf : i ∉ s.free) : i ∉ (upd p o (some i) s).free := by
  have h' := Hold.upd_enq hs (U := fun _ => 0) o hi
  have hpos := h'.pos
  have hc := (hs.updQ o (some i)).cnt i
  obtain ⟨a, rest, har, hq, hcnt, hfree⟩ := upd_spec hs o (some i)
  rw [hfree]; rintro (h1 | ⟨rfl, h2⟩)
  · exact hf h1
  · rw [hcnt] at hc; simp at hc; omega

/-- Other elements are never removed from `free_p` by `updateQ`. -/
lemma mem_free_upd {p : Fin n} {s : QS n} (hs : QOK p s) {i : Idx n} (o : Fin 4)
    (x : Option (Idx n)) (h : i ∈ s.free) : i ∈ (upd p o x s).free := by
  obtain ⟨a, rest, har, hq, hcnt, hfree⟩ := upd_spec hs o x
  exact (hfree i).2 (Or.inl h)

end Podc.WritableObjects.WF
