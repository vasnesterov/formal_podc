import Papers.PODC2024.HistoryIndependent.Avoidance

/-!
# Theorem 20: queues with `Peek`

A FIFO queue over the domain `Fin t` (the paper's `{1, …, t}`), with operations
`Enqueue(v)`, `Dequeue()` and the read-only `Peek()`; responses are `Option (Fin t)` (`none` is
the paper's `r₀ = ∅`, also used as the response of `Enqueue`).
-/

namespace Cslib.SharedMemory

open List

/-- Queue operations. -/
inductive QueueOp (t : ℕ) where
  | enq (v : Fin t)
  | deq
  | peek

/-- The FIFO queue with `Peek` over `Fin t`, initially empty. -/
abbrev queue (t : ℕ) : ObjSpec where
  State := List (Fin t)
  Op := QueueOp t
  Resp := Option (Fin t)
  init := []
  δ q
    | .enq v => (q ++ [v], none)
    | .deq => (q.tail, q.head?)
    | .peek => (q, q.head?)

namespace Queue

variable {t : ℕ}

/-- Representative states: `rep 0 = []`, `rep (j+1) = [j]`. -/
def rep (i : Fin (t + 1)) : List (Fin t) :=
  if h : i.val = 0 then [] else [⟨i.val - 1, by omega⟩]

lemma rep_zero : rep (0 : Fin (t + 1)) = [] := by simp [rep]

lemma rep_ne_zero {i : Fin (t + 1)} (h : i ≠ 0) : rep i = [⟨i.val - 1, by omega⟩] := by
  have : i.val ≠ 0 := fun h' => h (Fin.ext h')
  simp [rep, this]

lemma head_rep_inj : Function.Injective (fun i : Fin (t + 1) => (rep i).head?) := by
  intro i j hij
  simp only at hij
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · rw [hi, hj]
  · rw [hi, rep_zero, rep_ne_zero hj] at hij; simp at hij
  · rw [hj, rep_zero, rep_ne_zero hi] at hij; simp at hij
  · rw [rep_ne_zero hi, rep_ne_zero hj] at hij
    simp only [head?_cons, Option.some.injEq, Fin.mk.injEq] at hij
    have : i.val ≠ 0 := fun h' => hi (Fin.ext h')
    have : j.val ≠ 0 := fun h' => hj (Fin.ext h')
    exact Fin.ext (by omega)

/-- The value enqueued to reach `rep j` (`j ≠ 0`). -/
def val (j : Fin (t + 1)) (h : j ≠ 0) : Fin t :=
  ⟨j.val - 1, by have : j.val ≠ 0 := fun h' => h (Fin.ext h'); omega⟩

/-- The operation sequence `S(i₁, i₂)` of Section 5.4. -/
def path (i j : Fin (t + 1)) : List (QueueOp t) :=
  if hj : j = 0 then [.deq] else if i = 0 then [.enq (val j hj)] else [.enq (val j hj), .deq]

/-- The avoidance data for the queue: `N = t + 1` representatives. -/
def avoidData : AvoidData (queue t) (t + 1) where
  oread := .peek
  oread_ro _ := rfl
  rep := rep
  resp_inj := head_rep_inj
  path := path
  path_end i j hij := by
    unfold path
    by_cases hj : j = 0
    · subst hj
      rw [rep_ne_zero hij, rep_zero]; simp [ObjSpec.runOps]
    · by_cases hi : i = 0
      · subst hi; simp [hj, rep_zero, rep_ne_zero hj, val, ObjSpec.runOps]
      · simp [hj, hi, rep_ne_zero hi, rep_ne_zero hj, val, ObjSpec.runOps]
  path_mid i j hij m hm := by
    unfold path at hm ⊢
    by_cases hj : j = 0
    · subst hj
      simp only [dite_true, length_singleton] at hm ⊢
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
      · left; simp [ObjSpec.runOps]
      · right; rw [rep_ne_zero hij, rep_zero]; simp [ObjSpec.runOps]
    · by_cases hi : i = 0
      · subst hi
        simp only [hj, dite_false, ↓reduceIte, length_singleton] at hm ⊢
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
        · left; simp [ObjSpec.runOps]
        · right; simp [rep_zero, rep_ne_zero hj, val, ObjSpec.runOps]
      · simp only [hj, dite_false, hi, ↓reduceIte, length_cons, length_nil] at hm ⊢
        rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl
        · left; simp [ObjSpec.runOps]
        · left; simp [rep_ne_zero hi, ObjSpec.runOps]
        · right; simp [rep_ne_zero hi, rep_ne_zero hj, val, ObjSpec.runOps]
  start j := if hj : j = 0 then [] else [.enq (val j hj)]
  start_end j := by
    by_cases hj : j = 0
    · subst hj; simp [rep_zero, ObjSpec.runOps]
    · simp [hj, rep_ne_zero hj, val, ObjSpec.runOps]

end Queue

/-- **Theorem 20.** There is no wait-free state-quiescent HI implementation of a queue with
`Peek` over a domain of size `t` from base objects with fewer than `t + 1` states. Formally: in
any implementation where a process `r` may invoke `Peek` and another process `c` may invoke
`Enqueue` and `Dequeue`, if every base object has at most `t` states, the implementation is not
both wait-free and state-quiescent HI. (Holds for every `t ≥ 1`.) -/
theorem thm20 {t : ℕ} (ht : 1 ≤ t) {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type}
    [DecidableEq P] (I : Impl (queue t) B P L) (c r : P) (hcr : c ≠ r)
    (hr : I.allowed r .peek) (hc : ∀ o : QueueOp t, o ≠ .peek → I.allowed c o)
    (hB : ∀ j, Finite (B j).State ∧ Nat.card (B j).State < t + 1) :
    ¬ (I.WaitFree ∧ I.StateQuiescentHI) := by
  apply not_waitFree_stateQuiescentHI Queue.avoidData I c r (by omega) hcr hr _ _ hB
  · intro i j o ho
    simp only [Queue.avoidData, Queue.path] at ho
    split_ifs at ho <;> simp at ho <;> rcases ho with rfl | rfl <;> exact hc _ (by simp)
  · intro j o ho
    simp only [Queue.avoidData] at ho
    split_ifs at ho
    · simp at ho
    · simp at ho; subst ho; exact hc _ (by simp)

end Cslib.SharedMemory
