import Papers.PODC2026.ConsistentRefereeing.Queue
import Papers.PODC2026.ConsistentRefereeing.Contest

/-!
# Corollary 12 and Theorem 1: no lock-free strongly linearizable queues

Corollary 12 and Theorem 1 of Attiya, Castañeda, Enea, *Impossibility Results for Strong
Linearizability: The Difficulty of Consistent Refereeing* (PODC 2026), obtained by combining
Proposition 11 (`proposition11`: a lock-free strongly linearizable queue yields a lock-free
contest implementation that is strongly linearizable on the one-shot executions) with Theorem 5
(`theorem5`: no such contest implementation exists from interfering objects,
`(n − 2)`-window registers and stacks, for `n ≥ 4` processes).

The queue must allow the processes to use it as in Proposition 11: some process `ref` may
dequeue and every other process `p` may enqueue `e p`, for an injective `e : P → V` (e.g. a
queue without access restrictions over a value type with at least `n` elements).
-/

namespace Cslib.SharedMemory

namespace Referee

open Function

/-- **Corollary 12 of [ACE26].** For `n ≥ 4` processes there is no lock-free strongly
linearizable queue implementation from base objects each of which is interfering, an
`(n − 2)`-window register (or window-like with window `n − 2`), or a stack. -/
theorem corollary12 {V P ι L : Type} {B : ι → ObjSpec} [Fintype P] [DecidableEq P]
    [DecidableEq ι] (hP : 4 ≤ Fintype.card P)
    (hB : ∀ i, (B i).Interfering ∨ (B i).WindowLike (Fintype.card P - 2) ∨ (B i).StackLike)
    (Q : Impl (queueObj V) B P L) (ref : P) (e : P → V) (he : Injective e)
    (henq : ∀ p, p ≠ ref → Q.allowed p (.enq (e p))) (hdeq : Q.allowed ref .deq) :
    ¬ (Q.LockFree ∧ Q.StronglyLinearizable) := by
  rintro ⟨hlf, hsl⟩
  obtain ⟨hal, -, hwf, hslc⟩ := proposition11 he henq hdeq hlf hsl
  exact theorem5 ref hP hB (contestOfQueue Q ref e) hal
    (hwf.lockFreeOn (fun α h => h.oneShot)) hslc

/-- **Theorem 1 of [ACE26].** For `n ≥ 4` processes there is no lock-free strongly linearizable
queue implementation from interfering primitives. -/
theorem theorem1 {V P ι L : Type} {B : ι → ObjSpec} [Fintype P] [DecidableEq P]
    [DecidableEq ι] (hP : 4 ≤ Fintype.card P) (hB : ∀ i, (B i).Interfering)
    (Q : Impl (queueObj V) B P L) (ref : P) (e : P → V) (he : Injective e)
    (henq : ∀ p, p ≠ ref → Q.allowed p (.enq (e p))) (hdeq : Q.allowed ref .deq) :
    ¬ (Q.LockFree ∧ Q.StronglyLinearizable) :=
  corollary12 hP (fun i => Or.inl (hB i)) Q ref e he henq hdeq

end Referee

end Cslib.SharedMemory
