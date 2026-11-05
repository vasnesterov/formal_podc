import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Objects.Queue
import Mathlib.Tactic

/-!
# Sequential queues run in batches (the arithmetic of Lemmas 16 and 17)

The linearization ordering (3.2) of the paper runs the root blocks one after the other, each
block's enqueues before its dequeues. Here a block is a *batch* `(E, D)`: a list of enqueues
(key, value) and a list of dequeue keys. This file computes the state of a sequential FIFO queue
after a list of batches, the `size` recursion of line 50, and the response of every operation —
the facts used in Lemmas 16 and 17 and in `FindResponse` (lines 85–94).
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {K V : Type} [DecidableEq K]

/-- A batch: the enqueue sequence `E(B)` (keys with values) and the dequeue sequence `D(B)`. -/
abbrev Batch (K V : Type) := List (K × V) × List K

/-- The linearization (3.2) of a list of batches: `E(B₁) · D(B₁) · E(B₂) · D(B₂) ⋯`. -/
def batchLin (bs : List (Batch K V)) : List (K × FifoOp V) :=
  bs.flatMap fun B => B.1.map (fun e => (e.1, FifoOp.enq e.2)) ++ B.2.map (fun k => (k, FifoOp.deq))

/-- The `size` recursion of line 50: `size ← max(0, size + |E| - |D|)`. -/
def batchSize (bs : List (Batch K V)) : ℕ :=
  bs.foldl (fun s B => s + B.1.length - B.2.length) 0

/-- All enqueued values, in linearization order. -/
def enqVals (bs : List (Batch K V)) : List V := bs.flatMap fun B => B.1.map Prod.snd

/-- Number of enqueues. -/
def numEnq (bs : List (Batch K V)) : ℕ := (bs.map fun B => B.1.length).sum

/-! ### Helper lemmas -/

omit [DecidableEq K] in
theorem batchLin_append (bs cs : List (Batch K V)) :
    batchLin (bs ++ cs) = batchLin bs ++ batchLin cs := by
  simp [batchLin]

omit [DecidableEq K] in
theorem batchSize_append_singleton (bs : List (Batch K V)) (B : Batch K V) :
    batchSize (bs ++ [B]) = batchSize bs + B.1.length - B.2.length := by
  simp [batchSize, List.foldl_append]

omit [DecidableEq K] in
theorem enqVals_append (bs cs : List (Batch K V)) :
    enqVals (bs ++ cs) = enqVals bs ++ enqVals cs := by
  simp [enqVals]

omit [DecidableEq K] in
theorem numEnq_append (bs cs : List (Batch K V)) :
    numEnq (bs ++ cs) = numEnq bs + numEnq cs := by
  simp [numEnq]

omit [DecidableEq K] in
theorem batch_length_enqVals (bs : List (Batch K V)) : (enqVals bs).length = numEnq bs := by
  induction bs with
  | nil => rfl
  | cons B bs ih =>
    simp only [enqVals, List.flatMap_cons, List.length_append, List.length_map, numEnq,
      List.map_cons, List.sum_cons] at ih ⊢
    omega

omit [DecidableEq K] in
theorem batch_runOps_enqs (q : List V) (E : List (K × V)) :
    (queueObj V).runOps q (E.map fun e => FifoOp.enq e.2) = q ++ E.map Prod.snd := by
  induction E generalizing q with
  | nil => simp only [List.map_nil, List.append_nil]; rfl
  | cons e E ih =>
    rw [List.map_cons, ObjSpec.runOps_cons, queueObj_enq, ih]
    simp

omit [DecidableEq K] in
theorem batch_runOps_deqs (q : List V) (D : List K) :
    (queueObj V).runOps q (D.map fun _ => FifoOp.deq) = q.drop D.length := by
  induction D generalizing q with
  | nil => rfl
  | cons d D ih =>
    rw [List.map_cons, ObjSpec.runOps_cons, queueObj_deq, ih]
    simp [List.drop_tail]

omit [DecidableEq K] in
theorem batch_runOps_one (q : List V) (B : Batch K V) :
    (queueObj V).runOps q ((batchLin [B]).map Prod.snd) = (q ++ B.1.map Prod.snd).drop B.2.length := by
  simp only [batchLin, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append,
    List.map_map]
  rw [ObjSpec.runOps_append]
  have h1 := batch_runOps_enqs q B.1
  have h2 := batch_runOps_deqs (q ++ B.1.map Prod.snd) B.2
  simp only [Function.comp_def] at h1 h2 ⊢
  rw [h1, h2]

/-- **Lemma 16 (arithmetic).** After running the batches sequentially on an empty queue, the
queue holds the last `batchSize bs` enqueued values. -/
theorem runOps_batchLin (bs : List (Batch K V)) :
    batchSize bs ≤ numEnq bs ∧
    (queueObj V).runOps [] ((batchLin bs).map Prod.snd) = (enqVals bs).drop (numEnq bs - batchSize bs) := by
  induction bs using List.reverseRecOn with
  | nil => exact ⟨le_refl 0, rfl⟩
  | append_singleton bs B ih =>
    obtain ⟨h1, h2⟩ := ih
    have hlen := batch_length_enqVals bs
    have hn1 : numEnq [B] = B.1.length := by simp [numEnq]
    have he1 : enqVals [B] = B.1.map Prod.snd := by simp [enqVals]
    rw [batchSize_append_singleton, numEnq_append, enqVals_append, batchLin_append,
      List.map_append, ObjSpec.runOps_append, h2, batch_runOps_one, hn1, he1]
    refine ⟨by omega, ?_⟩
    rw [← List.drop_append_of_le_length (by omega), List.drop_drop]
    by_cases h : B.2.length ≤ batchSize bs + B.1.length
    · congr 1; omega
    · rw [List.drop_eq_nil_of_le, List.drop_eq_nil_of_le] <;> simp <;> omega

/-- Every enqueue gets response `none`. -/
theorem respIn_batchLin_enq (bs : List (Batch K V))
    (hnd : ((batchLin bs).map Prod.fst).Nodup) {k : K} {v : V} {B : Batch K V}
    (hB : B ∈ bs) (hk : (k, v) ∈ B.1) :
    (queueObj V).respIn [] (batchLin bs) k = some none := by
  obtain ⟨bs1, bs2, rfl⟩ := List.append_of_mem hB
  obtain ⟨E1, E2, hE⟩ := List.append_of_mem hk
  have hL : batchLin (bs1 ++ B :: bs2) =
      (batchLin bs1 ++ E1.map (fun e => (e.1, FifoOp.enq e.2))) ++ (k, FifoOp.enq v) ::
        (E2.map (fun e => (e.1, FifoOp.enq e.2)) ++ B.2.map (fun k => (k, FifoOp.deq)) ++
          batchLin bs2) := by
    simp [batchLin, hE]
  rw [ObjSpec.respIn_of_split hnd hL]

/-- **Lemma 17 (arithmetic).** The `i`-th dequeue (0-based) of batch `b` returns `null` iff
`size_{b-1} + |E_b| < i + 1`, and otherwise the value of the `e`-th enqueue (1-based) of the
linearization, `e = (i + 1) + (#enqueues before batch b) - size_{b-1}` (line 89). -/
theorem respIn_batchLin_deq (bs : List (Batch K V))
    (hnd : ((batchLin bs).map Prod.fst).Nodup) (b : ℕ) (hb : b < bs.length) (i : ℕ)
    (hi : i < bs[b].2.length) :
    (queueObj V).respIn [] (batchLin bs) bs[b].2[i] =
      some (if batchSize (bs.take b) + bs[b].1.length < i + 1 then none
        else (enqVals bs)[i + numEnq (bs.take b) - batchSize (bs.take b)]?) := by
  have hbs : bs = bs.take b ++ bs[b] :: bs.drop (b + 1) := by
    simp
  have hD : bs[b].2 = bs[b].2.take i ++ bs[b].2[i] :: bs[b].2.drop (i + 1) := by
    simp
  have hL : batchLin bs =
      (batchLin (bs.take b) ++ bs[b].1.map (fun e => (e.1, FifoOp.enq e.2)) ++
        (bs[b].2.take i).map (fun k => (k, FifoOp.deq))) ++ (bs[b].2[i], FifoOp.deq) ::
        ((bs[b].2.drop (i + 1)).map (fun k => (k, FifoOp.deq)) ++ batchLin (bs.drop (b + 1))) := by
    conv_lhs => rw [hbs]
    rw [batchLin_append]
    conv_lhs => rw [show bs[b] :: bs.drop (b + 1) = [bs[b]] ++ bs.drop (b + 1) from rfl,
      batchLin_append]
    conv_lhs => simp only [batchLin, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    conv_lhs => rw [hD, List.map_append, List.map_cons]
    simp only [List.append_assoc, List.cons_append]
    rfl
  rw [ObjSpec.respIn_of_split hnd hL]
  obtain ⟨hsn, hrun⟩ := runOps_batchLin (bs.take b)
  have hlen := batch_length_enqVals (bs.take b)
  have henq : enqVals bs = enqVals (bs.take b) ++ bs[b].1.map Prod.snd ++
      enqVals (bs.drop (b + 1)) := by
    conv_lhs => rw [hbs]
    rw [enqVals_append, show bs[b] :: bs.drop (b + 1) = [bs[b]] ++ bs.drop (b + 1) from rfl,
      enqVals_append]
    simp [enqVals]
  simp only [List.map_append, List.map_map, Function.comp_def]
  rw [ObjSpec.runOps_append, ObjSpec.runOps_append]
  have h1 := batch_runOps_enqs ((queueObj V).runOps [] ((batchLin (bs.take b)).map Prod.snd))
    bs[b].1
  have h2 := batch_runOps_deqs ((queueObj V).runOps [] ((batchLin (bs.take b)).map Prod.snd) ++
    bs[b].1.map Prod.snd) (bs[b].2.take i)
  rw [h1, h2, hrun, List.length_take_of_le (by omega),
    ← List.drop_append_of_le_length (by omega), List.drop_drop, List.head?_drop, henq]
  congr 1
  split_ifs with h
  · rw [List.getElem?_eq_none]
    simp only [List.length_append, List.length_map]
    omega
  · rw [show i + numEnq (bs.take b) - batchSize (bs.take b) =
        numEnq (bs.take b) - batchSize (bs.take b) + i by omega,
      List.getElem?_append_left (l₂ := enqVals (bs.drop (b + 1)))
        (by simp only [List.length_append, List.length_map]; omega)]

/-- In the non-null case of `respIn_batchLin_deq` the index is within the enqueues of the
first `b + 1` batches. -/
theorem deq_index_lt (bs : List (Batch K V)) (b : ℕ) (hb : b < bs.length) (i : ℕ)
    (h : ¬ batchSize (bs.take b) + bs[b].1.length < i + 1) :
    i + numEnq (bs.take b) - batchSize (bs.take b) < numEnq (bs.take (b + 1)) := by
  have hsn := (runOps_batchLin (V := V) (bs.take b)).1
  rw [List.take_succ_eq_append_getElem hb, numEnq_append]
  have : numEnq [bs[b]] = bs[b].1.length := by simp [numEnq]
  omega

end Podc.WaitFreeQueuePolylog
