import Mathlib
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.DetSpec
import Papers.PODC2023.RuntimeVerification.Impossibility

/-!
# Theorem 5.1 and Theorem A.1 for queues, stacks, sets, priority queues, counters, consensus

Each object is a deterministic sequential object (`detSpec`, a state machine). Operations carry
a fictitious tag so that a process never invokes the same operation twice (Section 2). The data
of the indistinguishability argument (Figure 4) are:

| object | `a : ra` (by `p₁`) | `b : rb` (by `p₂`) | `cₖ : rc` |
|---|---|---|---|
| queue | `enq(1) : ok` | `deq() : 1` | `deq() : empty` |
| stack | `push(1) : ok` | `pop() : 1` | `pop() : empty` |
| priority queue | `insert(1) : ok` | `deleteMin() : 1` | `deleteMin() : empty` |
| set | `insert(1) : true` | `contains(1) : true` | `contains(1) : true` |
| counter | `inc() : ok` | `read() : 1` | `read() : 1` |
| consensus | `decide(1) : 1` | `decide(2) : 1` | `decide(2) : 1` |
-/

namespace Podc2023.RuntimeVerification.Objects

open Cslib.SharedMemory.HerlihyWing
open Podc2023.RuntimeVerification Podc2023.RuntimeVerification.Impossibility

variable {n : ℕ} {Op Y W State : Type}

theorem prefixClosed_detSpec (init : State) (δ : State → Op → State × Y) :
    PrefixClosedSpec (P := Fin n) (fun _ => detSpec init δ) :=
  prefixClosedSpec_iff.2 (detSpec_prefixClosed init δ)

/-- Sufficient conditions for `ImpData.Good` for a deterministic object: `a` takes the initial
state to `s₁` with response `ra`, `b` takes `s₁` to `s₂` with response `rb`, every `cₖ` returns
`rc` in `s₂` and stays there, and `b` does not return `rb` in the initial state. -/
theorem good_of_det (hn : 2 ≤ n) (init : State) (δ : State → Op → State × Y) (D : ImpData Op Y)
    (s₁ s₂ : State) (h1 : δ init D.a = (s₁, D.ra)) (h2 : δ s₁ D.b = (s₂, D.rb))
    (h3 : ∀ k, δ s₂ (D.c k) = (s₂, D.rc)) (hb : (δ init D.b).2 ≠ D.rb)
    (hinj : Function.Injective D.c) (hca : ∀ k, D.c k ≠ D.a) (hcb : ∀ k, D.c k ≠ D.b) :
    D.Good hn (fun _ => detSpec init δ) where
  prefixClosed := prefixClosed_detSpec init δ
  legal i := by
    rw [seqHist_mem_detSpec]
    simp only [Mseq, runOK_cons, h1, h2, true_and]
    generalize List.range i = L
    induction L with
    | nil => trivial
    | cons j L ih => simp [h3, ih]
  illegal := by
    rw [seqHist_mem_detSpec]
    simp [hb]
  c_inj := hinj
  c_ne_a := hca
  c_ne_b := hcb

/-! ## Queue -/

inductive QOp | enq (v tag : ℕ) | deq (tag : ℕ)
  deriving DecidableEq
inductive QRes | ok | val (v : ℕ) | empty
  deriving DecidableEq

/-- FIFO queue. -/
def queueδ : List ℕ → QOp → List ℕ × QRes
  | q, .enq v _ => (q ++ [v], .ok)
  | [], .deq _ => ([], .empty)
  | v :: q, .deq _ => (q, .val v)

def queueData : ImpData QOp QRes := ⟨.enq 1 0, .deq 0, fun k => .deq (k + 1), .ok, .val 1, .empty⟩

theorem queue_good (hn : 2 ≤ n) : queueData.Good hn (fun _ => detSpec [] queueδ) :=
  good_of_det hn [] queueδ queueData [1] [] rfl rfl (fun _ => rfl) (by decide)
    (fun _ _ h => by simpa [queueData] using h) (fun _ => by simp [queueData])
    (fun _ => by simp [queueData])

/-- **Theorem 5.1 for queues.** -/
theorem thm_5_1_queue (hn : 2 ≤ n) (V : Verifier n QOp QRes (Hist (Fin n) QOp QRes)) :
    ¬ RuntimeVerifies V {H | Linearizable (fun _ => detSpec [] queueδ) H} :=
  thm_5_1 (queue_good hn) V

/-- **Theorem A.1 for queues.** -/
theorem thm_A_1_queue (hn : 2 ≤ n) (V : Verifier n QOp QRes (Hist (Fin n) QOp QRes)) :
    ¬ PredictivelyVerifies V {H | Linearizable (fun _ => detSpec [] queueδ) H} :=
  thm_A_1 (queue_good hn) V

/-! ## Stack -/

inductive SOp | push (v tag : ℕ) | pop (tag : ℕ)
  deriving DecidableEq

/-- LIFO stack. -/
def stackδ : List ℕ → SOp → List ℕ × QRes
  | s, .push v _ => (v :: s, .ok)
  | [], .pop _ => ([], .empty)
  | v :: s, .pop _ => (s, .val v)

def stackData : ImpData SOp QRes := ⟨.push 1 0, .pop 0, fun k => .pop (k + 1), .ok, .val 1, .empty⟩

theorem stack_good (hn : 2 ≤ n) : stackData.Good hn (fun _ => detSpec [] stackδ) :=
  good_of_det hn [] stackδ stackData [1] [] rfl rfl (fun _ => rfl) (by decide)
    (fun _ _ h => by simpa [stackData] using h) (fun _ => by simp [stackData])
    (fun _ => by simp [stackData])

/-- **Theorem 5.1 for stacks.** -/
theorem thm_5_1_stack (hn : 2 ≤ n) (V : Verifier n SOp QRes (Hist (Fin n) SOp QRes)) :
    ¬ RuntimeVerifies V {H | Linearizable (fun _ => detSpec [] stackδ) H} :=
  thm_5_1 (stack_good hn) V

/-- **Theorem A.1 for stacks.** -/
theorem thm_A_1_stack (hn : 2 ≤ n) (V : Verifier n SOp QRes (Hist (Fin n) SOp QRes)) :
    ¬ PredictivelyVerifies V {H | Linearizable (fun _ => detSpec [] stackδ) H} :=
  thm_A_1 (stack_good hn) V

/-! ## Priority queue -/

inductive PQOp | insert (v tag : ℕ) | deleteMin (tag : ℕ)
  deriving DecidableEq

/-- Min-priority queue; the state is the sorted list of its elements. -/
def pqδ : List ℕ → PQOp → List ℕ × QRes
  | s, .insert v _ => (s.orderedInsert (· ≤ ·) v, .ok)
  | [], .deleteMin _ => ([], .empty)
  | v :: s, .deleteMin _ => (s, .val v)

def pqData : ImpData PQOp QRes :=
  ⟨.insert 1 0, .deleteMin 0, fun k => .deleteMin (k + 1), .ok, .val 1, .empty⟩

theorem pq_good (hn : 2 ≤ n) : pqData.Good hn (fun _ => detSpec [] pqδ) :=
  good_of_det hn [] pqδ pqData [1] [] rfl rfl (fun _ => rfl) (by decide)
    (fun _ _ h => by simpa [pqData] using h) (fun _ => by simp [pqData])
    (fun _ => by simp [pqData])

/-- **Theorem 5.1 for priority queues.** -/
theorem thm_5_1_pq (hn : 2 ≤ n) (V : Verifier n PQOp QRes (Hist (Fin n) PQOp QRes)) :
    ¬ RuntimeVerifies V {H | Linearizable (fun _ => detSpec [] pqδ) H} :=
  thm_5_1 (pq_good hn) V

/-- **Theorem A.1 for priority queues.** -/
theorem thm_A_1_pq (hn : 2 ≤ n) (V : Verifier n PQOp QRes (Hist (Fin n) PQOp QRes)) :
    ¬ PredictivelyVerifies V {H | Linearizable (fun _ => detSpec [] pqδ) H} :=
  thm_A_1 (pq_good hn) V

/-! ## Set -/

inductive SetOp | insert (v tag : ℕ) | contains (v tag : ℕ)
  deriving DecidableEq

/-- Set of naturals: `insert` returns whether the element was added, `contains` membership. -/
def setδ : List ℕ → SetOp → List ℕ × Bool
  | s, .insert v _ => (if v ∈ s then s else v :: s, decide (v ∉ s))
  | s, .contains v _ => (s, decide (v ∈ s))

def setData : ImpData SetOp Bool :=
  ⟨.insert 1 0, .contains 1 0, fun k => .contains 1 (k + 1), true, true, true⟩

theorem set_good (hn : 2 ≤ n) : setData.Good hn (fun _ => detSpec [] setδ) :=
  good_of_det hn [] setδ setData [1] [1] rfl rfl (fun _ => rfl) (by decide)
    (fun _ _ h => by simpa [setData] using h) (fun _ => by simp [setData])
    (fun _ => by simp [setData])

/-- **Theorem 5.1 for sets.** -/
theorem thm_5_1_set (hn : 2 ≤ n) (V : Verifier n SetOp Bool (Hist (Fin n) SetOp Bool)) :
    ¬ RuntimeVerifies V {H | Linearizable (fun _ => detSpec [] setδ) H} :=
  thm_5_1 (set_good hn) V

/-- **Theorem A.1 for sets.** -/
theorem thm_A_1_set (hn : 2 ≤ n) (V : Verifier n SetOp Bool (Hist (Fin n) SetOp Bool)) :
    ¬ PredictivelyVerifies V {H | Linearizable (fun _ => detSpec [] setδ) H} :=
  thm_A_1 (set_good hn) V

/-! ## Counter -/

inductive COp | inc (tag : ℕ) | read (tag : ℕ)
  deriving DecidableEq

/-- Counter. -/
def counterδ : ℕ → COp → ℕ × QRes
  | c, .inc _ => (c + 1, .ok)
  | c, .read _ => (c, .val c)

def counterData : ImpData COp QRes := ⟨.inc 0, .read 0, fun k => .read (k + 1), .ok, .val 1, .val 1⟩

theorem counter_good (hn : 2 ≤ n) : counterData.Good hn (fun _ => detSpec 0 counterδ) :=
  good_of_det hn 0 counterδ counterData 1 1 rfl rfl (fun _ => rfl) (by decide)
    (fun _ _ h => by simpa [counterData] using h) (fun _ => by simp [counterData])
    (fun _ => by simp [counterData])

/-- **Theorem 5.1 for counters.** -/
theorem thm_5_1_counter (hn : 2 ≤ n) (V : Verifier n COp QRes (Hist (Fin n) COp QRes)) :
    ¬ RuntimeVerifies V {H | Linearizable (fun _ => detSpec 0 counterδ) H} :=
  thm_5_1 (counter_good hn) V

/-- **Theorem A.1 for counters.** -/
theorem thm_A_1_counter (hn : 2 ≤ n) (V : Verifier n COp QRes (Hist (Fin n) COp QRes)) :
    ¬ PredictivelyVerifies V {H | Linearizable (fun _ => detSpec 0 counterδ) H} :=
  thm_A_1 (counter_good hn) V

/-! ## Consensus -/

/-- `decide v tag`: propose `v`. -/
structure DecOp where
  v : ℕ
  tag : ℕ
  deriving DecidableEq

/-- Consensus as a sequential object: the first proposal is decided. -/
def consδ : Option ℕ → DecOp → Option ℕ × ℕ
  | none, o => (some o.v, o.v)
  | some d, _ => (some d, d)

def consData : ImpData DecOp ℕ := ⟨⟨1, 0⟩, ⟨2, 0⟩, fun k => ⟨2, k + 1⟩, 1, 1, 1⟩

theorem cons_good (hn : 2 ≤ n) : consData.Good hn (fun _ => detSpec none consδ) :=
  good_of_det hn none consδ consData (some 1) (some 1) rfl rfl (fun _ => rfl) (by decide)
    (fun _ _ h => by simpa [consData] using h) (fun _ => by simp [consData])
    (fun _ => by simp [consData])

/-- **Theorem 5.1 for consensus.** -/
theorem thm_5_1_consensus (hn : 2 ≤ n) (V : Verifier n DecOp ℕ (Hist (Fin n) DecOp ℕ)) :
    ¬ RuntimeVerifies V {H | Linearizable (fun _ => detSpec none consδ) H} :=
  thm_5_1 (cons_good hn) V

/-- **Theorem A.1 for consensus.** -/
theorem thm_A_1_consensus (hn : 2 ≤ n) (V : Verifier n DecOp ℕ (Hist (Fin n) DecOp ℕ)) :
    ¬ PredictivelyVerifies V {H | Linearizable (fun _ => detSpec none consδ) H} :=
  thm_A_1 (cons_good hn) V

end Podc2023.RuntimeVerification.Objects
