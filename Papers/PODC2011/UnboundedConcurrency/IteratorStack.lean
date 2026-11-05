import Podc.Computability.Distributed.SharedMemory.Arrival.Basic

/-!
# The iterator stack (Afek–Morrison–Wertheim, PODC 2011, Section 5.1)

A state of the iterator stack consists of a sequence `V` of values (a write-only stack, most
recent value first) and a sequence `I` of iterators. In the paper `I` is an infinite sequence of
naturals, `0` meaning "uninitialized"; in every reachable state the initialized iterators are
exactly the first `m` ones, where `m` is the number of writes. We store only the initialized
iterators, as the list `its` of their current positions (1-based positions into `vals`):

* `write v` prepends `v` to `vals`, initializes the next iterator (position `1`) and returns its
  index (`ISResp.idx`);
* `read k` returns the value at the position of iterator `k` if this position is valid
  (`1 ≤ pos ≤ |V|`), and `none` (`⊥`) otherwise, or if the iterator is uninitialized; an
  initialized iterator is incremented in any case (`ISResp.val`).

Iterators are numbered from `0` (the paper numbers them from `1`). From the initial state (`V`
empty, no initialized iterator) this object has exactly the behaviour of the paper's object.

## Main definitions

* `ISState`, `ISOp`, `ISResp`, `ISState.at`, `itStack W`
-/

-- CSLib candidate: the iterator stack object (Cslib/Computability/Distributed/SharedMemory/Objects/)
namespace Podc.UnboundedConcurrency

open Cslib.SharedMemory

/-- State of an iterator stack: the values `vals` (`V`, most recent first) and the positions
`its` of the initialized iterators (`I`; iterator `k` has position `its[k]`, 1-based). -/
@[ext] structure ISState (W : Type) where
  /-- The values, most recent first. -/
  vals : List W
  /-- Positions of the initialized iterators. -/
  its : List ℕ

/-- Operations of the iterator stack. -/
inductive ISOp (W : Type) where
  /-- Prepend a value; returns the index of a newly initialized iterator. -/
  | write (v : W)
  /-- Read (and advance) iterator `k`. -/
  | read (k : ℕ)

/-- Responses of the iterator stack. -/
inductive ISResp (W : Type) where
  /-- Response of `write`: the index of the newly initialized iterator. -/
  | idx (k : ℕ)
  /-- Response of `read`: a value or `⊥` (`none`). -/
  | val (v : Option W)

namespace ISState

variable {W : Type}

/-- The value at the 1-based position `p` (`⊥` if `p = 0` or `p > |V|`). -/
def «at» (s : ISState W) (p : ℕ) : Option W := if p = 0 then none else s.vals[p - 1]?

/-- The transition function of the iterator stack. -/
def δ : ISState W → ISOp W → ISState W × ISResp W
  | s, .write v => (⟨v :: s.vals, s.its ++ [1]⟩, .idx s.its.length)
  | s, .read k =>
    match s.its[k]? with
    | some p => (⟨s.vals, s.its.set k (p + 1)⟩, .val (s.at p))
    | none => (s, .val none)

end ISState

/-- The iterator stack over values `W`, initially empty. -/
abbrev itStack (W : Type) : ObjSpec where
  State := ISState W
  Op := ISOp W
  Resp := ISResp W
  init := ⟨[], []⟩
  δ := ISState.δ

namespace ISState

variable {W : Type}

@[simp] lemma δ_write (s : ISState W) (v : W) :
    s.δ (.write v) = (⟨v :: s.vals, s.its ++ [1]⟩, .idx s.its.length) := rfl

lemma δ_read_of_lt (s : ISState W) {k : ℕ} (hk : k < s.its.length) :
    s.δ (.read k) = (⟨s.vals, s.its.set k (s.its[k] + 1)⟩, .val (s.at s.its[k])) := by
  simp [δ, List.getElem?_eq_getElem hk]

lemma δ_read_of_le (s : ISState W) {k : ℕ} (hk : s.its.length ≤ k) :
    s.δ (.read k) = (s, .val none) := by
  simp [δ, List.getElem?_eq_none hk]

@[simp] lemma δ_read_its_length (s : ISState W) (k : ℕ) :
    (s.δ (.read k)).1.its.length = s.its.length := by
  rcases lt_or_ge k s.its.length with hk | hk
  · rw [δ_read_of_lt s hk]; simp
  · rw [δ_read_of_le s hk]

@[simp] lemma δ_read_vals (s : ISState W) (k : ℕ) : (s.δ (.read k)).1.vals = s.vals := by
  rcases lt_or_ge k s.its.length with hk | hk
  · rw [δ_read_of_lt s hk]
  · rw [δ_read_of_le s hk]

/-- The state effects of two reads commute. -/
lemma read_read_comm (s : ISState W) (k k' : ℕ) :
    ((s.δ (.read k)).1.δ (.read k')).1 = ((s.δ (.read k')).1.δ (.read k)).1 := by
  rcases eq_or_ne k k' with rfl | hkk
  · rfl
  rcases lt_or_ge k s.its.length with hk | hk <;>
    rcases lt_or_ge k' s.its.length with hk' | hk'
  · rw [δ_read_of_lt s hk, δ_read_of_lt s hk', δ_read_of_lt _ (by simpa using hk'),
      δ_read_of_lt _ (by simpa using hk)]
    simp only [List.getElem_set_ne hkk, List.getElem_set_ne hkk.symm]
    ext1
    · rfl
    · exact List.set_comm _ _ hkk
  · rw [δ_read_of_le s hk', δ_read_of_lt s hk, δ_read_of_le _ (by simpa using hk')]
  · rw [δ_read_of_le s hk, δ_read_of_lt s hk', δ_read_of_le _ (by simpa using hk)]
  · rw [δ_read_of_le s hk, δ_read_of_le s hk', δ_read_of_le s hk]

/-- The state effects of a write and of a read of an iterator other than the one the write
initializes commute. -/
lemma write_read_comm (s : ISState W) (v : W) {k : ℕ} (hk : k ≠ s.its.length) :
    ((s.δ (.write v)).1.δ (.read k)).1 = ((s.δ (.read k)).1.δ (.write v)).1 := by
  rcases lt_or_ge k s.its.length with hk' | hk'
  · rw [δ_write, δ_read_of_lt s hk', δ_read_of_lt _ (by simp; omega)]
    simp only [δ_write, List.length_set]
    ext1
    · rfl
    · simp [List.getElem_append_left hk', List.set_append_left _ _ hk']
  · rw [δ_write, δ_read_of_le s hk', δ_read_of_le _ (by simp; omega)]
    rfl

end ISState

end Podc.UnboundedConcurrency
