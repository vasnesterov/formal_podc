import Mathlib

/-!
# Loop-free route updates: the model (Ludwig, Marcinkowski, Schmid, PODC 2015, §2)

An *instance* consists of two simple routes `old` (`r₁`) and `new` (`r₂`) through the same set of
nodes, with the same source `s` (first node) and destination `d` (last node). As in §2 of the paper we
only keep the nodes that lie on both routes; the routes are lists without duplicates that are
permutations of each other.

A *state* is the set `A` of nodes that already use their new rule. In state `A` a node `v` forwards
to `out₂ v` if `v ∈ A` and to `out₁ v` otherwise (`fwd`). The destination has no outgoing rule.

* `LoopFree A` (strong loop-freedom, SLF): the forwarding graph of state `A` has no directed cycle.
* `RelaxedLoopFree A` (RLF): no directed cycle is reachable from the source `s`.

A *schedule* is a list of rounds `U₁, …, U_k` (finite sets of nodes), pairwise disjoint and covering
every node whose old and new rule differ (`toUpdate`). In round `t` the nodes of `U_t` are updated
asynchronously, so every state `U_{<t} ∪ X` with `X ⊆ U_t` must be loop-free (`IsSLF`, `IsRLF`).
-/

namespace Podc.LoopFreeUpdates

open Relation

variable {V : Type*} [DecidableEq V]

/-! ### Successors in a list -/

/-- The element following `v` in the list `l` (`none` if `v` is the last element or not in `l`). -/
def nextIn (l : List V) (v : V) : Option V := l[l.idxOf v + 1]?

theorem nextIn_eq_some_iff {l : List V} (hl : l.Nodup) {v w : V} :
    nextIn l v = some w ↔ ∃ (i : ℕ) (h : i + 1 < l.length), l[i] = v ∧ l[i + 1] = w := by
  constructor
  · intro h
    unfold nextIn at h
    rw [List.getElem?_eq_some_iff] at h
    obtain ⟨hlt, hw⟩ := h
    have hv : l.idxOf v < l.length := by omega
    exact ⟨l.idxOf v, hlt, List.getElem_idxOf hv, hw⟩
  · rintro ⟨i, h, rfl, rfl⟩
    unfold nextIn
    rw [hl.idxOf_getElem i (by omega)]
    simp [h]

theorem nextIn_getElem {l : List V} (hl : l.Nodup) (i : ℕ) (h : i + 1 < l.length) :
    nextIn l l[i] = some l[i + 1] :=
  (nextIn_eq_some_iff hl).2 ⟨i, h, rfl, rfl⟩

theorem idxOf_of_nextIn {l : List V} (hl : l.Nodup) {v w : V} (h : nextIn l v = some w) :
    l.idxOf w = l.idxOf v + 1 ∧ l.idxOf v + 1 < l.length := by
  obtain ⟨i, hi, rfl, rfl⟩ := (nextIn_eq_some_iff hl).1 h
  rw [hl.idxOf_getElem, hl.idxOf_getElem]
  exact ⟨rfl, hi⟩

theorem mem_of_nextIn {l : List V} (hl : l.Nodup) {v w : V} (h : nextIn l v = some w) :
    v ∈ l ∧ w ∈ l := by
  obtain ⟨i, hi, rfl, rfl⟩ := (nextIn_eq_some_iff hl).1 h
  exact ⟨List.getElem_mem _, List.getElem_mem _⟩

theorem nextIn_eq_none_of_not_mem {l : List V} {v : V} (h : v ∉ l) : nextIn l v = none := by
  unfold nextIn
  rw [List.idxOf_eq_length h]
  simp

theorem nextIn_isSome {l : List V} {v : V} (h : l.idxOf v + 1 < l.length) :
    (nextIn l v).isSome := by
  unfold nextIn
  simp [h]

/-! ### Instances -/

/-- A route-update instance: the old route `old` and the new route `new` are simple paths through the
same nodes, from the same source to the same destination. -/
structure Instance (V : Type*) where
  old : List V
  new : List V
  nodup : old.Nodup
  perm : old.Perm new
  ne_nil : old ≠ []
  head_eq : old.head? = new.head?
  getLast_eq : old.getLast? = new.getLast?

namespace Instance

variable (I : Instance V)

theorem nodup_new : I.new.Nodup := I.perm.nodup_iff.1 I.nodup

theorem new_ne_nil : I.new ≠ [] := by
  intro h; exact I.ne_nil (List.Perm.eq_nil (h ▸ I.perm))

/-- The source `s`. -/
def s : V := I.old.head I.ne_nil

/-- The destination `d`. -/
def d : V := I.old.getLast I.ne_nil

/-- The node set. -/
def nodes : Finset V := I.old.toFinset

theorem mem_new_iff {v : V} : v ∈ I.new ↔ v ∈ I.old := I.perm.mem_iff.symm

/-- `out₁`: the old rule. -/
def out₁ (v : V) : Option V := nextIn I.old v

/-- `out₂`: the new rule. -/
def out₂ (v : V) : Option V := nextIn I.new v

/-- `pos₁ v`: the position of `v` on the old route. -/
def pos₁ (v : V) : ℕ := I.old.idxOf v

/-- `pos₂ v`: the position of `v` on the new route. -/
def pos₂ (v : V) : ℕ := I.new.idxOf v

/-- The nodes that have to be updated: `U = {v : out₁ v ≠ out₂ v}`. -/
def toUpdate : Finset V := I.nodes.filter (fun v => I.out₁ v ≠ I.out₂ v)

/-! ### States and forwarding graphs -/

/-- The forwarding rule of `v` in state `A` (the set of already updated nodes). -/
def fwd (A : Finset V) (v : V) : Option V := if v ∈ A then I.out₂ v else I.out₁ v

/-- The edge relation of the forwarding graph in state `A`. -/
def Step (A : Finset V) (u v : V) : Prop := I.fwd A u = some v

/-- Strong loop-freedom: the forwarding graph of state `A` has no directed cycle. -/
def LoopFree (A : Finset V) : Prop := ∀ v, ¬ TransGen (I.Step A) v v

/-- Relaxed loop-freedom: no directed cycle of the forwarding graph of state `A` is reachable from
the source. -/
def RelaxedLoopFree (A : Finset V) : Prop :=
  ∀ v, ReflTransGen (I.Step A) I.s v → ¬ TransGen (I.Step A) v v

/-! ### Schedules -/

/-- The nodes updated before round `t` (rounds are numbered from `0`). -/
def done (rounds : List (Finset V)) (t : ℕ) : Finset V := (rounds.take t).foldr (· ∪ ·) ∅

/-- A schedule: pairwise disjoint rounds that together contain every node to be updated. -/
def IsSchedule (rounds : List (Finset V)) : Prop :=
  rounds.Pairwise Disjoint ∧ ∀ v ∈ I.toUpdate, ∃ r ∈ rounds, v ∈ r

/-- A strongly loop-free schedule (SLF): whatever subset `X` of round `t` has already been
installed, the forwarding graph is loop-free. -/
def IsSLF (rounds : List (Finset V)) : Prop :=
  I.IsSchedule rounds ∧
    ∀ (t : ℕ) (ht : t < rounds.length), ∀ X ⊆ rounds[t], I.LoopFree (done rounds t ∪ X)

/-- A relaxed loop-free schedule (RLF). -/
def IsRLF (rounds : List (Finset V)) : Prop :=
  I.IsSchedule rounds ∧
    ∀ (t : ℕ) (ht : t < rounds.length), ∀ X ⊆ rounds[t], I.RelaxedLoopFree (done rounds t ∪ X)

/-- There is a strongly loop-free schedule with exactly `k` rounds. -/
def HasSLF (k : ℕ) : Prop := ∃ rounds : List (Finset V), rounds.length = k ∧ I.IsSLF rounds

/-- There is a relaxed loop-free schedule with exactly `k` rounds. -/
def HasRLF (k : ℕ) : Prop := ∃ rounds : List (Finset V), rounds.length = k ∧ I.IsRLF rounds

/-! ### Node classification (§3.1)

The first letter tells whether the new (dashed) edge points forward (`F`) or backward (`B`) on the old
route; the second letter tells whether the old (solid) edge points forward or backward on the new
route. -/

/-- The new rule of `v` points forward on the old route. -/
def DashedFwd (v : V) : Prop := ∃ w, I.out₂ v = some w ∧ I.pos₁ v < I.pos₁ w

/-- The old rule of `v` points forward on the new route. -/
def SolidFwd (v : V) : Prop := ∃ w, I.out₁ v = some w ∧ I.pos₂ v < I.pos₂ w

/-- Type **FF**. -/
def IsFF (v : V) : Prop := v ∈ I.toUpdate ∧ I.DashedFwd v ∧ I.SolidFwd v
/-- Type **FB**. -/
def IsFB (v : V) : Prop := v ∈ I.toUpdate ∧ I.DashedFwd v ∧ ¬ I.SolidFwd v
/-- Type **BF**. -/
def IsBF (v : V) : Prop := v ∈ I.toUpdate ∧ ¬ I.DashedFwd v ∧ I.SolidFwd v
/-- Type **BB**. -/
def IsBB (v : V) : Prop := v ∈ I.toUpdate ∧ ¬ I.DashedFwd v ∧ ¬ I.SolidFwd v

end Instance

end Podc.LoopFreeUpdates
