import Mathlib
import Cslib.Foundations.Combinatorics.SimpleGraph.WalkParity

/-!
# Synchronous amnesiac flooding (Hussak–Trehan, PODC 2019)

Model (Definition 1.1 / Algorithm 1.1 of the paper): a simple graph `G`, a source `s`, synchronous
rounds `1, 2, …`. In round 1 the source sends `M` to all its neighbours. In round `t + 1`, every node
`v` that received `M` in round `t` sends `M` to every neighbour `w` that did *not* send `M` to `v` in
round `t`. Nodes keep no other memory.

* `FloodingTermination.afStep G M` — one round of amnesiac flooding as a map on sets of directed
  messages (`M u v`: `u` sends to `v` in the current round).
* `FloodingTermination.sends G s t u v` — in round `t`, node `u` sends `M` to `v`.
* `FloodingTermination.roundSet G s t` — the round-set `R_t` of Definition 2.1: `R_0 = {s}`, and
  for `t ≥ 1`, `R_t` is the set of nodes receiving `M` in round `t`.
* `TerminatesAfter G s T` — no message is sent in any round `t > T`;
  `IsTerminationTime G s T` — additionally `R_T ≠ ∅` (so `T` is the last active round).

The key fact (`sends_succ_iff`, `mem_roundSet_iff`) identifies the process with breadth-first search
in the bipartite double cover: `v ∈ R_t` iff `t` is a parity distance from `s` to `v`, i.e. there
is a walk of length `t` from `s` to `v` and no shorter walk of the same parity.
-/

namespace FloodingTermination

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (s : V)

/-- One synchronous round of amnesiac flooding. If `M u v` means "`u` sends `M` to `v` in round
`t`", then `afStep G M v w` means "`v` sends `M` to `w` in round `t + 1`": `v` received the message
in round `t`, `w` is a neighbour of `v`, and `w` did not send the message to `v` in round `t`. -/
def afStep (M : V → V → Prop) (v w : V) : Prop :=
  G.Adj v w ∧ (∃ u, M u v) ∧ ¬ M w v

/-- `sends G s t u v`: in round `t` of synchronous amnesiac flooding from the source `s`, node `u`
sends a copy of the message to node `v` (Algorithm 1.1). There are no messages in round `0`. -/
def sends : ℕ → V → V → Prop
  | 0 => fun _ _ => False
  | 1 => fun u v => u = s ∧ G.Adj u v
  | t + 2 => afStep G (sends (t + 1))

/-- The round-sets of Definition 2.1: `R_0 = {s}` and `R_t` (`t ≥ 1`) is the set of nodes which
receive the message in round `t`. -/
def roundSet : ℕ → Set V
  | 0 => {s}
  | t + 1 => {v | ∃ u, sends G s (t + 1) u v}

/-- Flooding has terminated after round `T`: no message is sent in any later round. -/
def TerminatesAfter (T : ℕ) : Prop :=
  ∀ t, T < t → roundSet G s t = ∅

/-- `T` is the termination time: the last round in which a message is sent (or `0` if the source
has no neighbours). -/
def IsTerminationTime (T : ℕ) : Prop :=
  (roundSet G s T).Nonempty ∧ TerminatesAfter G s T

variable {G s}

@[simp] lemma sends_zero (u v : V) : ¬ sends G s 0 u v := fun h => h

@[simp] lemma sends_one {u v : V} : sends G s 1 u v ↔ u = s ∧ G.Adj u v := Iff.rfl

lemma sends_add_two {t : ℕ} {v w : V} :
    sends G s (t + 2) v w ↔ G.Adj v w ∧ (∃ u, sends G s (t + 1) u v) ∧ ¬ sends G s (t + 1) w v :=
  Iff.rfl

@[simp] lemma roundSet_zero : roundSet G s 0 = {s} := rfl

lemma mem_roundSet_succ {t : ℕ} {v : V} :
    v ∈ roundSet G s (t + 1) ↔ ∃ u, sends G s (t + 1) u v := Iff.rfl

/-- If `v` has parity distance `t + 1`, then it has a neighbour with parity distance `t`. -/
lemma exists_isParityDist_of_succ {t : ℕ} {v : V} (h : G.IsParityDist s v (t + 1)) :
    ∃ u, G.Adj u v ∧ G.IsParityDist s u t := by
  obtain ⟨u, hu, huv⟩ := mem_walkSet_succ.1 h.1
  refine ⟨u, huv, hu, fun t' ht' hpar hm => h.2 (t' + 1) (by omega) (by omega)
    (mem_walkSet_succ_of_adj hm huv)⟩

/-- **Key lemma.** In round `t + 1`, `u` sends to `v` iff they are adjacent and their parity
distances from `s` are `t` and `t + 1` respectively: amnesiac flooding is breadth-first search in
the bipartite double cover of `G`. -/
theorem sends_succ_iff (t : ℕ) (u v : V) :
    sends G s (t + 1) u v ↔ G.Adj u v ∧ G.IsParityDist s u t ∧ G.IsParityDist s v (t + 1) := by
  induction t generalizing u v with
  | zero =>
    simp only [zero_add, sends_one, isParityDist_zero_iff]
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨h, rfl, ⟨u, rfl, h⟩, fun t' ht' hpar => by omega⟩
    · rintro ⟨h, rfl, -⟩
      exact ⟨rfl, h⟩
  | succ t ih =>
    rw [sends_add_two]
    simp only [ih]
    constructor
    · rintro ⟨huv, ⟨w, -, -, hu⟩, hnot⟩
      refine ⟨huv, hu, mem_walkSet_succ_of_adj hu.1 huv, fun t' ht' hpar hm => ?_⟩
      -- a shorter walk to `v` of the same parity must have length `t`
      rcases Nat.lt_or_ge t' t with hlt | hge
      · exact hu.2 (t' + 1) (by omega) (by omega) (mem_walkSet_succ_of_adj hm huv.symm)
      · have ht : t' = t := by omega
        subst ht
        exact hnot ⟨huv.symm, ⟨hm, fun t'' ht'' hpar' hm' =>
          hu.2 (t'' + 1) (by omega) (by omega) (mem_walkSet_succ_of_adj hm' huv.symm)⟩, hu⟩
    · rintro ⟨huv, hu, hv⟩
      obtain ⟨w, hwu, hw⟩ := exists_isParityDist_of_succ hu
      refine ⟨huv, ⟨w, hwu, hw, hu⟩, fun ⟨_, hvt, _⟩ => hv.2 t (by omega) (by omega) hvt.1⟩

/-- `v ∈ R_t` iff `t` is a parity distance from `s` to `v`. -/
theorem mem_roundSet_iff {t : ℕ} {v : V} : v ∈ roundSet G s t ↔ G.IsParityDist s v t := by
  cases t with
  | zero => simp
  | succ t =>
    rw [mem_roundSet_succ]
    simp only [sends_succ_iff]
    constructor
    · rintro ⟨u, -, -, hv⟩; exact hv
    · intro hv
      obtain ⟨u, hu, h⟩ := exists_isParityDist_of_succ hv
      exact ⟨u, hu, h, hv⟩

/-- Once a round is inactive, all later rounds are inactive. -/
lemma roundSet_succ_eq_empty {t : ℕ} (h : roundSet G s t = ∅) : roundSet G s (t + 1) = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false, mem_roundSet_iff]
  intro hv
  obtain ⟨u, -, hu⟩ := exists_isParityDist_of_succ hv
  rw [← mem_roundSet_iff, h] at hu
  exact hu

lemma roundSet_eq_empty_of_le {t t' : ℕ} (h : roundSet G s t = ∅) (ht : t ≤ t') :
    roundSet G s t' = ∅ := by
  induction ht with
  | refl => exact h
  | step _ ih => exact roundSet_succ_eq_empty ih

lemma terminatesAfter_iff {T : ℕ} : TerminatesAfter G s T ↔ roundSet G s (T + 1) = ∅ :=
  ⟨fun h => h _ (by omega), fun h _ ht => roundSet_eq_empty_of_le h ht⟩

lemma TerminatesAfter.mono {T T' : ℕ} (h : TerminatesAfter G s T) (hT : T ≤ T') :
    TerminatesAfter G s T' := fun t ht => h t (by omega)

lemma IsTerminationTime.unique {T T' : ℕ} (h : IsTerminationTime G s T)
    (h' : IsTerminationTime G s T') : T = T' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨v, hv⟩ := h'.1; rw [h.2 T' hlt] at hv; exact hv
  · obtain ⟨v, hv⟩ := h.1; rw [h'.2 T hlt] at hv; exact hv

/-- If flooding terminates after some round, it has a (unique) termination time. -/
lemma exists_isTerminationTime {T : ℕ} (h : TerminatesAfter G s T) :
    ∃ T' ≤ T, IsTerminationTime G s T' := by
  classical
  have hex : ∃ n, TerminatesAfter G s n := ⟨T, h⟩
  refine ⟨Nat.find hex, Nat.find_min' hex h, ?_, Nat.find_spec hex⟩
  rcases hn : Nat.find hex with _ | n
  · exact ⟨s, rfl⟩
  · rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have : TerminatesAfter G s n := terminatesAfter_iff.2 hempty
    exact Nat.find_min hex (by omega) this

lemma IsTerminationTime.le_iff {T T' : ℕ} (h : IsTerminationTime G s T) :
    T ≤ T' ↔ TerminatesAfter G s T' := by
  refine ⟨h.2.mono, fun h' => ?_⟩
  by_contra hlt
  obtain ⟨v, hv⟩ := h.1
  rw [h' T (by omega)] at hv
  exact hv

end FloodingTermination
