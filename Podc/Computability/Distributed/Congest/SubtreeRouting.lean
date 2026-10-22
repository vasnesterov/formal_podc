import Cslib.Foundations.Combinatorics.SimpleGraph.RootedTree
import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/Congest/SubtreeRouting.lean

/-!
# Pipelined convergecast and broadcast on a family of subtrees

Let `T` be a rooted spanning tree (parent pointers, `SimpleGraph.RootedTree`) and let
`T₁, …, T_k` be connected subtrees of `T` such that every tree edge lies in at most `c` of them.
Haeupler–Izumi–Zuzic (*Low-Congestion Shortcuts without Embedding*, PODC'16, Lemma 2) show that a
convergecast (and a broadcast) can be performed on all subtrees simultaneously in `O(D + c)`
CONGEST rounds, where `D` bounds the depth of `T`: each tree edge forwards one message per round,
and among the messages ready to cross an edge the one of the subtree whose top is shallowest
(ties broken by the subtree's ID) goes first.

We model this at the level of message schedules (one message per tree edge and round, no message
contents):

* `SubtreeFamily T ι`: the subtrees, each given by its set of tree edges (identified with their
  lower endpoints) and its top vertex; going up from an edge of the subtree one either reaches the
  top or stays in the subtree.
* `IsConvergecastSchedule` / `IsBroadcastSchedule`: a round `σ i v ≥ 1` for every message
  `(v, i)` (subtree `i`, tree edge `v`), with at most one message per edge and round, and the
  causality constraint (a message crosses `v`'s parent edge only after the messages of all
  `T_i`-children of `v` have arrived; for a broadcast, only after the message reached `v`).
* `greedy`: the round-by-round greedy algorithm with priority key `κ` (the message with the
  smallest key among the *ready* unsent ones crosses each edge).

## Main results

* `SubtreeFamily.sent_of_le`: the paper's induction: if the priority is *compatible* with the
  tree (a subtree of higher priority containing a child edge of `v` also contains `v`'s edge
  whenever `v`'s edge is in the lower-priority subtree), the message `(v, i)` is sent by round
  `h v + rank v i`, where `h` is any height function and `rank v i` is the position of `i` among
  the subtrees containing `v`'s edge.
* `SubtreeFamily.compatible_topDepth`: the paper's priority (depth of the top, then ID) is
  compatible.
* `SubtreeFamily.greedy_isConvergecastSchedule`: Lemma 2 of [HIZ16] for convergecasts: the greedy
  algorithm finishes within `D - 1 + c` rounds.
* `IsConvergecastSchedule.reverse`, `SubtreeFamily.exists_isBroadcastSchedule`: reversing time
  turns a convergecast schedule into a broadcast schedule, so broadcasts also take `≤ D - 1 + c`
  rounds.
-/

open Finset

namespace SimpleGraph

namespace RootedTree

variable {V : Type*} {G : SimpleGraph V} (T : G.RootedTree)

/-- A family of connected subtrees of the rooted tree `T`, indexed by `ι`. Subtree `i` consists of
the tree edges `s(v, parent v)` for `v ∈ edges i` (tree edges are identified with their lower
endpoints) and has top vertex `top i`: from every edge of the subtree, the parent endpoint is the
top or the lower endpoint of another edge of the subtree. -/
structure SubtreeFamily (ι : Type*) where
  /-- The tree edges of each subtree (lower endpoints). -/
  edges : ι → Finset V
  /-- The top vertex of each subtree. -/
  top : ι → V
  ne_root : ∀ i, ∀ v ∈ edges i, v ≠ T.root
  parent_mem : ∀ i, ∀ v ∈ edges i, T.parent v = top i ∨ T.parent v ∈ edges i

namespace SubtreeFamily

variable {T} {ι : Type*} (F : T.SubtreeFamily ι)

open Classical in
/-- Every tree edge lies in at most `c` of the subtrees. -/
def CongestionLE [Fintype ι] (c : ℕ) : Prop :=
  ∀ v, (univ.filter fun i => v ∈ F.edges i).card ≤ c

/-- The top of a subtree lies strictly above all of its edges. -/
theorem depth_top_lt {i : ι} {v : V} (hv : v ∈ F.edges i) : T.depth (F.top i) < T.depth v := by
  induction hd : T.depth v using Nat.strong_induction_on generalizing v with
  | _ d ih =>
    have h1 := T.depth_parent v (F.ne_root i v hv)
    rcases F.parent_mem i v hv with h | h
    · rw [← h]; omega
    · have := ih _ (by omega) h rfl; omega

/-- A priority key `κ` (smaller is more urgent) is compatible with the tree if, whenever `w` is a
`T_i`-child of `v` and a more urgent subtree `T_j` contains `w`'s edge, `T_j` also contains `v`'s
edge. -/
def Compatible {K : Type*} [LinearOrder K] (κ : ι → K) : Prop :=
  ∀ i j v w, v ∈ F.edges i → w ∈ F.edges j → T.parent w = v → κ j < κ i → v ∈ F.edges j

/-- The paper's priority: shallowest top first (ties broken by any order on the IDs) is
compatible. -/
theorem compatible_topDepth {K : Type*} [LinearOrder K] (κ : ι → K)
    (hκ : ∀ i j, κ j < κ i → T.depth (F.top j) ≤ T.depth (F.top i)) : F.Compatible κ := by
  intro i j v w hv hw hwv hji
  rcases F.parent_mem j w hw with h | h
  · have h1 := hκ i j hji
    have h2 := F.depth_top_lt hv
    rw [hwv] at h; subst h; omega
  · rwa [← hwv]

/-! ### Schedules -/

/-- A convergecast schedule finishing by round `R`: message `(v, i)` (subtree `i` sends its
partial aggregate over `v`'s parent edge) is sent in round `σ i v ∈ [1, R]`, after all messages of
`T_i`-children of `v`, and two messages crossing the same edge are sent in different rounds. -/
structure IsConvergecastSchedule (σ : ι → V → ℕ) (R : ℕ) : Prop where
  pos : ∀ i, ∀ v ∈ F.edges i, 1 ≤ σ i v
  le : ∀ i, ∀ v ∈ F.edges i, σ i v ≤ R
  causal : ∀ i, ∀ v ∈ F.edges i, ∀ w ∈ F.edges i, T.parent w = v → σ i w < σ i v
  capacity : ∀ i j, ∀ v, v ∈ F.edges i → v ∈ F.edges j → σ i v = σ j v → i = j

/-- A broadcast schedule finishing by round `R`: message `(v, i)` (the value of subtree `i` crosses
`v`'s parent edge downwards) is sent in round `σ i v ∈ [1, R]`, after the message crossed the
parent edge of `parent v` (if that edge is in `T_i`), one message per edge and round. -/
structure IsBroadcastSchedule (σ : ι → V → ℕ) (R : ℕ) : Prop where
  pos : ∀ i, ∀ v ∈ F.edges i, 1 ≤ σ i v
  le : ∀ i, ∀ v ∈ F.edges i, σ i v ≤ R
  causal : ∀ i, ∀ v ∈ F.edges i, ∀ w ∈ F.edges i, T.parent w = v → σ i v < σ i w
  capacity : ∀ i j, ∀ v, v ∈ F.edges i → v ∈ F.edges j → σ i v = σ j v → i = j

variable {F}

/-- Reversing time turns a convergecast schedule into a broadcast schedule of the same length. -/
theorem IsConvergecastSchedule.reverse {σ : ι → V → ℕ} {R : ℕ}
    (h : F.IsConvergecastSchedule σ R) : F.IsBroadcastSchedule (fun i v => R + 1 - σ i v) R where
  pos i v hv := by have := h.le i v hv; omega
  le i v hv := by have := h.pos i v hv; omega
  causal i v hv w hw hwv := by
    have := h.causal i v hv w hw hwv; have := h.le i v hv; have := h.pos i w hw; omega
  capacity i j v hi hj he := by
    have := h.le i v hi; have := h.le j v hj; have := h.pos i v hi; have := h.pos j v hj
    exact h.capacity i j v hi hj (by omega)

/-! ### The greedy algorithm -/

variable (F)
variable [Fintype ι] {K : Type*} [LinearOrder K] (κ : ι → K)

/-- The element of `s` with the smallest key (`none` if `s` is empty). -/
noncomputable def pick (s : Finset ι) : Option ι :=
  if h : s.Nonempty then some (s.exists_min_image κ h).choose else none

omit [Fintype ι] in
theorem pick_spec {s : Finset ι} {i : ι} (h : pick κ s = some i) :
    i ∈ s ∧ ∀ j ∈ s, κ i ≤ κ j := by
  unfold pick at h
  split_ifs at h with hs
  · cases h; exact (s.exists_min_image κ hs).choose_spec

omit [Fintype ι] in
theorem pick_eq_some {s : Finset ι} {i : ι} (hi : i ∈ s) (hmin : ∀ j ∈ s, j ≠ i → κ i < κ j) :
    pick κ s = some i := by
  have hs : s.Nonempty := ⟨i, hi⟩
  have h := (s.exists_min_image κ hs).choose_spec
  unfold pick
  rw [dite_eq_left hs]
  congr 1
  by_contra hne
  have := hmin _ h.1 hne
  have := h.2 i hi
  exact absurd this (not_le.2 ‹_›)

open Classical in
/-- The messages that are ready to cross `v`'s parent edge and not yet sent, given the set of
messages `S` sent so far: `(v, i)` is ready when all `T_i`-children of `v` have sent. -/
noncomputable def ready (S : V → ι → Prop) (v : V) : Finset ι :=
  univ.filter fun i => v ∈ F.edges i ∧ ¬ S v i ∧ ∀ w ∈ F.edges i, T.parent w = v → S w i

/-- The greedy convergecast: `greedy t v i` holds if message `(v, i)` was sent in one of the
rounds `1, …, t`. In each round, every tree edge sends the ready message with the smallest key. -/
noncomputable def greedy : ℕ → V → ι → Prop
  | 0 => fun _ _ => False
  | t + 1 => fun v i => greedy t v i ∨ pick κ (F.ready (greedy t) v) = some i

variable {F κ}

theorem greedy_succ {t : ℕ} {v : V} {i : ι} :
    F.greedy κ (t + 1) v i ↔ F.greedy κ t v i ∨ pick κ (F.ready (F.greedy κ t) v) = some i :=
  Iff.rfl

theorem greedy_mono {s t : ℕ} (hst : s ≤ t) {v : V} {i : ι} (h : F.greedy κ s v i) :
    F.greedy κ t v i := by
  induction hst with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem mem_ready {S : V → ι → Prop} {v : V} {i : ι} :
    i ∈ F.ready S v ↔ v ∈ F.edges i ∧ ¬ S v i ∧ ∀ w ∈ F.edges i, T.parent w = v → S w i := by
  classical
  unfold ready; simp

/-- Only edges of `T_i` carry messages of `T_i`. -/
theorem mem_edges_of_greedy {t : ℕ} {v : V} {i : ι} (h : F.greedy κ t v i) : v ∈ F.edges i := by
  induction t with
  | zero => exact h.elim
  | succ t ih =>
    rcases h with h | h
    · exact ih h
    · exact (mem_ready.1 (pick_spec κ h).1).1

/-- A message sent in round `t + 1` was ready: all messages of its `T_i`-children were sent by
round `t`. -/
theorem greedy_new {t : ℕ} {v : V} {i : ι} (h : F.greedy κ (t + 1) v i) (h' : ¬ F.greedy κ t v i) :
    pick κ (F.ready (F.greedy κ t) v) = some i := by
  rcases h with h | h
  · exact absurd h h'
  · exact h

variable (F κ) in
open Classical in
/-- The rank of `i` at edge `v`: the number of subtrees containing `v`'s edge whose key is at most
that of `i` (so the most urgent one has rank `1`). -/
noncomputable def rank (v : V) (i : ι) : ℕ :=
  (univ.filter fun j => v ∈ F.edges j ∧ κ j ≤ κ i).card

theorem rank_le_congestion {c : ℕ} (hc : F.CongestionLE c) (v : V) (i : ι) :
    F.rank κ v i ≤ c := by
  classical
  refine le_trans (card_le_card ?_) (hc v)
  intro j hj
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  convert hj.1

theorem one_le_rank {v : V} {i : ι} (hv : v ∈ F.edges i) : 1 ≤ F.rank κ v i := by
  classical
  apply card_pos.2
  exact ⟨i, by simp [hv]⟩

/-- **Lemma 2 of [HIZ16], main induction.** For a compatible priority key and a height function
`h` (`h w + 1 ≤ h (parent w)`), the greedy algorithm sends message `(v, i)` by round
`h v + rank v i`. -/
theorem sent_of_le (hκi : Function.Injective κ) (hκ : F.Compatible κ) (h : V → ℕ)
    (hh : ∀ w, w ≠ T.root → h w + 1 ≤ h (T.parent w)) :
    ∀ n v i, v ∈ F.edges i → h v + F.rank κ v i ≤ n → F.greedy κ n v i := by
  classical
  intro n
  induction n with
  | zero => intro v i hv hle; have := one_le_rank (F := F) (κ := κ) hv; omega
  | succ n ih =>
    intro v i hv hle
    by_cases hlt : h v + F.rank κ v i ≤ n
    · exact Or.inl (ih v i hv hlt)
    by_cases hs : F.greedy κ n v i
    · exact Or.inl hs
    right
    -- `(v, i)` is ready.
    have hready : i ∈ F.ready (F.greedy κ n) v := by
      refine mem_ready.2 ⟨hv, hs, fun w hw hwv => ih w i hw ?_⟩
      have h1 := hh w (F.ne_root i w hw)
      rw [hwv] at h1
      have h2 : F.rank κ w i ≤ F.rank κ v i := by
        apply card_le_card
        intro j hj
        simp only [mem_filter, mem_univ, true_and] at hj ⊢
        refine ⟨?_, hj.2⟩
        rcases eq_or_ne j i with rfl | hji
        · exact hv
        · exact hκ i j v w hv hj.1 hwv (lt_of_le_of_ne hj.2 (hκi.ne hji))
      omega
    refine pick_eq_some κ hready fun j hj hji => ?_
    rcases lt_or_gt_of_ne (hκi.ne hji) with hlt' | hgt
    · -- a more urgent ready message would already have been sent
      exfalso
      obtain ⟨hvj, hsj, -⟩ := mem_ready.1 hj
      apply hsj
      apply ih v j hvj
      have : F.rank κ v j < F.rank κ v i := by
        apply card_lt_card
        refine ⟨fun k hk => ?_, fun hsub => ?_⟩
        · simp only [mem_filter, mem_univ, true_and] at hk ⊢
          exact ⟨hk.1, hk.2.trans hlt'.le⟩
        · have : i ∈ univ.filter fun k => v ∈ F.edges k ∧ κ k ≤ κ j :=
            hsub (by simp [hv])
          simp only [mem_filter, mem_univ, true_and] at this
          exact absurd this.2 (not_le.2 hlt')
      omega
    · exact hgt

/-! ### The greedy schedule -/

variable (F κ) in
open Classical in
/-- The round in which the greedy algorithm sends message `(v, i)` (`0` if never). -/
noncomputable def greedyTime (i : ι) (v : V) : ℕ :=
  if h : ∃ t, F.greedy κ t v i then Nat.find h else 0

theorem greedy_greedyTime {v : V} {i : ι} (h : ∃ t, F.greedy κ t v i) :
    F.greedy κ (F.greedyTime κ i v) v i := by
  classical
  unfold greedyTime; rw [dite_eq_left h]; exact Nat.find_spec h

theorem greedyTime_le {v : V} {i : ι} {t : ℕ} (h : F.greedy κ t v i) :
    F.greedyTime κ i v ≤ t := by
  classical
  unfold greedyTime; rw [dite_eq_left ⟨t, h⟩]; exact Nat.find_min' _ h

theorem not_greedy_lt_greedyTime {v : V} {i : ι} {t : ℕ} (ht : t < F.greedyTime κ i v) :
    ¬ F.greedy κ t v i := fun h => absurd (greedyTime_le h) (not_le.2 ht)

theorem greedyTime_pos {v : V} {i : ι} (h : ∃ t, F.greedy κ t v i) :
    1 ≤ F.greedyTime κ i v := by
  have := greedy_greedyTime h
  rcases hz : F.greedyTime κ i v with _ | n
  · rw [hz] at this; exact this.elim
  · omega

/-- The message `(v, i)` was sent in round `greedyTime` and not before: it was ready then. -/
theorem greedy_pick_greedyTime {v : V} {i : ι} (h : ∃ t, F.greedy κ t v i) :
    pick κ (F.ready (F.greedy κ (F.greedyTime κ i v - 1)) v) = some i := by
  have hpos := greedyTime_pos h
  have h1 := greedy_greedyTime h
  obtain ⟨n, hn⟩ : ∃ n, F.greedyTime κ i v = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hn] at h1 ⊢
  exact greedy_new h1 (not_greedy_lt_greedyTime (by omega))

/-- **Lemma 2 of [HIZ16] (convergecast).** Let `T` have depth `≤ D` and let every tree edge lie in
at most `c` subtrees. With a compatible injective priority key (e.g. the paper's: depth of the
top, then the ID, see `compatible_topDepth`), the greedy algorithm is a convergecast schedule that
finishes within `D - 1 + c` rounds. -/
theorem greedy_isConvergecastSchedule (hκi : Function.Injective κ) (hκ : F.Compatible κ)
    {D c : ℕ} (hT : T.DepthLE D) (hc : F.CongestionLE c) :
    F.IsConvergecastSchedule (F.greedyTime κ) (D - 1 + c) := by
  classical
  have hsent : ∀ i, ∀ v ∈ F.edges i, F.greedy κ (D - 1 + c) v i := by
    intro i v hv
    refine sent_of_le hκi hκ (fun v => D - T.depth v) ?_ _ v i hv ?_
    · intro w hw
      have := T.depth_parent w hw; have := hT w; omega
    · have h1 := rank_le_congestion (κ := κ) hc v i
      have h2 := T.depth_pos (F.ne_root i v hv)
      omega
  have hex : ∀ i, ∀ v ∈ F.edges i, ∃ t, F.greedy κ t v i := fun i v hv => ⟨_, hsent i v hv⟩
  refine ⟨fun i v hv => greedyTime_pos (hex i v hv), fun i v hv => greedyTime_le (hsent i v hv),
    ?_, ?_⟩
  · intro i v hv w hw hwv
    have hp := greedy_pick_greedyTime (hex i v hv)
    have hr := (mem_ready.1 (pick_spec κ hp).1).2.2 w hw hwv
    have := greedyTime_le hr
    have := greedyTime_pos (hex i v hv)
    omega
  · intro i j v hi hj he
    have hpi := greedy_pick_greedyTime (hex i v hi)
    have hpj := greedy_pick_greedyTime (hex j v hj)
    rw [he, hpj] at hpi
    exact (Option.some_injective _ hpi).symm

/-- **Lemma 2 of [HIZ16] (both operations).** If every tree edge of a depth-`≤ D` tree lies in at
most `c` subtrees, a convergecast and a broadcast on all subtrees can be scheduled within
`D - 1 + c` rounds each. The convergecast is the paper's greedy algorithm (shallowest top first,
then smallest ID); the broadcast is its time reversal. -/
theorem exists_schedules [LinearOrder ι] {D c : ℕ} (hT : T.DepthLE D) (hc : F.CongestionLE c) :
    ∃ σ τ : ι → V → ℕ, F.IsConvergecastSchedule σ (D - 1 + c) ∧
      F.IsBroadcastSchedule τ (D - 1 + c) := by
  let κ : ι → ℕ ×ₗ ι := fun i => toLex (T.depth (F.top i), i)
  have hκi : Function.Injective κ := fun i j h => by
    have := congrArg (fun p => (ofLex p).2) h; simpa [κ] using this
  have hκ : F.Compatible κ := F.compatible_topDepth κ fun i j h => by
    rcases Prod.Lex.lt_iff.1 h with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  have h := greedy_isConvergecastSchedule hκi hκ hT hc
  exact ⟨_, _, h, h.reverse⟩

end SubtreeFamily

end RootedTree

end SimpleGraph
