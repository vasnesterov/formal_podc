import Mathlib

/-!
# Segment schedules: the model of Section 2 of Miller–Pelc (upper bounds)

All three algorithms of Section 2 of [Miller, Pelc, *Time versus cost tradeoffs for deterministic
rendezvous in networks*, PODC 2014] (Cheap, Fast, FastWithRelabeling) have the same shape: the
agent's time is cut into *segments* of `E` rounds, and in segment `i` the agent either executes
the procedure EXPLORE (which visits every node of the graph within `E` rounds, from any start) or
waits `E` rounds. Such an algorithm is a bit list (`true` = explore), the *segment schedule*; after
the list is exhausted the agent stays where it is.

**Model.** For the upper bounds of Section 2 no graph structure is needed: the network is an
arbitrary type `V` of nodes and EXPLORE is abstracted by `Explore V E`, a family of walks
`walk v t` (position after `t` rounds of EXPLORE started at `v`) visiting every node within `E`
rounds. EXPLORE always takes exactly `E` rounds (it waits at the end), so its position after `t`
rounds is `walk v (min t E)`. Executions are synchronous and deterministic. The adversary wakes
agent `A` at time `δA` and agent `B` at time `δB`, with `δA = 0 ∨ δB = 0` (time is counted from
the wake-up of the earlier agent). A sleeping agent sits at its starting node, where it can be
found. Both agents stop upon meeting.

* `pos X a r` : position of agent `a` at time `r` (after `r` rounds);
* `MeetsAt X A B r` : both agents are at the same node at time `r`;
* `meetTime X A B` : the first such time (rendezvous time, counted from the earlier wake-up);
* `cost X A B` : the number of rounds before the first meeting in which `A` changes its position,
  plus the same for `B` (the edge traversals of both agents before rendezvous).
-/

namespace Podc.RendezvousTimeCost.Upper

/-- `omega` after expanding products `(a + b) * E` into multiples of the atoms `x * E`. -/
macro "rtc_omega" : tactic =>
  `(tactic| ((try simp only [add_mul, mul_assoc, one_mul] at *) <;> omega))

/-- An exploration procedure with time bound `E` on a network with node set `V`: `walk v t` is
the position after `t` rounds of EXPLORE started at `v`, and every node is visited within `E`
rounds. (No graph structure is needed for the upper bounds of Section 2.) -/
structure Explore (V : Type*) (E : ℕ) where
  /-- Position after `t` rounds of EXPLORE started at `v`. -/
  walk : V → ℕ → V
  walk_zero : ∀ v, walk v 0 = v
  covers : ∀ v u, ∃ t ≤ E, walk v t = u

variable {V : Type*} {E : ℕ}

/-- Position after `s ≤ E` rounds of a segment started at `w`: EXPLORE if `b`, waiting otherwise. -/
def segStep (X : Explore V E) (b : Bool) (w : V) (s : ℕ) : V := if b then X.walk w s else w

/-- The solo trajectory of an agent following the segment schedule `bits` from node `v`:
position after `t` rounds of its own clock. After the schedule ends the agent stays. -/
def segTraj (X : Explore V E) : List Bool → V → ℕ → V
  | [], v, _ => v
  | b :: bs, v, t =>
    if t < E then segStep X b v t else segTraj X bs (segStep X b v E) (t - E)

/-- An agent: its segment schedule, its starting node and its wake-up delay. -/
structure Agent (V : Type*) where
  /-- The segment schedule (`true` = explore). -/
  bits : List Bool
  /-- The starting node. -/
  start : V
  /-- The wake-up time (rounds after time `0`). -/
  delay : ℕ

/-- Position of agent `a` at (global) time `r`. -/
def pos (X : Explore V E) (a : Agent V) (r : ℕ) : V := segTraj X a.bits a.start (r - a.delay)

/-- The agents are at the same node at time `r`. -/
def MeetsAt (X : Explore V E) (A B : Agent V) (r : ℕ) : Prop := pos X A r = pos X B r

/-- Rendezvous time: the first time at which the agents meet. -/
noncomputable def meetTime (X : Explore V E) (A B : Agent V) : ℕ := sInf {r | MeetsAt X A B r}

/-- Number of rounds among the first `n` in which the position `f` changes. -/
def moveCount [DecidableEq V] (f : ℕ → V) : ℕ → ℕ
  | 0 => 0
  | n + 1 => moveCount f n + if f (n + 1) = f n then 0 else 1

/-- Cost of rendezvous: edge traversals of both agents before the first meeting. -/
noncomputable def cost [DecidableEq V] (X : Explore V E) (A B : Agent V) : ℕ :=
  moveCount (pos X A) (meetTime X A B) + moveCount (pos X B) (meetTime X A B)

/-! ### Trajectories -/

section Traj

variable (X : Explore V E)

@[simp] lemma segStep_zero (b : Bool) (w : V) : segStep X b w 0 = w := by
  cases b <;> simp [segStep, X.walk_zero]

@[simp] lemma segStep_false (w : V) (s : ℕ) : segStep X false w s = w := rfl

@[simp] lemma segTraj_zero (bits : List Bool) (v : V) : segTraj X bits v 0 = v := by
  induction bits generalizing v with
  | nil => rfl
  | cons b bs ih =>
    simp only [segTraj]
    split_ifs with h
    · simp
    · have : E = 0 := by omega
      subst this
      simp [ih]

lemma segTraj_cons_of_le (b : Bool) (bs : List Bool) (v : V) {t : ℕ} (ht : t ≤ E) :
    segTraj X (b :: bs) v t = segStep X b v t := by
  simp only [segTraj]
  split_ifs with h
  · rfl
  · have : t = E := by omega
    subst this
    simp

lemma segTraj_cons_add (b : Bool) (bs : List Bool) (v : V) (t : ℕ) :
    segTraj X (b :: bs) v (E + t) = segTraj X bs (segStep X b v E) t := by
  simp only [segTraj]
  split_ifs with h
  · omega
  · congr 1; omega

/-- Position inside segment `i`: `s ≤ E` rounds after the start of segment `i`. -/
lemma segTraj_seg (bits : List Bool) (v : V) (i : ℕ) {s : ℕ} (hs : s ≤ E) :
    segTraj X bits v (i * E + s) =
      segStep X (bits.getD i false) (segTraj X bits v (i * E)) s := by
  induction bits generalizing v i with
  | nil => simp [segTraj]
  | cons b bs ih =>
    cases i with
    | zero => simp [segTraj_cons_of_le X b bs v hs]
    | succ i =>
      have h1 : (i + 1) * E + s = E + (i * E + s) := by ring
      have h2 : (i + 1) * E = E + i * E := by ring
      rw [h1, h2, segTraj_cons_add, segTraj_cons_add, ih]
      simp

/-- In an idle segment the agent does not move. -/
lemma segTraj_idle (bits : List Bool) (v : V) {i : ℕ} (hi : bits.getD i false = false)
    {s : ℕ} (hs : s ≤ E) : segTraj X bits v (i * E + s) = segTraj X bits v (i * E) := by
  rw [segTraj_seg X bits v i hs, hi, segStep_false]

/-- In an exploration segment the agent visits every node. -/
lemma segTraj_explore (bits : List Bool) (v : V) {i : ℕ} (hi : bits.getD i false = true)
    (u : V) : ∃ s ≤ E, segTraj X bits v (i * E + s) = u := by
  obtain ⟨s, hs, h⟩ := X.covers (segTraj X bits v (i * E)) u
  exact ⟨s, hs, by rw [segTraj_seg X bits v i hs, hi]; exact h⟩

/-- Over a run of idle segments `a, …, b-1` the agent does not move. -/
lemma segTraj_idle_range (bits : List Bool) (v : V) {a b : ℕ} (hab : a ≤ b)
    (hi : ∀ i, a ≤ i → i < b → bits.getD i false = false) {t : ℕ} (h1 : a * E ≤ t)
    (h2 : t ≤ b * E) : segTraj X bits v t = segTraj X bits v (a * E) := by
  induction b, hab using Nat.le_induction generalizing t with
  | base => congr 1; exact le_antisymm h2 h1
  | succ b hab ih =>
    by_cases ht : t ≤ b * E
    · exact ih (fun i h1 h2 => hi i h1 (by omega)) h1 ht
    · obtain ⟨s, rfl⟩ : ∃ s, t = b * E + s := ⟨t - b * E, by omega⟩
      have hs : s ≤ E := by rw [Nat.succ_mul] at h2; omega
      rw [segTraj_idle X bits v (hi b hab (by omega)) hs]
      exact ih (fun i h1 h2 => hi i h1 (by omega)) (Nat.mul_le_mul_right _ hab) le_rfl

/-- The trajectory up to time `k * E` only depends on the first `k` segments. -/
lemma segTraj_take (bits : List Bool) (v : V) {k t : ℕ} (ht : t ≤ k * E) :
    segTraj X bits v t = segTraj X (bits.take k) v t := by
  induction bits generalizing k v t with
  | nil => simp
  | cons b bs ih =>
    cases k with
    | zero => simp at ht; simp [ht]
    | succ k =>
      rw [List.take_succ_cons]
      by_cases htE : t ≤ E
      · rw [segTraj_cons_of_le X _ _ _ htE, segTraj_cons_of_le X _ _ _ htE]
      · obtain ⟨s, rfl⟩ : ∃ s, t = E + s := ⟨t - E, by omega⟩
        rw [segTraj_cons_add, segTraj_cons_add, ih]
        rw [Nat.succ_mul] at ht; omega

end Traj

/-! ### Agents -/

section Agents

variable (X : Explore V E)

@[simp] lemma pos_delay_add (a : Agent V) (t : ℕ) :
    pos X a (a.delay + t) = segTraj X a.bits a.start t := by
  simp [pos]

lemma pos_of_le_delay (a : Agent V) {r : ℕ} (hr : r ≤ a.delay) : pos X a r = a.start := by
  simp [pos, Nat.sub_eq_zero_of_le hr]

/-- An agent idle (in its own time) on the segments `i, …, j-1` stays at one node during the
global time window `[δ + iE, δ + jE]`. -/
lemma pos_idle_range (a : Agent V) {i j : ℕ} (hij : i ≤ j)
    (hi : ∀ k, i ≤ k → k < j → a.bits.getD k false = false) :
    ∀ r, a.delay + i * E ≤ r → r ≤ a.delay + j * E →
      pos X a r = segTraj X a.bits a.start (i * E) := by
  intro r h1 h2
  obtain ⟨t, rfl⟩ : ∃ t, r = a.delay + t := ⟨r - a.delay, by omega⟩
  rw [pos_delay_add]
  exact segTraj_idle_range X _ _ hij hi (by omega) (by omega)

/-- An agent exploring in its segment `i` visits every node in the window
`[δ + iE, δ + (i+1)E]`. -/
lemma pos_explore (a : Agent V) {i : ℕ} (hi : a.bits.getD i false = true) (u : V) :
    ∃ s ≤ E, pos X a (a.delay + i * E + s) = u := by
  obtain ⟨s, hs, h⟩ := segTraj_explore X a.bits a.start hi u
  exact ⟨s, hs, by rw [add_assoc, pos_delay_add, h]⟩

/-- If one agent stays at a node `c` during the window `[lo, hi]` and the other one visits every
node during the window `[b, b + E] ⊆ [lo, hi]`, they meet within `[b, b + E]`. -/
lemma meet_of_window {p q : ℕ → V} (c : V) {lo hi b : ℕ}
    (hp : ∀ r, lo ≤ r → r ≤ hi → p r = c) (hq : ∀ u, ∃ s ≤ E, q (b + s) = u)
    (h1 : lo ≤ b) (h2 : b + E ≤ hi) : ∃ r, b ≤ r ∧ r ≤ b + E ∧ p r = q r := by
  obtain ⟨s, hs, h⟩ := hq c
  exact ⟨b + s, by omega, by omega, by rw [h, hp _ (by omega) (by omega)]⟩

lemma meetsAt_comm (A B : Agent V) (r : ℕ) : MeetsAt X A B r ↔ MeetsAt X B A r := eq_comm

lemma meetTime_comm (A B : Agent V) : meetTime X A B = meetTime X B A := by
  simp only [meetTime, meetsAt_comm X A B]

lemma meetTime_le {A B : Agent V} {r : ℕ} (h : MeetsAt X A B r) : meetTime X A B ≤ r :=
  Nat.sInf_le h

end Agents

/-! ### Counting moves -/

section Moves

variable [DecidableEq V]

@[simp] lemma moveCount_zero (f : ℕ → V) : moveCount f 0 = 0 := rfl

lemma moveCount_succ (f : ℕ → V) (n : ℕ) :
    moveCount f (n + 1) = moveCount f n + if f (n + 1) = f n then 0 else 1 := rfl

lemma moveCount_mono (f : ℕ → V) {m n : ℕ} (h : m ≤ n) : moveCount f m ≤ moveCount f n := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => rw [moveCount_succ]; omega

lemma moveCount_le_self (f : ℕ → V) (n : ℕ) : moveCount f n ≤ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [moveCount_succ]; split_ifs <;> omega

lemma moveCount_congr {f g : ℕ → V} {n : ℕ} (h : ∀ t ≤ n, f t = g t) :
    moveCount f n = moveCount g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [moveCount_succ, moveCount_succ, ih (fun t ht => h t (by omega)), h n (by omega),
      h (n + 1) le_rfl]

lemma moveCount_const {f : ℕ → V} {n : ℕ} (c : V) (h : ∀ t ≤ n, f t = c) :
    moveCount f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [moveCount_succ, ih (fun t ht => h t (by omega)), h n (by omega), h (n + 1) le_rfl]
    simp

lemma moveCount_add (f : ℕ → V) (m n : ℕ) :
    moveCount f (m + n) = moveCount f m + moveCount (fun t => f (m + t)) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [← add_assoc, moveCount_succ, ih, moveCount_succ]; simp [add_assoc]

/-- Moves of a delayed agent are the moves of its solo trajectory. -/
lemma moveCount_shift (f : ℕ → V) (δ n : ℕ) :
    moveCount (fun r => f (r - δ)) n = moveCount f (n - δ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [moveCount_succ, ih]
    by_cases h : n < δ
    · rw [Nat.sub_eq_zero_of_le (show n + 1 ≤ δ by omega), Nat.sub_eq_zero_of_le h.le]; simp
    · rw [show n + 1 - δ = n - δ + 1 by omega, moveCount_succ]

variable (X : Explore V E)

lemma moveCount_pos (a : Agent V) (n : ℕ) :
    moveCount (pos X a) n = moveCount (segTraj X a.bits a.start) (n - a.delay) :=
  moveCount_shift _ _ _

lemma moveCount_segTraj_cons (b : Bool) (bs : List Bool) (v : V) (n : ℕ) :
    moveCount (segTraj X (b :: bs) v) n ≤
      (if b then E else 0) + moveCount (segTraj X bs (segStep X b v E)) (n - E) := by
  have hfirst : moveCount (segTraj X (b :: bs) v) (min n E) ≤ if b then E else 0 := by
    cases b
    · rw [moveCount_const v]; · simp
      intro t ht; rw [segTraj_cons_of_le X _ _ _ (by omega)]; rfl
    · exact (moveCount_le_self _ _).trans (by simp)
  by_cases h : n ≤ E
  · rw [min_eq_left h] at hfirst; omega
  · rw [min_eq_right (by omega)] at hfirst
    obtain ⟨s, rfl⟩ : ∃ s, n = E + s := ⟨n - E, by omega⟩
    rw [moveCount_add]
    simp only [segTraj_cons_add, Nat.add_sub_cancel_left]
    exact Nat.add_le_add hfirst le_rfl

/-- Moves during the first `k` segments: at most `E` per exploration segment. -/
lemma moveCount_segTraj_take (bits : List Bool) (v : V) {k n : ℕ} (hn : n ≤ k * E) :
    moveCount (segTraj X bits v) n ≤ E * (bits.take k).count true := by
  induction bits generalizing k v n with
  | nil => rw [moveCount_const (f := segTraj X [] v) v (fun _ _ => rfl)]; simp
  | cons b bs ih =>
    cases k with
    | zero => simp at hn; simp [hn]
    | succ k =>
      refine (moveCount_segTraj_cons X b bs v n).trans ?_
      have := ih (segStep X b v E) (k := k) (n := n - E) (by rw [Nat.succ_mul] at hn; omega)
      rw [List.take_succ_cons, List.count_cons]
      cases b <;> simp [mul_add] at this ⊢ <;> omega

/-- Total moves: at most `E` per exploration segment. -/
lemma moveCount_segTraj (bits : List Bool) (v : V) (n : ℕ) :
    moveCount (segTraj X bits v) n ≤ E * bits.count true := by
  induction bits generalizing v n with
  | nil => rw [moveCount_const (f := segTraj X [] v) v (fun _ _ => rfl)]; simp
  | cons b bs ih =>
    refine (moveCount_segTraj_cons X b bs v n).trans ?_
    have := ih (segStep X b v E) (n - E)
    rw [List.count_cons]
    cases b <;> simp [mul_add] at this ⊢ <;> omega

/-- To bound rendezvous time and cost it suffices to exhibit one meeting time `r ≤ T` with at
most `C` moves of both agents up to `r`. -/
lemma bounds_of_meet {A B : Agent V} {T C : ℕ}
    (h : ∃ r ≤ T, MeetsAt X A B r ∧ moveCount (pos X A) r + moveCount (pos X B) r ≤ C) :
    (∃ r, MeetsAt X A B r) ∧ meetTime X A B ≤ T ∧ cost X A B ≤ C := by
  obtain ⟨r, hrT, hm, hc⟩ := h
  have hle := meetTime_le X hm
  refine ⟨⟨r, hm⟩, hle.trans hrT, ?_⟩
  exact (add_le_add (moveCount_mono _ hle) (moveCount_mono _ hle)).trans hc

lemma exists_meet_swap {A B : Agent V} {T C : ℕ}
    (h : ∃ r ≤ T, MeetsAt X B A r ∧ moveCount (pos X B) r + moveCount (pos X A) r ≤ C) :
    ∃ r ≤ T, MeetsAt X A B r ∧ moveCount (pos X A) r + moveCount (pos X B) r ≤ C := by
  obtain ⟨r, h1, h2, h3⟩ := h
  exact ⟨r, h1, (meetsAt_comm X _ _ _).1 h2, by omega⟩

/-- Cost is at most twice the rendezvous time (at most one move per agent per round). -/
lemma cost_le_two_mul_meetTime (A B : Agent V) : cost X A B ≤ 2 * meetTime X A B := by
  have := moveCount_le_self (pos X A) (meetTime X A B)
  have := moveCount_le_self (pos X B) (meetTime X A B)
  unfold cost; omega

end Moves

end Podc.RendezvousTimeCost.Upper
