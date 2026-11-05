import Mathlib

/-!
# The multi-agent rotor-router with delayed deployments

Klasing, Kosowski, Pająk, Sauerwald, *The Multi-Agent Rotor-Router on the Ring: A Deterministic
Alternative to Parallel Random Walks*, PODC 2013 (full version hal-00735113v2), Sections 1.3
and 2.1.

* A `RotorGraph` is a finite set of nodes; node `v` has `deg v ≥ 1` outgoing arcs arranged in the
  fixed cyclic order `port v 0, …, port v (deg v - 1)` (the paper's `ρ_v`). Multi-arcs and loops
  are allowed; the paper's setting (the directed symmetric version of an undirected graph) is a
  special case.
* A configuration (`Config`) is the number of (indistinguishable) agents on each node and the
  port pointer of each node (a cyclic position, read modulo `deg v`).
* Rounds are synchronous. In a round with delays `d`, node `v` keeps `min (pos v) (d v)` agents
  (the stopped ones) and releases the others one by one: the `j`-th released agent leaves along
  the arc at cyclic position `ptr v + j`, and the pointer advances by the number of released
  agents (`step`). A delayed deployment `D` gives the delays `D t` of every round `t ≥ 1`; the
  undelayed system `R[k]` is `D = 0` (`undelayed`).
* `visits c₀ D t v` is the paper's `n_v^D(t)`: the agents placed on `v` initially plus the number
  of arrivals at `v` in rounds `1, …, t` (equation (4) of the paper).

The main technical fact (`visits_eq_visitsOf`) is the paper's description of the system by
cumulative exit counts: the `j`-th exit from `v` uses the arc at position `ptr₀ v + j`, so the
visits are a monotone function of the vector of cumulative exits.
-/

open Finset

namespace Podc.RotorRouterRing

/-- A directed graph with a fixed cyclic order of the outgoing arcs of every node. -/
structure RotorGraph (V : Type*) where
  /-- Number of outgoing arcs of a node. -/
  deg : V → ℕ
  deg_pos : ∀ v, 0 < deg v
  /-- The head of the arc at a given position of the cyclic order. -/
  port : (v : V) → Fin (deg v) → V

/-- A configuration: agent counts and port pointers. -/
@[ext]
structure Config (V : Type*) where
  /-- Number of agents on each node. -/
  pos : V → ℕ
  /-- Port pointer of each node, a cyclic position read modulo the degree. -/
  ptr : V → ℕ

variable {V : Type*}

namespace RotorGraph

variable (G : RotorGraph V)

/-- The head of the arc at cyclic position `j mod deg v`. -/
def target (v : V) (j : ℕ) : V := G.port v ⟨j % G.deg v, Nat.mod_lt _ (G.deg_pos v)⟩

variable [DecidableEq V]

/-- Among `m` agents released one by one from `v` when its pointer is at `p`, the number that go
to `u`. -/
def sent (v : V) (p m : ℕ) (u : V) : ℕ := Nat.count (fun j => G.target v (p + j) = u) m

lemma sent_add (v : V) (p a b : ℕ) (u : V) :
    G.sent v p (a + b) u = G.sent v p a u + G.sent v (p + a) b u := by
  unfold sent
  rw [Nat.count_add]
  simp only [add_assoc]

lemma sent_mono (v : V) (p : ℕ) {a b : ℕ} (h : a ≤ b) (u : V) :
    G.sent v p a u ≤ G.sent v p b u := Nat.count_monotone _ h

variable [Fintype V]

lemma sum_sent (v : V) (p m : ℕ) : ∑ u, G.sent v p m u = m := by
  induction m with
  | zero => simp [sent]
  | succ m ih =>
    have : ∀ u, G.sent v p (m + 1) u = G.sent v p m u + if G.target v (p + m) = u then 1 else 0 :=
      fun u => by simp [sent, Nat.count_succ]
    simp only [this, Finset.sum_add_distrib, ih, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- One synchronous round with delays `d`: `min (pos v) (d v)` agents stay on `v`, the others
are released one by one along consecutive arcs starting at the pointer. -/
def step (c : Config V) (d : V → ℕ) : Config V where
  pos u := min (c.pos u) (d u) + ∑ v, G.sent v (c.ptr v) (c.pos v - d v) u
  ptr v := c.ptr v + (c.pos v - d v)

/-- The execution of a delayed deployment `D` (delays `D t` in round `t ≥ 1`) from `c₀`:
`run c₀ D t` is the configuration at the start of round `t + 1`. -/
def run (c₀ : Config V) (D : ℕ → V → ℕ) : ℕ → Config V
  | 0 => c₀
  | t + 1 => G.step (run c₀ D t) (D (t + 1))

/-- The undelayed deployment (the rotor-router system `R[k]` itself). -/
def undelayed : ℕ → V → ℕ := fun _ _ => 0

/-- Number of agents released from `v` in round `t + 1`. -/
def moved (c₀ : Config V) (D : ℕ → V → ℕ) (t : ℕ) (v : V) : ℕ :=
  (G.run c₀ D t).pos v - D (t + 1) v

/-- Cumulative number of exits from `v` in rounds `1, …, t` (the paper's `e_v^D(t)`). -/
def exits (c₀ : Config V) (D : ℕ → V → ℕ) (t : ℕ) (v : V) : ℕ :=
  ∑ s ∈ range t, G.moved c₀ D s v

/-- The paper's `n_v^D(t)`: initial agents on `v` plus arrivals at `v` in rounds `1, …, t`. -/
def visits (c₀ : Config V) (D : ℕ → V → ℕ) (t : ℕ) (u : V) : ℕ :=
  c₀.pos u + ∑ s ∈ range t, ∑ w, G.sent w ((G.run c₀ D s).ptr w) (G.moved c₀ D s w) u

/-- Visits as a function of a vector `E` of cumulative exit counts. -/
def visitsOf (c₀ : Config V) (E : V → ℕ) (u : V) : ℕ :=
  c₀.pos u + ∑ w, G.sent w (c₀.ptr w) (E w) u

/-- All nodes have been visited by the end of round `t`. -/
def Covered (c₀ : Config V) (D : ℕ → V → ℕ) (t : ℕ) : Prop := ∀ v, 0 < G.visits c₀ D t v

/-- `T` is the cover time of the deployment: covered after `T` rounds, not before. -/
def CoverTime (c₀ : Config V) (D : ℕ → V → ℕ) (T : ℕ) : Prop :=
  G.Covered c₀ D T ∧ ∀ t < T, ¬ G.Covered c₀ D t

variable {G}
variable (c₀ : Config V) (D : ℕ → V → ℕ)

lemma exits_succ (t : ℕ) (v : V) : G.exits c₀ D (t + 1) v = G.exits c₀ D t v + G.moved c₀ D t v := by
  simp [exits, Finset.sum_range_succ]

lemma ptr_run (t : ℕ) (v : V) : (G.run c₀ D t).ptr v = c₀.ptr v + G.exits c₀ D t v := by
  induction t with
  | zero => simp [run, exits]
  | succ t ih =>
    simp only [run, step, exits_succ, ih, moved]
    ring

lemma sum_sent_run (t : ℕ) (w u : V) :
    ∑ s ∈ range t, G.sent w ((G.run c₀ D s).ptr w) (G.moved c₀ D s w) u
      = G.sent w (c₀.ptr w) (G.exits c₀ D t w) u := by
  induction t with
  | zero => simp [exits, sent]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, exits_succ, G.sent_add, ptr_run]

lemma visits_eq_visitsOf (t : ℕ) : G.visits c₀ D t = G.visitsOf c₀ (G.exits c₀ D t) := by
  funext u
  simp only [visits, visitsOf]
  rw [Finset.sum_comm]
  simp only [sum_sent_run]

/-- Agents present = visits so far minus exits so far. -/
lemma pos_add_exits (t : ℕ) (v : V) :
    (G.run c₀ D t).pos v + G.exits c₀ D t v = G.visits c₀ D t v := by
  induction t generalizing v with
  | zero => simp [run, exits, visits]
  | succ t ih =>
    have hv : G.visits c₀ D (t + 1) v = G.visits c₀ D t v +
        ∑ w, G.sent w ((G.run c₀ D t).ptr w) (G.moved c₀ D t w) v := by
      simp only [visits, Finset.sum_range_succ]; ring
    rw [hv, ← ih, exits_succ]
    simp only [run, step, moved]
    have : min ((G.run c₀ D t).pos v) (D (t + 1) v) + ((G.run c₀ D t).pos v - D (t + 1) v)
        = (G.run c₀ D t).pos v := by omega
    omega

lemma exits_le_visits (t : ℕ) (v : V) : G.exits c₀ D t v ≤ G.visits c₀ D t v := by
  rw [← pos_add_exits (G := G)]; omega

/-- The recurrence (2) of the paper: `e_v(t+1) = n_v(t) - D(v,t+1)` (truncated at the current
number of exits when more agents are stopped than present). -/
lemma exits_succ_eq (t : ℕ) (v : V) :
    G.exits c₀ D (t + 1) v = max (G.exits c₀ D t v) (G.visits c₀ D t v - D (t + 1) v) := by
  rw [exits_succ]
  have h := pos_add_exits (G := G) c₀ D t v
  simp only [moved]
  omega

lemma exits_mono_time {s t : ℕ} (h : s ≤ t) (v : V) : G.exits c₀ D s v ≤ G.exits c₀ D t v := by
  induction h with
  | refl => rfl
  | step _ ih => rw [exits_succ]; omega

lemma visitsOf_mono {c₀ : Config V} {E F : V → ℕ} (h : E ≤ F) : G.visitsOf c₀ E ≤ G.visitsOf c₀ F := by
  intro u
  simp only [visitsOf]
  gcongr with w
  exact G.sent_mono w _ (h w) u

lemma visits_mono_time {s t : ℕ} (h : s ≤ t) : G.visits c₀ D s ≤ G.visits c₀ D t := by
  rw [visits_eq_visitsOf, visits_eq_visitsOf]
  exact visitsOf_mono (fun v => exits_mono_time c₀ D h v)

lemma Covered.mono {s t : ℕ} (hst : s ≤ t) (h : G.Covered c₀ D s) : G.Covered c₀ D t :=
  fun v => lt_of_lt_of_le (h v) (visits_mono_time c₀ D hst v)

end RotorGraph

end Podc.RotorRouterRing
