import Mathlib
import Podc.Stabilization.Daemon

/-!
# Stateless computation: the model

Dolev, Erdmann, Lutz, Schapira, Zair, *Stateless Computation*, PODC 2017 (arXiv 1611.10068v1),
Section 2.

A network is a directed graph `G` (Mathlib's `Digraph V`) on a finite node set `V`.
Every node `i` has a private input `x i : X` and a *reaction function*
`δ i : (labels of the incoming arcs of i) → X → (labels of the outgoing arcs of i) × Y`.
Nodes have no other state: the global state is the *labeling* `ℓ : Arc G → L` of all arcs
(and the current outputs). A *schedule* `σ : ℕ → Finset V` activates, at step `t + 1`, the nodes
in `σ t`; an activated node applies its reaction function to its current incoming labels and
overwrites its outgoing labels and its output.

The paper calls the label space `Σ`; here it is the type `L` (`Σ` is Lean syntax).

## Main definitions

* `Arc G`, `inLab ℓ i`: arcs and the incoming labels of a node.
* `Protocol G L X Y`: a stateless protocol (the vector of reaction functions).
* `step`, `run`, `outputs`: executions under a schedule.
* `IsRFair r σ`: every node is activated in every window of `r` consecutive steps
  (and every step activates a nonempty set, as in the paper).
* `IsStable P x ℓ`: `ℓ` is a fixed point of every reaction function (a *stable labeling*).
* `OutputStabilizing r P`, `LabelStabilizing r P`: the paper's output / label r-stabilization.
* `syncRun`, `syncOut`: the synchronous execution (Part II of the paper).
-/

-- CSLib candidate: the stateless-protocol model with r-fair schedules (this file).
namespace StatelessComputation

variable {V : Type*} {L X Y : Type*}

/-- The arcs of the digraph `G`: pairs `(i, j)` with `G.Adj i j` (an arc from `i` to `j`). -/
abbrev Arc (G : Digraph V) := {p : V × V // G.Adj p.1 p.2}

/-- In-neighbours of `i`. -/
abbrev InNbr (G : Digraph V) (i : V) := {u : V // G.Adj u i}

/-- Out-neighbours of `i`. -/
abbrev OutNbr (G : Digraph V) (i : V) := {w : V // G.Adj i w}

/-- A labeling of the arcs of `G` by labels from `L`. -/
abbrev Labeling (G : Digraph V) (L : Type*) := Arc G → L

/-- The labels on the incoming arcs of node `i`. -/
def inLab {G : Digraph V} (ℓ : Labeling G L) (i : V) : InNbr G i → L :=
  fun u => ℓ ⟨(u.1, i), u.2⟩

/-- A stateless protocol on `G` with label space `L`, inputs `X` and outputs `Y`: one
reaction function per node, mapping incoming labels and the private input to outgoing labels
and an output value. (In the paper `X = Y = {0,1}`.) -/
structure Protocol (G : Digraph V) (L X Y : Type*) where
  /-- The reaction function of node `i`. -/
  δ : (i : V) → (InNbr G i → L) → X → (OutNbr G i → L) × Y

namespace Protocol

variable {G : Digraph V} [DecidableEq V] (P : Protocol G L X Y) (x : V → X)

/-- One global step: the nodes in `T` react to their current incoming labels. -/
def step (ℓ : Labeling G L) (T : Finset V) : Labeling G L := fun e =>
  if e.1.1 ∈ T then (P.δ e.1.1 (inLab ℓ e.1.1) (x e.1.1)).1 ⟨e.1.2, e.2⟩ else ℓ e

/-- The labeling sequence `ℓ⁰, ℓ¹, …` from the initial labeling `ℓ0` under schedule `σ`
(`σ t` is the set activated at step `t + 1`, i.e. the paper's `σ(t+1)`). -/
def run (ℓ0 : Labeling G L) (σ : ℕ → Finset V) : ℕ → Labeling G L
  | 0 => ℓ0
  | t + 1 => P.step x (run ℓ0 σ t) (σ t)

/-- The output sequence (`y0` = arbitrary initial outputs). -/
def outputs (ℓ0 : Labeling G L) (y0 : V → Y) (σ : ℕ → Finset V) : ℕ → V → Y
  | 0 => y0
  | t + 1 => fun i =>
      if i ∈ σ t then (P.δ i (inLab (P.run x ℓ0 σ t) i) (x i)).2 else outputs ℓ0 y0 σ t i

/-- A *stable labeling* (for input `x`): a fixed point of every reaction function. -/
def IsStable (ℓ : Labeling G L) : Prop :=
  ∀ i (w : OutNbr G i), (P.δ i (inLab ℓ i) (x i)).1 w = ℓ ⟨(i, w.1), w.2⟩

@[simp] lemma run_zero (ℓ0 : Labeling G L) (σ : ℕ → Finset V) : P.run x ℓ0 σ 0 = ℓ0 := rfl

lemma run_succ (ℓ0 : Labeling G L) (σ : ℕ → Finset V) (t : ℕ) :
    P.run x ℓ0 σ (t + 1) = P.step x (P.run x ℓ0 σ t) (σ t) := rfl

lemma step_of_mem {ℓ : Labeling G L} {T : Finset V} {e : Arc G} (h : e.1.1 ∈ T) :
    P.step x ℓ T e = (P.δ e.1.1 (inLab ℓ e.1.1) (x e.1.1)).1 ⟨e.1.2, e.2⟩ := by
  simp [step, h]

lemma step_of_not_mem {ℓ : Labeling G L} {T : Finset V} {e : Arc G} (h : e.1.1 ∉ T) :
    P.step x ℓ T e = ℓ e := by
  simp [step, h]

/-- A stable labeling is a fixed point of every global step. -/
lemma IsStable.step_eq {ℓ : Labeling G L} (h : P.IsStable x ℓ) (T : Finset V) :
    P.step x ℓ T = ℓ := by
  funext e
  by_cases he : e.1.1 ∈ T
  · rw [P.step_of_mem x he]; exact h e.1.1 ⟨e.1.2, e.2⟩
  · exact P.step_of_not_mem x he

end Protocol

/-- A sequence converges (is eventually constant): `Filter.EventuallyConst f atTop`
(`converges_iff`). -/
def Converges {α : Type*} (f : ℕ → α) : Prop := Filter.EventuallyConst f Filter.atTop

lemma converges_iff {α : Type*} {f : ℕ → α} : Converges f ↔ ∃ a, ∃ T, ∀ t, T ≤ t → f t = a :=
  Filter.eventuallyConst_atTop.trans
    ⟨fun ⟨T, h⟩ => ⟨f T, T, h⟩, fun ⟨_, T, h⟩ => ⟨T, fun t ht => (h t ht).trans (h T le_rfl).symm⟩⟩

open Cslib.SelfStabilization in
/-- An `r`-fair schedule: every step activates a nonempty set, and every node is activated at
least once in every `r` consecutive steps (`r`-bounded fairness of the daemon). -/
def IsRFair (r : ℕ) (σ : ℕ → Finset V) : Prop :=
  (∀ t, (σ t).Nonempty) ∧ BoundedFair r (fun t => (σ t : Set V))

/-- An `r`-fair schedule is `r'`-fair for every `r' ≥ r`. -/
lemma IsRFair.mono {r r' : ℕ} {σ : ℕ → Finset V} (h : IsRFair r σ) (hr : r ≤ r') :
    IsRFair r' σ :=
  ⟨h.1, h.2.mono hr⟩

/-- The synchronous schedule is `1`-fair (if there is a node). -/
lemma isRFair_sync [Fintype V] [Nonempty V] : IsRFair 1 (fun _ => (Finset.univ : Finset V)) :=
  ⟨fun _ => Finset.univ_nonempty, fun t v => ⟨t, le_rfl, by omega, Finset.mem_univ v⟩⟩

variable {G : Digraph V} [DecidableEq V]

/-- Output `r`-stabilization: for every input, initial labeling, initial outputs and `r`-fair
schedule, every node's output sequence converges. -/
def OutputStabilizing (r : ℕ) (P : Protocol G L X Y) : Prop :=
  ∀ x ℓ0 y0 σ, IsRFair r σ → ∀ i : V, Converges (fun t => P.outputs x ℓ0 y0 σ t i)

/-- Label `r`-stabilization: output `r`-stabilization and, in addition, the labeling sequence
converges for every input, initial labeling and `r`-fair schedule. -/
def LabelStabilizing (r : ℕ) (P : Protocol G L X Y) : Prop :=
  OutputStabilizing r P ∧ ∀ x ℓ0 σ, IsRFair r σ → Converges (P.run x ℓ0 σ)

/-! ### Synchronous executions (Part II of the paper) -/

namespace Protocol

variable (P : Protocol G L X Y) (x : V → X)

/-- The synchronous global transition: every node reacts. -/
def syncStep (ℓ : Labeling G L) : Labeling G L := fun e =>
  (P.δ e.1.1 (inLab ℓ e.1.1) (x e.1.1)).1 ⟨e.1.2, e.2⟩

/-- The output of node `i` when it reacts to labeling `ℓ`. -/
def out (ℓ : Labeling G L) (i : V) : Y := (P.δ i (inLab ℓ i) (x i)).2

/-- The synchronous labeling sequence `ℓᵗ = syncStep^[t] ℓ0`. The output of node `i` at time
`t + 1` is `P.out x (P.syncRun x ℓ0 t) i`. -/
def syncRun (ℓ0 : Labeling G L) (t : ℕ) : Labeling G L := (P.syncStep x)^[t] ℓ0

omit [DecidableEq V] in
lemma syncRun_succ (ℓ0 : Labeling G L) (t : ℕ) :
    P.syncRun x ℓ0 (t + 1) = P.syncStep x (P.syncRun x ℓ0 t) :=
  Function.iterate_succ_apply' _ _ _

lemma syncStep_eq_step [Fintype V] (ℓ : Labeling G L) :
    P.syncStep x ℓ = P.step x ℓ Finset.univ := by
  funext e; simp [syncStep, step]

/-- The synchronous run is the run under the schedule activating everybody. -/
lemma syncRun_eq_run [Fintype V] (ℓ0 : Labeling G L) (t : ℕ) :
    P.syncRun x ℓ0 t = P.run x ℓ0 (fun _ => Finset.univ) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [syncRun_succ, run_succ, ih, syncStep_eq_step]

/-- `P` is label-stabilizing under the synchronous schedule. -/
def SyncLabelStabilizing : Prop := ∀ x ℓ0, Converges (P.syncRun x ℓ0)

/-- `P` computes `f` under the synchronous schedule: from every initial labeling, every
node's output converges to `f x`. -/
def SyncComputes (f : (V → X) → Y) : Prop :=
  ∀ x ℓ0 (i : V), ∃ T, ∀ t, T ≤ t → P.out x (P.syncRun x ℓ0 t) i = f x

end Protocol

end StatelessComputation
