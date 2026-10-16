import Papers.PODC2015.CrashConsensusDigraph.Async

/-!
# Asynchronous crash-prone message passing on a digraph (crashes at arbitrary times)

The model of Section 4 with general crash faults. We reuse the asynchronous model of
`Papers/PODC2020/AsyncApproxBCDirected/AsyncModel.lean` (deterministic event-driven algorithms,
reliable FIFO links with adversarial finite delays, irrevocable outputs) with a *time-varying*
set of crashed nodes:

* a crash schedule `ct : V → Option ℕ`: `ct x = some c` means that `x` crashes at time `c`;
  `crashedAt ct t` is the set of nodes crashed at time `t`. Step `t` of the execution is the
  PODC 2020 step with faulty set `crashedAt ct t`: a crashed node takes no step (it processes no
  message, hence sends nothing new), messages to crashed nodes are dropped, but messages a node
  sent before crashing stay in the channels and may (or may not) be delivered. Since fairness is
  only required for links between nodes that never crash, this covers crashes in the middle of a
  broadcast. A node with `ct x = some 0` never starts (initially dead).
* Event sequences contain no Byzantine events (`.byz`).
* `FairC`: on every link between nodes that never crash, a non-empty channel is eventually served.
* `CrashSolvesGenOn I A G f ε`: for every crash schedule with at most `f` faulty nodes, all inputs
  in `I` and every event sequence: ε-agreement and validity (outputs in the convex hull of all
  inputs) for the nodes that never crash, and termination in fair executions.

`crashSolvesOn_of_gen`: this specializes to the initially-dead model `CrashSolvesOn` of
`Async.lean` (constant schedule), so Theorem 6 holds in this model too (`theorem6_gen`).
-/

open Finset

set_option linter.unusedSectionVars false

-- CSLib candidate (asynchronous crash-prone message passing on digraphs)

namespace CrashConsensusDigraph

open AsyncApproxBCDirected

variable {V M S : Type*} [DecidableEq V] [Fintype V]

open Classical in
/-- The nodes crashed at time `t` under the crash schedule `ct`. -/
noncomputable def crashedAt (ct : V → Option ℕ) (t : ℕ) : Finset V :=
  univ.filter fun x => ∃ c, ct x = some c ∧ c ≤ t

theorem mem_crashedAt {ct : V → Option ℕ} {t : ℕ} {x : V} :
    x ∈ crashedAt ct t ↔ ∃ c, ct x = some c ∧ c ≤ t := by
  classical
  unfold crashedAt
  rw [mem_filter]
  simp

theorem notMem_crashedAt_of_none {ct : V → Option ℕ} {t : ℕ} {x : V} (h : ct x = none) :
    x ∉ crashedAt ct t := by
  rw [mem_crashedAt]; simp [h]

theorem crashedAt_mono {ct : V → Option ℕ} {t t' : ℕ} (h : t ≤ t') {x : V}
    (hx : x ∈ crashedAt ct t) : x ∈ crashedAt ct t' := by
  rw [mem_crashedAt] at hx ⊢
  obtain ⟨c, hc, hct⟩ := hx
  exact ⟨c, hc, hct.trans h⟩

/-- At most `f` nodes ever crash. -/
def CrashAdm (ct : V → Option ℕ) (f : ℕ) : Prop :=
  ∃ F : Finset V, F.card ≤ f ∧ ∀ x c, ct x = some c → x ∈ F

section Run

variable (A : Algorithm V M S) (G : Digraph V) [DecidableRel G.Adj] (ct : V → Option ℕ)

/-- The execution determined by the crash schedule, the inputs and the event sequence. -/
noncomputable def runC (inp : V → ℝ) (ev : ℕ → Event V M) : ℕ → Config V M S
  | 0 => init A G (crashedAt ct 0) inp
  | t + 1 => step A G (crashedAt ct t) (runC inp ev t) (ev t)

theorem runC_zero (inp : V → ℝ) (ev : ℕ → Event V M) :
    runC A G ct inp ev 0 = init A G (crashedAt ct 0) inp := rfl

theorem runC_succ (inp : V → ℝ) (ev : ℕ → Event V M) (t : ℕ) :
    runC A G ct inp ev (t + 1) = step A G (crashedAt ct t) (runC A G ct inp ev t) (ev t) := rfl

/-- Fairness: on every link between nodes that never crash, a non-empty channel is eventually
served. -/
def FairC (inp : V → ℝ) (ev : ℕ → Event V M) : Prop :=
  ∀ x y, ct x = none → ct y = none → ∀ t, (runC A G ct inp ev t).chan x y ≠ [] →
    ∃ t' ≥ t, ev t' = .deliver x y

end Run

/-- **Asynchronous approximate crash consensus** (Section 4) for inputs in `I`, tolerating up to
`f` crashes at arbitrary times. -/
def CrashSolvesGenOn (I : Set ℝ) (A : Algorithm V M S) (G : Digraph V) [DecidableRel G.Adj]
    (f : ℕ) (ε : ℝ) : Prop :=
  ∀ ct : V → Option ℕ, CrashAdm ct f → ∀ (inp : V → ℝ), (∀ w, inp w ∈ I) →
    ∀ (ev : ℕ → Event V M), (∀ t x y m, ev t ≠ .byz x y m) →
    -- ε-agreement
    (∀ t v u y z, ct v = none → ct u = none → (runC A G ct inp ev t).dec v = some y →
      (runC A G ct inp ev t).dec u = some z → |y - z| ≤ ε) ∧
    -- validity: in the convex hull of all inputs
    (∀ t v y, ct v = none → (runC A G ct inp ev t).dec v = some y →
      (∃ w, inp w ≤ y) ∧ ∃ w, y ≤ inp w) ∧
    -- termination
    (FairC A G ct inp ev → ∀ v, ct v = none → ∃ t y, (runC A G ct inp ev t).dec v = some y)

/-! ## Initially dead nodes as a special case -/

/-- The schedule in which exactly the nodes of `B` are crashed from the start. -/
def deadAt (B : Finset V) : V → Option ℕ := fun x => if x ∈ B then some 0 else none

theorem crashedAt_deadAt (B : Finset V) (t : ℕ) : crashedAt (deadAt B) t = B := by
  ext x
  rw [mem_crashedAt]
  by_cases hx : x ∈ B <;> simp [deadAt, hx]

theorem deadAt_eq_none {B : Finset V} {x : V} : deadAt B x = none ↔ x ∉ B := by
  by_cases hx : x ∈ B <;> simp [deadAt, hx]

theorem runC_deadAt {A : Algorithm V M S} {G : Digraph V} [DecidableRel G.Adj] (B : Finset V)
    (inp : V → ℝ) (ev : ℕ → Event V M) (t : ℕ) :
    runC A G (deadAt B) inp ev t = run A G B inp ev t := by
  induction t with
  | zero => simp only [runC_zero, crashedAt_deadAt]; rfl
  | succ t ih => rw [runC_succ, ih, crashedAt_deadAt]; rfl

/-- An algorithm tolerating crashes at arbitrary times tolerates initially dead nodes. -/
theorem crashSolvesOn_of_gen {I : Set ℝ} {A : Algorithm V M S} {G : Digraph V}
    [DecidableRel G.Adj] {f : ℕ} {ε : ℝ} (h : CrashSolvesGenOn I A G f ε) :
    CrashSolvesOn I A G f ε := by
  intro B hB inp hinp ev hev
  have hadm : CrashAdm (deadAt B) f :=
    ⟨B, hB, fun x c hc => by by_contra hx; simp [deadAt, hx] at hc⟩
  obtain ⟨h1, h2, h3⟩ := h (deadAt B) hadm inp hinp ev hev
  refine ⟨fun t v u y z hv hu hy hz => ?_, fun t v y hv hy => ?_, fun hfair v hv => ?_⟩
  · rw [← runC_deadAt] at hy hz
    exact h1 t v u y z (deadAt_eq_none.mpr hv) (deadAt_eq_none.mpr hu) hy hz
  · rw [← runC_deadAt] at hy
    exact h2 t v y (deadAt_eq_none.mpr hv) hy
  · have hfair' : FairC A G (deadAt B) inp ev := by
      intro x y hx hy t hne
      rw [runC_deadAt] at hne
      exact hfair x y (deadAt_eq_none.mp hx) (deadAt_eq_none.mp hy) t hne
    obtain ⟨t, z, hz⟩ := h3 hfair' v (deadAt_eq_none.mpr hv)
    exact ⟨t, z, by rwa [runC_deadAt] at hz⟩

/-- **Theorem 6** in the model with crashes at arbitrary times. -/
theorem theorem6_gen {A : Algorithm V M S} {G : Digraph V} [DecidableRel G.Adj] {f : ℕ} {ε : ℝ}
    {I : Set ℝ} {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : ε < b - a)
    (hA : CrashSolvesGenOn I A G f ε) : CCA G f :=
  theorem6 ha hb hab (crashSolvesOn_of_gen hA)

end CrashConsensusDigraph
