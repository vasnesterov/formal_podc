import Cslib.Computability.Distributed.ApproxConsensus.Async.Replay
import Cslib.Computability.Distributed.ApproxConsensus.DigraphConditions
import Mathlib

/-!
# Asynchronous approximate consensus with crash faults: Theorem 6 and Lemma 1

Section 4. We use the asynchronous message-passing model on digraphs of
`Cslib/Computability/Distributed/ApproxConsensus/Async/Model.lean` (event-driven deterministic algorithms,
reliable FIFO links with adversarial finite delays, fairness = every non-empty link between
correct nodes is eventually served, irrevocable outputs).

* `CrashSolvesOn I A G f ε` — asynchronous approximate consensus tolerating `f` *initially dead*
  nodes: for every set `B` of at most `f` nodes that never take a step (crashed before the start),
  all inputs in `I`, and every event sequence without Byzantine events, outputs of fault-free nodes
  are within `ε` (ε-agreement), every output lies between two inputs (validity w.r.t. *all* inputs,
  as in the paper), and in fair executions every fault-free node outputs (termination).
  Initially dead nodes are a special case of crash faults, so an algorithm tolerating `f` crashes
  satisfies this; the impossibility below therefore holds for crash faults a fortiori.
* **Theorem 6** (`theorem6`): if such an algorithm exists (for an input range containing two
  values more than `ε` apart), then for every partition `L, C, R` of `V` with `L, R ≠ ∅`,
  `L ∪ C → R` or `C ∪ R → L` (`f + 1` distinct nodes with edges into the other side). This is
  condition CCA (`Cslib.ApproxConsensus.CCA`), equivalent to 2-reach (`cca_iff_twoReach`).
* **Lemma 1** (`lemma1`): under the condition of Theorem 6, `reachᵢ(Fᵢ) ∩ reachⱼ(Fⱼ) ≠ ∅` for all
  `Fᵢ ∌ i`, `Fⱼ ∌ j` of size `≤ f` — the key lemma of the sketched proof of Theorem 7.

The paper's proof of Theorem 6 is the classical "nodes in `L` cannot wait for `O(L)`" argument;
we make it precise by replaying executions (`exists_replay₂`, built on `sim_phase`): the
nodes of `O(R)` (resp. `O(L)`) are initially dead in two auxiliary executions with all inputs
`a` (resp. `b`), and their deliveries into `reach_v(·)` are replayed in one failure-free
execution with mixed inputs.
-/

open Finset

set_option linter.unusedSectionVars false

namespace CrashConsensusDigraph

open Cslib.ApproxConsensus Cslib.ApproxConsensus.Async

variable {V M S : Type*} [DecidableEq V] {A : Algorithm V M S} {G : Digraph V} [DecidableRel G.Adj]

/-- **Asynchronous approximate crash consensus** (Section 4) for inputs in `I`, tolerating up to
`f` initially dead nodes. -/
def CrashSolvesOn (I : Set ℝ) (A : Algorithm V M S) (G : Digraph V) [DecidableRel G.Adj] (f : ℕ)
    (ε : ℝ) : Prop :=
  ∀ B : Finset V, B.card ≤ f → ∀ (inp : V → ℝ), (∀ w, inp w ∈ I) → ∀ (ev : ℕ → Event V M),
    (∀ t x y m, ev t ≠ .byz x y m) →
    -- ε-agreement
    (∀ t v u y z, v ∉ B → u ∉ B → (run A G B inp ev t).dec v = some y →
      (run A G B inp ev t).dec u = some z → |y - z| ≤ ε) ∧
    -- validity: in the convex hull of all inputs
    (∀ t v y, v ∉ B → (run A G B inp ev t).dec v = some y → (∃ w, inp w ≤ y) ∧ ∃ w, y ≤ inp w) ∧
    -- termination
    (Fair A G B inp ev → ∀ v ∉ B, ∃ t y, (run A G B inp ev t).dec v = some y)

/-- Necessity of 2-reach for asynchronous approximate crash consensus. -/
theorem twoReach_of_crashSolvesOn [Fintype V] {f : ℕ} {ε : ℝ} {I : Set ℝ} {a b : ℝ} (ha : a ∈ I)
    (hb : b ∈ I) (hab : ε < b - a) (hA : CrashSolvesOn I A G f ε) : TwoReach G f := by
  classical
  intro Fu Fv u v hFu hFv hu hv
  by_contra hcon
  push Not at hcon
  set Rv : Finset V := univ.filter fun w => Reaches G Fv w v
  set Ru : Finset V := univ.filter fun w => Reaches G Fu w u
  have hdis : Disjoint Rv Ru := disjoint_left.mpr fun w h1 h2 => by
    simp only [Rv, Ru, mem_filter, mem_univ, true_and] at h1 h2; exact hcon w h1 h2
  have hvR : v ∈ Rv := by simp [Rv, Reaches.refl hv]
  have huR : u ∈ Ru := by simp [Ru, Reaches.refl hu]
  have hRvF : ∀ y ∈ Rv, y ∉ Fv ∧ y ∉ (∅ : Finset V) := fun y hy => by
    simp only [Rv, mem_filter, mem_univ, true_and] at hy; exact ⟨hy.1, notMem_empty y⟩
  have hRuF : ∀ y ∈ Ru, y ∉ Fu ∧ y ∉ (∅ : Finset V) := fun y hy => by
    simp only [Ru, mem_filter, mem_univ, true_and] at hy; exact ⟨hy.1, notMem_empty y⟩
  have hclv : ∀ x y, G.Adj x y → x ≠ y → y ∈ Rv → x ∉ Rv → x ∈ Fv ∨ x ∈ (∅ : Finset V) := by
    intro x y e _ hy hx
    left
    by_contra h
    simp only [Rv, mem_filter, mem_univ, true_and] at hy hx
    exact hx (hy.head e h)
  have hclu : ∀ x y, G.Adj x y → x ≠ y → y ∈ Ru → x ∉ Ru → x ∈ Fu ∨ x ∈ (∅ : Finset V) := by
    intro x y e _ hy hx
    left
    by_contra h
    simp only [Ru, mem_filter, mem_univ, true_and] at hy hx
    exact hx (hy.head e h)
  -- execution e₁: `Fv` initially dead, all inputs `a`; `v` decides `a`
  obtain ⟨-, hval₁, hterm₁⟩ := hA Fv hFv (fun _ => a) (fun _ => ha) roundRobin
    (fun t => roundRobin_ne_byz t)
  obtain ⟨T₁, y₁, hy₁⟩ := hterm₁ (roundRobin_fair _) v hv
  have hy₁a : y₁ = a := by
    obtain ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ := hval₁ T₁ v y₁ hv hy₁
    linarith
  -- execution e₂: `Fu` initially dead, all inputs `b`; `u` decides `b`
  obtain ⟨-, hval₂, hterm₂⟩ := hA Fu hFu (fun _ => b) (fun _ => hb) roundRobin
    (fun t => roundRobin_ne_byz t)
  obtain ⟨T₂, y₂, hy₂⟩ := hterm₂ (roundRobin_fair _) u hu
  have hy₂b : y₂ = b := by
    obtain ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ := hval₂ T₂ u y₂ hu hy₂
    linarith
  -- execution e₃: no faults, inputs `b` on `Ru` and `a` elsewhere; replay `e₁` on `Rv`, then `e₂`
  -- on `Ru` (messages from `Fv` into `Rv` and from `Fu` into `Ru` are delayed)
  set inp₃ : V → ℝ := fun w => if w ∈ Ru then b else a
  obtain ⟨ev₃, hev₃, h₁, h₂⟩ := exists_replay₂ (A := A) (B := ∅) hdis hRvF hRuF hclv hclu
    (inp₁ := fun _ => a) (inp₂ := fun _ => b) (inp := inp₃)
    (fun y hy => by simp [inp₃, disjoint_left.mp hdis hy]) (fun y hy => by simp [inp₃, hy])
    (fun t => roundRobin_ne_byz t) (fun t => roundRobin_ne_byz t) T₁ T₂
  obtain ⟨hconv₃, -, -⟩ := hA ∅ (by simp) inp₃
    (fun w => by simp only [inp₃]; split_ifs <;> assumption) ev₃
    (fun t x y m h => notMem_empty x (hev₃ t x y m h))
  have := hconv₃ (T₁ + T₂) v u a b (notMem_empty v) (notMem_empty u)
    (by rw [← (h₁.1 v hvR).2, hy₁, hy₁a]) (by rw [← (h₂.1 u huR).2, hy₂, hy₂b])
  rw [abs_le] at this
  linarith [this.1]

/-- **Theorem 6.** If an asynchronous approximate consensus algorithm tolerating `f` crash
(initially dead) nodes exists for `G` (with `ε`-agreement, for an input range containing two
values more than `ε` apart, e.g. `0` and `2ε` as in the paper), then for every partition
`L, C, R` of `V` with `L, R` non-empty, `L ∪ C → R` or `C ∪ R → L`. -/
theorem theorem6 [Fintype V] {f : ℕ} {ε : ℝ} {I : Set ℝ} {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I)
    (hab : ε < b - a) (hA : CrashSolvesOn I A G f ε) : CCA G f :=
  cca_iff_twoReach.mpr (twoReach_of_crashSolvesOn ha hb hab hA)

/-- Theorem 6 for arbitrary real inputs and `ε > 0`. -/
theorem theorem6' [Fintype V] {f : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hA : CrashSolvesOn Set.univ A G f ε) : CCA G f :=
  theorem6 (a := 0) (b := 2 * ε) (Set.mem_univ _) (Set.mem_univ _) (by linarith) hA

/-- **Lemma 1** (graph part): under the condition of Theorem 6, for all `i, j`, `Fᵢ ∌ i`,
`Fⱼ ∌ j` with `|Fᵢ|, |Fⱼ| ≤ f`, some node reaches `i` in `G_{Fᵢ}` and `j` in `G_{Fⱼ}`, i.e.
`reachᵢ(Fᵢ) ∩ reachⱼ(Fⱼ) ≠ ∅`; hence the heard sets of two nodes satisfying Condition WAIT
intersect. -/
theorem lemma1 [Fintype V] {f : ℕ} (hG : CCA G f) {Fi Fj : Finset V} {i j : V}
    (hFi : Fi.card ≤ f) (hFj : Fj.card ≤ f) (hi : i ∉ Fi) (hj : j ∉ Fj) :
    ∃ w, Reaches G Fi w i ∧ Reaches G Fj w j := by
  obtain ⟨w, h1, h2⟩ := cca_iff_twoReach.mp hG Fj Fi j i hFj hFi hj hi
  exact ⟨w, h1, h2⟩

end CrashConsensusDigraph
