import Papers.PODC2020.AsyncApproxBCDirected.Necessity
import Papers.PODC2020.AsyncApproxBCDirected.Conditions

/-!
# Asynchronous approximate consensus with crash faults: Theorem 6 and Lemma 1

Section 4. We reuse the asynchronous message-passing model on digraphs of
`Papers/PODC2020/AsyncApproxBCDirected/AsyncModel.lean` (event-driven deterministic algorithms,
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
  condition CCA of the PODC 2020 formalization (`AsyncApproxBCDirected.CCA`), equivalent to
  2-reach (`theorem17b`).
* **Lemma 1** (`lemma1`): under the condition of Theorem 6, `reachᵢ(Fᵢ) ∩ reachⱼ(Fⱼ) ≠ ∅` for all
  `Fᵢ ∌ i`, `Fⱼ ∌ j` of size `≤ f` — the key lemma of the sketched proof of Theorem 7.

The paper's proof of Theorem 6 is the classical "nodes in `L` cannot wait for `O(L)`" argument;
we make it precise by replaying executions (`sim_phase` of the PODC 2020 formalization): the
nodes of `O(R)` (resp. `O(L)`) are initially dead in two auxiliary executions with all inputs
`a` (resp. `b`), and their deliveries into `reach_v(·)` are replayed in one failure-free
execution with mixed inputs.
-/

open Finset

set_option linter.unusedSectionVars false

namespace CrashConsensusDigraph

open AsyncApproxBCDirected

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

theorem proj_empty_ne_byz (R : Finset V) (C : Config V M S) (e : Event V M) (x y : V) (m : M) :
    proj R ∅ C e ≠ .byz x y m := by
  cases e with
  | deliver a b =>
    simp only [proj, notMem_empty, ite_false]
    split_ifs
    · split <;> simp
    · simp
  | byz => simp [proj]
  | skip => simp [proj]

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
  have hRvF : ∀ y ∈ Rv, y ∉ Fv := fun y hy => by
    simp only [Rv, mem_filter, mem_univ, true_and] at hy; exact hy.1
  have hRuF : ∀ y ∈ Ru, y ∉ Fu := fun y hy => by
    simp only [Ru, mem_filter, mem_univ, true_and] at hy; exact hy.1
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
  -- execution e₁: `Fv` initially dead, all inputs `a`
  set inp₁ : V → ℝ := fun _ => a
  set ev₁ : ℕ → Event V M := roundRobin
  obtain ⟨-, hval₁, hterm₁⟩ := hA Fv hFv inp₁ (fun _ => ha) ev₁ (fun t => roundRobin_ne_byz t)
  obtain ⟨T₁, y₁, hy₁⟩ := hterm₁ (roundRobin_fair inp₁) v hv
  have hy₁0 : y₁ = a := by
    obtain ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ := hval₁ T₁ v y₁ hv hy₁
    simp only [inp₁] at h1 h2; linarith
  -- execution e₂: `Fu` initially dead, all inputs `b`
  set inp₂ : V → ℝ := fun _ => b
  set ev₂ : ℕ → Event V M := roundRobin
  obtain ⟨-, hval₂, hterm₂⟩ := hA Fu hFu inp₂ (fun _ => hb) ev₂ (fun t => roundRobin_ne_byz t)
  obtain ⟨T₂, y₂, hy₂⟩ := hterm₂ (roundRobin_fair inp₂) u hu
  have hy₂ε : y₂ = b := by
    obtain ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ := hval₂ T₂ u y₂ hu hy₂
    simp only [inp₂] at h1 h2; linarith
  -- execution e₃: no faults, inputs `b` on `Ru` and `a` elsewhere; replay `e₁` on `Rv`, then `e₂`
  -- on `Ru` (messages from `Fv` into `Rv` and from `Fu` into `Ru` are delayed)
  set inp₃ : V → ℝ := fun w => if w ∈ Ru then b else a
  set ev₃ : ℕ → Event V M := fun t =>
    if t < T₁ then proj Rv ∅ (run A G Fv inp₁ ev₁ t) (ev₁ t)
    else if t < T₁ + T₂ then proj Ru ∅ (run A G Fu inp₂ ev₂ (t - T₁)) (ev₂ (t - T₁))
    else .skip
  have hev₃ : ∀ t x y m, ev₃ t ≠ .byz x y m := by
    intro t x y m
    simp only [ev₃]
    split_ifs
    · exact proj_empty_ne_byz _ _ _ _ _ _
    · exact proj_empty_ne_byz _ _ _ _ _ _
    · simp
  obtain ⟨hconv₃, -, -⟩ := hA ∅ (by simp) inp₃
    (fun w => by simp only [inp₃]; split_ifs <;> assumption) ev₃ hev₃
  -- initial agreements
  have h0v : Agree Rv (run A G Fv inp₁ ev₁ 0) (run A G ∅ inp₃ ev₃ 0) := by
    refine ⟨fun y hy => ?_, fun x hx y hy => ?_⟩
    · have : y ∉ Ru := disjoint_left.mp hdis hy
      simp [run, init, inp₃, inp₁, this]
    · have hxu : x ∉ Ru := disjoint_left.mp hdis hx
      simp [run, init, inp₃, inp₁, hxu, hRvF x hx, sendTo, hRvF y hy]
  have h0u : Agree Ru (run A G Fu inp₂ ev₂ 0) (run A G ∅ inp₃ ev₃ 0) := by
    refine ⟨fun y hy => ?_, fun x hx y hy => ?_⟩
    · simp [run, init, inp₃, inp₂, hy]
    · simp [run, init, inp₃, inp₂, hx, hRuF x hx, sendTo, hRuF y hy]
  -- phase 1
  obtain ⟨p1a, p1b⟩ := sim_phase (A := A) (B := Fv) (B' := ∅) hRvF (fun y _ => notMem_empty y) hclv
    inp₁ inp₃ ev₁ ev₃ (fun t => roundRobin_ne_byz t) 0 T₁
    (fun k hk => by simp only [ev₃, Nat.zero_add, hk, ite_true]) (by simpa using h0v)
  -- phase 2
  have h1u : Agree Ru (run A G Fu inp₂ ev₂ 0) (run A G ∅ inp₃ ev₃ T₁) :=
    h0u.of_agreeOut (by simpa using p1b) hdis.symm
  obtain ⟨p2a, p2b⟩ := sim_phase (A := A) (B := Fu) (B' := ∅) hRuF (fun y _ => notMem_empty y) hclu
    inp₂ inp₃ ev₂ ev₃ (fun t => roundRobin_ne_byz t) T₁ T₂
    (fun k hk => by
      simp only [ev₃, show ¬ (T₁ + k < T₁) by omega, ite_false,
        show T₁ + k < T₁ + T₂ by omega, ite_true, Nat.add_sub_cancel_left]) h1u
  have h2v : Agree Rv (run A G Fv inp₁ ev₁ T₁) (run A G ∅ inp₃ ev₃ (T₁ + T₂)) :=
    (by simpa using p1a : Agree Rv _ _).of_agreeOut p2b hdis
  have hdv : (run A G ∅ inp₃ ev₃ (T₁ + T₂)).dec v = some a := by
    rw [← (h2v.1 v hvR).2, hy₁, hy₁0]
  have hdu : (run A G ∅ inp₃ ev₃ (T₁ + T₂)).dec u = some b := by
    rw [← (p2a.1 u huR).2, hy₂, hy₂ε]
  have := hconv₃ (T₁ + T₂) v u a b (notMem_empty v) (notMem_empty u) hdv hdu
  rw [abs_le] at this
  linarith [this.1]

/-- **Theorem 6.** If an asynchronous approximate consensus algorithm tolerating `f` crash
(initially dead) nodes exists for `G` (with `ε`-agreement, for an input range containing two
values more than `ε` apart, e.g. `0` and `2ε` as in the paper), then for every partition
`L, C, R` of `V` with `L, R` non-empty, `L ∪ C → R` or `C ∪ R → L`. -/
theorem theorem6 [Fintype V] {f : ℕ} {ε : ℝ} {I : Set ℝ} {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I)
    (hab : ε < b - a) (hA : CrashSolvesOn I A G f ε) : CCA G f :=
  theorem17b.mpr (twoReach_of_crashSolvesOn ha hb hab hA)

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
  obtain ⟨w, h1, h2⟩ := theorem17b.mp hG Fj Fi j i hFj hFi hj hi
  exact ⟨w, h1, h2⟩

end CrashConsensusDigraph
