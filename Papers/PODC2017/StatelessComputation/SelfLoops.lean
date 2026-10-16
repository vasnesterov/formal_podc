import Papers.PODC2017.StatelessComputation.Impossibility

/-!
# Theorem 3.1 needs a loop-free graph

The paper's graphs are "directed graphs `G = ([n], E)`" without saying whether self-loops
`(i, i) ∈ E` are allowed. With a self-loop a node can store a value on its own loop, i.e. it is
no longer stateless, and Theorem 3.1 fails: on the complete digraph *with* loops, the protocol
in which every node copies the label of its own loop to all its outgoing arcs has many stable
labelings, yet it is label `r`-stabilizing for every `r` (it converges as soon as every node has
been activated once).
-/

namespace StatelessComputation
namespace SelfLoops

variable {V : Type*} [DecidableEq V]

/-- The complete digraph with a self-loop at every node. -/
def loopG (V : Type*) : Digraph V := ⟨fun _ _ => True⟩

/-- Every node copies the label of its own loop to all its outgoing arcs and outputs it. -/
def copyP (V : Type*) : Protocol (loopG V) Bool Unit Bool :=
  ⟨fun i inl _ => (fun _ => inl ⟨i, trivial⟩, inl ⟨i, trivial⟩)⟩

/-- The loop labels never change. -/
lemma run_loop (x : V → Unit) (ℓ0 : Labeling (loopG V) Bool) (σ : ℕ → Finset V) (i : V) (t : ℕ) :
    (copyP V).run x ℓ0 σ t ⟨(i, i), trivial⟩ = ℓ0 ⟨(i, i), trivial⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Protocol.run_succ]
    by_cases h : i ∈ σ t
    · rw [Protocol.step_of_mem _ _ (e := ⟨(i, i), trivial⟩) h]; exact ih
    · rw [Protocol.step_of_not_mem _ _ (e := ⟨(i, i), trivial⟩) h]; exact ih

/-- After its first activation, a node's outgoing labels equal its initial loop label. -/
lemma run_after (x : V → Unit) (ℓ0 : Labeling (loopG V) Bool) (σ : ℕ → Finset V) (e : Arc (loopG V)) {s : ℕ}
    (hs : e.1.1 ∈ σ s) (t : ℕ) (ht : s < t) :
    (copyP V).run x ℓ0 σ t e = ℓ0 ⟨(e.1.1, e.1.1), trivial⟩ := by
  induction t with
  | zero => omega
  | succ t ih =>
    rw [Protocol.run_succ]
    by_cases h : e.1.1 ∈ σ t
    · rw [Protocol.step_of_mem _ _ h]; exact run_loop x ℓ0 σ e.1.1 t
    · rw [Protocol.step_of_not_mem _ _ h]
      exact ih (by rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h' | h'
                   · exact h'
                   · exact absurd (h' ▸ hs) h)

lemma outputs_after (x : V → Unit) (ℓ0 : Labeling (loopG V) Bool) (y0 : V → Bool) (σ : ℕ → Finset V) (i : V)
    {s : ℕ} (hs : i ∈ σ s) (t : ℕ) (ht : s < t) :
    (copyP V).outputs x ℓ0 y0 σ t i = ℓ0 ⟨(i, i), trivial⟩ := by
  induction t with
  | zero => omega
  | succ t ih =>
    simp only [Protocol.outputs]
    split_ifs with h
    · exact run_loop x ℓ0 σ i t
    · exact ih (by rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h' | h'
                   · exact h'
                   · exact absurd (h' ▸ hs) h)

/-- The copy protocol on the looped complete digraph is label `r`-stabilizing for every `r`. -/
theorem copyP_labelStabilizing (r : ℕ) : LabelStabilizing r (copyP V) := by
  refine ⟨fun x ℓ0 y0 σ hσ i => ?_, fun x ℓ0 σ hσ => ?_⟩
  · obtain ⟨s, -, hs, hi⟩ := hσ.2 0 i
    exact ⟨ℓ0 ⟨(i, i), trivial⟩, s + 1, fun t ht => outputs_after x ℓ0 y0 σ i hi t (by omega)⟩
  · refine ⟨fun e => ℓ0 ⟨(e.1.1, e.1.1), trivial⟩, r, fun t ht => funext fun e => ?_⟩
    obtain ⟨s, -, hs, hi⟩ := hσ.2 0 e.1.1
    exact run_after x ℓ0 σ e hi t (by omega)

omit [DecidableEq V] in
lemma copyP_stable (b : Bool) : (copyP V).IsStable (fun _ => ()) (fun _ => b) := fun _ _ => rfl

/-- **Theorem 3.1 fails for graphs with self-loops**: on two nodes with loops there is a
protocol with two distinct stable labelings that is label `(n-1)`-stabilizing (indeed label
`r`-stabilizing for every `r`). -/
theorem thm_3_1_false_with_loops :
    ∃ (G : Digraph (Fin 2)) (P : Protocol G Bool Unit Bool) (ℓ₁ ℓ₂ : Labeling G Bool),
      P.IsStable (fun _ => ()) ℓ₁ ∧ P.IsStable (fun _ => ()) ℓ₂ ∧ ℓ₁ ≠ ℓ₂ ∧ ∀ r, LabelStabilizing r P :=
  ⟨loopG (Fin 2), copyP (Fin 2), fun _ => true, fun _ => false, copyP_stable true,
    copyP_stable false, fun h => by
      have := congrFun h ⟨((0 : Fin 2), (0 : Fin 2)), trivial⟩
      simp at this,
    copyP_labelStabilizing⟩

end SelfLoops
end StatelessComputation
