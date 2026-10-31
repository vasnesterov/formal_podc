import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/AnonymousNetworks/Basic.lean

/-!
# Anonymous synchronous networks: function computation

The model of Charron-Bost and Lambein-Monette (*Know your audience*, PODC 2024) for distributed
function computation in static anonymous networks, in the synchronous round model.

* `Network V`: a static network on a finite vertex type `V`: a simple directed graph given by the
  out-neighbourhoods `out j`, with a self-loop at every vertex, and a *local output port numbering*
  `port j : V → ℕ` (injective on `out j`, values `< outdeg j`).
* `Algorithm I X`: an anonymous deterministic algorithm with inputs in `I` and outputs in `X`:
  states `Q`, messages `M`, initialisation `init : I → Q`, sending function
  `send : Q → ℕ → ℕ → M` (state, outdegree, output port), transition function
  `trans : Q → Multiset M → Q` (the multiset of the messages received in the round, including the
  agent's own message on its self-loop) and output map `out : Q → X`.
* `CommModel`: the four communication models of the paper. An algorithm is *allowed* in a model
  (`CommModel.Allowed`) when its sending function only depends on what the model lets the sender
  see:
  the state (simple broadcast, symmetric communications), the state and the outdegree (outdegree
  awareness), or also the output port (output port awareness). The model of symmetric
  communications additionally restricts the networks to bidirectional ones (`CommModel.NetOK`).
* `Network.run A x t i`: the state of agent `i` at the end of round `t` (synchronous starts).
* `Computes m C valid f A`: in every network of class `C` (and allowed by `m`) and for all valid
  inputs, the outputs of all agents converge to `f` of the input vector (paper: "`δ`-computes").
* Function classes on input vectors (lists): `SetBased`, `FrequencyBased`, `MultisetBased`, and
  `FrequencyBasedFrom k` (frequency-based on vectors of length `≥ k`).
-/

namespace Cslib.AnonNet

open Finset Filter Topology

universe u v

/-- A static anonymous network on the finite vertex type `V`: a simple directed graph (edge
`j → i` iff `i ∈ out j`) with a self-loop at every vertex, and a local output port numbering. -/
structure Network (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Out-neighbourhoods: agent `i` hears from agent `j` iff `i ∈ out j`. -/
  out : V → Finset V
  /-- Every agent hears from itself. -/
  self_mem : ∀ i, i ∈ out i
  /-- The output port of `j` leading to `i` (ports are numbered `0, …, outdeg j - 1`). -/
  port : V → V → ℕ
  port_lt : ∀ j i, i ∈ out j → port j i < (out j).card
  port_injOn : ∀ j, Set.InjOn (port j) (out j)

namespace Network

variable {V : Type*} [Fintype V] [DecidableEq V] (N : Network V)

/-- The edge relation: `N.Adj j i` iff there is an edge `j → i`. -/
def Adj (j i : V) : Prop := i ∈ N.out j

/-- In-neighbours of `i` (including `i` itself). -/
def inN (i : V) : Finset V := univ.filter fun j => i ∈ N.out j

/-- Outdegree (including the self-loop). -/
def outdeg (j : V) : ℕ := (N.out j).card

@[simp] lemma mem_inN {i j : V} : j ∈ N.inN i ↔ i ∈ N.out j := by simp [inN]

lemma self_mem_inN (i : V) : i ∈ N.inN i := by simp [N.self_mem]

/-- Bidirectional networks (symmetric communications). -/
def Symmetric : Prop := ∀ i j, i ∈ N.out j → j ∈ N.out i

/-- Strong connectivity. -/
def StronglyConnected : Prop := ∀ i j, Relation.ReflTransGen N.Adj i j

lemma Symmetric.inN_eq {N : Network V} (h : N.Symmetric) (i : V) : N.inN i = N.out i := by
  ext j; simp only [mem_inN]; exact ⟨h _ _, h _ _⟩

/-- In a strongly connected network with another vertex, every vertex hears from another one. -/
lemma exists_mem_inN_ne {N : Network V} (hsc : N.StronglyConnected) {i k : V} (hk : k ≠ i) :
    ∃ j ∈ N.inN i, j ≠ i := by
  have key : ∀ c, Relation.ReflTransGen N.Adj k c → k ≠ c → ∃ j ∈ N.inN c, j ≠ c := by
    intro c h
    induction h with
    | refl => intro h; exact absurd rfl h
    | @tail b c _ hbc ih =>
      intro hkc
      by_cases hb : b = c
      · subst hb; exact ih hkc
      · exact ⟨b, (N.mem_inN).2 hbc, hb⟩
  exact key i (hsc k i) hk

/-- In a strongly connected network, an agent hears from itself only iff it is alone. -/
lemma card_inN_eq_one_iff {N : Network V} (hsc : N.StronglyConnected) (i : V) :
    (N.inN i).card = 1 ↔ Fintype.card V = 1 := by
  constructor
  · intro h
    rw [Fintype.card_eq_one_iff]
    refine ⟨i, fun k => ?_⟩
    by_contra hk
    obtain ⟨j, hj, hji⟩ := exists_mem_inN_ne hsc hk
    rw [Finset.card_eq_one] at h
    obtain ⟨a, ha⟩ := h
    have h1 := N.self_mem_inN i
    rw [ha, Finset.mem_singleton] at h1 hj
    exact hji (hj.trans h1.symm)
  · intro h
    rw [Finset.card_eq_one]
    refine ⟨i, Finset.eq_singleton_iff_unique_mem.2 ⟨N.self_mem_inN i, fun j _ => ?_⟩⟩
    exact Fintype.card_le_one_iff.1 h.le j i

end Network

/-- An anonymous deterministic algorithm with inputs in `I` and outputs in `X`. -/
structure Algorithm (I : Type u) (X : Type v) where
  /-- Local states. -/
  Q : Type u
  /-- Messages. -/
  M : Type u
  /-- Initial state as a function of the input. -/
  init : I → Q
  /-- Sending function: state, outdegree, output port ↦ message. -/
  send : Q → ℕ → ℕ → M
  /-- Transition function: state, multiset of received messages ↦ new state. -/
  trans : Q → Multiset M → Q
  /-- Output variable. -/
  out : Q → X

namespace Network

variable {V : Type*} [Fintype V] [DecidableEq V] (N : Network V)
variable {I : Type u} {X : Type v}

/-- The multiset of messages received by `i` in a round starting in configuration `C`. -/
def recv (A : Algorithm I X) (C : V → A.Q) (i : V) : Multiset A.M :=
  (N.inN i).val.map fun j => A.send (C j) (N.outdeg j) (N.port j i)

/-- One synchronous round. -/
def step (A : Algorithm I X) (C : V → A.Q) : V → A.Q :=
  fun i => A.trans (C i) (N.recv A C i)

/-- The execution from an arbitrary initial configuration `C₀`. -/
def runFrom (A : Algorithm I X) (C₀ : V → A.Q) : ℕ → V → A.Q
  | 0 => C₀
  | t + 1 => N.step A (runFrom A C₀ t)

/-- The execution with input vector `x` (synchronous starts). -/
def run (A : Algorithm I X) (x : V → I) : ℕ → V → A.Q :=
  N.runFrom A (A.init ∘ x)

@[simp] lemma runFrom_zero (A : Algorithm I X) (C₀ : V → A.Q) : N.runFrom A C₀ 0 = C₀ := rfl

lemma runFrom_succ (A : Algorithm I X) (C₀ : V → A.Q) (t : ℕ) :
    N.runFrom A C₀ (t + 1) = N.step A (N.runFrom A C₀ t) := rfl

end Network

/-- The communication models of the paper. Symmetric communications = simple broadcast restricted
to bidirectional networks. -/
inductive CommModel
  | broadcast
  | outdegree
  | outPort
  | symmetric
  deriving DecidableEq

namespace CommModel

variable {I : Type u} {X : Type v}

/-- The sending functions allowed by the model. -/
def Allowed : CommModel → Algorithm I X → Prop
  | broadcast, A => ∀ q d ℓ d' ℓ', A.send q d ℓ = A.send q d' ℓ'
  | symmetric, A => ∀ q d ℓ d' ℓ', A.send q d ℓ = A.send q d' ℓ'
  | outdegree, A => ∀ q d ℓ ℓ', A.send q d ℓ = A.send q d ℓ'
  | outPort, _ => True

/-- The networks allowed by the model (bidirectional ones for symmetric communications). -/
def NetOK {V : Type*} [Fintype V] [DecidableEq V] : CommModel → Network V → Prop
  | symmetric, N => N.Symmetric
  | _, _ => True

end CommModel

/-- A network class: a predicate on networks with vertex set `Fin n`, for every `n`. -/
abbrev NetClass := ∀ n : ℕ, Network (Fin n) → Prop

/-- The class of static strongly connected networks. -/
def staticSC : NetClass := fun _ N => N.StronglyConnected

/-- Static strongly connected networks with at most `B` agents (`C^s_{≤B}`). -/
def sizeLE (B : ℕ) : NetClass := fun n N => N.StronglyConnected ∧ n ≤ B

/-- Static strongly connected networks with exactly `k` agents (`C^s_k`). -/
def sizeEq (k : ℕ) : NetClass := fun n N => N.StronglyConnected ∧ n = k

variable {I : Type u} {X : Type v}

/-- `A` computes `f` on the network `N`, for inputs satisfying `valid`: for every valid input
vector `x`, the output of every agent converges to `f x`. -/
def ComputesOn [TopologicalSpace X] (A : Algorithm I X) {n : ℕ} (N : Network (Fin n))
    (valid : List I → Prop) (f : List I → X) : Prop :=
  ∀ x : Fin n → I, valid (List.ofFn x) →
    ∀ i, Tendsto (fun t => A.out (N.run A x t i)) atTop (𝓝 (f (List.ofFn x)))

/-- `A` computes `f` in the network class `C` under the communication model `m`. -/
def Computes [TopologicalSpace X] (m : CommModel) (C : NetClass) (valid : List I → Prop)
    (f : List I → X) (A : Algorithm I X) : Prop :=
  ∀ n, 0 < n → ∀ N : Network (Fin n), C n N → m.NetOK N → ComputesOn A N valid f

/-- `f` is computable in the class `C` under the communication model `m` (paper: "`δ`-computable",
`δ` being the metric of `X`). -/
def Computable [TopologicalSpace X] (m : CommModel) (C : NetClass) (valid : List I → Prop)
    (f : List I → X) : Prop :=
  ∃ A : Algorithm I X, m.Allowed A ∧ Computes m C valid f A

/-- Computability is inherited by subclasses. -/
lemma Computable.mono [TopologicalSpace X] {m : CommModel} {C C' : NetClass}
    {valid : List I → Prop} {f : List I → X} (h : Computable m C valid f)
    (hC : ∀ n N, C' n N → C n N) : Computable m C' valid f := by
  obtain ⟨A, hA, hc⟩ := h
  exact ⟨A, hA, fun n hn N hN hok => hc n hn N (hC n N hN) hok⟩

/-! ### Function classes -/

/-- The frequency function of a (nonempty) vector: `ν_l(a) = |l⁻¹(a)| / |l|`. -/
def freq [DecidableEq I] (l : List I) (a : I) : ℚ := (l.count a : ℚ) / l.length

/-- Set-based functions: the value only depends on the set of entries. -/
def SetBased [DecidableEq I] (f : List I → X) : Prop :=
  ∀ l l' : List I, l ≠ [] → l' ≠ [] → l.toFinset = l'.toFinset → f l = f l'

/-- Frequency-based functions: the value only depends on the frequency function. -/
def FrequencyBased [DecidableEq I] (f : List I → X) : Prop :=
  ∀ l l' : List I, l ≠ [] → l' ≠ [] → freq l = freq l' → f l = f l'

/-- Frequency-based on the vectors of length at least `k`. -/
def FrequencyBasedFrom [DecidableEq I] (k : ℕ) (f : List I → X) : Prop :=
  ∀ l l' : List I, l ≠ [] → l' ≠ [] → k ≤ l.length → k ≤ l'.length → freq l = freq l' → f l = f l'

/-- Multiset-based (symmetric) functions: invariant under permutation of the arguments. -/
def MultisetBased (f : List I → X) : Prop :=
  ∀ l l' : List I, l.Perm l' → f l = f l'

lemma frequencyBasedFrom_one [DecidableEq I] (f : List I → X) :
    FrequencyBasedFrom 1 f ↔ FrequencyBased f := by
  constructor
  · intro h l l' hl hl' e
    exact h l l' hl hl' (List.length_pos_iff.2 hl) (List.length_pos_iff.2 hl') e
  · intro h l l' hl hl' _ _ e; exact h l l' hl hl' e

lemma FrequencyBased.frequencyBasedFrom [DecidableEq I] {f : List I → X}
    (h : FrequencyBased f) (k : ℕ) : FrequencyBasedFrom k f :=
  fun l l' hl hl' _ _ e => h l l' hl hl' e

/-- Equality of frequency functions, cross-multiplied. -/
lemma freq_eq_freq_iff [DecidableEq I] {l l' : List I} (hl : l ≠ []) (hl' : l' ≠ []) :
    freq l = freq l' ↔ ∀ a, l.count a * l'.length = l'.count a * l.length := by
  have h1 : (l.length : ℚ) ≠ 0 := by simp [hl]
  have h2 : (l'.length : ℚ) ≠ 0 := by simp [hl']
  constructor
  · intro h a
    have := congrFun h a
    simp only [freq] at this
    rw [div_eq_div_iff h1 h2] at this
    exact_mod_cast this
  · intro h; funext a
    simp only [freq]
    rw [div_eq_div_iff h1 h2]
    exact_mod_cast h a

/-! ### Lists of inputs -/

lemma count_ofFn [DecidableEq I] {n : ℕ} (x : Fin n → I) (a : I) :
    (List.ofFn x).count a = (univ.filter (fun i => x i = a)).card := by
  rw [← Multiset.coe_count, ← Fin.univ_val_map, Multiset.count_map]
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro i _; exact eq_comm

/-- A permutation of `List.ofFn x` is `List.ofFn (x ∘ σ)` for a bijection `σ`. -/
lemma exists_equiv_ofFn_comp_eq [DecidableEq I] {n : ℕ} (x : Fin n → I) {l' : List I}
    (h : (List.ofFn x).Perm l') : ∃ σ : Fin n ≃ Fin n, List.ofFn (x ∘ σ) = l' := by
  have hl : l'.length = n := by rw [← h.length_eq]; simp
  subst hl
  have hc : ∀ a, (univ.filter (fun i => l'.get i = a)).card =
      (univ.filter (fun i => x i = a)).card := by
    intro a
    rw [← count_ofFn, ← count_ofFn, List.ofFn_get, h.count_eq]
  let e : ∀ a, {i // l'.get i = a} ≃ {i // x i = a} := fun a =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype, hc])
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  conv_rhs => rw [← List.ofFn_get l']
  congr 1
  funext i
  exact Equiv.ofFiberEquiv_map e i

end Cslib.AnonNet
