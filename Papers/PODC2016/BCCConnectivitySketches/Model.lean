import Podc.Computability.Distributed.CongestedClique.Broadcast
import Papers.PODC2014.CongestedCliquePower.Claim6
import Mathlib

-- CSLib candidate: `TAlg`, `TAlg.toBits` (typed messages for Cslib/Computability/Distributed/CongestedClique/Broadcast.lean)

/-!
# The broadcast congested clique with typed messages; spanning forests

Montealegre–Todinca, *Deterministic graph connectivity in the broadcast congested clique*
(PODC 2016 BA; arXiv:1602.04095v3).

The model `BClique[b]` is `Cslib.CongestedClique.Bcast.Algorithm V I σ b` (staged in `Podc/`):
synchronous rounds, every node broadcasts one `b`-bit message per round, deterministic, no
failures, free local computation. To write protocols conveniently we use algorithms whose messages
live in a finite type `M` (`TAlg`) and convert them to `b`-bit algorithms whenever `|M| ≤ 2^b`
(`TAlg.toBits`, `TAlg.run_toBits`): this is the usual "a message from a set of size `|M|` takes
`⌈log₂ |M|⌉` bits".

* `TAlg`, `TAlg.run`, `TAlg.toBits`, `TAlg.run_toBits`.
* `TAlg.oneRound msg dec`: the one-round protocol in which node `v` broadcasts `msg v (input)` and
  every node outputs `dec (all messages)`.
* `nbrs G v`: the input of node `v` (its adjacency row).
* `IsSpanningForest G F`: `F ≤ G`, `F` acyclic, same connected components as `G`
  (the paper's "spanning forest" is a maximal one, footnote 1); `exists_isSpanningForest`.
-/

namespace Podc.BCCConnectivitySketches

open Cslib.CongestedClique SimpleGraph Finset

/-- A deterministic broadcast-clique algorithm whose messages live in a type `M`: node `v` in state
`s` broadcasts `send v s`, then moves to `step v s m` where `m w` is the message of `w`. -/
structure TAlg (V I σ M : Type*) where
  /-- Initial state from the identity and the input. -/
  init : V → I → σ
  /-- Message broadcast in state `s`. -/
  send : V → σ → M
  /-- State update from all broadcast messages. -/
  step : V → σ → (V → M) → σ

namespace TAlg

variable {V I σ M : Type*}

/-- States after `t` rounds on node inputs `inp`. -/
def run (A : TAlg V I σ M) (inp : V → I) : ℕ → V → σ
  | 0 => fun v => A.init v (inp v)
  | t + 1 => fun v => A.step v (A.run inp t v) (fun w => A.send w (A.run inp t w))

/-- A fixed injection of `M` into `b`-bit strings, when `|M| ≤ 2^b`. -/
noncomputable def encode [Fintype M] (b : ℕ) (hb : Fintype.card M ≤ 2 ^ b) : M ↪ Bcast.Msg b :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hb))

/-- The `b`-bit algorithm simulating `A` (messages encoded by `encode`, decoded by its left
inverse). Its acceptance output is irrelevant here (constantly `true`); the protocols' outputs are
functions of the final states. -/
noncomputable def toBits [Fintype M] [Nonempty M] (A : TAlg V I σ M) (b : ℕ)
    (hb : Fintype.card M ≤ 2 ^ b) : Bcast.Algorithm V I σ b where
  init := A.init
  send v s := encode b hb (A.send v s)
  step v s m := A.step v s (fun w => Function.invFun (encode b hb) (m w))
  out _ _ := true

/-- The `b`-bit simulation has exactly the same executions. -/
theorem run_toBits [Fintype M] [Nonempty M] (A : TAlg V I σ M) (b : ℕ)
    (hb : Fintype.card M ≤ 2 ^ b) (inp : V → I) : ∀ t, (A.toBits b hb).run inp t = A.run inp t
  | 0 => rfl
  | t + 1 => by
      have ih := run_toBits A b hb inp t
      funext v
      change A.step v ((A.toBits b hb).run inp t v)
          (fun w => Function.invFun (encode b hb) (encode b hb (A.send w ((A.toBits b hb).run inp t w))))
        = _
      rw [ih]
      simp only [Function.leftInverse_invFun (encode b hb).injective _]
      rfl

/-- The one-round protocol: node `v` with input `x` broadcasts `msg v x`; every node then outputs
`dec` of all messages (stored in the second component of its state). -/
def oneRound {R : Type*} (msg : V → I → M) (dec : (V → M) → R) : TAlg V I (I × Option R) M where
  init _ x := (x, none)
  send v s := msg v s.1
  step _ s m := (s.1, some (dec m))

theorem oneRound_run {R : Type*} (msg : V → I → M) (dec : (V → M) → R) (inp : V → I) (v : V) :
    (oneRound msg dec).run inp 1 v = (inp v, some (dec fun w => msg w (inp w))) := rfl

end TAlg

/-- The input of node `v` in `BClique`: its row of the adjacency matrix, i.e. its neighbourhood. -/
noncomputable def nbrs {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) : Finset V := by
  classical exact univ.filter (G.Adj v)

@[simp] lemma mem_nbrs {V : Type*} [Fintype V] (G : SimpleGraph V) (v w : V) :
    w ∈ nbrs G v ↔ G.Adj v w := by
  classical simp [nbrs]

/-- `⌈log₂ |M|⌉` bits suffice for messages in `M`. -/
lemma card_le_two_pow_clog (m : ℕ) : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by norm_num) m

/-- `F` is a (maximal) spanning forest of `G`: an acyclic subgraph with the same connected
components (footnote 1 of the paper: "a spanning forest designs a maximal one"). -/
def IsSpanningForest {V : Type*} (G F : SimpleGraph V) : Prop :=
  F ≤ G ∧ F.IsAcyclic ∧ ∀ u v, F.Reachable u v ↔ G.Reachable u v

/-- Every graph has a spanning forest. -/
lemma exists_isSpanningForest {V : Type*} (G : SimpleGraph V) : ∃ F, IsSpanningForest G F := by
  obtain ⟨F, hle, hac, hr⟩ := G.exists_isAcyclic_reachable_eq_le
  exact ⟨F, hle, hac, fun u v => by rw [hr]⟩

/-- A spanning forest of a subgraph `H ≤ G` with the same components is one of `G`. -/
lemma IsSpanningForest.of_le {V : Type*} {G H F : SimpleGraph V} (hF : IsSpanningForest H F)
    (hH : H ≤ G) (hr : ∀ u v, H.Reachable u v ↔ G.Reachable u v) : IsSpanningForest G F :=
  ⟨hF.1.trans hH, hF.2.1, fun u v => (hF.2.2 u v).trans (hr u v)⟩

end Podc.BCCConnectivitySketches
