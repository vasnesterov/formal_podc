import Cslib.Computability.Distributed.Congest.LowerBound

-- CSLib candidate: Cslib/Computability/Distributed/Congest/Typed.lean

/-!
# CONGEST algorithms with typed messages

Upper bounds are much easier to write with messages in a structured finite type `M` (node IDs,
small counters, flags) than with raw bit strings. `TAlgorithm V I σ M` is a synchronous
message-passing algorithm with messages in `M`; `TAlgorithm.toAlgorithm` turns it into a CSLib
CONGEST algorithm `Algorithm V I σ (msgBits M)` with `msgBits M = ⌈log₂ |M|⌉` bits per message,
by an injective binary encoding of `M`, and `run_toAlgorithm` says both have the same executions.

So a bound `msgBits M ≤ c · log n` shows that the typed algorithm is a CONGEST algorithm with
`O(log n)`-bit messages.
-/

namespace Cslib.Congest

/-- A synchronous message-passing algorithm on vertex set `V` (the IDs), node inputs `I`, states
`σ` and messages in `M`. Same conventions as `Algorithm`: in every round each node `v` sends
`send v s w` to every neighbour `w`, then updates its state, receiving `some m` from each
neighbour and `none` from non-neighbours. -/
structure TAlgorithm (V I σ M : Type*) where
  /-- Initial state from the node's ID and input. -/
  init : V → I → σ
  /-- Message sent by `v` in state `s` to neighbour `w`. -/
  send : V → σ → V → M
  /-- State update from the received messages. -/
  step : V → σ → (V → Option M) → σ

namespace TAlgorithm

variable {V I σ M : Type*}

/-- The state of every node after `t` synchronous rounds on graph `G` with node inputs `inp`. -/
def run (A : TAlgorithm V I σ M) (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → I) :
    ℕ → V → σ
  | 0 => fun v => A.init v (inp v)
  | t + 1 => fun v => A.step v (A.run G inp t v)
      (fun w => if G.Adj w v then some (A.send w (A.run G inp t w) v) else none)

lemma run_succ (A : TAlgorithm V I σ M) (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → I)
    (t : ℕ) (v : V) :
    A.run G inp (t + 1) v = A.step v (A.run G inp t v)
      (fun w => if G.Adj w v then some (A.send w (A.run G inp t w) v) else none) := rfl

/-- Number of bits needed for a message of type `M`. -/
def msgBits (M : Type*) [Fintype M] : ℕ := Nat.clog 2 (Fintype.card M)

variable [Fintype M]

/-- An injective binary encoding of `M`. -/
noncomputable def encode : M → Msg (msgBits M) := fun m =>
  (Fintype.equivFin (Msg (msgBits M))).symm
    (Fin.castLE (by
      have : Fintype.card (Msg (msgBits M)) = 2 ^ msgBits M := by simp [Msg]
      rw [this]
      exact Nat.le_pow_clog (by norm_num) _) (Fintype.equivFin M m))

lemma encode_injective : Function.Injective (encode (M := M)) := by
  intro a b h
  simp only [encode, EmbeddingLike.apply_eq_iff_eq, Fin.castLE_inj] at h
  exact h

variable [Nonempty M]

/-- Decoding (a left inverse of `encode`). -/
noncomputable def decode : Msg (msgBits M) → M := Function.invFun encode

@[simp] lemma decode_encode (m : M) : decode (encode m) = m :=
  Function.leftInverse_invFun encode_injective m

/-- The CONGEST algorithm with `msgBits M`-bit messages that encodes the typed messages. -/
noncomputable def toAlgorithm (A : TAlgorithm V I σ M) (out : V → σ → Bool) :
    Algorithm V I σ (msgBits M) where
  init := A.init
  send v s w := encode (A.send v s w)
  step v s m := A.step v s (fun w => (m w).map decode)
  out := out

/-- The encoded algorithm has the same executions. -/
@[simp] theorem run_toAlgorithm (A : TAlgorithm V I σ M) (out : V → σ → Bool)
    (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → I) :
    ∀ t, (A.toAlgorithm out).run G inp t = A.run G inp t
  | 0 => rfl
  | t + 1 => by
      funext v
      have ih := run_toAlgorithm A out G inp t
      simp only [Algorithm.run]
      rw [ih]
      simp only [toAlgorithm, run]
      congr 1
      funext w
      split_ifs <;> simp

end TAlgorithm

end Cslib.Congest
