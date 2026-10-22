import Papers.PODC2019.CRDTReplication.Protocol
import Cslib.Computability.Distributed.MessagePassing.FairExec

/-!
# The claims of Section III-D/E, stated for Algorithm 2

Each claim of the paper is stated as a `Prop` about the protocol `alg V QS` (variant `V`, quorum
system `QS`), quantifying over all reachable configurations `C` with history `h`. The proofs
(or refutations) are in the other files.

* "`s` is learned" is `Learned C s` (some query returned after learning `s`); `learnedOf C x`
  is the state learned by the query operation `x`; `LearnedBy C s v` records how `s` was learned
  (`v = true`: by vote, `false`: by consistent quorum).
* "`u₁` precedes `u₂`" is CSLib's real-time order `Precedes h x y` on operation instances.
* "the state `s` includes `u`" is `u ∈ H.C s` for a causal history `H` of the CRDT.
-/

namespace Podc.CRDTReplication

open Cslib.SharedMemory Cslib.AsyncMP

variable {P : Type} [Fintype P] [DecidableEq P] {D : CRDT}

/-- Update identifiers are unique in the history `h` (assumed in the paper). -/
def UniqueUpd (h : List (Label P D.spec)) : Prop :=
  ∀ x y u, opOf h x = some (CRDT.Cmd.upd u) → opOf h y = some (CRDT.Cmd.upd u) → x = y

/-- Comparability. -/
def Comparable {S : Type} [LE S] (s t : S) : Prop := s ≤ t ∨ t ≤ s

variable (V : Variant D) (QS : Finset (Finset P))

/-- **Lemma 1.** The payload state of every acceptor increases monotonically. -/
def Lemma1 : Prop :=
  ∀ C h C' (st : Step P D.spec (Msg P D) Act) ℓ, (alg V QS).Reach C h →
    (alg V QS).step C st = some (C', ℓ) → ∀ a, (C.loc a).s ≤ (C'.loc a).s

/-- **Corollary 1.** If `ACK(r, s)` and `ACK(r', s')` are sent by the same acceptor in this order,
then `s ⊑ s'`: an `ACK` already sent in `C` carries a state below every `ACK` sent by the same
acceptor afterwards. -/
def Corollary1 : Prop :=
  ∀ C h ss C' h', (alg V QS).Reach C h → (alg V QS).runFrom C ss = some (C', h') →
    ∀ a p p' n n' i i' s s', (a, p, Msg.ack n i s) ∈ C.sent →
      (a, p', Msg.ack n' i' s') ∈ C'.sent → (a, p', Msg.ack n' i' s') ∉ C.sent → s ≤ s'

/-- **Lemma 2.** A learned state is below the payload of every acceptor of some quorum. -/
def Lemma2 : Prop :=
  ∀ C h, (alg V QS).Reach C h → ∀ s, Learned C s → ∃ Q ∈ QS, ∀ a ∈ Q, s ≤ (C.loc a).s

/-- **Theorem 1 (Validity).** The causal history of any learned state is a subset of the updates
invoked before the query returned. -/
def Theorem1 (H : D.CausalHistory) : Prop :=
  ∀ C h, (alg V QS).Reach C h → ∀ x s, learnedOf C x = some s →
    ∀ u ∈ H.C s, ∃ y, opOf h y = some (CRDT.Cmd.upd u) ∧ ¬ Precedes h x y

/-- **Theorem 2 (Stability).** If query `x` precedes query `y`, the state learned by `x` is below
the state learned by `y`. -/
def Theorem2 : Prop :=
  ∀ C h, (alg V QS).Reach C h → ∀ x y s₁ s₂, Precedes h x y → learnedOf C x = some s₁ →
    learnedOf C y = some s₂ → s₁ ≤ s₂

/-- **Lemma 3.** Two learned states are comparable if one is learned by consistent quorum. -/
def Lemma3 : Prop :=
  ∀ C h, (alg V QS).Reach C h → ∀ s₁ s₂, LearnedBy C s₁ false → Learned C s₂ → Comparable s₁ s₂

/-- **Lemma 4.** Two learned states are comparable if both are learned by vote. -/
def Lemma4 : Prop :=
  ∀ C h, (alg V QS).Reach C h → ∀ s₁ s₂, LearnedBy C s₁ true → LearnedBy C s₂ true →
    Comparable s₁ s₂

/-- **Theorem 3 (Consistency).** Any two learned states are comparable. -/
def Theorem3 : Prop :=
  ∀ C h, (alg V QS).Reach C h → ∀ s₁ s₂, Learned C s₁ → Learned C s₂ → Comparable s₁ s₂

/-- **Theorem 4 (Update Stability).** If update `u₁` precedes update `u₂`, every learned state
that includes `u₂` also includes `u₁`. -/
def Theorem4 (H : D.CausalHistory) : Prop :=
  ∀ C h, (alg V QS).Reach C h → UniqueUpd h → ∀ x y u₁ u₂ s, Precedes h x y →
    opOf h x = some (CRDT.Cmd.upd u₁) → opOf h y = some (CRDT.Cmd.upd u₂) → Learned C s →
    u₂ ∈ H.C s → u₁ ∈ H.C s

/-- **Theorem 5 (Update Visibility).** If update `u` precedes query `y`, the state learned by `y`
includes `u`. -/
def Theorem5 (H : D.CausalHistory) : Prop :=
  ∀ C h, (alg V QS).Reach C h → ∀ x y u s, Precedes h x y → opOf h x = some (CRDT.Cmd.upd u) →
    learnedOf C y = some s → u ∈ H.C s

/-- **Main claim (Section III-E).** The protocol is linearizable (histories with unique update
identifiers). -/
def LinearizableClaim : Prop :=
  ∀ C h, (alg V QS).Reach C h → UniqueUpd h → ∃ L, IsLinearization h L

end Podc.CRDTReplication
