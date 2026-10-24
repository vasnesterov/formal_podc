import Papers.PODC2021.TrustedHardwareUnidirectional.SRB

/-!
# Sequenced reliable broadcast implements unidirectional rounds whenever `n > 2f`

This file refutes the Claim of Section 4.1 of Ben-David–Nayak ("Sequenced reliable broadcast
cannot implement unidirectionality in a system with `n > 2f` and `f > 1`").

**The echo protocol** (`echoProtocol f`). In round `r`, process `p`
1. SRB-broadcasts its signed round-`r` message `val r w`;
2. whenever it delivers `val r w` from some `s`, it SRB-broadcasts `echo r s w` (a relay of `s`'s
   signed message);
3. ends round `r` as soon as it has delivered, from `n - f` distinct senders, an echo of its own
   round-`r` message. Its round-`r` result is everything it has delivered so far: `p` has
   received `q`'s round-`r` message if it delivered `val r w` from `q` or any `echo r q w`.

**Why it works.** If `p` and `q` both end round `r`, the sets of senders whose echoes they counted
have `n - f` elements each, so (as `n > 2f`) they share a sender `s`, possibly Byzantine. SRB
delivers `s`'s messages to `p` and to `q` as prefixes of *one* sequence; whichever of
`echo r p _`, `echo r q _` comes first in that sequence was delivered by both. So `q` delivered
`echo r p _` before ending its round, or `p` delivered `echo r q _` before ending its own.
Signatures guarantee that relayed messages are genuine. Liveness: the `≥ n - f` correct processes
echo every message of `p`.

The flaw in the paper's proof: in its Scenario 1 the processes of `C₂` need not end the round
while their messages to `Q` are delayed — here they wait for echoes from `Q`.
-/

namespace Podc.TrustedHW

namespace Echo

variable {P V : Type}

/-- Messages of the echo protocol. -/
inductive Msg (P V : Type) where
  /-- The sender's own (signed) round-`r` message. -/
  | val (r : ℕ) (w : V)
  /-- A relay of `q`'s signed round-`r` message `w`. -/
  | echo (r : ℕ) (q : P) (w : V)
  deriving DecidableEq

/-- Local state: delivered messages per sender, and snapshots of the deliveries at the end of
each completed round. -/
structure State (P V : Type) where
  /-- Messages delivered so far, per sender. -/
  hist : P → List (Msg P V)
  /-- `done[r]` = `hist` at the moment round `r` ended. -/
  done : List (P → List (Msg P V))

open Classical

/-- The senders from which an echo of `p`'s round-`r` message has been delivered. -/
noncomputable def echoers (H : P → List (Msg P V)) (r : ℕ) (p : P) [Fintype P] : Finset P :=
  Finset.univ.filter fun s => ∃ w, Msg.echo r p w ∈ H s

/-- The round-`r` message of `q` received, according to the deliveries `H`. -/
noncomputable def recv (r : ℕ) (H : P → List (Msg P V)) (q : P) : Option V :=
  if h : ∃ w, Msg.val r w ∈ H q ∨ ∃ s, Msg.echo r q w ∈ H s then some h.choose else none

/-- The round results from the snapshots. -/
noncomputable def results (d : List (P → List (Msg P V))) : List (P → Option V) :=
  d.mapIdx fun r H => recv r H

/-- The echo produced when delivering `m` from `s`. -/
def echoOut (s : P) : Msg P V → List (Msg P V)
  | .val r w => [.echo r s w]
  | .echo .. => []

/-! ### Lemmas on results -/

@[simp] lemma length_results (d : List (P → List (Msg P V))) : (results d).length = d.length := by
  simp [results]

lemma getElem_results (d : List (P → List (Msg P V))) (r : ℕ) (h : r < (results d).length) :
    (results d)[r] = recv r (d[r]'(by simpa using h)) := by
  simp [results, List.getElem_mapIdx]

lemma results_append (d : List (P → List (Msg P V))) (H : P → List (Msg P V)) :
    results (d ++ [H]) = results d ++ [recv d.length H] := by
  simp [results, List.mapIdx_append]

lemma take_results_append (d : List (P → List (Msg P V))) (H : P → List (Msg P V)) {r : ℕ}
    (hr : r ≤ d.length) : (results (d ++ [H])).take r = (results d).take r := by
  rw [results_append, List.take_append_of_le_length (by simpa using hr)]

lemma recv_isSome_iff (r : ℕ) (H : P → List (Msg P V)) (q : P) :
    (recv r H q).isSome ↔ ∃ w, Msg.val r w ∈ H q ∨ ∃ s, Msg.echo r q w ∈ H s := by
  unfold recv; split_ifs with h <;> simp [h]

lemma recv_eq_some {r : ℕ} {H : P → List (Msg P V)} {q : P} {w : V} (h : recv r H q = some w) :
    Msg.val r w ∈ H q ∨ ∃ s, Msg.echo r q w ∈ H s := by
  unfold recv at h; split_ifs at h with h'
  cases h; exact h'.choose_spec

/-! ### List helpers -/

lemma take_of_prefix {α : Type*} {l l' : List α} (h : l <+: l') {n : ℕ} (hn : n ≤ l.length) :
    l'.take n = l.take n := by
  obtain ⟨t, rfl⟩ := h; exact List.take_append_of_le_length hn

lemma mem_of_mem_take_of_prefix {α : Type*} {l l' : List α} (h : l <+: l') {n : ℕ} {x : α}
    (hx : x ∈ l.take n) : x ∈ l' :=
  h.subset (List.mem_of_mem_take hx)

variable [Fintype P] [DecidableEq P]

/-- Does `p`, with deliveries `H`, end its current round `L`? -/
def Fires (f : ℕ) (H : P → List (Msg P V)) (L : ℕ) (p : P) : Prop :=
  Fintype.card P - f ≤ (echoers H L p).card

variable (P V) in
/-- **The echo protocol** for at most `f` Byzantine processes. -/
noncomputable def echoProtocol (f : ℕ) : SRBProtocol P V (Msg P V) (State P V) where
  relays
    | .val _ _ => ∅
    | .echo r q w => {(q, .val r w)}
  init _ cl := (⟨fun _ => [], []⟩, [.val 0 (cl [])])
  step p cl st s m :=
    let H := Function.update st.hist s (st.hist s ++ [m])
    if Fires f H st.done.length p then
      (⟨H, st.done ++ [H]⟩,
        echoOut s m ++ [.val (st.done.length + 1) (cl (results (st.done ++ [H])))])
    else (⟨H, st.done⟩, echoOut s m)
  rounds st := results st.done

end Echo

end Podc.TrustedHW
