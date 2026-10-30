import Cslib.Computability.CommunicationComplexity.Protocol
import Mathlib

-- CSLib candidate: Cslib/Computability/CommunicationComplexity/OneRound.lean

/-!
# One-round (simultaneous-message) two-party protocols

In a *round* of a two-party protocol both parties send a message to each other simultaneously
(the convention of e.g. Chang–Mishra–Nguyen–Salim, PODC 2025, footnote 1). A deterministic
one-round protocol is given by the two message functions and the two output functions; each
party's output depends on its own input and the message it received. Unlike the protocol trees
of `Cslib.CommunicationComplexity.Protocol`, the parties have *different* outputs (e.g. each
party colours its own edges).

Messages are bit strings of variable length. To make sure that the lengths do not carry hidden
information, `OneRoundProtocol.toProtocol` turns a one-round protocol whose messages have length
`≤ LA` and `≤ LB` into a protocol tree of `Cslib.CommunicationComplexity` (one symbol from an
alphabet of size `2 ^ (L + 1)` per party, i.e. `L + 1` bits) of cost `≤ LA + LB + 2` computing the
same outputs (`toProtocol_costLE`, `toProtocol_eval_fst`, `toProtocol_eval_snd`).

## Main definitions

* `OneRoundProtocol X Y OA OB`, `OneRoundProtocol.outputA/outputB`.
* `Cslib.CommunicationComplexity.bitsVal`, `listCode`: injective codes of bit lists.
-/

namespace Cslib.CommunicationComplexity

/-- The natural number with binary digits `l` (least significant first). -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * bitsVal l

lemma bitsVal_lt : ∀ l : List Bool, bitsVal l < 2 ^ l.length
  | [] => by simp [bitsVal]
  | b :: l => by
    have := bitsVal_lt l
    simp only [bitsVal, List.length_cons, pow_succ]
    split <;> omega

lemma bitsVal_injective_of_length_eq :
    ∀ {l l' : List Bool}, l.length = l'.length → bitsVal l = bitsVal l' → l = l'
  | [], [], _, _ => rfl
  | b :: l, b' :: l', hlen, h => by
    simp only [bitsVal] at h
    have hb : b = b' := by
      cases b <;> cases b' <;> simp at h ⊢ <;> omega
    subst hb
    have : bitsVal l = bitsVal l' := by split at h <;> omega
    rw [bitsVal_injective_of_length_eq (by simpa using hlen) this]

/-- An injective code of all bit lists by natural numbers: `2 ^ |l| + bitsVal l`. -/
def listCode (l : List Bool) : ℕ := 2 ^ l.length + bitsVal l

lemma listCode_lt (l : List Bool) : listCode l < 2 ^ (l.length + 1) := by
  have := bitsVal_lt l
  rw [listCode, pow_succ]; omega

lemma listCode_injective : Function.Injective listCode := by
  intro l l' h
  have hl : l.length = l'.length := by
    by_contra hne
    have h1 := bitsVal_lt l
    have h2 := bitsVal_lt l'
    unfold listCode at h
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hlt
      rw [pow_succ] at this; omega
    · have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hlt
      rw [pow_succ] at this; omega
  refine bitsVal_injective_of_length_eq hl ?_
  unfold listCode at h; rw [hl] at h; omega

/-- Code of a bit list of length `≤ L` as a symbol of an alphabet of size `2 ^ (L + 1)`. -/
def boundedCode (L : ℕ) (l : List Bool) : Fin (2 ^ (L + 1)) :=
  if h : l.length ≤ L then
    ⟨listCode l, (listCode_lt l).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))⟩
  else 0

lemma boundedCode_val {L : ℕ} {l : List Bool} (hl : l.length ≤ L) :
    (boundedCode L l).val = listCode l := by
  simp [boundedCode, hl]

open Classical in
/-- Decoding of `boundedCode`. -/
noncomputable def boundedDecode (L : ℕ) (i : Fin (2 ^ (L + 1))) : List Bool :=
  if h : ∃ l : List Bool, l.length ≤ L ∧ boundedCode L l = i then h.choose else []

lemma boundedDecode_boundedCode {L : ℕ} {l : List Bool} (hl : l.length ≤ L) :
    boundedDecode L (boundedCode L l) = l := by
  have hex : ∃ l' : List Bool, l'.length ≤ L ∧ boundedCode L l' = boundedCode L l := ⟨l, hl, rfl⟩
  rw [boundedDecode, dite_eq_left hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have h3 := congrArg Fin.val h2
  rw [boundedCode_val h1, boundedCode_val hl] at h3
  exact listCode_injective h3

/-- A deterministic **one-round** two-party protocol: Alice (input `x : X`) and Bob (input
`y : Y`) simultaneously send the bit strings `msgA x` and `msgB y`; then Alice outputs
`outA x (msgB y)` and Bob outputs `outB y (msgA x)`. -/
structure OneRoundProtocol (X Y OA OB : Type*) where
  /-- Alice's message. -/
  msgA : X → List Bool
  /-- Bob's message. -/
  msgB : Y → List Bool
  /-- Alice's output, from her input and Bob's message. -/
  outA : X → List Bool → OA
  /-- Bob's output, from his input and Alice's message. -/
  outB : Y → List Bool → OB

namespace OneRoundProtocol

variable {X Y OA OB : Type*} (P : OneRoundProtocol X Y OA OB)

/-- Alice's output on inputs `x`, `y`. -/
def outputA (x : X) (y : Y) : OA := P.outA x (P.msgB y)

/-- Bob's output on inputs `x`, `y`. -/
def outputB (x : X) (y : Y) : OB := P.outB y (P.msgA x)

/-- The protocol communicates at most `c` bits on every input. -/
def CostLE (c : ℕ) : Prop := ∀ x y, (P.msgA x).length + (P.msgB y).length ≤ c

/-- The one-round protocol as a protocol tree: Alice sends her message as one symbol of an
alphabet of size `2 ^ (LA + 1)`, then Bob sends his (computed from his input only); the leaf
holds both parties' output functions. -/
noncomputable def toProtocol (LA LB : ℕ) : Protocol X Y ((X → OA) × (Y → OB)) :=
  .alice (2 ^ (LA + 1)) (fun x => boundedCode LA (P.msgA x)) fun i =>
    .bob (2 ^ (LB + 1)) (fun y => boundedCode LB (P.msgB y)) fun j =>
      .ret (fun x => P.outA x (boundedDecode LB j), fun y => P.outB y (boundedDecode LA i))

theorem toProtocol_costLE (LA LB : ℕ) : (P.toProtocol LA LB).CostLE (LA + LB + 2) := by
  simp only [toProtocol, Protocol.CostLE, Nat.clog_pow 2 _ (by norm_num)]
  refine ⟨by omega, fun _ => ⟨by omega, fun _ => trivial⟩⟩

variable {LA LB : ℕ} (hA : ∀ x, (P.msgA x).length ≤ LA) (hB : ∀ y, (P.msgB y).length ≤ LB)
include hA hB

omit hA in
theorem toProtocol_eval_fst (x : X) (y : Y) :
    ((P.toProtocol LA LB).eval x y).1 x = P.outputA x y := by
  simp [toProtocol, Protocol.eval, outputA, boundedDecode_boundedCode (hB y)]

omit hB in
theorem toProtocol_eval_snd (x : X) (y : Y) :
    ((P.toProtocol LA LB).eval x y).2 y = P.outputB x y := by
  simp [toProtocol, Protocol.eval, outputB, boundedDecode_boundedCode (hA x)]

end OneRoundProtocol

end Cslib.CommunicationComplexity
