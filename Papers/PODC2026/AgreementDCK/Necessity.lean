import Papers.PODC2026.AgreementDCK.Dynamic

/-!
# Necessity of dynamic common knowledge (Theorems 1.2, 1.5 and Corollary 1.6)

David–Moses, *Brief Announcement: What is Agreement About if not Common Knowledge?*, PODC 2026.

A protocol is represented by the interpreted system `S` of its runs together with its decision
facts `dec i v` (`decideᵢ(v)`: process `i` decides `v` at the point). The paper's standing
assumption that a protocol decides "based on the local state of a process" is `DecLocal`.

The core of the section is one general lemma (`CN_of_precondition`): under `AoN(v)`, every
precondition `φ` for a nonfaulty process deciding `v` is dynamic common knowledge w.r.t. the
profile `𝛅(v) = (decide₁(v), …, decideₙ(v))` in every run in which all nonfaulty processes decide
`v`; by knowledge of preconditions, a nonfaulty process deciding `v` has nonfaulty knowledge of
this (`KN_CN_of_precondition`). Theorem 1.5 and both parts of Corollary 1.6 are instances.
-/

open Cslib.Knowledge Cslib.Knowledge.RunFact Cslib.Knowledge.System

namespace Podc.Knowledge

namespace Decisions

variable {ι R V : Type*} {L : ι → Type*} (S : System ι R L) (dec : ι → V → Fact R)

/-- Decisions are triggered by local states: `decideᵢ(v)` is `i`-local for every `i` and `v`. -/
def DecLocal : Prop := ∀ i v, S.IsLocal i (dec i v)

/-- `all_decide(v)`: every nonfaulty process of the run decides `v` at some time. -/
def allDecide (v : V) (r : R) : Prop := ∀ i ∈ S.nf r, ∃ t, dec i v r t

/-- `AoN(v)`: `⊨ i ∈ N ∧ decideᵢ(v) → all_decide(v)`. -/
def AoN (v : V) : Prop := ∀ i r t, i ∈ S.nf r → dec i v r t → allDecide S dec v r

/-- The profile `𝛅(v) = (decide₁(v), …, decideₙ(v))`. -/
def δ (v : V) : ι → Fact R := fun i => dec i v

/-- `φ` is a precondition for (nonfaulty) decisions on `v`: `⊨ i ∈ N ∧ decideᵢ(v) → φ`. -/
def Precondition (v : V) (φ : Fact R) : Prop := ∀ i r t, i ∈ S.nf r → dec i v r t → φ r t

/-- The protocol satisfies the validity condition `valid` (a run fact for every value):
`⊨ i ∈ N ∧ decideᵢ(v) → valid(v)` for every `v`. -/
def Validity (valid : V → R → Prop) : Prop := ∀ v, Precondition S dec v (lift (valid v))

/-- Agreement: no two nonfaulty processes decide different values in the same run. -/
def Agreement : Prop :=
  ∀ i j r t t' v w, i ∈ S.nf r → j ∈ S.nf r → dec i v r t → dec j w r t' → v = w

/-- Decision (termination): every nonfaulty process decides some value. -/
def Decision : Prop := ∀ r, ∀ i ∈ S.nf r, ∃ v t, dec i v r t

/-- `no_dec(w)`: no nonfaulty process decides `w` in the run. -/
def noDec (w : V) (r : R) : Prop := ∀ j ∈ S.nf r, ∀ t, ¬ dec j w r t

/-- Decisions of nonfaulty processes are remembered (stable): once a nonfaulty process satisfies
`decideᵢ(v)`, it does so forever after. -/
def Stable : Prop := ∀ i v r t t', i ∈ S.nf r → t ≤ t' → dec i v r t → dec i v r t'

variable {S dec}

/-- **Theorem 1.2** (knowledge of preconditions, [29]) for decisions: if `⊨ i ∈ N ∧ decideᵢ(v) → ψ`,
then `⊨ i ∈ N ∧ decideᵢ(v) → K_i^N ψ`. -/
theorem theorem_1_2 (hloc : DecLocal S dec) {i : ι} {v : V} {ψ : Fact R}
    (h : ∀ r t, i ∈ S.nf r → dec i v r t → ψ r t) :
    ∀ r t, i ∈ S.nf r → dec i v r t → S.KN i ψ r t :=
  kop (hloc i v) h

/-- Consequence of Theorem 1.2 noted in the paper: under `AoN(v)`, `K_i^N all_decide(v)` is a
precondition for a nonfaulty `i` deciding `v`. -/
theorem KN_allDecide (hloc : DecLocal S dec) {v : V} (haon : AoN S dec v) :
    ∀ i r t, i ∈ S.nf r → dec i v r t → S.KN i (lift (allDecide S dec v)) r t :=
  fun i => theorem_1_2 hloc (haon i)

/-- **Key lemma.** Under `AoN(v)`, every precondition `φ` for deciding `v` is dynamic common
knowledge w.r.t. `𝛅(v)` in every run in which all nonfaulty processes decide `v`. -/
theorem CN_of_precondition (hloc : DecLocal S dec) {v : V} (haon : AoN S dec v) {φ : Fact R}
    (hφ : Precondition S dec v φ) : ∀ r, allDecide S dec v r → S.CN (δ dec v) φ r := by
  refine CN_of_EN_valid fun r hr i hi => ⟨hr i hi, fun t ht => ?_⟩
  exact theorem_1_2 hloc (ψ := fun r t => φ r t ∧ allDecide S dec v r)
    (fun r t hi hd => ⟨hφ i r t hi hd, haon i r t hi hd⟩) r t hi ht

/-- A nonfaulty process deciding `v` knows (nonfaulty knowledge) that every precondition for
deciding `v` is dynamic common knowledge w.r.t. `𝛅(v)`. -/
theorem KN_CN_of_precondition (hloc : DecLocal S dec) {v : V} (haon : AoN S dec v) {φ : Fact R}
    (hφ : Precondition S dec v φ) :
    ∀ i r t, i ∈ S.nf r → dec i v r t → S.KN i (lift (S.CN (δ dec v) φ)) r t :=
  fun i => theorem_1_2 hloc fun r t hi hd =>
    CN_of_precondition hloc haon hφ r (haon i r t hi hd)

/-- **Theorem 1.5 (Necessity of DCK).** If the protocol satisfies `AoN(v)`, then
`⊨ i ∈ N ∧ decideᵢ(v) → K_i^N (C^N@𝛅(v) (all_decide(v)))`. -/
theorem theorem_1_5 (hloc : DecLocal S dec) {v : V} (haon : AoN S dec v) :
    ∀ i r t, i ∈ S.nf r → dec i v r t →
      S.KN i (lift (S.CN (δ dec v) (lift (allDecide S dec v)))) r t :=
  KN_CN_of_precondition hloc haon haon

/-- The run fact `all_decide(v)` is itself dynamic common knowledge w.r.t. `𝛅(v)`:
`⊨ all_decide(v) → C^N@𝛅(v) (all_decide(v))` (used in the discussion of Theorem 1.7). -/
theorem allDecide_CN (hloc : DecLocal S dec) {v : V} (haon : AoN S dec v) :
    ∀ r, allDecide S dec v r → S.CN (δ dec v) (lift (allDecide S dec v)) r :=
  CN_of_precondition hloc haon haon

/-- **Corollary 1.6, first part.** If `P` satisfies `AoN(v)` and the validity condition `valid`,
then `⊨ i ∈ N ∧ decideᵢ(v) → K_i^N (C^N@𝛅(v) (valid(v)))`. -/
theorem corollary_1_6_validity (hloc : DecLocal S dec) {valid : V → R → Prop}
    (hval : Validity S dec valid) {v : V} (haon : AoN S dec v) :
    ∀ i r t, i ∈ S.nf r → dec i v r t → S.KN i (lift (S.CN (δ dec v) (lift (valid v)))) r t :=
  KN_CN_of_precondition hloc haon (hval v)

/-- **Corollary 1.6, second part.** If `P` satisfies `AoN(v)` and Agreement, and `v ≠ w`, then
`⊨ i ∈ N ∧ decideᵢ(v) → K_i^N (C^N@𝛅(v) (no_dec(w)))`. -/
theorem corollary_1_6_noDec (hloc : DecLocal S dec) (hagr : Agreement S dec) {v w : V}
    (hvw : v ≠ w) (haon : AoN S dec v) :
    ∀ i r t, i ∈ S.nf r → dec i v r t →
      S.KN i (lift (S.CN (δ dec v) (lift (noDec S dec w)))) r t :=
  KN_CN_of_precondition hloc haon fun i r t hi hd j hj t' hd' =>
    hvw (hagr i j r t t' v w hi hj hd hd')

end Decisions

end Podc.Knowledge
