import Papers.PODC2026.RankingOpinions.Dynamics
import Mathlib.Tactic.Ring

/-!
# The Ranking protocol (Section 6): states, rules, basic invariants

Breitkopf, Dallot, El-Hayek, Schmid, *Ranking Opinions with Few States in Population Protocols*,
PODC 2026 (arXiv:2605.18707), Section 6.

A state is `⟨i, 𝔦 | 𝔧, j⟩` plus a token bit: bra color `i = bc`, bra ranking `𝔦 = br`, ket ranking
`𝔧 = kr`, ket color `j = kc`, token `tok` (the token "for color `j`" sits on the ket `|𝔧, j⟩`).
So there are `2 · k⁴` states.

## Interpretation of the rules

* "If multiple cases apply, select the first case that does not leave the agents unchanged": the
  cases are the bullets of rules (2)–(7), in order. A case "`X` meets `Y`" is tried with
  `(X, Y) = (initiator, responder)` and then with `(X, Y) = (responder, initiator)`; the first
  (case, orientation) that changes something is applied.
* Rankings are incremented modulo `k` (rule (3)).
* **Fix (self-synchronisation).** After every interaction, an agent holding the token for its own
  bra color (`tok ∧ bc = kc`) copies its ket ranking into its bra ranking (`br := kr`). Without this
  the protocol is wrong: the token holder cannot "broadcast" (rule (4)) the new ranking to its own
  bra, see `RankingCounterexample.lean`.
-/

set_option linter.unusedSectionVars false

namespace RankingOpinions.Ranking

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol Finset

variable {k : ℕ}

/-- A state `⟨bc, br | kr, kc⟩` (with a token on the ket iff `tok`). -/
@[ext] structure RState (k : ℕ) where
  /-- bra color (= the input color of the agent; never changes). -/
  bc : Fin k
  /-- bra ranking (the output). -/
  br : Fin k
  /-- ket ranking. -/
  kr : Fin k
  /-- ket color. -/
  kc : Fin k
  /-- the agent holds the token of the color `kc`. -/
  tok : Bool
deriving DecidableEq

/-- States as tuples. -/
def RState.equiv : RState k ≃ Fin k × Fin k × Fin k × Fin k × Bool where
  toFun s := (s.bc, s.br, s.kr, s.kc, s.tok)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (RState k) := Fintype.ofEquiv _ RState.equiv.symm

/-- **Theorem 1.2 (state count)**: the Ranking protocol uses `2 · k⁴` states. -/
theorem card_RState : Fintype.card (RState k) = 2 * k ^ 4 := by
  rw [Fintype.card_congr RState.equiv]; simp; ring

/-- A rule ("case"): `X` meets `Y`. -/
abbrev Rule (k : ℕ) := RState k → RState k → RState k × RState k

variable [NeZero k]

/-- Rule (2), token deletion: `⟨j,𝔧|𝔦,i⟩*` meets `⟨ℓ,𝔩|𝔦',i⟩*` with `𝔧 ≤ 𝔩`: the latter becomes
`⟨ℓ,𝔩|𝔦,i⟩` (no token). -/
def r2 : Rule k := fun X Y =>
  if X.tok ∧ Y.tok ∧ X.kc = Y.kc ∧ X.br ≤ Y.br then (X, {Y with kr := X.kr, tok := false})
  else (X, Y)

/-- Rule (3), ranking uniqueness: `⟨j,𝔧|𝔦,i⟩*` meets `⟨ℓ,𝔩|𝔦,u⟩*` with `i < u`: `𝔲 ← 𝔲 + 1`. -/
def r3 : Rule k := fun X Y =>
  if X.tok ∧ Y.tok ∧ X.kr = Y.kr ∧ X.kc < Y.kc then (X, {Y with kr := Y.kr + 1}) else (X, Y)

/-- Rule (4), first bullet: `⟨i,𝔦|𝔧,j⟩*` meets `⟨u,𝔲|𝔧',j⟩` (no token): `𝔧' ← 𝔧`. -/
def r4a : Rule k := fun X Y =>
  if X.tok ∧ Y.tok = false ∧ X.kc = Y.kc then (X, {Y with kr := X.kr}) else (X, Y)

/-- Rule (4), second bullet: `⟨i,𝔦|𝔧,j⟩*` meets `⟨j,𝔧'|𝔲,u⟩◦`: `𝔧' ← 𝔧`. -/
def r4b : Rule k := fun X Y =>
  if X.tok ∧ Y.bc = X.kc then (X, {Y with br := X.kr}) else (X, Y)

/-- Rule (5), Circles on the rankings: exchange the kets (with their tokens) iff this strictly
decreases the minimum of the two weights. -/
def r5 : Rule k := fun X Y =>
  if Profitable (X.br, X.kr) (Y.br, Y.kr) then
    ({X with kr := Y.kr, kc := Y.kc, tok := Y.tok}, {Y with kr := X.kr, kc := X.kc, tok := X.tok})
  else (X, Y)

/-- Rule (6), first bullet: `⟨i,𝔦|𝔦,i⟩` meets `⟨ℓ,𝔩|𝔦,i⟩*`: the token moves to the former. -/
def r6a : Rule k := fun X Y =>
  if X.tok = false ∧ X.bc = X.kc ∧ X.br = X.kr ∧ Y.tok ∧ Y.kc = X.kc ∧ Y.kr = X.kr then
    ({X with tok := true}, {Y with tok := false})
  else (X, Y)

/-- Rule (6), second bullet: `⟨j,𝔧|𝔦,i⟩` meets `⟨ℓ,𝔩|𝔦,i⟩*` with `j ≠ i`, `ℓ ≠ i`, `𝔧 < 𝔩`:
the token moves to the former. -/
def r6b : Rule k := fun X Y =>
  if X.tok = false ∧ Y.tok ∧ X.kc = Y.kc ∧ X.kr = Y.kr ∧ X.bc ≠ X.kc ∧ Y.bc ≠ Y.kc ∧
      X.br < Y.br then
    ({X with tok := true}, {Y with tok := false})
  else (X, Y)

/-- Rule (7), first bullet: `⟨i,𝔦|𝔦,i⟩*` meets `⟨u,𝔲|0,v⟩*` with `v ≠ i`, `𝔦 ≠ 0`: the former
becomes `⟨i,0|0,i⟩*`, the latter `⟨u,𝔲|𝔦,v⟩*`. -/
def r7a : Rule k := fun X Y =>
  if X.tok ∧ Y.tok ∧ X.bc = X.kc ∧ X.br = X.kr ∧ Y.kr = 0 ∧ Y.kc ≠ X.bc ∧ X.br ≠ 0 then
    ({X with br := 0, kr := 0}, {Y with kr := X.br})
  else (X, Y)

/-- Rule (7), second bullet: `⟨i,𝔦|𝔧,j⟩*` meets `⟨i,𝔦|𝔩,ℓ⟩*` with `j, ℓ ≠ i`: they exchange
their ket rankings. -/
def r7b : Rule k := fun X Y =>
  if X.tok ∧ Y.tok ∧ X.bc = Y.bc ∧ X.br = Y.br ∧ X.kc ≠ X.bc ∧ Y.kc ≠ Y.bc then
    ({X with kr := Y.kr}, {Y with kr := X.kr})
  else (X, Y)

/-- The cases of rules (2)–(7), in order. -/
def rules : List (Rule k) := [r2, r3, r4a, r4b, r5, r6a, r6b, r7a, r7b]

end RankingOpinions.Ranking

namespace RankingOpinions.Ranking

variable {k : ℕ}

/-- Apply a case to the pair `(a, b)`: first with `X = a`, `Y = b`; if that leaves the agents
unchanged, with `X = b`, `Y = a`. -/
def applyCase (r : Rule k) (a b : RState k) : RState k × RState k :=
  if r a b ≠ (a, b) then r a b else (r b a).swap

/-- Apply the first case that does not leave the agents unchanged. -/
def firstChange : List (Rule k) → RState k → RState k → RState k × RState k
  | [], a, b => (a, b)
  | r :: rs, a, b => if applyCase r a b ≠ (a, b) then applyCase r a b else firstChange rs a b

/-- Self-synchronisation (our fix): the holder of the token of its own bra color copies its ket
ranking into its bra ranking. -/
def norm (s : RState k) : RState k :=
  if s.tok ∧ s.bc = s.kc then {s with br := s.kr} else s

/-- A state is normal if it is fixed by `norm`. -/
def Normal (s : RState k) : Prop := s.tok → s.bc = s.kc → s.br = s.kr

variable [NeZero k]

/-- The transition function of the Ranking protocol. -/
def rδ (a b : RState k) : RState k × RState k :=
  (norm (firstChange rules a b).1, norm (firstChange rules a b).2)

/-- The Ranking protocol (Section 6, with self-synchronisation). -/
def ranking (k : ℕ) [NeZero k] : Cslib.PopulationProtocol.Protocol (RState k) := ⟨rδ⟩

/-- Rule (1), initialization: an agent of color `i` starts in `⟨i, i | i, i⟩*`. -/
def initState (i : Fin k) : RState k := ⟨i, i, i, i, true⟩

/-- Rule (8), output: the bra ranking. -/
def output (s : RState k) : Fin k := s.br

/-! ## Local invariants of a transition -/

/-- The local invariants of a transition `(a, b) ↦ (a', b')`: bra colors are unchanged, the ket
colors are kept or exchanged, and every color holding a token before still holds one after. -/
structure PairInv (a b a' b' : RState k) : Prop where
  bc1 : a'.bc = a.bc
  bc2 : b'.bc = b.bc
  kc : (a'.kc = a.kc ∧ b'.kc = b.kc) ∨ (a'.kc = b.kc ∧ b'.kc = a.kc)
  tok : ∀ c, (a.tok ∧ a.kc = c ∨ b.tok ∧ b.kc = c) → (a'.tok ∧ a'.kc = c ∨ b'.tok ∧ b'.kc = c)

lemma PairInv.refl (a b : RState k) : PairInv a b a b :=
  ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, fun _ h => h⟩

lemma PairInv.symm {a b a' b' : RState k} (h : PairInv b a b' a') : PairInv a b a' b' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h2, h1, ?_, fun c hc => (h4 c hc.symm).symm⟩
  rcases h3 with h3 | h3
  · exact Or.inl ⟨h3.2, h3.1⟩
  · exact Or.inr ⟨h3.2, h3.1⟩

/-- A rule satisfies the local invariants. -/
def RuleInv (r : Rule k) : Prop := ∀ a b, PairInv a b (r a b).1 (r a b).2

lemma applyCase_inv {r : Rule k} (hr : RuleInv r) (a b : RState k) :
    PairInv a b (applyCase r a b).1 (applyCase r a b).2 := by
  unfold applyCase
  split_ifs
  · exact hr a b
  · exact (hr b a).symm

lemma firstChange_inv {rs : List (Rule k)} (h : ∀ r ∈ rs, RuleInv r) (a b : RState k) :
    PairInv a b (firstChange rs a b).1 (firstChange rs a b).2 := by
  induction rs with
  | nil => exact PairInv.refl a b
  | cons r rs ih =>
    simp only [firstChange]
    split_ifs
    · exact applyCase_inv (h r (by simp)) a b
    · exact ih (fun r hr => h r (by simp [hr]))

lemma norm_bc (s : RState k) : (norm s).bc = s.bc := by unfold norm; split_ifs <;> rfl
lemma norm_kc (s : RState k) : (norm s).kc = s.kc := by unfold norm; split_ifs <;> rfl
lemma norm_tok (s : RState k) : (norm s).tok = s.tok := by unfold norm; split_ifs <;> rfl
lemma norm_kr (s : RState k) : (norm s).kr = s.kr := by unfold norm; split_ifs <;> rfl

lemma normal_norm (s : RState k) : Normal (norm s) := by
  unfold Normal norm; split_ifs with h
  · intro _ _; rfl
  · intro ht hc; exact absurd ⟨ht, hc⟩ h

lemma norm_of_normal {s : RState k} (h : Normal s) : norm s = s := by
  unfold norm; split_ifs with h'
  · ext <;> simp [h h'.1 h'.2]
  · rfl

lemma PairInv.norm {a b a' b' : RState k} (h : PairInv a b a' b') :
    PairInv a b (norm a') (norm b') := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [norm_bc, h1], by rw [norm_bc, h2], by simpa only [norm_kc] using h3,
    by simpa only [norm_kc, norm_tok] using h4⟩


lemma r2_inv : RuleInv (k := k) r2 := by
  intro a b; unfold r2; split_ifs with h
  · refine ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, fun c hc => Or.inl ?_⟩
    rcases hc with hc | hc
    · exact hc
    · exact ⟨h.1, h.2.2.1.trans hc.2⟩
  · exact PairInv.refl a b

lemma r3_inv : RuleInv (k := k) r3 := by
  intro a b; unfold r3; split_ifs
  · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, fun c hc => hc⟩
  · exact PairInv.refl a b

lemma r4a_inv : RuleInv (k := k) r4a := by
  intro a b; unfold r4a; split_ifs
  · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, fun c hc => hc⟩
  · exact PairInv.refl a b

lemma r4b_inv : RuleInv (k := k) r4b := by
  intro a b; unfold r4b; split_ifs
  · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, fun c hc => hc⟩
  · exact PairInv.refl a b

lemma r5_inv : RuleInv (k := k) r5 := by
  intro a b; unfold r5; split_ifs
  · exact ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩, fun c hc => hc.symm⟩
  · exact PairInv.refl a b

lemma r6a_inv : RuleInv (k := k) r6a := by
  intro a b; unfold r6a; split_ifs with h
  · refine ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, fun c hc => Or.inl ⟨rfl, ?_⟩⟩
    rcases hc with hc | hc
    · exact hc.2
    · exact h.2.2.2.2.1.symm.trans hc.2
  · exact PairInv.refl a b

lemma r6b_inv : RuleInv (k := k) r6b := by
  intro a b; unfold r6b; split_ifs with h
  · refine ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, fun c hc => Or.inl ⟨rfl, ?_⟩⟩
    rcases hc with hc | hc
    · exact hc.2
    · exact h.2.2.1.trans hc.2
  · exact PairInv.refl a b

lemma r7a_inv : RuleInv (k := k) r7a := by
  intro a b; unfold r7a; split_ifs
  · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, fun c hc => hc⟩
  · exact PairInv.refl a b

lemma r7b_inv : RuleInv (k := k) r7b := by
  intro a b; unfold r7b; split_ifs
  · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, fun c hc => hc⟩
  · exact PairInv.refl a b

lemma rules_inv : ∀ r ∈ (rules : List (Rule k)), RuleInv r := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [r2_inv, r3_inv, r4a_inv, r4b_inv, r5_inv, r6a_inv, r6b_inv, r7a_inv, r7b_inv]

/-- Every transition of the Ranking protocol satisfies the local invariants. -/
lemma rδ_inv (a b : RState k) : PairInv a b (rδ a b).1 (rδ a b).2 :=
  (firstChange_inv rules_inv a b).norm

lemma rδ_normal (a b : RState k) : Normal (rδ a b).1 ∧ Normal (rδ a b).2 :=
  ⟨normal_norm _, normal_norm _⟩

end RankingOpinions.Ranking
