import Papers.PODC2026.RankingOpinions.UnorderedOrdering
import Papers.PODC2026.RankingOpinions.Circles
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# The Ord-Circles protocol (Theorem 5.2)

Breitkopf, Dallot, El-Hayek, Schmid, *Ranking Opinions with Few States in Population Protocols*,
PODC 2026 (arXiv:2605.18707), Section 5.2 and Appendix 8.7.

Colors live in an arbitrary type `Col` with decidable equality; labels (bras, kets) in `Fin k`.
An agent stores its initial color `ic`, a leader bit `ld`, an ordering state
`os ∈ {U, I, CL, CLW}`, a braket `⟨bra|ket⟩` and an output color `out`.
Initially `ld = 1`, `os = U`, `⟨0|0⟩`, `out = ic`.

## Interpretation of the transition function (initiator `a`, responder `b`)

*Re-initializing* `a` for a label `l` sets `⟨l|l⟩`, `os = U`, `out = ic` (`reinit`).
`a` is *pending* if `os_a = CL`, *unstable* if `os_a ∈ {I, CLW}`, *consistent* if `bra = ket`.
The steps are applied in sequence:

1. (`step1`) If `a`, `b` are leaders of the same color, `a` stops being a leader. Then, if `b` is
   the leader of `a` (same color, `b` leader, `a` not), `bra_a ≠ bra_b` and `a` is not pending,
   `os_a := CLW`. Then, if `a`, `b` are leaders of different colors with the same bra and
   `os_b = U`, `os_a := I`. (`step1_eq_seq` shows that our closed form is this sequential
   reading.)
2. (`step2`) If `a` or `b` is pending (after step 1): if `a` is pending, `b` is a leader and they
   have the same color, `a` re-initializes for `bra_b`. *Pending agents do not take part in the
   other steps*: the interaction ends here.
3. If `a` is unstable and inconsistent and `ket_b = bra_a`, `a` and `b` exchange their kets.
4. If `a` is unstable and consistent: if `os_a = I`, `a` re-initializes for `bra_a + 1 mod k`;
   if `os_a = CLW`, `os_a := CL`. (Steps 3, 4: `step34`.) If `a` became pending, the
   interaction ends here (pending agents do not take part in Circles).
5. (`step5`) Circles: the agents exchange kets iff profitable; then, if exactly one of the two
   brakets is diagonal `⟨i|i⟩`, both agents set `out` to the *initial color* of that agent.

The output of an agent is `out`.

## Results

* `ordCircles_ordering` (**Lemma 8.13**) and `ordCircles_correct` (**Theorem 5.2**): with at most
  `k` colors, under weak fairness for *ordered* pairs (`Execution.OrderedFair`), eventually all
  agents are in ordering state `U`, two agents have the same bra iff they have the same color,
  and, if a unique majority color `μ` exists, all agents output `μ` forever.
* `ordCirclesSymm_correct`: the symmetrized protocol under (unordered) weak fairness.
* `ordCircles_not_weaklyFair`: Theorem 5.2 fails under weak fairness for unordered pairs.
* `card_ocState`: `|Col|² · 8 · k²` states, i.e. `O(k⁴)`.
-/

set_option linter.unusedSectionVars false

namespace RankingOpinions.Unordered

open Finset Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

variable {Col : Type*} [DecidableEq Col] {k : ℕ}

/-- Ordering states: unchanged (stable), increment, copy leader (pending), copy leader wait. -/
inductive OS
  | U
  | I
  | CL
  | CLW
  deriving DecidableEq

instance : Fintype OS := ⟨{.U, .I, .CL, .CLW}, by intro x; cases x <;> simp⟩

/-- Unstable ordering states: `I` and `CLW`. -/
def OS.unstable : OS → Prop
  | .I => True
  | .CLW => True
  | _ => False

instance : DecidablePred OS.unstable := fun o => by cases o <;> unfold OS.unstable <;> infer_instance

/-- States of Ord-Circles. -/
@[ext] structure OCState (Col : Type*) (k : ℕ) where
  /-- Initial color. -/
  ic : Col
  /-- Leader bit. -/
  ld : Bool
  /-- Ordering state. -/
  os : OS
  /-- Bra. -/
  bra : Fin k
  /-- Ket. -/
  ket : Fin k
  /-- Output color. -/
  out : Col
  deriving DecidableEq

/-- `OCState Col k ≃ Col × Bool × OS × Fin k × Fin k × Col`. -/
def OCState.equiv : OCState Col k ≃ Col × Bool × OS × Fin k × Fin k × Col where
  toFun s := (s.ic, s.ld, s.os, s.bra, s.ket, s.out)
  invFun s := ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype Col] : Fintype (OCState Col k) := Fintype.ofEquiv _ OCState.equiv.symm

/-- **Theorem 5.2, state count**: `|Col|² · 8 · k²` states, at most `8 k⁴` with `≤ k` colors. -/
theorem card_ocState [Fintype Col] :
    Fintype.card (OCState Col k) = Fintype.card Col ^ 2 * 8 * k ^ 2 := by
  rw [Fintype.card_congr OCState.equiv]
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  rw [show Fintype.card OS = 4 from rfl]; ring

theorem card_ocState_le [Fintype Col] (hC : Fintype.card Col ≤ k) :
    Fintype.card (OCState Col k) ≤ 8 * k ^ 4 := by
  rw [card_ocState]
  have : Fintype.card Col ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left hC 2
  calc Fintype.card Col ^ 2 * 8 * k ^ 2 ≤ k ^ 2 * 8 * k ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
    _ = 8 * k ^ 4 := by ring

/-- Re-initialization for the label `l`. -/
def reinit (p : OCState Col k) (l : Fin k) : OCState Col k :=
  { p with os := .U, bra := l, ket := l, out := p.ic }

/-- Step (1) (Ordering), closed form. -/
def step1 (p q : OCState Col k) : OCState Col k :=
  { p with
    ld := p.ld && !(decide (p.ic = q.ic) && q.ld)
    os := if p.ic = q.ic ∧ q.ld = true ∧ p.bra ≠ q.bra ∧ p.os ≠ .CL then .CLW
      else if p.ic ≠ q.ic ∧ p.ld = true ∧ q.ld = true ∧ p.bra = q.bra ∧ q.os = .U then .I
      else p.os }

/-- Step (1), literally as three rules applied in sequence. -/
def step1Seq (p q : OCState Col k) : OCState Col k :=
  let p1 := if p.ic = q.ic ∧ p.ld = true ∧ q.ld = true then { p with ld := false } else p
  let p2 := if p1.ic = q.ic ∧ q.ld = true ∧ p1.ld = false ∧ p1.bra ≠ q.bra ∧ p1.os ≠ .CL then
    { p1 with os := .CLW } else p1
  if p2.ic ≠ q.ic ∧ p2.ld = true ∧ q.ld = true ∧ p2.bra = q.bra ∧ q.os = .U then
    { p2 with os := .I } else p2

lemma step1_eq_seq (p q : OCState Col k) : step1 p q = step1Seq p q := by
  obtain ⟨i1, l1, o1, b1, k1, u1⟩ := p
  obtain ⟨i2, l2, o2, b2, k2, u2⟩ := q
  unfold step1 step1Seq
  by_cases h : i1 = i2 <;> cases l1 <;> cases l2 <;> simp [h] <;> split_ifs <;> simp_all

/-- Step (2): the pending initiator copies the bra of its leader. -/
def step2 (p q : OCState Col k) : OCState Col k :=
  if p.os = .CL ∧ p.ic = q.ic ∧ q.ld = true then reinit p q.bra else p

/-- Condition of step (3): `a` is unstable and inconsistent, and `ket_b = bra_a`. -/
def Swap3 (p q : OCState Col k) : Prop := p.os.unstable ∧ p.bra ≠ p.ket ∧ q.ket = p.bra

instance (p q : OCState Col k) : Decidable (Swap3 p q) := by unfold Swap3; infer_instance

/-- Step (3), initiator. -/
def step3a (p q : OCState Col k) : OCState Col k := if Swap3 p q then { p with ket := q.ket } else p

/-- Step (3), responder. -/
def step3b (p q : OCState Col k) : OCState Col k := if Swap3 p q then { q with ket := p.ket } else q

/-- Step (4). -/
def step4 (p : OCState Col k) : OCState Col k :=
  if p.os.unstable ∧ p.bra = p.ket then
    (if p.os = .I then reinit p (cyc p.bra) else { p with os := .CL }) else p

/-- Steps (3) and (4). -/
def step34 (p q : OCState Col k) : OCState Col k × OCState Col k :=
  (step4 (step3a p q), step3b p q)

/-- The output rule of Circles, with colors instead of labels. -/
def outRule (p q : OCState Col k) : OCState Col k × OCState Col k :=
  if p.bra = p.ket ∧ q.bra ≠ q.ket then ({ p with out := p.ic }, { q with out := p.ic })
  else if q.bra = q.ket ∧ p.bra ≠ p.ket then ({ p with out := q.ic }, { q with out := q.ic })
  else (p, q)

/-- Step (5): Circles. -/
def step5 (p q : OCState Col k) : OCState Col k × OCState Col k :=
  if Profitable (p.bra, p.ket) (q.bra, q.ket) then
    outRule { p with ket := q.ket } { q with ket := p.ket }
  else outRule p q

/-- The transition function of Ord-Circles. -/
def ocδ (p q : OCState Col k) : OCState Col k × OCState Col k :=
  if (step1 p q).os = .CL ∨ q.os = .CL then (step2 (step1 p q) q, q)
  else if (step34 (step1 p q) q).1.os = .CL then step34 (step1 p q) q
  else step5 (step34 (step1 p q) q).1 (step34 (step1 p q) q).2

/-- The Ord-Circles protocol. -/
def ordCircles (Col : Type*) [DecidableEq Col] (k : ℕ) : Protocol (OCState Col k) := ⟨ocδ⟩

/-- Initial configuration. -/
def ocInit {A : Type*} (input : A → Col) (hk : 0 < k) : Config A (OCState Col k) :=
  fun a => ⟨input a, true, .U, ⟨0, hk⟩, ⟨0, hk⟩, input a⟩

/-! ### Basic properties of the transition function -/

section Pure

variable (p q : OCState Col k)

@[simp] lemma step1_ic : (step1 p q).ic = p.ic := rfl
@[simp] lemma step1_bra : (step1 p q).bra = p.bra := rfl
@[simp] lemma step1_ket : (step1 p q).ket = p.ket := rfl
@[simp] lemma step1_ld : (step1 p q).ld = (p.ld && !(decide (p.ic = q.ic) && q.ld)) := rfl
@[simp] lemma reinit_ic (l : Fin k) : (reinit p l).ic = p.ic := rfl
@[simp] lemma reinit_ld (l : Fin k) : (reinit p l).ld = p.ld := rfl
@[simp] lemma reinit_os (l : Fin k) : (reinit p l).os = .U := rfl
@[simp] lemma reinit_bra (l : Fin k) : (reinit p l).bra = l := rfl
@[simp] lemma reinit_ket (l : Fin k) : (reinit p l).ket = l := rfl

lemma step34_snd : (step34 p q).2.ic = q.ic ∧ (step34 p q).2.ld = q.ld ∧
    (step34 p q).2.os = q.os ∧ (step34 p q).2.bra = q.bra ∧ (step34 p q).2.out = q.out := by
  unfold step34 step3b; split_ifs <;> simp

lemma step5_fields : (step5 p q).1.ic = p.ic ∧ (step5 p q).1.ld = p.ld ∧
    (step5 p q).1.os = p.os ∧ (step5 p q).1.bra = p.bra ∧
    (step5 p q).2.ic = q.ic ∧ (step5 p q).2.ld = q.ld ∧
    (step5 p q).2.os = q.os ∧ (step5 p q).2.bra = q.bra := by
  unfold step5 outRule; split_ifs <;> simp

lemma step5_kets : ((step5 p q).1.bra, (step5 p q).1.ket) =
      (exch (p.bra, p.ket) (q.bra, q.ket)).1 ∧
    ((step5 p q).2.bra, (step5 p q).2.ket) = (exch (p.bra, p.ket) (q.bra, q.ket)).2 := by
  unfold step5 outRule exch; split_ifs <;> simp_all

lemma ocδ_snd : (ocδ p q).2.ic = q.ic ∧ (ocδ p q).2.ld = q.ld ∧
    (ocδ p q).2.os = q.os ∧ (ocδ p q).2.bra = q.bra := by
  have h34 := step34_snd (step1 p q) q
  have h5 := step5_fields (step34 (step1 p q) q).1 (step34 (step1 p q) q).2
  unfold ocδ; split_ifs
  · simp
  · exact ⟨h34.1, h34.2.1, h34.2.2.1, h34.2.2.2.1⟩
  · exact ⟨h5.2.2.2.2.1.trans h34.1, h5.2.2.2.2.2.1.trans h34.2.1,
      h5.2.2.2.2.2.2.1.trans h34.2.2.1, h5.2.2.2.2.2.2.2.trans h34.2.2.2.1⟩

lemma step3a_fields : (step3a p q).ic = p.ic ∧ (step3a p q).ld = p.ld ∧ (step3a p q).os = p.os ∧
    (step3a p q).bra = p.bra := by
  unfold step3a; split_ifs <;> simp

lemma step4_fields : (step4 p).ic = p.ic ∧ (step4 p).ld = p.ld := by
  unfold step4; split_ifs <;> simp

lemma step34_fst_ic_ld : (step34 p q).1.ic = p.ic ∧ (step34 p q).1.ld = p.ld := by
  unfold step34
  rw [(step4_fields _).1, (step4_fields _).2, (step3a_fields p q).1, (step3a_fields p q).2.1]
  simp

lemma ocδ_fst_ic_ld : (ocδ p q).1.ic = p.ic ∧
    (ocδ p q).1.ld = (p.ld && !(decide (p.ic = q.ic) && q.ld)) := by
  have h34 := step34_fst_ic_ld (step1 p q) q
  have h5 := step5_fields (step34 (step1 p q) q).1 (step34 (step1 p q) q).2
  unfold ocδ; split_ifs
  · unfold step2; split_ifs <;> simp
  · simpa using h34
  · rw [h5.1, h5.2.1]; simpa using h34

lemma step1_os : (step1 p q).os =
    if p.ic = q.ic ∧ q.ld = true ∧ p.bra ≠ q.bra ∧ p.os ≠ .CL then .CLW
    else if p.ic ≠ q.ic ∧ p.ld = true ∧ q.ld = true ∧ p.bra = q.bra ∧ q.os = .U then .I
    else p.os := rfl

lemma step1_os_CL : (step1 p q).os = .CL → p.os = .CL := by
  rw [step1_os]; split_ifs <;> simp_all

lemma step2_osbra : ((step2 p q).os, (step2 p q).bra) =
    if p.os = .CL ∧ p.ic = q.ic ∧ q.ld = true then (.U, q.bra) else (p.os, p.bra) := by
  unfold step2; split_ifs <;> simp

lemma step2_fields : (step2 p q).ic = p.ic ∧ (step2 p q).ld = p.ld := by
  unfold step2; split_ifs <;> simp

lemma step34_osbra : ((step34 p q).1.os, (step34 p q).1.bra) =
    if p.os.unstable ∧ (p.bra = p.ket ∨ q.ket = p.bra) then
      (if p.os = .I then (.U, cyc p.bra) else (.CL, p.bra)) else (p.os, p.bra) := by
  have h3 := step3a_fields p q
  unfold step34 step4
  simp only
  rw [h3.2.2.1, h3.2.2.2]
  by_cases hu : p.os.unstable
  · have hk : p.bra = (step3a p q).ket ↔ (p.bra = p.ket ∨ q.ket = p.bra) := by
      unfold step3a Swap3
      split_ifs with h
      · exact ⟨fun _ => Or.inr h.2.2, fun _ => h.2.2.symm⟩
      · push Not at h
        refine ⟨Or.inl, ?_⟩
        rintro (h1 | h1)
        · exact h1
        · by_contra h2; exact h hu h2 h1
    simp only [hu, hk, true_and]
    split_ifs <;> simp [reinit, h3.2.2.2, h3.2.2.1]
  · simp [hu, h3.2.2.2, h3.2.2.1]

/-- The ordering part (ordering state and bra) of the initiator after an interaction. -/
lemma ocδ_fst_osbra : ((ocδ p q).1.os, (ocδ p q).1.bra) =
    if (step1 p q).os = .CL ∨ q.os = .CL then ((step2 (step1 p q) q).os, (step2 (step1 p q) q).bra)
    else ((step34 (step1 p q) q).1.os, (step34 (step1 p q) q).1.bra) := by
  have h5 := step5_fields (step34 (step1 p q) q).1 (step34 (step1 p q) q).2
  unfold ocδ; split_ifs
  · rfl
  · rfl
  · rw [h5.2.2.1, h5.2.2.2.1]

end Pure

section Pure2

variable {p q : OCState Col k}


/-- Local invariant: pending agents are consistent, and leaders are in ordering state `U` or
`I`. -/
def Inv (s : OCState Col k) : Prop :=
  (s.os = .CL → s.bra = s.ket) ∧ (s.ld = true → s.os = .U ∨ s.os = .I)

lemma inv_step1 (hp : Inv p) : Inv (step1 p q) := by
  refine ⟨fun h => hp.1 (step1_os_CL p q h), fun h => ?_⟩
  simp only [step1_ld, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.and_eq_false_imp, decide_eq_true_eq] at h
  rw [step1_os]
  split_ifs with h1 h2
  · exact absurd (h.2 h1.1) (by simp [h1.2.1])
  · exact Or.inr rfl
  · exact hp.2 h.1

lemma inv_step2 (hp : Inv p) : Inv (step2 p q) := by
  unfold step2; split_ifs
  · exact ⟨fun _ => rfl, fun _ => Or.inl rfl⟩
  · exact hp

lemma inv_step34 (hp : Inv p) (hq : Inv q) (hpc : p.os ≠ .CL) (hqc : q.os ≠ .CL) :
    Inv (step34 p q).1 ∧ Inv (step34 p q).2 := by
  have h3 := step3a_fields p q
  have hs := step34_snd p q
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => absurd (hs.2.2.1 ▸ h) hqc,
    fun h => hs.2.2.1 ▸ hq.2 (hs.2.1 ▸ h)⟩⟩
  · -- the initiator becomes pending only in step (4), when consistent
    unfold step34 step4 at *
    split_ifs at h ⊢ with h4 h5
    · simp at h
    · exact h4.2
    · exact absurd (h3.2.2.1 ▸ h) hpc
  · unfold step34 at h ⊢
    rw [(step4_fields _).2, h3.2.1] at h
    have hos : (step3a p q).os = .U ∨ (step3a p q).os = .I := h3.2.2.1 ▸ hp.2 h
    unfold step4
    simp only
    split_ifs with h4 h5
    · exact Or.inl rfl
    · exfalso
      rcases hos with e | e
      · rw [e] at h4; exact h4.1
      · exact h5 e
    · exact hos

lemma inv_step5 (hp : Inv p) (hq : Inv q) (hpc : p.os ≠ .CL) (hqc : q.os ≠ .CL) :
    Inv (step5 p q).1 ∧ Inv (step5 p q).2 := by
  have h := step5_fields p q
  refine ⟨⟨fun e => absurd (h.2.2.1 ▸ e) hpc, fun e => h.2.2.1 ▸ hp.2 (h.2.1 ▸ e)⟩,
    ⟨fun e => absurd (h.2.2.2.2.2.2.1 ▸ e) hqc, fun e => h.2.2.2.2.2.2.1 ▸ hq.2 (h.2.2.2.2.2.1 ▸ e)⟩⟩

lemma inv_ocδ (hp : Inv p) (hq : Inv q) : Inv (ocδ p q).1 ∧ Inv (ocδ p q).2 := by
  unfold ocδ
  split_ifs with h1 h2
  · exact ⟨inv_step2 (inv_step1 hp), hq⟩
  · push Not at h1
    exact inv_step34 (inv_step1 hp) hq h1.1 h1.2
  · push Not at h1
    have h34 := inv_step34 (q := q) (inv_step1 hp) hq h1.1 h1.2
    have hs := step34_snd (step1 p q) q
    exact inv_step5 h34.1 h34.2 h2 (by rw [hs.2.2.1]; exact h1.2)

/-- The ordering state of the initiator after step (1), when it is not pending. -/
def os1 (p q : OCState Col k) : OS :=
  if p.ic = q.ic ∧ q.ld = true ∧ p.bra ≠ q.bra ∧ p.os ≠ .CL then .CLW
  else if p.ic ≠ q.ic ∧ p.ld = true ∧ q.ld = true ∧ p.bra = q.bra ∧ q.os = .U then .I
  else p.os

/-- **Closed form of the ordering part** `(os, bra)` of the initiator after an interaction. -/
lemma ocδ_ord (hp : Inv p) (hq : Inv q) : ((ocδ p q).1.os, (ocδ p q).1.bra) =
    if p.os = .CL ∨ q.os = .CL then
      (if p.os = .CL ∧ p.ic = q.ic ∧ q.ld = true then (.U, q.bra) else (p.os, p.bra))
    else if (os1 p q).unstable ∧ (p.bra = p.ket ∨ q.ket = p.bra) then
      (if os1 p q = .I then (.U, cyc p.bra) else (.CL, p.bra))
    else (os1 p q, p.bra) := by
  have h1 : (step1 p q).os = os1 p q := rfl
  have hA : ((step1 p q).os = .CL ∨ q.os = .CL) ↔ (p.os = .CL ∨ q.os = .CL) := by
    rw [h1, os1]
    constructor
    · rintro (h | h)
      · split_ifs at h; simp_all
      · exact Or.inr h
    · rintro (h | h)
      · left
        have hl : p.ld = false := by
          cases e : p.ld
          · rfl
          · rcases hp.2 e with h' | h' <;> simp_all
        split_ifs with c1 c2 <;> simp_all
      · exact Or.inr h
  rw [ocδ_fst_osbra, step34_osbra, step2_osbra]
  by_cases hc : p.os = .CL ∨ q.os = .CL
  · rw [ite_eq_left (hA.2 hc), ite_eq_left hc]
    -- in the pending branch, step (1) does not change the ordering state
    have : (step1 p q).os = p.os := by
      rw [h1, os1]
      rcases hc with hc | hc
      · have hl : p.ld = false := by
          cases e : p.ld
          · rfl
          · rcases hp.2 e with h' | h' <;> simp_all
        split_ifs <;> simp_all
      · have hl : q.ld = false := by
          cases e : q.ld
          · rfl
          · rcases hq.2 e with h' | h' <;> simp_all
        split_ifs <;> simp_all
    by_cases hh : p.os = .CL ∧ p.ic = q.ic ∧ q.ld = true
    · rw [ite_eq_left (show (step1 p q).os = .CL ∧ (step1 p q).ic = q.ic ∧ q.ld = true by
        rw [this]; exact hh), ite_eq_left hh]
    · rw [ite_eq_right (show ¬((step1 p q).os = .CL ∧ (step1 p q).ic = q.ic ∧ q.ld = true) by
        rw [this]; exact hh), ite_eq_right hh, this]
      rfl
  · rw [ite_eq_right (fun h => hc (hA.1 h)), ite_eq_right hc]
    by_cases hh : (os1 p q).unstable ∧ (p.bra = p.ket ∨ q.ket = p.bra)
    · rw [ite_eq_left (show (step1 p q).os.unstable ∧ ((step1 p q).bra = (step1 p q).ket ∨
          q.ket = (step1 p q).bra) from hh), ite_eq_left hh]
      rfl
    · rw [ite_eq_right (show ¬((step1 p q).os.unstable ∧ ((step1 p q).bra = (step1 p q).ket ∨
          q.ket = (step1 p q).bra)) from hh), ite_eq_right hh]
      rfl

lemma os1_of_ld (hl : p.ld = true)
    (hr : (p.ld && !(decide (p.ic = q.ic) && q.ld)) = true) :
    os1 p q = if p.ic ≠ q.ic ∧ q.ld = true ∧ p.bra = q.bra ∧ q.os = .U then .I else p.os := by
  unfold os1
  have : ¬(p.ic = q.ic ∧ q.ld = true) := by
    rintro ⟨h1, h2⟩; simp [hl, h1, h2] at hr
  rw [ite_eq_right (fun h => this ⟨h.1, h.2.1⟩)]
  by_cases h : p.ic ≠ q.ic ∧ q.ld = true ∧ p.bra = q.bra ∧ q.os = .U
  · rw [ite_eq_left ⟨h.1, hl, h.2⟩, ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ⟨h'.1, h'.2.2⟩), ite_eq_right h]

/-- **Leaders**: the ordering part of a (non-demoted) leader changes only by `U → I` or
`U → U(bra+1)` (when meeting a stable leader of another color with the same bra), or
`I → U(bra+1)`. -/
lemma ocδ_leader (hp : Inv p) (hq : Inv q) (hl : p.ld = true) (hr : (ocδ p q).1.ld = true) :
    ((ocδ p q).1.os = p.os ∧ (ocδ p q).1.bra = p.bra) ∨
    ((ocδ p q).1.os = .I ∧ (ocδ p q).1.bra = p.bra ∧ p.os = .U ∧
      (p.ic ≠ q.ic ∧ q.ld = true ∧ q.os = .U ∧ q.bra = p.bra)) ∨
    ((ocδ p q).1.os = .U ∧ (ocδ p q).1.bra = cyc p.bra ∧
      (p.os = .I ∨ (p.os = .U ∧ p.ic ≠ q.ic ∧ q.ld = true ∧ q.os = .U ∧ q.bra = p.bra))) := by
  have hord := ocδ_ord hp hq
  have hpo : p.os = .U ∨ p.os = .I := hp.2 hl
  have hpc : p.os ≠ .CL := by rcases hpo with h | h <;> rw [h] <;> simp
  rw [(ocδ_fst_ic_ld p q).2] at hr
  by_cases hqc : q.os = .CL
  · left
    rw [ite_eq_left (Or.inr hqc), ite_eq_right (fun h => hpc h.1)] at hord
    exact ⟨congrArg Prod.fst hord, congrArg Prod.snd hord⟩
  rw [ite_eq_right (by tauto), os1_of_ld hl hr] at hord
  by_cases h3 : p.ic ≠ q.ic ∧ q.ld = true ∧ p.bra = q.bra ∧ q.os = .U
  · rw [ite_eq_left h3] at hord
    by_cases h4 : p.bra = p.ket ∨ q.ket = p.bra
    · rw [ite_eq_left ⟨trivial, h4⟩, ite_eq_left rfl] at hord
      right; right
      refine ⟨congrArg Prod.fst hord, congrArg Prod.snd hord, ?_⟩
      rcases hpo with h | h
      · exact Or.inr ⟨h, h3.1, h3.2.1, h3.2.2.2, h3.2.2.1.symm⟩
      · exact Or.inl h
    · rw [ite_eq_right (fun h => h4 h.2)] at hord
      rcases hpo with h | h
      · right; left
        exact ⟨congrArg Prod.fst hord, congrArg Prod.snd hord, h, h3.1, h3.2.1, h3.2.2.2,
          h3.2.2.1.symm⟩
      · left; exact ⟨(congrArg Prod.fst hord).trans h.symm, congrArg Prod.snd hord⟩
  · rw [ite_eq_right h3] at hord
    rcases hpo with h | h
    · rw [h] at hord
      rw [ite_eq_right (fun h' => h'.1)] at hord
      left; exact ⟨(congrArg Prod.fst hord).trans h.symm, congrArg Prod.snd hord⟩
    · by_cases h4 : p.bra = p.ket ∨ q.ket = p.bra
      · rw [h, ite_eq_left ⟨trivial, h4⟩, ite_eq_left rfl] at hord
        right; right
        exact ⟨congrArg Prod.fst hord, congrArg Prod.snd hord, Or.inl h⟩
      · rw [ite_eq_right (fun h' => h4 h'.2)] at hord
        left; exact ⟨congrArg Prod.fst hord, congrArg Prod.snd hord⟩

/-- **Non-leaders**: the possible changes of the ordering part of a non-leader. -/
lemma ocδ_nonleader (hp : Inv p) (hq : Inv q) (hl : p.ld = false) :
    ((ocδ p q).1.os = p.os ∧ (ocδ p q).1.bra = p.bra) ∨
    ((ocδ p q).1.os = .CLW ∧ (ocδ p q).1.bra = p.bra ∧
      (p.ic = q.ic ∧ q.ld = true ∧ p.bra ≠ q.bra ∧ p.os ≠ .CL)) ∨
    ((ocδ p q).1.os = .CL ∧ (ocδ p q).1.bra = p.bra ∧
      (p.os = .CLW ∨ (p.ic = q.ic ∧ q.ld = true ∧ p.bra ≠ q.bra ∧ p.os ≠ .CL))) ∨
    ((ocδ p q).1.os = .U ∧ (ocδ p q).1.bra = q.bra ∧ p.os = .CL ∧ p.ic = q.ic ∧ q.ld = true) ∨
    ((ocδ p q).1.os = .U ∧ (ocδ p q).1.bra = cyc p.bra ∧ p.os = .I) := by
  have hord := ocδ_ord hp hq
  have h1 : os1 p q = if p.ic = q.ic ∧ q.ld = true ∧ p.bra ≠ q.bra ∧ p.os ≠ .CL then .CLW
      else p.os := by
    unfold os1
    split_ifs <;> simp_all
  by_cases hA : p.os = .CL ∨ q.os = .CL
  · rw [ite_eq_left hA] at hord
    by_cases h : p.os = .CL ∧ p.ic = q.ic ∧ q.ld = true
    · rw [ite_eq_left h] at hord
      right; right; right; left
      exact ⟨congrArg Prod.fst hord, congrArg Prod.snd hord, h⟩
    · rw [ite_eq_right h] at hord
      left; exact ⟨congrArg Prod.fst hord, congrArg Prod.snd hord⟩
  · rw [ite_eq_right hA, h1] at hord
    have hpc : p.os ≠ .CL := fun h => hA (Or.inl h)
    by_cases h2 : p.ic = q.ic ∧ q.ld = true ∧ p.bra ≠ q.bra ∧ p.os ≠ .CL
    · rw [ite_eq_left h2] at hord
      by_cases h4 : p.bra = p.ket ∨ q.ket = p.bra
      · rw [ite_eq_left ⟨trivial, h4⟩, ite_eq_right (by simp)] at hord
        right; right; left
        exact ⟨congrArg Prod.fst hord, congrArg Prod.snd hord, Or.inr h2⟩
      · rw [ite_eq_right (fun h => h4 h.2)] at hord
        right; left
        exact ⟨congrArg Prod.fst hord, congrArg Prod.snd hord, h2⟩
    · rw [ite_eq_right h2] at hord
      by_cases h4 : p.os.unstable ∧ (p.bra = p.ket ∨ q.ket = p.bra)
      · rw [ite_eq_left h4] at hord
        by_cases h5 : p.os = .I
        · rw [ite_eq_left h5] at hord
          right; right; right; right
          exact ⟨congrArg Prod.fst hord, congrArg Prod.snd hord, h5⟩
        · rw [ite_eq_right h5] at hord
          right; right; left
          refine ⟨congrArg Prod.fst hord, congrArg Prod.snd hord, Or.inl ?_⟩
          have := h4.1
          cases e : p.os <;> simp_all [OS.unstable]
      · rw [ite_eq_right h4] at hord
        left; exact ⟨congrArg Prod.fst hord, congrArg Prod.snd hord⟩

/-- A pending agent meeting its leader re-initializes. -/
lemma ocδ_pending (hp : Inv p) (hq : Inv q) (h1 : p.os = .CL) (h2 : p.ic = q.ic)
    (h3 : q.ld = true) : (ocδ p q).1.os = .U := by
  have hord := ocδ_ord hp hq
  rw [ite_eq_left (Or.inl h1), ite_eq_left ⟨h1, h2, h3⟩] at hord
  exact congrArg Prod.fst hord

/-- An unstable agent meeting a non-pending agent whose ket is its bra (or being consistent)
re-initializes or becomes pending. -/
lemma ocδ_unstable (hp : Inv p) (hq : Inv q) (h1 : p.os.unstable) (h2 : q.os ≠ .CL)
    (h3 : p.bra = p.ket ∨ q.ket = p.bra) :
    (ocδ p q).1.os = .U ∨ (ocδ p q).1.os = .CL := by
  have hord := ocδ_ord hp hq
  have hpc : p.os ≠ .CL := by intro h; rw [h] at h1; exact h1
  rw [ite_eq_right (by tauto)] at hord
  have hu : (os1 p q).unstable := by
    unfold os1; split_ifs <;> trivial
  rw [ite_eq_left ⟨hu, h3⟩] at hord
  split_ifs at hord
  · exact Or.inl (congrArg Prod.fst hord)
  · exact Or.inr (congrArg Prod.fst hord)

/-- Two stable leaders of different colors with the same bra: the initiator changes its
ordering part. -/
lemma ocδ_conflict (hp : Inv p) (hq : Inv q) (hk : 2 ≤ k) (h1 : p.ld = true) (h2 : q.ld = true)
    (h3 : p.ic ≠ q.ic) (h4 : p.os = .U) (h5 : q.os = .U) (h6 : p.bra = q.bra) :
    (ocδ p q).1.os ≠ p.os ∨ (ocδ p q).1.bra ≠ p.bra := by
  have hord := ocδ_ord hp hq
  rw [ite_eq_right (by rw [h4, h5]; simp)] at hord
  have ho : os1 p q = .I := by
    unfold os1; rw [ite_eq_right (fun h => h3 h.1), ite_eq_left ⟨h3, h1, h2, h6, h5⟩]
  rw [ho] at hord
  by_cases h7 : OS.I.unstable ∧ (p.bra = p.ket ∨ q.ket = p.bra)
  · rw [ite_eq_left h7, ite_eq_left rfl, Prod.mk.injEq] at hord
    right; rw [hord.2]; exact cyc_ne hk _
  · rw [ite_eq_right h7, Prod.mk.injEq] at hord
    left; rw [hord.1, h4]; simp

/-- A stable non-pending agent meeting the leader of its color with a different bra becomes
unstable (or pending). -/
lemma ocδ_copy (hp : Inv p) (hq : Inv q) (h1 : p.ic = q.ic) (h2 : q.ld = true)
    (h3 : p.bra ≠ q.bra) (h4 : p.os = .U) (h5 : q.os ≠ .CL) :
    (ocδ p q).1.os = .CLW ∨ (ocδ p q).1.os = .CL := by
  have hord := ocδ_ord hp hq
  rw [ite_eq_right (by rw [h4]; simp [h5])] at hord
  have ho : os1 p q = .CLW := by
    unfold os1; rw [ite_eq_left ⟨h1, h2, h3, by rw [h4]; simp⟩]
  rw [ho] at hord
  by_cases h7 : OS.CLW.unstable ∧ (p.bra = p.ket ∨ q.ket = p.bra)
  · rw [ite_eq_left h7, ite_eq_right (by simp), Prod.mk.injEq] at hord
    exact Or.inr hord.1
  · rw [ite_eq_right h7, Prod.mk.injEq] at hord
    exact Or.inl hord.1

/-- **Quiet interactions**: if neither agent is pending and the initiator does not change its
leader bit and its ordering part, then the interaction is a Circles interaction (step (5)). -/
lemma ocδ_quiet (hp : Inv p) (hq : Inv q) (hk : 2 ≤ k ∨ p.ic = q.ic) (hpc : p.os ≠ .CL) (hqc : q.os ≠ .CL)
    (h1 : (ocδ p q).1.os = p.os) (h2 : (ocδ p q).1.bra = p.bra) (h3 : (ocδ p q).1.ld = p.ld) :
    ocδ p q = step5 p q := by
  have hord := ocδ_ord hp hq
  rw [ite_eq_right (by tauto)] at hord
  rw [h1, h2] at hord
  have hno : ¬((os1 p q).unstable ∧ (p.bra = p.ket ∨ q.ket = p.bra)) := by
    intro h
    rw [ite_eq_left h] at hord
    by_cases hI : os1 p q = .I
    · rw [ite_eq_left hI, Prod.mk.injEq] at hord
      rcases hk with hk | hk
      · exact cyc_ne hk p.bra hord.2.symm
      · -- `os1 = I` from `os = U` needs two leaders of different colors
        unfold os1 at hI
        split_ifs at hI with c1 c2
        · exact c2.1 hk
        · rw [hI] at hord; exact absurd hord.1 (by simp)
    · rw [ite_eq_right hI, Prod.mk.injEq] at hord
      exact hpc hord.1
  rw [ite_eq_right hno] at hord
  have ho : os1 p q = p.os := (congrArg Prod.fst hord).symm
  have hs1 : step1 p q = p := by
    rw [(ocδ_fst_ic_ld p q).2] at h3
    ext
    · rfl
    · exact h3
    · exact ho
    · rfl
    · rfl
    · rfl
  have hno' : ¬(p.os.unstable ∧ (p.bra = p.ket ∨ q.ket = p.bra)) := by rwa [← ho]
  have hs3 : ¬ Swap3 p q := fun h => hno' ⟨h.1, Or.inr h.2.2⟩
  have hs4 : ¬(p.os.unstable ∧ p.bra = p.ket) := fun h => hno' ⟨h.1, Or.inl h.2⟩
  have h34 : step34 p q = (p, q) := by
    unfold step34 step3a step3b step4
    rw [ite_eq_right hs3, ite_eq_right hs3, ite_eq_right hs4]
  unfold ocδ
  rw [hs1, ite_eq_right (by tauto), h34]
  simp only
  rw [ite_eq_right hpc]

/-- Indicator of `x = l`. -/
def ind (x l : Fin k) : ℕ := if x = l then 1 else 0

/-- Local balance of bras and kets (Invariant 3.3) for an update `(p, q) ↦ (p', q')`. -/
def LBal (p q p' q' : OCState Col k) : Prop :=
  ∀ l, ind p'.bra l + ind q'.bra l + ind p.ket l + ind q.ket l =
    ind p.bra l + ind q.bra l + ind p'.ket l + ind q'.ket l

lemma LBal.trans {p q p' q' p'' q'' : OCState Col k} (h1 : LBal p q p' q')
    (h2 : LBal p' q' p'' q'') : LBal p q p'' q'' := fun l => by
  have := h1 l; have := h2 l; omega

lemma LBal.of_eq {p q p' q' : OCState Col k} (h1 : p'.bra = p.bra) (h2 : p'.ket = p.ket)
    (h3 : q'.bra = q.bra) (h4 : q'.ket = q.ket) : LBal p q p' q' := fun l => by
  rw [h1, h2, h3, h4]

lemma lbal_reinit {p : OCState Col k} (hp : p.bra = p.ket) (l : Fin k) :
    LBal p q (reinit p l) q := fun l' => by
  simp only [reinit_bra, reinit_ket, hp]; omega

lemma lbal_step3 : LBal p q (step3a p q) (step3b p q) := by
  unfold step3a step3b
  split_ifs with h
  · intro l; simp only; rw [h.2.2]; omega
  · exact LBal.of_eq rfl rfl rfl rfl

lemma lbal_step4 : LBal p q (step4 p) q := by
  unfold step4
  split_ifs with h h'
  · exact lbal_reinit h.2 _
  · exact LBal.of_eq rfl rfl rfl rfl
  · exact LBal.of_eq rfl rfl rfl rfl

lemma lbal_step5 : LBal p q (step5 p q).1 (step5 p q).2 := by
  have h := step5_kets p q
  unfold exch at h
  split_ifs at h with hp
  · simp only [Prod.mk.injEq] at h
    intro l; rw [h.1.1, h.1.2, h.2.1, h.2.2]; omega
  · simp only [Prod.mk.injEq] at h
    exact LBal.of_eq h.1.1 h.1.2 h.2.1 h.2.2

/-- **Lemma 8.9** (local form): every interaction preserves the balance of bras and kets. -/
lemma lbal_ocδ (hp : Inv p) : LBal p q (ocδ p q).1 (ocδ p q).2 := by
  have h1 : LBal p q (step1 p q) q := LBal.of_eq rfl rfl rfl rfl
  unfold ocδ
  split_ifs with hA hB
  · refine h1.trans ?_
    unfold step2
    split_ifs with h
    · exact lbal_reinit (hp.1 (step1_os_CL p q h.1)) _
    · exact LBal.of_eq rfl rfl rfl rfl
  · exact h1.trans (lbal_step3.trans lbal_step4)
  · refine h1.trans ((lbal_step3.trans lbal_step4).trans ?_)
    exact lbal_step5

/-- Outputs are always initial colors of some agent. -/
lemma ocδ_out (p q : OCState Col k) : ((ocδ p q).1.out = p.out ∨ (ocδ p q).1.out = p.ic ∨ (ocδ p q).1.out = q.ic) ∧
    ((ocδ p q).2.out = q.out ∨ (ocδ p q).2.out = p.ic ∨ (ocδ p q).2.out = q.ic) := by
  have hr : ∀ (p' q' : OCState Col k), p'.ic = p.ic → q'.ic = q.ic →
      (p'.out = p.out ∨ p'.out = p.ic ∨ p'.out = q.ic) →
      (q'.out = q.out ∨ q'.out = p.ic ∨ q'.out = q.ic) →
      ((outRule p' q').1.out = p.out ∨ (outRule p' q').1.out = p.ic ∨
        (outRule p' q').1.out = q.ic) ∧
      ((outRule p' q').2.out = q.out ∨ (outRule p' q').2.out = p.ic ∨
        (outRule p' q').2.out = q.ic) := by
    intro p' q' h1 h2 h3 h4
    unfold outRule
    split_ifs
    · simp [h1]
    · simp [h2]
    · exact ⟨h3, h4⟩
  have h34 : ∀ p' : OCState Col k, p'.ic = p.ic → (p'.out = p.out ∨ p'.out = p.ic) →
      ((step34 p' q).1.ic = p.ic ∧ ((step34 p' q).1.out = p.out ∨ (step34 p' q).1.out = p.ic)) ∧
      (step34 p' q).2.ic = q.ic ∧ (step34 p' q).2.out = q.out := by
    intro p' h1 h2
    refine ⟨⟨(step34_fst_ic_ld p' q).1.trans h1, ?_⟩, (step34_snd p' q).1,
      (step34_snd p' q).2.2.2.2⟩
    unfold step34 step4 step3a
    split_ifs <;> simp_all [reinit]
  unfold ocδ
  split_ifs with hA hB
  · refine ⟨?_, Or.inl rfl⟩
    unfold step2; split_ifs <;> simp [reinit, step1]
  · have := h34 (step1 p q) rfl (Or.inl rfl)
    exact ⟨by rcases this.1.2 with h | h <;> simp [h], Or.inl this.2.2⟩
  · have := h34 (step1 p q) rfl (Or.inl rfl)
    unfold step5
    split_ifs
    · exact hr _ _ this.1.1 this.2.1 (by rcases this.1.2 with h | h <;> simp [h])
        (Or.inl this.2.2)
    · exact hr _ _ this.1.1 this.2.1 (by rcases this.1.2 with h | h <;> simp [h])
        (Or.inl this.2.2)

end Pure2

/-! ### Executions: basic facts and leader election -/

variable {A : Type*} [DecidableEq A] [Fintype A]

section Exec

variable (E : (ordCircles Col k).Execution A)

lemma oc_init (t : ℕ) : E.config (t + 1) (E.sched t).1 =
    (ocδ (E.config t (E.sched t).1) (E.config t (E.sched t).2)).1 := by
  rw [E.step t, interact_self_left]; rfl

lemma oc_resp (t : ℕ) : E.config (t + 1) (E.sched t).2 =
    (ocδ (E.config t (E.sched t).1) (E.config t (E.sched t).2)).2 := by
  rw [E.step t, interact_self_right _ _ (E.sched_ne t)]; rfl

lemma oc_other {t : ℕ} {x : A} (ha : x ≠ (E.sched t).1) (hb : x ≠ (E.sched t).2) :
    E.config (t + 1) x = E.config t x := by
  rw [E.step t]; exact interact_other _ _ ha hb

/-- Agents other than the initiator keep their color, leader bit, ordering state and bra. -/
lemma oc_frame {t : ℕ} {x : A} (hx : x ≠ (E.sched t).1) :
    (E.config (t + 1) x).ic = (E.config t x).ic ∧ (E.config (t + 1) x).ld = (E.config t x).ld ∧
    (E.config (t + 1) x).os = (E.config t x).os ∧ (E.config (t + 1) x).bra = (E.config t x).bra := by
  by_cases hxb : x = (E.sched t).2
  · subst hxb; rw [oc_resp]; exact ocδ_snd _ _
  · rw [oc_other E hx hxb]; exact ⟨rfl, rfl, rfl, rfl⟩

lemma oc_ic_succ (t : ℕ) (x : A) : (E.config (t + 1) x).ic = (E.config t x).ic := by
  by_cases hx : x = (E.sched t).1
  · subst hx; rw [oc_init]; exact (ocδ_fst_ic_ld _ _).1
  · exact (oc_frame E hx).1

lemma oc_ic_eq (t : ℕ) (x : A) : (E.config t x).ic = (E.config 0 x).ic := by
  induction t with
  | zero => rfl
  | succ t ih => rw [oc_ic_succ, ih]

lemma oc_inv (h0 : ∀ x, Inv (E.config 0 x)) (t : ℕ) (x : A) : Inv (E.config t x) := by
  induction t generalizing x with
  | zero => exact h0 x
  | succ t ih =>
    by_cases hxa : x = (E.sched t).1
    · subst hxa; rw [oc_init]; exact (inv_ocδ (ih _) (ih _)).1
    · by_cases hxb : x = (E.sched t).2
      · subst hxb; rw [oc_resp]; exact (inv_ocδ (ih _) (ih _)).2
      · rw [oc_other E hxa hxb]; exact ih x

lemma oc_ld_succ_le (t : ℕ) (x : A) :
    (E.config (t + 1) x).ld = true → (E.config t x).ld = true := by
  by_cases hx : x = (E.sched t).1
  · subst hx; rw [oc_init, (ocδ_fst_ic_ld _ _).2]; simp only [Bool.and_eq_true]
    exact fun h => h.1
  · rw [(oc_frame E hx).2.1]; exact id

lemma oc_exists_leader (h0 : ∀ x, (E.config 0 x).ld = true) (t : ℕ) (x : A) :
    ∃ y, (E.config t y).ic = (E.config t x).ic ∧ (E.config t y).ld = true := by
  induction t generalizing x with
  | zero => exact ⟨x, rfl, h0 x⟩
  | succ t ih =>
    obtain ⟨y, hy1, hy2⟩ := ih x
    by_cases hya : y = (E.sched t).1
    · by_cases hl : (E.config (t + 1) y).ld = true
      · exact ⟨y, by rw [oc_ic_succ, oc_ic_succ, hy1], hl⟩
      · have hd : (E.config t (E.sched t).1).ic = (E.config t (E.sched t).2).ic ∧
            (E.config t (E.sched t).2).ld = true := by
          rw [hya, oc_init, (ocδ_fst_ic_ld _ _).2] at hl
          rw [hya] at hy2
          rw [hy2] at hl
          by_cases hc : (E.config t (E.sched t).1).ic = (E.config t (E.sched t).2).ic <;>
            cases hq : (E.config t (E.sched t).2).ld <;> simp_all
        refine ⟨(E.sched t).2, ?_, ?_⟩
        · rw [oc_ic_succ, oc_ic_succ, ← hy1, hya, hd.1]
        · rw [(oc_frame E (Ne.symm (E.sched_ne t))).2.1]; exact hd.2
    · exact ⟨y, by rw [oc_ic_succ, oc_ic_succ, hy1], by rw [(oc_frame E hya).2.1]; exact hy2⟩

lemma oc_leaders_eventually_const :
    ∃ T, ∀ t ≥ T, ∀ x, (E.config t x).ld = (E.config T x).ld := by
  obtain ⟨T, -, hT⟩ := eventually_const_of_antitone
    (fun t => (univ.filter fun x => (E.config t x).ld = true).card) 0
    (fun t _ => Finset.card_le_card fun x => by simpa using oc_ld_succ_le E t x)
  refine ⟨T, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => exact fun _ => rfl
  | succ t ht ih =>
    intro x
    have hsub : (univ.filter fun x => (E.config (t + 1) x).ld = true) ⊆
        univ.filter fun x => (E.config t x).ld = true :=
      fun y => by simpa using oc_ld_succ_le E t y
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by have := hT t ht; have := hT (t + 1) (by omega); omega)
    have := congrArg (fun s => x ∈ s) heq
    simp only [mem_filter, mem_univ, true_and, eq_iff_iff] at this
    rw [← ih x]
    cases h1 : (E.config (t + 1) x).ld <;> cases h2 : (E.config t x).ld <;> simp_all

lemma oc_leader_unique (hE : E.OrderedFair) {T : ℕ}
    (hT : ∀ t ≥ T, ∀ x, (E.config t x).ld = (E.config T x).ld) {a b : A}
    (ha : (E.config T a).ld = true) (hb : (E.config T b).ld = true)
    (hab : (E.config T a).ic = (E.config T b).ic) : a = b := by
  by_contra hne
  obtain ⟨s, hs, hsched⟩ := hE a b hne T
  have h1 := oc_init E s
  rw [hsched] at h1
  have := congrArg OCState.ld h1
  rw [(ocδ_fst_ic_ld _ _).2, hT (s + 1) (by omega), hT s hs, oc_ic_eq E s a, oc_ic_eq E s b,
    ← oc_ic_eq E T a, ← oc_ic_eq E T b, hab, hT s hs b, ha, hb] at this
  simp at this

end Exec

/-! ### Potentials for the ordering states -/

/-- Potential of a leader, given the (eventually constant) set `S` of labels used by stable
leaders and a label `h ∉ S`. -/
def phiL (S : Finset (Fin k)) (h : Fin k) (s : OCState Col k) : ℕ :=
  if s.os = .U then 2 * dist s.bra h + 2 else if s.bra ∈ S then 2 * dist s.bra h + 1 else 2 * k + 2

lemma dist_lt (d h : Fin k) : dist d h < k := Nat.mod_lt _ (by have := d.isLt; omega)

/-- Potential of a non-leader whose leader has bra `Lb`. -/
def psiN (Lb : Fin k) (s : OCState Col k) : ℕ :=
  match s.os with
  | .U => if s.bra = Lb then 0 else 3
  | .CL => 1
  | .CLW => 2
  | .I => 4

section Main

variable (E : (ordCircles Col k).Execution A)

/-- **Lemma 8.11**: after leader election, the ordering part `(os, bra)` of every agent changes
only finitely often (in every execution, fair or not). -/
lemma oc_ord_stabilizes {T1 : ℕ} {lead : A → Prop} [DecidablePred lead] {input : A → Col}
    (ℓ : A → A)
    (hld : ∀ t ≥ T1, ∀ x, (E.config t x).ld = true ↔ lead x)
    (hinv : ∀ t x, Inv (E.config t x)) (hic : ∀ t x, (E.config t x).ic = input x)
    (hℓc : ∀ x, input (ℓ x) = input x) (hℓl : ∀ x, lead (ℓ x))
    (huniq : ∀ a b, lead a → lead b → input a = input b → a = b)
    (hLcard : (univ.filter lead).card ≤ k) :
    ∃ T ≥ T1, ∀ t ≥ T, ∀ x, (E.config (t + 1) x).os = (E.config t x).os ∧
      (E.config (t + 1) x).bra = (E.config t x).bra := by
  -- leader bits after `T1`
  have hldf : ∀ t ≥ T1, ∀ x, ¬ lead x → (E.config t x).ld = false := fun t ht x hx => by
    cases h : (E.config t x).ld
    · rfl
    · exact absurd ((hld t ht x).1 h) hx
  -- the description of a change of a leader's ordering part
  have hlchg : ∀ t ≥ T1, ∀ x, lead x → ((E.config (t + 1) x).os ≠ (E.config t x).os ∨
      (E.config (t + 1) x).bra ≠ (E.config t x).bra) →
      x = (E.sched t).1 ∧
      (((E.config (t + 1) x).os = .I ∧ (E.config (t + 1) x).bra = (E.config t x).bra ∧
        (E.config t x).os = .U ∧ lead (E.sched t).2 ∧ (E.config t (E.sched t).2).os = .U ∧
        (E.config t (E.sched t).2).bra = (E.config t x).bra ∧ (E.sched t).2 ≠ x) ∨
      ((E.config (t + 1) x).os = .U ∧ (E.config (t + 1) x).bra = cyc (E.config t x).bra ∧
        ((E.config t x).os = .I ∨ ((E.config t x).os = .U ∧ lead (E.sched t).2 ∧
          (E.config t (E.sched t).2).os = .U ∧
          (E.config t (E.sched t).2).bra = (E.config t x).bra ∧ (E.sched t).2 ≠ x)))) := by
    intro t ht x hx hchg
    have hxa : x = (E.sched t).1 := by
      by_contra h
      have := oc_frame E h
      exact hchg.elim (fun e => e this.2.2.1) (fun e => e this.2.2.2)
    subst hxa
    refine ⟨rfl, ?_⟩
    have hl := (hld t ht _).2 hx
    have hr : (ocδ (E.config t (E.sched t).1) (E.config t (E.sched t).2)).1.ld = true := by
      rw [← oc_init]; exact (hld (t + 1) (by omega) _).2 hx
    have hb : (E.sched t).2 ≠ (E.sched t).1 := Ne.symm (E.sched_ne t)
    rw [oc_init] at hchg ⊢
    rcases ocδ_leader (hinv t _) (hinv t _) hl hr with h | h | h
    · exact absurd h (by tauto)
    · exact Or.inl ⟨h.1, h.2.1, h.2.2.1, (hld t ht _).1 h.2.2.2.2.1, h.2.2.2.2.2.1,
        h.2.2.2.2.2.2, hb⟩
    · refine Or.inr ⟨h.1, h.2.1, ?_⟩
      rcases h.2.2 with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h'.1, (hld t ht _).1 h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2, hb⟩
  -- Phase 2: the set of labels of stable leaders only grows
  set Sset : ℕ → Finset (Fin k) := fun t =>
    (univ.filter fun x => lead x ∧ (E.config t x).os = .U).image fun x => (E.config t x).bra
    with hSset
  have hSmono : ∀ t ≥ T1, Sset t ⊆ Sset (t + 1) := by
    intro t ht l hl
    simp only [hSset, mem_image, mem_filter, mem_univ, true_and] at hl ⊢
    obtain ⟨x, ⟨hx, hU⟩, rfl⟩ := hl
    by_cases hc : (E.config (t + 1) x).os ≠ (E.config t x).os ∨
        (E.config (t + 1) x).bra ≠ (E.config t x).bra
    · obtain ⟨hxa, h⟩ := hlchg t ht x hx hc
      have hfb := oc_frame E (Ne.symm (E.sched_ne t))
      rcases h with h | h
      · exact ⟨(E.sched t).2, ⟨h.2.2.2.1, by rw [hfb.2.2.1]; exact h.2.2.2.2.1⟩,
          by rw [hfb.2.2.2]; exact h.2.2.2.2.2.1⟩
      · rcases h.2.2 with h' | h'
        · rw [hU] at h'; exact absurd h' (by simp)
        · exact ⟨(E.sched t).2, ⟨h'.2.1, by rw [hfb.2.2.1]; exact h'.2.2.1⟩,
            by rw [hfb.2.2.2]; exact h'.2.2.2.1⟩
    · push Not at hc
      exact ⟨x, ⟨hx, by rw [hc.1]; exact hU⟩, hc.2⟩
  obtain ⟨T2, hT2le, hT2⟩ := eventually_const_of_monotone (fun t => (Sset t).card) k T1
    (fun t => (card_le_univ _).trans (by simp)) (fun t ht => card_le_card (hSmono t ht))
  have hS : ∀ t ≥ T2, Sset t = Sset T2 := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih =>
      rw [← ih]; symm
      exact eq_of_subset_of_card_le (hSmono t (by omega))
        (by have := hT2 t ht; have := hT2 (t + 1) (by omega); omega)
  have hmemS : ∀ t ≥ T2, ∀ x, lead x → (E.config t x).os = .U → (E.config t x).bra ∈ Sset T2 :=
    fun t ht x hx hU => by
      rw [← hS t ht]
      simp only [hSset, mem_image, mem_filter, mem_univ, true_and]
      exact ⟨x, ⟨hx, hU⟩, rfl⟩
  -- Phase 3: leaders' ordering parts eventually never change
  obtain ⟨T3, hT3le, hT3⟩ : ∃ T3 ≥ T2, ∀ t ≥ T3, ∀ x, lead x →
      (E.config (t + 1) x).os = (E.config t x).os ∧
      (E.config (t + 1) x).bra = (E.config t x).bra := by
    by_cases hfull : ∃ h, h ∉ Sset T2
    · obtain ⟨h, hh⟩ := hfull
      set L := univ.filter lead
      have hstep : ∀ t ≥ T2, ∀ x ∈ L, phiL (Sset T2) h (E.config (t + 1) x) ≤
          phiL (Sset T2) h (E.config t x) ∧
          (((E.config (t + 1) x).os ≠ (E.config t x).os ∨
            (E.config (t + 1) x).bra ≠ (E.config t x).bra) →
          phiL (Sset T2) h (E.config (t + 1) x) < phiL (Sset T2) h (E.config t x)) := by
        intro t ht x hxL
        have hx : lead x := by simpa [L] using hxL
        by_cases hc : (E.config (t + 1) x).os ≠ (E.config t x).os ∨
            (E.config (t + 1) x).bra ≠ (E.config t x).bra
        · suffices phiL (Sset T2) h (E.config (t + 1) x) < phiL (Sset T2) h (E.config t x) from
            ⟨this.le, fun _ => this⟩
          obtain ⟨-, hcase⟩ := hlchg t (by omega) x hx hc
          rcases hcase with hc' | hc'
          · have hm := hmemS t ht x hx hc'.2.2.1
            have hne : (E.config t x).bra ≠ h := fun e => hh (e ▸ hm)
            unfold phiL
            rw [ite_eq_right (by rw [hc'.1]; simp), hc'.2.1, ite_eq_left hm,
              ite_eq_left hc'.2.2.1]
            omega
          · have hdl := dist_lt (cyc (E.config t x).bra) h
            unfold phiL
            rw [ite_eq_left hc'.1, hc'.2.1]
            rcases hc'.2.2 with hI | hU
            · rw [ite_eq_right (by rw [hI]; simp)]
              split_ifs with hm
              · have hne : (E.config t x).bra ≠ h := fun e => hh (e ▸ hm)
                have := dist_cyc hne
                omega
              · omega
            · have hm := hmemS t ht x hx hU.1
              have hne : (E.config t x).bra ≠ h := fun e => hh (e ▸ hm)
              have := dist_cyc hne
              rw [ite_eq_left hU.1]
              omega
        · push Not at hc
          unfold phiL
          rw [hc.1, hc.2]
          exact ⟨le_rfl, fun h' => by tauto⟩
      obtain ⟨T3, hT3le, hT3⟩ := eventually_const_of_antitone
        (fun t => ∑ x ∈ L, phiL (Sset T2) h (E.config t x)) T2
        (fun t ht => Finset.sum_le_sum fun x hx => (hstep t ht x hx).1)
      refine ⟨T3, hT3le, fun t ht x hx => ?_⟩
      by_contra hne
      have hc : (E.config (t + 1) x).os ≠ (E.config t x).os ∨
          (E.config (t + 1) x).bra ≠ (E.config t x).bra := by tauto
      have hlt := Finset.sum_lt_sum (fun y hy => (hstep t (by omega) y hy).1)
        ⟨x, by simpa [L] using hx, (hstep t (by omega) x (by simpa [L] using hx)).2 hc⟩
      have := hT3 t ht; have := hT3 (t + 1) (by omega); omega
    · -- all labels are used by stable leaders: no conflict can arise
      push Not at hfull
      refine ⟨T2, le_rfl, fun t ht x hx => ?_⟩
      by_contra hne
      have hc : (E.config (t + 1) x).os ≠ (E.config t x).os ∨
          (E.config (t + 1) x).bra ≠ (E.config t x).bra := by tauto
      have hSt : Sset t = univ := by rw [hS t ht]; exact eq_univ_of_forall hfull
      set LU := univ.filter fun x => lead x ∧ (E.config t x).os = .U
      have hLU : LU ⊆ univ.filter lead := fun y hy => by simp [LU] at hy ⊢; exact hy.1
      have hcard : (LU.image fun x => (E.config t x).bra).card = k := by
        have : (LU.image fun x => (E.config t x).bra) = Sset t := rfl
        rw [this, hSt]; simp
      have hcLU : LU.card = k := le_antisymm ((card_le_card hLU).trans hLcard)
        (hcard ▸ card_image_le)
      have hLUeq : LU = univ.filter lead := eq_of_subset_of_card_le hLU (by omega)
      have hinj : Set.InjOn (fun x => (E.config t x).bra) LU :=
        Finset.card_image_iff.1 (by rw [hcard, hcLU])
      have hallU : ∀ y, lead y → (E.config t y).os = .U := fun y hy => by
        have : y ∈ LU := by rw [hLUeq]; simpa using hy
        simp [LU] at this; exact this.2
      obtain ⟨-, hcase⟩ := hlchg t (by omega) x hx hc
      have hxLU : x ∈ LU := by simp [LU]; exact ⟨hx, hallU x hx⟩
      rcases hcase with hc' | hc'
      · exact hc'.2.2.2.2.2.2 (hinj (by simp [LU]; exact ⟨hc'.2.2.2.1, hc'.2.2.2.2.1⟩) hxLU
          hc'.2.2.2.2.2.1)
      · rcases hc'.2.2 with hI | hU
        · rw [hallU x hx] at hI; exact absurd hI (by simp)
        · exact hU.2.2.2.2 (hinj (by simp [LU]; exact ⟨hU.2.1, hU.2.2.1⟩) hxLU hU.2.2.2.1)
  have hT3' : ∀ t ≥ T3, ∀ x, lead x → (E.config t x).bra = (E.config T3 x).bra := by
    intro t ht x hx
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [(hT3 t ht x hx).2, ih]
  -- Phase 4: non-leaders' ordering parts eventually never change
  set N := univ.filter fun x => ¬ lead x
  have hstepN : ∀ t ≥ T3, ∀ x ∈ N, psiN (E.config T3 (ℓ x)).bra (E.config (t + 1) x) ≤
      psiN (E.config T3 (ℓ x)).bra (E.config t x) ∧
      (((E.config (t + 1) x).os ≠ (E.config t x).os ∨
        (E.config (t + 1) x).bra ≠ (E.config t x).bra) →
      psiN (E.config T3 (ℓ x)).bra (E.config (t + 1) x) <
        psiN (E.config T3 (ℓ x)).bra (E.config t x)) := by
    intro t ht x hxN
    have hx : ¬ lead x := by simpa [N] using hxN
    by_cases hc : (E.config (t + 1) x).os ≠ (E.config t x).os ∨
        (E.config (t + 1) x).bra ≠ (E.config t x).bra
    · suffices psiN (E.config T3 (ℓ x)).bra (E.config (t + 1) x) <
          psiN (E.config T3 (ℓ x)).bra (E.config t x) from ⟨this.le, fun _ => this⟩
      have hxa : x = (E.sched t).1 := by
        by_contra h
        have := oc_frame E h
        exact hc.elim (fun e => e this.2.2.1) (fun e => e this.2.2.2)
      subst hxa
      have hl := hldf t (by omega) _ hx
      -- the responder, if it is a leader of the same color, is `ℓ x`
      have hleader : (E.config t (E.sched t).1).ic = (E.config t (E.sched t).2).ic →
          (E.config t (E.sched t).2).ld = true →
          (E.config t (E.sched t).2).bra = (E.config T3 (ℓ (E.sched t).1)).bra := by
        intro h1 h2
        have hq := (hld t (by omega) _).1 h2
        have : (E.sched t).2 = ℓ (E.sched t).1 :=
          huniq _ _ hq (hℓl _) (by rw [hℓc, ← hic t, ← hic t, h1])
        rw [this]; exact hT3' t ht _ (hℓl _)
      rw [oc_init] at hc ⊢
      rcases ocδ_nonleader (hinv t _) (hinv t _) hl with h | h | h | h | h
      · exact absurd h (by tauto)
      · have hLb := hleader h.2.2.1 h.2.2.2.1
        have hne : (E.config t (E.sched t).1).bra ≠ (E.config T3 (ℓ (E.sched t).1)).bra := by
          rw [← hLb]; exact h.2.2.2.2.1
        unfold psiN
        rw [h.1]
        cases ho : (E.config t (E.sched t).1).os
        · simp [ite_eq_right hne]
        · simp
        · exact absurd ho h.2.2.2.2.2
        · exfalso; rw [h.1, h.2.1, ho] at hc; simp at hc
      · unfold psiN
        rw [h.1]
        rcases h.2.2 with h' | h'
        · rw [h']; simp
        · have hLb := hleader h'.1 h'.2.1
          have hne : (E.config t (E.sched t).1).bra ≠ (E.config T3 (ℓ (E.sched t).1)).bra := by
            rw [← hLb]; exact h'.2.2.1
          cases ho : (E.config t (E.sched t).1).os
          · simp [ite_eq_right hne]
          · simp
          · exact absurd ho h'.2.2.2
          · simp
      · have hLb := hleader h.2.2.2.1 h.2.2.2.2
        unfold psiN
        rw [h.1, h.2.2.1, h.2.1, hLb]
        simp
      · unfold psiN
        rw [h.1, h.2.2]
        split_ifs <;> simp
    · push Not at hc
      unfold psiN
      rw [hc.1, hc.2]
      exact ⟨le_rfl, fun h' => by tauto⟩
  obtain ⟨T4, hT4le, hT4⟩ := eventually_const_of_antitone
    (fun t => ∑ x ∈ N, psiN (E.config T3 (ℓ x)).bra (E.config t x)) T3
    (fun t ht => Finset.sum_le_sum fun x hx => (hstepN t ht x hx).1)
  refine ⟨T4, by omega, fun t ht x => ?_⟩
  by_cases hx : lead x
  · exact hT3 t (by omega) x hx
  · by_contra hne
    have hc : (E.config (t + 1) x).os ≠ (E.config t x).os ∨
        (E.config (t + 1) x).bra ≠ (E.config t x).bra := by tauto
    have hlt := Finset.sum_lt_sum (fun y hy => (hstepN t (by omega) y hy).1)
      ⟨x, by simpa [N] using hx, (hstepN t (by omega) x (by simpa [N] using hx)).2 hc⟩
    have := hT4 t ht; have := hT4 (t + 1) (by omega); omega

/-- **Lemma 8.9** (Invariant 3.3): in every reachable configuration, every label occurs as
often as a bra as it occurs as a ket. -/
lemma oc_balanced (hinv : ∀ t x, Inv (E.config t x))
    (h0 : ∀ x, (E.config 0 x).bra = (E.config 0 x).ket) (t : ℕ) (l : Fin k) :
    (univ.filter fun x => (E.config t x).bra = l).card =
      (univ.filter fun x => (E.config t x).ket = l).card := by
  simp only [Finset.card_filter]
  induction t with
  | zero => simp [h0]
  | succ t ih =>
    rcases hs : E.sched t with ⟨a, b⟩
    have hab : a ≠ b := by have := E.sched_ne t; rw [hs] at this; exact this
    have hi := oc_init E t
    have hr := oc_resp E t
    rw [hs] at hi hr
    have hrest : ∀ f : OCState Col k → Fin k,
        ∑ x ∈ (univ.erase a).erase b, (if f (E.config (t + 1) x) = l then 1 else 0) =
        ∑ x ∈ (univ.erase a).erase b, (if f (E.config t x) = l then 1 else 0) := by
      intro f
      apply Finset.sum_congr rfl
      intro x hx
      simp only [mem_erase] at hx
      rw [oc_other E (by rw [hs]; exact hx.2.1) (by rw [hs]; exact hx.1)]
    rw [sum_split (fun x => if (E.config t x).bra = l then 1 else 0) hab,
      sum_split (fun x => if (E.config t x).ket = l then 1 else 0) hab] at ih
    rw [sum_split (fun x => if (E.config (t + 1) x).bra = l then 1 else 0) hab,
      sum_split (fun x => if (E.config (t + 1) x).ket = l then 1 else 0) hab,
      hrest OCState.bra, hrest OCState.ket]
    have hb := lbal_ocδ (q := E.config t b) (hinv t a) l
    rw [← hi, ← hr] at hb
    simp only [ind] at hb
    omega

/-- Outputs are always input colors. -/
lemma oc_out_mem {input : A → Col} (hic : ∀ t x, (E.config t x).ic = input x)
    (h0 : ∀ x, ∃ y, (E.config 0 x).out = input y) (t : ℕ) (x : A) :
    ∃ y, (E.config t x).out = input y := by
  induction t generalizing x with
  | zero => exact h0 x
  | succ t ih =>
    have ho := ocδ_out (E.config t (E.sched t).1) (E.config t (E.sched t).2)
    by_cases hxa : x = (E.sched t).1
    · subst hxa; rw [oc_init]
      rcases ho.1 with h | h | h
      · rw [h]; exact ih _
      · exact ⟨_, h.trans (hic t _)⟩
      · exact ⟨_, h.trans (hic t _)⟩
    · by_cases hxb : x = (E.sched t).2
      · subst hxb; rw [oc_resp]
        rcases ho.2 with h | h | h
        · rw [h]; exact ih _
        · exact ⟨_, h.trans (hic t _)⟩
        · exact ⟨_, h.trans (hic t _)⟩
      · rw [oc_other E hxa hxb]; exact ih x

/-- The braket configuration. -/
def brk (C : Config A (OCState Col k)) : Config A (Braket k) := fun x => ((C x).bra, (C x).ket)

/-- A quiet interaction (step (5) only) is an interaction of the braket protocol of Circles. -/
lemma brk_step {t : ℕ} (hq : ocδ (E.config t (E.sched t).1) (E.config t (E.sched t).2) =
      step5 (E.config t (E.sched t).1) (E.config t (E.sched t).2)) :
    brk (E.config (t + 1)) = (circlesCore k).interact (brk (E.config t)) (E.sched t).1
      (E.sched t).2 := by
  funext x
  have h5 := step5_kets (E.config t (E.sched t).1) (E.config t (E.sched t).2)
  by_cases hxa : x = (E.sched t).1
  · subst hxa
    rw [interact_self_left]
    simp only [brk, circlesCore]
    rw [oc_init, hq]; exact h5.1
  · by_cases hxb : x = (E.sched t).2
    · subst hxb
      rw [interact_self_right _ _ (E.sched_ne t)]
      simp only [brk, circlesCore]
      rw [oc_resp, hq]; exact h5.2
    · rw [interact_other _ _ hxa hxb]
      simp only [brk]
      rw [oc_other E hxa hxb]

/-- **Lemmas 8.10–8.13**: under weak fairness for ordered pairs, eventually the leader bits,
bras and kets never change, all agents are in ordering state `U`, two agents have the same bra
iff they have the same color, every interaction is a Circles interaction, and the braket
configuration is stable. -/
theorem oc_converge (input : A → Col) (hk : 0 < k) (hcol : (colors input).card ≤ k)
    (h0 : E.config 0 = ocInit input hk) (hE : E.OrderedFair) :
    ∃ T, (∀ t ≥ T, ∀ x, (E.config t x).ld = (E.config T x).ld ∧ (E.config t x).os = .U ∧
        (E.config t x).bra = (E.config T x).bra ∧ (E.config t x).ket = (E.config T x).ket) ∧
      (∀ a b, (E.config T a).bra = (E.config T b).bra ↔ input a = input b) ∧
      (∀ t ≥ T, ocδ (E.config t (E.sched t).1) (E.config t (E.sched t).2) =
        step5 (E.config t (E.sched t).1) (E.config t (E.sched t).2)) ∧
      Stable (brk (E.config T)) := by
  classical
  have hic : ∀ t x, (E.config t x).ic = input x := fun t x => by rw [oc_ic_eq, h0]; rfl
  have hinv0 : ∀ x, Inv (E.config 0 x) := fun x => by
    rw [h0]; exact ⟨fun _ => rfl, fun _ => Or.inl rfl⟩
  have hinv := oc_inv E hinv0
  have hld0 : ∀ x, (E.config 0 x).ld = true := fun x => by rw [h0]; rfl
  -- leader election
  obtain ⟨T1, hT1⟩ := oc_leaders_eventually_const E
  set lead : A → Prop := fun x => (E.config T1 x).ld = true with hlead_def
  have hld : ∀ t ≥ T1, ∀ x, (E.config t x).ld = true ↔ lead x := fun t ht x => by
    rw [hT1 t ht]
  have hlead : ∀ x, ∃ y, input y = input x ∧ lead y := fun x => by
    obtain ⟨y, h1, h2⟩ := oc_exists_leader E hld0 T1 x
    exact ⟨y, by rwa [hic, hic] at h1, h2⟩
  choose ℓ hℓc hℓl using hlead
  have huniq : ∀ a b, lead a → lead b → input a = input b → a = b :=
    fun a b ha hb hab => oc_leader_unique E hE hT1 ha hb (by rw [hic, hic, hab])
  have hLcard : (univ.filter lead).card ≤ k := by
    refine le_trans ?_ hcol
    rw [colors, ← Finset.card_image_of_injOn (f := input) (s := univ.filter lead)]
    · exact card_le_card (image_subset_image (subset_univ _))
    · intro a ha b hb hab
      exact huniq a b (by simpa using ha) (by simpa using hb) hab
  -- the ordering parts stabilize
  obtain ⟨T4, hT4le, hT4⟩ := oc_ord_stabilizes E ℓ hld hinv hic hℓc hℓl huniq hLcard
  have hconst : ∀ t ≥ T4, ∀ x, (E.config t x).os = (E.config T4 x).os ∧
      (E.config t x).bra = (E.config T4 x).bra := by
    intro t ht x
    induction t, ht using Nat.le_induction with
    | base => exact ⟨rfl, rfl⟩
    | succ t ht ih => rw [(hT4 t ht x).1, (hT4 t ht x).2]; exact ih
  -- no pending agents
  have hnoCL : ∀ x, (E.config T4 x).os ≠ .CL := by
    intro x hx
    have hxl : ¬ lead x := fun h => by
      rcases (hinv T4 x).2 ((hld T4 hT4le x).2 h) with e | e <;> rw [hx] at e <;> simp at e
    have hne : x ≠ ℓ x := fun e => hxl (e ▸ hℓl x)
    obtain ⟨s, hs, hsched⟩ := hE x (ℓ x) hne T4
    have h1 := oc_init E s
    rw [hsched] at h1
    have := ocδ_pending (hinv s x) (hinv s (ℓ x)) (by rw [(hconst s hs x).1]; exact hx)
      (by rw [hic, hic, hℓc]) ((hld s (by omega) _).2 (hℓl x))
    rw [← h1, (hconst (s + 1) (by omega) x).1, hx] at this
    simp at this
  have hnoCL' : ∀ t ≥ T4, ∀ x, (E.config t x).os ≠ .CL := fun t ht x => by
    rw [(hconst t ht x).1]; exact hnoCL x
  have hk2 : 2 ≤ k ∨ ∀ a b, input a = input b := by
    by_cases h : ∃ a b, input a ≠ input b
    · obtain ⟨a, b, hab⟩ := h
      left
      refine le_trans ?_ hcol
      have : ({input a, input b} : Finset Col) ⊆ colors input := by
        intro c hc; simp only [mem_insert, mem_singleton] at hc
        rcases hc with rfl | rfl <;> simp [colors]
      have h2 := card_le_card this
      rwa [card_pair hab] at h2
    · push Not at h; exact Or.inr h
  -- after `T4`, every interaction is a Circles interaction
  have hquiet : ∀ t ≥ T4, ocδ (E.config t (E.sched t).1) (E.config t (E.sched t).2) =
      step5 (E.config t (E.sched t).1) (E.config t (E.sched t).2) := by
    intro t ht
    apply ocδ_quiet (hinv t _) (hinv t _)
      (hk2.elim Or.inl (fun h => Or.inr (by rw [hic, hic]; exact h _ _)))
      (hnoCL' t ht _) (hnoCL' t ht _)
    · rw [← oc_init]; exact (hT4 t ht _).1
    · rw [← oc_init]; exact (hT4 t ht _).2
    · rw [← oc_init, hT1 (t + 1) (by omega), hT1 t (by omega)]
  -- the braket part is an execution of Circles from `T4` on
  let Ec : (circlesCore k).Execution A :=
    { config := fun t => brk (E.config (T4 + t))
      sched := fun t => E.sched (T4 + t)
      sched_ne := fun t => E.sched_ne (T4 + t)
      step := fun t => brk_step E (hquiet (T4 + t) (by omega)) }
  obtain ⟨T5', hT5'⟩ := eventually_const Ec
  have hfairc : Ec.WeaklyFair := fun a b hab T => by
    obtain ⟨t, ht, hs⟩ := hE a b hab (T4 + T)
    refine ⟨t - T4, by omega, Or.inl ?_⟩
    show E.sched (T4 + (t - T4)) = (a, b)
    rw [show T4 + (t - T4) = t by omega]; exact hs
  have hstab := stable_of_weaklyFair Ec hfairc hT5'
  set T5 := T4 + T5' with hT5
  have hbk : ∀ t ≥ T5, ∀ x, (E.config t x).bra = (E.config T5 x).bra ∧
      (E.config t x).ket = (E.config T5 x).ket := by
    intro t ht x
    have := congrFun (hT5' (t - T4) (by omega)) x
    simp only [Ec, brk] at this
    rw [show T4 + (t - T4) = t by omega] at this
    exact Prod.ext_iff.1 this
  -- all agents are stable
  have hother : ∀ x, ∃ y, y ≠ x := fun x => by
    by_cases h : x = (E.sched 0).1
    · exact ⟨(E.sched 0).2, by rw [h]; exact Ne.symm (E.sched_ne 0)⟩
    · exact ⟨(E.sched 0).1, Ne.symm h⟩
  have hU : ∀ x, (E.config T4 x).os = .U := by
    intro x
    by_contra hne
    have hu : (E.config T4 x).os.unstable := by
      have h1 := hnoCL x
      revert hne h1
      cases (E.config T4 x).os <;> simp [OS.unstable]
    obtain ⟨y, hyx, hy⟩ : ∃ y, y ≠ x ∧ ((E.config T5 x).bra = (E.config T5 x).ket ∨
        (E.config T5 y).ket = (E.config T5 x).bra) := by
      by_cases hc : (E.config T5 x).bra = (E.config T5 x).ket
      · obtain ⟨y, hy⟩ := hother x; exact ⟨y, hy, Or.inl hc⟩
      · have hbal := oc_balanced E hinv (fun x => by rw [h0]; rfl) T5 (E.config T5 x).bra
        have : 0 < (univ.filter fun z => (E.config T5 z).ket = (E.config T5 x).bra).card := by
          rw [← hbal]; exact card_pos.2 ⟨x, by simp⟩
        obtain ⟨y, hy⟩ := card_pos.1 this
        simp only [mem_filter, mem_univ, true_and] at hy
        exact ⟨y, fun e => hc (by rw [e] at hy; exact hy.symm), Or.inr hy⟩
    obtain ⟨s, hs, hsched⟩ := hE x y (Ne.symm hyx) T5
    have h1 := oc_init E s
    rw [hsched] at h1
    have := ocδ_unstable (hinv s x) (hinv s y) (by rw [(hconst s (by omega) x).1]; exact hu)
      (hnoCL' s (by omega) y)
      (by rw [(hbk s hs x).1, (hbk s hs x).2, (hbk s hs y).2]; exact hy)
    rw [← h1, (hconst (s + 1) (by omega) x).1] at this
    rcases this with h | h
    · exact hne h
    · exact hnoCL x h
  have hUt : ∀ t ≥ T4, ∀ x, (E.config t x).os = .U := fun t ht x => by
    rw [(hconst t ht x).1]; exact hU x
  -- valid ordering
  have hdist : ∀ a b, lead a → lead b → input a ≠ input b →
      (E.config T5 a).bra ≠ (E.config T5 b).bra := by
    intro a b ha hb hab hd
    have hab' : a ≠ b := fun e => hab (e ▸ rfl)
    obtain ⟨s, hs, hsched⟩ := hE a b hab' T5
    have h1 := oc_init E s
    rw [hsched] at h1
    have hk2' : 2 ≤ k := hk2.resolve_right (fun h => hab (h a b))
    have := ocδ_conflict (hinv s a) (hinv s b) hk2' ((hld s (by omega) a).2 ha)
      ((hld s (by omega) b).2 hb) (by rw [hic, hic]; exact hab) (hUt s (by omega) a)
      (hUt s (by omega) b) (by rw [(hbk s hs a).1, (hbk s hs b).1]; exact hd)
    rw [← h1, (hconst (s + 1) (by omega) a).1, (hconst s (by omega) a).1,
      (hconst (s + 1) (by omega) a).2, (hconst s (by omega) a).2] at this
    simp at this
  have hcopy : ∀ x, (E.config T5 x).bra = (E.config T5 (ℓ x)).bra := by
    intro x
    by_contra hne
    have hxℓ : x ≠ ℓ x := fun e => hne (by rw [← e])
    obtain ⟨s, hs, hsched⟩ := hE x (ℓ x) hxℓ T5
    have h1 := oc_init E s
    rw [hsched] at h1
    have := ocδ_copy (hinv s x) (hinv s (ℓ x)) (by rw [hic, hic, hℓc])
      ((hld s (by omega) _).2 (hℓl x)) (by rw [(hbk s hs _).1, (hbk s hs _).1]; exact hne)
      (hUt s (by omega) x) (hnoCL' s (by omega) _)
    rw [← h1, hUt (s + 1) (by omega) x] at this
    rcases this with h | h <;> simp at h
  refine ⟨T5, fun t ht x => ⟨by rw [hT1 t (by omega), hT1 T5 (by omega)], hUt t (by omega) x,
    (hbk t ht x).1, (hbk t ht x).2⟩, fun a b => ?_, fun t ht => hquiet t (by omega), hstab⟩
  rw [hcopy a, hcopy b]
  constructor
  · intro h; by_contra hne
    exact hdist (ℓ a) (ℓ b) (hℓl a) (hℓl b) (by rw [hℓc, hℓc]; exact hne) h
  · intro h; rw [huniq (ℓ a) (ℓ b) (hℓl a) (hℓl b) (by rw [hℓc, hℓc, h])]

lemma outRule_out (p q : OCState Col k) :
    (outRule p q).1.out = (if p.bra = p.ket ∧ q.bra ≠ q.ket then p.ic
      else if q.bra = q.ket ∧ p.bra ≠ p.ket then q.ic else p.out) ∧
    (outRule p q).2.out = (if p.bra = p.ket ∧ q.bra ≠ q.ket then p.ic
      else if q.bra = q.ket ∧ p.bra ≠ p.ket then q.ic else q.out) := by
  unfold outRule; split_ifs <;> simp

/-- Number of agents with input color `c`. -/
def cnt (input : A → Col) (c : Col) : ℕ := (univ.filter fun a => input a = c).card

/-- `μ` is the unique color in relative majority. -/
def IsMajorityC (input : A → Col) (μ : Col) : Prop :=
  0 < cnt input μ ∧ ∀ c, c ≠ μ → cnt input c < cnt input μ

/-- **Theorem 5.2** (Ord-Circles solves relative majority in the unordered setting), for weak
fairness with ordered pairs: if at most `k` colors occur and `μ` is the unique color in relative
majority, then from some time on all agents output `μ`. -/
theorem ordCircles_correct (input : A → Col) (hk : 0 < k) (hcol : (colors input).card ≤ k)
    (h0 : E.config 0 = ocInit input hk) (hE : E.OrderedFair) (μ : Col)
    (hμ : IsMajorityC input μ) :
    ∃ T, ∀ t ≥ T, ∀ a, (E.config t a).out = μ := by
  classical
  obtain ⟨T, hT, hvalid, hquiet, hstab⟩ := oc_converge E input hk hcol h0 hE
  have hic : ∀ t x, (E.config t x).ic = input x := fun t x => by rw [oc_ic_eq, h0]; rfl
  have hinv0 : ∀ x, Inv (E.config 0 x) := fun x => by
    rw [h0]; exact ⟨fun _ => rfl, fun _ => Or.inl rfl⟩
  have hinv := oc_inv E hinv0
  obtain ⟨m, hm⟩ : ∃ m, input m = μ := by
    obtain ⟨m, hm⟩ := card_pos.1 hμ.1
    exact ⟨m, by simpa using hm⟩
  -- the stable braket configuration is `⋃ f(G_p)` for the label counts
  set x' : Fin k → ℕ := fun l => (univ.filter fun a => (E.config T a).bra = l).card with hx'
  have hbal := oc_balanced E hinv (fun x => by rw [h0]; rfl) T
  have hCounts : Counts (brakets (brk (E.config T))) x' := by
    intro c
    simp only [brakets, brk, Multiset.map_map, Function.comp_def, Multiset.count_map]
    constructor
    · simp [x', Finset.card, Finset.filter_val, eq_comm]
    · rw [show x' c = _ from hbal c]; simp [Finset.card, Finset.filter_val, eq_comm]
  have hlay := eq_layers_of_stable x' _ hCounts hstab.mstable
  have hdiag : ∀ i, (∃ a, brk (E.config T) a = (i, i)) ↔
      0 < x' i ∧ ∀ c, c ≠ i → x' c < x' i := by
    intro i; rw [← diag_mem_layers_iff, ← hlay]; simp [brakets]
  -- the label of `μ` is the unique majority label
  have hxm : x' (E.config T m).bra = cnt input μ := by
    simp only [x', cnt]; congr 1; ext a; simp [hvalid, hm]
  have hlt : ∀ l, l ≠ (E.config T m).bra → x' l < cnt input μ := by
    intro l hl
    by_cases hz : x' l = 0
    · rw [hz]; exact hμ.1
    · obtain ⟨a, ha⟩ := card_pos.1 (Nat.pos_of_ne_zero hz)
      simp only [mem_filter, mem_univ, true_and] at ha
      have hne : input a ≠ μ := fun e => hl (by rw [← ha]; exact (hvalid a m).2 (by rw [e, hm]))
      have : x' l = cnt input (input a) := by
        simp only [x', cnt]; congr 1; ext b; simp only [mem_filter, mem_univ, true_and]
        rw [← ha]; exact hvalid b a
      rw [this]; exact hμ.2 _ hne
  have hdiagμ : ∀ y, (E.config T y).bra = (E.config T y).ket → input y = μ := by
    intro y hy
    have := (hdiag (E.config T y).bra).1 ⟨y, by simp [brk, hy]⟩
    by_contra hne
    have h1 := hlt _ (fun e => hne (by rw [← hm]; exact (hvalid y m).1 e))
    have h2 := this.2 _ (fun e => hne (by rw [← hm]; exact (hvalid y m).1 e.symm))
    rw [hxm] at h2; omega
  obtain ⟨d, hd⟩ := (hdiag (E.config T m).bra).2
    ⟨by rw [hxm]; exact hμ.1, fun c hc => by rw [hxm]; exact hlt c hc⟩
  have hdd : (E.config T d).bra = (E.config T d).ket := by
    simp only [brk, Prod.mk.injEq] at hd; rw [hd.1, hd.2]
  -- after `T`, interactions only update outputs by the output rule
  have hδ : ∀ t ≥ T, ocδ (E.config t (E.sched t).1) (E.config t (E.sched t).2) =
      outRule (E.config t (E.sched t).1) (E.config t (E.sched t).2) := by
    intro t ht
    rw [hquiet t ht]
    unfold step5
    have hs := hstab _ _ (E.sched_ne t)
    simp only [brk] at hs
    rw [(hT t ht _).2.2.1, (hT t ht _).2.2.2, (hT t ht (E.sched t).2).2.2.1,
      (hT t ht (E.sched t).2).2.2.2] at *
    rw [ite_eq_right hs]
  set dg : A → Prop := fun z => (E.config T z).bra = (E.config T z).ket with hdg
  have hdgt : ∀ t ≥ T, ∀ z, ((E.config t z).bra = (E.config t z).ket ↔ dg z) := fun t ht z => by
    rw [(hT t ht z).2.2.1, (hT t ht z).2.2.2]
  have hstep : ∀ t ≥ T, ∀ x, (E.config (t + 1) x).out = (E.config t x).out ∨
      (E.config (t + 1) x).out = μ := by
    intro t ht x
    have ho := outRule_out (E.config t (E.sched t).1) (E.config t (E.sched t).2)
    by_cases hxa : x = (E.sched t).1
    · subst hxa
      rw [oc_init, hδ t ht, ho.1]
      split_ifs with h1 h2
      · right; rw [hic]; exact hdiagμ _ ((hdgt t ht _).1 h1.1)
      · right; rw [hic]; exact hdiagμ _ ((hdgt t ht _).1 h2.1)
      · left; rfl
    · by_cases hxb : x = (E.sched t).2
      · subst hxb
        rw [oc_resp, hδ t ht, ho.2]
        split_ifs with h1 h2
        · right; rw [hic]; exact hdiagμ _ ((hdgt t ht _).1 h1.1)
        · right; rw [hic]; exact hdiagμ _ ((hdgt t ht _).1 h2.1)
        · left; rfl
      · left; rw [oc_other E hxa hxb]
  have hgain : ∀ t ≥ T, ∀ x y, E.sched t = (x, y) → ((dg x ∧ ¬ dg y) ∨ (¬ dg x ∧ dg y)) →
      (E.config (t + 1) x).out = μ := by
    intro t ht x y hs hxy
    have ho := (outRule_out (E.config t x) (E.config t y)).1
    have hi := oc_init E t
    rw [hs] at hi
    simp only at hi
    have hδ' := hδ t ht
    rw [hs] at hδ'
    simp only at hδ'
    rw [hi, hδ', ho]
    rcases hxy with h | h
    · rw [ite_eq_left ⟨(hdgt t ht x).2 h.1, fun e => h.2 ((hdgt t ht y).1 e)⟩, hic]
      exact hdiagμ x h.1
    · rw [ite_eq_right (fun e => h.1 ((hdgt t ht x).1 e.1)),
        ite_eq_left ⟨(hdgt t ht y).2 h.2, fun e => h.1 ((hdgt t ht x).1 e)⟩, hic]
      exact hdiagμ y h.2
  have hpersist : ∀ x, ∀ s ≥ T, (E.config s x).out = μ → ∀ t ≥ s, (E.config t x).out = μ := by
    intro x s hs hx t hst
    induction t, hst using Nat.le_induction with
    | base => exact hx
    | succ t hst ih => rcases hstep t (by omega) x with h | h <;> [rw [h, ih]; exact h]
  by_cases hall : ∀ y, dg y
  · -- all agents diagonal: all inputs are `μ`, and outputs are always input colors
    have hin : ∀ y, input y = μ := fun y => hdiagμ y (hall y)
    refine ⟨0, fun t _ a => ?_⟩
    obtain ⟨y, hy⟩ := oc_out_mem E hic (fun x => ⟨x, by rw [h0]; rfl⟩) t a
    rw [hy, hin]
  · push Not at hall
    obtain ⟨nd, hnd⟩ := hall
    have hev : ∀ x, ∃ s ≥ T, (E.config s x).out = μ := by
      intro x
      by_cases hx : dg x
      · have hne : x ≠ nd := fun e => hnd (e ▸ hx)
        obtain ⟨t, ht, hs⟩ := hE x nd hne T
        exact ⟨t + 1, by omega, hgain t ht x nd hs (Or.inl ⟨hx, hnd⟩)⟩
      · have hdg : dg d := hdd
        have hne : x ≠ d := fun e => hx (e ▸ hdg)
        obtain ⟨t, ht, hs⟩ := hE x d hne T
        exact ⟨t + 1, by omega, hgain t ht x d hs (Or.inr ⟨hx, hdg⟩)⟩
    choose s hsT hs using hev
    refine ⟨univ.sup s, fun t ht a => hpersist a (s a) (hsT a) (hs a) t
      (le_trans (Finset.le_sup (mem_univ a)) ht)⟩

end Main

/-! ### Lemma 8.13 -/

/-- **Lemma 8.13** (the ordering converges inside Ord-Circles), for weak fairness with ordered
pairs: eventually all agents are in ordering state `U`, bras never change again, and two agents
have the same bra iff they have the same initial color. -/
theorem ordCircles_ordering (input : A → Col) (hk : 0 < k) (hcol : (colors input).card ≤ k)
    (E : (ordCircles Col k).Execution A) (h0 : E.config 0 = ocInit input hk)
    (hE : E.OrderedFair) :
    ∃ T, ∀ t ≥ T, (∀ x, (E.config t x).os = .U ∧ (E.config t x).bra = (E.config T x).bra) ∧
      ∀ a b, (E.config t a).bra = (E.config t b).bra ↔ input a = input b := by
  obtain ⟨T, hT, hvalid, -, -⟩ := oc_converge E input hk hcol h0 hE
  refine ⟨T, fun t ht => ⟨fun x => ⟨(hT t ht x).2.1, (hT t ht x).2.2.1⟩, fun a b => ?_⟩⟩
  rw [(hT t ht a).2.2.1, (hT t ht b).2.2.1]; exact hvalid a b

/-! ### The symmetrized protocol under (unordered) weak fairness -/

/-- **Theorem 5.2 for the symmetrized protocol** (`Protocol.symm`: every interaction applies the
Ord-Circles transition with both role assignments): correct under weak fairness for unordered
pairs (`Execution.WeaklyFair`). -/
theorem ordCirclesSymm_correct (input : A → Col) (hk : 0 < k) (hcol : (colors input).card ≤ k)
    (E : (ordCircles Col k).symm.Execution A) (h0 : E.config 0 = ocInit input hk)
    (hE : E.WeaklyFair) (μ : Col) (hμ : IsMajorityC input μ) :
    ∃ T, ∀ t ≥ T, ∀ a, (E.config t a).out = μ :=
  Execution.eventually_of_unfold (p := fun (C : Config A (OCState Col k)) => ∀ a, (C a).out = μ)
    (ordCircles_correct E.unfold input hk hcol (by rw [E.unfold_zero, h0]) hE.unfold μ hμ)

/-! ### Counterexample under weak fairness for unordered pairs -/

/-- The counterexample schedule: `(1,2)` (agent 1 increments its bra and exchanges kets with
agent 2), `(0,1)` (agent 0 is demoted and becomes pending), then forever `(1,0), (0,2), (1,2)`. -/
def cexSched2 (t : ℕ) : Fin 3 × Fin 3 :=
  match t with
  | 0 => (1, 2)
  | 1 => (0, 1)
  | t + 2 => cexPairs ⟨t % 3, Nat.mod_lt _ (by norm_num)⟩

lemma cexSched2_ne (t : ℕ) : (cexSched2 t).1 ≠ (cexSched2 t).2 := by
  match t with
  | 0 => decide
  | 1 => decide
  | t + 2 =>
    simp only [cexSched2]
    generalize (⟨t % 3, _⟩ : Fin 3) = i
    revert i; decide

/-- The Ord-Circles counterexample execution (`k = 2`, colors `0, 0, 1`). -/
def cexExec2 : (ordCircles (Fin 2) 2).Execution (Fin 3) :=
  Execution.ofSchedRec _ (ocInit cexInput (by norm_num)) cexSched2 cexSched2_ne

/-- The configuration reached after two steps: agent 0 is pending (it waits to meet its leader
as the initiator), agent 1 (leader of color 0) has `⟨1|0⟩`, agent 2 (leader of color 1) has
`⟨0|1⟩` and outputs color 1. -/
def cexStuck2 : Config (Fin 3) (OCState (Fin 2) 2) :=
  ![⟨0, false, .CL, 0, 0, 0⟩, ⟨0, true, .U, 1, 0, 0⟩, ⟨1, true, .U, 0, 1, 1⟩]

lemma cexExec2_stuck (t : ℕ) : cexExec2.config (t + 2) = cexStuck2 := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show t + 1 + 2 = (t + 2) + 1 by omega, cexExec2.step, ih]
    simp only [cexExec2, Execution.ofSchedRec, cexSched2]
    generalize (⟨t % 3, _⟩ : Fin 3) = i
    revert i; decide

lemma cexSched2_fair (a b : Fin 3) (hab : a ≠ b) (T : ℕ) :
    ∃ t ≥ T, cexSched2 t = (a, b) ∨ cexSched2 t = (b, a) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, cexPairs i = (a, b) ∨ cexPairs i = (b, a) := by
    revert a b; decide
  refine ⟨3 * T + i.val + 2, by omega, ?_⟩
  simp only [cexSched2]
  have : (⟨(3 * T + i.val) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = i := by
    ext; simp only; omega
  rw [this]; exact hi

/-- **Theorem 5.2 fails under weak fairness for unordered pairs.** For `k = 2` and three agents
with colors `0, 0, 1` (color 0 is the unique majority), there is a weakly fair execution
(every unordered pair interacts infinitely often) of Ord-Circles that is constant from time 2 on,
and in which agent 2 outputs color 1 forever. -/
theorem ordCircles_not_weaklyFair :
    ∃ E : (ordCircles (Fin 2) 2).Execution (Fin 3),
      E.config 0 = ocInit cexInput (by norm_num) ∧ (colors cexInput).card ≤ 2 ∧
      IsMajorityC cexInput 0 ∧ E.WeaklyFair ∧
      ∀ t ≥ 2, E.config t = cexStuck2 ∧ (E.config t 2).out ≠ 0 := by
  refine ⟨cexExec2, rfl, (card_le_univ _).trans (by simp),
    by unfold IsMajorityC cnt; decide, fun a b hab T => cexSched2_fair a b hab T, fun t ht => ?_⟩
  obtain ⟨t, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  rw [cexExec2_stuck]
  exact ⟨rfl, by decide⟩

end RankingOpinions.Unordered
