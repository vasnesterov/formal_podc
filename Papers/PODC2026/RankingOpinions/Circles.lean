import Papers.PODC2026.RankingOpinions.Dynamics

/-!
# The Circles protocol and relative majority (Theorem 1.1)

Breitkopf, Dallot, El-Hayek, Schmid, *Ranking Opinions with Few States in Population Protocols*,
PODC 2026 (arXiv:2605.18707), Section 3.

States: a braket `⟨i|j⟩` and an output color `out` (`k³` states).
Input: color `i` ↦ `⟨i|i⟩`, `out = i`.
Transition: (1) exchange kets iff that strictly decreases the minimum weight;
(2) if exactly one of the two agents is of the form `⟨i|i⟩`, both set `out := i`.
-/

set_option linter.unusedSectionVars false

namespace RankingOpinions

open Finset Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

variable {k : ℕ}

/-- States of Circles: a braket and an output color. -/
abbrev CState (k : ℕ) := Braket k × Fin k

/-- The braket part of Circles has `k²` states. -/
theorem card_Braket : Fintype.card (Braket k) = k ^ 2 := by
  simp [Fintype.card_prod, pow_two]

/-- Circles has `k³` states. -/
theorem card_CState : Fintype.card (CState k) = k ^ 3 := by
  simp [Fintype.card_prod, pow_succ, mul_assoc]

/-- The transition function of Circles (rules (1) and (2), applied in sequence). -/
def circlesδ (p q : CState k) : CState k × CState k :=
  let e := (exch p.1 q.1).1
  let f := (exch p.1 q.1).2
  if e.1 = e.2 ∧ f.1 ≠ f.2 then ((e, e.1), (f, e.1))
  else if f.1 = f.2 ∧ e.1 ≠ e.2 then ((e, f.1), (f, f.1))
  else ((e, p.2), (f, q.2))

/-- The Circles protocol. -/
def circles (k : ℕ) : Protocol (CState k) := ⟨circlesδ⟩

/-- Projection of Circles onto its braket part. -/
def circlesToCore : (circles k).Hom (circlesCore k) where
  f := Prod.fst
  map_fst p q := by simp only [circles, circlesδ, circlesCore]; split_ifs <;> rfl
  map_snd p q := by simp only [circles, circlesδ, circlesCore]; split_ifs <;> rfl

/-- Output map: `out`. -/
def output (s : CState k) : Fin k := s.2

/-- The initial configuration for an input assignment. -/
def circlesInit {A : Type*} (input : A → Fin k) : Config A (CState k) :=
  fun a => ((input a, input a), input a)

/-- `μ` is the unique color in relative majority. -/
def IsMajority {A : Type*} [Fintype A] (input : A → Fin k) (μ : Fin k) : Prop :=
  0 < inputCount input μ ∧ ∀ c, c ≠ μ → inputCount input c < inputCount input μ

variable {A : Type*} [DecidableEq A] [Fintype A]

lemma Hom.reachable {Q Q' : Type*} {P : Protocol Q} {P' : Protocol Q'} (φ : P.Hom P')
    {C C' : Config A Q} (h : P.Reachable C C') :
    P'.Reachable (fun x => φ.f (C x)) (fun x => φ.f (C' x)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih =>
    obtain ⟨a, b, hab, rfl⟩ := hst
    exact ih.tail ⟨a, b, hab, (φ.interact _ hab)⟩

/-- In a configuration whose braket part `B` is stable and whose only diagonal brakets are
`⟨μ|μ⟩`, an interaction does not change brakets, and every `out` either stays or becomes `μ`. -/
lemma step_out {B : Config A (Braket k)} (hB : Stable B) {μ : Fin k}
    (hdiag : ∀ x, (B x).1 = (B x).2 → (B x).1 = μ) {C : Config A (CState k)}
    (hC : ∀ x, (C x).1 = B x) {a b : A} (hab : a ≠ b) (x : A) :
    ((circles k).interact C a b x).1 = B x ∧
      (((circles k).interact C a b x).2 = (C x).2 ∨ ((circles k).interact C a b x).2 = μ) := by
  have hex : exch (C a).1 (C b).1 = ((C a).1, (C b).1) := by
    rw [exch, if_neg (by rw [hC, hC]; exact hB a b hab)]
  by_cases hxa : x = a
  · subst hxa
    simp only [Protocol.interact_self_left, circles, circlesδ, hex]
    split_ifs with h1 h2
    · exact ⟨hC x, Or.inr (by simp only [hC] at h1 ⊢; exact hdiag x h1.1)⟩
    · exact ⟨hC x, Or.inr (by simp only [hC] at h2 ⊢; exact hdiag b h2.1)⟩
    · exact ⟨hC x, Or.inl rfl⟩
  · by_cases hxb : x = b
    · subst hxb
      simp only [Protocol.interact_self_right _ _ hab, circles, circlesδ, hex]
      split_ifs with h1 h2
      · exact ⟨hC x, Or.inr (by simp only [hC] at h1 ⊢; exact hdiag a h1.1)⟩
      · exact ⟨hC x, Or.inr (by simp only [hC] at h2 ⊢; exact hdiag x h2.1)⟩
      · exact ⟨hC x, Or.inl rfl⟩
    · rw [Protocol.interact_other _ _ hxa hxb]
      exact ⟨hC x, Or.inl rfl⟩

/-- **Theorem 1.1** (The Circles protocol and relative majority).
Let `E` be an execution of Circles from the initial configuration of `input`, under a weakly fair
scheduler. Then
1. the brakets stabilize: from some time `T` on they never change;
2. in the stable configuration, an agent `⟨i|i⟩` exists iff `i` is the unique color in relative
   majority, and the multiset of brakets is `⋃_p f(G_p)` (Lemma 3.7);
3. if a unique majority color `μ` exists, then from some time on all agents output `μ`, and this
   output is stable (no future interaction can change any output). -/
theorem circles_correct (input : A → Fin k) (E : (circles k).Execution A)
    (h0 : E.config 0 = circlesInit input) (hE : E.WeaklyFair) :
    (∃ T, (∀ t ≥ T, ∀ a, (E.config t a).1 = (E.config T a).1) ∧
      brakets (fun a => (E.config T a).1) = layers (inputCount input) ∧
      ∀ i, (∃ a, (E.config T a).1 = (i, i)) ↔ IsMajority input i) ∧
    ∀ μ, IsMajority input μ →
      ∃ T, (∀ t ≥ T, ∀ a, output (E.config t a) = μ) ∧
        (circles k).OutputStable output (E.config T) := by
  set E' := E.map circlesToCore with hE'
  have h0' : E'.config 0 = initBrakets input := by
    funext a; simp [E', h0, circlesInit, initBrakets, circlesToCore]
  obtain ⟨T, hT, hS, hlay, hdiag⟩ := circlesCore_main E' input h0' (hE.map _)
  refine ⟨⟨T, fun t ht a => congrFun (hT t ht) a, hlay, hdiag⟩, fun μ hμ => ?_⟩
  set B := E'.config T with hB
  have hBdiag : ∀ x, (B x).1 = (B x).2 → (B x).1 = μ := by
    intro x hx
    have := (hdiag (B x).1).1 ⟨x, Prod.ext rfl hx.symm⟩
    by_contra hne
    exact absurd (this.2 μ (Ne.symm hne)) (not_lt.2 (hμ.2 _ hne).le)
  obtain ⟨d, hd⟩ := (hdiag μ).2 hμ
  have hbra : ∀ t ≥ T, ∀ x, (E.config t x).1 = B x := fun t ht x => congrFun (hT t ht) x
  -- persistence of `out = μ` after `T`
  have persist : ∀ t ≥ T, ∀ x, (E.config t x).2 = μ → (E.config (t + 1) x).2 = μ := by
    intro t ht x hx
    rw [E.step t]
    rcases (step_out hS hBdiag (hbra t ht) (E.sched_ne t) x).2 with h | h
    · rw [h, hx]
    · exact h
  -- the closed set of "final" configurations
  set S : Config A (CState k) → Prop := fun C => (∀ x, (C x).1 = B x) ∧ ∀ x, (C x).2 = μ
  have hSclosed : (circles k).Closed S := by
    rintro C C' ⟨h1, h2⟩ ⟨a, b, hab, rfl⟩
    refine ⟨fun x => (step_out hS hBdiag h1 hab x).1, fun x => ?_⟩
    rcases (step_out hS hBdiag h1 hab x).2 with h | h
    · rw [h, h2]
    · exact h
  -- every agent eventually outputs `μ`
  have hevent : ∀ x, ∃ t ≥ T, (E.config t x).2 = μ := by
    by_cases hall : ∀ y, (B y).1 = (B y).2
    · -- all brakets diagonal: all inputs are `μ`, and outputs were `μ` from the start
      have hin : ∀ y, input y = μ := by
        intro y
        have := hBdiag y (hall y)
        rw [hB, bra_const, h0'] at this
        exact this
      have hS0 : S (E.config 0) := by
        rw [h0]
        refine ⟨fun y => ?_, fun y => hin y⟩
        have h1 := hBdiag y (hall y); have h2 := hall y
        simp only [circlesInit, hin]
        exact Prod.ext h1.symm (h2 ▸ h1).symm
      intro x
      exact ⟨T, le_rfl, (hSclosed.execution E hS0 T (Nat.zero_le _)).2 x⟩
    · push Not at hall
      obtain ⟨b, hb⟩ := hall
      intro x
      by_cases hx : (B x).1 = (B x).2
      · -- `x` is diagonal: meet the non-diagonal agent `b`
        have hxb : x ≠ b := fun e => hb (e ▸ hx)
        obtain ⟨t, ht, hs⟩ := hE x b hxb T
        refine ⟨t + 1, by omega, ?_⟩
        have hex : exch (E.config t x).1 (E.config t b).1 = (B x, B b) := by
          rw [exch, hbra t ht, hbra t ht, if_neg (hS x b hxb)]
        rcases hs with hs | hs
        · rw [E.step t, hs]
          simp only [Protocol.interact_self_left, circles, circlesδ]
          rw [hex]; simp only
          rw [if_pos ⟨hx, hb⟩]; exact hBdiag x hx
        · rw [E.step t, hs]
          simp only [Protocol.interact_self_right _ _ (Ne.symm hxb), circles, circlesδ]
          have hex' : exch (E.config t b).1 (E.config t x).1 = (B b, B x) := by
            rw [exch, hbra t ht, hbra t ht, if_neg (hS b x (Ne.symm hxb))]
          rw [hex']; simp only
          rw [if_neg (fun h => hb h.1), if_pos ⟨hx, hb⟩]; exact hBdiag x hx
      · -- `x` is not diagonal: meet the diagonal agent `d`
        have hdd : (B d).1 = (B d).2 := by simp [hd]
        have hdμ : (B d).1 = μ := by simp [hd]
        have hdx : d ≠ x := by rintro rfl; exact hx hdd
        obtain ⟨t, ht, hs⟩ := hE d x hdx T
        refine ⟨t + 1, by omega, ?_⟩
        rcases hs with hs | hs
        · rw [E.step t, hs]
          simp only [Protocol.interact_self_right _ _ hdx, circles, circlesδ]
          have hex : exch (E.config t d).1 (E.config t x).1 = (B d, B x) := by
            rw [exch, hbra t ht, hbra t ht, if_neg (hS d x hdx)]
          rw [hex]; simp only
          rw [if_pos ⟨hdd, hx⟩]; exact hdμ
        · rw [E.step t, hs]
          simp only [Protocol.interact_self_left, circles, circlesδ]
          have hex : exch (E.config t x).1 (E.config t d).1 = (B x, B d) := by
            rw [exch, hbra t ht, hbra t ht, if_neg (hS x d (Ne.symm hdx))]
          rw [hex]; simp only
          rw [if_neg (fun h => hx h.1), if_pos ⟨hdd, hx⟩]; exact hdμ
  choose tx htx hout using hevent
  set T' := univ.sup tx with hT'
  have hall : ∀ x, ∀ t ≥ tx x, (E.config t x).2 = μ := by
    intro x t ht
    induction t, ht using Nat.le_induction with
    | base => exact hout x
    | succ t ht ih => exact persist t (le_trans (htx x) ht) x ih
  have hST : S (E.config T') := by
    refine ⟨fun x => hbra T' ?_ x, fun x => hall x T' (Finset.le_sup (mem_univ x))⟩
    obtain ⟨x⟩ : Nonempty A := ⟨d⟩
    exact le_trans (htx x) (Finset.le_sup (mem_univ x))
  refine ⟨T', fun t ht a => (hSclosed.execution E hST t ht).2 a, ?_⟩
  intro C' hC' a
  rw [output, output, (hSclosed.reachable hST hC').2 a, hST.2 a]

end RankingOpinions
