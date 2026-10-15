import Papers.PODC2026.RankingOpinions.Circles
import Cslib.Computability.Distributed.PopulationProtocols.Eventually
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Breaking ties (Section 4.3): `Circles_TieBreak`

Breitkopf, Dallot, El-Hayek, Schmid, PODC 2026, Section 4.3 and Appendix 8.5 (Theorem 4.3).

Each agent additionally stores a bit `tbt` (tie-break token). After the Circles transition:
1. (generation) if the agents exchanged kets and neither holds a token, the initiator generates one;
2. (destruction) if both hold a token, the initiator destroys its own;
3. (transfer) if exactly one holds a token, it is passed to the agent with the larger weight, and
   for equal weights to the one with the larger bra; (for equal weight *and* bra — unspecified in the
   paper — the token stays where it is);
finally, a token holder `a` with braket `⟨i_a|j_a⟩` sets `out_a := out_b := i_a`.

`tieBreak_correct`: under weak fairness all agents eventually output the same color forever, and
this color is one of the colors in relative majority (Theorem 4.3).
-/

set_option linter.unusedSectionVars false

namespace RankingOpinions

open Finset Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

variable {k : ℕ}

/-- States of `Circles_TieBreak`: a Circles state and the tie-break token bit (`2k³` states). -/
abbrev TBState (k : ℕ) := CState k × Bool

theorem card_TBState : Fintype.card (TBState k) = 2 * k ^ 3 := by
  rw [Fintype.card_prod, card_CState, Fintype.card_bool, mul_comm]

/-- Token rules 2 and 3 (destruction, transfer), given the keys of the two agents. -/
def tokMove (ka kb : ℕ) (ta tb : Bool) : Bool × Bool :=
  let ta2 := if ta && tb then false else ta
  if ta2 != tb then
    (if kb < ka then (true, false) else if ka < kb then (false, true) else (ta2, tb))
  else (ta2, tb)

/-- Transition function of `Circles_TieBreak`. -/
def tbδ (p q : TBState k) : TBState k × TBState k :=
  let r := circlesδ p.1 q.1
  let e := r.1.1
  let f := r.2.1
  let ta1 := p.2 || (decide (Profitable p.1.1 q.1.1) && !p.2 && !q.2)
  let t := tokMove (key e) (key f) ta1 q.2
  let oa := if t.1 then e.1 else if t.2 then f.1 else r.1.2
  let ob := if t.1 then e.1 else if t.2 then f.1 else r.2.2
  (((e, oa), t.1), ((f, ob), t.2))

/-- The protocol `Circles_TieBreak`. -/
def tieBreak (k : ℕ) : Protocol (TBState k) := ⟨tbδ⟩

def tbInit {A : Type*} (input : A → Fin k) : Config A (TBState k) :=
  fun a => (circlesInit input a, false)

def tbToCore : (tieBreak k).Hom (circlesCore k) where
  f s := s.1.1
  map_fst p q := by
    simp only [tieBreak, tbδ, circlesCore]
    exact circlesToCore.map_fst p.1 q.1
  map_snd p q := by
    simp only [tieBreak, tbδ, circlesCore]
    exact circlesToCore.map_snd p.1 q.1

/-! ## Token dynamics -/

/-- Value of the token holdings `(ta, tb)` (with keys `ka`, `kb` below `K`). -/
def tokVal (K ka kb : ℕ) (ta tb : Bool) : ℕ := (if ta then K - ka else 0) + (if tb then K - kb else 0)

lemma tokMove_cases {K ka kb : ℕ} (hka : ka < K) (hkb : kb < K) (ta tb : Bool) :
    tokMove ka kb ta tb = (ta, tb) ∨
      tokVal K ka kb (tokMove ka kb ta tb).1 (tokMove ka kb ta tb).2 < tokVal K ka kb ta tb := by
  unfold tokMove tokVal
  cases ta <;> cases tb <;> simp only [Bool.and_self, Bool.and_false, Bool.and_true,
    Bool.false_and, if_true, if_false, bne_self_eq_false, Bool.bne_true, Bool.bne_false,
    Bool.not_false, Bool.not_true] <;> split_ifs <;> simp_all <;> omega

lemma tokMove_exists {ka kb : ℕ} {ta tb : Bool} (h : (ta || tb) = true) :
    ((tokMove ka kb ta tb).1 || (tokMove ka kb ta tb).2) = true := by
  unfold tokMove; cases ta <;> cases tb <;> simp_all <;> split_ifs <;> simp

lemma tokMove_both (ka kb : ℕ) : tokMove ka kb true true ≠ (true, true) := by
  unfold tokMove; simp; split_ifs <;> simp

lemma tokMove_up {ka kb : ℕ} (h : ka < kb) : tokMove ka kb true false ≠ (true, false) := by
  unfold tokMove; simp; omega

lemma tokMove_up' {ka kb : ℕ} (h : kb < ka) : tokMove ka kb false true ≠ (false, true) := by
  unfold tokMove; simp; omega

lemma key_lt (e : Braket k) : key e < k * k + k := by
  unfold key
  have h1 := w_le e.1 e.2; have h2 := e.1.isLt
  have : w k e.1 e.2 * k ≤ k * k := Nat.mul_le_mul_right _ h1
  omega

variable {A : Type*} [DecidableEq A] [Fintype A]

/-- One interaction in a configuration whose brakets `B` are stable. -/
lemma tb_interact_stable {B : Config A (Braket k)} (hB : Stable B) {C : Config A (TBState k)}
    (hC : ∀ y, (C y).1.1 = B y) {a b : A} (hab : a ≠ b) :
    let C' := (tieBreak k).interact C a b
    (∀ y, (C' y).1.1 = B y) ∧
    ((C' a).2, (C' b).2) = tokMove (key (B a)) (key (B b)) (C a).2 (C b).2 ∧
    (C' a).1.2 = (if (C' a).2 then (B a).1 else if (C' b).2 then (B b).1
      else ((circles k).interact (fun z => (C z).1) a b a).2) ∧
    (C' b).1.2 = (if (C' a).2 then (B a).1 else if (C' b).2 then (B b).1
      else ((circles k).interact (fun z => (C z).1) a b b).2) ∧
    ∀ y, y ≠ a → y ≠ b → C' y = C y := by
  have hex : exch (C a).1.1 (C b).1.1 = (B a, B b) := by
    rw [exch, if_neg (by rw [hC, hC]; exact hB a b hab), hC, hC]
  have hnp : decide (Profitable (C a).1.1 (C b).1.1) = false := by
    rw [hC, hC]; simpa using hB a b hab
  have h1 : (circlesδ (C a).1 (C b).1).1.1 = B a := by
    simp only [circlesδ, hex]; split_ifs <;> rfl
  have h2 : (circlesδ (C a).1 (C b).1).2.1 = B b := by
    simp only [circlesδ, hex]; split_ifs <;> rfl
  refine ⟨fun y => ?_, ?_, ?_, ?_, fun y hya hyb => Protocol.interact_other _ _ hya hyb⟩
  · by_cases hya : y = a
    · subst hya; simp only [Protocol.interact_self_left, tieBreak, tbδ, h1]
    · by_cases hyb : y = b
      · subst hyb; simp only [Protocol.interact_self_right _ _ hab, tieBreak, tbδ, h2]
      · rw [Protocol.interact_other _ _ hya hyb, hC]
  · simp only [Protocol.interact_self_left, Protocol.interact_self_right _ _ hab, tieBreak, tbδ,
      h1, h2, hnp, Bool.false_and, Bool.or_false]
  · simp only [Protocol.interact_self_left, Protocol.interact_self_right _ _ hab, tieBreak, tbδ,
      h1, h2, hnp, Bool.false_and, Bool.or_false, circles]
  · simp only [Protocol.interact_self_left, Protocol.interact_self_right _ _ hab, tieBreak, tbδ,
      h1, h2, hnp, Bool.false_and, Bool.or_false, circles]

lemma tb_interact_tokens (C : Config A (TBState k)) {a b : A} (hab : a ≠ b) :
    (((tieBreak k).interact C a b a).2, ((tieBreak k).interact C a b b).2) =
      tokMove (key (circlesδ (C a).1 (C b).1).1.1) (key (circlesδ (C a).1 (C b).1).2.1)
        ((C a).2 || (decide (Profitable (C a).1.1 (C b).1.1) && !(C a).2 && !(C b).2)) (C b).2 := by
  simp only [Protocol.interact_self_left, Protocol.interact_self_right _ _ hab, tieBreak, tbδ]

/-- Two diagonal brakets of different colors can profitably exchange kets. -/
lemma profitable_diag {i j : Fin k} (h : i ≠ j) : Profitable (i, i) (j, j) := by
  unfold Profitable; simp only [w_self]
  exact lt_of_le_of_lt (min_le_left _ _) (lt_min (w_lt_of_ne h) (w_lt_of_ne h))

/-- Two untokened diagonal agents that cannot exchange do not change. -/
lemma tbδ_fix (p q : TBState k) (hp : p.1.1.1 = p.1.1.2) (hq : q.1.1.1 = q.1.1.2)
    (hpt : p.2 = false) (hqt : q.2 = false) (hnp : ¬ Profitable p.1.1 q.1.1) : tbδ p q = (p, q) := by
  have hex : exch p.1.1 q.1.1 = (p.1.1, q.1.1) := by rw [exch, if_neg hnp]
  have hr : circlesδ p.1 q.1 = (p.1, q.1) := by
    simp only [circlesδ, hex, hp, hq]; simp
  simp only [tbδ, hr, hpt, hqt, decide_eq_false hnp]
  simp only [tokMove]; simp
  exact ⟨Prod.ext rfl hpt.symm, Prod.ext rfl hqt.symm⟩

lemma init_interact_fix (input : A → Fin k) {a b : A} (hab : a ≠ b)
    (hp : ¬ Profitable (input a, input a) (input b, input b)) :
    (tieBreak k).interact (tbInit input) a b = tbInit input := by
  have hfix := tbδ_fix (tbInit input a) (tbInit input b) rfl rfl rfl rfl hp
  funext y
  by_cases hya : y = a
  · rw [hya, Protocol.interact_self_left]; simp only [tieBreak]; rw [hfix]
  · by_cases hyb : y = b
    · rw [hyb, Protocol.interact_self_right _ _ hab]; simp only [tieBreak]; rw [hfix]
    · rw [Protocol.interact_other _ _ hya hyb]

variable (input : A → Fin k) (E : (tieBreak k).Execution A)

lemma tok_persist (t : ℕ) (h : ∃ y, (E.config t y).2 = true) : ∃ y, (E.config (t + 1) y).2 = true := by
  obtain ⟨z, hz⟩ := h
  set a := (E.sched t).1; set b := (E.sched t).2
  have hab := E.sched_ne t
  have htok := tb_interact_tokens (E.config t) hab
  rw [← E.step t] at htok
  by_cases hza : z = a
  · have := tokMove_exists (ka := key (circlesδ (E.config t a).1 (E.config t b).1).1.1)
      (kb := key (circlesδ (E.config t a).1 (E.config t b).1).2.1)
      (ta := (E.config t a).2 || (decide (Profitable (E.config t a).1.1 (E.config t b).1.1) &&
        !(E.config t a).2 && !(E.config t b).2)) (tb := (E.config t b).2) (by rw [← hza, hz]; simp)
    rw [← htok] at this
    rcases Bool.or_eq_true_iff.1 this with h | h
    · exact ⟨a, h⟩
    · exact ⟨b, h⟩
  · by_cases hzb : z = b
    · have := tokMove_exists (ka := key (circlesδ (E.config t a).1 (E.config t b).1).1.1)
        (kb := key (circlesδ (E.config t a).1 (E.config t b).1).2.1)
        (ta := (E.config t a).2 || (decide (Profitable (E.config t a).1.1 (E.config t b).1.1) &&
          !(E.config t a).2 && !(E.config t b).2)) (tb := (E.config t b).2)
          (by rw [← hzb, hz]; simp)
      rw [← htok] at this
      rcases Bool.or_eq_true_iff.1 this with h | h
      · exact ⟨a, h⟩
      · exact ⟨b, h⟩
    · refine ⟨z, ?_⟩
      rw [E.step t, Protocol.interact_other _ _ hza hzb, hz]

/-- Before the first token appears the configuration is the initial one. -/
lemma tok_or_init (h0 : E.config 0 = tbInit input) (t : ℕ) :
    (∃ y, (E.config t y).2 = true) ∨ E.config t = tbInit input := by
  induction t with
  | zero => exact Or.inr h0
  | succ t ih =>
    rcases ih with h | h
    · exact Or.inl (tok_persist E t h)
    · set a := (E.sched t).1; set b := (E.sched t).2
      have hab := E.sched_ne t
      by_cases hp : Profitable (E.config t a).1.1 (E.config t b).1.1
      · left
        have htok := tb_interact_tokens (E.config t) hab
        rw [← E.step t] at htok
        have ha0 : (E.config t a).2 = false := by rw [h]; rfl
        have hb0 : (E.config t b).2 = false := by rw [h]; rfl
        have := tokMove_exists (ka := key (circlesδ (E.config t a).1 (E.config t b).1).1.1)
          (kb := key (circlesδ (E.config t a).1 (E.config t b).1).2.1)
          (ta := (E.config t a).2 || (decide (Profitable (E.config t a).1.1 (E.config t b).1.1) &&
            !(E.config t a).2 && !(E.config t b).2)) (tb := (E.config t b).2)
            (by simp [ha0, hb0, hp])
        rw [← htok] at this
        rcases Bool.or_eq_true_iff.1 this with h' | h'
        · exact ⟨a, h'⟩
        · exact ⟨b, h'⟩
      · right
        rw [E.step t, h]
        rw [h] at hp
        exact init_interact_fix input hab hp

/-- Total token value `∑_{y holds a token} (K - key y)` for fixed brakets `B`. -/
def tokPot (B : Config A (Braket k)) (C : Config A (TBState k)) : ℕ :=
  ∑ y, if (C y).2 then k * k + k - key (B y) else 0

/-- **Theorem 4.3** (`Circles_TieBreak`). Under a weakly fair scheduler, eventually all agents
output the same color `c` forever, and `c` is a color in relative majority (`x_c` is maximal);
in particular, if the majority is unique, everybody outputs it. -/
theorem tieBreak_correct (h0 : E.config 0 = tbInit input) (hE : E.WeaklyFair) :
    ∃ c, (∀ c', inputCount input c' ≤ inputCount input c) ∧
      ∃ T, ∀ t ≥ T, ∀ a, (E.config t a).1.2 = c := by
  set E2 := E.map tbToCore with hE2
  have h02 : E2.config 0 = initBrakets input := by
    funext a; simp [E2, h0, tbInit, circlesInit, initBrakets, tbToCore]
  obtain ⟨T0, hT0, hS, hlay, hdiag⟩ := circlesCore_main E2 input h02 (hE.map _)
  set B := E2.config T0 with hB
  have hbr : ∀ t ≥ T0, ∀ y, (E.config t y).1.1 = B y := fun t ht y => congrFun (hT0 t ht) y
  obtain ⟨p1, p2, hp⟩ : ∃ p1 p2 : A, p1 ≠ p2 := ⟨_, _, E.sched_ne 0⟩
  rcases tok_or_init input E h0 T0 with htok | hinit
  swap
  · -- no exchange ever happened: all agents have the same color
    have hBi : ∀ y, B y = (input y, input y) := by
      intro y; rw [← hbr T0 le_rfl, hinit]; rfl
    have hsame : ∀ y, input y = input p1 := by
      intro y; by_contra hne
      exact hS y p1 (fun e => hne (e ▸ rfl)) (by rw [hBi, hBi]; exact profitable_diag hne)
    have hfix : ∀ t ≥ T0, E.config t = tbInit input := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => exact hinit
      | succ t ht ih =>
        have hab := E.sched_ne t
        rw [E.step t, ih]
        apply init_interact_fix input hab
        have := hS _ _ hab; rwa [hBi, hBi] at this
    refine ⟨input p1, fun c' => ?_, T0, fun t ht a => by rw [hfix t ht, ← hsame a]; rfl⟩
    unfold inputCount
    apply Finset.card_le_card
    intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    exact hsame y
  -- tokens exist from `T0` on
  have htokT : ∀ t ≥ T0, ∃ y, (E.config t y).2 = true := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact htok
    | succ t _ ih => exact tok_persist E t ih
  -- the token potential is monotone and strictly decreases when tokens move
  have hstep : ∀ t ≥ T0, (∀ y, (E.config (t + 1) y).2 = (E.config t y).2) ∨
      tokPot B (E.config (t + 1)) < tokPot B (E.config t) := by
    intro t ht
    have hab := E.sched_ne t
    obtain ⟨-, htk, -, -, ho⟩ := tb_interact_stable hS (hbr t ht) hab
    rw [← E.step t] at htk ho
    set a := (E.sched t).1; set b := (E.sched t).2
    rcases tokMove_cases (K := k * k + k) (key_lt (B a)) (key_lt (B b)) (E.config t a).2
      (E.config t b).2 with h | h
    · left
      rw [← htk] at h
      intro y
      by_cases hya : y = a
      · rw [hya]; exact (Prod.ext_iff.1 h).1
      · by_cases hyb : y = b
        · rw [hyb]; exact (Prod.ext_iff.1 h).2
        · rw [ho y hya hyb]
    · right
      rw [← htk] at h
      unfold tokPot
      rw [sum_split _ hab, sum_split (fun y => if (E.config t y).2 then k * k + k - key (B y)
        else 0) hab]
      have hrest : ∑ x ∈ (univ.erase a).erase b,
          (if (E.config (t + 1) x).2 then k * k + k - key (B x) else 0) =
          ∑ x ∈ (univ.erase a).erase b,
          (if (E.config t x).2 then k * k + k - key (B x) else 0) := by
        apply Finset.sum_congr rfl; intro x hx; simp only [mem_erase] at hx
        rw [ho x hx.2.1 hx.1]
      rw [hrest]
      unfold tokVal at h
      simp only at h ⊢
      omega
  have hmono : ∀ t ≥ T0, tokPot B (E.config (t + 1)) ≤ tokPot B (E.config t) := by
    intro t ht
    rcases hstep t ht with h | h
    · unfold tokPot; simp only [h, le_refl]
    · exact h.le
  -- the potential is eventually constant
  obtain ⟨T1, hT1, hT1min⟩ : ∃ T1 ≥ T0, ∀ t ≥ T0, tokPot B (E.config T1) ≤ tokPot B (E.config t) := by
    classical
    have hex : ∃ m, ∃ u, tokPot B (E.config (T0 + u)) = m := ⟨_, 0, rfl⟩
    obtain ⟨u0, hu0⟩ := Nat.find_spec hex
    refine ⟨T0 + u0, by omega, fun t ht => ?_⟩
    rw [hu0]
    obtain ⟨u, rfl⟩ : ∃ u, t = T0 + u := ⟨t - T0, by omega⟩
    exact Nat.find_min' hex ⟨u, rfl⟩
  have hmono' : ∀ s ≥ T0, ∀ t ≥ s, tokPot B (E.config t) ≤ tokPot B (E.config s) := by
    intro s hs t ht
    induction t, ht using Nat.le_induction with
    | base => exact le_rfl
    | succ t ht ih => exact (hmono t (by omega)).trans ih
  -- tokens are constant from `T1` on
  have hconst : ∀ t ≥ T1, ∀ y, (E.config t y).2 = (E.config T1 y).2 := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => intro y; rfl
    | succ t ht ih =>
      rcases hstep t (by omega) with h | h
      · intro y; rw [h, ih]
      · exfalso
        have h1 := hT1min (t + 1) (by omega)
        have h2 := hmono' T1 hT1 t ht
        omega
  set tok := fun y => (E.config T1 y).2 with htokdef
  obtain ⟨z, hz⟩ := htokT T1 hT1
  -- interaction facts after `T1`
  have pairTok : ∀ t ≥ T1, ∀ a b, (E.sched t = (a, b)) →
      tokMove (key (B a)) (key (B b)) (tok a) (tok b) = (tok a, tok b) := by
    intro t ht a b hs
    have hab := E.sched_ne t
    rw [hs] at hab
    obtain ⟨-, htk, -, -, -⟩ := tb_interact_stable hS (hbr t (by omega)) hab
    rw [← hs, ← E.step t, hs] at htk
    simp only at htk
    rw [hconst (t + 1) (by omega), hconst (t + 1) (by omega), hconst t ht, hconst t ht] at htk
    exact htk.symm
  have huniq : ∀ y, tok y = true → y = z := by
    intro y hy
    by_contra hyz
    obtain ⟨t, ht, hs⟩ := hE z y (Ne.symm hyz) T1
    rcases hs with hs | hs
    · have := pairTok t ht _ _ hs; rw [show tok z = true from hz, hy] at this; exact tokMove_both _ _ this
    · have := pairTok t ht _ _ hs; rw [show tok z = true from hz, hy] at this; exact tokMove_both _ _ this
  have hmax : ∀ y, key (B y) ≤ key (B z) := by
    intro y
    by_contra hlt; push Not at hlt
    have hyz : y ≠ z := by rintro rfl; exact lt_irrefl _ hlt
    have hy : tok y = false := by
      by_contra h; exact hyz (huniq y (by simpa using h))
    obtain ⟨t, ht, hs⟩ := hE z y (Ne.symm hyz) T1
    rcases hs with hs | hs
    · have := pairTok t ht _ _ hs; rw [show tok z = true from hz, hy] at this; exact tokMove_up hlt this
    · have := pairTok t ht _ _ hs; rw [show tok z = true from hz, hy] at this; exact tokMove_up' hlt this
  set c := (B z).1 with hc
  have hBmem : ∀ y, B y ∈ layers (inputCount input) := by
    intro y; rw [← hlay]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val y)
  have hmaj : ∀ c', inputCount input c' ≤ inputCount input c := by
    intro c'
    by_contra hlt; push Not at hlt
    have hsup : inputCount input c < univ.sup (inputCount input) :=
      lt_of_lt_of_le hlt (Finset.le_sup (mem_univ c'))
    obtain ⟨f, hf, hkf⟩ := exists_key_gt (inputCount input) (hBmem z) hsup
    rw [← hlay] at hf
    obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hf
    exact absurd (hmax y) (not_le.2 hkf)
  have hdiagc : ∀ d, (B d).1 = (B d).2 → (B d).1 = c := by
    intro d hd
    have hzd : (B z).1 = (B z).2 := by
      by_contra hne
      have : key (B z) < key (B d) := key_lt_of_w_lt (by
        rw [show B d = ((B d).1, (B d).2) from rfl, hd, w_self]; exact w_lt_of_ne hne)
      exact absurd (hmax d) (not_le.2 this)
    have m1 := (hdiag (B d).1).1 ⟨d, Prod.ext rfl hd.symm⟩
    have m2 := (hdiag (B z).1).1 ⟨z, Prod.ext rfl hzd.symm⟩
    by_contra hne
    exact absurd (m1.2 _ (Ne.symm hne)) (not_lt.2 (m2.2 _ hne).le)
  -- outputs after an interaction at time `t ≥ T1`
  have outs : ∀ t ≥ T1, ∀ a b, E.sched t = (a, b) →
      ((E.config (t + 1) a).1.2 = c ∨ ((tok a || tok b) = false ∧
        ((E.config (t + 1) a).1.2 = (E.config t a).1.2 ∨ (E.config (t + 1) a).1.2 = c))) ∧
      ((E.config (t + 1) b).1.2 = c ∨ ((tok a || tok b) = false ∧
        ((E.config (t + 1) b).1.2 = (E.config t b).1.2 ∨ (E.config (t + 1) b).1.2 = c))) := by
    intro t ht a b hs
    have hab := E.sched_ne t
    rw [hs] at hab
    obtain ⟨-, -, hoa, hob, -⟩ := tb_interact_stable hS (hbr t (by omega)) hab
    rw [← hs, ← E.step t, hs] at hoa hob
    simp only at hoa hob
    rw [hconst (t + 1) (by omega), hconst (t + 1) (by omega)] at hoa hob
    have hcirc := fun x => (step_out hS hdiagc (C := fun w => (E.config t w).1)
      (hbr t (by omega)) hab x).2
    by_cases ha : tok a = true
    · have := huniq a ha
      rw [if_pos ha] at hoa hob
      exact ⟨Or.inl (hoa.trans (by rw [this])), Or.inl (hob.trans (by rw [this]))⟩
    · by_cases hb : tok b = true
      · have := huniq b hb
        rw [if_neg ha, if_pos hb] at hoa hob
        exact ⟨Or.inl (hoa.trans (by rw [this])), Or.inl (hob.trans (by rw [this]))⟩
      · rw [if_neg ha, if_neg hb] at hoa hob
        have hab0 : (tok a || tok b) = false := by simp_all
        exact ⟨Or.inr ⟨hab0, hoa ▸ hcirc a⟩, Or.inr ⟨hab0, hob ▸ hcirc b⟩⟩
  have persist : ∀ t ≥ T1, ∀ y, (E.config t y).1.2 = c → (E.config (t + 1) y).1.2 = c := by
    intro t ht y hy
    set a := (E.sched t).1; set b := (E.sched t).2
    have hs : E.sched t = (a, b) := rfl
    obtain ⟨h1, h2⟩ := outs t ht a b hs
    by_cases hya : y = a
    · rw [hya] at hy ⊢
      rcases h1 with h | ⟨-, h | h⟩
      · exact h
      · rw [h, hy]
      · exact h
    · by_cases hyb : y = b
      · rw [hyb] at hy ⊢
        rcases h2 with h | ⟨-, h | h⟩
        · exact h
        · rw [h, hy]
        · exact h
      · have hab := E.sched_ne t
        obtain ⟨-, -, -, -, ho⟩ := tb_interact_stable hS (hbr t (by omega)) hab
        rw [← E.step t] at ho
        rw [ho y hya hyb, hy]
  have reach : ∀ y, ∃ t ≥ T1, (E.config t y).1.2 = c := by
    intro y
    obtain ⟨w, hw⟩ : ∃ w, w ≠ y ∧ (y = z ∨ w = z) := by
      by_cases hyz : y = z
      · by_cases h1 : y = p1
        · exact ⟨p2, by rw [h1]; exact hp.symm, Or.inl hyz⟩
        · exact ⟨p1, Ne.symm h1, Or.inl hyz⟩
      · exact ⟨z, Ne.symm hyz, Or.inr rfl⟩
    obtain ⟨hwy, hzz⟩ := hw
    have htz : (tok y || tok w) = true := by
      rcases hzz with h | h <;> simp [h, hz, tok]
    obtain ⟨t, ht, hs⟩ := hE y w (Ne.symm hwy) T1
    refine ⟨t + 1, by omega, ?_⟩
    rcases hs with hs | hs
    · rcases (outs t ht _ _ hs).1 with h | ⟨h, -⟩
      · exact h
      · rw [htz] at h; exact absurd h (by simp)
    · rcases (outs t ht _ _ hs).2 with h | ⟨h, -⟩
      · exact h
      · rw [Bool.or_comm, htz] at h; exact absurd h (by simp)
  obtain ⟨T, -, hT⟩ := eventually_all (P := fun t y => (E.config t y).1.2 = c) T1 persist reach
  exact ⟨c, hmaj, T, hT⟩

end RankingOpinions
