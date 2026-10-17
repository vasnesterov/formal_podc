import Papers.PODC2026.RankingOpinions.TieShareRules
import Podc.Foundations.Data.Nat.Descent
import Papers.PODC2026.RankingOpinions.TieShareGeom

/-!
# Circles_TieSharing: correctness (Theorem 4.2)

Breitkopf, Dallot, El-Hayek, Schmid, PODC 2026, Theorem 4.2 / Appendix 8.4, for the sequential
reading of the rules (`tieShare k false`). Main result: `tieShare_correct`.

Structure of the proof (the paper's proof is a sketch; the steps below replace it):
* `win_of_diag`: a diagonal agent `⟨i|i⟩` is always a `winner` (this uses the sequential reading:
  rule (3) demotes a token holder of another color before it can apply rule (7)).
* After stabilization (Theorem 3.4, Lemma 3.7) every non-diagonal braket is an arc inside a sector
  `[μ, nxt S μ]` (Claim 2); the paper's inclusion `⊆` of modulo ranges (with its extra condition)
  becomes inclusion of offset intervals inside one sector (`rsub_iff` in `TieShareGeom`).
* `r = 1` (`Ctx1.main1`): sectors of the smallest greedy set with two colors. All tokens disappear
  (`Ctx1.no_tokens`, by `extinction` with rank (distance of the sector from `μ`, end offset,
  length)); afterwards rule (3) and rule (i) of the diagonal agents fix everybody. The paper's
  Lemma 8.2 ignores the tokens still present after stabilization.
* `r ≥ 2` (`Ctx.main2`): sectors of the set `M` of majority colors.
  - `Ctx.keep_nonLos`: an agent of a majority color which is not a loser stays so (F1);
  - `Ctx.tokIn_succ`: a sector containing a token keeps containing one;
  - `Ctx.no_spurious`: tokens not on a top arc `⟨μ|nxt M μ⟩` eventually disappear (rank: end offset,
    length; token multiplication into the next sector targets a loser of majority color, which
    happens at most once per agent);
  - `Ctx.ws_const`: eventually the set of token holders is constant;
  - `tok_at_T0` (the last exchange creates a token) and `witness` (Claim 3, made precise: once all
    agents of color `μ_s` have their final braket, one of them is a `winner_spreader` or a
    `loser`) give, through token multiplication, a top token in every sector (`Ctx.all_sectors`,
    the paper's "token ascent until attached" and induction over `s`);
  - rule (7) and rule (ii) of the top tokens then fix all statuses and outputs.
-/

set_option linter.unusedSectionVars false

namespace RankingOpinions

open Finset Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

variable {k : ℕ}

/-! ### Facts about two agents whose brakets do not change -/

/-- The facts used by the rules when no exchange takes place. -/
def relS (e f : Braket k) : PR :=
  nx (dg e) (dg f) (decide (e.1 = f.1)) (decide (e.2 = f.1)) (decide (f.2 = e.1))
    (decide (RSub e f)) (decide (RSub f e)) (decide (RSSub e f)) (decide (RSSub f e))

lemma relS_swap (e f : Braket k) : relS f e = (relS e f).swap := by
  simp only [relS, nx, PR.swap, eq_comm (a := f.1)]

lemma relOf_eq {e f : Braket k} (h : ¬ Profitable e f) : relOf e f = relS e f := by
  simp only [relOf, mkPR, relS, nx, decide_eq_false h]

lemma exch_swap (e f : Braket k) : exch f e = ((exch e f).2, (exch e f).1) := by
  unfold exch
  by_cases h : Profitable e f
  · rw [if_pos (profitable_comm.1 h), if_pos h]
  · rw [if_neg (fun h' => h (profitable_comm.1 h')), if_neg h]

lemma mkPR_swap (p q e f : Braket k) : mkPR q p f e = (mkPR p q e f).swap := by
  have : decide (Profitable q p) = decide (Profitable p q) := decide_eq_decide.2 profitable_comm
  simp only [mkPR, PR.swap, this, eq_comm (a := f.1)]

variable {A : Type*} [DecidableEq A] [Fintype A]

attribute [local irreducible] stUpd outUpd mkPR

/-- Status, output variable and braket of an agent in an execution. -/
abbrev stA (E : (tieShare k false).Execution A) (t : ℕ) (y : A) : St := (E.config t y).2.2
abbrev outA (E : (tieShare k false).Execution A) (t : ℕ) (y : A) : Fin k := (E.config t y).2.1
abbrev brA (E : (tieShare k false).Execution A) (t : ℕ) (y : A) : Braket k := (E.config t y).1

/-- `x` and `y` interact at time `t` (in some order). -/
def Meet (E : (tieShare k false).Execution A) (t : ℕ) (x y : A) : Prop :=
  E.sched t = (x, y) ∨ E.sched t = (y, x)

lemma Meet.ne {E : (tieShare k false).Execution A} {t : ℕ} {x y : A} (h : Meet E t x y) :
    x ≠ y := by
  rcases h with h | h <;> have := E.sched_ne t <;> rw [h] at this
  · exact this
  · exact Ne.symm this

lemma Meet.symm {E : (tieShare k false).Execution A} {t : ℕ} {x y : A} (h : Meet E t x y) :
    Meet E t y x := Or.symm h

lemma upd_true (r : PR) (sx sy : St) : upd true r sx sy = stUpd false r sx sy := rfl

lemma upd_false (r : PR) (sx sy : St) :
    upd false r sx sy = ((stUpd false r.swap sy sx).2, (stUpd false r.swap sy sx).1) := rfl

/-- The facts of an interaction of `x` with `y` at time `t`. -/
def rAt (E : (tieShare k false).Execution A) (t : ℕ) (x y : A) : PR :=
  mkPR (brA E t x) (brA E t y) (exch (brA E t x) (brA E t y)).1 (exch (brA E t x) (brA E t y)).2

lemma rAt_swap (E : (tieShare k false).Execution A) (t : ℕ) (x y : A) :
    rAt E t y x = (rAt E t x y).swap := by
  unfold rAt; rw [exch_swap, mkPR_swap]

/-- One interaction seen from agent `x` (general case). -/
lemma view (E : (tieShare k false).Execution A) {t : ℕ} {x y : A} (hm : Meet E t x y) :
    ∃ o : Bool,
      brA E (t + 1) x = (exch (brA E t x) (brA E t y)).1 ∧
      brA E (t + 1) y = (exch (brA E t x) (brA E t y)).2 ∧
      (stA E (t + 1) x, stA E (t + 1) y) = upd o (rAt E t x y) (stA E t x) (stA E t y) ∧
      outA E (t + 1) x = outUpd false (rAt E t x y) (stA E (t + 1) y) (stA E t y)
        (exch (brA E t x) (brA E t y)).2.1 (outA E t x) := by
  have hne := hm.ne
  rcases hm with h | h
  · refine ⟨true, ?_⟩
    obtain ⟨h1, h2⟩ := ts_interact false (E.config t) hne
    have ha : E.config (t + 1) x = (tieShare k false).interact (E.config t) x y x := by
      rw [E.step t, h]
    have hb : E.config (t + 1) y = (tieShare k false).interact (E.config t) x y y := by
      rw [E.step t, h]
    rw [upd_true]
    simp only [brA, stA, outA, rAt]
    rw [ha, hb, h1, h2]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · refine ⟨false, ?_⟩
    obtain ⟨h1, h2⟩ := ts_interact false (E.config t) (Ne.symm hne)
    have ha : E.config (t + 1) x = (tieShare k false).interact (E.config t) y x x := by
      rw [E.step t, h]
    have hb : E.config (t + 1) y = (tieShare k false).interact (E.config t) y x y := by
      rw [E.step t, h]
    have hxy : rAt E t x y = (rAt E t y x).swap := rAt_swap E t y x
    rw [hxy, upd_false, PR.swap_swap, exch_swap (brA E t y) (brA E t x)]
    simp only [brA, stA, outA, rAt]
    rw [ha, hb, h1, h2]
    exact ⟨rfl, rfl, rfl, rfl⟩

lemma view_other (E : (tieShare k false).Execution A) {t : ℕ} {z : A}
    (h1 : z ≠ (E.sched t).1) (h2 : z ≠ (E.sched t).2) : E.config (t + 1) z = E.config t z := by
  rw [E.step t, Protocol.interact_other _ _ h1 h2]

/-- Every agent either does not interact at time `t`, or meets some partner. -/
lemma step_cases (E : (tieShare k false).Execution A) (t : ℕ) (x : A) :
    E.config (t + 1) x = E.config t x ∨ ∃ y, Meet E t x y := by
  by_cases h1 : x = (E.sched t).1
  · right; exact ⟨(E.sched t).2, Or.inl (by rw [h1])⟩
  · by_cases h2 : x = (E.sched t).2
    · right; exact ⟨(E.sched t).1, Or.inr (by rw [h2])⟩
    · left; exact view_other E h1 h2

/-- One interaction seen from agent `x`, when the brakets are stable. -/
lemma view_stable (E : (tieShare k false).Execution A) {B : Config A (Braket k)}
    (hB : Stable B) {t : ℕ} (hC : ∀ y, brA E t y = B y) {x y : A} (hm : Meet E t x y) :
    ∃ o : Bool,
      brA E (t + 1) x = B x ∧ brA E (t + 1) y = B y ∧
      (stA E (t + 1) x, stA E (t + 1) y) = upd o (relS (B x) (B y)) (stA E t x) (stA E t y) ∧
      outA E (t + 1) x = outUpd false (relS (B x) (B y)) (stA E (t + 1) y) (stA E t y)
        (B y).1 (outA E t x) := by
  obtain ⟨o, h1, h2, h3, h4⟩ := view E hm
  have hex : exch (brA E t x) (brA E t y) = (B x, B y) := by
    rw [hC, hC, exch, ite_eq_right_iff.2 (fun h => absurd h (hB x y hm.ne))]
  have hr : rAt E t x y = relS (B x) (B y) := by
    unfold rAt; rw [hex, hC, hC]; exact relOf_eq (hB x y hm.ne)
  rw [hr] at h3 h4; rw [hex] at h1 h2 h4
  exact ⟨o, h1, h2, h3, h4⟩

/-! ### Generic "eventually forever" arguments -/

lemma never_after {W : ℕ → Prop} {T : ℕ} (hT : ¬ W T) (h : ∀ t ≥ T, ¬ W t → ¬ W (t + 1)) :
    ∀ t ≥ T, ¬ W t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hT
  | succ t ht ih => exact h t ht ih

lemma always_after {W : ℕ → Prop} {T : ℕ} (hT : W T) (h : ∀ t ≥ T, W t → W (t + 1)) :
    ∀ t ≥ T, W t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hT
  | succ t ht ih => exact h t ht ih

/-- **Extinction of tokens.** Agents of `R` hold tokens (`W`). If, after `T'`, an agent of `R` gains
a token only from a partner of `R` of smaller rank holding one, or (at most once) when it is a
loser (`L`) that never becomes a loser again; and if every agent of `R` loses its token infinitely
often; then eventually no agent of `R` holds a token. -/
lemma extinction (W L : ℕ → A → Prop) (R : A → Prop) (ρ : A → ℕ) (T' : ℕ)
    (hgain : ∀ t ≥ T', ∀ c, R c → ¬ W t c → W (t + 1) c →
      (∃ p, R p ∧ ρ p < ρ c ∧ W t p) ∨ (L t c ∧ ∀ t' ≥ t + 1, ¬ L t' c))
    (hkill : ∀ c, R c → ∀ T, ∃ t ≥ T, ¬ W (t + 1) c) :
    ∃ T ≥ T', ∀ t ≥ T, ∀ c, R c → ¬ W t c := by
  classical
  have key : ∀ n, ∃ T ≥ T', ∀ t ≥ T, ∀ c, R c → ρ c < n → ¬ W t c := by
    intro n
    induction n with
    | zero => exact ⟨T', le_rfl, fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ n ih =>
      obtain ⟨T1, hT1, hlow⟩ := ih
      have per : ∀ c, ∃ Tc, ∀ t ≥ Tc, (R c → ρ c < n + 1 → ¬ W t c) := by
        intro c
        by_cases hc : R c ∧ ρ c = n
        · obtain ⟨hR, hρ⟩ := hc
          have hg : ∀ t ≥ T1, ¬ W t c → W (t + 1) c → L t c ∧ ∀ t' ≥ t + 1, ¬ L t' c := by
            intro t ht h1 h2
            rcases hgain t (le_trans hT1 ht) c hR h1 h2 with ⟨p, hp, hlt, hw⟩ | h
            · exact absurd hw (hlow t ht p hp (by omega))
            · exact h
          obtain ⟨t1, ht1, hw1⟩ := hkill c hR T1
          by_cases hev : ∀ t ≥ t1 + 1, ¬ W t c
          · exact ⟨t1 + 1, fun t ht _ _ => hev t ht⟩
          · push Not at hev
            have hex : ∃ s, s ≥ t1 + 1 ∧ W s c := hev
            set s := Nat.find hex with hsdef
            obtain ⟨hs1, hs2⟩ := Nat.find_spec hex
            have hsne : s ≠ t1 + 1 := fun h => hw1 (h ▸ hs2)
            have hprev : ¬ W (s - 1) c := fun h =>
              Nat.find_min hex (show s - 1 < s by omega) ⟨by omega, h⟩
            have hsucc : W (s - 1 + 1) c := by rw [Nat.sub_add_cancel (by omega)]; exact hs2
            obtain ⟨-, hnl⟩ := hg (s - 1) (by omega) hprev hsucc
            obtain ⟨t3, ht3, hw3⟩ := hkill c hR s
            refine ⟨t3 + 1, fun t ht _ _ => never_after (W := fun t => W t c) hw3 ?_ t ht⟩
            intro t' ht' h1 h2
            exact hnl t' (by omega) (hg t' (by omega) h1 h2).1
        · exact ⟨T1, fun t ht hR hlt => hlow t ht c hR (by
            by_contra h; exact hc ⟨hR, by omega⟩)⟩
      obtain ⟨T2, -, hT2⟩ := Nat.eventually_forall_of_finite per 0
      exact ⟨max T1 T2, le_trans hT1 (le_max_left _ _),
        fun t ht c hR hlt => hT2 t (le_trans (le_max_right _ _) ht) c hR hlt⟩
  obtain ⟨T, hT, h⟩ := key (univ.sup ρ + 1)
  exact ⟨T, hT, fun t ht c hR => h t ht c hR
    (Nat.lt_succ_of_le (Finset.le_sup (f := ρ) (mem_univ c)))⟩

lemma rank_lt {k a a' b b' : ℕ} (hb : b ≤ k) (h : a < a' ∨ (a = a' ∧ b < b')) :
    a * (k + 1) + b < a' * (k + 1) + b' := by
  rcases h with h | ⟨rfl, h⟩
  · have : a * (k + 1) + (k + 1) ≤ a' * (k + 1) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h
    omega
  · omega

/-! ### The stable phase with at least two sectors -/

/-- The situation after the brakets stabilized, all of them being `S`-arcs. -/
structure Ctx (E : (tieShare k false).Execution A) where
  S : Finset (Fin k)
  hS : TwoPlus S
  hSne : S.Nonempty
  B : Config A (Braket k)
  hB : Stable B
  T0 : ℕ
  hT0 : ∀ t ≥ T0, ∀ y, brA E t y = B y
  hArc : ∀ y, IsArc S (B y)

namespace Ctx

variable {E : (tieShare k false).Execution A} (c : Ctx E)

noncomputable def σ (y : A) : Fin k := sec c.S (c.B y)
noncomputable def o (y : A) : ℕ := off c.S (c.B y)
noncomputable def e (y : A) : ℕ := en c.S (c.B y)
noncomputable def L (μ : Fin k) : ℕ := secLen c.S μ
/-- `y` holds the top arc of its sector. -/
def Top (y : A) : Prop := c.o y = 0 ∧ c.e y = c.L (c.σ y)

lemma σ_mem (y : A) : c.σ y ∈ c.S := sec_mem c.hSne _
lemma o_lt_e (y : A) : c.o y < c.e y := off_lt_en (c.hArc y)
lemma e_le (y : A) : c.e y ≤ c.L (c.σ y) := arc_en_le c.hS c.hSne (c.hArc y)
lemma L_lt (μ : Fin k) : c.L μ < k := secLen_lt μ

lemma dg_false (y : A) : dg (c.B y) = false := by
  simp only [dg, decide_eq_false_iff_not]; exact (c.hArc y).1

def sbB (x y : A) : Bool := decide ((c.B x).1 = (c.B y).1)
def kB (x y : A) : Bool := decide ((c.B x).2 = (c.B y).1)
def subB (x y : A) : Bool := decide (RSub (c.B x) (c.B y))
def qB (x y : A) : Bool := decide (RSSub (c.B x) (c.B y))
/-- The facts of an interaction of `x` with `y` in the stable phase. -/
def R (x y : A) : PR :=
  nx false false (c.sbB x y) (c.kB x y) (c.kB y x) (c.subB x y) (c.subB y x) (c.qB x y) (c.qB y x)

lemma sb_iff (x y : A) : c.sbB x y = true ↔ c.σ x = c.σ y ∧ c.o x = c.o y := by
  rw [sbB, decide_eq_true_iff]; exact bra_eq_iff

lemma sub_iff (x y : A) : c.subB x y = true ↔
    c.σ x = c.σ y ∧ c.o y ≤ c.o x ∧ c.e x ≤ c.e y := by
  rw [subB, decide_eq_true_iff]; exact rsub_iff c.hS c.hSne (c.hArc x) (c.hArc y)

lemma ssub_iff (x y : A) : c.qB x y = true ↔
    c.σ x = c.σ y ∧ c.o y ≤ c.o x ∧ c.e x ≤ c.e y ∧ (c.o x ≠ c.o y ∨ c.e x ≠ c.e y) := by
  rw [qB, decide_eq_true_iff]; exact rssub_iff c.hS c.hSne (c.hArc x) (c.hArc y)

lemma k_iff (x y : A) : c.kB x y = true ↔
    (c.σ x = c.σ y ∧ c.e x = c.o y ∧ c.e x < c.L (c.σ x)) ∨
      (c.e x = c.L (c.σ x) ∧ c.o y = 0 ∧ c.σ y = nxt c.S (c.σ x)) := by
  rw [kB, decide_eq_true_iff]; exact ket_eq_bra_iff c.hS c.hSne (c.hArc x)

lemma relS_eq (x y : A) : relS (c.B x) (c.B y) = c.R x y := by
  rw [relS, c.dg_false, c.dg_false]; rfl

lemma qb_sub {x y : A} (h : c.qB x y = true) : c.subB x y = true := by
  rw [qB, decide_eq_true_iff] at h; rw [subB, decide_eq_true_iff]; exact h.1

lemma false_of_not {b : Bool} (h : ¬ b = true) : b = false := by simpa using h

/-- One interaction in the stable phase, seen from `x`. -/
lemma step {t : ℕ} (ht : c.T0 ≤ t) {x y : A} (hm : Meet E t x y) :
    ∃ o : Bool,
      (stA E (t + 1) x, stA E (t + 1) y) = upd o (c.R x y) (stA E t x) (stA E t y) ∧
      outA E (t + 1) x =
        outUpd false (c.R x y) (stA E (t + 1) y) (stA E t y) (c.B y).1 (outA E t x) := by
  obtain ⟨o, -, -, h3, h4⟩ := view_stable E c.hB (c.hT0 t ht) hm
  rw [c.relS_eq] at h3 h4
  exact ⟨o, h3, h4⟩

lemma step1 {t : ℕ} (ht : c.T0 ≤ t) {x y : A} (hm : Meet E t x y) :
    ∃ o : Bool, stA E (t + 1) x = (upd o (c.R x y) (stA E t x) (stA E t y)).1 ∧
      stA E (t + 1) y = (upd o (c.R x y) (stA E t x) (stA E t y)).2 := by
  obtain ⟨o, h, -⟩ := c.step ht hm
  exact ⟨o, by rw [← h], by rw [← h]⟩

/-- F1: an agent at offset `0` (its color is a majority color) which is not a loser never
becomes a loser. -/
lemma keep_nonLos {t : ℕ} (ht : c.T0 ≤ t) {x : A} (hx : c.o x = 0) (h : stA E t x ≠ St.los) :
    stA E (t + 1) x ≠ St.los := by
  rcases step_cases E t x with h1 | ⟨y, hm⟩
  · simp only [stA, h1]; exact h
  · obtain ⟨o, h3, -⟩ := c.step1 ht hm
    rw [h3]
    exact upd_keep_nonLos o false _ _ _ _ _ _ _ _ (stA E t y) h
      (fun hs => by
        obtain ⟨h1, h2, -⟩ := (c.sub_iff x y).1 hs
        exact (c.sb_iff x y).2 ⟨h1, by omega⟩)
      (fun hs => by
        obtain ⟨h1, h2, -⟩ := (c.ssub_iff x y).1 hs
        exact (c.sb_iff x y).2 ⟨h1, by omega⟩)
      (fun h => absurd h Bool.false_ne_true)

lemma keep_nonLos_all {T : ℕ} (hT : c.T0 ≤ T) {x : A} (hx : c.o x = 0) (h : stA E T x ≠ St.los) :
    ∀ t ≥ T, stA E t x ≠ St.los :=
  always_after (W := fun t => stA E t x ≠ St.los) h
    (fun t ht h => c.keep_nonLos (le_trans hT ht) hx h)

/-! #### Top arcs -/

lemma top_of_eq {y : A} {μ : Fin k} (hμ : μ ∈ c.S) (h : c.B y = (μ, nxt c.S μ)) :
    c.σ y = μ ∧ c.Top y := by
  have hσ : c.σ y = μ := by
    unfold σ sec; rw [h]; exact secOf_of_mem hμ
  refine ⟨hσ, ?_⟩
  have := (top_iff c.hS c.hSne (c.hArc y)).2 (by rw [h]; unfold sec; simp only [secOf_of_mem hμ])
  exact this

lemma top_kB {y z : A} (hy : c.Top y) (h : c.kB y z = true) :
    c.o z = 0 ∧ c.σ z = nxt c.S (c.σ y) := by
  rcases (c.k_iff y z).1 h with ⟨-, -, h3⟩ | ⟨-, h2, h3⟩
  · have := hy.2; omega
  · exact ⟨h2, h3⟩

lemma kB_top {y z : A} (hy : c.Top y) (h0 : c.o z = 0) (hσ : c.σ z = nxt c.S (c.σ y)) :
    c.kB y z = true := (c.k_iff y z).2 (Or.inr ⟨hy.2, h0, hσ⟩)

lemma qB_top_false {y z : A} (hy : c.Top y) : c.qB y z = false := by
  apply false_of_not; intro h
  obtain ⟨h1, h2, h3, h4⟩ := (c.ssub_iff y z).1 h
  have := c.e_le z; rw [← h1] at this
  have := hy.1; have := hy.2
  omega

lemma qB_into_top {y z : A} (hy : c.Top y) (hσ : c.σ z = c.σ y) (hz : ¬ c.Top z) :
    c.qB z y = true := by
  have hz' := c.e_le z; rw [hσ] at hz'
  refine (c.ssub_iff z y).2 ⟨hσ, by rw [hy.1]; exact Nat.zero_le _, by rw [hy.2]; exact hz', ?_⟩
  by_contra h; push Not at h
  exact hz ⟨by rw [h.1, hy.1], by rw [h.2, hy.2, hσ]⟩

lemma subB_into_top {y z : A} (hy : c.Top y) (hσ : c.σ z = c.σ y) : c.subB z y = true := by
  have hz' := c.e_le z; rw [hσ] at hz'
  exact (c.sub_iff z y).2 ⟨hσ, by rw [hy.1]; exact Nat.zero_le _, by rw [hy.2]; exact hz'⟩

/-! #### Persistence of tokens in a sector (F2) -/

/-- Some agent of the sector of `μ` holds a token at time `t`. -/
def TokIn (t : ℕ) (μ : Fin k) : Prop := ∃ y, c.σ y = μ ∧ stA E t y = St.ws

lemma tokIn_succ {t : ℕ} (ht : c.T0 ≤ t) {μ : Fin k} (h : c.TokIn t μ) : c.TokIn (t + 1) μ := by
  obtain ⟨y, hy, hw⟩ := h
  rcases step_cases E t y with h1 | ⟨p, hm⟩
  · exact ⟨y, hy, by simp only [stA, h1]; exact hw⟩
  · obtain ⟨o, h3, h4⟩ := c.step1 ht hm
    rw [hw] at h3 h4
    have hsb : c.sbB y p = true → c.subB y p = true ∨ c.qB p y = true := by
      intro hb
      obtain ⟨h1, h2⟩ := (c.sb_iff y p).1 hb
      rcases le_or_gt (c.e y) (c.e p) with h5 | h5
      · exact Or.inl ((c.sub_iff y p).2 ⟨h1, by omega, h5⟩)
      · exact Or.inr ((c.ssub_iff p y).2 ⟨h1.symm, by omega, by omega, Or.inr (by omega)⟩)
    rcases upd_tok_survive o _ _ _ _ _ _ _ (stA E t p) hsb c.qb_sub with h5 | ⟨h5, h6⟩
    · exact ⟨y, hy, h3.trans h5⟩
    · exact ⟨p, ((c.sub_iff y p).1 h6).1 ▸ hy, h4.trans h5⟩

lemma tokIn_after {T : ℕ} (hT : c.T0 ≤ T) {μ : Fin k} (h : c.TokIn T μ) :
    ∀ t ≥ T, c.TokIn t μ :=
  always_after (W := fun t => c.TokIn t μ) h (fun t ht h => c.tokIn_succ (le_trans hT ht) h)

/-! #### Extinction of spurious tokens (F5) -/

variable (hTop : ∀ μ ∈ c.S, ∃ y, c.B y = (μ, nxt c.S μ))
include hTop

lemma exists_top (y : A) : ∃ tp, c.σ tp = c.σ y ∧ c.Top tp := by
  obtain ⟨tp, htp⟩ := hTop _ (c.σ_mem y)
  exact ⟨tp, c.top_of_eq (c.σ_mem y) htp⟩

/-- A token held by an agent which is not at the top of its sector eventually disappears, and
no such token is created any more. -/
lemma no_spurious (hE : E.WeaklyFair) :
    ∃ T ≥ c.T0, ∀ t ≥ T, ∀ y, ¬ c.Top y → stA E t y ≠ St.ws := by
  have hρ : ∀ y, c.e y - c.o y ≤ k := fun y => by have := c.e_le y; have := c.L_lt (c.σ y); omega
  refine extinction (fun t y => stA E t y = St.ws) (fun t y => stA E t y = St.los)
    (fun y => ¬ c.Top y) (fun y => c.e y * (k + 1) + (c.e y - c.o y)) c.T0 ?_ ?_
  · intro t ht z hz h1 h2
    rcases step_cases E t z with he | ⟨p, hm⟩
    · exact absurd (by simp only [stA, he] at h2; exact h2) h1
    · obtain ⟨o, h3, -⟩ := c.step1 ht hm
      rw [h3] at h2
      obtain ⟨hp, hcase⟩ := upd_gain o false false _ _ _ _ _ _ _ _ (stA E t p) h1
        (fun h => absurd h Bool.false_ne_true) h2
      rcases hcase with ⟨hk, hl⟩ | hq
      · rcases (c.k_iff p z).1 hk with ⟨hs, he, hlt⟩ | ⟨-, h0, -⟩
        · left
          refine ⟨p, fun htp => by rw [htp.2] at hlt; exact lt_irrefl _ hlt, ?_, hp⟩
          have := c.o_lt_e z
          exact rank_lt (hρ p) (Or.inl (by omega))
        · right
          refine ⟨hl, fun t' ht' => ?_⟩
          have hw : stA E (t + 1) z ≠ St.los := by rw [h3, h2]; decide
          exact c.keep_nonLos_all (by omega) h0 hw t' ht'
      · obtain ⟨hs, h5, h6, h7⟩ := (c.ssub_iff p z).1 hq
        left
        refine ⟨p, fun htp => hz ⟨?_, ?_⟩, ?_, hp⟩
        · have := htp.1; omega
        · have := htp.2; have := c.e_le z; rw [← hs] at *; omega
        · apply rank_lt (hρ p)
          rcases lt_or_eq_of_le h6 with h8 | h8
          · exact Or.inl h8
          · right; refine ⟨h8, ?_⟩
            rcases h7 with h9 | h9
            · have := c.o_lt_e p; omega
            · exact absurd h8 h9
  · intro z hz T
    obtain ⟨tp, hσ, htp⟩ := c.exists_top hTop z
    have hne : z ≠ tp := fun h => hz (h ▸ htp)
    obtain ⟨t, ht, hm⟩ := hE z tp hne (max T c.T0)
    refine ⟨t, le_trans (le_max_left _ _) ht, ?_⟩
    obtain ⟨o, h3, -⟩ := c.step1 (le_trans (le_max_right _ _) ht) hm
    show stA E (t + 1) z ≠ St.ws
    have hk : c.kB tp z = false := by
      apply false_of_not; intro h
      obtain ⟨-, h2⟩ := c.top_kB htp h
      rw [hσ] at h2; exact c.hS _ (c.σ_mem z) h2.symm
    have hR : c.R z tp = nx false false (c.sbB z tp) (c.kB z tp) false (c.subB z tp)
        (c.subB tp z) true false := by
      simp only [Ctx.R, hk, c.qB_into_top htp hσ.symm hz, c.qB_top_false htp]
    rw [h3, hR]
    exact upd_kill o _ _ _ _ _ _

/-- After the spurious tokens disappeared, a top agent gains a token only as a loser. -/
lemma top_gain {T5 : ℕ} (hT5 : c.T0 ≤ T5)
    (h5 : ∀ t ≥ T5, ∀ y, ¬ c.Top y → stA E t y ≠ St.ws) {t : ℕ} (ht : T5 ≤ t) {y : A}
    (h1 : stA E t y ≠ St.ws) (h2 : stA E (t + 1) y = St.ws) : stA E t y = St.los := by
  rcases step_cases E t y with he | ⟨p, hm⟩
  · exact absurd (by simp only [stA, he] at h2; exact h2) h1
  · obtain ⟨o, h3, -⟩ := c.step1 (le_trans hT5 ht) hm
    rw [h3] at h2
    obtain ⟨hp, hcase⟩ := upd_gain o false false _ _ _ _ _ _ _ _ (stA E t p) h1
      (fun h => absurd h Bool.false_ne_true) h2
    have htp : c.Top p := by by_contra h; exact h5 t ht p h hp
    rcases hcase with ⟨-, hl⟩ | hq
    · exact hl
    · rw [c.qB_top_false htp] at hq; exact absurd hq Bool.false_ne_true

/-- Eventually, the set of token holders never changes, and all of them are top agents. -/
lemma ws_const (hE : E.WeaklyFair) :
    ∃ T6 ≥ c.T0, (∀ t ≥ T6, ∀ y, ¬ c.Top y → stA E t y ≠ St.ws) ∧
      ∀ t ≥ T6, ∀ y, (stA E t y = St.ws ↔ stA E T6 y = St.ws) := by
  classical
  obtain ⟨T5, hT5, h5⟩ := c.no_spurious hTop hE
  have per : ∀ y, ∃ b : Prop, ∃ Ty, ∀ t ≥ Ty, (stA E t y = St.ws ↔ b) := by
    intro y
    by_cases hy : c.Top y
    · by_cases hex : ∃ t1 ≥ T5, stA E t1 y = St.ws
      · obtain ⟨t1, ht1, hw1⟩ := hex
        have hnl := c.keep_nonLos_all (le_trans hT5 ht1) hy.1 (by rw [hw1]; decide)
        by_cases hall : ∀ t ≥ t1, stA E t y = St.ws
        · exact ⟨True, t1, fun t ht => by simp [hall t ht]⟩
        · push Not at hall
          obtain ⟨t2, ht2, hw2⟩ := hall
          refine ⟨False, t2, fun t ht => ?_⟩
          have := never_after (W := fun t => stA E t y = St.ws) hw2 (fun t' ht' h1 h2 =>
            hnl t' (by omega) (c.top_gain hTop hT5 h5 (by omega) h1 h2)) t ht
          simp [this]
      · push Not at hex
        exact ⟨False, T5, fun t ht => by simp [hex t ht]⟩
    · exact ⟨False, T5, fun t ht => by simp [h5 t ht y hy]⟩
  choose b Ty hTy using per
  obtain ⟨T6', -, hT6'⟩ := Nat.eventually_forall_of_finite
    (p := fun y t => (stA E t y = St.ws ↔ b y)) (fun y => ⟨Ty y, hTy y⟩) 0
  refine ⟨max T6' T5, le_trans hT5 (le_max_right _ _),
    fun t ht => h5 t (le_trans (le_max_right _ _) ht), fun t ht y => ?_⟩
  rw [hT6' t (le_trans (le_max_left _ _) ht) y, hT6' _ (le_max_left _ _) y]

/-- **Lemma 8.3 / Claim 3 of the paper, made precise.** Eventually every sector has a top agent
holding a token forever, and these are the only tokens. -/
lemma all_sectors (hE : E.WeaklyFair) (hTok : ∃ y, stA E c.T0 y = St.ws)
    (hWit : ∀ μ ∈ c.S, ∃ y, c.σ y = μ ∧ c.o y = 0 ∧
      (stA E c.T0 y = St.ws ∨ stA E c.T0 y = St.los)) :
    ∃ T6 ≥ c.T0, (∀ t ≥ T6, ∀ y, ¬ c.Top y → stA E t y ≠ St.ws) ∧
      ∀ μ ∈ c.S, ∃ y, c.σ y = μ ∧ c.Top y ∧ ∀ t ≥ T6, stA E t y = St.ws := by
  obtain ⟨T6, hT6, h6, hc⟩ := c.ws_const hTop hE
  -- `Ws μ`: some agent of the sector of `μ` holds a token at `T6`
  have hWs_of_tok : ∀ μ, ∀ t ≥ c.T0, c.TokIn t μ → ∃ y, c.σ y = μ ∧ stA E T6 y = St.ws := by
    intro μ t ht h
    obtain ⟨y, hy, hw⟩ := c.tokIn_after ht h (max t T6) (le_max_left _ _)
    exact ⟨y, hy, (hc _ (le_max_right _ _) y).1 hw⟩
  have chain : ∀ μ ∈ c.S, (∃ y, c.σ y = μ ∧ stA E T6 y = St.ws) →
      ∃ y, c.σ y = nxt c.S μ ∧ stA E T6 y = St.ws := by
    intro μ hμ ⟨y, hy, hw⟩
    by_contra hno
    set ν := nxt c.S μ with hν
    have hnotok : ∀ t ≥ c.T0, ¬ c.TokIn t ν := fun t ht h => hno (hWs_of_tok ν t ht h)
    obtain ⟨w, hwσ, hw0, hwst⟩ := hWit ν (nxt_mem hμ)
    have hwl : stA E c.T0 w = St.los := by
      rcases hwst with h | h
      · exact absurd ⟨w, hwσ, h⟩ (hnotok c.T0 le_rfl)
      · exact h
    -- the witness stays a loser
    have hwl' : ∀ t ≥ c.T0, stA E t w = St.los := by
      refine always_after (W := fun t => stA E t w = St.los) hwl (fun t ht h => ?_)
      by_contra hnl
      rcases step_cases E t w with he | ⟨p, hm⟩
      · exact hnl (by simp only [stA, he]; exact h)
      · obtain ⟨o, h3, h4⟩ := c.step1 ht hm
        rw [h] at h3 h4
        rw [h3] at hnl
        rcases upd_los_leave o _ _ _ _ _ _ _ (stA E t p) hnl with h5 | ⟨h5, h6⟩
        · exact hnotok (t + 1) (by omega) ⟨w, hwσ, h3.trans h5⟩
        · exact hnotok (t + 1) (by omega)
            ⟨p, ((c.sb_iff w p).1 h6).1 ▸ hwσ, h4.trans h5⟩
    -- the token holder `y` is a top agent of the sector of `μ`, forever
    have hyT : c.Top y := by by_contra h; exact h6 T6 le_rfl y h hw
    have hyw : ∀ t ≥ T6, stA E t y = St.ws := fun t ht => (hc t ht y).2 hw
    have hne : w ≠ y := by
      intro h; rw [h, hy] at hwσ; exact c.hS μ hμ hwσ.symm
    obtain ⟨t, ht, hm⟩ := hE w y hne T6
    obtain ⟨o, h3, -⟩ := c.step1 (le_trans hT6 ht) hm
    rw [hwl' t (le_trans hT6 ht), hyw t ht] at h3
    have hσne : c.σ w ≠ c.σ y := by rw [hwσ, hy]; exact c.hS μ hμ
    have hsb : c.sbB w y = false := false_of_not fun h => hσne ((c.sb_iff w y).1 h).1
    have hsub1 : c.subB w y = false := false_of_not fun h => hσne ((c.sub_iff w y).1 h).1
    have hsub2 : c.subB y w = false := false_of_not fun h => hσne ((c.sub_iff y w).1 h).1.symm
    have hq1 : c.qB w y = false := false_of_not fun h => hσne ((c.ssub_iff w y).1 h).1
    have hq2 : c.qB y w = false := false_of_not fun h => hσne ((c.ssub_iff y w).1 h).1.symm
    have hk : c.kB y w = true := c.kB_top hyT hw0 (by rw [hwσ, hy])
    have hR : c.R w y = nx false false false (c.kB w y) true false false false false := by
      simp only [Ctx.R, hsb, hsub1, hsub2, hq1, hq2, hk]
    rw [hR, upd_mult] at h3
    exact hnotok (t + 1) (by omega) ⟨w, hwσ, h3⟩
  -- some sector has a token at `T0`
  obtain ⟨y0, hy0⟩ := hTok
  have base := hWs_of_tok (c.σ y0) c.T0 le_rfl ⟨y0, rfl, hy0⟩
  have hall : ∀ μ ∈ c.S, ∃ y, c.σ y = μ ∧ stA E T6 y = St.ws := by
    intro μ hμ
    obtain ⟨n, hn⟩ := nxt_iterate_reach c.hS (c.σ_mem y0) hμ
    rw [← hn]
    clear hn
    induction n with
    | zero => exact base
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact chain _ (by
        clear ih; induction n with
        | zero => exact c.σ_mem y0
        | succ n ih' => rw [Function.iterate_succ_apply']; exact nxt_mem ih') ih
  refine ⟨T6, hT6, h6, fun μ hμ => ?_⟩
  obtain ⟨y, hy, hw⟩ := hall μ hμ
  have hyT : c.Top y := by by_contra h; exact h6 T6 le_rfl y h hw
  exact ⟨y, hy, hyT, fun t ht => (hc t ht y).2 hw⟩

/-- **Theorem 4.2, case `r ≥ 2`, in sector coordinates.** Eventually forever: agents at offset `0`
(whose color is a majority color) are not losers; all other agents are losers and their `out` is a
majority color. -/
theorem main2 (hE : E.WeaklyFair) (hTok : ∃ y, stA E c.T0 y = St.ws)
    (hWit : ∀ μ ∈ c.S, ∃ y, c.σ y = μ ∧ c.o y = 0 ∧
      (stA E c.T0 y = St.ws ∨ stA E c.T0 y = St.los)) :
    ∃ T, ∀ t ≥ T, ∀ y, (c.o y = 0 → stA E t y ≠ St.los) ∧
      (c.o y ≠ 0 → stA E t y = St.los ∧ outA E t y ∈ c.S) := by
  obtain ⟨T6, hT6, h6, htop⟩ := c.all_sectors hTop hE hTok hWit
  choose! tp htpσ htpT htpw using htop
  suffices hp : (∀ t ≥ T6, ∀ y, ((c.o y = 0 → stA E t y ≠ St.los) ∧
      (c.o y ≠ 0 → stA E t y = St.los ∧ outA E t y ∈ c.S)) →
      ((c.o y = 0 → stA E (t + 1) y ≠ St.los) ∧
      (c.o y ≠ 0 → stA E (t + 1) y = St.los ∧ outA E (t + 1) y ∈ c.S))) ∧
      (∀ y, ∃ t ≥ T6, (c.o y = 0 → stA E t y ≠ St.los) ∧
      (c.o y ≠ 0 → stA E t y = St.los ∧ outA E t y ∈ c.S)) by
    obtain ⟨T, -, hT⟩ := eventually_all (P := fun t y => (c.o y = 0 → stA E t y ≠ St.los) ∧
      (c.o y ≠ 0 → stA E t y = St.los ∧ outA E t y ∈ c.S)) T6 hp.1 hp.2
    exact ⟨T, hT⟩
  refine ⟨?_, ?_⟩
  · -- persistence
    intro t ht y ⟨h1, h2⟩
    refine ⟨fun h0 => c.keep_nonLos (le_trans hT6 ht) h0 (h1 h0), fun h0 => ?_⟩
    obtain ⟨hl, hout⟩ := h2 h0
    rcases step_cases E t y with he | ⟨p, hm⟩
    · simp only [stA, outA, he]; exact ⟨hl, hout⟩
    · obtain ⟨o, h3, h4⟩ := c.step (le_trans hT6 ht) hm
      have hst : stA E (t + 1) y = St.los := by
        have := congrArg Prod.fst h3; simp only at this; rw [this, hl]
        apply upd_keep_los
        intro hp
        have hpT : c.Top p := by by_contra h; exact h6 t ht p h hp
        refine ⟨false_of_not fun h => h0 (c.top_kB hpT h).1,
          false_of_not fun h => ?_, false_of_not fun h => h0 ?_⟩
        · obtain ⟨-, h5, -⟩ := (c.ssub_iff p y).1 h; have := hpT.1; omega
        · rw [((c.sb_iff y p).1 h).2, hpT.1]
      refine ⟨hst, ?_⟩
      rw [h4]
      simp only [outUpd, rd, Ctx.R, nx, Bool.false_eq_true, if_false, Bool.false_and,
        Bool.and_false, ite_false]
      split_ifs with hc
      · have hpT : c.Top p := by by_contra h; exact h6 (t + 1) (by omega) p h hc.1
        have : (c.B p).1 = c.σ p := by
          have := hpT.1; unfold Ctx.o off at this; exact (dst_eq_zero this).symm
        rw [this]; exact c.σ_mem p
      · exact hout
  · -- eventually
    intro y
    by_cases h0 : c.o y = 0
    · set z := tp (c.σ y) (c.σ_mem y)
      have hz : c.Top z := htpT (c.σ y) (c.σ_mem y)
      have hzσ : c.σ z = c.σ y := htpσ (c.σ y) (c.σ_mem y)
      have hzw : ∀ t ≥ T6, stA E t z = St.ws := htpw (c.σ y) (c.σ_mem y)
      clear_value z
      by_cases hyz : y = z
      · refine ⟨T6, le_rfl, fun _ => by rw [hyz, hzw T6 le_rfl]; decide, fun h => absurd h0 h⟩
      · obtain ⟨t, ht, hm⟩ := hE y z hyz T6
        refine ⟨t + 1, by omega, fun _ => ?_, fun h => absurd h0 h⟩
        obtain ⟨o, h3, -⟩ := c.step1 (le_trans hT6 ht) hm
        rw [h3, hzw t ht]
        have hsb : c.sbB y z = true := (c.sb_iff y z).2 ⟨hzσ.symm, by rw [h0, hz.1]⟩
        have hR : c.R y z = nx false false true (c.kB y z) (c.kB z y) true (c.subB z y)
            (c.qB y z) false := by
          simp only [Ctx.R, hsb, c.subB_into_top hz hzσ.symm, c.qB_top_false hz]
        rw [hR]; exact upd_win_same o _ _ _ _ _
    · set z := tp (c.σ y) (c.σ_mem y)
      have hz : c.Top z := htpT (c.σ y) (c.σ_mem y)
      have hzσ : c.σ z = c.σ y := htpσ (c.σ y) (c.σ_mem y)
      have hzw : ∀ t ≥ T6, stA E t z = St.ws := htpw (c.σ y) (c.σ_mem y)
      clear_value z
      have hyT : ¬ c.Top y := fun h => h0 h.1
      have hyz : y ≠ z := fun h => hyT (h ▸ hz)
      obtain ⟨t, ht, hm⟩ := hE y z hyz T6
      refine ⟨t + 1, by omega, fun h => absurd h h0, fun _ => ?_⟩
      obtain ⟨o, h3, h4⟩ := c.step (le_trans hT6 ht) hm
      have hsb : c.sbB y z = false := false_of_not fun h => h0 (by rw [((c.sb_iff y z).1 h).2, hz.1])
      have hk : c.kB z y = false := false_of_not fun h => h0 (c.top_kB hz h).1
      have hR : c.R y z = nx false false false (c.kB y z) false true (c.subB z y) true false := by
        simp only [Ctx.R, hsb, hk, c.subB_into_top hz hzσ.symm, c.qB_into_top hz hzσ.symm hyT,
          c.qB_top_false hz]
      rw [hR, hzw t ht] at h3; rw [hR, hzw t ht] at h4
      have hl := upd_lose_inside o (c.kB y z) (c.subB z y) (stA E t y) (h6 t ht y hyT)
      have e1 := congrArg Prod.fst h3; have e2 := congrArg Prod.snd h3
      simp only at e1 e2
      refine ⟨e1.trans hl.1, ?_⟩
      rw [h4, e2, hl.2]
      simp only [outUpd, rd, nx, Bool.false_eq_true, if_false, and_self, if_true, ite_true]
      have : (c.B z).1 = c.σ z := by
        have := hz.1; unfold Ctx.o off at this; exact (dst_eq_zero this).symm
      rw [this]; exact c.σ_mem z

end Ctx

/-! ### The stable phase with a unique majority color -/

/-- The situation after the brakets stabilized when `μ` is the unique majority color: the
diagonal brakets are `⟨μ|μ⟩` (and exist), the others are `S`-arcs, and diagonal agents are always
winners. -/
structure Ctx1 (E : (tieShare k false).Execution A) where
  S : Finset (Fin k)
  hS : TwoPlus S
  hSne : S.Nonempty
  B : Config A (Braket k)
  hB : Stable B
  T0 : ℕ
  hT0 : ∀ t ≥ T0, ∀ y, brA E t y = B y
  μ : Fin k
  hμ : μ ∈ S
  hArc : ∀ y, dg (B y) = false → IsArc S (B y)
  hDiag : ∀ y, dg (B y) = true → (B y).1 = μ
  hd : ∃ d, dg (B d) = true
  hWin : ∀ t y, dg (brA E t y) = true → stA E t y = St.win

namespace Ctx1

variable {E : (tieShare k false).Execution A} (c : Ctx1 E)

noncomputable def σ (y : A) : Fin k := sec c.S (c.B y)
noncomputable def o (y : A) : ℕ := off c.S (c.B y)
noncomputable def e (y : A) : ℕ := en c.S (c.B y)
noncomputable def L (μ : Fin k) : ℕ := secLen c.S μ

def sbB (x y : A) : Bool := decide ((c.B x).1 = (c.B y).1)
def kB (x y : A) : Bool := decide ((c.B x).2 = (c.B y).1)
def subB (x y : A) : Bool := decide (RSub (c.B x) (c.B y))
def qB (x y : A) : Bool := decide (RSSub (c.B x) (c.B y))
def R (x y : A) : PR :=
  nx (dg (c.B x)) (dg (c.B y)) (c.sbB x y) (c.kB x y) (c.kB y x) (c.subB x y) (c.subB y x)
    (c.qB x y) (c.qB y x)

lemma σ_mem (y : A) : c.σ y ∈ c.S := sec_mem c.hSne _

lemma step {t : ℕ} (ht : c.T0 ≤ t) {x y : A} (hm : Meet E t x y) :
    ∃ o : Bool,
      (stA E (t + 1) x, stA E (t + 1) y) = upd o (c.R x y) (stA E t x) (stA E t y) ∧
      outA E (t + 1) x =
        outUpd false (c.R x y) (stA E (t + 1) y) (stA E t y) (c.B y).1 (outA E t x) := by
  obtain ⟨o, -, -, h3, h4⟩ := view_stable E c.hB (c.hT0 t ht) hm
  exact ⟨o, h3, h4⟩

lemma step1 {t : ℕ} (ht : c.T0 ≤ t) {x y : A} (hm : Meet E t x y) :
    ∃ o : Bool, stA E (t + 1) x = (upd o (c.R x y) (stA E t x) (stA E t y)).1 ∧
      stA E (t + 1) y = (upd o (c.R x y) (stA E t x) (stA E t y)).2 := by
  obtain ⟨o, h, -⟩ := c.step ht hm
  exact ⟨o, by rw [← h], by rw [← h]⟩

lemma win_of_dg {t : ℕ} (ht : c.T0 ≤ t) {y : A} (h : dg (c.B y) = true) : stA E t y = St.win :=
  c.hWin t y (by rw [c.hT0 t ht]; exact h)

lemma sub_iff {x y : A} (hx : dg (c.B x) = false) (hy : dg (c.B y) = false) :
    c.subB x y = true ↔ c.σ x = c.σ y ∧ c.o y ≤ c.o x ∧ c.e x ≤ c.e y := by
  rw [subB, decide_eq_true_iff]; exact rsub_iff c.hS c.hSne (c.hArc x hx) (c.hArc y hy)

lemma ssub_iff {x y : A} (hx : dg (c.B x) = false) (hy : dg (c.B y) = false) :
    c.qB x y = true ↔
      c.σ x = c.σ y ∧ c.o y ≤ c.o x ∧ c.e x ≤ c.e y ∧ (c.o x ≠ c.o y ∨ c.e x ≠ c.e y) := by
  rw [qB, decide_eq_true_iff]; exact rssub_iff c.hS c.hSne (c.hArc x hx) (c.hArc y hy)

lemma k_iff {x : A} (hx : dg (c.B x) = false) (y : A) : c.kB x y = true ↔
    (c.σ x = c.σ y ∧ c.e x = c.o y ∧ c.e x < c.L (c.σ x)) ∨
      (c.e x = c.L (c.σ x) ∧ c.o y = 0 ∧ c.σ y = nxt c.S (c.σ x)) := by
  rw [kB, decide_eq_true_iff]; exact ket_eq_bra_iff c.hS c.hSne (c.hArc x hx)

/-- A non-diagonal agent of color `μ`: sector `μ`, offset `0`. -/
lemma bra_mu_iff (y : A) : (c.B y).1 = c.μ ↔ c.σ y = c.μ ∧ c.o y = 0 := by
  constructor
  · intro h
    have : c.σ y = c.μ := by unfold σ sec; rw [h]; exact secOf_of_mem c.hμ
    refine ⟨this, ?_⟩
    unfold o off; rw [show sec c.S (c.B y) = c.μ from this, h, dst_self]
  · rintro ⟨h1, h2⟩
    have := (dst_eq_zero h2).symm
    rw [this]; exact h1

/-- F1 for the unique-majority case. -/
lemma keep_nonLos {t : ℕ} (ht : c.T0 ≤ t) {x : A} (hx : dg (c.B x) = false)
    (hμx : (c.B x).1 = c.μ) (h : stA E t x ≠ St.los) : stA E (t + 1) x ≠ St.los := by
  rcases step_cases E t x with h1 | ⟨y, hm⟩
  · simp only [stA, h1]; exact h
  · obtain ⟨ob, h3, -⟩ := c.step1 ht hm
    rw [h3]
    have hR : c.R x y = nx false (dg (c.B y)) (c.sbB x y) (c.kB x y) (c.kB y x) (c.subB x y)
        (c.subB y x) (c.qB x y) (c.qB y x) := by rw [R, hx]
    rw [hR]
    have hσ := (c.bra_mu_iff x).1 hμx
    -- the partner has the same bra whenever a rule could make `x` a loser
    have key : (dg (c.B y) = true ∨ c.subB x y = true) → c.sbB x y = true := by
      rintro (hy | hs)
      · rw [sbB, decide_eq_true_iff, hμx, c.hDiag y hy]
      · cases hy : dg (c.B y)
        · obtain ⟨h1, h2, -⟩ := (c.sub_iff hx hy).1 hs
          rw [sbB, decide_eq_true_iff, hμx]
          exact ((c.bra_mu_iff y).2 ⟨h1.symm.trans hσ.1, by omega⟩).symm
        · rw [sbB, decide_eq_true_iff, hμx, c.hDiag y hy]
    have hq : c.qB x y = true → c.subB x y = true := fun hq => by
      rw [qB, decide_eq_true_iff] at hq; rw [subB, decide_eq_true_iff]; exact hq.1
    exact upd_keep_nonLos ob _ _ _ _ _ _ _ _ _ (stA E t y) h (fun hs => key (Or.inr hs))
      (fun h' => key (Or.inr (hq h'))) (fun hy => key (Or.inl hy))

lemma keep_nonLos_all {T : ℕ} (hT : c.T0 ≤ T) {x : A} (hx : dg (c.B x) = false)
    (hμx : (c.B x).1 = c.μ) (h : stA E T x ≠ St.los) : ∀ t ≥ T, stA E t x ≠ St.los :=
  always_after (W := fun t => stA E t x ≠ St.los) h
    (fun t ht h => c.keep_nonLos (le_trans hT ht) hx hμx h)

/-- All tokens eventually disappear. -/
lemma no_tokens (hE : E.WeaklyFair) : ∃ T ≥ c.T0, ∀ t ≥ T, ∀ y, stA E t y ≠ St.ws := by
  have hρ : ∀ y, dg (c.B y) = false → c.e y - c.o y ≤ k := fun y hy => by
    have := arc_en_le c.hS c.hSne (c.hArc y hy)
    have := secLen_lt (S := c.S) (sec c.S (c.B y))
    show en c.S (c.B y) - off c.S (c.B y) ≤ k
    omega
  have hρ2 : ∀ y, dg (c.B y) = false → c.e y ≤ k := fun y hy => by
    have := arc_en_le c.hS c.hSne (c.hArc y hy)
    have := secLen_lt (S := c.S) (sec c.S (c.B y))
    show en c.S (c.B y) ≤ k
    omega
  obtain ⟨T, hT, h⟩ : ∃ T ≥ c.T0, ∀ t ≥ T, ∀ y, dg (c.B y) = false → stA E t y ≠ St.ws := by
    refine extinction (fun t y => stA E t y = St.ws) (fun t y => stA E t y = St.los)
      (fun y => dg (c.B y) = false)
      (fun y => (dst c.μ (c.σ y) * (k + 1) + c.e y) * (k + 1) + (c.e y - c.o y)) c.T0 ?_ ?_
    · intro t ht z hz h1 h2
      rcases step_cases E t z with he | ⟨p, hm⟩
      · exact absurd (by simp only [stA, he] at h2; exact h2) h1
      · obtain ⟨ob, h3, -⟩ := c.step1 ht hm
        rw [h3] at h2
        rw [R, hz] at h2
        obtain ⟨hp, hcase⟩ := upd_gain ob false _ _ _ _ _ _ _ _ _ (stA E t p) h1
          (fun hdp => by rw [c.win_of_dg ht hdp]; decide) h2
        have hpd : dg (c.B p) = false := by
          cases hdp : dg (c.B p)
          · rfl
          · rw [c.win_of_dg ht hdp] at hp; exact absurd hp (by decide)
        rcases hcase with ⟨hk, hl⟩ | hq
        · rcases (c.k_iff hpd z).1 hk with ⟨hs, he, hlt⟩ | ⟨hL, h0, hσ⟩
          · left
            refine ⟨p, hpd, ?_, hp⟩
            have := off_lt_en (c.hArc z hz)
            apply rank_lt (hρ p hpd); left
            apply rank_lt (hρ2 p hpd); right
            refine ⟨by rw [hs], ?_⟩
            unfold Ctx1.e Ctx1.o at *; omega
          · by_cases hn : nxt c.S (c.σ p) = c.μ
            · right
              refine ⟨hl, fun t' ht' => ?_⟩
              have hw : stA E (t + 1) z ≠ St.los := by rw [h3, R, hz, h2]; decide
              exact c.keep_nonLos_all (by omega) hz ((c.bra_mu_iff z).2 ⟨hσ.trans hn, h0⟩) hw t' ht'
            · left
              refine ⟨p, hpd, ?_, hp⟩
              have hd := dst_nxt c.hS c.hμ (c.σ_mem p) hn
              rw [← hσ] at hd
              have hpos := secLen_pos c.hS (c.σ_mem p)
              apply rank_lt (hρ p hpd); left
              apply rank_lt (hρ2 p hpd); left
              unfold Ctx1.L at *; omega
        · obtain ⟨hs, h5, h6, h7⟩ := (c.ssub_iff hpd hz).1 hq
          left
          refine ⟨p, hpd, ?_, hp⟩
          apply rank_lt (hρ p hpd)
          rcases lt_or_eq_of_le h6 with h8 | h8
          · left; apply rank_lt (hρ2 p hpd); right; exact ⟨by rw [hs], h8⟩
          · right; refine ⟨by rw [hs, h8], ?_⟩
            rcases h7 with h9 | h9
            · have := off_lt_en (c.hArc p hpd); unfold Ctx1.e Ctx1.o at *; omega
            · exact absurd h8 h9
    · intro z hz T
      obtain ⟨d, hd⟩ := c.hd
      have hne : z ≠ d := fun h => by rw [h, hd] at hz; exact Bool.noConfusion hz
      obtain ⟨t, ht, hm⟩ := hE z d hne (max T c.T0)
      refine ⟨t, le_trans (le_max_left _ _) ht, ?_⟩
      obtain ⟨ob, h3, -⟩ := c.step1 (le_trans (le_max_right _ _) ht) hm
      show stA E (t + 1) z ≠ St.ws
      rw [h3, R, hz, hd, c.win_of_dg (le_trans (le_max_right _ _) ht) hd,
        (upd_meet_diag ob _ _ _ _ _ _ _ _).1]
      split_ifs <;> decide
  refine ⟨T, hT, fun t ht y => ?_⟩
  cases hy : dg (c.B y)
  · exact h t ht y hy
  · rw [c.win_of_dg (le_trans hT ht) hy]; decide

/-- **Theorem 4.2, case `r = 1`, in terms of brakets.** -/
theorem main1 (hE : E.WeaklyFair) :
    ∃ T, ∀ t ≥ T, ∀ y, ((c.B y).1 = c.μ → stA E t y ≠ St.los) ∧
      ((c.B y).1 ≠ c.μ → stA E t y = St.los ∧ outA E t y = c.μ) := by
  obtain ⟨Te, hTe, hnt⟩ := c.no_tokens hE
  obtain ⟨d, hd⟩ := c.hd
  have hdμ := c.hDiag d hd
  suffices hp : (∀ t ≥ Te, ∀ y, (((c.B y).1 = c.μ → stA E t y ≠ St.los) ∧
      ((c.B y).1 ≠ c.μ → stA E t y = St.los ∧ outA E t y = c.μ)) →
      (((c.B y).1 = c.μ → stA E (t + 1) y ≠ St.los) ∧
      ((c.B y).1 ≠ c.μ → stA E (t + 1) y = St.los ∧ outA E (t + 1) y = c.μ))) ∧
      (∀ y, ∃ t ≥ Te, ((c.B y).1 = c.μ → stA E t y ≠ St.los) ∧
      ((c.B y).1 ≠ c.μ → stA E t y = St.los ∧ outA E t y = c.μ)) by
    obtain ⟨T, -, hT⟩ := eventually_all (P := fun t y => ((c.B y).1 = c.μ → stA E t y ≠ St.los) ∧
      ((c.B y).1 ≠ c.μ → stA E t y = St.los ∧ outA E t y = c.μ)) Te hp.1 hp.2
    exact ⟨T, hT⟩
  refine ⟨?_, fun y => ?_⟩
  · intro t ht y ⟨h1, h2⟩
    cases hy : dg (c.B y)
    · rcases step_cases E t y with he | ⟨p, hm⟩
      · simp only [stA, outA, he]; exact ⟨h1, h2⟩
      · obtain ⟨ob, h3, h4⟩ := c.step (le_trans hTe ht) hm
        have e1 := congrArg Prod.fst h3; simp only at e1
        rw [R, hy] at e1
        rw [(upd_noTok ob _ _ _ _ _ _ _ _ _ _ _ (hnt t ht y) (hnt t ht p)).1] at e1
        simp only [Bool.not_false, if_true] at e1
        by_cases hdp : dg (c.B p) = true
        · have hsbe : c.sbB y p = true ↔ (c.B y).1 = c.μ := by
            rw [sbB, decide_eq_true_iff, c.hDiag p hdp]
          rw [if_pos hdp] at e1
          refine ⟨fun hμy => ?_, fun hμy => ⟨?_, ?_⟩⟩
          · rw [e1, if_pos (hsbe.2 hμy)]; decide
          · rw [e1, if_neg (fun h => hμy (hsbe.1 h))]
          · rw [h4]
            simp only [outUpd, rd, R, nx, hy, hdp, Bool.not_false, Bool.and_true]
            rw [if_neg (fun h => hnt (t + 1) (by omega) p h.1), if_pos trivial]
            exact c.hDiag p hdp
        · rw [if_neg hdp] at e1
          refine ⟨fun hμy => by rw [e1]; exact h1 hμy, fun hμy => ⟨by rw [e1]; exact (h2 hμy).1, ?_⟩⟩
          rw [h4]
          simp only [outUpd, rd, R, nx, hy, hdp, Bool.not_false, Bool.and_true]
          rw [if_neg (fun h => hnt (t + 1) (by omega) p h.1)]
          simp only [Bool.false_eq_true, if_false]; exact (h2 hμy).2
    · have hw := c.win_of_dg (le_trans hTe (Nat.le_succ_of_le ht)) hy
      refine ⟨fun _ => by rw [hw]; decide, fun h => absurd (c.hDiag y hy) h⟩
  · cases hy : dg (c.B y)
    · have hne : y ≠ d := fun h => by rw [h, hd] at hy; exact Bool.noConfusion hy
      obtain ⟨t, ht, hm⟩ := hE y d hne Te
      obtain ⟨ob, h3, h4⟩ := c.step (le_trans hTe ht) hm
      have hR : c.R y d = nx false true (c.sbB y d) (c.kB y d) (c.kB d y) (c.subB y d)
          (c.subB d y) (c.qB y d) (c.qB d y) := by rw [R, hy, hd]
      rw [hR, c.win_of_dg (le_trans hTe ht) hd] at h3 h4
      have e1 := congrArg Prod.fst h3; have e2 := congrArg Prod.snd h3
      simp only at e1 e2
      rw [(upd_meet_diag ob _ _ _ _ _ _ _ _).1] at e1
      rw [(upd_meet_diag ob _ _ _ _ _ _ _ _).2] at e2
      refine ⟨t + 1, by omega, fun hμy => ?_, fun hμy => ?_⟩
      · rw [e1, if_pos (by rw [sbB, decide_eq_true_iff, hμy, hdμ])]; decide
      · refine ⟨by rw [e1, if_neg (by rw [sbB, decide_eq_true_iff, hdμ]; exact hμy)], ?_⟩
        rw [h4, e2]
        simp [outUpd, rd, nx, hdμ]
    · have hw := c.win_of_dg (le_refl Te |>.trans' hTe |> fun _ => le_trans hTe le_rfl) hy
      exact ⟨Te, le_rfl, fun _ => by rw [hw]; decide, fun h => absurd (c.hDiag y hy) h⟩

end Ctx1

/-! ### From an execution to the stable phase -/

lemma exch_fst_fst (e f : Braket k) : (exch e f).1.1 = e.1 := by unfold exch; split_ifs <;> rfl
lemma exch_snd_fst (e f : Braket k) : (exch e f).2.1 = f.1 := by unfold exch; split_ifs <;> rfl
lemma exch_of_not {e f : Braket k} (h : ¬ Profitable e f) : exch e f = (e, f) := by
  unfold exch; rw [if_neg h]
lemma exch_fst_ne {e f : Braket k} (h : Profitable e f) : (exch e f).1 ≠ e := by
  unfold exch; rw [if_pos h]; intro he
  have := congrArg Prod.snd he; simp only at this
  exact h.ket_ne this.symm
lemma exch_snd_ne {e f : Braket k} (h : Profitable e f) : (exch e f).2 ≠ f := by
  unfold exch; rw [if_pos h]; intro he
  have := congrArg Prod.snd he; simp only at this
  exact h.ket_ne this

section Glue

variable {input : A → Fin k} {E : (tieShare k false).Execution A}

lemma bra_eq_input (h0 : E.config 0 = tsInit input) (t : ℕ) (y : A) : (brA E t y).1 = input y := by
  have := bra_const (E.map (tsToCore false)) t y
  simp only [Execution.map_config, tsToCore, h0, tsInit] at this
  exact this

/-- Diagonal agents are always winners (sequential reading). -/
lemma win_of_diag (h0 : E.config 0 = tsInit input) :
    ∀ t y, dg (brA E t y) = true → stA E t y = St.win := by
  intro t
  induction t with
  | zero => intro y _; simp [stA, h0, tsInit]
  | succ t ih =>
    intro y hy
    rcases step_cases E t y with he | ⟨p, hm⟩
    · simp only [brA, stA, he] at hy ⊢; exact ih y hy
    · obtain ⟨o, h1, -, h3, -⟩ := view E hm
      unfold rAt mkPR at h3
      have e1 := congrArg Prod.fst h3; simp only at e1
      rw [e1]
      rw [h1] at hy
      apply upd_diag o _ _ _ _ _ _ _ _ _ _ _ _ (stA E t y) (stA E t p) hy (ih y)
      · intro hpa
        rw [decide_eq_false_iff_not]
        intro hprof
        have h2 : (brA E t y).1 = (brA E t y).2 := by simpa [dg] using hpa
        have hy' := hy
        unfold exch at hy'; rw [if_pos hprof] at hy'
        have h4 : (brA E t y).1 = (brA E t p).2 := by simpa [dg] using hy'
        exact hprof.ket_ne (h2.symm.trans h4)
      · simp only [decide_eq_false_iff_not]
        have h' : (exch (brA E t y) (brA E t p)).1.1 = (exch (brA E t y) (brA E t p)).1.2 := by
          simpa [dg] using hy
        have : (exch (brA E t y) (brA E t p)).1 =
            ((exch (brA E t y) (brA E t p)).1.1, (exch (brA E t y) (brA E t p)).1.1) :=
          Prod.ext_iff.2 ⟨rfl, h'.symm⟩
        rw [this]; exact not_rssub_diag _ _
      · intro hdb hsb
        simp only [decide_eq_false_iff_not]
        have h' : (exch (brA E t y) (brA E t p)).1.1 = (exch (brA E t y) (brA E t p)).1.2 := by
          simpa [dg] using hy
        have h'' : (exch (brA E t y) (brA E t p)).2.1 = (exch (brA E t y) (brA E t p)).2.2 := by
          simpa [dg] using hdb
        have hx : (exch (brA E t y) (brA E t p)).1 =
            ((exch (brA E t y) (brA E t p)).1.1, (exch (brA E t y) (brA E t p)).1.1) :=
          Prod.ext_iff.2 ⟨rfl, h'.symm⟩
        have hy' : (exch (brA E t y) (brA E t p)).2 =
            ((exch (brA E t y) (brA E t p)).2.1, (exch (brA E t y) (brA E t p)).2.1) :=
          Prod.ext_iff.2 ⟨rfl, h''.symm⟩
        rw [hx, hy']
        intro hq
        exact not_rsub_diag_diag (by simpa using hsb) hq.1

/-- At the end of the last exchange, some agent holds a token. -/
lemma tok_at_T0 {B : Config A (Braket k)} {T0 : ℕ} (hP : ∀ t ≥ T0, ∀ y, brA E t y = B y)
    (hmin : ¬ ∀ t ≥ T0 - 1, ∀ y, brA E t y = B y) (hpos : 0 < T0)
    (hnd : ∀ y, dg (B y) = false) : ∃ y, stA E T0 y = St.ws := by
  push Not at hmin
  obtain ⟨t, ht, y, hy⟩ := hmin
  have htt : t = T0 - 1 := by
    by_contra h; exact hy (hP t (by omega) y)
  subst htt
  obtain ⟨T, rfl⟩ : ∃ T, T0 = T + 1 := ⟨T0 - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hy ⊢
  set a := (E.sched T).1; set b := (E.sched T).2
  have hm : Meet E T a b := Or.inl rfl
  obtain ⟨o, h1, h2, h3, -⟩ := view E hm
  have hprof : Profitable (brA E T a) (brA E T b) := by
    by_contra hnp
    rw [exch_of_not hnp] at h1 h2
    simp only at h1 h2
    by_cases hya : y = a
    · rw [hya, ← h1] at hy; exact hy (hP _ le_rfl a)
    · by_cases hyb : y = b
      · rw [hyb, ← h2] at hy; exact hy (hP _ le_rfl b)
      · have := view_other E hya hyb
        exact hy (by simp only [brA] at hP ⊢; rw [← this]; exact hP _ le_rfl y)
  unfold rAt mkPR at h3
  rw [← h1, ← h2, hP _ le_rfl a, hP _ le_rfl b, hnd, hnd, decide_eq_true hprof] at h3
  rcases upd_exch o _ _ _ _ _ _ _ _ _ (stA E T a) (stA E T b) with h | h
  · exact ⟨a, by rw [← h3] at h; exact h⟩
  · exact ⟨b, by rw [← h3] at h; exact h⟩

/-- The witness invariant (Claim 3 of the paper, made precise): once all agents of color `μ`
have their final braket, some agent of color `μ` is a winner spreader or a loser. -/
lemma witness (h0 : E.config 0 = tsInit input) {B : Config A (Braket k)} {T0 : ℕ}
    (hP : ∀ t ≥ T0, ∀ y, brA E t y = B y) (hnd : ∀ y, dg (B y) = false) (μ : Fin k)
    (hμ : ∃ y, input y = μ) :
    ∃ y, input y = μ ∧ (stA E T0 y = St.ws ∨ stA E T0 y = St.los) := by
  classical
  have hex : ∃ T, ∀ t ≥ T, ∀ y, input y = μ → brA E t y = B y :=
    ⟨T0, fun t ht y _ => hP t ht y⟩
  set Tμ := Nat.find hex with hTμ
  have hspec := Nat.find_spec hex
  have hle : Tμ ≤ T0 := Nat.find_min' hex (fun t ht y _ => hP t ht y)
  -- `Tμ > 0`
  obtain ⟨y0, hy0⟩ := hμ
  have hpos : 0 < Tμ := by
    by_contra h
    have h' : Tμ = 0 := by omega
    have := hspec 0 (by omega) y0 hy0
    have hd := hnd y0
    rw [← this] at hd
    simp [brA, h0, tsInit, dg] at hd
  -- the last change of a braket of color `μ`
  obtain ⟨t1, ht1, y1, hy1, hne⟩ : ∃ t ≥ Tμ - 1, ∃ y, input y = μ ∧ brA E t y ≠ B y := by
    have := Nat.find_min hex (show Tμ - 1 < Tμ by omega)
    push Not at this; exact this
  have ht1' : t1 = Tμ - 1 := by
    by_contra h; exact hne (hspec t1 (by omega) y1 hy1)
  have hfin : ∀ t ≥ t1 + 1, ∀ y, input y = μ → brA E t y = B y := by
    intro t ht y hy; exact hspec t (by omega) y hy
  -- the invariant
  let W := fun t => ∃ y, input y = μ ∧ (stA E t y = St.ws ∨ stA E t y = St.los)
  have hbase : W (t1 + 1) := by
    rcases step_cases E t1 y1 with he | ⟨p, hm⟩
    · exact absurd (by simp only [brA, he] at hfin ⊢; rw [← he]; exact hfin _ le_rfl y1 hy1) hne
    · obtain ⟨o, h1, h2, h3, -⟩ := view E hm
      have hprof : Profitable (brA E t1 y1) (brA E t1 p) := by
        by_contra hnp
        rw [exch_of_not hnp] at h1
        simp only at h1
        exact hne (h1.symm.trans (hfin _ le_rfl y1 hy1))
      unfold rAt mkPR at h3
      have hda : dg (exch (brA E t1 y1) (brA E t1 p)).1 = false := by
        rw [← h1]; exact (congrArg dg (hfin _ le_rfl y1 hy1)).trans (hnd y1)
      have hsb : decide ((exch (brA E t1 y1) (brA E t1 p)).1.1 =
          (exch (brA E t1 y1) (brA E t1 p)).2.1) = decide (input y1 = input p) := by
        rw [exch_fst_fst, exch_snd_fst, bra_eq_input h0, bra_eq_input h0]
      rw [hda, hsb, decide_eq_true hprof] at h3
      have hdb : dg (exch (brA E t1 y1) (brA E t1 p)).2 = true →
          decide (input y1 = input p) = false := by
        intro hd
        simp only [decide_eq_false_iff_not]
        intro he
        rw [← h2, hfin _ le_rfl p (he ▸ hy1), hnd] at hd
        exact Bool.false_ne_true hd
      rcases upd_witness o true _ _ _ _ _ _ _ _ _ _ (stA E t1 y1) (stA E t1 p) hdb (Or.inl rfl)
        with h | ⟨hs, h⟩
      · exact ⟨y1, hy1, by rw [← h3] at h; exact h⟩
      · refine ⟨p, (by simpa [hy1] using hs : μ = input p).symm, by rw [← h3] at h; exact h⟩
  have hstep : ∀ t ≥ t1 + 1, W t → W (t + 1) := by
    rintro t ht ⟨y, hy, hw⟩
    rcases step_cases E t y with he | ⟨p, hm⟩
    · exact ⟨y, hy, by simp only [stA, he]; exact hw⟩
    · obtain ⟨o, h1, h2, h3, -⟩ := view E hm
      have hnp : ¬ Profitable (brA E t y) (brA E t p) := by
        intro hprof
        apply exch_fst_ne hprof
        rw [← h1, hfin _ (by omega) y hy, hfin _ ht y hy]
      rw [exch_of_not hnp] at h1 h2
      unfold rAt mkPR at h3
      rw [exch_of_not hnp, decide_eq_false hnp] at h3
      simp only at h3
      have hda : dg (brA E t y) = false := by rw [hfin t ht y hy]; exact hnd y
      have hsb : decide ((brA E t y).1 = (brA E t p).1) = decide (input y = input p) := by
        rw [bra_eq_input h0, bra_eq_input h0]
      rw [hda, hsb] at h3
      have hdb : dg (brA E t p) = true → decide (input y = input p) = false := by
        intro hd
        simp only [decide_eq_false_iff_not]
        intro he
        rw [hfin t ht p (he ▸ hy), hnd] at hd
        exact Bool.false_ne_true hd
      rcases upd_witness o false false _ _ _ _ _ _ _ _ _ (stA E t y) (stA E t p) hdb (Or.inr hw)
        with h | ⟨hs, h⟩
      · exact ⟨y, hy, by rw [← h3] at h; exact h⟩
      · refine ⟨p, (by simpa [hy] using hs : μ = input p).symm, by rw [← h3] at h; exact h⟩
  exact always_after (W := W) hbase hstep T0 (by omega)

end Glue

lemma arc_of_layer {S G : Finset (Fin k)} (hSG : S ⊆ G) {e : Braket k} (hmem : e ∈ circle G)
    (hnd : dg e = false) : IsArc S e := by
  obtain ⟨h1, h2⟩ := mem_circle.1 hmem
  have he : e = (e.1, nxt G e.1) := Prod.ext rfl h2
  rw [he]
  refine isArc_of_sup hSG h1 (fun h => ?_)
  have : e.1 = e.2 := by rw [h2, h]
  simp [dg, this] at hnd

lemma greedy_anti {x : Fin k → ℕ} {p p' : ℕ} (h : p ≤ p') : greedy x p' ⊆ greedy x p := by
  intro c hc; simp only [greedy, mem_filter, mem_univ, true_and] at hc ⊢; omega

/-- **Theorem 4.2** (Circles_TieSharing, sequential reading of the rules). Under a weakly fair
scheduler, from some time on, forever:
* every agent whose (input) color is in relative majority (`inputCount` maximal) is at
  `winner_spreader` or `winner`, and it outputs its own color;
* every other agent is a `loser`, and it outputs a color in relative majority. -/
theorem tieShare_correct (input : A → Fin k) (E : (tieShare k false).Execution A)
    (h0 : E.config 0 = tsInit input) (hE : E.WeaklyFair) :
    ∃ T, ∀ t ≥ T, ∀ a,
      (inputCount input (input a) = univ.sup (inputCount input) →
        (E.config t a).2.2 ≠ St.los ∧ tsOut (E.config t a) = input a) ∧
      (inputCount input (input a) < univ.sup (inputCount input) →
        (E.config t a).2.2 = St.los ∧
          inputCount input (tsOut (E.config t a)) = univ.sup (inputCount input)) := by
  classical
  set x := inputCount input with hxdef
  set q := univ.sup x with hqdef
  set E2 := E.map (tsToCore false) with hE2
  have h02 : E2.config 0 = initBrakets input := by
    funext a; simp [E2, h0, tsInit, initBrakets, tsToCore]
  obtain ⟨T, hT, hS, hlay, hdiag⟩ := circlesCore_main E2 input h02 (hE.map _)
  set B := E2.config T with hBdef
  have hBT : ∀ t ≥ T, ∀ y, brA E t y = B y := fun t ht y => congrFun (hT t ht) y
  have hbra : ∀ y, (B y).1 = input y := fun y => bra_eq_input h0 T y
  have hmemB : ∀ y, B y ∈ layers x := fun y => by
    rw [← hlay]; exact Multiset.mem_map_of_mem _ (mem_univ_val y)
  have hout : ∀ t a, tsOut (E.config t a) =
      if stA E t a = St.los then outA E t a else input a := by
    intro t a; unfold tsOut; rw [← bra_eq_input h0 t a]
  have hxle : ∀ c, x c ≤ q := fun c => Finset.le_sup (mem_univ c)
  obtain ⟨a0⟩ : Nonempty A := ⟨(E.sched 0).1⟩
  have hxa0 : 1 ≤ x (input a0) := by
    simp only [hxdef, inputCount]
    exact Finset.card_pos.2 ⟨a0, by simp⟩
  have hq1 : 1 ≤ q := le_trans hxa0 (hxle _)
  by_cases hmaj : ∃ μ, IsMajority input μ
  · -- one color in relative majority
    obtain ⟨μ, hμ⟩ := hmaj
    have hxμ : x μ = q := by
      apply le_antisymm (hxle μ) (Finset.sup_le fun c _ => ?_)
      by_cases hc : c = μ
      · rw [hc]
      · exact (hμ.2 c hc).le
    have hmajiff : ∀ c, x c = q ↔ c = μ := by
      intro c; constructor
      · intro h; by_contra hc; have : x c < x μ := hμ.2 c hc; omega
      · rintro rfl; exact hxμ
    have hdg : ∀ y, dg (B y) = true → (B y).1 = μ := by
      intro y hy
      have h1 : (B y).1 = (B y).2 := by simpa [dg] using hy
      have hm := (hdiag (B y).1).1 ⟨y, Prod.ext rfl h1.symm⟩
      by_contra hne
      exact absurd (hm.2 μ (Ne.symm hne)) (not_lt.2 (hμ.2 _ hne).le)
    have hWin := win_of_diag h0
    obtain ⟨d, hd⟩ := (hdiag μ).2 hμ
    have hdd : dg (B d) = true := by simp [dg, B, hd]
    have hfinal : ∀ t a, (((B a).1 = μ → stA E t a ≠ St.los) ∧
        ((B a).1 ≠ μ → stA E t a = St.los ∧ outA E t a = μ)) →
        ((x (input a) = q → (E.config t a).2.2 ≠ St.los ∧ tsOut (E.config t a) = input a) ∧
        (x (input a) < q → (E.config t a).2.2 = St.los ∧ x (tsOut (E.config t a)) = q)) := by
      intro t a ⟨h1, h2⟩
      rw [hbra] at h1 h2
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hst := h1 ((hmajiff _).1 h)
        exact ⟨hst, by rw [hout, if_neg hst]⟩
      · have hne : input a ≠ μ := fun he => by rw [he, hxμ] at h; exact lt_irrefl _ h
        obtain ⟨hl, ho⟩ := h2 hne
        exact ⟨hl, by rw [hout, if_pos hl, ho, hxμ]⟩
    by_cases hnd : ∃ y0, dg (B y0) = false
    · obtain ⟨y0, hy0⟩ := hnd
      -- some other color occurs in a non-trivial greedy set
      have hother : ∀ y, dg (B y) = false → ∃ p < q, B y ∈ circle (greedy x (p + 1)) ∧
          ∃ c' ∈ greedy x (p + 1), c' ≠ μ := by
        intro y hy
        obtain ⟨p, hp, hmem⟩ := mem_layers.1 (hmemB y)
        refine ⟨p, hp, hmem, ?_⟩
        obtain ⟨h1, h2⟩ := mem_circle.1 hmem
        by_cases hg : (B y).1 = μ
        · refine ⟨nxt (greedy x (p + 1)) (B y).1, nxt_mem h1, fun h => ?_⟩
          rw [← h2, ← hg] at h
          simp [dg, h] at hy
        · exact ⟨(B y).1, h1, hg⟩
      obtain ⟨p0, -, -, c0, hc0, hc0μ⟩ := hother y0 hy0
      set p2 := (univ.filter (· ≠ μ)).sup x with hp2
      have hfne : (univ.filter (· ≠ μ)).Nonempty := ⟨c0, by simp [hc0μ]⟩
      obtain ⟨cs, hcs, hxcs⟩ := Finset.exists_mem_eq_sup _ hfne x
      have hcsμ : cs ≠ μ := by simpa using hcs
      set S := greedy x p2 with hSdef
      have hμS : μ ∈ S := by
        simp only [hSdef, greedy, mem_filter, mem_univ, true_and]
        rw [hxμ, show p2 = x cs from hxcs]; exact hxle _
      have hcsS : cs ∈ S := by
        simp only [hSdef, greedy, mem_filter, mem_univ, true_and]; exact le_of_eq hxcs
      have hS2 : TwoPlus S := by
        intro ν hν he
        have := (nxt_eq_self_iff hν).1 he
        rw [this, mem_singleton] at hμS hcsS
        exact hcsμ (hcsS.trans hμS.symm)
      have hArc : ∀ y, dg (B y) = false → IsArc S (B y) := by
        intro y hy
        obtain ⟨p, -, hmem, c', hc', hc'μ⟩ := hother y hy
        refine arc_of_layer (greedy_anti ?_) hmem hy
        have : x c' ≤ p2 := Finset.le_sup (f := x) (by simp [hc'μ])
        simp only [greedy, mem_filter, mem_univ, true_and] at hc'
        omega
      let c1 : Ctx1 E :=
        { S := S, hS := hS2, hSne := ⟨μ, hμS⟩, B := B, hB := hS, T0 := T, hT0 := hBT, μ := μ,
          hμ := hμS, hArc := hArc, hDiag := hdg, hd := ⟨d, hdd⟩, hWin := hWin }
      obtain ⟨T', hT'⟩ := c1.main1 hE
      exact ⟨T', fun t ht a => hfinal t a (hT' t ht a)⟩
    · -- all brakets are diagonal: every agent has color `μ` and is a winner
      push Not at hnd
      have hall : ∀ y, dg (B y) = true := fun y => by simpa using hnd y
      refine ⟨T, fun t ht a => hfinal t a ⟨fun _ => ?_, fun h => absurd (hdg a (hall a)) h⟩⟩
      rw [hWin t a (by rw [hBT t ht a]; exact hall a)]; decide
  · -- several colors in relative majority
    set M := greedy x q with hMdef
    obtain ⟨c0, -, hc0⟩ := Finset.exists_mem_eq_sup univ ⟨input a0, mem_univ _⟩ x
    have hMne : M.Nonempty := ⟨c0, by
      have : q ≤ x c0 := le_of_eq hc0
      simp [hMdef, greedy, this]⟩
    have hM2 : TwoPlus M := by
      intro ν hν he
      have hM := (nxt_eq_self_iff hν).1 he
      apply hmaj
      refine ⟨ν, ?_, fun c hc => ?_⟩
      · have : q ≤ x ν := by simpa [hMdef, greedy] using hν
        show 0 < x ν; omega
      · have hcM : c ∉ M := by rw [hM, mem_singleton]; exact hc
        have h1 : x c < q := by simpa [hMdef, greedy] using hcM
        have h2 : q ≤ x ν := by simpa [hMdef, greedy] using hν
        show x c < x ν; omega
    have hnd : ∀ y, dg (B y) = false := by
      intro y
      by_contra hy
      have h1 : (B y).1 = (B y).2 := by simpa [dg] using hy
      exact hmaj ⟨_, (hdiag (B y).1).1 ⟨y, Prod.ext rfl h1.symm⟩⟩
    have hArc : ∀ y, IsArc M (B y) := by
      intro y
      obtain ⟨p, hp, hmem⟩ := mem_layers.1 (hmemB y)
      exact arc_of_layer (greedy_anti (by omega)) hmem (hnd y)
    have hex : ∃ T', ∀ t ≥ T', ∀ y, brA E t y = B y := ⟨T, hBT⟩
    set T0 := Nat.find hex with hT0def
    have hT0 := Nat.find_spec hex
    have hpos : 0 < T0 := by
      by_contra h
      have h' : T0 = 0 := by omega
      have := hT0 0 (by omega) a0
      have hd := hnd a0
      rw [← this] at hd
      simp [brA, h0, tsInit, dg] at hd
    have hmin : ¬ ∀ t ≥ T0 - 1, ∀ y, brA E t y = B y := Nat.find_min hex (by omega)
    let c : Ctx E :=
      { S := M, hS := hM2, hSne := hMne, B := B, hB := hS, T0 := T0, hT0 := hT0, hArc := hArc }
    have hTop : ∀ μ ∈ c.S, ∃ y, c.B y = (μ, nxt c.S μ) := by
      intro μ hμ
      have hmem : (μ, nxt M μ) ∈ layers x := by
        refine mem_layers.2 ⟨q - 1, by omega, ?_⟩
        rw [Nat.sub_add_cancel hq1]
        exact mem_circle.2 ⟨hμ, rfl⟩
      rw [← hlay] at hmem
      obtain ⟨y, -, hy⟩ := Multiset.mem_map.1 hmem
      exact ⟨y, hy⟩
    have hTok := tok_at_T0 hT0 hmin hpos hnd
    have hWit : ∀ μ ∈ c.S, ∃ y, c.σ y = μ ∧ c.o y = 0 ∧
        (stA E c.T0 y = St.ws ∨ stA E c.T0 y = St.los) := by
      intro μ hμ
      have hxμ : q ≤ x μ := by simpa [c, hMdef, greedy] using hμ
      have hex' : ∃ y, input y = μ := by
        have : 0 < x μ := by omega
        simp only [hxdef, inputCount, Finset.card_pos] at this
        obtain ⟨y, hy⟩ := this; exact ⟨y, by simpa using hy⟩
      obtain ⟨y, hy, hw⟩ := witness h0 hT0 hnd μ hex'
      have hb : (c.B y).1 = μ := (hbra y).trans hy
      have hσ : c.σ y = μ := by
        show secOf M (B y).1 = μ; rw [hbra, hy]; exact secOf_of_mem hμ
      refine ⟨y, hσ, ?_, hw⟩
      show dst (sec M (B y)) (B y).1 = 0
      rw [show sec M (B y) = μ from hσ, hbra, hy, dst_self]
    obtain ⟨T', hT'⟩ := c.main2 hTop hE hTok hWit
    refine ⟨T', fun t ht a => ?_⟩
    obtain ⟨h1, h2⟩ := hT' t ht a
    have ho : c.o a = 0 ↔ x (input a) = q := by
      have hb : (c.B a).1 = input a := hbra a
      constructor
      · intro h
        have h' : secOf M (input a) = input a := by
          have : dst (secOf M (c.B a).1) (c.B a).1 = 0 := h
          rw [hb] at this; exact dst_eq_zero this
        have hm := secOf_mem hMne (input a)
        rw [h'] at hm
        have : q ≤ x (input a) := by simpa [hMdef, greedy] using hm
        exact le_antisymm (hxle _) this
      · intro h
        have hm : input a ∈ M := by simp [hMdef, greedy, h]
        show dst (secOf M (c.B a).1) (c.B a).1 = 0
        rw [hb, secOf_of_mem hm, dst_self]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hst := h1 (ho.2 h)
      exact ⟨hst, by rw [hout, if_neg hst]⟩
    · have hne : c.o a ≠ 0 := fun h' => by rw [ho.1 h'] at h; exact lt_irrefl _ h
      obtain ⟨hl, hm⟩ := h2 hne
      refine ⟨hl, ?_⟩
      rw [hout, if_pos hl]
      have : q ≤ x (outA E t a) := by simpa [c, hMdef, greedy] using hm
      exact le_antisymm (hxle _) this

end RankingOpinions
