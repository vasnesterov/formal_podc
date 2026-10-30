import Papers.PODC2023.PPDoubleExpThresholds.Walk
import Mathlib.Tactic.IntervalCases

/-!
# Lemma 12(b): `Large(x)` on `(i−1)`-proper configurations (levels `i ≥ 2`)
-/

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

set_option hygiene false in
/-- Discharge `(prog n).instr p pc = some ins` using the local code listing `hcode`. -/
local macro "ins" : tactic => `(tactic| (rw [Program.instr, hcode]; try rfl))

/-- The invariant of `Large(x)` (registers at each instruction) on an `(i−1)`-proper start. -/
def LBInv (C : Reg n → ℕ) (i : ℕ) (k : Fin 4) (pc : ℕ) (D : Reg n → ℕ) : Prop :=
  match pc with
  | 0 => D = C
  | 1 => D = C
  | 4 => ∃ c, WalkSt C i k c c D
  | 5 => ∃ c, WalkSt C i k c c D
  | 6 => ∃ c, WalkSt C i k c c D
  | 7 => ∃ c, WalkSt C i k c c D ∧ c < C (reg n i k)
  | 8 => ∃ c, WalkSt C i k (c + 1) c D
  | 9 => ∃ c, WalkSt C i k (c + 1) ((c + 1) % N i) D ∧ c < N i
  | 10 => ∃ c, WalkSt C i k (c + 1) ((c + 1) % N i) D ∧ c < N i ∧ D (reg n (i - 1) 0) = 0
  | 11 => WalkSt C i k (N i) 0 D
  | 12 => D = lg C (reg n i k) (reg n i (bar k)) (N i) ∧ N i ≤ C (reg n i k)
  | 14 => ∃ c, WalkSt C i k c c D
  | 15 => ∃ c, WalkSt C i k c c D
  | 16 => ∃ c, WalkSt C i k c c D ∧ D (reg n (i - 1) 0) = 0
  | 17 => D = C
  | 19 => ∃ c, WalkSt C i k c c D ∧ 0 < c
  | 20 => ∃ c, WalkSt C i k (c + 1) (c + 1) D
  | 21 => ∃ c, WalkSt C i k c (c + 1) D
  | 22 => ∃ c, WalkSt C i k c c D
  | 23 => ∃ c, WalkSt C i k c c D
  | _ => False

theorem LBInv.lt {C : Reg n → ℕ} {i : ℕ} {k : Fin 4} {pc : ℕ} {D : Reg n → ℕ}
    (h : LBInv C i k pc D) : pc < 24 := by
  unfold LBInv at h; split at h <;> first | omega | exact h.elim

section

variable {i : ℕ} (hi : 2 ≤ i) (hin : i ≤ n)
include hi hin

omit hi hin in
theorem ctr_succ_mod_ne {c : ℕ} (hc : c < N i) (h : (c + 1) % N i ≠ 0) : (c + 1) % N i = c + 1 := by
  apply Nat.mod_eq_of_lt
  by_contra h'
  exact h (by rw [show c + 1 = N i by omega, Nat.mod_self])

/-- **Lemma 12(b)** for levels `i ≥ 2`. -/
theorem large_B (hAP : APA n (i - 2)) (hZ : ZeroB n (i - 1)) (hIA : IncrA n (i - 1)) :
    LargeB n i := by
  intro k C OF hC
  have hcode := code_large n hi k
  have hi1 : 1 ≤ i - 1 := by omega
  have hin1 : i - 1 ≤ n := by omega
  have hii : i - 1 + 1 = i := by omega
  have hNi := N_pos (i := i) (by omega)
  have hne := reg_ne_bar (by omega) hin k
  -- callee specifications on weakly proper configurations
  have zA := fun k' D OF (hD : WProper D (i - 1)) => zeroA_of_B hi1 hin1 hZ k' (C := D) OF hD
  have iA := fun bx by' D OF (hD : WProper D (i - 1)) => hIA bx by' D OF hD
  have pA := fun D OF (hD : Proper D (i - 2)) => hAP D OF (.inl hD)
  have hwC : WProper C (i - 1) := hC.wproper hi1
  obtain ⟨-, cx0, -, cy0, -⟩ := (proper_succ_iff hi1).1 hC
  -- the invariant
  let I : Loc (Reg n) → Prop := fun a => a.OF = OF ∧ LBInv C i k a.pc a.C
  have hIinv : ∀ a a', I a → (prog n).AStep (.large i k) a a' → I a' := by
    rintro ⟨pc, D, OF₁⟩ a' ⟨rfl, hI⟩ hs
    rw [astep_iff] at hs
    have hlt := hI.lt
    simp only at hlt hI ⊢
    interval_cases pc <;> simp only [LBInv] at hI <;>
      simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero] at hs
    · -- 0: Zero(x_{i-1}) on C
      subst hI
      obtain ⟨D', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, hD', rfl⟩ := ((zA 0 D OF₁ hwC).1 _ _ _).1 hr
      rw [hD']
      refine ⟨rfl, ?_⟩
      simp only [cx0, decide_true, Bool.cond_true, LBInv]
    · -- 1: Zero(y_{i-1}) on C
      subst hI
      obtain ⟨D', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, hD', rfl⟩ := ((zA 2 D OF₁ hwC).1 _ _ _).1 hr
      rw [hD']
      refine ⟨rfl, ?_⟩
      simp only [cy0, decide_true, Bool.cond_true, LBInv]
      exact ⟨0, WalkSt.start hi hin hC⟩
    · subst hs; exact ⟨rfl, hI⟩
    · -- 5: AssertProper(i-2)
      obtain ⟨c, hc⟩ := hI
      obtain ⟨D', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, hD', -⟩ := ((pA D OF₁ (hc.1.1.mono (by omega))).1 _ _ _).1 hr
      rw [hD']
      simp only [Bool.cond_self]
      exact ⟨rfl, c, hc⟩
    · -- 6: detect x
      obtain ⟨c, hc⟩ := hI
      rcases hs with ⟨hx, rfl⟩ | rfl
      · refine ⟨rfl, c, hc, ?_⟩
        rw [hc.x hi hin] at hx; omega
      · exact ⟨rfl, c, hc⟩
    · -- 7: move x x̄
      obtain ⟨c, hc, hlt⟩ := hI
      obtain ⟨-, rfl⟩ := hs
      exact ⟨rfl, c, hc.move hi hin hlt⟩
    · -- 8: IncrPair(x_{i-1}, y_{i-1})
      obtain ⟨c, hc⟩ := hI
      obtain ⟨D', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, -, hw, hoff, hctr⟩ := ((iA false false D OF₁ hc.1).1 _ _ _).1 hr
      simp only [Bool.cond_self]
      refine ⟨rfl, c, hc.change hi hin hw hoff ?_, hc.e_lt hi hin⟩
      rw [show kx false = 0 from rfl, show ky false = 2 from rfl] at hctr
      rw [hctr, hc.2.1, hii]
    · -- 9: Zero(x_{i-1})
      obtain ⟨c, hc, hcN⟩ := hI
      obtain ⟨D', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, hD', rfl⟩ := ((zA 0 D OF₁ hc.1).1 _ _ _).1 hr
      rw [hD']
      refine ⟨rfl, ?_⟩
      by_cases h0 : D (reg n (i - 1) 0) = 0
      · simp only [h0, decide_true, Bool.cond_true, LBInv]; exact ⟨c, hc, hcN, trivial⟩
      · simp only [h0, decide_false, Bool.cond_false, LBInv]
        have hne0 : (c + 1) % N i ≠ 0 := by
          rw [← hc.2.1, Ne, WProper.ctr_eq_zero]; tauto
        rw [ctr_succ_mod_ne hcN hne0] at hc
        exact ⟨c + 1, hc⟩
    · -- 10: Zero(y_{i-1})
      obtain ⟨c, hc, hcN, hx0⟩ := hI
      obtain ⟨D', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, hD', rfl⟩ := ((zA 2 D OF₁ hc.1).1 _ _ _).1 hr
      rw [hD']
      refine ⟨rfl, ?_⟩
      by_cases h0 : D (reg n (i - 1) 2) = 0
      · simp only [h0, decide_true, Bool.cond_true, LBInv]
        have he : (c + 1) % N i = 0 := by rw [← hc.2.1, WProper.ctr_eq_zero]; exact ⟨hx0, h0⟩
        have hcN' : c + 1 = N i := by
          by_contra h'
          rw [Nat.mod_eq_of_lt (by omega)] at he; omega
        rw [he, hcN'] at hc
        exact hc
      · simp only [h0, decide_false, Bool.cond_false, LBInv]
        have hne0 : (c + 1) % N i ≠ 0 := by
          rw [← hc.2.1, Ne, WProper.ctr_eq_zero]; tauto
        rw [ctr_succ_mod_ne hcN hne0] at hc
        exact ⟨c + 1, hc⟩
    · -- 11: swap
      subst hs
      exact ⟨rfl, hI.final hi hin hC, hI.2.2.2⟩
    · -- 14: goto 23
      subst hs; exact ⟨rfl, hI⟩
    · -- 15: Zero(x_{i-1})
      obtain ⟨c, hc⟩ := hI
      obtain ⟨D', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, hD', rfl⟩ := ((zA 0 D OF₁ hc.1).1 _ _ _).1 hr
      rw [hD']
      refine ⟨rfl, ?_⟩
      by_cases h0 : D (reg n (i - 1) 0) = 0
      · simp only [h0, decide_true, Bool.cond_true, LBInv]; exact ⟨c, hc, trivial⟩
      · simp only [h0, decide_false, Bool.cond_false, LBInv]
        refine ⟨c, hc, Nat.pos_of_ne_zero fun h => h0 ?_⟩
        exact (WProper.ctr_eq_zero.1 (hc.2.1.trans h)).1
    · -- 16: Zero(y_{i-1})
      obtain ⟨c, hc, hx0⟩ := hI
      obtain ⟨D', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, hD', rfl⟩ := ((zA 2 D OF₁ hc.1).1 _ _ _).1 hr
      rw [hD']
      refine ⟨rfl, ?_⟩
      by_cases h0 : D (reg n (i - 1) 2) = 0
      · simp only [h0, decide_true, Bool.cond_true, LBInv]
        have hc0 : c = 0 := by rw [← hc.2.1, WProper.ctr_eq_zero]; exact ⟨hx0, h0⟩
        subst hc0
        exact hc.eq_start hi hin hC
      · simp only [h0, decide_false, Bool.cond_false, LBInv]
        refine ⟨c, hc, Nat.pos_of_ne_zero fun h => h0 ?_⟩
        exact (WProper.ctr_eq_zero.1 (hc.2.1.trans h)).2
    · -- 19: detect x̄
      obtain ⟨c, hc, hc0⟩ := hI
      rcases hs with ⟨-, rfl⟩ | rfl
      · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        exact ⟨rfl, c', hc⟩
      · exact ⟨rfl, c, hc⟩
    · -- 20: move x̄ x
      obtain ⟨c, hc⟩ := hI
      obtain ⟨-, rfl⟩ := hs
      exact ⟨rfl, c, hc.move_back hi hin⟩
    · -- 21: IncrPair(x̄_{i-1}, ȳ_{i-1})
      obtain ⟨c, hc⟩ := hI
      obtain ⟨D', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, -, hw, hoff, hctr⟩ := ((iA true true D OF₁ hc.1).1 _ _ _).1 hr
      simp only [Bool.cond_self]
      refine ⟨rfl, c, hc.change hi hin hw hoff ?_⟩
      rw [show kx true = 1 from rfl, show ky true = 3 from rfl, hii] at hctr
      have b1 := hc.1.ctr_bar
      have b2 := hw.ctr_bar
      have he := hc.e_lt hi hin
      rw [hii, hc.2.1] at b1
      rw [hii] at b2
      have : ctr D (i - 1) 1 3 + 1 < N i := by omega
      rw [Nat.mod_eq_of_lt this] at hctr
      dsimp only
      omega
    · subst hs; exact ⟨rfl, hI⟩
    · subst hs; exact ⟨rfl, hI⟩
  have hreach : ∀ a, (prog n).AReach (.large i k) ⟨0, C, OF⟩ a → I a :=
    fun a ha => AReach.inv hIinv ha ⟨rfl, rfl⟩
  -- existence of returns of the callees
  have zret : ∀ k' D OF₁, WProper D (i - 1) → (prog n).Returns (.zero (i - 1) k') D OF₁ D OF₁
      (decide (D (reg n (i - 1) k') = 0)) := fun k' D OF₁ hD =>
    ((zA k' D OF₁ hD).1 _ _ _).2 ⟨rfl, rfl, rfl⟩
  have pret : ∀ D OF₁, Proper D (i - 2) → (prog n).Returns (.assertProper (i - 2)) D OF₁ D OF₁ false :=
    fun D OF₁ hD => ((pA D OF₁ hD).1 _ _ _).2 ⟨rfl, rfl, rfl⟩
  have iret : ∀ bx by' D OF₁, WProper D (i - 1) → ∃ D', (prog n).Returns (.incrPair (i - 1) bx by')
      D OF₁ D' OF₁ false ∧ WProper D' (i - 1) ∧ Off D D' (i - 1) ∧
      ctr D' (i - 1) (kx bx) (ky by') = (ctr D (i - 1) (kx bx) (ky by') + 1) % N i := by
    intro bx by' D OF₁ hD
    obtain ⟨hR, hnr, ht⟩ := iA bx by' D OF₁ hD
    rcases ht.returns_or_restarts with ⟨D', OF', b, hr⟩ | hr
    · obtain ⟨rfl, rfl, hw, hoff, hctr⟩ := (hR _ _ _).1 hr
      exact ⟨D', hr, hw, hoff, hii ▸ hctr⟩
    · exact absurd hr hnr
  -- paths
  have pStart : (prog n).AReach (.large i k) ⟨0, C, OF⟩ ⟨4, C, OF⟩ := by
    have h1 := zret 0 C OF hwC; have h2 := zret 2 C OF hwC
    rw [cx0, decide_eq_true rfl] at h1; rw [cy0, decide_eq_true rfl] at h2
    exact .head (.call (by ins) h1) (.single (.call (by ins) h2))
  -- one iteration: the walk goes up
  have pHead : ∀ c D, WalkSt C i k c c D → (prog n).AReach (.large i k) ⟨4, D, OF⟩ ⟨6, D, OF⟩ :=
    fun c D hc => .head (.goto (by ins)) (.single (.call (by ins) (pret D OF (hc.1.1.mono (by omega)))))
  have pA8 : ∀ c D, WalkSt C i k c c D → c < C (reg n i k) → ∃ D', WalkSt C i k (c + 1) ((c + 1) % N i) D' ∧
      (prog n).AReach (.large i k) ⟨4, D, OF⟩ ⟨9, D', OF⟩ := by
    intro c D hc hcx
    have hx : 0 < D (reg n i k) := by rw [hc.x hi hin]; omega
    have hc' := hc.move hi hin hcx
    obtain ⟨D', hr, hw, hoff, hctr⟩ := iret false false _ OF hc'.1
    refine ⟨D', hc'.change hi hin hw hoff (by rw [show kx false = 0 from rfl, show ky false = 2 from rfl] at hctr; rw [hctr, hc'.2.1]), ?_⟩
    exact (pHead c D hc).trans (.head (.detectT (by ins) hx) (.head (.move (by ins) hx)
      (.single (.call (by ins) hr))))
  have pUp : ∀ c D, WalkSt C i k c c D → c < C (reg n i k) → c + 1 < N i → ∃ D', WalkSt C i k (c + 1) (c + 1) D' ∧
      (prog n).AReach (.large i k) ⟨4, D, OF⟩ ⟨4, D', OF⟩ := by
    intro c D hc hcx hcN
    obtain ⟨D', hD', hp⟩ := pA8 c D hc hcx
    rw [Nat.mod_eq_of_lt hcN] at hD'
    refine ⟨D', hD', hp.trans ?_⟩
    have hz := zret 0 D' OF hD'.1
    have hne0 : ¬ (D' (reg n (i - 1) 0) = 0 ∧ D' (reg n (i - 1) 2) = 0) := by
      rw [← WProper.ctr_eq_zero, hD'.2.1]; omega
    have tail : (prog n).AReach (.large i k) ⟨14, D', OF⟩ ⟨4, D', OF⟩ :=
      .head (.goto (by ins)) (.single (.goto (by ins)))
    by_cases h0 : D' (reg n (i - 1) 0) = 0
    · have hz2 := zret 2 D' OF hD'.1
      have h2 : D' (reg n (i - 1) 2) ≠ 0 := fun h => hne0 ⟨h0, h⟩
      rw [h0, decide_eq_true rfl] at hz
      rw [decide_eq_false h2] at hz2
      exact .head (.call (by ins) hz) (.head (.call (by ins) hz2) tail)
    · rw [decide_eq_false h0] at hz
      exact .head (.call (by ins) hz) tail
  have pUps : N i ≤ C (reg n i k) → ∀ c, c < N i → ∃ D, WalkSt C i k c c D ∧
      (prog n).AReach (.large i k) ⟨0, C, OF⟩ ⟨4, D, OF⟩ := by
    intro hx c hc
    induction c with
    | zero => exact ⟨C, WalkSt.start hi hin hC, pStart⟩
    | succ c ih =>
      obtain ⟨D, hD, hp⟩ := ih (by omega)
      obtain ⟨D', hD', hp'⟩ := pUp c D hD (by omega) hc
      exact ⟨D', hD', hp.trans hp'⟩
  have pTop : ∀ D, WalkSt C i k (N i - 1) (N i - 1) D → N i ≤ C (reg n i k) →
      (prog n).AReach (.large i k) ⟨4, D, OF⟩ ⟨12, lg C (reg n i k) (reg n i (bar k)) (N i), OF⟩ := by
    intro D hD hx
    obtain ⟨D', hD', hp⟩ := pA8 _ D hD (by omega)
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self] at hD'
    obtain ⟨h0, h2⟩ := WProper.ctr_eq_zero.1 hD'.2.1
    have hz := zret 0 D' OF hD'.1; have hz2 := zret 2 D' OF hD'.1
    rw [h0, decide_eq_true rfl] at hz; rw [h2, decide_eq_true rfl] at hz2
    refine hp.trans (.head (.call (by ins) hz) (.head (.call (by ins) hz2) ?_))
    rw [← hD'.final hi hin hC]
    exact .single (.swap (by ins))
  -- the walk goes down to `C` and returns `false`
  have pDown : ∀ c D, WalkSt C i k c c D → (prog n).AReach (.large i k) ⟨4, D, OF⟩ ⟨17, C, OF⟩ := by
    intro c
    induction c with
    | zero =>
      intro D hD
      obtain rfl := hD.eq_start hi hin hC
      have hz := zret 0 D OF hwC; have hz2 := zret 2 D OF hwC
      rw [cx0, decide_eq_true rfl] at hz; rw [cy0, decide_eq_true rfl] at hz2
      exact (pHead 0 D hD).trans (.head (.detectF (by ins)) (.head (.call (by ins) hz)
        (.single (.call (by ins) hz2))))
    | succ c ih =>
      intro D hD
      have hne0 : ¬ (D (reg n (i - 1) 0) = 0 ∧ D (reg n (i - 1) 2) = 0) := by
        rw [← WProper.ctr_eq_zero, hD.2.1]; omega
      have hxb : 0 < D (reg n i (bar k)) := by rw [hD.xb hi hin]; omega
      have hD20 := hD.move_back hi hin
      obtain ⟨D', hr, hw, hoff, hctr⟩ := iret true true _ OF hD20.1
      have hD' : WalkSt C i k c c D' := by
        refine hD20.change hi hin hw hoff ?_
        rw [show kx true = 1 from rfl, show ky true = 3 from rfl] at hctr
        have b1 := hD20.1.ctr_bar
        have b2 := hw.ctr_bar
        have he := hD20.e_lt hi hin
        rw [hii, hD20.2.1] at b1
        rw [hii] at b2
        have : ctr (mv D (reg n i (bar k)) (reg n i k)) (i - 1) 1 3 + 1 < N i := by omega
        rw [Nat.mod_eq_of_lt this] at hctr
        omega
      have p19 : (prog n).AReach (.large i k) ⟨19, D, OF⟩ ⟨4, D', OF⟩ :=
        .head (.detectT (by ins) hxb) (.head (.move (by ins) hxb) (.head (.call (by ins) hr)
          (.head (.goto (by ins)) (.single (.goto (by ins))))))
      have hz := zret 0 D OF hD.1
      refine (pHead _ D hD).trans (.head (.detectF (by ins)) ?_)
      refine Relation.ReflTransGen.trans ?_ ((p19.trans (ih D' hD')))
      by_cases h0 : D (reg n (i - 1) 0) = 0
      · have hz2 := zret 2 D OF hD.1
        have h2 : D (reg n (i - 1) 2) ≠ 0 := fun h => hne0 ⟨h0, h⟩
        rw [h0, decide_eq_true rfl] at hz
        rw [decide_eq_false h2] at hz2
        exact .head (.call (by ins) hz) (.single (.call (by ins) hz2))
      · rw [decide_eq_false h0] at hz
        exact .single (.call (by ins) hz)
  -- callees never restart and terminate
  have callSpec : ∀ a, (prog n).AReach (.large i k) ⟨0, C, OF⟩ a → ∀ q tT tF,
      (prog n).instr (.large i k) a.pc = some (.call q tT tF) →
      ¬ (prog n).Restarts q a.C a.OF ∧ (prog n).Terminates q a.C a.OF := by
    intro a ha q tT tF hq
    obtain ⟨hOF, hI⟩ := hreach a ha
    obtain ⟨pc, D, OF₁⟩ := a
    have hlt := hI.lt
    simp only at hlt hI hq hOF ⊢
    interval_cases pc <;> simp only [LBInv] at hI <;>
      simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Instr.call.injEq] at hq <;> (try simp at hq) <;>
      obtain ⟨rfl, -, -⟩ := hq
    · subst hI; exact ⟨(zA 0 _ OF₁ hwC).2.1, (zA 0 _ OF₁ hwC).2.2⟩
    · subst hI; exact ⟨(zA 2 _ OF₁ hwC).2.1, (zA 2 _ OF₁ hwC).2.2⟩
    · obtain ⟨c, hc⟩ := hI
      exact ⟨(pA D OF₁ (hc.1.1.mono (by omega))).2.1, (pA D OF₁ (hc.1.1.mono (by omega))).2.2⟩
    · obtain ⟨c, hc⟩ := hI; exact ⟨(iA _ _ D OF₁ hc.1).2.1, (iA _ _ D OF₁ hc.1).2.2⟩
    · obtain ⟨c, hc, -⟩ := hI; exact ⟨(zA 0 D OF₁ hc.1).2.1, (zA 0 D OF₁ hc.1).2.2⟩
    · obtain ⟨c, hc, -⟩ := hI; exact ⟨(zA 2 D OF₁ hc.1).2.1, (zA 2 D OF₁ hc.1).2.2⟩
    · obtain ⟨c, hc⟩ := hI; exact ⟨(zA 0 D OF₁ hc.1).2.1, (zA 0 D OF₁ hc.1).2.2⟩
    · obtain ⟨c, hc, -⟩ := hI; exact ⟨(zA 2 D OF₁ hc.1).2.1, (zA 2 D OF₁ hc.1).2.2⟩
    · obtain ⟨c, hc⟩ := hI; exact ⟨(iA _ _ D OF₁ hc.1).2.1, (iA _ _ D OF₁ hc.1).2.2⟩
  refine ⟨fun C' OF' b => ⟨fun h => ?_, ?_⟩, fun h => ?_, ?_⟩
  · -- the returns
    obtain ⟨a, ha, rfl, rfl, hb⟩ := returns_iff.1 h
    obtain ⟨hOF, hI⟩ := hreach a ha
    refine ⟨hOF, ?_⟩
    obtain ⟨pc, D, OF₁⟩ := a
    have hlt := hI.lt
    simp only at hlt hI hb ⊢
    interval_cases pc <;> simp only [LBInv] at hI <;>
      simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Instr.ret.injEq] at hb <;> (try simp at hb)
    · exact .inr ⟨hb, hI.2, hI.1⟩
    · exact .inl ⟨hb, hI⟩
  · rintro ⟨hOF', ⟨hb, hC'⟩ | ⟨hb, hx, hC'⟩⟩ <;> rw [hOF', hb, hC']
    · exact returns_iff.2 ⟨_, pStart.trans (pDown 0 C (WalkSt.start hi hin hC)), rfl, rfl, by ins⟩
    · obtain ⟨D, hD, hp⟩ := pUps hx (N i - 1) (by omega)
      exact returns_iff.2 ⟨_, hp.trans (pTop D hD hx), rfl, rfl, by ins⟩
  · -- no restarts
    obtain ⟨a, ha, hr⟩ := restarts_iff.1 h
    rcases hr with hr | ⟨q, tT, tF, hq, hr⟩
    · obtain ⟨-, hI⟩ := hreach a ha
      obtain ⟨pc, D, OF₁⟩ := a
      have hlt := hI.lt
      simp only at hlt hI hr
      interval_cases pc <;> simp only [LBInv] at hI <;>
        simp [Program.instr, hcode] at hr
    · exact (callSpec a ha q tT tF hq).1 hr
  · -- termination
    refine terminates_of (fun a ha q tT tF hq => (callSpec a ha q tT tF hq).2) (fun a ha => ?_)
    let T : Loc (Reg n) → Prop := fun a => a.pc = 4 ∨ a.pc = 23 ∨
      ∃ b, (prog n).instr (.large i k) a.pc = some (.ret b)
    have hT : ∀ a, (prog n).AReach (.large i k) ⟨0, C, OF⟩ a → T a ∨
        ∃ a', (prog n).AStep (.large i k) a a' ∧ 24 - a'.pc < 24 - a.pc := by
      intro a ha
      obtain ⟨hOF, hI⟩ := hreach a ha
      obtain ⟨pc, D, OF₁⟩ := a
      have hlt := hI.lt
      simp only at hlt hI hOF ⊢
      interval_cases pc <;> simp only [LBInv] at hI
      · subst hI; exact .inr ⟨_, .call (by ins) (zret 0 D OF₁ hwC), by simp [cx0]⟩
      · subst hI; exact .inr ⟨_, .call (by ins) (zret 2 D OF₁ hwC), by simp [cy0]⟩
      · exact .inl (.inl rfl)
      · obtain ⟨c, hc⟩ := hI
        exact .inr ⟨_, .call (by ins) (pret D OF₁ (hc.1.1.mono (by omega))), by simp⟩
      · exact .inr ⟨_, .detectF (by ins), by simp⟩
      · obtain ⟨c, hc, hcx⟩ := hI
        have hx : 0 < D (reg n i k) := by rw [hc.x hi hin]; omega
        exact .inr ⟨_, .move (by ins) hx, by simp⟩
      · obtain ⟨c, hc⟩ := hI
        obtain ⟨D', hr, -⟩ := iret false false D OF₁ hc.1
        exact .inr ⟨_, .call (by ins) hr, by simp⟩
      · obtain ⟨c, hc, -⟩ := hI
        refine .inr ⟨_, .call (by ins) (zret 0 D OF₁ hc.1), ?_⟩
        cases decide (D (reg n (i - 1) 0) = 0) <;> simp
      · obtain ⟨c, hc, -⟩ := hI
        refine .inr ⟨_, .call (by ins) (zret 2 D OF₁ hc.1), ?_⟩
        cases decide (D (reg n (i - 1) 2) = 0) <;> simp
      · exact .inr ⟨_, .swap (by ins), by simp⟩
      · exact .inl (.inr (.inr ⟨true, by ins⟩))
      · exact .inr ⟨_, .goto (by ins), by simp⟩
      · obtain ⟨c, hc⟩ := hI
        refine .inr ⟨_, .call (by ins) (zret 0 D OF₁ hc.1), ?_⟩
        cases decide (D (reg n (i - 1) 0) = 0) <;> simp
      · obtain ⟨c, hc, -⟩ := hI
        refine .inr ⟨_, .call (by ins) (zret 2 D OF₁ hc.1), ?_⟩
        cases decide (D (reg n (i - 1) 2) = 0) <;> simp
      · exact .inl (.inr (.inr ⟨false, by ins⟩))
      · exact .inr ⟨_, .detectF (by ins), by simp⟩
      · obtain ⟨c, hc⟩ := hI
        have hxb : 0 < D (reg n i (bar k)) := by rw [hc.xb hi hin]; omega
        exact .inr ⟨_, .move (by ins) hxb, by simp⟩
      · obtain ⟨c, hc⟩ := hI
        obtain ⟨D', hr, -⟩ := iret true true D OF₁ hc.1
        exact .inr ⟨_, .call (by ins) hr, by simp⟩
      · exact .inr ⟨_, .goto (by ins), by simp⟩
      · exact .inl (.inr (.inl rfl))
    obtain ⟨a', haa', hT'⟩ := exists_target_of_rank (fun a => 24 - a.pc) hT a ha
    have ha' := ha.trans haa'
    rcases hT' with h4 | h23 | ⟨b, hb⟩
    · obtain ⟨hOF, hI⟩ := hreach a' ha'
      obtain ⟨pc, D, OF₁⟩ := a'
      simp only at h4 hOF hI; subst h4 hOF
      obtain ⟨c, hc⟩ := hI
      exact ⟨_, haa'.trans (pDown c D hc), .inl ⟨false, by ins⟩⟩
    · obtain ⟨hOF, hI⟩ := hreach a' ha'
      obtain ⟨pc, D, OF₁⟩ := a'
      simp only at h23 hOF hI; subst h23 hOF
      obtain ⟨c, hc⟩ := hI
      exact ⟨_, haa'.trans (.head (.goto (by ins)) (pDown c D hc)), .inl ⟨false, by ins⟩⟩
    · exact ⟨a', haa', .inl ⟨b, hb⟩⟩

end

end Podc.PPDoubleExpThresholds
