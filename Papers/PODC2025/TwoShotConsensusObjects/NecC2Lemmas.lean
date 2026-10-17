import Papers.PODC2025.TwoShotConsensusObjects.NecC15

/-!
# Necessity — lemmas for Proposition 2 (class `C₂`)

Setting: at the critical configuration, `fg` and `gf` are indistinguishable to both processes.

* `KSetup.c34`: Lemma 5 with roles `a` (runs solo first after `fg`, second operation `cₐ`) and
  `b` (runs solo next, second operation `c_b`); for `a = p₀` this gives properties (3), (4) of
  `C₂`, for `a = p₁` properties (5), (6).
* `KSetup.edge_dist`: if, from `fg`, the processes can reach (without touching the copy) a
  configuration where `p₀` is poised on `c` and `p₁` on `c'`, then the four pairs of property (2)
  are distinguishable to both processes.
-/

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

variable {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] {R : ιR → ObjSpec} {O : ObjSpec}
  {A : Alg 2 (withRW (ιS := ιS) R O)}

lemma mem_of_noAcc {C : Cfg A} {γ : List (Ev 2)} (hγ : CrashFree γ) {i : ιR ⊕ ιS}
    (hno : ∀ p, accCount C γ p i = 0) : (run C γ).mem i = C.mem i := by
  induction γ generalizing C with
  | nil => rfl
  | cons e γ ih =>
    have hγ' : CrashFree γ := fun q hq => hγ q (by simp [hq])
    rw [run_cons, ih hγ' (fun p => by have := hno p; rw [accCount_cons] at this; omega)]
    rcases e with r | r
    · have hr : objOf C r ≠ some i := by
        intro hr; have := hno r; rw [accCount_cons] at this; simp [hr] at this
      simp only [Cfg.next]
      rcases hact : A.act (C.loc r) with ⟨j, o, κ⟩ | v
      · rw [stepP_of_access C hact]
        have : i ≠ j := by rintro rfl; exact hr ((objOf_eq_some_iff _ _ _).2 ⟨o, κ, hact⟩)
        simp [Function.update_of_ne this]
      · rw [stepP_of_out C (show C.Out r v from hact)]
    · exact absurd (by simp) (hγ r)

namespace KSetup

variable (S : KSetup A)

/-- The two-step configurations `α a b` agree (except on the copy) when neither process
distinguishes `fg` from `gf`. -/
lemma agreeAll_two (h0 : ¬ Dist O S.s 0 [(0, S.op 0), (1, S.op 1)] [(1, S.op 1), (0, S.op 0)])
    (h1 : ¬ Dist O S.s 1 [(0, S.op 0), (1, S.op 1)] [(1, S.op 1), (0, S.op 0)]) {a b : Fin 2}
    (hab : a ≠ b) :
    AgreeAll (.inr S.k) ((S.E.next (.step a)).next (.step b)) ((S.E.next (.step b)).next (.step a)) := by
  have e1 := S.run_two a b
  have e2 := S.run_two b a
  refine ⟨fun p => ?_, fun j hj => ?_⟩
  · rw [← e1, ← e2]
    have hp : p = a ∨ p = b := by
      have := fin2_ne_iff.1 hab; subst this; fin_cases a <;> fin_cases p <;> simp
    rcases hp with rfl | rfl
    · rw [S.two_steps_loc_self hab, S.two_steps_loc_other (Ne.symm hab)]
      congr 1
      have hD : ¬ Dist O S.s p [(p, S.op p), (b, S.op b)] [(b, S.op b), (p, S.op p)] := by
        have := fin2_ne_iff.1 hab; subst this
        fin_cases p
        · exact h0
        · intro h; apply h1; exact fun e => h e.symm
      simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ (Ne.symm hab),
        view_nil, not_not, List.cons.injEq, and_true] at hD
      exact hD
    · rw [S.two_steps_loc_other hab, S.two_steps_loc_self (Ne.symm hab)]
      congr 1
      have hD : ¬ Dist O S.s p [(a, S.op a), (p, S.op p)] [(p, S.op p), (a, S.op a)] := by
        have := fin2_ne_iff.1 hab; subst this
        fin_cases a
        · exact h1
        · intro h; apply h0; exact fun e => h e.symm
      simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ (Ne.symm hab),
        view_nil, not_not, List.cons.injEq, and_true] at hD
      exact hD
  · rw [← e1, ← e2, S.two_steps_mem_other hab hj, S.two_steps_mem_other (Ne.symm hab) hj]

lemma notDist_orient (h0 : ¬ Dist O S.s 0 [(0, S.op 0), (1, S.op 1)] [(1, S.op 1), (0, S.op 0)])
    (h1 : ¬ Dist O S.s 1 [(0, S.op 0), (1, S.op 1)] [(1, S.op 1), (0, S.op 0)]) {a b : Fin 2}
    (hab : a ≠ b) (p : Fin 2) :
    ¬ Dist O S.s p [(a, S.op a), (b, S.op b)] [(b, S.op b), (a, S.op a)] := by
  have := fin2_ne_iff.1 hab; subst this
  fin_cases a <;> fin_cases p
  · exact h0
  · exact h1
  · intro h; exact h0 (fun e => h e.symm)
  · intro h; exact h1 (fun e => h e.symm)

/-- **Lemma 5** (in the form used in the proof of Proposition 2, roles `a`, `b`). After `α a b`,
`a` runs solo until it is poised on the copy again (operation `cₐ`), then `b` runs solo until it
is poised on the copy again (operation `c_b`). Then `fₐ cₐ f_b c_b` and `f_b fₐ cₐ c_b` are
distinguishable to both processes, and `fₐ cₐ f_b` and `f_b` are distinguishable to `b` or
`fₐ cₐ f_b c_b` and `f_b fₐ c_b cₐ` are distinguishable to both processes. -/
theorem c34 (hA : WFConsensus A) (h2 : TwoShot A)
    (h0 : ¬ Dist O S.s 0 [(0, S.op 0), (1, S.op 1)] [(1, S.op 1), (0, S.op 0)])
    (h1 : ¬ Dist O S.s 1 [(0, S.op 0), (1, S.op 1)] [(1, S.op 1), (0, S.op 0)]) {a b : Fin 2}
    (hab : a ≠ b) :
    ∃ (ta : ℕ) (ca : O.Op) (κa : O.Resp → A.L),
      (∀ t' < ta, objOf (run ((S.E.next (.step a)).next (.step b)) (solo a t')) a ≠ some (.inr S.k)) ∧
      A.act ((run ((S.E.next (.step a)).next (.step b)) (solo a ta)).loc a) = .access (.inr S.k) ca κa ∧
    ∃ (tb : ℕ) (cb : O.Op) (κb : O.Resp → A.L),
      (∀ t' < tb, objOf (run (run ((S.E.next (.step a)).next (.step b)) (solo a ta)) (solo b t')) b
        ≠ some (.inr S.k)) ∧
      A.act ((run (run ((S.E.next (.step a)).next (.step b)) (solo a ta)) (solo b tb)).loc b) =
        .access (.inr S.k) cb κb ∧
      DistBoth O S.s [(a, S.op a), (a, ca), (b, S.op b), (b, cb)]
        [(b, S.op b), (a, S.op a), (a, ca), (b, cb)] ∧
      (Dist O S.s b [(a, S.op a), (a, ca), (b, S.op b)] [(b, S.op b)] ∨
        DistBoth O S.s [(a, S.op a), (a, ca), (b, S.op b), (b, cb)]
          [(b, S.op b), (a, S.op a), (b, cb), (a, ca)]) := by
  have hab' := Ne.symm hab
  have hDa := S.notDist_orient h0 h1 hab a
  have hDb := S.notDist_orient h0 h1 hab b
  have hca0 : accCount S.I S.α a (.inr S.k) = 0 := by
    have := S.accCount_crit_le h2 a
    by_contra h
    exact hDa (S.dist_of_last hA h2 hab a (Or.inl rfl) (by omega))
  have hcb0 : accCount S.I S.α b (.inr S.k) = 0 := by
    have := S.accCount_crit_le h2 b
    by_contra h
    exact hDb (S.dist_of_last hA h2 hab b (Or.inr rfl) (by omega))
  have hall := S.agreeAll_two h0 h1 hab
  set s := S.s with hs
  set fa := S.op a with hfa
  set fb := S.op b with hfb
  set k := S.k with hk
  have hfb_eq : (O.δ (O.δ s fa).1 fb).2 = (O.δ s fb).2 := by
    have := hDb
    simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil,
      not_not, List.cons.injEq, and_true] at this
    exact this
  set Ea := S.E.next (.step a) with hEa
  set Eb := S.E.next (.step b) with hEb
  set Zab := Ea.next (.step b) with hZab
  set Zba := Eb.next (.step a) with hZba
  have hBEa : S.Branch a Ea := S.branch_one a
  have hBEb : S.Branch b Eb := S.branch_one b
  have hBZab : S.Branch a Zab := hBEa.next b
  have hBZba : S.Branch b Zba := hBEb.next a
  have hEaa : Ea.loc a = S.κ a (O.δ s fa).2 := stepK_loc_self (S.hop a)
  have hEab : Ea.loc b = S.E.loc b := stepK_loc_other (S.hop a) hab'
  have hEbb : Eb.loc b = S.κ b (O.δ s fb).2 := stepK_loc_self (S.hop b)
  have hEba : Eb.loc a = S.E.loc a := stepK_loc_other (S.hop b) hab
  have hEak : Ea.mem (.inr k) = (O.δ s fa).1 := stepK_mem_self (S.hop a)
  have hEbk : Eb.mem (.inr k) = (O.δ s fb).1 := stepK_mem_self (S.hop b)
  have hEab' : A.act (Ea.loc b) = .access (.inr k) fb (S.κ b) := by rw [hEab]; exact S.hop b
  have hEba' : A.act (Eb.loc a) = .access (.inr k) fa (S.κ a) := by rw [hEba]; exact S.hop a
  have hZaba : Zab.loc a = Ea.loc a := stepK_loc_other hEab' hab
  have hZabk : Zab.mem (.inr k) = (O.δ (O.δ s fa).1 fb).1 := by
    rw [hZab, stepK_mem_self hEab', hEak]
  have hZbab : Zba.loc b = S.κ b (O.δ s fb).2 := by rw [hZba, stepK_loc_other hEba' hab', hEbb]
  have hZbak : Zba.mem (.inr k) = (O.δ (O.δ s fb).1 fa).1 := by
    rw [hZba, stepK_mem_self hEba', hEbk]
  -- `a` runs solo after `fg`
  obtain ⟨ta, hnoA, ca, κca, hca⟩ := S.must_access' hA hab hBZab hBZba (hall.agreeExcept a)
  refine ⟨ta, ca, κca, hnoA, hca, ?_⟩
  set Za1 := run Zab (solo a ta) with hZa1
  set Zba1 := run Zba (solo a ta) with hZba1
  have hall1 : AgreeAll (.inr k) Za1 Zba1 := hall.run _ (crashFree_replicate ta a) (fun p => by
    by_cases hp : p = a
    · subst hp; exact solo_accCount_self hnoA
    · exact solo_accCount_other hp ta _)
  have hEaZ : AgreeExcept (.inr k) a Zab Ea := ⟨hZaba, fun j hj => stepK_mem_other hEab' hj⟩
  have hnoEa := noAcc_transfer hEaZ hnoA
  set Ea1 := run Ea (solo a ta) with hEa1
  have hEa1Z : AgreeExcept (.inr k) a Ea1 Za1 := (hEaZ.symm.soloRun ta hnoEa)
  have hcaEa : A.act (Ea1.loc a) = .access (.inr k) ca κca := by rw [hEa1Z.1]; exact hca
  have hcaZba : A.act (Zba1.loc a) = .access (.inr k) ca κca := by rw [← hall1.1 a]; exact hca
  have hEa1k : Ea1.mem (.inr k) = (O.δ s fa).1 := by rw [hEa1, solo_noAcc_mem hnoEa, hEak]
  have hZba1k : Zba1.mem (.inr k) = (O.δ (O.δ s fb).1 fa).1 := by
    rw [hZba1, solo_noAcc_mem (noAcc_transfer (hall.agreeExcept a) hnoA), hZbak]
  have hBZa1 : S.Branch a Za1 := hBZab.ext _ (crashFree_replicate ta a)
  have hBZba1 : S.Branch b Zba1 := hBZba.ext _ (crashFree_replicate ta a)
  have hBEa1 : S.Branch a Ea1 := hBEa.ext _ (crashFree_replicate ta a)
  -- `b` runs solo next
  obtain ⟨tb, hnoB, cb, κcb, hcb⟩ := S.must_access' hA hab hBZa1 hBZba1 (hall1.agreeExcept b)
  refine ⟨tb, cb, κcb, hnoB, hcb, ?_⟩
  -- the configuration `fₐ cₐ`
  set P := Ea1.next (.step a) with hP
  have hBP : S.Branch a P := hBEa1.next a
  have hcntE : ∀ r, S.Cnt r S.E 0 := fun r => by
    rcases fin2_cases_ne r a b hab with rfl | rfl
    · exact hca0 ▸ S.cnt_crit r
    · exact hcb0 ▸ S.cnt_crit r
  have hcaP : S.Cnt a P 2 :=
    (((hcntE a).next_self (S.hop a)).solo_self hnoEa).next_self hcaEa
  have hPa : P.loc a = κca (O.δ (O.δ s fa).1 ca).2 := by rw [hP, stepK_loc_self hcaEa, hEa1k]
  have hPk : P.mem (.inr k) = (O.δ (O.δ s fa).1 ca).1 := by rw [hP, stepK_mem_self hcaEa, hEa1k]
  have hPj : ∀ j, j ≠ .inr k → P.mem j = Za1.mem j := fun j hj => by
    rw [hP, stepK_mem_other hcaEa hj, hEa1Z.2 j hj]
  set Q := Zba1.next (.step a) with hQ
  have hBQ : S.Branch b Q := hBZba1.next a
  have hQa : Q.loc a = κca (O.δ (O.δ (O.δ s fb).1 fa).1 ca).2 := by
    rw [hQ, stepK_loc_self hcaZba, hZba1k]
  have hQj : ∀ j, j ≠ .inr k → Q.mem j = Za1.mem j := fun j hj => by
    rw [hQ, stepK_mem_other hcaZba hj, ← hall1.2 j hj]
  have hA3 : (O.δ (O.δ s fa).1 ca).2 ≠ (O.δ (O.δ (O.δ s fb).1 fa).1 ca).2 := by
    intro heq
    exact S.contra' hA h2 hab hBP hBQ ⟨by rw [hPa, hQa, heq], fun j hj => by
      rw [hPj j hj, hQj j hj]⟩ hcaP le_rfl
  have hA3' : DistBoth O s [(a, fa), (a, ca), (b, fb), (b, cb)] [(b, fb), (a, fa), (a, ca), (b, cb)]
      ↔ Dist O s b [(a, fa), (a, ca), (b, fb), (b, cb)] [(b, fb), (a, fa), (a, ca), (b, cb)] := by
    rw [distBoth_iff O hab]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]
    intro h; simp only [List.cons.injEq] at h; exact hA3 h.2.1
  rw [hA3']
  by_cases hb1 : (O.δ (O.δ (O.δ s fa).1 ca).1 fb).2 = (O.δ s fb).2
  swap
  · constructor
    · simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]
      intro h; simp only [List.cons.injEq] at h; exact hb1 h.1
    · left
      simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]
      intro h; simp only [List.cons.injEq] at h; exact hb1 h.1
  -- `fₐ cₐ f_b`: `b` cannot tell it from `f_b fₐ cₐ`
  have hPb : P.loc b = S.E.loc b := by
    rw [hP, stepK_loc_other hcaEa hab', hEa1, solo_loc_other hab', hEab]
  have hPb' : A.act (P.loc b) = .access (.inr k) fb (S.κ b) := by rw [hPb]; exact S.hop b
  set P' := P.next (.step b) with hP'
  have hBP' : S.Branch a P' := hBP.next b
  have hP'b : P'.loc b = S.κ b (O.δ s fb).2 := by rw [hP', stepK_loc_self hPb', hPk, hb1]
  have hP'k : P'.mem (.inr k) = (O.δ (O.δ (O.δ s fa).1 ca).1 fb).1 := by
    rw [hP', stepK_mem_self hPb', hPk]
  have hP'j : ∀ j, j ≠ .inr k → P'.mem j = Za1.mem j := fun j hj => by
    rw [hP', stepK_mem_other hPb' hj, hPj j hj]
  have hZba1b : Zba1.loc b = S.κ b (O.δ s fb).2 := by rw [hZba1, solo_loc_other hab', hZbab]
  have hQb : Q.loc b = S.κ b (O.δ s fb).2 := by rw [hQ, stepK_loc_other hcaZba hab', hZba1b]
  have hZa1b : Za1.loc b = S.κ b (O.δ s fb).2 := by rw [hall1.1 b, hZba1b]
  have hZP' : AgreeExcept (.inr k) b Za1 P' :=
    ⟨by rw [hZa1b, hP'b], fun j hj => (hP'j j hj).symm⟩
  have hZQ : AgreeExcept (.inr k) b Za1 Q := ⟨by rw [hZa1b, hQb], fun j hj => (hQj j hj).symm⟩
  have hZZ : AgreeExcept (.inr k) b Za1 Zba1 := hall1.agreeExcept b
  have hnoP' := noAcc_transfer hZP' hnoB
  have hnoQ := noAcc_transfer hZQ hnoB
  have hnoZ := noAcc_transfer hZZ hnoB
  set P'1 := run P' (solo b tb) with hP'1
  set Q1 := run Q (solo b tb) with hQ1
  set Zba2 := run Zba1 (solo b tb) with hZba2
  have hZa2P := (hZP'.soloRun tb hnoB)
  have hZa2Q := (hZQ.soloRun tb hnoB)
  have hZa2Z := (hZZ.soloRun tb hnoB)
  have hcbP : A.act (P'1.loc b) = .access (.inr k) cb κcb := by rw [← hZa2P.1]; exact hcb
  have hcbQ : A.act (Q1.loc b) = .access (.inr k) cb κcb := by rw [← hZa2Q.1]; exact hcb
  have hcbZ : A.act (Zba2.loc b) = .access (.inr k) cb κcb := by rw [← hZa2Z.1]; exact hcb
  have hP'1k : P'1.mem (.inr k) = (O.δ (O.δ (O.δ s fa).1 ca).1 fb).1 := by
    rw [hP'1, solo_noAcc_mem hnoP', hP'k]
  have hQ1k : Q1.mem (.inr k) = (O.δ (O.δ (O.δ s fb).1 fa).1 ca).1 := by
    rw [hQ1, solo_noAcc_mem hnoQ, hQ, stepK_mem_self hcaZba, hZba1k]
  have hZba2k : Zba2.mem (.inr k) = (O.δ (O.δ s fb).1 fa).1 := by
    rw [hZba2, solo_noAcc_mem hnoZ, hZba1k]
  have hmemPQ : ∀ j, j ≠ .inr k → P'1.mem j = Q1.mem j := fun j hj => by
    rw [← hZa2P.2 j hj, hZa2Q.2 j hj]
  have hmemPZ : ∀ j, j ≠ .inr k → P'1.mem j = Zba2.mem j := fun j hj => by
    rw [← hZa2P.2 j hj, hZa2Z.2 j hj]
  have hcbP' : S.Cnt b P' 1 :=
    ((((hcntE b).next_other hab).solo_other hab ta).next_other hab).next_self hPb'
  have hcbP2 : S.Cnt b (P'1.next (.step b)) 2 := (hcbP'.solo_self hnoP').next_self hcbP
  have hcaP2 : S.Cnt a (P'1.next (.step b)) 2 := ((hcaP.next_other hab').solo_other hab' tb).next_other hab'
  have hBP2 : S.Branch a (P'1.next (.step b)) := (hBP'.ext _ (crashFree_replicate tb b)).next b
  -- (3), `b`'s part
  have hB3 : (O.δ (O.δ (O.δ (O.δ s fa).1 ca).1 fb).1 cb).2 ≠
      (O.δ (O.δ (O.δ (O.δ s fb).1 fa).1 ca).1 cb).2 := by
    intro heq
    refine S.contra' hA h2 hab hBP2 ((hBQ.ext _ (crashFree_replicate tb b)).next b)
      ⟨?_, fun j hj => ?_⟩ hcbP2 le_rfl
    · rw [stepK_loc_self hcbP, stepK_loc_self hcbQ, hP'1k, hQ1k, heq]
    · rw [stepK_mem_other hcbP hj, stepK_mem_other hcbQ hj, hmemPQ j hj]
  -- `f_b fₐ c_b cₐ`
  set R1 := Zba2.next (.step b) with hR1
  have hZba2a : Zba2.loc a = Zba1.loc a := by rw [hZba2, solo_loc_other hab]
  have hR1a' : A.act (R1.loc a) = .access (.inr k) ca κca := by
    rw [hR1, stepK_loc_other hcbZ hab, hZba2a]; exact hcaZba
  have hR1k : R1.mem (.inr k) = (O.δ (O.δ (O.δ s fb).1 fa).1 cb).1 := by
    rw [hR1, stepK_mem_self hcbZ, hZba2k]
  have hBR1 : S.Branch b R1 := (hBZba1.ext _ (crashFree_replicate tb b)).next b
  have hA4 : (O.δ (O.δ s fa).1 ca).2 ≠ (O.δ (O.δ (O.δ (O.δ s fb).1 fa).1 cb).1 ca).2 := by
    intro heq
    refine S.contra' hA h2 hab hBP2 (hBR1.next a) ⟨?_, fun j hj => ?_⟩ hcaP2 le_rfl
    · rw [stepK_loc_other hcbP hab, hP'1, solo_loc_other hab, hP', stepK_loc_other hPb' hab, hPa,
        stepK_loc_self hR1a', hR1k, heq]
    · rw [stepK_mem_other hcbP hj, stepK_mem_other hR1a' hj, hR1, stepK_mem_other hcbZ hj,
        hmemPZ j hj]
  have hB4 : (O.δ (O.δ (O.δ (O.δ s fa).1 ca).1 fb).1 cb).2 ≠ (O.δ (O.δ (O.δ s fb).1 fa).1 cb).2 := by
    intro heq
    refine S.contra' hA h2 hab hBP2 hBR1 ⟨?_, fun j hj => ?_⟩ hcbP2 le_rfl
    · rw [stepK_loc_self hcbP, hR1, stepK_loc_self hcbZ, hP'1k, hZba2k, heq]
    · rw [stepK_mem_other hcbP hj, hR1, stepK_mem_other hcbZ hj, hmemPZ j hj]
  constructor
  · simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]
    intro h; simp only [List.cons.injEq] at h; exact hB3 h.2.1
  · right
    rw [distBoth_iff O hab]
    constructor
    · simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]
      intro h; simp only [List.cons.injEq] at h; exact hA4 h.2.1
    · simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]
      intro h; simp only [List.cons.injEq] at h; exact hB4 h.2.1

end KSetup

end TwoShotCons

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

variable {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] {R : ιR → ObjSpec} {O : ObjSpec}
  {A : Alg 2 (withRW (ιS := ιS) R O)}

namespace KSetup

variable (S : KSetup A)

/-- The configuration `fg` (after `α 0 1`). -/
abbrev F : Cfg A := (S.E.next (.step 0)).next (.step 1)
/-- The configuration `gf` (after `α 1 0`). -/
abbrev G : Cfg A := (S.E.next (.step 1)).next (.step 0)

/-- `{c, c'}` is an edge of the paper's graph `G` (Proposition 2): from `fg`, without accessing
the copy, the processes reach a configuration where `p₀` is poised on `c` and `p₁` on `c'`. -/
def Edge (c c' : O.Op) : Prop :=
  ∃ γ, CrashFree γ ∧ (∀ p, accCount S.F γ p (.inr S.k) = 0) ∧
    (∃ κ, A.act ((run S.F γ).loc 0) = .access (.inr S.k) c κ) ∧
    (∃ κ', A.act ((run S.F γ).loc 1) = .access (.inr S.k) c' κ')

/-- Edge property (2) of `C₂`: the four pairs are distinguishable to both processes. -/
theorem edge_dist (hA : WFConsensus A) (h2 : TwoShot A)
    (h0 : ¬ Dist O S.s 0 [(0, S.op 0), (1, S.op 1)] [(1, S.op 1), (0, S.op 0)])
    (h1 : ¬ Dist O S.s 1 [(0, S.op 0), (1, S.op 1)] [(1, S.op 1), (0, S.op 0)])
    {c c' : O.Op} (he : S.Edge c c') :
    DistBoth O S.s [(0, S.op 0), (1, S.op 1), (0, c), (1, c')]
      [(1, S.op 1), (0, S.op 0), (0, c), (1, c')] ∧
    DistBoth O S.s [(0, S.op 0), (1, S.op 1), (0, c), (1, c')]
      [(1, S.op 1), (0, S.op 0), (1, c'), (0, c)] ∧
    DistBoth O S.s [(0, S.op 0), (1, S.op 1), (1, c'), (0, c)]
      [(1, S.op 1), (0, S.op 0), (0, c), (1, c')] ∧
    DistBoth O S.s [(0, S.op 0), (1, S.op 1), (1, c'), (0, c)]
      [(1, S.op 1), (0, S.op 0), (1, c'), (0, c)] := by
  obtain ⟨γ, hγ, hno, ⟨κ0, hc0⟩, ⟨κ1, hc1⟩⟩ := he
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hall := S.agreeAll_two h0 h1 h01
  have hca0 : accCount S.I S.α 0 (.inr S.k) = 0 := by
    have := S.accCount_crit_le h2 0
    by_contra h
    exact (S.notDist_orient h0 h1 h01 0) (S.dist_of_last hA h2 h01 0 (Or.inl rfl) (by omega))
  have hcb0 : accCount S.I S.α 1 (.inr S.k) = 0 := by
    have := S.accCount_crit_le h2 1
    by_contra h
    exact (S.notDist_orient h0 h1 h01 1) (S.dist_of_last hA h2 h01 1 (Or.inr rfl) (by omega))
  set s := S.s
  set f := S.op 0
  set g := S.op 1
  set X := run S.F γ with hX
  set Y := run S.G γ with hY
  have hXY : AgreeAll (.inr S.k) X Y := hall.run γ hγ hno
  have hBX : S.Branch 0 X := ((S.branch_one 0).next 1).ext γ hγ
  have hBY : S.Branch 1 Y := ((S.branch_one 1).next 0).ext γ hγ
  have hc0Y : A.act (Y.loc 0) = .access (.inr S.k) c κ0 := by rw [← hXY.1 0]; exact hc0
  have hc1Y : A.act (Y.loc 1) = .access (.inr S.k) c' κ1 := by rw [← hXY.1 1]; exact hc1
  have hXk : X.mem (.inr S.k) = (O.δ (O.δ s f).1 g).1 := by
    rw [hX, mem_of_noAcc hγ hno]
    have := S.two_steps_mem_k h01; rw [S.run_two] at this; exact this
  have hYk : Y.mem (.inr S.k) = (O.δ (O.δ s g).1 f).1 := by
    rw [hY, mem_of_noAcc hγ (accCount_congr_of_agreeAll hall γ hγ hno)]
    have := S.two_steps_mem_k h10; rw [S.run_two] at this; exact this
  -- counts
  have hcX : ∀ r, S.Cnt r X 1 := by
    intro r
    have e0 : S.Cnt 0 S.E 0 := hca0 ▸ S.cnt_crit 0
    have e1 : S.Cnt 1 S.E 0 := hcb0 ▸ S.cnt_crit 1
    have hF0 : S.Cnt 0 S.F 1 := (e0.next_self (S.hop 0)).next_other h10
    have hF1 : S.Cnt 1 S.F 1 := (e1.next_other h01).next_self (by
      rw [stepK_loc_other (S.hop 0) h10]; exact S.hop 1)
    fin_cases r
    · have := hF0.ext γ hγ; rwa [hno 0] at this
    · have := hF1.ext γ hγ; rwa [hno 1] at this
  -- the two orders from a configuration where both are poised
  have key : ∀ (Z : Cfg A) (hc0Z : A.act (Z.loc 0) = .access (.inr S.k) c κ0)
      (hc1Z : A.act (Z.loc 1) = .access (.inr S.k) c' κ1),
      ((Z.next (.step 0)).next (.step 1)).loc 0 = κ0 (O.δ (Z.mem (.inr S.k)) c).2 ∧
      ((Z.next (.step 0)).next (.step 1)).loc 1 =
        κ1 (O.δ (O.δ (Z.mem (.inr S.k)) c).1 c').2 ∧
      ((Z.next (.step 1)).next (.step 0)).loc 1 = κ1 (O.δ (Z.mem (.inr S.k)) c').2 ∧
      ((Z.next (.step 1)).next (.step 0)).loc 0 =
        κ0 (O.δ (O.δ (Z.mem (.inr S.k)) c').1 c).2 ∧
      (∀ j, j ≠ .inr S.k → ((Z.next (.step 0)).next (.step 1)).mem j = Z.mem j) ∧
      (∀ j, j ≠ .inr S.k → ((Z.next (.step 1)).next (.step 0)).mem j = Z.mem j) := by
    intro Z hc0Z hc1Z
    have hc1' : A.act ((Z.next (.step 0)).loc 1) = .access (.inr S.k) c' κ1 := by
      rw [stepK_loc_other hc0Z h10]; exact hc1Z
    have hc0' : A.act ((Z.next (.step 1)).loc 0) = .access (.inr S.k) c κ0 := by
      rw [stepK_loc_other hc1Z h01]; exact hc0Z
    refine ⟨?_, ?_, ?_, ?_, fun j hj => ?_, fun j hj => ?_⟩
    · rw [stepK_loc_other hc1' h01, stepK_loc_self hc0Z]
    · rw [stepK_loc_self hc1', stepK_mem_self hc0Z]
    · rw [stepK_loc_other hc0' h10, stepK_loc_self hc1Z]
    · rw [stepK_loc_self hc0', stepK_mem_self hc1Z]
    · rw [stepK_mem_other hc1' hj, stepK_mem_other hc0Z hj]
    · rw [stepK_mem_other hc0' hj, stepK_mem_other hc1Z hj]
  obtain ⟨X1, X2, X3, X4, X5, X6⟩ := key X hc0 hc1
  obtain ⟨Y1, Y2, Y3, Y4, Y5, Y6⟩ := key Y hc0Y hc1Y
  have hB01 : S.Branch 0 ((X.next (.step 0)).next (.step 1)) := (hBX.next 0).next 1
  have hB10 : S.Branch 0 ((X.next (.step 1)).next (.step 0)) := (hBX.next 1).next 0
  have hC01 : S.Branch 1 ((Y.next (.step 0)).next (.step 1)) := (hBY.next 0).next 1
  have hC10 : S.Branch 1 ((Y.next (.step 1)).next (.step 0)) := (hBY.next 1).next 0
  have cnt01 : ∀ r, S.Cnt r ((X.next (.step 0)).next (.step 1)) 2 := by
    intro r; fin_cases r
    · exact ((hcX 0).next_self hc0).next_other h10
    · exact ((hcX 1).next_other h01).next_self (by rw [stepK_loc_other hc0 h10]; exact hc1)
  have cnt10 : ∀ r, S.Cnt r ((X.next (.step 1)).next (.step 0)) 2 := by
    intro r; fin_cases r
    · exact ((hcX 0).next_other h10).next_self (by rw [stepK_loc_other hc1 h01]; exact hc0)
    · exact ((hcX 1).next_self hc1).next_other h01
  have memXY : ∀ j, j ≠ .inr S.k → X.mem j = Y.mem j := hXY.2
  -- the eight inequalities
  have n1 : (O.δ (O.δ (O.δ s f).1 g).1 c).2 ≠ (O.δ (O.δ (O.δ s g).1 f).1 c).2 := by
    intro heq
    exact S.contra' hA h2 h01 hB01 hC01 ⟨by rw [X1, Y1, hXk, hYk, heq], fun j hj => by
      rw [X5 j hj, Y5 j hj, memXY j hj]⟩ (cnt01 0) le_rfl
  have n2 : (O.δ (O.δ (O.δ (O.δ s f).1 g).1 c).1 c').2 ≠
      (O.δ (O.δ (O.δ (O.δ s g).1 f).1 c).1 c').2 := by
    intro heq
    exact S.contra' hA h2 h01 hB01 hC01 ⟨by rw [X2, Y2, hXk, hYk, heq], fun j hj => by
      rw [X5 j hj, Y5 j hj, memXY j hj]⟩ (cnt01 1) le_rfl
  have n3 : (O.δ (O.δ (O.δ s f).1 g).1 c).2 ≠ (O.δ (O.δ (O.δ (O.δ s g).1 f).1 c').1 c).2 := by
    intro heq
    exact S.contra' hA h2 h01 hB01 hC10 ⟨by rw [X1, Y4, hXk, hYk, heq], fun j hj => by
      rw [X5 j hj, Y6 j hj, memXY j hj]⟩ (cnt01 0) le_rfl
  have n4 : (O.δ (O.δ (O.δ (O.δ s f).1 g).1 c).1 c').2 ≠ (O.δ (O.δ (O.δ s g).1 f).1 c').2 := by
    intro heq
    exact S.contra' hA h2 h01 hB01 hC10 ⟨by rw [X2, Y3, hXk, hYk, heq], fun j hj => by
      rw [X5 j hj, Y6 j hj, memXY j hj]⟩ (cnt01 1) le_rfl
  have n5 : (O.δ (O.δ (O.δ (O.δ s f).1 g).1 c').1 c).2 ≠ (O.δ (O.δ (O.δ s g).1 f).1 c).2 := by
    intro heq
    exact S.contra' hA h2 h01 hB10 hC01 ⟨by rw [X4, Y1, hXk, hYk, heq], fun j hj => by
      rw [X6 j hj, Y5 j hj, memXY j hj]⟩ (cnt10 0) le_rfl
  have n6 : (O.δ (O.δ (O.δ s f).1 g).1 c').2 ≠ (O.δ (O.δ (O.δ (O.δ s g).1 f).1 c).1 c').2 := by
    intro heq
    exact S.contra' hA h2 h01 hB10 hC01 ⟨by rw [X3, Y2, hXk, hYk, heq], fun j hj => by
      rw [X6 j hj, Y5 j hj, memXY j hj]⟩ (cnt10 1) le_rfl
  have n7 : (O.δ (O.δ (O.δ (O.δ s f).1 g).1 c').1 c).2 ≠
      (O.δ (O.δ (O.δ (O.δ s g).1 f).1 c').1 c).2 := by
    intro heq
    exact S.contra' hA h2 h01 hB10 hC10 ⟨by rw [X4, Y4, hXk, hYk, heq], fun j hj => by
      rw [X6 j hj, Y6 j hj, memXY j hj]⟩ (cnt10 0) le_rfl
  have n8 : (O.δ (O.δ (O.δ s f).1 g).1 c').2 ≠ (O.δ (O.δ (O.δ s g).1 f).1 c').2 := by
    intro heq
    exact S.contra' hA h2 h01 hB10 hC10 ⟨by rw [X3, Y3, hXk, hYk, heq], fun j hj => by
      rw [X6 j hj, Y6 j hj, memXY j hj]⟩ (cnt10 1) le_rfl
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
  · simp only [Dist, view_cons_self, view_cons_other O _ h01, view_cons_other O _ h10, view_nil]
    intro h; simp only [List.cons.injEq] at h
    first
    | exact n1 h.2.1 | exact n2 h.2.1 | exact n3 h.2.1 | exact n4 h.2.1
    | exact n5 h.2.1 | exact n6 h.2.1 | exact n7 h.2.1 | exact n8 h.2.1

end KSetup

end TwoShotCons
