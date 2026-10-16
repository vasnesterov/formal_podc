import Papers.PODC2025.TwoShotConsensusObjects.NecCore

/-!
# Necessity — Proposition 1 (and Lemma 5): the class `C₁.₅`

At the critical configuration, if `fg` and `gf` are distinguishable to process `a` but not to
process `b`, then the object satisfies the properties of `C₁.₅` with `a` in the role of `p₀`.

Compared with the paper, we also cover the case where `f` is the *second* access of `a` to the
copy (the paper implicitly assumes that both `f` and `g` are first accesses), and the case where
`a` does not access the copy again (then `f'` is arbitrary: we take `f' = f`); in both cases
`(5a)` holds.
-/

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

variable {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] {R : ιR → ObjSpec} {O : ObjSpec}
  {A : Alg 2 (withRW (ιS := ιS) R O)}

namespace KSetup

variable (S : KSetup A)

lemma allowed_of_branch {m : Fin 2 → Set O.Op} (hm : Allowed m A) {a : Fin 2} {X : Cfg A}
    (hX : S.Branch a X) {p : Fin 2} {k : ιS} {o : O.Op} {κ : O.Resp → A.L}
    (h : A.act (X.loc p) = .access (.inr k) o κ) : o ∈ m p := by
  obtain ⟨β, hβ, rfl⟩ := hX
  exact hm S.x _ ((S.hα.append (crashFree_single a)).append hβ) p k o κ h

lemma allowed_crit {m : Fin 2 → Set O.Op} (hm : Allowed m A) (p : Fin 2) : S.op p ∈ m p :=
  hm S.x S.α S.hα p S.k (S.op p) (S.κ p) (S.hop p)

lemma run_one (a : Fin 2) : run S.I (S.α ++ [.step a]) = S.E.next (.step a) := run_concat _ _ _

lemma run_two (a b : Fin 2) :
    run S.I (S.α ++ [.step a] ++ [.step b]) = (S.E.next (.step a)).next (.step b) := by
  rw [run_concat, run_one]

lemma branch_one (a : Fin 2) : S.Branch a (S.E.next (.step a)) := by
  rw [← run_one]; exact S.branch_step a

/-- **Proposition 1** (with Lemma 5): `fg`/`gf` distinguishable to `a` but not to `b` ⇒ the
`C₁.₅` properties with `a` in the role of `p₀`. -/
theorem c15 (hA : WFConsensus A) (h2 : TwoShot A) {m : Fin 2 → Set O.Op} (hm : Allowed m A)
    {a b : Fin 2} (hab : a ≠ b)
    (hDa : Dist O S.s a [(a, S.op a), (b, S.op b)] [(b, S.op b), (a, S.op a)])
    (hDb : ¬ Dist O S.s b [(a, S.op a), (b, S.op b)] [(b, S.op b), (a, S.op a)]) :
    C15Cond O m a b := by
  have hab' := Ne.symm hab
  -- `g` is the first access of `b`
  have hcb : accCount S.I S.α b (.inr S.k) = 0 := by
    have := S.accCount_crit_le h2 b
    by_contra h
    exact hDb (S.dist_of_last hA h2 hab b (Or.inr rfl) (by omega))
  set s := S.s with hs
  set f := S.op a with hf
  set g := S.op b with hg
  set k := S.k with hk
  have hgeq : (O.δ (O.δ s f).1 g).2 = (O.δ s g).2 := by
    have := hDb; simp only [Dist, view, resps, hab, hab', List.filterMap] at this
    simpa using this
  have hfne : (O.δ s f).2 ≠ (O.δ (O.δ s g).1 f).2 := by
    have := hDa; simp only [Dist, view, resps, hab, hab', List.filterMap] at this
    simpa using this
  -- configurations
  set Ea := S.E.next (.step a) with hEa
  set Eb := S.E.next (.step b) with hEb
  set Fa := Ea.next (.step b) with hFa
  set G := Eb.next (.step a) with hG
  have hBEa : S.Branch a Ea := S.branch_one a
  have hBEb : S.Branch b Eb := S.branch_one b
  have hBFa : S.Branch a Fa := hBEa.next b
  have hBG : S.Branch b G := hBEb.next a
  have hEaa : Ea.loc a = S.κ a (O.δ s f).2 := stepK_loc_self (S.hop a)
  have hEab : Ea.loc b = S.E.loc b := stepK_loc_other (S.hop a) hab'
  have hEbb : Eb.loc b = S.κ b (O.δ s g).2 := stepK_loc_self (S.hop b)
  have hEba : Eb.loc a = S.E.loc a := stepK_loc_other (S.hop b) hab
  have hEak : Ea.mem (.inr k) = (O.δ s f).1 := stepK_mem_self (S.hop a)
  have hEbk : Eb.mem (.inr k) = (O.δ s g).1 := stepK_mem_self (S.hop b)
  have hEaj : ∀ j, j ≠ .inr k → Ea.mem j = S.E.mem j := fun j hj => stepK_mem_other (S.hop a) hj
  have hEbj : ∀ j, j ≠ .inr k → Eb.mem j = S.E.mem j := fun j hj => stepK_mem_other (S.hop b) hj
  have hEab' : A.act (Ea.loc b) = .access (.inr k) g (S.κ b) := by rw [hEab]; exact S.hop b
  have hEba' : A.act (Eb.loc a) = .access (.inr k) f (S.κ a) := by rw [hEba]; exact S.hop a
  have hFab : Fa.loc b = S.κ b (O.δ (O.δ s f).1 g).2 := by
    rw [hFa, stepK_loc_self hEab', hEak]
  have hFaa : Fa.loc a = S.κ a (O.δ s f).2 := by rw [hFa, stepK_loc_other hEab' hab, hEaa]
  have hFak : Fa.mem (.inr k) = (O.δ (O.δ s f).1 g).1 := by rw [hFa, stepK_mem_self hEab', hEak]
  have hFaj : ∀ j, j ≠ .inr k → Fa.mem j = S.E.mem j := fun j hj => by
    rw [hFa, stepK_mem_other hEab' hj, hEaj j hj]
  have hGb : G.loc b = S.κ b (O.δ s g).2 := by rw [hG, stepK_loc_other hEba' hab', hEbb]
  have hGk : G.mem (.inr k) = (O.δ (O.δ s g).1 f).1 := by rw [hG, stepK_mem_self hEba', hEbk]
  have hGj : ∀ j, j ≠ .inr k → G.mem j = S.E.mem j := fun j hj => by
    rw [hG, stepK_mem_other hEba' hj, hEbj j hj]
  -- `b` cannot distinguish `fg` from `g` nor from `gf`
  have hFEb : AgreeExcept (.inr k) b Fa Eb :=
    ⟨by rw [hFab, hEbb, hgeq], fun j hj => by rw [hFaj j hj, hEbj j hj]⟩
  have hFG : AgreeExcept (.inr k) b Fa G :=
    ⟨by rw [hFab, hGb, hgeq], fun j hj => by rw [hFaj j hj, hGj j hj]⟩
  -- `b` runs solo from `fg` until it accesses `k` again (operation `g'`)
  obtain ⟨t1, hno1, g', κ', hg'⟩ := S.must_access' hA hab hBFa hBEb hFEb
  set F1 := run Fa (solo b t1) with hF1
  set Eb1 := run Eb (solo b t1) with hEb1
  set G1 := run G (solo b t1) with hG1
  have hF1Eb1 : AgreeExcept (.inr k) b F1 Eb1 := hFEb.soloRun t1 hno1
  have hF1G1 : AgreeExcept (.inr k) b F1 G1 := hFG.soloRun t1 hno1
  have hg'Eb : A.act (Eb1.loc b) = .access (.inr k) g' κ' := by rw [← hF1Eb1.1]; exact hg'
  have hg'G : A.act (G1.loc b) = .access (.inr k) g' κ' := by rw [← hF1G1.1]; exact hg'
  have hF1k : F1.mem (.inr k) = (O.δ (O.δ s f).1 g).1 := by rw [hF1, solo_noAcc_mem hno1, hFak]
  have hEb1k : Eb1.mem (.inr k) = (O.δ s g).1 := by
    rw [hEb1, solo_noAcc_mem (noAcc_transfer hFEb hno1), hEbk]
  have hG1k : G1.mem (.inr k) = (O.δ (O.δ s g).1 f).1 := by
    rw [hG1, solo_noAcc_mem (noAcc_transfer hFG hno1), hGk]
  have hBF1 : S.Branch a F1 := hBFa.ext _ (solo_crashFree b t1)
  have hBEb1 : S.Branch b Eb1 := hBEb.ext _ (solo_crashFree b t1)
  have hBG1 : S.Branch b G1 := hBG.ext _ (solo_crashFree b t1)
  have hg'm : g' ∈ m b := S.allowed_of_branch hm hBF1 hg'
  -- counts of `b`
  have hcF1 : S.Cnt b F1 1 := by
    have h0 : S.Cnt b S.E 0 := hcb ▸ S.cnt_crit b
    exact ((h0.next_other hab).next_self hEab').solo_self hno1
  set H := F1.next (.step b) with hH
  set K := Eb1.next (.step b) with hK
  have hcH : S.Cnt b H 2 := hcF1.next_self hg'
  have hBH : S.Branch a H := hBF1.next b
  have hBK : S.Branch b K := hBEb1.next b
  have hHb : H.loc b = κ' (O.δ (O.δ (O.δ s f).1 g).1 g').2 := by
    rw [hH, stepK_loc_self hg', hF1k]
  have hKb : K.loc b = κ' (O.δ (O.δ s g).1 g').2 := by rw [hK, stepK_loc_self hg'Eb, hEb1k]
  have hHj : ∀ j, j ≠ .inr k → H.mem j = F1.mem j := fun j hj => stepK_mem_other hg' hj
  have hKj : ∀ j, j ≠ .inr k → K.mem j = Eb1.mem j := fun j hj => stepK_mem_other hg'Eb hj
  have hHk : H.mem (.inr k) = (O.δ (O.δ (O.δ s f).1 g).1 g').1 := by
    rw [hH, stepK_mem_self hg', hF1k]
  have hKk : K.mem (.inr k) = (O.δ (O.δ s g).1 g').1 := by rw [hK, stepK_mem_self hg'Eb, hEb1k]
  -- (3), `b`'s part: `fgg'` vs `gfg'`
  have hg'3 : (O.δ (O.δ (O.δ s f).1 g).1 g').2 ≠ (O.δ (O.δ (O.δ s g).1 f).1 g').2 := by
    intro heq
    refine S.contra' hA h2 hab hBH (hBG1.next b) ?_ hcH le_rfl
    refine ⟨by rw [hHb, stepK_loc_self hg'G, hG1k, heq], fun j hj => ?_⟩
    rw [hHj j hj, stepK_mem_other hg'G hj, hF1G1.2 j hj]
  -- (4), `b`'s part: `fgg'` vs `gg'`
  have hg'4 : (O.δ (O.δ (O.δ s f).1 g).1 g').2 ≠ (O.δ (O.δ s g).1 g').2 := by
    intro heq
    refine S.contra' hA h2 hab hBH hBK ?_ hcH le_rfl
    refine ⟨by rw [hHb, hKb, heq], fun j hj => ?_⟩
    rw [hHj j hj, hKj j hj, hF1Eb1.2 j hj]
  -- `a` at `K` is still poised on `f`
  have hKa : K.loc a = S.E.loc a := by
    rw [hK, stepK_loc_other hg'Eb hab, hEb1, solo_loc_other hab, hEba]
  have hKa' : A.act (K.loc a) = .access (.inr k) f (S.κ a) := by rw [hKa]; exact S.hop a
  have hHa : H.loc a = S.κ a (O.δ s f).2 := by
    rw [hH, stepK_loc_other hg' hab, hF1, solo_loc_other hab, hFaa]
  have hfm : f ∈ m a := S.allowed_crit hm a
  have hgm : g ∈ m b := S.allowed_crit hm b
  by_cases hfa : (O.δ (O.δ (O.δ s g).1 g').1 f).2 = (O.δ s f).2
  swap
  · -- (5a) holds; take `f' = f`
    refine ⟨s, f, f, g, g', hfm, hfm, hgm, hg'm, hDa, hDb, ?_, ?_, ?_⟩
    · rw [distBoth_iff O hab]
      constructor
      · simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]; simp [hfne]
      · simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]; simp [hg'3]
    · rw [distBoth_iff O hab]
      constructor
      · simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]; simp [hfa]
      · simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]; simp [hgeq, Ne.symm hg'4]
    · left
      simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]; simp [hfa]
  -- `a` cannot tell `fgσg'` from `gσg'f`
  set Ka := K.next (.step a) with hKa_def
  have hBKa : S.Branch b Ka := hBK.next a
  have hKaa : Ka.loc a = S.κ a (O.δ (O.δ (O.δ s g).1 g').1 f).2 := by
    rw [hKa_def, stepK_loc_self hKa', hKk]
  have hKaj : ∀ j, j ≠ .inr k → Ka.mem j = K.mem j := fun j hj => stepK_mem_other hKa' hj
  have hKak : Ka.mem (.inr k) = (O.δ (O.δ (O.δ s g).1 g').1 f).1 := by
    rw [hKa_def, stepK_mem_self hKa', hKk]
  have hHKa : AgreeExcept (.inr k) a H Ka :=
    ⟨by rw [hHa, hKaa, hfa], fun j hj => by rw [hHj j hj, hKaj j hj, hKj j hj, hF1Eb1.2 j hj]⟩
  -- `f` is the first access of `a`
  have hca : accCount S.I S.α a (.inr k) = 0 := by
    have hle : accCount S.I S.α a (.inr k) ≤ 1 := S.accCount_crit_le h2 a
    by_contra hne
    have h1 : S.Cnt a S.E 1 := (show accCount S.I S.α a (.inr k) = 1 by omega) ▸ S.cnt_crit a
    have hcHa : S.Cnt a H 2 :=
      (((h1.next_self (S.hop a)).next_other hab').solo_other hab' t1).next_other hab'
    exact S.contra' hA h2 hab hBH hBKa hHKa hcHa le_rfl
  have hcHa : S.Cnt a H 1 := by
    have h0 : S.Cnt a S.E 0 := hca ▸ S.cnt_crit a
    exact (((h0.next_self (S.hop a)).next_other hab').solo_other hab' t1).next_other hab'
  -- `a` runs solo until it accesses `k` again (operation `f'`)
  obtain ⟨t0, hno0, f', κf', hf'⟩ := S.must_access' hA hab hBH hBKa hHKa
  set H1 := run H (solo a t0) with hH1
  set Ka1 := run Ka (solo a t0) with hKa1
  have hHKa1 : AgreeExcept (.inr k) a H1 Ka1 := hHKa.soloRun t0 hno0
  have hf'Ka : A.act (Ka1.loc a) = .access (.inr k) f' κf' := by rw [← hHKa1.1]; exact hf'
  have hBH1 : S.Branch a H1 := hBH.ext _ (solo_crashFree a t0)
  have hBKa1 : S.Branch b Ka1 := hBKa.ext _ (solo_crashFree a t0)
  have hf'm : f' ∈ m a := S.allowed_of_branch hm hBH1 hf'
  have hH1k : H1.mem (.inr k) = (O.δ (O.δ (O.δ s f).1 g).1 g').1 := by
    rw [hH1, solo_noAcc_mem hno0, hHk]
  have hKa1k : Ka1.mem (.inr k) = (O.δ (O.δ (O.δ s g).1 g').1 f).1 := by
    rw [hKa1, solo_noAcc_mem (noAcc_transfer hHKa hno0), hKak]
  -- (4), `a`'s part
  have hf'4 : (O.δ (O.δ (O.δ (O.δ s f).1 g).1 g').1 f').2 ≠
      (O.δ (O.δ (O.δ (O.δ s g).1 g').1 f).1 f').2 := by
    intro heq
    refine S.contra' hA h2 hab (hBH1.next a) (hBKa1.next a) ?_
      ((hcHa.solo_self hno0).next_self hf') le_rfl
    refine ⟨by rw [stepK_loc_self hf', stepK_loc_self hf'Ka, hH1k, hKa1k, heq], fun j hj => ?_⟩
    rw [stepK_mem_other hf' hj, stepK_mem_other hf'Ka hj, hHKa1.2 j hj]
  -- (5b): `fgσ_b σ_a f'g'` vs `gσ_b g' f σ_a f'`
  have hHF1 : AgreeExcept (.inr k) a H F1 :=
    ⟨by rw [hH, stepK_loc_other hg' hab], fun j hj => hHj j hj⟩
  set F1' := run F1 (solo a t0) with hF1'
  have hH1F1' : AgreeExcept (.inr k) a H1 F1' := hHF1.soloRun t0 hno0
  have hf'F : A.act (F1'.loc a) = .access (.inr k) f' κf' := by rw [← hH1F1'.1]; exact hf'
  have hF1'b : F1'.loc b = F1.loc b := by rw [hF1', solo_loc_other hab']
  have hg'F : A.act (F1'.loc b) = .access (.inr k) g' κ' := by rw [hF1'b]; exact hg'
  have hF1'k : F1'.mem (.inr k) = (O.δ (O.δ s f).1 g).1 := by
    rw [hF1', solo_noAcc_mem (noAcc_transfer hHF1 hno0), hF1k]
  set E4a := F1'.next (.step a) with hE4a
  set E4 := E4a.next (.step b) with hE4
  have hg'F4 : A.act (E4a.loc b) = .access (.inr k) g' κ' := by
    rw [hE4a, stepK_loc_other hf'F hab']; exact hg'F
  have hBE4 : S.Branch a E4 := ((hBF1.ext _ (solo_crashFree a t0)).next a).next b
  have hE4mem : ∀ j, j ≠ .inr k → E4.mem j = (Ka1.next (.step a)).mem j := fun j hj => by
    rw [hE4, stepK_mem_other hg'F4 hj, hE4a, stepK_mem_other hf'F hj, stepK_mem_other hf'Ka hj,
      ← hHKa1.2 j hj, hH1F1'.2 j hj]
  have hcF1a : S.Cnt a F1 1 := by
    have h0 : S.Cnt a S.E 0 := hca ▸ S.cnt_crit a
    exact ((h0.next_self (S.hop a)).next_other hab').solo_other hab' t1
  have hcF1' : S.Cnt a F1' 1 := hcF1a.solo_self (noAcc_transfer hHF1 hno0)
  have hf'5 : (O.δ (O.δ (O.δ s f).1 g).1 f').2 ≠ (O.δ (O.δ (O.δ (O.δ s g).1 g').1 f).1 f').2 := by
    intro heq
    refine S.contra' hA h2 hab hBE4 (hBKa1.next a) ?_ ((hcF1'.next_self hf'F).next_other hab') le_rfl
    refine ⟨?_, hE4mem⟩
    rw [hE4, stepK_loc_other hg'F4 hab, hE4a, stepK_loc_self hf'F, stepK_loc_self hf'Ka, hF1'k,
      hKa1k, heq]
  have hg'5 : (O.δ (O.δ (O.δ (O.δ s f).1 g).1 f').1 g').2 ≠ (O.δ (O.δ s g).1 g').2 := by
    intro heq
    have hcb' : S.Cnt b E4 2 := ((hcF1.solo_other hab t0).next_other hab).next_self hg'F4
    refine S.contra' hA h2 hab hBE4 (hBKa1.next a) ?_ hcb' le_rfl
    refine ⟨?_, hE4mem⟩
    rw [hE4, stepK_loc_self hg'F4, hE4a, stepK_mem_self hf'F, hF1'k, heq,
      stepK_loc_other hf'Ka hab', hKa1, solo_loc_other hab', hKa_def, stepK_loc_other hKa' hab',
      hKb]
  refine ⟨s, f, f', g, g', hfm, hf'm, hgm, hg'm, hDa, hDb, ?_, ?_, ?_⟩
  · rw [distBoth_iff O hab]
    constructor
    · simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]; simp [hfne]
    · simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]; simp [hg'3]
  · rw [distBoth_iff O hab]
    constructor
    · simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]; simp [Ne.symm hf'4]
    · simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]; simp [hgeq, Ne.symm hg'4]
  · right
    rw [distBoth_iff O hab]
    constructor
    · simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]; simp [Ne.symm hf'5]
    · simp only [Dist, view_cons_self, view_cons_other O _ hab, view_cons_other O _ hab', view_nil]; simp [hgeq, Ne.symm hg'5]

end KSetup

end TwoShotCons
