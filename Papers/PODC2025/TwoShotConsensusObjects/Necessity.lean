import Papers.PODC2025.TwoShotConsensusObjects.NecC2

/-!
# Necessity — Theorem 3

If objects of type `(O, m)` (with read/write objects) solve wait-free two-process consensus with
two-shot copies of `O`, then `(O, m)` is in `C₁`, `C₁.₅` or `C₂`.

The paper assumes an algorithm with the minimal number of copies; we argue by (strong) induction
on the number of copies, which is the same argument.
-/

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

variable {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] {R : ιR → ObjSpec} {O : ObjSpec}
  {A : Alg 2 (withRW (ιS := ιS) R O)}

namespace KSetup

variable (S : KSetup A)

lemma contra_out' (hA : WFConsensus A) {a b : Fin 2} (hab : a ≠ b) {X Y : Cfg A}
    (hX : S.Branch a X) (hY : S.Branch b Y) {r : Fin 2} {i : ιR ⊕ ιS}
    (hag : AgreeExcept i r X Y) {v : Bool} (hout : X.Out r v) : False := by
  obtain ⟨β, hβ, rfl⟩ := hX
  obtain ⟨β', hβ', rfl⟩ := hY
  exact S.contra_out hA hab hβ hβ' hag (t := 0) (fun t' ht' => absurd ht' (Nat.not_lt_zero _))
    hout

/-- The first time a solo run reaches a configuration poised on the copy is unique. -/
lemma first_poised_unique {C : Cfg A} {r : Fin 2} {t t' : ℕ} {c c' : O.Op}
    {κ κ' : O.Resp → A.L}
    (hno : ∀ u < t, objOf (run C (solo r u)) r ≠ some (.inr S.k))
    (hc : A.act ((run C (solo r t)).loc r) = .access (.inr S.k) c κ)
    (hno' : ∀ u < t', objOf (run C (solo r u)) r ≠ some (.inr S.k))
    (hc' : A.act ((run C (solo r t')).loc r) = .access (.inr S.k) c' κ') : c = c' := by
  have htt : t = t' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hno' t h ((objOf_eq_some_iff _ _ _).2 ⟨c, κ, hc⟩)
    · exact hno t' h ((objOf_eq_some_iff _ _ _).2 ⟨c', κ', hc'⟩)
  subst htt
  rw [hc] at hc'
  cases hc'
  rfl

/-- **Proposition 2** (with the minimality argument): if neither process distinguishes `fg`
from `gf`, then `(O, m)` satisfies `C₂`, or consensus is solvable with fewer copies of `O`. -/
theorem c2_or_smaller [Fintype ιS] (hR : ∀ j, IsRW (R j)) (hA : WFConsensus A) (h2 : TwoShot A)
    {m : Fin 2 → Set O.Op} (hm : Allowed m A)
    (h0 : ¬ Dist O S.s 0 [(0, S.op 0), (1, S.op 1)] [(1, S.op 1), (0, S.op 0)])
    (h1 : ¬ Dist O S.s 1 [(0, S.op 0), (1, S.op 1)] [(1, S.op 1), (0, S.op 0)]) :
    C2Cond O m ∨
      ∃ (ιR' ιS' : Type) (_ : DecidableEq ιR') (_ : DecidableEq ιS') (_ : Fintype ιS')
        (R' : ιR' → ObjSpec) (_ : ∀ j, IsRW (R' j)) (A' : Alg 2 (withRW (ιS := ιS') R' O)),
        Fintype.card ιS' < Fintype.card ιS ∧ WFConsensus A' ∧ TwoShot A' ∧ Allowed m A' := by
  classical
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  obtain ⟨ta, c0, κc0, hnoA, hc0, tb, c1, κc1, hnoB, hc1, D3, D4⟩ := S.c34 hA h2 h0 h1 h01
  obtain ⟨ta', g', κg', hnoA', hg', tb', f', κf', hnoB', hf', D5, D6⟩ := S.c34 hA h2 h0 h1 h10
  have hFG : AgreeAll (.inr S.k) S.F S.G := S.agreeAll_two h0 h1 h01
  have hGF : AgreeAll (.inr S.k) S.G S.F := S.agreeAll_two h0 h1 h10
  -- the edge `{c₀, c₁}`
  have he01 : S.Edge c0 c1 := by
    refine ⟨solo 0 ta ++ solo 1 tb, (solo_crashFree 0 ta).append (solo_crashFree 1 tb),
      fun p => ?_, ⟨κc0, ?_⟩, ⟨κc1, ?_⟩⟩
    · rw [accCount_append]
      fin_cases p
      · simp only [Fin.zero_eta]
        rw [solo_accCount_self hnoA, solo_accCount_other h01]
      · simp only [Fin.mk_one]
        rw [solo_accCount_other h10, solo_accCount_self hnoB]
    · rw [run_append, solo_loc_other h01]; exact hc0
    · rw [run_append]; exact hc1
  -- the edge `{f', g'}` (computed from `gf`, transferred to `fg`)
  have heFG : S.Edge f' g' := by
    set γ : List (Ev 2) := solo 1 ta' ++ solo 0 tb' with hγ
    have hγc : CrashFree γ := (solo_crashFree 1 ta').append (solo_crashFree 0 tb')
    have hnoG : ∀ p, accCount S.G γ p (.inr S.k) = 0 := fun p => by
      rw [hγ, accCount_append]
      fin_cases p
      · simp only [Fin.zero_eta]
        rw [solo_accCount_other h01, solo_accCount_self hnoB']
      · simp only [Fin.mk_one]
        rw [solo_accCount_self hnoA', solo_accCount_other h10]
    have hag := hGF.run γ hγc hnoG
    refine ⟨γ, hγc, accCount_congr_of_agreeAll hGF γ hγc hnoG, ⟨κf', ?_⟩, ⟨κg', ?_⟩⟩
    · rw [← hag.1 0, hγ, run_append]; exact hf'
    · rw [← hag.1 1, hγ, run_append, solo_loc_other h10]; exact hg'
  by_cases hconn : S.Conn (1, g') (0, c0)
  · left
    refine S.c2_of_conn hA h2 hm h0 h1 he01 heFG D3 D4 D5 D6 ?_
    have a1 : S.Conn (1, c1) (0, c0) :=
      Relation.ReflTransGen.single (Or.inr ⟨rfl, rfl, he01⟩)
    have a2 : S.Conn (0, c0) (1, g') := S.conn_symm hconn
    have a3 : S.Conn (1, g') (0, f') := Relation.ReflTransGen.single (Or.inr ⟨rfl, rfl, heFG⟩)
    exact a1.trans (a2.trans a3)
  · right
    let dec : Fin 2 → O.Op → Bool := fun p c => decide (S.Conn (p, c) (0, c0))
    have eF : run (initCfg A S.x) (S.α ++ [.step 0] ++ [.step 1]) = S.F := S.run_two 0 1
    have hβ : CrashFree (S.α ++ [.step 0] ++ [.step 1]) :=
      (S.hα.append (crashFree_single 0)).append (crashFree_single 1)
    refine reduction hR A hA h2 hm S.x _ hβ S.k dec ?_ ?_ ?_ ?_ <;> rw [eF]
    · -- (H1)
      intro γ hγ hno p v hout
      have hag := hFG.run γ hγ hno
      exact S.contra_out' hA h01 (((S.branch_one 0).next 1).ext γ hγ)
        (((S.branch_one 1).next 0).ext γ hγ) (hag.agreeExcept p) hout
    · -- (H2)
      intro γ hγ hno c c' κ κ' hc hc'
      have he : S.Edge c c' := ⟨γ, hγ, hno, ⟨κ, hc⟩, ⟨κ', hc'⟩⟩
      have hadj : S.Adj (0, c) (1, c') := Or.inl ⟨rfl, rfl, he⟩
      simp only [dec, decide_eq_decide]
      constructor
      · intro h; exact (Relation.ReflTransGen.single (S.adj_symm hadj)).trans h
      · intro h; exact (Relation.ReflTransGen.single hadj).trans h
    · -- (H3)
      intro t ht c κ hc
      have := S.first_poised_unique (noAcc_of_accCount_zero ht) hc hnoA hc0
      subst this
      simp [dec, Conn, Relation.ReflTransGen.refl]
    · -- (H3')
      intro t ht c κ hc
      have hnoF : ∀ u < ta', objOf (run S.F (solo 1 u)) 1 ≠ some (.inr S.k) :=
        noAcc_transfer (hGF.agreeExcept 1) hnoA'
      have hg'F : A.act ((run S.F (solo 1 ta')).loc 1) = .access (.inr S.k) g' κg' := by
        rw [← ((hGF.agreeExcept 1).soloRun ta' hnoA').1]; exact hg'
      have := S.first_poised_unique (noAcc_of_accCount_zero ht) hc hnoF hg'F
      subst this
      simpa [dec] using hconn

end KSetup

/-- **Theorem 3 of the paper (necessity).** If objects of type `(O, m)` solve two-shot
two-process consensus (with registers), then `(O, m)` belongs to `C₁`, `C₁.₅` or `C₂`. -/
theorem necessity {O : ObjSpec} {m : Fin 2 → Set O.Op} (h : Solvable O m) :
    C1 O m ∨ C15 O m ∨ C2 O m := by
  rw [classes_iff]
  obtain ⟨ιR, ιS, _, _, _, R, hR, A, hA, h2, hm⟩ := h
  -- strong induction on the number of copies
  induction hN : Fintype.card ιS using Nat.strong_induction_on generalizing ιR ιS R A with
  | _ N ih =>
  classical
  obtain ⟨S, i, hpo⟩ := exists_critSetup hA
  have hp : ∀ p, ∃ o κ, A.act ((run (initCfg A S.x) S.α).loc p) = .access i o κ := hpo
  rcases i with j | k
  · -- both poised on a read/write object: impossible
    exfalso
    obtain ⟨o0, κ0, ho0⟩ := hp 0
    obtain ⟨o1, κ1, ho1⟩ := hp 1
    set E := run (initCfg A S.x) S.α with hE
    have hvq : ∀ p q : Fin 2, p ≠ q → S.val q = !S.val p := by
      intro p q hpq
      have := S.val_ne hpq
      cases h1 : S.val p <;> cases h2 : S.val q <;> simp_all
    -- `p` steps first, then `q`; compared with `q` alone, `q` cannot tell
    have key : ∀ (p q : Fin 2) (hpq : p ≠ q) (op : (R j).Op) (κp : (R j).Resp → A.L)
        (oq : (R j).Op) (κq : (R j).Resp → A.L),
        A.act (E.loc p) = .access (.inl j) op κp → A.act (E.loc q) = .access (.inl j) oq κq →
        ((∀ s, ((R j).δ s op).1 = s) ∨ (∀ s s', (R j).δ s oq = (R j).δ s' oq)) → False := by
      intro p q hpq op κp oq κq hop hoq hcase
      have hoq' : A.act ((E.next (.step p)).loc q) = .access (.inl j) oq κq := by
        rw [next_loc_other E _ (by simpa using hpq.symm)]; exact hoq
      have hs : (withRW (ιS := ιS) R O (.inl j)).δ
          ((withRW (ιS := ιS) R O (.inl j)).δ (E.mem (.inl j)) op).1 oq =
          (withRW (ιS := ιS) R O (.inl j)).δ (E.mem (.inl j)) oq := by
        rcases hcase with h | h
        · exact congrArg (fun s => (R j).δ s oq) (h _)
        · exact h _ _
      have hag : AgreeOn {q} (run (initCfg A S.x) (S.α ++ [.step p] ++ [.step q]))
          (run (initCfg A S.x) (S.α ++ [.step q] ++ [])) := by
        have e1 : run (initCfg A S.x) (S.α ++ [.step q] ++ []) = E.next (.step q) := by
          rw [List.append_nil, run_concat]
        have e2 : run (initCfg A S.x) (S.α ++ [.step p] ++ [.step q]) =
            (E.next (.step p)).next (.step q) := by
          rw [run_concat, run_concat]
        rw [e1, e2]
        exact agreeOn_two_steps hpq hop hoq hs
      exact team_contra hA admOK_crashFree (Reach.initial admOK_crashFree S.x)
        (S.team p) (by rw [← hvq p q hpq]; exact S.team q)
        (InEs.of_crashFree ((S.hα.append (crashFree_single p)).append (crashFree_single q)) 0)
        (InEs.of_crashFree ((S.hα.append (crashFree_single q)).append (fun _ h => by simp at h)) 0) hag
    rcases hR j o0 with h0 | h0
    · exact key 0 1 (by decide) o0 κ0 o1 κ1 ho0 ho1 (Or.inl h0)
    · rcases hR j o1 with h1 | h1
      · exact key 1 0 (by decide) o1 κ1 o0 κ0 ho1 ho0 (Or.inl h1)
      · exact key 0 1 (by decide) o0 κ0 o1 κ1 ho0 ho1 (Or.inr h1)
  · obtain ⟨f, κf, hf⟩ := hp 0
    obtain ⟨g, κg, hg⟩ := hp 1
    let K : KSetup A := ⟨S, k, ![f, g], ![κf, κg], fun p => by fin_cases p <;> simpa⟩
    by_cases hD0 : Dist O K.s 0 [(0, K.op 0), (1, K.op 1)] [(1, K.op 1), (0, K.op 0)]
    · by_cases hD1 : Dist O K.s 1 [(0, K.op 0), (1, K.op 1)] [(1, K.op 1), (0, K.op 0)]
      · exact Or.inl ⟨K.s, K.op 0, K.op 1, K.allowed_crit hm 0, K.allowed_crit hm 1, hD0, hD1⟩
      · exact Or.inr (Or.inl (K.c15 hA h2 hm (by decide) hD0 hD1))
    · by_cases hD1 : Dist O K.s 1 [(0, K.op 0), (1, K.op 1)] [(1, K.op 1), (0, K.op 0)]
      · refine Or.inr (Or.inr (Or.inl (K.c15 hA h2 hm (a := 1) (b := 0) (by decide) ?_ ?_)))
        · exact fun e => hD1 e.symm
        · exact fun e => hD0 e.symm
      · rcases K.c2_or_smaller hR hA h2 hm hD0 hD1 with hc | ⟨ιR', ιS', _, _, _, R', hR', A', hlt,
          hA', h2', hm'⟩
        · exact Or.inr (Or.inr (Or.inr hc))
        · rw [hN] at hlt
          exact ih _ hlt ιR' ιS' _ _ _ R' hR' A' hA' h2' hm' rfl

end TwoShotCons
