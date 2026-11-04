import Papers.PODC2013.TMObservationalRefinement.NonVacuity

/-!
# Theorem 21 is false for Definition 2 as printed

Definition 2 does not require `txcommit` to occur inside a transaction, and Figure 2 lets a thread
continue an atomic block after a method call inside it was aborted (and then try to commit). So a
program can produce a "stray" `txcommit`, which is a non-transactional action. Two stray
`txcommit`s of different threads are unordered by `⊑` but ordered by `∼`; hence `H_C ⊑ H_A` does
not imply `H_C ⊑_trace H_A` (`theorem_21_false_literal`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.TMObservationalRefinement

open IKind Act Lang CmdClass

variable {T LV GV O M BE IE C : Type} [Lang T LV GV BE IE C]

/-- `x := n` is not an `assume` command. -/
lemma assign_not_isAssume (t : T) (x : LV) (n : ℤ) :
    ¬ IsAssume (T := T) (LV := LV) (GV := GV) (BE := BE) (IE := IE) (assign (C := C) t x n) := by
  rintro ⟨u, ⟨b, p, h⟩ | ⟨e, m, h⟩⟩
  all_goals
    have hu : u = t := by
      have := thr_assign (C := C) (GV := GV) (BE := BE) (IE := IE) t x n
      rw [h] at this; simpa using this
    subst hu
    let s : State T LV GV := fun _ => n + 1
    obtain ⟨v, hv⟩ : (sem (assign (C := C) u x n) s).Nonempty := by
      rw [sem_assign]; exact Set.singleton_nonempty _
    have hv1 : v (.inr (u, x)) = n := by
      have := hv; rw [sem_assign, Set.mem_singleton_iff] at this; rw [this]; simp
    rw [h] at hv
    first
    | (rw [sem_assume] at hv; have := congrFun hv.1 (.inr (u, x)); simp [s, hv1] at this)
    | (rw [sem_assumeEq] at hv; have := congrFun hv.1 (.inr (u, x)); simp [s, hv1] at this)

lemma wfThreadLit_of_concat {l : List (IKind O M)} {a : IKind O M} (h : WFThreadLit (l ++ [a])) :
    WFThreadLit l := by
  obtain ⟨hr, ht, hc⟩ := h
  refine ⟨((reqResp_concat _ _).mp hr).1, ?_, ((insideFor_concat _ _ _).mp hc).1⟩
  rw [List.filter_append] at ht
  by_cases hb : a.isBound
  · simp only [List.filter, hb] at ht; exact ((txAlt_concat _ _).mp ht).1
  · simpa [List.filter, hb] using ht

lemma wfThreadLit_of_prefix {l l' : List (IKind O M)} (h : WFThreadLit (l ++ l')) :
    WFThreadLit l := by
  induction l' using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton l' a ih => exact ih (wfThreadLit_of_concat (by simpa using h))

lemma WellFormedLit.of_prefix [DecidableEq T] {h h' : List (IAct T O M)} (hw : WellFormedLit h)
    (hp : h' <+: h) : WellFormedLit h' := by
  obtain ⟨r, rfl⟩ := hp
  intro t
  have := hw t
  simp only [proj, List.filter_append, List.map_append] at this
  exact wfThreadLit_of_prefix this

lemma wfThreadLit_snoc_txcommit {l : List (IKind O M)} (hl : WFThreadLit l) (he : Even l.length) :
    WFThreadLit (l ++ [txcommit]) := by
  obtain ⟨hr, ht, hc⟩ := hl
  refine ⟨(reqResp_concat _ _).mpr ⟨hr, fun _ => rfl, fun l' x h ho => ?_⟩, ?_,
    (insideFor_concat _ _ _).mpr ⟨hc, by simp [isCallRet]⟩⟩
  · exact absurd he (Nat.not_even_iff_odd.mpr ho)
  · simpa [List.filter_append, List.filter, isBound] using ht

lemma opac_append_left {P X Y : List (IAct T O M)} (h : Opac X Y) : Opac (P ++ X) (P ++ Y) := by
  induction P with
  | nil => simpa using h
  | cons p P ih =>
    have := Opac.cons_intro (A := []) (B := P ++ X) (S := P ++ Y) (ψ := p) (by simp) (by simpa using ih)
    simpa using this

lemma opac_swap {a b : IAct T O M} (hab : ¬ Constrained a b) : Opac [a, b] [b, a] := by
  have h1 : Opac [a] [a] := by
    have := Opac.cons_intro (A := []) (B := []) (S := []) (ψ := a) (by simp)
      ((opac_nil_left _).mpr rfl)
    simpa using this
  have := Opac.cons_intro (A := [a]) (B := []) (ψ := b) (by simpa using hab) (by simpa using h1)
  simpa using this

/-- The `txcommit` actions of a trace. -/
def isTxcA : Act T O M C → Bool
  | iface _ txcommit => true
  | _ => false

lemma filter_isTxcA (τ : List (Act T O M C)) :
    τ.filter isTxcA = ((history τ).filter (fun p => p.2.isTxcommit)).map (fun p => iface p.1 p.2) := by
  induction τ with
  | nil => rfl
  | cons a τ ih =>
    cases a with
    | cmd => simp [List.filter_cons, isTxcA, ih]
    | iface u k => cases k <;> simp [List.filter_cons, isTxcA, ih, isTxcommit]

lemma evalSet_nonempty (S : Set (State T LV GV)) (l : List (Act T O M C)) (hS : S.Nonempty)
    (h : ∀ σ, ∀ a ∈ l, (eval1 σ a).Nonempty) : (evalSet S l).Nonempty := by
  induction l generalizing S with
  | nil => exact hS
  | cons a l ih =>
    apply ih _ _ (fun σ b hb => h σ b (by simp [hb]))
    obtain ⟨σ, hσ⟩ := hS
    obtain ⟨σ', hσ'⟩ := h σ a (by simp)
    exact ⟨σ', σ, hσ, hσ'⟩

variable [DecidableEq T] [Fintype T]

/-- **Theorem 21 is false for Definition 2 as printed.** With two threads `t₁ ≠ t₂` both running
`x := atomic { x := o.f(1); x := 1 }`, the trace in which both calls abort, both threads go on
(Figure 2) with `x := 1` and then both issue a `txcommit` has the history
`H = H₈ (t₁, txcommit) (t₂, txcommit)`, which is well-formed in the printed sense. Let `H_C` be the
prefixes of `H` and `H_A` the prefixes of `S = H₈ (t₂, txcommit) (t₁, txcommit)` and of
`H₈ (t₁, txcommit)`. Both are transactional systems (printed Definition 2) and `H_C ⊑ H_A`, but the
two stray `txcommit`s are non-transactional, so no trace with a history in `H_A` is
observationally equivalent to the trace of `H`. -/
theorem theorem_21_false_literal (t₁ t₂ : T) (hne : t₁ ≠ t₂) (o : O) (f : M) (x : LV) :
    ∃ HC HA : Set (List (IAct T O M)), IsTSLit HC ∧ IsTSLit HA ∧ OpacRel HC HA ∧
      ¬ TraceRef (LV := LV) (GV := GV) (C := C) (BE := BE) (IE := IE) O M HC HA := by
  let H8 : List (IAct T O M) := [(t₁, txbegin), (t₁, ok), (t₁, .call o f 1), (t₁, aborted),
    (t₂, txbegin), (t₂, ok), (t₂, .call o f 1), (t₂, aborted)]
  let H9 := H8 ++ [(t₁, txcommit)]
  let H := H9 ++ [(t₂, txcommit)]
  let S9 := H8 ++ [(t₂, txcommit)]
  let S := S9 ++ [(t₁, txcommit)]
  have hprojHS : ∀ u, proj u S = proj u H := by
    intro u
    by_cases h1 : u = t₁
    · subst h1; simp [proj, S, S9, H, H9, H8, List.filter_cons, Ne.symm hne]
    by_cases h2 : u = t₂
    · subst h2; simp [proj, S, S9, H, H9, H8, List.filter_cons, hne]
    · simp [proj, S, S9, H, H9, H8, List.filter_cons, Ne.symm h1, Ne.symm h2]
  have hwfH : WellFormedLit H := by
    have base : WFThread ([txbegin, ok, .call o f 1, aborted] : List (IKind O M)) := by
      rw [wfThread_iff_run]; simp [TState.step]
    have base' := wfThreadLit_snoc_txcommit base.1 (by simp [Nat.even_iff])
    intro u
    by_cases h1 : u = t₁
    · subst h1; simpa [proj, H, H9, H8, List.filter_cons, Ne.symm hne] using base'
    by_cases h2 : u = t₂
    · subst h2; simpa [proj, H, H9, H8, List.filter_cons, hne] using base'
    · simpa [proj, H, H9, H8, List.filter_cons, Ne.symm h1, Ne.symm h2] using wfThreadLit_nil
  have hwfS : WellFormedLit S := fun u => by rw [hprojHS]; exact hwfH u
  refine ⟨{h | h <+: H}, {h | h <+: S ∨ h <+: H9}, ⟨fun h hh => hwfH.of_prefix hh,
    fun h hh h' hp => hp.trans hh⟩, ⟨fun h hh => ?_, fun h hh h' hp => ?_⟩, ?_, ?_⟩
  · rcases hh with hh | hh
    · exact hwfS.of_prefix hh
    · exact hwfH.of_prefix (hh.trans ⟨_, rfl⟩)
  · rcases hh with hh | hh
    · exact Or.inl (hp.trans hh)
    · exact Or.inr (hp.trans hh)
  · -- `H_C ⊑ H_A`
    intro h hh
    rcases List.prefix_concat_iff.mp hh with rfl | hh
    · refine ⟨S, Or.inl (List.prefix_refl _), ?_⟩
      have := opac_append_left (P := H8) (opac_swap (a := ((t₁, txcommit) : IAct T O M))
        (b := (t₂, txcommit)) (by simp [Constrained, hne, isEnd]))
      simpa [H, H9, S, S9] using this
    · exact ⟨h, Or.inr hh, Opac.refl h⟩
  · -- `¬ H_C ⊑_trace H_A`
    intro href
    let body : Cmd LV O M C BE IE := .seq (.call x o f (cst C 1)) (.prim (assign (C := C) t₁ x 1))
    let P : Prog T LV O M C BE IE := fun u =>
      .atomic x (.seq (.call x o f (cst C 1)) (.prim (assign u x 1)))
    have hP : P.Allowed := fun u => by
      simp only [P, Cmd.Allowed, true_and, and_true]
      exact ⟨by simp, by simp, assign_not_isAssume u x 1⟩
    let seg : T → List (Act T O M C) := fun u =>
      [.iface u .txbegin, .iface u .ok, .cmd u (assumeEq u (cst C 1) 1), .iface u (.call o f 1),
        .iface u .aborted]
    let τH : List (Act T O M C) := seg t₁ ++ seg t₂ ++
      [.cmd t₁ (assign t₁ x 1), .iface t₁ .txcommit, .cmd t₂ (assign t₂ x 1), .iface t₂ .txcommit]
    have hfull : ∀ u, Tr u (P u) (seg u ++ [.cmd u (assign u x 1), .iface u .txcommit,
        .iface u .committed, .cmd u (assign u x (vCom C))]) := by
      intro u
      have hb : Tr u (.seq (.call x o f (cst C 1)) (.prim (assign u x 1)) : Cmd LV O M C BE IE)
          ([.cmd u (assumeEq u (cst C 1) 1), .iface u (.call o f 1), .iface u .aborted] ++
            [.cmd u (assign u x 1)]) := Tr.seq (Tr.callAbort 1) (Tr.prim _)
      have := Tr.atomicCommit (x := x) hb (by
        intro τ' h
        have := congrArg List.getLast? h
        simp at this)
      simpa [seg] using this
    have hInA : InA P τH := by
      apply inA_of_ext
      intro u
      by_cases h1 : u = t₁
      · subst h1
        exact ⟨[.iface u .committed, .cmd u (assign u x (vCom C))], by
          simpa [τH, seg, tproj, List.filter_cons, Ne.symm hne] using hfull u⟩
      by_cases h2 : u = t₂
      · subst h2
        exact ⟨[.iface u .committed, .cmd u (assign u x (vCom C))], by
          simpa [τH, seg, tproj, List.filter_cons, hne] using hfull u⟩
      · exact ⟨_, by simpa [τH, seg, tproj, List.filter_cons, Ne.symm h1, Ne.symm h2] using hfull u⟩
    let s : State T LV GV := fun _ => 0
    have hev : eval s τH ≠ ∅ := by
      apply Set.Nonempty.ne_empty
      apply evalSet_nonempty _ _ (Set.singleton_nonempty s)
      intro σ a ha
      simp only [τH, seg, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ((h | h | h | h | h) | (h | h | h | h | h)) | h | h | h | h <;> subst h <;>
        simp [eval1, sem_assumeEq, sem_assign]
    have hhist : history τH = H := by
      simp [τH, seg, history, H, H9, H8, Act.toI, List.filterMap_cons]
    obtain ⟨τ', ⟨-, hτ'⟩, hobs⟩ := href P hP s τH ⟨⟨hInA, hev⟩, by
      show history τH <+: H; rw [hhist]⟩
    -- the history of `τ'` is `S`
    have hmem : ∀ u k, (u, k) ∈ H → (u, k) ∈ history τ' := by
      intro u k hk
      have : iface u k ∈ tproj u τH := by
        rw [← hhist] at hk
        simp only [history, List.mem_filterMap] at hk
        obtain ⟨a, ha, hak⟩ := hk
        cases a with
        | cmd => simp [Act.toI] at hak
        | iface u' k' =>
          simp [Act.toI] at hak; obtain ⟨rfl, rfl⟩ := hak
          simp [tproj, ha]
      rw [hobs.1 u] at this
      simp only [tproj, List.mem_filter] at this
      simp only [history, List.mem_filterMap]
      exact ⟨_, this.1, rfl⟩
    have hS : history τ' = S := by
      have h1 := hmem t₁ txcommit (by simp [H, H9])
      have h2 := hmem t₂ txcommit (by simp [H])
      rcases hτ' with hp | hp
      · rcases List.prefix_concat_iff.mp hp with e | hp
        · exact e
        · have := hp.subset h1; simp [S9, H8, hne] at this
      · have := hp.subset h2; simp [H9, H8, Ne.symm hne] at this
    -- flags of `txcommit`s in `τ'` are `false`
    have hflag : ∀ p ∈ ann (fun _ => false) τ', isTxcA p.1 = true → p.2 = false := by
      intro p hp hq
      have hp' : p ∈ (ann (fun _ => false) τ').filter (fun q => q.1.thread = p.1.thread) := by
        simp [hp]
      rw [ann_tproj, ← hobs.1, ← ann_tproj] at hp'
      have hp'' := List.mem_of_mem_filter hp'
      simp [τH, seg, ann, flag, upd, Act.isBoundA, isBound, Function.update_apply, hne,
        Ne.symm hne] at hp''
      rcases p with ⟨a, b⟩
      simp only at hq ⊢
      rcases hp'' with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        simp_all [isTxcA]
    have key : ∀ τ : List (Act T O M C), (∀ p ∈ ann (fun _ => false) τ, isTxcA p.1 = true → p.2 = false) →
        (nontrans τ).filter isTxcA = τ.filter isTxcA := by
      intro τ hτ
      simp only [nontrans, nontransFrom]
      conv_rhs => rw [← map_fst_ann (fun _ => false) τ]
      rw [← filter_map_fst, ← filter_map_fst, List.filter_filter]
      congr 1
      apply List.filter_congr
      intro p hp
      by_cases hq : isTxcA p.1 = true
      · simp [hq, hτ p hp hq]
      · simp [hq]
    have e1 := key τ' hflag
    have e2 : (nontrans τH).filter isTxcA = τH.filter isTxcA := by
      apply key
      intro p hp hq
      simp [τH, seg, ann, flag, upd, Act.isBoundA, isBound, Function.update_apply, hne,
        Ne.symm hne] at hp
      rcases p with ⟨a, b⟩
      simp only at hq ⊢
      rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp_all [isTxcA]
    have := congrArg (List.filter isTxcA) hobs.2
    rw [e2, e1, filter_isTxcA, filter_isTxcA, hS, hhist] at this
    simp [H, H9, H8, S, S9, isTxcommit] at this
    exact hne this.1

end Podc.TMObservationalRefinement
