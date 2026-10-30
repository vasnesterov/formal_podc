import Papers.PODC2021.ExtensionBasedReductions.Prover

/-!
# Theorem 1: correctness of the simulating prover

The invariant `SimInv` between the history of the simulated interaction of `𝒫_T` with
`h ∘ A ∘ A₁` and the history of the interaction of `𝒫` with `A`:
* every configuration `C` reached by `𝒫_T` has its `A`-part `toA C` reached by `𝒫` (the invariant of
  Section 7 of the paper, with canonical inputs);
* every configuration reached by `𝒫` consists of states whose decision values `𝒫` has seen;
* the protocols' responses so far are correct, and the usual game invariants hold.
-/

namespace Podc.ExtensionBasedReductions

open Cslib.NIS

open St

variable {P XT M ZS ZT : Type} [DecidableEq P] [Inhabited XT] [Inhabited M]

section Generic
variable {δA : Protocol P M ZS}

lemma ginv_fold {gs : GState P M} (hg : GInv δA gs) :
    ∀ {w : List (AMv P M ZS × ARp P M ZS)}, LegalRun (assignSpec (P := P)) δA gs w →
      GInv δA (w.foldl (fun g e => g.next e.1) gs)
  | [], _ => hg
  | e :: w, hw => by simpa using ginv_fold (hg.next hw.1) hw.2

lemma valid_configs {w : List (AMv P M ZS × ARp P M ZS)}
    (hw : ∀ e ∈ w, ValidResp (assignSpec (P := P)) δA e.1 e.2) :
    ∀ e ∈ w, ∀ D o, e.2 = .config D o → o = outs δA D := by
  intro e he D o heq
  have := hw e he
  rcases e with ⟨m, r⟩
  cases m with
  | query C q => simp only [ValidResp] at this; rw [this] at heq; cases heq; rfl
  | oracle C o' => obtain ⟨a, ha, -⟩ := this; simp only at ha heq; rw [ha] at heq; cases heq
  | endPhase C => simp only [ValidResp] at this heq; rw [this] at heq; cases heq

lemma legal_dummy {gs : GState P M} (hg : GInv δA gs) :
    Legal (assignSpec (P := P)) δA gs (dummy gs.base) :=
  ⟨Or.inl ⟨inputs gs.base, (reinit_inputs_self hg.1).symm⟩, fun q hq => by simp at hq⟩

end Generic

variable [Fintype P] [Finite ZS]
variable {δ1 : Protocol P XT M} {t : ℕ} {δA : Protocol P M ZS} {post : P → ZS → ZT}

/-- The invariant of the simulation. -/
structure SimInv (δ1 : Protocol P XT M) (t : ℕ) (δA : Protocol P M ZS) (post : P → ZS → ZT)
    (hs : List (YMv P XT ZT × YRp P XT ZT)) (ht : List (AMv P M ZS × ARp P M ZS)) : Prop where
  ginvY : GInv (compP δ1 t δA post) (statesOf hs)
  ginvA : GInv δA (statesOf ht)
  reach : ∀ C, (statesOf hs).Reached C → (statesOf ht).Reached (toA δ1 t C)
  valid : ∀ e ∈ ht, ∀ D o, e.2 = .config D o → o = outs δA D
  cover : ∀ D, (statesOf ht).Reached D → ∀ j, (D j).IsInit ∨ ∃ z, Reveals ht (D j) z

lemma simInv_init : SimInv δ1 t δA post [] [] where
  ginvY := GInv.start
  ginvA := GInv.start
  reach := fun C hC => by
    rcases hC with ⟨u, rfl⟩ | hC
    · refine Or.inl ⟨inputs (toA δ1 t (reinit (initC default) u)), ?_⟩
      show toA δ1 t (reinit (initC default) u) =
        reinit (initC default) (inputs (toA δ1 t (reinit (initC default) u)))
      rw [reinit_initC, reinit_initC]
      funext j
      have : toA δ1 t (initC u) j = init j (ucan δ1 t (initC u) j) := by
        unfold toA toAC; simp [truncS, initC]
      simp [initC, inputs, this, St.input]
    · simp [statesOf, GState.start] at hC
  valid := by simp
  cover := fun D hD j => by
    rcases hD with ⟨u, rfl⟩ | hD
    · left; simp [statesOf, GState.start, reinit, initC]
    · simp [statesOf, GState.start] at hD

/-- `valid` and `cover` after a window that keeps the base. -/
lemma valid_cover_window {ht0 w : List (AMv P M ZS × ARp P M ZS)}
    (hv0 : ∀ e ∈ ht0, ∀ D o, e.2 = .config D o → o = outs δA D)
    (hc0 : ∀ D, (statesOf ht0).Reached D → ∀ j, (D j).IsInit ∨ ∃ z, Reveals ht0 (D j) z)
    (hw : ∀ e ∈ w, ValidResp (assignSpec (P := P)) δA e.1 e.2)
    (hbase : (statesOf (ht0 ++ w)).base = (statesOf ht0).base)
    (hresp : ∀ D ∈ (statesOf (ht0 ++ w)).resp, D ∈ (statesOf ht0).resp ∨ ∃ e ∈ w, ∃ o, e.2 = .config D o) :
    (∀ e ∈ ht0 ++ w, ∀ D o, e.2 = .config D o → o = outs δA D) ∧
    (∀ D, (statesOf (ht0 ++ w)).Reached D → ∀ j, (D j).IsInit ∨ ∃ z, Reveals (ht0 ++ w) (D j) z) := by
  refine ⟨fun e he => ?_, fun D hD j => ?_⟩
  · rcases List.mem_append.1 he with he | he
    · exact hv0 e he
    · exact valid_configs hw e he
  · have mono : ∀ D, (statesOf ht0).Reached D →
        (D j).IsInit ∨ ∃ z, Reveals (ht0 ++ w) (D j) z := fun D hD => by
      rcases hc0 D hD j with h | ⟨z, hz⟩
      · exact Or.inl h
      · exact Or.inr ⟨z, reveals_mono hz w⟩
    rcases hD with ⟨u, rfl⟩ | hD
    · exact mono _ (Or.inl ⟨u, by rw [hbase]⟩)
    · rcases hresp D hD with hD' | ⟨e, he, o, heo⟩
      · exact mono _ (Or.inr hD')
      · exact Or.inr ⟨o j, e, List.mem_append_right _ he, D, o, j, heo, rfl, rfl⟩

section Cases
variable (hIS : IsIS δ1 t) (ht : 0 < t) (hw : WaitFree δ1)
include hIS ht hw

/-- A query of `𝒫_T` in which the process takes a step of `A`. -/
lemma step_queryA {hs : List (YMv P XT ZT × YRp P XT ZT)} {ht0 w : List (AMv P M ZS × ARp P M ZS)}
    {C : Config P XT} {q : P} {r : YRp P XT ZT} (hI : SimInv δ1 t δA post hs ht0)
    (hleg : Legal (assignSpec (P := P)) (compP δ1 t δA post) (statesOf hs) (.query C q))
    (hq : (decided δ1 (trunc t C q)).isSome)
    (hr : ProgRun ht0 (.ask (.query (toA δ1 t C) q) (fun h' => .done (yResp δ1 t post (step C q) h')))
      w r)
    (hv : ∀ e ∈ w, ValidResp (assignSpec (P := P)) δA e.1 e.2) :
    ValidResp (assignSpec (P := P)) (compP δ1 t δA post) (.query C q) r ∧
      LegalRun (assignSpec (P := P)) δA (statesOf ht0) w ∧
      SimInv δ1 t δA post (hs ++ [(.query C q, r)]) (ht0 ++ w) ∧
      w = [(.query (toA δ1 t C) q, .config (step (toA δ1 t C) q) (outs δA (step (toA δ1 t C) q)))] := by
  obtain ⟨hC, hqa⟩ := hleg
  have hRC := hI.ginvY.reach hC
  obtain ⟨hstep, hact, -⟩ := toA_stepA hIS ht hw hRC hq
  cases hr with
  | ask _ _ _ r' w' _ hr' =>
    cases hr'
    have hr0 := hv _ (List.mem_cons.2 (Or.inl rfl))
    simp only [ValidResp] at hr0
    subst hr0
    have hlegA : Legal (assignSpec (P := P)) δA (statesOf ht0) (.query (toA δ1 t C) q) :=
      ⟨hI.reach C hC, hact.1 hqa⟩
    set w : List (AMv P M ZS × ARp P M ZS) :=
      [(.query (toA δ1 t C) q, .config (step (toA δ1 t C) q) (outs δA (step (toA δ1 t C) q)))]
    have hst : statesOf (ht0 ++ w) = (statesOf ht0).next (Move.query (Q := YQ P ZS) (toA δ1 t C) q) := by
      rw [statesOf_append]; rfl
    obtain ⟨hval, hcov⟩ := valid_cover_window hI.valid hI.cover hv (by rw [hst]; rfl) (by
      intro D hD; rw [hst] at hD
      rcases hD with rfl | hD
      · exact Or.inr ⟨_, List.mem_singleton_self _, _, rfl⟩
      · exact Or.inl hD)
    have hreachA : (statesOf (ht0 ++ w)).Reached (step (toA δ1 t C) q) := by
      rw [hst]; exact Or.inr (Set.mem_insert _ _)
    refine ⟨?_, ⟨hlegA, trivial⟩, ⟨?_, ?_, ?_, hval, hcov⟩, rfl⟩
    · -- the response is correct
      show yResp δ1 t post (step C q) (ht0 ++ w) = _
      unfold yResp
      congr 1; funext j
      rw [outs_toA hIS ht hw (hRC.step hqa), hstep]
      rw [know_eq hval (hcov _ hreachA j)]; rfl
    · rw [statesOf_append]
      exact hI.ginvY.next (spec := assignSpec (P := P)) (m := Move.query C q) ⟨hC, hqa⟩
    · rw [hst]; exact hI.ginvA.next hlegA
    · intro C' hC'
      rw [statesOf_append] at hC'
      simp only [List.foldl_cons, List.foldl_nil, GState.next] at hC'
      rcases hC' with ⟨u, hu⟩ | hC'
      · have := hI.reach C' (Or.inl ⟨u, hu⟩)
        rw [hst]
        rcases this with ⟨u', hu'⟩ | h'
        · exact Or.inl ⟨u', hu'⟩
        · exact Or.inr (Set.mem_insert_of_mem _ h')
      · rcases hC' with rfl | hC'
        · rw [hstep]; exact hreachA
        · have := hI.reach C' (Or.inr hC')
          rw [hst]
          rcases this with ⟨u', hu'⟩ | h'
          · exact Or.inl ⟨u', hu'⟩
          · exact Or.inr (Set.mem_insert_of_mem _ h')

omit hIS ht hw in
/-- Re-reaching `reinit D₀ u` (for a reached `D₀`) after a harmless move: the facts we need. -/
lemma reach_window {ht0 : List (AMv P M ZS × ARp P M ZS)} (hgA : GInv δA (statesOf ht0))
    {D0 : Config P M} (hD0 : (statesOf ht0).Reached D0) (u : P → M) (r0 : ARp P M ZS)
    {w1 a : List (AMv P M ZS × ARp P M ZS)}
    (hr : ProgRun (ht0 ++ [(dummy (statesOf ht0).base, r0)])
      (reachP (statesOf ht0).base (reinit D0 u) (ht0 ++ [(dummy (statesOf ht0).base, r0)])) w1 a)
    (hv : ∀ e ∈ w1, ValidResp (assignSpec (P := P)) δA e.1 e.2) :
    a = ht0 ++ ((dummy (statesOf ht0).base, r0) :: w1) ∧
      LegalRun (assignSpec (P := P)) δA (statesOf ht0) ((dummy (statesOf ht0).base, r0) :: w1) ∧
      (statesOf (ht0 ++ ((dummy (statesOf ht0).base, r0) :: w1))).base = (statesOf ht0).base ∧
      (∀ D, (statesOf ht0).Reached D →
        (statesOf (ht0 ++ ((dummy (statesOf ht0).base, r0) :: w1))).Reached D) ∧
      (statesOf (ht0 ++ ((dummy (statesOf ht0).base, r0) :: w1))).Reached (reinit D0 u) ∧
      (∀ D ∈ (statesOf (ht0 ++ ((dummy (statesOf ht0).base, r0) :: w1))).resp,
        D ∈ (statesOf ht0).resp ∨ ∃ e ∈ (dummy (statesOf ht0).base, r0) :: w1, ∃ o, e.2 = .config D o) := by
  obtain ⟨hex, hsch⟩ := rsched_spec hgA hD0 u
  have hst1 : statesOf (ht0 ++ [(dummy (statesOf ht0).base, r0)]) = statesOf ht0 := by
    rw [statesOf_append]; rfl
  have hstart : (statesOf ht0).Reached (reinit (statesOf ht0).base (inputs (reinit D0 u))) :=
    Or.inl ⟨_, rfl⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := chain_spec (δA := δA) _ _ (statesOf ht0) _ w1 a hr
    hstart hsch hv
  have hst : statesOf (ht0 ++ ((dummy (statesOf ht0).base, r0) :: w1)) =
      w1.foldl (fun g e => g.next e.1) (statesOf ht0) := by
    rw [show ht0 ++ ((dummy (statesOf ht0).base, r0) :: w1) =
      (ht0 ++ [(dummy (statesOf ht0).base, r0)]) ++ w1 by simp, statesOf_append, hst1]
  rw [hex] at h5
  refine ⟨by rw [h1]; simp, ⟨legal_dummy hgA, by simpa [dummy, GState.next] using h2⟩, by rw [hst, h3],
    fun D hD => by rw [hst]; exact h4 D hD, by rw [hst]; exact h5, fun D hD => ?_⟩
  rw [hst] at hD
  rcases h6 D hD with h | ⟨e, he, o, heo⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, o, heo⟩

/-- A query of `𝒫_T` in which the process takes a step of `A₁`. -/
lemma step_queryA1 {hs : List (YMv P XT ZT × YRp P XT ZT)} {ht0 w : List (AMv P M ZS × ARp P M ZS)}
    {C : Config P XT} {q : P} {r : YRp P XT ZT} (hI : SimInv δ1 t δA post hs ht0)
    (hleg : Legal (assignSpec (P := P)) (compP δ1 t δA post) (statesOf hs) (.query C q))
    (hq : ¬ (decided δ1 (trunc t C q)).isSome)
    (hr : ProgRun ht0 (.ask (dummy (statesOf ht0).base) (fun h' =>
        (reachP (statesOf ht0).base (toA δ1 t (step C q)) h').bind fun h'' =>
          .done (yResp δ1 t post (step C q) h''))) w r)
    (hv : ∀ e ∈ w, ValidResp (assignSpec (P := P)) δA e.1 e.2) :
    ValidResp (assignSpec (P := P)) (compP δ1 t δA post) (.query C q) r ∧
      LegalRun (assignSpec (P := P)) δA (statesOf ht0) w ∧
      SimInv δ1 t δA post (hs ++ [(.query C q, r)]) (ht0 ++ w) := by
  obtain ⟨hC, hqa⟩ := hleg
  have hRC := hI.ginvY.reach hC
  have hq' : decided δ1 (trunc t C q) = none := by simpa using hq
  obtain ⟨-, -, hstep⟩ := toA_execA1 (δA := δA) (post := post) hIS ht hw hRC (μ := [q]) ⟨hq', trivial⟩
  simp only [exec_cons, exec_nil] at hstep
  cases hr with
  | ask _ _ _ r0 w' _ hr' =>
    obtain ⟨w1, w2, a, rfl, hr1, hr2⟩ := progRun_bind _ _ hr'
    cases hr2
    simp only [List.append_nil] at hv ⊢
    rw [hstep] at hr1
    obtain ⟨ha, hlr, hbase, hmono, hreachD, hresp⟩ := reach_window hI.ginvA (hI.reach C hC) _ r0 hr1
      (fun e he => hv e (List.mem_cons_of_mem _ he))
    rw [← hstep] at hreachD
    obtain ⟨hval, hcov⟩ := valid_cover_window hI.valid hI.cover hv hbase hresp
    refine ⟨?_, hlr, ⟨?_, by rw [statesOf_append]; exact ginv_fold hI.ginvA hlr, ?_, hval, hcov⟩⟩
    · show yResp δ1 t post (step C q) a = _
      rw [ha]; unfold yResp
      congr 1; funext j
      rw [outs_toA hIS ht hw (hRC.step hqa), know_eq hval (hcov _ hreachD j)]; rfl
    · rw [statesOf_append]
      exact hI.ginvY.next (spec := assignSpec (P := P)) (m := Move.query C q) ⟨hC, hqa⟩
    · intro C' hC'
      rw [statesOf_append] at hC'
      simp only [List.foldl_cons, List.foldl_nil, GState.next] at hC'
      rcases hC' with ⟨u, hu⟩ | hC'
      · exact hmono _ (hI.reach C' (Or.inl ⟨u, hu⟩))
      · rcases hC' with rfl | hC'
        · exact hreachD
        · exact hmono _ (hI.reach C' (Or.inr hC'))

/-- `𝒫_T` ends a phase. -/
lemma step_end {hs : List (YMv P XT ZT × YRp P XT ZT)} {ht0 w : List (AMv P M ZS × ARp P M ZS)}
    {C : Config P XT} {r : YRp P XT ZT} (hI : SimInv δ1 t δA post hs ht0)
    (hleg : Legal (assignSpec (P := P)) (compP δ1 t δA post) (statesOf hs) (.endPhase C))
    (hr : ProgRun ht0 (.ask (handler δ1 t post hs ht0 (.endPhase C)).1
      (handler δ1 t post hs ht0 (.endPhase C)).2) w r)
    (hv : ∀ e ∈ w, ValidResp (assignSpec (P := P)) δA e.1 e.2) :
    ValidResp (assignSpec (P := P)) (compP δ1 t δA post) (.endPhase C) r ∧
      LegalRun (assignSpec (P := P)) δA (statesOf ht0) w ∧
      SimInv δ1 t δA post (hs ++ [(.endPhase C, r)]) (ht0 ++ w) ∧
      ((toA δ1 t C ∈ (statesOf ht0).resp ∧ ∃ r', w = [(.endPhase (toA δ1 t C), r')]) ∨
       ((∃ u, toA δ1 t C = reinit (statesOf ht0).base u) ∧
        ∃ r', w = [(dummy (statesOf ht0).base, r')])) := by
  have hC : C ∈ (statesOf hs).resp := hleg
  have hRC := hI.ginvY.reach (Or.inr hC)
  have hstY : statesOf (hs ++ [(.endPhase C, r)]) = ⟨C, ∅⟩ := by rw [statesOf_append]; rfl
  have hreachY : ∀ C', (statesOf (hs ++ [(.endPhase C, r)])).Reached C' → ∃ x, C' = reinit C x := by
    intro C' hC'; rw [hstY] at hC'
    rcases hC' with ⟨x, hx⟩ | hC'
    · exact ⟨x, hx⟩
    · simp at hC'
  have hginvY : GInv (compP δ1 t δA post) (statesOf (hs ++ [(.endPhase C, r)])) := by
    rw [statesOf_append]
    exact hI.ginvY.next (spec := assignSpec (P := P)) (m := Move.endPhase C) hC
  simp only [handler] at hr
  split_ifs at hr with hin
  · obtain ⟨r', rfl, rfl⟩ := progRun_const hr
    have hlegA : Legal (assignSpec (P := P)) δA (statesOf ht0) (.endPhase (toA δ1 t C)) := hin
    have hstA : statesOf (ht0 ++ [(.endPhase (toA δ1 t C), r')]) = ⟨toA δ1 t C, ∅⟩ := by
      rw [statesOf_append]; rfl
    refine ⟨rfl, ⟨hlegA, trivial⟩, ⟨hginvY, ?_, ?_, ?_, ?_⟩, Or.inl ⟨hin, r', rfl⟩⟩
    · rw [statesOf_append]; exact hI.ginvA.next hlegA
    · intro C' hC'
      obtain ⟨x, rfl⟩ := hreachY C' hC'
      rw [hstA, toA_reinit hIS ht hw hRC]
      exact Or.inl ⟨_, rfl⟩
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact hI.valid e he
      · exact valid_configs hv e he
    · intro D hD j
      rw [hstA] at hD
      rcases hD with ⟨u, rfl⟩ | hD
      · by_cases hi : (toA δ1 t C j).IsInit
        · left; rw [reinit_of_isInit hi]; trivial
        · rw [reinit_of_not_isInit hi]
          rcases hI.cover _ (Or.inr hin) j with h | ⟨z, hz⟩
          · exact Or.inl h
          · exact Or.inr ⟨z, reveals_mono hz _⟩
      · simp at hD
  · obtain ⟨r', rfl, rfl⟩ := progRun_const hr
    have hlegA := legal_dummy hI.ginvA
    have hstA : statesOf (ht0 ++ [(dummy (statesOf ht0).base, r')]) = statesOf ht0 := by
      rw [statesOf_append]; rfl
    obtain ⟨u0, hu0⟩ : ∃ u, toA δ1 t C = reinit (statesOf ht0).base u := by
      rcases hI.reach C (Or.inr hC) with h | h
      · exact h
      · exact absurd h hin
    obtain ⟨hval, hcov⟩ := valid_cover_window hI.valid hI.cover hv (by rw [hstA])
      (by intro D hD; rw [hstA] at hD; exact Or.inl hD)
    refine ⟨rfl, ⟨hlegA, trivial⟩, ⟨hginvY, by rw [hstA]; exact hI.ginvA, ?_, hval, hcov⟩,
      Or.inr ⟨⟨u0, hu0⟩, r', rfl⟩⟩
    intro C' hC'
    obtain ⟨x, rfl⟩ := hreachY C' hC'
    rw [hstA, toA_reinit hIS ht hw hRC, hu0, reinit_reinit]
    exact Or.inl ⟨_, rfl⟩

lemma depth_le_of_reach {C1 : Config P XT} (hC1 : Reach δ1 C1) (j : P) : (C1 j).depth ≤ 2 * t := by
  by_cases hj : (decided δ1 (C1 j)).isSome
  · exact (hC1.depth_fin hIS ht hj).le
  · exact (hC1.depth_unfin hIS ht (by simpa using hj)).le

/-- The candidates for an assignment query form a finite set. -/
lemma candSet_finite {C : Config P XT} (hC : Reach (compP δ1 t δA post) C) (Ps : Finset P)
    (f : P → Option ZT) : (candSet δ1 t post C Ps f).Finite := by
  have hC1 := reach_trunc (δA := δA) (post := post) hIS ht hw hC
  refine ((List.finite_length_le P (Fintype.card P * (2 * t))).prod
    (Set.finite_univ (α := P → Option ZS))).subset ?_
  rintro ⟨μ, g⟩ ⟨-, hμ, -⟩
  refine ⟨?_, Set.mem_univ _⟩
  have hR := hC1.run hμ
  have h1 := measure_exec (trunc t C) μ
  have h2 : totalDepth (exec (trunc t C) μ) ≤ Fintype.card P * (2 * t) := by
    unfold totalDepth
    calc ∑ j, (exec (trunc t C) μ j).depth ≤ ∑ _j : P, 2 * t :=
          Finset.sum_le_sum fun j _ => depth_le_of_reach hIS ht hw hR j
      _ = Fintype.card P * (2 * t) := by simp
  show μ.length ≤ _
  omega

/-- Soundness of the answers to assignment queries. -/
lemma assign_sound {C : Config P XT} (hC : Reach (compP δ1 t δA post) C) {Ps : Finset P}
    {f : P → Option ZT} {c : List P × (P → Option ZS)} (hc : c ∈ candSet δ1 t post C Ps f)
    {μ' : List P} (hμ' : GoodSched δA (toA δ1 t (exec C c.1)) Ps (fun D => Satisfies δA D c.2) μ') :
    GoodSched (compP δ1 t δA post) C Ps (fun D => Satisfies (compP δ1 t δA post) D f) (c.1 ++ μ') := by
  obtain ⟨hPs1, hs1, hfinPs, hg⟩ := hc
  obtain ⟨hPs', hs', hsat⟩ := hμ'
  obtain ⟨hsY1, htrE, -⟩ := toA_execA1 (δA := δA) (post := post) hIS ht hw hC hs1
  have hRE := hC.run hsY1
  obtain ⟨hIE, hEE⟩ := canonY hIS ht hw hRE
  obtain ⟨hsY2, hexY, hIE'⟩ := execY_A (δA := δA) (h := post) hIS ht μ' hIE hs'
    (fun p hp => by rw [htrE]; exact hfinPs p (hPs' p hp))
  rw [← hEE] at hsY2 hexY
  refine ⟨fun p hp => ?_, (isSched_append _ _ _).2 ⟨hsY1, hsY2⟩, fun q z hq => ?_⟩
  · rcases List.mem_append.1 hp with hp | hp
    · exact hPs1 p hp
    · exact hPs' p hp
  · rw [exec_append, hexY, outs_Ycfg hIS ht hIE']
    obtain ⟨hn, hz⟩ := hg q
    cases hgq : c.2 q with
    | none => rw [hn.2 hgq] at hq; cases hq
    | some w =>
      have := hz w hgq
      rw [hq] at this; cases this
      rw [hsat q w hgq]; rfl

/-- Completeness of the answers to assignment queries. -/
lemma assign_complete {C : Config P XT} (hC : Reach (compP δ1 t δA post) C) {Ps : Finset P}
    {f : P → Option ZT}
    (hall : ∀ c ∈ candSet δ1 t post C Ps f,
      ¬ ∃ μ', GoodSched δA (toA δ1 t (exec C c.1)) Ps (fun D => Satisfies δA D c.2) μ') :
    ¬ ∃ μ, GoodSched (compP δ1 t δA post) C Ps (fun D => Satisfies (compP δ1 t δA post) D f) μ := by
  rintro ⟨μ, hPs, hsμ, hsat⟩
  obtain ⟨hI, hE⟩ := canonY hIS ht hw hC
  set C1 := trunc t C
  set CA := toA δ1 t C
  have hsμ' : IsSched (compP δ1 t δA post) (Ycfg δ1 C1 CA) μ := hE ▸ hsμ
  obtain ⟨μ1, μ', u', hm1, hm', hs1, hs', hfin, hI', hEx, -⟩ := decompY hIS ht μ hI hsμ'
  rw [← hE] at hEx
  obtain ⟨ext, hextPs, hext, hextfin⟩ := exists_complete hIS ht hI'.reach Ps
  set FinalA := exec (reinit CA u') μ'
  have hsatA : ∀ q z, f q = some z → ∃ w, outs δA FinalA q = some w ∧ post q w = z := by
    intro q z hq
    have := hsat q z hq
    rw [hEx, outs_Ycfg hIS ht hI'] at this
    cases ho : outs δA FinalA q with
    | none => rw [ho] at this; cases this
    | some w => rw [ho] at this; cases this; exact ⟨w, rfl, rfl⟩
  let gs : P → Option ZS := fun q => if f q = none then none else outs δA FinalA q
  have hsched : IsSched δ1 C1 (μ1 ++ ext) := (isSched_append _ _ _).2 ⟨hs1, hext⟩
  have hc : (μ1 ++ ext, gs) ∈ candSet δ1 t post C Ps f := by
    refine ⟨fun p hp => ?_, hsched, fun p hp => by rw [exec_append]; exact hextfin p hp,
      fun q => ⟨?_, fun z hz => ?_⟩⟩
    · rcases List.mem_append.1 hp with hp | hp
      · exact hPs p (hm1 p hp)
      · exact hextPs p hp
    · simp only [gs]
      split_ifs with hfq
      · simp [hfq]
      · obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hfq
        obtain ⟨w, hw', -⟩ := hsatA q z hz
        simp [hfq, hw']
    · simp only [gs] at hz
      split_ifs at hz with hfq
      obtain ⟨z0, hz0⟩ := Option.ne_none_iff_exists'.1 hfq
      obtain ⟨w, hw', hpw⟩ := hsatA q z0 hz0
      rw [hw'] at hz; cases hz
      rw [hz0, hpw]
  apply hall _ hc
  obtain ⟨-, htr, htoA⟩ := toA_execA1 (δA := δA) (post := post) hIS ht hw hC hsched
  set uP := ucan δ1 t (exec C (μ1 ++ ext))
  have hagree : ∀ j ∈ μ', uP j = u' j := by
    intro j hj
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (hfin j hj)
    have h1 := (hI'.fin j y hy).1
    have h2 : decided δ1 (exec C1 (μ1 ++ ext) j) = some y := by
      rw [exec_append, exec_of_terminated hext (by rw [hy]; simp), hy]
    rw [← h1]
    exact ucan_fin hw (by rw [htr]; exact hsched |> (hI.reach.run)) (by rw [htr]; exact h2)
  have key := exec_reinit (δ := δA) (reinit CA u') uP (α := μ') (fun j hj hi => by
    rw [reinit_of_isInit ((isInit_reinit_iff _ _ _).1 hi), hagree j hj])
  rw [reinit_reinit] at key
  refine ⟨μ', hm' |> fun h p hp => hPs p (h p hp), ?_, fun q w hq => ?_⟩
  · simp only
    rw [htoA, key.2]; exact hs'
  · simp only
    rw [htoA, key.1]
    simp only [gs] at hq
    split_ifs at hq with hfq
    have hni : ¬ (FinalA q).IsInit := by
      intro hi; obtain ⟨i, x, hx⟩ := (St.isInit_iff _).1 hi
      unfold outs at hq; rw [hx] at hq; simp at hq
    unfold outs; rw [reinit_of_not_isInit hni]; exact hq

omit hIS ht hw in
lemma legalRun_append {gs : GState P M} :
    ∀ {w1 w2 : List (AMv P M ZS × ARp P M ZS)},
      LegalRun (assignSpec (P := P)) δA gs w1 →
      LegalRun (assignSpec (P := P)) δA (w1.foldl (fun g e => g.next e.1) gs) w2 →
      LegalRun (assignSpec (P := P)) δA gs (w1 ++ w2)
  | [], _, _, h2 => h2
  | e :: w1, _, h1, h2 => ⟨h1.1, legalRun_append (gs := gs.next e.1) h1.2 (by simpa using h2)⟩

/-- Running the candidate loop. -/
lemma aloop_spec {C : Config P XT} (hC : Reach (compP δ1 t δA post) C) {Ps : Finset P}
    {f : P → Option ZT} (hf : ∀ q, (f q).isSome → q ∈ Ps) :
    ∀ (cs : List (List P × (P → Option ZS))) (gs : GState P M) (hcur w : List (AMv P M ZS × ARp P M ZS))
      (r : YRp P XT ZT), GInv δA gs → gs.Reached (toA δ1 t C) →
      (∀ c ∈ cs, c ∈ candSet δ1 t post C Ps f) →
      ProgRun hcur (aloop δ1 t gs.base C Ps cs hcur) w r →
      (∀ e ∈ w, ValidResp (assignSpec (P := P)) δA e.1 e.2) →
      LegalRun (assignSpec (P := P)) δA gs w ∧ (w.foldl (fun g e => g.next e.1) gs).base = gs.base ∧
      (∀ D, gs.Reached D → (w.foldl (fun g e => g.next e.1) gs).Reached D) ∧
      (∀ D ∈ (w.foldl (fun g e => g.next e.1) gs).resp, D ∈ gs.resp ∨ ∃ e ∈ w, ∃ o, e.2 = .config D o) ∧
      ∃ a, r = .answer a ∧
        (∀ μ, a = some μ → ∃ c ∈ cs, ∃ μ', μ = c.1 ++ μ' ∧
          GoodSched δA (toA δ1 t (exec C c.1)) Ps (fun D => Satisfies δA D c.2) μ') ∧
        (a = none → ∀ c ∈ cs,
          ¬ ∃ μ', GoodSched δA (toA δ1 t (exec C c.1)) Ps (fun D => Satisfies δA D c.2) μ')
  | [], gs, hcur, w, r, _, _, _, hr, _ => by
    cases hr
    exact ⟨trivial, rfl, fun D hD => hD, fun D hD => Or.inl hD, none, rfl, by simp, by simp⟩
  | (μ1, g) :: cs, gs, hcur, w, r, hg, hCA, hcs, hr, hv => by
    obtain ⟨w1, w2, a, rfl, hr1, hr2⟩ := progRun_bind _ _ hr
    have hc := hcs _ (List.mem_cons.2 (Or.inl rfl))
    obtain ⟨-, hs1, -, hgq⟩ := hc
    obtain ⟨-, -, htoA⟩ := toA_execA1 (δA := δA) (post := post) hIS ht hw hC hs1
    set D := toA δ1 t (exec C μ1)
    obtain ⟨hex, hsch⟩ := rsched_spec hg hCA (ucan δ1 t (exec C μ1))
    rw [← htoA] at hex hsch
    obtain ⟨-, h2, h3, h4, h5, h6, -, -⟩ := chain_spec (δA := δA) _ _ gs _ w1 a hr1
      (Or.inl ⟨_, rfl⟩) hsch (fun e he => hv e (List.mem_append_left _ he))
    rw [hex] at h5
    set gs1 := w1.foldl (fun g e => g.next e.1) gs
    cases hr2 with
    | ask _ _ _ r2 w3 _ hr3 =>
      have hv2 := hv _ (List.mem_append_right _ (List.mem_cons.2 (Or.inl rfl)))
      obtain ⟨a2, rfl, ha2⟩ := hv2
      have hlegO : Legal (assignSpec (P := P)) δA gs1 (.oracle D (Ps, g)) := by
        refine ⟨h5, fun q hq => hf q ?_⟩
        cases hfq : f q with
        | none => rw [((hgq q).1.1 hfq)] at hq; cases hq
        | some z => rfl
      have hgs1 : (gs1.next (Move.oracle (Q := YQ P ZS) D (Ps, g))) = gs1 := rfl
      simp only [lastResp_concat] at hr3
      cases a2 with
      | some μ' =>
        simp only at hr3
        cases hr3
        have hst : ((w1 ++ [(Move.oracle D (Ps, g), Resp.answer (some μ'))]).foldl
            (fun (g : GState P M) (e : AMv P M ZS × ARp P M ZS) => g.next e.1) gs) = gs1 := by simp [gs1, List.foldl_append, GState.next]
        refine ⟨legalRun_append h2 ⟨hlegO, trivial⟩, by rw [hst, h3], fun D' hD' => by
          rw [hst]; exact h4 D' hD', fun D' hD' => ?_, some (μ1 ++ μ'), rfl, fun μ hμ => ?_, by simp⟩
        · rw [hst] at hD'
          rcases h6 D' hD' with h | ⟨e, he, o, heo⟩
          · exact Or.inl h
          · exact Or.inr ⟨e, List.mem_append_left _ he, o, heo⟩
        · cases hμ; exact ⟨(μ1, g), List.mem_cons.2 (Or.inl rfl), μ', rfl, ha2⟩
      | none =>
        simp only at hr3
        have hg1 : GInv δA gs1 := ginv_fold hg h2
        obtain ⟨i1, i2, i3, i4, a, rfl, i5, i6⟩ := aloop_spec hC hf cs gs1 _ w3 r hg1 (h4 _ hCA)
          (fun c hc' => hcs c (List.mem_cons_of_mem _ hc')) (by rw [h3]; exact hr3)
          (fun e he => hv e (List.mem_append_right _ (List.mem_cons_of_mem _ he)))
        have hst : ((w1 ++ (Move.oracle D (Ps, g), Resp.answer none) :: w3).foldl
            (fun (g : GState P M) (e : AMv P M ZS × ARp P M ZS) => g.next e.1) gs) =
            w3.foldl (fun g e => g.next e.1) gs1 := by
          simp [gs1, List.foldl_append, GState.next]
        refine ⟨legalRun_append h2 ⟨hlegO, i1⟩, by rw [hst, i2, h3], fun D' hD' => by
          rw [hst]; exact i3 D' (h4 D' hD'), fun D' hD' => ?_, a, rfl, fun μ hμ => ?_, fun ha c hc' => ?_⟩
        · rw [hst] at hD'
          rcases i4 D' hD' with h | ⟨e, he, o, heo⟩
          · rcases h6 D' h with h' | ⟨e, he, o, heo⟩
            · exact Or.inl h'
            · exact Or.inr ⟨e, List.mem_append_left _ he, o, heo⟩
          · exact Or.inr ⟨e, List.mem_append_right _ (List.mem_cons_of_mem _ he), o, heo⟩
        · obtain ⟨c, hc', rest⟩ := i5 μ hμ
          exact ⟨c, List.mem_cons_of_mem _ hc', rest⟩
        · rcases List.mem_cons.1 hc' with rfl | hc'
          · exact ha2
          · exact i6 ha c hc'

lemma mem_cands_iff {C : Config P XT} (hC : Reach (compP δ1 t δA post) C) (Ps : Finset P)
    (f : P → Option ZT) (c : List P × (P → Option ZS)) :
    c ∈ cands δ1 t post C Ps f ↔ c ∈ candSet δ1 t post C Ps f := by
  unfold cands; rw [dif_pos (candSet_finite hIS ht hw hC Ps f)]; simp

/-- An assignment query of `𝒫_T`. -/
lemma step_oracle {hs : List (YMv P XT ZT × YRp P XT ZT)} {ht0 w : List (AMv P M ZS × ARp P M ZS)}
    {C : Config P XT} {o : YQ P ZT} {r : YRp P XT ZT} (hI : SimInv δ1 t δA post hs ht0)
    (hleg : Legal (assignSpec (P := P)) (compP δ1 t δA post) (statesOf hs) (.oracle C o))
    (hr : ProgRun ht0 (.ask (dummy (statesOf ht0).base) (fun h' =>
      aloop δ1 t (statesOf ht0).base C o.1 (cands δ1 t post C o.1 o.2) h')) w r)
    (hv : ∀ e ∈ w, ValidResp (assignSpec (P := P)) δA e.1 e.2) :
    ValidResp (assignSpec (P := P)) (compP δ1 t δA post) (.oracle C o) r ∧
      LegalRun (assignSpec (P := P)) δA (statesOf ht0) w ∧
      SimInv δ1 t δA post (hs ++ [(.oracle C o, r)]) (ht0 ++ w) := by
  obtain ⟨hC, hf⟩ := hleg
  have hRC := hI.ginvY.reach hC
  cases hr with
  | ask _ _ _ r0 w' _ hr' =>
    obtain ⟨i1, i2, i3, i4, a, rfl, i5, i6⟩ := aloop_spec hIS ht hw hRC hf _ (statesOf ht0) _ w' _
      hI.ginvA (hI.reach C hC) (fun c hc => (mem_cands_iff hIS ht hw hRC _ _ c).1 hc) hr'
      (fun e he => hv e (List.mem_cons_of_mem _ he))
    have hlr : LegalRun (assignSpec (P := P)) δA (statesOf ht0)
        ((dummy (statesOf ht0).base, r0) :: w') :=
      ⟨legal_dummy hI.ginvA, by simpa [dummy, GState.next] using i1⟩
    have hst : statesOf (ht0 ++ (dummy (statesOf ht0).base, r0) :: w') =
        w'.foldl (fun g e => g.next e.1) (statesOf ht0) := by
      rw [statesOf_append]; rfl
    obtain ⟨hval, hcov⟩ := valid_cover_window hI.valid hI.cover hv (by rw [hst, i2]) (by
      intro D hD; rw [hst] at hD
      rcases i4 D hD with h | ⟨e, he, o', heo⟩
      · exact Or.inl h
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, o', heo⟩)
    have hstY : statesOf (hs ++ [(.oracle C o, Resp.answer a)]) = statesOf hs := by
      rw [statesOf_append]; rfl
    refine ⟨⟨a, rfl, ?_⟩, hlr, ⟨by rw [hstY]; exact hI.ginvY,
      by rw [statesOf_append]; exact ginv_fold hI.ginvA hlr, fun C' hC' => ?_, hval, hcov⟩⟩
    · cases a with
      | some μ =>
        obtain ⟨c, hc, μ', rfl, hg⟩ := i5 μ rfl
        exact assign_sound hIS ht hw hRC ((mem_cands_iff hIS ht hw hRC _ _ c).1 hc) hg
      | none =>
        exact assign_complete hIS ht hw hRC
          (fun c hc => i6 rfl c ((mem_cands_iff hIS ht hw hRC _ _ c).2 hc))
    · rw [hstY] at hC'
      rw [hst]; exact i3 _ (hI.reach C' hC')

end Cases

end Podc.ExtensionBasedReductions
