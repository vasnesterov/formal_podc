import Papers.PODC2017.RegisterEmulationSpace.Algorithm2SafetySteps

/-!
# Algorithm 2 is safe in sequential runs (`Alg.SeqSafe`)
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace.Alg2

open Finset Function

variable {C B S V : Type*} [DecidableEq C] [LinearOrder B] [Fintype B] [Fintype S] [DecidableEq S]

local notation "Cf" => Cfg C B V (ℕ × V) (Loc B V)

variable (δ : B → S) (f : ℕ) (R : C → Finset B) (v₀ : V) (Wr : Finset C)

lemma hist_step (X : Cf) (e : Ev C V) :
    ∃ D : List (HEv C V), ((alg δ f R v₀).step X e).hist = X.hist ++ D ∧ D.length ≤ 1 := by
  cases e with
  | inv d o =>
    simp only [Alg.step_inv, Alg.doInv]
    split_ifs
    · exact ⟨_, rfl, by simp⟩
    · exact ⟨[], by simp, by simp⟩
  | step d =>
    simp only [Alg.step_step, doStep_eq]
    generalize ((alg δ f R v₀).act d (X.loc d)).1 = a
    rcases a with ⟨b, o⟩ | x | _
    · exact ⟨[], by simp, by simp⟩
    · rcases X.cur d with _ | o
      · exact ⟨[], by simp, by simp⟩
      · exact ⟨_, rfl, by simp⟩
    · exact ⟨[], by simp, by simp⟩
  | resp d n =>
    simp only [Alg.step_resp, Alg.doResp]
    split
    · exact ⟨[], by simp, by simp⟩
    · exact ⟨[], by simp [Alg.apply_hist], by simp⟩

lemma sinv_init : SInv δ f R v₀ Wr (alg δ f R v₀).initCfg [] none := by
  refine ⟨rfl, ?_, fun d => rfl, ?_, ?_, fun b => Or.inr (Or.inl rfl), ?_,
    fun d => Or.inr (Or.inl rfl), ?_, Or.inl rfl, ?_⟩
  · intro L₁ c x L₂ h; simp at h
  · intro c v h; cases h
  · intro c v h; cases h
  · intro d p hp; simp [Alg.initCfg] at hp
  · intro d hd; simp [Alg.initCfg, alg] at hd
  · intro c v h; cases h

/-- One event preserves the invariant, as long as the history stays sequential. -/
lemma sinv_step (hL : Layout δ f Wr R) {X : Cf} {L : List (C × HOp V × V)}
    {a : Option (C × HOp V)} (hgi : GI f R X) (hS : SInv δ f R v₀ Wr X L a) (e : Ev C V)
    (hwr : WrOK Wr X.hist) (hshape : SeqShape ((alg δ f R v₀).step X e).hist) :
    ∃ L' a', SInv δ f R v₀ Wr ((alg δ f R v₀).step X e) L' a' := by
  cases e with
  | inv d o =>
    simp only [Alg.step_inv, Alg.doInv] at hshape ⊢
    split_ifs at hshape ⊢ with hcur
    · -- the history was complete: `a = none`
      have ha : a = none := by
        obtain ⟨L'', a'', h⟩ := hshape
        rw [hS.hist] at h
        rcases a'' with _ | ⟨c'', o''⟩
        · rcases L''.eq_nil_or_concat with rfl | ⟨L₀, e₀, rfl⟩
          · simp [seqHist, aPart] at h
          · rw [List.concat_eq_append, seqHist_snoc, aPart, List.append_nil,
              show seqHist L₀ ++ [HEv.inv e₀.1 e₀.2.1, HEv.ret e₀.1 e₀.2.2] =
                (seqHist L₀ ++ [HEv.inv e₀.1 e₀.2.1]) ++ [HEv.ret e₀.1 e₀.2.2] by simp] at h
            have := (List.append_inj' h rfl).2
            simp at this
        · simp only [aPart] at h
          have := List.append_inj_left' h rfl
          exact (seqShape_eq (L' := L'') (a' := none) (by simpa [aPart] using this)).2
      subst ha
      exact ⟨L, _, sinv_inv δ f R v₀ Wr hgi hS d o⟩
    · exact ⟨L, a, hS⟩
  | step d =>
    simp only [Alg.step_step, doStep_eq] at hshape ⊢
    have hs := act_spec δ f R v₀ d (X.loc d)
    generalize ((alg δ f R v₀).act d (X.loc d)).1 = act at hs hshape ⊢
    generalize ((alg δ f R v₀).act d (X.loc d)).2 = l' at hs hshape ⊢
    cases hs with
    | trigW b hb => exact ⟨L, a, sinv_trigW δ f R v₀ Wr hS d b hb⟩
    | trigR b _ _ _ => exact ⟨L, a, sinv_trigR δ f R v₀ Wr hS d b⟩
    | retR _ hm _ hd =>
      have hcur : X.cur d = some .read := by
        have := (hgi.2 d).mode; rw [hm] at this
        rcases h : X.cur d with _ | _ | _ <;> simp_all [ModeOK]
      simp only [hcur]
      exact ⟨_, _, sinv_retR δ f R v₀ Wr hgi hS d hm hd⟩
    | toWp v _ hm _ hd => exact ⟨L, a, sinv_toWp δ f R v₀ Wr hgi hS d v hm hd⟩
    | retW hq hm hc =>
      obtain ⟨v, hcur⟩ : ∃ v, X.cur d = some (.write v) := by
        have := (hgi.2 d).mode; rw [hm] at this
        rcases h : X.cur d with _ | _ | v <;> simp_all [ModeOK]
      have ha : a = some (d, .write v) := curOf_eq_some (hS.cur d ▸ hcur)
      have hdW : d ∈ Wr := hwr d v (by rw [hS.hist, ha]; simp [aPart])
      simp only [hcur]
      exact ⟨_, _, sinv_retW δ f R v₀ Wr hL hgi hS d v hcur hm hq hc hdW⟩
    | skip _ _ _ =>
      simp only [update_eq_self]
      exact ⟨L, a, hS⟩
  | resp d n =>
    simp only [Alg.step_resp, Alg.doResp]
    split
    · exact ⟨L, a, hS⟩
    · rename_i p hp
      have hpm := List.mem_of_find?_eq_some hp
      unfold Alg.apply
      rcases hop : p.op with _ | w
      · simp only [alg, hop, Option.getD_some]
        exact ⟨L, a, sinv_respRead δ f R v₀ Wr hS d p.reg _ (fun x hx => List.mem_of_mem_filter hx)⟩
      · simp only [alg, hop]
        exact ⟨L, a, sinv_respWrite δ f R v₀ Wr hL hgi hS d p hpm w hop _
          (fun x => Alg.mem_filter_ne hgi.1 hpm)⟩

lemma sinv_run (hL : Layout δ f Wr R) (E : List (Ev C V))
    (hshape : SeqShape ((alg δ f R v₀).run E).hist) (hwr : WrOK Wr ((alg δ f R v₀).run E).hist) :
    ∃ L a, SInv δ f R v₀ Wr ((alg δ f R v₀).run E) L a := by
  induction E using List.reverseRecOn with
  | nil => exact ⟨[], none, sinv_init δ f R v₀ Wr⟩
  | append_singleton E e ih =>
    rw [Alg.run_append, Alg.exec_singleton] at hshape hwr ⊢
    obtain ⟨D, hD, hDl⟩ := hist_step δ f R v₀ ((alg δ f R v₀).run E) e
    have hpre : SeqShape ((alg δ f R v₀).run E).hist ∧ WrOK Wr ((alg δ f R v₀).run E).hist := by
      rw [hD] at hshape hwr
      refine ⟨?_, fun c v h => hwr c v (List.mem_append_left _ h)⟩
      rcases D with _ | ⟨ev, _ | _⟩
      · simpa using hshape
      · exact seqShape_of_snoc hshape
      · simp at hDl
    obtain ⟨L, a, hS⟩ := ih hpre.1 hpre.2
    exact sinv_step δ f R v₀ Wr hL (gi_run δ f R v₀ E) hS e hpre.2 hshape

/-- **Theorem 3 (safety in sequential runs)**: Algorithm 2 with a write-set layout satisfying the
capacity condition is safe in sequential runs (`Alg.SeqSafe`, the hypothesis of our lower bounds;
it is the restriction of the paper's WS-Regularity to sequential runs). -/
theorem seqSafe (hL : Layout δ f Wr R) : (alg δ f R v₀).SeqSafe v₀ ↑Wr := by
  intro E L c x hE hwrL
  have hshape : SeqShape ((alg δ f R v₀).run E).hist :=
    ⟨L ++ [(c, .read, x)], none, by simp [hE, aPart]⟩
  have hwr : WrOK Wr ((alg δ f R v₀).run E).hist := by
    intro d v hd
    rw [hE] at hd
    simp only [seqHist, List.mem_flatMap, List.mem_cons, HEv.inv.injEq,
      reduceCtorEq, or_false, List.not_mem_nil] at hd
    obtain ⟨e, he, rfl, hev⟩ := hd
    rcases List.mem_append.1 he with he | he
    · exact hwrL e he v hev.symm
    · simp only [List.mem_singleton] at he; subst he; cases hev
  obtain ⟨L', a', hS⟩ := sinv_run δ f R v₀ Wr hL E hshape hwr
  have h1 : seqHist L' ++ aPart a' = seqHist (L ++ [(c, .read, x)]) ++ aPart none := by
    rw [← hS.hist, hE]; simp [aPart]
  have := seqShape_eq h1
  exact hS.corr L c x [] (by rw [this.1])

end Podc.RegisterEmulationSpace.Alg2
