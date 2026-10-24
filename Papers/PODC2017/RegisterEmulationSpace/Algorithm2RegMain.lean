import Papers.PODC2017.RegisterEmulationSpace.Algorithm2RegSteps
import Papers.PODC2017.RegisterEmulationSpace.Algorithm2Layout

/-!
# Algorithm 2 is WS-Regular (Corollary 4) and the full Theorem 3
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace.Alg2

open Finset Function

variable {C B S V : Type*} [DecidableEq C] [LinearOrder B] [Fintype B] [Fintype S] [DecidableEq S]

local notation "Cf" => Cfg C B V (ℕ × V) (Loc B V)

variable (δ : B → S) (f : ℕ) (R : C → Finset B) (v₀ : V) (Wr : Finset C)

lemma rinv_init : RInv δ f R v₀ Wr (alg δ f R v₀).initCfg hinit := by
  refine ⟨trivial, fun d => rfl, ?_, ?_, ?_, fun _ => rfl, ?_, ?_, ?_, ?_,
    fun b => ⟨rfl, Or.inl le_rfl⟩, ?_, fun d => ⟨rfl, Or.inl le_rfl⟩, ?_, Or.inl rfl, ?_, ?_⟩
  · intro d o h; cases h
  · intro d o lv h; cases h
  · intro d v h; cases h
  · simp only [hinit, Bool.false_eq_true, false_iff, not_exists]
    intro d v h; cases h
  · intro d d' v v' h; cases h
  · intro c v h; cases h
  · intro c v h; cases h
  · intro d p hp; simp [Alg.initCfg] at hp
  · intro d hd; simp [Alg.initCfg, alg] at hd
  · intro d o lv h; cases h
  · intro c v h; cases h

/-- One event preserves the invariant, as long as the writes stay sequential. -/
lemma rinv_step (hL : Layout δ f Wr R) {X : Cf} (hgi : GI f R X)
    (hS : RInv δ f R v₀ Wr X (hscan v₀ X.hist)) (e : Ev C V) (hwr : WrOK Wr X.hist)
    (hws : (hscan v₀ ((alg δ f R v₀).step X e).hist).ws) :
    RInv δ f R v₀ Wr ((alg δ f R v₀).step X e) (hscan v₀ ((alg δ f R v₀).step X e).hist) := by
  cases e with
  | inv d o =>
    simp only [Alg.step_inv, Alg.doInv] at hws ⊢
    split_ifs at hws ⊢ with hcur
    · rw [hscan_snoc] at hws ⊢
      exact rinv_inv δ f R v₀ Wr hgi hS d o hcur hws.2
    · exact hS
  | step d =>
    simp only [Alg.step_step, doStep_eq] at hws ⊢
    have hs := act_spec δ f R v₀ d (X.loc d)
    generalize ((alg δ f R v₀).act d (X.loc d)).1 = act at hs hws ⊢
    generalize ((alg δ f R v₀).act d (X.loc d)).2 = l' at hs hws ⊢
    cases hs with
    | trigW b hb => exact rinv_trigW δ f R v₀ Wr hS d b hb
    | trigR b _ _ _ => exact rinv_trigR δ f R v₀ Wr hS d b
    | retR _ hm _ hd =>
      have hcur : X.cur d = some .read := by
        have := (hgi.2 d).mode; rw [hm] at this
        rcases h : X.cur d with _ | _ | _ <;> simp_all [ModeOK]
      simp only [hcur]
      rw [hscan_snoc]
      exact rinv_retR δ f R v₀ Wr hgi hS d hm hd
    | toWp v _ hm _ hd => exact rinv_toWp δ f R v₀ Wr hgi hS d v hm hd
    | retW hq hm hc =>
      obtain ⟨v, hcur⟩ := cur_of_wp f R hgi hm
      have hdW : d ∈ Wr := hwr d v (hS.inHist d _ hcur)
      simp only [hcur]
      rw [hscan_snoc]
      exact rinv_retW δ f R v₀ Wr hL hgi hS d v hcur hm hq hc hdW
    | skip _ _ _ =>
      simp only [update_eq_self]
      exact hS
  | resp d n =>
    simp only [Alg.step_resp, Alg.doResp]
    split
    · exact hS
    · rename_i p hp
      have hpm := List.mem_of_find?_eq_some hp
      unfold Alg.apply
      rcases hop : p.op with _ | w
      · simp only [alg, hop, Option.getD_some]
        exact rinv_respRead δ f R v₀ Wr hS d p.reg _ (fun x hx => List.mem_of_mem_filter hx)
      · simp only [alg, hop]
        exact rinv_respWrite δ f R v₀ Wr hL hgi hS d p hpm w hop _
          (fun x => Alg.mem_filter_ne hgi.1 hpm)

lemma rinv_run (hL : Layout δ f Wr R) (E : List (Ev C V))
    (hwr : WrOK Wr ((alg δ f R v₀).run E).hist) (hws : (hscan v₀ ((alg δ f R v₀).run E).hist).ws) :
    RInv δ f R v₀ Wr ((alg δ f R v₀).run E) (hscan v₀ ((alg δ f R v₀).run E).hist) := by
  induction E using List.reverseRecOn with
  | nil => exact rinv_init δ f R v₀ Wr
  | append_singleton E e ih =>
    rw [Alg.run_append, Alg.exec_singleton] at hws hwr ⊢
    obtain ⟨D, hD, hDl⟩ := hist_step δ f R v₀ ((alg δ f R v₀).run E) e
    have hpre : (hscan v₀ ((alg δ f R v₀).run E).hist).ws ∧ WrOK Wr ((alg δ f R v₀).run E).hist := by
      rw [hD] at hws hwr
      refine ⟨?_, fun c v h => hwr c v (List.mem_append_left _ h)⟩
      rcases D with _ | ⟨ev, _ | _⟩
      · simpa using hws
      · rw [hscan_snoc] at hws; exact hstep_ws v₀ _ _ hws
      · simp at hDl
    exact rinv_step δ f R v₀ Wr hL (gi_run δ f R v₀ E) (ih hpre.2 hpre.1) e hpre.2 hws

/-- **Corollary 4 / Theorem 3 (safety)**: Algorithm 2 with a write-set layout satisfying the
capacity condition is WS-Regular. -/
theorem wsRegular (hL : Layout δ f Wr R) : WSRegular (alg δ f R v₀) v₀ ↑Wr :=
  fun E hwr hws => (rinv_run δ f R v₀ Wr hL E hwr hws).reg

end Podc.RegisterEmulationSpace.Alg2

open Finset in
/-- **Theorem 3** (Section 3.3, Appendix D), complete form. For all `f > 0`, `n = |S| > 2f` and
every set `Wr` of `k` writers, Algorithm 2 with `kf + ⌈k/z⌉(f+1)` registers
(`z = ⌊(n - (f+1))/f⌋`), each written by at most `z` writers, is an `f`-tolerant wait-free
WS-Regular emulation of a `k`-writer register. -/
theorem Podc.RegisterEmulationSpace.Alg2.theorem3_wsRegular {C S V : Type*} [DecidableEq C]
    [Fintype S] [DecidableEq S] (Wr : Finset C) {f : ℕ} (hf : 0 < f)
    (hn : 2 * f < Fintype.card S) (v₀ : V) :
    ∃ (N : ℕ) (δ : Fin N → S) (R : C → Finset (Fin N)),
      N = #Wr * f + (#Wr ⌈/⌉ ((Fintype.card S - (f + 1)) / f)) * (f + 1) ∧
      (∀ b, #(Wr.filter fun c => b ∈ R c) ≤ (Fintype.card S - (f + 1)) / f) ∧
      Podc.RegisterEmulationSpace.Alg2.WaitFree (Podc.RegisterEmulationSpace.Alg2.alg δ f R v₀) δ f ∧
      Podc.RegisterEmulationSpace.Alg2.WSRegular (Podc.RegisterEmulationSpace.Alg2.alg δ f R v₀) v₀ ↑Wr := by
  obtain ⟨N, δ, R, hN, hz, hL, hwf, -, -⟩ := Podc.RegisterEmulationSpace.Alg2.theorem3 Wr hf hn v₀
  exact ⟨N, δ, R, hN, hz, hwf, Podc.RegisterEmulationSpace.Alg2.wsRegular δ f R v₀ Wr hL⟩
