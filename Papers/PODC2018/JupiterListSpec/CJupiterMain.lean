import Papers.PODC2018.JupiterListSpec.CJupiterInv
import Papers.PODC2018.JupiterListSpec.JupiterMain

/-!
# Main results for CJupiter, and the equivalence of CJupiter and Jupiter

* `cjupiter_inv` — Proposition 9 in invariant form: every replica of CJupiter holds the global
  state space restricted to the operations it processed, and its list is the list of its vertex;
* `cjupiter_weak` — **Theorem 18**: CJupiter satisfies the weak list specification;
* `cjupiter_conv` — **Theorem 11**: CJupiter satisfies the convergence property;
* `cjupiter_srv_enabled`, `cjupiter_recv_enabled` — the handlers never get stuck;
* `equivalence` — **Theorem 12**: under the same schedule (the same sequence of events), Jupiter
  and CJupiter are enabled at the same events and produce the same `do` events (with the same
  returned lists) and the same replica lists.
-/

namespace Podc.JupiterListSpec

variable {n : ℕ}

open Cfg CJup

theorem cjupiter_inv {es : List (Ev n)} {cfg : Cfg (cjupiter n)}
    (hr : run genOp (cjupiter n) es = some cfg) :
    ∀ S, Compat S cfg → GI S cfg ∧ CPI S cfg :=
  Cfg.reach (PI := CPI) (fun _ _ _ hP c => hP.clist c) (fun S _ => CPI.init S)
    (fun S cfg cfg' e hG hP hG' hs => by
      cases e with
      | «do» c u => obtain rfl := step_do hs; exact CPI.do hG hP hG'
      | srv c => exact CPI.srv hG hP hs hG'
      | recv c => exact CPI.recv hG hP hs hG') hr

/-- **Theorem 18**: CJupiter satisfies the weak list specification. -/
theorem cjupiter_weak {es : List (Ev n)} {cfg : Cfg (cjupiter n)}
    (hr : run genOp (cjupiter n) es = some cfg) :
    (absExec cfg).WF ∧ (absExec cfg).Weak :=
  (cjupiter_inv hr _ (RF.run hr).compat).1.weak

/-- **Theorem 11**: CJupiter satisfies the convergence property `A_cp`. -/
theorem cjupiter_conv {es : List (Ev n)} {cfg : Cfg (cjupiter n)}
    (hr : run genOp (cjupiter n) es = some cfg) : (absExec cfg).Conv :=
  (cjupiter_weak hr).2.conv

theorem cjupiter_srv_enabled {es : List (Ev n)} {cfg : Cfg (cjupiter n)}
    (hr : run genOp (cjupiter n) es = some cfg) {c : Fin n} (hc : cfg.up c ≠ []) :
    ∃ cfg', cfg.step genOp (.srv c) = some cfg' := by
  obtain ⟨hG, hP⟩ := cjupiter_inv hr _ (RF.run hr).compat
  obtain ⟨m, rest, hup⟩ := List.exists_cons_of_ne_nil hc
  obtain ⟨Ef, hx, -⟩ := csrv_ok hG hP hup
  simp [step, hup, cjupiter, hx]

theorem cjupiter_recv_enabled {es : List (Ev n)} {cfg : Cfg (cjupiter n)}
    (hr : run genOp (cjupiter n) es = some cfg) {c : Fin n} (hc : cfg.down c ≠ []) :
    ∃ cfg', cfg.step genOp (.recv c) = some cfg' := by
  obtain ⟨hG, hP⟩ := cjupiter_inv hr _ (RF.run hr).compat
  obtain ⟨m, rest, hdown⟩ := List.exists_cons_of_ne_nil hc
  obtain ⟨Ef, hx, -⟩ := crecv_ok hG hP hdown
  simp [step, hdown, cjupiter, hx]

/-! ### Theorem 12: equivalence -/

/-- The protocol-independent skeleton of a configuration: `do` events, knowledge, server order,
sequence numbers and the identifiers in transit. -/
def skel {P : Proto n} (cfg : Cfg P) :=
  (cfg.log, cfg.know, cfg.sv, cfg.seq, fun c => (cfg.up c).map P.oidOf,
    fun c => (cfg.down c).map P.oidOf)

theorem Compat.transfer {P₁ P₂ : Proto n} {cfg₁ : Cfg P₁} {cfg₂ : Cfg P₂} {S : Sched (Oid n)}
    (hk : skel cfg₁ = skel cfg₂) (h : Compat S cfg₁) : Compat S cfg₂ := by
  simp only [skel, Prod.mk.injEq] at hk
  obtain ⟨hlog, -, hsv, -, hup, -⟩ := hk
  have hD : cfg₁.D = cfg₂.D := by simp [D, hlog]
  refine ⟨h.cl, hlog ▸ h.orig, hlog ▸ h.ctx, hsv ▸ h.rank_sv, hsv ▸ h.sv_of_rank,
    fun c m hm => ?_, fun c => ?_, hD ▸ h.inj⟩
  · have : P₂.oidOf m ∈ (cfg₁.up c).map P₁.oidOf := by
      rw [congrFun hup c]; exact List.mem_map_of_mem hm
    obtain ⟨m₁, hm₁, he⟩ := List.mem_map.1 this
    rw [← hsv, ← he]; exact h.rank_up c m₁ hm₁
  · have h1 := h.up_sorted c
    have e1 : ((cfg₁.up c).map fun m => S.rank (P₁.oidOf m)) =
        ((cfg₁.up c).map P₁.oidOf).map S.rank := by simp
    have e2 : ((cfg₂.up c).map fun m => S.rank (P₂.oidOf m)) =
        ((cfg₂.up c).map P₂.oidOf).map S.rank := by simp
    rw [e1, congrFun hup c] at h1
    rw [e2]; exact h1

theorem run_snoc {P : Proto n} (g) (es : List (Ev n)) (e : Ev n) :
    run g P (es ++ [e]) = (run g P es).bind fun cfg => cfg.step g e := by
  simp [run, List.foldlM_append]

/-- One step transforms equal skeletons (and equal client lists) into equal skeletons. -/
theorem skel_step {P₁ P₂ : Proto n} {cfg₁ : Cfg P₁} {cfg₂ : Cfg P₂} {cfg₁' : Cfg P₁}
    {cfg₂' : Cfg P₂} (hk : skel cfg₁ = skel cfg₂)
    (hl : ∀ c, P₁.list (cfg₁.cs c) = P₂.list (cfg₂.cs c)) {e : Ev n}
    (h₁ : cfg₁.step genOp e = some cfg₁') (h₂ : cfg₂.step genOp e = some cfg₂') :
    skel cfg₁' = skel cfg₂' := by
  simp only [skel, Prod.mk.injEq] at hk ⊢
  obtain ⟨hlog, hknow, hsv, hseq, hup, hdown⟩ := hk
  cases e with
  | «do» c u =>
    obtain rfl := step_do h₁
    obtain rfl := step_do h₂
    simp only [doCfg, hlog, hknow, hseq, hsv, hl c, true_and]
    refine ⟨?_, ?_⟩
    · funext c'
      by_cases hc : c' = c
      · subst hc; simp [Function.update_self, congrFun hup c', P₁.oidOf_cdo, P₂.oidOf_cdo, hseq]
      · simp [Function.update_of_ne hc, congrFun hup c']
    · exact hdown
  | srv c =>
    obtain ⟨m₁, rest₁, s₁, m₁', hup₁, hs₁, rfl⟩ := step_srv h₁
    obtain ⟨m₂, rest₂, s₂, m₂', hup₂, hs₂, rfl⟩ := step_srv h₂
    have hc := congrFun hup c
    rw [hup₁, hup₂, List.map_cons, List.map_cons, List.cons.injEq] at hc
    have ho₁ := P₁.oidOf_srecv _ _ _ _ _ hs₁
    have ho₂ := P₂.oidOf_srecv _ _ _ _ _ hs₂
    refine ⟨hlog, hknow, by rw [hsv, hc.1], hseq, ?_, ?_⟩
    · funext c'
      by_cases hc' : c' = c
      · subst hc'; simp [Function.update_self, hc.2]
      · simp [Function.update_of_ne hc', congrFun hup c']
    · funext c'
      by_cases hc' : c' = c
      · simp [hc', congrFun hdown c]
      · simp [hc', congrFun hdown c', ho₁, ho₂, hc.1]
  | recv c =>
    obtain ⟨m₁, rest₁, s₁, hd₁, hs₁, rfl⟩ := step_recv h₁
    obtain ⟨m₂, rest₂, s₂, hd₂, hs₂, rfl⟩ := step_recv h₂
    have hc := congrFun hdown c
    rw [hd₁, hd₂, List.map_cons, List.map_cons, List.cons.injEq] at hc
    refine ⟨hlog, ?_, hsv, hseq, hup, ?_⟩
    · funext c'
      by_cases hc' : c' = c
      · subst hc'; simp [Function.update_self, congrFun hknow c', hc.1]
      · simp [Function.update_of_ne hc', congrFun hknow c']
    · funext c'
      by_cases hc' : c' = c
      · subst hc'; simp [Function.update_self, hc.2]
      · simp [Function.update_of_ne hc', congrFun hdown c']

/-- **Theorem 12 (equivalence of Jupiter and CJupiter).** Under the same schedule, Jupiter and
CJupiter accept the same events, and reach configurations with the same `do` events (same
replicas, operations and returned lists), the same knowledge, server order and messages in
transit (up to their payload), and the same lists at every replica. -/
theorem equivalence (es : List (Ev n)) :
    (run genOp (jupiter n) es).map skel = (run genOp (cjupiter n) es).map skel ∧
      ∀ cJ cC, run genOp (jupiter n) es = some cJ → run genOp (cjupiter n) es = some cC →
        (∀ c, (cJ.cs c).list = (cC.cs c).list) ∧ cJ.ss.list = cC.ss.list := by
  -- lists are determined by the skeleton
  have hlists : ∀ (es : List (Ev n)) cJ cC, run genOp (jupiter n) es = some cJ →
      run genOp (cjupiter n) es = some cC → skel cJ = skel cC →
      (∀ c, (cJ.cs c).list = (cC.cs c).list) ∧ cJ.ss.list = cC.ss.list := by
    intro es cJ cC hJ hC hk
    have hcJ := (RF.run hJ).compat
    obtain ⟨hGJ, hPJ⟩ := jupiter_inv hJ _ hcJ
    obtain ⟨hGC, hPC⟩ := cjupiter_inv hC _ (Compat.transfer hk hcJ)
    have hk' := hk
    simp only [skel, Prod.mk.injEq] at hk'
    refine ⟨fun c => ?_, ?_⟩
    · rw [hPJ.clist c, hPC.clist c, hk'.2.1]
    · rw [hPJ.slist, hPC.slist, hk'.2.2.1]
  suffices hs : (run genOp (jupiter n) es).map skel = (run genOp (cjupiter n) es).map skel by
    refine ⟨hs, fun cJ cC hJ hC => hlists es cJ cC hJ hC ?_⟩
    rw [hJ, hC] at hs; exact Option.some.inj hs
  induction es using List.reverseRecOn with
  | nil => rfl
  | append_singleton es e ih =>
    rw [run_snoc, run_snoc]
    cases hJ : run genOp (jupiter n) es with
    | none =>
      cases hC : run genOp (cjupiter n) es with
      | none => rfl
      | some cC => rw [hJ, hC] at ih; cases ih
    | some cJ =>
      cases hC : run genOp (cjupiter n) es with
      | none => rw [hJ, hC] at ih; cases ih
      | some cC =>
        rw [hJ, hC] at ih
        have hk : skel cJ = skel cC := Option.some.inj ih
        have hl := (hlists es cJ cC hJ hC hk).1
        have hk' := hk
        simp only [skel, Prod.mk.injEq] at hk'
        -- the same events are enabled
        have hen : (cJ.step genOp e).isSome = (cC.step genOp e).isSome := by
          cases e with
          | «do» c u => simp [step]
          | srv c =>
            have hu := congrFun hk'.2.2.2.2.1 c
            by_cases hc : cJ.up c = []
            · have : cC.up c = [] := by
                rw [hc, List.map_nil] at hu; exact List.map_eq_nil_iff.1 hu.symm
              simp [step, hc, this]
            · have hc' : cC.up c ≠ [] := fun h0 => hc (by
                rw [h0, List.map_nil] at hu; exact List.map_eq_nil_iff.1 hu)
              obtain ⟨_, h1⟩ := jupiter_srv_enabled hJ hc
              obtain ⟨_, h2⟩ := cjupiter_srv_enabled hC hc'
              simp [h1, h2]
          | recv c =>
            have hu := congrFun hk'.2.2.2.2.2 c
            by_cases hc : cJ.down c = []
            · have : cC.down c = [] := by
                rw [hc, List.map_nil] at hu; exact List.map_eq_nil_iff.1 hu.symm
              simp [step, hc, this]
            · have hc' : cC.down c ≠ [] := fun h0 => hc (by
                rw [h0, List.map_nil] at hu; exact List.map_eq_nil_iff.1 hu)
              obtain ⟨_, h1⟩ := jupiter_recv_enabled hJ hc
              obtain ⟨_, h2⟩ := cjupiter_recv_enabled hC hc'
              simp [h1, h2]
        simp only [Option.bind_some]
        cases h1 : cJ.step genOp e with
        | none =>
          rw [h1] at hen
          cases h2 : cC.step genOp e with
          | none => rfl
          | some _ => rw [h2] at hen; cases hen
        | some cJ' =>
          rw [h1] at hen
          cases h2 : cC.step genOp e with
          | none => rw [h2] at hen; cases hen
          | some cC' =>
            simp only [Option.map_some]
            exact congrArg some (skel_step hk hl h1 h2)

end Podc.JupiterListSpec
