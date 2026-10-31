import Papers.PODC2018.JupiterListSpec.JupiterInv

/-!
# Main results for Jupiter

* `jupiter_inv` — along every execution, Jupiter's state spaces are parts of the global state
  space of the schedule and every replica's list is the list of its vertex;
* `jupiter_weak` — **Jupiter satisfies the weak list specification** (the conjecture of Attiya et
  al., solved by Theorems 12 and 18 of the paper);
* `jupiter_conv` — Jupiter satisfies the convergence property `A_cp`;
* `jupiter_srv_enabled`, `jupiter_recv_enabled` — the handlers never get stuck (so the theorems
  above are not vacuous: every interleaving of user operations and enabled deliveries is an
  execution);
* `jupiter_quiescent` — when all channels are empty, all replicas hold the same list.
-/

namespace Podc.JupiterListSpec

variable {n : ℕ}

open Cfg Jup

/-- The invariant holds along every execution of Jupiter, for every compatible schedule. -/
theorem jupiter_inv {es : List (Ev n)} {cfg : Cfg (jupiter n)}
    (hr : run genOp (jupiter n) es = some cfg) :
    ∀ S, Compat S cfg → GI S cfg ∧ JPI S cfg :=
  Cfg.reach (PI := JPI) (fun _ _ _ hP c => hP.clist c) (fun S _ => JPI.init S)
    (fun S cfg cfg' e hG hP hG' hs => by
      cases e with
      | «do» c u => obtain rfl := step_do hs; exact JPI.do hG hP hG'
      | srv c => exact JPI.srv hG hP hs hG'
      | recv c => exact JPI.recv hG hP hs hG') hr

/-- **Jupiter satisfies the weak list specification** (Theorems 12 and 18; the conjecture of
Attiya et al.). For every execution, the abstract execution formed by its `do` events, with
visibility "the operation was known to the replica", is well formed and belongs to `A_weak`. -/
theorem jupiter_weak {es : List (Ev n)} {cfg : Cfg (jupiter n)}
    (hr : run genOp (jupiter n) es = some cfg) :
    (absExec cfg).WF ∧ (absExec cfg).Weak :=
  (jupiter_inv hr _ (RF.run hr).compat).1.weak

/-- Jupiter satisfies the convergence property `A_cp` (Theorem 11 for Jupiter). -/
theorem jupiter_conv {es : List (Ev n)} {cfg : Cfg (jupiter n)}
    (hr : run genOp (jupiter n) es = some cfg) : (absExec cfg).Conv :=
  (jupiter_weak hr).2.conv

/-- Server processing is always enabled when a message is pending. -/
theorem jupiter_srv_enabled {es : List (Ev n)} {cfg : Cfg (jupiter n)}
    (hr : run genOp (jupiter n) es = some cfg) {c : Fin n} (hc : cfg.up c ≠ []) :
    ∃ cfg', cfg.step genOp (.srv c) = some cfg' := by
  obtain ⟨hG, hP⟩ := jupiter_inv hr _ (RF.run hr).compat
  obtain ⟨m, rest, hup⟩ := List.exists_cons_of_ne_nil hc
  obtain ⟨Ef, hx, -⟩ := srv_ok hG hP hup
  simp [step, hup, jupiter, hx]

/-- Remote processing is always enabled when a message is pending. -/
theorem jupiter_recv_enabled {es : List (Ev n)} {cfg : Cfg (jupiter n)}
    (hr : run genOp (jupiter n) es = some cfg) {c : Fin n} (hc : cfg.down c ≠ []) :
    ∃ cfg', cfg.step genOp (.recv c) = some cfg' := by
  obtain ⟨hG, hP⟩ := jupiter_inv hr _ (RF.run hr).compat
  obtain ⟨m, rest, hdown⟩ := List.exists_cons_of_ne_nil hc
  obtain ⟨Ef, hx, -⟩ := recv_ok hG hP hdown
  simp [step, hdown, jupiter, hx]

/-- When all channels are empty, every client holds the same list as the server. -/
theorem jupiter_quiescent {es : List (Ev n)} {cfg : Cfg (jupiter n)}
    (hr : run genOp (jupiter n) es = some cfg) (hup : ∀ c, cfg.up c = [])
    (hdown : ∀ c, cfg.down c = []) (c : Fin n) : (cfg.cs c).list = cfg.ss.list := by
  set S := schedOf cfg
  obtain ⟨hG, hP⟩ := jupiter_inv hr S (RF.run hr).compat
  rw [hP.clist c, hP.slist]
  congr 1
  ext x
  rw [hG.know c x, List.mem_toFinset]
  simp only [hdown c, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  constructor
  · rintro (⟨hxD, hxc⟩ | ⟨hx, -⟩)
    · by_contra hxs
      have : x ∈ (cfg.up c).map (jupiter n).oidOf := by
        rw [hG.rf.up c]; simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨by simpa [D] using hxD, hxc, hxs⟩
      simp [hup c] at this
    · exact hx
  · intro hx
    by_cases hxc : x.1 = c
    · exact Or.inl ⟨hG.sv_D hx, hxc⟩
    · exact Or.inr ⟨hx, hxc⟩

end Podc.JupiterListSpec
