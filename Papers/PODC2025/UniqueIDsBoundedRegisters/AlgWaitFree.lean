import Papers.PODC2025.UniqueIDsBoundedRegisters.AlgInv
import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Potential
import Cslib.Computability.Distributed.SharedMemory.Task

/-!
# Algorithms 1 and 2: wait-freedom

* `alg_waitFreeUpTo`: Algorithm 2 (`1 ≤ n ≤ d`, `d ∣ m`) is wait-free in every infinite
  execution with at most `N` invocations (for every `N`). By the basic invariant at most
  `numInv ≤ N` tickets of `R₀` are successful, so `R₀` receives fewer than `d · (N + 1)`
  FAIs in total (`lt_of_count_residue`); the potential
  `3 · (d · (N + 1) - t) + μ(loc p)` (with the ghost ticket counter `t` of the execution) then
  decreases with every step of `p` (library `Impl.waitFreeOn_of_runPotential`).
* `alg1_waitFree`: Algorithm 1 (`d = n ≥ 1`) is wait-free: every `get()` takes exactly two
  base-object accesses (library `Impl.waitFree_of_potential`). For `n = 0` the loop never exits, so `1 ≤ n` is needed.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.UniqueIDs

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

lemma gstep_t_ge {n d m : ℕ} [NeZero m] (g : Gh P) (C : ACfg P n m) (ℓ : Label P uidObj) :
    g.t ≤ (gstep n d g C ℓ).t := by
  cases ℓ with
  | inv p o => simp [gstep]
  | ret p r => simp [gstep]
  | tau p =>
    simp only [gstep]
    cases C.loc p with
    | start => split_ifs <;> simp
    | _ => simp

/-- Potential of a local state: remaining accesses if the loop exits at once. -/
def stPot {n : ℕ} : St n → ℕ
  | .start => 2
  | .got _ => 1
  | _ => 0

/-- **Wait-freedom of Algorithm 2 for boundedly many calls**: if `1 ≤ n ≤ d` and `d ∣ m`, then
in every infinite execution with at most `N` invocations a process with a pending `get()` takes
only finitely many steps. -/
theorem alg_waitFreeUpTo (n d m : ℕ) [NeZero m] (hn : 1 ≤ n) (hnd : n ≤ d) (hdm : d ∣ m)
    (N : ℕ) : WaitFreeUpTo (alg (P := P) n d m) N := by
  refine Impl.waitFreeOn_of_runPotential _
    (fun p α C => 3 * (d * (N + 1) - (ghostOf n d m α).t) + stPot (C.loc p))
    fun p α C ℓ C' hα hN hs hp hp' => ?_
  have hα' : (alg (P := P) n d m).run (α ++ [ℓ]) = some C' := by
    rw [Impl.run_append_of_eq _ hα, Impl.runFrom_singleton, hs]
  have hG := ghostOf_append hα hs
  have ht := gstep_t_ge (d := d) (ghostOf n d m α) C ℓ
  rw [← hG] at ht
  have hB1 := lt_of_count_residue hn hnd ((inv1_of_run hdm hα).count_le.trans
    (le_trans (by simp) hN))
  have hB2 := lt_of_count_residue hn hnd ((inv1_of_run hdm hα').count_le.trans hN)
  rcases Impl.step_tau_or_other _ hs hp hp' with rfl | ⟨hq, hloc⟩
  · suffices 3 * (d * (N + 1) - (ghostOf n d m (α ++ [.tau p])).t) + stPot (C'.loc p) <
        3 * (d * (N + 1) - (ghostOf n d m α).t) + stPot (C.loc p) from ⟨this.le, fun _ => this⟩
    cases hlp : C.loc p with
    | idle => exact (alg_step_tau_idle hs hlp).elim
    | done v => exact (alg_step_tau_done hs hlp).elim
    | start =>
      obtain ⟨-, -, -, hloc⟩ := alg_step_tau_start hs hlp
      have h1 : (ghostOf n d m (α ++ [.tau p])).t = (ghostOf n d m α).t + 1 := by
        rw [hG]; simp only [gstep, hlp]; split_ifs <;> rfl
      have h2 : stPot (C'.loc p) ≤ 2 := by
        rw [hloc, Function.update_self]; split_ifs <;> simp [stPot]
      simp only [stPot] at h2 ⊢; omega
    | got i =>
      obtain ⟨-, -, -, hloc⟩ := alg_step_tau_got hs hlp
      have h1 : (ghostOf n d m (α ++ [.tau p])).t = (ghostOf n d m α).t := by
        rw [hG]; simp only [gstep, hlp]
      rw [hloc, Function.update_self]; simp only [stPot]; omega
  · rw [hloc]
    exact ⟨by omega, fun h => absurd (by rw [h]; rfl) hq⟩

/-- **Wait-freedom of Algorithm 1** (`d = n ≥ 1`): every `get()` applies FAI to `R₀` once
(the residue modulo `n` is always `< n`) and then FAI to one `R_{i+1}`. The hypothesis `1 ≤ n`
is necessary: for `n = 0` the loop never exits. -/
theorem alg1_waitFree (n m : ℕ) [NeZero m] (hn : 1 ≤ n) : (alg (P := P) n n m).WaitFree := by
  refine Impl.waitFree_of_potential _ (fun _ l => stPot l) ?_
  intro p l i o k hact x
  cases l with
  | idle => simp [alg] at hact
  | done v => simp [alg] at hact
  | start =>
    simp only [alg, Action.access.injEq] at hact
    obtain ⟨rfl, -, hk⟩ := hact
    cases eq_of_heq hk
    simp only [stPot]
    rw [dite_eq_left (Nat.mod_lt _ (by omega))]
    simp
  | got j =>
    simp only [alg, Action.access.injEq] at hact
    obtain ⟨rfl, -, hk⟩ := hact
    cases eq_of_heq hk
    simp [stPot]


/-- The hypothesis `1 ≤ n` of `alg1_waitFree` is necessary: with `n = 0` the loop of `get()`
never exits. -/
theorem alg_zero_not_waitFree [Nonempty P] (d m : ℕ) [NeZero m] :
    ¬ (alg (P := P) 0 d m).WaitFree := by
  obtain ⟨p⟩ := ‹Nonempty P›
  let cfg : ℕ → ACfg P 0 m := fun t => match t with
    | 0 => (alg (P := P) 0 d m).initCfg
    | t + 1 => ⟨Function.update (fun _ => .idle) p .start,
        Function.update (fun _ => none) p (some ()), fun _ => Fin.ofNat m t⟩
  let lbl : ℕ → Label P uidObj := fun t => match t with
    | 0 => .inv p ()
    | _ + 1 => .tau p
  have hstep : ∀ t, (alg (P := P) 0 d m).step (cfg t) (lbl t) = some (cfg (t + 1)) := by
    intro t
    cases t with
    | zero =>
      simp only [cfg, Impl.step, Impl.initCfg, alg]
      simp
      rfl
    | succ t =>
      simp only [cfg, lbl, Impl.step, alg]
      simp
      funext i
      rw [Fin.fin_one_eq_zero i]
      simp only [Function.update_self]
      ext
      simp [Fin.val_add, Nat.add_mod]
  let e : (alg (P := P) 0 d m).InfExec := ⟨cfg, lbl, rfl, hstep⟩
  intro h
  obtain ⟨N, hN⟩ := h e p 1 (fun t ht => by
    obtain ⟨t, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    simp [e, cfg])
  exact hN (N + 1) (by omega) rfl

end Cslib.SharedMemory.UniqueIDs
