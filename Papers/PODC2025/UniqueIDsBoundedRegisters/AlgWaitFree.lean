import Papers.PODC2025.UniqueIDsBoundedRegisters.AlgInv

/-!
# Algorithms 1 and 2: wait-freedom

* `alg_waitFreeUpTo`: Algorithm 2 (`1 ≤ n ≤ d`, `d ∣ m`) is wait-free in every infinite
  execution with at most `N` invocations (for every `N`). By the basic invariant at most
  `invCount ≤ N` tickets of `R₀` are successful, so `R₀` receives fewer than `d · (N + 1)`
  FAIs in total (`lt_of_count_residue`); the potential
  `3 · (d · (N + 1) - t) + μ(loc p)` then decreases with every step of `p`.
* `alg1_waitFree`: Algorithm 1 (`d = n ≥ 1`) is wait-free: every `get()` takes exactly two
  base-object accesses. For `n = 0` the loop never exits, so `1 ≤ n` is needed.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.UniqueIDs

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

/-- A natural-number sequence that never increases after `t0` cannot decrease infinitely
often. (Copy of `no_descent` from `StrangerFreeTasks`.) -/
lemma no_descent' (f : ℕ → ℕ) (t0 : ℕ) (hmono : ∀ t, t0 ≤ t → f (t + 1) ≤ f t)
    (hstrict : ∀ N, ∃ m, N ≤ m ∧ f (m + 1) < f m) : False := by
  have anti : ∀ a b, t0 ≤ a → a ≤ b → f b ≤ f a := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hb ih => exact (hmono b (ha.trans hb)).trans ih
  have key : ∀ c, ∃ t, t0 ≤ t ∧ f t + c ≤ f t0 := by
    intro c
    induction c with
    | zero => exact ⟨t0, le_rfl, le_rfl⟩
    | succ c ih =>
      obtain ⟨t, ht, hc⟩ := ih
      obtain ⟨m, hm, hlt⟩ := hstrict t
      exact ⟨m + 1, by omega, by have := anti t m ht hm; omega⟩
  obtain ⟨t, -, ht⟩ := key (f t0 + 1)
  omega

/-- The configurations of an infinite execution are reachable. -/
lemma alg_run_range {n d m : ℕ} [NeZero m] (e : (alg (P := P) n d m).InfExec) (t : ℕ) :
    (alg (P := P) n d m).run ((List.range t).map e.lbl) = some (e.cfg t) := by
  induction t with
  | zero => simp [e.cfg_zero]
  | succ t ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, Impl.run_append_of_eq _ ih,
      Impl.runFrom_singleton]
    exact e.step_eq t

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
  intro e hN p t₀ hpend
  have hrun := alg_run_range e
  let G : ℕ → Gh P := fun T => ghostOf n d m ((List.range T).map e.lbl)
  have hI : ∀ T, Inv1 n d m ((List.range T).map e.lbl) (e.cfg T) (G T) :=
    fun T => inv1_of_run hdm (hrun T)
  have hG : ∀ T, G (T + 1) = gstep n d (G T) (e.cfg T) (e.lbl T) := by
    intro T
    simp only [G, List.range_succ, List.map_append, List.map_singleton]
    exact ghostOf_append (hrun T) (e.step_eq T)
  have htB : ∀ T, (G T).t < d * (N + 1) :=
    fun T => lt_of_count_residue hn hnd ((hI T).count_le.trans (hN T))
  let f : ℕ → ℕ := fun T => 3 * (d * (N + 1) - (G T).t) + stPot ((e.cfg T).loc p)
  have hstep : ∀ T, t₀ ≤ T → f (T + 1) ≤ f T ∧ (e.lbl T = .tau p → f (T + 1) < f T) := by
    intro T hT
    have hs := e.step_eq T
    have ht := gstep_t_ge (d := d) (G T) (e.cfg T) (e.lbl T)
    rw [← hG] at ht
    have hB1 := htB T
    have hB2 := htB (T + 1)
    by_cases hq : (e.lbl T).proc = p
    · cases hl : e.lbl T with
      | inv q o =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        exact absurd (alg_step_inv hs).1 (hpend T hT)
      | ret q r =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        exact absurd (by simp [(alg_step_ret hs).2.1]) (hpend (T + 1) (by omega))
      | tau q =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        have hG' := hG T
        rw [hl] at hG'
        suffices f (T + 1) < f T from ⟨this.le, fun _ => this⟩
        simp only [f]
        cases hlp : (e.cfg T).loc q with
        | idle => exact (alg_step_tau_idle hs hlp).elim
        | done v => exact (alg_step_tau_done hs hlp).elim
        | start =>
          obtain ⟨-, -, -, hloc⟩ := alg_step_tau_start hs hlp
          have h1 : (G (T + 1)).t = (G T).t + 1 := by
            rw [hG']; simp only [gstep, hlp]; split_ifs <;> rfl
          have h2 : stPot ((e.cfg (T + 1)).loc q) ≤ 2 := by
            rw [hloc, Function.update_self]; split_ifs <;> simp [stPot]
          simp only [stPot] at h2 ⊢; omega
        | got i =>
          obtain ⟨-, -, -, hloc⟩ := alg_step_tau_got hs hlp
          have h1 : (G (T + 1)).t = (G T).t := by
            rw [hG']; simp only [gstep, hlp]
          rw [hloc, Function.update_self]; simp only [stPot]; omega
    · have := (Impl.step_other hs hq).1
      refine ⟨?_, fun h => absurd (by rw [h]; rfl) hq⟩
      simp only [f, this]; omega
  by_contra hcon
  push Not at hcon
  apply no_descent' f t₀ (fun T hT => (hstep T hT).1)
  intro M
  obtain ⟨T, hT, hl⟩ := hcon (max M t₀)
  exact ⟨T, le_of_max_le_left hT, (hstep T (le_of_max_le_right hT)).2 hl⟩

/-- **Bounded steps ⇒ wait-free.** (Copy of `Impl.waitFree_of_potential` from
`HistoryIndependent/Alg4WaitFree.lean`.) -/
theorem waitFree_of_stPotential {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {L : Type}
    [DecidableEq ι] (I : Impl A B P L) (μ : P → L → ℕ)
    (hμ : ∀ p l i o k, I.act p l = .access i o k → ∀ x, μ p (k x) < μ p l) : I.WaitFree := by
  intro e p n hpend
  let f : ℕ → ℕ := fun m => μ p ((e.cfg m).loc p)
  have hstep : ∀ m ≥ n, f (m + 1) ≤ f m ∧ (e.lbl m = .tau p → f (m + 1) < f m) := by
    intro m hm
    have hs := e.step_eq m
    by_cases hq : (e.lbl m).proc = p
    · cases hl : e.lbl m with
      | inv q o =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        exact absurd (Impl.step_inv hs).1 (hpend m hm)
      | ret q r =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        exact absurd (by simp [(Impl.step_ret hs).2.1]) (hpend (m + 1) (by omega))
      | tau q =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        obtain ⟨-, -, i, o, k, hact, -, hloc⟩ := Impl.step_tau hs
        have : f (m + 1) < f m := by
          simp only [f, hloc, Function.update_self]
          exact hμ _ _ i o k hact _
        exact ⟨this.le, fun _ => this⟩
    · have := (Impl.step_other hs hq).1
      refine ⟨by simp [f, this], fun h => absurd (by rw [h]; rfl) hq⟩
  by_contra hcon
  push Not at hcon
  apply no_descent' f n (fun T hT => (hstep T hT).1)
  intro M
  obtain ⟨T, hT, hl⟩ := hcon (max M n)
  exact ⟨T, le_of_max_le_left hT, (hstep T (le_of_max_le_right hT)).2 hl⟩

/-- **Wait-freedom of Algorithm 1** (`d = n ≥ 1`): every `get()` applies FAI to `R₀` once
(the residue modulo `n` is always `< n`) and then FAI to one `R_{i+1}`. The hypothesis `1 ≤ n`
is necessary: for `n = 0` the loop never exits. -/
theorem alg1_waitFree (n m : ℕ) [NeZero m] (hn : 1 ≤ n) : (alg (P := P) n n m).WaitFree := by
  refine waitFree_of_stPotential _ (fun _ l => stPot l) ?_
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
