import Papers.PODC2014.ReadUpdateTradeoffs.CounterSnapshot
import Papers.PODC2014.ReadUpdateTradeoffs.Asymptotics

/-!
# Asymptotic forms of Theorem 1, Corollary 1 and Theorem 2 of Hendler–Khait (PODC'14)

* `update_steps_exist` — from the non-asymptotic tradeoff: some update takes `s` steps with
  `N ≤ R · 3^s + 1`;
* `counter_update_logb`, `snapshot_update_logb` — Theorem 1 / Corollary 1: some update takes at
  least `log₃((N − 1)/R)` steps, i.e. `Ω(log (N / f(N)))` when reads take `R = O(f(N))` steps;
* `theorem2_counter`, `theorem2_snapshot` — Theorem 2: if reads take `O(log N)` steps then some
  update takes at least `log₃ N / 2` steps, for all large `N` (`Ω(log N)`).
-/

namespace Podc.ReadUpdateTradeoffs

open Cslib.SharedMemory Cslib.SharedMemory.Awareness

variable {A : ObjSpec} {ι P L V : Type} [Fintype P] [DecidableEq P] [DecidableEq ι]
  [DecidableEq V] {v₀ : V}

/-- Some update takes `s` steps, where `N ≤ R · 3^s + 1`. -/
theorem update_steps_exist {I : Impl A (RWC ι V v₀) P L} {u : P → A.Op} {rd : A.Op} {r : P}
    (hlin : I.Linearizable) (hrev : Reveals A r u rd) (hall : ∀ p, p ≠ r → I.allowed p (u p))
    {R : ℕ} (hR : SoloBound I r rd R) (hR1 : 1 ≤ R) (hN : 2 ≤ Fintype.card P) :
    ∃ s, Fintype.card P ≤ R * 3 ^ s + 1 ∧ ∃ α, I.Valid α ∧ ∃ p, p ≠ r ∧ opsOf α p = [u p] ∧
      respsOf α p = [] ∧ s ≤ tauCount α p := by
  classical
  have hex : ∃ k, Fintype.card P ≤ R * 3 ^ k + 1 :=
    ⟨Fintype.card P, by
      have h1 : Fintype.card P < 3 ^ Fintype.card P := Nat.lt_pow_self (by norm_num)
      have h2 : 3 ^ Fintype.card P ≤ R * 3 ^ Fintype.card P := Nat.le_mul_of_pos_left _ hR1
      omega⟩
  set k := Nat.find hex with hk
  have hkspec : Fintype.card P ≤ R * 3 ^ k + 1 := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · -- `s = 0`: an invocation suffices
    obtain ⟨p, hp⟩ : ∃ p, p ≠ r := by
      by_contra hcon; push_neg at hcon
      have : Fintype.card P ≤ 1 := Fintype.card_le_one_iff.2 (fun a b => (hcon a).trans (hcon b).symm)
      omega
    have hv : I.Valid [.inv p (u p)] := ⟨_, by
      rw [Impl.run, Impl.runFrom_singleton]
      exact Impl.step_inv_eq_some (I := I) rfl (hall p hp)⟩
    exact ⟨0, by rw [← h0]; exact hkspec, [.inv p (u p)], hv, p, hp, by simp, by simp,
      Nat.zero_le _⟩
  · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hlt : R * 3 ^ j + 1 < Fintype.card P := by
      have := Nat.find_min hex (show j < Nat.find hex by omega)
      omega
    obtain ⟨α, hα, p, hp, h1, h2, h3⟩ := update_lower_bound hlin hrev hall hR j hlt
    exact ⟨j + 1, hj ▸ hkspec, α, hα, p, hp, h1, h2, h3⟩

/-- **Theorem 1 of Hendler–Khait, PODC'14 (logarithmic form).** In a linearizable `N`-process
counter from read/write/CAS whose `read` completes within `R ≥ 1` solo steps, some increment
takes at least `log₃((N − 1)/R)` steps; with `R = O(f(N))` this is `Ω(log (N / f(N)))`. -/
theorem counter_update_logb {I : Impl counterObj (RWC ι V v₀) P L} (hlin : I.Linearizable)
    (r : P) (hall : ∀ p, p ≠ r → I.allowed p CtrOp.inc) {R : ℕ}
    (hR : SoloBound I r CtrOp.read R) (hR1 : 1 ≤ R) (hN : 2 ≤ Fintype.card P) :
    ∃ s : ℕ, Real.logb 3 (((Fintype.card P : ℝ) - 1) / (R : ℝ)) ≤ s ∧ ∃ α, I.Valid α ∧
      ∃ p, p ≠ r ∧ opsOf α p = [CtrOp.inc] ∧ respsOf α p = [] ∧ s ≤ tauCount α p := by
  obtain ⟨s, hs, rest⟩ := update_steps_exist (u := fun _ => (CtrOp.inc : counterObj.Op))
    (rd := CtrOp.read) hlin (counter_reveals r) hall hR hR1 hN
  exact ⟨s, logb_le_of_mul_pow _ R s hN hR1 (by omega), rest⟩

/-- **Corollary 1 of Hendler–Khait, PODC'14 (logarithmic form)**, for single-writer snapshots. -/
theorem snapshot_update_logb {n : ℕ} {I : Impl (snapObj n) (RWC ι V v₀) (Fin n) L}
    (hlin : I.Linearizable) (r : Fin n) (hall : ∀ p, p ≠ r → I.allowed p (SnapOp.update p 1))
    {R : ℕ} (hR : SoloBound I r SnapOp.scan R) (hR1 : 1 ≤ R) (hN : 2 ≤ n) :
    ∃ s : ℕ, Real.logb 3 (((n : ℝ) - 1) / R) ≤ s ∧ ∃ α, I.Valid α ∧
      ∃ p, p ≠ r ∧ opsOf α p = [SnapOp.update p 1] ∧ respsOf α p = [] ∧ s ≤ tauCount α p := by
  obtain ⟨s, hs, rest⟩ := update_steps_exist (u := fun p => (SnapOp.update p 1 : (snapObj n).Op))
    (rd := SnapOp.scan) hlin (snap_reveals r) hall hR hR1 (by simpa using hN)
  simp only [Fintype.card_fin] at hs
  exact ⟨s, logb_le_of_mul_pow n R s hN hR1 (by omega), rest⟩

/-- **Theorem 2 of Hendler–Khait, PODC'14 (counters).** If `read` takes `O(log N)` steps then
increments take `Ω(log N)` steps: for every `c` there is `N₀` such that every linearizable
counter for `N ≥ N₀` processes from read/write/CAS whose `read` completes within
`R ≤ c · log N` solo steps has an execution in which an increment takes `≥ log₃ N / 2` steps.
(The paper restricts to reads and writes and to polynomially many updates; our executions use
`N − 1` increments.) -/
theorem theorem2_counter (c : ℝ) : ∃ N₀ : ℕ,
    ∀ {P ι L V : Type} [Fintype P] [DecidableEq P] [DecidableEq ι] [DecidableEq V] {v₀ : V}
      {I : Impl counterObj (RWC ι V v₀) P L}, I.Linearizable → ∀ (r : P),
      (∀ p, p ≠ r → I.allowed p CtrOp.inc) → ∀ {R : ℕ}, SoloBound I r CtrOp.read R →
      1 ≤ R → (R : ℝ) ≤ c * Real.log (Fintype.card P) → N₀ ≤ Fintype.card P →
      ∃ s : ℕ, Real.logb 3 (Fintype.card P) / 2 ≤ s ∧ ∃ α, I.Valid α ∧
        ∃ p, p ≠ r ∧ opsOf α p = [CtrOp.inc] ∧ respsOf α p = [] ∧ s ≤ tauCount α p := by
  obtain ⟨N₀, hN₀⟩ := log_bound_of_mul_pow c
  refine ⟨max N₀ 2, ?_⟩
  intro P ι L V _ _ _ _ v₀ I hlin r hall R hR hR1 hRc hN
  obtain ⟨s, hs, rest⟩ := update_steps_exist (u := fun _ => (CtrOp.inc : counterObj.Op))
    (rd := CtrOp.read) hlin (counter_reveals r) hall hR hR1 (le_of_max_le_right hN)
  exact ⟨s, hN₀ _ R s (le_of_max_le_left hN) hR1 hRc (by omega), rest⟩

/-- **Theorem 2 of Hendler–Khait, PODC'14 (single-writer snapshots).** -/
theorem theorem2_snapshot (c : ℝ) : ∃ N₀ : ℕ,
    ∀ {ι L V : Type} [DecidableEq ι] [DecidableEq V] {v₀ : V} {n : ℕ}
      {I : Impl (snapObj n) (RWC ι V v₀) (Fin n) L}, I.Linearizable → ∀ (r : Fin n),
      (∀ p, p ≠ r → I.allowed p (SnapOp.update p 1)) → ∀ {R : ℕ}, SoloBound I r SnapOp.scan R →
      1 ≤ R → (R : ℝ) ≤ c * Real.log n → N₀ ≤ n →
      ∃ s : ℕ, Real.logb 3 n / 2 ≤ s ∧ ∃ α, I.Valid α ∧
        ∃ p, p ≠ r ∧ opsOf α p = [SnapOp.update p 1] ∧ respsOf α p = [] ∧ s ≤ tauCount α p := by
  obtain ⟨N₀, hN₀⟩ := log_bound_of_mul_pow c
  refine ⟨max N₀ 2, ?_⟩
  intro ι L V _ _ v₀ n I hlin r hall R hR hR1 hRc hN
  obtain ⟨s, hs, rest⟩ := update_steps_exist (u := fun p => (SnapOp.update p 1 : (snapObj n).Op))
    (rd := SnapOp.scan) hlin (snap_reveals r) hall hR hR1 (by simpa using le_of_max_le_right hN)
  simp only [Fintype.card_fin] at hs
  exact ⟨s, hN₀ n R s (le_of_max_le_left hN) hR1 hRc (by omega), rest⟩

end Podc.ReadUpdateTradeoffs
