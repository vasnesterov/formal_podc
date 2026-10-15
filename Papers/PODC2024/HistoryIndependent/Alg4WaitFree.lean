import Papers.PODC2024.HistoryIndependent.Alg4Inv

/-!
# Algorithm 4 is wait-free

* `Impl.waitFree_of_potential` (general, CSLib candidate): if a potential on local states
  strictly decreases with every base-object access of a process, the implementation is
  wait-free (each operation finishes within `μ p l` own steps).
* Every `Write` of Algorithm 4 takes at most `3K + 6` and every `Read` at most `6K + 6` low-level
  steps (`WPC.pot`, `RPC.pot`), hence `waitFree`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

-- CSLib candidate
namespace Impl

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
  (I : Impl A B P L)

/-- **Bounded steps ⇒ wait-free.** -/
theorem waitFree_of_potential (μ : P → L → ℕ)
    (hμ : ∀ p l i o k, I.act p l = .access i o k → ∀ x, μ p (k x) < μ p l) : I.WaitFree := by
  intro e p n hpend
  let f : ℕ → ℕ := fun m => μ p ((e.cfg m).loc p)
  -- one step: the potential does not increase, and decreases at internal steps of `p`
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
  have hmono : ∀ m ≥ n, ∀ j, f (m + j) ≤ f m := by
    intro m hm j
    induction j with
    | zero => simp
    | succ j ih => exact ((hstep (m + j) (by omega)).1).trans ih
  have key : ∀ k, ∀ m ≥ n, f m ≤ k → ∃ N, ∀ m' ≥ N, e.lbl m' ≠ .tau p := by
    intro k
    induction k with
    | zero =>
      intro m hm hf
      refine ⟨m, fun m' hm' heq => ?_⟩
      have h1 := (hstep m' (by omega)).2 heq
      have h2 := hmono m hm (m' - m)
      rw [show m + (m' - m) = m' by omega] at h2
      omega
    | succ k ih =>
      intro m hm hf
      by_cases hex : ∃ m' ≥ m, e.lbl m' = .tau p
      · obtain ⟨m', hm', heq⟩ := hex
        have h1 := (hstep m' (by omega)).2 heq
        have h2 := hmono m hm (m' - m)
        rw [show m + (m' - m) = m' by omega] at h2
        exact ih (m' + 1) (by omega) (by omega)
      · push Not at hex
        exact ⟨m, hex⟩
  exact key (f n) n le_rfl le_rfl

end Impl

namespace Alg4

variable {K : ℕ} [NeZero K]

/-- Upper bound on the remaining steps of the writer. -/
def WPC.pot (K : ℕ) : WPC K → ℕ
  | .idle | .done _ => 0
  | .up _ j => K - j.val
  | .down _ j => K + j.val + 1
  | .setA _ => 2 * K + 1
  | .clrB _ => 2 * K + 2
  | .rdF1' _ => 2 * K + 3
  | .rdF2 _ => 2 * K + 4
  | .setB _ => 2 * K + 5
  | .rdF1 _ => 2 * K + 6
  | .scanB _ j => 3 * K + 6 - j.val

/-- Upper bound on the remaining steps of the reader. -/
def RPC.pot (K : ℕ) : RPC K → ℕ
  | .idle | .done _ => 0
  | .resF2 _ => 1
  | .resF1 _ => 2
  | .clr j _ => K + 2 - j.val
  | .setF2 _ => K + 3
  | .bscan j _ => 2 * K + 3 - j.val
  | .down _ j => 2 * K + 4 + j.val
  | .up true j => 4 * K + 4 - j.val
  | .up false j => 6 * K + 5 - j.val
  | .start => 6 * K + 6

/-- **Algorithm 4 is wait-free.** -/
theorem waitFree (v₀ : Fin K) : (alg4 v₀).WaitFree := by
  refine (alg4 v₀).waitFree_of_potential
    (fun p l => match p with | .w => l.wpc.pot K | .r => l.rpc.pot K) ?_
  intro p l i o k hact x
  cases p with
  | w =>
    simp only [alg4, act, actW] at hact
    cases hw : l.wpc with
    | idle => simp [hw] at hact
    | done v => simp [hw] at hact
    | scanB v j =>
      simp only [hw] at hact; cases hact; dsimp only
      have := j.isLt
      unfold WPC.scanNext; split_ifs <;> simp [WPC.pot] <;> omega
    | setA v =>
      simp only [hw] at hact; cases hact; dsimp only
      have := v.isLt
      rcases WPC.afterSetA_spec v with ⟨_, _, hf⟩ | ⟨_, _, hf⟩ | ⟨_, _, hf⟩ <;> rw [hf] <;>
        simp [WPC.pot] <;> omega
    | down v j =>
      simp only [hw] at hact; cases hact; dsimp only
      have := j.isLt
      rcases WPC.downNext_spec v j with ⟨_, _, hf⟩ | ⟨_, _, hf⟩ | ⟨_, _, hf⟩ <;> rw [hf] <;>
        simp [WPC.pot] <;> first | omega | exact Fin.pos_iff_ne_zero.2 (by rintro rfl; simp_all)
    | up v j =>
      simp only [hw] at hact; cases hact; dsimp only
      have := j.isLt
      rcases WPC.upNext_spec v j with ⟨_, hf⟩ | ⟨_, hf⟩ <;> rw [hf] <;>
        simp [WPC.pot] <;> omega
    | _ =>
      simp only [hw] at hact; cases hact; dsimp only
      first
        | (simp only [WPC.pot]; omega)
        | (cases x <;> simp [WPC.pot])
  | r =>
    simp only [alg4, act, actR] at hact
    cases hr : l.rpc with
    | idle => simp [hr] at hact
    | done val => simp [hr] at hact
    | up b j =>
      simp only [hr] at hact; cases hact; dsimp only
      have := j.isLt
      cases x
      · simp only [Bool.false_eq_true, ite_false]
        unfold RPC.upNext; cases b <;> split_ifs <;> simp [RPC.pot] <;> first | omega | simp_all
      · simp only [ite_true]
        rcases RPC.found_spec j with ⟨_, hf⟩ | ⟨_, _, hf⟩ <;> rw [hf] <;>
          cases b <;> simp [RPC.pot] <;> omega
    | down val j =>
      simp only [hr] at hact; cases hact; dsimp only
      have := j.isLt
      rcases RPC.downNext_spec val j x with ⟨_, hf⟩ | ⟨_, _, hf⟩ <;> rw [hf] <;>
        simp [RPC.pot] <;> first | omega | exact Fin.pos_iff_ne_zero.2 (by rintro rfl; simp_all)
    | bscan j val =>
      simp only [hr] at hact; cases hact; dsimp only
      have := j.isLt
      rcases RPC.bscanNext_spec j val x with ⟨_, hf⟩ | ⟨_, hf⟩ <;> rw [hf] <;>
        simp [RPC.pot] <;> omega
    | clr j val =>
      simp only [hr] at hact; cases hact; dsimp only
      have := j.isLt
      rcases RPC.clrNext_spec j val with ⟨_, hf⟩ | ⟨_, hf⟩ <;> rw [hf] <;>
        simp [RPC.pot] <;> omega
    | _ =>
      simp only [hr] at hact; cases hact; dsimp only
      simp [RPC.pot]

end Alg4

end Cslib.SharedMemory
