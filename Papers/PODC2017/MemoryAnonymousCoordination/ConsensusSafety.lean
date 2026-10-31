import Papers.PODC2017.MemoryAnonymousCoordination.ConsensusLock

/-!
# Figure 2: agreement and validity (Theorem 4.1, agreement part; Theorem 4.2)

The invariant `Inv` (proved for every reachable configuration, `inv_of_run`) combines
* validity bookkeeping: every value in memory, in a local state or decided was the input of some
  process;
* the ghost invariant of a process `p` in the middle of a collect: *if* everything it has read and
  everything it has not yet read is `(p, y)`, then `y` is locked (`Lock`);
* a process that is about to write after seeing `(p, x)` everywhere, or about to decide `x`, or
  that has decided `x`, knows that `x` is locked.

Since two locked values are equal, all decisions agree.
-/

set_option linter.unusedSectionVars false

namespace Podc.MemoryAnonymousCoordination.Consensus

open Cslib.SharedMemory

variable {P V : Type} {m : ℕ} [DecidableEq V] [DecidableEq P] [Inhabited V]
  {n : ℕ} {sel : P → V → (Fin m → Option (P × V)) → Fin m} {π : P → Equiv.Perm (Fin m)}

/-- `v` was invoked (as an input) by some process in `α`. -/
def Valid (α : List (Label P (taskObj V V))) (v : V) : Prop :=
  ∃ q, (v : (taskObj V V).Op) ∈ opsOf α q

lemma Valid.mono {α : List (Label P (taskObj V V))} (β : List (Label P (taskObj V V))) {v : V}
    (h : Valid α v) : Valid (α ++ β) v := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, by rw [opsOf_append]; exact List.mem_append_left _ hq⟩

/-- All values in a local state are valid. -/
def LocValid (α : List (Label P (taskObj V V))) : Loc P V m → Prop
  | .idle => True
  | .collect x _ view => Valid α x ∧ ∀ j q v, view j = some (q, v) → Valid α v
  | .write x _ _ => Valid α x
  | .done v => Valid α v

lemma LocValid.mono {α : List (Label P (taskObj V V))} (β : List (Label P (taskObj V V)))
    {l : Loc P V m} (h : LocValid α l) : LocValid (α ++ β) l := by
  cases l with
  | idle => trivial
  | collect x k view => exact ⟨h.1.mono β, fun j q v hj => (h.2 j q v hj).mono β⟩
  | write x j b => exact Valid.mono β h
  | done v => exact Valid.mono β h

variable (n π) in
/-- The safety invariant of Figure 2. -/
structure Inv (α : List (Label P (taskObj V V))) (C : Cfg P V m) : Prop where
  idle : ∀ p, C.loc p = .idle → C.pend p = none
  memVal : ∀ r q v, C.mem r = some (q, v) → Valid α v
  locVal : ∀ p, LocValid α (C.loc p)
  outVal : ∀ p (v : V), outputs α p = some v → Valid α v
  ghost : ∀ p x k view y, C.loc p = .collect x k view →
    (∀ j, mixed (π p) k view C.mem j = some (p, y)) → ∃ T, Lock π n y C T
  wlast : ∀ p x j, C.loc p = .write x j true → ∃ T, Lock π n x C T
  done : ∀ p v, C.loc p = .done v → ∃ T, Lock π n v C T
  out : ∀ p (v : V), outputs α p = some v → ∃ T, Lock π n v C T

lemma inv_init : Inv n π [] (I n sel π).initCfg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Impl.initCfg, Impl.unnamed, alg, LocValid, outputs]

lemma inv_step [Fintype P] (hm : m + 1 = 2 * n) (hcard : Fintype.card P ≤ n)
    {α : List (Label P (taskObj V V))} {C C' : Cfg P V m} {ℓ : Label P (taskObj V V)}
    (hI : Inv n π α C) (h : (I n sel π).step C ℓ = some C') : Inv n π (α ++ [ℓ]) C' := by
  have hm0 := pos_of_hm hm
  have hn1 : 1 ≤ n := by omega
  have hex : ∀ w, (∃ T, Lock π n w C T) → ∃ T, Lock π n w C' T := fun w ⟨T, hT⟩ =>
    lock_step hm hT h
  cases ℓ with
  | inv p o =>
    obtain ⟨-, hpend, hmem, hloc⟩ := inv_cases h
    have hsc : C'.loc p = .collect o ⟨0, hm0⟩ (fun _ => none) := by
      rw [hloc]; simp [startCollect, hm0]
    have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
      rw [hloc, Function.update_of_ne hq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      by_cases hqp : q = p
      · subst hqp; rw [hsc] at hq; cases hq
      · rw [hpend, Function.update_of_ne hqp]; exact hI.idle q (by rwa [← hoth q hqp])
    · intro r q v hr; rw [hmem] at hr; exact (hI.memVal r q v hr).mono _
    · intro q
      by_cases hqp : q = p
      · subst hqp; rw [hsc]
        have ho : (o : (taskObj V V).Op) ∈ opsOf (α ++ [.inv q o]) q := by
          rw [opsOf_concat]; apply List.mem_append_right
          simp only [Label.invOf]
          exact List.mem_singleton_self _
        exact ⟨⟨q, ho⟩, by simp⟩
      · rw [hoth q hqp]; exact (hI.locVal q).mono _
    · intro q v hq; rw [outputs_append_inv] at hq; exact (hI.outVal q v hq).mono _
    · intro q x k view y hq hall
      by_cases hqp : q = p
      · subst hqp
        rw [hsc] at hq; obtain ⟨-, rfl, rfl⟩ := hq
        refine ⟨_, lock_establish hcard hsc rfl fun i => ?_⟩
        have := hall i
        rw [mixed_zero _ _ _ _ rfl] at this
        exact this
      · rw [hoth q hqp] at hq; rw [hmem] at hall; exact hex _ (hI.ghost q x k view y hq hall)
    · intro q x j hq
      by_cases hqp : q = p
      · subst hqp; rw [hsc] at hq; cases hq
      · rw [hoth q hqp] at hq; exact hex _ (hI.wlast q x j hq)
    · intro q v hq
      by_cases hqp : q = p
      · subst hqp; rw [hsc] at hq; cases hq
      · rw [hoth q hqp] at hq; exact hex _ (hI.done q v hq)
    · intro q v hq; rw [outputs_append_inv] at hq; exact hex _ (hI.out q v hq)
  | ret p r =>
    obtain ⟨hpn, hdone, hpend, hmem, hloc⟩ := ret_cases h
    have hd : C.loc p = .done r := hdone.resolve_right (fun hi => hpn (hI.idle p hi))
    have hsc : C'.loc p = .idle := by rw [hloc]; simp
    have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
      rw [hloc, Function.update_of_ne hq]
    have hrv : Valid α r := by have := hI.locVal p; rw [hd] at this; exact this
    have hout : ∀ q (v : V), outputs (α ++ [.ret p r]) q = some v →
        outputs α q = some v ∨ (q = p ∧ v = r) := by
      intro q v hq
      rw [outputs_concat] at hq
      cases ho : outputs α q with
      | some v' => rw [ho] at hq; exact Or.inl hq
      | none =>
        rw [ho] at hq
        change (Label.ret p r).retOf q = some v at hq
        rw [Label.retOf_ret] at hq
        split_ifs at hq with hpq
        · exact Or.inr ⟨hpq.symm, (Option.some.inj hq).symm⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      by_cases hqp : q = p
      · subst hqp; rw [hpend]; simp
      · rw [hpend, Function.update_of_ne hqp]; exact hI.idle q (by rwa [← hoth q hqp])
    · intro r' q v hr; rw [hmem] at hr; exact (hI.memVal r' q v hr).mono _
    · intro q
      by_cases hqp : q = p
      · subst hqp; rw [hsc]; trivial
      · rw [hoth q hqp]; exact (hI.locVal q).mono _
    · intro q v hq
      rcases hout q v hq with hq | ⟨-, rfl⟩
      · exact (hI.outVal q v hq).mono _
      · exact hrv.mono _
    · intro q x k view y hq hall
      by_cases hqp : q = p
      · subst hqp; rw [hsc] at hq; cases hq
      · rw [hoth q hqp] at hq; rw [hmem] at hall; exact hex _ (hI.ghost q x k view y hq hall)
    · intro q x j hq
      by_cases hqp : q = p
      · subst hqp; rw [hsc] at hq; cases hq
      · rw [hoth q hqp] at hq; exact hex _ (hI.wlast q x j hq)
    · intro q v hq
      by_cases hqp : q = p
      · subst hqp; rw [hsc] at hq; cases hq
      · rw [hoth q hqp] at hq; exact hex _ (hI.done q v hq)
    · intro q v hq
      rcases hout q v hq with hq | ⟨-, hvr⟩
      · exact hex _ (hI.out q v hq)
      · rw [hvr]; exact hex _ (hI.done p r hd)
  | tau p =>
    obtain ⟨-, hpend, hcase⟩ := tau_cases h
    rcases hcase with ⟨x, k, view, hl, hmem, hloc⟩ | ⟨x, j, b, hl, hmem, hloc⟩
    · -- a read
      have hlv := hI.locVal p
      rw [hl] at hlv
      have hview' : ∀ i q v, Function.update view k (C.mem (π p k)) i = some (q, v) →
          Valid α v := by
        intro i q v hi
        rw [Function.update_apply] at hi
        split_ifs at hi
        · exact hI.memVal _ q v hi
        · exact hlv.2 i q v hi
      have hpl : C'.loc p = afterRead n sel p x k view (C.mem (π p k)) := by rw [hloc]; simp
      have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
        rw [hloc, Function.update_of_ne hq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro q hq
        by_cases hqp : q = p
        · subst hqp; rw [hpl] at hq; unfold afterRead at hq
          split_ifs at hq; simp [finish] at hq
        · rw [hpend]; exact hI.idle q (by rwa [← hoth q hqp])
      · intro r q v hr; rw [hmem] at hr; exact (hI.memVal r q v hr).mono _
      · intro q
        by_cases hqp : q = p
        · subst hqp; rw [hpl]; unfold afterRead
          split_ifs with hk
          · exact ⟨hlv.1.mono _, fun i q' v hi => (hview' i q' v hi).mono _⟩
          · simp only [finish, LocValid]
            rcases adopt_mem hn1 (Function.update view k (C.mem (π q k))) x with h' | ⟨i, q', hi⟩
            · rw [h']; exact hlv.1.mono _
            · exact (hview' i q' _ hi).mono _
        · rw [hoth q hqp]; exact (hI.locVal q).mono _
      · intro q v hq; rw [outputs_append_tau] at hq; exact (hI.outVal q v hq).mono _
      · intro q x' k' view' y hq hall
        by_cases hqp : q = p
        · subst hqp; rw [hpl] at hq; unfold afterRead at hq
          split_ifs at hq with hk
          · simp only [Loc.collect.injEq] at hq; obtain ⟨-, rfl, rfl⟩ := hq
            rw [hmem, mixed_read _ _ _ _ hk] at hall
            exact hex _ (hI.ghost q x k view y hl hall)
          · simp [finish] at hq
        · rw [hoth q hqp] at hq; rw [hmem] at hall; exact hex _ (hI.ghost q x' k' view' y hq hall)
      · intro q x' j' hq
        by_cases hqp : q = p
        · subst hqp; rw [hpl] at hq; unfold afterRead at hq
          split_ifs at hq with hk
          simp only [finish, Loc.write.injEq, decide_eq_true_eq] at hq
          obtain ⟨rfl, -, hall⟩ := hq
          rw [mixed_last _ _ _ _ hk] at hall ⊢
          exact hex _ (hI.ghost q x k view _ hl hall)
        · rw [hoth q hqp] at hq; exact hex _ (hI.wlast q x' j' hq)
      · intro q v hq
        by_cases hqp : q = p
        · subst hqp; rw [hpl] at hq; unfold afterRead at hq
          split_ifs at hq; simp [finish] at hq
        · rw [hoth q hqp] at hq; exact hex _ (hI.done q v hq)
      · intro q v hq; rw [outputs_append_tau] at hq; exact hex _ (hI.out q v hq)
    · -- a write of `(p, x)`
      have hlv := hI.locVal p
      rw [hl] at hlv
      have hpl : C'.loc p = afterWrite x b := by rw [hloc]; simp
      have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
        rw [hloc, Function.update_of_ne hq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro q hq
        by_cases hqp : q = p
        · subst hqp; rw [hpl] at hq; unfold afterWrite at hq
          split_ifs at hq; simp [startCollect, hm0] at hq
        · rw [hpend]; exact hI.idle q (by rwa [← hoth q hqp])
      · intro r q v hr
        rw [hmem, Function.update_apply] at hr
        split_ifs at hr
        · simp only [Option.some.injEq, Prod.mk.injEq] at hr; rw [← hr.2]; exact hlv.mono _
        · exact (hI.memVal r q v hr).mono _
      · intro q
        by_cases hqp : q = p
        · subst hqp; rw [hpl]; unfold afterWrite
          split_ifs
          · exact hlv.mono _
          · simp only [startCollect, hm0, ↓reduceDIte]
            exact ⟨hlv.mono _, by simp⟩
        · rw [hoth q hqp]; exact (hI.locVal q).mono _
      · intro q v hq; rw [outputs_append_tau] at hq; exact (hI.outVal q v hq).mono _
      · intro q x' k' view' y hq hall
        by_cases hqp : q = p
        · subst hqp
          have hq' := hq
          rw [hpl] at hq; unfold afterWrite at hq
          split_ifs at hq
          simp only [startCollect, hm0, ↓reduceDIte, Loc.collect.injEq] at hq
          obtain ⟨-, rfl, -⟩ := hq
          refine ⟨_, lock_establish hcard hq' rfl fun i => ?_⟩
          have := hall i
          rw [mixed_zero _ _ _ _ rfl] at this
          exact this
        · rw [hoth q hqp] at hq
          refine hex _ (hI.ghost q x' k' view' y hq fun i => ?_)
          have hi := hall i
          rw [hmem] at hi
          rcases mixed_write (π q) k' view' C.mem (π p j) (some (p, x)) i with h' | ⟨h', -⟩
          · rwa [h'] at hi
          · rw [h'] at hi
            simp only [Option.some.injEq, Prod.mk.injEq] at hi
            exact absurd hi.1.symm hqp
      · intro q x' j' hq
        by_cases hqp : q = p
        · subst hqp; rw [hpl] at hq; unfold afterWrite at hq
          split_ifs at hq; simp [startCollect, hm0] at hq
        · rw [hoth q hqp] at hq; exact hex _ (hI.wlast q x' j' hq)
      · intro q v hq
        by_cases hqp : q = p
        · subst hqp; rw [hpl] at hq; unfold afterWrite at hq
          split_ifs at hq with hb
          · simp only [Loc.done.injEq] at hq; subst hq; subst hb
            exact hex _ (hI.wlast q x j hl)
          · simp [startCollect, hm0] at hq
        · rw [hoth q hqp] at hq; exact hex _ (hI.done q v hq)
      · intro q v hq; rw [outputs_append_tau] at hq; exact hex _ (hI.out q v hq)

lemma inv_of_run [Fintype P] (hm : m + 1 = 2 * n) (hcard : Fintype.card P ≤ n)
    {α : List (Label P (taskObj V V))} {C : Cfg P V m} (h : (I n sel π).run α = some C) :
    Inv n π α C :=
  Impl.run_induction (Q := fun α C => Inv n π α C) inv_init
    (fun _ _ _ _ _ hI hs => inv_step hm hcard hI hs) h

lemma safe [Fintype P] (hm : m + 1 = 2 * n) (hcard : Fintype.card P ≤ n)
    {α : List (Label P (taskObj V V))} {C : Cfg P V m} (hC : (I n sel π).run α = some C)
    (hos : OneShot α) : (consensus P V).Δ (inputs α) (outputs α) := by
  have hI : Inv n π α C := inv_of_run (sel := sel) hm hcard hC
  refine ⟨?_, ?_⟩
  · intro p q x y hx hy
    obtain ⟨T, hT⟩ := hI.out p x hx
    obtain ⟨T', hT'⟩ := hI.out q y hy
    exact hT.eq hm hT'
  · intro p y hy
    obtain ⟨q, hq⟩ := hI.outVal p y hy
    refine ⟨q, ?_⟩
    have hlen := hos q
    unfold inputs
    rcases hl : opsOf α q with _ | ⟨a, _ | ⟨b, t⟩⟩
    · rw [hl] at hq; exact absurd hq List.not_mem_nil
    · rw [hl] at hq; exact congrArg some (List.mem_singleton.1 hq).symm
    · rw [hl] at hlen; exact absurd hlen (by simp)

/-- Agreement and validity for `m + 1 = 2n` registers. -/
theorem solves_of_hm [Fintype P] (hm : m + 1 = 2 * n) (hcard : Fintype.card P ≤ n) :
    ((alg n sel).unnamed π).Solves (consensus P V) := fun α hα hos => by
  obtain ⟨C, hC⟩ := hα
  exact safe (sel := sel) hm hcard hC hos

end Podc.MemoryAnonymousCoordination.Consensus
