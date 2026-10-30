import Papers.PODC2025.AuditingWithoutLeaks.Inv

/-!
# Auxiliary invariants for the linearizability proof of Algorithm 1

* `DInv2`: during a `D` phase (`R.seq = SN + 1`) some writer is poised at line 15 with the
  sequence number `R.seq` and a pending `write R.val` (the visible write of the phase).
* `BInv`: the Boolean registers `B[t][·]` are still `false` for `t > R.seq`, and `B[R.seq][i]`
  is set only for readers recorded in the tracking bits.
-/

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au] {v₀ : V}
  {rnd : ℕ → Fin m → Bool} {C C' : Cfg m W Au V v₀}

/-- The visible writer of a `D` phase. -/
def DInv2 (C : Cfg m W Au V v₀) : Prop :=
  (rOf C).seq = snOf C + 1 →
    ∃ w, C.loc (.wr w) = .wHelp (rOf C).seq ∧ C.pend (.wr w) = some (.write (rOf C).val)

/-- The Boolean registers above `R.seq` are untouched. -/
def BInv (rnd : ℕ → Fin m → Bool) (C : Cfg m W Au V v₀) : Prop :=
  ∀ t i, (rOf C).seq ≤ t → (C.mem (.B t i) : Bool) = true →
    t = (rOf C).seq ∧ (rOf C).bits i ≠ rnd t i

lemma val_eq_of_seq_eq (E : Evo rnd C C') (h : (rOf C').seq = (rOf C).seq) :
    (rOf C').val = (rOf C).val := by
  have := E.hv (rOf C).seq le_rfl
  simp only [AuditingWithoutLeaks.hv, ite_true] at this
  rwa [← h, if_pos rfl] at this

theorem DInv2.step (hI : Inv rnd C) (hD : DInv2 C) {ℓ : Label (Proc m W Au) (auditReg m V v₀)}
    (hs : (alg1 rnd v₀).step C ℓ = some C') : DInv2 C' := by
  obtain ⟨hI', E⟩ := Inv.step hI hs
  intro hD'
  by_cases hseq : (rOf C').seq = (rOf C).seq
  · have hsn : snOf C' = snOf C := by
      have := E.sn; have := hI.seq_le; omega
    have hval := val_eq_of_seq_eq E hseq
    obtain ⟨w, hw, hwp⟩ := hD (by rw [← hseq, hD', hsn])
    rw [hseq, hval]
    refine ⟨w, ?_⟩
    cases ℓ with
    | inv p o =>
      obtain ⟨h0, -, hpend, hloc, -⟩ := Impl.step_inv hs
      have hne : Proc.wr w ≠ p := by
        rintro rfl; rw [h0] at hwp; cases hwp
      rw [hloc, hpend, Function.update_of_ne hne, Function.update_of_ne hne]; exact ⟨hw, hwp⟩
    | ret p r =>
      obtain ⟨-, hpend, -, l, hact, hloc⟩ := Impl.step_ret hs
      have hne : Proc.wr w ≠ p := by
        rintro rfl; rw [hw] at hact; simp [alg1, writerAct] at hact
      rw [hloc, hpend, Function.update_of_ne hne, Function.update_of_ne hne]; exact ⟨hw, hwp⟩
    | tau p =>
      obtain ⟨-, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
      rw [hpend]
      by_cases hne : Proc.wr w = p
      · subst hne
        rw [hw] at hact
        simp only [alg1, writerAct, Action.access.injEq] at hact
        obtain ⟨rfl, ho, -⟩ := hact
        obtain rfl := eq_of_heq ho
        exfalso
        have : snOf C' = (rOf C).seq := by
          have h1 : snOf C = (rOf C).seq - 1 := by omega
          simp only [snOf] at h1 ⊢
          simp [hmem, casObject, h1]
        omega
      · rw [hloc, Function.update_of_ne hne]; exact ⟨hw, hwp⟩
  · cases ℓ with
    | inv p o =>
      obtain ⟨-, -, -, -, hmem⟩ := Impl.step_inv hs
      exact absurd (by simp [rOf, hmem]) hseq
    | ret p r =>
      obtain ⟨-, -, hmem, -⟩ := Impl.step_ret hs
      exact absurd (by simp [rOf, hmem]) hseq
    | tau p =>
      obtain ⟨-, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
      cases p with
      | rd j =>
        exfalso; apply hseq
        cases hl : C.loc (.rd j) <;> simp only [alg1, readerAct, hl, reduceCtorEq] at hact <;>
          simp only [Action.access.injEq] at hact <;> obtain ⟨rfl, ho, -⟩ := hact <;>
          obtain rfl := eq_of_heq ho <;> simp [rOf, hmem]
      | au a =>
        exfalso; apply hseq
        cases hl : C.loc (.au a) <;> simp only [alg1, auditorAct, hl, reduceCtorEq] at hact <;>
          simp only [Action.access.injEq] at hact <;> obtain ⟨rfl, ho, -⟩ := hact <;>
          obtain rfl := eq_of_heq ho <;> simp [rOf, hmem]
      | wr w =>
        refine ⟨w, ?_⟩
        have hw := hI.wr w
        unfold WInv at hw
        cases hl : C.loc (.wr w) <;> rw [hl] at hw <;>
          simp only [alg1, writerAct, hl, reduceCtorEq] at hact
        case wCAS v sn r =>
          simp only [Action.access.injEq] at hact
          obtain ⟨rfl, ho, hk⟩ := hact
          obtain rfl := eq_of_heq ho
          obtain rfl := eq_of_heq hk
          by_cases heq : (C.mem .R : RVal m V) = r
          · have : (C'.mem .R : RVal m V) = ⟨sn, v, rnd sn⟩ := by simp [hmem, heq]
            simp [hloc, heq, rOf, this, hpend, hw.1]
          · exact absurd (by simp [rOf, hmem, heq]) hseq
        case wB v sn r todo =>
          cases todo with
          | nil => simp at hact
          | cons j rest =>
            simp only [Action.access.injEq] at hact
            obtain ⟨rfl, -, -⟩ := hact
            exact absurd (by simp [rOf, hmem]) hseq
        all_goals
          simp only [Action.access.injEq] at hact
          obtain ⟨rfl, ho, -⟩ := hact
          obtain rfl := eq_of_heq ho
          exact absurd (by simp [rOf, hmem]) hseq

theorem BInv.step (hI : Inv rnd C) (hB : BInv rnd C) {ℓ : Label (Proc m W Au) (auditReg m V v₀)}
    (hs : (alg1 rnd v₀).step C ℓ = some C') : BInv rnd C' := by
  obtain ⟨hI', E⟩ := Inv.step hI hs
  intro t i ht hb
  -- generic facts: if `B[t][i]` was already set, use the evolution of `R`
  have old : (C.mem (.B t i) : Bool) = true → t = (rOf C').seq ∧ (rOf C').bits i ≠ rnd t i := by
    intro hb0
    obtain ⟨h1, h2⟩ := hB t i (le_trans E.seq ht) hb0
    have hseq : (rOf C').seq = (rOf C).seq := by have := E.seq; omega
    have hf : Fetched rnd C i t := Or.inr ⟨h1, h2⟩
    rcases E.fet _ _ hf with ⟨h3, -⟩ | ⟨h3, h4⟩
    · omega
    · exact ⟨h3, h4⟩
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, -, -, hmem⟩ := Impl.step_inv hs
    exact old (by simpa [hmem] using hb)
  | ret p r =>
    obtain ⟨-, -, hmem, -⟩ := Impl.step_ret hs
    exact old (by simpa [hmem] using hb)
  | tau p =>
    obtain ⟨-, hpend, i', o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
    by_cases hi : i' = Obj.B t i
    · subst hi
      -- a writer writes `B[t][i]` at line 13
      cases p with
      | rd j =>
        cases hl : C.loc (.rd j) <;> simp only [alg1, readerAct, hl, reduceCtorEq] at hact <;>
          simp only [Action.access.injEq] at hact <;> obtain ⟨h, -, -⟩ := hact <;> cases h
      | au a =>
        cases hl : C.loc (.au a) <;> simp only [alg1, auditorAct, hl, reduceCtorEq] at hact <;>
          simp only [Action.access.injEq] at hact <;> obtain ⟨h, ho, -⟩ := hact <;> cases h
        obtain rfl := eq_of_heq ho
        exact old (by simpa [hmem] using hb)
      | wr w =>
        have hw := hI.wr w
        unfold WInv at hw
        cases hl : C.loc (.wr w) <;> rw [hl] at hw <;>
          simp only [alg1, writerAct, hl, reduceCtorEq] at hact <;>
          try (simp only [Action.access.injEq] at hact; obtain ⟨h, -, -⟩ := hact; cases h; done)
        case wB v sn r todo =>
          cases todo with
          | nil => simp at hact
          | cons j rest =>
            simp only [Action.access.injEq] at hact
            obtain ⟨h, -, -⟩ := hact
            cases h
            obtain ⟨-, hwr, -, -, hrd, -⟩ := hw
            have hf := hwr.2.2.2.1 i (hrd i (by simp))
            have hR : rOf C' = rOf C := by simp [rOf, hmem]
            rw [hR] at ht ⊢
            rcases hf with ⟨h1, -⟩ | ⟨h1, h2⟩
            · omega
            · exact ⟨h1, h2⟩
    · exact old (by simpa [hmem, Function.update_of_ne (Ne.symm hi)] using hb)

lemma BInv.init : BInv rnd ((alg1 rnd v₀ : Impl _ _ (Proc m W Au) _).initCfg) := by
  intro t i _ h; simp [Impl.initCfg, alg1] at h

lemma DInv2.init : DInv2 ((alg1 rnd v₀ : Impl _ _ (Proc m W Au) _).initCfg) := by
  intro h; simp [rOf, snOf, Impl.initCfg, alg1] at h

end Podc.AuditingWithoutLeaks
