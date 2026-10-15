import Papers.PODC2024.HistoryIndependent.ClassC
import Cslib.Computability.Distributed.SharedMemory.Indist
import Mathlib

/-!
# Proposition 19: the reader must write

Proposition 19 of Attiya, Bender, Farach-Colton, Oshman, Schiller, *History-Independent
Concurrent Objects*, PODC 2024: in any wait-free quiescent HI implementation of a SWSR
multi-valued register from binary registers, the reader must write to shared memory.
-/

namespace Cslib.SharedMemory

open List Impl

variable {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

/-- Process `r` never changes the memory: whenever it accesses a base object (in a reachable
configuration), the access leaves the object's state unchanged. -/
def Impl.NeverWrites {A : ObjSpec} (I : Impl A B P L) (r : P) : Prop :=
  ∀ C, I.Reachable C → C.pend r ≠ none → ∀ i o k, I.act r (C.loc r) = .access i o k →
    ((B i).δ (C.mem i) o).1 = C.mem i

/-- Solo steps of a process that never writes do not change the memory. -/
lemma Impl.NeverWrites.iterate_soloStep_mem {A : ObjSpec} {I : Impl A B P L} {r : P}
    (hnw : I.NeverWrites r) {α : List (Label P A)} {C : Config A B P L}
    (hα : I.run α = some C) (k : ℕ) : ((I.soloStep r)^[k] C).mem = C.mem := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set D := (I.soloStep r)^[k] C
    have hD : I.run (α ++ I.soloLabels r C k) = some D := by
      rw [run_append_of_eq I hα, runFrom_soloLabels]
    rw [← ih]
    unfold soloStep
    split_ifs with hp
    · rfl
    · unfold nextLabel
      split
      · rename_i i o kk hact
        have hs : I.step D (.tau r) = some { D with
            mem := Function.update D.mem i ((B i).δ (D.mem i) o).1,
            loc := Function.update D.loc r (kk ((B i).δ (D.mem i) o).2) } := by
          simp [step, hp, hact]
        rw [hs]
        simp only [Option.getD_some]
        rw [hnw D ⟨_, hD⟩ hp i o kk hact, Function.update_eq_self]
      · rename_i x l hact
        cases hs : I.step D (.ret r x) with
        | none => rfl
        | some D' => exact (step_ret hs).2.2.1

/-- **Proposition 19.** The reader must write in any wait-free quiescent HI implementation of a
SWSR `t`-valued register, `t ≥ 3`, from binary registers: if the reader `r` never changes the
memory, the implementation is not both wait-free and quiescent HI. (Any number of processes;
the access discipline is exactly single-writer `w` / single-reader `r`.) -/
theorem prop19 {t : ℕ} (ht : 3 ≤ t) (v₀ : Fin t) (b₀ : ι → Bool)
    (I : Impl (register (Fin t) v₀) (fun i => binaryRegister (b₀ i)) P L) (w r : P) (hwr : w ≠ r)
    (hallow : ∀ p o, I.allowed p o ↔ RWOp.SWSR w r p o) (hnw : I.NeverWrites r) :
    ¬ (I.WaitFree ∧ I.QuiescentHI) := by
  rintro ⟨hwf, h, hlin, hqhi⟩
  have hof := hwf.obstructionFree
  apply cor18 ht v₀ b₀ I w r hwr ((hallow _ _).2 (Or.inr ⟨rfl, rfl⟩))
    (fun v => (hallow _ _).2 (Or.inl ⟨rfl, v, rfl⟩))
  refine ⟨hwf, h, hlin, ?_⟩
  -- every state-quiescent configuration can be completed to a quiescent one by the reader alone,
  -- without changing the memory or the abstract state
  have hcomplete : ∀ α C, I.run α = some C → C.StateQuiescent → ∃ β D,
      I.run (α ++ β) = some D ∧ D.Quiescent ∧ D.mem = C.mem ∧
      linState (h (α ++ β)) = linState (h α) := by
    intro α C hα hsq
    have hval : I.Valid α := ⟨C, hα⟩
    -- ops of processes other than the writer are reads
    have hro : ∀ (γ : List (Label _ _)), I.Valid γ → ∀ p, p ≠ w → ∀ o ∈ opsOf γ p,
        (register (Fin t) v₀).ReadOnly o := by
      intro γ hγ p hp o ho
      have : Label.inv p o ∈ γ := by
        simp only [opsOf, mem_filterMap] at ho
        obtain ⟨ℓ, hℓ, hℓo⟩ := ho
        cases ℓ with
        | inv q o' =>
          simp only [Label.invOf_inv] at hℓo
          split_ifs at hℓo with hq
          · cases hℓo; subst hq; exact hℓ
        | ret => simp at hℓo
        | tau => simp at hℓo
      rcases (hallow _ _).1 (hγ.allowed_of_mem this) with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact absurd rfl hp
      · intro q; rfl
    -- the writer is idle
    have hw : C.pend w = none := by
      by_contra hne
      obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hne
      have hlast := I.run_pend hα ho
      have hmem : Label.inv w o ∈ α := by
        have := mem_of_getLast? hlast
        simp only [opsOf, mem_filterMap] at this
        obtain ⟨ℓ, hℓ, hℓo⟩ := this
        cases ℓ with
        | inv q o' =>
          simp only [Label.invOf_inv] at hℓo
          split_ifs at hℓo with hq
          · cases hℓo; subst hq; exact hℓ
        | ret => simp at hℓo
        | tau => simp at hℓo
      rcases (hallow _ _).1 (hval.allowed_of_mem hmem) with ⟨-, v, rfl⟩ | ⟨h1, -⟩
      · have := hsq w _ ho (if v = ⟨0, by omega⟩ then ⟨1, by omega⟩ else ⟨0, by omega⟩)
        simp only at this
        split_ifs at this with hv
        · rw [hv] at this; simp [Fin.ext_iff] at this
        · exact hv this
      · exact hwr h1
    -- run the reader solo to completion
    have hex : ∃ k, ((I.soloStep r)^[k] C).pend r = none := by
      by_cases hr : C.pend r = none
      · exact ⟨0, hr⟩
      · exact hof C r ⟨α, hα⟩ hr
    set K := I.soloTime r C
    set β := I.soloLabels r C K
    have hrun : I.run (α ++ β) = some ((I.soloStep r)^[K] C) := by
      rw [run_append_of_eq I hα, runFrom_soloLabels]
    have hβr : ∀ ℓ ∈ β, ℓ.proc = r := I.soloLabels_proc r C K
    have hne : ∀ q, q ≠ r → ∀ ℓ ∈ β, ℓ.proc ≠ q := fun q hq ℓ hℓ => by
      rw [hβr ℓ hℓ]; exact Ne.symm hq
    refine ⟨β, _, hrun, ?_, hnw.iterate_soloStep_mem hα K, ?_⟩
    · intro q
      by_cases hq : q = r
      · subst hq; exact I.soloTime_spec q C hex
      · rw [(I.runFrom_other (by rw [runFrom_soloLabels]) (hne q hq)).2]
        by_cases hqw : q = w
        · subst hqw; exact hw
        · exact I.run_pend_eq_none_of_not_allowed hα (fun o ho => by
            rcases (hallow _ _).1 ho with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact hqw h1
            · exact hq h1)
    · have hcw : (respsOf α w).length = (opsOf α w).length := by
        rcases I.run_counts hα w with ⟨-, h1⟩ | ⟨h1, -⟩
        · exact h1.symm
        · exact absurd hw h1
      have hβw : opsOf β w = [] := opsOf_eq_nil_of_proc_ne (hne w hwr)
      have hβw' : respsOf β w = [] := respsOf_eq_nil_of_proc_ne (hne w hwr)
      rw [(hlin _ ⟨_, hrun⟩).linState_of_changer (Valid.wellFormed I ⟨_, hrun⟩) w
          (hro _ ⟨_, hrun⟩),
        (hlin _ hval).linState_of_changer (Valid.wellFormed I hval) w (hro _ hval) hcw,
        opsOf_append, hβw, append_nil]
      rw [opsOf_append, respsOf_append, hβw, hβw', append_nil, append_nil, hcw]
  intro α α' C C' hα hα' hsq hsq' hlin'
  obtain ⟨β, D, hD, hDq, hDm, hDl⟩ := hcomplete α C hα hsq
  obtain ⟨β', D', hD', hDq', hDm', hDl'⟩ := hcomplete α' C' hα' hsq'
  rw [← hDm, ← hDm']
  exact hqhi _ _ _ _ hD hD' hDq hDq' (by rw [hDl, hDl', hlin'])

end Cslib.SharedMemory
