import Papers.PODC2015.MinimalSynchronyBC.Counterexample
import Papers.PODC2015.MinimalSynchronyBC.Consensus

/-!
# Sanity checks of the operational model

The machine of `Machine.lean` is not degenerate: in fault-free synchronous runs the algorithm of
Figure 4 decides (`sanity_decides`), also with mixed proposals and with a crashed process whose
round is coordinated by a correct process.
-/

namespace MinimalSynchronyBC.Sanity

open Cslib.Byzantine.PartialSync

/-- `n = 4`, `t = 1`, mixed proposals, no faults, zero delays: everybody decides `true` by
time 12 (checked by evaluation). -/
theorem sanity_decides :
    ∀ p : Fin 4, ((simStates (alg (V := Bool) (paperParams 4 1)) (fun p => decide (p.val ≠ 2))
      (fun _ => false) (fun _ _ _ => []) (init (paperParams 4 1) true) 12).getD p
        (init (paperParams 4 1) true)).dec = some true := by
  decide +kernel

/-- `n = 7`, `t = 2`, proposals as in the blocking run, process `6` crashed initially (it
coordinates round 7 only), zero delays: everybody decides by time 12. -/
theorem sanity_decides_crash :
    ∀ p : Fin 7, p.val ≠ 6 → ((simStates (alg (V := Bool) (paperParams 7 2))
      (fun p => decide (p.val ≤ 3)) (fun p => decide (p.val = 6)) (fun _ _ _ => [])
      (init (paperParams 7 2) true) 12).getD p (init (paperParams 7 2) true)).dec = some true := by
  decide +kernel

/-- With the repair `fixTimer` (a process returning at line 4 of Figure 3 also sets its timer, so
that it relays), the run of `theorem4_termination_false` is no longer stuck: every correct
process decides `true` by time 30 (checked by evaluation). -/
theorem repaired_blocking_run_decides :
    ∀ p : Fin 7, p.val ≠ 0 →
      (((simHist (alg (V := Bool) { paperParams 7 2 with fixTimer := true }) Blocking.R.inp
        Blocking.bad Blocking.R.byz Blocking.R.dl (init (paperParams 7 2) true) 30).getD 30
          []).getD p (init (paperParams 7 2) true)).dec = some true := by
  decide +kernel

/-! ### The hypotheses of the abstract layer are satisfiable -/

/-- A one-process execution of Figure 4 in which everything happens at time 0. -/
def triv : Fig4 (Fin 1) Bool where
  inp _ := true
  cb0 := { valid := fun _ _ => {true}, ret := fun _ => some (0, true) }
  est _ r := if r = 0 then none else some true
  ea _ r := if r = 0 then none else some true
  t5 _ r := r
  acIn _ r := if r = 0 then none else some true
  ac _ r := if r = 0 then none else some (.commit, true)
  D r _ _ _ := if r = 0 then none else some true
  decT _ := some (0, true)

theorem triv_follows : triv.Follows 0 ∅ where
  cb0 := { mono := fun _ => le_rfl
           op_termination := fun _ _ _ _ => rfl
           op_validity := fun _ h => by cases h; rfl
           set_termination := fun _ _ _ _ => ⟨0, ⟨true, rfl⟩⟩
           set_validity := fun {i τ v} _ hv => ⟨0, by simp, by simp_all [triv]⟩
           set_agreement := fun _ _ => ⟨0, fun _ _ => rfl⟩ }
  est0 _ := rfl
  est1 _ := rfl
  ea_est {i r v} _ h := by simp_all [triv]
  ea_valid r v hv i _ w hw := by
    simp only [triv] at hw hv
    split_ifs at hw with hr
    cases hw
    rcases hv 0 (by simp) with h | h <;> simp_all
  line5 {i r u e} _ hu he := by
    simp only [triv] at hu he ⊢
    split_ifs at hu he ⊢ with hr
    cases hu; cases he; simp
  acIn_none {i r} _ h := by simp_all [triv]
  ac r := { termination := fun h _ i _ => by
              have := h 0 (by simp); simp only [triv] at this ⊢; split_ifs at this ⊢ <;> simp_all
            domain := fun {i d v} _ h => ⟨0, by simp, by simp only [triv] at h ⊢; split_ifs at h ⊢ <;> simp_all⟩
            obligation := fun {v i d w} hv _ h => by
              simp only [triv] at h hv
              split_ifs at h hv with hr
              cases h
              rcases hv 0 (by simp) with h' | h' <;> simp_all
            quasi := fun {i k v d w} _ _ h1 h2 => by
              simp only [triv] at h1 h2; split_ifs at h1 h2 <;> simp_all }
  next {i r v} _ hr h := by simp only [triv] at h ⊢; split_ifs at h ⊢ <;> simp_all
  dec_rb r := { mono := fun h _ => h
                validity := fun {i j τ v} _ _ h => by
                  simp only [Fig4.decBc, triv] at h ⊢; split_ifs at h ⊢ <;> simp_all
                term1 := fun {i j v} _ _ h => ⟨0, by
                  simp only [Fig4.decBc, triv] at h ⊢; split_ifs at h ⊢ <;> simp_all⟩
                term2 := fun {_ _ _ τ _} _ _ h => ⟨τ, h⟩ }
  line9 {i τ v} _ h := by
    cases h
    have : triv.decFrom i 0 true = Set.univ := Set.eq_univ_of_forall fun j => ⟨1, rfl⟩
    rw [this, Set.ncard_univ]; simp

theorem triv_live : triv.Live 0 1 ∅ where
  mvalued := ⟨{true}, by simp, fun _ _ v h => by cases h; simp [triv]⟩
  nt := by simp
  ea_term r hr _ i _ := by simp [triv]; omega
  ea_ev _ r₀ := ⟨r₀ + 1, by omega, true, fun _ _ => by simp [triv], 0, by simp, by simp [triv]⟩
  cont {i r} _ hr _ _ := by simp [triv]
  t5_ge _ _ := le_rfl
  dec_live _ _ := rfl

/-- Hence `Fig4.termination` and the safety theorems are not vacuous. -/
example : ∀ i ∉ (∅ : Finset (Fin 1)), (triv.decT i).isSome :=
  Fig4.termination triv_follows triv_live (by simp) (by simp)

end MinimalSynchronyBC.Sanity
