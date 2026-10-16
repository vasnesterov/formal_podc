import Papers.PODC2019.HotStuff.Basic.Liveness

/-!
# Basic HotStuff: main results

* `lemma_1`, `theorem_2` (abstract asynchronous system, `Safety.lean`);
* `lemma_3` (abstract system);
* `impl_theorem_2`: safety of the partially synchronous implementation (via the refinement);
* `theorem_4` (`Liveness.lean`): liveness of the implementation;
* `nonvacuous`: a concrete run (`n = 4`, one silent Byzantine replica) in which every correct
  replica commits a new command.
-/

namespace HotStuff.Basic

open Classical Cslib.Byzantine.PartialSync

variable {P C : Type*} [Fintype P] [DecidableEq P]

/-- **Lemma 3.** If a correct replica is locked on a (non-genesis) `precommitQC`, then at least
`f + 1` correct replicas voted `pre-commit` for it, i.e. stored a matching `prepareQC`; their
current `prepareQC` has a view at least as high. -/
theorem lemma_3 {f : ℕ} {F : Finset P} (hF : F.card ≤ f) (h3 : 3 * f < Fintype.card P)
    {s : St P C} (hs : Reach f F s) {r : P} (hr : r ∉ F) (hl : ¬ (s.loc r).lock.IsGen) :
    f + 1 ≤ (Finset.univ.filter fun i => i ∉ F ∧ (i, (s.loc r).lock) ∈ s.votes ∧
      (s.loc r).lock.view ≤ (s.loc i).prepQC.view).card := by
  have hI := hs.inv
  obtain ⟨hv, hty⟩ := (hI.loc r hr).lock_valid
  have hty := hty.resolve_left hl
  rcases hv with hv | hv
  · exact absurd hv hl
  have hsub : signers F s.votes (s.loc r).lock ⊆ F ∪ (Finset.univ.filter fun i => i ∉ F ∧
      (i, (s.loc r).lock) ∈ s.votes ∧ (s.loc r).lock.view ≤ (s.loc i).prepQC.view) := by
    intro i hi
    rw [mem_signers] at hi
    by_cases hiF : i ∈ F
    · exact Finset.mem_union_left _ hiF
    · have hvi := hi.resolve_left hiF
      refine Finset.mem_union_right _ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hiF, hvi, (hI.loc i hiF).prep_ge _ hvi hty⟩
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

variable {f : ℕ} {leader : ℕ → P} {R : Run P (Msg P C) (Inp C)} {δ : ℕ}

/-- **Theorem 2 for the implementation.** In every run of the partially synchronous
implementation (any GST, any delays, any pacemaker behaviour, Byzantine replicas restricted only
by unforgeability), no two correct replicas ever commit conflicting nodes. -/
theorem impl_theorem_2 (hR : R.Valid f δ) (hA : R.AuthValid auth (hotstuff f leader))
    (h3 : 3 * f < Fintype.card P) {p q : P} (hp : p ∉ R.faulty) (hq : q ∉ R.faulty)
    {τ τ' : ℕ} {x y : Node C} (hx : x ∈ (R.st (hotstuff f leader) τ p).committed)
    (hy : y ∈ (R.st (hotstuff f leader) τ' q).committed) : ¬ Conflict x y := by
  have hs := abs_reach hA (max τ τ')
  have hx' := committed_mono R (le_max_left τ τ') p hx
  have hy' := committed_mono R (le_max_right τ τ') q hy
  refine theorem_2 hR.card_faulty h3 hs hp hq ?_ ?_
  · simp only [absSt, hp, ite_false]; exact hx'
  · simp only [absSt, hq, ite_false]; exact hy'

/-! ### Non-vacuity -/

/-- A concrete run: four replicas, replica `3` Byzantine and silent, GST `= 0`, instantaneous
delivery, no pacemaker interrupts, client commands `cmd`. -/
def exRun {C : Type*} (cmd : ℕ → C) : Run (Fin 4) (Msg (Fin 4) C) (Inp C) where
  faulty := {3}
  inp _ := (fun _ => false, cmd)
  gst := 0
  byz _ _ _ := []
  dl _ τ _ := τ

/-- Round-robin leaders. -/
def rr (v : ℕ) : Fin 4 := ⟨v % 4, Nat.mod_lt _ (by norm_num)⟩

theorem exRun_valid {C : Type*} (cmd : ℕ → C) : (exRun cmd).Valid 1 1 where
  card_faulty := by simp [exRun]
  dl_ge _ _ _ _ _ := le_rfl
  dl_le _ τ _ _ _ := by simp [exRun]

theorem exRun_authValid {C : Type*} (cmd : ℕ → C) : (exRun cmd).AuthValid auth (hotstuff 1 rr) :=
  Run.authValid_of_canonical (fun _ _ _ _ => rfl)

theorem exRun_correct {C : Type*} {cmd : ℕ → C} {r : Fin 4} (hr : r ≠ 3) :
    r ∉ (exRun cmd).faulty := by
  show r ∉ ({3} : Finset (Fin 4)); simpa using hr

theorem exRun_view {C : Type*} (cmd : ℕ → C) : ∀ p ∉ (exRun cmd).faulty,
    ((exRun cmd).st (hotstuff 1 rr) 0 p).view = 1 := fun _ _ => rfl

theorem exRun_nv {C : Type*} (cmd : ℕ → C) : ∀ p ∉ (exRun cmd).faulty, ∀ τ, 0 ≤ τ →
    τ < 0 + 8 * (1 + 1) → ((exRun cmd).inp p).1 τ = false := fun _ _ _ _ _ => rfl

/-- **Non-vacuity of Theorem 4.** With `n = 4`, `f = 1`, one silent Byzantine replica, `δ = 1`
and round-robin leaders, every correct replica has committed, by time `0 + 8 (δ + 1) = 16`, the
proposal of view `1`: a node whose newest command is the client command `cmd 1`. -/
theorem nonvacuous {C : Type*} (cmd : ℕ → C) :
    ∃ x j, (1, x, j) ∈ ((exRun cmd).st (hotstuff 1 rr) (0 + 8 * (1 + 1)) (rr 1)).props ∧
      x = cmd 1 :: (QCm.qc j).node ∧ ∀ r ∉ (exRun cmd).faulty,
        x ∈ ((exRun cmd).st (hotstuff 1 rr) (0 + 8 * (1 + 1)) r).committed :=
  theorem_4 (R := exRun cmd) (f := 1) (leader := rr) (δ := 1) (exRun_valid cmd)
    (exRun_authValid cmd) (by simp) (v := 1) (t₀ := 0) le_rfl (exRun_correct (by decide))
    (exRun_view cmd) (exRun_nv cmd)

end HotStuff.Basic
