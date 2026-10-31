import Papers.PODC2015.ExactMajorityAVC.AVCProb

/-!
# The pseudocode of Figure 1, taken literally, does not solve majority

Line 12 of Figure 1 reads `weight(x) · weight(y) = 0 and value(x) + value(y) > 0`. With this
condition a weak state meeting a state of *negative* value falls through to line 19, which leaves
both states unchanged: `+0` never becomes `−0`. When `B` is the majority this can be fatal.

Counterexample (`m = 1`, `d = 1`, i.e. the four-state protocol, `n = 3`): inputs `A, B, B`, i.e.
states `1₁, −1₁, −1₁`. The interaction of the first two agents (line 15/17) produces `−0, +0`;
the configuration `−0, +0, −1₁` is *silent* (every interaction leaves it unchanged), and agent `1`
outputs the minority value `A` forever. Under the uniformly random scheduler this configuration is
reached after one step with positive probability, so the probability of not having converged to
the majority does not tend to `0` (`not_tendsto_literal`). The same happens for every `m`
(the model checker finds `+3, −3, −3` for `m = 3`).

The intended condition is evident from the prose ("if a node with 0 weight meets a node with
non-zero weight, then it will adopt the sign of the interaction partner"); the corrected protocol
`avc` is proved correct in `AVCProb.lean`.
-/

namespace Podc.ExactMajorityAVC

open Cslib.PopulationProtocol Cslib.TransitionSystem Cslib.Probability.Markov St Filter Topology

/-- The literal protocol of Figure 1 on valid states. -/
def avcLitV {m d : ℕ} (hd : 1 ≤ d) (hm : m % 2 = 1) : Protocol (VSt m d) :=
  ⟨fun x y => (⟨_, (valid_update true hd hm x.2 y.2).1⟩, ⟨_, (valid_update true hd hm x.2 y.2).2⟩)⟩

/-- The inputs `A, B, B`. -/
def inpABB : Fin 3 → Bool := ![true, false, false]

/-- `B` is the strict majority. -/
lemma inpABB_majority : numInput inpABB true < numInput inpABB false := by decide

/-- The initial configuration `1₁, −1₁, −1₁` (`m = d = 1`). -/
def initABB : Config (Fin 3) (VSt 1 1) := initCfg le_rfl rfl inpABB

/-- The configuration `−0, +0, −1₁`. -/
def stuck : Config (Fin 3) (VSt 1 1) :=
  ![⟨zero false, trivial⟩, ⟨zero true, trivial⟩, ⟨one false 1, le_rfl, le_rfl⟩]

lemma initABB_step_stuck : (avcLitV le_rfl rfl).interact initABB 0 1 = stuck := by
  decide

/-- The configuration `−0, +0, −1₁` is silent for the literal protocol. -/
lemma stuck_silent : ∀ a b : Fin 3, a ≠ b → (avcLitV le_rfl rfl).interact stuck a b = stuck := by
  decide

lemma stuck_not_converged : ¬ Converged false (lift stuck) := fun h => by
  simpa [lift, stuck] using h 1

/-- **The literal pseudocode fails (reachability form).** From the initial configuration
`A, B, B` the literal protocol reaches a configuration from which no configuration where all
agents output the majority value `B` is reachable. -/
theorem literal_fails :
    (avcLitV le_rfl rfl).Reachable initABB stuck ∧
      ∀ E, (avcLitV le_rfl rfl).Reachable stuck E → ¬ Converged false (lift E) := by
  refine ⟨.single ⟨0, 1, by decide, initABB_step_stuck.symm⟩, fun E hE => ?_⟩
  have : E = stuck := by
    induction hE with
    | refl => rfl
    | tail _ hs ih =>
      subst ih; obtain ⟨a, b, hab, rfl⟩ := hs; exact stuck_silent a b hab
  subst this; exact stuck_not_converged

open Classical in
/-- **The literal pseudocode does not solve majority with probability 1.** Under the uniformly
random scheduler, started from inputs `A, B, B` (majority `B`), the probability that not all
agents output `B` after `t` steps does not tend to `0`. -/
theorem not_tendsto_literal :
    ¬ Tendsto (fun t => ∑ D ∈ {D | ¬ Converged false (lift D)}.toFinset,
      (uniformKernel (avcLitV le_rfl rfl) ^ t) initABB D) atTop (𝓝 0) := by
  set T := uniformKernel (A := Fin 3) (avcLitV (m := 1) (d := 1) le_rfl rfl)
  have hT : T ∈ Matrix.rowStochastic ℝ _ := uniformKernel_mem _ (by simp)
  have hpos : ∀ C D, 0 < T C D ↔ (avcLitV le_rfl rfl).Step C D := fun C D => by
    rw [uniformKernel_pos_iff, Protocol.toN_step_iff]
  -- the mass stays at `stuck`
  have hstay : ∀ k, (T ^ k) stuck stuck = 1 := by
    intro k
    have hout : ∀ E ∈ (Finset.univ.erase stuck), (T ^ k) stuck E = 0 := by
      intro E hE
      refine pow_eq_zero_of_closed hT (· = stuck) (fun F G hF hFG => ?_) rfl k
        (Finset.ne_of_mem_erase hE)
      subst hF; obtain ⟨a, b, hab, rfl⟩ := (hpos _ _).1 hFG; exact stuck_silent a b hab
    have := pow_sum_row hT k stuck
    rwa [← Finset.add_sum_erase _ _ (Finset.mem_univ stuck), Finset.sum_eq_zero hout,
      add_zero] at this
  have hc : 0 < T initABB stuck :=
    (hpos _ _).2 ⟨0, 1, by decide, initABB_step_stuck.symm⟩
  have hlow : ∀ k, T initABB stuck ≤
      ∑ D ∈ {D | ¬ Converged false (lift D)}.toFinset, (T ^ (k + 1)) initABB D := by
    intro k
    calc T initABB stuck = T initABB stuck * (T ^ k) stuck stuck := by rw [hstay, mul_one]
      _ ≤ ∑ E, T initABB E * (T ^ k) E stuck :=
          Finset.single_le_sum (f := fun E => T initABB E * (T ^ k) E stuck)
            (fun E _ => mul_nonneg (Matrix.nonneg_of_mem_rowStochastic hT) (pow_nonneg_entry hT k E stuck))
            (Finset.mem_univ stuck)
      _ = (T ^ (k + 1)) initABB stuck := by rw [pow_succ', Matrix.mul_apply]
      _ ≤ _ := Finset.single_le_sum (fun D _ => pow_nonneg_entry hT (k + 1) initABB D)
            (Set.mem_toFinset.2 stuck_not_converged)
  intro h
  have h' := (tendsto_add_atTop_iff_nat 1).2 h
  have := ge_of_tendsto h' (Eventually.of_forall hlow)
  linarith

end Podc.ExactMajorityAVC
