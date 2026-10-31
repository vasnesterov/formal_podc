import Papers.PODC2015.ExactMajorityAVC.AVCCorrect
import Cslib.Computability.Distributed.PopulationProtocols.RandomScheduler
import Cslib.Computability.Distributed.SelfStabilization.Markov

/-!
# AVC solves exact majority with probability 1 (Lemma A.1, Theorem 4.1, first part)

The random scheduler of the paper (Section 2): at each step an ordered pair of distinct agents is
drawn uniformly at random. On the finite set of configurations over the valid states `VSt m d`
this is the Markov kernel `Cslib.PopulationProtocol.uniformKernel`. Through CSLib's bridge
"reachability of a closed set from everywhere ⇒ probability `1`"
(`Cslib.TransitionSystem.tendsto_compl_of_reach`) we obtain:

* `lemma_A_1`: from every valid configuration with value sum `S ≠ 0`, the probability that not
  all agents have sign `sgn S` after `t` steps tends to `0`; and once all agents have sign
  `sgn S`, no agent ever changes its sign (`lemma_A_1_closed`);
* `theorem_4_1_correct`: AVC started from an input with a strict majority outputs the majority
  value at all agents with probability tending to `1`, and keeps it forever.

The expected-time bound `n³(m + d + 1)` of Lemma A.1 and the polylogarithmic bounds of
Theorem 4.1 are not formalized.
-/

namespace Podc.ExactMajorityAVC

open Cslib.PopulationProtocol Cslib.TransitionSystem Cslib.Probability.Markov St Filter Topology

/-- The valid states, a finite type. -/
abbrev VSt (m d : ℕ) := {x : St // x.Valid m d}

/-- The finite set of valid states. -/
def validFinset (m d : ℕ) : Finset St :=
  {zero true, zero false} ∪ ((Finset.Icc 1 d).image (one true) ∪ (Finset.Icc 1 d).image (one false))
    ∪ (Finset.Icc (-(m : ℤ)) m).image strong

lemma mem_validFinset {m d : ℕ} {x : St} (hx : x.Valid m d) : x ∈ validFinset m d := by
  rcases x with ⟨_ | _⟩ | ⟨_ | _, j⟩ | v <;> simp_all [validFinset, Valid]
  simp only [abs_eq_max_neg] at hx; omega

lemma finite_valid (m d : ℕ) : {x : St | x.Valid m d}.Finite :=
  (validFinset m d).finite_toSet.subset fun _ hx => mem_validFinset hx

noncomputable instance (m d : ℕ) : Fintype (VSt m d) := (finite_valid m d).fintype

variable {m d : ℕ}

set_option linter.unusedSectionVars false

/-- AVC on the finite type of valid states. -/
def avcV (hd : 1 ≤ d) (hm : m % 2 = 1) : Protocol (VSt m d) :=
  ⟨fun x y => (⟨_, (valid_update false hd hm x.2 y.2).1⟩, ⟨_, (valid_update false hd hm x.2 y.2).2⟩)⟩

variable {A : Type*} [DecidableEq A] [Fintype A]

/-- Forgetting validity. -/
def lift (C : Config A (VSt m d)) : Config A St := fun a => (C a).1

lemma validCfg_lift (C : Config A (VSt m d)) : ValidCfg m d (lift C) := fun a => (C a).2

lemma lift_interact (hd : 1 ≤ d) (hm : m % 2 = 1) (C : Config A (VSt m d)) (a b : A) :
    lift ((avcV hd hm).interact C a b) = (avc d).interact (lift C) a b := by
  funext x
  simp only [lift, Protocol.interact, avcV, avc]
  split_ifs <;> rfl

lemma lift_injective : Function.Injective (lift (A := A) (m := m) (d := d)) := by
  intro C D h; funext a; exact Subtype.ext (congrFun h a)

lemma step_lift_iff (hd : 1 ≤ d) (hm : m % 2 = 1) {C D : Config A (VSt m d)} :
    (avcV hd hm).Step C D ↔ (avc d).Step (lift C) (lift D) := by
  constructor
  · rintro ⟨a, b, hab, rfl⟩; exact ⟨a, b, hab, lift_interact hd hm C a b⟩
  · rintro ⟨a, b, hab, h⟩
    exact ⟨a, b, hab, lift_injective (h.trans (lift_interact hd hm C a b).symm)⟩

lemma reachable_lift (hd : 1 ≤ d) (hm : m % 2 = 1) {C D : Config A (VSt m d)}
    (h : (avcV hd hm).Reachable C D) : (avc d).Reachable (lift C) (lift D) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail ((step_lift_iff hd hm).1 hs)

/-- Reachable configurations of `avc d` from a valid configuration lift to `avcV`. -/
lemma exists_reachable_of_lift (hd : 1 ≤ d) (hm : m % 2 = 1) (C : Config A (VSt m d))
    {E : Config A St} (h : (avc d).Reachable (lift C) E) :
    ∃ D, (avcV hd hm).Reachable C D ∧ lift D = E := by
  induction h with
  | refl => exact ⟨C, .refl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨D, hD, rfl⟩ := ih
    obtain ⟨a, b, hab, rfl⟩ := hs
    exact ⟨_, hD.tail ⟨a, b, hab, rfl⟩, lift_interact hd hm D a b⟩

/-- The configurations that are "done": value sum `0`, or all signs equal to the sign of the sum. -/
def Good (C : Config A (VSt m d)) : Prop :=
  total (lift C) = 0 ∨ Converged (decide (0 < total (lift C))) (lift C)

lemma isTrap_good (hd : 1 ≤ d) (hm : m % 2 = 1) :
    IsTrap (Protocol.Step (A := A) (avcV hd hm)) {C | Good C} := by
  intro C D hC h
  have h' := (step_lift_iff hd hm).1 h
  have htot := total_step (validCfg_lift C) h'
  simp only [Set.mem_ofPred_eq, Good, htot] at hC ⊢
  rcases hC with h0 | hconv
  · exact Or.inl h0
  · exact Or.inr (converged_closed hd hm (validCfg_lift C) hconv (.single h'))

lemma reach_good (hd : 1 ≤ d) (hm : m % 2 = 1) (C : Config A (VSt m d)) :
    ∃ D ∈ {C | Good C}, Reach (avcV hd hm).Step C D := by
  by_cases h0 : total (lift C) = 0
  · exact ⟨C, Or.inl h0, .refl⟩
  obtain ⟨E, hE, hconv⟩ := exists_reachable_converged hd hm (lift C) (validCfg_lift C) h0
  obtain ⟨D, hD, rfl⟩ := exists_reachable_of_lift hd hm C hE
  refine ⟨D, Or.inr ?_, hD⟩
  rwa [total_reachable hd hm (validCfg_lift C) hE]

lemma uniformKernel_pos_iff_step (hd : 1 ≤ d) (hm : m % 2 = 1) (C D : Config A (VSt m d)) :
    0 < uniformKernel (avcV hd hm) C D ↔ (avcV hd hm).Step C D := by
  rw [uniformKernel_pos_iff, Protocol.toN_step_iff]

open Classical in
/-- **Lemma A.1 (probability-1 part).** Under the uniformly random scheduler (at least two
agents), from every valid configuration whose value sum `S` is non-zero, the probability that
not all agents have sign `sgn S` after `t` steps tends to `0`. -/
theorem lemma_A_1 (hd : 1 ≤ d) (hm : m % 2 = 1) (hA : 2 ≤ Fintype.card A)
    (C : Config A (VSt m d)) (hS : total (lift C) ≠ 0) :
    Tendsto (fun t => ∑ D ∈ {D | ¬ Converged (decide (0 < total (lift C))) (lift D)}.toFinset,
      (uniformKernel (avcV hd hm) ^ t) C D) atTop (𝓝 0) := by
  set T := uniformKernel (A := A) (avcV hd hm)
  have hT := uniformKernel_mem (A := A) (avcV hd hm) hA
  have hstep : ∀ C D, 0 < T C D → (avcV hd hm).Step C D :=
    fun C D h => (uniformKernel_pos_iff_step hd hm C D).1 h
  have hpos : ∀ C D, (avcV hd hm).Step C D → 0 < T C D :=
    fun C D h => (uniformKernel_pos_iff_step hd hm C D).2 h
  have hlim := tendsto_compl_of_reach (S := {C | Good C}) hT hstep hpos (isTrap_good hd hm)
    (reach_good hd hm) C
  refine squeeze_zero (fun t => Finset.sum_nonneg fun D _ => pow_nonneg_entry hT t C D)
    (fun t => ?_) hlim
  -- configurations with a different value sum have probability `0`
  have hzero : ∀ D, total (lift D) ≠ total (lift C) → (T ^ t) C D = 0 := by
    intro D hD
    refine pow_eq_zero_of_closed hT (fun E => total (lift E) = total (lift C))
      (fun E F hE hEF => ?_) rfl t hD
    rw [← hE]; exact total_step (validCfg_lift E) ((step_lift_iff hd hm).1 (hstep E F hEF))
  calc ∑ D ∈ {D | ¬ Converged (decide (0 < total (lift C))) (lift D)}.toFinset, (T ^ t) C D
      = ∑ D ∈ {D | ¬ Converged (decide (0 < total (lift C))) (lift D)}.toFinset.filter
          (fun D => total (lift D) = total (lift C)), (T ^ t) C D := by
        rw [Finset.sum_filter_of_ne]
        intro D _ hne; by_contra hD; exact hne (hzero D hD)
    _ ≤ ∑ D ∈ {C | Good C}.toFinsetᶜ, (T ^ t) C D := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun D hD => ?_)
          (fun D _ _ => pow_nonneg_entry hT t C D)
        rw [Finset.mem_filter, Set.mem_toFinset] at hD
        rw [Finset.mem_compl]; intro hmem
        rw [Set.mem_toFinset] at hmem
        rcases hmem with h0 | hc
        · rw [hD.2] at h0; exact hS h0
        · rw [hD.2] at hc; exact hD.1 hc

/-- **Lemma A.1, last sentence.** Once all agents have the same sign, they keep it forever. -/
theorem lemma_A_1_closed (hd : 1 ≤ d) (hm : m % 2 = 1) {C D : Config A (VSt m d)} {b : Bool}
    (hC : Converged b (lift C)) (h : (avcV hd hm).Reachable C D) : Converged b (lift D) :=
  converged_closed hd hm (validCfg_lift C) hC (reachable_lift hd hm h)

/-! ### Theorem 4.1: exact majority -/

/-- The initial state of an agent with input `A` (`true`, value `+m`) or `B` (`false`, value
`−m`). -/
def initState (m : ℕ) (b : Bool) : St := ofVal (if b then (m : ℤ) else -(m : ℤ))

lemma valid_initState (hd : 1 ≤ d) (hm : m % 2 = 1) (b : Bool) : (initState m b).Valid m d :=
  valid_ofVal hd (by cases b <;> simp <;> omega) (by cases b <;> simp)

/-- The initial configuration for the input assignment `inp` (`true` = `A`, `false` = `B`). -/
def initCfg (hd : 1 ≤ d) (hm : m % 2 = 1) (inp : A → Bool) : Config A (VSt m d) :=
  fun a => ⟨initState m (inp a), valid_initState hd hm (inp a)⟩

/-- Number of agents with input `b`. -/
def numInput (inp : A → Bool) (b : Bool) : ℕ := (Finset.univ.filter fun a => inp a = b).card

lemma total_initCfg (hd : 1 ≤ d) (hm : m % 2 = 1) (inp : A → Bool) :
    total (lift (initCfg hd hm inp)) = m * ((numInput inp true : ℤ) - numInput inp false) := by
  simp only [total, lift, initCfg, initState, value_ofVal, numInput]
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases inp a <;> simp

/-- **Theorem 4.1 (first part): "The AVC algorithm solves majority with probability 1."**
For odd `m`, `d ≥ 1`, at least two agents and an input with a strict majority, under the
uniformly random scheduler the probability that some agent does not output the majority value
(output `γ = sgn`) after `t` steps tends to `0`. -/
theorem theorem_4_1_correct (hd : 1 ≤ d) (hm : m % 2 = 1) (hA : 2 ≤ Fintype.card A)
    (inp : A → Bool) (hmaj : numInput inp true ≠ numInput inp false) :
    Tendsto (fun t => ∑ D ∈ {D | ¬ ∀ a, (lift D a).sgn =
        decide (numInput inp false < numInput inp true)}.toFinset,
      (uniformKernel (avcV hd hm) ^ t) (initCfg hd hm inp) D) atTop (𝓝 0) := by
  have htot := total_initCfg hd hm inp
  have hm0 : (0 : ℤ) < m := by omega
  have hS : total (lift (initCfg hd hm inp)) ≠ 0 := by
    rw [htot]; exact mul_ne_zero hm0.ne' (sub_ne_zero.2 (by exact_mod_cast hmaj))
  have key := lemma_A_1 hd hm hA (initCfg hd hm inp) hS
  have hdec : decide (0 < total (lift (initCfg hd hm inp))) =
      decide (numInput inp false < numInput inp true) := by
    rw [htot]; simp only [decide_eq_decide]
    constructor
    · intro h; have := pos_of_mul_pos_right h hm0.le; omega
    · intro h; exact mul_pos hm0 (by omega)
  simpa [Converged, hdec] using key

end Podc.ExactMajorityAVC
