import Papers.PODC2015.ExactMajorityAVC.AVC

/-!
# Correctness of AVC: Invariant 4.3 and Lemma A.1 (reachability part)

Configurations are CSLib's labelled configurations `A → St` (`Cslib.PopulationProtocol`), the
protocol is `avc d` (Figure 1 with the corrected line 12).

* `total_step`, `total_reachable`: **Invariant 4.3** — the sum of values never changes;
* `reachable_neg`: the sign symmetry of the protocol on configurations;
* `exists_reachable_converged`: from every valid configuration whose value sum `S` is non-zero, a
  configuration in which every agent has sign `sgn S` is reachable (the three phases of the
  proof of Lemma A.1);
* `converged_closed`: such configurations are closed (no agent ever changes its sign again).

The probabilistic statements are in `AVCProb.lean`.
-/

namespace Podc.ExactMajorityAVC

open Cslib.PopulationProtocol St

set_option linter.unusedSectionVars false

variable {A : Type*} [DecidableEq A] [Fintype A] {m d : ℕ}

lemma avc_δ (x y : St) : (avc d).δ x y = update false d x y := rfl

/-- The sum of the values of all agents. -/
def total (C : Config A St) : ℤ := ∑ a, (C a).value

/-- All agents are in valid states. -/
def ValidCfg (m d : ℕ) (C : Config A St) : Prop := ∀ a, (C a).Valid m d

/-- All agents have sign `b`. -/
def Converged (b : Bool) (C : Config A St) : Prop := ∀ a, (C a).sgn = b

/-- The configuration with all signs negated. -/
def negCfg (C : Config A St) : Config A St := fun a => (C a).neg

/-! ### Sums over an interaction -/

-- CSLib candidate (`PopulationProtocols/Basic.lean`)
/-- Additive functionals change only at the two interacting agents. -/
lemma sum_interact {Q : Type*} (P : Protocol Q) (f : Q → ℤ) (C : Config A Q) {a b : A}
    (hab : a ≠ b) :
    ∑ x, f (P.interact C a b x) =
      ∑ x, f (C x) - f (C a) - f (C b) + f (P.δ (C a) (C b)).1 + f (P.δ (C a) (C b)).2 := by
  have ha : a ∈ (Finset.univ : Finset A) := Finset.mem_univ a
  have hb : b ∈ (Finset.univ : Finset A).erase a := Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩
  have key : ∀ g : A → ℤ, ∑ x, g x = g a + g b + ∑ x ∈ ((Finset.univ : Finset A).erase a).erase b, g x :=
    fun g => by rw [add_assoc, Finset.add_sum_erase _ _ hb, Finset.add_sum_erase _ _ ha]
  rw [key, key (fun x => f (C x))]
  have hrest : ∑ x ∈ ((Finset.univ : Finset A).erase a).erase b, f (P.interact C a b x) =
      ∑ x ∈ ((Finset.univ : Finset A).erase a).erase b, f (C x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_erase] at hx
    rw [P.interact_other C hx.2.1 hx.1]
  rw [hrest, P.interact_self_left, P.interact_self_right C hab]
  ring

lemma interact_valid (hd : 1 ≤ d) (hm : m % 2 = 1) {C : Config A St} (hC : ValidCfg m d C)
    (a b x : A) : ((avc d).interact C a b x).Valid m d := by
  unfold Protocol.interact
  split_ifs
  · exact (valid_update false hd hm (hC a) (hC b)).1
  · exact (valid_update false hd hm (hC a) (hC b)).2
  · exact hC x

lemma step_valid (hd : 1 ≤ d) (hm : m % 2 = 1) {C D : Config A St} (hC : ValidCfg m d C)
    (h : (avc d).Step C D) : ValidCfg m d D := by
  obtain ⟨a, b, -, rfl⟩ := h
  exact interact_valid hd hm hC a b

lemma reachable_valid (hd : 1 ≤ d) (hm : m % 2 = 1) {C D : Config A St} (hC : ValidCfg m d C)
    (h : (avc d).Reachable C D) : ValidCfg m d D := by
  induction h with
  | refl => exact hC
  | tail _ hs ih => exact step_valid hd hm ih hs

/-- **Invariant 4.3**, one step. -/
theorem total_step {C D : Config A St} (hC : ValidCfg m d C) (h : (avc d).Step C D) :
    total D = total C := by
  obtain ⟨a, b, hab, rfl⟩ := h
  unfold total
  rw [sum_interact _ _ _ hab]
  have := value_update false (hC a) (hC b)
  simp only [avc] at this ⊢
  linarith

/-- **Invariant 4.3.** The sum `∑_v value(c(v))` never changes along reachable configurations. -/
theorem total_reachable (hd : 1 ≤ d) (hm : m % 2 = 1) {C D : Config A St} (hC : ValidCfg m d C)
    (h : (avc d).Reachable C D) : total D = total C := by
  induction h with
  | refl => rfl
  | tail hr hs ih => rw [total_step (reachable_valid hd hm hC hr) hs, ih]

/-! ### Sign symmetry on configurations -/

lemma negCfg_negCfg (C : Config A St) : negCfg (negCfg C) = C := by
  funext a; simp [negCfg]

lemma total_negCfg (C : Config A St) : total (negCfg C) = -total C := by
  simp [total, negCfg, Finset.sum_neg_distrib]

lemma validCfg_neg {C : Config A St} (hC : ValidCfg m d C) : ValidCfg m d (negCfg C) :=
  fun a => valid_neg (hC a)

lemma step_neg {C D : Config A St} (hC : ValidCfg m d C) (h : (avc d).Step C D) :
    (avc d).Step (negCfg C) (negCfg D) := by
  obtain ⟨a, b, hab, rfl⟩ := h
  refine ⟨b, a, hab.symm, ?_⟩
  funext x
  have key := update_neg (d := d) (hC a) (hC b)
  simp only [negCfg, Protocol.interact, avc] at key ⊢
  by_cases hxa : x = a
  · subst hxa; simp [hab, key]
  · by_cases hxb : x = b
    · subst hxb; simp [key, hxa]
    · simp [hxa, hxb]

lemma reachable_neg (hd : 1 ≤ d) (hm : m % 2 = 1) {C D : Config A St} (hC : ValidCfg m d C)
    (h : (avc d).Reachable C D) : (avc d).Reachable (negCfg C) (negCfg D) := by
  induction h with
  | refl => exact .refl
  | tail hr hs ih => exact ih.tail (step_neg (reachable_valid hd hm hC hr) hs)

lemma converged_negCfg {C : Config A St} (hC : ValidCfg m d C) {b : Bool} :
    Converged b (negCfg C) ↔ Converged (!b) C := by
  unfold Converged negCfg
  refine forall_congr' fun a => ?_
  rw [sgn_neg (hC a)]
  cases b <;> simp

/-! ### Closure of converged configurations -/

lemma step_converged_true {C D : Config A St} (hC : ValidCfg m d C) (hconv : Converged true C)
    (h : (avc d).Step C D) : Converged true D := by
  obtain ⟨a, b, hab, rfl⟩ := h
  intro x
  have := sgn_update_of_pos (d := d) (hC a) (hC b) (hconv a) (hconv b)
  unfold Protocol.interact
  split_ifs
  · exact this.1
  · exact this.2
  · exact hconv x

/-- Configurations in which all agents have the same sign are closed: no agent can ever change its
sign again (last sentence of Lemma A.1). -/
theorem converged_closed (hd : 1 ≤ d) (hm : m % 2 = 1) {C D : Config A St} (hC : ValidCfg m d C)
    {b : Bool} (hconv : Converged b C) (h : (avc d).Reachable C D) : Converged b D := by
  cases b
  · have h' := reachable_neg hd hm hC h
    have hc' : Converged true (negCfg C) := (converged_negCfg hC).2 hconv
    have key : ∀ E, (avc d).Reachable (negCfg C) E → Converged true E := by
      intro E hE
      induction hE with
      | refl => exact hc'
      | tail hr hs ih =>
        exact step_converged_true (reachable_valid hd hm (validCfg_neg hC) hr) ih hs
    exact (converged_negCfg (reachable_valid hd hm hC h)).1 (key _ h')
  · induction h with
    | refl => exact hconv
    | tail hr hs ih => exact step_converged_true (reachable_valid hd hm hC hr) ih hs

/-! ### Reachability of a converged configuration (Lemma A.1) -/

-- CSLib candidate (`SelfStabilization/TransitionSystem.lean`)
/-- Generic termination argument: if every non-goal configuration satisfying an invariant can
reach a configuration satisfying the invariant with a smaller measure, a goal configuration is
reachable. -/
lemma reach_of_measure {X : Type*} {R : X → X → Prop} (Inv Goal : X → Prop) (μ : X → ℕ)
    (h : ∀ x, Inv x → ¬ Goal x → ∃ y, Relation.ReflTransGen R x y ∧ Inv y ∧ μ y < μ x) :
    ∀ x, Inv x → ∃ y, Relation.ReflTransGen R x y ∧ Inv y ∧ Goal y := by
  intro x
  induction hμ : μ x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro hx
    by_cases hg : Goal x
    · exact ⟨x, .refl, hx, hg⟩
    · obtain ⟨y, hxy, hy, hlt⟩ := h x hx hg
      obtain ⟨z, hyz, hz, hgz⟩ := ih _ (hμ ▸ hlt) y rfl hy
      exact ⟨z, hxy.trans hyz, hz, hgz⟩

lemma reachable_interact (P : Protocol St) (C : Config A St) {a b : A} (hab : a ≠ b) :
    P.Reachable C (P.interact C a b) :=
  Relation.ReflTransGen.single ⟨a, b, hab, rfl⟩

lemma exists_pos_of_total_pos {C : Config A St} (h : 0 < total C) : ∃ v, 0 < (C v).value := by
  by_contra hne
  push Not at hne
  have : total C ≤ 0 := Finset.sum_nonpos fun a _ => hne a
  omega

lemma eq_zero_false {x : St} (hx : x.Valid m d) (h0 : 0 ≤ x.value) (hs : x.sgn = false) :
    x = zero false := by
  rcases x with ⟨_ | _⟩ | ⟨_ | _, j⟩ | v <;> simp_all
  rw [valid_strong_iff] at hx; omega

lemma eq_one_false {x : St} (hx : x.Valid m d) (hw : x.weight ≤ 1) (hv : x.value < 0) :
    ∃ i, x = one false i ∧ i ≤ d := by
  rcases x with ⟨_ | _⟩ | ⟨_ | _, j⟩ | v <;> simp_all [Valid]
  simp only [abs_eq_max_neg] at hx; omega

lemma eq_one_true {x : St} (hx : x.Valid m d) (hw : x.weight ≤ 1) (hv : 0 < x.value) :
    ∃ i, x = one true i ∧ i ≤ d := by
  rcases x with ⟨_ | _⟩ | ⟨_ | _, j⟩ | v <;> simp_all [Valid]
  simp only [abs_eq_max_neg] at hx; omega

/-- Phase 3 of Lemma A.1: if no value is negative and some value is positive, the weak states of
negative sign can all be turned positive. -/
lemma phase3 (hd : 1 ≤ d) (hm : m % 2 = 1) (C : Config A St) (hC : ValidCfg m d C)
    (h0 : ∀ a, 0 ≤ (C a).value) (hpos : ∃ v, 0 < (C v).value) :
    ∃ D, (avc d).Reachable C D ∧ Converged true D := by
  obtain ⟨D, hD, -, hg⟩ := reach_of_measure (R := (avc d).Step)
    (fun C => ValidCfg m d C ∧ (∀ a, 0 ≤ (C a).value) ∧ ∃ v, 0 < (C v).value)
    (Converged true) (fun C => (Finset.univ.filter fun a => (C a).sgn = false).card)
    (fun C ⟨hC, h0, v, hv⟩ hg => by
      simp only [Converged, not_forall, Bool.not_eq_true] at hg
      obtain ⟨a, ha⟩ := hg
      have hCa := eq_zero_false (hC a) (h0 a) ha
      have hav : a ≠ v := by rintro rfl; rw [hCa] at hv; simp at hv
      have hδ : (avc d).δ (C a) (C v) = (zero true, shift d (C v)) := by
        rw [hCa]; exact update_zero_pos hv
      refine ⟨(avc d).interact C a v, reachable_interact _ _ hav, ⟨interact_valid hd hm hC a v,
        fun x => ?_, v, ?_⟩, ?_⟩
      · unfold Protocol.interact; rw [hδ]; split_ifs
        · simp
        · simpa using hv.le
        · exact h0 x
      · rw [(avc d).interact_self_right C hav, hδ]; simpa using hv
      · apply Finset.card_lt_card
        refine Finset.ssubset_iff_of_subset (fun x hx => ?_) |>.2 ⟨a, by simp [ha], ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          unfold Protocol.interact at hx; rw [hδ] at hx
          split_ifs at hx with h1 h2
          · simp at hx
          · subst h2
            have : (C x).sgn = true := by
              rcases hcx : C x with ⟨_ | _⟩ | ⟨_ | _, j⟩ | w <;> rw [hcx] at hv <;> simp_all
            simp_all
          · exact hx
        · simp [Protocol.interact, hδ]) C ⟨hC, h0, hpos⟩
  exact ⟨D, hD, hg⟩

/-- Two intermediate states of opposite signs interacting repeatedly both become weak. -/
lemma pair_reach {u v : A} (huv : u ≠ v) (k : ℕ) :
    ∀ (C : Config A St) (i j : ℕ), d - i = k → i ≤ d → j ≤ d → C u = one false i →
      C v = one true j → ∃ D, (avc d).Reachable C D ∧ D u = zero false ∧ D v = zero true ∧
        ∀ x, x ≠ u → x ≠ v → D x = C x := by
  induction k with
  | zero =>
    intro C i j hk hi hj hu hv
    have hid : i = d := by omega
    refine ⟨(avc d).interact C u v, reachable_interact _ _ huv, ?_⟩
    have hδ : (avc d).δ (C u) (C v) = (zero false, zero true) := by
      rw [hu, hv]; rw [avc_δ]; rw [update_one_one hi hj]; simp [hid]
    refine ⟨by simp [hδ], by rw [(avc d).interact_self_right C huv, hδ], fun x hxu hxv => ?_⟩
    exact (avc d).interact_other C hxu hxv
  | succ k ih =>
    intro C i j hk hi hj hu hv
    by_cases hij : i = d ∨ j = d
    · refine ⟨(avc d).interact C u v, reachable_interact _ _ huv, ?_⟩
      have hδ : (avc d).δ (C u) (C v) = (zero false, zero true) := by
        rw [hu, hv]; rw [avc_δ]; rw [update_one_one hi hj]; simp [hij]
      refine ⟨by simp [hδ], by rw [(avc d).interact_self_right C huv, hδ], fun x hxu hxv => ?_⟩
      exact (avc d).interact_other C hxu hxv
    · push Not at hij
      have hδ : (avc d).δ (C u) (C v) = (one false (i + 1), one true (j + 1)) := by
        rw [hu, hv]; rw [avc_δ]; rw [update_one_one hi hj]
        simp [hij.1, hij.2]
      obtain ⟨D, hD, hDu, hDv, hDo⟩ := ih ((avc d).interact C u v) (i + 1) (j + 1) (by omega)
        (by omega) (by omega) (by simp [hδ]) (by rw [(avc d).interact_self_right C huv, hδ])
      refine ⟨D, (reachable_interact _ _ huv).trans hD, hDu, hDv, fun x hxu hxv => ?_⟩
      rw [hDo x hxu hxv, (avc d).interact_other C hxu hxv]

/-- Phase 2 of Lemma A.1: if all weights are at most `1` and the sum is positive, a configuration
without negative values is reachable. -/
lemma phase2 (hd : 1 ≤ d) (hm : m % 2 = 1) (C : Config A St) (hC : ValidCfg m d C)
    (hw : ∀ a, (C a).weight ≤ 1) (hS : 0 < total C) :
    ∃ D, (avc d).Reachable C D ∧ ValidCfg m d D ∧ 0 < total D ∧ ∀ a, 0 ≤ (D a).value := by
  obtain ⟨D, hD, ⟨hDv, -, hDS⟩, hg⟩ := reach_of_measure (R := (avc d).Step)
    (fun C => ValidCfg m d C ∧ (∀ a, (C a).weight ≤ 1) ∧ 0 < total C)
    (fun C => ∀ a, 0 ≤ (C a).value) (fun C => (Finset.univ.filter fun a => (C a).value < 0).card)
    (fun C ⟨hC, hw, hS⟩ hg => by
      push Not at hg
      obtain ⟨u, hu⟩ := hg
      obtain ⟨v, hv⟩ := exists_pos_of_total_pos hS
      obtain ⟨i, hCu, hi⟩ := eq_one_false (hC u) (hw u) hu
      obtain ⟨j, hCv, hj⟩ := eq_one_true (hC v) (hw v) hv
      have huv : u ≠ v := by rintro rfl; omega
      obtain ⟨D, hD, hDu, hDv, hDo⟩ := pair_reach huv _ C i j rfl hi hj hCu hCv
      refine ⟨D, hD, ⟨reachable_valid hd hm hC hD, fun x => ?_,
        (total_reachable hd hm hC hD).symm ▸ hS⟩, ?_⟩
      · by_cases hxu : x = u
        · subst hxu; simp [hDu]
        · by_cases hxv : x = v
          · subst hxv; simp [hDv]
          · rw [hDo x hxu hxv]; exact hw x
      · apply Finset.card_lt_card
        refine Finset.ssubset_iff_of_subset (fun x hx => ?_) |>.2 ⟨u, by simp [hu], by simp [hDu]⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        by_cases hxu : x = u
        · subst hxu; simp [hDu] at hx
        · by_cases hxv : x = v
          · subst hxv; simp [hDv] at hx
          · rwa [hDo x hxu hxv] at hx) C ⟨hC, hw, hS⟩
  exact ⟨D, hD, hDv, hDS, hg⟩

/-- Phase 1 of Lemma A.1: as long as there is a strong state and a negative value, a strong state
can meet a state of opposite sign, which decreases the total negative weight. -/
lemma phase1 (hd : 1 ≤ d) (hm : m % 2 = 1) (C : Config A St) (hC : ValidCfg m d C)
    (hS : 0 < total C) :
    ∃ D, (avc d).Reachable C D ∧ ValidCfg m d D ∧ 0 < total D ∧
      ((∀ a, 0 ≤ (D a).value) ∨ ∀ a, (D a).weight ≤ 1) := by
  obtain ⟨D, hD, ⟨hDv, hDS⟩, hg⟩ := reach_of_measure (R := (avc d).Step)
    (fun C => ValidCfg m d C ∧ 0 < total C)
    (fun C => (∀ a, 0 ≤ (C a).value) ∨ ∀ a, (C a).weight ≤ 1)
    (fun C => (∑ a, negPart (C a)).toNat)
    (fun C ⟨hC, hS⟩ hg => by
      push Not at hg
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hg
      have hnn : 0 ≤ ∑ x, negPart (C x) :=
        Finset.sum_nonneg fun x _ => le_max_left _ _
      -- the interacting pair: a positive initiator `p` and a negative responder `q`, one strong
      obtain ⟨p, q, hpq, hp, hq, hs⟩ : ∃ p q, p ≠ q ∧ 0 < (C p).value ∧ (C q).value < 0 ∧
          (1 < (C p).weight ∨ 1 < (C q).weight) := by
        have hwb := weight_eq_abs_value (C b)
        rcases lt_or_gt_of_ne (show (C b).value ≠ 0 by
          intro h0; rw [h0] at hwb; simp at hwb; omega) with hbn | hbp
        · obtain ⟨p, hp⟩ := exists_pos_of_total_pos hS
          exact ⟨p, b, by rintro rfl; omega, hp, hbn, Or.inr hb⟩
        · exact ⟨b, a, by rintro rfl; omega, hbp, ha, Or.inl hb⟩
      refine ⟨(avc d).interact C p q, reachable_interact _ _ hpq,
        ⟨interact_valid hd hm hC p q, (total_step hC ⟨p, q, hpq, rfl⟩).symm ▸ hS⟩, ?_⟩
      have hlt := negPart_update_lt (hC p) (hC q) hp hq hs
      have hsum := sum_interact (avc d) negPart C hpq
      simp only [avc] at hsum hlt ⊢
      have : 0 ≤ ∑ x, negPart ((avc d).interact C p q x) :=
        Finset.sum_nonneg fun x _ => le_max_left _ _
      simp only [avc] at this
      omega) C ⟨hC, hS⟩
  exact ⟨D, hD, hDv, hDS, hg⟩

/-- **Lemma A.1 (reachability part).** From every valid configuration whose sum of values `S` is
non-zero, a configuration in which every agent has sign `sgn S` is reachable. -/
theorem exists_reachable_converged (hd : 1 ≤ d) (hm : m % 2 = 1) (C : Config A St)
    (hC : ValidCfg m d C) (hS : total C ≠ 0) :
    ∃ D, (avc d).Reachable C D ∧ Converged (decide (0 < total C)) D := by
  have pos : ∀ C : Config A St, ValidCfg m d C → 0 < total C →
      ∃ D, (avc d).Reachable C D ∧ Converged true D := by
    intro C hC hS
    obtain ⟨D, hD, hDv, hDS, hg⟩ := phase1 hd hm C hC hS
    rcases hg with h0 | hw
    · obtain ⟨E, hE, hconv⟩ := phase3 hd hm D hDv h0 (exists_pos_of_total_pos hDS)
      exact ⟨E, hD.trans hE, hconv⟩
    · obtain ⟨E, hE, hEv, hES, h0⟩ := phase2 hd hm D hDv hw hDS
      obtain ⟨F, hF, hconv⟩ := phase3 hd hm E hEv h0 (exists_pos_of_total_pos hES)
      exact ⟨F, hD.trans (hE.trans hF), hconv⟩
  rcases lt_or_gt_of_ne hS with hneg | hpos
  · obtain ⟨D, hD, hconv⟩ := pos (negCfg C) (validCfg_neg hC) (by rw [total_negCfg]; omega)
    have hD' := reachable_neg hd hm (validCfg_neg hC) hD
    rw [negCfg_negCfg] at hD'
    refine ⟨negCfg D, hD', ?_⟩
    have := (converged_negCfg (b := false)
      (reachable_valid hd hm (validCfg_neg hC) hD)).2 hconv
    simpa [hneg.not_gt] using this
  · simpa [hpos] using pos C hC hpos

end Podc.ExactMajorityAVC
