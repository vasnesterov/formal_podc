import Papers.PODC2023.AmortizedByzantineBroadcast.DishonestMajorityModel

/-!
# Section 5 of [WXMRS23]: basic facts about executions of Algorithm 5.2

Reading-independent lemmas: monotonicity of knowledge and trust graphs, synchronous delivery,
slot arithmetic, and the origin lemma for honestly signed atoms (unforgeability).
-/

namespace Podc.AmortizedByzantineBroadcast.DishonestMajority

open SimpleGraph

variable {N V : Type*} [Fintype N] (P : Setup N V) {H : Set N} {adv : ℕ → N → Set (Msg N V)}

namespace Setup

/-! ### Slot arithmetic -/

lemma T_pos : 0 < P.T := by unfold T; omega

lemma loc_lt (r : ℕ) : P.loc r < P.T := Nat.mod_lt _ P.T_pos

lemma slot_mul_add (r : ℕ) : P.slot r * P.T + P.loc r = r := by
  unfold slot loc; rw [mul_comm]; exact Nat.div_add_mod r P.T

lemma slot_of_eq {k t : ℕ} (ht : t < P.T) : P.slot (k * P.T + t) = k := by
  unfold slot
  rw [add_comm, Nat.add_mul_div_right _ _ P.T_pos, Nat.div_eq_of_lt ht, zero_add]

lemma loc_of_eq {k t : ℕ} (ht : t < P.T) : P.loc (k * P.T + t) = t := by
  unfold loc; rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

lemma slot_mul (k : ℕ) : P.slot (k * P.T) = k := by
  simpa using P.slot_of_eq (k := k) (t := 0) P.T_pos

lemma loc_mul (k : ℕ) : P.loc (k * P.T) = 0 := by
  simpa using P.loc_of_eq (k := k) (t := 0) P.T_pos

/-- The previous round of a round with `loc r ≥ 1` is in the same slot. -/
lemma slot_pred {r : ℕ} (h : 1 ≤ P.loc r) : P.slot (r - 1) = P.slot r := by
  have h1 := P.slot_mul_add r
  have h2 := P.loc_lt r
  have : r - 1 = P.slot r * P.T + (P.loc r - 1) := by omega
  rw [this, P.slot_of_eq (by omega)]

lemma loc_pred {r : ℕ} (h : 1 ≤ P.loc r) : P.loc (r - 1) = P.loc r - 1 := by
  have h1 := P.slot_mul_add r
  have h2 := P.loc_lt r
  have : r - 1 = P.slot r * P.T + (P.loc r - 1) := by omega
  rw [this, P.loc_of_eq (by omega)]

/-- Moving forward inside a slot. -/
lemma slot_add {r d : ℕ} (h : P.loc r + d < P.T) : P.slot (r + d) = P.slot r := by
  have h1 := P.slot_mul_add r
  have : r + d = P.slot r * P.T + (P.loc r + d) := by omega
  rw [this, P.slot_of_eq h]

lemma loc_add {r d : ℕ} (h : P.loc r + d < P.T) : P.loc (r + d) = P.loc r + d := by
  have h1 := P.slot_mul_add r
  have : r + d = P.slot r * P.T + (P.loc r + d) := by omega
  rw [this, P.loc_of_eq h]

/-! ### Unfolding the execution -/

lemma cfg_zero (u : N) : P.cfg H adv 0 u = State.init := rfl

lemma know_succ (r : ℕ) (u : N) : (P.cfg H adv (r + 1) u).know =
    (P.cfg H adv r u).know ∪ (adv r u ∪ {a | ∃ w ∈ H, a ∈ (P.cfg H adv r w).out}) := rfl

lemma G_succ (r : ℕ) (u : N) : (P.cfg H adv (r + 1) u).G =
    P.G2 u r (P.cfg H adv r u).G (P.cfg H adv (r + 1) u).know := rfl

lemma out_succ (r : ℕ) (u : N) : (P.cfg H adv (r + 1) u).out =
    P.outSet u r (P.cfg H adv r u).G (P.cfg H adv (r + 1) u).know := rfl

/-- The graph of `u` after processing the accusations of round `r` (before removing equivocators);
the distances for accusing by distance are measured in it. -/
def Gacc (H : Set N) (adv : ℕ → N → Set (Msg N V)) (u : N) (r : ℕ) : SimpleGraph N :=
  P.G1 u r (P.cfg H adv r u).G (P.cfg H adv (r + 1) u).know

lemma Gacc_le (u : N) (r : ℕ) : P.Gacc H adv u r ≤ (P.cfg H adv r u).G :=
  deleteEdges_le _

lemma G_succ_le_Gacc (u : N) (r : ℕ) : (P.cfg H adv (r + 1) u).G ≤ P.Gacc H adv u r :=
  deleteEdges_le _

lemma G_succ_le (u : N) (r : ℕ) : (P.cfg H adv (r + 1) u).G ≤ (P.cfg H adv r u).G :=
  (P.G_succ_le_Gacc u r).trans (P.Gacc_le u r)

lemma G_anti (u : N) {r r' : ℕ} (h : r ≤ r') : (P.cfg H adv r' u).G ≤ (P.cfg H adv r u).G := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (P.G_succ_le u _).trans ih

lemma know_succ_sub (u : N) (r : ℕ) : (P.cfg H adv r u).know ⊆ (P.cfg H adv (r + 1) u).know :=
  Set.subset_union_left

lemma know_mono (u : N) {r r' : ℕ} (h : r ≤ r') :
    (P.cfg H adv r u).know ⊆ (P.cfg H adv r' u).know := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (P.know_succ_sub u _)

/-- Synchrony: what an honest node multicasts in round `r` is known to everybody after round
`r + 1`. -/
lemma deliver {w : N} (hw : w ∈ H) (u : N) {r : ℕ} {a : Msg N V}
    (ha : a ∈ (P.cfg H adv (r + 1) w).out) : a ∈ (P.cfg H adv (r + 2) u).know :=
  Or.inr (Or.inr ⟨w, hw, ha⟩)

lemma deliver_le {w : N} (hw : w ∈ H) (u : N) {r r' : ℕ} (hr : r + 2 ≤ r') {a : Msg N V}
    (ha : a ∈ (P.cfg H adv (r + 1) w).out) : a ∈ (P.cfg H adv r' u).know :=
  P.know_mono u hr (P.deliver hw u ha)

/-- Everything an honest node multicasts is either known to it or signed by it, and in the latter
case it is created by one of the three "creating" rules. -/
lemma out_cases {u : N} {r : ℕ} {G : SimpleGraph N} {K : Set (Msg N V)} {a : Msg N V}
    (ha : a ∈ P.outSet u r G K) :
    a ∈ K ∨
    (a = .prop (P.input (P.slot r)) (P.slot r) ∧ P.loc r = 0 ∧ u = P.S (P.slot r)) ∨
    (∃ x, a = .accuse x u ∧ 1 ≤ P.loc r ∧ P.loc r ≤ P.n ∧ ¬ HasProp K (P.slot r) ∧
      (P.G1 u r G K).Reachable u x ∧ (P.G1 u r G K).edist x (P.S (P.slot r)) < P.loc r) ∨
    (a = .corrupt (P.S (P.slot r)) u ∧ P.DsVote u r G K) := by
  rcases ha with ⟨x, y, rfl, h⟩ | ⟨m, j, rfl, h, -⟩ | h | ⟨m, rfl, h, -⟩ | h | h | ⟨w, rfl, h, -⟩
  · exact Or.inl h.2.1
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inl h

lemma out_known_or_signed {u : N} {r : ℕ} {G : SimpleGraph N} {K : Set (Msg N V)} {a : Msg N V}
    (ha : a ∈ P.outSet u r G K) : a ∈ K ∨ a.signer P.S = u := by
  rcases P.out_cases ha with h | ⟨rfl, -, rfl⟩ | ⟨x, rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl h
  all_goals exact Or.inr rfl

/-- The sender of slot `k` multicasts its proposal in round `0` of the slot. -/
lemma sender_out (k : ℕ) :
    Msg.prop (P.input k) k ∈ (P.cfg H adv (k * P.T + 1) (P.S k)).out := by
  rw [out_succ]
  exact Or.inr (Or.inr (Or.inl ⟨by rw [P.slot_mul], P.loc_mul k, by rw [P.slot_mul]⟩))

/-- Origin lemma (unforgeability): an atom signed by an honest node and known to an honest node
after round `r - 1` was multicast by its signer in some round `r' ≤ r - 2`. -/
lemma origin (hadv : P.AdvValid H adv) :
    ∀ r, ∀ v ∈ H, ∀ a ∈ (P.cfg H adv r v).know, a.signer P.S ∈ H →
      ∃ r', r' + 1 < r ∧ a ∈ (P.cfg H adv (r' + 1) (a.signer P.S)).out := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro v hv a ha hs
    have hout : ∀ r0, r0 + 1 < r → ∀ w ∈ H, a ∈ (P.cfg H adv (r0 + 1) w).out →
        ∃ r', r' + 1 < r ∧ a ∈ (P.cfg H adv (r' + 1) (a.signer P.S)).out := by
      intro r0 hr0 w hw haw
      rcases P.out_known_or_signed haw with hk | hsw
      · obtain ⟨r', h1, h2⟩ := ih (r0 + 1) hr0 w hw a hk hs
        exact ⟨r', by omega, h2⟩
      · exact ⟨r0, hr0, hsw ▸ haw⟩
    cases r with
    | zero => exact absurd ha (by simp [cfg_zero, State.init])
    | succ s =>
      rcases ha with ha | ha | ⟨w, hw, ha⟩
      · obtain ⟨r', h1, h2⟩ := ih s (by omega) v hv a ha hs
        exact ⟨r', by omega, h2⟩
      · obtain ⟨r0, hr0, w0, hw0, h0⟩ := hadv s v a hv ha hs
        exact hout r0 (by omega) w0 hw0 h0
      · cases s with
        | zero => exact absurd ha (by simp [cfg_zero, State.init])
        | succ r0 => exact hout r0 (by omega) w hw ha

end Setup

end Podc.AmortizedByzantineBroadcast.DishonestMajority
