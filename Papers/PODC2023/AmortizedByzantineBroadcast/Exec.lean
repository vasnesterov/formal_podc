import Papers.PODC2023.AmortizedByzantineBroadcast.Model

/-!
# Basic facts about runs of the Algorithm 4 model

* `exec_succ`: the state recursion in functional form;
* `mem_rcv_exec`, `mem_sent_exec`: what is in a node's state;
* `held_exec_of_le`, `mem_heldAt`: the items held at a round;
* timing: `roundOf_slotOf`, `slotOf_roundOf`, … .
-/

namespace Podc.AmortizedByzantineBroadcast

variable {n : ℕ} {V : Type} [DecidableEq V] [NeZero n] (P : Params n V) (pol : Skip)
  (sc : Scenario n V)

lemma exec_zero (u : Fin n) : exec P pol sc 0 u = ⟨[], []⟩ := by
  simp [exec, cfg, List.getD_eq_getElem?_getD]

lemma exec_succ (r : ℕ) (w : Fin n) :
    exec P pol sc (r + 1) w =
      ⟨(exec P pol sc r w).rcv ++ deliver (outs P pol sc r (exec P pol sc r)) r w,
       (exec P pol sc r w).sent ++
        ((outs P pol sc r (exec P pol sc r) w).map fun e => (r, e.1, e.2))⟩ := by
  have hE : exec P pol sc r = fun u : Fin n => (cfg P pol sc r)[(u : ℕ)]?.getD ⟨[], []⟩ := by
    funext u; simp [exec, List.getD_eq_getElem?_getD]
  rw [hE]
  simp only [exec, cfg, cfgStep]
  simp [List.getD_eq_getElem?_getD]

lemma mem_deliver (os : Fin n → List (Fin n × Item n V)) (r : ℕ) (w : Fin n) (t : ℕ) (s : Fin n)
    (x : Item n V) : (t, s, x) ∈ deliver os r w ↔ t = r ∧ (w, x) ∈ os s := by
  simp only [deliver, List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨u, ⟨a, b⟩, hab, h1, rfl, rfl, rfl⟩
    exact ⟨rfl, by subst h1; exact hab⟩
  · rintro ⟨rfl, h⟩
    exact ⟨s, (w, x), h, rfl, rfl, rfl, rfl⟩

lemma mem_rcv_exec (r : ℕ) (w : Fin n) (t : ℕ) (s : Fin n) (x : Item n V) :
    (t, s, x) ∈ (exec P pol sc r w).rcv ↔ t < r ∧ (w, x) ∈ outs P pol sc t (exec P pol sc t) s := by
  induction r with
  | zero => simp [exec_zero]
  | succ r ih =>
    rw [exec_succ]
    simp only [List.mem_append, ih, mem_deliver]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨rfl, h2⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | rfl
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨rfl, h2⟩

lemma mem_sent_exec (r : ℕ) (u : Fin n) (t : ℕ) (w : Fin n) (x : Item n V) :
    (t, w, x) ∈ (exec P pol sc r u).sent ↔ t < r ∧ (w, x) ∈ outs P pol sc t (exec P pol sc t) u := by
  induction r with
  | zero => simp [exec_zero]
  | succ r ih =>
    rw [exec_succ]
    simp only [List.mem_append, ih, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨⟨a, b⟩, hab, rfl, rfl, rfl⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨by omega, hab⟩
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | rfl
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨(w, x), h2, rfl, rfl, rfl⟩

lemma mem_held (st : St n V) (t : ℕ) (x : Item n V) :
    x ∈ held st t ↔ ∃ t' s, t' < t ∧ (t', s, x) ∈ st.rcv := by
  simp only [held, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a, b, c⟩, ⟨h1, h2⟩, rfl⟩
    exact ⟨a, b, h2, h1⟩
  · rintro ⟨a, b, h2, h1⟩
    exact ⟨⟨a, b, x⟩, ⟨h1, h2⟩, rfl⟩

lemma mem_heldIn (st : St n V) (a b : ℕ) (x : Item n V) :
    x ∈ heldIn st a b ↔ ∃ t' s, a ≤ t' ∧ t' < b ∧ (t', s, x) ∈ st.rcv := by
  simp only [heldIn, List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨c, d, e⟩, ⟨h1, h2, h3⟩, rfl⟩
    exact ⟨c, d, h2, h3, h1⟩
  · rintro ⟨c, d, h2, h3, h1⟩
    exact ⟨⟨c, d, x⟩, ⟨h1, h2, h3⟩, rfl⟩

lemma heldIn_sub_held (st : St n V) (a b : ℕ) (x : Item n V) (h : x ∈ heldIn st a b) :
    x ∈ held st b := by
  rw [mem_heldIn] at h; rw [mem_held]
  obtain ⟨t', s, -, h2, h3⟩ := h
  exact ⟨t', s, h2, h3⟩

/-- Items held by `w` at round `t` (in the state of any later round). -/
lemma mem_held_exec {r t : ℕ} (htr : t ≤ r) (w : Fin n) (x : Item n V) :
    x ∈ held (exec P pol sc r w) t ↔
      ∃ t' s, t' < t ∧ (w, x) ∈ outs P pol sc t' (exec P pol sc t') s := by
  rw [mem_held]
  simp only [mem_rcv_exec]
  constructor
  · rintro ⟨t', s, h1, -, h2⟩; exact ⟨t', s, h1, h2⟩
  · rintro ⟨t', s, h1, h2⟩; exact ⟨t', s, h1, by omega, h2⟩

lemma held_mono {r r' t t' : ℕ} (htr : t ≤ r) (ht'r' : t' ≤ r') (htt' : t ≤ t') (w : Fin n)
    {x : Item n V} (h : x ∈ held (exec P pol sc r w) t) : x ∈ held (exec P pol sc r' w) t' := by
  rw [mem_held_exec P pol sc htr] at h
  rw [mem_held_exec P pol sc ht'r']
  obtain ⟨a, s, h1, h2⟩ := h
  exact ⟨a, s, by omega, h2⟩

lemma mem_heldIn_exec {r a b : ℕ} (hbr : b ≤ r) (w : Fin n) (x : Item n V) :
    x ∈ heldIn (exec P pol sc r w) a b ↔
      ∃ t' s, a ≤ t' ∧ t' < b ∧ (w, x) ∈ outs P pol sc t' (exec P pol sc t') s := by
  rw [mem_heldIn]
  simp only [mem_rcv_exec]
  constructor
  · rintro ⟨t', s, h0, h1, -, h2⟩; exact ⟨t', s, h0, h1, h2⟩
  · rintro ⟨t', s, h0, h1, h2⟩; exact ⟨t', s, h0, h1, by omega, h2⟩

/-! ### Timing -/

lemma slotLen_pos : 0 < slotLen P := by simp [slotLen]

lemma stepOf_lt (r : ℕ) : stepOf r < 11 := Nat.mod_lt _ (by norm_num)

lemma epochOf_lt (r : ℕ) : epochOf P r < P.f + 2 := by
  unfold epochOf
  have := Nat.mod_lt r (slotLen_pos P)
  unfold slotLen at *
  omega

lemma one_le_slotOf (r : ℕ) : 1 ≤ slotOf P r := by simp [slotOf]

lemma mod_slotLen_mod_eleven (r : ℕ) : r % slotLen P % 11 = r % 11 := by
  unfold slotLen
  rw [Nat.mod_mul_right_mod]

lemma roundOf_slotOf (r : ℕ) : roundOf P (slotOf P r) (epochOf P r) (stepOf r) = r := by
  unfold roundOf slotOf epochOf stepOf
  have h1 := Nat.div_add_mod r (slotLen P)
  have h2 := Nat.div_add_mod (r % slotLen P) 11
  rw [mod_slotLen_mod_eleven] at h2
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_comm (r / slotLen P)]
  omega

lemma epochStart_eq (r : ℕ) : epochStart r = roundOf P (slotOf P r) (epochOf P r) 0 := by
  have := roundOf_slotOf P r
  unfold epochStart
  unfold roundOf at *
  unfold stepOf at this
  omega

lemma slotOf_roundOf {k i s : ℕ} (hk : 1 ≤ k) (hi : i < P.f + 2) (hs : s < 11) :
    slotOf P (roundOf P k i s) = k := by
  unfold slotOf roundOf
  have : 11 * i + s < slotLen P := by unfold slotLen; nlinarith
  rw [Nat.add_assoc, Nat.add_comm ((k - 1) * slotLen P), Nat.add_mul_div_right _ _ (slotLen_pos P), Nat.div_eq_of_lt this]
  omega

lemma epochOf_roundOf {k i s : ℕ} (hi : i < P.f + 2) (hs : s < 11) :
    epochOf P (roundOf P k i s) = i := by
  unfold epochOf roundOf
  have : 11 * i + s < slotLen P := by unfold slotLen; nlinarith
  rw [Nat.add_assoc, Nat.add_comm ((k - 1) * slotLen P), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt this]
  omega

lemma stepOf_roundOf (k i s : ℕ) (hs : s < 11) : stepOf (roundOf P k i s) = s := by
  unfold stepOf roundOf slotLen
  have : (k - 1) * (11 * (P.f + 2)) + 11 * i + s = 11 * ((k - 1) * (P.f + 2) + i) + s := by ring
  rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hs]

/-- A round is determined by its slot, epoch and step. -/
lemma eq_roundOf_iff {r k i s : ℕ} (hk : 1 ≤ k) (hi : i < P.f + 2) (hs : s < 11) :
    r = roundOf P k i s ↔ slotOf P r = k ∧ epochOf P r = i ∧ stepOf r = s := by
  constructor
  · rintro rfl
    exact ⟨slotOf_roundOf P hk hi hs, epochOf_roundOf P hi hs, stepOf_roundOf P k i s hs⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact (roundOf_slotOf P r).symm

lemma roundOf_lt_roundOf {k i j s s' : ℕ} (hij : i < j) (hs : s < 11) :
    roundOf P k i s < roundOf P k j s' := by
  unfold roundOf; omega

lemma roundOf_le_roundOf {k i j s s' : ℕ} (hij : i ≤ j) (hs : s ≤ s') :
    roundOf P k i s ≤ roundOf P k j s' := by
  unfold roundOf; omega

end Podc.AmortizedByzantineBroadcast
