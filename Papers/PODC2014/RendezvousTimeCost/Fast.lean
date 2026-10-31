import Papers.PODC2014.RendezvousTimeCost.Segments

/-!
# Algorithms Fast and FastWithRelabeling (Section 2 of Miller–Pelc)

* `binary ℓ` : binary representation of `ℓ`, most significant bit first;
  `modLabel x = c₁c₁c₂c₂⋯c_rc_r01` : the modified label (prefix-free: `modLabel_differ`);
  `fastSched S = (1, S[1], S[1], …, S[m], S[m])` : the segment schedule of Algorithm 2.
* `fastSched_meet` : for any two strings `SA`, `SB` that differ at (0-based) index `j`, the agents
  meet within `(2j + 3)E` rounds, for arbitrary wake-up times.
* `prop_2_2` (Proposition 2.2): Algorithm Fast meets in time `(4 ⌊log(L-1)⌋ + 9)E` at cost
  `(8 ⌊log(L-1)⌋ + 18)E`.
* `lexW t w` : the `t`-bit strings with exactly `w` ones in lexicographic order;
  `relabelLen L w` : the least positive `t` with `C(t, w) ≥ L`;
  `fastRelabel L w ℓ` : Algorithm FastWithRelabeling(w).
* `prop_2_3_time` (Proposition 2.3, time): `(4t + 5)E`.
* `prop_2_3_cost_false` : the cost bound `2wE` of Proposition 2.3 is **false**
  (explicit counterexample on the oriented 3-ring, `L = 2`, `w = 1`, cost `6 > 4`);
  `prop_2_3_cost_repaired` : the cost is at most `(8w + 6)E`.
* `cor_2_1` (Corollary 2.1, concrete form): for `w = c ≥ 1` and `L ≤ k ^ c`: time `≤ (4ck + 5)E`,
  cost `≤ (8c + 6)E` (the paper claims `2cE`).
-/

namespace Podc.RendezvousTimeCost.Upper

variable {V : Type*} {E : ℕ}

/-! ### Bit-string transformations -/

/-- Doubling every bit: `c₁c₂⋯ ↦ c₁c₁c₂c₂⋯`. -/
def dbl (x : List Bool) : List Bool := x.flatMap fun b => [b, b]

@[simp] lemma dbl_nil : dbl [] = [] := rfl

@[simp] lemma dbl_cons (a : Bool) (x : List Bool) : dbl (a :: x) = a :: a :: dbl x := rfl

@[simp] lemma dbl_length (x : List Bool) : (dbl x).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons a x ih => simp [ih]; ring

@[simp] lemma dbl_count (x : List Bool) : (dbl x).count true = 2 * x.count true := by
  induction x with
  | nil => rfl
  | cons a x ih => simp only [dbl_cons, List.count_cons, ih]; split_ifs <;> ring

lemma dbl_getD (x : List Bool) (j : ℕ) :
    (dbl x).getD (2 * j) false = x.getD j false ∧
      (dbl x).getD (2 * j + 1) false = x.getD j false := by
  induction x generalizing j with
  | nil => simp
  | cons a x ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, show 2 * j + 1 + 1 + 1 = 2 * j + 1 + 1 + 1
        from rfl, dbl_cons, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
        List.getD_cons_succ, List.getD_cons_succ]
      exact ih j

/-- The binary representation of `ℓ`, most significant bit first. -/
def binary (ℓ : ℕ) : List Bool := (Nat.digits 2 ℓ).reverse.map fun d => d == 1

lemma binary_length {ℓ : ℕ} (hℓ : ℓ ≠ 0) : (binary ℓ).length = Nat.log 2 ℓ + 1 := by
  simp [binary, Nat.length_digits 2 ℓ (by norm_num) hℓ]

lemma binary_injective : Function.Injective binary := by
  have key : ∀ ℓ, (binary ℓ).map (fun b => if b then 1 else 0) = (Nat.digits 2 ℓ).reverse := by
    intro ℓ
    rw [binary, List.map_map]
    conv_rhs => rw [← List.map_id (Nat.digits 2 ℓ).reverse]
    refine List.map_congr_left fun d hd => ?_
    have : d < 2 := Nat.digits_lt_base (by norm_num) (List.mem_reverse.1 hd)
    interval_cases d <;> rfl
  intro x y h
  have := key x
  rw [h, key y, List.reverse_inj] at this
  exact Nat.digits.injective 2 this.symm

/-- The modified label `M(x) = (c₁c₁c₂c₂⋯c_rc_r01)` of [Miller–Pelc, Section 2]. -/
def modLabel (x : List Bool) : List Bool := dbl x ++ [false, true]

@[simp] lemma modLabel_length (x : List Bool) : (modLabel x).length = 2 * x.length + 2 := by
  simp [modLabel]

@[simp] lemma modLabel_count (x : List Bool) : (modLabel x).count true = 2 * x.count true + 1 := by
  simp [modLabel]

lemma modLabel_cons (a : Bool) (x : List Bool) : modLabel (a :: x) = a :: a :: modLabel x := rfl

/-- Modified labels of distinct strings differ at an index smaller than both lengths (`M(x)` is
never a prefix of `M(y)`). -/
lemma modLabel_differ {x y : List Bool} (hxy : x ≠ y) :
    ∃ j < 2 * min x.length y.length + 2,
      (modLabel x).getD j false ≠ (modLabel y).getD j false := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => exact absurd rfl hxy
    | cons b y => cases b
                  · exact ⟨1, by simp, by simp [modLabel]⟩
                  · exact ⟨0, by simp, by simp [modLabel]⟩
  | cons a x ih =>
    cases y with
    | nil => cases a
             · exact ⟨1, by simp, by simp [modLabel]⟩
             · exact ⟨0, by simp, by simp [modLabel]⟩
    | cons b y =>
      by_cases hab : a = b
      · subst hab
        obtain ⟨j, hj, h⟩ := ih (fun h => hxy (h ▸ rfl))
        refine ⟨j + 2, ?_, ?_⟩
        · simp only [List.length_cons, Nat.add_min_add_right]; omega
        · simpa [modLabel_cons] using h
      · exact ⟨0, by omega, by simpa [modLabel_cons] using hab⟩

/-- The segment schedule of **Algorithm 2** (Fast): `T = (1, S[1], S[1], …, S[m], S[m])`. -/
def fastSched (S : List Bool) : List Bool := true :: dbl S

@[simp] lemma fastSched_count (S : List Bool) : (fastSched S).count true = 2 * S.count true + 1 :=
  by simp [fastSched]

lemma fastSched_getD (S : List Bool) (j : ℕ) :
    (fastSched S).getD (2 * j + 1) false = S.getD j false ∧
      (fastSched S).getD (2 * j + 2) false = S.getD j false := by
  rw [fastSched, List.getD_cons_succ, List.getD_cons_succ]
  exact dbl_getD S j

/-- **Algorithm 2** `Fast(ℓ)`: the schedule built from the modified binary label. -/
def fast (ℓ : ℕ) : List Bool := fastSched (modLabel (binary ℓ))

/-! ### Correctness and time of schedules of Fast type -/

/-- Core of Proposition 2.2: the earlier agent `P` (delay `0`) and the later agent `Q`
(delay `τ`) meet within `(2j + 3)E` rounds if their strings differ at index `j`. -/
lemma fastSched_core (X : Explore V E) {SP SQ : List Bool} {j : ℕ}
    (hj : SP.getD j false ≠ SQ.getD j false) (vP vQ : V) (τ : ℕ) :
    ∃ r ≤ (2 * j + 3) * E, MeetsAt X ⟨fastSched SP, vP, 0⟩ ⟨fastSched SQ, vQ, τ⟩ r := by
  set P : Agent V := ⟨fastSched SP, vP, 0⟩
  set Q : Agent V := ⟨fastSched SQ, vQ, τ⟩
  by_cases hτ : E ≤ τ
  · obtain ⟨s, hs, h⟩ := pos_explore X P (i := 0) rfl vQ
    simp only [P, zero_mul, add_zero, zero_add] at h
    refine ⟨s, hs.trans (Nat.le_mul_of_pos_left _ (by omega)), ?_⟩
    show pos X P s = pos X Q s
    rw [h, pos_of_le_delay X Q (by simp [Q]; omega)]
  · push Not at hτ
    have gP := fastSched_getD SP j
    have gQ := fastSched_getD SQ j
    cases hP : SP.getD j false
    · -- `P` idle in segments `2j+1, 2j+2`, `Q` explores in segment `2j+1`
      have hQ : SQ.getD j false = true := by rw [hP] at hj; simpa using hj.symm
      have hidle := pos_idle_range X P (i := 2 * j + 1) (j := 2 * j + 3) (by omega)
        (fun k hk1 hk2 => by
          obtain rfl | rfl : k = 2 * j + 1 ∨ k = 2 * j + 2 := by omega
          · simp only [P]; rw [gP.1, hP]
          · simp only [P]; rw [gP.2, hP])
      have hexp := pos_explore X Q (i := 2 * j + 1) (by simp only [Q]; rw [gQ.1, hQ])
      obtain ⟨r, hr1, hr2, hm⟩ := meet_of_window _ hidle hexp (by simp only [P, Q]; omega)
        (by simp only [P, Q]; rtc_omega)
      exact ⟨r, by simp only [Q] at hr2; rtc_omega, hm⟩
    · -- `Q` idle in segments `2j+1, 2j+2`, `P` explores in segment `2j+2`
      have hQ : SQ.getD j false = false := by rw [hP] at hj; simpa using hj.symm
      have hidle := pos_idle_range X Q (i := 2 * j + 1) (j := 2 * j + 3) (by omega)
        (fun k hk1 hk2 => by
          obtain rfl | rfl : k = 2 * j + 1 ∨ k = 2 * j + 2 := by omega
          · simp only [Q]; rw [gQ.1, hQ]
          · simp only [Q]; rw [gQ.2, hQ])
      have hexp := pos_explore X P (i := 2 * j + 2) (by simp only [P]; rw [gP.2, hP])
      obtain ⟨r, hr1, hr2, hm⟩ := meet_of_window _ hidle hexp (by simp only [P, Q]; rtc_omega)
        (by simp only [P, Q]; rtc_omega)
      exact ⟨r, by simp only [P] at hr2; rtc_omega, hm.symm⟩

/-- Correctness and time of any schedule of Fast type: if the strings `SA`, `SB` differ at the
(0-based) index `j`, the agents meet within `(2j + 3)E` rounds of the earlier wake-up, for
arbitrary starting nodes and wake-up times. (The paper's `(2j+1)E` with 1-based `j`.) -/
theorem fastSched_meet (X : Explore V E) {SA SB : List Bool} {j : ℕ}
    (hj : SA.getD j false ≠ SB.getD j false) (vA vB : V) {δA δB : ℕ} (hδ : δA = 0 ∨ δB = 0) :
    (∃ r, MeetsAt X ⟨fastSched SA, vA, δA⟩ ⟨fastSched SB, vB, δB⟩ r) ∧
      meetTime X ⟨fastSched SA, vA, δA⟩ ⟨fastSched SB, vB, δB⟩ ≤ (2 * j + 3) * E := by
  have : ∃ r ≤ (2 * j + 3) * E, MeetsAt X ⟨fastSched SA, vA, δA⟩ ⟨fastSched SB, vB, δB⟩ r := by
    rcases hδ with rfl | rfl
    · exact fastSched_core X hj vA vB δB
    · obtain ⟨r, hr, hm⟩ := fastSched_core X (Ne.symm hj) vB vA δA
      exact ⟨r, hr, (meetsAt_comm X _ _ _).1 hm⟩
  obtain ⟨r, hr, hm⟩ := this
  exact ⟨⟨r, hm⟩, (meetTime_le X hm).trans hr⟩

/-! ### Proposition 2.2 -/

variable [DecidableEq V]

/-- **Proposition 2.2** (stronger form, from its proof): Algorithm Fast completes rendezvous
within `(4 ⌊log₂ min(ℓA, ℓB)⌋ + 9)E` rounds, at cost at most twice that. -/
theorem prop_2_2_min (X : Explore V E) {ℓA ℓB : ℕ} (hA : 1 ≤ ℓA) (hB : 1 ≤ ℓB) (hne : ℓA ≠ ℓB)
    (vA vB : V) {δA δB : ℕ} (hδ : δA = 0 ∨ δB = 0) :
    (∃ r, MeetsAt X ⟨fast ℓA, vA, δA⟩ ⟨fast ℓB, vB, δB⟩ r) ∧
      meetTime X ⟨fast ℓA, vA, δA⟩ ⟨fast ℓB, vB, δB⟩ ≤ (4 * Nat.log 2 (min ℓA ℓB) + 9) * E ∧
      cost X ⟨fast ℓA, vA, δA⟩ ⟨fast ℓB, vB, δB⟩ ≤ (8 * Nat.log 2 (min ℓA ℓB) + 18) * E := by
  simp only [fast]
  obtain ⟨j, hj, hd⟩ := modLabel_differ (binary_injective.ne hne)
  obtain ⟨hm, ht⟩ := fastSched_meet X hd vA vB hδ
  rw [binary_length (by omega), binary_length (by omega)] at hj
  have hjl : 2 * j + 3 ≤ 4 * Nat.log 2 (min ℓA ℓB) + 9 := by
    rcases le_total ℓA ℓB with h | h
    · rw [min_eq_left h]; rw [min_eq_left (by have := Nat.log_mono_right (b := 2) h; omega)] at hj
      omega
    · rw [min_eq_right h]; rw [min_eq_right (by have := Nat.log_mono_right (b := 2) h; omega)] at hj
      omega
  have ht' := ht.trans (Nat.mul_le_mul_right E hjl)
  refine ⟨hm, ht', (cost_le_two_mul_meetTime X _ _).trans ?_⟩
  rtc_omega

/-- **Proposition 2.2** of [Miller–Pelc]: for distinct labels in `[1, L]`, Algorithm Fast
completes rendezvous with cost at most `(8 ⌊log₂(L-1)⌋ + 18)E` and in time at most
`(4 ⌊log₂(L-1)⌋ + 9)E`, for arbitrary starting nodes and wake-up times. -/
theorem prop_2_2 (X : Explore V E) {L ℓA ℓB : ℕ} (hA : ℓA ∈ Set.Icc 1 L)
    (hB : ℓB ∈ Set.Icc 1 L) (hne : ℓA ≠ ℓB) (vA vB : V) {δA δB : ℕ} (hδ : δA = 0 ∨ δB = 0) :
    (∃ r, MeetsAt X ⟨fast ℓA, vA, δA⟩ ⟨fast ℓB, vB, δB⟩ r) ∧
      meetTime X ⟨fast ℓA, vA, δA⟩ ⟨fast ℓB, vB, δB⟩ ≤ (4 * Nat.log 2 (L - 1) + 9) * E ∧
      cost X ⟨fast ℓA, vA, δA⟩ ⟨fast ℓB, vB, δB⟩ ≤ (8 * Nat.log 2 (L - 1) + 18) * E := by
  obtain ⟨h1, h2, h3⟩ := prop_2_2_min X hA.1 hB.1 hne vA vB hδ
  have hlog : Nat.log 2 (min ℓA ℓB) ≤ Nat.log 2 (L - 1) :=
    Nat.log_mono_right (by have := hA.2; have := hB.2; omega)
  refine ⟨h1, h2.trans (Nat.mul_le_mul_right _ (by omega)),
    h3.trans (Nat.mul_le_mul_right _ (by omega))⟩

/-! ### FastWithRelabeling -/

/-- All `n`-bit strings with exactly `k` ones, in lexicographic order (`false < true`). -/
def lexW : ℕ → ℕ → List (List Bool)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, 0 => (lexW n 0).map (false :: ·)
  | n + 1, k + 1 => (lexW n (k + 1)).map (false :: ·) ++ (lexW n k).map (true :: ·)

lemma lexW_length (n k : ℕ) : (lexW n k).length = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih => cases k <;> simp [lexW, ih, Nat.choose_succ_succ, add_comm]

lemma mem_lexW {n k : ℕ} {s : List Bool} :
    s ∈ lexW n k ↔ s.length = n ∧ s.count true = k := by
  induction n generalizing k s with
  | zero =>
    cases k <;> cases s <;> simp [lexW]
  | succ n ih =>
    cases k with
    | zero => cases s with
      | nil => simp [lexW]
      | cons b s => cases b <;> simp [lexW, ih]
    | succ k => cases s with
      | nil => simp [lexW]
      | cons b s => cases b <;> simp [lexW, ih]

/-- `lexW n k` is strictly increasing in the lexicographic order. -/
lemma lexW_sorted (n k : ℕ) : (lexW n k).Pairwise (· < ·) := by
  induction n generalizing k with
  | zero => cases k <;> simp [lexW]
  | succ n ih =>
    cases k with
    | zero => simpa [lexW, List.pairwise_map, List.cons_lt_cons_iff] using ih 0
    | succ k =>
      simp only [lexW, List.pairwise_append, List.pairwise_map, List.mem_map]
      refine ⟨?_, ?_, ?_⟩
      · simpa [List.cons_lt_cons_iff] using ih (k + 1)
      · simpa [List.cons_lt_cons_iff] using ih k
      · rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
        simp [List.cons_lt_cons_iff]

lemma lexW_nodup (n k : ℕ) : (lexW n k).Nodup :=
  (lexW_sorted n k).imp fun h => ne_of_lt h

/-- The least positive `t` with `C(t, w) ≥ L` (the length of the new labels). -/
noncomputable def relabelLen (L w : ℕ) : ℕ := sInf {t | 0 < t ∧ L ≤ t.choose w}

lemma le_choose_add {L w : ℕ} (hw : 1 ≤ w) : L ≤ (L + w).choose w := by
  induction w, hw using Nat.le_induction with
  | base => simp
  | succ w _ ih =>
    rw [← add_assoc, Nat.choose_succ_succ]
    omega

lemma relabelLen_spec {L w : ℕ} (hw : 1 ≤ w) :
    0 < relabelLen L w ∧ L ≤ (relabelLen L w).choose w :=
  Nat.sInf_mem (s := {t | 0 < t ∧ L ≤ t.choose w}) ⟨L + w, by omega, le_choose_add hw⟩

lemma relabelLen_le {L w t : ℕ} (ht : 0 < t) (h : L ≤ t.choose w) : relabelLen L w ≤ t :=
  Nat.sInf_le ⟨ht, h⟩

/-- The new label of `ℓ ∈ [1, L]`: the `ℓ`-th smallest (in lexicographic order) `t`-bit string
with exactly `w` ones, `t = relabelLen L w`. -/
noncomputable def newLabel (L w ℓ : ℕ) : List Bool := (lexW (relabelLen L w) w).getD (ℓ - 1) []

/-- **Algorithm FastWithRelabeling(w)**: Algorithm Fast run on the new label. -/
noncomputable def fastRelabel (L w ℓ : ℕ) : List Bool := fastSched (modLabel (newLabel L w ℓ))

lemma newLabel_mem {L w ℓ : ℕ} (hw : 1 ≤ w) (hℓ : ℓ ∈ Set.Icc 1 L) :
    newLabel L w ℓ ∈ lexW (relabelLen L w) w := by
  have h := (relabelLen_spec (L := L) hw).2
  have hi : ℓ - 1 < (lexW (relabelLen L w) w).length := by
    rw [lexW_length]; have := hℓ.1; have := hℓ.2; omega
  rw [newLabel, List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

lemma newLabel_injOn {L w ℓA ℓB : ℕ} (hw : 1 ≤ w) (hA : ℓA ∈ Set.Icc 1 L)
    (hB : ℓB ∈ Set.Icc 1 L) (hne : ℓA ≠ ℓB) : newLabel L w ℓA ≠ newLabel L w ℓB := by
  have h := (relabelLen_spec (L := L) hw).2
  have hiA : ℓA - 1 < (lexW (relabelLen L w) w).length := by
    rw [lexW_length]; have := hA.1; have := hA.2; omega
  have hiB : ℓB - 1 < (lexW (relabelLen L w) w).length := by
    rw [lexW_length]; have := hB.1; have := hB.2; omega
  rw [newLabel, newLabel, List.getD_eq_getElem _ _ hiA, List.getD_eq_getElem _ _ hiB,
    Ne, (lexW_nodup _ _).getElem_inj_iff]
  have := hA.1; have := hB.1
  omega

omit [DecidableEq V] in
/-- **Proposition 2.3** of [Miller–Pelc], time part: for `w ≥ 1`, Algorithm
FastWithRelabeling(w) completes rendezvous in time at most `(4t + 5)E`, where `t` is the least
positive integer with `C(t, w) ≥ L`. -/
theorem prop_2_3_time (X : Explore V E) {L w ℓA ℓB : ℕ} (hw : 1 ≤ w) (hA : ℓA ∈ Set.Icc 1 L)
    (hB : ℓB ∈ Set.Icc 1 L) (hne : ℓA ≠ ℓB) (vA vB : V) {δA δB : ℕ} (hδ : δA = 0 ∨ δB = 0) :
    (∃ r, MeetsAt X ⟨fastRelabel L w ℓA, vA, δA⟩ ⟨fastRelabel L w ℓB, vB, δB⟩ r) ∧
      meetTime X ⟨fastRelabel L w ℓA, vA, δA⟩ ⟨fastRelabel L w ℓB, vB, δB⟩ ≤
        (4 * relabelLen L w + 5) * E := by
  obtain ⟨j, hj, hd⟩ := modLabel_differ (newLabel_injOn hw hA hB hne)
  obtain ⟨hm, ht⟩ := fastSched_meet X hd vA vB hδ
  refine ⟨hm, ht.trans (Nat.mul_le_mul_right _ ?_)⟩
  rw [(mem_lexW.1 (newLabel_mem hw hA)).1, (mem_lexW.1 (newLabel_mem hw hB)).1, min_self] at hj
  omega

/-- Each agent running FastWithRelabeling(w) explores in exactly `4w + 3` segments, so it makes
at most `(4w + 3)E` moves. -/
lemma fastRelabel_count {L w ℓ : ℕ} (hw : 1 ≤ w) (hℓ : ℓ ∈ Set.Icc 1 L) :
    (fastRelabel L w ℓ).count true = 4 * w + 3 := by
  rw [fastRelabel, fastSched_count, modLabel_count, (mem_lexW.1 (newLabel_mem hw hℓ)).2]
  ring

/-- **Proposition 2.3, repaired cost bound**: Algorithm FastWithRelabeling(w) has cost at most
`(8w + 6)E` (instead of the paper's `2wE`, which is false: `prop_2_3_cost_false`). -/
theorem prop_2_3_cost_repaired (X : Explore V E) {L w ℓA ℓB : ℕ} (hw : 1 ≤ w)
    (hA : ℓA ∈ Set.Icc 1 L) (hB : ℓB ∈ Set.Icc 1 L) (vA vB : V) (δA δB : ℕ) :
    cost X ⟨fastRelabel L w ℓA, vA, δA⟩ ⟨fastRelabel L w ℓB, vB, δB⟩ ≤ (8 * w + 6) * E := by
  have h1 := (moveCount_segTraj X (fastRelabel L w ℓA) vA
    (meetTime X ⟨fastRelabel L w ℓA, vA, δA⟩ ⟨fastRelabel L w ℓB, vB, δB⟩ - δA))
  have h2 := (moveCount_segTraj X (fastRelabel L w ℓB) vB
    (meetTime X ⟨fastRelabel L w ℓA, vA, δA⟩ ⟨fastRelabel L w ℓB, vB, δB⟩ - δB))
  rw [fastRelabel_count hw hA, mul_comm E] at h1
  rw [fastRelabel_count hw hB, mul_comm E] at h2
  rw [cost, moveCount_pos, moveCount_pos]
  simp only at h1 h2 ⊢
  rtc_omega

/-! ### The cost bound of Proposition 2.3 is false -/

/-- The oriented ring with 3 nodes, explored clockwise: `E = 2`. -/
def ring3 : Explore (ZMod 3) 2 where
  walk v t := v + ((min t 2 : ℕ) : ZMod 3)
  walk_zero v := by simp
  covers v u := ⟨(u - v).val, by have := (u - v).val_lt; omega, by
    rw [min_eq_left (by have := (u - v).val_lt; omega), ZMod.natCast_zmod_val]; ring⟩

lemma relabelLen_two_one : relabelLen 2 1 = 2 :=
  le_antisymm (relabelLen_le (by norm_num) (by norm_num))
    (by have := (relabelLen_spec (L := 2) le_rfl).2; simpa using this)

lemma fastRelabel_two_one_one :
    fastRelabel 2 1 1 = [true, false, false, false, false, true, true, true, true, false, false,
      true, true] := by
  rw [fastRelabel, newLabel, relabelLen_two_one]; rfl

lemma fastRelabel_two_one_two :
    fastRelabel 2 1 2 = [true, true, true, true, true, false, false, false, false, false, false,
      true, true] := by
  rw [fastRelabel, newLabel, relabelLen_two_one]; rfl

/-- The execution of the counterexample: oriented 3-ring (`E = 2`), `L = 2`, `w = 1`, labels
`1 ↦ 01`, `2 ↦ 10`, simultaneous start at nodes `0` and `1`. The agents first meet at time `4`. -/
lemma ce_meetTime :
    meetTime ring3 ⟨fastRelabel 2 1 1, 0, 0⟩ ⟨fastRelabel 2 1 2, 1, 0⟩ = 4 := by
  rw [fastRelabel_two_one_one, fastRelabel_two_one_two]
  have h4 : MeetsAt ring3 ⟨[true, false, false, false, false, true, true, true, true, false,
      false, true, true], 0, 0⟩ ⟨[true, true, true, true, true, false, false, false, false, false,
      false, true, true], 1, 0⟩ 4 := by simp only [MeetsAt]; decide
  refine le_antisymm (meetTime_le _ h4) (le_csInf ⟨4, h4⟩ fun r hr => ?_)
  by_contra hlt
  push Not at hlt
  simp only [Set.mem_ofPred_eq, MeetsAt] at hr
  interval_cases r <;> revert hr <;> decide

/-- In the counterexample execution the cost (edge traversals before rendezvous) is `6`. -/
lemma ce_cost : cost ring3 ⟨fastRelabel 2 1 1, 0, 0⟩ ⟨fastRelabel 2 1 2, 1, 0⟩ = 6 := by
  rw [cost, ce_meetTime, fastRelabel_two_one_one, fastRelabel_two_one_two]
  decide

/-- **Proposition 2.3 (cost part) is false.** The claimed bound "cost at most `2 · w(L) · E`"
fails already for the oriented 3-ring (`E = 2`), `L = 2`, `w = 1`, simultaneous start: both agents
explore in their first segment, before anything distinguishes them, and the execution
`ce_cost` has cost `6 > 2 · 1 · 2`. -/
theorem prop_2_3_cost_false :
    ¬ ∀ (V : Type) [DecidableEq V] (E : ℕ) (X : Explore V E) (L w ℓA ℓB : ℕ) (vA vB : V)
      (δA δB : ℕ), 1 ≤ w → w ≤ L → ℓA ∈ Set.Icc 1 L → ℓB ∈ Set.Icc 1 L → ℓA ≠ ℓB → vA ≠ vB →
      (δA = 0 ∨ δB = 0) →
      cost X ⟨fastRelabel L w ℓA, vA, δA⟩ ⟨fastRelabel L w ℓB, vB, δB⟩ ≤ 2 * w * E := by
  intro h
  have := h (ZMod 3) 2 ring3 2 1 1 2 0 1 0 0 le_rfl (by norm_num) ⟨le_rfl, by norm_num⟩
    ⟨by norm_num, le_rfl⟩ (by norm_num) (by decide) (Or.inl rfl)
  rw [ce_cost] at this
  omega

/-! ### Corollary 2.1 -/

/-- `C(ck, c) ≥ k ^ c` (choose one element in each of `c` blocks of size `k`). -/
lemma pow_le_choose_mul (c k : ℕ) : k ^ c ≤ (c * k).choose c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ, Nat.succ_mul, Nat.add_choose_eq]
    have hmem : (c, 1) ∈ Finset.HasAntidiagonal.antidiagonal (c + 1) := by simp
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem)
    simpa using Nat.mul_le_mul_right k ih

/-- **Corollary 2.1** (concrete form): for a constant `w = c ≥ 1` and any `k ≥ 1` with
`L ≤ k ^ c` (e.g. `k = ⌈L^{1/c}⌉`), the new label length is `t ≤ c k`, so Algorithm
FastWithRelabeling(c) completes rendezvous in time at most `(4ck + 5)E = O(L^{1/c} E)` and at cost
at most `(8c + 6)E = O(E)` (the paper states `2cE`, relying on the false cost bound of
Proposition 2.3). -/
theorem cor_2_1 (X : Explore V E) {L c k ℓA ℓB : ℕ} (hc : 1 ≤ c) (hk : 1 ≤ k) (hL : L ≤ k ^ c)
    (hA : ℓA ∈ Set.Icc 1 L) (hB : ℓB ∈ Set.Icc 1 L) (hne : ℓA ≠ ℓB) (vA vB : V) {δA δB : ℕ}
    (hδ : δA = 0 ∨ δB = 0) :
    relabelLen L c ≤ c * k ∧
      (∃ r, MeetsAt X ⟨fastRelabel L c ℓA, vA, δA⟩ ⟨fastRelabel L c ℓB, vB, δB⟩ r) ∧
      meetTime X ⟨fastRelabel L c ℓA, vA, δA⟩ ⟨fastRelabel L c ℓB, vB, δB⟩ ≤
        (4 * c * k + 5) * E ∧
      cost X ⟨fastRelabel L c ℓA, vA, δA⟩ ⟨fastRelabel L c ℓB, vB, δB⟩ ≤ (8 * c + 6) * E := by
  have ht : relabelLen L c ≤ c * k :=
    relabelLen_le (Nat.mul_pos (by omega) (by omega)) (hL.trans (pow_le_choose_mul c k))
  obtain ⟨hm, htime⟩ := prop_2_3_time X hc hA hB hne vA vB hδ
  refine ⟨ht, hm, htime.trans (Nat.mul_le_mul_right _ (by rw [mul_assoc]; omega)),
    prop_2_3_cost_repaired X hc hA hB vA vB δA δB⟩

end Podc.RendezvousTimeCost.Upper
