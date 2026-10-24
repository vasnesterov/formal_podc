import Papers.PODC2025.AmnesiacFloodingFaults.Dichotomy
import Papers.PODC2025.AmnesiacFloodingFaults.WalkAlgebra

/-!
# Balance on cycles and faux-even cycles (Definition 5.4) and Theorem 5.1

`BalancedOn S w` (balance along a closed walk) is rewritten in terms of the two additive
functionals of `WalkAlgebra.lean`:
* the *flow* `Σ_k ([S(w_k,w_{k+1})] - [S(w_{k+1},w_k)])` — clockwise minus anticlockwise
  messages (`flowSum`), and
* for even length, the *alternating occupancy* `Σ_k (-1)^k ([S(w_k,w_{k+1})] + [S(w_{k+1},w_k)])`
  (`sigSum`).

`BalancedOn S w ↔ flowSum S w = 0 ∧ (Even L → sigSum S w = 0)` (`balancedOn_iff`). For an odd
cycle this is the paper's "equal number of messages in each direction", for an even cycle the
two parity classes of heads (`classSum` at `0` and `1`).

`Balanced G S` is Definition 5.4: balance on every cycle subgraph and on the even cycle
representation of every faux-even cycle. With the spanning results of `WalkAlgebra.lean` it is
equivalent to balance along every closed walk (`balancedAll_iff_balanced`), which yields
Theorem 5.1, Corollary 5.1.1 and Theorem 5.5 as stated in the paper.
-/

namespace AmnesiacFloodingFaults

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} {L : ℕ}

/-- Antisymmetric edge weight: messages `x → y` minus messages `y → x`. -/
noncomputable def gS (S : Config V) (x y : V) : ℤ := ind ((x, y) ∈ S) - ind ((y, x) ∈ S)

/-- Symmetric edge weight: number of messages on the edge `xy`. -/
noncomputable def oS (S : Config V) (x y : V) : ℤ := ind ((x, y) ∈ S) + ind ((y, x) ∈ S)

lemma gS_antisymm (S : Config V) (x y : V) : gS S x y = - gS S y x := by unfold gS; ring

lemma oS_symm (S : Config V) (x y : V) : oS S x y = oS S y x := by unfold oS; ring

section Sums

variable [NeZero L]

/-- Clockwise minus anticlockwise messages along the closed walk `w`. -/
noncomputable def flowSum (S : Config V) (w : ZMod L → V) : ℤ :=
  ∑ k, gS S (w k) (w (k + 1))

/-- Alternating occupancy `Σ_k (-1)^k (#messages on the edge w_k w_{k+1})`. -/
noncomputable def sigSum (S : Config V) (w : ZMod L → V) : ℤ :=
  ∑ k : ZMod L, (-1) ^ k.val * oS S (w k) (w (k + 1))

omit [NeZero L] in
lemma val_natCast_of_lt {i : ℕ} (h : i < L) : ((i : ZMod L)).val = i := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]

lemma sum_zmod_eq_sum_range (f : ZMod L → ℤ) : ∑ k, f k = ∑ i ∈ range L, f i := by
  symm
  apply Finset.sum_nbij (fun i : ℕ => (i : ZMod L))
  · intro a _; exact Finset.mem_univ _
  · intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have := congrArg ZMod.val hab
    simpa [val_natCast_of_lt ha, val_natCast_of_lt hb] using this
  · intro k _
    exact ⟨k.val, by simp [ZMod.val_lt], ZMod.natCast_zmod_val k⟩
  · intro a _; rfl

lemma neg_one_pow_val_add_one (hL : Even L) (k : ZMod L) :
    ((-1 : ℤ) ^ (k + 1).val) = - (-1) ^ k.val := by
  have h1 : (k + 1).val = (k.val + 1) % L := by
    conv_lhs => rw [← ZMod.natCast_zmod_val k]
    rw [← Nat.cast_add_one, ZMod.val_natCast]
  have hk := ZMod.val_lt k
  rw [h1]
  rcases Nat.lt_or_ge (k.val + 1) L with h | h
  · rw [Nat.mod_eq_of_lt h, pow_succ]; ring
  · have : k.val + 1 = L := by omega
    rw [this, Nat.mod_self, pow_zero]
    have hodd : Odd k.val := by
      rcases Nat.even_or_odd k.val with he | ho
      · exfalso; have := (Nat.even_add_one.1 (this ▸ hL)); exact this he
      · exact ho
    rw [hodd.neg_one_pow]; norm_num

/-- The total of the class differences is the flow. -/
lemma sum_cw_sub_ccw (S : Config V) (w : ZMod L → V) :
    ∑ k, (ind (cw S w k) - ind (ccw S w k)) = flowSum S w := by
  unfold flowSum gS
  simp only [Finset.sum_sub_distrib]
  congr 1
  rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod L))]
  simp [ccw]

lemma sum_alt_cw_sub_ccw (hL : Even L) (S : Config V) (w : ZMod L → V) :
    ∑ k : ZMod L, (-1) ^ k.val * (ind (cw S w k) - ind (ccw S w k)) = sigSum S w := by
  unfold sigSum oS
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have : ∑ k : ZMod L, (-1 : ℤ) ^ k.val * ind (ccw S w k) =
      - ∑ k : ZMod L, (-1 : ℤ) ^ k.val * ind ((w (k + 1), w k) ∈ S) := by
    rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod L))]
    simp only [Equiv.coe_addRight, ccw, add_sub_cancel_right, neg_one_pow_val_add_one hL,
      neg_mul, Finset.sum_neg_distrib]
  rw [this]
  simp [cw]

omit [NeZero L] in
lemma classSum_add_two (S : Config V) (w : ZMod L → V) (k₀ : ZMod L) :
    classSum S w (k₀ + 2) = classSum S w k₀ := by
  unfold classSum
  rw [← sum_class_shift (fun k => ind (cw S w k) - ind (ccw S w k)) k₀]
  congr 1; ext i; congr 3 <;> push_cast <;> ring

omit [NeZero L] in
lemma classSum_natCast (S : Config V) (w : ZMod L → V) (n : ℕ) :
    classSum S w (n : ZMod L) = classSum S w ((n % 2 : ℕ) : ZMod L) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [Nat.cast_add, Nat.cast_ofNat, classSum_add_two, ih m (by omega), Nat.add_mod_right]

lemma sum_range_two_mul (f : ℕ → ℤ) (M : ℕ) :
    ∑ i ∈ range (2 * M), f i = ∑ i ∈ range M, f (2 * i) + ∑ i ∈ range M, f (2 * i + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- For odd `L` every class sum is the flow. -/
lemma classSum_of_odd (hL : Odd L) (S : Config V) (w : ZMod L → V) (k₀ : ZMod L) :
    classSum S w k₀ = flowSum S w := by
  rw [← sum_cw_sub_ccw]
  have hcs : classSize L = L := by unfold classSize; simp [Nat.not_even_iff_odd.2 hL]
  unfold classSum
  rw [hcs]
  set h := fun k => ind (cw S w k) - ind (ccw S w k)
  let u : (ZMod L)ˣ := ZMod.unitOfCoprime 2 (Nat.coprime_two_left.2 hL)
  have hu : ((u : ZMod L)) = 2 := by simp [u]
  let e : ZMod L ≃ ZMod L := (Units.mulLeft u).trans (Equiv.addLeft k₀)
  have : ∑ i ∈ range L, h (k₀ + 2 * (i : ZMod L)) = ∑ x : ZMod L, h (e x) := by
    rw [sum_zmod_eq_sum_range (fun x => h (e x))]
    apply Finset.sum_congr rfl; intro i _
    simp [e, hu]
  rw [this, Equiv.sum_comp e h]

/-- For even `L`, the two class sums add up to the flow and differ by the alternating sum. -/
lemma classSum_zero_add_one (hL : Even L) (S : Config V) (w : ZMod L → V) :
    classSum S w 0 + classSum S w 1 = flowSum S w ∧
      classSum S w 0 - classSum S w 1 = sigSum S w := by
  obtain ⟨M, hM⟩ := hL
  have hcs : classSize L = M := by unfold classSize; simp [show Even L from ⟨M, hM⟩]; omega
  have hL2 : L = 2 * M := by omega
  set h := fun k => ind (cw S w k) - ind (ccw S w k)
  have hr : range L = range (2 * M) := by rw [hL2]
  have hsum : ∑ k, h k = ∑ i ∈ range M, h (2 * (i : ℕ) : ℕ) +
      ∑ i ∈ range M, h ((2 * i + 1 : ℕ)) := by
    rw [sum_zmod_eq_sum_range, hr, sum_range_two_mul (fun i => h i)]
  have halt : ∑ k : ZMod L, (-1) ^ k.val * h k = ∑ i ∈ range M, h (2 * (i : ℕ) : ℕ) -
      ∑ i ∈ range M, h ((2 * i + 1 : ℕ)) := by
    rw [sum_zmod_eq_sum_range (fun k => (-1) ^ k.val * h k), hr,
      sum_range_two_mul (fun i => (-1) ^ ((i : ZMod L)).val * h i)]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> rw [Finset.mem_range] at hi
    · rw [val_natCast_of_lt (by omega), pow_mul]; simp
    · rw [val_natCast_of_lt (by omega), pow_succ, pow_mul]; simp
  have c0 : classSum S w 0 = ∑ i ∈ range M, h (2 * (i : ℕ) : ℕ) := by
    unfold classSum; rw [hcs]; apply Finset.sum_congr rfl; intro i _; simp [h]
  have c1 : classSum S w 1 = ∑ i ∈ range M, h ((2 * i + 1 : ℕ)) := by
    unfold classSum; rw [hcs]; apply Finset.sum_congr rfl; intro i _
    have e1 : (1 : ZMod L) + 2 * (i : ZMod L) = ((2 * i + 1 : ℕ) : ZMod L) := by push_cast; ring
    rw [e1]
  rw [c0, c1, ← sum_cw_sub_ccw, ← sum_alt_cw_sub_ccw ⟨M, hM⟩]
  exact ⟨hsum.symm, halt.symm⟩

/-- Balance along a closed walk in terms of the flow and the alternating occupancy. -/
theorem balancedOn_iff (S : Config V) (w : ZMod L → V) :
    BalancedOn S w ↔ flowSum S w = 0 ∧ (Even L → sigSum S w = 0) := by
  rcases Nat.even_or_odd L with hL | hL
  · obtain ⟨h1, h2⟩ := classSum_zero_add_one hL S w
    constructor
    · intro hb
      rw [hb 0, hb 1] at h1 h2
      exact ⟨by linarith, fun _ => by linarith⟩
    · rintro ⟨hf, hs⟩ k₀
      have hs := hs hL
      have e0 : classSum S w 0 = 0 := by linarith
      have e1 : classSum S w 1 = 0 := by linarith
      rw [← ZMod.natCast_zmod_val k₀, classSum_natCast]
      rcases Nat.mod_two_eq_zero_or_one k₀.val with h | h <;> rw [h] <;> simpa
  · constructor
    · intro hb
      exact ⟨by rw [← classSum_of_odd hL S w 0]; exact hb 0,
        fun he => absurd he (Nat.not_even_iff_odd.2 hL)⟩
    · rintro ⟨hf, -⟩ k₀
      rw [classSum_of_odd hL]; exact hf

/-- On a closed walk of odd length (e.g. an odd cycle), balance means that equally many messages
travel in each direction (Definition 5.4, second case). -/
theorem balancedOn_iff_of_odd (hL : Odd L) (S : Config V) (w : ZMod L → V) :
    BalancedOn S w ↔ ∑ k, ind (cw S w k) = ∑ k, ind (ccw S w k) := by
  rw [balancedOn_iff, ← sum_cw_sub_ccw, Finset.sum_sub_distrib, sub_eq_zero]
  exact ⟨fun h => h.1, fun h => ⟨h, fun he => absurd he (Nat.not_even_iff_odd.2 hL)⟩⟩

end Sums

/-! ### From Mathlib walks to closed walks `ZMod L → V` and back -/

/-- The closed walk `ZMod p.length → V` traced by a closed Mathlib walk `p`. -/
def toFun {u : V} (p : G.Walk u u) : ZMod p.length → V := fun k => p.getVert k.val

lemma isClosedWalk_toFun {u : V} (p : G.Walk u u) (hp : 0 < p.length) :
    IsClosedWalk G (toFun p) := by
  have : NeZero p.length := ⟨by omega⟩
  intro k
  have hk := ZMod.val_lt k
  have h1 : (k + 1).val = (k.val + 1) % p.length := by
    conv_lhs => rw [← ZMod.natCast_zmod_val k]
    rw [← Nat.cast_add_one, ZMod.val_natCast]
  simp only [toFun, h1]
  rcases Nat.lt_or_ge (k.val + 1) p.length with h | h
  · rw [Nat.mod_eq_of_lt h]; exact p.adj_getVert_succ hk
  · have e : k.val + 1 = p.length := by omega
    rw [e, Nat.mod_self, Walk.getVert_zero]
    have := p.adj_getVert_succ hk
    rwa [e, Walk.getVert_length] at this

lemma walkFlow_eq_sum (g : V → V → ℤ) {u v : V} (p : G.Walk u v) :
    walkFlow g p = ∑ i ∈ range p.length, g (p.getVert i) (p.getVert (i + 1)) := by
  induction p with
  | nil => simp [walkFlow]
  | cons h p ih =>
    rw [walkFlow, ih, Walk.length_cons, Finset.sum_range_succ']
    simp only [Walk.getVert_cons_succ, Walk.getVert_zero, zero_add]
    ring

lemma walkSig_eq_sum (o : V → V → ℤ) {u v : V} (p : G.Walk u v) :
    walkSig o p = ∑ i ∈ range p.length, (-1) ^ i * o (p.getVert i) (p.getVert (i + 1)) := by
  induction p with
  | nil => simp [walkSig]
  | cons h p ih =>
    rw [walkSig, ih, Walk.length_cons, Finset.sum_range_succ']
    simp only [Walk.getVert_cons_succ, Walk.getVert_zero, zero_add, pow_succ, pow_zero, one_mul,
      mul_neg_one, neg_mul, Finset.sum_neg_distrib]
    ring

lemma getVert_succ_toFun {u : V} (p : G.Walk u u) {i : ℕ} (hi : i < p.length) :
    p.getVert (((i : ZMod p.length) + 1).val) = p.getVert (i + 1) := by
  rw [← Nat.cast_add_one, ZMod.val_natCast]
  rcases Nat.lt_or_ge (i + 1) p.length with h | h
  · rw [Nat.mod_eq_of_lt h]
  · have e : i + 1 = p.length := by omega
    rw [e, Nat.mod_self, Walk.getVert_zero, Walk.getVert_length]

lemma flowSum_toFun (S : Config V) {u : V} (p : G.Walk u u) [NeZero p.length] :
    flowSum S (toFun p) = walkFlow (gS S) p := by
  rw [flowSum, sum_zmod_eq_sum_range, walkFlow_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  simp only [toFun, val_natCast_of_lt hi, getVert_succ_toFun p hi]

lemma sigSum_toFun (S : Config V) {u : V} (p : G.Walk u u) [NeZero p.length] :
    sigSum S (toFun p) = walkSig (oS S) p := by
  rw [sigSum, sum_zmod_eq_sum_range, walkSig_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  simp only [toFun, val_natCast_of_lt hi, getVert_succ_toFun p hi]

lemma walkFlow_copy_aux (g : V → V → ℤ) {u v u' v' : V} (p : G.Walk u v) (hu : u = u')
    (hv : v = v') : walkFlow g (p.copy hu hv) = walkFlow g p := by
  subst hu hv; rfl

lemma walkSig_copy_aux (o : V → V → ℤ) {u v u' v' : V} (p : G.Walk u v) (hu : u = u')
    (hv : v = v') : walkSig o (p.copy hu hv) = walkSig o p := by
  subst hu hv; rfl

lemma walkFlow_concat_aux (g : V → V → ℤ) {u v x : V} (p : G.Walk u v) (h : G.Adj v x) :
    walkFlow g (p.concat h) = walkFlow g p + g v x := by
  induction p with
  | nil => simp [Walk.concat, walkFlow]
  | cons h' p ih => rw [Walk.concat_cons, walkFlow, walkFlow, ih]; ring

lemma walkSig_concat_aux (o : V → V → ℤ) {u v x : V} (p : G.Walk u v) (h : G.Adj v x) :
    walkSig o (p.concat h) = walkSig o p + (-1) ^ p.length * o v x := by
  induction p with
  | nil => simp [Walk.concat, walkSig]
  | cons h' p ih => rw [Walk.concat_cons, walkSig, walkSig, ih, Walk.length_cons, pow_succ]; ring

/-- The Mathlib walk `w 0 → w 1 → ⋯ → w n` along a closed walk `w : ZMod L → V`. -/
def prefixWalk (w : ZMod L → V) (hw : IsClosedWalk G w) :
    (n : ℕ) → G.Walk (w 0) (w (n : ZMod L))
  | 0 => Walk.nil.copy rfl (by rw [Nat.cast_zero])
  | n + 1 => (prefixWalk w hw n).concat (by rw [Nat.cast_succ]; exact hw n)

lemma prefixWalk_length (w : ZMod L → V) (hw : IsClosedWalk G w) (n : ℕ) :
    (prefixWalk w hw n).length = n := by
  induction n with
  | zero => simp [prefixWalk]
  | succ n ih => simp [prefixWalk, ih]

lemma walkFlow_prefixWalk (g : V → V → ℤ) (w : ZMod L → V) (hw : IsClosedWalk G w) (n : ℕ) :
    walkFlow g (prefixWalk w hw n) = ∑ i ∈ range n, g (w i) (w (i + 1)) := by
  induction n with
  | zero => rw [prefixWalk, walkFlow_copy_aux]; rfl
  | succ n ih => rw [prefixWalk, walkFlow_concat_aux, ih, Finset.sum_range_succ, Nat.cast_succ]

lemma walkSig_prefixWalk (o : V → V → ℤ) (w : ZMod L → V) (hw : IsClosedWalk G w) (n : ℕ) :
    walkSig o (prefixWalk w hw n) = ∑ i ∈ range n, (-1) ^ i * o (w i) (w (i + 1)) := by
  induction n with
  | zero => rw [prefixWalk, walkSig_copy_aux]; rfl
  | succ n ih =>
    rw [prefixWalk, walkSig_concat_aux, ih, Finset.sum_range_succ, Nat.cast_succ,
      prefixWalk_length]

/-- The closed Mathlib walk around a closed walk `w : ZMod L → V`. -/
def ofFun (w : ZMod L → V) (hw : IsClosedWalk G w) : G.Walk (w 0) (w 0) :=
  (prefixWalk w hw L).copy rfl (by rw [ZMod.natCast_self])

lemma ofFun_length (w : ZMod L → V) (hw : IsClosedWalk G w) : (ofFun w hw).length = L := by
  simp [ofFun, prefixWalk_length]

lemma flowSum_eq_walkFlow_ofFun [NeZero L] (S : Config V) (w : ZMod L → V)
    (hw : IsClosedWalk G w) : flowSum S w = walkFlow (gS S) (ofFun w hw) := by
  rw [flowSum, sum_zmod_eq_sum_range, ofFun, walkFlow_copy_aux, walkFlow_prefixWalk]

lemma sigSum_eq_walkSig_ofFun [NeZero L] (S : Config V) (w : ZMod L → V)
    (hw : IsClosedWalk G w) : sigSum S w = walkSig (oS S) (ofFun w hw) := by
  rw [sigSum, sum_zmod_eq_sum_range, ofFun]
  have := walkSig_prefixWalk (oS S) w hw L
  have h2 : ∑ i ∈ range L, (-1 : ℤ) ^ ((i : ZMod L)).val * oS S (w i) (w (i + 1)) =
      ∑ i ∈ range L, (-1) ^ i * oS S (w i) (w (i + 1)) := by
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.mem_range] at hi; rw [val_natCast_of_lt hi]
  rw [h2, ← this, walkSig_copy_aux]

end AmnesiacFloodingFaults
