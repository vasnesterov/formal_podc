import Papers.PODC2019.HardnessOptimization.MaxCutGraph

/-!
# Lemma 2.4 (max-cut lower-bound graphs), for every `k = 2 ^ L ≥ 2`

Bachrach et al., *Hardness of Distributed Optimization*, PODC 2019, Section 2.4.1.

The paper proves Lemma 2.4 via Claims 2.9–2.12 about a maximum cut; the proof of Claim 2.9 needs
the total weight of the non-`k⁴` edges to be `< k⁴`, which holds only for `k ≥ 128`. We give a
direct counting proof that works for every `L ≥ 1`. For a 2-colouring `σ` let `U σ` be the number
of uncut `k⁴`-edges. We show (`main_ineq`)

  `w(σ) + k⁴·U + 2·(uncut input edges between selected rows) + (k² + k)·(#badly placed rows)
      ≤ M + k³·U`,

which gives at once `w(σ) ≤ M` for all cuts, that a cut of weight `≥ M` cuts all heavy edges
(Claim 2.9, also for maximum cuts: `claim_2_9`), and that it then witnesses an intersection of
`x` and `y`. The converse uses the explicit cut of the paper (`cutσ_star`).
-/

namespace HardnessOptimization

namespace MaxCut

variable {L : ℕ}

/-- `[p]` as a natural number. -/
abbrev ind (p : Prop) [Decidable p] : ℕ := if p then 1 else 0

section Bits

/-- Flip bit `h` of a row index. -/
def flipAt (h : Fin L) (j : Idx L) : Idx L := Function.update j h (!j h)

lemma flipAt_invol (h : Fin L) : Function.Involutive (flipAt h) := by
  intro j
  funext i
  by_cases hi : i = h
  · subst hi; simp [flipAt]
  · simp [flipAt, Function.update_of_ne hi]

/-- Half of the row indices have bit `h` set. -/
lemma two_mul_sum_bit (h : Fin L) (g : Bool → ℕ) :
    2 * ∑ j : Idx L, g (j h) = 2 ^ L * (g true + g false) := by
  have e : ∑ j : Idx L, g (j h) = ∑ j : Idx L, g (!j h) := by
    rw [← Equiv.sum_comp (flipAt_invol h).toPerm (fun j => g (j h))]
    simp [flipAt]
  calc 2 * ∑ j : Idx L, g (j h) = ∑ j : Idx L, (g (j h) + g (!j h)) := by
        rw [Finset.sum_add_distrib, ← e, two_mul]
    _ = ∑ _j : Idx L, (g true + g false) := Finset.sum_congr rfl fun j _ => by
        cases j h <;> simp [add_comm]
    _ = _ := by simp

end Bits

section Decomp

variable (x y : Idx L → Idx L → Bool) (σ : CV L → Bool)

/-- `1` if the edge is not cut. -/
def uncut (e : CE L) : ℕ := ind (σ e.src = σ e.dst)

/-- Cut weight of the `k⁴`-edges. -/
def heavyCut : ℕ := (∑ s, ec x y σ (.cn s)) + (∑ s, ec x y σ (.cbar s)) +
  ∑ s, ∑ z, ∑ h, ∑ t, ec x y σ (.cyc s z h t)

/-- Number of uncut `k⁴`-edges. -/
def U : ℕ := (∑ s, uncut σ (.cn s)) + (∑ s, uncut σ (.cbar s)) +
  ∑ s, ∑ z, ∑ h, ∑ t, uncut σ (.cyc s z h t)

/-- Cut weight of the "medium" edges at a row (to `C_s` and to `Bin(row)`). -/
def med (s z : Bool) (j : Idx L) : ℕ := ec x y σ (.rc s z j) + ∑ h, ec x y σ (.bin s z j h)

/-- Cut weight of the light (input-dependent) edges of side `s`. -/
def light (s : Bool) : ℕ :=
  (∑ z, ∑ j, ec x y σ (.rn s z j)) + ∑ i, ∑ j, ec x y σ (.inp s i j)

/-- Weight of the input edges between two rows that are both separated from `N_s`. -/
def both (s : Bool) : ℕ := ∑ i, ∑ j,
  if σ (.row s false i) ≠ σ (.nn s) ∧ σ (.row s true j) ≠ σ (.nn s) then
    wt x y (.inp s i j) else 0

lemma cutσ_decomp : cutσ x y σ = heavyCut x y σ + (∑ s, ∑ z, ∑ j, med x y σ s z j) +
    ∑ s, light x y σ s := by
  rw [cutσ, sum_CE]
  simp only [heavyCut, med, light, Finset.sum_add_distrib]
  ring

lemma ec_add_uncut {e : CE L} (he : wt x y e = (2 ^ L) ^ 4) :
    ec x y σ e + (2 ^ L) ^ 4 * uncut σ e = (2 ^ L) ^ 4 := by
  unfold ec uncut ind
  split_ifs <;> simp [he]

lemma heavyCut_add : heavyCut x y σ + (2 ^ L) ^ 4 * U σ = (2 ^ L) ^ 4 * (8 * L + 4) := by
  have h1 : ∀ s, ec x y σ (.cn s) + (2 ^ L) ^ 4 * uncut σ (.cn s) = (2 ^ L) ^ 4 :=
    fun _ => ec_add_uncut x y σ rfl
  have h2 : ∀ s, ec x y σ (.cbar s) + (2 ^ L) ^ 4 * uncut σ (.cbar s) = (2 ^ L) ^ 4 :=
    fun _ => ec_add_uncut x y σ rfl
  have h3 : ∀ s z h t, ec x y σ (.cyc s z h t) + (2 ^ L) ^ 4 * uncut σ (.cyc s z h t) =
      (2 ^ L) ^ 4 := fun _ _ _ _ => ec_add_uncut x y σ rfl
  calc heavyCut x y σ + (2 ^ L) ^ 4 * U σ =
      (∑ s, (ec x y σ (.cn s) + (2 ^ L) ^ 4 * uncut σ (.cn s))) +
      (∑ s, (ec x y σ (.cbar s) + (2 ^ L) ^ 4 * uncut σ (.cbar s))) +
      ∑ s, ∑ z, ∑ h, ∑ t, (ec x y σ (.cyc s z h t) + (2 ^ L) ^ 4 * uncut σ (.cyc s z h t)) := by
        simp only [heavyCut, U, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
        ring
    _ = _ := by
        simp only [h1, h2, h3, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
          Fintype.card_fin, smul_eq_mul]
        ring

lemma sum_toNat_add (f : Idx L → Bool) : ∑ j, (f j).toNat + ∑ j, (!f j).toNat = 2 ^ L := by
  rw [← Finset.sum_add_distrib]
  calc _ = ∑ _j : Idx L, 1 := Finset.sum_congr rfl fun j _ => by cases f j <;> rfl
    _ = _ := by simp

/-- The light edges at a first-row vertex weigh `k` in total. -/
lemma lightdeg_fst (s : Bool) (i : Idx L) :
    wt x y (.rn s false i) + ∑ j, wt x y (.inp s i j) = 2 ^ L :=
  sum_toNat_add (fun j => xy x y s i j)

/-- The light edges at a second-row vertex weigh `k` in total. -/
lemma lightdeg_snd (s : Bool) (j : Idx L) :
    wt x y (.rn s true j) + ∑ i, wt x y (.inp s i j) = 2 ^ L :=
  sum_toNat_add (fun i => xy x y s i j)

private lemma bool_aux (p q n : Bool) (w : ℕ) :
    (if p = q then 0 else w) + 2 * (if p ≠ n ∧ q ≠ n then w else 0) =
      ind (p ≠ n) * w + ind (q ≠ n) * w := by
  cases p <;> cases q <;> cases n <;> simp <;> ring

lemma light_add_both (s : Bool) :
    light x y σ s + 2 * both x y σ s =
      2 ^ L * ∑ z, ∑ j, ind (σ (.row s z j) ≠ σ (.nn s)) := by
  have hrn : ∀ z j, ec x y σ (.rn s z j) = ind (σ (.row s z j) ≠ σ (.nn s)) * wt x y (.rn s z j) := by
    intro z j
    simp only [ec, CE.src, CE.dst, ind]
    split_ifs <;> simp_all
  have hinp : ∀ i j, ec x y σ (.inp s i j) +
      2 * (if σ (.row s false i) ≠ σ (.nn s) ∧ σ (.row s true j) ≠ σ (.nn s) then
        wt x y (.inp s i j) else 0) =
      ind (σ (.row s false i) ≠ σ (.nn s)) * wt x y (.inp s i j) +
        ind (σ (.row s true j) ≠ σ (.nn s)) * wt x y (.inp s i j) := fun i j =>
    bool_aux _ _ _ _
  have e1 : light x y σ s + 2 * both x y σ s =
      (∑ z, ∑ j, ind (σ (.row s z j) ≠ σ (.nn s)) * wt x y (.rn s z j)) +
      ((∑ i, ind (σ (.row s false i) ≠ σ (.nn s)) * ∑ j, wt x y (.inp s i j)) +
        ∑ j, ind (σ (.row s true j) ≠ σ (.nn s)) * ∑ i, wt x y (.inp s i j)) := by
    simp only [light, both, hrn, Finset.mul_sum, add_assoc]
    congr 1
    rw [← Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib, hinp]
    simp only [Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_comm
  have e2 : 2 ^ L * ∑ z, ∑ j, ind (σ (.row s z j) ≠ σ (.nn s)) =
      (∑ i, ind (σ (.row s false i) ≠ σ (.nn s)) *
        (wt x y (.rn s false i) + ∑ j, wt x y (.inp s i j))) +
      ∑ j, ind (σ (.row s true j) ≠ σ (.nn s)) *
        (wt x y (.rn s true j) + ∑ i, wt x y (.inp s i j)) := by
    simp only [lightdeg_fst, lightdeg_snd, Fintype.sum_bool, ← Finset.sum_mul]
    ring
  rw [e1, e2]
  simp only [Fintype.sum_bool, mul_add, Finset.sum_add_distrib]
  ring


/-- `G1 = |Bin(row) ∩ (side of C_s)|`: the number of bit-gadget neighbours of the row on the same
side as `C_s`. -/
def G1 (s z : Bool) (j : Idx L) : ℕ := ∑ h, ind (σ (.gad s z h (j h)) = σ (.cc s))

/-- The weight `2k² log k − k²` of a row–`C` edge. -/
def wc (L : ℕ) : ℕ := 2 * (2 ^ L) ^ 2 * L - (2 ^ L) ^ 2

lemma wc_add (hL : 1 ≤ L) : wc L + (2 ^ L) ^ 2 = 2 * (2 ^ L) ^ 2 * L := by
  unfold wc
  have : (2 ^ L) ^ 2 ≤ 2 * (2 ^ L) ^ 2 * L := by nlinarith
  omega

lemma G1_le (s z : Bool) (j : Idx L) : G1 σ s z j ≤ L := by
  calc G1 σ s z j ≤ ∑ _h : Fin L, 1 := Finset.sum_le_sum fun h _ => by unfold ind; split_ifs <;> simp
    _ = L := by simp

lemma med_same {s z : Bool} {j : Idx L} (hr : σ (.row s z j) = σ (.cc s)) :
    med x y σ s z j + 2 * (2 ^ L) ^ 2 * G1 σ s z j = 2 * (2 ^ L) ^ 2 * L := by
  have h0 : ec x y σ (.rc s z j) = 0 := by simp [ec, CE.src, CE.dst, hr]
  have h1 : ∀ h, ec x y σ (.bin s z j h) + 2 * (2 ^ L) ^ 2 * ind (σ (.gad s z h (j h)) = σ (.cc s))
      = 2 * (2 ^ L) ^ 2 := by
    intro h
    simp only [ec, CE.src, CE.dst, ind, hr]
    by_cases hg : σ (.gad s z h (j h)) = σ (.cc s)
    · simp [hg]
    · simp [hg, Ne.symm hg]; rfl
  rw [med, h0, zero_add, G1, Finset.mul_sum, ← Finset.sum_add_distrib]
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

private lemma bool_aux2 (a b c : Bool) (w : ℕ) (hr : a ≠ c) :
    (if a = b then 0 else w) = ind (b = c) * w := by
  cases a <;> cases b <;> cases c <;> simp_all

lemma med_diff {s z : Bool} {j : Idx L} (hr : σ (.row s z j) ≠ σ (.cc s)) :
    med x y σ s z j = wc L + 2 * (2 ^ L) ^ 2 * G1 σ s z j := by
  have h0 : ec x y σ (.rc s z j) = wc L := by simp [ec, CE.src, CE.dst, hr]; rfl
  have h1 : ∀ h, ec x y σ (.bin s z j h) =
      2 * (2 ^ L) ^ 2 * ind (σ (.gad s z h (j h)) = σ (.cc s)) := by
    intro h
    simp only [ec, CE.src, CE.dst]
    rw [mul_comm]
    exact bool_aux2 _ _ _ _ hr
  rw [med, h0, G1, Finset.mul_sum]
  simp only [h1]

/-- The per-row upper bound. -/
def base (L g : ℕ) : ℕ :=
  wc L + 2 * (2 ^ L) ^ 2 * g + if g = 0 then (2 ^ L) ^ 2 + 2 ^ L else 0

/-- A row is badly placed: no gadget neighbour on `C_s`'s side, but the row is not on `C_s`'s
side (while `N_s` is correctly placed). -/
def bad (s z : Bool) (j : Idx L) : Prop :=
  G1 σ s z j = 0 ∧ σ (.row s z j) ≠ σ (.cc s) ∧ σ (.nn s) ≠ σ (.cc s)

instance (s z : Bool) (j : Idx L) : Decidable (bad σ s z j) := by unfold bad; infer_instance

private lemma row_arith (hL : 1 ≤ L) (a b c : Bool) (m g : ℕ)
    (hsame : a = c → m + 2 * (2 ^ L) ^ 2 * g = 2 * (2 ^ L) ^ 2 * L)
    (hdiff : a ≠ c → m = wc L + 2 * (2 ^ L) ^ 2 * g) :
    m + 2 ^ L * ind (a ≠ b) + ((2 ^ L) ^ 2 + 2 ^ L) * ind (g = 0 ∧ a ≠ c ∧ b ≠ c) ≤
      base L g + 2 ^ L * ind (b = c) := by
  have hwc := wc_add hL
  have hk : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  unfold base
  generalize wc L = w at *
  generalize 2 ^ L = k at *
  have hkK : k ≤ k ^ 2 := by nlinarith
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · cases a <;> cases b <;> cases c <;> simp [ind] at * <;> omega
  · have : k ^ 2 ≤ k ^ 2 * g := Nat.le_mul_of_pos_right _ hg
    cases a <;> cases b <;> cases c <;> simp [ind, hg.ne'] at * <;> nlinarith

lemma row_bound (hL : 1 ≤ L) (s z : Bool) (j : Idx L) :
    med x y σ s z j + 2 ^ L * ind (σ (.row s z j) ≠ σ (.nn s)) +
        ((2 ^ L) ^ 2 + 2 ^ L) * ind (bad σ s z j) ≤
      base L (G1 σ s z j) + 2 ^ L * ind (σ (.nn s) = σ (.cc s)) :=
  row_arith hL _ _ _ _ _ (med_same x y σ) (med_diff x y σ)

/-- Number of uncut inner gadget edges `t^h_S – f^h_S` of the row set `(s, z)`. -/
def u (s z : Bool) : ℕ := ∑ h, ind (σ (.gad s z h true) = σ (.gad s z h false))

/-- Number of the two gadget vertices `t^h_S, f^h_S` lying on the side of `C_s`. -/
def nh (s z : Bool) (h : Fin L) : ℕ :=
  ind (σ (.gad s z h true) = σ (.cc s)) + ind (σ (.gad s z h false) = σ (.cc s))

lemma two_mul_sum_G1 (s z : Bool) : 2 * ∑ j, G1 σ s z j = 2 ^ L * ∑ h, nh σ s z h := by
  unfold G1
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ =>
    two_mul_sum_bit h (fun b => ind (σ (.gad s z h b) = σ (.cc s)))

private lemma nh_aux (a b c : Bool) : ind (a = c) + ind (b = c) ≤ 1 + ind (a = b) := by
  cases a <;> cases b <;> cases c <;> simp

lemma sum_nh_le (s z : Bool) : ∑ h, nh σ s z h ≤ L + u σ s z := by
  calc ∑ h, nh σ s z h ≤ ∑ h, (1 + ind (σ (.gad s z h true) = σ (.gad s z h false))) :=
        Finset.sum_le_sum fun h _ => nh_aux _ _ _
    _ = L + u σ s z := by simp [Finset.sum_add_distrib, u]

lemma sum_nh_lt (s z : Bool) (h0 : Fin L) (hh0 : nh σ s z h0 = 0) :
    ∑ h, nh σ s z h + 1 ≤ L + u σ s z := by
  have : ∑ h, nh σ s z h < ∑ h, (1 + ind (σ (.gad s z h true) = σ (.gad s z h false))) :=
    Finset.sum_lt_sum (fun h _ => nh_aux _ _ _) ⟨h0, Finset.mem_univ _, by omega⟩
  have e : ∑ h, (1 + ind (σ (.gad s z h true) = σ (.gad s z h false))) = L + u σ s z := by
    simp [Finset.sum_add_distrib, u]
  omega

lemma G1_eq_zero {s z : Bool} {j : Idx L} :
    G1 σ s z j = 0 ↔ ∀ h, σ (.gad s z h (j h)) ≠ σ (.cc s) := by
  unfold G1
  rw [Finset.sum_eq_zero_iff]
  simp [ind]

lemma Z_le_one (s z : Bool) (hall : ∀ h, nh σ s z h ≠ 0) :
    ∑ j, ind (G1 σ s z j = 0) ≤ 1 := by
  rw [Finset.sum_boole]
  simp only [Nat.cast_id]
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, G1_eq_zero] at ha hb
  funext h
  have h3 := hall h
  have h1 := ha h
  have h2 := hb h
  unfold nh at h3
  cases hah : a h <;> cases hbh : b h <;> simp_all [ind]

lemma Z_le_k (s z : Bool) : ∑ j, ind (G1 σ s z j = 0) ≤ 2 ^ L :=
  calc ∑ j, ind (G1 σ s z j = 0) ≤ ∑ _j : Idx L, 1 :=
        Finset.sum_le_sum fun j _ => by unfold ind; split_ifs <;> simp
    _ = 2 ^ L := by simp

lemma sum_base (s z : Bool) :
    ∑ j, base L (G1 σ s z j) ≤
      2 ^ L * wc L + (2 ^ L) ^ 3 * L + (2 ^ L) ^ 2 + 2 ^ L + (2 ^ L) ^ 3 * u σ s z := by
  have e1 : ∑ j, base L (G1 σ s z j) = 2 ^ L * wc L + 2 * (2 ^ L) ^ 2 * ∑ j, G1 σ s z j +
      ((2 ^ L) ^ 2 + 2 ^ L) * ∑ j, ind (G1 σ s z j = 0) := by
    simp only [base, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun j _ => ?_
      unfold ind; split_ifs <;> simp
  have e2 := two_mul_sum_G1 σ s z
  have hsum := sum_nh_le σ s z
  have e3 : 2 * (2 ^ L) ^ 2 * ∑ j, G1 σ s z j = (2 ^ L) ^ 3 * ∑ h, nh σ s z h := by
    calc _ = (2 ^ L) ^ 2 * (2 * ∑ j, G1 σ s z j) := by ring
      _ = _ := by rw [e2]; ring
  rw [e1, e3]
  by_cases hall : ∀ h, nh σ s z h ≠ 0
  · have hZ := Z_le_one σ s z hall
    have h4 := Nat.mul_le_mul_left ((2 ^ L) ^ 3) hsum
    have h5 := Nat.mul_le_mul_left ((2 ^ L) ^ 2 + 2 ^ L) hZ
    generalize 2 ^ L = k at *
    nlinarith
  · simp only [ne_eq, not_forall, not_not] at hall
    obtain ⟨h0, hh0⟩ := hall
    have hsum' := sum_nh_lt σ s z h0 hh0
    have hZ := Z_le_k σ s z
    have h4 := Nat.mul_le_mul_left ((2 ^ L) ^ 3) hsum'
    have h5 := Nat.mul_le_mul_left ((2 ^ L) ^ 2 + 2 ^ L) hZ
    generalize 2 ^ L = k at *
    nlinarith

lemma U_ge : (∑ s, ind (σ (.nn s) = σ (.cc s))) + ∑ s, ∑ z, u σ s z ≤ U σ := by
  have h1 : ∑ s, ind (σ (.nn s) = σ (.cc s)) = ∑ s, uncut σ (.cn s) :=
    Finset.sum_congr rfl fun s _ => by
      unfold uncut ind
      split_ifs <;> simp_all [CE.src, CE.dst, eq_comm]
  have h2 : ∑ s, ∑ z, u σ s z ≤ ∑ s, ∑ z, ∑ h, ∑ t, uncut σ (.cyc s z h t) :=
    Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun h _ => by
      rw [Fintype.sum_bool]
      exact Nat.le_add_right _ _
  unfold U
  omega

lemma M_eq (hL : 1 ≤ L) :
    M L = (2 ^ L) ^ 4 * (8 * L + 4) + 4 * (2 ^ L * wc L + (2 ^ L) ^ 3 * L + (2 ^ L) ^ 2 + 2 ^ L) := by
  have hwc := wc_add hL
  have h12 : 12 * L - 4 + 4 = 12 * L := by omega
  unfold M
  generalize 12 * L - 4 = a at h12 ⊢
  generalize wc L = w at hwc ⊢
  generalize 2 ^ L = k at *
  have e1 : k ^ 3 * (a + 4) = k ^ 3 * (12 * L) := by rw [h12]
  have e2 : k * (w + k ^ 2) = k * (2 * k ^ 2 * L) := by rw [hwc]
  nlinarith

/-- **Main inequality.** For every 2-colouring `σ`:
`w(σ) + k⁴·U + 2·Σ both + (k² + k)·#bad ≤ M + k³·U`, where `U` is the number of uncut
`k⁴`-edges. -/
theorem main_ineq (hL : 1 ≤ L) :
    cutσ x y σ + (2 ^ L) ^ 4 * U σ + 2 * ∑ s, both x y σ s +
        ((2 ^ L) ^ 2 + 2 ^ L) * ∑ s, ∑ z, ∑ j, ind (bad σ s z j) ≤
      M L + (2 ^ L) ^ 3 * U σ := by
  have hd := cutσ_decomp x y σ
  have hH := heavyCut_add x y σ
  have hl := light_add_both x y σ
  have hRz : ∀ s z, ∑ j, med x y σ s z j + 2 ^ L * ∑ j, ind (σ (.row s z j) ≠ σ (.nn s)) +
      ((2 ^ L) ^ 2 + 2 ^ L) * ∑ j, ind (bad σ s z j) ≤
      (2 ^ L * wc L + (2 ^ L) ^ 3 * L + (2 ^ L) ^ 2 + 2 ^ L + (2 ^ L) ^ 3 * u σ s z) +
        2 ^ L * (2 ^ L * ind (σ (.nn s) = σ (.cc s))) := by
    intro s z
    have h1 := Finset.sum_le_sum (s := Finset.univ) fun j _ => row_bound x y σ hL s z j
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      smul_eq_mul] at h1
    have h2 := sum_base σ s z
    have hc : Fintype.card (Idx L) = 2 ^ L := by simp
    rw [hc] at h1
    nlinarith
  have hU := U_ge σ
  have hM := M_eq hL
  have hk : 2 ≤ 2 ^ L := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  have hk3 : 2 * (2 ^ L) ^ 2 ≤ (2 ^ L) ^ 3 := by
    have : (2 ^ L) ^ 3 = 2 ^ L * (2 ^ L) ^ 2 := by ring
    rw [this]; exact Nat.mul_le_mul_right _ hk
  have hNC : ∀ s, 2 * (2 ^ L * (2 ^ L * ind (σ (.nn s) = σ (.cc s)))) ≤
      (2 ^ L) ^ 3 * ind (σ (.nn s) = σ (.cc s)) := fun s => by
    calc _ = 2 * (2 ^ L) ^ 2 * ind (σ (.nn s) = σ (.cc s)) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hk3
  have hUm := Nat.mul_le_mul_left ((2 ^ L) ^ 3) hU
  have hl0 := hl false
  have hl1 := hl true
  have hR00 := hRz false false
  have hR01 := hRz false true
  have hR10 := hRz true false
  have hR11 := hRz true true
  have hN0 := hNC false
  have hN1 := hNC true
  simp only [Fintype.sum_bool] at hd hl0 hl1 hUm ⊢
  nlinarith

end Decomp

section Structure

variable {x y : Idx L → Idx L → Bool} {σ : CV L → Bool}

lemma two_le_two_pow (hL : 1 ≤ L) : 2 ≤ 2 ^ L :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL

lemma uncut_eq_zero {e : CE L} : uncut σ e = 0 ↔ σ e.src ≠ σ e.dst := by
  unfold uncut ind; split_ifs <;> simp_all

/-- Every cut weighs at most `M`. -/
theorem cutσ_le_M (hL : 1 ≤ L) : cutσ x y σ ≤ M L := by
  have hm := main_ineq x y σ hL
  have : (2 ^ L) ^ 3 * U σ ≤ (2 ^ L) ^ 4 * U σ :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by positivity) (by norm_num))
  omega

lemma U_eq_zero_of_ge (hL : 1 ≤ L) (c : ℕ) (hc : c < (2 ^ L) ^ 4 - (2 ^ L) ^ 3)
    (h : M L ≤ cutσ x y σ + c) : U σ = 0 := by
  have hm := main_ineq x y σ hL
  by_contra hU
  have hk := two_le_two_pow hL
  have h1 : (2 ^ L) ^ 4 = (2 ^ L) ^ 3 + ((2 ^ L) ^ 4 - (2 ^ L) ^ 3) := by
    have : (2 ^ L) ^ 3 ≤ (2 ^ L) ^ 4 := Nat.pow_le_pow_right (by positivity) (by norm_num)
    omega
  have h2 : (2 ^ L) ^ 4 * U σ = (2 ^ L) ^ 3 * U σ + ((2 ^ L) ^ 4 - (2 ^ L) ^ 3) * U σ := by
    rw [h1, add_mul, Nat.add_sub_cancel_left]
  have h3 : ((2 ^ L) ^ 4 - (2 ^ L) ^ 3) * 1 ≤ ((2 ^ L) ^ 4 - (2 ^ L) ^ 3) * U σ :=
    Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.2 hU)
  omega

lemma heavy_facts (hU : U σ = 0) :
    (∀ s, σ (.cc s) ≠ σ (.nn s)) ∧ (∀ s, σ (.cc s) ≠ σ .cbar) ∧
      ∀ s z h t, σ (CE.cyc s z h t : CE L).src ≠ σ (CE.cyc s z h t : CE L).dst := by
  unfold U at hU
  simp only [Nat.add_eq_zero_iff, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies,
    uncut_eq_zero] at hU
  exact ⟨hU.1.1, hU.1.2, hU.2⟩

/-- **Lemma 2.4, "only if" direction**: a cut of weight `≥ M` witnesses `x ∩ y ≠ ∅`. -/
theorem inter_of_M_le (hL : 1 ≤ L) (h : M L ≤ cutσ x y σ) :
    ∃ i j, x i j = true ∧ y i j = true := by
  have hm := main_ineq x y σ hL
  have hU : U σ = 0 := U_eq_zero_of_ge hL 0 (by
    have hk := two_le_two_pow hL
    have : (2 ^ L) ^ 3 < (2 ^ L) ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega) (by simpa using h)
  rw [hU, mul_zero, mul_zero, add_zero, add_zero] at hm
  have hboth : ∑ s, both x y σ s = 0 := by omega
  have hbad : ∑ s, ∑ z, ∑ j, ind (bad σ s z j) = 0 := by
    have h0 : ((2 ^ L) ^ 2 + 2 ^ L) * ∑ s, ∑ z, ∑ j, ind (bad σ s z j) = 0 := by omega
    rcases Nat.mul_eq_zero.1 h0 with h0 | h0
    · exact absurd h0 (Nat.pos_iff_ne_zero.1 (by positivity))
    · exact h0
  obtain ⟨hcn, hcb, hcyc⟩ := heavy_facts hU
  have hCC : σ (.cc true) = σ (.cc false) := by
    have h1 := hcb true; have h2 := hcb false
    revert h1 h2; cases σ (.cc true) <;> cases σ (.cc false) <;> cases σ .cbar <;> simp
  have hmir : ∀ z h b, σ (.gad true z h b) = σ (.gad false z h b) := by
    intro z h b
    have a1 : σ (.gad false z h true) ≠ σ (.gad false z h false) := hcyc false z h true
    have a2 : σ (.gad false z h false) ≠ σ (.gad true z h true) := hcyc false z h false
    have a3 : σ (.gad true z h true) ≠ σ (.gad true z h false) := hcyc true z h true
    revert a1 a2 a3
    cases b <;> cases σ (.gad false z h true) <;> cases σ (.gad false z h false) <;>
      cases σ (.gad true z h true) <;> cases σ (.gad true z h false) <;> simp
  let p : Bool → Idx L := fun z h => σ (.gad false z h true) != σ (.cc false)
  have key : ∀ z h, σ (.gad false z h (p z h)) ≠ σ (.cc false) := by
    intro z h
    have a1 : σ (.gad false z h true) ≠ σ (.gad false z h false) := hcyc false z h true
    by_cases hc : σ (.gad false z h true) = σ (.cc false)
    · have hp : p z h = false := by simp [p, hc]
      rw [hp, ← hc]; exact Ne.symm a1
    · have hp : p z h = true := by simpa [p] using hc
      rw [hp]; exact hc
  have hG : ∀ s z, G1 σ s z (p z) = 0 := by
    intro s z
    rw [G1_eq_zero]
    intro h
    cases s
    · exact key z h
    · rw [hmir, hCC]; exact key z h
  have hrow : ∀ s z, σ (.row s z (p z)) = σ (.cc s) := by
    intro s z
    have h1 : ind (bad σ s z (p z)) = 0 :=
      Finset.sum_eq_zero_iff.1 (Finset.sum_eq_zero_iff.1 (Finset.sum_eq_zero_iff.1 hbad s
        (Finset.mem_univ _)) z (Finset.mem_univ _)) (p z) (Finset.mem_univ _)
    have h2 : ¬ bad σ s z (p z) := by simpa [ind] using h1
    unfold bad at h2
    by_contra h3
    exact h2 ⟨hG s z, h3, Ne.symm (hcn s)⟩
  have hxy : ∀ s, xy x y s (p false) (p true) = true := by
    intro s
    have h1 := Finset.sum_eq_zero_iff.1 (Finset.sum_eq_zero_iff.1
      (Finset.sum_eq_zero_iff.1 hboth s (Finset.mem_univ _)) (p false) (Finset.mem_univ _))
      (p true) (Finset.mem_univ _)
    have c1 : σ (.row s false (p false)) ≠ σ (.nn s) := by rw [hrow]; exact hcn s
    have c2 : σ (.row s true (p true)) ≠ σ (.nn s) := by rw [hrow]; exact hcn s
    simp only [ne_eq, c1, c2, not_false_eq_true, and_self, ite_true] at h1
    simpa [wt] using h1
  exact ⟨p false, p true, by simpa [xy] using hxy false, by simpa [xy] using hxy true⟩

end Structure

section Star

variable (x y : Idx L → Idx L → Bool)

/-- The cut of the paper for row indices `p false = j₁`, `p true = j₂`:
`S = {a^{j₁}_1, a^{j₂}_2, b^{j₁}_1, b^{j₂}_2, C_A, C_B} ∪ ⋃_z (T_z ∪ F_z) \ Bin(row j_z)`. -/
def σstar (p : Bool → Idx L) : CV L → Bool
  | .row _ z j => decide (j = p z)
  | .gad _ z h t => t != p z h
  | .cc _ => true
  | .nn _ => false
  | .cbar => false

lemma U_star (p : Bool → Idx L) : U (σstar p) = 0 := by
  unfold U
  simp only [Nat.add_eq_zero_iff, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies,
    uncut_eq_zero]
  refine ⟨⟨fun s => by simp [σstar, CE.src, CE.dst], fun s => by simp [σstar, CE.src, CE.dst]⟩,
    fun s z h t => ?_⟩
  cases t <;> cases p z h <;> simp [σstar, CE.src, CE.dst]

lemma both_star (p : Bool → Idx L) (s : Bool) :
    both x y (σstar p) s = wt x y (.inp s (p false) (p true)) := by
  unfold both
  simp [σstar, ite_and, Finset.sum_ite_eq']

lemma light_star (p : Bool → Idx L) (s : Bool) :
    light x y (σstar p) s + 2 * wt x y (.inp s (p false) (p true)) = 2 * 2 ^ L := by
  rw [← both_star, light_add_both]
  simp [σstar, ind, Finset.sum_ite_eq', mul_comm]

lemma sum_med_star (hL : 1 ≤ L) (p : Bool → Idx L) (s z : Bool) :
    ∑ j, med x y (σstar p) s z j = 2 ^ L * wc L + (2 ^ L) ^ 3 * L + (2 ^ L) ^ 2 := by
  have hG0 : G1 (σstar p) s z (p z) = 0 := by
    rw [G1_eq_zero]; intro h; simp [σstar]
  have hpt : ∀ j, med x y (σstar p) s z j + ind (j = p z) * wc L =
      wc L + 2 * (2 ^ L) ^ 2 * G1 (σstar p) s z j + ind (j = p z) * (2 * (2 ^ L) ^ 2 * L) := by
    intro j
    by_cases hj : j = p z
    · subst hj
      have := med_same x y (σstar p) (s := s) (z := z) (j := p z) (by simp [σstar])
      rw [hG0] at this ⊢
      simp only [ind, ite_true, mul_zero, add_zero, one_mul] at this ⊢
      omega
    · have := med_diff x y (σstar p) (s := s) (z := z) (j := j) (by simp [σstar, hj])
      simp [ind, hj, this]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Idx L))) rfl fun j _ => hpt j
  simp only [Finset.sum_add_distrib, ind, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, smul_eq_mul, ←
    Finset.mul_sum] at hsum
  have hnh : ∀ h, nh (σstar p) s z h = 1 := by
    intro h; unfold nh ind; simp only [σstar]
    rcases Bool.eq_false_or_eq_true (p z h) with hp | hp <;> simp [hp]
  have h2 := two_mul_sum_G1 (σstar p) s z
  simp only [hnh, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one] at h2
  have hc : Fintype.card (Idx L) = 2 ^ L := by simp
  rw [hc] at hsum
  have hwc := wc_add hL
  generalize ∑ j, med x y (σstar p) s z j = m at *
  generalize ∑ j, G1 (σstar p) s z j = g at *
  generalize wc L = w at *
  generalize 2 ^ L = k at *
  nlinarith

/-- The weight of the paper's cut: `w(S*) = M − 2·(w(a^{j₁}_1 a^{j₂}_2) + w(b^{j₁}_1 b^{j₂}_2))`. -/
theorem cutσ_star (hL : 1 ≤ L) (p : Bool → Idx L) :
    cutσ x y (σstar p) + 2 * (wt x y (.inp false (p false) (p true)) +
      wt x y (.inp true (p false) (p true))) = M L := by
  have hd := cutσ_decomp x y (σstar p)
  have hH := heavyCut_add x y (σstar p)
  rw [U_star, mul_zero, add_zero] at hH
  have hl0 := light_star x y p false
  have hl1 := light_star x y p true
  have hm00 := sum_med_star x y hL p false false
  have hm01 := sum_med_star x y hL p false true
  have hm10 := sum_med_star x y hL p true false
  have hm11 := sum_med_star x y hL p true true
  have hM := M_eq hL
  simp only [Fintype.sum_bool] at hd
  rw [hd, hH, hm00, hm01, hm10, hm11, hM]
  linarith

end Star

/-- **Lemma 2.4** (for every `k = 2 ^ L ≥ 2`): `G_{x,y}` has a cut of weight `≥ M` iff
`DISJ(x, y) = FALSE`. -/
theorem lemma_2_4 (hL : 1 ≤ L) (x y : Idx L → Idx L → Bool) :
    (∃ S : Finset (CV L), M L ≤ cutWeight x y S) ↔ ∃ i j, x i j = true ∧ y i j = true := by
  constructor
  · rintro ⟨S, hS⟩
    rw [cutWeight_eq] at hS
    exact inter_of_M_le hL hS
  · rintro ⟨i, j, hx, hy⟩
    let p : Bool → Idx L := fun z => if z then j else i
    refine ⟨Finset.univ.filter fun v => σstar p v = true, ?_⟩
    rw [cutWeight_eq]
    have e : (fun v => decide (v ∈ Finset.univ.filter fun v => σstar p v = true)) = σstar p := by
      funext v; simp
    rw [e]
    have := cutσ_star x y hL p
    have h1 : wt x y (.inp false (p false) (p true)) = 0 := by simp [wt, xy, p, hx]
    have h2 : wt x y (.inp true (p false) (p true)) = 0 := by simp [wt, xy, p, hy]
    rw [h1, h2] at this
    omega

/-- Every cut of `G_{x,y}` weighs at most `M`. -/
theorem cutWeight_le_M (hL : 1 ≤ L) (x y : Idx L → Idx L → Bool) (S : Finset (CV L)) :
    cutWeight x y S ≤ M L := by
  rw [cutWeight_eq]; exact cutσ_le_M hL

/-- Lemma 2.4 with the paper's predicate "there is a cut of weight (exactly) `M`". -/
theorem lemma_2_4_eq (hL : 1 ≤ L) (x y : Idx L → Idx L → Bool) :
    (∃ S : Finset (CV L), cutWeight x y S = M L) ↔ ∃ i j, x i j = true ∧ y i j = true := by
  rw [← lemma_2_4 hL]
  exact ⟨fun ⟨S, hS⟩ => ⟨S, hS.ge⟩, fun ⟨S, hS⟩ => ⟨S, le_antisymm (cutWeight_le_M hL x y S) hS⟩⟩

/-- The `k⁴`-edges: `C_A N_A`, `C_B N_B`, `C_A C̄_A`, `C̄_A C_B` and the gadget 4-cycles. -/
def CE.IsHeavy : CE L → Prop
  | .cn _ => True
  | .cbar _ => True
  | .cyc .. => True
  | _ => False

/-- **Claim 2.9** (for every `k = 2 ^ L ≥ 2`; the paper's proof needs `k ≥ 128`): a maximum cut
contains all edges of weight `k⁴`. -/
theorem claim_2_9 (hL : 1 ≤ L) (x y : Idx L → Idx L → Bool) (S : Finset (CV L))
    (hS : ∀ S', cutWeight x y S' ≤ cutWeight x y S) (e : CE L) (he : e.IsHeavy) :
    (e.src ∈ S ↔ e.dst ∉ S) := by
  let p : Bool → Idx L := fun _ _ => false
  have h1 := cutσ_star x y hL p
  have h2 := hS (Finset.univ.filter fun v => σstar p v = true)
  rw [cutWeight_eq, cutWeight_eq] at h2
  have e2 : (fun v => decide (v ∈ Finset.univ.filter fun v => σstar p v = true)) = σstar p := by
    funext v; simp
  rw [e2] at h2
  have hw : ∀ s, wt x y (.inp s (p false) (p true)) ≤ 1 := fun s => by
    simp only [wt]; cases xy x y s (p false) (p true) <;> simp
  have hw0 := hw false
  have hw1 := hw true
  have hk := two_le_two_pow hL
  have hU : U (fun v => decide (v ∈ S)) = 0 := by
    refine U_eq_zero_of_ge (x := x) (y := y) hL 4 ?_ (by omega)
    have : (2 ^ L) ^ 4 - (2 ^ L) ^ 3 = (2 ^ L) ^ 3 * (2 ^ L - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_succ]
    rw [this]
    have h3 : 8 ≤ (2 ^ L) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (2 ^ L) ^ 3 := Nat.pow_le_pow_left hk 3
    have h4 : 1 ≤ 2 ^ L - 1 := by omega
    nlinarith
  obtain ⟨hcn, hcb, hcyc⟩ := heavy_facts hU
  have key : decide (e.src ∈ S) ≠ decide (e.dst ∈ S) := by
    cases e with
    | cn s => exact hcn s
    | cbar s => exact hcb s
    | cyc s z h t => exact hcyc s z h t
    | _ => exact absurd he id
  simp only [ne_eq, decide_eq_decide] at key
  tauto

end MaxCut

end HardnessOptimization
