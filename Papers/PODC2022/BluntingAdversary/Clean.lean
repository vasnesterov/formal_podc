import Papers.PODC2022.BluntingAdversary.Removal

/-!
# Lemma 4.5: the object random steps rarely choose a spoiled iteration

We bound, for every strong adversary, the probability of `¬X` (some object random step of `O^k`
chose a preamble iteration that overlapped a program random step) by
`1 - (max{0, k - r} / k)^(n - 1)`, where `n` is the number of processes and `r` bounds the number
of program random steps of `P(O)`.

The proof is a supersolution argument (`MDP.opt_le_of_super`) with the potential
`Φ = [no xbad] · ∏_q w(spc q) · ψ(coins)`: `spc q` is the number of spoiled preamble iterations
of the current invocation of `q` (completed ones, plus the current one if it already overlaps a
program random step), `w s = (k - s)/k` is the probability that `q`'s object random step picks a
clean iteration, and `ψ t = ∏_{t < u ≤ r} ((k - u)/(k - u + 1))^(n - 1)` accounts for the
program random steps still to come. Each program random step spoils at most one iteration of at
most `n - 1` other processes, and `w (s + 1) ≥ w s · (k - t - 1)/(k - t)` when `s ≤ t`.
-/

namespace Podc.BluntingAdversary

open Cslib.SharedMemory
open scoped Classical

namespace Clean

open Removal

variable {P : Type} [DecidableEq P] {A : ObjSpec} {C L : Type} {ι : Type} [DecidableEq ι]
  {Bs : ι → ObjSpec}

/-! ### Numeric factors -/

/-- Probability that an object random step with `s` spoiled iterations out of `k` picks a clean
one. -/
noncomputable def w (k s : ℕ) : ℝ := ((k - s : ℕ) : ℝ) / k

/-- The factor lost by one spoiled iteration at the `u`-th program random step. -/
noncomputable def f (k u : ℕ) : ℝ := ((k - u : ℕ) : ℝ) / ((k - u : ℕ) + 1)

/-- The factor reserved for the program random steps `t + 1, …, r`. -/
noncomputable def ψ (k r n t : ℕ) : ℝ := ∏ u ∈ Finset.Ioc t r, f k u ^ (n - 1)

lemma f_nonneg (k u : ℕ) : 0 ≤ f k u := by unfold f; positivity

lemma f_le_one (k u : ℕ) : f k u ≤ 1 := by
  unfold f; rw [div_le_one (by positivity)]; linarith

lemma w_nonneg (k s : ℕ) : 0 ≤ w k s := by unfold w; positivity

lemma w_le_one {k : ℕ} (hk : 1 ≤ k) (s : ℕ) : w k s ≤ 1 := by
  unfold w
  have : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_one this]; exact_mod_cast Nat.sub_le k s

lemma w_zero {k : ℕ} (hk : 1 ≤ k) : w k 0 = 1 := by
  unfold w
  have : (k : ℝ) ≠ 0 := by have : (0 : ℝ) < k := by exact_mod_cast hk
                           exact this.ne'
  simp [this]

lemma w_anti (k : ℕ) {s s' : ℕ} (h : s ≤ s') : w k s' ≤ w k s := by
  unfold w
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le_sub_left h k) (by positivity)

lemma w_succ (k : ℕ) {s t : ℕ} (hst : s ≤ t) : w k s * f k (t + 1) ≤ w k (s + 1) := by
  rcases le_or_gt k (t + 1) with h | h
  · have : f k (t + 1) = 0 := by simp [f, Nat.sub_eq_zero_of_le h]
    rw [this, mul_zero]; exact w_nonneg _ _
  · unfold w f
    have e1 : ((k - s : ℕ) : ℝ) = k - s := by rw [Nat.cast_sub (by omega)]
    have e2 : ((k - (s + 1) : ℕ) : ℝ) = k - s - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    have e3 : ((k - (t + 1) : ℕ) : ℝ) = k - t - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e1, e2, e3]
    have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
    have ht : (t : ℝ) + 1 < k := by exact_mod_cast h
    rw [div_mul_div_comm, div_le_div_iff₀ (by nlinarith) hk]
    nlinarith

lemma ψ_nonneg (k r n t : ℕ) : 0 ≤ ψ k r n t :=
  Finset.prod_nonneg fun u _ => pow_nonneg (f_nonneg k u) _

lemma ψ_le_one (k r n t : ℕ) : ψ k r n t ≤ 1 :=
  Finset.prod_le_one₀ (fun u _ => pow_nonneg (f_nonneg k u) _)
    fun u _ => pow_le_one₀ (f_nonneg k u) (f_le_one k u)

lemma ψ_succ {k r n t : ℕ} (h : t + 1 ≤ r) :
    ψ k r n t = f k (t + 1) ^ (n - 1) * ψ k r n (t + 1) := by
  unfold ψ
  have : Finset.Ioc t r = insert (t + 1) (Finset.Ioc (t + 1) r) := by ext u; simp; omega
  rw [this, Finset.prod_insert (by simp)]

lemma ψ_zero (k r n : ℕ) (hk : 1 ≤ k) : ψ k r n 0 = (((k - r : ℕ) : ℝ) / k) ^ (n - 1) := by
  unfold ψ
  rw [Finset.prod_pow]
  congr 1
  induction r with
  | zero =>
    simp
    have : (k : ℝ) ≠ 0 := by have : (0 : ℝ) < k := by exact_mod_cast hk
                             exact this.ne'
    simp [this]
  | succ r ih =>
    rw [Finset.prod_Ioc_succ_top (Nat.zero_le r), ih]
    have hk0 : (k : ℝ) ≠ 0 := by have : (0 : ℝ) < k := by exact_mod_cast hk
                                 exact this.ne'
    unfold f
    rcases le_or_gt k r with h | h
    · simp [Nat.sub_eq_zero_of_le h, Nat.sub_eq_zero_of_le (show k ≤ r + 1 by omega)]
    · have : ((k - (r + 1) : ℕ) : ℝ) + 1 = ((k - r : ℕ) : ℝ) := by
        rw [show k - r = k - (r + 1) + 1 by omega]; push_cast; ring
      rw [this]
      have : ((k - r : ℕ) : ℝ) ≠ 0 := by
        have : 0 < k - r := by omega
        exact_mod_cast this.ne'
      field_simp

/-! ### The potential -/

section Potential

variable (Pi : P → L → Prop) (k r : ℕ)

/-- Number of spoiled preamble iterations of the current invocation of `q` (completed ones, plus
the current one if it already overlaps a program random step). -/
noncomputable def spc (q : P) (lk : LK L) (c : ℕ) : ℕ :=
  lk.res.countP (fun e => e.2) + if lk.ph = .pre ∧ curSp Pi q lk c then 1 else 0

/-- The factor of process `q`: the probability that its pending object random step will pick a
clean iteration, if no further iteration gets spoiled. -/
noncomputable def fac (q : P) (b : Bool) (lk : LK L) (c : ℕ) : ℝ :=
  if b = true ∧ lk.ph ≠ .tail then w k (spc Pi q lk c) else 1

/-- The potential: a lower bound on the probability of `X` from a configuration. -/
noncomputable def Φ [Fintype P] {M : Type} (sk : Cfg P C (LK L) M) : ℝ :=
  if ∃ q, (sk.lo q).xbad = true then 0 else
    (∏ q, fac Pi k q (sk.busy q) (sk.lo q) sk.coins) * ψ k r (Fintype.card P) sk.coins

/-- Every process has at most `coins` spoiled iterations. -/
def InvSp {M : Type} (sk : Cfg P C (LK L) M) : Prop :=
  ∀ q, sk.busy q = true → (sk.lo q).ph ≠ .tail → spc Pi q (sk.lo q) sk.coins ≤ sk.coins

variable {Pi k r}

omit [DecidableEq P] in
lemma spc_succ (q : P) (lk : LK L) (c : ℕ) : spc Pi q lk (c + 1) ≤ spc Pi q lk c + 1 := by
  unfold spc; split_ifs <;> omega

omit [DecidableEq P] in
lemma fac_nonneg (q : P) (b : Bool) (lk : LK L) (c : ℕ) : 0 ≤ fac Pi k q b lk c := by
  unfold fac; split_ifs
  · exact w_nonneg _ _
  · exact zero_le_one

omit [DecidableEq P] in
lemma fac_le_one (hk : 1 ≤ k) (q : P) (b : Bool) (lk : LK L) (c : ℕ) : fac Pi k q b lk c ≤ 1 := by
  unfold fac; split_ifs
  · exact w_le_one hk _
  · exact le_rfl

variable [Fintype P] {M : Type}

omit [DecidableEq P] in
lemma Φ_nonneg (sk : Cfg P C (LK L) M) : 0 ≤ Φ Pi k r sk := by
  unfold Φ; split_ifs
  · exact le_rfl
  · exact mul_nonneg (Finset.prod_nonneg fun q _ => fac_nonneg _ _ _ _) (ψ_nonneg _ _ _ _)

omit [DecidableEq P] in
lemma Φ_le_one (hk : 1 ≤ k) (sk : Cfg P C (LK L) M) : Φ Pi k r sk ≤ 1 := by
  unfold Φ; split_ifs
  · exact zero_le_one
  · calc _ ≤ (1 : ℝ) * 1 := mul_le_mul (Finset.prod_le_one₀ (fun q _ => fac_nonneg _ _ _ _)
          fun q _ => fac_le_one hk _ _ _ _) (ψ_le_one _ _ _ _) (ψ_nonneg _ _ _ _) zero_le_one
      _ = 1 := one_mul 1

/-- A move that changes only process `p` (not its `xbad` flag) and does not decrease its factor
does not decrease the potential. -/
lemma Φ_upd {sk sk' : Cfg P C (LK L) M} (p : P) (hc : sk'.coins = sk.coins)
    (hq : ∀ q, q ≠ p → sk'.busy q = sk.busy q ∧ sk'.lo q = sk.lo q)
    (hx : (sk'.lo p).xbad = (sk.lo p).xbad)
    (hf : fac Pi k p (sk.busy p) (sk.lo p) sk.coins ≤ fac Pi k p (sk'.busy p) (sk'.lo p) sk'.coins)
    (hs : InvSp Pi sk)
    (hsp : sk'.busy p = true → (sk'.lo p).ph ≠ .tail → spc Pi p (sk'.lo p) sk'.coins ≤ sk'.coins) :
    InvSp Pi sk' ∧ Φ Pi k r sk ≤ Φ Pi k r sk' := by
  refine ⟨fun q => ?_, ?_⟩
  · by_cases hqp : q = p
    · subst hqp; exact hsp
    · rw [(hq q hqp).1, (hq q hqp).2, hc]; exact hs q
  · have hex : (∃ q, (sk'.lo q).xbad = true) ↔ (∃ q, (sk.lo q).xbad = true) := by
      constructor <;> rintro ⟨q, h⟩ <;> refine ⟨q, ?_⟩ <;> by_cases hqp : q = p
      · subst hqp; rwa [← hx]
      · rwa [← (hq q hqp).2]
      · subst hqp; rwa [hx]
      · rwa [(hq q hqp).2]
    unfold Φ
    by_cases h1 : ∃ q, (sk.lo q).xbad = true
    · simp only [h1, hex.2 h1, ↓reduceIte, le_refl]
    · have h2 : ¬ ∃ q, (sk'.lo q).xbad = true := fun h => h1 (hex.1 h)
      simp only [h1, h2, ↓reduceIte, hc]
      refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ (fun q _ => fac_nonneg _ _ _ _)
        fun q _ => ?_) (ψ_nonneg _ _ _ _)
      by_cases hqp : q = p
      · subst hqp; rw [hc] at hf; exact hf
      · rw [(hq q hqp).1, (hq q hqp).2]

lemma prod_ite_ne (p : P) (x : ℝ) :
    ∏ q, (if q = p then 1 else x) = x ^ (Fintype.card P - 1) := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ]

/-- A program random step of an idle process `p` does not decrease the potential. -/
lemma Φ_coin {sk sk' : Cfg P C (LK L) M} (p : P) (hb : sk.busy p = false)
    (hbusy : sk'.busy = sk.busy) (hlo : sk'.lo = sk.lo) (hc : sk'.coins = sk.coins + 1)
    (hr : sk.coins + 1 ≤ r) (hs : InvSp Pi sk) : InvSp Pi sk' ∧ Φ Pi k r sk ≤ Φ Pi k r sk' := by
  refine ⟨fun q hqb hqph => ?_, ?_⟩
  · rw [hbusy] at hqb; rw [hlo] at hqph ⊢; rw [hc]
    have := hs q hqb hqph
    have := spc_succ (Pi := Pi) q (sk.lo q) sk.coins
    omega
  · unfold Φ; rw [hlo, hbusy, hc]
    split_ifs
    · exact le_rfl
    · rw [ψ_succ hr, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (ψ_nonneg _ _ _ _)
      rw [← prod_ite_ne p, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀ (fun q _ => ?_) fun q _ => ?_
      · split_ifs
        · simpa using fac_nonneg _ _ _ _
        · exact mul_nonneg (fac_nonneg _ _ _ _) (f_nonneg _ _)
      · by_cases hqp : q = p
        · subst hqp; simp [fac, hb]
        · simp only [hqp, ite_false]
          unfold fac
          split_ifs with h
          · calc w k (spc Pi q (sk.lo q) sk.coins) * f k (sk.coins + 1)
                ≤ w k (spc Pi q (sk.lo q) sk.coins + 1) := w_succ k (hs q h.1 h.2)
              _ ≤ w k (spc Pi q (sk.lo q) (sk.coins + 1)) := w_anti k (spc_succ _ _ _)
          · simpa using f_le_one k (sk.coins + 1)

lemma sum_clean (d : L × Bool) :
    ∀ l : List (L × Bool), ∑ j ∈ Finset.range l.length, (if (l.getD j d).2 = true then (0 : ℝ) else 1)
      = (l.length : ℝ) - (l.countP (fun e => e.2) : ℝ)
  | [] => by simp
  | a :: l => by
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [sum_clean d l]
    cases h : a.2 <;> simp [h]; ring

/-- The local state after the object random step chose iteration `j`. -/
def chosen (lk : LK L) (j : ℕ) : LK L :=
  { lk with cur := (resAt lk j).1, ph := .tail, xbad := lk.xbad || (resAt lk j).2 }

/-- An object random step averages the potential exactly. -/
lemma Φ_obj (hk : 1 ≤ k) (sk : Cfg P C (LK L) M) (p : P) (lk : LK L) (hlk : sk.lo p = lk)
    (hb : sk.busy p = true) (hph : lk.ph = .choose) (hlen : lk.res.length = k) :
    (∑ j : Fin (k - 1 + 1),
        (1 - Φ Pi k r { sk with lo := Function.update sk.lo p (chosen lk j) })) /
      (((k - 1 : ℕ) : ℝ) + 1) ≤ 1 - Φ Pi k r sk := by
  have hm1 : (((k - 1 : ℕ) : ℝ) + 1) = k := by
    rw [Nat.cast_sub hk]; push_cast; ring
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  rw [hm1]
  by_cases hx : ∃ q, (sk.lo q).xbad = true
  · have h0 : Φ Pi k r sk = 0 := by simp [Φ, hx]
    rw [h0, div_le_iff₀ hkpos]
    calc ∑ j : Fin (k - 1 + 1), (1 - Φ Pi k r _) ≤ ∑ _j : Fin (k - 1 + 1), (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => sub_le_self _ (Φ_nonneg _)
      _ = (1 - 0) * k := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
            sub_zero, one_mul, Nat.cast_add, Nat.cast_one, hm1]
  · push Not at hx
    set Y := ∏ q ∈ Finset.univ.erase p, fac Pi k q (sk.busy q) (sk.lo q) sk.coins with hY
    set Ψ := ψ k r (Fintype.card P) sk.coins
    have hΦ : Φ Pi k r sk = w k (lk.res.countP (fun e => e.2)) * Y * Ψ := by
      have hfp : fac Pi k p (sk.busy p) (sk.lo p) sk.coins = w k (lk.res.countP (fun e => e.2)) := by
        simp [fac, hb, hlk, hph, spc]
      simp only [Φ, hx, Bool.false_eq_true, exists_false, ite_false]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), hfp]
    have hΦj : ∀ j : Fin (k - 1 + 1),
        Φ Pi k r { sk with lo := Function.update sk.lo p (chosen lk j) } =
        (if (resAt lk j).2 = true then 0 else 1) * (Y * Ψ) := by
      intro j
      have hex : (∃ q, (Function.update sk.lo p (chosen lk j) q).xbad = true) ↔
          (resAt lk j).2 = true := by
        constructor
        · rintro ⟨q, hq⟩
          by_cases hqp : q = p
          · subst hqp; simpa [chosen, ← hlk, hx q] using hq
          · simp [Function.update_of_ne hqp, hx q] at hq
        · intro h; exact ⟨p, by simp [chosen, h]⟩
      simp only [Φ]
      rw [if_congr hex rfl rfl]
      split_ifs with h
      · simp
      · rw [one_mul, ← Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
        simp only [Function.update_self, fac, chosen, ne_eq, not_true_eq_false, and_false,
          ite_false, one_mul]
        congr 1
        exact Finset.prod_congr rfl fun q hq => by
          simp [fac, Function.update_of_ne (Finset.ne_of_mem_erase hq)]
    simp only [hΦj]
    have hcnt : ∑ j : Fin (k - 1 + 1), (if (resAt lk j).2 = true then (0 : ℝ) else 1) =
        (k : ℝ) - (lk.res.countP (fun e => e.2) : ℝ) := by
      rw [Fin.sum_univ_eq_sum_range (fun j => if (resAt lk j).2 = true then (0 : ℝ) else 1),
        show k - 1 + 1 = lk.res.length by omega]
      conv_rhs => rw [← hlen]
      exact sum_clean (lk.cur, false) lk.res
    have hle : lk.res.countP (fun e => e.2) ≤ k := hlen ▸ List.countP_le_length
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, hcnt, hΦ, w, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub hle]
    have : ((k - 1 + 1 : ℕ) : ℝ) = k := by rw [← hm1]; push_cast; ring
    rw [this]
    field_simp
    ring_nf
    exact le_rfl

end Potential

/-! ### The moves of `P(O^k)` -/

section Moves

variable {Pr : Program P A C} {I : Impl A Bs P L} {Pi : P → L → Prop} {k r : ℕ} [Fintype P]

/-- Deterministic moves preserve `InvSp` and do not decrease the potential. -/
theorem det_step (hk : 1 ≤ k) {sk sk' : Cfg P C (LK L) (Mem Bs)} {p : P}
    (hinv : InvK Pr I Pi k sk) (hs : InvSp Pi sk)
    (hm : (sys Pr (iterSem I Pi k)).move sk p = .det sk') :
    InvSp Pi sk' ∧ Φ Pi k r sk ≤ Φ Pi k r sk' := by
  cases hb : sk.busy p
  · cases hn : Pr.next p (sk.cl p) with
    | loc c => rw [move_loc Pr _ sk p hb hn] at hm; cases hm; exact ⟨hs, le_rfl⟩
    | rnd m g => rw [move_rnd Pr _ sk p hb hn] at hm; cases hm
    | done => rw [move_done Pr _ sk p hb hn] at hm; cases hm
    | call o κ =>
      rw [move_call_inl Pr _ sk p hb hn (iter_call I Pi k p (sk.lo p) o sk.mem sk.coins)] at hm
      cases hm
      refine Φ_upd p rfl (fun q hq => by simp [Function.update_of_ne hq]) (by simp) ?_ hs ?_
      · simp [fac, spc, curSp, hb, w_zero hk]
      · intro _ _; simp [spc, curSp]
  · obtain ⟨o, κ, hn, -⟩ := (hinv p).call hb
    have hip := hinv p
    cases hph : (sk.lo p).ph with
    | choose => rw [move_orand Pr _ sk p hb (iter_act_choose hph)] at hm; cases hm
    | tail =>
      cases ha : I.act p (sk.lo p).cur with
      | access i o' κ' =>
        rw [move_step Pr _ sk p hb (iter_act_tail_access hph ha)] at hm; cases hm
        refine Φ_upd p rfl (fun q hq => by simp [Function.update_of_ne hq]) (by simp) ?_ hs ?_
        · simp [fac, hph]
        · intro _ h; simp [hph] at h
      | ret r' l' =>
        rw [move_ret Pr _ sk p hb (iter_act_tail_ret hph ha) hn] at hm; cases hm
        refine Φ_upd p rfl (fun q hq => by simp [Function.update_of_ne hq]) (by simp) ?_ hs ?_
        · simp [fac, hph]
        · intro h; simp at h
    | pre =>
      by_cases hpi : Pi p (sk.lo p).cur
      · have hsp := hip.pre_sp hb hph hpi
        cases ha : I.act p (sk.lo p).cur with
        | ret r' l' =>
          rw [move_step Pr _ sk p hb (iter_act_pre_ret hph hpi ha)] at hm; cases hm
          refine Φ_upd p rfl (fun q hq => by simp [Function.update_of_ne hq]) (by simp)
            (by simp) hs (fun h1 h2 => by simpa using hs p (by simpa using h1) (by simpa using h2))
        | access i o' κ' =>
          rw [move_step Pr _ sk p hb (iter_act_pre_access hph hpi ha)] at hm; cases hm
          set l1 := κ' ((Bs i).δ (sk.mem i) o').2
          have hspc : spc Pi p
              { sk.lo p with cur := l1,
                             sp := if Pi p l1 then (sk.lo p).sp
                               else decide (sk.coins ≠ (sk.lo p).sc) } sk.coins =
              spc Pi p (sk.lo p) sk.coins := by
            by_cases hpi' : Pi p l1 <;> simp [spc, curSp, hpi, hpi', hsp, hph]
          have h0 := hs p hb (by simp [hph])
          refine Φ_upd p rfl (fun q hq => by simp [Function.update_of_ne hq]) (by simp) ?_ hs ?_
          · simp only [fac, Function.update_self]; rw [hspc]
          · intro _ _; simp only [Function.update_self]; rw [hspc]; exact h0
      · have h0 := hs p hb (by simp [hph])
        by_cases hlt : (sk.lo p).res.length + 1 < k
        · rw [move_step Pr _ sk p hb (iter_act_restart hph hpi hlt)] at hm; cases hm
          have hspc : spc Pi p
              { sk.lo p with cur := (sk.lo p).base,
                             res := (sk.lo p).res ++ [((sk.lo p).cur, (sk.lo p).sp)],
                             sc := sk.coins, sp := false }
              sk.coins = spc Pi p (sk.lo p) sk.coins := by
            cases hs' : (sk.lo p).sp <;> simp [spc, curSp, hpi, hph, hs', List.countP_append]
          refine Φ_upd p rfl (fun q hq => by simp [Function.update_of_ne hq]) (by simp) ?_ hs ?_
          · simp only [fac, Function.update_self]; rw [hspc]
          · intro _ _; simp only [Function.update_self]; rw [hspc]; exact h0
        · rw [move_step Pr _ sk p hb (iter_act_tochoose hph hpi hlt)] at hm; cases hm
          have hspc : spc Pi p
              { sk.lo p with res := (sk.lo p).res ++ [((sk.lo p).cur, (sk.lo p).sp)],
                             ph := .choose }
              sk.coins = spc Pi p (sk.lo p) sk.coins := by
            cases hs' : (sk.lo p).sp <;> simp [spc, curSp, hpi, hph, hs', List.countP_append]
          refine Φ_upd p rfl (fun q hq => by simp [Function.update_of_ne hq]) (by simp) ?_ hs ?_
          · simp only [fac, Function.update_self]; rw [hspc]; simp [hb, hph]
          · intro _ _; simp only [Function.update_self]; rw [hspc]; exact h0

end Moves

/-! ### Lemma 4.5 -/

section Main

variable {Pr : Program P A C} {I : Impl A Bs P L} {Pi : P → L → Prop} {k r : ℕ} [Fintype P]
  [Nonempty P]

/-- Reachable configurations of `P(O^k)` have at most `r` program random steps. -/
lemma coins_le (hEF : EffectFree I Pi) (hWF : PreambleWF I Pi) (hk : 1 ≤ k)
    (hr : AtMostRandom Pr (implSem I Pi) r) {sk : Cfg P C (LK L) (Mem Bs)}
    (h : (sys Pr (iterSem I Pi k)).Reach (initCfg Pr (iterSem I Pi k)) sk) : sk.coins ≤ r := by
  obtain ⟨-, hJ⟩ := reach_rel hEF hWF hk h
  obtain ⟨so, hrel, hso⟩ := hJ (fun _ => 0)
  rw [← hrel.coins]; exact hr so hso

lemma avg_le {m : ℕ} {a : Fin (m + 1) → ℝ} {b : ℝ} (h : ∀ i, a i ≤ b) :
    (∑ i, a i) / (m + 1) ≤ b := by
  rw [div_le_iff₀ (by positivity)]
  calc ∑ i, a i ≤ ∑ _i : Fin (m + 1), b := Finset.sum_le_sum fun i _ => h i
    _ = b * (m + 1) := by simp; ring

/-- **Lemma 4.5** of [Attiya–Enea–Welch, PODC 2022], in the form: against every strong
adversary, `Prob[¬X] ≤ 1 - (max{0, k - r} / k)^(n - 1)`, where `X` is the event that every object
random step of `P(O^k)` chooses a preamble iteration that did not overlap a program random step,
`n` is the number of processes and `r` bounds the number of program random steps of `P(O)`. -/
theorem optNX_le (hEF : EffectFree I Pi) (hWF : PreambleWF I Pi) (hk : 1 ≤ k)
    (hr : AtMostRandom Pr (implSem I Pi) r) :
    (sys Pr (iterSem I Pi k)).opt payNX (initCfg Pr (iterSem I Pi k)) ≤
      1 - (((k - r : ℕ) : ℝ) / k) ^ (Fintype.card P - 1) := by
  have hinit : Φ Pi k r (initCfg Pr (iterSem I Pi k)) =
      (((k - r : ℕ) : ℝ) / k) ^ (Fintype.card P - 1) := by
    rw [← ψ_zero k r _ hk]
    simp [Φ, initCfg, iterSem, fac]
  rw [← hinit]
  refine MDP.opt_le_of_super (fun sk x =>
      (sys Pr (iterSem I Pi k)).Reach (initCfg Pr (iterSem I Pi k)) sk ∧ InvSp Pi sk ∧
        x = 1 - Φ Pi k r sk) ?_ ?_ ?_ ?_ ⟨.refl _, ?_, rfl⟩
  · rintro s x ⟨-, -, rfl⟩; linarith [Φ_le_one (Pi := Pi) (r := r) hk s]
  · rintro s x ⟨-, -, rfl⟩ -
    unfold payNX; split_ifs with h
    · simp [Φ, h]
    · linarith [Φ_le_one (Pi := Pi) (r := r) hk s]
  · rintro s x q s' ⟨hreach, hs, rfl⟩ hm
    obtain ⟨hinv, -⟩ := reach_rel hEF hWF hk hreach
    obtain ⟨hs', hΦ⟩ := det_step (r := r) hk hinv hs hm
    exact ⟨_, by linarith, hreach.trans (.det q hm (.refl _)), hs', rfl⟩
  · rintro s x q m g ⟨hreach, hs, rfl⟩ hm
    obtain ⟨hinv, -⟩ := reach_rel hEF hWF hk hreach
    have hreach' : ∀ i, (sys Pr (iterSem I Pi k)).Reach (initCfg Pr (iterSem I Pi k)) (g i) :=
      fun i => hreach.trans (.rand q m g i hm (.refl _))
    cases hb : s.busy q
    · cases hn : Pr.next q (s.cl q) with
      | loc c => rw [move_loc Pr _ s q hb hn] at hm; cases hm
      | done => rw [move_done Pr _ s q hb hn] at hm; cases hm
      | call o κ =>
        rw [move_call_inl Pr _ s q hb hn (iter_call I Pi k q (s.lo q) o s.mem s.coins)] at hm
        cases hm
      | rnd m' g0 =>
        have hcs : ∀ i, (g i).busy = s.busy ∧ (g i).lo = s.lo ∧ (g i).coins = s.coins + 1 := by
          rw [move_rnd Pr _ s q hb hn] at hm; cases hm; intro i; simp
        have key : ∀ i, InvSp Pi (g i) ∧ Φ Pi k r s ≤ Φ Pi k r (g i) := fun i =>
          Φ_coin q hb (hcs i).1 (hcs i).2.1 (hcs i).2.2
            (by have := coins_le hEF hWF hk hr (hreach' i); rwa [(hcs i).2.2] at this) hs
        exact ⟨fun i => 1 - Φ Pi k r (g i), avg_le fun i => by linarith [(key i).2],
          fun i => ⟨hreach' i, (key i).1, rfl⟩⟩
    · obtain ⟨rfl, hph, -⟩ := step_rand_obj hk hinv hb hm
      have hlen := (hinv q).choose_len hb hph
      have hg : g = fun j => { s with lo := Function.update s.lo q (chosen (s.lo q) j) } := by
        rw [move_orand Pr _ s q hb (iter_act_choose hph)] at hm; cases hm; rfl
      have hsg : ∀ j, InvSp Pi (g j) := by
        intro j q' hb' hph'
        rw [hg] at hb' hph' ⊢
        by_cases hqq : q' = q
        · subst hqq; simp [chosen] at hph'
        · simp only [Function.update_of_ne hqq] at hb' hph' ⊢
          exact hs q' hb' hph'
      refine ⟨fun j => 1 - Φ Pi k r (g j), ?_, fun j => ⟨hreach' j, hsg j, rfl⟩⟩
      rw [hg]; exact Φ_obj hk s q (s.lo q) rfl hb hph hlen
  · intro q hq; simp [initCfg, iterSem] at hq

end Main

end Clean

end Podc.BluntingAdversary
