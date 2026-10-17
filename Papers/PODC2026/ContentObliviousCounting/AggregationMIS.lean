import Papers.PODC2026.ContentObliviousCounting.SimulationGeneric

/-!
# Cole–Vishkin MIS and one aggregation round on a virtual ring (Lemma 26)

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026, Lemma 26 and step 3 of the proof of Theorem 1.

The synchronous ring algorithm `misAlg op2` (a `SyncAlg`, to be run by the simulator of
Theorem 14 on the virtual ring of the active processes) does, with `lam` = common bound on the
bit length of the IDs:
* rounds `0 … lam-1` (*Cole–Vishkin colour reduction*): every node sends its colour, written with
  `wd lam r` bits, to its clockwise neighbour; a node of colour `c` whose counter-clockwise
  neighbour has colour `p ≠ c` takes the colour `2i + bit_i(c)`, `i` = lowest bit where `c` and
  `p` differ. Colours start as the IDs (`< 2^lam`); widths follow `w ↦ size (2w - 1)`, so after
  `lam` rounds the colouring is proper with colours `< 8`;
* rounds `lam … lam+7` (*MIS*): the leader starts in the MIS; in round `lam + i` the nodes of
  colour `i` that have no neighbour in the MIS join it (1-bit messages);
* round `lam + 8`: neighbours exchange their MIS bit;
* round `lam + 9` (*aggregation*): a node outside the MIS sends `true :: w` to its clockwise
  neighbour if that neighbour is in the MIS, otherwise to its counter-clockwise neighbour; a node
  in the MIS combines its value `w` with the received values (`op2` on encoded values).

The run is computed explicitly (`run_cv`, `run_mis`, `run_ex`, `run_agg`); the combinatorial
properties hold on any virtual ring with at least two nodes (`RingAx`).
-/

namespace Podc.ContentOblivious.Aggregation

open Cslib.ContentOblivious Simulation Finset

/-- Local state of the MIS/aggregation algorithm. -/
structure MState where
  lead : Bool
  lam : ℕ
  /-- Round counter. -/
  r : ℕ
  /-- Current colour. -/
  col : ℕ
  /-- Membership in the MIS. -/
  mis : Bool
  /-- The clockwise neighbour is in the MIS. -/
  cwIn : Bool
  /-- The counter-clockwise neighbour is in the MIS. -/
  ccwIn : Bool
  /-- The (encoded) partial aggregate. -/
  w : List Bool
  deriving Inhabited

/-- `MState` as a product, for the `Encodable` instance. -/
def MState.equiv : MState ≃ Bool × ℕ × ℕ × ℕ × Bool × Bool × Bool × List Bool where
  toFun s := (s.lead, s.lam, s.r, s.col, s.mis, s.cwIn, s.ccwIn, s.w)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Encodable MState := Encodable.ofEquiv _ MState.equiv

/-- The `w` lowest bits of `c`. -/
def bitsOf (w c : ℕ) : List Bool := (List.range w).map c.testBit

/-- The lowest bit position `< w` where `c` differs from the bit string `a`. -/
def lowDiff (w c : ℕ) (a : List Bool) : ℕ :=
  if h : ∃ i, i < w ∧ c.testBit i ≠ a.getD i false then Nat.find h else 0

/-- One Cole–Vishkin colour-reduction step. -/
def cvStep (w c : ℕ) (a : List Bool) : ℕ := 2 * lowDiff w c a + (c.testBit (lowDiff w c a)).toNat

/-- Width of the colours after one reduction step from colours `< 2^w`. -/
def nextW (w : ℕ) : ℕ := Nat.size (2 * w - 1)

/-- Width of the colours before round `r`. -/
def wd (lam : ℕ) : ℕ → ℕ
  | 0 => lam
  | r + 1 => nextW (wd lam r)

/-- Combination at a cluster centre of its value `w` with the values received from the
counter-clockwise (`a`) and the clockwise (`b`) neighbours (`[]` = nothing received). -/
def combine (op2 : List Bool → List Bool → List Bool) (a b w : List Bool) : List Bool :=
  let w1 := if b = [] then w else op2 w b.tail
  if a = [] then w1 else op2 a.tail w1

/-- The synchronous MIS + aggregation algorithm. -/
def misAlg (op2 : List Bool → List Bool → List Bool) : SyncAlg MState where
  msg s :=
    if s.r < s.lam then (bitsOf (wd s.lam s.r) s.col, [])
    else if s.r < s.lam + 9 then ([s.mis], [s.mis])
    else if s.r = s.lam + 9 then
      (if s.mis then ([], []) else if s.cwIn then (true :: s.w, []) else ([], true :: s.w))
    else ([], [])
  step s a b :=
    if s.r < s.lam then { s with col := cvStep (wd s.lam s.r) s.col a, r := s.r + 1 }
    else if s.r < s.lam + 8 then
      { s with mis := s.mis || (decide (s.col = s.r - s.lam) && !(a.headD false) &&
          !(b.headD false)), r := s.r + 1 }
    else if s.r = s.lam + 8 then
      { s with ccwIn := a.headD false, cwIn := b.headD false, r := s.r + 1 }
    else if s.r = s.lam + 9 then
      { s with w := if s.mis then combine op2 a b s.w else s.w, r := s.r + 1 }
    else { s with r := s.r + 1 }

/-- Initial state of a phase. -/
def initSt (lam : ℕ) (lead : Bool) (id : ℕ) (w : List Bool) : MState :=
  ⟨lead, lam, 0, id, lead, false, false, w⟩

/-- Number of rounds of the algorithm. -/
def rounds (lam : ℕ) : ℕ := lam + 10

/-! ### The explicit run -/

section run

variable {V : Type*} (op2 : List Bool → List Bool → List Bool) (nxt prv : V → V)
  (lam : ℕ) (lead : V → Bool) (id : V → ℕ) (w : V → List Bool)

/-- Colours during the colour reduction. -/
def colAt : ℕ → V → ℕ
  | 0 => id
  | t + 1 => fun v => cvStep (wd lam t) (colAt t v) (bitsOf (wd lam t) (colAt t (prv v)))

/-- MIS membership after the MIS rounds `lam … lam+i-1`. -/
def misAt : ℕ → V → Bool
  | 0 => lead
  | i + 1 => fun v => misAt i v || (decide (colAt prv lam id lam v = i) && !misAt i (prv v) &&
      !misAt i (nxt v))

/-- The synchronous run of `misAlg`. -/
abbrev runM := (misAlg op2).run nxt prv (fun v => initSt lam (lead v) (id v) (w v))

lemma runM_succ (t : ℕ) (v : V) :
    runM op2 nxt prv lam lead id w (t + 1) v =
      (misAlg op2).step (runM op2 nxt prv lam lead id w t v)
        ((misAlg op2).msg (runM op2 nxt prv lam lead id w t (prv v))).1
        ((misAlg op2).msg (runM op2 nxt prv lam lead id w t (nxt v))).2 := rfl

lemma run_cv {t : ℕ} (ht : t ≤ lam) (v : V) :
    runM op2 nxt prv lam lead id w t v =
      ⟨lead v, lam, t, colAt prv lam id t v, lead v, false, false, w v⟩ := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    simp only [runM, SyncAlg.run] at ih ⊢
    rw [ih (by omega), ih (by omega), ih (by omega)]
    simp [misAlg, show t < lam by omega, colAt]

lemma run_mis {i : ℕ} (hi : i ≤ 8) (v : V) :
    runM op2 nxt prv lam lead id w (lam + i) v =
      ⟨lead v, lam, lam + i, colAt prv lam id lam v, misAt nxt prv lam lead id i v, false, false,
        w v⟩ := by
  induction i generalizing v with
  | zero => exact run_cv op2 nxt prv lam lead id w le_rfl v
  | succ i ih =>
    rw [show lam + (i + 1) = lam + i + 1 by omega, runM_succ, ih (by omega), ih (by omega),
      ih (by omega)]
    simp [misAlg, show lam + i < lam + 9 by omega, show lam + i < lam + 8 by omega, misAt,
      Bool.and_assoc]

lemma run_ex (v : V) :
    runM op2 nxt prv lam lead id w (lam + 9) v =
      ⟨lead v, lam, lam + 9, colAt prv lam id lam v, misAt nxt prv lam lead id 8 v,
        misAt nxt prv lam lead id 8 (nxt v), misAt nxt prv lam lead id 8 (prv v), w v⟩ := by
  have h := run_mis op2 nxt prv lam lead id w (i := 8) le_rfl
  rw [show lam + 9 = lam + 8 + 1 by omega, runM_succ, h, h, h]
  simp [misAlg]

/-- Message of node `v` in the aggregation round. -/
def aggMsg (m cw : Bool) (wv : List Bool) : List Bool × List Bool :=
  if m then ([], []) else if cw then (true :: wv, []) else ([], true :: wv)

lemma run_agg (v : V) :
    runM op2 nxt prv lam lead id w (rounds lam) v =
      ⟨lead v, lam, lam + 10, colAt prv lam id lam v, misAt nxt prv lam lead id 8 v,
        misAt nxt prv lam lead id 8 (nxt v), misAt nxt prv lam lead id 8 (prv v),
        if misAt nxt prv lam lead id 8 v then
          combine op2 (aggMsg (misAt nxt prv lam lead id 8 (prv v))
              (misAt nxt prv lam lead id 8 (nxt (prv v))) (w (prv v))).1
            (aggMsg (misAt nxt prv lam lead id 8 (nxt v))
              (misAt nxt prv lam lead id 8 (nxt (nxt v))) (w (nxt v))).2 (w v)
        else w v⟩ := by
  have h := run_ex op2 nxt prv lam lead id w
  rw [rounds, show lam + 10 = lam + 9 + 1 by omega, runM_succ, h, h, h]
  simp [misAlg, aggMsg]

/-- Message lengths of the run: `wd lam r` bits in the colour reduction, one bit in the MIS
rounds, at most `1 + |w|` bits in the aggregation round. -/
lemma msg_len_le {r : ℕ} (hr : r < rounds lam) (v : V) :
    max ((misAlg op2).msg (runM op2 nxt prv lam lead id w r v)).1.length
      ((misAlg op2).msg (runM op2 nxt prv lam lead id w r v)).2.length ≤
      if r < lam then wd lam r else if r < lam + 9 then 1 else 1 + (w v).length := by
  rw [rounds] at hr
  rcases Nat.lt_or_ge r lam with h1 | h1
  · rw [run_cv op2 nxt prv lam lead id w h1.le]
    simp [misAlg, h1, bitsOf]
  rcases Nat.lt_or_ge r (lam + 9) with h2 | h2
  · obtain ⟨i, rfl⟩ : ∃ i, r = lam + i := ⟨r - lam, by omega⟩
    rw [run_mis op2 nxt prv lam lead id w (by omega)]
    simp [misAlg, h2]
  · have : r = lam + 9 := by omega
    subst this
    rw [run_ex]
    simp only [misAlg]
    split_ifs <;> simp_all

end run

/-! ### Cole–Vishkin colour reduction -/

section cv

lemma bitsOf_getD (w p i : ℕ) : (bitsOf w p).getD i false = (decide (i < w) && p.testBit i) := by
  unfold bitsOf
  by_cases h : i < w <;> simp [h, List.getD_eq_getElem?_getD]

lemma testBit_of_ge {w c i : ℕ} (hc : c < 2 ^ w) (hi : w ≤ i) : c.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hi))

lemma lowDiff_spec {w c p : ℕ} (hc : c < 2 ^ w) (hp : p < 2 ^ w) (hne : c ≠ p) :
    lowDiff w c (bitsOf w p) < w ∧
      c.testBit (lowDiff w c (bitsOf w p)) ≠ p.testBit (lowDiff w c (bitsOf w p)) := by
  have hex : ∃ i, i < w ∧ c.testBit i ≠ (bitsOf w p).getD i false := by
    by_contra hcon
    push Not at hcon
    apply hne
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < w
    · have := hcon i hi; rw [bitsOf_getD] at this; simpa [hi] using this
    · rw [testBit_of_ge hc (by omega), testBit_of_ge hp (by omega)]
  unfold lowDiff
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  rw [bitsOf_getD, decide_eq_true h1, Bool.true_and] at h2
  exact ⟨h1, h2⟩

lemma cvStep_lt {w c p : ℕ} (hc : c < 2 ^ w) (hp : p < 2 ^ w) (hne : c ≠ p) :
    cvStep w c (bitsOf w p) < 2 ^ nextW w := by
  obtain ⟨h1, -⟩ := lowDiff_spec hc hp hne
  have hb := Bool.toNat_le (c.testBit (lowDiff w c (bitsOf w p)))
  have : cvStep w c (bitsOf w p) ≤ 2 * w - 1 := by unfold cvStep; omega
  exact lt_of_le_of_lt this (Nat.lt_size_self _)

lemma cvStep_ne {w c p : ℕ} (q : ℕ) (hc : c < 2 ^ w) (hp : p < 2 ^ w) (hcp : c ≠ p) :
    cvStep w c (bitsOf w p) ≠ cvStep w p (bitsOf w q) := by
  obtain ⟨-, h2⟩ := lowDiff_spec hc hp hcp
  unfold cvStep
  intro h
  set i := lowDiff w c (bitsOf w p)
  set j := lowDiff w p (bitsOf w q)
  have hb1 := Bool.toNat_le (c.testBit i)
  have hb2 := Bool.toNat_le (p.testBit j)
  have hij : i = j := by omega
  have hbit : (c.testBit i).toNat = (p.testBit j).toNat := by omega
  rw [← hij] at hbit
  apply h2
  revert hbit; cases c.testBit i <;> cases p.testBit i <;> simp

lemma two_mul_le_pow (w : ℕ) : 2 * w ≤ 2 ^ ((w + 3) / 2) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w 4 with h | h
    · interval_cases w <;> norm_num
    · have := ih (w - 2) (by omega)
      have h4 : 4 ≤ 2 ^ ((w - 2 + 3) / 2) :=
        le_trans (by norm_num)
          (Nat.pow_le_pow_right (by norm_num) (show 2 ≤ (w - 2 + 3) / 2 by omega))
      rw [show (w + 3) / 2 = (w - 2 + 3) / 2 + 1 by omega, pow_succ]
      omega

lemma two_mul_nextW_le (w : ℕ) : 2 * nextW w ≤ w + 3 := by
  have : nextW w ≤ (w + 3) / 2 := by
    unfold nextW; rw [Nat.size_le]
    have := two_mul_le_pow w; have := Nat.one_le_two_pow (n := (w + 3) / 2); omega
  omega

lemma nextW_le_three {w : ℕ} (hw : w ≤ 3) : nextW w ≤ 3 := by
  unfold nextW; rw [Nat.size_le]; norm_num; omega

lemma nextW_lt {w : ℕ} (hw : 4 ≤ w) : nextW w ≤ w - 1 := by
  unfold nextW; rw [Nat.size_le]
  induction w, hw using Nat.le_induction with
  | base => norm_num
  | succ w hw ih =>
    rw [show w + 1 - 1 = (w - 1) + 1 by omega, pow_succ]; omega

lemma wd_succ' (lam r : ℕ) : wd lam (r + 1) = wd (nextW lam) r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [wd, ih]; rfl

lemma wd_le (lam r : ℕ) : wd lam r ≤ max 3 (lam - r) := by
  induction r with
  | zero => simp [wd]
  | succ r ih =>
    rw [wd]
    rcases Nat.lt_or_ge (wd lam r) 4 with h | h
    · have := nextW_le_three (w := wd lam r) (by omega); omega
    · have := nextW_lt h; omega

/-- The total width of the colour-reduction messages: `∑_{r<R} wd lam r ≤ 2 lam + 3 R`. -/
lemma sum_wd_le (R : ℕ) : ∀ lam, ∑ r ∈ range R, wd lam r ≤ 2 * lam + 3 * R := by
  induction R with
  | zero => simp
  | succ R ih =>
    intro lam
    rw [Finset.sum_range_succ']
    simp only [wd_succ']
    have := ih (nextW lam)
    have := two_mul_nextW_le lam
    simp only [wd]
    omega

end cv

/-! ### Properties on a virtual ring -/

/-- The virtual ring axioms on the active nodes (at least two of them). -/
structure RingAx {V : Type*} (act : V → Bool) (nxt prv : V → V) : Prop where
  nxt_act : ∀ v, act v = true → act (nxt v) = true
  prv_act : ∀ v, act v = true → act (prv v) = true
  prv_nxt : ∀ v, act v = true → prv (nxt v) = v
  nxt_prv : ∀ v, act v = true → nxt (prv v) = v
  nxt_ne : ∀ v, act v = true → nxt v ≠ v

section ring

variable {V : Type*} {act : V → Bool} {nxt prv : V → V}
  {lam : ℕ} {lead : V → Bool} {id : V → ℕ}

lemma RingAx.prv_ne (hR : RingAx act nxt prv) (v : V) (hv : act v = true) : prv v ≠ v := by
  intro h
  have := hR.nxt_prv v hv
  rw [h] at this
  exact hR.nxt_ne v hv this

/-- The colour reduction keeps a proper colouring with colours `< 2^(wd lam t)`. -/
lemma colAt_proper (hR : RingAx act nxt prv)
    (hid : ∀ u v, act u = true → act v = true → id u = id v → u = v)
    (hlam : ∀ v, act v = true → id v < 2 ^ lam) (t : ℕ) : ∀ v, act v = true →
    colAt prv lam id t v < 2 ^ wd lam t ∧ colAt prv lam id t v ≠ colAt prv lam id t (prv v) := by
  induction t with
  | zero =>
    intro v hv
    exact ⟨hlam v hv, fun h => hR.prv_ne v hv (hid _ _ (hR.prv_act v hv) hv h.symm)⟩
  | succ t ih =>
    intro v hv
    have h1 := ih v hv
    have h2 := ih (prv v) (hR.prv_act v hv)
    exact ⟨cvStep_lt h1.1 h2.1 h1.2,
      cvStep_ne _ h1.1 h2.1 h1.2⟩

/-- After `lam` rounds the colours are `< 8`. -/
lemma colAt_lt_eight (hR : RingAx act nxt prv)
    (hid : ∀ u v, act u = true → act v = true → id u = id v → u = v)
    (hlam : ∀ v, act v = true → id v < 2 ^ lam) (v : V) (hv : act v = true) :
    colAt prv lam id lam v < 8 := by
  have h := (colAt_proper hR hid hlam lam v hv).1
  have hw : wd lam lam ≤ 3 := by have := wd_le lam lam; omega
  exact lt_of_lt_of_le h (le_trans (Nat.pow_le_pow_right (by norm_num) hw) (by norm_num))

lemma colAt_ne_nxt (hR : RingAx act nxt prv)
    (hid : ∀ u v, act u = true → act v = true → id u = id v → u = v)
    (hlam : ∀ v, act v = true → id v < 2 ^ lam) (v : V) (hv : act v = true) :
    colAt prv lam id lam (nxt v) ≠ colAt prv lam id lam v := by
  have := (colAt_proper hR hid hlam lam (nxt v) (hR.nxt_act v hv)).2
  rwa [hR.prv_nxt v hv] at this

lemma misAt_mono {i j : ℕ} (hij : i ≤ j) (v : V) (h : misAt nxt prv lam lead id i v = true) :
    misAt nxt prv lam lead id j v = true := by
  induction j, hij using Nat.le_induction with
  | base => exact h
  | succ j _ ih => simp [misAt, ih]

/-- Independence of the MIS. -/
lemma misAt_indep (hR : RingAx act nxt prv)
    (hid : ∀ u v, act u = true → act v = true → id u = id v → u = v)
    (hlam : ∀ v, act v = true → id v < 2 ^ lam)
    (hlead : ∀ u v, lead u = true → lead v = true → u = v) (i : ℕ) :
    ∀ v, act v = true → ¬ (misAt nxt prv lam lead id i v = true ∧
      misAt nxt prv lam lead id i (nxt v) = true) := by
  induction i with
  | zero =>
    rintro v hv ⟨h1, h2⟩
    exact hR.nxt_ne v hv (hlead _ _ h2 h1)
  | succ i ih =>
    rintro v hv ⟨h1, h2⟩
    have hcol := colAt_ne_nxt hR hid hlam v hv
    have hpn := hR.prv_nxt v hv
    simp only [misAt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      at h1 h2
    rw [hpn] at h2
    rcases h1 with h1 | ⟨⟨hc1, -⟩, hn1⟩ <;> rcases h2 with h2 | ⟨⟨hc2, hp2⟩, -⟩
    · exact ih v hv ⟨h1, h2⟩
    · rw [h1] at hp2; cases hp2
    · rw [h2] at hn1; cases hn1
    · exact hcol (hc2.trans hc1.symm)

/-- Maximality: every active node outside the MIS has a neighbour in it. -/
lemma misAt_dom (hR : RingAx act nxt prv)
    (hid : ∀ u v, act u = true → act v = true → id u = id v → u = v)
    (hlam : ∀ v, act v = true → id v < 2 ^ lam) (v : V) (hv : act v = true) :
    misAt nxt prv lam lead id 8 v = true ∨ misAt nxt prv lam lead id 8 (prv v) = true ∨
      misAt nxt prv lam lead id 8 (nxt v) = true := by
  obtain ⟨i, hi⟩ : ∃ i, colAt prv lam id lam v = i := ⟨_, rfl⟩
  have hi8 : i < 8 := hi ▸ colAt_lt_eight hR hid hlam v hv
  suffices misAt nxt prv lam lead id (i + 1) v = true ∨
      misAt nxt prv lam lead id (i + 1) (prv v) = true ∨
      misAt nxt prv lam lead id (i + 1) (nxt v) = true by
    rcases this with h | h | h
    · exact Or.inl (misAt_mono (by omega) _ h)
    · exact Or.inr (Or.inl (misAt_mono (by omega) _ h))
    · exact Or.inr (Or.inr (misAt_mono (by omega) _ h))
  by_cases h1 : misAt nxt prv lam lead id i v = true
  · exact Or.inl (misAt_mono (Nat.le_succ i) _ h1)
  by_cases h2 : misAt nxt prv lam lead id i (prv v) = true
  · exact Or.inr (Or.inl (misAt_mono (Nat.le_succ i) _ h2))
  by_cases h3 : misAt nxt prv lam lead id i (nxt v) = true
  · exact Or.inr (Or.inr (misAt_mono (Nat.le_succ i) _ h3))
  left
  simp only [Bool.not_eq_true] at h2 h3
  simp [misAt, h2, h3, hi]

lemma misAt_lead (v : V) (hv : lead v = true) (i : ℕ) : misAt nxt prv lam lead id i v = true :=
  misAt_mono (Nat.zero_le i) v hv

/-- **Lemma 26** (Cole–Vishkin MIS). On a virtual ring of at least two nodes with distinct IDs
`< 2^lam` and at most one leader, after `lam + 9` rounds of `misAlg` the nodes with `mis = true`
form a maximal independent set containing the leader, and every node knows whether its two
neighbours are in it. Messages have `wd lam r` bits in round `r < lam` and one bit in rounds
`lam … lam+8`; in total at most `5·lam + 9` bits (`sum_wd_le`). -/
theorem lemma26 (hR : RingAx act nxt prv)
    (hid : ∀ u v, act u = true → act v = true → id u = id v → u = v)
    (hlam : ∀ v, act v = true → id v < 2 ^ lam) (op2 : List Bool → List Bool → List Bool)
    (w : V → List Bool)
    (hlead : ∀ u v, lead u = true → lead v = true → u = v) :
    let M := fun v => ((misAlg op2).run nxt prv (fun v => initSt lam (lead v) (id v) (w v))
      (lam + 9) v)
    (∀ v, act v = true → lead v = true → (M v).mis = true) ∧
    (∀ v, act v = true → (M v).mis = true → (M (nxt v)).mis = false) ∧
    (∀ v, act v = true → (M v).mis = false → (M (prv v)).mis = true ∨ (M (nxt v)).mis = true) ∧
    (∀ v, (M v).cwIn = (M (nxt v)).mis ∧ (M v).ccwIn = (M (prv v)).mis) := by
  intro M
  have hM : ∀ v, M v = _ := run_ex op2 nxt prv lam lead id w
  refine ⟨fun v _ hl => ?_, fun v hv hm => ?_, fun v hv hm => ?_, fun v => ?_⟩
  · rw [hM]; exact misAt_lead v hl 8
  · rw [hM] at hm ⊢
    by_contra h
    exact misAt_indep hR hid hlam hlead 8 v hv ⟨hm, by simpa using h⟩
  · simp only [hM] at hm ⊢
    rcases misAt_dom hR hid hlam v hv with h | h | h
    · rw [h] at hm; cases hm
    · exact Or.inl h
    · exact Or.inr h
  · rw [hM, hM, hM]; exact ⟨rfl, rfl⟩

end ring

end Podc.ContentOblivious.Aggregation
