import Papers.PODC2017.LCLGrids.Invariant
import Papers.PODC2017.LCLGrids.QSum

/-!
# 3-colouring toroidal grids needs `Ω(n)` rounds (Theorem 9)

Section 9 of Brandt et al., *LCL problems on grids* (PODC 2017).

**Model.** The toroidal `n × n` grid `Pos n` with a consistent orientation (every node knows which
of its edges points north, east, south, west) and unique identifiers `I : Pos n → ℕ`, all `< B`;
the nodes know `n`. A deterministic `T`-round LOCAL algorithm (for this `n`) is a map
`A : (ℤ × ℤ → ℕ) → Col` that only depends on the identifiers at the offsets `d` with
`|d₁| + |d₂| ≤ T` (`GridLocal T A`): thanks to the orientation, this is exactly the information
in the radius-`T` neighbourhood. Node `v` outputs `A (gview I v)`, `gview I v d = I (v + d)`.
`Colours3 n B A`: `A` properly 3-colours every `n × n` torus with identifiers in `[0, B)`.

**Theorem 9** (`theorem9`, `theorem9_not_isLittleO`): for odd `n`, an algorithm that 3-colours all
`n × n` tori with identifiers in `[0, 8n²)` runs in at least `n/8 - 1` rounds; so 3-colouring is
not solvable in `o(n)` rounds.

**Proof (as in the paper).** From a grid algorithm `A` with `T` rounds we build a `(T+1)`-round
cycle algorithm `cycAlg A`: node `x` of a directed `n`-cycle with identifier `id x` simulates the
column `x` of a horizontal strip of `2T + 3` rows (identifiers `id x * n + y`) of a torus whose
other rows carry fixed identifiers (`gridOf`), and outputs the label `ℓ(x, 0)` of Lemma 14. The
outputs sum to the row sum `s` of row `0`; by Lemma 12 this equals the row sum of a row far from
the strip, which does not depend on the cycle identifiers, so all cycles have the same sum `Q`,
and `Q` is odd with `|Q| ≤ n/2` (Lemma 14). Theorem 10 (`QSum.theorem10_of_solves`) then gives
`n ≤ 8(T + 1)`.

**Lemma 13** (`lemma13`): the row sum is the same for all identifier assignments of the torus
(identifiers in `[0, B)`, `B ≥ 3n²`) if `4(T + 2) ≤ n`; the paper states this for `T < n/4`
(with its convention that the radius-1 checking of `ℓ` adds `O(1)` rounds).
-/

namespace Podc.LCLGrids

open Finset

variable {n : ℕ}

/-- `A` is a `T`-round algorithm on oriented tori: its output only depends on the identifiers
at the offsets of the radius-`T` ball `{d | |d₁| + |d₂| ≤ T}`. -/
def GridLocal (T : ℕ) (A : (ℤ × ℤ → ℕ) → Col) : Prop :=
  ∀ g h : ℤ × ℤ → ℕ, (∀ d : ℤ × ℤ, |d.1| + |d.2| ≤ T → g d = h d) → A g = A h

/-- The view of node `v`: offset `d ↦` identifier of the node `v + d`. -/
def gview (I : Pos n → ℕ) (v : Pos n) : ℤ × ℤ → ℕ := fun d => I (sh v d.1 d.2)

/-- The colouring computed by `A` on the torus with identifiers `I`. -/
def colouring (A : (ℤ × ℤ → ℕ) → Col) (I : Pos n → ℕ) : Pos n → Col := fun v => A (gview I v)

/-- `A` properly 3-colours every `n × n` torus whose identifiers are distinct and `< B`. -/
def Colours3 (n B : ℕ) (A : (ℤ × ℤ → ℕ) → Col) : Prop :=
  ∀ I : Pos n → ℕ, Function.Injective I → (∀ v, I v < B) → IsProper (colouring A I)

/-! ### Rows of the strip -/

/-- Row `y` belongs to the strip of rows `-R, …, R`. -/
def InStrip (R : ℕ) (y : ZMod n) : Prop := y.val ≤ R ∨ n ≤ y.val + R

instance (R : ℕ) (y : ZMod n) : Decidable (InStrip R y) := inferInstanceAs (Decidable (_ ∨ _))

lemma val_intCast_of_nonneg [NeZero n] {z : ℤ} (h0 : 0 ≤ z) (h1 : z < n) :
    ((z : ZMod n).val : ℤ) = z := by
  rw [ZMod.val_intCast, Int.emod_eq_of_lt h0 h1]

lemma val_intCast_of_neg [NeZero n] {z : ℤ} (h0 : -n ≤ z) (h1 : z < 0) :
    ((z : ZMod n).val : ℤ) = z + n := by
  rw [ZMod.val_intCast, ← Int.add_mul_emod_self_right z 1 n, one_mul,
    Int.emod_eq_of_lt (by omega) (by omega)]

lemma inStrip_intCast [NeZero n] {R : ℕ} (hR : R < n) {z : ℤ} (hz : |z| ≤ R) :
    InStrip R (z : ZMod n) := by
  rw [abs_le] at hz
  rcases le_or_gt 0 z with h | h
  · have := val_intCast_of_nonneg (n := n) h (by omega); left; omega
  · have := val_intCast_of_neg (n := n) (z := z) (by omega) h; right; omega

lemma not_inStrip_intCast [NeZero n] {R : ℕ} {z : ℤ} (h0 : R < z) (h1 : z + R < n) :
    ¬ InStrip R (z : ZMod n) := by
  have := val_intCast_of_nonneg (n := n) (z := z) (by omega) (by omega)
  unfold InStrip; omega

/-! ### The reduction -/

/-- The torus built from a cycle with identifiers `id`: rows `-R, …, R` form a strip in which the
node `(x, y)` gets the identifier `id x * n + y`; the other nodes get fixed identifiers
`7n² + x n + y`. -/
def gridOf (R : ℕ) (id : ZMod n → ℕ) : Pos n → ℕ := fun v =>
  if InStrip R v.2 then id v.1 * n + v.2.val else 7 * n * n + v.1.val * n + v.2.val

lemma gridOf_of_inStrip {R : ℕ} {id : ZMod n → ℕ} {v : Pos n} (h : InStrip R v.2) :
    gridOf R id v = id v.1 * n + v.2.val := ite_eq_left_of_eq_true _ _ (eq_true h)

lemma gridOf_of_not_inStrip {R : ℕ} {id : ZMod n → ℕ} {v : Pos n} (h : ¬ InStrip R v.2) :
    gridOf R id v = 7 * n * n + v.1.val * n + v.2.val := ite_eq_right_of_eq_false _ _ (eq_false h)

lemma gridOf_lt [NeZero n] (R : ℕ) {id : ZMod n → ℕ} (hid : ∀ x, id x < 7 * n) (v : Pos n) :
    gridOf R id v < 8 * n ^ 2 := by
  have h1 := v.1.val_lt
  have h2 := v.2.val_lt
  have h3 := hid v.1
  unfold gridOf
  split_ifs
  · nlinarith
  · nlinarith

lemma gridOf_injective [NeZero n] (R : ℕ) {id : ZMod n → ℕ} (hinj : Function.Injective id)
    (hid : ∀ x, id x < 7 * n) : Function.Injective (gridOf R id) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  have hy := y.val_lt
  have hy' := y'.val_lt
  have hx := x.val_lt
  have hx' := x'.val_lt
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  simp only [gridOf] at h
  have key : ∀ a b a' b' : ℕ, b < n → b' < n → a * n + b = a' * n + b' → a = a' ∧ b = b' := by
    intro a b a' b' hb hb' e
    have e1 : (a * n + b) / n = a := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn,
      Nat.div_eq_of_lt hb, zero_add]
    have e2 : (a' * n + b') / n = a' := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn,
      Nat.div_eq_of_lt hb', zero_add]
    have : a = a' := by rw [← e1, ← e2, e]
    subst this; exact ⟨rfl, by omega⟩
  split_ifs at h with h1 h2 h2
  · obtain ⟨e1, e2⟩ := key _ _ _ _ hy hy' h
    rw [hinj e1, ZMod.val_injective n e2]
  · have := hid x; nlinarith
  · have := hid x'; nlinarith
  · obtain ⟨e1, e2⟩ := key (7 * n + x.val) y.val (7 * n + x'.val) y'.val hy hy' (by linarith)
    rw [ZMod.val_injective n (by omega : x.val = x'.val), ZMod.val_injective n e2]

/-- The grid view simulated by a cycle node from its cycle view `g`, for the grid node at offset
`(a, b)` from it. -/
def simView (n : ℕ) (g : ℤ → ℕ) (a b : ℤ) : ℤ × ℤ → ℕ :=
  fun d => g (a + d.1) * n + ((b + d.2 : ℤ) : ZMod n).val

/-- The cycle algorithm obtained from a grid algorithm `A`: simulate `A` on the `3 × 3` block of
the strip around the node and output the label `ℓ` of Lemma 14. -/
def cycAlg (n : ℕ) (A : (ℤ × ℤ → ℕ) → Col) (g : ℤ → ℕ) : ℤ :=
  (Block.mk (A (simView n g (-1) 1)) (A (simView n g 0 1)) (A (simView n g 1 1))
    (A (simView n g (-1) 0)) (A (simView n g 0 0)) (A (simView n g 1 0))
    (A (simView n g (-1) (-1))) (A (simView n g 0 (-1))) (A (simView n g 1 (-1)))).ell

lemma Block.ell_mem (B : Block) : B.ell = -1 ∨ B.ell = 0 ∨ B.ell = 1 := by
  unfold Block.ell; split_ifs <;> simp

lemma cycAlg_isLocal {T : ℕ} {A : (ℤ × ℤ → ℕ) → Col} (hA : GridLocal T A) :
    QSum.IsLocal (T + 1) (cycAlg n A) := by
  intro g h hgh
  have e : ∀ a b : ℤ, |a| ≤ 1 → A (simView n g a b) = A (simView n h a b) := by
    intro a b ha
    refine hA _ _ fun d hd => ?_
    simp only [simView]
    rw [hgh]
    have := abs_nonneg d.2
    have := abs_add_le a d.1
    push_cast; linarith
  simp only [cycAlg]
  rw [e (-1) 1 (by norm_num), e 0 1 (by norm_num), e 1 1 (by norm_num), e (-1) 0 (by norm_num),
    e 0 0 (by norm_num), e 1 0 (by norm_num), e (-1) (-1) (by norm_num), e 0 (-1) (by norm_num),
    e 1 (-1) (by norm_num)]

/-- In the strip, a node of the simulated torus computes what the cycle node simulates. -/
lemma colouring_gridOf_strip [NeZero n] {T : ℕ} {A : (ℤ × ℤ → ℕ) → Col} (hA : GridLocal T A)
    (hTn : T + 1 < n) (id : ZMod n → ℕ) (x : ZMod n) (a b : ℤ) (hb : |b| ≤ 1) :
    colouring A (gridOf (T + 1) id) (sh (x, 0) a b) = A (simView n (QSum.view id x) a b) := by
  refine hA _ _ fun d hd => ?_
  have hb2 : |b + d.2| ≤ ((T + 1 : ℕ) : ℤ) := by
    have := abs_add_le b d.2
    have := abs_nonneg d.1
    push_cast; linarith
  have hst := inStrip_intCast (n := n) hTn hb2
  simp only [gview, simView, QSum.view, sh_sh]
  have hpos : sh (x, (0 : ZMod n)) (a + d.1) (b + d.2) =
      (x + ((a + d.1 : ℤ) : ZMod n), ((b + d.2 : ℤ) : ZMod n)) := by simp [sh]
  rw [hpos, gridOf_of_inStrip hst]

/-- The sum of the cycle outputs is the row sum of row `0` of the simulated torus. -/
lemma cycleSum_cycAlg [NeZero n] {T : ℕ} {A : (ℤ × ℤ → ℕ) → Col} (hA : GridLocal T A)
    (hTn : T + 1 < n) (id : ZMod n → ℕ) :
    QSum.cycleSum (cycAlg n A) id = rowSum (colouring A (gridOf (T + 1) id)) 0 := by
  unfold QSum.cycleSum rowSum
  refine sum_congr rfl fun x _ => ?_
  rw [ell_eq_block, cycAlg]
  have e := colouring_gridOf_strip hA hTn id x
  simp only [block]
  rw [← e (-1) 1 (by norm_num), ← e 0 1 (by norm_num), ← e 1 1 (by norm_num),
    ← e (-1) 0 (by norm_num), ← e 1 0 (by norm_num), ← e (-1) (-1) (by norm_num),
    ← e 0 (-1) (by norm_num), ← e 1 (-1) (by norm_num)]
  have e0 := e 0 0 (by norm_num)
  simp only [sh_zero] at e0
  rw [← e0]

/-- Far from the strip, the simulated torus does not depend on the cycle identifiers. -/
lemma rowSum_far [NeZero n] {T : ℕ} {A : (ℤ × ℤ → ℕ) → Col} (hA : GridLocal T A)
    (hTn : 8 * T + 9 ≤ n) (id id' : ZMod n → ℕ) :
    rowSum (colouring A (gridOf (T + 1) id)) ((n / 2 : ℕ) : ZMod n) =
      rowSum (colouring A (gridOf (T + 1) id')) ((n / 2 : ℕ) : ZMod n) := by
  unfold rowSum
  refine sum_congr rfl fun x _ => ?_
  rw [ell_eq_block, ell_eq_block]
  have e : ∀ a b : ℤ, |b| ≤ 1 →
      colouring A (gridOf (T + 1) id) (sh (x, ((n / 2 : ℕ) : ZMod n)) a b) =
        colouring A (gridOf (T + 1) id') (sh (x, ((n / 2 : ℕ) : ZMod n)) a b) := by
    intro a b hb
    refine hA _ _ fun d hd => ?_
    rw [abs_le] at hb
    have h2 : |d.2| ≤ T := by have := abs_nonneg d.1; linarith
    rw [abs_le] at h2
    have hns := not_inStrip_intCast (n := n) (R := T + 1) (z := (n / 2 : ℕ) + b + d.2)
      (by push_cast; omega) (by push_cast; omega)
    simp only [gview, sh_sh]
    have hpos : sh (x, ((n / 2 : ℕ) : ZMod n)) (a + d.1) (b + d.2) =
        (x + ((a + d.1 : ℤ) : ZMod n), (((n / 2 : ℕ) + b + d.2 : ℤ) : ZMod n)) := by
      simp only [sh, Int.cast_add, Int.cast_natCast, add_assoc]
    rw [hpos, gridOf_of_not_inStrip hns, gridOf_of_not_inStrip hns]
  simp only [block]
  have e0 := e 0 0 (by norm_num)
  simp only [sh_zero] at e0
  rw [e (-1) 1 (by norm_num), e 0 1 (by norm_num), e 1 1 (by norm_num),
    e (-1) 0 (by norm_num), e0, e 1 0 (by norm_num), e (-1) (-1) (by norm_num),
    e 0 (-1) (by norm_num), e 1 (-1) (by norm_num)]

/-- **Theorem 9** of the paper (for one odd `n`). If a `T`-round algorithm properly 3-colours every
oriented `n × n` torus with identifiers in `[0, 8n²)` and `n` is odd, then `n ≤ 8T + 8`. -/
theorem theorem9 {T : ℕ} {A : (ℤ × ℤ → ℕ) → Col} (hn : Odd n) (hA : GridLocal T A)
    (hcol : Colours3 n (8 * n ^ 2) A) : n ≤ 8 * T + 8 := by
  have : NeZero n := ⟨by rintro rfl; exact Nat.not_odd_zero hn⟩
  by_contra hT
  replace hT := Nat.lt_of_not_le hT
  have hTn : T + 1 < n := by omega
  -- a fixed reference cycle
  let id₀ : ZMod n → ℕ := fun x => x.val
  have hid₀ : ∀ x, id₀ x < 7 * n := fun x => by have := x.val_lt; simp only [id₀]; omega
  have hproper : ∀ id : ZMod n → ℕ, Function.Injective id → (∀ x, id x < 7 * n) →
      IsProper (colouring A (gridOf (T + 1) id)) := fun id hinj hid =>
    hcol _ (gridOf_injective _ hinj hid) (gridOf_lt _ hid)
  have hp₀ := hproper id₀ (ZMod.val_injective n) hid₀
  set Q := rowSum (colouring A (gridOf (T + 1) id₀)) 0
  have hsolve : QSum.Solves n (7 * n) Q (cycAlg n A) := by
    intro id hinj hid
    refine ⟨fun v => Block.ell_mem _, ?_⟩
    rw [cycleSum_cycAlg hA hTn, rowSum_eq (hproper id hinj hid) 0 ((n / 2 : ℕ) : ZMod n),
      rowSum_far hA (by omega) id id₀, ← rowSum_eq hp₀]
  have := QSum.theorem10_of_solves (cycAlg_isLocal hA) hsolve le_rfl (odd_rowSum hp₀ hn 0)
    (two_mul_abs_rowSum_le hp₀ 0)
  omega

/-- **Theorem 9** of the paper: "the complexity of 3-colouring on 2-dimensional grids is
`Ω(n)`". If `A n` is a `T n`-round algorithm that properly 3-colours every oriented `n × n` torus
with identifiers in `[0, 8n²)` for every odd `n`, then `T(n) ≥ n/8 - 1` for odd `n` and
`T(n) ≠ o(n)`. -/
theorem theorem9_not_isLittleO (A : ℕ → (ℤ × ℤ → ℕ) → Col) (T : ℕ → ℕ)
    (hA : ∀ n, GridLocal (T n) (A n)) (hcol : ∀ n, Odd n → Colours3 n (8 * n ^ 2) (A n)) :
    (∀ n, Odd n → n ≤ 8 * T n + 8) ∧
      ¬ (fun n => (T n : ℝ)) =o[Filter.atTop] (fun n => (n : ℝ)) := by
  have main : ∀ n, Odd n → n ≤ 8 * T n + 8 := fun n hn => theorem9 hn (hA n) (hcol n hn)
  refine ⟨main, fun ho => ?_⟩
  have := ho.def (show (0 : ℝ) < 1 / 16 by norm_num)
  rw [Filter.eventually_atTop] at this
  obtain ⟨N, hN⟩ := this
  have h1 := hN (2 * (N + 16) + 1) (by omega)
  have h2 := main (2 * (N + 16) + 1) (by simp)
  simp only [Real.norm_natCast] at h1
  have : ((2 * (N + 16) + 1 : ℕ) : ℝ) ≤ 8 * (T (2 * (N + 16) + 1) : ℝ) + 8 := by exact_mod_cast h2
  have hpos : (33 : ℝ) ≤ ((2 * (N + 16) + 1 : ℕ) : ℝ) := by
    push_cast; linarith [(N.cast_nonneg : (0:ℝ) ≤ N)]
  nlinarith

end Podc.LCLGrids
