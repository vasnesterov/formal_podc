import Papers.PODC2014.RendezvousTimeCost.Ring

/-!
# Theorem 3.1: cost `E + o(E)` forces time `Ω(E L)`

We follow the proof of Theorem 3.1 of [Miller–Pelc], in the oriented ring of size `n`
(`E = n - 1`) with simultaneous start (`Ring.lean`).

* `fwd`, `back` : the largest clockwise / counterclockwise displacement of the trimmed solo
  execution (the paper's `forward(x)`, `back(x)`), measured on the line `ℤ`.
* `back_le_phi` : Fact 3.3 (with Facts 3.1, 3.2).
* `Eager` : the tournament relation of Facts 3.5; `exists_chain` : a Hamiltonian path of the
  tournament (by insertion sort, which works for any total relation).
* `step` : Facts 3.6–3.8 (one step of the induction).
* `thm_3_1_explicit` : the finite statement; `thm_3_1` : the asymptotic statement.
-/

namespace Podc.RendezvousTimeCost

open Finset

namespace LBCost

set_option linter.unusedSectionVars false

variable {n L : ℕ} [NeZero n]

/-- `forward(x)`: maximal clockwise displacement of `x` up to round `m_x`. -/
noncomputable def fwd (n : ℕ) [NeZero n] {L : ℕ} (V : Behaviour L) (x : Fin L) : ℤ :=
  (range (mx n V x + 1)).sup' nonempty_range_add_one (fun t => disp (V x) t)

/-- `back(x)`: maximal counterclockwise displacement of `x` up to round `m_x`. -/
noncomputable def back (n : ℕ) [NeZero n] {L : ℕ} (V : Behaviour L) (x : Fin L) : ℤ :=
  (range (mx n V x + 1)).sup' nonempty_range_add_one (fun t => - disp (V x) t)

lemma disp_le_fwd (V : Behaviour L) (x : Fin L) {t : ℕ} (ht : t ≤ mx n V x) :
    disp (V x) t ≤ fwd n V x :=
  le_sup' (fun t => disp (V x) t) (mem_range.2 (by omega))

lemma neg_back_le_disp (V : Behaviour L) (x : Fin L) {t : ℕ} (ht : t ≤ mx n V x) :
    - back n V x ≤ disp (V x) t := by
  have := le_sup' (fun t => - disp (V x) t) (mem_range.2 (Nat.lt_succ_of_le ht))
  simp only [back] at *
  linarith

lemma exists_fwd (V : Behaviour L) (x : Fin L) :
    ∃ t ≤ mx n V x, disp (V x) t = fwd n V x := by
  obtain ⟨t, ht, he⟩ := exists_mem_eq_sup' (nonempty_range_add_one (n := mx n V x))
    (fun t => disp (V x) t)
  exact ⟨t, Nat.lt_succ_iff.1 (mem_range.1 ht), he.symm⟩

lemma exists_back (V : Behaviour L) (x : Fin L) :
    ∃ t ≤ mx n V x, - disp (V x) t = back n V x := by
  obtain ⟨t, ht, he⟩ := exists_mem_eq_sup' (nonempty_range_add_one (n := mx n V x))
    (fun t => - disp (V x) t)
  exact ⟨t, Nat.lt_succ_iff.1 (mem_range.1 ht), he.symm⟩

lemma fwd_nonneg (V : Behaviour L) (x : Fin L) : 0 ≤ fwd n V x := by
  simpa using disp_le_fwd V x (Nat.zero_le _)

lemma back_nonneg (V : Behaviour L) (x : Fin L) : 0 ≤ back n V x := by
  simpa using neg_back_le_disp V x (Nat.zero_le _)

/-- A walk on `ℤ` that reaches `a ≥ 0` at time `t₁` and `-b ≤ 0` at time `t₂`, both before `m`,
makes at least `a + b + min a b` moves (Fact 3.2). -/
lemma moves_ge_of_extremes (v : ℕ → SignType) {m t₁ t₂ : ℕ} (h₁ : t₁ ≤ m) (h₂ : t₂ ≤ m)
    {a b : ℤ} (ha : disp v t₁ = a) (hb : - disp v t₂ = b) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    a + b + min a b ≤ moves v m := by
  have hm₁ := moves_mono v h₁
  have hm₂ := moves_mono v h₂
  rcases le_total t₁ t₂ with h | h
  · have e1 := abs_disp_le_moves v t₁
    have e2 := abs_disp_sub_le_moves v h
    rw [abs_of_nonneg (by omega)] at e1
    rw [abs_of_nonpos (by omega)] at e2
    have : (moves v t₂ : ℤ) ≤ moves v m := by exact_mod_cast hm₂
    have : a + b + min a b ≤ a + b + a := by simp
    omega
  · have e1 := abs_disp_le_moves v t₂
    have e2 := abs_disp_sub_le_moves v h
    rw [abs_of_nonpos (by omega)] at e1
    rw [abs_of_nonneg (by omega)] at e2
    have : (moves v t₁ : ℤ) ≤ moves v m := by exact_mod_cast hm₁
    have : a + b + min a b ≤ a + b + b := by simp
    omega

/-- An integer in `[-(n-1), -1]` is not `0` modulo `n`. -/
lemma intCast_ne_zero_of_bounds {d : ℤ} (h1 : d ≤ -1) (h2 : -(n : ℤ) < d) : (d : ZMod n) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro hd
  have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_of_neg (by omega)]; omega)
  omega

/-- **Fact 3.3**: if the algorithm has cost at most `E + φ`, then every clockwise-heavy agent has
`back(x) ≤ φ`. (The proof uses Facts 3.1 and 3.2.) -/
lemma back_le_phi (hn : 2 ≤ n) (hL : 2 ≤ L) {V : Behaviour L} (hV : IsRendezvous n V) {φ : ℕ}
    (hcost : CostLE n V (n - 1 + φ)) (x : Fin L) (hx : back n V x ≤ fwd n V x) :
    back n V x ≤ φ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨y, px, py, hyx, hp, hm⟩ := exists_meetTime_eq_mx V x hn hL
  set m := mx n V x
  have hc := hcost x y hyx.symm px py hp
  simp only [execCost, hm] at hc
  -- Fact 3.2 for `x`
  obtain ⟨t₁, ht₁, hf⟩ := exists_fwd (n := n) V x
  obtain ⟨t₂, ht₂, hb⟩ := exists_back (n := n) V x
  have hx2 := moves_ge_of_extremes (V x) ht₁ ht₂ hf hb (fwd_nonneg (n := n) V x)
    (back_nonneg (n := n) V x)
  rw [min_eq_right hx] at hx2
  -- extremes of `y` up to round `m`
  set fy := (range (m + 1)).sup' nonempty_range_add_one (fun t => disp (V y) t)
  set by' := (range (m + 1)).sup' nonempty_range_add_one (fun t => - disp (V y) t)
  obtain ⟨s₁, hs₁, hfy⟩ := exists_mem_eq_sup' (nonempty_range_add_one (n := m))
    (fun t => disp (V y) t)
  obtain ⟨s₂, hs₂, hby⟩ := exists_mem_eq_sup' (nonempty_range_add_one (n := m))
    (fun t => - disp (V y) t)
  have hfy0 : 0 ≤ fy := by
    have := le_sup' (fun t => disp (V y) t) (mem_range.2 (Nat.succ_pos m)); simpa using this
  have hby0 : 0 ≤ by' := by
    have := le_sup' (fun t => - disp (V y) t) (mem_range.2 (Nat.succ_pos m)); simpa using this
  have hy2 := moves_ge_of_extremes (V y) (Nat.lt_succ_iff.1 (mem_range.1 hs₁))
    (Nat.lt_succ_iff.1 (mem_range.1 hs₂)) hfy.symm hby.symm hfy0 hby0
  have hmin : 0 ≤ min fy by' := le_min hfy0 hby0
  have hcz : ((moves (V x) m : ℕ) : ℤ) + moves (V y) m ≤ (n : ℤ) - 1 + φ := by
    have : moves (V x) m + moves (V y) m ≤ n - 1 + φ := hc
    have h1 : (1 : ℕ) ≤ n := by omega
    have := (Nat.cast_le (α := ℤ)).2 this
    push_cast [h1] at this
    exact this
  -- the shifted start of `y` (Fact 3.1)
  set D : ℤ := fwd n V x + 1 + by'
  have hD : D + back n V x + fy < n := by
    have := back_nonneg (n := n) V x
    simp only [D]; linarith
  have hfx := fwd_nonneg (n := n) V x
  have hpne : px ≠ px + (D : ZMod n) := by
    intro h
    have h0 : ((D : ℤ) : ZMod n) = 0 := by linear_combination -h
    have h3 : (((-D) : ℤ) : ZMod n) ≠ 0 :=
      intCast_ne_zero_of_bounds (by simp only [D]; linarith)
        (by linarith [back_nonneg (n := n) V x])
    apply h3; push_cast; rw [h0, neg_zero]
  obtain ⟨t, ht⟩ := hV x y hyx.symm px (px + (D : ZMod n)) hpne
  have htm : meetTime n V x px y (px + (D : ZMod n)) ≤ m := meetTime_le_mx V hyx hpne
  have hmeet := meets_meetTime ⟨t, ht⟩
  set t' := meetTime n V x px y (px + (D : ZMod n))
  have hx1 := disp_le_fwd V x htm
  have hx0 := neg_back_le_disp V x htm
  have hy1 : disp (V y) t' ≤ fy := le_sup' (fun t => disp (V y) t) (mem_range.2 (by omega))
  have hy0 : - disp (V y) t' ≤ by' :=
    le_sup' (fun t => - disp (V y) t) (mem_range.2 (by omega))
  unfold Meets at hmeet
  have hz : ((disp (V x) t' - D - disp (V y) t' : ℤ) : ZMod n) = 0 := by
    push_cast; linear_combination hmeet
  exact intCast_ne_zero_of_bounds (by linarith) (by linarith) hz

/-! ### The tournament (Facts 3.5–3.8) -/

/-- `F = ⌈E/2⌉ = ⌊n/2⌋`. -/
def F (n : ℕ) : ℕ := n / 2

/-- The meeting round of execution `α(min a b, 0, max a b, F)`. -/
noncomputable def τ (n : ℕ) {L : ℕ} (V : Behaviour L) (a b : Fin L) : ℕ :=
  meetTime n V (min a b) 0 (max a b) (F n : ZMod n)

lemma τ_comm (V : Behaviour L) (a b : Fin L) : τ n V a b = τ n V b a := by
  simp [τ, min_comm, max_comm]

/-- `a` is the eager agent in `α(min a b, 0, max a b, F)`. -/
def Eager (n : ℕ) {L : ℕ} (V : Behaviour L) (a b : Fin L) : Prop :=
  disp (V b) (τ n V a b) + F n ≤ disp (V a) (τ n V a b)

lemma F_pos (hn : 2 ≤ n) : 0 < F n := by simp only [F]; omega

lemma zero_ne_F (hn : 2 ≤ n) : (0 : ZMod n) ≠ (F n : ZMod n) := by
  intro h
  have h' : ((F n : ℕ) : ZMod n) = 0 := h.symm
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (F_pos hn) h'
  simp only [F] at this; omega

lemma meets_τ (hn : 2 ≤ n) {V : Behaviour L} (hV : IsRendezvous n V) {a b : Fin L}
    (hab : a ≠ b) : Meets n V (min a b) 0 (max a b) (F n : ZMod n) (τ n V a b) := by
  apply meets_meetTime
  exact hV _ _ (by rcases le_total a b with h | h <;> simp [h, hab, hab.symm]) _ _ (zero_ne_F hn)

lemma τ_le_mx_left (hn : 2 ≤ n) {V : Behaviour L} {a b : Fin L} (hab : a ≠ b) :
    τ n V a b ≤ mx n V a := by
  unfold τ
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
    exact meetTime_le_mx V (Ne.symm hab) (zero_ne_F hn)
  · rw [min_eq_right h, max_eq_left h, meetTime_comm]
    exact meetTime_le_mx V (Ne.symm hab) (zero_ne_F hn).symm

lemma τ_le_mx_right (hn : 2 ≤ n) {V : Behaviour L} {a b : Fin L} (hab : a ≠ b) :
    τ n V a b ≤ mx n V b := by
  rw [τ_comm]; exact τ_le_mx_left hn (Ne.symm hab)

/-- An integer congruent to `±F` modulo `n` has absolute value at least `F`. -/
lemma le_abs_of_cong (hn : 2 ≤ n) {d : ℤ}
    (h : (d : ZMod n) = (F n : ZMod n) ∨ (d : ZMod n) = - (F n : ZMod n)) : (F n : ℤ) ≤ |d| := by
  have hF : 2 * (F n : ℤ) ≤ n := by simp only [F]; omega
  have hF0 : 0 < (F n : ℤ) := by exact_mod_cast F_pos hn
  rcases h with h | h
  · have : ((d - F n : ℤ) : ZMod n) = 0 := by push_cast; rw [h]; ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    obtain ⟨q, hq⟩ := this
    rcases lt_trichotomy q 0 with hq0 | rfl | hq0
    · have : (n : ℤ) * q ≤ - n := by nlinarith
      rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
    · have : (n : ℤ) ≤ n * q := by nlinarith
      rw [abs_of_nonneg (by linarith)]; linarith
  · have : ((d + F n : ℤ) : ZMod n) = 0 := by push_cast; rw [h]; ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    obtain ⟨q, hq⟩ := this
    rcases lt_trichotomy q 0 with hq0 | rfl | hq0
    · have : (n : ℤ) * q ≤ - n := by nlinarith
      rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith
    · have : (n : ℤ) ≤ n * q := by nlinarith
      rw [abs_of_nonneg (by linarith)]; linarith

/-- In `α(min a b, 0, max a b, F)` the displacements differ by at least `F`. -/
lemma F_le_abs_sub (hn : 2 ≤ n) {V : Behaviour L} (hV : IsRendezvous n V) {a b : Fin L}
    (hab : a ≠ b) : (F n : ℤ) ≤ |disp (V a) (τ n V a b) - disp (V b) (τ n V a b)| := by
  have hm := meets_τ hn hV hab
  apply le_abs_of_cong hn
  unfold Meets at hm
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h] at hm
    left; push_cast; linear_combination hm
  · rw [min_eq_right h, max_eq_left h] at hm
    right; push_cast; linear_combination -hm

/-- **Fact 3.5**: in `α(min a b, 0, max a b, F)` one of the agents is eager. -/
lemma eager_or (hn : 2 ≤ n) {V : Behaviour L} (hV : IsRendezvous n V) {a b : Fin L}
    (hab : a ≠ b) : Eager n V a b ∨ Eager n V b a := by
  have := F_le_abs_sub hn hV hab
  unfold Eager
  rw [τ_comm V b a]
  rcases le_abs'.1 this with h | h
  · right; linarith
  · left; linarith

/-- Base of Fact 3.8: every such execution lasts at least `F/2` rounds. -/
lemma F_le_two_τ (hn : 2 ≤ n) {V : Behaviour L} (hV : IsRendezvous n V) {a b : Fin L}
    (hab : a ≠ b) : F n ≤ 2 * τ n V a b := by
  have h := F_le_abs_sub hn hV hab
  have h1 := abs_disp_sub_le (V a) (Nat.zero_le (τ n V a b))
  have h2 := abs_disp_sub_le (V b) (Nat.zero_le (τ n V a b))
  simp only [disp_zero, sub_zero, Nat.cast_zero] at h1 h2
  have := abs_sub (disp (V a) (τ n V a b)) (disp (V b) (τ n V a b))
  have : (F n : ℤ) ≤ 2 * τ n V a b := by linarith
  exact_mod_cast this

/-- The cost bound applied to `α(min a b, 0, max a b, F)`. -/
lemma cost_τ (hn : 2 ≤ n) {V : Behaviour L} {φ : ℕ} (hcost : CostLE n V (n - 1 + φ))
    {a b : Fin L} (hab : a ≠ b) :
    (moves (V a) (τ n V a b) : ℤ) + moves (V b) (τ n V a b) ≤ (n : ℤ) - 1 + φ := by
  have h : execCost n V (min a b) 0 (max a b) (F n : ZMod n) ≤ n - 1 + φ :=
    hcost _ _ (by rcases le_total a b with h | h <;> simp [h, hab, hab.symm]) _ _ (zero_ne_F hn)
  have h1 : (1 : ℕ) ≤ n := by omega
  have h' : (execCost n V (min a b) 0 (max a b) (F n : ZMod n) : ℤ) ≤ (n : ℤ) - 1 + φ := by
    have := (Nat.cast_le (α := ℤ)).2 h; push_cast [h1] at this; exact this
  unfold execCost at h'
  rcases le_total a b with h | h
  · simp only [min_eq_left h, max_eq_right h] at h'
    simpa [τ, min_eq_left h, max_eq_right h] using h'
  · simp only [min_eq_right h, max_eq_left h] at h'
    simp only [τ, min_eq_right h, max_eq_left h]; push_cast at h' ⊢; linarith

/-- **Facts 3.6–3.8 (one step)**: along a path `a → b → c` of the tournament, with `c`
clockwise-heavy, the execution of the next edge is longer by at least `(F - 3φ)/2`. -/
lemma step (hn : 2 ≤ n) (hL : 2 ≤ L) {V : Behaviour L} (hV : IsRendezvous n V) {φ : ℕ}
    (hcost : CostLE n V (n - 1 + φ)) (hφ : 3 * φ < F n) {a b c : Fin L} (hab : a ≠ b)
    (hbc : b ≠ c) (hc : back n V c ≤ fwd n V c) (h1 : Eager n V a b) (h2 : Eager n V b c) :
    2 * τ n V a b + (F n - 3 * φ) ≤ 2 * τ n V b c := by
  have hcφ := back_le_phi hn hL hV hcost c hc
  have hdc := neg_back_le_disp V c (τ_le_mx_right hn hbc)
  unfold Eager at h1 h2
  have hc1 := cost_τ hn hcost hab
  have hma := abs_disp_le_moves (V a) (τ n V a b)
  have hmb := abs_disp_le_moves (V b) (τ n V a b)
  have hFn : (n : ℤ) - 1 ≤ 2 * F n := by simp only [F]; omega
  have hφ' : 3 * (φ : ℤ) < F n := by exact_mod_cast hφ
  -- Fact 3.6
  have f36 : 2 * disp (V b) (τ n V a b) ≤ (F n : ℤ) + φ := by
    have := le_abs_self (disp (V a) (τ n V a b))
    have := le_abs_self (disp (V b) (τ n V a b))
    linarith
  -- Fact 3.7
  have f37 : τ n V a b ≤ τ n V b c := by
    by_contra hlt
    push Not at hlt
    have e1 := abs_disp_le_moves (V b) (τ n V b c)
    have e2 := abs_disp_sub_le_moves (V b) hlt.le
    have := le_abs_self (disp (V b) (τ n V b c))
    have := neg_abs_le (disp (V b) (τ n V a b) - disp (V b) (τ n V b c))
    have := le_abs_self (disp (V a) (τ n V a b))
    linarith
  -- Fact 3.8
  have e := abs_disp_sub_le (V b) f37
  have := le_abs_self (disp (V b) (τ n V b c) - disp (V b) (τ n V a b))
  have h3 : 3 * φ ≤ F n := hφ.le
  have : ((2 * τ n V a b + (F n - 3 * φ) : ℕ) : ℤ) ≤ ((2 * τ n V b c : ℕ) : ℤ) := by
    push_cast [h3]; linarith
  exact_mod_cast this

/-- A Hamiltonian path in a tournament: insertion sort produces a chain for any relation that
is total on distinct elements. -/
lemma chain_orderedInsert {α : Type*} (R : α → α → Prop) [DecidableRel R] (a : α) :
    ∀ l : List α, l.IsChain R → (∀ b ∈ l, ¬ R a b → R b a) → (l.orderedInsert R a).IsChain R
  | [], _, _ => by simp
  | b :: l, hl, htot => by
    simp only [List.orderedInsert]
    split_ifs with h
    · exact List.isChain_cons_cons.2 ⟨h, hl⟩
    · have ih := chain_orderedInsert R a l hl.tail
        (fun c hc => htot c (List.mem_cons_of_mem _ hc))
      have hba : R b a := htot b (by simp) h
      cases l with
      | nil => simpa using hba
      | cons c l =>
        simp only [List.orderedInsert] at ih ⊢
        split_ifs with h'
        · simp only [h', ↓reduceIte] at ih
          exact List.isChain_cons_cons.2 ⟨hba, ih⟩
        · simp only [h', ↓reduceIte] at ih
          exact List.isChain_cons_cons.2 ⟨(List.isChain_cons_cons.1 hl).1, ih⟩

lemma chain_insertionSort {α : Type*} (R : α → α → Prop) [DecidableRel R]
    (htot : ∀ a b, a ≠ b → R a b ∨ R b a) :
    ∀ l : List α, l.Nodup → (l.insertionSort R).IsChain R
  | [], _ => by simp
  | a :: l, hl => by
    simp only [List.insertionSort]
    have hnd := List.nodup_cons.1 hl
    apply chain_orderedInsert R a _ (chain_insertionSort R htot l hnd.2)
    intro b hb hab
    have hb' : b ∈ l := (List.perm_insertionSort R l).mem_iff.1 hb
    rcases htot a b (fun h => hnd.1 (h ▸ hb')) with h | h
    · exact absurd h hab
    · exact h

/-- The chain induction (Fact 3.8): along a path of the tournament through clockwise-heavy
agents, the execution of the last edge lasts long. -/
lemma chain_bound (hn : 2 ≤ n) (hL : 2 ≤ L) {V : Behaviour L} (hV : IsRendezvous n V) {φ : ℕ}
    (hcost : CostLE n V (n - 1 + φ)) (hφ : 3 * φ < F n) :
    ∀ (l : List (Fin L)) (a b : Fin L), (a :: b :: l).IsChain (Eager n V) →
      (a :: b :: l).Nodup → (∀ c ∈ l, back n V c ≤ fwd n V c) →
      ∃ u v, u ≠ v ∧ 2 * τ n V a b + l.length * (F n - 3 * φ) ≤ 2 * τ n V u v
  | [], a, b, _, hnd, _ => ⟨a, b, by simpa using hnd, by simp⟩
  | c :: l, a, b, hch, hnd, hh => by
    have hab : a ≠ b := by intro h; simp [h] at hnd
    have hbc : b ≠ c := by intro h; simp [h] at hnd
    have hs := step hn hL hV hcost hφ hab hbc (hh c (by simp)) (List.isChain_cons_cons.1 hch).1
      (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch).2).1
    obtain ⟨u, v, huv, hb⟩ := chain_bound hn hL hV hcost hφ l b c
      (List.isChain_cons_cons.1 hch).2
      (List.nodup_cons.1 hnd).2 (fun d hd => hh d (by simp [hd]))
    refine ⟨u, v, huv, ?_⟩
    simp only [List.length_cons]
    nlinarith

/-- The bound for a set `S` of clockwise-heavy agents. -/
lemma bound_of_heavy (hn : 2 ≤ n) (hL : 2 ≤ L) {V : Behaviour L} (hV : IsRendezvous n V)
    {φ : ℕ} (hcost : CostLE n V (n - 1 + φ)) (hφ : 3 * φ < F n) (S : Finset (Fin L))
    (hS : ∀ c ∈ S, back n V c ≤ fwd n V c) :
    ∃ u v, u ≠ v ∧ (S.card - 1) * (F n - 3 * φ) ≤ 2 * τ n V u v := by
  classical
  set l := S.toList.insertionSort (Eager n V)
  have hperm : l.Perm S.toList := List.perm_insertionSort _ _
  have hlen : l.length = S.card := by rw [hperm.length_eq, length_toList]
  have hnd : l.Nodup := hperm.nodup_iff.2 (nodup_toList S)
  have hch : l.IsChain (Eager n V) :=
    chain_insertionSort _ (fun a b h => eager_or hn hV h) _ (nodup_toList S)
  have hmem : ∀ c ∈ l, back n V c ≤ fwd n V c := fun c hc =>
    hS c (mem_toList.1 (hperm.mem_iff.1 hc))
  match hl : l with
  | [] =>
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff], ?_⟩
    rw [← hlen]; simp
  | [a] =>
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff], ?_⟩
    rw [← hlen]; simp
  | a :: b :: l' =>
    have hab : a ≠ b := by intro h; simp [h] at hnd
    obtain ⟨u, v, huv, hb⟩ := chain_bound hn hL hV hcost hφ l' a b hch hnd
      (fun c hc => hmem c (by simp [hc]))
    refine ⟨u, v, huv, ?_⟩
    have h0 := F_le_two_τ hn hV hab
    rw [← hlen]
    simp only [List.length_cons, Nat.add_sub_cancel]
    have : F n - 3 * φ ≤ F n := Nat.sub_le _ _
    nlinarith

/-! ### Mirror symmetry -/

lemma mx_mirror (V : Behaviour L) (x : Fin L) : mx n (mirror V) x = mx n V x := by
  apply le_antisymm
  · unfold mx
    apply Finset.sup_le
    intro q hq
    simp only [mem_filter, mem_univ, true_and] at hq
    rw [meetTime_mirror]
    exact meetTime_le_mx V hq.1 (by simpa using hq.2)
  · unfold mx
    apply Finset.sup_le
    intro q hq
    simp only [mem_filter, mem_univ, true_and] at hq
    have : meetTime n V x q.2.1 q.1 q.2.2 = meetTime n (mirror V) x (-q.2.1) q.1 (-q.2.2) := by
      rw [meetTime_mirror]; simp
    rw [this]
    exact meetTime_le_mx (mirror V) hq.1 (by simpa using hq.2)

lemma fwd_mirror (V : Behaviour L) (x : Fin L) : fwd n (mirror V) x = back n V x := by
  unfold fwd back
  simp only [disp_mirror]
  congr 1
  rw [mx_mirror]

lemma back_mirror (V : Behaviour L) (x : Fin L) : back n (mirror V) x = fwd n V x := by
  unfold fwd back
  simp only [disp_mirror, neg_neg]
  congr 1
  rw [mx_mirror]

end LBCost

open LBCost

/-- **Theorem 3.1 of [Miller–Pelc], finite form.** In the oriented ring of size `n ≥ 2`
(`E = n - 1`, `F = ⌈E/2⌉ = ⌊n/2⌋`) with simultaneous start and `L ≥ 2` labels, every
rendezvous algorithm of cost at most `E + φ` with `3φ < F` has an execution lasting at least
`(⌈L/2⌉ - 1)(F - 3φ)/2` rounds. (The paper proves `(⌊L/2⌋ - 1)(F - 3φ)/2`.) -/
theorem thm_3_1_explicit {n L φ : ℕ} [NeZero n] (hn : 2 ≤ n) (hL : 2 ≤ L) (V : Behaviour L)
    (hV : IsRendezvous n V) (hcost : CostLE n V (n - 1 + φ)) (hφ : 3 * φ < n / 2) :
    ∃ x y px py, x ≠ y ∧ px ≠ py ∧
      ((L + 1) / 2 - 1) * (n / 2 - 3 * φ) ≤ 2 * meetTime n V x px y py := by
  classical
  set S₁ := (univ : Finset (Fin L)).filter (fun c => back n V c ≤ fwd n V c)
  set S₂ := (univ : Finset (Fin L)).filter (fun c => fwd n V c ≤ back n V c)
  have hcov : S₁ ∪ S₂ = univ := by
    ext c; simp only [S₁, S₂, mem_union, mem_filter, mem_univ, true_and, iff_true]
    exact le_total _ _
  have hcard : L ≤ S₁.card + S₂.card := by
    have := card_union_le S₁ S₂
    rw [hcov, card_univ, Fintype.card_fin] at this; exact this
  have hpos : (0 : ZMod n) ≠ (F n : ZMod n) := zero_ne_F hn
  by_cases h12 : S₂.card ≤ S₁.card
  · obtain ⟨u, v, huv, hb⟩ := bound_of_heavy hn hL hV hcost hφ S₁ (by simp [S₁])
    refine ⟨min u v, max u v, 0, (F n : ZMod n), ?_, hpos, ?_⟩
    · rcases le_total u v with h | h <;> simp [h, huv, huv.symm]
    · refine le_trans ?_ hb
      apply Nat.mul_le_mul_right; omega
  · obtain ⟨u, v, huv, hb⟩ := bound_of_heavy hn hL hV.mirror hcost.mirror hφ S₂ (by
      intro c hc; simp only [S₂, mem_filter, mem_univ, true_and] at hc
      rw [fwd_mirror, back_mirror]; exact hc)
    have hneg : (0 : ZMod n) ≠ -(F n : ZMod n) := by
      intro h; apply hpos; rw [← neg_neg (F n : ZMod n), ← h, neg_zero]
    refine ⟨min u v, max u v, 0, -(F n : ZMod n), ?_, hneg, ?_⟩
    · rcases le_total u v with h | h <;> simp [h, huv, huv.symm]
    · refine le_trans ?_ (le_trans hb (le_of_eq ?_))
      · apply Nat.mul_le_mul_right; omega
      · simp only [τ, meetTime_mirror, neg_zero]

/-- **Theorem 3.1 of [Miller–Pelc], linear form.** Cost at most `E + E/7` already forces time
`Ω(E L)`: in the oriented ring of size `n ≥ 2` (`E = n - 1`) with simultaneous start and
`L ≥ 2` labels, some execution lasts at least `E L / 112` rounds. -/
theorem thm_3_1_linear {n L φ : ℕ} [NeZero n] (hn : 2 ≤ n) (hL : 2 ≤ L) (V : Behaviour L)
    (hV : IsRendezvous n V) (hcost : CostLE n V (n - 1 + φ)) (hφ : 7 * φ ≤ n - 1) :
    ∃ x y px py, x ≠ y ∧ px ≠ py ∧ (n - 1) * L ≤ 112 * meetTime n V x px y py := by
  have hφ' : 3 * φ < n / 2 := by omega
  by_cases hL4 : 4 ≤ L
  · obtain ⟨x, y, px, py, hxy, hp, hb⟩ := thm_3_1_explicit hn hL V hV hcost hφ'
    refine ⟨x, y, px, py, hxy, hp, ?_⟩
    have h1 : n - 1 ≤ 14 * (n / 2 - 3 * φ) := by omega
    have h2 : L ≤ 4 * ((L + 1) / 2 - 1) := by omega
    calc (n - 1) * L ≤ (14 * (n / 2 - 3 * φ)) * (4 * ((L + 1) / 2 - 1)) :=
          Nat.mul_le_mul h1 h2
      _ = 56 * (((L + 1) / 2 - 1) * (n / 2 - 3 * φ)) := by ring
      _ ≤ 56 * (2 * meetTime n V x px y py) := Nat.mul_le_mul_left _ hb
      _ = _ := by ring
  · have hab : (⟨0, by omega⟩ : Fin L) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have h0 := F_le_two_τ hn hV hab
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, 0, (F n : ZMod n), hab, zero_ne_F hn, ?_⟩
    have : min (⟨0, by omega⟩ : Fin L) ⟨1, by omega⟩ = ⟨0, by omega⟩ :=
      min_eq_left (by simp [Fin.le_def])
    have h' : max (⟨0, by omega⟩ : Fin L) ⟨1, by omega⟩ = ⟨1, by omega⟩ :=
      max_eq_right (by simp [Fin.le_def])
    simp only [τ, this, h'] at h0
    have hF : F n = n / 2 := rfl
    calc (n - 1) * L ≤ (n - 1) * 3 := Nat.mul_le_mul_left _ (by omega)
      _ ≤ _ := by omega

/-- **Theorem 3.1 of [Miller–Pelc]**: any deterministic rendezvous algorithm of cost `E + o(E)`
must have time `Ω(E L)`. Here `A n L` is the algorithm for the oriented ring of size `n`
(`E = n - 1`) and labels `Fin L`, with simultaneous start; its cost is at most `E + φ n L` where
`φ n L = o(n)` uniformly in `L`. -/
theorem thm_3_1 (A : ℕ → ∀ L : ℕ, Behaviour L) (φ : ℕ → ℕ → ℕ)
    (hφ : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n L : ℕ, n₀ ≤ n → (φ n L : ℝ) ≤ ε * n)
    (hA : ∀ (n L : ℕ) [NeZero n], 2 ≤ n → 2 ≤ L →
      IsRendezvous n (A n L) ∧ CostLE n (A n L) (n - 1 + φ n L)) :
    ∃ n₀ : ℕ, ∀ (n L : ℕ) [NeZero n], n₀ ≤ n → 2 ≤ L →
      ∃ x y px py, x ≠ y ∧ px ≠ py ∧ (n - 1) * L ≤ 112 * meetTime n (A n L) x px y py := by
  obtain ⟨n₀, hn₀⟩ := hφ (1 / 8) (by norm_num)
  refine ⟨max n₀ 8, fun n L _ hn hL => ?_⟩
  have hn8 : 8 ≤ n := le_of_max_le_right hn
  obtain ⟨hV, hc⟩ := hA n L (by omega) hL
  have h := hn₀ n L (le_of_max_le_left hn)
  have h7 : 7 * φ n L ≤ n - 1 := by
    have : (8 * φ n L : ℝ) ≤ n := by linarith
    have : 8 * φ n L ≤ n := by exact_mod_cast this
    omega
  exact thm_3_1_linear (by omega) hL _ hV hc h7

end Podc.RendezvousTimeCost
