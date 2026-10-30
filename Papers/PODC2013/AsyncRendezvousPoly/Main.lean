import Papers.PODC2013.AsyncRendezvousPoly.Sync2
import Papers.PODC2013.AsyncRendezvousPoly.Labels

/-!
# Lemma 3.1 and Theorem 3.1

Dieudonné, Pelc, Villain, *How to meet asynchronously at polynomial cost*, PODC 2013
(arXiv:1301.7119v2), §3.2.

* `lemma_3_1`, `lemma_3_1_Y`: the catching lemma for `X` and `Y`.
* `theorem_3_1_explicit`: two agents with distinct positive labels `L₁`, `L₂` executing
  Algorithm RV-asynch-poly in a connected graph of size `n`, against any adversary (any walks
  `Wa`, `Wb`), meet no later than the moment one of them completes its `Π`-th edge traversal, where
  `Π = piBound P (2(n + l) + 1)`, `l = 2 min(|L₁|, |L₂|) + 2` (the first `2(n+l)+1` iterations).
* `theorem_3_1`: if `P` is polynomially bounded, `Π(n, m) = C (n + m + 1)^d`.
-/

namespace Podc.AsyncRendezvousPoly

open Traj Set

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {P : ℕ → ℕ}

omit [Fintype V] in
/-- **Lemma 3.1** of [DPV13]. If during the time interval `I = [s, e]` agent `b` keeps repeating
`X(m, v)` (its route repeats `X(m, v)` `c` times from index `β`, and it is inside this repetition
during `I`) and agent `a` follows an entire trajectory `X(m, v)` (occurring at index `α` of its
route) during `I`, then the agents meet during `I`. -/
theorem lemma_3_1 (E : Explorer G P) {m : ℕ} {v : V} {ra rb : ℕ → V} {Wa Wb : Walk}
    {α β c : ℕ} {s e : ℝ} (ha : Occ (E.X m v) ra α) (hb : Occ (pow (E.X m v) c) rb β)
    (hb1 : Wb.τ β ≤ s) (hb2 : e ≤ Wb.τ (β + (pow (E.X m v) c).len))
    (ha1 : s ≤ Wa.τ α) (ha2 : Wa.τ (α + (E.X m v).len) ≤ e) :
    ∃ t ∈ Icc s e, Meet ra rb Wa Wb t := by
  have hR : Occ (E.R m v) ra α := by simpa using (occIn_append_left _ _).occ ha
  have hrep : RepOcc (E.R m v) c β rb := RepOcc.of_occ hb
  have hlen : (pow (E.X m v) c).len = c * (2 * (E.R m v).len) := by
    rw [pow_len]; simp [Explorer.X]
  have hXR : (E.R m v).len ≤ (E.X m v).len := by simp [Explorer.X]; omega
  obtain ⟨t, ht, hte⟩ := meet_of_rep (by rw [E.len_eq]; exact E.P_pos m) hR hrep
    (hb1.trans ha1) ((Wa.τ_le (by omega)).trans (ha2.trans (hlen ▸ hb2)))
  exact ⟨t, ⟨ha1.trans hte.1, hte.2.trans ((Wa.τ_le (by omega)).trans ha2)⟩, ht⟩

omit [Fintype V] in
/-- **Lemma 3.1** of [DPV13], the version for `Y`. -/
theorem lemma_3_1_Y (E : Explorer G P) {m : ℕ} {v : V} {ra rb : ℕ → V} {Wa Wb : Walk}
    {α β c : ℕ} {s e : ℝ} (ha : Occ (E.Y m v) ra α) (hb : Occ (pow (E.Y m v) c) rb β)
    (hb1 : Wb.τ β ≤ s) (hb2 : e ≤ Wb.τ (β + (pow (E.Y m v) c).len))
    (ha1 : s ≤ Wa.τ α) (ha2 : Wa.τ (α + (E.Y m v).len) ≤ e) :
    ∃ t ∈ Icc s e, Meet ra rb Wa Wb t := by
  have hR : Occ (E.Y' m v) ra α := by simpa using (occIn_append_left _ _).occ ha
  have hrep : RepOcc (E.Y' m v) c β rb := RepOcc.of_occ hb
  have hlen : (pow (E.Y m v) c).len = c * (2 * (E.Y' m v).len) := by
    rw [pow_len]; simp [Explorer.Y]
  have hXR : (E.Y' m v).len ≤ (E.Y m v).len := by simp [Explorer.Y]; omega
  have hT : 1 ≤ (E.Y' m v).len := by rw [E.Y'_len]; unfold lenY'; have := E.P_pos m; omega
  obtain ⟨t, ht, hte⟩ := meet_of_rep hT hR hrep
    (hb1.trans ha1) ((Wa.τ_le (by omega)).trans (ha2.trans (hlen ▸ hb2)))
  exact ⟨t, ⟨ha1.trans hte.1, hte.2.trans ((Wa.τ_le (by omega)).trans ha2)⟩, ht⟩

/-! ### Theorem 3.1 -/

variable {E : Explorer G P}

/-- The core of the proof of Theorem 3.1, with `y` the first agent to complete its `(2 N0)`-th
fence: the agents meet before one of them completes its `(2 N0 + 1)`-th piece. -/
theorem core (hG : G.Connected) (hP : Monotone P) {x y : Agent V} (hx : x.bits ≠ [])
    (hy : y.bits ≠ []) {N0 l d : ℕ} (hN0 : Fintype.card V + l ≤ N0)
    (hlx : l ≤ x.bits.length) (hly : l ≤ y.bits.length) (hd1 : 1 ≤ d) (hdl : d < l)
    (hd : bit x.bits d ≠ bit y.bits d)
    (hfirst : y.W.τ (iS P y.bits (2 * N0 + 1)) ≤ x.W.τ (iS P x.bits (2 * N0 + 1)))
    (hno : NoMeet E x y (fS P x.bits (2 * N0 + 1)) (fS P y.bits (2 * N0 + 1))) : False := by
  have hP1 := E.P_pos
  have hN0' : Fintype.card V ≤ N0 := by omega
  have hEx := iS_le_fS x.bits hP1 hx (show 1 ≤ 2 * N0 + 1 by omega)
  have hEy := iS_le_fS y.bits hP1 hy (show 1 ≤ 2 * N0 + 1 by omega)
  obtain ⟨j, hj1, hj2, hM, hN⟩ := lemma_3_3 hG hP hx hy hN0' hfirst hno hEx hEy
  have h34 := lemma_3_4 hP hx hy hN0' hfirst hno hEx hEy hj1 hj2 hM
  have h35 := lemma_3_5 hG hx hy hN0' hno hEx le_rfl hj1 hj2 h34
  have hsx : d < nSeg x.bits (j + 1) := by unfold nSeg; omega
  have hsy : d < nSeg y.bits (2 * N0 + 1) := by unfold nSeg; omega
  obtain ⟨-, -, p3, p4⟩ := lemma_3_6 hG hP hx hy hN0' hno hj1 hj2 hN h35 (d - 1)
    (by rw [Nat.sub_add_cancel hd1]; exact hsx) (by rw [Nat.sub_add_cancel hd1]; exact hsy)
  rw [Nat.sub_add_cancel hd1] at p3 p4
  have hfx : fS P x.bits (j + 1) ≤ fS P x.bits (2 * N0 + 1) :=
    fS_mono x.bits hP1 hx (by omega) (by omega)
  cases hbx : bit x.bits d
  · have hby : bit y.bits d = true := by
      cases h : bit y.bits d
      · exact absurd (hbx.trans h.symm) hd
      · rfl
    obtain ⟨t, ht, htx, hty⟩ := meet_of_diff_bits hG hP hy hx (x := y) (y := x)
      (kx := 2 * N0 + 1) (ky := j + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      hsy hsx hby hbx p4 p3
    exact hno.symm.elim ht htx (segE_le_fS P y.bits _ d hsy) hty
      ((segE_le_fS P x.bits _ d hsx).trans hfx)
  · have hby : bit y.bits d = false := by
      cases h : bit y.bits d
      · rfl
      · exact absurd (hbx.trans h.symm) hd
    obtain ⟨t, ht, htx, hty⟩ := meet_of_diff_bits hG hP hx hy (x := x) (y := y)
      (kx := j + 1) (ky := 2 * N0 + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      hsx hsy hbx hby p3 p4
    exact hno.elim ht htx ((segE_le_fS P x.bits _ d hsx).trans hfx) hty
      (segE_le_fS P y.bits _ d hsy)

/-- **Theorem 3.1** of [DPV13], explicit form. Let `G` be a connected graph of size `n`, let
`R(k, ·)` be any exploration family with step counts `P` (`P` non-decreasing), and let two agents
with distinct positive labels `L₁`, `L₂` start at nodes `va`, `vb` and execute Algorithm
RV-asynch-poly. For every adversary (walks `Wa`, `Wb`), the agents meet at some time `t` no later
than the moment one of them completes its `Π`-th edge traversal, where
`Π = piBound P (2(n + l) + 1)` and `l = 2 min(|L₁|, |L₂|) + 2`. -/
theorem theorem_3_1_explicit (hG : G.Connected) (hP : Monotone P) (E : Explorer G P)
    {L₁ L₂ : ℕ} (h₁ : 0 < L₁) (h₂ : 0 < L₂) (hne : L₁ ≠ L₂) (va vb : V) (Wa Wb : Walk) :
    ∃ t, Meet (E.route (modLabel L₁) va) (E.route (modLabel L₂) vb) Wa Wb t ∧
      t ≤ Wa.τ (piBound P (2 * (Fintype.card V + (2 * min (binLen L₁) (binLen L₂) + 2)) + 1)) ∧
      t ≤ Wb.τ (piBound P (2 * (Fintype.card V + (2 * min (binLen L₁) (binLen L₂) + 2)) + 1)) := by
  have hP1 := E.P_pos
  set l := 2 * min (binLen L₁) (binLen L₂) + 2 with hl
  set N0 := Fintype.card V + l
  let a : Agent V := ⟨modLabel L₁, va, Wa⟩
  let b : Agent V := ⟨modLabel L₂, vb, Wb⟩
  have ha : a.bits ≠ [] := modLabel_ne_nil L₁
  have hb : b.bits ≠ [] := modLabel_ne_nil L₂
  have hla : l ≤ a.bits.length := by
    show l ≤ (modLabel L₁).length; rw [modLabel_length]; omega
  have hlb : l ≤ b.bits.length := by
    show l ≤ (modLabel L₂).length; rw [modLabel_length]; omega
  obtain ⟨d, hd1, hd2, hd⟩ := exists_bit_ne h₁ h₂ hne
  have hdl : d < l := by
    rw [modLabel_length, modLabel_length] at hd2; omega
  by_contra hcon
  have hno : NoMeet E a b (fS P a.bits (2 * N0 + 1)) (fS P b.bits (2 * N0 + 1)) := by
    intro t ht h1 h2
    exact hcon ⟨t, ht, h1.trans (Wa.τ_le (fS_le_piBound _ hP hP1 ha (by omega))),
      h2.trans (Wb.τ_le (fS_le_piBound _ hP hP1 hb (by omega)))⟩
  by_cases hf : b.W.τ (iS P b.bits (2 * N0 + 1)) ≤ a.W.τ (iS P a.bits (2 * N0 + 1))
  · exact core hG hP ha hb (l := l) le_rfl hla hlb hd1 hdl hd hf hno
  · exact core hG hP hb ha (l := l) le_rfl hlb hla hd1 hdl (Ne.symm hd) (not_le.1 hf).le hno.symm

/-- **Theorem 3.1** of [DPV13]. Assume Reingold's procedure (any exploration family `R(k, ·)`
whose step count `P(k)` is non-decreasing and polynomially bounded). There is a polynomial
`Π(n, m) = C (n + m + 1)^d`, non-decreasing in each variable, such that if two agents with distinct
positive labels `L₁`, `L₂` execute Algorithm RV-asynch-poly in any connected graph of size `n`,
then for every adversary their meeting occurs no later than the moment one of them performs
`Π(n, min(|L₁|, |L₂|))` edge traversals. -/
theorem theorem_3_1 (P : ℕ → ℕ) (hP : Monotone P) (hpoly : PolyBounded P) :
    ∃ C d : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.Connected →
      ∀ (E : Explorer G P) (L₁ L₂ : ℕ), 0 < L₁ → 0 < L₂ → L₁ ≠ L₂ → ∀ (va vb : V) (Wa Wb : Walk),
      ∃ t, Meet (E.route (modLabel L₁) va) (E.route (modLabel L₂) vb) Wa Wb t ∧
        t ≤ Wa.τ (C * (Fintype.card V + min (binLen L₁) (binLen L₂) + 1) ^ d) ∧
        t ≤ Wb.τ (C * (Fintype.card V + min (binLen L₁) (binLen L₂) + 1) ^ d) := by
  obtain ⟨C, d, hC⟩ := piBound_poly hpoly
  refine ⟨C, d, fun V _ _ G hG E L₁ L₂ h₁ h₂ hne va vb Wa Wb => ?_⟩
  obtain ⟨t, ht, h1, h2⟩ := theorem_3_1_explicit hG hP E h₁ h₂ hne va vb Wa Wb
  have hb := hC (Fintype.card V) (min (binLen L₁) (binLen L₂))
  exact ⟨t, ht, h1.trans (Wa.τ_le hb), h2.trans (Wb.τ_le hb)⟩

end Podc.AsyncRendezvousPoly
