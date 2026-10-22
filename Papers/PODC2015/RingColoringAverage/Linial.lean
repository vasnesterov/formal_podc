import Papers.PODC2015.RingColoringAverage.Model
import Podc.Foundations.Combinatorics.ShiftGraph

/-!
# Linial's lower bound for colouring rings, in the variable-radius model

Linial's `Ω(log* n)` lower bound, in the form needed for the paper's §3: for every valid colouring
algorithm with colour set `C` and every set `S` of identifiers that is larger than
`(2 ^ ·)^[2t] |C|`, some node of some ring with identifier set exactly `S` has radius `> t`.

Proof: if all nodes of all rings with identifiers `S` stop within radius `t`, the output on the
window `[-t, t]` defines a colouring of the `(2t+1)`-tuples of identifiers, and it is a proper
colouring of the shift graph (two consecutive windows of a ring are adjacent nodes), so
`Cslib.ShiftGraph.card_le_iterate_of_proper` bounds `|S|`.

## Main statements

* `Alg.exists_lt_radAt`: the lower bound for an arbitrary colour set `C`.
* `Alg.exists_lt_radAt_four`, `Alg.exists_lt_radAt_three`: the cases `C = Fin 4`, `C = Fin 3`
  with the bound `Nat.tower (2t + 2) < |S|`.
-/

namespace Podc.RingColoringAverage

open Cslib

/-- The view encoded by a list `l` of identifiers read at offsets `-t, …, l.length - t - 1`
(`0` elsewhere): offset `j` carries `l[j + t]`. -/
def listView (t : ℕ) (l : List ℕ) : ℤ → ℕ := fun j => l.getD (j + t).toNat 0

/-- If the identifiers of `R` at positions `s, s + 1, …, s + 2t` are `b 0, …, b (2t)`, then the
view of node `s + t` agrees with `listView t (List.ofFn b)` on `[-t, t]`. -/
theorem agreeOn_listView (R : IdRing) (t s : ℕ) (b : Fin (2 * t + 1) → ℕ)
    (h : ∀ i : Fin (2 * t + 1), R.id ((s + i : ℕ) : ℤ) = b i) :
    AgreeOn t (R.view ((s + t : ℕ) : ℤ)) (listView t (List.ofFn b)) := by
  intro j hj
  rw [abs_le] at hj
  have hi : (j + t).toNat < 2 * t + 1 := by omega
  have e : (((s + t : ℕ) : ℤ) + j) = ((s + (j + t).toNat : ℕ) : ℤ) := by omega
  simp only [IdRing.view_apply, listView, e, h ⟨_, hi⟩]
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

theorem le_iterate_two_pow (m c : ℕ) : c ≤ (fun c => 2 ^ c)^[m] c := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (Nat.lt_two_pow_self).le

/-- A valid colouring algorithm needs at least two colours. -/
theorem Alg.Valid.two_le_card {C : Type*} [Fintype C] [Inhabited C] {A : Alg C}
    (hA : A.Valid) : 2 ≤ Fintype.card C := by
  have h := hA.proper (IdRing.ofList [0, 1, 2] (by decide) (by decide)) 0
  exact Fintype.one_lt_card_iff.2 ⟨_, _, h⟩

/-- Linial's lower bound (used in §3 of the paper): if `|S| > (2 ^ ·)^[2t] |C|`, then for every
valid colouring algorithm with colours `C` some node of some ring whose identifiers are exactly
the elements of `S` has radius greater than `t`. -/
theorem Alg.exists_lt_radAt {C : Type*} [Fintype C] [Inhabited C] (A : Alg C) (hA : A.Valid)
    (S : Finset ℕ) (t : ℕ) (hS : (fun c => 2 ^ c)^[2 * t] (Fintype.card C) < S.card) :
    ∃ R : IdRing, R.n = S.card ∧ (∀ j, R.id j ∈ S) ∧ ∃ v : ℤ, t < A.radAt R v := by
  classical
  by_contra H
  push Not at H
  have h3 : 3 ≤ S.card := by
    have := hA.two_le_card; have := le_iterate_two_pow (2 * t) (Fintype.card C); omega
  let φ : (Fin (2 * t + 1) → ℕ) → C := fun b => A.output (listView t (List.ofFn b))
  have hφ : ShiftGraph.IsProper (S : Set ℕ) (2 * t) φ := by
    intro a ha haS
    -- the ring: `a 0, …, a (2t+1)`, followed by the other elements of `S`
    let T := S \ Finset.univ.image a
    have himg : Finset.univ.image a ⊆ S := by
      intro x hx; obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx; exact haS i
    have hcard : (Finset.univ.image a).card = 2 * t + 2 := by
      rw [Finset.card_image_of_injective _ ha.injective]; simp
    let L := List.ofFn a ++ T.sort
    have hLn : L.length = S.card := by
      simp only [L, List.length_append, List.length_ofFn, Finset.length_sort, T,
        Finset.card_sdiff_of_subset himg, hcard]
      have : 2 * t + 2 ≤ S.card := hcard ▸ Finset.card_le_card himg
      omega
    have hL : L.Nodup := by
      refine List.nodup_append.2 ⟨List.nodup_ofFn.2 ha.injective, Finset.sort_nodup _ _, ?_⟩
      intro x hx y hy hxy
      subst hxy
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      have := (Finset.mem_sdiff.1 (Finset.mem_sort _ |>.1 hy)).2
      exact this (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hL3 : 3 ≤ L.length := hLn ▸ h3
    let R := IdRing.ofList L hL hL3
    have hRS : ∀ j, R.id j ∈ S := by
      intro j
      have hn : (0 : ℤ) < L.length := by omega
      have h0 := Int.emod_nonneg j hn.ne'
      have h1 := Int.emod_lt_of_pos j hn
      have hk : (j % L.length).toNat < L.length := by omega
      show L.getD (j % L.length).toNat 0 ∈ S
      rw [List.getD_eq_getElem _ _ hk]
      rcases List.mem_append.1 (List.getElem_mem hk) with hx | hx
      · obtain ⟨i, hi⟩ := List.mem_ofFn.1 hx; rw [← hi]; exact haS i
      · exact (Finset.mem_sdiff.1 (Finset.mem_sort _ |>.1 hx)).1
    have hRa : ∀ k : Fin (2 * t + 2), R.id ((k : ℕ) : ℤ) = a k := by
      intro k
      have hk : (k : ℕ) < (List.ofFn a).length := by simp [k.isLt]
      have hkL : (k : ℕ) < L.length := by simp only [L, List.length_append]; omega
      rw [IdRing.ofList_id _ _ _ _ hkL, List.getElem_append_left hk,
        List.getElem_ofFn]
    have hv : ∀ (s : ℕ) (b : Fin (2 * t + 1) → ℕ),
        (∀ i : Fin (2 * t + 1), R.id ((s + i : ℕ) : ℤ) = b i) →
        A.outAt R ((s + t : ℕ) : ℤ) = φ b := by
      intro s b hb
      exact (Alg.output_eq_of_agreeOn (agreeOn_listView R t s b hb) (hA.stops R _)
        (H R hLn hRS _)).symm
    have e0 := hv 0 (a ∘ Fin.castSucc) fun i => by
      simpa using hRa (Fin.castSucc i)
    have e1 := hv 1 (a ∘ Fin.succ) fun i => by
      have := hRa (Fin.succ i)
      simp only [Fin.val_succ] at this
      simpa [Nat.add_comm] using this
    have hp := hA.proper R ((0 + t : ℕ) : ℤ)
    rw [e0, show ((0 + t : ℕ) : ℤ) + 1 = ((1 + t : ℕ) : ℤ) by omega, e1] at hp
    exact hp
  have := ShiftGraph.card_le_iterate_of_proper S (2 * t) φ hφ
  omega

theorem iterate_two_pow_eq_tower (m k : ℕ) :
    (fun c => 2 ^ c)^[m] (Nat.tower k) = Nat.tower (m + k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, show m + 1 + k = m + k + 1 by omega]
    rfl

/-- Linial's lower bound for 4-colouring algorithms: if `|S| > tower (2t + 2)`, some node of some
ring with identifier set `S` has radius `> t`. -/
theorem Alg.exists_lt_radAt_four (A : Alg (Fin 4)) (hA : A.Valid) (S : Finset ℕ) (t : ℕ)
    (hS : Nat.tower (2 * t + 2) < S.card) :
    ∃ R : IdRing, R.n = S.card ∧ (∀ j, R.id j ∈ S) ∧ ∃ v : ℤ, t < A.radAt R v := by
  refine A.exists_lt_radAt hA S t ?_
  have h4 : Fintype.card (Fin 4) = Nat.tower 2 := by decide
  rwa [h4, iterate_two_pow_eq_tower]

/-- Linial's lower bound for 3-colouring algorithms: if `|S| > tower (2t + 2)`, some node of some
ring with identifier set `S` has radius `> t`. -/
theorem Alg.exists_lt_radAt_three (A : Alg (Fin 3)) (hA : A.Valid) (S : Finset ℕ) (t : ℕ)
    (hS : Nat.tower (2 * t + 2) < S.card) :
    ∃ R : IdRing, R.n = S.card ∧ (∀ j, R.id j ∈ S) ∧ ∃ v : ℤ, t < A.radAt R v :=
  (A.map Fin.castSucc).exists_lt_radAt_four (hA.map (Fin.castSucc_injective 3)) S t hS
    |>.imp fun R ⟨hn, hid, v, hv⟩ => ⟨hn, hid, v, by rwa [Alg.radAt, Alg.rad_map] at hv⟩

end Podc.RingColoringAverage
