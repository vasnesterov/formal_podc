import Podc.Computability.Distributed.AnonymousNetworks.Lifting

-- CSLib candidate (paper-local for now)

/-!
# Directed cycles, bidirectional rings and their coverings

* `cycleNet k`: the directed cycle `j → j + 1` on `Fin k`, with self-loops (outdegree `2`).
* `ringNet k`: the bidirectional ring `j → j ± 1` on `Fin k`, with self-loops (outdegree `3` when
  `k ≥ 3`); it is symmetric.
* `proj k n : Fin (k * n) → Fin n`, `i ↦ i mod n`, is a fibration `cycleNet (k * n) → cycleNet n`
  for `n ≥ 2` and `ringNet (k * n) → ringNet n` for `n ≥ 3`, preserving outdegrees and output ports
  (`cycleFib`, `ringFib`): these are the coverings used in the proof of Theorem 4.1, (ii) ⇒ (i).
  For `n = 2` the bidirectional ring is `K₂` (one edge between the two agents, outdegree `2`) and
  `i ↦ i mod 2` is *not* a fibration from a larger bidirectional ring, which has outdegree `3`.
* `count_ofFn_comp_proj`: every value occurs `k` times as often in the lifted input.
-/

namespace Podc.KnowYourAudience

open Cslib.AnonNet Finset

/-! ### Arithmetic in `Fin k` -/

lemma fin_one_ne_zero {k : ℕ} [NeZero k] (hk : 2 ≤ k) : (1 : Fin k) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (show 1 < k by omega)] at this

lemma fin_two_ne_zero {k : ℕ} [NeZero k] (hk : 3 ≤ k) : (2 : Fin k) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (show 2 < k by omega)] at this

lemma fin_add_one_ne {k : ℕ} [NeZero k] (hk : 2 ≤ k) (j : Fin k) : j + 1 ≠ j := by
  intro h; exact fin_one_ne_zero hk (by simpa using h)

lemma fin_sub_one_ne {k : ℕ} [NeZero k] (hk : 2 ≤ k) (j : Fin k) : j - 1 ≠ j := by
  intro h; exact fin_one_ne_zero hk (by simpa using h)

lemma fin_sub_one_ne_add_one {k : ℕ} [NeZero k] (hk : 3 ≤ k) (j : Fin k) : j - 1 ≠ j + 1 := by
  intro h
  apply fin_two_ne_zero hk
  have : j + 1 - (j - 1) = 0 := by rw [← h]; simp
  rw [← this, sub_sub_eq_add_sub, add_assoc, add_sub_cancel_left]; ext; simp [Fin.val_add]

/-- Every vertex reaches every other one along the edges `j → j + 1`. -/
theorem fin_reach {k : ℕ} [NeZero k] (R : Fin k → Fin k → Prop) (h : ∀ j, R j (j + 1))
    (a b : Fin k) : Relation.ReflTransGen R a b := by
  have hk := NeZero.pos k
  have up : ∀ (v w : ℕ) (hv : v < k) (hw : w < k), v ≤ w →
      Relation.ReflTransGen R ⟨v, hv⟩ ⟨w, hw⟩ := by
    intro v w hv hw hvw
    induction w with
    | zero =>
      obtain rfl : v = 0 := by omega
      exact .refl
    | succ w ih =>
      rcases Nat.lt_or_ge v (w + 1) with h1 | h1
      · refine (ih (by omega) (by omega)).tail ?_
        have : (⟨w, by omega⟩ : Fin k) + 1 = ⟨w + 1, hw⟩ := by
          ext; simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < k by omega), Nat.mod_eq_of_lt hw]
        rw [← this]; exact h _
      · obtain rfl : v = w + 1 := by omega
        exact .refl
  have last : Relation.ReflTransGen R ⟨k - 1, by omega⟩ 0 := by
    apply Relation.ReflTransGen.single
    have : (⟨k - 1, by omega⟩ : Fin k) + 1 = 0 := by
      ext; simp only [Fin.val_add, Fin.val_one', Fin.val_zero]
      rw [Nat.add_mod_mod, Nat.sub_add_cancel hk, Nat.mod_self]
    rw [← this]; exact h _
  rcases le_total a.val b.val with hab | hab
  · exact up _ _ a.2 b.2 hab
  · exact ((up _ _ a.2 (by omega) (by omega)).trans last).trans (up 0 _ hk b.2 (by omega))

/-! ### The networks -/

/-- The directed cycle with self-loops on `Fin k`; port `0` is the self-loop, port `1` the edge
`j → j + 1`. -/
def cycleNet (k : ℕ) [NeZero k] : Network (Fin k) where
  out j := {j, j + 1}
  self_mem j := by simp
  port j i := if i = j then 0 else 1
  port_lt j i hi := by
    split_ifs with h
    · exact Finset.card_pos.2 ⟨j, by simp⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, h, false_or] at hi
      subst hi
      rw [Finset.card_pair (Ne.symm h)]; omega
  port_injOn j := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    by_cases h1 : a = j <;> by_cases h2 : b = j <;> simp_all

/-- The bidirectional ring with self-loops on `Fin k`; ports `0, 1, 2` lead to `j, j + 1, j - 1`. -/
def ringNet (k : ℕ) [NeZero k] : Network (Fin k) where
  out j := {j, j + 1, j - 1}
  self_mem j := by simp
  port j i := if i = j then 0 else if i = j + 1 then 1 else 2
  port_lt j i hi := by
    split_ifs with h h'
    · exact Finset.card_pos.2 ⟨j, by simp⟩
    · subst h'
      have : ({j, j + 1} : Finset (Fin k)) ⊆ {j, j + 1, j - 1} := by
        intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      have := Finset.card_le_card this
      rw [Finset.card_pair (Ne.symm h)] at this; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton, h, h', false_or] at hi
      subst hi
      have hk1 : k ≠ 1 := by rintro rfl; exact h (Subsingleton.elim _ _)
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm h, hk1]),
        Finset.card_pair (by intro e; exact h' (e ▸ rfl))]
      omega
  port_injOn j := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    by_cases h1 : a = j <;> by_cases h2 : b = j <;> by_cases h3 : a = j + 1 <;>
      by_cases h4 : b = j + 1 <;> simp_all

lemma cycleNet_sc (k : ℕ) [NeZero k] : (cycleNet k).StronglyConnected :=
  fin_reach _ (fun j => by simp [Network.Adj, cycleNet])

lemma ringNet_sc (k : ℕ) [NeZero k] : (ringNet k).StronglyConnected :=
  fin_reach _ (fun j => by simp [Network.Adj, ringNet])

lemma ringNet_symmetric (k : ℕ) [NeZero k] : (ringNet k).Symmetric := by
  intro i j h
  simp only [ringNet, Finset.mem_insert, Finset.mem_singleton] at h ⊢
  rcases h with rfl | rfl | rfl
  · left; rfl
  · right; right; simp
  · right; left; simp

lemma inN_cycleNet (k : ℕ) [NeZero k] (i : Fin k) : (cycleNet k).inN i = {i, i - 1} := by
  ext j
  simp only [Network.mem_inN, cycleNet, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl) <;> simp
  · rintro (rfl | rfl) <;> simp

lemma inN_ringNet (k : ℕ) [NeZero k] (i : Fin k) : (ringNet k).inN i = {i, i - 1, i + 1} := by
  ext j
  simp only [Network.mem_inN, ringNet, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl) <;> simp
  · rintro (rfl | rfl | rfl) <;> simp

/-! ### The covering maps `i ↦ i mod n` -/

/-- `i ↦ i mod n`, from `Fin (k * n)` to `Fin n`. -/
def proj (k n : ℕ) [NeZero n] : Fin (k * n) → Fin n :=
  fun i => ⟨i.val % n, Nat.mod_lt _ (NeZero.pos n)⟩

variable {k n : ℕ} [NeZero k] [NeZero n]

omit [NeZero k] in
lemma proj_add (a b : Fin (k * n)) : proj k n (a + b) = proj k n a + proj k n b := by
  ext
  simp only [proj, Fin.val_add]
  rw [Nat.mod_mod_of_dvd _ (dvd_mul_left n k), Nat.add_mod]

lemma proj_one : proj k n 1 = 1 := by
  ext
  simp only [proj, Fin.val_one']
  rw [Nat.mod_mod_of_dvd _ (dvd_mul_left n k)]

lemma proj_add_one (a : Fin (k * n)) : proj k n (a + 1) = proj k n a + 1 := by
  rw [proj_add, proj_one]

lemma proj_sub_one (a : Fin (k * n)) : proj k n (a - 1) = proj k n a - 1 := by
  have := proj_add (k := k) (n := n) (a - 1) 1
  rw [sub_add_cancel, proj_one] at this
  rw [this, add_sub_cancel_right]

omit [NeZero n] in
lemma le_mul_of_neZero : n ≤ k * n := Nat.le_mul_of_pos_left n (NeZero.pos k)

lemma bijOn_of_image_eq {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β}
    (f : α → β) (h : s.image f = t) (hc : t.card = s.card) : Set.BijOn f s t := by
  have inj : Set.InjOn f s := Finset.card_image_iff.1 (h ▸ hc)
  have := inj.bijOn_image
  rwa [← Finset.coe_image, h] at this

/-- `i ↦ i mod n` is a fibration of directed cycles `C_{kn} → C_n` (`n ≥ 2`). -/
def cycleFib (hn : 2 ≤ n) : Fibration (cycleNet (k * n)) (cycleNet n) where
  toFun := proj k n
  surjective j := ⟨⟨j.val, lt_of_lt_of_le j.2 le_mul_of_neZero⟩,
    by ext; simp [proj, Nat.mod_eq_of_lt j.2]⟩
  bijOn i := by
    have hkn : 2 ≤ k * n := le_trans hn le_mul_of_neZero
    rw [inN_cycleNet, inN_cycleNet]
    apply bijOn_of_image_eq
    · simp [Finset.image_insert, proj_sub_one]
    · rw [Finset.card_pair (fin_sub_one_ne hn _).symm, Finset.card_pair (fin_sub_one_ne hkn _).symm]

lemma cycleFib_compatible (hn : 2 ≤ n) (m : CommModel) :
    (cycleFib (k := k) hn).Compatible m := by
  have hkn : 2 ≤ k * n := le_trans hn le_mul_of_neZero
  have hdeg : ∀ j, (cycleNet n).outdeg (proj k n j) = (cycleNet (k * n)).outdeg j := by
    intro j
    simp only [Network.outdeg, cycleNet]
    rw [Finset.card_pair (fin_add_one_ne hn _).symm, Finset.card_pair (fin_add_one_ne hkn _).symm]
  cases m with
  | broadcast => trivial
  | symmetric => trivial
  | outdegree => exact hdeg
  | outPort =>
    refine fun j => ⟨hdeg j, fun i hi => ?_⟩
    simp only [cycleNet, Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [cycleFib, cycleNet]
    rcases hi with rfl | rfl
    · simp
    · rw [proj_add_one]; simp [fin_add_one_ne hn, fin_add_one_ne hkn]

/-- `i ↦ i mod n` is a fibration of bidirectional rings `R_{kn} → R_n` (`n ≥ 3`). -/
def ringFib (hn : 3 ≤ n) : Fibration (ringNet (k * n)) (ringNet n) where
  toFun := proj k n
  surjective j := ⟨⟨j.val, lt_of_lt_of_le j.2 le_mul_of_neZero⟩,
    by ext; simp [proj, Nat.mod_eq_of_lt j.2]⟩
  bijOn i := by
    have hkn : 3 ≤ k * n := le_trans hn le_mul_of_neZero
    rw [inN_ringNet, inN_ringNet]
    apply bijOn_of_image_eq
    · simp [Finset.image_insert, proj_sub_one, proj_add_one]
    · have card3 : ∀ {m : ℕ} [NeZero m], 3 ≤ m → ∀ a : Fin m,
          ({a, a - 1, a + 1} : Finset _).card = 3 :=
        by
        intro m _ hm a
        rw [Finset.card_insert_of_notMem, Finset.card_pair (fin_sub_one_ne_add_one hm a)]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨(fin_sub_one_ne (by omega) a).symm, (fin_add_one_ne (by omega) a).symm⟩
      rw [card3 hn, card3 hkn]

lemma ringFib_compatible (hn : 3 ≤ n) (m : CommModel) :
    (ringFib (k := k) hn).Compatible m := by
  have hkn : 3 ≤ k * n := le_trans hn le_mul_of_neZero
  have card3 : ∀ {m : ℕ} [NeZero m], 3 ≤ m → ∀ a : Fin m,
      ({a, a + 1, a - 1} : Finset _).card = 3 := by
    intro m _ hm a
    rw [Finset.card_insert_of_notMem, Finset.card_pair (fin_sub_one_ne_add_one hm a).symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(fin_add_one_ne (by omega) a).symm, (fin_sub_one_ne (by omega) a).symm⟩
  have hdeg : ∀ j, (ringNet n).outdeg (proj k n j) = (ringNet (k * n)).outdeg j := by
    intro j
    simp only [Network.outdeg, ringNet]
    rw [card3 hn, card3 hkn]
  cases m with
  | broadcast => trivial
  | symmetric => trivial
  | outdegree => exact hdeg
  | outPort =>
    refine fun j => ⟨hdeg j, fun i hi => ?_⟩
    simp only [ringNet, Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [ringFib, ringNet]
    rcases hi with rfl | rfl | rfl
    · simp
    · rw [proj_add_one]
      simp [fin_add_one_ne (by omega : 2 ≤ n), fin_add_one_ne (by omega : 2 ≤ k * n)]
    · rw [proj_sub_one]
      simp [fin_sub_one_ne (by omega : 2 ≤ n), fin_sub_one_ne (by omega : 2 ≤ k * n),
        fin_sub_one_ne_add_one hn, fin_sub_one_ne_add_one hkn]

omit [NeZero k] in
/-- In the lifted input `x ∘ proj`, every value occurs `k` times as often as in `x`. -/
lemma count_ofFn_comp_proj {I : Type*} [DecidableEq I] (x : Fin n → I) (a : I) :
    (List.ofFn (x ∘ proj k n)).count a = k * (List.ofFn x).count a := by
  rw [count_ofFn, count_ofFn]
  have h1 : (univ.filter (fun i => (x ∘ proj k n) i = a)) =
      (univ ×ˢ univ.filter (fun j => x j = a)).map
        (finProdFinEquiv (m := k) (n := n)).toEmbedding := by
    ext i
    simp only [Function.comp, mem_filter, mem_univ, true_and, mem_map_equiv, mem_product]
    have : proj k n i = (finProdFinEquiv.symm i).2 := by
      ext; simp [proj, finProdFinEquiv]
    rw [this]
  rw [h1, card_map, card_product, card_univ, Fintype.card_fin]

end Podc.KnowYourAudience
