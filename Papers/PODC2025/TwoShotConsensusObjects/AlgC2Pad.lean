import Papers.PODC2025.TwoShotConsensusObjects.Model

/-!
# Class `C₂`, sufficiency: padding (Lemma 2) and derived distinguishability facts

* `C2At O m s f g n c` — the body of `C2Cond` for a fixed witness;
* `C2At.pad` — **Lemma 2** of the paper: the sequence `c₀, …, cₙ` can be extended to
  `c₀, …, c_{3^k}` with `k ≥ 1` (we take `k = n`), by repeating `c_{n-1}, cₙ`;
* response-level consequences of the properties used by the decision procedure of Algorithm 3
  (Corollary 1 and the facts used in the proof of Lemma 4).
-/

namespace TwoShotCons

open Cslib.SharedMemory

variable {O : ObjSpec} {m : Fin 2 → Set O.Op}

/-- The four pairs of property (2) of class `C₂` for two (tagged) operations `x`, `y`. -/
def Pair4 (O : ObjSpec) (s : O.State) (f g : O.Op) (x y : Fin 2 × O.Op) : Prop :=
  DistBoth O s [(0, f), (1, g), x, y] [(1, g), (0, f), x, y] ∧
  DistBoth O s [(0, f), (1, g), x, y] [(1, g), (0, f), y, x] ∧
  DistBoth O s [(0, f), (1, g), y, x] [(1, g), (0, f), x, y] ∧
  DistBoth O s [(0, f), (1, g), y, x] [(1, g), (0, f), y, x]

lemma Pair4.symm {s : O.State} {f g : O.Op} {x y : Fin 2 × O.Op} (h : Pair4 O s f g x y) :
    Pair4 O s f g y x := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h4, h3, h2, h1⟩

/-- The properties of class `C₂` for a fixed witness `s, f, g, n, c` (the body of `C2Cond`). -/
def C2At (O : ObjSpec) (m : Fin 2 → Set O.Op) (s : O.State) (f g : O.Op) (n : ℕ)
    (c : ℕ → O.Op) : Prop :=
  Odd n ∧ f ∈ m 0 ∧ g ∈ m 1 ∧ (∀ i ≤ n, c i ∈ m (own i)) ∧
    ¬ Dist O s 0 [(0, f), (1, g)] [(1, g), (0, f)] ∧
    ¬ Dist O s 1 [(0, f), (1, g)] [(1, g), (0, f)] ∧
    (∀ i < n,
      DistBoth O s [(0, f), (1, g), (own i, c i), (own (i + 1), c (i + 1))]
        [(1, g), (0, f), (own i, c i), (own (i + 1), c (i + 1))] ∧
      DistBoth O s [(0, f), (1, g), (own i, c i), (own (i + 1), c (i + 1))]
        [(1, g), (0, f), (own (i + 1), c (i + 1)), (own i, c i)] ∧
      DistBoth O s [(0, f), (1, g), (own (i + 1), c (i + 1)), (own i, c i)]
        [(1, g), (0, f), (own i, c i), (own (i + 1), c (i + 1))] ∧
      DistBoth O s [(0, f), (1, g), (own (i + 1), c (i + 1)), (own i, c i)]
        [(1, g), (0, f), (own (i + 1), c (i + 1)), (own i, c i)]) ∧
    DistBoth O s [(0, f), (0, c 0), (1, g), (1, c 1)] [(1, g), (0, f), (0, c 0), (1, c 1)] ∧
    (Dist O s 1 [(0, f), (0, c 0), (1, g)] [(1, g)] ∨
      DistBoth O s [(0, f), (0, c 0), (1, g), (1, c 1)] [(1, g), (0, f), (1, c 1), (0, c 0)]) ∧
    DistBoth O s [(1, g), (1, c n), (0, f), (0, c (n - 1))]
      [(0, f), (1, g), (1, c n), (0, c (n - 1))] ∧
    (Dist O s 0 [(1, g), (1, c n), (0, f)] [(0, f)] ∨
      DistBoth O s [(1, g), (1, c n), (0, f), (0, c (n - 1))]
        [(0, f), (1, g), (0, c (n - 1)), (1, c n)])

lemma c2Cond_iff : C2Cond O m ↔ ∃ s f g n c, C2At O m s f g n c := Iff.rfl

lemma own_eq_of_mod {i j : ℕ} (h : i % 2 = j % 2) : own i = own j := by
  simp [own, h]

/-- **Lemma 2** (padding): a `C₂` witness with `n` odd yields one with `n = 3 ^ k`, `k ≥ 1`
(we take `k = n`), obtained by repeating `c_{n-1}, c_n`. -/
theorem C2At.pad {s : O.State} {f g : O.Op} {n : ℕ} {c : ℕ → O.Op}
    (h : C2At O m s f g n c) :
    ∃ k, 1 ≤ k ∧ ∃ c' : ℕ → O.Op, C2At O m s f g (3 ^ k) c' := by
  obtain ⟨hn, hf, hg, hc, h1a, h1b, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨n', rfl⟩ := hn
  set n := 2 * n' + 1 with hn
  set c' : ℕ → O.Op := fun i =>
    if i ≤ n then c i else if (i - n) % 2 = 1 then c (n - 1) else c n with hc'
  have hN : n ≤ 3 ^ n := (Nat.lt_pow_self (by norm_num)).le
  have hNodd : (3 ^ n) % 2 = 1 := by
    rw [Nat.pow_mod]; norm_num
  have hcN : c' (3 ^ n) = c n := by
    simp only [hc']
    split_ifs with h1 h2
    · rw [le_antisymm h1 hN]
    · omega
    · rfl
  have hcN1 : c' (3 ^ n - 1) = c (n - 1) := by
    simp only [hc']
    split_ifs with h1 h2
    · rw [show 3 ^ n - 1 = n - 1 by omega]
    · rfl
    · omega
  -- tagged operations beyond `n`
  have htag : ∀ i, n ≤ i →
      ((own i, c' i) = (own n, c n) ∧ (own (i + 1), c' (i + 1)) = (own (n - 1), c (n - 1))) ∨
      ((own i, c' i) = (own (n - 1), c (n - 1)) ∧ (own (i + 1), c' (i + 1)) = (own n, c n)) := by
    intro i hi
    rcases Nat.even_or_odd (i - n) with ⟨t, ht⟩ | ⟨t, ht⟩
    · left
      refine ⟨Prod.ext (own_eq_of_mod (by omega)) ?_, Prod.ext (own_eq_of_mod (by omega)) ?_⟩
      · simp only [hc']; split_ifs <;> first | rfl | (congr 1; omega)
      · simp only [hc']; split_ifs <;> first | rfl | (congr 1; omega)
    · right
      refine ⟨Prod.ext (own_eq_of_mod (by omega)) ?_, Prod.ext (own_eq_of_mod (by omega)) ?_⟩
      · simp only [hc']; split_ifs <;> first | rfl | (congr 1; omega)
      · simp only [hc']; split_ifs <;> first | rfl | (congr 1; omega)
  have hc0 : c' 0 = c 0 := by simp [hc']
  have hc1 : c' 1 = c 1 := by simp [hc']
  refine ⟨n, by omega, c', Odd.pow (by decide), hf, hg, ?_, h1a, h1b, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hin : i ≤ n
    · simpa [hc', hin] using hc i hin
    · rcases htag i (by omega) with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
        · simp only [Prod.mk.injEq] at h1
          rw [h1.1, h1.2]
          exact hc _ (by omega)
  · intro i hi
    by_cases hin : i + 1 ≤ n
    · have e1 : c' i = c i := by simp [hc']; omega
      have e2 : c' (i + 1) = c (i + 1) := by simp [hc', hin]
      rw [e1, e2]; exact h2 i (by omega)
    · have hp : Pair4 O s f g (own (n - 1), c (n - 1)) (own n, c n) := by
        have := h2 (n - 1) (by omega)
        rwa [show n - 1 + 1 = n by omega] at this
      have key : Pair4 O s f g (own i, c' i) (own (i + 1), c' (i + 1)) := by
        rcases htag i (by omega) with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2]; exact hp.symm
        · rw [e1, e2]; exact hp
      exact key
  · rwa [hc0, hc1]
  · rwa [hc0, hc1]
  · rwa [hcN, hcN1]
  · rwa [hcN, hcN1]

/-! ## Response-level consequences -/

section Facts

variable {s : O.State} {f g : O.Op}

/-- The responses of `x` after `fg[y]` and `gf[y]` differ (the four pairs of property (2), seen
by the caller of `x`), provided `f` and `g` respond identically in `fg` and `gf`. -/
lemma Pair4.resp_ne {p q : Fin 2} {x y : O.Op} (hP : Pair4 O s f g (p, x) (q, y)) (hpq : p ≠ q)
    (h1a : (O.δ s f).2 = (O.δ (O.δ s g).1 f).2) (h1b : (O.δ (O.δ s f).1 g).2 = (O.δ s g).2) :
    (O.δ (O.δ (O.δ s f).1 g).1 x).2 ≠ (O.δ (O.δ (O.δ s g).1 f).1 x).2 ∧
    (O.δ (O.δ (O.δ s f).1 g).1 x).2 ≠ (O.δ (O.δ (O.δ (O.δ s g).1 f).1 y).1 x).2 ∧
    (O.δ (O.δ (O.δ (O.δ s f).1 g).1 y).1 x).2 ≠ (O.δ (O.δ (O.δ s g).1 f).1 x).2 ∧
    (O.δ (O.δ (O.δ (O.δ s f).1 g).1 y).1 x).2 ≠
      (O.δ (O.δ (O.δ (O.δ s g).1 f).1 y).1 x).2 := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩⟩ := hP
  fin_cases p <;> fin_cases q <;> simp at hpq <;>
    simp_all [TwoShotCons.Dist, view, resps]

variable {n : ℕ} {c : ℕ → O.Op}

lemma C2At.h1a (h : C2At O m s f g n c) : (O.δ s f).2 = (O.δ (O.δ s g).1 f).2 := by
  have := h.2.2.2.2.1
  simpa [TwoShotCons.Dist, view, resps] using this

lemma C2At.h1b (h : C2At O m s f g n c) : (O.δ (O.δ s f).1 g).2 = (O.δ s g).2 := by
  have := h.2.2.2.2.2.1
  simpa [TwoShotCons.Dist, view, resps] using this

lemma own_ne_succ (i : ℕ) : own i ≠ own (i + 1) := by
  unfold own; split_ifs <;> simp <;> omega

lemma C2At.pair (h : C2At O m s f g n c) {i : ℕ} (hi : i < n) :
    Pair4 O s f g (own i, c i) (own (i + 1), c (i + 1)) :=
  h.2.2.2.2.2.2.1 i hi

/-- **Corollary 1** (response form): for adjacent `j, j' ≤ n`, the response of `c_j` after
`fg[c_j']` differs from the one after `gf[c_j']`. -/
lemma C2At.adj (h : C2At O m s f g n c) {j j' : ℕ} (hj : j ≤ n) (hj' : j' ≤ n)
    (hadj : j + 1 = j' ∨ j' + 1 = j) :
    (O.δ (O.δ (O.δ s f).1 g).1 (c j)).2 ≠ (O.δ (O.δ (O.δ s g).1 f).1 (c j)).2 ∧
    (O.δ (O.δ (O.δ s f).1 g).1 (c j)).2 ≠ (O.δ (O.δ (O.δ (O.δ s g).1 f).1 (c j')).1 (c j)).2 ∧
    (O.δ (O.δ (O.δ (O.δ s f).1 g).1 (c j')).1 (c j)).2 ≠ (O.δ (O.δ (O.δ s g).1 f).1 (c j)).2 ∧
    (O.δ (O.δ (O.δ (O.δ s f).1 g).1 (c j')).1 (c j)).2 ≠
      (O.δ (O.δ (O.δ (O.δ s g).1 f).1 (c j')).1 (c j)).2 := by
  rcases hadj with rfl | rfl
  · exact (h.pair (by omega)).resp_ne (own_ne_succ j) h.h1a h.h1b
  · exact (h.pair (by omega)).symm.resp_ne (own_ne_succ j').symm h.h1a h.h1b

lemma C2At.n_pos (h : C2At O m s f g n c) : 1 ≤ n := by
  obtain ⟨t, ht⟩ := h.1; omega

/-- For every `j ≤ n`, the response of `c_j` after `fg` differs from the one after `gf`. -/
lemma C2At.fg_gf (h : C2At O m s f g n c) {j : ℕ} (hj : j ≤ n) :
    (O.δ (O.δ (O.δ s f).1 g).1 (c j)).2 ≠ (O.δ (O.δ (O.δ s g).1 f).1 (c j)).2 := by
  have := h.n_pos
  by_cases hjn : j < n
  · exact (h.adj hj (j' := j + 1) (by omega) (by omega)).1
  · exact (h.adj hj (j' := j - 1) (by omega) (by omega)).1

end Facts

end TwoShotCons
