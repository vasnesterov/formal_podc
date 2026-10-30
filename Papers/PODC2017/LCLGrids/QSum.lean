import Mathlib

/-!
# The `q`-sum coordination problem on directed cycles (Theorem 10)

Section 9 of Brandt et al., *LCL problems on grids* (PODC 2017).

**Model.** A directed cycle with `n` nodes `ZMod n` (node `v` knows its successor `v + 1` and
predecessor `v - 1`) and unique identifiers `id : ZMod n → ℕ`, all `< B`. A deterministic
`T`-round LOCAL algorithm (for this `n`, which the nodes know) is a map `f : (ℤ → ℕ) → ℤ` that
only depends on the identifiers at offsets `-T, …, T` (`IsLocal T f`); node `v` outputs
`f (view id v)`, where `view id v j = id (v + j)`. In the `q`-sum coordination problem, every
node outputs `ℓ(v) ∈ {-1, 0, 1}` and `∑_v ℓ(v) = q(n)` (`Solves`).

**Theorem 10.** If `q(n)` is odd for odd `n` and `|q(n)| ≤ n/2`, then `q`-sum coordination needs
`Ω(n)` rounds. We prove a sharper and more general statement by a different argument than the
paper's: if `8T < n` and identifiers may range over `7n` values, then *any* algorithm whose
outputs always sum to the same integer `Q` on `n`-cycles (any output alphabet) has `Q = n·δ` for
some integer `δ` (`sum_eq_mul`). For odd `Q` with `2|Q| ≤ n` this is impossible, so `n ≤ 8T`
(`theorem10_of_solves`, `theorem10`).

**Proof idea.** Words are lists of identifiers; `wsum w` is the sum of the outputs of the nodes of
`w` whose whole radius-`T` window lies in `w`. For blocks `F, G` of length `K = 2T` and a middle
word `X`, `α_{FG}(|X|) = wsum (F X G)` only depends on `|X|` (complete `F X G` to two `n`-cycles
`F X G Y`, `F X' G Y`), and `wsum (F P H R G) = wsum (F P H) + wsum (H R G)`. With three blocks
`F, G, H`, these identities force all `α` to be affine with a common slope `δ`, and then the
two-block cycle identity `α_{FG}(L) + α_{GF}(n - 2K - L) = Q` gives `Q = n δ` (`alg`).
-/

-- CSLib candidate: Cslib/Computability/Distributed/Local/Cycles/SumCoordination.lean (whole file)

namespace Podc.LCLGrids.QSum

open Finset

/-- `f` is a `T`-round algorithm: its value only depends on the identifiers at offsets
`-T, …, T`. -/
def IsLocal (T : ℕ) (f : (ℤ → ℕ) → ℤ) : Prop :=
  ∀ g h : ℤ → ℕ, (∀ j : ℤ, |j| ≤ T → g j = h j) → f g = f h

variable {n : ℕ}

/-- The view of node `v` of the directed `n`-cycle: `j ↦` identifier of the node `j` steps
ahead (`j < 0`: behind). -/
def view (id : ZMod n → ℕ) (v : ZMod n) : ℤ → ℕ := fun j => id (v + j)

/-- The sum of the outputs of all nodes. -/
def cycleSum [NeZero n] (f : (ℤ → ℕ) → ℤ) (id : ZMod n → ℕ) : ℤ := ∑ v, f (view id v)

/-- `f` solves `q`-sum coordination on directed `n`-cycles with identifiers in `[0, B)`: on every
such cycle, every output is in `{-1, 0, 1}` and the outputs sum to `q`. -/
def Solves (n B : ℕ) [NeZero n] (q : ℤ) (f : (ℤ → ℕ) → ℤ) : Prop :=
  ∀ id : ZMod n → ℕ, Function.Injective id → (∀ v, id v < B) →
    (∀ v, f (view id v) = -1 ∨ f (view id v) = 0 ∨ f (view id v) = 1) ∧ cycleSum f id = q

/-! ### Words -/

section words

variable (T : ℕ) (f : (ℤ → ℕ) → ℤ)

/-- The window of position `i` of a word. -/
def win (w : List ℕ) (i : ℕ) : ℤ → ℕ := fun j => w.getD ((i : ℤ) + j).toNat 0

/-- The sum of the outputs at the positions of `w` whose whole radius-`T` window lies in `w`. -/
def wsum (w : List ℕ) : ℤ := ∑ i ∈ Ico T (w.length - T), f (win w i)

variable {T f}

/-- Gluing two words along a common piece `m` of length `2T`. -/
theorem wsum_overlap (hf : IsLocal T f) (u m v : List ℕ) (hm : m.length = 2 * T) :
    wsum T f (u ++ m ++ v) = wsum T f (u ++ m) + wsum T f (m ++ v) := by
  simp only [wsum, List.length_append, hm]
  rw [show u.length + 2 * T + v.length - T = u.length + T + v.length by omega,
    show u.length + 2 * T - T = u.length + T by omega,
    show 2 * T + v.length - T = T + v.length by omega,
    ← Finset.sum_Ico_consecutive _ (show T ≤ u.length + T by omega)
      (show u.length + T ≤ u.length + T + v.length by omega)]
  congr 1
  · refine sum_congr rfl fun i hi => hf _ _ fun j hj => ?_
    rw [mem_Ico] at hi
    rw [abs_le] at hj
    simp only [win]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, hm]; omega)]
  · have hsh := Finset.sum_Ico_add' (fun i => f (win (u ++ m ++ v) i)) T (T + v.length) u.length
    rw [show T + u.length = u.length + T by omega,
      show T + v.length + u.length = u.length + T + v.length by omega] at hsh
    rw [← hsh]
    refine sum_congr rfl fun i hi => hf _ _ fun j hj => ?_
    rw [mem_Ico] at hi
    rw [abs_le] at hj
    simp only [win, List.append_assoc]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

/-- The word of a cycle: `v ↦` the `v`-th letter. -/
def ofList (L : List ℕ) : ZMod n → ℕ := fun v => L.getD v.val 0

lemma sum_Ico_cast [NeZero n] (g : ZMod n → ℤ) (a : ℕ) :
    ∑ i ∈ Ico a (a + n), g (i : ZMod n) = ∑ v, g v := by
  induction a with
  | zero =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    rw [zero_add, ← Finset.range_eq_Ico,
      ← Fin.sum_univ_eq_sum_range (fun i => g (i : ZMod (k + 1))) (k + 1)]
    exact Fintype.sum_congr _ _ fun i => by
      rw [show (((i : ℕ) : ZMod (k + 1))) = i from ZMod.natCast_zmod_val (n := k + 1) i]
  | succ a ih =>
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    rw [← ih, show a + 1 + n = a + n + 1 by omega, Finset.sum_Ico_succ_top (by omega),
      Finset.sum_eq_sum_Ico_succ_bot (show a < a + n by omega),
      show ((a + n : ℕ) : ZMod n) = (a : ZMod n) by simp]
    ring

lemma getD_append_take (L : List ℕ) (hL : L.length = n) (m k : ℕ) (hm : m ≤ n)
    (hk : k < n + m) : (L ++ L.take m).getD k 0 = L.getD (k % n) 0 := by
  rcases lt_or_ge k n with h | h
  · rw [List.getD_append _ _ _ _ (by omega), Nat.mod_eq_of_lt h]
  · rw [List.getD_append_right _ _ _ _ (by omega), hL,
      show k % n = k - n by rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_take_of_lt (by omega)]

/-- The output sum of a cycle given by a word `L` of length `n`, as a word sum. -/
theorem cycleSum_ofList [NeZero n] (hf : IsLocal T f) (L : List ℕ) (hL : L.length = n)
    (hT : 2 * T ≤ n) : cycleSum f (ofList L : ZMod n → ℕ) = wsum T f (L ++ L.take (2 * T)) := by
  have hlen : (L ++ L.take (2 * T)).length - T = T + n := by
    simp only [List.length_append, List.length_take, hL]; omega
  rw [wsum, hlen, cycleSum, ← sum_Ico_cast _ T]
  refine (sum_congr rfl fun i hi => hf _ _ fun j hj => ?_).symm
  rw [mem_Ico] at hi
  rw [abs_le] at hj
  have hn : 0 < n := by omega
  simp only [view, win, ofList]
  rw [getD_append_take L hL _ _ hT (by omega)]
  congr 1
  have h1 : (((i : ZMod n) + (j : ZMod n)) : ZMod n) = (((i : ℤ) + j : ℤ) : ZMod n) := by
    push_cast; rfl
  rw [h1]
  have h2 := ZMod.val_intCast (n := n) ((i : ℤ) + j)
  have h3 : (((i : ℤ) + j).toNat : ℤ) = (i : ℤ) + j := Int.toNat_of_nonneg (by omega)
  have h4 : (((((i : ℤ) + j).toNat % n : ℕ)) : ℤ) = ((i : ℤ) + j) % n := by
    push_cast; rw [h3]
  omega

end words

/-! ### The algebraic core -/

/-- The algebraic core of the proof of Theorem 10. `A = α_{FG}`, `B = α_{GF}`, `a₁ = α_{FH}`,
`a₂ = α_{HG}`, `a₃ = α_{GH}`, `a₄ = α_{HF}` for three blocks `F, G, H` of length `K`, and
`N = n - 2K` is the total length of the two middle words of a two-block cycle. -/
theorem alg (N K : ℕ) (Q : ℤ) (A B a₁ a₂ a₃ a₄ : ℕ → ℤ) (hN : 2 * K + 1 ≤ N)
    (h1 : ∀ L ≤ N, A L + B (N - L) = Q) (h2 : ∀ p ≤ N, a₁ p + a₄ (N - p) = Q)
    (h3 : ∀ r ≤ N, a₂ r + a₃ (N - r) = Q)
    (h4 : ∀ p r, p + K + r ≤ N → A (p + K + r) = a₁ p + a₂ r)
    (h5 : ∀ p r, p + K + r ≤ N → B (p + K + r) = a₃ p + a₄ r) :
    ∃ δ : ℤ, Q = ((N + 2 * K : ℕ) : ℤ) * δ := by
  -- two functions glued by an overlap identity are affine with a common slope
  have affine : ∀ (C x y : ℕ → ℤ), (∀ p r, p + K + r ≤ N → C (p + K + r) = x p + y r) →
      (∀ p ≤ N - K, x p = x 0 + p * (y 1 - y 0)) ∧
      (∀ r ≤ N - K, y r = y 0 + r * (y 1 - y 0)) ∧ x 1 - x 0 = y 1 - y 0 := by
    intro C x y h
    have hs : ∀ p r, p + r + 1 + K ≤ N → x (p + 1) - x p = y (r + 1) - y r := by
      intro p r hpr
      have e1 := h (p + 1) r (by omega)
      have e2 := h p (r + 1) (by omega)
      rw [show p + 1 + K + r = p + K + (r + 1) by omega] at e1
      linarith
    have hx1 : x 1 - x 0 = y 1 - y 0 := hs 0 0 (by omega)
    refine ⟨fun p hp => ?_, fun r hr => ?_, hx1⟩
    · induction p with
      | zero => simp
      | succ p ih =>
        have := hs p 0 (by omega)
        rw [ih (by omega)] at this
        push_cast; linarith
    · induction r with
      | zero => simp
      | succ r ih =>
        have := hs 0 r (by omega)
        rw [ih (by omega)] at this
        push_cast; linarith
  obtain ⟨ha1, ha2, -⟩ := affine A a₁ a₂ h4
  obtain ⟨ha3, ha4, -⟩ := affine B a₃ a₄ h5
  set δ := a₂ 1 - a₂ 0
  set δ' := a₄ 1 - a₄ 0
  -- the two slopes agree
  have e1 := h2 K (by omega)
  have e2 := h2 (K + 1) (by omega)
  rw [ha1 K (by omega), ha4 (N - K) (by omega)] at e1
  rw [ha1 (K + 1) (by omega), ha4 (N - (K + 1)) (by omega)] at e2
  have e3 := h3 K (by omega)
  rw [ha2 K (by omega), ha3 (N - K) (by omega)] at e3
  -- a two-block cycle with middles of lengths `N - K` and `K`
  have e4 := h1 (N - 2 * K + K + 0) (by omega)
  rw [h4 _ _ (by omega), show N - (N - 2 * K + K + 0) = 0 + K + 0 by omega,
    h5 _ _ (by omega), ha1 _ (by omega), ha2 0 (by omega), ha3 0 (by omega),
    ha4 0 (by omega)] at e4
  have c1 : ((N - K : ℕ) : ℤ) = N - K := by omega
  have c2 : ((N - (K + 1) : ℕ) : ℤ) = N - K - 1 := by omega
  have c3 : ((N - 2 * K : ℕ) : ℤ) = N - 2 * K := by omega
  rw [c1] at e1 e3
  rw [c2] at e2
  rw [c3] at e4
  push_cast at e1 e2 e3 e4 ⊢
  have hδ : δ' = δ := by linear_combination e1 - e2
  rw [hδ] at e1 e3 e4
  exact ⟨δ, by linear_combination -e1 - e3 + e4⟩

/-! ### Theorem 10 -/

section main

variable {T B : ℕ} {f : (ℤ → ℕ) → ℤ} {Q : ℤ} [NeZero n]

lemma ofList_injective {L : List ℕ} (hL : L.length = n) (hnd : L.Nodup) :
    Function.Injective (ofList L : ZMod n → ℕ) := by
  intro v w h
  simp only [ofList] at h
  have hv : v.val < L.length := hL ▸ ZMod.val_lt v
  have hw : w.val < L.length := hL ▸ ZMod.val_lt w
  rw [List.getD_eq_getElem _ _ hv, List.getD_eq_getElem _ _ hw] at h
  exact ZMod.val_injective n ((hnd.getElem_inj_iff).1 h)

lemma ofList_lt {L : List ℕ} (hL : L.length = n) (hB : ∀ a ∈ L, a < B) (v : ZMod n) :
    ofList L v < B := by
  have hv : v.val < L.length := hL ▸ ZMod.val_lt v
  simp only [ofList]
  rw [List.getD_eq_getElem _ _ hv]
  exact hB _ (List.getElem_mem _)

/-- Every two-block cycle `F X G Y` gives `wsum (F X G) + wsum (G Y F) = Q`. -/
lemma cycle2 (hf : IsLocal T f) (hs : Solves n B Q f) (F X G Y : List ℕ)
    (hF : F.length = 2 * T) (hG : G.length = 2 * T)
    (hlen : F.length + X.length + G.length + Y.length = n) (hnd : (F ++ X ++ G ++ Y).Nodup)
    (hB : ∀ a ∈ F ++ X ++ G ++ Y, a < B) :
    wsum T f (F ++ X ++ G) + wsum T f (G ++ Y ++ F) = Q := by
  have hL : (F ++ X ++ G ++ Y).length = n := by simp only [List.length_append]; omega
  have h := (hs _ (ofList_injective hL hnd) (ofList_lt hL hB)).2
  rw [cycleSum_ofList hf _ hL (by omega)] at h
  rw [← h, show F ++ X ++ G ++ Y = F ++ (X ++ G ++ Y) by simp,
    List.take_left' hF, show F ++ (X ++ G ++ Y) ++ F = (F ++ X) ++ G ++ (Y ++ F) by simp,
    wsum_overlap hf _ _ _ hG]
  simp

lemma nodup4 {l₁ l₂ l₃ l₄ : List ℕ} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h₃ : l₃.Nodup)
    (h₄ : l₄.Nodup) (h₁₂ : ∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b) (h₁₃ : ∀ a ∈ l₁, ∀ b ∈ l₃, a ≠ b)
    (h₁₄ : ∀ a ∈ l₁, ∀ b ∈ l₄, a ≠ b) (h₂₃ : ∀ a ∈ l₂, ∀ b ∈ l₃, a ≠ b)
    (h₂₄ : ∀ a ∈ l₂, ∀ b ∈ l₄, a ≠ b) (h₃₄ : ∀ a ∈ l₃, ∀ b ∈ l₄, a ≠ b) :
    (l₁ ++ l₂ ++ l₃ ++ l₄).Nodup := by
  simp only [List.nodup_append, List.mem_append]
  refine ⟨⟨⟨h₁, h₂, h₁₂⟩, h₃, ?_⟩, h₄, ?_⟩
  · rintro a (ha | ha) b hb
    exacts [h₁₃ a ha b hb, h₂₃ a ha b hb]
  · rintro a ((ha | ha) | ha) b hb
    exacts [h₁₄ a ha b hb, h₂₄ a ha b hb, h₃₄ a ha b hb]

/-- A block of `2T` fresh identifiers starting at `b`. -/
def blk (T b : ℕ) : List ℕ := List.range' b (2 * T)

/-- `α_{bX, bY}(L)`: the word sum of `blk bX ++ W ++ blk bY` for the canonical middle word
`W = [3n, 3n + L)`. -/
def α (n T : ℕ) (f : (ℤ → ℕ) → ℤ) (bX bY L : ℕ) : ℤ :=
  wsum T f (blk T bX ++ List.range' (3 * n) L ++ blk T bY)

/-- The word sum `wsum (F W G)` only depends on the length of `W` (blocks in the first three
regions `[0, n), [n, 2n), [2n, 3n)` of identifiers; `W` avoids the regions of the blocks and the
last region `[6n, 7n)`). -/
lemma ld (hf : IsLocal T f) (hs : Solves n B Q f) (hB : 7 * n ≤ B) (hT : 4 * T + 1 ≤ n)
    {bX bY : ℕ} (hX : bX + n ≤ 3 * n) (hY : bY + n ≤ 3 * n) (hXY : bX + n ≤ bY ∨ bY + n ≤ bX)
    (W : List ℕ) (hW : W.length ≤ n - 4 * T) (hWnd : W.Nodup)
    (hWa : ∀ a ∈ W, a < 6 * n ∧ (a < bX ∨ bX + n ≤ a) ∧ (a < bY ∨ bY + n ≤ a)) :
    wsum T f (blk T bX ++ W ++ blk T bY) = α n T f bX bY W.length := by
  have hb : ∀ b a, a ∈ blk T b ↔ b ≤ a ∧ a < b + 2 * T := fun b a => List.mem_range'_1
  have hr : ∀ s L a, a ∈ List.range' s L ↔ s ≤ a ∧ a < s + L := fun s L a => List.mem_range'_1
  have hlb : ∀ b, (blk T b).length = 2 * T := fun b => by simp [blk]
  have key := fun (X : List ℕ) (hXl : X.length = W.length) (hXnd : X.Nodup)
      (hXa : ∀ a ∈ X, a < 6 * n ∧ (a < bX ∨ bX + n ≤ a) ∧ (a < bY ∨ bY + n ≤ a)) =>
    cycle2 hf hs (blk T bX) X (blk T bY) (List.range' (6 * n) (n - 4 * T - W.length))
      (hlb _) (hlb _) (by simp [blk, hXl]; omega)
      (nodup4 List.nodup_range' hXnd List.nodup_range' List.nodup_range'
        (fun a ha b hb' => by have := (hXa b hb'); rw [hb] at ha; omega)
        (fun a ha b hb' => by rw [hb] at ha hb'; omega)
        (fun a ha b hb' => by rw [hb] at ha; rw [hr] at hb'; omega)
        (fun a ha b hb' => by have := (hXa a ha); rw [hb] at hb'; omega)
        (fun a ha b hb' => by have := (hXa a ha); rw [hr] at hb'; omega)
        (fun a ha b hb' => by rw [hb] at ha; rw [hr] at hb'; omega))
      (by
        intro a ha
        simp only [List.mem_append] at ha
        rcases ha with ((ha | ha) | ha) | ha
        · rw [hb] at ha; omega
        · have := hXa a ha; omega
        · rw [hb] at ha; omega
        · rw [hr] at ha; omega)
  have e1 := key W rfl hWnd hWa
  have e2 := key (List.range' (3 * n) W.length) (by simp) List.nodup_range'
    (fun a ha => by rw [hr] at ha; omega)
  rw [α]; linarith

lemma two_cycle (hf : IsLocal T f) (hs : Solves n B Q f) (hB : 7 * n ≤ B) (hT : 4 * T + 1 ≤ n)
    {bX bY : ℕ} (hX : bX + n ≤ 3 * n) (hY : bY + n ≤ 3 * n) (hXY : bX + n ≤ bY ∨ bY + n ≤ bX)
    (L : ℕ) (hL : L ≤ n - 4 * T) :
    α n T f bX bY L + α n T f bY bX (n - 4 * T - L) = Q := by
  have hb : ∀ b a, a ∈ blk T b ↔ b ≤ a ∧ a < b + 2 * T := fun b a => List.mem_range'_1
  have hr : ∀ s L a, a ∈ List.range' s L ↔ s ≤ a ∧ a < s + L := fun s L a => List.mem_range'_1
  have hlb : ∀ b, (blk T b).length = 2 * T := fun b => by simp [blk]
  have e := cycle2 hf hs (blk T bX) (List.range' (3 * n) L) (blk T bY)
    (List.range' (4 * n) (n - 4 * T - L)) (hlb _) (hlb _) (by simp [blk]; omega)
    (nodup4 List.nodup_range' List.nodup_range' List.nodup_range' List.nodup_range'
      (fun a ha b hb' => by rw [hb] at ha; rw [hr] at hb'; omega)
      (fun a ha b hb' => by rw [hb] at ha hb'; omega)
      (fun a ha b hb' => by rw [hb] at ha; rw [hr] at hb'; omega)
      (fun a ha b hb' => by rw [hr] at ha; rw [hb] at hb'; omega)
      (fun a ha b hb' => by rw [hr] at ha hb'; omega)
      (fun a ha b hb' => by rw [hb] at ha; rw [hr] at hb'; omega))
    (by
      intro a ha
      simp only [List.mem_append] at ha
      rcases ha with ((ha | ha) | ha) | ha
      · rw [hb] at ha; omega
      · rw [hr] at ha; omega
      · rw [hb] at ha; omega
      · rw [hr] at ha; omega)
  have e2 := ld hf hs hB hT hY hX hXY.symm (List.range' (4 * n) (n - 4 * T - L)) (by simp)
    List.nodup_range' (fun a ha => by rw [hr] at ha; omega)
  simp only [List.length_range'] at e2
  rw [← e2]
  exact e

lemma three_blocks (hf : IsLocal T f) (hs : Solves n B Q f) (hB : 7 * n ≤ B)
    (hT : 4 * T + 1 ≤ n) {bX bY bZ : ℕ} (hX : bX + n ≤ 3 * n) (hY : bY + n ≤ 3 * n)
    (hZ : bZ + n ≤ 3 * n) (hXY : bX + n ≤ bY ∨ bY + n ≤ bX) (hXZ : bX + n ≤ bZ ∨ bZ + n ≤ bX)
    (hYZ : bY + n ≤ bZ ∨ bZ + n ≤ bY) (p r : ℕ) (hpr : p + 2 * T + r ≤ n - 4 * T) :
    α n T f bX bY (p + 2 * T + r) = α n T f bX bZ p + α n T f bZ bY r := by
  have hb : ∀ b a, a ∈ blk T b ↔ b ≤ a ∧ a < b + 2 * T := fun b a => List.mem_range'_1
  have hr : ∀ s L a, a ∈ List.range' s L ↔ s ≤ a ∧ a < s + L := fun s L a => List.mem_range'_1
  have hlb : ∀ b, (blk T b).length = 2 * T := fun b => by simp [blk]
  have hov := wsum_overlap hf (blk T bX ++ List.range' (4 * n) p) (blk T bZ)
    (List.range' (5 * n) r ++ blk T bY) (hlb _)
  have eW := ld hf hs hB hT hX hY hXY (List.range' (4 * n) p ++ blk T bZ ++ List.range' (5 * n) r)
    (by simp [blk]; omega)
    (by
      simp only [List.nodup_append, List.mem_append]
      refine ⟨⟨List.nodup_range', List.nodup_range', fun a ha b hb' => ?_⟩, List.nodup_range',
        fun a ha b hb' => ?_⟩
      · rw [hr] at ha; rw [hb] at hb'; omega
      · rw [hr] at hb'; rcases ha with ha | ha <;> [rw [hr] at ha; rw [hb] at ha] <;> omega)
    (by
      intro a ha
      simp only [List.mem_append] at ha
      rcases ha with (ha | ha) | ha
      · rw [hr] at ha; omega
      · rw [hb] at ha; omega
      · rw [hr] at ha; omega)
  have e1 := ld hf hs hB hT hX hZ hXZ (List.range' (4 * n) p) (by simp; omega) List.nodup_range'
    (fun a ha => by rw [hr] at ha; omega)
  have e2 := ld hf hs hB hT hZ hY hYZ.symm (List.range' (5 * n) r) (by simp; omega)
    List.nodup_range' (fun a ha => by rw [hr] at ha; omega)
  simp only [List.length_append, List.length_range', hlb] at eW e1 e2
  simp only [List.append_assoc] at hov eW e1 e2
  rw [← eW, ← e1, ← e2, ← hov]

/-- The core of Theorem 10: if `8T < n` and `f` makes every directed `n`-cycle with identifiers
in `[0, 7n)` sum to `Q`, then `Q` is a multiple of `n`. -/
theorem sum_eq_mul (hf : IsLocal T f) (hs : Solves n B Q f) (hB : 7 * n ≤ B)
    (hT : 8 * T + 1 ≤ n) : ∃ δ : ℤ, Q = n * δ := by
  have h4 : 4 * T + 1 ≤ n := by omega
  have hX : 0 + n ≤ 3 * n := by omega
  have hY : n + n ≤ 3 * n := by omega
  have hZ : 2 * n + n ≤ 3 * n := by omega
  obtain ⟨δ, hδ⟩ := alg (n - 4 * T) (2 * T) Q (α n T f 0 n) (α n T f n 0) (α n T f 0 (2 * n))
    (α n T f (2 * n) n) (α n T f n (2 * n)) (α n T f (2 * n) 0) (by omega)
    (fun L hL => two_cycle hf hs hB h4 hX hY (by omega) L hL)
    (fun L hL => two_cycle hf hs hB h4 hX hZ (by omega) L hL)
    (fun L hL => two_cycle hf hs hB h4 hZ hY (by omega) L hL)
    (fun p r h => three_blocks hf hs hB h4 hX hY hZ (by omega) (by omega) (by omega) p r h)
    (fun p r h => three_blocks hf hs hB h4 hY hX hZ (by omega) (by omega) (by omega) p r h)
  refine ⟨δ, ?_⟩
  rw [hδ, show n - 4 * T + 2 * (2 * T) = n by omega]

/-- Theorem 10, for one odd `n`: if `Q` is odd and `|Q| ≤ n/2`, then no algorithm with fewer than
`n/8` rounds makes all directed `n`-cycles (identifiers in `[0, B)`, `B ≥ 7n`) sum to `Q`. -/
theorem theorem10_of_solves (hf : IsLocal T f) (hs : Solves n B Q f) (hB : 7 * n ≤ B)
    (hQ : Odd Q) (hQn : 2 * |Q| ≤ n) : n ≤ 8 * T := by
  by_contra h
  obtain ⟨δ, hδ⟩ := sum_eq_mul hf hs hB (by omega)
  have hδ0 : δ ≠ 0 := by rintro rfl; simp at hδ; rw [hδ] at hQ; exact (Int.not_odd_zero hQ)
  have : (n : ℤ) ≤ |Q| := by
    rw [hδ, abs_mul, abs_of_nonneg (by positivity)]
    exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hδ0)
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  omega

/-- **Theorem 10** of the paper. Let `q : ℕ → ℤ` with `q(n)` odd for odd `n` and `|q(n)| ≤ n/2`.
If an algorithm (`f n`, running in `T n` rounds on `n`-cycles) solves `q`-sum coordination on
all directed cycles with identifiers in `[0, 7n)` (or any larger range), then `T(n) ≥ n/8` for
every odd `n`; in particular it does not run in `o(n)` rounds. -/
theorem theorem10 (q : ℕ → ℤ) (hq₁ : ∀ n, Odd n → Odd (q n)) (hq₂ : ∀ n, 2 * |q n| ≤ n)
    (f : ℕ → (ℤ → ℕ) → ℤ) (T : ℕ → ℕ) (hloc : ∀ n, IsLocal (T n) (f n))
    (hsolve : ∀ n (_ : NeZero n), Solves n (7 * n) (q n) (f n)) :
    (∀ n, Odd n → n ≤ 8 * T n) ∧
      ¬ (fun n => (T n : ℝ)) =o[Filter.atTop] (fun n => (n : ℝ)) := by
  have main : ∀ n, Odd n → n ≤ 8 * T n := fun n hn =>
    have : NeZero n := ⟨by rintro rfl; exact (Nat.not_odd_zero hn)⟩
    theorem10_of_solves (hloc n) (hsolve n this) le_rfl (hq₁ n hn) (hq₂ n)
  refine ⟨main, fun ho => ?_⟩
  have := ho.def (show (0 : ℝ) < 1 / 16 by norm_num)
  rw [Filter.eventually_atTop] at this
  obtain ⟨N, hN⟩ := this
  have h1 := hN (2 * N + 1) (by omega)
  have h2 := main (2 * N + 1) (by simp)
  simp only [Real.norm_natCast] at h1
  have : ((2 * N + 1 : ℕ) : ℝ) ≤ 8 * (T (2 * N + 1) : ℝ) := by exact_mod_cast h2
  have hpos : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  linarith

end main

end Podc.LCLGrids.QSum
