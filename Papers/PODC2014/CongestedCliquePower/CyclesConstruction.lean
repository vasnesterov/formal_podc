import Papers.PODC2014.CongestedCliquePower.CyclesBasic

/-!
# The `(C_ℓ, F)`-lower bound graph of Lemma 18 (Section 3.4 of Drucker–Kuhn–Oshman, PODC 2014)

Given a graph `F` and path lengths `len : VF → ℕ`, the graph `G0 len F` has vertices
`(i, h)` with `h ≤ len i` (`PV len`): `A i = (i, 0)` and `B i = (i, len i)` span two copies of `F`
(`F_A`, `F_B`), and `(i, 0), (i, 1), …, (i, len i)` is a path `P_i` of length `len i` from `A i`
to `B i`. This is the paper's construction (the internal nodes `u_{i,j}` of `P_i` are the
`(i, h)`, `0 < h < len i`).

`lowerBoundGraph` shows that `G0 len F` is a `(C_ℓ, F)`-lower bound graph whenever
* every path has length `≥ 1`;
* `len i + len j + 2 = ℓ` for every edge `{i, j}` of `F` (so the intended cycle
  `A i – A j –P_j– B j – B i –P_i– A i` has length `ℓ`);
* `ℓ ≤ len i + len j + 3` for all `i ≠ j`;
* `F` is `C_ℓ`-free.

The heart of the proof (condition II) is `exists_fitsSeq`: we follow a copy of `C_ℓ` as a cyclic
sequence. Internal path vertices have degree two, so the cycle traverses every path it enters
(`up_forced`, `down_forced`); it must use a path since `F` is `C_ℓ`-free; after normalizing the
copy so that it starts with `A i → (i, 1)`, it goes up `P_i`, makes `r ≥ 1` steps in `F_B`, goes
down a path `P_j` (`j ≠ i`), and makes `s ≥ 1` steps in `F_A` back to `A i` (`core`). The length
conditions force `r = s = 1` and `{i, j} ∈ E_F`.
-/

namespace Podc.CongestedCliquePower

open SimpleGraph

namespace CycleLB

variable {VF : Type*} (len : VF → ℕ)

/-- Vertices of the construction: `(i, h)` is the vertex at height `h` on the path `P_i`. -/
@[ext]
structure PV (len : VF → ℕ) where
  /-- The index of the path. -/
  i : VF
  /-- The height on the path (`0` for `A i`, `len i` for `B i`). -/
  h : ℕ
  le : h ≤ len i

/-- `PV len` is the disjoint union of the paths. -/
def PV.equivSigma : PV len ≃ Σ i, Fin (len i + 1) where
  toFun p := ⟨p.i, ⟨p.h, Nat.lt_succ_of_le p.le⟩⟩
  invFun s := ⟨s.1, s.2.val, Nat.le_of_lt_succ s.2.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype VF] : Fintype (PV len) := Fintype.ofEquiv _ (PV.equivSigma len).symm

lemma card_PV [Fintype VF] : Fintype.card (PV len) = ∑ i, (len i + 1) := by
  rw [Fintype.card_congr (PV.equivSigma len), Fintype.card_sigma]
  simp

variable (F : SimpleGraph VF)

/-- The graph `G'` of Lemma 18: two copies of `F` on the ends of the paths `P_i`. -/
def G0 : SimpleGraph (PV len) where
  Adj p q := (p.h = 0 ∧ q.h = 0 ∧ F.Adj p.i q.i) ∨ (p.h = len p.i ∧ q.h = len q.i ∧ F.Adj p.i q.i) ∨
    (p.i = q.i ∧ (q.h = p.h + 1 ∨ p.h = q.h + 1))
  symm := ⟨fun p q h => by
    rcases h with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b⟩
    · exact Or.inl ⟨b, a, c.symm⟩
    · exact Or.inr (Or.inl ⟨b, a, c.symm⟩)
    · exact Or.inr (Or.inr ⟨a.symm, b.symm⟩)⟩
  loopless := ⟨fun p h => by
    rcases h with ⟨-, -, c⟩ | ⟨-, -, c⟩ | ⟨-, b⟩
    · exact F.loopless.irrefl _ c
    · exact F.loopless.irrefl _ c
    · omega⟩

variable {len F}

lemma G0_adj {p q : PV len} : (G0 len F).Adj p q ↔
    (p.h = 0 ∧ q.h = 0 ∧ F.Adj p.i q.i) ∨ (p.h = len p.i ∧ q.h = len q.i ∧ F.Adj p.i q.i) ∨
      (p.i = q.i ∧ (q.h = p.h + 1 ∨ p.h = q.h + 1)) := Iff.rfl

/-- The vertex `v_{A,i}`. -/
def A (i : VF) : PV len := ⟨i, 0, Nat.zero_le _⟩

/-- The vertex `v_{B,i}`. -/
def B (i : VF) : PV len := ⟨i, len i, le_rfl⟩

@[simp] lemma A_i (i : VF) : (A i : PV len).i = i := rfl
@[simp] lemma A_h (i : VF) : (A i : PV len).h = 0 := rfl
@[simp] lemma B_i (i : VF) : (B i : PV len).i = i := rfl
@[simp] lemma B_h (i : VF) : (B i : PV len).h = len i := rfl

variable (ℓ : ℕ)

/-- The copies `F_A`, `F_B` of `F` in `G0 len F`. -/
def lbData (h1 : ∀ i, 1 ≤ len i) : LBData (cycleGraph ℓ) F (G0 len F) where
  φA := ⟨⟨A, fun h => Or.inl ⟨rfl, rfl, h⟩⟩, fun a b h => congrArg PV.i h⟩
  φB := ⟨⟨B, fun h => Or.inr (Or.inl ⟨rfl, rfl, h⟩)⟩, fun a b h => congrArg PV.i h⟩
  disjoint a b h := by
    have : (0 : ℕ) = len b := congrArg PV.h h
    have := h1 b
    omega

variable {ℓ}

lemma mem_range_φA (h1 : ∀ i, 1 ≤ len i) (y : PV len) :
    y ∈ Set.range (lbData (F := F) ℓ h1).φA ↔ y.h = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · intro hy
    exact ⟨y.i, PV.ext rfl hy.symm⟩

lemma mem_range_φB (h1 : ∀ i, 1 ≤ len i) (y : PV len) :
    y ∈ Set.range (lbData (F := F) ℓ h1).φB ↔ y.h = len y.i := by
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · intro hy
    exact ⟨y.i, PV.ext rfl hy.symm⟩

lemma lbData_φA (h1 : ∀ i, 1 ≤ len i) (a : VF) : (lbData (F := F) ℓ h1).φA a = A a := rfl

lemma lbData_φB (h1 : ∀ i, 1 ≤ len i) (a : VF) : (lbData (F := F) ℓ h1).φB a = B a := rfl

/-! ### Following a cycle along the paths -/

section Forced

variable {x : ℤ → PV len} (hx : IsCycSeq (G0 len F) ℓ x) (hℓ : 3 ≤ ℓ)
include hx hℓ

/-- A cycle that goes up a path at height `h` continues up to the top. -/
lemma up_forced {t : ℤ} {i : VF} {h : ℕ} (h0 : (x t).i = i) (h0' : (x t).h = h)
    (h1 : (x (t + 1)).i = i) (h1' : (x (t + 1)).h = h + 1) :
    ∀ u : ℕ, h + u ≤ len i → (x (t + u)).i = i ∧ (x (t + u)).h = h + u := by
  suffices H : ∀ u : ℕ, h + u + 1 ≤ len i →
      ((x (t + u)).i = i ∧ (x (t + u)).h = h + u) ∧
        ((x (t + (u + 1 : ℕ))).i = i ∧ (x (t + (u + 1 : ℕ))).h = h + (u + 1)) by
    intro u hu
    rcases u with _ | w
    · simpa using ⟨h0, h0'⟩
    · exact (H w (by omega)).2
  intro u
  induction u with
  | zero =>
    intro _
    refine ⟨by simpa using ⟨h0, h0'⟩, ?_⟩
    simpa using ⟨h1, h1'⟩
  | succ u ih =>
    intro hu
    obtain ⟨⟨hy0, hy0'⟩, hy1, hy1'⟩ := ih (by omega)
    refine ⟨⟨hy1, hy1'⟩, ?_⟩
    have hadj := hx.adj (t + (u + 1 : ℕ))
    have he : t + ((u + 1 + 1 : ℕ) : ℤ) = t + ((u + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [he]
    rcases G0_adj.1 hadj with ⟨a, -, -⟩ | ⟨a, -, -⟩ | ⟨a, b | b⟩
    · omega
    · rw [hy1] at a
      omega
    · exact ⟨by rw [← a, hy1], by omega⟩
    · exfalso
      apply hx.ne_two hℓ (t + u)
      have he2 : t + ↑u + 2 = t + ((u + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      rw [he2]
      ext
      · rw [← a, hy1, hy0]
      · rw [hy0']
        omega

/-- A cycle that goes down a path from height `h` continues down to the bottom. -/
lemma down_forced {t : ℤ} {i : VF} {h : ℕ} (h0 : (x t).i = i) (h0' : (x t).h = h)
    (h1 : (x (t + 1)).i = i) (h1' : (x (t + 1)).h + 1 = h) :
    ∀ u : ℕ, u ≤ h → (x (t + u)).i = i ∧ (x (t + u)).h + u = h := by
  have hhle : h ≤ len i := h0 ▸ h0' ▸ (x t).le
  suffices H : ∀ u : ℕ, u + 1 ≤ h →
      ((x (t + u)).i = i ∧ (x (t + u)).h + u = h) ∧
        ((x (t + (u + 1 : ℕ))).i = i ∧ (x (t + (u + 1 : ℕ))).h + (u + 1) = h) by
    intro u hu
    rcases u with _ | w
    · simpa using ⟨h0, h0'⟩
    · exact (H w (by omega)).2
  intro u
  induction u with
  | zero =>
    intro _
    refine ⟨by simpa using ⟨h0, h0'⟩, ?_⟩
    simpa using ⟨h1, h1'⟩
  | succ u ih =>
    intro hu
    obtain ⟨⟨hy0, hy0'⟩, hy1, hy1'⟩ := ih (by omega)
    refine ⟨⟨hy1, hy1'⟩, ?_⟩
    have hadj := hx.adj (t + (u + 1 : ℕ))
    have he : t + ((u + 1 + 1 : ℕ) : ℤ) = t + ((u + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [he]
    rcases G0_adj.1 hadj with ⟨a, -, -⟩ | ⟨a, -, -⟩ | ⟨a, b | b⟩
    · omega
    · rw [hy1] at a
      omega
    · exfalso
      apply hx.ne_two hℓ (t + u)
      have he2 : t + ↑u + 2 = t + ((u + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      rw [he2]
      ext
      · rw [← a, hy1, hy0]
      · omega
    · exact ⟨by rw [← a, hy1], by omega⟩

/-- If a cycle goes up some path, it also goes up some path starting from its bottom `A i`. -/
lemma up_from_zero : ∀ (h : ℕ) (t : ℤ), (x t).h = h → (x (t + 1)).i = (x t).i →
    (x (t + 1)).h = h + 1 →
    ∃ t', (x t').h = 0 ∧ (x (t' + 1)).i = (x t').i ∧ (x (t' + 1)).h = 1 := by
  intro h
  induction h with
  | zero => intro t h0 h1 h2; exact ⟨t, h0, h1, h2⟩
  | succ h ih =>
    intro t h0 h1 h2
    have hle := (x (t + 1)).le
    rw [h1, h2] at hle
    rcases G0_adj.1 (hx.adj_pred t) with ⟨-, a, -⟩ | ⟨-, a, -⟩ | ⟨a, b | b⟩
    · omega
    · omega
    · exact ih (t - 1) (by omega) (by rw [sub_add_cancel, a]) (by rw [sub_add_cancel]; omega)
    · exfalso
      apply hx.ne_two hℓ (t - 1)
      rw [show t - 1 + 2 = t + 1 by ring]
      ext
      · rw [h1, a]
      · omega

end Forced

/-! ### The core argument for condition II -/

section Core

variable {x : ℤ → PV len} (hx : IsCycSeq (G0 len F) ℓ x) (hℓ : 3 ≤ ℓ)
  (h1 : ∀ i, 1 ≤ len i) (h2 : ∀ i j, F.Adj i j → len i + len j + 2 = ℓ)
  (h3 : ∀ i j, i ≠ j → ℓ ≤ len i + len j + 3)
include hx hℓ h1 h2 h3

/-- A cycle starting with `A i → (i, 1)` is the intended cycle of an edge `{i, j}`:
it goes up `P_i`, takes the edge `B i B j`, goes down `P_j` and returns by the edge `A j A i`. -/
lemma core {i : VF} (hi : (x 0).i = i) (hA0 : (x 0).h = 0) (hup : (x 1).i = i ∧ (x 1).h = 1) :
    ∃ j, F.Adj i j ∧ len i + len j + 2 = ℓ ∧
      (∀ u : ℕ, u ≤ len i → (x u).i = i ∧ (x u).h = u) ∧
      (∀ u : ℕ, u ≤ len j →
        (x ((len i : ℤ) + 1 + u)).i = j ∧ (x ((len i : ℤ) + 1 + u)).h + u = len j) := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, len i = p := ⟨_, rfl⟩
  rw [hp]
  have hxℓ : x ℓ = x 0 := by simpa using hx.add_period 0
  -- Step 1: up the path `P_i`
  have hP : ∀ u : ℕ, u ≤ p → (x u).i = i ∧ (x u).h = u := by
    intro u hu
    have := up_forced hx hℓ (t := 0) (h := 0) hi hA0 (by simpa using hup.1)
      (by simpa using hup.2) u (by omega)
    simpa using this
  have hp1 : 1 ≤ p := hp ▸ h1 i
  -- Step 2: from `B i`, the cycle continues in `F_B`
  have hpm1 : x ((p : ℤ) - 1) = x ((p - 1 : ℕ) : ℤ) := by
    congr 1; omega
  obtain ⟨hB1, hF1⟩ : (x ((p : ℤ) + 1)).h = len (x ((p : ℤ) + 1)).i ∧
      F.Adj i (x ((p : ℤ) + 1)).i := by
    obtain ⟨hPi, hPh⟩ := hP p le_rfl
    rcases G0_adj.1 (hx.adj p) with ⟨a, -, -⟩ | ⟨-, b, c⟩ | ⟨a, b | b⟩
    · omega
    · exact ⟨b, hPi ▸ c⟩
    · have := (x ((p : ℤ) + 1)).le
      rw [← a, hPi] at this
      omega
    · exfalso
      apply hx.ne_two hℓ ((p : ℤ) - 1)
      rw [show (p : ℤ) - 1 + 2 = p + 1 by ring, hpm1]
      obtain ⟨hq1, hq2⟩ := hP (p - 1) (by omega)
      ext
      · rw [← a, hPi, hq1]
      · rw [hq2]; omega
  have hsum1 := h2 _ _ hF1
  have hlen1 := h1 (x ((p : ℤ) + 1)).i
  -- Step 3: the segment in `F_B`
  have hnotB0 : ¬ (x ℓ).h = len (x ℓ).i := by
    rw [hxℓ, hA0]
    have := h1 (x 0).i
    omega
  have hwit : (p : ℤ) + 1 + ((ℓ - p - 1 : ℕ) : ℤ) = ℓ := by omega
  have hex : ∃ s : ℕ, ¬ (x ((p : ℤ) + 1 + s)).h = len (x ((p : ℤ) + 1 + s)).i :=
    ⟨ℓ - p - 1, by rw [hwit]; exact hnotB0⟩
  have hr_le : Nat.find hex ≤ ℓ - p - 1 := Nat.find_min' hex (by rw [hwit]; exact hnotB0)
  have hr_spec := Nat.find_spec hex
  have hr_min : ∀ s < Nat.find hex,
      (x ((p : ℤ) + 1 + s)).h = len (x ((p : ℤ) + 1 + s)).i := by
    intro s hs
    have := Nat.find_min hex hs
    simpa using this
  obtain ⟨r, hr⟩ : ∃ r, Nat.find hex = r := ⟨_, rfl⟩
  rw [hr] at hr_le hr_spec hr_min
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0] at hr_spec
    simp only [CharP.cast_eq_zero, add_zero] at hr_spec
    exact hr_spec hB1
  have hidx : (p : ℤ) + 1 + ((r - 1 : ℕ) : ℤ) = p + r := by omega
  have hBr : (x ((p : ℤ) + r)).h = len (x ((p : ℤ) + r)).i := by
    have := hr_min (r - 1) (by omega)
    rwa [hidx] at this
  have hnB : ¬ (x ((p : ℤ) + r + 1)).h = len (x ((p : ℤ) + r + 1)).i := by
    rw [show (p : ℤ) + r + 1 = p + 1 + r by ring]
    exact hr_spec
  obtain ⟨j, hj⟩ : ∃ j, (x ((p : ℤ) + r)).i = j := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, len j = q := ⟨_, rfl⟩
  rw [hj, hq] at hBr
  have hq1 : 1 ≤ q := hq ▸ h1 j
  have hdown : (x ((p : ℤ) + r + 1)).i = j ∧ (x ((p : ℤ) + r + 1)).h + 1 = q := by
    rcases G0_adj.1 (hx.adj ((p : ℤ) + r)) with ⟨a, -, -⟩ | ⟨-, b, -⟩ | ⟨a, b | b⟩
    · omega
    · exact absurd b hnB
    · have := (x ((p : ℤ) + r + 1)).le
      rw [← a, hj, hq] at this
      omega
    · exact ⟨a ▸ hj, by omega⟩
  have hji : j ≠ i := by
    intro hji
    apply hx.ne_add (a := p) (d := r) (by omega) (by omega)
    obtain ⟨hPi, hPh⟩ := hP p le_rfl
    ext
    · rw [hPi, hj, hji]
    · rw [hPh, hBr, ← hq, hji, hp]
  -- Step 4: down the path `P_j`
  have hQ : ∀ u : ℕ, u ≤ q → (x ((p : ℤ) + r + u)).i = j ∧ (x ((p : ℤ) + r + u)).h + u = q :=
    down_forced hx hℓ hj hBr hdown.1 hdown.2
  have hm : p + r + q < ℓ := by
    by_contra hcon
    obtain ⟨hu1, -⟩ := hQ (ℓ - p - r) (by omega)
    rw [show (p : ℤ) + r + ((ℓ - p - r : ℕ) : ℤ) = ℓ by omega, hxℓ, hi] at hu1
    exact hji hu1.symm
  have h3ij := h3 i j hji.symm
  rw [hp, hq] at h3ij
  -- Step 5: the segment in `F_A` reaches `x ℓ = A i` without leaving `F_A`
  have hmm1 : x ((p : ℤ) + r + q - 1) = x ((p : ℤ) + r + ((q - 1 : ℕ) : ℤ)) := by
    congr 1; omega
  have hAseg : ∀ s : ℕ, p + r + q + s ≤ ℓ → (x ((p : ℤ) + r + q + s)).h = 0 := by
    intro s
    induction s with
    | zero =>
      intro _
      have := (hQ q le_rfl).2
      simp only [CharP.cast_eq_zero, add_zero]
      omega
    | succ s ih =>
      intro hs
      have ih := ih (by omega)
      rw [show ((p : ℤ) + r + q + ((s + 1 : ℕ) : ℤ)) = (p : ℤ) + r + q + s + 1 by push_cast; ring]
      rcases G0_adj.1 (hx.adj ((p : ℤ) + r + q + s)) with ⟨-, b, -⟩ | ⟨a, -, -⟩ | ⟨a, b | b⟩
      · exact b
      · have := h1 (x ((p : ℤ) + r + q + s)).i
        omega
      · exfalso
        rcases Nat.eq_zero_or_pos s with hs0 | hs0
        · subst hs0
          apply hx.ne_two hℓ ((p : ℤ) + r + q - 1)
          rw [show (p : ℤ) + r + q - 1 + 2 = p + r + q + ((0 : ℕ) : ℤ) + 1 by push_cast; ring,
            hmm1]
          obtain ⟨hc1, hc2⟩ := hQ (q - 1) (by omega)
          obtain ⟨hd1, -⟩ := hQ q le_rfl
          ext
          · rw [← a, hc1]
            simpa using hd1
          · rw [b, ih]
            omega
        · have : (p : ℤ) + r + q + s + 1 = ℓ := by omega
          rw [this, hxℓ, hA0] at b
          omega
      · omega
  -- Step 6: the lengths force `r = 1` and `{i, j} ∈ E_F`
  have hr1 : r = 1 := by
    by_contra hr1
    by_cases hmℓ : p + r + q = ℓ - 1
    · have hAl := hAseg 0 (by omega)
      have hjF : F.Adj j i := by
        have hidx' : (ℓ : ℤ) - 1 = p + r + q + ((0 : ℕ) : ℤ) := by omega
        rcases G0_adj.1 (hx.adj ((ℓ : ℤ) - 1)) with ⟨-, -, c⟩ | ⟨a, -, -⟩ | ⟨a, b | b⟩
        · rw [sub_add_cancel, hxℓ, hi] at c
          have hd1 := (hQ q le_rfl).1
          rw [hidx'] at c
          simpa [hd1] using c
        · rw [hidx', hAl] at a
          have := h1 (x ((p : ℤ) + r + q + ((0 : ℕ) : ℤ))).i
          omega
        · rw [sub_add_cancel, hxℓ, hA0] at b
          omega
        · rw [hidx', hAl] at b
          omega
      have := h2 j i hjF
      omega
    · omega
  subst hr1
  have hj' : (x ((p : ℤ) + 1)).i = j := by simpa using hj
  rw [hj'] at hF1 hsum1
  refine ⟨j, hF1, by omega, hP, ?_⟩
  · intro u hu
    rw [hq] at hu ⊢
    have := hQ u hu
    rwa [show (p : ℤ) + ((1 : ℕ) : ℤ) = p + 1 by push_cast; ring] at this

end Core

/-! ### From the description of the intended cycle to conditions (b), (c) -/

lemma fitsSeq_of_desc [NeZero ℓ] {x : ℤ → PV len} (hx : IsCycSeq (G0 len F) ℓ x)
    (h1 : ∀ i, 1 ≤ len i) {i j : VF} (hij : F.Adj i j) (hsum : len i + len j + 2 = ℓ)
    (hP : ∀ u : ℕ, u ≤ len i → (x u).i = i ∧ (x u).h = u)
    (hQ : ∀ u : ℕ, u ≤ len j →
      (x ((len i : ℤ) + 1 + u)).i = j ∧ (x ((len i : ℤ) + 1 + u)).h + u = len j) :
    FitsSeq (lbData (F := F) ℓ h1) x i j := by
  unfold FitsSeq
  simp only [lbData_φA, lbData_φB]
  have hxℓ : x ℓ = x 0 := by simpa using hx.add_period 0
  have eA : ∀ k, x ((len i : ℤ) + 1 + len j) = A k ↔ k = j := by
    intro k
    obtain ⟨a, b⟩ := hQ (len j) le_rfl
    constructor
    · intro h; rw [← a, h]; rfl
    · rintro rfl; ext
      · exact a
      · change _ = 0; omega
  refine ⟨hij, ?_, ?_, ?_⟩
  · refine ⟨(len i : ℤ) + 1 + len j, Or.inr ⟨(eA j).2 rfl, ?_⟩⟩
    rw [show (len i : ℤ) + 1 + len j + 1 = ℓ by omega, hxℓ]
    obtain ⟨a, b⟩ := hP 0 (Nat.zero_le _)
    ext
    · simpa using a
    · simpa using b
  · refine ⟨len i, Or.inl ⟨?_, ?_⟩⟩
    · obtain ⟨a, b⟩ := hP (len i) le_rfl
      ext
      · exact a
      · exact b
    · obtain ⟨a, b⟩ := hQ 0 (Nat.zero_le _)
      simp only [CharP.cast_eq_zero, add_zero] at a b
      ext
      · exact a
      · exact b
  · intro y
    simp only [mem_range_φA, mem_range_φB]
    constructor
    · rintro ⟨⟨t, rfl⟩, hy⟩
      obtain ⟨n, hn, hxn⟩ := hx.exists_nat_lt t
      rw [hxn] at hy ⊢
      by_cases hni : n ≤ len i
      · obtain ⟨a, b⟩ := hP n hni
        rw [a] at hy
        rcases hy with hy | hy
        · left; ext
          · exact a
          · exact hy
        · right; right; left; ext
          · exact a
          · exact hy
      · obtain ⟨a, b⟩ := hQ (n - len i - 1) (by omega)
        rw [show (len i : ℤ) + 1 + ((n - len i - 1 : ℕ) : ℤ) = n by omega] at a b
        rw [a] at hy
        rcases hy with hy | hy
        · right; left; ext
          · exact a
          · exact hy
        · right; right; right; ext
          · exact a
          · exact hy
    · rintro (rfl | rfl | rfl | rfl)
      · refine ⟨⟨0, ?_⟩, Or.inl rfl⟩
        obtain ⟨a, b⟩ := hP 0 (Nat.zero_le _)
        ext
        · simpa using a
        · simpa using b
      · exact ⟨⟨_, (eA j).2 rfl⟩, Or.inl rfl⟩
      · refine ⟨⟨len i, ?_⟩, Or.inr rfl⟩
        obtain ⟨a, b⟩ := hP (len i) le_rfl
        ext
        · exact a
        · exact b
      · refine ⟨⟨(len i : ℤ) + 1, ?_⟩, Or.inr rfl⟩
        obtain ⟨a, b⟩ := hQ 0 (Nat.zero_le _)
        simp only [CharP.cast_eq_zero, add_zero] at a b
        ext
        · exact a
        · exact b

/-! ### Condition II -/

section CondII

variable [NeZero ℓ] (hℓ : 3 ≤ ℓ)
  (h1 : ∀ i, 1 ≤ len i) (h2 : ∀ i j, F.Adj i j → len i + len j + 2 = ℓ)
  (h3 : ∀ i j, i ≠ j → ℓ ≤ len i + len j + 3)
include hℓ h2 h3

lemma exists_fitsSeq_of_up {x : ℤ → PV len} (hx : IsCycSeq (G0 len F) ℓ x)
    (hup : ∃ t, (x (t + 1)).i = (x t).i ∧ (x (t + 1)).h = (x t).h + 1) :
    ∃ i j, FitsSeq (lbData (F := F) ℓ h1) x i j := by
  obtain ⟨t, ht1, ht2⟩ := hup
  obtain ⟨t', h0, h0i, h0h⟩ := up_from_zero hx hℓ _ t rfl ht1 ht2
  have hx' := hx.shift t'
  obtain ⟨j, hij, hsum, hP, hQ⟩ := core hx' hℓ h1 h2 h3 (i := (x t').i) (by simp) (by simpa using h0)
    ⟨by simpa [add_comm] using h0i, by simpa [add_comm] using h0h⟩
  exact ⟨_, j, (fitsSeq_of_desc hx' h1 hij hsum hP hQ).shift t'⟩

/-- **Condition II** for sequences: every cycle of length `ℓ` in `G0 len F` is an intended
cycle. -/
lemma exists_fitsSeq (hF : (cycleGraph ℓ).Free F) {x : ℤ → PV len}
    (hx : IsCycSeq (G0 len F) ℓ x) : ∃ i j, FitsSeq (lbData (F := F) ℓ h1) x i j := by
  by_cases hpath : ∃ t, (x (t + 1)).i = (x t).i ∧
      ((x (t + 1)).h = (x t).h + 1 ∨ (x t).h = (x (t + 1)).h + 1)
  · obtain ⟨t, hi, hup | hdown⟩ := hpath
    · exact exists_fitsSeq_of_up hℓ h1 h2 h3 hx ⟨t, hi, hup⟩
    · obtain ⟨u, v, h⟩ := exists_fitsSeq_of_up hℓ h1 h2 h3 hx.neg
        ⟨-t - 1, by
          show (x (-(-t - 1 + 1))).i = (x (-(-t - 1))).i
          rw [show -(-t - 1 + 1) = t by ring, show -(-t - 1) = t + 1 by ring]
          exact hi.symm, by
          show (x (-(-t - 1 + 1))).h = (x (-(-t - 1))).h + 1
          rw [show -(-t - 1 + 1) = t by ring, show -(-t - 1) = t + 1 by ring]
          exact hdown⟩
      exact ⟨u, v, h.neg⟩
  · exfalso
    push Not at hpath
    have hstep : ∀ t, ((x t).h = 0 ∧ (x (t + 1)).h = 0 ∧ F.Adj (x t).i (x (t + 1)).i) ∨
        ((x t).h = len (x t).i ∧ (x (t + 1)).h = len (x (t + 1)).i ∧
          F.Adj (x t).i (x (t + 1)).i) := by
      intro t
      rcases G0_adj.1 (hx.adj t) with h | h | ⟨a, b⟩
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        have := hpath t a.symm
        rcases b with b | b
        · exact this.1 b
        · exact this.2 b
    -- the cycle stays inside `F_A` or inside `F_B`, giving a copy of `C_ℓ` in `F`
    have key : ∀ P : PV len → Prop, (∀ t, P (x t) → P (x (t + 1))) → P (x 0) →
        (∀ t, P (x t) → ∀ t', P (x t') → (x t).i = (x t').i → x t = x t') →
        (∀ t, P (x t) → P (x (t + 1)) → F.Adj (x t).i (x (t + 1)).i) → False := by
      intro P hPs hP0 hPinj hPadj
      have hall : ∀ n : ℕ, P (x n) := by
        intro n
        induction n with
        | zero => simpa using hP0
        | succ n ih => simpa using hPs n ih
      have hall' := hx.forall_of_forall_nat hall
      have hy : IsCycSeq F ℓ (fun t => (x t).i) :=
        { adj := fun t => hPadj t (hall' t) (hall' (t + 1))
          eq_iff := fun a b => by
            rw [← hx.eq_iff]
            exact ⟨hPinj a (hall' a) b (hall' b), fun h => congrArg PV.i h⟩ }
      exact hF ⟨copyOfSeq hy⟩
    rcases hstep 0 with ⟨h0, -, -⟩ | ⟨h0, -, -⟩
    · refine key (fun v => v.h = 0) (fun t ht => ?_) h0 (fun t ht t' ht' hi => ?_)
        (fun t ht _ => ?_)
      · rcases hstep t with h | ⟨a, -, -⟩
        · exact h.2.1
        · have := h1 (x t).i; omega
      · ext
        · exact hi
        · rw [ht, ht']
      · rcases hstep t with h | ⟨a, -, -⟩
        · exact h.2.2
        · have := h1 (x t).i; omega
    · refine key (fun v => v.h = len v.i) (fun t ht => ?_) h0 (fun t ht t' ht' hi => ?_)
        (fun t ht _ => ?_)
      · rcases hstep t with ⟨a, -, -⟩ | h
        · have := h1 (x t).i; omega
        · exact h.2.1
      · ext
        · exact hi
        · rw [ht, ht', hi]
      · rcases hstep t with ⟨a, -, -⟩ | h
        · have := h1 (x t).i; omega
        · exact h.2.2

end CondII

/-! ### Condition I: the intended cycles -/

section CondI

/-- The intended cycle of the edge `{i, j}`, as a function of the position `n ∈ [0, ℓ)`:
up `P_i` from `A i` to `B i`, then down `P_j` from `B j` to `A j`. -/
def interW (i j : VF) (n : ℕ) : PV len :=
  if hn : n ≤ len i then ⟨i, n, hn⟩ else ⟨j, len j - (n - len i - 1), Nat.sub_le _ _⟩

variable {i j : VF} (hij : F.Adj i j) (hsum : len i + len j + 2 = ℓ)
include hij hsum

lemma interW_adj {n : ℕ} (hn : n + 1 < ℓ) : (G0 len F).Adj (interW i j n) (interW i j (n + 1)) := by
  unfold interW
  split_ifs with ha hb hb
  · exact Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)
  · exact Or.inr (Or.inl ⟨by simp; omega, by simp; omega, hij⟩)
  · omega
  · exact Or.inr (Or.inr ⟨rfl, Or.inr (by simp only; omega)⟩)

lemma interW_adj_last : (G0 len F).Adj (interW i j (ℓ - 1)) (interW i j 0) := by
  simp only [interW, show ¬ (ℓ - 1 ≤ len i) by omega, Nat.zero_le, ↓reduceDIte]
  exact Or.inl ⟨by simp only; omega, rfl, hij.symm⟩

lemma interW_inj {n m : ℕ} (hn : n < ℓ) (hm : m < ℓ) (h : interW i j n = interW (len := len) i j m) :
    n = m := by
  have hne : i ≠ j := hij.ne
  unfold interW at h
  split_ifs at h with ha hb hb
  · exact congrArg PV.h h
  · exact absurd (congrArg PV.i h) hne
  · exact absurd (congrArg PV.i h).symm hne
  · have := congrArg PV.h h
    simp only at this
    omega

variable [NeZero ℓ]

/-- The intended cycle of the edge `{i, j}` as a cyclic sequence. -/
def interSeq (ℓ : ℕ) [NeZero ℓ] (i j : VF) (t : ℤ) : PV len := interW i j (cyc ℓ t : ℕ)

omit hij hsum in
lemma interSeq_natCast {n : ℕ} (hn : n < ℓ) : interSeq (len := len) ℓ i j n = interW i j n := by
  simp [interSeq, cyc_val_natCast hn]

lemma isCycSeq_interSeq (hℓ : 3 ≤ ℓ) : IsCycSeq (G0 len F) ℓ (interSeq ℓ i j) where
  adj t := by
    unfold interSeq
    rw [cyc_succ_val]
    have hlt := (cyc ℓ t).isLt
    split_ifs with h
    · exact interW_adj hij hsum h
    · have : (cyc ℓ t : ℕ) = ℓ - 1 := by omega
      rw [this]
      exact interW_adj_last hij hsum
  eq_iff a b := by
    rw [← cyc_eq_iff]
    constructor
    · intro h
      exact Fin.ext (interW_inj hij hsum (cyc ℓ a).isLt (cyc ℓ b).isLt h)
    · intro h
      unfold interSeq
      rw [h]

/-- **Condition I**: the intended cycle of an edge satisfies (b) and (c). -/
lemma exists_fits (hℓ : 3 ≤ ℓ) (h1 : ∀ i, 1 ≤ len i) :
    ∃ f : (cycleGraph ℓ).Copy (G0 len F), (lbData ℓ h1).Fits f i j := by
  have hz := isCycSeq_interSeq hij hsum hℓ
  refine ⟨copyOfSeq hz, fits_of_fitsSeq (by omega) ?_⟩
  rw [seq_copyOfSeq]
  refine fitsSeq_of_desc hz h1 hij hsum (fun u hu => ?_) (fun u hu => ?_)
  · rw [interSeq_natCast (by omega)]
    simp [interW, hu]
  · rw [show (len i : ℤ) + 1 + u = ((len i + 1 + u : ℕ) : ℤ) by push_cast; ring,
      interSeq_natCast (by omega)]
    simp only [interW, show ¬ (len i + 1 + u ≤ len i) by omega, ↓reduceDIte, true_and]
    omega

end CondI

/-! ### The lower bound graph -/

/-- **Lemma 18 (construction).** Under the length conditions, `G0 len F` is a
`(C_ℓ, F)`-lower bound graph with `F_A = {A i}`, `F_B = {B i}`. -/
noncomputable def lowerBoundGraph (hℓ : 3 ≤ ℓ) (h1 : ∀ i, 1 ≤ len i)
    (h2 : ∀ i j, F.Adj i j → len i + len j + 2 = ℓ) (h3 : ∀ i j, i ≠ j → ℓ ≤ len i + len j + 3)
    (hF : (cycleGraph ℓ).Free F) : LowerBoundGraph (cycleGraph ℓ) F (G0 len F) :=
  haveI : NeZero ℓ := ⟨by omega⟩
  { toLBData := lbData ℓ h1
    exists_copy := fun _ _ huv => exists_fits huv (h2 _ _ huv) hℓ h1
    fits_of_copy := fun f => by
      obtain ⟨u, v, h⟩ := exists_fitsSeq hℓ h1 h2 h3 hF (isCycSeq_seq (by omega) f)
      exact ⟨u, v, fits_of_fitsSeq (by omega) h⟩ }

lemma lowerBoundGraph_φA (hℓ : 3 ≤ ℓ) (h1 h2 h3) (hF : (cycleGraph ℓ).Free F) (a : VF) :
    (lowerBoundGraph (len := len) hℓ h1 h2 h3 hF).φA a = A a := rfl

lemma lowerBoundGraph_φB (hℓ : 3 ≤ ℓ) (h1 h2 h3) (hF : (cycleGraph ℓ).Free F) (a : VF) :
    (lowerBoundGraph (len := len) hℓ h1 h2 h3 hF).φB a = B a := rfl

/-- The cut between Alice's side (all vertices except the `B i`) and Bob's side (`V_B`)
consists of the last edges of the paths: at most `|V_F|` edges. -/
lemma card_cut_le [Fintype VF] [DecidableRel (G0 len F).Adj] (h1 : ∀ i, 1 ≤ len i) :
    (Finset.univ.filter fun pq : PV len × PV len =>
      decide (pq.1.h < len pq.1.i) = true ∧ decide (pq.2.h < len pq.2.i) = false ∧
        (G0 len F).Adj pq.1 pq.2).card ≤ Fintype.card VF := by
  classical
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun pq => pq.2.i) (fun _ _ => Finset.mem_univ _) ?_
  rintro ⟨p1, q1⟩ hpq ⟨p2, q2⟩ hpq' heq
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
    decide_eq_true_eq, decide_eq_false_iff_not, not_lt] at hpq hpq' heq
  obtain ⟨a1, b1, c1⟩ := hpq
  obtain ⟨a2, b2, c2⟩ := hpq'
  have hq1 : q1.h = len q1.i := le_antisymm q1.le b1
  have hq2 : q2.h = len q2.i := le_antisymm q2.le b2
  -- the Alice endpoint is `(i, len i - 1)` on the same path
  have key : ∀ p q : PV len, p.h < len p.i → q.h = len q.i → (G0 len F).Adj p q →
      p.i = q.i ∧ p.h + 1 = len q.i := by
    intro p q hp hq hpq
    rcases G0_adj.1 hpq with ⟨-, b, -⟩ | ⟨a, -, -⟩ | ⟨a, b | b⟩
    · have := h1 q.i; omega
    · omega
    · exact ⟨a, by omega⟩
    · rw [a] at hp; omega
  obtain ⟨k1, l1⟩ := key p1 q1 a1 hq1 c1
  obtain ⟨k2, l2⟩ := key p2 q2 a2 hq2 c2
  have hq : q1 = q2 := PV.ext heq (by rw [hq1, hq2, heq])
  subst hq
  have hp : p1 = p2 := PV.ext (by rw [k1, k2]) (by omega)
  subst hp
  rfl

end CycleLB

end Podc.CongestedCliquePower
