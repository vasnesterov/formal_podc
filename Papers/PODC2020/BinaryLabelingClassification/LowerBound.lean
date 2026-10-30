import Papers.PODC2020.BinaryLabelingClassification.Caterpillar
import Papers.PODC2020.BinaryLabelingClassification.Spine

/-!
# The `Ω(n)` lower bounds of Theorems 8.1 and 8.2

Both lower bounds run a hypothetical `T`-round white algorithm on the caterpillar
(`Caterpillar.graph`) and on mirrored copies of it (`Gm p q`, the caterpillar relabelled along
`mirror p q`). Nodes far (`≥ T`) from the four boundary nodes of the mirrored segment see the same
radius-`T` view in both trees, hence produce the same output; but the spine order differs.

* **Theorem 8.1 (V.a).** Labels alternate along the spine (`va_alternate`). Mirroring the segment
  `w_1 – ⋯ – w_{2T+4}` (`2T + 3` steps, an odd number) moves `w_{T+2}` to spine index `T + 3`, so
  the parity of its spine distance to the far node `w_{3T+5}` changes, while both nodes produce the same labels:
  contradiction. (The paper instead reduces 2-colouring of paths; the content is the same.)
* **Theorem 8.2 (VI.b, easiest problem).** Edge directions are monotone along the spine
  (`dirR_mono`). With three far-apart white nodes `w_c`, `w_k`, `w_e` (`c < k < e`): if the edge
  right of `w_k` points left, mirroring around `w_c` makes `w_c` point right while `w_k` keeps a
  left-pointing edge; otherwise mirroring around `w_e` gives the symmetric contradiction. This is
  the paper's "mirror the subpath around `v₁` (or `v₄`)" argument, with the paper's reduction to
  the almost-oriented-path problem done inside the caterpillar.

The final statements (`theorem_8_1_lower`, `theorem_8_2`) are for an arbitrary node set `V` with
`n = |V|` nodes (identifiers): a `T`-round algorithm can only exist if `n < (3T + 6) d`
(resp. `n < (6T + 10)(d + δ − 2)`), i.e. `T = Ω(n)`.
-/

namespace Podc.BinaryLabeling

open SimpleGraph Cslib.Local

namespace Caterpillar

variable {M a b r : ℕ}

/-- The white spine node `w_k` (clamped at `k = M`). -/
def wN (k : ℕ) : Node M a b r := .inl (⟨min k M, by omega⟩, none)

/-- The black spine node `b_k` (clamped at `k = M`). -/
def bN (k : ℕ) : Node M a b r := .inr (.inl (⟨min k M, by omega⟩, none))

lemma adj_wN_bN (k : ℕ) : graph.Adj (wN k : Node M a b r) (bN k) := by
  rw [adj_iff]; simp [adjP, wN, bN]

lemma adj_bN_wN (k : ℕ) : graph.Adj (bN k : Node M a b r) (wN (k + 1)) := by
  rw [adj_iff]; simp [adjP, wN, bN]; omega

@[simp] lemma col_wN (k : ℕ) : col (wN k : Node M a b r) = true := rfl
@[simp] lemma col_bN (k : ℕ) : col (bN k : Node M a b r) = false := rfl

lemma deg_wN {k : ℕ} (hk : 1 ≤ k) (hkM : k ≤ M) : deg graph (wN k : Node M a b r) = a + 2 :=
  deg_wS (k := ⟨min k M, by omega⟩) (by simp; omega)

lemma deg_bN {k : ℕ} (hkM : k < M) : deg graph (bN k : Node M a b r) = b + 2 :=
  deg_bS (k := ⟨min k M, by omega⟩) (by simp; omega)

lemma wN_ne {k : ℕ} (hk : k < M) : (wN k : Node M a b r) ≠ wN (k + 1) := by
  simp [wN, Fin.ext_iff]; omega

lemma bN_ne {k : ℕ} (hk : k < M) : (bN k : Node M a b r) ≠ bN (k + 1) := by
  simp [bN, Fin.ext_iff]; omega

lemma pos_wN {k : ℕ} (hk : k ≤ M) : pos (wN k : Node M a b r) = 2 * k := by
  simp [pos, wN]; omega

lemma pos_bN {k : ℕ} (hk : k ≤ M) : pos (bN k : Node M a b r) = 2 * k + 1 := by
  simp [pos, bN]; omega

/-- The caterpillar relabelled along the mirror of the segment `w_p – ⋯ – w_q`. -/
def Gm (p q : ℕ) : SimpleGraph (Node M a b r) := graph.comap (mirrorPerm p q).symm

lemma mirrorPerm_symm_apply (p q : ℕ) (y : Node M a b r) : (mirrorPerm p q).symm y = mirror p q y := by
  rfl

lemma Gm_adj {p q : ℕ} {y z : Node M a b r} :
    (Gm p q).Adj y z ↔ graph.Adj (mirror p q y) (mirror p q z) := by
  simp [Gm, mirrorPerm_symm_apply]

lemma Gm_adj_mirror {p q : ℕ} {y z : Node M a b r} :
    (Gm p q).Adj (mirror p q y) (mirror p q z) ↔ graph.Adj y z := by
  rw [Gm_adj, mirror_mirror, mirror_mirror]

lemma deg_Gm (p q : ℕ) (y : Node M a b r) : deg (Gm p q) (mirror p q y) = deg graph y :=
  deg_comap_equiv (mirrorPerm p q) graph y

lemma isInstance_Gm (p q : ℕ) : IsInstance (Gm p q : SimpleGraph (Node M a b r)) col := by
  have h := isInstance.comap_equiv (mirrorPerm p q) (G := (graph : SimpleGraph (Node M a b r)))
  have hc : (col ∘ (mirrorPerm p q).symm : Node M a b r → Bool) = col := by
    funext y; simp [mirrorPerm_symm_apply, col_mirror]
  rwa [hc] at h

/-- Nodes at distance `≥ T` from the boundary of the mirrored segment see the same radius-`T`
view in the caterpillar and in its mirrored copy. -/
lemma viewEq_Gm {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) (hq : q ≤ M) (T : ℕ) (u : Node M a b r)
    (hfar : ∀ y : Node M a b r, IsBoundary p q y → (T : ℤ) ≤ pos u - pos y ∨ (T : ℤ) ≤ pos y - pos u) :
    ViewEq T graph col (Gm p q) col u := by
  refine ⟨fun y hy z => ?_, fun _ _ => rfl⟩
  have hnb : ¬ IsBoundary p q y := by
    intro hb
    have h1 := natAbs_pos_le_edist u y
    have h2 : ((pos u - pos y).natAbs : ℕ∞) < T := lt_of_le_of_lt h1 hy
    have h3 : (pos u - pos y).natAbs < T := by exact_mod_cast h2
    have := hfar y hb
    omega
  rw [Gm_adj, adj_mirror hp hpq hq hnb]

lemma mirror_eq_self {p q : ℕ} (y : Node M a b r) (h : 2 * (q : ℤ) + 1 < pos y) :
    mirror p q y = y :=
  pos_mirror_of_not p q y (Or.inr h)

lemma mirror_eq_self' {p q : ℕ} (y : Node M a b r) (h : pos y < 2 * (p : ℤ) - 1) :
    mirror p q y = y :=
  pos_mirror_of_not p q y (Or.inl h)

lemma mirror_wN {p q k : ℕ} (hk : p ≤ k) (hkq : k ≤ q) (hq : q ≤ M) :
    mirror p q (wN k : Node M a b r) = wN (p + q - k) := by
  simp only [mirror, wN, rW, Sum.inl.injEq, Prod.mk.injEq, and_true]
  split_ifs with h
  · simp [Fin.ext_iff]; omega
  · exfalso; apply h; simp; omega

lemma mirror_bN {p q k : ℕ} (hk : p ≤ k) (hkq : k < q) (hq : q ≤ M) :
    mirror p q (bN k : Node M a b r) = bN (p + q - 1 - k) := by
  simp only [mirror, bN, rB, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, and_true]
  split_ifs with h
  · simp [Fin.ext_iff]; omega
  · exfalso; apply h; simp; omega

/-- **Theorem 8.1, lower bound, on the caterpillar.** No `T`-round white algorithm solves V.a
on all trees on the caterpillar's node set once the spine has `M + 1 ≥ 3T + 6` white nodes. -/
theorem va_lower {P : Problem} (hP : P.IsVa) (hda : P.d = a + 2) (hb : b = 0) {T : ℕ}
    (hM : 3 * T + 5 ≤ M) : ¬ WhiteSolvable P (Node M a b r) T := by
  rintro ⟨A, hA, hs⟩
  set q := 2 * T + 4 with hq
  set t := T + 2 with ht
  set u := 3 * T + 5 with hu
  have hsol := hs _ _ (isInstance (M := M) (a := a) (b := b) (r := r))
  have hsol' := hs _ _ (isInstance_Gm (M := M) (a := a) (b := b) (r := r) 1 q)
  -- the views of `w_t` and `w_u` agree in both trees
  have hvt : ViewEq T graph col (Gm 1 q) col (wN t : Node M a b r) := by
    refine viewEq_Gm le_rfl (by omega) (by omega) T _ fun y hy => ?_
    rw [pos_wN (by omega)]
    rcases pos_of_isBoundary hy with h | h | h | h <;> rw [h] <;> push_cast <;> omega
  have hvu : ViewEq T graph col (Gm 1 q) col (wN u : Node M a b r) := by
    refine viewEq_Gm le_rfl (by omega) (by omega) T _ fun y hy => ?_
    rw [pos_wN (by omega)]
    rcases pos_of_isBoundary hy with h | h | h | h <;> rw [h] <;> push_cast <;> omega
  have hAt := hA _ _ _ _ _ hvt
  have hAu := hA _ _ _ _ _ hvu
  -- alternation in the caterpillar, from `t` to `u = t + (2T + 3)`
  have halt := va_alternate hP hsol wN bN t (2 * T + 3)
    (fun k hk hk' => ⟨col_wN k, by rw [deg_wN (by omega) (by omega), hda]⟩)
    (fun k hk hk' => ⟨col_bN k, by rw [deg_bN (by omega), hb], wN_ne (by omega)⟩)
    (fun k _ _ => adj_wN_bN k) (fun k _ _ => adj_bN_wN k)
  -- alternation in the mirrored copy, from `t' = T + 3` to `u = t' + (2T + 2)`
  have halt' := va_alternate hP hsol' (fun k => mirror 1 q (wN k)) (fun k => mirror 1 q (bN k))
    (T + 3) (2 * T + 2)
    (fun k hk hk' => ⟨by simp [col_mirror], by
      rw [deg_Gm, deg_wN (by omega) (by omega), hda]⟩)
    (fun k hk hk' => ⟨by simp [col_mirror], by rw [deg_Gm, deg_bN (by omega), hb], fun h =>
      wN_ne (M := M) (a := a) (b := b) (r := r) (k := k) (by omega) (by
        have := congrArg (mirror 1 q) h; rwa [mirror_mirror, mirror_mirror] at this)⟩)
    (fun k _ _ => Gm_adj_mirror.2 (adj_wN_bN k)) (fun k _ _ => Gm_adj_mirror.2 (adj_bN_wN k))
  have e1 : t + (2 * T + 3) = u := by omega
  have e2 : T + 3 + (2 * T + 2) = u := by omega
  rw [e1] at halt
  rw [e2] at halt'
  have hwu : mirror 1 q (wN u : Node M a b r) = wN u :=
    mirror_eq_self _ (by rw [pos_wN (by omega)]; push_cast; omega)
  have hbu : mirror 1 q (bN u : Node M a b r) = bN u :=
    mirror_eq_self _ (by rw [pos_bN (by omega)]; push_cast; omega)
  have hwt : mirror 1 q (wN (T + 3) : Node M a b r) = wN t := by
    rw [mirror_wN (by omega) (by omega) (by omega), show 1 + q - (T + 3) = t by omega]
  have hbt : mirror 1 q (bN (T + 3) : Node M a b r) = bN (T + 1) := by
    rw [mirror_bN (by omega) (by omega) (by omega), show 1 + q - 1 - (T + 3) = T + 1 by omega]
  simp only [hwu, hbu, hwt, hbt] at halt'
  -- evaluate both sides through the algorithm
  have x1 : whiteOut A (Gm 1 q) col (wN u) (bN u) = whiteOut A graph col (wN u) (bN u) := by
    simp [whiteOut, hAu]
  have x2 : whiteOut A (Gm 1 q) col (wN t) (bN (T + 1)) =
      whiteOut A graph col (wN t) (bN t) := by
    simp only [whiteOut, col_wN, ↓reduceIte, ← hAt]
    have := va_white_const hP hsol (v := wN t) (col_wN t) (by rw [deg_wN (by omega) (by omega), hda])
      (adj_bN_wN (T + 1)).symm (adj_wN_bN t)
    simpa [whiteOut] using this
  rw [x1, x2, halt] at halt'
  have hpar1 : decide ((2 * T + 3) % 2 = 1) = true := by simp [Nat.add_mod]
  have hpar2 : decide ((2 * T + 2) % 2 = 1) = false := by simp [Nat.add_mod]
  rw [hpar1, hpar2] at halt'
  revert halt'
  cases whiteOut A graph col (wN t) (bN t) <;> simp

lemma dirR_even (x : Node M a b r → Node M a b r → Bool) (w bb : ℕ → Node M a b r) (j : ℕ) :
    dirR x w bb (2 * j) = !x (w j) (bb j) := by
  simp [dirR]

lemma dirR_odd (x : Node M a b r → Node M a b r → Bool) (w bb : ℕ → Node M a b r) (j : ℕ) :
    dirR x w bb (2 * j + 1) = x (w (j + 1)) (bb j) := by
  simp only [dirR, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.one_mod, one_ne_zero,
    ↓reduceIte]
  congr 2 <;> omega

/-- A white node with the same view in two trees writes the same labels. -/
lemma whiteOut_eq_of_viewEq {A : Algorithm (Node M a b r)} {T : ℕ} (hA : Cslib.Local.IsLocal T A)
    {G G' : SimpleGraph (Node M a b r)} {u : Node M a b r} (hu : col u = true)
    (h : ViewEq T G col G' col u) (z : Node M a b r) :
    whiteOut A G' col u z = whiteOut A G col u z := by
  simp [whiteOut, hu, hA _ _ _ _ _ h]

/-- **Theorem 8.2, lower bound, on the caterpillar** (easiest problem of VI.b). -/
theorem viEasy_lower {d δ : ℕ} {hd : 2 ≤ d} {hδ : 2 ≤ δ} (hda : d = a + 2) (hdb : δ = b + 2)
    {T : ℕ} (hM : 6 * T + 9 ≤ M) : ¬ WhiteSolvable (viEasy d δ hd hδ) (Node M a b r) T := by
  rintro ⟨A, hA, hs⟩
  set c := T + 2 with hc
  set q₁ := 2 * T + 3 with hq₁
  set k := 3 * T + 5 with hk
  set p₂ := 4 * T + 7 with hp₂
  set e := 5 * T + 8 with he
  set q₂ := 6 * T + 9 with hq₂
  have hsol := hs _ _ (isInstance (M := M) (a := a) (b := b) (r := r))
  have hsol₁ := hs _ _ (isInstance_Gm (M := M) (a := a) (b := b) (r := r) 1 q₁)
  have hsol₂ := hs _ _ (isInstance_Gm (M := M) (a := a) (b := b) (r := r) p₂ q₂)
  set x := whiteOut A graph col
  -- relevance of the spine, in the caterpillar and in its mirrored copies
  have hwG : ∀ (p q j : ℕ), 0 ≤ 2 * j + 1 → 2 * j + 1 < 2 * M - 1 →
      col (mirror p q (wN (j + 1) : Node M a b r)) = true ∧
      deg (Gm p q) (mirror p q (wN (j + 1)) : Node M a b r) = d ∧
      mirror p q (bN j : Node M a b r) ≠ mirror p q (bN (j + 1)) := by
    intro p q j _ hj
    refine ⟨by simp [col_mirror], by rw [deg_Gm, deg_wN (by omega) (by omega), hda], fun h => ?_⟩
    have := congrArg (mirror p q) h
    rw [mirror_mirror, mirror_mirror] at this
    exact bN_ne (M := M) (a := a) (b := b) (r := r) (k := j) (by omega) this
  have hbG : ∀ (p q j : ℕ), 0 ≤ 2 * j → 2 * j < 2 * M - 1 →
      col (mirror p q (bN j : Node M a b r)) = false ∧
      deg (Gm p q) (mirror p q (bN j) : Node M a b r) = δ ∧
      mirror p q (wN j : Node M a b r) ≠ mirror p q (wN (j + 1)) := by
    intro p q j _ hj
    refine ⟨by simp [col_mirror], by rw [deg_Gm, deg_bN (by omega), hdb], fun h => ?_⟩
    have := congrArg (mirror p q) h
    rw [mirror_mirror, mirror_mirror] at this
    exact wN_ne (M := M) (a := a) (b := b) (r := r) (k := j) (by omega) this
  have hw0 : ∀ j, 0 ≤ 2 * j + 1 → 2 * j + 1 < 2 * M - 1 →
      col (wN (j + 1) : Node M a b r) = true ∧ deg graph (wN (j + 1) : Node M a b r) = d ∧
      (bN j : Node M a b r) ≠ bN (j + 1) :=
    fun j _ hj => ⟨rfl, by rw [deg_wN (by omega) (by omega), hda], bN_ne (by omega)⟩
  have hb0 : ∀ j, 0 ≤ 2 * j → 2 * j < 2 * M - 1 →
      col (bN j : Node M a b r) = false ∧ deg graph (bN j : Node M a b r) = δ ∧
      (wN j : Node M a b r) ≠ wN (j + 1) :=
    fun j _ hj => ⟨rfl, by rw [deg_bN (by omega), hdb], wN_ne (by omega)⟩
  have monoG := fun {s t : ℕ} => dirR_mono hsol wN bN 0 (2 * M - 1) hw0 hb0 adj_wN_bN adj_bN_wN
    (s := s) (t := t) (Nat.zero_le _)
  have mono₁ := fun {s t : ℕ} => dirR_mono hsol₁ (fun j => mirror 1 q₁ (wN j))
    (fun j => mirror 1 q₁ (bN j)) 0 (2 * M - 1) (hwG 1 q₁) (hbG 1 q₁)
    (fun j => Gm_adj_mirror.2 (adj_wN_bN j)) (fun j => Gm_adj_mirror.2 (adj_bN_wN j))
    (s := s) (t := t) (Nat.zero_le _)
  have mono₂ := fun {s t : ℕ} => dirR_mono hsol₂ (fun j => mirror p₂ q₂ (wN j))
    (fun j => mirror p₂ q₂ (bN j)) 0 (2 * M - 1) (hwG p₂ q₂) (hbG p₂ q₂)
    (fun j => Gm_adj_mirror.2 (adj_wN_bN j)) (fun j => Gm_adj_mirror.2 (adj_bN_wN j))
    (s := s) (t := t) (Nat.zero_le _)
  -- views
  have far : ∀ (p q j : ℕ), j ≤ M → (∀ y : Node M a b r, IsBoundary p q y →
      (T : ℤ) ≤ 2 * j - pos y ∨ (T : ℤ) ≤ pos y - 2 * j) →
      ∀ y : Node M a b r, IsBoundary p q y →
      (T : ℤ) ≤ pos (wN j : Node M a b r) - pos y ∨ (T : ℤ) ≤ pos y - pos (wN j : Node M a b r) := by
    intro p q j hj h y hy
    rw [pos_wN hj]; exact h y hy
  have vc : ViewEq T graph col (Gm 1 q₁) col (wN c : Node M a b r) :=
    viewEq_Gm le_rfl (by omega) (by omega) T _ (far _ _ _ (by omega) fun y hy => by
      rcases pos_of_isBoundary hy with h | h | h | h <;> rw [h] <;> push_cast <;> omega)
  have vk₁ : ViewEq T graph col (Gm 1 q₁) col (wN k : Node M a b r) :=
    viewEq_Gm le_rfl (by omega) (by omega) T _ (far _ _ _ (by omega) fun y hy => by
      rcases pos_of_isBoundary hy with h | h | h | h <;> rw [h] <;> push_cast <;> omega)
  have vk₂ : ViewEq T graph col (Gm p₂ q₂) col (wN k : Node M a b r) :=
    viewEq_Gm (by omega) (by omega) (by omega) T _ (far _ _ _ (by omega) fun y hy => by
      rcases pos_of_isBoundary hy with h | h | h | h <;> rw [h] <;> push_cast <;> omega)
  have ve : ViewEq T graph col (Gm p₂ q₂) col (wN e : Node M a b r) :=
    viewEq_Gm (by omega) (by omega) (by omega) T _ (far _ _ _ (by omega) fun y hy => by
      rcases pos_of_isBoundary hy with h | h | h | h <;> rw [h] <;> push_cast <;> omega)
  -- the relevant spine nodes under the mirrors
  have m1c : mirror 1 q₁ (wN c : Node M a b r) = wN c := by
    rw [mirror_wN (by omega) (by omega) (by omega), show 1 + q₁ - c = c by omega]
  have m1bc : mirror 1 q₁ (bN c : Node M a b r) = bN (c - 1) := by
    rw [mirror_bN (by omega) (by omega) (by omega), show 1 + q₁ - 1 - c = c - 1 by omega]
  have m1k : mirror 1 q₁ (wN k : Node M a b r) = wN k :=
    mirror_eq_self _ (by rw [pos_wN (by omega)]; push_cast; omega)
  have m1bk : mirror 1 q₁ (bN (k - 1) : Node M a b r) = bN (k - 1) :=
    mirror_eq_self _ (by rw [pos_bN (by omega)]; push_cast; omega)
  have m2e : mirror p₂ q₂ (wN e : Node M a b r) = wN e := by
    rw [mirror_wN (by omega) (by omega) (by omega), show p₂ + q₂ - e = e by omega]
  have m2be : mirror p₂ q₂ (bN (e - 1) : Node M a b r) = bN e := by
    rw [mirror_bN (by omega) (by omega) (by omega), show p₂ + q₂ - 1 - (e - 1) = e by omega]
  have m2k : mirror p₂ q₂ (wN k : Node M a b r) = wN k :=
    mirror_eq_self' _ (by rw [pos_wN (by omega)]; push_cast; omega)
  have m2bk : mirror p₂ q₂ (bN k : Node M a b r) = bN k :=
    mirror_eq_self' _ (by rw [pos_bN (by omega)]; push_cast; omega)
  cases hxk : dirR x wN bN (2 * k) with
  | false =>
    -- the edge right of `w_k` points left; so does the edge left of `w_c`
    have h1 : dirR x wN bN (2 * (c - 1) + 1) = false := by
      by_contra hc'
      have := monoG (s := 2 * (c - 1) + 1) (t := 2 * k) (by omega) (by omega)
        (by simpa using hc')
      rw [hxk] at this; exact absurd this (by simp)
    -- in the copy mirrored around `w_c`, the edge right of `w_c` points right
    have h2 : dirR (whiteOut A (Gm 1 q₁) col) (fun j => mirror 1 q₁ (wN j))
        (fun j => mirror 1 q₁ (bN j)) (2 * c) = true := by
      rw [dirR_even, m1c, m1bc, whiteOut_eq_of_viewEq hA rfl vc]
      rw [dirR_odd, show c - 1 + 1 = c by omega] at h1
      simp [x] at h1; simp [h1]
    have h3 := mono₁ (s := 2 * c) (t := 2 * (k - 1) + 1) (by omega) (by omega) h2
    rw [dirR_odd, show k - 1 + 1 = k by omega, m1k, m1bk,
      whiteOut_eq_of_viewEq hA rfl vk₁] at h3
    have h4 := monoG (s := 2 * (k - 1) + 1) (t := 2 * k) (by omega) (by omega)
      (by rw [dirR_odd, show k - 1 + 1 = k by omega]; exact h3)
    rw [hxk] at h4; exact absurd h4 (by simp)
  | true =>
    -- the edge right of `w_k` points right; so does the edge right of `w_e`
    have h1 := monoG (s := 2 * k) (t := 2 * e) (by omega) (by omega) hxk
    -- in the copy mirrored around `w_e`, the edge left of `w_e` points left
    have h2 : dirR (whiteOut A (Gm p₂ q₂) col) (fun j => mirror p₂ q₂ (wN j))
        (fun j => mirror p₂ q₂ (bN j)) (2 * (e - 1) + 1) = false := by
      rw [dirR_odd, show e - 1 + 1 = e by omega, m2e, m2be,
        whiteOut_eq_of_viewEq hA rfl ve]
      rw [dirR_even] at h1
      simpa [x] using h1
    have h3 : dirR (whiteOut A (Gm p₂ q₂) col) (fun j => mirror p₂ q₂ (wN j))
        (fun j => mirror p₂ q₂ (bN j)) (2 * k) = true := by
      rw [dirR_even, m2k, m2bk, whiteOut_eq_of_viewEq hA rfl vk₂]
      rw [dirR_even] at hxk
      exact hxk
    have h4 := mono₂ (s := 2 * k) (t := 2 * (e - 1) + 1) (by omega) (by omega) h3
    rw [h2] at h4; exact absurd h4 (by simp)

end Caterpillar

end Podc.BinaryLabeling
