import Papers.PODC2024.OnlineLocalGrids.GridGeometry
import Papers.PODC2024.OnlineLocalGrids.Rows

/-!
# Lemma 3.6: forcing a row path with a large `b`-value

The adversary builds, inside a prescribed stretch `Z` of a row, a contiguous revealed row segment
`[L, R]` on which (unless the algorithm already coloured two adjacent revealed nodes alike) some
directed row path has `|b| ≥ k`. The segment has length `< segLen T k`, where
`segLen T k + 2T + 2 = 2^k (2T + 3)` (`segLen_add`); the paper's bound is `5^{k+1} T` for the
"discovered region".

Inductive step (as in the paper): build two segments for `k` far apart, then move the second one
(translation or reflection of its columns, `grid_exists_move`) next to the first, at gap
`2T + ℓ` with `ℓ ∈ {2, 3}` chosen by parity (Lemma 3.5), and reveal the nodes in between.
`choose_move` is the purely combinatorial part (choice of orientation and of `ℓ`).
-/

namespace Papers.PODC2024.OnlineLocalGrids

open SimpleGraph Cslib.OnlineLocal

/-- Length bound for the segment produced for `b`-value `k` with locality `T`. -/
def segLen (T : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * segLen T k + 2 * T + 2

lemma segLen_add (T k : ℕ) : segLen T k + 2 * T + 2 = 2 ^ k * (2 * T + 3) := by
  induction k with
  | zero => simp [segLen]; ring
  | succ k ih => simp only [segLen, pow_succ]; nlinarith

lemma one_le_segLen (T k : ℕ) : 1 ≤ segLen T k := by
  induction k with
  | zero => simp [segLen]
  | succ k ih => simp only [segLen]; omega

/-- The translation offset / reflection axis used to place the second segment. -/
def moveD (fl : Bool) (L2' L2 R2 : ℤ) : ℤ := if fl then L2' + R2 else L2' - L2

lemma cm_moveD_mem {fl : Bool} {L2' L2 R2 j : ℤ} (h1 : L2 ≤ j) (h2 : j ≤ R2) :
    L2' ≤ cm fl (moveD fl L2' L2 R2) j ∧ cm fl (moveD fl L2' L2 R2) j ≤ L2' + (R2 - L2) := by
  cases fl <;> simp only [cm, moveD, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- **Combinatorial core of the inductive step of Lemma 3.6.** Given the colours `g₁` of the first
segment `[L1, R1]` and `g₂` of the second segment `[L2, R2]` (each with a path of `|b| ≥ k` if
properly coloured), one can choose the orientation `fl` of the second segment and the extra gap
`ℓ ∈ {2, 3}` such that, whatever colours the gap nodes get, a properly coloured concatenation
contains a path with `|b| ≥ k + 1`. -/
lemma choose_move (T k : ℕ) (g₁ g₂ : ℤ → Fin 3) {L1 R1 L2 R2 : ℤ} (hLR1 : L1 ≤ R1)
    (hLR2 : L2 ≤ R2)
    (hf1 : RowProper g₁ L1 R1 → HasFactor g₁ L1 R1 k)
    (hf2 : RowProper g₂ L2 R2 → HasFactor g₂ L2 R2 k) :
    ∃ (fl : Bool) (ℓ : ℤ), (ℓ = 2 ∨ ℓ = 3) ∧ ∀ g : ℤ → Fin 3,
      (∀ j, L1 ≤ j → j ≤ R1 → g j = g₁ j) →
      (∀ j, L2 ≤ j → j ≤ R2 →
        g (cm fl (moveD fl (R1 + 2 * T + ℓ) L2 R2) j) = g₂ j) →
      RowProper g L1 (R1 + 2 * T + ℓ + (R2 - L2)) →
      HasFactor g L1 (R1 + 2 * T + ℓ + (R2 - L2)) (k + 1) := by
  by_cases hP : RowProper g₁ L1 R1 ∧ RowProper g₂ L2 R2
  swap
  · refine ⟨false, 2, Or.inl rfl, fun g h1 h2 hp => ?_⟩
    exfalso
    apply hP
    constructor
    · intro j hj1 hj2
      have := hp j hj1 (by omega)
      rwa [h1 j hj1 hj2.le, h1 (j + 1) (by omega) (by omega)] at this
    · refine rowProper_shift (d := R1 + 2 * T + 2 - L2) (g' := g) (fun j hj1 hj2 => ?_) ?_
      · have := h2 j hj1 hj2
        simpa [cm, moveD] using this
      · exact rowProper_mono hp (by omega) (by omega)
  obtain ⟨x1, n1, hx1, hy1, hs1⟩ := hf1 hP.1
  obtain ⟨x2, n2, hx2, hy2, hs2⟩ := hf2 hP.2
  obtain ⟨s1, hs1def⟩ : ∃ s, S g₁ x1 n1 = s := ⟨_, rfl⟩
  obtain ⟨s2, hs2def⟩ : ∃ s, S g₂ x2 n2 = s := ⟨_, rfl⟩
  rw [hs1def] at hs1
  rw [hs2def] at hs2
  obtain ⟨ε, hε, hεs1⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (k : ℤ) ≤ ε * s1 := by
    by_cases h : 0 ≤ s1
    · exact ⟨1, Or.inl rfl, by omega⟩
    · exact ⟨-1, Or.inr rfl, by omega⟩
  obtain ⟨fl, hfl⟩ : ∃ fl : Bool, (fl = true ↔ ε * s2 < 0) := ⟨decide (ε * s2 < 0), by simp⟩
  -- left-end colour and offset of the transported factor
  obtain ⟨c2, hc2def⟩ : ∃ c : Fin 3, (if fl then g₂ (x2 + n2) else g₂ x2) = c := ⟨_, rfl⟩
  obtain ⟨off, hoffdef⟩ : ∃ o : ℤ, (if fl then R2 - (x2 + n2) else x2 - L2) = o := ⟨_, rfl⟩
  set t : ℤ := ((k + 1 : ℕ) : ℤ) + 1 with ht
  obtain ⟨e, hedef⟩ : ∃ e : ℤ, ind (g₁ (x1 + n1)) + ind c2 + (R1 - (x1 + n1)) + 2 * T + off = e :=
    ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ, hpar⟩ : ∃ ℓ : ℤ, (ℓ = 2 ∨ ℓ = 3) ∧ ¬ (e + ℓ ≡ t [ZMOD 2]) := by
    by_cases h : (e + 2 - t) % 2 = 0
    · exact ⟨3, Or.inr rfl, by rw [Int.modEq_iff_dvd]; omega⟩
    · exact ⟨2, Or.inl rfl, by rw [Int.modEq_iff_dvd]; omega⟩
  refine ⟨fl, ℓ, hℓ, fun g h1 h2 hp => ?_⟩
  obtain ⟨L2', hL2'⟩ : ∃ L, R1 + 2 * T + ℓ = L := ⟨_, rfl⟩
  rw [hL2'] at h2 hp ⊢
  -- the transported second factor `[x2', x2' + n2]`
  obtain ⟨x2', hx2'off, hS2, hc2⟩ : ∃ x2' : ℤ, x2' = L2' + off ∧
      S g x2' n2 = (if fl then - s2 else s2) ∧ g x2' = c2 := by
    cases fl
    · simp only [Bool.false_eq_true, ↓reduceIte] at hoffdef hc2def h2 ⊢
      refine ⟨L2' - L2 + x2, by simp [moveD] at h2; omega, ?_, ?_⟩
      · rw [← hs2def]
        exact S_shift (fun j hj1 hj2 => by simpa [cm, moveD] using h2 j (by omega) (by omega))
      · rw [← hc2def]; simpa [cm, moveD] using h2 x2 (by omega) (by omega)
    · simp only [↓reduceIte] at hoffdef hc2def h2 ⊢
      refine ⟨L2' + R2 - (x2 + n2), by omega, ?_, ?_⟩
      · rw [← hs2def]
        exact S_flip (fun j hj1 hj2 => by simpa [cm, moveD] using h2 j (by omega) (by omega))
      · rw [← hc2def]; simpa [cm, moveD] using h2 (x2 + n2) (by omega) (by omega)
  have hoff : 0 ≤ off ∧ off + n2 ≤ R2 - L2 := by
    cases fl <;> simp only [Bool.false_eq_true, ↓reduceIte] at hoffdef <;> omega
  have hεs2 : (k : ℤ) ≤ ε * S g x2' n2 := by
    rw [hS2]
    cases fl
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have : ¬ ε * s2 < 0 := fun h => by simp_all
      rcases hε with rfl | rfl <;> omega
    · simp only [↓reduceIte]
      have : ε * s2 < 0 := hfl.1 rfl
      rcases hε with rfl | rfl <;> omega
  -- the connecting path from `x1 + n1` to `x2'`
  obtain ⟨gap, hgap⟩ : ∃ gap : ℕ, (gap : ℤ) = x2' - (x1 + n1) := ⟨(x2' - (x1 + n1)).toNat, by omega⟩
  have hS1 : S g x1 n1 = s1 := by
    rw [← hs1def]; exact S_congr (fun j hj1 hj2 => h1 j (by omega) (by omega))
  have hparh : ¬ (S g (x1 + n1) gap ≡ t [ZMOD 2]) := by
    have hpp := S_parity (g := g) (x := x1 + n1) (n := gap)
      (rowProper_mono hp (by omega) (by omega))
    rw [show x1 + n1 + (gap : ℤ) = x2' by omega, hc2, h1 (x1 + n1) (by omega) (by omega),
      show ind (g₁ (x1 + ↑n1)) + ind c2 + (gap : ℤ) = e + ℓ by omega] at hpp
    exact fun hc => hpar (hpp.symm.trans hc)
  have hcomb := combine (k := k + 1) (s₁ := s1) (h := S g (x1 + n1) gap) (s₂ := S g x2' n2) ε hε
    (by push_cast; omega) (by push_cast; omega) hparh
  have htot : S g x1 (n1 + gap + n2) = s1 + S g (x1 + n1) gap + S g x2' n2 := by
    rw [S_add, S_add, hS1, show x1 + ((n1 + gap : ℕ) : ℤ) = x2' by push_cast; omega]
  rcases hcomb with h | h | h | h
  · exact ⟨x1, n1, by omega, by omega, by rwa [hS1]⟩
  · exact ⟨x2', n2, by omega, by omega, h⟩
  · exact ⟨x1 + n1, gap, by omega, by omega, h⟩
  · exact ⟨x1, n1 + gap + n2, by omega, by push_cast; omega, by rwa [htot]⟩

/-! ### The adversary strategy -/

section Adversary

variable {ι : Type*} [DecidableEq ι] {m : ℕ} [NeZero m] (A : Algorithm ι (Fin 3)) (T : ℕ)

/-- The colour that the run `(pos, σ)` gives to the node at row `r`, column `j`. -/
def rowCol (pos : ι ≃ Fin m × Fin m) (σ : List ι) (r : ℤ) : ℤ → Fin 3 :=
  fun j => A.label ((grid m m).comap pos) T σ (pos.symm (pt r j))

omit [NeZero m] in
/-- After an invisible move, the labels of revealed nodes are unchanged (also when more nodes are
revealed later). -/
lemma label_after_move {pos : ι ≃ Fin m × Fin m} {μ : Equiv.Perm (Fin m × Fin m)} {σ : List ι}
    (h : AgreeOn (grid m m) ((grid m m).comap μ) (pos '' {x | x ∈ σ}) T) (τ : List ι) {x : ι}
    (hx : x ∈ σ) :
    A.label ((grid m m).comap (pos.trans μ)) T (σ ++ τ) x = A.label ((grid m m).comap pos) T σ x := by
  rw [label_append A _ T τ hx]
  exact (label_eq_of_agreeOn A (agreeOn_comap pos μ h) x).symm

omit [NeZero m] [DecidableEq ι] in
lemma trans_apply_of_fix {pos : ι ≃ Fin m × Fin m} {μ : Equiv.Perm (Fin m × Fin m)} {σ : List ι}
    (h : ∀ p ∈ ball (grid m m) (pos '' {x | x ∈ σ}) T, μ p = p) {x : ι} (hx : x ∈ σ) :
    (pos.trans μ) x = pos x :=
  h _ (subset_ball ⟨x, hx, rfl⟩)

omit [NeZero m] [DecidableEq ι] in
lemma image_trans_of_fix {pos : ι ≃ Fin m × Fin m} {μ : Equiv.Perm (Fin m × Fin m)} {σ : List ι}
    (h : ∀ p ∈ ball (grid m m) (pos '' {x | x ∈ σ}) T, μ p = p) :
    (pos.trans μ) '' {x | x ∈ σ} = pos '' {x | x ∈ σ} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (trans_apply_of_fix T h hx).symm⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, trans_apply_of_fix T h hx⟩

/-- The statement of **Lemma 3.6** for a given `k`: starting from any state (revealed nodes `σ₀`,
identifier placement `pos₀`), the adversary can reveal new nodes `δ` and invisibly re-place
identifiers (a permutation `μ` of positions fixing everything around `σ₀`) so that the new nodes
form exactly the row segment `[L, R]` of row `r`, inside the stretch `[a, a + segLen T k)`, and,
if the algorithm coloured that segment properly, it contains a row path with `|b| ≥ k`.
The stretch must be away from the grid border (margin `T`) and at distance `≥ 2T + 2` from all
previously revealed nodes. -/
def Lemma36 (k : ℕ) : Prop :=
  ∀ (σ₀ : List ι) (pos₀ : ι ≃ Fin m × Fin m) (r a : ℤ), σ₀.Nodup →
    (T : ℤ) ≤ r → r + T < m → (T : ℤ) ≤ a → a + segLen T k + T ≤ m →
    (∀ x ∈ σ₀, ∀ j, a ≤ j → j < a + segLen T k →
      2 * T + 2 ≤ (rz (pos₀ x) - r).natAbs + (cz (pos₀ x) - j).natAbs) →
    ∃ (δ : List ι) (μ : Equiv.Perm (Fin m × Fin m)) (L R : ℤ),
      (∀ p ∈ ball (grid m m) (pos₀ '' {x | x ∈ σ₀}) T, μ p = p) ∧
      (σ₀ ++ δ).Nodup ∧ a ≤ L ∧ L ≤ R ∧ R < a + segLen T k ∧
      (∀ x, x ∈ δ ↔ ∃ j, L ≤ j ∧ j ≤ R ∧ μ (pos₀ x) = pt r j) ∧
      (RowProper (rowCol A T (pos₀.trans μ) (σ₀ ++ δ) r) L R →
        HasFactor (rowCol A T (pos₀.trans μ) (σ₀ ++ δ) r) L R k)

lemma lemma36_zero : Lemma36 (m := m) A T 0 := by
  intro σ₀ pos₀ r a hnd hr1 hr2 ha1 ha2 hfar
  simp only [segLen] at ha2 hfar ⊢
  refine ⟨[pos₀.symm (pt r a)], 1, a, a, fun p _ => rfl, ?_, le_rfl, le_rfl, by omega, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hnd, List.nodup_singleton _, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_singleton] at hy
    subst hy hxy
    have := hfar _ hx a le_rfl (by omega)
    have e1 := rz_pt (m := m) (j := a) (show (0 : ℤ) ≤ r by omega) (show r < m by omega)
    have e2 := cz_pt (m := m) (r := r) (show (0 : ℤ) ≤ a by omega) (show a < m by omega)
    simp only [Equiv.apply_symm_apply, e1, e2] at this
    omega
  · intro x
    simp only [List.mem_singleton, Equiv.Perm.coe_one, id_eq]
    constructor
    · rintro rfl; exact ⟨a, le_rfl, le_rfl, by simp⟩
    · rintro ⟨j, h1, h2, h⟩
      obtain rfl : j = a := le_antisymm h2 h1
      rw [← h, Equiv.symm_apply_apply]
  · intro _
    exact ⟨a, 0, le_rfl, by simp, by simp⟩

lemma cmInv_moveD_mem {fl : Bool} {L2' L2 R2 j : ℤ} (h1 : L2' ≤ j) (h2 : j ≤ L2' + (R2 - L2)) :
    L2 ≤ cmInv fl (moveD fl L2' L2 R2) j ∧ cmInv fl (moveD fl L2' L2 R2) j ≤ R2 := by
  cases fl <;> simp only [cmInv, moveD, Bool.false_eq_true, ↓reduceIte] <;> omega

lemma lemma36_succ {k : ℕ} (ih : Lemma36 (m := m) A T k) : Lemma36 (m := m) A T (k + 1) := by
  intro σ₀ pos₀ r a hnd hr1 hr2 ha1 ha2 hfar
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ, segLen T k = s := ⟨_, rfl⟩
  have hs : ((segLen T (k + 1) : ℕ) : ℤ) = 2 * s + 2 * T + 2 := by
    simp only [segLen, hsdef]; push_cast; ring
  rw [hs] at ha2 hfar ⊢
  have hs1 : 1 ≤ s := hsdef ▸ one_le_segLen T k
  have hr0 : (0 : ℤ) ≤ r := by omega
  have hrm : r < m := by omega
  have rzpt : ∀ j, rz (pt (m := m) r j) = r := fun j => rz_pt hr0 hrm
  have czpt : ∀ j : ℤ, 0 ≤ j → j < m → cz (pt (m := m) r j) = j := fun j h0 h1 => cz_pt h0 h1
  have ptinj : ∀ j j' : ℤ, 0 ≤ j → j < m → 0 ≤ j' → j' < m → pt (m := m) r j = pt r j' → j = j' :=
    fun j j' h0 h1 h2 h3 h => by
      have := congrArg cz h; rwa [czpt j h0 h1, czpt j' h2 h3] at this
  -- Step 1: the first segment, in `[a, a + s)`
  obtain ⟨δ1, μ1, L1, R1, hfix1, hnd1, hL1, hLR1, hR1, hmem1, hfac1⟩ :=
    ih σ₀ pos₀ r a hnd hr1 hr2 ha1 (by omega) (fun x hx j hj1 hj2 => hfar x hx j hj1 (by omega))
  rw [hsdef] at hR1
  have hpos₁σ₀ : ∀ x ∈ σ₀, (pos₀.trans μ1) x = pos₀ x := fun x hx => trans_apply_of_fix T hfix1 hx
  -- Step 2: the second segment, in `[a2, a2 + s)`
  obtain ⟨δ2, μ2, L2, R2, hfix2, hnd2, hL2, hLR2, hR2, hmem2, hfac2⟩ :=
    ih (σ₀ ++ δ1) (pos₀.trans μ1) r (a + s + 2 * T + 2) hnd1 hr1 hr2 (by omega) (by omega) (by
      intro x hx j hj1 hj2
      rw [hsdef] at hj2
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · rw [hpos₁σ₀ x hx]; exact hfar x hx j (by omega) (by omega)
      · obtain ⟨j1, h1, h2, h3⟩ := (hmem1 x).1 hx
        rw [show (pos₀.trans μ1) x = μ1 (pos₀ x) from rfl, h3, rzpt, czpt j1 (by omega) (by omega)]
        omega)
  rw [hsdef] at hR2
  have hpos₂old : ∀ x ∈ σ₀ ++ δ1, ((pos₀.trans μ1).trans μ2) x = (pos₀.trans μ1) x :=
    fun x hx => trans_apply_of_fix T hfix2 hx
  obtain ⟨fl, ℓ, hℓ, hgood⟩ := choose_move T k (rowCol A T (pos₀.trans μ1) (σ₀ ++ δ1) r)
    (rowCol A T ((pos₀.trans μ1).trans μ2) (σ₀ ++ δ1 ++ δ2) r) hLR1 hLR2 hfac1 hfac2
  have hcm : ∀ j, L2 ≤ j → j ≤ R2 → R1 + 2 * T + ℓ ≤ cm fl (moveD fl (R1 + 2 * T + ℓ) L2 R2) j ∧
      cm fl (moveD fl (R1 + 2 * T + ℓ) L2 R2) j ≤ R1 + 2 * T + ℓ + (R2 - L2) :=
    fun j h1 h2 => cm_moveD_mem h1 h2
  -- Step 3: move the second segment next to the first one
  obtain ⟨μ3, hfix3, hmove3, hag3⟩ := grid_exists_move
    (U₁ := ((pos₀.trans μ1).trans μ2) '' {x | x ∈ σ₀ ++ δ1})
    (U₂ := ((pos₀.trans μ1).trans μ2) '' {x | x ∈ δ2}) (T := T) fl
    (moveD fl (R1 + 2 * T + ℓ) L2 R2)
    (by
      rintro u ⟨x, hx, rfl⟩
      obtain ⟨j, h1, h2, h3⟩ := (hmem2 x).1 hx
      obtain ⟨h4, h5⟩ := hcm j h1 h2
      rw [show ((pos₀.trans μ1).trans μ2) x = μ2 ((pos₀.trans μ1) x) from rfl, h3, rzpt,
        czpt j (by omega) (by omega)]
      omega)
    (by
      rintro u ⟨y, hy, rfl⟩ v ⟨x, hx, rfl⟩
      obtain ⟨j, h1, h2, h3⟩ := (hmem2 x).1 hx
      obtain ⟨h4, h5⟩ := hcm j h1 h2
      rw [show ((pos₀.trans μ1).trans μ2) x = μ2 ((pos₀.trans μ1) x) from rfl, h3,
        hpos₂old y hy]
      simp only [md, rzpt, czpt j (by omega) (by omega)]
      simp only [Set.mem_ofPred_eq, List.mem_append] at hy
      rcases hy with hy | hy
      · rw [hpos₁σ₀ y hy]
        exact ⟨hfar y hy j (by omega) (by omega), hfar y hy _ (by omega) (by omega)⟩
      · obtain ⟨j1, h6, h7, h8⟩ := (hmem1 y).1 hy
        rw [show (pos₀.trans μ1) y = μ1 (pos₀ y) from rfl, h8, rzpt,
          czpt j1 (by omega) (by omega)]
        omega)
  obtain ⟨L2', hL2'⟩ : ∃ x, R1 + 2 * (T : ℤ) + ℓ = x := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ x, moveD fl L2' L2 R2 = x := ⟨_, rfl⟩
  obtain ⟨R2', hR2'⟩ : ∃ x, L2' + (R2 - L2) = x := ⟨_, rfl⟩
  rw [hL2', hd, hR2'] at hgood
  rw [hL2', hd, hR2'] at hcm
  rw [hL2', hd] at hmove3
  set pos₃ := ((pos₀.trans μ1).trans μ2).trans μ3 with hpos₃
  have hU : ((pos₀.trans μ1).trans μ2) '' {x | x ∈ σ₀ ++ δ1} ∪
      ((pos₀.trans μ1).trans μ2) '' {x | x ∈ δ2} =
      ((pos₀.trans μ1).trans μ2) '' {x | x ∈ σ₀ ++ δ1 ++ δ2} := by
    rw [← Set.image_union]; congr 1; ext x; simp [or_assoc]
  rw [hU] at hag3
  have hpos₃old : ∀ x ∈ σ₀ ++ δ1, pos₃ x = (pos₀.trans μ1) x := by
    intro x hx
    rw [hpos₃, Equiv.trans_apply, hfix3 _ (subset_ball ⟨x, hx, rfl⟩), hpos₂old x hx]
  have hpos₃δ2 : ∀ x ∈ δ2, ∃ j, L2 ≤ j ∧ j ≤ R2 ∧ (pos₀.trans μ1).trans μ2 x = pt r j ∧
      pos₃ x = pt r (cm fl d j) := by
    intro x hx
    obtain ⟨j, h1, h2, h3⟩ := (hmem2 x).1 hx
    have h3' : ((pos₀.trans μ1).trans μ2) x = pt r j := h3
    obtain ⟨h4, h5⟩ := hmove3 _ ⟨x, hx, rfl⟩
    refine ⟨j, h1, h2, h3', ?_⟩
    obtain ⟨h6, h7⟩ := hcm j h1 h2
    rw [eq_pt_iff hr0 hrm (by omega) (by omega)]
    rw [hpos₃, Equiv.trans_apply, h4, h5, h3', rzpt, czpt j (by omega) (by omega)]
    exact ⟨rfl, rfl⟩
  -- Step 4: reveal the gap
  obtain ⟨n3, hn3⟩ : ∃ n : ℕ, (n : ℤ) = L2' - R1 - 1 := ⟨(L2' - R1 - 1).toNat, by omega⟩
  set δ3 : List ι := (List.range n3).map (fun i : ℕ => pos₃.symm (pt r (R1 + 1 + (i : ℤ))))
    with hδ3
  have hmem3 : ∀ x, x ∈ δ3 ↔ ∃ j, R1 < j ∧ j < L2' ∧ pos₃ x = pt r j := by
    intro x
    simp only [hδ3, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨R1 + 1 + i, by omega, by omega, by simp⟩
    · rintro ⟨j, h1, h2, h3⟩
      refine ⟨(j - R1 - 1).toNat, by omega, ?_⟩
      rw [show R1 + 1 + (((j - R1 - 1).toNat : ℕ) : ℤ) = j by omega, ← h3, Equiv.symm_apply_apply]
  -- where the new nodes sit
  have hnew : ∀ x, x ∈ δ1 ++ δ2 ++ δ3 ↔ ∃ j, L1 ≤ j ∧ j ≤ R2' ∧ pos₃ x = pt r j := by
    intro x
    constructor
    · intro hx
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · obtain ⟨j, h1, h2, h3⟩ := (hmem1 x).1 hx
        exact ⟨j, h1, by omega, by rw [hpos₃old x (List.mem_append_right _ hx)]; exact h3⟩
      · obtain ⟨j, h1, h2, -, h3⟩ := hpos₃δ2 x hx
        obtain ⟨h4, h5⟩ := hcm j h1 h2
        exact ⟨cm fl d j, by omega, h5, h3⟩
      · obtain ⟨j, h1, h2, h3⟩ := (hmem3 x).1 hx
        exact ⟨j, by omega, by omega, h3⟩
    · rintro ⟨j, h1, h2, h3⟩
      simp only [List.mem_append]
      by_cases hj1 : j ≤ R1
      · have hx' : (pos₀.trans μ1).symm (pt r j) ∈ δ1 :=
          (hmem1 _).2 ⟨j, h1, hj1, by simp⟩
        have : pos₃ ((pos₀.trans μ1).symm (pt r j)) = pos₃ x := by
          rw [hpos₃old _ (List.mem_append_right _ hx'), h3]; simp
        rw [pos₃.injective this] at hx'
        exact Or.inl (Or.inl hx')
      by_cases hj2 : j < L2'
      · exact Or.inr ((hmem3 x).2 ⟨j, by omega, hj2, h3⟩)
      · obtain ⟨h4, h5⟩ := cmInv_moveD_mem (fl := fl) (L2' := L2') (L2 := L2) (R2 := R2)
          (j := j) (by omega) (by omega)
        rw [hd] at h4 h5
        set j' := cmInv fl d j
        have hx' : ((pos₀.trans μ1).trans μ2).symm (pt r j') ∈ δ2 :=
          (hmem2 _).2 ⟨j', h4, h5, by simp⟩
        obtain ⟨j'', h6, h7, h8, h9⟩ := hpos₃δ2 _ hx'
        have hj'' : j'' = j' := by
          simp only [Equiv.apply_symm_apply] at h8
          exact (ptinj _ _ (by omega) (by omega) (by omega) (by omega) h8).symm
        rw [hj'', show cm fl d j' = j from cm_cmInv fl d j, ← h3] at h9
        rw [pos₃.injective h9] at hx'
        exact Or.inl (Or.inr hx')
  have hσ : σ₀ ++ (δ1 ++ δ2 ++ δ3) = σ₀ ++ δ1 ++ δ2 ++ δ3 := by simp
  refine ⟨δ1 ++ δ2 ++ δ3, μ1.trans (μ2.trans μ3), L1, R2', ?_, ?_, hL1, by omega, ?_, ?_, ?_⟩
  · -- the old region is fixed
    intro p hp
    have hp1 : μ1 p = p := hfix1 p hp
    have hp2 : μ2 p = p := hfix2 p (ball_mono_set (by
      rintro _ ⟨x, hx, rfl⟩; exact ⟨x, List.mem_append_left _ (hx : x ∈ σ₀), hpos₁σ₀ x hx⟩)
      hp)
    have hp3 : μ3 p = p := hfix3 p (ball_mono_set (by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x, List.mem_append_left _ (hx : x ∈ σ₀), ?_⟩
      rw [hpos₂old x (List.mem_append_left _ hx), hpos₁σ₀ x hx]) hp)
    simp [hp1, hp2, hp3]
  · -- no node is revealed twice
    rw [hσ, List.nodup_append]
    refine ⟨hnd2, ?_, ?_⟩
    · refine List.Nodup.map_on (fun i hi i' hi' h => ?_) List.nodup_range
      simp only [List.mem_range] at hi hi'
      have := ptinj _ _ (by omega) (by omega) (by omega) (by omega) (pos₃.symm.injective h)
      omega
    · intro x hx y hy hxy
      subst hxy
      obtain ⟨j, h1, h2, h3⟩ := (hmem3 x).1 hy
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · have hfx := hfar x hx j (by omega) (by omega)
        rw [← hpos₁σ₀ x hx, ← hpos₃old x (List.mem_append_left _ hx), h3, rzpt,
          czpt j (by omega) (by omega)] at hfx
        omega
      · obtain ⟨j1, h4, h5, h6⟩ := (hmem1 x).1 hx
        have h7 := hpos₃old x (List.mem_append_right _ hx)
        rw [h3, show (pos₀.trans μ1) x = μ1 (pos₀ x) from rfl, h6] at h7
        have := ptinj _ _ (by omega) (by omega) (by omega) (by omega) h7
        omega
      · obtain ⟨j2, h4, h5, -, h6⟩ := hpos₃δ2 x hx
        obtain ⟨h7, h8⟩ := hcm j2 h4 h5
        rw [h3] at h6
        have := ptinj _ _ (by omega) (by omega) (by omega) (by omega) h6
        omega
  · omega
  · intro x; exact hnew x
  · -- the factor
    rw [hσ]
    change RowProper (rowCol A T pos₃ (σ₀ ++ δ1 ++ δ2 ++ δ3) r) L1 R2' →
      HasFactor (rowCol A T pos₃ (σ₀ ++ δ1 ++ δ2 ++ δ3) r) L1 R2' (k + 1)
    apply hgood
    · intro j h1 h2
      have hx : (pos₀.trans μ1).symm (pt r j) ∈ δ1 := (hmem1 _).2 ⟨j, h1, h2, by simp⟩
      have hx3 : pos₃.symm (pt r j) = (pos₀.trans μ1).symm (pt r j) := by
        rw [Equiv.symm_apply_eq, hpos₃old _ (List.mem_append_right _ hx)]; simp
      simp only [rowCol, hx3]
      rw [hpos₃, label_after_move A T hag3 δ3
        (List.mem_append_left _ (List.mem_append_right _ hx)),
        label_after_move A T (agreeOn_of_fix μ2 hfix2) δ2 (List.mem_append_right _ hx)]
    · intro j h1 h2
      have hx : ((pos₀.trans μ1).trans μ2).symm (pt r j) ∈ δ2 := (hmem2 _).2 ⟨j, h1, h2, by simp⟩
      obtain ⟨j'', h6, h7, h8, h9⟩ := hpos₃δ2 _ hx
      have hj'' : j'' = j := by
        simp only [Equiv.apply_symm_apply] at h8
        exact (ptinj _ _ (by omega) (by omega) (by omega) (by omega) h8).symm
      rw [hj''] at h9
      have hx3 : pos₃.symm (pt r (cm fl d j)) = ((pos₀.trans μ1).trans μ2).symm (pt r j) := by
        rw [Equiv.symm_apply_eq, h9]
      simp only [rowCol, hx3]
      rw [hpos₃, label_after_move A T hag3 δ3 (List.mem_append_right _ hx)]

/-- **Lemma 3.6** (all `k`). -/
theorem lemma36 (k : ℕ) : Lemma36 (m := m) A T k := by
  induction k with
  | zero => exact lemma36_zero A T
  | succ k ih => exact lemma36_succ A T ih

end Adversary

end Papers.PODC2024.OnlineLocalGrids
