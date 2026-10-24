import Papers.PODC2025.RendezvousLabeledLine.ESRuling
import Cslib.Computability.Distributed.Local.ColorReduction

/-!
# Algorithm 3, colouring part (corrected), and Lemma 3.5

The paper colours the new ruling-set nodes of level `i` by a `(deg+1)`-list colouring of
`G^{9R-1}[S \ S_{<i}]` (lists avoiding the colours of `S_{<i}`), computed with Lemma 2.1 in
`O(R i)` rounds *after* all lower levels are done; this gives the recurrence
`T_i ≤ max(O(R i), T_{i-1}) + O(R i)`, i.e. `T_i = O(R i²)`, not `O(R i)` as claimed.

We split the colouring: Linial's colour reduction on `G^{9R-1}[N_i]` (`N_i` the new nodes of level
`i`, which does not need the colours of lower levels) gives `4096` classes; then the classes are
swept one by one, each new node taking the least colour in `[17]` not used by already coloured
ruling-set nodes within distance `9R - 1` (at most `16` of them). The sweep costs `O(R)` rounds
after the colours of the lower levels are known, so colours of level `i` are decided after
`40000 R i` rounds.
-/

namespace Podc.RendezvousLabeledLine

open Function Classical Cslib.LocallyIterative

namespace ES

variable (R : ℕ)

/-- Sweep over the colour classes `0..c-1` of the new nodes `N` (classes `g`), the old nodes `O`
having colours `old`. -/
noncomputable def swp (O N : ℤ → Prop) (old g : ℤ → ℕ) : ℕ → ℤ → ℕ
  | 0 => fun _ => 0
  | c + 1 => fun w => if g w = c then
      firstFree ({x | ∃ y, O y ∧ |y - w| ≤ 9 * (R : ℤ) - 1 ∧ old y = x} ∪
        {x | ∃ y, N y ∧ y ≠ w ∧ g y < c ∧ |y - w| ≤ 9 * (R : ℤ) - 1 ∧ swp O N old g c y = x})
      else swp O N old g c w

section swp

variable {R} {O N : ℤ → Prop} {old g : ℤ → ℕ}

lemma swp_succ (c : ℕ) (w : ℤ) : swp R O N old g (c + 1) w = if g w = c then
      firstFree ({x | ∃ y, O y ∧ |y - w| ≤ 9 * (R : ℤ) - 1 ∧ old y = x} ∪
        {x | ∃ y, N y ∧ y ≠ w ∧ g y < c ∧ |y - w| ≤ 9 * (R : ℤ) - 1 ∧ swp R O N old g c y = x})
      else swp R O N old g c w := rfl

lemma swp_stable (w : ℤ) : ∀ c, g w < c → swp R O N old g c w = swp R O N old g (g w + 1) w
  | 0, h => absurd h (Nat.not_lt_zero _)
  | c + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · rw [swp_succ, ite_eq_right (by omega), swp_stable w c h]
    · rw [h]

lemma finite_ball_image (P : ℤ → Prop) (f : ℤ → ℕ) (w : ℤ) (r : ℤ) :
    {x | ∃ y, P y ∧ |y - w| ≤ r ∧ f y = x}.Finite := by
  refine ((Set.finite_Icc (w - r) (w + r)).image f).subset ?_
  rintro x ⟨y, -, hy, rfl⟩
  exact ⟨y, by rw [abs_le] at hy; constructor <;> linarith, rfl⟩

/-- The greedy sweep extends a proper colouring with colours `≤ 16` of the old nodes to a proper
colouring with colours `≤ 16` of old and new nodes (all at pairwise distance `≥ R`). -/
theorem swp_spec (hR : 1 ≤ R) (K : ℕ) (hON : ∀ y, O y → ¬ N y)
    (hpack : Packed (fun y => O y ∨ N y) R)
    (hold : ∀ y y', O y → O y' → y ≠ y' → |y - y'| ≤ 9 * (R : ℤ) - 1 → old y ≠ old y')
    (hold16 : ∀ y, O y → old y ≤ 16)
    (hg : ∀ y y', N y → N y' → y ≠ y' → |y - y'| ≤ 9 * (R : ℤ) - 1 → g y ≠ g y')
    (hgK : ∀ y, N y → g y < K) :
    let col := fun y => if N y then swp R O N old g K y else old y
    (∀ y y', (O y ∨ N y) → (O y' ∨ N y') → y ≠ y' → |y - y'| ≤ 9 * (R : ℤ) - 1 →
      col y ≠ col y') ∧ ∀ y, (O y ∨ N y) → col y ≤ 16 := by
  intro col
  have hcolN : ∀ y, N y → col y = swp R O N old g (g y + 1) y := fun y hy => by
    simp only [col, ite_eq_left hy]; exact swp_stable y K (hgK y hy)
  have hcolO : ∀ y, O y → col y = old y := fun y hy => by simp [col, hON y hy]
  -- the colour of a new node avoids the set `F w`
  let F := fun w => {x | ∃ y, O y ∧ |y - w| ≤ 9 * (R : ℤ) - 1 ∧ old y = x} ∪
    {x | ∃ y, N y ∧ y ≠ w ∧ g y < g w ∧ |y - w| ≤ 9 * (R : ℤ) - 1 ∧
      swp R O N old g (g w) y = x}
  have hFfin : ∀ w, (F w).Finite := fun w =>
    (finite_ball_image _ _ _ _).union ((finite_ball_image (fun y => N y ∧ y ≠ w ∧ g y < g w)
      (swp R O N old g (g w)) w (9 * R - 1)).subset (by
        rintro x ⟨y, h1, h2, h3, h4, h5⟩; exact ⟨y, ⟨h1, h2, h3⟩, h4, h5⟩))
  have hswp : ∀ w, N w → swp R O N old g (g w + 1) w = firstFree (F w) := fun w hw => by
    rw [swp_succ, ite_eq_left rfl]
  have hnot : ∀ w, N w → col w ∉ F w := fun w hw => by
    rw [hcolN w hw, hswp w hw]; exact firstFree_notMem (hFfin w)
  -- `F w` consists of colours of ruling-set nodes within `9R - 1` of `w`
  have hFsub : ∀ w, N w → F w ⊆ col '' {u | (O u ∨ N u) ∧ u ≠ w ∧ |u - w| ≤ ((9 * R - 1 : ℕ) : ℤ)} := by
    intro w hw x hx
    have h9 : ((9 * R - 1 : ℕ) : ℤ) = 9 * (R : ℤ) - 1 := by push_cast [show 1 ≤ 9 * R by omega]; ring
    rcases hx with ⟨y, hy, hyw, rfl⟩ | ⟨y, hy, hyw, hlt, hd, rfl⟩
    · exact ⟨y, ⟨Or.inl hy, fun h => hON y hy (h ▸ hw), by rw [h9]; exact hyw⟩, hcolO y hy⟩
    · refine ⟨y, ⟨Or.inr hy, hyw, by rw [h9]; exact hd⟩, ?_⟩
      rw [hcolN y hy, swp_stable y (g w) hlt]
  have hncard : ∀ w, N w → (F w).ncard ≤ 16 := fun w hw => by
    have hfin : {u | (O u ∨ N u) ∧ u ≠ w ∧ |u - w| ≤ ((9 * R - 1 : ℕ) : ℤ)}.Finite :=
      (Set.finite_Icc (w - (9 * R - 1 : ℕ)) (w + (9 * R - 1 : ℕ))).subset fun u hu => by
        have := abs_le.1 hu.2.2; constructor <;> linarith
    calc (F w).ncard ≤ (col '' _).ncard := Set.ncard_le_ncard (hFsub w hw) (hfin.image _)
      _ ≤ _ := Set.ncard_image_le hfin
      _ ≤ 2 * ((9 * R - 1) / R) :=
        ncard_nbrs_le_of_packed (S := fun _ => fun y => O y ∨ N y) (ℓ := fun _ => 0) (k := 9 * R - 1)
          hpack hR (Or.inr hw)
      _ ≤ 16 := by
        have : (9 * R - 1) / R ≤ 8 := Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2
          (by omega))
        omega
  refine ⟨fun y y' hy hy' hne hd => ?_, fun y hy => ?_⟩
  · rcases hy with hy | hy <;> rcases hy' with hy' | hy'
    · rw [hcolO y hy, hcolO y' hy']; exact hold y y' hy hy' hne hd
    · intro h; apply hnot y' hy'; rw [← h, hcolO y hy]
      exact Or.inl ⟨y, hy, hd, rfl⟩
    · intro h; apply hnot y hy; rw [h, hcolO y' hy']
      exact Or.inl ⟨y', hy', by rwa [abs_sub_comm], rfl⟩
    · rcases lt_or_gt_of_ne (hg y y' hy hy' hne hd) with hlt | hlt
      · intro h; apply hnot y' hy'; rw [← h]
        refine Or.inr ⟨y, hy, hne, hlt, hd, ?_⟩
        rw [hcolN y hy, swp_stable y (g y') hlt]
      · intro h; apply hnot y hy; rw [h]
        refine Or.inr ⟨y', hy', hne.symm, hlt, by rwa [abs_sub_comm], ?_⟩
        rw [hcolN y' hy', swp_stable y' (g y) hlt]
  · rcases hy with hy | hy
    · rw [hcolO y hy]; exact hold16 y hy
    · rw [hcolN y hy, hswp y hy]
      exact (firstFree_le_ncard (hFfin y)).trans (hncard y hy)

/-- Locality of the sweep: `c` classes cost `9 R c` rounds. -/
lemma swp_congr {O' N' : ℤ → Prop} {old' g' : ℤ → ℕ} : ∀ (c : ℕ) (w r : ℤ), 9 * (R : ℤ) * c ≤ r →
    (∀ y, |y - w| ≤ r → (O y ↔ O' y) ∧ (N y ↔ N' y) ∧ old y = old' y ∧ g y = g' y) →
    swp R O N old g c w = swp R O' N' old' g' c w
  | 0, _, _, _, _ => rfl
  | c + 1, w, r, hr, h => by
    have h9 : (0 : ℤ) ≤ 9 * R * c := by positivity
    have hr' : 9 * (R : ℤ) * c + 9 * R ≤ r := by push_cast at hr; linarith
    have hw := h w (by simp; omega)
    have hin : ∀ y, |y - w| ≤ 9 * (R : ℤ) - 1 → |y - w| ≤ r := fun y hy => by omega
    have hrec : ∀ y, |y - w| ≤ 9 * (R : ℤ) →
        swp R O N old g c y = swp R O' N' old' g' c y := fun y hy =>
      swp_congr c y (r - 9 * R) (by linarith) fun z hz => h z (by
        calc |z - w| = |(z - y) + (y - w)| := by ring_nf
          _ ≤ |z - y| + |y - w| := abs_add_le _ _
          _ ≤ r := by linarith)
    have hA : {x | ∃ y, O y ∧ |y - w| ≤ 9 * (R : ℤ) - 1 ∧ old y = x} =
        {x | ∃ y, O' y ∧ |y - w| ≤ 9 * (R : ℤ) - 1 ∧ old' y = x} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      refine exists_congr fun y => ⟨fun ⟨h1, h2, h3⟩ => ?_, fun ⟨h1, h2, h3⟩ => ?_⟩
      · have hy := h y (hin y h2)
        exact ⟨hy.1.1 h1, h2, by rw [← hy.2.2.1]; exact h3⟩
      · have hy := h y (hin y h2)
        exact ⟨hy.1.2 h1, h2, by rw [hy.2.2.1]; exact h3⟩
    have hB : {x | ∃ y, N y ∧ y ≠ w ∧ g y < c ∧ |y - w| ≤ 9 * (R : ℤ) - 1 ∧
          swp R O N old g c y = x} =
        {x | ∃ y, N' y ∧ y ≠ w ∧ g' y < c ∧ |y - w| ≤ 9 * (R : ℤ) - 1 ∧
          swp R O' N' old' g' c y = x} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      refine exists_congr fun y => ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ?_, fun ⟨h1, h2, h3, h4, h5⟩ => ?_⟩
      · have hy := h y (hin y h4)
        exact ⟨hy.2.1.1 h1, h2, by rw [← hy.2.2.2]; exact h3, h4,
          by rw [← hrec y (by omega)]; exact h5⟩
      · have hy := h y (hin y h4)
        exact ⟨hy.2.1.2 h1, h2, by rw [hy.2.2.2]; exact h3, h4,
          by rw [hrec y (by omega)]; exact h5⟩
    rw [swp_succ, swp_succ, hw.2.2.2, hA, hB, hrec w (by rw [sub_self, abs_zero]; positivity)]

lemma swp_frame (v : ℤ) (ε : ℤˣ) : ∀ c i,
    swp R (O ∘ frame v ε) (N ∘ frame v ε) (old ∘ frame v ε) (g ∘ frame v ε) c i =
      swp R O N old g c (frame v ε i)
  | 0, _ => rfl
  | c + 1, i => by
    have hA : {x | ∃ y, (O ∘ frame v ε) y ∧ |y - i| ≤ 9 * (R : ℤ) - 1 ∧ (old ∘ frame v ε) y = x} =
        {x | ∃ y, O y ∧ |y - frame v ε i| ≤ 9 * (R : ℤ) - 1 ∧ old y = x} := by
      ext x
      simp only [Set.mem_ofPred_eq, comp]
      constructor
      · rintro ⟨y, h1, h2, h3⟩; exact ⟨_, h1, by rwa [abs_frame_sub_frame], h3⟩
      · rintro ⟨y, h1, h2, h3⟩
        obtain ⟨y', rfl⟩ := frame_surjective v ε y
        exact ⟨y', h1, by rwa [abs_frame_sub_frame] at h2, h3⟩
    have hB : {x | ∃ y, (N ∘ frame v ε) y ∧ y ≠ i ∧ (g ∘ frame v ε) y < c ∧
          |y - i| ≤ 9 * (R : ℤ) - 1 ∧
          swp R (O ∘ frame v ε) (N ∘ frame v ε) (old ∘ frame v ε) (g ∘ frame v ε) c y = x} =
        {x | ∃ y, N y ∧ y ≠ frame v ε i ∧ g y < c ∧ |y - frame v ε i| ≤ 9 * (R : ℤ) - 1 ∧
          swp R O N old g c y = x} := by
      ext x
      simp only [Set.mem_ofPred_eq, comp]
      constructor
      · rintro ⟨y, h1, h2, h3, h4, h5⟩
        refine ⟨_, h1, (frame_injective v ε).ne h2, h3, by rwa [abs_frame_sub_frame], ?_⟩
        rw [← swp_frame v ε c y]; exact h5
      · rintro ⟨y, h1, h2, h3, h4, h5⟩
        obtain ⟨y', rfl⟩ := frame_surjective v ε y
        refine ⟨y', h1, fun h => h2 (h ▸ rfl), h3, by rwa [abs_frame_sub_frame] at h4, ?_⟩
        rw [swp_frame v ε c y']; exact h5
    simp only [swp]
    rw [hA, hB, swp_frame v ε c i]
    rfl

end swp

/-! ### The colouring of Algorithm 3 -/

/-- New ruling-set nodes of level `i`. -/
def Nw (i : ℕ) : (ℤ → ℕ) → ℤ → Prop := fun ℓ v => Sle R i ℓ v ∧ lstar (ℓ v) = i

/-- Linial classes of the new nodes of level `i` on `G^{9R-1}[N_i]` (degree `≤ 16`). -/
noncomputable def gam (i : ℕ) : (ℤ → ℕ) → ℤ → ℕ := colRule (Nw R i) (9 * R - 1) (Nat.tower i) 16

/-- Colours of the ruling-set nodes of levels `≤ i`. -/
noncomputable def colLe : ℕ → (ℤ → ℕ) → ℤ → ℕ
  | 0 => fun _ _ => 0
  | i + 1 => fun ℓ w => if Nw R (i + 1) ℓ w then
      swp R (Sle R i ℓ) (Nw R (i + 1) ℓ) (colLe i ℓ) (gam R (i + 1) ℓ) 4096 w else colLe i ℓ w

lemma colLe_stable {ℓ : ℤ → ℕ} {w : ℤ} {i j : ℕ} (hij : i ≤ j) (hw : lstar (ℓ w) ≤ i) :
    colLe R j ℓ w = colLe R i ℓ w := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← ih (by omega), show i + (d + 1) = (i + d) + 1 by ring]
    simp only [colLe]
    rw [ite_eq_right (by rintro ⟨-, h⟩; omega)]

/-- Properness of `colLe i` on `S_{≤ i}` (the colouring part of Lemma 3.5 (3)). -/
theorem colLe_spec (hR : 1 ≤ R) {ℓ : ℤ → ℕ} (hℓ : Injective ℓ) (i : ℕ) :
    (∀ y y', Sle R i ℓ y → Sle R i ℓ y' → y ≠ y' → |y - y'| ≤ 9 * (R : ℤ) - 1 →
      colLe R i ℓ y ≠ colLe R i ℓ y') ∧ ∀ y, Sle R i ℓ y → colLe R i ℓ y ≤ 16 := by
  induction i with
  | zero => exact ⟨fun _ _ h => h.elim, fun _ h => h.elim⟩
  | succ i ih =>
    obtain ⟨s1, s2, -, s4, s5⟩ := Sle_spec R hR hℓ i
    obtain ⟨t1, -, -, -, -⟩ := Sle_spec R hR hℓ (i + 1)
    have hU : ∀ y, Sle R (i + 1) ℓ y ↔ Sle R i ℓ y ∨ Nw R (i + 1) ℓ y := fun y =>
      ⟨fun h => by
        by_cases hl : lstar (ℓ y) ≤ i
        · exact Or.inl (s5 y h hl)
        · obtain ⟨-, h2, -⟩ := Sle_spec R hR hℓ (i + 1)
          exact Or.inr ⟨h, by have := h2 y h; omega⟩,
       fun h => h.elim (s4 y) And.left⟩
    have hpack : Packed (fun y => Sle R i ℓ y ∨ Nw R (i + 1) ℓ y) R := fun u w hu hw =>
      t1 u w ((hU u).2 hu) ((hU w).2 hw)
    have hpN : Packed (Nw R (i + 1) ℓ) R := fun u w hu hw => t1 u w hu.1 hw.1
    obtain ⟨g1, g2⟩ := colRule_spec (Nw R (i + 1)) (9 * R - 1) (Nat.tower (i + 1)) 16
      (by norm_num) hℓ (fun v hv => (ncard_nbrs_le_of_packed hpN hR hv).trans (by
        have : (9 * R - 1) / R ≤ 8 := Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2
          (by omega))
        omega)) (fun v hv => lt_tower_of_lstar hv.2)
    have h9 : ((9 * R - 1 : ℕ) : ℤ) = 9 * (R : ℤ) - 1 := by
      push_cast [show 1 ≤ 9 * R by omega]; ring
    obtain ⟨c1, c2⟩ := swp_spec (R := R) (O := Sle R i ℓ) (N := Nw R (i + 1) ℓ)
      (old := colLe R i ℓ) (g := gam R (i + 1) ℓ) hR 4096
      (fun y hy hN => by have := s2 y hy; have := hN.2; omega) hpack ih.1 ih.2
      (fun y y' hy hy' hne hd => g1 y y' hy hy' hne (by rw [h9]; exact hd))
      (fun y _ => by have := g2 y; norm_num at this; exact this)
    exact ⟨fun y y' hy hy' => c1 y y' ((hU y).1 hy) ((hU y').1 hy'),
      fun y hy => c2 y ((hU y).1 hy)⟩

/-! ### Locality and equivariance of the colours -/

lemma Nw_isLocal (hR : 1 ≤ R) (i : ℕ) : IsLocal (Nw R i) (816 * R * i) := by
  intro ℓ ℓ' h h' v hv
  have h0 : (0 : ℤ) ≤ ((816 * R * i : ℕ) : ℤ) := by positivity
  simp only [Nw, Sle_isLocal R hR i ℓ ℓ' h h' v hv, hv v (by simpa using h0)]

lemma gam_isLocal (hR : 1 ≤ R) (i : ℕ) : IsLocal (gam R i) (825 * R * i + 27 * R) := by
  refine (colRule_isLocal (Nw_isLocal R hR i) _ _ 16).mono ?_
  have h1 := logStar_tower_le i
  have : (9 * R - 1) * (Nat.logStar (Nat.tower i) + 3) ≤ 9 * R * (i + 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

/-- Colours of level `≤ i` are decided after `40000 R i` rounds. -/
theorem colLe_isLocal (hR : 1 ≤ R) (i : ℕ) : IsLocal (colLe R i) (40000 * R * i) := by
  induction i with
  | zero => intro _ _ _ _ _ _; rfl
  | succ i ih =>
    intro ℓ ℓ' h h' w hw
    have hball : ∀ (ρ : ℕ) (y : ℤ) (r : ℤ), |y - w| ≤ r → (ρ : ℤ) + r ≤ 40000 * R * (i + 1) →
        ∀ x, |x - y| ≤ ρ → ℓ' x = ℓ x := fun ρ y r hy hr x hx => hw x (by
      calc |x - w| = |(x - y) + (y - w)| := by ring_nf
        _ ≤ |x - y| + |y - w| := abs_add_le _ _
        _ ≤ _ := by push_cast; omega)
    have hRi : (0 : ℤ) ≤ R * i := by positivity
    have hR' : (1 : ℤ) ≤ R := by exact_mod_cast hR
    have hN : Nw R (i + 1) ℓ' w ↔ Nw R (i + 1) ℓ w := by
      rw [Nw_isLocal R hR (i + 1) ℓ ℓ' h h' w (hball _ w 0 (by simp) (by push_cast; nlinarith))]
    simp only [colLe]
    by_cases hn : Nw R (i + 1) ℓ w
    · rw [ite_eq_left (hN.2 hn), ite_eq_left hn]
      refine swp_congr 4096 w (9 * R * 4096) (by simp) fun y hy => ⟨?_, ?_, ?_, ?_⟩
      · rw [Sle_isLocal R hR i ℓ ℓ' h h' y (hball _ y _ hy (by push_cast; nlinarith))]
      · rw [Nw_isLocal R hR (i + 1) ℓ ℓ' h h' y (hball _ y _ hy (by push_cast; nlinarith))]
      · exact ih ℓ ℓ' h h' y (hball _ y _ hy (by push_cast; nlinarith))
      · exact gam_isLocal R hR (i + 1) ℓ ℓ' h h' y (hball _ y _ hy (by push_cast; nlinarith))
    · rw [ite_eq_right (mt hN.1 hn), ite_eq_right hn]
      exact ih ℓ ℓ' h h' w (hball _ w 0 (by simp) (by push_cast; nlinarith))

lemma Nw_isEquivar (i : ℕ) : IsEquivar (Nw R i) := by
  intro ℓ v ε j
  simp only [Nw, Sle_isEquivar R i ℓ v ε j, comp]

theorem colLe_isEquivar (i : ℕ) : IsEquivar (colLe R i) := by
  induction i with
  | zero => intro _ _ _ _; rfl
  | succ i ih =>
    intro ℓ v ε j
    simp only [colLe]
    rw [Nw_isEquivar R (i + 1) ℓ v ε j]
    split_ifs
    · have e1 : Sle R i (ℓ ∘ frame v ε) = Sle R i ℓ ∘ frame v ε :=
        funext fun x => Sle_isEquivar R i ℓ v ε x
      have e2 : Nw R (i + 1) (ℓ ∘ frame v ε) = Nw R (i + 1) ℓ ∘ frame v ε :=
        funext fun x => Nw_isEquivar R (i + 1) ℓ v ε x
      have e3 : colLe R i (ℓ ∘ frame v ε) = colLe R i ℓ ∘ frame v ε :=
        funext fun x => ih ℓ v ε x
      have e4 : gam R (i + 1) (ℓ ∘ frame v ε) = gam R (i + 1) ℓ ∘ frame v ε :=
        funext fun x => colRule_isEquivar (Nw_isEquivar R (i + 1)) _ _ 16 ℓ v ε x
      rw [e1, e2, e3, e4, swp_frame]
    · exact ih ℓ v ε j

end ES

end Podc.RendezvousLabeledLine
