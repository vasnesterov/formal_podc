import Papers.PODC2020.DynamicPartitioningLB.Model

/-!
# Lemma 3.1: for `k = 3`, a merge needs at most two swaps

Pacut, Parham, Schmid, PODC 2020, Section 3, Lemma 3.1 (stated without proof in the paper):
"In a single repartition of nodes, ALG3 exchanges at most two pairs of nodes."

ALG3 keeps a component-respecting balanced configuration `P` (clusters of size `3`); when the
components of `a` and `b` (with `P a ≠ P b`) are merged it moves to the component-respecting
configuration *closest to `P`*, if one exists. We prove that some (hence the closest) such
configuration is at distance `≤ 4` from `P`, i.e. two swaps suffice (`lemma_3_1`,
`lemma_3_1_closest`).

Components are given by a labelling `comp : V → V`; the merged component structure is expressed
by the requirement `Q a = Q b` on top of respecting `comp`.

**Proof.** Let `X = P a`, `Y = P b`. Feasibility gives `|C(a)| + |C(b)| ≤ 3`.
* If `Y` holds a singleton component `s ≠ b` and `a` is a singleton, swap `a ↔ s` (this covers
  `|C(b)| = 2`). Symmetrically for `X`.
* Otherwise `a`, `b` are singletons and `X`, `Y` hold no other singleton. Every cluster of a
  component-respecting configuration has `(#singletons, #nodes in pairs) ∈ {(0,0), (3,0), (1,2)}`
  (`cluster_shape`). If no cluster of `P` consisted of three singletons, `2·#singletons =
  #pair-nodes` would hold globally; but a feasible `Q` has a cluster `{a, b, ·}` of three
  singletons, so `2·#singletons ≥ #pair-nodes + 6`. Hence some cluster `Z` of `P` consists of three
  singletons `x, y, ·`, and the two swaps `a ↔ x`, `b ↔ y` work.
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DynamicPartitioningLB.K3

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {ℓ : ℕ}

/-- The component of `v`. -/
def cls (comp : V → V) (v : V) : Finset V := univ.filter (fun w => comp w = comp v)

/-- Size of the component of `v`. -/
def csize (comp : V → V) (v : V) : ℕ := (cls comp v).card

/-- `R` collocates every component. -/
def Respects (comp : V → V) (R : Config V ℓ) : Prop := ∀ u v, comp u = comp v → R u = R v

/-- Nodes of cluster `c`. -/
def fiber (R : Config V ℓ) (c : Fin ℓ) : Finset V := univ.filter (fun v => R v = c)

variable {comp : V → V}

lemma mem_cls {v w : V} : w ∈ cls comp v ↔ comp w = comp v := by simp [cls]

lemma self_mem_cls (v : V) : v ∈ cls comp v := mem_cls.2 rfl

lemma cls_eq {u v : V} (h : comp u = comp v) : cls comp u = cls comp v := by
  ext w; simp [mem_cls, h]

lemma csize_pos (v : V) : 1 ≤ csize comp v := card_pos.2 ⟨v, self_mem_cls v⟩

lemma eq_of_csize_one {s w : V} (hs : csize comp s = 1) (hw : comp w = comp s) : w = s := by
  obtain ⟨x, hx⟩ := card_eq_one.1 hs
  have h1 : w ∈ cls comp s := mem_cls.2 hw
  have h2 : s ∈ cls comp s := self_mem_cls s
  rw [hx, mem_singleton] at h1 h2
  rw [h1, h2]

lemma cls_subset_fiber {R : Config V ℓ} (hR : Respects comp R) (v : V) :
    cls comp v ⊆ fiber R (R v) := by
  intro w hw; simp only [fiber, mem_filter, mem_univ, true_and]; exact hR w v (mem_cls.1 hw)

lemma card_fiber (hV : Fintype.card V = ℓ * 3) {R : Config V ℓ} (hR : Balanced 3 R) (c : Fin ℓ) :
    (fiber R c).card = 3 := card_fiber_eq hV hR c

/-! ### Swaps of singleton components -/

lemma perm_balanced {R : Config V ℓ} (hR : Balanced 3 R) (τ : Equiv.Perm V) :
    Balanced 3 (fun v => R (τ v)) := by
  intro c
  rw [card_equiv τ (t := univ.filter (fun v => R v = c)) (fun i => by simp)]
  exact hR c

lemma perm_respects {R : Config V ℓ} (hR : Respects comp R) {S : Finset V}
    (hS : ∀ s ∈ S, csize comp s = 1) {τ : Equiv.Perm V} (hτ : ∀ v ∉ S, τ v = v) :
    Respects comp (fun v => R (τ v)) := by
  intro u v huv
  by_cases hu : u ∈ S
  · rw [eq_of_csize_one (hS u hu) huv.symm]
  by_cases hv : v ∈ S
  · rw [eq_of_csize_one (hS v hv) huv]
  simp only [hτ u hu, hτ v hv]; exact hR u v huv

lemma perm_dist (R : Config V ℓ) {S : Finset V} {τ : Equiv.Perm V} (hτ : ∀ v ∉ S, τ v = v) :
    dist R (fun v => R (τ v)) ≤ S.card :=
  dist_le_of_subset fun v hv => by
    by_contra hS; exact hv (by simp only [hτ v hS])

/-- One swap: if `a` and some `s` collocated with `b` are singletons, swapping them works. -/
lemma swap_into {P : Config V ℓ} (hPb : Balanced 3 P) (hP : Respects comp P) {a b s : V}
    (hab : P a ≠ P b) (ha : csize comp a = 1) (hs : csize comp s = 1) (hsb : P s = P b)
    (hsb' : s ≠ b) :
    ∃ Q, Balanced 3 Q ∧ Respects comp Q ∧ Q a = Q b ∧ dist P Q ≤ 4 := by
  have hba : b ≠ a := fun h => hab (h ▸ rfl)
  refine ⟨fun v => P (Equiv.swap a s v), perm_balanced hPb _,
    perm_respects hP (S := {a, s}) (by simp [ha, hs]) (fun v hv => ?_), ?_, ?_⟩
  · simp only [mem_insert, mem_singleton, not_or] at hv
    exact Equiv.swap_apply_of_ne_of_ne hv.1 hv.2
  · simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hba hsb'.symm, hsb]
  · refine (perm_dist P (S := {a, s}) fun v hv => ?_).trans ((card_le_two).trans (by norm_num))
    simp only [mem_insert, mem_singleton, not_or] at hv
    exact Equiv.swap_apply_of_ne_of_ne hv.1 hv.2

/-- A cluster holding a component of size `2` holds a singleton component. -/
lemma exists_single (hV : Fintype.card V = ℓ * 3) {R : Config V ℓ} (hRb : Balanced 3 R)
    (hR : Respects comp R) {v : V} (hv : csize comp v = 2) :
    ∃ w, R w = R v ∧ comp w ≠ comp v ∧ csize comp w = 1 ∧
      fiber R (R v) = insert w (cls comp v) := by
  have hsub := cls_subset_fiber hR v
  have hF := card_fiber hV hRb (R v)
  have hlt : (cls comp v).card < (fiber R (R v)).card := by
    rw [hF]; unfold csize at hv; omega
  obtain ⟨w, hwF, hwc⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hwR : R w = R v := by simpa [fiber] using hwF
  have hwc' : comp w ≠ comp v := fun h => hwc (mem_cls.2 h)
  have hins : fiber R (R v) = insert w (cls comp v) := by
    symm
    apply eq_of_subset_of_card_le (insert_subset hwF hsub)
    rw [card_insert_of_notMem hwc, hF]; unfold csize at hv; omega
  refine ⟨w, hwR, hwc', ?_, hins⟩
  have hsubw : cls comp w ⊆ {w} := by
    intro u hu
    have hu' := cls_subset_fiber hR w hu
    rw [hwR, hins, mem_insert] at hu'
    rcases hu' with rfl | hu'
    · exact mem_singleton_self _
    · exact absurd ((mem_cls.1 hu).symm.trans (mem_cls.1 hu')) hwc'
  have h1 := card_le_card hsubw
  have h2 := csize_pos (comp := comp) w
  rw [card_singleton] at h1
  unfold csize at h2 ⊢; omega

/-! ### Counting singletons and pair-nodes -/

/-- Number of singleton nodes in cluster `c`. -/
def sCount (comp : V → V) (R : Config V ℓ) (c : Fin ℓ) : ℕ :=
  ((univ.filter (fun v => csize comp v = 1)).filter (fun v => R v = c)).card

/-- Number of nodes of components of size `2` in cluster `c`. -/
def pCount (comp : V → V) (R : Config V ℓ) (c : Fin ℓ) : ℕ :=
  ((univ.filter (fun v => csize comp v = 2)).filter (fun v => R v = c)).card

lemma filter_fiber (p : V → Prop) [DecidablePred p] (R : Config V ℓ) (c : Fin ℓ) :
    (univ.filter p).filter (fun v => R v = c) = (fiber R c).filter p := by
  ext v; simp [fiber, and_comm]

/-- Shape of a cluster of a component-respecting balanced configuration. -/
lemma cluster_shape (hV : Fintype.card V = ℓ * 3) {R : Config V ℓ} (hRb : Balanced 3 R)
    (hR : Respects comp R) (c : Fin ℓ) :
    (pCount comp R c = 0 ∧ (sCount comp R c = 0 ∨ sCount comp R c = 3)) ∨
      (pCount comp R c = 2 ∧ sCount comp R c = 1) := by
  unfold pCount sCount
  rw [filter_fiber, filter_fiber]
  have hF := card_fiber hV hRb c
  by_cases h2 : ∃ v ∈ fiber R c, csize comp v = 2
  · obtain ⟨v, hvF, hv⟩ := h2
    have hvc : R v = c := by simpa [fiber] using hvF
    obtain ⟨w, -, hwc, hw1, hins⟩ := exists_single hV hRb hR hv
    rw [hvc] at hins
    right
    have hcsz : ∀ u ∈ cls comp v, csize comp u = 2 := fun u hu => by
      unfold csize; rw [cls_eq (mem_cls.1 hu)]; exact hv
    have hwn : w ∉ cls comp v := fun h => hwc (mem_cls.1 h)
    rw [hins, filter_insert, filter_insert, ite_eq_right (by omega), ite_eq_left hw1]
    constructor
    · rw [filter_true_of_mem hcsz]; exact hv
    · rw [filter_false_of_mem (fun u hu => by rw [hcsz u hu]; omega), insert_empty, card_singleton]
  · push Not at h2
    left
    refine ⟨by rw [card_eq_zero, filter_eq_empty_iff]; exact h2, ?_⟩
    by_cases h3 : ∃ v ∈ fiber R c, csize comp v ≠ 1
    · left
      obtain ⟨v, hvF, hv⟩ := h3
      have hvc : R v = c := by simpa [fiber] using hvF
      have hv3 : 3 ≤ csize comp v := by
        have := csize_pos (comp := comp) v; have := h2 v hvF; omega
      have hcls : cls comp v = fiber R c := by
        apply eq_of_subset_of_card_le (hvc ▸ cls_subset_fiber hR v)
        rw [hF]; exact hv3
      rw [card_eq_zero, filter_eq_empty_iff]
      intro u hu
      rw [← hcls] at hu
      unfold csize; rw [cls_eq (mem_cls.1 hu)]; unfold csize at hv3; omega
    · right
      push Not at h3
      rw [filter_true_of_mem h3, hF]

lemma sum_sCount (R : Config V ℓ) :
    ∑ c, sCount comp R c = (univ.filter (fun v => csize comp v = 1)).card :=
  (card_eq_sum_card_fiberwise fun _ _ => mem_univ _).symm

lemma sum_pCount (R : Config V ℓ) :
    ∑ c, pCount comp R c = (univ.filter (fun v => csize comp v = 2)).card :=
  (card_eq_sum_card_fiberwise fun _ _ => mem_univ _).symm

/-- If two singletons `a ≠ b` can be collocated by a component-respecting configuration, some
cluster of every component-respecting configuration consists of three singletons. -/
lemma exists_triple (hV : Fintype.card V = ℓ * 3) {P Q : Config V ℓ} (hPb : Balanced 3 P)
    (hP : Respects comp P) (hQb : Balanced 3 Q) (hQ : Respects comp Q) {a b : V}
    (hab : a ≠ b) (ha : csize comp a = 1) (hb : csize comp b = 1) (hQab : Q a = Q b) :
    ∃ c, sCount comp P c = 3 := by
  by_contra hno
  push Not at hno
  have hP2 : ∀ c, 2 * sCount comp P c = pCount comp P c := by
    intro c
    rcases cluster_shape hV hPb hP c with ⟨h1, h2 | h2⟩ | ⟨h1, h2⟩
    · omega
    · exact absurd h2 (hno c)
    · omega
  have hQ2 : ∀ c, pCount comp Q c ≤ 2 * sCount comp Q c := by
    intro c
    rcases cluster_shape hV hQb hQ c with ⟨h1, h2 | h2⟩ | ⟨h1, h2⟩ <;> omega
  have hW : pCount comp Q (Q a) + 6 ≤ 2 * sCount comp Q (Q a) := by
    have h2 : 2 ≤ sCount comp Q (Q a) := by
      have : ({a, b} : Finset V) ⊆
          (univ.filter (fun v => csize comp v = 1)).filter (fun v => Q v = Q a) := by
        intro v hv
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl <;> simp [ha, hb, hQab]
      have := card_le_card this
      rwa [card_pair hab] at this
    rcases cluster_shape hV hQb hQ (Q a) with ⟨h1, h3 | h3⟩ | ⟨h1, h3⟩ <;> omega
  have hsumP : 2 * ∑ c, sCount comp P c = ∑ c, pCount comp P c := by
    rw [mul_sum]; exact sum_congr rfl fun c _ => hP2 c
  have hsumQ : ∑ c, pCount comp Q c + 6 ≤ 2 * ∑ c, sCount comp Q c := by
    rw [mul_sum, ← add_sum_erase _ _ (mem_univ (Q a)), ← add_sum_erase _ _ (mem_univ (Q a))]
    have := sum_le_sum fun c (_ : c ∈ univ.erase (Q a)) => hQ2 c
    omega
  rw [sum_sCount, sum_pCount] at hsumP hsumQ
  omega

/-- **Lemma 3.1** (Pacut, Parham, Schmid, PODC 2020), for clusters of size `k = 3`. Let `P` be a
balanced configuration respecting the components, and merge the components of `a` and `b`, which
`P` separates. If some balanced configuration respects the merged components, then one does at
distance at most `4` from `P` (two swaps). -/
theorem lemma_3_1 (hV : Fintype.card V = ℓ * 3) {P : Config V ℓ} (hPb : Balanced 3 P)
    (hP : Respects comp P) {a b : V} (hab : P a ≠ P b)
    (hfeas : ∃ Q : Config V ℓ, Balanced 3 Q ∧ Respects comp Q ∧ Q a = Q b) :
    ∃ Q, Balanced 3 Q ∧ Respects comp Q ∧ Q a = Q b ∧ dist P Q ≤ 4 := by
  obtain ⟨Q, hQb, hQ, hQab⟩ := hfeas
  have hcab : comp a ≠ comp b := fun h => hab (hP a b h)
  have hne : a ≠ b := fun h => hab (h ▸ rfl)
  -- the merged component fits in a cluster
  have hsize : csize comp a + csize comp b ≤ 3 := by
    have hdisj : Disjoint (cls comp a) (cls comp b) := by
      rw [disjoint_left]; intro w h1 h2; exact hcab ((mem_cls.1 h1).symm.trans (mem_cls.1 h2))
    have hsub : cls comp a ∪ cls comp b ⊆ fiber Q (Q a) :=
      union_subset (cls_subset_fiber hQ a) (hQab ▸ cls_subset_fiber hQ b)
    have := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_fiber hV hQb] at this
    exact this
  have hpa := csize_pos (comp := comp) a
  have hpb := csize_pos (comp := comp) b
  -- a singleton partner next to `b`
  by_cases hY : csize comp a = 1 ∧ ∃ s, P s = P b ∧ s ≠ b ∧ csize comp s = 1
  · obtain ⟨ha, s, hsb, hs, hs1⟩ := hY
    exact swap_into hPb hP hab ha hs1 hsb hs
  by_cases hX : csize comp b = 1 ∧ ∃ s, P s = P a ∧ s ≠ a ∧ csize comp s = 1
  · obtain ⟨hb, s, hsa, hs, hs1⟩ := hX
    obtain ⟨Q', h1, h2, h3, h4⟩ := swap_into hPb hP (Ne.symm hab) hb hs1 hsa hs
    exact ⟨Q', h1, h2, h3.symm, h4⟩
  -- both are singletons
  have ha : csize comp a = 1 := by
    by_contra ha
    obtain ⟨w, hw, hwc, hw1, -⟩ := exists_single hV hPb hP (v := a) (by omega)
    exact hX ⟨by omega, w, hw, fun h => hwc (h ▸ rfl), hw1⟩
  have hb : csize comp b = 1 := by
    by_contra hb
    obtain ⟨w, hw, hwc, hw1, -⟩ := exists_single hV hPb hP (v := b) (by omega)
    exact hY ⟨ha, w, hw, fun h => hwc (h ▸ rfl), hw1⟩
  -- a cluster of three singletons
  obtain ⟨Z, hZ⟩ := exists_triple hV hPb hP hQb hQ hne ha hb hQab
  have hZall : ∀ v, P v = Z → csize comp v = 1 := by
    have hsub : (univ.filter (fun v => csize comp v = 1)).filter (fun v => P v = Z) ⊆
        fiber P Z := by intro v; simp [fiber]
    have heq := eq_of_subset_of_card_le hsub (by rw [card_fiber hV hPb]; unfold sCount at hZ; omega)
    intro v hv
    have : v ∈ fiber P Z := by simp [fiber, hv]
    rw [← heq] at this
    exact (mem_filter.1 (mem_filter.1 this).1).2
  obtain ⟨x, y, w, hxy, hxw, hyw, hF⟩ := card_eq_three.1 (card_fiber hV hPb Z)
  have hmem : ∀ v, v ∈ fiber P Z ↔ P v = Z := fun v => by simp [fiber]
  have hx : P x = Z := (hmem x).1 (by rw [hF]; simp)
  have hy : P y = Z := (hmem y).1 (by rw [hF]; simp)
  have hw : P w = Z := (hmem w).1 (by rw [hF]; simp)
  -- `Z` is neither the cluster of `a` nor that of `b`
  have hZa : P a ≠ Z := by
    intro h
    have : a ∈ ({x, y, w} : Finset V) := by rw [← hF, hmem]; exact h
    simp only [mem_insert, mem_singleton] at this
    rcases this with rfl | rfl | rfl
    · exact hX ⟨hb, y, hy.trans h.symm, hxy.symm, hZall y hy⟩
    · exact hX ⟨hb, x, hx.trans h.symm, hxy, hZall x hx⟩
    · exact hX ⟨hb, x, hx.trans h.symm, hxw, hZall x hx⟩
  have hZb : P b ≠ Z := by
    intro h
    have : b ∈ ({x, y, w} : Finset V) := by rw [← hF, hmem]; exact h
    simp only [mem_insert, mem_singleton] at this
    rcases this with rfl | rfl | rfl
    · exact hY ⟨ha, y, hy.trans h.symm, hxy.symm, hZall y hy⟩
    · exact hY ⟨ha, x, hx.trans h.symm, hxy, hZall x hx⟩
    · exact hY ⟨ha, x, hx.trans h.symm, hxw, hZall x hx⟩
  have hxa : x ≠ a := fun h => hZa (h ▸ hx)
  have hya : y ≠ a := fun h => hZa (h ▸ hy)
  have hxb : x ≠ b := fun h => hZb (h ▸ hx)
  have hyb : y ≠ b := fun h => hZb (h ▸ hy)
  set τ : Equiv.Perm V := Equiv.swap a x * Equiv.swap b y
  have hfix : ∀ v ∉ ({a, b, x, y} : Finset V), τ v = v := by
    intro v hv
    simp only [mem_insert, mem_singleton, not_or] at hv
    simp only [τ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hv.2.1 hv.2.2.2, Equiv.swap_apply_of_ne_of_ne hv.1 hv.2.2.1]
  have hτa : τ a = x := by
    simp only [τ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hne hya.symm, Equiv.swap_apply_left]
  have hτb : τ b = y := by
    simp only [τ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hya hxy.symm]
  refine ⟨fun v => P (τ v), perm_balanced hPb τ,
    perm_respects hP (S := {a, b, x, y}) ?_ hfix, ?_, (perm_dist P hfix).trans card_le_four⟩
  · intro s hs
    simp only [mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl
    exacts [ha, hb, hZall _ hx, hZall _ hy]
  · simp only [hτa, hτb, hx, hy]

/-- Lemma 3.1 for ALG3's choice: the component-respecting configuration *closest* to `P` after
the merge is at distance at most `4` from `P`. -/
theorem lemma_3_1_closest (hV : Fintype.card V = ℓ * 3) {P : Config V ℓ} (hPb : Balanced 3 P)
    (hP : Respects comp P) {a b : V} (hab : P a ≠ P b) {Q : Config V ℓ}
    (hQ : Balanced 3 Q ∧ Respects comp Q ∧ Q a = Q b)
    (hmin : ∀ Q' : Config V ℓ, Balanced 3 Q' ∧ Respects comp Q' ∧ Q' a = Q' b →
      dist P Q ≤ dist P Q') :
    dist P Q ≤ 4 := by
  obtain ⟨Q', h1, h2, h3, h4⟩ := lemma_3_1 hV hPb hP hab ⟨Q, hQ⟩
  exact (hmin Q' ⟨h1, h2, h3⟩).trans h4

end Papers.PODC2020.DynamicPartitioningLB.K3
