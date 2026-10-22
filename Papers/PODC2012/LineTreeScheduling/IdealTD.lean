import Papers.PODC2012.LineTreeScheduling.TreeDecomp

/-!
# The ideal tree decomposition (Section 4.3): Lemmas 4.1 and 4.3

Chakaravarthy, Roy, Sabharwal, *Distributed algorithms for scheduling on line and tree networks*,
PODC 2012 (arXiv:1205.1924v2).

* `comp T C r x` — the component of `C \ {r}` containing `x` (for convex `C`: the vertices `y ∈ C`
  such that the path from `x` to `y` avoids `r`); convexity, neighbourhoods.
* `exists_balancer` — every nonempty convex set has a balancer (centroid).
* `IdealTD.Good T C ρ sub h` — the output of `BuildIdealTD` on the component `C`: a rooted tree on `C`
  with root `ρ`, given by the sets `sub x = C(x)`, all convex, every tree edge inside `C` joining an
  ancestor–descendant pair, pivot size `≤ 2`, depth `≤ h`.
* `IdealTD.good_glue` — making `r` the root above the trees of the components of `C \ {r}`.
* `IdealTD.exists_good` — `BuildIdealTD`: for a nonempty convex `C` with `|Γ[C]| ≤ 2` there is such a
  tree of depth `≤ 2⌊log₂ |C|⌋ + 1` (Cases 1, 2(a), 2(b) with the junction).
* `lemma_4_1` — Lemma 4.1: the ideal tree decomposition (pivot size 2, depth `≤ 2⌊log₂ n⌋ + 1`).
* `lemma_4_3` — Lemma 4.3: a layered decomposition with `Δ = 6` and length `≤ 2⌊log₂ n⌋ + 1`.
-/

set_option linter.unusedSectionVars false

namespace Podc.LineTreeScheduling

open SimpleGraph Finset TreeAA

variable {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V}

/-! ### Components of `C \ {r}` (CSLib candidate) -/

section Comp

-- CSLib candidate (with the lemmas of this section)
variable (T) in
/-- The component of `C \ {r}` containing `x`: the vertices `y ∈ C` such that `r` does not lie on the
path from `x` to `y` (for convex `C`, the path stays in `C`). Empty if `x = r`. -/
noncomputable def comp (C : Finset V) (r x : V) : Finset V := by
  classical exact C.filter fun y => ¬ Btw T x r y

variable {C C' : Finset V} {r x y u : V}

lemma mem_comp : y ∈ comp T C r x ↔ y ∈ C ∧ ¬ Btw T x r y := by
  unfold comp; simp

lemma comp_subset : comp T C r x ⊆ C := fun _ h => (mem_comp.1 h).1

lemma root_not_mem_comp : r ∉ comp T C r x := fun h => (mem_comp.1 h).2 (btw_right x r)

lemma comp_mono (h : C ⊆ C') : comp T C r x ⊆ comp T C' r x := fun _ hy =>
  mem_comp.2 ⟨h (mem_comp.1 hy).1, (mem_comp.1 hy).2⟩

lemma btw_of_not_mem_comp (hy : y ∈ C) (h : y ∉ comp T C r x) : Btw T x r y := by
  by_contra h'; exact h (mem_comp.2 ⟨hy, h'⟩)

variable (hT : T.IsTree)
include hT

lemma mem_comp_self (hx : x ∈ C) (hxr : x ≠ r) : x ∈ comp T C r x :=
  mem_comp.2 ⟨hx, fun h => hxr (eq_of_btw_self hT h).symm⟩

lemma comp_eq (hy : y ∈ comp T C r x) : comp T C r y = comp T C r x := by
  have hxy := (mem_comp.1 hy).2
  ext w
  simp only [mem_comp, and_congr_right_iff]
  intro _
  constructor
  · intro h h'
    rcases btw_or hT h' y with h'' | h''
    · exact hxy h''
    · exact h h''
  · intro h h'
    rcases btw_or hT h' x with h'' | h''
    · exact hxy h''.symm
    · exact h h''

lemma mem_comp_of_adj (hy : y ∈ C) (hxr : x ≠ r) (hyr : y ≠ r) (hxy : T.Adj x y) :
    y ∈ comp T C r x := by
  refine mem_comp.2 ⟨hy, fun h => ?_⟩
  unfold TreeAA.Btw at h
  rw [dist_eq_one_iff_adj.2 hxy] at h
  rcases Nat.eq_zero_or_pos (T.dist x r) with h0 | h0
  · exact hxr ((hT.connected.dist_eq_zero_iff).1 h0)
  · exact hyr ((hT.connected.dist_eq_zero_iff).1 (by omega : T.dist r y = 0)).symm

lemma convex_comp (hC : TreeAA.Convex (T := T) (C : Set V)) :
    TreeAA.Convex (T := T) (comp T C r x : Set V) := by
  intro y hy w hw v hv
  simp only [mem_coe] at hy hw ⊢
  refine mem_comp.2 ⟨hC y (comp_subset hy) w (comp_subset hw) v hv, fun h => ?_⟩
  have hw' : w ∈ comp T C r y := (comp_eq hT hy).symm ▸ hw
  rcases btw_or hT h y with h' | h'
  · exact (mem_comp.1 hy).2 h'
  · exact (mem_comp.1 hw').2 (hv.trans hT.connected h')

lemma mem_nbhd_comp (hu : u ∈ nbhd T (comp T C r x)) :
    u = r ∨ (u ∈ nbhd T C ∧ ∃ y ∈ comp T C r x, T.Adj y u) := by
  obtain ⟨hu, y, hy, hyu⟩ := mem_nbhd.1 hu
  by_cases huC : u ∈ C
  · left
    have h := btw_of_not_mem_comp huC hu
    rcases btw_or hT h y with h' | h'
    · exact absurd h' (mem_comp.1 hy).2
    · unfold TreeAA.Btw at h'
      rw [dist_eq_one_iff_adj.2 hyu] at h'
      rcases Nat.eq_zero_or_pos (T.dist y r) with h0 | h0
      · exact absurd ((hT.connected.dist_eq_zero_iff).1 h0 ▸ hy) root_not_mem_comp
      · exact ((hT.connected.dist_eq_zero_iff).1 (by omega : T.dist r u = 0)).symm
  · exact Or.inr ⟨mem_nbhd.2 ⟨huC, y, comp_subset hy, hyu⟩, y, hy, hyu⟩

open Classical in
/-- The neighbourhood of a component of `C \ {r}` consists of `r` and the neighbours of `C` adjacent
to the component. -/
lemma nbhd_comp_subset :
    nbhd T (comp T C r x) ⊆ insert r ((nbhd T C).filter fun u => ∃ y ∈ comp T C r x, T.Adj y u) := by
  intro u hu
  rcases mem_nbhd_comp hT hu with h | ⟨h1, h2⟩
  · simp [h]
  · exact mem_insert_of_mem (mem_filter.2 ⟨h1, h2⟩)

-- CSLib candidate
/-- **Balancers exist**: every nonempty convex vertex set `C` of a tree has a vertex `z` (a centroid)
splitting `C` into components of size at most `⌊|C|/2⌋`. We take `z` minimizing `∑_{y ∈ C} d(z, y)`. -/
lemma exists_balancer (hC : TreeAA.Convex (T := T) (C : Set V)) (hne : C.Nonempty) :
    ∃ z ∈ C, ∀ x ∈ C, x ≠ z → 2 * (comp T C z x).card ≤ C.card := by
  classical
  obtain ⟨z, hz, hmin⟩ := C.exists_min_image (fun z => ∑ y ∈ C, T.dist z y) hne
  refine ⟨z, hz, fun x hx hxz => ?_⟩
  obtain ⟨z', hzz', hz'x⟩ := exists_succ hT (Ne.symm hxz)
  have hz'C : z' ∈ C := hC z hz x hx z' hz'x
  set D := comp T C z x
  -- membership in `D` is decided by which side of the edge `zz'` a vertex lies on
  have hz'D : z' ∈ D := by
    refine mem_comp.2 ⟨hz'C, fun h => ?_⟩
    have := eq_of_btw_btw hT h hz'x.symm
    exact hzz'.ne this
  have hD : D = comp T C z z' := (comp_eq hT hz'D).symm
  have hside : ∀ y ∈ C, (y ∈ D ↔ Btw T z z' y) := by
    intro y hy
    rw [hD, mem_comp]
    simp only [hy, true_and]
    rcases btw_or_of_adj hT hzz' y with h | h
    · exact ⟨fun h' => absurd h.symm h', fun h' => absurd h'.symm (not_btw_of_adj hzz' h)⟩
    · exact ⟨fun _ => h.symm, fun _ h' => not_btw_of_adj hzz'.symm h h'.symm⟩
  have hpt : ∀ y ∈ C, T.dist z' y + (if y ∈ D then 1 else 0) =
      T.dist z y + (if y ∉ D then 1 else 0) := by
    intro y hy
    by_cases hyD : y ∈ D
    · have h := (hside y hy).1 hyD
      unfold TreeAA.Btw at h
      rw [dist_eq_one_iff_adj.2 hzz'] at h
      simp only [hyD, ite_true, not_true_eq_false, ite_false]
      omega
    · have h : Btw T z' z y := by
        rcases btw_or_of_adj hT hzz' y with h | h
        · exact h.symm
        · exact absurd ((hside y hy).2 h.symm) hyD
      unfold TreeAA.Btw at h
      rw [dist_eq_one_iff_adj.2 hzz'.symm] at h
      simp only [hyD, ite_false, not_false_eq_true, ite_true]
      omega
  have hsum := sum_congr rfl hpt
  rw [sum_add_distrib, sum_add_distrib, ← card_filter, ← card_filter] at hsum
  have h1 : C.filter (· ∈ D) = D := by
    ext y; simp only [mem_filter, and_iff_right_iff_imp]; exact fun h => comp_subset h
  have h2 := card_filter_add_card_filter_not (s := C) (· ∈ D)
  rw [h1] at hsum h2
  have := hmin z' hz'C
  omega

end Comp

/-! ### `BuildIdealTD` -/

namespace IdealTD

/-- The output of `BuildIdealTD` on the component `C` (Section 4.3): a rooted tree on `C` with root
`ρ`, given by the sets `sub x = C(x)` (`x` and its descendants), such that every `C(x)` is convex,
every edge of `T` inside `C` joins an ancestor–descendant pair, every pivot set `Γ[C(x)]` has at most
two elements, and every node has depth at most `h`. -/
structure Good (T : SimpleGraph V) (C : Finset V) (ρ : V) (sub : V → Finset V) (h : ℕ) : Prop where
  root_mem : ρ ∈ C
  sub_root : sub ρ = C
  mem_self : ∀ x ∈ C, x ∈ sub x
  sub_subset : ∀ x ∈ C, sub x ⊆ C
  sub_mono : ∀ x ∈ C, ∀ y ∈ C, x ∈ sub y → sub x ⊆ sub y
  antisymm : ∀ x ∈ C, ∀ y ∈ C, x ∈ sub y → y ∈ sub x → x = y
  chain : ∀ x ∈ C, ∀ y ∈ C, ∀ w, w ∈ sub x → w ∈ sub y → x ∈ sub y ∨ y ∈ sub x
  convex : ∀ x ∈ C, TreeAA.Convex (T := T) (sub x : Set V)
  adj : ∀ x ∈ C, ∀ y ∈ C, T.Adj x y → x ∈ sub y ∨ y ∈ sub x
  pivot : ∀ x ∈ C, (nbhd T (sub x)).card ≤ 2
  depth : ∀ w ∈ C, (C.filter fun x => w ∈ sub x).card ≤ h

lemma Good.mono {C : Finset V} {ρ : V} {sub : V → Finset V} {h h' : ℕ} (G : Good T C ρ sub h)
    (hh : h ≤ h') : Good T C ρ sub h' :=
  { G with depth := fun w hw => (G.depth w hw).trans hh }

lemma log_bound {m c : ℕ} (hm : 1 ≤ m) (hmc : 2 * m ≤ c) :
    2 * Nat.log 2 m + 1 ≤ 2 * Nat.log 2 c - 1 := by
  have h1 : Nat.log 2 (m * 2) = Nat.log 2 m + 1 := Nat.log_mul_base (by norm_num) (by omega)
  have h2 : Nat.log 2 (m * 2) ≤ Nat.log 2 c := Nat.log_mono_right (by omega)
  omega

variable (hT : T.IsTree)
include hT

/-- **Gluing**: given trees for all components of `C \ {r}`, making `r` the root above their roots
gives a tree for `C` (one level deeper). -/
theorem good_glue {C : Finset V} {r : V} (hr : r ∈ C) (hC : TreeAA.Convex (T := T) (C : Set V))
    (hΓ : (nbhd T C).card ≤ 2) {h : ℕ}
    (hp : ∀ x ∈ C, x ≠ r → ∃ ρ sub, Good T (comp T C r x) ρ sub h) :
    ∃ sub, Good T C r sub (h + 1) := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : V → Finset V, K = fun x => comp T C r x := ⟨_, rfl⟩
  have hp' : ∀ x ∈ C, x ≠ r → ∃ ρ sub, Good T (K x) ρ sub h := by subst hK; exact hp
  let F : Finset V → V → Finset V := fun D =>
    if hD : ∃ ρ sub, Good T D ρ sub h then hD.choose_spec.choose else fun _ => ∅
  have hF : ∀ x ∈ C, x ≠ r → ∃ ρ, Good T (K x) ρ (F (K x)) h := by
    intro x hx hxr
    have hD := hp' x hx hxr
    refine ⟨hD.choose, ?_⟩
    simp only [F, hD, ↓reduceDIte]
    exact hD.choose_spec.choose_spec
  let sub : V → Finset V := fun x => if x = r then C else F (K x) x
  have sub_r : sub r = C := by simp [sub]
  have sub_ne : ∀ x, x ≠ r → sub x = F (K x) x := fun x hx => by simp [sub, hx]
  have hKx : ∀ x ∈ C, x ≠ r → x ∈ K x := fun x hx hxr => by
    subst hK; exact mem_comp_self hT hx hxr
  have hKeq : ∀ x y, y ∈ K x → K y = K x := fun x y hy => by subst hK; exact comp_eq hT hy
  have hrK : ∀ x, r ∉ K x := fun x => by subst hK; exact root_not_mem_comp
  have hKC : ∀ x, K x ⊆ C := fun x => by subst hK; exact comp_subset
  -- `sub x ⊆ K x` for `x ≠ r`
  have hsubK : ∀ x ∈ C, x ≠ r → sub x ⊆ K x := by
    intro x hx hxr
    obtain ⟨ρ, G⟩ := hF x hx hxr
    rw [sub_ne x hxr]; exact G.sub_subset x (hKx x hx hxr)
  have hsubC : ∀ x ∈ C, sub x ⊆ C := by
    intro x hx
    by_cases hxr : x = r
    · rw [hxr, sub_r]
    · exact (hsubK x hx hxr).trans (hKC x)
  -- if `y ∈ K x` then the two pieces carry the same tree
  have hFeq : ∀ x y, y ∈ K x → F (K y) = F (K x) := fun x y hy => by rw [hKeq x y hy]
  refine ⟨sub, ⟨hr, sub_r, ?_, hsubC, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- mem_self
    intro x hx
    by_cases hxr : x = r
    · rw [hxr, sub_r]; exact hr
    · obtain ⟨ρ, G⟩ := hF x hx hxr
      rw [sub_ne x hxr]; exact G.mem_self x (hKx x hx hxr)
  · -- sub_mono
    intro x hx y hy hxy
    by_cases hyr : y = r
    · rw [hyr, sub_r]; exact hsubC x hx
    · have hxK : x ∈ K y := hsubK y hy hyr hxy
      have hxr : x ≠ r := fun h => hrK y (h ▸ hxK)
      obtain ⟨ρ, G⟩ := hF y hy hyr
      rw [sub_ne y hyr] at hxy ⊢
      rw [sub_ne x hxr, hFeq y x hxK]
      exact G.sub_mono x hxK y (hKx y hy hyr) hxy
  · -- antisymm
    intro x hx y hy hxy hyx
    by_cases hxr : x = r
    · by_cases hyr : y = r
      · rw [hxr, hyr]
      · exact absurd (hxr ▸ hsubK y hy hyr hxy) (hrK y)
    · by_cases hyr : y = r
      · exact absurd (hyr ▸ hsubK x hx hxr hyx) (hrK x)
      · have hxK : x ∈ K y := hsubK y hy hyr hxy
        obtain ⟨ρ, G⟩ := hF y hy hyr
        rw [sub_ne y hyr] at hxy
        rw [sub_ne x hxr, hFeq y x hxK] at hyx
        exact G.antisymm x hxK y (hKx y hy hyr) hxy hyx
  · -- chain
    intro x hx y hy w hwx hwy
    by_cases hxr : x = r
    · right; rw [hxr, sub_r]; exact hy
    · by_cases hyr : y = r
      · left; rw [hyr, sub_r]; exact hx
      · have hwK : w ∈ K x := hsubK x hx hxr hwx
        have hwK' : w ∈ K y := hsubK y hy hyr hwy
        have hKK : K x = K y := (hKeq x w hwK).symm.trans (hKeq y w hwK')
        have hxK : x ∈ K y := hKK ▸ hKx x hx hxr
        obtain ⟨ρ, G⟩ := hF y hy hyr
        rw [sub_ne x hxr, sub_ne y hyr, hFeq y x hxK] at *
        exact G.chain x hxK y (hKx y hy hyr) w hwx hwy
  · -- convex
    intro x hx
    by_cases hxr : x = r
    · rw [hxr, sub_r]; exact hC
    · obtain ⟨ρ, G⟩ := hF x hx hxr
      rw [sub_ne x hxr]; exact G.convex x (hKx x hx hxr)
  · -- adj
    intro x hx y hy hxy
    by_cases hxr : x = r
    · right; rw [hxr, sub_r]; exact hy
    · by_cases hyr : y = r
      · left; rw [hyr, sub_r]; exact hx
      · have hyK : y ∈ K x := by subst hK; exact mem_comp_of_adj hT hy hxr hyr hxy
        obtain ⟨ρ, G⟩ := hF x hx hxr
        rw [sub_ne x hxr, sub_ne y hyr, hFeq x y hyK]
        exact G.adj x (hKx x hx hxr) y hyK hxy
  · -- pivot
    intro x hx
    by_cases hxr : x = r
    · rw [hxr, sub_r]; exact hΓ
    · obtain ⟨ρ, G⟩ := hF x hx hxr
      rw [sub_ne x hxr]; exact G.pivot x (hKx x hx hxr)
  · -- depth
    intro w hw
    by_cases hwr : w = r
    · have : C.filter (fun x => w ∈ sub x) ⊆ {r} := by
        intro x hx'
        rw [mem_filter] at hx'
        rw [mem_singleton]
        by_contra hxr
        exact hrK x (hwr ▸ hsubK x hx'.1 hxr hx'.2)
      have := card_le_card this
      simp at this; omega
    · obtain ⟨ρ, G⟩ := hF w hw hwr
      have : C.filter (fun x => w ∈ sub x) ⊆
          insert r ((K w).filter fun x => w ∈ F (K w) x) := by
        intro x hx'
        rw [mem_filter] at hx'
        by_cases hxr : x = r
        · rw [hxr]; exact mem_insert_self _ _
        · have hwK : w ∈ K x := hsubK x hx'.1 hxr hx'.2
          have hKK : K w = K x := hKeq x w hwK
          refine mem_insert_of_mem (mem_filter.2 ⟨hKK ▸ hKx x hx'.1 hxr, ?_⟩)
          rw [hKK]; have := hx'.2; rwa [sub_ne x hxr] at this
      have h1 := (card_le_card this).trans (card_insert_le _ _)
      have h2 := G.depth w (hKx w hw hwr)
      omega


/-- **`BuildIdealTD`** (Section 4.3). For every nonempty convex `C` with at most two neighbours there
is a rooted tree on `C` with pivot size `≤ 2` and depth `≤ 2⌊log₂ |C|⌋ + 1`. Construction: take a
balancer `z` of `C`. If no component of `C \ {z}` is adjacent to both neighbours of `C` (Cases 1 and
2(a), and the degenerate case where a neighbour of `C` is attached to `z` itself), make `z` the root
above the recursively built trees of the components of `C \ {z}`. Otherwise (Case 2(b)) both
neighbours `u₁, u₂` of `C` are attached (at `y₁`, `y₂`) to one component; let `j` be the junction
(the median of `y₁, y₂, z`); make `j` the root above the trees of the components of `C \ {j}`, where
the component `K` containing `z` gets `z` as its root above the trees of the components of
`K \ {z}`. -/
theorem exists_good : ∀ (c : ℕ) (C : Finset V), C.card = c → C.Nonempty →
    TreeAA.Convex (T := T) (C : Set V) → (nbhd T C).card ≤ 2 →
    ∃ ρ sub, Good T C ρ sub (2 * Nat.log 2 c + 1) := by
  classical
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro C hc hne hC hΓ
  obtain ⟨z, hz, hbal⟩ := exists_balancer hT hC hne
  -- the recursive calls, on sets of size at most `⌊c/2⌋`
  have IH : ∀ E : Finset V, E.Nonempty → TreeAA.Convex (T := T) (E : Set V) →
      (nbhd T E).card ≤ 2 → 2 * E.card ≤ C.card →
      ∃ ρ sub, Good T E ρ sub (2 * Nat.log 2 c - 1) := by
    intro E hEne hE hEΓ hEc
    rw [hc] at hEc
    have hE1 : 1 ≤ E.card := card_pos.2 hEne
    obtain ⟨ρ, sub, G⟩ := ih E.card (by omega) E rfl hEne hE hEΓ
    exact ⟨ρ, sub, G.mono (log_bound hE1 hEc)⟩
  by_cases hB : ∃ x ∈ C, x ≠ z ∧ ∃ u₁ ∈ nbhd T C, ∃ u₂ ∈ nbhd T C, u₁ ≠ u₂ ∧
      (∃ y ∈ comp T C z x, T.Adj y u₁) ∧ (∃ y ∈ comp T C z x, T.Adj y u₂)
  swap
  · -- Cases 1 and 2(a): the balancer `z` is the root.
    push Not at hB
    obtain ⟨sub, G⟩ := good_glue hT hz hC hΓ (h := 2 * Nat.log 2 c - 1) fun x hx hxz => by
      refine IH _ ⟨x, mem_comp_self hT hx hxz⟩ (convex_comp hT hC) ?_ (hbal x hx hxz)
      refine (card_le_card (nbhd_comp_subset hT)).trans ((card_insert_le _ _).trans ?_)
      have : ((nbhd T C).filter fun u => ∃ y ∈ comp T C z x, T.Adj y u).card ≤ 1 := by
        refine card_le_one.2 fun u₁ hu₁ u₂ hu₂ => ?_
        rw [mem_filter] at hu₁ hu₂
        by_contra hne
        obtain ⟨y₂, hy₂, hyu₂⟩ := hu₂.2
        exact hB x hx hxz u₁ hu₁.1 u₂ hu₂.1 hne hu₁.2 y₂ hy₂ hyu₂
      omega
    exact ⟨z, sub, G.mono (by omega)⟩
  -- Case 2(b): both neighbours of `C` are attached to the same component `D` of `C \ {z}`.
  obtain ⟨x₀, hx₀, hx₀z, u₁, hu₁, u₂, hu₂, hne, ⟨y₁, hy₁, hyu₁⟩, ⟨y₂, hy₂, hyu₂⟩⟩ := hB
  set D := comp T C z x₀ with hDdef
  have hc2 : 2 ≤ c := hc ▸ one_lt_card.2 ⟨z, hz, x₀, hx₀, hx₀z.symm⟩
  have hlog : 1 ≤ Nat.log 2 c := Nat.log_pos (by norm_num) hc2
  have hΓC : ∀ u ∈ nbhd T C, u = u₁ ∨ u = u₂ := by
    intro u hu
    by_contra h
    push Not at h
    have : ({u, u₁, u₂} : Finset V) ⊆ nbhd T C := by
      intro v hv; simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    have h3 := card_le_card this
    rw [card_insert_of_notMem (by simp [h.1, h.2]), card_pair hne] at h3
    omega
  have hy₁C : y₁ ∈ C := comp_subset hy₁
  have hy₂C : y₂ ∈ C := comp_subset hy₂
  have hu₁C : u₁ ∉ C := (mem_nbhd.1 hu₁).1
  have hu₂C : u₂ ∉ C := (mem_nbhd.1 hu₂).1
  -- the junction
  obtain ⟨j, hj12, hj1z, hj2z⟩ := exists_median hT y₁ y₂ z
  have hjC : j ∈ C := hC y₁ hy₁C y₂ hy₂C j hj12
  have hD1 : comp T C z y₁ = D := comp_eq hT hy₁
  have hy₂' : y₂ ∈ comp T C z y₁ := hD1 ▸ hy₂
  have hjz : j ≠ z := by rintro rfl; exact (mem_comp.1 hy₂').2 hj12
  -- the component `K` of `C \ {j}` containing `z`
  set K := comp T C j z with hKdef
  have hzK : z ∈ K := mem_comp_self hT hz hjz.symm
  have hKC : K ⊆ C := comp_subset
  have hKconv : TreeAA.Convex (T := T) (K : Set V) := convex_comp hT hC
  have hKΓ : nbhd T K ⊆ {j} := by
    intro u hu
    rcases mem_nbhd_comp hT hu with h | ⟨huC, y, hyK, hyu⟩
    · simp [h]
    · exfalso
      rcases hΓC u huC with rfl | rfl
      · have := eq_of_adj_of_adj hT hC hu₁C (hKC hyK) hy₁C hyu.symm hyu₁.symm
        subst this
        exact (mem_comp.1 hyK).2 hj1z.symm
      · have := eq_of_adj_of_adj hT hC hu₂C (hKC hyK) hy₂C hyu.symm hyu₂.symm
        subst this
        exact (mem_comp.1 hyK).2 hj2z.symm
  have hKΓ' : (nbhd T K).card ≤ 1 := (card_le_card hKΓ).trans (by simp)
  -- the tree on `K`, with root `z`
  obtain ⟨subK, GK⟩ := good_glue hT hzK hKconv (by omega) (h := 2 * Nat.log 2 c - 1)
    fun x hx hxz => by
      refine IH _ ⟨x, mem_comp_self hT hx hxz⟩ (convex_comp hT hKconv) ?_ ?_
      · have h1 : nbhd T (comp T K z x) ⊆ insert z (nbhd T K) := by
          intro u hu
          rcases mem_nbhd_comp hT hu with h | ⟨h, -⟩
          · simp [h]
          · exact mem_insert_of_mem h
        exact (card_le_card h1).trans ((card_insert_le _ _).trans (by omega))
      · have := card_le_card (comp_mono (T := T) (r := z) (x := x) hKC)
        have := hbal x (hKC hx) hxz
        omega
  -- the tree on `C`, with root `j`
  obtain ⟨sub, G⟩ := good_glue hT hjC hC hΓ (h := 2 * Nat.log 2 c - 1 + 1) fun x hx hxj => by
    by_cases hzx : z ∈ comp T C j x
    · rw [← comp_eq hT hzx]; exact ⟨z, subK, GK⟩
    · set E := comp T C j x with hEdef
      -- `E` lies inside `D`
      have hED : E ⊆ D := by
        intro y hy
        have hyC : y ∈ C := comp_subset hy
        have hEy : comp T C j y = E := comp_eq hT hy
        have hyjz : Btw T y j z := btw_of_not_mem_comp hz (hEy ▸ hzx)
        have hjD : j ∈ comp T C z y₁ := by
          refine mem_comp.2 ⟨hjC, fun h => hjz ?_⟩
          exact (eq_of_btw_btw hT hj1z h)
        have hyj : y ∈ comp T C z j := by
          refine mem_comp.2 ⟨hyC, fun h => hjz ?_⟩
          have hG := hT.connected
          unfold TreeAA.Btw at h hyjz
          have c1 := dist_comm (G := T) (u := y) (v := j)
          have c2 := dist_comm (G := T) (u := y) (v := z)
          exact (hG.dist_eq_zero_iff).1 (by omega)
        rw [← hD1, ← comp_eq hT hjD]; exact hyj
      have hnot : ¬ ((∃ y ∈ E, T.Adj y u₁) ∧ (∃ y ∈ E, T.Adj y u₂)) := by
        rintro ⟨⟨v₁, hv₁, hvu₁⟩, ⟨v₂, hv₂, hvu₂⟩⟩
        have e1 := eq_of_adj_of_adj hT hC hu₁C (comp_subset hv₁) hy₁C hvu₁.symm hyu₁.symm
        have e2 := eq_of_adj_of_adj hT hC hu₂C (comp_subset hv₂) hy₂C hvu₂.symm hyu₂.symm
        subst e1 e2
        have : v₂ ∈ comp T C j v₁ := (comp_eq hT hv₁).symm ▸ hv₂
        exact (mem_comp.1 this).2 hj12
      have hEc : 2 * E.card ≤ C.card := by
        have := card_le_card hED
        have := hbal x₀ hx₀ hx₀z
        rw [← hDdef] at this
        omega
      have hEΓ : (nbhd T E).card ≤ 2 := by
        refine (card_le_card (nbhd_comp_subset hT)).trans ((card_insert_le _ _).trans ?_)
        have : ((nbhd T C).filter fun u => ∃ y ∈ comp T C j x, T.Adj y u).card ≤ 1 := by
          refine card_le_one.2 fun v hv v' hv' => ?_
          rw [mem_filter] at hv hv'
          rcases hΓC v hv.1 with rfl | rfl <;> rcases hΓC v' hv'.1 with rfl | rfl
          · rfl
          · exact absurd ⟨hv.2, hv'.2⟩ hnot
          · exact absurd ⟨hv'.2, hv.2⟩ hnot
          · rfl
        omega
      obtain ⟨ρ, s, G'⟩ := IH E ⟨x, mem_comp_self hT hx hxj⟩ (convex_comp hT hC) hEΓ hEc
      exact ⟨ρ, s, G'.mono (by omega)⟩
  exact ⟨j, sub, G.mono (by omega)⟩

end IdealTD

/-! ### Lemmas 4.1 and 4.3 -/

/-- The rooted tree on `V` produced by `BuildIdealTD` on `C = V`. -/
noncomputable def IdealTD.Good.toRootedTree {g : V} {sub : V → Finset V} {h : ℕ}
    (G : IdealTD.Good T univ g sub h) : RootedTree V where
  root := g
  sub := sub
  mem_sub_self z := G.mem_self z (mem_univ _)
  mem_sub_root x := by rw [G.sub_root]; exact mem_univ x
  sub_subset_sub {x y} hxy := G.sub_mono x (mem_univ _) y (mem_univ _) hxy
  eq_of_mem_sub {x y} hxy hyx := G.antisymm x (mem_univ _) y (mem_univ _) hxy hyx
  mem_sub_or {x y w} hx hy := G.chain x (mem_univ _) y (mem_univ _) w hx hy

/-- **Lemma 4.1** (ideal tree decomposition). Every tree network `T` on `n ≥ 1` vertices has a tree
decomposition with pivot size `θ = 2` and depth at most `2⌊log₂ n⌋ + 1`. -/
theorem lemma_4_1 (hT : T.IsTree) [Nonempty V] :
    ∃ D : TreeDecomp T, (∀ z, (nbhd T (D.H.sub z)).card ≤ 2) ∧
      ∀ x, D.H.depth x ≤ 2 * Nat.log 2 (Fintype.card V) + 1 := by
  obtain ⟨g, sub, G⟩ := IdealTD.exists_good hT _ univ rfl univ_nonempty
    (fun _ _ _ _ _ _ => mem_coe.2 (mem_univ _)) (by simp [nbhd])
  refine ⟨TreeDecomp.ofAdj hT G.toRootedTree (fun z => G.convex z (mem_univ _))
    (fun x y hxy => G.adj x (mem_univ _) y (mem_univ _) hxy),
    fun z => G.pivot z (mem_univ _), fun x => ?_⟩
  exact (G.depth x (mem_univ _)).trans (by rw [card_univ])

/-- **Lemma 4.3.** Every tree network `T` on `n` vertices has a layered decomposition with critical
set size `Δ = 6` and length `ℓ ≤ 2⌊log₂ n⌋ + 1` (Lemma 4.2 applied to the ideal tree decomposition
of Lemma 4.1). -/
theorem lemma_4_3 (hT : T.IsTree) :
    Nonempty (LayeredDecomp T 6 (2 * Nat.log 2 (Fintype.card V) + 1)) := by
  cases isEmpty_or_nonempty V with
  | inl hV =>
    exact ⟨⟨fun a => isEmptyElim a, fun a => isEmptyElim a, fun a => isEmptyElim a,
      fun a => isEmptyElim a, fun a => isEmptyElim a, fun a => isEmptyElim a⟩⟩
  | inr hV =>
    obtain ⟨D, hθ, hℓ⟩ := lemma_4_1 hT
    obtain ⟨L, -, -⟩ := lemma_4_2 hT D hθ hℓ
    exact ⟨L⟩

end Podc.LineTreeScheduling
