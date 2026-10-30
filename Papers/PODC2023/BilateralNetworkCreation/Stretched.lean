import Papers.PODC2023.BilateralNetworkCreation.TreeMetric

/-!
# The `k`-stretched complete binary tree

Section "parent-function graphs": a graph given by a parent function `par` with root `r`
(`par r = r`) and a height `h` decreasing by one along `par` is a tree, the height is the distance
from the root, and the metric subtree `sub G r u` of `TreeMetric.lean` is `{u}` plus the disjoint
union of the subtrees of the children of `u`.

Section "stretched tree": the `k`-stretched complete binary tree of depth `d` in a layered
encoding, its subtree sizes `sF d k ℓ` (depending only on the layer `ℓ`), its size, and Lemma D.1
of the paper (average layer).
-/

namespace Podc.BilateralNetworkCreation

open SimpleGraph Finset

/-! ### Parent-function graphs -/

section ParentGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph of a parent function: `x ~ y` iff `x ≠ y` and one is the parent of the other. -/
-- CSLib candidate: parent-function trees (`parGraph`, `IsParFun`)
def parGraph (par : V → V) : SimpleGraph V := SimpleGraph.fromRel fun x y => par x = y

omit [Fintype V] [DecidableEq V] in
lemma parGraph_adj {par : V → V} {x y : V} :
    (parGraph par).Adj x y ↔ x ≠ y ∧ (par x = y ∨ par y = x) := by
  simp [parGraph]

/-- `par` is a parent function with root `r` and height `h`. -/
structure IsParFun (par : V → V) (r : V) (h : V → ℕ) : Prop where
  par_root : par r = r
  h_root : h r = 0
  h_par : ∀ x, x ≠ r → h (par x) + 1 = h x

variable {par : V → V} {r : V} {h : V → ℕ} (hP : IsParFun par r h)
include hP

namespace IsParFun

omit [Fintype V] [DecidableEq V] in
lemma par_ne {x : V} (hx : x ≠ r) : par x ≠ x := by
  intro he
  have := hP.h_par x hx
  rw [he] at this
  omega

omit [Fintype V] [DecidableEq V] in
lemma adj_par {x : V} (hx : x ≠ r) : (parGraph par).Adj x (par x) :=
  parGraph_adj.2 ⟨(hP.par_ne hx).symm, Or.inl rfl⟩

omit [Fintype V] [DecidableEq V] in
lemma h_le_of_adj {x y : V} (hxy : (parGraph par).Adj x y) : h y ≤ h x + 1 := by
  obtain ⟨hne, hpar | hpar⟩ := parGraph_adj.1 hxy
  · subst hpar
    have hx : x ≠ r := by
      rintro rfl
      exact hne hP.par_root.symm
    have := hP.h_par x hx
    omega
  · subst hpar
    have hy : y ≠ r := by
      rintro rfl
      exact hne hP.par_root
    have := hP.h_par y hy
    omega

omit [Fintype V] [DecidableEq V] in
lemma h_le_walk {u v : V} (p : (parGraph par).Walk u v) : h v ≤ h u + p.length := by
  induction p with
  | nil => simp
  | cons hadj p ih =>
    have := hP.h_le_of_adj hadj
    simp only [Walk.length_cons]
    omega

omit [Fintype V] in
lemma exists_walk (x : V) : ∃ p : (parGraph par).Walk x r, p.length = h x := by
  induction hn : h x generalizing x with
  | zero =>
    by_cases hx : x = r
    · subst hx; exact ⟨Walk.nil, rfl⟩
    · have := hP.h_par x hx; omega
  | succ n ih =>
    have hx : x ≠ r := by
      rintro rfl; rw [hP.h_root] at hn; omega
    have := hP.h_par x hx
    obtain ⟨p, hp⟩ := ih (par x) (by omega)
    exact ⟨Walk.cons (hP.adj_par hx) p, by simp [hp]⟩

omit [Fintype V] in
lemma connected : (parGraph par).Connected := by
  have : Nonempty V := ⟨r⟩
  refine Connected.mk fun x y => ?_
  obtain ⟨p, -⟩ := hP.exists_walk x
  obtain ⟨q, -⟩ := hP.exists_walk y
  exact ⟨p.append q.reverse⟩

omit [Fintype V] in
lemma dist_eq (x : V) : (parGraph par).dist r x = h x := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := hP.exists_walk x
    have := dist_le p.reverse
    simp only [Walk.length_reverse] at this
    omega
  · obtain ⟨p, hp⟩ := hP.connected.exists_walk_length_eq_dist r x
    have := hP.h_le_walk p
    rw [hP.h_root] at this
    omega

lemma card_edgeSet : Nat.card (parGraph par).edgeSet + 1 = Nat.card V := by
  let f : {x : V // x ≠ r} → (parGraph par).edgeSet :=
    fun x => ⟨s(x.1, par x.1), hP.adj_par x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ he
      have he' := congrArg Subtype.val he
      simp only [f, Sym2.eq_iff] at he'
      rcases he' with ⟨rfl, -⟩ | ⟨h1, h2⟩
      · rfl
      · have a1 := hP.h_par x hx
        have a2 := hP.h_par y hy
        rw [h2] at a1
        rw [← h1] at a2
        omega
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ x y =>
      obtain ⟨hne, hpar | hpar⟩ := parGraph_adj.1 he <;> simp only at hne hpar
      · subst hpar
        have hx : x ≠ r := by
          rintro rfl
          exact hne hP.par_root.symm
        exact ⟨⟨x, hx⟩, rfl⟩
      · subst hpar
        have hy : y ≠ r := by
          rintro rfl
          exact hne hP.par_root
        exact ⟨⟨y, hy⟩, by simp [f, Sym2.eq_swap]⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨r⟩
  omega

lemma isTree : (parGraph par).IsTree :=
  isTree_iff_connected_and_card.2 ⟨hP.connected, hP.card_edgeSet⟩

end IsParFun

omit [Fintype V] [DecidableEq V] hP in
lemma IsParFun.isTree' (hP : IsParFun par r h) [Finite V] : (parGraph par).IsTree := by
  classical
  have := Fintype.ofFinite V
  exact hP.isTree

omit hP in
/-- The children of `u`. -/
def children (par : V → V) (u : V) : Finset V := univ.filter fun c => c ≠ u ∧ par c = u

omit hP in
lemma mem_children {u c : V} : c ∈ children par u ↔ c ≠ u ∧ par c = u := by simp [children]

namespace IsParFun

lemma h_child {u c : V} (hc : c ∈ children par u) : h c = h u + 1 := by
  obtain ⟨hcu, hpc⟩ := mem_children.1 hc
  have hcr : c ≠ r := by
    rintro rfl
    exact hcu (hP.par_root ▸ hpc)
  have := hP.h_par c hcr
  rw [hpc] at this
  omega

lemma mem_sub_iff {u x : V} :
    x ∈ sub (parGraph par) r u ↔ x = u ∨ ∃ c ∈ children par u, x ∈ sub (parGraph par) r c := by
  have hG := hP.connected
  have hd := hP.dist_eq
  constructor
  · intro hx
    by_cases hxu : x = u
    · exact Or.inl hxu
    right
    have h0 : (parGraph par).dist u x ≠ 0 := by
      rw [Ne, hG.dist_eq_zero_iff]
      exact Ne.symm hxu
    have hx' := mem_sub.1 hx
    obtain ⟨w, hw, hlw, hxw⟩ := exists_anc hG hx ((parGraph par).dist r u + 1) (by omega)
      (by omega)
    refine ⟨w, mem_children.2 ⟨?_, ?_⟩, hxw⟩
    · rintro rfl; omega
    · have hw' := mem_sub.1 hw
      have h1 : (parGraph par).dist u w = 1 := by omega
      obtain ⟨-, hpar | hpar⟩ := parGraph_adj.1 (dist_eq_one_iff_adj.1 h1)
      · exfalso
        have hur : u ≠ r := by
          rintro rfl
          rw [hP.par_root] at hpar
          subst hpar
          omega
        have := hP.h_par u hur
        rw [hpar] at this
        rw [hd, hd] at hlw
        omega
      · exact hpar
  · rintro (rfl | ⟨c, hc, hx⟩)
    · exact self_mem_sub
    · obtain ⟨hcu, hpc⟩ := mem_children.1 hc
      have hcr : c ≠ r := by
        rintro rfl
        exact hcu (hP.par_root ▸ hpc)
      have hcu' : c ∈ sub (parGraph par) r u := by
        have := hP.adj_par hcr
        rw [hpc] at this
        apply mem_sub_of_adj this
        rw [hd, hd]
        exact hP.h_child hc |>.symm
      exact sub_trans hG hcu' hx

lemma sub_eq (u : V) :
    sub (parGraph par) r u = insert u ((children par u).biUnion (sub (parGraph par) r)) := by
  ext x
  rw [hP.mem_sub_iff, mem_insert, mem_biUnion]

/-- Subtree size recursion: `|T_u| = 1 + ∑_{c child of u} |T_c|`. -/
lemma card_sub (u : V) :
    #(sub (parGraph par) r u) = 1 + ∑ c ∈ children par u, #(sub (parGraph par) r c) := by
  have hT := hP.isTree
  have hd := hP.dist_eq
  rw [hP.sub_eq u, card_insert_of_notMem, card_biUnion, add_comm]
  · intro c1 hc1 c2 hc2 hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx1 hx2
    apply hne
    apply anc_unique hT hx1 hx2
    rw [hd, hd, hP.h_child hc1, hP.h_child hc2]
  · rw [mem_biUnion]
    rintro ⟨c, hc, hu⟩
    have := layer_le_of_mem_sub hu
    rw [hd, hd, hP.h_child hc] at this
    omega

end IsParFun

end ParentGraph

/-! ### The stretched tree -/

section Stretched

/-- `⌈ℓ / k⌉`, the level in the binary tree `B` of the stretched-tree layer `ℓ`. -/
def sEx (k ℓ : ℕ) : ℕ := (ℓ + k - 1) / k

/-- The width `2 ^ ⌈ℓ / k⌉` of layer `ℓ` of the `k`-stretched tree. -/
def sW (k ℓ : ℕ) : ℕ := 2 ^ sEx k ℓ

/-- The ratio `sW k ℓ / sW k (ℓ - 1)` (`2` at the start of a stretched segment, else `1`). -/
def sRat (k ℓ : ℕ) : ℕ := 2 ^ (sEx k ℓ - sEx k (ℓ - 1))

/-- Vertices of the `k`-stretched complete binary tree of depth `d`: pairs (layer `ℓ ≤ d k`,
index `j < 2 ^ ⌈ℓ / k⌉`). -/
abbrev SVert (d k : ℕ) := Σ ℓ : Fin (d * k + 1), Fin (sW k ℓ)

variable {d k : ℕ}

lemma sEx_zero : sEx k 0 = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [sEx]
  · simp only [sEx, zero_add]; exact Nat.div_eq_of_lt (by omega)

lemma sEx_mono : Monotone (sEx k) := fun a b hab => Nat.div_le_div_right (by omega)

lemma sEx_add (hk : 1 ≤ k) (ℓ : ℕ) : sEx k (ℓ + k) = sEx k ℓ + 1 := by
  simp only [sEx]
  rw [show ℓ + k + k - 1 = ℓ + k - 1 + k by omega, Nat.add_div_right _ (by omega)]

lemma sEx_one (hk : 1 ≤ k) : sEx k 1 = 1 := by
  simp only [sEx]
  rw [show 1 + k - 1 = k by omega, Nat.div_self (by omega)]

lemma sW_pos (ℓ : ℕ) : 0 < sW k ℓ := Nat.two_pow_pos _

lemma sRat_pos (ℓ : ℕ) : 0 < sRat k ℓ := Nat.two_pow_pos _

lemma sW_eq (ℓ : ℕ) : sW k ℓ = sRat k ℓ * sW k (ℓ - 1) := by
  simp only [sW, sRat, ← pow_add]
  have := sEx_mono (k := k) (Nat.sub_le ℓ 1)
  congr 1
  omega

lemma sRat_eq (ℓ : ℕ) : sRat k ℓ = sW k ℓ / sW k (ℓ - 1) := by
  rw [sW_eq ℓ, Nat.mul_div_cancel _ (sW_pos _)]

/-- The root `⟨0, 0⟩`. -/
def sRoot : SVert d k := ⟨0, ⟨0, sW_pos _⟩⟩

/-- The parent function: `⟨ℓ, j⟩ ↦ ⟨ℓ - 1, j / (sW ℓ / sW (ℓ - 1))⟩`, and the root is fixed. -/
def sPar (x : SVert d k) : SVert d k :=
  if hx : x.1.val = 0 then sRoot else
    ⟨⟨x.1.val - 1, by omega⟩, ⟨x.2.val / sRat k x.1.val, by
      rw [Nat.div_lt_iff_lt_mul (sRat_pos _)]
      exact lt_of_lt_of_eq x.2.isLt ((sW_eq _).trans (mul_comm _ _))⟩⟩

/-- The `k`-stretched complete binary tree of depth `d`. -/
def stretchedTree (d k : ℕ) : SimpleGraph (SVert d k) := parGraph sPar

lemma SVert.ext_iff' {x y : SVert d k} : x = y ↔ x.1 = y.1 ∧ x.2.val = y.2.val := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, e⟩ := y
  constructor
  · rintro h; cases h; simp
  · rintro ⟨h1, h2⟩
    simp only at h1 h2
    subst h1
    simp [Fin.ext h2]

lemma eq_sRoot_of_fst {x : SVert d k} (hx : x.1.val = 0) : x = sRoot := by
  rw [SVert.ext_iff']
  have h2 : x.2.val < sW k x.1.val := x.2.2
  have h3 : sW k x.1.val = 1 := by simp [sW, hx, sEx_zero]
  exact ⟨Fin.ext hx, by simp [sRoot]; omega⟩

lemma sPar_of_ne {x : SVert d k} (hx : x.1.val ≠ 0) :
    sPar x = ⟨⟨x.1.val - 1, by omega⟩, ⟨x.2.val / sRat k x.1.val, by
      rw [Nat.div_lt_iff_lt_mul (sRat_pos _)]
      exact lt_of_lt_of_eq x.2.isLt ((sW_eq _).trans (mul_comm _ _))⟩⟩ :=
  dite_eq_right hx

lemma sPar_fst {x : SVert d k} (hx : x.1.val ≠ 0) : (sPar x).1.val = x.1.val - 1 := by
  simp [sPar, hx]

lemma sPar_snd {x : SVert d k} (hx : x.1.val ≠ 0) :
    (sPar x).2.val = x.2.val / sRat k x.1.val := by
  rw [sPar_of_ne hx]

lemma isParFun_sPar : IsParFun (sPar (d := d) (k := k)) sRoot (fun x => x.1.val) where
  par_root := by simp [sPar, sRoot]
  h_root := rfl
  h_par x hx := by
    have h0 : x.1.val ≠ 0 := fun h => hx (eq_sRoot_of_fst h)
    simp only [sPar_fst h0]
    omega

/-- The stretched tree is a tree. -/
theorem stretchedTree_isTree : (stretchedTree d k).IsTree := isParFun_sPar.isTree

/-- The layer of `x` is its distance from the root. -/
theorem stretchedTree_dist_root (x : SVert d k) :
    (stretchedTree d k).dist sRoot x = x.1.val := isParFun_sPar.dist_eq x

lemma card_children {u : SVert d k} (hu : u.1.val < d * k) :
    #(children sPar u) = sRat k (u.1.val + 1) := by
  set R := sRat k (u.1.val + 1) with hR
  have hRpos : 0 < R := sRat_pos _
  have hbound : ∀ i : Fin R, u.2.val * R + i.val < sW k (u.1.val + 1) := by
    intro i
    have e : sW k (u.1.val + 1) = R * sW k u.1.val := by rw [sW_eq, Nat.add_sub_cancel]
    have h1 : u.2.val < sW k u.1.val := u.2.2
    have h2 := i.2
    rw [e]
    nlinarith
  let f : Fin R → SVert d k := fun i => ⟨⟨u.1.val + 1, by omega⟩, ⟨u.2.val * R + i.val, hbound i⟩⟩
  have hf : Function.Injective f := by
    intro i i' he
    rw [SVert.ext_iff'] at he
    simp only [f] at he
    exact Fin.ext (by omega)
  have : children sPar u = univ.image f := by
    ext c
    rw [mem_children, mem_image]
    constructor
    · rintro ⟨hcu, hpc⟩
      have hc0 : c.1.val ≠ 0 := by
        intro h0
        rw [eq_sRoot_of_fst h0] at hpc hcu
        exact hcu (by rw [← hpc]; simp [sPar, sRoot])
      have h1 := congrArg (fun y => y.1.val) hpc
      have h2 := congrArg (fun y => y.2.val) hpc
      simp only [sPar_fst hc0, sPar_snd hc0] at h1 h2
      have hc1 : c.1.val = u.1.val + 1 := by omega
      have e : sRat k c.1.val = R := by rw [hc1]
      rw [e] at h2
      refine ⟨⟨c.2.val % R, Nat.mod_lt _ hRpos⟩, mem_univ _, ?_⟩
      rw [SVert.ext_iff']
      refine ⟨Fin.ext hc1.symm, ?_⟩
      simp only [f]
      rw [← h2, mul_comm]
      exact Nat.div_add_mod _ _
    · rintro ⟨i, -, rfl⟩
      have h0 : (f i).1.val ≠ 0 := by simp [f]
      refine ⟨fun he => ?_, ?_⟩
      · have := congrArg (fun y => y.1.val) he
        simp [f] at this
      · rw [SVert.ext_iff']
        refine ⟨Fin.ext ?_, ?_⟩
        · rw [sPar_fst h0]; simp [f]
        · rw [sPar_snd h0]
          simp only [f, ← hR]
          rw [mul_comm, Nat.mul_add_div hRpos, Nat.div_eq_of_lt i.2, add_zero]
  rw [this, card_image_of_injective _ hf, card_univ, Fintype.card_fin]

/-- Size of the subtree of a layer-`ℓ` vertex of the stretched tree:
`∑_{m = ℓ}^{d k} 2 ^ (⌈m/k⌉ - ⌈ℓ/k⌉)` (`0` for `ℓ > d k`). -/
def sF (d k ℓ : ℕ) : ℕ := ∑ m ∈ Ico ℓ (d * k + 1), 2 ^ (sEx k m - sEx k ℓ)

lemma sF_eq_zero {ℓ : ℕ} (hℓ : d * k < ℓ) : sF d k ℓ = 0 := by
  simp [sF, Ico_eq_empty_of_le (show d * k + 1 ≤ ℓ by omega)]

lemma sF_succ {ℓ : ℕ} (hℓ : ℓ ≤ d * k) :
    sF d k ℓ = 1 + sRat k (ℓ + 1) * sF d k (ℓ + 1) := by
  rw [sF, sum_eq_sum_Ico_succ_bot (by omega), sF, mul_sum, Nat.sub_self, pow_zero]
  congr 1
  refine sum_congr rfl fun m hm => ?_
  rw [mem_Ico] at hm
  have h1 := sEx_mono (k := k) (show ℓ ≤ ℓ + 1 by omega)
  have h2 := sEx_mono (k := k) (show ℓ + 1 ≤ m by omega)
  rw [sRat, Nat.add_sub_cancel, ← pow_add]
  congr 1
  omega

/-- Subtree sizes in the stretched tree depend only on the layer. -/
theorem card_sub_stretchedTree (x : SVert d k) :
    #(sub (stretchedTree d k) sRoot x) = sF d k x.1.val := by
  suffices H : ∀ n, ∀ x : SVert d k, d * k - x.1.val = n →
      #(sub (stretchedTree d k) sRoot x) = sF d k x.1.val from H _ x rfl
  intro n
  induction n with
  | zero =>
    intro x hx
    have hx' : x.1.val = d * k := by have := x.1.2; omega
    rw [stretchedTree, isParFun_sPar.card_sub, sF_succ (by omega),
      sF_eq_zero (show d * k < x.1.val + 1 by omega), mul_zero]
    rw [sum_eq_zero]
    intro c hc
    have h1 : c.1.val = x.1.val + 1 := isParFun_sPar.h_child hc
    have := c.1.2
    omega
  | succ n ih =>
    intro x hx
    simp only [stretchedTree] at ih ⊢
    rw [isParFun_sPar.card_sub, sF_succ (by omega)]
    congr 1
    rw [← card_children (u := x) (by omega)]
    refine sum_const_nat fun c hc => ?_
    have h1 : c.1.val = x.1.val + 1 := isParFun_sPar.h_child hc
    rw [ih c (by omega), h1]

/-! ### Size of the stretched tree and properties of `sF` -/

lemma card_SVert_eq_sum : Fintype.card (SVert d k) = ∑ ℓ ∈ range (d * k + 1), sW k ℓ := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (sW k) _

theorem sF_zero : sF d k 0 = Fintype.card (SVert d k) := by
  rw [card_SVert_eq_sum, sF, range_eq_Ico]
  simp [sEx_zero, sW]

lemma sF_le {a b : ℕ} (hab : a ≤ b) : sF d k b ≤ sF d k a := by
  unfold sF
  calc ∑ m ∈ Ico b (d * k + 1), 2 ^ (sEx k m - sEx k b)
      ≤ ∑ m ∈ Ico b (d * k + 1), 2 ^ (sEx k m - sEx k a) :=
        sum_le_sum fun m _ => Nat.pow_le_pow_right (by norm_num)
          (by have := sEx_mono (k := k) hab; omega)
    _ ≤ _ := sum_le_sum_of_subset (Ico_subset_Ico_left hab)

theorem sF_antitone : Antitone (sF d k) := fun _ _ hab => sF_le hab

lemma two_mul_sF_le {a b : ℕ} (hab : a ≤ b) (he : sEx k b = sEx k a + 1) :
    2 * sF d k b ≤ sF d k a := by
  unfold sF
  rw [mul_sum]
  calc ∑ m ∈ Ico b (d * k + 1), 2 * 2 ^ (sEx k m - sEx k b)
      = ∑ m ∈ Ico b (d * k + 1), 2 ^ (sEx k m - sEx k a) := sum_congr rfl fun m hm => by
        rw [mem_Ico] at hm
        have := sEx_mono (k := k) hm.1
        rw [← pow_succ']
        congr 1
        omega
    _ ≤ _ := sum_le_sum_of_subset (Ico_subset_Ico_left hab)

theorem two_mul_sF_add_le (hk : 1 ≤ k) (ℓ : ℕ) : 2 * sF d k (ℓ + k) ≤ sF d k ℓ :=
  two_mul_sF_le (by omega) (sEx_add hk ℓ)

theorem two_mul_sF_one_le (hk : 1 ≤ k) : 2 * sF d k 1 ≤ Fintype.card (SVert d k) :=
  sF_zero (d := d) ▸ two_mul_sF_le (by omega) (by rw [sEx_one hk, sEx_zero])

/-- The layers `b k + 1, …, b k + k` form the `(b+1)`-st level of stretched segments. -/
lemma sEx_seg (b i : ℕ) (hi : i < k) : sEx k (b * k + 1 + i) = b + 1 := by
  unfold sEx
  apply Nat.div_eq_of_lt_le
  · rw [add_mul, one_mul]; omega
  · rw [add_mul, add_mul, one_mul]; omega

lemma sum_sW (d : ℕ) :
    ∑ ℓ ∈ range (d * k + 1), sW k ℓ = (2 ^ (d + 1) - 2) * k + 1 := by
  induction d with
  | zero => simp [sW, sEx_zero]
  | succ d ih =>
    rw [show (d + 1) * k + 1 = (d * k + 1) + k by ring, sum_range_add, ih,
      sum_congr rfl fun i hi =>
        (by rw [sW, sEx_seg d i (mem_range.1 hi)] : sW k (d * k + 1 + i) = 2 ^ (d + 1)),
      sum_const, card_range, smul_eq_mul, pow_succ 2 (d + 1)]
    have : 2 ≤ 2 ^ (d + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize 2 ^ (d + 1) = t at *
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
    rw [show (s + 2) * 2 - 2 = 2 * s + 2 by omega, show s + 2 - 2 = s by omega]
    ring

/-- The stretched tree has `(2 ^ (d+1) - 2) k + 1` vertices. -/
theorem card_SVert : Fintype.card (SVert d k) = (2 ^ (d + 1) - 2) * k + 1 := by
  rw [card_SVert_eq_sum, sum_sW]

/-! ### Lemma D.1: the average layer -/

lemma sum_layer :
    ∑ x : SVert d k, ((x.1.val : ℕ) : ℝ) = ∑ ℓ ∈ range (d * k + 1), (ℓ : ℝ) * sW k ℓ := by
  rw [Fintype.sum_sigma]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun ℓ => (sW k ℓ : ℝ) * ℓ)]
  exact sum_congr rfl fun _ _ => mul_comm _ _

lemma sum_range_add_cast (c : ℝ) (n : ℕ) :
    ∑ i ∈ range n, (c + i) = n * c + n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma layer_sum_lb (hk : 1 ≤ k) (d : ℕ) :
    (k : ℝ) ^ 2 * (2 ^ d * (2 * d - 3) + 3) ≤ ∑ ℓ ∈ range (d * k + 1), (ℓ : ℝ) * sW k ℓ := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show (d + 1) * k + 1 = (d * k + 1) + k by ring, sum_range_add,
      sum_congr rfl fun i hi =>
        (by rw [sW, sEx_seg d i (mem_range.1 hi)]; push_cast; ring :
          ((d * k + 1 + i : ℕ) : ℝ) * (sW k (d * k + 1 + i) : ℝ)
            = ((d * k + 1 : ℝ) + i) * 2 ^ (d + 1)),
      ← sum_mul, sum_range_add_cast, pow_succ (2 : ℝ) d]
    push_cast
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hP : (0 : ℝ) ≤ 2 ^ d := by positivity
    nlinarith [mul_nonneg hP hk0]

/-- Lemma D.1 of the paper: the average layer of the `k`-stretched tree of depth `d` is at least
`k (d - 3/2)`. -/
theorem lemmaD1 (hk : 1 ≤ k) :
    (k : ℝ) * ((d : ℝ) - 3 / 2) * Fintype.card (SVert d k) ≤ ∑ x : SVert d k, ((x.1.val : ℕ) : ℝ) := by
  rw [sum_layer]
  have hS := layer_sum_lb hk d
  have h2 : 2 ≤ 2 ^ (d + 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcard : (Fintype.card (SVert d k) : ℝ) = (2 * 2 ^ d - 2) * k + 1 := by
    rw [card_SVert]
    push_cast [Nat.cast_sub h2]
    ring
  rw [hcard]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hP : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hS0 : 0 ≤ ∑ ℓ ∈ range (d * k + 1), (ℓ : ℝ) * sW k ℓ := sum_nonneg fun _ _ => by positivity
  have ht : 0 ≤ (2 * 2 ^ d - 2) * (k : ℝ) + 1 := by nlinarith
  rcases le_or_gt d 1 with hd | hd
  · have hd' : (d : ℝ) ≤ 1 := by exact_mod_cast hd
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ k) (by linarith : (0 : ℝ) ≤ 3 / 2 - d)) ht]
  · have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ k) (by linarith : (0 : ℝ) ≤ d - 3 / 2))
      (by linarith : (0 : ℝ) ≤ 2 * k - 1)]

end Stretched

end Podc.BilateralNetworkCreation
