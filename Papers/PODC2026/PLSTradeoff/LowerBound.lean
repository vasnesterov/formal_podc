import Papers.PODC2026.PLSTradeoff.Basic

/-!
# Refuting the strong tradeoff conjecture (Section 6)

Theorem 1.6 of *Near-Resolution of the Tradeoff Conjecture in Distributed Proof Labeling
Schemes* (A. Filtser, O. Fischer, PODC 2026): there are graphs in which every `t`-ball contains a
constant fraction of all nodes, a predicate with a `1`-PLS of cost `O(m)`, but every `t`-PLS for it
has cost `Ω(m / t)`.

## The construction

`G t m` is the layered graph `G_{t,m}` of the paper: `2t + 3` layers, the odd (paper) layers
`1, 3, …, 2t + 3` consist of a single node, the even layers of `m` nodes, and consecutive layers are
joined by complete bipartite graphs. Vertices are `LV t m = Fin (t + 2) ⊕ (Fin (t + 1) × Fin m)`:
`Sum.inl k` is the single node of paper layer `2k + 1`, `Sum.inr (k, i)` is node `i` of paper
layer `2k + 2`. The function `lay` is the paper layer minus one; two nodes are adjacent iff their
layers differ by exactly one.

Inputs are `m × m` bit matrices (`Inp m = Fin m → Fin m → Bool`, the paper's `{0,1}^{m²}`), and the
predicate `P t m` says that the two end nodes `vfirst = v¹` and `vlast = v^{2t+3}` have equal inputs
(inputs of all other nodes are ignored). The configuration family is `{G t m}` with all inputs.

## Results

* `Layered.lemma_6_3`: a `1`-PLS of cost `m`.
* `Layered.lemma_6_4_count`, `Layered.lemma_6_4`: every `t`-PLS of cost `p` satisfies
  `m² ≤ 2 p |V|`, hence `m ≤ 4 (t + 1) p`. The proof is a self-contained fooling-set argument
  replacing the reduction to nondeterministic two-party equality (Lemma 6.1 of the paper is not
  assumed): `X ↦ Prov(G, I_{X,X})` is injective, and there are at most `3^{p |V|}` labelings of
  cost `≤ p`.
* `Layered.ball_large`: for `t ≥ 2` and `m ≥ 1`, every `t`-ball contains at least a third of all
  nodes. For `t = 1` the paper's claim `min_v |B_t(v)| = Ω(|V|)` is false
  (`Layered.ball_t1_counterexample`: the `1`-ball of a node in an even layer has at most `3` nodes,
  while `|V(G_{1,m})| = 2m + 3`).
* `Layered.theorem_1_6`: the combination.

## Deviations from the paper

* In our model identifiers are the fixed vertex type, so a node knows its layer and index from its
  identity. The verifier of Lemma 6.3 therefore checks consistency by identity (node `i` of an even
  layer carries the `i`-th row of `I(v¹)`; each odd-layer node compares the two rows with the same
  index in its two neighbouring layers) instead of the paper's degree-based case distinction
  (Lemma 6.2) and the index tags `(i, I_i)`; this also makes the paper's assumption "`m` odd,
  `m ≥ 3`" (only used for the degree tricks) unnecessary. The labels have length exactly `m`.
* Planarity of `G_{t,m}` is not formalized (Mathlib has no planarity).
* The family in the paper is `{G_{t,m}}_{t,m}`; since our node set is a fixed type, we work with the
  singleton family `{G t m}` for each `t, m`. The lower bound for the singleton family is the
  stronger statement.
-/

namespace PLSTradeoff

namespace Layered

open SimpleGraph

/-- Vertices of `G_{t,m}`: `Sum.inl k` is the single node of paper layer `2k+1`, `Sum.inr (k, i)` is
node `i` of paper layer `2k+2`. -/
abbrev LV (t m : ℕ) := Fin (t + 2) ⊕ (Fin (t + 1) × Fin m)

variable {t m : ℕ}

/-- The layer of a node (the paper's layer minus one, i.e. `0, …, 2t+2`). -/
def lay : LV t m → ℕ
  | Sum.inl k => 2 * k.val
  | Sum.inr (k, _) => 2 * k.val + 1

variable (t m) in
/-- The layered graph `G_{t,m}` of Section 6: consecutive layers are joined by complete bipartite
graphs. -/
def G : SimpleGraph (LV t m) where
  Adj u v := lay u + 1 = lay v ∨ lay v + 1 = lay u
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with h | h <;> omega⟩

lemma adj_iff {u v : LV t m} : (G t m).Adj u v ↔ lay u + 1 = lay v ∨ lay v + 1 = lay u := Iff.rfl

lemma lay_le (v : LV t m) : lay v ≤ 2 * t + 2 := by
  rcases v with k | ⟨k, i⟩ <;> simp only [lay] <;> omega

lemma card_LV : Fintype.card (LV t m) = t + 2 + (t + 1) * m := by
  simp [Fintype.card_sum, Fintype.card_prod]

/-- The node `v¹` (first layer). -/
def vfirst : LV t m := Sum.inl 0

/-- The node `v^{2t+3}` (last layer). -/
def vlast : LV t m := Sum.inl (Fin.last (t + 1))

@[simp] lemma lay_vfirst : lay (vfirst : LV t m) = 0 := rfl

@[simp] lemma lay_vlast : lay (vlast : LV t m) = 2 * t + 2 := by
  simp [vlast, lay]; ring

lemma vlast_ne_vfirst : (vlast : LV t m) ≠ vfirst := by
  intro h; have := congrArg lay h; simp at this

/-- Inputs: `m²` bits, viewed as `m` rows of `m` bits. -/
abbrev Inp (m : ℕ) := Fin m → Fin m → Bool

variable (t m) in
/-- The predicate `P`: the two end nodes have equal inputs. -/
def P : SimpleGraph (LV t m) → (LV t m → Inp m) → Prop := fun _ I => I vfirst = I vlast

/-! ### Distances -/

lemma lay_le_of_walk {u v : LV t m} (w : (G t m).Walk u v) :
    lay v ≤ lay u + w.length ∧ lay u ≤ lay v + w.length := by
  induction w with
  | nil => simp
  | cons h w ih =>
    rw [adj_iff] at h
    simp only [Walk.length_cons]
    omega

/-- Distance lower bound: the layer changes by at most one along each edge. -/
lemma lay_le_of_edist {u v : LV t m} {R : ℕ} (h : (G t m).edist u v ≤ R) :
    lay v ≤ lay u + R ∧ lay u ≤ lay v + R := by
  have hne : (G t m).edist u v ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top R) h
  obtain ⟨w, hw⟩ := exists_walk_of_edist_ne_top hne
  have hR : w.length ≤ R := by rw [← hw] at h; exact_mod_cast h
  have := lay_le_of_walk w
  omega

lemma exists_lay (hm : 1 ≤ m) {j : ℕ} (hj : j ≤ 2 * t + 2) : ∃ x : LV t m, lay x = j := by
  rcases Nat.even_or_odd' j with ⟨k, rfl | rfl⟩
  · exact ⟨Sum.inl ⟨k, by omega⟩, rfl⟩
  · exact ⟨Sum.inr (⟨k, by omega⟩, ⟨0, hm⟩), rfl⟩

lemma edist_le_one_of_adj {u v : LV t m} (h : (G t m).Adj u v) : (G t m).edist u v ≤ 1 :=
  (edist_eq_one_iff_adj.2 h).le

/-- Distance upper bound between different layers. -/
lemma edist_le_of_lay (hm : 1 ≤ m) :
    ∀ d : ℕ, ∀ u w : LV t m, lay w = lay u + d + 1 → (G t m).edist u w ≤ (d + 1 : ℕ) := by
  intro d
  induction d with
  | zero =>
    intro u w h
    exact edist_le_one_of_adj (Or.inl (by omega))
  | succ d ih =>
    intro u w h
    obtain ⟨x, hx⟩ := exists_lay (t := t) hm (j := lay u + d + 1) (by have := lay_le w; omega)
    calc (G t m).edist u w ≤ (G t m).edist u x + (G t m).edist x w := SimpleGraph.edist_triangle
      _ ≤ (d + 1 : ℕ) + 1 := add_le_add (ih u x hx) (edist_le_one_of_adj (Or.inl (by omega)))
      _ = ((d + 1 + 1 : ℕ) : ℕ∞) := by push_cast; ring

/-- Two nodes in the same layer are at distance at most two. -/
lemma edist_le_two (hm : 1 ≤ m) {u w : LV t m} (h : lay u = lay w) : (G t m).edist u w ≤ 2 := by
  obtain ⟨x, hx⟩ := exists_lay (t := t) hm
    (j := if lay u = 0 then 1 else lay u - 1) (by have := lay_le u; split_ifs <;> omega)
  have h1 : (G t m).Adj u x := by rw [adj_iff]; split_ifs at hx <;> omega
  have h2 : (G t m).Adj x w := by rw [adj_iff]; split_ifs at hx <;> omega
  calc (G t m).edist u w ≤ (G t m).edist u x + (G t m).edist x w := SimpleGraph.edist_triangle
    _ ≤ 1 + 1 := add_le_add (edist_le_one_of_adj h1) (edist_le_one_of_adj h2)
    _ = 2 := by norm_num

/-- For `t ≥ 2`, the `t`-ball around `v` contains every node whose layer is within `t` of the
layer of `v`. -/
lemma edist_le_of_window (ht : 2 ≤ t) (hm : 1 ≤ m) {v u : LV t m} (h1 : lay u ≤ lay v + t)
    (h2 : lay v ≤ lay u + t) : (G t m).edist v u ≤ t := by
  rcases lt_trichotomy (lay v) (lay u) with h | h | h
  · refine (edist_le_of_lay hm (lay u - lay v - 1) v u (by omega)).trans ?_
    exact_mod_cast (by omega)
  · exact (edist_le_two hm h).trans (by exact_mod_cast ht)
  · rw [edist_comm]
    refine (edist_le_of_lay hm (lay v - lay u - 1) u v (by omega)).trans ?_
    exact_mod_cast (by omega)

/-! ### Lemma 6.3: a cheap `1`-PLS -/

/-- The label of node `i` of the even layer with index `j` (empty if `j` is out of range). -/
def L (ℓ : LV t m → Label) (j : ℕ) (i : Fin m) : Label :=
  if h : j < t + 1 then ℓ (Sum.inr (⟨j, h⟩, i)) else []

/-- The verifier of Lemma 6.3, as a function of the full configuration (it only reads the input of
the node itself and the labels of its neighbours). Even-layer nodes accept; the single node `k`
checks: if it is `v¹`, that the rows of its input are the labels of the next layer; if it is
`v^{2t+3}`, the same for the previous layer; otherwise, that the two neighbouring even layers carry
the same labels, index by index. -/
def verCore (I : LV t m → Inp m) (ℓ : LV t m → Label) : LV t m → Bool
  | Sum.inl k => decide
      ((k.val = 0 → ∀ i, L ℓ k.val i = List.ofFn (I (Sum.inl k) i)) ∧
       (k.val = t + 1 → ∀ i, L ℓ (k.val - 1) i = List.ofFn (I (Sum.inl k) i)) ∧
       (0 < k.val → k.val < t + 1 → ∀ i, L ℓ (k.val - 1) i = L ℓ k.val i))
  | Sum.inr _ => true

lemma verCore_congr {I I' : LV t m → Inp m} {ℓ ℓ' : LV t m → Label} {v : LV t m}
    (h : ∀ u, (G t m).edist v u ≤ 1 → I u = I' u ∧ ℓ u = ℓ' u) :
    verCore I ℓ v = verCore I' ℓ' v := by
  rcases v with k | ⟨k, i⟩
  · have hI := (h (Sum.inl k) (by simp)).1
    have hL : ∀ j, (j = k.val ∨ j = k.val - 1) → L ℓ j = L ℓ' j := by
      intro j hj
      funext i
      unfold L
      split_ifs with hjt
      · refine (h _ (edist_le_one_of_adj ?_)).2
        rw [adj_iff]; simp only [lay]; omega
      · rfl
    simp only [verCore, hI, hL k.val (Or.inl rfl), hL (k.val - 1) (Or.inr rfl)]
  · rfl

/-- The verifier: `verCore` applied to the radius-`1` view (so it is `1`-local by construction). -/
noncomputable def ver1 (Γ : SimpleGraph (LV t m)) (I : LV t m → Inp m) (ℓ : LV t m → Label)
    (v : LV t m) : Bool :=
  verCore (mask Γ v 1 I) (mask Γ v 1 ℓ) v

lemma ver1_eq (I : LV t m → Inp m) (ℓ : LV t m → Label) (v : LV t m) :
    ver1 (G t m) I ℓ v = verCore I ℓ v :=
  verCore_congr fun _ hu => ⟨mask_of_le hu, mask_of_le hu⟩

/-- The honest prover of Lemma 6.3: node `i` of every even layer gets row `i` of `I(v¹)`. -/
def prov1 (_ : SimpleGraph (LV t m)) (I : LV t m → Inp m) : LV t m → Label
  | Sum.inl _ => []
  | Sum.inr (_, i) => List.ofFn (I vfirst i)

variable (t m) in
/-- The `1`-PLS of Lemma 6.3. -/
noncomputable def pls1 : PLS {G t m} (P t m) 1 where
  prov := prov1
  ver := ver1
  isLocal := by
    intro Γ I ℓ Γ' I' ℓ' v h
    obtain ⟨h1, h2⟩ := viewEq_mask_eq h
    simp only [ver1, h1, h2]
  complete := by
    intro Γ hΓ I hP v
    rw [Set.mem_singleton_iff] at hΓ
    subst hΓ
    rw [ver1_eq]
    have hLp : ∀ j < t + 1, ∀ i, L (prov1 (G t m) I) j i = List.ofFn (I vfirst i) := by
      intro j hj i; simp [L, hj, prov1]
    rcases v with k | ⟨k, i⟩
    · simp only [verCore, decide_eq_true_eq]
      refine ⟨fun hk i => ?_, fun hk i => ?_, fun h1 h2 i => ?_⟩
      · have : (Sum.inl k : LV t m) = vfirst := by simp [vfirst, Fin.ext_iff, hk]
        rw [hLp _ (by omega), this]
      · have : (Sum.inl k : LV t m) = vlast := by simp [vlast, Fin.ext_iff, hk]
        rw [hLp _ (by omega), this, hP]
      · rw [hLp _ (by omega), hLp _ h2]
    · rfl
  sound := by
    intro Γ hΓ I ℓ hacc
    rw [Set.mem_singleton_iff] at hΓ
    subst hΓ
    have hacc' : ∀ v, verCore I ℓ v = true := fun v => (ver1_eq I ℓ v).symm.trans (hacc v)
    have key : ∀ j ≤ t, ∀ i, L ℓ j i = List.ofFn (I vfirst i) := by
      intro j
      induction j with
      | zero =>
        intro _ i
        have := hacc' vfirst
        simp only [vfirst, verCore, decide_eq_true_eq] at this
        exact this.1 rfl i
      | succ j ih =>
        intro hj i
        have := hacc' (Sum.inl ⟨j + 1, by omega⟩)
        simp only [verCore, decide_eq_true_eq] at this
        have h := this.2.2 (by simp) (by simp; omega) i
        simp only [Nat.add_sub_cancel] at h
        rw [← h]
        exact ih (by omega) i
    have hlast := hacc' vlast
    simp only [vlast, verCore, decide_eq_true_eq] at hlast
    funext i
    have h := hlast.2.1 (by simp) i
    simp only [Fin.val_last, Nat.add_sub_cancel] at h
    rw [key t le_rfl i] at h
    exact List.ofFn_injective h

/-- **Lemma 6.3** of [Filtser–Fischer, PODC 2026]: there is a `1`-PLS for `P` on `G_{t,m}` with cost
`O(m)` (here: exactly `m`). -/
theorem lemma_6_3 (t m : ℕ) : ∃ S : PLS {G t m} (P t m) 1, S.CostLE m := by
  refine ⟨pls1 t m, ?_⟩
  intro Γ _ I _ v
  rcases v with k | ⟨k, i⟩ <;> simp [pls1, prov1]

/-! ### Lemma 6.4: the lower bound for `t`-PLS -/

/-- The input where `v¹` gets `X`, `v^{2t+3}` gets `Y`, and all other nodes get zeros. -/
def inp (X Y : Inp m) : LV t m → Inp m := fun v =>
  if v = vfirst then X else if v = vlast then Y else fun _ _ => false

@[simp] lemma inp_vfirst (X Y : Inp m) : inp (t := t) X Y vfirst = X := by simp [inp]

@[simp] lemma inp_vlast (X Y : Inp m) : inp (t := t) X Y vlast = Y := by
  simp [inp, vlast_ne_vfirst]

/-- The fooling-set argument: the honest labels of the yes-instance `(X, X)` determine `X`.
If `Prov(I_{X,X}) = Prov(I_{Y,Y})`, then on the input `I_{X,Y}` with these labels every node in
paper layers `≤ t+1` sees the same `t`-view as in `I_{X,X}` and every node in paper layers `≥ t+2`
sees the same `t`-view as in `I_{Y,Y}`, so all nodes accept and soundness gives `X = Y`. -/
theorem prov_injective (S : PLS {G t m} (P t m) t) :
    Function.Injective fun X : Inp m => S.prov (G t m) (inp X X) := by
  intro X Y hXY
  simp only at hXY
  have hG : G t m ∈ ({G t m} : Set (SimpleGraph (LV t m))) := Set.mem_singleton _
  have hacc : ∀ v, S.ver (G t m) (inp X Y) (S.prov (G t m) (inp X X)) v = true := by
    intro v
    by_cases hv : lay v ≤ t
    · have hview : ViewEq t (G t m) (inp X Y) (S.prov (G t m) (inp X X))
          (G t m) (inp X X) (S.prov (G t m) (inp X X)) v := by
        refine ⟨fun _ _ _ => Iff.rfl, fun u hu => ⟨?_, rfl⟩⟩
        have := (lay_le_of_edist hu).1
        have hu' : u ≠ vlast := by rintro rfl; rw [lay_vlast] at this; omega
        simp [inp, hu']
      rw [S.isLocal _ _ _ _ _ _ _ hview]
      exact S.complete _ hG _ (by simp [P]) v
    · have hview : ViewEq t (G t m) (inp X Y) (S.prov (G t m) (inp X X))
          (G t m) (inp Y Y) (S.prov (G t m) (inp Y Y)) v := by
        refine ⟨fun _ _ _ => Iff.rfl, fun u hu => ⟨?_, hXY ▸ rfl⟩⟩
        have := (lay_le_of_edist hu).2
        have hu' : u ≠ vfirst := by rintro rfl; rw [lay_vfirst] at this; omega
        simp [inp, hu']
      rw [S.isLocal _ _ _ _ _ _ _ hview]
      exact S.complete _ hG _ (by simp [P]) v
  simpa [P] using S.sound _ hG _ _ hacc

/-- **Lemma 6.4** of [Filtser–Fischer, PODC 2026], counting form: a `t`-PLS for `P` on `G_{t,m}`
with cost `p` satisfies `m² ≤ 2 p |V(G_{t,m})|`. -/
theorem lemma_6_4_count (S : PLS {G t m} (P t m) t) {p : ℕ} (hS : S.CostLE p) :
    m * m ≤ 2 * p * Fintype.card (LV t m) := by
  have hG : G t m ∈ ({G t m} : Set (SimpleGraph (LV t m))) := Set.mem_singleton _
  -- encode a labeling of cost `≤ p` by the first `p` entries of each label
  let enc : Inp m → (LV t m → Fin p → Option Bool) :=
    fun X v i => (S.prov (G t m) (inp X X) v)[i.val]?
  have hinj : Function.Injective enc := by
    intro X Y h
    apply prov_injective S
    funext v
    apply List.ext_getElem?
    intro i
    show (S.prov (G t m) (inp X X) v)[i]? = (S.prov (G t m) (inp Y Y) v)[i]?
    have hX := hS _ hG (inp X X) (by simp [P]) v
    have hY := hS _ hG (inp Y Y) (by simp [P]) v
    by_cases hi : i < p
    · exact congrFun (congrFun h v) ⟨i, hi⟩
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  have hcard := Fintype.card_le_of_injective enc hinj
  simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_bool, Fintype.card_fin] at hcard
  set n := Fintype.card (LV t m)
  have : 2 ^ (m * m) ≤ 2 ^ (2 * p * n) :=
    calc 2 ^ (m * m) = (2 ^ m) ^ m := pow_mul _ _ _
      _ ≤ ((2 + 1) ^ p) ^ n := hcard
      _ ≤ (4 ^ p) ^ n := by gcongr; norm_num
      _ = 2 ^ (2 * p * n) := by rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul,
          mul_assoc]
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

/-- **Lemma 6.4** of [Filtser–Fischer, PODC 2026]: any `t`-PLS for `P` on `G_{t,m}` has cost
`Ω(m / t)`; explicitly, cost `p` implies `m ≤ 4 (t + 1) p`. -/
theorem lemma_6_4 (S : PLS {G t m} (P t m) t) {p : ℕ} (hS : S.CostLE p) :
    m ≤ 4 * (t + 1) * p := by
  have h := lemma_6_4_count S hS
  rw [card_LV] at h
  by_contra hcon
  have hcon := Nat.lt_of_not_le hcon
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp at h; omega
  · have h4 : 4 ≤ m := by nlinarith
    nlinarith

/-! ### Ball sizes -/

/-- For `t ≥ 2` and `m ≥ 1`, every `t`-ball of `G_{t,m}` contains at least a third of all nodes
(the claim `min_v |B_t(v)| = Ω(|V(G_{t,m})|)` of Theorem 1.6). -/
theorem ball_large (ht : 2 ≤ t) (hm : 1 ≤ m) (v : LV t m) :
    Fintype.card (LV t m) ≤ 3 * {u | (G t m).edist v u ≤ t}.ncard := by
  set a := lay v
  have ha : a ≤ 2 * t + 2 := lay_le v
  -- single nodes and even layers within distance `t` (in layers) of `v`
  set S1 : Finset (Fin (t + 2)) := Finset.univ.filter fun k => 2 * k.val ≤ a + t ∧ a ≤ 2 * k.val + t
  set S2 : Finset (Fin (t + 1)) :=
    Finset.univ.filter fun k => 2 * k.val + 1 ≤ a + t ∧ a ≤ 2 * k.val + 1 + t
  have hS1 : t + 2 ≤ 3 * S1.card := by
    have hsub : Finset.Ico ((a - t + 1) / 2) (min (t + 2) ((a + t) / 2 + 1)) ⊆
        S1.map Fin.valEmbedding := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_map, Fin.valEmbedding_apply]
      exact ⟨⟨j, by omega⟩, by simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and]; omega,
        rfl⟩
    have := Finset.card_le_card hsub
    simp only [Nat.card_Ico, Finset.card_map] at this
    omega
  have hS2 : t + 1 ≤ 3 * S2.card := by
    have hsub : Finset.Ico ((a - t) / 2) (min (t + 1) ((a + t + 1) / 2)) ⊆
        S2.map Fin.valEmbedding := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_map, Fin.valEmbedding_apply]
      exact ⟨⟨j, by omega⟩, by simp only [S2, Finset.mem_filter, Finset.mem_univ, true_and]; omega,
        rfl⟩
    have := Finset.card_le_card hsub
    simp only [Nat.card_Ico, Finset.card_map] at this
    omega
  have hsub : (↑(S1.disjSum (S2 ×ˢ (Finset.univ : Finset (Fin m)))) : Set (LV t m)) ⊆
      {u | (G t m).edist v u ≤ t} := by
    intro u hu
    simp only [Finset.mem_coe, Finset.mem_disjSum, Finset.mem_product, Finset.mem_univ,
      and_true] at hu
    simp only [Set.mem_ofPred_eq]
    rcases hu with ⟨k, hk, rfl⟩ | ⟨⟨k, i⟩, hk, rfl⟩
    · simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact edist_le_of_window ht hm (by show 2 * k.val ≤ a + t; omega)
        (by show a ≤ 2 * k.val + t; omega)
    · simp only [S2, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact edist_le_of_window ht hm (by show 2 * k.val + 1 ≤ a + t; omega)
        (by show a ≤ 2 * k.val + 1 + t; omega)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, Finset.card_disjSum, Finset.card_product, Finset.card_univ,
    Fintype.card_fin] at hle
  rw [card_LV]
  have : (t + 1) * m ≤ 3 * S2.card * m := Nat.mul_le_mul_right m hS2
  nlinarith

/-- The `1`-ball of a node in an even layer has at most `3` nodes (itself and its two
neighbours). -/
theorem ball_inr_one (k : Fin (t + 1)) (i : Fin m) :
    {u | (G t m).edist (Sum.inr (k, i)) u ≤ 1}.ncard ≤ 3 := by
  have hsub : {u | (G t m).edist (Sum.inr (k, i)) u ≤ 1} ⊆
      {Sum.inr (k, i), Sum.inl k.castSucc, Sum.inl k.succ} := by
    intro u hu
    simp only [Set.mem_ofPred_eq] at hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hne : (G t m).edist (Sum.inr (k, i)) u ≠ ⊤ := ne_top_of_le_ne_top (by simp) hu
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
    rw [← hn] at hu
    have hn1 : n ≤ 1 := by exact_mod_cast hu
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn1 with rfl | rfl
    · left; exact (edist_eq_zero_iff.1 hn.symm).symm
    · have hadj := edist_eq_one_iff_adj.1 (by rw [← hn]; rfl)
      rw [adj_iff] at hadj
      right
      rcases u with k' | ⟨k', i'⟩
      · simp only [lay] at hadj
        rcases hadj with h | h
        · right; simp [Fin.ext_iff]; omega
        · left; simp [Fin.ext_iff]; omega
      · simp only [lay] at hadj; omega
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
  refine (Set.ncard_insert_le _ _).trans ?_
  have := Set.ncard_insert_le (Sum.inl k.castSucc : LV t m) {Sum.inl k.succ}
  rw [Set.ncard_singleton] at this
  omega

/-- The ball-size claim of Theorem 1.6 fails for `t = 1`: no constant `c` gives
`|V(G_{1,m})| ≤ c · min_v |B_1(v)|` for all `m`. -/
theorem ball_t1_counterexample (c : ℕ) :
    ∃ m, ∃ v : LV 1 m, c * {u | (G 1 m).edist v u ≤ 1}.ncard < Fintype.card (LV 1 m) := by
  refine ⟨2 * c + 1, Sum.inr (0, 0), ?_⟩
  have := ball_inr_one (t := 1) (m := 2 * c + 1) 0 0
  rw [card_LV]
  have : c * {u | (G 1 (2 * c + 1)).edist (Sum.inr (0, 0)) u ≤ 1}.ncard ≤ c * 3 :=
    Nat.mul_le_mul_left c this
  omega

/-! ### Theorem 1.6 -/

/-- **Theorem 1.6** of [Filtser–Fischer, PODC 2026]: for the layered graphs `G_{t,m}` and the
end-node equality predicate `P`,
1. every `t`-ball contains a constant fraction (`≥ 1/3`) of the nodes (for `t ≥ 2`, `m ≥ 1`; the
   claim is false for `t = 1`, see `ball_t1_counterexample`),
2. there is a `1`-PLS of cost `m` (Lemma 6.3),
3. every `t`-PLS has cost `p ≥ m / (4 (t + 1))` (Lemma 6.4).
Planarity of `G_{t,m}` is not formalized. -/
theorem theorem_1_6 (t m : ℕ) :
    (2 ≤ t → 1 ≤ m → ∀ v : LV t m, Fintype.card (LV t m) ≤ 3 * {u | (G t m).edist v u ≤ t}.ncard) ∧
    (∃ S : PLS {G t m} (P t m) 1, S.CostLE m) ∧
    (∀ (S : PLS {G t m} (P t m) t) (p : ℕ), S.CostLE p → m ≤ 4 * (t + 1) * p) :=
  ⟨fun ht hm v => ball_large ht hm v, lemma_6_3 t m, fun S _ hS => lemma_6_4 S hS⟩

end Layered

end PLSTradeoff
