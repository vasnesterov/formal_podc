import Papers.PODC2014.CongestedCliquePower.LowerBoundGraph

/-!
# The construction of Lemma 21 (`K_{ℓ,m}`) is not a lower bound graph

A. Drucker, F. Kuhn, R. Oshman, *On the Power of the Congested Clique Model*, PODC 2014,
Section 3.5.

Lemma 21 states that a `(K_{ℓ,m}, F)`-lower bound graph exists; its proof claims that for a
bipartite `C₄`-free graph `F = (L ∪ R, E_F)` and all `ℓ, m ≥ 2` the following graph `G'` is one:
two copies `V_A = {u_i}`, `V_B = {v_i}` of `F` (`φA i = u_i`, `φB i = v_i`), the matching
`u_i v_i`, and sets `W_L` (`ℓ - 2` nodes) and `W_R` (`m - 2` nodes), with `W_L` complete to
`φA(R) ∪ φB(L) ∪ W_R` and `W_R` complete to `φA(L) ∪ φB(R) ∪ W_L` (`lemma21Graph`).

The proof claims that each side of a `K_{ℓ,m}` contains at least two nodes of `V_A ∪ V_B`
"as `|W_L| = ℓ - 2`, `|W_R| = m - 2`"; but nodes of `W_R` may sit on the `ℓ`-side. We show:

* `lemma21_bad_copy_succ` — for `m = ℓ + 1` (in particular `ℓ = 2`, `m = 3`) and any `F` having a
  vertex `k ∈ R` with two neighbours `i ≠ i'`, the copy `(W_R ∪ {u_k}) × (W_L ∪ {u_i, u_{i'}, v_k})`
  of `K_{ℓ,m}` uses no edge of `F_B`; `lemma21_bad_copy_succ'` is the symmetric case `ℓ = m + 1`.
* `lemma21_bad_copy_free` — for `m ≥ ℓ + 2` and `|V_F| ≥ m - ℓ + 2` there is a copy of `K_{ℓ,m}`
  using no edge of `F_A` or `F_B` at all.
* Consequences (`LBData.not_fits_of_noEB`, `LBData.isContained_inputGraph_of_noEB`): condition II of
  Definition 10 fails, and the conclusion of Observation 11 fails — the input graph `G(X, Y)` of
  the reduction with disjoint inputs `X = E_F`, `Y = ∅` (resp. `X = Y = ∅`) contains `K_{ℓ,m}`.
* `lemma_21_counterexample` — the concrete instance `ℓ = 2`, `m = 3`, `F = K_{2,1}` (the path
  `i – k – i'`, `N = 3`), which satisfies all hypotheses of the paper (`ex(3, C₄) = 3`,
  `extremalNumber_three_cycleGraph_four`).

Brute force indicates that for `ℓ = m` the construction is correct; this is not formalized.
-/

namespace Podc.CongestedCliquePower

open SimpleGraph

section Generic

variable {VH VF V : Type*} {H : SimpleGraph VH} {F : SimpleGraph VF} {G' : SimpleGraph V}

namespace LBData

variable (D : LBData H F G')

/-- The input graph `G(X, Y)` of the reduction of Lemma 13 for Alice's input `X` and Bob's input
`Y` (sets of edges of `F`): `G'` without the edges `φA(e)` for `e ∉ X` and `φB(e)` for `e ∉ Y`. -/
def inputGraph (X Y : Set (Sym2 VF)) : SimpleGraph V where
  Adj x y := G'.Adj x y ∧
    (∀ u v, F.Adj u v → D.φA u = x → D.φA v = y → s(u, v) ∈ X) ∧
    (∀ u v, F.Adj u v → D.φB u = x → D.φB v = y → s(u, v) ∈ Y)
  symm := ⟨fun _ _ ⟨h, hA, hB⟩ => ⟨h.symm,
    fun u v huv hu hv => Sym2.eq_swap ▸ hA v u huv.symm hv hu,
    fun u v huv hu hv => Sym2.eq_swap ▸ hB v u huv.symm hv hu⟩⟩
  loopless := ⟨fun x h => G'.loopless.irrefl x h.1⟩

lemma inputGraph_le (X Y : Set (Sym2 VF)) : D.inputGraph X Y ≤ G' := fun _ _ h => h.1

/-- `G(X, Y)` contains every edge of `G'` outside `E_A ∪ E_B` (hypothesis of Observation 11). -/
lemma inputGraph_fix (X Y : Set (Sym2 VF)) (x y : V) (h : G'.Adj x y) (hA : ¬ D.EA x y)
    (hB : ¬ D.EB x y) : (D.inputGraph X Y).Adj x y :=
  ⟨h, fun u v huv hu hv => absurd ⟨u, v, huv, hu, hv⟩ hA,
    fun u v huv hu hv => absurd ⟨u, v, huv, hu, hv⟩ hB⟩

/-- If `X ∩ Y = ∅`, then for no edge `e` of `F` are both `φA(e)` and `φB(e)` edges of `G(X, Y)`;
so by Observation 11 a lower bound graph's `G(X, Y)` would be `H`-free. -/
lemma inputGraph_not_both (X Y : Set (Sym2 VF)) (hXY : Disjoint X Y) :
    ¬ ∃ u v, F.Adj u v ∧ (D.inputGraph X Y).Adj (D.φA u) (D.φA v) ∧
      (D.inputGraph X Y).Adj (D.φB u) (D.φB v) := by
  rintro ⟨u, v, huv, ⟨-, hA, -⟩, ⟨-, -, hB⟩⟩
  exact Set.disjoint_left.1 hXY (hA u v huv rfl rfl) (hB u v huv rfl rfl)

/-- A copy of `H` none of whose edges is an edge of `F_B` violates conditions (b), (c) for every
edge of `F`. -/
lemma not_fits_of_noEB (f : H.Copy G') (hf : ∀ x y, CopyAdj f x y → ¬ D.EB x y) (u v : VF) :
    ¬ D.Fits f u v := fun ⟨huv, _, hB, _⟩ => hf _ _ hB ⟨u, v, huv, rfl, rfl⟩

/-- A copy of `H` none of whose edges is an edge of `F_B` lies in `G(E_F, ∅)` (Alice holds all
edges, Bob none: disjoint inputs). -/
lemma isContained_inputGraph_of_noEB (f : H.Copy G') (hf : ∀ x y, CopyAdj f x y → ¬ D.EB x y) :
    H ⊑ D.inputGraph Set.univ ∅ := by
  refine ⟨⟨⟨f, fun {a b} hab => ?_⟩, f.injective⟩⟩
  have hc : CopyAdj f (f a) (f b) := ⟨a, b, hab, rfl, rfl⟩
  exact ⟨hc.adj, fun _ _ _ _ _ => Set.mem_univ _,
    fun u v huv hu hv => absurd ⟨u, v, huv, hu, hv⟩ (hf _ _ hc)⟩

/-- A copy of `H` using no edge of `F_A` or `F_B` lies in `G(X, Y)` for all inputs `X, Y`. -/
lemma isContained_inputGraph_of_noE (f : H.Copy G') (hfA : ∀ x y, CopyAdj f x y → ¬ D.EA x y)
    (hfB : ∀ x y, CopyAdj f x y → ¬ D.EB x y) (X Y : Set (Sym2 VF)) :
    H ⊑ D.inputGraph X Y := by
  refine ⟨⟨⟨f, fun {a b} hab => ?_⟩, f.injective⟩⟩
  have hc : CopyAdj f (f a) (f b) := ⟨a, b, hab, rfl, rfl⟩
  exact ⟨hc.adj, fun u v huv hu hv => absurd ⟨u, v, huv, hu, hv⟩ (hfA _ _ hc),
    fun u v huv hu hv => absurd ⟨u, v, huv, hu, hv⟩ (hfB _ _ hc)⟩

end LBData

end Generic

/-! ### The construction of Lemma 21 -/

/-- Vertices of the graph of Lemma 21: `A i = u_i`, `B i = v_i`, `wL a ∈ W_L` (`ℓ - 2` nodes),
`wR a ∈ W_R` (`m - 2` nodes) and `p` isolated padding nodes. -/
inductive L21Vert (VF : Type*) (ℓ m p : ℕ)
  | A (i : VF)
  | B (i : VF)
  | wL (a : Fin (ℓ - 2))
  | wR (a : Fin (m - 2))
  | pad (a : Fin p)

namespace L21Vert

variable {VF : Type*} {ℓ m p : ℕ}

/-- Adjacency of the graph of Lemma 21 (`L` is the left side of `F`, `R = Lᶜ`). -/
def adj (F : SimpleGraph VF) (L : Set VF) : L21Vert VF ℓ m p → L21Vert VF ℓ m p → Prop
  | A i, A j => F.Adj i j
  | B i, B j => F.Adj i j
  | A i, B j => i = j
  | B i, A j => i = j
  | wL _, A j => j ∉ L
  | A j, wL _ => j ∉ L
  | wL _, B i => i ∈ L
  | B i, wL _ => i ∈ L
  | wR _, A i => i ∈ L
  | A i, wR _ => i ∈ L
  | wR _, B j => j ∉ L
  | B j, wR _ => j ∉ L
  | wL _, wR _ => True
  | wR _, wL _ => True
  | _, _ => False

end L21Vert

open L21Vert

/-- The graph `G'` of the proof of Lemma 21 for `F` with bipartition `(L, Lᶜ)`, sides `ℓ, m` of
`K_{ℓ,m}`, and `p` isolated padding nodes. -/
def lemma21Graph {VF : Type*} (F : SimpleGraph VF) (L : Set VF) (ℓ m p : ℕ) :
    SimpleGraph (L21Vert VF ℓ m p) where
  Adj := L21Vert.adj F L
  symm := ⟨fun x y h => by
    cases x <;> cases y <;> simp only [L21Vert.adj] at h ⊢ <;> first | exact h.symm | exact h⟩
  loopless := ⟨fun x h => by cases x <;> simp [L21Vert.adj] at h⟩

/-- The data `φA i = u_i`, `φB i = v_i` of the proof of Lemma 21. -/
def lemma21Data {VW VF : Type*} (H : SimpleGraph VW) (F : SimpleGraph VF) (L : Set VF)
    (ℓ m p : ℕ) : LBData H F (lemma21Graph F L ℓ m p) where
  φA := ⟨⟨L21Vert.A, fun h => h⟩, fun _ _ h => L21Vert.A.inj h⟩
  φB := ⟨⟨L21Vert.B, fun h => h⟩, fun _ _ h => L21Vert.B.inj h⟩
  disjoint _ _ h := by cases h


@[simp] lemma lemma21Data_φA {VW VF : Type*} (H : SimpleGraph VW) (F : SimpleGraph VF)
    (L : Set VF) (ℓ m p : ℕ) (i : VF) : (lemma21Data H F L ℓ m p).φA i = .A i := rfl

@[simp] lemma lemma21Data_φB {VW VF : Type*} (H : SimpleGraph VW) (F : SimpleGraph VF)
    (L : Set VF) (ℓ m p : ℕ) (i : VF) : (lemma21Data H F L ℓ m p).φB i = .B i := rfl

/-! ### The bad copy for `m = ℓ + 1`: `(W_R ∪ {u_k}) × (W_L ∪ {u_i, u_{i'}, v_k})` -/

section Succ

variable {VF : Type*} (F : SimpleGraph VF) (L : Set VF) (ℓ p : ℕ) (k i i' : VF)

/-- The `ℓ`-side of the bad copy: `W_R` (`ℓ - 1` nodes) and `u_k`. -/
def badSuccL (c : Fin ℓ) : L21Vert VF ℓ (ℓ + 1) p :=
  if h : c.val < ℓ - 1 then .wR ⟨c, by omega⟩ else .A k

/-- The `m`-side of the bad copy: `W_L` (`ℓ - 2` nodes), `u_i`, `u_{i'}` and `v_k`. -/
def badSuccR (c : Fin (ℓ + 1)) : L21Vert VF ℓ (ℓ + 1) p :=
  if h : c.val < ℓ - 2 then .wL ⟨c, h⟩
  else if c.val = ℓ - 2 then .A i else if c.val = ℓ - 1 then .A i' else .B k

variable {F L ℓ p k i i'}

lemma badSucc_adj (hk : k ∉ L) (hi : i ∈ L) (hi' : i' ∈ L) (hki : F.Adj k i)
    (hki' : F.Adj k i') (c : Fin ℓ) (d : Fin (ℓ + 1)) :
    (lemma21Graph F L ℓ (ℓ + 1) p).Adj (badSuccL ℓ p k c) (badSuccR ℓ p k i i' d) := by
  simp only [badSuccL, badSuccR]
  split_ifs <;> simp_all [lemma21Graph, L21Vert.adj]

lemma badSuccL_ne_B (c : Fin ℓ) (u : VF) : badSuccL ℓ p k c ≠ .B u := by
  simp only [badSuccL]; split_ifs <;> simp

/-- **Lemma 21 fails for `m = ℓ + 1`.** If some `k ∈ R` has two distinct neighbours `i, i' ∈ L`,
then `(W_R ∪ {u_k}) × (W_L ∪ {u_i, u_{i'}, v_k})` is a copy of `K_{ℓ,ℓ+1}` in the graph of
Lemma 21 that uses no edge of `F_B`. -/
theorem lemma21_bad_copy_succ (hk : k ∉ L) (hi : i ∈ L) (hi' : i' ∈ L)
    (hii' : i ≠ i') (hki : F.Adj k i) (hki' : F.Adj k i') :
    ∃ f : (completeBipartiteGraph (Fin ℓ) (Fin (ℓ + 1))).Copy (lemma21Graph F L ℓ (ℓ + 1) p),
      ∀ x y, CopyAdj f x y →
        ¬ (lemma21Data (completeBipartiteGraph (Fin ℓ) (Fin (ℓ + 1))) F L ℓ (ℓ + 1) p).EB x y := by
  have hki_ne : k ≠ i := fun h => hk (h ▸ hi)
  have hki'_ne : k ≠ i' := fun h => hk (h ▸ hi')
  let f : Fin ℓ ⊕ Fin (ℓ + 1) → L21Vert VF ℓ (ℓ + 1) p :=
    Sum.elim (badSuccL ℓ p k) (badSuccR ℓ p k i i')
  have hadj : ∀ {a b}, (completeBipartiteGraph (Fin ℓ) (Fin (ℓ + 1))).Adj a b →
      (lemma21Graph F L ℓ (ℓ + 1) p).Adj (f a) (f b) := by
    intro a b hab
    rcases a with c | c <;> rcases b with d | d <;> simp at hab
    · exact badSucc_adj hk hi hi' hki hki' c d
    · exact (badSucc_adj hk hi hi' hki hki' d c).symm
  have hinj : Function.Injective f := by
    intro a b h
    rcases a with c | c <;> rcases b with d | d <;>
      simp only [f, Sum.elim_inl, Sum.elim_inr, badSuccL, badSuccR] at h <;>
      split_ifs at h <;> simp_all [Fin.ext_iff] <;> omega
  refine ⟨⟨⟨f, hadj⟩, hinj⟩, ?_⟩
  rintro x y ⟨a, b, hab, rfl, rfl⟩ ⟨u, v, -, hu, hv⟩
  simp only [lemma21Data_φB] at hu hv
  rcases a with c | c
  · exact badSuccL_ne_B c u hu.symm
  rcases b with d | d
  · exact badSuccL_ne_B d v hv.symm
  · simp at hab

end Succ


/-! ### The symmetric bad copy for `ℓ = m + 1`: `(W_R ∪ {u_j, u_{j'}, v_k}) × (W_L ∪ {u_k})` -/

section Succ'

variable {VF : Type*} (F : SimpleGraph VF) (L : Set VF) (m p : ℕ) (k j j' : VF)

/-- The `ℓ`-side of the bad copy: `W_R` (`m - 2` nodes), `u_j`, `u_{j'}` and `v_k`. -/
def badSuccL' (c : Fin (m + 1)) : L21Vert VF (m + 1) m p :=
  if h : c.val < m - 2 then .wR ⟨c, h⟩
  else if c.val = m - 2 then .A j else if c.val = m - 1 then .A j' else .B k

/-- The `m`-side of the bad copy: `W_L` (`m - 1` nodes) and `u_k`. -/
def badSuccR' (c : Fin m) : L21Vert VF (m + 1) m p :=
  if h : c.val < m - 1 then .wL ⟨c, by omega⟩ else .A k

variable {F L m p k j j'}

lemma badSucc'_adj (hk : k ∈ L) (hj : j ∉ L) (hj' : j' ∉ L) (hkj : F.Adj k j)
    (hkj' : F.Adj k j') (c : Fin (m + 1)) (d : Fin m) :
    (lemma21Graph F L (m + 1) m p).Adj (badSuccL' m p k j j' c) (badSuccR' m p k d) := by
  simp only [badSuccL', badSuccR']
  split_ifs <;> simp_all [lemma21Graph, L21Vert.adj, F.adj_comm]

lemma badSuccR'_ne_B (c : Fin m) (u : VF) : badSuccR' m p k c ≠ .B u := by
  simp only [badSuccR']; split_ifs <;> simp

/-- **Lemma 21 fails for `ℓ = m + 1`** (symmetric to `lemma21_bad_copy_succ`): if some `k ∈ L`
has two distinct neighbours `j, j' ∈ R`, then `(W_R ∪ {u_j, u_{j'}, v_k}) × (W_L ∪ {u_k})` is a
copy of `K_{m+1,m}` that uses no edge of `F_B`. -/
theorem lemma21_bad_copy_succ' (hk : k ∈ L) (hj : j ∉ L) (hj' : j' ∉ L)
    (hjj' : j ≠ j') (hkj : F.Adj k j) (hkj' : F.Adj k j') :
    ∃ f : (completeBipartiteGraph (Fin (m + 1)) (Fin m)).Copy (lemma21Graph F L (m + 1) m p),
      ∀ x y, CopyAdj f x y →
        ¬ (lemma21Data (completeBipartiteGraph (Fin (m + 1)) (Fin m)) F L (m + 1) m p).EB x y := by
  have hkj_ne : k ≠ j := fun h => hj (h ▸ hk)
  have hkj'_ne : k ≠ j' := fun h => hj' (h ▸ hk)
  let f : Fin (m + 1) ⊕ Fin m → L21Vert VF (m + 1) m p :=
    Sum.elim (badSuccL' m p k j j') (badSuccR' m p k)
  have hadj : ∀ {a b}, (completeBipartiteGraph (Fin (m + 1)) (Fin m)).Adj a b →
      (lemma21Graph F L (m + 1) m p).Adj (f a) (f b) := by
    intro a b hab
    rcases a with c | c <;> rcases b with d | d <;> simp at hab
    · exact badSucc'_adj hk hj hj' hkj hkj' c d
    · exact (badSucc'_adj hk hj hj' hkj hkj' d c).symm
  have hinj : Function.Injective f := by
    intro a b h
    rcases a with c | c <;> rcases b with d | d <;>
      simp only [f, Sum.elim_inl, Sum.elim_inr, badSuccL', badSuccR'] at h <;>
      split_ifs at h <;> simp_all [Fin.ext_iff] <;> omega
  refine ⟨⟨⟨f, hadj⟩, hinj⟩, ?_⟩
  rintro x y ⟨a, b, hab, rfl, rfl⟩ ⟨u, v, -, hu, hv⟩
  simp only [lemma21Data_φB] at hu hv
  rcases a with c | c
  · rcases b with d | d
    · simp at hab
    · exact badSuccR'_ne_B d v hv.symm
  · exact badSuccR'_ne_B c u hu.symm

end Succ'

/-! ### `m ≥ ℓ + 2`: a copy of `K_{ℓ,m}` using no edge of `F` at all -/

section Free

variable {VF : Type*} {F : SimpleGraph VF} {L : Set VF} {ℓ m p : ℕ}

/-- **Lemma 21 fails badly for `m ≥ ℓ + 2`.** If `m ≥ ℓ + 2` and `|V_F| ≥ m - ℓ + 2`, then `ℓ`
nodes of `W_R` and `m` nodes of `W_L ∪ φA(L) ∪ φB(R)` form a copy of `K_{ℓ,m}` that uses no edge of
`F_A` or `F_B`. (No assumption on `F`: `W_R` is complete to `W_L ∪ φA(L) ∪ φB(R)`.) -/
theorem lemma21_bad_copy_free [Fintype VF] (hm : ℓ + 2 ≤ m)
    (hN : m ≤ ℓ - 2 + Fintype.card VF) :
    ∃ f : (completeBipartiteGraph (Fin ℓ) (Fin m)).Copy (lemma21Graph F L ℓ m p),
      (∀ x y, CopyAdj f x y →
        ¬ (lemma21Data (completeBipartiteGraph (Fin ℓ) (Fin m)) F L ℓ m p).EA x y) ∧
      (∀ x y, CopyAdj f x y →
        ¬ (lemma21Data (completeBipartiteGraph (Fin ℓ) (Fin m)) F L ℓ m p).EB x y) := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin m ↪ Fin (ℓ - 2) ⊕ VF) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hN)
  let g : Fin (ℓ - 2) ⊕ VF → L21Vert VF ℓ m p :=
    Sum.elim .wL fun x => if x ∈ L then .A x else .B x
  have hg : Function.Injective g := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b <;> simp only [g, Sum.elim_inl, Sum.elim_inr] at h
    · simpa using h
    all_goals split_ifs at h <;> simp_all
  let f : Fin ℓ ⊕ Fin m → L21Vert VF ℓ m p :=
    Sum.elim (fun c => .wR ⟨c, by omega⟩) (g ∘ e)
  have hR : ∀ (c : Fin ℓ) (d : Fin m),
      (lemma21Graph F L ℓ m p).Adj (.wR ⟨c, by omega⟩) (g (e d)) := by
    intro c d
    rcases e d with a | a
    · trivial
    · simp only [g, Sum.elim_inr]
      split_ifs with ha
      · exact ha
      · exact ha
  have hadj : ∀ {a b}, (completeBipartiteGraph (Fin ℓ) (Fin m)).Adj a b →
      (lemma21Graph F L ℓ m p).Adj (f a) (f b) := by
    intro a b hab
    rcases a with c | c <;> rcases b with d | d <;> simp at hab
    · exact hR c d
    · exact (hR d c).symm
  have hinj : Function.Injective f := by
    intro a b h
    rcases a with c | c <;> rcases b with d | d <;> simp only [f, Sum.elim_inl, Sum.elim_inr,
      Function.comp_apply] at h
    · simp only [L21Vert.wR.injEq, Fin.mk.injEq] at h
      exact congrArg _ (Fin.ext h)
    · exact absurd h.symm (by rcases e d with a | a <;> simp only [g, Sum.elim_inl,
        Sum.elim_inr] <;> [simp; split_ifs <;> simp])
    · exact absurd h (by rcases e c with a | a <;> simp only [g, Sum.elim_inl,
        Sum.elim_inr] <;> [simp; split_ifs <;> simp])
    · exact congrArg _ (e.injective (hg h))
  refine ⟨⟨⟨f, hadj⟩, hinj⟩, ?_, ?_⟩ <;>
    rintro x y ⟨a, b, hab, rfl, rfl⟩ ⟨u, v, -, hu, hv⟩ <;>
    simp only [lemma21Data_φA, lemma21Data_φB] at hu hv <;>
    rcases a with c | c <;> rcases b with d | d <;> simp_all [f]

end Free


/-! ### Consequences -/

/-- **The construction of Lemma 21 is not a `(K_{ℓ,ℓ+1}, F)`-lower bound graph.** If some
`k ∈ R` has two distinct neighbours `i, i' ∈ L` in `F`, then for the paper's `G'`, `φA`, `φB`
(sides `ℓ ≥ 2`, `m = ℓ + 1`, any padding):
1. condition II of Definition 10 fails: some copy of `K_{ℓ,ℓ+1}` fits no edge of `F`;
2. hence no `LowerBoundGraph` structure has this data;
3. the conclusion of Observation 11 fails: for the disjoint inputs `X = E_F` (Alice), `Y = ∅`
   (Bob), the input graph `G(X, Y)` (which satisfies the hypotheses of Observation 11:
   `inputGraph_le`, `inputGraph_fix`) contains `K_{ℓ,ℓ+1}`, although for no edge `e` of `F` are
   both `φA(e)`, `φB(e)` present. So the reduction of Lemma 13 answers "intersecting" on
   disjoint inputs. -/
theorem lemma21_fails_succ {VF : Type*} {F : SimpleGraph VF} {L : Set VF} (ℓ p : ℕ)
    {k i i' : VF} (hk : k ∉ L) (hi : i ∈ L) (hi' : i' ∈ L) (hii' : i ≠ i')
    (hki : F.Adj k i) (hki' : F.Adj k i') :
    let H := completeBipartiteGraph (Fin ℓ) (Fin (ℓ + 1))
    let D := lemma21Data H F L ℓ (ℓ + 1) p
    (∃ f : H.Copy (lemma21Graph F L ℓ (ℓ + 1) p), ∀ u v, ¬ D.Fits f u v) ∧
    (¬ ∃ LB : LowerBoundGraph H F (lemma21Graph F L ℓ (ℓ + 1) p), LB.toLBData = D) ∧
    H ⊑ D.inputGraph Set.univ ∅ ∧
    ¬ ∃ u v, F.Adj u v ∧ (D.inputGraph Set.univ ∅).Adj (D.φA u) (D.φA v) ∧
      (D.inputGraph Set.univ ∅).Adj (D.φB u) (D.φB v) := by
  intro H D
  obtain ⟨f, hf⟩ := lemma21_bad_copy_succ (p := p) hk hi hi' hii' hki hki'
  refine ⟨⟨f, D.not_fits_of_noEB f hf⟩, ?_, D.isContained_inputGraph_of_noEB f hf,
    D.inputGraph_not_both _ _ (Set.disjoint_empty _)⟩
  rintro ⟨LB, hLB⟩
  obtain ⟨u, v, h⟩ := LB.fits_of_copy f
  rw [hLB] at h
  exact D.not_fits_of_noEB f hf u v h

/-- The symmetric statement for `ℓ = m + 1` (some `k ∈ L` with two neighbours in `R`). -/
theorem lemma21_fails_succ' {VF : Type*} {F : SimpleGraph VF} {L : Set VF} (m p : ℕ)
    {k j j' : VF} (hk : k ∈ L) (hj : j ∉ L) (hj' : j' ∉ L) (hjj' : j ≠ j')
    (hkj : F.Adj k j) (hkj' : F.Adj k j') :
    let H := completeBipartiteGraph (Fin (m + 1)) (Fin m)
    let D := lemma21Data H F L (m + 1) m p
    (∃ f : H.Copy (lemma21Graph F L (m + 1) m p), ∀ u v, ¬ D.Fits f u v) ∧
    (¬ ∃ LB : LowerBoundGraph H F (lemma21Graph F L (m + 1) m p), LB.toLBData = D) ∧
    H ⊑ D.inputGraph Set.univ ∅ ∧
    ¬ ∃ u v, F.Adj u v ∧ (D.inputGraph Set.univ ∅).Adj (D.φA u) (D.φA v) ∧
      (D.inputGraph Set.univ ∅).Adj (D.φB u) (D.φB v) := by
  intro H D
  obtain ⟨f, hf⟩ := lemma21_bad_copy_succ' (p := p) hk hj hj' hjj' hkj hkj'
  refine ⟨⟨f, D.not_fits_of_noEB f hf⟩, ?_, D.isContained_inputGraph_of_noEB f hf,
    D.inputGraph_not_both _ _ (Set.disjoint_empty _)⟩
  rintro ⟨LB, hLB⟩
  obtain ⟨u, v, h⟩ := LB.fits_of_copy f
  rw [hLB] at h
  exact D.not_fits_of_noEB f hf u v h

/-- For `m ≥ ℓ + 2` and `|V_F| ≥ m - ℓ + 2` the construction of Lemma 21 is not a
`(K_{ℓ,m}, F)`-lower bound graph, and the input graph `G(X, Y)` contains `K_{ℓ,m}` for **all**
inputs `X, Y` (in particular `X = Y = ∅`). -/
theorem lemma21_fails_free {VF : Type*} [Fintype VF] {F : SimpleGraph VF} {L : Set VF}
    {ℓ m : ℕ} (p : ℕ) (hm : ℓ + 2 ≤ m) (hN : m ≤ ℓ - 2 + Fintype.card VF) :
    let H := completeBipartiteGraph (Fin ℓ) (Fin m)
    let D := lemma21Data H F L ℓ m p
    (∃ f : H.Copy (lemma21Graph F L ℓ m p), ∀ u v, ¬ D.Fits f u v) ∧
    (¬ ∃ LB : LowerBoundGraph H F (lemma21Graph F L ℓ m p), LB.toLBData = D) ∧
    ∀ X Y : Set (Sym2 VF), H ⊑ D.inputGraph X Y := by
  intro H D
  obtain ⟨f, hfA, hfB⟩ := lemma21_bad_copy_free (F := F) (L := L) (p := p) hm hN
  refine ⟨⟨f, D.not_fits_of_noEB f hfB⟩, ?_, D.isContained_inputGraph_of_noE f hfA hfB⟩
  rintro ⟨LB, hLB⟩
  obtain ⟨u, v, h⟩ := LB.fits_of_copy f
  rw [hLB] at h
  exact D.not_fits_of_noEB f hfB u v h

/-! ### The concrete counterexample `ℓ = 2`, `m = 3`, `F = K_{2,1}` -/

/-- `ex(3, C₄) = 3`: the triangle is `C₄`-free. -/
theorem extremalNumber_three_cycleGraph_four : extremalNumber 3 (cycleGraph 4) = 3 := by
  apply le_antisymm
  · rw [← Fintype.card_fin 3, extremalNumber_le_iff]
    intro G _ _
    exact card_edgeFinset_le_card_choose_two.trans (by simp)
  · have : 2 < extremalNumber (Fintype.card (Fin 3)) (cycleGraph 4) := by
      rw [lt_extremalNumber_iff]
      refine ⟨⊤, inferInstance, ?_, ?_⟩
      · rintro ⟨f⟩
        have := Fintype.card_le_of_injective f f.injective
        simp at this
      · rw [card_edgeFinset_top_eq_card_choose_two]; simp
    simp at this
    omega

/-- The graph `F = K_{2,1}` (the path `i – k – i'`) with `L = {i, i'}`, `R = {k}`
satisfies the hypotheses of Section 3.5: it has `N = 3 ≥ 2` vertices, is bipartite with sides
`L`, `R`, is `C₄`-free, and has `2 ≥ ex(3, C₄)/2` edges. -/
theorem k21_hypotheses :
    Fintype.card (Fin 2 ⊕ Fin 1) = 3 ∧
    (∀ x y, (completeBipartiteGraph (Fin 2) (Fin 1)).Adj x y →
      (x ∈ Set.range Sum.inl ↔ y ∉ Set.range Sum.inl)) ∧
    (cycleGraph 4).Free (completeBipartiteGraph (Fin 2) (Fin 1)) ∧
    (completeBipartiteGraph (Fin 2) (Fin 1)).edgeSet.ncard = 2 ∧
    extremalNumber 3 (cycleGraph 4) ≤ 2 * 2 := by
  refine ⟨by simp, ?_, ?_, ?_, by rw [extremalNumber_three_cycleGraph_four]; omega⟩
  · rintro (x | x) (y | y) h <;> simp at h ⊢
  · rintro ⟨f⟩
    have := Fintype.card_le_of_injective f f.injective
    simp at this
  · let _ : DecidableRel (completeBipartiteGraph (Fin 2) (Fin 1)).Adj := fun a b =>
      inferInstanceAs (Decidable (a.isLeft ∧ b.isRight ∨ a.isRight ∧ b.isLeft))
    rw [Set.ncard_eq_toFinset_card']
    decide

/-- **Counterexample to the proof of Lemma 21** (`ℓ = 2`, `m = 3`, `N = 3`,
`F = K_{2,1}` = the path `i – k – i'` with `L = {i, i'}`, `R = {k}`, no padding): with `W_L = ∅`,
`W_R = {w}`, the paper's graph `G'` contains the copy `{w, u_k} × {u_i, u_{i'}, v_k}` of `K_{2,3}`,
which fits no edge of `F` (condition II fails), so `G'` with the paper's `φA, φB` is not a
`(K_{2,3}, F)`-lower bound graph; and the input graph for the disjoint inputs `X = E_F`, `Y = ∅`
contains `K_{2,3}` (Observation 11 fails). -/
theorem lemma_21_counterexample :
    let F := completeBipartiteGraph (Fin 2) (Fin 1)
    let L : Set (Fin 2 ⊕ Fin 1) := Set.range Sum.inl
    let H := completeBipartiteGraph (Fin 2) (Fin 3)
    let D := lemma21Data H F L 2 3 0
    (∃ f : H.Copy (lemma21Graph F L 2 3 0), ∀ u v, ¬ D.Fits f u v) ∧
    (¬ ∃ LB : LowerBoundGraph H F (lemma21Graph F L 2 3 0), LB.toLBData = D) ∧
    H ⊑ D.inputGraph Set.univ ∅ ∧
    ¬ ∃ u v, F.Adj u v ∧ (D.inputGraph Set.univ ∅).Adj (D.φA u) (D.φA v) ∧
      (D.inputGraph Set.univ ∅).Adj (D.φB u) (D.φB v) :=
  lemma21_fails_succ (F := completeBipartiteGraph (Fin 2) (Fin 1)) (L := Set.range Sum.inl) 2 0
    (k := .inr 0) (i := .inl 0) (i' := .inl 1) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp)


end Podc.CongestedCliquePower
