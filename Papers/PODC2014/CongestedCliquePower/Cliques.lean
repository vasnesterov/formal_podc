import Papers.PODC2014.CongestedCliquePower.LowerBoundGraph

/-!
# Lower bound graphs for `K_ℓ` (Lemma 14 of Drucker–Kuhn–Oshman, PODC 2014)

A. Drucker, F. Kuhn, R. Oshman, *On the Power of the Congested Clique Model*, PODC 2014.

* `LBData.Fits.symm`, `LowerBoundGraph.ofIso` — general facts on Definition 10: the edge
  orientation does not matter, and lower bound graphs transport along graph isomorphisms.
* `lemma14Graph N k p` — the construction of Lemma 14 (whose proof the paper defers to a full
  version): independent sets `S₁, …, S₄` of size `N` (`LBVert.s i j` is `v_{i+1, j}`), perfect
  matchings `S₁–S₂`, `S₃–S₄`, all edges between `S₁ ∪ S₂` and `S₃ ∪ S₄`, `k = ℓ - 4` universal
  nodes `LBVert.u` (the paper writes `u₁, …, u_{ℓ-1}`, a typo) and `p` isolated padding nodes.
* `lemma14LowerBoundGraph` — it is a `(K_{4+k}, K_{N,N})`-lower bound graph.
* `lemma_14` — **Lemma 14**: for `ℓ ≥ 4` and `n ≥ 4(N-1) + ℓ` there is a `(K_ℓ, K_{N,N})`-lower
  bound graph on `Fin n`.
-/

namespace Podc.CongestedCliquePower

open SimpleGraph

section Transport

variable {VH VF V V₂ : Type*} {H : SimpleGraph VH} {F : SimpleGraph VF} {G' : SimpleGraph V}
  {G'' : SimpleGraph V₂}

lemma copyAdj_comp_iff (e : G' ≃g G'') (f : H.Copy G') (x y : V) :
    CopyAdj (e.toCopy.comp f) (e x) (e y) ↔ CopyAdj f x y := by
  unfold CopyAdj
  simp only [Copy.comp_apply]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    exact ⟨a, b, hab, e.injective ha, e.injective hb⟩
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact ⟨a, b, hab, rfl, rfl⟩

lemma mem_range_comp_iff {W : Type*} {K : SimpleGraph W} (e : G' ≃g G'') (f : K.Copy G')
    (x : V) : e x ∈ Set.range (e.toCopy.comp f) ↔ x ∈ Set.range f := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, e.injective (by simpa using ha)⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by simp⟩

namespace LBData

/-- Conditions (b), (c) of Definition 10 do not depend on the orientation of the edge. -/
lemma Fits.symm {D : LBData H F G'} {f : H.Copy G'} {u v : VF} (h : D.Fits f u v) :
    D.Fits f v u := by
  obtain ⟨huv, hA, hB, hc⟩ := h
  refine ⟨huv.symm, hA.symm, hB.symm, fun x => (hc x).trans ?_⟩
  tauto

/-- Transport of the two copies of `F` along a graph isomorphism `e : G' ≃g G''`. -/
def mapIso (D : LBData H F G') (e : G' ≃g G'') : LBData H F G'' where
  φA := e.toCopy.comp D.φA
  φB := e.toCopy.comp D.φB
  disjoint a b h := D.disjoint a b (e.injective (by simpa using h))

lemma fits_mapIso_iff (D : LBData H F G') (e : G' ≃g G'') (f : H.Copy G') (u v : VF) :
    (D.mapIso e).Fits (e.toCopy.comp f) u v ↔ D.Fits f u v := by
  have hA : ∀ a, (D.mapIso e).φA a = e (D.φA a) := fun a => rfl
  have hB : ∀ a, (D.mapIso e).φB a = e (D.φB a) := fun a => rfl
  unfold Fits
  simp only [hA, hB, copyAdj_comp_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [e.surjective.forall]
  refine forall_congr' fun x => ?_
  have hA' : e x ∈ Set.range (D.mapIso e).φA ↔ x ∈ Set.range D.φA :=
    mem_range_comp_iff e D.φA x
  have hB' : e x ∈ Set.range (D.mapIso e).φB ↔ x ∈ Set.range D.φB :=
    mem_range_comp_iff e D.φB x
  rw [mem_range_comp_iff, hA', hB']
  simp only [e.injective.eq_iff]

end LBData

/-- `(H, F)`-lower bound graphs transport along graph isomorphisms. -/
def LowerBoundGraph.ofIso (L : LowerBoundGraph H F G') (e : G' ≃g G'') :
    LowerBoundGraph H F G'' where
  toLBData := L.toLBData.mapIso e
  exists_copy u v huv := by
    obtain ⟨f, hf⟩ := L.exists_copy u v huv
    exact ⟨e.toCopy.comp f, (L.toLBData.fits_mapIso_iff e f u v).2 hf⟩
  fits_of_copy f := by
    obtain ⟨u, v, h⟩ := L.fits_of_copy (e.symm.toCopy.comp f)
    have hf : e.toCopy.comp (e.symm.toCopy.comp f) = f := by
      ext a; simp
    refine ⟨u, v, ?_⟩
    rw [← hf]
    exact (L.toLBData.fits_mapIso_iff e _ u v).2 h

end Transport

/-! ### The construction of Lemma 14 -/

/-- Vertices of the graph of Lemma 14: `s i j` is `v_{i+1, j}` (`i ∈ {0,1,2,3}`, `j ∈ [N]`),
`u a` are the `k = ℓ - 4` universal nodes and `pad a` the `p` isolated padding nodes. -/
inductive LBVert (N k p : ℕ) : Type
  | s (i : Fin 4) (j : Fin N)
  | u (a : Fin k)
  | pad (a : Fin p)
  deriving DecidableEq

namespace LBVert

variable {N k p : ℕ}

/-- `LBVert N k p ≃ (Fin 4 × Fin N) ⊕ Fin k ⊕ Fin p`. -/
def equivSum : LBVert N k p ≃ (Fin 4 × Fin N) ⊕ (Fin k ⊕ Fin p) where
  toFun
    | .s i j => .inl (i, j)
    | .u a => .inr (.inl a)
    | .pad a => .inr (.inr a)
  invFun
    | .inl (i, j) => .s i j
    | .inr (.inl a) => .u a
    | .inr (.inr a) => .pad a
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨i, j⟩ | a | a <;> rfl

instance : Fintype (LBVert N k p) := Fintype.ofEquiv _ equivSum.symm

lemma card : Fintype.card (LBVert N k p) = 4 * N + k + p := by
  rw [Fintype.card_congr equivSum]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

end LBVert

open LBVert

/-- Adjacency of the graph of Lemma 14. -/
def lbAdj {N k p : ℕ} : LBVert N k p → LBVert N k p → Prop
  | .s i j, .s i' j' => (i.val / 2 = i'.val / 2 ∧ i ≠ i' ∧ j = j') ∨ i.val / 2 ≠ i'.val / 2
  | .s _ _, .u _ => True
  | .u _, .s _ _ => True
  | .u a, .u b => a ≠ b
  | _, _ => False

/-- The `(K_ℓ, K_{N,N})`-lower bound graph of Lemma 14, with `ℓ = 4 + k` and `p` isolated
padding nodes: `S_i = {s i j | j}` are independent sets, `s 0 j ~ s 1 j` and `s 2 j ~ s 3 j`
(perfect matchings), `s i j ~ s i' j'` whenever `i ∈ {0,1}`, `i' ∈ {2,3}`, and the `u a` are
adjacent to all non-padding nodes. -/
def lemma14Graph (N k p : ℕ) : SimpleGraph (LBVert N k p) where
  Adj := lbAdj
  symm := ⟨fun x y h => by
    cases x <;> cases y <;> simp only [lbAdj] at h ⊢ <;> grind⟩
  loopless := ⟨fun x h => by
    cases x <;> simp [lbAdj] at h⟩

@[simp] lemma lemma14Graph_adj_ss {N k p : ℕ} (i i' : Fin 4) (j j' : Fin N) :
    (lemma14Graph N k p).Adj (.s i j) (.s i' j') ↔
      (i.val / 2 = i'.val / 2 ∧ i ≠ i' ∧ j = j') ∨ i.val / 2 ≠ i'.val / 2 := Iff.rfl

/-- `φA`: left vertex `j` of `K_{N,N}` ↦ `v_{1,j}`, right vertex `j` ↦ `v_{3,j}`. -/
def phiA {N k p : ℕ} : Fin N ⊕ Fin N → LBVert N k p
  | .inl j => .s 0 j
  | .inr j => .s 2 j

/-- `φB`: left vertex `j` of `K_{N,N}` ↦ `v_{2,j}`, right vertex `j` ↦ `v_{4,j}`. -/
def phiB {N k p : ℕ} : Fin N ⊕ Fin N → LBVert N k p
  | .inl j => .s 1 j
  | .inr j => .s 3 j

/-- The two copies of `K_{N,N}` in `lemma14Graph`. -/
def lemma14Data (N k p : ℕ) :
    LBData (⊤ : SimpleGraph (Fin (4 + k))) (completeBipartiteGraph (Fin N) (Fin N))
      (lemma14Graph N k p) where
  φA := ⟨⟨phiA, fun {x y} h => by
      rcases x with x | x <;> rcases y with y | y <;> simp_all [phiA, lemma14Graph, lbAdj]⟩,
    fun x y h => by rcases x with x | x <;> rcases y with y | y <;> simp_all [phiA]⟩
  φB := ⟨⟨phiB, fun {x y} h => by
      rcases x with x | x <;> rcases y with y | y <;> simp_all [phiB, lemma14Graph, lbAdj]⟩,
    fun x y h => by rcases x with x | x <;> rcases y with y | y <;> simp_all [phiB]⟩
  disjoint a b := by
    show phiA a ≠ phiB b
    rcases a with a | a <;> rcases b with b | b <;> simp [phiA, phiB]

variable {N k p : ℕ}

@[simp] lemma lemma14Data_φA (x : Fin N ⊕ Fin N) : (lemma14Data N k p).φA x = phiA x := rfl
@[simp] lemma lemma14Data_φB (x : Fin N ⊕ Fin N) : (lemma14Data N k p).φB x = phiB x := rfl

/-- The vertices of the `K_ℓ` witnessing the edge `{a, b}` of `K_{N,N}` (`a` left, `b` right):
`v_{1,a}, v_{2,a}, v_{3,b}, v_{4,b}` and all universal nodes. -/
def cliqueFun (a b : Fin N) : Fin (4 + k) → LBVert N k p :=
  Fin.addCases (fun i : Fin 4 => .s i (if i.val < 2 then a else b)) (fun c => .u c)

lemma cliqueFun_adj (a b : Fin N) {x y : Fin (4 + k)} (hxy : x ≠ y) :
    (lemma14Graph N k p).Adj (cliqueFun a b x) (cliqueFun a b y) := by
  induction x using Fin.addCases with
  | left i =>
    induction y using Fin.addCases with
    | left i' =>
      have hii' : i ≠ i' := fun h => hxy (h ▸ rfl)
      simp only [cliqueFun, Fin.addCases_left, lemma14Graph_adj_ss]
      fin_cases i <;> fin_cases i' <;> simp_all
    | right c => simp [cliqueFun, lemma14Graph, lbAdj]
  | right c =>
    induction y using Fin.addCases with
    | left i' => simp [cliqueFun, lemma14Graph, lbAdj]
    | right c' =>
      have hcc' : c ≠ c' := fun h => hxy (h ▸ rfl)
      simpa [cliqueFun, lemma14Graph, lbAdj] using hcc'

lemma cliqueFun_injective (a b : Fin N) : Function.Injective (cliqueFun (k := k) (p := p) a b) := by
  intro x y h
  by_contra hxy
  have := cliqueFun_adj (k := k) (p := p) a b hxy
  rw [h] at this
  exact (lemma14Graph N k p).loopless.irrefl _ this

/-- The copy of `K_ℓ` witnessing the edge `{a, b}` of `K_{N,N}` (Condition I). -/
def cliqueCopy (a b : Fin N) : (⊤ : SimpleGraph (Fin (4 + k))).Copy (lemma14Graph N k p) :=
  ⟨⟨cliqueFun a b, fun {_ _} hxy => cliqueFun_adj a b hxy⟩, cliqueFun_injective a b⟩

@[simp] lemma cliqueCopy_apply (a b : Fin N) (x : Fin (4 + k)) :
    cliqueCopy (p := p) a b x = cliqueFun a b x := rfl

lemma cliqueCopy_fits (a b : Fin N) :
    (lemma14Data N k p).Fits (cliqueCopy a b) (.inl a) (.inr b) := by
  have h : ∀ i : Fin 4, cliqueCopy (k := k) (p := p) a b (Fin.castAdd k i) =
      .s i (if i.val < 2 then a else b) := fun i => by simp [cliqueFun]
  have hne : ∀ i i' : Fin 4, i ≠ i' → Fin.castAdd k i ≠ Fin.castAdd k i' :=
    fun i i' hii' h => hii' (Fin.castAdd_injective _ _ h)
  refine ⟨by simp, ⟨Fin.castAdd k 0, Fin.castAdd k 2, ?_, ?_, ?_⟩,
    ⟨Fin.castAdd k 1, Fin.castAdd k 3, ?_, ?_, ?_⟩, fun x => ?_⟩
  · exact (top_adj _ _).2 (hne 0 2 (by decide))
  · simp [h, phiA]
  · simp [h, phiA]
  · exact (top_adj _ _).2 (hne 1 3 (by decide))
  · simp [h, phiB]
  · simp [h, phiB]
  · simp only [lemma14Data_φA, lemma14Data_φB, phiA, phiB]
    constructor
    · rintro ⟨⟨c, rfl⟩, hAB⟩
      induction c using Fin.addCases with
      | left i =>
        rw [h]
        fin_cases i <;> simp
      | right c =>
        exfalso
        simp only [cliqueCopy_apply, cliqueFun, Fin.addCases_right] at hAB
        rcases hAB with ⟨y | y, hy⟩ | ⟨y | y, hy⟩ <;> simp [phiA, phiB] at hy
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨⟨_, h 0⟩, Or.inl ⟨.inl a, rfl⟩⟩
      · exact ⟨⟨_, h 2⟩, Or.inl ⟨.inr b, rfl⟩⟩
      · exact ⟨⟨_, h 1⟩, Or.inr ⟨.inl a, rfl⟩⟩
      · exact ⟨⟨_, h 3⟩, Or.inr ⟨.inr b, rfl⟩⟩


/-- The independent set of a vertex: `S_i` ↦ `inl i`, `u c` ↦ `inr c` (padding: junk value). -/
def cls : LBVert N k p → Fin 4 ⊕ Fin k
  | .s i _ => .inl i
  | .u c => .inr c
  | .pad _ => .inl 0

/-- Condition II for `lemma14Graph`: a copy of `K_{4+k}` contains no padding node and at most one
node of each independent set `S_i`, hence (by counting) all universal nodes and exactly one node of
each `S_i`; the matchings force these to be `v_{1,a}, v_{2,a}, v_{3,b}, v_{4,b}`. -/
lemma lemma14_fits_of_copy (f : (⊤ : SimpleGraph (Fin (4 + k))).Copy (lemma14Graph N k p)) :
    ∃ x y, (lemma14Data N k p).Fits f x y := by
  have hadj : ∀ a b, a ≠ b → (lemma14Graph N k p).Adj (f a) (f b) :=
    fun a b hab => f.toHom.map_adj ((top_adj a b).2 hab)
  have hnpad : ∀ a q, f a ≠ .pad q := by
    intro a q h
    obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card (by simp; omega) a
    have := hadj a b hb.symm
    rw [h] at this
    cases hfb : f b <;> rw [hfb] at this <;> exact this
  have hinj : Function.Injective (cls ∘ f) := by
    intro a b h
    by_contra hab
    have hab' := hadj a b hab
    simp only [Function.comp_apply] at h
    cases ha : f a <;> cases hb : f b <;> rw [ha, hb] at hab' h
    all_goals first
      | exact hnpad _ _ ha
      | exact hnpad _ _ hb
      | simp_all [cls, lemma14Graph, lbAdj]
  have hbij := (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by simp⟩
  have hS : ∀ i : Fin 4, ∃ a j, f a = .s i j := by
    intro i
    obtain ⟨a, ha⟩ := hbij.2 (.inl i)
    cases hfa : f a with
    | s i' j =>
      simp only [Function.comp_apply, hfa, cls, Sum.inl.injEq] at ha
      exact ⟨a, j, by rw [hfa, ha]⟩
    | u c => simp [cls, hfa] at ha
    | pad q => exact absurd hfa (hnpad _ _)
  have huniq : ∀ a a' i j j', f a = .s i j → f a' = .s i j' → a = a' := by
    intro a a' i j j' h h'
    exact hinj (by simp [cls, h, h'])
  obtain ⟨a0, j0, h0⟩ := hS 0
  obtain ⟨a1, j1, h1⟩ := hS 1
  obtain ⟨a2, j2, h2⟩ := hS 2
  obtain ⟨a3, j3, h3⟩ := hS 3
  have hne : ∀ a a' i i' j j', f a = .s i j → f a' = .s i' j' → i ≠ i' → a ≠ a' := by
    rintro a a' i i' j j' h h' hii' rfl
    rw [h] at h'
    exact hii' (LBVert.s.inj h').1
  have h01 : j0 = j1 := by
    have := hadj a0 a1 (hne _ _ _ _ _ _ h0 h1 (by decide))
    rw [h0, h1] at this
    simpa using this
  have h23 : j2 = j3 := by
    have := hadj a2 a3 (hne _ _ _ _ _ _ h2 h3 (by decide))
    rw [h2, h3] at this
    simpa using this
  subst h01 h23
  refine ⟨.inl j0, .inr j2, by simp, ⟨a0, a2, ?_, ?_, ?_⟩, ⟨a1, a3, ?_, ?_, ?_⟩, fun x => ?_⟩
  · exact (top_adj _ _).2 (hne _ _ _ _ _ _ h0 h2 (by decide))
  · simp [h0, phiA]
  · simp [h2, phiA]
  · exact (top_adj _ _).2 (hne _ _ _ _ _ _ h1 h3 (by decide))
  · simp [h1, phiB]
  · simp [h3, phiB]
  · simp only [lemma14Data_φA, lemma14Data_φB, phiA, phiB]
    constructor
    · rintro ⟨⟨a, rfl⟩, hAB⟩
      obtain ⟨i, j, hij⟩ : ∃ i j, f a = .s i j := by
        rcases hAB with ⟨y | y, hy⟩ | ⟨y | y, hy⟩ <;> exact ⟨_, _, hy.symm⟩
      fin_cases i
      · rw [huniq _ _ _ _ _ hij h0, h0]; simp
      · rw [huniq _ _ _ _ _ hij h1, h1]; simp
      · rw [huniq _ _ _ _ _ hij h2, h2]; simp
      · rw [huniq _ _ _ _ _ hij h3, h3]; simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨⟨_, h0⟩, Or.inl ⟨.inl j0, rfl⟩⟩
      · exact ⟨⟨_, h2⟩, Or.inl ⟨.inr j2, rfl⟩⟩
      · exact ⟨⟨_, h1⟩, Or.inr ⟨.inl j0, rfl⟩⟩
      · exact ⟨⟨_, h3⟩, Or.inr ⟨.inr j2, rfl⟩⟩

variable (N k p) in
/-- `lemma14Graph N k p` is a `(K_{4+k}, K_{N,N})`-lower bound graph. -/
def lemma14LowerBoundGraph :
    LowerBoundGraph (⊤ : SimpleGraph (Fin (4 + k))) (completeBipartiteGraph (Fin N) (Fin N))
      (lemma14Graph N k p) where
  toLBData := lemma14Data N k p
  exists_copy x y hxy := by
    rcases x with a | a <;> rcases y with b | b <;> simp at hxy
    · exact ⟨cliqueCopy a b, cliqueCopy_fits a b⟩
    · exact ⟨cliqueCopy b a, (cliqueCopy_fits b a).symm⟩
  fits_of_copy := lemma14_fits_of_copy

/-- **Lemma 14.** For every `ℓ ≥ 4`, `N` and `n ≥ 4(N - 1) + ℓ` there is a `(K_ℓ, K_{N,N})`-lower
bound graph on `n` vertices. (The paper assumes `N ≥ 4`; no lower bound on `N` is needed.) -/
theorem lemma_14 (ℓ N n : ℕ) (hℓ : 4 ≤ ℓ) (hn : 4 * (N - 1) + ℓ ≤ n) :
    ∃ G' : SimpleGraph (Fin n), Nonempty
      (LowerBoundGraph (⊤ : SimpleGraph (Fin ℓ)) (completeBipartiteGraph (Fin N) (Fin N)) G') := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = 4 + k := ⟨ℓ - 4, by omega⟩
  have hcard : Fintype.card (LBVert N k (n - (4 * N + k))) = n := by
    rw [LBVert.card]; omega
  let e := Fintype.equivFinOfCardEq hcard
  exact ⟨_, ⟨(lemma14LowerBoundGraph N k _).ofIso (Iso.map e _)⟩⟩

end Podc.CongestedCliquePower
