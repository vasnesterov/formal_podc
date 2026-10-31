import Papers.PODC2018.JupiterListSpec.OT

/-!
# The global state space of CJupiter (Sections 3.3 and 5)

Fix a *schedule*: every operation `k : ι` has a server rank `rank k` (its position in the total
order `≺s` established by the server), a client `cl k`, an original form `orig k` and a generation
context `ctx k` (the operations its client had processed when generating it).

* `Sched.T k V` is the form of operation `k` transformed to the state (vertex) whose operation set
  is `V`: transform `k` against the `≺s`-last operation of `V \ ctx k` (recursively). This is the
  label of the edge `V → V ∪ {k}` of the n-ary ordered state space of CJupiter (Section 3.1,
  Lemmas 5 and 7) and of the 2D state spaces of Jupiter (Propositions 14 and 16).
* `Sched.L V` is the list content of vertex `V`.
* `Sched.Vert V` is the set of vertices of the (global) state space: causally closed operation
  sets consisting of a `≺s`-prefix plus operations of a single client.

Main results (under the schedule axioms `Sched.WF`):
* `Sched.edge` — along every edge `V → V ∪ {x}` between vertices the list evolves by applying
  `T x V`, which is a valid form of `x` (this is where CP1 is used; Theorem 11's argument);
* `Sched.mem_L` — the list at `V` contains exactly the inserted-but-not-deleted elements of `V`
  (condition 1(a) of the weak list specification);
* `Sched.compatible` — the lists of any two vertices are compatible (Theorem 26), via
  `Sched.Vert.inter` (vertex sets are closed under intersection: Lemmas 23–24) and
  `Sched.sublist_of_subset` (order preservation along paths: Lemma 25).
-/

namespace Podc.JupiterListSpec

/-- A schedule of operations identified by `ι` (which is also the type of list elements: an
operation `k` that inserts, inserts the element `k`). -/
structure Sched (ι : Type) where
  /-- position in the server's total order `≺s` -/
  rank : ι → ℕ
  /-- the generating client -/
  cl : ι → ℕ
  /-- the original operation -/
  orig : ι → LOp ι
  /-- the generation context -/
  ctx : ι → Finset ι

variable {ι : Type} [DecidableEq ι]

namespace Sched

variable (S : Sched ι)

/-- The `≺s`-last element of a nonempty set. -/
noncomputable def top (V : Finset ι) (h : V.Nonempty) : ι :=
  (V.exists_max_image S.rank h).choose

theorem top_mem (V : Finset ι) (h : V.Nonempty) : S.top V h ∈ V :=
  (V.exists_max_image S.rank h).choose_spec.1

theorem le_top (V : Finset ι) (h : V.Nonempty) {y : ι} (hy : y ∈ V) :
    S.rank y ≤ S.rank (S.top V h) :=
  (V.exists_max_image S.rank h).choose_spec.2 y hy

/-- If `l ∈ V` is strictly `≺s`-after every other element of `V`, it is the top. -/
theorem top_eq {V : Finset ι} (h : V.Nonempty) {l : ι} (hl : l ∈ V)
    (hlt : ∀ y ∈ V, y ≠ l → S.rank y < S.rank l) : S.top V h = l := by
  by_contra hne
  have h1 := hlt _ (S.top_mem V h) hne
  have h2 := S.le_top V h hl
  omega

/-- `T k V`: operation `k` transformed to vertex `V` (the label of the edge `V → V ∪ {k}`). -/
noncomputable def T (k : ι) (V : Finset ι) : LOp ι :=
  if h : (V \ S.ctx k).Nonempty then
    xf (T k (V.erase (S.top _ h))) (T (S.top _ h) (V.erase (S.top _ h)))
  else S.orig k
termination_by V.card
decreasing_by
  all_goals exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.1 (S.top_mem _ h)).1

/-- `L V`: the list content of vertex `V`, obtained along the path that adds the `≺s`-last
operation last. -/
noncomputable def L (V : Finset ι) : List ι :=
  if h : V.Nonempty then (S.T (S.top V h) (V.erase (S.top V h))).apply (L (V.erase (S.top V h)))
  else []
termination_by V.card
decreasing_by exact Finset.card_erase_lt_of_mem (S.top_mem _ h)

theorem T_of_subset {k : ι} {V : Finset ι} (h : V ⊆ S.ctx k) : S.T k V = S.orig k := by
  rw [T, dif_neg]
  rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset]
  exact h

/-- Unfolding `T` at the `≺s`-last operation `l`. -/
theorem T_insert {k l : ι} {V : Finset ι} (hlV : l ∉ V) (hlk : l ∉ S.ctx k)
    (hlt : ∀ y ∈ V, y ∉ S.ctx k → S.rank y < S.rank l) :
    S.T k (insert l V) = xf (S.T k V) (S.T l V) := by
  have hne : (insert l V \ S.ctx k).Nonempty := ⟨l, by simp [hlk]⟩
  have htop : S.top _ hne = l := by
    apply S.top_eq hne (by simp [hlk])
    intro y hy hyl
    simp only [Finset.mem_sdiff, Finset.mem_insert] at hy
    rcases hy with ⟨rfl | hy, hk⟩
    · exact absurd rfl hyl
    · exact hlt y hy hk
  rw [T, dif_pos hne]
  simp only [htop, Finset.erase_insert hlV]

/-- Unfolding `L` at the `≺s`-last operation `x`. -/
theorem L_insert {x : ι} {V : Finset ι} (hx : x ∉ V) (hlt : ∀ y ∈ V, S.rank y < S.rank x) :
    S.L (insert x V) = (S.T x V).apply (S.L V) := by
  have hne : (insert x V).Nonempty := ⟨x, by simp⟩
  have htop : S.top _ hne = x := by
    apply S.top_eq hne (by simp)
    intro y hy hyx
    simp only [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact absurd rfl hyx
    · exact hlt y hy
  rw [L, dif_pos hne]
  simp only [htop, Finset.erase_insert hx]

theorem L_empty : S.L ∅ = [] := by
  rw [L, dif_neg]; simp

/-- Causally closed operation sets. -/
def Closed (V : Finset ι) : Prop := ∀ x ∈ V, S.ctx x ⊆ V

/-- Vertices of the global state space: causally closed sets consisting of a `≺s`-prefix and of
operations of a single client. -/
def Vert (V : Finset ι) : Prop :=
  S.Closed V ∧ ∃ s c, (∀ x, S.rank x < s → x ∈ V) ∧ ∀ x ∈ V, s ≤ S.rank x → S.cl x = c

/-- An original operation that inserts, inserts its own identifier with its client's priority. -/
def OrigOk (k : ι) : Prop :=
  match S.orig k with
  | .ins a _ pr => a = k ∧ pr = S.cl k
  | _ => True

/-- Axioms of a schedule on a set `D` of (generated) operations. -/
structure WF (D : Set ι) : Prop where
  inj : Set.InjOn S.rank D
  ctx_sub : ∀ k ∈ D, ↑(S.ctx k) ⊆ D
  ctx_lt : ∀ k ∈ D, ∀ j ∈ S.ctx k, S.rank j < S.rank k
  /-- a client's earlier operations are in the context of its later ones -/
  own : ∀ k ∈ D, ∀ j ∈ D, S.cl j = S.cl k → S.rank j < S.rank k → j ∈ S.ctx k
  /-- operations of other clients are received in `≺s` order (FIFO from the server) -/
  pref : ∀ k ∈ D, ∀ j ∈ S.ctx k, S.cl j ≠ S.cl k → ∀ i, S.rank i ≤ S.rank j → i ∈ S.ctx k
  trans : ∀ k ∈ D, ∀ j ∈ S.ctx k, S.ctx j ⊆ S.ctx k
  /-- the original operation was valid at its generation state -/
  orig : ∀ k ∈ D, Real (S.orig k) (S.orig k) (S.L (S.ctx k))
  origOk : ∀ k ∈ D, S.OrigOk k

variable {S} {D : Set ι}

theorem WF.vert_ctx' (hW : S.WF D) {k : ι} (hk : k ∈ D) :
    ∃ s, (∀ x, S.rank x < s → x ∈ S.ctx k) ∧ ∀ x ∈ S.ctx k, s ≤ S.rank x → S.cl x = S.cl k := by
  by_cases hA : ∃ j ∈ S.ctx k, S.cl j ≠ S.cl k
  · classical
    let A := (S.ctx k).filter (fun j => S.cl j ≠ S.cl k)
    have hAne : A.Nonempty := by
      obtain ⟨j, hj, hjc⟩ := hA; exact ⟨j, by simp [A, hj, hjc]⟩
    obtain ⟨j0, hj0, hmax⟩ := A.exists_max_image S.rank hAne
    simp only [A, Finset.mem_filter] at hj0
    refine ⟨S.rank j0 + 1, fun x hx => hW.pref k hk j0 hj0.1 hj0.2 x (by omega), ?_⟩
    intro x hx hle
    by_contra hc
    have := hmax x (by simp [A, hx, hc])
    omega
  · push_neg at hA
    exact ⟨0, fun x hx => absurd hx (Nat.not_lt_zero _), fun x hx _ => hA x hx⟩

theorem WF.vert_ctx (hW : S.WF D) {k : ι} (hk : k ∈ D) : S.Vert (S.ctx k) := by
  obtain ⟨s, hpre, hcl⟩ := hW.vert_ctx' hk
  exact ⟨fun j hj => hW.trans k hk j hj, s, S.cl k, hpre, hcl⟩

/-- Extending the set of operations on which the schedule axioms hold by a new operation `x`
(the `≺s`-last of its client). -/
theorem WF.addOp (hW : S.WF D) {x : ι} (hinj : Set.InjOn S.rank (insert x D))
    (hsub : ↑(S.ctx x) ⊆ D)
    (hlt : ∀ j ∈ S.ctx x, S.rank j < S.rank x)
    (hown : ∀ j ∈ D, S.cl j = S.cl x → S.rank j < S.rank x → j ∈ S.ctx x)
    (hnew : ∀ k ∈ D, S.cl k = S.cl x → S.rank k < S.rank x)
    (hpref : ∀ j ∈ S.ctx x, S.cl j ≠ S.cl x → ∀ i, S.rank i ≤ S.rank j → i ∈ S.ctx x)
    (htrans : ∀ j ∈ S.ctx x, S.ctx j ⊆ S.ctx x)
    (horig : Real (S.orig x) (S.orig x) (S.L (S.ctx x)))
    (hok : S.OrigOk x) : S.WF (insert x D) := by
  refine ⟨hinj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro k (rfl | hk)
    · exact hsub.trans (Set.subset_insert _ _)
    · exact (hW.ctx_sub k hk).trans (Set.subset_insert _ _)
  · rintro k (rfl | hk)
    · exact hlt
    · exact hW.ctx_lt k hk
  · rintro k (rfl | hk) j (rfl | hj) hc hr
    · omega
    · exact hown j hj hc hr
    · have := hnew k hk hc.symm; omega
    · exact hW.own k hk j hj hc hr
  · rintro k (rfl | hk)
    · exact hpref
    · exact hW.pref k hk
  · rintro k (rfl | hk)
    · exact htrans
    · exact hW.trans k hk
  · rintro k (rfl | hk)
    · exact horig
    · exact hW.orig k hk
  · rintro k (rfl | hk)
    · exact hok
    · exact hW.origOk k hk

/-- The vertex `ctx x ∪ {x}` reached by the generating client of `x`. -/
theorem WF.vert_insert_ctx (hW : S.WF D) {k : ι} (hk : k ∈ D) : S.Vert (insert k (S.ctx k)) := by
  obtain ⟨s, hpre, hcl⟩ := hW.vert_ctx' hk
  refine ⟨?_, s, S.cl k, fun x hx => Finset.mem_insert_of_mem (hpre x hx), ?_⟩
  · intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact Finset.subset_insert _ _
    · exact (hW.trans k hk y hy).trans (Finset.subset_insert _ _)
  · intro x hx hxs
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rfl
    · exact hcl x hx hxs

/-- Removing the `≺s`-last element of a vertex gives a vertex. -/
theorem Vert.erase_top (hW : S.WF D) {V : Finset ι} (hV : S.Vert V) (hVD : ↑V ⊆ D)
    {m : ι} (hm : m ∈ V) (hmax : ∀ y ∈ V, S.rank y ≤ S.rank m) : S.Vert (V.erase m) := by
  obtain ⟨hcl, s, c, hpre, hcli⟩ := hV
  refine ⟨?_, min s (S.rank m), c, ?_, ?_⟩
  · intro x hx y hy
    have hxV := Finset.mem_of_mem_erase hx
    refine Finset.mem_erase.2 ⟨?_, hcl x hxV hy⟩
    rintro rfl
    have := hW.ctx_lt x (hVD hxV) y hy
    have := hmax x hxV
    omega
  · intro x hx
    refine Finset.mem_erase.2 ⟨?_, hpre x (by omega)⟩
    rintro rfl; omega
  · intro x hx hle
    have hxV := Finset.mem_of_mem_erase hx
    rcases le_total s (S.rank m) with h | h
    · exact hcli x hxV (by omega)
    · exfalso
      have h1 := hmax x hxV
      have : S.rank x = S.rank m := by omega
      exact Finset.ne_of_mem_erase hx (hW.inj (hVD hxV) (hVD hm) this)

/-- Removing from a vertex `V ⊇ U` (`U` a vertex) the `≺s`-last element of `V \ U` gives a
vertex. -/
theorem Vert.erase_top_sdiff (hW : S.WF D) {U V : Finset ι} (hU : S.Vert U) (hV : S.Vert V)
    (hVD : ↑V ⊆ D) (hUV : U ⊆ V) {m : ι} (hm : m ∈ V) (hmU : m ∉ U)
    (hmax : ∀ y ∈ V, y ∉ U → S.rank y ≤ S.rank m) : S.Vert (V.erase m) := by
  obtain ⟨hcl, s, c, hpre, hcli⟩ := hV
  obtain ⟨hclU, s0, c0, hpre0, hcli0⟩ := hU
  have hgt : ∀ y ∈ V, y ≠ m → S.rank m ≤ S.rank y → y ∈ U := by
    intro y hy hym hle
    by_contra hyU
    have := hmax y hy hyU
    exact hym (hW.inj (hVD hy) (hVD hm) (by omega))
  refine ⟨?_, min s (S.rank m), if s ≤ S.rank m then c else c0, ?_, ?_⟩
  · intro x hx y hy
    have hxV := Finset.mem_of_mem_erase hx
    refine Finset.mem_erase.2 ⟨?_, hcl x hxV hy⟩
    rintro rfl
    have hlt := hW.ctx_lt x (hVD hxV) _ hy
    have hxU := hgt x hxV (Finset.ne_of_mem_erase hx) (by omega)
    exact hmU (hclU x hxU hy)
  · intro x hx
    refine Finset.mem_erase.2 ⟨?_, hpre x (by omega)⟩
    rintro rfl; omega
  · intro x hx hle
    have hxV := Finset.mem_of_mem_erase hx
    split_ifs with h
    · exact hcli x hxV (by omega)
    · have hm0 : s0 ≤ S.rank m := by
        by_contra h'; exact hmU (hpre0 m (by omega))
      have hxm : S.rank m ≤ S.rank x := by omega
      have hxU := hgt x hxV (Finset.ne_of_mem_erase hx) hxm
      exact hcli0 x hxU (by omega)

/-- Vertices are closed under intersection (the LCA of Lemma 23 is the intersection). -/
theorem Vert.inter {V₁ V₂ : Finset ι} (h₁ : S.Vert V₁) (h₂ : S.Vert V₂) : S.Vert (V₁ ∩ V₂) := by
  obtain ⟨hc1, s1, c1, hp1, hl1⟩ := h₁
  obtain ⟨hc2, s2, c2, hp2, hl2⟩ := h₂
  refine ⟨fun x hx => Finset.subset_inter (hc1 x (Finset.mem_inter.1 hx).1)
    (hc2 x (Finset.mem_inter.1 hx).2), min s1 s2, if s1 ≤ s2 then c1 else c2, ?_, ?_⟩
  · intro x hx; exact Finset.mem_inter.2 ⟨hp1 x (by omega), hp2 x (by omega)⟩
  · intro x hx hle
    have := Finset.mem_inter.1 hx
    split_ifs with h
    · exact hl1 x this.1 (by omega)
    · exact hl2 x this.2 (by omega)

/-- General criterion: removing `m` from a vertex gives a vertex if no other element depends
on `m` and all elements `≺s`-after `m` belong to one client. -/
theorem Vert.erase_of {V : Finset ι} (hV : S.Vert V) {m : ι}
    (h1 : ∀ y ∈ V, y ≠ m → m ∉ S.ctx y)
    (h2 : ∃ c', ∀ y ∈ V, y ≠ m → S.rank m ≤ S.rank y → S.cl y = c') : S.Vert (V.erase m) := by
  obtain ⟨hcl, s, c, hpre, hcli⟩ := hV
  obtain ⟨c', hc'⟩ := h2
  refine ⟨?_, min s (S.rank m), if s ≤ S.rank m then c else c', ?_, ?_⟩
  · intro x hx y hy
    have hxV := Finset.mem_of_mem_erase hx
    refine Finset.mem_erase.2 ⟨?_, hcl x hxV hy⟩
    rintro rfl
    exact h1 x hxV (Finset.ne_of_mem_erase hx) hy
  · intro x hx
    refine Finset.mem_erase.2 ⟨?_, hpre x (by omega)⟩
    rintro rfl; omega
  · intro x hx hle
    have hxV := Finset.mem_of_mem_erase hx
    split_ifs with h
    · exact hcli x hxV (by omega)
    · exact hc' x hxV (Finset.ne_of_mem_erase hx) (by omega)

/-- `a` is alive in `V`: inserted by an operation of `V` and deleted by none. -/
def Alive (V : Finset ι) (a : ι) : Prop :=
  a ∈ V ∧ (∃ p pr, S.orig a = .ins a p pr) ∧ ∀ y ∈ V, ∀ p, S.orig y ≠ .del a p

/-- Statement A of the main induction: lists of vertices are duplicate-free and contain exactly
the alive elements. -/
def StA (D : Set ι) (n : ℕ) : Prop :=
  ∀ V : Finset ι, V.card ≤ n → S.Vert V → ↑V ⊆ D →
    (S.L V).Nodup ∧ ∀ a, a ∈ S.L V ↔ S.Alive V a

/-- Statement B of the main induction: edge consistency. -/
def StB (D : Set ι) (n : ℕ) : Prop :=
  ∀ (V : Finset ι) (x : ι), (insert x V).card ≤ n → x ∉ V → S.Vert V → S.Vert (insert x V) →
    ↑(insert x V) ⊆ D →
    S.L (insert x V) = (S.T x V).apply (S.L V) ∧ Real (S.orig x) (S.T x V) (S.L V)

theorem StA.mono {n m : ℕ} (h : S.StA D n) (hmn : m ≤ n) : S.StA D m :=
  fun V hV => h V (le_trans hV hmn)

theorem StB.mono {n m : ℕ} (h : S.StB D n) (hmn : m ≤ n) : S.StB D m :=
  fun V x hV => h V x (le_trans hV hmn)

/-- The element deleted by an original deletion belongs to its context. -/
theorem del_mem_ctx (hW : S.WF D) {n : ℕ} (hA : S.StA D n) {y a : ι} {p : ℕ} (hy : y ∈ D)
    (hn : (S.ctx y).card ≤ n) (hdel : S.orig y = .del a p) : a ∈ S.ctx y := by
  have h := hW.orig y hy
  rw [hdel] at h
  obtain ⟨-, h⟩ := h
  have ha : a ∈ S.L (S.ctx y) := List.mem_of_getElem? h
  exact ((hA _ hn (hW.vert_ctx hy) (hW.ctx_sub y hy)).2 a |>.1 ha).1

/-- Concurrent operations are independent. -/
theorem indep (hW : S.WF D) {n : ℕ} (hA : S.StA D n) {x y : ι} (hx : x ∈ D) (hy : y ∈ D)
    (hxy : x ≠ y) (h1 : x ∉ S.ctx y) (h2 : y ∉ S.ctx x) (hnx : (S.ctx x).card ≤ n)
    (hny : (S.ctx y).card ≤ n) : Indep (S.orig x) (S.orig y) := by
  have okx := hW.origOk x hx
  have oky := hW.origOk y hy
  have hcl : S.cl x ≠ S.cl y := by
    intro hc
    rcases lt_trichotomy (S.rank x) (S.rank y) with h | h | h
    · exact h1 (hW.own y hy x hx hc h)
    · exact hxy (hW.inj hx hy h)
    · exact h2 (hW.own x hx y hy hc.symm h)
  unfold OrigOk at okx oky
  cases hox : S.orig x <;> cases hoy : S.orig y <;> simp only [hox, hoy] at okx oky <;>
    simp only [Indep]
  · obtain ⟨rfl, rfl⟩ := okx; obtain ⟨rfl, rfl⟩ := oky; exact ⟨hxy, hcl⟩
  · obtain ⟨rfl, -⟩ := okx
    rintro rfl
    exact h1 (del_mem_ctx hW hA hy hny hoy)
  · obtain ⟨rfl, -⟩ := oky
    rintro rfl
    exact h2 (del_mem_ctx hW hA hx hnx hox)

theorem card_ctx_lt (hW : S.WF D) {V : Finset ι} (hV : S.Closed V) {y : ι} (hy : y ∈ V)
    (hyD : y ∈ D) : (S.ctx y).card < V.card := by
  apply Finset.card_lt_card
  refine ⟨hV y hy, fun h => ?_⟩
  have := hW.ctx_lt y hyD y (h hy)
  omega

/-- Inductive step for B. -/
theorem stB_succ (hW : S.WF D) {n : ℕ} (hA : S.StA D n) (hB : S.StB D n) : S.StB D (n + 1) := by
  intro V x hcard hxV hV hVx hD
  have hxD : x ∈ D := hD (Finset.mem_insert_self x V)
  have hVD : ↑V ⊆ D := fun y hy => hD (Finset.mem_insert_of_mem hy)
  have hcardV : V.card ≤ n := by rw [Finset.card_insert_of_notMem hxV] at hcard; omega
  have hctxV : S.ctx x ⊆ V := by
    intro y hy
    rcases Finset.mem_insert.1 (hVx.1 x (Finset.mem_insert_self x V) hy) with rfl | h
    · have := hW.ctx_lt _ hxD _ hy; omega
    · exact h
  by_cases htop : ∀ y ∈ V, S.rank y < S.rank x
  · -- `x` is the `≺s`-last operation
    refine ⟨S.L_insert hxV htop, ?_⟩
    by_cases hsub : V ⊆ S.ctx x
    · have hVeq : V = S.ctx x := le_antisymm hsub hctxV
      rw [S.T_of_subset hsub, hVeq]
      exact hW.orig x hxD
    · obtain ⟨l0, hl0V, hl0x⟩ := Finset.not_subset.1 hsub
      have hne : (V \ S.ctx x).Nonempty := ⟨l0, Finset.mem_sdiff.2 ⟨hl0V, hl0x⟩⟩
      obtain ⟨l, hl, hlmax⟩ := (V \ S.ctx x).exists_max_image S.rank hne
      obtain ⟨hlV, hlx⟩ := Finset.mem_sdiff.1 hl
      set V' := V.erase l with hV'
      have hlV' : l ∉ V' := Finset.notMem_erase l V
      have hVins : insert l V' = V := Finset.insert_erase hlV
      have hlD : l ∈ D := hVD hlV
      have hmax' : ∀ y ∈ V', y ∉ S.ctx x → S.rank y < S.rank l := by
        intro y hy hyx
        have hyV := Finset.mem_of_mem_erase hy
        have := hlmax y (Finset.mem_sdiff.2 ⟨hyV, hyx⟩)
        rcases this.lt_or_eq with h | h
        · exact h
        · exact absurd (hW.inj (hVD hyV) hlD h) (Finset.ne_of_mem_erase hy)
      have hT : S.T x V = xf (S.T x V') (S.T l V') := by
        rw [← hVins]; exact S.T_insert hlV' hlx hmax'
      -- `y ∈ V` after `l` are in `ctx x`
      have hafter : ∀ y ∈ V, y ≠ l → S.rank l ≤ S.rank y → y ∈ S.ctx x := by
        intro y hy hyl hle
        by_contra hyx
        have := hlmax y (Finset.mem_sdiff.2 ⟨hy, hyx⟩)
        exact hyl (hW.inj (hVD hy) hlD (by omega))
      have hV'v : S.Vert V' :=
        Vert.erase_top_sdiff hW (hW.vert_ctx hxD) hV hVD hctxV hlV hlx
          (fun y hy hyx => hlmax y (Finset.mem_sdiff.2 ⟨hy, hyx⟩))
      have hxV' : x ∉ V' := fun h => hxV (Finset.mem_of_mem_erase h)
      have hVx' : S.Vert (insert x V') := by
        have hxl : x ≠ l := fun h => hxV (h ▸ hlV)
        have : insert x V' = (insert x V).erase l := by
          rw [hV', Finset.erase_insert_of_ne hxl]
        rw [this]
        apply Vert.erase_of hVx
        · intro y hy hyl hly
          rcases Finset.mem_insert.1 hy with rfl | hy
          · exact hlx hly
          · have hlt := hW.ctx_lt y (hVD hy) l hly
            exact hlx (hW.trans x hxD y (hafter y hy hyl (by omega)) hly)
        · refine ⟨S.cl x, fun y hy hyl hle => ?_⟩
          rcases Finset.mem_insert.1 hy with rfl | hy
          · rfl
          · by_contra hc
            exact hlx (hW.pref x hxD y (hafter y hy hyl hle) hc l hle)
      have hcV : (insert x V').card ≤ n := by
        rw [Finset.card_insert_of_notMem hxV']
        have : V'.card = V.card - 1 := Finset.card_erase_of_mem hlV
        have := Finset.card_pos.2 ⟨l, hlV⟩
        omega
      have hcV2 : (insert l V').card ≤ n := by rw [hVins]; exact hcardV
      have hV'D : ↑V' ⊆ D := fun y hy => hVD (Finset.mem_of_mem_erase hy)
      obtain ⟨-, hRx⟩ := hB V' x hcV hxV' hV'v hVx' (by
        intro y hy; rcases Finset.mem_insert.1 hy with rfl | hy
        · exact hxD
        · exact hV'D hy)
      obtain ⟨hLl, hRl⟩ := hB V' l hcV2 hlV' hV'v (hVins ▸ hV) (hVins ▸ hVD)
      have hnd : (S.L V').Nodup :=
        (hA V' (by have : V'.card = V.card - 1 := Finset.card_erase_of_mem hlV; omega) hV'v hV'D).1
      have hind := indep hW hA hxD hlD (fun h => hxV (h ▸ hlV))
        (fun h => by have := hW.ctx_lt l hlD x h; have := htop l hlV; omega) hlx
        (by have := card_ctx_lt hW hVx.1 (Finset.mem_insert_self x V) hxD
            rw [Finset.card_insert_of_notMem hxV] at this; omega)
        (by have := card_ctx_lt hW hV.1 hlV hlD; omega)
      rw [hT, ← hVins, hLl]
      exact (square hnd hRx hRl hind).2
  · -- some `m ∈ V` is `≺s`-last
    push_neg at htop
    obtain ⟨m0, hm0V, hm0⟩ := htop
    have hVne : V.Nonempty := ⟨m0, hm0V⟩
    obtain ⟨m, hmV, hmmax⟩ := V.exists_max_image S.rank hVne
    have hmD : m ∈ D := hVD hmV
    have hxm : S.rank x < S.rank m := by
      have := hmmax m0 hm0V
      rcases (le_trans hm0 this).lt_or_eq with h | h
      · exact h
      · exact absurd (hW.inj hxD hmD h ▸ hmV) hxV
    have hmx : m ≠ x := fun h => hxV (h ▸ hmV)
    set W := V.erase m with hWdef
    have hmW : m ∉ W := Finset.notMem_erase m V
    have hxW : x ∉ W := fun h => hxV (Finset.mem_of_mem_erase h)
    have hVW : insert m W = V := Finset.insert_erase hmV
    have hWD : ↑W ⊆ D := fun y hy => hVD (Finset.mem_of_mem_erase hy)
    have hltm : ∀ y ∈ V, y ≠ m → S.rank y < S.rank m := by
      intro y hy hym
      rcases (hmmax y hy).lt_or_eq with h | h
      · exact h
      · exact absurd (hW.inj (hVD hy) hmD h) hym
    have hWv : S.Vert W := Vert.erase_top hW hV hVD hmV hmmax
    have hxWeq : insert x W = (insert x V).erase m := by
      rw [hWdef, Finset.erase_insert_of_ne hmx.symm]
    have hxWv : S.Vert (insert x W) := by
      rw [hxWeq]
      apply Vert.erase_top hW hVx hD (Finset.mem_insert_of_mem hmV)
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hxm.le
      · exact hmmax y hy
    have hxWD : ↑(insert x W) ⊆ D := by
      intro y hy; rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hxD
      · exact hWD hy
    have hcW : (insert x W).card ≤ n := by
      rw [Finset.card_insert_of_notMem hxW, hWdef, Finset.card_erase_of_mem hmV]
      have := Finset.card_pos.2 hVne; omega
    have hcW2 : (insert m W).card ≤ n := by rw [hVW]; exact hcardV
    obtain ⟨hLx, hRx⟩ := hB W x hcW hxW hWv hxWv hxWD
    obtain ⟨hLm, hRm⟩ := hB W m hcW2 hmW hWv (hVW ▸ hV) (hVW ▸ hVD)
    have hmctx : m ∉ S.ctx x := fun h => by have := hW.ctx_lt x hxD m h; omega
    have hxctx : x ∉ S.ctx m := fun h => hxV (hV.1 m hmV h)
    -- the operations of `W` after `x` are in `ctx m`
    have hafter : ∀ y ∈ W, y ∉ S.ctx m → S.rank y < S.rank x := by
      intro y hy hyc
      by_contra hle
      push_neg at hle
      obtain ⟨-, s, c, hpre, hcli⟩ := hV
      have hyV := Finset.mem_of_mem_erase hy
      have hsx : s ≤ S.rank x := by
        by_contra h; exact hxV (hpre x (by omega))
      have hyx : y ≠ x := fun h => hxW (h ▸ hy)
      have hyx' : S.rank x < S.rank y := by
        rcases hle.lt_or_eq with h | h
        · exact h
        · exact absurd (hW.inj hxD (hVD hyV) h).symm hyx
      have := hcli y hyV (by omega)
      have := hcli m hmV (by omega)
      exact hyc (hW.own m hmD y (hVD hyV) (by simp_all)
        (hltm y hyV (Finset.ne_of_mem_erase hy)))
    have hT1 : S.T m (insert x W) = xf (S.T m W) (S.T x W) := S.T_insert hxW hxctx hafter
    have hT2 : S.T x V = xf (S.T x W) (S.T m W) := by
      rw [← hVW]
      exact S.T_insert hmW hmctx (fun y hy _ => hltm y (Finset.mem_of_mem_erase hy)
        (Finset.ne_of_mem_erase hy))
    have hins : insert x V = insert m (insert x W) := by
      rw [← hVW, Finset.insert_comm]
    have hL1 : S.L (insert x V) = (S.T m (insert x W)).apply (S.L (insert x W)) := by
      rw [hins]
      apply S.L_insert (by simp [hmx, hmW])
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hxm
      · exact hltm y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy)
    have hnd : (S.L W).Nodup := (hA W (by
      rw [hWdef, Finset.card_erase_of_mem hmV]; omega) hWv hWD).1
    have hind := indep hW hA hxD hmD hmx.symm hxctx hmctx
      (by have := card_ctx_lt hW hVx.1 (Finset.mem_insert_self x V) hxD
          rw [Finset.card_insert_of_notMem hxV] at this; omega)
      (by have := card_ctx_lt hW hV.1 hmV hmD; omega)
    have hsq := square hnd hRx hRm hind
    have hLV : S.L V = (S.T m W).apply (S.L W) := hVW ▸ hLm
    refine ⟨?_, ?_⟩
    · rw [hL1, hT1, hLx, hT2, hLV]; exact hsq.1.symm
    · rw [hT2, hLV]; exact hsq.2

/-- Inductive step for A. -/
theorem stA_succ (hW : S.WF D) {n : ℕ} (hA : S.StA D n) (hB : S.StB D (n + 1)) :
    S.StA D (n + 1) := by
  intro V hcard hV hVD
  rcases V.eq_empty_or_nonempty with rfl | hne
  · simp [L_empty, Alive]
  obtain ⟨m, hmV, hmmax⟩ := V.exists_max_image S.rank hne
  have hmD := hVD hmV
  set W := V.erase m with hWdef
  have hmW : m ∉ W := Finset.notMem_erase m V
  have hVW : insert m W = V := Finset.insert_erase hmV
  have hWD : ↑W ⊆ D := fun y hy => hVD (Finset.mem_of_mem_erase hy)
  have hWv : S.Vert W := Vert.erase_top hW hV hVD hmV hmmax
  have hcW : W.card ≤ n := by
    rw [hWdef, Finset.card_erase_of_mem hmV]; omega
  obtain ⟨hL, hR⟩ := hB W m (by rw [hVW]; exact hcard) hmW hWv (hVW ▸ hV) (hVW ▸ hVD)
  obtain ⟨hndW, hmemW⟩ := hA W hcW hWv hWD
  rw [hVW] at hL
  refine ⟨hL ▸ hR.nodup hndW, fun a => ?_⟩
  -- no operation of `W` deletes `m`
  have hnodel : ∀ y ∈ W, ∀ p, S.orig y ≠ .del m p := by
    intro y hy p hdel
    have hyV := Finset.mem_of_mem_erase hy
    have hc := card_ctx_lt hW hV.1 hyV (hVD hyV)
    have hmc := del_mem_ctx hW hA (hVD hyV) (by omega) hdel
    have := hW.ctx_lt y (hVD hyV) m hmc
    have := hmmax y hyV
    omega
  rw [hL, ← hVW]
  have okm := hW.origOk m hmD
  unfold OrigOk at okm
  cases hom : S.orig m with
  | ins a' p pr =>
    rw [hom] at hR okm
    obtain ⟨rfl, -⟩ := okm
    rw [hR.mem_ins, hmemW]
    constructor
    · rintro (⟨haW, hins, hdel⟩ | rfl)
      · refine ⟨Finset.mem_insert_of_mem haW, hins, fun y hy q => ?_⟩
        rcases Finset.mem_insert.1 hy with rfl | hy
        · rw [hom]; simp
        · exact hdel y hy q
      · refine ⟨Finset.mem_insert_self _ _, ⟨p, pr, hom⟩, fun y hy q => ?_⟩
        rcases Finset.mem_insert.1 hy with rfl | hy
        · rw [hom]; simp
        · exact hnodel y hy q
    · rintro ⟨ha, hins, hdel⟩
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact Or.inr rfl
      · exact Or.inl ⟨ha, hins, fun y hy q => hdel y (Finset.mem_insert_of_mem hy) q⟩
  | del a' p =>
    rw [hom] at hR
    rw [hR.mem_del hndW, hmemW]
    constructor
    · rintro ⟨⟨haW, hins, hdel⟩, hne⟩
      refine ⟨Finset.mem_insert_of_mem haW, hins, fun y hy q => ?_⟩
      rcases Finset.mem_insert.1 hy with rfl | hy
      · rw [hom]; simp [Ne.symm hne]
      · exact hdel y hy q
    · rintro ⟨ha, hins, hdel⟩
      have ham : a ≠ m := by
        rintro rfl; obtain ⟨_, _, h⟩ := hins; rw [hom] at h; simp at h
      refine ⟨⟨(Finset.mem_insert.1 ha).resolve_left ham, hins,
        fun y hy q => hdel y (Finset.mem_insert_of_mem hy) q⟩, ?_⟩
      rintro rfl
      exact hdel m (Finset.mem_insert_self _ _) p hom
  | nop =>
    rw [hom] at hR
    rw [hR.mem_nop, hmemW]
    constructor
    · rintro ⟨haW, hins, hdel⟩
      refine ⟨Finset.mem_insert_of_mem haW, hins, fun y hy q => ?_⟩
      rcases Finset.mem_insert.1 hy with rfl | hy
      · rw [hom]; simp
      · exact hdel y hy q
    · rintro ⟨ha, hins, hdel⟩
      have ham : a ≠ m := by
        rintro rfl; obtain ⟨_, _, h⟩ := hins; rw [hom] at h; simp at h
      exact ⟨(Finset.mem_insert.1 ha).resolve_left ham, hins,
        fun y hy q => hdel y (Finset.mem_insert_of_mem hy) q⟩

theorem stAB (hW : S.WF D) : ∀ n, S.StA D n ∧ S.StB D n
  | 0 => by
    refine ⟨fun V hV _ _ => ?_, fun V x hc => ?_⟩
    · rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hV)]; simp [L_empty, Alive]
    · have := Finset.card_pos.2 (Finset.insert_nonempty x V); omega
  | n + 1 => by
    obtain ⟨hA, hB⟩ := stAB hW n
    have hB' := stB_succ hW hA hB
    exact ⟨stA_succ hW hA hB', hB'⟩

/-- **Edge consistency** (Proposition 9 / Theorem 11): along every edge `V → V ∪ {x}` between
vertices of the global state space, the list evolves by applying `T x V`, a valid form of `x`. -/
theorem edge (hW : S.WF D) {V : Finset ι} {x : ι} (hxV : x ∉ V) (hV : S.Vert V)
    (hVx : S.Vert (insert x V)) (hD : ↑(insert x V) ⊆ D) :
    S.L (insert x V) = (S.T x V).apply (S.L V) ∧ Real (S.orig x) (S.T x V) (S.L V) :=
  (stAB hW _).2 V x le_rfl hxV hV hVx hD

theorem L_nodup (hW : S.WF D) {V : Finset ι} (hV : S.Vert V) (hVD : ↑V ⊆ D) : (S.L V).Nodup :=
  ((stAB hW _).1 V le_rfl hV hVD).1

/-- The list of a vertex consists of its alive elements (condition 1(a) of `A_weak`). -/
theorem mem_L (hW : S.WF D) {V : Finset ι} (hV : S.Vert V) (hVD : ↑V ⊆ D) (a : ι) :
    a ∈ S.L V ↔ S.Alive V a :=
  ((stAB hW _).1 V le_rfl hV hVD).2 a

/-- Order preservation along paths (Lemma 25): if `U ⊆ V` are vertices, two elements of the list
of `U` that are still in the list of `V` keep their relative order. -/
theorem sublist_of_subset (hW : S.WF D) {U V : Finset ι} (hU : S.Vert U) (hV : S.Vert V)
    (hVD : ↑V ⊆ D) (hUV : U ⊆ V) {a b : ι} (ha : a ∈ S.L U) (hb : b ∈ S.L U)
    (hab : [a, b].Sublist (S.L V)) : [a, b].Sublist (S.L U) := by
  induction hk : (V \ U).card generalizing V with
  | zero =>
    have : V = U := le_antisymm (Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 hk))
      hUV
    exact this ▸ hab
  | succ k ih =>
    have hne : (V \ U).Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨m, hm, hmmax⟩ := (V \ U).exists_max_image S.rank hne
    obtain ⟨hmV, hmU⟩ := Finset.mem_sdiff.1 hm
    set W := V.erase m with hWdef
    have hmW : m ∉ W := Finset.notMem_erase m V
    have hVW : insert m W = V := Finset.insert_erase hmV
    have hWD : ↑W ⊆ D := fun y hy => hVD (Finset.mem_of_mem_erase hy)
    have hWv : S.Vert W := Vert.erase_top_sdiff hW hU hV hVD hUV hmV hmU
      (fun y hy hyU => hmmax y (Finset.mem_sdiff.2 ⟨hy, hyU⟩))
    have hUW : U ⊆ W := fun y hy => Finset.mem_erase.2 ⟨fun h => hmU (h ▸ hy), hUV hy⟩
    obtain ⟨hL, hR⟩ := edge hW hmW hWv (hVW ▸ hV) (hVW ▸ hVD)
    rw [hVW] at hL
    have hndW := L_nodup hW hWv hWD
    have hinW : ∀ c ∈ S.L U, c ∈ S.L V → c ∈ S.L W := by
      intro c hcU hcV
      obtain ⟨hcU', hins, -⟩ := (mem_L hW hU (fun y hy => hVD (hUV hy)) c).1 hcU
      obtain ⟨-, -, hdel⟩ := (mem_L hW hV hVD c).1 hcV
      exact (mem_L hW hWv hWD c).2 ⟨hUW hcU', hins,
        fun y hy q => hdel y (Finset.mem_of_mem_erase hy) q⟩
    have haW := hinW a ha (hab.subset (by simp))
    have hbW := hinW b hb (hab.subset (by simp))
    rw [hL] at hab
    have habW := hR.sublist hndW haW hbW hab
    refine ih hWv hWD hUW habW ?_
    rw [hWdef, Finset.erase_sdiff_comm, Finset.card_erase_of_mem hm]; omega

/-- State compatibility (Definition 20): no two elements appear in opposite orders. -/
def Compatible (l₁ l₂ : List ι) : Prop := ∀ a b, [a, b].Sublist l₁ → [b, a].Sublist l₂ → False

theorem not_both_orders {l : List ι} (hl : l.Nodup) {a b : ι} (h₁ : [a, b].Sublist l)
    (h₂ : [b, a].Sublist l) : False := by
  induction l with
  | nil => simp at h₁
  | cons c t ih =>
    rw [List.nodup_cons] at hl
    rw [List.sublist_cons_iff] at h₁ h₂
    rcases h₁ with h₁ | ⟨r, hr, h₁⟩ <;> rcases h₂ with h₂ | ⟨r', hr', h₂⟩
    · exact ih hl.2 h₁ h₂
    · simp only [List.cons.injEq] at hr'; obtain ⟨rfl, rfl⟩ := hr'
      exact hl.1 (h₁.subset (by simp))
    · simp only [List.cons.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
      exact hl.1 (h₂.subset (by simp))
    · simp only [List.cons.injEq] at hr hr'; obtain ⟨rfl, rfl⟩ := hr; obtain ⟨rfl, rfl⟩ := hr'
      exact hl.1 (h₁.subset (by simp))

/-- **Theorem 26 (pairwise state compatibility)**: the lists of any two vertices of the global
state space are compatible. -/
theorem compatible (hW : S.WF D) {V₁ V₂ : Finset ι} (h₁ : S.Vert V₁) (h₂ : S.Vert V₂)
    (hD₁ : ↑V₁ ⊆ D) (hD₂ : ↑V₂ ⊆ D) : Compatible (S.L V₁) (S.L V₂) := by
  intro a b hab hba
  have h₀ := h₁.inter h₂
  have hD₀ : ↑(V₁ ∩ V₂) ⊆ D := fun y hy => hD₁ (Finset.mem_inter.1 hy).1
  have hin : ∀ c, c ∈ S.L V₁ → c ∈ S.L V₂ → c ∈ S.L (V₁ ∩ V₂) := by
    intro c hc1 hc2
    obtain ⟨hc1, hins, hdel⟩ := (mem_L hW h₁ hD₁ c).1 hc1
    obtain ⟨hc2, -, -⟩ := (mem_L hW h₂ hD₂ c).1 hc2
    exact (mem_L hW h₀ hD₀ c).2 ⟨Finset.mem_inter.2 ⟨hc1, hc2⟩, hins,
      fun y hy q => hdel y (Finset.mem_inter.1 hy).1 q⟩
  have ha := hin a (hab.subset (by simp)) (hba.subset (by simp))
  have hb := hin b (hab.subset (by simp)) (hba.subset (by simp))
  exact not_both_orders (L_nodup hW h₀ hD₀)
    (sublist_of_subset hW h₀ h₁ hD₁ Finset.inter_subset_left ha hb hab)
    (sublist_of_subset hW h₀ h₂ hD₂ Finset.inter_subset_right hb ha hba)

end Sched

end Podc.JupiterListSpec
