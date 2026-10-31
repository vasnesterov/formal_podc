import Papers.PODC2015.RandomizedPLS.LowerBound

/-!
# Tools for the lower bounds of Section 5

* `mkConfig`: a port-numbered configuration (states = identities in `ℕ`) from a symmetric
  irreflexive relation; the neighbours in `front v` come first, at ports `0, 1, …` (this is how we
  realise "port numbers consistently ordered").
* `edgeCopies`: `r` copies of a single edge (`s = 1`), the patterns used throughout Section 5.
* `Copies.cross_adj_iff`: adjacency in the crossing `σ₁(G)`.
* Generic graph lemmas: `connected_of_descent` (connectivity from a descending neighbour),
  `not_reachable_of_closed`, `exists_cycle_of_seq` (a cycle from a cyclic sequence of distinct
  vertices), `cycle_support_of_cut` (a simple cycle through a cut vertex `z` stays in `z` plus one
  component of `G - z`) and `support_eq_of_edges` (a walk whose edges keep a block function
  constant stays in one block).
-/

namespace Podc.RandomizedPLS

open Classical

/-! ### Configurations from an adjacency relation -/

section mkConfig

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A configuration on `V` from a symmetric irreflexive relation `A`, with identities `st`. The
neighbours listed in `front v` occupy ports `0, 1, …` of `v`; the other neighbours follow. -/
@[reducible] noncomputable def mkConfig (A : V → V → Prop) (hsymm : ∀ v w, A v w → A w v)
    (hirr : ∀ v, ¬ A v v) (front : V → List V) (hfront : ∀ v, ∀ w ∈ front v, A v w)
    (hnd : ∀ v, (front v).Nodup) (st : V → ℕ) : Config ℕ where
  V := V
  nbrs v := front v ++ (Finset.univ.filter fun w => A v w ∧ w ∉ front v).toList
  nodup v := by
    refine List.nodup_append.2 ⟨hnd v, Finset.nodup_toList _, ?_⟩
    intro a ha b hb hab
    subst hab
    simp only [Finset.mem_toList, Finset.mem_filter] at hb
    exact hb.2.2 ha
  loopless v h := by
    rcases List.mem_append.1 h with h | h
    · exact hirr v (hfront v v h)
    · simp only [Finset.mem_toList, Finset.mem_filter] at h
      exact hirr v h.2.1
  symm v w h := by
    have hA : A v w := by
      rcases List.mem_append.1 h with h | h
      · exact hfront v w h
      · simp only [Finset.mem_toList, Finset.mem_filter] at h
        exact h.2.1
    by_cases hw : v ∈ front w
    · exact List.mem_append.2 (Or.inl hw)
    · exact List.mem_append.2 (Or.inr (by simp [hsymm v w hA, hw]))
  state := st

variable {A : V → V → Prop} {hsymm : ∀ v w, A v w → A w v} {hirr : ∀ v, ¬ A v v}
  {front : V → List V} {hfront : ∀ v, ∀ w ∈ front v, A v w} {hnd : ∀ v, (front v).Nodup}
  {st : V → ℕ}

lemma mkConfig_adj (v w : V) :
    (mkConfig A hsymm hirr front hfront hnd st).graph.Adj v w ↔ A v w := by
  change w ∈ front v ++ _ ↔ _
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact hfront v w h
    · simp only [Finset.mem_toList, Finset.mem_filter] at h
      exact h.2.1
  · intro h
    by_cases hw : w ∈ front v
    · exact List.mem_append.2 (Or.inl hw)
    · exact List.mem_append.2 (Or.inr (by simp [h, hw]))

lemma mkConfig_port {v w : V} (hw : w ∈ front v) :
    (mkConfig A hsymm hirr front hfront hnd st).port v w = (front v).idxOf w :=
  List.idxOf_append_of_mem hw

end mkConfig

/-! ### Copies of a single edge -/

section edgeCopies

variable {S : Type} (c : Config S) (r : ℕ)

/-- `r` pairwise independent, port-preserving copies of a single edge `e i false — e i true`. -/
@[reducible] noncomputable def edgeCopies (e : Fin r → Bool → c.V)
    (inj : ∀ i, e i false ≠ e i true) (disj : ∀ i j a b, i ≠ j → e i a ≠ e j b)
    (indep : ∀ i j a b, i ≠ j → ¬ c.Adj (e i a) (e j b)) (hom : ∀ i, c.Adj (e i false) (e i true))
    (port_eq : ∀ i j b, c.port (e i b) (e i !b) = c.port (e j b) (e j !b)) : Copies c r where
  W := Bool
  H := ⊤
  emb := e
  inj i a b h := by
    by_contra hab
    cases a <;> cases b <;> simp_all [eq_comm]
  disj := disj
  indep := indep
  hom i a b h := by
    cases a <;> cases b <;> simp at h
    · exact hom i
    · exact c.symm _ _ (hom i)
  port_eq i j a b h := by
    have : b = !a := by cases a <;> cases b <;> simp_all
    subst this
    exact port_eq i j a

variable {c r} {e : Fin r → Bool → c.V} {inj : ∀ i, e i false ≠ e i true}
  {disj : ∀ i j a b, i ≠ j → e i a ≠ e j b} {indep : ∀ i j a b, i ≠ j → ¬ c.Adj (e i a) (e j b)}
  {hom : ∀ i, c.Adj (e i false) (e i true)}
  {port_eq : ∀ i j b, c.port (e i b) (e i !b) = c.port (e j b) (e j !b)}

lemma edgeCopies_s : (edgeCopies c r e inj disj indep hom port_eq).s = 1 := by
  unfold Copies.s; rw [Finset.card_eq_one]
  exact ⟨s(false, true), by
    ext e; induction e using Sym2.ind with | _ x y => (cases x <;> cases y <;> simp)⟩

lemma edgeCopies_isArc {i j : Fin r} {x w : c.V} :
    (edgeCopies c r e inj disj indep hom port_eq).IsArc i j x w ↔
      ∃ k, (k = i ∨ k = j) ∧ ∃ b, e k b = x ∧ e k (!b) = w := by
  constructor
  · rintro ⟨k, hk, a, b, hab, hx, hw⟩
    have : b = !a := by cases a <;> cases b <;> simp_all
    subst this
    exact ⟨k, hk, a, hx, hw⟩
  · rintro ⟨k, hk, b, hx, hw⟩
    exact ⟨k, hk, b, !b, by cases b <;> simp, hx, hw⟩

end edgeCopies

/-! ### Adjacency in a crossing -/

namespace Copies

variable {S : Type} {c : Config S} {r : ℕ} (K : Copies c r)

lemma swap_swap {i j : Fin r} (hij : i ≠ j) (v : c.V) : K.swap i j (K.swap i j v) = v := by
  by_cases hi : ∃ a, K.emb i a = v
  · obtain ⟨a, rfl⟩ := hi
    rw [K.swap_emb_left, K.swap_emb_right hij]
  · by_cases hj : ∃ a, K.emb j a = v
    · obtain ⟨a, rfl⟩ := hj
      rw [K.swap_emb_right hij, K.swap_emb_left]
    · push Not at hi hj
      rw [K.swap_of_not_mem hi hj, K.swap_of_not_mem hi hj]

/-- Adjacency in the crossing: the edges of `G` that are not crossed, and the crossed edges
`{x, σ w}` for every arc `(x, w)` of the two copies. -/
lemma cross_adj_iff {i j : Fin r} (hij : i ≠ j) (x y : c.V) :
    (K.cross i j hij).graph.Adj x y ↔
      (c.graph.Adj x y ∧ ¬ K.IsArc i j x y) ∨ K.IsArc i j x (K.swap i j y) := by
  change y ∈ (c.nbrs x).map (K.newNbr i j x) ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    by_cases ha : K.IsArc i j x w
    · right
      rw [newNbr, ite_eq_left ha, K.swap_swap hij]
      exact ha
    · left
      rw [newNbr, ite_eq_right ha]
      exact ⟨hw, ha⟩
  · rintro (⟨h, ha⟩ | ha)
    · exact ⟨y, h, by rw [newNbr, ite_eq_right ha]⟩
    · exact ⟨K.swap i j y, K.adj_of_isArc ha, by rw [newNbr, ite_eq_left ha, K.swap_swap hij]⟩

end Copies

/-! ### Generic graph lemmas -/

section graph

variable {V : Type} {G : SimpleGraph V}

-- CSLib candidate
/-- If every vertex but `root` has a neighbour with a smaller potential, the graph is connected. -/
lemma connected_of_descent {α : Type} [LT α] [WellFoundedLT α] (root : V) (φ : V → α)
    (h : ∀ x, x ≠ root → ∃ y, G.Adj x y ∧ φ y < φ x) : G.Connected := by
  have key : ∀ a, ∀ x, φ x = a → G.Reachable x root := by
    intro a
    induction a using WellFoundedLT.induction with
    | _ a ih =>
      intro x hx
      by_cases hr : x = root
      · subst hr; rfl
      · obtain ⟨y, hxy, hy⟩ := h x hr
        exact hxy.reachable.trans (ih _ (hx ▸ hy) y rfl)
  have : Nonempty V := ⟨root⟩
  exact (SimpleGraph.connected_iff G).2
    ⟨fun u v => (key _ u rfl).trans (key _ v rfl).symm, inferInstance⟩

-- CSLib candidate
/-- A set closed under adjacency contains everything reachable from it. -/
lemma mem_of_reachable_of_closed (U : Set V) (hU : ∀ x y, G.Adj x y → x ∈ U → y ∈ U) {u v : V}
    (h : G.Reachable u v) (hu : u ∈ U) : v ∈ U := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons h' _ ih => exact ih (hU _ _ h' hu)

-- CSLib candidate
/-- A walk whose edges keep `β` constant stays in the block of its start. -/
lemma support_eq_of_edges {ι : Type} (β : V → ι) {u w : V} (q : G.Walk u w)
    (hq : ∀ x y, s(x, y) ∈ q.edges → β x = β y) : ∀ x ∈ q.support, β x = β u := by
  induction q with
  | nil => intro x hx; simp at hx; rw [hx]
  | @cons u u' w h q' ih =>
    intro x hx
    have h1 : β u = β u' := hq u u' (by simp)
    rcases List.mem_cons.1 (by simpa using hx) with rfl | hx
    · rfl
    · rw [ih (fun x y hxy => hq x y (by simp [hxy])) x hx, h1]

/-- A path ending at `z` stays, before reaching `z`, in the block of its start, if the edges
avoiding `z` keep `β` constant. -/
lemma path_support_of_cut {ι : Type} (z : V) (β : V → ι)
    (hβ : ∀ x y, G.Adj x y → x ≠ z → y ≠ z → β x = β y) {u w : V} (q : G.Walk u w)
    (hq : q.IsPath) (hw : w = z) : ∀ x ∈ q.support, x = z ∨ β x = β u := by
  induction q with
  | nil => intro x hx; simp at hx; left; rw [hx, hw]
  | @cons u u' w h q' ih =>
    intro x hx
    have hq' := hq.of_cons
    by_cases hu : u = z
    · subst hu hw
      exact absurd (SimpleGraph.Walk.isPath_iff_nil.1 hq) (by simp)
    rcases List.mem_cons.1 (by simpa using hx) with rfl | hx
    · exact Or.inr rfl
    · by_cases hu' : u' = z
      · subst hu' hw
        rw [SimpleGraph.Walk.nil_iff_support_eq.1 (SimpleGraph.Walk.isPath_iff_nil.1 hq')] at hx
        simp at hx; exact Or.inl hx
      · rcases ih hq' hw x hx with h' | h'
        · exact Or.inl h'
        · exact Or.inr (h'.trans (hβ u' u h.symm hu' hu))

-- CSLib candidate
/-- **Cycles through a cut vertex.** If the edges of `G - z` keep `β` constant, every simple
cycle consists of distinct vertices that are `z` or in a single block. The list returned has as
many elements as the cycle has nodes. -/
lemma cycle_support_of_cut {ι : Type} (z : V) (β : V → ι)
    (hβ : ∀ x y, G.Adj x y → x ≠ z → y ≠ z → β x = β y) {v : V} (p : G.Walk v v)
    (hp : p.IsCycle) :
    ∃ k, ∃ l : List V, l.Nodup ∧ l.length = p.length ∧ ∀ x ∈ l, x = z ∨ β x = k := by
  by_cases hz : z ∈ p.support
  · have hc := hp.rotate hz
    rw [← SimpleGraph.Walk.length_rotate p z hz]
    generalize p.rotate z hz = p' at hc
    cases p' with
    | nil => exact absurd hc SimpleGraph.Walk.not_isCycle_nil
    | @cons _ y _ h q =>
      have hq := ((SimpleGraph.Walk.cons_isCycle_iff q h).1 hc).1
      refine ⟨β y, q.support, hq.support_nodup, by simp, ?_⟩
      exact path_support_of_cut z β hβ q hq rfl
  · refine ⟨β v, p.support.tail, hp.support_nodup, by simp, fun x hx => Or.inr ?_⟩
    refine support_eq_of_edges β p (fun x y hxy => ?_) x (List.mem_of_mem_tail hx)
    have hx' := p.fst_mem_support_of_mem_edges hxy
    have hy' := p.snd_mem_support_of_mem_edges hxy
    exact hβ x y (p.adj_of_mem_edges hxy) (fun h => hz (h ▸ hx')) (fun h => hz (h ▸ hy'))

/-- A walk through `f 0, f 1, …, f k` along consecutive adjacencies. -/
lemma exists_seq_walk (f : ℕ → V) (m : ℕ) (hadj : ∀ i < m, G.Adj (f i) (f (i + 1))) :
    ∀ k ≤ m, ∃ p : G.Walk (f 0) (f k), p.support = (List.range (k + 1)).map f ∧
      p.edges = (List.range k).map fun i => s(f i, f (i + 1)) := by
  intro k hk
  induction k with
  | zero => exact ⟨SimpleGraph.Walk.nil, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨p, hs, he⟩ := ih (by omega)
    refine ⟨p.concat (hadj k (by omega)), ?_, ?_⟩
    · rw [SimpleGraph.Walk.support_concat, hs, List.range_succ (n := k + 1), List.map_append]
      simp
    · rw [SimpleGraph.Walk.edges_concat, he, List.range_succ (n := k), List.map_append]
      simp

-- CSLib candidate
/-- **A cycle from a cyclic sequence.** Distinct vertices `f 0, …, f m` (`m ≥ 2`) with
`f i ~ f (i+1)` and `f m ~ f 0` form a simple cycle with `m + 1` nodes. -/
lemma exists_cycle_of_seq (f : ℕ → V) (m : ℕ) (hm : 2 ≤ m)
    (hinj : ∀ i ≤ m, ∀ j ≤ m, f i = f j → i = j) (hadj : ∀ i < m, G.Adj (f i) (f (i + 1)))
    (hclose : G.Adj (f m) (f 0)) : ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = m + 1 := by
  obtain ⟨p, hs, he⟩ := exists_seq_walk f m hadj m le_rfl
  refine ⟨f m, SimpleGraph.Walk.cons hclose p, ?_, by simp [← SimpleGraph.Walk.length_edges, he]⟩
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def, hs]
    refine List.Nodup.map_on (fun a ha b hb h => hinj a ?_ b ?_ h) List.nodup_range <;>
      simp_all [List.mem_range]
  · rw [he]
    intro hmem
    obtain ⟨i, hi, hie⟩ := List.mem_map.1 hmem
    rw [List.mem_range] at hi
    rcases Sym2.eq_iff.1 hie with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hinj i (by omega) m le_rfl h1; omega
    · have := hinj (i + 1) (by omega) m le_rfl h2
      have := hinj i (by omega) 0 (by omega) h1
      omega

end graph

/-- A duplicate-free list of elements of `Fin n` whose values lie in `T` has at most `#T`
elements. -/
lemma length_le_of_vals {n : ℕ} {l : List (Fin n)} (hl : l.Nodup) (T : Finset ℕ)
    (hT : ∀ x ∈ l, x.val ∈ T) : l.length ≤ T.card := by
  have h1 : (l.map Fin.val).Nodup := hl.map Fin.val_injective
  rw [← List.length_map (f := Fin.val), ← List.toFinset_card_of_nodup h1]
  exact Finset.card_le_card fun a ha => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 ha)
    exact hT x hx

end Podc.RandomizedPLS
