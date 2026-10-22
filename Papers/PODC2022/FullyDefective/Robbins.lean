import Mathlib

/-!
# Robbins cycles in 2-edge-connected graphs

Section 4 of [CCGS22] (Censor-Hillel, Cohen, Gelles, Sela, *Distributed Computations in Fully-Defective
Networks*, PODC 2022) relies on the following classical fact (Robbins 1939, via Whitney's ear decomposition):
every 2-edge-connected graph has a *Robbins cycle*, i.e. a closed walk through all vertices (and all edges)
that never traverses an edge in both directions.

## Main declarations

* `RobbinsCycle G` — a closed walk `C : ZMod L → V` of `G` through every vertex that never traverses an edge
  in both directions.
* `RobbinsCycle.exists_of_bridgeless` — a finite, connected, bridgeless graph with at least two vertices has a
  Robbins cycle that moreover traverses every edge.
* `RobbinsCycle.connected`, `RobbinsCycle.not_isBridge` — conversely, a graph with a Robbins cycle is connected
  and bridgeless.

## Proof

We first prove Robbins' theorem in orientation form (`exists_strongOrientation`): there is a relation
`O ⊆ G.Adj` that is asymmetric, orients every edge, and is strongly connected. It is grown by ears: given an
asymmetric relation, strongly connected on a vertex set `S`, take an edge `xy` leaving `S`; since `xy` is not a
bridge there is a path from `y` back to `x` avoiding `xy`; orient `x → y` and this path up to its first return
to `S` (`ear_step`). The remaining edges are oriented by a well-order. A closed `O`-walk through every arc of `O`
(`exists_closed_chain`) is then a Robbins cycle traversing every edge.
-/

namespace Podc.FullyDefective

open Relation

/-- A Robbins cycle of `G` (Section 4 of [CCGS22]): a closed walk `C 0 → C 1 → ⋯ → C (L-1) → C 0`, indexed by
`ZMod L`, through every vertex, that never traverses an edge of `G` in both directions (edges may be traversed
several times in the same direction). -/
structure RobbinsCycle {V : Type*} (G : SimpleGraph V) where
  L : ℕ
  [neZero : NeZero L]
  C : ZMod L → V
  adj : ∀ j, G.Adj (C j) (C (j + 1))
  surj : Function.Surjective C
  oriented : ∀ i j, C i = C (j + 1) → C (i + 1) ≠ C j

attribute [instance] RobbinsCycle.neZero

variable {V : Type*} {G : SimpleGraph V}

/-! ### Walks along a cyclic sequence -/

-- CSLib candidate
/-- If every step `f (i + m) → f (i + m + 1)` with `m < n` of a cyclic sequence is an edge of `H`, then
`f (i + n)` is reachable from `f i` in `H`. -/
theorem reachable_of_steps {L : ℕ} (H : SimpleGraph V) (f : ZMod L → V) (i : ZMod L) :
    ∀ n : ℕ, (∀ m < n, H.Adj (f (i + m)) (f (i + m + 1))) → H.Reachable (f i) (f (i + n))
  | 0, _ => by simp
  | n + 1, h => by
    have ih := reachable_of_steps H f i n (fun m hm => h m (by omega))
    have := (h n (by omega)).reachable
    push_cast
    rw [← add_assoc]
    exact ih.trans this

-- CSLib candidate
/-- If every step of a cyclic sequence `f : ZMod L → V` is an edge of `H`, then all its values are mutually
reachable in `H`. -/
theorem reachable_of_forall_adj {L : ℕ} [NeZero L] (H : SimpleGraph V) (f : ZMod L → V)
    (h : ∀ j, H.Adj (f j) (f (j + 1))) (i j : ZMod L) : H.Reachable (f i) (f j) := by
  have := reachable_of_steps H f i (j - i).val (fun m _ => h _)
  rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this

namespace RobbinsCycle

/-- A graph with a Robbins cycle is connected. -/
theorem connected (C : RobbinsCycle G) : G.Connected := by
  have : Nonempty V := ⟨C.C 0⟩
  refine ⟨fun u v => ?_⟩
  obtain ⟨i, rfl⟩ := C.surj u
  obtain ⟨j, rfl⟩ := C.surj v
  exact reachable_of_forall_adj G C.C C.adj i j

/-- A graph with a Robbins cycle has no bridge: a closed walk through all vertices crossing a bridge would have
to cross it in both directions. (Mathlib's `IsBridge` does not require `e` to be an edge; non-edges are not
bridges of connected graphs either.) -/
theorem not_isBridge (C : RobbinsCycle G) (e : Sym2 V) : ¬ G.IsBridge e := by
  induction e using Sym2.ind with
  | h a b =>
  rw [SimpleGraph.isBridge_iff, not_not]
  set H := G.deleteEdges {s(a, b)}
  -- if the edge `ab` is traversed `x → y` at step `j`, walk on from `y` until the first visit of `x`
  have key : ∀ x y j, s(x, y) = s(a, b) → C.C j = x → C.C (j + 1) = y → H.Reachable y x := by
    intro x y j hxy hx hy
    obtain ⟨k, hk⟩ := C.surj x
    have hex : ∃ n : ℕ, C.C (j + 1 + n) = x := ⟨(k - (j + 1)).val, by simp [hk]⟩
    classical
    have hn := Nat.find_spec hex
    have hlt : ∀ m < Nat.find hex, C.C (j + 1 + m) ≠ x := fun m hm => Nat.find_min hex hm
    rw [← hn, ← hy]
    refine reachable_of_steps H C.C (j + 1) _ (fun m hm => ?_)
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨C.adj _, fun hmem => ?_⟩
    rw [Set.mem_singleton_iff, ← hxy, Sym2.eq_iff] at hmem
    rcases hmem with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact hlt m hm h1
    · exact C.oriented (j + 1 + m) j (h1.trans hy.symm) (h2.trans hx.symm)
  by_cases hab : ∃ j, C.C j = a ∧ C.C (j + 1) = b
  · obtain ⟨j, hj1, hj2⟩ := hab
    exact (key a b j rfl hj1 hj2).symm
  by_cases hba : ∃ j, C.C j = b ∧ C.C (j + 1) = a
  · obtain ⟨j, hj1, hj2⟩ := hba
    exact key b a j Sym2.eq_swap hj1 hj2
  push Not at hab hba
  obtain ⟨i, rfl⟩ := C.surj a
  obtain ⟨j, rfl⟩ := C.surj b
  refine reachable_of_forall_adj H C.C (fun k => ?_) i j
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨C.adj k, fun hmem => ?_⟩
  rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
  rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hab k h1 h2
  · exact hba k h1 h2

end RobbinsCycle

/-! ### Robbins' theorem: strong orientations of bridgeless graphs -/

/-- `D` is an orientation of some edges of `G` inside `S` (an asymmetric subrelation of `G.Adj` supported on
`S`) that is strongly connected on `S`. -/
structure StrongOn (G : SimpleGraph V) (S : Set V) (D : V → V → Prop) : Prop where
  mem : ∀ a b, D a b → a ∈ S ∧ b ∈ S
  adj : ∀ a b, D a b → G.Adj a b
  asymm : ∀ a b, D a b → ¬ D b a
  reach : ∀ u ∈ S, ∀ v ∈ S, ReflTransGen D u v

/-- One ear: orient the remaining part `c → ⋯ → z` of a path of `G'` (`G'` is `G` minus the first edge of the
ear) up to its first vertex in `S₀`. Invariants: `S` is `S₀` plus the ear vertices oriented so far, ending at
the current tip `c`; everything in `S` reaches `c`; `S₀` reaches everything in `S`. -/
theorem ear_step {G' : SimpleGraph V} (hG' : G' ≤ G) (S₀ : Set V) :
    ∀ {c z : V} (p : G'.Walk c z), p.IsPath → z ∈ S₀ → ∀ (S : Set V) (D : V → V → Prop),
      S₀ ⊆ S → c ∈ S → c ∉ S₀ →
      (∀ a b, D a b → a ∈ S ∧ b ∈ S) → (∀ a b, D a b → G.Adj a b) → (∀ a b, D a b → ¬ D b a) →
      (∀ u ∈ S, ReflTransGen D u c) → (∀ u ∈ S₀, ∀ v ∈ S, ReflTransGen D u v) →
      (∀ a, D a c ∨ D c a → a ∉ S₀ ∨ ¬ G'.Adj c a) →
      (∀ v ∈ p.support, v ∈ S → v ∈ S₀ ∨ v = c) →
      ∃ S' D', S ⊆ S' ∧ StrongOn G S' D' := by
  intro c z p
  induction p with
  | nil =>
    intro _ hz _ _ _ _ hc _ _ _ _ _ _ _
    exact absurd hz hc
  | @cons c w z h p ih =>
    intro hp hz S D hS₀ hcS hcS₀ hmem hadj hasymm hreach hreach₀ htip hsupp
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    obtain ⟨hp, hcp⟩ := hp
    have hwc : w ≠ c := (G'.ne_of_adj h).symm
    have hw : w ∈ S → w ∈ S₀ :=
      fun hwS => (hsupp w (by simp) hwS).resolve_right hwc
    set D' : V → V → Prop := fun a b => D a b ∨ (a = c ∧ b = w) with hD'
    have hmono : ∀ {u v}, ReflTransGen D u v → ReflTransGen D' u v :=
      fun h => ReflTransGen.mono (fun a b hab => Or.inl hab) _ _ h
    have hstep : ReflTransGen D' c w := ReflTransGen.single (Or.inr ⟨rfl, rfl⟩)
    by_cases hwS₀ : w ∈ S₀
    · -- close the ear at `w ∈ S₀`
      refine ⟨S, D', subset_rfl, ⟨?_, ?_, ?_, ?_⟩⟩
      · rintro a b (hab | ⟨rfl, rfl⟩)
        · exact hmem a b hab
        · exact ⟨hcS, hS₀ hwS₀⟩
      · rintro a b (hab | ⟨rfl, rfl⟩)
        · exact hadj a b hab
        · exact hG' h
      · have hwc' : ¬ D w c := fun hD =>
          (htip w (Or.inl hD)).elim (· hwS₀) (· h)
        rintro a b (hab | ⟨rfl, rfl⟩) (hba | ⟨h1, h2⟩)
        · exact hasymm a b hab hba
        · subst h1 h2; exact hwc' hab
        · exact hwc' hba
        · exact hwc h1
      · intro u hu v hv
        exact ((hmono (hreach u hu)).trans hstep).trans (hmono (hreach₀ w hwS₀ v hv))
    · -- extend the ear by the new vertex `w`
      have hwS : w ∉ S := fun hwS => hwS₀ (hw hwS)
      obtain ⟨S', D'', hSS', hgood⟩ := ih hp hz (insert w S) D'
        (hS₀.trans (Set.subset_insert _ _)) (Set.mem_insert _ _) hwS₀
        (by
          rintro a b (hab | ⟨rfl, rfl⟩)
          · exact ⟨Set.mem_insert_of_mem _ (hmem a b hab).1, Set.mem_insert_of_mem _ (hmem a b hab).2⟩
          · exact ⟨Set.mem_insert_of_mem _ hcS, Set.mem_insert _ _⟩)
        (by
          rintro a b (hab | ⟨rfl, rfl⟩)
          · exact hadj a b hab
          · exact hG' h)
        (by
          rintro a b (hab | ⟨rfl, rfl⟩) (hba | ⟨h1, h2⟩)
          · exact hasymm a b hab hba
          · exact hwS (h2 ▸ (hmem _ _ hab).1)
          · exact hwS (hmem _ _ hba).1
          · exact hwc h1)
        (by
          rintro u (rfl | hu)
          · exact ReflTransGen.refl
          · exact (hmono (hreach u hu)).trans hstep)
        (by
          rintro u hu v (rfl | hv)
          · exact (hmono (hreach u (hS₀ hu))).trans hstep
          · exact hmono (hreach₀ u hu v hv))
        (by
          rintro a ((hD | ⟨rfl, -⟩) | (hD | ⟨h1, -⟩))
          · exact absurd (hmem _ _ hD).2 hwS
          · exact Or.inl hcS₀
          · exact absurd (hmem _ _ hD).1 hwS
          · exact absurd h1 hwc)
        (by
          rintro v hv (rfl | hvS)
          · exact Or.inr rfl
          · refine (hsupp v (by simp [hv]) hvS).imp_right fun hvc => ?_
            subst hvc
            exact absurd hv hcp)
      exact ⟨S', D'', (Set.subset_insert _ _).trans hSS', hgood⟩

/-- Growing a strongly connected orientation by one ear: if `S ≠ univ` there is a strictly larger set with a
strongly connected orientation. -/
theorem StrongOn.exists_ssuperset [Finite V] (hconn : G.Connected)
    (hbr : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) {S : Set V} {D : V → V → Prop}
    (hD : StrongOn G S D) (hne : S.Nonempty) (hS : S ≠ Set.univ) :
    ∃ S' D', S ⊂ S' ∧ StrongOn G S' D' := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨y₀, hy₀⟩ : ∃ y, y ∉ S := by
    by_contra! h; exact hS (Set.eq_univ_of_forall h)
  obtain ⟨d, -, hdx, hdy⟩ := (hconn.preconnected x₀ y₀).some.exists_boundary_dart S hx₀ hy₀
  obtain ⟨⟨x, y⟩, hxy⟩ := d
  simp only at hdx hdy
  have hnb := hbr s(x, y) (by simpa using hxy)
  rw [SimpleGraph.isBridge_iff, not_not] at hnb
  set G' := G.deleteEdges {s(x, y)}
  obtain ⟨p⟩ := hnb.symm
  have hG' : G' ≤ G := SimpleGraph.deleteEdges_le _
  set D₁ : V → V → Prop := fun a b => D a b ∨ (a = x ∧ b = y)
  have hmono : ∀ {u v}, ReflTransGen D u v → ReflTransGen D₁ u v :=
    fun h => ReflTransGen.mono (fun a b hab => Or.inl hab) _ _ h
  have hstep : ReflTransGen D₁ x y := ReflTransGen.single (Or.inr ⟨rfl, rfl⟩)
  have hxy' : x ≠ y := G.ne_of_adj hxy
  obtain ⟨S', D', hSS', hgood⟩ := ear_step hG' S p.bypass p.bypass_isPath hdx (insert y S) D₁
    (Set.subset_insert _ _) (Set.mem_insert _ _) hdy
    (by
      rintro a b (hab | ⟨rfl, rfl⟩)
      · exact ⟨Set.mem_insert_of_mem _ (hD.mem a b hab).1, Set.mem_insert_of_mem _ (hD.mem a b hab).2⟩
      · exact ⟨Set.mem_insert_of_mem _ hdx, Set.mem_insert _ _⟩)
    (by
      rintro a b (hab | ⟨rfl, rfl⟩)
      · exact hD.adj a b hab
      · exact hxy)
    (by
      rintro a b (hab | ⟨rfl, rfl⟩) (hba | ⟨h1, h2⟩)
      · exact hD.asymm a b hab hba
      · exact hdy (h2 ▸ (hD.mem _ _ hab).1)
      · exact hdy (hD.mem _ _ hba).1
      · exact hxy' h2)
    (by
      rintro u (rfl | hu)
      · exact ReflTransGen.refl
      · exact (hmono (hD.reach u hu x hdx)).trans hstep)
    (by
      rintro u hu v (rfl | hv)
      · exact (hmono (hD.reach u hu x hdx)).trans hstep
      · exact hmono (hD.reach u hu v hv))
    (by
      rintro a ((hDa | ⟨rfl, -⟩) | (hDa | ⟨h1, -⟩))
      · exact absurd (hD.mem _ _ hDa).2 hdy
      · right
        rw [SimpleGraph.deleteEdges_adj]
        simp [Sym2.eq_swap]
      · exact absurd (hD.mem _ _ hDa).1 hdy
      · exact absurd h1.symm hxy')
    (by
      rintro v - (rfl | hv)
      · exact Or.inr rfl
      · exact Or.inl hv)
  refine ⟨S', D', ?_, hgood⟩
  refine Set.ssubset_iff_subset_ne.2 ⟨(Set.subset_insert _ _).trans hSS', ?_⟩
  rintro rfl
  exact hdy (hSS' (Set.mem_insert _ _))

/-- Robbins' theorem, intermediate form: a finite connected bridgeless graph has an asymmetric subrelation of
its adjacency that is strongly connected on all vertices. -/
theorem exists_strongOn_univ [Finite V] (hconn : G.Connected)
    (hbr : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) : ∃ D, StrongOn G Set.univ D := by
  obtain ⟨r⟩ := hconn.nonempty
  suffices h : ∀ n : ℕ, ∀ (S : Set V) (D : V → V → Prop), Sᶜ.ncard ≤ n → S.Nonempty →
      StrongOn G S D → ∃ D', StrongOn G Set.univ D' by
    refine h _ {r} (fun _ _ => False) le_rfl ⟨r, rfl⟩ ⟨by simp, by simp, by simp, ?_⟩
    rintro u rfl v rfl; exact ReflTransGen.refl
  intro n
  induction n with
  | zero =>
    intro S D hn _ hD
    have : Sᶜ = ∅ := (Set.ncard_eq_zero (s := Sᶜ)).1 (by omega)
    rw [Set.compl_empty_iff] at this
    exact ⟨D, this ▸ hD⟩
  | succ n ih =>
    intro S D hn hne hD
    by_cases hS : S = Set.univ
    · exact ⟨D, hS ▸ hD⟩
    obtain ⟨S', D', hSS', hD'⟩ := hD.exists_ssuperset hconn hbr hne hS
    refine ih S' D' ?_ (hne.mono hSS'.subset) hD'
    have := Set.ncard_lt_ncard (compl_lt_compl_iff_lt.2 hSS') (Set.toFinite _)
    omega

-- CSLib candidate
/-- **Robbins' theorem** (orientation form): a finite connected bridgeless graph has a strongly connected
orientation `O`: `O` is an asymmetric subrelation of `G.Adj` orienting every edge, and every vertex reaches every
vertex along `O`. -/
theorem exists_strongOrientation [Finite V] (hconn : G.Connected)
    (hbr : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ O : V → V → Prop, (∀ a b, O a b → G.Adj a b) ∧ (∀ a b, O a b → ¬ O b a) ∧
      (∀ a b, G.Adj a b → O a b ∨ O b a) ∧ ∀ u v, ReflTransGen O u v := by
  obtain ⟨D, hD⟩ := exists_strongOn_univ hconn hbr
  refine ⟨fun a b => D a b ∨ (G.Adj a b ∧ ¬ D a b ∧ ¬ D b a ∧ WellOrderingRel a b), ?_, ?_, ?_, ?_⟩
  · rintro a b (h | h)
    · exact hD.adj a b h
    · exact h.1
  · rintro a b (h | ⟨-, h1, h2, h3⟩) (h' | ⟨-, h1', h2', h3'⟩)
    · exact hD.asymm a b h h'
    · exact h2' h
    · exact h2 h'
    · exact asymm h3 h3'
  · intro a b hab
    by_cases h1 : D a b
    · exact Or.inl (Or.inl h1)
    by_cases h2 : D b a
    · exact Or.inr (Or.inl h2)
    rcases trichotomous_of WellOrderingRel a b with h | h | h
    · exact Or.inl (Or.inr ⟨hab, h1, h2, h⟩)
    · exact absurd h (G.ne_of_adj hab)
    · exact Or.inr (Or.inr ⟨hab.symm, h2, h1, h⟩)
  · intro u v
    exact ReflTransGen.mono (fun a b h => Or.inl h) _ _ (hD.reach u trivial v trivial)

/-! ### From a strongly connected orientation to a Robbins cycle -/

-- CSLib candidate
/-- In a strongly connected relation `O`, for any finite list of arcs there is a closed `O`-walk from `r` to `r`
(written as the list `r :: t`) containing each of these arcs as two consecutive entries. -/
theorem exists_closed_chain {O : V → V → Prop} (hreach : ∀ u v, ReflTransGen O u v) (r : V) :
    ∀ ds : List (V × V), (∀ d ∈ ds, O d.1 d.2) →
      ∃ t : List V, List.IsChain O (r :: t) ∧ (r :: t).getLast (List.cons_ne_nil _ _) = r ∧
        ∀ d ∈ ds, [d.1, d.2] <:+: r :: t
  | [], _ => ⟨[], .singleton _, rfl, by simp⟩
  | d :: ds, hds => by
    obtain ⟨t, ht, htl, htd⟩ := exists_closed_chain hreach r ds (fun d' hd' => hds d' (by simp [hd']))
    obtain ⟨p₁, hp₁, hp₁l⟩ := List.exists_isChain_cons_of_relationReflTransGen (hreach r d.1)
    obtain ⟨p₂, hp₂, hp₂l⟩ := List.exists_isChain_cons_of_relationReflTransGen (hreach d.2 r)
    have hO : O d.1 d.2 := hds d (by simp)
    -- the new closed walk is `(r :: p₁) ++ (d.2 :: p₂) ++ t`
    obtain ⟨X, hX⟩ : ∃ X, r :: p₁ = X ++ [d.1] :=
      ⟨(r :: p₁).dropLast, by rw [← hp₁l, List.dropLast_append_getLast]⟩
    obtain ⟨Y, hY⟩ : ∃ Y, d.2 :: p₂ = Y ++ [r] :=
      ⟨(d.2 :: p₂).dropLast, by rw [← hp₂l, List.dropLast_append_getLast]⟩
    have e1 : r :: (p₁ ++ d.2 :: p₂ ++ t) = X ++ d.1 :: d.2 :: (p₂ ++ t) := by
      rw [show r :: (p₁ ++ d.2 :: p₂ ++ t) = (r :: p₁) ++ d.2 :: (p₂ ++ t) by simp, hX]; simp
    have e2 : r :: (p₁ ++ d.2 :: p₂ ++ t) = (X ++ d.1 :: Y) ++ r :: t := by
      rw [show r :: (p₁ ++ d.2 :: p₂ ++ t) = (r :: p₁) ++ (d.2 :: p₂) ++ t by simp, hX, hY]; simp
    refine ⟨p₁ ++ d.2 :: p₂ ++ t, ?_, ?_, ?_⟩
    · rw [e1, List.isChain_split]
      refine ⟨hX ▸ hp₁, List.IsChain.cons_cons hO ?_⟩
      rw [← List.cons_append, hY, List.append_assoc, List.singleton_append, List.isChain_split]
      exact ⟨hY ▸ hp₂, ht⟩
    · simp only [e2]
      rw [List.getLast_append_of_ne_nil (by simp)]
      exact htl
    · rintro d' hd'
      rcases List.mem_cons.1 hd' with rfl | hd'
      · exact ⟨X, p₂ ++ t, by rw [e1]; simp⟩
      · exact (htd d' hd').trans ⟨X ++ d.1 :: Y, [], by rw [e2]; simp⟩

/-- A closed `O`-walk `r :: t` (ending at `r`) gives a cyclic sequence on `ZMod t.length` all of whose steps
are `O`-arcs and which contains every pair of consecutive entries of `r :: t` as a step. -/
theorem exists_cyclic_of_closed_chain {O : V → V → Prop} {r : V} {t : List V} (ht : t ≠ [])
    (hc : List.IsChain O (r :: t)) (hl : (r :: t).getLast (List.cons_ne_nil _ _) = r) :
    ∃ (L : ℕ) (_ : NeZero L) (C : ZMod L → V), (∀ j, O (C j) (C (j + 1))) ∧
      ∀ a b, [a, b] <:+: r :: t → ∃ j, C j = a ∧ C (j + 1) = b := by
  set w := r :: t with hw
  set L := t.length
  have hL : NeZero L := ⟨by simpa [L] using ht⟩
  have hwL : w.length = L + 1 := by simp [w, L]
  let C : ZMod L → V := fun j => w.getD j.val r
  have hC : ∀ k : ℕ, k < L + 1 → C k = w.getD k r := by
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · simp only [C, ZMod.val_cast_of_lt hk]
    · simp only [C, ZMod.natCast_self, ZMod.val_zero]
      rw [List.getLast_eq_getElem] at hl
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      simp only [w, hwL, add_tsub_cancel_right] at hl ⊢
      rw [hl]; rfl
  have hsucc : ∀ j : ZMod L, C (j + 1) = w.getD (j.val + 1) r := by
    intro j
    rw [← hC _ (by have := ZMod.val_lt j; omega)]
    push_cast
    rw [ZMod.natCast_zmod_val]
  refine ⟨L, hL, C, fun j => ?_, fun a b hab => ?_⟩
  · have hj := ZMod.val_lt j
    rw [hsucc]
    simp only [C]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact List.isChain_iff_getElem.1 hc j.val (by omega)
  · obtain ⟨s, u, hsu⟩ := hab
    have hlen : s.length + 2 + u.length = L + 1 := by
      rw [← hwL, ← hsu]; simp; omega
    refine ⟨(s.length : ℕ), ?_, ?_⟩
    · rw [hC _ (by omega), ← hsu]
      simp
    · have := hC (s.length + 1) (by omega)
      push_cast at this
      rw [this, ← hsu]
      simp

namespace RobbinsCycle

/-- **Robbins' theorem** in the form used in Section 4 of [CCGS22]: every finite, connected, bridgeless
(i.e. 2-edge-connected) graph with at least two vertices has a Robbins cycle; moreover, the cycle traverses
every edge of `G` (in one of the two directions). -/
theorem exists_of_bridgeless [Finite V] [Nontrivial V] (hconn : G.Connected)
    (hbr : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ C : RobbinsCycle G, ∀ v w, G.Adj v w →
      ∃ j, (C.C j = v ∧ C.C (j + 1) = w) ∨ (C.C j = w ∧ C.C (j + 1) = v) := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨O, hOadj, hOasymm, hOcover, hOreach⟩ := exists_strongOrientation hconn hbr
  obtain ⟨r⟩ := hconn.nonempty
  let ds : List (V × V) := (Finset.univ.filter fun d : V × V => O d.1 d.2).toList
  obtain ⟨t, htc, htl, htd⟩ := exists_closed_chain hOreach r ds (by simp [ds])
  obtain ⟨u, hu⟩ := hconn.preconnected.exists_adj_of_nontrivial r
  have hcov : ∀ a b, G.Adj a b → [a, b] <:+: r :: t ∨ [b, a] <:+: r :: t := by
    intro a b hab
    rcases hOcover a b hab with h | h
    · exact Or.inl (htd (a, b) (by simp [ds, h]))
    · exact Or.inr (htd (b, a) (by simp [ds, h]))
  have ht : t ≠ [] := by
    rintro rfl
    rcases hcov r u hu with h | h <;> simpa using h.length_le
  obtain ⟨L, hL, C, hC, hCd⟩ := exists_cyclic_of_closed_chain ht htc htl
  have hedge : ∀ v w, G.Adj v w →
      ∃ j, (C j = v ∧ C (j + 1) = w) ∨ (C j = w ∧ C (j + 1) = v) := by
    intro v w hvw
    rcases hcov v w hvw with h | h
    · obtain ⟨j, hj⟩ := hCd _ _ h; exact ⟨j, Or.inl hj⟩
    · obtain ⟨j, hj⟩ := hCd _ _ h; exact ⟨j, Or.inr hj⟩
  refine ⟨@RobbinsCycle.mk V G L hL C (fun j => hOadj _ _ (hC j)) (fun v => ?_)
    (fun i j hij hji => ?_), hedge⟩
  · obtain ⟨w, hw⟩ := hconn.preconnected.exists_adj_of_nontrivial v
    obtain ⟨j, ⟨hj, -⟩ | ⟨-, hj⟩⟩ := hedge v w hw
    · exact ⟨j, hj⟩
    · exact ⟨j + 1, hj⟩
  · have h1 := hC i
    rw [hij, hji] at h1
    exact hOasymm _ _ (hC j) h1

/-- Every finite 2-edge-connected graph with at least two vertices has a Robbins cycle. -/
theorem nonempty_of_bridgeless [Finite V] [Nontrivial V] (hconn : G.Connected)
    (hbr : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) : Nonempty (RobbinsCycle G) :=
  let ⟨C, _⟩ := exists_of_bridgeless hconn hbr; ⟨C⟩

/-- Characterization: a finite graph with at least two vertices has a Robbins cycle iff it is connected and
bridgeless. -/
theorem nonempty_iff [Finite V] [Nontrivial V] :
    Nonempty (RobbinsCycle G) ↔ G.Connected ∧ ∀ e ∈ G.edgeSet, ¬ G.IsBridge e :=
  ⟨fun ⟨C⟩ => ⟨C.connected, fun e _ => C.not_isBridge e⟩,
    fun h => nonempty_of_bridgeless h.1 h.2⟩

end RobbinsCycle

/-! ### Non-vacuity -/

/-- The triangle `0 → 1 → 2 → 0` is a Robbins cycle of the complete graph on three vertices. -/
def triangleRobbinsCycle : RobbinsCycle (⊤ : SimpleGraph (Fin 3)) where
  L := 3
  C := fun j => (j : Fin 3)
  adj := (by decide : ∀ j : Fin 3, (⊤ : SimpleGraph (Fin 3)).Adj j (j + 1))
  surj := (by decide : Function.Surjective fun j : Fin 3 => j)
  oriented := (by decide : ∀ i j : Fin 3, i = j + 1 → i + 1 ≠ j)

end Podc.FullyDefective
