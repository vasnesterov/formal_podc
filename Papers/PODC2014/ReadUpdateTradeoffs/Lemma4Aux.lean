import Papers.PODC2014.ReadUpdateTradeoffs.MaxRegSetup
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Auxiliary results for Lemma 4 of Hendler–Khait (PODC'14)

* `exists_indep` — an independent set of size `≥ |S|/3` in a graph on `S` in which every vertex
  has at most one out-edge (the paper invokes Turán's theorem for average degree `≤ 2`);
* `gstep_tau_cases` — uniform description of the ghost effect of one step;
* `ess_step` — assembling the next essential state after one step of each kept process.
-/

namespace Podc.ReadUpdateTradeoffs

open Cslib.SharedMemory Cslib.SharedMemory.Awareness

variable {P : Type} [DecidableEq P]

/-- **Independent sets in out-degree-one graphs.** For any `g : P → Option P` (the out-neighbour
of each vertex, if any) and finite `S`, there is `I ⊆ S` with `|S| ≤ 3 |I|` containing no edge
`p → g p` between two distinct vertices. -/
theorem exists_indep (g : P → Option P) :
    ∀ S : Finset P, ∃ I ⊆ S, S.card ≤ 3 * I.card ∧ ∀ p ∈ I, ∀ x ∈ I, g p = some x → x = p := by
  intro S
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, by simp, by simp at hn; omega, by simp⟩
  -- a vertex of in-degree at most one
  obtain ⟨v, hvS, hv⟩ : ∃ v ∈ S, (S.filter (fun u => g u = some v)).card ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    set s := S.filter (fun u => ∃ v ∈ S, g u = some v)
    have h1 := Finset.mul_card_image_le_card_of_maps_to (f := g) (s := s) (t := S.image some)
      (fun u hu => by
        obtain ⟨-, v, hv, huv⟩ := Finset.mem_filter.1 hu
        exact Finset.mem_image.2 ⟨v, hv, huv.symm⟩) 2 (fun b hb => by
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hb
        have : s.filter (fun a => g a = some v) = S.filter (fun u => g u = some v) := by
          ext u; simp only [s, Finset.mem_filter]
          constructor
          · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨h1, v, hv, h2⟩, h2⟩
        rw [this]; exact hcon v hv)
    rw [Finset.card_image_of_injective _ (Option.some_injective P)] at h1
    have h2 : s.card ≤ S.card := Finset.card_filter_le _ _
    have h3 : 0 < S.card := Finset.card_pos.2 hne
    omega
  -- remove `v`, its out-neighbour and its in-neighbour
  set R := insert v ((g v).toList.toFinset ∪ S.filter (fun u => g u = some v)) with hR
  have hRcard : R.card ≤ 3 := by
    refine (Finset.card_insert_le _ _).trans ?_
    have : ((g v).toList.toFinset ∪ S.filter (fun u => g u = some v)).card ≤ 2 := by
      refine (Finset.card_union_le _ _).trans ?_
      have : (g v).toList.toFinset.card ≤ 1 := by cases g v <;> simp
      omega
    omega
  set S' := S \ R with hS'
  have hvR : v ∈ R := Finset.mem_insert_self _ _
  have hS'lt : S'.card < n := by
    rw [← hn]
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.sdiff_subset, fun h => by
      have : v ∈ S' := h ▸ hvS
      exact (Finset.mem_sdiff.1 this).2 hvR⟩)
  obtain ⟨I', hI'S, hI'card, hI'ind⟩ := ih _ hS'lt S' rfl
  have hvI' : v ∉ I' := fun h => (Finset.mem_sdiff.1 (hI'S h)).2 hvR
  refine ⟨insert v I', Finset.insert_subset hvS (hI'S.trans Finset.sdiff_subset), ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hvI']
    have : S.card ≤ S'.card + R.card := by
      have := Finset.card_le_card_sdiff_add_card (s := S) (t := R)
      omega
    omega
  · intro p hp x hx hpx
    rcases Finset.mem_insert.1 hp with hpv | hp' <;> rcases Finset.mem_insert.1 hx with hxv | hx'
    · rw [hpv, hxv]
    · exfalso
      subst hpv
      have : x ∈ R := by simp [hR, hpx]
      exact (Finset.mem_sdiff.1 (hI'S hx')).2 this
    · exfalso
      subst hxv
      have hpS : p ∈ S := (Finset.mem_sdiff.1 (hI'S hp')).1
      have : p ∈ R := by simp [hR, hpS, hpx]
      exact (Finset.mem_sdiff.1 (hI'S hp')).2 this
    · exact hI'ind p hp' x hx' hpx

/-! ### One step, uniformly -/

variable {A : ObjSpec} {ι L V : Type} [DecidableEq ι] [DecidableEq V] {v₀ : V}
  {I : Impl A (RWC ι V v₀) P L}

/-- The ghost effect of one step of `p` accessing object `i`: only the awareness set of `p` and
the history of `i` change; `p` learns at most the familiarity set of `i`; the history of `i`
either stays or gets an entry of `p` carrying `p`'s new awareness set. -/
lemma gstep_tau_cases {C : Config A (RWC ι V v₀) P L} {G : Ghost P ι V} {p : P} {i : ι}
    {o : CASOp V} {k : V ⊕ Bool → L} (hact : I.act p (C.loc p) = .access i o k) :
    let G' := gstep I C G (.tau p)
    (∀ q, q ≠ p → G'.aw q = G.aw q) ∧ G'.aw p ⊆ G.aw p ∪ G.F i ∧
      (∀ j, j ≠ i → G'.hist j = G.hist j) ∧
      (G'.hist i = G.hist i ∨ ∃ v, G'.hist i = ⟨p, v, G'.aw p⟩ :: G.hist i) := by
  intro G'
  cases o with
  | read =>
    simp only [G', gstep_tau_read hact]
    refine ⟨fun q hq => by simp [Function.update_of_ne hq], by simp, fun j _ => by simp,
      Or.inl (by simp)⟩
  | write v =>
    simp only [G', gstep_tau_write hact]
    refine ⟨fun q _ => by simp, by simp, fun j hj => by
      simp [Function.update_of_ne hj], Or.inr ⟨v, by simp⟩⟩
  | cas a b =>
    simp only [G', gstep_tau_cas hact]
    refine ⟨fun q hq => by simp [Function.update_of_ne hq], by simp, fun j hj => ?_, ?_⟩
    · split_ifs <;> simp [Function.update_of_ne hj]
    · split_ifs
      · exact Or.inr ⟨b, by simp⟩
      · exact Or.inl (by simp)

/-! ### Assembling the next essential state -/

variable {W : Finset P} {val : P → ℕ}
variable {I : Impl maxRegObj (RWC ι V v₀) P L}

/-- After an execution with essential set `E₁` in which every process of `E₁` takes one more
step (in any order `l`), we obtain an execution with an `(i+1)`-step essential set `E' ⊆ E₁`,
the remaining processes of `E₁` becoming halted — provided they have smaller values, `E'` is
hidden and the block invariant holds. -/
lemma ess_step [Fintype P] {i : ℕ} {α₁ : List (Label P maxRegObj)}
    {C₁ : Config maxRegObj (RWC ι V v₀) P L} {G₁ : Ghost P ι V} {E₁ H : Finset P}
    (h₁ : Ess I W val i α₁ C₁ G₁ E₁ H) (l : List P) (hl : l.Perm E₁.toList)
    {C' : Config maxRegObj (RWC ι V v₀) P L} {G' : Ghost P ι V}
    (hrun : arunFrom I (C₁, G₁) (l.map .tau) = some (C', G')) {E' : Finset P} (hE' : E' ⊆ E₁)
    (hsup : ∀ h ∈ E₁ \ E', ∀ e ∈ E', val h < val e) (hhid : Hidden G' E')
    (hblk : ∀ o, BlockOK E' (G'.hist o)) :
    Ess I W val (i + 1) (α₁ ++ l.map .tau) C' G' E' (H ∪ (E₁ \ E')) := by
  have hlmem : ∀ p, p ∈ l ↔ p ∈ E₁ := fun p => by rw [hl.mem_iff, Finset.mem_toList]
  have hlnd : l.Nodup := hl.nodup_iff.2 (Finset.nodup_toList _)
  have hpend := runFrom_taus_pend l (arunFrom_fst I hrun)
  have hunion : E' ∪ (H ∪ (E₁ \ E')) = E₁ ∪ H := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; constructor
    · rintro (h | h | ⟨h, -⟩)
      · exact Or.inl (hE' h)
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · by_cases hx : x ∈ E'
        · exact Or.inl hx
        · exact Or.inr (Or.inr ⟨h, hx⟩)
      · exact Or.inr (Or.inl h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hhid, ?_, hblk⟩
  · rw [arun_append_of_eq I h₁.run]; exact hrun
  · rw [hunion]; exact h₁.subW
  · rw [Finset.disjoint_union_right]
    exact ⟨Finset.disjoint_of_subset_left hE' h₁.disj, Finset.disjoint_sdiff⟩
  · intro ℓ hℓ
    rw [hunion]
    rcases List.mem_append.1 hℓ with hℓ | hℓ
    · exact h₁.labels ℓ hℓ
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hℓ
      exact Finset.mem_union_left _ ((hlmem p).1 hp)
  · intro p hp
    rw [hunion] at hp
    simp [opsOf_map_tau, h₁.ops p hp]
  · intro p; simp [respsOf_map_tau, h₁.resps p]
  · intro p hp; rw [hpend]; exact h₁.pend p (hE' hp)
  · intro h hh e he
    rcases Finset.mem_union.1 hh with hh | hh
    · exact h₁.supreme h hh e (hE' he)
    · exact hsup h hh e he
  · intro e he
    rw [tauCount_append, tauCount_map_tau, h₁.steps e (hE' he),
      List.count_eq_one_of_mem hlnd ((hlmem e).2 (hE' he))]

end Podc.ReadUpdateTradeoffs
