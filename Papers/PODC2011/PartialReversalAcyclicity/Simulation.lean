import Papers.PODC2011.PartialReversalAcyclicity.PR
import Papers.PODC2011.PartialReversalAcyclicity.NewPR

/-!
# Section 5: simulation relations `PR → OneStepPR → NewPR`, and acyclicity of `PR`

* `R0` (Section 5.2): same directed graph `G'` and same lists. Lemma 5.1 and Theorem 5.2.
  A step `reverse(S)` is simulated by the steps `reverse(u)`, `u ∈ S`, one at a time; this needs
  `S` finite, so this part assumes a finite node set (`[Finite V]`), as the paper implicitly does.
* `Rel` (Section 5.3, the paper's `R`): same `G'`; if `parity[u]` is even then
  `list[u] ⊆ out-nbrsᵤ`; if odd then `list[u] ⊆ in-nbrsᵤ`. Lemma 5.3 and Theorem 5.4.
  The matching sequence of `NewPR` steps differs from the paper's in a corner case (see
  `README.md`): we use one `reverse(w)` step when the set `NewPR` would reverse is nonempty,
  and two (a dummy one, then the real one) otherwise.
* Theorem 5.5: every reachable state of `PR` is acyclic.
-/

noncomputable section
open Classical

namespace Podc.PartialReversalAcyclicity

variable {V : Type*} {N : Network V}

/-! ### Facts about `PR.effect` -/

namespace PR

theorem revSet_congr {s t : PRState V} (h : s.list = t.list) : revSet N s = revSet N t := by
  funext u; simp [revSet, h]

/-- The effect of a step depends only on `G'` and the lists. -/
theorem effect_congr {S : Set V} {s t : PRState V} (hd : arcs N s.dir = arcs N t.dir)
    (hl : s.list = t.list) :
    arcs N (effect N S s).dir = arcs N (effect N S t).dir ∧
      (effect N S s).list = (effect N S t).list := by
  have hr := revSet_congr (N := N) hl
  refine ⟨arcs_eq_of_dir_eq fun x y hxy => ?_, ?_⟩
  · simp only [effect, hr, dir_eq_of_arcs_eq hd hxy]
  · funext x; simp only [effect, hr, hl]

theorem effect_dir_apply (S : Set V) (s : PRState V) (x y : V) :
    (effect N S s).dir x y = if x ∈ S ∧ y ∈ revSet N s x then .out
      else if y ∈ S ∧ x ∈ revSet N s y then .inc else s.dir x y := rfl

theorem effect_list_apply (S : Set V) (s : PRState V) (x : V) :
    (effect N S s).list x =
      if x ∈ S then ∅ else s.list x ∪ {y | y ∈ S ∧ x ∈ revSet N s y} := rfl

theorem effect_empty (s : PRState V) : effect N ∅ s = s := by
  ext x y <;> simp [effect]

/-- Executing `reverse(insert a S)` is executing `reverse({a})` and then `reverse(S)`, when `a`
is not adjacent to any node of `S`. -/
theorem effect_insert {a : V} {S : Set V} (ha : a ∉ S) (hind : ∀ x ∈ S, ¬ N.Adj a x)
    (s : PRState V) : effect N (insert a S) s = effect N S (effect N {a} s) := by
  have hnr : ∀ x ∈ S, x ∉ revSet N s a := fun x hx h => hind x hx (revSet_subset s a h)
  have hnr' : ∀ x ∈ S, a ∉ revSet N s x := fun x hx h =>
    hind x hx (Network.adj_comm.mp (revSet_subset s x h))
  have hl1 : ∀ x ∈ S, (effect N {a} s).list x = s.list x := by
    intro x hx
    have hxa : x ≠ a := fun h => ha (h ▸ hx)
    rw [effect_list_of_notMem (by simpa using hxa)]
    ext y; simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff, or_iff_left_iff_imp]
    rintro ⟨rfl, h⟩; exact absurd h (hnr x hx)
  have hr1 : ∀ x ∈ S, revSet N (effect N {a} s) x = revSet N s x := fun x hx => by
    simp [revSet, hl1 x hx]
  ext x y
  · rw [effect_dir_apply, effect_dir_apply, effect_dir_apply]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases hxS : x ∈ S <;> by_cases hyS : y ∈ S
    · have hxa : x ≠ a := fun h => ha (h ▸ hxS)
      have hya : y ≠ a := fun h => ha (h ▸ hyS)
      simp [hxS, hyS, hr1 x hxS, hr1 y hyS, hxa, hya]
    · have hxa : x ≠ a := fun h => ha (h ▸ hxS)
      by_cases hya : y = a
      · subst hya; simp [hxS, hyS, hxa, hr1 x hxS, hnr x hxS, hnr' x hxS]
      · simp [hxS, hyS, hxa, hya, hr1 x hxS]
    · have hya : y ≠ a := fun h => ha (h ▸ hyS)
      by_cases hxa : x = a
      · subst hxa; simp [hxS, hyS, hya, hr1 y hyS, hnr y hyS, hnr' y hyS]
      · simp [hxS, hyS, hxa, hya, hr1 y hyS]
    · simp [hxS, hyS]
  · rw [effect_list_apply, effect_list_apply, effect_list_apply]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases hxS : x ∈ S
    · simp [hxS]
    · by_cases hxa : x = a
      · subst hxa
        simp only [hxS, or_false, ite_true, ite_false, Set.mem_empty_iff_false,
          Set.empty_union, Set.mem_ofPred_eq, false_iff, not_and]
        intro hyS
        rw [hr1 y hyS]; exact hnr' y hyS
      · simp only [hxS, hxa, or_false, ite_false, Set.mem_union, Set.mem_ofPred_eq]
        constructor
        · rintro (h | ⟨rfl | hyS, h⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr ⟨rfl, h⟩)
          · exact Or.inr ⟨hyS, by rw [hr1 _ hyS]; exact h⟩
        · rintro ((h | ⟨rfl, h⟩) | ⟨hyS, h⟩)
          · exact Or.inl h
          · exact Or.inr ⟨Or.inl rfl, h⟩
          · exact Or.inr ⟨Or.inr hyS, by rw [← hr1 _ hyS]; exact h⟩

end PR

/-! ### Section 5.2: `PR → OneStepPR` -/

variable (N) in
/-- The relation `R0` of Section 5.2: `s.G' = t.G'` and `s.list[u] = t.list[u]` for all `u`. -/
def R0 (s t : PRState V) : Prop := arcs N s.dir = arcs N t.dir ∧ s.list = t.list

/-- Lemma 5.1 (a) of [Radeva–Lynch]. -/
theorem lemma_5_1_a : R0 N (PR.init N) (PR.init N) := ⟨rfl, rfl⟩

/-- Simulating a parallel step by single steps (the core of Lemma 5.1 (b)). -/
theorem simulate_parallel {S : Set V} (hS : S.Finite) :
    (∀ x ∈ S, ∀ y ∈ S, ¬ N.Adj x y) → N.dest ∉ S → ∀ s t : PRState V,
      (∀ u ∈ S, IsSink N s.dir u) → R0 N s t →
      ∃ t', Relation.ReflTransGen (OneStepPR.Step N) t t' ∧ R0 N (PR.effect N S s) t' := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    intro _ _ s t _ hst
    exact ⟨t, .refl, by rw [PR.effect_empty]; exact hst⟩
  | @insert a S ha _ ih =>
    intro hind hdest s t hsink hst
    have hindS : ∀ x ∈ S, ∀ y ∈ S, ¬ N.Adj x y := fun x hx y hy =>
      hind x (Set.mem_insert_of_mem a hx) y (Set.mem_insert_of_mem a hy)
    have hna : ∀ x ∈ S, ¬ N.Adj a x := fun x hx =>
      hind a (Set.mem_insert a S) x (Set.mem_insert_of_mem a hx)
    have hsa : IsSink N t.dir a := (isSink_congr hst.1).mp (hsink a (Set.mem_insert a S))
    have hstep : OneStepPR.Step N t (PR.effect N {a} t) :=
      ⟨a, fun h => hdest (h ▸ Set.mem_insert a S), hsa, rfl⟩
    have h1 := PR.effect_congr (S := {a}) hst.1 hst.2
    have hsink1 : ∀ u ∈ S, IsSink N (PR.effect N {a} s).dir u := by
      intro u hu v hv
      have hua : u ∉ ({a} : Set V) := by
        simp only [Set.mem_singleton_iff]; rintro rfl; exact ha hu
      rw [PR.effect_dir_of_notMem hua]
      have : ¬ (v ∈ ({a} : Set V) ∧ u ∈ PR.revSet N s v) := by
        rintro ⟨hv', hu'⟩
        rw [Set.mem_singleton_iff] at hv'; subst hv'
        exact hna u hu (PR.revSet_subset s _ hu')
      rw [ite_eq_right this]
      exact hsink u (Set.mem_insert_of_mem a hu) v hv
    obtain ⟨t', ht', hR⟩ := ih hindS (fun h => hdest (Set.mem_insert_of_mem a h)) _ _ hsink1 h1
    refine ⟨t', .head hstep ht', ?_⟩
    rw [PR.effect_insert ha hna]; exact hR

/-- Lemma 5.1 (b) of [Radeva–Lynch]: for `s` reachable in `PR`, `(s, t) ∈ R0` and a step
`(s, s')` of `PR`, there is a finite sequence of steps of `OneStepPR` from `t` to some `t'` with
`(s', t') ∈ R0`. (Reachability of `t` is not needed.) -/
theorem lemma_5_1_b [Finite V] {s s' t : PRState V} (hs : PR.Reachable N s) (hst : R0 N s t)
    (hstep : PR.Step N s s') :
    ∃ t', Relation.ReflTransGen (OneStepPR.Step N) t t' ∧ R0 N s' t' := by
  obtain ⟨S, -, hdest, hsink, rfl⟩ := hstep
  have hc := PR.consistent_of_reachable hs
  exact simulate_parallel S.toFinite
    (fun x hx y hy hxy => hc.not_both_sinks hxy (hsink x hx) (hsink y hy)) hdest s t hsink hst

/-- Theorem 5.2 of [Radeva–Lynch]: for every reachable state `s` of `PR` there is a reachable
state `t` of `OneStepPR` with `(s, t) ∈ R0`. -/
theorem thm_5_2 [Finite V] {s : PRState V} (hs : PR.Reachable N s) :
    ∃ t, OneStepPR.Reachable N t ∧ R0 N s t := by
  induction hs with
  | refl => exact ⟨_, .refl, lemma_5_1_a⟩
  | @tail s s' hs hstep ih =>
    obtain ⟨t, ht, hst⟩ := ih
    obtain ⟨t', htt', hst'⟩ := lemma_5_1_b hs hst hstep
    exact ⟨t', ht.trans htt', hst'⟩

/-! ### Section 5.3: `OneStepPR → NewPR` -/

variable (N) in
/-- The relation `R` of Section 5.3: `s.G' = t.G'`; if `t.parity[u] = even` then
`s.list[u] ⊆ out-nbrsᵤ`; if `t.parity[u] = odd` then `s.list[u] ⊆ in-nbrsᵤ`. -/
def Rel (s : PRState V) (t : NewPRState V) : Prop :=
  arcs N s.dir = arcs N t.dir ∧
    (∀ u, Even (t.count u) → s.list u ⊆ N.outNbrs u) ∧
    (∀ u, Odd (t.count u) → s.list u ⊆ N.inNbrs u)

/-- Lemma 5.3 (a) of [Radeva–Lynch]. -/
theorem lemma_5_3_a : Rel N (PR.init N) (NewPR.init N) :=
  ⟨rfl, fun _ _ => Set.empty_subset _, fun _ _ => Set.empty_subset _⟩

/-- Claim 5.4 of [Radeva–Lynch] (inside the proof of Lemma 5.3): if `w` is a sink and its
neighbour `u` has even parity, then `w ∈ out-nbrsᵤ`. -/
theorem claim_5_4_even {t : NewPRState V} (ht : NewPR.Reachable N t) {u w : V}
    (hadj : N.Adj u w) (hw : IsSink N t.dir w) (hu : Even (t.count u)) : N.init u w := by
  rcases hadj with h | h
  · exact h
  · exfalso
    rcases Nat.even_or_odd (t.count w) with hwe | hwo
    · -- Invariant 4.1 (a): the edge would point from `w` to `u`
      have := ((NewPR.inv_4_1 ht h).1 hwe hu).2
      rw [hw u (Or.inl h)] at this; exact absurd this (by simp)
    · -- Invariant 4.2 (c): `count[w] = count[u]`, contradicting the parities
      have := (NewPR.inv_4_2 ht (Or.inr h)).2.2.1 hu h
      rw [this] at hwo; exact (Nat.not_even_iff_odd.mpr hwo) hu

/-- Claim 5.4, the symmetric part (used in "Part 3" of the proof of Lemma 5.3). -/
theorem claim_5_4_odd {t : NewPRState V} (ht : NewPR.Reachable N t) {u w : V}
    (hadj : N.Adj u w) (hw : IsSink N t.dir w) (hu : Odd (t.count u)) : N.init w u := by
  rcases hadj with h | h
  · exfalso
    rcases Nat.even_or_odd (t.count w) with hwe | hwo
    · have := (NewPR.inv_4_2 ht (Or.inl h)).2.1 hu h
      rw [this] at hwe; exact (Nat.not_even_iff_odd.mpr hu) hwe
    · have := ((NewPR.inv_4_1 ht h).2 hu hwo).2
      rw [hw u (Or.inr h)] at this; exact absurd this (by simp)
  · exact h

theorem PR.revSet_eq_nbrs {s : PRState V} {u : V}
    (h : s.list u = ∅ ∨ s.list u = N.nbrs u) : PR.revSet N s u = N.nbrs u := by
  rcases h with h | h
  · simp [PR.revSet, h]
  · simp [PR.revSet, h]

theorem PR.revSet_eq_diff {s : PRState V} {u : V} (h : s.list u ≠ N.nbrs u) :
    PR.revSet N s u = N.nbrs u \ s.list u := by
  simp [PR.revSet, h]

/-- The `NewPR` side of Lemma 5.3 (b): a sink `w` can reverse exactly the edges to the set of
its parity (one step), or, if that set is empty, after a dummy step the edges to the other set
(two steps). -/
theorem NewPR.exists_steps {t : NewPRState V} {w : V} (hwd : w ≠ N.dest)
    (hw : IsSink N t.dir w) (X : Set V)
    (hX : (NewPR.revSet N t w).Nonempty ∧ X = NewPR.revSet N t w ∨
      NewPR.revSet N t w = ∅ ∧
        X = (if Even (t.count w) then N.outNbrs w else N.inNbrs w)) :
    ∃ t', Relation.ReflTransGen (NewPR.Step N) t t' ∧ t'.dir = flipAt t.dir w X ∧
      ∀ u, u ≠ w → t'.count u = t.count u := by
  rcases hX with ⟨-, rfl⟩ | ⟨h0, rfl⟩
  · refine ⟨_, .single ⟨w, hwd, hw, rfl⟩, rfl, fun u hu => ?_⟩
    simp [NewPR.effect, hu]
  · set t1 := NewPR.effect N w t with ht1
    have hd1 : t1.dir = t.dir := by simp [t1, NewPR.effect, h0]
    have hw1 : IsSink N t1.dir w := hd1 ▸ hw
    have hr1 : NewPR.revSet N t1 w =
        (if Even (t.count w) then N.outNbrs w else N.inNbrs w) := by
      by_cases he : Even (t.count w)
      · have : ¬ Even (t1.count w) := by simp [t1, NewPR.effect, Nat.even_add_one, he]
        simp [NewPR.revSet, this, he]
      · have : Even (t1.count w) := by simp [t1, NewPR.effect, Nat.even_add_one, he]
        simp [NewPR.revSet, this, he]
    refine ⟨NewPR.effect N w t1, .tail (.single ⟨w, hwd, hw, rfl⟩) ⟨w, hwd, hw1, rfl⟩, ?_, ?_⟩
    · simp only [NewPR.effect, hr1, ← hd1]
    · intro u hu
      simp [NewPR.effect, t1, hu]

/-- Lemma 5.3 (b) of [Radeva–Lynch]: for reachable `s` of `OneStepPR` and `t` of `NewPR` with
`(s, t) ∈ R`, and a step `(s, s')` of `OneStepPR`, there is a finite sequence of steps of
`NewPR` from `t` to some `t'` with `(s', t') ∈ R`. (The sequence is one or two `reverse(w)`
steps, but not always the one the paper prescribes; see `README.md`.) -/
theorem lemma_5_3_b {s s' : PRState V} {t : NewPRState V} (hs : OneStepPR.Reachable N s)
    (ht : NewPR.Reachable N t) (hst : Rel N s t) (hstep : OneStepPR.Step N s s') :
    ∃ t', Relation.ReflTransGen (NewPR.Step N) t t' ∧ Rel N s' t' := by
  obtain ⟨w, hwd, hws, rfl⟩ := hstep
  obtain ⟨harcs, heven, hodd⟩ := hst
  have hsPR := hs.toPR
  have hwt : IsSink N t.dir w := (isSink_congr harcs).mp hws
  have hlist := PR.cor_3_4 hsPR hws
  have hdisj : ∀ v, v ∈ N.inNbrs w → v ∉ N.outNbrs w := fun _ h =>
    Network.not_mem_outNbrs_of_mem_inNbrs h
  -- the set reversed by `w` in `OneStepPR` is one that `NewPR` can reverse in one or two steps
  have hX : (NewPR.revSet N t w).Nonempty ∧ PR.revSet N s w = NewPR.revSet N t w ∨
      NewPR.revSet N t w = ∅ ∧ PR.revSet N s w =
        (if Even (t.count w) then N.outNbrs w else N.inNbrs w) := by
    rcases Nat.even_or_odd (t.count w) with he | ho
    · have hsub := heven w he
      have hr : NewPR.revSet N t w = N.inNbrs w := by simp [NewPR.revSet, he]
      simp only [hr, he, ite_true]
      rcases (N.inNbrs w).eq_empty_or_nonempty with hin | hin
      · -- `in-nbrs_w = ∅`: `w` reverses all its edges, i.e. its `out-nbrs`
        right
        refine ⟨hin, ?_⟩
        have hn : N.nbrs w = N.outNbrs w := by rw [Network.nbrs_eq_union, hin, Set.empty_union]
        rw [PR.revSet_eq_nbrs, hn]
        rcases hlist with h | h
        · exact Or.inl (h.trans hin)
        · exact Or.inr (h.trans hn.symm)
      · left
        refine ⟨hin, ?_⟩
        have hlo : s.list w = N.outNbrs w := by
          rcases hlist with h | h
          · exfalso
            obtain ⟨v, hv⟩ := hin
            exact hdisj v hv (hsub (h ▸ hv))
          · exact h
        have hne : s.list w ≠ N.nbrs w := by
          intro h
          obtain ⟨v, hv⟩ := hin
          have : v ∈ s.list w := h ▸ Network.inNbrs_subset_nbrs w hv
          exact hdisj v hv (hlo ▸ this)
        rw [PR.revSet_eq_diff hne, hlo, Network.nbrs_diff_outNbrs]
    · have hsub := hodd w ho
      have hne' : ¬ Even (t.count w) := Nat.not_even_iff_odd.mpr ho
      have hr : NewPR.revSet N t w = N.outNbrs w := by simp [NewPR.revSet, hne']
      simp only [hr, hne', ite_false]
      rcases (N.outNbrs w).eq_empty_or_nonempty with hout | hout
      · right
        refine ⟨hout, ?_⟩
        have hn : N.nbrs w = N.inNbrs w := by rw [Network.nbrs_eq_union, hout, Set.union_empty]
        rw [PR.revSet_eq_nbrs, hn]
        rcases hlist with h | h
        · exact Or.inr (h.trans hn.symm)
        · exact Or.inl (h.trans hout)
      · left
        refine ⟨hout, ?_⟩
        have hli : s.list w = N.inNbrs w := by
          rcases hlist with h | h
          · exact h
          · exfalso
            obtain ⟨v, hv⟩ := hout
            exact hdisj v (hsub (h ▸ hv)) hv
        have hne : s.list w ≠ N.nbrs w := by
          intro h
          obtain ⟨v, hv⟩ := hout
          have : v ∈ s.list w := h ▸ Network.outNbrs_subset_nbrs w hv
          exact hdisj v (hli ▸ this) hv
        rw [PR.revSet_eq_diff hne, hli, Network.nbrs_diff_inNbrs]
  obtain ⟨t', htt', hdir, hcount⟩ := NewPR.exists_steps hwd hwt _ hX
  refine ⟨t', htt', ?_, ?_, ?_⟩
  · -- Part 1: the same edges are reversed
    rw [PR.effect_singleton_dir, hdir]
    exact arcs_flipAt_congr harcs w _
  · -- Part 2
    intro u hu
    by_cases huw : u = w
    · subst huw; simp [PR.effect]
    · rw [hcount u huw] at hu
      rw [PR.effect_list_of_notMem (by simpa using huw)]
      refine Set.union_subset (heven u hu) ?_
      rintro y ⟨hy, hyu⟩
      rw [Set.mem_singleton_iff] at hy; subst hy
      exact claim_5_4_even ht (Network.adj_comm.mp (PR.revSet_subset s _ hyu)) hwt hu
  · -- Part 3
    intro u hu
    by_cases huw : u = w
    · subst huw; simp [PR.effect]
    · rw [hcount u huw] at hu
      rw [PR.effect_list_of_notMem (by simpa using huw)]
      refine Set.union_subset (hodd u hu) ?_
      rintro y ⟨hy, hyu⟩
      rw [Set.mem_singleton_iff] at hy; subst hy
      exact claim_5_4_odd ht (Network.adj_comm.mp (PR.revSet_subset s _ hyu)) hwt hu

/-- Theorem 5.4 of [Radeva–Lynch]: for every reachable state `s` of `OneStepPR` there is a
reachable state `t` of `NewPR` with `(s, t) ∈ R`. -/
theorem thm_5_4 {s : PRState V} (hs : OneStepPR.Reachable N s) :
    ∃ t, NewPR.Reachable N t ∧ Rel N s t := by
  induction hs with
  | refl => exact ⟨_, .refl, lemma_5_3_a⟩
  | @tail s s' hs hstep ih =>
    obtain ⟨t, ht, hst⟩ := ih
    obtain ⟨t', htt', hst'⟩ := lemma_5_3_b hs ht hst hstep
    exact ⟨t', ht.trans htt', hst'⟩

/-- Theorem 5.5 of [Radeva–Lynch]: in any reachable state `s` of `PR` (Gafni–Bertsekas partial
reversal) the directed graph `s.G'` is acyclic. -/
theorem thm_5_5 [Finite V] {s : PRState V} (hs : PR.Reachable N s) :
    IsAcyclic (arcs N s.dir) := by
  obtain ⟨r, hr, hsr⟩ := thm_5_2 hs
  obtain ⟨t, ht, hrt⟩ := thm_5_4 hr
  rw [hsr.1, hrt.1]
  exact NewPR.thm_4_3 ht

/-- `OneStepPR` keeps the graph acyclic too (no finiteness needed). -/
theorem OneStepPR.acyclic {s : PRState V} (hs : OneStepPR.Reachable N s) :
    IsAcyclic (arcs N s.dir) := by
  obtain ⟨t, ht, hst⟩ := thm_5_4 hs
  rw [hst.1]
  exact NewPR.thm_4_3 ht

end Podc.PartialReversalAcyclicity

end
