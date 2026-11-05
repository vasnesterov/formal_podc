import Papers.PODC2013.MessageAdversariesVsFD.Model

/-!
# Strongly correct processes (Section 2.2) and the claims made about them

* `InfReach.refl`, `InfReach.trans`: `⇝∞` is a preorder, so `↔∞` is an equivalence relation
  (Section 2.2).
* `SC_eq`: with finitely many processes, the strongly correct processes are exactly those whose
  messages are always eventually received (directly or not) by every process, as claimed in Part 2
  of the proof of Lemma 2.
* `mem_SC_of_source` (proof of Lemma 4: `S ⊆ SC`), `SC_nonempty_of_tour` (Part 2 of the proof of
  Lemma 2), `SC_nonempty_of_inter` (proof of Lemma 5: the intersection part of QUORUM alone
  implies `SC ≠ ∅`, so the liveness part of QUORUM is redundant).
* Facts used in the proof of Lemma 6: `eventually_no_edge_into_SC` (B) and
  `exists_SC_hears_of_quorum` (A).
-/

namespace Podc.MessageAdversariesVsFD

open Cslib.HeardOf (Graph Hears)
open Cslib.DynNet (Journey)

variable {P : Type} {p : ℕ → Graph P}

theorem InfReach.refl (p : ℕ → Graph P) (i : P) : InfReach p i i := fun r => ⟨r, .refl⟩

theorem InfReach.trans {i j k : P} (h₁ : InfReach p i j) (h₂ : InfReach p j k) :
    InfReach p i k := by
  intro r
  obtain ⟨t, ht⟩ := h₁ r
  obtain ⟨t', ht'⟩ := h₂ t
  exact ⟨t', ht.trans ht'⟩

/-- If `j` hears `i` at infinitely many rounds, then `i ⇝∞ j`. -/
theorem InfReach.of_frequently {i j : P} (h : ∀ r, ∃ t ≥ r, Hears (p t) j i) : InfReach p i j := by
  intro r
  obtain ⟨t, htr, hij⟩ := h r
  refine ⟨t + 1, Journey.trans (Journey.self htr) (.step .refl ?_)⟩
  rcases hij with rfl | h
  · exact Or.inl rfl
  · exact Or.inr h

/-- The equivalence class of `i` under `↔∞`, when `i` reaches everybody, is a source component. -/
theorem isSourceComp_of_forall {i : P} (hi : ∀ j, InfReach p i j) :
    IsSourceComp p {y | InfReach p y i} := by
  refine ⟨⟨i, InfReach.refl p i⟩, fun x hx y => ⟨fun hy => ⟨hx.trans (hi y), hy.trans (hi x)⟩,
    fun h => h.2.trans hx⟩, fun x hx y hy => hy.trans hx⟩

/-- A source component is the class of any of its elements. -/
theorem IsSourceComp.eq_class {X : Set P} (hX : IsSourceComp p X) {x : P} (hx : x ∈ X) :
    X = {y | InfReach p x y ∧ InfReach p y x} := by
  ext y; exact hX.2.1 x hx y

/-- With finitely many processes, every process is reached (`⇝∞`) from a minimal process, i.e. one
that reaches back every process reaching it. -/
theorem exists_minimal_reaching [Finite P] (j : P) :
    ∃ y, InfReach p y j ∧ ∀ z, InfReach p z y → InfReach p y z := by
  classical
  have := Fintype.ofFinite P
  let anc : P → Finset P := fun y => Finset.univ.filter fun z => InfReach p z y
  obtain ⟨y, hy, hmin⟩ := (Finset.univ.filter fun y => InfReach p y j).exists_min_image
    (fun y => (anc y).card) ⟨j, by simp [InfReach.refl]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy hmin
  refine ⟨y, hy, fun z hz => ?_⟩
  have hsub : anc z ⊆ anc y := by
    intro w hw; simp only [anc, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact hw.trans hz
  have hcard := hmin z (hz.trans hy)
  have heq : anc z = anc y := Finset.eq_of_subset_of_card_le hsub hcard
  have : y ∈ anc z := by rw [heq]; simp [anc, InfReach.refl]
  simpa [anc] using this

/-- The class of a minimal process is a source component. -/
theorem isSourceComp_of_minimal {y : P} (hy : ∀ z, InfReach p z y → InfReach p y z) :
    IsSourceComp p {z | InfReach p y z ∧ InfReach p z y} := by
  refine ⟨⟨y, InfReach.refl p y, InfReach.refl p y⟩, fun x hx z => ⟨fun hz => ?_, fun hz => ?_⟩,
    fun x hx z hz => ?_⟩
  · exact ⟨hx.2.trans hz.1, hz.2.trans hx.1⟩
  · exact ⟨hx.1.trans hz.1, hz.2.trans hx.2⟩
  · have hzy : InfReach p z y := hz.trans hx.2
    exact ⟨hy z hzy, hzy⟩

/-- **Characterization of the strongly correct processes.** With finitely many processes, `i` is
strongly correct iff `i ⇝∞ j` for every process `j`, i.e. the messages of `i` are always
eventually received (directly or indirectly) by every process (claimed in Part 2 of the proof of
Lemma 2). -/
theorem SC_eq [Finite P] (p : ℕ → Graph P) : SC p = {i | ∀ j, InfReach p i j} := by
  ext i
  constructor
  · rintro ⟨X, hX, hiX, huniq⟩ j
    obtain ⟨y, hyj, hy⟩ := exists_minimal_reaching (p := p) j
    have hY := isSourceComp_of_minimal hy
    have := huniq _ hY
    have hiY : i ∈ {z | InfReach p y z ∧ InfReach p z y} := by rw [this]; exact hiX
    exact hiY.2.trans hyj
  · intro hi
    refine ⟨_, isSourceComp_of_forall hi, InfReach.refl p i, fun Y hY => ?_⟩
    obtain ⟨y, hy⟩ := hY.1
    have hiY : i ∈ Y := hY.2.2 y hy i (hi y)
    rw [hY.eq_class hiY]
    ext z
    exact ⟨fun h => h.2, fun h => ⟨hi z, h⟩⟩

theorem mem_SC_iff [Finite P] {i : P} : i ∈ SC p ↔ ∀ j, InfReach p i j := by
  rw [SC_eq]; rfl

/-- Processes that reach (`⇝∞`) a strongly correct process are strongly correct. -/
theorem mem_SC_of_infReach [Finite P] {i j : P} (hj : j ∈ SC p) (h : InfReach p i j) :
    i ∈ SC p :=
  mem_SC_iff.2 fun k => h.trans (mem_SC_iff.1 hj k)

/-- A source in the sense of SOURCE is strongly correct (proof of Lemma 4: `S ⊆ SC`). -/
theorem mem_SC_of_source [Finite P] {s : P} {r₀ : ℕ} (h : ∀ t ≥ r₀, ∀ i, Hears (p t) i s) :
    s ∈ SC p :=
  mem_SC_iff.2 fun i => InfReach.of_frequently fun r => ⟨max r r₀, le_max_left _ _,
    h _ (le_max_right _ _) i⟩

theorem SC_nonempty_of_source [Finite P] (hp : p ∈ SOURCE) : (SC p).Nonempty := by
  obtain ⟨s, r₀, h⟩ := hp
  exact ⟨s, mem_SC_of_source h⟩

/-- Under TOUR, `⇝∞` is total (Part 2 of the proof of Lemma 2). -/
theorem infReach_total_of_tour (hp : p ∈ TOUR) (i j : P) : InfReach p i j ∨ InfReach p j i := by
  by_cases hij : i = j
  · subst hij; exact Or.inl (InfReach.refl p i)
  by_contra h
  push Not at h
  obtain ⟨h₁, h₂⟩ := h
  have k₁ : ¬ ∀ r, ∃ t ≥ r, Hears (p t) j i := fun hh => h₁ (InfReach.of_frequently hh)
  have k₂ : ¬ ∀ r, ∃ t ≥ r, Hears (p t) i j := fun hh => h₂ (InfReach.of_frequently hh)
  push Not at k₁ k₂
  obtain ⟨r₁, hr₁⟩ := k₁
  obtain ⟨r₂, hr₂⟩ := k₂
  rcases hp (max r₁ r₂) i j hij with h | h
  · exact hr₁ _ (le_max_left _ _) (Or.inr h)
  · exact hr₂ _ (le_max_right _ _) (Or.inr h)

/-- Under TOUR, there are strongly correct processes ("there is a single set `X` of strongly
correct process simulators", Part 2 of the proof of Lemma 2). -/
theorem SC_nonempty_of_tour [Finite P] [Nonempty P] (hp : p ∈ TOUR) : (SC p).Nonempty := by
  obtain ⟨j⟩ := ‹Nonempty P›
  obtain ⟨y, -, hy⟩ := exists_minimal_reaching (p := p) j
  refine ⟨y, mem_SC_iff.2 fun k => ?_⟩
  rcases infReach_total_of_tour hp y k with h | h
  · exact h
  · exact hy k h

/-- The intersection part of QUORUM alone implies `SC ≠ ∅` (proof of Lemma 5). In particular the
liveness conjunct `SC ≠ ∅` in the definition of QUORUM is redundant (`quorum_iff`). -/
theorem SC_nonempty_of_inter [Finite P] [Nonempty P]
    (h : ∀ i j t t', ∃ k, Hears (p t) i k ∧ Hears (p t') j k) : (SC p).Nonempty := by
  obtain ⟨j⟩ := ‹Nonempty P›
  obtain ⟨y, -, hy⟩ := exists_minimal_reaching (p := p) j
  refine ⟨y, mem_SC_iff.2 fun l => ?_⟩
  -- for every round `t`, some `k t` is heard by both `y` and `l` at round `t`
  choose k hk using fun t => h y l t t
  -- some `k₀` occurs infinitely often
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, ∀ r, ∃ t ≥ r, k t = k₀ := by
    by_contra hc
    push Not at hc
    choose R hR using hc
    classical
    have := Fintype.ofFinite P
    let r := Finset.univ.sup R
    exact hR (k r) r (Finset.le_sup (Finset.mem_univ _)) rfl
  have hky : InfReach p k₀ y := InfReach.of_frequently fun r => by
    obtain ⟨t, ht, rfl⟩ := hk₀ r; exact ⟨t, ht, (hk t).1⟩
  have hkl : InfReach p k₀ l := InfReach.of_frequently fun r => by
    obtain ⟨t, ht, rfl⟩ := hk₀ r; exact ⟨t, ht, (hk t).2⟩
  exact (hy k₀ hky).trans hkl

/-- The liveness part of QUORUM is implied by its intersection part (for `n ≥ 1`). -/
theorem quorum_iff [Finite P] [Nonempty P] :
    p ∈ QUORUM ↔ ∀ i j t t', ∃ k, Hears (p t) i k ∧ Hears (p t') j k :=
  ⟨fun h => h.1, fun h => ⟨h, SC_nonempty_of_inter h⟩⟩

/-- (B) in the proof of Lemma 6: after some round, no message from a weakly correct process is
received by a strongly correct process. -/
theorem eventually_no_edge_into_SC [Finite P] (p : ℕ → Graph P) :
    ∃ T, ∀ t ≥ T, ∀ j ∉ SC p, ∀ i ∈ SC p, ¬ p t j i := by
  classical
  have := Fintype.ofFinite P
  have key : ∀ j i, j ∉ SC p → i ∈ SC p → ∃ T, ∀ t ≥ T, ¬ p t j i := by
    intro j i hj hi
    by_contra hc
    push Not at hc
    exact hj (mem_SC_of_infReach hi (InfReach.of_frequently fun r => by
      obtain ⟨t, ht, h⟩ := hc r; exact ⟨t, ht, Or.inr h⟩))
  choose! T hT using key
  refine ⟨Finset.univ.sup fun j => Finset.univ.sup fun i => T j i, fun t ht j hj i hi => ?_⟩
  apply hT j i hj hi
  refine le_trans ?_ ht
  exact le_trans (Finset.le_sup (f := fun i => T j i) (Finset.mem_univ i))
    (Finset.le_sup (f := fun j => Finset.univ.sup fun i => T j i) (Finset.mem_univ j))

/-- (A) in the proof of Lemma 6: under QUORUM, at every round every process receives the message
of some strongly correct process. -/
theorem exists_SC_hears_of_quorum [Finite P] (hp : p ∈ QUORUM) (t : ℕ) (i : P) :
    ∃ k ∈ SC p, Hears (p t) i k := by
  obtain ⟨T, hT⟩ := eventually_no_edge_into_SC p
  obtain ⟨s, hs⟩ := hp.2
  obtain ⟨k, hki, hks⟩ := hp.1 i s t T
  refine ⟨k, ?_, hki⟩
  by_contra hk
  rcases hks with rfl | h
  · exact hk hs
  · exact hT T le_rfl k hk s hs h

end Podc.MessageAdversariesVsFD
