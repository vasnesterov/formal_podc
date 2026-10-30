import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/AsymmetricQuorum.lean

/-!
# Asymmetric Byzantine quorum systems

Asymmetric trust in the sense of Damgård–Desmedt–Fitzi–Nielsen (ASIACRYPT 2007) and
Alpos–Cachin–Tackmann–Zanolini (*Asymmetric distributed trust*, Distributed Computing 2024):
every process `i` has its own fail-prone system `F i` and its own quorum system `Q i`.

* `star A` is `A*`, the collection of all subsets of members of `A`.
* `B3 F`: no two fail-prone sets of two processes together with a set they both foresee cover
  all processes.
* `IsQuorumSystem F Q`: *consistency* (two quorums of any two processes meet outside every set
  that both processes foresee) and *availability* (every fail-prone set of `i` avoids a quorum
  of `i`).
* `IsKernel Q i K`: `K` meets every quorum of `i`.
* For the actual faulty set `Fault` of an execution: `Wise F Fault i` (correct and `Fault` is
  foreseen by `i`), `IsGuild F Q Fault G` (wise members, each with a quorum inside `G`), and
  the maximal guild `maxGuild F Q Fault` (union of all guilds, itself a guild).

## Main lemmas

* `IsQuorumSystem.exists_mem_inter_notMem`: quorums of two wise processes share a correct
  process.
* `IsGuild.exists_mem_guild_of_quorum`: every quorum of a guild member contains a correct guild
  member.
* `IsQuorumSystem.isKernel_correct`: the correct members of a quorum of a wise process form a
  kernel for every wise process.
* `b3_canonical`, `isQuorumSystem_canonical`: one fail-prone set per process with its
  canonical quorum: both conditions reduce to pairwise intersection of the quorums.
-/

namespace Cslib.AsymmetricQuorum

variable {P : Type*}

/-- `A*`: all subsets of members of `A`. -/
def star (A : Set (Finset P)) : Set (Finset P) := {X | ∃ Y ∈ A, X ⊆ Y}

theorem mem_star {A : Set (Finset P)} {X : Finset P} : X ∈ star A ↔ ∃ Y ∈ A, X ⊆ Y := Iff.rfl

theorem subset_mem_star {A : Set (Finset P)} {Y : Finset P} (hY : Y ∈ A) : Y ∈ star A :=
  ⟨Y, hY, subset_rfl⟩

variable [DecidableEq P]

/-- The `B³` condition (Definition 2.3 of Amores-Sesar et al., from Alpos et al.):
`P ⊄ Fᵢ ∪ Fⱼ ∪ Fᵢⱼ` for all fail-prone sets `Fᵢ ∈ F i`, `Fⱼ ∈ F j`, `Fᵢⱼ ∈ (F i)* ∩ (F j)*`. -/
def B3 [Fintype P] (F : P → Set (Finset P)) : Prop :=
  ∀ i j, ∀ Fi ∈ F i, ∀ Fj ∈ F j, ∀ Fij ∈ star (F i) ∩ star (F j),
    ¬ (Finset.univ ⊆ Fi ∪ Fj ∪ Fij)

/-- An asymmetric Byzantine quorum system `Q` for the asymmetric fail-prone system `F`
(Definition 2.1 of Amores-Sesar et al.). -/
structure IsQuorumSystem (F Q : P → Set (Finset P)) : Prop where
  /-- Consistency: `Qᵢ ∩ Qⱼ ⊄ Fᵢⱼ` for every `Fᵢⱼ ∈ (F i)* ∩ (F j)*`. -/
  consistency : ∀ i j, ∀ Qi ∈ Q i, ∀ Qj ∈ Q j, ∀ Fij ∈ star (F i) ∩ star (F j), ¬ Qi ∩ Qj ⊆ Fij
  /-- Availability: every fail-prone set of `i` is disjoint from some quorum of `i`. -/
  availability : ∀ i, ∀ Fi ∈ F i, ∃ Qi ∈ Q i, Disjoint Fi Qi

/-- `K` is a kernel for `i`: it meets every quorum of `i`. -/
def IsKernel (Q : P → Set (Finset P)) (i : P) (K : Set P) : Prop :=
  ∀ Qi ∈ Q i, ∃ x ∈ Qi, x ∈ K

/-- A wise process: correct, and it foresees the actual faulty set `Fault`. -/
def Wise (F : P → Set (Finset P)) (Fault : Set P) (i : P) : Prop :=
  i ∉ Fault ∧ ∃ X ∈ F i, Fault ⊆ (X : Set P)

/-- A guild (Definition 2.2): a set of wise processes containing a quorum of each member. -/
def IsGuild (F Q : P → Set (Finset P)) (Fault : Set P) (G : Set P) : Prop :=
  (∀ i ∈ G, Wise F Fault i) ∧ ∀ i ∈ G, ∃ Qi ∈ Q i, (Qi : Set P) ⊆ G

/-- The maximal guild: the union of all guilds. -/
def maxGuild (F Q : P → Set (Finset P)) (Fault : Set P) : Set P :=
  ⋃₀ {G | IsGuild F Q Fault G}

omit [DecidableEq P] in
theorem isGuild_maxGuild (F Q : P → Set (Finset P)) (Fault : Set P) :
    IsGuild F Q Fault (maxGuild F Q Fault) := by
  constructor
  · rintro i ⟨G, hG, hi⟩
    exact hG.1 i hi
  · rintro i ⟨G, hG, hi⟩
    obtain ⟨Qi, hQi, hsub⟩ := hG.2 i hi
    exact ⟨Qi, hQi, hsub.trans (Set.subset_sUnion_of_mem hG)⟩

omit [DecidableEq P] in
theorem IsGuild.subset_maxGuild {F Q : P → Set (Finset P)} {Fault G : Set P}
    (hG : IsGuild F Q Fault G) : G ⊆ maxGuild F Q Fault :=
  Set.subset_sUnion_of_mem hG

omit [DecidableEq P] in
theorem IsGuild.notMem_fault {F Q : P → Set (Finset P)} {Fault G : Set P}
    (hG : IsGuild F Q Fault G) {i : P} (hi : i ∈ G) : i ∉ Fault :=
  (hG.1 i hi).1

/-- Quorums of two wise processes share a correct process. -/
theorem IsQuorumSystem.exists_mem_inter_notMem {F Q : P → Set (Finset P)}
    (hQ : IsQuorumSystem F Q) {Fault : Set P} {i j : P} (hi : Wise F Fault i)
    (hj : Wise F Fault j) {Qi Qj : Finset P} (hQi : Qi ∈ Q i) (hQj : Qj ∈ Q j) :
    ∃ x ∈ Qi, x ∈ Qj ∧ x ∉ Fault := by
  classical
  obtain ⟨_, X, hX, hFX⟩ := hi
  obtain ⟨_, Y, hY, hFY⟩ := hj
  set Fij := (Qi ∩ Qj).filter (· ∈ Fault)
  have hX' : Fij ⊆ X := fun x hx => by
    have := (Finset.mem_filter.1 hx).2; exact_mod_cast hFX this
  have hY' : Fij ⊆ Y := fun x hx => by
    have := (Finset.mem_filter.1 hx).2; exact_mod_cast hFY this
  have h := hQ.consistency i j Qi hQi Qj hQj Fij ⟨⟨X, hX, hX'⟩, ⟨Y, hY, hY'⟩⟩
  rw [Finset.not_subset] at h
  obtain ⟨x, hx, hxF⟩ := h
  rw [Finset.mem_inter] at hx
  exact ⟨x, hx.1, hx.2, fun h' => hxF (Finset.mem_filter.2 ⟨Finset.mem_inter.2 hx, h'⟩)⟩

/-- Every quorum of a guild member contains a correct guild member. -/
theorem IsGuild.exists_mem_guild_of_quorum {F Q : P → Set (Finset P)} (hQ : IsQuorumSystem F Q)
    {Fault G : Set P} (hG : IsGuild F Q Fault G) {i : P} (hi : i ∈ G) {Qi : Finset P}
    (hQi : Qi ∈ Q i) : ∃ x ∈ Qi, x ∈ G := by
  obtain ⟨Q', hQ', hsub⟩ := hG.2 i hi
  obtain ⟨x, hx, hx', -⟩ := hQ.exists_mem_inter_notMem (hG.1 i hi) (hG.1 i hi) hQi hQ'
  exact ⟨x, hx, hsub hx'⟩

/-- The correct members of a quorum of a wise process form a kernel for every wise process. -/
theorem IsQuorumSystem.isKernel_correct {F Q : P → Set (Finset P)} (hQ : IsQuorumSystem F Q)
    {Fault : Set P} {i j : P} (hi : Wise F Fault i) (hj : Wise F Fault j) {Qi : Finset P}
    (hQi : Qi ∈ Q i) : IsKernel Q j {x | x ∈ Qi ∧ x ∉ Fault} := by
  intro Qj hQj
  obtain ⟨x, hx, hx', hxF⟩ := hQ.exists_mem_inter_notMem hi hj hQi hQj
  exact ⟨x, hx', hx, hxF⟩

/-! ### One fail-prone set per process, canonical quorums -/

section Canonical

variable [Fintype P]

/-- The fail-prone system with the single fail-prone set `P \ q i` for every `i`. -/
def canonicalFailProne (q : P → Finset P) : P → Set (Finset P) := fun i => {Finset.univ \ q i}

/-- The quorum system with the single quorum `q i` for every `i`. -/
def canonicalQuorums (q : P → Finset P) : P → Set (Finset P) := fun i => {q i}

theorem b3_canonical {q : P → Finset P} (h : ∀ i j, (q i ∩ q j).Nonempty) :
    B3 (canonicalFailProne q) := by
  rintro i j Fi hFi Fj hFj Fij ⟨⟨X, hX, hXs⟩, _⟩ hcov
  simp only [canonicalFailProne, Set.mem_singleton_iff] at hFi hFj hX
  subst hFi hFj hX
  obtain ⟨x, hx⟩ := h i j
  rw [Finset.mem_inter] at hx
  have := hcov (Finset.mem_univ x)
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and] at this
  rcases this with (h1 | h1) | h1
  · exact h1 hx.1
  · exact h1 hx.2
  · have := hXs h1; simp [hx.1] at this

theorem isQuorumSystem_canonical {q : P → Finset P} (h : ∀ i j, (q i ∩ q j).Nonempty) :
    IsQuorumSystem (canonicalFailProne q) (canonicalQuorums q) where
  consistency := by
    rintro i j Qi hQi Qj hQj Fij ⟨⟨X, hX, hXs⟩, _⟩ hsub
    simp only [canonicalQuorums, canonicalFailProne, Set.mem_singleton_iff] at hQi hQj hX
    subst hQi hQj hX
    obtain ⟨x, hx⟩ := h i j
    have := hXs (hsub hx)
    rw [Finset.mem_inter] at hx
    simp [hx.1] at this
  availability := by
    intro i Fi hFi
    simp only [canonicalFailProne, Set.mem_singleton_iff] at hFi
    subst hFi
    exact ⟨q i, rfl, Finset.sdiff_disjoint⟩

/-- With canonical single quorums and no faults, every process is wise and the whole set of
processes is the maximal guild. -/
theorem isGuild_univ_canonical (q : P → Finset P) :
    IsGuild (canonicalFailProne q) (canonicalQuorums q) ∅ Set.univ :=
  ⟨fun i _ => ⟨Set.notMem_empty i, _, rfl, Set.empty_subset _⟩,
    fun i _ => ⟨q i, rfl, Set.subset_univ _⟩⟩

theorem maxGuild_canonical_empty (q : P → Finset P) :
    maxGuild (canonicalFailProne q) (canonicalQuorums q) ∅ = Set.univ :=
  Set.eq_univ_of_univ_subset (isGuild_univ_canonical q).subset_maxGuild

end Canonical

end Cslib.AsymmetricQuorum
