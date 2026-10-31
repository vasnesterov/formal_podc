import Mathlib

/-!
# Trust graphs and the inconsistency number

§2–3 of J. P. Bezerra, P. Kuznetsov, *How to Tame Multiple Spending in Decentralized
Cryptocurrencies* (PODC 2022, full version arXiv:2205.14076).

* `TrustModel P`: a quorum map `Q : P → Set (Finset P)` and a fault model `F : Set (Finset P)`;
  the paper's standing assumptions are the separate predicates `SelfMem` (`p ∈ Q` for every
  quorum `Q` of `p`) and `DownClosed` (inclusion-closed fault model).
* `trustGraph F S`: the graph `G_{F,S}` on the correct processes `Π − F`, with an edge `p — q`
  iff `S p ∩ S q ⊈ F`.
* `IsIndep F S C`: `C` (a set of processes) is an independent set of `G_{F,S}`;
  `card_le_indepNum`, `exists_isIndep_card_eq_indepNum` relate it to Mathlib's
  `SimpleGraph.indepNum`.
* `inconsistencyNumber T` (Definition 3.4): the largest independence number over all graphs
  `G_{F,S}`, `F ∈ T.F`, `S` a quorum map.
-/

namespace Podc.MultipleSpending

open Finset

variable {P : Type*}

/-- A trust model `(Q, F)`: a quorum map and a fault model. -/
structure TrustModel (P : Type*) where
  /-- `Q p` is the set of quorums of `p`. -/
  Q : P → Set (Finset P)
  /-- The fault model (adversary structure): the sets of processes that may be faulty. -/
  F : Set (Finset P)

namespace TrustModel

variable (T : TrustModel P)

/-- Every process belongs to each of its quorums (standing assumption of §2). -/
def SelfMem : Prop := ∀ p, ∀ Q ∈ T.Q p, p ∈ Q

/-- The fault model is inclusion-closed (standing assumption of §2). -/
def DownClosed : Prop := ∀ F ∈ T.F, ∀ F' ⊆ F, F' ∈ T.F

/-- Every process has at least one quorum (implicit in §3: otherwise there is no quorum map). -/
def HasQuorums : Prop := ∀ p, (T.Q p).Nonempty

/-- The family `𝒮` of quorum maps: `S p ∈ Q p` for every process `p`. -/
def QuorumMaps : Set (P → Finset P) := {S | ∀ p, S p ∈ T.Q p}

/-- `p` is live in `F`: it has a quorum without faulty processes. -/
def Live (F : Finset P) (p : P) : Prop := ∃ Q ∈ T.Q p, Disjoint Q F

theorem quorumMaps_nonempty (h : T.HasQuorums) : T.QuorumMaps.Nonempty :=
  ⟨fun p => (h p).some, fun p => (h p).some_mem⟩

end TrustModel

/-- A set all of whose finite subsets have at most `k` elements has at most `k` elements. -/
theorem encard_le_of_finset {α : Type*} {s : Set α} {k : ℕ}
    (h : ∀ D : Finset α, ↑D ⊆ s → D.card ≤ k) : s.encard ≤ k := by
  by_contra hlt
  push Not at hlt
  have : ((k + 1 : ℕ) : ℕ∞) ≤ s.encard := by
    rw [Nat.cast_add, Nat.cast_one]; exact Order.add_one_le_of_lt hlt
  obtain ⟨t, hts, ht⟩ := Set.exists_subset_encard_eq this
  have hfin : t.Finite := Set.finite_of_encard_eq_coe ht
  have hcard := h hfin.toFinset (by simpa using hts)
  rw [hfin.encard_eq_coe_toFinset_card] at ht
  have : hfin.toFinset.card = k + 1 := by exact_mod_cast ht
  omega

variable [DecidableEq P]

/-- The trust graph `G_{F,S}`: vertices are the correct processes `Π − F`, and two distinct
processes are adjacent iff their quorums intersect in a correct process. -/
def trustGraph (F : Finset P) (S : P → Finset P) : SimpleGraph {p // p ∉ F} where
  Adj p q := p ≠ q ∧ ¬ (S p ∩ S q ⊆ F)
  symm := ⟨fun p q h => ⟨h.1.symm, by rw [Finset.inter_comm]; exact h.2⟩⟩
  loopless := ⟨fun p h => h.1 rfl⟩

/-- `C` is an independent set of `G_{F,S}` (Definition 3.2), seen as a set of processes:
its members are correct and the quorums of any two distinct members meet only in `F`. -/
def IsIndep (F : Finset P) (S : P → Finset P) (C : Finset P) : Prop :=
  Disjoint C F ∧ ∀ p ∈ C, ∀ q ∈ C, p ≠ q → S p ∩ S q ⊆ F

variable [Fintype P]

theorem card_le_indepNum {F : Finset P} {S : P → Finset P} {C : Finset P}
    (h : IsIndep F S C) : C.card ≤ (trustGraph F S).indepNum := by
  classical
  let C' : Finset {p // p ∉ F} := C.subtype (· ∉ F)
  have hcard : C'.card = C.card := by
    simp only [C', Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem fun p hp => Finset.disjoint_left.mp h.1 hp
  rw [← hcard]
  apply SimpleGraph.IsIndepSet.card_le_indepNum
  intro p hp q hq hpq hadj
  simp only [C', Finset.mem_coe, Finset.mem_subtype] at hp hq
  exact hadj.2 (h.2 p hp q hq (fun e => hpq (Subtype.ext e)))

omit [Fintype P] in
theorem exists_isIndep_card_eq_indepNum (F : Finset P) (S : P → Finset P) :
    ∃ C, IsIndep F S C ∧ C.card = (trustGraph F S).indepNum := by
  obtain ⟨s, hs⟩ := (trustGraph F S).exists_isNIndepSet_indepNum
  refine ⟨s.map (Function.Embedding.subtype _), ⟨?_, ?_⟩, by rw [Finset.card_map, hs.card_eq]⟩
  · rw [Finset.disjoint_left]
    intro p hp
    obtain ⟨p', -, rfl⟩ := Finset.mem_map.mp hp
    exact p'.2
  · intro p hp q hq hpq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_map.mp hq
    by_contra hc
    have hne : p' ≠ q' := fun e => hpq (by rw [e])
    exact hs.isIndepSet (Finset.mem_coe.mpr hp') (Finset.mem_coe.mpr hq') hne ⟨hne, hc⟩

theorem indepNum_le_card (F : Finset P) (S : P → Finset P) :
    (trustGraph F S).indepNum ≤ Fintype.card P := by
  obtain ⟨C, -, hC⟩ := exists_isIndep_card_eq_indepNum F S
  rw [← hC]
  exact Finset.card_le_univ C

/-- The inconsistency number `λ(𝒢_{Q,F})` (Definition 3.4): the highest independence number of
a graph `G_{F,S}`, `F ∈ F`, `S ∈ 𝒮`. (If there is no such graph the paper's `max ∅` is
undefined; here it is `0`.) -/
noncomputable def inconsistencyNumber (T : TrustModel P) : ℕ :=
  sSup {k | ∃ F ∈ T.F, ∃ S ∈ T.QuorumMaps, (trustGraph F S).indepNum = k}

namespace TrustModel

variable (T : TrustModel P)

theorem bddAbove_indepNums :
    BddAbove {k | ∃ F ∈ T.F, ∃ S ∈ T.QuorumMaps, (trustGraph F S).indepNum = k} :=
  ⟨Fintype.card P, by rintro k ⟨F, -, S, -, rfl⟩; exact indepNum_le_card F S⟩

theorem indepNum_le_inconsistencyNumber {F : Finset P} (hF : F ∈ T.F) {S : P → Finset P}
    (hS : S ∈ T.QuorumMaps) : (trustGraph F S).indepNum ≤ inconsistencyNumber T :=
  le_csSup T.bddAbove_indepNums ⟨F, hF, S, hS, rfl⟩

/-- An independent set of some `G_{F,S}` has at most `λ` elements. -/
theorem card_le_inconsistencyNumber {F : Finset P} (hF : F ∈ T.F) {S : P → Finset P}
    (hS : S ∈ T.QuorumMaps) {C : Finset P} (hC : IsIndep F S C) :
    C.card ≤ inconsistencyNumber T :=
  (card_le_indepNum hC).trans (T.indepNum_le_inconsistencyNumber hF hS)

/-- Partial quorum maps suffice: if the members of `C` (correct for `F`) have quorums `R p`
pairwise intersecting only in `F`, then `|C| ≤ λ` (the other processes get arbitrary quorums). -/
theorem card_le_inconsistencyNumber_of_family (hQ : T.HasQuorums) {F : Finset P} (hF : F ∈ T.F)
    {C : Finset P} (hCF : Disjoint C F) (R : P → Finset P) (hR : ∀ p ∈ C, R p ∈ T.Q p)
    (hdisj : ∀ p ∈ C, ∀ q ∈ C, p ≠ q → R p ∩ R q ⊆ F) : C.card ≤ inconsistencyNumber T := by
  classical
  let S : P → Finset P := fun p => if p ∈ C then R p else (hQ p).some
  have hS : S ∈ T.QuorumMaps := fun p => by
    by_cases hp : p ∈ C
    · simp only [S, hp, ↓reduceIte]; exact hR p hp
    · simp only [S, hp, ↓reduceIte]; exact (hQ p).some_mem
  refine T.card_le_inconsistencyNumber hF hS ⟨hCF, fun p hp q hq hpq => ?_⟩
  simp only [S, hp, hq, ↓reduceIte]
  exact hdisj p hp q hq hpq

/-- `λ ≤ k` as soon as every independent set of every graph has at most `k` elements. -/
theorem inconsistencyNumber_le {k : ℕ}
    (h : ∀ F ∈ T.F, ∀ S ∈ T.QuorumMaps, ∀ C, IsIndep F S C → C.card ≤ k) :
    inconsistencyNumber T ≤ k := by
  apply csSup_le'
  rintro _ ⟨F, hF, S, hS, rfl⟩
  obtain ⟨C, hC, hcard⟩ := exists_isIndep_card_eq_indepNum F S
  rw [← hcard]
  exact h F hF S hS C hC

/-- The inconsistency number is attained (when the family of graphs is nonempty). -/
theorem exists_isIndep_card_eq_inconsistencyNumber (hF : T.F.Nonempty) (hQ : T.HasQuorums) :
    ∃ F ∈ T.F, ∃ S ∈ T.QuorumMaps, ∃ C, IsIndep F S C ∧ C.card = inconsistencyNumber T := by
  obtain ⟨F₀, hF₀⟩ := hF
  obtain ⟨S₀, hS₀⟩ := T.quorumMaps_nonempty hQ
  obtain ⟨F, hF, S, hS, hk⟩ := Nat.sSup_mem (s := {k | ∃ F ∈ T.F, ∃ S ∈ T.QuorumMaps, (trustGraph F S).indepNum = k})
    ⟨_, ⟨F₀, hF₀, S₀, hS₀, rfl⟩⟩ T.bddAbove_indepNums
  obtain ⟨C, hC, hcard⟩ := exists_isIndep_card_eq_indepNum F S
  exact ⟨F, hF, S, hS, C, hC, hcard.trans hk⟩

end TrustModel

end Podc.MultipleSpending
