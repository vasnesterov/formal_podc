import Papers.PODC2020.RoundBasedKSetTopology.Defs

/-!
# Basic facts on domination and covering numbers

Elementary lemmas used throughout: monotonicity of `Out`, specifications of the `sInf`/`sSup`
definitions of `γ`, `γ^eq`, `cov`, relabelings, "lower sets" of processes (the `i` processes
with the smallest inputs), and the "decide the minimum received value" algorithm.
-/

namespace Podc.RoundBasedKSetTopology

open Cslib.HeardOf Finset

variable {α V : Type*}

/-! ### `Out` and domination -/

section Out

variable [Fintype α]

theorem mem_out {G : Graph α} {P : Finset α} {q : α} : q ∈ out G P ↔ ∃ p ∈ P, Hears G q p := by
  classical
  unfold out; convert Finset.mem_filter (s := univ) (a := q) using 1
  simp only [mem_univ, true_and]

theorem subset_out (G : Graph α) (P : Finset α) : P ⊆ out G P :=
  fun p hp => mem_out.2 ⟨p, hp, hears_self G p⟩

omit [Fintype α] in
theorem hears_mono {G H : Graph α} (h : G ≤ H) {q p : α} (hq : Hears G q p) : Hears H q p :=
  hq.imp id (fun e => h _ _ e)

theorem out_mono_graph {G H : Graph α} (h : G ≤ H) (P : Finset α) : out G P ⊆ out H P :=
  fun _ hq => by
    obtain ⟨p, hp, h'⟩ := mem_out.1 hq
    exact mem_out.2 ⟨p, hp, hears_mono h h'⟩

theorem out_mono {G : Graph α} {P Q : Finset α} (h : P ⊆ Q) : out G P ⊆ out G Q :=
  fun _ hq => by
    obtain ⟨p, hp, h'⟩ := mem_out.1 hq
    exact mem_out.2 ⟨p, h hp, h'⟩

theorem dominates_iff_out {G : Graph α} {P : Finset α} : Dominates G P ↔ out G P = univ := by
  constructor
  · intro h; exact eq_univ_of_forall fun q => mem_out.2 (h q)
  · intro h q; exact mem_out.1 (h ▸ mem_univ q)

omit [Fintype α] in
theorem Dominates.mono_graph {G H : Graph α} {P : Finset α} (hP : Dominates G P) (h : G ≤ H) :
    Dominates H P := fun q => by
  obtain ⟨p, hp, h'⟩ := hP q
  exact ⟨p, hp, hears_mono h h'⟩

omit [Fintype α] in
theorem Dominates.mono {G : Graph α} {P Q : Finset α} (hP : Dominates G P) (h : P ⊆ Q) :
    Dominates G Q := fun q => by
  obtain ⟨p, hp, h'⟩ := hP q
  exact ⟨p, h hp, h'⟩

theorem dominates_univ (G : Graph α) : Dominates G univ := fun q => ⟨q, mem_univ q, hears_self G q⟩

omit [Fintype α] in
theorem Dominates.nonempty [Nonempty α] {G : Graph α} {P : Finset α} (hP : Dominates G P) :
    P.Nonempty := by
  obtain ⟨p, hp, -⟩ := hP (Classical.arbitrary α)
  exact ⟨p, hp⟩

end Out

/-! ### Specifications of the combinatorial numbers -/

section Numbers

variable [Fintype α]

theorem exists_dominating_card_domNum (G : Graph α) :
    ∃ P : Finset α, Dominates G P ∧ P.card = domNum G := by
  rcases isEmpty_or_nonempty α with hα | hα
  · refine ⟨∅, fun q => isEmptyElim q, ?_⟩
    have : {i | 1 ≤ i ∧ i ≤ Fintype.card α ∧ ∃ P : Finset α, P.card = i ∧ Dominates G P} = ∅ := by
      ext i; simp only [Fintype.card_eq_zero, Set.mem_empty_iff_false, iff_false]
      intro h; exact absurd h.2.1 (by have := h.1; omega)
    unfold domNum; rw [this]; simp
  · have hne : Set.Nonempty
        {i | 1 ≤ i ∧ i ≤ Fintype.card α ∧ ∃ P : Finset α, P.card = i ∧ Dominates G P} := ⟨Fintype.card α, Fintype.card_pos, le_rfl, univ, card_univ, dominates_univ G⟩
    obtain ⟨-, -, P, hP, hd⟩ := Nat.sInf_mem hne
    exact ⟨P, hd, hP⟩

theorem domNum_le_card [Nonempty α] {G : Graph α} {P : Finset α} (hP : Dominates G P) :
    domNum G ≤ P.card :=
  Nat.sInf_le ⟨card_pos.2 hP.nonempty, card_le_univ P, P, rfl, hP⟩

/-- Every set of at least `γ^eq(G)` processes dominates `G`. -/
theorem dominates_of_eqDomNum_le {G : Graph α} {P : Finset α} (h : eqDomNum G ≤ P.card) :
    Dominates G P := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact fun q => isEmptyElim q
  have hne : Set.Nonempty
      {i | 1 ≤ i ∧ i ≤ Fintype.card α ∧ ∀ P : Finset α, P.card = i → Dominates G P} := ⟨Fintype.card α, Fintype.card_pos, le_rfl, fun P hP =>
        (eq_univ_of_card P hP) ▸ dominates_univ G⟩
  obtain ⟨-, -, hall⟩ := Nat.sInf_mem hne
  obtain ⟨Q, hQP, hQ⟩ := exists_subset_card_eq h
  exact (hall Q hQ).mono hQP

theorem eqDomNum_le_card (G : Graph α) : eqDomNum G ≤ Fintype.card α := by
  rcases Set.eq_empty_or_nonempty
    {i | 1 ≤ i ∧ i ≤ Fintype.card α ∧ ∀ P : Finset α, P.card = i → Dominates G P} with h | h
  · simp [eqDomNum, h]
  · exact (Nat.sInf_mem h).2.1

theorem eqDomNum_le_eqDomNumSet {S : Set (Graph α)} {G : Graph α} (hG : G ∈ S) :
    eqDomNum G ≤ eqDomNumSet S :=
  le_csSup ⟨Fintype.card α, by rintro _ ⟨H, -, rfl⟩; exact eqDomNum_le_card H⟩ ⟨G, hG, rfl⟩

theorem eqDomNumSet_le_card (S : Set (Graph α)) : eqDomNumSet S ≤ Fintype.card α := by
  rcases (eqDomNum '' S).eq_empty_or_nonempty with h | h
  · simp [eqDomNumSet, h]
  · exact csSup_le h (by rintro _ ⟨H, -, rfl⟩; exact eqDomNum_le_card H)

/-- Every set of at least `γ^eq(S)` processes dominates every graph of `S`. -/
theorem dominates_of_eqDomNumSet_le {S : Set (Graph α)} {G : Graph α} (hG : G ∈ S)
    {P : Finset α} (h : eqDomNumSet S ≤ P.card) : Dominates G P :=
  dominates_of_eqDomNum_le ((eqDomNum_le_eqDomNumSet hG).trans h)

theorem cov_le_card_out {i : ℕ} (G : Graph α) {P : Finset α} (hP : P.card = i) :
    cov i G ≤ (out G P).card :=
  Nat.sInf_le ⟨P, hP, rfl⟩

theorem covSet_le_cov {i : ℕ} {S : Set (Graph α)} {G : Graph α} (hG : G ∈ S) :
    covSet i S ≤ cov i G :=
  Nat.sInf_le ⟨G, hG, rfl⟩

/-- `cov_i(G)` is attained (for `i ≤ n`). -/
theorem exists_card_out_eq_cov {i : ℕ} (G : Graph α) (hi : i ≤ Fintype.card α) :
    ∃ P : Finset α, P.card = i ∧ (out G P).card = cov i G := by
  obtain ⟨P, -, hP⟩ := exists_subset_card_eq (s := (univ : Finset α)) (by simpa using hi)
  exact Nat.sInf_mem (s := {c | ∃ P : Finset α, P.card = i ∧ (out G P).card = c})
    ⟨_, P, hP, rfl⟩

/-- Covering numbers are monotone in `i`. -/
theorem cov_mono {i j : ℕ} (G : Graph α) (hij : i ≤ j) (hj : j ≤ Fintype.card α) :
    cov i G ≤ cov j G := by
  obtain ⟨P, hP, hcov⟩ := exists_card_out_eq_cov G hj
  obtain ⟨Q, hQP, hQ⟩ := exists_subset_card_eq (hij.trans hP.ge)
  exact (cov_le_card_out G hQ).trans (hcov ▸ card_le_card (out_mono hQP))

theorem cov_le_card (i : ℕ) (G : Graph α) : cov i G ≤ Fintype.card α := by
  rcases Nat.lt_or_ge (Fintype.card α) i with h | h
  · have : {c | ∃ P : Finset α, P.card = i ∧ (out G P).card = c} = ∅ := by
      ext c; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨P, hP, -⟩; have := card_le_univ P; omega
    simp [cov, this]
  · obtain ⟨P, -, hP⟩ := exists_card_out_eq_cov G h
    exact hP ▸ card_le_univ _

theorem covSet_le_card (i : ℕ) (S : Set (Graph α)) : covSet i S ≤ Fintype.card α := by
  rcases (cov i '' S).eq_empty_or_nonempty with h | h
  · simp [covSet, h]
  · obtain ⟨_, G, hG, rfl⟩ := h
    exact (covSet_le_cov hG).trans (cov_le_card i G)

end Numbers

/-! ### Relabelings -/

section Relabel

theorem hears_relabel (π : Equiv.Perm α) (G : Graph α) (q p : α) :
    Hears (relabel π G) q p ↔ Hears G (π.symm q) (π.symm p) := by
  unfold Hears relabel
  rw [π.symm.injective.eq_iff]

theorem relabel_mono (π : Equiv.Perm α) {G H : Graph α} (h : G ≤ H) :
    relabel π G ≤ relabel π H := fun _ _ e => h _ _ e

variable [Fintype α]

theorem out_relabel (π : Equiv.Perm α) (G : Graph α) (P : Finset α) :
    out (relabel π G) P = (out G (P.map π.symm.toEmbedding)).map π.toEmbedding := by
  ext q
  rw [mem_map]
  constructor
  · intro hq
    obtain ⟨p, hp, h⟩ := mem_out.1 hq
    rw [hears_relabel] at h
    exact ⟨π.symm q, mem_out.2 ⟨π.symm p, mem_map_of_mem _ hp, h⟩, by simp⟩
  · rintro ⟨q', hq', rfl⟩
    obtain ⟨p', hp', h⟩ := mem_out.1 hq'
    obtain ⟨p, hp, rfl⟩ := mem_map.1 hp'
    exact mem_out.2 ⟨p, hp, by rw [hears_relabel]; simpa using h⟩

theorem card_out_relabel (π : Equiv.Perm α) (G : Graph α) (P : Finset α) :
    (out (relabel π G) P).card = (out G (P.map π.symm.toEmbedding)).card := by
  rw [out_relabel, card_map]

theorem dominates_relabel_iff (π : Equiv.Perm α) (G : Graph α) (P : Finset α) :
    Dominates (relabel π G) P ↔ Dominates G (P.map π.symm.toEmbedding) := by
  rw [dominates_iff_out, dominates_iff_out, out_relabel]
  constructor
  · intro h
    apply eq_univ_of_card
    rw [← card_map π.toEmbedding, h, card_univ]
  · intro h; rw [h]; exact eq_univ_of_card _ (by simp)

end Relabel

/-! ### Lower sets of processes -/

-- CSLib candidate: Cslib/Foundations/Data/Finset (lower sets w.r.t. a function)
/-- There is a set of `i` processes holding the `i` smallest inputs. -/
theorem exists_lowerSet [Fintype α] [LinearOrder V] (x : α → V) {i : ℕ}
    (hi : i ≤ Fintype.card α) :
    ∃ P : Finset α, P.card = i ∧ ∀ p ∈ P, ∀ q ∉ P, x p ≤ x q := by
  classical
  induction i with
  | zero => exact ⟨∅, rfl, by simp⟩
  | succ i ih =>
    obtain ⟨P, hP, hlow⟩ := ih (by omega)
    have hne : (univ \ P).Nonempty := by
      rw [← card_pos, card_sdiff_of_subset (subset_univ _), card_univ]; omega
    obtain ⟨m, hm, hmin⟩ := exists_min_image (univ \ P) x hne
    have hmP : m ∉ P := (mem_sdiff.1 hm).2
    refine ⟨insert m P, by rw [card_insert_of_notMem hmP, hP], ?_⟩
    intro p hp q hq
    rw [mem_insert, not_or] at hq
    rcases mem_insert.1 hp with rfl | hp
    · exact hmin q (mem_sdiff.2 ⟨mem_univ q, hq.2⟩)
    · exact hlow p hp q hq.2

/-! ### The "minimum received value" algorithm -/

theorem msgs_eq_some {G : Graph α} {x : α → V} {p q : α} {a : V} :
    msgs G x p q = some a ↔ Hears G p q ∧ x q = a := by
  classical
  unfold msgs; split_ifs with h <;> simp [h]

section MinAlg

variable [LinearOrder V] [Nonempty V]

/-- The values received from members of `D`. -/
def heardVals (D : Finset α) (v : α → Option V) : Finset V := D.biUnion fun q => (v q).toFinset

omit [Nonempty V] in
theorem mem_heardVals {D : Finset α} {v : α → Option V} {a : V} :
    a ∈ heardVals D v ↔ ∃ q ∈ D, v q = some a := by
  simp [heardVals, Option.mem_toFinset]

/-- The minimum of a finite set of values (an arbitrary value if empty). -/
noncomputable def minOf (s : Finset V) : V := if h : s.Nonempty then s.min' h else Classical.arbitrary V

/-- Decide the minimum value received from the members of `D` (the algorithm of Section 3). -/
noncomputable def minFrom (D : Finset α) : Decision α V := fun _ v => minOf (heardVals D v)

/-- If `p` hears some member of `D`, `minFrom D` makes `p` decide the input of a member of `D`
that it hears, and this value is at most every input it hears from `D`. -/
theorem minFrom_spec {D : Finset α} {G : Graph α} {x : α → V} {p : α}
    (h : ∃ q ∈ D, Hears G p q) :
    (∃ q ∈ D, Hears G p q ∧ minFrom D p (msgs G x p) = x q) ∧
      ∀ q ∈ D, Hears G p q → minFrom D p (msgs G x p) ≤ x q := by
  obtain ⟨q₀, hq₀, hh₀⟩ := h
  have hne : (heardVals D (msgs G x p)).Nonempty :=
    ⟨x q₀, mem_heardVals.2 ⟨q₀, hq₀, msgs_eq_some.2 ⟨hh₀, rfl⟩⟩⟩
  have hdef : minFrom D p (msgs G x p) = (heardVals D (msgs G x p)).min' hne := by
    simp [minFrom, minOf, hne]
  constructor
  · obtain ⟨q, hq, hv⟩ := mem_heardVals.1 (min'_mem _ hne)
    obtain ⟨hh, hx⟩ := msgs_eq_some.1 hv
    exact ⟨q, hq, hh, by rw [hdef, hx]⟩
  · intro q hq hh
    rw [hdef]
    exact min'_le _ _ (mem_heardVals.2 ⟨q, hq, msgs_eq_some.2 ⟨hh, rfl⟩⟩)

variable [Fintype α]

/-- Deciding the minimum received value is valid. -/
theorem minFrom_univ_valid (G : Graph α) (x : α → V) (p : α) :
    ∃ q, minFrom univ p (msgs G x p) = x q := by
  obtain ⟨⟨q, -, -, h⟩, -⟩ := minFrom_spec (D := univ) (G := G) (x := x) (p := p)
    ⟨p, mem_univ p, hears_self G p⟩
  exact ⟨q, h⟩

/-- **Key counting lemma.** With "decide the minimum received value", if `P` holds the `|P|`
smallest inputs, every process hearing `P` decides an input of `P`; hence at most
`|P| + (n - |Out_G(P)|)` values are decided. -/
theorem ncard_range_minFrom_le (G : Graph α) (x : α → V) {P : Finset α}
    (hlow : ∀ p ∈ P, ∀ q ∉ P, x p ≤ x q) :
    (Set.range fun p => minFrom univ p (msgs G x p)).ncard ≤
      P.card + (Fintype.card α - (out G P).card) := by
  classical
  set d := fun p => minFrom univ p (msgs G x p)
  have hsub : univ.image d ⊆ P.image x ∪ (univ \ out G P).image d := by
    intro a ha
    obtain ⟨p, -, rfl⟩ := mem_image.1 ha
    by_cases hp : p ∈ out G P
    · apply mem_union_left
      obtain ⟨q, hqP, hpq⟩ := mem_out.1 hp
      obtain ⟨⟨r, -, -, hr⟩, hmin⟩ := minFrom_spec (D := univ) (G := G) (x := x) (p := p)
        ⟨p, mem_univ p, hears_self G p⟩
      have hle : d p ≤ x q := hmin q (mem_univ q) hpq
      by_cases hrP : r ∈ P
      · exact mem_image.2 ⟨r, hrP, hr.symm⟩
      · have h1 : x q ≤ x r := hlow q hqP r hrP
        have h2 : x q ≤ d p := by simp only [d]; rw [hr]; exact h1
        exact mem_image.2 ⟨q, hqP, le_antisymm h2 hle⟩
    · exact mem_union_right _ (mem_image.2 ⟨p, mem_sdiff.2 ⟨mem_univ p, hp⟩, rfl⟩)
  have hrange : Set.range d = ↑(univ.image d) := by simp
  rw [hrange, Set.ncard_coe_finset]
  calc (univ.image d).card ≤ (P.image x ∪ (univ \ out G P).image d).card := card_le_card hsub
    _ ≤ (P.image x).card + ((univ \ out G P).image d).card := card_union_le _ _
    _ ≤ P.card + (univ \ out G P).card := add_le_add card_image_le card_image_le
    _ = P.card + (Fintype.card α - (out G P).card) := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ]

end MinAlg

end Podc.RoundBasedKSetTopology
