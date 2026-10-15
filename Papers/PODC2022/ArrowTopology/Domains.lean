import Papers.PODC2022.ArrowTopology.DomainBridge

/-!
# Domain restrictions for two voters and three alternatives (Section 4)

Concrete setting of Section 4 of S. Rajsbaum, A. Raventós-Pujol, *A Distributed Combinatorial
Topology Approach to Arrow's Impossibility Theorem*, PODC 2022 (and Section 4.3 of the full
version): two voters (`Fin 2`), alternatives `Alt = {A, B, C}`.

A profile is written `prof o₁ o₂` with `o₁ o₂ : Ord3` among the six orders `ABC, …, CBA`
(`BAC` = `B ≻ A ≻ C`). Domains are sets of profiles; the finite ones are given by lists of
`Prof2 = Ord3 × Ord3` (`dom L`).

All statements are stated with `AdmitsNonDictatorial` on `Set (Profile (Fin 2) Alt)`, and proved
by transferring to sign functions (`admitsNonDictatorial_iff_sign`) and deciding there with a
Boolean checker `admitsB` (`admitsNonDictatorial_dom_iff`; it enumerates the 64 sign functions
that are unanimous on the 6 unanimous vertices).

## Main results

* `not_admits_C1`, `not_admits_C2` (Sec. 4.1): the cylinders admit no non-dictatorial map.
* `prop41_admits`, `prop41_maximal` (PODC Prop. 4.1, first part): correct.
  `prop41_equal_blueEdge`: the "different blue edges" condition is needed.
* `prop41_moreover_false`, `not_admits_ABC_ACB`: the last sentence of Prop. 4.1 ("every domain
  contained in one of these maximal domains belongs to `D_T`") is **false**.
* Theorem 4.2 (PODC) is **false** for adjacent blue edges: `thm42_false`,
  `thm42_not_admits_of_adjacent`, explicit instance `thm42_counterexample`
  (`R₁ = (BAC, ACB)`, `R₂ = (CBA, ACB)`). It holds for disjoint blue edges (critical pairs):
  `thm42_admits_of_disjoint`, `thm42_maximal`. Its "moreover" part is false too:
  `thm42_moreover_false`.
* `paper_triple_example_not_critical`: the full version's example critical triple
  `((BAC, ACB), (BCA, ABC), (BCA, ACB))` has both of its first two profiles in `C₁`.
* `thm6` (full version, Theorem 6): the corrected characterization, for domains in which every
  pair is free: non-dictatorial maps exist iff the domain misses a critical pair or a critical
  triple.
-/

namespace Podc.ArrowTopology

open Cslib.SocialChoice

/-! ### Alternatives, orders, profiles -/

/-- The three alternatives. -/
inductive Alt | A | B | C
  deriving DecidableEq, Repr

instance : Fintype Alt := Fintype.ofList [.A, .B, .C] (by intro x; cases x <;> simp)

/-- `A, B, C` as a `ThreeAlts`: the pairs are `AB, BC, CA`. -/
def Alt.three : ThreeAlts Alt where
  x := .A
  y := .B
  z := .C
  hxy := by decide
  hyz := by decide
  hxz := by decide
  cover w := by cases w <;> simp

/-- The six strict orders on `{A, B, C}`, written top to bottom. -/
inductive Ord3 | ABC | ACB | BAC | BCA | CAB | CBA
  deriving DecidableEq, Repr

instance : Fintype Ord3 :=
  Fintype.ofList [.ABC, .ACB, .BAC, .BCA, .CAB, .CBA] (by intro x; cases x <;> simp)

namespace Ord3

/-- Position (`0` = top) of an alternative. -/
def rank : Ord3 → Alt → ℕ
  | ABC, .A => 0 | ABC, .B => 1 | ABC, .C => 2
  | ACB, .A => 0 | ACB, .C => 1 | ACB, .B => 2
  | BAC, .B => 0 | BAC, .A => 1 | BAC, .C => 2
  | BCA, .B => 0 | BCA, .C => 1 | BCA, .A => 2
  | CAB, .C => 0 | CAB, .A => 1 | CAB, .B => 2
  | CBA, .C => 0 | CBA, .B => 1 | CBA, .A => 2

/-- The order as a preference. -/
def toPref (o : Ord3) : Pref Alt where
  P a b := o.rank a < o.rank b
  irrefl _ := lt_irrefl _
  trans h1 h2 := lt_trans h1 h2
  total {a b} := by revert a b; cases o <;> decide

instance (o : Ord3) : DecidableRel o.toPref.P := fun a b =>
  inferInstanceAs (Decidable (o.rank a < o.rank b))

/-- Signs on `AB, BC, CA` (`true` = first above second). -/
def sgn : Ord3 → Fin 3 → Bool
  | ABC => ![true, true, false]
  | ACB => ![true, false, false]
  | BAC => ![false, true, false]
  | BCA => ![false, true, true]
  | CAB => ![true, false, true]
  | CBA => ![false, false, true]

theorem sgn_spec (o : Ord3) (j : Fin 3) :
    o.sgn j = decide (o.toPref.P (Alt.three.pr j).1 (Alt.three.pr j).2) := by
  revert j; cases o <;> decide

theorem sig1_toPref (o : Ord3) (j : Fin 3) : Alt.three.sig1 o.toPref j = o.sgn j := by
  rw [Bool.eq_iff_iff, ThreeAlts.sig1_eq_true_iff, sgn_spec, decide_eq_true_iff]

theorem toPref_injective : Function.Injective toPref := by
  intro o o' h
  have : ∀ j, o.sgn j = o'.sgn j := fun j => by rw [← sig1_toPref, ← sig1_toPref, h]
  clear h; revert this; revert o o'; decide

theorem exists_sgn_eq {b0 b1 b2 : Bool} (h : OutTri b0 b1 b2) :
    ∃ o : Ord3, o.sgn 0 = b0 ∧ o.sgn 1 = b1 ∧ o.sgn 2 = b2 := by
  revert h; revert b0 b1 b2; decide

/-- Every preference on `{A, B, C}` is one of the six orders. -/
theorem toPref_surjective : Function.Surjective toPref := by
  intro r
  obtain ⟨o, h0, h1, h2⟩ := exists_sgn_eq (Alt.three.sig1_outTri r)
  refine ⟨o, Alt.three.sig1_injective fun j => ?_⟩
  rw [sig1_toPref]; fin_cases j <;> assumption

end Ord3

/-- A profile for two voters, as a pair of orders. -/
abbrev Prof2 := Ord3 × Ord3

/-- The profile `(o₁, o₂)`. -/
def prof (o₁ o₂ : Ord3) : Profile (Fin 2) Alt := ![o₁.toPref, o₂.toPref]

/-- The profile of a pair. -/
def Prof2.toProfile (p : Prof2) : Profile (Fin 2) Alt := prof p.1 p.2

/-- The triangle of `N_I` spanned by a profile (its signature). -/
def tri (p : Prof2) : Fin 3 → Fin 2 → Bool := fun j => ![p.1.sgn j, p.2.sgn j]

theorem sig_toProfile (p : Prof2) : Alt.three.sig p.toProfile = tri p := by
  funext j i
  fin_cases i <;> simp [ThreeAlts.sig, Prof2.toProfile, prof, tri, Ord3.sig1_toPref]

theorem Prof2.toProfile_injective : Function.Injective Prof2.toProfile := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [toProfile, prof, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [Ord3.toPref_injective h0, Ord3.toPref_injective h1]

theorem Prof2.toProfile_surjective : Function.Surjective Prof2.toProfile := by
  intro R
  obtain ⟨a, ha⟩ := Ord3.toPref_surjective (R 0)
  obtain ⟨b, hb⟩ := Ord3.toPref_surjective (R 1)
  refine ⟨(a, b), funext fun i => ?_⟩
  fin_cases i <;> simp [toProfile, prof, ha, hb]

/-- The domain consisting of the profiles of a list. -/
def dom (L : List Prof2) : Set (Profile (Fin 2) Alt) := Prof2.toProfile '' {p | p ∈ L}

theorem mem_dom {L : List Prof2} {p : Prof2} : p.toProfile ∈ dom L ↔ p ∈ L :=
  Prof2.toProfile_injective.mem_set_image

theorem sig_image_dom (L : List Prof2) : Alt.three.sig '' dom L = tri '' {p | p ∈ L} := by
  rw [dom, Set.image_image]; simp only [sig_toProfile]

/-! ### The Boolean checker -/

/-- The sign function that is unanimous on unanimous vertices and sends the split vertex
`(j, (c, ¬c))` to `b j c`. -/
def sfun (b : Fin 3 → Bool → Bool) : Vtx (Fin 2) → Bool := fun v =>
  if v.2 0 = v.2 1 then v.2 0 else b v.1 (v.2 0)

/-- `p` is sent to a triangle of `N_O` (not to a hollow triangle). -/
def goodB (s : Vtx (Fin 2) → Bool) (p : Prof2) : Bool :=
  !(s (0, tri p 0) == s (1, tri p 1) && s (1, tri p 1) == s (2, tri p 2))

/-- `s` is the projection to voter `k` on the vertices of the profiles in `L`. -/
def projB (s : Vtx (Fin 2) → Bool) (L : List Prof2) (k : Fin 2) : Bool :=
  L.all fun p => s (0, tri p 0) == tri p 0 k && s (1, tri p 1) == tri p 1 k &&
    s (2, tri p 2) == tri p 2 k

/-- Split-vertex values from six Booleans. -/
def bits6 (a0 a1 b0 b1 c0 c1 : Bool) : Fin 3 → Bool → Bool :=
  fun j c => cond c (![a1, b1, c1] j) (![a0, b0, c0] j)

/-- All 64 assignments of split-vertex values. -/
def allBits : List (Fin 3 → Bool → Bool) := do
  let a0 ← [false, true]
  let a1 ← [false, true]
  let b0 ← [false, true]
  let b1 ← [false, true]
  let c0 ← [false, true]
  let c1 ← [false, true]
  pure (bits6 a0 a1 b0 b1 c0 c1)

/-- Does the domain `dom L` admit a unanimous, IIA, non-dictatorial aggregation map? -/
def admitsB (L : List Prof2) : Bool :=
  allBits.any fun b => L.all (goodB (sfun b)) && !projB (sfun b) L 0 && !projB (sfun b) L 1

def allOrd : List Ord3 := [.ABC, .ACB, .BAC, .BCA, .CAB, .CBA]

/-- All 36 profiles. -/
def allProf : List Prof2 := allOrd.flatMap fun a => allOrd.map fun b => (a, b)

/-! ### Soundness and completeness of the checker -/

theorem fin2_eq (σ : Fin 2 → Bool) : σ = ![σ 0, σ 1] := by
  funext i; fin_cases i <;> rfl

/-- A sign function unanimous at a vertex agrees there with its `sfun` normal form. -/
theorem eq_sfun_of_unan (s : Vtx (Fin 2) → Bool) (j : Fin 3) (σ : Fin 2 → Bool)
    (hU : ∀ c, σ = (fun _ => c) → s (j, σ) = c) :
    s (j, σ) = sfun (fun j c => s (j, ![c, !c])) (j, σ) := by
  rw [fin2_eq σ] at hU ⊢
  generalize σ 0 = x at hU ⊢
  generalize σ 1 = y at hU ⊢
  cases x <;> cases y <;> simp [sfun]
  · exact hU false (by funext i; fin_cases i <;> rfl)
  · exact hU true (by funext i; fin_cases i <;> rfl)

theorem sfun_unanimous (b : Fin 3 → Bool → Bool) (j : Fin 3) (c : Bool) :
    sfun b (j, fun _ => c) = c := by
  simp [sfun]

theorem sfun_congr {b b' : Fin 3 → Bool → Bool} (h : ∀ j c, b j c = b' j c) : sfun b = sfun b' := by
  funext v; simp [sfun, h]

theorem exists_mem_allBits (b : Fin 3 → Bool → Bool) : ∃ b' ∈ allBits, ∀ j c, b' j c = b j c := by
  refine ⟨bits6 (b 0 false) (b 0 true) (b 1 false) (b 1 true) (b 2 false) (b 2 true), ?_, ?_⟩
  · generalize b 0 false = a0; generalize b 0 true = a1; generalize b 1 false = b0
    generalize b 1 true = b1; generalize b 2 false = c0; generalize b 2 true = c1
    revert a0 a1 b0 b1 c0 c1; decide
  · intro j c; fin_cases j <;> cases c <;> rfl

theorem goodB_iff (s : Vtx (Fin 2) → Bool) (p : Prof2) :
    goodB s p = true ↔ OutTri (s (0, tri p 0)) (s (1, tri p 1)) (s (2, tri p 2)) := by
  unfold goodB OutTri
  generalize s (0, tri p 0) = x; generalize s (1, tri p 1) = y; generalize s (2, tri p 2) = z
  cases x <;> cases y <;> cases z <;> decide

theorem projB_iff (s : Vtx (Fin 2) → Bool) (L : List Prof2) (k : Fin 2) :
    projB s L k = true ↔ ∀ p ∈ L, ∀ j, s (j, tri p j) = tri p j k := by
  simp only [projB, List.all_eq_true, Bool.and_eq_true, beq_iff_eq]
  refine forall₂_congr fun p _ => ⟨?_, fun h => ⟨⟨h 0, h 1⟩, h 2⟩⟩
  rintro ⟨⟨h0, h1⟩, h2⟩ j
  fin_cases j <;> assumption

/-- Sign-level conditions on `tri '' L` only depend on the values on its vertices. -/
theorem sign_conds_congr {L : List Prof2} {s s' : Vtx (Fin 2) → Bool}
    (h : ∀ p ∈ L, ∀ j, s (j, tri p j) = s' (j, tri p j)) :
    (SignSimplicialOn (tri '' {p | p ∈ L}) s ↔ ∀ p ∈ L, goodB s' p = true) ∧
      ∀ k, (SignProjectionOn (tri '' {p | p ∈ L}) s k ↔ projB s' L k = true) := by
  refine ⟨?_, fun k => ?_⟩
  · simp only [SignSimplicialOn, Set.forall_mem_image, Set.mem_ofPred_eq, goodB_iff]
    exact forall₂_congr fun p hp => by rw [h p hp 0, h p hp 1, h p hp 2]
  · simp only [SignProjectionOn, Set.forall_mem_image, Set.mem_ofPred_eq, projB_iff]
    exact forall₂_congr fun p hp => forall_congr' fun j => by rw [h p hp j]

/-- **Checker correctness.** `admitsB L` decides whether the finite domain `dom L` admits a
unanimous, IIA, non-dictatorial aggregation map. -/
theorem admitsNonDictatorial_dom_iff (L : List Prof2) :
    AdmitsNonDictatorial (dom L) ↔ admitsB L = true := by
  rw [Alt.three.admitsNonDictatorial_iff_sign, sig_image_dom]
  constructor
  · rintro ⟨s, hU, hS, hP⟩
    obtain ⟨b', hb', hbb'⟩ := exists_mem_allBits fun j c => s (j, ![c, !c])
    have hag : ∀ p ∈ L, ∀ j, s (j, tri p j) = sfun b' (j, tri p j) := by
      intro p hp j
      rw [sfun_congr hbb']
      exact eq_sfun_of_unan s j _ fun c hc => hU _ ⟨p, hp, rfl⟩ j c hc
    obtain ⟨h1, h2⟩ := sign_conds_congr hag
    simp only [admitsB, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
    refine ⟨b', hb', ⟨h1.1 hS, ?_⟩, ?_⟩
    · cases h : projB (sfun b') L 0
      · rfl
      · exact absurd ((h2 0).2 h) (hP 0)
    · cases h : projB (sfun b') L 1
      · rfl
      · exact absurd ((h2 1).2 h) (hP 1)
  · intro h
    simp only [admitsB, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      List.all_eq_true] at h
    obtain ⟨b, -, ⟨hg, hp0⟩, hp1⟩ := h
    obtain ⟨h1, h2⟩ := sign_conds_congr (L := L) (s := sfun b) (s' := sfun b)
      fun _ _ _ => rfl
    refine ⟨sfun b, ?_, h1.2 hg, fun k hk => ?_⟩
    · rintro _ ⟨p, -, rfl⟩ j c hc
      rw [hc]; exact sfun_unanimous b j c
    · have := (h2 k).1 hk
      fin_cases k
      · exact absurd (hp0.symm.trans this) (by decide)
      · exact absurd (hp1.symm.trans this) (by decide)

theorem mem_allProf (p : Prof2) : p ∈ allProf := by revert p; decide

/-- `N_I`: the domain of all profiles. -/
theorem dom_allProf : dom allProf = Set.univ :=
  Set.eq_univ_of_forall fun R => by
    obtain ⟨p, rfl⟩ := Prof2.toProfile_surjective R
    exact mem_dom.2 (mem_allProf p)

theorem dom_diff (L : List Prof2) (p1 p2 : Prof2) :
    dom L \ {p1.toProfile, p2.toProfile} = dom (L.filter fun p => p ≠ p1 ∧ p ≠ p2) := by
  ext R
  obtain ⟨p, rfl⟩ := Prof2.toProfile_surjective R
  simp only [Set.mem_sdiff, mem_dom, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prof2.toProfile_injective.eq_iff, List.mem_filter, decide_eq_true_eq]
  tauto

theorem dom_diff3 (L : List Prof2) (p1 p2 p3 : Prof2) :
    dom L \ {p1.toProfile, p2.toProfile, p3.toProfile} =
      dom (L.filter fun p => p ≠ p1 ∧ p ≠ p2 ∧ p ≠ p3) := by
  ext R
  obtain ⟨p, rfl⟩ := Prof2.toProfile_surjective R
  simp only [Set.mem_sdiff, mem_dom, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prof2.toProfile_injective.eq_iff, List.mem_filter, decide_eq_true_eq]
  tauto

/-- A domain containing all vertices of `N_I`, contained in `D'`, without non-dictatorial maps
forces `D'` to have none either. -/
theorem not_admits_of_dom_subset {C : List Prof2} (hC : ¬ AdmitsNonDictatorial (dom C))
    (hcov : ∀ (j : Fin 3) (σ : Fin 2 → Bool), ∃ p ∈ C, tri p j = σ)
    {D' : Set (Profile (Fin 2) Alt)} (hsub : dom C ⊆ D') : ¬ AdmitsNonDictatorial D' := by
  intro h
  refine hC (AdmitsNonDictatorial.mono hsub
    (fun R' _ a b => Alt.three.cover_of_forall_exists_sig_eq ?_ R' a b) h)
  intro j σ
  obtain ⟨p, hp, he⟩ := hcov j σ
  exact ⟨p.toProfile, mem_dom.2 hp, by rw [sig_toProfile, he]⟩

/-- If `dom M` admits a non-dictatorial map, so does every `D ⊆ dom M` containing all vertices. -/
theorem admits_of_subset_dom {M : List Prof2} (hM : AdmitsNonDictatorial (dom M))
    {D : Set (Profile (Fin 2) Alt)} (hsub : D ⊆ dom M)
    (hv : ∀ (j : Fin 3) (σ : Fin 2 → Bool), ∃ R ∈ D, Alt.three.sig R j = σ) :
    AdmitsNonDictatorial D :=
  AdmitsNonDictatorial.mono hsub (fun R' _ a b => Alt.three.cover_of_forall_exists_sig_eq hv R' a b) hM

/-! ### The domains of Section 4 -/

/-- Number of pairs (`AB, BC, CA`) on which the two voters disagree. -/
def ndis (p : Prof2) : ℕ := (Finset.univ.filter fun j : Fin 3 => p.1.sgn j ≠ p.2.sgn j).card

/-- The torus `T` (Sec. 3/4.1): the 24 profiles where the voters disagree on exactly one or two
pairs. -/
def Tlist : List Prof2 := allProf.filter fun p => ndis p = 1 ∨ ndis p = 2

/-- The torus `T` as a domain. -/
def domT : Set (Profile (Fin 2) Alt) := dom Tlist

/-- The cylinder `C₁` (left cylinder of Figs. 9–10; a connected component of `T`). -/
def C1 : List Prof2 :=
  [(.ABC, .ACB), (.ABC, .CAB), (.ACB, .CAB), (.ACB, .CBA), (.BAC, .ABC), (.BAC, .ACB),
   (.BCA, .ABC), (.BCA, .BAC), (.CAB, .BCA), (.CAB, .CBA), (.CBA, .BAC), (.CBA, .BCA)]

/-- The cylinder `C₂`: `C₁` with the voters swapped. -/
def C2 : List Prof2 := C1.map Prod.swap

/-- A critical profile: the voters disagree on exactly two pairs (its triangle has one vertex on
the green cycle and an edge on the blue cycle). -/
def IsCritical (p : Prof2) : Prop := ndis p = 2

instance : DecidablePred IsCritical := fun p => inferInstanceAs (Decidable (ndis p = 2))

/-- The split vertices (`U^{(+,−)}`, `U^{(−,+)}`) of the triangle of `p`: for a critical profile,
its blue edge. -/
def blueEdge (p : Prof2) : Finset (Vtx (Fin 2)) :=
  (Finset.univ.filter fun j : Fin 3 => p.1.sgn j ≠ p.2.sgn j).image fun j => (j, tri p j)

/-- A critical pair (full version, Sec. 4.3): `R₁ ∈ C₁`, `R₂ ∈ C₂` critical with disjoint blue
edges. -/
def IsCriticalPair (p1 p2 : Prof2) : Prop :=
  p1 ∈ C1 ∧ p2 ∈ C2 ∧ IsCritical p1 ∧ IsCritical p2 ∧ Disjoint (blueEdge p1) (blueEdge p2)

/-- A critical triple (full version, Sec. 4.3): `R₁ ∈ C₁`, `R₂ ∈ C₂` critical whose blue edges
share exactly one vertex, and the antiunanimity profile `R₃` whose (blue) edges are these two. -/
def IsCriticalTriple (p1 p2 p3 : Prof2) : Prop :=
  p1 ∈ C1 ∧ p2 ∈ C2 ∧ IsCritical p1 ∧ IsCritical p2 ∧
    (blueEdge p1 ∩ blueEdge p2).card = 1 ∧ ndis p3 = 3 ∧ blueEdge p3 = blueEdge p1 ∪ blueEdge p2

instance (p1 p2 : Prof2) : Decidable (IsCriticalPair p1 p2) := by
  unfold IsCriticalPair; infer_instance

instance (p1 p2 p3 : Prof2) : Decidable (IsCriticalTriple p1 p2 p3) := by
  unfold IsCriticalTriple; infer_instance

/-! #### Sanity checks on the combinatorics -/

theorem Tlist_length : Tlist.length = 24 := by decide +kernel

theorem C1_subset_T : ∀ p ∈ C1, p ∈ Tlist := by decide +kernel

theorem C2_subset_T : ∀ p ∈ C2, p ∈ Tlist := by decide +kernel

theorem T_subset_C1_C2 : ∀ p ∈ Tlist, p ∈ C1 ∨ p ∈ C2 := by decide +kernel

theorem C1_disjoint_C2 : ∀ p ∈ C1, p ∉ C2 := by decide +kernel

theorem critical_count : (C1.filter IsCritical).length = 6 ∧ (C2.filter IsCritical).length = 6 :=
  by decide +kernel

/-- Two blue edges (of critical profiles of `C₁` and `C₂`) are equal, adjacent (share exactly one
vertex) or disjoint. -/
theorem blueEdge_trichotomy : ∀ p1 ∈ C1, ∀ p2 ∈ C2, IsCritical p1 → IsCritical p2 →
    blueEdge p1 = blueEdge p2 ∨ (blueEdge p1 ∩ blueEdge p2).card = 1 ∨
      Disjoint (blueEdge p1) (blueEdge p2) := by decide +kernel

/-- Each cylinder contains all 12 vertices of `N_I`. -/
theorem C1_covers : ∀ (j : Fin 3) (σ : Fin 2 → Bool), ∃ p ∈ C1, tri p j = σ := by decide +kernel

theorem C2_covers : ∀ (j : Fin 3) (σ : Fin 2 → Bool), ∃ p ∈ C2, tri p j = σ := by decide +kernel

/-! ### Section 4.1: the cylinders -/

/-- Sec. 4.1 of [Rajsbaum–Raventós-Pujol, PODC 2022] ("basic domain restriction"): the cylinder
`C₁` admits no unanimous, IIA, non-dictatorial aggregation map. -/
theorem not_admits_C1 : ¬ AdmitsNonDictatorial (dom C1) := by
  rw [admitsNonDictatorial_dom_iff]; decide +kernel

/-- Sec. 4.1: the same for the cylinder `C₂`. -/
theorem not_admits_C2 : ¬ AdmitsNonDictatorial (dom C2) := by
  rw [admitsNonDictatorial_dom_iff]; decide +kernel

/-- Any domain containing a whole cylinder admits no non-dictatorial map. -/
theorem not_admits_of_C1_subset {D' : Set (Profile (Fin 2) Alt)} (h : dom C1 ⊆ D') :
    ¬ AdmitsNonDictatorial D' := not_admits_of_dom_subset not_admits_C1 C1_covers h

theorem not_admits_of_C2_subset {D' : Set (Profile (Fin 2) Alt)} (h : dom C2 ⊆ D') :
    ¬ AdmitsNonDictatorial D' := not_admits_of_dom_subset not_admits_C2 C2_covers h

/-- Maximality: if `L ⊇ C₁ ∪ C₂`, `p₁ ∈ C₁`, `p₂ ∈ C₂`, then every domain strictly between
`dom L \ {p₁, p₂}` and `dom L` contains a whole cylinder, hence admits no non-dictatorial map. -/
theorem not_admits_of_ssuperset {L : List Prof2} (hL1 : ∀ p ∈ C1, p ∈ L) (hL2 : ∀ p ∈ C2, p ∈ L)
    {p1 p2 : Prof2} (h1 : p1 ∈ C1) (h2 : p2 ∈ C2) {D' : Set (Profile (Fin 2) Alt)}
    (hlt : dom L \ {p1.toProfile, p2.toProfile} ⊂ D') (hsub : D' ⊆ dom L) :
    ¬ AdmitsNonDictatorial D' := by
  obtain ⟨R, hRD', hRn⟩ := Set.exists_of_ssubset hlt
  have hR : R = p1.toProfile ∨ R = p2.toProfile := by
    by_contra hc
    exact hRn ⟨hsub hRD', by simpa using hc⟩
  rcases hR with rfl | rfl
  · apply not_admits_of_C1_subset
    rintro _ ⟨p, hp, rfl⟩
    by_cases hpp : p = p1
    · rw [hpp]; exact hRD'
    · have hp2 : p ≠ p2 := fun e => C1_disjoint_C2 p hp (e ▸ h2)
      refine hlt.1 ⟨mem_dom.2 (hL1 p hp), ?_⟩
      simp [Prof2.toProfile_injective.eq_iff, hpp, hp2]
  · apply not_admits_of_C2_subset
    rintro _ ⟨p, hp, rfl⟩
    by_cases hpp : p = p2
    · rw [hpp]; exact hRD'
    · have hp1 : p ≠ p1 := fun e => C1_disjoint_C2 p1 h1 (e ▸ hp)
      refine hlt.1 ⟨mem_dom.2 (hL2 p hp), ?_⟩
      simp [Prof2.toProfile_injective.eq_iff, hpp, hp1]

/-! ### Proposition 4.1 (domains inside the torus `T`) -/

/-- Proposition 4.1 of [Rajsbaum–Raventós-Pujol, PODC 2022], existence part: removing from `T`
a critical profile of `C₁` and a critical profile of `C₂` with different blue edges yields a
domain admitting a unanimous, IIA, non-dictatorial aggregation map. -/
theorem prop41_admits : ∀ p1 ∈ C1, ∀ p2 ∈ C2, IsCritical p1 → IsCritical p2 →
    blueEdge p1 ≠ blueEdge p2 →
      AdmitsNonDictatorial (domT \ {p1.toProfile, p2.toProfile}) := by
  intro p1 h1 p2 h2 c1 c2 hne
  rw [domT, dom_diff, admitsNonDictatorial_dom_iff]
  revert p1 p2
  decide +kernel

/-- Proposition 4.1, maximality part: such a domain is maximal (in `T`) among the domains
admitting a unanimous, IIA, non-dictatorial aggregation map. -/
theorem prop41_maximal {p1 p2 : Prof2} (h1 : p1 ∈ C1) (h2 : p2 ∈ C2)
    {D' : Set (Profile (Fin 2) Alt)} (hlt : domT \ {p1.toProfile, p2.toProfile} ⊂ D')
    (hsub : D' ⊆ domT) : ¬ AdmitsNonDictatorial D' :=
  not_admits_of_ssuperset C1_subset_T C2_subset_T h1 h2 hlt hsub

/-- The condition "both blue edges must be different" of Proposition 4.1 is needed. -/
theorem prop41_equal_blueEdge : ∀ p1 ∈ C1, ∀ p2 ∈ C2, IsCritical p1 → IsCritical p2 →
    blueEdge p1 = blueEdge p2 →
      ¬ AdmitsNonDictatorial (domT \ {p1.toProfile, p2.toProfile}) := by
  intro p1 h1 p2 h2 c1 c2 hne
  rw [domT, dom_diff, admitsNonDictatorial_dom_iff]
  revert p1 p2
  decide +kernel


/-! #### The "moreover" part of Proposition 4.1 is false -/

theorem isDictatorOn_singleton {F : Aggregation (Fin 2) Alt} {R : Profile (Fin 2) Alt} {k : Fin 2}
    (h : F R = R k) : IsDictatorOn {R} F k := by
  rintro _ rfl a b hab; rw [h]; exact hab

/-- Counterexample to the last sentence of Proposition 4.1 (and of Theorem 4.2): the one-profile
domain `{(ABC, ACB)}` admits no unanimous, IIA, non-dictatorial aggregation map. Unanimity forces
`A ≻ B` and `A ≻ C`, so `F(R) ∈ {ABC, ACB}`, which is the preference of one of the voters. -/
theorem not_admits_ABC_ACB : ¬ AdmitsNonDictatorial {prof .ABC .ACB} := by
  rintro ⟨F, hU, -, hnd⟩
  set R := prof .ABC .ACB
  have hAB : (F R).P .A .B := hU R rfl _ _ (by
    rw [Fin.forall_fin_two]
    exact ⟨show Ord3.ABC.toPref.P .A .B by decide, show Ord3.ACB.toPref.P .A .B by decide⟩)
  have hAC : (F R).P .A .C := hU R rfl _ _ (by
    rw [Fin.forall_fin_two]
    exact ⟨show Ord3.ABC.toPref.P .A .C by decide, show Ord3.ACB.toPref.P .A .C by decide⟩)
  have s0 : Alt.three.sig1 (F R) 0 = true := (Alt.three.sig1_eq_true_iff _ 0).2 hAB
  have s2 : Alt.three.sig1 (F R) 2 = false := (Alt.three.sig1_eq_false_iff _ 2).2 hAC
  rcases (F R).total (show Alt.B ≠ Alt.C by decide) with hBC | hCB
  · have s1 : Alt.three.sig1 (F R) 1 = true := (Alt.three.sig1_eq_true_iff _ 1).2 hBC
    refine hnd 0 (isDictatorOn_singleton (Alt.three.sig1_injective fun j => ?_))
    show _ = Alt.three.sig1 (Ord3.toPref .ABC) j
    rw [Ord3.sig1_toPref]; fin_cases j <;> assumption
  · have s1 : Alt.three.sig1 (F R) 1 = false := (Alt.three.sig1_eq_false_iff _ 1).2 hCB
    refine hnd 1 (isDictatorOn_singleton (Alt.three.sig1_injective fun j => ?_))
    show _ = Alt.three.sig1 (Ord3.toPref .ACB) j
    rw [Ord3.sig1_toPref]; fin_cases j <;> assumption

/-- The last sentence of Proposition 4.1 ("every domain contained in one of these maximal domains
belongs to `D_T`") is **false**: `{(ABC, ACB)}` lies in every such maximal domain
`T \ {R₁, R₂}` but admits no non-dictatorial map. -/
theorem prop41_moreover_false :
    (∃ p1 ∈ C1, ∃ p2 ∈ C2, IsCritical p1 ∧ IsCritical p2 ∧ blueEdge p1 ≠ blueEdge p2) ∧
    ∀ p1 ∈ C1, ∀ p2 ∈ C2, IsCritical p1 → IsCritical p2 →
      {prof .ABC .ACB} ⊆ domT \ {p1.toProfile, p2.toProfile} ∧
      ¬ AdmitsNonDictatorial {prof .ABC .ACB} := by
  refine ⟨by decide +kernel, fun p1 h1 p2 h2 c1 c2 => ⟨?_, not_admits_ABC_ACB⟩⟩
  rw [Set.singleton_subset_iff, domT, dom_diff]
  refine mem_dom (p := (.ABC, .ACB)) |>.2 ?_
  revert p1 p2
  decide +kernel

/-! ### Theorem 4.2 (domains inside `N_I`) -/

/-- Theorem 4.2 of [Rajsbaum–Raventós-Pujol, PODC 2022], corrected existence part: if the blue
edges of the critical profiles `R₁ ∈ C₁`, `R₂ ∈ C₂` are **disjoint** (a critical pair), then
`N_I \ {R₁, R₂}` admits a unanimous, IIA, non-dictatorial aggregation map. -/
theorem thm42_admits_of_disjoint : ∀ p1 ∈ C1, ∀ p2 ∈ C2, IsCritical p1 → IsCritical p2 →
    Disjoint (blueEdge p1) (blueEdge p2) →
      AdmitsNonDictatorial (Set.univ \ {p1.toProfile, p2.toProfile}) := by
  intro p1 h1 p2 h2 c1 c2 hd
  rw [← dom_allProf, dom_diff, admitsNonDictatorial_dom_iff]
  revert p1 p2
  decide +kernel

/-- Theorem 4.2, maximality part: `N_I \ {R₁, R₂}` (`R₁ ∈ C₁`, `R₂ ∈ C₂`) is maximal among the
domains admitting a non-dictatorial map: any strictly larger domain contains a whole cylinder. -/
theorem thm42_maximal {p1 p2 : Prof2} (h1 : p1 ∈ C1) (h2 : p2 ∈ C2)
    {D' : Set (Profile (Fin 2) Alt)} (hlt : Set.univ \ {p1.toProfile, p2.toProfile} ⊂ D') :
    ¬ AdmitsNonDictatorial D' := by
  rw [← dom_allProf] at hlt
  exact not_admits_of_ssuperset (fun p _ => mem_allProf p) (fun p _ => mem_allProf p) h1 h2 hlt
    (by rw [dom_allProf]; exact Set.subset_univ _)

/-- Theorem 4.2 fails for **adjacent** blue edges: if the blue edges of the critical profiles
`R₁ ∈ C₁`, `R₂ ∈ C₂` share exactly one vertex, then `N_I \ {R₁, R₂}` admits **no** unanimous,
IIA, non-dictatorial aggregation map (the antiunanimity profile spanned by both edges is still
there: one needs to remove the whole critical triple). -/
theorem thm42_not_admits_of_adjacent : ∀ p1 ∈ C1, ∀ p2 ∈ C2, IsCritical p1 → IsCritical p2 →
    (blueEdge p1 ∩ blueEdge p2).card = 1 →
      ¬ AdmitsNonDictatorial (Set.univ \ {p1.toProfile, p2.toProfile}) := by
  intro p1 h1 p2 h2 c1 c2 hd
  rw [← dom_allProf, dom_diff, admitsNonDictatorial_dom_iff]
  revert p1 p2
  decide +kernel

/-- With equal blue edges, `N_I \ {R₁, R₂}` admits no non-dictatorial map either. -/
theorem thm42_not_admits_of_eq : ∀ p1 ∈ C1, ∀ p2 ∈ C2, IsCritical p1 → IsCritical p2 →
    blueEdge p1 = blueEdge p2 →
      ¬ AdmitsNonDictatorial (Set.univ \ {p1.toProfile, p2.toProfile}) := by
  intro p1 h1 p2 h2 c1 c2 hd
  rw [← dom_allProf, dom_diff, admitsNonDictatorial_dom_iff]
  revert p1 p2
  decide +kernel

/-- Explicit counterexample to Theorem 4.2: `R₁ = (BAC, ACB) ∈ C₁` and `R₂ = (CBA, ACB) ∈ C₂` are
critical with different (adjacent) blue edges, yet `N_I \ {R₁, R₂}` admits no unanimous, IIA,
non-dictatorial aggregation map. (`(R₁, R₂, (BCA, ACB))` is a critical triple; the full version's
example of a critical triple uses `(BCA, ABC)` instead of `R₂`, which has the same blue edge as
`R₂` but lies in `C₁`, see `paper_triple_example_not_critical`.) -/
theorem thm42_counterexample :
    ((Ord3.BAC, Ord3.ACB) ∈ C1 ∧ (Ord3.CBA, Ord3.ACB) ∈ C2 ∧ IsCritical (.BAC, .ACB) ∧
      IsCritical (.CBA, .ACB) ∧ blueEdge (.BAC, .ACB) ≠ blueEdge (.CBA, .ACB)) ∧
    ¬ AdmitsNonDictatorial (Set.univ \ {prof .BAC .ACB, prof .CBA .ACB}) := by
  refine ⟨by decide +kernel, ?_⟩
  have := thm42_not_admits_of_adjacent (.BAC, .ACB) (by decide) (.CBA, .ACB) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact this

/-- Theorem 4.2 of [Rajsbaum–Raventós-Pujol, PODC 2022], existence part, as stated
("different blue edges" suffices), is **false**. -/
theorem thm42_false : ¬ ∀ p1 ∈ C1, ∀ p2 ∈ C2, IsCritical p1 → IsCritical p2 →
    blueEdge p1 ≠ blueEdge p2 →
      AdmitsNonDictatorial (Set.univ \ {p1.toProfile, p2.toProfile}) := fun h =>
  thm42_counterexample.2 (h (.BAC, .ACB) (by decide) (.CBA, .ACB) (by decide) (by decide +kernel)
    (by decide +kernel) thm42_counterexample.1.2.2.2.2)

/-- The "moreover" part of Theorem 4.2 is false as well: e.g. the unanimous one-profile domain
`{(ABC, ABC)}` admits no non-dictatorial map. (It is a subdomain of every `N_I \ {R₁, R₂}` with
`R₁, R₂` critical, since a critical profile is not unanimous; that containment is not stated here.)
Like `prop41_moreover_false`, this counterexample loses vertices of `N_I`; see
`thm42_moreover_of_pairFree` for the statement that holds when all pairs stay free. -/
theorem thm42_moreover_false : ¬ AdmitsNonDictatorial {prof .ABC .ABC} := by
  have : ({prof .ABC .ABC} : Set (Profile (Fin 2) Alt)) = dom [(.ABC, .ABC)] := by
    ext R; simp [dom, Prof2.toProfile]
  rw [this, admitsNonDictatorial_dom_iff]; decide +kernel

/-! ### The "moreover" sentences hold for subdomains keeping all vertices -/

/-- Non-dictatorial aggregation passes to every subdomain in which all pairs are free. -/
theorem admits_of_subset_of_pairFree {D D' : Set (Profile (Fin 2) Alt)}
    (hD' : AdmitsNonDictatorial D') (hsub : D ⊆ D')
    (hfree : ∀ a b : Alt, a ≠ b → PairFree D a b) : AdmitsNonDictatorial D :=
  AdmitsNonDictatorial.mono hsub (fun R' _ a b =>
    Alt.three.cover_of_forall_exists_sig_eq
      (Alt.three.forall_exists_sig_eq_of_pairFree hfree) R' a b) hD'

/-- Corrected last sentence of Proposition 4.1: every subdomain of `T \ {R₁, R₂}` in which every
pair of alternatives is free (i.e. which keeps all vertices of `N_I`) admits a unanimous, IIA,
non-dictatorial aggregation map. -/
theorem prop41_moreover_of_pairFree : ∀ p1 ∈ C1, ∀ p2 ∈ C2, IsCritical p1 → IsCritical p2 →
    blueEdge p1 ≠ blueEdge p2 → ∀ D : Set (Profile (Fin 2) Alt),
      D ⊆ domT \ {p1.toProfile, p2.toProfile} → (∀ a b : Alt, a ≠ b → PairFree D a b) →
        AdmitsNonDictatorial D :=
  fun p1 h1 p2 h2 c1 c2 hne _ hsub hfree =>
    admits_of_subset_of_pairFree (prop41_admits p1 h1 p2 h2 c1 c2 hne) hsub hfree

/-- Corrected last sentence of Theorem 4.2 (for critical pairs): every subdomain of
`N_I \ {R₁, R₂}` (disjoint blue edges) in which every pair is free admits a non-dictatorial map. -/
theorem thm42_moreover_of_pairFree : ∀ p1 ∈ C1, ∀ p2 ∈ C2, IsCritical p1 → IsCritical p2 →
    Disjoint (blueEdge p1) (blueEdge p2) → ∀ D : Set (Profile (Fin 2) Alt),
      D ⊆ Set.univ \ {p1.toProfile, p2.toProfile} → (∀ a b : Alt, a ≠ b → PairFree D a b) →
        AdmitsNonDictatorial D :=
  fun p1 h1 p2 h2 c1 c2 hd _ hsub hfree =>
    admits_of_subset_of_pairFree (thm42_admits_of_disjoint p1 h1 p2 h2 c1 c2 hd) hsub hfree

/-! ### The paper's example of a critical triple -/

/-- The full version's example of a critical triple, `((BAC, ACB), (BCA, ABC), (BCA, ACB))`, is not
one: both `(BAC, ACB)` and `(BCA, ABC)` lie in the cylinder `C₁` (the profile of `C₂` with the
same blue edge as `(BCA, ABC)` is `(CBA, ACB)`), and removing these three profiles from `N_I`
does not allow a non-dictatorial map. -/
theorem paper_triple_example_not_critical :
    (Ord3.BAC, Ord3.ACB) ∈ C1 ∧ (Ord3.BCA, Ord3.ABC) ∈ C1 ∧ (Ord3.BCA, Ord3.ABC) ∉ C2 ∧
    blueEdge (.BCA, .ABC) = blueEdge (.CBA, .ACB) ∧ IsCriticalTriple (.BAC, .ACB) (.CBA, .ACB) (.BCA, .ACB) ∧
    ¬ AdmitsNonDictatorial
      (Set.univ \ {prof .BAC .ACB, prof .BCA .ABC, prof .BCA .ACB}) := by
  refine ⟨by decide +kernel, ?_⟩
  have := dom_diff3 allProf (.BAC, .ACB) (.BCA, .ABC) (.BCA, .ACB)
  rw [dom_allProf] at this
  rw [show prof .BAC .ACB = Prof2.toProfile (.BAC, .ACB) from rfl,
    show prof .BCA .ABC = Prof2.toProfile (.BCA, .ABC) from rfl,
    show prof .BCA .ACB = Prof2.toProfile (.BCA, .ACB) from rfl, this,
    admitsNonDictatorial_dom_iff]
  decide +kernel

/-! ### Theorem 6 of the full version: the characterization -/

/-- The 18 critical pairs. -/
def cpList : List (Prof2 × Prof2) :=
  (C1.flatMap fun p1 => C2.map fun p2 => (p1, p2)).filter fun q => IsCriticalPair q.1 q.2

/-- The 6 antiunanimity profiles (the voters disagree on every pair). -/
def antiList : List Prof2 := allProf.filter fun p => ndis p = 3

/-- The 12 critical triples. -/
def ctList : List (Prof2 × Prof2 × Prof2) :=
  (C1.flatMap fun p1 => C2.flatMap fun p2 => antiList.map fun p3 => (p1, p2, p3)).filter
    fun q => IsCriticalTriple q.1 q.2.1 q.2.2

theorem mem_cpList {p1 p2 : Prof2} : (p1, p2) ∈ cpList ↔ IsCriticalPair p1 p2 := by
  simp only [cpList, List.mem_filter, List.mem_flatMap, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    exact ⟨⟨p1, h.1, p2, h.2.1, rfl⟩, h⟩

theorem mem_ctList {p1 p2 p3 : Prof2} :
    (p1, p2, p3) ∈ ctList ↔ IsCriticalTriple p1 p2 p3 := by
  simp only [ctList, antiList, List.mem_filter, List.mem_flatMap, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    exact ⟨⟨p1, h.1, p2, h.2.1, p3, ⟨mem_allProf p3, h.2.2.2.2.2.1⟩, rfl⟩, h⟩

/-- The 18 critical pairs, listed explicitly. -/
def cpLit : List (Prof2 × Prof2) :=
  [((.ABC, .CAB), (.CAB, .ABC)), ((.ABC, .CAB), (.CBA, .ACB)), ((.ABC, .CAB), (.ACB, .BAC)),
   ((.ACB, .CBA), (.CAB, .ABC)), ((.ACB, .CBA), (.CBA, .ACB)), ((.ACB, .CBA), (.BCA, .CAB)),
   ((.BAC, .ACB), (.CAB, .ABC)), ((.BAC, .ACB), (.ACB, .BAC)), ((.BAC, .ACB), (.ABC, .BCA)),
   ((.BCA, .ABC), (.ACB, .BAC)), ((.BCA, .ABC), (.ABC, .BCA)), ((.BCA, .ABC), (.BAC, .CBA)),
   ((.CAB, .BCA), (.CBA, .ACB)), ((.CAB, .BCA), (.BCA, .CAB)), ((.CAB, .BCA), (.BAC, .CBA)),
   ((.CBA, .BAC), (.ABC, .BCA)), ((.CBA, .BAC), (.BCA, .CAB)), ((.CBA, .BAC), (.BAC, .CBA))]

/-- The 12 critical triples, listed explicitly. -/
def ctLit : List (Prof2 × Prof2 × Prof2) :=
  [((.ABC, .CAB), (.ABC, .BCA), (.ABC, .CBA)), ((.ABC, .CAB), (.BCA, .CAB), (.BAC, .CAB)),
   ((.ACB, .CBA), (.ACB, .BAC), (.ACB, .BCA)), ((.ACB, .CBA), (.BAC, .CBA), (.ABC, .CBA)),
   ((.BAC, .ACB), (.CBA, .ACB), (.BCA, .ACB)), ((.BAC, .ACB), (.BAC, .CBA), (.BAC, .CAB)),
   ((.BCA, .ABC), (.CAB, .ABC), (.CBA, .ABC)), ((.BCA, .ABC), (.BCA, .CAB), (.BCA, .ACB)),
   ((.CAB, .BCA), (.CAB, .ABC), (.CAB, .BAC)), ((.CAB, .BCA), (.ABC, .BCA), (.ACB, .BCA)),
   ((.CBA, .BAC), (.CBA, .ACB), (.CBA, .ABC)), ((.CBA, .BAC), (.ACB, .BAC), (.CAB, .BAC))]

theorem cpList_eq : cpList = cpLit := by decide +kernel

set_option maxRecDepth 100000 in
theorem ctList_eq : ctList = ctLit := by decide +kernel

theorem cpList_length : cpList.length = 18 := by rw [cpList_eq]; rfl

theorem ctList_length : ctList.length = 12 := by rw [ctList_eq]; rfl

/-- Every unanimous sign function on all of `N_I` that is not a projection sends both profiles of
some critical pair, or all three profiles of some critical triple, to hollow triangles. -/
def thm6B : Bool := allBits.all fun b =>
  projB (sfun b) allProf 0 || projB (sfun b) allProf 1 ||
    cpLit.any (fun q => !goodB (sfun b) q.1 && !goodB (sfun b) q.2) ||
    ctLit.any (fun q => !goodB (sfun b) q.1 && !goodB (sfun b) q.2.1 && !goodB (sfun b) q.2.2)

theorem thm6B_eq_true : thm6B = true := by decide +kernel

theorem cpList_admits : ∀ q ∈ cpList,
    admitsB (allProf.filter fun p => p ≠ q.1 ∧ p ≠ q.2) = true := by
  rw [cpList_eq]; decide +kernel

theorem ctList_admits : ∀ q ∈ ctList,
    admitsB (allProf.filter fun p => p ≠ q.1 ∧ p ≠ q.2.1 ∧ p ≠ q.2.2) = true := by
  -- (the Boolean form `List.all` is much faster in the kernel than `List.decidableBAll`)
  have h : (ctLit.all fun q =>
      admitsB (allProf.filter fun p => p ≠ q.1 ∧ p ≠ q.2.1 ∧ p ≠ q.2.2)) = true := by
    decide +kernel
  rw [ctList_eq]
  simpa only [List.all_eq_true] using h

theorem signProjectionOn_of_projB {D : Set (Profile (Fin 2) Alt)} {s : Vtx (Fin 2) → Bool}
    {k : Fin 2} (h : projB s allProf k = true) : SignProjectionOn (Alt.three.sig '' D) s k := by
  rintro _ ⟨R, -, rfl⟩ j
  obtain ⟨p, rfl⟩ := Prof2.toProfile_surjective R
  rw [sig_toProfile]
  exact (projB_iff s allProf k).1 h p (mem_allProf p) j

/-- **Theorem 6 of the full version** of [Rajsbaum–Raventós-Pujol] (Domain Restriction
Characterization), two voters and three alternatives: a domain `D` in which every pair of
alternatives is free (equivalently, containing all vertices of `N_I`) admits a unanimous, IIA,
non-dictatorial aggregation map iff `D` misses both profiles of some critical pair or all three
profiles of some critical triple. -/
theorem thm6 (D : Set (Profile (Fin 2) Alt)) (hfree : ∀ a b : Alt, a ≠ b → PairFree D a b) :
    AdmitsNonDictatorial D ↔
      (∃ p1 p2, IsCriticalPair p1 p2 ∧ p1.toProfile ∉ D ∧ p2.toProfile ∉ D) ∨
      (∃ p1 p2 p3, IsCriticalTriple p1 p2 p3 ∧
        p1.toProfile ∉ D ∧ p2.toProfile ∉ D ∧ p3.toProfile ∉ D) := by
  have hv := Alt.three.forall_exists_sig_eq_of_pairFree hfree
  constructor
  · intro h
    obtain ⟨s, hU, hS, hP⟩ := (Alt.three.admitsNonDictatorial_iff_sign D).1 h
    obtain ⟨b, hb, hbb⟩ := exists_mem_allBits fun j c => s (j, ![c, !c])
    have hs : s = sfun b := by
      funext v
      obtain ⟨j, σ⟩ := v
      rw [sfun_congr hbb]
      apply eq_sfun_of_unan
      intro c hc
      obtain ⟨R, hR, hRσ⟩ := hv j σ
      have := hU _ ⟨R, hR, rfl⟩ j c (hRσ.trans hc)
      rwa [hRσ] at this
    subst hs
    have hbad : ∀ p, goodB (sfun b) p = false → p.toProfile ∉ D := by
      intro p hp hpD
      have := hS _ ⟨_, hpD, rfl⟩
      rw [sig_toProfile, ← goodB_iff, hp] at this
      exact absurd this (by decide)
    have := thm6B_eq_true
    simp only [thm6B, List.all_eq_true, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
      Bool.not_eq_true'] at this
    rcases this b hb with ((hp0 | hp1) | ⟨⟨p1, p2⟩, hq, h1, h2⟩) | ⟨⟨p1, p2, p3⟩, hq, ⟨h1, h2⟩, h3⟩
    · exact absurd (signProjectionOn_of_projB hp0) (hP 0)
    · exact absurd (signProjectionOn_of_projB hp1) (hP 1)
    · exact Or.inl ⟨p1, p2, mem_cpList.1 (cpList_eq ▸ hq), hbad _ h1, hbad _ h2⟩
    · exact Or.inr ⟨p1, p2, p3, mem_ctList.1 (ctList_eq ▸ hq), hbad _ h1, hbad _ h2, hbad _ h3⟩
  · rintro (⟨p1, p2, hc, h1, h2⟩ | ⟨p1, p2, p3, hc, h1, h2, h3⟩)
    · have hM := (admitsNonDictatorial_dom_iff _).2 (cpList_admits (p1, p2) (mem_cpList.2 hc))
      refine admits_of_subset_dom hM ?_ hv
      intro R hR
      obtain ⟨p, rfl⟩ := Prof2.toProfile_surjective R
      rw [mem_dom, List.mem_filter, decide_eq_true_eq]
      refine ⟨mem_allProf p, ?_, ?_⟩ <;> rintro rfl <;> contradiction
    · have hM := (admitsNonDictatorial_dom_iff _).2
        (ctList_admits (p1, p2, p3) (mem_ctList.2 hc))
      refine admits_of_subset_dom hM ?_ hv
      intro R hR
      obtain ⟨p, rfl⟩ := Prof2.toProfile_surjective R
      rw [mem_dom, List.mem_filter, decide_eq_true_eq]
      refine ⟨mem_allProf p, ?_, ?_, ?_⟩ <;> rintro rfl <;> contradiction

end Podc.ArrowTopology
