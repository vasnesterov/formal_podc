import Papers.PODC2025.RelativisticComputing.Spacetime

/-!
# Relating classical, relativistic and computational executions (Jayanti, PODC 2025, §6.2)

* `lemma_6_2` — every relativistic execution refines a computational execution;
* `lemma_6_3` — characterization of classical executions. The paper's statement (P1–P3 suffice)
  needs the extra hypothesis that the total order embeds into `(ℝ, <)`, which is automatic for
  countably many processors (`lemma_6_3_of_countable`) but not in general (`Counterexample.lean`);
* `lemma_6_4_forward`, `lemma_6_4_backward` — classical executions = total orderings of
  computational executions (backward direction for countable executions);
* `corollary_6_5`, `lemma_6_6`;
* `theorem_6_7` — the Central Theorem, for countably many processors; `theorem_6_7_on` is the
  version for any class of countable executions (e.g. finite executions); `classical_iff_frames`
  is the classical ⇔ relativistic part, which holds without any countability assumption when
  observers are only asked about frames in which no two steps are simultaneous.
-/

namespace RelativisticComputing

variable {Proc Msg : Type} {A : Algorithm Proc Msg}

lemma rel_eq_of_iff {S : Type} {r r' : S → S → Prop} (h : ∀ a b, r a b ↔ r' a b) : r = r' :=
  funext fun a => funext fun b => propext (h a b)

/-! ### Basic facts about classical executions -/

lemma IsClassical.isSTO {S : Set (Step A)} {lt : S → S → Prop} (h : IsClassical A S lt) :
    IsSTO lt := by
  obtain ⟨t, ht, hlt⟩ := h
  rw [rel_eq_of_iff hlt]
  exact isSTO_of_real t ht.inj

/-! ### Lemma 6.2 -/

/-- **Lemma 6.2.** Every relativistic execution `(S, ≺_S)` is a refinement of some computational
execution `(S, ◁_S)` (here stated for the underlying physical execution `(S, ε)`). -/
theorem lemma_6_2 (X : Spacetime) {S : Set (Step A)} {ε : S → X.Pt} (h : IsRelPhys X A S ε) :
    ∃ R, IsComputational A S R ∧ ∀ a b, R a b → X.prec (ε a) (ε b) :=
  ⟨_, isComputational_of_refined (fun _ _ _ => X.prec_trans _ _ _) h.procSeq h.msgValid
    h.msgForward⟩

/-- **Lemma 6.2** for relativistic executions `(S, ≺_S)`. -/
theorem lemma_6_2' (X : Spacetime) {S : Set (Step A)} {prec : S → S → Prop}
    (h : IsRelativistic X A S prec) : ∃ R, IsComputational A S R ∧ ∀ a b, R a b → prec a b := by
  obtain ⟨ε, hε, hp⟩ := h
  obtain ⟨R, hR, hsub⟩ := lemma_6_2 X hε
  exact ⟨R, hR, fun a b h => (hp a b).2 (hsub a b h)⟩

/-! ### Lemma 6.3 -/

/-- **Lemma 6.3** (corrected). `(S, <_S)` is a classical execution iff (P1) `<_S` is a strict
total order, (P2) the steps of every processor form a rooted consecutively permissible sequence,
(P3) messages are valid, received at most once and oriented forward, **and** `<_S` embeds into the
real line. The paper omits the last condition; see `lemma_6_3_of_countable` and
`Counterexample.lean`. -/
theorem lemma_6_3 {S : Set (Step A)} {lt : S → S → Prop} :
    IsClassical A S lt ↔ IsSTO lt ∧ ProcSeq S lt ∧ MsgValid S ∧ MsgForward S lt ∧
      ∃ t : S → ℝ, ∀ a b, lt a b ↔ t a < t b := by
  constructor
  · intro h
    have hsto := h.isSTO
    obtain ⟨t, ht, hlt⟩ := h
    have e := rel_eq_of_iff hlt
    have h2 := ht.procSeq
    have h4 := ht.msgForward
    rw [← e] at h2 h4
    exact ⟨hsto, h2, ht.msgValid, h4, t, hlt⟩
  · rintro ⟨hsto, hseq, hv, hfwd, t, ht⟩
    refine ⟨t, ?_, ht⟩
    have e := rel_eq_of_iff ht
    rw [e] at hseq hfwd
    exact ⟨injective_of_embedding hsto ht, hseq, hv, hfwd⟩

/-- **Lemma 6.3** for executions with countably many steps: P1, P2, P3 characterize classical
executions. -/
theorem lemma_6_3_of_countableSteps {S : Set (Step A)} [Countable S] {lt : S → S → Prop} :
    IsClassical A S lt ↔ IsSTO lt ∧ ProcSeq S lt ∧ MsgValid S ∧ MsgForward S lt := by
  rw [lemma_6_3]
  constructor
  · rintro ⟨h1, h2, h3, h4, -⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4, exists_real_embedding h1⟩

/-- **Lemma 6.3** as stated in the paper, under the additional hypothesis that there are countably
many processors. -/
theorem lemma_6_3_of_countable [Countable Proc] {S : Set (Step A)} {lt : S → S → Prop} :
    IsClassical A S lt ↔ IsSTO lt ∧ ProcSeq S lt ∧ MsgValid S ∧ MsgForward S lt := by
  constructor
  · intro h
    have : Countable S := ((lemma_6_3.1 h).2.1).countable
    exact lemma_6_3_of_countableSteps.1 h
  · rintro ⟨h1, h2, h3, h4⟩
    have : Countable S := h2.countable
    exact lemma_6_3_of_countableSteps.2 ⟨h1, h2, h3, h4⟩

/-! ### Lemma 6.4 and Corollary 6.5 -/

/-- **Lemma 6.4**, first half: every classical execution is a total ordering of a computational
execution. -/
theorem lemma_6_4_forward {S : Set (Step A)} {lt : S → S → Prop} (h : IsClassical A S lt) :
    ∃ R, IsComputational A S R ∧ IsTotalOrderingOf R lt := by
  obtain ⟨hsto, hseq, hv, hfwd, -⟩ := lemma_6_3.1 h
  obtain ⟨hR, hsub⟩ := isComputational_of_refined hsto.trans hseq hv hfwd
  exact ⟨_, hR, hsto, hsub⟩

/-- A total ordering of a computational execution satisfies P1–P3. -/
lemma procSeq_of_totalOrdering {S : Set (Step A)} {R lt : S → S → Prop}
    (hR : IsComputational A S R) (hlt : IsTotalOrderingOf R lt) :
    ProcSeq S lt ∧ MsgForward S lt := by
  obtain ⟨hsto, hsub⟩ := hlt
  refine ⟨hR.procSeq.congr fun a b hab => ⟨hsub a b, fun h => ?_⟩,
    fun a b h => hsub a b (hR.msgForward a b h)⟩
  have hne : a ≠ b := by rintro rfl; exact hsto.irrefl a h
  rcases hR.procSeq.total a b hab hne with h' | h'
  · exact h'
  · exact absurd (hsub b a h') (hsto.asymm h)

/-- **Lemma 6.4**, second half, for countable executions: every total ordering of a computational
execution with countably many steps is a classical execution. (False for uncountable executions:
`Counterexample.lean`.) -/
theorem lemma_6_4_backward {S : Set (Step A)} [Countable S] {R lt : S → S → Prop}
    (hR : IsComputational A S R) (hlt : IsTotalOrderingOf R lt) : IsClassical A S lt := by
  obtain ⟨hseq, hfwd⟩ := procSeq_of_totalOrdering hR hlt
  exact lemma_6_3_of_countableSteps.2 ⟨hlt.1, hseq, hR.msgValid, hfwd⟩

/-- **Lemma 6.4** (countably many processors): the classical executions of `A` are exactly the
total orderings of computational executions of `A`. -/
theorem lemma_6_4 [Countable Proc] {S : Set (Step A)} {lt : S → S → Prop} :
    IsClassical A S lt ↔ ∃ R, IsComputational A S R ∧ IsTotalOrderingOf R lt := by
  refine ⟨lemma_6_4_forward, fun ⟨R, hR, hlt⟩ => ?_⟩
  have : Countable S := hR.procSeq.countable
  exact lemma_6_4_backward hR hlt

/-- **Corollary 6.5** (countable executions): every total ordering of a relativistic execution is
a classical execution. -/
theorem corollary_6_5 (X : Spacetime) {S : Set (Step A)} [Countable S] {prec lt : S → S → Prop}
    (h : IsRelativistic X A S prec) (hlt : IsTotalOrderingOf prec lt) : IsClassical A S lt := by
  obtain ⟨R, hR, hsub⟩ := lemma_6_2' X h
  exact lemma_6_4_backward hR ⟨hlt.1, fun a b h => hlt.2 a b (hsub a b h)⟩

/-! ### Lemma 6.6 -/

/-- **Lemma 6.6** (strong form). Every classical execution `(S, <_S)` is extracted from a
relativistic physical execution `(S, ε)` in which all processors move along the world line of a
body at rest in a frame `F`; moreover `≺_S` and the chronological order of `F` both coincide with
`<_S`, and no two steps are simultaneous in `F`. -/
theorem lemma_6_6_strong (X : Spacetime) {S : Set (Step A)} {lt : S → S → Prop}
    (h : IsClassical A S lt) :
    ∃ ε : S → X.Pt, IsRelPhys X A S ε ∧ (∀ a b, lt a b ↔ X.prec (ε a) (ε b)) ∧
      ∃ F : X.Frame, Function.Injective (fun s => X.time F (ε s)) ∧
        ∀ a b, lt a b ↔ X.time F (ε a) < X.time F (ε b) := by
  obtain ⟨t, ht, hlt⟩ := h
  obtain ⟨F, γ, hwl, htime, hmono⟩ := X.rest
  have hγ : ∀ τ τ', X.prec (γ τ) (γ τ') ↔ τ < τ' := fun τ τ' =>
    ⟨fun h => by simpa [htime] using X.time_mono F _ _ h, hmono τ τ'⟩
  have hiff : ∀ a b, X.prec (γ (t a)) (γ (t b)) ↔ t a < t b := fun a b => hγ _ _
  refine ⟨fun s => γ (t s), ⟨?_, ⟨fun _ => Set.range γ, fun _ => hwl, fun s => ⟨t s, rfl⟩⟩, ?_,
    ht.msgValid, ?_⟩, fun a b => (hlt a b).trans (hiff a b).symm, F, ?_, ?_⟩
  · intro a b hab
    apply ht.inj
    simpa [htime] using congrArg (X.time F) hab
  · rw [rel_eq_of_iff hiff]; exact ht.procSeq
  · rw [rel_eq_of_iff hiff]; exact ht.msgForward
  · intro a b hab
    apply ht.inj
    simpa [htime] using hab
  · intro a b
    simp only [htime]
    exact hlt a b

/-- **Lemma 6.6.** Every classical execution is also a relativistic execution. -/
theorem lemma_6_6 (X : Spacetime) {S : Set (Step A)} {lt : S → S → Prop}
    (h : IsClassical A S lt) : IsRelativistic X A S lt := by
  obtain ⟨ε, hε, hlt, -⟩ := lemma_6_6_strong X h
  exact ⟨ε, hε, hlt⟩

/-! ### The Central Theorem -/

/-- A property of totally ordered executions (a predicate on pairs `(S, <_S)`). -/
abbrev Property (A : Algorithm Proc Msg) := (S : Set (Step A)) → (S → S → Prop) → Prop

/-- (1) `P` is satisfied by all classical executions of `A` (whose step set lies in the class
`C`; by default all executions). -/
def ClassicallySatisfies (A : Algorithm Proc Msg) (P : Property A)
    (C : Set (Set (Step A)) := Set.univ) : Prop :=
  ∀ S ∈ C, ∀ lt, IsClassical A S lt → P S lt

/-- (2) `P` is satisfied by all total orderings of computational executions of `A`. -/
def ComputationallySatisfies (A : Algorithm Proc Msg) (P : Property A)
    (C : Set (Set (Step A)) := Set.univ) : Prop :=
  ∀ S ∈ C, ∀ R, IsComputational A S R → ∀ lt, IsTotalOrderingOf R lt → P S lt

/-- (3) `P` is satisfied in the reference frame of every observer of every relativistic execution
of `A`. An observer in frame `F` perceives the steps in the chronological order of `F`; steps that
are simultaneous in `F` may be perceived in any order (all tie-breakings must satisfy `P`). -/
def RelativisticallySatisfies (X : Spacetime) (A : Algorithm Proc Msg) (P : Property A)
    (C : Set (Set (Step A)) := Set.univ) : Prop :=
  ∀ S ∈ C, ∀ ε, IsRelPhys X A S ε → ∀ (F : X.Frame) (lt : S → S → Prop), IsSTO lt →
    (∀ a b, X.time F (ε a) < X.time F (ε b) → lt a b) → P S lt

/-- (3') Variant of (3) quantifying only over frames in which no two steps are simultaneous (then
the chronological order of the frame is a total order of the steps). -/
def RelativisticallySatisfies' (X : Spacetime) (A : Algorithm Proc Msg) (P : Property A)
    (C : Set (Set (Step A)) := Set.univ) : Prop :=
  ∀ S ∈ C, ∀ ε, IsRelPhys X A S ε → ∀ F : X.Frame, Function.Injective (fun s => X.time F (ε s)) →
    P S (fun a b => X.time F (ε a) < X.time F (ε b))

/-- (2) ⟹ (3), for any class of executions. -/
theorem comp_to_rel (X : Spacetime) {P : Property A} {C : Set (Set (Step A))}
    (h : ComputationallySatisfies A P C) : RelativisticallySatisfies X A P C := by
  intro S hS ε hε F lt hsto hF
  obtain ⟨R, hR, hsub⟩ := lemma_6_2 X hε
  exact h S hS R hR lt ⟨hsto, fun a b hab => hF a b (X.time_mono F _ _ (hsub a b hab))⟩

/-- (3) ⟹ (1), for any class of executions. -/
theorem rel_to_classical (X : Spacetime) {P : Property A} {C : Set (Set (Step A))}
    (h : RelativisticallySatisfies X A P C) : ClassicallySatisfies A P C := by
  intro S hS lt hcl
  obtain ⟨ε, hε, -, F, -, hF⟩ := lemma_6_6_strong X hcl
  exact h S hS ε hε F lt hcl.isSTO fun a b hab => (hF a b).2 hab

/-- (1) ⟹ (2), for any class of executions with countably many steps. -/
theorem classical_to_comp {P : Property A} {C : Set (Set (Step A))}
    (hC : ∀ S ∈ C, Countable S) (h : ClassicallySatisfies A P C) :
    ComputationallySatisfies A P C := by
  intro S hS R hR lt hlt
  have : Countable S := hC S hS
  exact h S hS lt (lemma_6_4_backward hR hlt)

/-- **Theorem 6.7 (Central Theorem)**, for any class `C` of executions with countably many steps
(e.g. all finite executions): the three statements are equivalent. -/
theorem theorem_6_7_on (X : Spacetime) (P : Property A) (C : Set (Set (Step A)))
    (hC : ∀ S ∈ C, Countable S) :
    (ClassicallySatisfies A P C ↔ ComputationallySatisfies A P C) ∧
      (ComputationallySatisfies A P C ↔ RelativisticallySatisfies X A P C) :=
  ⟨⟨classical_to_comp hC, fun h => rel_to_classical X (comp_to_rel X h)⟩,
    ⟨comp_to_rel X, fun h => classical_to_comp hC (rel_to_classical X h)⟩⟩

/-- **Theorem 6.7 (Central Theorem).** For a distributed algorithm `A` with countably many
processors and any property `P` of totally ordered executions, the following are equivalent:
(1) `P` is satisfied by all classical executions of `A`; (2) `P` is satisfied by all total
orderings of computational executions of `A`; (3) `P` is satisfied in the reference frame of every
observer of every relativistic execution of `A`. (Without countability, (1) ⟹ (2) fails:
`theorem_6_7_false`.) -/
theorem theorem_6_7 [Countable Proc] (X : Spacetime) (P : Property A) :
    (ClassicallySatisfies A P ↔ ComputationallySatisfies A P) ∧
      (ComputationallySatisfies A P ↔ RelativisticallySatisfies X A P) := by
  constructor
  · refine ⟨fun h => ?_, fun h => rel_to_classical X (comp_to_rel X h)⟩
    intro S _ R hR lt hlt
    have : Countable S := hR.procSeq.countable
    exact h S trivial lt (lemma_6_4_backward hR hlt)
  · refine ⟨comp_to_rel X, fun h => ?_⟩
    intro S _ R hR lt hlt
    have : Countable S := hR.procSeq.countable
    exact rel_to_classical X h S trivial lt (lemma_6_4_backward hR hlt)

/-- **Classical ⟺ relativistic, unconditionally.** For any algorithm (any number of processors),
`P` holds for all classical executions iff it holds in every relativistic execution for every
observer whose frame orders the steps strictly. -/
theorem classical_iff_frames (X : Spacetime) (P : Property A) (C : Set (Set (Step A))) :
    ClassicallySatisfies A P C ↔ RelativisticallySatisfies' X A P C := by
  constructor
  · intro h S hS ε hε F hinj
    apply h S hS
    refine ⟨fun s => X.time F (ε s), ⟨hinj, ?_, hε.msgValid, ?_⟩, fun _ _ => Iff.rfl⟩
    · refine hε.procSeq.congr fun a b hab => ⟨X.time_mono F _ _, fun hlt => ?_⟩
      have hne : a ≠ b := by rintro rfl; exact lt_irrefl _ hlt
      rcases hε.procSeq.total a b hab hne with h' | h'
      · exact h'
      · exact absurd (X.time_mono F _ _ h') (not_lt.2 hlt.le)
    · exact fun a b hab => X.time_mono F _ _ (hε.msgForward a b hab)
  · intro h S hS lt hcl
    obtain ⟨ε, hε, -, F, hinj, hF⟩ := lemma_6_6_strong X hcl
    rw [rel_eq_of_iff hF]
    exact h S hS ε hε F hinj

end RelativisticComputing
