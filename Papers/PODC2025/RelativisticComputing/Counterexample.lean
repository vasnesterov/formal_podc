import Papers.PODC2025.RelativisticComputing.Central

/-!
# Lemma 6.3/6.4 and the Central Theorem fail for uncountably many processors

The backward direction of Lemma 6.3 (P1–P3 ⟹ classical) and the second half of Lemma 6.4 (every
total ordering of a computational execution is a classical execution) construct the time map by
listing the steps as a sequence `s₁, s₂, …` in `<_S` order and setting `t(sᵢ) = i`. This assumes
that `<_S` has order type at most `ω`, which is false in general:

* even for two processors, `<_S` can have order type `ω + 1` (`omegaPlusOne`): the statement still
  holds, because every countable linear order embeds into `ℝ` (`lemma_6_3_of_countable`);
* for uncountably many processors the statements are false: with processors indexed by the
  "double arrow" `ℝ ×ₗ Bool`, each taking one step and sending no message, the empty relation is a
  computational execution and the lexicographic order of the processors is a total ordering of it,
  but this order does not embed into `(ℝ, <)`, so it is not a classical execution
  (`lemma_6_4_false`, `lemma_6_3_false`; the same order is a total ordering of a relativistic
  execution in which all steps are simultaneous for one observer, refuting Corollary 6.5:
  `corollary_6_5_false`). Consequently (1) ⟹ (2) of the Central Theorem fails for
  the property "the order embeds into the real line" (`theorem_6_7_false`); (1) ⟹ (3) fails as
  well when observers may perceive simultaneous steps in any order (`theorem_6_7_false_frames`).
-/

namespace RelativisticComputing

/-- The trivial algorithm: one state, one event, every transition allowed, no messages. -/
def trivAlg (Proc : Type) : Algorithm Proc Empty where
  State := Unit
  Event := Unit
  init _ := Set.univ
  δ _ _ _ _ := True
  sendTo _ := none
  recv _ := none

/-- The double arrow: `ℝ × Bool` ordered lexicographically. -/
abbrev DArrow := Lex (ℝ × Bool)

/-- The step taken by processor `p` in the trivial algorithm. -/
def tstep {Proc : Type} (p : Proc) : Step (trivAlg Proc) := ⟨p, (), (), (), trivial⟩

lemma tstep_proc {Proc : Type} (s : Step (trivAlg Proc)) : tstep s.proc = s := by
  cases s; rfl

/-- All steps of the trivial algorithm (one per processor). -/
def S₀ (Proc : Type) : Set (Step (trivAlg Proc)) := Set.univ

/-- The lexicographic order of the processors. -/
def lt₀ (a b : S₀ DArrow) : Prop := a.1.proc < b.1.proc

lemma S₀_ext {Proc : Type} {a b : S₀ Proc} (h : a.1.proc = b.1.proc) : a = b := by
  apply Subtype.ext
  rw [← tstep_proc a.1, ← tstep_proc b.1, h]

lemma msgEdge_S₀ {Proc : Type} (a b : S₀ Proc) : ¬ MsgEdge a b := by
  rintro ⟨m, -, -⟩; exact m.elim

lemma msgValid_S₀ (Proc : Type) : MsgValid (S₀ Proc) :=
  ⟨fun _ _ m => m.elim, fun _ _ m => m.elim⟩

/-- The empty relation is a computational execution on `S₀`. -/
lemma isComputational_S₀ (Proc : Type) :
    IsComputational (trivAlg Proc) (S₀ Proc) (fun _ _ => False) where
  closure := by
    funext a b
    apply propext
    refine ⟨False.elim, fun h => ?_⟩
    induction h with
    | single h => rcases h with ⟨_, h⟩ | h
                  · exact h
                  · exact msgEdge_S₀ _ _ h
    | tail _ _ ih => exact ih
  procSeq :=
    { irrefl := fun _ h => h
      trans := fun _ _ _ _ _ h => h.elim
      total := fun a b hab hne => (hne (S₀_ext hab)).elim
      finite_pred := fun _ => by simp
      rooted := fun _ _ => Set.mem_univ _
      consec := fun _ _ _ h => h.elim }
  msgValid := msgValid_S₀ Proc
  msgForward a b h := msgEdge_S₀ a b h

lemma isSTO_lt₀ : IsSTO lt₀ where
  irrefl a := lt_irrefl a.1.proc
  trans _ _ _ := lt_trans
  total _ _ hne := lt_or_gt_of_ne fun h => hne (S₀_ext h)

/-- The double-arrow order of the steps does not embed into the real line. -/
theorem lt₀_not_real : ¬ ∃ t : S₀ DArrow → ℝ, ∀ a b, lt₀ a b ↔ t a < t b := by
  rintro ⟨t, ht⟩
  let st : DArrow → S₀ DArrow := fun p => ⟨tstep p, Set.mem_univ _⟩
  have h1 : ∀ x : ℝ, t (st (toLex (x, false))) < t (st (toLex (x, true))) := fun x =>
    (ht _ _).1 (Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, Bool.false_lt_true⟩))
  have h2 : ∀ x y : ℝ, x < y → t (st (toLex (x, true))) < t (st (toLex (y, false))) :=
    fun x y hxy => (ht _ _).1 (Prod.Lex.toLex_lt_toLex.2 (Or.inl hxy))
  choose q hq using fun x => exists_rat_btwn (h1 x)
  have hmono : StrictMono q := fun x y hxy => by
    have := h2 x y hxy
    have a := (hq x).2
    have b := (hq y).1
    exact_mod_cast (a.trans this).trans b
  have : Countable ℝ := hmono.injective.countable
  exact Cardinal.not_countable_real (Set.countable_univ_iff.2 this)

/-- **Lemma 6.4 (second half) is false** for uncountably many processors: a total ordering of a
computational execution that is not a classical execution. -/
theorem lemma_6_4_false :
    IsComputational (trivAlg DArrow) (S₀ DArrow) (fun _ _ => False) ∧
      IsTotalOrderingOf (fun _ _ => False) lt₀ ∧ ¬ IsClassical (trivAlg DArrow) (S₀ DArrow) lt₀ :=
  ⟨isComputational_S₀ _, ⟨isSTO_lt₀, fun _ _ h => h.elim⟩,
    fun ⟨t, _, ht⟩ => lt₀_not_real ⟨t, ht⟩⟩

/-- **Lemma 6.3 (backward direction) is false** for uncountably many processors: `(S₀, lt₀)`
satisfies P1, P2 and P3 but is not a classical execution. -/
theorem lemma_6_3_false :
    IsSTO lt₀ ∧ ProcSeq (S₀ DArrow) lt₀ ∧ MsgValid (S₀ DArrow) ∧ MsgForward (S₀ DArrow) lt₀ ∧
      ¬ IsClassical (trivAlg DArrow) (S₀ DArrow) lt₀ := by
  obtain ⟨hR, hlt, hncl⟩ := lemma_6_4_false
  obtain ⟨hseq, hfwd⟩ := procSeq_of_totalOrdering hR hlt
  exact ⟨isSTO_lt₀, hseq, msgValid_S₀ _, hfwd, hncl⟩

/-- The property "the order embeds into the real line". -/
def EmbedsInReals {Proc Msg : Type} {A : Algorithm Proc Msg} : Property A :=
  fun S lt => ∃ t : S → ℝ, ∀ a b, lt a b ↔ t a < t b

/-- **Theorem 6.7 is false** for uncountably many processors: for the trivial algorithm on the
processors `ℝ ×ₗ Bool`, the property "the order embeds into `ℝ`" holds for all classical
executions, and in every relativistic execution for every observer whose frame orders the steps
strictly, but not for all total orderings of computational executions. -/
theorem theorem_6_7_false :
    ClassicallySatisfies (trivAlg DArrow) EmbedsInReals ∧
      (∀ X : Spacetime, RelativisticallySatisfies' X (trivAlg DArrow) EmbedsInReals) ∧
      ¬ ComputationallySatisfies (trivAlg DArrow) EmbedsInReals := by
  have hcl : ClassicallySatisfies (trivAlg DArrow) EmbedsInReals :=
    fun _ _ _ ⟨t, _, ht⟩ => ⟨t, ht⟩
  refine ⟨hcl, fun X => (classical_iff_frames X _ _).1 hcl, fun h => ?_⟩
  obtain ⟨hR, hlt, -⟩ := lemma_6_4_false
  exact lt₀_not_real (h _ trivial _ hR _ hlt)

/-! ### The tie-breaking reading of (3) also fails -/

/-- An injection `ℝ × Bool → ℝ`. -/
noncomputable def daPos (p : ℝ × Bool) : ℝ := if p.2 then -Real.exp p.1 else Real.exp p.1

lemma daPos_injective : Function.Injective daPos := by
  rintro ⟨x, c⟩ ⟨y, d⟩ h
  have ex := Real.exp_pos x
  have ey := Real.exp_pos y
  cases c <;> cases d <;> simp only [daPos, Bool.false_eq_true, ite_false, ite_true,
    neg_inj, Real.exp_eq_exp] at h
  · rw [h]
  · linarith
  · linarith
  · rw [h]

/-- Place the step of processor `(x, b)` at time `0` and position `± exp x` (`+` for `false`,
`-` for `true`) in `1+1`-dimensional Minkowski spacetime: all steps are simultaneous for the
observer at rest. -/
noncomputable def εDA (a : S₀ DArrow) : (minkowski 1).Pt :=
  (0, EuclideanSpace.single 0 (daPos (ofLex a.1.proc)))

lemma εDA_injective : Function.Injective εDA := by
  intro a b hab
  apply S₀_ext
  have h := congrArg (fun e : (minkowski 1).Pt => e.2 0) hab
  simp only [εDA, PiLp.single_apply, ite_true] at h
  exact ofLex_inj.1 (daPos_injective h)

/-- Any injective placement of the steps of the trivial algorithm in any spacetime, with each
processor's single step on its own (one-point) world line, is a relativistic physical
execution. -/
lemma isRelPhys_trivAlg {Proc : Type} (X : Spacetime) (ε : S₀ Proc → X.Pt)
    (hε : Function.Injective ε) (hwl : ∀ e, X.IsWorldLine {e}) :
    IsRelPhys X (trivAlg Proc) (S₀ Proc) ε where
  inj := hε
  worldLines := by
    refine ⟨fun p => {ε ⟨tstep p, Set.mem_univ _⟩}, fun p => hwl _, fun s => ?_⟩
    simp only [Set.mem_singleton_iff, tstep_proc]
  procSeq :=
    { irrefl := fun _ h => X.prec_irrefl _ h
      trans := fun _ _ _ _ _ h1 h2 => X.prec_trans _ _ _ h1 h2
      total := fun a b hab hne => (hne (S₀_ext hab)).elim
      finite_pred := fun a => by
        refine Set.Finite.subset (Set.finite_singleton a) fun b ⟨hb, _⟩ => ?_
        exact S₀_ext hb
      rooted := fun _ _ => Set.mem_univ _
      consec := fun _ _ _ _ _ => rfl }
  msgValid := msgValid_S₀ _
  msgForward a b h := (msgEdge_S₀ a b h).elim

lemma isRelPhys_εDA : IsRelPhys (minkowski 1) (trivAlg DArrow) (S₀ DArrow) εDA :=
  isRelPhys_trivAlg _ _ εDA_injective fun _ => Set.subsingleton_singleton.isChain

/-- **Theorem 6.7, (1) ⟹ (3) is false** for uncountably many processors when an observer may
perceive simultaneous steps in any order (`RelativisticallySatisfies`): all steps of the
execution `εDA` are simultaneous for the observer at rest, and ordering them lexicographically
gives an order that does not embed into `ℝ`. -/
theorem theorem_6_7_false_frames :
    ClassicallySatisfies (trivAlg DArrow) EmbedsInReals ∧
      ¬ RelativisticallySatisfies (minkowski 1) (trivAlg DArrow) EmbedsInReals := by
  refine ⟨fun _ _ _ ⟨t, _, ht⟩ => ⟨t, ht⟩, fun h => ?_⟩
  refine lt₀_not_real (h _ trivial εDA isRelPhys_εDA ⟨0, by simp⟩ lt₀ isSTO_lt₀ fun a b hab => ?_)
  exfalso
  simp [minkowski, minkTime, εDA] at hab

/-- **Corollary 6.5 is false** for uncountably many processors: in the relativistic execution
`εDA` no two steps are causally related, so the lexicographic order `lt₀` is a total ordering of
it, but `lt₀` is not a classical execution. -/
theorem corollary_6_5_false :
    IsRelativistic (minkowski 1) (trivAlg DArrow) (S₀ DArrow)
        (fun a b => (minkowski 1).prec (εDA a) (εDA b)) ∧
      IsTotalOrderingOf (fun a b => (minkowski 1).prec (εDA a) (εDA b)) lt₀ ∧
      ¬ IsClassical (trivAlg DArrow) (S₀ DArrow) lt₀ := by
  refine ⟨⟨εDA, isRelPhys_εDA, fun _ _ => Iff.rfl⟩, ⟨isSTO_lt₀, fun a b ⟨hne, h⟩ => ?_⟩,
    lemma_6_4_false.2.2⟩
  exfalso
  apply hne
  simp only [εDA, sub_self] at h ⊢
  have h0 : ‖EuclideanSpace.single (0 : Fin 1) (daPos (ofLex b.1.proc)) -
      EuclideanSpace.single 0 (daPos (ofLex a.1.proc))‖ = 0 := le_antisymm h (norm_nonneg _)
  rw [norm_eq_zero, sub_eq_zero] at h0
  rw [h0]

end RelativisticComputing
