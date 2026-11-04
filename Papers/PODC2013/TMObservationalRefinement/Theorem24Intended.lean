import Papers.PODC2013.TMObservationalRefinement.Theorem24

/-!
# The Theorem 24 counterexample needs the literal Figure 2

`theorem_24_false` uses the trace sets of Figure 2 *as printed* (`Tr`). There, the trace of the body
`C` goes on after an aborted method call, and the first rule for `x := atomic {C}` requires the
whole trace of `C` to end with `aborted`. So if the body has, say, a local assignment after the call,
an aborted call never lets the block finish with `x := aborted`, and the effect of that assignment
can be reproduced by a successful call instead.

Section 2 states the intended semantics: when the transactional system aborts a call, "the
execution of C terminates" (and the trace set "contains traces in which C is aborted in the
middle of its execution"); the journal version's Figure 4 formalizes this. `TrI` is Figure 2 with this
repair: the body of an atomic block is cut at its first `aborted`.

`theorem_24_cex_fails_intended`: with the repaired trace sets, the pair `H_C`, `H_A` of
`theorem_24_false` is **not** in the state-observational-refinement relation, already for the
minimal deterministic language. The witness program is `r := atomic { y := o.f(1); z := 1 }`: the
trace in which the call is aborted ends with `r = aborted` and `z` unchanged, while every trace with
a history in `H_A` that sets `r` to `aborted` runs `z := 1`.

This does not prove Theorem 24 for the repaired semantics; it shows that the refutation in
`Theorem24.lean` rests on the Figure 2 slip that `prop_13_false` documents.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Podc.TMObservationalRefinement

open IKind Act Lang CmdClass

variable {T LV GV O M BE IE C : Type} [Lang T LV GV BE IE C]

/-- Figure 2 with the intended semantics of aborts (Section 2: "Once this happens, the execution of
C terminates"; JACM Figure 4): the body of an atomic block is cut at its first `aborted`. Only the
three rules for atomic blocks differ from `Tr`. -/
inductive TrI (t : T) : Cmd LV O M C BE IE → List (Act T O M C) → Prop
  | prim (c : C) : TrI t (.prim c) [.cmd t c]
  | seq {C₁ C₂ τ₁ τ₂} : TrI t C₁ τ₁ → TrI t C₂ τ₂ → TrI t (.seq C₁ C₂) (τ₁ ++ τ₂)
  | iteT {b C₁ C₂ τ} : TrI t C₁ τ → TrI t (.ite b C₁ C₂) (.cmd t (assume t b true) :: τ)
  | iteF {b C₁ C₂ τ} : TrI t C₂ τ → TrI t (.ite b C₁ C₂) (.cmd t (assume t b false) :: τ)
  | whileF {b C} : TrI t (.while b C) [.cmd t (assume t b false)]
  | whileT {b C τ τ'} : TrI t C τ → TrI t (.while b C) τ' →
      TrI t (.while b C) (.cmd t (assume t b true) :: (τ ++ τ'))
  | callRet {x o f e} (n n' : ℤ) : TrI t (.call x o f e)
      [.cmd t (assumeEq t e n), .iface t (.call o f n), .iface t (.ret n' o f),
        .cmd t (assign t x n')]
  | callAbort {x o f e} (n : ℤ) : TrI t (.call x o f e)
      [.cmd t (assumeEq t e n), .iface t (.call o f n), .iface t .aborted]
  | atomicAbort {x Cb τ τ'} : TrI t Cb (τ ++ .iface t .aborted :: τ') → .iface t .aborted ∉ τ →
      TrI t (.atomic x Cb) (.iface t .txbegin :: .iface t .ok :: (τ ++
        [.iface t .aborted, .cmd t (assign t x (vAb C))]))
  | atomicCommit {x Cb τ} : TrI t Cb τ → .iface t .aborted ∉ τ →
      TrI t (.atomic x Cb) (.iface t .txbegin :: .iface t .ok :: (τ ++
        [.iface t .txcommit, .iface t .committed, .cmd t (assign t x (vCom C))]))
  | atomicCommitAbort {x Cb τ} : TrI t Cb τ → .iface t .aborted ∉ τ →
      TrI t (.atomic x Cb) (.iface t .txbegin :: .iface t .ok :: (τ ++
        [.iface t .txcommit, .iface t .aborted, .cmd t (assign t x (vAb C))]))

variable [DecidableEq T]

/-- `A(P)` with the repaired atomic-block rules. -/
def InAI (P : Prog T LV O M C BE IE) (τ : List (Act T O M C)) : Prop :=
  ∃ τ', τ <+: τ' ∧ ∀ t, TrI t (P t) (tproj t τ')

/-- `[[P]](s, H)` with the repaired atomic-block rules. -/
def denHI (P : Prog T LV O M C BE IE) (s : State T LV GV) (H : Set (List (IAct T O M))) :
    Set (List (Act T O M C)) :=
  {τ | InAI P τ ∧ eval s τ ≠ ∅ ∧ history τ ∈ H}

/-- Definition 14 (`H_C ⊑_state H_A`) with the repaired atomic-block rules. -/
def StateRefI (O M : Type) (HC HA : Set (List (IAct T O M))) : Prop :=
  ∀ P : Prog T LV O M C BE IE, P.Allowed → ∀ (s : State T LV GV) τ, τ ∈ denHI P s HC →
    ∃ τ' ∈ denHI P s HA, eval s τ = eval s τ'

/-! ### The witness program, in the minimal language with one thread -/

section witness

local notation "A" => Act Unit Unit Unit (MinCmd Unit)
local notation "St" => State Unit ℕ ℕ

/-- `r := atomic { y := o.f(1); z := 1 }` with `r = 0`, `y = 1`, `z = 2`. -/
def t24iProg : Prog Unit ℕ Unit Unit (MinCmd Unit) MinBE MinIE := fun _ =>
  .atomic 0 (.seq (.call 1 () () (fun _ => 1)) (.prim (Lang.assign (C := MinCmd Unit) () 2 1)))

lemma t24i_tproj (τ : List A) : tproj () τ = τ := List.filter_eq_self.mpr (by simp)

lemma t24i_evalSet_iface (σ : St) (k : IKind Unit Unit) (l : List A) :
    evalSet {σ} (iface () k :: l) = evalSet {σ} l := by
  simp only [evalSet]; congr 1; ext; simp [evalStep, eval1]

lemma t24i_evalSet_assign (σ : St) (x : ℕ) (n : ℤ) (l : List A) :
    evalSet {σ} (cmd () (Lang.assign (C := MinCmd Unit) () x n) :: l) =
      evalSet {Function.update σ (.inr ((), x)) n} l := by
  simp only [evalSet]; congr 1; ext; simp [evalStep, eval1, Lang.sem, MinCmd.sem, Lang.assign]

lemma t24i_evalSet_assumeEq (σ : St) (n : ℤ) (l : List A) :
    evalSet {σ} (cmd () (Lang.assumeEq (C := MinCmd Unit) () (fun _ => 1) n) :: l) =
      if (1 : ℤ) = n then evalSet {σ} l else ∅ := by
  simp only [evalSet]
  split_ifs with h
  · congr 1; ext; simp [evalStep, eval1, Lang.sem, MinCmd.sem, Lang.assumeEq, h]
  · rw [show evalStep {σ} (cmd () (Lang.assumeEq (C := MinCmd Unit) () (fun _ => 1) n) : A) = ∅ by
      ext; simp [evalStep, eval1, Lang.sem, MinCmd.sem, Lang.assumeEq, h]]
    exact t24_evalSet_empty _

lemma t24i_evalSet_nil (σ : St) : evalSet {σ} ([] : List A) = {σ} := rfl

/-- The initial state: every variable is `5`. -/
def t24iS : St := fun _ => 5

/-- The final state of the trace with the aborted call: `r = aborted (= 0)`. -/
def t24iF : St := Function.update t24iS (.inr ((), 0)) 0

/-- The trace in which the call is aborted and the block ends with `r := aborted`. -/
def t24iTau : List A :=
  [iface () txbegin, iface () ok, cmd () (Lang.assumeEq (C := MinCmd Unit) () (fun _ => 1) 1),
    iface () (.call () () 1), iface () aborted, cmd () (Lang.assign (C := MinCmd Unit) () 0 0)]

lemma t24i_eval_tau : eval t24iS t24iTau = {t24iF} := by
  simp [eval, t24iTau, t24i_evalSet_iface, t24i_evalSet_assumeEq, t24i_evalSet_assign,
    t24i_evalSet_nil, t24iF]


/-- **The counterexample of `theorem_24_false` fails for the intended semantics of aborts.**
With the repaired trace sets `TrI`, the transactional systems `H_C` (prefixes of
`txbegin OK call aborted`) and `H_A` (prefixes of `txbegin OK call ret(v) txcommit aborted`) are not
in the state-observational-refinement relation, even for the minimal deterministic language. -/
theorem theorem_24_cex_fails_intended :
    ¬ StateRefI (T := Unit) (LV := ℕ) (GV := ℕ) (C := MinCmd Unit) (BE := MinBE) (IE := MinIE)
      Unit Unit {h | h <+: t24H (() : Unit) (() : Unit) (() : Unit)}
      {h | ∃ v, h <+: t24S (() : Unit) (() : Unit) (() : Unit) v} := by
  intro hR
  have hP : (t24iProg).Allowed := fun u => by
    simp [t24iProg, Cmd.Allowed, IsAssume, Lang.assume, Lang.assumeEq, CmdClass.thr, CmdClass.glob,
      MinCmd.thr, MinCmd.glob]
  have hbody : TrI () (.seq (.call 1 () () (fun _ => 1))
      (.prim (Lang.assign (C := MinCmd Unit) () 2 1)) : Cmd ℕ Unit Unit (MinCmd Unit) MinBE MinIE)
      (([cmd () (Lang.assumeEq (C := MinCmd Unit) () (fun _ => 1) 1), iface () (.call () () 1)] :
        List A) ++ iface () aborted :: [cmd () (Lang.assign (C := MinCmd Unit) () 2 1)]) :=
    TrI.seq (C₁ := .call 1 () () (fun _ => 1))
      (τ₁ := ([cmd () (Lang.assumeEq (C := MinCmd Unit) () (fun _ => 1) 1),
        iface () (.call () () 1), iface () aborted] : List A)) (TrI.callAbort 1) (TrI.prim _)
  have hτ : t24iTau ∈
      denHI t24iProg t24iS {h | h <+: t24H (() : Unit) (() : Unit) (() : Unit)} := by
    refine ⟨⟨t24iTau, List.prefix_refl _, fun u => ?_⟩, ?_, ?_⟩
    · rw [t24i_tproj]
      exact TrI.atomicAbort (x := 0) hbody (by simp)
    · rw [t24i_eval_tau]; simp
    · simp [t24iTau, history, t24H, List.filterMap_cons]
  obtain ⟨τ', ⟨⟨τ₀, hpre, htr⟩, hne, ⟨v, hv⟩⟩, heq⟩ := hR t24iProg hP t24iS t24iTau hτ
  rw [t24i_eval_tau] at heq
  have hF : t24iF ∈ eval t24iS τ' := by rw [← heq]; rfl
  have h0 := htr ()
  rw [t24i_tproj] at h0
  obtain ⟨k, rfl⟩ : ∃ k, τ' = τ₀.take k := ⟨_, List.prefix_iff_eq_take.mp hpre⟩
  clear hpre htr hτ heq hne
  simp only [t24iProg] at h0
  cases h0 with
  | atomicAbort hb hn =>
    rename_i τ τ''
    generalize hl : τ ++ _ = l at hb
    cases hb with
    | seq h1 h2 =>
      cases h2
      cases h1 with
      | callRet n n' =>
        have : (iface () aborted : A) ∈ τ ++ iface () aborted :: τ'' := by simp
        rw [hl] at this; simp at this
      | callAbort n =>
        rcases τ with _ | ⟨a, _ | ⟨b, _ | ⟨c, τ⟩⟩⟩ <;> simp at hl hn
        · obtain ⟨rfl, rfl, rfl⟩ := hl
          rcases k with _ | _ | _ | _ | _ | _ | k <;>
            simp [eval, t24i_evalSet_iface, t24i_evalSet_assumeEq, t24i_evalSet_assign,
              t24i_evalSet_nil, history, List.filterMap_cons, t24S] at hF hv
          all_goals first
            | (have h := congrFun hF (Sum.inr ((), 0)); simp [t24iF, t24iS] at h; done)
            | (have h := congrFun hF.2 (Sum.inr ((), 0)); simp [t24iF, t24iS] at h; done)
            | (have h := congrFun hF (Sum.inr ((), 2)); simp [t24iF, t24iS] at h; done)
            | (have h := congrFun hF.2 (Sum.inr ((), 2)); simp [t24iF, t24iS] at h; done)
        · exact absurd hl.2.2.1.symm hn.2.2.1
  | atomicCommit hb hn =>
    cases hb with
    | seq h1 h2 =>
      cases h2
      cases h1 with
      | callAbort n => simp at hn
      | callRet n n' =>
        rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;>
          simp [eval, t24i_evalSet_iface, t24i_evalSet_assumeEq, t24i_evalSet_assign,
            t24i_evalSet_nil, history, List.filterMap_cons, t24S] at hF hv
        all_goals first
          | (have h := congrFun hF (Sum.inr ((), 0)); simp [t24iF, t24iS] at h; done)
          | (have h := congrFun hF.2 (Sum.inr ((), 0)); simp [t24iF, t24iS] at h; done)
          | (have h := congrFun hF (Sum.inr ((), 2)); simp [t24iF, t24iS] at h; done)
          | (have h := congrFun hF.2 (Sum.inr ((), 2)); simp [t24iF, t24iS] at h; done)
  | atomicCommitAbort hb hn =>
    cases hb with
    | seq h1 h2 =>
      cases h2
      cases h1 with
      | callAbort n => simp at hn
      | callRet n n' =>
        rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;>
          simp [eval, t24i_evalSet_iface, t24i_evalSet_assumeEq, t24i_evalSet_assign,
            t24i_evalSet_nil, history, List.filterMap_cons, t24S] at hF hv
        all_goals first
          | (have h := congrFun hF (Sum.inr ((), 0)); simp [t24iF, t24iS] at h; done)
          | (have h := congrFun hF.2 (Sum.inr ((), 0)); simp [t24iF, t24iS] at h; done)
          | (have h := congrFun hF (Sum.inr ((), 2)); simp [t24iF, t24iS] at h; done)
          | (have h := congrFun hF.2 (Sum.inr ((), 2)); simp [t24iF, t24iS] at h; done)

end witness

end Podc.TMObservationalRefinement
