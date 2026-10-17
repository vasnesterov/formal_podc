import Papers.PODC2011.KSetAgreement.InitDeadImpossible

/-!
# Restricted algorithms (Definition 1) and lifting their executions

`A.restrict D` is the paper's restricted algorithm `A|D` (Definition 1): the same code, run by the
processes of `D` only, with all messages to processes outside `D` dropped. An execution of the
compiled restricted algorithm (with arbitrary input function `ι`) is *lifted* to an execution of
`A` on all processes, in which the processes outside `D` never take a step (they are initially
dead) and the processes of `D` go through exactly the same local states. Fairness and crashes of
the processes of `D` are preserved by the lifting.
-/

namespace KSetAgreement

open Cslib Cslib.FLP

variable {P M S V : Type*} [DecidableEq P] [DecidableEq M]

namespace KAlgorithm

variable (A : KAlgorithm P M S V) (D : Finset P)

/-- Keep only the messages to `D`, re-addressed to the subtype. -/
def restrictSends (ms : Multiset (P × M)) : Multiset ({p // p ∈ D} × M) :=
  ms.filterMap fun qm => if h : qm.1 ∈ D then some (⟨qm.1, h⟩, qm.2) else none

/-- **Definition 1** of [BRS11]: the restricted algorithm `A|D`, obtained by dropping all messages
sent to processes outside `D` (the code is unchanged). -/
def restrict : KAlgorithm {p // p ∈ D} M S V where
  init p v := A.init p.1 v
  step p e st := A.step p.1 e st
  send p e st := restrictSends D (A.send p.1 e st)
  out p e st := A.out p.1 e st

omit [DecidableEq M] in
theorem restrict_run (p : {p // p ∈ D}) (es : List (Option M)) (st : S × Option V) :
    (A.restrict D).run p es st = ((A.run p.1 es st).1, restrictSends D (A.run p.1 es st).2) := by
  induction es generalizing st with
  | nil => simp [run, restrictSends]
  | cons e es ih =>
    have happly : (A.restrict D).apply p e st = A.apply p.1 e st := rfl
    simp only [run, happly, ih]
    simp [restrictSends, restrict, Multiset.filterMap_add]

end KAlgorithm

/-- Lifting a message of the restricted system. -/
def liftMsg {D : Finset P} (m : Message {p // p ∈ D} M) : Message P M := ⟨m.dest.1, m.msg⟩

omit [DecidableEq P] [DecidableEq M] in
theorem liftMsg_injective {D : Finset P} : Function.Injective (liftMsg (M := M) (D := D)) := by
  rintro ⟨⟨a, ha⟩, x⟩ ⟨⟨b, hb⟩, y⟩ h
  simp only [liftMsg, Message.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

omit [DecidableEq M] in
theorem filter_map_wrap (D : Finset P) (ms : Multiset (P × M)) :
    (ms.map KAlgorithm.wrap).filter (fun m => m.dest ∈ D) =
      ((KAlgorithm.restrictSends D ms).map KAlgorithm.wrap).map liftMsg := by
  induction ms using Multiset.induction_on with
  | empty => simp [KAlgorithm.restrictSends]
  | cons qm ms ih =>
    by_cases h : qm.1 ∈ D
    · simp [KAlgorithm.restrictSends, h, KAlgorithm.wrap, liftMsg] at ih ⊢
      exact ih
    · simp [KAlgorithm.restrictSends, h, KAlgorithm.wrap] at ih ⊢
      exact ih

/-- The simulation relation: same local states on `D`, and the messages in flight to `D` are
exactly the lifted messages of the restricted system. -/
def Rel (D : Finset P) (t : State {p // p ∈ D} M (Loc M S V)) (s : State P M (Loc M S V)) :
    Prop :=
  (∀ p : {p // p ∈ D}, (s.proc p.1).state = (t.proc p).state) ∧
    s.msgs.filter (fun m => m.dest ∈ D) = t.msgs.map liftMsg

variable (A : KAlgorithm P M S V) (D : Finset P)

omit [DecidableEq M] in
theorem rel_start [Fintype P] (ιB : {p // p ∈ D} → Bool → V) (δB : V → Bool) (x : P → V)
    (inpB : {p // p ∈ D} → Bool) (inpA : P → Bool) (hinp : ∀ p : {p // p ∈ D}, inpA p.1 = inpB p) :
    Rel D (((A.restrict D).alg ιB δB).start inpB) ((A.algX x).start inpA) := by
  refine ⟨fun p => rfl, ?_⟩
  simp only [Algorithm.start, Multiset.filter_map, Multiset.map_map]
  rw [Finset.univ_eq_attach]
  have h1 : (Finset.univ : Finset P).val.filter ((fun m : Message P M => m.dest ∈ D) ∘
      (fun p => (⟨p, Sum.inl (inpA p)⟩ : Message P M))) = D.val := by
    show Multiset.filter (fun p => p ∈ D) _ = _
    exact congrArg Finset.val (Finset.filter_univ_mem D)
  rw [h1]
  conv_lhs => rw [← Multiset.attach_map_val D.val]
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl ?_
  intro p _
  simp [liftMsg, hinp ⟨p.1, p.2⟩]

omit [DecidableEq M] in
theorem nextLoc_restrict (ιB : {p // p ∈ D} → Bool → V) (ιA : P → Bool → V) (p : {p // p ∈ D})
    (msg : Bool ⊕ M) (l : Loc M S V) (hι : ∀ b, msg = Sum.inl b → ιB p b = ιA p.1 b) :
    (A.restrict D).nextLoc ιB p msg l = A.nextLoc ιA p.1 msg l := by
  rcases msg with b | c
  · rcases l with buf | st
    · simp only [KAlgorithm.nextLoc, KAlgorithm.restrict_run, hι b rfl]
      rfl
    · rfl
  · rcases l with buf | st
    · rfl
    · rfl

omit [DecidableEq M] in
theorem sendLoc_restrict (ιB : {p // p ∈ D} → Bool → V) (ιA : P → Bool → V) (p : {p // p ∈ D})
    (msg : Bool ⊕ M) (l : Loc M S V) (hι : ∀ b, msg = Sum.inl b → ιB p b = ιA p.1 b) :
    (A.restrict D).sendLoc ιB p msg l = KAlgorithm.restrictSends D (A.sendLoc ιA p.1 msg l) := by
  rcases msg with b | c
  · rcases l with buf | st
    · simp only [KAlgorithm.sendLoc, KAlgorithm.restrict_run, hι b rfl]
      rfl
    · simp [KAlgorithm.sendLoc, KAlgorithm.restrictSends]
  · rcases l with buf | st
    · simp [KAlgorithm.sendLoc, KAlgorithm.restrictSends]
    · rfl

theorem rel_step (ιB : {p // p ∈ D} → Bool → V) (δB : V → Bool) (x : P → V)
    (inpB : {p // p ∈ D} → Bool) (hx : ∀ p : {p // p ∈ D}, ιB p (inpB p) = x p.1)
    {t t' : State {p // p ∈ D} M (Loc M S V)} {s : State P M (Loc M S V)}
    (hg : GoodState inpB δB t) (hrel : Rel D t s) {m : Message {p // p ∈ D} M}
    (htr : ((A.restrict D).alg ιB δB).lts.Tr t (some m) t') :
    (A.algX x).lts.Tr s (some (liftMsg m)) ((A.algX x).recvMsg (liftMsg m) s) ∧
      Rel D t' ((A.algX x).recvMsg (liftMsg m) s) := by
  obtain ⟨hm, rfl⟩ := htr
  have hmem : liftMsg m ∈ s.msgs := by
    have : liftMsg m ∈ s.msgs.filter (fun m => m.dest ∈ D) := by
      rw [hrel.2]; exact Multiset.mem_map_of_mem _ hm
    exact Multiset.mem_of_mem_filter this
  have hι : ∀ b, m.msg = Sum.inl b → ιB m.dest b = (fun p _ => x p) m.dest.1 b := by
    intro b hb
    rw [hg.2 m hm b hb]
    exact hx m.dest
  have hst := hrel.1 m.dest
  refine ⟨⟨hmem, rfl⟩, ?_, ?_⟩
  · intro p
    simp only [Algorithm.recvMsg]
    by_cases hp : p = m.dest
    · subst hp
      simp only [liftMsg, ↓reduceIte]
      show A.nextLoc (fun p _ => x p) m.dest.1 m.msg (s.proc m.dest.1).state =
        (A.restrict D).nextLoc ιB m.dest m.msg (t.proc m.dest).state
      rw [nextLoc_restrict A D ιB (fun p _ => x p) _ _ _ hι, hst]
    · have hp' : p.1 ≠ m.dest.1 := fun h => hp (Subtype.ext h)
      simp only [liftMsg, hp, hp', ↓reduceIte]
      exact hrel.1 p
  · simp only [Algorithm.recvMsg, Multiset.filter_add, Multiset.map_add]
    congr 1
    · rw [multiset_filter_erase (fun m : Message P M => m.dest ∈ D) _ _
        (show (liftMsg m).dest ∈ D from m.dest.2), hrel.2,
        Multiset.map_erase _ liftMsg_injective]
    · show ((A.sendLoc _ _ _ _).map _).filter _ = (((A.restrict D).sendLoc _ _ _ _).map _).map _
      rw [sendLoc_restrict A D ιB (fun p _ => x p) _ _ _ hι, ← hst]
      exact filter_map_wrap D _

end KSetAgreement
