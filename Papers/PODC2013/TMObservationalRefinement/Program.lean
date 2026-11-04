import Papers.PODC2013.TMObservationalRefinement.Semantics

/-!
# Programs and their trace sets (Section 2, Figure 2, Section 5)

* `Cmd`: the commands of Section 2; `Cmd.Allowed`: the syntactic restrictions of Section 2
  (thread-local primitive commands, no global accesses and no nested atomic blocks inside atomic
  blocks, method calls only inside atomic blocks, no direct use of `assume`).
* `Tr t C τ`: `τ ∈ A(C)_t` (Figure 2).
* `InA P τ`: `τ ∈ A(P)` (prefixes of interleavings), `den P s` = `[[P]](s)`,
  `denH P s H` = `[[P]](s, H)`.
* `StateRef`, `TraceRef` (Definitions 14, 15), `OpacRel` (`H_C ⊑ H_A`), `IsTS`, `completeSub`.
* `prop_13_false`: Proposition 13 is false: `A(P)` contains traces that are not well-formed
  (Figure 2 lets a thread continue an atomic block after a method call was aborted).
* `wfTrace_of_inA`: the repair — traces of `A(P)` with a well-formed history are well-formed.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.TMObservationalRefinement

open IKind Act Lang CmdClass

/-- Commands (Section 2). -/
inductive Cmd (LV O M C BE IE : Type) where
  | prim (c : C)
  | seq (C₁ C₂ : Cmd LV O M C BE IE)
  | ite (b : BE) (C₁ C₂ : Cmd LV O M C BE IE)
  | while (b : BE) (C : Cmd LV O M C BE IE)
  | atomic (x : LV) (C : Cmd LV O M C BE IE)
  | call (x : LV) (o : O) (f : M) (e : IE)

variable {T LV GV O M BE IE C : Type} [Lang T LV GV BE IE C]

/-- **Figure 2**: `Tr t C τ` iff `τ ∈ A(C)_t`. -/
inductive Tr (t : T) : Cmd LV O M C BE IE → List (Act T O M C) → Prop
  | prim (c : C) : Tr t (.prim c) [.cmd t c]
  | seq {C₁ C₂ τ₁ τ₂} : Tr t C₁ τ₁ → Tr t C₂ τ₂ → Tr t (.seq C₁ C₂) (τ₁ ++ τ₂)
  | iteT {b C₁ C₂ τ} : Tr t C₁ τ → Tr t (.ite b C₁ C₂) (.cmd t (assume t b true) :: τ)
  | iteF {b C₁ C₂ τ} : Tr t C₂ τ → Tr t (.ite b C₁ C₂) (.cmd t (assume t b false) :: τ)
  | whileF {b C} : Tr t (.while b C) [.cmd t (assume t b false)]
  | whileT {b C τ τ'} : Tr t C τ → Tr t (.while b C) τ' →
      Tr t (.while b C) (.cmd t (assume t b true) :: (τ ++ τ'))
  | callRet {x o f e} (n n' : ℤ) : Tr t (.call x o f e)
      [.cmd t (assumeEq t e n), .iface t (.call o f n), .iface t (.ret n' o f), .cmd t (assign t x n')]
  | callAbort {x o f e} (n : ℤ) : Tr t (.call x o f e)
      [.cmd t (assumeEq t e n), .iface t (.call o f n), .iface t .aborted]
  | atomicAbort {x Cb τ} : Tr t Cb (τ ++ [.iface t .aborted]) →
      Tr t (.atomic x Cb) (.iface t .txbegin :: .iface t .ok :: (τ ++
        [.iface t .aborted, .cmd t (assign t x (vAb C))]))
  | atomicCommit {x Cb τ} : Tr t Cb τ → (∀ τ', τ ≠ τ' ++ [.iface t .aborted]) →
      Tr t (.atomic x Cb) (.iface t .txbegin :: .iface t .ok :: (τ ++
        [.iface t .txcommit, .iface t .committed, .cmd t (assign t x (vCom C))]))
  | atomicCommitAbort {x Cb τ} : Tr t Cb τ → (∀ τ', τ ≠ τ' ++ [.iface t .aborted]) →
      Tr t (.atomic x Cb) (.iface t .txbegin :: .iface t .ok :: (τ ++
        [.iface t .txcommit, .iface t .aborted, .cmd t (assign t x (vAb C))]))

/-- Programs `P = C₁ ‖ … ‖ C_m`: one command per thread. -/
abbrev Prog (T LV O M C BE IE : Type) := T → Cmd LV O M C BE IE

/-- `assume` commands (which programs may not use directly). -/
def IsAssume (c : C) : Prop :=
  ∃ t, (∃ b p, c = assume (T := T) (LV := LV) (GV := GV) t b p) ∨
    (∃ e n, c = assumeEq (T := T) (LV := LV) (GV := GV) (BE := BE) t e n)

/-- The syntactic restrictions of Section 2 for a command of thread `t`; `ins` says whether we are
inside an atomic block. -/
def Cmd.Allowed (t : T) : Bool → Cmd LV O M C BE IE → Prop
  | ins, .prim c => thr c = t ∧ (ins = true → glob c = false) ∧
      ¬ IsAssume (T := T) (LV := LV) (GV := GV) (BE := BE) (IE := IE) c
  | ins, .seq C₁ C₂ => C₁.Allowed t ins ∧ C₂.Allowed t ins
  | ins, .ite _ C₁ C₂ => C₁.Allowed t ins ∧ C₂.Allowed t ins
  | ins, .while _ C => C.Allowed t ins
  | ins, .atomic _ C => ins = false ∧ C.Allowed t true
  | ins, .call .. => ins = true

/-- A program of the language of Section 2. -/
def Prog.Allowed (P : Prog T LV O M C BE IE) : Prop := ∀ t, (P t).Allowed t false

variable [DecidableEq T]

/-- `τ ∈ A(P)`: a prefix of an interleaving of traces of the threads. -/
def InA (P : Prog T LV O M C BE IE) (τ : List (Act T O M C)) : Prop :=
  ∃ τ', τ <+: τ' ∧ ∀ t, Tr t (P t) (tproj t τ')

/-- `[[P]](s)` (equation (3)). -/
def den (P : Prog T LV O M C BE IE) (s : State T LV GV) : Set (List (Act T O M C)) :=
  {τ | InA P τ ∧ eval s τ ≠ ∅}

/-- `[[P]](s, H)` (equation (1)). -/
def denH (P : Prog T LV O M C BE IE) (s : State T LV GV) (H : Set (List (IAct T O M))) :
    Set (List (Act T O M C)) :=
  {τ | τ ∈ den P s ∧ history τ ∈ H}

/-- A transactional system: a prefix-closed set of (repaired) well-formed histories. -/
def IsTS (H : Set (List (IAct T O M))) : Prop :=
  (∀ h ∈ H, WellFormed h) ∧ ∀ h ∈ H, ∀ h', h' <+: h → h' ∈ H

/-- A transactional system with Definition 2 as printed. -/
def IsTSLit (H : Set (List (IAct T O M))) : Prop :=
  (∀ h ∈ H, WellFormedLit h) ∧ ∀ h ∈ H, ∀ h', h' <+: h → h' ∈ H

/-- `H|complete`. -/
def completeSub (H : Set (List (IAct T O M))) : Set (List (IAct T O M)) :=
  {h | h ∈ H ∧ Complete h}

/-- `H_C ⊑ H_A` (after Definition 4). -/
def OpacRel (HC HA : Set (List (IAct T O M))) : Prop := ∀ H ∈ HC, ∃ S ∈ HA, Opac H S

/-- **Definition 14**: observational refinement with respect to states. -/
def StateRef (O M : Type) (HC HA : Set (List (IAct T O M))) : Prop :=
  ∀ P : Prog T LV O M C BE IE, P.Allowed → ∀ (s : State T LV GV) τ, τ ∈ denH P s HC →
    ∃ τ' ∈ denH P s HA, eval s τ = eval s τ'

/-- **Definition 15**: observational refinement with respect to traces. -/
def TraceRef (O M : Type) (HC HA : Set (List (IAct T O M))) : Prop :=
  ∀ P : Prog T LV O M C BE IE, P.Allowed → ∀ (s : State T LV GV) τ, τ ∈ denH P s HC →
    ∃ τ' ∈ denH P s HA, ObsEq τ τ'

/-! ### Basic properties of `Tr` -/

lemma Tr.thread {t : T} {Cm : Cmd LV O M C BE IE} {τ : List (Act T O M C)} (h : Tr t Cm τ) :
    ∀ x ∈ τ, x.thread = t := by
  induction h with
  | prim => simp
  | seq _ _ ih₁ ih₂ => intro x hx; simp at hx; rcases hx with hx | hx; exacts [ih₁ x hx, ih₂ x hx]
  | iteT _ ih | iteF _ ih => intro x hx; simp at hx; rcases hx with rfl | hx; rfl; exact ih x hx
  | whileF => simp
  | whileT _ _ ih₁ ih₂ =>
    intro x hx; simp at hx; rcases hx with rfl | hx | hx; rfl; exacts [ih₁ x hx, ih₂ x hx]
  | callRet => intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> rfl
  | callAbort => intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> rfl
  | atomicAbort _ ih =>
    intro x hx; simp at hx
    rcases hx with rfl | rfl | hx | rfl | rfl
    · rfl
    · rfl
    · exact ih x (by simp [hx])
    · rfl
    · rfl
  | atomicCommit _ _ ih | atomicCommitAbort _ _ ih =>
    intro x hx; simp at hx
    rcases hx with rfl | rfl | hx | rfl | rfl | rfl <;> first | rfl | exact ih x hx

lemma split_append_cons {α : Type} {l₁ l₂ A B : List α} {x : α} (h : l₁ ++ l₂ = A ++ x :: B) :
    (∃ B', l₁ = A ++ x :: B' ∧ B = B' ++ l₂) ∨ (∃ A', A = l₁ ++ A' ∧ l₂ = A' ++ x :: B) := by
  rcases List.append_eq_append_iff.mp h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · exact Or.inr ⟨a', h1, h2⟩
  · rcases c' with _ | ⟨y, c'⟩
    · exact Or.inr ⟨[], by simp [h1], by simpa using h2.symm⟩
    · simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact Or.inl ⟨c', h1, rfl⟩

/-- Properties of the traces of allowed commands: commands are thread-local; inside atomic blocks
there are no global commands; outside, global commands are executed outside transactions and every
trace leaves the thread outside a transaction. -/
theorem Tr.props {t : T} {Cm : Cmd LV O M C BE IE} {τ : List (Act T O M C)} (h : Tr t Cm τ) :
    ∀ ins, Cm.Allowed t ins →
      (∀ c, Act.cmd t c ∈ τ → thr c = t) ∧
      (ins = true → ∀ c, Act.cmd t c ∈ τ → glob c = false) ∧
      (ins = false → ∀ st : T → Bool, st t = false → stAfter st τ t = false ∧
        ∀ τ₁ c τ₂, τ = τ₁ ++ Act.cmd t c :: τ₂ → glob c = true → stAfter st τ₁ t = false) := by
  induction h with
  | prim c =>
    intro ins hA
    obtain ⟨h1, h2, -⟩ := hA
    refine ⟨by simp [h1], by intro hi c' hc; simp at hc; subst hc; exact h2 hi, ?_⟩
    intro _ st hst
    refine ⟨by simpa [stAfter, upd] using hst, ?_⟩
    intro τ₁ c' τ₂ he _
    rcases τ₁ with _ | ⟨y, τ₁⟩
    · simpa using hst
    · simp at he
  | seq h₁ h₂ ih₁ ih₂ =>
    intro ins hA
    obtain ⟨a1, a2, a3⟩ := ih₁ ins hA.1
    obtain ⟨b1, b2, b3⟩ := ih₂ ins hA.2
    refine ⟨fun c hc => ?_, fun hi c hc => ?_, fun hi st hst => ?_⟩
    · simp at hc; rcases hc with hc | hc; exacts [a1 c hc, b1 c hc]
    · simp at hc; rcases hc with hc | hc; exacts [a2 hi c hc, b2 hi c hc]
    · obtain ⟨e1, e2⟩ := a3 hi st hst
      obtain ⟨f1, f2⟩ := b3 hi _ e1
      refine ⟨by rw [stAfter_append]; exact f1, fun τ₁ c τ₂ he hg => ?_⟩
      rcases split_append_cons he with ⟨B', rfl, -⟩ | ⟨A', rfl, h2⟩
      · exact e2 τ₁ c B' rfl hg
      · rw [stAfter_append]; exact f2 A' c τ₂ h2 hg
  | iteT _ ih | iteF _ ih =>
    intro ins hA
    obtain ⟨a1, a2, a3⟩ := ih ins (by first | exact hA.1 | exact hA.2)
    refine ⟨fun c hc => ?_, fun hi c hc => ?_, fun hi st hst => ?_⟩
    · simp at hc; rcases hc with rfl | hc; simp; exact a1 c hc
    · simp at hc; rcases hc with rfl | hc; simp; exact a2 hi c hc
    · obtain ⟨e1, e2⟩ := a3 hi st (by simpa [upd] using hst)
      refine ⟨by simpa [stAfter, upd] using e1, fun τ₁ c τ₂ he hg => ?_⟩
      rcases τ₁ with _ | ⟨y, τ₁⟩
      · simp at he; obtain ⟨rfl, -⟩ := he; simp at hg
      · simp at he; obtain ⟨rfl, he⟩ := he
        simpa [stAfter, upd] using e2 τ₁ c τ₂ he hg
  | whileF =>
    intro ins hA
    refine ⟨by simp, by simp, fun _ st hst => ⟨by simpa [stAfter, upd] using hst, ?_⟩⟩
    intro τ₁ c τ₂ he hg
    rcases τ₁ with _ | ⟨y, τ₁⟩
    · simp at he; obtain ⟨rfl, -⟩ := he; simp at hg
    · simp at he
  | @whileT b Cb τa τb h₁ h₂ ih₁ ih₂ =>
    intro ins hA
    obtain ⟨a1, a2, a3⟩ := ih₁ ins hA
    obtain ⟨b1, b2, b3⟩ := ih₂ ins hA
    refine ⟨fun c hc => ?_, fun hi c hc => ?_, fun hi st hst => ?_⟩
    · simp at hc; rcases hc with rfl | hc | hc; simp; exacts [a1 c hc, b1 c hc]
    · simp at hc; rcases hc with rfl | hc | hc; simp; exacts [a2 hi c hc, b2 hi c hc]
    · have hst' : upd st (Act.cmd t (assume t b true) : Act T O M C) t = false := by
        simpa [upd] using hst
      obtain ⟨e1, e2⟩ := a3 hi _ hst'
      obtain ⟨f1, f2⟩ := b3 hi _ e1
      refine ⟨by simp only [stAfter_cons, stAfter_append]; exact f1, fun τ₁ c τ₂ he hg => ?_⟩
      rcases τ₁ with _ | ⟨y, τ₁⟩
      · simp at he; obtain ⟨rfl, -⟩ := he; simp at hg
      · simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, he⟩ := he
        simp only [stAfter_cons]
        rcases split_append_cons he with ⟨B', rfl, -⟩ | ⟨A', rfl, h2⟩
        · exact e2 τ₁ c B' rfl hg
        · rw [stAfter_append]; exact f2 A' c τ₂ h2 hg
  | callRet n n' =>
    intro ins hA
    refine ⟨?_, ?_, fun hi => by simp [Cmd.Allowed] at hA; simp_all⟩
    · intro c hc; simp at hc; rcases hc with rfl | rfl <;> simp
    · intro _ c hc; simp at hc; rcases hc with rfl | rfl <;> simp
  | callAbort n =>
    intro ins hA
    refine ⟨?_, ?_, fun hi => by simp [Cmd.Allowed] at hA; simp_all⟩
    · intro c hc; simp at hc; subst hc; simp
    · intro _ c hc; simp at hc; subst hc; simp
  | atomicAbort h ih | atomicCommit h _ ih | atomicCommitAbort h _ ih =>
    intro ins hA
    obtain ⟨hins, hA⟩ := hA
    obtain ⟨a1, a2, -⟩ := ih true hA
    refine ⟨fun c hc => ?_, fun hi => by simp_all, fun _ st hst => ⟨?_, ?_⟩⟩
    · simp at hc
      first
      | (rcases hc with hc | rfl; exact a1 c (by simp [hc]); simp)
      | (rcases hc with hc | rfl; exact a1 c hc; simp)
    · simp [stAfter_append, upd]
    · intro τ₁ c τ₂ he hg
      exfalso
      have hc : Act.cmd t c ∈ τ₁ ++ Act.cmd t c :: τ₂ := by simp
      rw [← he] at hc
      simp at hc
      first
      | (rcases hc with hc | rfl
         · simp [a2 rfl c (by simp [hc])] at hg
         · simp at hg)
      | (rcases hc with hc | rfl
         · simp [a2 rfl c hc] at hg
         · simp at hg)

/-- **Repair of Proposition 13**: a trace of an allowed program whose history is well-formed is a
well-formed trace (repaired Definition 12). -/
theorem wfTrace_of_inA {P : Prog T LV O M C BE IE} (hP : P.Allowed) {τ : List (Act T O M C)}
    (hτ : InA P τ) (hh : WellFormed (history τ)) : WFTrace τ := by
  obtain ⟨τ', ⟨r, rfl⟩, htr⟩ := hτ
  refine ⟨hh, fun t c hc => ?_, fun τ₁ t c τ₂ he hg => ?_⟩
  · have hm : Act.cmd t c ∈ tproj t (τ ++ r) := by simp [tproj, hc]
    exact ((htr t).props false (hP t)).1 c hm
  · have e : tproj t (τ ++ r) = tproj t τ₁ ++ Act.cmd t c :: (tproj t τ₂ ++ tproj t r) := by
      rw [he]; simp [tproj]
    obtain ⟨-, -, h3⟩ := (htr t).props false (hP t)
    have := (h3 rfl (fun _ => false) rfl).2 _ c _ e hg
    rw [openIn_iff _ _ (fun a ha => by simp [tproj] at ha; exact ha.2)]
    simp [this]

/-! ### Building traces of `A(P)` -/

lemma tproj_flatMap (u : T) (L : List T) (hL : L.Nodup) (e : T → List (Act T O M C))
    (he : ∀ v, ∀ x ∈ e v, x.thread = v) :
    tproj u (L.flatMap e) = if u ∈ L then e u else [] := by
  induction L with
  | nil => simp [tproj]
  | cons v L ih =>
    rw [List.nodup_cons] at hL
    simp only [List.flatMap_cons, tproj_append, ih hL.2, List.mem_cons]
    by_cases hv : v = u
    · subst hv
      simp only [hL.1, ite_false, List.append_nil, true_or, ite_true]
      exact List.filter_eq_self.mpr (fun x hx => by simp [he _ x hx])
    · have : tproj u (e v) = [] := List.filter_eq_nil_iff.mpr (fun x hx => by
        simp [he _ x hx, hv])
      rw [this, List.nil_append]
      by_cases hu : u ∈ L <;> simp [hu, Ne.symm hv]

variable [Fintype T]

/-- A trace is in `A(P)` if every thread's projection extends to a trace of its command. -/
theorem inA_of_ext (P : Prog T LV O M C BE IE) (τ : List (Act T O M C))
    (h : ∀ u, ∃ ext, Tr u (P u) (tproj u τ ++ ext)) : InA P τ := by
  choose e he using h
  have hthr : ∀ v, ∀ x ∈ e v, x.thread = v :=
    fun v x hx => (he v).thread x (by simp [hx])
  refine ⟨τ ++ (Finset.univ.toList).flatMap e, ⟨_, rfl⟩, fun u => ?_⟩
  rw [tproj_append, tproj_flatMap u _ (Finset.nodup_toList _) e hthr]
  simpa using he u

/-! ### Proposition 13 is false -/

/-- **Proposition 13 is false**: with the trace sets of Figure 2, `A(P)` contains traces that are
not well-formed (even for Definition 12 as printed). In `x := atomic { y := o.f(1); y := o.f(1) }`,
Figure 2 allows the first call to abort and the block to go on with the second call: the trace
`txbegin OK assume call aborted assume call` is in `A(P)`, but its history has a `call` after the
transaction aborted. -/
theorem prop_13_false (t : T) (o : O) (f : M) (x y : LV) :
    ¬ ∀ P : Prog T LV O M C BE IE, P.Allowed → ∀ τ, InA P τ → WFTraceLit τ := by
  intro hall
  let body : Cmd LV O M C BE IE := .seq (.call y o f (cst C 1)) (.call y o f (cst C 1))
  let P : Prog T LV O M C BE IE := fun _ => .atomic x body
  have hP : P.Allowed := fun u => by simp [P, body, Cmd.Allowed]
  have hbody : ∀ u, Tr u body ([.cmd u (assumeEq u (cst C 1) 1), .iface u (.call o f 1),
      .iface u .aborted] ++ [.cmd u (assumeEq u (cst C 1) 1), .iface u (.call o f 1),
      .iface u (.ret 0 o f), .cmd u (assign u y 0)]) := fun u =>
    Tr.seq (Tr.callAbort 1) (Tr.callRet 1 0)
  let τ : List (Act T O M C) := [.iface t .txbegin, .iface t .ok, .cmd t (assumeEq t (cst C 1) 1),
    .iface t (.call o f 1), .iface t .aborted, .cmd t (assumeEq t (cst C 1) 1),
    .iface t (.call o f 1)]
  have hτ : InA P τ := by
    apply inA_of_ext
    intro u
    have hfull := Tr.atomicCommit (x := x) (hbody u) (by
      intro τ' h
      have := congrArg List.getLast? h
      simp at this)
    by_cases hu : u = t
    · subst hu
      refine ⟨[.iface u (.ret 0 o f), .cmd u (assign u y 0), .iface u .txcommit, .iface u .committed,
        .cmd u (assign u x (vCom C))], ?_⟩
      simpa [τ, tproj] using hfull
    · exact ⟨_, by simpa [τ, tproj, List.filter_cons, Ne.symm hu] using hfull⟩
  have hw := (hall P hP τ hτ).1 t
  have hpr : proj t (history τ) = [txbegin, ok, .call o f 1, aborted, .call o f 1] := by
    simp [τ, history, proj, Act.toI, List.filterMap_cons]
  rw [hpr] at hw
  have := hw.2.2 [txbegin, ok, .call o f 1, aborted] (.call o f 1) [] (by simp) (by simp [isCallRet])
  have e : ([txbegin, ok, .call o f 1, aborted] : List (IKind O M)) =
      [txbegin, ok, .call o f 1] ++ [aborted] := rfl
  rw [e, inTx_concat] at this
  simp [isCtl] at this

end Podc.TMObservationalRefinement
