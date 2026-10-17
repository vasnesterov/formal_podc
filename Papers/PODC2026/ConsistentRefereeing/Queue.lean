import Papers.PODC2026.ConsistentRefereeing.Defs

/-!
# Proposition 11: a contest object from a strongly linearizable queue

Proposition 11 of Attiya, Castañeda, Enea, *Impossibility Results for Strong Linearizability:
The Difficulty of Consistent Refereeing* (PODC 2026): a lock-free strongly linearizable queue
can implement a wait-free strongly linearizable contest object.

Given a queue implementation `Q : Impl (queueObj V) B P L` and an injective encoding
`e : P → V` of process identifiers, `contestOfQueue Q ref e` is the contest implementation
running directly on `Q`'s base objects with `Q`'s local states (the composition is flattened):
a competitor `p` runs `Q`'s code for `enq (e p)` and returns `true` (`ok`), the referee runs
`Q`'s code for `deq` and returns the decoded dequeued value (`false` = `winner none` if the
queue is empty).

The paper's proof says "due to strong linearizability, we can assume that the queue is atomic";
we do the composition argument concretely:

* every execution of the contest implementation translates label by label into an execution of
  `Q` (`trFrom`): invocations `compete p ↦ enq (e p)`, `decide ↦ deq`, internal steps unchanged,
  and a response is replaced by the queue response that `Q`'s program returns at that point
  (read off the current configuration, `trLbl`), with matching configurations
  (`runFrom_trFrom`);
* a linearization of the translated execution translates back (`isLinearization_back`): the
  contest state is simulated by the queue state as long as the referee has not dequeued (the
  winner is the decoded head of the queue). This needs the referee to invoke `decide` at most
  once (the contest object is one-shot): with two `decide`s the second `deq` would return the
  second enqueued value.

Results (`proposition11`): the contest implementation is lock-free (on all executions), wait-free
on the one-shot executions `Adm ref` (lock-freedom of `Q` and the one-shot discipline bound the
number of operations), and strongly linearizable on executions in which the referee invokes at
most one operation (in particular on `Adm ref`).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

namespace Referee

open Function

variable {V P ι L : Type} {B : ι → ObjSpec}

section Defs

variable [DecidableEq P]

namespace QueueContest

/-- The queue operation run for a contest operation. -/
def toQOp (e : P → V) : ContestOp P → FifoOp V
  | .compete i => .enq (e i)
  | .decide => .deq

/-- Decoding a queue value into a process identifier (`none` if it encodes no process). -/
noncomputable def decode (e : P → V) (v : V) : Option P := by
  classical exact if h : ∃ p, e p = v then some h.choose else none

lemma decode_apply {e : P → V} (he : Injective e) (p : P) : decode e (e p) = some p := by
  have h : ∃ q, e q = e p := ⟨p, rfl⟩
  unfold decode
  split_ifs
  exact congrArg some (he (Exists.choose_spec h))

/-- The contest response returned by process `p` when its queue operation returns `r`. -/
noncomputable def toCResp (ref : P) (e : P → V) (p : P) (r : Option V) : ContestResp P :=
  if p = ref then .winner (r.bind (decode e)) else .ok

/-- The contest action corresponding to an action of the queue implementation. -/
noncomputable def toCAct (ref : P) (e : P → V) (p : P) :
    Action (queueObj V) B L → Action (contestObj P) B L
  | .access i o k => .access i o k
  | .ret r l => .ret (toCResp ref e p r) l

end QueueContest

open QueueContest

/-- **The contest implementation of Proposition 11**, built from the queue implementation `Q`:
competitor `p` enqueues `e p`, the referee dequeues and returns the decoded value. -/
noncomputable def contestOfQueue (Q : Impl (queueObj V) B P L) (ref : P) (e : P → V) :
    Impl (contestObj P) B P L where
  memInit := Q.memInit
  locInit := Q.locInit
  invoke p l o := Q.invoke p l (toQOp e o)
  act p l := toCAct ref e p (Q.act p l)
  allowed p o := o = roleOp ref p

namespace QueueContest

/-- Translation of configurations: pending contest operations become queue operations. -/
def trCfg (e : P → V) (C : Config (contestObj P) B P L) : Config (queueObj V) B P L :=
  ⟨C.loc, fun p => (C.pend p).map (toQOp e), C.mem⟩

/-- Translation of a label at configuration `C`: a response is replaced by the response of the
queue implementation's next action. -/
def trLbl (Q : Impl (queueObj V) B P L) (e : P → V) (C : Config (contestObj P) B P L) :
    Label P (contestObj P) → Label P (queueObj V)
  | .inv p o => .inv p (toQOp e o)
  | .tau p => .tau p
  | .ret p _ => match Q.act p (C.loc p) with
    | .ret r _ => .ret p r
    | .access _ _ _ => .ret p none

end QueueContest

end Defs

open QueueContest

variable [DecidableEq P] [DecidableEq ι] (Q : Impl (queueObj V) B P L) (ref : P) (e : P → V)

namespace QueueContest

/-- Translation of an execution from configuration `C`, label by label. -/
noncomputable def trFrom : Config (contestObj P) B P L → List (Label P (contestObj P)) →
    List (Label P (queueObj V))
  | _, [] => []
  | C, ℓ :: α => trLbl Q e C ℓ :: trFrom (((contestOfQueue Q ref e).step C ℓ).getD C) α

/-- Translation of an execution (from the initial configuration). -/
noncomputable def trExec (α : List (Label P (contestObj P))) : List (Label P (queueObj V)) :=
  trFrom Q ref e (contestOfQueue Q ref e).initCfg α

lemma toCAct_eq_access {a : Action (queueObj V) B L} {i : ι} {o : (B i).Op}
    {k : (B i).Resp → L} {p : P} (h : toCAct ref e p a = .access i o k) : a = .access i o k := by
  cases a with
  | access i' o' k' => simpa [toCAct] using h
  | ret r l => simp [toCAct] at h

lemma toCAct_eq_ret {a : Action (queueObj V) B L} {r : ContestResp P} {l : L} {p : P}
    (h : toCAct ref e p a = .ret r l) : ∃ r', a = .ret r' l ∧ r = toCResp ref e p r' := by
  cases a with
  | access i' o' k' => simp [toCAct] at h
  | ret r' l' =>
    simp only [toCAct, Action.ret.injEq] at h
    exact ⟨r', by rw [h.2], h.1.symm⟩

lemma map_update_pend (f : P → Option (ContestOp P)) (p : P) (x : Option (ContestOp P)) :
    (fun q => (update f p x q).map (toQOp e)) = update (fun q => (f q).map (toQOp e)) p
      (x.map (toQOp e)) := by
  funext q; by_cases hq : q = p
  · subst hq; simp
  · simp [update_of_ne hq]

variable {Q ref e}

/-- One step of the contest implementation is one step of the queue implementation on the
translated configurations. -/
lemma step_tr (hallow : ∀ p, Q.allowed p (toQOp e (roleOp ref p)))
    {C C' : Config (contestObj P) B P L} {ℓ : Label P (contestObj P)}
    (h : (contestOfQueue Q ref e).step C ℓ = some C') :
    Q.step (trCfg e C) (trLbl Q e C ℓ) = some (trCfg e C') := by
  obtain ⟨loc', pend', mem'⟩ := C'
  cases ℓ with
  | inv p o =>
    obtain ⟨h0, hal, hpend, hloc, hmem⟩ := Impl.step_inv h
    have hal' : Q.allowed p (toQOp e o) := by
      have : o = roleOp ref p := hal
      subst this; exact hallow p
    simp only at hpend hloc hmem
    subst hpend hloc hmem
    simp [Impl.step, trCfg, trLbl, h0, hal', contestOfQueue, map_update_pend]
  | tau p =>
    obtain ⟨h0, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
    simp only at hpend hloc hmem
    subst hpend hloc hmem
    have hact' := toCAct_eq_access ref e hact
    have h0' : (trCfg e C).pend p ≠ none := by simpa [trCfg] using h0
    simp only [Impl.step, trLbl, h0', ↓reduceIte]
    simp only [trCfg] at hact' ⊢
    rw [hact']
  | ret p r =>
    obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
    simp only at hpend hloc hmem
    subst hpend hloc hmem
    obtain ⟨r', hact', -⟩ := toCAct_eq_ret ref e hact
    have h0' : (trCfg e C).pend p ≠ none := by simpa [trCfg] using h0
    simp only [Impl.step, trLbl, hact']
    simp only [trCfg] at h0' hact' ⊢
    simp [h0', hact', map_update_pend]

/-! ### Translated executions -/

/-- A translated execution runs on the translated configurations. -/
lemma runFrom_trFrom (hallow : ∀ p, Q.allowed p (toQOp e (roleOp ref p)))
    {C C' : Config (contestObj P) B P L} {α : List (Label P (contestObj P))}
    (h : (contestOfQueue Q ref e).runFrom C α = some C') :
    Q.runFrom (trCfg e C) (trFrom Q ref e C α) = some (trCfg e C') := by
  induction α generalizing C with
  | nil => simp only [Impl.runFrom_nil, Option.some.injEq] at h; subst h; rfl
  | cons ℓ α ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : (contestOfQueue Q ref e).step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      simp only [trFrom, hs, Option.getD_some, Impl.runFrom_cons, step_tr hallow hs,
        Option.bind_some]
      exact ih h

lemma run_trExec (hallow : ∀ p, Q.allowed p (toQOp e (roleOp ref p)))
    {C : Config (contestObj P) B P L} {α : List (Label P (contestObj P))}
    (h : (contestOfQueue Q ref e).run α = some C) :
    Q.run (trExec Q ref e α) = some (trCfg e C) :=
  runFrom_trFrom hallow h

lemma valid_trExec (hallow : ∀ p, Q.allowed p (toQOp e (roleOp ref p)))
    {α : List (Label P (contestObj P))} (h : (contestOfQueue Q ref e).Valid α) :
    Q.Valid (trExec Q ref e α) := by
  obtain ⟨C, hC⟩ := h; exact ⟨_, run_trExec hallow hC⟩

lemma trFrom_prefix (C : Config (contestObj P) B P L) (α β : List (Label P (contestObj P))) :
    trFrom Q ref e C α <+: trFrom Q ref e C (α ++ β) := by
  induction α generalizing C with
  | nil => exact List.nil_prefix
  | cons ℓ α ih =>
    simp only [List.cons_append, trFrom]
    exact List.cons_prefix_cons.2 ⟨rfl, ih _⟩

lemma trExec_prefix {α β : List (Label P (contestObj P))} (h : α <+: β) :
    trExec Q ref e α <+: trExec Q ref e β := by
  obtain ⟨γ, rfl⟩ := h; exact trFrom_prefix _ _ _

lemma opsOf_trFrom (C : Config (contestObj P) B P L) (α : List (Label P (contestObj P)))
    (p : P) : opsOf (trFrom Q ref e C α) p = (opsOf α p).map (toQOp e) := by
  induction α generalizing C with
  | nil => rfl
  | cons ℓ α ih =>
    simp only [trFrom, opsOf_cons, ih, List.map_append]
    congr 1
    cases ℓ with
    | inv q o => by_cases hq : q = p <;> simp [trLbl, hq]
    | tau q => simp [trLbl]
    | ret q r => simp only [trLbl]; split <;> simp

lemma respsOf_trFrom {C C' : Config (contestObj P) B P L} {α : List (Label P (contestObj P))}
    (h : (contestOfQueue Q ref e).runFrom C α = some C') (p : P) :
    respsOf α p = (respsOf (trFrom Q ref e C α) p).map (toCResp ref e p) := by
  induction α generalizing C with
  | nil => rfl
  | cons ℓ α ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : (contestOfQueue Q ref e).step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      simp only [trFrom, hs, Option.getD_some, respsOf_cons, ih h, List.map_append]
      congr 1
      cases ℓ with
      | inv q o => simp [trLbl]
      | tau q => simp [trLbl]
      | ret q r =>
        obtain ⟨-, -, -, l, hact, -⟩ := Impl.step_ret hs
        obtain ⟨r', hact', hr⟩ := toCAct_eq_ret ref e hact
        simp only [trLbl, hact']
        by_cases hq : q = p
        · subst hq; simp [hr]
        · simp [hq]

lemma opOf_trExec (α : List (Label P (contestObj P))) (x : OpId P) :
    opOf (trExec Q ref e α) x = (opOf α x).map (toQOp e) := by
  simp [opOf, trExec, opsOf_trFrom]

lemma invoked_trExec_iff (α : List (Label P (contestObj P))) (x : OpId P) :
    Invoked (trExec Q ref e α) x ↔ Invoked α x := by
  simp [Invoked, trExec, opsOf_trFrom]

lemma respOf_trExec {α : List (Label P (contestObj P))} (h : (contestOfQueue Q ref e).Valid α)
    (x : OpId P) : respOf α x = (respOf (trExec Q ref e α) x).map (toCResp ref e x.1) := by
  obtain ⟨C, hC⟩ := h
  simp [respOf, trExec, respsOf_trFrom hC x.1]

lemma completed_trExec_iff {α : List (Label P (contestObj P))}
    (h : (contestOfQueue Q ref e).Valid α) (x : OpId P) :
    Completed (trExec Q ref e α) x ↔ Completed α x := by
  obtain ⟨C, hC⟩ := h
  simp [Completed, trExec, respsOf_trFrom hC x.1]

lemma precedes_trExec {α : List (Label P (contestObj P))} (h : (contestOfQueue Q ref e).Valid α)
    {a b : OpId P} (hab : Precedes α a b) : Precedes (trExec Q ref e α) a b := by
  obtain ⟨β, γ, rfl, h1, h2⟩ := hab
  obtain ⟨δ, hδ⟩ := trExec_prefix (Q := Q) (ref := ref) (e := e) (List.prefix_append β γ)
  exact ⟨_, δ, hδ.symm, (completed_trExec_iff h.of_append a).2 h1,
    fun h' => h2 ((invoked_trExec_iff β b).1 h')⟩

/-- In an execution of the contest implementation, every process only invokes the operation of
its role. -/
lemma role_of_runFrom {C C' : Config (contestObj P) B P L} {α : List (Label P (contestObj P))}
    (h : (contestOfQueue Q ref e).runFrom C α = some C') {p : P} {o : ContestOp P}
    (ho : o ∈ opsOf α p) : o = roleOp ref p := by
  induction α generalizing C with
  | nil => simp at ho
  | cons ℓ α ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : (contestOfQueue Q ref e).step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      simp only [opsOf_cons, List.mem_append] at ho
      rcases ho with ho | ho
      · cases ℓ with
        | inv q o' =>
          by_cases hq : q = p
          · subst hq
            simp only [Label.invOf_inv, ite_true, Option.toList_some, List.mem_singleton] at ho
            subst ho
            exact (Impl.step_inv hs).2.1
          · simp [hq] at ho
        | tau q => simp at ho
        | ret q r => simp at ho
      · exact ih h ho

/-! ### Linearizations translate back -/

/-- Translating a queue linearization back: every operation of `p` is `roleOp ref p`. -/
def back (ref : P) (M : List (OpId P × FifoOp V)) : List (OpId P × ContestOp P) :=
  M.map (fun y => (y.1, roleOp ref y.1.1))

lemma map_fst_back (M : List (OpId P × FifoOp V)) :
    (back ref M).map Prod.fst = M.map Prod.fst := by
  simp [back, Function.comp_def]

/-- The simulation of the contest state by the queue state, along a sequential history: as long
as the referee's `deq` has not been linearized, the contest state is the decoded head of the
queue. -/
lemma seqOK_back (he : Injective e) {α : List (Label P (contestObj P))}
    {β : List (Label P (queueObj V))}
    (hresp : ∀ x r, respOf α x = some r → ∃ r', respOf β x = some r' ∧ r = toCResp ref e x.1 r') :
    ∀ (M : List (OpId P × FifoOp V)) (q : List V) (s : Option P),
      (∀ y ∈ M, y.2 = toQOp e (roleOp ref y.1.1)) → (M.map Prod.fst).Nodup →
      (∀ y ∈ M, y.1.1 = ref → y.1.2 = 0) →
      (ref ∈ M.map (fun y => y.1.1) → s = q.head?.bind (decode e) ∧ ∀ v ∈ q, ∃ p, e p = v) →
      SeqOK β q M → SeqOK α s (back ref M) := by
  intro M
  induction M with
  | nil => intros; trivial
  | cons y M ih =>
    obtain ⟨x, o⟩ := y
    intro q s hop hnd hz hH hseq
    simp only [SeqOK] at hseq
    obtain ⟨hr, hseq'⟩ := hseq
    have ho : o = toQOp e (roleOp ref x.1) := hop (x, o) (by simp)
    subst ho
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hop' : ∀ y ∈ M, y.2 = toQOp e (roleOp ref y.1.1) := fun y hy => hop y (by simp [hy])
    have hz' : ∀ y ∈ M, y.1.1 = ref → y.1.2 = 0 := fun y hy => hz y (by simp [hy])
    simp only [back, List.map_cons, SeqOK]
    by_cases hx : x.1 = ref
    · have hxr : roleOp ref x.1 = .decide := by rw [hx]; simp [roleOp]
      rw [hxr] at hr hseq' ⊢
      obtain ⟨hs, -⟩ := hH (by simp [hx])
      refine ⟨fun r hr' => ?_, ih _ s hop' hnd.2 hz' ?_ hseq'⟩
      · obtain ⟨r', h1, h2⟩ := hresp x r hr'
        have h3 := hr r' h1
        subst h2
        simp only [toQOp] at h3
        simp [toCResp, hx, ← h3, hs]
      · intro hm
        obtain ⟨y, hy, hyr⟩ := List.mem_map.1 hm
        have hx0 := hz (x, toQOp e (roleOp ref x.1)) (by simp) hx
        have hy0 := hz' y hy hyr
        have hyx : y.1 = x := Prod.ext (by simp [hyr, hx]) (by simp at hx0; simp [hy0, hx0])
        exact absurd (List.mem_map.2 ⟨y, hy, hyx⟩) hnd.1
    · have hxr : roleOp ref x.1 = .compete x.1 := by simp [roleOp, hx]
      rw [hxr] at hr hseq' ⊢
      refine ⟨fun r hr' => ?_, ih _ _ hop' hnd.2 hz' ?_ hseq'⟩
      · obtain ⟨r', -, h2⟩ := hresp x r hr'
        simp [h2, toCResp, hx]
      · intro hm
        obtain ⟨hs, hq⟩ := hH (List.mem_cons_of_mem _ hm)
        simp only [toQOp]
        refine ⟨?_, ?_⟩
        · cases q with
          | nil => simp [hs, decode_apply he]
          | cons v q =>
            obtain ⟨p, rfl⟩ := hq v (by simp)
            simp [hs, decode_apply he]
        · intro v hv
          simp only [List.mem_append, List.mem_singleton] at hv
          rcases hv with hv | rfl
          · exact hq v hv
          · exact ⟨x.1, rfl⟩

/-- A linearization of the translated execution translates back to a linearization of the
contest execution, provided the referee invokes at most one operation. -/
lemma isLinearization_back (he : Injective e) {α : List (Label P (contestObj P))}
    (hv : (contestOfQueue Q ref e).Valid α) (hone : (opsOf α ref).length ≤ 1)
    {M : List (OpId P × FifoOp V)} (hM : IsLinearization (trExec Q ref e α) M) :
    IsLinearization α (back ref M) := by
  obtain ⟨C, hC⟩ := hv
  have hv : (contestOfQueue Q ref e).Valid α := ⟨C, hC⟩
  have hop : ∀ y ∈ M, opOf α y.1 = some (roleOp ref y.1.1) ∧ y.2 = toQOp e (roleOp ref y.1.1) := by
    intro y hy
    have h1 := hM.op_eq y hy
    rw [opOf_trExec] at h1
    obtain ⟨o, ho, ho'⟩ := Option.map_eq_some_iff.1 h1
    have hrole : o = roleOp ref y.1.1 := by
      apply role_of_runFrom hC
      simp only [opOf] at ho
      exact List.mem_of_getElem? ho
    subst hrole
    exact ⟨ho, ho'.symm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [map_fst_back]; exact hM.nodup
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    exact (hop z hz).1
  · intro a ha
    rw [map_fst_back]; exact hM.complete a ((completed_trExec_iff hv a).2 ha)
  · intro a b hab hb
    rw [map_fst_back] at hb ⊢
    exact hM.realtime a b (precedes_trExec hv hab) hb
  · refine seqOK_back he (β := trExec Q ref e α) ?_ M [] none (fun y hy => (hop y hy).2)
      hM.nodup ?_ (fun _ => ⟨rfl, by simp⟩) hM.seq
    · intro x r hr
      rw [respOf_trExec hv] at hr
      obtain ⟨r', h1, h2⟩ := Option.map_eq_some_iff.1 hr
      exact ⟨r', h1, h2.symm⟩
    · intro y hy hyr
      have := hM.invoked_of_mem (List.mem_map.2 ⟨y, hy, rfl⟩)
      rw [invoked_trExec_iff] at this
      simp only [Invoked, hyr] at this
      omega

/-! ### Proposition 11 -/

lemma hallow_of (henq : ∀ p, p ≠ ref → Q.allowed p (.enq (e p))) (hdeq : Q.allowed ref .deq) :
    ∀ p, Q.allowed p (toQOp e (roleOp ref p)) := by
  intro p
  by_cases hp : p = ref
  · subst hp; simpa [roleOp, toQOp] using hdeq
  · simpa [roleOp, toQOp, hp] using henq p hp

end QueueContest

variable {Q ref e}

/-- The contest implementation is strongly linearizable on the executions in which the referee
invokes at most one operation (the contest object is one-shot). -/
theorem contestOfQueue_strongLinOn (he : Injective e)
    (hallow : ∀ p, Q.allowed p (toQOp e (roleOp ref p))) (hsl : Q.StronglyLinearizable) :
    (contestOfQueue Q ref e).StrongLinOn (fun α => (opsOf α ref).length ≤ 1) := by
  obtain ⟨f, hf, hpre⟩ := hsl
  refine ⟨fun α => back ref (f (trExec Q ref e α)),
    fun α hα hone => isLinearization_back he hα hone (hf _ (valid_trExec hallow hα)), ?_⟩
  intro α β hβ _ hαβ
  exact (hpre _ _ (valid_trExec hallow hβ) (trExec_prefix hαβ)).map _

namespace QueueContest

/-- An infinite execution of the contest implementation translates to one of the queue
implementation. -/
noncomputable def trInf (hallow : ∀ p, Q.allowed p (toQOp e (roleOp ref p)))
    (ex : (contestOfQueue Q ref e).InfExec) : Q.InfExec where
  cfg n := trCfg e (ex.cfg n)
  lbl n := trLbl Q e (ex.cfg n) (ex.lbl n)
  cfg_zero := by rw [ex.cfg_zero]; rfl
  step_eq n := step_tr hallow (ex.step_eq n)

lemma trLbl_isStep {C : Config (contestObj P) B P L} {ℓ : Label P (contestObj P)}
    (h : ℓ.IsStep) : (trLbl Q e C ℓ).IsStep := by
  cases ℓ with
  | inv p o => exact h.elim
  | tau p => trivial
  | ret p r => simp only [trLbl]; split <;> trivial

lemma eq_ret_of_trLbl {C : Config (contestObj P) B P L} {ℓ : Label P (contestObj P)} {p : P}
    {r : Option V} (h : trLbl Q e C ℓ = .ret p r) : ∃ r', ℓ = .ret p r' := by
  cases ℓ with
  | inv q o => simp [trLbl] at h
  | tau q => simp [trLbl] at h
  | ret q r' =>
    simp only [trLbl] at h
    split at h <;> (simp only [Label.ret.injEq] at h; exact ⟨r', by rw [h.1]⟩)

end QueueContest

/-- The contest implementation is lock-free (on all executions). -/
theorem contestOfQueue_lockFree (hallow : ∀ p, Q.allowed p (toQOp e (roleOp ref p)))
    (hlf : Q.LockFree) : (contestOfQueue Q ref e).LockFree := by
  intro ex hs N
  obtain ⟨m, hm, p, r, h⟩ := hlf (trInf hallow ex) (fun N => by
    obtain ⟨m, hm, h⟩ := hs N; exact ⟨m, hm, trLbl_isStep h⟩) N
  obtain ⟨r', h'⟩ := eq_ret_of_trLbl h
  exact ⟨m, hm, p, r', h'⟩

/-- The contest implementation is wait-free on one-shot executions: by lock-freedom of the queue,
infinitely many steps would give infinitely many responses, but in a one-shot execution every
process returns at most once. -/
theorem contestOfQueue_waitFreeOn [Fintype P] (hallow : ∀ p, Q.allowed p (toQOp e (roleOp ref p)))
    (hlf : Q.LockFree) : (contestOfQueue Q ref e).WaitFreeOn (Adm ref) := by
  classical
  intro ex hE p n _
  by_contra hcon
  push Not at hcon
  have hrets := contestOfQueue_lockFree hallow hlf ex (fun N => by
    obtain ⟨m, hm, h⟩ := hcon N; exact ⟨m, hm, by rw [h]; trivial⟩)
  obtain ⟨q, hq⟩ : ∃ q, ∀ N, ∃ m ≥ N, ∃ r, ex.lbl m = .ret q r := by
    by_contra hno
    push Not at hno
    choose Nf hNf using hno
    obtain ⟨m, hm, q, r, h⟩ := hrets (Finset.univ.sup Nf)
    exact hNf q m (le_trans (Finset.le_sup (Finset.mem_univ _)) hm) r h
  obtain ⟨m₁, -, r₁, h₁⟩ := hq 0
  obtain ⟨m₂, hm₂, r₂, h₂⟩ := hq (m₁ + 1)
  have hlen : 2 ≤ (respsOf (ex.lbls (m₂ + 1)) q).length := by
    obtain ⟨γ, hγ⟩ := ex.lbls_prefix hm₂
    rw [Impl.InfExec.lbls_succ, respsOf_append, ← hγ, respsOf_append, Impl.InfExec.lbls_succ,
      respsOf_append, h₁, h₂]
    simp; omega
  have h1 := (hE (m₂ + 1)).oneShot q
  rcases (contestOfQueue Q ref e).run_counts (ex.run_lbls (m₂ + 1)) q with ⟨-, h2⟩ | ⟨-, h2⟩ <;>
    omega

/-- **Proposition 11 of [ACE26].** A lock-free strongly linearizable queue implementation `Q`
(in which competitors may enqueue their (injectively encoded) identifiers and the referee may
dequeue) yields a contest implementation from the same base objects that is lock-free,
wait-free and strongly linearizable on the one-shot executions `Adm ref` considered in the
paper. (Strong linearizability holds as soon as the referee invokes at most one operation,
`contestOfQueue_strongLinOn`; it fails in general if the referee may `decide` twice.) -/
theorem proposition11 [Fintype P] (he : Injective e)
    (henq : ∀ p, p ≠ ref → Q.allowed p (.enq (e p))) (hdeq : Q.allowed ref .deq)
    (hlf : Q.LockFree) (hsl : Q.StronglyLinearizable) :
    (∀ p, (contestOfQueue Q ref e).allowed p (roleOp ref p)) ∧
    (contestOfQueue Q ref e).LockFree ∧ (contestOfQueue Q ref e).WaitFreeOn (Adm ref) ∧
    (contestOfQueue Q ref e).StrongLinOn (Adm ref) := by
  have hallow := hallow_of henq hdeq
  exact ⟨fun _ => rfl, contestOfQueue_lockFree hallow hlf, contestOfQueue_waitFreeOn hallow hlf,
    (contestOfQueue_strongLinOn he hallow hsl).mono (fun α h => h.oneShot ref)⟩

end Referee

end Cslib.SharedMemory
