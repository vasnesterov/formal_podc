import Papers.PODC2026.ConsistentRefereeing.Defs
import Podc.SharedMemory.Potential

/-!
# Theorem 3: a linearizable contest object from a read/write register

Theorem 3 of Attiya, Castañeda, Enea, *Impossibility Results for Strong Linearizability: The
Difficulty of Consistent Refereeing* (PODC 2026): there is a wait-free (decisively) linearizable
contest implementation from reads and writes.

The algorithm: a register `X` (values `Option P`, initially `none` = `false`). A competitor
invoking `compete i` reads `X` and, if it reads `none`, writes `some i`; it returns `true`
(`ok`). The referee reads `X` and returns what it read (`winner`).

We prove wait-freedom and linearizability (`theorem3`) on all executions in which the referee
invokes at most one operation. That restriction is necessary (the contest object is one-shot):
if two competitors both read `none`, the first writes, the referee decides (returning the first
writer), and then the second competitor writes, a second `decide` returns the second writer,
which no sequential history allows. Competitors may invoke `compete` any number of times.

*Decisive* linearizability (prefix-monotonicity up to subsequences) is not defined in our
framework and is not proved.

The linearization is built along the execution, following the paper's proof:

* a `compete` that reads a non-`none` value is appended at its read;
* a `compete` that writes is linearized at its write: at the *front* of the linearization if no
  `decide` has been linearized yet, appended otherwise;
* a `decide` is appended at its read.

Invariant (`Inv`): as long as no `decide` is linearized, the abstract state (the first
competitor of the linearization) is the value of `X` (so the linearization is empty while
`X = none`), and a competitor about to write was not preceded by any linearized operation
(it read `none` before any linearized operation completed), which makes the insertion at the
front respect the real-time order.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

namespace Referee

open Function

variable {P : Type} [DecidableEq P]

/-- Local states of the read/write contest implementation. -/
inductive RWLoc (P : Type) where
  /-- No pending operation. -/
  | idle
  /-- `compete i`: about to read `X`. -/
  | cRead (i : P)
  /-- `compete i`: read `none`, about to write `some i`. -/
  | cWrite (i : P)
  /-- `compete`: about to return `ok`. -/
  | cDone
  /-- `decide`: about to read `X`. -/
  | dRead
  /-- `decide`: about to return `winner w`. -/
  | dDone (w : Option P)

/-- The implementation of Theorem 3, from one register `X : Option P` initialized to `none`. -/
def rwContest (ref : P) :
    Impl (contestObj P) (fun _ : Unit => register (Option P) none) P (RWLoc P) where
  memInit _ := none
  locInit _ := .idle
  invoke _ _ o := match o with
    | .compete i => .cRead i
    | .decide => .dRead
  act _ l := match l with
    | .idle => .ret .ok .idle
    | .cRead i => .access () .read (fun r => match r with
        | none => .cWrite i
        | some _ => .cDone)
    | .cWrite i => .access () (.write (some i)) (fun _ => .cDone)
    | .cDone => .ret .ok .idle
    | .dRead => .access () .read (fun r => .dDone r)
    | .dDone w => .ret (.winner w) .idle
  allowed p o := o = roleOp ref p

/-- Wait-freedom: every operation takes at most two steps. -/
theorem rwContest_waitFree (ref : P) : (rwContest ref).WaitFree := by
  refine (rwContest ref).waitFree_of_potential
    (fun _ l => match l with | .cRead _ => 2 | .cWrite _ => 1 | .dRead => 1 | _ => 0) ?_
  intro p l i o k hact x
  cases l with
  | idle => simp [rwContest] at hact
  | cDone => simp [rwContest] at hact
  | dDone w => simp [rwContest] at hact
  | cRead j =>
    simp only [rwContest, Action.access.injEq] at hact
    obtain ⟨-, -, hk⟩ := hact
    rw [← eq_of_heq hk]
    cases x <;> simp
  | cWrite j =>
    simp only [rwContest, Action.access.injEq] at hact
    obtain ⟨-, -, hk⟩ := hact
    rw [← eq_of_heq hk]
    simp
  | dRead =>
    simp only [rwContest, Action.access.injEq] at hact
    obtain ⟨-, -, hk⟩ := hact
    rw [← eq_of_heq hk]
    simp

namespace RW

/-! ### The invariant -/

/-- The current operation instance of `p`. -/
abbrev cur (α : List (Label P (contestObj P))) (p : P) : OpId P := (p, (respsOf α p).length)

/-- No `decide` has been linearized. -/
def AllCompete (Lin : List (OpId P × ContestOp P)) : Prop := ∀ y ∈ Lin, y.2 ≠ .decide

/-- Status of process `p`, by its local state. -/
def St (ref : P) (α : List (Label P (contestObj P)))
    (C : Config (contestObj P) (fun _ : Unit => register (Option P) none) P (RWLoc P))
    (Lin : List (OpId P × ContestOp P)) (p : P) : Prop :=
  match C.loc p with
  | .idle => C.pend p = none
  | .cRead i => C.pend p = some (.compete i) ∧ cur α p ∉ Lin.map Prod.fst ∧
      opOf α (cur α p) = some (.compete i)
  | .cWrite i => C.pend p = some (.compete i) ∧ cur α p ∉ Lin.map Prod.fst ∧
      opOf α (cur α p) = some (.compete i) ∧
      (AllCompete Lin → ∀ a ∈ Lin.map Prod.fst, ¬ Precedes α a (cur α p))
  | .cDone => C.pend p ≠ none ∧ ∃ i, (cur α p, .compete i) ∈ Lin
  | .dRead => C.pend p = some .decide ∧ cur α p ∉ Lin.map Prod.fst ∧
      opOf α (cur α p) = some .decide ∧ AllCompete Lin ∧ p = ref
  | .dDone w => C.pend p ≠ none ∧
      linResp (A := contestObj P) Lin (cur α p) = some (ContestResp.winner w)

/-- The invariant. -/
structure Inv (ref : P) (α : List (Label P (contestObj P)))
    (C : Config (contestObj P) (fun _ : Unit => register (Option P) none) P (RWLoc P))
    (Lin : List (OpId P × ContestOp P)) : Prop where
  lin : IsLinearization α Lin
  phase1 : AllCompete Lin → linState (A := contestObj P) Lin = C.mem ()
  st : ∀ p, St ref α C Lin p

/-! ### Auxiliary lemmas -/

lemma runOps_some (w : P) (os : List (ContestOp P)) :
    (contestObj P).runOps (some w) os = some w := by
  induction os with
  | nil => rfl
  | cons o os ih => cases o <;> simpa [ObjSpec.runOps] using ih

lemma linState_eq_none {Lin : List (OpId P × ContestOp P)} (h : AllCompete Lin)
    (h' : linState (A := contestObj P) Lin = none) : Lin = [] := by
  cases Lin with
  | nil => rfl
  | cons y Lin =>
    obtain ⟨x, o⟩ := y
    cases o with
    | decide => exact absurd rfl (h _ (List.mem_cons_self ..))
    | compete i =>
      simp only [linState, List.map_cons] at h'
      rw [ObjSpec.runOps_cons] at h'
      simp [runOps_some] at h'

/-- Linearized `compete`s respond `ok`. -/
lemma linRespFrom_compete {x : OpId P} (q : Option P) (Lin : List (OpId P × ContestOp P))
    (hx : x ∈ Lin.map Prod.fst) (hc : ∀ y ∈ Lin, y.1 = x → ∃ i, y.2 = .compete i) :
    linRespFrom (contestObj P) x q Lin = some ContestResp.ok := by
  induction Lin generalizing q with
  | nil => simp at hx
  | cons y Lin ih =>
    obtain ⟨y, o⟩ := y
    simp only [linRespFrom]
    split_ifs with h
    · obtain ⟨i, hi⟩ := hc (y, o) (by simp) h
      simp only at hi; subst hi; rfl
    · simp only [List.map_cons, List.mem_cons] at hx
      exact ih _ (hx.resolve_left (Ne.symm h)) (fun z hz => hc z (by simp [hz]))

lemma linResp_compete {α : List (Label P (contestObj P))} {Lin : List (OpId P × ContestOp P)}
    (hL : IsLinearization α Lin) {x : OpId P} {i : P} (hx : (x, .compete i) ∈ Lin) :
    linResp (A := contestObj P) Lin x = some ContestResp.ok := by
  apply linRespFrom_compete _ _ (List.mem_map.2 ⟨_, hx, rfl⟩)
  intro y hy hyx
  have h1 := hL.op_eq y hy
  have h2 := hL.op_eq _ hx
  rw [hyx] at h1
  rw [h1] at h2
  exact ⟨i, Option.some.inj h2⟩

/-- When no `decide` is linearized, every operation responds `ok`, from any state. -/
lemma linRespFrom_allCompete {x : OpId P} (q q' : Option P) (Lin : List (OpId P × ContestOp P))
    (h : AllCompete Lin) :
    linRespFrom (contestObj P) x q Lin = linRespFrom (contestObj P) x q' Lin := by
  induction Lin generalizing q q' with
  | nil => rfl
  | cons y Lin ih =>
    obtain ⟨y, o⟩ := y
    cases o with
    | decide => exact absurd rfl (h _ (List.mem_cons_self ..))
    | compete i =>
      simp only [linRespFrom]
      split_ifs
      · rfl
      · exact ih _ _ (fun z hz => h z (by simp [hz]))

lemma seqOK_allCompete {α : List (Label P (contestObj P))} (q q' : Option P)
    (Lin : List (OpId P × ContestOp P)) (h : AllCompete Lin) (hs : SeqOK α q Lin) :
    SeqOK α q' Lin := by
  induction Lin generalizing q q' with
  | nil => trivial
  | cons y Lin ih =>
    obtain ⟨y, o⟩ := y
    cases o with
    | decide => exact absurd rfl (h _ (List.mem_cons_self ..))
    | compete i =>
      simp only [SeqOK] at hs ⊢
      exact ⟨hs.1, ih _ _ (fun z hz => h z (by simp [hz])) hs.2⟩

/-- Inserting a pending operation at the front of a linearization (no linearized operation
precedes it). -/
lemma isLinearization_cons {α : List (Label P (contestObj P))}
    {Lin : List (OpId P × ContestOp P)} (hL : IsLinearization α Lin) {x : OpId P} {i : P}
    (hx : opOf α x = some (.compete i)) (hxL : x ∉ Lin.map Prod.fst) (hxc : ¬ Completed α x)
    (hrt : ∀ a ∈ Lin.map Prod.fst, ¬ Precedes α a x) (hall : AllCompete Lin) :
    IsLinearization α ((x, .compete i) :: Lin) where
  nodup := List.nodup_cons.2 ⟨hxL, hL.nodup⟩
  op_eq y hy := by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx
    · exact hL.op_eq y hy
  complete a ha := List.mem_cons_of_mem _ (hL.complete a ha)
  realtime a b hab hb := by
    simp only [List.map_cons, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact absurd hab (hrt a (hL.complete a hab.completed))
    · exact (hL.realtime a b hab hb).cons _
  seq := by
    simp only [SeqOK]
    refine ⟨fun r hr => absurd (completed_iff_respOf.2 (by rw [hr]; rfl)) hxc, ?_⟩
    exact seqOK_allCompete _ _ Lin hall hL.seq

lemma cur_append_of_ne (α : List (Label P (contestObj P))) (ℓ : Label P (contestObj P)) {q : P}
    (hq : ℓ.proc ≠ q) : cur (α ++ [ℓ]) q = cur α q := by
  simp [cur, respsOf_append, Label.retOf_eq_none_of_proc_ne hq]

lemma cur_append_tau (α : List (Label P (contestObj P))) (p q : P) :
    cur (α ++ [.tau p]) q = cur α q := by
  simp [cur, respsOf_append]

lemma invoked_of_opOf {α : List (Label P (contestObj P))} {x : OpId P} {o : ContestOp P}
    (h : opOf α x = some o) : Invoked α x := by
  simp only [opOf] at h; exact (List.getElem?_eq_some_iff.1 h).1

lemma not_completed_cur (α : List (Label P (contestObj P))) (p : P) :
    ¬ Completed α (cur α p) := by
  simp [Completed]

/-- Statuses of processes whose local state does not change are preserved, when the
linearization only grows by other pending operations and keeps the responses. -/
lemma St.transfer {ref : P} {α : List (Label P (contestObj P))} {ℓ : Label P (contestObj P)}
    {C C' : Config (contestObj P) (fun _ : Unit => register (Option P) none) P (RWLoc P)}
    {Lin Lin' : List (OpId P × ContestOp P)} {q : P} (h : St ref α C Lin q)
    (hloc : C'.loc q = C.loc q) (hpend : C'.pend q = C.pend q)
    (hcur : cur (α ++ [ℓ]) q = cur α q) (h1 : ∀ y ∈ Lin, y ∈ Lin')
    (h2 : ∀ x ∈ Lin'.map Prod.fst, x ∉ Lin.map Prod.fst → x ≠ cur α q ∧ ¬ Completed α x)
    (h3 : AllCompete Lin' → AllCompete Lin)
    (h4 : ∀ x ∈ Lin.map Prod.fst,
      linResp (A := contestObj P) Lin' x = linResp (A := contestObj P) Lin x)
    (h5 : q = ref → AllCompete Lin → AllCompete Lin') :
    St ref (α ++ [ℓ]) C' Lin' q := by
  have hnot : cur α q ∉ Lin.map Prod.fst → cur α q ∉ Lin'.map Prod.fst :=
    fun hn hm => (h2 _ hm hn).1 rfl
  unfold St at h ⊢
  rw [hloc, hpend, hcur]
  split at h
  · exact h
  · obtain ⟨a, b, c⟩ := h
    exact ⟨a, hnot b, by rw [opOf_append_of_invoked (invoked_of_opOf c)]; exact c⟩
  · obtain ⟨a, b, c, d⟩ := h
    refine ⟨a, hnot b, by rw [opOf_append_of_invoked (invoked_of_opOf c)]; exact c, ?_⟩
    intro hall x hx hpre
    have hpre' := hpre.of_append_of_invoked (invoked_of_opOf c)
    by_cases hxL : x ∈ Lin.map Prod.fst
    · exact d (h3 hall) x hxL hpre'
    · exact (h2 x hx hxL).2 hpre'.completed
  · obtain ⟨a, i, b⟩ := h
    exact ⟨a, i, h1 _ b⟩
  · obtain ⟨a, b, c, d, e⟩ := h
    exact ⟨a, hnot b, by rw [opOf_append_of_invoked (invoked_of_opOf c)]; exact c, h5 e d, e⟩
  · obtain ⟨a, b⟩ := h
    refine ⟨a, ?_⟩
    rw [h4 _ (linResp_isSome_iff.1 (by rw [b]; rfl))]; exact b

/-- In an execution, every process only invokes the operation of its role. -/
lemma role_of_runFrom {ref : P} {C C'} {α : List (Label P (contestObj P))}
    (h : (rwContest ref).runFrom C α = some C') {p : P} {o : ContestOp P}
    (ho : o ∈ opsOf α p) : o = roleOp ref p := by
  induction α generalizing C with
  | nil => simp at ho
  | cons ℓ α ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : (rwContest ref).step C ℓ with
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

lemma eq_ref_of_decide {ref p : P} (h : ContestOp.decide = roleOp ref p) : p = ref := by
  by_contra hp; simp [roleOp, hp] at h


/-! ### Preservation of the invariant -/

/-- Configurations of the read/write contest implementation. -/
abbrev Cfg (P : Type) :=
  Config (contestObj P) (fun _ : Unit => register (Option P) none) P (RWLoc P)

variable {ref : P}

lemma St.others {α : List (Label P (contestObj P))} {ℓ : Label P (contestObj P)} {C C' : Cfg P}
    {Lin Lin' : List (OpId P × ContestOp P)} {p : P} (hst : ∀ q, St ref α C Lin q)
    (hstep : (rwContest ref).step C ℓ = some C') (hp : ℓ.proc = p)
    (h1 : ∀ y ∈ Lin, y ∈ Lin')
    (h2 : ∀ x ∈ Lin'.map Prod.fst, x ∉ Lin.map Prod.fst → x.1 = p ∧ ¬ Completed α x)
    (h3 : AllCompete Lin' → AllCompete Lin)
    (h4 : ∀ x ∈ Lin.map Prod.fst,
      linResp (A := contestObj P) Lin' x = linResp (A := contestObj P) Lin x)
    (h5 : p ≠ ref → AllCompete Lin → AllCompete Lin') :
    ∀ q, q ≠ p → St ref (α ++ [ℓ]) C' Lin' q := by
  intro q hq
  have hpq : ℓ.proc ≠ q := hp ▸ Ne.symm hq
  obtain ⟨hl, hpd⟩ := Impl.step_other hstep hpq
  refine (hst q).transfer hl hpd (cur_append_of_ne α ℓ hpq) h1 (fun x hx hxL => ?_) h3 h4
    (fun hqr hall => h5 (hqr ▸ Ne.symm hq) hall)
  obtain ⟨a, b⟩ := h2 x hx hxL
  refine ⟨fun h => hq ?_, b⟩
  rw [h] at a; exact a

lemma St.others_same {α : List (Label P (contestObj P))} {ℓ : Label P (contestObj P)}
    {C C' : Cfg P} {Lin : List (OpId P × ContestOp P)} {p : P} (hst : ∀ q, St ref α C Lin q)
    (hstep : (rwContest ref).step C ℓ = some C') (hp : ℓ.proc = p) :
    ∀ q, q ≠ p → St ref (α ++ [ℓ]) C' Lin q :=
  St.others hst hstep hp (fun _ hy => hy) (fun _ hx hxL => absurd hx hxL) id (fun _ _ => rfl)
    (fun _ => id)

lemma St.others_append {α : List (Label P (contestObj P))} {ℓ : Label P (contestObj P)}
    {C C' : Cfg P} {Lin : List (OpId P × ContestOp P)} {p : P} {o : ContestOp P}
    (hst : ∀ q, St ref α C Lin q) (hstep : (rwContest ref).step C ℓ = some C')
    (hp : ℓ.proc = p) (ho : o = .decide → p = ref) :
    ∀ q, q ≠ p → St ref (α ++ [ℓ]) C' (Lin ++ [(cur α p, o)]) q := by
  refine St.others hst hstep hp (fun _ hy => List.mem_append_left _ hy) ?_ ?_ ?_ ?_
  · intro x hx hxL
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact absurd hx hxL
    · exact ⟨rfl, not_completed_cur α p⟩
  · exact fun h y hy => h y (List.mem_append_left _ hy)
  · exact fun x hx => linResp_append_of_mem _ hx
  · intro hpr hall y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hall y hy
    · simp only [List.mem_singleton] at hy; subst hy
      exact fun h => hpr (ho h)

lemma St.others_cons {α : List (Label P (contestObj P))} {ℓ : Label P (contestObj P)}
    {C C' : Cfg P} {Lin : List (OpId P × ContestOp P)} {p i : P}
    (hst : ∀ q, St ref α C Lin q) (hstep : (rwContest ref).step C ℓ = some C')
    (hp : ℓ.proc = p) (hall : AllCompete Lin) (hnot : cur α p ∉ Lin.map Prod.fst) :
    ∀ q, q ≠ p → St ref (α ++ [ℓ]) C' ((cur α p, .compete i) :: Lin) q := by
  refine St.others hst hstep hp (fun _ hy => List.mem_cons_of_mem _ hy) ?_ ?_ ?_ ?_
  · intro x hx hxL
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨rfl, not_completed_cur α p⟩
    · exact absurd hx hxL
  · exact fun h y hy => h y (List.mem_cons_of_mem _ hy)
  · intro x hx
    have hne : cur α p ≠ x := fun h => hnot (h ▸ hx)
    simp only [linResp, linRespFrom, hne, ↓reduceIte]
    exact linRespFrom_allCompete _ _ Lin hall
  · intro _ _ y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · simp
    · exact hall y hy


lemma linState_append {Lin : List (OpId P × ContestOp P)} (x : OpId P) (o : ContestOp P) :
    linState (A := contestObj P) (Lin ++ [(x, o)]) =
      ((contestObj P).δ (linState (A := contestObj P) Lin) o).1 := by
  simp [linState, ObjSpec.runOps]

lemma inv_step {α : List (Label P (contestObj P))} {C C' : Cfg P}
    {Lin : List (OpId P × ContestOp P)} {ℓ : Label P (contestObj P)}
    (hrun : (rwContest ref).run α = some C) (hI : Inv ref α C Lin)
    (hstep : (rwContest ref).step C ℓ = some C') (hone : (opsOf (α ++ [ℓ]) ref).length ≤ 1) :
    ∃ Lin', Inv ref (α ++ [ℓ]) C' Lin' := by
  cases ℓ with
  | inv p o =>
    obtain ⟨h0, hal, hpend, hloc, hmem⟩ := Impl.step_inv hstep
    have hal' : o = roleOp ref p := hal
    have hlen : (opsOf α p).length = (respsOf α p).length := by
      rcases (rwContest ref).run_counts hrun p with ⟨-, h1⟩ | ⟨h1, -⟩
      · exact h1
      · exact absurd h0 h1
    have hidle : C.loc p = .idle := by
      have h := hI.st p
      cases hl : C.loc p <;> first | rfl | simp [St, hl, h0] at h
    have hcurp : cur (α ++ [.inv p o]) p = cur α p := by simp [cur, respsOf_append]
    have hnotin : cur α p ∉ Lin.map Prod.fst := fun hm => by
      have := hI.lin.invoked_of_mem hm; simp [Invoked] at this; omega
    have hop : opOf (α ++ [.inv p o]) (cur α p) = some o := by
      simp [opOf, opsOf_append, ← hlen]
    refine ⟨Lin, hI.lin.append_inv p o, by rw [hmem]; exact hI.phase1, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq
      unfold St
      rw [hloc, hpend, hcurp]
      cases o with
      | compete i =>
        simp only [update_self, rwContest]
        exact ⟨by simp, hnotin, hop⟩
      | decide =>
        have hqr := eq_ref_of_decide hal'
        simp only [update_self, rwContest]
        refine ⟨by simp, hnotin, hop, ?_, hqr⟩
        intro y hy hyd
        have h1 := hI.lin.op_eq y hy
        rw [hyd] at h1
        have hm : ContestOp.decide ∈ opsOf α y.1.1 := by
          simp only [opOf] at h1; exact List.mem_of_getElem? h1
        have hr := eq_ref_of_decide (role_of_runFrom hrun hm)
        have hinv := invoked_of_opOf h1
        simp only [Invoked, hr] at hinv
        subst hqr
        have : (opsOf (α ++ [.inv q .decide]) q).length = (opsOf α q).length + 1 := by
          simp [opsOf_append]
        omega
    · exact St.others_same hI.st hstep rfl q hq
  | tau p =>
    obtain ⟨h0, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hstep
    have hst := hI.st p
    have hcurp : cur (α ++ [.tau p]) p = cur α p := cur_append_tau α p p
    cases hl : C.loc p with
    | idle => simp [rwContest, hl] at hact
    | cDone => simp [rwContest, hl] at hact
    | dDone w => simp [rwContest, hl] at hact
    | cRead j =>
      simp only [rwContest, hl, Action.access.injEq] at hact
      obtain ⟨-, ho, hk⟩ := hact
      have ho' := eq_of_heq ho; subst ho'
      have hk' := eq_of_heq hk; subst hk'
      simp only [St, hl] at hst
      obtain ⟨hp1, hp2, hp3⟩ := hst
      have hmem' : C'.mem = C.mem := by rw [hmem]; funext u; cases u; simp
      have hop : opOf (α ++ [.tau p]) (cur α p) = some (ContestOp.compete j) := by
        rw [opOf_append_of_invoked (invoked_of_opOf hp3)]; exact hp3
      cases hx : C.mem () with
      | none =>
        refine ⟨Lin, hI.lin.append_tau p, by rw [hmem']; exact hI.phase1, fun q => ?_⟩
        by_cases hq : q = p
        · subst hq
          unfold St
          rw [hloc, hpend, hcurp]
          simp only [update_self, hx]
          refine ⟨hp1, hp2, hop, ?_⟩
          intro hall a ha
          have := linState_eq_none hall (by rw [hI.phase1 hall, hx])
          subst this; simp at ha
        · exact St.others_same hI.st hstep rfl q hq
      | some w =>
        refine ⟨Lin ++ [(cur α p, ContestOp.compete j)],
          (hI.lin.push hp3 hp2 (not_completed_cur α p)).append_tau p, ?_, fun q => ?_⟩
        · intro hall
          have hall' : AllCompete Lin := fun y hy => hall y (List.mem_append_left _ hy)
          rw [hmem', linState_append, hI.phase1 hall', hx]
          rfl
        · by_cases hq : q = p
          · subst hq
            unfold St
            rw [hloc, hpend, hcurp]
            simp only [update_self, hx]
            exact ⟨h0, j, by simp⟩
          · exact St.others_append hI.st hstep rfl (by simp) q hq
    | cWrite j =>
      simp only [rwContest, hl, Action.access.injEq] at hact
      obtain ⟨-, ho, hk⟩ := hact
      have ho' := eq_of_heq ho; subst ho'
      have hk' := eq_of_heq hk; subst hk'
      simp only [St, hl] at hst
      obtain ⟨hp1, hp2, hp3, hp4⟩ := hst
      have hmem' : C'.mem () = some j := by rw [hmem]; simp
      by_cases hall : AllCompete Lin
      · refine ⟨(cur α p, ContestOp.compete j) :: Lin, (isLinearization_cons hI.lin hp3 hp2
          (not_completed_cur α p) (hp4 hall) hall).append_tau p, ?_, fun q => ?_⟩
        · intro _
          rw [hmem']
          show (contestObj P).runOps none (ContestOp.compete j :: Lin.map Prod.snd) = some j
          rw [ObjSpec.runOps_cons]
          exact runOps_some j _
        · by_cases hq : q = p
          · subst hq
            unfold St
            rw [hloc, hpend, hcurp]
            simp only [update_self]
            exact ⟨h0, j, by simp⟩
          · exact St.others_cons hI.st hstep rfl hall hp2 q hq
      · refine ⟨Lin ++ [(cur α p, ContestOp.compete j)],
          (hI.lin.push hp3 hp2 (not_completed_cur α p)).append_tau p,
          fun h => absurd (fun y hy => h y (List.mem_append_left _ hy)) hall, fun q => ?_⟩
        by_cases hq : q = p
        · subst hq
          unfold St
          rw [hloc, hpend, hcurp]
          simp only [update_self]
          exact ⟨h0, j, by simp⟩
        · exact St.others_append hI.st hstep rfl (by simp) q hq
    | dRead =>
      simp only [rwContest, hl, Action.access.injEq] at hact
      obtain ⟨-, ho, hk⟩ := hact
      have ho' := eq_of_heq ho; subst ho'
      have hk' := eq_of_heq hk; subst hk'
      simp only [St, hl] at hst
      obtain ⟨hp1, hp2, hp3, hall, hpr⟩ := hst
      have hmem' : C'.mem = C.mem := by rw [hmem]; funext u; cases u; simp
      refine ⟨Lin ++ [(cur α p, .decide)],
        (hI.lin.push hp3 hp2 (not_completed_cur α p)).append_tau p,
        fun h => absurd (h _ (List.mem_append_right _ (List.mem_singleton_self _))) (by simp),
        fun q => ?_⟩
      by_cases hq : q = p
      · subst hq
        unfold St
        rw [hloc, hpend, hcurp]
        simp only [update_self]
        refine ⟨h0, ?_⟩
        rw [linResp_append_singleton_self _ hp2, hI.phase1 hall]
      · exact St.others_append hI.st hstep rfl (fun _ => hpr) q hq
  | ret p r =>
    obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hstep
    have hst := hI.st p
    cases hl : C.loc p with
    | idle => simp only [St, hl] at hst; exact absurd hst h0
    | cRead j => simp [rwContest, hl] at hact
    | cWrite j => simp [rwContest, hl] at hact
    | dRead => simp [rwContest, hl] at hact
    | cDone =>
      simp only [rwContest, hl, Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      simp only [St, hl] at hst
      obtain ⟨-, i, hi⟩ := hst
      refine ⟨Lin, hI.lin.append_ret_of_linResp (linResp_compete hI.lin hi),
        by rw [hmem]; exact hI.phase1, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; unfold St; rw [hloc, hpend]; simp
      · exact St.others_same hI.st hstep rfl q hq
    | dDone w =>
      simp only [rwContest, hl, Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      simp only [St, hl] at hst
      refine ⟨Lin, hI.lin.append_ret_of_linResp hst.2,
        by rw [hmem]; exact hI.phase1, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; unfold St; rw [hloc, hpend]; simp
      · exact St.others_same hI.st hstep rfl q hq

/-- Every execution in which the referee invokes at most one operation satisfies the
invariant for some linearization. -/
theorem exists_inv (ref : P) (α : List (Label P (contestObj P))) :
    ∀ C, (rwContest ref).run α = some C → (opsOf α ref).length ≤ 1 → ∃ Lin, Inv ref α C Lin := by
  induction α using List.reverseRecOn with
  | nil =>
    intro C h _
    simp only [Impl.run_nil, Option.some.injEq] at h
    subst h
    exact ⟨[], isLinearization_nil, fun _ => rfl, fun p => by simp [St, rwContest, Impl.initCfg]⟩
  | append_singleton α ℓ ih =>
    intro C h hone
    rw [Impl.run, Impl.runFrom_append] at h
    cases hα : (rwContest ref).runFrom (rwContest ref).initCfg α with
    | none => simp [hα] at h
    | some C₀ =>
      simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
      have hone' : (opsOf α ref).length ≤ 1 := by
        rw [opsOf_append, List.length_append] at hone; omega
      obtain ⟨Lin, hI⟩ := ih C₀ hα hone'
      exact inv_step hα hI h hone

end RW

/-- **Theorem 3 of [ACE26].** For any set of processes and any referee `ref`, there is a
wait-free implementation of the contest object from a single read/write register that is
linearizable on every execution in which the referee invokes at most one operation (the
contest object is one-shot; competitors may invoke `compete` any number of times). Every process
may invoke exactly the operation of its role. (The paper also claims *decisive* linearizability,
which is not formalized.) -/
theorem theorem3 (ref : P) :
    ∃ (L : Type) (I : Impl (contestObj P) (fun _ : Unit => register (Option P) none) P L),
      (∀ p o, I.allowed p o ↔ o = roleOp ref p) ∧ I.WaitFree ∧
      ∀ α, I.Valid α → (opsOf α ref).length ≤ 1 → ∃ Lin, IsLinearization α Lin := by
  refine ⟨_, rwContest ref, fun _ _ => Iff.rfl, rwContest_waitFree ref, ?_⟩
  rintro α ⟨C, hC⟩ hone
  obtain ⟨Lin, hI⟩ := RW.exists_inv ref α C hC hone
  exact ⟨Lin, hI.lin⟩

end Referee

end Cslib.SharedMemory
