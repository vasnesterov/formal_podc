import Papers.PODC2012.OptimismConcurrency.ImplModel

/-!
# The class `SM`: (safe-)strict serializability, and Theorem 6 (σ₀ of Figure 1)

Gramoli, Kuznetsov, Ravi, *Optimism for Boosting Concurrency* (arXiv 1203.4751v8), §3 (Figure 1),
§4 ("The class SM") and Appendix C.1 (Theorem 6 = part 1 of Theorem 2).

In a TM-based implementation every high-level operation runs as a transaction; we identify a
transaction with a high-level operation `(p, x, k)` (the `k`-th operation of `p` on `x`), its
events being `H|π` (`txEvents`). A transaction is *committed* if it returned a response, *aborted*
if a read or write returned `⊥`, and *commit-pending* ("started committing") if all its reads and
writes are done, the code `LL` has nothing left to do but `return`, and no response was given.

* `cseq H C` — the members of `Cseq(H)`: the subsequence of `H` of the events of the committed
  transactions (exactly `complete H`) and of the commit-pending transactions selected by `C`.
* `Legal S` — a sequential execution `S` (a concatenation of transactions) is legal: every read
  returns the latest value written before it, starting from the empty list `head → tail` (`mem0`).
* `StrictSer H`, `SafeStrictSer H` — the paper's definitions (§4, Appendix C.1).
* `sigma0` — the schedule `σ₀` of Figure 1; `sigma0_lsl`: it is `(LL, set)`-LSL.
* `theorem_6_loophole` — an honest, LSL, safe-strict serializable history exporting `σ₀` (with a
  stalled commit-pending `remove(2)`): Theorem 6 is false for the paper's definitions as stated.
* `theorem_6_appendix` — the repair: with the definition of Appendix C.1 (`cseq` = complete
  operations only), a strictly serializable history whose committed operations follow `LL` does
  not export `σ₀` (the paper's proof); `theorem_6_quiescent` — the same for the §4 definition when
  every transaction committed or aborted.
-/

namespace Podc.OptimismConcurrency

open Cslib.SharedMemory

/-! ## Transactions of a two-level history -/

section General

variable {P X Op Res Obj Val : Type} [DecidableEq P] [DecidableEq X]

/-- A transaction (= a high-level operation): its process, its object and its index among the
operations of the process on the object. -/
abbrev TxId (P X : Type) := P × X × ℕ

/-- The events of the transaction `t` in `H` (`H|π`; contains the aborted access, if any). -/
def txEvents (H : Hist P X Op Res Obj Val) (t : TxId P X) : Hist P X Op Res Obj Val :=
  (splitOps (restrictPX H t.1 t.2.1)).getD t.2.2 []

/-- `t` is a transaction of `H` (it performed at least one event: its invocation). -/
def IsTxn (H : Hist P X Op Res Obj Val) (t : TxId P X) : Prop := t.2.2 < numOps H t.1 t.2.1

/-- `t` is committed: it returned a response. -/
def Committed (H : Hist P X Op Res Obj Val) (t : TxId P X) : Prop :=
  ∃ e ∈ txEvents H t, e.isRes = true

/-- `t` is aborted: one of its reads or writes returned `⊥`. -/
def Aborted (H : Hist P X Op Res Obj Val) (t : TxId P X) : Prop :=
  ∃ e ∈ txEvents H t, e.isAbort = true

/-- `t` is complete: committed or aborted. -/
def TxComplete (H : Hist P X Op Res Obj Val) (t : TxId P X) : Prop :=
  ∃ e ∈ txEvents H t, e.isTerm = true

/-- `t` is incomplete (live): invoked, neither committed nor aborted. -/
def Incomplete (H : Hist P X Op Res Obj Val) (t : TxId P X) : Prop :=
  IsTxn H t ∧ ¬ TxComplete H t

instance (H : Hist P X Op Res Obj Val) (t : TxId P X) : Decidable (IsTxn H t) :=
  inferInstanceAs (Decidable (_ < _))
instance (H : Hist P X Op Res Obj Val) (t : TxId P X) : Decidable (Committed H t) :=
  inferInstanceAs (Decidable (∃ e ∈ _, _))
instance (H : Hist P X Op Res Obj Val) (t : TxId P X) : Decidable (Aborted H t) :=
  inferInstanceAs (Decidable (∃ e ∈ _, _))
instance (H : Hist P X Op Res Obj Val) (t : TxId P X) : Decidable (TxComplete H t) :=
  inferInstanceAs (Decidable (∃ e ∈ _, _))
instance (H : Hist P X Op Res Obj Val) (t : TxId P X) : Decidable (Incomplete H t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Process, object and "is a high-level invocation" of an event. -/
def Ev.skel (e : Ev P X Op Res Obj Val) : P × X × Bool := (e.proc, e.obj, e.isInv)

/-- Transaction of each position, computed from the skeletons of the events; `c p x` counts the
invocations of `p` on `x` so far. -/
def txOfSkel (c : P → X → ℕ) : List (P × X × Bool) → List (Option (TxId P X))
  | [] => []
  | (p, x, b) :: l =>
    let k := if b then c p x + 1 else c p x
    (if k = 0 then none else some (p, x, k - 1)) ::
      txOfSkel (fun p' x' => if p' = p ∧ x' = x then k else c p' x') l

/-- `txList H` lists, for every position of `H`, the transaction its event belongs to (`none`
for an event of a process before its first invocation). -/
def txList (H : Hist P X Op Res Obj Val) : List (Option (TxId P X)) :=
  txOfSkel (fun _ _ => 0) (H.map Ev.skel)

/-- **Real-time order** `t →_H t'`: `t` is complete and its last event precedes the first event
of `t'` (there is a cut of `H` with all events of `t` before it and all events of `t'` after
it). -/
def Precedes (H : Hist P X Op Res Obj Val) (t t' : TxId P X) : Prop :=
  TxComplete H t ∧ ∃ n, some t ∉ (txList H).drop n ∧ some t' ∉ (txList H).take n

lemma precedes_iff_bounded (H : Hist P X Op Res Obj Val) (t t' : TxId P X) :
    Precedes H t t' ↔ TxComplete H t ∧
      ∃ n < (txList H).length + 1, some t ∉ (txList H).drop n ∧ some t' ∉ (txList H).take n := by
  refine and_congr_right fun _ => ⟨fun ⟨n, h1, h2⟩ => ?_, fun ⟨n, _, h⟩ => ⟨n, h⟩⟩
  by_cases hn : n < (txList H).length + 1
  · exact ⟨n, hn, h1, h2⟩
  · refine ⟨(txList H).length, by omega, by simp, ?_⟩
    rw [List.take_of_length_le (by omega)] at h2
    rwa [List.take_length]

instance (H : Hist P X Op Res Obj Val) (t t' : TxId P X) : Decidable (Precedes H t t') :=
  decidable_of_iff _ (precedes_iff_bounded H t t').symm

/-- Is the event at the head of the position list in a transaction selected by `C`? -/
def headSel (C : TxId P X → Bool) : List (Option (TxId P X)) → Bool
  | some t :: _ => C t
  | _ => false

/-- Auxiliary for `cseq`: walk along `H` and its list of transactions. -/
def cseqAux (C : TxId P X → Bool) :
    List (Option (TxId P X)) → Hist P X Op Res Obj Val → Hist P X Op Res Obj Val
  | _, [] => []
  | ts, e :: l =>
    if keepC e l || headSel C ts then e :: cseqAux C ts.tail l else cseqAux C ts.tail l

/-- **`Cseq(H)`** (§4): the subsequence of `H` that consists of all the events of the committed
transactions (i.e. `complete H`) and of the transactions selected by `C` (to be applied with `C`
selecting only commit-pending transactions). -/
def cseq (H : Hist P X Op Res Obj Val) (C : TxId P X → Bool) : Hist P X Op Res Obj Val :=
  cseqAux C (txList H) H

lemma cseqAux_false (ts : List (Option (TxId P X))) (H : Hist P X Op Res Obj Val) :
    cseqAux (fun _ => false) ts H = lookFilter keepC H := by
  induction H generalizing ts with
  | nil => rfl
  | cons e l ih =>
    have : headSel (fun _ : TxId P X => false) ts = false := by
      rcases ts with _ | ⟨_ | _, _⟩ <;> rfl
    simp only [cseqAux, lookFilter, this, Bool.or_false, ih]

/-- Selecting no commit-pending transaction, `Cseq(H)` is `complete(H)`. -/
lemma cseq_false (H : Hist P X Op Res Obj Val) : cseq H (fun _ => false) = complete H :=
  cseqAux_false _ _

/-- `n` is the length of `H_k`, the prefix of `H` up to the last event of `t`. -/
def PrefixUpTo (H : Hist P X Op Res Obj Val) (t : TxId P X) (n : ℕ) : Prop :=
  0 < n ∧ (txList H)[n - 1]? = some (some t) ∧ some t ∉ (txList H).drop n

instance (H : Hist P X Op Res Obj Val) (t : TxId P X) (n : ℕ) : Decidable (PrefixUpTo H t n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end General

/-! ## Legal sequential executions of `(LL, set)` -/

section Legal

variable {P : Type} [DecidableEq P]

/-- One event of a sequential execution: a read must return the current content of the
location; a write takes effect at its (successful) response; `⊥` responses are illegal (aborted
accesses are not part of the sequential execution). Configuration: memory and pending access. -/
def legStep (c : Mem × Option Pend) : LEv P → Option (Mem × Option Pend)
  | .rinv _ _ y => if c.2 = none then some (c.1, some (.rd y)) else none
  | .rres _ _ v => match c.2 with
    | some (.rd y) => if v.isSome ∧ v = c.1 y then some (c.1, none) else none
    | _ => none
  | .winv _ _ y n => if c.2 = none then some (c.1, some (.wr y n)) else none
  | .wres _ _ ok => match c.2 with
    | some (.wr y n) => if ok then some (Function.update c.1 y (some n), none) else none
    | _ => none
  | _ => some c

/-- Run `legStep` along a sequential execution. -/
def legRun (c : Mem × Option Pend) : LHist P → Option (Mem × Option Pend)
  | [] => some c
  | e :: l => (legStep c e).bind (fun c' => legRun c' l)

/-- A sequential execution is **legal**: every read returns the latest value written before it
(the initial memory is the empty list `head → tail`). -/
def Legal (S : LHist P) : Prop := (legRun (mem0, none) S).isSome

instance (S : LHist P) : Decidable (Legal S) :=
  inferInstanceAs (Decidable ((legRun (mem0, none) S).isSome = true))

omit [DecidableEq P] in
lemma legRun_append (c : Mem × Option Pend) (l₁ l₂ : LHist P) :
    legRun c (l₁ ++ l₂) = (legRun c l₁).bind (fun c' => legRun c' l₂) := by
  induction l₁ generalizing c with
  | nil => simp [legRun]
  | cons e l ih =>
    simp only [List.cons_append, legRun]
    cases legStep c e <;> simp [ih]

end Legal

/-! ## Commit-pending transactions, strict and safe-strict serializability -/

section SM

variable {P : Type} [DecidableEq P]

/-- `t` is **commit-pending** ("started committing", §4): it is incomplete, all its reads and
writes returned, and the only thing left to do for `LL` is to return. -/
def CommitPending (H : LHist P) (t : TxId P Unit) : Prop :=
  Incomplete H t ∧
    ∃ o s r, (txEvents H t).foldl cstep CSt.idle = .run o s ∧ act o s = .ret r

/-- `ord` is a legal sequential execution of all transactions of `σ`, each with its events in
`σ` (so it is equivalent to `σ`), that respects the real-time order of `σ`. -/
def SerialWitness (σ : LHist P) (ord : List (TxId P Unit)) : Prop :=
  ord.Nodup ∧ (∀ t, t ∈ ord ↔ IsTxn σ t) ∧ Legal (ord.flatMap (txEvents σ)) ∧
    ∀ t t', t ∈ ord → t' ∈ ord → Precedes σ t t' → ord.idxOf t < ord.idxOf t'

/-- **Strict serializability** (§4): some `σ ∈ Cseq(H)` (all committed transactions and some
commit-pending ones) is equivalent to a legal sequential execution respecting `→_σ`. -/
def StrictSer (H : LHist P) : Prop :=
  ∃ C : TxId P Unit → Bool, (∀ t, C t = true → CommitPending H t) ∧
    ∃ ord, SerialWitness (cseq H C) ord

/-- **Safe-strict serializability** (§4): `H` is strictly serializable and every transaction
`π_k` that is incomplete or aborted is consistent with a legal sequential execution
`π₀ ⋯ πᵢ · π_k` where `π₀, …, πᵢ` are transactions of some `σ ∈ Cseq(H_k)` (`H_k` = prefix of `H`
up to the last event of `π_k`), with their events in `σ`, and `π_k` with its events in `H_k`
(without its aborted access). -/
def SafeStrictSer (H : LHist P) : Prop :=
  StrictSer H ∧ ∀ t, IsTxn H t → (Incomplete H t ∨ Aborted H t) →
    ∃ n, PrefixUpTo H t n ∧ ∃ C : TxId P Unit → Bool,
      (∀ u, C u = true → CommitPending (H.take n) u) ∧
      ∃ pre : List (TxId P Unit), pre.Nodup ∧ (∀ u ∈ pre, IsTxn (cseq (H.take n) C) u) ∧
        Legal (pre.flatMap (txEvents (cseq (H.take n) C)) ++ dropAbort (txEvents (H.take n) t))

/-- Every transaction committed or aborted (no live and no commit-pending transaction). -/
def Quiescent (H : LHist P) : Prop := ∀ t, IsTxn H t → TxComplete H t

end SM

/-! ## The schedule `σ₀` of Figure 1 -/

/-- `contains(5)` by process `1`, first part: reads `h`, `X₁ = ⟨1, X₃⟩`, `X₃ = ⟨3, X₄⟩`. -/
def con5a : LHist ℕ :=
  [.inv 1 () (.contains 5)] ++ rd 1 headL ⟨.ninf, Xl 1⟩ ++ rd 1 (Xl 1) ⟨.fin 1, Xl 3⟩ ++
    rd 1 (Xl 3) ⟨.fin 3, Xl 4⟩

/-- `insert(2)` by process `2`: reads `h`, `X₁`, `X₃`, allocates `X₂ := ⟨2, X₃⟩`, writes
`X₁ := ⟨1, X₂⟩`, returns `true`. -/
def ins2 : LHist ℕ :=
  [.inv 2 () (.insert 2)] ++ rd 2 headL ⟨.ninf, Xl 1⟩ ++ rd 2 (Xl 1) ⟨.fin 1, Xl 3⟩ ++
    rd 2 (Xl 3) ⟨.fin 3, Xl 4⟩ ++ wr 2 (Xl 2) ⟨.fin 2, Xl 3⟩ ++ wr 2 (Xl 1) ⟨.fin 1, Xl 2⟩ ++
    [.res 2 () true]

/-- `insert(5)` by process `3`: reads `h`, `X₁`, `X₂`, `X₃`, `X₄`, `tail`, allocates
`X₅ := ⟨5, tail⟩`, writes `X₄ := ⟨4, X₅⟩`, returns `true`. -/
def ins5 : LHist ℕ :=
  [.inv 3 () (.insert 5)] ++ rd 3 headL ⟨.ninf, Xl 1⟩ ++ rd 3 (Xl 1) ⟨.fin 1, Xl 2⟩ ++
    rd 3 (Xl 2) ⟨.fin 2, Xl 3⟩ ++ rd 3 (Xl 3) ⟨.fin 3, Xl 4⟩ ++ rd 3 (Xl 4) ⟨.fin 4, tailL⟩ ++
    rd 3 tailL ⟨.pinf, tailL⟩ ++ wr 3 (Xl 5) ⟨.fin 5, tailL⟩ ++ wr 3 (Xl 4) ⟨.fin 4, Xl 5⟩ ++
    [.res 3 () true]

/-- `contains(5)`, second part: reads `X₄ = ⟨4, X₅⟩`, `X₅`, returns `true`. -/
def con5b : LHist ℕ :=
  rd 1 (Xl 4) ⟨.fin 4, Xl 5⟩ ++ rd 1 (Xl 5) ⟨.fin 5, tailL⟩ ++ [.res 1 () true]

/-- A history of Figure 1: process `0` builds `{1, 3, 4}`; then `contains(5)` (process `1`) runs
concurrently first with `insert(2)` (process `2`), then with `insert(5)` (process `3`). -/
def hist0 : LHist ℕ := pre134 ++ con5a ++ ins2 ++ ins5 ++ con5b

/-- **The schedule `σ₀` of Figure 1.** -/
def sigma0 : LSched ℕ := hist0.map Ev.erase

/-! ### Concrete histories: local serializability and linearizability -/

lemma numOps_eq_zero_of {P X Op Res Obj Val : Type} [DecidableEq P] [DecidableEq X]
    (H : Hist P X Op Res Obj Val) (p : P) (x : X) (h : ∀ e ∈ H, e.proc ≠ p) :
    numOps H p x = 0 := by
  unfold numOps restrictPX
  rw [List.filter_eq_nil_iff.2 (fun e he => by simp [h e he])]
  rfl

/-- Local serializability of a concrete history from witnesses `W p k` (a sequential history of
`LL` preceding the `k`-th operation of `p`). -/
lemma locSer_of_witness (H : LHist ℕ) (N : ℕ) (W : ℕ → ℕ → LHist ℕ)
    (hN : ∀ e ∈ H, e.proc < N)
    (h : ∀ p < N, ∀ k < numOps H p (), W p k ++ localView H p () k ∈ (SigLL : Set (LHist ℕ))) :
    LocSer SigLL H := by
  intro p x k hk
  by_cases hp : p < N
  · exact ⟨W p k, h p hp k hk⟩
  · rw [numOps_eq_zero_of H p x (fun e he => by have := hN e he; omega)] at hk
    omega

/-- `insert(5)` run alone on `{1, 3, 4}` (a sequential history used as a witness). -/
def ins5seq : LHist ℕ :=
  [.inv 3 () (.insert 5)] ++ rd 3 headL ⟨.ninf, Xl 1⟩ ++ rd 3 (Xl 1) ⟨.fin 1, Xl 3⟩ ++
    rd 3 (Xl 3) ⟨.fin 3, Xl 4⟩ ++ rd 3 (Xl 4) ⟨.fin 4, tailL⟩ ++ rd 3 tailL ⟨.pinf, tailL⟩ ++
    wr 3 (Xl 5) ⟨.fin 5, tailL⟩ ++ wr 3 (Xl 4) ⟨.fin 4, Xl 5⟩ ++ [.res 3 () true]

/-- Witnesses of local serializability for the histories of this file. -/
def lsWit : ℕ → ℕ → LHist ℕ
  | 0, k => pre134.take (10 * k)
  | 1, _ => pre134 ++ ins5seq
  | 2, _ => pre134
  | 3, _ => pre134 ++ ins2
  | _, _ => pre134 ++ ins2 ++ ins5

lemma hist0_honest : Honest hist0 := by decide +kernel

lemma complete_hist0 : complete hist0 = hist0 := by decide +kernel

lemma hist0_locSer : LocSer SigLL hist0 :=
  locSer_of_witness hist0 4 lsWit (by decide +kernel) (by decide +kernel)

/-- Linearization points of `hist0`. -/
def lp0 : List (LPLabel ℕ setObj) :=
  [.inv 0 (.insert 4), .lin 0, .ret 0 true, .inv 0 (.insert 3), .lin 0, .ret 0 true,
    .inv 0 (.insert 1), .lin 0, .ret 0 true, .inv 1 (.contains 5),
    .inv 2 (.insert 2), .lin 2, .ret 2 true, .inv 3 (.insert 5), .lin 3, .ret 3 true,
    .lin 1, .ret 1 true]

instance instDecEqSetObjRespSM : DecidableEq setObj.Resp := inferInstanceAs (DecidableEq Bool)

lemma hist0_lsl : LSL_LL hist0 := by
  refine ⟨hist0_locSer, ?_⟩
  have hrun : (lpRun (setObj.init, fun _ => .idle) lp0).isSome := by decide +kernel
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 hrun
  exact hwLinearizable_of_lpRun hc' rfl

/-- **Figure 1** (caption): `σ₀` is an `(LL, set)`-LSL schedule (exported by the honest
history `hist0`). -/
theorem sigma0_lsl : LSLSched SigLL (specSet ℕ) sigma0 :=
  ⟨hist0, hist0_lsl, by unfold Exports sched sigma0; rw [complete_hist0]⟩

/-! ## Theorem 6 as stated fails: a stalled commit-pending transaction -/

/-- `remove(2)` by process `4`: reads `h`, `X₁ = ⟨1, X₂⟩`, `X₂ = ⟨2, X₃⟩`, writes
`X₁ := ⟨1, X₃⟩`, and then stalls before returning (commit-pending). -/
def rem2 : LHist ℕ :=
  [.inv 4 () (.remove 2)] ++ rd 4 headL ⟨.ninf, Xl 1⟩ ++ rd 4 (Xl 1) ⟨.fin 1, Xl 2⟩ ++
    rd 4 (Xl 2) ⟨.fin 2, Xl 3⟩ ++ wr 4 (Xl 1) ⟨.fin 1, Xl 3⟩

/-- `hist0` with a stalled `remove(2)` after `insert(5)` (informally: a NOrec-like execution,
with value-based validation, in which process `4` stops after its commit took effect). -/
def histLoop : LHist ℕ := pre134 ++ con5a ++ ins2 ++ ins5 ++ rem2 ++ con5b

lemma histLoop_honest : Honest histLoop := by decide +kernel

lemma complete_histLoop : complete histLoop = hist0 := by decide +kernel

lemma histLoop_locSer : LocSer SigLL histLoop :=
  locSer_of_witness histLoop 5 lsWit (by decide +kernel) (by decide +kernel)

/-- Linearization points of `histLoop` (`remove(2)` stays pending and is not linearized). -/
def lpLoop : List (LPLabel ℕ setObj) :=
  [.inv 0 (.insert 4), .lin 0, .ret 0 true, .inv 0 (.insert 3), .lin 0, .ret 0 true,
    .inv 0 (.insert 1), .lin 0, .ret 0 true, .inv 1 (.contains 5),
    .inv 2 (.insert 2), .lin 2, .ret 2 true, .inv 3 (.insert 5), .lin 3, .ret 3 true,
    .inv 4 (.remove 2), .lin 1, .ret 1 true]

lemma histLoop_lsl : LSL_LL histLoop := by
  refine ⟨histLoop_locSer, ?_⟩
  have hrun : (lpRun (setObj.init, fun _ => .idle) lpLoop).isSome := by decide +kernel
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 hrun
  exact hwLinearizable_of_lpRun hc' rfl

/-- The stalled `remove(2)`. -/
abbrev tRem : TxId ℕ Unit := (4, (), 0)

lemma commitPending_rem : CommitPending histLoop tRem :=
  ⟨by decide +kernel, .remove 2, .done true, true, by decide +kernel, rfl⟩

/-- The selection of commit-pending transactions: `remove(2)`. -/
def selRem (t : TxId ℕ Unit) : Bool := decide (t = tRem)

/-- The serialization: the prefix, `insert(2)`, `insert(5)`, `remove(2)`, `contains(5)`. -/
def ordLoop : List (TxId ℕ Unit) :=
  [(0, (), 0), (0, (), 1), (0, (), 2), (2, (), 0), (3, (), 0), tRem, (1, (), 0)]

lemma isTxn_proc {P X Op Res Obj Val : Type} [DecidableEq P] [DecidableEq X]
    (H : Hist P X Op Res Obj Val) (t : TxId P X) (h : IsTxn H t) : ∃ e ∈ H, e.proc = t.1 := by
  by_contra hc
  push Not at hc
  unfold IsTxn at h
  rw [numOps_eq_zero_of H t.1 t.2.1 hc] at h
  omega

/-- The transactions of a concrete history (with processes `< N`) are those of a list. -/
lemma isTxn_iff_of (H : LHist ℕ) (L : List (TxId ℕ Unit)) (N : ℕ)
    (hN : ∀ e ∈ H, e.proc < N) (h1 : ∀ t ∈ L, IsTxn H t)
    (h2 : ((List.range N).all fun p =>
      (List.range (numOps H p ())).all fun k => decide ((p, (), k) ∈ L)) = true) :
    ∀ t, t ∈ L ↔ IsTxn H t := by
  rintro ⟨p, x, k⟩
  refine ⟨h1 _, fun h => ?_⟩
  obtain ⟨e, he, hp⟩ := isTxn_proc H _ h
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h2
  exact h2 p (by simpa [hp] using hN e he) k h

lemma serialWitness_loop : SerialWitness (cseq histLoop selRem) ordLoop := by
  have h4 : ∀ t ∈ ordLoop, ∀ t' ∈ ordLoop, Precedes (cseq histLoop selRem) t t' →
      ordLoop.idxOf t < ordLoop.idxOf t' := by
    decide +kernel
  exact ⟨by decide +kernel, isTxn_iff_of _ _ 5 (by decide +kernel) (by decide +kernel)
    (by decide +kernel),
    by decide +kernel, fun t t' ht ht' => h4 t ht t' ht'⟩

lemma strictSer_loop : StrictSer histLoop := by
  refine ⟨selRem, fun t ht => ?_, ordLoop, serialWitness_loop⟩
  simp only [selRem, decide_eq_true_eq] at ht
  subst ht
  exact commitPending_rem

/-- A property of all transactions of a concrete history (with processes `< N`), checked on a
finite range. -/
lemma forall_txn_of (H : LHist ℕ) (N : ℕ) (Q : TxId ℕ Unit → Prop) [DecidablePred Q]
    (hN : ∀ e ∈ H, e.proc < N)
    (h : ((List.range N).all fun p =>
      (List.range (numOps H p ())).all fun k => decide (Q (p, (), k))) = true) :
    ∀ t, IsTxn H t → Q t := by
  rintro ⟨p, x, k⟩ ht
  obtain ⟨e, he, hp⟩ := isTxn_proc H _ ht
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h p (by simpa [hp] using hN e he) k ht

/-- The only incomplete or aborted transaction of `histLoop` is `remove(2)`. -/
lemma histLoop_live : ∀ t, IsTxn histLoop t → (Incomplete histLoop t ∨ Aborted histLoop t) →
    t = tRem :=
  forall_txn_of histLoop 5 (fun t => (Incomplete histLoop t ∨ Aborted histLoop t) → t = tRem)
    (by decide +kernel) (by decide +kernel)

/-- Length of `H_k` for `remove(2)`. -/
def nRem : ℕ := (pre134 ++ con5a ++ ins2 ++ ins5 ++ rem2).length

lemma safeStrictSer_loop : SafeStrictSer histLoop := by
  refine ⟨strictSer_loop, fun t ht hl => ?_⟩
  obtain rfl := histLoop_live t ht hl
  refine ⟨nRem, by decide +kernel, fun _ => false, fun _ h => absurd h (by simp),
    [(0, (), 0), (0, (), 1), (0, (), 2), (2, (), 0), (3, (), 0)], by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- **Theorem 6 (part 1 of Theorem 2), the SM half, fails as stated.** The paper claims that no
`(LL, set)`-LSL implementation in `SM` (based on a safe-strict serializable TM) accepts `σ₀`.
But acceptance only looks at `complete(H)`, and safe-strict serializability lets a stalled
commit-pending transaction (here `remove(2)`, which re-links `X₁ := ⟨1, X₃⟩`) justify the read of
`contains(5)`. `histLoop` is honest (every read returns the latest written value), LSL,
safe-strict serializable, has a commit-pending transaction, and exports `σ₀`. -/
theorem theorem_6_loophole :
    ∃ H : LHist ℕ, Honest H ∧ LSL_LL H ∧ SafeStrictSer H ∧ CommitPending H tRem ∧
      Exports H sigma0 :=
  ⟨histLoop, histLoop_honest, histLoop_lsl, safeStrictSer_loop, commitPending_rem,
    by unfold Exports sched sigma0; rw [complete_histLoop]⟩

/-! ## Erasure: transactions and real-time order are determined by the schedule -/

section Erase

variable {P X Op Res Obj Val : Type} [DecidableEq P] [DecidableEq X]

/-- Process of a schedule event. -/
def SEv.proc : SEv P X Op Obj Val → P
  | .inv p .. | .res p .. | .rinv p .. | .rres p .. | .winv p .. | .wres p .. => p

/-- Object of a schedule event. -/
def SEv.obj : SEv P X Op Obj Val → X
  | .inv _ x _ | .res _ x | .rinv _ x _ | .rres _ x | .winv _ x _ _ | .wres _ x => x

/-- High-level invocation. -/
def SEv.isInv : SEv P X Op Obj Val → Bool
  | .inv .. => true
  | _ => false

/-- High-level response. -/
def SEv.isRes : SEv P X Op Obj Val → Bool
  | .res .. => true
  | _ => false

/-- Skeleton of a schedule event. -/
def SEv.skel (s : SEv P X Op Obj Val) : P × X × Bool := (s.proc, s.obj, s.isInv)

omit [DecidableEq P] [DecidableEq X] in
lemma Ev.skel_eq (e : Ev P X Op Res Obj Val) : e.skel = e.erase.skel := by
  cases e <;> rfl

/-- `splitOps` for any type of events. -/
def splitG {α : Type} (isI : α → Bool) (l : List α) : List (List α) :=
  (l.foldr (fun e (acc : List α × List (List α)) =>
    if isI e then ([], (e :: acc.1) :: acc.2) else (e :: acc.1, acc.2)) ([], [])).2

lemma foldr_split_map {α β : Type} (isI : β → Bool) (g : α → β) (l : List α) :
    (l.map g).foldr (fun e (acc : List β × List (List β)) =>
      if isI e then ([], (e :: acc.1) :: acc.2) else (e :: acc.1, acc.2)) ([], []) =
    (((l.foldr (fun e (acc : List α × List (List α)) =>
      if isI (g e) then ([], (e :: acc.1) :: acc.2) else (e :: acc.1, acc.2)) ([], [])).1.map g),
     ((l.foldr (fun e (acc : List α × List (List α)) =>
      if isI (g e) then ([], (e :: acc.1) :: acc.2) else (e :: acc.1, acc.2)) ([], [])).2.map
        (List.map g))) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.map_cons, List.foldr_cons, ih]
    split_ifs <;> simp

lemma splitG_map {α β : Type} (isI : β → Bool) (g : α → β) (l : List α) :
    splitG isI (l.map g) = (splitG (isI ∘ g) l).map (List.map g) := by
  unfold splitG
  rw [foldr_split_map]
  rfl

/-- Events of a transaction, in a schedule. -/
def txEventsS (σ : List (SEv P X Op Obj Val)) (t : TxId P X) : List (SEv P X Op Obj Val) :=
  (splitG SEv.isInv (σ.filter fun s => decide (s.proc = t.1) && decide (s.obj = t.2.1))).getD
    t.2.2 []

/-- Number of operations of `p` on `x`, in a schedule. -/
def numOpsS (σ : List (SEv P X Op Obj Val)) (p : P) (x : X) : ℕ :=
  (splitG SEv.isInv (σ.filter fun s => decide (s.proc = p) && decide (s.obj = x))).length

lemma restrictPX_map_erase (H : Hist P X Op Res Obj Val) (p : P) (x : X) :
    (restrictPX H p x).map Ev.erase =
      (H.map Ev.erase).filter (fun s => decide (s.proc = p) && decide (s.obj = x)) := by
  rw [List.filter_map, restrictPX]
  congr 2
  funext e
  cases e <;> rfl

omit [DecidableEq P] [DecidableEq X] in
lemma splitOps_map_erase (l : Hist P X Op Res Obj Val) :
    (splitOps l).map (List.map Ev.erase) = splitG SEv.isInv (l.map Ev.erase) := by
  rw [splitG_map]
  have : (SEv.isInv ∘ Ev.erase : Ev P X Op Res Obj Val → Bool) = Ev.isInv := by
    funext e; cases e <;> rfl
  rw [this]
  rfl

lemma txEvents_map_erase (H : Hist P X Op Res Obj Val) (t : TxId P X) :
    (txEvents H t).map Ev.erase = txEventsS (H.map Ev.erase) t := by
  unfold txEvents txEventsS
  rw [← restrictPX_map_erase, ← splitOps_map_erase]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (splitOps (restrictPX H t.1 t.2.1))[t.2.2]? <;> simp

lemma numOps_eq_numOpsS (H : Hist P X Op Res Obj Val) (p : P) (x : X) :
    numOps H p x = numOpsS (H.map Ev.erase) p x := by
  unfold numOps numOpsS
  rw [← restrictPX_map_erase, ← splitOps_map_erase, List.length_map]

lemma txList_eq (H : Hist P X Op Res Obj Val) :
    txList H = txOfSkel (fun _ _ => 0) ((H.map Ev.erase).map SEv.skel) := by
  unfold txList
  rw [List.map_map]
  congr 1
  exact List.map_congr_left (fun e _ => Ev.skel_eq e)

/-- Real-time order, computed on a schedule. -/
def PrecS (σ : List (SEv P X Op Obj Val)) (t t' : TxId P X) : Prop :=
  (∃ s ∈ txEventsS σ t, s.isRes = true) ∧ ∃ n < σ.length + 1,
    some t ∉ (txOfSkel (fun _ _ => 0) (σ.map SEv.skel)).drop n ∧
    some t' ∉ (txOfSkel (fun _ _ => 0) (σ.map SEv.skel)).take n

instance (σ : List (SEv P X Op Obj Val)) (t t' : TxId P X) : Decidable (PrecS σ t t') :=
  inferInstanceAs (Decidable (_ ∧ _))

lemma precedes_of_precS (H : Hist P X Op Res Obj Val) (t t' : TxId P X)
    (h : PrecS (H.map Ev.erase) t t') : Precedes H t t' := by
  obtain ⟨⟨s, hs, hr⟩, n, -, h1, h2⟩ := h
  refine ⟨?_, n, by rwa [txList_eq], by rwa [txList_eq]⟩
  rw [← txEvents_map_erase, List.mem_map] at hs
  obtain ⟨e, he, rfl⟩ := hs
  refine ⟨e, he, ?_⟩
  cases e <;> simp_all [SEv.isRes, Ev.erase, Ev.isTerm, Ev.isRes]

end Erase

/-! ## Theorem 6 repaired: no quiescent strictly serializable history exports `σ₀` -/

section Quiescent

variable {P : Type} [DecidableEq P]

/-- Effect of a schedule event on the configuration of a legal run (writes take effect at their
response). -/
def sStep (c : Mem × Option Pend) : SEv P Unit SetOp Loc NodeV → Mem × Option Pend
  | .rinv _ _ y => (c.1, some (.rd y))
  | .rres _ _ => (c.1, none)
  | .winv _ _ y n => (c.1, some (.wr y n))
  | .wres _ _ => match c.2 with
    | some (.wr y n) => (Function.update c.1 y (some n), none)
    | _ => (c.1, none)
  | _ => c

/-- Run `sStep` along a schedule. -/
def sRun (c : Mem × Option Pend) : List (SEv P Unit SetOp Loc NodeV) → Mem × Option Pend
  | [] => c
  | s :: l => sRun (sStep c s) l

omit [DecidableEq P] in
lemma legStep_eq {c c' : Mem × Option Pend} {e : LEv P} (h : legStep c e = some c') :
    c' = sStep c e.erase := by
  rcases c with ⟨m, q⟩
  cases e with
  | inv => simp [legStep] at h; simp [h, sStep, Ev.erase]
  | res => simp [legStep] at h; simp [h, sStep, Ev.erase]
  | rinv => simp [legStep] at h; simp [← h.2, sStep, Ev.erase]
  | winv => simp [legStep] at h; simp [← h.2, sStep, Ev.erase]
  | rres p x v =>
    simp only [legStep] at h
    split at h <;> simp at h
    simp [← h.2, sStep, Ev.erase]
  | wres p x ok =>
    simp only [legStep] at h
    split at h <;> simp at h
    obtain ⟨rfl, rfl⟩ := h
    simp [sStep, Ev.erase]

omit [DecidableEq P] in
/-- The configuration reached by a legal run depends only on the schedule. -/
lemma legRun_eq {c c' : Mem × Option Pend} {l : LHist P} (h : legRun c l = some c') :
    c' = sRun c (l.map Ev.erase) := by
  induction l generalizing c with
  | nil => simp [legRun] at h; simp [h, sRun]
  | cons e l ih =>
    simp only [legRun] at h
    cases he : legStep c e with
    | none => simp [he] at h
    | some c₁ =>
      rw [he, Option.bind_some] at h
      rw [List.map_cons, sRun, ← legStep_eq he]
      exact ih h

/-- A block of `contains(5)` by process `1` with the read pattern of `σ₀` and arbitrary values. -/
def conBlk (a0 a1 a3 a4 a5 : Option NodeV) (b : Bool) : LHist ℕ :=
  [.inv 1 () (.contains 5), .rinv 1 () headL, .rres 1 () a0, .rinv 1 () (Xl 1), .rres 1 () a1,
    .rinv 1 () (Xl 3), .rres 1 () a3, .rinv 1 () (Xl 4), .rres 1 () a4, .rinv 1 () (Xl 5),
    .rres 1 () a5, .res 1 () b]

lemma seqRun_rd (m : Mem) (q : ℕ) (o : SetOp) (st : St) (p : ℕ) (y : Loc) (v : Option NodeV)
    (l : LHist ℕ) :
    seqRun ⟨m, some (q, o, st), none⟩ (.rinv p () y :: .rres p () v :: l) =
      if q = p ∧ act o st = .read y ∧ v = m y ∧ v.isSome then
        seqRun ⟨m, some (q, o, onRead o st y (v.getD ⟨.ninf, 0⟩)), none⟩ l else none := by
  rcases v with _ | v <;> simp only [seqRun, seqStep] <;> split_ifs <;> simp_all
  split_ifs <;> simp_all

lemma seqRun_inv (m : Mem) (p : ℕ) (o : SetOp) (l : LHist ℕ) :
    seqRun ⟨m, none, none⟩ (.inv p () o :: l) = seqRun ⟨m, some (p, o, .start), none⟩ l := rfl

/-- If `contains` reads a node `n` and then reads `z`, then `n.next = z` (it is traversing). -/
lemma onRead_contains_read {v : ℤ} {s : St} {y : Loc} {n : NodeV} {z : Loc}
    (h : act (.contains v) (onRead (.contains v) s y n) = .read z) :
    ∃ y', onRead (.contains v) s y n = .trav y' n ∧ n.next = z := by
  cases s with
  | start => simp_all [onRead, act]
  | trav old prev =>
    simp only [onRead] at h ⊢
    split_ifs at h ⊢
    · simp_all [act]
    · simp [finish, act] at h
  | alloc => simp [onRead, act] at h
  | wr => simp [onRead, act] at h
  | done => simp [onRead, act] at h

/-- `LL` forces the values read by `contains(5)` from `X₁` and `X₄`: since it reads `X₃` next,
`X₁.next = X₃`; since it reads `X₅` next, `X₄.next = X₅`. -/
lemma seqRun_conBlk (cfg : SCfg ℕ) (a0 a1 a3 a4 a5 : Option NodeV) (b : Bool)
    (h : (seqRun cfg (conBlk a0 a1 a3 a4 a5 b)).isSome) :
    (∃ n, a1 = some n ∧ n.next = Xl 3) ∧ ∃ n, a4 = some n ∧ n.next = Xl 5 := by
  rcases cfg with ⟨m, cur, pd⟩
  rcases cur with _ | _
  · rcases pd with _ | _
    · simp only [conBlk, seqRun_inv, seqRun_rd] at h
      split_ifs at h with h0 h1 h3 h4 h5
      · obtain ⟨-, -, -, ha0⟩ := h0
        obtain ⟨-, -, -, ha1⟩ := h1
        obtain ⟨-, hx3, -, -⟩ := h3
        obtain ⟨-, hx4, -, ha4⟩ := h4
        obtain ⟨-, hx5, -, -⟩ := h5
        obtain ⟨n1, rfl⟩ := Option.isSome_iff_exists.1 ha1
        obtain ⟨n4, rfl⟩ := Option.isSome_iff_exists.1 ha4
        simp only [Option.getD_some] at hx3 hx4 hx5
        obtain ⟨y1, hy1, hn1⟩ := onRead_contains_read hx3
        rw [hy1] at hx4 hx5
        obtain ⟨y3, hy3, -⟩ := onRead_contains_read hx4
        rw [hy3] at hx5
        obtain ⟨-, -, hn4⟩ := onRead_contains_read hx5
        exact ⟨⟨n1, rfl, hn1⟩, ⟨n4, rfl, hn4⟩⟩
      all_goals simp at h
    · simp [conBlk, seqRun, seqStep] at h
  · simp [conBlk, seqRun, seqStep] at h

omit [DecidableEq P] in
lemma legRun_inv (c : Mem × Option Pend) (p : P) (o : SetOp) (l : LHist P) :
    legRun c (.inv p () o :: l) = legRun c l := rfl

omit [DecidableEq P] in
lemma legRun_rd (m : Mem) (p : P) (y : Loc) (v : Option NodeV) (l : LHist P) :
    legRun (m, none) (.rinv p () y :: .rres p () v :: l) =
      if v.isSome ∧ v = m y then legRun (m, none) l else none := by
  simp only [legRun, legStep, ite_true, Option.bind_some]
  split_ifs <;> simp

/-- Legality forces the values read by `contains(5)` from `X₁` and `X₄` (it writes nothing). -/
lemma legRun_conBlk (c : Mem × Option Pend) (a0 a1 a3 a4 a5 : Option NodeV) (b : Bool)
    (h : (legRun c (conBlk a0 a1 a3 a4 a5 b)).isSome) :
    a1 = c.1 (Xl 1) ∧ a4 = c.1 (Xl 4) := by
  rcases c with ⟨m, q⟩
  rcases q with _ | _
  · simp only [conBlk, legRun_inv, legRun_rd] at h
    split_ifs at h with h0 h1 h3 h4 h5 <;> simp_all
  · simp [conBlk, legRun, legStep] at h

omit [DecidableEq P] in
lemma erase_eq_inv_iff {e : LEv P} {p : P} {o : SetOp} :
    e.erase = SEv.inv p () o ↔ e = .inv p () o := by
  cases e <;> simp [Ev.erase]

omit [DecidableEq P] in
lemma erase_eq_rinv_iff {e : LEv P} {p : P} {y : Loc} :
    e.erase = SEv.rinv p () y ↔ e = .rinv p () y := by
  cases e <;> simp [Ev.erase]

omit [DecidableEq P] in
lemma erase_eq_rres_iff {e : LEv P} {p : P} :
    e.erase = SEv.rres p () ↔ ∃ v, e = .rres p () v := by
  cases e <;> simp [Ev.erase]

omit [DecidableEq P] in
lemma erase_eq_res_iff {e : LEv P} {p : P} :
    e.erase = SEv.res p () ↔ ∃ r, e = .res p () r := by
  cases e <;> simp [Ev.erase]

lemma conBlk_of_erase (B : LHist ℕ) (h : B.map Ev.erase = txEventsS sigma0 (1, (), 0)) :
    ∃ a0 a1 a3 a4 a5 b, B = conBlk a0 a1 a3 a4 a5 b := by
  have hs : txEventsS sigma0 (1, (), 0) = [.inv 1 () (.contains 5), .rinv 1 () headL,
      .rres 1 (), .rinv 1 () (Xl 1), .rres 1 (), .rinv 1 () (Xl 3), .rres 1 (), .rinv 1 () (Xl 4),
      .rres 1 (), .rinv 1 () (Xl 5), .rres 1 (), .res 1 ()] := by
    decide +kernel
  rw [hs] at h
  simp only [List.map_eq_cons_iff, erase_eq_inv_iff, erase_eq_rinv_iff, erase_eq_rres_iff, erase_eq_res_iff,
    List.map_eq_nil_iff] at h
  obtain ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, ⟨a0, rfl⟩, _, _, rfl, rfl, _, _, rfl, ⟨a1, rfl⟩,
    _, _, rfl, rfl, _, _, rfl, ⟨a3, rfl⟩, _, _, rfl, rfl, _, _, rfl, ⟨a4, rfl⟩, _, _, rfl, rfl,
    _, _, rfl, ⟨a5, rfl⟩, _, _, rfl, ⟨b, rfl⟩, rfl⟩ := h
  exact ⟨a0, a1, a3, a4, a5, b, rfl⟩

/-- A serialization of six transactions respecting the real-time constraints of `σ₀`
(`a → b → c → d`, `c → e → f`) is one of three orders. -/
lemma ord_cases {T : Type} [DecidableEq T] (ord : List T) (a b c d e f : T)
    (hd : [a, b, c, d, e, f].Nodup) (hnd : ord.Nodup) (hmem : ∀ t, t ∈ ord ↔ t ∈ [a, b, c, d, e, f])
    (h1 : ord.idxOf a < ord.idxOf b) (h2 : ord.idxOf b < ord.idxOf c)
    (h3 : ord.idxOf c < ord.idxOf d) (h4 : ord.idxOf c < ord.idxOf e)
    (h5 : ord.idxOf e < ord.idxOf f) :
    ord = [a, b, c, d, e, f] ∨ ord = [a, b, c, e, d, f] ∨ ord = [a, b, c, e, f, d] := by
  have hlen : ord.length = 6 := ((List.perm_ext_iff_of_nodup hnd hd).2 hmem).length_eq
  have mem : ∀ t ∈ [a, b, c, d, e, f], t ∈ ord := fun t ht => (hmem t).2 ht
  have g : ∀ t ∈ [a, b, c, d, e, f], ord[ord.idxOf t]? = some t :=
    fun t ht => List.getElem?_idxOf (mem t ht)
  have lt : ∀ t ∈ [a, b, c, d, e, f], ord.idxOf t < 6 :=
    fun t ht => hlen ▸ List.idxOf_lt_length_of_mem (mem t ht)
  have inj : ∀ x ∈ [a, b, c, d, e, f], ∀ y ∈ [a, b, c, d, e, f], x ≠ y →
      ord.idxOf x ≠ ord.idxOf y := by
    intro x hx y hy hxy hi
    have := g x hx
    rw [hi, g y hy] at this
    exact hxy (Option.some_injective _ this).symm
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    and_true, not_or] at hd
  have ga := g a (by simp); have gb := g b (by simp); have gc := g c (by simp)
  have gd := g d (by simp); have ge := g e (by simp); have gf := g f (by simp)
  have la := lt a (by simp); have lb := lt b (by simp); have lc := lt c (by simp)
  have ld := lt d (by simp); have le := lt e (by simp); have lf := lt f (by simp)
  have iad := inj a (by simp) d (by simp) (by tauto)
  have iae := inj a (by simp) e (by simp) (by tauto)
  have iaf := inj a (by simp) f (by simp) (by tauto)
  have ibd := inj b (by simp) d (by simp) (by tauto)
  have ibe := inj b (by simp) e (by simp) (by tauto)
  have ibf := inj b (by simp) f (by simp) (by tauto)
  have icf := inj c (by simp) f (by simp) (by tauto)
  have ide := inj d (by simp) e (by simp) (by tauto)
  have idf := inj d (by simp) f (by simp) (by tauto)
  generalize ord.idxOf a = ia at *
  generalize ord.idxOf b = ib at *
  generalize ord.idxOf c = ic at *
  generalize ord.idxOf d = id at *
  generalize ord.idxOf e = ie at *
  generalize ord.idxOf f = jf at *
  have hab : ia = 0 ∧ ib = 1 ∧ ic = 2 := by omega
  obtain ⟨rfl, rfl, rfl⟩ := hab
  have key : (id = 3 ∧ ie = 4 ∧ jf = 5) ∨ (id = 4 ∧ ie = 3 ∧ jf = 5) ∨
      (id = 5 ∧ ie = 3 ∧ jf = 4) := by omega
  have ext : ∀ l : List T, l.length = 6 → ord[0]? = l[0]? → ord[1]? = l[1]? → ord[2]? = l[2]? →
      ord[3]? = l[3]? → ord[4]? = l[4]? → ord[5]? = l[5]? → ord = l := by
    intro l hl e0 e1 e2 e3 e4 e5
    apply List.ext_getElem?
    intro j
    rcases j with _ | _ | _ | _ | _ | _ | j
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  rcases key with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact Or.inl (ext _ rfl ga gb gc gd ge gf)
  · exact Or.inr (Or.inl (ext _ rfl ga gb gc ge gd gf))
  · exact Or.inr (Or.inr (ext _ rfl ga gb gc ge gf gd))

lemma seqRun_app (c : SCfg ℕ) (l₁ l₂ : LHist ℕ) :
    seqRun c (l₁ ++ l₂) = (seqRun c l₁).bind (fun c' => seqRun c' l₂) := by
  induction l₁ generalizing c with
  | nil => simp [seqRun]
  | cons e l ih =>
    simp only [List.cons_append, seqRun]
    cases seqStep c e <;> simp [ih]

/-- In a legal `A ++ B ++ R`, the block `B` runs legally from the memory left by `A`, which is
determined by the schedule of `A`. -/
lemma legal_mid (A B R : LHist ℕ) (h : Legal (A ++ B ++ R)) :
    (legRun (sRun (mem0, none) (A.map Ev.erase)) B).isSome := by
  unfold Legal at h
  rw [legRun_append, legRun_append] at h
  cases hA : legRun (mem0, none) A with
  | none => simp [hA] at h
  | some cA =>
    rw [hA, Option.bind_some] at h
    rw [← legRun_eq hA]
    cases hB : legRun cA B with
    | none => simp [hB] at h
    | some _ => rfl

/-- The transactions of `σ₀`. -/
abbrev tI4 : TxId ℕ Unit := (0, (), 0)
/-- `insert(3)` of the prefix. -/
abbrev tI3 : TxId ℕ Unit := (0, (), 1)
/-- `insert(1)` of the prefix. -/
abbrev tI1 : TxId ℕ Unit := (0, (), 2)
/-- `contains(5)`. -/
abbrev tC5 : TxId ℕ Unit := (1, (), 0)
/-- `insert(2)`. -/
abbrev tI2 : TxId ℕ Unit := (2, (), 0)
/-- `insert(5)`. -/
abbrev tI5 : TxId ℕ Unit := (3, (), 0)

lemma numOpsS_sigma0_ge (p : ℕ) (hp : 4 ≤ p) (x : Unit) : numOpsS sigma0 p x = 0 := by
  have h : ∀ s ∈ sigma0, s.proc < 4 := by decide +kernel
  unfold numOpsS
  rw [List.filter_eq_nil_iff.2 (fun s hs => by have := h s hs; simp; omega)]
  rfl

/-- The transactions of a history exporting `σ₀`, with no commit-pending transaction. -/
lemma isTxn_of_sigma0 (G : LHist ℕ) (hE : G.map Ev.erase = sigma0) (t : TxId ℕ Unit) :
    IsTxn G t ↔ t ∈ [tI4, tI3, tI1, tC5, tI2, tI5] := by
  obtain ⟨p, x, k⟩ := t
  cases x
  unfold IsTxn
  simp only [numOps_eq_numOpsS, hE]
  by_cases hp : p < 4
  · interval_cases p
    · rw [show numOpsS sigma0 0 () = 3 by decide +kernel]; simp; omega
    · rw [show numOpsS sigma0 1 () = 1 by decide +kernel]; simp
    · rw [show numOpsS sigma0 2 () = 1 by decide +kernel]; simp
    · rw [show numOpsS sigma0 3 () = 1 by decide +kernel]; simp
  · rw [numOpsS_sigma0_ge p (by omega)]; simp; omega

lemma blocks_erase (G : LHist ℕ) (hE : G.map Ev.erase = sigma0) (o : List (TxId ℕ Unit)) :
    (o.flatMap (txEvents G)).map Ev.erase = o.flatMap (txEventsS sigma0) := by
  rw [List.map_flatMap]
  congr 1
  funext t
  rw [txEvents_map_erase, hE]

/-- **Theorem 6 (part 1 of Theorem 2), the SM half, with the definition of Appendix C.1.**
Appendix C.1 defines strict serializability with `cseq(α)` = the events of the *complete*
operations only (no commit-pending transactions). No history `H` that is strictly serializable
in this sense, and whose committed operations follow `LL` (`complete(H)` is locally serializable
w.r.t. `Σ_LL`), exports the schedule `σ₀` of Figure 1. This is the paper's proof: `contains(5)`
reads `X₁` with `next = X₃`, so it is serialized before `insert(2)`, which precedes `insert(5)` in
real time; then `contains(5)` reads `X₄` before `insert(5)` writes `X₄ := ⟨4, X₅⟩`, so its
`next` is `tail`, while `LL` reads `X₅` next. -/
theorem theorem_6_appendix (H : LHist ℕ) (hS : ∃ ord, SerialWitness (complete H) ord)
    (hL : LocSer SigLL (complete H)) : ¬ Exports H sigma0 := by
  intro hE
  obtain ⟨ord, hnd, hmem, hleg, hrt⟩ := hS
  have hE' : (complete H).map Ev.erase = sigma0 := hE
  generalize complete H = G at hE' hmem hleg hrt hL
  have hmem' : ∀ t, t ∈ ord ↔ t ∈ [tI4, tI3, tI1, tC5, tI2, tI5] :=
    fun t => (hmem t).trans (isTxn_of_sigma0 G hE' t)
  have mo : ∀ t ∈ [tI4, tI3, tI1, tC5, tI2, tI5], t ∈ ord := fun t ht => (hmem' t).2 ht
  have prec : ∀ t t', PrecS sigma0 t t' → t ∈ [tI4, tI3, tI1, tC5, tI2, tI5] →
      t' ∈ [tI4, tI3, tI1, tC5, tI2, tI5] → ord.idxOf t < ord.idxOf t' := by
    intro t t' hp ht ht'
    exact hrt t t' (mo t ht) (mo t' ht') (precedes_of_precS G t t' (hE' ▸ hp))
  have h1 := prec tI4 tI3 (by decide +kernel) (by simp) (by simp)
  have h2 := prec tI3 tI1 (by decide +kernel) (by simp) (by simp)
  have h3 := prec tI1 tC5 (by decide +kernel) (by simp) (by simp)
  have h4 := prec tI1 tI2 (by decide +kernel) (by simp) (by simp)
  have h5 := prec tI2 tI5 (by decide +kernel) (by simp) (by simp)
  -- the block of `contains(5)`
  have hB : (txEvents G tC5).map Ev.erase = txEventsS sigma0 tC5 := by
    rw [txEvents_map_erase, hE']
  obtain ⟨a0, a1, a3, a4, a5, b, hBc⟩ := conBlk_of_erase _ hB
  -- `LL`: `X₁.next = X₃` and `X₄.next = X₅`
  have hll : (∃ n, a1 = some n ∧ n.next = Xl 3) ∧ ∃ n, a4 = some n ∧ n.next = Xl 5 := by
    have hk : 0 < numOps G 1 () := by
      rw [numOps_eq_numOpsS, hE']; decide +kernel
    obtain ⟨S₀, hS₀⟩ := hL 1 () 0 hk
    have hv : localView G 1 () 0 = conBlk a0 a1 a3 a4 a5 b := by
      show dropAbort (txEvents G tC5) = _
      rw [hBc]; simp [dropAbort, conBlk, Ev.isAbort]
    rw [hv] at hS₀
    change (seqRun scfg0 (S₀ ++ conBlk a0 a1 a3 a4 a5 b)).isSome = true at hS₀
    rw [seqRun_app] at hS₀
    cases hc : seqRun scfg0 S₀ with
    | none => simp [hc] at hS₀
    | some cfg =>
      rw [hc, Option.bind_some] at hS₀
      exact seqRun_conBlk cfg _ _ _ _ _ _ hS₀
  obtain ⟨⟨n1, rfl, hn1⟩, ⟨n4, rfl, hn4⟩⟩ := hll
  rcases ord_cases ord tI4 tI3 tI1 tC5 tI2 tI5 (by decide) hnd hmem' h1 h2 h3 h4 h5 with
    rfl | rfl | rfl
  · -- `contains(5)` before `insert(2)`: it reads the initial `X₄ = ⟨4, tail⟩`
    have hs : [tI4, tI3, tI1, tC5, tI2, tI5].flatMap (txEvents G) =
        [tI4, tI3, tI1].flatMap (txEvents G) ++ txEvents G tC5 ++
          [tI2, tI5].flatMap (txEvents G) := by simp
    rw [hs, hBc] at hleg
    have hm := legal_mid _ _ _ hleg
    rw [blocks_erase G hE'] at hm
    have h4m := (legRun_conBlk _ _ _ _ _ _ _ hm).2
    rw [show (sRun (mem0, none) ([tI4, tI3, tI1].flatMap (txEventsS sigma0))).1 (Xl 4) =
      some ⟨.fin 4, tailL⟩ by decide +kernel] at h4m
    cases h4m
    simp [Xl, tailL] at hn4
  · -- `insert(2)` before `contains(5)`: it reads `X₁ = ⟨1, X₂⟩`
    have hs : [tI4, tI3, tI1, tI2, tC5, tI5].flatMap (txEvents G) =
        [tI4, tI3, tI1, tI2].flatMap (txEvents G) ++ txEvents G tC5 ++
          [tI5].flatMap (txEvents G) := by simp
    rw [hs, hBc] at hleg
    have hm := legal_mid _ _ _ hleg
    rw [blocks_erase G hE'] at hm
    have h1m := (legRun_conBlk _ _ _ _ _ _ _ hm).1
    rw [show (sRun (mem0, none) ([tI4, tI3, tI1, tI2].flatMap (txEventsS sigma0))).1 (Xl 1) =
      some ⟨.fin 1, Xl 2⟩ by decide +kernel] at h1m
    cases h1m
    simp [Xl] at hn1
  · have hs : [tI4, tI3, tI1, tI2, tI5, tC5].flatMap (txEvents G) =
        [tI4, tI3, tI1, tI2, tI5].flatMap (txEvents G) ++ txEvents G tC5 ++ [] := by simp
    rw [hs, hBc] at hleg
    have hm := legal_mid _ _ _ hleg
    rw [blocks_erase G hE'] at hm
    have h1m := (legRun_conBlk _ _ _ _ _ _ _ hm).1
    rw [show (sRun (mem0, none) ([tI4, tI3, tI1, tI2, tI5].flatMap (txEventsS sigma0))).1 (Xl 1) =
      some ⟨.fin 1, Xl 2⟩ by decide +kernel] at h1m
    cases h1m
    simp [Xl] at hn1

/-- **Theorem 6 (part 1 of Theorem 2), the SM half, repaired** with the §4 definition of strict
serializability: if every transaction committed or aborted (no live or commit-pending
transaction), no strictly serializable history whose committed operations follow `LL` exports
`σ₀`. -/
theorem theorem_6_quiescent (H : LHist ℕ) (hS : StrictSer H) (hQ : Quiescent H)
    (hL : LocSer SigLL (complete H)) : ¬ Exports H sigma0 := by
  obtain ⟨C, hC, ord, hw⟩ := hS
  have hCf : C = fun _ => false := by
    funext t
    cases hct : C t
    · rfl
    · exact absurd (hQ t (hC t hct).1.1) (hC t hct).1.2
  subst hCf
  rw [cseq_false] at hw
  exact theorem_6_appendix H ⟨ord, hw⟩ hL

end Quiescent

end Podc.OptimismConcurrency
