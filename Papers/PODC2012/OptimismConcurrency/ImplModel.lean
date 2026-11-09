import Papers.PODC2012.OptimismConcurrency.LinCheck

/-!
# Concurrent implementations of `(LL, set)` and the class `P` (§2, §4)

An implementation is modelled by the set of histories it exports (`IsImpl`). The processes run
the sequential code `LL` (the *client*): the next invocation of a process is determined by its
local history (`clientSt`, `ClientMove`); the implementation decides when and how to respond to
pending reads and writes (`RespMove`). An implementation must be prefix-closed and may not
refuse client invocations (receptiveness). Its responses may depend on the whole history so far
(base objects are arbitrary and unbounded, §2), and so may its internal decisions.

The class `P` (§4: deadlock-free pessimistic LSL implementations) is `ClassP`. We use the
*strongest* reasonable reading of every ingredient, so that exhibiting a member of `ClassP`
refutes any statement about all members of the paper's class:
* LS-linearizability of every exported history (`LSL_LL`);
* pessimism: no read or write ever returns `⊥`;
* deadlock-freedom (`DeadlockFree`): whenever an operation is in progress some non-invocation
  event is possible (never stuck), and, without new invocations, only boundedly many events can
  happen before some operation returns a matching response (so *every* continuation without new
  invocations, fair or not, completes an operation);
* honesty of every history (every read returns the latest written value), which implies the
  paper's obedience assumption.
-/

namespace Podc.OptimismConcurrency

variable {P : Type} [DecidableEq P]

/-! ## The client (`LL` code run by each process) -/

/-- Local state of a client process. -/
inductive CSt
  | idle
  /-- running operation `o` in control state `s`, no pending read/write -/
  | run (o : SetOp) (s : St)
  /-- running `o` in state `s`, with the pending read/write `q` -/
  | pend (o : SetOp) (s : St) (q : Pend)
  deriving DecidableEq

/-- Effect of an event of the process on its client state. -/
def cstep : CSt → LEv P → CSt
  | _, .inv _ _ o => .run o .start
  | .run o s, .rinv _ _ y => .pend o s (.rd y)
  | .pend o s (.rd y), .rres _ _ (some n) => .run o (onRead o s y n)
  | _, .rres _ _ none => .idle
  | .run o s, .winv _ _ y n => .pend o s (.wr y n)
  | .pend o s (.wr y _), .wres _ _ true => .run o (onWrite s y)
  | _, .wres _ _ false => .idle
  | _, .res .. => .idle
  | c, _ => c

/-- The client state of `p` after `H`. -/
def clientSt (H : LHist P) (p : P) : CSt := (H.filter (fun e => decide (e.proc = p))).foldl cstep .idle

/-- `p` has an operation in progress. -/
def InProgress (H : LHist P) (p : P) : Prop := clientSt H p ≠ .idle

/-- The location `X` occurs in the event. -/
def Ev.mentions (X : Loc) : LEv P → Bool
  | .rinv _ _ y => decide (y = X)
  | .rres _ _ (some n) => decide (n.next = X)
  | .winv _ _ y n => decide (y = X) || decide (n.next = X)
  | _ => false

/-- `X` is fresh after `H`: not a sentinel and never mentioned. -/
def Fresh (H : LHist P) (X : Loc) : Prop :=
  X ≠ headL ∧ X ≠ tailL ∧ ∀ e ∈ H, Ev.mentions X e = false

/-- Invocations the client may issue after `H` (dictated by the code `LL`). -/
def ClientMove (H : LHist P) : LEv P → Prop
  | .inv p _ _ => clientSt H p = .idle
  | .rinv p _ y => ∃ o s, clientSt H p = .run o s ∧ act o s = .read y
  | .winv p _ y n => ∃ o s, clientSt H p = .run o s ∧
      (act o s = .write y n ∨ (act o s = .alloc n ∧ Fresh H y))
  | .res p _ r => ∃ o s, clientSt H p = .run o s ∧ act o s = .ret r
  | _ => False

/-- Responses the implementation may give after `H`: to a pending read or write. -/
def RespMove (H : LHist P) : LEv P → Prop
  | .rres p _ _ => ∃ o s y, clientSt H p = .pend o s (.rd y)
  | .wres p _ _ => ∃ o s y n, clientSt H p = .pend o s (.wr y n)
  | _ => False

/-- `I` (the set of exported histories) is an implementation of `(LL, set)` run by `LL`
clients. -/
structure IsImpl (I : Set (LHist P)) : Prop where
  nil_mem : [] ∈ I
  prefix_closed : ∀ H e, H ++ [e] ∈ I → H ∈ I
  moves : ∀ H e, H ++ [e] ∈ I → ClientMove H e ∨ RespMove H e
  receptive : ∀ H ∈ I, ∀ e, ClientMove H e → H ++ [e] ∈ I

/-- Pessimistic: no read or write ever returns `⊥`. -/
def Pessimistic (I : Set (LHist P)) : Prop := ∀ H ∈ I, ∀ e ∈ H, e.isAbort = false

/-- Deadlock-freedom (strong form, see the module docstring). -/
def DeadlockFree (I : Set (LHist P)) : Prop :=
  (∀ H ∈ I, (∃ p, InProgress H p) → ∃ e : LEv P, e.isInv = false ∧ H ++ [e] ∈ I) ∧
  (∀ H ∈ I, ∃ B : ℕ, ∀ E : LHist P, H ++ E ∈ I →
    (∀ e ∈ E, e.isInv = false ∧ e.isRes = false) → E.length ≤ B)

/-- **The class `P`**: deadlock-free pessimistic LSL implementations of `(LL, set)` (here also
required to be honest, which implies obedience). -/
def ClassP (I : Set (LHist P)) : Prop :=
  IsImpl I ∧ (∀ H ∈ I, LSL_LL H) ∧ Pessimistic I ∧ DeadlockFree I ∧ (∀ H ∈ I, Honest H)

/-! ## The schedule `σ` of Figure 2(a) -/

/-- A complete read of `y` returning `n`. -/
def rd (p : P) (y : Loc) (n : NodeV) : LHist P := [.rinv p () y, .rres p () (some n)]

/-- A complete (successful) write of `n` to `y`. -/
def wr (p : P) (y : Loc) (n : NodeV) : LHist P := [.winv p () y n, .wres p () true]

/-- Node `Xᵥ` of the figures: location `v + 1`. -/
def Xl (v : ℕ) : Loc := v + 1

/-- Initial part of Figure 2(a): process `0` inserts `1`, `2`, `3` sequentially (state
`{1, 2, 3}`, value `i` in node `Xᵢ`). -/
def pre123 : LHist ℕ :=
  [.inv 0 () (.insert 1)] ++ rd 0 headL ⟨.ninf, tailL⟩ ++ rd 0 tailL ⟨.pinf, tailL⟩ ++
    wr 0 (Xl 1) ⟨.fin 1, tailL⟩ ++ wr 0 headL ⟨.ninf, Xl 1⟩ ++ [.res 0 () true] ++
  [.inv 0 () (.insert 2)] ++ rd 0 headL ⟨.ninf, Xl 1⟩ ++ rd 0 (Xl 1) ⟨.fin 1, tailL⟩ ++
    rd 0 tailL ⟨.pinf, tailL⟩ ++ wr 0 (Xl 2) ⟨.fin 2, tailL⟩ ++ wr 0 (Xl 1) ⟨.fin 1, Xl 2⟩ ++
    [.res 0 () true] ++
  [.inv 0 () (.insert 3)] ++ rd 0 headL ⟨.ninf, Xl 1⟩ ++ rd 0 (Xl 1) ⟨.fin 1, Xl 2⟩ ++
    rd 0 (Xl 2) ⟨.fin 2, tailL⟩ ++ rd 0 tailL ⟨.pinf, tailL⟩ ++ wr 0 (Xl 3) ⟨.fin 3, tailL⟩ ++
    wr 0 (Xl 2) ⟨.fin 2, Xl 3⟩ ++ [.res 0 () true]

/-- Initial part of Figure 1 (and of our counterexample to Theorem 3): process `0` inserts `4`,
`3`, `1` sequentially (state `{1, 3, 4}`, value `i` in node `Xᵢ`). -/
def pre134 : LHist ℕ :=
  [.inv 0 () (.insert 4)] ++ rd 0 headL ⟨.ninf, tailL⟩ ++ rd 0 tailL ⟨.pinf, tailL⟩ ++
    wr 0 (Xl 4) ⟨.fin 4, tailL⟩ ++ wr 0 headL ⟨.ninf, Xl 4⟩ ++ [.res 0 () true] ++
  [.inv 0 () (.insert 3)] ++ rd 0 headL ⟨.ninf, Xl 4⟩ ++ rd 0 (Xl 4) ⟨.fin 4, tailL⟩ ++
    wr 0 (Xl 3) ⟨.fin 3, Xl 4⟩ ++ wr 0 headL ⟨.ninf, Xl 3⟩ ++ [.res 0 () true] ++
  [.inv 0 () (.insert 1)] ++ rd 0 headL ⟨.ninf, Xl 3⟩ ++ rd 0 (Xl 3) ⟨.fin 3, Xl 4⟩ ++
    wr 0 (Xl 1) ⟨.fin 1, Xl 3⟩ ++ wr 0 headL ⟨.ninf, Xl 1⟩ ++ [.res 0 () true]

/-- A history of Figure 2(a): then process `1` runs `insert(1)` and process `2` runs
`insert(2)` concurrently; both return `false`. -/
def hist2a : LHist ℕ :=
  pre123 ++
  [.inv 1 () (.insert 1), .inv 2 () (.insert 2)] ++
  [.rinv 1 () headL, .rinv 2 () headL, .rres 1 () (some ⟨.ninf, Xl 1⟩),
    .rres 2 () (some ⟨.ninf, Xl 1⟩)] ++
  [.rinv 1 () (Xl 1), .rinv 2 () (Xl 1), .rres 1 () (some ⟨.fin 1, Xl 2⟩),
    .rres 2 () (some ⟨.fin 1, Xl 2⟩)] ++
  [.res 1 () false] ++ rd 2 (Xl 2) ⟨.fin 2, Xl 3⟩ ++ [.res 2 () false]

/-- **The schedule `σ` of Figure 2(a).** -/
def sigma2a : LSched ℕ := hist2a.map Ev.erase

/-- **Theorem 7** (part 2 of Theorem 2), first half, as claimed: no implementation in `P`
accepts `σ`. (Refuted in `Lookahead.lean`.) -/
def Theorem7Claim : Prop := ∀ I : Set (LHist ℕ), ClassP I → ¬ Accepts I sigma2a

end Podc.OptimismConcurrency
