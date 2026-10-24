import Papers.PODC2017.RegisterEmulationSpace.Runs

/-!
# Algorithm 2 (Section 3.3, Appendix D): the upper bound

Base registers store pairs `(timestamp, value)`, initially `(0, v₀)`. Every client `c` has a *write
set* `R c` of registers (the paper's `R_j`, `j = ⌊i/z⌋`; `R c = ∅` for clients that never write).

* `collect()`: trigger a read on every register (in parallel — the paper scans the registers of a
  server sequentially, which only delays responses) and wait until every register of some `n - f`
  servers has responded; the result is the pair with the highest timestamp read.
* `write(v)`: collect, take `ts := max + 1`; registers of `R c` that still have a pending write of
  `c` (from earlier writes) form `coverSet`; trigger `write(ts, v)` on all other registers of `R c`
  and wait until `|wrSet| ≥ |R c| - f`. When a pending write on a register `b ∈ coverSet` responds,
  `b` is removed from `coverSet` and rewritten with the *current* `(ts, v)` (lines 29–34), also
  after the write has returned.
* `read()`: collect and return the value of the highest timestamp.

Local state (`Loc`): `ts, val` (`tsVal`); `pw` = registers with a pending write of the client
(a ghost-free mirror of the pending low-level writes); `cov` (`coverSet`); `wr` (`wrSet`); `q` =
registers to be (re)written with the current `tsVal` (a write is triggered only in a step, so the
re-trigger of line 32 and the triggers of line 10 are queued here); the mode; and the state of the
current collect (`rq` = registers not yet read, `got` = registers that responded, `best` = maximum
read so far).
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace.Alg2

open Finset

/-- Modes of a client. -/
inductive Mode (V : Type*) where
  /-- no pending high-level operation -/
  | idle
  /-- collecting for a read -/
  | rd
  /-- collecting for a write of `v` -/
  | wc (v : V)
  /-- writing phase of a write (lines 6–11) -/
  | wp

/-- Local state of a client. -/
structure Loc (B V : Type*) where
  /-- `tsVal.ts` -/
  ts : ℕ
  /-- `tsVal.val` -/
  val : V
  /-- registers with a pending low-level write of this client -/
  pw : Finset B
  /-- `coverSet` -/
  cov : Finset B
  /-- `wrSet` -/
  wr : Finset B
  /-- registers to be (re)written with `tsVal` -/
  q : Finset B
  /-- current phase -/
  mode : Mode V
  /-- registers not yet read in the current collect -/
  rq : Finset B
  /-- registers that responded in the current collect -/
  got : Finset B
  /-- maximum `(ts, val)` read in the current collect -/
  best : ℕ × V

variable {C B S V : Type*} [DecidableEq C] [LinearOrder B] [Fintype B] [Fintype S] [DecidableEq S]

/-- The smallest element of a finite set, if any. -/
def pick (s : Finset B) : Option B := if h : s.Nonempty then some (s.min' h) else none

lemma pick_mem {s : Finset B} {b : B} (h : pick s = some b) : b ∈ s := by
  unfold pick at h; split at h
  · cases h; exact min'_mem _ _
  · cases h

lemma pick_eq_none {s : Finset B} (h : pick s = none) : s = ∅ := by
  unfold pick at h; split at h
  · cases h
  · rename_i h'; exact not_nonempty_iff_eq_empty.1 h'

lemma pick_eq_none_iff {s : Finset B} : pick s = none ↔ s = ∅ := by
  refine ⟨pick_eq_none, ?_⟩
  rintro rfl; simp [pick]

/-- The collect is complete: every register of at least `n - f` servers responded. -/
def Done (δ : B → S) (f : ℕ) (got : Finset B) : Prop :=
  Fintype.card S - f ≤ #(univ.filter fun s => ∀ b, δ b = s → b ∈ got)

instance (δ : B → S) (f : ℕ) (got : Finset B) : Decidable (Done δ f got) := by
  unfold Done; infer_instance

/-- The local state after a step that triggers nothing. -/
def afterQ (δ : B → S) (f : ℕ) (R : Finset B) (l : Loc B V) : Act B (ℕ × V) V × Loc B V :=
  match l.mode with
  | .idle => (.skip, l)
  | .rd =>
    match pick l.rq with
    | some b => (.trig b .read, { l with rq := l.rq.erase b })
    | none => if Done δ f l.got then (.ret l.best.2, { l with mode := .idle }) else (.skip, l)
  | .wc v =>
    match pick l.rq with
    | some b => (.trig b .read, { l with rq := l.rq.erase b })
    | none =>
      if Done δ f l.got then
        (.skip, { l with ts := l.best.1 + 1, val := v, cov := l.pw, wr := ∅, q := R \ l.pw,
                         mode := .wp })
      else (.skip, l)
  | .wp => if #R ≤ #l.wr + f then (.ret l.val, { l with mode := .idle }) else (.skip, l)

/-- Start a collect. -/
def startCollect (v₀ : V) (m : Mode V) (l : Loc B V) : Loc B V :=
  { l with mode := m, rq := univ, got := ∅, best := (0, v₀) }

/-- The mode is a collect (for a read or for a write). -/
def Mode.isColl {V : Type*} : Mode V → Bool
  | .rd => true
  | .wc _ => true
  | _ => false

@[simp] lemma Mode.isColl_rd : (Mode.rd : Mode V).isColl = true := rfl
@[simp] lemma Mode.isColl_wc (v : V) : (Mode.wc v).isColl = true := rfl
@[simp] lemma Mode.isColl_idle : (Mode.idle : Mode V).isColl = false := rfl
@[simp] lemma Mode.isColl_wp : (Mode.wp : Mode V).isColl = false := rfl

/-- Response to a low-level read with value `w`. -/
def recvRead (l : Loc B V) (b : B) (w : ℕ × V) : Loc B V :=
  if l.mode.isColl then
    { l with got := insert b l.got, best := if l.best.1 < w.1 then w else l.best }
  else l

/-- Response to a low-level write on `b` (lines 29–34). -/
def recvWrite (l : Loc B V) (b : B) : Loc B V :=
  if b ∈ l.cov then { l with pw := l.pw.erase b, cov := l.cov.erase b, q := insert b l.q }
  else { l with pw := l.pw.erase b, wr := insert b l.wr }

/-- **Algorithm 2** of the paper, for the write sets `R` (servers `δ`, failure threshold `f`,
initial value `v₀`). -/
def alg (δ : B → S) (f : ℕ) (R : C → Finset B) (v₀ : V) : Alg C B V (ℕ × V) (Loc B V) where
  init c := { ts := 0, val := v₀, pw := ∅, cov := ∅, wr := R c, q := ∅, mode := .idle, rq := ∅,
              got := ∅, best := (0, v₀) }
  winit _ := (0, v₀)
  invoke _ o l :=
    match l.mode with
    | .idle =>
      match o with
      | .read => startCollect v₀ .rd l
      | .write v => startCollect v₀ (.wc v) l
    | _ => l
  act c l :=
    match pick l.q with
    | some b => (.trig b (.write (l.ts, l.val)), { l with q := l.q.erase b, pw := insert b l.pw })
    | none => afterQ δ f (R c) l
  recv _ l p r :=
    match p.op with
    | .read => recvRead l p.reg (r.getD (0, v₀))
    | .write _ => recvWrite l p.reg

end Podc.RegisterEmulationSpace.Alg2
