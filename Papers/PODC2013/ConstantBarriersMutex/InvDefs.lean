import Papers.PODC2013.ConstantBarriersMutex.Basic

/-!
# The inductive invariant (definitions)

The invariant is the TSO version of Lemma 2 of the paper: every condition that the paper states
in terms of program counters is restated in terms of *performed* writes (memory) and the contents
of the store buffers.

* `LI s q` — local invariant of `q` by program counter: the contents of `q`'s store buffer and
  the memory values of `apply[q]` and `lock`.
* `HC s q` — facts about the candidates / dequeued process held in `q`'s local variables.
* `Inv s` — `LI`, `HC` and global clauses: the owner of `lock` (`lockRole`), uniqueness of the
  process in the critical or exit section (`uniq`, Lemma 2(d)), the meaning of `signal`
  (`sig`, repaired Lemma 2(c)), the promotion queue (`nodup`, `pq`, `inpq`, `q4`), and `exits`
  versus the ghost counter of CS entries (`ex1`–`ex3`).

`lv s` is the *logical* memory: the view of the lock owner, i.e. memory updated by the writes
that the lock owner has issued but not performed. Only the lock owner accesses `promQ`,
`inPromQ` and `exits` (writes), so `lv s` carries their current values.
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

/-- The writes of the doorway of `q` in program order (statements 17, 18, 20). -/
def doorList (q : Proc h) : List (W h) :=
  .signal q false :: .apply q true :: (List.range (h + 1)).reverse.map (fun l => .node (anc q l) q)

/-- Writes the exit section may have pending before statement 43/47. -/
def ExitType (q : Proc h) (w : W h) : Prop :=
  w = .apply q false ∨ w.isExits = true ∨ w.isPromQ = true ∨ ∃ r b, w = .inPromQ r b

/-- The logical memory: the view of the lock owner. -/
def lv (s : Cfg h) : Mem h :=
  match s.mem.lock with
  | some g => s.mem.view (s.buf g)
  | none => s.mem

/-- `g` holds the lock: in the CS or exit section, before its write to `lock` is performed. -/
def Holds (s : Cfg h) (g : Proc h) : Prop :=
  match s.pc g with
  | .cs | .x31 | .x32 | .x34 _ _ _ | .x35 _ _ | .x36 _ _ _ | .x37 _ _ _ | .x38 _ _ _ | .x42 | .x43
  | .x45 | .x46 _ | .x47 _ => True
  | .x48 nx => .lock (some nx) ∈ s.buf g
  | .x50 o => .lock o ∈ s.buf g
  | _ => False

/-- `g` has performed `lock ← nx` but not yet `signal[nx] ← true`. -/
def Hands (s : Cfg h) (g nx : Proc h) : Prop :=
  (s.pc g = .x48 nx ∧ s.buf g = []) ∨ (s.pc g = .x50 (some nx) ∧ s.buf g = [.signal nx true])

/-- Pending writes of the exit section before statement 43/47. -/
def XB (s : Cfg h) (q : Proc h) (B : List (W h)) : Prop :=
  (∀ w ∈ B, ExitType q w) ∧ (s.mem.apply q = true ↔ .apply q false ∈ B) ∧ .apply q false ∉ B.tail

/-- Local invariant of the doorway: `k` writes issued, `i` of them performed. -/
def DoorLI (s : Cfg h) (q : Proc h) (k : ℕ) : Prop :=
  ∃ i ≤ k, s.buf q = ((doorList q).take k).drop i ∧ (s.mem.apply q = true ↔ 2 ≤ i) ∧
    (i = 1 → s.mem.signal q = false)

/-- Local invariant of process `q`, by program counter. -/
def LI (s : Cfg h) (q : Proc h) : Prop :=
  match s.pc q with
  | .rem => s.buf q = [] ∧ s.mem.apply q = false
  | .e18 => DoorLI s q 1
  | .e19 l => l ≤ h ∧ DoorLI s q (2 + (h - l))
  | .e22 => DoorLI s q (h + 3)
  | .e23 | .e24 | .e25a _ | .e25b _ | .e26 | .e27 => s.buf q = [] ∧ s.mem.apply q = true
  | .cs | .x31 => s.buf q = [] ∧ s.mem.apply q = true ∧ s.mem.lock = some q
  | .x32 => s.mem.lock = some q ∧
      ((s.buf q = [.apply q false] ∧ s.mem.apply q = true) ∨
       (s.buf q = [] ∧ s.mem.apply q = false))
  | .x34 _ _ acc => s.mem.lock = some q ∧ XB s q (s.buf q) ∧ q ∉ acc
  | .x35 _ cands => s.mem.lock = some q ∧ XB s q (s.buf q) ∧ q ∉ cands
  | .x36 _ c rest | .x37 _ c rest | .x38 _ c rest =>
      s.mem.lock = some q ∧ XB s q (s.buf q) ∧ q ∉ rest ∧ c ≠ q
  | .x42 | .x43 | .x45 => s.mem.lock = some q ∧ XB s q (s.buf q)
  | .x46 nx | .x47 nx => s.mem.lock = some q ∧ XB s q (s.buf q) ∧ nx ≠ q
  | .x48 nx => nx ≠ q ∧
      ((∃ B, s.buf q = B ++ [.lock (some nx)] ∧ XB s q B ∧ s.mem.lock = some q) ∨
       (s.buf q = [] ∧ s.mem.lock = some nx ∧ s.mem.apply q = false ∧ s.mem.signal nx = false))
  | .x50 none =>
      (∃ B, s.buf q = B ++ [.lock none] ∧ XB s q B ∧ s.mem.lock = some q) ∨
      (s.buf q = [] ∧ s.mem.apply q = false)
  | .x50 (some nx) => nx ≠ q ∧
      ((∃ B, s.buf q = B ++ [.lock (some nx), .signal nx true] ∧ XB s q B ∧
          s.mem.lock = some q) ∨
       (s.buf q = [.signal nx true] ∧ s.mem.lock = some nx ∧ s.mem.apply q = false ∧
          s.mem.signal nx = false) ∨
       (s.buf q = [] ∧ s.mem.apply q = false))

/-- The process `nx` about to be (or just) handed the lock. -/
def NxOK (s : Cfg h) (nx : Proc h) : Prop :=
  (s.pc nx).Entry ∧ s.mem.apply nx = true ∧ nx ∉ (lv s).promQ ∧ (lv s).inPromQ nx = false

/-- Facts about the processes named in the local variables of `q`. -/
def HC (s : Cfg h) (q : Proc h) : Prop :=
  match s.pc q with
  | .x36 _ c _ => (s.pc c).Entry ∧ s.mem.apply c = true
  | .x37 _ c _ => (s.pc c).Entry ∧ s.mem.apply c = true ∧ c ∉ (lv s).promQ ∧
      (lv s).inPromQ c = false
  | .x38 _ c _ => c ∈ (lv s).promQ
  | .x43 => (lv s).promQ = []
  | .x45 => (lv s).promQ ≠ []
  | .x46 nx => (s.pc nx).Entry ∧ s.mem.apply nx = true ∧ nx ∉ (lv s).promQ
  | .x47 nx | .x48 nx => NxOK s nx
  | .x50 none => s.buf q ≠ [] → (lv s).promQ = []
  | .x50 (some nx) => s.buf q ≠ [] → NxOK s nx
  | _ => True

/-- The inductive invariant. -/
structure Inv (s : Cfg h) : Prop where
  loc : ∀ q, LI s q
  hc : ∀ q, HC s q
  lockRole : ∀ g, s.mem.lock = some g → Holds s g ∨
    ((s.pc g).Entry ∧ s.mem.apply g = true ∧ (s.mem.signal g = true ∨ ∃ g', Hands s g' g))
  uniq : ∀ g₁ g₂, s.InCSX g₁ → s.InCSX g₂ → g₁ = g₂
  sig : ∀ q, s.mem.signal q = true → (s.pc q).Entry → s.mem.apply q = true →
    s.mem.lock = some q ∧ ∀ g, ¬ Hands s g q
  nodup : (lv s).promQ.Nodup
  pq : ∀ q ∈ (lv s).promQ, (s.pc q).Entry ∧ s.mem.apply q = true ∧ s.mem.lock ≠ some q
  inpq : ∀ q, (lv s).inPromQ q = true ↔
    ((q ∈ (lv s).promQ ∧ ∀ g l rest, s.pc g ≠ .x38 l q rest) ∨ ∃ g, s.pc g = .x46 q)
  q4 : s.mem.lock = none → s.mem.promQ = []
  ex1 : ∀ g, (s.pc g = .cs ∨ s.pc g = .x31 ∨ s.pc g = .x32) → s.ent = s.mem.exits + 1
  ex2 : ∀ g v, .exits v ∈ s.buf g → v = s.mem.exits + 1 ∧ s.ent = v
  ex3 : (∀ g, s.pc g ≠ .cs ∧ s.pc g ≠ .x31 ∧ s.pc g ≠ .x32 ∧ ∀ v, .exits v ∉ s.buf g) →
    s.ent = s.mem.exits
  ex4 : ∀ g, (s.buf g).countP (fun w => w.isExits) ≤ 1

end Podc.ConstantBarriersMutex
