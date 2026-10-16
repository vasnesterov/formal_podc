import Papers.PODC2011.TimestampSpace.Defs

/-!
# Algorithms 3 and 4 (Section 6): the model

The upper bound of Helmi, Higham, Pacheco, Woelfel (PODC 2011, Section 6): timestamps are pairs
`(rnd, turn) ∈ ℕ × ℕ`, `compare` (Algorithm 3) is the lexicographic order and accesses no shared
memory, `getTS` is Algorithm 4.

**Memory.** The paper treats the `scan` of line 13 as atomic ("Since scan is linearizable, we
treat it as atomic"). A CSLib `Impl` accesses one base object per step, so the whole register
array `R[1], R[2], …` (unbounded; `R[0]` is never accessed) is *one* base object `memObj P` with
three primitives:
* `read i` (returns the view of `R[i]` only),
* `write i v` (writes `R[i]`),
* `scan k` (atomic snapshot of `R[1..k]`; Algorithm 4 only uses `r[1..myrnd+1]` of its scan,
  so it scans exactly these registers).
`MOp.idx` is the largest register index a primitive touches; the space bound says that all
accesses have index `≤ ⌈2√M⌉`.

**Register contents.** `⊥` (`none`) or `⟨seq, rnd⟩` (`Val`), `seq` a list of getTS-ids. The
getTS-id of an operation of process `p` is `(p, c)` where `c` is the number of operations `p`
completed before (i.e. its CSLib `OpId`); processes count their operations in their local state
(`Loc.cnt`).

**Program.** One base-object access per local state (`PC`):
* `wh j v` — line 1 (while loop): read `R[j]`; `v` is the value read from `R[j-1]` (= `r[j-1]`;
  the paper's line 2 copies it, we do not re-read). When `R[j] = ⊥`: `myrnd = j - 1`.
* `loop k i v s` — iteration `i` of the for loop (line 5), `myrnd = k`, `r[myrnd] = v`, at line
  `s`: `s6` reads `R[k+1]`, `s7` reads `R[i]` and compares `r[k].seq[i]` with `last(R[i].seq)`,
  `s8` writes `R[i]` and returns `(k, i)`, `s10` reads `R[i]` again (line 10 is a separate read,
  as in the paper's proof of Claim 6.13), `s11` writes `R[i]`.
* `scan k` — line 13–14, `fin k w` — line 15 (`w = ⟨last(r[1].seq), …, last(r[k].seq), id⟩`),
  `done r` — about to return `r`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp.Alg4

open Cslib.SharedMemory

variable {P : Type}

/-- Non-`⊥` register contents `⟨seq, rnd⟩`. -/
structure Val (P : Type) where
  /-- Sequence of getTS-ids. -/
  seq : List (P × ℕ)
  /-- Round number. -/
  rnd : ℕ

/-- The register array (`none` = `⊥`). -/
abbrev Mem (P : Type) := ℕ → Option (Val P)

/-- `last(x.seq)` (`none` for `⊥`). -/
def lastId (x : Option (Val P)) : Option (P × ℕ) := x.bind fun v => v.seq.getLast?

/-- `x.seq[j]` (1-based; `none` for `⊥` or out of range). -/
def seqAt (x : Option (Val P)) (j : ℕ) : Option (P × ℕ) := x.bind fun v => v.seq[j - 1]?

/-- `x.rnd` (`0` for `⊥`). -/
def rndOf (x : Option (Val P)) : ℕ :=
  match x with
  | some v => v.rnd
  | none => 0

/-- Primitives on the register array. -/
inductive MOp (P : Type) where
  /-- Read `R[i]`. -/
  | read (i : ℕ)
  /-- Write `v` to `R[i]`. -/
  | write (i : ℕ) (v : Val P)
  /-- Atomic snapshot of `R[1..k]`. -/
  | scan (k : ℕ)

/-- The largest register index touched by a primitive. -/
def MOp.idx : MOp P → ℕ
  | .read i => i
  | .write i _ => i
  | .scan k => k

/-- The view of the registers `R[lo..hi]` (everything else hidden). -/
def view (R : Mem P) (lo hi : ℕ) : Mem P := fun j => if lo ≤ j ∧ j ≤ hi then R j else none

/-- The register array as a single base object. -/
abbrev memObj (P : Type) : ObjSpec where
  State := Mem P
  Op := MOp P
  Resp := Mem P
  init := fun _ => none
  δ R o := match o with
    | .read i => (R, view R i i)
    | .write i v => (Function.update R i (some v), fun _ => none)
    | .scan k => (R, view R 1 k)

/-- Algorithm 3: lexicographic comparison of timestamps. -/
def lexLt (a b : ℕ × ℕ) : Bool := decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2))

/-- The line of the for loop a process is at. -/
inductive Stg where
  | s6 | s7 | s8 | s10 | s11
  deriving DecidableEq

/-- Program counters (with the relevant local variables). -/
inductive PC (P : Type) where
  | idle
  | done (r : (ℕ × ℕ) ⊕ Bool)
  | wh (j : ℕ) (v : Option (Val P))
  | loop (k i : ℕ) (v : Option (Val P)) (s : Stg)
  | scan (k : ℕ)
  | fin (k : ℕ) (w : Val P)

/-- Local state: number of completed operations and program counter. -/
structure Loc (P : Type) where
  /-- Number of operations completed so far (the current getTS-id is `(p, cnt)`). -/
  cnt : ℕ
  /-- Program counter. -/
  pc : PC P

/-- After iteration `i` of the for loop: next iteration or the scan. -/
def nextIt (k i : ℕ) (v : Option (Val P)) : PC P :=
  if i + 2 ≤ k then .loop k (i + 1) v .s6 else .scan k

/-- End of the while loop at `R[j] = ⊥`, `myrnd = j - 1`. -/
def endWh (j : ℕ) (v : Option (Val P)) : PC P :=
  if 3 ≤ j then .loop (j - 1) 1 v .s6 else .scan (j - 1)

/-- Line 15: `⟨last(r[1].seq), …, last(r[k].seq), id⟩` (the default `id` is never used: all
`r[1..k]` are non-`⊥`). -/
def newSeq (r : Mem P) (k : ℕ) (id : P × ℕ) : List (P × ℕ) :=
  (List.range k).map (fun j => (lastId (r (j + 1))).getD id) ++ [id]

variable [DecidableEq P]

/-- The base objects: a single register array. -/
abbrev BB (P : Type) : Unit → ObjSpec := fun _ => memObj P

/-- The high-level object. -/
abbrev TS := tsObj (ℕ × ℕ)

/-- Actions of Algorithm 4 (and Algorithm 3). -/
def act (p : P) (l : Loc P) : Action TS (BB P) (Loc P) :=
  match l.pc with
  | .idle => .ret (.inr false) l
  | .done r => .ret r ⟨l.cnt + 1, .idle⟩
  | .wh j v => .access () (MOp.read j) fun r =>
      match r j with
      | some x => ⟨l.cnt, .wh (j + 1) (some x)⟩
      | none => ⟨l.cnt, endWh j v⟩
  | .loop k i v .s6 => .access () (MOp.read (k + 1)) fun r =>
      match r (k + 1) with
      | none => ⟨l.cnt, .loop k i v .s7⟩
      | some _ => ⟨l.cnt, .done (.inl (k + 1, 0))⟩
  | .loop k i v .s7 => .access () (MOp.read i) fun r =>
      ⟨l.cnt, if seqAt v i = lastId (r i) then .loop k i v .s8 else .loop k i v .s10⟩
  | .loop k i _ .s8 => .access () (MOp.write i ⟨[(p, l.cnt)], k⟩) fun _ =>
      ⟨l.cnt, .done (.inl (k, i))⟩
  | .loop k i v .s10 => .access () (MOp.read i) fun r =>
      ⟨l.cnt, if rndOf (r i) < k then .loop k i v .s11 else nextIt k i v⟩
  | .loop k i v .s11 => .access () (MOp.write i ⟨[(p, l.cnt)], k⟩) fun _ =>
      ⟨l.cnt, nextIt k i v⟩
  | .scan k => .access () (MOp.scan (k + 1)) fun r =>
      match r (k + 1) with
      | none => ⟨l.cnt, .fin k ⟨newSeq r k (p, l.cnt), k + 1⟩⟩
      | some _ => ⟨l.cnt, .done (.inl (k + 1, 0))⟩
  | .fin k w => .access () (MOp.write (k + 1) w) fun _ => ⟨l.cnt, .done (.inl (k + 1, 0))⟩

/-- Algorithms 3 and 4 as a CSLib implementation (unbounded register array; the space bound
is a theorem about the indices actually accessed). -/
def alg4 : Impl TS (BB P) P (Loc P) where
  memInit _ := fun _ => none
  locInit _ := ⟨0, .idle⟩
  invoke _ l o := match o with
    | .getTS => ⟨l.cnt, .wh 1 none⟩
    | .compare a b => ⟨l.cnt, .done (.inr (lexLt a b))⟩
  act := act

/-- Configurations. -/
abbrev ACfg (P : Type) := Config TS (BB P) P (Loc P)

/-- The register array of a configuration. -/
abbrev Rg (C : ACfg P) : Mem P := C.mem ()

/-- The effect of a base-object access of `p` in local state `l` with memory `R`. -/
def eff (p : P) (l : Loc P) (R : Mem P) : Loc P × Mem P :=
  match act p l with
  | .access _ o k => (k ((memObj P).δ R o).2, ((memObj P).δ R o).1)
  | .ret _ _ => (l, R)

/-- Local states at which the next step is a base-object access. -/
def PC.isAcc : PC P → Prop
  | .idle => False
  | .done _ => False
  | _ => True

/-- Number of `getTS` invocations in an execution (all processes). -/
def totalGetTS (α : List (Label P TS)) : ℕ :=
  α.countP fun ℓ => match ℓ with
    | .inv _ .getTS => true
    | _ => false

/-! ### Step lemmas -/

section Steps

variable {C C' : ACfg P} {p : P}

lemma step_inv' {o : TSOp (ℕ × ℕ)} (h : (alg4 (P := P)).step C (.inv p o) = some C') :
    C.pend p = none ∧ C'.pend = Function.update C.pend p (some o) ∧
      C'.loc = Function.update C.loc p ((alg4 (P := P)).invoke p (C.loc p) o) ∧
      C'.mem = C.mem := by
  obtain ⟨h1, -, h2, h3, h4⟩ := Impl.step_inv h
  exact ⟨h1, h2, h3, h4⟩

lemma step_tau' (h : (alg4 (P := P)).step C (.tau p) = some C') :
    C.pend p ≠ none ∧ (C.loc p).pc.isAcc ∧ C'.pend = C.pend ∧
      C'.loc = Function.update C.loc p (eff p (C.loc p) (Rg C)).1 ∧
      Rg C' = (eff p (C.loc p) (Rg C)).2 := by
  obtain ⟨h1, h2, i, o, k, hact, h3, h4⟩ := Impl.step_tau h
  refine ⟨h1, ?_, h2, ?_, ?_⟩
  · change act p (C.loc p) = _ at hact
    unfold act at hact
    cases hpc : (C.loc p).pc with
    | idle => simp [hpc] at hact
    | done r => simp [hpc] at hact
    | _ => simp [PC.isAcc]
  · rw [h4]; change act p (C.loc p) = _ at hact
    simp only [eff, hact]
  · cases i
    simp only [Rg, h3, Function.update_self]
    change act p (C.loc p) = _ at hact
    simp only [eff, hact]

lemma step_ret' {r : (ℕ × ℕ) ⊕ Bool} (h : (alg4 (P := P)).step C (.ret p r) = some C') :
    C.pend p ≠ none ∧ C'.pend = Function.update C.pend p none ∧ C'.mem = C.mem ∧
      (((C.loc p).pc = .done r ∧
        C'.loc = Function.update C.loc p ⟨(C.loc p).cnt + 1, .idle⟩) ∨
       ((C.loc p).pc = .idle)) := by
  obtain ⟨h1, h2, h3, l, hact, h4⟩ := Impl.step_ret h
  refine ⟨h1, h2, h3, ?_⟩
  change act p (C.loc p) = _ at hact
  unfold act at hact
  cases hpc : (C.loc p).pc with
  | idle => exact Or.inr rfl
  | done r' =>
    simp only [hpc, Action.ret.injEq] at hact
    obtain ⟨rfl, rfl⟩ := hact
    exact Or.inl ⟨rfl, h4⟩
  | wh j v => simp [hpc] at hact
  | loop k i v s => cases s <;> simp [hpc] at hact
  | scan k => simp [hpc] at hact
  | fin k w => simp [hpc] at hact

end Steps

/-! ### Effects of accesses, per program counter -/

section Eff

variable (p : P) (c : ℕ) (R : Mem P)

lemma eff_wh_some {j : ℕ} {v : Option (Val P)} {x : Val P} (h : R j = some x) :
    eff p ⟨c, .wh j v⟩ R = (⟨c, .wh (j + 1) (some x)⟩, R) := by
  simp [eff, act, view, h]

lemma eff_wh_none {j : ℕ} {v : Option (Val P)} (h : R j = none) :
    eff p ⟨c, .wh j v⟩ R = (⟨c, endWh j v⟩, R) := by
  simp [eff, act, view, h]

lemma eff_s6_none {k i : ℕ} {v : Option (Val P)} (h : R (k + 1) = none) :
    eff p ⟨c, .loop k i v .s6⟩ R = (⟨c, .loop k i v .s7⟩, R) := by
  simp [eff, act, view, h]

lemma eff_s6_some {k i : ℕ} {v : Option (Val P)} {x : Val P} (h : R (k + 1) = some x) :
    eff p ⟨c, .loop k i v .s6⟩ R = (⟨c, .done (.inl (k + 1, 0))⟩, R) := by
  simp [eff, act, view, h]

lemma eff_s7 {k i : ℕ} {v : Option (Val P)} :
    eff p ⟨c, .loop k i v .s7⟩ R =
      (⟨c, if seqAt v i = lastId (R i) then .loop k i v .s8 else .loop k i v .s10⟩, R) := by
  simp [eff, act, view]

lemma eff_s8 {k i : ℕ} {v : Option (Val P)} :
    eff p ⟨c, .loop k i v .s8⟩ R =
      (⟨c, .done (.inl (k, i))⟩, Function.update R i (some ⟨[(p, c)], k⟩)) := by
  simp [eff, act]

lemma eff_s10 {k i : ℕ} {v : Option (Val P)} :
    eff p ⟨c, .loop k i v .s10⟩ R =
      (⟨c, if rndOf (R i) < k then .loop k i v .s11 else nextIt k i v⟩, R) := by
  simp [eff, act, view]

lemma eff_s11 {k i : ℕ} {v : Option (Val P)} :
    eff p ⟨c, .loop k i v .s11⟩ R =
      (⟨c, nextIt k i v⟩, Function.update R i (some ⟨[(p, c)], k⟩)) := by
  simp [eff, act]

lemma eff_scan_none {k : ℕ} (h : R (k + 1) = none) :
    eff p ⟨c, .scan k⟩ R = (⟨c, .fin k ⟨newSeq R k (p, c), k + 1⟩⟩, R) := by
  have hv : newSeq (view R 1 (k + 1)) k (p, c) = newSeq R k (p, c) := by
    simp only [newSeq, view]
    congr 1
    apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    simp only [show 1 ≤ j + 1 ∧ j + 1 ≤ k + 1 from ⟨by omega, by omega⟩, and_self, ite_true]
  simp [eff, act, view, h, hv]

lemma eff_scan_some {k : ℕ} {x : Val P} (h : R (k + 1) = some x) :
    eff p ⟨c, .scan k⟩ R = (⟨c, .done (.inl (k + 1, 0))⟩, R) := by
  simp [eff, act, view, h]

lemma eff_fin {k : ℕ} {w : Val P} :
    eff p ⟨c, .fin k w⟩ R = (⟨c, .done (.inl (k + 1, 0))⟩, Function.update R (k + 1) (some w)) := by
  simp [eff, act]

end Eff

/-! ### Ghost state

Updated deterministically along a run (`gstep`, `ghostOf`). Times are step numbers (`t` = number
of labels so far; the step being taken has time `t + 1`).
* `wt j` / `bt j` — time of the last / first write to `R[j]` (`0` if never written);
* `rsc j` — scan time of the line-15 value in `R[j]`; `psc p` — scan time of the line-15 value
  `p` holds (`r[myrnd]` or its own value at line 15);
* `ph` — current phase `Φ` (phase `ϕ ≥ 1` starts at the first scan by a `getTS` with
  `myrnd = ϕ - 1`), `pst` — its start time, `wc` — registers written in the current phase;
* `ninv` — number of invalidation writes (first write to a register within a phase);
* `cr` — available credits `(id, b)` of getTS ids (`b = true`: the "last write" credit,
  `b = false`: the "first invalidation write" credit), cf. the charging of Claim 6.13;
* `free j` — `R[j]` holds a last write of its writer that is not an invalidation write and whose
  credit has not been used yet;
* `nget` — number of `getTS` invocations.
-/

/-- Ghost state. -/
structure Gh (P : Type) where
  t : ℕ
  wt : ℕ → ℕ
  bt : ℕ → ℕ
  rsc : ℕ → ℕ
  psc : P → ℕ
  ph : ℕ
  pst : ℕ
  wc : Finset ℕ
  ninv : ℕ
  cr : Finset ((P × ℕ) × Bool)
  free : ℕ → Bool
  nget : ℕ

/-- Initial ghost state. -/
def Gh.init : Gh P :=
  ⟨0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, 0, 0, ∅, 0, ∅, fun _ => false, 0⟩

/-- Credits after a write of `id` to `R[j]`: an invalidation write uses the writer's last-write
credit (if the write is the writer's last one, `dead`), else its first-invalidation credit (if
still available), else the last-write credit of the writer of the overwritten value. -/
def crAfter (cr : Finset ((P × ℕ) × Bool)) (old : Option (Val P)) (id : P × ℕ) (inval dead : Bool) :
    Finset ((P × ℕ) × Bool) :=
  if inval then
    (if dead then cr.erase (id, true)
     else if (id, false) ∈ cr then cr.erase (id, false)
     else match lastId old with
       | some x => cr.erase (x, true)
       | none => cr)
  else cr

/-- Ghost update for a write of `id` to `R[j]` (`dead`: the writer will not write again; `sc`:
scan time of a line-15 value). -/
def gwrite (G : Gh P) (R : Mem P) (id : P × ℕ) (j : ℕ) (dead : Bool) (sc : Option ℕ) : Gh P :=
  let inval := decide (j ∉ G.wc)
  { G with
    t := G.t + 1
    wt := Function.update G.wt j (G.t + 1)
    bt := if (R j).isNone then Function.update G.bt j (G.t + 1) else G.bt
    rsc := match sc with
      | some s => Function.update G.rsc j s
      | none => G.rsc
    wc := insert j G.wc
    ninv := if inval then G.ninv + 1 else G.ninv
    cr := crAfter G.cr (R j) id inval dead
    free := Function.update G.free j (!inval && dead) }

/-- Ghost update along a step from configuration `C`. -/
def gstep (G : Gh P) (C : ACfg P) : Label P TS → Gh P
  | .inv p o => match o with
    | .getTS =>
      { G with
        t := G.t + 1
        nget := G.nget + 1
        cr := insert ((p, (C.loc p).cnt), true) (insert ((p, (C.loc p).cnt), false) G.cr) }
    | .compare _ _ => { G with t := G.t + 1 }
  | .ret _ _ => { G with t := G.t + 1 }
  | .tau p =>
    match (C.loc p).pc with
    | .wh j _ => match Rg C j with
      | some _ => { G with t := G.t + 1, psc := Function.update G.psc p (G.rsc j) }
      | none => { G with t := G.t + 1 }
    | .loop _ i _ .s8 => gwrite G (Rg C) (p, (C.loc p).cnt) i true none
    | .loop k i _ .s11 => gwrite G (Rg C) (p, (C.loc p).cnt) i (Rg C (k + 1)).isSome none
    | .scan k =>
      if G.ph ≤ k then
        { G with
          t := G.t + 1
          psc := Function.update G.psc p (G.t + 1)
          ph := k + 1
          pst := G.t + 1
          wc := ∅
          cr := G.cr.erase ((p, (C.loc p).cnt), false) }
      else { G with t := G.t + 1, psc := Function.update G.psc p (G.t + 1) }
    | .fin k _ => gwrite G (Rg C) (p, (C.loc p).cnt) (k + 1) true (some (G.psc p))
    | _ => { G with t := G.t + 1 }

/-- One step of the (configuration, ghost) fold. -/
noncomputable def gfold (X : ACfg P × Gh P) (ℓ : Label P TS) : ACfg P × Gh P :=
  match (alg4 (P := P)).step X.1 ℓ with
  | some C' => (C', gstep X.2 X.1 ℓ)
  | none => X

/-- The ghost state after an execution. -/
noncomputable def ghostOf (α : List (Label P TS)) : Gh P :=
  (α.foldl gfold ((alg4 (P := P)).initCfg, Gh.init)).2

lemma foldl_gfold_fst {α : List (Label P TS)} {C : ACfg P} (h : (alg4 (P := P)).run α = some C) :
    (α.foldl gfold ((alg4 (P := P)).initCfg, Gh.init)).1 = C := by
  induction α using List.reverseRecOn generalizing C with
  | nil => simpa [Impl.run] using h
  | append_singleton α ℓ ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases hα : (alg4 (P := P)).runFrom (alg4 (P := P)).initCfg α with
    | none => simp [hα] at h
    | some C₀ =>
      simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have := ih hα
      generalize List.foldl gfold ((alg4 (P := P)).initCfg, Gh.init) α = X at this ⊢
      obtain ⟨C₁, g⟩ := X
      simp only at this; subst this
      simp [gfold, h]

lemma ghostOf_append {α : List (Label P TS)} {ℓ : Label P TS} {C C' : ACfg P}
    (h : (alg4 (P := P)).run α = some C) (hs : (alg4 (P := P)).step C ℓ = some C') :
    ghostOf (α ++ [ℓ]) = gstep (ghostOf α) C ℓ := by
  have hX := foldl_gfold_fst h
  unfold ghostOf
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  generalize List.foldl gfold ((alg4 (P := P)).initCfg, Gh.init) α = X at hX ⊢
  obtain ⟨C₀, g₀⟩ := X
  simp only at hX
  subst hX
  simp [gfold, hs]

lemma run_append_singleton {α : List (Label P TS)} {ℓ : Label P TS} {C' : ACfg P}
    (h : (alg4 (P := P)).run (α ++ [ℓ]) = some C') :
    ∃ C, (alg4 (P := P)).run α = some C ∧ (alg4 (P := P)).step C ℓ = some C' := by
  rw [Impl.run, Impl.runFrom_append] at h
  cases hα : (alg4 (P := P)).runFrom (alg4 (P := P)).initCfg α with
  | none => simp [hα] at h
  | some C₀ =>
    simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
    exact ⟨C₀, hα, h⟩

end Cslib.SharedMemory.Timestamp.Alg4
