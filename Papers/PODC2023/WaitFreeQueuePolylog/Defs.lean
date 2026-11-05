import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Potential
import Cslib.Computability.Distributed.SharedMemory.Objects.Queue
import Mathlib.Tactic

/-!
# The unbounded-space queue of Naderibeni and Ruppert (Fig. 4)

The queue is an implementation (`Cslib.SharedMemory.Impl`) of the sequential FIFO queue
`queueObj V` from one base object, the shared memory `memObj V`, whose operations are the
shared-memory accesses of Fig. 4.

**The ordering tree.** A complete binary tree of height `H ≥ 1` in heap numbering: the root
is node `1`, the children of `n` are `2n` (left) and `2n+1` (right), the parent of `n` is
`n / 2`; the leaves are the nodes `2^H, …, 2^(H+1) - 1`, and process `p : Fin np`
(`np ≤ 2^H`) owns the leaf `2^H + p`. (The paper uses height `⌈log₂ p⌉`.)

**Shared memory.** For every node `n`: `head n` (the field `v.head`), the blocks array
`blk n : ℕ → Option (Blk V)` (`none` = `null`), and the only mutable block field `super`,
stored separately as `sup n i : Option ℕ`. All other block fields are written when the block
is created, before it is installed, and never change (Section 4.1).

**Atomicity.** Every access to a *mutable* shared location (a `head` field, an entry of a
`blocks` array, a `super` field) is a separate step. Reads of fields of blocks that are
already installed are reads of immutable data; they are grouped with the preceding step of
the same line (the values read are the same whenever they are read). In particular one step
of `IndexDequeue`, of `FindResponse` (including the search of line 91) and of `GetEnqueue`
(including the binary search of line 114) is one access each.

**Variants.** `Variant.paper` is Fig. 4 as printed: `Append` increments `leaf.head` by a
plain write (line 13), so the `super` field of a leaf block is not set by `Append`, and line 78
reads `v.blocks[…]`. A `null` `super` field read at line 72 is used as `0`.
`Variant.fixed` is the repaired algorithm: line 13 is replaced by `Advance(leaf, h)` (which
sets `leaf.blocks[h].super` and advances `leaf.head`), and line 78 reads the blocks of the left
sibling `v.parent.left.blocks[…]` (as the proof of Lemma 13 says).
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

/-- A block (Fig. 3). One record for all nodes: `endl`/`endr` are used in internal nodes,
`elem` in leaves (`some x` for `Enqueue(x)`, `none` for `Dequeue`), `size` in the root.
The mutable field `super` is kept in `Mem.sup`. -/
structure Blk (V : Type) where
  sumenq : ℕ
  sumdeq : ℕ
  endl : ℕ
  endr : ℕ
  size : ℕ
  elem : Option V

/-- The empty block `B₀` stored in `blocks[0]` of every node (all integer fields `0`). -/
def Blk.zero {V : Type} : Blk V := ⟨0, 0, 0, 0, 0, none⟩

/-- `end_dir` of a block: `endl` for `d = 0` (left), `endr` otherwise. -/
def Blk.endd {V : Type} (B : Blk V) (d : ℕ) : ℕ := if d = 0 then B.endl else B.endr

/-- The shared memory. -/
structure Mem (V : Type) where
  head : ℕ → ℕ
  blk : ℕ → ℕ → Option (Blk V)
  sup : ℕ → ℕ → Option ℕ

variable {V : Type}

/-- Initially `head = 1`, `blocks[0] = B₀` and all other entries and `super` fields are `null`. -/
def initMem : Mem V where
  head _ := 1
  blk _ i := if i = 0 then some Blk.zero else none
  sup _ _ := none

namespace Mem

/-- The block `n.blocks[i]`, reading `null` as `B₀` (only used on installed blocks). -/
def bk (M : Mem V) (n i : ℕ) : Blk V := (M.blk n i).getD Blk.zero

/-- `n.blocks[i] := B`. -/
def setBlk (M : Mem V) (n i : ℕ) (B : Blk V) : Mem V :=
  { M with blk := Function.update M.blk n (Function.update (M.blk n) i (some B)) }

/-- `n.blocks[i].super := x`. -/
def setSup (M : Mem V) (n i x : ℕ) : Mem V :=
  { M with sup := Function.update M.sup n (Function.update (M.sup n) i (some x)) }

/-- `n.head := h`. -/
def setHead (M : Mem V) (n h : ℕ) : Mem V :=
  { M with head := Function.update M.head n h }

end Mem

/-- Variants of the pseudocode: `leafAdv` — `Append` calls `Advance(leaf, h)` instead of the
plain increment of line 13; `sib78` — line 78 reads the left sibling's blocks. -/
structure Variant where
  leafAdv : Bool
  sib78 : Bool

/-- Fig. 4 as printed. -/
def Variant.paper : Variant := ⟨false, false⟩

/-- The repaired algorithm. -/
def Variant.fixed : Variant := ⟨true, true⟩

/-! ### The computations done by the grouped read steps -/

/-- `CreateBlock(v, h)` (lines 40–57), given the value `el + 1` read from `v.left.head` at
line 43; the step reads `v.right.head` (line 44) and then installed blocks. -/
def createBlock (M : Mem V) (v h el : ℕ) : Option (Blk V) :=
  let er := M.head (2 * v + 1) - 1
  let L := M.bk (2 * v) el
  let R := M.bk (2 * v + 1) er
  let Pr := M.bk v (h - 1)
  let se := L.sumenq + R.sumenq
  let sd := L.sumdeq + R.sumdeq
  let numenq := se - Pr.sumenq
  let numdeq := sd - Pr.sumdeq
  let size := if v = 1 then Pr.size + numenq - numdeq else 0
  if numenq + numdeq = 0 then none
  else some ⟨se, sd, el, er, size, none⟩

/-- One level of `IndexDequeue(v, b, i)` for `v ≠ root` (lines 71–80): returns the arguments
`(sup, i)` of the recursive call on `v.parent`. -/
def idxStep (var : Variant) (M : Mem V) (v b i : ℕ) : ℕ × ℕ :=
  let m := v / 2
  let d := v % 2
  let sup0 := (M.sup v b).getD 0
  let sup := if (M.bk m sup0).endd d < b then sup0 + 1 else sup0
  let i1 := i + ((M.bk v (b - 1)).sumdeq - (M.bk v ((M.bk m (sup - 1)).endd d)).sumdeq)
  let sib := if var.sib78 then 2 * m else v
  let i2 := if d = 1 then
      i1 + ((M.bk sib (M.bk m sup).endl).sumdeq - (M.bk sib (M.bk m (sup - 1)).endl).sumdeq)
    else i1
  (sup, i2)

/-- The least `j ∈ [lo, hi]` with `x ≤ f j` (`hi` if there is none). -/
def findFirst (f : ℕ → ℕ) (x lo hi : ℕ) : ℕ :=
  ((List.range' lo (hi + 1 - lo)).find? (fun j => decide (x ≤ f j))).getD hi

/-- `FindResponse(b, i)` (lines 83–96) up to the call of `GetEnqueue`: `none` if the dequeue
is a null dequeue, otherwise `some (bₑ, iₑ)`. -/
def findResp (M : Mem V) (b i : ℕ) : Option (ℕ × ℕ) :=
  let B := M.bk 1 b
  let Bp := M.bk 1 (b - 1)
  let numenq := B.sumenq - Bp.sumenq
  if Bp.size + numenq < i then none
  else
    let e := i + Bp.sumenq - Bp.size
    let be := findFirst (fun j => (M.bk 1 j).sumenq) e 0 b
    some (be, e - (M.bk 1 (be - 1)).sumenq)

/-- One level of `GetEnqueue(v, b, i)` for an internal node `v` (lines 101–116): returns the
arguments `(child, b', i')` of the recursive call. -/
def getEnqStep (M : Mem V) (v b i : ℕ) : ℕ × ℕ × ℕ :=
  let B := M.bk v b
  let Bp := M.bk v (b - 1)
  let sumleft := (M.bk (2 * v) B.endl).sumenq
  let prevleft := (M.bk (2 * v) Bp.endl).sumenq
  let prevright := (M.bk (2 * v + 1) Bp.endr).sumenq
  let d := if i ≤ sumleft - prevleft then 0 else 1
  let i' := if d = 0 then i else i - (sumleft - prevleft)
  let prev := if d = 0 then prevleft else prevright
  let c := 2 * v + d
  let b' := findFirst (fun j => (M.bk c j).sumenq) (i' + prev) (Bp.endd d + 1) (B.endd d)
  (c, b', i' - ((M.bk c (b' - 1)).sumenq - prev))

/-! ### The memory as a base object -/

/-- Operations on the shared memory. -/
inductive MOp (V : Type) where
  /-- Read `n.head`. -/
  | readHead (n : ℕ)
  /-- Read the (installed) block `n.blocks[i]`. -/
  | readBlk (n i : ℕ)
  /-- Test `n.blocks[i] ≠ null` (line 28). -/
  | testBlk (n i : ℕ)
  /-- `n.blocks[i] := B` (line 12). -/
  | writeBlk (n i : ℕ) (B : Blk V)
  /-- `n.head := h` (line 13 of the printed algorithm). -/
  | writeHead (n h : ℕ)
  /-- `CAS(n.blocks[i], null, B)` (line 35). -/
  | casBlk (n i : ℕ) (B : Blk V)
  /-- `CAS(n.blocks[i].super, null, x)` (line 61). -/
  | casSup (n i x : ℕ)
  /-- `CAS(n.head, h, h+1)` (line 63). -/
  | casHead (n h : ℕ)
  /-- Lines 44–56 of `CreateBlock(v, h)` after line 43 read `v.left.head = el + 1`. -/
  | create (v h el : ℕ)
  /-- One level of `IndexDequeue` (reads `v.blocks[b].super`, then installed blocks). -/
  | idx (var : Variant) (v b i : ℕ)
  /-- `FindResponse(b, i)` up to the call of `GetEnqueue`. -/
  | findResp (b i : ℕ)
  /-- One level of `GetEnqueue` at an internal node. -/
  | getEnq (v b i : ℕ)

/-- Responses of memory operations. -/
inductive MResp (V : Type) where
  | nat (n : ℕ)
  | bool (b : Bool)
  | blk (B : Option (Blk V))
  | pair (a b : ℕ)
  | opair (o : Option (ℕ × ℕ))
  | triple (a b c : ℕ)

/-- The effect of a memory operation. -/
def memδ (M : Mem V) : MOp V → Mem V × MResp V
  | .readHead n => (M, .nat (M.head n))
  | .readBlk n i => (M, .blk (M.blk n i))
  | .testBlk n i => (M, .bool (M.blk n i).isSome)
  | .writeBlk n i B => (M.setBlk n i B, .bool true)
  | .writeHead n h => (M.setHead n h, .bool true)
  | .casBlk n i B =>
    if (M.blk n i).isNone then (M.setBlk n i B, .bool true) else (M, .bool false)
  | .casSup n i x =>
    if (M.sup n i).isNone then (M.setSup n i x, .bool true) else (M, .bool false)
  | .casHead n h =>
    if M.head n = h then (M.setHead n (h + 1), .bool true) else (M, .bool false)
  | .create v h el => (M, .blk (createBlock M v h el))
  | .idx var v b i => let r := idxStep var M v b i; (M, .pair r.1 r.2)
  | .findResp b i => (M, .opair (findResp M b i))
  | .getEnq v b i => let r := getEnqStep M v b i; (M, .triple r.1 r.2.1 r.2.2)

/-- The shared memory as a single base object. -/
def memObj (V : Type) : ObjSpec where
  State := Mem V
  Op := MOp V
  Resp := MResp V
  init := initMem
  δ := memδ

/-! ### Local states -/

/-- Where `Advance` returns to. -/
inductive Ctx where
  /-- `Append` (repaired line 13); continue with `Propagate(leaf.parent)`. -/
  | app
  /-- Line 29 of `Refresh(v)` (`k`-th refresh, `h` read at line 25) for direction `d`. -/
  | ref (v k h d : ℕ)
  /-- Line 36 of `Refresh(v)`; `res` is the result of the CAS of line 35. -/
  | own (v k h : ℕ) (res : Bool)

/-- Program counters (with the local variables that are live there). -/
inductive Pc (V : Type) where
  | idle
  /-- Line 2/6: read `leaf.head`. -/
  | app0
  /-- Line 2/6: read `leaf.blocks[h - 1]` and build the new leaf block. -/
  | app1 (h : ℕ)
  /-- Line 12: `leaf.blocks[h] := B`. -/
  | app2 (h : ℕ) (B : Blk V)
  /-- Line 13 as printed: `leaf.head := h + 1`. -/
  | app3 (h : ℕ)
  /-- Line 60 of `Advance(w, hw)`: read `w.parent.head`. -/
  | adv0 (c : Ctx) (w hw : ℕ)
  /-- Line 61: `CAS(w.blocks[hw].super, null, hp)`. -/
  | adv1 (c : Ctx) (w hw hp : ℕ)
  /-- Line 63: `CAS(w.head, hw, hw + 1)`. -/
  | adv2 (c : Ctx) (w hw : ℕ)
  /-- Line 25 of the `k`-th `Refresh(v)` of `Propagate(v)` (`k ∈ {1, 2}`). -/
  | r25 (v k : ℕ)
  /-- Line 27 (direction `d`). -/
  | r27 (v k h d : ℕ)
  /-- Line 28 (direction `d`, `childHead = ch`). -/
  | r28 (v k h d ch : ℕ)
  /-- Line 43. -/
  | c43 (v k h : ℕ)
  /-- Lines 44–56. -/
  | c44 (v k h el : ℕ)
  /-- Line 35. -/
  | r35 (v k h : ℕ) (B : Blk V)
  /-- `IndexDequeue(v, b, i)` with `v ≠ root`. -/
  | idx (v b i : ℕ)
  /-- `FindResponse(b, i)`. -/
  | fr (b i : ℕ)
  /-- `GetEnqueue(v, b, i)`. -/
  | ge (v b i : ℕ)
  /-- About to return `r`. -/
  | done (r : Option V)

/-- Local state: program counter, the current operation and the index `lh` of its block in
the leaf (set at line 12). -/
structure Loc (V : Type) where
  pc : Pc V
  cur : FifoOp V
  lh : ℕ

section Program

variable (H : ℕ)

/-- Leaves are the nodes `≥ 2^H`. -/
def isLeaf (n : ℕ) : Bool := decide (2 ^ H ≤ n)

/-- Start `Advance(w, hw)` (the root has no `super` fields: lines 59–62 are skipped). -/
def enterAdv (c : Ctx) (w hw : ℕ) : Pc V := if w = 1 then .adv2 c w hw else .adv0 c w hw

/-- After `Propagate` reached the root: an `Enqueue` returns, a `Dequeue` calls
`IndexDequeue(leaf, lh, 1)` (line 8). -/
def afterProp (leaf : ℕ) (l : Loc V) : Pc V :=
  match l.cur with
  | .enq _ => .done none
  | .deq => if leaf = 1 then .fr l.lh 1 else .idx leaf l.lh 1

/-- After the `k`-th `Refresh(v)` returned `res` (lines 17–22). -/
def refDone (leaf : ℕ) (l : Loc V) (v k : ℕ) (res : Bool) : Pc V :=
  if k = 1 ∧ res = false then .r25 v 2
  else if v = 1 then afterProp leaf l else .r25 (v / 2) 1

/-- After `Advance` returned. -/
def afterAdv (leaf : ℕ) (l : Loc V) : Ctx → Pc V
  | .app => .r25 (leaf / 2) 1
  | .ref v k h d => if d = 0 then .r27 v k h 1 else .c43 v k h
  | .own v k _ res => refDone leaf l v k res

/-- The program of process `p` (leaf `2^H + p`) for the variant `var`, one step per access. -/
def act (var : Variant) (p : ℕ) (l : Loc V) : Action (queueObj V) (fun _ : Unit => memObj V) (Loc V) :=
  let leaf := 2 ^ H + p
  let go := fun pc : Pc V => ({ l with pc := pc } : Loc V)
  match l.pc with
  | .idle => .ret none l
  | .done r => .ret r { l with pc := .idle }
  | .app0 => .access () (MOp.readHead leaf) fun r => match r with
      | .nat h => go (.app1 h)
      | _ => l
  | .app1 h => .access () (MOp.readBlk leaf (h - 1)) fun r => match r with
      | .blk (some Bp) =>
        go (.app2 h (match l.cur with
          | .enq x => ⟨Bp.sumenq + 1, Bp.sumdeq, 0, 0, 0, some x⟩
          | .deq => ⟨Bp.sumenq, Bp.sumdeq + 1, 0, 0, 0, none⟩))
      | _ => l
  | .app2 h B => .access () (MOp.writeBlk leaf h B) fun _ =>
      { l with pc := if var.leafAdv then enterAdv .app leaf h else .app3 h, lh := h }
  | .app3 h => .access () (MOp.writeHead leaf (h + 1)) fun _ => go (.r25 (leaf / 2) 1)
  | .adv0 c w hw => .access () (MOp.readHead (w / 2)) fun r => match r with
      | .nat hp => go (.adv1 c w hw hp)
      | _ => l
  | .adv1 c w hw hp => .access () (MOp.casSup w hw hp) fun _ => go (.adv2 c w hw)
  | .adv2 c w hw => .access () (MOp.casHead w hw) fun _ => go (afterAdv leaf l c)
  | .r25 v k => .access () (MOp.readHead v) fun r => match r with
      | .nat h => go (.r27 v k h 0)
      | _ => l
  | .r27 v k h d => .access () (MOp.readHead (2 * v + d)) fun r => match r with
      | .nat ch => go (.r28 v k h d ch)
      | _ => l
  | .r28 v k h d ch => .access () (MOp.testBlk (2 * v + d) ch) fun r => match r with
      | .bool true => go (enterAdv (.ref v k h d) (2 * v + d) ch)
      | _ => go (afterAdv leaf l (.ref v k h d))
  | .c43 v k h => .access () (MOp.readHead (2 * v)) fun r => match r with
      | .nat hl => go (.c44 v k h (hl - 1))
      | _ => l
  | .c44 v k h el => .access () (MOp.create v h el) fun r => match r with
      | .blk (some B) => go (.r35 v k h B)
      | _ => go (refDone leaf l v k true)
  | .r35 v k h B => .access () (MOp.casBlk v h B) fun r => match r with
      | .bool res => go (enterAdv (.own v k h res) v h)
      | _ => l
  | .idx v b i => .access () (MOp.idx var v b i) fun r => match r with
      | .pair s i' => go (if v / 2 = 1 then .fr s i' else .idx (v / 2) s i')
      | _ => l
  | .fr b i => .access () (MOp.findResp b i) fun r => match r with
      | .opair none => go (.done none)
      | .opair (some (be, ie)) => go (.ge 1 be ie)
      | _ => l
  | .ge v b i =>
    if isLeaf H v then .access () (MOp.readBlk v b) fun r => match r with
      | .blk B => go (.done ((B.getD Blk.zero).elem))
      | _ => l
    else .access () (MOp.getEnq v b i) fun r => match r with
      | .triple c b' i' => go (.ge c b' i')
      | _ => l

/-- The queue implementation for processes `Fin np`, tree height `H`, variant `var`. -/
def queueImpl (var : Variant) (np : ℕ) :
    Impl (queueObj V) (fun _ : Unit => memObj V) (Fin np) (Loc V) where
  memInit _ := initMem
  locInit _ := ⟨.idle, .deq, 0⟩
  invoke _ _ o := ⟨.app0, o, 0⟩
  act p l := act H var p l

end Program

end Podc.WaitFreeQueuePolylog
