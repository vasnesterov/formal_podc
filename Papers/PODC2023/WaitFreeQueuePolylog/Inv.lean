import Papers.PODC2023.WaitFreeQueuePolylog.Frame
import Papers.PODC2023.WaitFreeQueuePolylog.Steps

/-!
# The invariant of the repaired algorithm

The temporal arguments of the paper (Lemma 9, the double refresh of Lemma 10, and Lemma 12) are
turned into invariants with the help of ghost variables (`Ghost`), updated alongside the
execution by `gstep` (they never influence the algorithm):

* `pg p` — the numbers of installed blocks in the children of `v` when process `p` executed
  line 25 of its current `Refresh(v)` (its "snapshot"); `ph p` — the value `h` it read there;
  `pg1 p` — the snapshot of its first `Refresh` while it performs the second one;
* `bg n j` — the snapshot of the `Refresh` that installed `n.blocks[j]`;
* `hm n j` — the value of `n.parent.head` when `n.blocks[j]` was installed;
* `hs n j` — the numbers of installed blocks in the children of `n` when `n.head` became `j`.

Lemma 9 becomes "`end_d` of a block is at least the installer's snapshot" (`GInv.bg_le`);
Lemma 10 becomes "a refresh that reads `h` from `v.head` has a snapshot at least `hs v h`", and
`hs` is monotone; Lemma 12 becomes `MInv.l12up` and `GInv.hm_lb`.
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type}

/-- Ghost variables. -/
structure Ghost (np : ℕ) where
  pg : Fin np → ℕ × ℕ
  ph : Fin np → ℕ
  pg1 : Fin np → ℕ × ℕ
  bg : ℕ → ℕ → ℕ × ℕ
  hm : ℕ → ℕ → ℕ
  hs : ℕ → ℕ → ℕ × ℕ

/-- Initial ghost state. -/
def Ghost.init (np : ℕ) : Ghost np := ⟨fun _ => (0, 0), fun _ => 0, fun _ => (0, 0),
  fun _ _ => (0, 0), fun _ _ => 0, fun _ _ => (0, 0)⟩

/-- Component `d` of a pair (`d = 0`: left). -/
def gd (g : ℕ × ℕ) (d : ℕ) : ℕ := if d = 0 then g.1 else g.2

/-- The leaf of process `p`. -/
def leafOf (H : ℕ) {np : ℕ} (p : Fin np) : ℕ := 2 ^ H + p.val

/-- Update a two-argument function at one point. -/
def upd2 {X : Type} (f : ℕ → ℕ → X) (n j : ℕ) (x : X) : ℕ → ℕ → X :=
  Function.update f n (Function.update (f n) j x)

/-- The children counts of `v`. -/
def ccnt (M : Mem V) (v : ℕ) : ℕ × ℕ := (cnt M (2 * v), cnt M (2 * v + 1))

/-- Ghost update for a step of process `p` in local state `l` from memory `M`. -/
def gstepLoc (H : ℕ) {np : ℕ} (M : Mem V) (G : Ghost np) (p : Fin np) (l : Loc V) : Ghost np :=
  match l.pc with
  | .r25 v _ => ⟨Function.update G.pg p (ccnt M v), Function.update G.ph p (M.head v),
      Function.update G.pg1 p (G.pg p), G.bg, G.hm, G.hs⟩
  | .r35 v _ h _ => if (M.blk v h).isNone then
      ⟨G.pg, G.ph, G.pg1, upd2 G.bg v h (G.pg p), upd2 G.hm v h (M.head (v / 2)), G.hs⟩ else G
  | .app2 h _ => ⟨G.pg, G.ph, G.pg1, G.bg, upd2 G.hm (leafOf H p) h (M.head (leafOf H p / 2)),
      G.hs⟩
  | .adv2 _ w hw => if M.head w = hw then
      ⟨G.pg, G.ph, G.pg1, G.bg, G.hm, upd2 G.hs w (hw + 1) (ccnt M w)⟩ else G
  | _ => G

/-- Ghost update along a labelled step from configuration `C`. -/
def gstep (H : ℕ) {np : ℕ} (C : Config (queueObj V) (fun _ : Unit => memObj V) (Fin np) (Loc V))
    (G : Ghost np) : Label (Fin np) (queueObj V) → Ghost np
  | .tau p => gstepLoc H (C.mem ()) G p (C.loc p)
  | _ => G

/-- Memory invariants about the `super` fields (Invariant 3, third claim, and Lemma 12's upper
bound). -/
structure MInv (H : ℕ) (M : Mem V) : Prop where
  supNone : ∀ n i, cnt M n < i → M.sup n i = none
  supSet : ∀ n, 2 ≤ n → ∀ i, 1 ≤ i → i < M.head n → (M.sup n i).isSome
  supBound : ∀ n i s, M.sup n i = some s → s ≤ M.head (n / 2)
  l12up : ∀ n, 2 ≤ n → ∀ b s, 1 ≤ b → M.sup n b = some s → ∀ j, j ≤ cnt M (n / 2) →
    b ≤ endOf M (n / 2) j (n % 2) → s ≤ j

/-- Ghost invariants. -/
structure GInv (H : ℕ) {np : ℕ} (M : Mem V) (G : Ghost np) : Prop where
  bg_le : ∀ n, 1 ≤ n → n < 2 ^ H → ∀ j, 1 ≤ j → j ≤ cnt M n →
    (G.bg n j).1 ≤ (M.bk n j).endl ∧ (G.bg n j).2 ≤ (M.bk n j).endr
  hs_le_bg : ∀ n, 1 ≤ n → n < 2 ^ H → ∀ j, 1 ≤ j → j ≤ cnt M n →
    (G.hs n j).1 ≤ (G.bg n j).1 ∧ (G.hs n j).2 ≤ (G.bg n j).2
  hs_mono : ∀ n, 1 ≤ n → n < 2 ^ H → ∀ j j', 1 ≤ j → j ≤ j' → j' ≤ M.head n →
    (G.hs n j).1 ≤ (G.hs n j').1 ∧ (G.hs n j).2 ≤ (G.hs n j').2
  hs_le_cnt : ∀ n, 1 ≤ n → n < 2 ^ H → ∀ j, j ≤ M.head n →
    (G.hs n j).1 ≤ cnt M (2 * n) ∧ (G.hs n j).2 ≤ cnt M (2 * n + 1)
  hm_le : ∀ n, 2 ≤ n → ∀ b, 1 ≤ b → b ≤ cnt M n →
    G.hm n b ≤ M.head (n / 2) ∧ ∀ s, M.sup n b = some s → G.hm n b ≤ s
  /-- Lemma 12's lower bound (with `bg ≤ end` and `hm ≤ super`). -/
  hm_lb : ∀ n, 2 ≤ n → n < 2 ^ (H + 1) → ∀ b, 1 ≤ b → b ≤ cnt M n → ∀ j, 1 ≤ j →
    j ≤ cnt M (n / 2) → gd (G.bg (n / 2) j) (n % 2) < b → j ≤ G.hm n b

section PInv

variable (H : ℕ) {np : ℕ} (os : List (FifoOp V)) (rs : List (Option V)) (M : Mem V) (G : Ghost np)
  (p : Fin np) (pend : Option (FifoOp V)) (l : Loc V)

/-- The current operation instance of `p`. -/
abbrev xOf : OpId (Fin np) := (p, rs.length)

/-- The new leaf block built at line 2 / 6 from the previous block `Bp`. -/
def newLeafBlk (o : FifoOp V) (Bp : Blk V) : Blk V :=
  match o with
  | .enq x => ⟨Bp.sumenq + 1, Bp.sumdeq, 0, 0, 0, some x⟩
  | .deq => ⟨Bp.sumenq, Bp.sumdeq + 1, 0, 0, 0, none⟩

/-- Pending, before the leaf write. -/
def PreW : Prop :=
  pend = some l.cur ∧ os.length = rs.length + 1 ∧
  cnt M (leafOf H p) = rs.length ∧ M.head (leafOf H p) = cnt M (leafOf H p) + 1

/-- Pending, after the leaf write. -/
def Base : Prop :=
  pend = some l.cur ∧ os.length = rs.length + 1 ∧
  cnt M (leafOf H p) = os.length ∧ l.lh = cnt M (leafOf H p)

/-- `Base` and the leaf's head has been advanced. -/
def BaseH : Prop := Base H os rs M p pend l ∧ M.head (leafOf H p) = cnt M (leafOf H p) + 1

/-- The current operation of `p` is contained in the blocks `1..g` of the child `2v + d`. -/
def InChild (v d g : ℕ) : Prop :=
  xOf rs p ∈ (pre H np M (2 * v + d) g).map Prod.fst

/-- `p` is in the `k`-th `Refresh(v)` after line 25, having read `h`. -/
def RefCtx (v k h : ℕ) : Prop :=
  1 ≤ v ∧ v < 2 ^ H ∧ (k = 1 ∨ k = 2) ∧ 1 ≤ h ∧ h ≤ M.head v ∧ G.ph p = h ∧
  (G.pg p).1 ≤ cnt M (2 * v) ∧ (G.pg p).2 ≤ cnt M (2 * v + 1) ∧
  (G.hs v h).1 ≤ (G.pg p).1 ∧ (G.hs v h).2 ≤ (G.pg p).2 ∧
  (h < M.head v → (G.pg p).1 ≤ (G.hs v (h + 1)).1 ∧ (G.pg p).2 ≤ (G.hs v (h + 1)).2) ∧
  (∃ dc, dc < 2 ∧ InChild H rs M p v dc (gd (G.pg p) dc) ∧
    (k = 2 → InChild H rs M p v dc (gd (G.pg1 p) dc) ∧
      (G.pg1 p).1 ≤ (G.hs v h).1 ∧ (G.pg1 p).2 ≤ (G.hs v h).2)) ∧
  ∀ d, d < 2 → ∀ b, gd (G.pg p) d < b → b ≤ cnt M (2 * v + d) → h ≤ G.hm (2 * v + d) b

/-- The `super` fields of the child blocks `1..e` of `c` are set, and at most `h` while
`v.blocks[h]` is empty (Lemma 12's upper bound for the block about to be installed). -/
def SupUp (c e v h : ℕ) : Prop :=
  ∀ b, 1 ≤ b → b ≤ e → ∃ s, M.sup c b = some s ∧ (M.blk v h = none → s ≤ h)

/-- What a terminated `Refresh` guarantees. -/
def OwnPost (v k : ℕ) (res : Bool) : Prop :=
  (res = true ∨ k = 2) → xOf rs p ∈ (pre H np M v (cnt M v)).map Prod.fst

/-- `p` is in `Propagate(v)` before line 25 of its `k`-th refresh. -/
def PropAt (v k : ℕ) : Prop :=
  1 ≤ v ∧ v < 2 ^ H ∧ (k = 1 ∨ k = 2) ∧
  ∃ dc, dc < 2 ∧ InChild H rs M p v dc (cnt M (2 * v + dc)) ∧
    (k = 2 → InChild H rs M p v dc (gd (G.pg p) dc) ∧ G.ph p < M.head v ∧
      (G.pg p).1 ≤ (G.hs v (G.ph p + 1)).1 ∧ (G.pg p).2 ≤ (G.hs v (G.ph p + 1)).2 ∧
      (G.pg p).1 ≤ cnt M (2 * v) ∧ (G.pg p).2 ≤ cnt M (2 * v + 1))

/-- The current operation is in the root (it is in `L`). -/
def InRoot : Prop := xOf rs p ∈ (pre H np M 1 (cnt M 1)).map Prod.fst

/-- The generic precondition of `Advance(w, hw)`. -/
def AdvOK (w hw : ℕ) : Prop := 1 ≤ w ∧ w < 2 ^ (H + 1) ∧ 1 ≤ hw ∧ hw ≤ cnt M w

/-- The context-specific part of the invariant while in `Advance`. -/
def CtxInv : Ctx → ℕ → ℕ → Prop
  | .app, w, hw => w = leafOf H p ∧ Base H os rs M p pend l ∧ hw = l.lh
  | .ref v k h d, w, hw => RefCtx H rs M G p v k h ∧ BaseH H os rs M p pend l ∧ d < 2 ∧
      w = 2 * v + d ∧ gd (G.pg p) d ≤ hw ∧ (d = 1 → (G.pg p).1 < M.head (2 * v))
  | .own v k h res, w, hw => RefCtx H rs M G p v k h ∧ BaseH H os rs M p pend l ∧ w = v ∧ hw = h ∧
      OwnPost H rs M p v k res

/-- The per-process invariant, by program counter. -/
def PInv : Prop :=
  (∀ j, 1 ≤ j → j ≤ cnt M (leafOf H p) → os[j - 1]? = some (blkOp (M.bk (leafOf H p) j))) ∧
  match l.pc with
  | .idle => pend = none ∧ os.length = rs.length ∧
      cnt M (leafOf H p) = rs.length ∧ M.head (leafOf H p) = cnt M (leafOf H p) + 1
  | .app0 => PreW H os rs M p pend l
  | .app1 h => PreW H os rs M p pend l ∧ h = M.head (leafOf H p)
  | .app2 h B => PreW H os rs M p pend l ∧ h = M.head (leafOf H p) ∧
      B = newLeafBlk l.cur (M.bk (leafOf H p) (h - 1))
  | .app3 _ => False
  | .adv0 c w hw => AdvOK H M w hw ∧ 2 ≤ w ∧ CtxInv H os rs M G p pend l c w hw
  | .adv1 c w hw hp => AdvOK H M w hw ∧ 2 ≤ w ∧ G.hm w hw ≤ hp ∧ hp ≤ M.head (w / 2) ∧
      CtxInv H os rs M G p pend l c w hw
  | .adv2 c w hw => AdvOK H M w hw ∧ (2 ≤ w → (M.sup w hw).isSome) ∧
      CtxInv H os rs M G p pend l c w hw
  | .r25 v k => PropAt H rs M G p v k ∧ BaseH H os rs M p pend l
  | .r27 v k h d => RefCtx H rs M G p v k h ∧ BaseH H os rs M p pend l ∧ d < 2 ∧
      (d = 1 → (G.pg p).1 < M.head (2 * v))
  | .r28 v k h d ch => RefCtx H rs M G p v k h ∧ BaseH H os rs M p pend l ∧ d < 2 ∧
      (d = 1 → (G.pg p).1 < M.head (2 * v)) ∧ gd (G.pg p) d ≤ ch ∧ 1 ≤ ch ∧
      ch ≤ M.head (2 * v + d)
  | .c43 v k h => RefCtx H rs M G p v k h ∧ BaseH H os rs M p pend l ∧
      (G.pg p).1 < M.head (2 * v) ∧ (G.pg p).2 < M.head (2 * v + 1)
  | .c44 v k h el => RefCtx H rs M G p v k h ∧ BaseH H os rs M p pend l ∧ (G.pg p).1 ≤ el ∧
      (M.bk v (h - 1)).endl ≤ el ∧ el < M.head (2 * v) ∧ (G.pg p).2 < M.head (2 * v + 1) ∧
      SupUp M (2 * v) el v h
  | .r35 v k h B => RefCtx H rs M G p v k h ∧ BaseH H os rs M p pend l ∧
      (G.pg p).1 ≤ B.endl ∧ (G.pg p).2 ≤ B.endr ∧
      (M.bk v (h - 1)).endl ≤ B.endl ∧ (M.bk v (h - 1)).endr ≤ B.endr ∧
      B.endl < M.head (2 * v) ∧ B.endr < M.head (2 * v + 1) ∧
      B.sumenq = (M.bk (2 * v) B.endl).sumenq + (M.bk (2 * v + 1) B.endr).sumenq ∧
      B.sumdeq = (M.bk (2 * v) B.endl).sumdeq + (M.bk (2 * v + 1) B.endr).sumdeq ∧
      (M.bk v (h - 1)).sumenq + (M.bk v (h - 1)).sumdeq < B.sumenq + B.sumdeq ∧
      (v = 1 → B.size = (M.bk v (h - 1)).size + (B.sumenq - (M.bk v (h - 1)).sumenq) -
        (B.sumdeq - (M.bk v (h - 1)).sumdeq)) ∧
      SupUp M (2 * v) B.endl v h ∧ SupUp M (2 * v + 1) B.endr v h
  | .idx v b i => BaseH H os rs M p pend l ∧ l.cur = .deq ∧ InRoot H rs M p ∧ 2 ≤ v ∧
      v < 2 ^ (H + 1) ∧ 1 ≤ b ∧ b ≤ cnt M v ∧ 1 ≤ i ∧ i ≤ (deqs (ops H np M v b)).length ∧
      (deqs (ops H np M v b))[i - 1]? = some (xOf rs p)
  | .fr b i => BaseH H os rs M p pend l ∧ l.cur = .deq ∧ InRoot H rs M p ∧ 1 ≤ b ∧ b ≤ cnt M 1 ∧
      1 ≤ i ∧ i ≤ (deqs (ops H np M 1 b)).length ∧
      (deqs (ops H np M 1 b))[i - 1]? = some (xOf rs p)
  | .ge v b i => BaseH H os rs M p pend l ∧ l.cur = .deq ∧ 1 ≤ v ∧ v < 2 ^ (H + 1) ∧ 1 ≤ b ∧
      b ≤ cnt M v ∧ 1 ≤ i ∧ i ≤ (enqs (ops H np M v b)).length ∧
      ∃ e, (enqs (ops H np M v b))[i - 1]? = some e ∧
        (queueObj V).respIn [] (rootLin H np M) (xOf rs p) = some (some e.2)
  | .done r => BaseH H os rs M p pend l ∧
      (queueObj V).respIn [] (rootLin H np M) (xOf rs p) = some r

end PInv

/-- The invariant of reachable configurations (with ghost state). -/
structure Inv (H np : ℕ) (α : List (Label (Fin np) (queueObj V)))
    (C : Config (queueObj V) (fun _ : Unit => memObj V) (Fin np) (Loc V)) (G : Ghost np) :
    Prop where
  shape : Shape H np (C.mem ())
  minv : MInv H (C.mem ())
  ginv : GInv H (C.mem ()) G
  lin : IsLinearization α (rootLin H np (C.mem ()))
  proc : ∀ p, PInv H (opsOf α p) (respsOf α p) (C.mem ()) G p (C.pend p) (C.loc p)

end Podc.WaitFreeQueuePolylog
