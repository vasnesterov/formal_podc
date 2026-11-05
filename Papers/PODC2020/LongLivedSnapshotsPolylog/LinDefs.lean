import Papers.PODC2020.LongLivedSnapshotsPolylog.LinBasic

/-!
# Linearizability of Algorithm 1: certificates and the invariant

A **certificate** `Cert α V t0 t1` of a view `V` says that `V` is a "direct view" computed by a
`CompScan` iteration whose line-11 read happened at time `t0` and whose `MaxScan(MA_h)` (line 17)
happened at time `t1`: the high-order bits `(a, b)` of `MR_left`, `MR_right` are constant on
`[t0, t1]`, `V = (a·m + MA_h.left, b·m + MA_h.right)` at time `t1` (`h = a + b`),
`MR(t0) ≤ V ≤ MR(t1)` componentwise, and both components of `V` are actual values of the max
registers before `t1`.

Two certificates are ordered like their times `t1` (`cert_le_of_le`, in `LinMain.lean`); every
completed operation has a certificate inside its execution interval (`OpCert`). This replaces
Definition 3.2 and the linearization rules of the paper, which are wrong
(`Counterexample.lean`).
-/

namespace Podc.LongLivedSnapshotsPolylog

open Cslib.SharedMemory
open Podc.LimitedUseSnapshots (maxArrObj MAOp)

variable {n : ℕ} (m X : ℕ)

/-- Certificate of the view `V` (see the module docstring). -/
def Cert (α : List (Lbl n)) (V : ℕ × ℕ) (t0 t1 : ℕ) : Prop :=
  t0 ≤ t1 ∧ t1 ≤ α.length ∧
  (∃ a b, (∀ t, t0 ≤ t → t ≤ t1 →
      vL (cfgAt m X α t) / m = a ∧ vR (cfgAt m X α t) / m = b) ∧
    V = (a * m + (vMA (cfgAt m X α t1) (a + b)).1, b * m + (vMA (cfgAt m X α t1) (a + b)).2)) ∧
  vL (cfgAt m X α t0) ≤ V.1 ∧ vR (cfgAt m X α t0) ≤ V.2 ∧
  V.1 ≤ vL (cfgAt m X α t1) ∧ V.2 ≤ vR (cfgAt m X α t1) ∧
  (∃ t', t' ≤ t1 ∧ vL (cfgAt m X α t') = V.1) ∧ (∃ t', t' ≤ t1 ∧ vR (cfgAt m X α t') = V.2)

/-- The context of a `CompScan` instance of process `p` started at time `bt`: its operation was
invoked before `bt`, a `MaxUpdate`'s value is already in its max register at `bt`, the flag
`cs.upd` matches the operation, and the first collect (if any) was read after `bt`. -/
def Ctx (α : List (Lbl n)) (p : Fin n) (cs : CS n) (bt : ℕ) : Prop :=
  bt ≤ α.length ∧ Invoked (α.take bt) (curOp α p) ∧
  (∀ v, opOf α (curOp α p) = some (.upd0 v) → v ≤ vL (cfgAt m X α bt)) ∧
  (∀ v, opOf α (curOp α p) = some (.upd1 v) → v ≤ vR (cfgAt m X α bt)) ∧
  (cs.upd = false ↔ opOf α (curOp α p) = some .scan) ∧
  (∀ h0, cs.h0 = some h0 → ∀ j, ∃ t, bt ≤ t ∧ t ≤ α.length ∧
    (vH (cfgAt m X α t) j).1 = (h0 j).1)

/-- Facts about the reads of lines 10–12 of the current iteration: `MR_left` was `l` at time
`t0`, `MR_right` was `r2` at time `t2 ≥ t0` and had the high-order bits of `r2` at a time
`≤ t0`; the timestamp `H[p].ts` at time `t0` is the current local one. -/
def Rd (α : List (Lbl n)) (C : Cfg n) (p : Fin n) (cs : CS n) (l r2 bt t0 t2 : ℕ) : Prop :=
  Ctx m X α p cs bt ∧ bt ≤ t0 ∧ t0 ≤ t2 ∧ t2 ≤ α.length ∧
  (∃ tr, tr ≤ t0 ∧ vR (cfgAt m X α tr) / m = r2 / m) ∧
  vL (cfgAt m X α t0) = l ∧ vR (cfgAt m X α t2) = r2 ∧
  (vH (cfgAt m X α t0) p).1 = (C.loc p).ts

/-- Facts about the `MaxScan(MA_h)` of line 17, performed at time `t1`, that returned `v`. -/
def ScanOK (α : List (Lbl n)) (l r2 : ℕ) (v : ℕ × ℕ) (t1 : ℕ) : Prop :=
  v = vMA (cfgAt m X α t1) (idx m l r2) ∧ l % m ≤ v.1 ∧ r2 % m ≤ v.2 ∧
  l / m * m + v.1 ≤ vL (cfgAt m X α t1) ∧ r2 / m * m + v.2 ≤ vR (cfgAt m X α t1) ∧
  (0 < v.1 → ∃ t', t' ≤ t1 ∧ vL (cfgAt m X α t') = l / m * m + v.1) ∧
  (0 < v.2 → ∃ t', t' ≤ t1 ∧ vR (cfgAt m X α t') = r2 / m * m + v.2)

/-- The response `r` is correct for a view `V` of the current operation of `p`. -/
def RetOK (α : List (Lbl n)) (p : Fin n) (r V : ℕ × ℕ) : Prop :=
  (opOf α (curOp α p) = some .scan → r = V) ∧
  (∀ v, opOf α (curOp α p) = some (.upd0 v) → v ≤ V.1 ∧ r = (0, 0)) ∧
  (∀ v, opOf α (curOp α p) = some (.upd1 v) → v ≤ V.2 ∧ r = (0, 0))

/-- The per-process invariant, by program counter. -/
def PFL (α : List (Lbl n)) (C : Cfg n) (p : Fin n) : PC n → Prop
  | .idle => True
  | .wm s v => opOf α (curOp α p) = some (if s then .upd1 v else .upd0 v)
  | .rdR1 cs => ∃ bt, Ctx m X α p cs bt
  | .rdL cs r1 => ∃ bt tr, Ctx m X α p cs bt ∧ bt ≤ tr ∧ tr ≤ α.length ∧
      vR (cfgAt m X α tr) = r1
  | .rdR2 cs r1 l => ∃ bt tr t0, Ctx m X α p cs bt ∧ bt ≤ tr ∧ tr ≤ t0 ∧ t0 ≤ α.length ∧
      vR (cfgAt m X α tr) = r1 ∧ vL (cfgAt m X α t0) = l ∧
      (vH (cfgAt m X α t0) p).1 = (C.loc p).ts
  | .upL cs l r2 => ∃ bt t0 t2, Rd m X α C p cs l r2 bt t0 t2
  | .upR cs l r2 => ∃ bt t0 t2, Rd m X α C p cs l r2 bt t0 t2 ∧
      l % m ≤ (vMA C (idx m l r2)).1
  | .scanMA cs l r2 => ∃ bt t0 t2, Rd m X α C p cs l r2 bt t0 t2 ∧
      l % m ≤ (vMA C (idx m l r2)).1 ∧ r2 % m ≤ (vMA C (idx m l r2)).2
  | .chkL cs l r2 v => ∃ bt t0 t2 t1, Rd m X α C p cs l r2 bt t0 t2 ∧ t2 ≤ t1 ∧
      t1 ≤ α.length ∧ ScanOK m X α l r2 v t1
  | .chkR cs l r2 v => ∃ bt t0 t2 t1 te, Rd m X α C p cs l r2 bt t0 t2 ∧ t2 ≤ t1 ∧ t1 ≤ te ∧
      te ≤ α.length ∧ ScanOK m X α l r2 v t1 ∧ vL (cfgAt m X α te) / m = l / m
  | .wH cs V => ∃ bt t0 t1, Ctx m X α p cs bt ∧ bt ≤ t0 ∧ Cert m X α V t0 t1 ∧
      (vH (cfgAt m X α t0) p).1 = (C.loc p).ts
  | .col cs _ k acc => ∃ bt, Ctx m X α p cs bt ∧ ∀ j : Fin n, j.1 < k.1 →
      ∃ t, bt ≤ t ∧ t ≤ α.length ∧ vH (cfgAt m X α t) j = acc j ∧
        (0 < (acc j).1 → ∃ t0 t1, Cert m X α (acc j).2 t0 t1 ∧
          (vH (cfgAt m X α t0) j).1 + 1 = (acc j).1)
  | .retV r => ∃ V t0 t1, Cert m X α V t0 t1 ∧ Invoked (α.take t0) (curOp α p) ∧
      RetOK α p r V

/-- Invariant on `MA_j`: its components are the low-order bits of values of `MR_left`,
`MR_right` whose high-order bits `(a, b)` (with `a + b = j`) were simultaneously current. -/
def MAInv (α : List (Lbl n)) (C : Cfg n) : Prop :=
  ∀ j, vMA C j ≠ (0, 0) → ∃ t, t ≤ α.length ∧
    vL (cfgAt m X α t) / m + vR (cfgAt m X α t) / m = j ∧
    vL (cfgAt m X α t) / m * m + (vMA C j).1 ≤ vL C ∧
    vR (cfgAt m X α t) / m * m + (vMA C j).2 ≤ vR C ∧
    (0 < (vMA C j).1 → ∃ t', t' ≤ α.length ∧
      vL (cfgAt m X α t') = vL (cfgAt m X α t) / m * m + (vMA C j).1) ∧
    (0 < (vMA C j).2 → ∃ t', t' ≤ α.length ∧
      vR (cfgAt m X α t') = vR (cfgAt m X α t) / m * m + (vMA C j).2)

/-- Invariant on the helping array: a nonzero timestamp comes with a certificate of the view,
computed after `H[j].ts` reached its previous value. -/
def HInv (α : List (Lbl n)) (C : Cfg n) : Prop :=
  ∀ j, 0 < (vH C j).1 → ∃ t0 t1, Cert m X α (vH C j).2 t0 t1 ∧
    (vH (cfgAt m X α t0) j).1 + 1 = (vH C j).1

/-- Every nonzero value of a max register was written by an invoked `MaxUpdate`. -/
def WInv (α : List (Lbl n)) (C : Cfg n) : Prop :=
  (0 < vL C → ∃ u, opOf α u = some (.upd0 (vL C)) ∧ Invoked α u) ∧
  (0 < vR C → ∃ u, opOf α u = some (.upd1 (vR C)) ∧ Invoked α u)

/-- A completed operation has a certificate inside its execution interval, consistent with its
response. -/
def OpCert (α : List (Lbl n)) (x : OpId (Fin n)) : Prop :=
  ∃ V t0 t1, Cert m X α V t0 t1 ∧ Invoked (α.take t0) x ∧ ¬ Completed (α.take t1) x ∧
    (opOf α x = some .scan → respOf α x = some V) ∧
    (∀ v, opOf α x = some (.upd0 v) → v ≤ V.1 ∧ respOf α x = some (0, 0)) ∧
    (∀ v, opOf α x = some (.upd1 v) → v ≤ V.2 ∧ respOf α x = some (0, 0))

/-- The invariant of Algorithm 1. -/
def Inv (α : List (Lbl n)) (C : Cfg n) : Prop :=
  BasicInv C ∧ MAInv m X α C ∧ HInv m X α C ∧ WInv α C ∧
  (∀ x, Completed α x → OpCert m X α x) ∧ ∀ p, PFL m X α C p (C.loc p).pc

end Podc.LongLivedSnapshotsPolylog
