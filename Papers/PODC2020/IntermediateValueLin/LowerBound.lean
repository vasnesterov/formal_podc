import Papers.PODC2020.IntermediateValueLin.Snapshot
import Mathlib.Data.List.Forall2

/-!
# Theorem 3: the `Ω(n)` lower bound for linearizable batched counters (conditional)

Rinberg–Keidar, PODC 2020, Section 6.2, Theorem 3: *for any linearizable wait-free
implementation of a batched counter object with `n` processes from SWMR registers, the step
complexity of `update` is `Ω(n)`.*

The paper derives this from the lower bound of Israeli and Shirazi [21] for (binary) snapshots
from SWMR registers, by the reduction of Algorithm 3. We do not formalize [21]: it is the
hypothesis `ISLowerBound n b` ("no linearizable wait-free implementation of the binary snapshot
with `n` processes from SWMR registers has all its updates performing at most `b` base-object
accesses"). `theorem3` shows that the same bound `b` then holds for batched counters: the
reduction adds no base-object accesses at all.

## The reduction

Given a batched-counter implementation `C` from registers, `Reduction.comp C` is Algorithm 3 with
`C`'s code inlined for the counter accesses: a process keeps its bit `v_p`, the current snapshot
operation, and `C`'s local state; its base objects are `C`'s registers. A snapshot `update_p(v)`
runs `C.update(enc)` and a `scan` runs `C.read()` and returns the bits `0, …, n-1` of the result.

**Difference from the paper's Algorithm 3.** The composed algorithm has *no* shortcut on line 4:
if `v = v_p` it still runs `C.update(0)` (legal: `0 ≥ 0`) instead of returning at once; `v_p` is
updated when the operation returns. This does not matter for the reduction: Invariant 1 still
holds (adding `0` keeps the counter), and the shortcut could only *decrease* the number of
accesses of an update. It makes the simulation exact: every label of the composed execution
corresponds to exactly one label of an execution of `C` (`Reduction.LRel`: invocation ↦
invocation with the encoded counter operation, internal step ↦ the same internal step, response
↦ response), so operation instances, real-time order and per-process access counts coincide.

## Proof structure

* `Reduction.step_sim`: a composed step is a step of `C` on the projected configuration
  (`projCfg`, `projLbl`).
* `Reduction.sim_of_run`: every composed execution `α` has a corresponding execution `β` of `C`
  (`Sim`): same shape, `C`'s operations are the encodings of the snapshot operations along each
  process (`encOps`), and the snapshot responses are the decodings of `C`'s responses.
* `Reduction.isLinearization_lift`: a linearization of `β` gives one of `α` (legality by
  Invariant 1 along the linearization, using that every process's instances appear in program
  order, `IsLinearization.procIds_eq`).
* Transfer of the access discipline (`comp_allowed`), of SWMR (`comp_swmr`), wait-freedom
  (`comp_waitFree`, projecting infinite executions), linearizability (`comp_linearizable`) and of
  the step bound (`comp_stepsLE`).
-/

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

namespace Podc.IntermediateValueLin

/-- **The Israeli–Shirazi lower bound [21] (hypothesis, not proved here)**, for bound `b`: there
is no linearizable, wait-free implementation of the binary snapshot object with `n` processes
(process `p` updates only component `p`) from SWMR registers in which every `update` performs at
most `b` base-object accesses. ([21] proves this for `b < n` up to a constant factor, i.e. update
step complexity `Ω(n)`; the paper notes that the proof applies to binary snapshots [20].) -/
def ISLowerBound (n b : ℕ) : Prop :=
  ∀ (ι V Lc : Type) [DecidableEq ι] (v₀ : V) (owner : ι → Fin n)
    (I : Impl (binSnap n) (fun _ : ι => register V v₀) (Fin n) Lc),
    (∀ p o, I.allowed p o ↔ o.Allowed p) → I.SWMR owner → I.WaitFree → I.Linearizable →
    ¬ I.StepsLE (fun o => ∃ i v, o = .update i v) b

namespace Reduction

variable {n : ℕ}

/-! ## Encoding snapshot operations as counter operations -/

/-- The counter increment of `update_p(v)` when `p`'s bit is `b` (Algorithm 3 without the line-4
shortcut): `0` if `b = v`, else `2^p` or `2^n - 2^p`. -/
def enc (n : ℕ) (p : Fin n) (b v : Bool) : ℕ := if b = v then 0 else delta n p v

/-- The bit of the updating process after operation `o` (was `b`). -/
def newVal : SnapOp n → Bool → Bool
  | .update _ v, _ => v
  | .scan, b => b

/-- The counter operation run by process `p` (bit `b`) for snapshot operation `o`. -/
def toBC (p : Fin n) (b : Bool) : SnapOp n → BCOp
  | .update _ v => .update (enc n p b v)
  | .scan => .read

/-- The snapshot response for counter response `r`: a dummy for `update`, the bits of `r` for
`scan`. -/
def outResp : SnapOp n → ℕ → (Fin n → Bool)
  | .update _ _, _ => fun _ => false
  | .scan, r => decode n r

/-- The bit of a process after its operations `os` (from `b`). -/
def lastValFrom (b : Bool) (os : List (SnapOp n)) : Bool := os.foldl (fun b o => newVal o b) b

/-- The counter operations of process `p` for its snapshot operations `os` (bit initially `b`). -/
def encOps (p : Fin n) : Bool → List (SnapOp n) → List BCOp
  | _, [] => []
  | b, o :: os => toBC p b o :: encOps p (newVal o b) os

lemma encOps_concat (p : Fin n) (b : Bool) (os : List (SnapOp n)) (o : SnapOp n) :
    encOps p b (os ++ [o]) = encOps p b os ++ [toBC p (lastValFrom b os) o] := by
  induction os generalizing b with
  | nil => rfl
  | cons o' os ih => simp [encOps, ih, lastValFrom]

lemma encOps_getElem? (p : Fin n) (b : Bool) (os : List (SnapOp n)) (k : ℕ) :
    (encOps p b os)[k]? = os[k]?.map (toBC p (lastValFrom b (os.take k))) := by
  induction os generalizing b k with
  | nil => simp [encOps]
  | cons o os ih =>
    cases k with
    | zero => simp [encOps, lastValFrom]
    | succ k => simp [encOps, ih, lastValFrom]

lemma lastValFrom_concat (b : Bool) (os : List (SnapOp n)) (o : SnapOp n) :
    lastValFrom b (os ++ [o]) = newVal o (lastValFrom b os) := by
  simp [lastValFrom]

lemma zipWith_concat_right {X Y Z : Type} (f : X → Y → Z) {l : List X} {m : List Y} (y : Y)
    (h : m.length < l.length) :
    List.zipWith f l (m ++ [y]) = List.zipWith f l m ++ [f (l[m.length]'h) y] := by
  induction m generalizing l with
  | nil => cases l with
    | nil => simp at h
    | cons a l => simp
  | cons c m ih => cases l with
    | nil => simp at h
    | cons a l =>
      simp only [List.cons_append, List.zipWith_cons_cons, List.length_cons,
        List.getElem_cons_succ, List.cons.injEq, true_and]
      exact ih (by simpa using h)

lemma zipWith_append_left_of_le {X Y Z : Type} (f : X → Y → Z) {l l' : List X} {m : List Y}
    (h : m.length ≤ l.length) : List.zipWith f (l ++ l') m = List.zipWith f l m := by
  induction m generalizing l with
  | nil => simp
  | cons c m ih => cases l with
    | nil => simp at h
    | cons a l =>
      simp only [List.cons_append, List.zipWith_cons_cons, List.cons.injEq, true_and]
      exact ih (by simpa using h)

/-! ## Corresponding labels -/

/-- A label of the composed execution and the corresponding label of `C`'s execution: same
process and same kind (an update invocation corresponds to an update invocation, a scan to a
read). -/
inductive LRel : Label (Fin n) (binSnap n) → Label (Fin n) batchedCounter → Prop
  | upd (p i : Fin n) (v : Bool) (w : ℕ) : LRel (.inv p (.update i v)) (.inv p (.update w))
  | scan (p : Fin n) : LRel (.inv p .scan) (.inv p .read)
  | tau (p : Fin n) : LRel (.tau p) (.tau p)
  | ret (p : Fin n) (r : Fin n → Bool) (r' : ℕ) : LRel (.ret p r) (.ret p r')

lemma LRel.counts {ℓ : Label (Fin n) (binSnap n)} {ℓ' : Label (Fin n) batchedCounter}
    (h : LRel ℓ ℓ') (p : Fin n) :
    (ℓ.invOf p).toList.length = (ℓ'.invOf p).toList.length ∧
      (ℓ.retOf p).toList.length = (ℓ'.retOf p).toList.length ∧
      ℓ.isTauOf p = ℓ'.isTauOf p := by
  cases h <;> simp only [Label.invOf_inv, Label.invOf_tau, Label.invOf_ret, Label.retOf_inv,
    Label.retOf_tau, Label.retOf_ret, Label.isTauOf_inv, Label.isTauOf_tau,
    Label.isTauOf_ret] <;> (try split_ifs) <;> simp

lemma forall₂_counts {α : List (Label (Fin n) (binSnap n))}
    {β : List (Label (Fin n) batchedCounter)} (h : List.Forall₂ LRel α β) (p : Fin n) :
    (opsOf α p).length = (opsOf β p).length ∧ (respsOf α p).length = (respsOf β p).length ∧
      α.countP (Label.isTauOf p) = β.countP (Label.isTauOf p) := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    obtain ⟨a1, a2, a3⟩ := hr.counts p
    obtain ⟨b1, b2, b3⟩ := ih
    simp only [opsOf_cons, respsOf_cons, List.length_append, List.countP_cons, a1, a2, a3, b1,
      b2, b3, and_self]

lemma precedes_of_forall₂ {α : List (Label (Fin n) (binSnap n))}
    {β : List (Label (Fin n) batchedCounter)} (h : List.Forall₂ LRel α β) {a b : OpId (Fin n)}
    (hp : Precedes α a b) : Precedes β a b := by
  obtain ⟨α₁, α₂, rfl, hc, hni⟩ := hp
  refine ⟨β.take α₁.length, β.drop α₁.length, (List.take_append_drop _ _).symm, ?_, ?_⟩
  · have h1 : List.Forall₂ LRel α₁ (β.take α₁.length) := by
      simpa using List.forall₂_take α₁.length h
    have := (forall₂_counts h1 a.1).2.1
    unfold Completed at *; omega
  · have h1 : List.Forall₂ LRel α₁ (β.take α₁.length) := by
      simpa using List.forall₂_take α₁.length h
    have := (forall₂_counts h1 b.1).1
    unfold Invoked at *; omega

lemma not_ret_of_forall₂ {γ : List (Label (Fin n) (binSnap n))}
    {γ' : List (Label (Fin n) batchedCounter)} (h : List.Forall₂ LRel γ γ') {p : Fin n}
    (hr : ∀ r, .ret p r ∉ γ) : ∀ r, .ret p r ∉ γ' := by
  induction h with
  | nil => simp
  | cons hl _ ih =>
    intro r hm
    rcases List.mem_cons.1 hm with rfl | hm
    · cases hl with
      | ret q r₀ r' => exact hr r₀ (by simp)
    · exact ih (fun r' hr' => hr r' (List.mem_cons_of_mem _ hr')) r hm

/-! ## Linearizations of `C`'s execution give linearizations of the composed execution -/

/-- `IsLinearization.procIds` for the batched counter: the instances of `p` in `M`. -/
abbrev pids (M : List (OpId (Fin n) × BCOp)) (p : Fin n) : List (OpId (Fin n)) :=
  IsLinearization.procIds (A := batchedCounter) M p

/-- The position of an instance of `p` in a linearization is its index among `p`'s instances. -/
lemma idx_eq {β : List (Label (Fin n) batchedCounter)}
    {L M N : List (OpId (Fin n) × BCOp)} {x : OpId (Fin n)} {o : BCOp} (hwf : WellFormed β)
    (hL : IsLinearization β L) (h : L = M ++ (x, o) :: N) : x.2 = (pids M x.1).length := by
  have heq := hL.procIds_eq hwf x.1
  have e : pids L x.1 = pids M x.1 ++ x :: pids N x.1 := by
    subst h; simp [pids, IsLinearization.procIds, List.filter_append]
  change pids L x.1 = List.map (fun j => (x.1, j)) (List.range (pids L x.1).length) at heq
  rw [e] at heq
  have := congrArg (fun l => l[(pids M x.1).length]?) heq
  simp only [List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero,
    List.getElem?_map] at this
  rw [List.getElem?_range (by simp)] at this
  simp only [Option.map_some, Option.some.injEq] at this
  rw [this]

/-- Lifting a list of instances of `C`'s execution to the composed execution: same instances,
with their snapshot operations. -/
def liftLin (α : List (Label (Fin n) (binSnap n))) (L : List (OpId (Fin n) × BCOp)) :
    List (OpId (Fin n) × SnapOp n) :=
  L.map fun y => (y.1, (opOf α y.1).getD .scan)

/-- **Legality** (Invariant 1 along a linearization): if `L = M ++ N` linearizes `β`, the counter
state `s` after `M` has bits `σ`, and `σ p` is the bit of `p` after its instances in `M`, then
the lifted `N` is legal for the snapshot from `σ`. -/
lemma seq_lift {α : List (Label (Fin n) (binSnap n))} {β : List (Label (Fin n) batchedCounter)}
    (hops : ∀ p, opsOf β p = encOps p false (opsOf α p))
    (hresps : ∀ p, respsOf α p = List.zipWith outResp (opsOf α p) (respsOf β p))
    (hal : ∀ p o, o ∈ opsOf α p → o.Allowed p) (hwf : WellFormed β)
    {L : List (OpId (Fin n) × BCOp)} (hL : IsLinearization β L) :
    ∀ (N M : List (OpId (Fin n) × BCOp)) (s : ℕ) (σ : Fin n → Bool), L = M ++ N →
      (∀ j : Fin n, s.testBit j = σ j) →
      (∀ p, σ p = lastValFrom false ((opsOf α p).take (pids M p).length)) →
      SeqOK β s N → SeqOK α σ (liftLin α N)
  | [], _, _, _, _, _, _, _ => trivial
  | (x, oC) :: N, M, s, σ, hsplit, hbits, hσ, hseq => by
    obtain ⟨hr, hseq'⟩ := hseq
    obtain ⟨p, k⟩ := x
    have hk : k = (pids M p).length := idx_eq hwf hL hsplit
    have hoC : opOf β (p, k) = some oC := hL.op_eq ((p, k), oC) (by rw [hsplit]; simp)
    simp only [opOf] at hoC
    rw [hops p, encOps_getElem?] at hoC
    obtain ⟨oS, hoS, hoCe⟩ := Option.map_eq_some_iff.1 hoC
    have hσp : σ p = lastValFrom false ((opsOf α p).take k) := by rw [hσ p, hk]
    rw [← hσp] at hoCe
    subst hoCe
    have hopS : opOf α (p, k) = some oS := hoS
    have hmem : oS ∈ opsOf α p := List.mem_of_getElem? hoS
    simp only [liftLin, List.map_cons, hopS, Option.getD_some]
    refine ⟨fun r hr' => ?_, ?_⟩
    · -- the response
      simp only [respOf, hresps p, List.getElem?_zipWith, hoS] at hr'
      cases hrb : (respsOf β p)[k]? with
      | none => simp [hrb] at hr'
      | some rb =>
        simp only [hrb, Option.some.injEq] at hr'
        subst hr'
        have := hr rb hrb
        cases oS with
        | update i v => rfl
        | scan =>
          simp only [toBC] at this
          subst this
          funext j
          exact (hbits j).symm
    · refine seq_lift hops hresps hal hwf hL N (M ++ [((p, k), toBC p (σ p) oS)]) _ _
        (by rw [hsplit]; simp) ?_ ?_ hseq'
      · intro j
        cases oS with
        | scan => exact hbits j
        | update i v =>
          have hi : i = p := hal p _ hmem
          subst hi
          simp only [toBC, enc]
          by_cases hv : σ i = v
          · simp only [hv, ite_true, Nat.add_zero]
            rw [hbits j, ← hv, Function.update_eq_self]
          · simp only [hv, ite_false]
            exact testBit_add_delta hbits i hv j
      · intro q
        have hpq : pids (M ++ [((p, k), toBC p (σ p) oS)]) q =
            pids M q ++ (if p = q then [(p, k)] else []) := by
          by_cases h : p = q <;> simp [pids, IsLinearization.procIds, List.filter_append, h]
        rw [hpq]
        by_cases h : p = q
        · subst h
          simp only [ite_true, List.length_append, List.length_singleton]
          rw [← hk, List.take_add_one, hoS, Option.toList_some, lastValFrom_concat, ← hσp]
          cases oS with
          | scan => rfl
          | update i v =>
            have hi : i = p := hal p _ hmem
            subst hi; simp [newVal]
        · simp only [h, ite_false, List.append_nil]
          rw [← hσ q]
          cases oS with
          | scan => rfl
          | update i v =>
            have hi : i = p := hal p _ hmem
            subst hi; simp [Function.update_of_ne (Ne.symm h)]

/-- **Linearizations transfer**: a linearization of `C`'s execution `β` lifts to a linearization
of the composed execution `α`. -/
theorem isLinearization_lift {α : List (Label (Fin n) (binSnap n))}
    {β : List (Label (Fin n) batchedCounter)} (hF : List.Forall₂ LRel α β)
    (hops : ∀ p, opsOf β p = encOps p false (opsOf α p))
    (hresps : ∀ p, respsOf α p = List.zipWith outResp (opsOf α p) (respsOf β p))
    (hal : ∀ p o, o ∈ opsOf α p → o.Allowed p) (hwf : WellFormed β)
    {L : List (OpId (Fin n) × BCOp)} (hL : IsLinearization β L) :
    IsLinearization α (liftLin α L) := by
  have hids : (liftLin α L).map Prod.fst = L.map Prod.fst := by simp [liftLin]
  refine ⟨by rw [hids]; exact hL.nodup, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have hinv : Invoked α z.1 := by
      have h1 := hL.mem_invoked (List.mem_map_of_mem hz)
      have h2 := (forall₂_counts hF z.1.1).1
      unfold Invoked at *; omega
    obtain ⟨o, ho⟩ : ∃ o, opOf α z.1 = some o := by
      simp only [opOf]; exact ⟨_, List.getElem?_eq_getElem hinv⟩
    simp [ho]
  · intro a ha
    rw [hids]
    apply hL.complete
    have := (forall₂_counts hF a.1).2.1
    unfold Completed at *; omega
  · intro a b hab hb
    rw [hids] at hb ⊢
    exact hL.realtime a b (precedes_of_forall₂ hF hab) hb
  · have := seq_lift hops hresps hal hwf hL L [] 0 (fun _ => false) (by simp)
      (fun j => Nat.zero_testBit _) (fun p => by simp [pids, IsLinearization.procIds, lastValFrom]) hL.seq
    exact this

/-! ## The composed algorithm -/

/-- Local state of the composed algorithm: the bit `v_p` (before the current operation), the
current snapshot operation and the local state of `C`. -/
structure CompLoc (n : ℕ) (Lc : Type) where
  /-- The bit of the process before its current operation. -/
  v : Bool
  /-- The current snapshot operation. -/
  op : SnapOp n
  /-- The local state of the counter implementation `C`. -/
  l : Lc

variable {ι V Lc : Type} [DecidableEq ι] {v₀ : V}

/-- **Algorithm 3 with `C` inlined** (without the line-4 shortcut): `update_p(v)` runs `C`'s
`update(enc n p v_p v)`, `scan` runs `C`'s `read()` and returns the bits `0, …, n-1` of its
result; `v_p ← v` when an update returns. The base objects are `C`'s registers. -/
def comp (C : Impl batchedCounter (fun _ : ι => register V v₀) (Fin n) Lc) :
    Impl (binSnap n) (fun _ : ι => register V v₀) (Fin n) (CompLoc n Lc) where
  memInit := C.memInit
  locInit p := ⟨false, .scan, C.locInit p⟩
  invoke p s o := ⟨s.v, o, C.invoke p s.l (toBC p s.v o)⟩
  act p s := match C.act p s.l with
    | .access i o k => .access i o (fun r => ⟨s.v, s.op, k r⟩)
    | .ret r l => .ret (outResp s.op r) ⟨newVal s.op s.v, s.op, l⟩
  allowed p o := o.Allowed p

/-- Configurations of the composed algorithm. -/
abbrev SCfg (n : ℕ) (ι V Lc : Type) (v₀ : V) :=
  Config (binSnap n) (fun _ : ι => register V v₀) (Fin n) (CompLoc n Lc)

/-- Configurations of `C`. -/
abbrev CCfg (n : ℕ) (ι V Lc : Type) (v₀ : V) :=
  Config batchedCounter (fun _ : ι => register V v₀) (Fin n) Lc

variable {C : Impl batchedCounter (fun _ : ι => register V v₀) (Fin n) Lc}

lemma comp_step_inv {D D' : SCfg n ι V Lc v₀} {p : Fin n} {o : SnapOp n}
    (h : (comp C).step D (.inv p o) = some D') :
    D.pend p = none ∧ o.Allowed p ∧
      D' = { D with
        pend := Function.update D.pend p (some o),
        loc := Function.update D.loc p
          ⟨(D.loc p).v, o, C.invoke p (D.loc p).l (toBC p (D.loc p).v o)⟩ } := by
  obtain ⟨hp, hal, -⟩ := Impl.step_inv h
  rw [Impl.step_inv_eq_some hp hal] at h
  exact ⟨hp, hal, (Option.some.inj h).symm⟩

lemma comp_step_tau {D D' : SCfg n ι V Lc v₀} {p : Fin n}
    (h : (comp C).step D (.tau p) = some D') :
    D.pend p ≠ none ∧ ∃ i o k, C.act p (D.loc p).l = .access i o k ∧
      D' = { D with
        mem := Function.update D.mem i ((register V v₀).δ (D.mem i) o).1,
        loc := Function.update D.loc p
          ⟨(D.loc p).v, (D.loc p).op, k ((register V v₀).δ (D.mem i) o).2⟩ } := by
  obtain ⟨hp, -⟩ := Impl.step_tau h
  refine ⟨hp, ?_⟩
  cases hc : C.act p (D.loc p).l with
  | access i o k =>
    have hact : (comp C).act p (D.loc p) =
        .access i o (fun r => ⟨(D.loc p).v, (D.loc p).op, k r⟩) := by simp [comp, hc]
    rw [Impl.step_tau_eq_some hp hact] at h
    exact ⟨i, o, k, rfl, (Option.some.inj h).symm⟩
  | ret r l =>
    have hact : (comp C).act p (D.loc p) =
        .ret (outResp (D.loc p).op r) ⟨newVal (D.loc p).op (D.loc p).v, (D.loc p).op, l⟩ := by
      simp [comp, hc]
    simp [Impl.step, hp, hact] at h

lemma comp_step_ret {D D' : SCfg n ι V Lc v₀} {p : Fin n} {r : Fin n → Bool}
    (h : (comp C).step D (.ret p r) = some D') :
    D.pend p ≠ none ∧ ∃ r' l, C.act p (D.loc p).l = .ret r' l ∧ r = outResp (D.loc p).op r' ∧
      D' = { D with
        pend := Function.update D.pend p none,
        loc := Function.update D.loc p ⟨newVal (D.loc p).op (D.loc p).v, (D.loc p).op, l⟩ } := by
  obtain ⟨hp, -, -, l₀, hact₀, -⟩ := Impl.step_ret h
  refine ⟨hp, ?_⟩
  cases hc : C.act p (D.loc p).l with
  | access i o k =>
    have hact : (comp C).act p (D.loc p) =
        .access i o (fun r => ⟨(D.loc p).v, (D.loc p).op, k r⟩) := by simp [comp, hc]
    rw [hact] at hact₀; cases hact₀
  | ret r' l =>
    have hact : (comp C).act p (D.loc p) =
        .ret (outResp (D.loc p).op r') ⟨newVal (D.loc p).op (D.loc p).v, (D.loc p).op, l⟩ := by
      simp [comp, hc]
    rw [hact] at hact₀
    obtain ⟨rfl, -⟩ := Action.ret.inj hact₀
    rw [Impl.step_ret_eq_some hp hact] at h
    exact ⟨r', l, rfl, rfl, (Option.some.inj h).symm⟩

/-! ## Projection to `C` -/

/-- The configuration of `C` represented by a composed configuration. -/
def projCfg (D : SCfg n ι V Lc v₀) : CCfg n ι V Lc v₀ :=
  ⟨fun p => (D.loc p).l, fun p => (D.pend p).map (toBC p (D.loc p).v), D.mem⟩

/-- The label of `C` corresponding to a composed label taken from configuration `D`. -/
def projLbl (C : Impl batchedCounter (fun _ : ι => register V v₀) (Fin n) Lc)
    (D : SCfg n ι V Lc v₀) : Label (Fin n) (binSnap n) → Label (Fin n) batchedCounter
  | .inv p o => .inv p (toBC p (D.loc p).v o)
  | .tau p => .tau p
  | .ret p _ => .ret p (match C.act p (D.loc p).l with
    | .ret r _ => r
    | .access _ _ _ => 0)

/-- The local state records the pending operation. -/
def PendOp (D : SCfg n ι V Lc v₀) : Prop := ∀ p o, D.pend p = some o → (D.loc p).op = o

lemma cfg_ext {E E' : CCfg n ι V Lc v₀} (h1 : E.loc = E'.loc) (h2 : E.pend = E'.pend)
    (h3 : E.mem = E'.mem) : E = E' := by
  cases E; cases E'; simp_all

/-- **Step simulation**: a composed step is a step of `C` on the projected configuration, with a
corresponding label. -/
theorem step_sim (hall : ∀ p o, C.allowed p o) {D D' : SCfg n ι V Lc v₀}
    {ℓ : Label (Fin n) (binSnap n)} (hD : PendOp D) (h : (comp C).step D ℓ = some D') :
    C.step (projCfg D) (projLbl C D ℓ) = some (projCfg D') ∧ PendOp D' ∧
      LRel ℓ (projLbl C D ℓ) := by
  cases ℓ with
  | inv p o =>
    obtain ⟨hp, -, rfl⟩ := comp_step_inv h
    have hp' : (projCfg D).pend p = none := by simp [projCfg, hp]
    refine ⟨?_, ?_, ?_⟩
    · simp only [projLbl]
      rw [Impl.step_inv_eq_some hp' (hall _ _)]
      refine congrArg some (cfg_ext ?_ ?_ rfl)
      · funext q; by_cases hq : q = p
        · subst hq; simp [projCfg]
        · simp [projCfg, hq]
      · funext q; by_cases hq : q = p
        · subst hq; simp [projCfg]
        · simp [projCfg, hq]
    · intro q o' hq'
      by_cases hq : q = p
      · subst hq; simp_all
      · simp only [Function.update_of_ne hq] at hq' ⊢; exact hD q o' hq'
    · cases o with
      | update i v => exact LRel.upd p i v _
      | scan => exact LRel.scan p
  | tau p =>
    obtain ⟨hp, i, o, k, hc, rfl⟩ := comp_step_tau h
    have hp' : (projCfg D).pend p ≠ none := by simpa [projCfg] using hp
    refine ⟨?_, ?_, LRel.tau p⟩
    · simp only [projLbl]
      rw [Impl.step_tau_eq_some (I := C) hp' (i := i) (o := o) (k := k) hc]
      refine congrArg some (cfg_ext ?_ ?_ rfl)
      · funext q; by_cases hq : q = p
        · subst hq; simp [projCfg]
        · simp [projCfg, hq]
      · funext q; by_cases hq : q = p
        · subst hq; simp [projCfg]
        · simp [projCfg, hq]
    · intro q o' hq'
      by_cases hq : q = p
      · subst hq; simp only [Function.update_self]; exact hD q o' hq'
      · simp only [Function.update_of_ne hq]; exact hD q o' hq'
  | ret p r =>
    obtain ⟨hp, r', l, hc, rfl, rfl⟩ := comp_step_ret h
    have hp' : (projCfg D).pend p ≠ none := by simpa [projCfg] using hp
    have hl : projLbl C D (.ret p (outResp (D.loc p).op r')) = .ret p r' := by
      simp [projLbl, hc]
    rw [hl]
    refine ⟨?_, ?_, LRel.ret p _ r'⟩
    · rw [Impl.step_ret_eq_some (I := C) hp' (r := r') (l := l) hc]
      refine congrArg some (cfg_ext ?_ ?_ rfl)
      · funext q; by_cases hq : q = p
        · subst hq; simp [projCfg]
        · simp [projCfg, hq]
      · funext q; by_cases hq : q = p
        · subst hq; simp [projCfg]
        · simp [projCfg, hq]
    · intro q o' hq'
      by_cases hq : q = p
      · subst hq; simp at hq'
      · simp only [Function.update_of_ne hq] at hq' ⊢; exact hD q o' hq'

/-- The relation between a composed execution `α` (final configuration `D`) and an execution
`β` of `C`. -/
structure Sim (C : Impl batchedCounter (fun _ : ι => register V v₀) (Fin n) Lc)
    (α : List (Label (Fin n) (binSnap n))) (D : SCfg n ι V Lc v₀)
    (β : List (Label (Fin n) batchedCounter)) : Prop where
  run : C.run β = some (projCfg D)
  rel : List.Forall₂ LRel α β
  ops : ∀ p, opsOf β p = encOps p false (opsOf α p)
  resps : ∀ p, respsOf α p = List.zipWith outResp (opsOf α p) (respsOf β p)
  v : ∀ p, (D.loc p).v = lastValFrom false ((opsOf α p).take (respsOf α p).length)
  pendOp : PendOp D

theorem sim_step (hall : ∀ p o, C.allowed p o) {α : List (Label (Fin n) (binSnap n))}
    {D D' : SCfg n ι V Lc v₀} {β : List (Label (Fin n) batchedCounter)}
    {ℓ : Label (Fin n) (binSnap n)} (hα : (comp C).run α = some D) (hS : Sim C α D β)
    (h : (comp C).step D ℓ = some D') : Sim C (α ++ [ℓ]) D' (β ++ [projLbl C D ℓ]) := by
  obtain ⟨hst, hpo, hrel⟩ := step_sim hall hS.pendOp h
  have hrun : C.run (β ++ [projLbl C D ℓ]) = some (projCfg D') := by
    rw [Impl.run_concat, hS.run, Option.bind_some, hst]
  have hF : List.Forall₂ LRel (α ++ [ℓ]) (β ++ [projLbl C D ℓ]) :=
    List.rel_append hS.rel (List.Forall₂.cons hrel List.Forall₂.nil)
  have hlen : ∀ q, (respsOf α q).length = (respsOf β q).length :=
    fun q => (forall₂_counts hS.rel q).2.1
  have hle : ∀ q, (respsOf α q).length ≤ (opsOf α q).length :=
    fun q => (comp C).run_resps_le_ops hα q
  cases ℓ with
  | inv p o =>
    obtain ⟨hp, -, rfl⟩ := comp_step_inv h
    have hidle := (comp C).run_idle_counts hα hp
    refine ⟨hrun, hF, fun q => ?_, fun q => ?_, fun q => ?_, hpo⟩
    · by_cases hq : q = p
      · subst hq
        simp only [projLbl, opsOf_concat, Label.invOf_inv, ite_true, Option.toList_some]
        rw [hS.ops, encOps_concat, hS.v, ← hidle, List.take_length]
      · simp [projLbl, Ne.symm hq, hS.ops q]
    · by_cases hq : q = p
      · subst hq
        simp only [projLbl, respsOf_append_inv, opsOf_concat, Label.invOf_inv, ite_true,
          Option.toList_some]
        rw [zipWith_append_left_of_le _ (by rw [← hlen]; exact hle q)]
        exact hS.resps q
      · simp only [projLbl, respsOf_append_inv, opsOf_concat, Label.invOf_inv, Ne.symm hq,
          ite_false, Option.toList_none, List.append_nil]
        exact hS.resps q
    · by_cases hq : q = p
      · subst hq
        simp only [Function.update_self, respsOf_append_inv, opsOf_concat, Label.invOf_inv,
          ite_true, Option.toList_some]
        rw [List.take_append_of_le_length (hle q)]
        exact hS.v q
      · simp only [Function.update_of_ne hq, respsOf_append_inv, opsOf_concat, Label.invOf_inv,
          Ne.symm hq, ite_false, Option.toList_none, List.append_nil]
        exact hS.v q
  | tau p =>
    obtain ⟨hp, i, o, k, hc, rfl⟩ := comp_step_tau h
    refine ⟨hrun, hF, fun q => ?_, fun q => ?_, fun q => ?_, hpo⟩
    · simp only [projLbl, opsOf_append_tau]; exact hS.ops q
    · simp only [projLbl, opsOf_append_tau, respsOf_append_tau]; exact hS.resps q
    · simp only [opsOf_append_tau, respsOf_append_tau]
      by_cases hq : q = p
      · subst hq; simp only [Function.update_self]; exact hS.v q
      · simp only [Function.update_of_ne hq]; exact hS.v q
  | ret p r =>
    have hD := hS.pendOp
    obtain ⟨hp, r', l, hc, rfl, rfl⟩ := comp_step_ret h
    have hl : projLbl C D (.ret p (outResp (D.loc p).op r')) = .ret p r' := by
      simp [projLbl, hc]
    rw [hl] at hrun hF ⊢
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
    obtain ⟨-, -, hop⟩ := (comp C).run_pend_curOp hα ho
    have hopo : (D.loc p).op = o := hD p o ho
    have hlt : (respsOf α p).length < (opsOf α p).length := by
      have := (comp C).run_pend_counts hα hp; omega
    have hget : (opsOf α p)[(respsOf α p).length]'hlt = o := by
      simp only [opOf] at hop
      exact (List.getElem?_eq_some_iff.1 hop).2
    refine ⟨hrun, hF, fun q => ?_, fun q => ?_, fun q => ?_, hpo⟩
    · simp only [opsOf_append_ret]; exact hS.ops q
    · by_cases hq : q = p
      · subst hq
        simp only [opsOf_append_ret, respsOf_concat, Label.retOf_ret, ite_true,
          Option.toList_some]
        have hlt' : (respsOf β q).length < (opsOf α q).length := by rw [← hlen]; exact hlt
        have hget' : (opsOf α q)[(respsOf β q).length]'hlt' = o := by
          have := hop
          simp only [opOf, hlen q] at this
          exact (List.getElem?_eq_some_iff.1 this).2
        rw [zipWith_concat_right _ _ hlt', ← hS.resps q, hget', hopo]
      · simp only [opsOf_append_ret, respsOf_concat, Label.retOf_ret, Ne.symm hq, ite_false,
          Option.toList_none, List.append_nil]
        exact hS.resps q
    · by_cases hq : q = p
      · subst hq
        simp only [Function.update_self, opsOf_append_ret, respsOf_concat, Label.retOf_ret,
          ite_true, Option.toList_some, List.length_append, List.length_singleton]
        rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, lastValFrom_concat,
          hget, hopo, ← hS.v q]
      · simp only [Function.update_of_ne hq, opsOf_append_ret, respsOf_concat, Label.retOf_ret,
          Ne.symm hq, ite_false, Option.toList_none, List.append_nil]
        exact hS.v q

/-- Every composed execution has a corresponding execution of `C`. -/
theorem sim_of_run (hall : ∀ p o, C.allowed p o) {α : List (Label (Fin n) (binSnap n))}
    {D : SCfg n ι V Lc v₀} (h : (comp C).run α = some D) : ∃ β, Sim C α D β :=
  (comp C).run_induction (Q := fun α D => ∃ β, Sim C α D β)
    ⟨[], ⟨rfl, List.Forall₂.nil, fun _ => rfl, fun _ => rfl, fun _ => rfl,
      fun _ _ h => by simp [Impl.initCfg] at h⟩⟩
    (fun _ _ _ _ hα ⟨_, hS⟩ hs => ⟨_, sim_step hall hα hS hs⟩) h

/-! ## Transfer of the properties of `C` -/

/-- The composed algorithm has the snapshot's access discipline. -/
theorem comp_allowed (p : Fin n) (o : SnapOp n) : (comp C).allowed p o ↔ o.Allowed p :=
  Iff.rfl

/-- The composed algorithm writes the registers exactly as `C` does, so it uses them as SWMR
registers if `C` does. -/
theorem comp_swmr {owner : ι → Fin n} (hsw : C.SWMR owner) : (comp C).SWMR owner := by
  intro p s i o k h v hv
  cases hc : C.act p s.l with
  | access i' o' k' =>
    have hact : (comp C).act p s = .access i' o' (fun r => ⟨s.v, s.op, k' r⟩) := by
      simp [comp, hc]
    rw [hact] at h
    cases h
    exact hsw p s.l _ _ _ hc v hv
  | ret r l =>
    have hact : (comp C).act p s = .ret (outResp s.op r) ⟨newVal s.op s.v, s.op, l⟩ := by
      simp [comp, hc]
    rw [hact] at h; cases h

lemma pendOp_of_run (hall : ∀ p o, C.allowed p o) {α : List (Label (Fin n) (binSnap n))}
    {D : SCfg n ι V Lc v₀} (h : (comp C).run α = some D) : PendOp D :=
  (sim_of_run hall h).elim fun _ hS => hS.pendOp

/-- The projection of an infinite composed execution is an infinite execution of `C`. -/
def projInf (hall : ∀ p o, C.allowed p o) (e : (comp C).InfExec) : C.InfExec where
  cfg m := projCfg (e.cfg m)
  lbl m := projLbl C (e.cfg m) (e.lbl m)
  cfg_zero := by rw [e.cfg_zero]; rfl
  step_eq m := (step_sim hall (pendOp_of_run hall (e.run_pre m)) (e.step_eq m)).1

/-- Wait-freedom transfers to the composed algorithm. -/
theorem comp_waitFree (hall : ∀ p o, C.allowed p o) (hwf : C.WaitFree) : (comp C).WaitFree := by
  intro e p m hpend
  obtain ⟨N, hN⟩ := hwf (projInf hall e) p m (fun m' hm' => by
    simpa [projInf, projCfg] using hpend m' hm')
  refine ⟨N, fun m' hm' heq => hN m' hm' ?_⟩
  simp [projInf, heq, projLbl]

/-- Linearizability transfers to the composed algorithm. -/
theorem comp_linearizable (hall : ∀ p o, C.allowed p o) (hlin : C.Linearizable) :
    (comp C).Linearizable := by
  obtain ⟨hC, hhC⟩ := hlin
  refine Impl.linearizable_of_run fun α D h => ?_
  obtain ⟨β, hS⟩ := sim_of_run hall h
  have hβ : C.Valid β := ⟨_, hS.run⟩
  exact ⟨_, isLinearization_lift hS.rel hS.ops hS.resps
    (fun p o ho => (comp C).allowed_of_mem_opsOf ⟨D, h⟩ ho) hβ.wellFormed (hhC β hβ)⟩

/-- The step bound for updates transfers: a composed update performs exactly the accesses of
the corresponding update of `C`. -/
theorem comp_stepsLE (hall : ∀ p o, C.allowed p o) {b : ℕ}
    (hb : C.StepsLE (fun o => ∃ v, o = .update v) b) :
    (comp C).StepsLE (fun o => ∃ i v, o = .update i v) b := by
  rintro α p o γ ⟨i, v, rfl⟩ ⟨D, hD⟩ hret
  obtain ⟨β, hS⟩ := sim_of_run hall hD
  have hF := hS.rel
  have h1 : List.Forall₂ LRel α (β.take α.length) := by
    simpa using List.forall₂_take α.length hF
  have h2 : List.Forall₂ LRel (.inv p (.update i v) :: γ) (β.drop α.length) := by
    simpa using List.forall₂_drop α.length hF
  generalize hd : β.drop α.length = rest at h2
  cases h2 with
  | cons hl hγ =>
    rename_i ℓ' γ'
    cases hl with
    | upd _ _ _ w =>
      have hβ : β = β.take α.length ++ .inv p (.update w) :: γ' := by
        rw [← hd, List.take_append_drop]
      have hv : C.Valid (β.take α.length ++ .inv p (.update w) :: γ') := by
        rw [← hβ]; exact ⟨_, hS.run⟩
      have := hb _ p _ γ' ⟨w, rfl⟩ hv (not_ret_of_forall₂ hγ hret)
      rw [(forall₂_counts hγ p).2.2]
      exact this

end Reduction

open Reduction in
/-- **Theorem 3** (conditional on the Israeli–Shirazi lower bound [21], `ISLowerBound n b`): no
linearizable, wait-free implementation of a batched counter for `n` processes from SWMR registers
(`owner i` is the only writer of register `i`) has all its `update`s performing at most `b`
base-object accesses. With [21] (`ISLowerBound n b` for `b = Θ(n)`), the step complexity of
`update` is `Ω(n)`. -/
theorem theorem3 {n b : ℕ} (hIS : ISLowerBound n b) {ι V Lc : Type} [DecidableEq ι] {v₀ : V}
    (owner : ι → Fin n) (C : Impl batchedCounter (fun _ : ι => register V v₀) (Fin n) Lc)
    (hall : ∀ p o, C.allowed p o) (hsw : C.SWMR owner) (hwf : C.WaitFree)
    (hlin : C.Linearizable) : ¬ C.StepsLE (fun o => ∃ v, o = .update v) b := fun hb =>
  hIS ι V (CompLoc n Lc) v₀ owner (comp C) comp_allowed (comp_swmr hsw)
    (comp_waitFree hall hwf) (comp_linearizable hall hlin) (comp_stepsLE hall hb)

end Podc.IntermediateValueLin
