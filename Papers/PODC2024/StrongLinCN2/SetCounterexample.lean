import Podc.StrongLin.Basic
import Podc.SharedMemory.Objects

/-!
# Algorithm 2 (a set from test&set) is not strongly linearizable

Attiya, Castañeda and Enea, *Strong Linearizability using Primitives with Consensus Number 2*
(PODC 2024), Section 4.3, Algorithm 2: a set (`Put(x)` / `Take()`, where `Take` removes and
returns an arbitrary element, or `EMPTY`) implemented from an infinite array `Items` of
read/write registers (initially `⊥`), an infinite array `TS` of test&set objects (initially `0`)
and a readable fetch&increment `Max` (initially `1`):

```
Put(x):  max = Max.fetch&increment(); Items[max].write(x); return OK
Take():  taken_old = 0; max_old = 0
         while true:
            taken_new = 0
            max_new = Max.read() - 1
            for c in 1..max_new:
               x = Items[c].read()
               if x ≠ ⊥ then if TS[c].test&set() == 0 then return x
            if taken_new == taken_old ∧ max_new == max_old then return EMPTY
            taken_old = taken_new; max_old = max_new
```

The pseudocode never increments `taken_new`; the (probably intended) reading where `taken_new` is
incremented whenever `TS[c].test&set()` returns `1` is modelled too: the parameter
`countTaken : Bool` of `alg2` selects the reading. The counterexample works for both.

## The counterexample

Three processes: `0` does `put 1`, `1` does `put 2`, `2` does `take`.
In the prefix `pre`, both puts perform their fetch&increment (`Max = 3`), the take performs a
full first scan (both items `⊥`; `max` changed from `0` to `2`, so it scans again), reads `Max`
again and reads `Items[1] = ⊥`; then `put 1` writes `Items[1]` and **completes**.
* Extension `exB`: the take reads `Items[2] = ⊥`, the double-collect test succeeds and it returns
  `EMPTY`. Since `put 1` completed before, the take must be linearized *before* `put 1`, hence
  already in the linearization of `pre`, with response `EMPTY`.
* Extension `exA`: `put 2` writes `Items[2]`, the take reads it, wins `TS[2]` and returns `2`.
  The linearization of `pre` (a prefix of that of `exA`) already contains the take with response
  `EMPTY`, a contradiction.

Hence no prefix-closed linearization function exists (`alg2_not_stronglyLinearizable`).
(We do not prove anything about plain linearizability of Algorithm 2.)

## Modelling

* The implemented set is the nondeterministic sequential specification `setSpec`
  (`NSpec`, states `Set ℕ`, `take` returns any element, or `empty` on the empty set).
  The `ObjSpec` `setOps` is only used for its operation/response types: its transition function
  is a dummy and is **never used** (`NStronglyLinearizable` only refers to `setSpec`).
* Items are natural numbers; `⊥` is `none`. Processes: `Fin 3`.
* One base-object access per step; local computation (loop bounds, the final test of an
  iteration) is folded into the transitions (`next`).
-/

namespace StrongLinCN2.SetCE

open Cslib.SharedMemory

/-! ## The set object -/

/-- Set operations. -/
inductive SetOp where
  | put (x : ℕ)
  | take
  deriving DecidableEq

/-- Set responses. -/
inductive SetResp where
  | ok
  | empty
  | item (x : ℕ)
  deriving DecidableEq

/-- The implemented object: only its operation and response types are used. The transition
function is a dummy, never used: the sequential specification is `setSpec`. -/
abbrev setOps : ObjSpec := ⟨Unit, SetOp, SetResp, (), fun _ _ => ((), .ok)⟩

/-- Transitions of the sequential set: `put x` adds `x` and returns `ok`; `take` returns `empty`
on the empty set, otherwise removes and returns an arbitrary element. -/
def setStep : Set ℕ → SetOp → SetResp → Set ℕ → Prop
  | q, .put x, r, q' => r = .ok ∧ q' = insert x q
  | q, .take, r, q' => (q = ∅ ∧ r = .empty ∧ q' = q) ∨ (∃ x ∈ q, r = .item x ∧ q' = q \ {x})

/-- The nondeterministic sequential specification of a set (initially empty). -/
def setSpec : NSpec SetOp SetResp where
  State := Set ℕ
  init := ∅
  Step := setStep

/-! ## Algorithm 2 -/

/-- Base objects: registers `Items[c]`, test&sets `TS[c]`, the readable fetch&increment `Max`. -/
inductive Obj where
  | items (c : ℕ)
  | ts (c : ℕ)
  | max
  deriving DecidableEq

/-- Types of the base objects. -/
abbrev base : Obj → ObjSpec
  | .items _ => register (Option ℕ) none
  | .ts _ => tasObj
  | .max => rfaiObj

/-- Local states (program counters with local variables). `tO`/`mO` are `taken_old`/`max_old`,
`tN`/`mN` are `taken_new`/`max_new`, `c` the loop index. -/
inductive Loc where
  | idle
  | putFAI (x : ℕ)
  | putWrite (x m : ℕ)
  | retOk
  | readMax (tO mO : ℕ)
  | readItem (tO mO tN mN c : ℕ)
  | tas (tO mO tN mN c x : ℕ)
  | retEmpty
  | retItem (x : ℕ)

/-- Continue the scan at index `c` (or finish the iteration: the double-collect test). -/
def next (tO mO tN mN c : ℕ) : Loc :=
  if c ≤ mN then .readItem tO mO tN mN c
  else if tN = tO ∧ mN = mO then .retEmpty else .readMax tN mN

/-- The program. `countTaken` selects whether `taken_new` is incremented when a test&set
returns `1`. -/
def act (countTaken : Bool) : Loc → Action setOps base Loc
  | .idle => .ret .ok .idle
  | .putFAI x => .access .max FAIOp.fai (fun m => .putWrite x m)
  | .putWrite x m => .access (.items m) (RWOp.write (some x)) (fun _ => .retOk)
  | .retOk => .ret .ok .idle
  | .readMax tO mO => .access .max FAIOp.read (fun v => next tO mO 0 (v - 1) 1)
  | .readItem tO mO tN mN c => .access (.items c) RWOp.read (fun v =>
      match v with
      | none => next tO mO tN mN (c + 1)
      | some x => .tas tO mO tN mN c x)
  | .tas tO mO tN mN c x => .access (.ts c) () (fun b =>
      if b then next tO mO (if countTaken then tN + 1 else tN) mN (c + 1) else .retItem x)
  | .retEmpty => .ret .empty .idle
  | .retItem x => .ret (.item x) .idle

/-- Invocation. -/
def invoke : SetOp → Loc
  | .put x => .putFAI x
  | .take => .readMax 0 0

/-- Initial memory: `Items[c] = ⊥`, `TS[c] = 0`, `Max = 1`. -/
def memInit : (i : Obj) → (base i).State
  | .items _ => (none : Option ℕ)
  | .ts _ => false
  | .max => (1 : ℕ)

/-- Algorithm 2 of the paper, for three processes. -/
def alg2 (countTaken : Bool) : Impl setOps base (Fin 3) Loc where
  memInit := memInit
  locInit _ := .idle
  invoke _ _ o := invoke o
  act _ l := act countTaken l

/-! ## Computable steps -/

abbrev Cfg := Config setOps base (Fin 3) Loc
abbrev Lbl := Label (Fin 3) setOps

/-- A computable copy of `Impl.step` for `alg2` (`Impl.step` decides `allowed` classically). -/
def cstep (countTaken : Bool) (C : Cfg) : Lbl → Option Cfg
  | .inv p o =>
    if C.pend p = none then
      some { C with pend := Function.update C.pend p (some o),
                    loc := Function.update C.loc p (invoke o) }
    else none
  | .tau p =>
    if C.pend p = none then none else
    match act countTaken (C.loc p) with
    | .access i o k =>
      some { C with mem := Function.update C.mem i ((base i).δ (C.mem i) o).1,
                    loc := Function.update C.loc p (k ((base i).δ (C.mem i) o).2) }
    | .ret _ _ => none
  | .ret p r =>
    if C.pend p = none then none else
    match act countTaken (C.loc p) with
    | .access _ _ _ => none
    | .ret r' l =>
      if r = r' then
        some { C with pend := Function.update C.pend p none, loc := Function.update C.loc p l }
      else none

lemma step_eq_cstep (countTaken : Bool) (C : Cfg) (ℓ : Lbl) :
    (alg2 countTaken).step C ℓ = cstep countTaken C ℓ := by
  cases ℓ with
  | inv p o =>
    simp only [Impl.step, cstep, alg2, and_true]
  | tau p =>
    simp only [Impl.step, cstep, alg2]
    split_ifs
    · rfl
    · generalize act countTaken (C.loc p) = a
      cases a <;> rfl
  | ret p r =>
    simp only [Impl.step, cstep, alg2]
    split_ifs
    · rfl
    · generalize act countTaken (C.loc p) = a
      cases a
      · rfl
      · simp only

/-- Computable run. -/
def crunFrom (countTaken : Bool) (C : Cfg) : List Lbl → Option Cfg
  | [] => some C
  | ℓ :: α => (cstep countTaken C ℓ).bind (fun C' => crunFrom countTaken C' α)

lemma runFrom_eq_crunFrom (countTaken : Bool) (C : Cfg) (α : List Lbl) :
    (alg2 countTaken).runFrom C α = crunFrom countTaken C α := by
  induction α generalizing C with
  | nil => rfl
  | cons ℓ α ih => simp only [Impl.runFrom_cons, crunFrom, step_eq_cstep, ih]

lemma valid_of_crun (countTaken : Bool) (α : List Lbl)
    (h : (crunFrom countTaken (alg2 countTaken).initCfg α).isSome = true) :
    (alg2 countTaken).Valid α := by
  rw [Impl.Valid, Impl.run, runFrom_eq_crunFrom]
  exact Option.isSome_iff_exists.1 h

/-! ## The executions -/

/-- The common prefix: both puts perform their fetch&increment (`Max = 3`); the take reads
`Max`, scans `Items[1]`, `Items[2]` (both `⊥`; `max_new = 2 ≠ max_old = 0`, so it iterates
again), reads `Max` again and reads `Items[1] = ⊥`; then `put 1` writes `Items[1]` and returns. -/
def pre : List Lbl :=
  [.inv 0 (.put 1), .tau 0, .inv 1 (.put 2), .tau 1, .inv 2 .take,
   .tau 2, .tau 2, .tau 2, .tau 2, .tau 2, .tau 0, .ret 0 .ok]

/-- Extension B: the take returns `EMPTY`. -/
def exB : List Lbl := pre ++ [.tau 2, .ret 2 .empty]

/-- Extension A: `put 2` completes and the take returns `2`. -/
def exA : List Lbl := pre ++ [.tau 1, .ret 1 .ok, .tau 2, .tau 2, .ret 2 (.item 2)]

theorem valid_B (countTaken : Bool) : (alg2 countTaken).Valid exB := by
  apply valid_of_crun; cases countTaken <;> decide +kernel

theorem valid_A (countTaken : Bool) : (alg2 countTaken).Valid exA := by
  apply valid_of_crun; cases countTaken <;> decide +kernel

theorem valid_pre (countTaken : Bool) : (alg2 countTaken).Valid pre :=
  (alg2 countTaken).valid_of_prefix (valid_B countTaken) (List.prefix_append _ _)

theorem pre_prefix_B : pre <+: exB := List.prefix_append _ _

theorem pre_prefix_A : pre <+: exA := List.prefix_append _ _

/-! ## Facts about the histories -/

/-- `put 1` (instance `(0, 0)`) has completed in the prefix. -/
theorem completed_pre_put : Completed pre (0, 0) := by unfold Completed; decide

/-- In `exB` the take (instance `(2, 0)`) returns `empty`. -/
theorem respOf_B_take : respOf exB (2, 0) = some .empty := by decide

/-- In `exA` the take (instance `(2, 0)`) returns `item 2`. -/
theorem respOf_A_take : respOf exA (2, 0) = some (.item 2) := by decide

theorem completed_B_take : Completed exB (2, 0) := by unfold Completed; decide

theorem opOf_B_put : opOf exB (0, 0) = some (.put 1) := by decide

theorem opOf_B_take : opOf exB (2, 0) = some .take := by decide

theorem opsOf_B : opsOf exB = fun p => if p = 2 then [.take] else [.put (p.val + 1)] := by
  funext p; fin_cases p <;> rfl

/-- The only `take` instance invoked in `exB` is `(2, 0)`. -/
theorem eq_of_opOf_B_take {x : OpId (Fin 3)} (h : opOf exB x = some .take) : x = (2, 0) := by
  obtain ⟨p, k⟩ := x
  simp only [opOf, opsOf_B] at h
  fin_cases p <;> rcases k with _ | k <;> simp_all

/-! ## Legality of sequential set histories -/

/-- From a state containing `x`, a legal sequence in which every `take` returns `empty` contains
no `take` at all. -/
lemma legal_no_take {q : Set ℕ} {x : ℕ} {l : List (SetOp × SetResp)} (hl : setSpec.Legal q l)
    (hx : x ∈ q) (hno : ∀ z ∈ l, z.1 = .take → z.2 = .empty) : ∀ z ∈ l, z.1 ≠ .take := by
  induction l generalizing q with
  | nil => simp
  | cons z l ih =>
    obtain ⟨o, r⟩ := z
    obtain ⟨q', hst, hl'⟩ := hl
    have hno' : ∀ z ∈ l, z.1 = .take → z.2 = .empty := fun z hz => hno z (by simp [hz])
    cases o with
    | put y =>
      obtain ⟨-, rfl⟩ := hst
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · simp
      · exact ih hl' (Set.mem_insert_of_mem _ hx) hno' z hz
    | take =>
      have hr : r = .empty := hno (.take, r) (by simp) rfl
      subst hr
      rcases hst with ⟨rfl, -, -⟩ | ⟨y, -, h, -⟩
      · exact absurd hx (Set.notMem_empty x)
      · cases h

/-- In a legal sequential set history in which every `take` returns `empty`, no `take` follows a
`put`. -/
lemma legal_put_take {q : Set ℕ} {l : List (SetOp × SetResp)} (hl : setSpec.Legal q l)
    (hno : ∀ z ∈ l, z.1 = .take → z.2 = .empty) {x : ℕ} {r r' : SetResp}
    (hs : [(SetOp.put x, r), (SetOp.take, r')].Sublist l) : False := by
  induction l generalizing q with
  | nil => simp at hs
  | cons z l ih =>
    obtain ⟨q', hst, hl'⟩ := hl
    have hno' : ∀ z ∈ l, z.1 = .take → z.2 = .empty := fun z hz => hno z (by simp [hz])
    cases hs with
    | cons _ hs => exact ih hl' hno' hs
    | cons_cons _ hs =>
      obtain ⟨-, rfl⟩ := hst
      exact legal_no_take hl' (Set.mem_insert x q) hno' _ (List.singleton_sublist.1 hs) rfl

/-! ## The main theorem -/

/-- **Algorithm 2 (set from test&set, Section 4.3) is not strongly linearizable**, for both readings
of the `taken_new` counter. -/
theorem alg2_not_stronglyLinearizable (countTaken : Bool) :
    ¬ (alg2 countTaken).NStronglyLinearizable setSpec := by
  rintro ⟨h, hlin, hpre⟩
  have hB := hlin _ (valid_B countTaken)
  have hA := hlin _ (valid_A countTaken)
  have hP := hlin _ (valid_pre countTaken)
  obtain ⟨MB, hMB⟩ := hpre _ _ (valid_B countTaken) pre_prefix_B
  obtain ⟨MA, hMA⟩ := hpre _ _ (valid_A countTaken) pre_prefix_A
  -- the take is linearized in the prefix
  have key : ∃ y ∈ h pre, y.1 = (2, 0) := by
    by_contra hn
    obtain ⟨y0, hy0, hy0id⟩ := List.mem_map.1 (hP.complete _ completed_pre_put)
    obtain ⟨y2, hy2, hy2id⟩ := List.mem_map.1 (hB.complete _ completed_B_take)
    have hy0B : y0 ∈ h exB := hMB ▸ List.mem_append_left _ hy0
    have y2M : y2 ∈ MB := by
      rw [← hMB] at hy2
      rcases List.mem_append.1 hy2 with h2 | h2
      · exact absurd ⟨y2, h2, hy2id⟩ hn
      · exact h2
    have e0 : y0.2.1 = .put 1 := by
      have := hB.op_eq y0 hy0B
      rw [hy0id, opOf_B_put] at this
      exact (Option.some.inj this).symm
    have e2 : y2.2.1 = .take := by
      have := hB.op_eq y2 hy2
      rw [hy2id] at this
      exact Option.some.inj (this.symm.trans opOf_B_take)
    have hno : ∀ z ∈ (h exB).map Prod.snd, z.1 = .take → z.2 = .empty := by
      intro z hz ht
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
      have hop := hB.op_eq y hy
      rw [ht] at hop
      exact hB.resp_eq y hy _ (by rw [eq_of_opOf_B_take hop]; exact respOf_B_take)
    have hsub : [y0.2, y2.2].Sublist ((h exB).map Prod.snd) := by
      rw [← hMB, List.map_append]
      exact (List.singleton_sublist.2 (List.mem_map_of_mem hy0)).append
        (List.singleton_sublist.2 (List.mem_map_of_mem y2M))
    obtain ⟨i0, o0, r0⟩ := y0
    obtain ⟨i2, o2, r2⟩ := y2
    simp only at e0 e2
    subst e0 e2
    exact legal_put_take hB.legal hno hsub
  obtain ⟨y, hy, hyid⟩ := key
  have r1 := hB.resp_eq y (hMB ▸ List.mem_append_left _ hy) _ (by rw [hyid]; exact respOf_B_take)
  have r2 := hA.resp_eq y (hMA ▸ List.mem_append_left _ hy) _ (by rw [hyid]; exact respOf_A_take)
  rw [r1] at r2
  cases r2

end StrongLinCN2.SetCE
