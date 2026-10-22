import Papers.PODC2025.ByzantineSWMRRegisters.SigTest

/-!
# The objects of Hu–Toueg (PODC 2025)

Sequential specifications (as CSLib `ObjSpec`s) and invocation disciplines (`allowed`) of

* the one-shot **test-or-set** object (Definition 26), setter `s`;
* the SWMR **verifiable register** (Definition 10), writer `w`, values `V`, initial value `v₀`;
* the SWMR **authenticated register** (Definition 15);
* the SWMR **sticky register** (Definition 21), initially `⊥` (`none`);

and their `SigTest` structures (`tosSig`, `verSig v`, `authSig v`, `stickySig v`), which
encode the validity/unforgeability/relay properties (Observations 11–13, 16–18, 22–24, 27).
Also the SWMR register base objects (`swmrAccess`, `swmr_singleWriter`).

Sets of written/signed values are `Set V`; the specifications decide membership classically.
-/

namespace Podc.ByzantineSWMRRegisters

open Cslib.SharedMemory Cslib.SharedMemory.Byzantine

noncomputable section

open Classical

variable {P : Type}

/-! ## Test-or-set -/

/-- Operations of test-or-set. -/
inductive TosOp where
  | set
  | test
  deriving DecidableEq

/-- Responses of test-or-set: `done` (for `Set`) or a bit (for `Test`). -/
inductive TosResp where
  | done
  | bit (b : Bool)
  deriving DecidableEq

/-- Definition 26: test-or-set; the state records whether a `Set` has occurred. -/
abbrev testOrSet : ObjSpec where
  State := Bool
  Op := TosOp
  Resp := TosResp
  init := false
  δ q
    | .set => (true, .done)
    | .test => (q, .bit q)

/-- `Set` only by the setter `s`, `Test` by every other process. -/
def tosAllowed (s : P) (p : P) : TosOp → Prop
  | .set => p = s
  | .test => p ≠ s

/-- One-shot use: every process invokes at most one operation. -/
def oneShot (_p : P) (os : List TosOp) : Prop := os.length ≤ 1

/-- Test-or-set as a `SigTest` (Observation 27). -/
def tosSig (s : P) : SigTest testOrSet (tosAllowed s) s where
  setOps := [.set]
  testOp := .test
  pos r := r = .bit true
  R k q := k = 0 ∨ q = true
  setOps_ne_nil := by simp
  R_zero _ := Or.inl rfl
  R_stable k q o h := by
    cases o <;> simp_all [testOrSet]
  R_succ k hk q _ := by
    simp only [List.length_singleton, Nat.lt_one_iff] at hk; subst hk
    simp [testOrSet]
  pos_iff q := by simp [testOrSet]
  not_R_init := by simp [testOrSet]
  only_setter q o p h1 h2 h3 := by
    cases o
    · exact h3
    · simp_all [testOrSet]
  allowed_set o ho := by simp at ho; subst ho; rfl
  allowed_test p hp := hp

/-! ## Verifiable register -/

/-- Operations of the verifiable register. -/
inductive VerOp (V : Type) where
  | read
  | write (v : V)
  | sign (v : V)
  | verify (v : V)

/-- Responses: `done` (write), a value (read), a boolean (sign: success/fail; verify). -/
inductive RegResp (V : Type) where
  | done
  | val (v : V)
  | bool (b : Bool)

/-- States of the verifiable register: current value, written values, signed values. -/
structure VerState (V : Type) where
  /-- The current value. -/
  cur : V
  /-- The values written so far. -/
  written : Set V
  /-- The values signed so far (successful `Sign`s). -/
  signed : Set V

/-- Definition 10: the SWMR verifiable register with initial value `v₀`. -/
abbrev verReg (V : Type) (v₀ : V) : ObjSpec where
  State := VerState V
  Op := VerOp V
  Resp := RegResp V
  init := ⟨v₀, ∅, ∅⟩
  δ q
    | .read => (q, .val q.cur)
    | .write v => (⟨v, insert v q.written, q.signed⟩, .done)
    | .sign v => if v ∈ q.written then (⟨q.cur, q.written, insert v q.signed⟩, .bool true)
        else (q, .bool false)
    | .verify v => (q, .bool (decide (v ∈ q.signed)))

/-- `Write` and `Sign` by the writer `w`, `Read` and `Verify` by the readers. -/
def verAllowed {V : Type} (w : P) (p : P) : VerOp V → Prop
  | .write _ => p = w
  | .sign _ => p = w
  | .read => p ≠ w
  | .verify _ => p ≠ w

/-- The verifiable register as a `SigTest`: sign = `Write(v); Sign(v)`, test = `Verify(v)`
(Observations 11–13). -/
def verSig {V : Type} (v₀ : V) (w : P) (v : V) : SigTest (verReg V v₀) (verAllowed w) w where
  setOps := [.write v, .sign v]
  testOp := .verify v
  pos r := r = .bool true
  R k q := k = 0 ∨ (k = 1 ∧ v ∈ q.written) ∨ (2 ≤ k ∧ v ∈ q.signed)
  setOps_ne_nil := by simp
  R_zero _ := Or.inl rfl
  R_stable k q o h := by
    cases o with
    | read => exact h
    | write u => rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
    | sign u =>
      simp only [verReg]; split_ifs
      · rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
      · exact h
    | verify u => exact h
  R_succ k hk q h := by
    simp only [List.length_cons, List.length_nil] at hk
    obtain _ | _ | k := k
    · simp [verReg]
    · rcases h with h | ⟨-, h⟩ | ⟨h, -⟩
      · simp at h
      · simp [verReg, h]
      · omega
    · omega
  pos_iff q := by simp [verReg]
  not_R_init := by simp [verReg]
  only_setter q o p h1 h2 h3 := by
    cases o with
    | read => exact absurd h2 h1
    | write u => simp_all [verReg]
    | sign u => exact h3
    | verify u => exact absurd h2 h1
  allowed_set o ho := by simp at ho; rcases ho with rfl | rfl <;> rfl
  allowed_test p hp := hp

/-! ## Authenticated register -/

/-- Operations of the authenticated register. -/
inductive AuthOp (V : Type) where
  | read
  | write (v : V)
  | verify (v : V)

/-- States of the authenticated register: current value and the values written so far
together with the initial value. -/
structure AuthState (V : Type) where
  /-- The current value. -/
  cur : V
  /-- `v₀` and the values written so far. -/
  written : Set V

/-- Definition 15: the SWMR authenticated register with initial value `v₀`. -/
abbrev authReg (V : Type) (v₀ : V) : ObjSpec where
  State := AuthState V
  Op := AuthOp V
  Resp := RegResp V
  init := ⟨v₀, {v₀}⟩
  δ q
    | .read => (q, .val q.cur)
    | .write v => (⟨v, insert v q.written⟩, .done)
    | .verify v => (q, .bool (decide (v ∈ q.written)))

/-- `Write` by the writer `w`, `Read` and `Verify` by the readers. -/
def authAllowed {V : Type} (w : P) (p : P) : AuthOp V → Prop
  | .write _ => p = w
  | .read => p ≠ w
  | .verify _ => p ≠ w

/-- The authenticated register as a `SigTest`: sign = `Write(v)`, test = `Verify(v)`, for a value
`v ≠ v₀` (Observations 16–18). -/
def authSig {V : Type} {v₀ : V} (w : P) {v : V} (hv : v ≠ v₀) :
    SigTest (authReg V v₀) (authAllowed w) w where
  setOps := [.write v]
  testOp := .verify v
  pos r := r = .bool true
  R k q := k = 0 ∨ v ∈ q.written
  setOps_ne_nil := by simp
  R_zero _ := Or.inl rfl
  R_stable k q o h := by
    cases o with
    | read => exact h
    | write u => rcases h with h | h <;> simp_all
    | verify u => exact h
  R_succ k hk q h := by
    simp only [List.length_singleton, Nat.lt_one_iff] at hk; subst hk
    simp [authReg]
  pos_iff q := by simp [authReg]
  not_R_init := by simp [authReg, hv]
  only_setter q o p h1 h2 h3 := by
    cases o with
    | read => exact absurd h2 h1
    | write u => exact h3
    | verify u => exact absurd h2 h1
  allowed_set o ho := by simp at ho; subst ho; rfl
  allowed_test p hp := hp

/-! ## Sticky register -/

/-- Operations of the sticky register. -/
inductive StickyOp (V : Type) where
  | read
  | write (v : V)

/-- Definition 21: the SWMR sticky register, initially `⊥ = none`; only the first write takes
effect. -/
abbrev stickyReg (V : Type) : ObjSpec where
  State := Option V
  Op := StickyOp V
  Resp := RegResp (Option V)
  init := none
  δ q
    | .read => (q, .val q)
    | .write v => (some (q.getD v), .done)

/-- `Write` by the writer `w`, `Read` by the readers. -/
def stickyAllowed {V : Type} (w : P) (p : P) : StickyOp V → Prop
  | .write _ => p = w
  | .read => p ≠ w

/-- The sticky register as a `SigTest`: sign = `Write(v)`, test = `Read`, positive iff the read
returns a value `≠ ⊥` (Observations 22–24). -/
def stickySig {V : Type} (w : P) (v : V) : SigTest (stickyReg V) (stickyAllowed w) w where
  setOps := [.write v]
  testOp := .read
  pos r := r ≠ .val none
  R k q := k = 0 ∨ q.isSome
  setOps_ne_nil := by simp
  R_zero _ := Or.inl rfl
  R_stable k q o h := by
    cases o with
    | read => exact h
    | write u => right; simp
  R_succ k hk q h := by
    simp only [List.length_singleton, Nat.lt_one_iff] at hk; subst hk
    simp [stickyReg]
  pos_iff q := by cases q <;> simp [stickyReg]
  not_R_init := by simp [stickyReg]
  only_setter q o p h1 h2 h3 := by
    cases o with
    | read => exact absurd h2 h1
    | write u => exact h3
  allowed_set o ho := by simp at ho; subst ho; rfl
  allowed_test p hp := hp

lemma tosSig_admits (s : P) : (tosSig s).Admits oneShot := by
  refine ⟨fun k => ?_, fun p _ => ⟨by simp [oneShot], by simp [oneShot, tosSig]⟩⟩
  simp only [oneShot, tosSig, List.length_take, List.length_singleton]; omega

lemma sigTest_admits_true {A : ObjSpec} {allowed : P → A.Op → Prop} {s : P}
    (T : SigTest A allowed s) : T.Admits (fun _ _ => True) :=
  ⟨fun _ => trivial, fun _ _ => ⟨trivial, trivial⟩⟩

/-! ## SWMR registers as base objects -/

/-- Access rights for SWMR registers `i : ι` owned by `owner i`: everybody may read, only the
owner may write. -/
def swmrAccess {ι : Type} {Val : ι → Type} {v₀ : (i : ι) → Val i} (owner : ι → P) :
    Access P (fun i => register (Val i) (v₀ i)) :=
  fun p i o => match o with
    | .read => True
    | .write _ => owner i = p

lemma swmr_singleWriter {ι : Type} {Val : ι → Type} {v₀ : (i : ι) → Val i} (owner : ι → P) :
    SingleWriter (swmrAccess (v₀ := v₀) owner) owner where
  readOnly p i o hacc hne q := by
    cases o with
    | read => rfl
    | write u => exact absurd hacc hne
  overwrite i q q' := ⟨.write q', rfl, rfl⟩

end

end Podc.ByzantineSWMRRegisters
