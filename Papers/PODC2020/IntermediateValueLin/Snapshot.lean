import Papers.PODC2020.IntermediateValueLin.Objects
import Mathlib.Algebra.BigOperators.Fin

/-!
# Binary snapshot from a batched counter (Algorithm 3, Invariant 1, Lemmas 3 and 4)

Rinberg–Keidar, PODC 2020, Section 6.2.

* `binSnap n`: the *binary snapshot* object with `n` components: `update i b` sets component `i`
  to `b` (and returns a dummy), `scan` returns all components. `SnapOp.Allowed p`: process `p`
  may only update its own component `p` (and may scan).
* `alg3 n`: **Algorithm 3**, implementing `binSnap n` from one (atomic) batched counter `BC`.
  Process `p` keeps its last written bit `v_p`; `update_p(v)` returns at once if `v = v_p`
  (line 4), otherwise it adds `2^p` (`0 → 1`) or `2^n - 2^p` (`1 → 0`) to the counter; `scan`
  reads the counter and returns its bits `0, …, n-1`.
* `alg3_invariant1` (**Invariant 1**, generalized to concurrent executions): for every execution
  there is a linearization `L` (by the linearization points of Lemma 4) such that the counter
  holds `c · 2^n + ∑ᵢ vᵢ 2^i`, `vᵢ` the parameter of the last `update_i` in `L` (`0` if none).
* `binSnap_scan_resp` (**Lemma 3**, in the form used by Lemma 4: legality of the linearization).
* `alg3_linearizable` (**Lemma 4**), `alg3_waitFree`, `alg3_update_steps` (an update performs at
  most one counter access), `alg3_scan_steps` (a scan performs at most one access).

The arithmetic of Invariant 1 is `testBit_add_delta`: adding `2^p` to a counter whose bit `p` is
`0`, or `2^n - 2^p` to one whose bit `p` is `1`, flips exactly bit `p` among the bits `< n`.
-/

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

namespace Podc.IntermediateValueLin

/-! ## The binary snapshot object -/

/-- Operations of the binary snapshot with `n` components. -/
inductive SnapOp (n : ℕ) where
  /-- `update_i(b)`: set component `i` to `b`. -/
  | update (i : Fin n) (b : Bool)
  /-- `scan()`: return all components. -/
  | scan
  deriving DecidableEq

/-- The binary snapshot object (Section 6.2): the state is a vector of `n` bits, initially all
`0` (`false`); `update i b` sets component `i` to `b` and returns the dummy all-`false` vector,
`scan` returns the state. -/
abbrev binSnap (n : ℕ) : ObjSpec where
  State := Fin n → Bool
  Op := SnapOp n
  Resp := Fin n → Bool
  init := fun _ => false
  δ s
    | .update i b => (Function.update s i b, fun _ => false)
    | .scan => (s, s)

/-- Single-writer discipline of the snapshot: process `p` may update only component `p`; every
process may scan. -/
def SnapOp.Allowed {n : ℕ} (p : Fin n) : SnapOp n → Prop
  | .update i _ => i = p
  | .scan => True

/-- One step of "the last value written to component `i`". -/
def lastUpdStep {n : ℕ} (i : Fin n) (b : Bool) : SnapOp n → Bool
  | .update j v => if j = i then v else b
  | .scan => b

/-- The parameter of the last `update_i` in a sequence of operations (`false` if there is none),
the paper's `vᵢ`. -/
def lastUpd {n : ℕ} (i : Fin n) (os : List (SnapOp n)) : Bool := os.foldl (lastUpdStep i) false

lemma binSnap_runOps_apply {n : ℕ} (σ : Fin n → Bool) (os : List (SnapOp n)) (i : Fin n) :
    (binSnap n).runOps σ os i = os.foldl (lastUpdStep i) (σ i) := by
  induction os generalizing σ with
  | nil => rfl
  | cons o os ih =>
    rw [ObjSpec.runOps_cons, ih, List.foldl_cons]
    congr 1
    cases o with
    | update j v =>
      by_cases h : j = i
      · subst h; simp [lastUpdStep]
      · simp [lastUpdStep, h, Function.update_of_ne (Ne.symm h)]
    | scan => rfl

/-- The state of the binary snapshot after a sequential history: component `i` holds the
parameter of the last `update_i` (`false` if there is none). -/
lemma binSnap_linState_apply {n : ℕ} (L : List (OpId (Fin n) × SnapOp n)) (i : Fin n) :
    linState (A := binSnap n) L i = lastUpd i (L.map Prod.snd) :=
  binSnap_runOps_apply _ _ i

/-- **Lemma 3** (sequential correctness of the snapshot, in the form needed for Lemma 4): in a
linearization `L = L₁ ++ (x, scan) :: L₂` of a history of the binary snapshot, a completed scan
`x` returns, for every component `i`, the parameter of the last `update_i` in `L₁` (`false` if
there is none). -/
theorem binSnap_scan_resp {n : ℕ} {α : List (Label (Fin n) (binSnap n))}
    {L L₁ L₂ : List (OpId (Fin n) × SnapOp n)} {x : OpId (Fin n)} {r : Fin n → Bool}
    (hL : IsLinearization α L) (hs : L = L₁ ++ (x, .scan) :: L₂) (hr : respOf α x = some r)
    (i : Fin n) : r i = lastUpd i (L₁.map Prod.snd) := by
  have h1 := hL.respIn_eq hr
  rw [ObjSpec.respIn_of_split hL.nodup hs] at h1
  simp only [Option.some.injEq] at h1
  rw [← h1]
  exact binSnap_runOps_apply _ _ i

/-! ## Bit arithmetic (Invariant 1) -/

/-- The bits `0, …, n-1` of a counter value (lines 10–12 of Algorithm 3). -/
def decode (n s : ℕ) : Fin n → Bool := fun j => s.testBit j

/-- The amount added to the counter by `update_p(v)` when component `p` changes (lines 6–7):
`2^p` for `0 → 1`, `2^n - 2^p` for `1 → 0`. -/
def delta (n : ℕ) (p : Fin n) (v : Bool) : ℕ := if v then 2 ^ (p : ℕ) else 2 ^ n - 2 ^ (p : ℕ)

lemma testBit_add_two_pow_of_false {s p : ℕ} (h : s.testBit p = false) (j : ℕ) :
    (s + 2 ^ p).testBit j = if j = p then true else s.testBit j := by
  set r := s % 2 ^ (p + 1) with hr
  set q := s / 2 ^ (p + 1) with hq
  have hs : s = 2 ^ (p + 1) * q + r := (Nat.div_add_mod s _).symm
  have hr2 : r < 2 ^ (p + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hrp : r.testBit p = false := by
    rw [hr, Nat.testBit_mod_two_pow]; simp [h]
  have hpow : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ, Nat.mul_comm]
  have hr1 : r < 2 ^ p := by
    by_contra hc
    have h1 : r = 2 ^ p + (r - 2 ^ p) := by omega
    have h2 : r - 2 ^ p < 2 ^ p := by omega
    rw [h1, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow h2] at hrp
    simp at hrp
  have hb : 2 ^ p * 1 + r < 2 ^ (p + 1) := by omega
  have e : s + 2 ^ p = 2 ^ (p + 1) * q + (2 ^ p * 1 + r) := by omega
  rw [e, Nat.testBit_two_pow_mul_add _ hb, hs, Nat.testBit_two_pow_mul_add _ hr2,
    Nat.testBit_two_pow_mul_add _ hr1]
  rcases Nat.lt_trichotomy j p with hj | rfl | hj
  · simp [hj, Nat.lt_succ_of_lt hj, Nat.ne_of_lt hj]
  · simp
  · have : ¬ j < p + 1 := by omega
    simp [this, Nat.ne_of_gt hj]

lemma testBit_add_two_pow_sub_of_true {s p n : ℕ} (hp : p < n) (h : s.testBit p = true)
    {j : ℕ} (hj : j < n) :
    (s + (2 ^ n - 2 ^ p)).testBit j = if j = p then false else s.testBit j := by
  have hge := Nat.ge_two_pow_of_testBit h
  set s' := s - 2 ^ p
  have hs : s = s' + 2 ^ p := by omega
  have h' : s'.testBit p = false := by
    have := Nat.testBit_two_pow_add_eq s' p
    rw [Nat.add_comm, ← hs, h] at this
    simpa using this.symm
  have hle : 2 ^ p ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hp)
  have e : s + (2 ^ n - 2 ^ p) = 2 ^ n + s' := by omega
  rw [e, Nat.testBit_two_pow_add_gt hj, hs, testBit_add_two_pow_of_false h']
  split_ifs with hjp
  · subst hjp; exact h'
  · rfl

/-- **The induction step of Invariant 1.** If the bits `< n` of the counter `s` are `σ` and
component `p` changes to `v ≠ σ p`, then after adding `delta n p v` the bits `< n` are
`σ[p ↦ v]`. -/
lemma testBit_add_delta {n s : ℕ} {σ : Fin n → Bool} (hs : ∀ j : Fin n, s.testBit j = σ j)
    (p : Fin n) {v : Bool} (hv : σ p ≠ v) (j : Fin n) :
    (s + delta n p v).testBit j = Function.update σ p v j := by
  cases v with
  | true =>
    have h0 : s.testBit p = false := by rw [hs]; simpa using hv
    simp only [delta, ite_true]
    rw [testBit_add_two_pow_of_false h0, Function.update_apply]
    by_cases hj : j = p
    · subst hj; simp
    · simp [hj, Fin.val_ne_of_ne hj, hs]
  | false =>
    have h1 : s.testBit p = true := by rw [hs]; simpa using hv
    simp only [delta, Bool.false_eq_true, ite_false]
    rw [testBit_add_two_pow_sub_of_true p.isLt h1 j.isLt, Function.update_apply]
    by_cases hj : j = p
    · subst hj; simp
    · simp [hj, Fin.val_ne_of_ne hj, hs]

/-- The paper's sum `∑ᵢ vᵢ 2^i`. -/
def bitsVal {n : ℕ} (σ : Fin n → Bool) : ℕ := ∑ i : Fin n, (σ i).toNat * 2 ^ (i : ℕ)

lemma bitsVal_lt_and_testBit : ∀ {n : ℕ} (σ : Fin n → Bool),
    bitsVal σ < 2 ^ n ∧ ∀ j : Fin n, (bitsVal σ).testBit j = σ j
  | 0, σ => ⟨by simp [bitsVal], fun j => j.elim0⟩
  | n + 1, σ => by
    obtain ⟨ih1, ih2⟩ := bitsVal_lt_and_testBit (n := n) (fun i => σ i.succ)
    have hsum : bitsVal σ = (σ 0).toNat + 2 * bitsVal (fun i : Fin n => σ i.succ) := by
      simp only [bitsVal, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
        Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ, Nat.mul_comm 2, Nat.mul_assoc]
    have hb : (σ 0).toNat ≤ 1 := Bool.toNat_le _
    refine ⟨?_, fun j => ?_⟩
    · rw [hsum, pow_succ]; omega
    · rw [hsum]
      cases j using Fin.cases with
      | zero =>
        simp only [Fin.val_zero, Nat.testBit_zero]
        cases σ 0 <;> simp
      | succ j =>
        simp only [Fin.val_succ, Nat.testBit_add_one]
        have : ((σ 0).toNat + 2 * bitsVal (fun i : Fin n => σ i.succ)) / 2 =
            bitsVal (fun i : Fin n => σ i.succ) := by omega
        rw [this, ih2 j]

/-- A counter value whose bits `< n` are `σ` has the form `c · 2^n + ∑ᵢ σᵢ 2^i`. -/
lemma eq_mul_add_bitsVal {n s : ℕ} {σ : Fin n → Bool} (hs : ∀ j : Fin n, s.testBit j = σ j) :
    s = s / 2 ^ n * 2 ^ n + bitsVal σ := by
  have hmod : s % 2 ^ n = bitsVal σ := by
    obtain ⟨hlt, hbit⟩ := bitsVal_lt_and_testBit σ
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < n
    · have := hbit ⟨i, hi⟩
      simp only at this
      simp [hi, this, ← hs ⟨i, hi⟩]
    · have : bitsVal σ < 2 ^ i :=
        Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
      simp [hi, Nat.testBit_lt_two_pow this]
  rw [← hmod, Nat.mul_comm]; exact (Nat.div_add_mod s _).symm

/-! ## Algorithm 3 -/

/-- Program counter of Algorithm 3. -/
inductive Alg3Pc where
  /-- No pending operation. -/
  | idle
  /-- `update(v)` invoked, at line 4. -/
  | upd (v : Bool)
  /-- `update` performed its counter access, about to return. -/
  | updRet
  /-- `scan` invoked, at line 9. -/
  | scan
  /-- `scan` read `sum` from the counter, about to return its bits. -/
  | scanRet (sum : ℕ)

/-- Local state of a process in Algorithm 3: the local variable `vᵢ` and the program counter. -/
structure Alg3Loc where
  /-- The local variable `vᵢ` (initially `0`). -/
  v : Bool
  /-- The program counter. -/
  pc : Alg3Pc

/-- **Algorithm 3**: a binary snapshot for processes `Fin n` from one batched counter `BC`
(the single base object, indexed by `Unit`, initially `0`).

* `update_p(v)`: if `v = v_p`, return (line 4); otherwise apply `BC.update(2^p)` if `v = 1` or
  `BC.update(2^n - 2^p)` if `v = 0` (lines 6–7) and set `v_p ← v` (line 5; `v_p` is local, so
  setting it together with the access is equivalent), then return.
* `scan`: `sum ← BC.read()` (line 9), return the bits `0, …, n-1` of `sum` (lines 10–13).

Process `p` may only update component `p` (`SnapOp.Allowed`). -/
def alg3 (n : ℕ) : Impl (binSnap n) (fun _ : Unit => batchedCounter) (Fin n) Alg3Loc where
  memInit _ := 0
  locInit _ := ⟨false, .idle⟩
  invoke _ s o := match o with
    | .update _ v => ⟨s.v, .upd v⟩
    | .scan => ⟨s.v, .scan⟩
  act p s := match s.pc with
    | .idle => .ret (fun _ => false) s
    | .upd v => if s.v = v then .ret (fun _ => false) ⟨s.v, .idle⟩
        else .access () (.update (delta n p v)) (fun _ => ⟨v, .updRet⟩)
    | .updRet => .ret (fun _ => false) ⟨s.v, .idle⟩
    | .scan => .access () .read (fun r => ⟨s.v, .scanRet r⟩)
    | .scanRet r => .ret (decode n r) ⟨s.v, .idle⟩
  allowed p o := o.Allowed p

namespace Alg3

variable {n : ℕ}

/-- Abbreviation for the configurations of Algorithm 3. -/
abbrev Cfg (n : ℕ) := Config (binSnap n) (fun _ : Unit => batchedCounter) (Fin n) Alg3Loc

/-- The status of process `p` (local state `s`, pending operation `pd`) w.r.t. the linearization
`L` of `α`: before the linearization point its current instance is not in `L`, after it `L`
assigns it the response the process will return. -/
def ProcOK (α : List (Label (Fin n) (binSnap n))) (L : List (OpId (Fin n) × SnapOp n))
    (pd : Option (SnapOp n)) (s : Alg3Loc) (p : Fin n) : Prop :=
  match s.pc with
  | .idle => pd = none
  | .upd v => pd = some (.update p v) ∧ curOp α p ∉ L.map Prod.fst
  | .updRet => pd ≠ none ∧
      (binSnap n).respIn (binSnap n).init L (curOp α p) = some (fun _ => false)
  | .scan => pd = some .scan ∧ curOp α p ∉ L.map Prod.fst
  | .scanRet r => pd ≠ none ∧
      (binSnap n).respIn (binSnap n).init L (curOp α p) = some (decode n r)

/-- The invariant of Algorithm 3 (Invariant 1 together with the linearization points of
Lemma 4): `L` linearizes `α`, the bits `< n` of the counter are the abstract state `linState L`,
the local `v_p` is component `p` of the abstract state, and every process is consistent with `L`. -/
structure Inv (α : List (Label (Fin n) (binSnap n))) (D : Cfg n)
    (L : List (OpId (Fin n) × SnapOp n)) : Prop where
  lin : IsLinearization α L
  mem : ∀ j : Fin n, (D.mem ()).testBit j = linState (A := binSnap n) L j
  loc : ∀ p, (D.loc p).v = linState (A := binSnap n) L p
  proc : ∀ p, ProcOK α L (D.pend p) (D.loc p) p

lemma ProcOK.frame {α α' : List (Label (Fin n) (binSnap n))}
    {L M : List (OpId (Fin n) × SnapOp n)} {pd : Option (SnapOp n)} {s : Alg3Loc} {q : Fin n}
    (h : ProcOK α L pd s q) (hc : curOp α' q = curOp α q)
    (hM : ∀ y ∈ M, y.1.1 ≠ q) : ProcOK α' (L ++ M) pd s q := by
  have hnm : curOp α q ∉ M.map Prod.fst := by
    intro hm
    obtain ⟨y, hy, hy'⟩ := List.mem_map.1 hm
    exact hM y hy (by rw [hy'])
  unfold ProcOK at h ⊢
  rw [hc]
  cases hs : s.pc <;> simp only [hs] at h ⊢
  · exact h
  · exact ⟨h.1, by simp only [List.map_append, List.mem_append, not_or]; exact ⟨h.2, hnm⟩⟩
  · exact ⟨h.1, ObjSpec.respIn_append_of_eq_some h.2 M⟩
  · exact ⟨h.1, by simp only [List.map_append, List.mem_append, not_or]; exact ⟨h.2, hnm⟩⟩
  · exact ⟨h.1, ObjSpec.respIn_append_of_eq_some h.2 M⟩

lemma procOK_pend {α : List (Label (Fin n) (binSnap n))} {L : List (OpId (Fin n) × SnapOp n)}
    {pd : Option (SnapOp n)} {s : Alg3Loc} {p : Fin n} (h : ProcOK α L pd s p) (hp : pd ≠ none) :
    s.pc ≠ .idle := by
  intro hi; unfold ProcOK at h; rw [hi] at h; exact hp h

lemma inv_nil : Inv ([] : List (Label (Fin n) (binSnap n))) (alg3 n).initCfg [] where
  lin := isLinearization_nil
  mem j := by simp [Impl.initCfg, alg3]; rfl
  loc p := rfl
  proc p := by simp [ProcOK, Impl.initCfg, alg3]

/-- The update of the abstract state by `update p v`/`scan` keeps the other components. -/
lemma linState_concat_other {L : List (OpId (Fin n) × SnapOp n)} {x : OpId (Fin n)}
    {o : SnapOp n} {p q : Fin n} (ho : o.Allowed p) (hq : q ≠ p) :
    linState (A := binSnap n) (L ++ [(x, o)]) q = linState (A := binSnap n) L q := by
  rw [linState_concat]
  cases o with
  | update i v =>
    simp only [SnapOp.Allowed] at ho; subst ho
    simp [Function.update_of_ne hq]
  | scan => rfl

theorem inv_step {α : List (Label (Fin n) (binSnap n))} {D D' : Cfg n} {ℓ}
    {L : List (OpId (Fin n) × SnapOp n)} (hα : (alg3 n).run α = some D) (hI : Inv α D L)
    (h : (alg3 n).step D ℓ = some D') : ∃ L', Inv (α ++ [ℓ]) D' L' := by
  cases ℓ with
  | inv p o =>
    obtain ⟨hp, hal, -⟩ := Impl.step_inv h
    rw [Impl.step_inv_eq_some hp hal] at h
    cases h
    have hpc := hI.proc p
    have hni : curOp α p ∉ L.map Prod.fst := fun hm => by
      have := hI.lin.mem_invoked hm
      exact (alg3 n).not_invoked_curOp_of_idle hα hp this
    refine ⟨L, hI.lin.append_inv p o, hI.mem, fun q => ?_, fun q => ?_⟩
    · by_cases hq : q = p
      · subst hq; dsimp only; rw [Function.update_self, ← hI.loc]; cases o <;> rfl
      · dsimp only; rw [Function.update_of_ne hq]; exact hI.loc q
    · by_cases hq : q = p
      · subst hq
        simp only [Function.update_self]
        cases o with
        | update i v =>
          simp only [alg3, SnapOp.Allowed] at hal; subst hal
          simp [ProcOK, alg3, hni]
        | scan => simp [ProcOK, alg3, hni]
      · dsimp only; rw [Function.update_of_ne hq, Function.update_of_ne hq]
        simpa using (hI.proc q).frame (M := []) (curOp_append_inv α p q o) (by simp)
  | tau p =>
    obtain ⟨hp, -, i, o, k, hact, -⟩ := Impl.step_tau h
    have hpc := hI.proc p
    cases hpd : D.pend p with
    | none => exact absurd hpd hp
    | some op =>
    obtain ⟨hinv, -, hop⟩ := (alg3 n).run_pend_curOp hα hpd
    cases hl : (D.loc p).pc with
    | idle => simp [alg3, hl] at hact
    | updRet => simp [alg3, hl] at hact
    | scanRet r => simp [alg3, hl] at hact
    | upd v =>
      by_cases hv : (D.loc p).v = v
      · simp [alg3, hl, hv] at hact
      have hact' : (alg3 n).act p (D.loc p) =
          .access () (.update (delta n p v)) (fun _ => ⟨v, .updRet⟩) := by
        simp [alg3, hl, hv]
      rw [Impl.step_tau_eq_some hp hact'] at h
      cases h
      simp only [ProcOK, hl, hpd] at hpc
      obtain ⟨hpo, hni⟩ := hpc
      cases hpo
      set x := curOp α p
      refine ⟨L ++ [(x, .update p v)], (hI.lin.push hop hni (not_completed_curOp α p)).append_tau p,
        fun j => ?_, fun q => ?_, fun q => ?_⟩
      · simp only [Function.update_self]
        rw [linState_concat (A := binSnap n)]
        exact testBit_add_delta hI.mem p (by rw [← hI.loc]; exact hv) j
      · by_cases hq : q = p
        · subst hq; dsimp only; rw [Function.update_self, linState_concat (A := binSnap n)]; simp
        · dsimp only; rw [Function.update_of_ne hq, linState_concat_other (o := .update p v) rfl hq]
          exact hI.loc q
      · by_cases hq : q = p
        · subst hq
          simp only [Function.update_self, ProcOK, curOp_append_tau, hpd, ne_eq, reduceCtorEq,
            not_false_eq_true, true_and]
          rw [ObjSpec.respIn_concat_self hni]
        · dsimp only; rw [Function.update_of_ne hq]
          exact (hI.proc q).frame (curOp_append_tau α p q)
            (by simp only [List.mem_singleton]; rintro y rfl; exact Ne.symm hq)
    | scan =>
      have hact' : (alg3 n).act p (D.loc p) =
          .access () .read (fun r => ⟨(D.loc p).v, .scanRet r⟩) := by
        simp [alg3, hl]
      rw [Impl.step_tau_eq_some hp hact'] at h
      cases h
      simp only [ProcOK, hl, hpd] at hpc
      obtain ⟨hpo, hni⟩ := hpc
      cases hpo
      set x := curOp α p
      refine ⟨L ++ [(x, .scan)], (hI.lin.push hop hni (not_completed_curOp α p)).append_tau p,
        fun j => ?_, fun q => ?_, fun q => ?_⟩
      · rw [linState_concat (A := binSnap n)]; simpa using hI.mem j
      · by_cases hq : q = p
        · subst hq; rw [linState_concat (A := binSnap n)]; simpa using hI.loc q
        · dsimp only; rw [Function.update_of_ne hq, linState_concat_other (o := .scan) (p := p) trivial hq]
          exact hI.loc q
      · by_cases hq : q = p
        · subst hq
          simp only [Function.update_self, ProcOK, curOp_append_tau, hpd, ne_eq, reduceCtorEq,
            not_false_eq_true, true_and]
          rw [ObjSpec.respIn_concat_self hni]
          congr 1
          funext j
          exact (hI.mem j).symm
        · dsimp only; rw [Function.update_of_ne hq]
          exact (hI.proc q).frame (curOp_append_tau α p q)
            (by simp only [List.mem_singleton]; rintro y rfl; exact Ne.symm hq)
  | ret p r =>
    obtain ⟨hp, -, -, l, hact, -⟩ := Impl.step_ret h
    have hpc := hI.proc p
    cases hpd : D.pend p with
    | none => exact absurd hpd hp
    | some op =>
    obtain ⟨hinv, -, hop⟩ := (alg3 n).run_pend_curOp hα hpd
    have hframe : ∀ (M : List (OpId (Fin n) × SnapOp n)), (∀ y ∈ M, y.1.1 = p) → ∀ q, q ≠ p →
        ProcOK (α ++ [.ret p r]) (L ++ M) (D.pend q) (D.loc q) q := fun M hM q hq =>
      (hI.proc q).frame (curOp_append_ret_of_ne α r (Ne.symm hq))
        (fun y hy => by rw [hM y hy]; exact Ne.symm hq)
    cases hl : (D.loc p).pc with
    | idle => exact absurd hl (procOK_pend hpc (by rw [hpd]; simp))
    | scan => simp [alg3, hl] at hact
    | upd v =>
      by_cases hv : (D.loc p).v = v
      · have hact' : (alg3 n).act p (D.loc p) = .ret (fun _ => false) ⟨(D.loc p).v, .idle⟩ := by
          simp [alg3, hl, hv]
        rw [hact'] at hact
        obtain ⟨rfl, -⟩ := Action.ret.inj hact
        rw [Impl.step_ret_eq_some hp hact'] at h
        cases h
        simp only [ProcOK, hl, hpd] at hpc
        obtain ⟨hpo, hni⟩ := hpc
        cases hpo
        set x := curOp α p
        have hL' := hI.lin.push hop hni (not_completed_curOp α p)
        have hst : linState (A := binSnap n) (L ++ [(x, .update p v)]) =
            linState (A := binSnap n) L := by
          rw [linState_concat]
          simp only
          rw [← hv, hI.loc p, Function.update_eq_self]
        refine ⟨L ++ [(x, .update p v)], hL'.append_ret_of_respIn ?_, fun j => ?_, fun q => ?_,
          fun q => ?_⟩
        · rw [ObjSpec.respIn_concat_self hni]
        · rw [hst]; exact hI.mem j
        · rw [hst]
          by_cases hq : q = p
          · subst hq; simp [hI.loc]
          · dsimp only; rw [Function.update_of_ne hq]; exact hI.loc q
        · by_cases hq : q = p
          · subst hq; simp [ProcOK]
          · dsimp only; rw [Function.update_of_ne hq, Function.update_of_ne hq]
            exact hframe _ (by simp [x]) q hq
      · simp [alg3, hl, hv] at hact
    | updRet =>
      have hact' : (alg3 n).act p (D.loc p) = .ret (fun _ => false) ⟨(D.loc p).v, .idle⟩ := by
        simp [alg3, hl]
      rw [hact'] at hact
      obtain ⟨rfl, -⟩ := Action.ret.inj hact
      rw [Impl.step_ret_eq_some hp hact'] at h
      cases h
      simp only [ProcOK, hl] at hpc
      refine ⟨L, hI.lin.append_ret_of_respIn hpc.2, hI.mem, fun q => ?_, fun q => ?_⟩
      · by_cases hq : q = p
        · subst hq; simp [hI.loc]
        · dsimp only; rw [Function.update_of_ne hq]; exact hI.loc q
      · by_cases hq : q = p
        · subst hq; simp [ProcOK]
        · dsimp only; rw [Function.update_of_ne hq, Function.update_of_ne hq]
          simpa using hframe [] (by simp) q hq
    | scanRet s =>
      have hact' : (alg3 n).act p (D.loc p) = .ret (decode n s) ⟨(D.loc p).v, .idle⟩ := by
        simp [alg3, hl]
      rw [hact'] at hact
      obtain ⟨rfl, -⟩ := Action.ret.inj hact
      rw [Impl.step_ret_eq_some hp hact'] at h
      cases h
      simp only [ProcOK, hl] at hpc
      refine ⟨L, hI.lin.append_ret_of_respIn hpc.2, hI.mem, fun q => ?_, fun q => ?_⟩
      · by_cases hq : q = p
        · subst hq; simp [hI.loc]
        · dsimp only; rw [Function.update_of_ne hq]; exact hI.loc q
      · by_cases hq : q = p
        · subst hq; simp [ProcOK]
        · dsimp only; rw [Function.update_of_ne hq, Function.update_of_ne hq]
          simpa using hframe [] (by simp) q hq

theorem inv_of_run {α : List (Label (Fin n) (binSnap n))} {D : Cfg n}
    (h : (alg3 n).run α = some D) : ∃ L, Inv α D L :=
  (alg3 n).run_induction (Q := fun α D => ∃ L, Inv α D L) ⟨[], inv_nil⟩
    (fun _ _ _ _ hα ⟨_, hI⟩ hs => inv_step hα hI hs) h

end Alg3

/-- **Invariant 1** (for arbitrary, possibly concurrent, executions of Algorithm 3): every
execution `α` has a linearization `L` (given by the linearization points of Lemma 4) such that the
counter holds `c · 2^n + ∑ᵢ vᵢ 2^i` for some `c ∈ ℕ`, where `vᵢ` is the parameter of the last
`update_i` in `L` (`0` if there is none), and the local variable `v_p` of every process equals
`v_p`. -/
theorem alg3_invariant1 {n : ℕ} {α : List (Label (Fin n) (binSnap n))} {D : Alg3.Cfg n}
    (h : (alg3 n).run α = some D) :
    ∃ L, IsLinearization α L ∧
      (∃ c : ℕ, D.mem () = c * 2 ^ n + ∑ i : Fin n, (lastUpd i (L.map Prod.snd)).toNat * 2 ^ (i : ℕ)) ∧
      ∀ p, (D.loc p).v = lastUpd p (L.map Prod.snd) := by
  obtain ⟨L, hI⟩ := Alg3.inv_of_run h
  refine ⟨L, hI.lin, ⟨D.mem () / 2 ^ n, ?_⟩, fun p => by rw [hI.loc, binSnap_linState_apply]⟩
  have := eq_mul_add_bitsVal hI.mem
  conv_lhs => rw [this]
  simp only [bitsVal, binSnap_linState_apply]

/-- **Lemma 4**: Algorithm 3 is a linearizable implementation of the binary snapshot (from an
atomic batched counter). -/
theorem alg3_linearizable (n : ℕ) : (alg3 n).Linearizable :=
  Impl.linearizable_of_run fun _ _ h => (Alg3.inv_of_run h).imp fun _ hI => hI.lin

/-- Potential for the step bounds: one access left in phases `upd`/`scan`, none otherwise. -/
def Alg3.pot (s : Alg3Loc) : ℕ :=
  match s.pc with
  | .upd _ => 1
  | .scan => 1
  | _ => 0

lemma Alg3.pot_access {n : ℕ} (p : Fin n) (l : Alg3Loc) (i : Unit) (o : BCOp) (k : ℕ → Alg3Loc)
    (h : (alg3 n).act p l = .access i o k) (x : ℕ) : Alg3.pot (k x) < Alg3.pot l := by
  cases hl : l.pc with
  | idle => simp [alg3, hl] at h
  | updRet => simp [alg3, hl] at h
  | scanRet r => simp [alg3, hl] at h
  | upd v =>
    by_cases hv : l.v = v
    · simp [alg3, hl, hv] at h
    · simp only [alg3, hl, hv, ite_false] at h
      cases h
      simp [Alg3.pot, hl]
  | scan =>
    simp only [alg3, hl] at h
    cases h
    simp [Alg3.pot, hl]

/-- Algorithm 3 is wait-free (if the counter is atomic). -/
theorem alg3_waitFree (n : ℕ) : (alg3 n).WaitFree :=
  (alg3 n).waitFree_of_potential (fun _ s => Alg3.pot s)
    fun p l i o k h x => Alg3.pot_access p l i o k h x

/-- An `update` of Algorithm 3 accesses the counter at most once. -/
theorem alg3_update_steps (n : ℕ) : (alg3 n).StepsLE (fun o => ∃ i b, o = .update i b) 1 := by
  rintro α p o γ ⟨i, b, rfl⟩ hv hret
  obtain ⟨l, hl⟩ := (alg3 n).tauSteps_le_potential_invoke (fun _ s => Alg3.pot s)
    (fun p l i o k h x => Alg3.pot_access p l i o k h x) hv hret
  simpa [alg3, Alg3.pot] using hl

/-- A `scan` of Algorithm 3 accesses the counter at most once. -/
theorem alg3_scan_steps (n : ℕ) : (alg3 n).StepsLE (fun o => o = .scan) 1 := by
  rintro α p o γ rfl hv hret
  obtain ⟨l, hl⟩ := (alg3 n).tauSteps_le_potential_invoke (fun _ s => Alg3.pot s)
    (fun p l i o k h x => Alg3.pot_access p l i o k h x) hv hret
  simpa [alg3, Alg3.pot] using hl

end Podc.IntermediateValueLin
