import Papers.PODC2020.IntermediateValueLin.Objects
import Papers.PODC2020.IntermediateValueLin.Canonical
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Algorithm 2: an IVL batched counter from SWMR registers (Lemma 2, Theorem 2)

Rinberg–Keidar, PODC 2020, Section 6.1.

```
shared array v[1 … n]
procedure update_i(v):  v[i] ← v[i] + v
procedure read:         sum ← 0; for i = 1 … n: sum ← sum + v[i]; return sum
```

Model: `n` processes `Fin n`, base objects `n` read/write registers over `ℕ` (initially `0`);
register `i` is written only by process `i` (`alg2_swmr`). Process `i` keeps a local copy `own` of
its register (it is the only writer), so `update_i(v)` is a single write of `own + v`; `read` reads
the `n` registers one by one.

* `alg2_sandwich` (the proof of **Lemma 2**): in every execution, with the canonical
  linearizations `H₁` (reads at their invocation, updates at their response) and `H₂` (updates at
  their invocation, reads at their response) of the paper's proof, every completed read returns a
  value between its values in `τ(H₁)` and `τ(H₂)`.
* `lemma2`: Algorithm 2 is an IVL implementation of the batched counter.
* `theorem2` (**Theorem 2**): a wait-free IVL batched counter from SWMR registers in which every
  `update` takes one step and every `read` takes `n` steps.
-/

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

namespace Podc.IntermediateValueLin.Alg2

variable {n : ℕ}

/-- Program counter of a process. -/
inductive PC where
  /-- No pending operation. -/
  | idle
  /-- `update(v)` invoked, the write is next. -/
  | upd (v : ℕ)
  /-- `update(v)` has written, the response is next. -/
  | updRet (v : ℕ)
  /-- `read`: registers `0 … j-1` have been read, their sum is `s`. -/
  | rd (j s : ℕ)

/-- Local state: the local copy of the own register and the program counter. -/
structure Loc where
  /-- Local copy of the process's own register. -/
  own : ℕ
  /-- Program counter. -/
  pc : PC

/-- The base objects: `n` registers over `ℕ`, initially `0`. -/
abbrev Regs (n : ℕ) : Fin n → ObjSpec := fun _ => register ℕ 0

/-- **Algorithm 2.** -/
def alg2 (n : ℕ) : Impl batchedCounter (Regs n) (Fin n) Loc where
  memInit _ := 0
  locInit _ := ⟨0, .idle⟩
  invoke _ l
    | .update v => ⟨l.own, .upd v⟩
    | .read => ⟨l.own, .rd 0 0⟩
  act i l :=
    match l.pc with
    | .idle => .ret 0 l
    | .upd v => .access i (.write (l.own + v)) (fun _ => ⟨l.own + v, .updRet v⟩)
    | .updRet _ => .ret 0 ⟨l.own, .idle⟩
    | .rd j s =>
      if h : j < n then .access ⟨j, h⟩ .read (fun r => ⟨l.own, .rd (j + 1) (s + r)⟩)
      else .ret s ⟨l.own, .idle⟩

/-! ### Canonical linearizations and sums -/

/-- `update` operations. -/
def isUpd : BCOp → Bool
  | .update _ => true
  | .read => false

/-- The paper's `H₁`: reads at their invocation, updates at their response. -/
abbrev L₁ (α : List (Label (Fin n) batchedCounter)) : List (OpId (Fin n) × BCOp) :=
  canon (fun o => !isUpd o) α

/-- The paper's `H₂`: updates at their invocation, reads at their response. -/
abbrev L₂ (α : List (Label (Fin n) batchedCounter)) : List (OpId (Fin n) × BCOp) :=
  canon isUpd α

/-- The sum of the values of the updates of process `k` in `L`. -/
def usum (L : List (OpId (Fin n) × BCOp)) (k : Fin n) : ℕ :=
  ((L.filter (fun y => y.1.1 = k)).map (fun y => y.2.val)).sum

@[simp] lemma usum_nil (k : Fin n) : usum [] k = 0 := rfl

lemma usum_append (L M : List (OpId (Fin n) × BCOp)) (k : Fin n) :
    usum (L ++ M) k = usum L k + usum M k := by
  simp [usum, List.filter_append]

lemma usum_singleton (x : OpId (Fin n)) (o : BCOp) (k : Fin n) :
    usum [(x, o)] k = if x.1 = k then o.val else 0 := by
  by_cases h : x.1 = k <;> simp [usum, h]

lemma usum_le_append (L M : List (OpId (Fin n) × BCOp)) (k : Fin n) :
    usum L k ≤ usum (L ++ M) k := by
  rw [usum_append]; omega

lemma usum_singleton_of_ne {x : OpId (Fin n)} (o : BCOp) {k : Fin n} (h : x.1 ≠ k) :
    usum [(x, o)] k = 0 := by
  simp [usum_singleton, h]

lemma usum_singleton_read (x : OpId (Fin n)) (k : Fin n) : usum [(x, .read)] k = 0 := by
  simp [usum_singleton]

/-- The total of the update values in `L` is the sum over processes. -/
lemma sum_val_eq (L : List (OpId (Fin n) × BCOp)) :
    ((L.map Prod.snd).map BCOp.val).sum = ∑ k, usum L k := by
  induction L with
  | nil => simp
  | cons y L ih =>
    have : ∀ k, usum (y :: L) k = (if y.1.1 = k then y.2.val else 0) + usum L k := by
      intro k; by_cases h : y.1.1 = k <;> simp [usum, h]
    simp only [List.map_cons, List.sum_cons, ih, this, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The sequential specification of the batched counter. -/
abbrev bcQ : QSpec BCOp ℕ := batchedCounter.toQSpec

/-- The response of a read appended to `L` is the total of `L`. -/
lemma tau_concat_read {L : List (OpId (Fin n) × BCOp)} {x : OpId (Fin n)}
    (hx : x ∉ L.map Prod.fst) : tau bcQ (L ++ [(x, .read)]) x = some (∑ k, usum L k) := by
  unfold tau
  rw [ObjSpec.respIn_concat_self hx]
  exact congrArg some ((batchedCounter_runOps 0 _).trans (by rw [sum_val_eq]; simp))

/-- The response of an update appended to `L` is `0`. -/
lemma tau_concat_update {L : List (OpId (Fin n) × BCOp)} {x : OpId (Fin n)} (v : ℕ)
    (hx : x ∉ L.map Prod.fst) : tau bcQ (L ++ [(x, .update v)]) x = some 0 := by
  unfold tau
  rw [ObjSpec.respIn_concat_self hx]

lemma tau_append_of_mem {L M : List (OpId (Fin n) × BCOp)} {x : OpId (Fin n)}
    (hx : x ∈ L.map Prod.fst) : tau bcQ (L ++ M) x = tau bcQ L x := by
  unfold tau; exact ObjSpec.respIn_append_of_mem (A := bcQ.obj) hx M

/-- In a skeleton linearization, an update instance gets the response `0`. -/
lemma tau_of_update {α : List (Label (Fin n) batchedCounter)} {L : List (OpId (Fin n) × BCOp)}
    (hL : IsSkelLin α L) {x : OpId (Fin n)} (hx : x ∈ L.map Prod.fst) {v : ℕ}
    (ho : opOf α x = some (.update v)) : tau bcQ L x = some 0 := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1
    ((ObjSpec.respIn_isSome_iff (A := bcQ.obj) (q := bcQ.init)).2 hx)
  obtain ⟨L₁', L₂', o, hs, hro⟩ := ObjSpec.exists_split_of_respIn_eq_some hr
  have hmem : (x, o) ∈ L := by rw [hs]; simp
  have := hL.op_eq _ hmem
  simp only [opOf_skel] at this
  rw [ho] at this; cases this
  unfold tau; rw [hr, ← hro]

/-! ### The invariant -/

/-- The sum over the processes with index `< j`. -/
def psum (f : Fin n → ℕ) (j : ℕ) : ℕ := ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < j), f i

lemma psum_mono {f g : Fin n → ℕ} (h : ∀ i, f i ≤ g i) (j : ℕ) : psum f j ≤ psum g j :=
  Finset.sum_le_sum fun i _ => h i

lemma psum_succ (f : Fin n → ℕ) {j : ℕ} (hj : j < n) :
    psum f (j + 1) = psum f j + f ⟨j, hj⟩ := by
  unfold psum
  have : Finset.univ.filter (fun i : Fin n => i.val < j + 1) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun i : Fin n => i.val < j)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h; rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | h)
      · simp
      · omega
  rw [this, Finset.sum_insert (by simp), add_comm]

lemma psum_n (f : Fin n → ℕ) : psum f n = ∑ i, f i := by
  unfold psum; congr 1; ext i; simp

/-- The invariant of a pending reader `k` with program counter `rd j s`: `w` is the vector of
the per-process totals of `H₁` at its invocation. -/
def ReaderInv (α : List (Label (Fin n) batchedCounter)) (k : Fin n) (j s : ℕ) : Prop :=
  ∃ w : Fin n → ℕ, tau bcQ (L₁ α) (curOp α k) = some (∑ i, w i) ∧
    (∀ i, w i ≤ usum (L₁ α) i) ∧ psum w j ≤ s ∧ s ≤ psum (usum (L₂ α)) j

/-- The invariant of process `k`. -/
def ProcInv (α : List (Label (Fin n) batchedCounter)) (C : Config batchedCounter (Regs n) (Fin n) Loc)
    (k : Fin n) : Prop :=
  match (C.loc k).pc with
  | .idle => C.pend k = none ∧ usum (L₁ α) k = (C.loc k).own ∧ usum (L₂ α) k = (C.loc k).own
  | .upd v => C.pend k = some (.update v) ∧ usum (L₁ α) k = (C.loc k).own ∧
      usum (L₂ α) k = (C.loc k).own + v
  | .updRet v => C.pend k = some (.update v) ∧ usum (L₁ α) k + v = (C.loc k).own ∧
      usum (L₂ α) k = (C.loc k).own
  | .rd j s => C.pend k = some .read ∧ usum (L₁ α) k = (C.loc k).own ∧
      usum (L₂ α) k = (C.loc k).own ∧ j ≤ n ∧ ReaderInv α k j s

/-- The global invariant. -/
structure Inv (α : List (Label (Fin n) batchedCounter))
    (C : Config batchedCounter (Regs n) (Fin n) Loc) : Prop where
  mem_own : ∀ k, C.mem k = (C.loc k).own
  proc : ∀ k, ProcInv α C k
  done : ∀ a r, respOf α a = some r → ∃ r₁ r₂, tau bcQ (L₁ α) a = some r₁ ∧
    tau bcQ (L₂ α) a = some r₂ ∧ r₁ ≤ r ∧ r ≤ r₂

lemma ProcInv.bounds {α : List (Label (Fin n) batchedCounter)}
    {C : Config batchedCounter (Regs n) (Fin n) Loc} {k : Fin n} (h : ProcInv α C k) :
    usum (L₁ α) k ≤ (C.loc k).own ∧ (C.loc k).own ≤ usum (L₂ α) k := by
  unfold ProcInv at h
  split at h <;> omega

/-- Processes other than the one taking a step keep their invariant, if the step only appends
entries of other processes (or reads) to the canonical linearizations. -/
lemma procInv_other {α α' : List (Label (Fin n) batchedCounter)}
    {C C' : Config batchedCounter (Regs n) (Fin n) Loc} {k : Fin n} (h : ProcInv α C k)
    (hloc : C'.loc k = C.loc k) (hpend : C'.pend k = C.pend k)
    {M₁ M₂ : List (OpId (Fin n) × BCOp)} (h1 : L₁ α' = L₁ α ++ M₁) (h2 : L₂ α' = L₂ α ++ M₂)
    (hM₁ : usum M₁ k = 0) (hM₂ : usum M₂ k = 0) (hcur : curOp α' k = curOp α k) :
    ProcInv α' C' k := by
  unfold ProcInv ReaderInv at h ⊢
  rw [hloc, hpend, h1, h2, usum_append, usum_append, hM₁, hM₂]
  split at h
  · simpa using h
  · simpa using h
  · simpa using h
  · rename_i j s _
    obtain ⟨hp, h1', h2', hj, w, hw, hwle, hs1, hs2⟩ := h
    refine ⟨hp, by simpa using h1', by simpa using h2', hj, w, ?_, ?_, hs1, ?_⟩
    · rw [hcur, tau_append_of_mem (ObjSpec.mem_of_respIn_eq_some hw), hw]
    · exact fun i => (hwle i).trans (usum_le_append _ _ i)
    · exact hs2.trans (psum_mono (fun i => usum_le_append _ _ i) j)

lemma done_append {α : List (Label (Fin n) batchedCounter)} {M₁ M₂ : List (OpId (Fin n) × BCOp)}
    {a : OpId (Fin n)} {r : ℕ}
    (h : ∃ r₁ r₂, tau bcQ (L₁ α) a = some r₁ ∧ tau bcQ (L₂ α) a = some r₂ ∧ r₁ ≤ r ∧ r ≤ r₂) :
    ∃ r₁ r₂, tau bcQ (L₁ α ++ M₁) a = some r₁ ∧ tau bcQ (L₂ α ++ M₂) a = some r₂ ∧
      r₁ ≤ r ∧ r ≤ r₂ := by
  obtain ⟨r₁, r₂, h1, h2, h3, h4⟩ := h
  exact ⟨r₁, r₂, by rw [tau_append_of_mem (ObjSpec.mem_of_respIn_eq_some h1), h1],
    by rw [tau_append_of_mem (ObjSpec.mem_of_respIn_eq_some h2), h2], h3, h4⟩

lemma inv_init : Inv [] (alg2 n).initCfg where
  mem_own _ := rfl
  proc k := by simp [ProcInv, Impl.initCfg, alg2]
  done a r h := by simp [respOf] at h

lemma pc_of_pend_none {α : List (Label (Fin n) batchedCounter)}
    {C : Config batchedCounter (Regs n) (Fin n) Loc} {k : Fin n} (h : ProcInv α C k)
    (hk : C.pend k = none) : (C.loc k).pc = .idle := by
  unfold ProcInv at h
  split at h <;> simp_all

/-- The invariant is preserved by every step. -/
lemma inv_step {α : List (Label (Fin n) batchedCounter)}
    {C C' : Config batchedCounter (Regs n) (Fin n) Loc} {ℓ : Label (Fin n) batchedCounter}
    (hrun : (alg2 n).run α = some C) (hI : Inv α C) (hs : (alg2 n).step C ℓ = some C') :
    Inv (α ++ [ℓ]) C' := by
  have hv : (alg2 n).Valid α := ⟨C, hrun⟩
  have hwf : WellFormed α := hv.wellFormed
  have hc₁ := canonInv_of_wellFormed (fun o => !isUpd o) hwf
  have hc₂ := canonInv_of_wellFormed isUpd hwf
  have hcat₁ : L₁ (α ++ [ℓ]) = L₁ α ++ canonEnt (fun o => !isUpd o) α ℓ := canon_concat _ _ _
  have hcat₂ : L₂ (α ++ [ℓ]) = L₂ α ++ canonEnt isUpd α ℓ := canon_concat _ _ _
  -- entries of the lists have invoked identities
  have hmem_inv : ∀ (f : BCOp → Bool) x, x ∈ (canon f α).map Prod.fst → Invoked α x := by
    intro f x hx
    have := (isSkelLin_canon f hwf).mem_invoked hx
    simpa using this
  cases ℓ with
  | inv p o =>
    obtain ⟨hpend, -, hpend', hloc', hmem'⟩ := Impl.step_inv hs
    have hpc := pc_of_pend_none (hI.proc p) hpend
    have hidle := (alg2 n).run_idle_counts hrun hpend
    have hP := hI.proc p
    unfold ProcInv at hP; rw [hpc] at hP
    obtain ⟨-, hu₁, hu₂⟩ := hP
    set x : OpId (Fin n) := (p, (opsOf α p).length) with hx
    have hxc : curOp α p = x := by simp [curOp, hx, hidle]
    have hxnot : ∀ f : BCOp → Bool, x ∉ (canon f α).map Prod.fst := fun f hm => by
      have := hmem_inv f x hm; simp [Invoked, hx] at this
    have hother : ∀ k, k ≠ p → C'.loc k = C.loc k ∧ C'.pend k = C.pend k := fun k hk => by
      rw [hloc', hpend']; simp [Function.update_of_ne hk]
    refine ⟨?_, ?_, ?_⟩
    · intro k
      rw [hmem', hI.mem_own k]
      by_cases hk : k = p
      · subst hk; rw [hloc', Function.update_self]; cases o <;> rfl
      · rw [(hother k hk).1]
    · intro k
      by_cases hk : k = p
      · subst hk
        unfold ProcInv ReaderInv
        rw [hloc', hpend', Function.update_self, Function.update_self, hcat₁, hcat₂]
        cases o with
        | update v =>
          simp only [alg2, canonEnt, isUpd, Bool.not_true, Bool.false_eq_true, ite_false,
            ite_true, List.append_nil, usum_append, usum_singleton, ite_true]
          simp [hu₁, hu₂]
        | read =>
          simp only [alg2, canonEnt, isUpd, Bool.not_false, Bool.false_eq_true, ite_false,
            ite_true, List.append_nil, usum_append, usum_singleton_read, add_zero]
          refine ⟨by simp, hu₁, hu₂, Nat.zero_le _, usum (L₁ α), ?_, fun i => le_rfl,
            by simp [psum], Nat.zero_le _⟩
          rw [curOp_append_inv, hxc]
          exact tau_concat_read (hxnot _)
      · have hpk : p ≠ k := fun h => hk h.symm
        refine procInv_other (hI.proc k) (hother k hk).1 (hother k hk).2 hcat₁ hcat₂ ?_ ?_
          (curOp_append_inv α p k o)
        · cases o <;> simp [canonEnt, isUpd, usum_singleton, hpk]
        · cases o <;> simp [canonEnt, isUpd, usum_singleton, hpk]
    · intro a r ha
      rw [respOf_append_of_not_ret (by simp)] at ha
      rw [hcat₁, hcat₂]
      exact done_append (hI.done a r ha)
  | tau p =>
    have hpend : C.pend p ≠ none := (Impl.step_tau hs).1
    have hL₁ : L₁ (α ++ [.tau p]) = L₁ α ++ [] := by rw [hcat₁]; rfl
    have hL₂ : L₂ (α ++ [.tau p]) = L₂ α ++ [] := by rw [hcat₂]; rfl
    have hP := hI.proc p
    have hdone : ∀ (a : OpId (Fin n)) (r : ℕ), respOf (α ++ [.tau p]) a = some r → ∃ r₁ r₂,
        tau bcQ (L₁ (α ++ [.tau p])) a = some r₁ ∧ tau bcQ (L₂ (α ++ [.tau p])) a = some r₂ ∧
          r₁ ≤ r ∧ r ≤ r₂ := by
      intro a r ha
      rw [respOf_append_of_not_ret (by simp)] at ha
      rw [hL₁, hL₂]
      exact done_append (hI.done a r ha)
    rcases hl : C.loc p with ⟨own, pc⟩
    unfold ProcInv at hP
    rw [hl] at hP
    cases pc with
    | idle => exact absurd hP.1 hpend
    | updRet v =>
      simp [Impl.step, hpend, alg2, hl] at hs
    | upd v =>
      have hstep : (alg2 n).step C (.tau p) = some { C with
          mem := Function.update C.mem p (own + v),
          loc := Function.update C.loc p ⟨own + v, .updRet v⟩ } := by
        simp [Impl.step, hpend, alg2, hl]
      rw [hstep] at hs; cases hs
      obtain ⟨hp1, hp2, hp3⟩ := hP
      refine ⟨?_, ?_, hdone⟩
      · intro k
        by_cases hk : k = p
        · subst hk; simp
        · simp [Function.update_of_ne hk, hI.mem_own k]
      · intro k
        by_cases hk : k = p
        · subst hk
          unfold ProcInv
          simp only [Function.update_self, hL₁, hL₂, List.append_nil]
          exact ⟨hp1, by simp at hp2; omega, by simpa using hp3⟩
        · exact procInv_other (hI.proc k) (by simp [Function.update_of_ne hk]) rfl hL₁ hL₂ rfl rfl
            (curOp_append_tau α p k)
    | rd j s =>
      obtain ⟨hp1, hp2, hp3, hj, w, hw, hwle, hs1, hs2⟩ := hP
      by_cases hjn : j < n
      · have hstep : (alg2 n).step C (.tau p) = some { C with
            mem := Function.update C.mem ⟨j, hjn⟩ (C.mem ⟨j, hjn⟩),
            loc := Function.update C.loc p ⟨own, .rd (j + 1) (s + C.mem ⟨j, hjn⟩)⟩ } := by
          simp [Impl.step, hpend, alg2, hl, hjn]
        rw [hstep] at hs; cases hs
        have hb := (hI.proc ⟨j, hjn⟩).bounds
        rw [← hI.mem_own] at hb
        refine ⟨?_, ?_, hdone⟩
        · intro k
          rw [Function.update_eq_self]
          by_cases hk : k = p
          · subst hk; simp [hI.mem_own k, hl]
          · simp [Function.update_of_ne hk, hI.mem_own k]
        · intro k
          by_cases hk : k = p
          · subst hk
            unfold ProcInv ReaderInv
            simp only [Function.update_self, hL₁, hL₂, List.append_nil, curOp_append_tau]
            refine ⟨hp1, by simpa [hl] using hp2, by simpa [hl] using hp3, hjn, w, hw, hwle, ?_, ?_⟩
            · rw [psum_succ _ hjn]
              have := hwle ⟨j, hjn⟩
              omega
            · rw [psum_succ _ hjn]
              omega
          · exact procInv_other (hI.proc k) (by simp [Function.update_of_ne hk]) rfl hL₁ hL₂ rfl
              rfl (curOp_append_tau α p k)
      · simp [Impl.step, hpend, alg2, hl, hjn] at hs
  | ret p r =>
    have hpend : C.pend p ≠ none := (Impl.step_ret hs).1
    have hP := hI.proc p
    rcases hl : C.loc p with ⟨own, pc⟩
    unfold ProcInv at hP
    rw [hl] at hP
    set x : OpId (Fin n) := curOp α p with hx
    have hxnc : ¬ Completed α x := not_completed_curOp α p
    cases pc with
    | idle => exact absurd hP.1 hpend
    | upd v => simp [Impl.step, hpend, alg2, hl] at hs
    | updRet v =>
      obtain ⟨hp1, hp2, hp3⟩ := hP
      have hr : r = 0 := by
        by_contra h
        simp [Impl.step, hpend, alg2, hl, h] at hs
      subst hr
      have hstep : (alg2 n).step C (.ret p 0) = some { C with
          pend := Function.update C.pend p none,
          loc := Function.update C.loc p ⟨own, .idle⟩ } := by
        simp [Impl.step, hpend, alg2, hl]
      rw [hstep] at hs; cases hs
      have hop : opOf α x = some (.update v) := ((alg2 n).run_pend_curOp hrun hp1).2.2
      have hL₁ : L₁ (α ++ [.ret p 0]) = L₁ α ++ [(x, .update v)] := by
        rw [hcat₁]; simp [canonEnt, ← hx, hop, isUpd]
      have hL₂ : L₂ (α ++ [.ret p 0]) = L₂ α ++ [] := by
        rw [hcat₂]; simp [canonEnt, ← hx, hop, isUpd]
      have hxnot₁ : x ∉ (L₁ α).map Prod.fst := by
        intro hm
        obtain ⟨⟨y, o'⟩, hy, hyx⟩ := List.mem_map.1 hm
        simp only at hyx; subst hyx
        have := hc₁.lin.op_eq _ hy
        simp only [opOf_skel] at this
        rw [hop] at this; cases this
        exact hxnc (hc₁.late _ hy rfl)
      have hxin₂ : x ∈ (L₂ α).map Prod.fst := hc₂.early x _ hop rfl
      refine ⟨?_, ?_, ?_⟩
      · intro k
        by_cases hk : k = p
        · subst hk; simp [hI.mem_own k, hl]
        · simp [Function.update_of_ne hk, hI.mem_own k]
      · intro k
        by_cases hk : k = p
        · subst hk
          unfold ProcInv
          simp only [Function.update_self, hL₁, hL₂, List.append_nil, usum_append,
            usum_singleton, hx, ite_true, BCOp.val_update]
          exact ⟨trivial, by simp at hp2; omega, by simpa using hp3⟩
        · have hpk : p ≠ k := fun h => hk h.symm
          exact procInv_other (hI.proc k) (by simp [Function.update_of_ne hk])
            (by simp [Function.update_of_ne hk]) hL₁ hL₂ (by simp [usum_singleton, hx, hpk]) rfl
            (curOp_append_ret_of_ne α 0 hpk)
      · intro a r' ha
        rw [respOf_append_ret] at ha
        split_ifs at ha with hax
        · cases ha
          rw [hax]
          exact ⟨0, 0, by rw [hL₁]; exact tau_concat_update v hxnot₁,
            by rw [hL₂, List.append_nil]; exact tau_of_update hc₂.lin hxin₂ hop, le_rfl, le_rfl⟩
        · rw [hL₁, hL₂]; exact done_append (hI.done a r' ha)
    | rd j s =>
      obtain ⟨hp1, hp2, hp3, hj, w, hw, hwle, hs1, hs2⟩ := hP
      have hjn : ¬ j < n := by
        intro hjn
        simp [Impl.step, hpend, alg2, hl, hjn] at hs
      have hjeq : j = n := by omega
      rw [hjeq] at hs1 hs2
      have hr : r = s := by
        by_contra h
        simp [Impl.step, hpend, alg2, hl, h, hjn] at hs
      subst hr
      have hstep : (alg2 n).step C (.ret p r) = some { C with
          pend := Function.update C.pend p none,
          loc := Function.update C.loc p ⟨own, .idle⟩ } := by
        simp [Impl.step, hpend, alg2, hl, hjn]
      rw [hstep] at hs; cases hs
      have hop : opOf α x = some .read := ((alg2 n).run_pend_curOp hrun hp1).2.2
      have hL₁ : L₁ (α ++ [.ret p r]) = L₁ α ++ [] := by
        rw [hcat₁]; simp [canonEnt, ← hx, hop, isUpd]
      have hL₂ : L₂ (α ++ [.ret p r]) = L₂ α ++ [(x, .read)] := by
        rw [hcat₂]; simp [canonEnt, ← hx, hop, isUpd]
      have hxnot₂ : x ∉ (L₂ α).map Prod.fst := by
        intro hm
        obtain ⟨⟨y, o'⟩, hy, hyx⟩ := List.mem_map.1 hm
        simp only at hyx; subst hyx
        have := hc₂.lin.op_eq _ hy
        simp only [opOf_skel] at this
        rw [hop] at this; cases this
        exact hxnc (hc₂.late _ hy rfl)
      refine ⟨?_, ?_, ?_⟩
      · intro k
        by_cases hk : k = p
        · subst hk; simp [hI.mem_own k, hl]
        · simp [Function.update_of_ne hk, hI.mem_own k]
      · intro k
        by_cases hk : k = p
        · subst hk
          unfold ProcInv
          simp only [Function.update_self, hL₁, hL₂, List.append_nil, usum_append,
            usum_singleton_read, add_zero]
          exact ⟨trivial, hp2, hp3⟩
        · have hpk : p ≠ k := fun h => hk h.symm
          exact procInv_other (hI.proc k) (by simp [Function.update_of_ne hk])
            (by simp [Function.update_of_ne hk]) hL₁ hL₂ rfl (usum_singleton_read _ _)
            (curOp_append_ret_of_ne α r hpk)
      · intro a r' ha
        rw [respOf_append_ret] at ha
        split_ifs at ha with hax
        · cases ha
          rw [hax]
          refine ⟨∑ i, w i, ∑ k, usum (L₂ α) k, by rw [hL₁, List.append_nil]; exact hw,
            by rw [hL₂]; exact tau_concat_read hxnot₂, ?_, ?_⟩
          · rw [← psum_n]; exact hs1
          · rw [← psum_n]; exact hs2
        · rw [hL₁, hL₂]; exact done_append (hI.done a r' ha)

/-! ### Lemma 2 and Theorem 2 -/

/-- The proof of **Lemma 2**: in every execution of Algorithm 2, every completed operation returns
a value between the values it gets in `τ(H₁)` and `τ(H₂)`, where `H₁ = L₁ α` (reads at their
invocation, updates at their response) and `H₂ = L₂ α` (updates at their invocation, reads at
their response) are the canonical linearizations of the paper's proof. -/
theorem alg2_sandwich {α : List (Label (Fin n) batchedCounter)} (hv : (alg2 n).Valid α) :
    ∀ a r, respOf α a = some r → ∃ r₁ r₂, tau bcQ (L₁ α) a = some r₁ ∧
      tau bcQ (L₂ α) a = some r₂ ∧ r₁ ≤ r ∧ r ≤ r₂ := by
  obtain ⟨C, hC⟩ := hv
  exact ((alg2 n).run_induction (Q := Inv) inv_init
    (fun _ _ _ _ h hI hs => inv_step h hI hs) hC).done

/-- **Lemma 2.** Algorithm 2 is an IVL implementation of a batched counter. -/
theorem lemma2 : (alg2 n).IVL := fun _ hv =>
  ⟨_, _, isSkelLin_canon _ hv.wellFormed, isSkelLin_canon _ hv.wellFormed, alg2_sandwich hv⟩

/-- Potential: the number of base-object accesses left in the current operation. -/
def pot (n : ℕ) (l : Loc) : ℕ :=
  match l.pc with
  | .upd _ => 1
  | .rd j _ => n - j
  | _ => 0

lemma pot_dec : ∀ (p : Fin n) (l : Loc) (i : Fin n) (o : RWOp ℕ) (k : ℕ → Loc),
    (alg2 n).act p l = .access i o k → ∀ x, pot n (k x) < pot n l := by
  intro p l i o k h x
  rcases l with ⟨own, pc⟩
  cases pc with
  | idle => simp [alg2] at h
  | updRet v => simp [alg2] at h
  | upd v =>
    simp only [alg2, Action.access.injEq] at h
    obtain ⟨rfl, -, hk⟩ := h
    subst hk
    simp [pot]
  | rd j s =>
    by_cases hj : j < n
    · simp only [alg2, hj, dite_true, Action.access.injEq] at h
      obtain ⟨rfl, -, hk⟩ := h
      subst hk
      simp only [pot]; omega
    · simp [alg2, hj] at h

/-- Algorithm 2 is wait-free. -/
theorem alg2_waitFree : (alg2 n).WaitFree := (alg2 n).waitFree_of_potential (fun _ => pot n) pot_dec

/-- Register `i` is written only by process `i`: the registers are single-writer. -/
theorem alg2_swmr : (alg2 n).SWMR id := by
  intro p l i o k h v ho
  subst ho
  rcases l with ⟨own, pc⟩
  cases pc with
  | idle => simp [alg2] at h
  | updRet v => simp [alg2] at h
  | upd v' =>
    simp only [alg2, Action.access.injEq] at h
    exact h.1.symm
  | rd j s =>
    by_cases hj : j < n
    · simp only [alg2, hj, dite_true, Action.access.injEq] at h
      obtain ⟨rfl, h2, -⟩ := h
      cases h2
    · simp [alg2, hj] at h

/-- Every `update` takes (at most) one step. -/
theorem alg2_update_steps : (alg2 n).StepsLE (fun o => isUpd o = true) 1 := by
  intro α p o γ ho hv hret
  obtain ⟨l, hl⟩ := (alg2 n).tauSteps_le_potential_invoke (fun _ => pot n) pot_dec hv hret
  cases o with
  | update v => simpa [alg2, pot] using hl
  | read => simp [isUpd] at ho

/-- Every `read` takes (at most) `n` steps. -/
theorem alg2_read_steps : (alg2 n).StepsLE (fun o => o = .read) n := by
  intro α p o γ ho hv hret
  subst ho
  obtain ⟨l, hl⟩ := (alg2 n).tauSteps_le_potential_invoke (fun _ => pot n) pot_dec hv hret
  simpa [alg2, pot] using hl

variable (n) in
/-- **Theorem 2.** There is a bounded wait-free IVL implementation of a batched counter for `n`
processes using only SWMR registers (register `i` is written only by process `i`), in which
every `update` takes at most one step (`O(1)`) and every `read` at most `n` steps (`O(n)`); all
operations may be invoked by all processes. -/
theorem theorem2 : ∃ (L : Type) (I : Impl batchedCounter (fun _ : Fin n => register ℕ 0) (Fin n) L),
    (∀ p o, I.allowed p o) ∧ I.SWMR id ∧ I.WaitFree ∧ I.IVL ∧
      I.StepsLE (fun o => isUpd o = true) 1 ∧ I.StepsLE (fun o => o = .read) n :=
  ⟨Loc, alg2 n, fun _ _ => trivial, alg2_swmr, alg2_waitFree, lemma2, alg2_update_steps,
    alg2_read_steps⟩

end Podc.IntermediateValueLin.Alg2
