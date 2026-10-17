import Podc.Algebra.BigOperators.Update
import Podc.SharedMemory.Objects.FetchAdd
import Podc.SharedMemory.Objects.TestAndSet
import Podc.SharedMemory.Potential
import Podc.SharedMemory.StrongLin.Basic

/-!
# Readable fetch&increment from readable test&set (Theorem 9)

Attiya, Castañeda and Enea, *Strong Linearizability using Primitives with Consensus Number 2*,
PODC 2024, Section 4.2. The processes share an infinite array `M[0], M[1], …` of readable
test&set objects (base objects `rtasObj`, indexed by `ℕ`, all initially `0` = `false`).

* `fetch&increment()`: apply test&set to `M[0], M[1], …` in increasing order until one returns
  `0`; return its index.
* `read()`: read `M[0], M[1], …` until one reads `0`; return its index.

Linearization (paper): every operation is linearized at the step where it obtains `0` (by a
test&set or a read). The set entries always form a prefix `M[0..F-1]` and the abstract state is
`F` (the paper says "the maximum index `i` such that `M[i]` is `0`", a typo for the minimum).
We prove that this is a forward simulation (`linSim`), hence the implementation is strongly
linearizable, and that it is lock-free (`lockFree`): a potential that strictly decreases with
every invocation and every internal step (`pot_lt`), so an execution without responses is finite.

Processes: any finite type `P` (finiteness is only needed for lock-freedom). The implementation
is not wait-free (a `fetch&increment` may be overtaken forever); we do not formalize this.
-/

namespace StrongLinCN2.FAI

open Cslib.SharedMemory

/-- Base objects: the readable test&set objects `M[j]`, `j : ℕ`. -/
abbrev B : ℕ → ObjSpec := fun _ => rtasObj

/-- The primitive applied to `M[j]` by an operation. -/
def toB : FAIOp → RTASOp
  | .fai => .tas
  | .read => .read

/-- Local states (program counters). -/
inductive Loc where
  | idle
  /-- Operation `o`, about to access `M[i]`. -/
  | acc (o : FAIOp) (i : ℕ)
  /-- About to return `v`. -/
  | retv (v : ℕ)
  deriving DecidableEq

variable (P : Type) [DecidableEq P]

/-- The implementation of Section 4.2. -/
def impl : Impl rfaiObj B P Loc where
  memInit _ := false
  locInit _ := .idle
  invoke _ _ o := .acc o 0
  act _
    | .idle => .ret 0 .idle
    | .acc o i => .access i (toB o) (fun b => if b then .acc o (i + 1) else .retv i)
    | .retv v => .ret v .idle

set_option linter.unusedSectionVars false

variable {P}

/-! ## Auxiliary facts about the objects -/

/-- The bit of `M[i]` after applying `toB o` to it in state `b`. -/
def setAfter : FAIOp → Bool → Bool
  | .fai, _ => true
  | .read, b => b

lemma δ_toB (b : Bool) (o : FAIOp) : rtasObj.δ b (toB o) = (setAfter o b, b) := by
  cases o <;> rfl

lemma linState_le_append_single (Lin : List (OpId P × rfaiObj.Op)) (x : OpId P) (o : FAIOp) :
    linState Lin ≤ linState (Lin ++ [(x, o)]) := by
  rw [linState_concat]; cases o <;> simp

lemma resp_δ (F : ℕ) (o : FAIOp) : (rfaiObj.δ F o).2 = F := by cases o <;> rfl

/-- An access to an entry inside the set prefix does not change the memory. -/
lemma mem_update_lt {m : ℕ → Bool} {F i : ℕ} (o : FAIOp) (hm : ∀ j, m j = decide (j < F))
    (hi : i < F) (j : ℕ) : Function.update m i (setAfter o (m i)) j = decide (j < F) := by
  by_cases hj : j = i
  · subst hj; rw [Function.update_self, hm]; cases o <;> simp [setAfter, hi]
  · rw [Function.update_of_ne hj, hm]

/-- An access to the first unset entry extends the set prefix iff it is a test&set. -/
lemma mem_update_eq {m : ℕ → Bool} {F : ℕ} (o : FAIOp) (hm : ∀ j, m j = decide (j < F))
    (j : ℕ) : Function.update m F (setAfter o (m F)) j = decide (j < (rfaiObj.δ F o).1) := by
  by_cases hj : j = F
  · subst hj; rw [Function.update_self, hm]; cases o <;> simp [setAfter]
  · rw [Function.update_of_ne hj, hm]
    cases o
    · by_cases h : j < F <;> simp [h] <;> omega
    · rfl

/-! ## The simulation invariant -/

/-- Status of a process. -/
def St (α : List (Label P rfaiObj)) (C : Config rfaiObj B P Loc)
    (Lin : List (OpId P × rfaiObj.Op)) (p : P) : Prop :=
  match C.loc p with
  | .idle => C.pend p = none
  | .acc o i => C.pend p = some o ∧ curOp α p ∉ Lin.map Prod.fst ∧ opOf α (curOp α p) = some o ∧
      i ≤ linState Lin
  | .retv v => C.pend p ≠ none ∧ rfaiObj.respIn rfaiObj.init Lin (curOp α p) = some v

/-- The simulation invariant: the set entries form the prefix `M[0..F-1]` where `F` is the
abstract state. -/
structure Inv (α : List (Label P rfaiObj)) (C : Config rfaiObj B P Loc)
    (Lin : List (OpId P × rfaiObj.Op)) : Prop where
  lin : IsLinearization α Lin
  mem : ∀ j, C.mem j = decide (j < linState Lin)
  st : ∀ p, St α C Lin p

/-- Transfer of the status of a process whose local state and pending operation do not change,
when the linearization is extended without it and the abstract state does not decrease. -/
lemma St.transfer {α α' : List (Label P rfaiObj)} {C C' : Config rfaiObj B P Loc}
    {Lin M : List (OpId P × rfaiObj.Op)} {q : P} (h : St α C Lin q)
    (hloc : C'.loc q = C.loc q) (hpend : C'.pend q = C.pend q) (hcur : curOp α' q = curOp α q)
    (hop : ∀ o, opOf α (curOp α q) = some o → opOf α' (curOp α q) = some o)
    (hM : curOp α q ∉ M.map Prod.fst) (hF : linState Lin ≤ linState (Lin ++ M)) :
    St α' C' (Lin ++ M) q := by
  unfold St at h ⊢
  rw [hloc, hpend, hcur]
  split at h
  · exact h
  · refine ⟨h.1, ?_, hop _ h.2.2.1, h.2.2.2.trans hF⟩
    simp only [List.map_append, List.mem_append, not_or]; exact ⟨h.2.1, hM⟩
  · refine ⟨h.1, ?_⟩
    exact ObjSpec.respIn_append_of_eq_some h.2 _

lemma linSim : (impl P).LinSim Inv where
  init := by
    refine ⟨isLinearization_nil, fun j => ?_, fun p => ?_⟩
    · simp [impl, Impl.initCfg, linState, ObjSpec.runOps]
    · simp [St, impl, Impl.initCfg]
  lin _ _ _ _ h := h.lin
  step := by
    intro α C Lin ℓ C' hrun hI hstep
    have hcnt := (impl P).run_counts hrun
    cases ℓ with
    | inv p o =>
      obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv hstep
      have hlen : (opsOf α p).length = (respsOf α p).length := by
        rcases hcnt p with ⟨-, h1⟩ | ⟨h1, -⟩
        · exact h1
        · exact absurd h0 h1
      have hidle : C.loc p = .idle := by
        have := hI.st p
        unfold St at this
        split at this <;> simp_all
      have hnot : curOp α p ∉ Lin.map Prod.fst := by
        intro hm
        have := hI.lin.invoked_of_mem hm
        simp [Invoked] at this; omega
      have hop : opOf (α ++ [.inv p o]) (curOp α p) = some o := by
        simp [opOf, opsOf_append, ← hlen]
      refine ⟨[], ?_⟩
      rw [List.append_nil]
      refine ⟨hI.lin.append_inv p o, by rw [hmem]; exact hI.mem, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq
        unfold St
        rw [hloc, Function.update_self, hpend, Function.update_self, curOp_append_inv]
        exact ⟨rfl, hnot, hop, Nat.zero_le _⟩
      · simpa using (hI.st q).transfer (α' := α ++ [.inv p o]) (C' := C') (M := [])
          (by rw [hloc, Function.update_of_ne hq]) (by rw [hpend, Function.update_of_ne hq])
          (curOp_append_inv _ _ _ _) (fun _ h => opOf_append_of_eq_some h _) (by simp) (by simp)
    | tau p =>
      obtain ⟨h0, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hstep
      have hlocq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
        rw [hloc, Function.update_of_ne hq]
      have hpendq : ∀ q, C'.pend q = C.pend q := fun q => by rw [hpend]
      have hst := hI.st p
      cases hl : C.loc p with
      | idle => simp [impl, hl] at hact
      | retv v => simp [impl, hl] at hact
      | acc o' j =>
        simp only [impl, hl, Action.access.injEq] at hact
        obtain ⟨rfl, ho, hk⟩ := hact
        have ho' : o = toB o' := (eq_of_heq ho).symm
        subst ho'
        have hk' : k = fun b => if b then Loc.acc o' (j + 1) else Loc.retv j := (eq_of_heq hk).symm
        subst hk'
        unfold St at hst; rw [hl] at hst
        obtain ⟨hp1, hp2, hp3, hp4⟩ := hst
        have hnc : ¬ Completed α (curOp α p) := by simp [Completed]
        have hδ : (B j).δ (C.mem j) (toB o') = (setAfter o' (C.mem j), C.mem j) := δ_toB _ _
        rw [hδ] at hmem hloc
        cases hb : C.mem j with
        | true =>
          -- `M[j]` is set: move on, no linearization
          have hjF : j < linState Lin := by simpa [hI.mem j] using hb
          refine ⟨[], ?_⟩
          rw [List.append_nil]
          refine ⟨hI.lin.append_tau p, fun j' => ?_, fun q => ?_⟩
          · rw [hmem]; exact mem_update_lt o' hI.mem hjF j'
          · by_cases hq : q = p
            · subst hq
              unfold St
              rw [hloc, Function.update_self, hb, hpend, curOp_append_tau]
              exact ⟨hp1, hp2, opOf_append_of_eq_some hp3 _, hjF⟩
            · simpa using (hI.st q).transfer (M := []) (hlocq q hq) (hpendq q)
                (curOp_append_tau _ _ _) (fun _ h => opOf_append_of_eq_some h _) (by simp) (by simp)
        | false =>
          -- `M[j]` is the first unset entry: the linearization point
          have hjF : j = linState Lin := by
            have := hI.mem j; rw [hb] at this; simp at this; omega
          refine ⟨[(curOp α p, o')], (hI.lin.push hp3 hp2 hnc).append_tau p, fun j' => ?_,
            fun q => ?_⟩
          · rw [hmem, linState_concat]; subst hjF; exact mem_update_eq o' hI.mem j'
          · by_cases hq : q = p
            · subst hq
              unfold St
              rw [hloc, Function.update_self, hb, hpend, curOp_append_tau,
                ObjSpec.respIn_concat_self hp2, resp_δ, hjF]
              exact ⟨by rw [hp1]; simp, rfl⟩
            · exact (hI.st q).transfer (hlocq q hq) (hpendq q) (curOp_append_tau _ _ _)
                (fun _ h => opOf_append_of_eq_some h _)
                (by simp only [List.map_cons, List.map_nil, List.mem_singleton]
                    exact fun h => hq (congrArg Prod.fst h))
                (linState_le_append_single _ _ _)
    | ret p r =>
      obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hstep
      have hst := hI.st p
      cases hl : C.loc p with
      | idle => unfold St at hst; rw [hl] at hst; exact absurd hst h0
      | acc o i => simp [impl, hl] at hact
      | retv v =>
        simp only [impl, hl, Action.ret.injEq] at hact
        obtain ⟨rfl, rfl⟩ := hact
        unfold St at hst; rw [hl] at hst
        refine ⟨[], ?_⟩
        rw [List.append_nil]
        refine ⟨hI.lin.append_ret_of_respIn hst.2, by rw [hmem]; exact hI.mem, fun q => ?_⟩
        by_cases hq : q = p
        · subst hq; unfold St; rw [hloc, Function.update_self, hpend, Function.update_self]
        · simpa using (hI.st q).transfer (M := []) (by rw [hloc, Function.update_of_ne hq])
            (by rw [hpend, Function.update_of_ne hq]) (curOp_append_ret_of_ne _ _ (Ne.symm hq))
            (fun _ h => opOf_append_of_eq_some h _) (by simp) (by simp)

/-- **Strong linearizability** of the implementation of Section 4.2. -/
theorem stronglyLinearizable : (impl P).StronglyLinearizable :=
  (impl P).stronglyLinearizable_of_linSim _ linSim

/-! ## Lock-freedom -/

/-- The number of set entries (the first unset index) of a memory. -/
noncomputable def front (m : ℕ → Bool) : ℕ := by
  classical
  exact if h : ∃ j, m j = false then Nat.find h else 0

lemma front_eq {m : ℕ → Bool} {F : ℕ} (h : ∀ j, m j = decide (j < F)) : front m = F := by
  classical
  have hex : ∃ j, m j = false := ⟨F, by simp [h]⟩
  simp only [front, dite_eq_left hex]
  rw [Nat.find_eq_iff]
  refine ⟨by simp [h], fun n hn => by simp [h, hn]⟩

/-- Weight of a local state, given the frontier `F` and the slack `K`. -/
def wt (K F : ℕ) : Loc → ℕ
  | .idle => F + K + 2
  | .acc _ i => F + 1 - i + K
  | .retv _ => 0

/-- The potential: sum of the weights of all processes (slack `K = |P|`). -/
noncomputable def pot [Fintype P] (C : Config rfaiObj B P Loc) : ℕ :=
  ∑ q, wt (Fintype.card P) (front C.mem) (C.loc q)

/-- Every step that is not a response strictly decreases the potential. -/
lemma pot_lt [Fintype P] {α : List (Label P rfaiObj)} {C C' : Config rfaiObj B P Loc}
    {ℓ : Label P rfaiObj} (hrun : (impl P).run α = some C) (h : (impl P).step C ℓ = some C')
    (hℓ : ∀ p r, ℓ ≠ .ret p r) : pot C' < pot C := by
  have hI := (impl P).simLin_spec Inv linSim α C hrun
  set Lin := (impl P).simLin Inv α
  set F := linState Lin
  have hF : front C.mem = F := front_eq hI.mem
  cases ℓ with
  | ret p r => exact absurd rfl (hℓ p r)
  | inv p o =>
    obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
    have hidle : C.loc p = .idle := by
      have := hI.st p
      unfold St at this
      split at this <;> simp_all
    apply Fintype.sum_lt_sum_of_eq_off p
    · intro q hq; simp [hloc, hmem, Function.update_of_ne hq]
    · simp only [hloc, hmem, Function.update_self, hidle, hF]
      simp [impl, wt]; omega
  | tau p =>
    obtain ⟨h0, -, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
    have hlocq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
      rw [hloc, Function.update_of_ne hq]
    have hst := hI.st p
    cases hl : C.loc p with
    | idle => simp [impl, hl] at hact
    | retv v => simp [impl, hl] at hact
    | acc o' j =>
      simp only [impl, hl, Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact
      have ho' : o = toB o' := (eq_of_heq ho).symm
      subst ho'
      have hk' : k = fun b => if b then Loc.acc o' (j + 1) else Loc.retv j := (eq_of_heq hk).symm
      subst hk'
      unfold St at hst; rw [hl] at hst
      have hjF := hst.2.2.2
      have hδ : (B j).δ (C.mem j) (toB o') = (setAfter o' (C.mem j), C.mem j) := δ_toB _ _
      rw [hδ] at hmem hloc
      cases hb : C.mem j with
      | true =>
        have hjF' : j < F := by simpa [hI.mem j] using hb
        have hF' : front C'.mem = F := front_eq (fun j' => by
          rw [hmem]; exact mem_update_lt o' hI.mem hjF' j')
        apply Fintype.sum_lt_sum_of_eq_off p
        · intro q hq; simp only [hlocq q hq, hF, hF']
        · simp only [hloc, Function.update_self, hb, hF, hF', hl, wt, ite_true]; omega
      | false =>
        have hjF' : j = F := by
          have := hI.mem j; rw [hb] at this; simp at this; omega
        have hF' : front C'.mem = (rfaiObj.δ F o').1 := front_eq (fun j' => by
          rw [hmem]; subst hjF'; exact mem_update_eq o' hI.mem j')
        have hpF : wt (Fintype.card P) (front C'.mem) (C'.loc p) = 0 := by
          simp only [hloc, Function.update_self, hb]; simp [wt]
        apply Fintype.sum_lt_sum_of_le_add (c := 1) p
        · intro q hq
          rw [hlocq q hq, hF, hF']
          cases C.loc q <;> cases o' <;> simp [wt] <;> omega
        · rw [hpF, hF, hl, Nat.nsmul_eq_mul, mul_one]; simp only [wt]; omega

/-- **Lock-freedom** (for finitely many processes): in every infinite execution, infinitely many
operations return. (Even without the hypothesis that infinitely many steps are taken: an
execution suffix without responses is finite.) -/
theorem lockFree [Fintype P] : (impl P).LockFree :=
  (impl P).lockFree_of_potential pot fun _ _ _ _ => pot_lt

/-- **Theorem 9** (Attiya–Castañeda–Enea, PODC 2024): the implementation of Section 4.2 is a
lock-free strongly-linearizable implementation of readable fetch&increment from readable
test&set objects. -/
theorem theorem9 [Fintype P] : (impl P).LockFree ∧ (impl P).StronglyLinearizable :=
  ⟨lockFree, stronglyLinearizable⟩

end StrongLinCN2.FAI
