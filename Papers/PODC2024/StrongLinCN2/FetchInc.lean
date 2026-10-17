import Podc.StrongLin.Basic
import Podc.SharedMemory.Objects

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

lemma linState_append_single (Lin : List (OpId P × rfaiObj.Op)) (x : OpId P) (o : FAIOp) :
    linState (Lin ++ [(x, o)]) = (rfaiObj.δ (linState Lin) o).1 := by
  rw [linState, List.map_append, ObjSpec.runOps_append]; rfl

lemma linState_le_append_single (Lin : List (OpId P × rfaiObj.Op)) (x : OpId P) (o : FAIOp) :
    linState Lin ≤ linState (Lin ++ [(x, o)]) := by
  rw [linState_append_single]; cases o <;> simp

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

/-- The current instance of `p`. -/
abbrev cur (α : List (Label P rfaiObj)) (p : P) : OpId P := (p, (respsOf α p).length)

/-- Status of a process. -/
def St (α : List (Label P rfaiObj)) (C : Config rfaiObj B P Loc)
    (Lin : List (OpId P × rfaiObj.Op)) (p : P) : Prop :=
  match C.loc p with
  | .idle => C.pend p = none
  | .acc o i => C.pend p = some o ∧ cur α p ∉ Lin.map Prod.fst ∧ opOf α (cur α p) = some o ∧
      i ≤ linState Lin
  | .retv v => C.pend p ≠ none ∧ linResp Lin (cur α p) = some v

/-- The simulation invariant: the set entries form the prefix `M[0..F-1]` where `F` is the
abstract state. -/
structure Inv (α : List (Label P rfaiObj)) (C : Config rfaiObj B P Loc)
    (Lin : List (OpId P × rfaiObj.Op)) : Prop where
  lin : IsLinearization α Lin
  mem : ∀ j, C.mem j = decide (j < linState Lin)
  st : ∀ p, St α C Lin p

lemma cur_append_inv (α : List (Label P rfaiObj)) (p q : P) (o : rfaiObj.Op) :
    cur (α ++ [.inv p o]) q = cur α q := by simp [cur, respsOf_append]

lemma cur_append_tau (α : List (Label P rfaiObj)) (p q : P) :
    cur (α ++ [.tau p]) q = cur α q := by simp [cur, respsOf_append]

lemma cur_append_ret_of_ne (α : List (Label P rfaiObj)) {p q : P} (r : ℕ) (h : p ≠ q) :
    cur (α ++ [.ret p r]) q = cur α q := by simp [cur, respsOf_append, h]

lemma opOf_append_of_opOf {α : List (Label P rfaiObj)} {x : OpId P} {o : rfaiObj.Op}
    (ℓ : Label P rfaiObj) (h : opOf α x = some o) : opOf (α ++ [ℓ]) x = some o := by
  have hinv : Invoked α x := by simp only [opOf] at h; exact (List.getElem?_eq_some_iff.1 h).1
  rw [opOf_append_of_invoked hinv, h]

/-- Transfer of the status of a process whose local state and pending operation do not change,
when the linearization is extended without it and the abstract state does not decrease. -/
lemma St.transfer {α α' : List (Label P rfaiObj)} {C C' : Config rfaiObj B P Loc}
    {Lin M : List (OpId P × rfaiObj.Op)} {q : P} (h : St α C Lin q)
    (hloc : C'.loc q = C.loc q) (hpend : C'.pend q = C.pend q) (hcur : cur α' q = cur α q)
    (hop : ∀ o, opOf α (cur α q) = some o → opOf α' (cur α q) = some o)
    (hM : cur α q ∉ M.map Prod.fst) (hF : linState Lin ≤ linState (Lin ++ M)) :
    St α' C' (Lin ++ M) q := by
  unfold St at h ⊢
  rw [hloc, hpend, hcur]
  split at h
  · exact h
  · refine ⟨h.1, ?_, hop _ h.2.2.1, h.2.2.2.trans hF⟩
    simp only [List.map_append, List.mem_append, not_or]; exact ⟨h.2.1, hM⟩
  · refine ⟨h.1, ?_⟩
    rw [linResp_append_of_mem _ (linResp_isSome_iff.1 (by rw [h.2]; rfl)), h.2]

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
      have hnot : cur α p ∉ Lin.map Prod.fst := by
        intro hm
        have := hI.lin.invoked_of_mem hm
        simp [Invoked] at this; omega
      have hop : opOf (α ++ [.inv p o]) (cur α p) = some o := by
        simp [opOf, opsOf_append, ← hlen]
      refine ⟨[], ?_⟩
      rw [List.append_nil]
      refine ⟨hI.lin.append_inv p o, by rw [hmem]; exact hI.mem, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq
        unfold St
        rw [hloc, Function.update_self, hpend, Function.update_self, cur_append_inv]
        exact ⟨rfl, hnot, hop, Nat.zero_le _⟩
      · simpa using (hI.st q).transfer (α' := α ++ [.inv p o]) (C' := C') (M := [])
          (by rw [hloc, Function.update_of_ne hq]) (by rw [hpend, Function.update_of_ne hq])
          (cur_append_inv _ _ _ _) (fun o' h => opOf_append_of_opOf _ h) (by simp) (by simp)
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
        have hnc : ¬ Completed α (cur α p) := by simp [Completed]
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
              rw [hloc, Function.update_self, hb, hpend, cur_append_tau]
              exact ⟨hp1, hp2, opOf_append_of_opOf _ hp3, hjF⟩
            · simpa using (hI.st q).transfer (M := []) (hlocq q hq) (hpendq q)
                (cur_append_tau _ _ _) (fun o' h => opOf_append_of_opOf _ h) (by simp) (by simp)
        | false =>
          -- `M[j]` is the first unset entry: the linearization point
          have hjF : j = linState Lin := by
            have := hI.mem j; rw [hb] at this; simp at this; omega
          refine ⟨[(cur α p, o')], (hI.lin.push hp3 hp2 hnc).append_tau p, fun j' => ?_,
            fun q => ?_⟩
          · rw [hmem, linState_append_single]; subst hjF; exact mem_update_eq o' hI.mem j'
          · by_cases hq : q = p
            · subst hq
              unfold St
              rw [hloc, Function.update_self, hb, hpend, cur_append_tau,
                linResp_append_singleton_self _ hp2, resp_δ, hjF]
              exact ⟨by rw [hp1]; simp, rfl⟩
            · exact (hI.st q).transfer (hlocq q hq) (hpendq q) (cur_append_tau _ _ _)
                (fun o' h => opOf_append_of_opOf _ h)
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
        refine ⟨hI.lin.append_ret_of_linResp hst.2, by rw [hmem]; exact hI.mem, fun q => ?_⟩
        by_cases hq : q = p
        · subst hq; unfold St; rw [hloc, Function.update_self, hpend, Function.update_self]
        · simpa using (hI.st q).transfer (M := []) (by rw [hloc, Function.update_of_ne hq])
            (by rw [hpend, Function.update_of_ne hq]) (cur_append_ret_of_ne _ _ (Ne.symm hq))
            (fun o' h => opOf_append_of_opOf _ h) (by simp) (by simp)

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

lemma sum_lt_of_one [Fintype P] (f g : P → ℕ) (p : P) (h1 : ∀ q, q ≠ p → g q = f q)
    (h2 : g p < f p) : ∑ q, g q < ∑ q, f q := by
  apply Finset.sum_lt_sum
  · intro q _; by_cases hq : q = p
    · subst hq; exact h2.le
    · rw [h1 q hq]
  · exact ⟨p, Finset.mem_univ _, h2⟩

lemma sum_lt_of_drop [Fintype P] (f g : P → ℕ) (p : P) (h1 : ∀ q, q ≠ p → g q ≤ f q + 1)
    (h2 : g p + Fintype.card P ≤ f p) : ∑ q, g q < ∑ q, f q := by
  rw [← Finset.add_sum_erase _ g (Finset.mem_univ p),
    ← Finset.add_sum_erase _ f (Finset.mem_univ p)]
  have h3 : ∑ q ∈ Finset.univ.erase p, g q ≤ ∑ q ∈ Finset.univ.erase p, (f q + 1) :=
    Finset.sum_le_sum (fun q hq => h1 q (Finset.ne_of_mem_erase hq))
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ] at h3
  have : 0 < Fintype.card P := Fintype.card_pos_iff.2 ⟨p⟩
  omega

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
    apply sum_lt_of_one _ _ p
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
        apply sum_lt_of_one _ _ p
        · intro q hq; simp only [hlocq q hq, hF, hF']
        · simp only [hloc, Function.update_self, hb, hF, hF', hl, wt, ite_true]; omega
      | false =>
        have hjF' : j = F := by
          have := hI.mem j; rw [hb] at this; simp at this; omega
        have hF' : front C'.mem = (rfaiObj.δ F o').1 := front_eq (fun j' => by
          rw [hmem]; subst hjF'; exact mem_update_eq o' hI.mem j')
        have hpF : wt (Fintype.card P) (front C'.mem) (C'.loc p) = 0 := by
          simp only [hloc, Function.update_self, hb]; simp [wt]
        apply sum_lt_of_drop _ _ p
        · intro q hq
          rw [hlocq q hq, hF, hF']
          cases C.loc q <;> cases o' <;> simp [wt] <;> omega
        · rw [hpF, hF, hl]; simp only [wt]; omega

-- CSLib candidate
/-- A prefix of an infinite execution is a finite execution. -/
lemma run_range {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {L : Type} [DecidableEq ι]
    {I : Impl A B P L} (e : I.InfExec) (t : ℕ) :
    I.run ((List.range t).map e.lbl) = some (e.cfg t) := by
  induction t with
  | zero => simp [e.cfg_zero]
  | succ t ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, I.run_append_of_eq ih,
      I.runFrom_singleton, e.step_eq]

/-- **Lock-freedom** (for finitely many processes): in every infinite execution, infinitely many
operations return. (Even without the hypothesis that infinitely many steps are taken: an
execution suffix without responses is finite.) -/
theorem lockFree [Fintype P] : (impl P).LockFree := by
  intro e _ N
  by_contra hcon
  push Not at hcon
  have key : ∀ k, pot (e.cfg (N + k)) + k ≤ pot (e.cfg N) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := pot_lt (run_range e (N + k)) (e.step_eq (N + k))
        (fun p r => hcon (N + k) (by omega) p r)
      rw [show N + (k + 1) = N + k + 1 by omega]; omega
  have := key (pot (e.cfg N) + 1)
  omega

/-- **Theorem 9** (Attiya–Castañeda–Enea, PODC 2024): the implementation of Section 4.2 is a
lock-free strongly-linearizable implementation of readable fetch&increment from readable
test&set objects. -/
theorem theorem9 [Fintype P] : (impl P).LockFree ∧ (impl P).StronglyLinearizable :=
  ⟨lockFree, stronglyLinearizable⟩

end StrongLinCN2.FAI
