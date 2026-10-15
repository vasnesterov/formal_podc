import Cslib.Computability.Distributed.SharedMemory.Linearization
import Cslib.Computability.Distributed.SharedMemory.Progress
import Mathlib.Data.Finite.Card
import Mathlib

/-!
# The avoidance lower bound (core of Theorem 17 and Theorem 20)

A common abstraction of the proofs of Theorem 17 (class `C_t`) and Theorem 20 (queue with
`Peek`) of Attiya, Bender, Farach-Colton, Oshman, Schiller, *History-Independent Concurrent
Objects*, PODC 2024.

`AvoidData A N` packages:
* a read-only operation `oread`;
* `N` *representative* states `rep 0, …, rep (N-1)` on which `oread` gives pairwise distinct
  responses;
* for `i ≠ j`, a sequence of operations `path i j` from `rep i` to `rep j` such that `oread`
  responds, at every intermediate state, as at `rep i` or as at `rep j` (for `C_t` this is the
  single operation `ochange(rep i, rep j)`; for the queue it is `Enqueue(j), Dequeue()`);
* for every `j`, a sequence of operations `start j` from the initial state to `rep j`.

`not_waitFree_stateQuiescentHI`: if every base object has fewer than `N` states, there is no
wait-free, state-quiescent history-independent implementation in which some process `r` may
invoke `oread` and another process `c` may invoke all operations of the paths.

The proof follows Lemmas 15–16 / 37–38 of the paper: we maintain `N` executions, the `i`-th
of which never lets the reader observe a state answering like `rep i`, while the reader cannot
distinguish them; in each round the changer moves every execution to one of two representative
states whose canonical memory representations agree on the base object the reader accesses
next. The case where the two chosen states coincide with the current one (`q_k = q_{k+1}` in
Lemma 16, where `ochange(q,q)` is undefined) is handled by an empty move (`move`).
-/

namespace Cslib.SharedMemory

open List

/-- Data for the avoidance lower bound. -/
structure AvoidData (A : ObjSpec) (N : ℕ) where
  /-- The read-only operation of the reader. -/
  oread : A.Op
  oread_ro : A.ReadOnly oread
  /-- Representative states. -/
  rep : Fin N → A.State
  /-- `oread` distinguishes the representatives. -/
  resp_inj : Function.Injective (fun i => (A.δ (rep i) oread).2)
  /-- Operation sequences between representatives. -/
  path : Fin N → Fin N → List A.Op
  path_end : ∀ i j, i ≠ j → A.runOps (rep i) (path i j) = rep j
  path_mid : ∀ i j, i ≠ j → ∀ m ≤ (path i j).length,
    (A.δ (A.runOps (rep i) ((path i j).take m)) oread).2 = (A.δ (rep i) oread).2 ∨
    (A.δ (A.runOps (rep i) ((path i j).take m)) oread).2 = (A.δ (rep j) oread).2
  /-- Operation sequences from the initial state to the representatives. -/
  start : Fin N → List A.Op
  start_end : ∀ j, A.runOps A.init (start j) = rep j

namespace AvoidData

variable {A : ObjSpec} {N : ℕ} (D : AvoidData A N)

/-- The response of `oread` at representative `a`. -/
def resp (a : Fin N) : A.Resp := (A.δ (D.rep a) D.oread).2

/-- Move from `rep i` to `rep j` (empty if `i = j`). -/
def move (i j : Fin N) : List A.Op := if i = j then [] else D.path i j

lemma move_end (i j : Fin N) : A.runOps (D.rep i) (D.move i j) = D.rep j := by
  unfold move; split_ifs with h
  · subst h; rfl
  · exact D.path_end i j h

lemma move_mid (i j : Fin N) (m : ℕ) (hm : m ≤ (D.move i j).length) :
    (A.δ (A.runOps (D.rep i) ((D.move i j).take m)) D.oread).2 = D.resp i ∨
    (A.δ (A.runOps (D.rep i) ((D.move i j).take m)) D.oread).2 = D.resp j := by
  unfold move at hm ⊢; split_ifs with h
  · left; simp [resp]
  · rw [if_neg h] at hm; exact D.path_mid i j h m hm

end AvoidData


end Cslib.SharedMemory

namespace Cslib.SharedMemory

open List

section Main

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
  {N : ℕ} (D : AvoidData A N) (I : Impl A B P L) (c r : P)

/-- The invariant of the construction, for the execution `E` that avoids representative `i`:
the changer `c` is idle and has moved the object to `rep cur`; the reader `r` has a pending
`oread` (and nothing else) and is in local state `lr`; since the reader was invoked, the
object only visited states where `oread` answers like a representative other than `i`. -/
structure Good (E : List (Label P A)) (i cur : Fin N) (lr : L) : Prop where
  run : ∃ C, I.run E = some C ∧ C.loc r = lr ∧ C.pend r = some D.oread ∧ C.pend c = none ∧
    ∀ p, p ≠ c → p ≠ r → C.pend p = none
  procs : ∀ ℓ ∈ E, ℓ.proc = c ∨ ℓ.proc = r
  opsr : opsOf E r = [D.oread]
  respsr : respsOf E r = []
  respsc : (respsOf E c).length = (opsOf E c).length
  state : A.runOps A.init (opsOf E c) = D.rep cur
  cur_ne : cur ≠ i
  pre : ∃ M₀ ≤ (opsOf E c).length, (∀ j < M₀, Precedes E (c, j) (r, 0)) ∧
    ∀ j, M₀ ≤ j → j ≤ (opsOf E c).length → ∃ a, a ≠ i ∧
      (A.δ (A.runOps A.init ((opsOf E c).take j)) D.oread).2 = D.resp a

variable {D I c r}

/-- Under the invariant, operations of processes other than the changer are read-only. -/
lemma Good.readOnly {E : List (Label P A)} {i cur : Fin N} {lr : L} (hg : Good D I c r E i cur lr)
    (β : List (Label P A)) (hβ : ∀ ℓ ∈ β, ℓ.proc = c ∨ ℓ.proc = r)
    (hβr : opsOf β r = []) : ∀ p, p ≠ c → ∀ o ∈ opsOf (E ++ β) p, A.ReadOnly o := by
  intro p hpc o ho
  by_cases hpr : p = r
  · subst hpr; rw [opsOf_append, hg.opsr, hβr] at ho; simp at ho; subst ho; exact D.oread_ro
  · rw [opsOf_eq_nil_of_proc_ne] at ho
    · simp at ho
    · intro ℓ hℓ
      rcases mem_append.1 hℓ with hℓ | hℓ
      · rcases hg.procs ℓ hℓ with h | h <;> rw [h] <;> [exact Ne.symm hpc; exact Ne.symm hpr]
      · rcases hβ ℓ hℓ with h | h <;> rw [h] <;> [exact Ne.symm hpc; exact Ne.symm hpr]

/-- The starting configuration of the construction. -/
lemma Good.init (hcr : c ≠ r) (hof : I.ObstructionFree) (hr : I.allowed r D.oread)
    {a i : Fin N} (hstart : ∀ o ∈ D.start a, I.allowed c o) (hai : a ≠ i) :
    Good D I c r (I.soloOps c I.initCfg (D.start a) ++ [.inv r D.oread]) i a
      (I.invoke r (I.locInit r) D.oread) := by
  classical
  obtain ⟨C₁, h1run, h1c, h1procs, h1ops, h1resps⟩ :=
    I.soloOps_spec hof c (D.start a) hstart (α := []) rfl rfl
  set S := I.soloOps c I.initCfg (D.start a)
  have hSne : ∀ q, q ≠ c → ∀ ℓ ∈ S, ℓ.proc ≠ q := fun q hq ℓ hℓ => by rw [h1procs ℓ hℓ]; exact Ne.symm hq
  have hrS := I.runFrom_other h1run (hSne r (Ne.symm hcr))
  have hSr : opsOf S r = [] := opsOf_eq_nil_of_proc_ne (hSne r (Ne.symm hcr))
  have hSr' : respsOf S r = [] := respsOf_eq_nil_of_proc_ne (hSne r (Ne.symm hcr))
  have hstep : I.step C₁ (.inv r D.oread) = some { C₁ with
      pend := Function.update C₁.pend r (some D.oread),
      loc := Function.update C₁.loc r (I.invoke r (C₁.loc r) D.oread) } := by
    simp [Impl.step, hrS.2, Impl.initCfg, hr]
  refine ⟨⟨_, by rw [Impl.run, Impl.runFrom_append_of_eq I h1run, Impl.runFrom_singleton, hstep],
    ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, hai, ?_⟩
  · simp [hrS.1, Impl.initCfg]
  · simp
  · simp [Function.update_of_ne hcr, h1c]
  · intro p hpc hpr
    simp only [Function.update_of_ne hpr]
    rw [(I.runFrom_other h1run (hSne p hpc)).2]; rfl
  · intro ℓ hℓ
    rcases mem_append.1 hℓ with hℓ | hℓ
    · exact Or.inl (h1procs ℓ hℓ)
    · simp at hℓ; subst hℓ; exact Or.inr rfl
  · simp [hSr]
  · simp [hSr']
  · simp [h1ops, h1resps, Ne.symm hcr]
  · simp [h1ops, Ne.symm hcr, D.start_end]
  · refine ⟨(D.start a).length, by simp [h1ops, Ne.symm hcr], ?_, ?_⟩
    · intro j hj
      refine ⟨S, [.inv r D.oread], rfl, ?_, ?_⟩
      · simp only [Completed]; rw [h1resps]; exact hj
      · simp [Invoked, hSr]
    · intro j hj1 hj2
      simp only [opsOf_append, h1ops, opsOf_cons, Label.invOf_inv, Ne.symm hcr, if_false,
        Option.toList_none, nil_append, opsOf_nil, append_nil] at hj2 ⊢
      rw [take_of_length_le (by omega), D.start_end]
      exact ⟨a, hai, rfl⟩

/-- One round of the construction (Lemma 16): the changer moves the object from `rep cur` to
`rep new` (solo, each operation to completion), then the reader takes one step, accessing base
object `ℓ`, whose state is `can new ℓ` by history independence. -/
lemma Good.extend {E : List (Label P A)} {i cur new : Fin N} {lr : L}
    (hg : Good D I c r E i cur lr) (hcr : c ≠ r) (hof : I.ObstructionFree)
    (hmove : ∀ o ∈ D.move cur new, I.allowed c o)
    {h : List (Label P A) → List (OpId P × A.Op)} (hlin : I.IsLinFun h)
    (can : Fin N → (j : ι) → (B j).State)
    (hcan : ∀ E C a, I.run E = some C → C.StateQuiescent → linState (h E) = D.rep a →
      C.mem = can a)
    (hnew : new ≠ i) {ℓ : ι} {o : (B ℓ).Op} {k : (B ℓ).Resp → L}
    (hact : I.act r lr = .access ℓ o k) :
    ∃ C, I.run E = some C ∧ Good D I c r (E ++ I.soloOps c C (D.move cur new) ++ [.tau r]) i new
      (k ((B ℓ).δ (can new ℓ) o).2) := by
  classical
  obtain ⟨C, hrun, hlr, hpr, hpc, hpo⟩ := hg.run
  obtain ⟨C₁, h1run, h1c, h1procs, h1ops, h1resps⟩ :=
    I.soloOps_spec hof c (D.move cur new) hmove hrun hpc
  set S := I.soloOps c C (D.move cur new) with hS
  have hSne : ∀ q, q ≠ c → ∀ ℓ ∈ S, ℓ.proc ≠ q := fun q hq ℓ hℓ => by
    rw [h1procs ℓ hℓ]; exact Ne.symm hq
  have hrS := I.runFrom_other h1run (hSne r (Ne.symm hcr))
  have hSr : opsOf S r = [] := opsOf_eq_nil_of_proc_ne (hSne r (Ne.symm hcr))
  have hSr' : respsOf S r = [] := respsOf_eq_nil_of_proc_ne (hSne r (Ne.symm hcr))
  have hSproc : ∀ ℓ ∈ S, ℓ.proc = c ∨ ℓ.proc = r := fun ℓ hℓ => Or.inl (h1procs ℓ hℓ)
  have hrunES : I.run (E ++ S) = some C₁ := by rw [Impl.run_append_of_eq I hrun, h1run]
  have hpo1 : ∀ p, p ≠ c → p ≠ r → C₁.pend p = none := fun p hpc' hpr' => by
    rw [(I.runFrom_other h1run (hSne p hpc')).2]; exact hpo p hpc' hpr'
  -- state-quiescence and memory
  have hsq : C₁.StateQuiescent := by
    intro p o' hp
    by_cases hpc' : p = c
    · subst hpc'; simp [h1c] at hp
    · by_cases hpr' : p = r
      · subst hpr'; rw [hrS.2, hpr] at hp; cases hp; exact D.oread_ro
      · simp [hpo1 p hpc' hpr'] at hp
  have hlinES : linState (h (E ++ S)) = D.rep new := by
    rw [(hlin _ ⟨_, hrunES⟩).linState_of_changer (Impl.Valid.wellFormed I ⟨_, hrunES⟩) c
      (hg.readOnly S hSproc hSr)]
    · rw [opsOf_append, h1ops, ObjSpec.runOps_append, hg.state, D.move_end]
    · rw [respsOf_append, opsOf_append, length_append, length_append, hg.respsc, h1ops, h1resps]
  have hmem : C₁.mem = can new := hcan _ _ _ hrunES hsq hlinES
  -- the reader's step
  have hloc1 : C₁.loc r = lr := by rw [hrS.1, hlr]
  have hpend1 : C₁.pend r = some D.oread := by rw [hrS.2, hpr]
  have hstep : I.step C₁ (.tau r) = some { C₁ with
      mem := Function.update C₁.mem ℓ ((B ℓ).δ (C₁.mem ℓ) o).1,
      loc := Function.update C₁.loc r (k ((B ℓ).δ (C₁.mem ℓ) o).2) } := by
    simp [Impl.step, hpend1, hloc1, hact]
  refine ⟨C, hrun, ⟨⟨_, by rw [Impl.run_append_of_eq I hrunES, Impl.runFrom_singleton, hstep],
    ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, hnew, ?_⟩⟩
  · simp [hmem]
  · exact hpend1
  · exact h1c
  · exact hpo1
  · intro ℓ' hℓ'
    rcases mem_append.1 hℓ' with hℓ' | hℓ'
    · rcases mem_append.1 hℓ' with hℓ' | hℓ'
      · exact hg.procs ℓ' hℓ'
      · exact hSproc ℓ' hℓ'
    · simp at hℓ'; subst hℓ'; exact Or.inr rfl
  · simp only [← hS]; simp [hg.opsr, hSr]
  · simp only [← hS]; simp [hg.respsr, hSr']
  · simp only [← hS, opsOf_append, respsOf_append, length_append, hg.respsc, h1ops, h1resps]
    simp
  · simp only [← hS, opsOf_append, h1ops]
    simp [ObjSpec.runOps_append, hg.state, D.move_end]
  · obtain ⟨M₀, hM₀, hprec, havoid⟩ := hg.pre
    have hops : opsOf (E ++ S ++ [.tau r]) c = opsOf E c ++ D.move cur new := by
      simp [h1ops]
    simp only [← hS]
    refine ⟨M₀, by rw [hops, length_append]; omega, fun j hj => ?_, ?_⟩
    · rw [append_assoc]; exact (hprec j hj).mono
    · intro j hj1 hj2
      rw [hops, take_append]
      rw [hops, length_append] at hj2
      by_cases hjle : j ≤ (opsOf E c).length
      · rw [show j - (opsOf E c).length = 0 by omega, take_zero, append_nil]
        exact havoid j hj1 hjle
      · rw [take_of_length_le (by omega), ObjSpec.runOps_append, hg.state]
        rcases D.move_mid cur new (j - (opsOf E c).length) (by omega) with h1 | h1
        · exact ⟨cur, hg.cur_ne, h1⟩
        · exact ⟨new, hnew, h1⟩

/-- Lemma 15 for the constructed executions: if the reader returned `x` now, `x` would be the
response of a representative other than `i`. -/
lemma Good.ret_resp {E : List (Label P A)} {i cur : Fin N} {lr : L}
    (hg : Good D I c r E i cur lr) {h : List (Label P A) → List (OpId P × A.Op)}
    (hlin : I.IsLinFun h) {x : A.Resp} {l : L} (hact : I.act r lr = .ret x l) :
    ∃ a, a ≠ i ∧ x = D.resp a := by
  classical
  obtain ⟨C, hrun, hlr, hpr, hpc, hpo⟩ := hg.run
  obtain ⟨C', hstep⟩ : ∃ C', I.step C (.ret r x) = some C' := by
    simp [Impl.step, hpr, hlr, hact]
  have hrun' : I.run (E ++ [.ret r x]) = some C' := by
    rw [Impl.run_append_of_eq I hrun, Impl.runFrom_singleton, hstep]
  have hval : I.Valid (E ++ [.ret r x]) := ⟨_, hrun'⟩
  have hL := hlin _ hval
  obtain ⟨M₀, hM₀, hprec, havoid⟩ := hg.pre
  have hβ : ∀ ℓ ∈ [Label.ret r x], ℓ.proc = c ∨ ℓ.proc = r := by simp [Label.proc]
  have hro := hg.readOnly [.ret r x] hβ (by simp)
  have hresp : respOf (E ++ [.ret r x]) (r, 0) = some x := by simp [respOf, hg.respsr]
  obtain ⟨j, hj1, hj2, o, ho, hx⟩ := hL.resp_eq (Impl.Valid.wellFormed I hval) c
    (fun y hy hyc => hro _ hyc _ (hL.op_mem hy)) hresp M₀ (fun j hj => (hprec j hj).mono)
  have hopsc : opsOf (E ++ [.ret r x]) c = opsOf E c := by simp
  have ho' : o = D.oread := by simp [opOf, hg.opsr] at ho; exact ho.symm
  subst ho'
  rw [hopsc] at hj2 hx
  obtain ⟨a, ha, hra⟩ := havoid j hj1 hj2
  exact ⟨a, ha, hx.trans hra⟩

lemma opsOf_length_le_of_prefix {α β : List (Label P A)} (h : α <+: β) (p : P) :
    (opsOf α p).length ≤ (opsOf β p).length :=
  (h.sublist.filterMap _).length_le

lemma respsOf_length_le_of_prefix {α β : List (Label P A)} (h : α <+: β) (p : P) :
    (respsOf α p).length ≤ (respsOf β p).length :=
  (h.sublist.filterMap _).length_le

variable (D I c r)

/-- **Avoidance lower bound** (core of Theorems 17 and 20). If every base object has fewer than
`N` states, no implementation in which a process `r` may invoke `oread` and another process `c`
may invoke the operations of all paths is both wait-free and state-quiescent history
independent. -/
theorem not_waitFree_stateQuiescentHI (hN : 2 ≤ N) (hcr : c ≠ r) (hr : I.allowed r D.oread)
    (hpath : ∀ i j, ∀ o ∈ D.path i j, I.allowed c o)
    (hstart : ∀ j, ∀ o ∈ D.start j, I.allowed c o)
    (hB : ∀ j, Finite (B j).State ∧ Nat.card (B j).State < N) :
    ¬ (I.WaitFree ∧ I.StateQuiescentHI) := by
  classical
  rintro ⟨hwf, h, hlin, hhi⟩
  have hof := hwf.obstructionFree
  -- reference executions and canonical representations
  have href : ∀ a, ∃ C, I.run (I.soloOps c I.initCfg (D.start a)) = some C ∧
      C.StateQuiescent ∧ linState (h (I.soloOps c I.initCfg (D.start a))) = D.rep a := by
    intro a
    obtain ⟨C₁, h1run, h1c, h1procs, h1ops, h1resps⟩ :=
      I.soloOps_spec hof c (D.start a) (hstart a) (α := []) rfl rfl
    have hne : ∀ q, q ≠ c → ∀ ℓ ∈ I.soloOps c I.initCfg (D.start a), ℓ.proc ≠ q :=
      fun q hq ℓ hℓ => by rw [h1procs ℓ hℓ]; exact Ne.symm hq
    refine ⟨C₁, h1run, ?_, ?_⟩
    · apply Config.Quiescent.stateQuiescent
      intro p
      by_cases hp : p = c
      · subst hp; exact h1c
      · rw [(I.runFrom_other h1run (hne p hp)).2]; rfl
    · rw [(hlin _ ⟨_, h1run⟩).linState_of_changer (Impl.Valid.wellFormed I ⟨_, h1run⟩) c, h1ops,
        D.start_end]
      · intro p hp o ho; rw [opsOf_eq_nil_of_proc_ne (hne p hp)] at ho; simp at ho
      · rw [h1ops, h1resps]
  choose Cref hCref using href
  let can : Fin N → (j : ι) → (B j).State := fun a => (Cref a).mem
  have hcan : ∀ E C a, I.run E = some C → C.StateQuiescent → linState (h E) = D.rep a →
      C.mem = can a := fun E C a h1 h2 h3 =>
    hhi E _ C (Cref a) h1 (hCref a).1 h2 (hCref a).2.1 (h3.trans (hCref a).2.2.symm)
  have hmove : ∀ a b, ∀ o ∈ D.move a b, I.allowed c o := by
    intro a b o ho; unfold AvoidData.move at ho; split_ifs at ho
    · simp at ho
    · exact hpath a b o ho
  -- the rounds
  let i₀ : Fin N := ⟨0, by omega⟩
  let i₁ : Fin N := ⟨1, by omega⟩
  let St := (Fin N → List (Label P A)) × (Fin N → Fin N) × L
  let GoodAll : St → Prop := fun s => ∀ i, Good D I c r (s.1 i) i (s.2.1 i) s.2.2
  have hinit : ∃ s, GoodAll s := by
    let other : Fin N → Fin N := fun i => if i = i₀ then i₁ else i₀
    have hother : ∀ i, other i ≠ i := by
      intro i; simp only [other]; split_ifs with h1
      · subst h1; simp [i₀, i₁, Fin.ext_iff]
      · exact Ne.symm h1
    exact ⟨(fun i => I.soloOps c I.initCfg (D.start (other i)) ++ [.inv r D.oread], other,
      I.invoke r (I.locInit r) D.oread),
      fun i => Good.init hcr hof hr (hstart _) (hother i)⟩
  have hstep : ∀ s, GoodAll s → ∃ s', GoodAll s' ∧ ∀ i, ∃ β, s'.1 i = s.1 i ++ β ++ [.tau r] := by
    rintro ⟨E, cur, lr⟩ hs
    cases hact : I.act r lr with
    | ret x l =>
      exfalso
      obtain ⟨a, ha, hx⟩ := (hs i₀).ret_resp hlin hact
      obtain ⟨a', ha', hx'⟩ := (hs a).ret_resp hlin hact
      exact ha' (D.resp_inj (hx'.symm.trans hx))
    | access ℓ o k =>
      obtain ⟨a, b, hab, heq⟩ : ∃ a b : Fin N, a ≠ b ∧ can a ℓ = can b ℓ := by
        obtain ⟨hfin, hcard⟩ := hB ℓ
        by_contra hcon
        push Not at hcon
        have hinj : Function.Injective (fun x : Fin N => can x ℓ) :=
          fun x y hxy => by by_contra hne; exact hcon x y hne hxy
        have := Nat.card_le_card_of_injective _ hinj
        simp at this; omega
      let new : Fin N → Fin N := fun i => if i = a then b else a
      have hnew : ∀ i, new i ≠ i := by
        intro i; simp only [new]; split_ifs with h1
        · subst h1; exact Ne.symm hab
        · exact Ne.symm h1
      have hcannew : ∀ i, can (new i) ℓ = can a ℓ := by
        intro i; simp only [new]; split_ifs
        · exact heq.symm
        · rfl
      have hext := fun i => (hs i).extend hcr hof (hmove (cur i) (new i)) hlin can hcan (hnew i) hact
      choose C hC hgood using hext
      refine ⟨(fun i => E i ++ I.soloOps c (C i) (D.move (cur i) (new i)) ++ [.tau r], new,
        k ((B ℓ).δ (can a ℓ) o).2), fun i => ?_, fun i => ⟨_, rfl⟩⟩
      have := hgood i
      rw [hcannew i] at this
      exact this
  choose s₀ hs₀ using hinit
  choose nxt hnxt hext using hstep
  let seq : ℕ → {s // GoodAll s} :=
    fun n => Nat.rec ⟨s₀, hs₀⟩ (fun _ t => ⟨nxt t.1 t.2, hnxt t.1 t.2⟩) n
  let F : ℕ → List (Label P A) := fun n => (seq n).1.1 i₀
  have hF : ∀ n, ∃ β, F (n + 1) = F n ++ β ++ [.tau r] := fun n => hext (seq n).1 (seq n).2 i₀
  have hFlen : ∀ n, n ≤ (F n).length := by
    intro n; induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => obtain ⟨β, hβ⟩ := hF n; rw [hβ]; simp; omega
  have hFgood : ∀ n, Good D I c r (F n) i₀ ((seq n).1.2.1 i₀) (seq n).1.2.2 :=
    fun n => (seq n).2 i₀
  obtain ⟨e, hlbl, hcfg⟩ := I.exists_infExec_of_chain F
    (fun n => by obtain ⟨β, hβ⟩ := hF n; rw [hβ, append_assoc]; exact prefix_append _ _) hFlen
    (fun n => by obtain ⟨C, hC, -⟩ := (hFgood n).run; exact ⟨C, hC⟩)
  have hmono : ∀ n m, n ≤ m → F n <+: F m := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact prefix_refl _
    | succ m _ ih => obtain ⟨β, hβ⟩ := hF m; rw [hβ, append_assoc]; exact ih.trans (prefix_append _ _)
  -- the reader is pending forever
  have hpend : ∀ m ≥ (F 0).length, (e.cfg m).pend r ≠ none := by
    intro m hm
    have hrun := hcfg m m (hFlen m)
    have hpre1 : F 0 <+: (F m).take m := by
      have h0 := hmono 0 m (Nat.zero_le _)
      rw [prefix_iff_eq_take] at h0 ⊢
      rw [take_take, Nat.min_eq_left hm]; exact h0
    have hpre2 : (F m).take m <+: F m := take_prefix _ _
    have h1 := opsOf_length_le_of_prefix hpre1 r
    have h2 := opsOf_length_le_of_prefix hpre2 r
    have h3 := respsOf_length_le_of_prefix hpre2 r
    rw [(hFgood 0).opsr] at h1
    rw [(hFgood m).opsr] at h2
    rw [(hFgood m).respsr] at h3
    rcases I.run_counts hrun r with ⟨-, h4⟩ | ⟨h4, -⟩
    · simp only [length_singleton, length_nil] at h1 h2 h3; omega
    · exact h4
  obtain ⟨N₀, hN₀⟩ := hwf e r (F 0).length hpend
  obtain ⟨β, hβ⟩ := hF N₀
  have hlen' := hFlen (N₀ + 1)
  apply hN₀ ((F (N₀ + 1)).length - 1) (by omega)
  rw [hlbl (N₀ + 1) _ (by omega)]
  simp only [hβ]
  simp

end Main

end Cslib.SharedMemory
