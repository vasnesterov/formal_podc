import Papers.PODC2023.PPDoubleExpThresholds.ProgramToMachineDefs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# From population programs to population machines: invariants and the abstraction relation

* Generic facts on population machines: inversion of `Machine.Exec`, preservation of pointer
  domains and of the number of units, finiteness of the set of reachable configurations.
* The abstraction relation `Abs m s` between configurations `m` of the machine of
  `ProgramToMachineDefs` and configurations `s` of the program: the program configuration `s` is
  the one "currently simulated" by `m` (`Loc` lists the possible positions of `m`), and its
  sub-relation `CAbs` for machine configurations at the start of a simulated program instruction.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.PPDoubleExpThresholds.ProgramToMachine

open Finset Cslib.TransitionSystem

/-! ### Generic facts about population machines -/

section Generic

variable {Q F : Type} [Fintype Q] [Fintype F] [DecidableEq Q] [DecidableEq F] {A : Machine Q F}
  {m m' : Machine.Cfg Q F} {a : ℕ}

theorem exec_move_inv {x y : Q} (hIP : m.ptr A.IP = .nat a) (hI : A.instr a = some (.move x y))
    (h : A.Exec m m') : ∃ u w, m.ptr (A.V (some x)) = .reg u ∧ m.ptr (A.V (some y)) = .reg w ∧
      0 < m.reg u ∧ m' = ⟨Function.update (Function.update m.reg u (m.reg u - 1)) w
        (Function.update m.reg u (m.reg u - 1) w + 1), Function.update m.ptr A.IP (.nat (a + 1))⟩ := by
  cases h with
  | move hi hI' hu hw hpos =>
    rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'; exact ⟨_, _, hu, hw, hpos, rfl⟩
  | detect hi hI' => rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'
  | assign hi hI' => rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'
  | jump hi hI' => rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'

theorem exec_detect_inv {x : Q} (hIP : m.ptr A.IP = .nat a) (hI : A.instr a = some (.detect x))
    (h : A.Exec m m') : ∃ u b, m.ptr (A.V (some x)) = .reg u ∧
      (b = false ∨ b = decide (0 < m.reg u)) ∧
      m' = ⟨m.reg, Function.update (Function.update m.ptr A.CF (.bool b)) A.IP (.nat (a + 1))⟩ := by
  cases h with
  | move hi hI' => rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'
  | detect hi hI' hu b hb =>
    rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'; exact ⟨_, b, hu, hb, rfl⟩
  | assign hi hI' => rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'
  | jump hi hI' => rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'

theorem exec_assign_inv {X Y : F} {f : Val Q → Val Q} (hIP : m.ptr A.IP = .nat a)
    (hI : A.instr a = some (.assign X Y f)) (hX : X ≠ A.IP) (h : A.Exec m m') :
    m' = ⟨m.reg, Function.update (Function.update m.ptr X (f (m.ptr Y))) A.IP (.nat (a + 1))⟩ := by
  cases h with
  | move hi hI' => rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'
  | detect hi hI' => rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'
  | assign hi hI' => rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'; rfl
  | jump hi hI' => rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'; exact absurd rfl hX

theorem exec_jump_inv {Y : F} {f : Val Q → Val Q} (hIP : m.ptr A.IP = .nat a)
    (hI : A.instr a = some (.assign A.IP Y f)) (h : A.Exec m m') :
    m' = ⟨m.reg, Function.update m.ptr A.IP (f (m.ptr Y))⟩ := by
  cases h with
  | move hi hI' => rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'
  | detect hi hI' => rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'
  | assign hi hI' hX => rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'; exact absurd rfl hX
  | jump hi hI' => rw [hIP] at hi; cases hi; rw [hI] at hI'; cases hI'; rfl

theorem instr_valid {i : ℕ} {I : MInstr Q F} (h : A.instr i = some I) :
    1 ≤ i ∧ i ≤ A.instrs.length ∧ I ∈ A.instrs := by
  unfold Machine.instr at h
  split_ifs at h with h0
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 h
  exact ⟨by omega, by omega, List.mem_of_getElem? h⟩

/-- The last instruction is a jump: then executing an instruction keeps all pointers in their
domains. -/
def LastJump (A : Machine Q F) : Prop :=
  ∃ Y f, A.instr A.instrs.length = some (.assign A.IP Y f)

theorem next_mem_dom (hL : LastJump A) {i : ℕ} {I : MInstr Q F} (h : A.instr i = some I)
    (hI : ∀ Y f, I ≠ .assign A.IP Y f) : Val.nat (i + 1) ∈ A.dom A.IP := by
  obtain ⟨h1, h2, -⟩ := instr_valid h
  have hne : i ≠ A.instrs.length := by
    rintro rfl; obtain ⟨Y, f, hY⟩ := hL; rw [hY] at h; cases h; exact hI Y f rfl
  rw [A.dom_IP]; simp only [Finset.mem_map, Finset.mem_Icc, Function.Embedding.coeFn_mk]
  exact ⟨i + 1, ⟨by omega, by omega⟩, rfl⟩

theorem exec_dom (hL : LastJump A) (hd : ∀ X, m.ptr X ∈ A.dom X) (h : A.Exec m m') :
    ∀ X, m'.ptr X ∈ A.dom X := by
  intro Z
  cases h with
  | move hi hI =>
    simp only [Function.update_apply]; split_ifs with h1
    · subst h1; exact next_mem_dom hL hI (by simp)
    · exact hd Z
  | detect hi hI hu b hb =>
    simp only [Function.update_apply]; split_ifs with h1 h2
    · subst h1; exact next_mem_dom hL hI (by simp)
    · subst h2; rw [A.dom_CF]; cases b <;> simp
    · exact hd Z
  | @assign i X Y f hi hI hX =>
    simp only [Function.update_apply]; split_ifs with h1 h2
    · subst h1; exact next_mem_dom hL hI (fun Y' f' h => hX (MInstr.assign.inj h).1)
    · subst h2; exact A.assign_mem _ _ _ (instr_valid hI).2.2 _ (hd Y)
    · exact hd Z
  | @jump i Y f hi hI =>
    simp only [Function.update_apply]; split_ifs with h1
    · subst h1; exact A.assign_mem _ _ _ (instr_valid hI).2.2 _ (hd Y)
    · exact hd Z

theorem exec_total (h : A.Exec m m') : Machine.total m' = Machine.total m := by
  cases h with
  | @move i x y u w hi hI hu hw hpos =>
    unfold Machine.total
    simp only
    by_cases huw : u = w
    · subst huw
      rw [Function.update_idem, Function.update_self, Nat.sub_add_cancel hpos,
        Function.update_eq_self]
    · have hu' : u ∈ Finset.univ \ {w} := by simp [huw]
      rw [Finset.sum_update_of_mem (Finset.mem_univ _), Finset.sum_update_of_mem hu',
        Function.update_of_ne (Ne.symm huw)]
      have h1 := Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ w) m.reg
      have h2 := Finset.sum_eq_add_sum_sdiff_singleton_of_mem hu' m.reg
      omega
  | _ => rfl

theorem reach_inv (hL : LastJump A) (hd : ∀ X, m.ptr X ∈ A.dom X) (h : Reach A.Step m m') :
    (∀ X, m'.ptr X ∈ A.dom X) ∧ Machine.total m' = Machine.total m := by
  induction h with
  | refl => exact ⟨hd, rfl⟩
  | tail _ h ih =>
    rcases h with h | ⟨rfl, -⟩
    · exact ⟨exec_dom hL ih.1 h, (exec_total h).trans ih.2⟩
    · exact ih

theorem finite_reach_machine (hL : LastJump A) (hd : ∀ X, m.ptr X ∈ A.dom X) :
    {m' | Reach A.Step m m'}.Finite := by
  have hreg : {r : Q → ℕ | ∀ q, r q ≤ Machine.total m}.Finite := by
    have := Set.Finite.pi (t := fun _ : Q => Set.Iic (Machine.total m))
      (fun _ => Set.finite_Iic _)
    simpa [Set.pi, Set.mem_Iic] using this
  have hptr : {p : F → Val Q | ∀ X, p X ∈ A.dom X}.Finite := by
    have := Set.Finite.pi (t := fun X : F => (A.dom X : Set (Val Q))) (fun X => (A.dom X).finite_toSet)
    simpa [Set.pi] using this
  refine ((hreg.prod hptr).image fun x => (⟨x.1, x.2⟩ : Machine.Cfg Q F)).subset ?_
  intro m' hm'
  obtain ⟨hd', ht⟩ := reach_inv hL hd hm'
  refine ⟨(m'.reg, m'.ptr), ⟨fun q => ?_, hd'⟩, rfl⟩
  rw [← ht]
  exact Finset.single_le_sum (f := m'.reg) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)

end Generic

/-! ### The machine of Appendix B.2: basic facts -/

variable {R P : Type} [Fintype R] [DecidableEq R] [DecidableEq P] [Nonempty R]
variable {prog : Program R P}

/-- Machine configurations. -/
abbrev MCfg (prog : Program R P) := Machine.Cfg R (PtrT prog)

section
variable (hwf : prog.WellFormed)

@[simp] theorem machine_IP : (machine prog hwf).IP = .IP := rfl
@[simp] theorem machine_CF : (machine prog hwf).CF = .CF := rfl
@[simp] theorem machine_OF : (machine prog hwf).OF = .OF := rfl
@[simp] theorem machine_V (x : Option R) : (machine prog hwf).V x = .V x := rfl
@[simp] theorem machine_dom : (machine prog hwf).dom = dom prog := rfl
@[simp] theorem machine_instr (i : ℕ) : (machine prog hwf).instr i = ins prog i := rfl
@[simp] theorem machine_instrs : (machine prog hwf).instrs = instrs prog := rfl

end

variable (prog) in
theorem length_instrs : (instrs prog).length = hb prog + 4 * (pairs (R := R)).length := by
  simp only [instrs, helper, hb, List.length_append, List.length_cons, List.length_nil,
    length_flatMap_block, List.length_map, List.length_range]
  omega

theorem lastJump (hwf : prog.WellFormed) : LastJump (machine prog hwf) := by
  refine ⟨.IP, cst (.nat 1), ?_⟩
  simp only [machine_instr, machine_instrs, machine_IP, length_instrs]
  rw [ins_hb prog le_rfl, helperInstr, ite_eq_right (lt_irrefl _)]

@[simp] theorem retP_ne_IP (q : P) : retP prog q ≠ .IP := by unfold retP; split_ifs <;> simp
@[simp] theorem retP_ne_CF (q : P) : retP prog q ≠ .CF := by unfold retP; split_ifs <;> simp
@[simp] theorem retP_ne_V (q : P) (x : Option R) : retP prog q ≠ .V x := by
  unfold retP; split_ifs <;> simp
@[simp] theorem IP_ne_retP (q : P) : (.IP : PtrT prog) ≠ retP prog q := (retP_ne_IP q).symm
@[simp] theorem CF_ne_retP (q : P) : (.CF : PtrT prog) ≠ retP prog q := (retP_ne_CF q).symm
@[simp] theorem V_ne_retP (q : P) (x : Option R) : (.V x : PtrT prog) ≠ retP prog q :=
  (retP_ne_V q x).symm

omit [Nonempty R] in
theorem retP_inj {q q' : P} (hq : q ∈ used prog) (hq' : q' ∈ used prog) :
    retP prog q = retP prog q' ↔ q = q' := by
  rw [retP_of_mem prog hq, retP_of_mem prog hq']; simp

/-- The register map as a function (`V_x` points to `vm m x`). -/
def vm (m : MCfg prog) (x : R) : R :=
  match m.ptr (.V (some x)) with
  | .reg q => q
  | _ => x

/-- Program registers seen through a register map `ν`. -/
def view (m : MCfg prog) (ν : R → R) : R → ℕ := fun x => m.reg (ν x)

/-- All pointers are in their domains. -/
def DomOK (m : MCfg prog) : Prop := ∀ X, m.ptr X ∈ dom prog X

theorem ptr_V_eq {m : MCfg prog} (hd : DomOK m) (x : R) : m.ptr (.V (some x)) = .reg (vm m x) := by
  have := hd (.V (some x))
  simp only [dom, mem_image] at this
  obtain ⟨q, -, hq⟩ := this
  simp [vm, ← hq]

theorem vm_mem_cl {m : MCfg prog} (hd : DomOK m) (x : R) : vm m x ∈ cl prog x := by
  have := hd (.V (some x))
  rw [ptr_V_eq hd] at this
  simpa [dom] using this

theorem vm_congr {m m' : MCfg prog} (h : ∀ x, m'.ptr (.V (some x)) = m.ptr (.V (some x))) :
    vm m' = vm m := by
  funext x; simp only [vm, h]

theorem total_view {m : MCfg prog} {ν : R → R} (hν : Function.Injective ν) :
    Program.total (view m ν) = Machine.total m := by
  unfold Program.total Machine.total view
  exact Equiv.sum_comp (Equiv.ofBijective ν (Finite.injective_iff_bijective.1 hν)) m.reg

theorem bool_of_dom {m : MCfg prog} (hd : DomOK m) : ∃ b, m.ptr .CF = .bool b := by
  have := hd .CF; simp only [dom, mem_insert, mem_singleton] at this
  rcases this with h | h <;> exact ⟨_, h⟩

theorem bool_of_dom_OF {m : MCfg prog} (hd : DomOK m) : ∃ b, m.ptr .OF = .bool b := by
  have := hd .OF; simp only [dom, mem_insert, mem_singleton] at this
  rcases this with h | h <;> exact ⟨_, h⟩

/-! ### Call stacks -/

variable (prog) in
/-- Well-formed call stacks: the bottom frame is `Main` and every other frame was called by the
frame below it. -/
inductive GoodStk : List (P × ℕ) → Prop
  | base (pc : ℕ) : GoodStk [(prog.main, pc)]
  | cons {q pc p pc' σ tT tF} : prog.instr p pc' = some (.call q tT tF) → GoodStk ((p, pc') :: σ) →
      GoodStk ((q, pc) :: (p, pc') :: σ)

theorem GoodStk.top {p pc pc' σ} (h : GoodStk prog ((p, pc) :: σ)) : GoodStk prog ((p, pc') :: σ) := by
  cases h with
  | base => exact .base _
  | cons hc h => exact .cons hc h

theorem GoodStk.mem_used (hwf : prog.WellFormed) {σ} (h : GoodStk prog σ) :
    ∀ f ∈ σ, f.1 ∈ used prog := by
  induction h with
  | base pc => simp [main_mem_used]
  | @cons q pc p pc' σ tT tF hc h ih =>
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact mem_used_of_call hwf (ih (p, pc') (by simp)) (mem_code_of_getElem? hc)
    · exact ih f hf

theorem GoodStk.rank_le (hwf : prog.WellFormed) {rank : P → ℕ}
    (hrank : ∀ p ∈ prog.procs, ∀ q tT tF, Instr.call q tT tF ∈ prog.code p → rank q < rank p)
    {p pc σ} (h : GoodStk prog ((p, pc) :: σ)) : ∀ f ∈ (p, pc) :: σ, rank p ≤ rank f.1 := by
  generalize hσ : (p, pc) :: σ = τ at h
  induction h generalizing p pc σ with
  | base pc =>
    simp only [List.cons.injEq, Prod.mk.injEq, List.nil_eq] at hσ
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hσ
    simp
  | @cons q pc₀ p' pc' σ' tT tF hc h ih =>
    simp only [List.cons.injEq, Prod.mk.injEq] at hσ
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hσ
    have ih' := ih rfl
    have hp' : p' ∈ prog.procs := used_subset hwf (h.mem_used hwf (p', pc') (by simp))
    have hlt := hrank p' hp' p tT tF (mem_code_of_getElem? hc)
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact le_rfl
    · have := ih' f hf; omega

theorem GoodStk.callee_notMem (hwf : prog.WellFormed) {p pc σ q tT tF}
    (h : GoodStk prog ((p, pc) :: σ)) (hc : prog.instr p pc = some (.call q tT tF)) :
    ∀ f ∈ (p, pc) :: σ, f.1 ≠ q := by
  obtain ⟨rank, hrank⟩ := hwf.acyclic
  intro f hf hfq
  have h1 := h.rank_le hwf hrank f hf
  have hp : p ∈ prog.procs := used_subset hwf (h.mem_used hwf (p, pc) (by simp))
  have h2 := hrank p hp q tT tF (mem_code_of_getElem? hc)
  rw [hfq] at h1; omega

/-- The return-address pointers encode the call stack. -/
def RetOK (m : MCfg prog) : List (P × ℕ) → Prop
  | [] => True
  | [(p, _)] => m.ptr (retP prog p) = .nat 3
  | (q, _) :: (p, pc') :: σ => m.ptr (retP prog q) = .nat (addr prog p pc' + 2) ∧ RetOK m ((p, pc') :: σ)

theorem RetOK.top {m : MCfg prog} {p pc pc' σ} (h : RetOK m ((p, pc) :: σ)) :
    RetOK m ((p, pc') :: σ) := by
  cases σ with
  | nil => exact h
  | cons f σ => obtain ⟨_, _⟩ := f; exact h

theorem RetOK.congr {m m' : MCfg prog} {σ : List (P × ℕ)}
    (h : ∀ f ∈ σ, m'.ptr (retP prog f.1) = m.ptr (retP prog f.1)) (hr : RetOK m σ) : RetOK m' σ := by
  induction σ with
  | nil => trivial
  | cons f σ ih =>
    obtain ⟨q, pc⟩ := f
    cases σ with
    | nil => simp only [RetOK] at hr ⊢; rw [h (q, pc) (by simp)]; exact hr
    | cons g σ =>
      obtain ⟨p, pc'⟩ := g
      simp only [RetOK] at hr ⊢
      exact ⟨by rw [h (q, pc) (by simp)]; exact hr.1,
        ih (fun f hf => h f (List.mem_cons_of_mem _ hf)) hr.2⟩

/-- `RetOK` is preserved if no return-address pointer changes. -/
theorem RetOK.of_ret (hwf : prog.WellFormed) {m m' : MCfg prog} {σ : List (P × ℕ)}
    (hg : GoodStk prog σ) (h : ∀ u, m'.ptr (.ret u) = m.ptr (.ret u)) (hr : RetOK m σ) :
    RetOK m' σ :=
  hr.congr fun f hf => by rw [retP_of_mem prog (hg.mem_used hwf f hf)]; exact h _

/-! ### The abstraction relation -/

/-- The register of the `j`-th loop of the helper that units are moved from. -/
noncomputable def hsrc (j : ℕ) : R := ((pairs (R := R)).getD j (x0, x0)).1

/-- The register of the `j`-th loop of the helper that units are moved to. -/
noncomputable def hdst (j : ℕ) : R := ((pairs (R := R)).getD j (x0, x0)).2

/-- Invariant inside the helper at offset `t`: the move of a loop is only reached after `detect`
returned `true`. -/
def HInv (m : MCfg prog) (t : ℕ) : Prop :=
  t < 4 * (pairs (R := R)).length →
    (t % 4 = 1 → m.ptr .CF = .bool true → 0 < m.reg (vm m (hsrc (t / 4)))) ∧
    (t % 4 = 2 → 0 < m.reg (vm m (hsrc (t / 4))))

/-- Machine configurations at the start of a simulated program instruction (`clean`), or after
`Main` returned (`final`). -/
inductive CLoc (m : MCfg prog) : Cfg R P → Prop
  | clean {C OF p pc σ} : m.ptr .IP = .nat (addr prog p pc) → RetOK m ((p, pc) :: σ) →
      C = view m (vm m) → Function.Injective (vm m) → CLoc m ⟨C, OF, (p, pc) :: σ⟩
  | final {C OF pc b} : m.ptr .IP = .nat 3 → prog.instr prog.main pc = some (.ret b) →
      CLoc m ⟨C, OF, [(prog.main, pc)]⟩

/-- All positions of the machine, with the program configuration they simulate. -/
inductive Loc (m : MCfg prog) : Cfg R P → Prop
  | cl {s} : CLoc m s → Loc m s
  /-- Before `ret_Main := 3`. -/
  | pre1 {C OF} : m.ptr .IP = .nat 1 → C = view m (vm m) → Function.Injective (vm m) →
      Loc m ⟨C, OF, [(prog.main, 0)]⟩
  /-- Before `IP := start(Main)`. -/
  | pre2 {C OF} : m.ptr .IP = .nat 2 → m.ptr (retP prog prog.main) = .nat 3 →
      C = view m (vm m) → Function.Injective (vm m) → Loc m ⟨C, OF, [(prog.main, 0)]⟩
  /-- After `V_□ := V_x` of `swap x, y`. -/
  | swap1 {C OF p pc σ x y} : prog.instr p pc = some (.swap x y) →
      m.ptr .IP = .nat (addr prog p pc + 1) → m.ptr (.V none) = m.ptr (.V (some x)) →
      RetOK m ((p, pc) :: σ) → C = view m (vm m) → Function.Injective (vm m) →
      Loc m ⟨C, OF, (p, pc) :: σ⟩
  /-- After `V_x := V_y` of `swap x, y`. -/
  | swap2 {C OF p pc σ x y u} : prog.instr p pc = some (.swap x y) →
      m.ptr .IP = .nat (addr prog p pc + 2) → m.ptr (.V none) = .reg u → u ∈ cl prog x →
      vm m x = vm m y → RetOK m ((p, pc) :: σ) → C = view m (Function.update (vm m) x u) →
      Function.Injective (Function.update (vm m) x u) → Loc m ⟨C, OF, (p, pc) :: σ⟩
  /-- After `detect x > 0`. -/
  | det {C OF p pc σ x tT tF b} : prog.instr p pc = some (.detect x tT tF) →
      m.ptr .IP = .nat (addr prog p pc + 1) → m.ptr .CF = .bool b → (b = true → 0 < C x) →
      RetOK m ((p, pc) :: σ) → C = view m (vm m) → Function.Injective (vm m) →
      Loc m ⟨C, OF, (p, pc) :: σ⟩
  /-- After `ret_q := a + 2` of `call q`. -/
  | call1 {C OF p pc σ q tT tF} : prog.instr p pc = some (.call q tT tF) →
      m.ptr .IP = .nat (addr prog p pc + 1) → m.ptr (retP prog q) = .nat (addr prog p pc + 2) →
      RetOK m ((p, pc) :: σ) → C = view m (vm m) → Function.Injective (vm m) →
      Loc m ⟨C, OF, (p, pc) :: σ⟩
  /-- Back from a call, before the conditional jump on the returned value. -/
  | call2 {C OF p pc σ q tT tF b} : prog.instr p pc = some (.call q tT tF) →
      m.ptr .IP = .nat (addr prog p pc + 2) → m.ptr .CF = .bool b →
      RetOK m ((p, cond b tT tF) :: σ) → C = view m (vm m) → Function.Injective (vm m) →
      Loc m ⟨C, OF, (p, cond b tT tF) :: σ⟩
  /-- After `CF := b` of `return b`. -/
  | ret1 {C OF q pc σ b} : prog.instr q pc = some (.ret b) →
      m.ptr .IP = .nat (addr prog q pc + 1) → m.ptr .CF = .bool b →
      RetOK m ((q, pc) :: σ) → C = view m (vm m) → Function.Injective (vm m) →
      Loc m ⟨C, OF, (q, pc) :: σ⟩
  /-- Inside the restart helper: the program is at a `restart`. -/
  | helper {s t} : m.ptr .IP = .nat (hb prog + t) → t ≤ 4 * (pairs (R := R)).length → HInv m t →
      prog.AtRestart s → Program.total s.C = Machine.total m → Function.Injective (vm m) → Loc m s

variable (prog) in
/-- The abstraction relation. -/
structure Abs (m : MCfg prog) (s : Cfg R P) : Prop where
  dom : DomOK m
  of : m.ptr .OF = .bool s.OF
  good : GoodStk prog s.stk
  loc : Loc m s

variable (prog) in
/-- The abstraction relation at clean positions. -/
structure CAbs (m : MCfg prog) (s : Cfg R P) : Prop where
  dom : DomOK m
  of : m.ptr .OF = .bool s.OF
  good : GoodStk prog s.stk
  loc : CLoc m s

theorem CAbs.abs {m : MCfg prog} {s} (h : CAbs prog m s) : Abs prog m s :=
  ⟨h.dom, h.of, h.good, .cl h.loc⟩

theorem Abs.out (hwf : prog.WellFormed) {m : MCfg prog} {s} (h : Abs prog m s) :
    (machine prog hwf).out m = some s.OF := by
  simp [Machine.out, h.of]

end Podc.PPDoubleExpThresholds.ProgramToMachine
