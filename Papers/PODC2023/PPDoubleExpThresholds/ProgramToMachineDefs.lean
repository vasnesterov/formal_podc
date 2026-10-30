import Papers.PODC2023.PPDoubleExpThresholds.Program
import Papers.PODC2023.PPDoubleExpThresholds.Machine
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# From population programs to population machines: the construction (Appendix B.2)

Given a well-formed population program `prog` over registers `R` (nonempty) and procedures `P`,
we build the population machine of Appendix B.2 of the paper:

* registers: `R` (the same registers);
* pointers (`Ptr`): `OF`, `CF`, `IP`, the register map `V_x` (`x ∈ R ∪ {□}`) and one
  return-address pointer for each *used* procedure (`Main` and every procedure called somewhere);
* instructions (`instrs`):
  1. `ret_Main := 3`, 2. `IP := start(Main)` (call `Main`), 3. `IP := 3` (loop forever if `Main`
     returns);
  then one *block* per used procedure: its instructions compiled one by one (`cinstr`), followed by
  a *guard* `IP := (address of the guard)` (a self-loop, reached when the program jumps beyond the
  end of the procedure, where the program hangs); then the helper code for `restart` (`helper`,
  Figure 7 of the paper): move all units to a fixed register `x₀`, then distribute them, and jump
  to instruction 1.

Compilation of the flat program instructions (address `a` of the instruction):

* `x ↦ y` ⟶ `x ↦ y`;
* `swap x, y` ⟶ `V_□ := V_x; V_x := V_y; V_y := V_□`;
* `OF := b` ⟶ `OF := b`;
* `detect x > 0` (targets `tT`, `tF`) ⟶ `detect x > 0; IP := (CF ? tT : tF)`;
* `call q` (targets `tT`, `tF`) ⟶ `ret_q := a + 2; IP := start(q); IP := (CF ? tT : tF)`;
* `return b` (in procedure `p`) ⟶ `CF := b; IP := ret_p`;
* `goto t` ⟶ `IP := t`;
* `restart` ⟶ `IP := start(helper)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.PPDoubleExpThresholds.ProgramToMachine

open Finset

/-! ### Pointers -/

/-- The pointers of the machine; `U` is the type of procedures with a return-address pointer. -/
inductive Ptr (R U : Type)
  | OF
  | CF
  | IP
  /-- The register map: `V (some x) = V_x`, `V none = V_□`. -/
  | V (x : Option R)
  /-- The return-address pointer of a procedure. -/
  | ret (u : U)
  deriving DecidableEq

namespace Ptr

variable {R U : Type}

/-- `Ptr R U ≃ (Unit ⊕ Unit ⊕ Unit) ⊕ Option R ⊕ U`. -/
def equiv : Ptr R U ≃ (Unit ⊕ Unit ⊕ Unit) ⊕ Option R ⊕ U where
  toFun
    | OF => .inl (.inl ())
    | CF => .inl (.inr (.inl ()))
    | IP => .inl (.inr (.inr ()))
    | V x => .inr (.inl x)
    | ret u => .inr (.inr u)
  invFun
    | .inl (.inl ()) => OF
    | .inl (.inr (.inl ())) => CF
    | .inl (.inr (.inr ())) => IP
    | .inr (.inl x) => V x
    | .inr (.inr u) => ret u
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; rcases x with (_ | _ | _) | _ | _ <;> rfl

instance [Fintype R] [Fintype U] : Fintype (Ptr R U) := Fintype.ofEquiv _ equiv.symm

theorem card [Fintype R] [Fintype U] : Fintype.card (Ptr R U) = Fintype.card R + Fintype.card U + 4 := by
  rw [Fintype.card_congr equiv]
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_option]
  omega

end Ptr

/-! ### The program-dependent data -/

variable {R P : Type} [Fintype R] [DecidableEq R] [DecidableEq P]

/-- The procedure called by an instruction. -/
def callee : Instr R P → Option P
  | .call q _ _ => some q
  | _ => none

/-- Number of machine instructions for one program instruction. -/
def mlen : Instr R P → ℕ
  | .move .. => 1
  | .swap .. => 3
  | .setOF _ => 1
  | .detect .. => 2
  | .call .. => 3
  | .ret _ => 2
  | .goto _ => 1
  | .restart => 1

omit [Fintype R] [DecidableEq R] [DecidableEq P] in
theorem mlen_le_three (i : Instr R P) : mlen i ≤ 3 := by cases i <;> simp [mlen]

omit [Fintype R] [DecidableEq R] [DecidableEq P] in
theorem mlen_pos (i : Instr R P) : 0 < mlen i := by cases i <;> simp [mlen]

/-- Conditional jump target on `CF`. -/
def cj (a b : ℕ) : Val R → Val R := fun v => if v = .bool true then .nat a else .nat b

/-- A constant function. -/
def cst (v : Val R) : Val R → Val R := fun _ => v

variable (prog : Program R P)

/-- The used procedures: `Main` and every procedure called by some procedure of the program. -/
def used : Finset P :=
  insert prog.main (prog.procs.biUnion fun p => ((prog.code p).filterMap callee).toFinset)

/-- Procedures with a return-address pointer. -/
abbrev UP := {p // p ∈ used prog}

/-- The pointer type of the machine. -/
abbrev PtrT := Ptr R (UP prog)

/-- The return-address pointer of a procedure (`OF` for unused procedures, never needed). -/
def retP (q : P) : PtrT prog := if h : q ∈ used prog then .ret ⟨q, h⟩ else .OF

/-- Machine length of the instruction at index `i` of `p` (`0` outside the code). -/
def mlenAt (p : P) (i : ℕ) : ℕ := ((prog.code p)[i]?.map mlen).getD 0

/-- Offset of program instruction `pc` inside the block of `p`; for `pc ≥ |code p|` this is the
offset of the guard. -/
def off (p : P) (pc : ℕ) : ℕ := ∑ i ∈ range (min pc (prog.code p).length), mlenAt prog p i

/-- Length of the block of `p` (compiled code and guard). -/
def blen (p : P) : ℕ := off prog p (prog.code p).length + 1

/-- The used procedures, in some fixed order. -/
noncomputable def usedList : List P := (used prog).toList

/-- Start address of the block of `p`. -/
noncomputable def base (p : P) : ℕ := 4 + (((usedList prog).takeWhile (· ≠ p)).map (blen prog)).sum

/-- Address of program instruction `pc` of `p`. -/
noncomputable def addr (p : P) (pc : ℕ) : ℕ := base prog p + off prog p pc

/-- Start address of the restart helper. -/
noncomputable def hb : ℕ := 4 + ((usedList prog).map (blen prog)).sum

open Classical in
/-- The swap class of `x`: `x` and all registers reachable from `x` by swap edges. -/
noncomputable def cl (x : R) : Finset R :=
  univ.filter fun z => z = x ∨ Relation.TransGen prog.SwapEdge x z

/-- `V_y := V_□` maps values outside the domain of `V_y` to `y` (never happens at run time). -/
noncomputable def clampV (y : R) (v : Val R) : Val R :=
  if v ∈ (cl prog y).image Val.reg then v else .reg y

/-- Compilation of the program instruction at `(p, pc)`. -/
noncomputable def cinstr (p : P) (pc : ℕ) : Instr R P → List (MInstr R (PtrT prog))
  | .move x y => [.move x y]
  | .swap x y => [.assign (.V none) (.V (some x)) id, .assign (.V (some x)) (.V (some y)) id,
      .assign (.V (some y)) (.V none) (clampV prog y)]
  | .setOF b => [.assign .OF .OF (cst (.bool b))]
  | .detect x tT tF => [.detect x, .assign .IP .CF (cj (addr prog p tT) (addr prog p tF))]
  | .call q tT tF => [.assign (retP prog q) .IP (cst (.nat (addr prog p pc + 2))),
      .assign .IP .IP (cst (.nat (base prog q))), .assign .IP .CF (cj (addr prog p tT) (addr prog p tF))]
  | .ret b => [.assign .CF .CF (cst (.bool b)), .assign .IP (retP prog p) id]
  | .goto t => [.assign .IP .IP (cst (.nat (addr prog p t)))]
  | .restart => [.assign .IP .IP (cst (.nat (hb prog)))]

theorem length_cinstr (p : P) (pc : ℕ) (i : Instr R P) : (cinstr prog p pc i).length = mlen i := by
  cases i <;> rfl

/-- Compiled code at index `i` of `p` (empty outside the code). -/
noncomputable def cinstrAt (p : P) (i : ℕ) : List (MInstr R (PtrT prog)) :=
  match (prog.code p)[i]? with
  | some ins => cinstr prog p i ins
  | none => []

/-- The guard of `p`: a self-loop. -/
noncomputable def guard (p : P) : MInstr R (PtrT prog) :=
  .assign .IP .IP (cst (.nat (addr prog p (prog.code p).length)))

/-- The block of `p`: compiled code followed by the guard. -/
noncomputable def block (p : P) : List (MInstr R (PtrT prog)) :=
  (List.range (prog.code p).length).flatMap (cinstrAt prog p) ++ [guard prog p]

/-! ### The restart helper (Figure 7) -/

variable [Nonempty R]

/-- The register collecting all units. -/
noncomputable def x0 : R := Classical.arbitrary R

/-- The other registers. -/
noncomputable def rest : List R := (univ.erase (x0 (R := R))).toList

/-- The loops of the helper: first move everything from each `y ≠ x₀` to `x₀`, then from `x₀` to
each `z ≠ x₀`. -/
noncomputable def pairs : List (R × R) := (rest (R := R)).map (·, x0) ++ (rest (R := R)).map (x0, ·)

/-- Instruction `t` of the helper: loop `j = t / 4` is
`detect y > 0; IP := (CF ? a + 2 : a + 4); y ↦ z; IP := a` for `(y, z) = pairs[j]`; the last
instruction is `IP := 1`. -/
noncomputable def helperInstr (t : ℕ) : MInstr R (PtrT prog) :=
  if t < 4 * (pairs (R := R)).length then
    match t % 4 with
    | 0 => .detect ((pairs (R := R)).getD (t / 4) (x0, x0)).1
    | 1 => .assign .IP .CF (cj (hb prog + 4 * (t / 4) + 2) (hb prog + 4 * (t / 4) + 4))
    | 2 => .move ((pairs (R := R)).getD (t / 4) (x0, x0)).1 ((pairs (R := R)).getD (t / 4) (x0, x0)).2
    | _ => .assign .IP .IP (cst (.nat (hb prog + 4 * (t / 4))))
  else .assign .IP .IP (cst (.nat 1))

/-- The helper code. -/
noncomputable def helper : List (MInstr R (PtrT prog)) :=
  (List.range (4 * (pairs (R := R)).length + 1)).map (helperInstr prog)

/-- All instructions of the machine. -/
noncomputable def instrs : List (MInstr R (PtrT prog)) :=
  [.assign (retP prog prog.main) .IP (cst (.nat 3)), .assign .IP .IP (cst (.nat (base prog prog.main))),
    .assign .IP .IP (cst (.nat 3))] ++ (usedList prog).flatMap (block prog) ++ helper prog

/-- The instruction at address `i` (as `Machine.instr`). -/
noncomputable def ins (i : ℕ) : Option (MInstr R (PtrT prog)) :=
  if i = 0 then none else (instrs prog)[i - 1]?


/-! ### Layout lemmas -/

omit [Fintype R] [DecidableEq R] [DecidableEq P] [Nonempty R] in
theorem list_sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

omit [Fintype R] [DecidableEq R] [DecidableEq P] [Nonempty R] in
theorem sum_range_le_of_lt (f : ℕ → ℕ) {j n : ℕ} (h : j < n) :
    ∑ i ∈ range j, f i + f j ≤ ∑ i ∈ range n, f i := by
  rw [← sum_range_succ]
  exact Finset.sum_le_sum_of_subset (by intro x; simp; omega)

omit [Fintype R] [DecidableEq R] [DecidableEq P] [Nonempty R] in
theorem getElem?_flatMap_range {α : Type} (g : ℕ → List α) {n j k : ℕ} (hj : j < n)
    (hk : k < (g j).length) :
    ((List.range n).flatMap g)[∑ i ∈ range j, (g i).length + k]? = (g j)[k]? := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · rw [List.getElem?_append_left, ih h]
      rw [List.length_flatMap, list_sum_range (fun i => (g i).length)]
      have := sum_range_le_of_lt (fun i => (g i).length) h
      omega
    · rw [List.getElem?_append_right (by
        rw [List.length_flatMap, list_sum_range (fun i => (g i).length)]; omega)]
      simp [List.length_flatMap, list_sum_range (fun i => (g i).length)]

omit [Nonempty R] in
theorem length_cinstrAt (p : P) (i : ℕ) : (cinstrAt prog p i).length = mlenAt prog p i := by
  unfold cinstrAt mlenAt
  cases (prog.code p)[i]? <;> simp [length_cinstr]

omit [Nonempty R] in
theorem off_of_le (p : P) {pc : ℕ} (h : (prog.code p).length ≤ pc) :
    off prog p pc = off prog p (prog.code p).length := by
  simp [off, Nat.min_eq_right h]

omit [Nonempty R] in
theorem off_zero (p : P) : off prog p 0 = 0 := by simp [off]

omit [Nonempty R] in
theorem length_body (p : P) :
    ((List.range (prog.code p).length).flatMap (cinstrAt prog p)).length =
      off prog p (prog.code p).length := by
  rw [List.length_flatMap, list_sum_range (fun i => (cinstrAt prog p i).length), off, min_self]
  simp only [length_cinstrAt]

omit [Nonempty R] in
theorem length_block (p : P) : (block prog p).length = blen prog p := by
  rw [block, List.length_append, length_body, blen]; rfl

omit [Nonempty R] in
theorem lt_length_of_getElem? {p : P} {pc : ℕ} {i : Instr R P} (hi : (prog.code p)[pc]? = some i) :
    pc < (prog.code p).length := by
  by_contra h; simp [List.getElem?_eq_none (not_lt.1 h)] at hi

omit [Nonempty R] in
theorem off_add_le {p : P} {pc : ℕ} {i : Instr R P} (hi : (prog.code p)[pc]? = some i) :
    off prog p pc + mlen i ≤ off prog p (prog.code p).length := by
  have hpc := lt_length_of_getElem? prog hi
  have h2 := sum_range_le_of_lt (mlenAt prog p) hpc
  simp only [off, Nat.min_eq_left hpc.le, min_self]
  simpa [mlenAt, hi] using h2

omit [Nonempty R] in
theorem getElem?_block (p : P) {pc : ℕ} {i : Instr R P} (hi : (prog.code p)[pc]? = some i)
    {k : ℕ} (hk : k < mlen i) : (block prog p)[off prog p pc + k]? = (cinstr prog p pc i)[k]? := by
  have hpc := lt_length_of_getElem? prog hi
  have hci : cinstrAt prog p pc = cinstr prog p pc i := by simp [cinstrAt, hi]
  have hoff : off prog p pc = ∑ i ∈ range pc, (cinstrAt prog p i).length := by
    simp only [off, Nat.min_eq_left hpc.le, length_cinstrAt]
  have hle := off_add_le prog hi
  rw [block, List.getElem?_append_left (by rw [length_body]; omega), hoff,
    getElem?_flatMap_range _ hpc, hci]
  rw [hci, length_cinstr]; exact hk

omit [Nonempty R] in
theorem getElem?_block_guard (p : P) :
    (block prog p)[off prog p (prog.code p).length]? = some (guard prog p) := by
  rw [block, List.getElem?_append_right (by rw [length_body]), length_body]
  simp

omit [Fintype R] [DecidableEq R] [DecidableEq P] [Nonempty R] in
theorem takeWhile_ne_of_append {α : Type} [DecidableEq α] {pre post : List α} {p : α}
    (h : p ∉ pre) : (pre ++ p :: post).takeWhile (· ≠ p) = pre := by
  induction pre with
  | nil => simp
  | cons a l ih =>
    simp only [List.mem_cons, not_or] at h
    rw [List.cons_append, List.takeWhile_cons, ite_eq_left (by simpa using Ne.symm h.1), ih h.2]

omit [Nonempty R] in
theorem mem_usedList {p : P} : p ∈ usedList prog ↔ p ∈ used prog := by simp [usedList]

theorem length_flatMap_block (l : List P) :
    (l.flatMap (block prog)).length = (l.map (blen prog)).sum := by
  rw [List.length_flatMap]; simp only [length_block]

/-- The block of a used procedure inside the instruction list. -/
theorem ins_base {p : P} (hp : p ∈ used prog) {j : ℕ} (hj : j < blen prog p) :
    ins prog (base prog p + j) = (block prog p)[j]? := by
  obtain ⟨pre, post, hl⟩ := List.append_of_mem ((mem_usedList prog).2 hp)
  have hnd : (usedList prog).Nodup := Finset.nodup_toList _
  rw [hl] at hnd
  have hpre : p ∉ pre := fun h => by
    rw [List.nodup_append] at hnd; exact hnd.2.2 p h p (by simp) rfl
  have hb : base prog p = 4 + (pre.flatMap (block prog)).length := by
    rw [base, hl, takeWhile_ne_of_append hpre, length_flatMap_block]
  rw [← length_block prog p] at hj
  have e : instrs prog = ([.assign (retP prog prog.main) .IP (cst (.nat 3)),
      .assign .IP .IP (cst (.nat (base prog prog.main))), .assign .IP .IP (cst (.nat 3))] ++
      pre.flatMap (block prog)) ++ (block prog p ++ (post.flatMap (block prog) ++ helper prog)) := by
    simp [instrs, hl, List.append_assoc]
  rw [ins, ite_eq_right (by rw [hb]; omega), hb, e, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_left (by simp; omega)]
  congr 1; simp; omega

theorem ins_addr {p : P} (hp : p ∈ used prog) {pc : ℕ} {i : Instr R P}
    (hi : (prog.code p)[pc]? = some i) {k : ℕ} (hk : k < mlen i) :
    ins prog (addr prog p pc + k) = (cinstr prog p pc i)[k]? := by
  have := off_add_le prog hi
  rw [addr, add_assoc, ins_base prog hp (by rw [blen]; omega), getElem?_block prog p hi hk]

theorem ins_guard {p : P} (hp : p ∈ used prog) {pc : ℕ} (hpc : (prog.code p).length ≤ pc) :
    ins prog (addr prog p pc) = some (guard prog p) := by
  have := ins_base prog hp (j := off prog p (prog.code p).length) (by rw [blen]; omega)
  rw [addr, off_of_le prog p hpc, this, getElem?_block_guard]

theorem ins_one : ins prog 1 = some (.assign (retP prog prog.main) .IP (cst (.nat 3))) := by
  simp [ins, instrs]

theorem ins_two : ins prog 2 = some (.assign .IP .IP (cst (.nat (base prog prog.main)))) := by
  simp [ins, instrs]

theorem ins_three : ins prog 3 = some (.assign .IP .IP (cst (.nat 3))) := by
  simp [ins, instrs]

theorem ins_hb {t : ℕ} (ht : t ≤ 4 * (pairs (R := R)).length) :
    ins prog (hb prog + t) = some (helperInstr prog t) := by
  have e : instrs prog = ([.assign (retP prog prog.main) .IP (cst (.nat 3)),
      .assign .IP .IP (cst (.nat (base prog prog.main))), .assign .IP .IP (cst (.nat 3))] ++
      (usedList prog).flatMap (block prog)) ++ helper prog := rfl
  have hl : (([.assign (retP prog prog.main) .IP (cst (.nat 3)),
      .assign .IP .IP (cst (.nat (base prog prog.main))), .assign .IP .IP (cst (.nat 3))] :
        List (MInstr R (PtrT prog))) ++
      (usedList prog).flatMap (block prog)).length = 3 + ((usedList prog).map (blen prog)).sum := by
    simp only [List.length_append, List.length_cons, List.length_nil, length_flatMap_block]
  rw [ins, ite_eq_right (by simp [hb]), e, hb, List.getElem?_append_right (by rw [hl]; omega), hl,
    show 4 + ((usedList prog).map (blen prog)).sum + t - 1 -
      (3 + ((usedList prog).map (blen prog)).sum) = t by omega]
  simp [helper, List.getElem?_map, List.getElem?_range (show t < 4 * (pairs (R := R)).length + 1 by omega)]

theorem le_length_of_ins {i : ℕ} {I} (h : ins prog i = some I) : 1 ≤ i ∧ i ≤ (instrs prog).length := by
  unfold ins at h
  split_ifs at h with h0
  have := (List.getElem?_eq_some_iff.1 h).1
  omega


/-! ### Domains -/

omit [Nonempty R] in
theorem retP_of_mem {q : P} (hq : q ∈ used prog) : retP prog q = .ret ⟨q, hq⟩ := by
  simp [retP, hq]

/-- Call sites `(p, pc)` of `q` in used procedures. -/
def sitesOf (q : P) : Finset (P × ℕ) := (used prog).biUnion fun p =>
  ((range (prog.code p).length).filter fun pc => (prog.code p)[pc]?.bind callee = some q).image (p, ·)

/-- Domain of the return-address pointer of `q`: the addresses following its call sites, and
instruction 3 (the return address of `Main`; for other procedures it only keeps the domain
nonempty). -/
noncomputable def retDom (q : P) : Finset (Val R) :=
  insert (.nat 3) ((sitesOf prog q).image fun pp => .nat (addr prog pp.1 pp.2 + 2))

/-- The pointer domains. -/
noncomputable def dom : PtrT prog → Finset (Val R)
  | .OF => {.bool false, .bool true}
  | .CF => {.bool false, .bool true}
  | .IP => (Icc 1 (instrs prog).length).map ⟨Val.nat, fun _ _ h => by cases h; rfl⟩
  | .V (some x) => (cl prog x).image .reg
  | .V none => univ.image .reg
  | .ret q => retDom prog q.1

/-- Valid instruction addresses. -/
def Valid (a : ℕ) : Prop := 1 ≤ a ∧ a ≤ (instrs prog).length

theorem mem_dom_IP {a : ℕ} : Val.nat a ∈ dom prog .IP ↔ Valid prog a := by
  simp only [dom, mem_map, mem_Icc, Function.Embedding.coeFn_mk, Val.nat.injEq, Valid]
  constructor
  · rintro ⟨b, hb, h⟩; obtain rfl : b = a := Val.nat.inj h; exact hb
  · intro h; exact ⟨a, h, rfl⟩

theorem valid_of_ins {a : ℕ} {I} (h : ins prog a = some I) : Valid prog a :=
  le_length_of_ins prog h

theorem valid_addr {p : P} (hp : p ∈ used prog) (t : ℕ) : Valid prog (addr prog p t) := by
  rcases h : (prog.code p)[t]? with _ | i
  · exact valid_of_ins prog (ins_guard prog hp (List.getElem?_eq_none_iff.1 h))
  · have := ins_addr prog hp h (k := 0) (mlen_pos i)
    rw [add_zero] at this
    cases i <;> exact valid_of_ins prog this

theorem valid_base {p : P} (hp : p ∈ used prog) : Valid prog (base prog p) := by
  have := valid_addr prog hp 0; rwa [addr, off_zero, add_zero] at this

theorem valid_hb {t : ℕ} (ht : t ≤ 4 * (pairs (R := R)).length) : Valid prog (hb prog + t) :=
  valid_of_ins prog (ins_hb prog ht)

theorem valid_three : Valid prog 3 := valid_of_ins prog (ins_three prog)

theorem valid_one : Valid prog 1 := valid_of_ins prog (ins_one prog)

theorem valid_call {p : P} (hp : p ∈ used prog) {pc : ℕ} {q : P} {tT tF : ℕ}
    (h : (prog.code p)[pc]? = some (.call q tT tF)) : Valid prog (addr prog p pc + 2) :=
  valid_of_ins prog (ins_addr prog hp h (k := 2) (by simp [mlen]))

theorem mem_retDom_valid {q : P} {v : Val R} (hv : v ∈ retDom prog q) :
    ∃ a, v = .nat a ∧ Valid prog a := by
  simp only [retDom, mem_insert, mem_image] at hv
  rcases hv with hv | ⟨pp, hs, rfl⟩
  · exact ⟨3, hv, valid_three prog⟩
  · simp only [sitesOf, mem_biUnion, mem_image, mem_filter, mem_range] at hs
    obtain ⟨p, hp', pc, ⟨-, hc⟩, rfl⟩ := hs
    rcases hi : (prog.code p)[pc]? with _ | i
    · simp [hi] at hc
    · rw [hi] at hc
      cases i <;> simp [callee] at hc
      subst hc
      exact ⟨_, rfl, valid_call prog hp' hi⟩

/-! ### Well-formedness facts -/

variable {prog}

omit [Fintype R] [Nonempty R] in
theorem used_subset (hwf : prog.WellFormed) : used prog ⊆ prog.procs := by
  intro p hp
  simp only [used, mem_insert, mem_biUnion, List.mem_toFinset, List.mem_filterMap] at hp
  rcases hp with rfl | ⟨p', hp', i, hi, hc⟩
  · exact hwf.main_mem
  · cases i <;> simp [callee] at hc
    subst hc; exact hwf.call_mem p' hp' _ _ _ hi

omit [Fintype R] [Nonempty R] in
theorem mem_used_of_call (hwf : prog.WellFormed) {p : P} (hp : p ∈ used prog) {q : P} {tT tF : ℕ}
    (h : Instr.call q tT tF ∈ prog.code p) : q ∈ used prog := by
  simp only [used, mem_insert, mem_biUnion, List.mem_toFinset, List.mem_filterMap]
  exact Or.inr ⟨p, used_subset hwf hp, _, h, rfl⟩

omit [Fintype R] [Nonempty R] in
theorem mem_code_of_getElem? {p : P} {pc : ℕ} {i : Instr R P} (h : (prog.code p)[pc]? = some i) :
    i ∈ prog.code p := List.mem_of_getElem? h

omit [Nonempty R] in
theorem cl_subset {x y : R} (h : prog.SwapEdge x y) : cl prog y ⊆ cl prog x := by
  intro z hz
  simp only [cl, mem_filter, mem_univ, true_and] at hz ⊢
  right
  rcases hz with rfl | hz
  · exact .single h
  · exact .head h hz

omit [Nonempty R] in
theorem self_mem_cl (x : R) : x ∈ cl prog x := by simp [cl]

theorem mem_rest {y : R} : y ∈ rest (R := R) ↔ y ≠ x0 := by simp [rest]

theorem pairs_ne' : ∀ yz ∈ pairs (R := R), yz.1 ≠ yz.2 := by
  intro yz h
  simp only [pairs, List.mem_append, List.mem_map] at h
  rcases h with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · exact mem_rest.1 hy
  · exact (mem_rest.1 hy).symm

theorem pairs_ne {j : ℕ} (hj : j < (pairs (R := R)).length) :
    ((pairs (R := R)).getD j (x0, x0)).1 ≠ ((pairs (R := R)).getD j (x0, x0)).2 := by
  rw [List.getD_eq_getElem _ _ hj]
  exact pairs_ne' _ (List.getElem_mem hj)

variable (prog) in
theorem mem_instrs {I : MInstr R (PtrT prog)} (h : I ∈ instrs prog) :
    I = .assign (retP prog prog.main) .IP (cst (.nat 3)) ∨
    I = .assign .IP .IP (cst (.nat (base prog prog.main))) ∨ I = .assign .IP .IP (cst (.nat 3)) ∨
    (∃ p ∈ used prog, ∃ pc ins, (prog.code p)[pc]? = some ins ∧ I ∈ cinstr prog p pc ins) ∨
    (∃ p ∈ used prog, I = guard prog p) ∨
    ∃ t < 4 * (pairs (R := R)).length + 1, I = helperInstr prog t := by
  simp only [instrs, List.mem_append, List.mem_cons, List.mem_flatMap, block, List.mem_range,
    helper, List.mem_map, List.not_mem_nil, or_false] at h
  rcases h with ((h | h | h) | ⟨p, hp, ⟨pc, -, hI⟩ | rfl⟩) | ⟨t, ht, rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · right; right; right; left
    refine ⟨p, (mem_usedList prog).1 hp, pc, ?_⟩
    unfold cinstrAt at hI
    split at hI
    · exact ⟨_, ‹_›, hI⟩
    · simp at hI
  · exact .inr (.inr (.inr (.inr (.inl ⟨p, (mem_usedList prog).1 hp, rfl⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨t, ht, rfl⟩))))


omit [Nonempty R] in
theorem main_mem_used : prog.main ∈ used prog := mem_insert_self _ _

theorem cj_mem {a b : ℕ} (ha : Valid prog a) (hb : Valid prog b) (v : Val R) :
    cj a b v ∈ dom prog .IP := by
  unfold cj; split_ifs
  · exact (mem_dom_IP prog).2 ha
  · exact (mem_dom_IP prog).2 hb

theorem move_ne_instrs (hwf : prog.WellFormed) :
    ∀ x y, MInstr.move x y ∈ instrs prog → x ≠ y := by
  intro x y h
  rcases mem_instrs prog h with h | h | h | ⟨p, hp, pc, ins, hi, hI⟩ | ⟨p, hp, h⟩ | ⟨t, ht, h⟩
  · simp at h
  · simp at h
  · simp at h
  · cases ins <;> simp [cinstr] at hI
    obtain ⟨rfl, rfl⟩ := hI
    exact hwf.move_ne p (used_subset hwf hp) _ _ (mem_code_of_getElem? hi)
  · simp [guard] at h
  · unfold helperInstr at h
    split_ifs at h with h1
    split at h <;> simp only [MInstr.move.injEq, reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact pairs_ne (by omega)

theorem assign_mem_instrs (hwf : prog.WellFormed) :
    ∀ X Y f, MInstr.assign X Y f ∈ instrs prog → ∀ v ∈ dom prog Y, f v ∈ dom prog X := by
  intro X Y f h v hv
  rcases mem_instrs prog h with h | h | h | ⟨p, hp, pc, ins, hi, hI⟩ | ⟨p, hp, h⟩ | ⟨t, ht, h⟩
  · simp only [MInstr.assign.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [retP_of_mem prog main_mem_used]
    simp [dom, retDom, cst]
  · simp only [MInstr.assign.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (mem_dom_IP prog).2 (valid_base prog main_mem_used)
  · simp only [MInstr.assign.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (mem_dom_IP prog).2 (valid_three prog)
  · have hmem := mem_code_of_getElem? hi
    cases ins with
    | move x y => simp [cinstr] at hI
    | swap x y =>
      simp only [cinstr, List.mem_cons, MInstr.assign.injEq, List.not_mem_nil, or_false] at hI
      rcases hI with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · simp only [dom, mem_image, mem_univ, true_and, id] at hv ⊢
        obtain ⟨q, -, rfl⟩ := hv; exact ⟨q, rfl⟩
      · simp only [dom, id] at hv ⊢
        exact image_subset_image (cl_subset ⟨p, used_subset hwf hp, .inl hmem⟩) hv
      · simp only [dom, clampV]
        split_ifs with h1
        · exact h1
        · exact mem_image_of_mem _ (self_mem_cl y)
    | setOF b =>
      simp only [cinstr, List.mem_cons, MInstr.assign.injEq, List.not_mem_nil, or_false] at hI
      obtain ⟨rfl, rfl, rfl⟩ := hI
      cases b <;> simp [dom, cst]
    | detect x tT tF =>
      simp only [cinstr, List.mem_cons, MInstr.assign.injEq, List.not_mem_nil, or_false,
        reduceCtorEq, false_or] at hI
      obtain ⟨rfl, rfl, rfl⟩ := hI
      exact cj_mem (valid_addr prog hp _) (valid_addr prog hp _) v
    | call q tT tF =>
      have hq := mem_used_of_call hwf hp hmem
      simp only [cinstr, List.mem_cons, MInstr.assign.injEq, List.not_mem_nil, or_false] at hI
      rcases hI with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · rw [retP_of_mem prog hq]
        simp only [dom, retDom, cst, mem_insert, mem_image]
        right
        refine ⟨(p, pc), ?_, rfl⟩
        simp only [sitesOf, mem_biUnion, mem_image, mem_filter, mem_range]
        exact ⟨p, hp, pc, ⟨lt_length_of_getElem? prog hi, by simp [hi, callee]⟩, rfl⟩
      · exact (mem_dom_IP prog).2 (valid_base prog hq)
      · exact cj_mem (valid_addr prog hp _) (valid_addr prog hp _) v
    | ret b =>
      simp only [cinstr, List.mem_cons, MInstr.assign.injEq, List.not_mem_nil, or_false] at hI
      rcases hI with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · cases b <;> simp [dom, cst]
      · rw [retP_of_mem prog hp] at hv
        obtain ⟨a, rfl, ha⟩ := mem_retDom_valid prog hv
        exact (mem_dom_IP prog).2 ha
    | goto t =>
      simp only [cinstr, List.mem_cons, MInstr.assign.injEq, List.not_mem_nil, or_false] at hI
      obtain ⟨rfl, rfl, rfl⟩ := hI
      exact (mem_dom_IP prog).2 (valid_addr prog hp _)
    | restart =>
      simp only [cinstr, List.mem_cons, MInstr.assign.injEq, List.not_mem_nil, or_false] at hI
      obtain ⟨rfl, rfl, rfl⟩ := hI
      exact (mem_dom_IP prog).2 (by simpa using valid_hb prog (t := 0) (Nat.zero_le _))
  · simp only [guard, MInstr.assign.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (mem_dom_IP prog).2 (valid_addr prog hp _)
  · unfold helperInstr at h
    split_ifs at h with h1
    · split at h <;> simp only [MInstr.assign.injEq, reduceCtorEq] at h
      · obtain ⟨rfl, rfl, rfl⟩ := h
        exact cj_mem (by simpa [add_assoc] using valid_hb prog (t := 4 * (t / 4) + 2) (by omega))
          (by simpa [add_assoc] using valid_hb prog (t := 4 * (t / 4) + 4) (by omega)) v
      · obtain ⟨rfl, rfl, rfl⟩ := h
        exact (mem_dom_IP prog).2 (valid_hb prog (by omega))
    · simp only [MInstr.assign.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (mem_dom_IP prog).2 (valid_one prog)

variable (prog) in
/-- **The population machine of Appendix B.2** simulating `prog`. -/
noncomputable def machine (hwf : prog.WellFormed) : Machine R (PtrT prog) where
  dom := dom prog
  instrs := instrs prog
  OF := .OF
  CF := .CF
  IP := .IP
  V := .V
  OF_ne_CF := by simp
  OF_ne_IP := by simp
  CF_ne_IP := by simp
  V_inj := fun _ _ h => Ptr.V.inj h
  V_ne_OF := by simp
  V_ne_CF := by simp
  V_ne_IP := by simp
  dom_OF := rfl
  dom_CF := rfl
  dom_IP := rfl
  dom_V := by
    rintro (_ | x) v hv <;> simp only [dom, mem_image] at hv <;> obtain ⟨q, -, rfl⟩ := hv <;>
      exact ⟨q, rfl⟩
  mem_dom_V := fun x => mem_image_of_mem _ (self_mem_cl x)
  dom_V_none := ⟨.reg x0, by simp [dom]⟩
  move_ne := move_ne_instrs hwf
  assign_mem := assign_mem_instrs hwf

end Podc.PPDoubleExpThresholds.ProgramToMachine
