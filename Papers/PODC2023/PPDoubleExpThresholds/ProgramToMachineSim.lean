import Papers.PODC2023.PPDoubleExpThresholds.ProgramToMachineStep

/-!
# From population programs to population machines: program steps are simulated

From every machine configuration related to a program configuration `s` one can reach a *clean*
machine configuration related to a configuration reachable from `s` (`to_clean`), and every
program step from a configuration related to a clean machine configuration can be simulated by a
machine path ending in a clean configuration (`clean_sim`). The `restart` helper is handled by
`helper_collect` and `helper_distribute`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.PPDoubleExpThresholds.ProgramToMachine

open Finset Cslib.TransitionSystem

variable {R P : Type} [Fintype R] [DecidableEq R] [DecidableEq P] [Nonempty R]
variable {prog : Program R P}

section Sim

variable (hwf : prog.WellFormed)

local notation "MM" => machine prog hwf

/-! ### Building machine steps -/

theorem step_assign {m : MCfg prog} {a : ℕ} {X Y : PtrT prog} {f : Val R → Val R}
    (hIP : m.ptr .IP = .nat a) (hI : ins prog a = some (.assign X Y f)) (hX : X ≠ .IP) :
    (MM).Step m ⟨m.reg, Function.update (Function.update m.ptr X (f (m.ptr Y))) .IP (.nat (a + 1))⟩ :=
  .inl (.assign (A := MM) hIP hI hX)

theorem step_jump {m : MCfg prog} {a : ℕ} {Y : PtrT prog} {f : Val R → Val R}
    (hIP : m.ptr .IP = .nat a) (hI : ins prog a = some (.assign .IP Y f)) :
    (MM).Step m ⟨m.reg, Function.update m.ptr .IP (f (m.ptr Y))⟩ :=
  .inl (.jump (A := MM) hIP hI)

theorem step_detect {m : MCfg prog} {a : ℕ} {x u : R} (hIP : m.ptr .IP = .nat a)
    (hI : ins prog a = some (.detect x)) (hu : m.ptr (.V (some x)) = .reg u) (b : Bool)
    (hb : b = false ∨ b = decide (0 < m.reg u)) :
    (MM).Step m ⟨m.reg, Function.update (Function.update m.ptr .CF (.bool b)) .IP (.nat (a + 1))⟩ :=
  .inl (.detect (A := MM) hIP hI hu b hb)

theorem step_move {m : MCfg prog} {a : ℕ} {x y u w : R} (hIP : m.ptr .IP = .nat a)
    (hI : ins prog a = some (.move x y)) (hu : m.ptr (.V (some x)) = .reg u)
    (hw : m.ptr (.V (some y)) = .reg w) (hpos : 0 < m.reg u) :
    (MM).Step m ⟨Function.update (Function.update m.reg u (m.reg u - 1)) w
        (Function.update m.reg u (m.reg u - 1) w + 1), Function.update m.ptr .IP (.nat (a + 1))⟩ :=
  .inl (.move (A := MM) hIP hI hu hw hpos)

theorem domOK_of_reach {m m' : MCfg prog} (hd : DomOK m) (h : Reach (MM).Step m m') : DomOK m' :=
  (reach_inv (lastJump hwf) hd h).1

theorem total_of_reach {m m' : MCfg prog} (hd : DomOK m) (h : Reach (MM).Step m m') :
    Machine.total m' = Machine.total m :=
  (reach_inv (lastJump hwf) hd h).2

/-! ### Reaching a clean position -/

theorem cont_call2 {m : MCfg prog} {C OF p pc σ q tT tF b} (hd : DomOK m)
    (hof : m.ptr .OF = .bool OF) (hg : GoodStk prog ((p, cond b tT tF) :: σ))
    (hi : prog.instr p pc = some (.call q tT tF)) (hIP : m.ptr .IP = .nat (addr prog p pc + 2))
    (hCF : m.ptr .CF = .bool b) (hr : RetOK m ((p, cond b tT tF) :: σ)) (hC : C = view m (vm m))
    (hinj : Function.Injective (vm m)) :
    ∃ m', Reach (MM).Step m m' ∧ CAbs prog m' ⟨C, OF, (p, cond b tT tF) :: σ⟩ := by
  have hp : p ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
  have hI := ins_addr prog hp hi (k := 2) (by simp [mlen])
  have hs := step_jump hwf hIP hI
  have hvm : ∀ {m' : MCfg prog}, (∀ x, m'.ptr (.V (some x)) = m.ptr (.V (some x))) →
      vm m' = vm m := vm_congr
  refine ⟨_, .single hs, domOK_of_reach hwf hd (.single hs), by simpa using hof, hg,
    .clean ?_ (hr.of_ret hwf hg (fun u => by simp)) ?_ ?_⟩
  · cases b <;> simp [cj, hCF]
  · rwa [hvm (fun x => by simp)]
  · rwa [hvm (fun x => by simp)]

theorem cont_ret1_cons {m : MCfg prog} {C OF q pc p pc' σ b tT tF} (hd : DomOK m)
    (hof : m.ptr .OF = .bool OF) (hg : GoodStk prog ((q, pc) :: (p, pc') :: σ))
    (hi : prog.instr q pc = some (.ret b)) (hc : prog.instr p pc' = some (.call q tT tF))
    (hIP : m.ptr .IP = .nat (addr prog q pc + 1))
    (hCF : m.ptr .CF = .bool b) (hr : RetOK m ((q, pc) :: (p, pc') :: σ)) (hC : C = view m (vm m))
    (hinj : Function.Injective (vm m)) :
    ∃ m', Reach (MM).Step m m' ∧ CAbs prog m' ⟨C, OF, (p, cond b tT tF) :: σ⟩ := by
  have hq : q ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
  have hI := ins_addr prog hq hi (k := 1) (by simp [mlen])
  have hs := step_jump hwf hIP hI
  have hg' : GoodStk prog ((p, pc') :: σ) := by cases hg with | cons _ h => exact h
  have hvm : ∀ {m' : MCfg prog}, (∀ x, m'.ptr (.V (some x)) = m.ptr (.V (some x))) →
      vm m' = vm m := vm_congr
  obtain ⟨m', h1, h2⟩ := cont_call2 hwf (domOK_of_reach hwf hd (.single hs)) (by simpa using hof)
    hg'.top hc (by simpa [RetOK] using hr.1) (b := b) (by simpa using hCF)
    ((hr.2.of_ret hwf hg' (fun u => by simp)).top) (C := C) (by rwa [hvm (fun x => by simp)])
    (by rwa [hvm (fun x => by simp)])
  exact ⟨m', .head hs h1, h2⟩

theorem cont_ret1_nil {m : MCfg prog} {C OF q pc b} (hd : DomOK m)
    (hof : m.ptr .OF = .bool OF) (hg : GoodStk prog [(q, pc)])
    (hi : prog.instr q pc = some (.ret b)) (hIP : m.ptr .IP = .nat (addr prog q pc + 1))
    (hr : RetOK m [(q, pc)]) :
    ∃ m', Reach (MM).Step m m' ∧ CAbs prog m' ⟨C, OF, [(q, pc)]⟩ := by
  have hq : q ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
  have hI := ins_addr prog hq hi (k := 1) (by simp [mlen])
  have hs := step_jump hwf hIP hI
  have hqm : q = prog.main := by cases hg; rfl
  subst hqm
  refine ⟨_, .single hs, domOK_of_reach hwf hd (.single hs), by simpa using hof, hg, .final ?_ hi⟩
  simpa [RetOK] using hr

theorem cont_det {m : MCfg prog} {C OF p pc σ x tT tF b} (hd : DomOK m)
    (hof : m.ptr .OF = .bool OF) (hg : GoodStk prog ((p, pc) :: σ))
    (hi : prog.instr p pc = some (.detect x tT tF)) (hIP : m.ptr .IP = .nat (addr prog p pc + 1))
    (hCF : m.ptr .CF = .bool b) (hr : RetOK m ((p, pc) :: σ)) (hC : C = view m (vm m))
    (hinj : Function.Injective (vm m)) :
    ∃ m', Reach (MM).Step m m' ∧ CAbs prog m' ⟨C, OF, (p, cond b tT tF) :: σ⟩ := by
  have hp : p ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
  have hI := ins_addr prog hp hi (k := 1) (by simp [mlen])
  have hs := step_jump hwf hIP hI
  have hvm : ∀ {m' : MCfg prog}, (∀ x, m'.ptr (.V (some x)) = m.ptr (.V (some x))) →
      vm m' = vm m := vm_congr
  refine ⟨_, .single hs, domOK_of_reach hwf hd (.single hs), by simpa using hof, hg.top,
    .clean ?_ (hr.of_ret hwf hg (fun u => by simp)).top ?_ ?_⟩
  · cases b <;> simp [cj, hCF]
  · rwa [hvm (fun x => by simp)]
  · rwa [hvm (fun x => by simp)]

theorem cont_call1 {m : MCfg prog} {C OF p pc σ q tT tF} (hd : DomOK m)
    (hof : m.ptr .OF = .bool OF) (hg : GoodStk prog ((p, pc) :: σ))
    (hi : prog.instr p pc = some (.call q tT tF)) (hIP : m.ptr .IP = .nat (addr prog p pc + 1))
    (hret : m.ptr (retP prog q) = .nat (addr prog p pc + 2)) (hr : RetOK m ((p, pc) :: σ))
    (hC : C = view m (vm m)) (hinj : Function.Injective (vm m)) :
    ∃ m', Reach (MM).Step m m' ∧ CAbs prog m' ⟨C, OF, (q, 0) :: (p, pc) :: σ⟩ := by
  have hp : p ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
  have hI := ins_addr prog hp hi (k := 1) (by simp [mlen])
  have hs := step_jump hwf hIP hI
  have hvm : ∀ {m' : MCfg prog}, (∀ x, m'.ptr (.V (some x)) = m.ptr (.V (some x))) →
      vm m' = vm m := vm_congr
  refine ⟨_, .single hs, domOK_of_reach hwf hd (.single hs), by simpa using hof, .cons hi hg,
    .clean ?_ ⟨by simpa using hret, hr.of_ret hwf hg (fun u => by simp)⟩ ?_ ?_⟩
  · simp [cst, addr_eq_base]
  · rwa [hvm (fun x => by simp)]
  · rwa [hvm (fun x => by simp)]

theorem cont_swap2 {m : MCfg prog} {C OF p pc σ x y u} (hd : DomOK m)
    (hof : m.ptr .OF = .bool OF) (hg : GoodStk prog ((p, pc) :: σ))
    (hi : prog.instr p pc = some (.swap x y)) (hIP : m.ptr .IP = .nat (addr prog p pc + 2))
    (hV : m.ptr (.V none) = .reg u) (hu : u ∈ cl prog x) (hxy : vm m x = vm m y)
    (hr : RetOK m ((p, pc) :: σ)) (hC : C = view m (Function.update (vm m) x u))
    (hinj : Function.Injective (Function.update (vm m) x u)) :
    ∃ m', Reach (MM).Step m m' ∧ CAbs prog m' ⟨swp C x y, OF, (p, pc + 1) :: σ⟩ := by
  have hp : p ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
  have hI := ins_addr prog hp hi (k := 2) (by simp [mlen])
  have hs := step_assign hwf hIP hI (by simp)
  have hedge : prog.SwapEdge x y := ⟨p, used_subset hwf hp, .inl (mem_code_of_getElem? hi)⟩
  have hcl : clampV prog y (.reg u) = .reg u := by
    rw [clampV, ite_eq_left]; rw [← cl_eq hedge]; exact mem_image_of_mem _ hu
  have hvm : vm ⟨m.reg, Function.update (Function.update m.ptr (.V (some y))
      (clampV prog y (m.ptr (.V none)))) .IP (.nat (addr prog p pc + 2 + 1))⟩ =
      Function.update (vm m) x u ∘ Equiv.swap x y := by
    funext r
    simp only [vm, Function.update_apply, hV, hcl, Function.comp_apply]
    by_cases hry : r = y
    · subst hry; simp [Equiv.swap_apply_right]
    · by_cases hrx : r = x
      · subst hrx; simp [Equiv.swap_apply_left, hry, Ne.symm hry, ptr_V_eq hd, hxy]
      · simp [hry, hrx, Equiv.swap_apply_of_ne_of_ne hrx hry, ptr_V_eq hd]
  refine ⟨_, .single hs, domOK_of_reach hwf hd (.single hs), by simpa using hof, hg.top,
    .clean ?_ (hr.of_ret hwf hg (fun u => by simp)).top ?_ ?_⟩
  · simp [addr_succ hi, mlen]
  · rw [hvm, hC]; rfl
  · rw [hvm]; exact hinj.comp (Equiv.injective _)

theorem cont_swap1 {m : MCfg prog} {C OF p pc σ x y} (hd : DomOK m)
    (hof : m.ptr .OF = .bool OF) (hg : GoodStk prog ((p, pc) :: σ))
    (hi : prog.instr p pc = some (.swap x y)) (hIP : m.ptr .IP = .nat (addr prog p pc + 1))
    (hV : m.ptr (.V none) = m.ptr (.V (some x))) (hr : RetOK m ((p, pc) :: σ))
    (hC : C = view m (vm m)) (hinj : Function.Injective (vm m)) :
    ∃ m', Reach (MM).Step m m' ∧ CAbs prog m' ⟨swp C x y, OF, (p, pc + 1) :: σ⟩ := by
  have hp : p ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
  have hI := ins_addr prog hp hi (k := 1) (by simp [mlen])
  have hs := step_assign hwf hIP hI (by simp)
  have hvm : vm ⟨m.reg, Function.update (Function.update m.ptr (.V (some x)) (id (m.ptr (.V (some y)))))
      .IP (.nat (addr prog p pc + 1 + 1))⟩ = Function.update (vm m) x (vm m y) := by
    funext r
    simp only [vm, Function.update_apply]
    split_ifs with h1 <;> simp_all [ptr_V_eq hd]
  obtain ⟨m', h1, h2⟩ := cont_swap2 hwf (C := C) (u := vm m x) (domOK_of_reach hwf hd (.single hs))
    (by simpa using hof) hg hi (by simp) (by simp [hV, ptr_V_eq hd]) (vm_mem_cl hd x)
    (by rw [hvm]; simp [Function.update_apply])
    (hr.of_ret hwf hg (fun u => by simp))
    (by rw [hvm, Function.update_idem, Function.update_eq_self]; exact hC)
    (by rw [hvm, Function.update_idem, Function.update_eq_self]; exact hinj)
  exact ⟨m', .head hs h1, h2⟩

theorem cont_pre2 {m : MCfg prog} {C OF} (hd : DomOK m)
    (hof : m.ptr .OF = .bool OF) (hIP : m.ptr .IP = .nat 2)
    (hret : m.ptr (retP prog prog.main) = .nat 3) (hC : C = view m (vm m))
    (hinj : Function.Injective (vm m)) :
    ∃ m', Reach (MM).Step m m' ∧ CAbs prog m' ⟨C, OF, [(prog.main, 0)]⟩ := by
  have hs := step_jump hwf hIP (ins_two prog)
  have hvm : ∀ {m' : MCfg prog}, (∀ x, m'.ptr (.V (some x)) = m.ptr (.V (some x))) →
      vm m' = vm m := vm_congr
  refine ⟨_, .single hs, domOK_of_reach hwf hd (.single hs), by simpa using hof, .base 0,
    .clean ?_ ?_ ?_ ?_⟩
  · simp [cst, addr_eq_base]
  · simpa [RetOK] using hret
  · rwa [hvm (fun x => by simp)]
  · rwa [hvm (fun x => by simp)]

theorem cont_pre1 {m : MCfg prog} {C OF} (hd : DomOK m)
    (hof : m.ptr .OF = .bool OF) (hIP : m.ptr .IP = .nat 1) (hC : C = view m (vm m))
    (hinj : Function.Injective (vm m)) :
    ∃ m', Reach (MM).Step m m' ∧ CAbs prog m' ⟨C, OF, [(prog.main, 0)]⟩ := by
  have hs := step_assign hwf hIP (ins_one prog) (by simp)
  have hvm : ∀ {m' : MCfg prog}, (∀ x, m'.ptr (.V (some x)) = m.ptr (.V (some x))) →
      vm m' = vm m := vm_congr
  obtain ⟨m', h1, h2⟩ := cont_pre2 hwf (C := C) (OF := OF) (domOK_of_reach hwf hd (.single hs))
    (by simp [retP_of_mem prog main_mem_used, hof]) (by simp) (by simp [cst])
    (by rwa [hvm (fun x => by simp)]) (by rwa [hvm (fun x => by simp)])
  exact ⟨m', .head hs h1, h2⟩

/-! ### The restart helper -/

/-- `E` after moving `c` units from `y` to `z`. -/
def shiftv (E : R → ℕ) (y z : R) (c : ℕ) : R → ℕ :=
  Function.update (Function.update E y (E y - c)) z (E z + c)

omit [Fintype R] [Nonempty R] in
theorem shiftv_zero (E : R → ℕ) (y z : R) : shiftv E y z 0 = E := by
  simp [shiftv]

omit [Fintype R] [Nonempty R] in
theorem shiftv_succ (E : R → ℕ) {y z : R} (hyz : y ≠ z) (c : ℕ) (hc : c + 1 ≤ E y) :
    shiftv (mv E y z) y z c = shiftv E y z (c + 1) := by
  funext r
  simp only [shiftv, mv, Function.update_apply]
  by_cases hrz : r = z
  · subst hrz; simp [Ne.symm hyz]; omega
  · by_cases hry : r = y
    · subst hry; simp [hyz]; omega
    · simp [hrz, hry]

/-- Pointers other than `IP` and `CF` are unchanged. -/
def Same (m m' : MCfg prog) : Prop := ∀ X, X ≠ .IP → X ≠ .CF → m'.ptr X = m.ptr X

theorem Same.trans {m m' m'' : MCfg prog} (h : Same m m') (h' : Same m' m'') : Same m m'' :=
  fun X h1 h2 => (h' X h1 h2).trans (h X h1 h2)

theorem Same.refl (m : MCfg prog) : Same m m := fun _ _ _ => rfl

theorem ins_loop {j k : ℕ} (hj : j < (pairs (R := R)).length) (hk : k < 4) :
    ins prog (hb prog + 4 * j + k) = some (helperInstr prog (4 * j + k)) := by
  rw [add_assoc]; exact ins_hb prog (by omega)

/-- One loop of the helper moves any number `c` of units available. -/
theorem helper_loop {j : ℕ} (hj : j < (pairs (R := R)).length) {ν : R → R}
    (hν : Function.Injective ν) : ∀ (c : ℕ) (m : MCfg prog), DomOK m →
      (∀ x, m.ptr (.V (some x)) = .reg (ν x)) → m.ptr .IP = .nat (hb prog + 4 * j) →
      c ≤ view m ν (hsrc j) →
      ∃ m', Reach (MM).Step m m' ∧ m'.ptr .IP = .nat (hb prog + 4 * j + 4) ∧ Same m m' ∧
        view m' ν = shiftv (view m ν) (hsrc j) (hdst j) c := by
  have hl : 4 * j < 4 * (pairs (R := R)).length := by omega
  have I0 : ins prog (hb prog + 4 * j) = some (.detect (hsrc j)) := by
    have := ins_loop (prog := prog) hj (k := 0) (by omega)
    rw [add_zero] at this; rw [this, helperInstr_0 prog (by omega) (by omega)]
    simp
  have I1 := ins_loop (prog := prog) hj (k := 1) (by omega)
  rw [helperInstr_1 prog (by omega) (by omega), show (4 * j + 1) / 4 = j by omega] at I1
  have I2 := ins_loop (prog := prog) hj (k := 2) (by omega)
  rw [helperInstr_2 prog (by omega) (by omega), show (4 * j + 2) / 4 = j by omega] at I2
  have I3 := ins_loop (prog := prog) hj (k := 3) (by omega)
  rw [helperInstr_3 prog (by omega) (by omega), show (4 * j + 3) / 4 = j by omega] at I3
  have hyz : hsrc j ≠ hdst j := pairs_ne (R := R) hj
  intro c
  induction c with
  | zero =>
    intro m hd hV hIP _
    have s1 := step_detect hwf hIP I0 (hV _) false (.inl rfl)
    refine ⟨_, .head s1 (.single (step_jump hwf (a := hb prog + 4 * j + 1) (by simp) I1)),
      by simp [cj], fun X h1 h2 => by simp [h1, h2], ?_⟩
    rw [shiftv_zero]; rfl
  | succ c ih =>
    intro m hd hV hIP hc
    have hpos : 0 < m.reg (ν (hsrc j)) := by simp only [view] at hc; omega
    have s1 := step_detect hwf hIP I0 (hV _) true (.inr (by simp [hpos]))
    obtain ⟨m₄, hr, h4IP, h4S, h4V⟩ : ∃ m₄, Reach (MM).Step m m₄ ∧
        m₄.ptr .IP = .nat (hb prog + 4 * j) ∧ Same m m₄ ∧
        view m₄ ν = mv (view m ν) (hsrc j) (hdst j) :=
      ⟨_, .head s1 (.head (step_jump hwf (a := hb prog + 4 * j + 1)
        (by simp) I1) (.head (step_move hwf (a := hb prog + 4 * j + 2) (u := ν (hsrc j))
        (w := ν (hdst j)) (by simp [cj]) I2 (by simp [hV]) (by simp [hV]) hpos)
        (.single (step_jump hwf (a := hb prog + 4 * j + 3) (by simp) I3)))),
        by simp [cst], fun X h1 h2 => by simp [h1, h2], by dsimp only; exact view_move hν hyz⟩
    obtain ⟨m', h1, h2, h3, h4⟩ := ih m₄ (domOK_of_reach hwf hd hr)
      (fun x => by rw [h4S _ (by simp) (by simp)]; exact hV x) h4IP (by
        rw [h4V]; simp [mv, view, hyz]; simp only [view] at hc; omega)
    refine ⟨m', hr.trans h1, h2, h4S.trans h3, ?_⟩
    rw [h4, h4V, shiftv_succ _ hyz _ hc]

theorem length_pairs : (pairs (R := R)).length = 2 * (rest (R := R)).length := by
  simp [pairs]; omega

theorem hsrc_collect {j : ℕ} (hj : j < (rest (R := R)).length) :
    hsrc j = (rest (R := R))[j] ∧ hdst j = (x0 : R) := by
  have : (pairs (R := R))[j]? = some ((rest (R := R))[j], x0) := by
    rw [pairs, List.getElem?_append_left (by simpa using hj)]; simp [hj]
  simp only [hsrc, hdst, List.getD_eq_getElem?_getD, this, Option.getD_some]; simp

theorem hsrc_dist {j : ℕ} (hj : j < (rest (R := R)).length) :
    hsrc ((rest (R := R)).length + j) = (x0 : R) ∧
      hdst ((rest (R := R)).length + j) = (rest (R := R))[j] := by
  have : (pairs (R := R))[(rest (R := R)).length + j]? = some (x0, (rest (R := R))[j]) := by
    rw [pairs, List.getElem?_append_right (by simp)]; simp [hj]
  simp only [hsrc, hdst, List.getD_eq_getElem?_getD, this, Option.getD_some]; simp

omit [Fintype R] [DecidableEq R] [DecidableEq P] [Nonempty R] in
theorem drop_cons_eq {α : Type} {l l' : List α} {j : ℕ} {y : α} (h : l.drop j = y :: l') :
    ∃ hj : j < l.length, l[j] = y ∧ l.drop (j + 1) = l' := by
  have hj : j < l.length := by
    by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at h; simp at h
  refine ⟨hj, ?_, ?_⟩
  · have := List.getElem_drop (xs := l) (i := j) (j := 0) (h := by rw [h]; simp)
    simp only [h, List.getElem_cons_zero, add_zero] at this
    exact this.symm
  · rw [← List.drop_drop, h]; rfl

/-- The collecting phase of the helper. -/
theorem helper_collect {ν : R → R} (hν : Function.Injective ν) :
    ∀ (l : List R) (j : ℕ), (rest (R := R)).drop j = l → j ≤ (rest (R := R)).length →
      ∀ m : MCfg prog, DomOK m → (∀ x, m.ptr (.V (some x)) = .reg (ν x)) →
      m.ptr .IP = .nat (hb prog + 4 * j) → (∀ y ∈ rest (R := R), y ∉ l → view m ν y = 0) →
      ∃ m', Reach (MM).Step m m' ∧ m'.ptr .IP = .nat (hb prog + 4 * (rest (R := R)).length) ∧
        Same m m' ∧ ∀ y ∈ rest (R := R), view m' ν y = 0 := by
  intro l
  induction l with
  | nil =>
    intro j hl hj m _ _ hIP h0
    have : j = (rest (R := R)).length := by
      have := List.drop_eq_nil_iff.1 hl; omega
    subst this
    exact ⟨m, .refl, hIP, Same.refl m, fun y hy => h0 y hy (by simp)⟩
  | cons y l ih =>
    intro j hl hj m hd hV hIP h0
    obtain ⟨hjr, hry, hl'⟩ := drop_cons_eq hl
    obtain ⟨hs, hd'⟩ := hsrc_collect (R := R) hjr
    have hjp : j < (pairs (R := R)).length := by rw [length_pairs]; omega
    obtain ⟨m₁, h1, h2, h3, h4⟩ := helper_loop hwf hjp hν (view m ν y) m hd hV hIP
      (by rw [hs, hry])
    obtain ⟨m', h5, h6, h7, h8⟩ := ih (j + 1) hl' (by omega) m₁ (domOK_of_reach hwf hd h1)
      (fun x => by rw [h3 _ (by simp) (by simp)]; exact hV x) (by rw [h2, show hb prog + 4 * j + 4 = hb prog + 4 * (j + 1) by omega])
      (fun y' hy' hy'l => by
        have hx0 : y' ≠ x0 := mem_rest.1 hy'
        rw [h4, hs, hd', hry]
        simp only [shiftv, Function.update_apply, hx0, if_false]
        split_ifs with hyy
        · omega
        · exact h0 y' hy' (by simp [hyy, hy'l]))
    exact ⟨m', h1.trans h5, h6, h3.trans h7, h8⟩

/-- The distributing phase of the helper. -/
theorem helper_distribute {ν : R → R} (hν : Function.Injective ν) (C' : R → ℕ) :
    ∀ (l : List R) (j : ℕ), (rest (R := R)).drop j = l → j ≤ (rest (R := R)).length →
      ∀ m : MCfg prog, DomOK m → (∀ x, m.ptr (.V (some x)) = .reg (ν x)) →
      m.ptr .IP = .nat (hb prog + 4 * ((rest (R := R)).length + j)) →
      (∀ z ∈ l, view m ν z = 0) → (∀ z ∈ rest (R := R), z ∉ l → view m ν z = C' z) →
      view m ν x0 = C' x0 + (l.map C').sum →
      ∃ m', Reach (MM).Step m m' ∧
        m'.ptr .IP = .nat (hb prog + 4 * (pairs (R := R)).length) ∧ Same m m' ∧ view m' ν = C' := by
  intro l
  induction l with
  | nil =>
    intro j hl hj m _ _ hIP _ hC hx0
    have : j = (rest (R := R)).length := by
      have := List.drop_eq_nil_iff.1 hl; omega
    subst this
    refine ⟨m, .refl, by rw [hIP, length_pairs]; congr 2; omega, Same.refl m, ?_⟩
    funext z
    by_cases hz : z = x0
    · subst hz; simpa using hx0
    · exact hC z (mem_rest.2 hz) (by simp)
  | cons z l ih =>
    intro j hl hj m hd hV hIP h0 hC hx0
    obtain ⟨hjr, hrz, hl'⟩ := drop_cons_eq hl
    obtain ⟨hs, hd'⟩ := hsrc_dist (R := R) hjr
    have hjp : (rest (R := R)).length + j < (pairs (R := R)).length := by rw [length_pairs]; omega
    have hnd : (z :: l).Nodup := hl ▸ (Finset.nodup_toList _).sublist (List.drop_sublist _ _)
    have hzl : z ∉ l := (List.nodup_cons.1 hnd).1
    have hzr : z ∈ rest (R := R) := List.mem_of_mem_drop (hl ▸ List.mem_cons_self)
    have hzx : z ≠ x0 := mem_rest.1 hzr
    obtain ⟨m₁, h1, h2, h3, h4⟩ := helper_loop hwf hjp hν (C' z) m hd hV hIP
      (by rw [hs, hx0]; simp; omega)
    obtain ⟨m', h5, h6, h7, h8⟩ := ih (j + 1) hl' (by omega) m₁ (domOK_of_reach hwf hd h1)
      (fun x => by rw [h3 _ (by simp) (by simp)]; exact hV x) (by rw [h2, show hb prog + 4 * ((rest (R := R)).length + j) + 4 =
        hb prog + 4 * ((rest (R := R)).length + (j + 1)) by omega])
      (fun z' hz' => by
        have hz'r : z' ∈ rest (R := R) := List.mem_of_mem_drop (hl ▸ List.mem_cons_of_mem _ hz')
        have hx0' : z' ≠ x0 := mem_rest.1 hz'r
        have hzz : z' ≠ z := fun h => hzl (h ▸ hz')
        rw [h4, hs, hd', hrz]
        simp only [shiftv, Function.update_apply, hx0', hzz, if_false]
        exact h0 z' (List.mem_cons_of_mem _ hz'))
      (fun z' hz' hz'l => by
        have hx0' : z' ≠ x0 := mem_rest.1 hz'
        rw [h4, hs, hd', hrz]
        simp only [shiftv, Function.update_apply, hx0', if_false]
        split_ifs with hzz
        · subst hzz; rw [h0 z' List.mem_cons_self]; simp
        · exact hC z' hz' (by simp [hzz, hz'l]))
      (by
        rw [h4, hs, hd', hrz]
        simp only [shiftv, Function.update_apply, Ne.symm hzx, if_false, if_true, hx0]
        simp; omega)
    exact ⟨m', h1.trans h5, h6, h3.trans h7, h8⟩

theorem total_eq_rest (f : R → ℕ) : Program.total f = f x0 + ((rest (R := R)).map f).sum := by
  unfold Program.total
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (x0 : R)), rest, Finset.sum_map_toList]

/-- **The restart helper** reaches every register configuration with the same number of units
and then jumps to instruction 1. -/
theorem helper_restart {m : MCfg prog} (hd : DomOK m) (hIP : m.ptr .IP = .nat (hb prog))
    (hinj : Function.Injective (vm m)) (C' : R → ℕ) (hC' : Program.total C' = Machine.total m) :
    ∃ m', Reach (MM).Step m m' ∧ m'.ptr .IP = .nat 1 ∧ Same m m' ∧ view m' (vm m) = C' := by
  have hV : ∀ x, m.ptr (.V (some x)) = .reg (vm m x) := ptr_V_eq hd
  obtain ⟨m₁, h1, h2, h3, h4⟩ := helper_collect hwf hinj (rest (R := R)) 0 rfl (Nat.zero_le _) m hd
    hV (by simpa using hIP) (fun y hy hy' => absurd hy hy')
  have hd₁ := domOK_of_reach hwf hd h1
  have hV₁ : ∀ x, m₁.ptr (.V (some x)) = .reg (vm m x) :=
    fun x => by rw [h3 _ (by simp) (by simp)]; exact hV x
  have htot : Program.total (view m₁ (vm m)) = Machine.total m := by
    rw [total_view hinj, total_of_reach hwf hd h1]
  obtain ⟨m₂, h5, h6, h7, h8⟩ := helper_distribute hwf hinj C' (rest (R := R)) 0 rfl (Nat.zero_le _)
    m₁ hd₁ hV₁ (by simpa using h2) h4 (fun z hz hz' => absurd hz hz') (by
      have e1 := total_eq_rest (view m₁ (vm m))
      have e2 := total_eq_rest C'
      have e3 : ((rest (R := R)).map (view m₁ (vm m))).sum = 0 :=
        List.sum_eq_zero (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact h4 y hy)
      omega)
  have I := ins_hb prog (le_refl (4 * (pairs (R := R)).length))
  rw [helperInstr, ite_eq_right (lt_irrefl _)] at I
  have s := step_jump hwf h6 I
  exact ⟨_, h1.trans (h5.tail s), by simp [cst], h3.trans (h7.trans
    (fun X h1 h2 => by simp [h1, h2])), h8⟩

/-- Skipping the remaining loops of the helper (every `detect` returns `false`). -/
theorem helper_skip {ν : R → R} (hν : Function.Injective ν) : ∀ (k j : ℕ),
    j + k = (pairs (R := R)).length → ∀ m : MCfg prog, DomOK m →
    (∀ x, m.ptr (.V (some x)) = .reg (ν x)) → m.ptr .IP = .nat (hb prog + 4 * j) →
    ∃ m', Reach (MM).Step m m' ∧ m'.ptr .IP = .nat (hb prog + 4 * (pairs (R := R)).length) ∧
      Same m m' := by
  intro k
  induction k with
  | zero => intro j hj m _ _ hIP; exact ⟨m, .refl, by rw [hIP, ← hj, add_zero], Same.refl m⟩
  | succ k ih =>
    intro j hj m hd hV hIP
    obtain ⟨m₁, h1, h2, h3, -⟩ := helper_loop hwf (j := j) (by omega) hν 0 m hd hV hIP (Nat.zero_le _)
    obtain ⟨m', h4, h5, h6⟩ := ih (j + 1) (by omega) m₁ (domOK_of_reach hwf hd h1)
      (fun x => by rw [h3 _ (by simp) (by simp)]; exact hV x)
      (by rw [h2, show hb prog + 4 * j + 4 = hb prog + 4 * (j + 1) by omega])
    exact ⟨m', h1.trans h4, h5, h3.trans h6⟩

/-- From anywhere inside the helper, the machine can reach instruction 1. -/
theorem helper_exit {m : MCfg prog} {t : ℕ} (hd : DomOK m) (hIP : m.ptr .IP = .nat (hb prog + t))
    (ht : t ≤ 4 * (pairs (R := R)).length) (hH : HInv m t) (hinj : Function.Injective (vm m)) :
    ∃ m', Reach (MM).Step m m' ∧ m'.ptr .IP = .nat 1 ∧ Same m m' := by
  have hV : ∀ x, m.ptr (.V (some x)) = .reg (vm m x) := ptr_V_eq hd
  -- first reach the start of a loop
  obtain ⟨m₁, j, h1, hj, h1IP, h1S⟩ : ∃ m₁ j, Reach (MM).Step m m₁ ∧
      j ≤ (pairs (R := R)).length ∧ m₁.ptr .IP = .nat (hb prog + 4 * j) ∧ Same m m₁ := by
    rcases Nat.lt_or_ge t (4 * (pairs (R := R)).length) with hlt | hge
    · have I := ins_hb prog ht
      rcases (by omega : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3) with hk | hk | hk | hk
      · exact ⟨m, t / 4, .refl, by omega, by rw [hIP]; congr 2; omega, Same.refl m⟩
      · rw [helperInstr_1 prog hlt hk] at I
        obtain ⟨b, hCF⟩ := bool_of_dom hd
        cases b
        · exact ⟨_, t / 4 + 1, .single (step_jump hwf hIP I), by omega,
            by simp [cj, hCF]; omega, fun X h1 h2 => by simp [h1, h2]⟩
        · have hpos := (hH hlt).1 hk hCF
          have I2 := ins_hb (prog := prog) (t := 4 * (t / 4) + 2) (by omega)
          rw [helperInstr_2 prog (by omega) (by omega), show (4 * (t / 4) + 2) / 4 = t / 4 by omega]
            at I2
          have I3 := ins_hb (prog := prog) (t := 4 * (t / 4) + 3) (by omega)
          rw [helperInstr_3 prog (by omega) (by omega), show (4 * (t / 4) + 3) / 4 = t / 4 by omega]
            at I3
          exact ⟨_, t / 4, .head (step_jump hwf hIP I) (.head (step_move hwf
            (u := vm m (hsrc (t / 4))) (w := vm m (hdst (t / 4))) (by simp [cj, hCF]; omega) I2
            (by simp [hV]) (by simp [hV]) hpos) (.single (step_jump hwf
              (by simp; rfl) I3))), by omega, by simp [cst], fun X h1 h2 => by simp [h1, h2]⟩
      · rw [helperInstr_2 prog hlt hk] at I
        have hpos := (hH hlt).2 hk
        have I3 := ins_hb (prog := prog) (t := t + 1) (by omega)
        rw [helperInstr_3 prog (by omega) (by omega), show (t + 1) / 4 = t / 4 by omega] at I3
        exact ⟨_, t / 4, .head (step_move hwf (u := vm m (hsrc (t / 4)))
          (w := vm m (hdst (t / 4))) hIP I (by simp [hV]) (by simp [hV]) hpos) (.single
            (step_jump hwf (by simp; rfl) I3)), by omega, by simp [cst],
            fun X h1 h2 => by simp [h1, h2]⟩
      · rw [helperInstr_3 prog hlt hk] at I
        exact ⟨_, t / 4, .single (step_jump hwf hIP I), by omega, by simp [cst],
          fun X h1 h2 => by simp [h1, h2]⟩
    · exact ⟨m, (pairs (R := R)).length, .refl, le_rfl, by rw [hIP]; congr 2; omega, Same.refl m⟩
  obtain ⟨m₂, h2, h2IP, h2S⟩ := helper_skip hwf hinj ((pairs (R := R)).length - j) j (by omega) m₁
    (domOK_of_reach hwf hd h1) (fun x => by rw [h1S _ (by simp) (by simp)]; exact hV x) h1IP
  have I := ins_hb prog (le_refl (4 * (pairs (R := R)).length))
  rw [helperInstr, ite_eq_right (lt_irrefl _)] at I
  exact ⟨_, h1.trans (h2.tail (step_jump hwf h2IP I)), by simp [cst],
    h1S.trans (h2S.trans (fun X h1 h2 => by simp [h1, h2]))⟩

/-! ### Main simulation lemmas -/

/-- From every related configuration a clean one is reachable. -/
theorem to_clean {m : MCfg prog} {s : Cfg R P} (h : Abs prog m s) :
    ∃ m' s', Reach (MM).Step m m' ∧ Reach prog.Step s s' ∧ CAbs prog m' s' := by
  obtain ⟨hd, hof, hg, hloc⟩ := h
  cases hloc with
  | cl h => exact ⟨m, s, .refl, .refl, hd, hof, hg, h⟩
  | pre1 hIP hC hinj =>
    obtain ⟨m', h1, h2⟩ := cont_pre1 hwf hd hof hIP hC hinj
    exact ⟨m', _, h1, .refl, h2⟩
  | pre2 hIP hret hC hinj =>
    obtain ⟨m', h1, h2⟩ := cont_pre2 hwf hd hof hIP hret hC hinj
    exact ⟨m', _, h1, .refl, h2⟩
  | swap1 hi hIP hV hr hC hinj =>
    obtain ⟨m', h1, h2⟩ := cont_swap1 hwf hd hof hg hi hIP hV hr hC hinj
    exact ⟨m', _, h1, .single (.inl (.swap hi)), h2⟩
  | swap2 hi hIP hV hu hxy hr hC hinj =>
    obtain ⟨m', h1, h2⟩ := cont_swap2 hwf hd hof hg hi hIP hV hu hxy hr hC hinj
    exact ⟨m', _, h1, .single (.inl (.swap hi)), h2⟩
  | @det C OF p pc σ x tT tF b hi hIP hCF hb hr hC hinj =>
    obtain ⟨m', h1, h2⟩ := cont_det hwf hd hof hg hi hIP hCF hr hC hinj
    refine ⟨m', _, h1, ?_, h2⟩
    cases b
    · exact .single (.inl (.detectF hi))
    · exact .single (.inl (.detectT hi (hb rfl)))
  | call1 hi hIP hret hr hC hinj =>
    obtain ⟨m', h1, h2⟩ := cont_call1 hwf hd hof hg hi hIP hret hr hC hinj
    exact ⟨m', _, h1, .single (.inl (.call hi)), h2⟩
  | call2 hi hIP hCF hr hC hinj =>
    obtain ⟨m', h1, h2⟩ := cont_call2 hwf hd hof hg hi hIP hCF hr hC hinj
    exact ⟨m', _, h1, .refl, h2⟩
  | @ret1 C OF q pc σ b hi hIP hCF hr hC hinj =>
    cases σ with
    | nil =>
      obtain ⟨m', h1, h2⟩ := cont_ret1_nil hwf (C := C) hd hof hg hi hIP hr
      exact ⟨m', _, h1, .refl, h2⟩
    | cons f σ =>
      obtain ⟨p, pc'⟩ := f
      obtain ⟨tT, tF, hc⟩ : ∃ tT tF, prog.instr p pc' = some (.call q tT tF) := by
        cases hg with
        | cons hc _ => exact ⟨_, _, hc⟩
      obtain ⟨m', h1, h2⟩ := cont_ret1_cons hwf hd hof hg hi hc hIP hCF hr hC hinj
      exact ⟨m', _, h1, .single (.inl (.ret hi hc)), h2⟩
  | @helper s t hIP ht hH hat htot hinj =>
    obtain ⟨m₁, h1, h1IP, h1S⟩ := helper_exit hwf hd hIP ht hH hinj
    have hvm : vm m₁ = vm m := vm_congr (fun x => h1S _ (by simp) (by simp))
    obtain ⟨m₂, h2, h3⟩ := cont_pre1 hwf (C := view m₁ (vm m₁)) (OF := s.OF)
      (domOK_of_reach hwf hd h1) (by rw [h1S _ (by simp) (by simp)]; exact hof) h1IP rfl
      (by rwa [hvm])
    refine ⟨m₂, ⟨view m₁ (vm m₁), s.OF, [(prog.main, 0)]⟩, h1.trans h2,
      .single (.inr (.inl ⟨hat, ?_, rfl, rfl⟩)), h3⟩
    simp only
    rw [hvm, total_view hinj, total_of_reach hwf hd h1, htot]

/-- Every program step from a configuration related to a clean machine configuration is simulated
by a machine path ending in a clean configuration. -/
theorem clean_sim {m : MCfg prog} {s s' : Cfg R P} (h : CAbs prog m s) (hs : prog.Step s s') :
    ∃ m', Reach (MM).Step m m' ∧ CAbs prog m' s' := by
  rcases hs with h₀ | hR | ⟨rfl, -⟩
  · obtain ⟨hd, hof, hg, hloc⟩ := h
    have hvm : ∀ {m' : MCfg prog}, (∀ x, m'.ptr (.V (some x)) = m.ptr (.V (some x))) →
        vm m' = vm m := vm_congr
    cases h₀ with
    | @move C OF p pc σ x y hi hx =>
      cases hloc with
      | final _ hi' => rw [hi] at hi'; cases hi'
      | clean hIP hr hC hinj =>
        have hp : p ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
        have hI := ins_addr prog hp hi (k := 0) (by simp [mlen])
        rw [add_zero] at hI
        have hxy : x ≠ y := hwf.move_ne p (used_subset hwf hp) x y (mem_code_of_getElem? hi)
        have hs := step_move hwf hIP hI (ptr_V_eq hd x) (ptr_V_eq hd y) (by rw [hC] at hx; exact hx)
        refine ⟨_, .single hs, domOK_of_reach hwf hd (.single hs), by simpa using hof, hg.top,
          .clean ?_ (hr.of_ret hwf hg (fun u => by simp)).top ?_ ?_⟩
        · simp [addr_succ hi, mlen]
        · rw [hvm (fun x => by simp), hC]
          exact (view_move hinj hxy).symm
        · rwa [hvm (fun x => by simp)]
    | @swap C OF p pc σ x y hi =>
      cases hloc with
      | final _ hi' => rw [hi] at hi'; cases hi'
      | clean hIP hr hC hinj =>
        have hp : p ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
        have hI := ins_addr prog hp hi (k := 0) (by simp [mlen])
        rw [add_zero] at hI
        have hs := step_assign hwf hIP hI (by simp)
        obtain ⟨m', h1, h2⟩ := cont_swap1 hwf (C := C) (domOK_of_reach hwf hd (.single hs))
          (by simpa using hof) hg hi (by simp) (by simp) (hr.of_ret hwf hg (fun u => by simp))
          (by rwa [hvm (fun x => by simp)]) (by rwa [hvm (fun x => by simp)])
        exact ⟨m', .head hs h1, h2⟩
    | @setOF C OF p pc σ b hi =>
      cases hloc with
      | final _ hi' => rw [hi] at hi'; cases hi'
      | clean hIP hr hC hinj =>
        have hp : p ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
        have hI := ins_addr prog hp hi (k := 0) (by simp [mlen])
        rw [add_zero] at hI
        have hs := step_assign hwf hIP hI (by simp)
        refine ⟨_, .single hs, domOK_of_reach hwf hd (.single hs), by simp [cst], hg.top,
          .clean ?_ (hr.of_ret hwf hg (fun u => by simp)).top ?_ ?_⟩
        · simp [addr_succ hi, mlen]
        · rwa [hvm (fun x => by simp)]
        · rwa [hvm (fun x => by simp)]
    | @detectT C OF p pc σ x tT tF hi hx =>
      cases hloc with
      | final _ hi' => rw [hi] at hi'; cases hi'
      | clean hIP hr hC hinj =>
        have hp : p ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
        have hI := ins_addr prog hp hi (k := 0) (by simp [mlen])
        rw [add_zero] at hI
        have hs := step_detect hwf hIP hI (ptr_V_eq hd x) true
          (.inr (by rw [hC] at hx; simp [view] at hx ⊢; exact hx))
        obtain ⟨m', h1, h2⟩ := cont_det hwf (C := C) (b := true) (domOK_of_reach hwf hd (.single hs))
          (by simpa using hof) hg hi (by simp) (by simp) (hr.of_ret hwf hg (fun u => by simp))
          (by rwa [hvm (fun x => by simp)]) (by rwa [hvm (fun x => by simp)])
        exact ⟨m', .head hs h1, h2⟩
    | @detectF C OF p pc σ x tT tF hi =>
      cases hloc with
      | final _ hi' => rw [hi] at hi'; cases hi'
      | clean hIP hr hC hinj =>
        have hp : p ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
        have hI := ins_addr prog hp hi (k := 0) (by simp [mlen])
        rw [add_zero] at hI
        have hs := step_detect hwf hIP hI (ptr_V_eq hd x) false (.inl rfl)
        obtain ⟨m', h1, h2⟩ := cont_det hwf (C := C) (b := false)
          (domOK_of_reach hwf hd (.single hs))
          (by simpa using hof) hg hi (by simp) (by simp) (hr.of_ret hwf hg (fun u => by simp))
          (by rwa [hvm (fun x => by simp)]) (by rwa [hvm (fun x => by simp)])
        exact ⟨m', .head hs h1, h2⟩
    | @goto C OF p pc σ t hi =>
      cases hloc with
      | final _ hi' => rw [hi] at hi'; cases hi'
      | clean hIP hr hC hinj =>
        have hp : p ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
        have hI := ins_addr prog hp hi (k := 0) (by simp [mlen])
        rw [add_zero] at hI
        have hs := step_jump hwf hIP hI
        refine ⟨_, .single hs, domOK_of_reach hwf hd (.single hs), by simpa using hof, hg.top,
          .clean ?_ (hr.of_ret hwf hg (fun u => by simp)).top ?_ ?_⟩
        · simp [cst]
        · rwa [hvm (fun x => by simp)]
        · rwa [hvm (fun x => by simp)]
    | @call C OF p pc σ q tT tF hi =>
      cases hloc with
      | final _ hi' => rw [hi] at hi'; cases hi'
      | clean hIP hr hC hinj =>
        have hp : p ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
        have hq := mem_used_of_call hwf hp (mem_code_of_getElem? hi)
        have hnm := hg.callee_notMem hwf hi
        have hI := ins_addr prog hp hi (k := 0) (by simp [mlen])
        rw [add_zero] at hI
        have hs := step_assign hwf hIP hI (by simp)
        obtain ⟨m', h1, h2⟩ := cont_call1 hwf (C := C) (OF := OF)
          (domOK_of_reach hwf hd (.single hs))
          (by simp [retP_of_mem prog hq, hof]) hg hi (by simp) (by simp [cst])
          (hr.congr fun f hf => by
            have hf' : retP prog f.1 ≠ retP prog q :=
              fun h => hnm f hf ((retP_inj (hg.mem_used hwf f hf) hq).1 h)
            simp [hf'])
          (by rwa [hvm (fun x => by simp)]) (by rwa [hvm (fun x => by simp)])
        exact ⟨m', .head hs h1, h2⟩
    | @ret C OF q pc p pc' σ b q' tT tF hi hc =>
      cases hloc with
      | clean hIP hr hC hinj =>
        have e : q' = q := by
          cases hg with
          | cons hc' _ => rw [hc] at hc'; cases hc'; rfl
        subst e
        have hq : q' ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
        have hI := ins_addr prog hq hi (k := 0) (by simp [mlen])
        rw [add_zero] at hI
        have hs := step_assign hwf hIP hI (by simp)
        obtain ⟨m', h1, h2⟩ := cont_ret1_cons hwf (C := C) (b := b)
          (domOK_of_reach hwf hd (.single hs))
          (by simpa using hof) hg hi hc (by simp) (by simp [cst])
          (hr.of_ret hwf hg (fun u => by simp))
          (by rwa [hvm (fun x => by simp)]) (by rwa [hvm (fun x => by simp)])
        exact ⟨m', .head hs h1, h2⟩
  · obtain ⟨⟨p, pc, σ, hstk, hi⟩, htot, hOF, hstk'⟩ := hR
    obtain ⟨hd, hof, hg, hloc⟩ := h
    obtain ⟨C, OF, stk⟩ := s
    simp only at hstk; subst hstk
    cases hloc with
    | final _ hi' => rw [hi] at hi'; cases hi'
    | clean hIP hr hC hinj =>
      have hp : p ∈ used prog := hg.mem_used hwf _ List.mem_cons_self
      have hI := ins_addr prog hp hi (k := 0) (by simp [mlen])
      rw [add_zero] at hI
      have hs := step_jump hwf hIP hI
      have hvm : vm ⟨m.reg, Function.update m.ptr .IP (cst (.nat (hb prog)) (m.ptr .IP))⟩ = vm m :=
        vm_congr (fun x => by simp)
      obtain ⟨m₂, h2, h2IP, h2S, h2V⟩ := helper_restart hwf (domOK_of_reach hwf hd (.single hs))
        (by simp [cst]) (by rwa [hvm]) s'.C (by
          rw [htot]; simp only at hC ⊢; rw [hC, total_view hinj]; rfl)
      have hvm₂ : vm m₂ = vm m := by
        rw [vm_congr (fun x => h2S _ (by simp) (by simp)), hvm]
      obtain ⟨m₃, h3, h4⟩ := cont_pre1 hwf (C := s'.C) (OF := s'.OF)
        (domOK_of_reach hwf hd ((Relation.ReflTransGen.single hs).trans h2))
        (by rw [h2S _ (by simp) (by simp), hOF]; simpa using hof) h2IP
        (by rw [hvm₂, ← hvm, h2V]) (by rwa [hvm₂])
      refine ⟨m₃, (Relation.ReflTransGen.single hs).trans (h2.trans h3), ?_⟩
      obtain ⟨C', OF', stk'⟩ := s'
      simp only at hstk'; subst hstk'
      exact h4
  · exact ⟨m, .refl, h⟩

end Sim

end Podc.PPDoubleExpThresholds.ProgramToMachine
