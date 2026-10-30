import Papers.PODC2023.PPDoubleExpThresholds.ProgramToMachineInv

/-!
# From population programs to population machines: machine steps are simulated

Every step of the machine from a configuration related (`Abs`) to a program configuration `s`
leads to a configuration related to a configuration reachable from `s` (`step_abs`). Hence every
configuration reachable in the machine is related to a configuration reachable in the program
(`reach_abs`), and outputs agree along the relation.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.PPDoubleExpThresholds.ProgramToMachine

open Finset Cslib.TransitionSystem

variable {R P : Type} [Fintype R] [DecidableEq R] [DecidableEq P] [Nonempty R]
variable {prog : Program R P}

omit [Nonempty R] in
theorem addr_succ {p : P} {pc : ℕ} {i : Instr R P} (hi : prog.instr p pc = some i) :
    addr prog p (pc + 1) = addr prog p pc + mlen i := by
  have hpc := lt_length_of_getElem? prog hi
  have h1 : min pc (prog.code p).length = pc := Nat.min_eq_left hpc.le
  have h2 : min (pc + 1) (prog.code p).length = pc + 1 := Nat.min_eq_left hpc
  have hi' : (prog.code p)[pc]? = some i := hi
  simp only [addr, off, h1, h2, sum_range_succ, mlenAt, hi']
  simp; omega

omit [Nonempty R] in
theorem addr_eq_base {p : P} : addr prog p 0 = base prog p := by simp [addr, off_zero]

theorem view_move {m : MCfg prog} {ν : R → R} (hν : Function.Injective ν) {x y : R} (hxy : x ≠ y) :
    (fun r => Function.update (Function.update m.reg (ν x) (m.reg (ν x) - 1)) (ν y)
      (Function.update m.reg (ν x) (m.reg (ν x) - 1) (ν y) + 1) (ν r)) =
      mv (view m ν) x y := by
  have hne : ν x ≠ ν y := hν.ne hxy
  funext r
  simp only [mv, view, Function.update_apply]
  by_cases hrx : r = x
  · subst hrx; simp [hne, hxy]
  · by_cases hry : r = y
    · subst hry; simp [Ne.symm hne, hrx]
    · simp [hν.ne hrx, hν.ne hry, hrx, hry]

theorem cl_eq {x y : R} (h : prog.SwapEdge x y) : cl prog x = cl prog y := by
  apply le_antisymm
  · apply cl_subset
    obtain ⟨p, hp, h⟩ := h
    exact ⟨p, hp, h.symm⟩
  · exact cl_subset h

variable (prog) in
theorem helperInstr_0 {t : ℕ} (ht : t < 4 * (pairs (R := R)).length) (hk : t % 4 = 0) :
    helperInstr prog t = .detect (hsrc (t / 4)) := by
  simp [helperInstr, ht, hk, hsrc]

variable (prog) in
theorem helperInstr_1 {t : ℕ} (ht : t < 4 * (pairs (R := R)).length) (hk : t % 4 = 1) :
    helperInstr prog t = .assign .IP .CF (cj (hb prog + 4 * (t / 4) + 2) (hb prog + 4 * (t / 4) + 4)) := by
  simp [helperInstr, ht, hk]

variable (prog) in
theorem helperInstr_2 {t : ℕ} (ht : t < 4 * (pairs (R := R)).length) (hk : t % 4 = 2) :
    helperInstr prog t = .move (hsrc (t / 4)) (hdst (t / 4)) := by
  simp [helperInstr, ht, hk, hsrc, hdst]

variable (prog) in
theorem helperInstr_3 {t : ℕ} (ht : t < 4 * (pairs (R := R)).length) (hk : t % 4 = 3) :
    helperInstr prog t = .assign .IP .IP (cst (.nat (hb prog + 4 * (t / 4)))) := by
  simp [helperInstr, ht, hk]

section Step

variable (hwf : prog.WellFormed)

local notation "MM" => machine prog hwf

theorem cfg_eta (m : MCfg prog) : (⟨m.reg, m.ptr⟩ : MCfg prog) = m := rfl

/-- One step from a clean position. -/
theorem exec_clean {m m' : MCfg prog} {s : Cfg R P} (hd : DomOK m) (hof : m.ptr .OF = .bool s.OF)
    (hg : GoodStk prog s.stk) (hloc : CLoc m s) (hd' : DomOK m') (hex : (MM).Exec m m') :
    ∃ s', Abs prog m' s' ∧ Reach prog.Step s s' := by
  cases hloc with
  | @final C OF pc b hIP hi =>
    have hI : (MM).instr 3 = some (.assign .IP .IP (cst (.nat 3))) := ins_three prog
    obtain rfl := exec_jump_inv (A := MM) hIP hI hex
    refine ⟨_, ⟨hd', hof, hg, .cl (.final ?_ hi)⟩, .refl⟩
    simp [cst]
  | @clean C OF p pc σ hIP hr hC hinj =>
    have hp : p ∈ used prog := hg.mem_used hwf (p, pc) (by simp)
    rcases hi : (prog.code p)[pc]? with _ | i
    · have hlen := List.getElem?_eq_none_iff.1 hi
      have hI := ins_guard prog hp hlen
      obtain rfl := exec_jump_inv (A := MM) hIP hI hex
      have e : addr prog p (prog.code p).length = addr prog p pc := by
        simp [addr, off_of_le prog p hlen]
      refine ⟨_, ?_, .refl⟩
      simp only [machine_IP, cst, e, ← hIP, Function.update_eq_self]
      exact ⟨hd, hof, hg, .cl (.clean hIP hr hC hinj)⟩
    · have hI : ∀ k, k < mlen i → (MM).instr (addr prog p pc + k) = (cinstr prog p pc i)[k]? :=
        fun k hk => ins_addr prog hp hi hk
      have hIP0 : m.ptr (MM).IP = .nat (addr prog p pc + 0) := hIP
      have hnext := addr_succ (prog := prog) (p := p) (pc := pc) hi
      cases i with
      | move x y =>
        obtain ⟨u, w, hu, hw, hpos, rfl⟩ := exec_move_inv (A := MM) hIP0 (hI 0 (by simp [mlen])) hex
        rw [machine_V, ptr_V_eq hd] at hu hw
        cases hu; cases hw
        have hxy : x ≠ y := hwf.move_ne p (used_subset hwf hp) x y (mem_code_of_getElem? hi)
        have hx : 0 < C x := by rw [hC]; exact hpos
        refine ⟨⟨mv C x y, OF, (p, pc + 1) :: σ⟩, ⟨hd', by simpa using hof, hg.top,
          .cl (.clean ?_ (hr.of_ret hwf hg (fun u => by simp)).top ?_ ?_)⟩,
          .single (.inl (.move hi hx))⟩
        · simp [hnext, mlen]
        · rw [vm_congr (m := m) (fun x => by simp), hC]
          exact (view_move hinj hxy).symm
        · rwa [vm_congr (m := m) (fun x => by simp)]
      | swap x y =>
        obtain rfl := exec_assign_inv (A := MM) hIP0 (hI 0 (by simp [mlen])) (by simp) hex
        refine ⟨_, ⟨hd', by simpa using hof, hg, .swap1 hi ?_ ?_ (hr.of_ret hwf hg
          (fun u => by simp)) ?_ ?_⟩, .refl⟩
        · simp
        · simp
        · rwa [vm_congr (m := m) (fun x => by simp)]
        · rwa [vm_congr (m := m) (fun x => by simp)]
      | setOF b =>
        obtain rfl := exec_assign_inv (A := MM) hIP0 (hI 0 (by simp [mlen])) (by simp) hex
        refine ⟨⟨C, b, (p, pc + 1) :: σ⟩, ⟨hd', by simp [cst], hg.top,
          .cl (.clean ?_ (hr.of_ret hwf hg (fun u => by simp)).top ?_ ?_)⟩,
          .single (.inl (.setOF hi))⟩
        · simp [hnext, mlen]
        · rwa [vm_congr (m := m) (fun x => by simp)]
        · rwa [vm_congr (m := m) (fun x => by simp)]
      | detect x tT tF =>
        obtain ⟨u, b, hu, hb, rfl⟩ :=
          exec_detect_inv (A := MM) hIP0 (hI 0 (by simp [mlen])) hex
        rw [machine_V, ptr_V_eq hd] at hu
        cases hu
        refine ⟨_, ⟨hd', by simpa using hof, hg, .det hi (b := b) ?_ ?_ ?_
          (hr.of_ret hwf hg (fun u => by simp)) ?_ ?_⟩, .refl⟩
        · simp
        · simp
        · rintro rfl; rw [hC]; simpa [view] using hb
        · rwa [vm_congr (m := m) (fun x => by simp)]
        · rwa [vm_congr (m := m) (fun x => by simp)]
      | call q tT tF =>
        obtain rfl := exec_assign_inv (A := MM) hIP0 (hI 0 (by simp [mlen])) (by simp) hex
        have hq := mem_used_of_call hwf hp (mem_code_of_getElem? hi)
        have hnm := hg.callee_notMem hwf hi
        refine ⟨_, ⟨hd', by simp [retP_of_mem prog hq, hof], hg, .call1 hi ?_ ?_ ?_ ?_ ?_⟩, .refl⟩
        · simp
        · simp [cst]
        · refine hr.congr fun f hf => ?_
          have hf' : retP prog f.1 ≠ retP prog q :=
            fun h => hnm f hf ((retP_inj (hg.mem_used hwf f hf) hq).1 h)
          simp [Function.update_apply, hf']
        · rwa [vm_congr (m := m) (fun x => by simp)]
        · rwa [vm_congr (m := m) (fun x => by simp)]
      | ret b =>
        obtain rfl := exec_assign_inv (A := MM) hIP0 (hI 0 (by simp [mlen])) (by simp) hex
        refine ⟨_, ⟨hd', by simpa using hof, hg, .ret1 hi ?_ ?_
          (hr.of_ret hwf hg (fun u => by simp)) ?_ ?_⟩, .refl⟩
        · simp
        · simp [cst]
        · rwa [vm_congr (m := m) (fun x => by simp)]
        · rwa [vm_congr (m := m) (fun x => by simp)]
      | goto t =>
        obtain rfl := exec_jump_inv (A := MM) hIP0 (hI 0 (by simp [mlen])) hex
        refine ⟨⟨C, OF, (p, t) :: σ⟩, ⟨hd', by simpa using hof, hg.top,
          .cl (.clean ?_ (hr.of_ret hwf hg (fun u => by simp)).top ?_ ?_)⟩,
          .single (.inl (.goto hi))⟩
        · simp [cst]
        · rwa [vm_congr (m := m) (fun x => by simp)]
        · rwa [vm_congr (m := m) (fun x => by simp)]
      | restart =>
        obtain rfl := exec_jump_inv (A := MM) hIP0 (hI 0 (by simp [mlen])) hex
        refine ⟨_, ⟨hd', by simpa using hof, hg, .helper (t := 0) ?_ (Nat.zero_le _) ?_
          ⟨p, pc, σ, rfl, hi⟩ ?_ ?_⟩, .refl⟩
        · simp [cst]
        · intro h0; simp [HInv] at *
        · rw [hC, total_view hinj]; rfl
        · rwa [vm_congr (m := m) (fun x => by simp)]

/-- One step from any position. -/
theorem exec_abs {m m' : MCfg prog} {s : Cfg R P} (h : Abs prog m s) (hex : (MM).Exec m m') :
    ∃ s', Abs prog m' s' ∧ Reach prog.Step s s' := by
  obtain ⟨hd, hof, hg, hloc⟩ := h
  have hd' : DomOK m' := exec_dom (lastJump hwf) hd hex
  cases hloc with
  | cl h => exact exec_clean hwf hd hof hg h hd' hex
  | @pre1 C OF hIP hC hinj =>
    have hI : (MM).instr 1 = some (.assign (retP prog prog.main) .IP (cst (.nat 3))) := ins_one prog
    obtain rfl := exec_assign_inv (A := MM) hIP hI (by simp) hex
    refine ⟨_, ⟨hd', by simp [retP_of_mem prog main_mem_used, hof], hg, .pre2 ?_ ?_ ?_ ?_⟩, .refl⟩
    · simp
    · simp [cst]
    · rwa [vm_congr (m := m) (fun x => by simp)]
    · rwa [vm_congr (m := m) (fun x => by simp)]
  | @pre2 C OF hIP hret hC hinj =>
    have hI : (MM).instr 2 = some (.assign .IP .IP (cst (.nat (base prog prog.main)))) := ins_two prog
    obtain rfl := exec_jump_inv (A := MM) hIP hI hex
    refine ⟨_, ⟨hd', by simpa using hof, hg, .cl (.clean (pc := 0) ?_ ?_ ?_ ?_)⟩, .refl⟩
    · simp [cst, addr_eq_base]
    · simpa [RetOK] using hret
    · rwa [vm_congr (m := m) (fun x => by simp)]
    · rwa [vm_congr (m := m) (fun x => by simp)]
  | @swap1 C OF p pc σ x y hi hIP hV hr hC hinj =>
    have hp : p ∈ used prog := hg.mem_used hwf (p, pc) (by simp)
    have hI := ins_addr prog hp hi (k := 1) (by simp [mlen])
    obtain rfl := exec_assign_inv (A := MM) hIP hI (by simp) hex
    have hvm : vm ⟨m.reg, Function.update (Function.update m.ptr (.V (some x)) (m.ptr (.V (some y))))
        .IP (.nat (addr prog p pc + 1 + 1))⟩ = Function.update (vm m) x (vm m y) := by
      funext r
      simp only [vm, Function.update_apply]
      split_ifs with h1 <;> simp_all [ptr_V_eq hd]
    refine ⟨_, ⟨hd', by simpa using hof, hg, .swap2 (u := vm m x) hi ?_ ?_ (vm_mem_cl hd x) ?_
      (hr.of_ret hwf hg (fun u => by simp)) ?_ ?_⟩, .refl⟩
    · simp
    · simp [hV, ptr_V_eq hd]
    · simp only [machine_IP, machine_V, cst, id] at hvm ⊢
      rw [hvm]; simp [Function.update_apply]
    · simp only [machine_IP, machine_V, cst, id] at hvm ⊢
      rw [hvm, Function.update_idem, Function.update_eq_self]; exact hC
    · simp only [machine_IP, machine_V, cst, id] at hvm ⊢
      rw [hvm, Function.update_idem, Function.update_eq_self]; exact hinj
  | @swap2 C OF p pc σ x y u hi hIP hV hu hxy hr hC hinj =>
    have hp : p ∈ used prog := hg.mem_used hwf (p, pc) (by simp)
    have hI := ins_addr prog hp hi (k := 2) (by simp [mlen])
    obtain rfl := exec_assign_inv (A := MM) hIP hI (by simp) hex
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
    refine ⟨⟨swp C x y, OF, (p, pc + 1) :: σ⟩, ⟨hd', by simpa using hof, hg.top,
      .cl (.clean ?_ (hr.of_ret hwf hg (fun u => by simp)).top ?_ ?_)⟩,
      .single (.inl (.swap hi))⟩
    · simp [addr_succ hi, mlen]
    · simp only [machine_IP, machine_V] at hvm ⊢
      rw [hvm, hC]; rfl
    · simp only [machine_IP, machine_V] at hvm ⊢
      rw [hvm]; exact hinj.comp (Equiv.injective _)
  | @det C OF p pc σ x tT tF b hi hIP hCF hb hr hC hinj =>
    have hp : p ∈ used prog := hg.mem_used hwf (p, pc) (by simp)
    have hI := ins_addr prog hp hi (k := 1) (by simp [mlen])
    obtain rfl := exec_jump_inv (A := MM) hIP hI hex
    refine ⟨⟨C, OF, (p, cond b tT tF) :: σ⟩, ⟨hd', by simpa using hof, hg.top,
      .cl (.clean ?_ (hr.of_ret hwf hg (fun u => by simp)).top ?_ ?_)⟩, ?_⟩
    · cases b <;> simp [cj, hCF]
    · rwa [vm_congr (m := m) (fun x => by simp)]
    · rwa [vm_congr (m := m) (fun x => by simp)]
    · cases b
      · exact .single (.inl (.detectF hi))
      · exact .single (.inl (.detectT hi (hb rfl)))
  | @call1 C OF p pc σ q tT tF hi hIP hret hr hC hinj =>
    have hp : p ∈ used prog := hg.mem_used hwf (p, pc) (by simp)
    have hI := ins_addr prog hp hi (k := 1) (by simp [mlen])
    obtain rfl := exec_jump_inv (A := MM) hIP hI hex
    refine ⟨⟨C, OF, (q, 0) :: (p, pc) :: σ⟩, ⟨hd', by simpa using hof, .cons hi hg,
      .cl (.clean ?_ ?_ ?_ ?_)⟩, .single (.inl (.call hi))⟩
    · simp [cst, addr_eq_base]
    · exact ⟨by simpa using hret, hr.of_ret hwf hg (fun u => by simp)⟩
    · rwa [vm_congr (m := m) (fun x => by simp)]
    · rwa [vm_congr (m := m) (fun x => by simp)]
  | @call2 C OF p pc σ q tT tF b hi hIP hCF hr hC hinj =>
    have hp : p ∈ used prog := hg.mem_used hwf (p, cond b tT tF) (by simp)
    have hI := ins_addr prog hp hi (k := 2) (by simp [mlen])
    obtain rfl := exec_jump_inv (A := MM) hIP hI hex
    refine ⟨_, ⟨hd', by simpa using hof, hg,
      .cl (.clean ?_ (hr.of_ret hwf hg (fun u => by simp)) ?_ ?_)⟩, .refl⟩
    · cases b <;> simp [cj, hCF]
    · rwa [vm_congr (m := m) (fun x => by simp)]
    · rwa [vm_congr (m := m) (fun x => by simp)]
  | @ret1 C OF q pc σ b hi hIP hCF hr hC hinj =>
    have hq : q ∈ used prog := hg.mem_used hwf (q, pc) (by simp)
    have hI := ins_addr prog hq hi (k := 1) (by simp [mlen])
    obtain rfl := exec_jump_inv (A := MM) hIP hI hex
    cases σ with
    | nil =>
      have hqm : q = prog.main := by cases hg; rfl
      subst hqm
      refine ⟨_, ⟨hd', by simpa using hof, hg, .cl (.final ?_ hi)⟩, .refl⟩
      simpa [RetOK] using hr
    | cons f σ =>
      obtain ⟨p, pc'⟩ := f
      obtain ⟨tT, tF, hc⟩ : ∃ tT tF, prog.instr p pc' = some (.call q tT tF) := by
        cases hg with
        | cons hc _ => exact ⟨_, _, hc⟩
      have hg' : GoodStk prog ((p, pc') :: σ) := by cases hg with | cons _ h => exact h
      refine ⟨⟨C, OF, (p, cond b tT tF) :: σ⟩, ⟨hd', by simpa using hof, hg'.top,
        .call2 hc ?_ (b := b) ?_ ?_ ?_ ?_⟩, .single (.inl (.ret hi hc))⟩
      · simpa [RetOK] using hr.1
      · simpa using hCF
      · exact (hr.2.of_ret hwf hg' (fun u => by simp)).top
      · rwa [vm_congr (m := m) (fun x => by simp)]
      · rwa [vm_congr (m := m) (fun x => by simp)]
  | @helper s t hIP ht hH hat htot hinj =>
    have hI := ins_hb prog ht
    rcases Nat.lt_or_ge t (4 * (pairs (R := R)).length) with hlt | hge
    · have hj : t / 4 < (pairs (R := R)).length := by omega
      have hvm : ∀ {m' : MCfg prog}, (∀ x, m'.ptr (.V (some x)) = m.ptr (.V (some x))) →
          vm m' = vm m := vm_congr
      rcases (by omega : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3) with hk | hk | hk | hk
      · rw [helperInstr_0 prog hlt hk] at hI
        obtain ⟨u, b, hu, hb, rfl⟩ := exec_detect_inv (A := MM) hIP hI hex
        rw [machine_V, ptr_V_eq hd] at hu
        cases hu
        refine ⟨s, ⟨hd', by simpa using hof, hg, .helper (t := t + 1) (by simp; omega) (by omega)
          ?_ hat ?_ ?_⟩, .refl⟩
        · intro _
          refine ⟨fun _ hCF => ?_, fun h2 => by omega⟩
          simp at hCF; subst hCF
          rw [hvm (fun x => by simp), show (t + 1) / 4 = t / 4 by omega]
          simpa using hb
        · exact htot
        · rwa [hvm (fun x => by simp)]
      · rw [helperInstr_1 prog hlt hk] at hI
        obtain rfl := exec_jump_inv (A := MM) hIP hI hex
        obtain ⟨b, hCF⟩ := bool_of_dom hd
        cases b
        · refine ⟨s, ⟨hd', by simpa using hof, hg, .helper (t := 4 * (t / 4) + 4) ?_ (by omega)
            ?_ hat ?_ ?_⟩, .refl⟩
          · simp [cj, hCF]; omega
          · intro _; exact ⟨fun h => by omega, fun h => by omega⟩
          · exact htot
          · rwa [hvm (fun x => by simp)]
        · refine ⟨s, ⟨hd', by simpa using hof, hg, .helper (t := 4 * (t / 4) + 2) ?_ (by omega)
            ?_ hat ?_ ?_⟩, .refl⟩
          · simp [cj, hCF]; omega
          · intro _
            refine ⟨fun h => by omega, fun _ => ?_⟩
            rw [hvm (fun x => by simp), show (4 * (t / 4) + 2) / 4 = t / 4 by omega]
            exact (hH hlt).1 hk hCF
          · exact htot
          · rwa [hvm (fun x => by simp)]
      · rw [helperInstr_2 prog hlt hk] at hI
        have htot' := exec_total hex
        obtain ⟨u, w, hu, hw, hpos, rfl⟩ := exec_move_inv (A := MM) hIP hI hex
        refine ⟨s, ⟨hd', by simpa using hof, hg, .helper (t := t + 1) (by simp; omega) (by omega)
          ?_ hat ?_ ?_⟩, .refl⟩
        · intro _; exact ⟨fun h => by omega, fun h => by omega⟩
        · rw [htot', htot]
        · rwa [hvm (fun x => by simp)]
      · rw [helperInstr_3 prog hlt hk] at hI
        obtain rfl := exec_jump_inv (A := MM) hIP hI hex
        refine ⟨s, ⟨hd', by simpa using hof, hg, .helper (t := 4 * (t / 4)) ?_ (by omega)
          ?_ hat ?_ ?_⟩, .refl⟩
        · simp [cst]
        · intro _; exact ⟨fun h => by omega, fun h => by omega⟩
        · exact htot
        · rwa [hvm (fun x => by simp)]
    · rw [helperInstr, ite_eq_right (by omega)] at hI
      obtain rfl := exec_jump_inv (A := MM) hIP hI hex
      have hvm : vm ⟨m.reg, Function.update m.ptr (MM).IP (cst (.nat 1) (m.ptr .IP))⟩ = vm m :=
        vm_congr (fun x => by simp)
      refine ⟨⟨view m (vm m), s.OF, [(prog.main, 0)]⟩, ⟨hd', by simpa using hof, .base 0,
        .pre1 ?_ ?_ ?_⟩, .single (.inr (.inl ⟨hat, ?_, rfl, rfl⟩))⟩
      · simp [cst]
      · rw [hvm]; rfl
      · rwa [hvm]
      · rw [total_view hinj, htot]

end Step

end Podc.PPDoubleExpThresholds.ProgramToMachine
