import Papers.PODC2023.PPDoubleExpThresholds.MachineToProtocolElect
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Representation of machine configurations by clean protocol configurations

`Rep c C`: the clean configuration `c` represents the machine configuration `C`, possibly in the
middle of executing an instruction (one constructor per intermediate stage of `⟨move⟩`, `⟨test⟩`,
`⟨pointer⟩`). Each instruction is *committed* (the machine step happens) at one protocol step:
`(V_x)^v_emit, v ↦ (V_x)^v_done, z` for moves, `(V_x)^v_b, CF ↦ (V_x)^v_done, CF^b` for
detections, `X^i_map, Y^v ↦ X^{f(v)}_done, Y^v` for ordinary assignments, and the single step of
the special assignments.

This file also contains the machine-side facts: pointer values stay in their domains (`WF`), the
number of units is invariant, finitely many configurations are reachable, and the reachability
characterization of `Machine.Decides`.
-/

set_option linter.unusedSectionVars false

namespace Podc.PPDoubleExpThresholds

open Cslib Cslib.PopulationProtocol Cslib.TransitionSystem M2P

namespace Machine

variable {Q F : Type*} [Fintype Q] [Fintype F] [DecidableEq Q] [DecidableEq F]
variable (A : Machine Q F)

/-! ### Machine-side facts -/

omit [Fintype F] [DecidableEq F] in
theorem _root_.Podc.PPDoubleExpThresholds.M2P.sum_mvR {r : Q → ℕ} {a : Q}
    (ha : 0 < r a) (b : Q) : ∑ q, mvR r a b q = ∑ q, r q := by
  have := regsM_mvR (F := Unit) (r := r) b ha
  have h2 := congrArg Multiset.card this
  simp only [Multiset.card_add, card_regsM, Multiset.card_singleton] at h2
  omega

theorem instr_some {i : ℕ} {I : MInstr Q F} (h : A.instr i = some I) :
    1 ≤ i ∧ i ≤ A.instrs.length := by
  unfold instr at h
  split_ifs at h with h0
  have := (List.getElem?_eq_some_iff.1 h).1
  omega

theorem mem_dom'_IP {j : ℕ} : Val.nat j ∈ A.dom' A.IP ↔ 1 ≤ j ∧ j ≤ A.instrs.length + 1 := by
  simp [dom']

theorem dom'_of_ne {X : F} (h : X ≠ A.IP) : A.dom' X = A.dom X := by simp [dom', h]

theorem exists_nat_of_mem_dom_IP {v : Val Q} (h : v ∈ A.dom A.IP) :
    ∃ j, v = .nat j ∧ 1 ≤ j ∧ j ≤ A.instrs.length := by
  rw [A.dom_IP, Finset.mem_map] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, rfl, by simpa using ha⟩

theorem mem_dom_IP {j : ℕ} : Val.nat j ∈ A.dom A.IP ↔ 1 ≤ j ∧ j ≤ A.instrs.length := by
  constructor
  · intro h
    obtain ⟨a, ha, h⟩ := A.exists_nat_of_mem_dom_IP h
    cases ha; exact h
  · intro h
    rw [A.dom_IP, Finset.mem_map]
    exact ⟨j, by simpa using h, rfl⟩

/-- Pointer values lie in their (protocol) domains. -/
def WF (C : Cfg Q F) : Prop := ∀ X, C.ptr X ∈ A.dom' X

theorem wf_of_initial {C : Cfg Q F} (h : A.IsInitial C) : A.WF C := by
  intro X
  by_cases hX : X = A.IP
  · subst hX; rw [h.1, A.mem_dom'_IP]; omega
  · rw [A.dom'_of_ne hX]; exact h.2.2 X

theorem mem_dom_of_wf {C : Cfg Q F} (hw : A.WF C) {Y : F} {i : ℕ} {I : MInstr Q F}
    (hi : C.ptr A.IP = .nat i) (hI : A.instr i = some I) : C.ptr Y ∈ A.dom Y := by
  by_cases hY : Y = A.IP
  · subst hY; rw [hi, A.mem_dom_IP]; exact A.instr_some hI
  · have := hw Y; rwa [A.dom'_of_ne hY] at this

theorem exec_wf {C C' : Cfg Q F} (hw : A.WF C) (h : A.Exec C C') : A.WF C' := by
  intro X
  cases h with
  | move hi hI hu hw' hpos =>
    have := A.instr_some hI
    by_cases hX : X = A.IP
    · subst hX; simp [A.mem_dom'_IP]; omega
    · simp only [Function.update_of_ne hX]; exact hw X
  | detect hi hI hu b hb =>
    have := A.instr_some hI
    by_cases hX : X = A.IP
    · subst hX; simp [A.mem_dom'_IP]; omega
    · simp only [Function.update_of_ne hX]
      by_cases hC : X = A.CF
      · subst hC; simp [A.dom'_of_ne A.CF_ne_IP, A.dom_CF]
      · simp only [Function.update_of_ne hC]; exact hw X
  | @assign i X₀ Y₀ f hi hI hX' =>
    have := A.instr_some hI
    by_cases hX : X = A.IP
    · subst hX; simp [A.mem_dom'_IP]; omega
    · simp only [Function.update_of_ne hX]
      by_cases hXX : X = X₀
      · subst hXX; simp only [Function.update_self, A.dom'_of_ne hX]
        exact A.assign_mem _ _ _ (List.mem_of_getElem? (by
          unfold instr at hI; split_ifs at hI; exact hI)) _ (A.mem_dom_of_wf hw hi hI)
      · simp only [Function.update_of_ne hXX]; exact hw X
  | jump hi hI =>
    by_cases hX : X = A.IP
    · subst hX; simp only [Function.update_self]
      have := A.assign_mem _ _ _ (List.mem_of_getElem? (by
          unfold instr at hI; split_ifs at hI; exact hI)) _ (A.mem_dom_of_wf hw hi hI)
      obtain ⟨j, hj, h1, h2⟩ := A.exists_nat_of_mem_dom_IP this
      rw [hj, A.mem_dom'_IP]; omega
    · simp only [Function.update_of_ne hX]; exact hw X

theorem exec_total {C C' : Cfg Q F} (h : A.Exec C C') : total C' = total C := by
  cases h with
  | move hi hI hu hw hpos =>
    exact sum_mvR hpos _
  | detect => rfl
  | assign => rfl
  | jump => rfl

theorem step_wf {C C' : Cfg Q F} (hw : A.WF C) (h : A.Step C C') : A.WF C' := by
  rcases h with h | ⟨rfl, -⟩
  · exact A.exec_wf hw h
  · exact hw

theorem step_total {C C' : Cfg Q F} (h : A.Step C C') : total C' = total C := by
  rcases h with h | ⟨rfl, -⟩
  · exact A.exec_total h
  · rfl

theorem reach_wf {C C' : Cfg Q F} (hw : A.WF C) (h : Reach A.Step C C') : A.WF C' := by
  induction h with
  | refl => exact hw
  | tail _ hs ih => exact A.step_wf ih hs

theorem reach_total {C C' : Cfg Q F} (h : Reach A.Step C C') : total C' = total C := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (A.step_total hs).trans ih

theorem reach_finite {C₀ : Cfg Q F} (hw : A.WF C₀) : {C | Reach A.Step C₀ C}.Finite := by
  let T1 : Set (Q → ℕ) := Set.pi Set.univ (fun _ => Set.Iic (total C₀))
  let T2 : Set (F → Val Q) := Set.pi Set.univ (fun X => (A.dom' X : Set (Val Q)))
  have h1 : T1.Finite := Set.Finite.pi (fun _ => Set.finite_Iic _)
  have h2 : T2.Finite := Set.Finite.pi (fun X => (A.dom' X).finite_toSet)
  refine ((h1.prod h2).image (fun p => (⟨p.1, p.2⟩ : Cfg Q F))).subset ?_
  intro C hC
  refine ⟨(C.reg, C.ptr), ⟨?_, ?_⟩, rfl⟩
  · intro q _
    have := A.reach_total hC
    simp only [Set.mem_Iic]
    rw [← this]; unfold total
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  · intro X _; exact A.reach_wf hw hC X

theorem step_total_rel (C : Cfg Q F) : ∃ C', A.Step C C' := by
  by_cases h : ∃ C', A.Exec C C' ∧ C' ≠ C
  · obtain ⟨C', h1, -⟩ := h; exact ⟨C', .inl h1⟩
  · push Not at h; exact ⟨C, .inr ⟨rfl, h⟩⟩

/-- Reachability form of `Machine.Decides`. -/
theorem reach_stable_of_decides {φ : ℕ → Bool} (hA : A.Decides φ) {C₀ : Cfg Q F}
    (h0 : A.IsInitial C₀) :
    ∀ C, Reach A.Step C₀ C → ∃ C', Reach A.Step C C' ∧ StableOut A.Step A.out (φ (total C₀)) C' :=
  reach_stable_of_forall_fair (A.reach_finite (A.wf_of_initial h0))
    (fun x _ => A.step_total_rel x) (fun E hE0 hE => by
      have := hA E (hE0 ▸ h0) hE; rwa [hE0] at this)

/-! ### Simp lemmas for the special pointers -/

@[simp] theorem IP_ne_V (x : Option Q) : A.IP ≠ A.V x := (A.V_ne_IP x).symm
@[simp] theorem V_ne_IP' (x : Option Q) : A.V x ≠ A.IP := A.V_ne_IP x
@[simp] theorem CF_ne_V (x : Option Q) : A.CF ≠ A.V x := (A.V_ne_CF x).symm
@[simp] theorem V_ne_CF' (x : Option Q) : A.V x ≠ A.CF := A.V_ne_CF x
@[simp] theorem OF_ne_V (x : Option Q) : A.OF ≠ A.V x := (A.V_ne_OF x).symm
@[simp] theorem V_ne_OF' (x : Option Q) : A.V x ≠ A.OF := A.V_ne_OF x
@[simp] theorem CF_ne_IP' : A.CF ≠ A.IP := A.CF_ne_IP
@[simp] theorem IP_ne_CF : A.IP ≠ A.CF := A.CF_ne_IP.symm
@[simp] theorem OF_ne_IP' : A.OF ≠ A.IP := A.OF_ne_IP
@[simp] theorem IP_ne_OF : A.IP ≠ A.OF := A.OF_ne_IP.symm
@[simp] theorem V_eq_V_iff {x y : Option Q} : A.V x = A.V y ↔ x = y := A.V_inj.eq_iff

/-! ### Clean configurations with an instruction in progress -/

/-- All pointer agents in stage `none`, with the values of `C`. -/
def idleG (C : Cfg Q F) : F → St Q F := fun X => .ptr X (C.ptr X) .none

/-- `IP^i_wait`, and `Z` in state `s`; all others idle. -/
def gW (C : Cfg Q F) (i : ℕ) (Z : F) (s : St Q F) : F → St Q F :=
  Function.update (Function.update (idleG C) A.IP (.ptr A.IP (.nat i) .wait)) Z s

/-- `IP^i_half`; all others idle. -/
def gH (C : Cfg Q F) (i : ℕ) : F → St Q F :=
  Function.update (idleG C) A.IP (.ptr A.IP (.nat i) .half)

theorem pi_eq (C : Cfg Q F) : pi C = render C.reg (idleG C) := rfl

theorem ownerResp_idleG (C : Cfg Q F) : OwnerResp (idleG C) := fun _ => rfl

theorem ownerResp_gW (C : Cfg Q F) (i : ℕ) {Z : F} {s : St Q F} (hs : s.owner = some Z) :
    OwnerResp (A.gW C i Z s) := by
  intro X
  simp only [gW, Function.update_apply]
  split_ifs with h1 h2
  · subst h1; exact hs
  · subst h2; rfl
  · rfl

theorem ownerResp_gH (C : Cfg Q F) (i : ℕ) : OwnerResp (A.gH C i) := by
  intro X
  simp only [gH, Function.update_apply]
  split_ifs with h1
  · subst h1; rfl
  · rfl

/-- The representation relation between clean protocol configurations and machine
configurations (with the instruction in progress). -/
inductive Rep : Multiset (St Q F) → Cfg Q F → Prop
  | idle {C : Cfg Q F} (hw : A.WF C) : Rep (pi C) C
  | mvEmit {C : Cfg Q F} {i : ℕ} {x y u : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat i)
      (hI : A.instr i = some (.move x y)) (hu : C.ptr (A.V (some x)) = .reg u) :
      Rep (render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .emit))) C
  | mvDone {C : Cfg Q F} {i : ℕ} {x y u w : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat (i + 1))
      (hI : A.instr i = some (.move x y)) (hu : C.ptr (A.V (some x)) = .reg u)
      (hw' : C.ptr (A.V (some y)) = .reg w) (hpos : 0 < C.reg w) :
      Rep (render (mvR C.reg w A.z0)
        (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .done))) C
  | mvHalf {C : Cfg Q F} {i : ℕ} {x y w : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat (i + 1))
      (hI : A.instr i = some (.move x y)) (hw' : C.ptr (A.V (some y)) = .reg w)
      (hpos : 0 < C.reg w) :
      Rep (render (mvR C.reg w A.z0) (A.gH C i)) C
  | mvTake {C : Cfg Q F} {i : ℕ} {x y w : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat (i + 1))
      (hI : A.instr i = some (.move x y)) (hw' : C.ptr (A.V (some y)) = .reg w)
      (hpos : 0 < C.reg w) :
      Rep (render (mvR C.reg w A.z0)
        (A.gW C i (A.V (some y)) (.ptr (A.V (some y)) (.reg w) .take))) C
  | mvFin {C : Cfg Q F} {i : ℕ} {x y w : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat (i + 1))
      (hI : A.instr i = some (.move x y)) (hw' : C.ptr (A.V (some y)) = .reg w) :
      Rep (render C.reg (A.gW C i (A.V (some y)) (.ptr (A.V (some y)) (.reg w) .done))) C
  | tsTest {C : Cfg Q F} {i : ℕ} {x u : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat i)
      (hI : A.instr i = some (.detect x)) (hu : C.ptr (A.V (some x)) = .reg u) :
      Rep (render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .test))) C
  | tsRes {C : Cfg Q F} {i : ℕ} {x u : Q} {b : Bool} (hw : A.WF C) (hi : C.ptr A.IP = .nat i)
      (hI : A.instr i = some (.detect x)) (hu : C.ptr (A.V (some x)) = .reg u)
      (hb : b = true → 0 < C.reg u) :
      Rep (render C.reg (A.gW C i (A.V (some x))
        (.ptr (A.V (some x)) (.reg u) (if b then .tt else .ff)))) C
  | tsFin {C : Cfg Q F} {i : ℕ} {x u : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat (i + 1))
      (hI : A.instr i = some (.detect x)) (hu : C.ptr (A.V (some x)) = .reg u) :
      Rep (render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .done))) C
  | asMap {C : Cfg Q F} {i : ℕ} {X Y : F} {f : Val Q → Val Q} (hw : A.WF C)
      (hi : C.ptr A.IP = .nat i) (hI : A.instr i = some (.assign X Y f)) (hXY : X ≠ Y)
      (hX : X ≠ A.IP) (hY : Y ≠ A.IP) :
      Rep (render C.reg (A.gW C i X (.map X i))) C
  | asFin {C : Cfg Q F} {i : ℕ} {X Y : F} {f : Val Q → Val Q} (hw : A.WF C)
      (hi : C.ptr A.IP = .nat (i + 1)) (hI : A.instr i = some (.assign X Y f)) (hXY : X ≠ Y)
      (hX : X ≠ A.IP) (hY : Y ≠ A.IP) :
      Rep (render C.reg (A.gW C i X (.ptr X (C.ptr X) .done))) C

end Machine

end Podc.PPDoubleExpThresholds
