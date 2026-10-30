import Papers.PODC2023.PPDoubleExpThresholds.MachineToProtocolFire

/-!
# Backward simulation: every protocol step from a clean configuration is a machine step

`rep_step`: if `Rep c C` and `c → c'` then `Rep c' C'` for some `C'` with `C →* C'` (at most one
machine step). Every transition enabled at a clean configuration is the one expected by the stage
of the instruction in progress (or the commit step).
-/

set_option linter.unusedSectionVars false

namespace Podc.PPDoubleExpThresholds

open Cslib Cslib.PopulationProtocol Cslib.TransitionSystem M2P

namespace Machine

variable {Q F : Type*} [Fintype Q] [Fintype F] [DecidableEq Q] [DecidableEq F]
variable (A : Machine Q F)

/-- `clean_fires`, indexed by the pointer of the first agent. -/
theorem clean_fires' {r : Q → ℕ} {g : F → St Q F} (hg : OwnerResp g) {t : Transition (St Q F)}
    (ht : A.Tr t) {c' : Multiset (St Q F)} (hf : t.Fires (render r g) c') {X : F}
    (hX : t.p.owner = some X) :
    t.p = g X ∧
      (∀ Y, t.q.owner = some Y → Y ≠ X ∧ t.q = g Y ∧
        c' = render r (Function.update (Function.update g X t.p') Y t.q')) ∧
      (∀ u, t.q = .reg u → ∃ u', t.q' = .reg u' ∧ 0 < r u ∧
        c' = render (mvR r u u') (Function.update g X t.p')) := by
  obtain ⟨X₀, hp, h⟩ := A.clean_fires hg ht hf
  have hX₀ : X₀ = X := by
    have := hg X₀; rw [← hp, hX] at this; exact (Option.some_injective _ this).symm
  subst hX₀
  refine ⟨hp, fun Y hY => ?_, fun u hu => ?_⟩
  · rcases h with ⟨Y₀, hne, hq, hc⟩ | ⟨u, u', hq, -, -, -⟩
    · have : Y₀ = Y := by
        have := hg Y₀; rw [← hq, hY] at this; exact (Option.some_injective _ this).symm
      subst this; exact ⟨hne, hq, hc⟩
    · rw [hq] at hY; simp at hY
  · rcases h with ⟨Y₀, -, hq, -⟩ | ⟨u₀, u', hq, hq', hpos, hc⟩
    · have := hg Y₀; rw [← hq, hu] at this; simp at this
    · rw [hq] at hu; cases hu; exact ⟨u', hq', hpos, hc⟩

/-- In a clean configuration, a transition whose partner `q` is unchanged (`q' = q`) only
changes the first agent. -/
theorem clean_fires_fixq {r : Q → ℕ} {g : F → St Q F} (hg : OwnerResp g)
    {t : Transition (St Q F)} (ht : A.Tr t) {c' : Multiset (St Q F)}
    (hf : t.Fires (render r g) c') {X : F} (hX : t.p.owner = some X) (hqq : t.q' = t.q) :
    t.p = g X ∧ c' = render r (Function.update g X t.p') := by
  obtain ⟨hp, hY, hu⟩ := A.clean_fires' hg ht hf hX
  refine ⟨hp, ?_⟩
  cases hq : t.q with
  | reg u =>
    obtain ⟨u', hu', hpos, hc⟩ := hu u hq
    rw [hqq, hq] at hu'; cases hu'
    rw [hc, mvR_self hpos]
  | ptr Y v s =>
    obtain ⟨hne, hq', hc⟩ := hY Y (by rw [hq]; rfl)
    rw [hc, hqq, hq']
    congr 1
    conv_lhs => rw [show g Y = Function.update g X t.p' Y from (Function.update_of_ne hne ..).symm]
    exact Function.update_eq_self _ _
  | map Y j =>
    obtain ⟨hne, hq', hc⟩ := hY Y (by rw [hq]; rfl)
    rw [hc, hqq, hq']
    congr 1
    conv_lhs => rw [show g Y = Function.update g X t.p' Y from (Function.update_of_ne hne ..).symm]
    exact Function.update_eq_self _ _

/-- In a clean configuration, the two agents of a transition belong to different pointers. -/
theorem clean_owner_ne {r : Q → ℕ} {g : F → St Q F} (hg : OwnerResp g)
    {t : Transition (St Q F)} (ht : A.Tr t) {c' : Multiset (St Q F)}
    (hf : t.Fires (render r g) c') (h : t.p.owner = t.q.owner) : False := by
  obtain ⟨⟨X, hX⟩, -⟩ := Tr.shape A ht
  obtain ⟨-, hY, -⟩ := A.clean_fires' hg ht hf hX
  exact (hY X (h ▸ hX)).1 rfl

set_option hygiene false in
/-- Dismiss a transition that cannot fire in a clean configuration of a given stage. -/
macro "kill_bk" : tactic => `(tactic| first
  | (exfalso; apply A.clean_owner_ne hg ht' hf; simp_all; done)
  | (obtain ⟨hp, -, -⟩ := A.clean_fires' hg ht' hf rfl
     simp only [gW, gH, Function.update_apply, idleG] at hp
     split_ifs at hp <;> first | (simp at hp; done) | (simp_all; done))
  | (obtain ⟨-, hY, -⟩ := A.clean_fires' hg ht' hf rfl
     obtain ⟨-, hq, -⟩ := hY _ rfl
     simp only [gW, gH, Function.update_apply, idleG] at hq
     split_ifs at hq <;> first | (simp at hq; done) | (simp_all; done))
  | (obtain ⟨hp, hY, -⟩ := A.clean_fires' hg ht' hf rfl
     obtain ⟨-, hq, -⟩ := hY _ rfl
     simp only [gW, gH, Function.update_apply, idleG] at hp hq
     split_ifs at hp hq <;> simp_all; done))

theorem move_ne' {i : ℕ} {x y : Q} (hI : A.instr i = some (.move x y)) : x ≠ y :=
  A.move_ne x y (List.mem_of_getElem? (by unfold instr at hI; split_ifs at hI; exact hI))

theorem ptr_V_reg {C : Cfg Q F} (hw : A.WF C) (x : Option Q) : ∃ u, C.ptr (A.V x) = .reg u := by
  have := hw (A.V x); rw [A.dom'_of_ne (A.V_ne_IP x)] at this
  exact A.dom_V x _ this

theorem rep_idle_step {C : Cfg Q F} (hw : A.WF C) {t : Transition (St Q F)} (ht : A.Tr t)
    {c' : Multiset (St Q F)} (hf : t.Fires (pi C) c') :
    ∃ C', A.Rep c' C' ∧ Reach A.Step C C' := by
  have hg := ownerResp_idleG (Q := Q) C
  cases ht with
  | elect hX ha hb =>
    obtain ⟨-, hY, -⟩ := A.clean_fires' hg (.elect hX ha hb) hf ha
    exact absurd rfl (hY _ hb).1
  | electIP ha hb =>
    obtain ⟨-, hY, -⟩ := A.clean_fires' hg (.electIP ha hb) hf ha
    exact absurd rfl (hY _ hb).1
  | mvStart hI hv =>
    obtain ⟨hp, hY, -⟩ := A.clean_fires' hg (.mvStart hI hv) hf rfl
    obtain ⟨-, hq, rfl⟩ := hY _ rfl
    simp only [idleG, St.ptr.injEq, true_and] at hp hq
    obtain ⟨hi, -⟩ := hp; obtain ⟨hv', rfl⟩ := hq
    obtain ⟨u, hu⟩ := A.ptr_V_reg hw (some _)
    rw [hu] at hv'; subst hv'
    exact ⟨C, .mvEmit hw hi.symm hI hu, .refl⟩
  | tsStart hI hv =>
    obtain ⟨hp, hY, -⟩ := A.clean_fires' hg (.tsStart hI hv) hf rfl
    obtain ⟨-, hq, rfl⟩ := hY _ rfl
    simp only [idleG, St.ptr.injEq, true_and] at hp hq
    obtain ⟨hi, -⟩ := hp; obtain ⟨hv', rfl⟩ := hq
    obtain ⟨u, hu⟩ := A.ptr_V_reg hw (some _)
    rw [hu] at hv'; subst hv'
    exact ⟨C, .tsTest hw hi.symm hI hu, .refl⟩
  | asStart hI hXY hX hY =>
    obtain ⟨hp, hY', -⟩ := A.clean_fires' hg (.asStart hI hXY hX hY) hf rfl
    obtain ⟨-, hq, rfl⟩ := hY' _ rfl
    simp only [idleG, St.ptr.injEq, true_and] at hp hq
    exact ⟨C, .asMap hw hp.1.symm hI hXY hX hY, .refl⟩
  | jmp hI hY hv =>
    obtain ⟨hp, hY', -⟩ := A.clean_fires' hg (.jmp hI hY hv) hf rfl
    obtain ⟨-, hq, -⟩ := hY' _ rfl
    simp only [idleG, St.ptr.injEq, true_and] at hp hq
    obtain ⟨hv', rfl⟩ := hq; subst hv'
    have hi := hp.1.symm
    rw [fires_unique hf (A.fire_jmp hi hY)]
    have hE := Exec.jump hi hI
    exact ⟨_, .idle (A.exec_wf hw hE), .single (.inl hE)⟩
  | asSelf hI hY hv =>
    obtain ⟨hp, hY', -⟩ := A.clean_fires' hg (.asSelf hI hY hv) hf rfl
    obtain ⟨-, hq, -⟩ := hY' _ rfl
    simp only [idleG, St.ptr.injEq, true_and] at hp hq
    obtain ⟨hv', rfl⟩ := hq; subst hv'
    have hi := hp.1.symm
    rw [fires_unique hf (A.fire_asSelf hi hY)]
    have hE := Exec.assign hi hI hY
    exact ⟨_, .idle (A.exec_wf hw hE), .single (.inl hE)⟩
  | asIP hI hX =>
    obtain ⟨hp, hY', -⟩ := A.clean_fires' hg (.asIP hI hX) hf rfl
    obtain ⟨-, hq, -⟩ := hY' _ rfl
    simp only [idleG, St.ptr.injEq, true_and] at hp hq
    obtain ⟨hv', rfl⟩ := hq; subst hv'
    have hi := hp.1.symm
    rw [fires_unique hf (A.fire_asIP hi hX)]
    have hE := Exec.assign hi hI hX
    exact ⟨_, .idle (A.exec_wf hw hE), .single (.inl hE)⟩
  | @jmpIP i f q hI =>
    obtain ⟨hp, hc⟩ := A.clean_fires_fixq hg (.jmpIP hI) hf rfl rfl
    simp only [idleG, St.ptr.injEq, true_and] at hp
    have hi := hp.1.symm
    have hE := Exec.jump hi hI
    refine ⟨_, ?_, .single (.inl hE)⟩
    rw [hc]
    have : Function.update (idleG C) A.IP (.ptr A.IP (f (.nat i)) .none) =
        idleG ⟨C.reg, Function.update C.ptr A.IP (f (C.ptr A.IP))⟩ := by
      rw [idleG_update, hi]
    rw [this]
    exact .idle (A.exec_wf hw hE)
  | mvEmit hI hv =>
    obtain ⟨hp, -⟩ := A.clean_fires' hg (.mvEmit hI hv) hf rfl; simp [idleG] at hp
  | mvHalf hI hv =>
    obtain ⟨hp, -⟩ := A.clean_fires' hg (.mvHalf hI hv) hf rfl; simp [idleG] at hp
  | mvTake hI hv =>
    obtain ⟨hp, -⟩ := A.clean_fires' hg (.mvTake hI hv) hf rfl; simp [idleG] at hp
  | mvPut hI hv =>
    obtain ⟨hp, -⟩ := A.clean_fires' hg (.mvPut hI hv) hf rfl; simp [idleG] at hp
  | mvEnd hI hv =>
    obtain ⟨hp, -⟩ := A.clean_fires' hg (.mvEnd hI hv) hf rfl; simp [idleG] at hp
  | tsYes hI hv =>
    obtain ⟨hp, -⟩ := A.clean_fires' hg (.tsYes hI hv) hf rfl; simp [idleG] at hp
  | tsNo hI hv hq =>
    obtain ⟨hp, -⟩ := A.clean_fires' hg (.tsNo hI hv hq) hf rfl; simp [idleG] at hp
  | tsSet b hI hv =>
    obtain ⟨hp, -⟩ := A.clean_fires' hg (.tsSet b hI hv) hf rfl; cases b <;> simp [idleG] at hp
  | tsEnd hI hv =>
    obtain ⟨hp, -⟩ := A.clean_fires' hg (.tsEnd hI hv) hf rfl; simp [idleG] at hp
  | asMap hI hXY hX hY hv =>
    obtain ⟨hp, -⟩ := A.clean_fires' hg (.asMap hI hXY hX hY hv) hf rfl; simp [idleG] at hp
  | asEnd hI hXY hX hY hv =>
    obtain ⟨hp, -⟩ := A.clean_fires' hg (.asEnd hI hXY hX hY hv) hf rfl; simp [idleG] at hp

theorem rep_mvEmit_step {C : Cfg Q F} {i : ℕ} {x y u : Q} (hw : A.WF C)
    (hi : C.ptr A.IP = .nat i) (hI : A.instr i = some (.move x y))
    (hu : C.ptr (A.V (some x)) = .reg u) {t : Transition (St Q F)} (ht : A.Tr t)
    {c' : Multiset (St Q F)}
    (hf : t.Fires (render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .emit))) c') :
    ∃ C', A.Rep c' C' ∧ Reach A.Step C C' := by
  have hg := A.ownerResp_gW C i (s := .ptr (A.V (some x)) (.reg u) .emit) rfl
  have hxy := A.move_ne' hI
  have ht' := ht
  cases ht
  case mvEmit j x' y' u' hI' hv =>
    obtain ⟨hp, -, hU⟩ := A.clean_fires' hg ht' hf rfl
    simp only [gW, Function.update_apply, idleG] at hp
    split_ifs at hp with h1 h2
    · simp only [V_eq_V_iff, Option.some_inj] at h1; subst h1
      simp only [St.ptr.injEq, Val.reg.injEq, true_and] at hp; obtain ⟨rfl, -⟩ := hp
      obtain ⟨-, -, hpos, -⟩ := hU _ rfl
      obtain ⟨w, hw'⟩ := A.ptr_V_reg hw (some y)
      rw [fires_unique hf (A.fire_mvEmit hi hu hpos w)]
      have hE := Exec.move hi hI hu hw' hpos
      refine ⟨_, .mvDone (A.exec_wf hw hE) (by simp) hI (by simp [hu]) (by simp [hw'])
        pos_mvR, .single (.inl hE)⟩
    · simp at h2
    · simp at hp
  all_goals kill_bk

section phases

variable {C : Cfg Q F} {i : ℕ} {t : Transition (St Q F)} {c' : Multiset (St Q F)}

theorem rep_mvDone_step {x y u w : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat (i + 1))
    (hI : A.instr i = some (.move x y)) (hu : C.ptr (A.V (some x)) = .reg u)
    (hw' : C.ptr (A.V (some y)) = .reg w) (hpos : 0 < C.reg w) (ht : A.Tr t)
    (hf : t.Fires (render (mvR C.reg w A.z0)
      (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .done))) c') :
    ∃ C', A.Rep c' C' ∧ Reach A.Step C C' := by
  have hg := A.ownerResp_gW C i (s := .ptr (A.V (some x)) (.reg u) .done) rfl
  have hxy := A.move_ne' hI
  have ht' := ht
  cases ht
  case mvHalf j x' y' v hI' hv =>
    obtain ⟨hp, hY, -⟩ := A.clean_fires' hg ht' hf rfl
    obtain ⟨-, hq, -⟩ := hY _ rfl
    simp only [gW, gH, Function.update_apply, idleG, IP_ne_V, V_ne_IP', if_true, if_false, St.ptr.injEq, Val.nat.injEq, true_and, and_true, V_eq_V_iff, Option.some_inj, ite_true, ite_false, reduceIte] at hp; subst hp
    rw [hI] at hI'; simp only [Option.some.injEq, MInstr.move.injEq] at hI'
    obtain ⟨rfl, rfl⟩ := hI'
    simp only [gW, gH, Function.update_apply, idleG, IP_ne_V, V_ne_IP', if_true, if_false, St.ptr.injEq, Val.nat.injEq, true_and, and_true, V_eq_V_iff, Option.some_inj, ite_true, ite_false, reduceIte] at hq; subst hq
    rw [fires_unique hf (A.fire_mvHalf hu)]
    exact ⟨C, .mvHalf hw hi hI hw' hpos, .refl⟩
  case mvEnd j x' y' v hI' hv =>
    exfalso
    obtain ⟨hp, hY, -⟩ := A.clean_fires' hg ht' hf rfl
    obtain ⟨-, hq, -⟩ := hY _ rfl
    simp only [gW, gH, Function.update_apply, idleG, IP_ne_V, V_ne_IP', if_true, if_false, St.ptr.injEq, Val.nat.injEq, true_and, and_true, V_eq_V_iff, Option.some_inj, ite_true, ite_false, reduceIte] at hp; subst hp
    rw [hI] at hI'; simp only [Option.some.injEq, MInstr.move.injEq] at hI'
    obtain ⟨rfl, rfl⟩ := hI'
    simp only [gW, Function.update_apply, V_eq_V_iff, Option.some_inj, if_neg (Ne.symm hxy),
      V_ne_IP', if_false, idleG] at hq
    simp at hq
  all_goals kill_bk

theorem rep_mvHalf_step {x y w : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat (i + 1))
    (hI : A.instr i = some (.move x y)) (hw' : C.ptr (A.V (some y)) = .reg w)
    (hpos : 0 < C.reg w) (ht : A.Tr t)
    (hf : t.Fires (render (mvR C.reg w A.z0) (A.gH C i)) c') :
    ∃ C', A.Rep c' C' ∧ Reach A.Step C C' := by
  have hg := A.ownerResp_gH C i
  have hxy := A.move_ne' hI
  have ht' := ht
  cases ht
  case mvTake j x' y' v s hI' hv =>
    obtain ⟨hp, hY, -⟩ := A.clean_fires' hg ht' hf rfl
    obtain ⟨-, hq, -⟩ := hY _ rfl
    simp only [gW, gH, Function.update_apply, idleG, IP_ne_V, V_ne_IP', if_true, if_false, St.ptr.injEq, Val.nat.injEq, true_and, and_true, V_eq_V_iff, Option.some_inj, ite_true, ite_false, reduceIte] at hp; subst hp
    rw [hI] at hI'; simp only [Option.some.injEq, MInstr.move.injEq] at hI'
    obtain ⟨rfl, rfl⟩ := hI'
    simp only [gW, gH, Function.update_apply, idleG, IP_ne_V, V_ne_IP', if_true, if_false, St.ptr.injEq, Val.nat.injEq, true_and, and_true, V_eq_V_iff, Option.some_inj, ite_true, ite_false, reduceIte] at hq; obtain ⟨hv', rfl⟩ := hq; rw [hw'] at hv'; subst hv'
    rw [fires_unique hf (A.fire_mvTake hw')]
    exact ⟨C, .mvTake hw hi hI hw' hpos, .refl⟩
  all_goals kill_bk

theorem rep_mvTake_step {x y w : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat (i + 1))
    (hI : A.instr i = some (.move x y)) (hw' : C.ptr (A.V (some y)) = .reg w)
    (hpos : 0 < C.reg w) (ht : A.Tr t)
    (hf : t.Fires (render (mvR C.reg w A.z0)
      (A.gW C i (A.V (some y)) (.ptr (A.V (some y)) (.reg w) .take))) c') :
    ∃ C', A.Rep c' C' ∧ Reach A.Step C C' := by
  have hg := A.ownerResp_gW C i (s := .ptr (A.V (some y)) (.reg w) .take) rfl
  have hxy := A.move_ne' hI
  have ht' := ht
  cases ht
  case mvPut j x' y' u' hI' hv =>
    obtain ⟨hp, -, -⟩ := A.clean_fires' hg ht' hf rfl
    simp only [gW, gH, Function.update_apply, idleG, IP_ne_V, V_ne_IP', if_true, if_false, St.ptr.injEq, Val.nat.injEq, true_and, and_true, V_eq_V_iff, Option.some_inj, ite_true, ite_false, reduceIte] at hp
    split_ifs at hp with h1
    · subst h1; simp only [St.ptr.injEq, Val.reg.injEq, true_and] at hp
      obtain ⟨rfl, -⟩ := hp
      rw [fires_unique hf (A.fire_mvPut hpos)]
      exact ⟨C, .mvFin hw hi hI hw', .refl⟩
    · simp at hp
  all_goals kill_bk

theorem rep_mvFin_step {x y w : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat (i + 1))
    (hI : A.instr i = some (.move x y)) (hw' : C.ptr (A.V (some y)) = .reg w) (ht : A.Tr t)
    (hf : t.Fires (render C.reg
      (A.gW C i (A.V (some y)) (.ptr (A.V (some y)) (.reg w) .done))) c') :
    ∃ C', A.Rep c' C' ∧ Reach A.Step C C' := by
  have hg := A.ownerResp_gW C i (s := .ptr (A.V (some y)) (.reg w) .done) rfl
  have ht' := ht
  have hxy := A.move_ne' hI
  cases ht
  case mvEnd j x' y' v hI' hv =>
    obtain ⟨hp, hY, -⟩ := A.clean_fires' hg ht' hf rfl
    obtain ⟨-, hq, -⟩ := hY _ rfl
    simp only [gW, gH, Function.update_apply, idleG, IP_ne_V, V_ne_IP', if_true, if_false, St.ptr.injEq, Val.nat.injEq, true_and, and_true, V_eq_V_iff, Option.some_inj, ite_true, ite_false, reduceIte] at hp; subst hp
    rw [hI] at hI'; simp only [Option.some.injEq, MInstr.move.injEq] at hI'
    obtain ⟨rfl, rfl⟩ := hI'
    simp only [gW, gH, Function.update_apply, idleG, IP_ne_V, V_ne_IP', if_true, if_false, St.ptr.injEq, Val.nat.injEq, true_and, and_true, V_eq_V_iff, Option.some_inj, ite_true, ite_false, reduceIte] at hq; subst hq
    rw [fires_unique hf (A.fire_mvEnd hi hw')]
    exact ⟨C, .idle hw, .refl⟩
  case mvHalf j x' y' v hI' hv =>
    exfalso
    obtain ⟨hp, hY, -⟩ := A.clean_fires' hg ht' hf rfl
    obtain ⟨-, hq, -⟩ := hY _ rfl
    simp only [gW, gH, Function.update_apply, idleG, IP_ne_V, V_ne_IP', if_true, if_false, St.ptr.injEq, Val.nat.injEq, true_and, and_true, V_eq_V_iff, Option.some_inj, ite_true, ite_false, reduceIte] at hp; subst hp
    rw [hI] at hI'; simp only [Option.some.injEq, MInstr.move.injEq] at hI'
    obtain ⟨rfl, rfl⟩ := hI'
    simp only [gW, Function.update_apply, V_eq_V_iff, Option.some_inj, if_neg hxy,
      V_ne_IP', if_false, idleG] at hq
    simp at hq
  all_goals kill_bk

theorem rep_tsTest_step {x u : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat i)
    (hI : A.instr i = some (.detect x)) (hu : C.ptr (A.V (some x)) = .reg u) (ht : A.Tr t)
    (hf : t.Fires (render C.reg
      (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .test))) c') :
    ∃ C', A.Rep c' C' ∧ Reach A.Step C C' := by
  have hg := A.ownerResp_gW C i (s := .ptr (A.V (some x)) (.reg u) .test) rfl
  have ht' := ht
  cases ht
  case tsYes j x' u' hI' hv =>
    obtain ⟨hp, -, hU⟩ := A.clean_fires' hg ht' hf rfl
    simp only [gW, gH, Function.update_apply, idleG, IP_ne_V, V_ne_IP', if_true, if_false, St.ptr.injEq, Val.nat.injEq, true_and, and_true, V_eq_V_iff, Option.some_inj, ite_true, ite_false, reduceIte] at hp
    split_ifs at hp with h1
    · subst h1; simp only [St.ptr.injEq, Val.reg.injEq, true_and] at hp
      obtain ⟨rfl, -⟩ := hp
      obtain ⟨-, -, hpos, -⟩ := hU _ rfl
      rw [fires_unique hf (A.fire_tsYes hpos)]
      exact ⟨C, .tsRes hw hi hI hu (fun _ => hpos), .refl⟩
    · simp at hp
  case tsNo j x' u' q hI' hv hq =>
    obtain ⟨hp, hc⟩ := A.clean_fires_fixq hg ht' hf rfl rfl
    simp only [gW, gH, Function.update_apply, idleG, IP_ne_V, V_ne_IP', if_true, if_false, St.ptr.injEq, Val.nat.injEq, true_and, and_true, V_eq_V_iff, Option.some_inj, ite_true, ite_false, reduceIte] at hp
    split_ifs at hp with h1
    · subst h1; simp only [St.ptr.injEq, Val.reg.injEq, true_and] at hp
      obtain ⟨rfl, -⟩ := hp
      rw [hc]
      refine ⟨C, ?_, .refl⟩
      convert Rep.tsRes (A := A) (b := false) hw hi hI hu (by simp) using 2
      simp only [gW, Function.update_idem]; rfl
    · simp at hp
  all_goals kill_bk

theorem rep_tsRes_step {x u : Q} {b : Bool} (hw : A.WF C) (hi : C.ptr A.IP = .nat i)
    (hI : A.instr i = some (.detect x)) (hu : C.ptr (A.V (some x)) = .reg u)
    (hb : b = true → 0 < C.reg u) (ht : A.Tr t)
    (hf : t.Fires (render C.reg (A.gW C i (A.V (some x))
      (.ptr (A.V (some x)) (.reg u) (if b then .tt else .ff)))) c') :
    ∃ C', A.Rep c' C' ∧ Reach A.Step C C' := by
  have hg := A.ownerResp_gW C i (s := .ptr (A.V (some x)) (.reg u) (if b then .tt else .ff)) rfl
  have ht' := ht
  cases ht
  case tsSet j x' v w s b' hI' hv =>
    obtain ⟨hp, hY, -⟩ := A.clean_fires' hg ht' hf rfl
    obtain ⟨-, hq, -⟩ := hY _ rfl
    by_cases hx : x' = x
    · subst hx
      have hbb : b' = b ∧ v = .reg u := by
        simp only [gW, Function.update_apply, if_pos rfl, St.ptr.injEq, true_and] at hp
        cases b <;> cases b' <;> simp_all
      obtain ⟨hbb1, rfl⟩ := hbb
      subst b'
      simp only [gW, Function.update_apply, idleG, CF_ne_V, CF_ne_IP', if_false,
        St.ptr.injEq, true_and] at hq
      obtain ⟨rfl, rfl⟩ := hq
      rw [fires_unique hf (A.fire_tsSet hi b)]
      have hE := Exec.detect hi hI hu b (by
        cases b
        · exact .inl rfl
        · exact .inr (by simp [hb rfl]))
      exact ⟨_, .tsFin (A.exec_wf hw hE) (by simp) hI (by simp [hu]), .single (.inl hE)⟩
    · exfalso
      have hx' : A.V (some x') ≠ A.V (some x) := by simpa using hx
      simp only [gW, Function.update_apply, if_neg hx', V_ne_IP', if_false, idleG] at hp
      cases b' <;> simp at hp
  all_goals kill_bk

theorem rep_tsFin_step {x u : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat (i + 1))
    (hI : A.instr i = some (.detect x)) (hu : C.ptr (A.V (some x)) = .reg u) (ht : A.Tr t)
    (hf : t.Fires (render C.reg
      (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .done))) c') :
    ∃ C', A.Rep c' C' ∧ Reach A.Step C C' := by
  have hg := A.ownerResp_gW C i (s := .ptr (A.V (some x)) (.reg u) .done) rfl
  have ht' := ht
  cases ht
  case tsEnd j x' v hI' hv =>
    obtain ⟨hp, hY, -⟩ := A.clean_fires' hg ht' hf rfl
    obtain ⟨-, hq, -⟩ := hY _ rfl
    simp only [gW, gH, Function.update_apply, idleG, IP_ne_V, V_ne_IP', if_true, if_false, St.ptr.injEq, Val.nat.injEq, true_and, and_true, V_eq_V_iff, Option.some_inj, ite_true, ite_false, reduceIte] at hp; subst hp
    rw [hI] at hI'; simp only [Option.some.injEq, MInstr.detect.injEq] at hI'
    subst hI'
    simp only [gW, gH, Function.update_apply, idleG, IP_ne_V, V_ne_IP', if_true, if_false, St.ptr.injEq, Val.nat.injEq, true_and, and_true, V_eq_V_iff, Option.some_inj, ite_true, ite_false, reduceIte] at hq; subst hq
    rw [fires_unique hf (A.fire_tsEnd hi hu)]
    exact ⟨C, .idle hw, .refl⟩
  all_goals kill_bk

theorem rep_asMap_step {X Y : F} {f : Val Q → Val Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat i)
    (hI : A.instr i = some (.assign X Y f)) (hXY : X ≠ Y) (hX : X ≠ A.IP) (hY : Y ≠ A.IP)
    (ht : A.Tr t) (hf : t.Fires (render C.reg (A.gW C i X (.map X i))) c') :
    ∃ C', A.Rep c' C' ∧ Reach A.Step C C' := by
  have hg := A.ownerResp_gW C i (s := .map X i) rfl
  have ht' := ht
  cases ht
  case asMap j X' Y' f' v s hI' hXY' hX' hY' hv =>
    obtain ⟨hp, hYY, -⟩ := A.clean_fires' hg ht' hf rfl
    obtain ⟨-, hq, -⟩ := hYY _ rfl
    by_cases hXX : X' = X
    · subst hXX
      simp only [gW, Function.update_self, St.map.injEq, true_and] at hp
      subst hp
      rw [hI] at hI'; simp only [Option.some.injEq, MInstr.assign.injEq] at hI'
      obtain ⟨-, rfl, rfl⟩ := hI'
      simp only [gW, Function.update_apply, idleG, if_neg (Ne.symm hXY'), if_neg hY',
        St.ptr.injEq, true_and] at hq
      obtain ⟨rfl, rfl⟩ := hq
      rw [fires_unique hf (A.fire_asMap hXY' hX hY')]
      have hE := Exec.assign hi hI hX
      refine ⟨_, ?_, .single (.inl hE)⟩
      have := Rep.asFin (A := A) (A.exec_wf hw hE) (by simp) hI hXY' hX hY'
      convert this using 4
      simp [Function.update_of_ne hX]
    · exfalso
      simp only [gW, Function.update_apply, if_neg hXX, if_neg hX', idleG] at hp
      simp at hp
  all_goals kill_bk

theorem rep_asFin_step {X Y : F} {f : Val Q → Val Q} (hw : A.WF C)
    (hi : C.ptr A.IP = .nat (i + 1)) (hI : A.instr i = some (.assign X Y f)) (hXY : X ≠ Y)
    (hX : X ≠ A.IP) (hY : Y ≠ A.IP) (ht : A.Tr t)
    (hf : t.Fires (render C.reg (A.gW C i X (.ptr X (C.ptr X) .done))) c') :
    ∃ C', A.Rep c' C' ∧ Reach A.Step C C' := by
  have hg := A.ownerResp_gW C i (s := .ptr X (C.ptr X) .done) rfl
  have ht' := ht
  cases ht
  case asEnd j X' Y' f' v hI' hXY' hX' hY' hv =>
    obtain ⟨hp, hYY, -⟩ := A.clean_fires' hg ht' hf rfl
    simp only [gW, Function.update_apply, if_neg (Ne.symm hX), if_pos rfl, ite_true,
      St.ptr.injEq, Val.nat.injEq, true_and, and_true] at hp
    subst hp
    rw [hI] at hI'; simp only [Option.some.injEq, MInstr.assign.injEq] at hI'
    obtain ⟨rfl, rfl, rfl⟩ := hI'
    obtain ⟨-, hq, -⟩ := hYY _ rfl
    simp only [gW, Function.update_apply, if_pos rfl, St.ptr.injEq, true_and] at hq
    obtain ⟨rfl, -⟩ := hq
    rw [fires_unique hf (A.fire_asEnd hi hX)]
    exact ⟨C, .idle hw, .refl⟩
  all_goals kill_bk

end phases

/-- **Backward simulation.** -/
theorem rep_step {c c' : Multiset (St Q F)} {C : Cfg Q F} (h : A.Rep c C)
    (hs : MStep {t | A.Tr t} c c') : ∃ C', A.Rep c' C' ∧ Reach A.Step C C' := by
  obtain ⟨t, ht, hf⟩ := hs
  cases h with
  | idle hw => exact A.rep_idle_step hw ht hf
  | mvEmit hw hi hI hu => exact A.rep_mvEmit_step hw hi hI hu ht hf
  | mvDone hw hi hI hu hw' hpos => exact A.rep_mvDone_step hw hi hI hu hw' hpos ht hf
  | mvHalf hw hi hI hw' hpos => exact A.rep_mvHalf_step hw hi hI hw' hpos ht hf
  | mvTake hw hi hI hw' hpos => exact A.rep_mvTake_step hw hi hI hw' hpos ht hf
  | mvFin hw hi hI hw' => exact A.rep_mvFin_step hw hi hI hw' ht hf
  | tsTest hw hi hI hu => exact A.rep_tsTest_step hw hi hI hu ht hf
  | tsRes hw hi hI hu hb => exact A.rep_tsRes_step hw hi hI hu hb ht hf
  | tsFin hw hi hI hu => exact A.rep_tsFin_step hw hi hI hu ht hf
  | asMap hw hi hI hXY hX hY => exact A.rep_asMap_step hw hi hI hXY hX hY ht hf
  | asFin hw hi hI hXY hX hY => exact A.rep_asFin_step hw hi hI hXY hX hY ht hf

end Machine

end Podc.PPDoubleExpThresholds
