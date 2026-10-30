import Papers.PODC2023.PPDoubleExpThresholds.MachineToProtocolRep

/-!
# The individual protocol steps between clean configurations

One lemma per step of an instruction (`fire_*`): the transition fires and leads to the next
representation (cf. `Rep`).
-/

set_option linter.unusedSectionVars false

namespace Podc.PPDoubleExpThresholds

open Cslib Cslib.PopulationProtocol Cslib.TransitionSystem M2P

namespace Machine

variable {Q F : Type*} [Fintype Q] [Fintype F] [DecidableEq Q] [DecidableEq F]
variable (A : Machine Q F)

theorem fire_pp {r : Q → ℕ} {g g' : F → St Q F} (t : Transition (St Q F)) {X Y : F}
    (hXY : X ≠ Y) (hp : g X = t.p) (hq : g Y = t.q)
    (hg' : Function.update (Function.update g X t.p') Y t.q' = g') :
    t.Fires (render r g) (render r g') := by
  rw [← hg']; exact clean_fire_pp t hXY hp.symm hq.symm

theorem fire_pr {r r' : Q → ℕ} {g g' : F → St Q F} (t : Transition (St Q F)) {X : F} {u u' : Q}
    (hp : g X = t.p) (hq : t.q = .reg u) (hq' : t.q' = .reg u') (hu : 0 < r u)
    (hr : mvR r u u' = r') (hg' : Function.update g X t.p' = g') :
    t.Fires (render r g) (render r' g') := by
  rw [← hg', ← hr]; exact clean_fire_pr t hp.symm hq hq' hu

theorem mvR_mvR {r : Q → ℕ} {a b : Q} (c : Q) (ha : 0 < r a) :
    mvR (mvR r a b) b c = mvR r a c := by
  funext q
  simp only [mvR, Function.update_apply]
  split_ifs <;> subst_vars <;> first | omega | (simp_all; omega) | simp_all

theorem mvR_mvR_self {r : Q → ℕ} {a b : Q} (ha : 0 < r a) : mvR (mvR r a b) b a = r := by
  rw [mvR_mvR _ ha, mvR_self ha]

theorem pos_mvR {r : Q → ℕ} {a b : Q} : 0 < mvR r a b b := by
  simp [mvR]

/-- Shorthand for the `IP` agent. -/
abbrev ipS (i : ℕ) (s : Stage) : St Q F := .ptr A.IP (.nat i) s

/-- Updating the `IP` value of a configuration only changes the idle agent of `IP`. -/
theorem update_idleG_IP (C : Cfg Q F) (v : Val Q) (r : Q → ℕ) (s : St Q F) :
    Function.update (idleG ⟨r, Function.update C.ptr A.IP v⟩) A.IP s =
      Function.update (idleG C) A.IP s := by
  funext Z; simp only [idleG, Function.update_apply]; split_ifs <;> simp_all

theorem idleG_update (C : Cfg Q F) (Z : F) (v : Val Q) (r : Q → ℕ) :
    idleG (⟨r, Function.update C.ptr Z v⟩ : Cfg Q F) =
      Function.update (idleG C) Z (.ptr Z v .none) := by
  funext X; simp only [idleG, Function.update_apply]; split_ifs <;> simp_all

/-! ### `⟨move⟩` -/

section move

variable {C : Cfg Q F} {i : ℕ} {x y u w : Q}

theorem fire_mvStart (hi : C.ptr A.IP = .nat i) (hu : C.ptr (A.V (some x)) = .reg u) :
    (⟨A.ipS i .none, .ptr (A.V (some x)) (.reg u) .none, A.ipS i .wait,
      .ptr (A.V (some x)) (.reg u) .emit⟩ : Transition (St Q F)).Fires
      (pi C) (render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .emit))) := by
  refine fire_pp _ (X := A.IP) (Y := A.V (some x)) (by simp) (by simp [idleG, hi])
    (by simp [idleG, hu]) ?_
  rfl

/-- The commit step of `x ↦ y`. -/
theorem fire_mvEmit (hi : C.ptr A.IP = .nat i) (hu : C.ptr (A.V (some x)) = .reg u)
    (hpos : 0 < C.reg u) (w : Q) :
    (⟨.ptr (A.V (some x)) (.reg u) .emit, .reg u, .ptr (A.V (some x)) (.reg u) .done,
      .reg A.z0⟩ : Transition (St Q F)).Fires
      (render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .emit)))
      (render (mvR (mvR C.reg u w) w A.z0)
        (A.gW ⟨mvR C.reg u w, Function.update C.ptr A.IP (.nat (i + 1))⟩ i (A.V (some x))
          (.ptr (A.V (some x)) (.reg u) .done))) := by
  refine fire_pr _ (X := A.V (some x)) (by simp [gW]) rfl rfl hpos (mvR_mvR _ hpos).symm ?_
  funext Z; simp only [gW, idleG, Function.update_apply]; split_ifs <;> simp_all

theorem fire_mvHalf {r : Q → ℕ} (hu : C.ptr (A.V (some x)) = .reg u) :
    (⟨A.ipS i .wait, .ptr (A.V (some x)) (.reg u) .done, A.ipS i .half,
      .ptr (A.V (some x)) (.reg u) .none⟩ : Transition (St Q F)).Fires
      (render r (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .done)))
      (render r (A.gH C i)) := by
  refine fire_pp _ (X := A.IP) (Y := A.V (some x)) (by simp) (by simp [gW]) (by simp [gW]) ?_
  funext Z; simp only [gW, gH, idleG, Function.update_apply]; split_ifs <;> simp_all

theorem fire_mvTake {r : Q → ℕ} (hw : C.ptr (A.V (some y)) = .reg w) :
    (⟨A.ipS i .half, .ptr (A.V (some y)) (.reg w) .none, A.ipS i .wait,
      .ptr (A.V (some y)) (.reg w) .take⟩ : Transition (St Q F)).Fires
      (render r (A.gH C i))
      (render r (A.gW C i (A.V (some y)) (.ptr (A.V (some y)) (.reg w) .take))) := by
  refine fire_pp _ (X := A.IP) (Y := A.V (some y)) (by simp) (by simp [gH])
    (by simp [gH, idleG, hw]) ?_
  funext Z; simp only [gW, gH, idleG, Function.update_apply]; split_ifs <;> simp_all

theorem fire_mvPut (hpos : 0 < C.reg w) :
    (⟨.ptr (A.V (some y)) (.reg w) .take, .reg A.z0, .ptr (A.V (some y)) (.reg w) .done,
      .reg w⟩ : Transition (St Q F)).Fires
      (render (mvR C.reg w A.z0)
        (A.gW C i (A.V (some y)) (.ptr (A.V (some y)) (.reg w) .take)))
      (render C.reg (A.gW C i (A.V (some y)) (.ptr (A.V (some y)) (.reg w) .done))) := by
  refine fire_pr _ (X := A.V (some y)) (by simp [gW]) rfl rfl pos_mvR (mvR_mvR_self hpos) ?_
  funext Z; simp only [gW, gH, idleG, Function.update_apply]; split_ifs <;> simp_all

theorem fire_mvEnd (hi : C.ptr A.IP = .nat (i + 1)) (hw : C.ptr (A.V (some y)) = .reg w) :
    (⟨A.ipS i .wait, .ptr (A.V (some y)) (.reg w) .done, A.ipS (i + 1) .none,
      .ptr (A.V (some y)) (.reg w) .none⟩ : Transition (St Q F)).Fires
      (render C.reg (A.gW C i (A.V (some y)) (.ptr (A.V (some y)) (.reg w) .done)))
      (pi C) := by
  refine fire_pp _ (X := A.IP) (Y := A.V (some y)) (by simp) (by simp [gW]) (by simp [gW]) ?_
  funext Z; simp only [gW, gH, idleG, Function.update_apply]; split_ifs <;> simp_all
  
end move

/-! ### `⟨test⟩` -/

section test

variable {C : Cfg Q F} {i : ℕ} {x u : Q}

theorem fire_tsStart (hi : C.ptr A.IP = .nat i) (hu : C.ptr (A.V (some x)) = .reg u) :
    (⟨A.ipS i .none, .ptr (A.V (some x)) (.reg u) .none, A.ipS i .wait,
      .ptr (A.V (some x)) (.reg u) .test⟩ : Transition (St Q F)).Fires
      (pi C) (render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .test))) := by
  refine fire_pp _ (X := A.IP) (Y := A.V (some x)) (by simp) (by simp [idleG, hi])
    (by simp [idleG, hu]) ?_
  rfl

theorem fire_tsYes (hpos : 0 < C.reg u) :
    (⟨.ptr (A.V (some x)) (.reg u) .test, .reg u, .ptr (A.V (some x)) (.reg u) .tt, .reg u⟩ :
      Transition (St Q F)).Fires
      (render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .test)))
      (render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u)
        (if true then .tt else .ff)))) := by
  refine fire_pr _ (X := A.V (some x)) (by simp [gW]) rfl rfl hpos (mvR_self hpos) ?_
  funext Z; simp only [gW, gH, idleG, Function.update_apply]; split_ifs <;> simp_all

/-- `(V_x)^v_test, IP ↦ (V_x)^v_false, IP` (the `IP` agent is a partner different from `v`). -/
theorem fire_tsNo :
    (⟨.ptr (A.V (some x)) (.reg u) .test, A.ipS i .wait, .ptr (A.V (some x)) (.reg u) .ff,
      A.ipS i .wait⟩ : Transition (St Q F)).Fires
      (render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .test)))
      (render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u)
        (if false then .tt else .ff)))) := by
  refine fire_pp _ (X := A.V (some x)) (Y := A.IP) (by simp) (by simp [gW]) (by simp [gW]) ?_
  funext Z; simp only [gW, gH, idleG, Function.update_apply]; split_ifs <;> simp_all

/-- The commit step of `detect x > 0`. -/
theorem fire_tsSet (hi : C.ptr A.IP = .nat i) (b : Bool) :
    (⟨.ptr (A.V (some x)) (.reg u) (if b then .tt else .ff), .ptr A.CF (C.ptr A.CF) .none,
      .ptr (A.V (some x)) (.reg u) .done, .ptr A.CF (.bool b) .none⟩ :
      Transition (St Q F)).Fires
      (render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u)
        (if b then .tt else .ff))))
      (render C.reg (A.gW ⟨C.reg, Function.update (Function.update C.ptr A.CF (.bool b)) A.IP
        (.nat (i + 1))⟩ i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .done))) := by
  refine fire_pp _ (X := A.V (some x)) (Y := A.CF) (by simp) (by simp [gW]) (by simp [gW, idleG])
    ?_
  funext Z; simp only [gW, gH, idleG, Function.update_apply]; split_ifs <;> simp_all

theorem fire_tsEnd (hi : C.ptr A.IP = .nat (i + 1)) (hu : C.ptr (A.V (some x)) = .reg u) :
    (⟨A.ipS i .wait, .ptr (A.V (some x)) (.reg u) .done, A.ipS (i + 1) .none,
      .ptr (A.V (some x)) (.reg u) .none⟩ : Transition (St Q F)).Fires
      (render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .done)))
      (pi C) := by
  refine fire_pp _ (X := A.IP) (Y := A.V (some x)) (by simp) (by simp [gW]) (by simp [gW]) ?_
  funext Z; simp only [gW, gH, idleG, Function.update_apply]; split_ifs <;> simp_all

end test

/-! ### `⟨pointer⟩` -/

section pointer

variable {C : Cfg Q F} {i : ℕ} {X Y : F} {f : Val Q → Val Q}

theorem fire_asStart (hi : C.ptr A.IP = .nat i) (hX : X ≠ A.IP) :
    (⟨A.ipS i .none, .ptr X (C.ptr X) .none, A.ipS i .wait, .map X i⟩ :
      Transition (St Q F)).Fires (pi C) (render C.reg (A.gW C i X (.map X i))) := by
  refine fire_pp _ (X := A.IP) (Y := X) (Ne.symm hX) (by simp [idleG, hi]) (by simp [idleG]) ?_
  rfl

/-- The commit step of an ordinary assignment `X := f(Y)`. -/
theorem fire_asMap (hXY : X ≠ Y) (hX : X ≠ A.IP) (hY : Y ≠ A.IP) :
    (⟨.map X i, .ptr Y (C.ptr Y) .none, .ptr X (f (C.ptr Y)) .done, .ptr Y (C.ptr Y) .none⟩ :
      Transition (St Q F)).Fires
      (render C.reg (A.gW C i X (.map X i)))
      (render C.reg (A.gW ⟨C.reg, Function.update (Function.update C.ptr X (f (C.ptr Y))) A.IP
        (.nat (i + 1))⟩ i X (.ptr X (f (C.ptr Y)) .done))) := by
  refine fire_pp _ (X := X) (Y := Y) hXY (by simp [gW]) (by simp [gW, idleG, hY, Ne.symm hXY]) ?_
  funext Z; simp only [gW, gH, idleG, Function.update_apply]; split_ifs <;> simp_all

theorem fire_asEnd (hi : C.ptr A.IP = .nat (i + 1)) (hX : X ≠ A.IP) :
    (⟨A.ipS i .wait, .ptr X (C.ptr X) .done, A.ipS (i + 1) .none, .ptr X (C.ptr X) .none⟩ :
      Transition (St Q F)).Fires (render C.reg (A.gW C i X (.ptr X (C.ptr X) .done))) (pi C) := by
  refine fire_pp _ (X := A.IP) (Y := X) (Ne.symm hX) (by simp [gW, Ne.symm hX]) (by simp [gW])
    ?_
  funext Z; simp only [gW, gH, idleG, Function.update_apply]; split_ifs <;> simp_all

theorem fire_jmp (hi : C.ptr A.IP = .nat i) (hY : Y ≠ A.IP) :
    (⟨A.ipS i .none, .ptr Y (C.ptr Y) .none, .ptr A.IP (f (C.ptr Y)) .none,
      .ptr Y (C.ptr Y) .none⟩ : Transition (St Q F)).Fires (pi C)
      (pi ⟨C.reg, Function.update C.ptr A.IP (f (C.ptr Y))⟩) := by
  refine fire_pp _ (X := A.IP) (Y := Y) (Ne.symm hY) (by simp [idleG, hi]) (by simp [idleG]) ?_
  funext Z; simp only [gW, gH, idleG, Function.update_apply]; split_ifs <;> simp_all

theorem fire_asSelf (hi : C.ptr A.IP = .nat i) (hY : Y ≠ A.IP) :
    (⟨A.ipS i .none, .ptr Y (C.ptr Y) .none, A.ipS (i + 1) .none,
      .ptr Y (f (C.ptr Y)) .none⟩ : Transition (St Q F)).Fires (pi C)
      (pi ⟨C.reg, Function.update (Function.update C.ptr Y (f (C.ptr Y))) A.IP (.nat (i + 1))⟩) := by
  refine fire_pp _ (X := A.IP) (Y := Y) (Ne.symm hY) (by simp [idleG, hi]) (by simp [idleG]) ?_
  funext Z; simp only [gW, gH, idleG, Function.update_apply]; split_ifs <;> simp_all

theorem fire_asIP (hi : C.ptr A.IP = .nat i) (hX : X ≠ A.IP) :
    (⟨A.ipS i .none, .ptr X (C.ptr X) .none, A.ipS (i + 1) .none,
      .ptr X (f (.nat i)) .none⟩ : Transition (St Q F)).Fires (pi C)
      (pi ⟨C.reg, Function.update (Function.update C.ptr X (f (C.ptr A.IP))) A.IP
        (.nat (i + 1))⟩) := by
  refine fire_pp _ (X := A.IP) (Y := X) (Ne.symm hX) (by simp [idleG, hi]) (by simp [idleG]) ?_
  funext Z; simp only [gW, gH, idleG, Function.update_apply]; split_ifs <;> simp_all

theorem fire_jmpIP (hi : C.ptr A.IP = .nat i) :
    (⟨A.ipS i .none, .ptr A.OF (C.ptr A.OF) .none, .ptr A.IP (f (.nat i)) .none,
      .ptr A.OF (C.ptr A.OF) .none⟩ : Transition (St Q F)).Fires (pi C)
      (pi ⟨C.reg, Function.update C.ptr A.IP (f (C.ptr A.IP))⟩) := by
  refine fire_pp _ (X := A.IP) (Y := A.OF) (by simp) (by simp [idleG, hi]) (by simp [idleG]) ?_
  funext Z; simp only [gW, gH, idleG, Function.update_apply]; split_ifs <;> simp_all

end pointer


end Machine

end Podc.PPDoubleExpThresholds
