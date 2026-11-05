import Papers.PODC2019.RMESubLogBoth.InvFrame

/-!
# Steps that only change the program counter
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

section
variable {c : Cfg k} {own : ℕ → ℕ}

@[simp] lemma Cfg.setPc_pc_self (c : Cfg k) (p : Fin k) (r : PC k) : (c.setPc p r).pc p = r := by
  simp [Cfg.setPc]

@[simp] lemma Cfg.setPc_pc_ne (c : Cfg k) {p j : Fin k} (r : PC k) (h : j ≠ p) :
    (c.setPc p r).pc j = c.pc j := by
  simp [Cfg.setPc, h]

@[simp] lemma Cfg.setPc_node (c : Cfg k) (p : Fin k) (r : PC k) : (c.setPc p r).node = c.node := rfl
@[simp] lemma Cfg.setPc_pred (c : Cfg k) (p : Fin k) (r : PC k) : (c.setPc p r).pred = c.pred := rfl
@[simp] lemma Cfg.setPc_nn (c : Cfg k) (p : Fin k) (r : PC k) : (c.setPc p r).nn = c.nn := rfl
@[simp] lemma Cfg.setPc_csig (c : Cfg k) (p : Fin k) (r : PC k) : (c.setPc p r).csig = c.csig := rfl
@[simp] lemma Cfg.setPc_tail (c : Cfg k) (p : Fin k) (r : PC k) : (c.setPc p r).tail = c.tail := rfl
@[simp] lemma Cfg.setPc_nxt (c : Cfg k) (p : Fin k) (r : PC k) : (c.setPc p r).nxt = c.nxt := rfl
@[simp] lemma Cfg.setPc_holder (c : Cfg k) (p : Fin k) (r : PC k) :
    (c.setPc p r).holder = c.holder := rfl

lemma vp_setPc {p : Fin k} {r : PC k} (ho : r.ovr = (c.pc p).ovr) (j : Fin k) :
    (c.setPc p r).vp j = c.vp j := by
  refine vp_congr ?_ (by simp) (fun _ _ => by simp)
  by_cases hj : j = p
  · subst hj; simp [ho]
  · simp [hj]

/-- A step that only changes the program counter of `p` (keeping `mypred` overrides) preserves
the invariant, provided the local invariant of `p` holds afterwards. -/
lemma inv_setPc (hG : Glob c own) (hL : ∀ q, LI c own q) {p : Fin k} {r : PC k}
    (ho : r.ovr = (c.pc p).ovr) (h13 : ∀ a, r ≠ .l13 a) (hR : r.InR → c.holder = some p)
    (hself : LI (c.setPc p r) own p) : Inv (c.setPc p r) := by
  have hvp := vp_setPc (c := c) ho
  have h13' : ∀ j a, (c.setPc p r).pc j = .l13 a → c.pc j = .l13 a := by
    intro j a hj
    by_cases hjp : j = p
    · subst hjp; simp at hj; exact absurd hj (h13 a)
    · simpa [hjp] using hj
  refine ⟨own, hG.of_eq rfl rfl rfl rfl rfl hvp (fun _ => Iff.rfl) ?_, ?_⟩
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; simp at hq; simpa using hR hq
    · simp [hqp] at hq; simpa using hG.holder q hq
  · intro q
    by_cases hqp : q = p
    · subst hqp; exact hself
    · exact (hL q).of_eq (by simp [hqp]) h13' rfl rfl rfl rfl rfl hvp (fun _ h => h)
        (fun _ _ => rfl)

end

end Podc.RMESubLogBoth
