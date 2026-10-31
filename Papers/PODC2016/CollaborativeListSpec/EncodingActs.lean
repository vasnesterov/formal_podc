import Papers.PODC2016.CollaborativeListSpec.Encoding

/-!
# The actions of `α_w` and `γ_w^i`, position by position
-/

namespace Podc.CollaborativeListSpec

namespace Params

variable {Rep U : Type} (E : Params Rep U) (w : ℕ → Bool)

/-! ### `α_w` -/

theorem act_Op {t : ℕ} (ht : t ≤ E.d) : E.act w (3 * t) = .doOp E.r1 (.ins (E.Op t) (E.lenA w t)) := by
  rw [act, if_pos (by omega), if_pos (by omega), show 3 * t / 3 = t by omega]

theorem act_Cl {t : ℕ} (ht : t ≤ E.d) :
    E.act w (3 * t + 1) = .doOp E.r1 (.ins (E.Cl t) (E.lenA w t + 1)) := by
  rw [act, if_pos (by omega), if_neg (by omega), if_pos (by omega), show (3 * t + 1) / 3 = t by omega]

theorem act_send {t : ℕ} (ht : t ≤ E.d) : E.act w (3 * t + 2) = .send E.r1 := by
  rw [act, if_pos (by omega), if_neg (by omega), if_neg (by omega)]

theorem act_Star : E.act w (3 * E.d + 3) = .doOp E.r1 (.ins E.Star (E.lenA w E.d + 1)) := by
  rw [act, if_neg (by omega), if_pos rfl]

theorem act_send_star : E.act w (3 * E.d + 4) = .send E.r1 := by
  rw [act, if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem act_delOp {t : ℕ} (ht : t ≤ E.d) : E.act w (3 * E.d + 5 + 2 * t) = .doOp E.r1 (.del (E.Op t)) := by
  rw [act, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    if_pos (by omega), show (3 * E.d + 5 + 2 * t - (3 * E.d + 5)) / 2 = t by omega]

theorem act_delCl {t : ℕ} (ht : t ≤ E.d) :
    E.act w (3 * E.d + 6 + 2 * t) = .doOp E.r1 (.del (E.Cl t)) := by
  rw [act, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    if_neg (by omega), show (3 * E.d + 6 + 2 * t - (3 * E.d + 5)) / 2 = t by omega]

theorem act_Bee (h : E.odd = true) : E.act w (5 * E.d + 7) = .doOp E.r1 (.ins E.Bee 0) := by
  rw [act, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos ⟨h, rfl⟩]

theorem act_delBee (h : E.odd = true) : E.act w (5 * E.d + 8) = .doOp E.r1 (.del E.Bee) := by
  rw [act, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos ⟨h, rfl⟩]

theorem Lα_eq : E.Lα = 5 * E.d + 8 + (if E.odd then 2 else 0) := rfl

theorem act_last : E.act w (E.Lα - 1) = .send E.r1 := by
  rw [act, if_neg (by unfold Lα; split <;> omega), if_neg (by unfold Lα; split <;> omega),
    if_neg (by unfold Lα; split <;> omega), if_neg (by unfold Lα; split <;> omega),
    if_neg (by unfold Lα; split <;> simp_all), if_neg (by unfold Lα; split <;> simp_all)]

@[simp] theorem act_rep (p : ℕ) : (E.act w p).rep = E.r1 := by
  unfold act; split_ifs <;> rfl

theorem act_ins_iff {q : ℕ} {r : Rep} {x : U} {k : ℕ} :
    E.act w q = .doOp r (.ins x k) ↔ r = E.r1 ∧
      ((∃ t ≤ E.d, (q = 3 * t ∧ x = E.Op t ∧ k = E.lenA w t) ∨
        (q = 3 * t + 1 ∧ x = E.Cl t ∧ k = E.lenA w t + 1)) ∨
      (q = 3 * E.d + 3 ∧ x = E.Star ∧ k = E.lenA w E.d + 1) ∨
      (E.odd = true ∧ q = 5 * E.d + 7 ∧ x = E.Bee ∧ k = 0)) := by
  constructor
  · intro h
    unfold act at h
    split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;> simp only [Act.doOp.injEq, LOp.ins.injEq,
      reduceCtorEq, false_and, and_false] at h
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, Or.inl ⟨q / 3, by omega, Or.inl ⟨by omega, rfl, rfl⟩⟩⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, Or.inl ⟨q / 3, by omega, Or.inr ⟨by omega, rfl, rfl⟩⟩⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, Or.inr (Or.inl ⟨h4, rfl, rfl⟩)⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, Or.inr (Or.inr ⟨h8.1, h8.2, rfl, rfl⟩)⟩
  · rintro ⟨rfl, ⟨t, ht, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩ | ⟨rfl, rfl, rfl⟩ | ⟨h, rfl, rfl, rfl⟩⟩
    · exact E.act_Op w ht
    · exact E.act_Cl w ht
    · exact E.act_Star w
    · exact E.act_Bee w h

theorem act_del_iff {q : ℕ} {r : Rep} {x : U} :
    E.act w q = .doOp r (.del x) ↔ r = E.r1 ∧
      ((∃ t ≤ E.d, (q = 3 * E.d + 5 + 2 * t ∧ x = E.Op t) ∨ (q = 3 * E.d + 6 + 2 * t ∧ x = E.Cl t)) ∨
      (E.odd = true ∧ q = 5 * E.d + 8 ∧ x = E.Bee)) := by
  constructor
  · intro h
    unfold act at h
    split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;> simp only [Act.doOp.injEq, LOp.del.injEq,
      reduceCtorEq, false_and, and_false] at h
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, Or.inl ⟨(q - (3 * E.d + 5)) / 2, by omega, Or.inl ⟨by omega, rfl⟩⟩⟩
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, Or.inl ⟨(q - (3 * E.d + 5)) / 2, by omega, Or.inr ⟨by omega, rfl⟩⟩⟩
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, Or.inr ⟨h9.1, h9.2, rfl⟩⟩
  · rintro ⟨rfl, ⟨t, ht, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨h, rfl, rfl⟩⟩
    · exact E.act_delOp w ht
    · exact E.act_delCl w ht
    · exact E.act_delBee w h

theorem act_ne_read {q : ℕ} {r : Rep} : E.act w q ≠ .doOp r .read := by
  unfold act; split_ifs <;> simp

theorem act_ne_recv {q : ℕ} {r : Rep} {s : ℕ} : E.act w q ≠ .recv r s := by
  unfold act; split_ifs <;> simp

theorem act_send_iff {q : ℕ} {r : Rep} (hq : q < E.Lα) :
    E.act w q = .send r ↔ r = E.r1 ∧
      ((∃ t ≤ E.d, q = 3 * t + 2) ∨ q = 3 * E.d + 4 ∨ q = E.Lα - 1) := by
  constructor
  · intro h
    unfold act at h
    split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;> simp only [Act.send.injEq,
      reduceCtorEq] at h
    · exact ⟨h.symm, Or.inl ⟨q / 3, by omega, by omega⟩⟩
    · exact ⟨h.symm, Or.inr (Or.inl h5)⟩
    · refine ⟨h.symm, Or.inr (Or.inr ?_)⟩
      unfold Lα at hq ⊢; split at hq <;> simp_all <;> omega
  · rintro ⟨rfl, ⟨t, ht, rfl⟩ | rfl | rfl⟩
    · exact E.act_send w ht
    · exact E.act_send_star w
    · exact E.act_last w

end Params

end Podc.CollaborativeListSpec
