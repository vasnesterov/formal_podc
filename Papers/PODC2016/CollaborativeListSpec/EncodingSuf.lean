import Papers.PODC2016.CollaborativeListSpec.EncodingActs

/-!
# The actions of the extension `γ_w^i` of `α_w`, position by position
-/

namespace Podc.CollaborativeListSpec

namespace Params

variable {Rep U : Type} (E : Params Rep U) (w : ℕ → Bool) (i : ℕ)

theorem g_lt {p : ℕ} (h : p < E.Lα) : E.g w i p = E.act w p := by rw [g, if_pos h]

theorem g_suf (q : ℕ) : E.g w i (E.Lα + q) = E.suf w i q := by
  rw [g, if_neg (by omega), Nat.add_sub_cancel_left]

theorem mpos_of_le {j : ℕ} (h : j ≤ E.d + 1) : E.mpos j = 3 * j - 1 := by rw [mpos, if_pos h]

theorem mpos_top : E.mpos (E.d + 2) = 3 * E.d + 4 := by rw [mpos, if_neg (by omega)]

theorem suf_doOp_iff (hi : i ≤ E.d) {q : ℕ} {r : Rep} {op : LOp U} :
    E.suf w i q = .doOp r op ↔ (q = 2 * i ∧ r = E.r2 ∧ op = .read) ∨
      (q = 2 * i + 1 ∧ r = E.r2 ∧ op = .ins E.X (E.lenA w (i - 1) + 1)) ∨
      (q = 2 * i + 5 ∧ r = E.r1 ∧ op = .read) ∨ (2 * i + E.d + 9 ≤ q ∧ r = E.r3 ∧ op = .read) := by
  unfold suf
  split_ifs <;> simp only [Act.doOp.injEq, reduceCtorEq, false_iff] <;>
    first
    | (constructor
       · rintro ⟨rfl, rfl⟩; simp_all
       · rintro (⟨h, rfl, rfl⟩ | ⟨h, rfl, rfl⟩ | ⟨h, rfl, rfl⟩ | ⟨h, rfl, rfl⟩) <;>
           first | exact ⟨rfl, rfl⟩ | omega)
    | omega

theorem suf_send_iff {q : ℕ} {r : Rep} : E.suf w i q = .send r ↔ q = 2 * i + 2 ∧ r = E.r2 := by
  unfold suf
  split_ifs <;> simp only [Act.send.injEq, reduceCtorEq, false_iff] <;>
    first
    | (constructor
       · rintro rfl; exact ⟨by omega, rfl⟩
       · rintro ⟨-, rfl⟩; rfl)
    | omega

theorem suf_recv_iff {q : ℕ} {r : Rep} {s : ℕ} :
    E.suf w i q = .recv r s ↔
      (∃ t < i, (q = 2 * t ∧ r = E.r2 ∧ s = E.mpos (t + 1)) ∨ (q = 2 * t + 1 ∧ r = E.r1 ∧ s = E.mpos (t + 1))) ∨
      (q = 2 * i + 3 ∧ r = E.r2 ∧ s = E.pmx i) ∨ (q = 2 * i + 4 ∧ r = E.r1 ∧ s = E.pmx i) ∨
      (∃ t < i, q = 2 * i + 6 + t ∧ r = E.r3 ∧ s = E.mpos (t + 1)) ∨
      (q = 3 * i + 6 ∧ r = E.r3 ∧ s = E.pmx i) ∨
      (∃ t < E.d + 2 - i, q = 3 * i + 7 + t ∧ r = E.r3 ∧ s = E.mpos (i + 1 + t)) := by
  constructor
  · intro h
    unfold suf at h
    split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 <;>
      simp only [Act.recv.injEq, reduceCtorEq] at h
    · obtain ⟨rfl, rfl⟩ := h; exact Or.inl ⟨q / 2, by omega, Or.inl ⟨by omega, rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := h; exact Or.inl ⟨q / 2, by omega, Or.inr ⟨by omega, rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := h; exact Or.inr (Or.inl ⟨h6, rfl, rfl⟩)
    · obtain ⟨rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inl ⟨h7, rfl, rfl⟩))
    · obtain ⟨rfl, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q - (2 * i + 6), by omega, by omega, rfl, rfl⟩)))
    · obtain ⟨rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h10, rfl, rfl⟩))))
    · obtain ⟨rfl, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨q - (3 * i + 7), by omega, by omega, rfl, rfl⟩))))
  · rintro (⟨t, ht, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨t, ht, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨t, ht, rfl, rfl, rfl⟩)
    · unfold suf; rw [if_pos (by omega), if_pos (by omega), show 2 * t / 2 = t by omega]
    · unfold suf; rw [if_pos (by omega), if_neg (by omega), show (2 * t + 1) / 2 = t by omega]
    · unfold suf
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
    · unfold suf
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos rfl]
    · unfold suf
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
        show 2 * i + 6 + t - (2 * i + 6) = t by omega]
    · unfold suf
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
    · unfold suf
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos (by omega), show 3 * i + 7 + t - (3 * i + 7) = t by omega]

theorem suf_read2 : E.suf w i (2 * i) = .doOp E.r2 .read := by
  unfold suf; rw [if_neg (by omega), if_pos rfl]

theorem suf_insX : E.suf w i (2 * i + 1) = .doOp E.r2 (.ins E.X (E.lenA w (i - 1) + 1)) := by
  unfold suf; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem suf_sendX : E.suf w i (2 * i + 2) = .send E.r2 := by
  unfold suf; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem suf_read1 : E.suf w i (2 * i + 5) = .doOp E.r1 .read := by
  unfold suf
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem suf_read3 (hi : i ≤ E.d) : E.suf w i (2 * i + E.d + 9) = .doOp E.r3 .read :=
  (E.suf_doOp_iff w i hi).2 (Or.inr (Or.inr (Or.inr ⟨le_rfl, rfl, rfl⟩)))

end Params

end Podc.CollaborativeListSpec
