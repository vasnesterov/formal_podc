import Papers.PODC2016.CollaborativeListSpec.LBRecover

/-!
# Theorems 8 and 9: the metadata lower bound

**Decoding (Theorem 9).** If two bit strings `w ≠ w'` lead to the same state of `R₁` at the end
of `α_w`, let `i` be the first differing bit. The executions `β_w^i` and `β_{w'}^i` start from the
same configuration as far as the remaining actions can tell (same replica states, same messages
`m₁ … mᵢ`), so `R₁`'s read returns the same list in both; by `recover_correct` this list
determines `wᵢ`. Hence `w ↦ σ_w` is injective, and some `σ_w` needs `d` bits.
-/

namespace Podc.CollaborativeListSpec

variable {Rep U Q M : Type} [DecidableEq Rep] [DecidableEq U] {P : Protocol Rep (LOp U) (List U) Q M}

/-- The number of deletions in an execution. -/
def numDel {Rep U : Type} (α : List (Act Rep (LOp U))) : ℕ :=
  α.countP fun a => match a with
    | .doOp _ (.del _) => true
    | _ => false

theorem pre_add (g : ℕ → Act Rep (LOp U)) (L m : ℕ) :
    pre g (L + m) = pre g L ++ (List.range m).map (fun q => g (L + q)) := by
  simp [pre, List.range_add, List.map_map, Function.comp_def]

namespace Params

variable (E : Params Rep U)

theorem AB_congr {w w' : ℕ → Bool} {j : ℕ} (h : ∀ t, 1 ≤ t → t ≤ j → w t = w' t) :
    E.AB w j = E.AB w' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [AB, ih (fun t h1 h2 => h t h1 (by omega)), h (j + 1) (by omega) le_rfl]

theorem act_congr {w w' : ℕ → Bool} {i : ℕ} (hi : i ≤ E.d) (h : ∀ t, 1 ≤ t → t < i → w t = w' t)
    {p : ℕ} (hp : p < 3 * i) : E.act w p = E.act w' p := by
  have hA : ∀ j, j < i → E.lenA w j = E.lenA w' j := fun j hj => by
    rw [lenA, lenA, E.AB_congr (w := w) (w' := w') (j := j) (fun t h1 h2 => h t h1 (by omega))]
  unfold act
  rw [if_pos (show p < 3 * (E.d + 1) by omega), if_pos (show p < 3 * (E.d + 1) by omega),
    hA (p / 3) (by omega)]

theorem suf_congr {w w' : ℕ → Bool} {i : ℕ} (h : ∀ t, 1 ≤ t → t < i → w t = w' t) (q : ℕ) :
    E.suf w i q = E.suf w' i q := by
  have : E.lenA w (i - 1) = E.lenA w' (i - 1) := by
    rw [lenA, lenA, E.AB_congr (w := w) (w' := w') (j := i - 1) (fun t h1 h2 => h t h1 (by omega))]
  unfold suf; rw [this]

/-- `R₁`'s read in `β_w^i` only depends on `σ_w` and `m₁ … mᵢ` (the `Recover` experiment). -/
theorem y_congr (hi1 : 1 ≤ i) (hi : i ≤ E.d) {w w' : ℕ → Bool} (h : ∀ t, 1 ≤ t → t < i → w t = w' t)
    (hσ : (P.exec (pre (E.act w) E.Lα)).st E.r1 = (P.exec (pre (E.act w') E.Lα)).st E.r1) :
    rval P (E.g w i) (E.Lα + (2 * i + 5)) = rval P (E.g w' i) (E.Lα + (2 * i + 5)) := by
  have hL := E.three_d_lt_Lα
  simp only [rval, E.g_read1]
  suffices key : (P.exec (pre (E.g w i) (E.Lα + (2 * i + 5)))).st =
      (P.exec (pre (E.g w' i) (E.Lα + (2 * i + 5)))).st by rw [key]
  have hpre : ∀ w : ℕ → Bool, pre (E.g w i) (E.Lα + (2 * i + 5)) = pre (E.act w) E.Lα ++
      (List.range (2 * i + 5)).map (E.suf w i) := by
    intro w
    rw [pre_add, pre_congr (g := E.g w i) (g' := E.act w) (n := E.Lα) (fun p hp => E.g_lt w i hp)]
    congr 1; apply List.map_congr_left; intro q _; exact E.g_suf w i q
  rw [hpre, hpre, Protocol.exec_append, Protocol.exec_append,
    List.map_congr_left (fun q _ => E.suf_congr h q)]
  apply Protocol.foldl_step_congr _ {s | s < 3 * i}
  · funext r
    by_cases hr : r = E.r1
    · subst hr; exact hσ
    · have h1 : ∀ w : ℕ → Bool, ∀ a ∈ pre (E.act w) E.Lα, a.rep ≠ r := by
        intro w a ha; simp only [pre, List.mem_map] at ha
        obtain ⟨p, -, rfl⟩ := ha; rw [E.act_rep]; exact Ne.symm hr
      rw [Protocol.exec_st_of_not_acting _ r (h1 w), Protocol.exec_st_of_not_acting _ r (h1 w')]
  · simp
  · intro s hs
    simp only [Set.mem_setOf_eq] at hs
    rw [← Protocol.exec_sent_getElem?_take _ (n := 3 * i) hs,
      ← Protocol.exec_sent_getElem?_take (pre (E.act w') E.Lα) (n := 3 * i) hs, pre_take, pre_take,
      min_eq_left (by omega), pre_congr (g := E.act w) (g' := E.act w') (n := 3 * i) (fun p hp => E.act_congr hi h hp)]
  · intro a ha s hs
    simp only [List.mem_map, List.mem_range] at ha
    obtain ⟨q, hq, rfl⟩ := ha
    rcases hsuf : E.suf w' i q with ⟨r, op⟩ | r | ⟨r, src⟩ <;> rw [hsuf] at hs <;>
      simp only [Act.src?_doOp, Act.src?_send, Act.src?_recv, reduceCtorEq,
        Option.some.injEq] at hs
    subst hs
    simp only [Set.mem_setOf_eq, Protocol.exec_sent_length, length_pre]
    rcases (E.suf_recv_iff w' i).1 hsuf with
      ⟨t, ht, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨t, ht, h1, -⟩ | ⟨h1, -⟩ |
        ⟨t, ht, h1, -⟩
    · left; rw [mpos_eq_send E (by omega)]; omega
    · left; rw [mpos_eq_send E (by omega)]; omega
    · right; unfold pmx; omega
    · right; unfold pmx; omega
    all_goals omega

/-- **Decoding.** The state of `R₁` at the end of `α_w` determines the bits `w₁ … w_d`. -/
theorem state_determines_bits (hP : PushBased P Weak (LBAdm P)) {w w' : ℕ → Bool}
    (hσ : (P.exec (pre (E.act w) E.Lα)).st E.r1 = (P.exec (pre (E.act w') E.Lα)).st E.r1) :
    ∀ j, 1 ≤ j → j ≤ E.d → w j = w' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj1 hjd
    have hy := E.y_congr (P := P) hj1 hjd (fun t h1 h2 => ih t h2 h1 (by omega)) hσ
    have h1 := E.recover_correct (w := w) hP hj1 hjd
    have h2 := E.recover_correct (w := w') hP hj1 hjd
    rw [hy] at h1
    exact Bool.eq_iff_iff.2 (h1.symm.trans h2)

end Params

end Podc.CollaborativeListSpec
