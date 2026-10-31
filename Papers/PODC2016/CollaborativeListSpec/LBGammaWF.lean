import Papers.PODC2016.CollaborativeListSpec.LBAlpha
import Papers.PODC2016.CollaborativeListSpec.EncodingSuf

/-!
# `γ_w^i` is a well-formed execution with causal atomic broadcast (Claims 10 and 11)
-/

namespace Podc.CollaborativeListSpec

namespace Params

variable {Rep U Q M : Type} [DecidableEq Rep] [DecidableEq U] {P : Protocol Rep (LOp U) (List U) Q M}
  (E : Params Rep U) (w : ℕ → Bool) (i : ℕ)

theorem g_rep_lt {q : ℕ} (h : q < E.Lα) : (E.g w i q).rep = E.r1 := by
  rw [E.g_lt w i h]; exact E.act_rep w q

theorem g_recv_iff {q : ℕ} {r : Rep} {s : ℕ} :
    E.g w i q = .recv r s ↔ E.Lα ≤ q ∧ E.suf w i (q - E.Lα) = .recv r s := by
  rw [g]; split_ifs with h
  · simp only [E.act_ne_recv w, false_iff, not_and]; omega
  · simp; omega

theorem g_send_iff {q : ℕ} {r : Rep} :
    E.g w i q = .send r ↔ (q < E.Lα ∧ E.act w q = .send r) ∨ (q = E.pmx i ∧ r = E.r2) := by
  rw [g]; split_ifs with h
  · constructor
    · exact fun h' => Or.inl ⟨h, h'⟩
    · rintro (⟨-, h'⟩ | ⟨rfl, -⟩)
      · exact h'
      · unfold pmx at h; omega
  · rw [suf_send_iff]
    constructor
    · rintro ⟨h1, rfl⟩; exact Or.inr ⟨by unfold pmx; omega, rfl⟩
    · rintro (⟨h', -⟩ | ⟨rfl, rfl⟩)
      · omega
      · unfold pmx; exact ⟨by omega, rfl⟩

theorem g_pmx : E.g w i (E.pmx i) = .send E.r2 := (E.g_send_iff w i).2 (Or.inr ⟨rfl, rfl⟩)

theorem pmx_lt_Lγ : E.pmx i < E.Lγ i := by unfold pmx Lγ; omega

theorem Lα_le_pmx : E.Lα < E.pmx i := by unfold pmx; omega

theorem three_d_lt_Lα : 3 * E.d + 4 < E.Lα := by rw [Lα_eq]; omega

/-- The send events of `γ_w^i`. -/
theorem isSend_γ_iff {s : ℕ} : IsSend (E.γ w i) s ↔
    (∃ t ≤ E.d, s = 3 * t + 2) ∨ s = 3 * E.d + 4 ∨ s = E.Lα - 1 ∨ s = E.pmx i := by
  have hL := E.three_d_lt_Lα
  unfold IsSend γ
  simp only [pre_getElem?]
  constructor
  · rintro ⟨r, h⟩
    split_ifs at h with hs
    have h := Option.some.inj h
    rcases (E.g_send_iff w i).1 h with ⟨hs', h'⟩ | ⟨rfl, -⟩
    · obtain ⟨-, h⟩ := (E.act_send_iff w hs').1 h'
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · have hp := E.pmx_lt_Lγ i
    have hLγ : E.Lα ≤ E.Lγ i := by unfold Lγ; omega
    rintro (⟨t, ht, rfl⟩ | rfl | rfl | rfl)
    · refine ⟨E.r1, ?_⟩
      rw [if_pos (by omega), E.g_lt w i (by omega), E.act_send w ht]
    · refine ⟨E.r1, ?_⟩
      rw [if_pos (by omega), E.g_lt w i (by omega), E.act_send_star w]
    · refine ⟨E.r1, ?_⟩
      have : 0 < E.Lα := by omega
      rw [if_pos (by omega), E.g_lt w i (by omega), E.act_last w]
    · exact ⟨E.r2, by rw [if_pos hp, E.g_pmx]⟩

/-- The rank of a message in the broadcast order `m₁ … mᵢ mₓ m_{i+1} … m_{d+3}`. -/
def rk (s : ℕ) : ℕ :=
  if s = E.pmx i then i else if s = 3 * E.d + 4 then E.d + 2 else if s = E.Lα - 1 then E.d + 3
  else if (s + 1) / 3 ≤ i then (s + 1) / 3 - 1 else (s + 1) / 3

/-- How many messages each replica receives in `γ_w^i`. -/
def cnt (r : Rep) : ℕ := if r = E.r1 ∨ r = E.r2 then i + 1 else if r = E.r3 then E.d + 3 else 0

/-- Where replica `r` receives its `k`-th message in `γ_w^i`. -/
def rpos (r : Rep) (k : ℕ) : ℕ :=
  if r = E.r2 then (if k < i then E.Lα + 2 * k else E.Lα + 2 * i + 3)
  else if r = E.r1 then (if k < i then E.Lα + 2 * k + 1 else E.Lα + 2 * i + 4)
  else if k < i then E.Lα + 2 * i + 6 + k else if k = i then E.Lα + 3 * i + 6
  else E.Lα + 3 * i + 7 + (k - i - 1)

theorem cnt_r1 : E.cnt i E.r1 = i + 1 := by simp [cnt]
theorem cnt_r2 : E.cnt i E.r2 = i + 1 := by simp [cnt]
theorem cnt_r3 : E.cnt i E.r3 = E.d + 3 := by simp [cnt, Ne.symm E.h13, Ne.symm E.h23]
theorem rpos_r2 (k : ℕ) :
    E.rpos i E.r2 k = if k < i then E.Lα + 2 * k else E.Lα + 2 * i + 3 := by simp [rpos]
theorem rpos_r1 (k : ℕ) :
    E.rpos i E.r1 k = if k < i then E.Lα + 2 * k + 1 else E.Lα + 2 * i + 4 := by
  simp [rpos, E.h12]
theorem rpos_r3 (k : ℕ) : E.rpos i E.r3 k = if k < i then E.Lα + 2 * i + 6 + k else
    if k = i then E.Lα + 3 * i + 6 else E.Lα + 3 * i + 7 + (k - i - 1) := by
  simp [rpos, Ne.symm E.h13, Ne.symm E.h23]

variable {i}

theorem rk_send {t : ℕ} (ht : t ≤ E.d) :
    E.rk i (3 * t + 2) = if t < i then t else t + 1 := by
  have := E.three_d_lt_Lα
  unfold rk pmx
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  split_ifs <;> omega

theorem rk_mpos (hi : i ≤ E.d) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ E.d + 2) :
    E.rk i (E.mpos j) = if j ≤ i then j - 1 else j := by
  unfold mpos
  split_ifs with h1 h2 h2
  · rw [show 3 * j - 1 = 3 * (j - 1) + 2 by omega, rk_send E (by omega), if_pos (by omega)]
  · rw [show 3 * j - 1 = 3 * (j - 1) + 2 by omega, rk_send E (by omega), if_neg (by omega)]; omega
  · omega
  · have := E.three_d_lt_Lα
    unfold rk pmx; rw [if_neg (by omega), if_pos rfl]; omega

theorem rk_pmx : E.rk i (E.pmx i) = i := by unfold rk; rw [if_pos rfl]

theorem rk_last : E.rk i (E.Lα - 1) = E.d + 3 := by
  have : 5 * E.d + 8 ≤ E.Lα := by rw [Lα_eq]; omega
  unfold rk pmx; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem rk_star : E.rk i (3 * E.d + 4) = E.d + 2 := by
  have := E.three_d_lt_Lα
  unfold rk; rw [if_neg (by unfold pmx; omega), if_pos rfl]

theorem mpos_eq_send {t : ℕ} (ht : t ≤ E.d) : E.mpos (t + 1) = 3 * t + 2 := by
  rw [mpos_of_le E (by omega)]; omega

/-- A send of `γ_w^i` is determined by its rank. -/
theorem send_of_rank (hi1 : 1 ≤ i) (hi : i ≤ E.d) {s : ℕ} (hs : IsSend (E.γ w i) s) :
    (E.rk i s < i ∧ s = E.mpos (E.rk i s + 1)) ∨ (E.rk i s = i ∧ s = E.pmx i) ∨
      (i < E.rk i s ∧ E.rk i s ≤ E.d + 2 ∧ s = E.mpos (E.rk i s)) ∨
      (E.rk i s = E.d + 3 ∧ s = E.Lα - 1) := by
  rcases (E.isSend_γ_iff w i).1 hs with ⟨t, ht, rfl⟩ | rfl | rfl | rfl
  · rw [rk_send E ht]
    split_ifs with h
    · exact Or.inl ⟨h, (mpos_eq_send E ht).symm⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, (mpos_eq_send E ht).symm⟩))
  · rw [rk_star]; exact Or.inr (Or.inr (Or.inl ⟨by omega, le_rfl, (mpos_top E).symm⟩))
  · rw [rk_last]; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · rw [rk_pmx]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)

theorem γ_getElem? (q : ℕ) :
    (E.γ w i)[q]? = if q < E.Lγ i then some (E.g w i q) else none := pre_getElem? _ _ _

theorem isSend_mpos (hi : i ≤ E.d) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ E.d + 2) :
    IsSend (E.γ w i) (E.mpos j) := by
  rw [isSend_γ_iff]
  rcases Nat.lt_or_ge j (E.d + 2) with h | h
  · obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
    exact Or.inl ⟨t, by omega, mpos_eq_send E (by omega)⟩
  · obtain rfl : j = E.d + 2 := by omega
    exact Or.inr (Or.inl (mpos_top E))

theorem isSend_pmx : IsSend (E.γ w i) (E.pmx i) := by
  rw [isSend_γ_iff]; exact Or.inr (Or.inr (Or.inr rfl))

/-- **Claim 11.** `γ_w^i` (hence `β_w^i`) satisfies causal atomic broadcast. -/
theorem causalAtomic_γ (hi1 : 1 ≤ i) (hi : i ≤ E.d) : CausalAtomic (E.γ w i) := by
  have hL := E.three_d_lt_Lα
  have hL2 : 5 * E.d + 8 ≤ E.Lα := by rw [Lα_eq]; omega
  have hp : E.pmx i = E.Lα + 2 * i + 2 := rfl
  have hLγ : E.Lγ i = E.Lα + 2 * i + E.d + 10 := rfl
  have h12 := E.h12; have h13 := E.h13; have h23 := E.h23
  apply causalAtomic_of_rank (E.rk i) (E.cnt i) (E.rpos i)
  · -- monotonicity
    intro r k k' hk hk'
    unfold rpos cnt at *
    split_ifs at * <;> first | omega | (exfalso; simp_all)
  · -- the receive events
    intro q r s
    rw [γ_getElem?]
    constructor
    · intro h
      split_ifs at h with hq
      have h := Option.some.inj h
      obtain ⟨hLq, h⟩ := (E.g_recv_iff w i).1 h
      obtain ⟨q', rfl⟩ : ∃ q', q = E.Lα + q' := ⟨q - E.Lα, by omega⟩
      rw [Nat.add_sub_cancel_left] at h
      rcases (E.suf_recv_iff w i).1 h with
        ⟨t, ht, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨t, ht, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨t, ht, rfl, rfl, rfl⟩
      · refine ⟨t, by rw [cnt_r2]; omega, by rw [rpos_r2, if_pos ht], E.isSend_mpos w hi
          (by omega) (by omega), by rw [rk_mpos E hi (by omega) (by omega), if_pos (by omega)]; rfl⟩
      · refine ⟨t, by rw [cnt_r1]; omega, by rw [rpos_r1, if_pos ht]; omega, E.isSend_mpos w hi
          (by omega) (by omega), by rw [rk_mpos E hi (by omega) (by omega), if_pos (by omega)]; rfl⟩
      · exact ⟨i, by rw [cnt_r2]; omega, by rw [rpos_r2, if_neg (by omega)]; omega,
          E.isSend_pmx w, rk_pmx E⟩
      · exact ⟨i, by rw [cnt_r1]; omega, by rw [rpos_r1, if_neg (by omega)]; omega,
          E.isSend_pmx w, rk_pmx E⟩
      · refine ⟨t, by rw [cnt_r3]; omega, by rw [rpos_r3, if_pos ht]; omega, E.isSend_mpos w hi
          (by omega) (by omega), by rw [rk_mpos E hi (by omega) (by omega), if_pos (by omega)]; rfl⟩
      · exact ⟨i, by rw [cnt_r3]; omega, by rw [rpos_r3, if_neg (by omega), if_pos rfl]; omega,
          E.isSend_pmx w, rk_pmx E⟩
      · refine ⟨i + 1 + t, by rw [cnt_r3]; omega,
          by rw [rpos_r3, if_neg (by omega), if_neg (by omega)]; omega, E.isSend_mpos w hi
          (by omega) (by omega), by rw [rk_mpos E hi (by omega) (by omega), if_neg (by omega)]⟩
    · rintro ⟨k, hk, rfl, hs, rfl⟩
      have hsend := E.send_of_rank w hi1 hi hs
      have key : ∀ q', q' < 2 * i + E.d + 10 → E.suf w i q' = .recv r s →
          E.Lα + q' = E.rpos i r (E.rk i s) →
          (if E.rpos i r (E.rk i s) < E.Lγ i then some (E.g w i (E.rpos i r (E.rk i s))) else none)
            = some (Act.recv r s) := by
        intro q' hq' h1 h2
        rw [← h2, if_pos (by omega), g_suf, h1]
      by_cases hr2 : r = E.r2
      · subst hr2
        rw [cnt_r2] at hk
        rcases hsend with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
        · exact key (2 * E.rk i s) (by omega) ((E.suf_recv_iff w i).2
            (Or.inl ⟨_, h1, Or.inl ⟨rfl, rfl, h2⟩⟩)) (by rw [rpos_r2, if_pos h1])
        · exact key (2 * i + 3) (by omega) ((E.suf_recv_iff w i).2
            (Or.inr (Or.inl ⟨rfl, rfl, h2⟩))) (by rw [rpos_r2, if_neg (by omega)]; omega)
        · omega
        · omega
      by_cases hr1 : r = E.r1
      · subst hr1
        rw [cnt_r1] at hk
        rcases hsend with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
        · exact key (2 * E.rk i s + 1) (by omega) ((E.suf_recv_iff w i).2
            (Or.inl ⟨_, h1, Or.inr ⟨rfl, rfl, h2⟩⟩)) (by rw [rpos_r1, if_pos h1]; omega)
        · exact key (2 * i + 4) (by omega) ((E.suf_recv_iff w i).2
            (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h2⟩)))) (by rw [rpos_r1, if_neg (by omega)]; omega)
        · omega
        · omega
      by_cases hr3 : r = E.r3
      · subst hr3
        rw [cnt_r3] at hk
        rcases hsend with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h1', h2⟩ | ⟨h1, -⟩
        · exact key (2 * i + 6 + E.rk i s) (by omega) ((E.suf_recv_iff w i).2
            (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, h1, rfl, rfl, h2⟩)))))
            (by rw [rpos_r3, if_pos h1]; omega)
        · exact key (3 * i + 6) (by omega) ((E.suf_recv_iff w i).2
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h2⟩))))))
            (by rw [rpos_r3, if_neg (by omega), if_pos h1]; omega)
        · refine key (3 * i + 7 + (E.rk i s - i - 1)) (by omega) ((E.suf_recv_iff w i).2
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, by omega, rfl, rfl, ?_⟩)))))) ?_
          · rw [show i + 1 + (E.rk i s - i - 1) = E.rk i s by omega]; exact h2
          · rw [rpos_r3, if_neg (by omega), if_neg (by omega)]; omega
        · omega
      · simp [cnt, hr1, hr2, hr3] at hk
  · -- ranks are injective on sends
    intro s s' hs hs' heq
    rcases E.send_of_rank w hi1 hi hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h1', h2⟩ | ⟨h1, h2⟩ <;>
    rcases E.send_of_rank w hi1 hi hs' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h1'', h2'⟩ | ⟨h1', h2'⟩ <;>
    first | omega | (rw [h2, h2', heq])
  · -- happens-before between sends respects ranks
    intro s s' hs hs' hss
    have hlt := hss.lt
    rcases (E.isSend_γ_iff w i).1 hs' with ⟨t', ht', rfl⟩ | rfl | rfl | rfl
    · rcases (E.isSend_γ_iff w i).1 hs with ⟨t, ht, rfl⟩ | rfl | rfl | rfl
      · rw [rk_send E ht, rk_send E ht']; split_ifs <;> omega
      · omega
      · omega
      · omega
    · rcases (E.isSend_γ_iff w i).1 hs with ⟨t, ht, rfl⟩ | rfl | rfl | rfl
      · rw [rk_send E ht, rk_star]; split_ifs <;> omega
      · omega
      · omega
      · omega
    · rcases (E.isSend_γ_iff w i).1 hs with ⟨t, ht, rfl⟩ | rfl | rfl | rfl
      · rw [rk_send E ht, rk_last]; split_ifs <;> omega
      · rw [rk_star, rk_last]; omega
      · omega
      · omega
    · -- `s' = mₓ`: only `m₁ … mᵢ` happen before it
      have hS : ∀ q p, Imm (E.γ w i) q p →
          p ∈ {q | q < 3 * i ∨ (E.Lα ≤ q ∧ q ≤ E.pmx i ∧ (E.g w i q).rep = E.r2)} →
          q ∈ {q | q < 3 * i ∨ (E.Lα ≤ q ∧ q ≤ E.pmx i ∧ (E.g w i q).rep = E.r2)} := by
        rintro q p ⟨hqp, a, b, ha, hb, hab⟩ hp
        rw [γ_getElem?] at ha hb
        split_ifs at ha hb with h1 h2
        obtain rfl := Option.some.inj ha
        obtain rfl := Option.some.inj hb
        simp only [Set.mem_setOf_eq] at hp ⊢
        rcases hp with hp | ⟨hp1, hp2, hp3⟩
        · exact Or.inl (by omega)
        rcases hab with hab | hab
        · rw [hp3] at hab
          by_cases hqL : q < E.Lα
          · rw [E.g_rep_lt w i hqL] at hab; exact absurd hab E.h12
          · exact Or.inr ⟨by omega, by omega, hab⟩
        · rcases hgp : E.g w i p with ⟨r, op⟩ | r | ⟨r, src⟩ <;> rw [hgp] at hab <;>
            simp only [Act.src?_doOp, Act.src?_send, Act.src?_recv, reduceCtorEq,
              Option.some.injEq] at hab
          subst hab
          obtain ⟨-, h⟩ := (E.g_recv_iff w i).1 hgp
          rcases (E.suf_recv_iff w i).1 h with
            ⟨t, ht, ⟨h, -, rfl⟩ | ⟨h, -, rfl⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨t, ht, h, -⟩ | ⟨h, -⟩ | ⟨t, ht, h, -⟩
          · left; rw [mpos_eq_send E (by omega)]; omega
          · left; rw [mpos_eq_send E (by omega)]; omega
          all_goals (unfold pmx at hp2; omega)
      have hmem := hss.mem_of_closed hS (Or.inr ⟨(E.Lα_le_pmx i).le, le_rfl, by rw [g_pmx]; rfl⟩)
      simp only [Set.mem_setOf_eq] at hmem
      rw [rk_pmx]
      rcases (E.isSend_γ_iff w i).1 hs with ⟨t, ht, rfl⟩ | rfl | rfl | rfl
      · rw [rk_send E ht]; split_ifs <;> omega
      · omega
      · omega
      · omega

theorem γ_eq_take (n : ℕ) (hn : n ≤ E.Lγ i) : pre (E.g w i) n = (E.γ w i).take n := by
  rw [γ, pre_take, min_eq_left hn]

/-- **Claim 10.** Every prefix of `γ_w^i` is a well-formed admitted execution. -/
theorem gamma_ok (hP : PushBased P Weak (LBAdm P)) (hi1 : 1 ≤ i) (hi : i ≤ E.d) :
    ∀ n ≤ E.Lγ i, P.WF (pre (E.g w i) n) ∧ LBAdm P (pre (E.g w i) n) := by
  have hca := E.causalAtomic_γ w hi1 hi
  have huniq : ∀ n, UniqueIns (pre (E.g w i) n) := by
    intro n
    refine E.uniqueIns_of_insAt (i := i) (fun q _ r x k h => ?_)
    by_cases hq : q < E.Lα
    · rw [E.g_lt w i hq] at h; exact E.insAt_of_act w h
    · rw [g, if_neg hq] at h
      rcases (E.suf_doOp_iff w i hi).1 h with ⟨-, -, h⟩ | ⟨h1, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;>
        simp only [reduceCtorEq, LOp.ins.injEq] at h
      exact Or.inr (Or.inr (Or.inr ⟨by omega, h.1⟩))
  intro n
  induction n with
  | zero =>
    intro hn
    have := E.alpha_ok (w := w) hP 0 (Nat.zero_le _)
    rwa [show pre (E.g w i) 0 = pre (E.act w) 0 from rfl]
  | succ n ih =>
    intro hn
    by_cases hnL : n + 1 ≤ E.Lα
    · rw [pre_congr (g := E.g w i) (g' := E.act w) (n := n + 1) (fun p hp => E.g_lt w i (by omega))]
      exact E.alpha_ok hP _ hnL
    obtain ⟨hwf, hadm⟩ := ih (by omega)
    have hgn : E.g w i n = E.suf w i (n - E.Lα) := by rw [g, if_neg (by omega)]
    refine ⟨WF_pre_succ.2 ⟨hwf, ?_⟩, ?_, huniq _, DelOK_pre_succ hadm.2.2 ?_⟩
    · rcases hact : E.g w i n with ⟨r, op⟩ | r | ⟨r, src⟩
      · trivial
      · rw [hgn] at hact
        obtain ⟨h1, rfl⟩ := (E.suf_send_iff w i).1 hact
        have hins : (pre (E.g w i) n)[n - 1]? = some (.doOp E.r2 (.ins E.X (E.lenA w (i - 1) + 1))) := by
          rw [pre_getElem?_of_lt _ (by omega), g, if_neg (by omega),
            show n - 1 - E.Lα = 2 * i + 1 by omega, suf_insX]
        obtain ⟨-, h⟩ := hP.ins _ hwf hadm _ _ _ _ hins
        show ((P.exec (pre (E.g w i) n)).st E.r2).2.isSome
        rwa [pre_take, min_eq_left (by omega), show n - 1 + 1 = n by omega] at h
      · rw [hgn] at hact
        show src < n ∧ ∃ r', (pre (E.g w i) (n + 1))[src]? = some (.send r')
        have hsend : ∀ s, IsSend (E.γ w i) s → s < n → ∃ r', (pre (E.g w i) (n + 1))[s]? = some (.send r') := by
          rintro s ⟨r', h⟩ hs
          refine ⟨r', ?_⟩
          rw [γ_getElem?] at h; split_ifs at h with h'
          rw [pre_getElem?_of_lt _ (by omega), h]
        have hL := E.three_d_lt_Lα
        rcases (E.suf_recv_iff w i).1 hact with
          ⟨t, ht, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩⟩ | ⟨h, -, rfl⟩ | ⟨h, -, rfl⟩ | ⟨t, ht, -, -, rfl⟩ |
            ⟨h, -, rfl⟩ | ⟨t, ht, -, -, rfl⟩
        all_goals first
          | (have hlt : E.mpos (t + 1) < n := by rw [mpos_eq_send E (by omega)]; omega
             exact ⟨hlt, hsend _ (E.isSend_mpos w hi (by omega) (by omega)) hlt⟩)
          | (have hlt : E.pmx i < n := by unfold pmx; omega
             exact ⟨hlt, hsend _ (E.isSend_pmx w) hlt⟩)
          | (have hlt : E.mpos (i + 1 + t) < n := by unfold mpos; split_ifs <;> omega
             exact ⟨hlt, hsend _ (E.isSend_mpos w hi (by omega) (by omega)) hlt⟩)
    · rw [E.γ_eq_take w _ hn]; exact hca.take _
    · intro r a h
      rw [hgn] at h
      rcases (E.suf_doOp_iff w i hi).1 h with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;>
        simp at h

end Params

end Podc.CollaborativeListSpec
