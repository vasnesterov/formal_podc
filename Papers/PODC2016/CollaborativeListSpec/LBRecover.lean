import Papers.PODC2016.CollaborativeListSpec.LBGammaWF

/-!
# Correctness of `Recover` (Claims 12, 13 and the final argument of Theorem 9)

In `γ_w^i`, with the abstract execution whose visibility is happens-before (push-based, third
condition), `R₁`'s read after receiving `m₁ … mᵢ, mₓ` returns `[x, ∗]` iff `wᵢ = 1`.
-/

namespace Podc.CollaborativeListSpec

variable {Rep U Q M : Type} [DecidableEq Rep] [DecidableEq U] {P : Protocol Rep (LOp U) (List U) Q M}

theorem rel_of_pairwise_pair {R : U → U → Prop} {l : List U} {a b : U} (h : l.Pairwise R)
    (hs : [a, b].Sublist l) : R a b := by
  have := h.sublist hs; simpa using this

theorem eq_pair_of_mem {l : List U} {a b : U} (hl : l.Nodup) (hab : a ≠ b)
    (hm : ∀ x, x ∈ l ↔ x = a ∨ x = b) : l = [a, b] ∨ l = [b, a] := by
  have hp : l.Perm [a, b] := by
    rw [List.perm_ext_iff_of_nodup hl (by simp [hab])]; intro x; rw [hm]; simp
  have hlen := hp.length_eq
  match l, hlen with
  | [c, e], _ =>
    have hc := (hm c).1 (by simp)
    have he := (hm e).1 (by simp)
    have hce : c ≠ e := by simpa using hl
    rcases hc with rfl | rfl <;> rcases he with rfl | rfl
    · exact absurd rfl hce
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hce

namespace Params

variable (E : Params Rep U) {w : ℕ → Bool} {i : ℕ}

theorem γ_get {q : ℕ} (hq : q < E.Lγ i) : (E.γ w i)[q]? = some (E.g w i q) := by
  rw [γ_getElem?, if_pos hq]

theorem hb_ro {q p : ℕ} (hqp : q < p) (hp : p < E.Lγ i) (h : (E.g w i q).rep = (E.g w i p).rep) :
    HB (E.γ w i) q p :=
  HB.of_rep hqp (E.γ_get (by omega)) (E.γ_get hp) h

theorem hb_recv {q p : ℕ} {r : Rep} (hqp : q < p) (hp : p < E.Lγ i) (h : E.g w i p = .recv r q) :
    HB (E.γ w i) q p :=
  HB.of_recv hqp (E.γ_get (by omega)) (by rw [E.γ_get hp, h])

theorem insVis_iff {p : ℕ} {r : Rep} {op : LOp U} (hp : p < E.Lγ i) (hg : E.g w i p = .doOp r op)
    (x : U) : InsVis (P.hist (E.γ w i)) (visHB (E.γ w i)) p x ↔
      ∃ q, (q = p ∨ HB (E.γ w i) q p) ∧ q < E.Lγ i ∧ ∃ r' k, E.g w i q = .doOp r' (.ins x k) := by
  constructor
  · rintro ⟨q, r', k, v, hv, hq⟩
    obtain ⟨hql, hgq, -⟩ := hist_pre_eq_some hq
    exact ⟨q, hv.imp_right (fun h => h.1), hql, r', k, hgq⟩
  · rintro ⟨q, hv, hql, r', k, hgq⟩
    refine ⟨q, r', k, _, ?_, hist_pre_eq hql hgq⟩
    rcases hv with rfl | hv
    · exact Or.inl rfl
    · exact Or.inr ⟨hv, ⟨_, _, E.γ_get hql |>.trans (by rw [hgq])⟩, ⟨_, _, E.γ_get hp |>.trans (by rw [hg])⟩⟩

theorem delVis_iff {p : ℕ} {r : Rep} {op : LOp U} (hp : p < E.Lγ i) (hg : E.g w i p = .doOp r op)
    (x : U) : DelVis (P.hist (E.γ w i)) (visHB (E.γ w i)) p x ↔
      ∃ q, (q = p ∨ HB (E.γ w i) q p) ∧ q < E.Lγ i ∧ ∃ r', E.g w i q = .doOp r' (.del x) := by
  constructor
  · rintro ⟨q, r', v, hv, hq⟩
    obtain ⟨hql, hgq, -⟩ := hist_pre_eq_some hq
    exact ⟨q, hv.imp_right (fun h => h.1), hql, r', hgq⟩
  · rintro ⟨q, hv, hql, r', hgq⟩
    refine ⟨q, r', _, ?_, hist_pre_eq hql hgq⟩
    rcases hv with rfl | hv
    · exact Or.inl rfl
    · exact Or.inr ⟨hv, ⟨_, _, E.γ_get hql |>.trans (by rw [hgq])⟩, ⟨_, _, E.γ_get hp |>.trans (by rw [hg])⟩⟩

/-- Events that happen before `R₂`'s events up to position `B ≤ pos(mₓ)`: the prefix of `α_w`
before `send mᵢ` and earlier events of `R₂`. -/
theorem closed_R2 (hi : i ≤ E.d) {B : ℕ} (hB : B ≤ E.pmx i) :
    ∀ q p, Imm (E.γ w i) q p →
      p ∈ {q | q < 3 * i ∨ (E.Lα ≤ q ∧ q ≤ B ∧ (E.g w i q).rep = E.r2)} →
      q ∈ {q | q < 3 * i ∨ (E.Lα ≤ q ∧ q ≤ B ∧ (E.g w i q).rep = E.r2)} := by
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
    all_goals (unfold pmx at hB; omega)

/-- Events that happen before `R₂`'s and `R₃`'s events: no deletion is among them. -/
theorem closed_R23 (hi : i ≤ E.d) :
    ∀ q p, Imm (E.γ w i) q p →
      p ∈ {q | q < 3 * E.d + 5 ∨ (E.Lα ≤ q ∧ ((E.g w i q).rep = E.r2 ∨ (E.g w i q).rep = E.r3))} →
      q ∈ {q | q < 3 * E.d + 5 ∨ (E.Lα ≤ q ∧ ((E.g w i q).rep = E.r2 ∨ (E.g w i q).rep = E.r3))} := by
  have hL := E.three_d_lt_Lα
  rintro q p ⟨hqp, a, b, ha, hb, hab⟩ hp
  rw [γ_getElem?] at ha hb
  split_ifs at ha hb with h1 h2
  obtain rfl := Option.some.inj ha
  obtain rfl := Option.some.inj hb
  simp only [Set.mem_setOf_eq] at hp ⊢
  rcases hp with hp | ⟨hp1, hp3⟩
  · exact Or.inl (by omega)
  rcases hab with hab | hab
  · rw [hab]
    by_cases hqL : q < E.Lα
    · rw [E.g_rep_lt w i hqL] at hab
      rcases hp3 with h | h <;> rw [h] at hab
      · exact absurd hab E.h12
      · exact absurd hab E.h13
    · exact Or.inr ⟨by omega, hp3⟩
  · rcases hgp : E.g w i p with ⟨r, op⟩ | r | ⟨r, src⟩ <;> rw [hgp] at hab <;>
      simp only [Act.src?_doOp, Act.src?_send, Act.src?_recv, reduceCtorEq,
        Option.some.injEq] at hab
    subst hab
    rw [hgp] at hp3; simp only [Act.rep_recv] at hp3
    obtain ⟨-, h⟩ := (E.g_recv_iff w i).1 hgp
    have hpmx : E.Lα ≤ E.pmx i ∧ (E.g w i (E.pmx i)).rep = E.r2 := ⟨(E.Lα_le_pmx i).le, by rw [g_pmx]; rfl⟩
    rcases (E.suf_recv_iff w i).1 h with
      ⟨t, ht, ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨t, ht, -, rfl, rfl⟩ |
        ⟨-, rfl, rfl⟩ | ⟨t, ht, -, rfl, rfl⟩
    · left; rw [mpos_eq_send E (by omega)]; omega
    · exfalso; rcases hp3 with h | h; exact E.h12 h; exact E.h13 h
    · exact Or.inr ⟨hpmx.1, Or.inl hpmx.2⟩
    · exfalso; rcases hp3 with h | h; exact E.h12 h; exact E.h13 h
    · left; rw [mpos_eq_send E (by omega)]; omega
    · exact Or.inr ⟨hpmx.1, Or.inl hpmx.2⟩
    · left; unfold mpos; split_ifs <;> omega

section Pos

variable (w i)

theorem g_recv2 {t : ℕ} (ht : t < i) : E.g w i (E.Lα + 2 * t) = .recv E.r2 (E.mpos (t + 1)) := by
  rw [g_suf, suf_recv_iff]; exact Or.inl ⟨t, ht, Or.inl ⟨rfl, rfl, rfl⟩⟩
theorem g_recv1 {t : ℕ} (ht : t < i) :
    E.g w i (E.Lα + (2 * t + 1)) = .recv E.r1 (E.mpos (t + 1)) := by
  rw [g_suf, suf_recv_iff]; exact Or.inl ⟨t, ht, Or.inr ⟨rfl, rfl, rfl⟩⟩
theorem g_recv1x : E.g w i (E.Lα + (2 * i + 4)) = .recv E.r1 (E.pmx i) := by
  rw [g_suf, suf_recv_iff]; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
theorem g_recv3 {t : ℕ} (ht : t < i) :
    E.g w i (E.Lα + (2 * i + 6 + t)) = .recv E.r3 (E.mpos (t + 1)) := by
  rw [g_suf, suf_recv_iff]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t, ht, rfl, rfl, rfl⟩)))
theorem g_recv3x : E.g w i (E.Lα + (3 * i + 6)) = .recv E.r3 (E.pmx i) := by
  rw [g_suf, suf_recv_iff]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
theorem g_recv3' {t : ℕ} (ht : t < E.d + 2 - i) :
    E.g w i (E.Lα + (3 * i + 7 + t)) = .recv E.r3 (E.mpos (i + 1 + t)) := by
  rw [g_suf, suf_recv_iff]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨t, ht, rfl, rfl, rfl⟩))))
theorem g_read2 : E.g w i (E.Lα + 2 * i) = .doOp E.r2 .read := by rw [g_suf, suf_read2]
theorem g_insX : E.g w i (E.Lα + (2 * i + 1)) = .doOp E.r2 (.ins E.X (E.lenA w (i - 1) + 1)) := by
  rw [g_suf, suf_insX]
theorem g_read1 : E.g w i (E.Lα + (2 * i + 5)) = .doOp E.r1 .read := by rw [g_suf, suf_read1]
theorem g_read3 (hi : i ≤ E.d) : E.g w i (E.Lα + (2 * i + E.d + 9)) = .doOp E.r3 .read := by
  rw [g_suf, suf_read3 E w i hi]

end Pos

theorem g_ins_iff (hi : i ≤ E.d) {q : ℕ} {r : Rep} {x : U} {k : ℕ} (h : E.g w i q = .doOp r (.ins x k)) :
    (q < E.Lα ∧ E.act w q = .doOp r (.ins x k)) ∨ (q = E.Lα + (2 * i + 1) ∧ x = E.X) := by
  by_cases hq : q < E.Lα
  · rw [E.g_lt w i hq] at h; exact Or.inl ⟨hq, h⟩
  · rw [g, if_neg hq] at h
    rcases (E.suf_doOp_iff w i hi).1 h with ⟨-, -, h⟩ | ⟨h1, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;>
      simp only [reduceCtorEq, LOp.ins.injEq] at h
    exact Or.inr ⟨by omega, h.1⟩

theorem g_del_iff (hi : i ≤ E.d) {q : ℕ} {r : Rep} {x : U} (h : E.g w i q = .doOp r (.del x)) :
    q < E.Lα ∧ E.act w q = .doOp r (.del x) := by
  by_cases hq : q < E.Lα
  · rw [E.g_lt w i hq] at h; exact ⟨hq, h⟩
  · rw [g, if_neg hq] at h
    rcases (E.suf_doOp_iff w i hi).1 h with ⟨-, -, h⟩ | ⟨h1, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;>
      simp at h

/-- **Recover is correct.** In `γ_w^i`, `R₁`'s read `y` returns `[x, ∗]` iff `wᵢ = 1`
(Claims 12 and 13 and the argument with `R₃`'s read `z`). -/
theorem recover_correct (hP : PushBased P Weak (LBAdm P)) (hi1 : 1 ≤ i) (hi : i ≤ E.d) :
    rval P (E.g w i) (E.Lα + (2 * i + 5)) = [E.X, E.Star] ↔ w i = true := by
  have hL := E.three_d_lt_Lα
  have hL2 : 5 * E.d + 8 ≤ E.Lα := by rw [Lα_eq]; omega
  have hLγ : E.Lγ i = E.Lα + 2 * i + E.d + 10 := rfl
  have hpmx : E.pmx i = E.Lα + 2 * i + 2 := rfl
  obtain ⟨hwf, hadm⟩ := E.gamma_ok (w := w) hP hi1 hi _ le_rfl
  obtain ⟨lo, -, hc, hirr, htr⟩ := hP.spec _ hwf hadm
  have hc' : ListCond (P.hist (E.γ w i)) (visHB (E.γ w i)) lo := hc
  have resp : ∀ {p : ℕ} {r : Rep} {op : LOp U}, p < E.Lγ i → E.g w i p = .doOp r op →
      (∀ a, a ∈ rval P (E.g w i) p ↔ InsVis (P.hist (E.γ w i)) (visHB (E.γ w i)) p a ∧
        ¬ DelVis (P.hist (E.γ w i)) (visHB (E.γ w i)) p a) ∧ (rval P (E.g w i) p).Pairwise lo ∧
      (∀ a k, op = .ins a k → (rval P (E.g w i) p)[min k ((rval P (E.g w i) p).length - 1)]? = some a) :=
    fun hp hg => hc' _ _ _ _ (hist_pre_eq hp hg)
  have trans : ∀ {p : ℕ} {r : Rep} {op : LOp U}, p < E.Lγ i → E.g w i p = .doOp r op →
      ∀ a ∈ rval P (E.g w i) p, ∀ b ∈ rval P (E.g w i) p, ∀ c ∈ rval P (E.g w i) p,
        lo a b → lo b c → lo a c :=
    fun hp hg => (htr _ _ _ _ (hist_pre_eq hp hg)).1
  have hrv : ∀ p < E.Lα, rval P (E.g w i) p = rval P (E.act w) p :=
    fun p hp => rval_congr (fun q hq => E.g_lt w i (by omega))
  obtain ⟨hLj, hLs⟩ := E.rval_insert_phase (w := w) hP
  have rep1 : ∀ q < E.Lα, (E.g w i q).rep = E.r1 := fun q hq => E.g_rep_lt w i hq
  -- positions
  have hmi : E.mpos i = 3 * i - 1 := by rw [mpos_of_le E (by omega)]
  -- chains
  have to_recv2 : ∀ q < 3 * i - 1, HB (E.γ w i) q (E.Lα + 2 * (i - 1)) := by
    intro q hq
    refine (E.hb_ro (by omega) (by omega) (by rw [rep1 _ (by omega), rep1 _ (by omega)])).trans
      (E.hb_recv (p := E.Lα + 2 * (i - 1)) (q := 3 * i - 1) (r := E.r2) (by omega) (by omega) ?_)
    rw [E.g_recv2 w i (by omega), show i - 1 + 1 = i by omega, hmi]
  have to_recv3 : ∀ q < 3 * i - 1, HB (E.γ w i) q (E.Lα + (2 * i + 6 + (i - 1))) := by
    intro q hq
    refine (E.hb_ro (by omega) (by omega) (by rw [rep1 _ (by omega), rep1 _ (by omega)])).trans
      (E.hb_recv (q := 3 * i - 1) (r := E.r3) (by omega) (by omega) ?_)
    rw [E.g_recv3 w i (by omega), show i - 1 + 1 = i by omega, hmi]
  have hread2 := E.g_read2 w i
  have hinsX := E.g_insX w i
  have hread1 := E.g_read1 w i
  have hread3 := E.g_read3 w i hi
  have r2_le : ∀ q, q ∈ {q | q < 3 * i ∨ (E.Lα ≤ q ∧ q ≤ E.Lα + 2 * i ∧ (E.g w i q).rep = E.r2)} →
      (∀ r x k, E.g w i q = .doOp r (.ins x k) → x ∈ E.L w (i - 1)) ∧
      (∀ r x, E.g w i q ≠ .doOp r (.del x)) := by
    rintro q hq
    refine ⟨fun r x k h => ?_, fun r x h => ?_⟩
    · rcases E.g_ins_iff hi h with ⟨hqL, h⟩ | ⟨rfl, -⟩
      · rcases hq with hq | ⟨h1, -, -⟩
        · rw [mem_L]
          obtain ⟨-, ⟨t, ht, ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩⟩ | ⟨rfl, -⟩ | ⟨-, rfl, -⟩⟩ :=
            (E.act_ins_iff w).1 h
          · exact ⟨t, by omega, Or.inl rfl⟩
          · exact ⟨t, by omega, Or.inr rfl⟩
          · omega
          · omega
        · omega
      · rcases hq with hq | ⟨-, h2, -⟩ <;> omega
    · obtain ⟨hqL, h⟩ := E.g_del_iff hi h
      obtain ⟨-, ⟨t, ht, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ | ⟨-, rfl, -⟩⟩ := (E.act_del_iff w).1 h <;>
        rcases hq with hq | ⟨h1, -, -⟩ <;> omega
  have S2 : ∀ q, HB (E.γ w i) q (E.Lα + 2 * i) →
      q ∈ {q | q < 3 * i ∨ (E.Lα ≤ q ∧ q ≤ E.Lα + 2 * i ∧ (E.g w i q).rep = E.r2)} :=
    fun q hq => hq.mem_of_closed (E.closed_R2 hi (by omega))
      (Or.inr ⟨by omega, le_rfl, by rw [hread2]; rfl⟩)
  -- Claim 12: the read of R₂ returns `L_{i-1}`
  have hv_mem : ∀ x, x ∈ rval P (E.g w i) (E.Lα + 2 * i) ↔ x ∈ E.L w (i - 1) := by
    intro x
    rw [(resp (by omega) hread2).1 x, E.insVis_iff (by omega) hread2, E.delVis_iff (by omega) hread2]
    constructor
    · rintro ⟨⟨q, hq, hql, r', k, hgq⟩, -⟩
      rcases hq with rfl | hq
      · rw [hread2] at hgq; cases hgq
      · exact (r2_le q (S2 q hq)).1 _ _ _ hgq
    · intro hx
      refine ⟨?_, ?_⟩
      · obtain ⟨t, ht, rfl | rfl⟩ := mem_L.1 hx
        · refine ⟨3 * t, Or.inr ((to_recv2 _ (by omega)).trans (E.hb_ro (by omega) (by omega) ?_)),
            by omega, _, _, by rw [E.g_lt w i (by omega), E.act_Op w (by omega)]⟩
          rw [hread2, E.g_recv2 w i (by omega)]; rfl
        · refine ⟨3 * t + 1, Or.inr ((to_recv2 _ (by omega)).trans (E.hb_ro (by omega) (by omega) ?_)),
            by omega, _, _, by rw [E.g_lt w i (by omega), E.act_Cl w (by omega)]⟩
          rw [hread2, E.g_recv2 w i (by omega)]; rfl
      · rintro ⟨q, hq, hql, r', hgq⟩
        rcases hq with rfl | hq
        · rw [hread2] at hgq; cases hgq
        · exact (r2_le q (S2 q hq)).2 _ _ hgq
  have hv : rval P (E.g w i) (E.Lα + 2 * i) = E.L w (i - 1) := by
    have h1 : (E.L w (i - 1)).Pairwise lo := by
      have := (resp (p := 3 * (i - 1) + 1) (by omega)
        (by rw [E.g_lt w i (by omega), E.act_Cl w (by omega)])).2.1
      rwa [hrv _ (by omega), (hLj (i - 1) (by omega)).2] at this
    exact (eq_of_pairwise h1 (resp (by omega) hread2).2.1 hirr (trans (by omega) hread2)
      (fun x => (hv_mem x).symm)).symm
  -- the insertion of `x` by `R₂`
  have hx_resp : rval P (E.g w i) (E.Lα + (2 * i + 1)) =
      (E.AB w (i - 1)).1 ++ [E.Op (i - 1), E.X, E.Cl (i - 1)] ++ (E.AB w (i - 1)).2 := by
    have hprev : ∀ q, HB (E.γ w i) q (E.Lα + (2 * i + 1)) → q = E.Lα + 2 * i ∨ HB (E.γ w i) q (E.Lα + 2 * i) := by
      intro q hq
      obtain ⟨k, a, hk, ha, hrep, hqk⟩ := hq.of_not_recv (E.γ_get (by omega)) (by rw [hinsX]; rfl)
      rw [E.γ_get (by omega)] at ha; obtain rfl := Option.some.inj ha
      rw [hinsX] at hrep
      have hkL : E.Lα ≤ k := by
        by_contra h; rw [rep1 k (by omega)] at hrep; exact E.h12 hrep
      rcases Nat.lt_or_ge k (E.Lα + 2 * i) with hk' | hk'
      · have := E.hb_ro (w := w) (i := i) hk' (by omega) (by rw [hrep, hread2]; rfl)
        rcases hqk with rfl | hqk
        · exact Or.inr this
        · exact Or.inr (hqk.trans this)
      · obtain rfl : k = E.Lα + 2 * i := by omega
        exact hqk
    have hmem : ∀ x, x ∈ rval P (E.g w i) (E.Lα + (2 * i + 1)) ↔
        x ∈ rval P (E.g w i) (E.Lα + 2 * i) ∨ x = E.X := by
      intro x
      rw [(resp (by omega) hinsX).1 x, E.insVis_iff (by omega) hinsX, E.delVis_iff (by omega) hinsX,
        hv_mem]
      constructor
      · rintro ⟨⟨q, hq, hql, r', k, hgq⟩, -⟩
        rcases hq with rfl | hq
        · rw [hinsX] at hgq; simp at hgq; exact Or.inr hgq.2.1.symm
        · rcases hprev q hq with rfl | hq
          · rw [hread2] at hgq; cases hgq
          · exact Or.inl ((r2_le q (S2 q hq)).1 _ _ _ hgq)
      · intro hx
        refine ⟨?_, ?_⟩
        · rcases hx with hx | rfl
          · obtain ⟨q, hq, hql, r', k, hgq⟩ := (E.insVis_iff (by omega) hread2 x).1
              (((resp (by omega) hread2).1 x).1 ((hv_mem x).2 hx)).1
            have h2x : HB (E.γ w i) (E.Lα + 2 * i) (E.Lα + (2 * i + 1)) :=
              E.hb_ro (by omega) (by omega) (by rw [hread2, hinsX]; rfl)
            refine ⟨q, Or.inr ?_, hql, r', k, hgq⟩
            rcases hq with rfl | hq
            · exact h2x
            · exact hq.trans h2x
          · exact ⟨_, Or.inl rfl, by omega, _, _, hinsX⟩
        · rintro ⟨q, hq, hql, r', hgq⟩
          rcases hq with rfl | hq
          · rw [hinsX] at hgq; cases hgq
          · rcases hprev q hq with rfl | hq
            · rw [hread2] at hgq; cases hgq
            · exact (r2_le q (S2 q hq)).2 _ _ hgq
    have hXv : E.X ∉ rval P (E.g w i) (E.Lα + 2 * i) := by
      rw [hv, mem_L]; rintro ⟨t, -, h | h⟩ <;> simp at h
    have h := eq_insertIdx_of_weak (resp (by omega) hread2).2.1 (resp (by omega) hinsX).2.1 hirr
      (trans (by omega) hinsX) hmem hXv ((resp (by omega) hinsX).2.2 E.X _ rfl)
    rw [h, hv, min_eq_left (by simp [L, lenA]), insertIdx_X]
  have hOX : lo (E.Op (i - 1)) E.X :=
    rel_of_pairwise_pair (resp (by omega) hinsX).2.1 (by rw [hx_resp]; simp)
  have hXC : lo E.X (E.Cl (i - 1)) :=
    rel_of_pairwise_pair (resp (by omega) hinsX).2.1 (by rw [hx_resp]; simp)
  have hstar_pw : (E.Lstar w).Pairwise lo := by
    have := (resp (p := 3 * E.d + 3) (by omega) (by rw [E.g_lt w i (by omega), E.act_Star w])).2.1
    rwa [hrv _ (by omega), hLs] at this
  -- no deletion is visible to the reads of `R₂` and `R₃`
  have noDel3 : ∀ q, (q = E.Lα + (2 * i + E.d + 9) ∨ HB (E.γ w i) q (E.Lα + (2 * i + E.d + 9))) →
      ∀ r x, E.g w i q ≠ .doOp r (.del x) := by
    intro q hq r x h
    obtain ⟨hqL, h⟩ := E.g_del_iff hi h
    rcases hq with rfl | hq
    · omega
    have := hq.mem_of_closed (E.closed_R23 hi) (Or.inr ⟨by omega, Or.inr (by rw [hread3]; rfl)⟩)
    simp only [Set.mem_setOf_eq] at this
    obtain ⟨-, ⟨t, ht, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ | ⟨-, rfl, -⟩⟩ := (E.act_del_iff w).1 h <;> omega
  have hz : ∀ x, (x = E.Op (i - 1) ∨ x = E.Cl (i - 1) ∨ x = E.X ∨ x = E.Star) →
      x ∈ rval P (E.g w i) (E.Lα + (2 * i + E.d + 9)) := by
    have hr3 : ∀ q, E.Lα + (2 * i + 6 + (i - 1)) ≤ q → q < E.Lα + (2 * i + E.d + 9) →
        (E.g w i q).rep = E.r3 → HB (E.γ w i) q (E.Lα + (2 * i + E.d + 9)) := by
      intro q h1 h2 h3
      rcases h1.lt_or_eq with h1 | rfl
      · exact E.hb_ro (by omega) (by omega) (by rw [h3, hread3]; rfl)
      · exact E.hb_ro (by omega) (by omega) (by rw [h3, hread3]; rfl)
    intro x hx
    refine ((resp (by omega) hread3).1 x).2 ⟨?_, ?_⟩
    · rw [E.insVis_iff (by omega) hread3]
      rcases hx with rfl | rfl | rfl | rfl
      · refine ⟨3 * (i - 1), Or.inr ((to_recv3 _ (by omega)).trans (hr3 _ le_rfl (by omega) ?_)),
          by omega, _, _, by rw [E.g_lt w i (by omega), E.act_Op w (by omega)]⟩
        rw [E.g_recv3 w i (by omega)]; rfl
      · refine ⟨3 * (i - 1) + 1, Or.inr ((to_recv3 _ (by omega)).trans (hr3 _ le_rfl (by omega) ?_)),
          by omega, _, _, by rw [E.g_lt w i (by omega), E.act_Cl w (by omega)]⟩
        rw [E.g_recv3 w i (by omega)]; rfl
      · refine ⟨E.Lα + (2 * i + 1), Or.inr ?_, by omega, _, _, hinsX⟩
        have h1 : HB (E.γ w i) (E.Lα + (2 * i + 1)) (E.pmx i) :=
          E.hb_ro (by omega) (by omega) (by rw [hinsX, g_pmx]; rfl)
        have h2 : HB (E.γ w i) (E.pmx i) (E.Lα + (3 * i + 6)) :=
          E.hb_recv (r := E.r3) (by omega) (by omega) (E.g_recv3x w i)
        exact h1.trans (h2.trans (hr3 _ (by omega) (by omega) (by rw [E.g_recv3x w i]; rfl)))
      · refine ⟨3 * E.d + 3, Or.inr ?_, by omega, _, _, by rw [E.g_lt w i (by omega), E.act_Star w]⟩
        have h1 : HB (E.γ w i) (3 * E.d + 3) (3 * E.d + 4) :=
          E.hb_ro (by omega) (by omega) (by rw [rep1 _ (by omega), rep1 _ (by omega)])
        have hrc := E.g_recv3' w i (t := E.d + 1 - i) (by omega)
        rw [show i + 1 + (E.d + 1 - i) = E.d + 2 by omega, mpos_top] at hrc
        have h2 : HB (E.γ w i) (3 * E.d + 4) (E.Lα + (3 * i + 7 + (E.d + 1 - i))) :=
          E.hb_recv (r := E.r3) (by omega) (by omega) hrc
        exact h1.trans (h2.trans (hr3 _ (by omega) (by omega) (by rw [hrc]; rfl)))
    · rw [E.delVis_iff (by omega) hread3]
      rintro ⟨q, hq, -, r', hgq⟩
      exact noDel3 q hq _ _ hgq
  have htz := trans (by omega) hread3
  -- Claim 13: the read of `R₁` returns `x ∗` or `∗ x`
  have hy_mem : ∀ x, x ∈ rval P (E.g w i) (E.Lα + (2 * i + 5)) ↔ x = E.X ∨ x = E.Star := by
    have hr1 : ∀ q < E.Lα, HB (E.γ w i) q (E.Lα + (2 * i + 5)) := fun q hq =>
      E.hb_ro (by omega) (by omega) (by rw [rep1 _ hq, hread1]; rfl)
    have nodelXS : ∀ q r, E.g w i q = .doOp r (.del E.X) ∨ E.g w i q = .doOp r (.del E.Star) → False := by
      rintro q r (h | h) <;>
      · obtain ⟨-, h⟩ := E.g_del_iff hi h
        obtain ⟨-, ⟨t, -, ⟨-, h⟩ | ⟨-, h⟩⟩ | ⟨-, -, h⟩⟩ := (E.act_del_iff w).1 h <;> simp at h
    intro x
    rw [(resp (by omega) hread1).1 x, E.insVis_iff (by omega) hread1, E.delVis_iff (by omega) hread1]
    constructor
    · rintro ⟨⟨q, hq, hql, r', k, hgq⟩, hnd⟩
      have hql' : q ≤ E.Lα + (2 * i + 5) := by rcases hq with rfl | hq; exact le_rfl; exact hq.lt.le
      rcases E.g_ins_iff hi hgq with ⟨hqL, h⟩ | ⟨-, rfl⟩
      · obtain ⟨-, ⟨t, ht, ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩⟩ | ⟨rfl, rfl, -⟩ | ⟨ho, rfl, rfl, -⟩⟩ :=
          (E.act_ins_iff w).1 h
        · exact absurd ⟨3 * E.d + 5 + 2 * t, Or.inr (hr1 _ (by omega)), by omega, _,
            by rw [E.g_lt w i (by omega), E.act_delOp w ht]⟩ hnd
        · exact absurd ⟨3 * E.d + 6 + 2 * t, Or.inr (hr1 _ (by omega)), by omega, _,
            by rw [E.g_lt w i (by omega), E.act_delCl w ht]⟩ hnd
        · exact Or.inr rfl
        · have : E.Lα = 5 * E.d + 10 := by rw [Lα_eq, ho]; rfl
          exact absurd ⟨_, Or.inr (hr1 (5 * E.d + 8) (by omega)), by omega, _,
            by rw [E.g_lt w i (by omega), E.act_delBee w ho]⟩ hnd
      · exact Or.inl rfl
    · rintro (rfl | rfl)
      · refine ⟨⟨E.Lα + (2 * i + 1), Or.inr ?_, by omega, _, _, hinsX⟩, ?_⟩
        · have h1 : HB (E.γ w i) (E.Lα + (2 * i + 1)) (E.pmx i) :=
            E.hb_ro (by omega) (by omega) (by rw [hinsX, g_pmx]; rfl)
          have h2 : HB (E.γ w i) (E.pmx i) (E.Lα + (2 * i + 4)) :=
            E.hb_recv (r := E.r1) (by omega) (by omega) (E.g_recv1x w i)
          exact h1.trans (h2.trans (E.hb_ro (by omega) (by omega)
            (by rw [E.g_recv1x w i, hread1]; rfl)))
        · rintro ⟨q, -, -, r', hgq⟩; exact nodelXS q r' (Or.inl hgq)
      · refine ⟨⟨3 * E.d + 3, Or.inr (hr1 _ (by omega)), by omega, _, _,
          by rw [E.g_lt w i (by omega), E.act_Star w]⟩, ?_⟩
        rintro ⟨q, -, -, r', hgq⟩; exact nodelXS q r' (Or.inr hgq)
  have hy_pw := (resp (by omega) hread1).2.1
  have hy := eq_pair_of_mem (nodup_of_pairwise hy_pw hirr) (by simp) hy_mem
  have hXz := hz _ (Or.inr (Or.inr (Or.inl rfl)))
  have hSz := hz _ (Or.inr (Or.inr (Or.inr rfl)))
  have hOz := hz _ (Or.inl rfl)
  have hCz := hz _ (Or.inr (Or.inl rfl))
  constructor
  · intro hy1
    by_contra hw
    have hSO := rel_of_pairwise_pair hstar_pw (E.Star_before_Op hi1 hi (by simpa using hw))
    have hSX := htz _ hSz _ hOz _ hXz hSO hOX
    have hXS := rel_of_pairwise_pair hy_pw (by rw [hy1])
    exact hirr _ (htz _ hXz _ hSz _ hXz hXS hSX)
  · intro hw
    rcases hy with hy | hy
    · exact hy
    · exfalso
      have hCS := rel_of_pairwise_pair hstar_pw (E.Cl_before_Star hi1 hi hw)
      have hXS := htz _ hXz _ hCz _ hSz hXC hCS
      have hSX := rel_of_pairwise_pair hy_pw (by rw [hy])
      exact hirr _ (htz _ hXz _ hSz _ hXz hXS hSX)

end Params

end Podc.CollaborativeListSpec
