import Papers.PODC2016.WeakCrashFailures.Fig1Safety

/-!
# Fig. 1: levels and ranks for the termination proof

* `lvl c`: the position of a program counter in the code (rounds, line 16 check, line 21 loop);
  it never decreases (`lvl_step`).
* `rk c`: progress inside the non-waiting parts of a level; every own step that stays on the
  same level decreases it (`rk_step`), provided `decision = ⊥` and, in the last loop, all states
  are `3`.
* `wrk S0 c`: progress inside the waiting loop of round `r`, relative to a set `S0` of processes
  with `state ≥ r` of size `≥ n − 1` (`wrk_step`).
* `drk c`: progress towards the next read of `decision` (`drk_step`), used once `decision ≠ ⊥`.
-/

namespace Podc.WeakCrashFailures.Fig1

open Finset

variable {n : ℕ} {x : Fin n → ℕ}

/-- The level of a program counter. -/
def lvl : PC → ℕ
  | .start => 0
  | .scan r _ _ _ => 2 * r - 1
  | .scanIn r _ _ _ => 2 * r - 1
  | .wait r _ _ _ => 2 * r
  | .chk _ _ _ => 7
  | .chkIn _ _ _ => 7
  | .fin _ _ => 8
  | .finDec _ _ _ => 8
  | .finIn _ _ => 8
  | .done _ => 9

/-- Rank inside the non-waiting code of a level. -/
def rk (n : ℕ) : PC → ℕ
  | .scan _ j _ _ => 2 * (n - j) + 2
  | .scanIn _ j _ _ => 2 * (n - j) + 1
  | .chk j _ _ => 2 * (n - j) + 2
  | .chkIn j _ _ => 2 * (n - j) + 1
  | .fin j _ => 3 * (n - j) + 2
  | .finDec j _ b => 3 * (n - j) + if b then 1 else 3
  | .finIn j _ => 3 * (n - j)
  | _ => 0

/-- Rank inside a waiting loop relative to `S0`. -/
def wrk (n : ℕ) (S0 : Finset (Fin n)) : PC → ℕ
  | .wait _ j cnt _ => if (S0.filter fun k => k.val < j).card ≤ cnt then n - j else 2 * n + 1 - j
  | _ => 0

/-- Rank towards the next read of `decision`. -/
def drk (n : ℕ) : PC → ℕ
  | .start => 3 * n + 4
  | .scan _ j _ _ => 2 * (n - j) + n + 3
  | .scanIn _ j _ _ => 2 * (n - j) + n + 2
  | .wait _ j _ _ => n - j + 1
  | .chk j _ _ => 2 * (n - j) + 4
  | .chkIn j _ _ => 2 * (n - j) + 3
  | .fin _ _ => 2
  | .finDec _ _ _ => 1
  | .finIn _ _ => 3
  | .done _ => 0

lemma lvl_step {C : Cfg n} (hI : Inv x C) (q : Fin n) :
    lvl (C.pc q) ≤ lvl ((step x q C).pc q) := by
  have hli := hI.li q
  cases hc : C.pc q with
  | start => simp [step, hc, lvl]
  | scan r j cnt mx =>
    rw [hc] at hli; obtain ⟨h1, h3, -⟩ := hli
    simp only [step, hc]; split_ifs <;> simp [lvl] <;> omega
  | scanIn r j cnt mx => simp [step, hc, lvl]
  | wait r j cnt mx =>
    rw [hc] at hli; obtain ⟨h1, h3, -⟩ := hli
    simp only [step, hc]
    by_cases hj : j < n
    · simp [hj, lvl]
    · simp only [hj, ite_false]
      cases hd : C.dec with
      | some d => simp [lvl]; omega
      | none => dsimp only; split_ifs <;> simp [lvl] <;> omega
  | chk j cnt mx => simp only [step, hc]; split_ifs <;> simp [lvl]
  | chkIn j cnt mx => simp [step, hc, lvl]
  | fin j mx => simp only [step, hc]; split_ifs <;> simp [lvl]
  | finDec j mx b => simp only [step, hc]; split <;> (try split_ifs) <;> simp [lvl]
  | finIn j mx => simp [step, hc, lvl]
  | done v => simp [step, hc]

/-- Own steps inside a non-waiting level decrease `rk`. -/
lemma rk_step {C : Cfg n} (hI : Inv x C) (q : Fin n) (hdn : C.dec = none)
    (hnd : ∀ v, (step x q C).pc q ≠ .done v) (hs : C.pc q ≠ .start)
    (hw : ∀ r j cnt mx, C.pc q ≠ .wait r j cnt mx)
    (henv : 8 ≤ lvl (C.pc q) → ∀ k, C.st k = 3)
    (hlv : lvl ((step x q C).pc q) = lvl (C.pc q)) :
    rk n ((step x q C).pc q) < rk n (C.pc q) := by
  have hli := hI.li q
  cases hc : C.pc q with
  | start => exact absurd hc hs
  | wait r j cnt mx => exact absurd hc (hw r j cnt mx)
  | done v => exact absurd (by rw [step_done hc, hc]) (hnd v)
  | scan r j cnt mx =>
    rw [hc] at hli hlv; obtain ⟨h1, h3, hj, -⟩ := hli
    simp only [step, hc] at hlv hnd ⊢
    split_ifs at hlv hnd ⊢ with h1' h2' h3'
    · simp only [setPc_pc_self, rk]; omega
    · simp only [setPc_pc_self, rk]; omega
    · simp at hnd
    · simp [lvl] at hlv; omega
  | scanIn r j cnt mx =>
    rw [hc] at hli; obtain ⟨-, -, hj, -⟩ := hli
    simp [step, hc, rk]; omega
  | chk j cnt mx =>
    rw [hc] at hli hlv; obtain ⟨hj, -⟩ := hli
    simp only [step, hc] at hlv hnd ⊢
    split_ifs at hlv hnd ⊢
    · simp only [setPc_pc_self, rk]; omega
    · simp only [setPc_pc_self, rk]; omega
    · simp at hnd
    · simp [lvl] at hlv
  | chkIn j cnt mx =>
    rw [hc] at hli; obtain ⟨-, hj, -⟩ := hli
    simp [step, hc, rk]; omega
  | fin j mx =>
    rw [hc] at hli henv; obtain ⟨hjn, -⟩ := hli
    simp only [step, hc] at hnd ⊢
    split_ifs at hnd ⊢ with hj
    · have h3 := henv (by simp [lvl]) ⟨j, hj⟩
      simp [rk, stAt_of_lt hj, h3]
    · simp at hnd
  | finDec j mx b =>
    rw [hc] at hli; obtain ⟨-, -, hj, -⟩ := hli
    simp only [step, hc, hdn]
    split_ifs with hb
    · simp [rk, hb]
    · simp [rk, hb]
  | finIn j mx =>
    rw [hc] at hli; obtain ⟨-, -, hj, -⟩ := hli
    simp [step, hc, rk]; omega

lemma card_filter_lt_succ (S0 : Finset (Fin n)) {j : ℕ} (hj : j < n) :
    (S0.filter fun k : Fin n => k.val < j + 1).card =
      (S0.filter fun k : Fin n => k.val < j).card + if (⟨j, hj⟩ : Fin n) ∈ S0 then 1 else 0 := by
  have hu : (S0.filter fun k : Fin n => k.val < j + 1) =
      (S0.filter fun k : Fin n => k.val < j) ∪ (S0.filter fun k : Fin n => k = ⟨j, hj⟩) := by
    ext k
    simp only [mem_union, mem_filter, Fin.ext_iff]
    constructor
    · rintro ⟨hk, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact Or.inl ⟨hk, h⟩
      · exact Or.inr ⟨hk, h⟩
    · rintro (⟨hk, h⟩ | ⟨hk, h⟩)
      · exact ⟨hk, by omega⟩
      · exact ⟨hk, by omega⟩
  have hd : Disjoint (S0.filter fun k : Fin n => k.val < j)
      (S0.filter fun k : Fin n => k = ⟨j, hj⟩) := by
    rw [disjoint_filter]; intro k _ hk he; rw [he] at hk; simp at hk
  rw [hu, card_union_of_disjoint hd]
  congr 1
  split_ifs with hm
  · rw [card_eq_one]; refine ⟨⟨j, hj⟩, ?_⟩
    ext k; simp only [mem_filter, mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hm, h⟩⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro k hk rfl; exact hm hk

/-- Own steps inside the waiting loop of round `r` decrease `wrk S0`, if every process of `S0`
has `state ≥ r` and `|S0| ≥ n − 1`. -/
lemma wrk_step {C : Cfg n} (hI : Inv x C) (q : Fin n) (hdn : C.dec = none) {r j cnt mx : ℕ}
    (hc : C.pc q = .wait r j cnt mx) {S0 : Finset (Fin n)} (hS0 : ∀ k ∈ S0, r ≤ C.st k)
    (hS0c : n - 1 ≤ S0.card) (hlv : lvl ((step x q C).pc q) = lvl (C.pc q)) :
    wrk n S0 ((step x q C).pc q) < wrk n S0 (C.pc q) := by
  have hli := hI.li q
  rw [hc] at hli hlv ⊢; obtain ⟨h1, h3, hjn, -⟩ := hli
  simp only [step, hc] at hlv ⊢
  by_cases hj : j < n
  · simp only [hj, ite_true, setPc_pc_self, wrk]
    rw [card_filter_lt_succ S0 hj]
    by_cases hm : (⟨j, hj⟩ : Fin n) ∈ S0
    · have hr : r ≤ stAt C j := by rw [stAt_of_lt hj]; exact hS0 _ hm
      simp only [hm, ite_true, hr]
      split_ifs <;> omega
    · simp only [hm, ite_false]
      split_ifs <;> omega
  · simp only [hj, ite_false] at hlv ⊢
    simp only [hdn] at hlv ⊢
    split_ifs at hlv ⊢ with hge hr3 hcn
    · simp [lvl] at hlv; omega
    · simp [lvl] at hlv; omega
    · simp [lvl] at hlv; omega
    · have hfil : (S0.filter fun k : Fin n => k.val < j) = S0 := by
        ext k; simp only [mem_filter, and_iff_left_iff_imp]; intro; have := k.isLt; omega
      have h0 : (S0.filter fun k : Fin n => k.val < 0) = ∅ := by ext k; simp
      simp only [setPc_pc_self, wrk, hfil, h0, card_empty, Nat.zero_le, ite_true, Nat.sub_zero]
      have hjn' : j = n := by omega
      subst hjn'
      rw [ite_eq_right_iff.2 (fun h => absurd h (by omega))]
      omega

/-- Once `decision ≠ ⊥`, own steps decrease `drk` until the process decides. -/
lemma drk_step {C : Cfg n} (hI : Inv x C) (q : Fin n) (hds : C.dec.isSome)
    (hnd : ∀ v, (step x q C).pc q ≠ .done v) :
    drk n ((step x q C).pc q) < drk n (C.pc q) := by
  have hli := hI.li q
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hds
  cases hc : C.pc q with
  | start => simp [step, hc, drk]; omega
  | scan r j cnt mx =>
    rw [hc] at hli; obtain ⟨-, -, hj, -⟩ := hli
    simp only [step, hc] at hnd ⊢
    split_ifs at hnd ⊢ <;> simp_all [drk] <;> omega
  | scanIn r j cnt mx =>
    rw [hc] at hli; obtain ⟨-, -, hj, -⟩ := hli
    simp [step, hc, drk]; omega
  | wait r j cnt mx =>
    rw [hc] at hli; obtain ⟨-, -, hj, -⟩ := hli
    simp only [step, hc, hd] at hnd ⊢
    split_ifs at hnd ⊢ <;> first | (simp [drk]; omega) | exact (hnd d (by simp)).elim
  | chk j cnt mx =>
    rw [hc] at hli; obtain ⟨hj, -⟩ := hli
    simp only [step, hc] at hnd ⊢
    split_ifs at hnd ⊢ <;> simp_all [drk] <;> omega
  | chkIn j cnt mx =>
    rw [hc] at hli; obtain ⟨-, hj, -⟩ := hli
    simp [step, hc, drk]; omega
  | fin j mx =>
    simp only [step, hc] at hnd ⊢
    split_ifs at hnd ⊢ <;> simp_all [drk]
  | finDec j mx b =>
    simp only [step, hc, hd] at hnd ⊢
    simp at hnd
  | finIn j mx => simp [step, hc, drk]
  | done v => exact absurd (by rw [step_done hc, hc]) (hnd v)

end Podc.WeakCrashFailures.Fig1
