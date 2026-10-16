import Papers.PODC2015.SynchronousCounting.Recursive
import Cslib.Computability.Distributed.Byzantine.SyncCounting.Impossibility

/-!
# Theorem 1 as stated is false for `n = 1`

Theorem 1 of the paper assumes only `N = kn`, `3 ≤ k`, `F < (f+1)⌈k/2⌉`, `C > 1` and
`3(F+2)(2m)^k ∣ c`, and claims (§3.4) that `F < N/3` follows. For `n = 1`, `f = 0`, `k = 3` the
hypotheses allow `F = 1 < 2 = (f+1)⌈3/2⌉`, i.e. a `1`-resilient counter on `N = 3` nodes, which
does not exist (`Cslib.Byzantine.SyncCounting.not_isCounter_of_card_eq_three`). The base counter required by
the theorem exists: the trivial `0`-resilient counter on one node (`achievable_one`).

* `not_achievable_three_one`: there is no synchronous `C`-counter (`C ≥ 2`) on 3 nodes tolerating
  one fault.
* `theorem1_as_stated_false`: the statement of Theorem 1, even with the implicit assumption
  `f < n/3` added, is false.
* `construction_fails`: concretely, in the paper's construction `B` on 3 single-node blocks with
  `F = 1`, the Byzantine node mirrors each receiver's own phase-king register back to it; then
  every correct node sees its value `N - F = 2` times and the other correct value only `F = 1`
  time, so it keeps counting on its own (`pkStep_of_dominant`) and the two correct nodes never
  agree.
-/

namespace SynchronousCounting

open Cslib.Byzantine.SyncCounting Finset

/-- No synchronous counter on 3 nodes tolerates one Byzantine fault. -/
theorem not_achievable_three_one {C T S : ℕ} (hC : 2 ≤ C) : ¬ Achievable 3 1 C T S := by
  rintro ⟨X, _, _, A, -, hA⟩
  exact not_isCounter_of_card_eq_three (by simp) hC A T hA

/-- **Theorem 1 as stated in the paper is false**, even with the assumption `f < n/3` (which the
paper uses implicitly) added: take `n = 1`, `f = 0`, `k = 3`, `F = 1`, `C = 2`, `c = 3·3·4³`. -/
theorem theorem1_as_stated_false :
    ¬ ∀ n f c T S k F C : ℕ, Achievable n f c T S → 3 * f < n → 3 ≤ k →
      F < (f + 1) * half k → 1 < C → boostTime k F ∣ c →
      Achievable (k * n) F C (T + boostTime k F) (S + Nat.clog 2 (C + 1) + 1) := by
  intro h
  have := h 1 0 (boostTime 3 1) 0 _ 3 1 2 (achievable_one (by decide)) (by norm_num)
    le_rfl (by decide) (by norm_num) dvd_rfl
  exact not_achievable_three_one le_rfl this

/-- For `n ≥ 3`, the existence of a base counter already forces `f < n/3`
(`Cslib.Byzantine.SyncCounting.not_isCounter_of_three_le_card`). -/
lemma three_mul_lt_of_achievable {n f c T S : ℕ} (h : Achievable n f c T S) (hn : 3 ≤ n)
    (hc : 2 ≤ c) : 3 * f < n := by
  obtain ⟨X, _, _, A, -, hA⟩ := h
  by_contra hf
  exact not_isCounter_of_three_le_card (by simpa using hn) (by simpa using (not_lt.1 hf)) hc A T hA

/-- **Theorem 1 holds exactly as stated when `n ≥ 3`.** (Then `f < n/3` follows from the existence
of `A`, and `3F < kn` follows from it.) Together with `theorem1_as_stated_false` (`n = 1`) and
`theorem1_paper` (`n = 2`, `f = 0`), only the case `n = 2`, `f ≥ 1` stays open; it is vacuous iff no
`1`-resilient counter on two nodes exists, which the paper takes for granted but we do not prove. -/
theorem theorem1_of_three_le {n f c T S k F C : ℕ} (h : Achievable n f c T S) (hn : 3 ≤ n)
    (hk : 3 ≤ k) (hF : F < (f + 1) * half k) (hC : 1 < C) (hc : boostTime k F ∣ c) :
    Achievable (k * n) F C (T + boostTime k F) (S + Nat.clog 2 (C + 1) + 1) := by
  have hc2 : 2 ≤ c := by
    rcases Nat.eq_zero_or_pos c with rfl | hpos
    · obtain ⟨X, _, ⟨x⟩, A, -, -⟩ := h
      exact (A.h ⟨0, by omega⟩ x).elim0
    · have : 2 ≤ boostTime k F := by
        have : 0 < (2 * half k) ^ k := pow_pos (by simp only [half]; omega) _
        unfold boostTime; nlinarith
      exact this.trans (Nat.le_of_dvd hpos hc)
  exact theorem1_paper h (three_mul_lt_of_achievable h hn hc2) (by omega) hk hF hC hc

/-! ### The construction itself fails for `n = 1`, `k = 3`, `F = 1` -/

section Explicit

variable {C : ℕ} [NeZero C]

/-- The base counter size used in the counterexample, `c = 3(F+2)(2m)^k = 576`. -/
abbrev c₀ : ℕ := boostTime 3 1

/-- The paper's `B` for `n = 1`, `k = 3`, `F = 1`. -/
abbrev B₃ (C : ℕ) [NeZero C] := construction 3 1 C (trivialCounter c₀ (by decide))

/-- The faulty node. -/
abbrev byz : Fin 3 × Fin 1 := (2, 0)

/-- Node `(i, 0)` counts as `i + t mod C`, the base counter as `t mod c₀`. -/
def badExec (t : ℕ) (v : Fin 3 × Fin 1) : BState (Fin c₀) C :=
  (⟨t % c₀, Nat.mod_lt _ (by decide)⟩, some ⟨(v.1.val + t) % C, Nat.mod_lt _ (Nat.pos_of_neZero C)⟩,
    true)

/-- The Byzantine node sends every receiver a copy of the receiver's own state. -/
def badMsg (t : ℕ) (v : Fin 3 × Fin 1) : Fin 3 × Fin 1 → BState (Fin c₀) C :=
  fun w => if w = byz then badExec t v else badExec t w

lemma isExec_badExec : IsExec (B₃ C) {byz} badExec := by
  intro t v hv
  refine ⟨badMsg t v, fun w hw => ?_, ?_⟩
  · simp only [mem_singleton] at hw; simp [badMsg, hw]
  have hv' : v ≠ byz := by simpa using hv
  have hmv : badMsg (C := C) t v v = badExec t v := by simp [badMsg, hv']
  -- the received phase-king registers
  set ma : Fin 3 × Fin 1 → Option (Fin C) := fun u => (badMsg (C := C) t v u).2.1 with hma
  set x : Fin C := ⟨(v.1.val + t) % C, Nat.mod_lt _ (Nat.pos_of_neZero C)⟩ with hx
  have hpk : ∀ (king : Fin 3 × Fin 1) (r : ℕ),
      pkStep 1 king r ma (badExec (C := C) t v).2.1 (badExec (C := C) t v).2.2 = (some (incr x), true) := by
    intro king r
    apply pkStep_of_dominant
    · -- `v` and the Byzantine node both carry `x`
      have hsub : ({v, byz} : Finset _) ⊆ univ.filter fun u => ma u = some x := by
        intro u hu
        rcases mem_insert.1 hu with rfl | hu
        · simp [hma, hmv, badExec, hx]
        · rw [mem_singleton] at hu; subst hu; simp [hma, badMsg, badExec, hx]
      have := card_le_card hsub
      rw [card_pair hv'] at this
      simpa [cntA] using this
    · -- any other value comes only from the third node
      intro j hj
      obtain ⟨o, ho⟩ : ∃ o : Fin 3 × Fin 1, ∀ u, u ≠ v → u ≠ byz → u = o := by
        obtain ⟨i, i0⟩ := v
        refine ⟨if i = 0 then (1, 0) else (0, 0), fun ⟨u, u0⟩ h1 h2 => ?_⟩
        obtain rfl := Subsingleton.elim u0 0
        obtain rfl := Subsingleton.elim i0 0
        fin_cases i <;> fin_cases u <;> simp_all
      have hsub : (univ.filter fun u => ma u = some j) ⊆ {o} := by
        intro u hu
        simp only [mem_filter, mem_univ, true_and] at hu
        by_cases h1 : u = v
        · subst h1; simp [hma, hmv, badExec] at hu; exact absurd (hu.symm.trans hx.symm) hj
        by_cases h2 : u = byz
        · subst h2; simp [hma, badMsg, badExec] at hu; exact absurd (hu.symm.trans hx.symm) hj
        exact mem_singleton.2 (ho u h1 h2)
      have := card_le_card hsub
      simpa [cntA] using this
    · simp
  simp only [construction]
  rw [hmv, hpk]
  simp only [badExec, trivialCounter, badMsg, incr, hx, Prod.mk.injEq,
    ite_self, Option.some.injEq, Fin.ext_iff, and_true]
  exact ⟨(Nat.mod_add_mod _ _ _).symm, by rw [Nat.mod_add_mod, Nat.add_assoc]⟩

/-- **The paper's construction is not a 1-resilient counter on 3 nodes**: the two correct nodes
output `t mod C` and `t + 1 mod C` forever. -/
theorem construction_fails (hC : 2 ≤ C) (T : ℕ) : ¬ IsCounter (B₃ C) 1 T := by
  intro h
  have hs := h {byz} (by simp) badExec isExec_badExec
  have := congrArg Fin.val (hs.out_eq (le_refl T) (i := (0, 0)) (j := (1, 0)) (by simp) (by simp))
  simp [B₃, construction, badExec] at this
  rw [Nat.add_mod (1 : ℕ), Nat.mod_eq_of_lt (show 1 < C by omega)] at this
  have h1 := Nat.mod_lt T (show 0 < C by omega)
  rcases Nat.lt_or_ge (1 + T % C) C with h2 | h2
  · rw [Nat.mod_eq_of_lt h2] at this; omega
  · rw [show 1 + T % C = C by omega, Nat.mod_self] at this; omega

end Explicit

end SynchronousCounting
