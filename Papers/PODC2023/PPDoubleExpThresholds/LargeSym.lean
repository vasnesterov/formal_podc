import Papers.PODC2023.PPDoubleExpThresholds.LargeC

/-!
# Lemma 12(c) for `j = i − 1`: the symmetry argument

For an `(i−1)`-high configuration the random walk of `Large(x)` does not stay among weakly proper
configurations; the paper shows termination by noting that one iteration of the loop can be undone
by another one (the relation `∼` on loop heads is symmetric). We formalize this with the explicit
relation `Iter` (one iteration from a loop head to the next) and `iter_symm`.

The paper's proof appeals to Lemma 11(c) (`IncrPair` is `(i−1)`-robust), which is false
(`lemma_11c_false`); the configurations of the loop stay `(i−1)`-high for a different reason:
the pair sums on level `i − 1` never change, and one of them exceeds `N_{i−1}` once line 9 passed.
-/

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

set_option hygiene false in
local macro "ins" : tactic => `(tactic| (rw [Program.instr, hcode]; try rfl))

/-! ### Commutation of changes on disjoint registers -/

section comm

variable {C : Reg n → ℕ} {a b c d : Reg n}

theorem mv_lg_comm (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (m : ℕ) :
    mv (lg C a b m) c d = lg (mv C c d) a b m := by
  funext z
  simp only [mv, lg, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

theorem mv_swp_comm (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    mv (swp C a b) c d = swp (mv C c d) a b := by
  funext z
  simp only [mv, swp, Equiv.swap_apply_def]
  split_ifs <;> subst_vars <;> simp_all

theorem mv_mv_comm (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    mv (mv C a b) c d = mv (mv C c d) a b := by
  funext z
  simp only [mv]
  split_ifs <;> subst_vars <;> simp_all <;> omega

theorem mv_apply_ne (hc : z ≠ c) (hd : z ≠ d) : mv C c d z = C z := by
  simp [mv, hc, hd]

end comm

/-! ### `IncrPair` commutes with moves on other levels -/

section frame

variable {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (hZB : ZeroB n i) (hZC : ZeroC n i)
include hi hin hZB hZC

theorem geq_mv {D : Reg n → ℕ} {c d : Reg n} (hc : i < c.lvl) (hd : i < d.lvl) :
    Geq (mv D c d) i ↔ Geq D i := by
  have hval : ∀ l k0, 1 ≤ l → l ≤ i → mv D c d (reg n l k0) = D (reg n l k0) := by
    intro l k0 hl hli
    have hlv := lvl_reg (n := n) hl (by omega) k0
    refine mv_apply_ne ?_ ?_ <;> intro h <;> rw [h] at hlv <;> omega
  unfold Geq
  rw [proper_iff_of_agree (by omega) (fun l hl hli k0 => hval l k0 hl (by omega))]
  simp only [psum, hval i _ (by omega) le_rfl]

theorem incr_frame (bx by' : Bool) {D D' : Reg n → ℕ} {OF OF' b : Bool} (hD : Geq D i)
    (h : (prog n).Returns (.incrPair i bx by') D OF D' OF' b) {c d : Reg n} (hc : i < c.lvl)
    (hd : i < d.lvl) :
    (prog n).Returns (.incrPair i bx by') (mv D c d) OF (mv D' c d) OF' b := by
  have hne : ∀ k0 : Fin 4, c ≠ reg n i k0 ∧ d ≠ reg n i k0 := fun k0 =>
    ⟨fun h => by rw [h, lvl_reg hi hin] at hc; omega, fun h => by rw [h, lvl_reg hi hin] at hd; omega⟩
  have hval : ∀ E k0, mv E c d (reg n i k0) = E (reg n i k0) := fun E k0 =>
    mv_apply_ne (fun h => (hne k0).1 h.symm) (fun h => (hne k0).2 h.symm)
  have zr : ∀ k0 E, Geq E i → ∀ E' OF₁ OF' b, ZR n i k0 E OF₁ E' OF' b ↔ OF' = OF₁ ∧
      ((b = false ∧ E' = E ∧ 0 < E (reg n i k0)) ∨
       (b = true ∧ N i ≤ E (reg n i (bar k0)) ∧ E' = lg E (reg n i (bar k0)) (reg n i k0) (N i))) :=
    fun k0 E hE E' OF₁ => (hZB k0 E OF₁ hE.1 (hE.psum _)).1 E'
  have gm : ∀ E, Geq E i → Geq (mv E c d) i := fun E hE => (geq_mv hi hin hZB hZC hc hd).2 hE
  have lgc : ∀ E k1 k2 m, mv (lg E (reg n i k1) (reg n i k2) m) c d =
      lg (mv E c d) (reg n i k1) (reg n i k2) m := fun E k1 k2 m =>
    mv_lg_comm (hne k1).1 (hne k2).1 (hne k1).2 (hne k2).2 m
  have swc : ∀ E k1 k2, mv (swp E (reg n i k1) (reg n i k2)) c d =
      swp (mv E c d) (reg n i k1) (reg n i k2) := fun E k1 k2 =>
    mv_swp_comm (hne k1).1 (hne k2).1 (hne k1).2 (hne k2).2
  have mvc : ∀ E k1 k2, mv (mv E (reg n i k1) (reg n i k2)) c d =
      mv (mv E c d) (reg n i k1) (reg n i k2) := fun E k1 k2 =>
    mv_mv_comm (hne k1).1 (hne k2).1 (hne k1).2 (hne k2).2
  obtain ⟨-, -, hret⟩ := incr_geq hi hin hZB hZC bx by' (OF := OF) hD
  obtain ⟨rfl, hb, -⟩ := hret D' OF' b h
  subst hb
  rw [incr_returns_iff _ _ hZC] at h ⊢
  obtain ⟨-, hF⟩ := h
  refine ⟨rfl, ?_⟩
  rcases hF with ⟨C1, h1, hpos, rfl⟩ | ⟨C1, OF1, C3, h1, h3, rfl⟩ | ⟨C1, OF1, C3, h1, h3, hpos, rfl⟩
  · obtain ⟨-, ⟨-, rfl, hp⟩ | ⟨h, -⟩⟩ := (zr _ _ hD _ _ _ _).1 h1
    swap; · exact absurd h (by simp)
    refine .inl ⟨mv C1 c d, (zr _ _ (gm _ hD) _ _ _ _).2 ⟨rfl, .inl ⟨rfl, rfl, by rw [hval]; exact hp⟩⟩,
      by rw [hval]; exact hpos, mvc _ _ _⟩
  · obtain ⟨rfl, ⟨h, -⟩ | ⟨-, hm1, rfl⟩⟩ := (zr _ _ hD _ _ _ _).1 h1
    · exact absurd h (by simp)
    have hD2 : Geq (swp (lg D (reg n i (bar (bar (ky by')))) (reg n i (bar (ky by'))) (N i))
        (reg n i (ky by')) (reg n i (bar (ky by')))) i := by
      simp only [bar_bar]
      exact ((ps_lg hi hin _ (by simpa using hm1)).trans (ps_swp hi hin _)).geq hi hin hD
    obtain ⟨-, ⟨h, -⟩ | ⟨-, hm3, rfl⟩⟩ := (zr _ _ hD2 _ _ _ _).1 h3
    · exact absurd h (by simp)
    have hz1 := (zr (bar (ky by')) (mv D c d) (gm _ hD) _ OF1 OF1 true).2
      ⟨rfl, .inr ⟨rfl, by rw [hval]; exact hm1, rfl⟩⟩
    have hE2 : swp (lg (mv D c d) (reg n i (bar (bar (ky by')))) (reg n i (bar (ky by'))) (N i))
        (reg n i (ky by')) (reg n i (bar (ky by'))) =
        mv (swp (lg D (reg n i (bar (bar (ky by')))) (reg n i (bar (ky by'))) (N i))
          (reg n i (ky by')) (reg n i (bar (ky by')))) c d := by rw [swc, lgc]
    have hz3 := (zr (bar (kx bx)) (swp (lg (mv D c d) (reg n i (bar (bar (ky by')))) (reg n i (bar (ky by'))) (N i)) (reg n i (ky by')) (reg n i (bar (ky by'))))
      (by rw [hE2]; exact gm _ hD2) _ OF1 OF1 true).2
      ⟨rfl, .inr ⟨rfl, by rw [hE2, hval]; exact hm3, rfl⟩⟩
    refine .inr (.inl ⟨_, OF1, _, hz1, hz3, ?_⟩)
    rw [hE2, ← lgc, ← swc]
  · obtain ⟨rfl, ⟨h, -⟩ | ⟨-, hm1, rfl⟩⟩ := (zr _ _ hD _ _ _ _).1 h1
    · exact absurd h (by simp)
    have hD2 : Geq (swp (lg D (reg n i (bar (bar (ky by')))) (reg n i (bar (ky by'))) (N i))
        (reg n i (ky by')) (reg n i (bar (ky by')))) i := by
      simp only [bar_bar]
      exact ((ps_lg hi hin _ (by simpa using hm1)).trans (ps_swp hi hin _)).geq hi hin hD
    obtain ⟨-, ⟨-, rfl, hp⟩ | ⟨h, -⟩⟩ := (zr _ _ hD2 _ _ _ _).1 h3
    swap; · exact absurd h (by simp)
    have hz1 := (zr (bar (ky by')) (mv D c d) (gm _ hD) _ OF1 OF1 true).2
      ⟨rfl, .inr ⟨rfl, by rw [hval]; exact hm1, rfl⟩⟩
    have hE2 : swp (lg (mv D c d) (reg n i (bar (bar (ky by')))) (reg n i (bar (ky by'))) (N i))
        (reg n i (ky by')) (reg n i (bar (ky by'))) =
        mv (swp (lg D (reg n i (bar (bar (ky by')))) (reg n i (bar (ky by'))) (N i))
          (reg n i (ky by')) (reg n i (bar (ky by')))) c d := by rw [swc, lgc]
    have hv : 0 < swp (lg (mv D c d) (reg n i (bar (bar (ky by')))) (reg n i (bar (ky by'))) (N i))
        (reg n i (ky by')) (reg n i (bar (ky by'))) (reg n i (bar (kx bx))) := by
      rw [hE2, hval]; exact hp
    have hz3 := (zr (bar (kx bx)) (swp (lg (mv D c d) (reg n i (bar (bar (ky by')))) (reg n i (bar (ky by'))) (N i)) (reg n i (ky by')) (reg n i (bar (ky by'))))
      (by rw [hE2]; exact gm _ hD2) _ OF1 OF1 false).2
      ⟨rfl, .inl ⟨rfl, rfl, hv⟩⟩
    refine .inr (.inr ⟨_, OF1, _, hz1, hz3, hv, ?_⟩)
    rw [hE2, mvc]

end frame

/-! ### One iteration of the loop of `Large`, and its symmetry -/

section iter

variable (n) (i : ℕ) (k : Fin 4) (OF : Bool)

/-- `IncrPair` at level `i − 1` returns (with output flag `OF`). -/
abbrev IR (bx by' : Bool) (D D' : Reg n → ℕ) : Prop :=
  (prog n).Returns (.incrPair (i - 1) bx by') D OF D' OF false

/-- The `else` branch of the loop up to line 22: `Zero(x_{i−1}) ∧ Zero(y_{i−1})` failed, leaving
the registers `H`. -/
def Bpre (D H : Reg n → ℕ) : Prop :=
  (0 < D (reg n (i - 1) 0) ∧ H = D) ∨
  (N (i - 1) ≤ D (reg n (i - 1) 1) ∧
    0 < lg D (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1)) (reg n (i - 1) 2) ∧
    H = lg D (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1)))

/-- One iteration of the loop of `Large(x)` from the loop head with registers `D` to the next loop
head with registers `D'` (without returning). -/
def Iter (D D' : Reg n → ℕ) : Prop :=
  (0 < D (reg n i k) ∧ IR n i OF false false (mv D (reg n i k) (reg n i (bar k))) D' ∧
    0 < D' (reg n (i - 1) 0)) ∨
  (0 < D (reg n i k) ∧ ∃ F, IR n i OF false false (mv D (reg n i k) (reg n i (bar k))) F ∧
    N (i - 1) ≤ F (reg n (i - 1) 1) ∧
    0 < lg F (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1)) (reg n (i - 1) 2) ∧
    D' = lg F (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1))) ∨
  Bpre n i D D' ∨
  (∃ H, Bpre n i D H ∧ 0 < H (reg n i (bar k)) ∧
    IR n i OF true true (mv H (reg n i (bar k)) (reg n i k)) D')

end iter

section iterProps

variable {i : ℕ} (hi : 2 ≤ i) (hin : i ≤ n) (k : Fin 4) (OF : Bool)
  (hZB : ZeroB n (i - 1)) (hZC : ZeroC n (i - 1)) (hIB : IncrB n (i - 1))
include hi hin hZB hZC

theorem regs_ne : (reg n (i - 1) 0 ≠ reg n (i - 1) 1 ∧ reg n (i - 1) 0 ≠ reg n (i - 1) 2 ∧
    reg n (i - 1) 1 ≠ reg n (i - 1) 2 ∧ reg n (i - 1) 0 ≠ reg n (i - 1) 3 ∧
    reg n (i - 1) 1 ≠ reg n (i - 1) 3) := by
  simp only [Ne, reg_inj (n := n) (i := i - 1) (j := i - 1) (by omega) (by omega) (by omega) (by omega)]
  decide

theorem regs_lvl_ne (a b : Fin 4) : reg n (i - 1) a ≠ reg n i b := by
  intro h
  have := congrArg Reg.lvl h
  rw [lvl_reg (by omega) (by omega), lvl_reg (by omega) hin] at this
  omega

/-- The configurations of the loop are `Geq` on level `i − 1`, with the pair sums of the start. -/
def GP (C E : Reg n → ℕ) (l : ℕ) : Prop := Geq E l ∧ ∀ k', psum E l k' = psum C l k'

theorem iter_gp {C D D' : Reg n → ℕ} (hD : GP C D (i - 1)) (h : Iter n i k OF D D') :
    GP C D' (i - 1) := by
  have hl : 1 ≤ i - 1 := by omega
  have hln : i - 1 ≤ n := by omega
  have hlv : ∀ k', i - 1 < (reg n i k').lvl := fun k' => by rw [lvl_reg (by omega) hin]; omega
  have hmv : ∀ E (a b : Fin 4), GP C E (i - 1) → GP C (mv E (reg n i a) (reg n i b)) (i - 1) :=
    fun E a b hE => ⟨(geq_mv hl hln hZB hZC (hlv a) (hlv b)).2 hE.1, fun k' => by
      rw [← hE.2 k']; simp only [psum]
      rw [mv_apply_ne (regs_lvl_ne hi hin hZB hZC _ _) (regs_lvl_ne hi hin hZB hZC _ _),
        mv_apply_ne (regs_lvl_ne hi hin hZB hZC _ _) (regs_lvl_ne hi hin hZB hZC _ _)]⟩
  have hir : ∀ bx by' E E', GP C E (i - 1) → IR n i OF bx by' E E' → GP C E' (i - 1) := by
    intro bx by' E E' hE hr
    obtain ⟨-, -, hret⟩ := incr_geq hl hln hZB hZC bx by' (OF := OF) hE.1
    obtain ⟨-, -, hps⟩ := hret _ _ _ hr
    exact ⟨hps.geq hl hln hE.1, fun k' => (hps.2 k').trans (hE.2 k')⟩
  have hlg : ∀ E, GP C E (i - 1) → N (i - 1) ≤ E (reg n (i - 1) 1) →
      GP C (lg E (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1))) (i - 1) := fun E hE hm => by
    have := ps_lg hl hln 1 hm (C := E)
    exact ⟨this.geq hl hln hE.1, fun k' => (this.2 k').trans (hE.2 k')⟩
  rcases h with ⟨-, hr, -⟩ | ⟨-, F, hr, hm, -, rfl⟩ | hB | ⟨H, hB, -, hr⟩
  · exact hir _ _ _ _ (hmv _ _ _ hD) hr
  · exact hlg _ (hir _ _ _ _ (hmv _ _ _ hD) hr) hm
  · rcases hB with ⟨-, rfl⟩ | ⟨hm, -, rfl⟩
    exacts [hD, hlg _ hD hm]
  · have hH : GP C H (i - 1) := by
      rcases hB with ⟨-, rfl⟩ | ⟨hm, -, rfl⟩
      exacts [hD, hlg _ hD hm]
    exact hir _ _ _ _ (hmv _ _ _ hH) hr

include hIB in
/-- **The relation `∼` of the proof of Lemma 12(c) is symmetric**: one iteration of the loop of
`Large` can be undone by another iteration. -/
theorem iter_symm {D D' : Reg n → ℕ} (hD : Geq D (i - 1)) (h : Iter n i k OF D D') :
    Iter n i k OF D' D := by
  have hl : 1 ≤ i - 1 := by omega
  have hln : i - 1 ≤ n := by omega
  have hlv : ∀ k', i - 1 < (reg n i k').lvl := fun k' => by rw [lvl_reg (by omega) hin]; omega
  have hne := reg_ne_bar (by omega) hin k
  obtain ⟨r01, r02, r12, r03, r13⟩ := regs_ne hi hin hZB hZC (n := n)
  have hlvne := regs_lvl_ne hi hin hZB hZC (n := n)
  have gmv : ∀ E (a b : Fin 4), Geq E (i - 1) → Geq (mv E (reg n i a) (reg n i b)) (i - 1) :=
    fun E a b hE => (geq_mv hl hln hZB hZC (hlv a) (hlv b)).2 hE
  have hirr : ∀ bx by' E E', Geq E (i - 1) → IR n i OF bx by' E E' → Geq E' (i - 1) ∧ Off E E' (i - 1) := by
    intro bx by' E E' hE hr
    obtain ⟨-, -, hret⟩ := incr_geq hl hln hZB hZC bx by' (OF := OF) hE
    obtain ⟨-, -, hps⟩ := hret _ _ _ hr
    exact ⟨hps.geq hl hln hE, hps.1⟩
  have offi : ∀ E E' (a : Fin 4), Off E E' (i - 1) → E' (reg n i a) = E (reg n i a) := fun E E' a h =>
    h _ (by rw [lvl_reg (by omega) hin]; omega)
  have mvl : ∀ E (a b c : Fin 4), mv E (reg n i a) (reg n i b) (reg n (i - 1) c) = E (reg n (i - 1) c) :=
    fun E a b c => mv_apply_ne (hlvne c a) (hlvne c b)
  have lgy : ∀ E, lg E (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1)) (reg n (i - 1) 2) =
      E (reg n (i - 1) 2) := fun E => lg_apply_other _ (Ne.symm r12) (Ne.symm r02) _
  have lgxb : ∀ E, lg E (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1)) (reg n (i - 1) 1) =
      E (reg n (i - 1) 0) + N (i - 1) := fun E => lg_apply_x _ (Ne.symm r01) _
  have lglg : ∀ E, N (i - 1) ≤ E (reg n (i - 1) 1) →
      lg (lg E (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1))) (reg n (i - 1) 1) (reg n (i - 1) 0)
        (N (i - 1)) = E := fun E hm => lg_lg E (Ne.symm r01) hm
  -- undoing `x ↦ x̄; IncrPair(x, y)` by `x̄ ↦ x; IncrPair(x̄, ȳ)`
  have undoA : ∀ F, 0 < D (reg n i k) →
      IR n i OF false false (mv D (reg n i k) (reg n i (bar k))) F →
      Geq F (i - 1) ∧ 0 < F (reg n i (bar k)) ∧
        IR n i OF true true (mv F (reg n i (bar k)) (reg n i k)) D ∧
        F (reg n (i - 1) 2) = F (reg n (i - 1) 2) := by
    intro F hx hr
    have hE := gmv D k (bar k) hD
    obtain ⟨hF, hoff⟩ := hirr _ _ _ _ hE hr
    refine ⟨hF, ?_, ?_, rfl⟩
    · rw [offi _ _ _ hoff]; simp [mv, hne, Ne.symm hne]
    · have hrev := (hIB false false _ OF _ OF false hE hr).1
      simp only [Bool.not_false] at hrev
      have := incr_frame hl hln hZB hZC true true hF hrev (hlv (bar k)) (hlv k)
      rwa [rev1 D (Ne.symm hne) hx] at this
  -- undoing `x̄ ↦ x; IncrPair(x̄, ȳ)` by `x ↦ x̄; IncrPair(x, y)`
  have undoB : ∀ H D', Geq H (i - 1) → 0 < H (reg n i (bar k)) →
      IR n i OF true true (mv H (reg n i (bar k)) (reg n i k)) D' →
      0 < D' (reg n i k) ∧ IR n i OF false false (mv D' (reg n i k) (reg n i (bar k))) H := by
    intro H D' hH hxb hr
    have hM := gmv H (bar k) k hH
    obtain ⟨hD', hoff⟩ := hirr _ _ _ _ hM hr
    refine ⟨?_, ?_⟩
    · rw [offi _ _ _ hoff]; simp [mv, hne]
    · have hrev := (hIB true true _ OF _ OF false hM hr).1
      simp only [Bool.not_true] at hrev
      have := incr_frame hl hln hZB hZC false false hD' hrev (hlv k) (hlv (bar k))
      rwa [rev1 H hne hxb] at this
  rcases h with ⟨hx, hr, hpos⟩ | ⟨hx, F, hr, hm, hy, rfl⟩ | hB | ⟨H, hB, hxb, hr⟩
  · obtain ⟨-, hxb, hr', -⟩ := undoA D' hx hr
    exact .inr (.inr (.inr ⟨D', .inl ⟨hpos, rfl⟩, hxb, hr'⟩))
  · obtain ⟨-, hxb, hr', -⟩ := undoA F hx hr
    refine .inr (.inr (.inr ⟨F, .inr ⟨by rw [lgxb]; omega, by rw [lglg F hm]; rwa [lgy] at hy,
      (lglg F hm).symm⟩, ?_, ?_⟩))
    · exact hxb
    · exact hr'
  · rcases hB with ⟨hpos, rfl⟩ | ⟨hm, hy, rfl⟩
    · exact .inr (.inr (.inl (.inl ⟨hpos, rfl⟩)))
    · refine .inr (.inr (.inl (.inr ⟨by rw [lgxb]; omega, ?_, (lglg D hm).symm⟩)))
      rw [lglg D hm]; rwa [lgy] at hy
  · have hH : Geq H (i - 1) := by
      rcases hB with ⟨-, rfl⟩ | ⟨hm, -, rfl⟩
      · exact hD
      · exact (ps_lg hl hln 1 hm (C := D)).geq hl hln hD
    obtain ⟨hx, hr'⟩ := undoB H D' hH hxb hr
    rcases hB with ⟨hpos, rfl⟩ | ⟨hm, hy, rfl⟩
    · exact .inl ⟨hx, hr', hpos⟩
    · refine .inr (.inl ⟨hx, _, hr', by rw [lgxb]; omega, ?_, (lglg D hm).symm⟩)
      rw [lglg D hm]; rwa [lgy] at hy

end iterProps

/-! ### The invariant of `Large(x)` on `(i−1)`-high configurations -/

section inv

variable (n) (i : ℕ) (k : Fin 4) (OF : Bool)

/-- The registers at the first loop head: both `Zero` calls of line 9 returned `true`. -/
def Cstar (C : Reg n → ℕ) : Reg n → ℕ :=
  lg (lg C (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1))) (reg n (i - 1) 3) (reg n (i - 1) 2)
    (N (i - 1))

/-- Inside one iteration started at the loop head with registers `D₀`. -/
def SMid (D₀ : Reg n → ℕ) (pc : ℕ) (E : Reg n → ℕ) : Prop :=
  match pc with
  | 4 => E = D₀
  | 5 => E = D₀
  | 6 => E = D₀
  | 7 => E = D₀ ∧ 0 < D₀ (reg n i k)
  | 8 => 0 < D₀ (reg n i k) ∧ E = mv D₀ (reg n i k) (reg n i (bar k))
  | 9 => 0 < D₀ (reg n i k) ∧ IR n i OF false false (mv D₀ (reg n i k) (reg n i (bar k))) E
  | 10 => 0 < D₀ (reg n i k) ∧ ∃ F, IR n i OF false false (mv D₀ (reg n i k) (reg n i (bar k))) F ∧
      N (i - 1) ≤ F (reg n (i - 1) 1) ∧ E = lg F (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1))
  | 11 => True
  | 12 => True
  | 14 => Iter n i k OF D₀ E
  | 15 => E = D₀
  | 16 => N (i - 1) ≤ D₀ (reg n (i - 1) 1) ∧ E = lg D₀ (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1))
  | 17 => True
  | 19 => Bpre n i D₀ E
  | 20 => Bpre n i D₀ E ∧ 0 < E (reg n i (bar k))
  | 21 => ∃ H, Bpre n i D₀ H ∧ 0 < H (reg n i (bar k)) ∧ E = mv H (reg n i (bar k)) (reg n i k)
  | 22 => Iter n i k OF D₀ E
  | 23 => Iter n i k OF D₀ E
  | _ => False

/-- The invariant of `Large(x)` started on `C` (`(i−1)`-high). -/
def SInv (C : Reg n → ℕ) (pc : ℕ) (E : Reg n → ℕ) : Prop :=
  match pc with
  | 0 => E = C
  | 1 => N (i - 1) ≤ C (reg n (i - 1) 1) ∧ E = lg C (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1))
  | 2 => True
  | pc => N (i - 1) ≤ C (reg n (i - 1) 1) ∧ N (i - 1) ≤ C (reg n (i - 1) 3) ∧
      ∃ D₀, Relation.ReflTransGen (Iter n i k OF) (Cstar n i C) D₀ ∧ SMid n i k OF D₀ pc E

end inv

theorem SMid.lt {i : ℕ} {k : Fin 4} {OF : Bool} {D₀ : Reg n → ℕ} {pc : ℕ} {E : Reg n → ℕ}
    (h : SMid n i k OF D₀ pc E) : pc < 24 := by
  unfold SMid at h; split at h <;> first | omega | exact h.elim

theorem SInv.lt {i : ℕ} {k : Fin 4} {OF : Bool} {C : Reg n → ℕ} {pc : ℕ} {E : Reg n → ℕ}
    (h : SInv n i k OF C pc E) : pc < 24 := by
  unfold SInv at h
  split at h
  · omega
  · omega
  · omega
  · obtain ⟨-, -, D₀, -, h⟩ := h; exact h.lt

/-- **Lemma 12(c)** for `j = i − 1`. -/
theorem large_robust_mid {i : ℕ} (hi : 2 ≤ i) (hin : i ≤ n) (hAPA : APA n (i - 2))
    (hZB : ZeroB n (i - 1)) (hZC : ZeroC n (i - 1)) (hIB : IncrB n (i - 1)) (k : Fin 4) :
    RobustOn n (fun j => j = i - 1) (.large i k) := by
  intro j hj hjn hji C OF hC
  subst hji
  have hl : 1 ≤ i - 1 := by omega
  have hln : i - 1 ≤ n := by omega
  have hcode := code_large n hi k
  have hlv : ∀ k', i - 1 < (reg n i k').lvl := fun k' => by rw [lvl_reg (by omega) hin]; omega
  have hne := reg_ne_bar (by omega) hin k
  obtain ⟨r01, r02, r12, r03, r13⟩ := regs_ne hi hin hZB hZC (n := n)
  have r23 : reg n (i - 1) 2 ≠ reg n (i - 1) 3 := reg_ne_bar hl hln 2
  have hlvne := regs_lvl_ne hi hin hZB hZC (n := n)
  have hNl := N_pos hl
  -- callee semantics on `Geq` configurations
  have zx : ∀ E, Geq E (i - 1) → ∀ E' OF' b, (prog n).Returns (.zero (i - 1) 0) E OF E' OF' b ↔
      OF' = OF ∧ ((b = false ∧ E' = E ∧ 0 < E (reg n (i - 1) 0)) ∨
        (b = true ∧ N (i - 1) ≤ E (reg n (i - 1) 1) ∧
          E' = lg E (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1)))) :=
    fun E hE => (hZB 0 E OF hE.1 (hE.psum 0)).1
  have zy : ∀ E, Geq E (i - 1) → ∀ E' OF' b, (prog n).Returns (.zero (i - 1) 2) E OF E' OF' b ↔
      OF' = OF ∧ ((b = false ∧ E' = E ∧ 0 < E (reg n (i - 1) 2)) ∨
        (b = true ∧ N (i - 1) ≤ E (reg n (i - 1) 3) ∧
          E' = lg E (reg n (i - 1) 3) (reg n (i - 1) 2) (N (i - 1)))) :=
    fun E hE => (hZB 2 E OF hE.1 (hE.psum 2)).1
  have ap : ∀ E, Geq E (i - 1) → Spec n (.assertProper (i - 2)) E OF fun E' b => E' = E ∧ b = false :=
    fun E hE => hAPA E OF (.inl (by rw [show i - 2 = i - 1 - 1 by omega]; exact hE.1))
  have ir := fun bx by' E (hE : Geq E (i - 1)) => incr_geq hl hln hZB hZC bx by' (OF := OF) hE
  -- `GP` helpers
  have gpmv : ∀ E (a b : Fin 4), GP C E (i - 1) → GP C (mv E (reg n i a) (reg n i b)) (i - 1) :=
    fun E a b hE => ⟨(geq_mv hl hln hZB hZC (hlv a) (hlv b)).2 hE.1, fun k' => by
      rw [← hE.2 k']; simp only [psum]
      rw [mv_apply_ne (hlvne _ _) (hlvne _ _), mv_apply_ne (hlvne _ _) (hlvne _ _)]⟩
  have gpswp : ∀ E, GP C E (i - 1) → GP C (swp E (reg n i k) (reg n i (bar k))) (i - 1) := by
    intro E hE
    have hoff := off_swp E (lvl_reg (by omega) hin k) (lvl_reg (by omega) hin (bar k))
    exact ⟨(hoff.geq_iff hl (by omega) hin).2 hE.1, fun k' => by
      rw [hoff.psum_eq hl hln (by omega)]; exact hE.2 k'⟩
  have gpir : ∀ bx by' E E' OF' b, GP C E (i - 1) →
      (prog n).Returns (.incrPair (i - 1) bx by') E OF E' OF' b → GP C E' (i - 1) := by
    intro bx by' E E' OF' b hE hr
    obtain ⟨-, -, hps⟩ := (ir bx by' E hE.1).2.2 _ _ _ hr
    exact ⟨hps.geq hl hln hE.1, fun k' => (hps.2 k').trans (hE.2 k')⟩
  have gplg : ∀ (a : Fin 4) E, GP C E (i - 1) → N (i - 1) ≤ E (reg n (i - 1) a) →
      GP C (lg E (reg n (i - 1) a) (reg n (i - 1) (bar a)) (N (i - 1))) (i - 1) := by
    intro a E hE hm
    have := ps_lg hl hln a hm (C := E)
    exact ⟨this.geq hl hln hE.1, fun k' => (this.2 k').trans (hE.2 k')⟩
  have gplgx : ∀ E, GP C E (i - 1) → N (i - 1) ≤ E (reg n (i - 1) 1) →
      GP C (lg E (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1))) (i - 1) := fun E hE hm => gplg 1 E hE hm
  have gplgy : ∀ E, GP C E (i - 1) → N (i - 1) ≤ E (reg n (i - 1) 3) →
      GP C (lg E (reg n (i - 1) 3) (reg n (i - 1) 2) (N (i - 1))) (i - 1) := fun E hE hm => gplg 3 E hE hm
  have mvl : ∀ E (a b c : Fin 4), mv E (reg n i a) (reg n i b) (reg n (i - 1) c) = E (reg n (i - 1) c) :=
    fun E a b c => mv_apply_ne (hlvne c a) (hlvne c b)
  have lgxy : ∀ E, lg E (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1)) (reg n (i - 1) 2) =
      E (reg n (i - 1) 2) := fun E => lg_apply_other _ (Ne.symm r12) (Ne.symm r02) _
  have lgxyb : ∀ E, lg E (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1)) (reg n (i - 1) 3) =
      E (reg n (i - 1) 3) := fun E => lg_apply_other _ (Ne.symm r13) (Ne.symm r03) _
  have lgxb : ∀ E, lg E (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1)) (reg n (i - 1) 1) =
      E (reg n (i - 1) 0) + N (i - 1) := fun E => lg_apply_x _ (Ne.symm r01) _
  have lgyb : ∀ E, lg E (reg n (i - 1) 3) (reg n (i - 1) 2) (N (i - 1)) (reg n (i - 1) 3) =
      E (reg n (i - 1) 2) + N (i - 1) := fun E => lg_apply_x _ (Ne.symm r23) _
  have hgpC : GP C C (i - 1) := ⟨hC.geq, fun _ => rfl⟩
  -- the invariant
  let I : Loc (Reg n) → Prop := fun a => a.OF = OF ∧ GP C a.C (i - 1) ∧ SInv n i k OF C a.pc a.C
  have hIinv : ∀ a a', I a → (prog n).AStep (.large i k) a a' → I a' := by
    rintro ⟨pc, E, OF₁⟩ a' ⟨rfl, hgp, hI⟩ hs
    rw [astep_iff] at hs
    have hlt := hI.lt
    simp only at hlt hI hgp ⊢
    interval_cases pc <;> simp only [SInv, SMid, and_false, exists_false, false_and] at hI <;>
      simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero] at hs
    · -- 0
      subst hI
      obtain ⟨E', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, ⟨rfl, rfl, -⟩ | ⟨rfl, hm, rfl⟩⟩ := (zx E hgp.1 _ _ _).1 hr
      · exact ⟨rfl, hgp, trivial⟩
      · exact ⟨rfl, gplgx E hgp hm, hm, rfl⟩
    · -- 1
      obtain ⟨hmx, rfl⟩ := hI
      obtain ⟨E', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, ⟨rfl, rfl, -⟩ | ⟨rfl, hm, rfl⟩⟩ := (zy _ hgp.1 _ _ _).1 hr
      · exact ⟨rfl, hgp, trivial⟩
      · refine ⟨rfl, gplgy _ hgp hm, hmx, by rwa [lgxyb] at hm, _, .refl, rfl⟩
    · subst hs; exact ⟨rfl, hgp, hI⟩
    · -- 5: AssertProper
      obtain ⟨E', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, rfl, -⟩ := ((ap E hgp.1).1 _ _ _).1 hr
      simp only [Bool.cond_self]
      exact ⟨rfl, hgp, hI⟩
    · -- 6: detect x
      obtain ⟨hmx, hmy, D₀, hst, rfl⟩ := hI
      rcases hs with ⟨hx, rfl⟩ | rfl
      · exact ⟨rfl, hgp, hmx, hmy, E, hst, rfl, hx⟩
      · exact ⟨rfl, hgp, hmx, hmy, E, hst, rfl⟩
    · -- 7: move
      obtain ⟨hmx, hmy, D₀, hst, rfl, hx⟩ := hI
      obtain ⟨-, rfl⟩ := hs
      exact ⟨rfl, gpmv _ _ _ hgp, hmx, hmy, E, hst, hx, rfl⟩
    · -- 8: IncrPair
      obtain ⟨hmx, hmy, D₀, hst, hx, rfl⟩ := hI
      obtain ⟨E', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, rfl, -⟩ := (ir false false _ hgp.1).2.2 _ _ _ hr
      simp only [Bool.cond_self]
      exact ⟨rfl, gpir _ _ _ _ _ _ hgp hr, hmx, hmy, D₀, hst, hx, hr⟩
    · -- 9: Zero(x_{i-1})
      obtain ⟨hmx, hmy, D₀, hst, hx, hir⟩ := hI
      obtain ⟨E', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, ⟨rfl, rfl, hp⟩ | ⟨rfl, hm, rfl⟩⟩ := (zx E hgp.1 _ _ _).1 hr
      · exact ⟨rfl, hgp, hmx, hmy, D₀, hst, .inl ⟨hx, hir, hp⟩⟩
      · exact ⟨rfl, gplgx E hgp hm, hmx, hmy, D₀, hst, hx, E, hir, hm, rfl⟩
    · -- 10: Zero(y_{i-1})
      obtain ⟨hmx, hmy, D₀, hst, hx, F, hir, hm, rfl⟩ := hI
      obtain ⟨E', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, ⟨rfl, rfl, hp⟩ | ⟨rfl, hm', rfl⟩⟩ := (zy _ hgp.1 _ _ _).1 hr
      · exact ⟨rfl, hgp, hmx, hmy, D₀, hst, .inr (.inl ⟨hx, F, hir, hm, hp, rfl⟩)⟩
      · exact ⟨rfl, gplgy _ hgp hm', hmx, hmy, D₀, hst, trivial⟩
    · obtain ⟨hmx, hmy, D₀, hst, -⟩ := hI
      subst hs; exact ⟨rfl, gpswp E hgp, hmx, hmy, D₀, hst, trivial⟩
    · subst hs; exact ⟨rfl, hgp, hI⟩
    · -- 15: Zero(x_{i-1})
      obtain ⟨hmx, hmy, D₀, hst, hE⟩ := hI
      subst hE
      obtain ⟨E', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, ⟨rfl, rfl, hp⟩ | ⟨rfl, hm, rfl⟩⟩ := (zx _ hgp.1 _ _ _).1 hr
      · exact ⟨rfl, hgp, hmx, hmy, _, hst, .inl ⟨hp, rfl⟩⟩
      · exact ⟨rfl, gplgx _ hgp hm, hmx, hmy, _, hst, hm, rfl⟩
    · -- 16: Zero(y_{i-1})
      obtain ⟨hmx, hmy, D₀, hst, hm, rfl⟩ := hI
      obtain ⟨E', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, ⟨rfl, rfl, hp⟩ | ⟨rfl, hm', rfl⟩⟩ := (zy _ hgp.1 _ _ _).1 hr
      · exact ⟨rfl, hgp, hmx, hmy, D₀, hst, .inr ⟨hm, hp, rfl⟩⟩
      · exact ⟨rfl, gplgy _ hgp hm', hmx, hmy, D₀, hst, trivial⟩
    · -- 19: detect x̄
      obtain ⟨hmx, hmy, D₀, hst, hB⟩ := hI
      rcases hs with ⟨hx, rfl⟩ | rfl
      · exact ⟨rfl, hgp, hmx, hmy, D₀, hst, hB, hx⟩
      · exact ⟨rfl, hgp, hmx, hmy, D₀, hst, .inr (.inr (.inl hB))⟩
    · -- 20: move
      obtain ⟨hmx, hmy, D₀, hst, hB, hx⟩ := hI
      obtain ⟨-, rfl⟩ := hs
      exact ⟨rfl, gpmv _ _ _ hgp, hmx, hmy, D₀, hst, E, hB, hx, rfl⟩
    · -- 21: IncrPair
      obtain ⟨hmx, hmy, D₀, hst, H, hB, hx, rfl⟩ := hI
      obtain ⟨E', OF', b, hr, rfl⟩ := hs
      obtain ⟨rfl, rfl, -⟩ := (ir true true _ hgp.1).2.2 _ _ _ hr
      simp only [Bool.cond_self]
      exact ⟨rfl, gpir _ _ _ _ _ _ hgp hr, hmx, hmy, D₀, hst, .inr (.inr (.inr ⟨H, hB, hx, hr⟩))⟩
    · subst hs; exact ⟨rfl, hgp, hI⟩
    · -- 23: next loop head
      obtain ⟨hmx, hmy, D₀, hst, hit⟩ := hI
      subst hs
      exact ⟨rfl, hgp, hmx, hmy, E, hst.tail hit, rfl⟩
  have hreach : ∀ a, (prog n).AReach (.large i k) ⟨0, C, OF⟩ a → I a :=
    fun a ha => AReach.inv hIinv ha ⟨rfl, hgpC, rfl⟩
  -- every configuration of the loop is `(i−1)`-high
  have hhigh : ∀ E, GP C E (i - 1) → N (i - 1) ≤ C (reg n (i - 1) 1) →
      N (i - 1) ≤ C (reg n (i - 1) 3) → High E (i - 1) := by
    intro E hE hmx hmy
    refine ⟨hE.1.1, fun hP => ?_, hE.1.2.1, hE.1.2.2⟩
    obtain ⟨-, e0, e1, e2, e3⟩ := (proper_succ_iff hl).1 hP
    have s0 := hE.2 0; have s2 := hE.2 2
    simp only [psum, show bar 0 = 1 from rfl, show bar 2 = 3 from rfl, e0, e1, e2, e3] at s0 s2
    apply hC.2.1
    rw [proper_succ_iff hl]
    exact ⟨hC.1, by omega, by omega, by omega, by omega⟩
  -- existence of callee returns
  have zxr : ∀ E, Geq E (i - 1) → ∀ b, (b = false ∧ 0 < E (reg n (i - 1) 0)) ∨
      (b = true ∧ N (i - 1) ≤ E (reg n (i - 1) 1)) → ∃ E', (prog n).Returns (.zero (i - 1) 0) E OF E' OF b ∧
        (b = false → E' = E) ∧ (b = true → E' = lg E (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1))) := by
    rintro E hE b (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨E, (zx E hE _ _ _).2 ⟨rfl, .inl ⟨rfl, rfl, h⟩⟩, fun _ => rfl, by simp⟩
    · exact ⟨_, (zx E hE _ _ _).2 ⟨rfl, .inr ⟨rfl, h, rfl⟩⟩, by simp, fun _ => rfl⟩
  have zyr : ∀ E, Geq E (i - 1) → ∀ b, (b = false ∧ 0 < E (reg n (i - 1) 2)) ∨
      (b = true ∧ N (i - 1) ≤ E (reg n (i - 1) 3)) → ∃ E', (prog n).Returns (.zero (i - 1) 2) E OF E' OF b ∧
        (b = false → E' = E) ∧ (b = true → E' = lg E (reg n (i - 1) 3) (reg n (i - 1) 2) (N (i - 1))) := by
    rintro E hE b (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨E, (zy E hE _ _ _).2 ⟨rfl, .inl ⟨rfl, rfl, h⟩⟩, fun _ => rfl, by simp⟩
    · exact ⟨_, (zy E hE _ _ _).2 ⟨rfl, .inr ⟨rfl, h, rfl⟩⟩, by simp, fun _ => rfl⟩
  have pHead : ∀ D, Geq D (i - 1) → (prog n).AReach (.large i k) ⟨4, D, OF⟩ ⟨6, D, OF⟩ := fun D hD =>
    .head (.goto (by ins)) (.single (.call (by ins) (((ap D hD).1 D OF false).2 ⟨rfl, rfl, rfl⟩)))
  have hGir : ∀ bx by' E E', Geq E (i - 1) →
      (prog n).Returns (.incrPair (i - 1) bx by') E OF E' OF false → Geq E' (i - 1) := by
    intro bx by' E E' hE hr
    obtain ⟨-, -, hps⟩ := (ir bx by' E hE).2.2 _ _ _ hr
    exact hps.geq hl hln hE
  have hGmv : ∀ E (a b : Fin 4), Geq E (i - 1) → Geq (mv E (reg n i a) (reg n i b)) (i - 1) :=
    fun E a b hE => (geq_mv hl hln hZB hZC (hlv a) (hlv b)).2 hE
  have hGlg : ∀ E, Geq E (i - 1) → N (i - 1) ≤ E (reg n (i - 1) 1) →
      Geq (lg E (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1))) (i - 1) := fun E hE hm =>
    (ps_lg hl hln 1 hm (C := E)).geq hl hln hE
  -- one iteration is a path between loop heads
  have iter_path : ∀ D D', Geq D (i - 1) → Iter n i k OF D D' →
      (prog n).AReach (.large i k) ⟨4, D, OF⟩ ⟨4, D', OF⟩ := by
    intro D D' hD h
    have tail14 : ∀ E, (prog n).AReach (.large i k) ⟨14, E, OF⟩ ⟨4, E, OF⟩ := fun E =>
      .head (.goto (by ins)) (.single (.goto (by ins)))
    have pre8 : 0 < D (reg n i k) → (prog n).AReach (.large i k) ⟨4, D, OF⟩
        ⟨8, mv D (reg n i k) (reg n i (bar k)), OF⟩ := fun hx =>
      (pHead D hD).trans (.head (.detectT (by ins) hx) (.single (.move (by ins) hx)))
    -- the `else` branch up to line 19
    have pre19 : ∀ H, Bpre n i D H → (prog n).AReach (.large i k) ⟨4, D, OF⟩ ⟨19, H, OF⟩ := by
      intro H hB
      refine (pHead D hD).trans (.head (.detectF (by ins)) ?_)
      rcases hB with ⟨hp, rfl⟩ | ⟨hm, hp, rfl⟩
      · obtain ⟨E', hr, h1, -⟩ := zxr H hD false (.inl ⟨rfl, hp⟩)
        rw [h1 rfl] at hr
        exact .single (.call (by ins) hr)
      · obtain ⟨E', hr, -, h1⟩ := zxr D hD true (.inr ⟨rfl, hm⟩)
        rw [h1 rfl] at hr
        obtain ⟨E'', hr', h2, -⟩ := zyr _ (hGlg D hD hm) false (.inl ⟨rfl, hp⟩)
        rw [h2 rfl] at hr'
        exact .head (.call (by ins) hr) (.single (.call (by ins) hr'))
    rcases h with ⟨hx, hr, hp⟩ | ⟨hx, F, hr, hm, hp, rfl⟩ | hB | ⟨H, hB, hxb, hr⟩
    · have hD' := hGir _ _ _ _ (hGmv D k (bar k) hD) hr
      obtain ⟨E', hr', h1, -⟩ := zxr D' hD' false (.inl ⟨rfl, hp⟩)
      rw [h1 rfl] at hr'
      exact (pre8 hx).trans (.head (.call (by ins) hr) (.head (.call (by ins) hr') (tail14 _)))
    · have hF := hGir _ _ _ _ (hGmv D k (bar k) hD) hr
      obtain ⟨E', hr', -, h1⟩ := zxr F hF true (.inr ⟨rfl, hm⟩)
      rw [h1 rfl] at hr'
      obtain ⟨E'', hr'', h2, -⟩ := zyr _ (hGlg F hF hm) false (.inl ⟨rfl, hp⟩)
      rw [h2 rfl] at hr''
      exact (pre8 hx).trans (.head (.call (by ins) hr) (.head (.call (by ins) hr')
        (.head (.call (by ins) hr'') (tail14 _))))
    · exact (pre19 D' hB).trans (.head (.detectF (by ins)) (.single (.goto (by ins))))
    · exact (pre19 H hB).trans (.head (.detectT (by ins) hxb) (.head (.move (by ins) hxb)
        (.head (.call (by ins) hr) (.head (.goto (by ins)) (.single (.goto (by ins)))))))
  -- back to the first loop head
  have hgpStar : N (i - 1) ≤ C (reg n (i - 1) 1) → N (i - 1) ≤ C (reg n (i - 1) 3) →
      GP C (Cstar n i C) (i - 1) := fun hmx hmy =>
    gplgy _ (gplgx C hgpC hmx) (by rwa [lgxyb])
  have back : N (i - 1) ≤ C (reg n (i - 1) 1) → N (i - 1) ≤ C (reg n (i - 1) 3) → ∀ E,
      Relation.ReflTransGen (Iter n i k OF) (Cstar n i C) E →
      GP C E (i - 1) ∧ (prog n).AReach (.large i k) ⟨4, E, OF⟩ ⟨4, Cstar n i C, OF⟩ := by
    intro hmx hmy E hE
    induction hE with
    | refl => exact ⟨hgpStar hmx hmy, .refl⟩
    | tail _ hit ih =>
      obtain ⟨hgp1, hp1⟩ := ih
      have hgp2 := iter_gp hi hin k OF hZB hZC hgp1 hit
      exact ⟨hgp2, (iter_path _ _ hgp2.1 (iter_symm hi hin k OF hZB hZC hIB hgp1.1 hit)).trans hp1⟩
  have fromStar : N (i - 1) ≤ C (reg n (i - 1) 1) → N (i - 1) ≤ C (reg n (i - 1) 3) →
      ∃ E, (prog n).AReach (.large i k) ⟨4, Cstar n i C, OF⟩ ⟨17, E, OF⟩ := by
    intro hmx hmy
    have hS := (hgpStar hmx hmy).1
    have hm1 : N (i - 1) ≤ Cstar n i C (reg n (i - 1) 1) := by
      simp only [Cstar]
      rw [lg_apply_other _ r13 r12, lgxb]; omega
    obtain ⟨E', hr, -, h1⟩ := zxr _ hS true (.inr ⟨rfl, hm1⟩)
    rw [h1 rfl] at hr
    have hm2 : N (i - 1) ≤ lg (Cstar n i C) (reg n (i - 1) 1) (reg n (i - 1) 0) (N (i - 1))
        (reg n (i - 1) 3) := by
      rw [lgxyb]; simp only [Cstar]; rw [lgyb]; omega
    obtain ⟨E'', hr', -, h2⟩ := zyr _ (hGlg _ hS hm1) true (.inr ⟨rfl, hm2⟩)
    rw [h2 rfl] at hr'
    exact ⟨_, (pHead _ hS).trans (.head (.detectF (by ins)) (.head (.call (by ins) hr)
      (.single (.call (by ins) hr'))))⟩
  have hcallT : ∀ a, (prog n).AReach (.large i k) ⟨0, C, OF⟩ a → ∀ q tT tF,
      (prog n).instr (.large i k) a.pc = some (.call q tT tF) → (prog n).Terminates q a.C a.OF := by
    intro a ha q tT tF hq
    obtain ⟨hOF, hgp, hI⟩ := hreach a ha
    obtain ⟨pc, E, OF₁⟩ := a
    have hlt := hI.lt
    simp only at hOF hgp hI hq hlt ⊢
    subst hOF
    interval_cases pc <;>
      simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Instr.call.injEq, reduceCtorEq] at hq <;> obtain ⟨rfl, -, -⟩ := hq
    all_goals first
      | exact (hZB _ E _ hgp.1.1 (hgp.1.psum _)).2.2
      | exact (ap E hgp.1).2.2
      | exact (ir _ _ E hgp.1).1
  have hrank : ∀ a, (prog n).AReach (.large i k) ⟨0, C, OF⟩ a →
      ((prog n).ADone (.large i k) a ∨ a.pc = 23) ∨ ∃ a', (prog n).AStep (.large i k) a a' ∧
        (if a'.pc ≤ 3 then 40 - a'.pc else 30 - a'.pc) < (if a.pc ≤ 3 then 40 - a.pc else 30 - a.pc) := by
    intro a ha
    obtain ⟨hOF, hgp, hI⟩ := hreach a ha
    obtain ⟨pc, E, OF₁⟩ := a
    have hlt := hI.lt
    simp only at hOF hgp hI hlt ⊢
    have callStep : ∀ q tT tF, (prog n).instr (.large i k) pc = some (.call q tT tF) →
        (pc < tT ∧ pc < tF ∧ (pc ≤ 3 ∨ (4 ≤ tT ∧ 4 ≤ tF))) →
        ((prog n).ADone (.large i k) ⟨pc, E, OF₁⟩ ∨ pc = 23) ∨
          ∃ a', (prog n).AStep (.large i k) ⟨pc, E, OF₁⟩ a' ∧
            (if a'.pc ≤ 3 then 40 - a'.pc else 30 - a'.pc) < (if pc ≤ 3 then 40 - pc else 30 - pc) := by
      intro q tT tF hq hlt'
      rcases (hcallT ⟨pc, E, OF₁⟩ ha q tT tF hq).returns_or_restarts with ⟨C', OF', b, hr⟩ | hr
      · refine .inr ⟨_, .call hq hr, ?_⟩
        cases b <;> simp only [cond_true, cond_false] <;> split_ifs <;> omega
      · exact .inl (.inl (.inr (.inr ⟨q, tT, tF, hq, hr⟩)))
    interval_cases pc <;> simp only [SInv, SMid, and_false, exists_false, false_and] at hI
    · exact callStep _ _ _ (by ins) (by omega)
    · exact callStep _ _ _ (by ins) (by omega)
    · exact .inl (.inl (.inr (.inl (by ins))))
    · exact .inr ⟨_, .goto (by ins), by simp⟩
    · exact callStep _ _ _ (by ins) (by omega)
    · exact .inr ⟨_, .detectF (by ins), by simp⟩
    · obtain ⟨-, -, D₀, -, rfl, hx⟩ := hI
      exact .inr ⟨_, .move (by ins) hx, by simp⟩
    · exact callStep _ _ _ (by ins) (by omega)
    · exact callStep _ _ _ (by ins) (by omega)
    · exact callStep _ _ _ (by ins) (by omega)
    · exact .inr ⟨_, .swap (by ins), by simp⟩
    · exact .inl (.inl (.inl ⟨true, by ins⟩))
    · exact .inr ⟨_, .goto (by ins), by simp⟩
    · exact callStep _ _ _ (by ins) (by omega)
    · exact callStep _ _ _ (by ins) (by omega)
    · exact .inl (.inl (.inl ⟨false, by ins⟩))
    · exact .inr ⟨_, .detectF (by ins), by simp⟩
    · obtain ⟨-, -, D₀, -, -, hx⟩ := hI
      exact .inr ⟨_, .move (by ins) hx, by simp⟩
    · exact callStep _ _ _ (by ins) (by omega)
    · exact .inr ⟨_, .goto (by ins), by simp⟩
    · exact .inl (.inr rfl)
  refine ⟨terminates_of hcallT (fun a ha => ?_), fun C' OF' b h => ?_⟩
  · obtain ⟨a', haa', hT⟩ := exists_target_of_rank
      (T := fun a => (prog n).ADone (.large i k) a ∨ a.pc = 23)
      (fun a => if a.pc ≤ 3 then 40 - a.pc else 30 - a.pc) hrank a ha
    rcases hT with hd | h23
    · exact ⟨a', haa', hd⟩
    · obtain ⟨hOF, hgp, hI⟩ := hreach a' (ha.trans haa')
      obtain ⟨pc, E, OF₁⟩ := a'
      simp only at h23 hOF hgp hI
      subst h23 hOF
      simp only [SInv, SMid] at hI
      obtain ⟨hmx, hmy, D₀, hst, hit⟩ := hI
      obtain ⟨-, hb⟩ := back hmx hmy E (hst.tail hit)
      obtain ⟨E17, h17⟩ := fromStar hmx hmy
      exact ⟨_, haa'.trans (.head (.goto (by ins)) (hb.trans h17)), .inl ⟨false, by ins⟩⟩
  · obtain ⟨a, ha, rfl, rfl, hb⟩ := returns_iff.1 h
    obtain ⟨hOF, hgp, hI⟩ := hreach a ha
    obtain ⟨pc, E, OF₁⟩ := a
    have hlt := hI.lt
    simp only at hlt hOF hgp hI hb ⊢
    refine ⟨hOF, ?_⟩
    interval_cases pc <;> simp only [SInv, SMid, and_false, exists_false, false_and] at hI <;>
      simp [Program.instr, hcode] at hb
    all_goals (obtain ⟨hmx, hmy, -⟩ := hI; exact hhigh E hgp hmx hmy)

end Podc.PPDoubleExpThresholds
