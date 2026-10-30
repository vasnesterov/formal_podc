import Papers.PODC2023.PPDoubleExpThresholds.Zero

/-!
# Lemma 11: `IncrPair(x, y)`

The code of `IncrPair` is straight-line; `incr_returns_iff`, `incr_restarts_iff` and
`incr_terminates` describe it in terms of its two calls of `Zero`.
-/

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

set_option hygiene false in
local macro "ins" : tactic => `(tactic| (rw [Program.instr, hcode]; try rfl))

section

variable (n) (i : ℕ) (bx by' : Bool)

/-- `Zero(z)` at level `i` returns `b` with `D'`. -/
abbrev ZR (k : Fin 4) (D : Reg n → ℕ) (OF : Bool) (D' : Reg n → ℕ) (OF' b : Bool) : Prop :=
  (prog n).Returns (.zero i k) D OF D' OF' b

end

/-- The final register configuration of `IncrPair` in each branch. -/
def IFin (n i : ℕ) (bx by' : Bool) (C : Reg n → ℕ) (OF : Bool) (D : Reg n → ℕ) (OF' : Bool) :
    Prop :=
  (∃ C1, ZR n i (bar (ky by')) C OF C1 OF' false ∧ 0 < C1 (reg n i (bar (ky by'))) ∧
    D = mv C1 (reg n i (bar (ky by'))) (reg n i (ky by'))) ∨
  (∃ C1 OF1 C3, ZR n i (bar (ky by')) C OF C1 OF1 true ∧
    ZR n i (bar (kx bx)) (swp C1 (reg n i (ky by')) (reg n i (bar (ky by')))) OF1 C3 OF' true ∧
    D = swp C3 (reg n i (kx bx)) (reg n i (bar (kx bx)))) ∨
  (∃ C1 OF1 C3, ZR n i (bar (ky by')) C OF C1 OF1 true ∧
    ZR n i (bar (kx bx)) (swp C1 (reg n i (ky by')) (reg n i (bar (ky by')))) OF1 C3 OF' false ∧
    0 < C3 (reg n i (bar (kx bx))) ∧ D = mv C3 (reg n i (bar (kx bx))) (reg n i (kx bx)))

/-- The invariant of `IncrPair`. -/
def IInv (n i : ℕ) (bx by' : Bool) (C : Reg n → ℕ) (OF : Bool) (pc : ℕ) (D : Reg n → ℕ)
    (OF' : Bool) : Prop :=
  match pc with
  | 0 => D = C ∧ OF' = OF
  | 1 => ZR n i (bar (ky by')) C OF D OF' true
  | 2 => ∃ C1, ZR n i (bar (ky by')) C OF C1 OF' true ∧
      D = swp C1 (reg n i (ky by')) (reg n i (bar (ky by')))
  | 3 => ∃ C1 OF1, ZR n i (bar (ky by')) C OF C1 OF1 true ∧
      ZR n i (bar (kx bx)) (swp C1 (reg n i (ky by')) (reg n i (bar (ky by')))) OF1 D OF' true
  | 5 => ∃ C1 OF1, ZR n i (bar (ky by')) C OF C1 OF1 true ∧
      ZR n i (bar (kx bx)) (swp C1 (reg n i (ky by')) (reg n i (bar (ky by')))) OF1 D OF' false
  | 7 => ZR n i (bar (ky by')) C OF D OF' false
  | 4 => IFin n i bx by' C OF D OF'
  | 6 => IFin n i bx by' C OF D OF'
  | 8 => IFin n i bx by' C OF D OF'
  | _ => False

theorem IInv.lt {i : ℕ} {bx by' : Bool} {C : Reg n → ℕ} {OF : Bool} {pc : ℕ} {D : Reg n → ℕ}
    {OF' : Bool} (h : IInv n i bx by' C OF pc D OF') : pc < 9 := by
  unfold IInv at h; split at h <;> first | omega | exact h.elim

section

variable {i : ℕ} (bx by' : Bool)

theorem incr_reach {C : Reg n → ℕ} {OF : Bool} (hZC : ZeroC n i) :
    ∀ a, (prog n).AReach (.incrPair i bx by') ⟨0, C, OF⟩ a → IInv n i bx by' C OF a.pc a.C a.OF := by
  have hcode := code_incrPair n i bx by'
  intro a ha
  refine AReach.inv (I := fun a => IInv n i bx by' C OF a.pc a.C a.OF) ?_ ha ⟨rfl, rfl⟩
  rintro ⟨pc, D, OF₁⟩ a' hI hs
  rw [astep_iff] at hs
  have hlt := hI.lt
  simp only at hlt hI ⊢
  interval_cases pc <;> simp only [IInv] at hI <;>
    simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero] at hs
  · obtain ⟨rfl, rfl⟩ := hI
    obtain ⟨C', OF', b, hr, rfl⟩ := hs
    cases b
    · exact hr
    · exact hr
  · subst hs; exact ⟨D, hI, rfl⟩
  · obtain ⟨C1, h1, rfl⟩ := hI
    obtain ⟨C', OF', b, hr, rfl⟩ := hs
    cases b
    · exact ⟨C1, OF₁, h1, hr⟩
    · exact ⟨C1, OF₁, h1, hr⟩
  · obtain ⟨C1, OF1, h1, h2⟩ := hI
    subst hs; exact .inr (.inl ⟨C1, OF1, D, h1, h2, rfl⟩)
  · subst hs; exact hI
  · obtain ⟨C1, OF1, h1, h2⟩ := hI
    obtain ⟨hpos, rfl⟩ := hs
    exact .inr (.inr ⟨C1, OF1, D, h1, h2, hpos, rfl⟩)
  · subst hs; exact hI
  · obtain ⟨hpos, rfl⟩ := hs
    exact .inl ⟨D, hI, hpos, rfl⟩

/-- `IncrPair` returns exactly as described by `IFin` (and always returns `false`). -/
theorem incr_returns_iff {C : Reg n → ℕ} {OF : Bool} (hZC : ZeroC n i) {C' : Reg n → ℕ}
    {OF' b : Bool} :
    (prog n).Returns (.incrPair i bx by') C OF C' OF' b ↔ b = false ∧ IFin n i bx by' C OF C' OF' := by
  have hcode := code_incrPair n i bx by'
  constructor
  · intro h
    obtain ⟨a, ha, rfl, rfl, hb⟩ := returns_iff.1 h
    have hI := incr_reach bx by' hZC a ha
    obtain ⟨pc, D, OF₁⟩ := a
    have hlt := hI.lt
    simp only at hlt hI hb ⊢
    interval_cases pc <;> simp only [IInv] at hI <;>
      simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Instr.ret.injEq, reduceCtorEq] at hb
    exact ⟨hb.symm, hI⟩
  · rintro ⟨rfl, hF⟩
    refine returns_iff.2 ⟨⟨8, C', OF'⟩, ?_, rfl, rfl, by ins⟩
    rcases hF with ⟨C1, h1, hpos, rfl⟩ | ⟨C1, OF1, C3, h1, h3, rfl⟩ | ⟨C1, OF1, C3, h1, h3, hpos, rfl⟩
    · exact .head (.call (by ins) h1) (.single (.move (by ins) hpos))
    · exact .head (.call (by ins) h1) (.head (.swap (by ins)) (.head (.call (by ins) h3)
        (.head (.swap (by ins)) (.head (.goto (by ins)) (.single (.goto (by ins)))))))
    · exact .head (.call (by ins) h1) (.head (.swap (by ins)) (.head (.call (by ins) h3)
        (.head (.move (by ins) hpos) (.single (.goto (by ins))))))

/-- `IncrPair` restarts iff one of its `Zero` calls does. -/
theorem incr_restarts_iff {C : Reg n → ℕ} {OF : Bool} (hZC : ZeroC n i) :
    (prog n).Restarts (.incrPair i bx by') C OF ↔
      (prog n).Restarts (.zero i (bar (ky by'))) C OF ∨
      ∃ C1 OF1, ZR n i (bar (ky by')) C OF C1 OF1 true ∧
        (prog n).Restarts (.zero i (bar (kx bx)))
          (swp C1 (reg n i (ky by')) (reg n i (bar (ky by')))) OF1 := by
  have hcode := code_incrPair n i bx by'
  constructor
  · intro h
    obtain ⟨a, ha, hr⟩ := restarts_iff.1 h
    have hI := incr_reach bx by' hZC a ha
    obtain ⟨pc, D, OF₁⟩ := a
    have hlt := hI.lt
    simp only at hlt hI hr
    rcases hr with hr | ⟨q, tT, tF, hq, hr⟩
    · interval_cases pc <;> simp [Program.instr, hcode] at hr
    · interval_cases pc <;> simp only [IInv] at hI <;>
        simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq, Instr.call.injEq, reduceCtorEq] at hq <;> obtain ⟨rfl, -, -⟩ := hq
      · obtain ⟨rfl, rfl⟩ := hI; exact .inl hr
      · obtain ⟨C1, h1, rfl⟩ := hI; exact .inr ⟨C1, OF₁, h1, hr⟩
  · rintro (h | ⟨C1, OF1, h1, h⟩)
    · exact restarts_iff.2 ⟨_, .refl, .inr ⟨_, 1, 7, by ins, h⟩⟩
    · exact restarts_iff.2 ⟨⟨2, _, OF1⟩, .head (.call (by ins) h1) (.single (.swap (by ins))),
        .inr ⟨_, 3, 5, by ins, h⟩⟩

/-- `IncrPair` terminates if its `Zero` calls do. -/
theorem incr_terminates {C : Reg n → ℕ} {OF : Bool} (hZC : ZeroC n i)
    (h1 : (prog n).Terminates (.zero i (bar (ky by'))) C OF)
    (h2 : ∀ C1 OF1, ZR n i (bar (ky by')) C OF C1 OF1 true →
      (prog n).Terminates (.zero i (bar (kx bx)))
        (swp C1 (reg n i (ky by')) (reg n i (bar (ky by')))) OF1) :
    (prog n).Terminates (.incrPair i bx by') C OF := by
  have hcode := code_incrPair n i bx by'
  refine terminates_of (fun a ha q tT tF hq => ?_) (fun a ha => ?_)
  · have hI := incr_reach bx by' hZC a ha
    obtain ⟨pc, D, OF₁⟩ := a
    have hlt := hI.lt
    simp only at hlt hI hq ⊢
    interval_cases pc <;> simp only [IInv] at hI <;>
      simp only [Program.instr, hcode, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Instr.call.injEq, reduceCtorEq] at hq <;> obtain ⟨rfl, -, -⟩ := hq
    · obtain ⟨rfl, rfl⟩ := hI; exact h1
    · obtain ⟨C1, hC1, rfl⟩ := hI; exact h2 C1 OF₁ hC1
  · refine exists_target_of_rank (T := (prog n).ADone (.incrPair i bx by')) (fun a => 9 - a.pc)
      (fun a ha => ?_) a ha
    have hI := incr_reach bx by' hZC a ha
    obtain ⟨pc, D, OF₁⟩ := a
    have hlt := hI.lt
    simp only at hlt hI ⊢
    interval_cases pc <;> simp only [IInv] at hI
    · obtain ⟨rfl, rfl⟩ := hI
      rcases h1.returns_or_restarts with ⟨C', OF', b, hr⟩ | hr
      · exact .inr ⟨_, .call (by ins) hr, by cases b <;> simp⟩
      · exact .inl (.inr (.inr ⟨_, 1, 7, by ins, hr⟩))
    · exact .inr ⟨_, .swap (by ins), by simp⟩
    · obtain ⟨C1, hC1, rfl⟩ := hI
      rcases (h2 C1 OF₁ hC1).returns_or_restarts with ⟨C', OF', b, hr⟩ | hr
      · exact .inr ⟨_, .call (by ins) hr, by cases b <;> simp⟩
      · exact .inl (.inr (.inr ⟨_, 3, 5, by ins, hr⟩))
    · exact .inr ⟨_, .swap (by ins), by simp⟩
    · exact .inr ⟨_, .goto (by ins), by simp⟩
    · obtain ⟨C1, OF1, -, h3⟩ := hI
      exact .inr ⟨_, .move (by ins) (hZC _ _ _ _ _ h3), by simp⟩
    · exact .inr ⟨_, .goto (by ins), by simp⟩
    · exact .inr ⟨_, .move (by ins) (hZC _ _ _ _ _ hI), by simp⟩
    · exact .inl (.inl ⟨false, by ins⟩)

end

/-! ### Register bookkeeping -/

theorem ky_not (b : Bool) : ky (!b) = bar (ky b) := by cases b <;> rfl
theorem kx_not (b : Bool) : kx (!b) = bar (kx b) := by cases b <;> rfl

/-- `C'` and `C` agree outside level `i` and have the same pair sums on level `i`. -/
def PS (C C' : Reg n → ℕ) (i : ℕ) : Prop := Off C C' i ∧ ∀ k, psum C' i k = psum C i k

theorem PS.refl (C : Reg n → ℕ) (i : ℕ) : PS C C i := ⟨Off.refl C i, fun _ => rfl⟩

theorem PS.trans {C C' C'' : Reg n → ℕ} {i : ℕ} (h : PS C C' i) (h' : PS C' C'' i) : PS C C'' i :=
  ⟨h.1.trans h'.1, fun k => (h'.2 k).trans (h.2 k)⟩

theorem PS.symm {C C' : Reg n → ℕ} {i : ℕ} (h : PS C C' i) : PS C' C i :=
  ⟨h.1.symm, fun k => (h.2 k).symm⟩

theorem PS.geq {C C' : Reg n → ℕ} {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (h : PS C C' i)
    (hC : Geq C i) : Geq C' i := by
  refine ⟨(h.1.proper_iff (by omega) hin).2 hC.1, ?_, ?_⟩ <;> rw [h.2]
  exacts [hC.2.1, hC.2.2]

section pair

variable {C C' : Reg n → ℕ} {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (k : Fin 4)
include hi hin

/-- A change inside the pair `{k, bar k}` of level `i` keeping its sum. -/
theorem ps_of_pair (hoth : ∀ z, z ≠ reg n i k → z ≠ reg n i (bar k) → C' z = C z)
    (hs : C' (reg n i k) + C' (reg n i (bar k)) = C (reg n i k) + C (reg n i (bar k))) :
    PS C C' i := by
  refine ⟨fun z hz => hoth z ?_ ?_, fun k' => ?_⟩
  · rintro rfl; exact hz (lvl_reg hi hin k)
  · rintro rfl; exact hz (lvl_reg hi hin _)
  by_cases h1 : k' = k
  · subst h1; exact hs
  by_cases h2 : k' = bar k
  · subst h2; rw [psum_bar, psum_bar]; exact hs
  have h3 : bar k' ≠ k := fun h => h2 (by rw [← h, bar_bar])
  have h4 : bar k' ≠ bar k := fun h => h1 (by rw [← bar_bar k', h, bar_bar])
  simp only [psum]
  rw [hoth _ (by rw [Ne, reg_inj hi hin hi hin]; simp [h1]) (by rw [Ne, reg_inj hi hin hi hin]; simp [h2]),
    hoth _ (by rw [Ne, reg_inj hi hin hi hin]; simp [h3]) (by rw [Ne, reg_inj hi hin hi hin]; simp [h4])]

theorem ps_mv (hpos : 0 < C (reg n i (bar k))) :
    PS C (mv C (reg n i (bar k)) (reg n i k)) i := by
  have hne := reg_ne_bar hi hin k
  refine ps_of_pair hi hin k (fun z h1 h2 => by simp [mv, h1, h2]) ?_
  simp [mv, hne, Ne.symm hne]; omega

theorem ps_mv' (hpos : 0 < C (reg n i k)) :
    PS C (mv C (reg n i k) (reg n i (bar k))) i := by
  have hne := reg_ne_bar hi hin k
  refine ps_of_pair hi hin k (fun z h1 h2 => by simp [mv, h1, h2]) ?_
  simp [mv, hne, Ne.symm hne]; omega

theorem ps_swp : PS C (swp C (reg n i k) (reg n i (bar k))) i := by
  refine ps_of_pair hi hin k (fun z h1 h2 => by simp [swp, Equiv.swap_apply_of_ne_of_ne h1 h2]) ?_
  simp [swp, Equiv.swap_apply_left, Equiv.swap_apply_right]; omega

theorem ps_lg {m : ℕ} (hm : m ≤ C (reg n i k)) :
    PS C (lg C (reg n i k) (reg n i (bar k)) m) i :=
  ⟨lg_off hi hin k m, psum_lg hi hin k hm⟩

end pair

/-! ### `IncrPair` on `Geq` configurations -/

section geq

variable {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (hZB : ZeroB n i) (hZC : ZeroC n i)
include hi hin hZB

/-- `Zero(z̄)` on `Geq` configurations. -/
theorem zr_bar (k0 : Fin 4) {D : Reg n → ℕ} {OF : Bool} (hD : Geq D i) {D' : Reg n → ℕ}
    {OF' b : Bool} : ZR n i (bar k0) D OF D' OF' b ↔ OF' = OF ∧
      ((b = false ∧ D' = D ∧ 0 < D (reg n i (bar k0))) ∨
       (b = true ∧ N i ≤ D (reg n i k0) ∧ D' = lg D (reg n i k0) (reg n i (bar k0)) (N i))) := by
  have := (hZB (bar k0) D OF hD.1 (hD.psum _)).1 D' OF' b
  simp only [bar_bar] at this
  exact this

include hZC

/-- `IncrPair` on `Geq` configurations: terminates, never restarts, returns `false`, keeps `OF`
and the pair sums, and only changes level `i` (used in the proof of Lemma 12(c)). -/
theorem incr_geq (bx by' : Bool) {C : Reg n → ℕ} {OF : Bool} (hC : Geq C i) :
    (prog n).Terminates (.incrPair i bx by') C OF ∧ ¬ (prog n).Restarts (.incrPair i bx by') C OF ∧
    ∀ C' OF' b, (prog n).Returns (.incrPair i bx by') C OF C' OF' b →
      OF' = OF ∧ b = false ∧ PS C C' i := by
  have hzB := fun k0 D (OF : Bool) (hD : Geq D i) => hZB (bar k0) D OF hD.1 (hD.psum _)
  -- the configuration after the first `Zero` returned `true` and the swap
  have hC2 : ∀ C1 OF1, ZR n i (bar (ky by')) C OF C1 OF1 true → OF1 = OF ∧
      PS C (swp C1 (reg n i (ky by')) (reg n i (bar (ky by')))) i := by
    intro C1 OF1 h1
    obtain ⟨rfl, ⟨h, -⟩ | ⟨-, hm, rfl⟩⟩ := (zr_bar hi hin hZB (ky by') hC).1 h1
    · exact absurd h (by simp)
    · exact ⟨rfl, (ps_lg hi hin _ hm).trans (ps_swp hi hin _)⟩
  refine ⟨incr_terminates bx by' hZC (hzB _ C OF hC).2.2 (fun C1 OF1 h1 => ?_), ?_, ?_⟩
  · obtain ⟨rfl, hps⟩ := hC2 C1 OF1 h1
    exact (hzB _ _ _ (hps.geq hi hin hC)).2.2
  · rw [incr_restarts_iff bx by' hZC]
    rintro (h | ⟨C1, OF1, h1, h⟩)
    · exact (hzB _ C OF hC).2.1 h
    · obtain ⟨rfl, hps⟩ := hC2 C1 OF1 h1
      exact (hzB _ _ _ (hps.geq hi hin hC)).2.1 h
  · intro C' OF' b h
    obtain ⟨rfl, hF⟩ := (incr_returns_iff bx by' hZC).1 h
    refine ⟨?_, rfl, ?_⟩ <;>
    rcases hF with ⟨C1, h1, hpos, rfl⟩ | ⟨C1, OF1, C3, h1, h3, rfl⟩ | ⟨C1, OF1, C3, h1, h3, hpos, rfl⟩
    · exact ((zr_bar hi hin hZB _ hC).1 h1).1
    · obtain ⟨rfl, hps⟩ := hC2 C1 OF1 h1
      exact ((zr_bar hi hin hZB _ (hps.geq hi hin hC)).1 h3).1
    · obtain ⟨rfl, hps⟩ := hC2 C1 OF1 h1
      exact ((zr_bar hi hin hZB _ (hps.geq hi hin hC)).1 h3).1
    · obtain ⟨-, ⟨-, rfl, -⟩ | ⟨h, -⟩⟩ := (zr_bar hi hin hZB _ hC).1 h1
      · exact ps_mv hi hin _ hpos
      · exact absurd h (by simp)
    · obtain ⟨rfl, hps⟩ := hC2 C1 OF1 h1
      obtain ⟨-, ⟨h, -⟩ | ⟨-, hm, rfl⟩⟩ := (zr_bar hi hin hZB _ (hps.geq hi hin hC)).1 h3
      · exact absurd h (by simp)
      · exact hps.trans ((ps_lg hi hin _ hm).trans (ps_swp hi hin _))
    · obtain ⟨rfl, hps⟩ := hC2 C1 OF1 h1
      obtain ⟨-, ⟨-, rfl, -⟩ | ⟨h, -⟩⟩ := (zr_bar hi hin hZB _ (hps.geq hi hin hC)).1 h3
      · exact hps.trans (ps_mv hi hin _ hpos)
      · exact absurd h (by simp)

/-- `IncrG` (the property of `IncrPair` used for Lemma 12(c)). -/
theorem incr_G : IncrG n i := by
  intro bx by' C OF hC
  obtain ⟨hT, hR, hret⟩ := incr_geq hi hin hZB hZC bx by' hC
  refine ⟨hT, hR, fun C' OF' b h => ?_⟩
  obtain ⟨h1, h2, hps⟩ := hret C' OF' b h
  exact ⟨h1, h2, hps.geq hi hin hC, hps.1⟩

end geq

/-! ### Lemma 11(a): weakly proper configurations -/

theorem digits_inj {a b a' b' m : ℕ} (hb : b ≤ m) (hb' : b' ≤ m)
    (h : a * (m + 1) + b = a' * (m + 1) + b') : a = a' ∧ b = b' := by
  have h1 : (a * (m + 1) + b) % (m + 1) = b := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have h2 : (a' * (m + 1) + b') % (m + 1) = b' := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hbb : b = b' := by rw [← h1, ← h2, h]
  subst hbb
  exact ⟨Nat.eq_of_mul_eq_mul_right (by omega : 0 < m + 1) (by omega), rfl⟩

theorem kx_cases (b : Bool) : (kx b = 0 ∧ bar (kx b) = 1) ∨ (kx b = 1 ∧ bar (kx b) = 0) := by
  cases b <;> simp [kx, bar]

theorem ky_cases (b : Bool) : (ky b = 2 ∧ bar (ky b) = 3) ∨ (ky b = 3 ∧ bar (ky b) = 2) := by
  cases b <;> simp [ky, bar]

section wproper

variable {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n)
include hi hin

/-- Weakly proper configurations with the same counter and the same other levels are equal. -/
theorem wproper_ext (bx by' : Bool) {C' C'' : Reg n → ℕ} (h' : WProper C' i) (h'' : WProper C'' i)
    (hoff : Off C' C'' i) (hctr : ctr C' i (kx bx) (ky by') = ctr C'' i (kx bx) (ky by')) :
    C' = C'' := by
  obtain ⟨hx, hy⟩ := digits_inj (h'.le _) (h''.le _) hctr
  have hxb : C' (reg n i (bar (kx bx))) = C'' (reg n i (bar (kx bx))) := by
    rw [h'.bar_eq, h''.bar_eq, hx]
  have hyb : C' (reg n i (bar (ky by'))) = C'' (reg n i (bar (ky by'))) := by
    rw [h'.bar_eq, h''.bar_eq, hy]
  funext z
  by_cases hz : z.lvl = i
  · obtain rfl | ⟨l, k, hl, hln, rfl⟩ := z.eq_reg
    · simp [Reg.lvl] at hz; omega
    rw [lvl_reg hl hln] at hz; subst hz
    rcases kx_cases bx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases ky_cases by' with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rw [h1] at hx <;> rw [h2] at hxb <;> rw [h3] at hy <;> rw [h4] at hyb <;>
      fin_cases k <;> assumption
  · exact (hoff z hz).symm

/-- **Lemma 11(a)**. -/
theorem incr_A (hZB : ZeroB n i) (hZC : ZeroC n i) : IncrA n i := by
  intro bx by' C OF hC
  obtain ⟨hT, hR, hret⟩ := incr_geq hi hin hZB hZC bx by' hC.geq
  have hN := N_pos hi
  -- the properties of every return
  have hprop : ∀ C' OF' b, (prog n).Returns (.incrPair i bx by') C OF C' OF' b →
      OF' = OF ∧ b = false ∧ WProper C' i ∧ Off C C' i ∧
      ctr C' i (kx bx) (ky by') = (ctr C i (kx bx) (ky by') + 1) % N (i + 1) := by
    intro C' OF' b h
    obtain ⟨h1, h2, hps⟩ := hret C' OF' b h
    have hw : WProper C' i :=
      ⟨(hps.1.proper_iff (by omega) hin).2 hC.1, by rw [hps.2]; exact hC.2.1,
        by rw [hps.2]; exact hC.2.2⟩
    refine ⟨h1, h2, hw, hps.1, ?_⟩
    obtain ⟨-, hF⟩ := (incr_returns_iff bx by' hZC).1 h
    have zA := fun k0 D OF (hD : WProper D i) => zeroA_of_B hi hin hZB k0 (C := D) OF hD
    have hneX := reg_ne_bar hi hin (kx bx)
    have hneY := reg_ne_bar hi hin (ky by')
    have hXY : ∀ a b : Fin 4, a = kx bx ∨ a = bar (kx bx) → b = ky by' ∨ b = bar (ky by') →
        reg n i a ≠ reg n i b := by
      intro a b ha hb
      rw [Ne, reg_inj hi hin hi hin]
      rcases kx_cases bx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases ky_cases by' with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [h1, h2, h3, h4] <;> decide
    have x1 := hXY _ _ (.inl rfl) (.inl rfl)
    have x2 := hXY _ _ (.inl rfl) (.inr rfl)
    have x3 := hXY _ _ (.inr rfl) (.inl rfl)
    have x4 := hXY _ _ (.inr rfl) (.inr rfl)
    have cY := hC.le (ky by'); have cX := hC.le (kx bx)
    have cYb := hC.bar_eq (ky by'); have cXb := hC.bar_eq (kx bx)
    simp only [ctr, N_succ]
    rcases hF with ⟨C1, h1, hpos, rfl⟩ | ⟨C1, OF1, C3, h1, h3, rfl⟩ | ⟨C1, OF1, C3, h1, h3, hpos, rfl⟩
    · obtain ⟨-, hC1, -⟩ := ((zA _ C OF hC).1 _ _ _).1 h1
      subst C1
      have hYlt : C (reg n i (ky by')) < N i := by omega
      simp only [mv, hneY, Ne.symm hneY, x1, x2, x3, if_true, if_false, Nat.sub_zero, Nat.add_zero]
      rw [Nat.mod_eq_of_lt (by nlinarith)]
      ring
    · obtain ⟨-, hC1, hb1⟩ := ((zA _ C OF hC).1 _ _ _).1 h1
      subst C1
      have hY0 : C (reg n i (bar (ky by'))) = 0 := by simpa using hb1.symm
      have hw2 : WProper (swp C (reg n i (ky by')) (reg n i (bar (ky by')))) i :=
        ⟨((ps_swp hi hin _).1.proper_iff (by omega) hin).2 hC.1,
          by rw [(ps_swp hi hin _).2]; exact hC.2.1, by rw [(ps_swp hi hin _).2]; exact hC.2.2⟩
      obtain ⟨-, hC3, hb3⟩ := ((zA _ _ OF1 hw2).1 _ _ _).1 h3
      subst C3
      have hX0 : C (reg n i (bar (kx bx))) = 0 := by
        simpa [swp, Equiv.swap_apply_of_ne_of_ne x3 x4] using hb3.symm
      simp only [swp, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne x1 x2,
        Equiv.swap_apply_of_ne_of_ne x3 x4, Equiv.swap_apply_of_ne_of_ne (Ne.symm x1) (Ne.symm x3)]
      rw [hY0, hX0, show C (reg n i (ky by')) = N i by omega, show C (reg n i (kx bx)) = N i by omega,
        show N i * (N i + 1) + N i + 1 = (N i + 1) ^ 2 by ring, Nat.mod_self]
      simp
    · obtain ⟨-, hC1, hb1⟩ := ((zA _ C OF hC).1 _ _ _).1 h1
      subst C1
      have hY0 : C (reg n i (bar (ky by'))) = 0 := by simpa using hb1.symm
      have hw2 : WProper (swp C (reg n i (ky by')) (reg n i (bar (ky by')))) i :=
        ⟨((ps_swp hi hin _).1.proper_iff (by omega) hin).2 hC.1,
          by rw [(ps_swp hi hin _).2]; exact hC.2.1, by rw [(ps_swp hi hin _).2]; exact hC.2.2⟩
      obtain ⟨-, hC3, -⟩ := ((zA _ _ OF1 hw2).1 _ _ _).1 h3
      subst C3
      simp only [swp, Equiv.swap_apply_of_ne_of_ne x3 x4] at hpos
      have hXlt : C (reg n i (kx bx)) < N i := by omega
      simp only [mv, swp, hneX, Ne.symm hneX, x1, Ne.symm x1, Ne.symm x3, if_true, if_false,
        Nat.sub_zero, Nat.add_zero, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne x1 x2]
      rw [show C (reg n i (ky by')) = N i by omega, hY0]
      rw [Nat.mod_eq_of_lt (by nlinarith)]
      ring
  refine ⟨fun C' OF' b => ⟨fun h => ?_, ?_⟩, hR, hT⟩
  · obtain ⟨h1, h2, h3⟩ := hprop C' OF' b h
    exact ⟨h1, h2, h3⟩
  · rintro ⟨rfl, rfl, hw, hoff, hctr⟩
    rcases hT.returns_or_restarts with ⟨C'', OF'', b, hr⟩ | hr
    · obtain ⟨rfl, rfl, hw'', hoff'', hctr''⟩ := hprop _ _ _ hr
      rwa [wproper_ext hi hin bx by' hw hw'' (hoff.symm.trans hoff'') (hctr.trans hctr''.symm)]
    · exact absurd hr hR

end wproper

/-! ### Lemma 11(b): reversibility -/

section rev

variable {R : Type*} [DecidableEq R]

theorem swp_lg_eq_shift {n : ℕ} (C : Reg n → ℕ) {x y : Reg n} (hxy : x ≠ y) (m : ℕ) :
    swp (lg C x y m) x y = shift C x y m := by
  funext z
  simp only [swp, lg, shift, Function.update_apply, Equiv.swap_apply_def]
  split_ifs <;> subst_vars <;> simp_all

theorem rev1 (C : R → ℕ) {c d : R} (hcd : c ≠ d) (h : 0 < C d) : mv (mv C d c) c d = C := by
  funext z
  simp only [mv]
  split_ifs <;> subst_vars <;> simp_all <;> omega

theorem rev2 (C : R → ℕ) {a b c d : R} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) {m : ℕ} (h1 : m ≤ C c) (h2 : m ≤ C a) :
    shift (shift (shift (shift C c d m) a b m) d c m) b a m = C := by
  funext z
  simp only [shift]
  split_ifs <;> subst_vars <;> simp_all <;> omega

theorem rev3 (C : R → ℕ) {a b c d : R} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) {m : ℕ} (h1 : m ≤ C c) (h2 : 0 < C b) :
    mv (shift (mv (shift C c d m) b a) d c m) a b = C := by
  funext z
  simp only [shift, mv]
  split_ifs <;> subst_vars <;> simp_all <;> omega

end rev

section incrB

variable {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (hZB : ZeroB n i) (hZC : ZeroC n i)
include hi hin hZB hZC

/-- **Lemma 11(b)**: `IncrPair(x, y)` is reversible by `IncrPair(x̄, ȳ)` on `Geq` configurations,
and it only changes level `i`. -/
theorem incr_B : IncrB n i := by
  intro bx by' C OF C' OF' b hC h
  obtain ⟨-, -, hret⟩ := incr_geq hi hin hZB hZC bx by' hC
  obtain ⟨hOF, -, hps⟩ := hret C' OF' b h
  refine ⟨?_, hps.1⟩
  subst OF'
  obtain ⟨-, hF⟩ := (incr_returns_iff bx by' hZC).1 h
  have hC' : Geq C' i := hps.geq hi hin hC
  -- register names
  set X := reg n i (kx bx) with hX
  set Xb := reg n i (bar (kx bx)) with hXb
  set Y := reg n i (ky by') with hY
  set Yb := reg n i (bar (ky by')) with hYb
  have hXY : ∀ a b : Fin 4, a = kx bx ∨ a = bar (kx bx) → b = ky by' ∨ b = bar (ky by') →
      reg n i a ≠ reg n i b := by
    intro a b ha hb
    rw [Ne, reg_inj hi hin hi hin]
    rcases kx_cases bx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases ky_cases by' with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [h1, h2, h3, h4] <;> decide
  have x1 : X ≠ Y := hXY _ _ (.inl rfl) (.inl rfl)
  have x2 : X ≠ Yb := hXY _ _ (.inl rfl) (.inr rfl)
  have x3 : Xb ≠ Y := hXY _ _ (.inr rfl) (.inl rfl)
  have x4 : Xb ≠ Yb := hXY _ _ (.inr rfl) (.inr rfl)
  have hXXb : X ≠ Xb := reg_ne_bar hi hin _
  have hYYb : Y ≠ Yb := reg_ne_bar hi hin _
  -- `Zero(z)` (the reverse calls) on `Geq` configurations
  have zr : ∀ k0 D, Geq D i → ∀ D' OF' b, ZR n i k0 D OF D' OF' b ↔ OF' = OF ∧
      ((b = false ∧ D' = D ∧ 0 < D (reg n i k0)) ∨
       (b = true ∧ N i ≤ D (reg n i (bar k0)) ∧ D' = lg D (reg n i (bar k0)) (reg n i k0) (N i))) :=
    fun k0 D hD => (hZB k0 D OF hD.1 (hD.psum _)).1
  rw [incr_returns_iff _ _ hZC]
  refine ⟨rfl, ?_⟩
  simp only [IFin, ky_not, kx_not, bar_bar]
  rcases hF with ⟨C1, h1, hpos, rfl⟩ | ⟨C1, OF1, C3, h1, h3, rfl⟩ | ⟨C1, OF1, C3, h1, h3, hpos, rfl⟩
  · -- first branch: `ȳ ↦ y`
    obtain ⟨-, ⟨-, rfl, -⟩ | ⟨h, -⟩⟩ := (zr_bar hi hin hZB (ky by') hC).1 h1
    swap; · exact absurd h (by simp)
    have hYpos : 0 < mv C1 Yb Y Y := by simp [mv, hYYb]
    refine .inl ⟨_, ((zr _ _ hC' _ _ _).2 ⟨rfl, .inl ⟨rfl, rfl, hYpos⟩⟩), hYpos, ?_⟩
    exact (rev1 C1 hYYb hpos).symm
  · -- second branch: both digits overflow
    obtain ⟨rfl, ⟨h, -⟩ | ⟨-, hm1, rfl⟩⟩ := (zr_bar hi hin hZB (ky by') hC).1 h1
    · exact absurd h (by simp)
    rw [swp_lg_eq_shift _ hYYb] at h3
    have hC2 : Geq (shift C Y Yb (N i)) i :=
      (by rw [← swp_lg_eq_shift _ hYYb]; exact (ps_lg hi hin _ hm1).trans (ps_swp hi hin _) :
        PS C (shift C Y Yb (N i)) i).geq hi hin hC
    obtain ⟨-, ⟨h, -⟩ | ⟨-, hm3, rfl⟩⟩ := (zr_bar hi hin hZB (kx bx) hC2).1 h3
    · exact absurd h (by simp)
    rw [show swp (lg (shift C Y Yb (N i)) X Xb (N i)) X Xb = shift (shift C Y Yb (N i)) X Xb (N i)
      from swp_lg_eq_shift _ hXXb _] at *
    set C' := shift (shift C Y Yb (N i)) X Xb (N i) with hC'def
    have hm1' : N i ≤ C' Yb := by
      rw [hC'def, shift_apply_other _ (Ne.symm x2) (Ne.symm x4), shift_apply_y _ hYYb]; omega
    have hE : Geq (shift C' Yb Y (N i)) i :=
      (by rw [← swp_lg_eq_shift _ (Ne.symm hYYb)]
          exact (ps_lg hi hin (bar (ky by')) (by simpa using hm1')).trans
            (by simpa using ps_swp hi hin (C := lg C' Yb Y (N i)) (bar (ky by'))) :
        PS C' (shift C' Yb Y (N i)) i).geq hi hin hC'
    have hm3' : N i ≤ shift C' Yb Y (N i) Xb := by
      rw [shift_apply_other _ x4 x3, hC'def, shift_apply_y _ hXXb]; omega
    refine .inr (.inl ⟨lg C' Yb Y (N i), OF1, lg (shift C' Yb Y (N i)) Xb X (N i), ?_, ?_, ?_⟩)
    · exact (zr _ _ hC' _ _ _).2 ⟨rfl, .inr ⟨rfl, hm1', rfl⟩⟩
    · rw [swp_lg_eq_shift _ (Ne.symm hYYb)]
      exact (zr _ _ hE _ _ _).2 ⟨rfl, .inr ⟨rfl, hm3', rfl⟩⟩
    · try rw [swp_lg_eq_shift _ (Ne.symm hXXb)]
      try rw [swp_lg_eq_shift _ (Ne.symm hYYb)]
      rw [hC'def]
      have hm3x : N i ≤ C X := by rw [shift_apply_other _ x1 x2] at hm3; exact hm3
      exact (rev2 C hXXb x1 x2 x3 x4 hYYb hm1 hm3x).symm
  · -- third branch: `ȳ` overflows, `x̄ ↦ x`
    obtain ⟨rfl, ⟨h, -⟩ | ⟨-, hm1, rfl⟩⟩ := (zr_bar hi hin hZB (ky by') hC).1 h1
    · exact absurd h (by simp)
    rw [swp_lg_eq_shift _ hYYb] at h3
    have hC2 : Geq (shift C Y Yb (N i)) i :=
      (by rw [← swp_lg_eq_shift _ hYYb]; exact (ps_lg hi hin _ hm1).trans (ps_swp hi hin _) :
        PS C (shift C Y Yb (N i)) i).geq hi hin hC
    obtain ⟨-, ⟨-, rfl, -⟩ | ⟨h, -⟩⟩ := (zr_bar hi hin hZB (kx bx) hC2).1 h3
    swap; · exact absurd h (by simp)
    set C' := mv (shift C Y Yb (N i)) Xb X with hC'def
    have hm1' : N i ≤ C' Yb := by
      rw [hC'def]; simp [mv, Ne.symm x2, Ne.symm x4, shift_apply_y _ hYYb]
    have hE : Geq (shift C' Yb Y (N i)) i :=
      (by rw [← swp_lg_eq_shift _ (Ne.symm hYYb)]
          exact (ps_lg hi hin (bar (ky by')) (by simpa using hm1')).trans
            (by simpa using ps_swp hi hin (C := lg C' Yb Y (N i)) (bar (ky by'))) :
        PS C' (shift C' Yb Y (N i)) i).geq hi hin hC'
    have hXpos : 0 < shift C' Yb Y (N i) X := by
      rw [shift_apply_other _ x2 x1, hC'def]; simp [mv, hXXb]
    refine .inr (.inr ⟨lg C' Yb Y (N i), OF1, shift C' Yb Y (N i), ?_, ?_, hXpos, ?_⟩)
    · exact (zr _ _ hC' _ _ _).2 ⟨rfl, .inr ⟨rfl, hm1', rfl⟩⟩
    · rw [swp_lg_eq_shift _ (Ne.symm hYYb)]
      exact (zr _ _ hE _ _ _).2 ⟨rfl, .inl ⟨rfl, rfl, hXpos⟩⟩
    · have hXbpos : 0 < C Xb := by rwa [shift_apply_other _ x3 x4] at hpos
      exact (rev3 C hXXb x1 x2 x3 x4 hYYb hm1 hXbpos).symm

end incrB

/-! ### Lemma 11(c) for `j < i` -/

/-- **Lemma 11(c)** for `j < i` (the case `j = i` is false, see `lemma_11c_false`). -/
theorem incr_robust_lt {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (hZC : ZeroC n i)
    (hZR : ∀ k, Robust n (.zero i k)) (bx by' : Bool) :
    RobustOn n (fun j => j < i) (.incrPair i bx by') := by
  intro j hj hjn hji C OF hC
  have hlv : ∀ k, (reg n i k).lvl = i := fun k => lvl_reg hi hin k
  have hHmv : ∀ D (a b : Fin 4), High (mv D (reg n i a) (reg n i b)) j ↔ High D j := fun D a b =>
    (off_mv D (hlv a) (hlv b)).high_iff hj hji hin
  have hHswp : ∀ D (a b : Fin 4), High (swp D (reg n i a) (reg n i b)) j ↔ High D j := fun D a b =>
    (off_swp D (hlv a) (hlv b)).high_iff hj hji hin
  refine ⟨incr_terminates bx by' hZC ((hZR _ j hj hjn trivial C OF hC).1) (fun C1 OF1 h1 => ?_),
    fun C' OF' b h => ?_⟩
  · obtain ⟨rfl, hC1⟩ := (hZR _ j hj hjn trivial C OF hC).2 _ _ _ h1
    exact (hZR _ j hj hjn trivial _ _ ((hHswp _ _ _).2 hC1)).1
  · obtain ⟨-, hF⟩ := (incr_returns_iff bx by' hZC).1 h
    rcases hF with ⟨C1, h1, -, rfl⟩ | ⟨C1, OF1, C3, h1, h3, rfl⟩ | ⟨C1, OF1, C3, h1, h3, -, rfl⟩
    · obtain ⟨rfl, hC1⟩ := (hZR _ j hj hjn trivial C OF hC).2 _ _ _ h1
      exact ⟨rfl, (hHmv _ _ _).2 hC1⟩
    · obtain ⟨rfl, hC1⟩ := (hZR _ j hj hjn trivial C OF hC).2 _ _ _ h1
      obtain ⟨rfl, hC3⟩ := (hZR _ j hj hjn trivial _ _ ((hHswp _ _ _).2 hC1)).2 _ _ _ h3
      exact ⟨rfl, (hHswp _ _ _).2 hC3⟩
    · obtain ⟨rfl, hC1⟩ := (hZR _ j hj hjn trivial C OF hC).2 _ _ _ h1
      obtain ⟨rfl, hC3⟩ := (hZR _ j hj hjn trivial _ _ ((hHswp _ _ _).2 hC1)).2 _ _ _ h3
      exact ⟨rfl, (hHmv _ _ _).2 hC3⟩

end Podc.PPDoubleExpThresholds
