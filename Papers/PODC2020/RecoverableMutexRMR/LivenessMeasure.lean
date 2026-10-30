import Papers.PODC2020.RecoverableMutexRMR.LivenessStep

/-!
# Liveness, part 2: a lexicographic progress measure for one process

For a process `q` we define the measure `(sNum, Kb, rnk)` (compared lexicographically):

* `sNum = 1` iff the current ticket of `q` is skipped (`A[cur q] = −1`);
* `Kb = Kc + bfl`, where `Kc` counts the tickets `x ∈ (Token, C]` that are skipped, or claimed
  by `q` while `W[q]` does not hold `x`, and `bfl (pc q) = 1` before line 10 of `Exit()` or in
  `Recover()`;
* `rnk` is a rank of the program counter that decreases along every forward edge.

As long as no new ticket is skipped, `q` does not crash and does not enter or leave the
remainder section and does not enter the critical section from line 31, every step does not
increase the measure, and every step of `q` that changes its program counter strictly decreases
it (`measure_step`).
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

namespace Live

/-- `1` iff the current ticket of `q` is skipped. -/
def sNum (s : Cfg P) (g : Ghost P) (q : P) : ℕ := if s.A (g.cur q) = .skipped then 1 else 0

/-- Tickets counted by `Kc`. -/
def cnt (s : Cfg P) (q : P) (x : ℕ) : Prop :=
  s.A x = .skipped ∨ (s.A x = .claimed q ∧ (s.W q).1 ≠ x)

instance (s : Cfg P) (q : P) : DecidablePred (cnt s q) := fun x => by
  unfold cnt; infer_instance

/-- Skipped tickets and tickets claimed by `q` but not held in `W[q]`, beyond `Token`. -/
def Kc (s : Cfg P) (q : P) : ℕ := ((Finset.Ioc s.T s.C).filter (cnt s q)).card

/-- `1` in `Recover()` and between the critical section and line 10. -/
def bfl : PC P → ℕ
  | .r15 | .r16 | .r18 | .cs | .x9 | .x10 => 1
  | _ => 0

/-- Second component of the measure. -/
def Kb (s : Cfg P) (q : P) : ℕ := Kc s q + bfl (s.pc q)

/-- Rank of a program counter, given whether the current ticket is skipped (`S`) and whether
`W[q]` holds no ticket (`Z`). -/
def rkS (S Z : Bool) : PC P → ℕ
  | .l3 => if S then (if Z then 23 else 29) else 26
  | .l4 => if S then 22 else 25
  | .l5 _ => if S then 28 else 24
  | .w23 => if S then 27 else 23
  | .w24 _ => if S then 26 else 22
  | .w25 _ => if S then 25 else 21
  | .w26 => if S then 24 else 20
  | k => rk0 k

/-- Third component of the measure. -/
def rnk (s : Cfg P) (g : Ghost P) (q : P) : ℕ :=
  rkS (decide (s.A (g.cur q) = .skipped)) (decide ((s.W q).1 = 0)) (s.pc q)

/-! ### Pure lemmas on the control-flow graph -/

lemma bfl_succ {k k' : PC P} (h : Succ k k') (hcs : k' = .cs → ∀ w, k ≠ .w31 w) :
    bfl k' + (if k = .x10 then 1 else 0) ≤ bfl k := by
  cases h <;> (try cases ‹Ret›) <;> simp_all [bfl, Ret.pc]

lemma rkS_succ {S Z Z' : Bool} {k k' : PC P} (h : Succ k k') (hne : k ≠ k') (hb : ¬ Back k k')
    (hcs : k' = .cs → ∀ w, k ≠ .w31 w) (hrem : k ≠ .rem) (hrem' : k' ≠ .rem)
    (f1 : k = .l3 → S = true → Z = true → k' = .l4) (f2 : k = .l4 → S = false)
    (f3 : ∀ w, k = .w25 w → k' = .w28 w → S = false) (f4 : k' = .w26 → S = true)
    (f5 : k = .w26 → S = true ∧ Z' = true) : rkS S Z' k' < rkS S Z k := by
  cases h <;> (try cases ‹Ret›) <;> cases S <;> cases Z <;> cases Z' <;>
    simp_all [rkS, rk0, Ret.pc, Back, IsM34]

/-! ### Counting lemmas -/

lemma Kc_le_of {s s' : Cfg P} {q : P} (hT : s.T ≤ s'.T)
    (h : ∀ x, s'.T < x → x ≤ s'.C → cnt s' q x → x ≤ s.C ∧ cnt s q x) : Kc s' q ≤ Kc s q := by
  unfold Kc
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hx ⊢
  have := h x hx.1.1 hx.1.2 hx.2
  exact ⟨⟨by omega, this.1⟩, this.2⟩

lemma Kc_le_succ_of {s s' : Cfg P} {q : P} {y : ℕ} (hT : s.T ≤ s'.T)
    (h : ∀ x, s'.T < x → x ≤ s'.C → cnt s' q x → (x ≤ s.C ∧ cnt s q x) ∨ x = y) :
    Kc s' q ≤ Kc s q + 1 := by
  unfold Kc
  calc ((Finset.Ioc s'.T s'.C).filter (cnt s' q)).card
      ≤ (insert y ((Finset.Ioc s.T s.C).filter (cnt s q))).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_insert] at hx ⊢
        rcases h x hx.1.1 hx.1.2 hx.2 with h' | h'
        · exact Or.inr ⟨⟨by omega, h'.1⟩, h'.2⟩
        · exact Or.inl h'
    _ ≤ _ := Finset.card_insert_le _ _

lemma Kc_lt_of {s s' : Cfg P} {q : P} (hT : s'.T = s.T + 1)
    (h : ∀ x, s'.T < x → x ≤ s'.C → cnt s' q x → x ≤ s.C ∧ cnt s q x)
    (hy : s.T + 1 ≤ s.C) (hc : cnt s q (s.T + 1)) : Kc s' q < Kc s q := by
  unfold Kc
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx ⊢
    have := h x hx.1.1 hx.1.2 hx.2
    exact ⟨⟨by omega, this.1⟩, this.2⟩
  · intro hsub
    have := hsub (show s.T + 1 ∈ (Finset.Ioc s.T s.C).filter (cnt s q) by
      simp only [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨by omega, hy⟩, hc⟩)
    simp only [Finset.mem_filter, Finset.mem_Ioc] at this
    omega

/-! ### Step lemmas -/

section Step

variable {s : Cfg P} {g : Ghost P} {r q : P}

lemma A_step_of_skipped
    (hsk : ∀ x, (s.step r).A x = .skipped → s.A x = .skipped) (x : ℕ) :
    (s.step r).A x = s.A x ∨ (s.A x = .empty ∧ s.pc r = .w24 x ∧ (s.step r).A x = .claimed r) := by
  rcases step_A s r x with h | ⟨h0, ⟨h1, h2⟩ | ⟨_, h2⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨h0, h1, h2⟩
  · have := hsk x h2; simp_all

lemma W_fst_step (hI : Inv s g) (hne : ¬ (r = q ∧ s.pc q = .x10)) :
    (s.step r).W q = s.W q ∨ (r = q ∧ (∃ c, s.pc q = .l5 c) ∧ s.W q = (0, false)) ∨
      (r = q ∧ s.pc q = .w26 ∧ (s.W q).1 = g.cur q ∧ s.A (g.cur q) = .skipped) ∨
      ((s.step r).W q).1 = (s.W q).1 := by
  rcases step_W s r q with h | ⟨rfl, ⟨c, hc⟩ | hc | hc⟩ | ⟨ρ, ℓ, _, h1, h2⟩
  · exact Or.inl h
  · have := hI.loc r; rw [LI, hc] at this
    exact Or.inr (Or.inl ⟨rfl, ⟨c, hc⟩, this.2.1⟩)
  · have := hI.loc r; rw [LI, hc] at this
    exact Or.inr (Or.inr (Or.inl ⟨rfl, hc, this.2.1, this.2.2.2⟩))
  · exact absurd ⟨rfl, hc⟩ hne
  · exact Or.inr (Or.inr (Or.inr (by rw [h1, h2])))

lemma cnt_incl (hI : Inv s g) (hsk : ∀ x, (s.step r).A x = .skipped → s.A x = .skipped)
    (x : ℕ) (hx : (s.step r).T < x) (hc : cnt (s.step r) q x) :
    (x ≤ s.C ∧ cnt s q x) ∨ (r = q ∧ s.pc q = .x10 ∧ x = (s.W q).1) := by
  have hne : (s.step r).A x ≠ .empty := by
    rcases hc with h | ⟨h, _⟩ <;> simp [h]
  by_cases h10 : r = q ∧ s.pc q = .x10
  · -- `x10` changes only `W` and `pc`
    obtain ⟨rfl, h10⟩ := h10
    have hA : (s.step r).A = s.A := by simp [Cfg.step, h10]
    have hW : (s.step r).W r = (0, false) := by simp [Cfg.step, h10]
    rw [hA] at hne
    by_cases hx' : x = (s.W r).1
    · exact Or.inr ⟨rfl, h10, hx'⟩
    · left
      refine ⟨(hI.A_ne x hne).2, ?_⟩
      unfold cnt at hc ⊢; rw [hA] at hc
      rcases hc with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.1, fun h' => hx' h'.symm⟩
  · left
    rcases A_step_of_skipped hsk x with hA | ⟨h0, h24, hA⟩
    · rw [hA] at hne
      refine ⟨(hI.A_ne x hne).2, ?_⟩
      unfold cnt at hc ⊢; rw [hA] at hc
      rcases hc with h | ⟨h1, h2⟩
      · exact Or.inl h
      · right; refine ⟨h1, ?_⟩
        have hT : s.T ≤ (s.step r).T := by rcases step_T s r with h | h <;> omega
        rcases W_fst_step (g := g) hI h10 with hW | ⟨_, _, hW⟩ | ⟨_, _, hW, hsk'⟩ | hW
        · rwa [hW] at h2
        · rw [hW]; simp only; omega
        · intro h'; rw [hW] at h'; subst h'; simp_all
        · rwa [hW] at h2
    · exfalso
      unfold cnt at hc; rw [hA] at hc
      rcases hc with h | ⟨h1, h2⟩
      · simp at h
      · simp only [Slot.claimed.injEq] at h1; subst h1
        apply h2
        have := hI.loc r; rw [LI, h24] at this
        have hW : (s.step r).W r = s.W r := by simp [Cfg.step, h24]
        rw [hW]; exact this.2.1

lemma T_le_step (s : Cfg P) (r : P) : s.T ≤ (s.step r).T := by
  rcases step_T s r with h | h <;> omega

lemma C_le_step (s : Cfg P) (r : P) : s.C ≤ (s.step r).C := by
  rcases step_C s r with h | h <;> omega

lemma Kc_step (hI : Inv s g) (hsk : ∀ x, (s.step r).A x = .skipped → s.A x = .skipped) :
    Kc (s.step r) q + (if r = q ∧ s.pc q = .x10 then 0 else 1) ≤ Kc s q + 1 := by
  split_ifs with h10
  · have := Kc_le_succ_of (s := s) (s' := s.step r) (q := q) (y := (s.W q).1) (T_le_step s r)
      (fun x hx _ hc => by
        rcases cnt_incl hI hsk x hx hc with h | h
        · exact Or.inl h
        · exact Or.inr h.2.2)
    omega
  · have := Kc_le_of (s := s) (s' := s.step r) (q := q) (T_le_step s r)
      (fun x hx _ hc => by
        rcases cnt_incl hI hsk x hx hc with h | h
        · exact h
        · exact absurd ⟨h.1, h.2.1⟩ h10)
    omega

/-- (a) The flag `sNum` does not increase. -/
lemma sNum_step (hI : Inv s g) (hsk : ∀ x, (s.step r).A x = .skipped → s.A x = .skipped) :
    sNum (s.step r) (g.next s (.step r)) q ≤ sNum s g q := by
  unfold sNum
  rcases ghost_cur_step g s r q with h | ⟨rfl, h4, h⟩
  · rw [h]; split_ifs with h1 h2 <;> simp_all
  · rw [h]
    have hA : (s.step r).A = s.A := by simp [Cfg.step, h4]
    have h0 : s.A (s.C + 1) = .empty := by
      by_contra hne; have := (hI.A_ne _ hne).2; omega
    rw [hA, h0]; simp

/-- (b) The second component does not increase. -/
lemma Kb_step (hI : Inv s g) (hsk : ∀ x, (s.step r).A x = .skipped → s.A x = .skipped)
    (hcs : (s.step r).pc q = .cs → ∀ w, s.pc q ≠ .w31 w) : Kb (s.step r) q ≤ Kb s q := by
  unfold Kb
  have hK := Kc_step (q := q) hI hsk
  by_cases hrq : r = q
  · subst hrq
    have hb := bfl_succ (succ_step s r) hcs
    split_ifs at hK hb with h <;> simp_all <;> omega
  · rw [step_pc_ne s (Ne.symm hrq)]
    have : ¬ (r = q ∧ s.pc q = .x10) := fun h => hrq h.1
    simp only [this, ite_false] at hK
    omega

/-- At a back edge of `q`, the second component strictly decreases. -/
lemma Kb_back (hI : Inv s g) (hsk : ∀ x, (s.step q).A x = .skipped → s.A x = .skipped)
    (hb : Back (s.pc q) ((s.step q).pc q)) : Kb (s.step q) q < Kb s q := by
  have hT := step_T_of_back s q hb
  obtain ⟨⟨ρ', hρ'⟩, ρ, ℓ, hk⟩ := hb
  have hbfl : bfl ((s.step q).pc q) = bfl (s.pc q) := by
    rcases hk with hk | hk <;> rw [hρ', hk] <;> rfl
  have hne : ¬ (q = q ∧ s.pc q = .x10) := by rcases hk with hk | hk <;> simp [hk]
  have hℓ : s.T = ℓ := by
    rcases hk with hk | hk <;> by_contra hc <;> simp [Cfg.step, hk, hc, Cfg.setPc] at hT
  have hc : s.T + 1 ≤ s.C ∧ cnt s q (s.T + 1) := by
    have hl := hI.loc q
    rcases hk with hk | hk <;> rw [LI, hk] at hl <;> subst hℓ
    · have h1 := hl.2.2.1
      exact ⟨(hI.A_ne _ (by simp [h1])).2, Or.inr ⟨h1, hl.2.2.2⟩⟩
    · have h1 := hl.2.2
      exact ⟨(hI.A_ne _ (by simp [h1])).2, Or.inl h1⟩
  have := Kc_lt_of (s := s) (s' := s.step q) (q := q) hT
    (fun x hx _ hc => by
      rcases cnt_incl hI hsk x hx hc with h | h
      · exact h
      · exact absurd ⟨h.1, h.2.1⟩ hne) hc.1 hc.2
  unfold Kb; omega

lemma sNum_l4 (hI : Inv s g) (h4 : s.pc q = .l4) : sNum (s.step q) (g.next s (.step q)) q = 0 := by
  unfold sNum
  rcases ghost_cur_step g s q q with h | ⟨_, _, h⟩
  · simp [Ghost.next, h4] at h
    exfalso
    have := hI.cur_le q
    have : g.cur q = s.C + 1 := by
      have h' := congrFun (show (Function.update g.cur q (s.C + 1)) = _ from rfl) q
      simp at h'
      omega
    omega
  · rw [h]
    have hA : (s.step q).A = s.A := by simp [Cfg.step, h4]
    have h0 : s.A (s.C + 1) = .empty := by
      by_contra hne; have := (hI.A_ne _ hne).2; omega
    rw [hA, h0]; simp

lemma W_fst_step_ne (hrq : r ≠ q) : ((s.step r).W q).1 = (s.W q).1 := by
  rcases step_W s r q with h | ⟨h, _⟩ | ⟨ρ, ℓ, _, h1, h2⟩
  · rw [h]
  · exact absurd h hrq
  · rw [h1, h2]

/-- (c) The rank does not increase once the first two components are fixed, and it strictly
decreases at every step of `q` that changes its program counter. -/
lemma rnk_step (hI : Inv s g) (hI' : Inv (s.step r) (g.next s (.step r)))
    (hsk : ∀ x, (s.step r).A x = .skipped → s.A x = .skipped)
    (hcs : (s.step r).pc q = .cs → ∀ w, s.pc q ≠ .w31 w)
    (hrem : s.pc q ≠ .rem) (hrem' : (s.step r).pc q ≠ .rem)
    (hS : sNum (s.step r) (g.next s (.step r)) q = sNum s g q)
    (hK : Kb (s.step r) q = Kb s q) :
    rnk (s.step r) (g.next s (.step r)) q ≤ rnk s g q ∧
      (r = q → (s.step r).pc q ≠ s.pc q → rnk (s.step r) (g.next s (.step r)) q < rnk s g q) := by
  have hSS : decide ((s.step r).A ((g.next s (.step r)).cur q) = .skipped) =
      decide (s.A (g.cur q) = .skipped) := by
    unfold sNum at hS; split_ifs at hS with h1 h2 h2 <;> simp_all
  by_cases hrq : r = q
  · subst hrq
    by_cases hpc : (s.step r).pc r = s.pc r
    · obtain ⟨w, hw, -⟩ := spin s r hpc
      refine ⟨?_, fun _ h => absurd hpc h⟩
      unfold rnk; rw [hpc, hw]; simp [rkS, rk0]
    · have hb : ¬ Back (s.pc r) ((s.step r).pc r) := fun hb => by
        have := Kb_back hI hsk hb; omega
      have key := rkS_succ (S := decide (s.A (g.cur r) = .skipped))
        (Z := decide ((s.W r).1 = 0)) (Z' := decide (((s.step r).W r).1 = 0))
        (succ_step s r) (Ne.symm hpc) hb hcs hrem hrem'
        (fun h3 _ hZ => by
          have hZ' : (s.W r).1 = 0 := by simpa using hZ
          have hW : s.W r = (0, false) := by
            rcases hb2 : (s.W r).2 with _ | _
            · exact Prod.ext hZ' hb2
            · have := (hI.grant r hb2).1; omega
          simp [Cfg.step, h3, hW, Cfg.setPc])
        (fun h4 => by
          have := sNum_l4 hI h4
          unfold sNum at this hS; split_ifs at hS this with h1 h2; simp_all)
        (fun w h25 h28 => by
          have hl := hI.loc r; rw [LI, h25] at hl
          have hcur := hI.W_cur r (by rw [hl.2.1]; exact hl.2.2.1)
          rw [hl.2.1] at hcur
          have hA : s.A w = .claimed r := by
            by_contra hA; simp [Cfg.step, h25, hA, Cfg.setPc] at h28
          rw [← hcur, hA]; simp)
        (fun h26 => by
          have hl := hI'.loc r; rw [LI, h26] at hl
          rw [← hSS]; simpa using hl.2.2.2)
        (fun h26 => by
          have hl := hI.loc r; rw [LI, h26] at hl
          refine ⟨by simpa using hl.2.2.2, ?_⟩
          simp [Cfg.step, h26])
      unfold rnk; rw [hSS]
      exact ⟨key.le, fun _ _ => key⟩
  · unfold rnk
    rw [hSS, step_pc_ne s (Ne.symm hrq), W_fst_step_ne hrq]
    exact ⟨le_rfl, fun h => absurd h hrq⟩

end Step

end Live

end Podc.RecoverableMutexRMR
