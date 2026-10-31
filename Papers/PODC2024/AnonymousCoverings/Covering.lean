import Papers.PODC2024.AnonymousCoverings.Scan

/-!
# The covering count (Lemma 4.5 of the paper)

Lemma 4.5 of the paper bounds by `|A|` the number of registers last written by the complement `Ā`
of a set `A` that reads only from itself. We prove the slightly stronger bound for the registers
**not** last written by `A` (this also counts registers never written); the printed form is
`Exec.lemma_4_5` in `Lemmas.lean`:

> If, from time `t₂` on, every read by a member of `A` returns a value last written by a member of
> `A`, and some member of `A` is live, then at time `t₂` at most `|A|` registers are not last
> written by a member of `A`.

Proof (the paper's): take the first scan of a member of `A` that starts at or after `t₂` and
completes. Until it completes, each member of `A` writes at most once (a second write would come
after an earlier completed scan). The scanner reads every register, and every register not last
written by `A` at `t₂` must have been rewritten by `A` before it is read; distinct registers need
distinct writers.
-/

namespace Podc.AnonymousCoverings

open Finset

variable {P R D X : Type*} [DecidableEq P] [DecidableEq R] [Fintype R]

namespace Exec

variable {A : Algo R D X} (e : Exec (P := P) A)

/-- The registers that, at time `t`, are not last written by a member of `S`. -/
def notWrittenBy (S : Finset P) (t : ℕ) : Finset R :=
  univ.filter fun r => ∀ b ∈ S, (e.reg t r).writer ≠ some b

/-- The registers that, at time `t`, are last written by a member of `S`. -/
def writtenBy (S : Finset P) (t : ℕ) : Finset R :=
  univ.filter fun r => ∃ b ∈ S, (e.reg t r).writer = some b

theorem card_writtenBy_add (S : Finset P) (t : ℕ) :
    (e.writtenBy S t).card + (e.notWrittenBy S t).card = Fintype.card R := by
  classical
  unfold writtenBy notWrittenBy
  rw [← card_univ, ← card_filter_add_card_filter_not (s := univ)
    (p := fun r => ∃ b ∈ S, (e.reg t r).writer = some b)]
  congr 2
  ext r; simp

/-- **Lemma 4.5** (strengthened form). If from time `t₂` on every member of `A` reads only registers
last written by members of `A`, and some member of `A` is live, then at time `t₂` at most `|A|`
registers are not last written by `A`. -/
theorem card_notWrittenBy_le (S : Finset P) (t₂ : ℕ) (h0 : ∀ r, (e.reg 0 r).writer = none)
    (hS : ∀ t ≥ t₂, ∀ a ∈ S, ∀ r, e.act t = .read a r → ∃ b ∈ S, (e.reg t r).writer = some b)
    (hlive : ∃ a ∈ S, e.Live a) : (e.notWrittenBy S t₂).card ≤ S.card := by
  classical
  -- the first completion of a scan of a member of `S` started at or after `t₂`
  let Good : ℕ → Prop := fun c =>
    ∃ a ∈ S, e.Completes c a ∧ ∃ s, t₂ ≤ s ∧ s < c ∧ e.WritesAt s a
  have hex : ∃ c, Good c := by
    obtain ⟨a, ha, hl⟩ := hlive
    obtain ⟨w, hw, r, hr⟩ := e.exists_write_of_live hl t₂
    obtain ⟨c, hc, hcc, -⟩ := e.exists_completes_after_write hl hr
    exact ⟨c, a, ha, hcc, w, hw, hc, r, hr⟩
  obtain ⟨a, ha, hcomp, s, hs1, hs2, r₀, hr₀⟩ := Nat.find_spec hex
  set c := Nat.find hex with hcdef
  have hmin : ∀ c', c' < c → ¬ Good c' := fun c' h => Nat.find_min hex h
  -- each member of `S` writes at most once in `[t₂, c)`
  have once : ∀ b ∈ S, ∀ w₁ w₂, t₂ ≤ w₁ → w₁ < c → t₂ ≤ w₂ → w₂ < c →
      e.WritesAt w₁ b → e.WritesAt w₂ b → w₁ = w₂ := by
    intro b hb w₁ w₂ h1 h2 h3 h4 hw1 hw2
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨c', hc1, hc2, hc3⟩ := e.exists_completes_between hlt hw1 hw2
      exact hmin c' (by omega) ⟨b, hb, hc3, w₁, h1, hc1, hw1⟩
    · obtain ⟨c', hc1, hc2, hc3⟩ := e.exists_completes_between hlt hw2 hw1
      exact hmin c' (by omega) ⟨b, hb, hc3, w₂, h3, hc1, hw2⟩
  -- the scan of `a` started at `s` does not complete before `c`
  have hnc : ∀ t, s < t → t ≤ c → (e.loc t a).scan ≠ none := by
    intro t ht1 ht2 hnone
    have hs0 := e.scan_after_write hr₀
    rcases Nat.eq_or_lt_of_le (show s + 1 ≤ t by omega) with heq | hlt
    · rw [← heq, hs0] at hnone; exact absurd hnone (by simp)
    · obtain ⟨r, hr1, hr2, hr3, hr4, -⟩ :=
        Nat.exists_first_Ioc (Q := fun t => (e.loc t a).scan = none) (s := s + 1) (B := t)
          (by rw [hs0]; simp) ⟨t, hlt, le_rfl, hnone⟩
      exact hmin r (by omega) ⟨a, ha, e.completes_of_scan_none hr3 hr4, s, hs1, by omega,
        r₀, hr₀⟩
  have cover := e.read_all_of_scan hr₀ hcomp hs2 hnc
  -- every register not written by `S` at `t₂` is rewritten by some member of `S` in `[t₂, c)`
  have key : ∀ r ∈ e.notWrittenBy S t₂, ∃ b ∈ S, ∃ w, t₂ ≤ w ∧ w < c ∧ e.act w = .write b r := by
    intro r hr
    simp only [notWrittenBy, mem_filter, mem_univ, true_and] at hr
    obtain ⟨tr, htr1, htr2, htr3⟩ := cover r
    obtain ⟨b, hb, hwb⟩ := hS tr (by omega) a ha r htr3
    obtain ⟨w, hw1, hw2, hw3, hw4⟩ := e.exists_last_write hwb (h0 r)
    refine ⟨b, hb, w, ?_, by omega, hw2⟩
    by_contra hlt
    push Not at hlt
    have : e.reg t₂ r = e.reg (w + 1) r :=
      e.reg_eq_of_no_write (by omega) fun w' h1 h2 p => hw4 w' (by omega) (by omega) p
    exact hr b hb (by rw [this, hw3, hwb])
  refine card_le_card_of_forall_subsingleton
    (fun r b => ∃ w, t₂ ≤ w ∧ w < c ∧ e.act w = .write b r) (fun r hr => key r hr) ?_
  rintro b hb r₁ ⟨-, w₁, h1, h2, h3⟩ r₂ ⟨-, w₂, h4, h5, h6⟩
  have := once b hb w₁ w₂ h1 h2 h4 h5 ⟨r₁, h3⟩ ⟨r₂, h6⟩
  subst this
  rw [h3] at h6
  cases h6
  rfl

/-- From time `T` on, members of `S` read only registers last written by members of `S`. -/
def ReadsOnlyFrom (S : Finset P) (T : ℕ) : Prop :=
  ∀ t ≥ T, ∀ a ∈ S, ∀ r, e.act t = .read a r → ∃ b ∈ S, (e.reg t r).writer = some b

theorem writtenBy_subset_notWrittenBy {S₁ S₂ : Finset P} (hd : Disjoint S₁ S₂) (t : ℕ) :
    e.writtenBy S₁ t ⊆ e.notWrittenBy S₂ t := by
  intro r hr
  simp only [writtenBy, notWrittenBy, mem_filter, mem_univ, true_and] at hr ⊢
  obtain ⟨b, hb, hw⟩ := hr
  intro b' hb' hw'
  rw [hw] at hw'; cases hw'
  exact disjoint_left.1 hd hb hb'

/-- If, from time `T` on, exactly `|S|` registers are not last written by `S` and some member of
`S` is live, we get a contradiction: the first write of a live member of `S` into such a register
decreases the count. -/
theorem false_of_card_notWrittenBy_eq (S : Finset P) (T : ℕ)
    (heq : ∀ t ≥ T, (e.notWrittenBy S t).card = S.card) {a : P} (ha : a ∈ S) (hla : e.Live a) :
    False := by
  classical
  have hpos : 0 < (e.notWrittenBy S T).card := by
    rw [heq T le_rfl]; exact card_pos.2 ⟨a, ha⟩
  obtain ⟨r, hr⟩ := card_pos.1 hpos
  have hex : ∃ w, T ≤ w ∧ ∃ b ∈ S, e.act w = .write b r := by
    obtain ⟨w, hw, hw'⟩ := e.exists_write_reg_of_live hla r T
    exact ⟨w, hw, a, ha, hw'⟩
  obtain ⟨hw0T, b, hb, hwb⟩ := Nat.find_spec hex
  set w0 := Nat.find hex
  have hin : ∀ t, T ≤ t → t ≤ w0 → r ∈ e.notWrittenBy S t := by
    intro t ht htw
    induction t, ht using Nat.le_induction with
    | base => exact hr
    | succ t ht ih =>
      have ih := ih (by omega)
      by_cases hw : ∃ p, e.act t = .write p r
      · obtain ⟨p, hp⟩ := hw
        have hpS : p ∉ S := fun hpS => Nat.find_min hex (show t < w0 by omega) ⟨ht, p, hpS, hp⟩
        simp only [notWrittenBy, mem_filter, mem_univ, true_and]
        intro b' hb' hw'
        rw [e.writer_succ_of_write hp] at hw'; cases hw'
        exact hpS hb'
      · push Not at hw
        simp only [notWrittenBy, mem_filter, mem_univ, true_and] at ih ⊢
        rw [e.reg_succ_of_not_write hw]; exact ih
  have hsub : e.notWrittenBy S (w0 + 1) ⊆ (e.notWrittenBy S w0).erase r := by
    intro r' hr'
    have hne : r' ≠ r := by
      rintro rfl
      simp only [notWrittenBy, mem_filter, mem_univ, true_and] at hr'
      exact hr' b hb (e.writer_succ_of_write hwb)
    refine mem_erase.2 ⟨hne, ?_⟩
    have : e.reg (w0 + 1) r' = e.reg w0 r' :=
      e.reg_succ_of_not_write fun p hp => by rw [hwb] at hp; cases hp; exact hne rfl
    simp only [notWrittenBy, mem_filter, mem_univ, true_and] at hr' ⊢
    rw [← this]; exact hr'
  have c1 := card_le_card hsub
  rw [card_erase_of_mem (hin w0 hw0T le_rfl), heq w0 hw0T, heq (w0 + 1) (by omega)] at c1
  have : 0 < S.card := card_pos.2 ⟨a, ha⟩
  omega

/-- **Two disjoint live groups cannot both read only from themselves forever** (the content of
Lemmas 4.5–4.7 of the paper, used in the proof of Theorem 4.8). Needs at least `|S₁| + |S₂|`
registers and fair (round-robin) writes. -/
theorem false_of_two_closed (S₁ S₂ : Finset P) (hd : Disjoint S₁ S₂)
    (hcard : S₁.card + S₂.card ≤ Fintype.card R) (h0 : ∀ r, (e.reg 0 r).writer = none) (T : ℕ)
    (h₁ : e.ReadsOnlyFrom S₁ T) (h₂ : e.ReadsOnlyFrom S₂ T)
    (hl₁ : ∃ a ∈ S₁, e.Live a) (hl₂ : ∃ a ∈ S₂, e.Live a) : False := by
  classical
  have heq : ∀ t ≥ T, (e.notWrittenBy S₁ t).card = S₁.card := by
    intro t ht
    have a1 := e.card_notWrittenBy_le S₁ t h0 (fun t' ht' => h₁ t' (by omega)) hl₁
    have a2 := e.card_notWrittenBy_le S₂ t h0 (fun t' ht' => h₂ t' (by omega)) hl₂
    have a3 := card_le_card (e.writtenBy_subset_notWrittenBy hd t)
    have a4 := e.card_writtenBy_add S₁ t
    omega
  obtain ⟨a, ha, hla⟩ := hl₁
  exact e.false_of_card_notWrittenBy_eq S₁ T heq ha hla

end Exec

end Podc.AnonymousCoverings
