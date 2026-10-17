import Papers.PODC2025.StrangerFreeTasks.Alg1WaitFreeK1Inv

/-!
# Algorithm 1 for `k = 1`: doomed configurations and progress measures

Fix a process `p`. A register value is *non-`p`* (`NonP`) if its seen set is not contained in
`{p}`; values written by other processes are always non-`p`.

* `Doomed p C`: `p` has not decided and will necessarily decide (output) within a bounded number
  of its own steps: either its seen set already contains another process, or it is about to read
  a non-`p` value in its current first collect, or the register it does *not* write next holds
  a non-`p` value. `doomed_step`: doomed configurations stay doomed (until `p` decides), and the
  potential `pot` decreases with every step of `p`.
* `prog p C`: a progress measure of `p` that increases by one with each step of `p`
  (`prog_step`).
-/

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {P : Type} [DecidableEq P]

/-- A value whose seen set is not contained in `{p}`. -/
def NonP (p : P) (v : Triple P) : Prop := ¬ v.seen ⊆ {p}

lemma nonP_write {p x : P} (hx : x ≠ p) {n : ℕ} {s : Finset P} (hs : x ∈ s) :
    NonP p ⟨some x, n, s⟩ := by
  intro h; exact hx (Finset.mem_singleton.1 (h hs))

lemma two_le_card {p : P} {s : Finset P} (hp : p ∈ s) (h : ¬ s ⊆ {p}) : 2 ≤ s.card := by
  obtain ⟨q, hq, hq'⟩ := Finset.not_subset.1 h
  exact Finset.one_lt_card.2 ⟨p, hp, q, hq, fun e => hq' (by simp [e])⟩

/-- A step of a process other than `p` keeps non-`p` registers non-`p`. -/
lemma nonP_step_other {α : List (Label P (laObj P))} {C C' : Cfg P 1} {ℓ : Label P (laObj P)}
    {p : P} (hB : BInv α C) (h : (alg1 1).step C ℓ = some C') (hℓ : ℓ.proc ≠ p)
    {r : Fin (1 + 1)} (hr : NonP p (C.mem r)) : NonP p (C'.mem r) := by
  rcases step_mem h with hm | ⟨y, rfl, -, hm⟩
  · rwa [hm]
  · rw [hm, Function.update_apply]; split_ifs
    · exact nonP_write hℓ (hB.self y)
    · exact hr

/-! ### Doomed configurations -/

/-- `p` will decide within a bounded number of its own steps. -/
def Doomed (p : P) (C : Cfg P 1) : Prop :=
  (C.loc p).phase ≠ .done ∧
    (¬ (C.loc p).seen ⊆ {p} ∨
      ((C.loc p).phase = .col1 ∧ ∃ r, (C.loc p).j ≤ r ∧ NonP p (C.mem r)) ∨
      ((C.loc p).phase ≠ .col1 ∧ NonP p (C.mem ((C.loc p).i + 1))))

/-- Number of own steps of `p` until its next decision. -/
def dist (l : Loc P 1) : ℕ :=
  match l.phase with
  | .idle => 5
  | .wr => 5
  | .col1 => 4 - l.j.val
  | .col2 => 2 - l.j.val
  | .done => 0

open Classical in
/-- Potential of a doomed configuration: an upper bound on the number of steps of `p` before it
decides. -/
noncomputable def pot (p : P) (C : Cfg P 1) : ℕ :=
  dist (C.loc p) + (if (C.loc p).phase = .col2 ∧ (C.loc p).seen ⊆ {p} then 5 else 0)

lemma Doomed.congr {p : P} {C C' : Cfg P 1} (hD : Doomed p C) (hl : C'.loc p = C.loc p)
    (hm : ∀ r, NonP p (C.mem r) → NonP p (C'.mem r)) : Doomed p C' := by
  obtain ⟨h1, h2 | ⟨h2, r, hr, h3⟩ | ⟨h2, h3⟩⟩ := hD
  · exact ⟨by rwa [hl], Or.inl (by rwa [hl])⟩
  · exact ⟨by rwa [hl], Or.inr (Or.inl ⟨by rwa [hl], r, by rwa [hl], hm r h3⟩)⟩
  · exact ⟨by rwa [hl], Or.inr (Or.inr ⟨by rwa [hl], by rw [hl]; exact hm _ h3⟩)⟩

lemma pot_congr {p : P} {C C' : Cfg P 1} (hl : C'.loc p = C.loc p) : pot p C' = pot p C := by
  simp only [pot, hl]

/-- Doomed configurations stay doomed until `p` decides; `pot` never increases and decreases at
every step of `p`. -/
lemma doomed_step {α : List (Label P (laObj P))} {C C' : Cfg P 1} {ℓ : Label P (laObj P)}
    {p : P} (hB : BInv α C) (hD : Doomed p C)
    (h : (alg1 1).step C ℓ = some C') (hnd : (C'.loc p).phase ≠ .done) :
    Doomed p C' ∧ pot p C' ≤ pot p C ∧ (ℓ = .tau p → pot p C' < pot p C) := by
  by_cases hℓ : ℓ.proc = p
  swap
  · have hl := (Impl.step_other h hℓ).1
    refine ⟨hD.congr hl (fun r hr => nonP_step_other hB h hℓ hr), (pot_congr hl).le, ?_⟩
    rintro rfl; exact absurd rfl hℓ
  cases ℓ with
  | inv q o =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨-, -, h3, h4⟩ := step_inv_alg1 h
    have hlp : C'.loc q = if (C.loc q).phase = .idle then { C.loc q with phase := .wr }
        else C.loc q := by rw [h3, Function.update_self]
    by_cases hid : (C.loc q).phase = .idle
    · rw [ite_eq_left hid] at hlp
      obtain ⟨-, h2 | ⟨h2, -⟩ | ⟨-, h3⟩⟩ := hD
      · refine ⟨⟨hnd, Or.inl (by rwa [hlp])⟩, ?_, by simp⟩
        simp [pot, dist, hlp, hid]
      · rw [hid] at h2; cases h2
      · refine ⟨⟨hnd, Or.inr (Or.inr ⟨by rw [hlp]; simp, by rw [hlp, h4]; exact h3⟩)⟩, ?_,
          by simp⟩
        simp [pot, dist, hlp, hid]
    · rw [ite_eq_right hid] at hlp
      exact ⟨hD.congr hlp (fun r hr => by rwa [h4]), (pot_congr hlp).le, by simp⟩
  | ret q o =>
    obtain ⟨-, -, h3, h4, -⟩ := step_ret_alg1 h
    have hl : C'.loc p = C.loc p := by rw [h4]
    exact ⟨hD.congr hl (fun r hr => by rwa [h3]), (pot_congr hl).le, by simp⟩
  | tau q =>
    simp only [Label.proc] at hℓ; subst hℓ
    have hself := hB.self q
    obtain ⟨hnd0, hD'⟩ := hD
    rcases step_tau_k1 h with ⟨hph, hm, hl⟩ | ⟨hph, hj, hm, hl⟩ | ⟨hph, hj, hm, hl⟩ |
      ⟨hph, hj, hm, hl⟩ | ⟨hph, hj, hm, hl⟩
    · -- write
      have hpot : pot q C' < pot q C := by simp [pot, dist, hl, hph]
      refine ⟨⟨hnd, ?_⟩, hpot.le, fun _ => hpot⟩
      rcases hD' with h2 | ⟨h2, -⟩ | ⟨-, h3⟩
      · exact Or.inl (by rwa [hl])
      · rw [hph] at h2; cases h2
      · refine Or.inr (Or.inl ⟨by rw [hl]; rfl, (C.loc q).i + 1, by rw [hl]; exact Fin.zero_le _, ?_⟩)
        rw [hm, Function.update_of_ne (fin2_add_one_ne _)]; exact h3
    · -- first collect, first read
      have hpot : pot q C' < pot q C := by simp [pot, dist, hl, hph, hj]
      refine ⟨⟨hnd, ?_⟩, hpot.le, fun _ => hpot⟩
      rcases hD' with h2 | ⟨-, r, -, h3⟩ | ⟨h2, -⟩
      · left; rw [hl]; intro h'; exact h2 (Finset.subset_union_left.trans h')
      · rcases fin2_cases_k1 r with rfl | rfl
        · left; rw [hl]; intro h'; exact h3 (Finset.subset_union_right.trans h')
        · right; left; refine ⟨by rw [hl]; exact hph, 1, by rw [hl], by rw [hm]; exact h3⟩
      · exact absurd hph h2
    · -- first collect, second read
      have hD'' : ¬ (C'.loc q).seen ⊆ {q} := by
        rcases hD' with h2 | ⟨-, r, hr, h3⟩ | ⟨h2, -⟩
        · rw [hl]; intro h'; exact h2 (Finset.subset_union_left.trans h')
        · rw [hj] at hr
          obtain rfl : r = 1 := le_antisymm (fin2_le_one r) hr
          rw [hl]; intro h'; exact h3 (Finset.subset_union_right.trans h')
        · exact absurd hph h2
      have hpot : pot q C' < pot q C := by
        have : ¬ ((C.loc q).seen ∪ (C.mem 1).seen ⊆ {q}) := by rw [hl] at hD''; exact hD''
        simp [pot, dist, hl, hph, hj, this]
      exact ⟨⟨hnd, Or.inl hD''⟩, hpot.le, fun _ => hpot⟩
    · -- second collect, first read
      have hpot : pot q C' < pot q C := by
        simp only [pot, dist, hl, hph, hj, true_and]
        have : (C.loc q).seen ∪ ((C.loc q).collect 0).seen ⊆ {q} → (C.loc q).seen ⊆ {q} :=
          fun h' => Finset.subset_union_left.trans h'
        split_ifs <;> simp_all
      refine ⟨⟨hnd, ?_⟩, hpot.le, fun _ => hpot⟩
      rcases hD' with h2 | ⟨h2, -⟩ | ⟨-, h3⟩
      · left; rw [hl]; intro h'; exact h2 (Finset.subset_union_left.trans h')
      · rw [hph] at h2; cases h2
      · right; right; refine ⟨by rw [hl]; simp [hph], by rw [hl, hm]; exact h3⟩
    · -- second collect, second read: the decision
      rcases decision_cases_k1 (P := P) { C.loc q with
          snap := (C.loc q).snap && decide (C.mem 1 = (C.loc q).collect 1),
          seen := (C.loc q).seen ∪ ((C.loc q).collect 1).seen, j := 1 } with h' | ⟨h', hc, -⟩
      · rw [← hl] at h'; exact absurd h' hnd
      rw [← hl] at h'
      have hsub : (C.loc q).seen ⊆ {q} := by
        by_contra hs
        have := two_le_card (s := (C.loc q).seen ∪ ((C.loc q).collect 1).seen)
          (Finset.mem_union_left _ hself)
          (fun h'' => hs (Finset.subset_union_left.trans h''))
        simp only at hc; omega
      rcases hD' with h2 | ⟨h2, -⟩ | ⟨-, h3⟩
      · exact absurd hsub h2
      · rw [hph] at h2; cases h2
      have hpot : pot q C' < pot q C := by
        simp [pot, dist, h', hph, hj, hsub]
      refine ⟨⟨hnd, Or.inr (Or.inr ⟨by rw [h']; simp, ?_⟩)⟩, hpot.le, fun _ => hpot⟩
      rw [hm, hl, decision_i]; exact h3

/-! ### Progress of `p` -/

/-- Progress measure of a local state: increases by one with every step. -/
def progL (l : Loc P 1) : ℕ :=
  match l.phase with
  | .idle => 0
  | .wr => 5 * l.seq + 4
  | .col1 => 5 * l.seq + l.j.val
  | .col2 => 5 * l.seq + 2 + l.j.val
  | .done => 0

/-- Progress measure of `p`. -/
def prog (p : P) (C : Cfg P 1) : ℕ := progL (C.loc p)

lemma prog_step {C C' : Cfg P 1} {ℓ : Label P (laObj P)} {p : P} (hS : SInvK1 C)
    (h : (alg1 1).step C ℓ = some C') (hnd : (C'.loc p).phase ≠ .done) :
    prog p C ≤ prog p C' ∧ (ℓ = .tau p → prog p C' = prog p C + 1) ∧
      (ℓ ≠ .tau p → prog p C' = prog p C ∨ prog p C' = 4) := by
  by_cases hℓ : ℓ.proc = p
  swap
  · have hl := (Impl.step_other h hℓ).1
    refine ⟨by simp [prog, hl], ?_, fun _ => Or.inl (by simp [prog, hl])⟩
    rintro rfl; exact absurd rfl hℓ
  cases ℓ with
  | inv q o =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨-, -, h3, -⟩ := step_inv_alg1 h
    have hlp : C'.loc q = if (C.loc q).phase = .idle then { C.loc q with phase := .wr }
        else C.loc q := by rw [h3, Function.update_self]
    by_cases hid : (C.loc q).phase = .idle
    · refine ⟨by simp [prog, progL, hlp, hid], by simp, fun _ => Or.inr ?_⟩
      simp [prog, progL, hlp, hid, hS.idle_seq q hid]
    · exact ⟨by simp [prog, hlp, hid], by simp, fun _ => Or.inl (by simp [prog, hlp, hid])⟩
  | ret q o =>
    obtain ⟨-, -, -, h4, -⟩ := step_ret_alg1 h
    exact ⟨by simp [prog, h4], by simp, fun _ => Or.inl (by simp [prog, h4])⟩
  | tau q =>
    simp only [Label.proc] at hℓ; subst hℓ
    suffices e : prog q C' = prog q C + 1 from ⟨by omega, fun _ => e, fun h' => absurd rfl h'⟩
    rcases step_tau_k1 h with ⟨hph, hm, hl⟩ | ⟨hph, hj, hm, hl⟩ | ⟨hph, hj, hm, hl⟩ |
      ⟨hph, hj, hm, hl⟩ | ⟨hph, hj, hm, hl⟩
    · simp [prog, progL, hl, hph]; omega
    · simp [prog, progL, hl, hph, hj]
    · simp [prog, progL, hl, hph, hj]
    · simp [prog, progL, hl, hph, hj]
    · rcases decision_cases_k1 (P := P) { C.loc q with
          snap := (C.loc q).snap && decide (C.mem 1 = (C.loc q).collect 1),
          seen := (C.loc q).seen ∪ ((C.loc q).collect 1).seen, j := 1 } with h' | ⟨h', -, -⟩
      · rw [← hl] at h'; exact absurd h' hnd
      · rw [← hl] at h'
        have e1 : progL (C'.loc q) = 5 * (C'.loc q).seq + 4 := by simp [progL, h']
        simp only [prog]
        rw [e1, hl, decision_seq]
        simp [progL, hph, hj]

lemma prog_decode {p : P} {C : Cfg P 1} {s : ℕ} (h : prog p C = 5 * s + 3) :
    (C.loc p).phase = .col2 ∧ (C.loc p).j = 1 ∧ (C.loc p).seq = s := by
  have hj := (C.loc p).j.isLt
  unfold prog progL at h
  split at h <;> rename_i hph
  · omega
  · omega
  · omega
  · refine ⟨hph, Fin.ext (by simp; omega), by omega⟩
  · omega

lemma prog_le (p : P) (C : Cfg P 1) : prog p C ≤ 5 * (C.loc p).seq + 4 := by
  have hj := (C.loc p).j.isLt
  unfold prog progL; split <;> omega

/-! ### Other processes write `A[1]` at most once (in a never-doomed execution) -/

/-- Invariant of a process `x ≠ p` in an odd iteration after its third write: it outputs
instead of writing `A[1]` again. -/
def IA (p : P) (C : Cfg P 1) : Prop :=
  ∀ x, x ≠ p → (C.loc x).seq % 2 = 1 → 3 ≤ (C.loc x).seq →
    ((C.loc x).phase = .col1 → (C.loc x).j = 1 →
        (((C.loc x).collect 0).id = some x ∧ (C.mem 1).id ≠ some x) ∨
          2 ≤ (C.loc x).seen.card) ∧
    ((C.loc x).phase = .col2 → 2 ≤ (C.loc x).seen.card) ∧ (C.loc x).phase ≠ .wr

lemma ia_init (p : P) : IA p ((alg1 (P := P) 1).initCfg) := by
  intro x _ _ h3; simp [Impl.initCfg, alg1, locInit] at h3

lemma ia_step {α : List (Label P (laObj P))} {C C' : Cfg P 1} {ℓ : Label P (laObj P)}
    {p : P} (hB : BInv α C) (hS : SInvK1 C) (hND : ¬ Doomed p C)
    (hpd : (C.loc p).phase ≠ .done) (h : (alg1 1).step C ℓ = some C') (hI : IA p C) :
    IA p C' := by
  intro x hxp hodd h3
  by_cases hℓ : ℓ.proc = x
  swap
  · have hl := (Impl.step_other h hℓ).1
    rw [hl] at hodd h3 ⊢
    obtain ⟨a1, a2, a3⟩ := hI x hxp hodd h3
    refine ⟨fun hc hj => ?_, a2, a3⟩
    rcases a1 hc hj with ⟨h1, h2⟩ | h1
    · refine Or.inl ⟨h1, ?_⟩
      rcases step_mem h with hm | ⟨y, rfl, -, hm⟩
      · rwa [hm]
      · rw [hm, Function.update_apply]; split_ifs
        · simp only [ne_eq, Option.some.injEq]; exact hℓ
        · exact h2
    · exact Or.inr h1
  cases ℓ with
  | inv q o =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨-, -, h4, h5⟩ := step_inv_alg1 h
    have hlp : C'.loc q = if (C.loc q).phase = .idle then { C.loc q with phase := .wr }
        else C.loc q := by rw [h4, Function.update_self]
    by_cases hid : (C.loc q).phase = .idle
    · rw [hlp, ite_eq_left hid] at h3; simp [hS.idle_seq q hid] at h3
    · rw [hlp, ite_eq_right hid] at hodd h3 ⊢; rw [h5]; exact hI q hxp hodd h3
  | ret q o =>
    obtain ⟨-, -, h4, h5, -⟩ := step_ret_alg1 h
    rw [h5] at hodd h3 ⊢; rw [h4]; exact hI x hxp hodd h3
  | tau q =>
    simp only [Label.proc] at hℓ; subst hℓ
    have hself := hB.self q
    rcases step_tau_k1 h with ⟨hph, hm, hl⟩ | ⟨hph, hj, hm, hl⟩ | ⟨hph, hj, hm, hl⟩ |
      ⟨hph, hj, hm, hl⟩ | ⟨hph, hj, hm, hl⟩
    · rw [hl]; refine ⟨fun _ hj => (by simp at hj), fun hc => (by simp at hc), by simp⟩
    · rw [hl] at hodd h3 ⊢
      simp only at hodd h3 ⊢
      refine ⟨fun _ _ => ?_, fun hc => (by rw [hph] at hc; cases hc), by rw [hph]; simp⟩
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (hS.mem0 q (by omega))
      by_cases hyq : y = q
      · subst hyq
        refine Or.inl ⟨by simp [hy], ?_⟩
        rw [hm]; intro h1
        apply hND
        have n1 : NonP p (C.mem 1) := fun hs => hxp (Finset.mem_singleton.1 (hs (hS.mem_self 1 y h1)))
        have n0' : NonP p (C.mem 0) := fun hs => hxp (Finset.mem_singleton.1 (hs (hS.mem_self 0 y hy)))
        refine ⟨hpd, Or.inr ?_⟩
        by_cases hp1 : (C.loc p).phase = .col1
        · exact Or.inl ⟨hp1, 1, fin2_le_one _, n1⟩
        · refine Or.inr ⟨hp1, ?_⟩
          rcases fin2_cases_k1 ((C.loc p).i + 1) with e | e <;> rw [e]
          · exact n0'
          · exact n1
      · right
        apply two_le_card (Finset.mem_union_left _ hself)
        intro hs
        exact hyq (Finset.mem_singleton.1 (hs (Finset.mem_union_right _ (hS.mem_self 0 y hy))))
    · rw [hl] at hodd h3 ⊢
      simp only at hodd h3 ⊢
      obtain ⟨a1, -, -⟩ := hI q hxp hodd h3
      refine ⟨fun hc => (by cases hc), fun _ => ?_, by simp⟩
      rcases a1 hph hj with ⟨-, h2⟩ | h1
      · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (hS.mem1 q (by omega))
        have hyq : y ≠ q := fun e => h2 (by rw [hy, e])
        apply two_le_card (Finset.mem_union_left _ hself)
        intro hs
        exact hyq (Finset.mem_singleton.1 (hs (Finset.mem_union_right _ (hS.mem_self 1 y hy))))
      · exact h1.trans (Finset.card_le_card Finset.subset_union_left)
    · rw [hl] at hodd h3 ⊢
      simp only at hodd h3 ⊢
      obtain ⟨-, a2, -⟩ := hI q hxp hodd h3
      refine ⟨fun hc => (by rw [hph] at hc; cases hc), fun _ => ?_, by rw [hph]; simp⟩
      exact (a2 hph).trans (Finset.card_le_card Finset.subset_union_left)
    · obtain ⟨-, a2, -⟩ := hI q hxp (by rw [hl] at hodd; simpa using hodd)
        (by rw [hl] at h3; simpa using h3)
      have hd : (C'.loc q).phase = .done := by
        rw [hl]; apply decision_done; left
        exact lt_of_lt_of_le (by omega) ((a2 hph).trans (Finset.card_le_card Finset.subset_union_left))
      rw [hd]; exact ⟨fun hc => (by cases hc), fun hc => (by cases hc), by simp⟩

/-! ### Provenance of second writes -/

/-- A process that is about to make its second write (to `A[1]`) and read the initial value of
`A[1]` belongs to `X`. -/
def PROV (X : Set P) (C : Cfg P 1) : Prop :=
  ∀ x, ((C.loc x).phase = .col2 ∨ (C.loc x).phase = .wr) → (C.loc x).seq = 1 →
    ((C.loc x).collect 1).id = none → x ∈ X

lemma prov_init (X : Set P) : PROV X ((alg1 (P := P) 1).initCfg) := by
  intro x hx; simp [Impl.initCfg, alg1, locInit] at hx

lemma prov_step {X : Set P} {C C' : Cfg P 1} {ℓ : Label P (laObj P)} (hS : SInvK1 C)
    (h : (alg1 1).step C ℓ = some C') (hX : (C.mem 1).id = none → ℓ.proc ∈ X)
    (hP : PROV X C) : PROV X C' := by
  intro x hph hs hc
  by_cases hℓ : ℓ.proc = x
  swap
  · have hl := (Impl.step_other h hℓ).1
    rw [hl] at hph hs hc; exact hP x hph hs hc
  cases ℓ with
  | inv q o =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨-, -, h4, -⟩ := step_inv_alg1 h
    have hlp : C'.loc q = if (C.loc q).phase = .idle then { C.loc q with phase := .wr }
        else C.loc q := by rw [h4, Function.update_self]
    by_cases hid : (C.loc q).phase = .idle
    · rw [hlp, ite_eq_left hid] at hs; simp [hS.idle_seq q hid] at hs
    · rw [hlp, ite_eq_right hid] at hph hs hc; exact hP q hph hs hc
  | ret q o =>
    obtain ⟨-, -, -, h5, -⟩ := step_ret_alg1 h
    rw [h5] at hph hs hc; exact hP x hph hs hc
  | tau q =>
    simp only [Label.proc] at hℓ hX; subst hℓ
    rcases step_tau_k1 h with ⟨hph', hm, hl⟩ | ⟨hph', hj, hm, hl⟩ | ⟨hph', hj, hm, hl⟩ |
      ⟨hph', hj, hm, hl⟩ | ⟨hph', hj, hm, hl⟩
    · rw [hl] at hph; simp at hph
    · rw [hl] at hph; simp [hph'] at hph
    · rw [hl] at hc; simp only [Function.update_self] at hc; exact hX hc
    · rw [hl] at hs hc; exact hP q (Or.inl hph') hs hc
    · rw [hl] at hs hc; simp only [decision_seq, decision_collect] at hs hc
      exact hP q (Or.inl hph') hs hc

/-! ### Late iterations of `p` -/

lemma seen_sub_of_not_doomed {p : P} {C : Cfg P 1} (hND : ¬ Doomed p C)
    (hpd : (C.loc p).phase ≠ .done) : (C.loc p).seen ⊆ {p} := by
  by_contra h; exact hND ⟨hpd, Or.inl h⟩

/-- In an odd iteration (`p` wrote `A[0]`), `p` reading a non-`p` value of `A[0]` in its second
collect would be doomed. -/
lemma mem0_of_not_doomed {p : P} {C : Cfg P 1} (hS : SInvK1 C) (hND : ¬ Doomed p C)
    (hpd : (C.loc p).phase ≠ .done) (hph : (C.loc p).phase = .col2)
    (hodd : (C.loc p).seq % 2 = 1) : ¬ NonP p (C.mem 0) := by
  intro hn; apply hND
  refine ⟨hpd, Or.inr (Or.inr ⟨by rw [hph]; simp, ?_⟩)⟩
  have hi : (C.loc p).i = 1 := Fin.ext (by rw [hS.i_par p, hodd]; rfl)
  rw [hi]; exact hn

/-- Invariant of `p`'s odd iterations that started after the last write of another process to
`A[1]` (sequence number above `sT`). -/
def QP (p : P) (sT : ℕ) (C : Cfg P 1) : Prop :=
  sT < (C.loc p).seq → (C.loc p).seq % 2 = 1 → 3 ≤ (C.loc p).seq →
    ((C.loc p).phase = .col1 → (C.loc p).j = 1 →
        ((C.loc p).collect 0).id ≠ none ∧ (C.mem 0 = (C.loc p).collect 0 ∨ NonP p (C.mem 0))) ∧
    ((C.loc p).phase = .col2 →
        ((C.loc p).collect 0).id ≠ none ∧ ((C.loc p).collect 1).id ≠ none ∧
        C.mem 1 = (C.loc p).collect 1 ∧ (C.loc p).snap = true ∧
        ((C.loc p).j = 0 → C.mem 0 = (C.loc p).collect 0 ∨ NonP p (C.mem 0))) ∧
    (C.loc p).phase ≠ .wr

/-- At the end of such an iteration, `p` outputs. -/
lemma qp_final {α : List (Label P (laObj P))} {C C' : Cfg P 1} {p : P} {sT : ℕ}
    (hB : BInv α C) (hS : SInvK1 C) (hND : ¬ Doomed p C) (hpd : (C.loc p).phase ≠ .done)
    (hQ : QP p sT C) (hs : sT < (C.loc p).seq) (hodd : (C.loc p).seq % 2 = 1)
    (h3 : 3 ≤ (C.loc p).seq) (hph : (C.loc p).phase = .col2) (hj : (C.loc p).j = 1)
    (h : (alg1 1).step C (.tau p) = some C') : (C'.loc p).phase = .done := by
  have c := (hQ hs hodd h3).2.1 hph
  obtain ⟨c0, c1, hm1, hsnap, -⟩ := c
  have hsub := seen_sub_of_not_doomed hND hpd
  have hseen : (C.loc p).seen = {p} :=
    Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.2 (hB.self p))
  have hcol : ∀ r, ((C.loc p).collect r).id ≠ none → ((C.loc p).collect r).seen = {p} := by
    intro r hr
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hr
    have hw' := hS.col_self p r w hw
    have hsub' := (hS.col_sub p r).trans hsub
    have : w = p := Finset.mem_singleton.1 (hsub' hw')
    subst this
    exact Finset.Subset.antisymm hsub' (Finset.singleton_subset_iff.2 hw')
  rcases step_tau_k1 h with ⟨hph', -⟩ | ⟨hph', -⟩ | ⟨hph', -⟩ | ⟨-, hj', -⟩ |
    ⟨-, -, -, hl⟩
  · rw [hph] at hph'; cases hph'
  · rw [hph] at hph'; cases hph'
  · rw [hph] at hph'; cases hph'
  · rw [hj] at hj'; cases hj'
  rw [hl]; apply decision_done; right
  refine ⟨by simp [hsnap, hm1], fun r => ?_⟩
  simp only
  rw [hseen, hcol 1 c1]
  rcases fin2_cases_k1 r with rfl | rfl
  · rw [hcol 0 c0]; simp
  · rw [hcol 1 c1]; simp

lemma qp_step {α : List (Label P (laObj P))} {C C' : Cfg P 1} {ℓ : Label P (laObj P)}
    {p : P} {sT : ℕ} (hB : BInv α C) (hS : SInvK1 C) (hND : ¬ Doomed p C)
    (hpd : (C.loc p).phase ≠ .done)
    (hFW : ∀ y, ℓ = .tau y → y ≠ p → (C.loc y).phase = .wr → (C.loc y).i ≠ 1)
    (h : (alg1 1).step C ℓ = some C') (hQ : QP p sT C) : QP p sT C' := by
  intro hs hodd h3
  by_cases hℓ : ℓ.proc = p
  swap
  · have hl := (Impl.step_other h hℓ).1
    rw [hl] at hs hodd h3 ⊢
    obtain ⟨a1, a2, a3⟩ := hQ hs hodd h3
    -- the memory: unchanged, or a write of another process to `A[0]`
    have hm : (C'.mem 1 = C.mem 1) ∧ (C'.mem 0 = C.mem 0 ∨ NonP p (C'.mem 0)) := by
      rcases step_mem h with hm | ⟨y, rfl, hy, hm⟩
      · rw [hm]; exact ⟨rfl, Or.inl rfl⟩
      · have hi : (C.loc y).i = 0 := by
          rcases fin2_cases_k1 (C.loc y).i with e | e
          · exact e
          · exact absurd e (hFW y rfl hℓ hy)
        rw [hm, hi]
        refine ⟨Function.update_of_ne (by decide) _ _, Or.inr ?_⟩
        rw [Function.update_self]; exact nonP_write hℓ (hB.self y)
    obtain ⟨hm1, hm0⟩ := hm
    refine ⟨fun hc hj => ?_, fun hc => ?_, a3⟩
    · obtain ⟨b1, b2⟩ := a1 hc hj
      refine ⟨b1, ?_⟩
      rcases hm0 with e | e
      · rw [e]; exact b2
      · exact Or.inr e
    · obtain ⟨b1, b2, b3, b4, b5⟩ := a2 hc
      refine ⟨b1, b2, by rw [hm1]; exact b3, b4, fun hj => ?_⟩
      rcases hm0 with e | e
      · rw [e]; exact b5 hj
      · exact Or.inr e
  cases ℓ with
  | inv q o =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨-, -, h4, h5⟩ := step_inv_alg1 h
    have hlp : C'.loc q = if (C.loc q).phase = .idle then { C.loc q with phase := .wr }
        else C.loc q := by rw [h4, Function.update_self]
    by_cases hid : (C.loc q).phase = .idle
    · rw [hlp, ite_eq_left hid] at hs; simp [hS.idle_seq q hid] at hs
    · rw [hlp, ite_eq_right hid] at hs hodd h3 ⊢; rw [h5]; exact hQ hs hodd h3
  | ret q o =>
    obtain ⟨-, -, h4, h5, -⟩ := step_ret_alg1 h
    rw [h5] at hs hodd h3 ⊢; rw [h4]; exact hQ hs hodd h3
  | tau q =>
    simp only [Label.proc] at hℓ; subst hℓ
    rcases step_tau_k1 h with ⟨hph, hm, hl⟩ | ⟨hph, hj, hm, hl⟩ | ⟨hph, hj, hm, hl⟩ |
      ⟨hph, hj, hm, hl⟩ | ⟨hph, hj, hm, hl⟩
    · rw [hl]; exact ⟨fun _ hj => (by simp at hj), fun hc => (by simp at hc), by simp⟩
    · rw [hl] at hs hodd h3 ⊢
      simp only at hs hodd h3 ⊢
      refine ⟨fun _ _ => ⟨by simpa using hS.mem0 q (by omega), Or.inl (by rw [hm]; simp)⟩,
        fun hc => (by rw [hph] at hc; cases hc), by rw [hph]; simp⟩
    · rw [hl] at hs hodd h3 ⊢
      simp only at hs hodd h3 ⊢
      obtain ⟨a1, -, -⟩ := hQ hs hodd h3
      obtain ⟨b1, b2⟩ := a1 hph hj
      refine ⟨fun hc => (by cases hc), fun _ => ⟨?_, ?_, ?_, by simp, fun _ => ?_⟩, by simp⟩
      · rw [Function.update_of_ne (by decide)]; exact b1
      · simpa using hS.mem1 q (by omega)
      · rw [hm]; simp
      · rw [hm, Function.update_of_ne (by decide)]; exact b2
    · rw [hl] at hs hodd h3 ⊢
      simp only at hs hodd h3 ⊢
      obtain ⟨-, a2, -⟩ := hQ hs hodd h3
      obtain ⟨b1, b2, b3, b4, b5⟩ := a2 hph
      have e0 : C.mem 0 = (C.loc q).collect 0 := by
        rcases b5 hj with e | e
        · exact e
        · exact absurd e (mem0_of_not_doomed hS hND hpd hph hodd)
      refine ⟨fun hc => (by rw [hph] at hc; cases hc), fun _ => ⟨b1, b2, by rw [hm]; exact b3,
        by simp [b4, e0], fun hj' => (by simp at hj')⟩, by rw [hph]; simp⟩
    · have hd := qp_final hB hS hND hpd hQ (by rw [hl] at hs; simpa using hs)
        (by rw [hl] at hodd; simpa using hodd) (by rw [hl] at h3; simpa using h3) hph hj h
      rw [hd]; exact ⟨fun hc => (by cases hc), fun hc => (by cases hc), by simp⟩

end Cslib.SharedMemory.StrangerFree
