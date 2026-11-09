import Papers.PODC2010.GroupMutexLogRMR.Model
import Cslib.Foundations.Data.Finset.SumUpdate

/-!
# The inductive invariant behind mutual exclusion (P1)

The paper derives P1 from its Invariant 5 and states Invariants 1–8 without proofs. Several of
them are false or imprecise as stated (see `Deadlock.lean` for Invariant 8), and none is inductive
on its own. `Inv` below is an inductive strengthening (validated first with an explicit-state
model checker): its clause `i5` is the paper's Invariant 5, `l1` is the paper's Lemma 1, `a3`,
`e2`, `e3` are the paper's Invariant 2, `p5`, `p11`, `p13` are the paper's Invariant 4, and the
clauses `w1`–`w5`, `win`, `winS` describe the `Ex`/`Exclear` protocol (the paper's Invariants 6–7,
corrected).
-/

namespace Podc.GroupMutexLogRMR

/-- Position of a program counter in the code. -/
def PC.idx : PC → ℕ
  | .rem => 0 | .l1_1 => 1 | .l1_2 => 2 | .l1_3 => 3 | .l1_4 => 4 | .l1_5 => 5 | .l1_6 => 6
  | .l1_7 => 7 | .l2 => 8 | .l3 => 9 | .l4 => 10 | .l5_1 => 11 | .l5_2 => 12 | .l5_3 => 13
  | .l5_4 => 14 | .l5_5 => 15 | .l6 => 16 | .l7 => 17 | .l8 => 18 | .l9 => 19 | .l10 => 20
  | .l11 => 21 | .l12 => 22 | .cs => 23 | .l13 => 24 | .l14 => 25 | .l15 => 26 | .l16_1 => 27
  | .l16_2 => 28 | .l16_3 => 29 | .l16_4 => 30 | .l16_5 => 31 | .l16_6 => 32 | .l16_7 => 33
  | .l16_8 => 34 | .l16_9 => 35 | .l16_10 => 36 | .l16_11 => 37 | .l16_12 => 38 | .l16_13 => 39
  | .l16_14 => 40

/-- `pc` lies between `lo` and `hi` (inclusive) in the code. -/
def PC.btw (lo hi pc : PC) : Prop := lo.idx ≤ pc.idx ∧ pc.idx ≤ hi.idx

instance (lo hi pc : PC) : Decidable (PC.btw lo hi pc) := by unfold PC.btw; infer_instance

variable {n : ℕ} {J : Type} [DecidableEq J]

/-- Contribution of a process to the counter `C[s,d]`. -/
def Loc.cnt (l : Loc J) (s : J) (d : Bool) : ℕ :=
  if l.s = s then
    if l.pc = .l1_2 then (if d = false then 1 else 0)
    else if PC.btw .l1_3 .l1_7 l.pc then 1
    else if PC.btw .l2 .l16_6 l.pc ∧ l.d = d then 1 else 0
  else 0

/-- The side of a process in the sense of the paper ("`p` is of side `d'`"): its `d` at lines
1.4–16.6, except at line 1.6, where it is `d̄`. -/
def Loc.pside (l : Loc J) : Option Bool :=
  if l.pc = .l1_6 then some (!l.d)
  else if PC.btw .l1_4 .l16_6 l.pc then some l.d else none

/-- No process of session `s` is of side `e`, and none is at lines 1.5–1.6. -/
def NoSide (c : Cfg n J) (s : J) (e : Bool) : Prop :=
  ∀ z, (c.loc z).s = s → (c.loc z).pc ≠ .l1_5 ∧ (c.loc z).pc ≠ .l1_6 ∧ (c.loc z).pside ≠ some e

/-- A process of session `s` and side `d` with program counter in `[lo, hi]`. -/
def ExW (c : Cfg n J) (s : J) (d : Bool) (lo hi : PC) : Prop :=
  ∃ m, (c.loc m).s = s ∧ (c.loc m).d = d ∧ PC.btw lo hi (c.loc m).pc

/-- Per-process clauses of the invariant. -/
structure LI (c : Cfg n J) (y : Fin n) : Prop where
  tm : PC.btw .l4 .l13 (c.loc y).pc → (c.loc y).tm ≤ c.G
  l1 : PC.btw .l1_7 .l8 (c.loc y).pc → c.S.1 = (c.loc y).s → c.S.2.1 = !(c.loc y).d →
    ∃ q, (c.loc q).s ≠ (c.loc y).s ∧ PC.btw .l5_1 .l8 (c.loc q).pc ∧
      ((c.loc y).pc = .l3 → (c.loc q).tm < c.G) ∧
      (PC.btw .l4 .l8 (c.loc y).pc → (c.loc q).tm < (c.loc y).tm)
  l14 : ((c.loc y).pc = .l1_4 ∨ (c.loc y).pc = .l1_5) →
    (c.loc y).d = c.In (c.loc y).s ∨ (c.S.1 = (c.loc y).s ∧ c.S.2.1 = (c.loc y).d)
  l16 : (c.loc y).pc = .l1_6 → c.S.1 = (c.loc y).s ∧ c.S.2.1 = !(c.loc y).d
  i5 : PC.btw .l9 .l16_6 (c.loc y).pc →
    c.S.1 = (c.loc y).s ∧ c.S.2.1 = (c.loc y).d ∧ c.Out (c.loc y).s = (c.loc y).d
  i7 : (c.loc y).pc = .l7 → c.S = ((c.loc y).s, (c.loc y).d, (c.loc y).s)
  i8 : PC.btw .l1_7 .l8 (c.loc y).pc → c.Out (c.loc y).s = (c.loc y).d →
    c.S.1 = (c.loc y).s ∧ c.S.2.1 = (c.loc y).d
  a1 : ((c.loc y).pc = .l5_2 ∨ (c.loc y).pc = .l5_3) → c.linkS y = true →
    (c.loc y).a = (c.S.1, c.S.2.1)
  a2 : ((c.loc y).pc = .l5_3 ∨ (c.loc y).pc = .l5_4) → c.linkS y = true →
    ∃ sh dh, (c.loc y).b = some (sh, dh) ∧ (sh ≠ c.S.1 → ExW c sh dh .l5_1 .l8)
  a3 : (c.loc y).pc = .l5_4 → c.linkS y = true →
    NoSide c c.S.1 c.S.2.1 ∧ ∀ sh dh, (c.loc y).b = some (sh, dh) → sh ≠ c.S.1
  p5 : (c.loc y).pc = .l5_5 → ∃ sh dh, (c.loc y).b = some (sh, dh) ∧
    (sh ≠ (c.loc y).s → c.S = (sh, dh, (c.loc y).s) ∧ c.Out sh ≠ dh ∧ ExW c sh dh .l5_1 .l8) ∧
    (sh = (c.loc y).s → c.S.1 = sh ∧ c.S.2.1 = dh ∧ (c.loc y).d = dh)
  e1 : PC.btw .l16_5 .l16_10 (c.loc y).pc → c.linkS y = true →
    c.S.1 = (c.loc y).s ∧ c.S.2.1 = (c.loc y).d
  x1 : PC.btw .l16_8 .l16_9 (c.loc y).pc → c.linkS y = true →
    (c.loc y).b ≠ some ((c.loc y).s, !(c.loc y).d)
  x2 : PC.btw .l16_8 .l16_9 (c.loc y).pc → c.linkS y = true → ∀ sh dh,
    (c.loc y).b = some (sh, dh) → sh ≠ (c.loc y).s → ExW c sh dh .l5_1 .l8
  x3 : PC.btw .l16_8 .l16_9 (c.loc y).pc → c.linkEx y = true → ∀ dh,
    (c.loc y).b = some ((c.loc y).s, dh) → ∃ m, (c.loc m).s = (c.loc y).s ∧ (c.loc m).d = dh ∧
      PC.btw .l5_1 .l16_2 (c.loc m).pc ∧ ((c.loc m).pc = .l16_2 → c.linkEx m = true)
  e2 : (c.loc y).pc = .l16_9 → c.linkS y = true → c.linkEx y = true →
    NoSide c (c.loc y).s (c.loc y).d ∧ ∃ sh dh, (c.loc y).b = some (sh, dh) ∧ sh ≠ (c.loc y).s
  e3 : (c.loc y).pc = .l16_10 → c.linkS y = true →
    NoSide c (c.loc y).s (c.loc y).d ∧ ∃ sh dh, (c.loc y).b = some (sh, dh) ∧ sh ≠ (c.loc y).s ∧
      ExW c sh dh .l5_1 .l8
  p11 : (c.loc y).pc = .l16_11 → ∃ sh dh, (c.loc y).b = some (sh, dh) ∧
    c.S = (sh, dh, (c.loc y).s) ∧ sh ≠ (c.loc y).s ∧ c.Out sh ≠ dh ∧ ExW c sh dh .l5_1 .l8
  w1 : PC.btw .l16_4 .l16_9 (c.loc y).pc → c.linkEx y = true → c.Ex = none
  w2 : PC.btw .l16_4 .l16_9 (c.loc y).pc → c.linkEx y = true → ∀ z,
    (PC.btw .l11 .l16_3 (c.loc z).pc ∨ ((c.loc z).pc = .l10 ∧ c.linkEx z = false)) →
    (c.loc z).s = (c.loc y).s ∧ (c.loc z).d = (c.loc y).d ∧ (c.loc y).pc ≠ .l16_9
  w3 : ((c.loc y).pc = .l16_3 ∨ ((c.loc y).pc = .l16_2 ∧ c.linkEx y = false)) → c.Ex = none
  w4 : PC.btw .l16_4 .l16_9 (c.loc y).pc → c.linkEx y = true →
    ¬ (c.S.1 = (c.loc y).s ∧ c.S.2.1 = (c.loc y).d) →
    ∃ m, (c.loc m).s = c.S.1 ∧ (c.loc m).d = c.S.2.1 ∧ PC.btw .l5_1 .l10 (c.loc m).pc ∧
      ((c.loc m).pc = .l10 → c.linkEx m = true)
  w5 : PC.btw .l16_6 .l16_9 (c.loc y).pc → c.linkEx y = true → c.Exclear (c.loc y).s = false
  win : PC.btw .l16_10 .l16_14 (c.loc y).pc →
    c.Ex = some (c.loc y).s ∧ c.Exclear (c.loc y).s = false ∧ ∀ z, z ≠ y →
      ¬ PC.btw .l16_10 .l16_14 (c.loc z).pc ∧
      (PC.btw .l11 .l16_3 (c.loc z).pc →
        (c.loc z).pc = .l11 ∨ ((c.loc z).pc = .l12 ∧ (c.loc z).a.1 = (c.loc y).s)) ∧
      ((c.loc z).pc = .l10 → c.linkEx z = false) ∧
      (PC.btw .l16_4 .l16_9 (c.loc z).pc → c.linkEx z = false)
  winS : PC.btw .l16_10 .l16_14 (c.loc y).pc → c.S.1 ≠ (c.loc y).s → ExW c c.S.1 c.S.2.1 .l5_1 .l12
  p13 : (c.loc y).pc = .l16_13 → c.S = ((c.loc y).a.1, (c.loc y).a.2, (c.loc y).a.1) ∨
    (c.Out (c.loc y).a.1 = (c.loc y).a.2 ∧ c.S.1 ≠ (c.loc y).a.1 ∧ (c.loc y).a.1 = (c.loc y).s)

/-- The invariant. -/
structure Inv (c : Cfg n J) : Prop where
  gC : ∀ s d, c.C s d = ∑ y, (c.loc y).cnt s d
  gQ : ∀ y, c.Q y = if PC.btw .l5_1 .l13 (c.loc y).pc then
    some ((c.loc y).s, (c.loc y).d, (c.loc y).tm) else none
  g4 : ∀ s, c.In s ≠ c.Out s ∨ (c.S.1 = s ∧ c.S.2.1 = c.Out s)
  g5 : ∀ s, c.S.1 = s → c.In s = c.S.2.1 → ∃ y, (c.loc y).s = s ∧
    (c.loc y).pside = some c.S.2.1 ∧ PC.btw .l1_4 .l15 (c.loc y).pc
  g7 : ∀ s y, c.S.1 ≠ s → (c.loc y).s = s → ∀ e, (c.loc y).pside = some e → e = c.In s
  gU : ∀ y z, y ≠ z → ((c.loc y).pc = .l5_5 ∨ (c.loc y).pc = .l16_11) →
    (c.loc z).pc ≠ .l5_5 ∧ (c.loc z).pc ≠ .l16_11
  /-- the paper's Invariant 3 -/
  g8 : c.Out c.S.1 ≠ c.S.2.1 → ∃ z, ((c.loc z).pc = .l5_5 ∨ (c.loc z).pc = .l16_11) ∧
    (c.loc z).b = some (c.S.1, c.S.2.1) ∧ (c.loc z).s = c.S.2.2
  li : ∀ y, LI c y

/-! ## Basic facts -/

section Basic

/-- Invariant of the scan for the smallest element, after scanning the processes in `P`. -/
def QGood (Q : Fin n → Option (J × Bool × ℕ)) (acc : Option (Fin n)) (P : Fin n → Prop) : Prop :=
  (acc = none → ∀ q, P q → Q q = none) ∧
  (∀ r, acc = some r → ∃ s d t, Q r = some (s, d, t) ∧
    ∀ q, P q → ∀ s' d' t', Q q = some (s', d', t') → t ≤ t')

theorem qstep_good {Q : Fin n → Option (J × Bool × ℕ)} {acc : Option (Fin n)} {P : Fin n → Prop}
    (h : QGood Q acc P) (q : Fin n) : QGood Q (qstep Q acc q) (fun x => P x ∨ x = q) := by
  obtain ⟨h1, h2⟩ := h
  rcases hq : Q q with _ | ⟨sq, dq, tq⟩
  · have e : qstep Q acc q = acc := by simp [qstep, hq]
    rw [e]
    refine ⟨fun ha x hx => ?_, fun r hr => ?_⟩
    · rcases hx with hx | rfl
      · exact h1 ha x hx
      · exact hq
    · obtain ⟨s, d, t, he, hle⟩ := h2 r hr
      refine ⟨s, d, t, he, fun x hx s' d' t' hx' => ?_⟩
      rcases hx with hx | rfl
      · exact hle x hx s' d' t' hx'
      · rw [hq] at hx'; cases hx'
  · rcases acc with _ | r0
    · have e : qstep Q none q = some q := by simp [qstep, hq]
      rw [e]
      refine ⟨fun ha => (by cases ha), fun r hr => ?_⟩
      cases hr
      refine ⟨sq, dq, tq, hq, fun x hx s' d' t' hx' => ?_⟩
      rcases hx with hx | rfl
      · rw [h1 rfl x hx] at hx'; cases hx'
      · rw [hq] at hx'; cases hx'; exact le_rfl
    · obtain ⟨s0, d0, t0, he0, hle0⟩ := h2 r0 rfl
      by_cases hlt : tq < t0
      · have e : qstep Q (some r0) q = some q := by simp [qstep, hq, he0, hlt]
        rw [e]
        refine ⟨fun ha => (by cases ha), fun r hr => ?_⟩
        cases hr
        refine ⟨sq, dq, tq, hq, fun x hx s' d' t' hx' => ?_⟩
        rcases hx with hx | rfl
        · have := hle0 x hx s' d' t' hx'; omega
        · rw [hq] at hx'; cases hx'; exact le_rfl
      · have e : qstep Q (some r0) q = some r0 := by simp [qstep, hq, he0, hlt]
        rw [e]
        refine ⟨fun ha => (by cases ha), fun r hr => ?_⟩
        cases hr
        refine ⟨s0, d0, t0, he0, fun x hx s' d' t' hx' => ?_⟩
        rcases hx with hx | rfl
        · exact hle0 x hx s' d' t' hx'
        · rw [hq] at hx'; cases hx'; omega

theorem foldl_qstep_good {Q : Fin n → Option (J × Bool × ℕ)} (l : List (Fin n))
    {acc : Option (Fin n)} {P : Fin n → Prop} (h : QGood Q acc P) :
    QGood Q (l.foldl (qstep Q) acc) (fun x => P x ∨ x ∈ l) := by
  induction l generalizing acc P with
  | nil => simpa using h
  | cons q l ih =>
    have := ih (qstep_good h q)
    simp only [List.foldl_cons]
    refine ⟨fun ha x hx => this.1 ha x ?_, fun r hr => ?_⟩
    · rcases hx with hx | hx
      · exact Or.inl (Or.inl hx)
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr hx
    · obtain ⟨s, d, t, he, hle⟩ := this.2 r hr
      refine ⟨s, d, t, he, fun x hx => hle x ?_⟩
      rcases hx with hx | hx
      · exact Or.inl (Or.inl hx)
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr hx

theorem qminProc_good (Q : Fin n → Option (J × Bool × ℕ)) : QGood Q (qminProc Q) (fun _ => True) := by
  have := foldl_qstep_good (List.finRange n) (Q := Q) (acc := none) (P := fun _ => False)
    ⟨fun _ _ h => h.elim, fun r hr => by cases hr⟩
  refine ⟨fun ha x _ => this.1 ha x (Or.inr (List.mem_finRange x)), fun r hr => ?_⟩
  obtain ⟨s, d, t, he, hle⟩ := this.2 r hr
  exact ⟨s, d, t, he, fun x _ => hle x (Or.inr (List.mem_finRange x))⟩

/-- `Min(Q)` is `⊥` iff `Q` is empty. -/
theorem minQ_eq_none {Q : Fin n → Option (J × Bool × ℕ)} :
    minQ Q = none ↔ ∀ q, Q q = none := by
  have spec := qminProc_good Q
  constructor
  · intro h q
    unfold minQ at h
    rcases hp : qminProc Q with _ | r
    · exact spec.1 hp q trivial
    · rw [hp] at h
      obtain ⟨s, d, t, he, -⟩ := spec.2 r hp
      simp [he] at h
  · intro h
    unfold minQ
    rcases hp : qminProc Q with _ | r
    · rfl
    · obtain ⟨s, d, t, he, -⟩ := spec.2 r hp
      rw [h r] at he; cases he

/-- `Min(Q) = (s, d)` comes from an element of `Q` with the least time-stamp. -/
theorem minQ_eq_some {Q : Fin n → Option (J × Bool × ℕ)} {s : J} {d : Bool}
    (h : minQ Q = some (s, d)) :
    ∃ r t, Q r = some (s, d, t) ∧ ∀ q s' d' t', Q q = some (s', d', t') → t ≤ t' := by
  have spec := qminProc_good Q
  unfold minQ at h
  rcases hp : qminProc Q with _ | r
  · rw [hp] at h; cases h
  · rw [hp] at h
    obtain ⟨s0, d0, t, he, h2⟩ := spec.2 r hp
    simp only [Option.bind_some, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨r, t, he, fun q s' d' t' hq => h2 q trivial s' d' t' hq⟩

/-- A counter contribution is at most one. -/
theorem Loc.cnt_le_one (l : Loc J) (s : J) (d : Bool) : l.cnt s d ≤ 1 := by
  unfold Loc.cnt; split_ifs <;> simp

/-- If `C[s,d] = 0` then no process contributes to it. -/
theorem cnt_eq_zero_of_C {c : Cfg n J} (hI : Inv c) {s : J} {d : Bool} (h : c.C s d = 0) (y : Fin n) :
    (c.loc y).cnt s d = 0 := by
  rw [hI.gC] at h
  exact (Finset.sum_eq_zero_iff.1 h) y (Finset.mem_univ y)

/-- A contributing process makes the counter positive. -/
theorem C_pos_of_cnt {c : Cfg n J} (hI : Inv c) {s : J} {d : Bool} (y : Fin n)
    (h : (c.loc y).cnt s d ≠ 0) : c.C s d ≠ 0 := by
  intro h0; exact h (cnt_eq_zero_of_C hI h0 y)

/-- Sum of contributions after changing one local state. -/
theorem sum_cnt_update (loc : Fin n → Loc J) (p : Fin n) (l : Loc J) (s : J) (d : Bool) :
    ∑ y, (Function.update loc p l y).cnt s d + (loc p).cnt s d = ∑ y, (loc y).cnt s d + l.cnt s d :=
  Fintype.sum_comp_update_add (fun l : Loc J => l.cnt s d) loc p l

end Basic

/-- **Mutual exclusion (P1) from the invariant**: processes in the CS request the same session. -/
theorem Inv.mutex {c : Cfg n J} (hI : Inv c) (y z : Fin n) (hy : (c.loc y).pc = .cs)
    (hz : (c.loc z).pc = .cs) : (c.loc y).s = (c.loc z).s := by
  have h1 := (hI.li y).i5 (by rw [hy]; decide)
  have h2 := (hI.li z).i5 (by rw [hz]; decide)
  rw [← h1.1, ← h2.1]

end Podc.GroupMutexLogRMR
