import Papers.PODC2012.CloserLookFT.TestAndSet
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# Safety of the corrected test-and-set algorithm (Theorem 3.2, corrected)

Taubenfeld, *A closer look at fault tolerance*, PODC 2012, Section 3.1. `TestAndSet.lean` shows
that Theorem 3.2 (at most one winner) fails for the printed algorithm. Here we prove it for the
corrected algorithm (`fixed = true`: line 10 also loses when `locked = 0`) for **every** number
of processes `n ≥ 2` (`theorem_3_2_fixed`).

## Proof idea (an inductive invariant over global states, no ghost state)

Call `p` *holding* if it is at line 10 (second read), line 14, a winner, or at line 1 of `reset`
(`TLoc.hold`), and a *candidate* if `turn = p` and all locks `p` has checked so far held `p`
(`TLoc.cand`; `TLoc.cert` are the checked indices). For a holding or candidate process `p`:

* `lost p` — checked locks that no longer hold `p`;
* `dest p` — other processes with a pending write (line 5 `lock[j] := q`, or a release
  `lock[j] := 0`) to a lock that currently holds `p`;
* `live p` — other processes about to write `turn` (line 2), plus the competing process whose
  identifier is in `turn`.

Invariant `Inv`:
1. (`ic`) `|lost p| + |dest p| + |live p| ≤ n − 1`. When `p` starts checking, `dest p` and
   `live p` are disjoint sets of other processes. Afterwards `p` writes no lock, so a lock of `p`
   is lost only through a pending write of `dest p` (which leaves `dest p`); and nobody joins
   `live p`, because `turn ≠ 0` (`h0`) and only the owner of `turn` and line-2 writers count.
2. (`il`) If `p` is holding and `r ≠ p` is a candidate owning `turn`, then no lock checked by
   `r` holds `p` (`p` writes no lock while holding).
3. (`h1`) At most one process is holding. A second process `r` entering the holding zone would,
   by (2), have taken all `n − 1` locks from the holder `p`, so `|lost p| = n − 1` and by (1)
   `live p = ∅`, although `r ∈ live p`.

This is the paper's counting argument ("each other process can overwrite at most one lock
already set by another process") made precise; it does not use the `winner` register.
-/

namespace Podc.CloserLookFT.TAS

/-! ## Classification of locations -/

/-- The *holding zone*: lines 10 (second read) – 14, a winner, and the first line of `reset`. -/
def TLoc.hold : TLoc → Bool
  | .x10b | .w14 | .won | .r1a | .r1b => true
  | _ => false

/-- A *candidate*: a process that has verified all locks read so far (`locked = 1`). -/
def TLoc.cand : TLoc → Bool
  | .chk _ true | .u9a true | .x10a true => true
  | _ => false

/-- Competing locations (inside the `repeat` loop or at the first read of line 10). -/
def TLoc.comp : TLoc → Bool
  | .get _ | .getw _ | .chk _ _ | .u9a _ | .u9b | .x10a _ => true
  | _ => false

/-- The lock indices a process has already verified. -/
def TLoc.cert (n : ℕ) : TLoc → Finset ℕ
  | .chk j _ => Finset.Ico 1 j
  | _ => Finset.Icc 1 (n - 1)

/-- The lock index of a pending write. -/
def TLoc.target : TLoc → Option ℕ
  | .getw j | .relw j | .rrelw j => some j
  | _ => none

/-- Lock indices in program counters are in range. -/
def TLoc.idxOK (n : ℕ) : TLoc → Prop
  | .get j | .getw j | .chk j _ | .rel j | .relw j | .rrel j | .rrelw j => 1 ≤ j ∧ j ≤ n - 1
  | _ => True

/-- A pending write to a lock currently holding `p`. -/
def pendOn (m : TMem) (p : ℕ) (l : TLoc) : Bool :=
  match l.target with
  | some j => decide (m.lk j = p)
  | none => false

variable (n : ℕ)

/-! ## Effect of one step of the corrected algorithm -/

section Step
set_option linter.unusedSectionVars false
variable {n} {a : ℕ} {m m' : TMem} {l l' : TLoc}
  (hm : (tstep n true a m l).1 = m') (hl : (tstep n true a m l).2 = l')
include hm hl

theorem step_idx (hn : 2 ≤ n) (h : l.idxOK n) : l'.idxOK n := by
  subst hm hl
  cases l <;> simp only [tstep, nextGet, TLoc.idxOK] at h ⊢ <;> (try split_ifs) <;>
    simp <;> omega

theorem step_lock :
    m'.lock = m.lock ∨ ∃ j, l.target = some j ∧ l'.target = none ∧
      (m' = m.setLk j a ∨ m' = m.setLk j 0) := by
  subst hm hl
  cases l <;> simp only [tstep, nextGet] <;> (try split_ifs) <;> simp [TLoc.target]

theorem step_turn :
    m'.turn = m.turn ∨ (l = .l2 ∧ m'.turn = a) ∨ (l = .r1b ∧ m'.turn = 0) := by
  subst hm hl
  cases l <;> simp [tstep, TMem.setLk]

theorem step_target {j : ℕ} (h : l'.target = some j) :
    m' = m ∧ (m.lk j = 0 ∨ m.lk j = a) := by
  subst hm hl
  cases l <;> simp only [tstep, nextGet] at h ⊢ <;> (try split_ifs at h ⊢) <;>
    simp_all [TLoc.target]

theorem step_hold (h : l'.hold) :
    m'.lock = m.lock ∧ m'.turn = m.turn ∧ (l.hold ∨ (l = .x10a true ∧ m.turn = a)) := by
  subst hm hl
  cases l <;> simp only [tstep, nextGet] at h ⊢ <;> (try split_ifs at h ⊢) <;>
    simp_all [TLoc.hold]

theorem step_l2 (h : l' = .l2) : m' = m ∧ l = .l1 ∧ m.turn = 0 := by
  subst hm hl
  cases l <;> simp only [tstep, nextGet] at h ⊢ <;> (try split_ifs at h ⊢) <;> simp_all

theorem step_comp (h : l'.comp) : l.comp ∨ l = .l2 := by
  subst hm hl
  cases l <;> simp only [tstep, nextGet] at h ⊢ <;> (try split_ifs at h ⊢) <;> simp_all [TLoc.comp]

theorem step_cand (h : l'.cand) (ht : m'.turn = a) :
    l'.cert n = ∅ ∨
      (l.cand ∧ m' = m ∧ ∀ i ∈ l'.cert n, i ∈ l.cert n ∨ m.lk i = a) := by
  subst hm hl
  cases l with
  | chk j lo =>
    by_cases hj : m.lk j = a <;>
    cases lo <;> simp only [tstep] at h ht ⊢ <;> split_ifs at h ht ⊢ <;>
      simp_all [TLoc.cand, TLoc.cert] <;> right <;> intro i hi1 hi2 <;>
      rcases Nat.lt_or_ge i j with hij | hij <;> simp_all <;>
      (have : i = j := by omega) <;> simp_all
  | u9a lo =>
    cases lo <;> simp only [tstep] at h ht ⊢ <;> split_ifs at h ht ⊢
    all_goals simp_all [TLoc.cand, TLoc.cert]
  | _ =>
    simp only [tstep, nextGet] at h ht ⊢
    all_goals (try split_ifs at h ht ⊢) <;> simp_all [TLoc.cand, TLoc.cert]

end Step

/-! ## Locks -/

theorem TMem.lk_setLk_ne {m : TMem} {i j v : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i ≠ j) :
    (m.setLk j v).lk i = m.lk i := by
  simp only [TMem.lk, TMem.setLk, List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> omega

theorem TMem.lk_setLk_self {m : TMem} {j v : ℕ} (hj : 1 ≤ j) (hl : j ≤ m.lock.length) :
    (m.setLk j v).lk j = v := by
  simp only [TMem.lk, TMem.setLk, List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> first | omega | rfl

theorem TMem.lk_setLk {m : TMem} {i j v : ℕ} :
    (m.setLk j v).lk i = v ∨ (m.setLk j v).lk i = m.lk i := by
  simp only [TMem.lk, TMem.setLk, List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> simp_all

theorem TMem.lk_eq_of_lock {m m' : TMem} (h : m'.lock = m.lock) (i : ℕ) : m'.lk i = m.lk i := by
  simp [TMem.lk, h]

theorem TMem.setLk_length {m : TMem} {j v : ℕ} : (m.setLk j v).lock.length = m.lock.length := by
  simp [TMem.setLk]

/-! ## The invariant -/

/-- The processes other than `p` with a pending write to a lock holding `p` (each such write
destroys one of `p`'s locks). -/
def dest (m : TMem) (pc : ℕ → TLoc) (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun r => r ≠ p ∧ pendOn m p (pc r) = true)

/-- The processes other than `p` that may still win while `p` holds: those about to write `turn`
(line 2) and the competing process whose identifier is in `turn`. -/
def live (m : TMem) (pc : ℕ → TLoc) (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter
    (fun r => r ≠ p ∧ (pc r = .l2 ∨ (m.turn = r ∧ (pc r).comp = true)))

/-- The locks verified by `p` that no longer hold `p`. -/
def lost (m : TMem) (pc : ℕ → TLoc) (p : ℕ) : Finset ℕ :=
  ((pc p).cert n).filter (fun j => m.lk j ≠ p)

/-- `p` holds (lines 10–14, winner, start of `reset`) or is a candidate owning `turn`. -/
def Certified (m : TMem) (pc : ℕ → TLoc) (p : ℕ) : Prop :=
  (pc p).hold = true ∨ (m.turn = p ∧ (pc p).cand = true)

/-- The inductive invariant of the corrected algorithm. -/
structure Inv (m : TMem) (pc : ℕ → TLoc) : Prop where
  /-- `n − 1` locks. -/
  llen : m.lock.length = n - 1
  /-- Lock indices in program counters are in range. -/
  wf : ∀ r, 1 ≤ r → r ≤ n → (pc r).idxOK n
  /-- While some process holds, `turn ≠ 0`. -/
  h0 : ∀ p, 1 ≤ p → p ≤ n → (pc p).hold = true → m.turn ≠ 0
  /-- At most one process holds. -/
  h1 : ∀ p q, 1 ≤ p → p ≤ n → 1 ≤ q → q ≤ n → (pc p).hold = true → (pc q).hold = true → p = q
  /-- The counting invariant. -/
  ic : ∀ p, 1 ≤ p → p ≤ n → Certified m pc p →
    (lost n m pc p).card + (dest n m pc p).card + (live n m pc p).card ≤ n - 1
  /-- A candidate competing with a holder has checked no lock of the holder. -/
  il : ∀ p r, 1 ≤ p → p ≤ n → 1 ≤ r → r ≤ n → p ≠ r → (pc p).hold = true → m.turn = r →
    (pc r).cand = true → ∀ j ∈ (pc r).cert n, m.lk j ≠ p

/-! ## Preservation of the invariant -/

section Preserve
variable {n : ℕ} {m m' : TMem} {pc : ℕ → TLoc} {a : ℕ} {l' : TLoc}

theorem pendOn_iff {m : TMem} {p : ℕ} {l : TLoc} :
    pendOn m p l = true ↔ ∃ j, l.target = some j ∧ m.lk j = p := by
  unfold pendOn; cases l.target <;> simp

theorem TLoc.idx_of_target {l : TLoc} {j : ℕ} (h : l.idxOK n) (ht : l.target = some j) :
    1 ≤ j ∧ j ≤ n - 1 := by
  cases l <;> simp_all [TLoc.target, TLoc.idxOK]

theorem TLoc.one_le_of_mem_cert {l : TLoc} {i : ℕ} (h : i ∈ l.cert n) : 1 ≤ i := by
  cases l <;> simp [TLoc.cert] at h <;> omega

theorem TLoc.cert_of_hold {l : TLoc} (h : l.hold = true) : l.cert n = Finset.Icc 1 (n - 1) := by
  cases l <;> simp_all [TLoc.hold, TLoc.cert]

theorem dest_live_le {p : ℕ} (hp1 : 1 ≤ p) (hp2 : p ≤ n) (ht : m.turn = p) :
    (dest n m pc p).card + (live n m pc p).card ≤ n - 1 := by
  rw [← Finset.card_union_of_disjoint]
  · calc (dest n m pc p ∪ live n m pc p).card ≤ ((Finset.Icc 1 n).erase p).card := by
          apply Finset.card_le_card
          intro r hr
          simp only [dest, live, Finset.mem_union, Finset.mem_filter] at hr
          rw [Finset.mem_erase]; rcases hr with h | h <;> exact ⟨h.2.1, h.1⟩
      _ = n - 1 := by rw [Finset.card_erase_of_mem (by simp; omega)]; simp
  · rw [Finset.disjoint_left]
    intro r h1 h2
    simp only [dest, live, Finset.mem_filter] at h1 h2
    obtain ⟨_, hne, hpend⟩ := h1
    obtain ⟨_, _, h | ⟨h, _⟩⟩ := h2
    · simp [h, pendOn, TLoc.target] at hpend
    · exact hne (h.symm.trans ht)

theorem dest_congr {m m' : TMem} {pc pc' : ℕ → TLoc} {p : ℕ} (hlk : ∀ i, m'.lk i = m.lk i)
    (hpc : ∀ r, r ≠ p → pc' r = pc r) : dest n m' pc' p = dest n m pc p := by
  unfold dest pendOn
  refine Finset.filter_congr (fun r _ => ?_)
  by_cases hr : r = p
  · simp [hr]
  · rw [hpc r hr]; cases (pc r).target <;> simp [hlk]

theorem live_congr {m m' : TMem} {pc pc' : ℕ → TLoc} {p : ℕ} (ht : m'.turn = m.turn)
    (hpc : ∀ r, r ≠ p → pc' r = pc r) : live n m' pc' p = live n m pc p := by
  unfold live
  refine Finset.filter_congr (fun r _ => ?_)
  by_cases hr : r = p
  · simp [hr]
  · rw [hpc r hr, ht]

variable (I : Inv n m pc) (ha1 : 1 ≤ a) (ha2 : a ≤ n)
  (hm : (tstep n true a m (pc a)).1 = m') (hl : (tstep n true a m (pc a)).2 = l')
include I ha1 ha2 hm hl

omit ha1 ha2 in
theorem Inv.step_llen : m'.lock.length = n - 1 := by
  rcases step_lock hm hl with h | ⟨j, -, -, h | h⟩
  · rw [h, I.llen]
  all_goals rw [h, TMem.setLk_length, I.llen]

theorem Inv.step_wf (hn : 2 ≤ n) :
    ∀ r, 1 ≤ r → r ≤ n → (Function.update pc a l' r).idxOK n := by
  intro r h1 h2
  by_cases hr : r = a
  · subst hr; rw [Function.update_self]; exact step_idx hm hl hn (I.wf r h1 h2)
  · rw [Function.update_of_ne hr]; exact I.wf r h1 h2

theorem Inv.no_new_hold {p : ℕ} (hp1 : 1 ≤ p) (hp2 : p ≤ n) (hpa : p ≠ a)
    (hp : (pc p).hold = true) (h' : l'.hold = true) : False := by
  obtain ⟨-, -, hh | ⟨hx, ht⟩⟩ := step_hold hm hl h'
  · exact hpa (I.h1 p a hp1 hp2 ha1 ha2 hp hh)
  · have hil := I.il p a hp1 hp2 ha1 ha2 hpa hp ht (by rw [hx]; rfl)
    rw [hx] at hil
    have hlost : (lost n m pc p).card = n - 1 := by
      simp only [lost, TLoc.cert_of_hold hp]
      rw [Finset.filter_true_of_mem (s := Finset.Icc 1 (n - 1)) (fun j hj => hil j hj)]; simp
    have hic := I.ic p hp1 hp2 (Or.inl hp)
    have hlive : a ∈ live n m pc p := by
      simp only [live, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨ha1, ha2⟩, Ne.symm hpa, Or.inr ⟨ht, by rw [hx]; rfl⟩⟩
    have := Finset.card_pos.mpr ⟨a, hlive⟩
    omega

theorem Inv.step_h1 : ∀ p q, 1 ≤ p → p ≤ n → 1 ≤ q → q ≤ n →
    (Function.update pc a l' p).hold = true → (Function.update pc a l' q).hold = true →
    p = q := by
  intro p q hp1 hp2 hq1 hq2 hp hq
  by_cases hpa : p = a <;> by_cases hqa : q = a
  · rw [hpa, hqa]
  · subst hpa; rw [Function.update_self] at hp; rw [Function.update_of_ne hqa] at hq
    exact (I.no_new_hold ha1 ha2 hm hl hq1 hq2 hqa hq hp).elim
  · subst hqa; rw [Function.update_self] at hq; rw [Function.update_of_ne hpa] at hp
    exact (I.no_new_hold ha1 ha2 hm hl hp1 hp2 hpa hp hq).elim
  · rw [Function.update_of_ne hpa] at hp; rw [Function.update_of_ne hqa] at hq
    exact I.h1 p q hp1 hp2 hq1 hq2 hp hq

theorem Inv.step_h0 : ∀ p, 1 ≤ p → p ≤ n → (Function.update pc a l' p).hold = true →
    m'.turn ≠ 0 := by
  intro p hp1 hp2 hp
  by_cases hpa : p = a
  · subst hpa; rw [Function.update_self] at hp
    obtain ⟨-, ht, hh | ⟨-, ht'⟩⟩ := step_hold hm hl hp
    · rw [ht]; exact I.h0 p hp1 hp2 hh
    · rw [ht, ht']; omega
  · rw [Function.update_of_ne hpa] at hp
    rcases step_turn hm hl with ht | ⟨-, ht⟩ | ⟨hr, -⟩
    · rw [ht]; exact I.h0 p hp1 hp2 hp
    · rw [ht]; omega
    · exact absurd (I.h1 p a hp1 hp2 ha1 ha2 hp (by rw [hr]; rfl)) hpa

theorem Inv.step_il : ∀ p r, 1 ≤ p → p ≤ n → 1 ≤ r → r ≤ n → p ≠ r →
    (Function.update pc a l' p).hold = true → m'.turn = r →
    (Function.update pc a l' r).cand = true →
    ∀ j ∈ (Function.update pc a l' r).cert n, m'.lk j ≠ p := by
  intro p r hp1 hp2 hr1 hr2 hpr hp ht hc j hj
  by_cases hpa : p = a
  · subst hpa
    rw [Function.update_self] at hp
    rw [Function.update_of_ne (Ne.symm hpr)] at hc hj
    obtain ⟨hlk, ht', hh | ⟨-, ht''⟩⟩ := step_hold hm hl hp
    · rw [TMem.lk_eq_of_lock hlk]
      exact I.il p r hp1 hp2 hr1 hr2 hpr hh (ht' ▸ ht) hc j hj
    · exact absurd (ht''.symm.trans (ht'.symm.trans ht)) hpr
  · rw [Function.update_of_ne hpa] at hp
    by_cases hra : r = a
    · subst hra
      rw [Function.update_self] at hc hj
      rcases step_cand hm hl hc ht with he | ⟨hc0, hme, hsub⟩
      · rw [he] at hj; simp at hj
      · subst hme
        rcases hsub j hj with hj' | hj'
        · exact I.il p r hp1 hp2 hr1 hr2 hpr hp ht hc0 j hj'
        · rw [hj']; exact Ne.symm hpr
    · rw [Function.update_of_ne hra] at hc hj
      have ht0 : m.turn = r := by
        rcases step_turn hm hl with h | ⟨-, h⟩ | ⟨-, h⟩
        · rw [← h, ht]
        · exact absurd (h.symm.trans ht) (Ne.symm hra)
        · omega
      have := I.il p r hp1 hp2 hr1 hr2 hpr hp ht0 hc j hj
      rcases step_lock hm hl with h | ⟨k, -, -, h | h⟩
      · rw [TMem.lk_eq_of_lock h]; exact this
      · rw [h]
        rcases TMem.lk_setLk (m := m) (i := j) (j := k) (v := a) with h' | h' <;> rw [h']
        · exact Ne.symm hpa
        · exact this
      · rw [h]
        rcases TMem.lk_setLk (m := m) (i := j) (j := k) (v := 0) with h' | h' <;> rw [h']
        · omega
        · exact this

theorem Inv.step_lost_dest {p : ℕ} (hp1 : 1 ≤ p) (hpa : p ≠ a) :
    (lost n m' (Function.update pc a l') p).card + (dest n m' (Function.update pc a l') p).card ≤
      (lost n m pc p).card + (dest n m pc p).card := by
  have hpp : Function.update pc a l' p = pc p := Function.update_of_ne hpa _ _
  rcases step_lock hm hl with hlk | ⟨j, htj, htj', hset⟩
  · have e1 : lost n m' (Function.update pc a l') p = lost n m pc p := by
      simp only [lost, hpp, TMem.lk_eq_of_lock hlk]
    have e2 : dest n m' (Function.update pc a l') p ⊆ dest n m pc p := by
      intro r hr
      simp only [dest, Finset.mem_filter, pendOn_iff] at hr ⊢
      obtain ⟨hr1, hrp, k, hk, hkp⟩ := hr
      by_cases hra : r = a
      · exfalso; subst hra; rw [Function.update_self] at hk
        obtain ⟨hme, h0 | h0⟩ := step_target hm hl hk <;> rw [hme] at hkp
        · omega
        · exact hpa (hkp.symm.trans h0)
      · rw [Function.update_of_ne hra] at hk
        exact ⟨hr1, hrp, k, hk, by rwa [TMem.lk_eq_of_lock hlk] at hkp⟩
    rw [e1]; have := Finset.card_le_card e2; omega
  · obtain ⟨v, hv, hvp⟩ : ∃ v, m' = m.setLk j v ∧ v ≠ p := by
      rcases hset with h | h
      · exact ⟨a, h, Ne.symm hpa⟩
      · exact ⟨0, h, by omega⟩
    have hj := TLoc.idx_of_target (I.wf a ha1 ha2) htj
    have hlkj : m'.lk j = v := by
      rw [hv]; exact TMem.lk_setLk_self hj.1 (by rw [I.llen]; exact hj.2)
    have hlki : ∀ i, 1 ≤ i → i ≠ j → m'.lk i = m.lk i := fun i hi hij => by
      rw [hv]; exact TMem.lk_setLk_ne hi hj.1 hij
    have hd : dest n m' (Function.update pc a l') p ⊆ (dest n m pc p).erase a := by
      intro r hr
      simp only [dest, Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc, pendOn_iff] at hr ⊢
      obtain ⟨hr1, hrp, k, hk, hkp⟩ := hr
      by_cases hra : r = a
      · subst hra; rw [Function.update_self, htj'] at hk; simp at hk
      · rw [Function.update_of_ne hra] at hk
        have hk1 := (TLoc.idx_of_target (I.wf r hr1.1 hr1.2) hk).1
        have hkj : k ≠ j := by rintro rfl; exact hvp (hlkj.symm.trans hkp)
        exact ⟨hra, hr1, hrp, k, hk, by rwa [hlki k hk1 hkj] at hkp⟩
    have c3 := Finset.card_le_card hd
    by_cases hjp : m.lk j = p
    · have ha_mem : a ∈ dest n m pc p := by
        simp only [dest, Finset.mem_filter, Finset.mem_Icc, pendOn_iff]
        exact ⟨⟨ha1, ha2⟩, Ne.symm hpa, j, htj, hjp⟩
      have hl' : lost n m' (Function.update pc a l') p ⊆ insert j (lost n m pc p) := by
        intro i hi
        simp only [lost, hpp, Finset.mem_filter, Finset.mem_insert] at hi ⊢
        by_cases hij : i = j
        · exact Or.inl hij
        · exact Or.inr ⟨hi.1, by rw [← hlki i (TLoc.one_le_of_mem_cert hi.1) hij]; exact hi.2⟩
      have c1 := Finset.card_le_card hl'
      have c2 := Finset.card_insert_le j (lost n m pc p)
      have c4 := Finset.card_erase_of_mem ha_mem
      have c5 := Finset.card_pos.mpr ⟨a, ha_mem⟩
      omega
    · have hl' : lost n m' (Function.update pc a l') p ⊆ lost n m pc p := by
        intro i hi
        simp only [lost, hpp, Finset.mem_filter] at hi ⊢
        refine ⟨hi.1, ?_⟩
        by_cases hij : i = j
        · subst hij; exact hjp
        · rw [← hlki i (TLoc.one_le_of_mem_cert hi.1) hij]; exact hi.2
      have c1 := Finset.card_le_card hl'
      have c4 := Finset.card_erase_le (s := dest n m pc p) (a := a)
      omega

omit I ha2 in
theorem Inv.step_live_sub {p : ℕ} (hpa : p ≠ a) (hturn : m.turn ≠ 0) :
    live n m' (Function.update pc a l') p ⊆ live n m pc p := by
  intro r hr
  simp only [live, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
  obtain ⟨hr1, hrp, h⟩ := hr
  refine ⟨hr1, hrp, ?_⟩
  by_cases hra : r = a
  · subst hra; rw [Function.update_self] at h
    rcases h with h | ⟨ht, hcomp⟩
    · exact absurd (step_l2 hm hl h).2.2 hturn
    · rcases step_turn hm hl with h' | ⟨h', -⟩ | ⟨-, h'⟩
      · rcases step_comp hm hl hcomp with hc | hc
        · exact Or.inr ⟨h'.symm.trans ht, hc⟩
        · exact Or.inl hc
      · exact Or.inl h'
      · omega
  · rw [Function.update_of_ne hra] at h
    rcases h with h | ⟨ht, hcomp⟩
    · exact Or.inl h
    · refine Or.inr ⟨?_, hcomp⟩
      rcases step_turn hm hl with h' | ⟨-, h'⟩ | ⟨-, h'⟩
      · exact h'.symm.trans ht
      · exact absurd (h'.symm.trans ht) (Ne.symm hra)
      · omega

theorem Inv.step_ic : ∀ p, 1 ≤ p → p ≤ n → Certified m' (Function.update pc a l') p →
    (lost n m' (Function.update pc a l') p).card + (dest n m' (Function.update pc a l') p).card +
      (live n m' (Function.update pc a l') p).card ≤ n - 1 := by
  intro p hp1 hp2 hcert
  by_cases hpa : p = a
  · subst hpa
    have hpc : ∀ r, r ≠ p → Function.update pc p l' r = pc r :=
      fun r hr => Function.update_of_ne hr _ _
    rcases hcert with hh | ⟨ht, hc⟩
    · rw [Function.update_self] at hh
      obtain ⟨hlk, ht', hc0⟩ := step_hold hm hl hh
      have hcert0 : Certified m pc p := by
        rcases hc0 with h | ⟨hx, htp⟩
        · exact Or.inl h
        · exact Or.inr ⟨htp, by rw [hx]; rfl⟩
      have hce : (pc p).cert n = Finset.Icc 1 (n - 1) := by
        rcases hc0 with h | ⟨hx, -⟩
        · exact TLoc.cert_of_hold h
        · rw [hx]; rfl
      have e1 : lost n m' (Function.update pc p l') p = lost n m pc p := by
        simp only [lost, Function.update_self, TLoc.cert_of_hold hh, hce, TMem.lk_eq_of_lock hlk]
      rw [e1, dest_congr (TMem.lk_eq_of_lock hlk) hpc, live_congr ht' hpc]
      exact I.ic p hp1 hp2 hcert0
    · rw [Function.update_self] at hc
      rcases step_cand hm hl hc ht with he | ⟨hc0, hme, hsub⟩
      · have e1 : (lost n m' (Function.update pc p l') p).card = 0 := by
          simp [lost, he]
        have := dest_live_le (pc := Function.update pc p l') hp1 hp2 ht
        omega
      · rw [hme] at ht ⊢
        have hsub' : lost n m (Function.update pc p l') p ⊆ lost n m pc p := by
          intro i hi
          simp only [lost, Function.update_self, Finset.mem_filter] at hi ⊢
          rcases hsub i hi.1 with h | h
          · exact ⟨h, hi.2⟩
          · exact absurd h hi.2
        rw [dest_congr (fun _ => rfl) hpc, live_congr rfl hpc]
        have := Finset.card_le_card hsub'
        have := I.ic p hp1 hp2 (Or.inr ⟨ht, hc0⟩)
        omega
  · have hpp : Function.update pc a l' p = pc p := Function.update_of_ne hpa _ _
    have hcert0 : Certified m pc p := by
      rcases hcert with hh | ⟨ht, hc⟩
      · rw [hpp] at hh; exact Or.inl hh
      · rw [hpp] at hc
        refine Or.inr ⟨?_, hc⟩
        rcases step_turn hm hl with h' | ⟨-, h'⟩ | ⟨-, h'⟩
        · exact h'.symm.trans ht
        · exact absurd (h'.symm.trans ht) (Ne.symm hpa)
        · omega
    have hturn : m.turn ≠ 0 := by
      rcases hcert0 with hh | ⟨ht, -⟩
      · exact I.h0 p hp1 hp2 hh
      · omega
    have h1 := I.step_lost_dest ha1 ha2 hm hl hp1 hpa
    have h2 := Finset.card_le_card (Inv.step_live_sub ha1 hm hl hpa hturn)
    have h3 := I.ic p hp1 hp2 hcert0
    omega

/-- One step of a process preserves the invariant. -/
theorem Inv.step (hn : 2 ≤ n) : Inv n m' (Function.update pc a l') :=
  ⟨I.step_llen hm hl, I.step_wf ha1 ha2 hm hl hn, I.step_h0 ha1 ha2 hm hl,
    I.step_h1 ha1 ha2 hm hl, I.step_ic ha1 ha2 hm hl, I.step_il ha1 ha2 hm hl⟩

end Preserve

/-! ## From the list model to the invariant -/

/-- The program counter of process `r` in a global state (`idle` for non-processes). -/
def pcOf (s : TSys) (r : ℕ) : TLoc := if r = 0 then .idle else s.2.getD (r - 1) .idle

theorem tsysStep_eq {s : TSys} (hlen : s.2.length = n) {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ n) :
    (tsysStep n true s a).1 = (tstep n true a s.1 (pcOf s a)).1 ∧
    (tsysStep n true s a).2.length = n ∧
    pcOf (tsysStep n true s a) = Function.update (pcOf s) a (tstep n true a s.1 (pcOf s a)).2 := by
  have hpa : pcOf s a = s.2.getD (a - 1) .idle := by simp [pcOf]; omega
  have hst : tsysStep n true s a = ((tstep n true a s.1 (pcOf s a)).1,
      s.2.set (a - 1) (tstep n true a s.1 (pcOf s a)).2) := by
    simp only [tsysStep, ha1, ha2, and_self, ↓reduceIte, hpa]
  rw [hst]
  refine ⟨rfl, by simp [hlen], ?_⟩
  funext r
  simp only [pcOf, Function.update_apply, List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> simp_all <;> omega

theorem inv_init (n : ℕ) : Inv n (tinit n).1 (pcOf (tinit n)) := by
  have hpc : ∀ r, pcOf (tinit n) r = .idle := by
    intro r; simp only [pcOf, tinit]
    split_ifs
    · rfl
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split_ifs <;> rfl
  refine ⟨by simp [tinit], ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hpc, TLoc.idxOK, TLoc.hold, Certified, TLoc.cand]

theorem inv_trun (hn : 2 ≤ n) (σ : List ℕ) :
    (trun n true σ).2.length = n ∧ Inv n (trun n true σ).1 (pcOf (trun n true σ)) := by
  unfold trun
  suffices h : ∀ s : TSys, s.2.length = n → Inv n s.1 (pcOf s) →
      (σ.foldl (tsysStep n true) s).2.length = n ∧
        Inv n (σ.foldl (tsysStep n true) s).1 (pcOf (σ.foldl (tsysStep n true) s)) from
    h _ (by simp [tinit]) (inv_init n)
  induction σ with
  | nil => exact fun s h1 h2 => ⟨h1, h2⟩
  | cons a σ ih =>
    intro s h1 h2
    simp only [List.foldl_cons]
    apply ih
    · by_cases ha : 1 ≤ a ∧ a ≤ n
      · exact (tsysStep_eq n h1 ha.1 ha.2).2.1
      · simpa [tsysStep, ha] using h1
    · by_cases ha : 1 ≤ a ∧ a ≤ n
      · obtain ⟨e1, -, e3⟩ := tsysStep_eq n h1 ha.1 ha.2
        rw [e3]
        exact h2.step ha.1 ha.2 e1.symm rfl hn
      · simpa [tsysStep, ha] using h2

theorem count_won_le_one (l : List TLoc)
    (h : ∀ i j (hi : i < l.length) (hj : j < l.length), l[i] = .won → l[j] = .won → i = j) :
    l.count .won ≤ 1 := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have ht : ∀ i j (hi : i < t.length) (hj : j < t.length), t[i] = .won → t[j] = .won → i = j :=
      fun i j hi hj h1 h2 => by
        have := h (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by simpa using h1)
          (by simpa using h2)
        omega
    rw [List.count_cons]
    by_cases hx : x = .won
    · subst hx
      have : t.count .won = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        obtain ⟨k, hk, hk'⟩ := List.getElem_of_mem hmem
        have := h 0 (k + 1) (by simp) (by simp; omega) rfl (by simpa using hk')
        omega
      simp [this]
    · have := ih ht
      simp [hx, this]

/-- **Theorem 3.2 of [Taubenfeld 2012], for the corrected algorithm** (line 10 also loses when
`locked = 0`): for every number `n ≥ 2` of processes, every (well-structured) run has at most
one winner. -/
theorem theorem_3_2_fixed (n : ℕ) (hn : 2 ≤ n) : Theorem32 n true := by
  intro σ
  obtain ⟨hlen, I⟩ := inv_trun n hn σ
  unfold winners
  apply count_won_le_one
  intro i j hi hj h1 h2
  have hpc : ∀ k (hk : k < (trun n true σ).2.length),
      pcOf (trun n true σ) (k + 1) = (trun n true σ).2[k] := by
    intro k hk; simp [pcOf, List.getD_eq_getElem?_getD, hk]
  have := I.h1 (i + 1) (j + 1) (by omega) (by omega) (by omega) (by omega)
    (by rw [hpc i hi, h1]; rfl) (by rw [hpc j hj, h2]; rfl)
  omega

/-- Non-vacuity: a solo run of the corrected algorithm has a winner. -/
theorem fixed_solo_win : winners (trun 2 true (List.replicate 10 1)) = 1 := by decide

/-- Non-vacuity for `n = 3`. -/
theorem fixed_solo_win_3 : winners (trun 3 true (List.replicate 13 2)) = 1 := by decide

end Podc.CloserLookFT.TAS
