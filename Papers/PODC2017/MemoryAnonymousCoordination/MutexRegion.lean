import Papers.PODC2017.MemoryAnonymousCoordination.MutexDFInv

/-!
# Figure 1: at most two give-ups without progress

In the *region* where no process holds the lock or is exiting (every process is in the remainder
section, active (lines 2–3) or passive (lines 5–8)), we show that a weak collect ("give up",
line 4 with fewer than `⌈m/2⌉` own entries) can happen at most twice:

* `GInv` (*clean race*): nobody is passive, a scanning process has passed fewer than `⌈m/2⌉`
  zeros, and a collecting process either is guaranteed to see `⌈m/2⌉` own values, or has read
  fewer than `⌈m/2⌉` zeros in total (read or still to be read) and every non-own non-zero value it
  has read is still in place. `GInv` holds after a passive process leaves the wait loop
  (`GInv.of_leaveW`) and is preserved by steps other than weak collects (`GInv.step`).
* A weak collect from `GInv` leads to `DInv q p` (`GInv.weak`): `p` is passive and `q` owns a
  register `p` will never erase; then `p` never leaves the wait loop again and nobody gives up
  any more (`DInv.step`, `DInv.not_weak`).
* By `DFInv.not_weak_of_pas`, between two weak collects the first loser leaves the wait loop.
-/

set_option linter.unusedSectionVars false

namespace Podc.MemoryAnonymousCoordination.Mutex

open Cslib.SharedMemory Finset

variable {P : Type} [DecidableEq P] {m : ℕ} (π : P → Equiv.Perm (Fin m))

/-- The region: remainder, active or passive. -/
def InReg (l : Loc P) : Prop := l = .rem ∨ Act l ∨ Pas l

/-- The register `q` is about to write its identifier to (line 2). -/
def wtgt (q : P) : Loc P → Finset (Fin m)
  | .scanW j => univ.filter (fun r => posn π q r = j)
  | _ => ∅

/-- A clean race. -/
structure GInv (loc : P → Loc P) (M : Fin m → Option P) : Prop where
  noPas : ∀ p, ¬ Pas (loc p)
  scan : ∀ p j, (loc p = .scan j ∨ loc p = .scanW j) →
    #(univ.filter (fun r => posn π p r < j ∧ M r = none)) + 1 ≤ thr m
  coll : ∀ p q, p ≠ q → ∀ vs, loc p = .coll vs →
    thr m ≤ vs.count (some p) + #(univ.filter (fun r => vs.length ≤ posn π p r ∧
      M r = some p ∧ r ∉ wtgt π q (loc q))) ∨
    (vs.count none + #(univ.filter (fun r => vs.length ≤ posn π p r ∧ M r = none)) + 1 ≤ thr m ∧
      vs.length ≤ vs.count (some p) + vs.count none +
        #(univ.filter (fun r => posn π p r < vs.length ∧ M r = some q)))

/-- `q` has won: `p` is passive and `q` owns a register that `p` never erases and that `p`'s
current wait pass has not read yet. -/
def DInv (q p : P) (loc : P → Loc P) (M : Fin m → Option P) : Prop :=
  Pas (loc p) ∧ ¬ Pas (loc q) ∧ (∃ r, M r = some q ∧ r ∉ tgt π p (loc p)) ∧
    ∀ j, loc p = .wait j true → ∃ r, j ≤ posn π p r ∧ M r = some q

variable {π}

section Step

variable {loc : P → Loc P} {M M' : Fin m → Option P} {x : P} {l' : Loc P}

lemma thr_pos (hm : 1 ≤ m) : 1 ≤ thr m := by unfold thr; omega

/-- A non-passive process in the region only writes its own identifier. -/
lemma TStep.write_own (hs : TStep m π x (loc x) M l' M') (hr : InReg (loc x))
    (hp : ¬ Pas (loc x)) (r : Fin m) : M' r = M r ∨ M' r = some x := by
  generalize hlx : loc x = lx at hs
  cases hs with
  | @scanW j _ hj =>
    by_cases h : r = π x ⟨j, hj⟩
    · subst h; simp
    · left; exact Function.update_of_ne h _ _
  | rstW => simp [Pas, hlx] at hp
  | exit => rw [hlx] at hr; simp [InReg, Act, Pas] at hr
  | _ => exact Or.inl rfl

lemma TStep.zero_of_write_own (hs : TStep m π x (loc x) M l' M') (hr : InReg (loc x))
    (hp : ¬ Pas (loc x)) {r : Fin m} (h : M' r = none) : M r = none := by
  rcases hs.write_own hr hp r with h1 | h1 <;> simp_all

lemma TStep.some_of_write_own (hs : TStep m π x (loc x) M l' M') (hr : InReg (loc x))
    (hp : ¬ Pas (loc x)) {r : Fin m} {c : P} (h : M r = some c) : M' r = some c ∨ M' r = some x :=
  by rcases hs.write_own hr hp r with h1 | h1 <;> simp_all

lemma not_act_and_pas {l : Loc P} (h1 : Act l) (h2 : Pas l) : False := by
  cases l <;> simp [Act, Pas] at h1 h2

/-- A step from a passive to an active local state leaves the wait loop. -/
lemma TStep.leaveW (hs : TStep m π x (loc x) M l' M') (hx : Pas (loc x)) (hx' : Act l') :
    (∃ j, loc x = .wait j true) ∧ l' = .scan 0 ∧ M' = M := by
  generalize hlx : loc x = lx at hs
  cases hs with
  | @wait j z _ hj =>
    rcases afterWait_cases j z (M (π x ⟨j, hj⟩)) with ⟨z', h1⟩ | h1 | h1 <;> rw [h1] at hx' ⊢ <;>
      simp only [Act] at hx'
    refine ⟨⟨j, ?_⟩, rfl, rfl⟩
    unfold afterWait at h1; split_ifs at h1 with h2 h3
    simp only [Bool.and_eq_true] at h3; rw [h3.1]
  | @rst1 j _ hj _ =>
    rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hx' <;>
      simp [Act] at hx'
  | @rstW j _ hj =>
    rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hx' <;>
      simp [Act] at hx'
  | rst0 => simp [Act] at hx'
  | idle => exact (not_act_and_pas hx' (hlx ▸ hx)).elim
  | _ => simp [Pas, hlx] at hx

/-- A step from a non-passive to a passive local state is a weak collect. -/
lemma TStep.weak_of_pas (hs : TStep m π x (loc x) M l' M') (hx : ¬ Pas (loc x)) (hx' : Pas l') :
    ∃ vs, loc x = .coll vs ∧ l' = .rst 0 := by
  generalize hlx : loc x = lx at hs
  cases hs with
  | @coll vs _ hj =>
    rcases afterColl_cases (m := m) x (vs ++ [M (π x ⟨vs.length, hj⟩)]) with
      ⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at hx' ⊢ <;> simp [Pas] at hx'
    exact ⟨vs, rfl, rfl⟩
  | @scan1 j _ hj _ =>
    rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hx' <;>
      simp [Pas] at hx'
  | @scanW j _ hj =>
    rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hx' <;>
      simp [Pas] at hx'
  | @exit j _ hj =>
    rcases nextExit_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hx' <;>
      simp [Pas] at hx'
  | idle => exact (hx (hlx ▸ hx')).elim
  | scan0 => simp [Pas] at hx'
  | retLock => simp [Pas] at hx'
  | retUnlock => simp [Pas] at hx'
  | invLock => simp [Pas] at hx'
  | invUnlock => simp [Pas] at hx'
  | _ => simp [Pas, hlx] at hx

/-- **W**: leaving the wait loop starts a clean race. -/
lemma GInv.of_leaveW (hP : ∀ a b c : P, a ≠ b → c = a ∨ c = b) (hm : 1 ≤ m)
    (hD : DFInv π loc M) (hs : TStep m π x (loc x) M l' M') (hx : Pas (loc x)) (hx' : Act l') :
    GInv π (Function.update loc x l') M' := by
  obtain ⟨⟨jw, hw⟩, rfl, rfl⟩ := hs.leaveW hx hx'
  refine ⟨fun p => ?_, fun p j hp => ?_, fun p q hpq vs hp => ?_⟩
  · by_cases hpx : p = x
    · subst hpx; simp [Pas]
    · rw [Function.update_of_ne hpx]; exact hD.nbp x p (Ne.symm hpx) hx
  · by_cases hpx : p = x
    · subst hpx
      simp only [Function.update_self] at hp
      rcases hp with hp | hp <;> cases hp
      simpa using thr_pos hm
    · rw [Function.update_of_ne hpx] at hp
      have := hD.phi x p (Ne.symm hpx) hx
      rcases hp with hp | hp <;> simp only [hp, gapsS] at this <;> omega
  · by_cases hpx : p = x
    · subst hpx; simp at hp
    · rw [Function.update_of_ne hpx] at hp
      have hq : q = x := (hP p x q hpx).resolve_left (Ne.symm hpq)
      subst hq
      left
      have := hD.R q p (Ne.symm hpx) hx vs hp
      simpa [hw, tgt, wtgt] using this

/-- Registers other than the pending write target of a non-passive process in the region are not
changed by its step. -/
lemma TStep.mem_eq_of_not_wtgt (hs : TStep m π x (loc x) M l' M') (hr : InReg (loc x))
    (hp : ¬ Pas (loc x)) {r : Fin m} (h : r ∉ wtgt π x (loc x)) : M' r = M r := by
  generalize hlx : loc x = lx at hs
  cases hs with
  | @scanW j _ hj =>
    have : r ≠ π x ⟨j, hj⟩ := fun h' => h (by rw [hlx, h']; simp [wtgt])
    exact Function.update_of_ne this _ _
  | rstW => simp [Pas, hlx] at hp
  | exit => rw [hlx] at hr; simp [InReg, Act, Pas] at hr
  | _ => rfl

/-- The new pending write target of `x` holds `0` or was already the target. -/
lemma TStep.wtgt_new (hs : TStep m π x (loc x) M l' M') {r : Fin m} (h : r ∈ wtgt π x l') :
    M r = none ∨ r ∈ wtgt π x (loc x) := by
  generalize hlx : loc x = lx at hs
  cases hs with
  | @scan0 j _ hj h0 =>
    simp only [wtgt, mem_filter, mem_univ, true_and] at h
    left; rw [eq_of_posn_eq π hj h]; exact h0
  | idle => exact Or.inr h
  | @scan1 j _ hj _ =>
    rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at h <;>
      simp [wtgt] at h
  | @scanW j _ hj =>
    rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at h <;>
      simp [wtgt] at h
  | @coll vs _ hj =>
    rcases afterColl_cases (m := m) x (vs ++ [M (π x ⟨vs.length, hj⟩)]) with
      ⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at h <;> simp [wtgt] at h
  | @rst1 j _ hj _ =>
    rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at h <;>
      simp [wtgt] at h
  | @rstW j _ hj =>
    rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at h <;>
      simp [wtgt] at h
  | @exit j _ hj =>
    rcases nextExit_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at h <;>
      simp [wtgt] at h
  | @wait j z _ hj =>
    rcases afterWait_cases j z (M (π x ⟨j, hj⟩)) with ⟨z', h1⟩ | h1 | h1 <;> rw [h1] at h <;>
      simp [wtgt] at h
  | _ => simp [wtgt] at h

/-- Splitting the unread part of a collect at the register just read. -/
lemma card_unread_split (a : P) (vs : List (Option P)) (hj : vs.length < m)
    (Q : Fin m → Prop) [DecidablePred Q] :
    #(univ.filter (fun r => vs.length ≤ posn π a r ∧ Q r)) =
      #(univ.filter (fun r => vs.length + 1 ≤ posn π a r ∧ Q r)) +
        if Q (π a ⟨vs.length, hj⟩) then 1 else 0 := by
  have : univ.filter (fun r => vs.length ≤ posn π a r ∧ Q r) =
      univ.filter (fun r => vs.length + 1 ≤ posn π a r ∧ Q r) ∪
        (if Q (π a ⟨vs.length, hj⟩) then {π a ⟨vs.length, hj⟩} else ∅) := by
    ext r
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hr0 : posn π a r = vs.length
      · have := eq_of_posn_eq π hj hr0; subst this; right; simp [h2]
      · left; exact ⟨by omega, h2⟩
    · rintro (⟨h1, h2⟩ | h1)
      · exact ⟨by omega, h2⟩
      · split_ifs at h1 with h2
        · simp at h1; subst h1; simp [h2]
        · simp at h1
  rw [this]
  split_ifs with h1
  · rw [card_union_of_disjoint (by simp), card_singleton]
  · simp

/-- Splitting the read part of a collect at the register just read. -/
lemma card_read_split (a : P) (vs : List (Option P)) (hj : vs.length < m)
    (Q : Fin m → Prop) [DecidablePred Q] :
    #(univ.filter (fun r => posn π a r < vs.length + 1 ∧ Q r)) =
      #(univ.filter (fun r => posn π a r < vs.length ∧ Q r)) +
        if Q (π a ⟨vs.length, hj⟩) then 1 else 0 := by
  have : univ.filter (fun r => posn π a r < vs.length + 1 ∧ Q r) =
      univ.filter (fun r => posn π a r < vs.length ∧ Q r) ∪
        (if Q (π a ⟨vs.length, hj⟩) then {π a ⟨vs.length, hj⟩} else ∅) := by
    ext r
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hr0 : posn π a r = vs.length
      · have := eq_of_posn_eq π hj hr0; subst this; right; simp [h2]
      · left; exact ⟨by omega, h2⟩
    · rintro (⟨h1, h2⟩ | h1)
      · exact ⟨by omega, h2⟩
      · split_ifs at h1 with h2
        · simp at h1; subst h1; simp [h2]
        · simp at h1
  rw [this]
  split_ifs with h1
  · rw [card_union_of_disjoint (by simp), card_singleton]
  · simp

/-- **G1**: a clean race stays clean until somebody gives up. -/
lemma GInv.step (hP : ∀ a b c : P, a ≠ b → c = a ∨ c = b) (hm : 1 ≤ m) (hG : GInv π loc M)
    (hreg : InReg (loc x)) (hs : TStep m π x (loc x) M l' M')
    (hnw : ∀ vs, loc x = .coll vs → l' ≠ .rst 0) : GInv π (Function.update loc x l') M' := by
  have hxp := hG.noPas x
  refine ⟨fun p => ?_, fun p j hp => ?_, fun p q hpq vs hp => ?_⟩
  · by_cases hpx : p = x
    · subst hpx
      rw [Function.update_self]
      intro h'
      obtain ⟨vs, h1, h2⟩ := hs.weak_of_pas hxp h'
      exact hnw vs h1 h2
    · rw [Function.update_of_ne hpx]; exact hG.noPas p
  · by_cases hpx : p = x
    · subst hpx
      rw [Function.update_self] at hp
      generalize hlx : loc p = lx at hs
      cases hs with
      | @scan0 j₀ _ hj h0 =>
        rcases hp with hp | hp <;> cases hp
        exact hG.scan p j (Or.inl hlx)
      | @scan1 j₀ _ hj h0 =>
        rcases nextScan_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hp <;>
          rcases hp with hp | hp <;> cases hp
        refine le_trans (Nat.add_le_add_right (card_le_card fun r hr => ?_) 1)
          (hG.scan p j₀ (Or.inl hlx))
        simp only [mem_filter, mem_univ, true_and] at hr ⊢
        have : posn π p r ≠ j₀ := fun h' => h0 (by rw [← eq_of_posn_eq π hj h']; exact hr.2)
        exact ⟨by omega, hr.2⟩
      | @scanW j₀ _ hj =>
        rcases nextScan_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hp <;>
          rcases hp with hp | hp <;> cases hp
        refine le_trans (Nat.add_le_add_right (card_le_card fun r hr => ?_) 1)
          (hG.scan p j₀ (Or.inr hlx))
        simp only [mem_filter, mem_univ, true_and] at hr ⊢
        have hr0 : r ≠ π p ⟨j₀, hj⟩ := fun h' => by rw [h'] at hr; simp at hr
        rw [Function.update_of_ne hr0] at hr
        have : posn π p r ≠ j₀ := fun h' => hr0 (eq_of_posn_eq π hj h')
        exact ⟨by omega, hr.2⟩
      | @coll vs _ hj =>
        rcases afterColl_cases (m := m) p (vs ++ [M (π p ⟨vs.length, hj⟩)]) with
          ⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at hp <;>
          rcases hp with hp | hp <;> cases hp
        simpa using thr_pos hm
      | invLock =>
        rcases hp with hp | hp <;> cases hp
        simpa using thr_pos hm
      | idle => exact hG.scan p j (by rw [hlx]; exact hp)
      | @wait j₀ z _ hj => exact absurd (by rw [hlx]; trivial) hxp
      | rst0 => exact absurd (by rw [hlx]; trivial) hxp
      | rst1 => exact absurd (by rw [hlx]; trivial) hxp
      | rstW => exact absurd (by rw [hlx]; trivial) hxp
      | @exit j₀ _ hj =>
        rcases nextExit_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hp <;>
          rcases hp with hp | hp <;> cases hp
      | _ => rcases hp with hp | hp <;> cases hp
    · rw [Function.update_of_ne hpx] at hp
      refine le_trans (Nat.add_le_add_right (card_le_card fun r hr => ?_) 1) (hG.scan p j hp)
      simp only [mem_filter, mem_univ, true_and] at hr ⊢
      exact ⟨hr.1, hs.zero_of_write_own hreg hxp hr.2⟩
  · by_cases hpx : p = x
    · subst hpx
      rw [Function.update_self] at hp
      rw [Function.update_of_ne (Ne.symm hpq)]
      generalize hlx : loc p = lx at hs
      cases hs with
      | @scan1 j₀ _ hj h0 =>
        rcases nextScan_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨h2, h1⟩ <;> rw [h1] at hp <;>
          cases hp
        right
        refine ⟨?_, by simp⟩
        simp only [List.count_nil, List.length_nil, Nat.zero_le, true_and, zero_add]
        refine le_trans (Nat.add_le_add_right (card_le_card fun r hr => ?_) 1)
          (hG.scan p j₀ (Or.inl hlx))
        simp only [mem_filter, mem_univ, true_and] at hr ⊢
        have hr0 : r ≠ π p ⟨j₀, hj⟩ := fun h' => h0 (h' ▸ hr)
        exact ⟨posn_lt_of_ne hj h2 hr0, hr⟩
      | @scanW j₀ _ hj =>
        rcases nextScan_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨h2, h1⟩ <;> rw [h1] at hp <;>
          cases hp
        right
        refine ⟨?_, by simp⟩
        simp only [List.count_nil, List.length_nil, Nat.zero_le, true_and, zero_add]
        refine le_trans (Nat.add_le_add_right (card_le_card fun r hr => ?_) 1)
          (hG.scan p j₀ (Or.inr hlx))
        simp only [mem_filter, mem_univ, true_and] at hr ⊢
        have hr0 : r ≠ π p ⟨j₀, hj⟩ := fun h' => by rw [h'] at hr; simp at hr
        rw [Function.update_of_ne hr0] at hr
        exact ⟨posn_lt_of_ne hj h2 hr0, hr⟩
      | @coll vs₀ _ hj =>
        rcases afterColl_cases (m := m) p (vs₀ ++ [M (π p ⟨vs₀.length, hj⟩)]) with
          ⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at hp <;> cases hp
        have hsplit1 := card_unread_split (π := π) p vs₀ hj
          (fun r => M r = some p ∧ r ∉ wtgt π q (loc q))
        have hsplit2 := card_unread_split (π := π) p vs₀ hj (fun r => M r = none)
        have hsplit3 := card_read_split (π := π) p vs₀ hj (fun r => M r = some q)
        simp only [List.length_append, List.length_cons, List.length_nil, count_append_one]
        rcases hG.coll p q hpq vs₀ hlx with h1 | ⟨h1, h2⟩
        · left
          split_ifs at hsplit1 ⊢ with h3 h4 <;> simp_all <;> omega
        · right
          cases hv : M (π p ⟨vs₀.length, hj⟩) with
          | none => simp only [hv] at hsplit1 hsplit2 hsplit3 ⊢; simp at hsplit2 hsplit3 ⊢; omega
          | some c =>
            rcases hP p q c hpq with rfl | rfl
            · simp at hsplit2 hsplit3 ⊢; rw [hv] at hsplit2 hsplit3; simp at hsplit2 hsplit3
              omega
            · simp [hv, hpq.symm] at hsplit2 hsplit3 ⊢; omega
      | idle => exact hG.coll p q hpq vs (by rw [hlx]; exact hp)
      | @rst1 j₀ _ hj _ =>
        rcases nextRst_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hp <;>
          cases hp
      | @rstW j₀ _ hj =>
        rcases nextRst_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hp <;>
          cases hp
      | @exit j₀ _ hj =>
        rcases nextExit_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hp <;>
          cases hp
      | @wait j₀ z _ hj =>
        rcases afterWait_cases j₀ z (M (π p ⟨j₀, hj⟩)) with ⟨z', h1⟩ | h1 | h1 <;> rw [h1] at hp <;>
          cases hp
      | _ => cases hp
    · rw [Function.update_of_ne hpx] at hp
      have hq : q = x := (hP p x q hpx).resolve_left (Ne.symm hpq)
      subst hq
      rw [Function.update_self]
      rcases hG.coll p q hpq vs hp with h1 | ⟨h1, h2⟩
      · left
        refine h1.trans (Nat.add_le_add_left (card_le_card fun r hr => ?_) _)
        simp only [mem_filter, mem_univ, true_and] at hr ⊢
        refine ⟨hr.1, ?_, fun h' => ?_⟩
        · rw [hs.mem_eq_of_not_wtgt hreg hxp hr.2.2]; exact hr.2.1
        · rcases hs.wtgt_new h' with h'' | h''
          · rw [hr.2.1] at h''; cases h''
          · exact hr.2.2 h''
      · right
        refine ⟨le_trans (Nat.add_le_add_right (Nat.add_le_add_left
          (card_le_card fun r hr => ?_) _) 1) h1, h2.trans (Nat.add_le_add_left
          (card_le_card fun r hr => ?_) _)⟩
        · simp only [mem_filter, mem_univ, true_and] at hr ⊢
          exact ⟨hr.1, hs.zero_of_write_own hreg hxp hr.2⟩
        · simp only [mem_filter, mem_univ, true_and] at hr ⊢
          refine ⟨hr.1, ?_⟩
          rcases hs.some_of_write_own hreg hxp hr.2 with h' | h' <;> exact h'

/-- A weak collect: the last read, fewer than `⌈m/2⌉` own values. -/
lemma TStep.weak_count {vs : List (Option P)} {N N' : Fin m → Option P}
    (hs : TStep m π x (.coll vs) N (.rst 0) N') :
    ∃ hj : vs.length < m, N' = N ∧ m ≤ vs.length + 1 ∧
      (vs ++ [N (π x ⟨vs.length, hj⟩)]).count (some x) < thr m := by
  generalize hl : (Loc.coll vs : Loc P) = l at hs
  generalize hl' : (Loc.rst 0 : Loc P) = l'' at hs
  cases hs with
  | @coll vs₀ _ hj =>
    cases hl
    rcases afterColl_cases (m := m) x (vs ++ [N (π x ⟨vs.length, hj⟩)]) with
      ⟨-, h1⟩ | ⟨h2, h3, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at hl' <;> cases hl'
    exact ⟨hj, rfl, by simpa using h2, h3⟩
  | idle => rw [← hl'] at hl; cases hl
  | _ => cases hl

/-- No register is unread after the last read. -/
lemma card_unread_last (a : P) (vs : List (Option P)) (hl : m ≤ vs.length + 1)
    (Q : Fin m → Prop) [DecidablePred Q] :
    #(univ.filter (fun r => vs.length + 1 ≤ posn π a r ∧ Q r)) = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro r _ h
  have := posn_lt π a r
  omega

/-- **G2**: a weak collect in a clean race is won by the other process. -/
lemma GInv.weak (hP : ∀ a b c : P, a ≠ b → c = a ∨ c = b) (hG : GInv π loc M) {y : P}
    (hxy : x ≠ y) {vs : List (Option P)} (hx : loc x = .coll vs)
    (hs : TStep m π x (.coll vs) M (.rst 0) M') :
    DInv π y x (Function.update loc x (.rst 0)) M' := by
  obtain ⟨hj, hMM, hlast, hcnt⟩ := hs.weak_count
  rw [hMM]
  refine ⟨by simp [Pas], by rw [Function.update_of_ne (Ne.symm hxy)]; exact hG.noPas y, ?_,
    fun j h => by simp at h⟩
  simp only [Function.update_self, tgt, notMem_empty, not_false_eq_true, and_true]
  by_contra hno
  push Not at hno
  have hsplit1 := card_unread_split (π := π) x vs hj (fun r => M r = some x ∧ r ∉ wtgt π y (loc y))
  have hsplit2 := card_unread_split (π := π) x vs hj (fun r => M r = none)
  rw [card_unread_last x vs hlast] at hsplit1 hsplit2
  rw [count_append_one] at hcnt
  have hy0 : #(univ.filter (fun r => posn π x r < vs.length ∧ M r = some y)) = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro r _ h; exact hno r h.2
  have hthr : 2 * thr m ≤ m + 1 := by unfold thr; omega
  rcases hG.coll x y hxy vs hx with h1 | ⟨h1, h2⟩
  · split_ifs at hsplit1 hcnt <;> simp_all <;> omega
  · cases hv : M (π x ⟨vs.length, hj⟩) with
    | none => simp only [hv] at hsplit2 hcnt; simp at hsplit2 hcnt; omega
    | some c =>
      rcases hP x y c hxy with rfl | rfl
      · simp only [hv] at hsplit2 hcnt; simp at hsplit2 hcnt; omega
      · exact hno _ hv

/-- **D1**: once `q` has won, it stays so. -/
lemma DInv.step (hP : ∀ a b c : P, a ≠ b → c = a ∨ c = b) (hDF : DFInv π loc M) {p q : P}
    (hpq : p ≠ q) (hD : DInv π q p loc M) (hreg : InReg (loc x))
    (hs : TStep m π x (loc x) M l' M') : DInv π q p (Function.update loc x l') M' := by
  obtain ⟨hpP, hqP, ⟨r, hr, hrt⟩, hw⟩ := hD
  rcases hP p q x hpq with hx | hx
  · subst x
    unfold DInv
    rw [Function.update_self, Function.update_of_ne (Ne.symm hpq)]
    generalize hlx : loc p = lx at hs
    rw [hlx] at hpP hrt hw
    cases hs with
    | @rst0 j _ hj h0 =>
      refine ⟨trivial, hqP, ⟨r, hr, ?_⟩, fun j h => by cases h⟩
      simp only [tgt, mem_filter, mem_univ, true_and]
      intro h'; rw [eq_of_posn_eq π hj h', h0] at hr; exact hpq (Option.some.inj hr)
    | @rst1 j _ hj _ =>
      rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1]
      · exact ⟨trivial, hqP, ⟨r, hr, by simp [tgt]⟩, fun j h => by cases h⟩
      · refine ⟨trivial, hqP, ⟨r, hr, by simp [tgt]⟩, fun j h => ?_⟩
        cases h; exact ⟨r, by simp, hr⟩
    | @rstW j _ hj =>
      have hr0 : r ≠ π p ⟨j, hj⟩ := fun h' => hrt (by rw [h']; simp [tgt])
      have hr' : Function.update M (π p ⟨j, hj⟩) none r = some q := by
        rw [Function.update_of_ne hr0]; exact hr
      rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1]
      · exact ⟨trivial, hqP, ⟨r, hr', by simp [tgt]⟩, fun j h => by cases h⟩
      · refine ⟨trivial, hqP, ⟨r, hr', by simp [tgt]⟩, fun j h => ?_⟩
        cases h; exact ⟨r, by simp, hr'⟩
    | @wait j z _ hj =>
      unfold afterWait
      split_ifs with h1 h2
      · refine ⟨trivial, hqP, ⟨r, hr, by simp [tgt]⟩, fun j' h => ?_⟩
        simp only [Loc.wait.injEq] at h
        obtain ⟨rfl, h3⟩ := h
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h3
        obtain ⟨r', hr'1, hr'2⟩ := hw j (by rw [h3.1])
        refine ⟨r', ?_, hr'2⟩
        have : posn π p r' ≠ j := fun h' => by
          rw [eq_of_posn_eq π hj h', h3.2] at hr'2; cases hr'2
        omega
      · exfalso
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h2
        obtain ⟨r', hr'1, hr'2⟩ := hw j (by rw [h2.1])
        have := posn_lt π p r'
        rw [eq_of_posn_eq π hj (show posn π p r' = j by omega), h2.2] at hr'2
        cases hr'2
      · refine ⟨trivial, hqP, ⟨r, hr, by simp [tgt]⟩, fun j' h => ?_⟩
        cases h; exact ⟨r, by simp, hr⟩
    | idle => exact ⟨hpP, hqP, ⟨r, hr, hrt⟩, hw⟩
    | _ => simp [Pas] at hpP
  · subst x
    unfold DInv
    rw [Function.update_self, Function.update_of_ne hpq]
    refine ⟨hpP, fun h' => ?_, ⟨r, ?_, hrt⟩, fun j h => ?_⟩
    · obtain ⟨vs, h1, rfl⟩ := hs.weak_of_pas hqP h'
      rw [h1] at hs
      obtain ⟨hj, -, hlast, hcnt⟩ := hs.weak_count
      have := hDF.not_weak_of_pas hpq.symm hpP h1 hj hlast
      omega
    · rcases hs.some_of_write_own hreg hqP hr with h' | h' <;> exact h'
    · obtain ⟨r', h1, h2⟩ := hw j h
      exact ⟨r', h1, by rcases hs.some_of_write_own hreg hqP h2 with h' | h' <;> exact h'⟩

/-- **D2**: nobody gives up once the race is decided. -/
lemma DInv.not_weak (hP : ∀ a b c : P, a ≠ b → c = a ∨ c = b) (hDF : DFInv π loc M) {p q : P}
    (hpq : p ≠ q) (hD : DInv π q p loc M) {vs : List (Option P)} (hx : loc x = .coll vs)
    (hs : TStep m π x (.coll vs) M (.rst 0) M') : False := by
  rcases hP p q x hpq with rfl | rfl
  · have := hD.1; rw [hx] at this; exact this
  · obtain ⟨hj, -, hlast, hcnt⟩ := hs.weak_count
    have := hDF.not_weak_of_pas hpq.symm hD.1 hx hj hlast
    omega

end Step

end Podc.MemoryAnonymousCoordination.Mutex
