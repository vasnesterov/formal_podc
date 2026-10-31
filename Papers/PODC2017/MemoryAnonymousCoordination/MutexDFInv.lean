import Papers.PODC2017.MemoryAnonymousCoordination.MutexME

/-!
# Figure 1: the invariant used for deadlock-freedom

Global invariant `DFInv` of all reachable configurations (two processes `a ≠ b`):
* `own1`, `own2`: a process in the remainder, waiting (lines 6–8) or returning from `unlock()` owns
  no register (no register holds its identifier); during the loops of lines 5 and 12 it owns no
  register at the positions already passed;
* `c0`: during a collect, a register at a position already read holds the own identifier only if
  it was read as such (count version);
* `z`: if both processes are *active* (lines 2–3), no register holding `0` has been *covered* by
  both (passed by the current scan of line 2, or by both scans if collecting);
* `cc`: if both processes are collecting, `pot a + pot b ≥ m`, where `pot` is the number of own
  values read so far plus the number of own registers not read yet;
* `phi`: if `a` is *passive* (lines 5–8), the registers owned by `a` or about to be erased by `a`,
  plus the `0`s already passed by a scanning `b`, are fewer than `⌈m/2⌉`;
* `R`: if `a` is passive and `b` collects, the collect of `b` is guaranteed to see at least
  `⌈m/2⌉` own values: `b` cannot give up while `a` is passive;
* `nbp`: the processes are never both passive.
-/

set_option linter.unusedSectionVars false

namespace Podc.MemoryAnonymousCoordination.Mutex

open Cslib.SharedMemory Finset

variable {P : Type} [DecidableEq P] {m : ℕ} (π : P → Equiv.Perm (Fin m))

/-- Active: lines 2–3. -/
def Act : Loc P → Prop
  | .scan _ | .scanW _ | .coll _ => True
  | _ => False

/-- Passive: lines 5–8. -/
def Pas : Loc P → Prop
  | .rst _ | .rstW _ | .wait _ _ => True
  | _ => False

/-- Owning nothing: remainder, waiting, returning from `unlock()`. -/
def Own0 : Loc P → Prop
  | .rem | .wait _ _ | .retUnlock => True
  | _ => False

/-- Registers covered by the current scan (line 2) of `a`, all registers during a collect. -/
def cov (a : P) : Loc P → Finset (Fin m)
  | .scan j | .scanW j => univ.filter (fun r => posn π a r < j)
  | .coll _ => univ
  | _ => ∅

/-- The register `a` is about to erase (line 5). -/
def tgt (a : P) : Loc P → Finset (Fin m)
  | .rstW j => univ.filter (fun r => posn π a r = j)
  | _ => ∅

/-- Number of `0`s at positions already passed by a scanning process. -/
def gapsS (b : P) (l : Loc P) (M : Fin m → Option P) : ℕ :=
  match l with
  | .scan j | .scanW j => #(univ.filter (fun r => posn π b r < j ∧ M r = none))
  | _ => 0

/-- Own values read so far plus own registers not read yet. -/
def pot (a : P) (vs : List (Option P)) (M : Fin m → Option P) : ℕ :=
  vs.count (some a) + #(univ.filter (fun r => vs.length ≤ posn π a r ∧ M r = some a))

/-- The invariant for deadlock-freedom. -/
structure DFInv (loc : P → Loc P) (M : Fin m → Option P) : Prop where
  own1 : ∀ a, Own0 (loc a) → ∀ r, M r ≠ some a
  own2 : ∀ a j, (loc a = .rst j ∨ loc a = .rstW j ∨ loc a = .exit j) →
    ∀ r, posn π a r < j → M r ≠ some a
  c0 : ∀ a vs, loc a = .coll vs →
    #(univ.filter (fun r => posn π a r < vs.length ∧ M r = some a)) ≤ vs.count (some a)
  z : ∀ a b, a ≠ b → Act (loc a) → Act (loc b) → ∀ r, M r = none → r ∈ cov π a (loc a) →
    r ∉ cov π b (loc b)
  cc : ∀ a b, a ≠ b → ∀ va vb, loc a = .coll va → loc b = .coll vb →
    m ≤ pot π a va M + pot π b vb M
  phi : ∀ a b, a ≠ b → Pas (loc a) →
    #(univ.filter (fun r => M r = some a ∨ r ∈ tgt π a (loc a))) + gapsS π b (loc b) M + 1 ≤ thr m
  R : ∀ a b, a ≠ b → Pas (loc a) → ∀ vs, loc b = .coll vs →
    thr m ≤ vs.count (some b) +
      #(univ.filter (fun r => vs.length ≤ posn π b r ∧ M r = some b ∧ r ∉ tgt π a (loc a)))
  nbp : ∀ a b, a ≠ b → Pas (loc a) → ¬ Pas (loc b)

variable {π}

lemma DFInv.init : DFInv π (fun _ : P => (.rem : Loc P)) (fun _ => none) where
  own1 _ _ _ := by simp
  own2 _ _ h := by simp at h
  c0 _ _ h := by simp at h
  z _ _ _ h := by simp [Act] at h
  cc _ _ _ _ _ h := by simp at h
  phi _ _ _ h := by simp [Pas] at h
  R _ _ _ h := by simp [Pas] at h
  nbp _ _ _ h := by simp [Pas] at h

/-! ### Simple facts about the continuations -/

lemma nextScan_cases (j : ℕ) : (j + 1 < m ∧ (nextScan m j : Loc P) = .scan (j + 1)) ∨
    (m ≤ j + 1 ∧ (nextScan m j : Loc P) = .coll []) := by
  unfold nextScan; split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

lemma nextRst_cases (j : ℕ) : (j + 1 < m ∧ (nextRst m j : Loc P) = .rst (j + 1)) ∨
    (m ≤ j + 1 ∧ (nextRst m j : Loc P) = .wait 0 true) := by
  unfold nextRst; split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

lemma nextExit_cases (j : ℕ) : (j + 1 < m ∧ (nextExit m j : Loc P) = .exit (j + 1)) ∨
    (m ≤ j + 1 ∧ (nextExit m j : Loc P) = .retUnlock) := by
  unfold nextExit; split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

lemma afterWait_cases (j : ℕ) (z : Bool) (v : Option P) :
    (∃ z', afterWait m j z v = .wait (j + 1) z') ∨ afterWait m j z v = .scan 0 ∨
      afterWait m j z v = .wait 0 true := by
  unfold afterWait; split_ifs <;> simp

lemma afterColl_cases (x : P) (vs : List (Option P)) :
    (vs.length < m ∧ afterColl m x vs = .coll vs) ∨
    (m ≤ vs.length ∧ vs.count (some x) < thr m ∧ afterColl m x vs = .rst 0) ∨
    (m ≤ vs.length ∧ vs.count (some x) = m ∧ afterColl m x vs = .retLock) ∨
    (m ≤ vs.length ∧ thr m ≤ vs.count (some x) ∧ afterColl m x vs = .scan 0) := by
  unfold afterColl; split_ifs with h1 h2 h3
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨by omega, h2, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, h3, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, rfl⟩))

/-! ### Preservation: ownership facts -/

section Step

variable {loc : P → Loc P} {M M' : Fin m → Option P} {x : P} {l' : Loc P}

/-- Registers at positions `≤ j`, all registers if `j + 1 ≥ m`. -/
lemma posn_lt_of_ne {a : P} {r : Fin m} {j : ℕ} (hj : j < m) (hm : m ≤ j + 1)
    (hr : r ≠ π a ⟨j, hj⟩) : posn π a r < j := by
  have h1 := posn_lt π a r
  have h2 : posn π a r ≠ j := fun h => hr (eq_of_posn_eq π hj h)
  omega

lemma DFInv.own1_step (h : DFInv π loc M) (hs : TStep m π x (loc x) M l' M') :
    ∀ a, Own0 (Function.update loc x l' a) → ∀ r, M' r ≠ some a := by
  intro a ha r
  by_cases hax : a = x
  · subst hax
    rw [Function.update_self] at ha
    generalize hlx : loc a = lx at hs
    cases hs with
    | @rst1 j _ hj h0 =>
      rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨h2, h1⟩ <;> rw [h1] at ha
      · simp [Own0] at ha
      · by_cases hr : r = π a ⟨j, hj⟩
        · rw [hr]; exact h0
        · exact h.own2 a j (Or.inl hlx) r (posn_lt_of_ne hj h2 hr)
    | @rstW j _ hj =>
      rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨h2, h1⟩ <;> rw [h1] at ha
      · simp [Own0] at ha
      · by_cases hr : r = π a ⟨j, hj⟩
        · rw [hr]; simp
        · rw [Function.update_of_ne hr]
          exact h.own2 a j (Or.inr (Or.inl hlx)) r (posn_lt_of_ne hj h2 hr)
    | @exit j _ hj =>
      rcases nextExit_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨h2, h1⟩ <;> rw [h1] at ha
      · simp [Own0] at ha
      · by_cases hr : r = π a ⟨j, hj⟩
        · rw [hr]; simp
        · rw [Function.update_of_ne hr]
          exact h.own2 a j (Or.inr (Or.inr hlx)) r (posn_lt_of_ne hj h2 hr)
    | @wait j z _ hj =>
      rcases afterWait_cases j z (M (π a ⟨j, hj⟩)) with ⟨z', h1⟩ | h1 | h1 <;> rw [h1] at ha
      · exact h.own1 a (by rw [hlx]; trivial) r
      · simp [Own0] at ha
      · exact h.own1 a (by rw [hlx]; trivial) r
    | retUnlock => exact h.own1 a (by rw [hlx]; trivial) r
    | idle => exact h.own1 a (by rw [hlx]; exact ha) r
    | scan0 => simp [Own0] at ha
    | @scan1 j _ hj _ =>
      rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        simp [Own0] at ha
    | @scanW j _ hj =>
      rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        simp [Own0] at ha
    | @coll vs _ hj =>
      rcases afterColl_cases (m := m) a (vs ++ [M (π a ⟨vs.length, hj⟩)]) with
        ⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at ha <;> simp [Own0] at ha
    | rst0 => simp [Own0] at ha
    | retLock => simp [Own0] at ha
    | invLock => simp [Own0] at ha
    | invUnlock => simp [Own0] at ha
  · rw [Function.update_of_ne hax] at ha
    intro hr
    exact h.own1 a ha r (hs.mem_some (Ne.symm hax) hr)

lemma DFInv.own2_step (h : DFInv π loc M) (hs : TStep m π x (loc x) M l' M') :
    ∀ a j, (Function.update loc x l' a = .rst j ∨ Function.update loc x l' a = .rstW j ∨
      Function.update loc x l' a = .exit j) → ∀ r, posn π a r < j → M' r ≠ some a := by
  intro a j ha r hr
  by_cases hax : a = x
  · subst hax
    rw [Function.update_self] at ha
    generalize hlx : loc a = lx at hs
    cases hs with
    | @rst0 j₀ _ hj h0 =>
      rcases ha with h1 | h1 | h1 <;> cases h1
      exact h.own2 a j (Or.inl hlx) r hr
    | @rst1 j₀ _ hj h0 =>
      rcases nextRst_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        rcases ha with h2 | h2 | h2 <;> cases h2
      by_cases hr0 : r = π a ⟨j₀, hj⟩
      · rw [hr0]; exact h0
      · have : posn π a r ≠ j₀ := fun h' => hr0 (eq_of_posn_eq π hj h')
        exact h.own2 a j₀ (Or.inl hlx) r (by omega)
    | @rstW j₀ _ hj =>
      rcases nextRst_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        rcases ha with h2 | h2 | h2 <;> cases h2
      by_cases hr0 : r = π a ⟨j₀, hj⟩
      · rw [hr0]; simp
      · rw [Function.update_of_ne hr0]
        have : posn π a r ≠ j₀ := fun h' => hr0 (eq_of_posn_eq π hj h')
        exact h.own2 a j₀ (Or.inr (Or.inl hlx)) r (by omega)
    | @exit j₀ _ hj =>
      rcases nextExit_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        rcases ha with h2 | h2 | h2 <;> cases h2
      by_cases hr0 : r = π a ⟨j₀, hj⟩
      · rw [hr0]; simp
      · rw [Function.update_of_ne hr0]
        have : posn π a r ≠ j₀ := fun h' => hr0 (eq_of_posn_eq π hj h')
        exact h.own2 a j₀ (Or.inr (Or.inr hlx)) r (by omega)
    | @coll vs _ hj =>
      rcases afterColl_cases (m := m) a (vs ++ [M (π a ⟨vs.length, hj⟩)]) with
        ⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at ha <;>
        rcases ha with h2 | h2 | h2 <;> cases h2
      omega
    | invUnlock => rcases ha with h2 | h2 | h2 <;> cases h2; omega
    | idle => exact h.own2 a j (by rw [hlx]; exact ha) r hr
    | @scan1 j₀ _ hj _ =>
      rcases nextScan_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        rcases ha with h2 | h2 | h2 <;> cases h2
    | @scanW j₀ _ hj =>
      rcases nextScan_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        rcases ha with h2 | h2 | h2 <;> cases h2
    | @wait j₀ z _ hj =>
      rcases afterWait_cases j₀ z (M (π a ⟨j₀, hj⟩)) with ⟨z', h1⟩ | h1 | h1 <;> rw [h1] at ha <;>
        rcases ha with h2 | h2 | h2 <;> cases h2
    | _ => rcases ha with h2 | h2 | h2 <;> cases h2
  · rw [Function.update_of_ne hax] at ha
    intro h'
    exact h.own2 a j ha r hr (hs.mem_some (Ne.symm hax) h')

lemma DFInv.c0_step (h : DFInv π loc M) (hs : TStep m π x (loc x) M l' M') :
    ∀ a vs, Function.update loc x l' a = .coll vs →
      #(univ.filter (fun r => posn π a r < vs.length ∧ M' r = some a)) ≤ vs.count (some a) := by
  intro a vs ha
  by_cases hax : a = x
  · subst hax
    rw [Function.update_self] at ha
    generalize hlx : loc a = lx at hs
    cases hs with
    | @scan1 j₀ _ hj _ =>
      rcases nextScan_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        cases ha
      simp
    | @scanW j₀ _ hj =>
      rcases nextScan_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        cases ha
      simp
    | @coll vs₀ _ hj =>
      rcases afterColl_cases (m := m) a (vs₀ ++ [M (π a ⟨vs₀.length, hj⟩)]) with
        ⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at ha <;> cases ha
      have h0 := h.c0 a vs₀ hlx
      rw [count_append_one]
      have hsub : univ.filter (fun r => posn π a r < (vs₀ ++ [M (π a ⟨vs₀.length, hj⟩)]).length ∧
          M r = some a) ⊆ univ.filter (fun r => posn π a r < vs₀.length ∧ M r = some a) ∪
          (if M (π a ⟨vs₀.length, hj⟩) = some a then {π a ⟨vs₀.length, hj⟩} else ∅) := by
        intro r hr
        simp only [mem_filter, mem_univ, true_and, List.length_append, List.length_cons,
          List.length_nil] at hr
        by_cases hr0 : posn π a r = vs₀.length
        · have := eq_of_posn_eq π hj hr0
          subst this
          simp [hr.2]
        · simp only [mem_union, mem_filter, mem_univ, true_and]
          left; exact ⟨by omega, hr.2⟩
      refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
      split_ifs <;> simp <;> omega
    | idle => exact h.c0 a vs (by rw [hlx]; exact ha)
    | @rst1 j₀ _ hj h0 =>
      rcases nextRst_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        cases ha
    | @rstW j₀ _ hj =>
      rcases nextRst_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        cases ha
    | @exit j₀ _ hj =>
      rcases nextExit_cases (m := m) (P := P) j₀ with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        cases ha
    | @wait j₀ z _ hj =>
      rcases afterWait_cases j₀ z (M (π a ⟨j₀, hj⟩)) with ⟨z', h1⟩ | h1 | h1 <;> rw [h1] at ha <;>
        cases ha
    | _ => cases ha
  · rw [Function.update_of_ne hax] at ha
    refine (card_le_card fun r hr => ?_).trans (h.c0 a vs ha)
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    exact ⟨hr.1, hs.mem_some (Ne.symm hax) hr.2⟩

/-- A step of `x` leaving it active: a covered `0` was a covered `0` before. -/
lemma TStep.zero_cov (hs : TStep m π x (loc x) M l' M') (ha : Act l') {r : Fin m}
    (hr : M' r = none) (hc : r ∈ cov π x l') :
    Act (loc x) ∧ M r = none ∧ r ∈ cov π x (loc x) := by
  generalize hlx : loc x = lx at hs
  cases hs with
  | scan0 hj h0 => exact ⟨trivial, hr, by simpa [cov] using hc⟩
  | @scan1 j _ hj h0 =>
    refine ⟨trivial, hr, ?_⟩
    have hr0 : r ≠ π x ⟨j, hj⟩ := fun h' => h0 (h' ▸ hr)
    have := posn_lt π x r
    have hne : posn π x r ≠ j := fun h' => hr0 (eq_of_posn_eq π hj h')
    simp only [cov, mem_filter, mem_univ, true_and]
    rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨h2, h1⟩ <;> rw [h1] at hc
    · simp [cov] at hc; omega
    · omega
  | @scanW j _ hj =>
    have hr0 : r ≠ π x ⟨j, hj⟩ := fun h' => by rw [h'] at hr; simp at hr
    rw [Function.update_of_ne hr0] at hr
    refine ⟨trivial, hr, ?_⟩
    have := posn_lt π x r
    have hne : posn π x r ≠ j := fun h' => hr0 (eq_of_posn_eq π hj h')
    simp only [cov, mem_filter, mem_univ, true_and]
    rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨h2, h1⟩ <;> rw [h1] at hc
    · simp [cov] at hc; omega
    · omega
  | @coll vs _ hj =>
    rcases afterColl_cases (m := m) x (vs ++ [M (π x ⟨vs.length, hj⟩)]) with
      ⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at hc ha
    · exact ⟨trivial, hr, by simp [cov]⟩
    · simp [Act] at ha
    · simp [Act] at ha
    · simp [cov] at hc
  | @wait j z _ hj =>
    rcases afterWait_cases j z (M (π x ⟨j, hj⟩)) with ⟨z', h1⟩ | h1 | h1 <;> rw [h1] at hc ha <;>
      simp [cov] at hc ha
  | invLock => simp [cov] at hc
  | idle => exact ⟨ha, hr, hc⟩
  | @rst1 j _ hj _ =>
    rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
      simp [Act] at ha
  | @rstW j _ hj =>
    rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
      simp [Act] at ha
  | @exit j _ hj =>
    rcases nextExit_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
      simp [Act] at ha
  | _ => simp [Act] at ha

/-- A step of `x` leaving it active creates no `0`. -/
lemma TStep.zero_of_act (hs : TStep m π x (loc x) M l' M') (ha : Act l') {r : Fin m}
    (hr : M' r = none) : M r = none := by
  generalize hlx : loc x = lx at hs
  cases hs with
  | @scanW j _ hj =>
    have hr0 : r ≠ π x ⟨j, hj⟩ := fun h' => by rw [h'] at hr; simp at hr
    rwa [Function.update_of_ne hr0] at hr
  | @rstW j _ hj =>
    rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
      simp [Act] at ha
  | @exit j _ hj =>
    rcases nextExit_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
      simp [Act] at ha
  | _ => exact hr

lemma DFInv.z_step (hP : ∀ a b c : P, a ≠ b → c = a ∨ c = b) (h : DFInv π loc M)
    (hs : TStep m π x (loc x) M l' M') :
    ∀ a b, a ≠ b → Act (Function.update loc x l' a) → Act (Function.update loc x l' b) →
      ∀ r, M' r = none → r ∈ cov π a (Function.update loc x l' a) →
        r ∉ cov π b (Function.update loc x l' b) := by
  intro a b hab ha hb r hr hra hrb
  rcases hP a b x hab with hx | hx
  · subst x
    rw [Function.update_self] at ha hra
    rw [Function.update_of_ne hab.symm] at hb hrb
    obtain ⟨h1, h2, h3⟩ := hs.zero_cov ha hr hra
    exact h.z a b hab h1 hb r h2 h3 hrb
  · subst x
    rw [Function.update_self] at hb hrb
    rw [Function.update_of_ne hab] at ha hra
    obtain ⟨h1, h2, h3⟩ := hs.zero_cov hb hr hrb
    exact h.z a b hab ha h1 r h2 hra h3

/-- Reading the next register does not change `pot`. -/
lemma pot_read (a : P) (vs : List (Option P)) (M : Fin m → Option P) (hj : vs.length < m) :
    pot π a (vs ++ [M (π a ⟨vs.length, hj⟩)]) M = pot π a vs M := by
  unfold pot
  rw [count_append_one]
  have hsplit : univ.filter (fun r => vs.length ≤ posn π a r ∧ M r = some a) =
      univ.filter (fun r => (vs ++ [M (π a ⟨vs.length, hj⟩)]).length ≤ posn π a r ∧
        M r = some a) ∪
      (if M (π a ⟨vs.length, hj⟩) = some a then {π a ⟨vs.length, hj⟩} else ∅) := by
    ext r
    simp only [mem_filter, mem_univ, true_and, List.length_append, List.length_cons,
      List.length_nil, mem_union]
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
  rw [hsplit]
  split_ifs with h1
  · rw [card_union_of_disjoint]
    · simp; omega
    · simp
  · simp

/-- Every register holds one of the two identifiers or `0`: counting. -/
lemma card_le_of_cover {a b : P} (hP : ∀ c : P, c = a ∨ c = b) {M : Fin m → Option P}
    (h0 : ∀ r, M r ≠ none) : m ≤ #(univ.filter (fun r => M r = some a)) +
      #(univ.filter (fun r => M r = some b)) := by
  have : (univ : Finset (Fin m)) ⊆ univ.filter (fun r => M r = some a) ∪
      univ.filter (fun r => M r = some b) := by
    intro r _
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 (h0 r)
    rcases hP c with rfl | rfl <;> simp [hc]
  have := (card_le_card this).trans (card_union_le _ _)
  simpa using this

/-- `cc` when `x` starts a collect and memory holds no `0`. -/
lemma cc_establish {x y : P} (hP2 : ∀ c : P, c = x ∨ c = y) {M : Fin m → Option P}
    (hz : ∀ r, M r ≠ none) {vy : List (Option P)}
    (hc0 : #(univ.filter (fun r => posn π y r < vy.length ∧ M r = some y)) ≤ vy.count (some y)) :
    m ≤ pot π x [] M + pot π y vy M := by
  have h1 := card_le_of_cover hP2 hz
  have h2 : univ.filter (fun r => M r = some y) ⊆
      univ.filter (fun r => posn π y r < vy.length ∧ M r = some y) ∪
      univ.filter (fun r => vy.length ≤ posn π y r ∧ M r = some y) := by
    intro r hr
    simp only [mem_filter, mem_univ, true_and, mem_union] at hr ⊢
    by_cases h : posn π y r < vy.length
    · exact Or.inl ⟨h, hr⟩
    · exact Or.inr ⟨by omega, hr⟩
  have h3 := (card_le_card h2).trans (card_union_le _ _)
  simp only [pot, List.count_nil, List.length_nil, Nat.zero_le, true_and, zero_add]
  omega

/-- `cc` for a step of `x` into or inside a collect, `y` collecting. -/
lemma DFInv.cc_aux (hP : ∀ a b c : P, a ≠ b → c = a ∨ c = b) (h : DFInv π loc M)
    (hs : TStep m π x (loc x) M l' M') {y : P} (hxy : x ≠ y) {vx vy : List (Option P)}
    (hx : l' = .coll vx) (hy : loc y = .coll vy) (hz : ∀ r, M' r ≠ none) :
    m ≤ pot π x vx M' + pot π y vy M' := by
  generalize hlx : loc x = lx at hs
  cases hs with
  | @coll vs _ hj =>
    rcases afterColl_cases (m := m) x (vs ++ [M (π x ⟨vs.length, hj⟩)]) with
      ⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at hx <;> cases hx
    rw [pot_read]; exact h.cc x y hxy vs vy hlx hy
  | idle => exact h.cc x y hxy vx vy (hlx.trans hx) hy
  | @scan1 j _ hj _ =>
    rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hx <;>
      cases hx
    exact cc_establish (fun c => hP x y c hxy) hz (h.c0 y vy hy)
  | @scanW j _ hj =>
    rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hx <;>
      cases hx
    refine cc_establish (fun c => hP x y c hxy) hz ((card_le_card fun r hr => ?_).trans (h.c0 y vy hy))
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    exact ⟨hr.1, (TStep.scanW (π := π) (x := x) (M := M) hj).mem_some hxy hr.2⟩
  | @rst1 j _ hj _ =>
    rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hx <;>
      cases hx
  | @rstW j _ hj =>
    rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hx <;>
      cases hx
  | @exit j _ hj =>
    rcases nextExit_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hx <;>
      cases hx
  | @wait j z _ hj =>
    rcases afterWait_cases j z (M (π x ⟨j, hj⟩)) with ⟨z', h1⟩ | h1 | h1 <;> rw [h1] at hx <;>
      cases hx
  | _ => cases hx

lemma DFInv.cc_step (hP : ∀ a b c : P, a ≠ b → c = a ∨ c = b) (h : DFInv π loc M)
    (hs : TStep m π x (loc x) M l' M')
    (hz : ∀ a b, a ≠ b → Act (Function.update loc x l' a) → Act (Function.update loc x l' b) →
      ∀ r, M' r = none → r ∈ cov π a (Function.update loc x l' a) →
        r ∉ cov π b (Function.update loc x l' b)) :
    ∀ a b, a ≠ b → ∀ va vb, Function.update loc x l' a = .coll va →
      Function.update loc x l' b = .coll vb → m ≤ pot π a va M' + pot π b vb M' := by
  intro a b hab va vb ha hb
  have hz' : ∀ r, M' r ≠ none := fun r hr =>
    hz a b hab (by rw [ha]; trivial) (by rw [hb]; trivial) r hr (by rw [ha]; simp [cov])
      (by rw [hb]; simp [cov])
  rcases hP a b x hab with hx | hx
  · subst x
    rw [Function.update_self] at ha
    rw [Function.update_of_ne hab.symm] at hb
    exact h.cc_aux hP hs hab ha hb hz'
  · subst x
    rw [Function.update_self] at hb
    rw [Function.update_of_ne hab] at ha
    rw [add_comm]
    exact h.cc_aux hP hs hab.symm hb ha hz'

/-- The `0`s passed by a scan do not increase by a step of the scanning process. -/
lemma TStep.gaps_le (hs : TStep m π x (loc x) M l' M') :
    gapsS π x l' M' ≤ gapsS π x (loc x) M := by
  generalize hlx : loc x = lx at hs
  cases hs with
  | scan0 => exact le_rfl
  | @scan1 j _ hj h0 =>
    rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1]
    swap; · simp [gapsS]
    simp only [gapsS]
    refine card_le_card fun r hr => ?_
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    refine ⟨?_, hr.2⟩
    have : posn π x r ≠ j := fun h' => h0 (by rw [← eq_of_posn_eq π hj h']; exact hr.2)
    omega
  | @scanW j _ hj =>
    rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1]
    swap; · simp [gapsS]
    simp only [gapsS]
    refine card_le_card fun r hr => ?_
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    have hr0 : r ≠ π x ⟨j, hj⟩ := fun h' => by rw [h'] at hr; simp at hr
    rw [Function.update_of_ne hr0] at hr
    refine ⟨?_, hr.2⟩
    have : posn π x r ≠ j := fun h' => hr0 (eq_of_posn_eq π hj h')
    omega
  | @coll vs _ hj =>
    rcases afterColl_cases (m := m) x (vs ++ [M (π x ⟨vs.length, hj⟩)]) with
      ⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] <;> simp [gapsS]
  | @wait j z _ hj =>
    rcases afterWait_cases j z (M (π x ⟨j, hj⟩)) with ⟨z', h1⟩ | h1 | h1 <;> rw [h1] <;>
      simp [gapsS]
  | @rst1 j _ hj _ =>
    rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [gapsS]
  | @rstW j _ hj =>
    rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [gapsS]
  | @exit j _ hj =>
    rcases nextExit_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [gapsS]
  | idle => exact le_rfl
  | _ => simp [gapsS]

/-- After a complete collect `vs ++ [v]`, the registers owned by `a` are at most the own values
read. -/
lemma card_own_le_count (h : DFInv π loc M) {a : P} {vs : List (Option P)} (hl : loc a = .coll vs)
    (hj : vs.length < m) (hlast : m ≤ vs.length + 1) :
    #(univ.filter (fun r => M r = some a)) ≤ (vs ++ [M (π a ⟨vs.length, hj⟩)]).count (some a) := by
  have h0 := h.c0 a vs hl
  rw [count_append_one]
  have hsub : univ.filter (fun r => M r = some a) ⊆
      univ.filter (fun r => posn π a r < vs.length ∧ M r = some a) ∪
      (if M (π a ⟨vs.length, hj⟩) = some a then {π a ⟨vs.length, hj⟩} else ∅) := by
    intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    by_cases hr0 : posn π a r = vs.length
    · have := eq_of_posn_eq π hj hr0
      subst this
      simp [hr]
    · simp only [mem_union, mem_filter, mem_univ, true_and]
      have := posn_lt π a r
      left; exact ⟨by omega, hr⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  split_ifs <;> simp <;> omega

/-- At the end of a collect, `pot` is at most the number of own values read. -/
lemma pot_le_count (a : P) (vs : List (Option P)) (M : Fin m → Option P) (hj : vs.length < m) (hlast : m ≤ vs.length + 1) :
    pot π a vs M ≤ (vs ++ [M (π a ⟨vs.length, hj⟩)]).count (some a) := by
  unfold pot
  rw [count_append_one]
  have : univ.filter (fun r => vs.length ≤ posn π a r ∧ M r = some a) ⊆
      (if M (π a ⟨vs.length, hj⟩) = some a then {π a ⟨vs.length, hj⟩} else ∅) := by
    intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    have := posn_lt π a r
    have h1 := eq_of_posn_eq π hj (show posn π a r = vs.length by omega)
    subst h1
    simp [hr.2]
  have := card_le_card this
  split_ifs at this ⊢ <;> simp only [card_singleton, card_empty] at this <;> omega

/-- A weak collect cannot end while the other process is passive. -/
lemma DFInv.not_weak_of_pas (h : DFInv π loc M) {a b : P} (hab : a ≠ b) (hb : Pas (loc b))
    {vs : List (Option P)} (hl : loc a = .coll vs) (hj : vs.length < m)
    (hlast : m ≤ vs.length + 1) :
    thr m ≤ (vs ++ [M (π a ⟨vs.length, hj⟩)]).count (some a) := by
  have h1 := h.R b a hab.symm hb vs hl
  have h2 : #(univ.filter (fun r => vs.length ≤ posn π a r ∧ M r = some a ∧
      r ∉ tgt π b (loc b))) ≤ #(univ.filter (fun r => vs.length ≤ posn π a r ∧ M r = some a)) :=
    card_le_card fun r hr => by
      simp only [mem_filter, mem_univ, true_and] at hr ⊢
      exact ⟨hr.1, hr.2.1⟩
  have h3 := pot_le_count (π := π) a vs M hj hlast
  unfold pot at h3
  omega

lemma DFInv.nbp_aux (h : DFInv π loc M) (hs : TStep m π x (loc x) M l' M') {y : P}
    (hxy : x ≠ y) (hx : Pas l') (hy : Pas (loc y)) : False := by
  generalize hlx : loc x = lx at hs
  cases hs with
  | @coll vs _ hj =>
    rcases afterColl_cases (m := m) x (vs ++ [M (π x ⟨vs.length, hj⟩)]) with
      ⟨-, h1⟩ | ⟨h2, h3, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at hx <;> simp only [Pas] at hx
    have := h.not_weak_of_pas hxy hy hlx hj (by simpa using h2)
    omega
  | @scan1 j _ hj _ =>
    rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hx <;>
      simp [Pas] at hx
  | @scanW j _ hj =>
    rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hx <;>
      simp [Pas] at hx
  | @exit j _ hj =>
    rcases nextExit_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hx <;>
      simp [Pas] at hx
  | scan0 => simp [Pas] at hx
  | retLock => simp [Pas] at hx
  | retUnlock => simp [Pas] at hx
  | invLock => simp [Pas] at hx
  | invUnlock => simp [Pas] at hx
  | _ => exact h.nbp y x hxy.symm hy (by rw [hlx]; trivial)

lemma DFInv.nbp_step (hP : ∀ a b c : P, a ≠ b → c = a ∨ c = b) (h : DFInv π loc M)
    (hs : TStep m π x (loc x) M l' M') :
    ∀ a b, a ≠ b → Pas (Function.update loc x l' a) → ¬ Pas (Function.update loc x l' b) := by
  intro a b hab ha hb
  rcases hP a b x hab with hx | hx
  · subst x
    rw [Function.update_self] at ha
    rw [Function.update_of_ne hab.symm] at hb
    exact h.nbp_aux hs hab ha hb
  · subst x
    rw [Function.update_self] at hb
    rw [Function.update_of_ne hab] at ha
    exact h.nbp_aux hs hab.symm hb ha

/-- Erasing one register adds at most one `0` passed by a scan. -/
lemma gapsS_update_le (b : P) (l : Loc P) (M : Fin m → Option P) (r0 : Fin m) :
    gapsS π b l (Function.update M r0 none) ≤ gapsS π b l M + 1 := by
  have key : ∀ j, #(univ.filter (fun r => posn π b r < j ∧ Function.update M r0 none r = none)) ≤
      #(univ.filter (fun r => posn π b r < j ∧ M r = none)) + 1 := by
    intro j
    refine (card_le_card (fun r hr => ?_)).trans ((card_union_le
      (univ.filter (fun r => posn π b r < j ∧ M r = none)) {r0}).trans (by simp))
    simp only [mem_filter, mem_univ, true_and] at hr
    simp only [mem_union, mem_filter, mem_univ, true_and, mem_singleton]
    by_cases h : r = r0
    · right; exact h
    · left; rw [Function.update_of_ne h] at hr; exact hr
  cases l with
  | scan j => exact key j
  | scanW j => exact key j
  | _ => simp [gapsS]

/-- If `a` is collecting and `b` scanning, no `0` has been passed by `b`. -/
lemma DFInv.gapsS_eq_zero (h : DFInv π loc M) {a b : P} (hab : a ≠ b) {vs : List (Option P)}
    (ha : loc a = .coll vs) : gapsS π b (loc b) M = 0 := by
  cases hb : loc b <;> simp only [gapsS]
  all_goals
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro r - ⟨h1, h2⟩
    refine h.z a b hab (by rw [ha]; trivial) (by rw [hb]; trivial) r h2 (by rw [ha]; simp [cov])
      (by rw [hb]; simp [cov, h1])

lemma DFInv.phi_step (hP : ∀ a b c : P, a ≠ b → c = a ∨ c = b) (h : DFInv π loc M)
    (hs : TStep m π x (loc x) M l' M') :
    ∀ a b, a ≠ b → Pas (Function.update loc x l' a) →
      #(univ.filter (fun r => M' r = some a ∨ r ∈ tgt π a (Function.update loc x l' a))) +
        gapsS π b (Function.update loc x l' b) M' + 1 ≤ thr m := by
  intro a b hab ha
  rcases hP a b x hab with hx | hx
  · subst x
    rw [Function.update_self] at ha ⊢
    rw [Function.update_of_ne hab.symm]
    generalize hlx : loc a = lx at hs
    cases hs with
    | @coll vs _ hj =>
      rcases afterColl_cases (m := m) a (vs ++ [M (π a ⟨vs.length, hj⟩)]) with
        ⟨-, h1⟩ | ⟨h2, h3, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at ha ⊢ <;>
        simp only [Pas] at ha
      have h4 := card_own_le_count h hlx hj (by simpa using h2)
      have h5 := h.gapsS_eq_zero hab hlx
      simp only [tgt, notMem_empty, or_false]
      omega
    | @rst0 j _ hj h0 =>
      have := h.phi a b hab (by rw [hlx]; trivial)
      rw [hlx] at this
      have heq : univ.filter (fun r => M r = some a ∨ r ∈ tgt π a (.rstW j)) =
          univ.filter (fun r => M r = some a ∨ r ∈ tgt π a (.rst j)) := by
        ext r
        simp only [tgt, mem_filter, mem_univ, true_and, notMem_empty, or_false,
          or_iff_left_iff_imp]
        intro hr; rw [eq_of_posn_eq π hj hr]; exact h0
      rw [heq]; exact this
    | @rst1 j _ hj _ =>
      have := h.phi a b hab (by rw [hlx]; trivial)
      rw [hlx] at this
      rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;>
        simpa [tgt] using this
    | @rstW j _ hj =>
      have := h.phi a b hab (by rw [hlx]; trivial)
      rw [hlx] at this
      have hg := gapsS_update_le (π := π) b (loc b) M (π a ⟨j, hj⟩)
      have hsub : univ.filter (fun r => Function.update M (π a ⟨j, hj⟩) none r = some a) ⊆
          (univ.filter (fun r => M r = some a ∨ r ∈ tgt π a (.rstW j))).erase (π a ⟨j, hj⟩) := by
        intro r hr
        simp only [mem_filter, mem_univ, true_and] at hr
        have hr0 : r ≠ π a ⟨j, hj⟩ := fun h' => by rw [h'] at hr; simp at hr
        rw [Function.update_of_ne hr0] at hr
        simp [hr0, hr]
      have hc := card_le_card hsub
      rw [card_erase_of_mem (by simp [tgt])] at hc
      have hpos : 0 < #(univ.filter (fun r => M r = some a ∨ r ∈ tgt π a (.rstW j))) :=
        card_pos.2 ⟨π a ⟨j, hj⟩, by simp [tgt]⟩
      rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;>
        simp only [tgt, notMem_empty, or_false] <;> omega
    | @wait j z _ hj =>
      have := h.phi a b hab (by rw [hlx]; trivial)
      rw [hlx] at this
      rcases afterWait_cases j z (M (π a ⟨j, hj⟩)) with ⟨z', h1⟩ | h1 | h1 <;> rw [h1] at ha ⊢
      · simpa [tgt] using this
      · simp [Pas] at ha
      · simpa [tgt] using this
    | idle =>
      have := h.phi a b hab (by rw [hlx]; exact ha)
      rwa [hlx] at this
    | @scan1 j _ hj _ =>
      rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        simp [Pas] at ha
    | @scanW j _ hj =>
      rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        simp [Pas] at ha
    | @exit j _ hj =>
      rcases nextExit_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        simp [Pas] at ha
    | scan0 => simp [Pas] at ha
    | retLock => simp [Pas] at ha
    | retUnlock => simp [Pas] at ha
    | invLock => simp [Pas] at ha
    | invUnlock => simp [Pas] at ha
  · subst x
    rw [Function.update_self]
    rw [Function.update_of_ne hab] at ha ⊢
    have h1 := h.phi a b hab ha
    have h2 := hs.gaps_le
    have h3 : #(univ.filter (fun r => M' r = some a ∨ r ∈ tgt π a (loc a))) ≤
        #(univ.filter (fun r => M r = some a ∨ r ∈ tgt π a (loc a))) :=
      card_le_card fun r hr => by
        simp only [mem_filter, mem_univ, true_and] at hr ⊢
        rcases hr with hr | hr
        · exact Or.inl (hs.mem_some hab.symm hr)
        · exact Or.inr hr
    omega

/-- Counting registers holding `b` outside `T`, `a` or in `T`, and `0`. -/
lemma card_le_three {a b : P} (hP2 : ∀ c : P, c = a ∨ c = b) (M : Fin m → Option P)
    (T : Finset (Fin m)) :
    m ≤ #(univ.filter (fun r => M r = some b ∧ r ∉ T)) +
      #(univ.filter (fun r => M r = some a ∨ r ∈ T)) + #(univ.filter (fun r => M r = none)) := by
  have : (univ : Finset (Fin m)) ⊆ univ.filter (fun r => M r = some b ∧ r ∉ T) ∪
      univ.filter (fun r => M r = some a ∨ r ∈ T) ∪ univ.filter (fun r => M r = none) := by
    intro r _
    simp only [mem_union, mem_filter, mem_univ, true_and]
    cases hr : M r with
    | none => right; rfl
    | some c =>
      rcases hP2 c with rfl | rfl
      · left; right; left; rfl
      · by_cases hT : r ∈ T
        · left; right; right; exact hT
        · left; left; exact ⟨rfl, hT⟩
  have h1 := card_le_card this
  have h2 := card_union_le (univ.filter (fun r => M r = some b ∧ r ∉ T) ∪
      univ.filter (fun r => M r = some a ∨ r ∈ T)) (univ.filter (fun r => M r = none))
  have h3 := card_union_le (univ.filter (fun r => M r = some b ∧ r ∉ T))
      (univ.filter (fun r => M r = some a ∨ r ∈ T))
  simp only [card_univ, Fintype.card_fin] at h1
  omega

lemma DFInv.R_step (hP : ∀ a b c : P, a ≠ b → c = a ∨ c = b) (h : DFInv π loc M)
    (hs : TStep m π x (loc x) M l' M') :
    ∀ a b, a ≠ b → Pas (Function.update loc x l' a) → ∀ vs, Function.update loc x l' b = .coll vs →
      thr m ≤ vs.count (some b) + #(univ.filter (fun r => vs.length ≤ posn π b r ∧
        M' r = some b ∧ r ∉ tgt π a (Function.update loc x l' a))) := by
  intro a b hab ha vs hb
  rcases hP a b x hab with hx | hx
  · subst x
    rw [Function.update_self] at ha ⊢
    rw [Function.update_of_ne hab.symm] at hb
    generalize hlx : loc a = lx at hs
    cases hs with
    | @coll va _ hj =>
      rcases afterColl_cases (m := m) a (va ++ [M (π a ⟨va.length, hj⟩)]) with
        ⟨-, h1⟩ | ⟨h2, h3, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at ha ⊢ <;>
        simp only [Pas] at ha
      have h4 := h.cc a b hab va vs hlx hb
      have h5 := pot_le_count (π := π) a va M hj (by simpa using h2)
      simp only [tgt, notMem_empty, not_false_eq_true, and_true]
      unfold pot at h4 h5
      unfold thr at h3 ⊢
      omega
    | @rst0 j _ hj h0 =>
      have := h.R a b hab (by rw [hlx]; trivial) vs hb
      rw [hlx] at this
      have heq : univ.filter (fun r => vs.length ≤ posn π b r ∧ M r = some b ∧
          r ∉ tgt π a (.rstW j)) = univ.filter (fun r => vs.length ≤ posn π b r ∧
            M r = some b ∧ r ∉ tgt π a (.rst j)) := by
        ext r
        simp only [tgt, mem_filter, mem_univ, true_and, notMem_empty, not_false_eq_true,
          and_true]
        constructor
        · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, h2, fun hr' => ?_⟩
          rw [eq_of_posn_eq π hj hr', h0] at h2
          exact hab (Option.some.inj h2)
      rw [heq]; exact this
    | @rst1 j _ hj _ =>
      have := h.R a b hab (by rw [hlx]; trivial) vs hb
      rw [hlx] at this
      rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;>
        simpa [tgt] using this
    | @rstW j _ hj =>
      have := h.R a b hab (by rw [hlx]; trivial) vs hb
      rw [hlx] at this
      have heq : univ.filter (fun r => vs.length ≤ posn π b r ∧
          Function.update M (π a ⟨j, hj⟩) none r = some b) =
          univ.filter (fun r => vs.length ≤ posn π b r ∧ M r = some b ∧
            r ∉ tgt π a (.rstW j)) := by
        ext r
        simp only [mem_filter, mem_univ, true_and, tgt]
        by_cases hr0 : r = π a ⟨j, hj⟩
        · subst hr0; simp
        · rw [Function.update_of_ne hr0]
          have : posn π a r ≠ j := fun h' => hr0 (eq_of_posn_eq π hj h')
          simp [this]
      rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;>
        simpa [tgt, heq] using this
    | @wait j z _ hj =>
      have := h.R a b hab (by rw [hlx]; trivial) vs hb
      rw [hlx] at this
      rcases afterWait_cases j z (M (π a ⟨j, hj⟩)) with ⟨z', h1⟩ | h1 | h1 <;> rw [h1] at ha ⊢
      · simpa [tgt] using this
      · simp [Pas] at ha
      · simpa [tgt] using this
    | idle =>
      have := h.R a b hab (by rw [hlx]; exact ha) vs hb
      rwa [hlx] at this
    | @scan1 j _ hj _ =>
      rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        simp [Pas] at ha
    | @scanW j _ hj =>
      rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        simp [Pas] at ha
    | @exit j _ hj =>
      rcases nextExit_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at ha <;>
        simp [Pas] at ha
    | scan0 => simp [Pas] at ha
    | retLock => simp [Pas] at ha
    | retUnlock => simp [Pas] at ha
    | invLock => simp [Pas] at ha
    | invUnlock => simp [Pas] at ha
  · subst x
    rw [Function.update_self] at hb
    rw [Function.update_of_ne hab] at ha ⊢
    generalize hlx : loc b = lx at hs
    cases hs with
    | @coll vb _ hj =>
      rcases afterColl_cases (m := m) b (vb ++ [M (π b ⟨vb.length, hj⟩)]) with
        ⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at hb <;> cases hb
      have := h.R a b hab ha vb hlx
      rw [count_append_one]
      have hsub : univ.filter (fun r => vb.length ≤ posn π b r ∧ M r = some b ∧
          r ∉ tgt π a (loc a)) ⊆ univ.filter (fun r =>
            (vb ++ [M (π b ⟨vb.length, hj⟩)]).length ≤ posn π b r ∧ M r = some b ∧
            r ∉ tgt π a (loc a)) ∪
          (if M (π b ⟨vb.length, hj⟩) = some b then {π b ⟨vb.length, hj⟩} else ∅) := by
        intro r hr
        simp only [mem_filter, mem_univ, true_and] at hr
        by_cases hr0 : posn π b r = vb.length
        · have := eq_of_posn_eq π hj hr0
          subst this
          simp [hr.2.1]
        · simp only [mem_union, mem_filter, mem_univ, true_and, List.length_append,
            List.length_cons, List.length_nil]
          left; exact ⟨by omega, hr.2⟩
      have hc := (card_le_card hsub).trans (card_union_le _ _)
      split_ifs at hc ⊢ <;> simp only [card_singleton, card_empty] at hc <;> omega
    | idle => exact h.R a b hab ha vs (by rw [hlx]; exact hb)
    | @scan1 j _ hj h0 =>
      rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨h2, h1⟩ <;> rw [h1] at hb <;>
        cases hb
      have h3 := h.phi a b hab ha
      rw [hlx] at h3
      have h4 := card_le_three (fun c => hP a b c hab) M (tgt π a (loc a))
      have h5 : #(univ.filter (fun r => M r = none)) ≤ gapsS π b (.scan j) M := by
        refine card_le_card fun r hr => ?_
        simp only [mem_filter, mem_univ, true_and] at hr ⊢
        have hr0 : r ≠ π b ⟨j, hj⟩ := fun h' => h0 (h' ▸ hr)
        exact ⟨posn_lt_of_ne hj h2 hr0, hr⟩
      simp only [List.count_nil, List.length_nil, Nat.zero_le, true_and, zero_add]
      unfold thr at h3 ⊢
      omega
    | @scanW j _ hj =>
      rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨h2, h1⟩ <;> rw [h1] at hb <;>
        cases hb
      have h3 := h.phi a b hab ha
      rw [hlx] at h3
      have h4 := card_le_three (fun c => hP a b c hab) (Function.update M (π b ⟨j, hj⟩) (some b))
        (tgt π a (loc a))
      have h5 : #(univ.filter (fun r => Function.update M (π b ⟨j, hj⟩) (some b) r = none)) ≤
          gapsS π b (.scanW j) M := by
        refine card_le_card fun r hr => ?_
        simp only [mem_filter, mem_univ, true_and] at hr ⊢
        have hr0 : r ≠ π b ⟨j, hj⟩ := fun h' => by rw [h'] at hr; simp at hr
        rw [Function.update_of_ne hr0] at hr
        exact ⟨posn_lt_of_ne hj h2 hr0, hr⟩
      have h6 : #(univ.filter (fun r => Function.update M (π b ⟨j, hj⟩) (some b) r = some a ∨
          r ∈ tgt π a (loc a))) ≤ #(univ.filter (fun r => M r = some a ∨ r ∈ tgt π a (loc a))) :=
        card_le_card fun r hr => by
          simp only [mem_filter, mem_univ, true_and] at hr ⊢
          rcases hr with hr | hr
          · exact Or.inl ((TStep.scanW (π := π) (x := b) (M := M) hj).mem_some hab.symm hr)
          · exact Or.inr hr
      simp only [List.count_nil, List.length_nil, Nat.zero_le, true_and, zero_add]
      unfold thr at h3 ⊢
      omega
    | @rst1 j _ hj _ =>
      rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hb <;>
        cases hb
    | @rstW j _ hj =>
      rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hb <;>
        cases hb
    | @exit j _ hj =>
      rcases nextExit_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hb <;>
        cases hb
    | @wait j z _ hj =>
      rcases afterWait_cases j z (M (π b ⟨j, hj⟩)) with ⟨z', h1⟩ | h1 | h1 <;> rw [h1] at hb <;>
        cases hb
    | _ => cases hb

/-- `DFInv` is preserved by every step (two processes). -/
theorem DFInv.step (hP : ∀ a b c : P, a ≠ b → c = a ∨ c = b) (h : DFInv π loc M)
    (hs : TStep m π x (loc x) M l' M') : DFInv π (Function.update loc x l') M' :=
  have hz := h.z_step hP hs
  { own1 := h.own1_step hs
    own2 := h.own2_step hs
    c0 := h.c0_step hs
    z := hz
    cc := h.cc_step hP hs hz
    phi := h.phi_step hP hs
    R := h.R_step hP hs
    nbp := h.nbp_step hP hs }

end Step

variable (π) in
/-- `DFInv` holds in every reachable configuration. -/
theorem dfInv_of_run (hP : ∀ a b c : P, a ≠ b → c = a ∨ c = b) {α : List (Label P mutexObj)}
    {C : Cfg m P} (h : (I m π).run α = some C) : DFInv π C.loc C.mem :=
  Impl.invariant_of_run (Inv := fun C : Cfg m P => DFInv π C.loc C.mem) DFInv.init
    (fun C ℓ C' hC hs => by
      obtain ⟨h1, h2⟩ := step_tstep' hs
      rw [h2]; exact hC.step hP h1) h

end Podc.MemoryAnonymousCoordination.Mutex
