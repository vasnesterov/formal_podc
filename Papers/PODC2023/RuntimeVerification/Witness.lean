import Mathlib
import Papers.PODC2023.RuntimeVerification.Verifier

/-!
# The reported sketch is a history of `A*` (Lemma 8.1 (1), Corollary 7.2)

An execution of `A*` alone (Figure 7) has `L = 6` steps per operation. With input `A` given as an
abstract implementation `𝒜` (a set of histories), an execution is admissible if its history of
`A` belongs to `𝒜`. A history `h` (responses `(y, λ)`) is a *history of `A*`* if it is the history
of `A*` in such an execution.

`sketch_isAStarHist`: for every execution `E` of `V_O` running `A*` (with `A`'s history in a
prefix-closed `𝒜`) and every time `s`, the sketch `X(τ)` of the contents `τ` of `M` at time `s`
is a history of `A*`. In particular every reported witness is a history of `A*`.

Construction (the paper's proof of Lemma 8.1, made explicit): keep the operations appearing in
the views of `τ`; keep the `A`-steps of `E` that happen before the last `N.Snapshot` of a tuple
of `τ`; drop the `N.Snapshot` of operations whose tuple is not in `τ`; and retime: the
invocation/`N.Write` of an operation at the stage of the smallest view containing it, its
`N.Snapshot`/response at the stage of its view, the `A`-steps between, in their original order.
-/

namespace Podc2023.RuntimeVerification

open Cslib.SharedMemory.HerlihyWing Sketch

set_option linter.unusedSectionVars false

variable {n : ℕ} {Op Y : Type} [DecidableEq Op] [DecidableEq Y] [Inhabited Op] [Inhabited Y]

/-- An execution of `A*` (6 steps per operation) with input `𝒜`. -/
def IsAStarExec {T : Type} [LinearOrder T] (𝒜 : Set (Hist (Fin n) Op Y)) (F : Exec n Op Y T) :
    Prop :=
  F.WF ∧ (F.hA 6).toList ∈ 𝒜

/-- `h` is a history of `A*` with input `𝒜`. -/
def IsAStarHist (𝒜 : Set (Hist (Fin n) Op Y)) (h : Hist (Fin n) Op (Y × Finset (IRec n Op))) :
    Prop :=
  ∃ (T : Type) (_ : LinearOrder T) (F : Exec n Op Y T), IsAStarExec 𝒜 F ∧ (F.hS 6).toList = h

namespace Witness

variable (E : Exec n Op Y ℕ) (s : ℕ)

/-- The `j`-th operation of `q` has its tuple in `τ = E.tauAt s`. -/
def InTau (q : Fin n) (j : ℕ) : Prop := 8 * j + 6 < E.len q ∧ E.T q (8 * j + 6) < s

/-- One past the last `N.Snapshot` of a tuple of `τ`. -/
noncomputable def tstar : ℕ := (E.tauAt s).sup fun v => E.T v.p (8 * v.k + 4) + 1

/-- The stage of an `E`-time `u < tstar`: the size of the smallest view of `τ` whose snapshot is
not before `u`. -/
noncomputable def win (u : ℕ) : ℕ :=
  sInf {c | ∃ q j, InTau E s q j ∧ u ≤ E.T q (8 * j + 4) ∧ (E.view 8 q j).card = c}

/-- The new time of the step `j` of the `k`-th operation of `p`. -/
noncomputable def ftime (p : Fin n) (k : ℕ) : ℕ → TX
  | 0 => lex3 (sInv (E.tauAt s) p k) 0 (rank p k)
  | 1 => lex3 (sInv (E.tauAt s) p k) 1 (rank p k)
  | 2 => lex3 (win E s (E.T p (8 * k + 2))) 2 (E.T p (8 * k + 2))
  | 3 => lex3 (win E s (E.T p (8 * k + 3))) 2 (E.T p (8 * k + 3))
  | 4 => lex3 (E.view 8 p k).card 3 (rank p k)
  | _ => lex3 (E.view 8 p k).card 4 (rank p k)

/-- The step `8k + j` of `p` happens before `tstar`. -/
def Early (p : Fin n) (k j : ℕ) : Prop := 8 * k + j < E.len p ∧ E.T p (8 * k + j) < tstar E s

open Classical in
/-- Number of steps of `p` in the witness execution. -/
noncomputable def flen (p : Fin n) : ℕ :=
  6 * (XTH (E.tauAt s)).c p +
    if (XTH (E.tauAt s)).c p < (XTH (E.tauAt s)).m p then
      2 + (if Early E s p ((XTH (E.tauAt s)).c p) 2 then 1 else 0) +
        (if Early E s p ((XTH (E.tauAt s)).c p) 3 then 1 else 0)
    else 0

/-- The witness execution of `A*`. -/
noncomputable def F : Exec n Op Y TX where
  len := flen E s
  op := E.op
  y := E.y
  T p i := ftime E s p (i / 6) (i % 6)

/-- The step `j` of the `k`-th operation of `p` is a step of `F`. -/
def Incl (p : Fin n) (k j : ℕ) : Prop :=
  k < (XTH (E.tauAt s)).c p ∨ (k < (XTH (E.tauAt s)).m p ∧
    (j < 2 ∨ (j = 2 ∧ Early E s p k 2) ∨ (j = 3 ∧ Early E s p k 3)))

variable {E s}

theorem F_T (p : Fin n) {k j : ℕ} (hj : j < 6) : (F E s).T p (6 * k + j) = ftime E s p k j := by
  show ftime E s p ((6 * k + j) / 6) ((6 * k + j) % 6) = _
  rw [show (6 * k + j) / 6 = k by omega, show (6 * k + j) % 6 = j by omega]

theorem lt_tstar {u : ℕ} : u < tstar E s ↔ ∃ q j, InTau E s q j ∧ u ≤ E.T q (8 * j + 4) := by
  rw [tstar, Finset.lt_sup_iff]
  constructor
  · rintro ⟨v, hv, hu⟩
    obtain ⟨q, j, h1, h2, rfl⟩ := Exec.mem_tauAt.1 hv
    exact ⟨q, j, ⟨h1, h2⟩, by simp only [Exec.tup] at hu; omega⟩
  · rintro ⟨q, j, ⟨h1, h2⟩, hu⟩
    exact ⟨_, Exec.mem_tauAt.2 ⟨q, j, h1, h2, rfl⟩, by simp only [Exec.tup]; omega⟩

theorem tup_mem {q : Fin n} {j : ℕ} (h : InTau E s q j) : E.tup q j ∈ E.tauAt s :=
  Exec.mem_tauAt.2 ⟨q, j, h.1, h.2, rfl⟩

theorem lt_c_iff' (hw : E.WF) {p : Fin n} {k : ℕ} : k < (XTH (E.tauAt s)).c p ↔ InTau E s p k := by
  rw [lt_c_iff (Exec.valid_tauAt hw s)]
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩
    obtain ⟨q, j, h1, h2, rfl⟩ := Exec.mem_tauAt.1 ht
    exact ⟨h1, h2⟩
  · intro h
    exact ⟨_, tup_mem h, rfl, rfl⟩

theorem lt_m_iff' (hw : E.WF) {p : Fin n} {k : ℕ} :
    k < (XTH (E.tauAt s)).m p ↔ (p, k, E.op p k) ∈ allInv (E.tauAt s) := by
  rw [lt_m_iff (Exec.valid_tauAt hw s)]
  constructor
  · rintro ⟨x, hx, rfl, rfl⟩
    have := Exec.op_of_mem_allInv hx
    obtain ⟨a, b, c⟩ := x
    simp only at this
    subst this
    exact hx
  · intro h
    exact ⟨_, h, rfl, rfl⟩

theorem intau_early (hw : E.WF) {p : Fin n} {k : ℕ} (h : InTau E s p k) {j : ℕ} (hj : j < 5) :
    Early E s p k j := by
  refine ⟨by have := h.1; omega, ?_⟩
  refine lt_tstar.2 ⟨p, k, h, ?_⟩
  rcases Nat.lt_or_ge j 4 with h4 | h4
  · exact (hw.mono _ _ _ (by omega) (by have := h.1; omega)).le
  · rw [show j = 4 by omega]

/-- The key fact: an operation is visible iff its `N.Write` happens before `tstar`. -/
theorem vis_iff (hw : E.WF) {p : Fin n} {k : ℕ} :
    k < (XTH (E.tauAt s)).m p ↔ Early E s p k 1 := by
  rw [lt_m_iff' hw, Exec.mem_allInv_tauAt]
  constructor
  · rintro ⟨q, j, h1, h2, h3, h4, -⟩
    exact ⟨h3, lt_tstar.2 ⟨q, j, ⟨h1, h2⟩, h4.le⟩⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨q, j, ⟨h3, h4⟩, h5⟩ := lt_tstar.1 h2
    refine ⟨q, j, h3, h4, h1, lt_of_le_of_ne h5 ?_, rfl⟩
    exact Exec.T_ne hw (by norm_num) (by norm_num) (by norm_num) h1 (by omega)

theorem early_mono (hw : E.WF) {p : Fin n} {k j j' : ℕ} (hjj : j ≤ j') (h : Early E s p k j') :
    Early E s p k j := by
  refine ⟨by have := h.1; omega, ?_⟩
  rcases hjj.lt_or_eq with h' | h'
  · exact lt_trans (hw.mono _ _ _ (by omega) h.1) h.2
  · subst h'; exact h.2

theorem c_le_m (hw : E.WF) (p : Fin n) : (XTH (E.tauAt s)).c p ≤ (XTH (E.tauAt s)).m p :=
  (XTH_WF (Exec.valid_tauAt hw s)).c_le_m p

theorem m_le_c (hw : E.WF) (p : Fin n) : (XTH (E.tauAt s)).m p ≤ (XTH (E.tauAt s)).c p + 1 :=
  (XTH_WF (Exec.valid_tauAt hw s)).m_le_c p

theorem len_aux {c m k j : ℕ} (hj : j < 6) (A B : Prop) [Decidable A] [Decidable B] (hBA : B → A)
    (hcm : c ≤ m) (hmc : m ≤ c + 1) :
    6 * k + j < 6 * c + (if c < m then 2 + (if A then 1 else 0) + (if B then 1 else 0) else 0) ↔
      k < c ∨ (k < m ∧ (j < 2 ∨ (j = 2 ∧ A) ∨ (j = 3 ∧ B))) := by
  rcases Nat.lt_trichotomy k c with h | rfl | h
  · simp only [h, true_or, iff_true]
    split_ifs <;> omega
  · simp only [lt_irrefl, false_or]
    by_cases hkm : k < m
    · simp only [hkm, ite_true, true_and]
      by_cases hA : A <;> by_cases hB : B <;>
        simp only [hA, hB, ite_true, ite_false, and_true, and_false, or_false] <;>
        constructor <;> intro h <;> first | omega | exact absurd (hBA hB) hA
    · simp only [hkm, ite_false, false_and, iff_false]
      omega
  · have : ¬ k < c := by omega
    simp only [this, false_or]
    constructor
    · intro h'; exfalso; split_ifs at h' <;> omega
    · rintro ⟨h1, -⟩; omega

theorem lt_flen (hw : E.WF) (p : Fin n) {k j : ℕ} (hj : j < 6) :
    6 * k + j < flen E s p ↔ Incl E s p k j := by
  classical
  rw [flen, Incl]
  have := len_aux (c := (XTH (E.tauAt s)).c p) (m := (XTH (E.tauAt s)).m p) (k := k) hj
    (Early E s p ((XTH (E.tauAt s)).c p) 2) (Early E s p ((XTH (E.tauAt s)).c p) 3)
    (early_mono hw (by norm_num)) (c_le_m hw p) (m_le_c hw p)
  convert this using 1
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · rcases Nat.lt_or_ge k ((XTH (E.tauAt s)).c p) with h | h
      · exact Or.inl h
      · have : k = (XTH (E.tauAt s)).c p := by have := m_le_c (s := s) hw p; omega
        subst this
        exact Or.inr ⟨h1, h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · rcases Nat.lt_or_ge k ((XTH (E.tauAt s)).c p) with h | h
      · exact Or.inl h
      · have : k = (XTH (E.tauAt s)).c p := by have := m_le_c (s := s) hw p; omega
        subst this
        exact Or.inr ⟨h1, h2⟩

theorem win_spec {u : ℕ} (hu : u < tstar E s) :
    ∃ q j, InTau E s q j ∧ u ≤ E.T q (8 * j + 4) ∧ (E.view 8 q j).card = win E s u := by
  obtain ⟨q, j, h1, h2⟩ := lt_tstar.1 hu
  exact Nat.sInf_mem (s := {c | ∃ q j, InTau E s q j ∧ u ≤ E.T q (8 * j + 4) ∧
    (E.view 8 q j).card = c}) ⟨_, q, j, h1, h2, rfl⟩

theorem win_le {u : ℕ} {q : Fin n} {j : ℕ} (h1 : InTau E s q j) (h2 : u ≤ E.T q (8 * j + 4)) :
    win E s u ≤ (E.view 8 q j).card :=
  Nat.sInf_le ⟨q, j, h1, h2, rfl⟩

theorem win_mono {u u' : ℕ} (hu : u ≤ u') (hu' : u' < tstar E s) : win E s u ≤ win E s u' := by
  obtain ⟨q, j, h1, h2, h3⟩ := win_spec hu'
  rw [← h3]
  exact win_le h1 (hu.trans h2)

theorem sInv_le_win (hw : E.WF) {p : Fin n} {k : ℕ} (h : Early E s p k 2) :
    sInv (E.tauAt s) p k ≤ win E s (E.T p (8 * k + 2)) := by
  obtain ⟨q, j, h1, h2, h3⟩ := win_spec h.2
  rw [← h3]
  have hx : (p, k, E.op p k) ∈ (E.tup q j).view := by
    simp only [Exec.tup]
    rw [Exec.mem_view8]
    dsimp only
    exact ⟨by have := h.1; omega, lt_of_lt_of_le (hw.mono _ _ _ (by omega) h.1) h2, rfl⟩
  exact sInv_le (tup_mem h1) hx

theorem incl_vis (hw : E.WF) {p : Fin n} {k j : ℕ} (h : Incl E s p k j) :
    k < (XTH (E.tauAt s)).m p := by
  rcases h with h | ⟨h, -⟩
  · exact lt_of_lt_of_le h (c_le_m hw p)
  · exact h

theorem incl_early (hw : E.WF) {p : Fin n} {k j : ℕ} (h : Incl E s p k j) (hj : j < 4) :
    Early E s p k j ∨ j < 2 := by
  rcases h with h | ⟨-, h | ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
  · exact Or.inl (intau_early hw ((lt_c_iff' hw).1 h) (by omega))
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inl h

theorem incl_tau {p : Fin n} {k j : ℕ} (h : Incl E s p k j) (hj : 4 ≤ j) :
    k < (XTH (E.tauAt s)).c p := by
  rcases h with h | ⟨-, h | ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
  · exact h
  all_goals omega

theorem ftime_succ (hw : E.WF) {p : Fin n} {k j : ℕ} (hj : j < 5) (h : Incl E s p k (j + 1)) :
    ftime E s p k j < ftime E s p k (j + 1) := by
  interval_cases j
  · simp [ftime]
  · have he : Early E s p k 2 := by
      rcases incl_early hw h (by norm_num) with h | h
      · exact h
      · omega
    have := sInv_le_win hw he
    simp only [ftime, lex3_lt]
    omega
  · have he : Early E s p k 3 := by
      rcases incl_early hw h (by norm_num) with h | h
      · exact h
      · omega
    have h23 := hw.mono p (8 * k + 2) (8 * k + 3) (by omega) he.1
    have := win_mono h23.le he.2
    simp only [ftime, lex3_lt, true_and]
    omega
  · have ht := (lt_c_iff' hw).1 (incl_tau h (by norm_num))
    have := win_le (s := s) ht (hw.mono p (8 * k + 3) (8 * k + 4) (by omega) (by have := ht.1; omega)).le
    simp only [ftime, lex3_lt]
    omega
  · simp [ftime]

theorem ftime_next (hw : E.WF) {p : Fin n} {k : ℕ} (h : Incl E s p (k + 1) 0) :
    ftime E s p k 5 < ftime E s p (k + 1) 0 := by
  have hv := Exec.valid_tauAt hw s
  have hm := incl_vis hw h
  have hc : k < (XTH (E.tauAt s)).c p := by have := m_le_c (s := s) hw p; omega
  have ht := (lt_c_iff' hw).1 hc
  have hx := (lt_m_iff' hw).1 hm
  have h1 := (vis_iff hw).1 hm
  have key := (card_lt_sInv_iff hv (tup_mem ht) hx).2 (by
    simp only [Exec.tup]
    rw [Exec.mem_view8]
    rintro ⟨-, h2, -⟩
    have := hw.mono p (8 * k + 4) (8 * (k + 1) + 1) (by omega) h1.1
    exact lt_asymm h2 this)
  simp only [Exec.tup] at key
  simp only [ftime, lex3_lt]
  exact Or.inl key

theorem F_T_succ (hw : E.WF) {p : Fin n} {i : ℕ} (h : i + 1 < (F E s).len p) :
    (F E s).T p i < (F E s).T p (i + 1) := by
  obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 6 ∧ i = 6 * k + j := ⟨i / 6, i % 6, by omega, by omega⟩
  change _ < flen E s p at h
  rcases Nat.lt_or_ge j 5 with hj5 | hj5
  · rw [show 6 * k + j + 1 = 6 * k + (j + 1) by omega] at h ⊢
    rw [F_T p hj, F_T p (by omega)]
    exact ftime_succ hw hj5 ((lt_flen hw p (by omega)).1 h)
  · obtain rfl : j = 5 := by omega
    rw [show 6 * k + 5 + 1 = 6 * (k + 1) + 0 by omega] at h ⊢
    rw [F_T p hj, F_T p (by omega)]
    exact ftime_next hw ((lt_flen hw p (by omega)).1 h)

theorem ftime_inj (hw : E.WF) {p q : Fin n} {k k' j j' : ℕ} (hj : j < 6) (hj' : j' < 6)
    (h : Incl E s p k j) (h' : Incl E s q k' j') (he : ftime E s p k j = ftime E s q k' j') :
    p = q ∧ k = k' ∧ j = j' := by
  have hT : ∀ (j j' : ℕ), 2 ≤ j → j < 4 → 2 ≤ j' → j' < 4 → Incl E s p k j → Incl E s q k' j' →
      E.T p (8 * k + j) = E.T q (8 * k' + j') → p = q ∧ k = k' ∧ j = j' := by
    intro j j' h1 h2 h3 h4 h h' he
    have e1 := incl_early hw h h2
    have e2 := incl_early hw h' h4
    obtain ⟨rfl, h5⟩ := hw.inj p q _ _ (e1.resolve_right (by omega)).1
      (e2.resolve_right (by omega)).1 he
    exact ⟨rfl, by omega, by omega⟩
  interval_cases j <;> interval_cases j' <;> simp [ftime, lex3_inj] at he
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := rank_inj he.2; exact ⟨rfl, rfl, rfl⟩)
    | exact hT _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) h h' he.2

theorem F_WF (hw : E.WF) : (F E s).WF where
  mono p i j hij hj := by
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact lt_trans (ih h (by omega)) (F_T_succ hw hj)
      · subst h; exact F_T_succ hw hj
  inj p q i i' hi hi' he := by
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 6 ∧ i = 6 * k + j := ⟨i / 6, i % 6, by omega, by omega⟩
    obtain ⟨k', j', hj', rfl⟩ : ∃ k j, j < 6 ∧ i' = 6 * k + j :=
      ⟨i' / 6, i' % 6, by omega, by omega⟩
    rw [F_T p hj, F_T q hj'] at he
    obtain ⟨rfl, rfl, rfl⟩ := ftime_inj hw hj hj' ((lt_flen hw p hj).1 hi)
      ((lt_flen hw q hj').1 hi') he
    exact ⟨rfl, rfl⟩

theorem incl_lt2_iff (hw : E.WF) {p : Fin n} {k j : ℕ} (hj : j < 2) :
    Incl E s p k j ↔ k < (XTH (E.tauAt s)).m p :=
  ⟨incl_vis hw, fun h => Or.inr ⟨h, Or.inl hj⟩⟩

theorem incl_ge4_iff {p : Fin n} {k j : ℕ} (hj : 4 ≤ j) :
    Incl E s p k j ↔ k < (XTH (E.tauAt s)).c p :=
  ⟨fun h => incl_tau h hj, Or.inl⟩

theorem incl_A_iff (hw : E.WF) {p : Fin n} {k j : ℕ} (hj : j = 2 ∨ j = 3) :
    Incl E s p k j ↔ Early E s p k j := by
  constructor
  · intro h
    exact (incl_early hw h (by omega)).resolve_right (by omega)
  · intro h
    have hv := (vis_iff hw).2 (early_mono hw (by omega) h)
    rcases hj with rfl | rfl
    · exact Or.inr ⟨hv, Or.inr (Or.inl ⟨rfl, h⟩)⟩
    · exact Or.inr ⟨hv, Or.inr (Or.inr ⟨rfl, h⟩)⟩

theorem mem_view_iff (hw : E.WF) {p q : Fin n} {k j : ℕ} {o : Op} (hk : InTau E s p k) :
    (q, j, o) ∈ E.view 8 p k ↔
      j < (XTH (E.tauAt s)).m q ∧ sInv (E.tauAt s) q j ≤ (E.view 8 p k).card ∧ o = E.op q j := by
  have hv := Exec.valid_tauAt hw s
  have ht := tup_mem hk
  constructor
  · intro hx
    have hx' : (q, j, o) ∈ allInv (E.tauAt s) := mem_allInv.2 ⟨_, ht, hx⟩
    have ho : o = E.op q j := Exec.op_of_mem_allInv hx'
    subst ho
    exact ⟨(lt_m_iff' hw).2 hx', sInv_le ht hx, rfl⟩
  · rintro ⟨h1, h2, rfl⟩
    have hx := (lt_m_iff' hw).1 h1
    by_contra hn
    have := (card_lt_sInv_iff hv ht hx).2 hn
    exact absurd h2 (by simp only [Exec.tup] at this; omega)

theorem F_view (hw : E.WF) {p : Fin n} {k : ℕ} (hk : InTau E s p k) :
    (F E s).view 6 p k = E.view 8 p k := by
  ext ⟨q, j, o⟩
  rw [Exec.mem_view (by norm_num), mem_view_iff hw hk]
  dsimp only
  rw [show (F E s).len q = flen E s q from rfl, lt_flen hw q (by norm_num),
    incl_lt2_iff hw (by norm_num), F_T q (by norm_num), F_T p (by norm_num)]
  simp only [ftime, lex3_lt]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by omega, h3⟩

theorem hS_m (hw : E.WF) (p : Fin n) : ((F E s).hS 6).m p = (XTH (E.tauAt s)).m p := by
  show cnt 6 0 (flen E s p) = _
  apply Exec.eq_of_lt_iff
  intro k
  rw [lt_cnt (by norm_num), lt_flen hw p (by norm_num), incl_lt2_iff hw (by norm_num)]

theorem hS_c (hw : E.WF) (p : Fin n) : ((F E s).hS 6).c p = (XTH (E.tauAt s)).c p := by
  show cnt 6 5 (flen E s p) = _
  apply Exec.eq_of_lt_iff
  intro k
  rw [lt_cnt (by norm_num), lt_flen hw p (by norm_num), incl_ge4_iff (by norm_num)]

theorem X_tr (hw : E.WF) {p : Fin n} {k : ℕ} (hk : InTau E s p k) :
    (XTH (E.tauAt s)).tr p k = lex3 (E.view 8 p k).card 1 (rank p k) := by
  have := res_eq (Exec.valid_tauAt hw s) (tup_mem hk)
  simp only [Exec.tup] at this
  show lex3 (resOf' (E.tauAt s) p k).2.card 1 (rank p k) = _
  rw [show resOf' (E.tauAt s) p k = _ from this]

theorem hS_eq (hw : E.WF) : ((F E s).hS 6).toList = (XTH (E.tauAt s)).toList := by
  have hv := Exec.valid_tauAt hw s
  have hwS : ((F E s).hS 6).WF := Exec.proj_WF (F_WF hw) _ (by norm_num) (by norm_num)
  refine TH.toList_eq_of_iso (h := (F E s).hS 6) (h' := XTH (E.tauAt s)) hwS (XTH_WF hv)
    (hS_m hw) (hS_c hw) ?_ ?_ ?_
  · intro p k hk
    rw [hS_m hw, lt_m_iff' hw] at hk
    exact (op_eq hv hk).symm
  · intro p k hk
    rw [hS_c hw, lt_c_iff' hw] at hk
    have := res_eq hv (tup_mem hk)
    simp only [Exec.tup] at this
    rw [this]
    show (E.y p k, (F E s).view 6 p k) = _
    rw [F_view hw hk]
  · rintro ⟨p, k, b⟩ ⟨q, j, b'⟩ hx hy
    have ti : ∀ p k, ((F E s).hS 6).ti p k = (XTH (E.tauAt s)).ti p k := fun p k => by
      show (F E s).T p (6 * k + 0) = _
      rw [F_T p (by norm_num)]; rfl
    have tr : ∀ p k, ((F E s).hS 6).tr p k = lex3 (E.view 8 p k).card 4 (rank p k) := fun p k => by
      show (F E s).T p (6 * k + 5) = _
      rw [F_T p (by norm_num)]; rfl
    cases b <;> cases b' <;>
      simp only [TH.time, TH.Valid, Bool.false_eq_true, ite_true, ite_false, hS_c hw,
        lt_c_iff' hw] at hx hy ⊢
    · rw [ti, ti]
    · rw [ti, tr, X_tr hw hy]
      simp only [XTH, lex3_lt]; omega
    · rw [ti, tr, X_tr hw hx]
      simp only [XTH, lex3_lt]; omega
    · rw [tr, tr, X_tr hw hx, X_tr hw hy]
      simp [lex3_lt]

theorem hA_eq (hw : E.WF) :
    ((E.hA 8).cut (tstar E s)).toList = ((F E s).hA 6).toList := by
  have hwA : (E.hA 8).WF := Exec.proj_WF hw _ (by norm_num) (by norm_num)
  have hwF : ((F E s).hA 6).WF := Exec.proj_WF (F_WF hw) _ (by norm_num) (by norm_num)
  refine TH.toList_eq_of_iso (h := (E.hA 8).cut (tstar E s)) (h' := (F E s).hA 6) (hwA.cut _) hwF
    ?_ ?_ ?_ ?_ ?_
  · intro p
    apply Exec.eq_of_lt_iff
    intro k
    rw [TH.cut_m_iff hwA]
    show k < cnt 8 2 (E.len p) ∧ E.T p (8 * k + 2) < tstar E s ↔ k < cnt 6 2 (flen E s p)
    rw [lt_cnt (by norm_num), lt_cnt (by norm_num), lt_flen hw p (by norm_num),
      incl_A_iff hw (by norm_num)]
    rfl
  · intro p
    apply Exec.eq_of_lt_iff
    intro k
    rw [TH.cut_c_iff hwA]
    show k < cnt 8 3 (E.len p) ∧ E.T p (8 * k + 3) < tstar E s ↔ k < cnt 6 3 (flen E s p)
    rw [lt_cnt (by norm_num), lt_cnt (by norm_num), lt_flen hw p (by norm_num),
      incl_A_iff hw (by norm_num)]
    rfl
  · intro _ _ _; rfl
  · intro _ _ _; rfl
  · have hmono : StrictMonoOn (fun u => lex3 (win E s u) 2 u) (Set.Iio (tstar E s)) := by
      intro u hu u' hu' huu
      have := win_mono (s := s) huu.le hu'
      simp only [lex3_lt, true_and]
      omega
    have ht : ∀ x, ((F E s).hA 6).time x =
        (fun u => lex3 (win E s u) 2 u) (((E.hA 8).cut (tstar E s)).time x) := by
      rintro ⟨p, k, b⟩
      cases b
      · show (F E s).T p (6 * k + 2) = _
        rw [F_T p (by norm_num)]; rfl
      · show (F E s).T p (6 * k + 3) = _
        rw [F_T p (by norm_num)]; rfl
    intro x y hx hy
    rw [ht, ht]
    exact (hmono.lt_iff_lt ((TH.valid_cut_iff hwA _ x).1 hx).2
      ((TH.valid_cut_iff hwA _ y).1 hy).2).symm

end Witness

/-- **Lemma 8.1 (1).** The sketch of the contents of `M` at any time is a history of `A*`. -/
theorem sketch_isAStarHist {𝒜 : Set (Hist (Fin n) Op Y)} (h𝒜 : ∀ h ∈ 𝒜, ∀ h', h' <+: h → h' ∈ 𝒜)
    {E : Exec n Op Y ℕ} (hw : E.WF) (hA : (E.hA 8).toList ∈ 𝒜) (s : ℕ) :
    IsAStarHist 𝒜 (XTH (E.tauAt s)).toList := by
  refine ⟨TX, inferInstance, Witness.F E s, ⟨Witness.F_WF hw, ?_⟩, Witness.hS_eq hw⟩
  rw [← Witness.hA_eq hw]
  exact h𝒜 _ hA _ (TH.toList_cut_prefix (Exec.proj_WF hw _ (by norm_num) (by norm_num)) _)

end Podc2023.RuntimeVerification
