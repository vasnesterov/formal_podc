import Papers.PODC2025.LanguageDecidability.Timed
import Papers.PODC2025.LanguageDecidability.CounterCex
import Papers.PODC2025.LanguageDecidability.CounterAWords

/-!
# Counters against the timed adversary (Lemma 6.2, Lemma 6.4 / Figure 9)

* `lemma_6_2` — **Lemma 6.2** for `WEC_COUNT` and `SEC_COUNT`, every `n ≥ 2` (words of
  `CounterAWords.lean`).
* `lemma_6_2_WEC` — the same for `WEC_COUNT`, `n = 2`, with a self-contained word: no algorithm predictively strongly decides
  `WEC_COUNT` (`n = 2`), even with the weaker Definition 6.1 of `Timed.lean`. As for Lemma 5.2,
  the word of the paper's proof is unsuitable (it violates property (1)); we use the word
  "`p₀` reads `0` forever, `p₁` reads `1` forever" (not in `WEC_COUNT`: no increments, yet `p₁`
  reads `1`), which is a limit of words of `WEC_COUNT` (`p₀` increments in round `m` and reads `1`
  afterwards). On tight executions the sketch is the input, so predictive strong decidability
  is strong decidability there (`Timed.psd_closed`).
* `fig9_fails` — the algorithm of **Figure 9** (proof of Lemma 6.4) has the bug of Figure 5:
  in the tight execution of `x5 ∈ SEC_COUNT` (whose sketch is `x5` itself) process `p₀` sets
  its flag in its first iteration (an `inc`) and reports `NO` forever; so Figure 9 does not
  predictively weakly decide `SEC_COUNT`, even with the weaker Definition 6.2.
-/

namespace Podc2025.LanguageDecidability.Counter

open Podc2025.LanguageDecidability Podc2025.LanguageDecidability.Timed

/-! ### Lemma 6.2 for `WEC_COUNT` -/

lemma oi_single (m : ℕ) : ∀ j, oi (fun j => decide (j = m)) j = if m < j then 1 else 0
  | 0 => rfl
  | j + 1 => by
    rw [oi, oi_single m j]
    by_cases h : j = m
    · subst h; simp
    · by_cases h' : m < j
      · simp [h, h', show m < j + 1 by omega]
      · simp [h, h', show ¬ m < j + 1 by omega]

/-- `p₀` reads `0` forever, `p₁` reads `1` forever. -/
def xBad : CWord 2 := fam (fun _ => false) (fun _ => 0) 1

/-- `p₀` reads `0` up to round `m`, increments in round `m` and reads `1` afterwards; `p₁` reads
`1` forever. -/
def yGood (m : ℕ) : CWord 2 := fam (fun j => decide (j = m)) (fun j => if j ≤ m then 0 else 1) 1

lemma incs_xBad : ∀ N, incs xBad N = 0
  | 0 => rfl
  | N + 1 => by
    rw [incs, incs_xBad N]
    have : ¬ IsInc (xBad N) := by
      rw [xBad, isInc_fam]; simp
    simp [this]

lemma xBad_not_mem : xBad ∉ (WEC : Set (CWord 2)) := by
  rintro ⟨-, -, -, -, S, ⟨N, hN, -⟩, hev⟩
  rw [incs_xBad] at hN
  subst hN
  exact not_evReads_fam _ _ _ (by norm_num) hev

lemma yGood_mem (m : ℕ) : yGood m ∈ (WEC : Set (CWord 2)) := by
  refine ⟨wf_fam _ _ _, typed_fam _ _ _, wec1_fam _ _ _ ?_, wec2_fam _ _ _ ?_, ?_⟩
  · intro j _
    rw [oi_single]
    split_ifs <;> omega
  · intro j j' _ _ _
    split_ifs <;> omega
  · refine ⟨oi (fun j => decide (j = m)) (m + 1), finIncs_fam _ _ _ fun j hj => by
      simp; omega, 4 * (m + 1), fun r p v hr h => ?_⟩
    rw [oi_single]
    rcases fam_val _ _ _ h with ⟨h1, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · simp [show ¬ r / 4 ≤ m by omega, show m < m + 1 by omega]
    · simp

lemma yGood_agree (m : ℕ) : ∀ i < 4 * m, yGood m i = xBad i := by
  intro i hi
  obtain ⟨j, k, hk, rfl⟩ := fam_decomp i
  have hj : j < m := by omega
  simp only [yGood, xBad]
  interval_cases k
  · rw [add_zero, fam0, fam0]; simp [show j ≠ m by omega]
  · rw [fam1, fam1]; simp [show j ≠ m by omega, show j ≤ m by omega]
  · rw [fam2, fam2]
  · rw [fam3, fam3]

/-- **Lemma 6.2** (`WEC_COUNT ∉ PSD`), for `n = 2` and the weaker Definition 6.1. -/
theorem lemma_6_2_WEC : ¬ Timed.PSD (WEC : Set (CWord 2)) := by
  rintro ⟨V, hV⟩
  exact psd_closed hV isDistLang_WEC (wf_fam _ _ _) xBad_not_mem fun k =>
    ⟨yGood k, yGood_mem k, fun i hi => yGood_agree k i (by omega)⟩

/-- **Lemma 6.2** (`WEC_COUNT, SEC_COUNT ∉ PSD`) for every `n ≥ 2`, with the weaker
Definition 6.1. Word: `p₀` increments, then reads `1` forever, all other processes read `0`
forever (not in `WEC_COUNT`); it is a limit of words of `SEC_COUNT ⊆ WEC_COUNT` in which the
other processes eventually read `1` (`CounterAWords.lean`). -/
theorem lemma_6_2 {n : ℕ} (hn2 : 1 < n) :
    ¬ Timed.PSD (WEC : Set (CWord n)) ∧ ¬ Timed.PSD (SEC : Set (CWord n)) := by
  have hn : 0 < n := by omega
  have happ : ∀ k, ∃ y ∈ (SEC : Set (CWord n)), ∀ m < k, y m = cw hn (gBad (n := n)) m :=
    fun k => ⟨cw hn (gGood k), cw_good_mem hn k, fun m hm => cw_good_agree hn k m (by omega)⟩
  refine ⟨fun ⟨V, hV⟩ => psd_closed hV isDistLang_WEC (cw_wf hn _) (cw_bad_not_mem hn2) fun k => ?_,
    fun ⟨V, hV⟩ => psd_closed hV isDistLang_SEC (cw_wf hn _)
      (fun h => cw_bad_not_mem hn2 h.1) happ⟩
  obtain ⟨y, hy, h⟩ := happ k
  exact ⟨y, hy.1, h⟩

/-! ### Figure 9 -/

section fig9

variable {n : ℕ}

/-- Counter alphabets. -/
abbrev CI : Fin n → Type := fun _ => CInv
/-- Counter alphabets. -/
abbrev CO : Fin n → Type := fun _ => CRes

/-- Triples `(vⱼ, wⱼ, viewⱼ)` stored in `M`. -/
abbrev Trip (n : ℕ) := CInv × CRes × View (n := n) CI CO

/-- Number of `inc` invocations in a view. -/
def incCount (vw : View (n := n) CI CO) : ℕ := ∑ q, (vw q).countP fun a => decide (IsInc a)

/-- The fourth clause of Line 06 of Figure 9: some `read` returned more than the number of
`inc`s in its view. -/
def fourth (M : Fin n → List (Trip n)) : Bool :=
  (List.finRange n).any fun q => (M q).any fun tr =>
    tr.1 == .read && match tr.2.1 with
      | .val r => decide (incCount tr.2.2 < r)
      | .ack => false

/-- Lines 01–02 of Figure 9 (as in Figure 5). -/
def pre9 (t : ℕ) (p : Fin n) (l : Loc × List (Trip n)) (v : CInv)
    (m : (Fin n → ℕ) × (Fin n → List (Trip n))) :
    (Loc × List (Trip n)) × ((Fin n → ℕ) × (Fin n → List (Trip n))) :=
  (((pre5 t p l.1 v m.1).1, l.2), ((pre5 t p l.1 v m.1).2, m.2))

/-- Lines 05–06 of Figure 9, literally. -/
def post9 (_t : ℕ) (p : Fin n) (l : Loc × List (Trip n)) (wv : CRes × View (n := n) CI CO)
    (m : (Fin n → ℕ) × (Fin n → List (Trip n))) :
    (Loc × List (Trip n)) × ((Fin n → ℕ) × (Fin n → List (Trip n))) × Verdict :=
  let currIncs := ∑ j, m.1 j
  let currRead := match wv.1 with
    | .val r => r
    | .ack => l.1.currRead
  let sl := l.2 ++ [(l.1.inv, wv.1, wv.2)]
  let M' := Function.update m.2 p sl
  let l' : Loc := { l.1 with currRead := currRead, prevRead := currRead, prevIncs := currIncs }
  if l.1.flag then ((l', sl), (m.1, M'), .no)
  else if currRead < m.1 p ∨ currRead < l.1.prevRead then
    (({ l' with flag := true }, sl), (m.1, M'), .no)
  else if currRead ≠ currIncs ∨ l.1.prevIncs < currIncs then ((l', sl), (m.1, M'), .no)
  else if fourth M' then ((l', sl), (m.1, M'), .no)
  else ((l', sl), (m.1, M'), .yes)

/-- The algorithm of Figure 9 (against `A_τ`). -/
def fig9Alg : Alg n CI (TO CI CO) Verdict where
  L := Loc × List (Trip n)
  M := (Fin n → ℕ) × (Fin n → List (Trip n))
  m0 := (fun _ => 0, fun _ => [])
  l0 := fun _ => ({}, [])
  pre := pre9
  post := post9

lemma flag9_step (s : ℕ → TEv (n := n) CI CO) (t : ℕ) (p : Fin n)
    (h : (((trun fig9Alg s t).loc p).1).flag = true) :
    (((trun fig9Alg s (t + 1)).loc p).1).flag = true := by
  simp only [trun]
  cases hs : s t with
  | pre q v =>
    simp only [TEv.toEv, Alg.next]
    by_cases hq : p = q
    · subst hq; rw [Function.update_self]
      cases v <;> simpa [fig9Alg, pre9, pre5] using h
    · rw [Function.update_of_ne hq]; exact h
  | post q w vw =>
    simp only [TEv.toEv, Alg.next]
    by_cases hq : p = q
    · subst hq; rw [Function.update_self]
      simp only [fig9Alg, post9] at h ⊢
      simp [h]
    · rw [Function.update_of_ne hq]; exact h
  | send q v => exact h
  | tw q v => exact h
  | ts q w => exact h
  | recv q w vw => exact h

lemma flag9_mono (s : ℕ → TEv (n := n) CI CO) {t : ℕ} (p : Fin n)
    (h : (((trun fig9Alg s t).loc p).1).flag = true) :
    ∀ t', t ≤ t' → (((trun fig9Alg s t').loc p).1).flag = true := by
  intro t' ht'
  induction ht' with
  | refl => exact h
  | step _ ih => exact flag9_step s _ p ih

lemma touts9_of_flag (s : ℕ → TEv (n := n) CI CO) {t : ℕ} {p : Fin n} {w : CRes}
    {vw : View (n := n) CI CO} (h : (((trun fig9Alg s t).loc p).1).flag = true)
    (hs : s t = .post p w vw) : touts fig9Alg s t = some (p, .no) := by
  simp only [touts, hs, TEv.toEv, Alg.next]
  simp only [fig9Alg, post9] at h ⊢
  simp [h]

end fig9

/-- In the tight execution of `x5`, process `p₀` sets its flag in its first iteration. -/
lemma flag9_x5 : (((trun (fig9Alg (n := 2)) (tcanon x5) 6).loc 0).1).flag = true := by
  decide

/-- **Figure 9 is wrong**: in the tight execution of `x5 ∈ SEC_COUNT`, `p₀` reports `NO`
infinitely often. -/
theorem fig9_noSet_infinite :
    (NoSet (touts (fig9Alg (n := 2)) (tcanon x5)) 0).Infinite := by
  rw [infinite_iff_frequently]
  intro N
  refine ⟨12 * (N + 1) + 5, by omega, ?_⟩
  have hflag := flag9_mono _ 0 flag9_x5 (12 * (N + 1) + 5) (by omega)
  refine touts9_of_flag _ hflag (w := .val 1) (vw := annOf x5 (4 * (N + 1) + 1)) ?_
  rw [show 12 * (N + 1) + 5 = 3 * (4 * (N + 1) + 1) + 2 by ring, tcanon_eq _ _ _ (by norm_num)]
  simp [tseg, x5, fam1]

/-- **The algorithm of Figure 9 does not predictively weakly decide `SEC_COUNT`** (proof of
Lemma 6.4), even for the weaker Definition 6.2: the execution is tight, so its sketch is its
input `x5 ∈ SEC_COUNT`, and `p₀` reports `NO` infinitely often. -/
theorem fig9_fails : ¬ PWDecides (fig9Alg (n := 2)) (SEC : Set (CWord 2)) := by
  intro h
  rcases (h _ x5 x5 (tIsExec_tcanon (wf_fam _ _ _)) (tHasInput_tcanon x5)
    (tHasSketch_tcanon x5)).1 x5_mem_SEC with h1 | ⟨-, h2⟩
  · exact fig9_noSet_infinite (h1 0)
  · exact h2 x5_mem_SEC

end Podc2025.LanguageDecidability.Counter
