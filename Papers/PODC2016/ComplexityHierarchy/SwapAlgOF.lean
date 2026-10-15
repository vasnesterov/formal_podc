import Papers.PODC2016.ComplexityHierarchy.SwapAlg

/-!
# Swap and read (Section 8 of [EGSZ16]): obstruction-freedom and Theorem 8.8

[EGSZ16] F. Ellen, R. Gelashvili, N. Shavit, L. Zhu, *A Complexity-Based Hierarchy for
Multiprocessor Synchronization*, PODC 2016 (arXiv 1607.06139), Section 8.

* `swapAlg_obstructionFree`: Algorithm 1 (with double-collect scans) is obstruction-free
  (CSLib's `Impl.ObstructionFree`: from every reachable configuration a pending process running
  solo returns). This is Lemma 8.7 (without the explicit bound `3n − 2` on the number of scans).
* `theorem_8_8`: Theorem 8.8.

## Proof of obstruction-freedom (Lemma 8.7)

A pending process running solo first finishes its current scan (at most three collects: the
current one, then two complete collects of the now unchanging memory). If it then swaps, the next
scan returns the current memory, which is dominated by its laps `l` (`Dom`). From then on every
swap writes `l` into a location differing from `l` (decreasing their number `cnt`), or, when all
locations contain `l` and `v* = vstar l` is not yet two laps ahead, increments `l v*`, which
increases the lead of `v*` (`LeadK`). The measure `cnt + (m + 1) · (2 − lead)` decreases with
every swap–scan cycle, so the process decides.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ComplexityHierarchy.SwapRead

open Cslib.SharedMemory Finset

variable {k m : ℕ} {P : Type} [NeZero k] [NeZero m] [DecidableEq P]

/-! ### Leads and the number of differing locations -/

/-- `w` is at least `t` laps ahead of every other value. -/
def LeadK (l : Laps k) (w : Fin k) (t : ℕ) : Prop := ∀ u, u ≠ w → l u + t ≤ l w

lemma leadK_zero (l : Laps k) : LeadK l (vstar l) 0 := fun u _ => by simpa using le_vstar l u

lemma LeadK.succ {l : Laps k} {w : Fin k} {t : ℕ} (h : LeadK l w t) :
    LeadK (Function.update l w (l w + 1)) w (t + 1) := fun u hu => by
  have := h u hu; simp [Function.update_of_ne hu]; omega

lemma LeadK.vstar_eq {l : Laps k} {w : Fin k} {t : ℕ} (h : LeadK l w (t + 1)) : vstar l = w := by
  by_contra hne
  have h1 := h _ hne
  have h2 := le_vstar l w
  omega

/-- The number of locations whose laps differ from `l`. -/
def cnt (l : Laps k) (mem : Fin m → SVal k P) : ℕ := (univ.filter fun i => (mem i).2 ≠ l).card

lemma cnt_le (l : Laps k) (mem : Fin m → SVal k P) : cnt l mem ≤ m := by
  unfold cnt; exact (card_filter_le _ _).trans (by simp)

lemma cnt_update {l : Laps k} {mem : Fin m → SVal k P} {j : Fin m} (hj : (mem j).2 ≠ l)
    (t : Option (P × ℕ)) : cnt l (Function.update mem j (t, l)) + 1 = cnt l mem := by
  unfold cnt
  have : (univ.filter fun i => (Function.update mem j (t, l) i).2 ≠ l) =
      (univ.filter fun i => (mem i).2 ≠ l).erase j := by
    ext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [hi]
  rw [this, card_erase_of_mem (by simp [hj])]
  have : 0 < (univ.filter fun i => (mem i).2 ≠ l).card := card_pos.2 ⟨j, by simp [hj]⟩
  omega

/-! ### Solo steps -/

/-- `p` running solo from `C` eventually returns. -/
def Term (p : P) (C : DCfg k m P) : Prop := ∃ n, (((swapAlg k m P).soloStep p)^[n] C).pend p = none

lemma Term.of_iter {p : P} {C : DCfg k m P} (n : ℕ)
    (h : Term p (((swapAlg k m P).soloStep p)^[n] C)) : Term p C := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t + n, by rw [Function.iterate_add_apply]; exact ht⟩

variable {p : P} {C : DCfg k m P}

lemma solo_read (hp : C.pend p ≠ none) (hph : (C.loc p).ph = .scan) :
    (swapAlg k m P).soloStep p C =
      ⟨Function.update C.loc p (readStep (C.loc p) (C.mem (C.loc p).idx)), C.pend, C.mem⟩ := by
  have hn : (swapAlg k m P).nextLabel C p = .tau p := by simp [Impl.nextLabel, act_scan hph]
  simp [Impl.soloStep, hp, hn, step_tau_scan hp hph]

lemma solo_swap {j : Fin m} (hp : C.pend p ≠ none) (hph : (C.loc p).ph = .swap j) :
    (swapAlg k m P).soloStep p C =
      ⟨Function.update C.loc p (afterSwap (C.loc p) (C.mem j)), C.pend,
        Function.update C.mem j (some (p, (C.loc p).seq), (C.loc p).l)⟩ := by
  have hn : (swapAlg k m P).nextLabel C p = .tau p := by simp [Impl.nextLabel, act_swap hph]
  simp [Impl.soloStep, hp, hn, step_tau_swap hp hph]

lemma term_done {w : Fin k} (hp : C.pend p ≠ none) (hph : (C.loc p).ph = .done w) : Term p C := by
  refine ⟨1, ?_⟩
  have hn : (swapAlg k m P).nextLabel C p = .ret p w := by simp [Impl.nextLabel, act_done hph]
  have hs : (swapAlg k m P).step C (.ret p w) =
      some { C with pend := Function.update C.pend p none,
                    loc := Function.update C.loc p (C.loc p) } := by
    simp [Impl.step, hp, act_done hph]; rfl
  simp [Impl.soloStep, hp, hn, hs]

/-- The outcome of a complete collect returning `c`, from local state `d` to `d'`. -/
def Finished (d d' : DLoc k m P) (c : Fin m → SVal k P) : Prop :=
  d'.s = d.s ∧ d'.seq = d.seq ∧ d'.inp = d.inp ∧
  ((d.prev = some c ∧ d'.ph = (after d.l d.s (vecs c)).1 ∧ d'.l = (after d.l d.s (vecs c)).2) ∨
   (d.prev ≠ some c ∧ d'.ph = .scan ∧ d'.prev = some c ∧ d'.idx = 0 ∧ d'.l = d.l))

/-- A solo run of `p` completing its current collect. -/
lemma solo_collect (p : P) (n : ℕ) : ∀ C : DCfg k m P, C.pend p ≠ none → (C.loc p).ph = .scan →
    (C.loc p).idx.val + n + 1 = m →
    ∃ c : Fin m → SVal k P, (∀ j, (C.loc p).idx ≤ j → c j = C.mem j) ∧
      (∀ j, j < (C.loc p).idx → c j = (C.loc p).cur j) ∧
      (((swapAlg k m P).soloStep p)^[n + 1] C).pend = C.pend ∧
      (((swapAlg k m P).soloStep p)^[n + 1] C).mem = C.mem ∧
      Finished (C.loc p) ((((swapAlg k m P).soloStep p)^[n + 1] C).loc p) c := by
  induction n with
  | zero =>
    intro C hp hph hidx
    rw [zero_add, Function.iterate_one, solo_read hp hph]
    refine ⟨Function.update (C.loc p).cur (C.loc p).idx (C.mem (C.loc p).idx), fun j hj => ?_,
      fun j hj => ?_, rfl, rfl, ?_⟩
    · have : j = (C.loc p).idx := Fin.ext (by have := j.isLt; rw [Fin.le_def] at hj; omega)
      subst this; simp
    · rw [Function.update_of_ne (ne_of_lt hj)]
    · simp only [Function.update_self]
      rcases readStep_cases (C.loc p) (C.mem (C.loc p).idx) with ⟨hlt, -⟩ | ⟨-, hpv, hrs⟩ |
        ⟨-, hpv, hrs⟩
      · omega
      · rw [hrs]; exact ⟨rfl, rfl, rfl, Or.inl ⟨hpv, rfl, rfl⟩⟩
      · rw [hrs]; exact ⟨rfl, rfl, rfl, Or.inr ⟨hpv, by simp [hph], rfl, rfl, rfl⟩⟩
  | succ n ih =>
    intro C hp hph hidx
    have hlt : (C.loc p).idx.val + 1 < m := by omega
    rcases readStep_cases (C.loc p) (C.mem (C.loc p).idx) with ⟨hlt', hrs⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · set C1 := (swapAlg k m P).soloStep p C with hC1
      have hC1' := solo_read hp hph
      rw [← hC1, hrs] at hC1'
      have hl1 : C1.loc p = { C.loc p with
          idx := ⟨(C.loc p).idx.val + 1, hlt'⟩,
          cur := Function.update (C.loc p).cur (C.loc p).idx (C.mem (C.loc p).idx) } := by
        rw [hC1']; simp
      have hp1 : C1.pend = C.pend := by rw [hC1']
      have hm1 : C1.mem = C.mem := by rw [hC1']
      obtain ⟨c, hc, hc', h2, h3, h4⟩ := ih C1 (by rw [hp1]; exact hp) (by rw [hl1]; exact hph)
        (by rw [hl1]; simp only; omega)
      refine ⟨c, fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_⟩
      · by_cases hjj : j = (C.loc p).idx
        · subst hjj
          rw [hc' _ (by rw [hl1, Fin.lt_def]; simp), hl1]; simp
        · rw [← hm1]; refine hc j ?_
          rw [hl1, Fin.le_def]; rw [Fin.le_def] at hj
          have : j.val ≠ (C.loc p).idx.val := fun h' => hjj (Fin.ext h')
          simp only; omega
      · rw [hc' j (by rw [hl1, Fin.lt_def]; rw [Fin.lt_def] at hj; simp only; omega), hl1]
        simp [Function.update_of_ne (ne_of_lt hj)]
      · rw [Function.iterate_succ_apply, ← hC1, h2, hp1]
      · rw [Function.iterate_succ_apply, ← hC1, h3, hm1]
      · rw [Function.iterate_succ_apply, ← hC1]
        rw [hl1] at h4; exact h4
    · exact absurd hlt h1
    · exact absurd hlt h1

/-- A scan started from scratch (after a swap) returns the current memory: two collects. -/
lemma solo_fresh_scan (hp : C.pend p ≠ none) (hph : (C.loc p).ph = .scan)
    (hpr : (C.loc p).prev = none) (hidx : (C.loc p).idx = 0) :
    ∃ n, (((swapAlg k m P).soloStep p)^[n] C).pend = C.pend ∧
      (((swapAlg k m P).soloStep p)^[n] C).mem = C.mem ∧
      ((((swapAlg k m P).soloStep p)^[n] C).loc p).ph =
        (after (C.loc p).l (C.loc p).s (vecs C.mem)).1 ∧
      ((((swapAlg k m P).soloStep p)^[n] C).loc p).l =
        (after (C.loc p).l (C.loc p).s (vecs C.mem)).2 := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  obtain ⟨c, hc, -, h2, h3, h4⟩ := solo_collect p (m - 1) C hp hph (by rw [hidx]; simp; omega)
  have hcm : c = C.mem := funext fun j => hc j (by rw [hidx, Fin.le_def]; simp)
  set C1 := ((swapAlg k m P).soloStep p)^[m - 1 + 1] C with hC1
  obtain ⟨hs1, hseq1, -, h4⟩ := h4
  rcases h4 with ⟨hpv, -⟩ | ⟨-, hph1, hpv1, hidx1, hl1⟩
  · rw [hpr] at hpv; cases hpv
  obtain ⟨c', hc', -, h2', h3', h4'⟩ := solo_collect p (m - 1) C1 (by rw [h2]; exact hp) hph1
    (by rw [hidx1]; simp; omega)
  have hcm' : c' = C.mem := funext fun j => by
    rw [hc' j (by rw [hidx1, Fin.le_def]; simp), h3]
  obtain ⟨hs2, -, -, h4'⟩ := h4'
  rcases h4' with ⟨-, hph2, hl2⟩ | ⟨hne, -⟩
  · refine ⟨(m - 1 + 1) + (m - 1 + 1), ?_, ?_, ?_, ?_⟩
    · rw [Function.iterate_add_apply, ← hC1, h2', h2]
    · rw [Function.iterate_add_apply, ← hC1, h3', h3]
    · rw [Function.iterate_add_apply, ← hC1, hph2, hcm', hl1, hs1]
    · rw [Function.iterate_add_apply, ← hC1, hl2, hcm', hl1, hs1]
  · exact absurd (by rw [hpv1, hcm, hcm']) hne

/-- A swap followed by a fresh scan. -/
lemma solo_cycle {j : Fin m} (hp : C.pend p ≠ none) (hph : (C.loc p).ph = .swap j) :
    ∃ n, (((swapAlg k m P).soloStep p)^[n] C).pend = C.pend ∧
      (((swapAlg k m P).soloStep p)^[n] C).mem =
        Function.update C.mem j (some (p, (C.loc p).seq), (C.loc p).l) ∧
      ((((swapAlg k m P).soloStep p)^[n] C).loc p).ph = (after (C.loc p).l (C.mem j).2
        (vecs (Function.update C.mem j (some (p, (C.loc p).seq), (C.loc p).l)))).1 ∧
      ((((swapAlg k m P).soloStep p)^[n] C).loc p).l = (after (C.loc p).l (C.mem j).2
        (vecs (Function.update C.mem j (some (p, (C.loc p).seq), (C.loc p).l)))).2 := by
  set C1 := (swapAlg k m P).soloStep p C with hC1
  have hC1' := solo_swap hp hph
  rw [← hC1] at hC1'
  have hl1 : C1.loc p = afterSwap (C.loc p) (C.mem j) := by rw [hC1']; simp
  have hp1 : C1.pend = C.pend := by rw [hC1']
  have hm1 : C1.mem = Function.update C.mem j (some (p, (C.loc p).seq), (C.loc p).l) := by
    rw [hC1']
  obtain ⟨n, h2, h3, h4, h5⟩ := solo_fresh_scan (C := C1) (by rw [hp1]; exact hp)
    (by rw [hl1]; rfl) (by rw [hl1]; rfl) (by rw [hl1]; rfl)
  refine ⟨n + 1, ?_, ?_, ?_, ?_⟩
  · rw [Function.iterate_add_apply, Function.iterate_one, ← hC1, h2, hp1]
  · rw [Function.iterate_add_apply, Function.iterate_one, ← hC1, h3, hm1]
  · rw [Function.iterate_add_apply, Function.iterate_one, ← hC1, h4, hl1, hm1]; rfl
  · rw [Function.iterate_add_apply, Function.iterate_one, ← hC1, h5, hl1, hm1]; rfl

lemma vecs_update_le {mem : Fin m → SVal k P} {j : Fin m} {l : Laps k}
    {t : Option (P × ℕ)} (hdom : ∀ i, (mem i).2 ≤ l) (i : Fin m) :
    vecs (Function.update mem j (t, l)) i ≤ l := by
  by_cases hi : i = j
  · subst hi; simp [vecs]
  · simp only [vecs, Function.update_of_ne hi]; exact hdom i

/-- The main solo loop of Lemma 8.7: from a swap of laps `l` dominating the memory into a
location that differs from `l`, the process decides. -/
lemma term_main (μ : ℕ) : ∀ (C : DCfg k m P) (j : Fin m) (t : ℕ), C.pend p ≠ none →
    (C.loc p).ph = .swap j → (∀ i, (C.mem i).2 ≤ (C.loc p).l) → (C.mem j).2 ≠ (C.loc p).l →
    LeadK (C.loc p).l (vstar (C.loc p).l) t → t ≤ 2 →
    cnt (C.loc p).l C.mem + (m + 1) * (2 - t) ≤ μ → Term p C := by
  induction μ using Nat.strong_induction_on with
  | _ μ ih =>
  intro C j t hp hph hdom hj hlead ht hμ
  obtain ⟨n, h2, h3, h4, h5⟩ := solo_cycle hp hph
  refine Term.of_iter n ?_
  set C2 := ((swapAlg k m P).soloStep p)^[n] C with hC2
  set l := (C.loc p).l with hl
  set mem1 := Function.update C.mem j (some (p, (C.loc p).seq), l) with hmem1
  have hmerge : l = merge l (C.mem j).2 (vecs mem1) := by
    apply le_antisymm (le_merge_l _ _ _)
    intro v
    exact merge_le le_rfl (hdom j v) (fun i => vecs_update_le hdom i v)
  have hcnt : cnt l mem1 + 1 = cnt l C.mem := cnt_update hj _
  have hp2 : C2.pend p ≠ none := by rw [h2]; exact hp
  rcases after_cases' l (C.mem j).2 (vecs mem1) l hmerge with ⟨-, -, haf⟩ | ⟨hall, hlead2, haf⟩ |
    ⟨hne, haf⟩
  · rw [haf] at h4; exact term_done hp2 h4
  · -- all locations contain `l`, no 2-lap leader: promote `vstar l`
    have ht2 : t < 2 := by
      by_contra hc
      exact hlead2 fun u hu => by have := hlead u hu; omega
    have hl2 : (C2.loc p).l = Function.update l (vstar l) (l (vstar l) + 1) := by rw [h5, haf]
    have hph2 : (C2.loc p).ph = .swap 0 := by rw [h4, haf]
    have hmem2 : ∀ i, (C2.mem i).2 = l := fun i => by rw [h3]; exact hall i
    have hlead' : LeadK (C2.loc p).l (vstar (C2.loc p).l) (t + 1) := by
      rw [hl2, hlead.succ.vstar_eq]; exact hlead.succ
    have hle : l ≤ (C2.loc p).l := by
      rw [hl2]; intro v
      by_cases hv : v = vstar l
      · subst hv; simp
      · simp [Function.update_of_ne hv]
    have hne2 : l ≠ (C2.loc p).l := by
      intro he
      have := congrFun he (vstar l)
      rw [hl2] at this; simp at this
    have hc2 := cnt_le (C2.loc p).l C2.mem
    have hc1 : cnt l mem1 = 0 := by
      unfold cnt; simp only [card_eq_zero, filter_eq_empty_iff, mem_univ, true_implies, not_not]
      exact hall
    refine ih _ ?_ C2 0 (t + 1) hp2 hph2 (fun i => by rw [hmem2]; exact hle)
      (by rw [hmem2]; exact hne2) hlead' (by omega) le_rfl
    rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl <;> omega
  · -- swap `l` into the first location differing from `l`
    have hl2 : (C2.loc p).l = l := by rw [h5, haf]
    have hph2 : (C2.loc p).ph = .swap (firstNe (vecs mem1) l) := by rw [h4, haf]
    have hmem2 : C2.mem = mem1 := h3
    have hdiff : (C2.mem (firstNe (vecs mem1) l)).2 ≠ (C2.loc p).l := by
      rw [hmem2, hl2]
      exact firstNe_ne (by by_contra hc; push Not at hc; exact hne hc)
    refine ih _ ?_ C2 _ t hp2 hph2 (fun i => by rw [hmem2, hl2]; exact vecs_update_le hdom i)
      hdiff (by rw [hl2]; exact hlead) ht le_rfl
    rw [hl2, hmem2]
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;> omega

/-- From a swap (with arbitrary laps), the process decides. -/
lemma term_swap {j : Fin m} (hp : C.pend p ≠ none) (hph : (C.loc p).ph = .swap j) : Term p C := by
  obtain ⟨n, h2, h3, h4, h5⟩ := solo_cycle hp hph
  refine Term.of_iter n ?_
  set C2 := ((swapAlg k m P).soloStep p)^[n] C with hC2
  set mem1 := Function.update C.mem j (some (p, (C.loc p).seq), (C.loc p).l) with hmem1
  set L := merge (C.loc p).l (C.mem j).2 (vecs mem1) with hL
  have hp2 : C2.pend p ≠ none := by rw [h2]; exact hp
  have hdomL : ∀ i, (C2.mem i).2 ≤ L := fun i => by rw [h3]; exact le_merge_a (C.loc p).l (C.mem j).2 (vecs mem1) i
  rcases after_cases' (C.loc p).l (C.mem j).2 (vecs mem1) L hL with ⟨-, -, haf⟩ |
    ⟨hall, -, haf⟩ | ⟨hne, haf⟩
  · rw [haf] at h4; exact term_done hp2 h4
  · have hl2 : (C2.loc p).l = Function.update L (vstar L) (L (vstar L) + 1) := by rw [h5, haf]
    have hph2 : (C2.loc p).ph = .swap 0 := by rw [h4, haf]
    have hle : L ≤ (C2.loc p).l := by
      rw [hl2]; intro v
      by_cases hv : v = vstar L
      · subst hv; simp
      · simp [Function.update_of_ne hv]
    have hne2 : (C2.mem 0).2 ≠ (C2.loc p).l := by
      rw [h3]; intro he
      have := congrFun he (vstar L)
      rw [hl2] at this
      have h0 : vecs mem1 0 = L := hall 0
      simp only [vecs] at h0
      rw [h0] at this; simp at this
    exact term_main _ C2 0 0 hp2 hph2 (fun i => (hdomL i).trans hle) hne2 (leadK_zero _) (by omega)
      le_rfl
  · have hl2 : (C2.loc p).l = L := by rw [h5, haf]
    have hph2 : (C2.loc p).ph = .swap (firstNe (vecs mem1) L) := by rw [h4, haf]
    have hdiff : (C2.mem (firstNe (vecs mem1) L)).2 ≠ (C2.loc p).l := by
      rw [h3, hl2]
      exact firstNe_ne (by by_contra hc; push Not at hc; exact hne hc)
    exact term_main _ C2 _ 0 hp2 hph2 (fun i => by rw [hl2]; exact hdomL i) hdiff
      (by rw [hl2]; exact leadK_zero _) (by omega) le_rfl

/-- After a scan the process decides (or keeps running and decides). -/
lemma term_post (hp : C.pend p ≠ none) (h1 : (C.loc p).ph ≠ .scan) (h2 : (C.loc p).ph ≠ .idle) :
    Term p C := by
  rcases hph : (C.loc p).ph with _ | _ | j | w
  · exact absurd hph h2
  · exact absurd hph h1
  · exact term_swap hp hph
  · exact term_done hp hph

/-- From the middle of a scan, the process decides: the scan completes within three collects. -/
lemma term_scan (hp : C.pend p ≠ none) (hph : (C.loc p).ph = .scan) : Term p C := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hidx := (C.loc p).idx.isLt
  obtain ⟨c, -, -, h2, h3, h4⟩ := solo_collect p (m - 1 - (C.loc p).idx.val) C hp hph (by omega)
  refine Term.of_iter (m - 1 - (C.loc p).idx.val + 1) ?_
  set C1 := ((swapAlg k m P).soloStep p)^[m - 1 - (C.loc p).idx.val + 1] C with hC1
  have hp1 : C1.pend p ≠ none := by rw [h2]; exact hp
  obtain ⟨-, -, -, h4⟩ := h4
  rcases h4 with ⟨-, hph1, -⟩ | ⟨-, hph1, hpv1, hidx1, -⟩
  · exact term_post hp1 (by rw [hph1]; exact after_ph_ne_scan _ _ _)
      (by rw [hph1]; exact after_ph_ne_idle _ _ _)
  obtain ⟨c', hc', -, h2', h3', h4'⟩ := solo_collect p (m - 1) C1 hp1 hph1 (by rw [hidx1]; simp; omega)
  refine Term.of_iter (m - 1 + 1) ?_
  set C2 := ((swapAlg k m P).soloStep p)^[m - 1 + 1] C1 with hC2
  have hp2 : C2.pend p ≠ none := by rw [h2']; exact hp1
  have hcm' : c' = C1.mem := funext fun j => hc' j (by rw [hidx1, Fin.le_def]; simp)
  obtain ⟨-, -, -, h4'⟩ := h4'
  rcases h4' with ⟨-, hph2, -⟩ | ⟨-, hph2, hpv2, hidx2, -⟩
  · exact term_post hp2 (by rw [hph2]; exact after_ph_ne_scan _ _ _)
      (by rw [hph2]; exact after_ph_ne_idle _ _ _)
  obtain ⟨c'', hc'', -, h2'', -, h4''⟩ := solo_collect p (m - 1) C2 hp2 hph2
    (by rw [hidx2]; simp; omega)
  refine Term.of_iter (m - 1 + 1) ?_
  have hp3 : (((swapAlg k m P).soloStep p)^[m - 1 + 1] C2).pend p ≠ none := by rw [h2'']; exact hp2
  have hcm'' : c'' = c' := funext fun j => by
    rw [hc'' j (by rw [hidx2, Fin.le_def]; simp), h3', hcm']
  obtain ⟨-, -, -, h4''⟩ := h4''
  rcases h4'' with ⟨-, hph3, -⟩ | ⟨hne, -⟩
  · exact term_post hp3 (by rw [hph3]; exact after_ph_ne_scan _ _ _)
      (by rw [hph3]; exact after_ph_ne_idle _ _ _)
  · exact absurd (by rw [hpv2, hcm'']) hne

variable [Fintype P]

/-- Algorithm 1 is obstruction-free (Lemma 8.7 of [EGSZ16], without the explicit step bound). -/
theorem swapAlg_obstructionFree (hP : Fintype.card P ≤ m + 1) :
    (swapAlg k m P).ObstructionFree := by
  intro C p ⟨α, hα⟩ hp
  have hI := sInv_run hP hα
  have hidle : (C.loc p).ph ≠ .idle := fun h => hp (hI.idle p h).2
  by_cases hs : (C.loc p).ph = .scan
  · exact term_scan hp hs
  · exact term_post hp hs hidle

end Cslib.SharedMemory.ComplexityHierarchy.SwapRead

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory SwapRead

/-- **Theorem 8.8** of [EGSZ16] (Ellen–Gelashvili–Shavit–Zhu, *A Complexity-Based Hierarchy for
Multiprocessor Synchronization*, PODC 2016): there is an obstruction-free protocol for consensus
among `n` processes (inputs and decisions in `Fin n`) that uses only `n − 1` memory locations
supporting `read` and `swap` (`swapLoc V v₀`, all initially `v₀`). Agreement and (strong) validity
hold in every finite execution (`Impl.Solves (consensus …)`), and the protocol is obstruction-free
from every reachable configuration (`Impl.ObstructionFree`). The protocol is Algorithm 1
(`swapAlg`), with scans implemented by double collect; the swap arguments carry the process
identifier and a sequence number (as in the paper), so the protocol is anonymous only in the sense
that identifiers are used for nothing but these tags. Stated for `n ≥ 2` (for `n = 1` there are
no locations). -/
theorem theorem_8_8 (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    ∃ (V : Type) (v₀ : V) (L : Type)
      (I : Impl (taskObj (Fin n) (Fin n)) (fun _ : Fin (n - 1) => swapLoc V v₀) (Fin n) L),
      (∀ i, I.memInit i = v₀) ∧ (∀ p x, I.allowed p x) ∧
        I.Solves (consensus (Fin n) (Fin n)) ∧ I.ObstructionFree := by
  have : NeZero (n - 1) := ⟨by omega⟩
  have hP : Fintype.card (Fin n) ≤ n - 1 + 1 := by simp; omega
  exact ⟨SVal n (Fin n), (none, 0), DLoc n (n - 1) (Fin n), swapAlg n (n - 1) (Fin n),
    fun _ => rfl, fun _ _ => trivial, swapAlg_solves hP, swapAlg_obstructionFree hP⟩

end Cslib.SharedMemory.ComplexityHierarchy
