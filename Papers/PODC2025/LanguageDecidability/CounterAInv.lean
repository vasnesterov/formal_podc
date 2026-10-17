import Papers.PODC2025.LanguageDecidability.CounterAExec
import Papers.PODC2025.LanguageDecidability.CounterDefs

/-!
# The invariant of the corrected algorithm of Figure 5 (`wecAlg`)

For an execution `s` with input `x` we describe the local state of every process and the shared
array `INCS` in terms of the prefix of `x` produced so far (`symCount s t` symbols):

* `lastRead x p k` — the value returned by the last `read` of `p` among the first `k` symbols
  (`0` if none): this is `prev_read`/`curr_read`;
* `lastInv x p k` — the last invocation of `p` among the first `k` symbols;
* `viol x p k` — the symbol at `k` is a response of `p` that violates a safety property checked in
  the second clause of Line 06 (ill-typed operation, or (1)/(2) violated by a `read`);
  `bad x p k` — some response of `p` before `k` is a violation: this is `flag`;
* `INCS[p] = count = ownIncs x p k` (`+ 1` while an `inc` of `p` is announced but not yet sent).

`inv` is the invariant (`PInv`), proved by induction along the execution; `post_verdict` describes
the value reported at a `post` event.
-/

namespace Podc2025.LanguageDecidability.Counter

open Podc2025.LanguageDecidability

variable {n : ℕ}

/-! ### Functions of the input word -/

/-- `prev_read` after the symbol `a`. -/
def newRead : CInv ⊕ CRes → ℕ → ℕ
  | .inr (.val v), _ => v
  | _, old => old

/-- The current invocation after the symbol `a`. -/
def newInv : CInv ⊕ CRes → CInv → CInv
  | .inl v, _ => v
  | _, old => old

/-- The value of the last `read` of `p` among the first `k` symbols (`0` if none). -/
def lastRead (x : CWord n) (p : Fin n) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if (x k).1 = p then newRead (x k).2 (lastRead x p k) else lastRead x p k

/-- The last invocation of `p` among the first `k` symbols. -/
def lastInv (x : CWord n) (p : Fin n) : ℕ → CInv
  | 0 => .read
  | k + 1 => if (x k).1 = p then newInv (x k).2 (lastInv x p k) else lastInv x p k

/-- The response of a `read` returning `v` violates (1) or (2) (with the given values of
`ownIncs` and `prev_read`). -/
def readBad (w : CRes) (a b : ℕ) : Bool :=
  match w with
  | .val v => decide (v < a ∨ v < b)
  | .ack => false

lemma readBad_iff {w : CRes} {a b : ℕ} :
    readBad w a b = true ↔ ∃ v, w = .val v ∧ (v < a ∨ v < b) := by
  cases w <;> simp [readBad]

/-- The symbol at `k` is a response of `p` violating a safety property. -/
def viol (x : CWord n) (p : Fin n) (k : ℕ) : Prop :=
  ∃ w, x k = ⟨p, .inr w⟩ ∧
    (illTyped (lastInv x p k) w = true ∨ readBad w (ownIncs x p k) (lastRead x p k) = true)

/-- Some response of `p` among the first `k` symbols is a violation. -/
def bad (x : CWord n) (p : Fin n) (k : ℕ) : Prop := ∃ j < k, viol x p j

/-- No symbol of `p` strictly between `r` and `K`. -/
def NoP (x : CWord n) (p : Fin n) (r K : ℕ) : Prop := ∀ m, r < m → m < K → (x m).1 ≠ p

section word

variable {x : CWord n} {p : Fin n} {k : ℕ}

lemma viol_proc (h : viol x p k) : (x k).1 = p := by
  obtain ⟨w, hw, -⟩ := h; rw [hw]

lemma bad_succ : bad x p (k + 1) ↔ bad x p k ∨ viol x p k := by
  constructor
  · rintro ⟨j, hj, hv⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact Or.inl ⟨j, hj, hv⟩
    · exact Or.inr hv
  · rintro (⟨j, hj, hv⟩ | hv)
    · exact ⟨j, by omega, hv⟩
    · exact ⟨k, by omega, hv⟩

lemma bad_mono {k k' : ℕ} (h : k ≤ k') (hb : bad x p k) : bad x p k' := by
  obtain ⟨j, hj, hv⟩ := hb; exact ⟨j, by omega, hv⟩

lemma ownIncs_succ_of_ne (h : (x k).1 ≠ p) : ownIncs x p (k + 1) = ownIncs x p k := by
  simp [ownIncs, h]

lemma lastRead_succ_of_ne (h : (x k).1 ≠ p) : lastRead x p (k + 1) = lastRead x p k := by
  simp [lastRead, h]

lemma lastInv_succ_of_ne (h : (x k).1 ≠ p) : lastInv x p (k + 1) = lastInv x p k := by
  simp [lastInv, h]

lemma bad_succ_of_ne (h : (x k).1 ≠ p) : bad x p (k + 1) ↔ bad x p k := by
  rw [bad_succ]; exact ⟨fun h' => h'.elim id fun hv => absurd (viol_proc hv) h, Or.inl⟩

lemma const_of_noP {a b : ℕ} (hab : a ≤ b) (h : ∀ m, a ≤ m → m < b → (x m).1 ≠ p) :
    lastRead x p b = lastRead x p a ∧ lastInv x p b = lastInv x p a ∧
      ownIncs x p b = ownIncs x p a ∧ (bad x p b ↔ bad x p a) := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨rfl, rfl, rfl, Iff.rfl⟩
  | succ b hb ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih fun m h1 h2 => h m h1 (by omega)
    have hb' := h b hb (by omega)
    rw [lastRead_succ_of_ne hb', lastInv_succ_of_ne hb', ownIncs_succ_of_ne hb',
      bad_succ_of_ne hb']
    exact ⟨h1, h2, h3, h4⟩

lemma succ_of_inv {v : CInv} (h : x k = ⟨p, .inl v⟩) :
    lastRead x p (k + 1) = lastRead x p k ∧ lastInv x p (k + 1) = v ∧
      ownIncs x p (k + 1) = ownIncs x p k + (if v = .inc then 1 else 0) ∧
      (bad x p (k + 1) ↔ bad x p k) := by
  refine ⟨by simp [lastRead, h, newRead], by simp [lastInv, h, newInv], ?_, ?_⟩
  · cases v <;> simp [ownIncs, h, IsInc]
  · rw [bad_succ]
    refine ⟨fun h' => h'.elim id fun ⟨w, hw, _⟩ => ?_, Or.inl⟩
    rw [h] at hw; simp at hw

lemma succ_of_res {w : CRes} (h : x k = ⟨p, .inr w⟩) :
    lastRead x p (k + 1) = newRead (.inr w) (lastRead x p k) ∧
      lastInv x p (k + 1) = lastInv x p k ∧ ownIncs x p (k + 1) = ownIncs x p k ∧
      (bad x p (k + 1) ↔ bad x p k ∨
        (illTyped (lastInv x p k) w = true ∨
          readBad w (ownIncs x p k) (lastRead x p k) = true)) := by
  refine ⟨by simp [lastRead, h], by simp [lastInv, h, newInv], by simp [ownIncs, h, IsInc], ?_⟩
  rw [bad_succ]
  refine or_congr Iff.rfl ⟨fun ⟨w', hw', hv⟩ => ?_, fun hv => ⟨w, h, hv⟩⟩
  rw [h] at hw'; simp at hw'; subst hw'; exact hv

end word

/-! ### The steps of `wecAlg` -/

lemma postFix_mem (t : ℕ) (p : Fin n) (l : Loc) (w : CRes) (m : Fin n → ℕ) :
    (postFix t p l w m).2.1 = m := by
  cases w <;> simp only [postFix] <;> split_ifs <;> rfl

lemma postFix_fst (t : ℕ) (p : Fin n) (l : Loc) (w : CRes) (m : Fin n → ℕ) :
    (postFix t p l w m).1 =
      { l with
        currRead := newRead (.inr w) l.currRead
        prevRead := newRead (.inr w) l.currRead
        prevIncs := ∑ j, m j
        flag := l.flag || illTyped l.inv w || readBad w (m p) l.prevRead } := by
  cases w <;> cases hf : l.flag <;> simp only [postFix, newRead, readBad, hf] <;> split_ifs <;>
    simp_all

lemma postFix_verdict (t : ℕ) (p : Fin n) (l : Loc) (w : CRes) (m : Fin n → ℕ) :
    (postFix t p l w m).2.2 = .no ↔ (l.flag = true ∨ illTyped l.inv w = true ∨
      readBad w (m p) l.prevRead = true ∨ newRead (.inr w) l.currRead ≠ ∑ j, m j ∨
      l.prevIncs < ∑ j, m j) := by
  cases w <;> simp only [postFix, newRead, readBad] <;> split_ifs <;> (simp_all; try tauto)

/-! ### Configurations of `wecAlg` along an execution -/

/-- Scheduling events for counter words. -/
abbrev CEv (n : ℕ) := Ev (n := n) (fun _ => CInv) (fun _ => CRes)

/-- The shared array `INCS` at time `t`. -/
def memAt (s : ℕ → CEv n) (t : ℕ) : Fin n → ℕ := ((wecAlg (n := n)).run s t).mem

/-- The local states at time `t`. -/
def locAt (s : ℕ → CEv n) (t : ℕ) : Fin n → Loc := ((wecAlg (n := n)).run s t).loc

/-- `curr_incs`: the sum of the entries of `INCS` at time `t`. -/
def sumMem (s : ℕ → CEv n) (t : ℕ) : ℕ := ∑ j, memAt s t j

variable {s : ℕ → CEv n}

lemma step_pre {t : ℕ} {q : Fin n} {v : CInv} (h : s t = .pre q v) :
    memAt s (t + 1) = (pre5 t q (locAt s t q) v (memAt s t)).2 ∧
    locAt s (t + 1) = Function.update (locAt s t) q (pre5 t q (locAt s t q) v (memAt s t)).1 := by
  simp only [memAt, locAt, Alg.run, h, Alg.next]; exact ⟨rfl, rfl⟩

lemma step_sym {t : ℕ} (h : (s t).sym.isSome = true) :
    memAt s (t + 1) = memAt s t ∧ locAt s (t + 1) = locAt s t := by
  simp only [memAt, locAt, Alg.run, Alg.next_of_sym _ h]; exact ⟨rfl, rfl⟩

lemma step_post {t : ℕ} {q : Fin n} {w : CRes} (h : s t = .post q w) :
    memAt s (t + 1) = memAt s t ∧
    locAt s (t + 1) =
      Function.update (locAt s t) q (postFix t q (locAt s t q) w (memAt s t)).1 := by
  simp only [memAt, locAt, Alg.run, h, Alg.next]
  exact ⟨postFix_mem t q _ w _, rfl⟩

lemma outs_post_eq {t : ℕ} {q : Fin n} {w : CRes} (h : s t = .post q w) :
    (wecAlg (n := n)).outs s t = some (q, (postFix t q (locAt s t q) w (memAt s t)).2.2) := by
  simp only [Alg.outs, h, Alg.next]; rfl

/-! ### The invariant -/

/-- The part of the invariant common to all program counters. -/
def Base (x : CWord n) (p : Fin n) (k : ℕ) (l : Loc) (mp : ℕ) : Prop :=
  (l.flag = true ↔ bad x p k) ∧ l.prevRead = lastRead x p k ∧ l.currRead = lastRead x p k ∧
    l.count = mp

/-- The invariant of process `p` after `K` input symbols, with local state `l`, `INCS[p] = mp`
and program counter given by the last argument. -/
def PInv (x : CWord n) (p : Fin n) (K : ℕ) (l : Loc) (mp : ℕ) : Phase CInv CRes → Prop
  | .idle => Base x p K l mp ∧ mp = ownIncs x p K
  | .ready v => Base x p K l mp ∧ mp = ownIncs x p K + (if v = .inc then 1 else 0) ∧ l.inv = v
  | .waiting => Base x p K l mp ∧ mp = ownIncs x p K ∧ l.inv = lastInv x p K
  | .got w => ∃ r < K, x r = ⟨p, .inr w⟩ ∧ NoP x p r K ∧ Base x p r l mp ∧
      mp = ownIncs x p r ∧ l.inv = lastInv x p r

lemma Base.succ_of_ne {x : CWord n} {p : Fin n} {K : ℕ} {l : Loc} {mp : ℕ}
    (hK : (x K).1 ≠ p) (h : Base x p K l mp) : Base x p (K + 1) l mp := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [Base, bad_succ_of_ne hK, lastRead_succ_of_ne hK]; exact ⟨h1, h2, h3, h4⟩

lemma PInv.succ_of_ne {x : CWord n} {p : Fin n} {K : ℕ} {l : Loc} {mp : ℕ}
    {φ : Phase CInv CRes} (hK : (x K).1 ≠ p) (h : PInv x p K l mp φ) :
    PInv x p (K + 1) l mp φ := by
  cases φ with
  | idle => exact ⟨h.1.succ_of_ne hK, by rw [ownIncs_succ_of_ne hK]; exact h.2⟩
  | ready v => exact ⟨h.1.succ_of_ne hK, by rw [ownIncs_succ_of_ne hK]; exact h.2.1, h.2.2⟩
  | waiting =>
    exact ⟨h.1.succ_of_ne hK, by rw [ownIncs_succ_of_ne hK]; exact h.2.1,
      by rw [lastInv_succ_of_ne hK]; exact h.2.2⟩
  | got w =>
    obtain ⟨r, hr, hxr, hnp, hb, hm, hi⟩ := h
    refine ⟨r, by omega, hxr, fun m h1 h2 => ?_, hb, hm, hi⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
    · exact hnp m h1 h2
    · exact hK

variable {x : CWord n} {ι : ℕ → ℕ}

/-- **The invariant of `wecAlg`** along an execution `s` with input `x`. -/
theorem inv (hs : IsExec s) (hx : IsInput s x ι) :
    ∀ t p, PInv x p (symCount s t) (locAt s t p) (memAt s t p) (phs s t p) := by
  intro t
  induction t with
  | zero =>
    intro p
    show PInv x p 0 {} 0 .idle
    simp [PInv, Base, bad, lastRead, ownIncs]
  | succ t ih =>
    intro p
    have hv := hs.valid t
    rcases h : s t with ⟨q, v⟩ | ⟨q, v⟩ | ⟨q, w⟩ | ⟨q, w⟩ <;> rw [h] at hv <;>
      simp only [Enabled, Ev.need, Ev.proc] at hv
    · -- Lines 01–02
      have hK : symCount s (t + 1) = symCount s t := symCount_succ_of_isNone (by rw [h]; rfl)
      obtain ⟨hm, hl⟩ := step_pre h
      rw [hK, hm, hl, phs_succ, h]
      by_cases hp : p = q
      · subst hp
        have ih := ih p; rw [hv] at ih
        obtain ⟨⟨hf, hpr, hcr, hc⟩, hmo⟩ := ih
        simp only [phStep_pre_self, Function.update_self]
        cases v <;> simp [PInv, Base, pre5, hf, hpr, hcr, hc, hmo]
      · rw [phStep_of_ne (e := (Ev.pre q v : CEv n)) hp, Function.update_of_ne hp]
        have : (pre5 t q (locAt s t q) v (memAt s t)).2 p = memAt s t p := by
          cases v <;> simp [pre5, Function.update_of_ne hp]
        rw [this]; exact ih p
    · -- Line 03
      have hsome : (s t).sym.isSome = true := by rw [h]; rfl
      have hxk := hx.sym_eq hsome
      rw [h] at hxk; simp only [Ev.sym, Option.some.injEq] at hxk
      obtain ⟨hm, hl⟩ := step_sym hsome
      rw [symCount_succ_of_isSome hsome, hm, hl, phs_succ, h]
      by_cases hp : p = q
      · subst hp
        have ih := ih p; rw [hv] at ih
        obtain ⟨⟨hf, hpr, hcr, hc⟩, hmo, hinv⟩ := ih
        obtain ⟨e1, e2, e3, e4⟩ := succ_of_inv hxk.symm
        simp only [phStep_send_self, PInv, Base]
        rw [e1, e2, e3, e4]; exact ⟨⟨hf, hpr, hcr, hc⟩, hmo, hinv⟩
      · rw [phStep_of_ne (e := (Ev.send q v : CEv n)) hp]
        exact (ih p).succ_of_ne (by rw [← hxk]; exact Ne.symm hp)
    · -- Line 04
      have hsome : (s t).sym.isSome = true := by rw [h]; rfl
      have hxk := hx.sym_eq hsome
      rw [h] at hxk; simp only [Ev.sym, Option.some.injEq] at hxk
      obtain ⟨hm, hl⟩ := step_sym hsome
      rw [symCount_succ_of_isSome hsome, hm, hl, phs_succ, h]
      by_cases hp : p = q
      · subst hp
        have ih := ih p; rw [hv] at ih
        obtain ⟨hb, hmo, hinv⟩ := ih
        simp only [phStep_recv_self]
        exact ⟨symCount s t, by omega, hxk.symm, fun m h1 h2 => by omega, hb, hmo, hinv⟩
      · rw [phStep_of_ne (e := (Ev.recv q w : CEv n)) hp]
        exact (ih p).succ_of_ne (by rw [← hxk]; exact Ne.symm hp)
    · -- Lines 05–06
      have hK : symCount s (t + 1) = symCount s t := symCount_succ_of_isNone (by rw [h]; rfl)
      obtain ⟨hm, hl⟩ := step_post h
      rw [hK, hm, hl, phs_succ, h]
      by_cases hp : p = q
      · subst hp
        have ih := ih p; rw [hv] at ih
        obtain ⟨r, hr, hxr, hnp, ⟨hf, hpr, hcr, hc⟩, hmo, hinv⟩ := ih
        obtain ⟨c1, -, c3, c4⟩ :=
          const_of_noP (x := x) (p := p) (show r + 1 ≤ symCount s t by omega)
            (fun m h1 h2 => hnp m (by omega) h2)
        obtain ⟨d1, -, d3, d4⟩ := succ_of_res hxr
        simp only [phStep_post_self, Function.update_self, PInv, Base, postFix_fst]
        refine ⟨⟨?_, ?_, ?_, hc⟩, ?_⟩
        · rw [c4, d4, ← hf, ← hinv, ← hmo, ← hpr]; simp only [Bool.or_eq_true]; tauto
        · rw [c1, d1, hcr]
        · rw [c1, d1, hcr]
        · rw [c3, d3, hmo]
      · rw [phStep_of_ne (e := (Ev.post q w : CEv n)) hp, Function.update_of_ne hp]; exact ih p

/-! ### Consequences -/

lemma count_eq_mem (hs : IsExec s) (hx : IsInput s x ι) (t : ℕ) (p : Fin n) :
    (locAt s t p).count = memAt s t p := by
  have h := inv hs hx t p
  generalize phs s t p = φ at h
  cases φ with
  | idle => exact h.1.2.2.2
  | ready v => exact h.1.2.2.2
  | waiting => exact h.1.2.2.2
  | got w => obtain ⟨r, -, -, -, hb, -⟩ := h; exact hb.2.2.2

lemma mem_eq (hs : IsExec s) (hx : IsInput s x ι) (t : ℕ) (p : Fin n) :
    ownIncs x p (symCount s t) ≤ memAt s t p ∧
      (phs s t p ≠ .ready .inc → memAt s t p = ownIncs x p (symCount s t)) := by
  have h := inv hs hx t p
  generalize phs s t p = φ at h
  cases φ with
  | idle => exact ⟨h.2.ge, fun _ => h.2⟩
  | ready v =>
    refine ⟨by rw [h.2.1]; omega, fun hne => ?_⟩
    have : v ≠ .inc := fun e => hne (by rw [e])
    rw [h.2.1]; simp [this]
  | waiting => exact ⟨h.2.1.ge, fun _ => h.2.1⟩
  | got w =>
    obtain ⟨r, hr, hxr, hnp, -, hm, -⟩ := h
    have := (const_of_noP (x := x) (p := p) (show r + 1 ≤ symCount s t by omega)
      (fun m h1 h2 => hnp m (by omega) h2)).2.2.1
    have h2 : ownIncs x p (r + 1) = ownIncs x p r := (succ_of_res hxr).2.2.1
    rw [this, h2, ← hm]; exact ⟨le_rfl, fun _ => rfl⟩

lemma mem_mono_succ (hs : IsExec s) (hx : IsInput s x ι) (t : ℕ) (q : Fin n) :
    memAt s t q ≤ memAt s (t + 1) q := by
  rcases h : s t with ⟨p, v⟩ | ⟨p, v⟩ | ⟨p, w⟩ | ⟨p, w⟩
  · rw [(step_pre h).1]
    by_cases hq : q = p
    · subst hq; cases v <;> simp [pre5, count_eq_mem hs hx]
    · cases v <;> simp [pre5, Function.update_of_ne hq]
  · rw [(step_sym (by rw [h]; rfl)).1]
  · rw [(step_sym (by rw [h]; rfl)).1]
  · rw [(step_post h).1]

lemma sumMem_mono (hs : IsExec s) (hx : IsInput s x ι) : Monotone (sumMem s) :=
  monotone_nat_of_le_succ fun t => Finset.sum_le_sum fun q _ => mem_mono_succ hs hx t q

lemma incs_eq_sum (x : CWord n) : ∀ k, incs x k = ∑ p, ownIncs x p k
  | 0 => by simp [incs, ownIncs]
  | k + 1 => by
    rw [incs, incs_eq_sum x k]
    simp only [ownIncs, Finset.sum_add_distrib]
    congr 1
    by_cases hi : IsInc (x k) <;> simp [hi]

lemma incs_le_sumMem (hs : IsExec s) (hx : IsInput s x ι) (t : ℕ) :
    incs x (symCount s t) ≤ sumMem s t := by
  rw [incs_eq_sum]; exact Finset.sum_le_sum fun p _ => (mem_eq hs hx t p).1

lemma sumMem_eq (hs : IsExec s) (hx : IsInput s x ι) {t : ℕ}
    (h : ∀ p, phs s t p ≠ .ready .inc) : sumMem s t = incs x (symCount s t) := by
  rw [incs_eq_sum]; exact Finset.sum_congr rfl fun p _ => (mem_eq hs hx t p).2 (h p)

/-- The report at a `post` event (Lines 05–06). -/
theorem post_verdict (hs : IsExec s) (hx : IsInput s x ι) {t : ℕ} {p : Fin n} {w : CRes}
    (h : s t = .post p w) :
    ∃ r < symCount s t, x r = ⟨p, .inr w⟩ ∧ NoP x p r (symCount s t) ∧
      ∃ d, (wecAlg (n := n)).outs s t = some (p, d) ∧
        (d = .no ↔ bad x p (r + 1) ∨ lastRead x p (r + 1) ≠ sumMem s t ∨
          (locAt s t p).prevIncs < sumMem s t) := by
  have hi := inv hs hx t p
  have hv := hs.valid t
  rw [h] at hv; simp only [Enabled, Ev.need, Ev.proc] at hv
  rw [hv] at hi
  obtain ⟨r, hr, hxr, hnp, ⟨hf, hpr, hcr, -⟩, hmo, hinv⟩ := hi
  refine ⟨r, hr, hxr, hnp, _, outs_post_eq h, ?_⟩
  obtain ⟨d1, -, -, d4⟩ := succ_of_res hxr
  rw [postFix_verdict, d4, d1, hf, hinv, hmo, hpr, hcr]
  simp only [sumMem]
  tauto

lemma prevIncs_post {t : ℕ} {p : Fin n} {w : CRes} (h : s t = .post p w) :
    (locAt s (t + 1) p).prevIncs = sumMem s t := by
  rw [(step_post h).2, Function.update_self, postFix_fst]; rfl

lemma prevIncs_of_ne {t : ℕ} {p : Fin n} (h : ∀ w, s t ≠ .post p w) :
    (locAt s (t + 1) p).prevIncs = (locAt s t p).prevIncs := by
  rcases hs : s t with ⟨q, v⟩ | ⟨q, v⟩ | ⟨q, w⟩ | ⟨q, w⟩
  · rw [(step_pre hs).2]
    by_cases hq : p = q
    · subst hq; rw [Function.update_self]; cases v <;> rfl
    · rw [Function.update_of_ne hq]
  · rw [(step_sym (by rw [hs]; rfl)).2]
  · rw [(step_sym (by rw [hs]; rfl)).2]
  · have hq : p ≠ q := by rintro rfl; exact h w hs
    rw [(step_post hs).2, Function.update_of_ne hq]

end Podc2025.LanguageDecidability.Counter
