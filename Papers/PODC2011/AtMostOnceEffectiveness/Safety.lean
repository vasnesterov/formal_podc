import Papers.PODC2011.AtMostOnceEffectiveness.Steps
import Papers.PODC2011.AtMostOnceEffectiveness.Rank

/-!
# Lemma 4.1: `KK_β` solves the at-most-once problem

We prove an inductive invariant `Inv` of all reachable configurations (for `β ≥ 1`).

Notation for a local state `s` of process `p`:
* `Ann s`: `p` has announced `NEXT_p` in `next_p` in its current iteration
  (status `gatherTry`, `gatherDone`, `check`, `do` or `done`);
* `ReadNext s r`: `p` has read `next_r` in its current iteration;
* `ReadDone s r`: `p` has read line `r` of `done` in its current iteration;
* `Busy s`: `p` passed `check` and has not yet recorded the job (`do` or `done`);
* `line C p`: the jobs recorded so far in line `p` of `done`;
* `Claimed C p i`: `i` is recorded in line `p`, or `p` is busy with `i`.

The heart of the proof (the paper's Case 2) is captured by two invariants:
* `K`: two processes that announced the same job and read each other's `next` registers, saw it
  (one of them has it in its `TRY` set);
* `L`: a process `q` that announced job `i` and already read `next_p`, where `p` claims `i`, has
  `i` in its `TRY` or `DONE` set, or `i` is recorded in line `p` and `q` will still read that line.

The paper's argument "`i ∉ t₂.DONE_q` since `t₂.NEXT_q = i`" is not needed.
-/

set_option linter.unusedSectionVars false

namespace Podc.AtMostOnceEffectiveness

open Function

variable {m n β : ℕ} {C C' : Config m Reg ℕ LState} {p q : Fin m}

/-- `p` has written `NEXT_p` to `next_p` in its current iteration. -/
def Ann (s : LState) : Prop :=
  s.status = .gatherTry ∨ s.status = .gatherDone ∨ s.status = .check ∨ s.status = .doIt ∨
    s.status = .done

/-- `p` has read `next_r` in its current iteration. -/
def ReadNext (s : LState) (r : ℕ) : Prop :=
  (s.status = .gatherTry ∧ r < s.q) ∨ s.status = .gatherDone ∨ s.status = .check ∨
    s.status = .doIt ∨ s.status = .done

/-- `p` has read line `r` of `done` in its current iteration. -/
def ReadDone (s : LState) (r : ℕ) : Prop :=
  (s.status = .gatherDone ∧ r < s.q) ∨ s.status = .check ∨ s.status = .doIt ∨ s.status = .done

/-- `p` passed `check` and has not recorded its job yet. -/
def Busy (s : LState) : Prop := s.status = .doIt ∨ s.status = .done

/-- The jobs recorded in line `p` of `done`. -/
def line (C : Config m Reg ℕ LState) (p : Fin m) : List ℕ :=
  (List.range ((C.loc p).pos p - 1)).map (fun j => C.mem (.done p (j + 1)))

/-- The jobs performed by `p`, in order. -/
def plog (C : Config m Reg ℕ LState) (p : Fin m) : List ℕ :=
  (C.log.filter (fun e => e.1 = p)).map Prod.snd

/-- The job performed by `p` but not yet recorded. -/
def pend (C : Config m Reg ℕ LState) (p : Fin m) : List ℕ :=
  if (C.loc p).status = .done then [(C.loc p).nxt] else []

/-- `p` claims job `i`. -/
def Claimed (C : Config m Reg ℕ LState) (p : Fin m) (i : ℕ) : Prop :=
  i ∈ line C p ∨ (Busy (C.loc p) ∧ (C.loc p).nxt = i)

/-- The safety invariant. -/
structure Inv (m n : ℕ) (C : Config m Reg ℕ LState) : Prop where
  ann : ∀ p, Ann (C.loc p) → C.mem (.next p) = (C.loc p).nxt
  nxtJ : ∀ p, (C.loc p).status ≠ .compNext → (C.loc p).status ≠ .finished →
    (C.loc p).nxt ∈ Finset.Icc 1 n
  posOwn : ∀ p : Fin m, 1 ≤ (C.loc p).pos p
  lineZero : ∀ (p : Fin m) j, (C.loc p).pos p ≤ j → C.mem (.done p j) = 0
  plogEq : ∀ p, plog C p = line C p ++ pend C p
  lineJ : ∀ p, ∀ x ∈ line C p, x ∈ Finset.Icc 1 n
  lineNodup : ∀ p, (line C p).Nodup
  own : ∀ p, ∀ x ∈ line C p, x ∈ (C.loc p).doneS
  reader : ∀ p q : Fin m, q ≠ p → 1 ≤ (C.loc p).pos q ∧
    (C.loc p).pos q - 1 ≤ (line C q).length ∧
    ∀ x ∈ (line C q).take ((C.loc p).pos q - 1), x ∈ (C.loc p).doneS
  busy : ∀ p, Busy (C.loc p) → (C.loc p).nxt ∉ (C.loc p).tryS ∧ (C.loc p).nxt ∉ (C.loc p).doneS
  qSet : ∀ p, (C.loc p).status = .setNext → (C.loc p).q = 0
  qlt : ∀ p, ((C.loc p).status = .gatherTry ∨ (C.loc p).status = .gatherDone) → (C.loc p).q < m
  K : ∀ p q : Fin m, p ≠ q → Ann (C.loc p) → Ann (C.loc q) → (C.loc p).nxt = (C.loc q).nxt →
    ReadNext (C.loc p) q → ReadNext (C.loc q) p →
    (C.loc p).nxt ∈ (C.loc p).tryS ∨ (C.loc q).nxt ∈ (C.loc q).tryS
  L : ∀ p q : Fin m, p ≠ q → Ann (C.loc q) → ReadNext (C.loc q) p → Claimed C p (C.loc q).nxt →
    (C.loc q).nxt ∈ (C.loc q).tryS ∨ (C.loc q).nxt ∈ (C.loc q).doneS ∨
      (¬ ReadDone (C.loc q) p ∧ (C.loc q).nxt ∈ line C p)
  S : ∀ p q : Fin m, ∀ i, p ≠ q → Claimed C p i → Claimed C q i → False

/-! ## Frame lemmas for `line`, `plog`, `pend` -/

lemma val_ne_of_ne {a b : Fin m} (h : a ≠ b) : a.val ≠ b.val := fun e => h (Fin.ext e)

lemma KStep.line_ne (hs : KStep m n β C p C') (hq : q ≠ p) : line C' q = line C q := by
  unfold line
  rw [hs.loc_ne hq]
  congr 1
  funext j
  exact hs.mem_done_ne _ _ (val_ne_of_ne hq)

lemma KStep.plog_ne (hs : KStep m n β C p C') (hq : q ≠ p) : plog C' q = plog C q := by
  unfold plog
  cases hs <;> simp [List.filter_append, Ne.symm hq]

lemma KStep.pend_ne (hs : KStep m n β C p C') (hq : q ≠ p) : pend C' q = pend C q := by
  unfold pend; rw [hs.loc_ne hq]

lemma KStep.plog_self (hs : KStep m n β C p C') :
    plog C' p = plog C p ++ (if (C.loc p).status = .doIt then [(C.loc p).nxt] else []) := by
  unfold plog
  cases hs <;> simp_all [List.filter_append]

lemma KStep.pend_self (hs : KStep m n β C p C') :
    pend C' p = (if (C.loc p).status = .doIt then [(C.loc p).nxt] else []) := by
  unfold pend
  cases hs with
  | tryRead h hq => simp [adv_status]; split_ifs <;> simp_all
  | trySkip h hq => simp [adv_status]; split_ifs <;> simp_all
  | doneAdv h hq => simp [adv_status]; split_ifs <;> simp_all
  | _ => simp_all

lemma KStep.line_self (hs : KStep m n β C p C') (hpos : 1 ≤ (C.loc p).pos p) :
    line C' p = line C p ++ pend C p := by
  unfold line pend
  cases hs with
  | writeDone h =>
    simp only [update_self, h, ite_true]
    have : (C.loc p).pos p + 1 - 1 = ((C.loc p).pos p - 1) + 1 := by omega
    rw [this, List.range_succ, List.map_append]
    congr 1
    · apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      rw [update_of_ne]
      intro e; simp only [Reg.done.injEq] at e; omega
    · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      rw [show (C.loc p).pos p - 1 + 1 = (C.loc p).pos p by omega]
      simp
  | doneRead h hq hpos' hv =>
    simp [h, update_of_ne (Ne.symm hq)]
  | _ => simp_all

lemma KStep.doneS_mono (hs : KStep m n β C p C') : (C.loc p).doneS ⊆ (C'.loc p).doneS := by
  cases hs <;> simp [Finset.subset_insert]

lemma KStep.tryS_mono (hs : KStep m n β C p C') (h : (C.loc p).status ≠ .compNext) :
    (C.loc p).tryS ⊆ (C'.loc p).tryS := by
  cases hs <;> simp_all [addTry] <;> split_ifs <;> simp [Finset.subset_insert]

lemma KStep.nxt_eq (hs : KStep m n β C p C') (h : (C.loc p).status ≠ .compNext) :
    (C'.loc p).nxt = (C.loc p).nxt := by
  cases hs <;> simp_all

lemma mem_addTry {v : ℕ} {t : Finset ℕ} (hv : 0 < v) : v ∈ addTry v t := by
  simp [addTry, hv]

lemma subset_addTry (v : ℕ) (t : Finset ℕ) : t ⊆ addTry v t := by
  unfold addTry; split_ifs <;> simp [Finset.subset_insert]

/-- `ReadNext` after a `gatherTry` step: the process has read one more register. -/
lemma readNext_adv {s : LState} {t : Finset ℕ} (hst : s.status = .gatherTry) (hq : s.q < m) (r : ℕ) (hr : r < m)
    (h : ReadNext (({ s with tryS := t } : LState).adv m .gatherDone) r) :
    r < s.q ∨ r = s.q := by
  unfold ReadNext at h
  simp only [adv_status, adv_q] at h
  split_ifs at h with h1 <;> simp [hst] at h <;> omega

lemma readNext_adv' {s : LState} (hst : s.status = .gatherTry) (hq : s.q < m) (r : ℕ) (hr : r < m)
    (h : ReadNext (s.adv m .gatherDone) r) : r < s.q ∨ r = s.q := by
  have : s = ({ s with tryS := s.tryS } : LState) := rfl
  rw [this] at h
  exact readNext_adv hst hq r hr h

/-! ## Preservation of the simple invariants -/

section Simple

variable (hI : Inv m n C) (hs : KStep m n β C p C')
include hI hs

lemma Inv.ann_step : ∀ r, Ann (C'.loc r) → C'.mem (.next r) = (C'.loc r).nxt := by
  intro r hr
  by_cases hrp : r = p
  · subst hrp
    have h0 := hI.ann r
    cases hs with
    | tryRead h hq =>
      simp only [Ann, update_self, adv_status, adv_nxt] at hr ⊢; exact h0 (by simp [Ann, h])
    | trySkip h hq =>
      simp only [Ann, update_self, adv_status, adv_nxt] at hr ⊢; exact h0 (by simp [Ann, h])
    | doneAdv h hq =>
      simp only [Ann, update_self, adv_status, adv_nxt] at hr ⊢; exact h0 (by simp [Ann, h])
    | doneRead h hq hp hv => simp only [update_self]; exact h0 (by simp [Ann, h])
    | checkOk h h1 h2 => simp only [update_self]; exact h0 (by simp [Ann, h])
    | checkFail h h1 => simp [Ann] at hr
    | perform h => simp only [update_self]; exact h0 (by simp [Ann, h])
    | writeDone h => simp [Ann] at hr
    | compNext h hb => simp [Ann] at hr
    | finish h hb => simp [Ann] at hr
    | setNext h => simp
  · rw [hs.loc_ne hrp] at hr ⊢; rw [hs.mem_next_ne _ (val_ne_of_ne hrp)]; exact hI.ann r hr

lemma Inv.nxtJ_step (hβ : 1 ≤ β) : ∀ r, (C'.loc r).status ≠ .compNext →
    (C'.loc r).status ≠ .finished → (C'.loc r).nxt ∈ Finset.Icc 1 n := by
  intro r h1 h2
  by_cases hrp : r = p
  · subst hrp
    have h0 := hI.nxtJ r
    cases hs with
    | compNext h hb =>
      simp only [update_self]
      have hne : (free n (C.loc r) \ (C.loc r).tryS).Nonempty :=
        Finset.card_pos.mp (by omega)
      have := rank_mem hne (kIdx m r (free n (C.loc r)).card)
      simp only [free, Finset.mem_sdiff] at this
      exact this.1.1
    | finish h hb => simp at h2
    | checkFail h h1' => simp at h1
    | writeDone h => simp at h1
    | tryRead h hq => simp only [update_self, adv_nxt]; exact h0 (by simp [h]) (by simp [h])
    | trySkip h hq => simp only [update_self, adv_nxt]; exact h0 (by simp [h]) (by simp [h])
    | doneAdv h hq => simp only [update_self, adv_nxt]; exact h0 (by simp [h]) (by simp [h])
    | doneRead h hq hp hv => simp only [update_self]; exact h0 (by simp [h]) (by simp [h])
    | checkOk h h1' h2' => simp only [update_self]; exact h0 (by simp [h]) (by simp [h])
    | perform h => simp only [update_self]; exact h0 (by simp [h]) (by simp [h])
    | setNext h => simp only [update_self]; exact h0 (by simp [h]) (by simp [h])
  · rw [hs.loc_ne hrp] at h1 h2 ⊢; exact hI.nxtJ r h1 h2

lemma Inv.posOwn_step : ∀ r : Fin m, 1 ≤ (C'.loc r).pos r := by
  intro r
  by_cases hrp : r = p
  · subst hrp
    have h0 := hI.posOwn r
    cases hs with
    | doneRead h hq hp hv => simp [update_of_ne (Ne.symm hq), h0]
    | writeDone h => simp
    | _ => simp_all
  · rw [hs.loc_ne hrp]; exact hI.posOwn r

lemma Inv.lineZero_step : ∀ (r : Fin m) j, (C'.loc r).pos r ≤ j → C'.mem (.done r j) = 0 := by
  intro r j hj
  by_cases hrp : r = p
  · subst hrp
    have h0 := hI.lineZero r
    cases hs with
    | doneRead h hq hp hv =>
      simp only [update_self, update_of_ne (Ne.symm hq)] at hj; exact h0 j hj
    | writeDone h =>
      simp only [update_self] at hj
      simp only
      rw [update_of_ne (by simp only [ne_eq, Reg.done.injEq, true_and]; omega)]
      exact h0 j (by omega)
    | _ => simp_all
  · rw [hs.loc_ne hrp] at hj; rw [hs.mem_done_ne _ _ (val_ne_of_ne hrp)]; exact hI.lineZero r j hj

lemma Inv.plogEq_step : ∀ r, plog C' r = line C' r ++ pend C' r := by
  intro r
  by_cases hrp : r = p
  · subst hrp
    rw [hs.plog_self, hs.line_self (hI.posOwn r), hs.pend_self, hI.plogEq r, List.append_assoc]
  · rw [hs.plog_ne hrp, hs.line_ne hrp, hs.pend_ne hrp]; exact hI.plogEq r

lemma Inv.lineJ_step : ∀ r, ∀ x ∈ line C' r, x ∈ Finset.Icc 1 n := by
  intro r x hx
  by_cases hrp : r = p
  · subst hrp
    rw [hs.line_self (hI.posOwn r), List.mem_append] at hx
    rcases hx with hx | hx
    · exact hI.lineJ r x hx
    · unfold pend at hx
      split_ifs at hx with h
      · simp only [List.mem_singleton] at hx; subst hx
        exact hI.nxtJ r (by simp [h]) (by simp [h])
      · simp at hx
  · rw [hs.line_ne hrp] at hx; exact hI.lineJ r x hx

lemma Inv.lineNodup_step : ∀ r, (line C' r).Nodup := by
  intro r
  by_cases hrp : r = p
  · subst hrp
    rw [hs.line_self (hI.posOwn r)]
    unfold pend
    split_ifs with h
    · rw [List.nodup_append]
      refine ⟨hI.lineNodup r, List.nodup_singleton _, ?_⟩
      intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb
      intro e; subst e
      exact (hI.busy r (Or.inr h)).2 (hI.own r _ ha)
    · simpa using hI.lineNodup r
  · rw [hs.line_ne hrp]; exact hI.lineNodup r

lemma Inv.own_step : ∀ r, ∀ x ∈ line C' r, x ∈ (C'.loc r).doneS := by
  intro r x hx
  by_cases hrp : r = p
  · subst hrp
    rw [hs.line_self (hI.posOwn r), List.mem_append] at hx
    rcases hx with hx | hx
    · exact hs.doneS_mono (hI.own r x hx)
    · unfold pend at hx
      split_ifs at hx with h
      · simp only [List.mem_singleton] at hx; subst hx
        cases hs <;> simp_all
      · simp at hx
  · rw [hs.line_ne hrp] at hx; rw [hs.loc_ne hrp]; exact hI.own r x hx

lemma Inv.busy_step : ∀ r, Busy (C'.loc r) →
    (C'.loc r).nxt ∉ (C'.loc r).tryS ∧ (C'.loc r).nxt ∉ (C'.loc r).doneS := by
  intro r hr
  by_cases hrp : r = p
  · subst hrp
    have h0 := hI.busy r
    cases hs with
    | checkOk h h1 h2 => simp [h1, h2]
    | perform h => simpa using h0 (Or.inl h)
    | tryRead h hq => simp [Busy, adv_status] at hr; split_ifs at hr <;> simp_all
    | trySkip h hq => simp [Busy, adv_status] at hr; split_ifs at hr <;> simp_all
    | doneAdv h hq => simp [Busy, adv_status] at hr; split_ifs at hr <;> simp_all
    | _ => simp_all [Busy]
  · rw [hs.loc_ne hrp] at hr ⊢; exact hI.busy r hr

lemma Inv.qSet_step : ∀ r, (C'.loc r).status = .setNext → (C'.loc r).q = 0 := by
  intro r hr
  by_cases hrp : r = p
  · subst hrp
    cases hs with
    | tryRead h hq => simp [adv_status] at hr; split_ifs at hr <;> simp_all
    | trySkip h hq => simp [adv_status] at hr; split_ifs at hr <;> simp_all
    | doneAdv h hq => simp [adv_status] at hr; split_ifs at hr <;> simp_all
    | _ => simp_all
  · rw [hs.loc_ne hrp] at hr ⊢; exact hI.qSet r hr

lemma Inv.qlt_step : ∀ r, ((C'.loc r).status = .gatherTry ∨ (C'.loc r).status = .gatherDone) →
    (C'.loc r).q < m := by
  intro r hr
  have hm : 0 < m := r.pos
  by_cases hrp : r = p
  · subst hrp
    have h0 := hI.qlt r
    cases hs with
    | tryRead h hq => simp only [update_self, adv_q]; split_ifs <;> omega
    | trySkip h hq => simp only [update_self, adv_q]; split_ifs <;> omega
    | doneAdv h hq => simp only [update_self, adv_q]; split_ifs <;> omega
    | doneRead h hq hp hv => simpa using h0 (Or.inr h)
    | setNext h => simp [hI.qSet r h, hm]
    | _ => simp_all
  · rw [hs.loc_ne hrp] at hr ⊢; exact hI.qlt r hr

omit hs in
lemma Inv.line_length_le (r : Fin m) : (line C r).length ≤ n := by
  have h1 := List.toFinset_card_of_nodup (hI.lineNodup r)
  have h2 : (line C r).toFinset ⊆ Finset.Icc 1 n := by
    intro x hx; exact hI.lineJ r x (List.mem_toFinset.mp hx)
  have := Finset.card_le_card h2
  simp at this; omega

omit hs in
lemma Inv.line_length (r : Fin m) : (line C r).length = (C.loc r).pos r - 1 := by
  simp [line]

omit hs in
lemma Inv.line_getElem (r : Fin m) (j : ℕ) (hj : j < (line C r).length) :
    (line C r)[j] = C.mem (.done r (j + 1)) := by
  simp [line]

lemma Inv.reader_step : ∀ a b : Fin m, b ≠ a → 1 ≤ (C'.loc a).pos b ∧
    (C'.loc a).pos b - 1 ≤ (line C' b).length ∧
    ∀ x ∈ (line C' b).take ((C'.loc a).pos b - 1), x ∈ (C'.loc a).doneS := by
  intro a b hba
  by_cases hap : a = p
  · subst hap
    have hb' : line C' b = line C b := hs.line_ne hba
    rw [hb']
    obtain ⟨h1, h2, h3⟩ := hI.reader a b hba
    cases hs with
    | doneRead h hq hp hv =>
      simp only [update_self]
      by_cases hbr : b.val = (C.loc a).q
      · rw [← hbr] at hp hv ⊢
        simp only [update_self]
        have hlt : (C.loc a).pos b < (C.loc b).pos b := by
          by_contra hc; push Not at hc
          have := hI.lineZero b _ hc; omega
        have hlen := hI.line_length b
        refine ⟨by omega, by omega, ?_⟩
        intro x hx
        rw [show (C.loc a).pos b + 1 - 1 = ((C.loc a).pos b - 1) + 1 by omega,
          List.take_add_one] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact Finset.mem_insert_of_mem (h3 x hx)
        · rw [List.getElem?_eq_getElem (by omega), hI.line_getElem b _ (by omega)] at hx
          simp only [Option.toList_some, List.mem_singleton] at hx
          rw [hx, show (C.loc a).pos b - 1 + 1 = (C.loc a).pos b by omega]
          exact Finset.mem_insert_self _ _
      · rw [update_of_ne hbr]
        exact ⟨h1, h2, fun x hx => Finset.mem_insert_of_mem (h3 x hx)⟩
    | writeDone h =>
      simp only [update_self, update_of_ne (val_ne_of_ne hba)]
      exact ⟨h1, h2, fun x hx => Finset.mem_insert_of_mem (h3 x hx)⟩
    | _ => simp_all
  · rw [hs.loc_ne hap]
    by_cases hbp : b = p
    · subst hbp
      obtain ⟨h1, h2, h3⟩ := hI.reader a b hba
      rw [hs.line_self (hI.posOwn b), List.take_append_of_le_length h2]
      refine ⟨h1, by simp; omega, h3⟩
    · rw [hs.line_ne hbp]; exact hI.reader a b hba

/-- `K` for a pair containing the stepping process. -/
lemma Inv.K_step_self (a : Fin m) (ha : a ≠ p) (hp : Ann (C'.loc p)) (hpa : Ann (C'.loc a))
    (heq : (C'.loc p).nxt = (C'.loc a).nxt) (h1 : ReadNext (C'.loc p) a)
    (h2 : ReadNext (C'.loc a) p) :
    (C'.loc p).nxt ∈ (C'.loc p).tryS ∨ (C'.loc a).nxt ∈ (C'.loc a).tryS := by
  rw [hs.loc_ne ha] at hpa h2 heq ⊢
  have K0 := hI.K p a (Ne.symm ha)
  cases hs with
  | compNext h hb => simp [Ann] at hp
  | finish h hb => simp [Ann] at hp
  | checkFail h h1' => simp [Ann] at hp
  | writeDone h => simp [Ann] at hp
  | setNext h => simp [ReadNext, hI.qSet p h] at h1
  | tryRead h hq =>
    simp only [update_self, adv_nxt, adv_tryS] at h1 heq ⊢
    have hqm := hI.qlt p (Or.inl h)
    rcases readNext_adv h hqm a a.isLt h1 with hlt | hlt
    · rcases K0 (by simp [Ann, h]) hpa heq (Or.inl ⟨h, hlt⟩) h2 with h3 | h3
      · exact Or.inl (subset_addTry _ _ h3)
      · exact Or.inr h3
    · left
      rw [← hlt, hI.ann a hpa, ← heq]
      exact mem_addTry (Finset.mem_Icc.mp (hI.nxtJ p (by simp [h]) (by simp [h]))).1
  | trySkip h hq =>
    simp only [update_self, adv_nxt, adv_tryS] at h1 heq ⊢
    have hqm := hI.qlt p (Or.inl h)
    rcases readNext_adv' h hqm a a.isLt h1 with hlt | hlt
    · exact K0 (by simp [Ann, h]) hpa heq (Or.inl ⟨h, hlt⟩) h2
    · exact absurd (Fin.ext (hlt.trans hq)) ha
  | doneRead h hq hp' hv =>
    simp only [update_self] at heq ⊢; exact K0 (by simp [Ann, h]) hpa heq (by simp [ReadNext, h]) h2
  | doneAdv h hq =>
    simp only [update_self, adv_nxt, adv_tryS] at heq ⊢
    exact K0 (by simp [Ann, h]) hpa heq (by simp [ReadNext, h]) h2
  | checkOk h h1' h2' =>
    simp only [update_self] at heq ⊢; exact K0 (by simp [Ann, h]) hpa heq (by simp [ReadNext, h]) h2
  | perform h =>
    simp only [update_self] at heq ⊢; exact K0 (by simp [Ann, h]) hpa heq (by simp [ReadNext, h]) h2

lemma Inv.K_step : ∀ a b : Fin m, a ≠ b → Ann (C'.loc a) → Ann (C'.loc b) →
    (C'.loc a).nxt = (C'.loc b).nxt → ReadNext (C'.loc a) b → ReadNext (C'.loc b) a →
    (C'.loc a).nxt ∈ (C'.loc a).tryS ∨ (C'.loc b).nxt ∈ (C'.loc b).tryS := by
  intro a b hab ha hb heq h1 h2
  by_cases hap : a = p
  · subst hap; exact hI.K_step_self hs b (Ne.symm hab) ha hb heq h1 h2
  · by_cases hbp : b = p
    · subst hbp; exact (hI.K_step_self hs a hab hb ha heq.symm h2 h1).symm
    · rw [hs.loc_ne hap, hs.loc_ne hbp] at *
      exact hI.K a b hab ha hb heq h1 h2

lemma Inv.claimed_mono {a : Fin m} {i : ℕ} (h : Claimed C a i) : Claimed C' a i := by
  by_cases hap : a = p
  · subst hap
    unfold Claimed at h ⊢
    rw [hs.line_self (hI.posOwn a)]
    rcases h with h | ⟨hb, he⟩
    · exact Or.inl (List.mem_append_left _ h)
    · rcases hb with hb | hb
      · cases hs <;> simp_all [Busy]
      · left; apply List.mem_append_right; simp [pend, hb, he]
  · unfold Claimed at h ⊢; rw [hs.line_ne hap, hs.loc_ne hap]; exact h

lemma Inv.claimed_new {a : Fin m} {i : ℕ} (h : Claimed C' a i) : Claimed C a i ∨
    (a = p ∧ (C.loc p).status = .check ∧ (C.loc p).nxt ∉ (C.loc p).tryS ∧
      (C.loc p).nxt ∉ (C.loc p).doneS ∧ i = (C.loc p).nxt) := by
  by_cases hap : a = p
  · subst hap
    unfold Claimed at h
    rw [hs.line_self (hI.posOwn a), List.mem_append] at h
    rcases h with (h | h) | ⟨hb, he⟩
    · exact Or.inl (Or.inl h)
    · unfold pend at h; split_ifs at h with h'
      · simp only [List.mem_singleton] at h; exact Or.inl (Or.inr ⟨Or.inr h', h.symm⟩)
      · simp at h
    · cases hs with
      | checkOk h h1 h2 => right; simp_all
      | perform h => left; right; simp_all [Busy]
      | tryRead h hq => simp [Busy, adv_status] at hb; split_ifs at hb <;> simp_all
      | trySkip h hq => simp [Busy, adv_status] at hb; split_ifs at hb <;> simp_all
      | doneAdv h hq => simp [Busy, adv_status] at hb; split_ifs at hb <;> simp_all
      | _ => simp_all [Busy]
  · unfold Claimed at h ⊢; rw [hs.line_ne hap, hs.loc_ne hap] at h; exact Or.inl h

lemma Inv.S_step : ∀ a b : Fin m, ∀ i, a ≠ b → Claimed C' a i → Claimed C' b i → False := by
  intro a b i hab ha hb
  have key : ∀ c, c ≠ p → Claimed C c i → (C.loc p).status = .check →
      (C.loc p).nxt ∉ (C.loc p).tryS → (C.loc p).nxt ∉ (C.loc p).doneS → i = (C.loc p).nxt →
      False := by
    intro c hc hcl hst h1 h2 hi
    subst hi
    rcases hI.L c p hc (by simp [Ann, hst]) (by simp [ReadNext, hst]) hcl with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h.1 (by simp [ReadDone, hst])
  rcases hI.claimed_new hs ha with ha' | ⟨rfl, hst, h1, h2, hi⟩ <;>
    rcases hI.claimed_new hs hb with hb' | ⟨rfl, hst', h1', h2', hi'⟩
  · exact hI.S a b i hab ha' hb'
  · exact key a hab ha' hst' h1' h2' hi'
  · exact key b (Ne.symm hab) hb' hst h1 h2 hi
  · exact hab rfl

/-- `L` when the stepping process is the reader. -/
lemma Inv.L_step_reader (a : Fin m) (ha : a ≠ p) (hp : Ann (C'.loc p))
    (h1 : ReadNext (C'.loc p) a) (hcl : Claimed C' a (C'.loc p).nxt) :
    (C'.loc p).nxt ∈ (C'.loc p).tryS ∨ (C'.loc p).nxt ∈ (C'.loc p).doneS ∨
      (¬ ReadDone (C'.loc p) a ∧ (C'.loc p).nxt ∈ line C' a) := by
  have hcl' : Claimed C a (C'.loc p).nxt := by
    unfold Claimed at hcl ⊢; rwa [hs.line_ne ha, hs.loc_ne ha] at hcl
  rw [hs.line_ne ha]
  have L0 := hI.L a p ha
  cases hs with
  | compNext h hb => simp [Ann] at hp
  | finish h hb => simp [Ann] at hp
  | checkFail h h1' => simp [Ann] at hp
  | writeDone h => simp [Ann] at hp
  | setNext h => simp [ReadNext, hI.qSet p h] at h1
  | tryRead h hq =>
    simp only [update_self, adv_nxt, adv_tryS, adv_doneS] at h1 hcl' ⊢
    have hnrd : ¬ ReadDone ((({ (C.loc p) with
        tryS := addTry (C.mem (.next (C.loc p).q)) (C.loc p).tryS }) : LState).adv m .gatherDone) a := by
      unfold ReadDone; simp only [adv_status, adv_q]; split_ifs <;> simp [h]
    have hqm := hI.qlt p (Or.inl h)
    rcases readNext_adv h hqm a a.isLt h1 with hlt | hlt
    · rcases L0 (by simp [Ann, h]) (Or.inl ⟨h, hlt⟩) hcl' with h3 | h3 | h3
      · exact Or.inl (subset_addTry _ _ h3)
      · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr ⟨hnrd, h3.2⟩)
    · rcases hcl' with h3 | ⟨hb, he⟩
      · exact Or.inr (Or.inr ⟨hnrd, h3⟩)
      · left
        have hann : Ann (C.loc a) := by rcases hb with hb | hb <;> simp [Ann, hb]
        rw [← hlt, hI.ann a hann, he]
        exact mem_addTry (Finset.mem_Icc.mp (hI.nxtJ p (by simp [h]) (by simp [h]))).1
  | trySkip h hq =>
    simp only [update_self, adv_nxt, adv_tryS, adv_doneS] at h1 hcl' ⊢
    have hnrd : ¬ ReadDone ((C.loc p).adv m .gatherDone) a := by
      unfold ReadDone; simp only [adv_status, adv_q]; split_ifs <;> simp [h]
    have hqm := hI.qlt p (Or.inl h)
    rcases readNext_adv' h hqm a a.isLt h1 with hlt | hlt
    · rcases L0 (by simp [Ann, h]) (Or.inl ⟨h, hlt⟩) hcl' with h3 | h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr ⟨hnrd, h3.2⟩)
    · exact absurd (Fin.ext (hlt.trans hq)) ha
  | doneRead h hq hp' hv =>
    simp only [update_self] at hcl' ⊢
    rcases L0 (by simp [Ann, h]) (by simp [ReadNext, h]) hcl' with h3 | h3 | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl (Finset.mem_insert_of_mem h3))
    · exact Or.inr (Or.inr ⟨by simpa [ReadDone, h] using h3.1, h3.2⟩)
  | doneAdv h hq =>
    simp only [update_self, adv_nxt, adv_tryS, adv_doneS] at hcl' ⊢
    rcases L0 (by simp [Ann, h]) (by simp [ReadNext, h]) hcl' with h3 | h3 | ⟨h3, h4⟩
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
    · by_cases hrd : ReadDone ((C.loc p).adv m .check) a
      · right; left
        have hqm := hI.qlt p (Or.inr h)
        have haq : a.val = (C.loc p).q := by
          unfold ReadDone at h3 hrd
          simp only [adv_status, adv_q] at hrd
          simp only [h] at h3
          have := a.isLt
          split_ifs at hrd <;> simp [h] at hrd h3 <;> omega
        have hq' : ¬ ((C.loc p).pos a ≤ n ∧ 0 < C.mem (.done a ((C.loc p).pos a))) := by
          rcases hq with hq | hq
          · exact absurd (Fin.ext (haq.trans hq)) ha
          · rwa [haq]
        obtain ⟨r1, r2, r3⟩ := hI.reader p a ha
        have hlen : (line C a).length ≤ (C.loc p).pos a - 1 := by
          by_contra hc; push Not at hc
          apply hq'
          have hj := hI.lineJ a _ (List.getElem_mem hc)
          rw [hI.line_getElem a _ hc, show (C.loc p).pos ↑a - 1 + 1 = (C.loc p).pos a by omega]
            at hj
          have := hI.line_length_le a
          simp only [Finset.mem_Icc] at hj
          constructor <;> omega
        exact r3 _ (by rw [List.take_of_length_le hlen]; exact h4)
      · exact Or.inr (Or.inr ⟨hrd, h4⟩)
  | checkOk h h1' h2' =>
    simp only [update_self] at hcl' ⊢
    rcases L0 (by simp [Ann, h]) (by simp [ReadNext, h]) hcl' with h3 | h3 | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
    · exact absurd (by simp [ReadDone, h]) h3.1
  | perform h =>
    simp only [update_self] at hcl' ⊢
    rcases L0 (by simp [Ann, h]) (by simp [ReadNext, h]) hcl' with h3 | h3 | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
    · exact absurd (by simp [ReadDone, h]) h3.1

lemma Inv.L_step : ∀ a b : Fin m, a ≠ b → Ann (C'.loc b) → ReadNext (C'.loc b) a →
    Claimed C' a (C'.loc b).nxt →
    (C'.loc b).nxt ∈ (C'.loc b).tryS ∨ (C'.loc b).nxt ∈ (C'.loc b).doneS ∨
      (¬ ReadDone (C'.loc b) a ∧ (C'.loc b).nxt ∈ line C' a) := by
  intro a b hab hb h1 hcl
  by_cases hbp : b = p
  · subst hbp; exact hI.L_step_reader hs a hab hb h1 hcl
  · rw [hs.loc_ne hbp] at hb h1 hcl ⊢
    by_cases hap : a = p
    · subst hap
      rcases hI.claimed_new hs hcl with hcl' | ⟨_, hst, h1', h2', hi⟩
      · rcases hI.L a b hab hb h1 hcl' with h3 | h3 | h3
        · exact Or.inl h3
        · exact Or.inr (Or.inl h3)
        · refine Or.inr (Or.inr ⟨h3.1, ?_⟩)
          rw [hs.line_self (hI.posOwn a)]; exact List.mem_append_left _ h3.2
      · rcases hI.K a b hab (by simp [Ann, hst]) hb hi.symm (by simp [ReadNext, hst]) h1 with
          h3 | h3
        · exact absurd h3 h1'
        · exact Or.inl h3
    · rw [hs.line_ne hap]
      have hcl' : Claimed C a (C.loc b).nxt := by
        unfold Claimed at hcl ⊢; rwa [hs.line_ne hap, hs.loc_ne hap] at hcl
      exact hI.L a b hab hb h1 hcl'

end Simple

end Podc.AtMostOnceEffectiveness

namespace Podc.AtMostOnceEffectiveness

open Function

variable {m n β : ℕ} {C C' : Config m Reg ℕ LState} {p q : Fin m}

/-- The invariant is preserved by every step (for `β ≥ 1`). -/
theorem Inv.step (hβ : 1 ≤ β) (hI : Inv m n C) (hs : (kk m n β).step C p = some C') :
    Inv m n C' :=
  have hs := step_inv hs
  { ann := hI.ann_step hs
    nxtJ := hI.nxtJ_step hs hβ
    posOwn := hI.posOwn_step hs
    lineZero := hI.lineZero_step hs
    plogEq := hI.plogEq_step hs
    lineJ := hI.lineJ_step hs
    lineNodup := hI.lineNodup_step hs
    own := hI.own_step hs
    reader := hI.reader_step hs
    busy := hI.busy_step hs
    qSet := hI.qSet_step hs
    qlt := hI.qlt_step hs
    K := hI.K_step hs
    L := hI.L_step hs
    S := hI.S_step hs }

lemma line_init (p : Fin m) : line (kk m n β).init p = [] := by
  unfold line; simp [Alg.init, kk, LState.init]

theorem Inv.init : Inv m n (kk m n β).init where
  ann := by intro p h; simp [Ann, Alg.init, kk, LState.init] at h
  nxtJ := by intro p h; simp [Alg.init, kk, LState.init] at h
  posOwn := by intro p; simp [Alg.init, kk, LState.init]
  lineZero := by intro p j _; simp [Alg.init, kk]
  plogEq := by intro p; rw [line_init]; simp [plog, pend, Alg.init, kk, LState.init]
  lineJ := by intro p x hx; simp [line_init] at hx
  lineNodup := by intro p; simp [line_init]
  own := by intro p x hx; simp [line_init] at hx
  reader := by intro p q _; simp [line_init, Alg.init, kk, LState.init]
  busy := by intro p h; simp [Busy, Alg.init, kk, LState.init] at h
  qSet := by intro p h; simp [Alg.init, kk, LState.init] at h
  qlt := by intro p h; simp [Alg.init, kk, LState.init] at h
  K := by intro p q _ h; simp [Ann, Alg.init, kk, LState.init] at h
  L := by intro p q _ h; simp [Ann, Alg.init, kk, LState.init] at h
  S := by
    intro p q i _ h; simp only [Claimed, line_init] at h; simp [Busy, Alg.init, kk, LState.init] at h

/-- Every reachable configuration satisfies the invariant (for `β ≥ 1`). -/
theorem Inv.of_reachable (hβ : 1 ≤ β) {C : Config m Reg ℕ LState}
    (h : (kk m n β).Reachable C) : Inv m n C := by
  induction h with
  | init => exact Inv.init
  | step _ hs ih => exact ih.step hβ hs

lemma count_map_snd_eq_sum (l : List (Fin m × ℕ)) (i : ℕ) :
    (l.map Prod.snd).count i =
      ∑ p : Fin m, ((l.filter (fun e => e.1 = p)).map Prod.snd).count i := by
  induction l with
  | nil => simp
  | cons e l ih =>
    have h : ∀ p : Fin m, ((List.filter (fun x => decide (x.1 = p)) (e :: l)).map Prod.snd).count i
        = (if e.1 = p then (if e.2 = i then 1 else 0) else 0) +
          ((List.filter (fun x => decide (x.1 = p)) l).map Prod.snd).count i := by
      intro p; by_cases h : e.1 = p <;> simp [List.filter_cons, h, List.count_cons] <;> omega
    rw [Finset.sum_congr rfl (fun p _ => h p), Finset.sum_add_distrib, ← ih]
    simp [List.count_cons, Finset.sum_ite_eq]
    omega

/-- In a configuration satisfying the invariant, every job of `{1, …, n}` was performed at most
once. -/
theorem Inv.count_le_one (hI : Inv m n C) (i : ℕ) : (C.log.map Prod.snd).count i ≤ 1 := by
  rw [count_map_snd_eq_sum]
  have hp : ∀ p, (plog C p).count i ≤ 1 := by
    intro p
    rw [hI.plogEq p, List.count_append]
    have h1 := List.nodup_iff_count_le_one.mp (hI.lineNodup p) i
    unfold pend; split_ifs with h
    · by_cases hi : i = (C.loc p).nxt
      · subst hi
        have : (C.loc p).nxt ∉ line C p := fun hm => (hI.busy p (Or.inr h)).2 (hI.own p _ hm)
        rw [List.count_eq_zero_of_not_mem this]; simp
      · simp [List.count_singleton', Ne.symm hi]; exact h1
    · simpa using h1
  have hcl : ∀ p, 0 < (plog C p).count i → Claimed C p i := by
    intro p hc
    rw [List.count_pos_iff, hI.plogEq p, List.mem_append] at hc
    rcases hc with hc | hc
    · exact Or.inl hc
    · unfold pend at hc; split_ifs at hc with h
      · simp only [List.mem_singleton] at hc; exact Or.inr ⟨Or.inr h, hc.symm⟩
      · simp at hc
  by_cases hex : ∃ p, 0 < (plog C p).count i
  · obtain ⟨p, hpos⟩ := hex
    rw [Finset.sum_eq_single p]
    · exact hp p
    · intro b _ hb
      by_contra hc
      exact hI.S b p i hb (hcl b (Nat.pos_of_ne_zero hc)) (hcl p hpos)
    · simp
  · push Not at hex
    have : ∀ p, (plog C p).count i = 0 := fun p => Nat.le_zero.mp (hex p)
    simp only [plog] at this
    simp [this]

/-- **Lemma 4.1** of [Kentros–Kiayias]: algorithm `KK_β` solves the at-most-once problem; no
execution contains `do_{p,i}` and `do_{q,i}` for the same job (with `p = q` or `p ≠ q`).
The paper states it for every `β`; for `β = 0` the algorithm may pick a "job" from an empty set
(the paper's `rank` is undefined there), so we assume `β ≥ 1`. -/
theorem lemma_4_1 (hβ : 1 ≤ β) : (kk m n β).AtMostOnce n := by
  intro C hC j _
  exact (Inv.of_reachable hβ hC).count_le_one j

end Podc.AtMostOnceEffectiveness
