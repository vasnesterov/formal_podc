import Papers.PODC2025.AuditingWithoutLeaks.Inv
import Cslib.Computability.Distributed.SharedMemory.Potential

/-!
# Wait-freedom of Algorithm 1 (Lemma 2)

Readers take at most three steps per read; an audit takes `(R.seq - lsa)(m+1) + 2` steps after
reading `R`. A write performs at most `m + 1` failed iterations of its repeat loop with the same
`R.seq`: an iteration fails without a change of `R.seq` only if some reader inserted itself into
the (encrypted) reader set meanwhile, and each reader does so at most once per sequence number
(Lemma 17). After `R.seq` reaches the writer's sequence number, the next read of `R` exits the
loop. The potential below formalizes this; since an auditor's number of steps is only determined
by its read of `R`, the potential is used after the process' first step.
-/

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au] {v₀ : V}
  {rnd : ℕ → Fin m → Bool}

variable (rnd) in
/-- Number of readers recorded in the tracking bits of `r`. -/
def fcount (r : RVal m V) : ℕ := (Finset.univ.filter fun i => r.bits i ≠ rnd r.seq i).card

lemma fcount_le (r : RVal m V) : fcount rnd r ≤ m := by
  unfold fcount
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- Remaining steps inside a writer's loop iteration. -/
def wpos : Loc m V → ℕ
  | .wV _ _ r => (todoOf rnd r).length + 2
  | .wB _ _ _ todo => todo.length + 1
  | .wCAS _ _ _ => 1
  | _ => 0

variable (rnd) in
/-- The potential of a process (meaningful while it is pending). -/
noncomputable def pot (C : Cfg m W Au V v₀) : Proc m W Au → ℕ
  | .rd j => match C.loc (.rd j) with
    | .rSN _ => 3
    | .rFX _ _ => 2
    | .rCAS _ _ _ => 1
    | _ => 0
  | .wr w => match C.loc (.wr w) with
    | .wSN _ => (m + 1) * (m + 3) + 3
    | .wR _ sn => if sn ≤ (rOf C).seq then 2 else (m - fcount rnd (rOf C) + 1) * (m + 3) + 2
    | .wV _ sn r | .wB _ sn r _ | .wCAS _ sn r =>
      wpos (rnd := rnd) (C.loc (.wr w)) +
        (if (rOf C).seq < sn then (m - fcount rnd r) * (m + 3) + 2 else 2)
    | .wHelp _ => 1
    | _ => 0
  | .au a => match C.loc (.au a) with
    | .aV _ r s => (r.seq - s) * (m + 1) + 1
    | .aB _ r s _ j => (r.seq - s - 1) * (m + 1) + (m - j.val) + 1
    | .aCAS _ _ => 1
    | _ => 0

section
variable {C C' : Cfg m W Au V v₀}

lemma fcount_mono (E : Evo rnd C C') (h : (rOf C').seq = (rOf C).seq) :
    fcount rnd (rOf C) ≤ fcount rnd (rOf C') := by
  unfold fcount
  apply Finset.card_le_card
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro hi
  have hf : Fetched rnd C i (rOf C).seq := Or.inr ⟨rfl, hi⟩
  rcases E.fet _ _ hf with ⟨h1, -⟩ | ⟨-, h2⟩
  · omega
  · rw [h]; exact h2

/-- Steps of other processes do not increase the potential. -/
lemma pot_other (hI : Inv rnd C) {ℓ : Label (Proc m W Au) (auditReg m V v₀)}
    (hs : (alg1 rnd v₀).step C ℓ = some C') {p : Proc m W Au} (hp : ℓ.proc ≠ p) :
    pot rnd C' p ≤ pot rnd C p := by
  have E := (Inv.step hI hs).2
  have hloc : C'.loc p = C.loc p := by
    have hp' : p ≠ ℓ.proc := Ne.symm hp
    cases ℓ with
    | inv q o => obtain ⟨-, -, -, h, -⟩ := Impl.step_inv hs; simp only [Label.proc] at hp'; simp [h, Function.update_of_ne hp']
    | ret q r => obtain ⟨-, -, -, l, -, h⟩ := Impl.step_ret hs; simp only [Label.proc] at hp'; simp [h, Function.update_of_ne hp']
    | tau q => obtain ⟨-, -, i, o, k, -, -, h⟩ := Impl.step_tau hs; simp only [Label.proc] at hp'; simp [h, Function.update_of_ne hp']
  cases p with
  | rd j => simp only [pot, hloc]; exact le_rfl
  | au a => simp only [pot, hloc]; exact le_rfl
  | wr w =>
    have hw := hI.wr w
    unfold WInv at hw
    have hseq := E.seq
    simp only [pot, hloc]
    cases hl : C.loc (.wr w) <;> simp only [hl] at hw ⊢
    case wR v sn =>
      obtain ⟨-, -, h3⟩ := hw
      have := hI.seq_le
      by_cases h1 : sn ≤ (rOf C).seq
      · simp [h1, (show sn ≤ (rOf C').seq by omega)]
      · rw [if_neg h1]
        by_cases h2 : sn ≤ (rOf C').seq
        · rw [if_pos h2]; omega
        · rw [if_neg h2]
          have heq : (rOf C').seq = (rOf C).seq := by have := hI.sn_le; omega
          have := fcount_mono E heq
          have := fcount_le (rnd := rnd) (rOf C)
          have : m - fcount rnd (rOf C') ≤ m - fcount rnd (rOf C) := by omega
          exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
    all_goals first
      | exact le_rfl
      | (apply Nat.add_le_add_left; split_ifs <;> omega)

lemma todoOf_length_le (r : RVal m V) : (todoOf rnd r).length ≤ m := by
  unfold todoOf
  exact (List.length_filter_le _ _).trans (by simp)

/-- A failed compare&swap of a writer whose triple has the current sequence number means that
some reader inserted itself meanwhile (Lemma 2 / Lemma 17). -/
lemma fcount_lt {C : Cfg m W Au V v₀} (hI : Inv rnd C) {sn : ℕ} {r : RVal m V}
    (hw : WR rnd C sn r) (hlt : (rOf C).seq < sn) (hne : rOf C ≠ r) :
    fcount rnd r < fcount rnd (rOf C) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hw
  have hs : r.seq = (rOf C).seq := by omega
  have hv : r.val = (rOf C).val := by rw [h3, hs]; simp [AuditingWithoutLeaks.hv]
  have hsub : ∀ i, r.bits i ≠ rnd r.seq i → (rOf C).bits i ≠ rnd (rOf C).seq i := by
    intro i hi
    rcases h4 i hi with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · rwa [hs] at h
  obtain ⟨i, hi⟩ : ∃ i, r.bits i ≠ (rOf C).bits i := by
    by_contra hc
    push_neg at hc
    apply hne
    cases r; cases h : rOf C
    simp only [h] at hs hv hc
    simp only [RVal.mk.injEq]
    exact ⟨hs.symm, hv.symm, funext fun i => (hc i).symm⟩
  have hbool : ∀ a b c : Bool, a ≠ c → b ≠ c → a = b := by decide
  have hri : r.bits i = rnd r.seq i := by
    by_contra hc
    exact hi (hbool _ _ _ hc (by rw [hs]; exact hsub i hc))
  have hRi : (rOf C).bits i ≠ rnd (rOf C).seq i := by
    rw [← hs, ← hri]; exact fun h => hi h.symm
  unfold fcount
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub' => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hsub x hx
  · have := hsub' (show i ∈ Finset.univ.filter (fun i => (rOf C).bits i ≠ rnd (rOf C).seq i) by
      simp [hRi])
    simp [hri] at this

lemma aNext_ne_aR {A A' : Set (Fin m × V)} {r : RVal m V} {s lsa : ℕ} :
    aNext rnd A r s ≠ .aR A' lsa := by
  unfold aNext; split_ifs <;> simp

/-- Internal steps of `p` decrease its potential (unless `p` is about to read `R` in an audit),
and never lead to the state `aR`. -/
lemma pot_own {C C' : Cfg m W Au V v₀} (hI : Inv rnd C) {p : Proc m W Au}
    (hs : (alg1 rnd v₀).step C (.tau p) = some C') (hnaR : ∀ A lsa, C.loc p ≠ .aR A lsa) :
    pot rnd C' p < pot rnd C p ∧ ∀ A lsa, C'.loc p ≠ .aR A lsa := by
  obtain ⟨h0, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
  have hnew : C'.loc p = k ((BO m V v₀ i).δ (C.mem i) o).2 := by simp [hloc]
  cases p with
  | rd j =>
    cases hl : C.loc (.rd j) <;> simp only [alg1, readerAct, hl, reduceCtorEq] at hact <;>
      simp only [Action.access.injEq] at hact <;> obtain ⟨rfl, ho, hk⟩ := hact <;>
      obtain rfl := eq_of_heq ho <;> obtain rfl := eq_of_heq hk
    case rSN prev =>
      by_cases hsil : prev.map Prod.fst = some (C.mem .SN)
      · obtain ⟨⟨x, pv⟩, rfl, hx⟩ := Option.map_eq_some_iff.1 hsil
        simp only at hx
        have : C'.loc (.rd j) = .rRet (some (x, pv)) pv := by simp [hnew, hx]
        simp [pot, this, hl]
      · have : C'.loc (.rd j) = .rFX prev (C.mem .SN) := by simp [hnew, hsil]
        simp [pot, this, hl]
    all_goals simp [pot, hnew, hl]
  | au a =>
    have hr := hI.au a
    unfold AInv at hr
    cases hl : C.loc (.au a) <;> rw [hl] at hr <;>
      simp only [alg1, auditorAct, hl, reduceCtorEq] at hact
    case aR A lsa => exact absurd hl (hnaR A lsa)
    all_goals
      simp only [Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact
      obtain rfl := eq_of_heq ho
      obtain rfl := eq_of_heq hk
      simp only [pot, hnew, hl]
    case aCAS A r => simp
    case aV A r s =>
      have hs' := hr.2.2.1
      unfold aVnext
      split_ifs with hm
      · refine ⟨?_, by simp⟩
        simp only
        have : (r.seq - s - 1) * (m + 1) + (m + 1) = (r.seq - s) * (m + 1) := by
          rw [← Nat.succ_mul]; congr 1; omega
        omega
      · have hm0 : m = 0 := by omega
        subst hm0
        unfold aNext
        split_ifs with h2
        · simp; omega
        · simp; omega
    case aB A r s val j =>
      have hs' := hr.2.2.1
      have hj := j.2
      unfold aBnext
      split_ifs with hm
      · simp; omega
      · unfold aNext
        split_ifs with h2
        · simp
          have : r.seq - (s + 1) = r.seq - s - 1 := by omega
          rw [this]; omega
        · simp; omega
  | wr w =>
    have hr := hI.wr w
    unfold WInv at hr
    cases hl : C.loc (.wr w) <;> rw [hl] at hr <;>
      simp only [alg1, writerAct, hl, reduceCtorEq] at hact
    case wB v sn r todo =>
      cases todo with
      | nil => simp at hact
      | cons j rest =>
        simp only [Action.access.injEq] at hact
        obtain ⟨rfl, ho, hk⟩ := hact
        obtain rfl := eq_of_heq ho
        obtain rfl := eq_of_heq hk
        have hR : rOf C' = rOf C := by simp [rOf, hmem]
        simp only [pot, hnew, hl, hR]
        cases rest with
        | nil => simp [wBnext, wpos]
        | cons j2 rest2 => simp [wBnext, wpos]
    all_goals
      simp only [Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact
      obtain rfl := eq_of_heq ho
      obtain rfl := eq_of_heq hk
    case wSN v =>
      have hR : rOf C' = rOf C := by simp [rOf, hmem]
      simp only [pot, hnew, hl, hR]
      refine ⟨?_, by simp⟩
      split_ifs
      · omega
      · have : m - fcount rnd (rOf C) + 1 ≤ m + 1 := by omega
        have := Nat.mul_le_mul_right (m + 3) this
        omega
    case wR v sn =>
      have hR : rOf C' = rOf C := by simp [rOf, hmem]
      simp only [pot, hnew, hl, hR]
      by_cases hb : sn ≤ (rOf C).seq
      · have : sn ≤ (C.mem .R : RVal m V).seq := hb
        simp [this, hb]
      · have : ¬ sn ≤ (C.mem .R : RVal m V).seq := hb
        simp only [this, ↓reduceIte, hb]
        refine ⟨?_, by simp⟩
        simp only [wpos]
        have h1 : (C.mem .R : RVal m V) = rOf C := rfl
        rw [h1, if_pos (by omega)]
        have := todoOf_length_le (rnd := rnd) (rOf C)
        have : (m - fcount rnd (rOf C) + 1) * (m + 3) = (m - fcount rnd (rOf C)) * (m + 3) + (m + 3) := by
          rw [Nat.succ_mul]
        omega
    case wV v sn r =>
      have hR : rOf C' = rOf C := by simp [rOf, hmem]
      simp only [pot, hnew, hl, hR]
      cases htd : todoOf rnd r with
      | nil => simp [wBnext, wpos, htd]
      | cons j rest => simp [wBnext, wpos, htd]
    case wCAS v sn r =>
      obtain ⟨hp1, hw, -, -⟩ := hr
      by_cases heq : (C.mem .R : RVal m V) = r
      · simp [pot, hnew, hl, heq, wpos]; split_ifs <;> omega
      · have hR : rOf C' = rOf C := by simp [rOf, hmem, heq]
        have hnew' : C'.loc (.wr w) = .wR v sn := by simp [hnew, heq]
        simp only [pot, hnew', hl, hR, wpos]
        refine ⟨?_, by simp⟩
        by_cases hb : sn ≤ (rOf C).seq
        · simp only [hb, ↓reduceIte, if_neg (show ¬ (rOf C).seq < sn by omega)]; omega
        · simp only [hb, ↓reduceIte, if_pos (show (rOf C).seq < sn by omega)]
          have := fcount_lt hI hw (by omega) heq
          have := fcount_le (rnd := rnd) (rOf C)
          have h2 : m - fcount rnd (rOf C) + 1 ≤ m - fcount rnd r := by omega
          have := Nat.mul_le_mul_right (m + 3) h2
          omega
    case wHelp sn => simp [pot, hnew, hl]

/-- An internal step never leads to the state `aR` (entered only by an invocation). -/
lemma tau_not_aR {C C' : Cfg m W Au V v₀} {p : Proc m W Au}
    (hs : (alg1 rnd v₀).step C (.tau p) = some C') : ∀ A lsa, C'.loc p ≠ .aR A lsa := by
  obtain ⟨h0, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
  have hnew : C'.loc p = k ((BO m V v₀ i).δ (C.mem i) o).2 := by simp [hloc]
  intro A lsa
  rw [hnew]
  cases p with
  | rd j =>
    cases hl : C.loc (.rd j) <;> simp only [alg1, readerAct, hl, reduceCtorEq] at hact <;>
      simp only [Action.access.injEq] at hact <;> obtain ⟨rfl, ho, hk⟩ := hact <;>
      obtain rfl := eq_of_heq ho <;> obtain rfl := eq_of_heq hk <;> simp <;> split <;>
      (try split) <;> (try split) <;> simp
  | wr w =>
    cases hl : C.loc (.wr w) <;> simp only [alg1, writerAct, hl, reduceCtorEq] at hact
    case wB v sn r todo =>
      cases todo with
      | nil => simp at hact
      | cons j rest =>
        simp only [Action.access.injEq] at hact
        obtain ⟨rfl, ho, hk⟩ := hact
        obtain rfl := eq_of_heq ho
        obtain rfl := eq_of_heq hk
        cases rest <;> simp [wBnext]
    all_goals
      simp only [Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact
      obtain rfl := eq_of_heq ho
      obtain rfl := eq_of_heq hk
    case wV v sn r => cases todoOf rnd r <;> simp [wBnext]
    all_goals simp <;> split <;> (try split) <;> simp
  | au a =>
    cases hl : C.loc (.au a) <;> simp only [alg1, auditorAct, hl, reduceCtorEq] at hact <;>
      simp only [Action.access.injEq] at hact <;> obtain ⟨rfl, ho, hk⟩ := hact <;>
      obtain rfl := eq_of_heq ho <;> obtain rfl := eq_of_heq hk
    case aR A' lsa' => simp [aNext_ne_aR]
    case aV A' r s => simp only [aVnext]; split_ifs <;> simp [aNext_ne_aR]
    case aB A' r s val j => simp only [aBnext]; split_ifs <;> simp [aNext_ne_aR]
    case aCAS A' r => simp

/-- **Lemma 2.** Algorithm 1 is wait-free. -/
theorem alg1_waitFree : (alg1 (W := W) (Au := Au) rnd v₀).WaitFree := by
  intro e p n hp
  have hInv : ∀ t, Inv rnd (e.cfg t) := fun t => Inv.of_run (e.run_pre t)
  -- classification of the label at time `s ≥ n`
  have hcls : ∀ s ≥ n, e.lbl s = .tau p ∨ (e.lbl s).proc ≠ p := by
    intro s hs
    cases h : e.lbl s with
    | tau q => by_cases hq : q = p
               · left; rw [hq]
               · right; simpa [Label.proc] using hq
    | inv q o =>
      right; intro hq; simp only [Label.proc] at hq; subst hq
      have := e.step_eq s; rw [h] at this
      exact hp s hs (Impl.step_inv this).1
    | ret q r =>
      right; intro hq; simp only [Label.proc] at hq; subst hq
      have := e.step_eq s; rw [h] at this
      have h2 := (Impl.step_ret this).2.1
      apply hp (s + 1) (by omega)
      rw [h2]; simp
  have hloc_other : ∀ s, (e.lbl s).proc ≠ p → (e.cfg (s + 1)).loc p = (e.cfg s).loc p := by
    intro s hs
    have hst := e.step_eq s
    have hp' : p ≠ (e.lbl s).proc := Ne.symm hs
    cases h : e.lbl s with
    | inv q o => rw [h] at hst hp'; obtain ⟨-, -, -, hl, -⟩ := Impl.step_inv hst
                 simp only [Label.proc] at hp'; simp [hl, Function.update_of_ne hp']
    | ret q r => rw [h] at hst hp'; obtain ⟨-, -, -, l, -, hl⟩ := Impl.step_ret hst
                 simp only [Label.proc] at hp'; simp [hl, Function.update_of_ne hp']
    | tau q => rw [h] at hst hp'; obtain ⟨-, -, i, o, k, -, -, hl⟩ := Impl.step_tau hst
               simp only [Label.proc] at hp'; simp [hl, Function.update_of_ne hp']
  by_cases hex : ∃ t ≥ n, e.lbl t = .tau p
  · obtain ⟨t, ht, hlt⟩ := hex
    have hnaR : ∀ s ≥ t + 1, ∀ A lsa, (e.cfg s).loc p ≠ .aR A lsa := by
      intro s hs
      induction s, hs using Nat.le_induction with
      | base =>
        have := e.step_eq t; rw [hlt] at this
        exact tau_not_aR this
      | succ s hs ih =>
        rcases hcls s (by omega) with h | h
        · have := e.step_eq s; rw [h] at this; exact tau_not_aR this
        · rw [hloc_other s h]; exact ih
    have hmono : ∀ s ≥ t + 1, pot rnd (e.cfg (s + 1)) p ≤ pot rnd (e.cfg s) p ∧
        (e.lbl s = .tau p → pot rnd (e.cfg (s + 1)) p < pot rnd (e.cfg s) p) := by
      intro s hs
      rcases hcls s (by omega) with h | h
      · have := e.step_eq s; rw [h] at this
        have := (pot_own (hInv s) this (hnaR s hs)).1
        exact ⟨this.le, fun _ => this⟩
      · refine ⟨pot_other (hInv s) (e.step_eq s) h, fun h' => ?_⟩
        rw [h'] at h; exact absurd rfl h
    obtain ⟨T, hT, hc⟩ := Nat.eventually_not_of_succ_le (f := fun s => pot rnd (e.cfg s) p)
      (N := t + 1) (fun s hs => (hmono s hs).1) (p := fun s => e.lbl s = .tau p)
      (fun s hs => (hmono s hs).2)
    exact ⟨T, hc⟩
  · push_neg at hex
    exact ⟨n, hex⟩

end

end Podc.AuditingWithoutLeaks
