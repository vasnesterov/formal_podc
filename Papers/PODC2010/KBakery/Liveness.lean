import Papers.PODC2010.KBakery.Progress

/-!
# Starvation freedom (Lemma 5 of the paper; Lemma 5.5 of the thesis)

*If a non-faulty process `p` is in the trying protocol and at most `k − 1` processes crash,
then `p` eventually enters the CS.* Proved for both variants.

Proof structure (following the paper): among the non-crashed processes that stay in the trying
protocol forever, take `m` with the smallest final `(ticket, id)`. Every other non-crashed process
`q` eventually keeps `Want[q][m]` "good" for `m` forever (`(Ticket[m], m) < (Want[q][m], q)`):
* a stuck `q` has a larger final pair;
* a `q` that takes finitely many steps rests in the NCS (`Want = ∞`);
* any other `q` leaves the trying protocol infinitely often and, after `m`'s ticket is fixed, its
  next passage chooses a ticket larger than `m`'s (`reach_good`).
Then the next full scan of `m` removes all non-crashed processes from its predecessor set, which
then has fewer than `k` elements, so `m` leaves the loop and enters the CS — a contradiction.
-/

set_option linter.unusedSectionVars false

namespace Podc.KBakery

open Finset

variable {P : Type} [LinearOrder P] [Fintype P]
variable {fife : Bool} {k : ℕ}

/-- `q`'s ticket and announcement are both larger than `(tm, m)`. -/
def Gd (s : Cfg P) (tm : ℕ) (m q : P) : Prop :=
  lexLt tm m (s.ticket q) q ∧ wantGood tm m (s.want q m) q

omit [Fintype P] in
lemma lexLt_mono {v w w' : ℕ} {r q : P} (h : lexLt v r w q) (hw : w ≤ w') : lexLt v r w' q := by
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl (by omega)
  · rcases hw.lt_or_eq with hw | hw
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, h'⟩

/-- A step changes `Want[q][m]` only to `Ticket[q]` or `∞`. -/
lemma want_step_cases {s : Cfg P} {p i q m : P} :
    (stepAt fife k s p i).want q m = s.want q m ∨ (stepAt fife k s p i).want q m = s.ticket q ∨
      (stepAt fife k s p i).want q m = ⊤ := by
  by_cases hq : q = p
  · subst hq
    rw [stepAt_want]
    rcases hpc : s.pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
      simp only [core, hpc] <;> (try split_ifs) <;> (try cases fife) <;>
      by_cases hmi : m = i <;> simp [Function.update_apply, hmi]
  · left; rw [stepAt_want, core_want_ne hq]

lemma gd_step {s : Cfg P} {p i : P} (hI : Inv k s) (ha : Admissible s p i) {tm : ℕ} {m q : P} (h : Gd s tm m q) :
    Gd (stepAt fife k s p i) tm m q := by
  refine ⟨lexLt_mono h.1 (ticket_mono hI ha q), ?_⟩
  rcases want_step_cases (fife := fife) (k := k) (s := s) (p := p) (i := i) (q := q) (m := m)
    with hw | hw | hw <;> rw [hw]
  · exact h.2
  · exact wantGood_coe.2 h.1
  · exact Or.inl (WithTop.coe_lt_top _)

/-- Domain of `reach_good`: `q` is on its way from the CS/exit/NCS to line 19, in a passage whose
ticket will be larger than `(tm, m)`. -/
def DomQ (s : Cfg P) (tm : ℕ) (m q : P) : Prop :=
  match s.pc q with
  | .cs | .ex _ | .ncs | .d14 _ => True
  | .d15 acc rem => tm ≤ acc ∨ m ∈ rem ∨ lexLt tm m (s.ticket q) q
  | .d16 _ => lexLt tm m (s.ticket q) q
  | _ => False

/-- Distance (in own steps) from the CS around the loop to line 19. -/
def cycMu (N : ℕ) : PC P → ℕ
  | .d16 rem => rem.card + 1
  | .d15 _ rem => rem.card + 1 + (N + 1)
  | .d14 rem => rem.card + 1 + (2 * N + 2)
  | .ncs => 3 * N + 4
  | .ex rem => rem.card + 1 + (3 * N + 4)
  | .cs => 4 * N + 6
  | _ => 0

lemma domQ_step {s : Cfg P} {q i m : P} {tm : ℕ} (hI : Inv k s) (ha : Admissible s q i)
    (hqm : q ≠ m) (htm : s.ticket m = tm) (hD : DomQ s tm m q) :
    Gd (stepAt fife k s q i) tm m q ∨
      (DomQ (stepAt fife k s q i) tm m q ∧
        cycMu (Fintype.card P) ((stepAt fife k s q i).pc q) < cycMu (Fintype.card P) (s.pc q)) := by
  have hc : ∀ s : Finset P, s.card ≤ Fintype.card P := fun s => card_le_univ s
  have he : (univ.erase q).card + 1 = Fintype.card P := by
    rw [card_erase_add_one (mem_univ q), card_univ]
  have hw := hI.wantC q m hqm
  unfold DomQ at hD ⊢
  unfold WantSpec at hw
  rcases hpc : s.pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp only [hpc] at hD hw <;>
    simp only [Gd, stepAt_pc, stepAt_ticket, stepAt_want, core, hpc] <;> (try split_ifs) <;>
    simp [cycMu, Function.update_apply] <;> first
    | (right; exact card_erase_lt_of_mem ‹_›)
    | (right; omega)
    | (right; exact ⟨hD, card_erase_lt_of_mem ‹_›⟩)
    | (right
       refine ⟨?_, card_erase_lt_of_mem ‹_›⟩
       rcases hD with hD | hD | hD
       · exact Or.inl (Or.inl hD)
       · by_cases hmi : m = i
         · subst hmi; exact Or.inl (Or.inr htm.ge)
         · exact Or.inr (Or.inl ⟨hmi, hD⟩)
       · exact Or.inr (Or.inr hD))
    | (have h0 := admissible_of_not_mem ha (by simpa [hpc, PC.rem] using ‹i ∉ _›)
       simp only [hpc, PC.rem] at h0
       subst h0
       simp at hD hw
       first
       | (right; omega)
       | (left; exact ⟨hD, by rw [hw]; exact wantGood_coe.2 hD⟩)
       | exact ⟨hD, by rw [hw]; exact wantGood_coe.2 hD⟩
       | (right
          refine ⟨?_, by omega⟩
          rcases hD with hD | hD
          · exact Or.inl (by omega)
          · exact lexLt_mono hD ((hI.g1 q acc' ∅ hpc (by simp)).trans (Nat.le_succ _))))

/-- Phase A of the loop argument: from lines 20–22 back to line 19. -/
def loopMuA (N : ℕ) : PC P → ℕ
  | .scan _ rem => rem.card + 1 + (N + 1)
  | .chk _ rem _ => rem.card + 1
  | _ => 0

/-- At line 19, line 23 or in the CS. -/
def PC.AtHead : PC P → Prop
  | .head _ _ | .cap23 _ | .cs => True
  | _ => False

lemma loopA_step {s : Cfg P} {m i : P} (h : (s.pc m).Settled) (h' : ¬(s.pc m).AtHead) :
    ((stepAt fife k s m i).pc m).AtHead ∨
      (((stepAt fife k s m i).pc m).Settled ∧
        loopMuA (Fintype.card P) ((stepAt fife k s m i).pc m) < loopMuA (Fintype.card P) (s.pc m)) := by
  rw [stepAt_pc]
  rcases hpc : s.pc m with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp [hpc, PC.Settled, PC.AtHead] at h h' <;>
    simp only [core, hpc] <;> (try split_ifs) <;> (try cases fife) <;>
    simp [PC.AtHead, PC.Settled, loopMuA] <;> exact card_erase_lt_of_mem ‹_›

/-- Phase B of the loop argument: `pred \ C` is covered by the current scan (`C` = crashed). -/
def DomB (s : Cfg P) (m : P) (C : Finset P) : Prop :=
  match s.pc m with
  | .head _ _ | .cap23 _ | .cs => True
  | .scan pred rem => pred \ C ⊆ rem
  | .chk pred _ _ => pred \ C = ∅
  | _ => False

/-- Measure of phase B. -/
def loopMuB (N k : ℕ) : PC P → ℕ
  | .head pred cap => if k ≤ pred.card ∧ cap = false then 3 * N + 5 else N + 2
  | .scan _ rem => rem.card + 1 + (N + 1) + (N + 2)
  | .chk _ rem _ => rem.card + 1 + (N + 2)
  | .cap23 rem => rem.card + 1
  | _ => 0

lemma loopB_step {s : Cfg P} {m i : P} {C : Finset P} (hI : Inv k s) (ha : Admissible s m i)
    (hC : C.card < k)
    (hgood : ∀ j, j ∉ C → j ≠ m → wantGood (s.ticket m) m (s.want j m) j)
    (hD : DomB s m C) (hcs : s.pc m ≠ .cs) :
    (stepAt fife k s m i).pc m = .cs ∨
      (DomB (stepAt fife k s m i) m C ∧
        loopMuB (Fintype.card P) k ((stepAt fife k s m i).pc m) <
          loopMuB (Fintype.card P) k (s.pc m)) := by
  have hc : ∀ s : Finset P, s.card ≤ Fintype.card P := fun s => card_le_univ s
  have hsmall : ∀ pred : Finset P, pred \ C = ∅ → pred.card < k := by
    intro pred h
    have : pred ⊆ C := by
      intro x hx; by_contra hxC
      have : x ∈ pred \ C := mem_sdiff.2 ⟨hx, hxC⟩
      rw [h] at this; simp at this
    exact (card_le_card this).trans_lt hC
  unfold DomB at hD ⊢
  rw [stepAt_pc]
  rcases hpc : s.pc m with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp only [hpc] at hD hcs <;>
    simp only [core, hpc] <;> (try split_ifs) <;> (try cases fife) <;>
    simp [loopMuB] <;> first
    | exact card_erase_lt_of_mem ‹_›
    | exact absurd rfl hcs
    | (have := hc pred; split_ifs <;> omega)
    | (have := hsmall pred (by simpa using hD); split_ifs <;> omega)
    | (refine ⟨?_, card_erase_lt_of_mem ‹_›⟩
       intro x hx
       rw [mem_union]
       by_cases hxC : x ∈ C
       · exact Or.inl hxC
       · right
         have hxp : x ∈ pred := by
           first | exact hx | exact (mem_erase.1 hx).2
         have hxr := hD (mem_sdiff.2 ⟨hxp, hxC⟩)
         refine mem_erase.2 ⟨?_, hxr⟩
         rintro rfl
         first
         | exact (mem_erase.1 hx).1 rfl
         | (have hxm : x ≠ m := fun h => hI.scanNot m pred rem' hpc (h ▸ hxr)
            exact ‹¬wantGood _ _ _ _› (hgood x hxC hxm)))
    | exact ⟨sdiff_eq_empty_iff_subset.1 hD, card_erase_lt_of_mem ‹_›⟩
    | (have h0 := admissible_of_not_mem ha (by simpa [hpc, PC.rem] using ‹i ∉ _›)
       simp only [hpc, PC.rem] at h0
       subst h0
       have hpc' : pred \ C = ∅ := by first | exact subset_empty.1 hD | exact hD
       have := hsmall pred hpc'
       first
       | exact sdiff_eq_empty_iff_subset.1 hpc'
       | exact ⟨sdiff_eq_empty_iff_subset.1 hpc', by omega⟩
       | (split_ifs <;> omega)
       | (simp [this.not_ge]))

namespace Run

variable (r : Run fife k P)

lemma gd_forever {tm : ℕ} {m q : P} {T : ℕ} (h : Gd (r.s T) tm m q) :
    ∀ t ≥ T, Gd (r.s t) tm m q := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact h
  | succ t ht ih => rw [r.step t]; exact gd_step (r.inv t) (r.adm t) ih

/-- After `m`'s ticket is fixed to `tm`, a process `q` that takes infinitely many steps and is
at some time `t₁ ≥ T₀` on its way from the CS to its next doorway eventually gets `Gd`. -/
lemma reach_good {tm : ℕ} {m q : P} {T₀ : ℕ} (htm : ∀ t ≥ T₀, (r.s t).ticket m = tm)
    (hqm : q ≠ m) (hinf : ∀ T, ∃ t ≥ T, r.sched t = q) {t₁ : ℕ} (h₁ : T₀ ≤ t₁)
    (hD : DomQ (r.s t₁) tm m q) : ∃ t ≥ t₁, Gd (r.s t) tm m q := by
  apply exists_good_of_measure r.sched q hinf (fun t => Gd (r.s t) tm m q)
    (fun t => DomQ (r.s t) tm m q) (fun t => cycMu (Fintype.card P) ((r.s t).pc q)) t₁ hD
  intro t ht hDt hG
  by_cases hs : r.sched t = q
  · have hadm := r.adm t
    rw [hs] at hadm
    rcases domQ_step (fife := fife) (k := k) (r.inv t) hadm hqm (htm t (by omega)) hDt with
      h | ⟨h1, h2⟩
    · exact absurd (by rw [r.step t, hs]; exact h) hG
    · rw [r.step t, hs]
      exact ⟨h1, h2.le, fun _ => h2⟩
  · have hpc := r.pc_succ_of_ne hs
    have htk := r.ticket_succ_of_ne hs
    refine ⟨?_, by rw [hpc], fun h => absurd h hs⟩
    unfold DomQ at hDt ⊢
    rw [hpc, htk]
    exact hDt

lemma want_eq_ticket_of_settled {s : Cfg P} (hI : Inv k s) {q m : P} (hqm : q ≠ m)
    (h : (s.pc q).Settled) : s.want q m = s.ticket q := by
  have hw := hI.wantC q m hqm
  unfold WantSpec at hw
  rcases hpc : s.pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp [hpc, PC.Settled] at h hw ⊢ <;> exact hw

/-- Every non-crashed `q ≠ m` eventually keeps `Want[q][m]` good for `(tm, m)` forever, provided
`m`'s ticket is `tm` from `T₀` on and `q`, if it gets stuck at lines 19–23, has a larger pair. -/
lemma eventually_want_good {tm : ℕ} {m q : P} {T₀ : ℕ} (htm : ∀ t ≥ T₀, (r.s t).ticket m = tm)
    (hq : ¬ r.Crashed q) (hqm : q ≠ m)
    (hstuck : ∀ T', (∀ t ≥ T', ((r.s t).pc q).Settled ∧ (r.s t).ticket q = (r.s T').ticket q) →
      lexLt tm m ((r.s T').ticket q) q) :
    ∃ Tq, ∀ t ≥ Tq, wantGood tm m ((r.s t).want q m) q := by
  by_cases hfin : ∃ T, ∀ t ≥ T, r.sched t ≠ q
  · -- finitely many steps: `q` rests in the NCS
    obtain ⟨T, hT⟩ := hfin
    have hc := r.pc_const_of_fin_sched hT
    have hncs : (r.s T).pc q = .ncs := by
      by_contra h
      exact hq ⟨T, fun t ht => ⟨hT t ht, by rw [(hc t ht).1]; exact h⟩⟩
    have hw := (r.inv T).wantC q m hqm
    unfold WantSpec at hw
    rw [hncs] at hw
    refine ⟨T, fun t ht => ?_⟩
    rw [(hc t ht).2, hw]
    exact Or.inl (WithTop.coe_lt_top _)
  push Not at hfin
  have hinf : ∀ T, ∃ t ≥ T, r.sched t = q := hfin
  by_cases hst : ∃ T, ∀ t ≥ T, ((r.s t).pc q).InTrying
  · -- stuck: `q` has a larger final pair
    obtain ⟨T, hT⟩ := hst
    obtain ⟨T', -, hS⟩ := r.settles hq hT
    have hl := hstuck T' hS
    refine ⟨T', fun t ht => ?_⟩
    obtain ⟨hs1, hs2⟩ := hS t ht
    rw [want_eq_ticket_of_settled (r.inv t) hqm hs1, hs2]
    exact wantGood_coe.2 hl
  · push Not at hst
    obtain ⟨t₁, ht₁, hnt⟩ := hst T₀
    have hD : DomQ (r.s t₁) tm m q := by
      unfold DomQ
      rcases hpc : (r.s t₁).pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ |
        ⟨pred, rem'⟩ | ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
        simp [hpc, PC.InTrying, PC.InDoorway, PC.InWaiting] at hnt ⊢
    obtain ⟨t, ht, hG⟩ := r.reach_good htm hqm hinf ht₁ hD
    exact ⟨t, fun t' ht' => (r.gd_forever hG t' ht').2⟩

end Run

lemma settled_inTrying {c : PC P} (h : c.Settled) : c.InTrying := by
  cases c <;> simp_all [PC.Settled, PC.InTrying, PC.InDoorway, PC.InWaiting]

lemma settled_ne_cs {c : PC P} (h : c.Settled) : c ≠ .cs := by
  rintro rfl; simp [PC.Settled] at h

open Classical in
/-- **Starvation freedom** (Lemma 5 / Lemma 5.5, and Lemma 5.5 for Figure 5.5 as claimed in the
thesis' Section 5.6.1). In every execution in which fewer than `k` processes crash, every
non-crashed process that is in the trying protocol eventually enters the CS. -/
theorem starvation_freedom (r : Run fife k P)
    (hcr : (univ.filter fun q => r.Crashed q).card < k)
    (p : P) (hp : ¬ r.Crashed p) (t₀ : ℕ) (htry : ((r.s t₀).pc p).InTrying) :
    ∃ t ≥ t₀, (r.s t).pc p = .cs := by
  by_contra H
  push Not at H
  set C := univ.filter fun q => r.Crashed q with hC
  set S := univ.filter fun q => ¬ r.Crashed q ∧ ∃ T, ∀ t ≥ T, ((r.s t).pc q).InTrying with hS
  have hpS : p ∈ S := by
    simp only [hS, mem_filter, mem_univ, true_and]
    exact ⟨hp, t₀, r.trying_forever htry H⟩
  have hsettle : ∀ q ∈ S, ∃ T', ∀ t ≥ T', ((r.s t).pc q).Settled ∧
      (r.s t).ticket q = (r.s T').ticket q := by
    intro q hq
    simp only [hS, mem_filter, mem_univ, true_and] at hq
    obtain ⟨T, hT⟩ := hq.2
    obtain ⟨T', -, h⟩ := r.settles hq.1 hT
    exact ⟨T', h⟩
  choose! Tq hTq using hsettle
  set ft : P → ℕ := fun q => (r.s (Tq q)).ticket q with hft
  obtain ⟨m, hmS, hmin⟩ := S.exists_min_image (fun q => toLex (ft q, q)) ⟨p, hpS⟩
  set T₀ := Tq m
  set tm := ft m
  have htm : ∀ t ≥ T₀, (r.s t).ticket m = tm := fun t ht => (hTq m hmS t ht).2
  have hmset : ∀ t ≥ T₀, ((r.s t).pc m).Settled := fun t ht => (hTq m hmS t ht).1
  have hmnc : ¬ r.Crashed m := by
    simp only [hS, mem_filter, mem_univ, true_and] at hmS; exact hmS.1
  -- every non-crashed `q ≠ m` eventually keeps `Want[q][m]` good
  have hev : ∀ q ∈ univ.filter (fun q => q ≠ m ∧ ¬ r.Crashed q),
      ∃ Tg, ∀ t ≥ Tg, wantGood tm m ((r.s t).want q m) q := by
    intro q hq
    simp only [mem_filter, mem_univ, true_and] at hq
    apply r.eventually_want_good htm hq.2 hq.1
    intro T' hT'
    have hqS : q ∈ S := by
      simp only [hS, mem_filter, mem_univ, true_and]
      exact ⟨hq.2, T', fun t ht => settled_inTrying (hT' t ht).1⟩
    have heq : (r.s T').ticket q = ft q := by
      have h1 := (hT' (max T' (Tq q)) (le_max_left _ _)).2
      have h2 := (hTq q hqS (max T' (Tq q)) (le_max_right _ _)).2
      rw [← h1, h2]
    rw [heq]
    have hle := hmin q hqS
    simp only [Prod.Lex.toLex_le_toLex] at hle
    rcases hle with hle | ⟨hle, hle'⟩
    · exact Or.inl hle
    · exact Or.inr ⟨hle, lt_of_le_of_ne hle' (Ne.symm hq.1)⟩
  choose! Tg hTg using hev
  set G := univ.filter (fun q => q ≠ m ∧ ¬ r.Crashed q)
  set Ts := max T₀ (G.sup Tg)
  have hgood : ∀ t ≥ Ts, ∀ j, j ∉ C → j ≠ m →
      wantGood ((r.s t).ticket m) m ((r.s t).want j m) j := by
    intro t ht j hjC hjm
    have hjG : j ∈ G := by
      simp only [G, mem_filter, mem_univ, true_and]
      exact ⟨hjm, by simpa [hC] using hjC⟩
    rw [htm t (le_trans (le_max_left _ _) ht)]
    exact hTg j hjG t (le_trans (le_trans (le_sup hjG) (le_max_right _ _)) ht)
  have hinf : ∀ T, ∃ t ≥ T, r.sched t = m :=
    r.inf_sched_of_not_crashed hmnc (T := T₀) fun t ht h => by
      have := hmset t ht; rw [h] at this; simp [PC.Settled] at this
  -- Phase A: `m` reaches line 19 (or line 23 / the CS)
  have hA : ∃ t ≥ Ts, ((r.s t).pc m).AtHead := by
    by_cases h0 : ((r.s Ts).pc m).AtHead
    · exact ⟨Ts, le_rfl, h0⟩
    apply exists_good_of_measure r.sched m hinf (fun t => ((r.s t).pc m).AtHead)
      (fun t => ((r.s t).pc m).Settled ∧ ¬ ((r.s t).pc m).AtHead)
      (fun t => loopMuA (Fintype.card P) ((r.s t).pc m)) Ts ⟨hmset Ts (le_max_left _ _), h0⟩
    intro t ht ⟨hDs, hDa⟩ hG
    by_cases hs : r.sched t = m
    · rcases loopA_step (fife := fife) (k := k) (i := r.choice t) hDs hDa with h | ⟨h1, h2⟩
      · exact absurd (by rw [r.step t, hs]; exact h) hG
      · have hst := r.step t
        rw [hs] at hst
        rw [hst] at hG ⊢
        exact ⟨⟨h1, hG⟩, h2.le, fun _ => h2⟩
    · rw [r.pc_succ_of_ne hs]
      exact ⟨⟨hDs, hDa⟩, le_rfl, fun h => absurd h hs⟩
  obtain ⟨tA, htA, hAt⟩ := hA
  -- Phase B: `m` empties its predecessor set of non-crashed processes and enters the CS
  obtain ⟨t, ht, hcs⟩ := exists_good_of_measure r.sched m hinf (fun t => (r.s t).pc m = .cs)
    (fun t => DomB (r.s t) m C)
    (fun t => loopMuB (Fintype.card P) k ((r.s t).pc m)) tA (by
      unfold DomB
      rcases hpc : (r.s tA).pc m with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ |
        ⟨pred, rem'⟩ | ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp [hpc, PC.AtHead] at hAt ⊢) (by
      intro t ht hD hG
      by_cases hs : r.sched t = m
      · have hadm := r.adm t
        rw [hs] at hadm
        have hTt : Ts ≤ t := le_trans htA ht
        rcases loopB_step (fife := fife) (r.inv t) hadm hcr (hgood t hTt) hD
            (settled_ne_cs (hmset t (le_trans (le_max_left _ _) hTt))) with h | ⟨h1, h2⟩
        · exact absurd (by rw [r.step t, hs]; exact h) hG
        · rw [r.step t, hs]
          exact ⟨h1, h2.le, fun _ => h2⟩
      · refine ⟨?_, by rw [r.pc_succ_of_ne hs], fun h => absurd h hs⟩
        unfold DomB at hD ⊢
        rw [r.pc_succ_of_ne hs]
        exact hD)
  exact settled_ne_cs (hmset t (le_trans (le_max_left _ _) (le_trans htA ht))) hcs

end Podc.KBakery
