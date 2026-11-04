import Papers.PODC2015.SafetyLivenessExclusion.Lemmas

/-!
# Theorem 4.9 for reactive implementations (repaired proof)

**Theorem 4.9** of Bushkov–Guerraoui (PODC 2015): if there is a strongest liveness property that
does not exclude `S`, it is `Lmax`.

We prove it for every class `𝓒` of *reactive* valid implementations (processes take steps only
while executing an operation) that contains the two trivial implementations of the paper's proof:
the silent implementation `I_t` (`silent`) and the one-shot responders `I_b` (`responder`).
By `Setting.isStrongestNonExcl_iff` it suffices to show that every history that is fair for all
implementations ensuring `S` lies in `Lmax` (`core_subset_Lmax`). The argument follows the paper:

1. `I_t` ensures `S` (all its histories are input-only, hence histories of any implementation),
   so a core history `h` has no response; it is finite and every process is pending or crashed
   at its end.
2. If every process crashed, `h` has no well-formed extension, so the assumption on `Lmax`
   puts `h` into `Lmax`. (The paper's proof misses this case.)
3. Otherwise some correct process `l₀` is pending on `inv l₀ x₀`. *Repair:* take a response `r₀`
   with `inv l₀ x₀ · res l₀ r₀ ∈ S` (the paper's assumption) and an implementation `I'` ensuring
   `S` with this history. The responder `I_b` (answers `r₀` to `l₀`'s first invocation `x₀`,
   nothing else) ensures `S`, because each of its histories is a history of `I'`: the other
   processes' invocations and crashes commute with `l₀`'s run in `I'` (frame lemma), *since
   reactive processes do not step while idle*. But `h` is not fair for `I_b`.

The paper instead derives `inv_l · res_l ∈ S` from `h · res_l ∈ S`, which is unjustified (for
consensus, `propose₂(1) · propose₁(0) · decide₁(1)` satisfies agreement and validity while
`propose₁(0) · decide₁(1)` does not), and uses commutation without reactivity; without it the
theorem is false (`Counterexample.lean`).
-/

namespace Podc.SafetyLivenessExclusion

open Hist

variable {n : ℕ} {Inv Res : Type}

namespace Impl

variable {I : Impl n Inv Res}

theorem IsHistOf.finHist {l : List (Ext n Inv Res)} (h : I.IsHistOf (.fin l)) : I.FinHist l := by
  rcases h with ⟨l', h1, h2⟩ | ⟨e, he⟩
  · cases h1; exact h2
  · obtain ⟨K, hK⟩ := he
    rw [← hK K le_rfl]; exact e.finHist_pre K

/-- Implementations without internal actions: every action of an infinite execution is
external, so its history is infinite. -/
theorem InfExec.not_hasHist_fin (hstep : ∀ i q b q' b', ¬ I.stepT i q b q' b')
    (hbase : ∀ b b', ¬ I.baseT b b') (e : I.InfExec) (l : List (Ext n Inv Res)) :
    ¬ e.HasHist (.fin l) := by
  have hlen : ∀ k, (hist (e.pre k)).length = k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have : e.pre (k + 1) = e.pre k ++ [e.act k] := by simp [InfExec.pre, List.range_succ]
      rw [this, hist_append, List.length_append, ih]
      have ht := e.trans k
      generalize e.cfg k = c at ht
      generalize e.cfg (k + 1) = c' at ht
      generalize e.act k = a at ht ⊢
      cases ht with
      | step _ h => exact absurd h (hstep _ _ _ _ _)
      | base h => exact absurd h (hbase _ _)
      | _ => rfl
  rintro ⟨K, hK⟩
  have h1 : hist (e.pre (K + l.length + 1)) = l := hK (K + l.length + 1) (by omega)
  have h2 := hlen (K + l.length + 1)
  rw [h1] at h2
  omega

theorem Trans.mem_eq {c c' : I.Cfg} {e : Ext n Inv Res} (h : I.Trans c (.ext e) c') :
    c'.mem = c.mem := by
  cases h <;> rfl

end Impl

/-! ## The silent implementation `I_t` -/

/-- The silent implementation `I_t` of the proof of Theorem 4.9: each process accepts one
invocation and never answers; no base objects. -/
abbrev silent : Impl n Inv Res where
  Q := Bool
  B := Unit
  initQ _ q := q = false
  initB _ := True
  invT _ q _ q' := q = false ∧ q' = true
  resT _ _ _ _ := False
  stepT _ _ _ _ _ := False
  baseT _ _ := False

theorem noRes_snoc {l : List (Ext n Inv Res)} (hl : ∀ e ∈ l, ¬ e.IsRes) {e : Ext n Inv Res}
    (he : ¬ e.IsRes) : ∀ e' ∈ l ++ hist [Act.ext e], ¬ e'.IsRes := by
  intro e' h'
  simp only [Impl.hist_single_ext, List.mem_append, List.mem_singleton] at h'
  rcases h' with h' | rfl
  · exact hl e' h'
  · exact he

/-- Local state of `I_t` encoding a status. -/
def silentLoc : PStat → Option Bool
  | .idle => some false
  | .pend => some true
  | .dead => none

theorem silent_inv {c : (silent : Impl n Inv Res).Cfg} {l : List (Ext n Inv Res)}
    (hc : (silent : Impl n Inv Res).Reach c l) :
    (∀ e ∈ l, ¬ e.IsRes) ∧ ∃ σ, runStat l = some σ ∧ ∀ i, c.loc i = silentLoc (σ i) := by
  refine Impl.Reach.induct (P := fun c l => (∀ e ∈ l, ¬ e.IsRes) ∧
    ∃ σ, runStat l = some σ ∧ ∀ i, c.loc i = silentLoc (σ i)) ?_ ?_ hc
  · intro c hc
    refine ⟨by simp, _, rfl, fun i => ?_⟩
    obtain ⟨q, hq, hq'⟩ := hc.1 i
    rw [hq, hq']; rfl
  · rintro c l a c' - ⟨hres, σ, hσ, hloc⟩ ht
    cases ht with
    | @inv i x q q' hq ht =>
      obtain ⟨rfl, rfl⟩ := ht
      have hi : σ i = .idle := by
        have := hloc i; rw [hq] at this
        cases h : σ i <;> rw [h] at this <;> first | rfl | cases this
      refine ⟨noRes_snoc hres (by simp [Ext.IsRes]), Function.update σ i .pend, ?_, fun j => ?_⟩
      · simp [runStat_append, hσ, stepStat, hi]
      · by_cases hj : j = i
        · subst hj; simp only [Function.update_self]; rfl
        · simp only [Function.update_of_ne hj]; exact hloc j
    | res _ ht => exact absurd ht id
    | @crash i q hq =>
      have hi : σ i ≠ .dead := by
        intro h; have := hloc i; rw [hq, h] at this; cases this
      refine ⟨noRes_snoc hres (by simp [Ext.IsRes]), Function.update σ i .dead, ?_, fun j => ?_⟩
      · simp [runStat_append, hσ, stepStat, hi]
      · by_cases hj : j = i
        · subst hj; simp only [Function.update_self]; rfl
        · simp only [Function.update_of_ne hj]; exact hloc j
    | step _ ht => exact absurd ht id
    | base ht => exact absurd ht id

theorem silent_valid [Nonempty Inv] : (silent : Impl n Inv Res).Valid := by
  refine ⟨⟨⟨fun _ => some false, ()⟩, fun i => ⟨false, rfl, rfl⟩, trivial⟩, ?_, ?_⟩
  · rintro l ⟨c, hc⟩
    obtain ⟨-, σ, hσ, -⟩ := silent_inv hc
    simp [WF, hσ]
  · intro c l hc σ hσ i hi x
    obtain ⟨-, σ', hσ', hloc⟩ := silent_inv hc
    rw [hσ] at hσ'; cases hσ'
    have := hloc i
    rw [hi] at this
    exact ⟨_, .inv this ⟨rfl, rfl⟩⟩

theorem silent_reactive : (silent : Impl n Inv Res).Reactive := by
  rintro c l - σ - i - ⟨c', ht⟩
  cases ht with
  | step _ h => exact h

/-- `I_t` has no infinite execution. -/
theorem silent_no_infExec (e : (silent : Impl n Inv Res).InfExec) : False := by
  let w : Option Bool → ℕ := fun o => match o with
    | some false => 2
    | some true => 1
    | none => 0
  let pot : (silent : Impl n Inv Res).Cfg → ℕ := fun c => ∑ i, w (c.loc i)
  have hdec : ∀ k, pot (e.cfg (k + 1)) < pot (e.cfg k) := by
    intro k
    have ht := e.trans k
    generalize e.cfg k = c at ht
    generalize e.cfg (k + 1) = c' at ht
    generalize e.act k = a at ht
    cases ht with
    | @inv i x q q' hq ht =>
      obtain ⟨rfl, rfl⟩ := ht
      apply Finset.sum_lt_sum
      · intro j _
        by_cases hj : j = i
        · subst hj; simp [hq, w]
        · simp [Function.update_of_ne hj]
      · exact ⟨i, Finset.mem_univ _, by simp [hq, w]⟩
    | res _ ht => exact absurd ht id
    | @crash i q hq =>
      apply Finset.sum_lt_sum
      · intro j _
        by_cases hj : j = i
        · subst hj; simp [w]
        · simp [Function.update_of_ne hj]
      · refine ⟨i, Finset.mem_univ _, ?_⟩
        cases q <;> simp [hq, w]
    | step _ ht => exact absurd ht id
    | base ht => exact absurd ht id
  have : ∀ k, pot (e.cfg k) + k ≤ pot (e.cfg 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => have := hdec k; omega
  have := this (pot (e.cfg 0) + 1)
  omega

/-! ## The responders `I_b` -/

/-- Local states of the responder. -/
inductive RState where
  | fresh
  | ready
  | done
  | stuck
  deriving DecidableEq

/-- The responder `I_b` of the proof of Theorem 4.9: process `l₀` answers `r₀` to its first
invocation if it is `x₀`; every other invocation is never answered; no base objects. -/
abbrev responder (l₀ : Fin n) (x₀ : Inv) (r₀ : Res) : Impl n Inv Res where
  Q := RState
  B := Unit
  initQ _ q := q = .fresh
  initB _ := True
  invT i q y q' := (q = .fresh ∨ q = .done) ∧
    ((i = l₀ ∧ y = x₀ ∧ q = .fresh ∧ q' = .ready) ∨ (¬ (i = l₀ ∧ y = x₀ ∧ q = .fresh) ∧ q' = .stuck))
  resT i q r q' := i = l₀ ∧ q = .ready ∧ r = r₀ ∧ q' = .done
  stepT _ _ _ _ _ := False
  baseT _ _ := False

section Responder

variable (l₀ : Fin n) (x₀ : Inv) (r₀ : Res)

/-- Local states of `I_b` encoding a status. -/
def RState.Fits : Option RState → PStat → Prop
  | none, s => s = .dead
  | some RState.fresh, s => s = .idle
  | some RState.done, s => s = .idle
  | some RState.ready, s => s = .pend
  | some RState.stuck, s => s = .pend

theorem responder_inv {c : (responder l₀ x₀ r₀).Cfg} {l : List (Ext n Inv Res)}
    (hc : (responder l₀ x₀ r₀).Reach c l) :
    (∃ σ, runStat l = some σ ∧ ∀ i, RState.Fits (c.loc i) (σ i)) ∧
      (proj l l₀ = [] → c.loc l₀ = some RState.fresh) ∧
      (proj l l₀ = [.inv l₀ x₀] → c.loc l₀ = some RState.ready) := by
  refine Impl.Reach.induct (P := fun c l =>
    (∃ σ, runStat l = some σ ∧ ∀ i, RState.Fits (c.loc i) (σ i)) ∧
      (proj l l₀ = [] → c.loc l₀ = some RState.fresh) ∧
      (proj l l₀ = [.inv l₀ x₀] → c.loc l₀ = some RState.ready))
    ?_ ?_ hc
  · intro c hc
    have hl : ∀ i, c.loc i = some RState.fresh := by
      intro i; obtain ⟨q, hq, hq'⟩ := hc.1 i; rw [hq, hq']
    exact ⟨⟨_, rfl, fun i => by rw [hl i]; rfl⟩, fun _ => hl l₀, by simp⟩
  · rintro c l a c' - ⟨⟨σ, hσ, hfit⟩, hfresh, hready⟩ ht
    cases ht with
    | @inv i y q q' hq ht =>
      obtain ⟨hq0, ht⟩ := ht
      have hi : σ i = .idle := by
        have := hfit i; rw [hq] at this
        rcases hq0 with rfl | rfl <;> exact this
      simp only [Impl.hist_single_ext]
      refine ⟨⟨Function.update σ i .pend, by simp [runStat_append, hσ, stepStat, hi],
        fun j => ?_⟩, ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj
          rcases ht with ⟨-, -, -, rfl⟩ | ⟨-, rfl⟩ <;> simp [RState.Fits]
        · simpa [Function.update_of_ne hj] using hfit j
      · intro hf
        by_cases hil : i = l₀
        · subst hil; rw [proj_snoc_of_eq (e := Ext.inv i y) (i := i) _ rfl] at hf; simp at hf
        · rw [proj_snoc_of_ne (e := Ext.inv i y) _ hil] at hf
          simpa [Function.update_of_ne (Ne.symm hil)] using hfresh hf
      · intro hf
        by_cases hil : i = l₀
        · subst hil
          rw [proj_snoc_of_eq (e := Ext.inv i y) (i := i) _ rfl] at hf
          obtain ⟨h1, h2⟩ := List.append_eq_singleton_iff.1 hf |>.resolve_right (by simp)
          have hf0 := hfresh h1
          rw [hq] at hf0; cases hf0
          simp only [List.singleton_inj, Ext.inv.injEq, true_and] at h2
          subst h2
          rcases ht with ⟨-, -, -, rfl⟩ | ⟨hne, -⟩
          · simp
          · exact absurd ⟨rfl, rfl, rfl⟩ hne
        · rw [proj_snoc_of_ne (e := Ext.inv i y) _ hil] at hf
          simpa [Function.update_of_ne (Ne.symm hil)] using hready hf
    | @res i r q q' hq ht =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
      have hi : σ i = .pend := by have := hfit i; rw [hq] at this; exact this
      simp only [Impl.hist_single_ext]
      refine ⟨⟨Function.update σ i .idle, by simp [runStat_append, hσ, stepStat, hi],
        fun j => ?_⟩, ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; simp [RState.Fits]
        · simpa [Function.update_of_ne hj] using hfit j
      · intro hf; rw [proj_snoc_of_eq (e := Ext.res i r) (i := i) _ rfl] at hf; simp at hf
      · intro hf
        rw [proj_snoc_of_eq (e := Ext.res i r) (i := i) _ rfl] at hf
        obtain ⟨-, h2⟩ := List.append_eq_singleton_iff.1 hf |>.resolve_right (by simp)
        simp at h2
    | @crash i q hq =>
      have hi : σ i ≠ .dead := by
        have := hfit i; rw [hq] at this
        cases q <;> simp_all [RState.Fits]
      simp only [Impl.hist_single_ext]
      refine ⟨⟨Function.update σ i .dead, by simp [runStat_append, hσ, stepStat, hi],
        fun j => ?_⟩, ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; simp [RState.Fits]
        · simpa [Function.update_of_ne hj] using hfit j
      · intro hf
        by_cases hil : i = l₀
        · subst hil; rw [proj_snoc_of_eq (e := Ext.crash i) (i := i) _ rfl] at hf; simp at hf
        · rw [proj_snoc_of_ne (e := Ext.crash i) _ hil] at hf
          simpa [Function.update_of_ne (Ne.symm hil)] using hfresh hf
      · intro hf
        by_cases hil : i = l₀
        · subst hil
          rw [proj_snoc_of_eq (e := Ext.crash i) (i := i) _ rfl] at hf
          obtain ⟨-, h2⟩ := List.append_eq_singleton_iff.1 hf |>.resolve_right (by simp)
          simp at h2
        · rw [proj_snoc_of_ne (e := Ext.crash i) _ hil] at hf
          simpa [Function.update_of_ne (Ne.symm hil)] using hready hf
    | step _ ht => exact absurd ht id
    | base ht => exact absurd ht id

theorem responder_valid : (responder l₀ x₀ r₀).Valid := by
  refine ⟨⟨⟨fun _ => some RState.fresh, ()⟩, fun i => ⟨.fresh, rfl, rfl⟩, trivial⟩, ?_, ?_⟩
  · rintro l ⟨c, hc⟩
    obtain ⟨⟨σ, hσ, -⟩, -⟩ := responder_inv l₀ x₀ r₀ hc
    simp [WF, hσ]
  · intro c l hc σ hσ i hi x
    obtain ⟨⟨σ', hσ', hfit⟩, -⟩ := responder_inv l₀ x₀ r₀ hc
    rw [hσ] at hσ'; cases hσ'
    have h := hfit i
    rw [hi] at h
    have hq : ∃ q, c.loc i = some q ∧ (q = RState.fresh ∨ q = RState.done) := by
      rcases hc' : c.loc i with _ | q
      · rw [hc'] at h; cases h
      · rw [hc'] at h
        cases q
        · exact ⟨_, rfl, Or.inl rfl⟩
        · cases h
        · exact ⟨_, rfl, Or.inr rfl⟩
        · cases h
    obtain ⟨q, hq, hq'⟩ := hq
    by_cases hc3 : i = l₀ ∧ x = x₀ ∧ q = .fresh
    · exact ⟨_, .inv (q' := RState.ready) hq ⟨hq', Or.inl ⟨hc3.1, hc3.2.1, hc3.2.2, rfl⟩⟩⟩
    · exact ⟨_, .inv (q' := RState.stuck) hq ⟨hq', Or.inr ⟨hc3, rfl⟩⟩⟩

theorem responder_reactive : (responder l₀ x₀ r₀).Reactive := by
  rintro c l - σ - i - ⟨c', ht⟩
  cases ht with
  | step _ h => exact h

/-- The histories of the responder are histories of any reactive valid implementation `I'`
that has `inv l₀ x₀ · res l₀ r₀` as a history (frame argument). -/
theorem responder_finHist_sub {I' : Impl n Inv Res} (hV : I'.Valid) (hR : I'.Reactive)
    (hE : I'.FinHist [.inv l₀ x₀, .res l₀ r₀]) {g : List (Ext n Inv Res)}
    (hg : (responder l₀ x₀ r₀).FinHist g) : I'.FinHist g := by
  -- decompose the execution of `I'`
  obtain ⟨cE, c₀, as, hi, hr, hh⟩ := hE
  obtain ⟨α, rest, rfl, hα, hrest⟩ := Impl.hist_eq_cons hh
  obtain ⟨β, γ, rfl, hβ, -⟩ := Impl.hist_eq_cons hrest
  obtain ⟨cA, hrA, hr2⟩ := Impl.Run.of_append hr
  cases hr2 with
  | @cons _ cA' _ _ _ htA hr3 =>
  obtain ⟨cB, hrB, hr4⟩ := Impl.Run.of_append hr3
  cases hr4 with
  | @cons _ cC _ _ _ htB _ =>
  have hreachA : I'.Reach cA [] := ⟨c₀, α, hi, hrA, hα⟩
  have hreachA' : I'.Reach cA' [.inv l₀ x₀] := by simpa using hreachA.trans htA
  have hβonly : ∀ a ∈ β, a.Only l₀ := by
    obtain ⟨σ, hσ⟩ : ∃ σ, runStat [Ext.inv (Res := Res) l₀ x₀] = some σ :=
      WF.exists (hV.2.1 _ ⟨_, hreachA'⟩)
    refine hreachA'.only_of_reactive hR hσ (fun j hj => ?_) hrB hβ
    have : runStat [Ext.inv (Res := Res) l₀ x₀] =
        some (Function.update (fun _ => PStat.idle) l₀ .pend) := by
      simp [runStat, stepStat]
    rw [this] at hσ; cases hσ
    simp [Function.update_of_ne hj]
  have hinvRun : I'.Run cA (.ext (.inv l₀ x₀) :: β) cB := .cons htA hrB
  have honly : ∀ a ∈ (Act.ext (.inv l₀ x₀) :: β : List (Act n Inv Res)), a.Only l₀ := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · simp [Act.Only, Ext.proc]
    · exact hβonly a ha
  -- the simulation
  obtain ⟨cb, hcb⟩ := hg
  suffices H : ∃ c', I'.Reach c' g ∧
      ((cb.loc l₀ = some RState.fresh → c'.loc l₀ = cA.loc l₀ ∧ c'.mem = cA.mem) ∧
        (cb.loc l₀ = some RState.ready → c'.loc l₀ = cB.loc l₀ ∧ c'.mem = cB.mem)) by
    obtain ⟨c', hc', -⟩ := H
    exact ⟨c', hc'⟩
  refine Impl.Reach.induct (P := fun cb g => ∃ c', I'.Reach c' g ∧
      ((cb.loc l₀ = some RState.fresh → c'.loc l₀ = cA.loc l₀ ∧ c'.mem = cA.mem) ∧
        (cb.loc l₀ = some RState.ready → c'.loc l₀ = cB.loc l₀ ∧ c'.mem = cB.mem))) ?_ ?_ hcb
  · intro c hc
    have h0 : c.loc l₀ = some RState.fresh := by
      obtain ⟨q, hq, hq'⟩ := hc.1 l₀; rw [hq, hq']
    exact ⟨cA, hreachA, fun _ => ⟨rfl, rfl⟩, fun h => by rw [h0] at h; cases h⟩
  · rintro cb g a cb' hreach ⟨c', hc', hfr, hrd⟩ ht
    obtain ⟨⟨σ, hσ, hfit⟩, -⟩ := responder_inv l₀ x₀ r₀ hreach
    -- generic input step in `I'`
    have input : ∀ e : Ext n Inv Res, ¬ e.IsRes → WF (g ++ [e]) → a = .ext e →
        (cb'.loc l₀ = cb.loc l₀ ∨ (cb'.loc l₀ ≠ some RState.fresh ∧ cb'.loc l₀ ≠ some RState.ready)) →
        e.proc ≠ l₀ ∨ (cb'.loc l₀ ≠ some RState.fresh ∧ cb'.loc l₀ ≠ some RState.ready) →
        ∃ c'', I'.Reach c'' (g ++ hist [a]) ∧
          ((cb'.loc l₀ = some RState.fresh → c''.loc l₀ = cA.loc l₀ ∧ c''.mem = cA.mem) ∧
            (cb'.loc l₀ = some RState.ready → c''.loc l₀ = cB.loc l₀ ∧ c''.mem = cB.mem)) := by
      intro e he hwf rfl hloc hcase
      obtain ⟨c'', ht''⟩ := hc'.input hV.2.2 he hwf
      refine ⟨c'', hc'.trans ht'', ?_⟩
      rcases hcase with hne | hgone
      · have hl : c''.loc l₀ = c'.loc l₀ := ht''.loc_eq (by simpa [Act.IsProc] using hne)
        have hm : c''.mem = c'.mem := Impl.Trans.mem_eq ht''
        rcases hloc with hloc | hgone
        · rw [hloc, hl, hm]; exact ⟨hfr, hrd⟩
        · exact ⟨fun h => absurd h hgone.1, fun h => absurd h hgone.2⟩
      · exact ⟨fun h => absurd h hgone.1, fun h => absurd h hgone.2⟩
    cases ht with
    | @inv i y q q' hq ht =>
      obtain ⟨hq0, ht⟩ := ht
      have hi : σ i = .idle := by
        have := hfit i; rw [hq] at this; rcases hq0 with rfl | rfl <;> exact this
      have hwf : WF (g ++ [Ext.inv i y]) := by
        simp [WF, runStat_append, hσ, stepStat, hi]
      rcases ht with ⟨rfl, rfl, rfl, rfl⟩ | ⟨hne, rfl⟩
      · -- `l₀`'s first invocation `x₀`: replay `inv l₀ x₀ · β` in `I'`
        obtain ⟨hl, hm⟩ := hfr hq
        obtain ⟨d, hd, hdl, hdm, -⟩ := hinvRun.frame honly hl hm
        refine ⟨d, by simpa [hβ] using hc'.run hd, ?_, ?_⟩
        · intro h; simp at h
        · intro _; exact ⟨hdl, hdm⟩
      · by_cases hil : i = l₀
        · subst hil
          exact input _ (by simp [Ext.IsRes]) hwf rfl (Or.inr (by simp)) (Or.inr (by simp))
        · exact input _ (by simp [Ext.IsRes]) hwf rfl
            (Or.inl (by simp [Function.update_of_ne (Ne.symm hil)]))
            (Or.inl (by simpa [Ext.proc] using hil))
    | @res i r q q' hq ht =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
      obtain ⟨hl, hm⟩ := hrd hq
      obtain ⟨d, hd, -, -, -⟩ := (Impl.Run.single htB).frame
        (by simp [Act.Only, Ext.proc]) hl hm
      refine ⟨d, by simpa using hc'.run hd, ?_, ?_⟩ <;> intro h <;> simp at h
    | @crash i q hq =>
      have hi : σ i ≠ .dead := by
        have := hfit i; rw [hq] at this
        cases q <;> simp_all [RState.Fits]
      have hwf : WF (g ++ [Ext.crash (Inv := Inv) (Res := Res) i]) := by
        simp [WF, runStat_append, hσ, stepStat, hi]
      by_cases hil : i = l₀
      · subst hil
        exact input _ (by simp [Ext.IsRes]) hwf rfl (Or.inr (by simp)) (Or.inr (by simp))
      · exact input _ (by simp [Ext.IsRes]) hwf rfl
          (Or.inl (by simp [Function.update_of_ne (Ne.symm hil)]))
          (Or.inl (by simpa [Ext.proc] using hil))
    | step _ ht => exact absurd ht id
    | base ht => exact absurd ht id

end Responder

/-! ## The core lies in `Lmax` -/

/-- A history in which every process crashed has no proper well-formed extension. -/
theorem eq_fin_of_all_dead {l : List (Ext n Inv Res)} {σ : Fin n → PStat}
    (hσ : runStat l = some σ) (hd : ∀ i, σ i = .dead) {h : Hist (Ext n Inv Res)}
    (hpre : FinPrefix l h) (hU : h ∈ U) : h = .fin l := by
  have key : ∀ e : Ext n Inv Res, ¬ WF (l ++ [e]) := by
    intro e hwf
    obtain ⟨σ', hσ'⟩ := hwf.exists
    obtain ⟨σ₀, h₀, he⟩ := runStat_append_eq_some.1 hσ'
    rw [hσ] at h₀; cases h₀
    rw [stepStat_dead (hd _)] at he; cases he
  cases h with
  | fin m =>
    obtain ⟨t, rfl⟩ := hpre
    cases t with
    | nil => simp
    | cons e t =>
      exfalso
      apply key e
      exact fin_mem_U.1 (safe_prefixClosed _ _ hU _ (by simp [FinPrefix]))
  | inf f =>
    exfalso
    have hl := finPrefix_inf_iff.1 hpre
    apply key (f l.length)
    have : l ++ [f l.length] = pfx f (l.length + 1) := by
      rw [pfx_succ, ← hl]
    rw [this]
    exact fin_mem_U.1 (safe_prefixClosed _ _ hU _ (finPrefix_pfx f _))

/-- The core of `Theorem 4.9`: in a class of reactive valid implementations containing `I_t` and
the responders, every history that is fair for all implementations ensuring `S` lies in `Lmax`. -/
theorem core_subset_Lmax [Nonempty Inv] (𝓒 : Set (Impl n Inv Res))
    (h𝓒 : ∀ I ∈ 𝓒, I.Valid ∧ I.Reactive) (hsil : silent ∈ 𝓒)
    (hresp : ∀ l x r, responder l x r ∈ 𝓒) {S Lmax : Set (Hist (Ext n Inv Res))}
    (hseq : ∀ i x, ∃ r, Hist.fin [Ext.inv i x, Ext.res i r] ∈ S)
    (himpl : ∀ i x r, Hist.fin [Ext.inv i x, Ext.res i r] ∈ S →
      ∃ I ∈ 𝓒, I.EnsuresS S ∧ I.FinHist [Ext.inv i x, Ext.res i r])
    (hL : LmaxAssumptions Lmax) (hex : ∃ I, (setting 𝓒 S Lmax).ensS I) :
    (setting 𝓒 S Lmax).core ⊆ Lmax := by
  intro h hh
  obtain ⟨I₀, hI₀, hI₀S⟩ := hex
  -- Step 1: `I_t` ensures `S`, so `h` is a fair history of `I_t`.
  have hsilS : (silent : Impl n Inv Res).EnsuresS S := by
    rintro l ⟨c, hc⟩
    obtain ⟨hres, σ, hσ, -⟩ := silent_inv hc
    exact hI₀S l ((h𝓒 I₀ hI₀).1.finHist_of_noRes hres (by simp [WF, hσ]))
  rcases hh silent ⟨hsil, hsilS⟩ with ⟨c, l, hc, hfair, rfl⟩ | ⟨e, -, -⟩
  swap
  · exact (silent_no_infExec e).elim
  obtain ⟨hres, σ, hσ, hloc⟩ := silent_inv hc
  -- every process is pending or crashed
  have hnidle : ∀ i, σ i ≠ .idle := by
    intro i hi
    have := hloc i
    rw [hi] at this
    obtain ⟨x⟩ := ‹Nonempty Inv›
    have := hfair _ _ (.inv (x := x) this ⟨rfl, rfl⟩)
    exact this
  by_cases hpend : ∃ l₀, σ l₀ = .pend
  · -- Step 3: the responder
    exfalso
    obtain ⟨l₀, hl₀⟩ := hpend
    obtain ⟨x₀, hx₀⟩ := (noRes_proj hres hσ l₀).2 hl₀
    obtain ⟨r₀, hr₀⟩ := hseq l₀ x₀
    obtain ⟨I', hI', hI'S, hE⟩ := himpl l₀ x₀ r₀ hr₀
    have hbS : (responder l₀ x₀ r₀).EnsuresS S := fun g hg =>
      hI'S g (responder_finHist_sub l₀ x₀ r₀ (h𝓒 I' hI').1 (h𝓒 I' hI').2 hE hg)
    rcases hh _ ⟨hresp l₀ x₀ r₀, hbS⟩ with ⟨cb, l', hcb, hfb, heq⟩ | ⟨e, -, he⟩
    · cases heq
      have hready := (responder_inv l₀ x₀ r₀ hcb).2.2 hx₀
      have := hfb _ _ (.res (r := r₀) hready ⟨rfl, rfl, rfl, rfl⟩)
      exact this
    · exact Impl.InfExec.not_hasHist_fin (fun _ _ _ _ _ h => h) (fun _ _ h => h) e l he
  · -- Step 2: every process crashed
    push Not at hpend
    have hd : ∀ i, σ i = .dead := by
      intro i; have h1 := hnidle i; have h2 := hpend i
      cases h : σ i <;> simp_all
    obtain ⟨h', hh', hpre⟩ := hL.ext l (by simp [WF, hσ])
    rwa [← eq_fin_of_all_dead hσ hd hpre (hL.subset_U hh')]

/-- **Theorem 4.9** (repaired), for any class `𝓒` of reactive valid implementations that contains
the trivial implementations `I_t` and `I_b` of the paper's proof (e.g. the reactive
implementations from read/write registers, or all reactive implementations): if a strongest
liveness property not excluding `S` exists, it is `Lmax`. Assumes a non-empty set of
invocations. -/
theorem theorem_4_9 [Nonempty Inv] (𝓒 : Set (Impl n Inv Res))
    (h𝓒 : ∀ I ∈ 𝓒, I.Valid ∧ I.Reactive) (hsil : silent ∈ 𝓒)
    (hresp : ∀ l x r, responder l x r ∈ 𝓒) {S Lmax : Set (Hist (Ext n Inv Res))}
    (hS : SafetyAssumptions 𝓒 S) (hL : LmaxAssumptions Lmax) (L : Set (Hist (Ext n Inv Res)))
    (hLs : (setting 𝓒 S Lmax).IsStrongestNonExcl L) : L = Lmax := by
  apply Setting.eq_Lmax_of_core_subset _ _ hLs
  apply core_subset_Lmax 𝓒 h𝓒 hsil hresp hS.seq _ hL
  · obtain ⟨I, hI, -⟩ := not_not.1 hLs.2.1
    exact ⟨I, hI⟩
  · intro i x r hr
    obtain ⟨I, hI, hIS, hIh⟩ := hS.impl _ hr
    exact ⟨I, hI, hIS, Impl.IsHistOf.finHist hIh⟩

/-- **Theorem 4.9** for the class of all reactive valid implementations. -/
theorem theorem_4_9_reactive [Nonempty Inv] {S Lmax : Set (Hist (Ext n Inv Res))}
    (hS : SafetyAssumptions {I | I.Valid ∧ I.Reactive} S) (hL : LmaxAssumptions Lmax)
    (L : Set (Hist (Ext n Inv Res)))
    (hLs : (setting {I | I.Valid ∧ I.Reactive} S Lmax).IsStrongestNonExcl L) : L = Lmax :=
  theorem_4_9 _ (fun _ h => h) ⟨silent_valid, silent_reactive⟩
    (fun l x r => ⟨responder_valid l x r, responder_reactive l x r⟩) hS hL L hLs

/-- **Corollaries 4.10–4.11** (scheme, reactive class): if `Lmax` excludes `S` (e.g.
wait-freedom and consensus from registers [5], local progress and opacity [4], taken as
hypotheses), there is no strongest liveness property that does not exclude `S`. -/
theorem corollary_4_10 [Nonempty Inv] (𝓒 : Set (Impl n Inv Res))
    (h𝓒 : ∀ I ∈ 𝓒, I.Valid ∧ I.Reactive) (hsil : silent ∈ 𝓒)
    (hresp : ∀ l x r, responder l x r ∈ 𝓒) {S Lmax : Set (Hist (Ext n Inv Res))}
    (hS : SafetyAssumptions 𝓒 S) (hL : LmaxAssumptions Lmax)
    (hmax : (setting 𝓒 S Lmax).Excludes Lmax) :
    ¬ ∃ L, (setting 𝓒 S Lmax).IsStrongestNonExcl L :=
  Setting.no_strongest_of_excludes_Lmax _ (theorem_4_9 𝓒 h𝓒 hsil hresp hS hL) hmax

end Podc.SafetyLivenessExclusion
