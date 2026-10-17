import Papers.PODC2026.ConsistentRefereeing.LongLivedLemmas

/-!
# No wait-free strongly linearizable long-lived contest (Theorems 25 and 30 of [ACE26])

The final arguments of Sections 5.1 and 5.2 of [ACE26], treated uniformly (`LLCtx.main`), and
the two theorems:

* `theorem25` — no wait-free strongly linearizable long-lived contest implementation from
  read/write registers (every primitive is read-only or a blind write), `n ≥ 3`;
* `theorem30` — none from `w`-window registers and test&set objects (every base object is
  window-like with window `w` or test&set-like), `n ≥ 4`, `3w ≤ n`.

Both assume wait-freedom and strong linearizability only on admissible executions (`LLAdm`);
`theorem25'`, `theorem30'` use the unrestricted notions. `register_rw`, `windowObj_hyp30`,
`tasObj_hyp30`: the standard objects satisfy the hypotheses.

## Map of Section 5

Definition 15: `LLCtx.W`, `LLCtx.Closed`; Proposition 16: `W_eq_of_dec`, `W_ext_subset`,
`Closed.ext`, `exists_super_ext1`, `not_decIn_of_super`, `super_of_not_invoked`; Lemma 17:
`lemma17`; Definition 18: `Helping`; Lemma 19: `lemma19`; Lemma 20: `lemma20`; Lemmas 21/27:
`lemma27` (`lemma21`); Lemmas 22/28: `lemma28` (`lemma22`); Lemma 23: the first cases of `main`;
Lemmas 24/29: `lemma24_1`, `lemma24_2`; the case analyses of Lemmas 20/27/28: `pair`,
`window_final`; Theorems 25/30: `main`.

Structure of `LLCtx.main` (after Lemmas 19, 27, 28, 24(1)): `α` helping with `W(α) = ∅` and `β`
with `W(αβp) ∩ W(αβqp) = ∅` for all competitors `q`. Case analysis of the referee's next step:
* invocation (`decide` not yet invoked): it commutes with any competitor step (Lemma 23);
* response: `αβp` and `αβqp` both contain the response, so they share their valency;
* a primitive on `R`: by Lemma 23 every competitor is poised to write `R`; then
  - `R` test&set-like: **new argument** `const_valency_contra` (the paper's argument for this
    case has a gap, see below);
  - `R` window-like, referee writes: `αβpγ` vs `αβqpγ` (case "all processes write to `R`");
  - `R` window-like, referee reads: Lemma 24(2)/29(2) and the paper's final argument.

## Differences from the paper

* **Model.** Schedules (`LLCtx.ext`) instead of arbitrary label sequences: in an admissible
  execution every process has at most one possible next label, so this loses nothing.
  Indistinguishability is agreement of the final configurations (memory, local states and
  pending operations of the observers: CSLib's `AgreeOn`). Invocations and responses are steps
  that do not access memory; all case analyses treat them (like reads, or as commuting steps).
* **Lemma 17** additionally assumes that `decide` is pending in `α` (under the paper's
  history-based indistinguishability the excluded case — `decide` already returned — is
  trivial; with configuration-based indistinguishability it is needed). In its proof, the
  operations of `q` must be counted inside the extension `β'` (`α'` may contain a different
  number of operations of `q`).
* **Lemma 19, 22, 24, 28, 29**: "due to wait-freedom" is `resps_unbounded` (a competitor
  scheduled infinitely often in an infinite competitors-only extension completes infinitely
  many operations) and `exists_solo_return`; the infinite executions are built as limits of
  chains (`chain_infExec`).
* **Theorem 25, last paragraph** ("We have that αβp is closed. Otherwise, if ... then by
  Lemma 23 ... contradicting Lemma 24(1). Thus, it must be that ...") is garbled; the intended
  argument (Lemma 23 contradicts Lemma 24(1) unless every competitor writes to `R` and the
  referee reads `R`) is the one formalized.
* **Lemma 28, test&set case**: "αβq and αβq′ are closed" — `αβq′` is supervalent there; only
  `αβq` closed is needed (typo).
* **Lemma 29**: the proof's last sentence cites Lemma 21 instead of Lemma 27 (typo); for `w = 0`
  the required sequences (`|γ| = w`, `γ = qλ`) do not exist — we use window `max w 1`.
* **Theorem 30, case "all processes T&S the same test&set object R" — proof gap.** The paper
  claims that `αβγpγ′₁q′ᵏγ′₂` and `αβγ′₁q′ᵏγpγ′₂` end with the same shared memory and are
  indistinguishable to every `q″ ≠ q, q′`. This holds if `R` is already set after `αβ`, but if
  `R` is unset, `q` wins the test&set in the first execution and `q′` wins it in the second;
  `q′` then takes `k` more steps (and the processes of `γ′₂` more steps) whose effect on the
  memory, and on what `q″` observes, depends on that outcome. The theorem is true:
  we replace the argument (`const_valency_contra`): once a competitor's step has set `R`, every
  later step of the referee (on `R`) leaves the memory unchanged and commutes with every
  competitor step, so by Lemma 17 the singleton `W(αβq u p)` does not depend on the
  competitors-only extension `u`; choosing `u` in which some competitor completes more than
  `y = W(αβqp)` operations contradicts the specification (no extension can output `y`).
  This argument does not use Lemma 29(2).
* **Generality.** Theorem 25 holds for any base objects whose primitives are read-only or blind
  writes; Theorem 30 for any window-like objects (`ObjSpec.WindowLike`) and test&set-like
  objects (`ObjSpec.TASLike`: every primitive sets the object to a fixed state; readable
  test&set objects are *not* covered, as in the paper).
* Lemma 14 is formalized in `LongLivedPossible.lean` for an atomic counter (readable
  fetch&increment), max register and snapshot (`lemma14_counter`, `lemma14_maxRegister`,
  `lemma14_snapshot`); the fetch&increment-only / fetch&add variants are not. Corollaries 26
  and 31 are not formalized: they need a composition theorem for strongly linearizable
  implementations, which the framework lacks.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Referee

open Impl

namespace LLCtx

variable {P ι L : Type} {B : ι → ObjSpec} [DecidableEq P] [DecidableEq ι] [Fintype P]
  {X : LLCtx P ι L B} {w : ℕ}

lemma Good.pend_ref_ext1_of_idle {β : List (LLabel P)} (hβ : X.Good β)
    (hp : (X.cfg β).pend X.ref = none) (hops : opsOf β X.ref = []) :
    (X.cfg (X.ext β [X.ref])).pend X.ref ≠ none := by
  have hn : X.nl β X.ref = some (.inv X.ref (roleOp X.ref X.ref)) := by
    simp [nl, hp, hops]
  rw [ext_singleton, ext1_of_some hn]
  have := (step_inv (hβ.nl_step hn).1).2.2.1
  rw [this]; simp

lemma eq_R_of_act {C : Config (llObj P) B P L} {c : P} {R i : ι} {o : (B R).Op}
    {k : (B R).Resp → L} {o' : (B i).Op} {k' : (B i).Resp → L}
    (h1 : X.I.act c (C.loc c) = .access R o k) (h2 : X.I.act c (C.loc c) = .access i o' k') :
    i = R := by
  rw [h1] at h2; simp only [Action.access.injEq] at h2; exact h2.1.symm

/-- **The final argument of Theorems 25 and 30 of [ACE26]** (uniform version): under `X.Hyp w`
there is no such implementation. -/
theorem main (hH : X.Hyp w) : False := by
  obtain ⟨c₀, hc₀⟩ := exists_comp (X := X) (by have := hH.card3; omega)
  obtain ⟨α₀, hα₀, hsup₀, hh₀⟩ := X.lemma19 hc₀
  have hnd₀ := X.lemma28 hH hα₀ hsup₀
  have hS := X.lemma27 hH
  obtain ⟨σ, hσ, hdis₀⟩ := X.lemma24_1 hS hα₀ hnd₀ hh₀
  obtain ⟨β, hβ_def⟩ : ∃ β, β = X.ext α₀ σ := ⟨_, rfl⟩
  have hβ : X.Good β := hβ_def ▸ hα₀.ext σ
  have hnd : X.NoDec β := hβ_def ▸ hnd₀.ext hσ
  have hh : X.Helping β := hβ_def ▸ hh₀.ext hσ
  have hdis : ∀ q, q ≠ X.ref →
      Disjoint (X.W (X.ext β [X.ref])) (X.W (X.ext β [q, X.ref])) := by
    intro q hq; have := hdis₀ q hq; rwa [ext_append, ext_append, ← hβ_def] at this
  have key : ∀ q, q ≠ X.ref → ∀ x, x ∈ X.W (X.ext β [X.ref]) →
      x ∈ X.W (X.ext β [q, X.ref]) → False :=
    fun q hq x h1 h2 => W_disj_contra (hdis q hq) h1 h2
  have hcl : X.Closed (X.ext β [X.ref]) := by simpa using hh [] comp_nil
  have hndβ : ¬ X.DecIn β := by simpa using hnd [] comp_nil
  have hres : respsOf β X.ref = [] := hβ.resps_ref_eq_nil hndβ
  have hrc0 : X.ref ∉ [c₀] := by simpa using Ne.symm hc₀
  by_cases hp : (X.cfg β).pend X.ref = none
  · -- the referee's next step is the invocation of `decide`: it commutes with `c₀`'s step
    have hops : opsOf β X.ref = [] := by
      rcases hβ.ref_counts with ⟨-, h⟩ | ⟨h, -⟩
      · rw [hres] at h; exact List.length_eq_zero_iff.1 h
      · exact absurd hp h
    have S := hβ.sim_swap (Ne.symm hc₀) (nonConflict_of_not_pend hp)
    have e : X.ext β [X.ref, c₀] = X.ext (X.ext β [X.ref]) [c₀] := by rw [← ext_append]; rfl
    have hcl' : X.Closed (X.ext β [X.ref, c₀]) := by
      rw [e]; exact hcl.ext (hβ.ext _) (comp_singleton hc₀)
    have hp' : (X.cfg (X.ext β [X.ref, c₀])).pend X.ref ≠ none := by
      rw [e]; exact (hβ.ext _).pend_ref_ext (hβ.pend_ref_ext1_of_idle hp hops)
        (comp_singleton hc₀)
    obtain ⟨x, hx1, hx2⟩ := X.lemma17 S.good S.good' hcl' hp' hc₀ (Q := Set.univ) trivial
      trivial S.agree
    exact key c₀ hc₀ x (W_cons_subset β X.ref [c₀] (comp_singleton hc₀) hx1) hx2
  cases hact : X.I.act X.ref ((X.cfg β).loc X.ref) with
  | ret r l =>
    -- the referee's next step returns: `βp` and `βc₀p` both contain the response
    have hnl : X.nl β X.ref = some (.ret X.ref r) := by
      rw [nl_of_pend hp]; simp [nextLabel, hact]
    have hnl' : X.nl (X.ext β [c₀]) X.ref = some (.ret X.ref r) := by
      rw [hβ.nl_ext_of_not_mem hrc0, hnl]
    have r1 : respsOf (X.ext β [X.ref]) X.ref = [r] := by
      rw [ext_singleton, ext1_of_some hnl, respsOf_append, hres]; simp
    have r2 : respsOf (X.ext β [c₀, X.ref]) X.ref = [r] := by
      rw [show [c₀, X.ref] = [c₀] ++ [X.ref] from rfl, ext_append, ext_singleton,
        ext1_of_some hnl', respsOf_append, respsOf_ext_of_not_mem hrc0, hres]; simp
    obtain ⟨x₁, hr1, hd1⟩ := (hβ.ext [X.ref]).dec_of_completed (by rw [r1]; simp)
    obtain ⟨x₂, hr2, hd2⟩ := (hβ.ext [c₀, X.ref]).dec_of_completed (by rw [r2]; simp)
    simp only [respOf, r1, r2, List.getElem?_cons_zero, Option.some.injEq] at hr1 hr2
    have hx : x₁ = x₂ := by rw [hr1] at hr2; simpa using hr2
    subst hx
    exact key c₀ hc₀ x₁ (by rw [W_eq_of_dec (hβ.ext _) hd1]; rfl)
      (by rw [W_eq_of_dec (hβ.ext _) hd2]; rfl)
  | access R o k =>
    have hacc : X.Accesses (X.cfg β) X.ref R := ⟨hp, o, k, hact⟩
    have hpref : ∀ τ, X.Comp τ → (X.cfg (X.ext (X.ext β τ) [X.ref])).pend X.ref ≠ none := by
      intro τ hτ
      have hs := hβ.ext_other hτ.not_mem
      rw [ext_singleton]
      have := (hβ.ext τ).mem_ext1_access (c := X.ref) (by rw [hs.2]; exact hp)
        (by rw [hs.1]; exact hact)
      rw [this.2.2, hs.2]; exact hp
    have hpref0 : (X.cfg (X.ext β [X.ref])).pend X.ref ≠ none := by
      simpa using hpref [] comp_nil
    -- Lemma 23: every competitor is poised to write to `R`
    have hall0 : ∀ q, q ≠ X.ref → ∃ R', X.Writes (X.cfg β) q R' := by
      intro q hq
      rcases quiet_or_writes (X := X) (X.cfg β) q with hqt | h
      · exfalso
        obtain ⟨q', hq', hqq'⟩ := exists_comp_ne (X := X) hH.card3 q
        have S := ((hβ.sim_quiet hq hqt).ext (σ := [X.ref])
          (by simpa using Ne.symm hq)).symm
        obtain ⟨x, hx1, hx2⟩ := X.lemma17 S.good S.good' hcl hpref0 hq' (Q := {x | x ≠ q})
          hqq' (Ne.symm hq) S.agree
        rw [← ext_append] at hx2
        exact key q hq x hx1 hx2
      · exact h
    have hall : ∀ q, q ≠ X.ref → X.Writes (X.cfg β) q R := by
      intro q hq
      obtain ⟨R', hR'⟩ := hall0 q hq
      by_cases hRR : R' = R
      · rwa [hRR] at hR'
      · exfalso
        have S := hβ.sim_swap (Ne.symm hq)
          (nonConflict_of_ne hacc hR'.accesses (Ne.symm hRR))
        have e : X.ext β [X.ref, q] = X.ext (X.ext β [X.ref]) [q] := by
          rw [← ext_append]; rfl
        have hcl' : X.Closed (X.ext β [X.ref, q]) := by
          rw [e]; exact hcl.ext (hβ.ext _) (comp_singleton hq)
        have hp' : (X.cfg (X.ext β [X.ref, q])).pend X.ref ≠ none := by
          rw [e]; exact (hβ.ext _).pend_ref_ext hpref0 (comp_singleton hq)
        obtain ⟨x, hx1, hx2⟩ := X.lemma17 S.good S.good' hcl' hp' hq (Q := Set.univ) trivial
          trivial S.agree
        exact key q hq x (W_cons_subset β X.ref [q] (comp_singleton hq) hx1) hx2
    rcases hH.obj R with hW | ⟨⟨s₁, hs₁⟩, -⟩
    swap
    · -- `R` is a test&set object: the referee's step becomes invisible once `R` is set
      have hα₁ := hβ.ext [c₀]
      have hmem1 : (X.cfg (X.ext β [c₀])).mem R = s₁ := by
        obtain ⟨hp0, o0, k0, hact0⟩ := (hall c₀ hc₀).accesses
        rw [ext_singleton, (hβ.mem_ext1_access hp0 hact0).1, hs₁]
      apply X.const_valency_contra hS hα₁ (hnd.ext (comp_singleton hc₀))
        (hh.ext (comp_singleton hc₀)) ?_ ?_ hc₀
      · intro u hu
        have e : X.ext (X.ext β [c₀]) (u ++ [X.ref]) = X.ext (X.ext β ([c₀] ++ u)) [X.ref] := by
          simp only [ext_append]
        rw [e]
        exact hpref _ (comp_append.2 ⟨comp_singleton hc₀, hu⟩)
      · intro u hu c hc
        rw [ext_append, ext_append]
        have hg := hα₁.ext u
        refine (hg.sim_swap (Ne.symm hc) ?_).cfg_eq
        have hm : (X.cfg (X.ext (X.ext β [c₀]) u)).mem R = s₁ := hα₁.tas_mem hs₁ hmem1 u
        have hs : (X.cfg (X.ext (X.ext β [c₀]) u)).loc X.ref = (X.cfg β).loc X.ref := by
          rw [← ext_append]
          exact (hβ.ext_other (comp_append.2 ⟨comp_singleton hc₀, hu⟩).not_mem).1
        intro i o₁ k₁ j o₂ k₂ _ hacta _ hactb
        rw [hs] at hacta
        have hiR : i = R := eq_R_of_act hact hacta
        subst hiR
        by_cases hj : j = i
        · subst hj; right; rw [hm, hs₁, hs₁]; exact ⟨rfl, rfl⟩
        · left; exact Ne.symm hj
    -- `R` is a window register
    obtain ⟨q, hq⟩ := exists_comp (X := X) (by have := hH.card3; omega)
    obtain ⟨q', hq', hq'q⟩ := exists_comp_ne (X := X) hH.card3 q
    obtain ⟨l₀, l₁, l₂, hl₀, hl₁, hl₂, hlnd, hlm⟩ := exists_lists (X := X) (m := w - 1)
      (by have := hH.cardw; have := hH.w1; omega) q q'
    have hw1 := hH.w1
    -- facts on the chosen lists
    have hnd012 := List.nodup_append.1 hlnd
    have hnd01 := List.nodup_append.1 hnd012.1
    have m0 : ∀ x ∈ l₀, x ≠ X.ref ∧ x ≠ q ∧ x ≠ q' := fun x hx => hlm x (by simp [hx])
    have m1 : ∀ x ∈ l₁, x ≠ X.ref ∧ x ≠ q ∧ x ≠ q' := fun x hx => hlm x (by simp [hx])
    have m2 : ∀ x ∈ l₂, x ≠ X.ref ∧ x ≠ q ∧ x ≠ q' := fun x hx => hlm x (by simp [hx])
    have d01 : ∀ x ∈ l₀, x ∉ l₁ := fun x hx h => hnd01.2.2 x hx x h rfl
    have d02 : ∀ x ∈ l₀, x ∉ l₂ := fun x hx h => hnd012.2.2 x (by simp [hx]) x h rfl
    have d12 : ∀ x ∈ l₁, x ∉ l₂ := fun x hx h => hnd012.2.2 x (by simp [hx]) x h rfl
    have c0 : X.Comp l₀ := fun x hx => (m0 x hx).1
    have c1 : X.Comp l₁ := fun x hx => (m1 x hx).1
    have c2 : X.Comp l₂ := fun x hx => (m2 x hx).1
    by_cases hro : (B R).ReadOnly o
    swap
    · -- the referee writes to `R`: `βpγ` and `βqpγ` are indistinguishable to `p` and `q'`
      have hwsnd : (X.ref :: l₀).Nodup := List.nodup_cons.2 ⟨fun h => (m0 _ h).1 rfl, hnd01.1⟩
      have hwsq : ∀ a ∈ X.ref :: l₀, a ≠ q := by
        intro a ha; rcases List.mem_cons.1 ha with rfl | ha
        · exact Ne.symm hq
        · exact (m0 a ha).2.1
      have hstate : ∀ x, x ≠ q → (X.cfg β).loc x = (X.cfg (X.ext β [q])).loc x ∧
          (X.cfg β).pend x = (X.cfg (X.ext β [q])).pend x := fun x hx => by
        have := hβ.ext_other (σ := [q]) (by simpa using hx); exact ⟨this.1.symm, this.2.symm⟩
      have S := hβ.sim_window (hβ.ext [q]) hW hwsnd (List.cons_ne_nil _ _)
        (by simp [hl₀]; omega) (Q := {x | x ≠ q}) (fun x hx => hstate x hx)
        (fun a ha => hstate a (hwsq a ha))
        (fun j hj => by
          rw [ext_singleton, hβ.mem_ext1 (fun h => hj (Accesses.unique h (hall q hq).accesses))])
        (fun a ha => by
          rcases List.mem_cons.1 ha with rfl | ha
          · exact ⟨hp, o, k, hact, hro⟩
          · exact hall a (m0 a ha).1)
        (by rw [ext_singleton, opsOf_ext1_of_ne (Ne.symm hq)])
      have e : X.ext β (X.ref :: l₀) = X.ext (X.ext β [X.ref]) l₀ := by
        rw [← ext_append]; rfl
      have hcl' : X.Closed (X.ext β (X.ref :: l₀)) := by
        rw [e]; exact hcl.ext (hβ.ext _) c0
      have hp' : (X.cfg (X.ext β (X.ref :: l₀))).pend X.ref ≠ none := by
        rw [e]; exact (hβ.ext _).pend_ref_ext hpref0 c0
      obtain ⟨x, hx1, hx2⟩ := X.lemma17 S.good S.good' hcl' hp' hq' (Q := {x | x ≠ q})
        hq'q (Ne.symm hq) S.agree
      have e2 : X.ext (X.ext β [q]) (X.ref :: l₀) = X.ext (X.ext β [q, X.ref]) l₀ := by
        rw [← ext_append, ← ext_append]; rfl
      rw [e2] at hx2
      exact key q hq x (W_cons_subset β X.ref l₀ c0 hx1) (W_ext_subset _ c0 hx2)
    -- the referee reads `R`: Lemma 24(2) / 29(2) with `G = qλ`, `A = q'λ'₁`, `V = q'λ'₂`
    set G := q :: l₀ with hG_def
    set A := q' :: l₁ with hA_def
    set V := q' :: l₂ with hV_def
    have cG : X.Comp G := comp_cons hq c0
    have cA : X.Comp A := comp_cons hq' c1
    have cV : X.Comp V := comp_cons hq' c2
    obtain ⟨kk, D1, D2⟩ := X.lemma24_2 hS hβ hnd hh cA cG cV hq'
    set G' := G ++ [X.ref] with hG'_def
    have hqG : ∀ x ∈ G, x ≠ X.ref ∧ x ≠ q' ∧ x ∉ l₁ ∧ x ∉ l₂ := by
      intro x hx; rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨hq, Ne.symm hq'q, fun h => (m1 x h).2.1 rfl, fun h => (m2 x h).2.1 rfl⟩
      · exact ⟨(m0 x hx).1, (m0 x hx).2.2, d01 x hx, d02 x hx⟩
    have hG'mem : ∀ x ∈ G', x ≠ q' ∧ x ∉ l₁ ∧ x ∉ l₂ := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact ⟨(hqG x hx).2.1, (hqG x hx).2.2⟩
      · simp only [List.mem_singleton] at hx; subst hx
        exact ⟨Ne.symm hq', fun h => (m1 _ h).1 rfl, fun h => (m2 _ h).1 rfl⟩
    have hGnd : G.Nodup := List.nodup_cons.2 ⟨fun h => (m0 q h).2.1 rfl, hnd01.1⟩
    have hG'nd : G'.Nodup := by
      rw [hG'_def, List.nodup_append]
      refine ⟨hGnd, List.nodup_singleton _, ?_⟩
      intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb; exact (hqG a ha).1
    have hq'G' : q' ∉ G' := fun h => (hG'mem q' h).1 rfl
    have hAnd : A.Nodup := List.nodup_cons.2 ⟨fun h => (m1 q' h).2.2 rfl, hnd01.2.1⟩
    have hVnd : V.Nodup := List.nodup_cons.2 ⟨fun h => (m2 q' h).2.2 rfl, hnd012.2.1⟩
    have hAG' : ∀ x ∈ A, x ∉ G' := by
      intro x hx h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hq'G' h
      · exact (hG'mem x h).2.1 hx
    -- `Y2 = β A q'^k`
    set Ak := A ++ List.replicate kk q' with hAk_def
    have cAk : X.Comp Ak := comp_append.2 ⟨cA, comp_replicate hq' kk⟩
    have hAkG' : ∀ x ∈ G', x ∉ Ak := by
      intro x hx h
      rcases List.mem_append.1 h with h | h
      · exact hAG' x h hx
      · rw [List.eq_of_mem_replicate h] at hx; exact hq'G' hx
    set Y2 := X.ext β Ak with hY2_def
    have hY2 : X.Good Y2 := hβ.ext Ak
    have hY2st : ∀ x, x ∉ Ak → (X.cfg Y2).loc x = (X.cfg β).loc x ∧
        (X.cfg Y2).pend x = (X.cfg β).pend x := fun x hx => hβ.ext_other hx
    have hcG : ∀ σ', X.Comp σ' → X.Closed (X.ext β (σ' ++ [X.ref])) := hh
    rcases quiet_or_writes (X := X) (X.cfg Y2) q' with hqt | ⟨R', hR'⟩
    · -- `q'` reads (or returns/invokes): `βAq'^(k+1)Gp` and `βAq'^kGpq'` are
      -- indistinguishable to `p` and `q`
      have S1 := (hY2.sim_quiet hq' hqt).ext (σ := G') (fun p hp' => (hG'mem p hp').1)
      have hZ2 := hY2.ext G'
      have hqt' : X.Quiet (X.cfg (X.ext Y2 G')) q' :=
        hqt.congr (hY2.ext_other hq'G').1.symm (hY2.ext_other hq'G').2.symm
      have S := S1.trans (hZ2.sim_quiet hq' hqt').symm
      have e3 : X.ext β (Ak ++ [q'] ++ G ++ [X.ref]) = X.ext (X.ext Y2 [q']) G' := by
        rw [hY2_def, ← ext_append, ← ext_append]; simp [hG'_def]
      have e4 : X.ext β (Ak ++ G ++ [X.ref] ++ [q']) = X.ext (X.ext Y2 G') [q'] := by
        rw [hY2_def, ← ext_append, ← ext_append]; simp [hG'_def]
      have hcomp3 : X.Comp (Ak ++ [q'] ++ G) :=
        comp_append.2 ⟨comp_append.2 ⟨cAk, comp_singleton hq'⟩, cG⟩
      have hcl3 : X.Closed (X.ext (X.ext Y2 [q']) G') := by rw [← e3]; exact hcG _ hcomp3
      have hp3 : (X.cfg (X.ext (X.ext Y2 [q']) G')).pend X.ref ≠ none := by
        rw [← e3, ext_append]; exact hpref _ hcomp3
      obtain ⟨x, hx1, hx2⟩ := X.lemma17 S.good S.good' hcl3 hp3 hq (Q := {x | x ≠ q'})
        (Ne.symm hq'q) (Ne.symm hq') S.agree
      rw [← e3] at hx1; rw [← e4] at hx2
      apply W_disj_contra D2 (x := x)
      · rw [List.replicate_succ', ← List.append_assoc]; exact hx1
      · exact hx2
    by_cases hRR : R' = R
    swap
    · -- `q'` accesses another object: its step commutes with those of `G` and `p`
      have S := hY2.sim_pass (c := q') (u := G') hq'G' hG'nd hR'.accesses (fun a ha => by
        refine ⟨R, Ne.symm hRR, ?_⟩
        have hs := hY2st a (hAkG' a ha)
        rcases List.mem_append.1 ha with ha | ha
        · exact (hall a (hqG a ha).1).accesses.congr hs.1.symm hs.2.symm
        · simp only [List.mem_singleton] at ha; subst ha
          exact hacc.congr hs.1.symm hs.2.symm)
      have e3 : X.ext β (Ak ++ [q'] ++ G ++ [X.ref]) = X.ext Y2 (q' :: G') := by
        rw [hY2_def, ← ext_append]; simp [hG'_def]
      have e4 : X.ext β (Ak ++ G ++ [X.ref] ++ [q']) = X.ext Y2 (G' ++ [q']) := by
        rw [hY2_def, ← ext_append]; simp [hG'_def]
      have hcomp3 : X.Comp (Ak ++ [q'] ++ G) :=
        comp_append.2 ⟨comp_append.2 ⟨cAk, comp_singleton hq'⟩, cG⟩
      have hcl3 : X.Closed (X.ext Y2 (q' :: G')) := by rw [← e3]; exact hcG _ hcomp3
      have hp3 : (X.cfg (X.ext Y2 (q' :: G'))).pend X.ref ≠ none := by
        rw [← e3, ext_append]; exact hpref _ hcomp3
      obtain ⟨x, hx1, hx2⟩ := X.lemma17 S.good S.good' hcl3 hp3 hq (Q := Set.univ) trivial
        trivial S.agree
      rw [← e3] at hx1; rw [← e4] at hx2
      apply W_disj_contra D2 (x := x)
      · rw [List.replicate_succ', ← List.append_assoc]; exact hx1
      · exact hx2
    subst hRR
    -- `q'` is poised to write to `R` after `βAq'^k`: `βGpAq'^kV` and `βAq'^kGpV` end in the
    -- same configuration
    have hresp : ∀ o', ¬ (B R').ReadOnly o' → ∀ s s', ((B R').δ s o').2 = ((B R').δ s' o').2 :=
      fun o' ho' => (hW.1 o').resolve_left ho'
    -- Step 1: the writes of `G`
    obtain ⟨os, h1, h2, h3, h4, h5, h6⟩ := hβ.window hY2 hresp hGnd
      (fun a ha => by have := hY2st a (hAkG' a (List.mem_append_left _ ha))
                      exact ⟨this.1.symm, this.2.symm⟩)
      (fun a ha => hall a (hqG a ha).1)
    have hmR : (X.cfg (X.ext β G)).mem R' = (X.cfg (X.ext Y2 G)).mem R' := by
      rw [h3, h4]
      exact hW.2 os (by intro h; rw [h] at h1; simp [hG_def] at h1)
        (by simp [h1, hG_def, hl₀]; omega) h2 _ _
    -- Step 2: the read of the referee
    have hgβG := hβ.ext G
    have hgY2G := hY2.ext G
    have hsβG : (X.cfg (X.ext β G)).loc X.ref = (X.cfg β).loc X.ref ∧
        (X.cfg (X.ext β G)).pend X.ref = (X.cfg β).pend X.ref := hβ.ext_other cG.not_mem
    have hsY2G : (X.cfg (X.ext Y2 G)).loc X.ref = (X.cfg β).loc X.ref ∧
        (X.cfg (X.ext Y2 G)).pend X.ref = (X.cfg β).pend X.ref := by
      rw [hY2_def, ← ext_append]
      exact hβ.ext_other (comp_append.2 ⟨cAk, cG⟩).not_mem
    obtain ⟨r1m, r1l, r1p⟩ := hgβG.mem_ext1_access (c := X.ref) (by rw [hsβG.2]; exact hp)
      (by rw [hsβG.1]; exact hact)
    obtain ⟨r2m, r2l, r2p⟩ := hgY2G.mem_ext1_access (c := X.ref) (by rw [hsY2G.2]; exact hp)
      (by rw [hsY2G.1]; exact hact)
    set X1 := X.ext β G' with hX1_def
    set Z2 := X.ext Y2 G' with hZ2_def
    have eX1 : X1 = X.ext1 (X.ext β G) X.ref := by rw [hX1_def, hG'_def, ext_append, ext_singleton]
    have eZ2 : Z2 = X.ext1 (X.ext Y2 G) X.ref := by rw [hZ2_def, hG'_def, ext_append, ext_singleton]
    have hX1 : X.Good X1 := hβ.ext G'
    have hZ2 : X.Good Z2 := hY2.ext G'
    -- (a) the processes of `G'` agree at `X1` and `Z2`
    have hagG' : ∀ a ∈ G', (X.cfg X1).loc a = (X.cfg Z2).loc a ∧
        (X.cfg X1).pend a = (X.cfg Z2).pend a := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · have hne : a ≠ X.ref := (hqG a ha).1
        rw [eX1, eZ2, (hgβG.ext1_other hne).1, (hgβG.ext1_other hne).2,
          (hgY2G.ext1_other hne).1, (hgY2G.ext1_other hne).2]
        exact h6 a ha
      · simp only [List.mem_singleton] at ha; subst ha
        rw [eX1, eZ2, r1l, r2l, r1p, r2p, hsβG.2, hsY2G.2, hmR]
        exact ⟨rfl, rfl⟩
    -- (b) memory
    have hro' : ∀ s, ((B R').δ s o).1 = s := hro
    have hmX1 : ∀ j, j ≠ R' → (X.cfg X1).mem j = (X.cfg β).mem j := by
      intro j hj
      rw [eX1, hgβG.mem_ext1 (fun h => hj (Accesses.unique h
        (hacc.congr hsβG.1.symm hsβG.2.symm)))]
      exact (h5 j hj).1
    have hmZ2 : ∀ j, j ≠ R' → (X.cfg Z2).mem j = (X.cfg Y2).mem j := by
      intro j hj
      rw [eZ2, hgY2G.mem_ext1 (fun h => hj (Accesses.unique h
        (hacc.congr hsY2G.1.symm hsY2G.2.symm)))]
      exact (h5 j hj).2
    have hmRR : (X.cfg X1).mem R' = (X.cfg Z2).mem R' := by
      rw [eX1, eZ2, r1m, r2m, hro', hro', hmR]
    -- (c) other processes
    have hX1st : ∀ x, x ∉ G' → (X.cfg X1).loc x = (X.cfg β).loc x ∧
        (X.cfg X1).pend x = (X.cfg β).pend x := fun x hx => hβ.ext_other hx
    have hZ2st : ∀ x, x ∉ G' → (X.cfg Z2).loc x = (X.cfg Y2).loc x ∧
        (X.cfg Z2).pend x = (X.cfg Y2).pend x := fun x hx => hY2.ext_other hx
    have hopsβ : opsOf β X.ref ≠ [] := (hβ.pend_ref_ne_none_iff.1 hp).1
    have hinv : ∀ τ, opsOf (X.ext β τ) X.ref ≠ [] := by
      intro τ h; exact hopsβ ((hβ.opsOf_ext_ref_eq_nil τ).1 h).1
    -- Step 3: the writes of `A` after `X1` and after `β`
    have S3 := hX1.sim_window hβ hW hAnd (List.cons_ne_nil _ _)
      (by simp [hA_def, hl₁]; omega) (Q := {x | x ∉ G'})
      (fun x hx => hX1st x hx) (fun a ha => hX1st a (hAG' a ha))
      (fun j hj => hmX1 j hj)
      (fun a ha => (hall a (cA a ha)).congr (hX1st a (hAG' a ha)).1.symm
        (hX1st a (hAG' a ha)).2.symm)
      (by rw [hX1_def]; exact ⟨fun h => absurd h (hinv _), fun h => absurd h hopsβ⟩)
    have S4 := S3.ext (σ := List.replicate kk q') (fun p hp' => by
      rw [List.eq_of_mem_replicate hp']; exact hq'G')
    have eY2 : X.ext (X.ext β A) (List.replicate kk q') = Y2 := by
      rw [hY2_def, hAk_def, ext_append]
    rw [eY2] at S4
    set Y1 := X.ext (X.ext X1 A) (List.replicate kk q') with hY1_def
    have hY1st : ∀ x, x ∉ Ak → (X.cfg Y1).loc x = (X.cfg X1).loc x ∧
        (X.cfg Y1).pend x = (X.cfg X1).pend x := by
      intro x hx
      rw [hY1_def, ← ext_append]; exact hX1.ext_other hx
    -- Step 4: the writes of `V`
    have hYZ : ∀ x, (X.cfg Y1).loc x = (X.cfg Z2).loc x ∧
        (X.cfg Y1).pend x = (X.cfg Z2).pend x := by
      intro x
      by_cases hx : x ∈ G'
      · rw [(hY1st x (hAkG' x hx)).1, (hY1st x (hAkG' x hx)).2]; exact hagG' x hx
      · rw [S4.agree.loc x hx, S4.agree.pend x hx, (hZ2st x hx).1, (hZ2st x hx).2]
        exact ⟨rfl, rfl⟩
    have hVQ : ∀ a ∈ V, a ∉ G' := by
      intro a ha h
      rcases List.mem_cons.1 ha with rfl | ha
      · exact hq'G' h
      · exact (hG'mem a h).2.2 ha
    have S5 := S4.good.sim_window hZ2 hW hVnd (List.cons_ne_nil _ _)
      (by simp [hV_def, hl₂]; omega) (Q := Set.univ) (fun x _ => hYZ x) (fun a _ => hYZ a)
      (fun j hj => by rw [S4.agree.mem, hmZ2 j hj])
      (fun a ha => by
        have hY := S4.agree.loc a (hVQ a ha)
        have hYp := S4.agree.pend a (hVQ a ha)
        rcases List.mem_cons.1 ha with rfl | ha'
        · exact hR'.congr hY.symm hYp.symm
        · have hs := hY2st a (fun h => by
            rcases List.mem_append.1 h with h | h
            · rcases List.mem_cons.1 h with rfl | h
              · exact (m2 _ ha').2.2 rfl
              · exact d12 a h ha'
            · exact (m2 _ ha').2.2 (List.eq_of_mem_replicate h))
          exact ((hall a (m2 a ha').1).congr hs.1.symm hs.2.symm).congr hY.symm hYp.symm)
      (⟨fun h => absurd h (by rw [hY1_def, ← ext_append, hX1_def, ← ext_append]; exact hinv _),
        fun h => absurd h (by rw [hZ2_def, hY2_def, ← ext_append]; exact hinv _)⟩)
    have e1 : X.ext β (G ++ [X.ref] ++ A ++ List.replicate kk q' ++ V) = X.ext Y1 V := by
      rw [hY1_def, hX1_def, ← ext_append, ← ext_append, ← ext_append]; simp [hG'_def]
    have e2 : X.ext β (A ++ List.replicate kk q' ++ G ++ [X.ref] ++ V) = X.ext Z2 V := by
      rw [hZ2_def, hY2_def, ← ext_append, ← ext_append]; simp [hG'_def, hAk_def]
    have hcl1 : X.Closed (X.ext Y1 V) := by
      rw [hY1_def, ← ext_append, ← ext_append]
      exact (hcG G cG).ext (hβ.ext _) (comp_append.2 ⟨cA,
        comp_append.2 ⟨comp_replicate hq' kk, cV⟩⟩)
    have hX1p : (X.cfg X1).pend X.ref ≠ none := by rw [eX1, r1p, hsβG.2]; exact hp
    have hp1 : (X.cfg (X.ext Y1 V)).pend X.ref ≠ none := by
      rw [hY1_def, ← ext_append, ← ext_append]
      exact hX1.pend_ref_ext hX1p (comp_append.2 ⟨cA, comp_append.2 ⟨comp_replicate hq' kk, cV⟩⟩)
    obtain ⟨x, hx1, hx2⟩ := X.lemma17 S5.good S5.good' hcl1 hp1 hq (Q := Set.univ) trivial
      trivial S5.agree
    rw [← e1] at hx1; rw [← e2] at hx2
    exact W_disj_contra D1 hx1 hx2

end LLCtx

/-! ## The theorems -/

variable {P ι L : Type} {B : ι → ObjSpec} [Fintype P] [DecidableEq P] [DecidableEq ι]

/-- The context of Section 5 built from the hypotheses of the theorems. -/
def LLCtx.ofHyp {I : Impl (llObj P) B P L} {ref : P} (hallow : ∀ p, I.allowed p (roleOp ref p))
    (hwf : I.WaitFreeOn (LLAdm ref))
    (h : List (LLabel P) → List (OpId P × ContestOp P × LLResp))
    (hlin : ∀ α, I.Valid α → LLAdm ref α → IsNLinearization (llSpec P) α (h α))
    (hpc : ∀ α β, I.Valid β → LLAdm ref β → α <+: β → h α <+: h β) : LLCtx P ι L B :=
  ⟨I, ref, h, hallow, hwf, hlin, hpc⟩

/-- **Theorem 25 of [ACE26].** For `n ≥ 3` processes there is no wait-free strongly
linearizable implementation of the long-lived contest object from read/write registers.

Base objects are arbitrary objects all of whose primitives are read-only or blind writes
(`hB`, e.g. `register V v₀`, see `register_rw`); wait-freedom and strong linearizability (w.r.t.
the nondeterministic specification `llSpec`) are only assumed on admissible executions
(`LLAdm ref`: competitors invoke `compete`, the referee invokes `decide` at most once). -/
theorem theorem25 (ref : P) (hP : 3 ≤ Fintype.card P)
    (hB : ∀ i o, (B i).ReadOnly o ∨ (B i).Overwrites o)
    (I : Impl (llObj P) B P L) (hallow : ∀ p, I.allowed p (roleOp ref p))
    (hwf : I.WaitFreeOn (LLAdm ref)) (hsl : I.NStrongLinOn (llSpec P) (LLAdm ref)) : False := by
  obtain ⟨h, hlin, hpc⟩ := hsl
  let X : LLCtx P ι L B := LLCtx.ofHyp hallow hwf h hlin hpc
  exact LLCtx.main (X := X) (w := 1)
    ⟨fun i => Or.inl (ObjSpec.windowLike_one_of_rw (hB i)), le_rfl, hP, by omega⟩

/-- **Theorem 30 of [ACE26].** For `n ≥ 4` processes and `3w ≤ n` there is no wait-free
strongly linearizable implementation of the long-lived contest object from `w`-window
registers and test&set objects.

Every base object is window-like with window `w` (`ObjSpec.WindowLike`, e.g. `windowObj V w`)
or test&set-like (`ObjSpec.TASLike`: every primitive sets the object to a fixed state, e.g.
`tasObj`). Wait-freedom and strong linearizability are only assumed on admissible executions. -/
theorem theorem30 (ref : P) (w : ℕ) (hP : 4 ≤ Fintype.card P) (hw : 3 * w ≤ Fintype.card P)
    (hB : ∀ i, (B i).WindowLike w ∨ (B i).TASLike)
    (I : Impl (llObj P) B P L) (hallow : ∀ p, I.allowed p (roleOp ref p))
    (hwf : I.WaitFreeOn (LLAdm ref)) (hsl : I.NStrongLinOn (llSpec P) (LLAdm ref)) : False := by
  obtain ⟨h, hlin, hpc⟩ := hsl
  let X : LLCtx P ι L B := LLCtx.ofHyp hallow hwf h hlin hpc
  refine LLCtx.main (X := X) (w := max w 1) ⟨fun i => ?_, le_max_right _ _, by omega, ?_⟩
  · rcases hB i with h1 | h1
    · exact Or.inl (h1.mono (le_max_left _ _))
    · exact Or.inr ⟨h1, hP⟩
  · rcases Nat.eq_zero_or_pos w with h0 | h0
    · subst h0; simp; omega
    · rw [max_eq_left h0]; exact hw

/-- Theorem 25 for the unrestricted notions of wait-freedom and strong linearizability. -/
theorem theorem25' (ref : P) (hP : 3 ≤ Fintype.card P)
    (hB : ∀ i o, (B i).ReadOnly o ∨ (B i).Overwrites o)
    (I : Impl (llObj P) B P L) (hallow : ∀ p, I.allowed p (roleOp ref p))
    (hwf : I.WaitFree) (hsl : I.NStronglyLinearizable (llSpec P)) : False :=
  theorem25 ref hP hB I hallow (hwf.waitFreeOn _) (hsl.nStrongLinOn _)

/-- Theorem 30 for the unrestricted notions of wait-freedom and strong linearizability. -/
theorem theorem30' (ref : P) (w : ℕ) (hP : 4 ≤ Fintype.card P) (hw : 3 * w ≤ Fintype.card P)
    (hB : ∀ i, (B i).WindowLike w ∨ (B i).TASLike)
    (I : Impl (llObj P) B P L) (hallow : ∀ p, I.allowed p (roleOp ref p))
    (hwf : I.WaitFree) (hsl : I.NStronglyLinearizable (llSpec P)) : False :=
  theorem30 ref w hP hw hB I hallow (hwf.waitFreeOn _) (hsl.nStrongLinOn _)

/-! ## Non-vacuity of the hypotheses on the base objects -/

/-- Read/write registers satisfy the hypothesis of Theorem 25. -/
lemma register_rw (V : Type) (v₀ : V) (o : (register V v₀).Op) :
    (register V v₀).ReadOnly o ∨ (register V v₀).Overwrites o := by
  cases o with
  | read => exact Or.inl (register_read_readOnly v₀)
  | write v => exact Or.inr (register_write_overwrites v₀ v)

/-- `w`-window registers satisfy the hypothesis of Theorem 30. -/
lemma windowObj_hyp30 (V : Type) (w : ℕ) :
    (windowObj V w).WindowLike w ∨ (windowObj V w).TASLike :=
  Or.inl (windowObj_windowLike V le_rfl)

/-- Test&set objects satisfy the hypothesis of Theorem 30. -/
lemma tasObj_hyp30 (w : ℕ) : tasObj.WindowLike w ∨ tasObj.TASLike := Or.inr tasObj_tasLike

end Cslib.SharedMemory.Referee
