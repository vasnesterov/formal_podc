import Papers.PODC2018.LockFreeVsWaitFree.Claim9
import Cslib.Computability.Distributed.SharedMemory.ObjClasses.Basic

/-!
# Theorem 11 of [ACHP18]: no wait-free `n`-LLAA from `(n-1)`-window registers

* `Ctx.build` — the construction in the proof of Lemma 8 (case `n > 2`): the processes other
  than `p₀` and `q` run solo in turn, each until it is about to write `R` or has completed `k + 3`
  operations without writing `R`.
* `Ctx.window` — the window argument of Lemma 8: if all processes are about to write the same
  `(n-1)`-window-like object `R`, the configurations after `p₀, p₂, …, p_{n-1}` write and after
  `q, p₀, p₂, …, p_{n-1}` write agree on everything except `q`.
* `Ctx.false_of_critical` — **Lemma 8 + Theorem 11**: a critical execution of an implementation
  from `(n-1)`-window-like base objects leads to a contradiction.
* `theorem_11` — **Theorem 11**: there is no wait-free linearizable implementation of `n`-LLAA
  from base objects that are window-like with window `n - 1` (this includes `k`-window registers
  for `k ≤ n - 1`, in particular read/write registers, `theorem_11_window`).

The paper proves Lemma 8 as a separate statement ("some extension is ambivalent or has a critical
extension") and then derives the contradiction in Theorem 11 by a case analysis on the two
outcomes. We merge the two: in each case of Lemma 8 we directly produce two univalent
executions with different values in which some process `q ≠ p₀` returned the same value after
`k + 2` earlier operations (`Ctx.false_of_witness`).
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeVsWaitFree

open Cslib SharedMemory Impl

namespace Ctx

variable {P ι L : Type} {B : ι → ObjSpec} [DecidableEq P] [DecidableEq ι] {X : Ctx P ι L B}

/-! ### Running the other processes until they are about to write `R` -/

/-- **The construction of Lemma 8** (case `n > 2`): the processes of `rs` run solo in turn, each
until it is about to write `R` or has completed `k + 3` operations. Either all of them end up
about to write `R`, or one of them completed `k + 3` operations without anybody writing `R`. -/
theorem build {α : List (LLabel P)} (hα : X.Good α) {q : P} {R : ι} (k : ℕ) :
    ∀ rs : List P, rs.Nodup → (∀ r ∈ rs, r ≠ X.p₀ ∧ r ≠ q) →
    ∀ σ : List P, X.p₀ ∉ σ → q ∉ σ → (∀ r ∈ rs, r ∉ σ) → X.NoW R α σ →
      (∃ τ : List P, (∀ p ∈ τ, p ∈ rs) ∧ X.NoW R α (σ ++ τ) ∧
          ∀ r ∈ rs, X.Wr (X.ext α (σ ++ τ)) r R) ∨
      (∃ (σ' : List P) (r : P) (x : ℝ) (m : ℕ), X.p₀ ∉ σ' ∧ q ∉ σ' ∧ X.NoW R α σ' ∧
          r ≠ X.p₀ ∧ k + 2 ≤ m ∧ respOf (X.ext α σ') (r, m) = some x) := by
  intro rs
  induction rs with
  | nil => intro _ _ σ _ _ _ hn; exact Or.inl ⟨[], by simp, by simpa using hn, by simp⟩
  | cons r rs ih =>
    intro hnd hrs σ h0 hq hσ hn
    obtain ⟨hrrs, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨hr0, hrq⟩ := hrs r List.mem_cons_self
    have hβ : X.Good (X.ext α σ) := hα.ext σ
    classical
    have hex : ∃ N, X.Wr (X.ext (X.ext α σ) (List.replicate N r)) r R ∨
        k + 3 ≤ (respsOf (X.extL (X.ext α σ) (List.replicate N r)) r).length := by
      obtain ⟨N, hN⟩ := hβ.exists_resps_extL hr0 (k + 3)
      exact ⟨N, Or.inr hN⟩
    set N := Nat.find hex
    have hmin : ∀ n < N, ¬ X.Wr (X.ext (X.ext α σ) (List.replicate n r)) r R :=
      fun n hn h => Nat.find_min hex hn (Or.inl h)
    have hn1 : X.NoW R α (σ ++ List.replicate N r) :=
      (noW_append R α σ _).2 ⟨hn, noW_replicate R _ r N hmin⟩
    have hr0' : X.p₀ ∉ σ ++ List.replicate N r := by
      simp only [List.mem_append, not_or]
      exact ⟨h0, fun h => hr0 (List.eq_of_mem_replicate h).symm⟩
    have hrq' : q ∉ σ ++ List.replicate N r := by
      simp only [List.mem_append, not_or]
      exact ⟨hq, fun h => hrq (List.eq_of_mem_replicate h).symm⟩
    rcases Nat.find_spec hex with hW | hK
    · rcases ih hnd' (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr'))
        (σ ++ List.replicate N r) hr0' hrq' (fun r' hr' => by
          simp only [List.mem_append, not_or]
          refine ⟨hσ r' (List.mem_cons_of_mem _ hr'), fun h => ?_⟩
          rw [List.eq_of_mem_replicate h] at hr'; exact hrrs hr') hn1 with
        ⟨τ, hτ, hnτ, hwτ⟩ | h
      · refine Or.inl ⟨List.replicate N r ++ τ, fun p hp => ?_, by simpa using hnτ, ?_⟩
        · rcases List.mem_append.1 hp with hp | hp
          · rw [List.eq_of_mem_replicate hp]; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hτ p hp)
        · intro r' hr'
          rcases List.mem_cons.1 hr' with rfl | hr'
          · have hrτ : r' ∉ τ := fun h => hrrs (hτ _ h)
            rw [← List.append_assoc, ext_append,
              (hα.ext _).wr_ext_of_not_mem hrτ, ext_append]
            exact hW
          · simpa using hwτ r' hr'
      · exact Or.inr h
    · obtain ⟨x, hx⟩ := exists_last_resp hK
      obtain ⟨m, hm, hxm⟩ := hx (X.ext α σ)
      refine Or.inr ⟨σ ++ List.replicate N r, r, x, m, hr0', hrq', hn1, hr0, hm, ?_⟩
      rw [ext_append, ext_eq_append (X.ext α σ)]; exact hxm

/-! ### The window argument -/

/-- If all processes of `ps` are poised, the schedule `ps` consists of their internal steps. -/
lemma ext_eq_blockWrite {D : List (LLabel P)} (hD : X.Good D) {R : ι} :
    ∀ ps : List P, ps.Nodup → (∀ r ∈ ps, ∃ o, X.I.PoisedAt (X.cfg D) r R o) →
      X.ext D ps = D ++ blockWrite ps := by
  intro ps
  induction ps generalizing D with
  | nil => intros; simp
  | cons p ps ih =>
    intro hnd hpo
    obtain ⟨hp, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨o, hpend, k, hact⟩ := hpo p List.mem_cons_self
    have hnl : X.nl D p = some (.tau p) := by
      rw [nl_of_pend hpend]; simp [nextLabel, hact]
    rw [ext_cons, ext1_of_some hnl, ih (hD.nl_step hnl).2 hnd' (fun r hr => by
      obtain ⟨o', h'⟩ := hpo r (List.mem_cons_of_mem _ hr)
      refine ⟨o', ?_⟩
      have hrp : r ∉ [p] := by
        simp only [List.mem_singleton]; rintro rfl; exact hp hr
      rw [← ext1_of_some hnl, ← ext_singleton, hD.poised_ext_of_not_mem hrp]
      exact h')]
    simp

/-- **The window argument of Lemma 8.** If `q` and all processes of `ps` (at least `w` of them)
are about to write the same base object `R`, window-like with window `w`, then the
configurations after the writes of `ps` and after the writes of `q` and then `ps` agree on the
memory and on all processes but `q`. -/
theorem window {D : List (LLabel P)} (hD : X.Good D) {R : ι} {w : ℕ} (hR : (B R).WindowLike w)
    {q : P} (ps : List P) (hnd : ps.Nodup) (hq : q ∉ ps) (hne : ps ≠ []) (hw : w ≤ ps.length)
    (hW : ∀ r ∈ q :: ps, X.Wr D r R) :
    AgreeOn {r | r ≠ q} (X.cfg (X.ext D ps)) (X.cfg (X.ext D (q :: ps))) := by
  classical
  have hW' : ∀ r, ∃ o' : (B R).Op, r ∈ q :: ps →
      X.I.PoisedAt (X.cfg D) r R o' ∧ ¬ (B R).ReadOnly o' := by
    intro r
    by_cases hr : r ∈ q :: ps
    · obtain ⟨o', h⟩ := hW r hr; exact ⟨o', fun _ => h⟩
    · obtain ⟨o', -⟩ := hW q List.mem_cons_self; exact ⟨o', fun h => absurd h hr⟩
  choose o ho using hW'
  have hpo : ∀ r ∈ q :: ps, X.I.PoisedAt (X.cfg D) r R (o r) := fun r hr => (ho r hr).1
  have hro : ∀ r ∈ q :: ps, ¬ (B R).ReadOnly (o r) := fun r hr => (ho r hr).2
  -- the first block of writes
  have hpoD : ∀ r ∈ ps, ∃ o', X.I.PoisedAt (X.cfg D) r R o' :=
    fun r hr => ⟨o r, hpo r (List.mem_cons_of_mem _ hr)⟩
  set es : List (P × Σ i, (B i).Op) := ps.map fun r => (r, ⟨R, o r⟩) with hes
  have hesf : es.map Prod.fst = ps := by simp [hes, Function.comp_def]
  have hess : es.map Prod.snd = (ps.map o).map (Sigma.mk R) := by simp [hes]
  obtain ⟨C₁, hr₁, hm₁, hp₁, hl₁, hk₁⟩ := runFrom_poised_block (I := X.I) (C := X.cfg D)
    (es := es) (by rw [hesf]; exact hnd) (fun e he => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 he
      exact hpo r (List.mem_cons_of_mem _ hr))
  rw [hesf] at hr₁ hl₁
  have hc₁ : X.cfg (X.ext D ps) = C₁ := by
    have := (hD.ext ps).run
    rw [ext_eq_blockWrite hD ps hnd hpoD] at this ⊢
    rw [run_append_of_eq _ hD.run, hr₁] at this
    exact (Option.some.inj this).symm
  -- the step of `q`
  obtain ⟨hqpend, kq, hqact⟩ := hpo q List.mem_cons_self
  have hnlq : X.nl D q = some (.tau q) := by
    rw [nl_of_pend hqpend]; simp [nextLabel, hqact]
  set D' := X.ext1 D q with hD'
  have hD'g : X.Good D' := hD.ext1 q
  have hsq := (hD.nl_step hnlq).1
  rw [← ext1_of_some hnlq] at hsq
  have hqact' := hqact
  obtain ⟨-, -, i₀, o₀, k₀, hact₀, hmem₀, hloc₀⟩ := step_tau hsq
  rw [hqact] at hact₀
  cases hact₀
  have hother : ∀ r, r ≠ q → (X.cfg D').loc r = (X.cfg D).loc r ∧
      (X.cfg D').pend r = (X.cfg D).pend r := fun r hr => hD.ext1_other hr
  have hpoD' : ∀ r ∈ ps, X.I.PoisedAt (X.cfg D') r R (o r) := fun r hr =>
    (hpo r (List.mem_cons_of_mem _ hr)).congr (hother r (fun h => hq (h ▸ hr))).1.symm
      (hother r (fun h => hq (h ▸ hr))).2.symm
  obtain ⟨C₂, hr₂, hm₂, hp₂, hl₂, hk₂⟩ := runFrom_poised_block (I := X.I) (C := X.cfg D')
    (es := es) (by rw [hesf]; exact hnd) (fun e he => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 he
      exact hpoD' r hr)
  rw [hesf] at hr₂ hl₂
  have hc₂ : X.cfg (X.ext D (q :: ps)) = C₂ := by
    have := (hD.ext (q :: ps)).run
    rw [ext_cons, ext_eq_blockWrite hD'g ps hnd (fun r hr => ⟨o r, hpoD' r hr⟩)] at this ⊢
    rw [run_append_of_eq _ hD'g.run, hr₂] at this
    exact (Option.some.inj this).symm
  rw [hc₁, hc₂]
  have hos : ∀ o' ∈ ps.map o, ¬ (B R).ReadOnly o' := by
    intro o' ho'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ho'
    exact hro r (List.mem_cons_of_mem _ hr)
  refine ⟨?_, fun r hr => ?_, fun r hr => ?_⟩
  · rw [hm₁, hm₂, hess, applyAccesses_map_mk, applyAccesses_map_mk]
    funext j
    by_cases hj : j = R
    · subst hj
      simp only [Function.update_self]
      exact hR.2 _ (by simpa using hne) (by simpa using hw) hos _ _
    · simp only [Function.update_of_ne hj]
      rw [hmem₀, Function.update_of_ne hj]
  · simp only [Set.mem_ofPred_eq] at hr
    by_cases hrps : r ∈ ps
    · obtain ⟨k₁, s₁, hka₁, hl₁'⟩ := hk₁ (r, ⟨R, o r⟩) (List.mem_map.2 ⟨r, hrps, rfl⟩)
      obtain ⟨k₂, s₂, hka₂, hl₂'⟩ := hk₂ (r, ⟨R, o r⟩) (List.mem_map.2 ⟨r, hrps, rfl⟩)
      simp only at hka₁ hka₂ hl₁' hl₂'
      rw [(hother r hr).1, hka₁] at hka₂
      cases hka₂
      rw [hl₁', hl₂']
      congr 1
      rcases hR.1 (o r) with hro' | hsi
      · exact absurd hro' (hro r (List.mem_cons_of_mem _ hrps))
      · exact hsi s₁ s₂
    · rw [hl₁ r hrps, hl₂ r hrps, (hother r hr).1]
  · simp only [Set.mem_ofPred_eq] at hr
    rw [hp₁, hp₂, (hother r hr).2]

/-! ### Lemma 8 and Theorem 11 -/

variable [Fintype P]

/-- **Lemma 8 and the proof of Theorem 11 of [ACHP18].** An implementation from base objects
that are window-like with window `n - 1` (`n` the number of processes) has no critical
execution. -/
theorem false_of_critical (hB : ∀ i, (B i).WindowLike (Fintype.card P - 1))
    {α : List (LLabel P)} {v v' : ℝ} {q : P} (hc : X.Critical α v q v') : False := by
  have hα := hc.1
  have hq := hc.2.1
  have hvv := hc.2.2.1
  have hv := hc.2.2.2.1
  have hv' := hc.2.2.2.2.1
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (abs_pos.2 (sub_ne_zero.2 hvv))
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hs0 := hc.nl_p₀
  have hsq : (X.nl α q).isSome := nl_isSome_of_ne hq
  have hqp : X.p₀ ∉ [q] := by simpa using Ne.symm hq
  -- `ext α [p₀, q]` is `v`-univalent
  have hvpq : X.Univ (X.ext α [X.p₀, q]) v := by
    have : X.ext α [X.p₀, q] = X.ext1 α X.p₀ ++ X.extL (X.ext1 α X.p₀) [q] := by
      rw [← ext_eq_append, ← ext_singleton, ← ext_append]; rfl
    rw [this]; exact hv.ext (by rw [← this]; exact hα.ext _)
  have hops : opsOf (X.ext α [X.p₀, q]) X.p₀ = opsOf (X.ext α [q, X.p₀]) X.p₀ ∧
      respsOf (X.ext α [X.p₀, q]) X.p₀ = respsOf (X.ext α [q, X.p₀]) X.p₀ :=
    p₀_eq_of_single (σ := []) (τ := [q]) (σ' := [q]) (τ' := []) hα (by simp) hqp hqp (by simp)
  by_cases hA : ∀ i o, X.I.PoisedAt (X.cfg α) X.p₀ i o → ∀ o', X.I.PoisedAt (X.cfg α) q i o' →
      (B i).ReadOnly o'
  · -- the step of `q` does not write the object accessed by `p₀`: `p₀` cannot distinguish
    -- `p₀(q(C))` from `q(p₀(C))`
    have ag := hα.swap' hq hsq hs0 hA
    have := hvpq.potent_of_agree (hα.ext _) (ag.symm.agree (show X.p₀ ≠ q from Ne.symm hq))
      hops.1 hops.2
    exact hvv (hv'.2 v this)
  push Not at hA
  obtain ⟨R, o, hpo, o', hpo', hro'⟩ := hA
  by_cases hRO : (B R).ReadOnly o
  · -- `p₀` reads `R`, `q` writes `R`: `q(p₀(C))` and `p₀(q(C))` are ambivalent for `q`
    have ag := hα.swap' (Ne.symm hq) hs0 hsq (fun i o₁ h₁ o₂ h₂ => by
      obtain rfl := h₁.unique hpo'
      rw [PoisedAt.op_eq h₂ hpo]; exact hRO)
    obtain ⟨N, x, m₁, m₂, hm₁, hx₁, hm₂, hx₂⟩ :=
      solo_witness (hα.ext _) (hα.ext _) hq (ag.agree (show q ≠ X.p₀ from hq)) k
    exact false_of_witness
      (hvpq.ext' (List.prefix_append _ _) ((hα.ext _).ext (List.replicate N q)))
      (hv'.ext' (List.prefix_append _ _) ((hα.ext _).ext (List.replicate N q))) hk hq
      hx₁ hm₁ hx₂ hm₂
  -- both write `R`
  have hR0 : X.Wr α X.p₀ R := ⟨o, hpo, hRO⟩
  have hRq : X.Wr α q R := ⟨o', hpo', hro'⟩
  set rs := ((Finset.univ.erase X.p₀).erase q).toList with hrs
  have hrsnd : rs.Nodup := Finset.nodup_toList _
  have hmem : ∀ r ∈ rs, r ≠ X.p₀ ∧ r ≠ q := by
    intro r hr
    simp only [hrs, Finset.mem_toList, Finset.mem_erase] at hr
    exact ⟨hr.2.1, hr.1⟩
  have hlen : rs.length + 2 = Fintype.card P := by
    have h1 : q ∈ Finset.univ.erase X.p₀ := Finset.mem_erase.2 ⟨hq, Finset.mem_univ _⟩
    have h2 := Finset.card_erase_of_mem h1
    have h3 := Finset.card_erase_of_mem (Finset.mem_univ X.p₀)
    have h4 : 0 < (Finset.univ.erase X.p₀).card := Finset.card_pos.2 ⟨q, h1⟩
    simp only [hrs, Finset.length_toList, h2, h3, Finset.card_univ] at h4 ⊢
    omega
  rcases build hα (q := q) (R := R) k rs hrsnd hmem [] (by simp) (by simp) (by simp) (by simp)
    with ⟨τ, hτ, hnτ, hwτ⟩ | ⟨σ', r, x, m, h0σ', hqσ', hnσ', hr0, hm, hx⟩
  · -- all processes are about to write `R`: the window argument
    simp only [List.nil_append] at hnτ hwτ
    have h0τ : X.p₀ ∉ τ := fun h => (hmem _ (hτ _ h)).1 rfl
    have hqτ : q ∉ τ := fun h => (hmem _ (hτ _ h)).2 rfl
    obtain ⟨c1, c2⟩ := claim9 hc hR0 hRq τ h0τ hqτ hnτ
    set D := X.ext α τ
    have hD : X.Good D := hα.ext τ
    have h0rs : X.p₀ ∉ rs := fun h => (hmem _ h).1 rfl
    have hqrs : q ∉ X.p₀ :: rs := by
      simp only [List.mem_cons, not_or]; exact ⟨hq, fun h => (hmem _ h).2 rfl⟩
    have ag := window hD (hB R) (X.p₀ :: rs) (List.nodup_cons.2 ⟨h0rs, hrsnd⟩) hqrs (by simp)
      (by simp; omega) (fun r hr => by
        rcases List.mem_cons.1 hr with rfl | hr
        · exact (hα.wr_ext_of_not_mem hqτ).2 hRq
        rcases List.mem_cons.1 hr with rfl | hr
        · exact (hα.wr_ext_of_not_mem h0τ).2 hR0
        · exact hwτ r hr)
    have hE1 : X.Univ (X.ext D (X.p₀ :: rs)) v := by
      have : X.ext D (X.p₀ :: rs) = X.ext α (τ ++ [X.p₀]) ++ X.extL (X.ext α (τ ++ [X.p₀])) rs := by
        rw [← ext_eq_append, ← ext_append, ← ext_append]; simp
      rw [this]; exact c1.ext (by rw [← this]; exact hD.ext _)
    have hE2 : X.Potent (X.ext D (q :: X.p₀ :: rs)) v := by
      obtain ⟨e1, e2⟩ := p₀_eq_of_single (σ := []) (τ := rs) (σ' := [q]) (τ' := rs) hD (by simp)
        h0rs hqp h0rs
      exact hE1.potent_of_agree (hD.ext _) (ag.agree (show X.p₀ ≠ q from Ne.symm hq))
        (by simpa using e1) (by simpa using e2)
    have hE2' : X.Univ (X.ext D (q :: X.p₀ :: rs)) v' := by
      have : X.ext D (q :: X.p₀ :: rs) =
          X.ext α (τ ++ [q, X.p₀]) ++ X.extL (X.ext α (τ ++ [q, X.p₀])) rs := by
        rw [← ext_eq_append, ← ext_append, ← ext_append]; simp
      rw [this]; exact c2.ext (by rw [← this]; exact hD.ext _)
    exact hvv (hE2'.2 v hE2)
  · -- some process completed `k + 3` operations without writing `R`
    obtain ⟨c1, c2⟩ := claim9 hc hR0 hRq σ' h0σ' hqσ' hnσ'
    have hc' : Completed (X.ext α σ') (r, m) := by
      simp only [respOf] at hx; simp only [Completed]
      exact (List.getElem?_eq_some_iff.1 hx).1
    have hx1 : respOf (X.ext α (σ' ++ [X.p₀])) (r, m) = some x := by
      rw [ext_append, ext_eq_append (X.ext α σ'), respOf_append_of_completed hc', hx]
    have hx2 : respOf (X.ext α (σ' ++ [q, X.p₀])) (r, m) = some x := by
      rw [ext_append, ext_eq_append (X.ext α σ'), respOf_append_of_completed hc', hx]
    exact false_of_witness c1 c2 hk hr0 hx1 hm hx2 hm

end Ctx

/-- **Theorem 11 of [ACHP18].** Let `n ≥ 2` processes share base objects that are window-like
with window `n - 1` (every operation is read-only or a blind write with a state-independent
response, and any `n - 1` consecutive writes determine the state: e.g. `k`-window registers for
`k ≤ n - 1`, in particular read/write registers). Then there is no implementation of the
`n`-LLAA object, with `p₀` the only process of side `0`, that is wait-free and linearizable —
even when wait-freedom and linearizability are only required for the executions in which every
process invokes `output()` of its side and `p₀` invokes it at most once (`Adm p₀`). -/
theorem theorem_11 {P ι L : Type} [Fintype P] [DecidableEq P] [DecidableEq ι] {B : ι → ObjSpec}
    (hB : ∀ i, (B i).WindowLike (Fintype.card P - 1)) (I : Impl llaaObj B P L) (p₀ p₁ : P)
    (hp : p₁ ≠ p₀) (hallow : ∀ p, I.allowed p (side p₀ p)) (hwf : I.WaitFreeOn (Adm p₀))
    (hlin : ∀ α, I.Valid α → Adm p₀ α → ∃ L, IsNLinearization llaaSpec α L) : False := by
  let X : Ctx P ι L B := ⟨I, p₀, hallow, hwf, hlin⟩
  obtain ⟨α, v, q, v', hc⟩ := X.exists_critical (p₁ := p₁) hp
  exact X.false_of_critical hB hc

/-- **Theorem 11 of [ACHP18]**, for `k`-window registers with `k ≤ n - 1` (this includes
read/write registers, `k = 1`) and the unrestricted progress and correctness conditions:
no implementation of `n`-LLAA (`n ≥ 2`) from such registers is wait-free and linearizable. -/
theorem theorem_11_window {P ι L : Type} [Fintype P] [DecidableEq P] [DecidableEq ι]
    (V : ι → Type) (w : ι → ℕ) (hw : ∀ i, w i ≤ Fintype.card P - 1)
    (I : Impl llaaObj (fun i => windowObj (V i) (w i)) P L) (p₀ p₁ : P) (hp : p₁ ≠ p₀)
    (hallow : ∀ p, I.allowed p (side p₀ p)) (hwf : I.WaitFree)
    (hlin : ∀ α, I.Valid α → ∃ L, IsNLinearization llaaSpec α L) : False :=
  theorem_11 (fun i => windowObj_windowLike (V i) (hw i)) I p₀ p₁ hp hallow
    (hwf.waitFreeOn _) (fun α hα _ => hlin α hα)

end Podc.LockFreeVsWaitFree
