import Papers.PODC2026.ConflictFreedom.Alg1Live

/-!
# Theorem 4.4: Algorithm 1 is weakly conflict-free

* Obstruction-freedom (`obstructionFree`): if a correct process eventually runs solo, then from
  some time on nobody else takes steps; the process reaches a round `B + 1` that nobody else
  ever entered, is the only participant of `GCA_{B+1}`, and by Commitment commits a trace
  containing its command, so it leaves the loop and returns.
* Weak conflict-freedom (`weakConflictFree`): suppose the execution is eventually conflict-free
  but no correct process completes all its operations. From some time `T₀` on, every operation
  is pending forever and only correct processes take steps. All correct processes go through
  round `B + 1` (`Setup.progress`). The inputs to `GCA_{B+1}` are compatible (invariant (I) of
  the paper): they are `t_q · cmd_q` with `t_q` outputs of `GCA_B` (compatible by Convergence),
  and every command that is not in the common prefix of the `t_q` belongs to an operation that has
  not completed — by Lemma A.1, because completed operations committed at rounds `≤ B` — hence to
  an operation pending at a time after `T₀`, and two such commands of distinct processes do not
  conflict since the execution is conflict-free from then on. Commitment then makes some correct
  process leave the loop and return: a contradiction (`Setup.false_of_compat`).
-/

namespace Podc.ConflictFreedom

open Cslib.SharedMemory Cslib.Mazurkiewicz Classical

namespace Alg1

variable {A : ObjSpec} {n : ℕ} [Inhabited A.Resp] [Inhabited A.Op] [NeZero n]

/-- The best round read so far (`0` outside phase `readS`). -/
def bestR (l : Loc A n) : ℕ :=
  match l.phase with
  | .readS _ best => best.1
  | _ => 0

/-- A bound on all rounds and best rounds of a configuration. -/
noncomputable def bnd (C : Cfg A n) : ℕ := Finset.univ.sup fun i => max (C.loc i).r (bestR (C.loc i))

lemma r_le_bnd (C : Cfg A n) (i : Fin n) : (C.loc i).r ≤ bnd C :=
  (le_max_left _ _).trans (Finset.le_sup (f := fun i => max (C.loc i).r (bestR (C.loc i)))
    (Finset.mem_univ i))

lemma best_le_bnd (C : Cfg A n) {i : Fin n} {j : ℕ} {best : ℕ × Tr A n}
    (h : (C.loc i).phase = .readS j best) : best.1 ≤ bnd C := by
  have : bestR (C.loc i) = best.1 := by simp [bestR, h]
  rw [← this]
  exact (le_max_right _ _).trans (Finset.le_sup (f := fun i => max (C.loc i).r (bestR (C.loc i)))
    (Finset.mem_univ i))

/-- A command of an invoked operation that has not completed is the pending operation of its
process. -/
lemma pend_of_valid {α : List (Label (Fin n) A)} {C : Cfg A n}
    (hrun : (impl (A := A) (n := n)).run α = some C) {c : Cmd A n} (hv : ValidCmd α c)
    (hnc : ¬ Completed α (opId c)) :
    C.pend c.2.1 = some c.1 ∧ c.2.2 = (respsOf α c.2.1).length + 1 := by
  have hinv := hv.invoked
  simp only [Invoked, Completed, opId] at hinv hnc
  rcases Impl.run_counts _ hrun c.2.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · omega
  · obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h1
    have hlast := Impl.run_pend _ hrun ho
    have hk : c.2.2 - 1 = (opsOf α c.2.1).length - 1 := by omega
    have hop := hv.2
    simp only [opId, opOf, hk] at hop
    rw [List.getLast?_eq_getElem?] at hlast
    rw [hlast] at hop
    refine ⟨by rw [ho, hop], by have := hv.1; omega⟩

/-- Theorem 4.4 of [KST26], part (1): Algorithm 1 is obstruction-free. -/
theorem obstructionFree : ObstructionFreeP (impl (A := A) (n := n)) := by
  intro e p n₀ hc hp ⟨τ, hsolo⟩
  set T₀ := max n₀ τ
  have hpT : PendingFrom e p T₀ := fun m hm => hp m (le_of_max_le_left hm)
  have hS : Setup e (· = p) T₀ (bnd (e.cfg T₀)) :=
    ⟨fun q hq => hq ▸ hpT, fun q hq => hq ▸ hc.takesInfSteps hp,
      fun i hi m hm hs => by rw [hsolo m (le_of_max_le_right hm) hs]; exact Ne.symm hi,
      r_le_bnd _, fun i j best h => best_le_bnd _ h⟩
  refine hS.false_of_compat ⟨p, rfl⟩ fun t ht hall => ?_
  obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.1 (hall p rfl)
  have hI := (inv_at e t).1
  refine ⟨g.inp, ?_⟩
  rintro x ⟨j, l, hl, rfl⟩
  rw [gst_loc] at hl
  by_cases hj : j = p
  · subst hj; rw [hI.locAt_of_hist hg] at hl; cases hl; exact le_rfl
  · rw [hS.none_out hj ht] at hl; cases hl

/-- Invariant (I) of the proof of Theorem 4.4: in an execution that is conflict-free from `T₀`
on, once every process of `Q` has completed `GCA_{B+1}`, the inputs of `GCA_{B+1}` are
compatible. -/
theorem Setup.compat_round {e : (impl (A := A) (n := n)).InfExec} {Q : Fin n → Prop} {T₀ B : ℕ}
    (hS : Setup e Q T₀ B)
    (hecf : ∀ m ≥ T₀, ∀ p q, p ≠ q → ∀ o o', (e.cfg m).pend p = some o →
      (e.cfg m).pend q = some o' → ¬ A.Conflicting o o')
    {t : ℕ} (ht : T₀ ≤ t) (hall : ∀ q, Q q → ((e.cfg t).loc q).hist (B + 1) ≠ none) :
    Compat (GCA.inputs (gst (e.cfg t) (B + 1))) := by
  obtain ⟨hI, hJ, hK⟩ := inv_at e t
  haveI : Nonempty (GCA.Loc n (Tr A n)) := ⟨GCA.Loc.init ⊥⟩
  choose! gq hgq using fun q (hq : Q q) => Option.ne_none_iff_exists'.1 (hall q hq)
  set cq : Fin n → Cmd A n := fun q => ((e.cfg T₀).loc q).cmd with hcq
  choose! t0 ht0 using fun q (hq : Q q) =>
    (hS.qstate hq ht).inp (gq q) (hI.locAt_of_hist (hgq q hq))
  set J := Finset.univ.filter Q with hJdef
  -- every input is one of the `t0 q · cq q`
  have hinputs : ∀ x ∈ GCA.inputs (gst (e.cfg t) (B + 1)), ∃ q ∈ J, x = (t0 q).snoc (cq q) := by
    rintro x ⟨j, l, hl, rfl⟩
    rw [gst_loc] at hl
    by_cases hj : Q j
    · rw [hI.locAt_of_hist (hgq j hj)] at hl; simp only [Option.some.injEq] at hl; subst hl
      exact ⟨j, by simp [hJdef, hj], (ht0 j hj).2⟩
    · rw [hS.none_out hj ht] at hl; cases hl
  by_cases hJne : J.Nonempty
  swap
  · refine ⟨⊥, fun x hx => ?_⟩
    obtain ⟨q, hq, -⟩ := hinputs x hx
    exact absurd ⟨q, hq⟩ hJne
  set g0 := J.inf' hJne t0 with hg0
  -- the bases are compatible (Convergence of `GCA_B`)
  obtain ⟨z0, hz0⟩ := GCA.convergence_of_reach (hI.reach B)
  have hc : ∃ z, ∀ q ∈ J, t0 q ≤ z := by
    refine ⟨z0, fun q hq => ?_⟩
    have hq' : Q q := by simpa [hJdef] using hq
    rcases (ht0 q hq').1 with ⟨-, h⟩ | ⟨-, ⟨i, g, hg, hpc, hout⟩⟩
    · rw [h]; exact bot_le
    · exact hz0 _ ⟨i, g, ⟨by simpa [gst_loc] using hg, hpc⟩, hout.symm⟩
  have hg : ∀ q ∈ J, g0 ≤ t0 q := fun q hq => Finset.inf'_le _ hq
  -- commands outside the common prefix belong to pending operations
  have key : ∀ x, (∃ q ∈ J, x ∈ (t0 q).supp ∧ x ∉ g0.supp) ∨
      (∃ q ∈ J, cq q ∉ (t0 q).supp ∧ x = cq q) →
      ValidCmd (e.pre t) x ∧ ¬ Completed (e.pre t) (opId x) := by
    intro x hx
    have hxg : x ∉ g0.supp := by
      rcases hx with ⟨q, hq, -, h⟩ | ⟨q, hq, h1, rfl⟩
      · exact h
      · exact fun h' => h1 (NTrace.supp_mono (hg q hq) h')
    obtain ⟨q, hq, hxq⟩ : ∃ q ∈ J, x ∈ ((t0 q).snoc (cq q)).supp := by
      rcases hx with ⟨q, hq, h, -⟩ | ⟨q, hq, -, rfl⟩
      · exact ⟨q, hq, by rw [NTrace.supp_snoc]; exact Finset.mem_insert_of_mem h⟩
      · exact ⟨q, hq, by rw [NTrace.supp_snoc]; exact Finset.mem_insert_self _ _⟩
    have hq' : Q q := by simpa [hJdef] using hq
    have hv : ValidCmd (e.pre t) x :=
      (hK.known (B + 1) q (gq q) (hI.locAt_of_hist (hgq q hq')) x
        (by rw [(ht0 q hq').2]; exact hxq)).1
    refine ⟨hv, fun hcomp => hxg ?_⟩
    obtain ⟨t', o, hcom, hop, hmem, -⟩ := isCom_of_completed hI hK hcomp
    have hox : ((o, (opId x).1, (opId x).2 + 1) : Cmd A n) = x := by
      have : o = x.1 := by rw [hv.2] at hop; exact (Option.some.inj hop).symm
      have hk1 : 1 ≤ x.2.2 := hv.1
      obtain ⟨o', i, k⟩ := x
      simp only [opId] at this hk1 ⊢
      rw [this, Nat.sub_add_cancel hk1]
    rw [hox] at hmem
    obtain ⟨-, -, -, -, hcrS, -⟩ := (hK.at_ (opId x).1).compl (opId x).2 hcomp
    have hcrB : crOf (e.cfg t) (opId x) ≤ B := hcrS.trans (hS.S_le ht _)
    have hcr1 : 1 ≤ crOf (e.cfg t) (opId x) := by
      obtain ⟨i, g, hg', -⟩ := hcom; exact hI.one_le_of_locAt hg'
    have hle : t' ≤ g0 := by
      refine Finset.le_inf' hJne t0 fun q hq => ?_
      have hq' : Q q := by simpa [hJdef] using hq
      rcases (ht0 q hq').1 with ⟨h1, -⟩ | ⟨-, hout⟩
      · omega
      · exact lemma_A1' hI hJ hcom hcrB (by simpa using hout)
    exact NTrace.supp_mono hle hmem
  obtain ⟨z, hz⟩ := NTrace.compat_snoc J t0 cq g0 hc hg (by
    intro a ha b hb hab hconf
    have mem_key : ∀ x ∈ (J.biUnion fun j => (t0 j).supp \ g0.supp) ∪
        (J.filter fun j => cq j ∉ (t0 j).supp).image cq,
        ValidCmd (e.pre t) x ∧ ¬ Completed (e.pre t) (opId x) := by
      intro x hx
      apply key
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_image,
        Finset.mem_filter] at hx
      rcases hx with ⟨q, hq, h1, h2⟩ | ⟨q, ⟨hq, h1⟩, rfl⟩
      · exact Or.inl ⟨q, hq, h1, h2⟩
      · exact Or.inr ⟨q, hq, h1, rfl⟩
    obtain ⟨hva, hca⟩ := mem_key a ha
    obtain ⟨hvb, hcb⟩ := mem_key b hb
    obtain ⟨hpa, hia⟩ := pend_of_valid (e.run_pre t) hva hca
    obtain ⟨hpb, hib⟩ := pend_of_valid (e.run_pre t) hvb hcb
    have hown : a.2.1 ≠ b.2.1 := by
      intro he
      apply hab
      have h1 : a.1 = b.1 := by rw [he, hpb] at hpa; exact (Option.some.inj hpa).symm
      have h2 : a.2.2 = b.2.2 := by rw [hia, hib, he]
      obtain ⟨o, i, k⟩ := a
      obtain ⟨o', i', k'⟩ := b
      simp only at h1 h2 he
      rw [h1, he, h2]
    exact hecf t ht _ _ hown _ _ hpa hpb hconf)
  refine ⟨z, fun x hx => ?_⟩
  obtain ⟨q, hq, rfl⟩ := hinputs x hx
  exact hz q hq

/-- Theorem 4.4 of [KST26], part (2): in every eventually conflict-free infinite execution of
Algorithm 1, some correct process completes all of its operations. -/
theorem progress_of_eventuallyConflictFree (e : (impl (A := A) (n := n)).InfExec)
    (hecf : EventuallyConflictFree e) : ∃ p, Correct e p ∧ CompletesAll e p := by
  by_contra hno
  push Not at hno
  obtain ⟨τ, hτ⟩ := hecf
  -- from some time on every process is pending forever, and faulty processes take no steps
  have hT : ∀ p, ∃ m, PendingFrom e p m ∧
      (¬ Correct e p → ∀ m' ≥ m, (e.lbl m').IsStep → (e.lbl m').proc ≠ p) := by
    intro p
    by_cases hp : Correct e p
    · have := hno p hp
      simp only [CompletesAll, not_forall, not_not] at this
      obtain ⟨m, hm⟩ := this
      exact ⟨m, hm, fun h => absurd hp h⟩
    · have hp' := hp
      simp only [Correct, TakesInfSteps, not_or, not_forall, not_exists, not_and] at hp'
      obtain ⟨⟨N, hN⟩, hidle⟩ := hp'
      obtain ⟨m, hm, hpm⟩ := hidle N
      refine ⟨max m N, fun m' hm' hnone => ?_, fun _ m' hm' hs hpr => hN m' (by omega) hs hpr⟩
      obtain ⟨t, ht1, -, r, hr⟩ := e.exists_ret_between (show m ≤ m' by omega) hpm hnone
      exact hN t (by omega) (by rw [hr]; trivial) (by rw [hr]; rfl)
  choose mp hmp using hT
  set T₀ := max τ (Finset.univ.sup mp) with hT₀
  have hmpT : ∀ p, mp p ≤ T₀ := fun p =>
    (Finset.le_sup (f := mp) (Finset.mem_univ p)).trans (le_max_right _ _)
  have hpendT : ∀ p, PendingFrom e p T₀ := fun p m hm => (hmp p).1 m ((hmpT p).trans hm)
  have hS : Setup e (Correct e) T₀ (bnd (e.cfg T₀)) :=
    ⟨fun q _ => hpendT q, fun q hq => hq.takesInfSteps (hpendT q),
      fun i hi m hm hs => (hmp i).2 hi m ((hmpT i).trans hm) hs,
      r_le_bnd _, fun i j best h => best_le_bnd _ h⟩
  obtain ⟨p, hp⟩ := exists_takesInfSteps e
  exact hS.false_of_compat ⟨p, Or.inl hp⟩ fun t ht hall =>
    hS.compat_round (fun m hm => hτ m (le_of_max_le_left hm)) ht hall

/-- Theorem 4.4 of [KST26]: Algorithm 1 (with Algorithm 2 implementing every `GCA_r`) is weakly
conflict-free. -/
theorem weakConflictFree : WeakConflictFree (impl (A := A) (n := n)) :=
  ⟨obstructionFree, progress_of_eventuallyConflictFree⟩

end Alg1

end Podc.ConflictFreedom
