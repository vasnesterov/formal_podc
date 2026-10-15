import Cslib.Computability.Distributed.SharedMemory.Valency

/-!
# Read and test-and-set: Lemma 9.1 and Theorem 9.2 of EGSZ'16

Ellen, Gelashvili, Shavit, Zhu, *A Complexity-Based Hierarchy for Multiprocessor
Synchronization*, PODC 2016, Section 9: for `n ≥ 3` processes, obstruction-free binary consensus
cannot be solved with finitely many memory locations supporting only `read()` and
`test-and-set()`.

## Model

* `tasLoc`: a location with value in `ℕ`; `read()` returns the value; `test-and-set()` returns the
  old value and sets the location to `1` if it was `0` (otherwise leaves it unchanged). The memory
  is `B := fun _ : ι => tasLoc` for a finite type `ι` of locations; initial values are arbitrary
  (`Impl.memInit`).
* Binary consensus algorithms `I : Impl BinCons B P L` (see `Cslib/Computability/Distributed/SharedMemory/Valency.lean`), with
  weak validity (`weakConsensus`) and one-shot obstruction-freedom (`OneShotOF`) — both weaker
  than the paper's assumptions.

Key facts about this memory: a nonzero location stays nonzero forever (`step_mem_ne_zero`), and a
step that is not a test-and-set on a location with value `0` does not change the memory
(`soloStep_mem_eq`).

## Main results

* `exists_more_nonzero`: one round of the proof of Lemma 9.1.
* `lemma_9_1` (**Lemma 9.1**): if all processes are bivalent from a reachable configuration, then
  for every `k` an execution reaches a configuration from which all processes are bivalent and in
  which at least `k` locations are nonzero.
* `theorem_9_2` (**Theorem 9.2**): there is no such algorithm for a finite set of locations.

## The gap in the paper's proof of Lemma 9.1, and its repair

Let `L` be the set of nonzero locations after `α_k ξ` (where `ξ` is given by Lemma 6.6: `p₀`
decides `0` and `p₁` decides `1` in their solo runs), and let `z ∉ {p₀, p₁}`. The paper lets `β` be
the shortest prefix of `z`'s solo execution `δ` from `Cα_kξ` ending with a test-and-set on a
location `r ∉ L`, and then argues about the configurations `Cα_kξψβ` and `Cα_kξψψ'β`, where `ψ, ψ'`
are steps of `p₀`/`p₁`. But the preliminary steps of `z` in `β` (reads, and test-and-sets on
locations of `L`) may return different values after `ψ` (which may have set locations to `1`) or
after `ψ'` (which may be a test-and-set on `r`), so `z` need not behave as in `β` there: the
configurations the paper reasons about are not well defined in general.

**Repair.** First run `z`'s preliminary steps `β⁻` (they change no memory, so `D' := Cα_kξβ⁻`
agrees with `Cα_kξ` on `p₀`, `p₁` and the memory); now `z` is *poised* at `D'` to perform its
test-and-set `τ_z` on `r` (with value `0`). Then:

* if `z` returns before poising on such a location, its solo run changed no memory, hence is
  invisible to `p₀`, `p₁`, and the one of them deciding the opposite of `z`'s decision violates
  agreement;
* if `{p₀, p₁}` is bivalent from `D'τ_z`, we are done (`r` is now nonzero);
* otherwise there are `a ≠ b` in `{p₀, p₁}` and `x` such that `a` decides `x` from `D'τ_z` and `b`
  decides `!x` from `D'` (solo). Let `ψ` be the longest prefix of `b`'s solo run `γ` from `D'` such
  that `a` still decides `x` from `D'ψτ_z` (the full run does not qualify, by agreement), and let
  `ψ'` be `b`'s next step. Then `a` decides `!x` from `D'ψψ'τ_z`. Instead of the paper's case
  analysis on `ψ'`, we observe that **`τ_z` (a test-and-set) commutes with any single step of `b`
  as far as `a` and the memory are concerned** (`soloStep_comm_agree`: test-and-set is idempotent,
  reads do not change memory, steps on different locations commute). Hence `D'ψψ'τ_z` and
  `D'ψτ_zψ'` agree on `a` and on the memory, so `a` decides `!x` from `D'ψτ_zψ'` and `x` from
  `D'ψτ_z`: `{a, b}` is bivalent from `D'ψτ_z`, which has `r` and all of `L` nonzero.

So the lemma and the theorem are correct; only the proof needed this repair. We prove the
statement "at least `k` nonzero locations" (the paper: "`k` locations have been set to `1`"),
which also holds for arbitrary initial memory contents.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory Impl

/-- Primitives of a test-and-set location. -/
inductive TasOp
  /-- `read()`: return the value. -/
  | read
  /-- `test-and-set()`: return the old value; set the location to `1` if it was `0`. -/
  | tas
  deriving DecidableEq

/-- Transition function of a test-and-set location. -/
def tasδ : ℕ → TasOp → ℕ × ℕ
  | s, .read => (s, s)
  | s, .tas => (if s = 0 then 1 else s, s)

@[simp] lemma tasδ_read (s : ℕ) : tasδ s .read = (s, s) := rfl

@[simp] lemma tasδ_tas (s : ℕ) : tasδ s .tas = (if s = 0 then 1 else s, s) := rfl

/-- A memory location supporting `read()` and `test-and-set()`. -/
abbrev tasLoc : ObjSpec where
  State := ℕ
  Op := TasOp
  Resp := ℕ
  init := 0
  δ := tasδ

variable {ι P L : Type} [DecidableEq P] [DecidableEq ι]
  {I : Impl BinCons (fun _ : ι => tasLoc) P L}

lemma step_mem_ne_zero {C C' : Config BinCons (fun _ : ι => tasLoc) P L} {ℓ : Label P BinCons}
    (h : I.step C ℓ = some C') {i : ι} (hi : C.mem i ≠ 0) : C'.mem i ≠ 0 := by
  cases ℓ with
  | inv p o => rw [(step_inv h).2.2.2.2]; exact hi
  | ret p r => rw [(step_ret h).2.2.1]; exact hi
  | tau p =>
    obtain ⟨-, -, j, o, k, -, hm, -⟩ := step_tau h
    rw [hm]
    by_cases hij : i = j
    · subst hij
      cases o <;> simp [hi]
    · simp [Function.update_of_ne hij, hi]

lemma runFrom_mem_ne_zero {C C' : Config BinCons (fun _ : ι => tasLoc) P L}
    {β : List (Label P BinCons)} (h : I.runFrom C β = some C') {i : ι} (hi : C.mem i ≠ 0) :
    C'.mem i ≠ 0 := by
  induction β generalizing C with
  | nil => simp only [runFrom_nil, Option.some.injEq] at h; subst h; exact hi
  | cons ℓ β ih =>
    simp only [runFrom_cons] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      exact ih h (step_mem_ne_zero hs hi)

lemma reachBy_mem_ne_zero {Q : Set P} {C C' : Config BinCons (fun _ : ι => tasLoc) P L}
    (h : I.ReachBy Q C C') {i : ι} (hi : C.mem i ≠ 0) : C'.mem i ≠ 0 := by
  obtain ⟨β, -, h⟩ := h; exact runFrom_mem_ne_zero h hi

/-- The set of nonzero locations. -/
def nzSet [Fintype ι] (C : Config BinCons (fun _ : ι => tasLoc) P L) : Finset ι :=
  Finset.univ.filter (fun i => C.mem i ≠ 0)

lemma reachBy_nzSet_subset [Fintype ι] {Q : Set P} {C C' : Config BinCons (fun _ : ι => tasLoc) P L}
    (h : I.ReachBy Q C C') : nzSet C ⊆ nzSet C' := by
  intro i hi
  simp only [nzSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact reachBy_mem_ne_zero h hi

lemma soloStep_of_pend_none {W : Config BinCons (fun _ : ι => tasLoc) P L} {p : P}
    (hp : W.pend p = none) : I.soloStep p W = W := by
  simp [soloStep, hp]

lemma soloStep_access {W : Config BinCons (fun _ : ι => tasLoc) P L} {p : P}
    (hp : W.pend p ≠ none) {i : ι} {o : TasOp} {k : ℕ → L}
    (hact : I.act p (W.loc p) = .access i o k) :
    I.soloStep p W = { W with mem := Function.update W.mem i (tasδ (W.mem i) o).1,
                              loc := Function.update W.loc p (k (tasδ (W.mem i) o).2) } := by
  simp [soloStep, nextLabel, hp, hact, step]

lemma soloStep_ret {W : Config BinCons (fun _ : ι => tasLoc) P L} {p : P}
    (hp : W.pend p ≠ none) {r : Bool} {l : L} (hact : I.act p (W.loc p) = .ret r l) :
    I.soloStep p W = { W with pend := Function.update W.pend p none,
                              loc := Function.update W.loc p l } := by
  simp [soloStep, nextLabel, hp, hact, step]

lemma soloStep_mem_eq {W : Config BinCons (fun _ : ι => tasLoc) P L} {p : P}
    (h : ∀ i k, I.act p (W.loc p) = .access i TasOp.tas k → W.mem i ≠ 0) :
    (I.soloStep p W).mem = W.mem := by
  by_cases hp : W.pend p = none
  · simp [soloStep, hp]
  cases hact : I.act p (W.loc p) with
  | access i o k =>
    rw [soloStep_access hp hact]
    cases o with
    | read => simp
    | tas => simp [h i k hact]
  | ret r l => rw [soloStep_ret hp hact]

lemma soloStep_tas_ne_zero {W : Config BinCons (fun _ : ι => tasLoc) P L} {p : P}
    (hp : W.pend p ≠ none) {r : ι} {k : ℕ → L} (hact : I.act p (W.loc p) = .access r TasOp.tas k) :
    (I.soloStep p W).mem r ≠ 0 := by
  rw [soloStep_access hp hact]
  simp only [Function.update_self, tasδ_tas]
  split_ifs <;> omega

/-- The step of `z` (a test-and-set on `r`) and any step of `b` commute, as far as the memory and
the other processes are concerned. -/
lemma soloStep_comm_agree {W : Config BinCons (fun _ : ι => tasLoc) P L} {z b a : P} (hzb : z ≠ b)
    (haz : a ≠ z) (hab : a ≠ b) (hz : W.pend z ≠ none) {r : ι} {k : ℕ → L}
    (hzact : I.act z (W.loc z) = .access r TasOp.tas k) :
    AgreeOn {a} (I.soloStep z (I.soloStep b W)) (I.soloStep b (I.soloStep z W)) := by
  by_cases hb : W.pend b = none
  · have e1 : I.soloStep b W = W := soloStep_of_pend_none hb
    have e2 : I.soloStep b (I.soloStep z W) = I.soloStep z W := by
      have : (I.soloStep z W).pend b = none := by
        rw [(soloStep_other (I := I) (Ne.symm hzb) W).2]; exact hb
      exact soloStep_of_pend_none this
    rw [e1, e2]; exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  cases hbact : I.act b (W.loc b) with
  | access i o k' =>
    rw [soloStep_access hb hbact, soloStep_access hz hzact]
    rw [soloStep_access (p := z) (i := r) (o := .tas) (k := k) ?h1 ?h2,
      soloStep_access (p := b) (i := i) (o := o) (k := k') ?h3 ?h4]
    case h1 => exact hz
    case h2 => simpa [Function.update_of_ne hzb] using hzact
    case h3 => exact hb
    case h4 => simpa [Function.update_of_ne (Ne.symm hzb)] using hbact
    refine ⟨?_, fun q hq => ?_, fun q hq => rfl⟩
    · funext j
      simp only [Function.update_apply]
      by_cases hjr : j = r <;> by_cases hji : j = i <;> by_cases hir : i = r
      all_goals (try subst hjr)
      all_goals (try subst hji)
      all_goals (cases o <;> simp_all)
    · rw [Set.mem_singleton_iff] at hq; subst hq
      simp [Function.update_of_ne haz, Function.update_of_ne hab]
  | ret v l =>
    rw [soloStep_ret hb hbact, soloStep_access hz hzact]
    rw [soloStep_access (p := z) (i := r) (o := .tas) (k := k) ?h1 ?h2,
      soloStep_ret (p := b) (r := v) (l := l) ?h3 ?h4]
    case h1 => simpa [Function.update_of_ne hzb] using hz
    case h2 => simpa [Function.update_of_ne hzb] using hzact
    case h3 => exact hb
    case h4 => simpa [Function.update_of_ne (Ne.symm hzb)] using hbact
    refine ⟨rfl, fun q hq => ?_, fun q hq => ?_⟩
    · rw [Set.mem_singleton_iff] at hq; subst hq
      simp [Function.update_of_ne haz, Function.update_of_ne hab]
    · simp only [Set.mem_singleton_iff] at hq; subst hq
      simp [Function.update_of_ne hab]

section Main

variable [Fintype P] [Fintype ι]

/-- One round of the (repaired) proof of Lemma 9.1: from a reachable configuration from which all
processes are bivalent, an execution reaches a configuration from which all processes are still
bivalent and strictly more locations are nonzero. -/
theorem exists_more_nonzero (hS : I.Solves (weakConsensus P Bool)) (hof : I.OneShotOF)
    (hn : 3 ≤ Fintype.card P) {C : Config BinCons (fun _ : ι => tasLoc) P L} (hC : I.Reach C)
    (hb : I.Bivalent Set.univ C) :
    ∃ C', I.ReachBy Set.univ C C' ∧ I.Bivalent Set.univ C' ∧
      (nzSet C).card < (nzSet C').card := by
  classical
  -- solo runs are executions
  have hsolo : ∀ (p : P) (W : Config BinCons (fun _ : ι => tasLoc) P L) (j : ℕ),
      I.ReachBy Set.univ W ((I.soloStep p)^[j] W) := fun p W j =>
    ⟨_, (I.soloLabels_steps p W j).mono (Set.subset_univ _), I.runFrom_soloLabels p W j⟩
  have hsolo1 : ∀ (p : P) (W : Config BinCons (fun _ : ι => tasLoc) P L),
      I.ReachBy Set.univ W (I.soloStep p W) := fun p W => hsolo p W 1
  -- Lemma 6.6: two processes deciding differently
  obtain ⟨D, hCD, p₀, -, p₁, -, hd₀, hd₁⟩ :=
    hC.exists_two_deciders hS hof Finset.univ (by simpa using hb)
  have hCD : I.ReachBy Set.univ C D := by simpa using hCD
  have hD : I.Reach D := hC.reachBy hCD
  have hne : p₀ ≠ p₁ := by
    rintro rfl; have := hD.canDecide_self_unique hd₀ hd₁; simp at this
  have hpendD : ∀ q, D.pend q ≠ none :=
    hD.pend_of_bivalent hS (bivalent_of_canDecide (Q := Set.univ) trivial trivial hd₀ hd₁)
  obtain ⟨z, hz0, hz1⟩ : ∃ z, z ≠ p₀ ∧ z ≠ p₁ := by
    by_contra hc
    push Not at hc
    have hsub : (Finset.univ : Finset P) ⊆ {p₀, p₁} := by
      intro x _
      by_cases hx : x = p₀
      · simp [hx]
      · simp [hc x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Finset.card_pair hne] at this; omega
  -- how a round ends
  have hfinal : ∀ (F : Config BinCons (fun _ : ι => tasLoc) P L) (r : ι),
      I.ReachBy Set.univ D F → D.mem r = 0 → F.mem r ≠ 0 → I.Bivalent Set.univ F →
      ∃ C', I.ReachBy Set.univ C C' ∧ I.Bivalent Set.univ C' ∧
        (nzSet C).card < (nzSet C').card := by
    intro F r hDF hr0 hr1 hbF
    refine ⟨F, hCD.trans hDF, hbF, ?_⟩
    have h1 := Finset.card_le_card (reachBy_nzSet_subset hCD)
    have h2 : nzSet D ⊂ nzSet F := (Finset.ssubset_iff_of_subset (reachBy_nzSet_subset hDF)).2
      ⟨r, by simp [nzSet, hr1], by simp [nzSet, hr0]⟩
    have := Finset.card_lt_card h2
    omega
  -- `z` runs solo until it is poised to test-and-set a location that is `0`
  obtain ⟨α, hα, h1α, -⟩ := id hD
  have hfin := hof α D z hα h1α (hpendD z)
  obtain ⟨m, hbefore, hstop⟩ := I.exists_solo_until z D
    (fun a => ∃ i k, a = Action.access i TasOp.tas k ∧ D.mem i = 0) hfin
  set D' := (I.soloStep z)^[m] D with hD'def
  have hmem : ∀ j ≤ m, ((I.soloStep z)^[j] D).mem = D.mem := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', soloStep_mem_eq, ih (by omega)]
      intro i k hact hi0
      exact (hbefore j (by omega)).2 ⟨i, k, hact, by rw [← ih (by omega)]; exact hi0⟩
  have hD'mem : D'.mem = D.mem := hmem m le_rfl
  have hD'other : ∀ q, q ≠ z → D'.loc q = D.loc q ∧ D'.pend q = D.pend q := fun q hq =>
    I.iterate_soloStep_other hq D m
  have hag : ∀ q, q ≠ z → AgreeOn {q} D D' := fun q hq =>
    ⟨hD'mem.symm,
      fun q' hq' => by
        simp only [Set.mem_singleton_iff] at hq'; rw [hq']; exact (hD'other q hq).1.symm,
      fun q' hq' => by
        simp only [Set.mem_singleton_iff] at hq'; rw [hq']; exact (hD'other q hq).2.symm⟩
  have hd₀' : I.CanDecide {p₀} D' false := canDecide_of_agreeOn (hag p₀ (Ne.symm hz0)) hd₀
  have hd₁' : I.CanDecide {p₁} D' true := canDecide_of_agreeOn (hag p₁ (Ne.symm hz1)) hd₁
  have hD'R : I.ReachBy Set.univ D D' := hsolo z D m
  have hD'Reach : I.Reach D' := hD.reachBy hD'R
  have hrunz : I.runFrom D (I.soloLabels z D m) = some D' := I.runFrom_soloLabels z D m
  by_cases hret : D'.pend z = none
  · -- `z` decided without changing the memory: contradiction with agreement
    exfalso
    have hc := I.runFrom_counts hrunz z 1 0 (Or.inr ⟨hpendD z, rfl⟩)
    rw [I.opsOf_soloLabels] at hc
    simp only [hret, List.length_nil, Nat.add_zero, Nat.zero_add, true_and, ne_eq,
      not_true_eq_false, false_and, or_false] at hc
    obtain ⟨u, hu⟩ : ∃ u, u ∈ respsOf (I.soloLabels z D m) z := by
      match h : respsOf (I.soloLabels z D m) z with
      | [] => rw [h] at hc; simp at hc
      | x :: _ => exact ⟨x, by simp⟩
    have hnu : I.CanDecide Set.univ D' (!u) := by
      cases u
      · exact hd₁'.mono (Set.subset_univ _)
      · exact hd₀'.mono (Set.subset_univ _)
    have := hD.decides_canDecide_eq hS (I.soloLabels_steps z D m) hrunz
      ⟨z, mem_respsOf_iff.1 hu⟩ hnu
    cases u <;> simp at this
  obtain ⟨r, k, hact, hr0⟩ := hstop.resolve_left hret
  -- `E` = after `z`'s test-and-set on `r`
  set E := I.soloStep z D' with hEdef
  have hE : I.ReachBy Set.univ D E := hD'R.trans (hsolo1 z D')
  have hEr : E.mem r ≠ 0 := soloStep_tas_ne_zero hret hact
  have hER : I.Reach E := hD.reachBy hE
  have hpendE : ∀ q, q ≠ z → E.pend q ≠ none := fun q hq => by
    rw [(soloStep_other (I := I) hq D').2, (hD'other q hq).2]; exact hpendD q
  -- the core argument
  have key : ∀ a b x, a ≠ z → b ≠ z → a ≠ b → I.CanDecide {a} E x →
      I.CanDecide {b} D' (!x) → ∃ C', I.ReachBy Set.univ C C' ∧ I.Bivalent Set.univ C' ∧
        (nzSet C).card < (nzSet C').card := by
    intro a b x haz hbz hab haE hbD'
    have hWo : ∀ q, q ≠ b → ∀ j, ((I.soloStep b)^[j] D').loc q = D'.loc q ∧
        ((I.soloStep b)^[j] D').pend q = D'.pend q := fun q hq j =>
      I.iterate_soloStep_other hq D' j
    have hpzW : ∀ j, ((I.soloStep b)^[j] D').pend z ≠ none := fun j => by
      rw [(hWo z hbz.symm j).2]; exact hret
    have hactW : ∀ j, I.act z (((I.soloStep b)^[j] D').loc z) = .access r TasOp.tas k :=
      fun j => by rw [(hWo z hbz.symm j).1]; exact hact
    have hRW : ∀ j, I.ReachBy Set.univ D (I.soloStep z ((I.soloStep b)^[j] D')) := fun j =>
      (hD'R.trans (hsolo b D' j)).trans (hsolo1 z _)
    let G : ℕ → Prop := fun j => I.CanDecide {a} (I.soloStep z ((I.soloStep b)^[j] D')) x
    have hG0 : G 0 := haE
    have hpb : D'.pend b ≠ none := by rw [(hD'other b hbz).2]; exact hpendD b
    obtain ⟨α', hα', h1α', -⟩ := id hD'Reach
    obtain ⟨K, hK⟩ := hof α' D' b hα' h1α' hpb
    have hGK : ¬ G K := by
      intro hG
      have hrun := I.runFrom_soloLabels b D' K
      have hc := I.runFrom_counts hrun b 1 0 (Or.inr ⟨hpb, rfl⟩)
      rw [I.opsOf_soloLabels] at hc
      simp only [hK, List.length_nil, Nat.add_zero, Nat.zero_add, true_and, ne_eq,
        not_true_eq_false, false_and, or_false] at hc
      obtain ⟨y, hy⟩ : ∃ y, y ∈ respsOf (I.soloLabels b D' K) b := by
        match h : respsOf (I.soloLabels b D' K) b with
        | [] => rw [h] at hc; simp at hc
        | x :: _ => exact ⟨x, by simp⟩
      have hyx : y = !x := hD'Reach.canDecide_self_unique
        ⟨_, _, I.soloLabels_steps b D' K, hrun, b, mem_respsOf_iff.1 hy⟩ hbD'
      have := hD'Reach.decides_canDecide_eq hS (Q := Set.univ)
        (β := I.soloLabels b D' K ++ I.soloLabels z ((I.soloStep b)^[K] D') 1)
        (((I.soloLabels_steps b D' K).mono (Set.subset_univ _)).append
          ((I.soloLabels_steps z _ 1).mono (Set.subset_univ _)))
        (by rw [I.runFrom_append_of_eq hrun, I.runFrom_soloLabels]; rfl)
        ⟨b, List.mem_append_left _ (mem_respsOf_iff.1 hy)⟩ hG
      subst hyx; cases x <;> simp at this
    have hGm : G (Nat.findGreatest G K) :=
      Nat.findGreatest_spec (P := G) (m := 0) (Nat.zero_le _) hG0
    set m' := Nat.findGreatest G K with hm'def
    have hm'K : m' < K := lt_of_le_of_ne (Nat.findGreatest_le K) (fun e => hGK (e ▸ hGm))
    have hGm1 : ¬ G (m' + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hm'K
    have hstep : (I.soloStep b)^[m' + 1] D' = I.soloStep b ((I.soloStep b)^[m'] D') :=
      Function.iterate_succ_apply' _ _ _
    set Wm := (I.soloStep b)^[m'] D' with hWm
    set F := I.soloStep z Wm with hF
    have hF' : I.CanDecide {a} (I.soloStep z (I.soloStep b Wm)) (!x) := by
      have hR : I.Reach (I.soloStep z (I.soloStep b Wm)) :=
        hD.reachBy (by rw [← hstep]; exact hRW _)
      have hpa : (I.soloStep z (I.soloStep b Wm)).pend a ≠ none := by
        rw [(soloStep_other (I := I) haz _).2, (soloStep_other (I := I) hab _).2, (hWo a hab m').2,
          (hD'other a haz).2]
        exact hpendD a
      have hng : ¬ I.CanDecide {a} (I.soloStep z (I.soloStep b Wm)) x := by
        rw [← hstep]; exact hGm1
      exact hR.canDecide_not_of_canDecide hof hpa (Set.mem_singleton a) hng
    have hcomm := soloStep_comm_agree (I := I) (W := Wm) hbz.symm haz hab (hpzW m') (hactW m')
    have h2 : I.CanDecide Set.univ F (!x) := CanDecide.of_reachBy (hsolo1 b F)
      ((canDecide_of_agreeOn hcomm hF').mono (Set.subset_univ _))
    have h1 : I.CanDecide Set.univ F x := hGm.mono (Set.subset_univ _)
    exact hfinal F r (hRW m') hr0 (soloStep_tas_ne_zero (hpzW m') (hactW m'))
      (bivalent_of_canDecide_not h1 h2)
  obtain ⟨x₀, h₀E⟩ := hER.exists_canDecide_self hof (hpendE p₀ (Ne.symm hz0))
  obtain ⟨x₁, h₁E⟩ := hER.exists_canDecide_self hof (hpendE p₁ (Ne.symm hz1))
  cases x₀
  · exact key p₀ p₁ false (Ne.symm hz0) (Ne.symm hz1) hne h₀E hd₁'
  · cases x₁
    · exact hfinal E r hE hr0 hEr (bivalent_of_canDecide (Q := Set.univ) (a := p₁) (b := p₀)
        (v := false) trivial trivial h₁E h₀E)
    · exact key p₁ p₀ true (Ne.symm hz1) (Ne.symm hz0) (Ne.symm hne) h₁E hd₀'

/-- **Lemma 9.1** of [EGSZ16] (Ellen, Gelashvili, Shavit, Zhu, *A Complexity-Based Hierarchy for
Multiprocessor Synchronization*, PODC 2016), for `n ≥ 3` processes and a memory of locations
supporting only `read()` and `test-and-set()`: if the set of all processes is bivalent from a
reachable configuration `C`, then for every `k` an execution from `C` reaches a configuration `C'`
from which all processes are still bivalent and in which at least `k` locations are nonzero.
(The proof in the paper has a gap, repaired here: see the module docstring.) -/
theorem lemma_9_1 (hS : I.Solves (weakConsensus P Bool)) (hof : I.OneShotOF)
    (hn : 3 ≤ Fintype.card P) (k : ℕ) {C : Config BinCons (fun _ : ι => tasLoc) P L}
    (hC : I.Reach C) (hb : I.Bivalent Set.univ C) :
    ∃ C', I.ReachBy Set.univ C C' ∧ I.Bivalent Set.univ C' ∧
      k ≤ (Finset.univ.filter (fun i => C'.mem i ≠ 0)).card := by
  induction k with
  | zero => exact ⟨C, ReachBy.refl _ _, hb, Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨C₁, h1, hb1, hk1⟩ := ih
    obtain ⟨C₂, h2, hb2, hk2⟩ := exists_more_nonzero hS hof hn (hC.reachBy h1) hb1
    exact ⟨C₂, h1.trans h2, hb2, by simp only [nzSet] at hk2; omega⟩

/-- **Theorem 9.2** of [EGSZ16]: for `n ≥ 3` processes, there is no obstruction-free binary
consensus algorithm using finitely many memory locations that support only `read()` and
`test-and-set()`. This is the formal content of the paper's statement that an *unbounded* number
of such locations is necessary (for any finite set `ι` of locations, no algorithm exists).

We prove it for weak validity (`weakConsensus`) and one-shot obstruction-freedom, i.e. under
weaker assumptions than the paper, and for arbitrary initial memory contents (`memInit`); all
processes must be allowed to invoke both inputs (`hall`). -/
theorem theorem_9_2 (I : Impl BinCons (fun _ : ι => tasLoc) P L)
    (hS : I.Solves (weakConsensus P Bool)) (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v)
    (hn : 3 ≤ Fintype.card P) : False := by
  classical
  obtain ⟨p₀, p₁, hne⟩ : ∃ p₀ p₁ : P, p₀ ≠ p₁ := by
    obtain ⟨p₀, -, p₁, -, h⟩ := Finset.one_lt_card.1 (by rw [Finset.card_univ]; omega :
      1 < (Finset.univ : Finset P).card)
    exact ⟨p₀, p₁, h⟩
  obtain ⟨C, hC, h0, h1⟩ := I.exists_initial_bivalent hS hof hall hne
  have hb : I.Bivalent Set.univ C :=
    bivalent_of_canDecide (a := p₀) (b := p₁) (v := false) trivial trivial h0 h1
  obtain ⟨C', -, -, hk⟩ := lemma_9_1 hS hof hn (Fintype.card ι + 1) hC hb
  have := Finset.card_le_univ (Finset.univ.filter (fun i => C'.mem i ≠ 0))
  omega

end Main

end Cslib.SharedMemory.ComplexityHierarchy
