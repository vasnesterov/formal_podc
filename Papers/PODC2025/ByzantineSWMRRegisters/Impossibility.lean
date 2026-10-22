import Papers.PODC2025.ByzantineSWMRRegisters.SigTest
import Cslib.Foundations.Combinatorics.Labelling

/-!
# The impossibility of Theorem 29 (Hu–Toueg, PODC 2025), for every signature-like object

`SigTest.no_byzCorrect`: if `3 ≤ n ≤ 3f`, no implementation of an object with a `SigTest`
structure from single-writer base objects (e.g. SWMR registers) is correct (Byzantine
linearizable and terminating) against `f` Byzantine processes. Theorem 29 (test-or-set) and
Theorem 31 (verifiable, authenticated and sticky registers) are instances (`Main.lean`).

The proof follows the paper's histories `H1`, `H2`, `H3` (Figure 1), with the processes split
into three groups `G1 ∋ s`, `G2 ∋ pa`, `G3 ∋ pb` of size `≤ f` each:

* `H1` (`G3` Byzantine and silent): the setter performs its set operations, then `pa` tests;
  by validity the test is positive.
* `H2` (`G1` Byzantine): `G1` replays its `H1` steps (`Impl.replay`), so `G2` sees exactly what it
  saw in `H1` and `pa`'s test is positive again; then `G1` resets its objects to their initial
  states (`Impl.exists_setMem`), and `pb` tests; by relay its test is positive.
* `H3` (`G2` Byzantine, `G1` correct but asleep): `G2` first writes its objects' `H2` contents and
  then replays its `H2` steps while `pb` tests; `G3` cannot distinguish `H3` from `H2`, so `pb`'s
  test is positive although the correct setter never invoked anything — contradicting
  unforgeability.
-/

namespace Podc.ByzantineSWMRRegisters

open Cslib.SharedMemory Cslib.SharedMemory.Byzantine

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

/-! ## Helper lemmas -/

omit [DecidableEq P] [DecidableEq ι] in
lemma Event.respects_of_respects {e : Event P A B} {Bz Bz' : Finset P} (h : e.Respects Bz)
    (h1 : e.proc ∉ Bz) (h2 : e.proc ∉ Bz') : e.Respects Bz' := by
  cases e <;> simp_all [Event.Respects]

omit [DecidableEq ι] in
lemma opsOf_hist_of_steps {β : List (Event P A B)} (hβ : ∀ e ∈ β, ∃ q, e.IsStepOf q) (p : P) :
    opsOf (hist β) p = [] := by
  simp only [opsOf, hist, List.filterMap_eq_nil_iff]
  intro ℓ hℓ
  obtain ⟨e, he, hℓe⟩ := List.mem_filterMap.1 hℓ
  obtain ⟨r, hr⟩ := hβ e he
  cases ℓ with
  | inv q' o => exact absurd hℓe (hr.hist_inv q' o)
  | ret _ _ => rfl
  | tau _ => rfl

section FilterMem

variable {S : Finset P}

lemma opsOf_filter_mem (h : List (Label P A)) {p : P} (hp : p ∈ S) :
    opsOf (h.filter (fun ℓ => ℓ.proc ∈ S)) p = opsOf h p := by
  induction h with
  | nil => rfl
  | cons ℓ h ih =>
    rw [List.filter_cons]
    split_ifs with hℓ
    · rw [opsOf_cons, opsOf_cons, ih]
    · have hne : ℓ.proc ≠ p := fun h' => by simp [h', hp] at hℓ
      rw [opsOf_cons, ih, Label.invOf_eq_none_of_proc_ne hne]; rfl

lemma respsOf_filter_mem (h : List (Label P A)) {p : P} (hp : p ∈ S) :
    respsOf (h.filter (fun ℓ => ℓ.proc ∈ S)) p = respsOf h p := by
  induction h with
  | nil => rfl
  | cons ℓ h ih =>
    rw [List.filter_cons]
    split_ifs with hℓ
    · rw [respsOf_cons, respsOf_cons, ih]
    · have hne : ℓ.proc ≠ p := fun h' => by simp [h', hp] at hℓ
      rw [respsOf_cons, ih, Label.retOf_eq_none_of_proc_ne hne]; rfl

lemma opsOf_filter_not_mem (h : List (Label P A)) {p : P} (hp : p ∉ S) :
    opsOf (h.filter (fun ℓ => ℓ.proc ∈ S)) p = [] := by
  induction h with
  | nil => rfl
  | cons ℓ h ih =>
    rw [List.filter_cons]
    split_ifs with hℓ
    · have hne : ℓ.proc ≠ p := fun h' => by simp [h'] at hℓ; exact hp hℓ
      rw [opsOf_cons, ih, Label.invOf_eq_none_of_proc_ne hne]; rfl
    · exact ih

end FilterMem


/-! ## Invoking an operation and running until it completes -/

section Phases

variable [Fintype P] (I : Impl A B P L) (acc : Access P B) {allowed : P → A.Op → Prop} {s : P}
  {T : SigTest A allowed s} {f : ℕ} {adm : P → List A.Op → Prop}

include T in
/-- Invoke `o` at the correct idle process `p` and let all correct processes run until `p`'s
operation completes (termination). -/
lemma invoke_complete (hC : I.ByzCorrect acc f adm) (hadm : T.Admits adm) {Bz : Finset P}
    (hBz : Bz.card ≤ f) {α : List (Event P A B)} {C : Config A B P L}
    (hα : I.brun acc α = some C) (hresp : ∀ e ∈ α, e.Respects Bz) {p : P} {o : A.Op}
    (hp : p ∉ Bz) (hidle : C.pend p = none) (hallow : I.allowed p o)
    (hok : T.AdmOK (hist (α ++ [.inv p o]))) :
    ∃ β C', I.brun acc (α ++ .inv p o :: β) = some C' ∧ (∀ e ∈ β, ∃ q ∉ Bz, e.IsStepOf q) ∧
      C'.pend p = none ∧ (∀ q, opsOf (hist β) q = []) := by
  obtain ⟨C₁, h₁⟩ := I.bstep_inv_isSome acc hidle hallow
  have hα₁ : I.brun acc (α ++ [.inv p o]) = some C₁ :=
    I.brunFrom_trans acc hα ((I.brunFrom_singleton acc _ _).trans h₁)
  have hresp₁ : ∀ e ∈ α ++ [.inv p o], e.Respects Bz := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact hresp e he
    · simp at he; subst he; exact hp
  obtain ⟨β, C', hβ, hsteps, hidle'⟩ :=
    hC.exists_completion I acc hBz hα₁ hresp₁ (hok.adm_take hadm Bz) hp
  refine ⟨β, C', ?_, hsteps, hidle', opsOf_hist_of_steps (fun e he => ?_)⟩
  · have := I.brunFrom_trans acc hα₁ hβ
    rw [Impl.brun]; simpa using this
  · obtain ⟨q, -, hq⟩ := hsteps e he; exact ⟨q, hq⟩

omit [DecidableEq P] [DecidableEq ι] [Fintype P] in
lemma Event.respects_and_not_mem_of_step {Bz : Finset P} {β : List (Event P A B)}
    (hβ : ∀ e ∈ β, ∃ q ∉ Bz, e.IsStepOf q) : ∀ e ∈ β, e.Respects Bz ∧ e.proc ∉ Bz := by
  intro e he
  obtain ⟨q, hq, hqe⟩ := hβ e he
  exact ⟨hqe.respects hq, hqe.proc ▸ hq⟩

omit [Fintype P] in
lemma exists_respOf_of_idle {α : List (Event P A B)} {C : Config A B P L}
    (h : I.brun acc α = some C) {p : P} {o : A.Op} (hops : opsOf (hist α) p = [o])
    (hidle : C.pend p = none) : ∃ r, respOf (hist α) (p, 0) = some r := by
  have := I.respsOf_length_of_idle acc h hidle
  rw [hops] at this
  simp only [respOf]
  obtain ⟨r, hr⟩ := List.length_eq_one_iff.1 this
  exact ⟨r, by simp [hr]⟩

include T in
/-- History `H1`, first part: with `G3` Byzantine and silent, the setter performs its first `k`
set operations, each completing before the next is invoked. -/
lemma phase1 (hC : I.ByzCorrect acc f adm) (hadm : T.Admits adm) (hall : I.allowed = allowed)
    {G3 : Finset P} (hG3 : G3.card ≤ f) (hs : s ∉ G3) :
    ∀ k ≤ T.setOps.length, ∃ α C, I.brun acc α = some C ∧
      (∀ e ∈ α, e.Respects G3 ∧ e.proc ∉ G3) ∧ opsOf (hist α) s = T.setOps.take k ∧
      (∀ q, q ≠ s → opsOf (hist α) q = []) ∧ C.pend s = none ∧
      (∀ j, j + 1 < k → Precedes (hist α) (s, j) (s, j + 1))
  | 0, _ => ⟨[], I.initCfg, rfl, by simp, by simp, by simp, rfl, by simp⟩
  | k + 1, hk => by
    obtain ⟨α, C, hα, hev, hops, hoth, hidle, hprec⟩ :=
      phase1 hC hadm hall hG3 hs k (by omega)
    have hk' : k < T.setOps.length := by omega
    have htake : T.setOps.take (k + 1) = T.setOps.take k ++ [T.setOps[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk']; rfl
    have hok : T.AdmOK (hist (α ++ [.inv s T.setOps[k]])) := by
      refine ⟨?_, fun q hq => ?_⟩
      · simp only [hist_append, opsOf_append, hops, hist_cons, Event.hist_inv, Option.toList_some,
          hist_nil, List.append_nil, opsOf_cons, Label.invOf_inv, ite_true, opsOf_nil]
        rw [← htake]; exact List.take_prefix _ _
      · simp [hoth q hq, Ne.symm hq]
    obtain ⟨β, C', hrun, hsteps, hidle', hβops⟩ := invoke_complete I acc (T := T) hC hadm hG3 hα
      (fun e he => (hev e he).1) hs hidle (by rw [hall]; exact T.allowed_set _ (by simp))
      hok
    have hβ := Event.respects_and_not_mem_of_step hsteps
    refine ⟨α ++ .inv s T.setOps[k] :: β, C', hrun, fun e he => ?_, ?_, fun q hq => ?_, hidle',
      fun j hj => ?_⟩
    · simp only [List.mem_append, List.mem_cons] at he
      rcases he with he | rfl | he
      · exact hev e he
      · exact ⟨hs, hs⟩
      · exact hβ e he
    · rw [hist_append, hist_cons, opsOf_append, opsOf_append, hops, hβops, htake]; simp
    · simp [hoth q hq, hβops, Ne.symm hq]
    · have hsplit : hist (α ++ .inv s T.setOps[k] :: β) =
          hist α ++ hist (.inv s T.setOps[k] :: β) := by simp
      by_cases hjk : j + 1 < k
      · rw [hsplit]; exact (hprec j hjk).mono
      · have hj' : j + 1 = k := by omega
        refine ⟨hist α, _, hsplit, ?_, ?_⟩
        · simp only [Completed]
          rw [I.respsOf_length_of_idle acc hα hidle, hops, List.length_take]; omega
        · simp only [Invoked, hops, List.length_take]; omega

end Phases

omit [DecidableEq ι] in
lemma hist_nil_of_proc_ne {α : List (Event P A B)} {p : P} (h : ∀ e ∈ α, e.proc ≠ p) :
    opsOf (hist α) p = [] ∧ respsOf (hist α) p = [] := by
  have : ∀ ℓ ∈ hist α, ℓ.proc ≠ p := fun ℓ hℓ => by
    obtain ⟨e, he, hℓe⟩ := List.mem_filterMap.1 hℓ
    rw [Event.proc_of_hist hℓe]; exact h e he
  exact ⟨opsOf_eq_nil_of_proc_ne this, respsOf_eq_nil_of_proc_ne this⟩

section Core

variable [Fintype P] (I : Impl A B P L) (acc : Access P B) {allowed : P → A.Op → Prop} {s : P}
  {T : SigTest A allowed s} {f : ℕ} {adm : P → List A.Op → Prop}

include T in
/-- The core of Theorem 29: a partition of the processes into three groups of size `≤ f`
containing the setter and two testers yields a contradiction. -/
theorem false_of_groups (hC : I.ByzCorrect acc f adm) (hadm : T.Admits adm)
    (hall : I.allowed = allowed) (hI : I.RespectsAccess acc) {owner : ι → P}
    (hSW : SingleWriter acc owner) {G1 G2 G3 : Finset P} (h12 : Disjoint G1 G2)
    (h13 : Disjoint G1 G3) (h23 : Disjoint G2 G3) (hc1 : G1.card ≤ f) (hc2 : G2.card ≤ f)
    (hc3 : G3.card ≤ f) (hcov : ∀ p, p ∈ G1 ∨ p ∈ G2 ∨ p ∈ G3) {pa pb : P} (hs : s ∈ G1)
    (hpa : pa ∈ G2) (hpb : pb ∈ G3) : False := by
  have hcov' : ∀ p, p ∈ G1 ∨ p ∈ G2 ∨ p ∈ G3 := hcov
  have hsG2 : s ∉ G2 := Finset.disjoint_left.1 h12 hs
  have hsG3 : s ∉ G3 := Finset.disjoint_left.1 h13 hs
  have hpaG1 : pa ∉ G1 := Finset.disjoint_right.1 h12 hpa
  have hpaG3 : pa ∉ G3 := Finset.disjoint_left.1 h23 hpa
  have hpbG1 : pb ∉ G1 := Finset.disjoint_right.1 h13 hpb
  have hpbG2 : pb ∉ G2 := Finset.disjoint_right.1 h23 hpb
  have hpas : pa ≠ s := fun h => hpaG1 (h ▸ hs)
  have hpbs : pb ≠ s := fun h => hpbG1 (h ▸ hs)
  have hpapb : pa ≠ pb := fun h => hpaG3 (h ▸ hpb)
  have hm : 0 < T.setOps.length := List.length_pos_iff.2 T.setOps_ne_nil
  subst hall
  /- ### History `H1` -/
  obtain ⟨α, C, hα, hev, hops, hoth, hidle, hprec⟩ :=
    phase1 I acc (T := T) hC hadm rfl hc3 hsG3 _ le_rfl
  rw [List.take_length] at hops
  have hpaidle : C.pend pa = none := I.pend_eq_none_of_opsOf_nil acc hα (hoth pa hpas)
  have hok1 : T.AdmOK (hist (α ++ [.inv pa T.testOp])) := by
    refine ⟨by simp [hops, hpas], fun q hq => ?_⟩
    by_cases hqa : q = pa
    · subst hqa; simp [hoth _ hq]
    · simp [hoth q hq, Ne.symm hqa]
  obtain ⟨β1, C4, hrun1, hsteps1, hidle1, hβ1ops⟩ := invoke_complete I acc (T := T) hC hadm hc3
    hα (fun e he => (hev e he).1) hpaG3 hpaidle (T.allowed_test _ hpas) hok1
  set γ := α ++ .inv pa T.testOp :: β1 with hγ
  have hγev : ∀ e ∈ γ, e.Respects G3 ∧ e.proc ∉ G3 := by
    intro e he
    simp only [hγ, List.mem_append, List.mem_cons] at he
    rcases he with he | rfl | he
    · exact hev e he
    · exact ⟨hpaG3, hpaG3⟩
    · exact Event.respects_and_not_mem_of_step hsteps1 e he
  have hγops : ∀ q, opsOf (hist γ) q =
      if q = s then T.setOps else if q = pa then [T.testOp] else [] := by
    intro q
    simp only [hγ, hist_append, hist_cons, opsOf_append, hβ1ops, Event.hist_inv,
      Option.toList_some, List.singleton_append, opsOf_cons, Label.invOf_inv, List.append_nil]
    by_cases hqs : q = s
    · subst hqs; simp [hops, hpas]
    · by_cases hqa : q = pa
      · subst hqa; simp [hoth _ hqs, hqs]
      · simp [hoth _ hqs, hqs, hqa, Ne.symm hqa]
  obtain ⟨r1, hr1⟩ := exists_respOf_of_idle I acc hrun1 (o := T.testOp) (by rw [hγops]; simp [hpas]) hidle1
  have hok1' : T.AdmOK (hist γ) := by
    refine ⟨by rw [hγops]; simp, fun q hq => ?_⟩
    rw [hγops, ite_eq_right hq]; split_ifs <;> simp
  have hBL1 := hC.1 G3 hc3 γ ⟨⟨C4, hrun1⟩, fun e he => (hγev e he).1⟩
    (fun p _ => hok1'.adm hadm p)
  have hsplit1 : hist γ = hist α ++ hist (.inv pa T.testOp :: β1) := by simp [hγ]
  have hpos1 : T.pos r1 := by
    refine T.validity hBL1 hsG3 (x := (pa, 0)) hpaG3 (fun k hk => ?_) (fun k hk => ?_) ?_ ?_ hr1
    · simp [opOf, hγops, List.getElem?_eq_getElem hk]
    · rw [hsplit1]; exact (hprec k hk).mono
    · refine ⟨hist α, _, hsplit1, ?_, ?_⟩
      · simp only [Completed]
        rw [I.respsOf_length_of_idle acc hα hidle, hops]; omega
      · simp [Invoked, hoth pa hpas]
    · simp [opOf, hγops, hpas]
  /- ### History `H2`: `G1` Byzantine replays `H1`, resets its objects, then `pb` tests -/
  have hS1 : Disjoint (G2 ∪ G3) G1 := Finset.disjoint_union_left.2 ⟨h12.symm, h13.symm⟩
  obtain ⟨γ2, D4, hγ2, hγ2ev, hγ2hist, hag4, hloc4⟩ := I.replay acc hI (subset_refl G1)
    hrun1 (fun e he => by
      rcases hcov' e.proc with h | h | h
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact absurd h (hγev e he).2)
    (fun e he heS => Event.respects_of_respects (hγev e he).1 (hγev e he).2
      (Finset.disjoint_left.1 hS1 heS))
    ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  -- `G3` took no step in `H1`: its objects and local states are initial
  have hγG3 : ∀ e ∈ γ, ∀ q ∈ G3, e.proc ≠ q := fun e he q hq h => (hγev e he).2 (h ▸ hq)
  have hC4G3 : ∀ q ∈ G3, C4.pend q = none ∧ C4.loc q = I.locInit q := fun q hq =>
    I.brunFrom_pend_loc acc hrun1 (fun e he => hγG3 e he q hq)
  have hC4mem : ∀ i, owner i ∈ G3 → C4.mem i = I.memInit i := fun i hi =>
    I.brunFrom_mem_of_owner acc hI hSW hrun1 (fun e he => hγG3 e he _ hi)
  obtain ⟨T4, hT4⟩ := I.brunFrom_mem_finite acc hrun1
  obtain ⟨ρ, D5, hρ, hρev, hρhist, hρloc, hρpend, hρmem⟩ := I.exists_setMem acc hSW G1
    (T4.filter (fun i => owner i ∈ G1)) (fun i hi => (Finset.mem_filter.1 hi).2) D4 I.memInit
  have hD5mem : ∀ i, owner i ∉ G2 → D5.mem i = I.memInit i := by
    intro i hi
    rw [hρmem i, ← hag4.1]
    split_ifs with hiT
    · rfl
    · rcases hcov' (owner i) with h | h | h
      · have : i ∉ T4 := fun h' => hiT (Finset.mem_filter.2 ⟨h', h⟩)
        exact hT4 i this
      · exact absurd h hi
      · exact hC4mem i h
  have hD5 : I.brun acc (γ2 ++ ρ) = some D5 := I.brunFrom_trans acc hγ2 hρ
  have hδev : ∀ e ∈ γ2 ++ ρ, e.Respects G1 := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact (hγ2ev e he).1
    · exact (hρev e he).1
  have hδops : ∀ q, opsOf (hist (γ2 ++ ρ)) q = if q = pa then [T.testOp] else [] := by
    intro q
    rw [hist_append, hρhist, List.append_nil, hγ2hist]
    by_cases hq : q ∈ G2 ∪ G3
    · rw [opsOf_filter_mem _ hq, hγops, ite_eq_right (fun h => hsG2 (by
        rcases Finset.mem_union.1 (h ▸ hq) with h' | h'
        · exact h'
        · exact absurd h' hsG3))]
    · rw [opsOf_filter_not_mem _ hq, ite_eq_right]
      rintro rfl; exact hq (Finset.mem_union_left _ hpa)
  have hpbD5 : D5.pend pb = none := by
    rw [hρpend, ← (hag4.2 pb (Finset.mem_union_right _ hpb)).2]; exact (hC4G3 pb hpb).1
  have hok2 : T.AdmOK (hist (γ2 ++ ρ ++ [.inv pb T.testOp])) := by
    refine ⟨by rw [hist_append, opsOf_append, hδops, ite_eq_right (Ne.symm hpas)]; simp [hpbs],
      fun q hq => ?_⟩
    rw [hist_append, opsOf_append, hδops]
    by_cases hqa : q = pa
    · subst hqa; simp [Ne.symm hpapb]
    · by_cases hqb : q = pb
      · subst hqb; simp [hqa]
      · simp [hqa, Ne.symm hqb]
  obtain ⟨β3, D7, hrun3, hsteps3, hidle3, hβ3ops⟩ := invoke_complete I acc (T := T) hC hadm hc1
    hD5 hδev hpbG1 hpbD5 (T.allowed_test _ hpbs) hok2
  set H2 := γ2 ++ ρ ++ .inv pb T.testOp :: β3 with hH2
  have hH2ops : ∀ q, opsOf (hist H2) q = if q = pa ∨ q = pb then [T.testOp] else [] := by
    intro q
    rw [hH2, hist_append, opsOf_append, hδops, hist_cons, opsOf_append, hβ3ops]
    by_cases hqa : q = pa
    · subst hqa; simp [Ne.symm hpapb]
    · by_cases hqb : q = pb
      · subst hqb; simp [hqa]
      · simp [hqa, hqb, Ne.symm hqb]
  obtain ⟨r2, hr2⟩ := exists_respOf_of_idle I acc hrun3 (o := T.testOp)
    (by rw [hH2ops]; simp) hidle3
  have hok2' : T.AdmOK (hist H2) := by
    refine ⟨by rw [hH2ops, ite_eq_right (by rintro (h | h) <;> [exact hpas h.symm; exact hpbs h.symm])]; exact List.nil_prefix, fun q hq => ?_⟩
    rw [hH2ops]; split_ifs
    · exact List.prefix_refl _
    · exact List.nil_prefix
  have hH2ev : ∀ e ∈ H2, e.Respects G1 := by
    intro e he
    simp only [hH2, List.mem_append, List.mem_cons] at he
    rcases he with (he | he) | rfl | he
    · exact (hγ2ev e he).1
    · exact (hρev e he).1
    · exact hpbG1
    · exact (Event.respects_and_not_mem_of_step hsteps3 e he).1
  have hBL2 := hC.1 G1 hc1 H2 ⟨⟨D7, hrun3⟩, hH2ev⟩ (fun p _ => hok2'.adm hadm p)
  have hsplit2 : hist H2 = hist (γ2 ++ ρ) ++ hist (.inv pb T.testOp :: β3) := by simp [hH2]
  have hpaS : pa ∈ G2 ∪ G3 := Finset.mem_union_left _ hpa
  have hresps_pa : respsOf (hist (γ2 ++ ρ)) pa = respsOf (hist γ) pa := by
    rw [hist_append, hρhist, List.append_nil, hγ2hist, respsOf_filter_mem _ hpaS]
  have hr1' : respOf (hist H2) (pa, 0) = some r1 := by
    have hlen : 0 < (respsOf (hist γ) pa).length := completed_of_respOf hr1
    simp only [respOf] at hr1 ⊢
    rw [hsplit2, respsOf_append, hresps_pa, List.getElem?_append_left hlen]; exact hr1
  have hpos2 : T.pos r2 := by
    refine T.relay hBL2 (x := (pa, 0)) (y := (pb, 0)) hpaG1 hpbG1 ?_ ?_ hr1' hpos1 ?_ hr2
    · simp [opOf, hH2ops]
    · simp [opOf, hH2ops]
    · refine ⟨hist (γ2 ++ ρ), _, hsplit2, ?_, ?_⟩
      · simp only [Completed]; rw [hresps_pa]; exact completed_of_respOf hr1
      · rw [Invoked, hδops, ite_eq_right (Ne.symm hpapb)]; simp
  /- ### History `H3`: `G2` Byzantine, `G1` correct and asleep -/
  obtain ⟨T5, hT5⟩ := I.brunFrom_mem_finite acc hD5
  obtain ⟨σ, E5, hσ, hσev, hσhist, hσloc, hσpend, hσmem⟩ := I.exists_setMem acc hSW G2
    (T5.filter (fun i => owner i ∈ G2)) (fun i hi => (Finset.mem_filter.1 hi).2) I.initCfg D5.mem
  have hE5mem : E5.mem = D5.mem := by
    funext i
    rw [hσmem i]
    split_ifs with hiT
    · rfl
    · by_cases hi : owner i ∈ G2
      · have : i ∉ T5 := fun h' => hiT (Finset.mem_filter.2 ⟨h', hi⟩)
        exact (hT5 i this).symm
      · exact (hD5mem i hi).symm
  have hag5 : Agree G3 D5 E5 := by
    refine ⟨hE5mem.symm, fun q hq => ?_⟩
    have h4 := hag4.2 q (Finset.mem_union_right _ hq)
    rw [hρloc, hρpend, hσloc, hσpend, ← h4.1, ← h4.2, (hC4G3 q hq).1, (hC4G3 q hq).2]
    exact ⟨rfl, rfl⟩
  obtain ⟨D5', hD5', hsuf⟩ := I.brunFrom_append_eq_some acc
    (show I.brunFrom acc I.initCfg ((γ2 ++ ρ) ++ (.inv pb T.testOp :: β3)) = some D7 from hrun3)
  have hD5'eq : D5' = D5 := by
    have := hD5.symm.trans hD5'; exact (Option.some.inj this).symm
  subst hD5'eq
  have hS3 : Disjoint G3 G2 := h23.symm
  obtain ⟨ρ3, E7, hρ3, hρ3ev, hρ3hist, -, -⟩ := I.replay acc hI (subset_refl G2) hsuf
    (fun e he => by
      rcases List.mem_cons.1 he with rfl | he
      · exact Finset.mem_union_left _ hpb
      · obtain ⟨q, hq, hqe⟩ := hsteps3 e he
        rw [hqe.proc]
        rcases hcov' q with h | h | h
        · exact absurd h hq
        · exact Finset.mem_union_right _ h
        · exact Finset.mem_union_left _ h)
    (fun e he heS => by
      rcases List.mem_cons.1 he with rfl | he
      · exact hpbG2
      · obtain ⟨q, hq, hqe⟩ := hsteps3 e he
        exact hqe.respects (by rw [← hqe.proc]; exact Finset.disjoint_left.1 hS3 heS))
    hag5
  set H3 := σ ++ ρ3 with hH3
  have hrunH3 : I.brun acc H3 = some E7 := I.brunFrom_trans acc hσ hρ3
  have hH3hist : hist H3 = (hist (.inv pb T.testOp :: β3)).filter (fun ℓ => ℓ.proc ∈ G3) := by
    rw [hH3, hist_append, hσhist, hρ3hist, List.nil_append]
  have hsufops : ∀ q, opsOf (hist (.inv pb T.testOp :: β3)) q =
      if q = pb then [T.testOp] else [] := by
    intro q
    rw [hist_cons, opsOf_append, hβ3ops]
    by_cases hqb : q = pb
    · subst hqb; simp
    · simp [hqb, Ne.symm hqb]
  have hH3ops : ∀ q, opsOf (hist H3) q = if q = pb then [T.testOp] else [] := by
    intro q
    rw [hH3hist]
    by_cases hq : q ∈ G3
    · rw [opsOf_filter_mem _ hq, hsufops]
    · rw [opsOf_filter_not_mem _ hq, ite_eq_right]
      rintro rfl; exact hq hpb
  have hok3 : T.AdmOK (hist H3) := by
    refine ⟨by rw [hH3ops, ite_eq_right (Ne.symm hpbs)]; exact List.nil_prefix, fun q hq => ?_⟩
    rw [hH3ops]; split_ifs
    · exact List.prefix_refl _
    · exact List.nil_prefix
  have hBL3 := hC.1 G2 hc2 H3 ⟨⟨E7, hrunH3⟩, fun e he => by
      rcases List.mem_append.1 he with he | he
      · exact (hσev e he).1
      · exact (hρ3ev e he).1⟩
    (fun p _ => hok3.adm hadm p)
  -- `pb`'s test returns `r2` in `H3` as in `H2`
  have hpbδ : respsOf (hist (γ2 ++ ρ)) pb = [] := by
    rw [hist_append, hρhist, List.append_nil, hγ2hist,
      respsOf_filter_mem _ (Finset.mem_union_right _ hpb)]
    exact (hist_nil_of_proc_ne (fun e he => hγG3 e he pb hpb)).2
  have hr3 : respOf (hist H3) (pb, 0) = some r2 := by
    simp only [respOf] at hr2 ⊢
    rw [hsplit2, respsOf_append, hpbδ, List.nil_append] at hr2
    rw [hH3hist, respsOf_filter_mem _ hpb]; exact hr2
  have hnf := T.unforgeability hBL3 hsG2 (x := (pb, 0)) hpbG2 (by simp [opOf, hH3ops]) hr3 hpos2
  refine hnf ⟨hist H3, [], by simp, completed_of_respOf hr3, ?_⟩
  rw [Invoked, hH3ops, ite_eq_right (Ne.symm hpbs)]; simp

end Core

omit [DecidableEq P] in
/-- For `3 ≤ n ≤ 3f`, the processes split into three groups of size `≤ f`, the first containing
the given process `s`. -/
lemma exists_groups [Fintype P] {f : ℕ} (hn3 : 3 ≤ Fintype.card P)
    (hn : Fintype.card P ≤ 3 * f) (s : P) :
    ∃ G1 G2 G3 : Finset P, ∃ pa pb : P, Disjoint G1 G2 ∧ Disjoint G1 G3 ∧ Disjoint G2 G3 ∧
      G1.card ≤ f ∧ G2.card ≤ f ∧ G3.card ≤ f ∧ (∀ p, p ∈ G1 ∨ p ∈ G2 ∨ p ∈ G3) ∧
      s ∈ G1 ∧ pa ∈ G2 ∧ pb ∈ G3 := by
  obtain ⟨g, hsurj, hcard⟩ := Fintype.exists_fin_labelling_le (α := P) (k := 3) (t := f)
    Finset.univ (by simpa using hn3) hn
  set a := g s
  obtain ⟨pa, hpa⟩ := hsurj (a + 1) (Finset.mem_univ _)
  obtain ⟨pb, hpb⟩ := hsurj (a + 2) (Finset.mem_univ _)
  have hdis : ∀ i j : Fin 3, i ≠ j →
      Disjoint (Finset.univ.filter (fun x => g x = i)) (Finset.univ.filter (fun x => g x = j)) :=
    fun i j hij => Finset.disjoint_filter.2 (fun x _ hi hj => hij (hi ▸ hj))
  have h3 : ∀ a : Fin 3, a ≠ a + 1 ∧ a ≠ a + 2 ∧ a + 1 ≠ a + 2 := by decide
  have hcov : ∀ a x : Fin 3, x = a ∨ x = a + 1 ∨ x = a + 2 := by decide
  refine ⟨Finset.univ.filter (fun x => g x = a), Finset.univ.filter (fun x => g x = a + 1),
    Finset.univ.filter (fun x => g x = a + 2), pa, pb, hdis _ _ (h3 a).1, hdis _ _ (h3 a).2.1,
    hdis _ _ (h3 a).2.2, hcard _, hcard _, hcard _, fun p => ?_, by simp [a], by simp [hpa],
    by simp [hpb]⟩
  simpa using hcov a (g p)

/-- **Theorem 29, generalized.** If `3 ≤ n ≤ 3f`, no implementation of an object with a
`SigTest` structure from single-writer base objects (e.g. SWMR registers) is correct against `f`
Byzantine processes, even if correctness is only required for the executions in which the setter
invokes a prefix of its set operations and every other process invokes at most one test. -/
theorem SigTest.no_byzCorrect [Fintype P] {allowed : P → A.Op → Prop} {s : P}
    (T : SigTest A allowed s) {acc : Access P B} {owner : ι → P} (hSW : SingleWriter acc owner)
    (I : Impl A B P L) (hall : I.allowed = allowed) (hI : I.RespectsAccess acc) {f : ℕ}
    (hn3 : 3 ≤ Fintype.card P) (hn : Fintype.card P ≤ 3 * f) {adm : P → List A.Op → Prop}
    (hadm : T.Admits adm) : ¬ I.ByzCorrect acc f adm := by
  intro hC
  obtain ⟨G1, G2, G3, pa, pb, h12, h13, h23, hc1, hc2, hc3, hcov, hs, hpa, hpb⟩ :=
    exists_groups hn3 hn s
  exact false_of_groups I acc (T := T) hC hadm hall hI hSW h12 h13 h23 hc1 hc2 hc3 hcov hs hpa hpb

end Podc.ByzantineSWMRRegisters
