import Papers.PODC2011.RulesOfThumb.Model

/-!
# Valency of histories

The *stable coloring* of Appendix F (Definition F.10): a history `h`, together with a set `P` of
nodes that are already scheduled for the next time step (the pending reactions of the
"act-and-tell" model of Appendix F.6), is coloured by the set `F.lims h P` of action profiles to
which some fair dynamics from `h`, whose next activation set contains `P`, converges.

We prove the basic facts used in the valency argument:
* colours shrink along transitions (`lims_anti`, `lims_step_subset`, `lims_run_subset`);
* histories with the same length and the same `k` most recent profiles have the same future
  (`Equiv`, `lims_eq_of_equiv`), for `k`-recall reaction functions;
* two histories that differ only in the actions of one node `j` become equivalent after `j` is
  activated alone `k` times (`equiv_run_single`), for self-independent `k`-recall reaction
  functions; so (in a convergent system) their colours intersect (`lims_inter_nonempty`).
-/

namespace Podc.RulesOfThumb

open Filter

universe u v

variable {ι : Type u} {A : ι → Type v} [DecidableEq ι]

namespace System

variable (F : System A)

/-- The colour of the act-and-tell state `(h, P)`: limits of fair dynamics from `h` whose next
activation set contains `P`. -/
def lims (h : Hist A) (P : Finset ι) : Set (Profile A) :=
  {a | ∃ σ, IsSchedule σ ∧ Fair σ ∧ P ⊆ σ (h.time + 1) ∧ F.ConvergesTo h σ a}

variable {F}

lemma lims_anti {h : Hist A} {P Q : Finset ι} (hPQ : P ⊆ Q) : F.lims h Q ⊆ F.lims h P :=
  fun _ ⟨σ, h1, h2, h3, h4⟩ => ⟨σ, h1, h2, hPQ.trans h3, h4⟩

lemma convergesTo_run {s0 : Hist A} {σ : ℕ → Finset ι} {a : Profile A}
    (h : F.ConvergesTo s0 σ a) (m : ℕ) : F.ConvergesTo (F.run s0 σ m) σ a := by
  unfold ConvergesTo at *
  rw [eventually_atTop] at *
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun j hj => by rw [← F.run_add]; exact hN _ (by omega)⟩

/-- The tail of a fair dynamics converging to `a` witnesses `a` in the colour of every history
it passes through. -/
lemma mem_lims_run {s0 : Hist A} {σ : ℕ → Finset ι} {a : Profile A} (hs : IsSchedule σ)
    (hf : Fair σ) (hc : F.ConvergesTo s0 σ a) (m : ℕ) {S : Finset ι}
    (hS : S ⊆ σ ((F.run s0 σ m).time + 1)) : a ∈ F.lims (F.run s0 σ m) S :=
  ⟨σ, hs, hf, hS, convergesTo_run hc m⟩

lemma fair_update {σ : ℕ → Finset ι} (hf : Fair σ) (t₀ : ℕ) (P : Finset ι) :
    Fair (fun t => if t = t₀ then P else σ t) := by
  intro i
  refine (hf i).mp ((eventually_ne_atTop t₀).mono fun t ht hi => ?_)
  simpa [ht] using hi

lemma lims_step_subset {h : Hist A} {P : Finset ι} (hP : P.Nonempty) :
    F.lims (F.step h P) ∅ ⊆ F.lims h P := by
  rintro a ⟨σ', hs, hf, -, hc⟩
  set σ : ℕ → Finset ι := fun t => if t = h.time + 1 then P else σ' t
  have hrun : ∀ m, F.run h σ (m + 1) = F.run (F.step h P) σ' m := by
    intro m
    rw [add_comm, F.run_add]
    have : F.run h σ 1 = F.step h P := by simp [run_succ, σ]
    rw [this]
    exact F.run_congr fun t ht _ => by simp at ht; simp [σ]; omega
  refine ⟨σ, fun t => ?_, fair_update hf _ _, by simp [σ], ?_⟩
  · by_cases ht : t = h.time + 1 <;> simp [σ, ht, hP, hs t]
  · unfold ConvergesTo at *
    rw [eventually_atTop] at *
    obtain ⟨N, hN⟩ := hc
    refine ⟨N + 1, fun m hm => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hrun]; exact hN m (by omega)

lemma lims_step_subset' {h : Hist A} {P : Finset ι} (hP : P.Nonempty) :
    F.lims (F.step h P) ∅ ⊆ F.lims h ∅ :=
  (lims_step_subset hP).trans (lims_anti (Finset.empty_subset _))

lemma lims_run_subset {h : Hist A} {τ : ℕ → Finset ι} (hτ : IsSchedule τ) (m : ℕ) :
    F.lims (F.run h τ m) ∅ ⊆ F.lims h ∅ := by
  induction m with
  | zero => exact le_rfl
  | succ m ih => exact (lims_step_subset' (hτ _)).trans ih

variable [Fintype ι] [Nonempty ι]

/-- In a convergent system every colour is nonempty. -/
lemma lims_nonempty (hconv : F.Convergent) (h : Hist A) (P : Finset ι) :
    (F.lims h P).Nonempty := by
  have hs : IsSchedule (fun _ : ℕ => (Finset.univ : Finset ι)) := fun _ => Finset.univ_nonempty
  have hf : Fair (fun _ : ℕ => (Finset.univ : Finset ι)) := fun i =>
    Filter.Frequently.of_forall fun _ => Finset.mem_univ i
  obtain ⟨a, ha⟩ := hconv h _ hs hf
  exact ⟨a, _, hs, hf, Finset.subset_univ _, ha⟩

end System

/-! ### Equivalent histories -/

/-- Two histories at the same time with the same `k` most recent profiles. -/
structure HEquiv (k : ℕ) (h h' : Hist A) : Prop where
  time_eq : h.time = h'.time
  take_eq : h.toList.take k = h'.toList.take k

namespace System

variable {F : System A}

lemma take_cons_succ {α : Type*} (a : α) (l : List α) (k : ℕ) :
    (a :: l).take (k + 1) = a :: l.take k := rfl

lemma _root_.Podc.RulesOfThumb.HEquiv.cur_eq {k : ℕ} (hk : 1 ≤ k) {h h' : Hist A} (he : HEquiv k h h') : h.cur = h'.cur := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have := he.take_eq
  simp only [Hist.toList, take_cons_succ, List.cons.injEq] at this
  exact this.1

lemma _root_.Podc.RulesOfThumb.HEquiv.step {k : ℕ} (hk : 1 ≤ k) (hrec : ∀ i, F.HasRecall i k) {h h' : Hist A}
    (hkt : k ≤ h.time) (he : HEquiv k h h') (T : Finset ι) :
    HEquiv k (F.step h T) (F.step h' T) ∧ (F.step h T).cur = (F.step h' T).cur := by
  have hcur : (F.step h T).cur = (F.step h' T).cur := by
    funext i
    by_cases hi : i ∈ T
    · rw [step_cur_of_mem _ hi, step_cur_of_mem _ hi, ← he.time_eq]
      exact hrec i h h' he.time_eq hkt he.take_eq
    · rw [step_cur_of_not_mem _ hi, step_cur_of_not_mem _ hi, he.cur_eq hk]
  refine ⟨⟨by simp [he.time_eq], ?_⟩, hcur⟩
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [step_toList, step_toList, take_cons_succ, take_cons_succ, hcur]
  have e : ∀ x : List (Profile A), x.take k = (x.take (k + 1)).take k := fun x => by
    rw [List.take_take, min_eq_left (Nat.le_succ k)]
  rw [e h.toList, e h'.toList, he.take_eq]

lemma _root_.Podc.RulesOfThumb.HEquiv.run {k : ℕ} (hk : 1 ≤ k) (hrec : ∀ i, F.HasRecall i k) {h h' : Hist A}
    (hkt : k ≤ h.time) (he : HEquiv k h h') (σ : ℕ → Finset ι) (m : ℕ) :
    HEquiv k (F.run h σ m) (F.run h' σ m) := by
  induction m with
  | zero => exact he
  | succ m ih =>
    rw [run_succ, run_succ, ← ih.time_eq]
    exact (ih.step hk hrec (by simp; omega) _).1

lemma _root_.Podc.RulesOfThumb.HEquiv.convergesTo_iff {k : ℕ} (hk : 1 ≤ k) (hrec : ∀ i, F.HasRecall i k) {h h' : Hist A}
    (hkt : k ≤ h.time) (he : HEquiv k h h') (σ : ℕ → Finset ι) (a : Profile A) :
    F.ConvergesTo h σ a ↔ F.ConvergesTo h' σ a := by
  unfold ConvergesTo
  have : ∀ m, (F.run h σ m).cur = (F.run h' σ m).cur := fun m => (he.run hk hrec hkt σ m).cur_eq hk
  simp only [this]

lemma lims_eq_of_equiv {k : ℕ} (hk : 1 ≤ k) (hrec : ∀ i, F.HasRecall i k) {h h' : Hist A}
    (hkt : k ≤ h.time) (he : HEquiv k h h') (P : Finset ι) : F.lims h P = F.lims h' P := by
  ext a
  simp only [lims, he.time_eq, he.convergesTo_iff hk hrec hkt]

/-! ### Activating one node alone -/

lemma othersEq_step {j : ι} (hsi : F.SelfIndependent) {h h' : Hist A} (he : OthersEq j h h') :
    (F.step h {j}).cur = (F.step h' {j}).cur ∧ OthersEq j (F.step h {j}) (F.step h' {j}) := by
  have hcur : (F.step h {j}).cur = (F.step h' {j}).cur := by
    funext l
    by_cases hl : l = j
    · subst hl
      rw [step_cur_of_mem _ (Finset.mem_singleton_self _),
        step_cur_of_mem _ (Finset.mem_singleton_self _)]
      exact hsi _ h h' he
    · rw [step_cur_of_not_mem _ (by simpa using hl), step_cur_of_not_mem _ (by simpa using hl)]
      have := he
      unfold OthersEq Hist.toList at this
      exact (List.forall₂_cons.mp this).1 l hl
  refine ⟨hcur, ?_⟩
  unfold OthersEq
  rw [step_toList, step_toList, hcur]
  exact List.Forall₂.cons (fun _ _ => rfl) he

/-- Activating `j` alone `n` times from two histories that differ only in `j`'s actions makes
the `n` most recent profiles equal. -/
lemma othersEq_run_single {j : ι} (hsi : F.SelfIndependent) {h h' : Hist A}
    (he : OthersEq j h h') (n : ℕ) :
    OthersEq j (F.run h (fun _ => {j}) n) (F.run h' (fun _ => {j}) n) ∧
      (F.run h (fun _ => {j}) n).toList.take n = (F.run h' (fun _ => {j}) n).toList.take n := by
  induction n with
  | zero => exact ⟨he, by simp⟩
  | succ n ih =>
    rw [run_succ, run_succ]
    obtain ⟨hc, ho⟩ := othersEq_step hsi ih.1
    refine ⟨ho, ?_⟩
    rw [step_toList, step_toList, take_cons_succ, take_cons_succ, hc, ih.2]

lemma _root_.Podc.RulesOfThumb.OthersEq.time_eq {j : ι} {h h' : Hist A} (he : OthersEq j h h') : h.time = h'.time := by
  rw [← Hist.length_toList, ← Hist.length_toList]; exact he.length_eq

lemma equiv_run_single {k : ℕ} {j : ι} (hsi : F.SelfIndependent) {h h' : Hist A}
    (he : OthersEq j h h') :
    HEquiv k (F.run h (fun _ => {j}) k) (F.run h' (fun _ => {j}) k) :=
  ⟨OthersEq.time_eq (othersEq_run_single hsi he k).1, (othersEq_run_single hsi he k).2⟩

lemma isSchedule_single (j : ι) : IsSchedule (fun _ : ℕ => ({j} : Finset ι)) :=
  fun _ => Finset.singleton_nonempty j

variable [Fintype ι] [Nonempty ι]

/-- Two histories differing only in node `j`'s actions have a common colour. -/
lemma lims_inter_nonempty {k : ℕ} (hk : 1 ≤ k) (hrec : ∀ i, F.HasRecall i k)
    (hsi : F.SelfIndependent) (hconv : F.Convergent) {j : ι} {h h' : Hist A}
    (he : OthersEq j h h') : (F.lims h ∅ ∩ F.lims h' ∅).Nonempty := by
  obtain ⟨a, ha⟩ := lims_nonempty hconv (F.run h (fun _ => {j}) k) ∅
  have heq := lims_eq_of_equiv hk hrec (by simp) (equiv_run_single (k := k) hsi he) ∅
  refine ⟨a, lims_run_subset (isSchedule_single j) k ha, ?_⟩
  exact lims_run_subset (isSchedule_single j) k (heq ▸ ha)

/-- Variant: the second history is coloured with `j` already pending. -/
lemma lims_inter_nonempty' {k : ℕ} (hk : 1 ≤ k) (hrec : ∀ i, F.HasRecall i k)
    (hsi : F.SelfIndependent) (hconv : F.Convergent) {j : ι} {h h' : Hist A}
    (he : OthersEq j h h') : (F.lims h ∅ ∩ F.lims h' {j}).Nonempty := by
  obtain ⟨a, ha⟩ := lims_nonempty hconv (F.run h (fun _ => {j}) k) ∅
  have heq := lims_eq_of_equiv hk hrec (by simp) (equiv_run_single (k := k) hsi he) ∅
  refine ⟨a, lims_run_subset (isSchedule_single j) k ha, ?_⟩
  have ha' := heq ▸ ha
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [add_comm, F.run_add] at ha'
  have h1 := lims_run_subset (isSchedule_single j) k ha'
  exact lims_step_subset (Finset.singleton_nonempty j) h1

omit [DecidableEq ι] [Fintype ι] [Nonempty ι] in
/-- Two subsingleton sets with a common element are equal. -/
lemma subsingleton_eq_of_inter {α : Type*} {s t : Set α}
    (hs : s.Subsingleton) (ht : t.Subsingleton) (h : (s ∩ t).Nonempty) : s = t := by
  obtain ⟨x, hxs, hxt⟩ := h
  ext y
  exact ⟨fun hy => hs hy hxs ▸ hxt, fun hy => ht hy hxt ▸ hxs⟩

end System

end Podc.RulesOfThumb
