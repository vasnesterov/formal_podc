import Papers.PODC2026.ConsistentRefereeing.LongLivedBasic

/-!
# Competitors-valency (Section 5 of [ACE26]): Definition 15, Proposition 16, Lemmas 17, 19

Generic part of the impossibility proofs for the long-lived contest object: nothing here depends
on the base objects.

* `X.W α` — the competitors-valency `W(α)` (Definition 15);
* `X.Closed α` — `α` is competitors-closed; `¬ X.Closed α` is "supervalent" (Definition 15);
* `X.Helping α` — every `αβp` (`β` competitors-only) is closed (Definition 18);
* Proposition 16 (1)–(6): `W_eq_of_dec`, `W_ext_subset`, `Closed.ext`,
  `exists_super_ext1`, `not_decIn_of_super`, `super_of_not_invoked`;
* `resps_unbounded`, `exists_solo_return` — consequences of wait-freedom for schedules;
* `lemma17` — Lemma 17 (the key use of strong linearizability);
* `lemma19` — Lemma 19 (helping supervalent executions exist);
* `lemma24_1`, `lemma24_2` — the generic parts of Lemmas 24 and 29;
* `const_valency_contra` — a new generic argument used to repair the test&set case of the proof
  of Theorem 30.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Referee

open Impl

namespace LLCtx

variable {P ι L : Type} {B : ι → ObjSpec} [DecidableEq P] [DecidableEq ι] (X : LLCtx P ι L B)

/-! ### Definition 15 -/

/-- The competitors-valency `W(α)` (Definition 15 of [ACE26]): the outputs of `decide()` in the
linearizations of the competitors-only extensions of `α`. -/
def W (α : List (LLabel P)) : Set ℕ := {x | ∃ σ, X.Comp σ ∧ X.Dec (X.ext α σ) x}

/-- `α` is competitors-closed (Definition 15 of [ACE26]): every infinite competitors-only
extension has a finite prefix whose linearization contains `decide()`. Not closed =
competitors-supervalent. -/
def Closed (α : List (LLabel P)) : Prop :=
  ∀ s : ℕ → P, (∀ n, s n ≠ X.ref) → ∃ n, X.DecIn (X.ext α (pre s n))

/-- A (supervalent) execution is competitors-helping (Definition 18 of [ACE26]) if `αβp` is
closed for every competitors-only extension `β`. -/
def Helping (α : List (LLabel P)) : Prop :=
  ∀ σ, X.Comp σ → X.Closed (X.ext α (σ ++ [X.ref]))

/-- No competitors-only extension of `α` has `decide()` in its linearization (equivalently
`W(α) = ∅`). -/
def NoDec (α : List (LLabel P)) : Prop := ∀ σ, X.Comp σ → ¬ X.DecIn (X.ext α σ)

variable {X}

lemma noDec_iff (α : List (LLabel P)) : X.NoDec α ↔ ∀ x, x ∉ X.W α := by
  constructor
  · rintro h x ⟨σ, hσ, hx⟩; exact h σ hσ ⟨x, hx⟩
  · rintro h σ hσ ⟨x, hx⟩; exact h x ⟨σ, hσ, hx⟩

lemma NoDec.ext {α : List (LLabel P)} (h : X.NoDec α) {σ : List P} (hσ : X.Comp σ) :
    X.NoDec (X.ext α σ) := by
  intro τ hτ; rw [← ext_append]; exact h _ (comp_append.2 ⟨hσ, hτ⟩)

lemma Helping.ext {α : List (LLabel P)} (h : X.Helping α) {σ : List P} (hσ : X.Comp σ) :
    X.Helping (X.ext α σ) := by
  intro τ hτ; rw [← ext_append, ← List.append_assoc]; exact h _ (comp_append.2 ⟨hσ, hτ⟩)

/-! ### Pigeonhole and infinite paths -/

lemma exists_infinitely_often [Fintype P] (s : ℕ → P) : ∃ c, ∀ N, ∃ n ≥ N, s n = c := by
  classical
  by_contra hno
  push Not at hno
  choose Nf hNf using hno
  exact hNf (s (Finset.univ.sup Nf)) _ (Finset.le_sup (Finset.mem_univ _)) rfl

/-- König-free infinite paths: if `Φ` holds for `[]` and every competitors-only schedule with
`Φ` can be extended by a competitor keeping `Φ`, there is an infinite competitors-only schedule
all of whose prefixes satisfy `Φ`. -/
lemma exists_inf_path (Φ : List P → Prop) (h0 : Φ [])
    (hstep : ∀ σ, X.Comp σ → Φ σ → ∃ q, q ≠ X.ref ∧ Φ (σ ++ [q])) :
    ∃ s : ℕ → P, (∀ n, s n ≠ X.ref) ∧ ∀ n, Φ (pre s n) := by
  classical
  have H : ∀ σ : List P, ∃ q : P, (X.Comp σ ∧ Φ σ) → q ≠ X.ref ∧ Φ (σ ++ [q]) := by
    intro σ
    by_cases h : X.Comp σ ∧ Φ σ
    · obtain ⟨q, hq⟩ := hstep σ h.1 h.2; exact ⟨q, fun _ => hq⟩
    · exact ⟨X.ref, fun h' => absurd h' h⟩
  choose g hg using H
  let seq : ℕ → List P := fun n => Nat.rec [] (fun _ σ => σ ++ [g σ]) n
  have hseq : ∀ n, X.Comp (seq n) ∧ Φ (seq n) := by
    intro n
    induction n with
    | zero => exact ⟨comp_nil, h0⟩
    | succ n ih =>
      obtain ⟨h1, h2⟩ := hg _ ih
      exact ⟨comp_append.2 ⟨ih.1, comp_singleton h1⟩, h2⟩
  refine ⟨fun n => g (seq n), fun n => (hg _ (hseq n)).1, fun n => ?_⟩
  have : pre (fun n => g (seq n)) n = seq n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pre_succ, ih]
  rw [this]; exact (hseq n).2

/-- Contrapositive form: a "critical" extension exists. -/
lemma exists_critical (Φ : List P → Prop) (h0 : Φ [])
    (hno : ∀ s : ℕ → P, (∀ n, s n ≠ X.ref) → ¬ ∀ n, Φ (pre s n)) :
    ∃ σ, X.Comp σ ∧ Φ σ ∧ ∀ q, q ≠ X.ref → ¬ Φ (σ ++ [q]) := by
  by_contra hc
  push Not at hc
  obtain ⟨s, hs, hΦ⟩ := exists_inf_path (X := X) Φ h0 hc
  exact hno s hs hΦ

/-! ### Infinite executions of schedules and wait-freedom -/

lemma ext_pre_succ (α : List (LLabel P)) (s : ℕ → P) (n : ℕ) :
    X.ext α (pre s (n + 1)) = X.ext1 (X.ext α (pre s n)) (s n) := by
  rw [pre_succ, ext_append, ext_singleton]

lemma extL_pre_succ (α : List (LLabel P)) (s : ℕ → P) (n : ℕ) :
    X.extL α (pre s (n + 1)) = X.extL α (pre s n) ++ (X.nl (X.ext α (pre s n)) (s n)).toList := by
  rw [pre_succ, extL_append]; simp [extL]

/-- The limit of a chain of good executions. -/
lemma chain_infExec (E : ℕ → List (LLabel P)) (hmono : ∀ k, E k <+: E (k + 1))
    (hlen : ∀ k, k ≤ (E k).length) (hgood : ∀ k, X.Good (E k)) :
    ∃ e : X.I.InfExec, (∀ k n (hn : n < (E k).length), e.lbl n = (E k)[n]) ∧
      (∀ t, LLAdm X.ref (e.lbls t)) ∧
      (∀ k n, n ≤ (E k).length → X.Good ((E k).take n) ∧ X.cfg ((E k).take n) = e.cfg n) := by
  obtain ⟨e, hlbl, hcfg⟩ := X.I.exists_infExec_of_chain E hmono hlen (fun k => (hgood k).1)
  have hgt : ∀ k n, X.Good ((E k).take n) := fun k n =>
    (hgood k).of_prefix (List.take_prefix _ _)
  refine ⟨e, hlbl, fun t => ?_, fun k n hn => ⟨hgt k n, ?_⟩⟩
  · have : e.lbls t = (E t).take t := by
      apply List.ext_getElem
      · simp [InfExec.lbls]; have := hlen t; omega
      · intro n h1 h2
        simp only [InfExec.lbls, List.getElem_map, List.getElem_range, List.getElem_take]
        simp only [InfExec.lbls, List.length_map, List.length_range] at h1
        exact hlbl t n (by have := hlen t; omega)
    rw [this]; exact (hgt t t).2
  · have h1 := (hgt k n).run
    rw [hcfg k n hn] at h1
    exact (Option.some.inj h1).symm

/-- **Wait-freedom along a schedule.** If every step of the schedule `s` adds a label and `c` is
scheduled infinitely often, `c` cannot stay pending forever. -/
lemma core [Fintype P] {α : List (LLabel P)} (hα : X.Good α) (s : ℕ → P)
    (hs : ∀ n, (X.nl (X.ext α (pre s n)) (s n)).isSome) {c : P}
    (hinf : ∀ N, ∃ n ≥ N, s n = c) (N : ℕ)
    (hpend : ∀ n ≥ N, (X.cfg (X.ext α (pre s n))).pend c ≠ none) : False := by
  set E : ℕ → List (LLabel P) := fun k => X.ext α (pre s k) with hE
  have hEs : ∀ k, ∃ ℓ, X.nl (E k) (s k) = some ℓ ∧ E (k + 1) = E k ++ [ℓ] := by
    intro k
    obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.1 (hs k)
    exact ⟨ℓ, hℓ, by simp only [hE]; rw [ext_pre_succ, ext1_of_some hℓ]⟩
  have hlen : ∀ k, (E k).length = α.length + k := by
    intro k
    induction k with
    | zero => simp [hE, pre]
    | succ k ih =>
      obtain ⟨ℓ, -, he⟩ := hEs k
      rw [he, List.length_append, ih]; simp; omega
  have hgood : ∀ k, X.Good (E k) := fun k => hα.ext _
  obtain ⟨e, hlbl, hadm, hcfg⟩ := X.chain_infExec E
    (fun k => by obtain ⟨ℓ, -, he⟩ := hEs k; rw [he]; exact List.prefix_append _ _)
    (fun k => by rw [hlen]; omega) hgood
  have hcfgE : ∀ k, e.cfg (α.length + k) = X.cfg (E k) := by
    intro k
    have := (hcfg k (E k).length le_rfl).2
    rw [List.take_length, hlen] at this; exact this.symm
  obtain ⟨N', hN'⟩ := X.wf e hadm c (α.length + N) (by
    intro m hm
    have := hcfgE (m - α.length)
    rw [Nat.add_sub_cancel' (by omega)] at this
    rw [this]; exact hpend _ (by omega))
  obtain ⟨n, hn, hsn⟩ := hinf (N + N')
  obtain ⟨ℓ, hℓ, he⟩ := hEs n
  have hstep := ((hgood n).nl_step hℓ).1
  rw [← he] at hstep
  have htau : ℓ = .tau c := X.I.eq_tau_of_step hstep (by rw [nl_proc hℓ, hsn])
    (hpend n (by omega)) (hpend (n + 1) (by omega))
  apply hN' (α.length + n) (by omega)
  rw [hlbl (n + 1) (α.length + n) (by rw [hlen]; omega), ← htau]
  simp only [he, List.getElem_append_right (by rw [hlen]; omega), hlen]
  simp

/-- **Wait-freedom for competitors.** A competitor scheduled infinitely often in an infinite
competitors-only extension completes infinitely many operations. -/
lemma resps_unbounded [Fintype P] {α : List (LLabel P)} (hα : X.Good α) {s : ℕ → P}
    (hs : ∀ n, s n ≠ X.ref) {c : P} (hinf : ∀ N, ∃ n ≥ N, s n = c) (x : ℕ) :
    ∃ n, x < (respsOf (X.extL α (pre s n)) c).length := by
  classical
  by_contra hno
  push Not at hno
  set f : ℕ → ℕ := fun n => (respsOf (X.extL α (pre s n)) c).length with hf
  have hfs : ∀ n, f (n + 1) = f n + (respsOf (X.nl (X.ext α (pre s n)) (s n)).toList c).length := by
    intro n; simp only [hf, extL_pre_succ, respsOf_append, List.length_append]
  have hmono : Monotone f := monotone_nat_of_le_succ (fun n => by rw [hfs]; omega)
  set K := Nat.findGreatest (fun K => ∃ n, K ≤ f n) x with hK
  obtain ⟨n₀, hn₀⟩ : ∃ n, K ≤ f n :=
    Nat.findGreatest_spec (P := fun K => ∃ n, K ≤ f n) (Nat.zero_le x) ⟨0, Nat.zero_le _⟩
  have hconst : ∀ n ≥ n₀, f n = K := by
    intro n hn
    have h1 : f n ≤ K := Nat.le_findGreatest (hno n) ⟨n, le_rfl⟩
    have h2 := hmono hn
    omega
  obtain ⟨n₁, hn₁, hsn₁⟩ := hinf n₀
  -- after `n₁`, `c` is pending forever
  have hgo : ∀ n ≥ n₀, ((X.cfg (X.ext α (pre s n))).pend c ≠ none ∨ s n = c) →
      (X.cfg (X.ext α (pre s (n + 1)))).pend c ≠ none := by
    intro n hn h
    rw [ext_pre_succ]
    by_cases hsc : s n = c
    · rw [hsc]
      obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.1 (nl_isSome_of_ne (X := X)
        (α := X.ext α (pre s n)) (hsc ▸ hs n))
      have hstep := (((hα.ext _)).nl_step hℓ).1
      rw [← ext1_of_some hℓ] at hstep
      have hproc := nl_proc hℓ
      cases ℓ with
      | inv q o =>
        simp only [Label.proc] at hproc; subst hproc
        simp [(step_inv hstep).2.2.1]
      | tau q =>
        have := step_tau hstep
        rw [this.2.1]; simp only [Label.proc] at hproc; rw [← hproc]; exact this.1
      | ret q r =>
        exfalso
        simp only [Label.proc] at hproc; subst hproc
        have e1 := hfs n
        rw [hsc, hℓ, hconst n hn, hconst (n + 1) (by omega)] at e1
        simp [respsOf_cons] at e1
    · rw [((hα.ext _).ext1_other (Ne.symm hsc)).2]
      exact h.resolve_right hsc
  have hpend : ∀ n ≥ n₁ + 1, (X.cfg (X.ext α (pre s n))).pend c ≠ none := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hgo n₁ hn₁ (Or.inr hsn₁)
    | succ n hn ih => exact hgo n (by omega) (Or.inl ih)
  exact X.core hα s (fun n => nl_isSome_of_ne (hs n)) hinf (n₁ + 1) hpend

/-- **Wait-freedom, solo.** A pending process running solo returns. -/
lemma exists_solo_return [Fintype P] {α : List (LLabel P)} (hα : X.Good α) (r : P) :
    ∃ m, (X.cfg (X.ext α (List.replicate m r))).pend r = none := by
  by_contra hno
  push Not at hno
  have hpre : ∀ n, pre (fun _ => r) n = List.replicate n r := pre_const r
  refine X.core hα (fun _ => r) (fun n => ?_) (fun N => ⟨N, le_rfl, rfl⟩) 0
    (fun n _ => by rw [hpre]; exact hno n)
  rw [hpre, nl_of_pend (hno n)]; rfl

/-! ### Proposition 16 -/

/-- Proposition 16(1) of [ACE26] (in the form: if `decide()` is in `h α` with output `x`, then
`W(α) = {x}`). -/
lemma W_eq_of_dec {α : List (LLabel P)} (hα : X.Good α) {x : ℕ} (hx : X.Dec α x) :
    X.W α = {x} := by
  ext y
  simp only [W, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨σ, -, hy⟩
    exact Dec.unique (hα.ext σ) hy (hx.mono (hα.ext σ) (prefix_ext _ _))
  · rintro rfl; exact ⟨[], comp_nil, by simpa using hx⟩

/-- Proposition 16(2) of [ACE26]. -/
lemma W_ext_subset (α : List (LLabel P)) {σ : List P} (hσ : X.Comp σ) :
    X.W (X.ext α σ) ⊆ X.W α := by
  rintro x ⟨τ, hτ, hx⟩
  exact ⟨σ ++ τ, comp_append.2 ⟨hσ, hτ⟩, by rwa [ext_append]⟩

/-- Proposition 16(5) of [ACE26]. -/
lemma not_decIn_of_super {α : List (LLabel P)} (h : ¬ X.Closed α) : ¬ X.DecIn α := by
  intro hd; exact h (fun s _ => ⟨0, by simpa [pre] using hd⟩)

/-- Proposition 16(3) of [ACE26]. -/
lemma Closed.ext {α : List (LLabel P)} (hα : X.Good α) (h : X.Closed α) {σ : List P}
    (hσ : X.Comp σ) : X.Closed (X.ext α σ) := by
  intro s hs
  classical
  let s' : ℕ → P := fun n => if hn : n < σ.length then σ[n] else s (n - σ.length)
  have hs' : ∀ n, s' n ≠ X.ref := by
    intro n; simp only [s']; split_ifs
    · exact hσ _ (List.getElem_mem _)
    · exact hs _
  have hpre1 : pre s' σ.length = σ := by
    apply List.ext_getElem (by simp [length_pre])
    intro n h1 h2; simp only [pre, List.getElem_map, List.getElem_range, s', h2, dite_true]
  have hpre2 : (fun i => s' (σ.length + i)) = s := by
    funext i; simp [s']
  obtain ⟨n, hn⟩ := h s' hs'
  by_cases hle : n ≤ σ.length
  · refine ⟨0, hn.mono ((hα.ext _).ext _) ?_⟩
    simp only [pre_zero, ext_nil]
    rw [← hpre1]; exact ext_prefix_of_prefix α (pre_prefix s' hle)
  · refine ⟨n - σ.length, ?_⟩
    have : pre s' n = σ ++ pre s (n - σ.length) := by
      rw [show n = σ.length + (n - σ.length) by omega, pre_add, hpre1, hpre2]; simp
    rwa [← ext_append, ← this]

/-- Proposition 16(4) of [ACE26]. -/
lemma exists_super_ext1 {α : List (LLabel P)} (h : ¬ X.Closed α) :
    ∃ q, q ≠ X.ref ∧ ¬ X.Closed (X.ext α [q]) := by
  by_contra hno
  push Not at hno
  apply h
  intro s hs
  obtain ⟨m, hm⟩ := hno (s 0) (hs 0) (fun n => s (1 + n)) (fun n => hs _)
  refine ⟨1 + m, ?_⟩
  rw [pre_add, ← ext_append] at *
  simpa [pre] using hm

/-- Proposition 16(6) of [ACE26]. -/
lemma super_of_not_invoked {α : List (LLabel P)} (hα : X.Good α)
    (hinv : opsOf α X.ref = []) {c : P} (hc : c ≠ X.ref) : ¬ X.Closed α := by
  intro h
  obtain ⟨n, x, hx⟩ := h (fun _ => c) (fun _ => hc)
  have hg := hα.ext (pre (fun _ => c) n)
  have h1 := (X.lin _ hg.1 hg.2).op_eq _ hx
  have h2 : opsOf (X.ext α (pre (fun _ => c) n)) X.ref = [] := by
    rw [opsOf_ext_of_not_mem]; · exact hinv
    rw [pre_const]; intro hm; exact hc (List.eq_of_mem_replicate hm).symm
  simp [opOf, h2] at h1

/-- A closed execution has nonempty valency. -/
lemma Closed.nonempty {α : List (LLabel P)} (h : X.Closed α) {c : P} (hc : c ≠ X.ref) :
    ∃ x, x ∈ X.W α := by
  obtain ⟨n, x, hx⟩ := h (fun _ => c) (fun _ => hc)
  exact ⟨x, pre (fun _ => c) n, comp_pre (fun _ => hc) n, hx⟩

/-- In a closed execution the referee has invoked `decide`. -/
lemma Closed.invoked {α : List (LLabel P)} (hα : X.Good α) (h : X.Closed α) {c : P}
    (hc : c ≠ X.ref) : opsOf α X.ref ≠ [] :=
  fun hinv => super_of_not_invoked hα hinv hc h

/-- If `decide()` is not in `h α`, `decide` has not returned in `α`. -/
lemma Good.resps_ref_eq_nil {α : List (LLabel P)} (hα : X.Good α) (h : ¬ X.DecIn α) :
    respsOf α X.ref = [] := by
  by_contra hne
  obtain ⟨x, -, hx⟩ := hα.dec_of_completed hne
  exact h ⟨x, hx⟩

/-- In a closed execution in which `decide()` is not in the linearization, `decide` is
pending. -/
lemma Closed.pend {α : List (LLabel P)} (hα : X.Good α) (h : X.Closed α) (hnd : ¬ X.DecIn α)
    {c : P} (hc : c ≠ X.ref) : (X.cfg α).pend X.ref ≠ none :=
  hα.pend_ref_ne_none_iff.2 ⟨h.invoked hα hc, hα.resps_ref_eq_nil hnd⟩

/-- A closed execution whose valency is a singleton keeps it in all extensions. -/
lemma W_ext_eq_of_closed {α : List (LLabel P)} (hα : X.Good α) (h : X.Closed α) {y : ℕ}
    (hy : X.W α = {y}) {σ : List P} (hσ : X.Comp σ) {c : P} (hc : c ≠ X.ref) :
    X.W (X.ext α σ) = {y} := by
  obtain ⟨x, hx⟩ := (h.ext hα hσ).nonempty hc
  have := W_ext_subset α hσ hx
  rw [hy] at this; simp only [Set.mem_singleton_iff] at this; subst this
  apply Set.Subset.antisymm
  · rw [← hy]; exact W_ext_subset α hσ
  · simpa using hx

/-- The counting argument in terms of valencies. -/
lemma not_mem_W_of_resps {β : List (LLabel P)} (hβ : X.Good β) (hnd : ¬ X.DecIn β) {c : P}
    (hc : c ≠ X.ref) {v : ℕ} (hv : v < (respsOf β c).length) (τ : List P) :
    v ∉ X.W (X.ext β τ) := by
  rintro ⟨τ', -, hd⟩
  rw [← ext_append, ext_eq_append] at hd
  exact not_dec_of_resps hβ hnd hc hv (by rw [← ext_eq_append]; exact hβ.ext _) hd

/-! ### Lemma 17 -/

/-- **Lemma 17 of [ACE26].** Let `α` be closed, with `decide` pending, and let `α'` be
indistinguishable from `α` to the referee and to a competitor `c` (their final configurations
agree on a set `Q` containing both). Then `W(α) ∩ W(α') ≠ ∅`.

(The pending hypothesis is implicit in the paper: if `decide` has already returned in `α`, the
referee's local state does not determine the history of `α'`.) -/
theorem lemma17 [Fintype P] {α α' : List (LLabel P)} (hα : X.Good α) (hα' : X.Good α')
    (hcl : X.Closed α) (hpend : (X.cfg α).pend X.ref ≠ none) {Q : Set P} {c : P}
    (hc : c ≠ X.ref) (hcQ : c ∈ Q) (hrQ : X.ref ∈ Q) (hag : AgreeOn Q (X.cfg α) (X.cfg α')) :
    ∃ x, x ∈ X.W α ∧ x ∈ X.W α' := by
  set s : ℕ → P := fun _ => c with hs_def
  have hs : ∀ n, s n ≠ X.ref := fun _ => hc
  obtain ⟨n₀, x, hx⟩ := hcl s hs
  obtain ⟨n₁, hn₁⟩ := X.resps_unbounded hα hs (c := c) (fun N => ⟨N, le_rfl, rfl⟩) x
  set σ := pre s (n₀ + n₁) with hσ_def
  have hσc : X.Comp σ := comp_pre hs _
  have hσQ : ∀ p ∈ σ, p ∈ Q := by
    intro p hp; simp only [hσ_def, pre_const, s] at hp; rw [List.eq_of_mem_replicate hp]; exact hcQ
  have hrσ : X.ref ∉ σ := hσc.not_mem
  have hdec : X.Dec (X.ext α σ) x :=
    hx.mono (hα.ext _) (ext_prefix_of_prefix α (pre_prefix s (Nat.le_add_right _ _)))
  have hresp : x < (respsOf (X.extL α σ) c).length := by
    obtain ⟨u, hu⟩ := pre_prefix s (Nat.le_add_left n₁ n₀)
    rw [hσ_def, ← hu, extL_append, respsOf_append, List.length_append]; omega
  have hpend' : (X.cfg α').pend X.ref ≠ none := by rw [← hag.pend _ hrQ]; exact hpend
  have hst : X.ref ∈ Q → (opsOf α X.ref = [] ↔ opsOf α' X.ref = []) := fun _ =>
    ⟨fun h => absurd h (hα.pend_ref_ne_none_iff.1 hpend).1,
     fun h => absurd h (hα'.pend_ref_ne_none_iff.1 hpend').1⟩
  obtain ⟨hL, hag2, hst2⟩ := transfer hα hα' hag hst hσQ
  set β := X.ext α σ with hβ
  set β' := X.ext α' σ with hβ'
  have hgβ : X.Good β := hα.ext σ
  have hgβ' : X.Good β' := hα'.ext σ
  have hpβ : (X.cfg β).pend X.ref ≠ none := by rw [(hα.ext_other hrσ).2]; exact hpend
  have hpβ' : (X.cfg β').pend X.ref ≠ none := by rw [(hα'.ext_other hrσ).2]; exact hpend'
  obtain ⟨m, hm⟩ := X.exists_solo_return hgβ X.ref
  set τ := List.replicate m X.ref with hτ
  obtain ⟨hL2, -, -⟩ := transfer hgβ hgβ' hag2 hst2 (σ := τ) (fun p hp => by
    rw [List.eq_of_mem_replicate hp]; exact hrQ)
  have hgβτ : X.Good (X.ext β τ) := hgβ.ext τ
  have hgβτ' : X.Good (X.ext β' τ) := hgβ'.ext τ
  -- `decide` has returned at the end of `βτ`, with output `x`
  have hcomp : respsOf (X.ext β τ) X.ref ≠ [] := by
    have hne : opsOf (X.ext β τ) X.ref ≠ [] := by
      have := (hgβ.pend_ref_ne_none_iff.1 hpβ).1
      rw [ext_eq_append, opsOf_append]; simp [this]
    rcases hgβτ.ref_counts with ⟨-, h2⟩ | ⟨h1, -⟩
    · intro h; rw [h] at h2; simp at h2; exact hne h2
    · exact absurd hm h1
  obtain ⟨x', hx'r, hx'⟩ := hgβτ.dec_of_completed hcomp
  have hxx' : x' = x := Dec.unique hgβτ hx' (hdec.mono hgβτ (prefix_ext _ _))
  subst hxx'
  -- the same response at the end of `β'τ`
  have hrr : respsOf (X.ext β' τ) X.ref = respsOf (X.ext β τ) X.ref := by
    rw [ext_eq_append, ext_eq_append, respsOf_append, respsOf_append, ← hL2,
      (hgβ.pend_ref_ne_none_iff.1 hpβ).2, (hgβ'.pend_ref_ne_none_iff.1 hpβ').2]
  have hdec' : X.Dec (X.ext β' τ) x' := by
    rw [← hrr] at hcomp
    obtain ⟨x'', hr'', hd''⟩ := hgβτ'.dec_of_completed hcomp
    have : respOf (X.ext β' τ) (X.ref, 0) = respOf (X.ext β τ) (X.ref, 0) := by
      simp only [respOf, hrr]
    rw [this, hx'r] at hr''
    simp only [Option.some.injEq, LLResp.val.injEq] at hr''
    rwa [hr'']
  -- hence `decide` is already in `h β'`
  have hdin : X.DecIn β' := by
    by_contra hnd
    apply not_dec_of_resps hgβ' hnd hc (x := x') (γ := X.extL β' τ)
    · rw [hβ', ext_eq_append, respsOf_append, List.length_append, ← hL]; omega
    · exact hgβτ'
    · exact hdec'
  obtain ⟨y, hy⟩ := hdin
  have hyx : y = x' := Dec.unique hgβτ' (hy.mono hgβτ' (prefix_ext _ _)) hdec'
  subst hyx
  exact ⟨y, ⟨σ, hσc, hdec⟩, ⟨σ, hσc, hy⟩⟩

/-! ### Lemma 19 -/

lemma respsOf_prefix {α β : List (LLabel P)} (h : α <+: β) (p : P) :
    respsOf α p <+: respsOf β p := by
  obtain ⟨u, rfl⟩ := h; rw [respsOf_append]; exact List.prefix_append _ _

lemma opsOf_prefix {α β : List (LLabel P)} (h : α <+: β) (p : P) :
    opsOf α p <+: opsOf β p := by
  obtain ⟨u, rfl⟩ := h; rw [opsOf_append]; exact List.prefix_append _ _

/-- **Lemma 19 of [ACE26].** There is a helping supervalent execution. -/
theorem lemma19 [Fintype P] {c : P} (hc : c ≠ X.ref) :
    ∃ α, X.Good α ∧ ¬ X.Closed α ∧ X.Helping α := by
  classical
  by_contra hno
  push Not at hno
  have H : ∀ α : List (LLabel P), ∃ σ : List P, (X.Good α ∧ ¬ X.Closed α) →
      X.Comp σ ∧ ¬ X.Closed (X.ext α (σ ++ [X.ref])) := by
    intro α
    by_cases h : X.Good α ∧ ¬ X.Closed α
    · have := hno α h.1 h.2
      simp only [Helping, not_forall] at this
      obtain ⟨σ, hσ, h'⟩ := this
      exact ⟨σ, fun _ => ⟨hσ, h'⟩⟩
    · exact ⟨[], fun h' => absurd h' h⟩
  choose g hg using H
  obtain ⟨a, ha0, ha_succ⟩ : ∃ a : ℕ → List (LLabel P), a 0 = [] ∧
      ∀ i, a (i + 1) = X.ext (a i) (g (a i) ++ [X.ref]) :=
    ⟨fun n => Nat.rec [] (fun _ α => X.ext α (g α ++ [X.ref])) n, rfl, fun _ => rfl⟩
  have ha : ∀ i, X.Good (a i) ∧ ¬ X.Closed (a i) := by
    intro i
    induction i with
    | zero => rw [ha0]; exact ⟨good_nil, super_of_not_invoked good_nil (by simp [opsOf]) hc⟩
    | succ i ih => rw [ha_succ]; exact ⟨ih.1.ext _, (hg _ ih).2⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → List (LLabel P), ∀ i, b i = X.ext (a i) (g (a i)) :=
    ⟨fun i => X.ext (a i) (g (a i)), fun _ => rfl⟩
  have hab : ∀ i, a (i + 1) = X.ext1 (b i) X.ref := by
    intro i; rw [ha_succ, ext_append, ext_singleton, hb]
  have hgb : ∀ i, X.Good (b i) := fun i => by rw [hb]; exact (ha i).1.ext _
  have hres : ∀ i, respsOf (a i) X.ref = [] := fun i =>
    (ha i).1.resps_ref_eq_nil (not_decIn_of_super (ha i).2)
  have hresb : ∀ i, respsOf (b i) X.ref = [] := by
    intro i
    have := respsOf_prefix (show b i <+: a (i + 1) by
      rw [hab]; exact List.prefix_append _ _) X.ref
    rw [hres] at this; exact List.eq_nil_of_prefix_nil this
  have hnl : ∀ i, ∃ ℓ, X.nl (b i) X.ref = some ℓ := by
    intro i
    unfold nl
    split_ifs with h1 h2
    · exfalso
      rcases (hgb i).ref_counts with ⟨-, h3⟩ | ⟨h3, -⟩
      · rw [hresb i] at h3; simp at h3; exact h2.2 h3
      · exact h3 h1
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  have hmono : ∀ i, a i <+: a (i + 1) := fun i => by rw [ha_succ]; exact prefix_ext _ _
  have hlenab : ∀ i, (a i).length < (a (i + 1)).length ∧ (a i).length ≤ (b i).length ∧
      (b i).length < (a (i + 1)).length := by
    intro i
    obtain ⟨ℓ, hℓ⟩ := hnl i
    have h1 : (a i).length ≤ (b i).length := by simp [hb i, ext_eq_append]
    have h2 : (a (i + 1)).length = (b i).length + 1 := by rw [hab, ext1_of_some hℓ]; simp
    omega
  have hlen : ∀ i, i ≤ (a i).length := by
    intro i
    induction i with
    | zero => simp [ha0]
    | succ i ih => have := (hlenab i).1; omega
  obtain ⟨e, hlbl, hadm, hcfg⟩ := X.chain_infExec a hmono hlen (fun i => (ha i).1)
  have hmono' : ∀ i j, i ≤ j → a i <+: a j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact List.prefix_refl _
    | succ j _ ih => exact ih.trans (hmono j)
  have hinv1 : opsOf (a 1) X.ref ≠ [] := by
    have h0 := hab 0; simp only [zero_add] at h0
    rw [h0]; exact (hgb 0).opsOf_ext1_ref_ne_nil
  -- the referee is pending forever after `a 1`
  have hpend : ∀ m ≥ (a 1).length, (e.cfg m).pend X.ref ≠ none := by
    intro m hm
    have hm1 : 1 ≤ m := by have := hlen 1; omega
    obtain ⟨hgt, hct⟩ := hcfg m m (hlen m)
    rw [← hct]
    apply hgt.pend_ref_ne_none_iff.2
    constructor
    · have hp : a 1 <+: (a m).take m := List.prefix_take_iff.2 ⟨hmono' 1 m hm1, hm⟩
      have := opsOf_prefix hp X.ref
      intro h; rw [h] at this; exact hinv1 (List.eq_nil_of_prefix_nil this)
    · have := respsOf_prefix (List.take_prefix m (a m)) X.ref
      rw [hres] at this; exact List.eq_nil_of_prefix_nil this
  obtain ⟨N', hN'⟩ := X.wf e hadm X.ref (a 1).length hpend
  -- the referee's step in round `N' + 1` is internal
  set i := N' + 1 with hi
  obtain ⟨ℓ, hℓ⟩ := hnl i
  have hstep := ((hgb i).nl_step hℓ).1
  rw [← ext1_of_some hℓ, ← hab] at hstep
  have hpb : (X.cfg (b i)).pend X.ref ≠ none := by
    apply (hgb i).pend_ref_ne_none_iff.2 ⟨?_, hresb i⟩
    have h1 : a 1 <+: b i := (hmono' 1 i (by omega)).trans (by rw [hb]; exact prefix_ext _ _)
    have := opsOf_prefix h1 X.ref
    intro h; rw [h] at this; exact hinv1 (List.eq_nil_of_prefix_nil this)
  have hpa : (X.cfg (a (i + 1))).pend X.ref ≠ none := by
    have := hpend (a (i + 1)).length (by
      have := (hmono' 1 (i + 1) (by omega)).length_le; omega)
    have h2 := (hcfg (i + 1) (a (i + 1)).length le_rfl).2
    rw [List.take_length] at h2; rwa [h2]
  have htau : ℓ = .tau X.ref := X.I.eq_tau_of_step hstep (nl_proc hℓ) hpb hpa
  apply hN' (b i).length (by have := (hlenab i).2.1; have := hlen i; omega)
  rw [hlbl (i + 1) (b i).length (hlenab i).2.2, ← htau]
  simp only [hab, ext1_of_some hℓ]
  simp

/-! ### Generic parts of Lemmas 24 and 29 -/

/-- Closed executions have singleton valencies (Lemmas 21 and 27, as a hypothesis). -/
def Sing : Prop := ∀ α, X.Good α → X.Closed α → ∃ x, X.W α = {x}

/-- **Lemma 24(1) / Lemma 29(1) of [ACE26]** (generic part). Let `α` be helping with
`W(α) = ∅`. There is a competitors-only extension `β` such that `W(αβp) ∩ W(αβqp) = ∅` for
every competitor `q`. -/
theorem lemma24_1 [Fintype P] (hS : X.Sing) {α : List (LLabel P)} (hα : X.Good α)
    (hnd : X.NoDec α) (hh : X.Helping α) :
    ∃ σ, X.Comp σ ∧ ∀ q, q ≠ X.ref →
      Disjoint (X.W (X.ext α (σ ++ [X.ref]))) (X.W (X.ext α (σ ++ [q, X.ref]))) := by
  have hcl : ∀ σ, X.Comp σ → X.Closed (X.ext α (σ ++ [X.ref])) := hh
  obtain ⟨x, hx⟩ := hS _ (hα.ext _) (hcl [] comp_nil)
  have hsing : ∀ σ, X.Comp σ → ∃ y, X.W (X.ext α (σ ++ [X.ref])) = {y} :=
    fun σ hσ => hS _ (hα.ext _) (hcl σ hσ)
  obtain ⟨σ, hσ, hΦ, hcrit⟩ := X.exists_critical (fun σ => x ∈ X.W (X.ext α (σ ++ [X.ref])))
    (by rw [hx]; rfl) (by
      intro s hs hall
      obtain ⟨c', hc'⟩ := exists_infinitely_often s
      have hc'r : c' ≠ X.ref := by obtain ⟨m, -, hm⟩ := hc' 0; rw [← hm]; exact hs m
      obtain ⟨n, hn⟩ := X.resps_unbounded hα hs hc' x
      have hgn := hα.ext (pre s n)
      have hv : x < (respsOf (X.ext α (pre s n)) c').length := by
        rw [ext_eq_append, respsOf_append, List.length_append]; omega
      have hmem : x ∈ X.W (X.ext (X.ext α (pre s n)) [X.ref]) := by
        rw [← ext_append]; exact hall n
      exact not_mem_W_of_resps hgn (hnd _ (comp_pre hs n)) hc'r hv [X.ref] hmem)
  refine ⟨σ, hσ, fun q hq => ?_⟩
  obtain ⟨y₁, hy₁⟩ := hsing σ hσ
  rw [hy₁] at hΦ ⊢
  simp only [Set.mem_singleton_iff] at hΦ; subst hΦ
  have hσq : X.Comp (σ ++ [q]) := comp_append.2 ⟨hσ, comp_singleton hq⟩
  obtain ⟨y₂, hy₂⟩ := hsing _ hσq
  have hne := hcrit q hq
  simp only [List.append_assoc, List.singleton_append] at hy₂ hne
  rw [hy₂] at hne ⊢
  simp only [Set.mem_singleton_iff] at hne
  simp only [Set.disjoint_singleton]; exact hne

lemma resps_le_ext (β : List (LLabel P)) (σ : List P) (q : P) :
    (respsOf β q).length ≤ (respsOf (X.ext β σ) q).length := by
  rw [ext_eq_append, respsOf_append, List.length_append]; omega

/-- Valencies along a solo run of a competitor change as it completes more operations. -/
lemma eventually_ne [Fintype P] {α : List (LLabel P)} (hα : X.Good α) (hnd : X.NoDec α)
    {A G : List P} (hA : X.Comp A) (hG : X.Comp G) {q : P} (hq : q ≠ X.ref) (z : ℕ → ℕ)
    (hz : ∀ k, z k ∈ X.W (X.ext α (A ++ List.replicate k q ++ G ++ [X.ref]))) (v : ℕ) :
    ∃ ℓ₀, ∀ k ≥ ℓ₀, z k ≠ v := by
  obtain ⟨ℓ₀, hℓ₀⟩ := X.resps_unbounded (hα.ext A) (s := fun _ => q) (fun _ => hq)
    (c := q) (fun N => ⟨N, le_rfl, rfl⟩) v
  refine ⟨ℓ₀, fun k hk hzk => ?_⟩
  have hcomp : X.Comp (A ++ List.replicate k q ++ G) :=
    comp_append.2 ⟨comp_append.2 ⟨hA, comp_replicate hq k⟩, hG⟩
  have hgk := hα.ext (A ++ List.replicate k q ++ G)
  apply not_mem_W_of_resps hgk (hnd _ hcomp) hq (v := v) ?_ [X.ref]
  · rw [← ext_append]; rw [← hzk]; exact hz k
  · rw [ext_append, ext_append]
    have h1 := resps_le_ext (X := X) (X.ext (X.ext α A) (List.replicate k q)) G q
    have h2 : (respsOf (X.extL (X.ext α A) (List.replicate k q)) q).length ≤
        (respsOf (X.ext (X.ext α A) (List.replicate k q)) q).length := by
      rw [ext_eq_append (X.ext α A), respsOf_append, List.length_append]; omega
    have : (respsOf (X.extL (X.ext α A) (pre (fun _ => q) ℓ₀)) q).length ≤
        (respsOf (X.extL (X.ext α A) (List.replicate k q)) q).length := by
      obtain ⟨u, hu⟩ := pre_prefix (fun _ => q) hk
      rw [pre_const, pre_const] at hu
      rw [← hu, extL_append, respsOf_append, List.length_append, pre_const]; omega
    omega

/-- **Lemma 24(2) / Lemma 29(2) of [ACE26]** (generic part). Let `α` be helping with
`W(α) = ∅`, let `A`, `G`, `V` be competitors-only schedules and `q'` a competitor. There is a
`k ≥ 0` with
`W(α G p A q'^k V) ∩ W(α A q'^k G p V) = ∅` and `W(α A q'^(k+1) G p) ∩ W(α A q'^k G p q') = ∅`.
(For Lemma 24, `A = []`, `G = [q]`, `V = [q']`.) -/
theorem lemma24_2 [Fintype P] (hS : X.Sing) {α : List (LLabel P)} (hα : X.Good α)
    (hnd : X.NoDec α) (hh : X.Helping α) {A G V : List P} (hA : X.Comp A) (hG : X.Comp G)
    (hV : X.Comp V) {q' : P} (hq' : q' ≠ X.ref) :
    ∃ k, Disjoint (X.W (X.ext α (G ++ [X.ref] ++ A ++ List.replicate k q' ++ V)))
        (X.W (X.ext α (A ++ List.replicate k q' ++ G ++ [X.ref] ++ V))) ∧
      Disjoint (X.W (X.ext α (A ++ List.replicate (k + 1) q' ++ G ++ [X.ref])))
        (X.W (X.ext α (A ++ List.replicate k q' ++ G ++ [X.ref] ++ [q']))) := by
  classical
  have hcomp : ∀ k, X.Comp (A ++ List.replicate k q' ++ G) := fun k =>
    comp_append.2 ⟨comp_append.2 ⟨hA, comp_replicate hq' k⟩, hG⟩
  obtain ⟨y, hy⟩ := hS _ (hα.ext _) (hh G hG)
  have hz : ∀ k, ∃ z, X.W (X.ext α (A ++ List.replicate k q' ++ G ++ [X.ref])) = {z} :=
    fun k => hS _ (hα.ext _) (hh _ (hcomp k))
  choose z hz using hz
  have hzmem : ∀ k, z k ∈ X.W (X.ext α (A ++ List.replicate k q' ++ G ++ [X.ref])) := by
    intro k; rw [hz k]; rfl
  have hfirst : ∀ k, X.W (X.ext α (G ++ [X.ref] ++ A ++ List.replicate k q' ++ V)) = {y} := by
    intro k
    have : G ++ [X.ref] ++ A ++ List.replicate k q' ++ V =
        (G ++ [X.ref]) ++ (A ++ List.replicate k q' ++ V) := by simp
    rw [this, ext_append]
    exact W_ext_eq_of_closed (hα.ext _) (hh G hG) hy
      (comp_append.2 ⟨comp_append.2 ⟨hA, comp_replicate hq' k⟩, hV⟩) hq'
  have hsecond : ∀ k (U : List P), X.Comp U →
      X.W (X.ext α (A ++ List.replicate k q' ++ G ++ [X.ref] ++ U)) = {z k} := by
    intro k U hU
    rw [ext_append]
    exact W_ext_eq_of_closed (hα.ext _) (hh _ (hcomp k)) (hz k) hU hq'
  obtain ⟨ℓ₀, hℓ₀⟩ := X.eventually_ne hα hnd hA hG hq' z hzmem y
  obtain ⟨k, hk, hne⟩ : ∃ k ≥ ℓ₀, z k ≠ z (k + 1) := by
    by_contra hno
    push Not at hno
    have hconst : ∀ k ≥ ℓ₀, z k = z ℓ₀ := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => rfl
      | succ k hk ih => rw [← hno k hk, ih]
    obtain ⟨ℓ₁, hℓ₁⟩ := X.eventually_ne hα hnd hA hG hq' z hzmem (z ℓ₀)
    exact hℓ₁ (max ℓ₀ ℓ₁) (le_max_right _ _) (hconst _ (le_max_left _ _))
  refine ⟨k, ?_, ?_⟩
  · rw [hfirst, hsecond k V hV, Set.disjoint_singleton]; exact Ne.symm (hℓ₀ k hk)
  · rw [hz (k + 1), hsecond k [q'] (comp_singleton hq'), Set.disjoint_singleton]
    exact Ne.symm hne

/-- **Constant valency argument** (used for the test&set case of Theorem 30, where the paper's
argument has a gap). Let `α` be helping with `W(α) = ∅`, the referee pending and poised to take
an internal step after every competitors-only extension, and suppose that the referee's step
commutes with every competitor step after every competitors-only extension. Then we reach a
contradiction: by Lemma 17 the singleton `W(αup)` does not depend on `u`, while a competitor
completing many operations in `u` forbids every fixed output. -/
theorem const_valency_contra [Fintype P] (hS : X.Sing) {α : List (LLabel P)} (hα : X.Good α)
    (hnd : X.NoDec α) (hh : X.Helping α)
    (hpend : ∀ u, X.Comp u → (X.cfg (X.ext α (u ++ [X.ref]))).pend X.ref ≠ none)
    (hcomm : ∀ u, X.Comp u → ∀ c, c ≠ X.ref →
      X.cfg (X.ext α (u ++ [X.ref, c])) = X.cfg (X.ext α (u ++ [c, X.ref])))
    {c₀ : P} (hc₀ : c₀ ≠ X.ref) : False := by
  classical
  have hy : ∀ u, ∃ y, X.Comp u → X.W (X.ext α (u ++ [X.ref])) = {y} := by
    intro u
    by_cases hu : X.Comp u
    · obtain ⟨y, hy⟩ := hS _ (hα.ext _) (hh u hu); exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hu⟩
  choose y hy using hy
  have hconst : ∀ u, X.Comp u → y u = y [] := by
    intro u hu
    induction u using List.reverseRecOn with
    | nil => rfl
    | append_singleton u c ih =>
      obtain ⟨hu', hc⟩ := comp_append.1 hu
      have hc' : c ≠ X.ref := hc c (by simp)
      have hcl : X.Closed (X.ext α (u ++ [X.ref, c])) := by
        have : u ++ [X.ref, c] = (u ++ [X.ref]) ++ [c] := by simp
        rw [this, ext_append]; exact (hh u hu').ext (hα.ext _) (comp_singleton hc')
      have hg1 := hα.ext (u ++ [X.ref, c])
      have hg2 := hα.ext (u ++ [c, X.ref])
      have hp : (X.cfg (X.ext α (u ++ [X.ref, c]))).pend X.ref ≠ none := by
        have : u ++ [X.ref, c] = (u ++ [X.ref]) ++ [c] := by simp
        rw [this, ext_append, ext_singleton, (((hα.ext _)).ext1_other (Ne.symm hc')).2]
        exact hpend u hu'
      have hag : AgreeOn Set.univ (X.cfg (X.ext α (u ++ [X.ref, c])))
          (X.cfg (X.ext α (u ++ [c, X.ref]))) := by
        rw [hcomm u hu' c hc']; exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩
      obtain ⟨z, hz1, hz2⟩ := X.lemma17 hg1 hg2 hcl hp hc' (Set.mem_univ c)
        (Set.mem_univ _) hag
      have e1 : u ++ [X.ref, c] = (u ++ [X.ref]) ++ [c] := by simp
      have e2 : u ++ [c, X.ref] = (u ++ [c]) ++ [X.ref] := by simp
      rw [e1, ext_append] at hz1
      have hz1' := W_ext_subset _ (comp_singleton hc') hz1
      rw [hy u hu'] at hz1'
      rw [e2, hy _ hu] at hz2
      simp only [Set.mem_singleton_iff] at hz1' hz2
      rw [← ih hu', ← hz1', hz2]
  obtain ⟨n, hn⟩ := X.resps_unbounded hα (s := fun _ => c₀) (fun _ => hc₀) (c := c₀)
    (fun N => ⟨N, le_rfl, rfl⟩) (y [])
  rw [pre_const] at hn
  have hcomp : X.Comp (List.replicate n c₀) := comp_replicate hc₀ n
  apply not_mem_W_of_resps (hα.ext _) (hnd _ hcomp) hc₀ (v := y []) ?_ [X.ref]
  · rw [← ext_append, hy _ hcomp, hconst _ hcomp]; rfl
  · rw [ext_eq_append, respsOf_append, List.length_append]; omega

end LLCtx

end Cslib.SharedMemory.Referee
