import Papers.PODC2022.ConsensusFromSwap.Model

/-!
# Valency of a set of processes; Lemmas 13 and 14 (Section 5)

Binary consensus (`V = Bool`). We fix a base configuration `C₀` (an initial configuration) and
assume agreement and solo termination for all configurations reachable from it (`Setting`).

* `CanDec Q C v`: there is a `Q`-only execution from `C` after which some process of `Q` has
  decided `v` (decisions taken before `C` count; this makes "`Q` is `v`-univalent" =
  `¬ CanDec Q C (!v)` well behaved, see `differencies.md`).
* `Biv Q C`: `Q` is bivalent in `C`; `Q` is univalent iff `¬ Biv Q C`.
* `ptrace C p α`: the local states of `p` before each of its steps in the execution `α` from
  `C`; `Indist p C α C' α'` (the paper's `α ∼_p α'`): same states before every step and the same
  final state.

Main results: `lemma13` (block updates after a `Q`-only execution keep `Q` bivalent) and
`lemma14` (the key lemma of Section 5), both for arbitrary objects; covering processes must be
poised to apply an operation that overwrites the object (e.g. `Swap`).
-/

namespace ConsensusFromSwap

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {P : Type} [DecidableEq P]
  {A : Alg T P Bool}

/-! ## Valency -/

/-- Some `Q`-only execution from `C` leads to a configuration where a process of `Q` has decided
`v`. -/
def CanDec (Q : Set P) (C : Cfg A) (v : Bool) : Prop :=
  ∃ β : List P, (∀ r ∈ β, r ∈ Q) ∧ ∃ q ∈ Q, (run C β).Out q v

/-- `Q` is bivalent in `C`. -/
def Biv (Q : Set P) (C : Cfg A) : Prop := CanDec Q C false ∧ CanDec Q C true

/-- `C` is reachable from `C₀`. -/
def Reach (C₀ C : Cfg A) : Prop := ∃ α, run C₀ α = C

/-- The assumptions of Section 5 on a binary consensus algorithm, relative to an initial
configuration `C₀`: agreement and solo termination in all reachable configurations. -/
structure Setting (C₀ : Cfg A) : Prop where
  /-- Agreement. -/
  agree : ∀ α p q u w, (run C₀ α).Out p u → (run C₀ α).Out q w → u = w
  /-- Solo termination (obstruction-freedom). -/
  of : ∀ α p, ∃ t, (run (run C₀ α) (solo p t)).Dec p

/-- `p` is poised to apply an operation to object `i` that sets `i` to a value independent of its
old value (for swap objects: a `Swap`): `p` *covers* `i`. -/
def Cfg.Covers (C : Cfg A) (p : P) (i : ι) : Prop :=
  ∃ o k, A.act (C.loc p) = .access i o k ∧ ∀ s s', ((T i).δ s o).1 = ((T i).δ s' o).1

lemma Cfg.Covers.poised {C : Cfg A} {p : P} {i : ι} (h : C.Covers p i) : C.Poised p i := by
  obtain ⟨o, k, h, -⟩ := h
  exact ⟨o, k, h⟩

lemma Reach.run {C₀ C : Cfg A} (h : Reach C₀ C) (β : List P) :
    Reach C₀ (ConsensusFromSwap.run C β) := by
  obtain ⟨α, rfl⟩ := h
  exact ⟨α ++ β, run_append _ _ _⟩

lemma Reach.refl (C₀ : Cfg A) : Reach C₀ C₀ := ⟨[], rfl⟩

section Setting

variable {C₀ : Cfg A} (hS : Setting C₀)
include hS

lemma Setting.agree' {C : Cfg A} (hC : Reach C₀ C) {p q : P} {u w : Bool} (hp : C.Out p u)
    (β : List P) (hq : (run C β).Out q w) : u = w := by
  obtain ⟨α, rfl⟩ := hC
  rw [← run_append] at hq
  exact hS.agree _ p q u w (by rw [run_append]; exact hp.run β) hq

lemma Setting.of' {C : Cfg A} (hC : Reach C₀ C) (p : P) : ∃ t, (run C (solo p t)).Dec p := by
  obtain ⟨α, rfl⟩ := hC
  exact hS.of α p

/-- A decided process makes every set of processes univalent. -/
lemma Setting.not_biv_of_dec {C : Cfg A} (hC : Reach C₀ C) {p : P} (hp : C.Dec p) (Q : Set P) :
    ¬ Biv Q C := by
  rintro ⟨⟨β₀, -, q₀, -, h₀⟩, ⟨β₁, -, q₁, -, h₁⟩⟩
  obtain ⟨u, hu⟩ := hp
  have e0 := hS.agree' hC hu β₀ h₀
  have e1 := hS.agree' hC hu β₁ h₁
  rw [e0] at e1
  exact Bool.false_ne_true e1

lemma Setting.not_dec_of_biv {C : Cfg A} (hC : Reach C₀ C) {Q : Set P} (h : Biv Q C) (p : P) :
    ¬ C.Dec p := fun hp => hS.not_biv_of_dec hC hp Q h

/-- If `Q` cannot decide `!v` from `C`, then every `q ∈ Q` running solo decides `v`. -/
lemma Setting.solo_out_of_not_canDec {C : Cfg A} (hC : Reach C₀ C) {Q : Set P} {v : Bool}
    (h : ¬ CanDec Q C (!v)) {q : P} (hq : q ∈ Q) : ∃ t, (run C (solo q t)).Out q v := by
  obtain ⟨t, w, hw⟩ := hS.of' hC q
  refine ⟨t, ?_⟩
  cases hwv : w == v with
  | true => rwa [beq_iff_eq.1 hwv] at hw
  | false =>
    exfalso
    have : w = !v := by cases w <;> cases v <;> simp_all
    exact h ⟨solo q t, fun r hr => by rw [List.eq_of_mem_replicate hr]; exact hq, q, hq,
      this ▸ hw⟩

end Setting

lemma AgreeOn.canDec_iff {R Q : Set P} {C D : Cfg A} (h : AgreeOn R C D) (hQR : Q ⊆ R)
    {v : Bool} : CanDec Q C v ↔ CanDec Q D v := by
  constructor
  · rintro ⟨β, hβ, q, hq, h'⟩
    exact ⟨β, hβ, q, hq, ((h.run (fun r hr => hQR (hβ r hr))).out_iff (hQR hq)).1 h'⟩
  · rintro ⟨β, hβ, q, hq, h'⟩
    exact ⟨β, hβ, q, hq, ((h.run (fun r hr => hQR (hβ r hr))).out_iff (hQR hq)).2 h'⟩

lemma AgreeOn.biv_iff {R Q : Set P} {C D : Cfg A} (h : AgreeOn R C D) (hQR : Q ⊆ R) :
    Biv Q C ↔ Biv Q D := by
  simp only [Biv, h.canDec_iff hQR]

lemma CanDec.of_run {Q : Set P} {C : Cfg A} {v : Bool} {β : List P} (hβ : ∀ r ∈ β, r ∈ Q)
    (h : CanDec Q (run C β) v) : CanDec Q C v := by
  obtain ⟨γ, hγ, q, hq, h'⟩ := h
  refine ⟨β ++ γ, fun r hr => ?_, q, hq, by rwa [run_append]⟩
  rcases List.mem_append.1 hr with hr | hr
  · exact hβ r hr
  · exact hγ r hr

lemma CanDec.of_out {Q : Set P} {C : Cfg A} {v : Bool} {q : P} (hq : q ∈ Q) (h : C.Out q v) :
    CanDec Q C v := ⟨[], by simp, q, hq, h⟩

/-! ## Blocks of covering processes -/

/-- `cs` is a list of `(process, object)` pairs with distinct processes, each covering its
object in `C`. (Distinctness of the objects is not needed here.) -/
def Covering (C : Cfg A) (cs : List (P × ι)) : Prop :=
  (cs.map Prod.fst).Nodup ∧ ∀ c ∈ cs, C.Covers c.1 c.2

/-- The block update by the processes of `cs`. -/
def block (cs : List (P × ι)) : List P := cs.map Prod.fst

lemma Cfg.Covers.of_loc {C D : Cfg A} {p : P} {i : ι} (h : C.Covers p i)
    (hl : D.loc p = C.loc p) : D.Covers p i := by
  obtain ⟨o, k, h1, h2⟩ := h
  exact ⟨o, k, by rw [hl]; exact h1, h2⟩

lemma Covering.of_loc {C D : Cfg A} {cs : List (P × ι)} (h : Covering C cs)
    (hl : ∀ c ∈ cs, D.loc c.1 = C.loc c.1) : Covering D cs :=
  ⟨h.1, fun c hc => (h.2 c hc).of_loc (hl c hc)⟩

lemma Covering.run {C : Cfg A} {cs : List (P × ι)} (h : Covering C cs) {β : List P}
    (hβ : ∀ r ∈ β, r ∉ block cs) : Covering (ConsensusFromSwap.run C β) cs :=
  h.of_loc fun _c hc => run_loc_other C β fun r hr hrc =>
    hβ r hr (hrc ▸ List.mem_map_of_mem hc)

lemma mem_block {cs : List (P × ι)} {p : P} : p ∈ block cs ↔ ∃ i, (p, i) ∈ cs := by
  simp [block]

/-- After a block update, the covered objects have values determined by the states of the
covering processes: configurations agreeing on the covering processes and on all other objects
have the same memory after the block. -/
lemma block_mem_eq {C D : Cfg A} {cs : List (P × ι)} (hC : Covering C cs) (hD : Covering D cs)
    (hl : ∀ c ∈ cs, C.loc c.1 = D.loc c.1)
    (hm : ∀ j, (∀ c ∈ cs, c.2 ≠ j) → C.mem j = D.mem j) :
    (run C (block cs)).mem = (run D (block cs)).mem := by
  induction cs generalizing C D with
  | nil => funext j; exact hm j (by simp)
  | cons c cs ih =>
    obtain ⟨p, i⟩ := c
    have hnd := hC.1
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hpC := hC.2 (p, i) (by simp)
    have hpD := hD.2 (p, i) (by simp)
    obtain ⟨o, k, h1, h2⟩ := hpC
    have h1' : A.act (D.loc p) = .access i o k := by
      rw [← hl (p, i) (by simp)]; exact h1
    simp only [block, List.map_cons, run_cons]
    have hnot : ∀ c ∈ cs, c.1 ≠ p := fun c hc h => hnd.1 (h ▸ List.mem_map_of_mem hc)
    refine ih ?_ ?_ ?_ ?_
    · refine ⟨hnd.2, fun c hc => (hC.2 c (by simp [hc])).of_loc ?_⟩
      exact C.step_loc_other (hnot c hc)
    · refine ⟨hnd.2, fun c hc => (hD.2 c (by simp [hc])).of_loc ?_⟩
      exact D.step_loc_other (hnot c hc)
    · intro c hc
      rw [C.step_loc_other (hnot c hc), D.step_loc_other (hnot c hc)]
      exact hl c (by simp [hc])
    · intro j hj
      rw [C.step_of_access h1, D.step_of_access h1']
      by_cases hji : j = i
      · subst hji; simp only [Function.update_self]; exact h2 _ _
      · simp only [Function.update_of_ne hji]
        exact hm j (by
          intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact Ne.symm hji
          · exact hj c hc)

/-- A step of a process that is not poised on any covered object commutes with the block. -/
lemma block_comm {C : Cfg A} {cs : List (P × ι)} (hC : Covering C cs) {s : P}
    (hs : s ∉ block cs) (hsp : ∀ c ∈ cs, ¬ C.Poised s c.2) :
    run C (block cs ++ [s]) = run C (s :: block cs) := by
  induction cs generalizing C with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨p, i⟩ := c
    have hnd := hC.1
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hsp' : s ≠ p := fun h => hs (by simp [block, h])
    have hnot : ∀ c ∈ cs, c.1 ≠ p := fun c hc h => hnd.1 (h ▸ List.mem_map_of_mem hc)
    have hih := ih (C := C.step p)
      ⟨hnd.2, fun c hc => (hC.2 c (by simp [hc])).of_loc (C.step_loc_other (hnot c hc))⟩
      (fun h => hs (by simp [block] at h ⊢; exact Or.inr h))
      (fun c hc h => by
        rw [Cfg.Poised, C.step_loc_other hsp'] at h
        exact hsp c (by simp [hc]) h)
    simp only [block, run_cons] at hih
    simp only [block, List.map_cons, List.cons_append, run_cons]
    rw [hih, C.step_comm (Ne.symm hsp')]
    intro j hj hsj
    obtain ⟨o, k, h1, -⟩ := hC.2 (p, i) (by simp)
    obtain ⟨o', k', h1'⟩ := hj
    rw [h1] at h1'
    cases h1'
    exact hsp (p, i) (by simp) hsj

/-- The block update does not change the local states of other processes. -/
lemma run_block_loc_other (C : Cfg A) (cs : List (P × ι)) {q : P} (hq : q ∉ block cs) :
    (run C (block cs)).loc q = C.loc q :=
  run_loc_other C _ (fun _r hr h => hq (h ▸ hr))

/-- The block update only changes covered objects. -/
lemma run_block_mem_other {C : Cfg A} {cs : List (P × ι)} (hC : Covering C cs) {j : ι}
    (hj : ∀ c ∈ cs, c.2 ≠ j) : (run C (block cs)).mem j = C.mem j := by
  induction cs generalizing C with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨p, i⟩ := c
    have hnd := hC.1
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hnot : ∀ c ∈ cs, c.1 ≠ p := fun c hc h => hnd.1 (h ▸ List.mem_map_of_mem hc)
    simp only [block, List.map_cons, run_cons]
    have := ih (C := C.step p) ⟨hnd.2, fun c hc => (hC.2 c (by simp [hc])).of_loc
      (C.step_loc_other (hnot c hc))⟩ (fun c hc => hj c (by simp [hc]))
    rw [block] at this
    rw [this]
    exact C.step_mem_other (hC.2 (p, i) (by simp)).poised (Ne.symm (hj (p, i) (by simp)))

/-! ## Lemma 13 -/

section Lemma13

variable {C₀ : Cfg A} (hS : Setting C₀)
include hS

/-- **Lemma 13** of [Ovens 2022]: if `Q = {q₀, q₁}` is bivalent in `C` and processes outside `Q`
cover objects, then there is a `Q`-only execution `γ` from `C` such that `Q` is bivalent after
`γ` followed by the block update `β`. (For arbitrary objects; covering = poised on an operation
that overwrites the object.) -/
theorem lemma13 {q₀ q₁ : P} (hq : q₀ ≠ q₁) {C : Cfg A} (hC : Reach C₀ C)
    (hb : Biv {q₀, q₁} C) {cs : List (P × ι)} (hcov : Covering C cs)
    (hQ : ∀ c ∈ cs, c.1 ≠ q₀ ∧ c.1 ≠ q₁) :
    ∃ γ : List P, (∀ r ∈ γ, r ∈ ({q₀, q₁} : Set P)) ∧
      Biv {q₀, q₁} (run C (γ ++ block cs)) := by
  classical
  set Q : Set P := {q₀, q₁}
  have hQb : ∀ q ∈ Q, q ∉ block cs := by
    intro q hq hqb
    obtain ⟨i, hi⟩ := mem_block.1 hqb
    rcases hq with rfl | rfl
    · exact (hQ _ hi).1 rfl
    · exact (hQ _ hi).2 rfl
  by_cases h0 : Biv Q (run C (block cs))
  · exact ⟨[], by simp, h0⟩
  -- `Q` is `!u`-univalent in `Cβ`
  obtain ⟨u, hu⟩ : ∃ u, ¬ CanDec Q (run C (block cs)) u := by
    by_contra h
    push Not at h
    exact h0 ⟨h false, h true⟩
  obtain ⟨α, hα, q, hqQ, hqα⟩ : CanDec Q C u := by cases u; exacts [hb.1, hb.2]
  -- the first prefix of `α` after which `Q` can decide `u` after the block
  let f : ℕ → Prop := fun m => CanDec Q (run C (α.take m ++ block cs)) u
  have hfα : f α.length := by
    simp only [f, List.take_length]
    refine CanDec.of_out hqQ ?_
    rw [run_append, Cfg.Out, run_block_loc_other _ _ (hQb q hqQ)]
    exact hqα
  have hex : ∃ m, f m := ⟨_, hfα⟩
  set m := Nat.find hex
  have hfm : f m := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h
    have := hfm
    simp only [f, h, List.take_zero, List.nil_append] at this
    exact hu this
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hfm' : ¬ f m' := Nat.find_min hex (by omega)
  have hmlen : m' < α.length := by
    by_contra hc
    push Not at hc
    apply hfm'
    simp only [f, List.take_of_length_le hc]
    simpa [f, List.take_of_length_le (by omega : α.length ≤ m)] using hfm
  set s := α[m']
  have htake : α.take m = α.take m' ++ [s] := by
    rw [hm']; exact List.take_succ_eq_append_getElem hmlen
  have hsQ : s ∈ Q := hα s (List.getElem_mem hmlen)
  set α' := α.take m'
  have hα' : ∀ r ∈ α', r ∈ Q := fun r hr => hα r (List.mem_of_mem_take hr)
  set E := run C α'
  have hE : Reach C₀ E := hC.run α'
  have hcovE : Covering E cs := hcov.run (fun r hr => hQb r (hα' r hr))
  have hsb : s ∉ block cs := hQb s hsQ
  -- `Q` is `!u`-univalent after `α'` and the block
  have hnu : ¬ CanDec Q (run E (block cs)) u := by
    have := hfm'; simp only [f, run_append] at this; exact this
  have hu' : CanDec Q (run (E.step s) (block cs)) u := by
    have := hfm; simp only [f, htake, run_append] at this; exact this
  refine ⟨α' ++ [s], fun r hr => ?_, ?_⟩
  · rcases List.mem_append.1 hr with hr | hr
    · exact hα' r hr
    · rw [List.mem_singleton.1 hr]; exact hsQ
  rw [run_append, run_concat]
  by_cases hcase : ∃ c ∈ cs, E.Poised s c.2
  · -- `s` accesses a covered object: the other process of `Q` cannot tell the difference
    obtain ⟨c, hc, hsc⟩ := hcase
    obtain ⟨q', hq'Q, hq's⟩ : ∃ q' ∈ Q, q' ≠ s := by
      rcases hsQ with h | h
      · exact ⟨q₁, by simp [Q], by rw [h]; exact Ne.symm hq⟩
      · exact ⟨q₀, by simp [Q], by rw [show s = q₁ from h]; exact hq⟩
    have hcovEs : Covering (E.step s) cs := hcovE.of_loc fun c hc =>
      E.step_loc_other (fun h => hsb (h ▸ List.mem_map_of_mem hc))
    have hmem : (run (E.step s) (block cs)).mem = (run E (block cs)).mem := by
      refine block_mem_eq hcovEs hcovE (fun c hc => E.step_loc_other
        (fun h => hsb (h ▸ List.mem_map_of_mem hc))) (fun j hj => ?_)
      refine E.step_mem_other hsc ?_
      intro h; exact hj c hc h.symm
    have hag : AgreeOn {q'} (run E (block cs)) (run (E.step s) (block cs)) := by
      refine ⟨hmem.symm, fun r hr => ?_⟩
      rw [Set.mem_singleton_iff.1 hr, run_block_loc_other _ _ (hQb q' hq'Q),
        run_block_loc_other _ _ (hQb q' hq'Q), E.step_loc_other hq's]
    have hu1 : ¬ CanDec Q (run E (block cs)) (!(!u)) := by simpa using hnu
    obtain ⟨t, ht⟩ := hS.solo_out_of_not_canDec (hE.run _) hu1 hq'Q
    have ht' := ((hag.run (α := solo q' t) (fun r hr => by
      rw [List.eq_of_mem_replicate hr]; rfl)).out_iff rfl).1 ht
    have hcd : CanDec Q (run (E.step s) (block cs)) (!u) :=
      ⟨solo q' t, fun r hr => by rw [List.eq_of_mem_replicate hr]; exact hq'Q, q', hq'Q, ht'⟩
    cases u
    · exact ⟨hu', hcd⟩
    · exact ⟨hcd, hu'⟩
  · -- `s` accesses another object (or has decided): it commutes with the block
    push Not at hcase
    have hcomm := block_comm hcovE hsb hcase
    rw [run_cons] at hcomm
    rw [← hcomm, run_concat]
    have hu1 : ¬ CanDec Q (run E (block cs)) (!(!u)) := by simpa using hnu
    have hreach : Reach C₀ ((run E (block cs)).step s) := by
      rw [← run_singleton]; exact (hE.run _).run _
    obtain ⟨t, w, hw⟩ := hS.of' hreach s
    have hw' : w = !u := by
      by_contra hne
      have : w = u := by cases w <;> cases u <;> simp_all
      subst this
      exact hnu ⟨s :: solo s t, fun r hr => by
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact hsQ
        · rw [List.eq_of_mem_replicate hr]; exact hsQ, s, hsQ, by
          rw [run_cons]; exact hw⟩
    subst hw'
    have hcd : CanDec Q ((run E (block cs)).step s) (!u) :=
      ⟨solo s t, fun r hr => by rw [List.eq_of_mem_replicate hr]; exact hsQ, s, hsQ, hw⟩
    rw [← hcomm] at hu'
    rw [run_concat] at hu'
    cases u
    · exact ⟨hu', hcd⟩
    · exact ⟨hcd, hu'⟩

end Lemma13

/-! ## Indistinguishability of executions to one process -/

/-- The local states of `p` before each of its steps in the execution `α` from `C`. -/
def ptrace (C : Cfg A) (p : P) : List P → List A.L
  | [] => []
  | r :: α => (if r = p then [C.loc p] else []) ++ ptrace (C.step r) p α

/-- The paper's `α ∼_p α'` for executions `α` from `C` and `α'` from `C'`: `p` is in the same
states before each of its steps and in the same final state. (Deterministic processes: the
operations applied by `p` are determined by these states.) -/
def Indist (p : P) (C : Cfg A) (α : List P) (C' : Cfg A) (α' : List P) : Prop :=
  ptrace C p α = ptrace C' p α' ∧ (run C α).loc p = (run C' α').loc p

@[simp] lemma ptrace_nil (C : Cfg A) (p : P) : ptrace C p [] = [] := rfl

lemma ptrace_append (C : Cfg A) (p : P) (α β : List P) :
    ptrace C p (α ++ β) = ptrace C p α ++ ptrace (run C α) p β := by
  induction α generalizing C with
  | nil => simp
  | cons r α ih => simp [ptrace, ih, List.append_assoc]

lemma ptrace_of_not_mem (C : Cfg A) {p : P} {α : List P} (h : ∀ r ∈ α, r ≠ p) :
    ptrace C p α = [] := by
  induction α generalizing C with
  | nil => rfl
  | cons r α ih =>
    simp only [ptrace, h r (by simp), ite_false, List.nil_append]
    exact ih _ (fun r' hr' => h r' (by simp [hr']))

lemma ptrace_singleton (C : Cfg A) (p : P) : ptrace C p [p] = [C.loc p] := by
  simp [ptrace]

/-- Membership in a trace: `p` was in state `l` right before one of its steps. -/
lemma mem_ptrace {C : Cfg A} {p : P} {α : List P} {l : A.L} (h : l ∈ ptrace C p α) :
    ∃ α₁ α₂, α = α₁ ++ p :: α₂ ∧ (run C α₁).loc p = l := by
  induction α generalizing C with
  | nil => simp at h
  | cons r α ih =>
    simp only [ptrace, List.mem_append] at h
    rcases h with h | h
    · split_ifs at h with hr
      · subst hr
        simp only [List.mem_singleton] at h
        exact ⟨[], α, rfl, h.symm⟩
      · simp at h
    · obtain ⟨α₁, α₂, rfl, h2⟩ := ih h
      exact ⟨r :: α₁, α₂, rfl, h2⟩

lemma solo_mem_ptrace (C : Cfg A) (p : P) {t s : ℕ} (hs : s < t) :
    (run C (solo p s)).loc p ∈ ptrace C p (solo p t) := by
  obtain ⟨d, rfl⟩ : ∃ d, t = s + 1 + d := ⟨t - s - 1, by omega⟩
  rw [solo_add, solo_succ, ptrace_append, ptrace_append, ptrace_singleton]
  simp

lemma indist_refl_nil {p : P} {C C' : Cfg A} (h : C.loc p = C'.loc p) :
    Indist p C [] C' (solo p 0) := ⟨rfl, h⟩

/-- Extending both executions: other processes' steps on the left, then one step of `p` on both
sides from states with the same value of the accessed object. -/
lemma Indist.extend {p : P} {C C' : Cfg A} {α : List P} {j : ℕ}
    (h : Indist p C α C' (solo p j)) {lam : List P} (hlam : ∀ r ∈ lam, r ≠ p) {i : ι}
    (hpi : (run C' (solo p j)).Poised p i)
    (hmem : (run (run C α) lam).mem i = (run C' (solo p j)).mem i) :
    Indist p C (α ++ lam ++ [p]) C' (solo p (j + 1)) := by
  obtain ⟨htr, hloc⟩ := h
  have hloc' : (run (run C α) lam).loc p = (run C' (solo p j)).loc p := by
    rw [run_loc_other _ _ hlam, hloc]
  obtain ⟨o, k, hpa⟩ := hpi
  have hpa' : A.act ((run (run C α) lam).loc p) = .access i o k := by rw [hloc']; exact hpa
  refine ⟨?_, ?_⟩
  · rw [ptrace_append, ptrace_append, ptrace_of_not_mem _ hlam, solo_succ, ptrace_append,
      ptrace_singleton, ptrace_singleton, htr, List.append_nil, run_append, hloc']
  · rw [run_concat, run_append, solo_succ, run_concat,
      Cfg.step_of_access _ hpa', Cfg.step_of_access _ hpa]
    simp [hmem]

lemma Indist.append_other {p : P} {C C' : Cfg A} {α α' : List P}
    (h : Indist p C α C' α') {lam : List P} (hlam : ∀ r ∈ lam, r ≠ p) :
    Indist p C (α ++ lam) C' α' := by
  obtain ⟨htr, hloc⟩ := h
  refine ⟨?_, ?_⟩
  · rw [ptrace_append, ptrace_of_not_mem _ hlam, List.append_nil, htr]
  · rw [run_append, run_loc_other _ _ hlam, hloc]

/-! ## Lemma 14 -/

section Lemma14

variable {C₀ : Cfg A} (hS : Setting C₀)
include hS

/-- **Lemma 14** of [Ovens 2022] (for arbitrary objects). Let `Q ⊆ R`, `p ∉ R` (the paper:
`R = Q ∪ P_{i+1}`, `p = p_i`), let `Q` be bivalent in `C` and `C ∼_p C'`, and let `δ` be `p`'s solo
execution from `C'`. Then there is `j` such that
* (a) for every `j' ≤ j` there is an `(R ∪ {p})`-only execution `α` from `C` with `Q` bivalent in
  `Cα` and `α ∼_p δ_{j'}`;
* `p` is poised on some object `B` with operation `d` in `C'δ_j`, and for every `α` as in (a) for
  `j` and every `R`-only execution `λ` from `Cα`:
* (b) if `value(B, Cαλ) = value(B, C'δ_j)` then `Q` is univalent in `Cαλd`;
* (c) if `d` does not change `value(B, C'δ_j)` and `B` has this value in some configuration of
  `λ`, then `Q` is univalent in `Cαλ`. -/
theorem lemma14 {Q R : Set P} (hQR : Q ⊆ R) {p : P} (hpR : p ∉ R) {C C' : Cfg A}
    (hC : Reach C₀ C) (hC' : Reach C₀ C') (hb : Biv Q C) (hl : C.loc p = C'.loc p) :
    ∃ j : ℕ,
      (∀ j' ≤ j, ∃ α : List P, (∀ r ∈ α, r ∈ insert p R) ∧ Biv Q (run C α) ∧
        Indist p C α C' (solo p j')) ∧
      ∃ (B : ι) (o : (T B).Op) (k : (T B).Resp → A.L),
        A.act ((run C' (solo p j)).loc p) = .access B o k ∧
        ∀ α : List P, (∀ r ∈ α, r ∈ insert p R) → Biv Q (run C α) →
          Indist p C α C' (solo p j) → ∀ lam : List P, (∀ r ∈ lam, r ∈ R) →
          ((run (run C α) lam).mem B = (run C' (solo p j)).mem B →
              ¬ Biv Q (run (run C α) (lam ++ [p]))) ∧
          (((T B).δ ((run C' (solo p j)).mem B) o).1 = (run C' (solo p j)).mem B →
            (∃ l₁ l₂, lam = l₁ ++ l₂ ∧
              (run (run C α) l₁).mem B = (run C' (solo p j)).mem B) →
            ¬ Biv Q (run (run C α) lam)) := by
  classical
  let G : ℕ → Prop := fun m => ∀ α : List P, (∀ r ∈ α, r ∈ insert p R) →
    Indist p C α C' (solo p m) → ¬ Biv Q (run C α)
  have hex : ∃ m, G m := by
    obtain ⟨t, ht⟩ := hS.of' hC' p
    obtain ⟨w, hw⟩ := ht
    exact ⟨t, fun α _ hind => hS.not_biv_of_dec (hC.run α) (p := p)
      ⟨w, by rw [Cfg.Out, hind.2]; exact hw⟩ Q⟩
  set m := Nat.find hex
  have hGm : G m := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    have := hGm
    rw [h0] at this
    exact this [] (by simp) (indist_refl_nil hl) hb
  obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have ha : ∀ j' ≤ j, ∃ α : List P, (∀ r ∈ α, r ∈ insert p R) ∧ Biv Q (run C α) ∧
      Indist p C α C' (solo p j') := by
    intro j' hj'
    have := Nat.find_min hex (show j' < m by omega)
    simp only [G, not_forall, not_not] at this
    obtain ⟨α, hα, hind, hbiv⟩ := this
    exact ⟨α, hα, hbiv, hind⟩
  -- `p` is poised in `C'δ_j`
  obtain ⟨αj, hαj, hbj, hindj⟩ := ha j le_rfl
  have hnd : ¬ (run C' (solo p j)).Dec p := by
    intro hd
    apply hS.not_dec_of_biv (hC.run αj) hbj p
    obtain ⟨w, hw⟩ := hd
    exact ⟨w, by rw [Cfg.Out, hindj.2]; exact hw⟩
  obtain ⟨B, hBp⟩ : ∃ B, (run C' (solo p j)).Poised p B := by
    rcases (run C' (solo p j)).dec_or_poised p with h | h
    · exact absurd h hnd
    · exact h
  obtain ⟨o, k, hpa⟩ := hBp
  have hGj : G (j + 1) := hj ▸ hGm
  refine ⟨j, ha, B, o, k, hpa, ?_⟩
  intro α hα _ hind lam hlam
  have hlamp : ∀ r ∈ lam, r ≠ p := fun r hr h => hpR (h ▸ hlam r hr)
  have hαlam : ∀ (l : List P), (∀ r ∈ l, r ∈ R) → ∀ r ∈ α ++ l ++ [p], r ∈ insert p R := by
    intro l hl r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (hr | hr) | hr
    · exact hα r hr
    · exact Set.mem_insert_of_mem _ (hl r hr)
    · exact hr ▸ Set.mem_insert _ _
  refine ⟨fun hmem => ?_, fun hd hex' => ?_⟩
  · -- (b)
    have := hGj (α ++ lam ++ [p]) (hαlam lam hlam) (hind.extend hlamp ⟨o, k, hpa⟩ hmem)
    rwa [List.append_assoc, run_append] at this
  · -- (c)
    obtain ⟨l₁, l₂, rfl, hmem⟩ := hex'
    have hl₁ : ∀ r ∈ l₁, r ∈ R := fun r hr => hlam r (by simp [hr])
    have hl₂ : ∀ r ∈ l₂, r ∈ R := fun r hr => hlam r (by simp [hr])
    have hl₂p : ∀ r ∈ l₂, r ≠ p := fun r hr h => hpR (h ▸ hl₂ r hr)
    have hind' := (hind.extend (fun r hr => hlamp r (by simp [hr])) ⟨o, k, hpa⟩ hmem).append_other
      hl₂p
    have hnb := hGj _ (fun r hr => by
      rcases List.mem_append.1 hr with hr | hr
      · exact hαlam l₁ hl₁ r hr
      · exact Set.mem_insert_of_mem _ (hl₂ r hr)) hind'
    -- `d` does not change the memory, so `Cαλ₁` and `Cαλ₁d` agree on `R`
    set E := run (run C α) l₁
    have hloc' : E.loc p = (run C' (solo p j)).loc p := by
      rw [run_loc_other _ _ (fun r hr => hlamp r (by simp [hr])), hind.2]
    have hpa' : A.act (E.loc p) = .access B o k := by rw [hloc']; exact hpa
    have hstep : (E.step p).mem = E.mem := by
      rw [E.step_of_access hpa']
      funext i
      by_cases hiB : i = B
      · subst hiB; simp [hmem, hd]
      · simp [Function.update_of_ne hiB]
    have hag : AgreeOn R E (E.step p) := agreeOn_step_of_mem_eq E hpR hstep
    have hag2 := hag.run hl₂
    rw [run_append, hag2.biv_iff hQR]
    rwa [run_append, run_append, run_append, run_singleton] at hnb

end Lemma14

/-! ## More on blocks; changes of object values -/

/-- After a block update by processes covering *distinct* objects, the value of each covered
object depends only on the state of its covering process. -/
lemma block_mem_covered {C D : Cfg A} {cs : List (P × ι)} (hC : Covering C cs)
    (hD : Covering D cs) (hnd : (cs.map Prod.snd).Nodup) (hl : ∀ c ∈ cs, C.loc c.1 = D.loc c.1) :
    ∀ c ∈ cs, (run C (block cs)).mem c.2 = (run D (block cs)).mem c.2 := by
  induction cs generalizing C D with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨p, i⟩ := c
    have hnd1 := hC.1
    simp only [List.map_cons, List.nodup_cons] at hnd1 hnd
    have hnot : ∀ c ∈ cs, c.1 ≠ p := fun c hc h => hnd1.1 (h ▸ List.mem_map_of_mem hc)
    have hnoti : ∀ c ∈ cs, c.2 ≠ i := fun c hc h => hnd.1 (h ▸ List.mem_map_of_mem hc)
    obtain ⟨o, k, h1, h2⟩ := hC.2 (p, i) (by simp)
    have h1' : A.act (D.loc p) = .access i o k := by rw [← hl (p, i) (by simp)]; exact h1
    have hCs : Covering (C.step p) cs := ⟨hnd1.2, fun c hc => (hC.2 c (by simp [hc])).of_loc
      (C.step_loc_other (hnot c hc))⟩
    have hDs : Covering (D.step p) cs := ⟨hnd1.2, fun c hc => (hD.2 c (by simp [hc])).of_loc
      (D.step_loc_other (hnot c hc))⟩
    intro c hc
    simp only [block, List.map_cons, run_cons]
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · have e1 := run_block_mem_other hCs hnoti
      have e2 := run_block_mem_other hDs hnoti
      simp only [block] at e1 e2
      rw [e1, e2, C.step_of_access h1, D.step_of_access h1']
      simp only [Function.update_self]
      exact h2 _ _
    · have := ih hCs hDs hnd.2 (fun c hc => by
        rw [C.step_loc_other (hnot c hc), D.step_loc_other (hnot c hc)]
        exact hl c (by simp [hc])) c hc
      simpa [block] using this

/-- If the block update changes none of the covered objects, it does not change the memory. -/
lemma block_mem_eq_self {C : Cfg A} {cs : List (P × ι)} (hC : Covering C cs)
    (h : ∀ c ∈ cs, (run C (block cs)).mem c.2 = C.mem c.2) :
    (run C (block cs)).mem = C.mem := by
  funext j
  by_cases hj : ∃ c ∈ cs, c.2 = j
  · obtain ⟨c, hc, rfl⟩ := hj
    exact h c hc
  · push Not at hj
    exact run_block_mem_other hC hj

/-- **Observation 15** of [Ovens 2022] (generalized): if the block update by processes outside `Q`
does not change the covered objects, then `Q` is bivalent before it iff after it. -/
lemma obs15 {C : Cfg A} {cs : List (P × ι)} (hC : Covering C cs) {Q : Set P}
    (hQ : ∀ q ∈ Q, q ∉ block cs) (h : ∀ c ∈ cs, (run C (block cs)).mem c.2 = C.mem c.2) :
    Biv Q C ↔ Biv Q (run C (block cs)) := by
  have hag : AgreeOn Q C (run C (block cs)) :=
    ⟨(block_mem_eq_self hC h).symm, fun q hq => (run_block_loc_other C cs (hQ q hq)).symm⟩
  exact hag.biv_iff le_rfl

/-- The value of object `x` changes (at some configuration) during the execution `lam` from
`C`. -/
def Changes (C : Cfg A) (lam : List P) (x : ι) : Prop :=
  ∃ l₁ l₂, lam = l₁ ++ l₂ ∧ (run C l₁).mem x ≠ C.mem x

/-- A change during `lam` from `run C pre` is a change during `pre ++ lam` from `C`. -/
lemma Changes.of_suffix {C : Cfg A} {pre lam : List P} {x : ι} (h : Changes (run C pre) lam x) :
    Changes C (pre ++ lam) x := by
  obtain ⟨l₁, l₂, rfl, hne⟩ := h
  by_cases h0 : (run C pre).mem x = C.mem x
  · exact ⟨pre ++ l₁, l₂, by simp, by rw [run_append, ← h0]; exact hne⟩
  · exact ⟨pre, l₁ ++ l₂, rfl, h0⟩

lemma Changes.append_right {C : Cfg A} {lam : List P} {x : ι} (h : Changes C lam x)
    (rest : List P) : Changes C (lam ++ rest) x := by
  obtain ⟨l₁, l₂, rfl, hne⟩ := h
  exact ⟨l₁, l₂ ++ rest, by simp, hne⟩

lemma changes_of_ne {C : Cfg A} {lam : List P} {x : ι} (h : (run C lam).mem x ≠ C.mem x) :
    Changes C lam x := ⟨lam, [], by simp, h⟩

/-- If `p`'s state `l` occurs in its trace along `α` from `C`, then `p` took a step from state
`l` in `α`. -/
lemma Indist.step_of_solo {p : P} {C C' : Cfg A} {α : List P} {j : ℕ}
    (h : Indist p C α C' (solo p j)) {t : ℕ} (ht : t < j) :
    ∃ α₁ α₂, α = α₁ ++ p :: α₂ ∧ (run C α₁).loc p = (run C' (solo p t)).loc p := by
  have hmem := solo_mem_ptrace C' p ht
  rw [← h.1] at hmem
  exact mem_ptrace hmem

/-- A step of a process `p` (outside the block and outside `Q`) on an object covered by the
block is overwritten by the block: `Q` is bivalent after `pβ` iff after `β`. -/
lemma biv_step_block_iff {G : Cfg A} {cs : List (P × ι)} (hG : Covering G cs) {Q : Set P}
    (hQ : ∀ q ∈ Q, q ∉ block cs) {p : P} (hpb : p ∉ block cs) (hpQ : p ∉ Q) {B : ι}
    (hpB : G.Poised p B) (hB : ∃ c ∈ cs, c.2 = B) :
    Biv Q (run (G.step p) (block cs)) ↔ Biv Q (run G (block cs)) := by
  have hl : ∀ c ∈ cs, (G.step p).loc c.1 = G.loc c.1 := fun c hc =>
    G.step_loc_other (fun h => hpb (h ▸ List.mem_map_of_mem hc))
  have hGp : Covering (G.step p) cs := hG.of_loc hl
  have hmem : (run (G.step p) (block cs)).mem = (run G (block cs)).mem := by
    refine block_mem_eq hGp hG hl (fun x hx => G.step_mem_other hpB ?_)
    rintro rfl
    obtain ⟨c, hc, hcB⟩ := hB
    exact hx c hc hcB
  have hag : AgreeOn Q (run G (block cs)) (run (G.step p) (block cs)) := by
    refine ⟨hmem.symm, fun q hq => ?_⟩
    rw [run_block_loc_other _ _ (hQ q hq), run_block_loc_other _ _ (hQ q hq),
      G.step_loc_other (by rintro rfl; exact hpQ hq)]
  exact (hag.biv_iff le_rfl).symm

/-! ## From the correctness of a binary consensus algorithm to `Setting`; Observation 12 -/

/-- A binary consensus algorithm (agreement + obstruction-freedom) satisfies the assumptions of
Section 5 from every initial configuration. -/
lemma setting_of {S : Set Bool} (hA : SolvesSetAgreement A 1 S) (hof : ObstructionFree A S)
    {x : P → Bool} (hx : InputsIn S x) : Setting (initCfg A x) where
  agree α p q u w hu hw := by
    by_contra hne
    have h1 := hA.agreement x hx α
    have : ({u, w} : Set Bool) ⊆ (run (initCfg A x) α).decSet := by
      intro z hz
      rcases hz with rfl | rfl
      · exact ⟨p, hu⟩
      · exact ⟨q, hw⟩
    have h2 := (Set.encard_le_encard this).trans h1
    rw [Set.encard_pair hne] at h2
    exact absurd h2 (by decide)
  of α p := hof x hx α p

lemma SolvesSetAgreement.validity_univ {k : ℕ} (hA : SolvesSetAgreement A k Set.univ) :
    ∀ x : P → Bool, ∀ α p v, (run (initCfg A x) α).Out p v → ∃ q, x q = v :=
  fun x => hA.validity x (fun _ => trivial)

/-- **Observation 12** of [Ovens 2022]: if `q₀` has input `0` and `q₁` has input `1`, then
`Q = {q₀, q₁}` is bivalent in the initial configuration. -/
theorem obs12 (hval : ∀ x : P → Bool, ∀ α p v, (run (initCfg A x) α).Out p v → ∃ q, x q = v)
    (hof : ObstructionFree A Set.univ) {x : P → Bool} {q₀ q₁ : P} (h0 : x q₀ = false)
    (h1 : x q₁ = true) : Biv {q₀, q₁} (initCfg A x) := by
  have solo_dec : ∀ (q : P) (b : Bool), x q = b → ∃ t, (run (initCfg A x) (solo q t)).Out q b := by
    intro q b hb
    subst hb
    obtain ⟨t, w, hw⟩ := hof (fun _ => x q) (fun _ => trivial) [] q
    obtain ⟨q', hq'⟩ := hval (fun _ => x q) (solo q t) q w (by simpa using hw)
    subst hq'
    have hag : AgreeOn {q} (initCfg A x) (initCfg A (fun _ => x q)) :=
      ⟨rfl, fun r hr => by rw [Set.mem_singleton_iff.1 hr]; rfl⟩
    have := (hag.run (α := solo q t) (fun r hr => by
      rw [List.eq_of_mem_replicate hr]; rfl)).out_iff rfl (v := x q)
    exact ⟨t, this.2 (by simpa using hw)⟩
  obtain ⟨t₀, ht₀⟩ := solo_dec q₀ false h0
  obtain ⟨t₁, ht₁⟩ := solo_dec q₁ true h1
  exact ⟨⟨solo q₀ t₀, fun r hr => by rw [List.eq_of_mem_replicate hr]; simp, q₀, by simp, ht₀⟩,
    ⟨solo q₁ t₁, fun r hr => by rw [List.eq_of_mem_replicate hr]; simp, q₁, by simp, ht₁⟩⟩

end ConsensusFromSwap
