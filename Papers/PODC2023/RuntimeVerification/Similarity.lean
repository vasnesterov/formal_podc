import Mathlib
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Equiv

/-!
# Similarity of histories and the class `GenLin` (Section 7.1)

Castañeda, Rodríguez, *Asynchronous Wait-Free Runtime Verification and Enforcement of
Linearizability*, PODC 2023 (arXiv 2301.02638v3).

Histories are the single-object Herlihy–Wing histories of CSLib
(`Cslib.SharedMemory.HerlihyWing.History P Unit Op R`); an operation instance is identified by
`OpId` `(p, (), k)` = the `k`-th operation of process `p`. Linearizability is CSLib's amended
definition `Cslib.SharedMemory.HerlihyWing.Linearizable` (Sela–Herlihy–Petrank), which is exactly
Definition 4.2 of the paper (the paper uses the definition of [95] = Sela–Herlihy–Petrank).

* `Prec H a b` — the paper's `a ≺_H b` (operations complete or pending).
* `Obtain E E'` — `E'` is obtained from `E` by removing invocations of pending operations and
  appending responses to pending operations (Definition 7.1 (1)).
* `Similar E F` — Definition 7.1.
* `GenLin O` — Definition 7.2: `O` is closed under prefixes and similarity.
* `SimS E F` — a semantic characterization of similarity, `similar_iff_simS`.
* `lemma_7_1` — Lemma 7.1: linearizability (w.r.t. a prefix-closed sequential specification)
  belongs to `GenLin`.

-- CSLib candidate: `similar_iff_simS`, `lemma_7_1_prefix`, `lemma_7_1_similar` (and helpers).
-/

namespace Podc2023.RuntimeVerification

open Cslib.SharedMemory.HerlihyWing

/-- Single-object histories. -/
abbrev Hist (P Op R : Type) := History P Unit Op R

variable {P Op R : Type} [DecidableEq P]

/-- The paper's `a ≺_H b` (Section 7.1): `b` is an operation of `H` (complete or pending) and the
response of `a` precedes the invocation of `b`. -/
def Prec (H : Hist P Op R) (a b : OpId P Unit) : Prop := Precedes H a b ∧ Invoked H b

/-- `Obtain E E'`: `E'` can be obtained from `E` by removing invocations of some pending
operations and appending responses to some pending operations (Definition 7.1 (1)). A removed
invocation is the last event of its process (hence pending); appended responses go at the end.
(That appended responses answer pending operations is enforced by the well-formedness of the
final history in `Similar`.) -/
inductive Obtain : Hist P Op R → Hist P Op R → Prop
  | refl (E : Hist P Op R) : Obtain E E
  | drop (β γ : Hist P Op R) (p : P) (o : Op) (E' : Hist P Op R) :
      (∀ e ∈ γ, e.proc ≠ p) → Obtain (β ++ γ) E' → Obtain (β ++ Event.inv p () o :: γ) E'
  | append (E : Hist P Op R) (p : P) (r : R) (E' : Hist P Op R) :
      Obtain (E ++ [Event.res p () r]) E' → Obtain E E'

/-- **Definition 7.1.** The (well-formed) history `E` is *similar* to `F` if some history `E'`
obtained from `E` by appending responses to some pending operations and removing invocations of
some pending operations is equivalent to `F` and satisfies `≺_{E'} ⊆ ≺_F`. -/
def Similar (E F : Hist P Op R) : Prop :=
  WellFormed E ∧ ∃ E', Obtain E E' ∧ WellFormed E' ∧ Equiv E' F ∧
    ∀ a b, Prec E' a b → Prec F a b

/-- **Definition 7.2.** An (abstract) object, i.e. a set of histories, is in `GenLin` if it is
closed under prefixes and under similarity. -/
def GenLin (O : Set (Hist P Op R)) : Prop :=
  (∀ F ∈ O, ∀ E, E <+: F → E ∈ O) ∧ (∀ F ∈ O, ∀ E, Similar E F → E ∈ O)

/-- Semantic form of similarity: `F`'s operations are operations of `E` (with the same
arguments), `E`'s complete operations are complete in `F` (with the same responses), and the
real-time order of `E` towards operations of `F` is preserved. -/
structure SimS (E F : Hist P Op R) : Prop where
  wfE : WellFormed E
  wfF : WellFormed F
  op_eq : ∀ a, Invoked F a → opOf E a = opOf F a
  res_eq : ∀ a, Completed E a → resOf F a = resOf E a
  prec : ∀ a b, Precedes E a b → Invoked F b → Precedes F a b


/-! ## Auxiliary lemmas -/

section Aux

omit [DecidableEq P] in
lemma prefix_getElem? {α : Type} {l₁ l₂ : List α} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₂[i]? = l₁[i]? := by
  rw [List.prefix_iff_getElem?.1 h i hi, List.getElem?_eq_getElem hi]

lemma opsOf_eq_nil_of_proc_ne {γ : Hist P Op R} {p : P} (h : ∀ e ∈ γ, e.proc ≠ p) (x : Unit) :
    opsOf γ p x = [] := by
  induction γ with
  | nil => rfl
  | cons e γ ih =>
    rw [opsOf_cons, ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    have he := h e List.mem_cons_self
    cases e with
    | inv q y o => simp only [Event.proc_inv] at he; simp [he]
    | res q y r => simp

lemma restrictP_eq_nil_of_proc_ne {γ : Hist P Op R} {p : P} (h : ∀ e ∈ γ, e.proc ≠ p) :
    restrictP γ p = [] := by
  simp only [restrictP, List.filter_eq_nil_iff, decide_eq_true_eq]; exact h

/-- Erasing an invocation event preserves real-time precedence. -/
lemma precedes_erase_inv {β γ : Hist P Op R} {p : P} {o : Op} {a b : OpId P Unit}
    (h : Precedes (β ++ Event.inv p () o :: γ) a b) : Precedes (β ++ γ) a b := by
  obtain ⟨β', γ', hs, hc, hni⟩ := h
  rcases List.append_eq_append_iff.1 hs.symm with ⟨a', rfl, rfl⟩ | ⟨c', rfl, hc'⟩
  · exact ⟨β', a' ++ γ, by simp, hc, hni⟩
  · cases c' with
    | nil =>
      simp only [List.nil_append, List.append_nil] at hc' hc hni
      subst hc'
      exact ⟨β, γ, rfl, hc, hni⟩
    | cons e c'' =>
      simp only [List.cons_append, List.cons.injEq] at hc'
      obtain ⟨rfl, rfl⟩ := hc'
      refine ⟨β ++ c'', γ', by simp, ?_, ?_⟩
      · simpa [Completed] using hc
      · intro hi; apply hni
        simp only [Invoked, opsOf_append, opsOf_cons, List.length_append] at hi ⊢; omega

/-- Re-inserting a dropped pending invocation (the last event of its process) preserves
real-time precedence towards operations that are still invoked. -/
lemma precedes_insert_inv {β γ : Hist P Op R} {p : P} {o : Op} {a b : OpId P Unit}
    (hγ : ∀ e ∈ γ, e.proc ≠ p) (h : Precedes (β ++ γ) a b) (hb : Invoked (β ++ γ) b) :
    Precedes (β ++ Event.inv p () o :: γ) a b := by
  obtain ⟨β', γ', hs, hc, hni⟩ := h
  rcases List.append_eq_append_iff.1 hs.symm with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
  · exact ⟨β', a' ++ Event.inv p () o :: γ, by simp, hc, hni⟩
  · refine ⟨β ++ Event.inv p () o :: c', γ', by simp, ?_, ?_⟩
    · simpa [Completed] using hc
    · intro hi
      apply hni
      by_cases hp : b.p = p
      · have h1 : opsOf c' b.p b.x = [] := opsOf_eq_nil_of_proc_ne
          (fun e he => by rw [hp]; exact hγ e (List.mem_append_left _ he)) _
        have h2 : opsOf γ' b.p b.x = [] := opsOf_eq_nil_of_proc_ne
          (fun e he => by rw [hp]; exact hγ e (List.mem_append_right _ he)) _
        simp only [Invoked, opsOf_append, List.length_append, h1, h2] at hb ⊢; omega
      · have : ((Event.inv p () o : Event P Unit Op R).invOf b.p b.x) = none := by
          simp [Ne.symm hp]
        simp only [Invoked, opsOf_append, opsOf_cons, List.length_append, this,
          Option.toList_none, List.length_nil] at hi ⊢
        omega

/-- What `Obtain` preserves. -/
lemma Obtain.props {E E' : Hist P Op R} (h : Obtain E E') :
    (∀ p x, opsOf E' p x <+: opsOf E p x) ∧ (∀ p x, ressOf E p x <+: ressOf E' p x) ∧
      (∀ a b, Precedes E a b → Invoked E' b → Precedes E' a b) := by
  induction h with
  | refl E => exact ⟨fun _ _ => List.prefix_refl _, fun _ _ => List.prefix_refl _,
      fun _ _ h _ => h⟩
  | drop β γ p o E' hγ _ ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨fun q x => (h1 q x).trans ?_, fun q x => ?_,
      fun a b hab hb => h3 a b (precedes_erase_inv hab) hb⟩
    · by_cases hq : p = q
      · subst hq
        simp only [opsOf_append, opsOf_cons, opsOf_eq_nil_of_proc_ne hγ, List.append_nil]
        exact List.prefix_append _ _
      · have : ((Event.inv p () o : Event P Unit Op R).invOf q x) = none := by simp [hq]
        simp [this]
    · have : ressOf (β ++ Event.inv p () o :: γ) q x = ressOf (β ++ γ) q x := by simp
      rw [this]; exact h2 q x
  | append E p r E' _ ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨fun q x => ?_, fun q x => ?_, fun a b hab hb => h3 a b hab.mono hb⟩
    · have : opsOf (E ++ [Event.res p () r]) q x = opsOf E q x := by simp
      rw [← this]; exact h1 q x
    · refine (List.prefix_append (ressOf E q x) (ressOf ([Event.res p () r] : Hist P Op R) q x)).trans ?_
      rw [← ressOf_append]; exact h2 q x

/-- The process subhistory of a well-formed single-object history, with its operations and
responses. -/
lemma restrictP_form {H : Hist P Op R} (hH : WellFormed H) (p : P) :
    ∃ M : List (OpRec P Unit Op R), (∀ e ∈ M, e.p = p) ∧
      ((restrictP H p = seqHist M ∧ opsOf H p () = M.map (·.o) ∧ ressOf H p () = M.map (·.r)) ∨
       ∃ o, restrictP H p = seqHist M ++ [.inv p () o] ∧ opsOf H p () = M.map (·.o) ++ [o] ∧
         ressOf H p () = M.map (·.r)) := by
  obtain ⟨M, hM, h | ⟨⟨⟩, o, h⟩⟩ := hH.restrictP_eq p
  all_goals
    have hf : M.filter (fun e => decide (e.p = p) && decide (e.x = ())) = M :=
      List.filter_eq_self.2 (fun e he => by simp [hM e he])
  · refine ⟨M, hM, Or.inl ⟨h, ?_, ?_⟩⟩
    · rw [opsOf_eq_restrictP, h, opsOf_seqHist, hf]
    · rw [ressOf_eq_restrictP, h, ressOf_seqHist, hf]
  · refine ⟨M, hM, Or.inr ⟨o, h, ?_, ?_⟩⟩
    · rw [opsOf_eq_restrictP, h, opsOf_append, opsOf_seqHist, hf]; simp
    · rw [ressOf_eq_restrictP, h, ressOf_append, ressOf_seqHist, hf]; simp

omit [DecidableEq P] in
lemma recs_eq {M N : List (OpRec P Unit Op R)} {p : P} (hM : ∀ e ∈ M, e.p = p)
    (hN : ∀ e ∈ N, e.p = p) (ho : M.map (·.o) = N.map (·.o)) (hr : M.map (·.r) = N.map (·.r)) :
    M = N := by
  induction M generalizing N with
  | nil => cases N with
    | nil => rfl
    | cons => simp at ho
  | cons e M ih =>
    cases N with
    | nil => simp at ho
    | cons f N =>
      simp only [List.map_cons, List.cons.injEq] at ho hr
      have he := hM e List.mem_cons_self
      have hf := hN f List.mem_cons_self
      congr 1
      · obtain ⟨p1, ⟨⟩, o1, r1⟩ := e
        obtain ⟨p2, ⟨⟩, o2, r2⟩ := f
        simp only at he hf ho hr
        subst he hf; rw [ho.1, hr.1]
      · exact ih (fun e he => hM e (List.mem_cons_of_mem _ he))
          (fun e he => hN e (List.mem_cons_of_mem _ he)) ho.2 hr.2

/-- Under `SimS E F`, the subhistories of a process in `E` and `F` coincide, or differ by the
pending invocation of `E` (not invoked in `F`), or by the response in `F` to the pending
invocation of `E`. -/
lemma SimS.restrictP_cases {E F : Hist P Op R} (h : SimS E F) (p : P) :
    restrictP E p = restrictP F p ∨ (∃ o, restrictP E p = restrictP F p ++ [.inv p () o]) ∨
      ∃ r, restrictP F p = restrictP E p ++ [.res p () r] := by
  have hop : opsOf F p () <+: opsOf E p () := by
    rw [List.prefix_iff_getElem?]
    intro i hi
    have := h.op_eq ⟨p, (), i⟩ hi
    simp only [opOf] at this
    rw [this]; exact List.getElem?_eq_getElem hi
  have hres : ressOf E p () <+: ressOf F p () := by
    rw [List.prefix_iff_getElem?]
    intro i hi
    have := h.res_eq ⟨p, (), i⟩ hi
    simp only [resOf] at this
    rw [this]; exact List.getElem?_eq_getElem hi
  obtain ⟨M, hM, ⟨hE, hoE, hrE⟩ | ⟨o, hE, hoE, hrE⟩⟩ := restrictP_form h.wfE p <;>
  obtain ⟨N, hN, ⟨hF, hoF, hrF⟩ | ⟨o', hF, hoF, hrF⟩⟩ := restrictP_form h.wfF p <;>
  rw [hoE, hoF] at hop <;> rw [hrE, hrF] at hres <;>
  have l1 := hop.length_le <;> have l2 := hres.length_le <;>
  simp only [List.length_append, List.length_map, List.length_singleton] at l1 l2
  · -- both complete
    left
    have ho := hop.eq_of_length (by simp; omega)
    have hr := hres.eq_of_length (by simp; omega)
    rw [hE, hF, recs_eq hM hN ho.symm hr]
  · omega
  · rcases Nat.lt_or_ge M.length N.length with hlt | hge
    · right; right
      have ho := hop.eq_of_length (by simp; omega)
      obtain ⟨t, ht⟩ := hres
      have htl : t.length = 1 := by
        have := congrArg List.length ht; simp at this; omega
      obtain ⟨r, rfl⟩ := List.length_eq_one_iff.1 htl
      refine ⟨r, ?_⟩
      have hNM : N = M ++ [⟨p, (), o, r⟩] := by
        refine recs_eq hN (fun e he => ?_) (by rw [ho]; simp) (by rw [← ht]; simp)
        rcases List.mem_append.1 he with he | he
        · exact hM e he
        · simp only [List.mem_singleton] at he; rw [he]
      rw [hF, hE, hNM]; simp
    · right; left
      have hr := hres.eq_of_length (by simp; omega)
      have ho : N.map (·.o) = M.map (·.o) := by
        have := List.prefix_iff_eq_take.1 hop
        rw [this, List.length_map, show N.length = (M.map (·.o)).length by simp; omega]
        simp
      exact ⟨o, by rw [hE, hF, recs_eq hM hN ho.symm hr]⟩
  · left
    have ho := hop.eq_of_length (by simp; omega)
    obtain ⟨h1, h2⟩ := List.append_inj' ho rfl
    simp only [List.cons.injEq, and_true] at h2
    have hr := hres.eq_of_length (by simp; omega)
    rw [hE, hF, recs_eq hM hN h1.symm hr, h2]

/-- A process subhistory ending with an invocation: the invocation is the last event of the
process in the history. -/
lemma exists_split_last_inv {H s : Hist P Op R} {p : P} {o : Op}
    (h : restrictP H p = s ++ [Event.inv p () o]) :
    ∃ β γ, H = β ++ Event.inv p () o :: γ ∧ (∀ e ∈ γ, e.proc ≠ p) ∧ restrictP β p = s := by
  unfold restrictP at h
  obtain ⟨l₁, l₂, rfl, h1, h2⟩ := List.filter_eq_append_iff.1 h
  obtain ⟨m₁, m₂, rfl, hm1, -, hm2⟩ := List.filter_eq_cons_iff.1 h2
  refine ⟨l₁ ++ m₁, m₂, by simp, fun e he => by simpa using List.filter_eq_nil_iff.1 hm2 e he, ?_⟩
  have : m₁.filter (fun e => decide (e.proc = p)) = [] := List.filter_eq_nil_iff.2 hm1
  simp only [restrictP, List.filter_append, h1, this, List.append_nil]

/-- Construction for `SimS → Similar`: modify the processes of `ps` one by one. -/
lemma SimS.build {E F : Hist P Op R} (hS : SimS E F) (ps : List P) :
    ∃ H : Hist P Op R, (∀ E', Obtain H E' → Obtain E E') ∧
      (∀ a b, Precedes H a b → Invoked H b → Precedes E a b) ∧
      (∀ q, restrictP H q = if q ∈ ps then restrictP F q else restrictP E q) := by
  induction ps with
  | nil => exact ⟨E, fun _ h => h, fun _ _ h _ => h, fun q => by simp⟩
  | cons p ps ih =>
    obtain ⟨H, hob, hpre, hres⟩ := ih
    have hres' : ∀ q, q ≠ p → restrictP H q =
        if q ∈ p :: ps then restrictP F q else restrictP E q := fun q hq => by
      rw [hres q]; simp [hq]
    by_cases hp : p ∈ ps
    · refine ⟨H, hob, hpre, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; rw [hres q]; simp [hp]
      · exact hres' q hq
    have hHp : restrictP H p = restrictP E p := by rw [hres p]; simp [hp]
    rcases hS.restrictP_cases p with h0 | ⟨o, h0⟩ | ⟨r, h0⟩
    · refine ⟨H, hob, hpre, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; simp [hHp, h0]
      · exact hres' q hq
    · rw [h0] at hHp
      obtain ⟨β, γ, rfl, hγ, hβ⟩ := exists_split_last_inv hHp
      refine ⟨β ++ γ, fun E' h => hob E' (Obtain.drop β γ p o E' hγ h),
        fun a b hab hb => hpre a b (precedes_insert_inv hγ hab hb) ?_, fun q => ?_⟩
      · simp only [Invoked, opsOf_append, opsOf_cons, List.length_append] at hb ⊢; omega
      · by_cases hq : q = p
        · subst hq
          simp only [restrictP_append, restrictP_eq_nil_of_proc_ne hγ, List.append_nil, hβ,
            List.mem_cons, true_or, ite_true]
        · rw [← hres' q hq]
          simp [restrictP, List.filter_append, Ne.symm hq]
    · refine ⟨H ++ [Event.res p () r], fun E' h => hob E' (Obtain.append H p r E' h),
        fun a b hab hb => ?_, fun q => ?_⟩
      · have hb' : Invoked H b := by simpa [Invoked] using hb
        exact hpre a b (hab.of_append_of_invoked hb') hb'
      · by_cases hq : q = p
        · subst hq; simp [restrictP_append, hHp, h0, restrictP_singleton]
        · rw [restrictP_append, hres' q hq]
          simp [restrictP_singleton, Ne.symm hq]

/-- A prefix of a linearization that contains all operations completed in `E`, each of its
elements being completed in `E` or preceding (in the list) one that is. -/
lemma exists_prefix_cover (E : Hist P Op R) (M : List (OpRec P Unit Op R)) :
    ∃ N, N <+: M ∧ (∀ a ∈ idsOf M, Completed E a → a ∈ idsOf N) ∧
      (∀ c ∈ idsOf N, Completed E c ∨ ∃ a, Completed E a ∧ [c, a].Sublist (idsOf N)) := by
  induction M using List.reverseRecOn with
  | nil => exact ⟨[], List.prefix_refl _, fun a ha => by simp at ha, fun c hc => by simp at hc⟩
  | append_singleton M e ih =>
    obtain ⟨N, hN, h1, h2⟩ := ih
    by_cases hz : Completed E ⟨e.p, e.x, cnt M e.p e.x⟩
    · refine ⟨M ++ [e], List.prefix_refl _, fun a ha _ => ha, fun c hc => ?_⟩
      rw [idsOf_concat] at hc ⊢
      rcases List.mem_append.1 hc with hc | hc
      · exact Or.inr ⟨_, hz, pair_sublist_iff.2 ⟨idsOf M, _, rfl, hc, List.mem_singleton_self _⟩⟩
      · rw [List.mem_singleton] at hc; subst hc; exact Or.inl hz
    · refine ⟨N, hN.trans (List.prefix_append _ _), fun a ha hca => ?_, h2⟩
      rw [idsOf_concat] at ha
      rcases List.mem_append.1 ha with ha | ha
      · exact h1 a ha hca
      · rw [List.mem_singleton] at ha; subst ha; exact absurd hca hz

end Aux

/-- Definition 7.1 is equivalent to its semantic form. -/
theorem similar_iff_simS {E F : Hist P Op R} : Similar E F ↔ SimS E F := by
  constructor
  · rintro ⟨hE, E', hob, hwf', heq, hprec⟩
    obtain ⟨h1, h2, h3⟩ := hob.props
    have hinv : ∀ a, Invoked E' a ↔ Invoked F a := fun a => by
      simp only [Invoked, heq.opsOf_eq]
    refine ⟨hE, fun q => by rw [← heq q]; exact hwf' q, fun a ha => ?_, fun a hc => ?_,
      fun a b hab hb => (hprec a b ⟨h3 a b hab ((hinv b).2 hb), (hinv b).2 hb⟩).1⟩
    · rw [← heq.opOf_eq]
      exact prefix_getElem? (h1 a.p a.x) ((hinv a).2 ha)
    · rw [← heq.resOf_eq]
      exact prefix_getElem? (h2 a.p a.x) hc
  · intro h
    obtain ⟨H, hob, hpre, hres⟩ := h.build (E.map Event.proc ++ F.map Event.proc)
    have heq : Equiv H F := by
      intro q
      rw [hres q]
      split_ifs with hq
      · rfl
      · have hE : restrictP E q = [] := restrictP_eq_nil_of_proc_ne fun e he hep =>
          hq (List.mem_append_left _ (List.mem_map.2 ⟨e, he, hep⟩))
        have hF : restrictP F q = [] := restrictP_eq_nil_of_proc_ne fun e he hep =>
          hq (List.mem_append_right _ (List.mem_map.2 ⟨e, he, hep⟩))
        rw [hE, hF]
    have hinv : ∀ a, Invoked H a ↔ Invoked F a := fun a => by
      simp only [Invoked, heq.opsOf_eq]
    exact ⟨h.wfE, H, hob H (Obtain.refl H), fun q => by rw [heq q]; exact h.wfF q, heq,
      fun a b ⟨hab, hb⟩ => ⟨h.prec a b (hpre a b hab hb) ((hinv b).1 hb), (hinv b).1 hb⟩⟩

theorem SimS.similar {E F : Hist P Op R} (h : SimS E F) : Similar E F := similar_iff_simS.2 h

theorem Similar.simS {E F : Hist P Op R} (h : Similar E F) : SimS E F := similar_iff_simS.1 h

/-- A `GenLin` object is closed under semantic similarity. -/
theorem GenLin.mem_of_simS {O : Set (Hist P Op R)} (hO : GenLin O) {E F : Hist P Op R}
    (hF : F ∈ O) (h : SimS E F) : E ∈ O :=
  hO.2 F hF E h.similar

/-- A `GenLin` object is closed under prefixes. -/
theorem GenLin.mem_of_prefix {O : Set (Hist P Op R)} (hO : GenLin O) {E F : Hist P Op R}
    (hF : F ∈ O) (h : E <+: F) : E ∈ O :=
  hO.1 F hF E h

/-! ## Lemma 7.1: linearizability is in `GenLin` -/

/-- A sequential specification is prefix closed (as is every specification given by a state
machine, Definition 4.1). -/
def PrefixClosedSpec (spec : SeqSpec P Unit Op R) : Prop :=
  ∀ M N : List (OpRec P Unit Op R), seqHist (M ++ N) ∈ spec () → seqHist M ∈ spec ()

/-- **Lemma 7.1 (1).** Every prefix of a linearizable history is linearizable. -/
theorem lemma_7_1_prefix {spec : SeqSpec P Unit Op R} (hspec : PrefixClosedSpec spec)
    {E F : Hist P Op R} (hF : Linearizable spec F) (h : E <+: F) : Linearizable spec E := by
  obtain ⟨t, rfl⟩ := h
  obtain ⟨hwfF, M, hM⟩ := linearizable_iff.1 hF
  have hwfE : WellFormed E := hwfF.of_append
  obtain ⟨N, ⟨T, rfl⟩, h1, h2⟩ := exists_prefix_cover E M
  have hids : idsOf (N ++ T) = idsOf N ++ idsGo N T := idsOf_append N T
  have hnd := nodup_idsOf (N ++ T)
  have hsub : ∀ a ∈ idsOf N, a ∈ idsOf (N ++ T) := fun a ha => by
    rw [hids]; exact List.mem_append_left _ ha
  have hsub2 : ∀ a b, [a, b].Sublist (idsOf N) → [a, b].Sublist (idsOf (N ++ T)) :=
    fun a b hab => by rw [hids]; exact hab.trans (List.sublist_append_left _ _)
  have hinvN : ∀ c ∈ idsOf N, Invoked E c := by
    intro c hc
    rcases h2 c hc with hcc | ⟨a, ha, hca⟩
    · exact hwfE.invoked_of_completed hcc
    · by_contra hni
      have hpre : Precedes (E ++ t) a c := ⟨E, t, rfl, ha, hni⟩
      exact pair_sublist_asymm hnd (hM.realtime a c hpre (hsub c hc)) (hsub2 c a hca)
  refine linearizable_iff.2 ⟨hwfE, N, IsLinA.mk' hwfE ?_ ?_ ?_ ?_⟩
  · intro a e hae
    have hae' : (a, e) ∈ (idsOf (N ++ T)).zip (N ++ T) := by
      rw [hids, List.zip_append (by simp)]; exact List.mem_append_left _ hae
    obtain ⟨ho, hr⟩ := hM.recs a e hae'
    have hai : Invoked E a := hinvN a (List.of_mem_zip hae).1
    refine ⟨by rw [opOf_append_of_invoked hai] at ho; exact ho, fun hc => ?_⟩
    have := hr hc.mono
    rw [resOf_append_of_completed hc] at this; exact this
  · intro a ha; exact h1 a (hM.complete a ha.mono) ha
  · have hX : ∀ S : Hist P Op R, restrictX S () = S := fun S =>
      List.filter_eq_self.2 (fun e _ => by simp)
    refine ⟨isSeq_seqHist N, fun x => ?_⟩
    have hl := hM.legal.2 x
    cases x
    rw [hX] at hl ⊢
    exact hspec N T hl
  · intro a b hab hb
    have hab' := hM.realtime a b hab.mono (hsub b hb)
    have ha : a ∈ idsOf N := h1 a (hab'.subset List.mem_cons_self) hab.completed
    have hne : a ≠ b := by rintro rfl; exact pair_sublist_irrefl hnd a hab'
    rcases pair_sublist_total (nodup_idsOf N) ha hb hne with h | h
    · exact h
    · exact absurd hab' (pair_sublist_asymm hnd (hsub2 b a h))

/-- **Lemma 7.1 (2).** Every history similar to a linearizable history is linearizable. -/
theorem lemma_7_1_similar {spec : SeqSpec P Unit Op R} {E F : Hist P Op R}
    (hF : Linearizable spec F) (h : Similar E F) : Linearizable spec E := by
  have hS := h.simS
  obtain ⟨-, M, hM⟩ := linearizable_iff.1 hF
  have hcF : ∀ a, Completed E a → Completed F a := fun a ha =>
    completed_iff_resOf.2 (by rw [hS.res_eq a ha]; exact completed_iff_resOf.1 ha)
  refine linearizable_iff.2 ⟨hS.wfE, M, IsLinA.mk' hS.wfE ?_ ?_ hM.legal ?_⟩
  · intro a e hae
    obtain ⟨h1, h2⟩ := hM.recs a e hae
    refine ⟨by rw [hS.op_eq a (Invoked.of_opOf h1)]; exact h1, fun hc => ?_⟩
    rw [← hS.res_eq a hc]; exact h2 (hcF a hc)
  · intro a ha; exact hM.complete a (hcF a ha)
  · intro a b hab hb
    exact hM.realtime a b (hS.prec a b hab (hM.recs.invoked hb)) hb

/-- **Lemma 7.1.** The abstract object of all histories linearizable with respect to a
(prefix-closed) sequential specification belongs to `GenLin`. -/
theorem lemma_7_1 {spec : SeqSpec P Unit Op R} (hspec : PrefixClosedSpec spec) :
    GenLin {H : Hist P Op R | Linearizable spec H} :=
  ⟨fun _ hF _ h => lemma_7_1_prefix hspec hF h, fun _ hF _ h => lemma_7_1_similar hF h⟩

end Podc2023.RuntimeVerification
