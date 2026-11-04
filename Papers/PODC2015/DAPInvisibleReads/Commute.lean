import Papers.PODC2015.DAPInvisibleReads.Model

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Transactional/Commute.lean

/-!
# Commuting the steps of disjoint-access transactions

The indistinguishability arguments of Section 3 (Lemmas 1–3 of the paper) reorder the steps of
transactions that do not contend on base objects. This file proves the reordering principle we
use instead of the paper's Lemmas 1 and 2:

* `move_left`, `commute`: if no configuration reachable by interleaving the label lists `σ` (of
  process `a`) and `τ` (of process `b`) has `a` and `b` poised to contend on a base object, then
  `σ ++ τ` and `τ ++ σ` lead to the same configuration.
* `noContendFrom_of_wdap`: under WDAP, this hypothesis holds as soon as the processes can be split
  into two sides whose transactions access disjoint sets of transactional objects, with `a` and
  `b` on different sides. The proof only needs the transactions to be disjoint-access *at the
  time of each step*: transactions are not known a priori, so a transaction that will later
  conflict with another one is still disjoint-access from it until the conflicting operation is
  invoked.
-/

namespace Podc.DAPInvisibleReads

open Cslib.SharedMemory

variable {X V P : Type} [DecidableEq P]

/-! ### Data sets come from invocations -/

/-- The operation `o` occurs in the record `t`. -/
def TxRec.Has (t : TxRec X V) (o : TOp X V) : Prop := (∃ r, (o, r) ∈ t.ops) ∨ t.pend = some o

/-- The operation `o` occurs in some record of `s`. -/
def PState.Has (s : PState X V) (o : TOp X V) : Prop := (∃ t ∈ s.done, t.Has o) ∨ s.cur.Has o

lemma PState.has_step {s : PState X V} {ℓ : Lbl P X V} {o : TOp X V} (h : (s.step ℓ).Has o) :
    s.Has o ∨ ∃ q, ℓ = .inv q o := by
  cases ℓ with
  | inv q o' =>
    simp only [PState.step] at h
    rcases h with ⟨t, ht, h⟩ | ⟨r, hr⟩ | h
    · exact Or.inl (Or.inl ⟨t, ht, h⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨r, hr⟩))
    · simp only [Option.some.injEq] at h; subst h; exact Or.inr ⟨q, rfl⟩
  | tau q => exact Or.inl h
  | ret q r =>
    simp only [PState.step] at h
    split at h
    · exact Or.inl h
    · rename_i o' hp
      split at h
      · rcases h with ⟨t, ht, h⟩ | h
        · simp only [List.mem_append, List.mem_singleton] at ht
          rcases ht with ht | rfl
          · exact Or.inl (Or.inl ⟨t, ht, h⟩)
          · rcases h with ⟨r', hr'⟩ | h
            · simp only [List.mem_append, List.mem_singleton] at hr'
              rcases hr' with hr' | hr'
              · exact Or.inl (Or.inr (Or.inl ⟨r', hr'⟩))
              · simp only [Prod.mk.injEq] at hr'; rw [hr'.1]; exact Or.inl (Or.inr (Or.inr hp))
            · simp at h
        · rcases h with ⟨r', hr'⟩ | h <;> simp [TxRec.empty] at *
      · rcases h with ⟨t, ht, h⟩ | ⟨r', hr'⟩ | h
        · exact Or.inl (Or.inl ⟨t, ht, h⟩)
        · simp only [List.mem_append, List.mem_singleton] at hr'
          rcases hr' with hr' | hr'
          · exact Or.inl (Or.inr (Or.inl ⟨r', hr'⟩))
          · simp only [Prod.mk.injEq] at hr'; rw [hr'.1]; exact Or.inl (Or.inr (Or.inr hp))
        · simp at h

lemma PState.has_foldl (l : List (Lbl P X V)) (s : PState X V) {o : TOp X V}
    (h : (l.foldl PState.step s).Has o) : s.Has o ∨ ∃ q, .inv q o ∈ l := by
  induction l generalizing s with
  | nil => exact Or.inl h
  | cons ℓ l ih =>
    rcases ih _ h with h | ⟨q, hq⟩
    · rcases PState.has_step h with h | ⟨q, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by simp⟩
    · exact Or.inr ⟨q, by simp [hq]⟩

/-- The transactional objects of the operations invoked by `p`. -/
def objs (h : List (Lbl P X V)) (p : P) : Set X := {x | ∃ o ∈ opsOf h p, o.obj = some x}

lemma has_pstate {h : List (Lbl P X V)} {p : P} {o : TOp X V} (ho : (pstate h p).Has o) :
    o ∈ opsOf h p := by
  rcases PState.has_foldl _ _ ho with h0 | ⟨q, hq⟩
  · rcases h0 with ⟨t, ht, -⟩ | h0
    · simp [PState.init] at ht
    · rcases h0 with ⟨r, hr⟩ | h0 <;> simp [PState.init, TxRec.empty] at *
  · simp only [projP, List.mem_filter, decide_eq_true_eq] at hq
    obtain ⟨hq, hp⟩ := hq
    simp only [Label.proc] at hp; subst hp
    simp only [opsOf, List.mem_filterMap]
    exact ⟨_, hq, by simp⟩

lemma dSet_subset_objs (h : List (Lbl P X V)) (T : TxId P) : DSet h T ⊆ objs h T.1 := by
  intro x hx
  have key : ∀ o, (txRec h T).Has o → o.obj = some x → x ∈ objs h T.1 := by
    intro o ho hox
    refine ⟨o, has_pstate ?_, hox⟩
    unfold txRec at ho
    rcases T with ⟨p, k⟩
    simp only [List.getD_eq_getElem?_getD] at ho
    rcases lt_or_ge k ((pstate h p).done.length + 1) with hk | hk
    · rw [List.getElem?_eq_getElem (by simpa using hk), Option.getD_some] at ho
      by_cases hk' : k < (pstate h p).done.length
      · rw [List.getElem_append_left hk'] at ho
        exact Or.inl ⟨_, List.getElem_mem hk', ho⟩
      · have : k = (pstate h p).done.length := by omega
        subst this
        simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
          List.getElem_cons_zero] at ho
        exact Or.inr ho
    · rw [List.getElem?_eq_none (by simpa using hk), Option.getD_none] at ho
      rcases ho with ⟨r, hr⟩ | ho <;> simp [TxRec.empty] at *
  rcases hx with ⟨q, hq, hx⟩ | ⟨o, ho, hx⟩
  · exact key q.1 (Or.inl ⟨q.2, by simpa using hq⟩) hx
  · exact key o (Or.inr ho) hx

/-- **Side partition of transactions.** If every transaction is put on one of two sides, with
the data sets of the two sides disjoint, transactions on different sides are disjoint-access. -/
lemma connected_sideT {h : List (Lbl P X V)} (f : TxId P → Bool) (S : Bool → Set X)
    (hS : Disjoint (S true) (S false)) (hf : ∀ T, DSet h T ⊆ S (f T)) {T T' : TxId P}
    (hc : Connected h T T') : f T = f T' := by
  induction hc with
  | refl => rfl
  | tail _ hbc ih =>
    rename_i b c
    obtain ⟨-, -, x, hx1, hx2⟩ := hbc
    have h1 := hf _ hx1
    have h2 := hf _ hx2
    rw [ih]
    by_contra hne
    have : ∀ u w : Bool, u ≠ w → Disjoint (S u) (S w) := by
      intro u w huw
      cases u <;> cases w <;> simp_all [disjoint_comm]
    exact Set.disjoint_left.1 (this _ _ hne) h1 h2

/-- **Side partition.** If the processes are split into two sides whose operations access
disjoint sets of transactional objects, transactions on different sides are disjoint-access. -/
lemma connected_side {h : List (Lbl P X V)} (f : P → Bool) (S : Bool → Set X)
    (hS : Disjoint (S true) (S false)) (hf : ∀ p, objs h p ⊆ S (f p)) {T T' : TxId P}
    (hc : Connected h T T') : f T.1 = f T'.1 :=
  connected_sideT (fun T => f T.1) S hS (fun T => (dSet_subset_objs h T).trans (hf T.1)) hc

/-! ### Commuting non-contending steps -/

variable {ι : Type} {B : ι → ObjSpec} {L : Type} [DecidableEq ι]
variable (I : Impl (tmSpec X V) B P L)

/-- In `C`, processes `a` and `b` are not poised to contend on a base object. -/
def NoContend (C : Config (tmSpec X V) B P L) (a b : P) : Prop :=
  ∀ (i j : ι) (o : (B i).Op) (o' : (B j).Op) k k', C.pend a ≠ none → C.pend b ≠ none →
    I.act a (C.loc a) = .access i o k → I.act b (C.loc b) = .access j o' k' →
    i ≠ j ∨ (Trivial o ∧ Trivial o')

/-- No configuration reachable from `C` with labels satisfying `G` has `a` and `b` poised to
contend. -/
def NoContendFrom (G : Lbl P X V → Prop) (C : Config (tmSpec X V) B P L) (a b : P) : Prop :=
  ∀ ω C', (∀ ℓ ∈ ω, G ℓ) → I.runFrom C ω = some C' → NoContend I C' a b

variable {I}

lemma NoContendFrom.step {G : Lbl P X V → Prop} {C C₁ : Config (tmSpec X V) B P L} {a b : P}
    (h : NoContendFrom I G C a b) {ℓ : Lbl P X V} (hℓ : G ℓ) (hs : I.step C ℓ = some C₁) :
    NoContendFrom I G C₁ a b := by
  intro ω C' hω hr
  refine h (ℓ :: ω) C' ?_ (by simp [hs, hr])
  intro ℓ' h'; rcases List.mem_cons.1 h' with rfl | h' <;> [exact hℓ; exact hω ℓ' h']

lemma NoContendFrom.self {G : Lbl P X V → Prop} {C : Config (tmSpec X V) B P L} {a b : P}
    (h : NoContendFrom I G C a b) : NoContend I C a b := h [] C (by simp) rfl

omit [DecidableEq P] [DecidableEq ι] in
lemma NoContend.symm {C : Config (tmSpec X V) B P L} {a b : P} (h : NoContend I C a b) :
    NoContend I C b a := by
  intro i j o o' k k' ha hb hai hbj
  rcases h j i o' o k' k hb ha hbj hai with h | h
  · exact Or.inl (Ne.symm h)
  · exact Or.inr ⟨h.2, h.1⟩

lemma NoContendFrom.symm {G : Lbl P X V → Prop} {C : Config (tmSpec X V) B P L} {a b : P}
    (h : NoContendFrom I G C a b) : NoContendFrom I G C b a :=
  fun ω C' hω hr => (h ω C' hω hr).symm

/-- One step of `a` and one step of `b` commute when they do not contend. -/
lemma swap_steps {a b : P} (hab : a ≠ b) {C Ca Cab : Config (tmSpec X V) B P L}
    {s t : Lbl P X V} (hs : s.proc = a) (ht : t.proc = b) (hnc : NoContend I C a b)
    (h1 : I.step C s = some Ca) (h2 : I.step Ca t = some Cab) :
    ∃ Cb, I.step C t = some Cb ∧ I.step Cb s = some Cab := by
  refine Impl.step_comm hab hs ht h1 h2 ?_
  intro i o k j o' k' hsa hai htb hbj
  subst hsa htb
  have hpa : C.pend a ≠ none := (Impl.step_tau h1).1
  have hb' := Impl.step_other h1 (q := b) (by simpa [Label.proc] using hab)
  have hpb : C.pend b ≠ none := by rw [← hb'.2]; exact (Impl.step_tau h2).1
  rcases hnc i j o o' k k' hpa hpb hai hbj with h | ⟨h, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h _, h' _⟩

/-- Moving a step of `b` to the left of a sequence of steps of `a`. -/
lemma move_left {a b : P} (hab : a ≠ b) (G : Lbl P X V → Prop) {t : Lbl P X V}
    (ht : t.proc = b) :
    ∀ (σ : List (Lbl P X V)) (C D : Config (tmSpec X V) B P L), (∀ ℓ ∈ σ, ℓ.proc = a ∧ G ℓ) →
      NoContendFrom I G C a b → I.runFrom C (σ ++ [t]) = some D → I.runFrom C (t :: σ) = some D
  | [], C, D, _, _, h => by simpa using h
  | s :: σ, C, D, hσ, hnc, h => by
    simp only [List.cons_append, Impl.runFrom_cons] at h
    cases hs : I.step C s with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      have ih := move_left hab G ht σ C₁ D (fun ℓ h => hσ ℓ (by simp [h]))
        (hnc.step (hσ s (by simp)).2 hs) h
      simp only [Impl.runFrom_cons] at ih
      cases ht' : I.step C₁ t with
      | none => simp [ht'] at ih
      | some C₂ =>
        simp only [ht', Option.bind_some] at ih
        obtain ⟨Cb, hCb, hCb'⟩ := swap_steps hab (hσ s (by simp)).1 ht hnc.self hs ht'
        simp [hCb, hCb', ih]

/-- **Commutation.** Steps of `a` and steps of `b` that never contend can be reordered. -/
lemma commute {a b : P} (hab : a ≠ b) (G : Lbl P X V → Prop) :
    ∀ (τ σ : List (Lbl P X V)) (C D : Config (tmSpec X V) B P L),
      (∀ ℓ ∈ σ, ℓ.proc = a ∧ G ℓ) → (∀ ℓ ∈ τ, ℓ.proc = b ∧ G ℓ) →
      NoContendFrom I G C a b → I.runFrom C (σ ++ τ) = some D → I.runFrom C (τ ++ σ) = some D
  | [], σ, C, D, _, _, _, h => by simpa using h
  | t :: τ, σ, C, D, hσ, hτ, hnc, h => by
    have h' : I.runFrom C ((σ ++ [t]) ++ τ) = some D := by simpa using h
    rw [Impl.runFrom_append] at h'
    cases h1 : I.runFrom C (σ ++ [t]) with
    | none => simp [h1] at h'
    | some C₁ =>
      simp only [h1, Option.bind_some] at h'
      have hm := move_left hab G (hτ t (by simp)).1 σ C C₁ hσ hnc h1
      simp only [Impl.runFrom_cons] at hm
      cases hs : I.step C t with
      | none => simp [hs] at hm
      | some C₀ =>
        simp only [hs, Option.bind_some] at hm
        have h3 : I.runFrom C₀ (σ ++ τ) = some D := by
          rw [Impl.runFrom_append_of_eq I hm]; exact h'
        have := commute hab G τ σ C₀ D hσ (fun ℓ h => hτ ℓ (by simp [h]))
          (hnc.step (hτ t (by simp)).2 hs) h3
        simp [hs, this]

/-! ### WDAP rules out contention between the two sides -/

/-- Under WDAP, processes on different sides of a partition by accessed objects never contend:
the hypothesis of `commute` holds for any labels whose invocations stay on their side. -/
lemma noContendFrom_of_wdap (hW : WDAP I) {π : List (Lbl P X V)}
    {C : Config (tmSpec X V) B P L} (hπ : I.run π = some C) (G : Lbl P X V → Prop)
    (f : P → Bool) (S : Bool → Set X) (hS : Disjoint (S true) (S false))
    (hf : ∀ p, objs π p ⊆ S (f p))
    (hG : ∀ ℓ, G ℓ → ∀ q o x, ℓ = .inv q o → o.obj = some x → x ∈ S (f q))
    {a b : P} (hab : a ≠ b) (hfab : f a ≠ f b) : NoContendFrom I G C a b := by
  intro ω C' hω hr i j o o' k k' hpa hpb hai hbj
  by_cases hij : i = j
  · subst hij
    by_contra hc
    have hnt : ¬ Trivial o ∨ ¬ Trivial o' := by
      by_contra h'; simp only [not_or, not_not] at h'; exact hc (Or.inr h')
    have hrun : I.run (π ++ ω) = some C' := by rw [Impl.run_append_of_eq I hπ]; exact hr
    have hconn := hW _ _ hrun a b hab hpa hpb i o o' k k' hai hbj hnt
    refine hfab (connected_side f S hS ?_ hconn)
    intro p x hx
    obtain ⟨o₁, ho₁, hx⟩ := hx
    simp only [opsOf_append, List.mem_append] at ho₁
    rcases ho₁ with ho₁ | ho₁
    · exact hf p ⟨o₁, ho₁, hx⟩
    · simp only [opsOf, List.mem_filterMap] at ho₁
      obtain ⟨ℓ, hℓ, hinv⟩ := ho₁
      have := Label.eq_inv_of_invOf_eq_some hinv
      exact hG ℓ (hω ℓ hℓ) p o₁ x this hx
  · exact Or.inl hij

end Podc.DAPInvisibleReads
