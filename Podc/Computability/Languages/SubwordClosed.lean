import Cslib.Computability.Languages.RegularLanguage
import Mathlib.Computability.NFA
import Mathlib.Order.WellFoundedSet

/-!
# Subword-closed languages are regular (Haines), and regular languages are closed under letter maps

* `Cslib.Language.IsRegular.of_sublist_closed`: over a finite alphabet, every language that is
  closed under taking subwords (scattered sublists, `List.Sublist`) is regular. Proof: the
  complement is upward closed; by Higman's lemma its minimal elements form a finite antichain `B`,
  so the complement is the finite union of the regular languages `Σ* b₁ Σ* … b_k Σ*`, `b ∈ B`.
* `Cslib.Language.IsRegular.map`: the image of a regular language under a letter-to-letter map
  is regular (via an NFA and the subset construction).

Built for PODC 2012 *Waiting in Dynamic Networks* (`Papers/PODC2012/TVGWaitingExpressivity`).
-- CSLib candidate (both results).
-/

namespace Cslib.Language

open List

variable {α β : Type*}

/-- The words having `b` as a subword. -/
def supWords (b : List α) : Language α := {l | b <+ l}

/-- The words having some word of `B` as a subword. -/
def supWordsOf (B : Set (List α)) : Language α := {l | ∃ b ∈ B, b <+ l}

theorem cons_sublist_iff_exists {x : α} {b l : List α} :
    x :: b <+ l ↔ ∃ l₁ l₂, l = l₁ ++ x :: l₂ ∧ b <+ l₂ := by
  constructor
  · intro h
    induction l with
    | nil => exact absurd h (by simp)
    | cons y l ih =>
      rcases h with _ | ⟨_, h⟩ | ⟨_, h⟩
      · obtain ⟨l₁, l₂, rfl, h₂⟩ := ih ‹_›
        exact ⟨y :: l₁, l₂, rfl, h₂⟩
      · exact ⟨[], l, rfl, h⟩
  · rintro ⟨l₁, l₂, rfl, h⟩
    exact (h.cons_cons x).trans (sublist_append_right _ _)

theorem supWords_cons (x : α) (b : List α) :
    supWords (x :: b) = (⊤ : Language α) * ({[x]} * supWords b) := by
  ext l
  simp only [supWords, Language.mem_mul, cons_sublist_iff_exists]
  constructor
  · rintro ⟨l₁, l₂, rfl, h⟩
    exact ⟨l₁, trivial, [x] ++ l₂, ⟨[x], rfl, l₂, h, rfl⟩, by simp⟩
  · rintro ⟨l₁, -, _, ⟨_, rfl, l₂, h, rfl⟩, rfl⟩
    exact ⟨l₁, l₂, by simp, h⟩

theorem isRegular_supWords (b : List α) : _root_.Language.IsRegular (supWords b) := by
  induction b with
  | nil =>
    have : supWords ([] : List α) = ⊤ := by
      ext l; simp only [supWords, nil_sublist]; exact iff_of_true trivial trivial
    rw [this]; exact Cslib.Language.IsRegular.top
  | cons x b ih =>
    rw [supWords_cons]
    exact Cslib.Language.IsRegular.mul Cslib.Language.IsRegular.top
      (Cslib.Language.IsRegular.mul (Cslib.Language.IsRegular.char x) ih)

theorem isRegular_supWordsOf {B : Set (List α)} (hB : B.Finite) :
    _root_.Language.IsRegular (supWordsOf B) := by
  induction B, hB using Set.Finite.induction_on with
  | empty =>
    have : supWordsOf (∅ : Set (List α)) = 0 := by
      ext l; simp only [supWordsOf, Set.mem_empty_iff_false, false_and, exists_false]; rfl
    rw [this]; exact Cslib.Language.IsRegular.zero
  | @insert b B _ _ ih =>
    have : supWordsOf (insert b B) = supWords b + supWordsOf B := by
      ext l
      simp only [supWordsOf, Set.mem_insert_iff, exists_eq_or_imp, supWords]
      rfl
    rw [this]; exact Cslib.Language.IsRegular.add (isRegular_supWords b) ih

theorem sublistForall₂_eq_iff {l₁ l₂ : List α} : SublistForall₂ (· = ·) l₁ l₂ ↔ l₁ <+ l₂ := by
  rw [sublistForall₂_iff]
  constructor
  · rintro ⟨l, h, hl⟩
    rw [forall₂_eq_eq_eq] at h
    rwa [h]
  · intro h; exact ⟨l₁, forall₂_refl l₁, h⟩

/-- **Higman's lemma** for the subword order over a finite alphabet. -/
theorem sublist_wellQuasiOrdered [Finite α] :
    WellQuasiOrdered (fun l₁ l₂ : List α => l₁ <+ l₂) := by
  have h := Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ (· = ·)
    (Set.finite_univ (α := α)).partiallyWellOrderedOn
  simp only [Set.mem_univ, implies_true, Set.ofPred_true] at h
  rw [Set.partiallyWellOrderedOn_univ_iff] at h
  intro f
  obtain ⟨m, n, hmn, hr⟩ := h f
  exact ⟨m, n, hmn, sublistForall₂_eq_iff.mp hr⟩

/-- **Haines' theorem**: over a finite alphabet, a language closed under subwords is regular. -/
theorem IsRegular.of_sublist_closed [Finite α] {L : Language α}
    (hL : ∀ l ∈ L, ∀ l', l' <+ l → l' ∈ L) : _root_.Language.IsRegular L := by
  -- the minimal words outside `L`
  set B : Set (List α) := {b | b ∉ L ∧ ∀ c, c ∉ L → c <+ b → c = b} with hBdef
  have hanti : IsAntichain (fun l₁ l₂ : List α => l₁ <+ l₂) B := by
    intro b₁ hb₁ b₂ hb₂ hne h
    exact hne (hb₂.2 b₁ hb₁.1 h)
  have hfin : B.Finite := hanti.finite_of_wellQuasiOrdered sublist_wellQuasiOrdered
  have hmin : ∀ c, c ∉ L → ∃ b ∈ B, b <+ c := by
    intro c hc
    have hne : {c' | c' ∉ L ∧ c' <+ c}.Nonempty := ⟨c, hc, Sublist.refl c⟩
    obtain ⟨b, ⟨hbL, hbc⟩, hbmin⟩ :=
      (measure (List.length (α := α))).wf.has_min _ hne
    refine ⟨b, ⟨hbL, fun c' hc'L hc'b => ?_⟩, hbc⟩
    have := hbmin c' ⟨hc'L, hc'b.trans hbc⟩
    exact hc'b.eq_of_length_le (not_lt.mp this)
  have heq : L = (supWordsOf B)ᶜ := by
    ext l
    show l ∈ L ↔ ¬ ∃ b ∈ B, b <+ l
    simp only [not_exists, not_and]
    constructor
    · intro hl b hb hbl
      exact hb.1 (hL l hl b hbl)
    · intro h
      by_contra hl
      obtain ⟨b, hb, hbl⟩ := hmin l hl
      exact h b hb hbl
  rw [heq]
  exact (isRegular_supWordsOf hfin).compl

/-- The NFA reading the image of a DFA's language under a letter map. -/
def _root_.DFA.mapNFA {σ : Type*} (f : α → β) (M : DFA α σ) : NFA β σ where
  step s b := {s' | ∃ a, f a = b ∧ M.step s a = s'}
  start := {M.start}
  accept := M.accept

theorem _root_.DFA.mem_mapNFA_evalFrom {σ : Type*} (f : α → β) (M : DFA α σ) (S : Set σ)
    (w : List β) (s' : σ) :
    s' ∈ (M.mapNFA f).evalFrom S w ↔ ∃ s ∈ S, ∃ l, l.map f = w ∧ M.evalFrom s l = s' := by
  induction w generalizing S with
  | nil =>
    simp only [NFA.evalFrom_nil, List.map_eq_nil_iff, exists_eq_left, DFA.evalFrom_nil]
    constructor
    · intro h; exact ⟨s', h, rfl⟩
    · rintro ⟨s, hs, rfl⟩; exact hs
  | cons b w ih =>
    rw [NFA.evalFrom_cons, ih]
    constructor
    · rintro ⟨s₁, hs₁, l, rfl, hl⟩
      obtain ⟨s, hs, a, rfl, hstep⟩ := NFA.mem_stepSet.mp hs₁
      exact ⟨s, hs, a :: l, rfl, by simp [DFA.evalFrom, hstep, ← hl]⟩
    · rintro ⟨s, hs, l, hlw, hl⟩
      obtain ⟨a, l, rfl⟩ : ∃ a l', l = a :: l' := by
        cases l with
        | nil => simp at hlw
        | cons a l => exact ⟨a, l, rfl⟩
      simp only [List.map_cons, List.cons.injEq] at hlw
      refine ⟨M.step s a, NFA.mem_stepSet.mpr ⟨s, hs, a, hlw.1, rfl⟩, l, hlw.2, ?_⟩
      simpa [DFA.evalFrom] using hl

theorem _root_.DFA.mapNFA_accepts {σ : Type*} (f : α → β) (M : DFA α σ) :
    (M.mapNFA f).accepts = Language.map f M.accepts := by
  ext w
  simp only [NFA.accepts, NFA.eval, Language.map]
  constructor
  · rintro ⟨s', hs', h⟩
    obtain ⟨s, rfl, l, rfl, rfl⟩ := (M.mem_mapNFA_evalFrom f _ w s').mp h
    exact ⟨l, hs', rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨_, hl, (M.mem_mapNFA_evalFrom f _ _ _).mpr ⟨_, rfl, l, rfl, rfl⟩⟩

/-- Regular languages are closed under letter-to-letter maps. -/
theorem IsRegular.map {α β : Type} (f : α → β) {L : Language α} (h : _root_.Language.IsRegular L) :
    _root_.Language.IsRegular (Language.map f L) := by
  classical
  obtain ⟨σ, _, M, rfl⟩ := h
  exact ⟨Set σ, inferInstance, (M.mapNFA f).toDFA, by rw [NFA.toDFA_correct, DFA.mapNFA_accepts]⟩

end Cslib.Language
