import Papers.PODC2012.TVGWaitingExpressivity.FromDFA
import Podc.Computability.Languages.SubwordClosed

/-!
# Waiting allowed: `𝓛_wait` is the class of regular languages (Theorem 4.1)

The paper's proof goes through a quasi-order `≺` on *words* (Lemma 4.2, Propositions 4.3–4.9,
Theorem 4.12) and a theorem of Harju–Ilie (Theorem 4.7); several of those steps are broken (see
`README.md`). We prove Theorem 4.1 by working on *walks* (words over the finite alphabet of edges)
instead, which is the idea of the paper's Lemma 4.2 made exact:

* `Sched.sublist` (Lemma 4.2, corrected): if an edge sequence can be scheduled with waiting, so can
  each of its subsequences — use, for each kept edge, the departure date it had in the original
  journey; the dropped edges become pauses.
* Hence the set of schedulable edge sequences is closed under subwords and therefore regular
  (Haines' theorem, `Cslib.Language.IsRegular.of_sublist_closed`, from Higman's lemma).
* Intersecting with the (regular) set of walks from an initial to an accepting node and projecting
  each edge to its label gives `L_wait(G)`; regular languages are closed under both operations.

The argument never uses that time is discrete, nor any property of `ρ` and `ζ`.
-/

namespace Podc.TVGWaitingExpressivity

open TVG TVGAutomaton List

variable {V α : Type*}

/-- `IsWalk u l v`: the edge sequence `l` is a walk from `u` to `v` in the footprint. -/
def IsWalk : V → List (V × α × V) → V → Prop
  | u, [], v => u = v
  | u, e :: l, v => e.1 = u ∧ IsWalk e.2.2 l v

namespace TVG

variable (G : TVG V α)

/-- `G.Sched t l`: the edge sequence `l` can be traversed, waiting allowed, by a journey that is at
the start node of `l` at time `t`. -/
def Sched : ℕ → List (V × α × V) → Prop
  | _, [] => True
  | t, e :: l => ∃ t₁, t ≤ t₁ ∧ G.present e t₁ ∧ Sched (t₁ + G.latency e t₁) l

variable {G}

/-- Starting earlier never hurts when waiting is allowed. -/
theorem Sched.anti {t₀ t : ℕ} {l : List (V × α × V)} (h : t₀ ≤ t) (hs : G.Sched t l) :
    G.Sched t₀ l := by
  cases l with
  | nil => trivial
  | cons e l =>
    obtain ⟨t₁, ht₁, hp, hl⟩ := hs
    exact ⟨t₁, h.trans ht₁, hp, hl⟩

/-- **Lemma 4.2** of [CFGSY'12], in the form used: with waiting allowed, every subsequence of a
schedulable edge sequence is schedulable (from the same start date). -/
theorem Sched.sublist {l' l : List (V × α × V)} (hsub : l' <+ l) :
    ∀ {t}, G.Sched t l → G.Sched t l' := by
  induction hsub with
  | slnil => intro _ _; trivial
  | cons e _ ih =>
    intro t ⟨t₁, ht₁, _, hl⟩
    exact (ih hl).anti (by omega)
  | cons_cons e _ ih =>
    intro t ⟨t₁, ht₁, hp, hl⟩
    exact ⟨t₁, ht₁, hp, ih hl⟩

/-- Journeys with waiting are exactly schedulable walks. -/
theorem exists_journey_wait_iff {u : V} {t : ℕ} {w : List α} {v : V} :
    (∃ t', G.Journey wait u t w v t') ↔
      ∃ l, IsWalk u l v ∧ l.map (fun e => e.2.1) = w ∧ G.Sched t l := by
  induction w generalizing u t with
  | nil =>
    simp only [journey_nil_iff]
    constructor
    · rintro ⟨_, rfl, rfl⟩; exact ⟨[], rfl, rfl, trivial⟩
    · rintro ⟨l, hl, hlw, -⟩
      rw [map_eq_nil_iff] at hlw
      subst hlw
      exact ⟨t, Eq.symm hl, rfl⟩
  | cons a w ih =>
    simp only [journey_cons_iff]
    constructor
    · rintro ⟨t', v', t₁, ht₁, hp, hj⟩
      obtain ⟨l, hl, hlw, hs⟩ := ih.mp ⟨t', hj⟩
      exact ⟨(u, a, v') :: l, ⟨rfl, hl⟩, by simp [hlw], t₁, ht₁, hp, hs⟩
    · rintro ⟨l, hl, hlw, hs⟩
      cases l with
      | nil => simp at hlw
      | cons e l =>
        obtain ⟨u', a', v'⟩ := e
        obtain ⟨rfl, hl⟩ := hl
        simp only [map_cons, cons.injEq] at hlw
        obtain ⟨rfl, hlw⟩ := hlw
        obtain ⟨t₁, ht₁, hp, hs⟩ := hs
        obtain ⟨t', hj⟩ := ih.mpr ⟨l, hl, hlw, hs⟩
        exact ⟨t', v', t₁, ht₁, hp, hj⟩

end TVG

section WalksDFA

open Classical

/-- A DFA over the edge alphabet recognising the walks from a node of `I` to a node of `F`.
States: `none` = dead, `some none` = nothing read yet, `some (some v)` = the walk is at `v`. -/
noncomputable def walksDFA (I F : Set V) : DFA (V × α × V) (Option (Option V)) where
  step
    | some none, e => if e.1 ∈ I then some (some e.2.2) else none
    | some (some u), e => if e.1 = u then some (some e.2.2) else none
    | none, _ => none
  start := some none
  accept := {x | (x = some none ∧ ∃ s ∈ I, s ∈ F) ∨ ∃ v ∈ F, x = some (some v)}

theorem walksDFA_evalFrom_none (I F : Set V) (l : List (V × α × V)) :
    (walksDFA I F).evalFrom none l = none := by
  induction l with
  | nil => rfl
  | cons e l ih => exact ih

theorem walksDFA_evalFrom_some (I F : Set V) (u : V) (l : List (V × α × V)) :
    (walksDFA (α := α) I F).evalFrom (some (some u)) l ∈ (walksDFA (α := α) I F).accept ↔
      ∃ v ∈ F, IsWalk u l v := by
  induction l generalizing u with
  | nil =>
    simp only [DFA.evalFrom_nil, walksDFA, Set.mem_ofPred_eq, reduceCtorEq, false_and, false_or,
      Option.some.injEq, IsWalk]
  | cons e l ih =>
    rw [DFA.evalFrom_cons]
    by_cases he : e.1 = u
    · have : (walksDFA I F).step (some (some u)) e = some (some e.2.2) := by
        simp [walksDFA, he]
      rw [this, ih]
      simp [IsWalk, he]
    · have : (walksDFA I F).step (some (some u)) e = none := by
        simp [walksDFA, he]
      rw [this, walksDFA_evalFrom_none]
      simp [walksDFA, IsWalk, he]

/-- The walks from a node of `I` to a node of `F`, as a language over the edges. -/
def walks (I F : Set V) : Language (V × α × V) := {l | ∃ s ∈ I, ∃ f ∈ F, IsWalk s l f}

theorem mem_walks {I F : Set V} {l : List (V × α × V)} :
    l ∈ walks I F ↔ ∃ s ∈ I, ∃ f ∈ F, IsWalk s l f := Iff.rfl

theorem walksDFA_accepts (I F : Set V) : (walksDFA (α := α) I F).accepts = walks I F := by
  ext l
  rw [mem_walks]
  change (walksDFA (α := α) I F).evalFrom (some none) l ∈ (walksDFA (α := α) I F).accept ↔ _
  cases l with
  | nil =>
    simp only [DFA.evalFrom_nil, walksDFA, Set.mem_ofPred_eq, true_and, Option.some.injEq,
      reduceCtorEq, and_false, exists_false, or_false, IsWalk]
    constructor
    · rintro ⟨s, hs, hf⟩; exact ⟨s, hs, s, hf, rfl⟩
    · rintro ⟨s, hs, f, hf, rfl⟩; exact ⟨s, hs, hf⟩
  | cons e l =>
    rw [DFA.evalFrom_cons]
    by_cases he : e.1 ∈ I
    · have : (walksDFA (α := α) I F).step (some none) e = some (some e.2.2) := by
        simp [walksDFA, he]
      rw [this, walksDFA_evalFrom_some]
      simp only [IsWalk]
      constructor
      · rintro ⟨v, hv, hw⟩; exact ⟨e.1, he, v, hv, rfl, hw⟩
      · rintro ⟨s, -, v, hv, -, hw⟩; exact ⟨v, hv, hw⟩
    · have : (walksDFA (α := α) I F).step (some none) e = none := by
        simp [walksDFA, he]
      rw [this, walksDFA_evalFrom_none]
      simp only [walksDFA, Set.mem_ofPred_eq, reduceCtorEq, false_and, false_or, and_false,
        exists_false, IsWalk]
      constructor
      · rintro ⟨v, -, ⟨⟩⟩
      · rintro ⟨s, hs, f, -, rfl, -⟩; exact absurd hs he

end WalksDFA

/-- `L_wait(G)` is the label image of the schedulable walks from `I` to `F`. -/
theorem Lwait_eq_map (A : TVGAutomaton V α) :
    A.Lwait = Language.map (fun e : V × α × V => e.2.1)
      ((walksDFA A.init A.accept).accepts ⊓ {l | A.Sched A.start l}) := by
  ext w
  rw [walksDFA_accepts]
  simp only [Lwait, lang, Language.map]
  change (∃ s ∈ A.init, ∃ f ∈ A.accept, ∃ t', _) ↔ ∃ l, _ ∧ _
  constructor
  · rintro ⟨s, hs, f, hf, h⟩
    obtain ⟨l, hl, hlw, hsch⟩ := exists_journey_wait_iff.mp h
    exact ⟨l, ⟨⟨s, hs, f, hf, hl⟩, hsch⟩, hlw⟩
  · rintro ⟨l, ⟨⟨s, hs, f, hf, hl⟩, hsch⟩, hlw⟩
    exact ⟨s, hs, f, hf, exists_journey_wait_iff.mpr ⟨l, hl, hlw, hsch⟩⟩

/-- The hard inclusion of Theorem 4.1: for every TVG-automaton with finitely many nodes over a
finite alphabet, `L_wait(G)` is regular (for arbitrary presence and latency functions). -/
theorem Lwait_isRegular {V α : Type} [Finite V] [Finite α] (A : TVGAutomaton V α) :
    A.Lwait.IsRegular := by
  have := Fintype.ofFinite V
  rw [Lwait_eq_map]
  apply Cslib.Language.IsRegular.map
  apply Language.IsRegular.inf
  · exact ⟨_, inferInstance, _, rfl⟩
  · exact Cslib.Language.IsRegular.of_sublist_closed fun l hl l' hl' => Sched.sublist hl' hl

/-- **Theorem 4.1** of [CFGSY'12]: `𝓛_wait = 𝓡`, the languages accepted by TVG-automata when
waiting is allowed are exactly the regular languages (over any finite alphabet). -/
theorem theorem_4_1 (α : Type) [Finite α] : LwaitFamily α = {L | L.IsRegular} := by
  ext L
  constructor
  · rintro ⟨V, _, A, rfl⟩
    exact Lwait_isRegular A
  · exact isRegular_mem_LwaitFamily

end Podc.TVGWaitingExpressivity
