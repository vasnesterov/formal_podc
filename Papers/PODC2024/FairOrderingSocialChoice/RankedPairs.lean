import Mathlib

/-!
# Ranked Pairs: the greedy acyclic edge selection

Ranked Pairs (Tideman; Algorithm 2 of Ramseyer–Goel) iterates over the ordered pairs `(a, b)` of
distinct candidates in decreasing order of weight and accepts an edge unless it closes a directed
cycle with the edges accepted so far. The output ranking is the transitive closure of the accepted
edges.

We abstract the processing order as a `key : α × α → β` into a well-founded linear order: edges are
processed in increasing `key`. Ranked Pairs is the case where `key` is weight-antitone (heavier
edges first) and injective (ties broken by a fixed rule). Candidates range over a set `S`.

* `accepted S key e`: the edge `e` is accepted (defined by well-founded recursion on `key`).
* `before S key e`: the edges accepted before `e` is processed.
* `rpLt S key`: the output relation (transitive closure of accepted edges).
* `rpLt_irrefl` (acyclicity), `rpLt_total`: the output is a strict total order on `S`.
* `rejected_path` (Lemma 5.3 shape): a rejected edge `(a, b)` is closed by a path `b ⇝ a` of
  edges accepted earlier.
* `accepted_of_top`: an edge is accepted if every earlier accepted edge belongs to a relation `U`
  that contains it and is acyclic (used for Observation 5.4: weight-1 edges are always accepted).
-/

-- CSLib candidate: a generic `Ranked Pairs` / greedy-acyclic-selection module for
-- `Cslib/Foundations/SocialChoice/`.

namespace Podc.FairOrderingSocialChoice.RP

open Relation

variable {α β : Type*} [LinearOrder β] [WellFoundedLT β]

theorem tg_mono {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : TransGen r a b) : TransGen p a b := TransGen.mono h _ _ hab

theorem rtg_mono {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : ReflTransGen r a b) : ReflTransGen p a b := ReflTransGen.mono h _ _ hab

/-- Ranked Pairs' accepted edges, by well-founded recursion on the processing order `key`:
`e = (a, b)` is accepted iff `a, b ∈ S` are distinct and the edges accepted before `e` contain
no path from `b` to `a`. -/
noncomputable def accepted (S : Set α) (key : α × α → β) : α × α → Prop :=
  (InvImage.wf key wellFounded_lt).fix fun e rec =>
    e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2 ∧
      ¬ ReflTransGen (fun x y => ∃ h : key (x, y) < key e, rec (x, y) h) e.2 e.1

/-- The edges accepted before `e` is processed. -/
def before (S : Set α) (key : α × α → β) (e : α × α) (x y : α) : Prop :=
  key (x, y) < key e ∧ accepted S key (x, y)

theorem accepted_iff (S : Set α) (key : α × α → β) (e : α × α) :
    accepted S key e ↔
      e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2 ∧ ¬ ReflTransGen (before S key e) e.2 e.1 := by
  unfold accepted
  rw [WellFounded.fix_eq]
  have : (fun x y => ∃ h : key (x, y) < key e,
      (InvImage.wf key wellFounded_lt).fix (fun e rec => e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2 ∧
        ¬ ReflTransGen (fun x y => ∃ h : key (x, y) < key e, rec (x, y) h) e.2 e.1) (x, y)) =
      fun x y => key (x, y) < key e ∧ (InvImage.wf key wellFounded_lt).fix (fun e rec =>
        e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2 ∧
        ¬ ReflTransGen (fun x y => ∃ h : key (x, y) < key e, rec (x, y) h) e.2 e.1) (x, y) := by
    funext x y; apply propext; exact ⟨fun ⟨h, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
  rw [this]; rfl

/-- The output relation of Ranked Pairs: `a` is ranked before `b`. -/
def rpLt (S : Set α) (key : α × α → β) (a b : α) : Prop :=
  TransGen (fun x y => accepted S key (x, y)) a b

variable {S : Set α} {key : α × α → β}

theorem mem_of_accepted {e : α × α} (h : accepted S key e) : e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2 :=
  let ⟨h1, h2, h3, _⟩ := (accepted_iff S key e).1 h; ⟨h1, h2, h3⟩

/-- **Lemma 5.3 (shape).** If Ranked Pairs rejects an edge `(a, b)` between distinct candidates,
the edges accepted before it contain a path from `b` to `a`. -/
theorem rejected_path {a b : α} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (h : ¬ accepted S key (a, b)) : ReflTransGen (before S key (a, b)) b a := by
  by_contra h'
  exact h ((accepted_iff S key _).2 ⟨ha, hb, hab, h'⟩)

/-! ### Acyclicity -/

section Acyclic

/-- First-use decomposition: a path in `R ∪ {e}` either avoids `e` or reaches `e.1` in `R`. -/
theorem reflTransGen_sup_single {R : α → α → Prop} {p q : α} {u v : α}
    (h : ReflTransGen (fun x y => R x y ∨ (x = p ∧ y = q)) u v) :
    ReflTransGen R u v ∨ ReflTransGen R u p := by
  induction h with
  | refl => exact Or.inl .refl
  | tail _ hst ih =>
    rcases ih with ih | ih
    · rcases hst with hst | ⟨rfl, rfl⟩
      · exact Or.inl (ih.tail hst)
      · exact Or.inr ih
    · exact Or.inr ih

/-- A path in `R ∪ {(p, q)}` either is an `R`-path or passes through the edge `(p, q)`. -/
theorem transGen_sup_single_split {R : α → α → Prop} {p q : α} {u v : α}
    (h : TransGen (fun x y => R x y ∨ (x = p ∧ y = q)) u v) :
    TransGen R u v ∨ (ReflTransGen (fun x y => R x y ∨ (x = p ∧ y = q)) u p ∧
      ReflTransGen (fun x y => R x y ∨ (x = p ∧ y = q)) q v) := by
  induction h with
  | single h =>
    rcases h with h | ⟨rfl, rfl⟩
    · exact Or.inl (.single h)
    · exact Or.inr ⟨.refl, .refl⟩
  | tail hab hst ih =>
    rcases ih with ih | ⟨ih1, ih2⟩
    · rcases hst with hst | ⟨rfl, rfl⟩
      · exact Or.inl (ih.tail hst)
      · exact Or.inr ⟨(tg_mono (fun _ _ h => Or.inl h) ih).to_reflTransGen, .refl⟩
    · exact Or.inr ⟨ih1, ih2.tail hst⟩

/-- Accepted edges with key `< k`. -/
private def accLt (S : Set α) (key : α × α → β) (k : β) (x y : α) : Prop :=
  key (x, y) < k ∧ accepted S key (x, y)

private def accLe (S : Set α) (key : α × α → β) (k : β) (x y : α) : Prop :=
  key (x, y) ≤ k ∧ accepted S key (x, y)

private theorem transGen_accLt_exists {k : β} {x y : α} (h : TransGen (accLt S key k) x y) :
    ∃ k' < k, TransGen (accLe S key k') x y := by
  induction h with
  | single h => exact ⟨_, h.1, .single ⟨le_rfl, h.2⟩⟩
  | tail _ hst ih =>
    obtain ⟨k', hk', ih⟩ := ih
    refine ⟨max k' (key (_, _)), max_lt hk' hst.1, ?_⟩
    exact .tail (tg_mono (fun _ _ h => ⟨h.1.trans (le_max_left _ _), h.2⟩) ih)
      ⟨le_max_right _ _, hst.2⟩

private theorem transGen_acc_exists {x y : α} (h : rpLt S key x y) :
    ∃ k, TransGen (accLe S key k) x y := by
  induction h with
  | single h => exact ⟨_, .single ⟨le_rfl, h⟩⟩
  | @tail b c _ hst ih =>
    obtain ⟨k', ih⟩ := ih
    refine ⟨max k' (key (b, c)), ?_⟩
    exact .tail (tg_mono (fun _ _ h => ⟨h.1.trans (le_max_left _ _), h.2⟩) ih)
      ⟨le_max_right _ _, hst⟩

/-- Ranked Pairs' accepted edges contain no directed cycle, provided the processing order is
injective on candidate edges (ties broken by a fixed rule). -/
theorem rpLt_irrefl (hkey : ∀ e e' : α × α, e.1 ∈ S → e.2 ∈ S → e'.1 ∈ S → e'.2 ∈ S →
      key e = key e' → e = e') (x : α) : ¬ rpLt S key x x := by
  intro hx
  obtain ⟨k, hk⟩ := transGen_acc_exists hx
  suffices H : ∀ k, ∀ x, ¬ TransGen (accLe S key k) x x from H k x hk
  intro k
  induction k using WellFoundedLT.induction with
  | _ k ih =>
  intro x hx
  -- the cycle in `accLt k` is impossible by induction
  have hlt : ∀ y, ¬ TransGen (accLt S key k) y y := by
    intro y hy
    obtain ⟨k', hk', hy'⟩ := transGen_accLt_exists hy
    exact ih k' hk' y hy'
  by_cases hE : ∃ e, key e = k ∧ accepted S key e
  · obtain ⟨e, rfl, he⟩ := hE
    have hsplit : ∀ u v, accLe S key (key e) u v ↔
        accLt S key (key e) u v ∨ (u = e.1 ∧ v = e.2) := by
      intro u v
      constructor
      · rintro ⟨h1, h2⟩
        rcases h1.lt_or_eq with h1 | h1
        · exact Or.inl ⟨h1, h2⟩
        · right
          have := hkey (u, v) e (mem_of_accepted h2).1 (mem_of_accepted h2).2.1
            (mem_of_accepted he).1 (mem_of_accepted he).2.1 h1
          rw [← this]; exact ⟨rfl, rfl⟩
      · rintro (⟨h1, h2⟩ | ⟨rfl, rfl⟩)
        · exact ⟨h1.le, h2⟩
        · exact ⟨le_rfl, he⟩
    have hx' : TransGen (fun u v => accLt S key (key e) u v ∨ (u = e.1 ∧ v = e.2)) x x :=
      tg_mono (fun u v h => (hsplit u v).1 h) hx
    -- either the cycle avoids `e`, or it gives a path `e.2 ⇝ e.1` of earlier accepted edges
    have key_path : ReflTransGen (accLt S key (key e)) e.2 e.1 → False := by
      intro hp
      rw [accepted_iff] at he
      exact he.2.2.2 (rtg_mono (fun u v h => ⟨h.1, h.2⟩) hp)
    rcases transGen_sup_single_split hx' with h | ⟨h1, h2⟩
    · exact hlt x h
    · rcases reflTransGen_sup_single (h2.trans h1) with h | h
      · exact key_path h
      · exact key_path h
  · push Not at hE
    exact hlt x (tg_mono (fun u v h =>
      ⟨h.1.lt_of_ne fun h' => hE _ h' h.2, h.2⟩) hx)

end Acyclic

/-! ### The output is a strict total order -/

theorem before_le {e : α × α} {x y : α} (h : before S key e x y) : accepted S key (x, y) := h.2

/-- A path of edges accepted before `e` gives the output order. -/
theorem rpLt_of_before {e : α × α} {x y : α} (h : ReflTransGen (before S key e) x y) (hxy : x ≠ y) :
    rpLt S key x y := by
  rcases reflTransGen_iff_eq_or_transGen.1 h with h | h
  · exact absurd h.symm hxy
  · exact tg_mono (fun _ _ h => h.2) h

theorem rpLt_trans {a b c : α} (h₁ : rpLt S key a b) (h₂ : rpLt S key b c) : rpLt S key a c :=
  h₁.trans h₂

/-- Any two distinct candidates are ordered by Ranked Pairs' output. -/
theorem rpLt_total {a b : α} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    rpLt S key a b ∨ rpLt S key b a := by
  by_cases h : accepted S key (a, b)
  · exact Or.inl (.single h)
  · exact Or.inr (rpLt_of_before (rejected_path ha hb hab h) hab.symm)

theorem mem_of_rpLt {a b : α} (h : rpLt S key a b) : a ∈ S ∧ b ∈ S := by
  induction h with
  | single h => exact ⟨(mem_of_accepted h).1, (mem_of_accepted h).2.1⟩
  | tail _ h ih => exact ⟨ih.1, (mem_of_accepted h).2.1⟩

/-- If `rpLt a b` then `(b, a)` was rejected (given injectivity of the order). -/
theorem not_accepted_of_rpLt (hkey : ∀ e e' : α × α, e.1 ∈ S → e.2 ∈ S → e'.1 ∈ S → e'.2 ∈ S →
      key e = key e' → e = e') {a b : α} (h : rpLt S key a b) : ¬ accepted S key (b, a) :=
  fun h' => rpLt_irrefl hkey a (h.tail h')

/-- **Observation 5.4 (shape).** Let `U` be an acyclic relation containing the edge `e` and every
edge accepted before `e`. Then `e` is accepted. (For Ranked Pairs, `U` = the unanimous pairs:
weight-1 edges are processed first and are never rejected.) -/
theorem accepted_of_acyclic {U : α → α → Prop} (hU : ∀ x, ¬ TransGen U x x) {e : α × α}
    (h1 : e.1 ∈ S) (h2 : e.2 ∈ S) (he : U e.1 e.2)
    (hbefore : ∀ x y, before S key e x y → U x y) : accepted S key e := by
  obtain ⟨a, b⟩ := e
  have hne : a ≠ b := by intro h; rw [h] at he; exact hU _ (.single he)
  by_contra hrej
  have := rejected_path (key := key) h1 h2 hne hrej
  exact hU b (TransGen.tail' (rtg_mono hbefore this) he)

end Podc.FairOrderingSocialChoice.RP
