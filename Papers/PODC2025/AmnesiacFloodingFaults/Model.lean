import Mathlib

/-!
# Amnesiac flooding on message configurations (Section 3)

Austin, Gadouleau, Mertzios, Trehan, *Amnesiac Flooding: Easy to Break, Difficult to Escape*
(PODC 2025, brief announcement; full version arXiv 2502.06001).

Model: a simple graph `G`, synchronous rounds. A *configuration* (Definition 3.1) is a set `S` of
directed messages `(u, v)` ("`u` sent the message to `v` in the current round"); it is *on `G`*
(`IsConfig G S`) if every message travels along an edge. One round of amnesiac flooding with
initiator set `I` is the operator `A_{I,G}` of Definition 3.2 (`step G I`):
`(u, v) ∈ A_{I,G}(S)` iff `uv ∈ E`, `(v, u) ∉ S`, and `u` received a message in `S` or `u ∈ I`.
`af G = A_{∅,G}` is the fault-free round without new initiators.

* `Terminates G S` — `A_∅^k(S) = ∅` for some `k`;
* `runFrom G Is S` — apply `A_{I_1}, …, A_{I_k}` (multicast, Lemma 3.1 / Theorem 2.1);
* `Reachable G S` — `S = A_{I_k} ⋯ A_{I_1}(∅)` for some sequence (Theorem 5.5 (2));
* `rev S` — the reversed configuration `S̄` (Definition 5.5);
* `sources G S` — the nodes sending to all their neighbours (the sinks of `S̄`).

Main results: `lemma_5_2` (time reversal) and `lemma_5_3`.
-/

namespace AmnesiacFloodingFaults

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A configuration of messages (Definition 3.1): `(u, v) ∈ S` means `u` sent the message to `v`
in the current round. -/
abbrev Config (V : Type*) := Set (V × V)

/-- `S` is a configuration on `G`: every message travels along an edge of `G`. -/
def IsConfig (S : Config V) : Prop := ∀ u v, (u, v) ∈ S → G.Adj u v

/-- `u` is *active* in `S`: it received a message. -/
def Active (S : Config V) (u : V) : Prop := ∃ w, (w, u) ∈ S

/-- The operator `A_{I,G}` of Definition 3.2: one round of amnesiac flooding in which the nodes of
`I` initiate (send to all neighbours). -/
def step (I : Set V) (S : Config V) : Config V :=
  {e | G.Adj e.1 e.2 ∧ (e.2, e.1) ∉ S ∧ (e.1 ∈ I ∨ Active S e.1)}

/-- One fault-free round `A_{∅,G}`. -/
abbrev af (S : Config V) : Config V := step G ∅ S

/-- Amnesiac flooding started from the configuration `S` terminates. -/
def Terminates (S : Config V) : Prop := ∃ k, (af G)^[k] S = ∅

/-- Multicast: apply `A_{I_1,G}`, then `A_{I_2,G}`, … to `S`, where `Is = [I_1, I_2, …]`. -/
def runFrom : List (Set V) → Config V → Config V
  | [], S => S
  | I :: Is, S => runFrom Is (step G I S)

/-- `S` arises from the empty configuration by a sequence of multicasts
(statement (2) of Theorem 5.5). -/
def Reachable (S : Config V) : Prop := ∃ Is : List (Set V), runFrom G Is ∅ = S

/-- The reversed configuration `S̄` of Definition 5.5. -/
def rev (S : Config V) : Config V := {e | (e.2, e.1) ∈ S}

/-- The nodes that send to all of their neighbours in `S`, i.e. the sinks of `S̄`. -/
def sources (S : Config V) : Set V := {u | ∀ v, G.Adj u v → (u, v) ∈ S}

variable {G}

@[simp] lemma mem_step {I : Set V} {S : Config V} {u v : V} :
    (u, v) ∈ step G I S ↔ G.Adj u v ∧ (v, u) ∉ S ∧ (u ∈ I ∨ Active S u) := Iff.rfl

@[simp] lemma mem_rev {S : Config V} {u v : V} : (u, v) ∈ rev S ↔ (v, u) ∈ S := Iff.rfl

@[simp] lemma rev_rev (S : Config V) : rev (rev S) = S := by ext ⟨u, v⟩; simp

@[simp] lemma rev_empty : rev (∅ : Config V) = ∅ := by ext ⟨u, v⟩; simp

@[simp] lemma step_empty_empty : step G ∅ (∅ : Config V) = ∅ := by
  ext ⟨u, v⟩; simp [Active]

lemma iterate_af_empty (k : ℕ) : (af G)^[k] (∅ : Config V) = ∅ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; exact step_empty_empty

lemma isConfig_step (I : Set V) (S : Config V) : IsConfig G (step G I S) :=
  fun _ _ h => h.1

lemma isConfig_iterate {S : Config V} (hS : IsConfig G S) (k : ℕ) :
    IsConfig G ((af G)^[k] S) := by
  cases k with
  | zero => exact hS
  | succ k => rw [Function.iterate_succ_apply']; exact isConfig_step _ _

lemma IsConfig.rev {S : Config V} (hS : IsConfig G S) : IsConfig G (rev S) :=
  fun u v h => (hS v u h).symm

lemma isConfig_empty : IsConfig G (∅ : Config V) := fun _ _ h => h.elim

lemma Terminates.of_iterate {S : Config V} {k : ℕ} (h : Terminates G ((af G)^[k] S)) :
    Terminates G S := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m + k, by rw [Function.iterate_add_apply]; exact hm⟩

lemma terminates_iterate_iff {S : Config V} {k : ℕ} :
    Terminates G ((af G)^[k] S) ↔ Terminates G S := by
  refine ⟨Terminates.of_iterate, fun ⟨m, hm⟩ => ⟨m, ?_⟩⟩
  rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hm,
    iterate_af_empty]

@[simp] lemma runFrom_nil (S : Config V) : runFrom G [] S = S := rfl

lemma runFrom_append (Is Js : List (Set V)) (S : Config V) :
    runFrom G (Is ++ Js) S = runFrom G Js (runFrom G Is S) := by
  induction Is generalizing S with
  | nil => rfl
  | cons I Is ih => exact ih _

lemma runFrom_isConfig {Is : List (Set V)} {S : Config V} (hS : IsConfig G S) :
    IsConfig G (runFrom G Is S) := by
  induction Is generalizing S with
  | nil => exact hS
  | cons I Is ih => exact ih (isConfig_step _ _)

lemma Reachable.isConfig {S : Config V} (h : Reachable G S) : IsConfig G S := by
  obtain ⟨Is, rfl⟩ := h
  exact runFrom_isConfig isConfig_empty

lemma Reachable.step {S : Config V} (h : Reachable G S) (I : Set V) :
    Reachable G (step G I S) := by
  obtain ⟨Is, rfl⟩ := h
  exact ⟨Is ++ [I], by rw [runFrom_append]; rfl⟩

lemma reachable_empty : Reachable G (∅ : Config V) := ⟨[], rfl⟩

/-- **Lemma 5.2** (time reversal). Running one round backwards — reverse, apply `A_∅`, reverse
again — and then re-initiating at the nodes `T` that send to all their neighbours in `S` (the
sinks of `S̄`) recovers `S`. The paper's statement defines `T` as the sinks of `S` (a typo: its
proof uses the sinks of `S̄`; see `lemma_5_2_as_stated_false`). -/
theorem lemma_5_2 {S : Config V} (hS : IsConfig G S) :
    step G (sources G S) (rev (af G (rev S))) = S := by
  ext ⟨x, y⟩
  simp only [mem_step, mem_rev, Set.mem_empty_iff_false, false_or, Active, sources,
    Set.mem_ofPred_eq, not_and, not_exists]
  constructor
  · rintro ⟨hxy, h1, h2⟩
    have hsend : ∃ w, (x, w) ∈ S := by
      rcases h2 with h2 | ⟨_, -, -, w, hw⟩
      · exact ⟨y, h2 y hxy⟩
      · exact ⟨w, hw⟩
    obtain ⟨w, hw⟩ := hsend
    by_contra hn
    exact h1 hxy hn w hw
  · intro hxy
    refine ⟨hS x y hxy, fun _ h => (h hxy).elim, ?_⟩
    by_cases hall : ∀ v, G.Adj x v → (x, v) ∈ S
    · exact Or.inl hall
    · push Not at hall
      obtain ⟨z, hz, hzS⟩ := hall
      exact Or.inr ⟨z, hz, hzS, y, hxy⟩

/-- **Lemma 5.3.** For every `k`, `S` is obtained from the configuration `A_∅^k(S̄)` reversed, by a
sequence of `k` multicasts. -/
theorem lemma_5_3 {S : Config V} (hS : IsConfig G S) (k : ℕ) :
    ∃ Is : List (Set V), Is.length = k ∧ runFrom G Is (rev ((af G)^[k] (rev S))) = S := by
  induction k generalizing S with
  | zero => exact ⟨[], rfl, by simp⟩
  | succ k ih =>
    set S' := rev (af G (rev S)) with hS'
    have hc : IsConfig G S' := (isConfig_step _ _).rev
    obtain ⟨Is, hlen, hIs⟩ := ih hc
    refine ⟨Is ++ [sources G S], by simp [hlen], ?_⟩
    rw [runFrom_append]
    have : (af G)^[k] (rev S') = (af G)^[k + 1] (rev S) := by
      rw [hS', rev_rev, Function.iterate_succ_apply]
    rw [← this, hIs]
    exact lemma_5_2 hS

end AmnesiacFloodingFaults
