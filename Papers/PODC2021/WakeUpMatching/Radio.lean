import Papers.PODC2021.WakeUpMatching.Basic

/-!
# One round of the maximal matching protocol (Algorithms 1–3) and Lemma 5.1

Dani, Gupta, Hayes, Pettie, PODC 2021 (arXiv:2104.09096v2), Sections 2.3, 4 and 5.

**Radio model (no collision detection).** In each timestep every node sends, listens or sleeps;
a listening node `v` receives the message of `u` iff `u` is the *unique* neighbour of `v` that
sends in this timestep; otherwise (silence or collision) it receives nothing (`recv`).

**One round** (three timesteps) of Algorithm 1, given the current partner variables `partner`
and the roles `ρ` drawn by the nodes (`recruit` with probability `r(t)/2`, `accept` with
probability `r(t)/2`, `sleep` otherwise; nodes with a partner sleep):

* timestep 1: recruiters send their ID; acceptors listen (`hear₁`);
* timestep 2: an acceptor that heard `x` sends `(x, myID)`; recruiters listen (`hear₂`); a
  recruiter that hears `(x, y)` with `x = myID` sets `partner ← y` (`matchR`);
* timestep 3: a matched recruiter sends `(x, y)`; acceptors that sent in timestep 2 listen
  (`hear₃`); an acceptor that hears `(x, y)` with `y = myID` sets `partner ← x` (`matchA`).

Node IDs are the vertices themselves (the paper assumes unique IDs).

* `round_isMatchingState` — **Lemma 5.1** (one step): the partner variables encode a matching after
  every round, for *every* choice of roles (hence with probability one);
* `round_mono` — matched nodes stay matched to the same partner (`M(t) ⊆ M(t')`);
* `round_matches_of_isolated` — the sufficient condition used in the proof of Lemma 5.2.
-/

set_option linter.unusedSectionVars false

namespace Podc.WakeUpMatching

open Finset

/-- The role a node draws for a round. -/
inductive Role
  | recruit
  | accept
  | sleep
  deriving DecidableEq

instance : Fintype Role := ⟨{.recruit, .accept, .sleep}, fun x => by cases x <;> simp⟩

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `v` receives `msg`: exactly one neighbour of `v` sends, and it sends `msg`. -/
def Receives {α : Type*} (send : V → Option α) (v : V) (msg : α) : Prop :=
  ∃ u, G.Adj v u ∧ send u = some msg ∧ ∀ u', G.Adj v u' → (send u').isSome → u' = u

theorem Receives.unique {α : Type*} {send : V → Option α} {v : V} {m₁ m₂ : α}
    (h₁ : Receives G send v m₁) (h₂ : Receives G send v m₂) : m₁ = m₂ := by
  obtain ⟨u₁, a₁, s₁, h₁⟩ := h₁
  obtain ⟨u₂, a₂, s₂, -⟩ := h₂
  have := h₁ u₂ a₂ (by simp [s₂])
  subst this
  exact Option.some_injective _ (s₁.symm.trans s₂)

/-- What a listening node receives (no collision detection: `none` = silence or collision). -/
noncomputable def recv {α : Type*} (send : V → Option α) (v : V) : Option α := by
  classical
  exact if h : ∃ m, Receives G send v m then some h.choose else none

theorem recv_eq_some {α : Type*} {send : V → Option α} {v : V} {m : α} :
    recv G send v = some m ↔ Receives G send v m := by
  classical
  unfold recv
  constructor
  · intro h
    split_ifs at h with hex
    · rw [← Option.some_injective _ h]; exact hex.choose_spec
  · intro h
    rw [dite_eq_left_of_eq_true (eq_true ⟨m, h⟩)]
    exact congrArg some (Receives.unique G (Exists.choose_spec ⟨m, h⟩) h)

section Round

variable (partner : V → Option V) (ρ : V → Role)

/-- `v` is unmatched and recruits in this round. -/
def IsRec (v : V) : Prop := partner v = none ∧ ρ v = .recruit

/-- `v` is unmatched and accepts in this round. -/
def IsAcc (v : V) : Prop := partner v = none ∧ ρ v = .accept

instance (v : V) : Decidable (IsRec partner ρ v) := by unfold IsRec; infer_instance
instance (v : V) : Decidable (IsAcc partner ρ v) := by unfold IsAcc; infer_instance

/-- Timestep 1: recruiters send their ID. -/
def send₁ (u : V) : Option V := if IsRec partner ρ u then some u else none

/-- Timestep 1: what an acceptor hears. -/
noncomputable def hear₁ (a : V) : Option V :=
  if IsAcc partner ρ a then recv G (send₁ partner ρ) a else none

/-- Timestep 2: an acceptor that heard `x` sends `(x, myID)`. -/
noncomputable def send₂ (a : V) : Option (V × V) := (hear₁ G partner ρ a).map fun x => (x, a)

/-- Timestep 2: what a recruiter hears. -/
noncomputable def hear₂ (v : V) : Option (V × V) :=
  if IsRec partner ρ v then recv G (send₂ G partner ρ) v else none

/-- The recruiter's new partner (Algorithm 2, lines 4–6). -/
noncomputable def matchR (v : V) : Option V :=
  match hear₂ G partner ρ v with
  | some (x, y) => if x = v then some y else none
  | none => none

/-- Timestep 3: a matched recruiter sends `(myID, partner)`. -/
noncomputable def send₃ (v : V) : Option (V × V) := (matchR G partner ρ v).map fun y => (v, y)

/-- Timestep 3: what an acceptor that sent in timestep 2 hears. -/
noncomputable def hear₃ (a : V) : Option (V × V) :=
  if IsAcc partner ρ a ∧ (hear₁ G partner ρ a).isSome then recv G (send₃ G partner ρ) a else none

/-- The acceptor's new partner (Algorithm 3, lines 7–9). -/
noncomputable def matchA (a : V) : Option V :=
  match hear₃ G partner ρ a with
  | some (x, y) => if y = a then some x else none
  | none => none

/-- The partner variables after the round. -/
noncomputable def round (v : V) : Option V :=
  if (partner v).isSome then partner v
  else if ρ v = .recruit then matchR G partner ρ v
  else if ρ v = .accept then matchA G partner ρ v
  else none

end Round

/-- The partner variables encode a matching of `G`. -/
def IsMatchingState (partner : V → Option V) : Prop :=
  ∀ v w, partner v = some w → G.Adj v w ∧ partner w = some v

variable {G}

theorem matchR_eq_some {partner : V → Option V} {ρ : V → Role} {v w : V}
    (h : matchR G partner ρ v = some w) :
    IsRec partner ρ v ∧ Receives G (send₂ G partner ρ) v (v, w) := by
  unfold matchR at h
  cases h2 : hear₂ G partner ρ v with
  | none => rw [h2] at h; simp at h
  | some p =>
    obtain ⟨x, y⟩ := p
    rw [h2] at h
    simp only at h
    split_ifs at h with hx
    · subst hx
      cases h
      unfold hear₂ at h2
      split_ifs at h2 with hr
      exact ⟨hr, (recv_eq_some G).1 h2⟩

theorem matchA_eq_some {partner : V → Option V} {ρ : V → Role} {a x : V}
    (h : matchA G partner ρ a = some x) :
    IsAcc partner ρ a ∧ (hear₁ G partner ρ a).isSome ∧
      Receives G (send₃ G partner ρ) a (x, a) := by
  unfold matchA at h
  cases h3 : hear₃ G partner ρ a with
  | none => rw [h3] at h; simp at h
  | some p =>
    obtain ⟨x', y⟩ := p
    rw [h3] at h
    simp only at h
    split_ifs at h with hy
    · subst hy
      cases h
      unfold hear₃ at h3
      split_ifs at h3 with hr
      exact ⟨hr.1, hr.2, (recv_eq_some G).1 h3⟩

theorem hear₁_eq_some {partner : V → Option V} {ρ : V → Role} {a x : V}
    (h : hear₁ G partner ρ a = some x) :
    IsAcc partner ρ a ∧ Receives G (send₁ partner ρ) a x := by
  unfold hear₁ at h
  split_ifs at h with ha
  exact ⟨ha, (recv_eq_some G).1 h⟩

theorem send₁_eq_some {partner : V → Option V} {ρ : V → Role} {u x : V}
    (h : send₁ partner ρ u = some x) : IsRec partner ρ u ∧ x = u := by
  unfold send₁ at h
  split_ifs at h with hu
  exact ⟨hu, (Option.some_injective _ h).symm⟩

theorem send₂_eq_some {partner : V → Option V} {ρ : V → Role} {a x y : V}
    (h : send₂ G partner ρ a = some (x, y)) : hear₁ G partner ρ a = some x ∧ y = a := by
  unfold send₂ at h
  cases h1 : hear₁ G partner ρ a with
  | none => rw [h1] at h; simp at h
  | some x' => rw [h1] at h; simp only [Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at h; exact ⟨by rw [h.1], h.2.symm⟩

theorem send₃_eq_some {partner : V → Option V} {ρ : V → Role} {v x y : V}
    (h : send₃ G partner ρ v = some (x, y)) : matchR G partner ρ v = some y ∧ x = v := by
  unfold send₃ at h
  cases h1 : matchR G partner ρ v with
  | none => rw [h1] at h; simp at h
  | some y' => rw [h1] at h; simp only [Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at h; exact ⟨by rw [h.2], h.1.symm⟩

/-- If a recruiter `v` matches with `w`, then `w` is an acceptor neighbour that heard `v`. -/
theorem matchR_spec {partner : V → Option V} {ρ : V → Role} {v w : V}
    (h : matchR G partner ρ v = some w) :
    IsRec partner ρ v ∧ G.Adj v w ∧ hear₁ G partner ρ w = some v := by
  obtain ⟨hr, u, hvu, hs, -⟩ := matchR_eq_some h
  obtain ⟨h1, rfl⟩ := send₂_eq_some hs
  exact ⟨hr, hvu, h1⟩

/-- If an acceptor `a` matches with `x`, then `x` is a recruiter neighbour that matched with `a`. -/
theorem matchA_spec {partner : V → Option V} {ρ : V → Role} {a x : V}
    (h : matchA G partner ρ a = some x) :
    IsAcc partner ρ a ∧ G.Adj a x ∧ matchR G partner ρ x = some a := by
  obtain ⟨ha, -, u, hau, hs, -⟩ := matchA_eq_some h
  obtain ⟨hm, rfl⟩ := send₃_eq_some hs
  exact ⟨ha, hau, hm⟩

/-- Conversely, a recruiter's match is reciprocated by the acceptor (timestep 3 is collision
free at the acceptor, because the acceptor heard a unique recruiter in timestep 1). -/
theorem matchA_of_matchR {partner : V → Option V} {ρ : V → Role} {v w : V}
    (h : matchR G partner ρ v = some w) : matchA G partner ρ w = some v := by
  obtain ⟨hr, hvw, h1⟩ := matchR_spec h
  obtain ⟨ha, u, hwu, hs, huniq⟩ := hear₁_eq_some h1
  obtain ⟨-, rfl⟩ := send₁_eq_some hs
  -- `w` hears `(v, w)` in timestep 3
  have hrecv : Receives G (send₃ G partner ρ) w (v, w) := by
    refine ⟨v, hwu, by simp [send₃, h], fun u' hu' hs' => ?_⟩
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs'
    obtain ⟨y', hy'⟩ : ∃ y', matchR G partner ρ u' = some y' := by
      unfold send₃ at hy
      cases hm : matchR G partner ρ u' with
      | none => rw [hm] at hy; simp at hy
      | some y' => exact ⟨y', rfl⟩
    exact huniq u' hu' (by simp [send₁, (matchR_spec hy').1])
  have h3 : hear₃ G partner ρ w = some (v, w) := by
    unfold hear₃
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨ha, by simp [h1]⟩)]
    exact (recv_eq_some G).2 hrecv
  simp [matchA, h3]

/-- **Lemma 5.1** (inductive step): if the partner variables encode a matching before a round,
they encode a matching after it, whatever roles the nodes chose. -/
theorem round_isMatchingState {partner : V → Option V} (hp : IsMatchingState G partner)
    (ρ : V → Role) : IsMatchingState G (round G partner ρ) := by
  intro v w h
  unfold round at h
  by_cases hv : (partner v).isSome
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hv)] at h
    obtain ⟨hvw, hwv⟩ := hp v w h
    exact ⟨hvw, by simp [round, hwv]⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false hv)] at h
  have hv' : partner v = none := by simpa using hv
  split_ifs at h with hrec hacc
  · -- `v` recruited
    obtain ⟨-, hvw, h1⟩ := matchR_spec h
    obtain ⟨⟨hw, hwa⟩, -⟩ := hear₁_eq_some h1
    refine ⟨hvw, ?_⟩
    simp [round, hw, hwa, matchA_of_matchR h]
  · -- `v` accepted
    obtain ⟨-, hvw, hm⟩ := matchA_spec h
    obtain ⟨hw, hwr⟩ := (matchR_spec hm).1
    refine ⟨hvw, ?_⟩
    simp [round, hw, hwr, hm]

/-- Matched nodes keep their partner: `M(t) ⊆ M(t + 1)`. -/
theorem round_mono {partner : V → Option V} {ρ : V → Role} {v w : V}
    (h : partner v = some w) : round G partner ρ v = some w := by
  simp [round, h]

/-- The partner variables after `t` rounds of Algorithm 1 with role choices `ρ 1, …, ρ t`. -/
noncomputable def partnerAfter (G : SimpleGraph V) [DecidableRel G.Adj] (ρ : ℕ → V → Role) :
    ℕ → V → Option V
  | 0 => fun _ => none
  | t + 1 => round G (partnerAfter G ρ t) (ρ (t + 1))

/-- **Lemma 5.1.** For every sequence of role choices (so with probability one), at the end of
every round `t ≥ 0` the partner variables encode a matching `M(t)`. -/
theorem lemma_5_1 (ρ : ℕ → V → Role) (t : ℕ) : IsMatchingState G (partnerAfter G ρ t) := by
  induction t with
  | zero => intro v w h; simp only [partnerAfter, reduceCtorEq] at h
  | succ t ih => exact round_isMatchingState ih (ρ (t + 1))

/-- The sufficient condition in the proof of Lemma 5.2: if unmatched neighbours `v` (recruiter)
and `w` (acceptor) are such that no other unmatched neighbour of `w` recruits and no other
unmatched neighbour of `v` accepts, then `v` and `w` get matched to each other. -/
theorem round_matches_of_isolated {partner : V → Option V} {ρ : V → Role} {v w : V}
    (hvw : G.Adj v w) (hv : IsRec partner ρ v) (hw : IsAcc partner ρ w)
    (hNw : ∀ u, G.Adj w u → u ≠ v → ¬ IsRec partner ρ u)
    (hNv : ∀ u, G.Adj v u → u ≠ w → ¬ IsAcc partner ρ u) :
    round G partner ρ v = some w ∧ round G partner ρ w = some v := by
  -- timestep 1: `w` hears `v`
  have h1 : hear₁ G partner ρ w = some v := by
    unfold hear₁
    rw [ite_eq_left_of_eq_true _ _ (eq_true hw)]
    refine (recv_eq_some G).2 ⟨v, hvw.symm, by simp [send₁, hv], fun u hu hs => ?_⟩
    by_contra hne
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hs
    exact hNw u hu hne (send₁_eq_some hx).1
  -- timestep 2: `v` hears `(v, w)`
  have h2 : matchR G partner ρ v = some w := by
    have : hear₂ G partner ρ v = some (v, w) := by
      unfold hear₂
      rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
      refine (recv_eq_some G).2 ⟨w, hvw, by simp [send₂, h1], fun u hu hs => ?_⟩
      by_contra hne
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hs
      obtain ⟨x, y⟩ := p
      exact hNv u hu hne (hear₁_eq_some (send₂_eq_some hp).1).1
    simp [matchR, this]
  have hvn : (partner v).isSome = false := by simp [hv.1]
  have hwn : (partner w).isSome = false := by simp [hw.1]
  refine ⟨by simp [round, hvn, hv.2, h2], ?_⟩
  simp [round, hwn, hw.2, matchA_of_matchR h2]

end Podc.WakeUpMatching
