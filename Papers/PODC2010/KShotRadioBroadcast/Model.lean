import Mathlib


-- CSLib candidate: oblivious multi-hop radio networks with the k-shot rule (Cslib/Computability/Distributed/Radio/...)
/-!
# Oblivious `k`-shot broadcasting in radio networks (Section 2 of the paper)

Karmakar, Koutris, Pagourtzis, Sakavalas. *k-shot Broadcasting in Ad Hoc Radio Networks*,
arXiv:1603.08393v1 (full version of Koutris–Pagourtzis, PODC 2010 brief announcement).

**Networks.** Nodes are the elements of a finite type `V` (the labels `1, …, n`). A network is a
directed relation `E : V → V → Prop` (`E u v`: `u` can transmit to `v`) together with a source
`s : V`. Undirected (symmetric) networks are the case `E = G.Adj` for a `SimpleGraph G`.

**Oblivious protocols.** An oblivious protocol is a schedule `σ : ℕ → Finset V` of transmission
sets (`σ t` is used at step `t ≥ 1`; `σ 0` is ignored). With the `k`-shot rule, a node that
received the source message at step `r` transmits at the first `k` steps `t > r` with `v ∈ σ t`
(`TransmitsAt`). The source holds the message at step `0`; there are no spontaneous
transmissions.

**Collisions.** Synchronous steps, no collision detection: an uninformed node `v` receives the
message at step `t` iff exactly one of its in-neighbours transmits at step `t` (`recvTime`).
-/

namespace Podc.KShotRadioBroadcast

open Finset

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An oblivious protocol: the transmission set of every step `t ≥ 1`. -/
abbrev Schedule (V : Type*) := ℕ → Finset V

/-- Number of appearances of `v` in the schedule at the steps strictly between `a` and `b`. -/
def count (σ : Schedule V) (v : V) (a b : ℕ) : ℕ :=
  ((Finset.Ioo a b).filter (fun t => v ∈ σ t)).card

/-- The `k`-shot rule: a node `v` that received the message at step `r` transmits at step `t` iff
`t` is one of the first `k` appearances of `v` in the schedule after step `r`. -/
def TransmitsAt (σ : Schedule V) (k r : ℕ) (v : V) (t : ℕ) : Prop :=
  r < t ∧ v ∈ σ t ∧ count σ v r t < k

theorem count_mono {σ : Schedule V} {v : V} {a b b' : ℕ} (hb : b ≤ b') :
    count σ v a b ≤ count σ v a b' := by
  unfold count
  exact card_le_card (filter_subset_filter _ (Ioo_subset_Ioo_right hb))

instance (σ : Schedule V) (k r : ℕ) (v : V) (t : ℕ) : Decidable (TransmitsAt σ k r v t) := by
  unfold TransmitsAt; infer_instance

open Classical in
/-- `recvTime σ k E s t v = some r` iff node `v` has received the source message by step `t`,
namely at step `r ≤ t`. At step `t + 1`, an uninformed node is informed iff exactly one of its
in-neighbours that is informed transmits. -/
noncomputable def recvTime (σ : Schedule V) (k : ℕ) (E : V → V → Prop) (s : V) :
    ℕ → V → Option ℕ
  | 0 => fun v => if v = s then some 0 else none
  | t + 1 => fun v =>
    match recvTime σ k E s t v with
    | some r => some r
    | none =>
      if ∃! u, E u v ∧ ∃ r, recvTime σ k E s t u = some r ∧ TransmitsAt σ k r u (t + 1) then
        some (t + 1) else none

/-- Node `u` transmits at step `t + 1` (it is informed by step `t`, at some step `r`, and `t + 1`
is one of its `k` transmission steps). -/
def Transmits (σ : Schedule V) (k : ℕ) (E : V → V → Prop) (s : V) (t : ℕ) (u : V) : Prop :=
  ∃ r, recvTime σ k E s t u = some r ∧ TransmitsAt σ k r u (t + 1)

/-- Broadcasting is complete at step `t`: every node has received the message. -/
def Complete (σ : Schedule V) (k : ℕ) (E : V → V → Prop) (s : V) (t : ℕ) : Prop :=
  ∀ v, (recvTime σ k E s t v).isSome

/-- An oblivious `k`-shot protocol (schedule `σ`) *correctly broadcasts from `s` on undirected
networks* if on every connected undirected network it completes broadcasting at some step. -/
def CorrectOnUndirected (σ : Schedule V) (k : ℕ) (s : V) : Prop :=
  ∀ G : SimpleGraph V, G.Connected → ∃ t, Complete σ k G.Adj s t

section basic

variable {σ : Schedule V} {k : ℕ} {E : V → V → Prop} {s : V}

@[simp] theorem recvTime_zero (v : V) :
    recvTime σ k E s 0 v = if v = s then some 0 else none := rfl

theorem recvTime_succ_of_some {t : ℕ} {v : V} {r : ℕ} (h : recvTime σ k E s t v = some r) :
    recvTime σ k E s (t + 1) v = some r := by
  simp [recvTime, h]

open Classical in
theorem recvTime_succ_of_none {t : ℕ} {v : V} (h : recvTime σ k E s t v = none) :
    recvTime σ k E s (t + 1) v =
      if ∃! u, E u v ∧ Transmits σ k E s t u then some (t + 1) else none := by
  simp only [recvTime, h, Transmits]
  exact if_congr Iff.rfl rfl rfl

/-- Once informed, a node stays informed with the same reception step. -/
theorem recvTime_mono {t t' : ℕ} (htt : t ≤ t') {v : V} {r : ℕ}
    (h : recvTime σ k E s t v = some r) : recvTime σ k E s t' v = some r := by
  induction htt with
  | refl => exact h
  | step _ ih => exact recvTime_succ_of_some ih

/-- The reception step is at most the current step. -/
theorem recvTime_le {t : ℕ} {v : V} {r : ℕ} (h : recvTime σ k E s t v = some r) : r ≤ t := by
  induction t generalizing r with
  | zero =>
    simp only [recvTime_zero] at h
    split_ifs at h with h1 <;> simp_all
  | succ t ih =>
    cases h' : recvTime σ k E s t v with
    | some r' =>
      rw [recvTime_succ_of_some h'] at h
      cases h; exact (ih h').trans (Nat.le_succ _)
    | none =>
      rw [recvTime_succ_of_none h'] at h
      split_ifs at h <;> simp_all

theorem Complete.mono {t t' : ℕ} (htt : t ≤ t') (h : Complete σ k E s t) :
    Complete σ k E s t' := by
  intro v
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (h v)
  simp [recvTime_mono htt hr]

end basic

/-! ## Appearances and first occurrences -/

open Classical in
/-- The first step after `T` at which `v` appears in the schedule (if any). -/
noncomputable def nextApp (σ : Schedule V) (v : V) (T : ℕ) : Option ℕ :=
  if h : ∃ t, T < t ∧ v ∈ σ t then some (Nat.find h) else none

/-- The step of the (greedy) first occurrence of the sequence `R` after step `T`: `t(R, T)` in
the paper. `occ σ [] T = T`. `none` if `R` does not occur after `T`. -/
noncomputable def occ (σ : Schedule V) : List V → ℕ → Option ℕ
  | [], T => some T
  | v :: R, T => (nextApp σ v T).bind (occ σ R)

section occ

variable {σ : Schedule V}

theorem nextApp_spec {v : V} {T a : ℕ} (h : nextApp σ v T = some a) :
    T < a ∧ v ∈ σ a ∧ ∀ t, T < t → t < a → v ∉ σ t := by
  classical
  unfold nextApp at h
  split_ifs at h with hex
  cases h
  refine ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, fun t h1 h2 h3 => ?_⟩
  exact Nat.find_min hex h2 ⟨h1, h3⟩

theorem nextApp_eq_none {v : V} {T : ℕ} (h : nextApp σ v T = none) :
    ∀ t, T < t → v ∉ σ t := by
  classical
  unfold nextApp at h
  split_ifs at h with hex
  intro t h1 h2; exact hex ⟨t, h1, h2⟩

theorem nextApp_isSome {v : V} {T t : ℕ} (h1 : T < t) (h2 : v ∈ σ t) :
    ∃ a, nextApp σ v T = some a ∧ a ≤ t := by
  classical
  have hex : ∃ t, T < t ∧ v ∈ σ t := ⟨t, h1, h2⟩
  exact ⟨_, by simp [nextApp, hex], Nat.find_min' hex ⟨h1, h2⟩⟩

theorem occ_nil (T : ℕ) : occ σ ([] : List V) T = some T := rfl

theorem occ_cons (v : V) (R : List V) (T : ℕ) :
    occ σ (v :: R) T = (nextApp σ v T).bind (occ σ R) := rfl

theorem occ_append (R R' : List V) (T : ℕ) :
    occ σ (R ++ R') T = (occ σ R T).bind (occ σ R') := by
  induction R generalizing T with
  | nil => simp [occ]
  | cons v R ih =>
    simp only [List.cons_append, occ_cons]
    cases nextApp σ v T <;> simp [ih]

theorem le_of_occ {R : List V} {T a : ℕ} (h : occ σ R T = some a) : T ≤ a := by
  induction R generalizing T with
  | nil => simp [occ] at h; omega
  | cons v R ih =>
    rw [occ_cons] at h
    cases h' : nextApp σ v T with
    | none => simp [h'] at h
    | some b =>
      rw [h'] at h
      exact (nextApp_spec h').1.le.trans (ih h)

end occ

end Podc.KShotRadioBroadcast
