import Papers.PODC2013.SourceDetectionCongest.Basic

/-!
# Algorithm 1: pipelined Bellman–Ford

Synchronous rounds on the communication relation `E` (`E u v`: `u` can send to `v`). In every
round each node `v`

* (Lines 7–10) sends the `β` lexicographically smallest entries `(h_s, s)` of its list `L_v` that
  are not yet marked as sent to all its out-neighbours, and marks them as sent
  (the paper's algorithm is `β = 1`: "the smallest unsent pair");
* (Lines 11–15) for every received pair `(h_s, s)` such that `L_v` has no entry `(h', s)` with
  `h' ≤ h_s + 1`, replaces the entry for `s` by `(h_s + 1, s)` and marks it unsent;
* (Line 16, optional) deletes all entries with distance `> cap`.

The journal pseudocode places Line 16 *after* the loop (`cap = ⊤` here, the deletion is done by
`output`); a per-round deletion (as one may also read the pseudocode) is `cap = h`. Both variants
are covered.

`L_v` has at most one entry per source, so we store it as a function `est : V → ℕ∞`
(`est s = ⊤`: no entry for `s`), together with the flags `sent : V → Bool`. Processing the
received pairs one by one (Lines 11–15) gives the same result as taking, for every `s`, the minimum
received distance (`recv`), which is what `step` does.
-/

namespace Podc.SourceDetectionCongest

open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Local state of a node: its list `L_v` (as `est`, `⊤` = no entry) and the `sent_v` flags. -/
structure State (V : Type*) where
  /-- `est s = h` iff `(h, s) ∈ L_v`; `est s = ⊤` iff `L_v` has no entry for `s`. -/
  est : V → ℕ∞
  /-- The flag `sent_v` of the entry for `s`. -/
  sent : V → Bool

namespace State

/-- The list `L_v` as a set of lexicographically ordered pairs. -/
noncomputable def entries (st : State V) : Finset (ℕ ×ₗ V) :=
  (univ.filter fun s => st.est s ≠ ⊤).image fun s => toLex ((st.est s).toNat, s)

/-- The entries of `L_v` with `sent_v = false`. -/
noncomputable def unsent (st : State V) : Finset (ℕ ×ₗ V) :=
  (univ.filter fun s => st.est s ≠ ⊤ ∧ st.sent s = false).image
    fun s => toLex ((st.est s).toNat, s)

variable {st : State V} {m : ℕ} {s : V}

lemma mem_entries : toLex (m, s) ∈ st.entries ↔ st.est s = m := by
  simp only [entries, mem_image, mem_filter, mem_univ, true_and, EmbeddingLike.apply_eq_iff_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨s', hs', rfl, rfl⟩; exact (ENat.natCast_toNat hs').symm
  · intro h; exact ⟨s, by simp [h], by simp [h], rfl⟩

lemma mem_unsent : toLex (m, s) ∈ st.unsent ↔ st.est s = m ∧ st.sent s = false := by
  simp only [unsent, mem_image, mem_filter, mem_univ, true_and, EmbeddingLike.apply_eq_iff_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨s', ⟨hs', hf⟩, rfl, rfl⟩; exact ⟨(ENat.natCast_toNat hs').symm, hf⟩
  · rintro ⟨h, hf⟩; exact ⟨s, ⟨by simp [h], hf⟩, by simp [h], rfl⟩

lemma unsent_subset : st.unsent ⊆ st.entries := by
  intro x hx
  obtain ⟨⟨m, s⟩, rfl⟩ := toLex.surjective x
  exact mem_entries.2 (mem_unsent.1 hx).1

end State

/-- The message of a node in state `st`: the `β` smallest unsent entries (Lines 7–10;
`β = 1` in Algorithm 1). -/
noncomputable def msg (β : ℕ) (st : State V) : Finset (ℕ ×ₗ V) := topk β st.unsent

/-- The received pairs that concern source `s`. -/
noncomputable def recvSet (inbox : V → Finset (ℕ ×ₗ V)) (s : V) : Finset (ℕ ×ₗ V) :=
  (univ.biUnion inbox).filter fun x => (ofLex x).2 = s

/-- The smallest `h_s + 1` over all received pairs `(h_s, s)` (`⊤` if none). -/
noncomputable def recv (inbox : V → Finset (ℕ ×ₗ V)) (s : V) : ℕ∞ :=
  (recvSet inbox s).inf fun x => (((ofLex x).1 + 1 : ℕ) : ℕ∞)

/-- One round at a node in state `st` that received the pairs `inbox u` from each `u`
(Lines 7–16). The flag of `s` is reset iff the entry of `s` improved; otherwise it is set if the
entry of `s` was sent in this round. Entries with distance `> cap` are deleted (Line 16). -/
noncomputable def step (β : ℕ) (cap : ℕ∞) (st : State V) (inbox : V → Finset (ℕ ×ₗ V)) :
    State V where
  est s := if cap < min (st.est s) (recv inbox s) then ⊤ else min (st.est s) (recv inbox s)
  sent s := if recv inbox s < st.est s then false
    else st.sent s || decide (toLex ((st.est s).toNat, s) ∈ msg β st)

/-- Initial state (Lines 1–5): `L_v = {(0, v)}` if `v ∈ S`, else `L_v = ∅`. -/
def init (S : Finset V) (v : V) : State V where
  est s := if s = v ∧ v ∈ S then 0 else ⊤
  sent _ := false

variable (E : V → V → Prop) [DecidableRel E] (S : Finset V) (β : ℕ) (cap : ℕ∞)

/-- The state of every node after `t` rounds (`L_v^t` of Definition 4.2 is `(run … t v).entries`).
In round `t + 1` node `v` receives `msg β (run t u)` from every `u` with `E u v`. -/
noncomputable def run : ℕ → V → State V
  | 0, v => init S v
  | t + 1, v => step β cap (run t v) (fun u => if E u v then msg β (run t u) else ∅)

/-- The output (Lines 16–17): `top_σ` of the entries with distance `≤ h`. -/
noncomputable def output (h σ : ℕ) (st : State V) : Finset (ℕ ×ₗ V) :=
  topk σ (st.entries.filter fun x => (ofLex x).1 ≤ h)

/-- Algorithm 1 of the paper: one pair per message, Line 16 after the loop. -/
noncomputable abbrev alg1 : ℕ → V → State V := run E S 1 ⊤

end Podc.SourceDetectionCongest
