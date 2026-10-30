import Papers.PODC2024.SleepyTOB.Tally

/-!
# The extended graded agreement (Figure 3) and Lemma 1

D'Amato, Losa, Zanolini, PODC 2024, Section 3.2.

One instance of the extended graded agreement runs in a round `r`:

* `H = H_r`, `B = B_r`: honest and Byzantine processes awake at round `r` (`O_r = H ∪ B`);
  `Hnext = H_{r+1}`: the honest processes awake at the end of round `r` (the receivers).
  Since the adversary is growing (`B_r ⊆ B_{r+1}`), `Hnext` is disjoint from `B`.
* Every receiver `p` starts with an initial vote assignment `M0 p` (at most one message per
  process, equivocations already discarded), all from senders in `P0`.
* In the send phase each honest `q ∈ H` multicasts its input `input q`; `R p q` is the set of
  round-`r` vote messages that `p` received from `q`. Honest senders send only their input;
  processes not awake at round `r` send nothing; Byzantine senders send anything.
* `M p` (the paper's `M_r^p`): the round-`r` vote of `q` if `p` received exactly one, nothing if
  `q` equivocated in round `r`, and the initial vote `M0 p q` if `p` received no round-`r` vote
  from `q`.
* In a synchronous round every receiver gets every honest round-`r` vote (`Sync`).

Lemma 1 holds under the assumption `|H_r| > 2|O_r ∪ P0|/3` (`Quorum`): the five graded-agreement
properties of Definition 4 in synchronous rounds (`lemma_1`), and clique validity in every round
(`lemma_1_clique_validity`, generalised in `clique_validity`).
-/

namespace Podc.SleepyTOB

open Finset

noncomputable section
open Classical

variable {P α : Type*} [Fintype P]

/-- One instance of the extended graded agreement of Figure 3 (round `r`). -/
structure ExtGA (P α : Type*) [Fintype P] where
  /-- `H_r`: honest processes awake at round `r` (the senders). -/
  H : Finset P
  /-- `B_r`: Byzantine processes (awake) at round `r`. -/
  B : Finset P
  /-- `H_{r+1}`: honest processes awake at the end of round `r` (the receivers). -/
  Hnext : Finset P
  /-- `P0`: senders of the initial vote messages. -/
  P0 : Finset P
  /-- The input log of each honest sender. -/
  input : P → List α
  /-- `M0 p`: initial vote set of receiver `p`, at most one vote per process. -/
  M0 : P → Votes P α
  /-- `R p q`: round-`r` vote messages received by `p` from `q`. -/
  R : P → P → Set (List α)
  disjoint_H_B : Disjoint H B
  /-- Growing adversary: a process honest at round `r + 1` is not Byzantine at round `r`. -/
  disjoint_Hnext_B : Disjoint Hnext B
  M0_mem : ∀ p q, M0 p q ≠ none → q ∈ P0
  R_asleep : ∀ p q, q ∉ H ∪ B → R p q = ∅
  R_honest : ∀ p q, q ∈ H → R p q ⊆ {input q}

namespace ExtGA

variable (G : ExtGA P α)

/-- `O_r = H_r ∪ B_r`. -/
def O : Finset P := G.H ∪ G.B

/-- The final vote set `M_r^p` of receiver `p` (Figure 3). -/
def M (p : P) : Votes P α := fun q =>
  if G.R p q = ∅ then G.M0 p q
  else if hq : ∃ l, G.R p q = {l} then some hq.choose else none

/-- The round is synchronous: every receiver gets every honest round-`r` vote. -/
def Sync : Prop := ∀ p ∈ G.Hnext, ∀ q ∈ G.H, G.R p q = {G.input q}

/-- The assumption of Section 3.2: `|H_r| > 2/3 |O_r ∪ P0|`. -/
def Quorum : Prop := 2 * #(G.O ∪ G.P0) < 3 * #G.H

variable {G}

theorem M_of_R_empty {p q : P} (h : G.R p q = ∅) : G.M p q = G.M0 p q := by
  simp [M, h]

theorem M_of_R_singleton {p q : P} {l : List α} (h : G.R p q = {l}) : G.M p q = some l := by
  have hne : ¬ G.R p q = ∅ := by rw [h]; exact Set.singleton_ne_empty l
  have hex : ∃ l', G.R p q = {l'} := ⟨l, h⟩
  have hl : l = hex.choose := Set.singleton_eq_singleton_iff.1 (h.symm.trans hex.choose_spec)
  simp only [M, hne, hex, ↓reduceIte, ↓reduceDIte]
  exact congrArg some hl.symm

theorem voters_M_subset (p : P) : voters (G.M p) ⊆ G.O ∪ G.P0 := by
  intro q hq
  have hq' : G.M p q ≠ none := (mem_filter.1 hq).2
  rw [mem_union]
  by_cases hR : G.R p q = ∅
  · rw [M_of_R_empty hR] at hq'
    exact Or.inr (G.M0_mem p q hq')
  · left
    by_contra hO
    exact hR (G.R_asleep p q hO)

/-- In a synchronous round the final vote set of a receiver is a faithful tally. -/
theorem faithful (hs : G.Sync) {p : P} (hp : p ∈ G.Hnext) :
    Faithful (G.M p) (G.O ∪ G.P0) G.H G.input :=
  ⟨voters_M_subset p, fun q hq => M_of_R_singleton (hs p hp q hq)⟩

/-- An honest process not in `H_r` is not awake at round `r`, so the receiver uses its initial
vote; an honest process in `H_r` contributes its round-`r` vote or (if that vote was not
received) its initial vote. -/
theorem M_honest {p q : P} (hqB : q ∉ G.B) :
    G.M p q = G.M0 p q ∨ (q ∈ G.H ∧ G.M p q = some (G.input q)) := by
  by_cases hR : G.R p q = ∅
  · exact Or.inl (M_of_R_empty hR)
  · right
    have hqH : q ∈ G.H := by
      by_contra hqH
      exact hR (G.R_asleep p q (by simp [hqH, hqB]))
    refine ⟨hqH, M_of_R_singleton ?_⟩
    have hsub := G.R_honest p q hqH
    obtain ⟨l, hl⟩ := Set.nonempty_iff_ne_empty.2 hR
    have := hsub hl
    rw [Set.mem_singleton_iff] at this
    subst this
    exact Set.Subset.antisymm hsub (Set.singleton_subset_iff.2 hl)

end ExtGA

/-- The properties of graded agreement (Definition 4), for honest senders `H` with inputs
`input`, honest receivers `Hnext` and tallies `T p` of the receivers.

* Integrity is stated as in [MMR] and in the proof of Lemma 1: an output log is *extended by* some
  honest input (Definition 4 literally says "inputs the log", see `integrity_literal_false`).
* Validity is stated for every common prefix of the honest inputs, in particular for the longest
  one (grade-1 outputs are prefix closed, `Grade1.of_prefix`). -/
structure IsGradedAgreement (H Hnext : Finset P) (input : P → List α) (T : P → Votes P α) :
    Prop where
  graded_consistency : ∀ p ∈ Hnext, ∀ p' ∈ Hnext, ∀ Λ, Grade1 (T p) Λ → Outputs (T p') Λ
  integrity : ∀ p ∈ Hnext, ∀ Λ, Outputs (T p) Λ → ∃ q ∈ H, Λ <+: input q
  validity : ∀ Λ, (∀ q ∈ H, Λ <+: input q) → ∀ p ∈ Hnext, Grade1 (T p) Λ
  uniqueness : ∀ p ∈ Hnext, ∀ p' ∈ Hnext, ∀ Λ Λ', Grade1 (T p) Λ → Grade1 (T p') Λ' →
    Compatible Λ Λ'
  bounded_divergence : ∀ p ∈ Hnext, ∀ S : Finset (List α), (S : Set (List α)).Pairwise Conflict →
    (∀ Λ ∈ S, Outputs (T p) Λ) → #S ≤ 2

/-- **Lemma 1** (first part). In a synchronous round, if `|H_r| > 2/3 |O_r ∪ P0|`, the extended
graded agreement of Figure 3 satisfies graded consistency, integrity, validity, uniqueness and
bounded divergence. -/
theorem lemma_1 (G : ExtGA P α) (hq : G.Quorum) (hs : G.Sync) :
    IsGradedAgreement G.H G.Hnext G.input G.M where
  graded_consistency _ hp _ hp' _ hg :=
    (G.faithful hs hp).consistency (G.faithful hs hp') hq hg
  integrity _ hp _ ho := (G.faithful hs hp).integrity hq ho
  validity _ hall _ hp := (G.faithful hs hp).grade1_of_forall hq hall
  uniqueness _ hp _ hp' _ _ hg hg' :=
    (G.faithful hs hp).uniqueness (G.faithful hs hp') hq hg hg'
  bounded_divergence _ _ S hS hout := card_le_two_of_pairwise_conflict S hS hout

/-- **Clique validity**, general form (holds in synchronous and asynchronous rounds). Let `H'` be a
set of processes that are not Byzantine at round `r`, such that the members of `H'` awake at
round `r` input extensions of `Λ`, and let `p` be a receiver whose initial vote set contains a vote
for an extension of `Λ` from every member of `H'`. If `|H'| > 2/3 |O_r ∪ P0|`, then `p` outputs
`Λ` with grade 1.

Compared with Lemma 1, `H'` need not be contained in `H_r ∪ H_{r+1}` (only disjoint from `B_r`),
and the receiver need not be in `H'`: both generalisations are needed where the paper applies
clique validity (proofs of Lemma 2 and Theorem 2). -/
theorem clique_validity (G : ExtGA P α) {Λ : List α} {H' : Finset P} (hH' : Disjoint H' G.B)
    (hin : ∀ q ∈ H', q ∈ G.H → Λ <+: G.input q) {p : P}
    (hM0 : ∀ q ∈ H', ∃ l, G.M0 p q = some l ∧ Λ <+: l)
    (hc : 2 * #(G.O ∪ G.P0) < 3 * #H') : Grade1 (G.M p) Λ := by
  refine grade1_of_subset_votesFor (ExtGA.voters_M_subset p) ?_ hc
  intro q hq
  simp only [votesFor, mem_filter, mem_univ, true_and]
  have hqB : q ∉ G.B := Finset.disjoint_left.1 hH' hq
  rcases ExtGA.M_honest (p := p) hqB with h | ⟨hqH, h⟩
  · rw [h]; exact hM0 q hq
  · exact ⟨_, h, hin q hq hqH⟩

/-- **Lemma 1** (clique validity, as stated in the paper). Let `H' ⊆ H_r ∪ H_{r+1}` be such that
all members of `H' ∩ H_r` input an extension of `Λ` and, for every `p ∈ H' ∩ H_{r+1}`, `M0 p`
contains a vote for an extension of `Λ` from each process of `H'`. If `|H'| > 2/3 |O_r ∪ P0|`, all
processes of `H' ∩ H_{r+1}` output `Λ` with grade 1. Holds in synchronous and asynchronous
rounds. -/
theorem lemma_1_clique_validity (G : ExtGA P α) {Λ : List α} {H' : Finset P}
    (hsub : H' ⊆ G.H ∪ G.Hnext) (hin : ∀ q ∈ H' ∩ G.H, Λ <+: G.input q)
    (hM0 : ∀ p ∈ H' ∩ G.Hnext, ∀ q ∈ H', ∃ l, G.M0 p q = some l ∧ Λ <+: l)
    (hc : 2 * #(G.O ∪ G.P0) < 3 * #H') : ∀ p ∈ H' ∩ G.Hnext, Grade1 (G.M p) Λ := by
  intro p hp
  refine clique_validity G ?_ (fun q hq hqH => hin q (mem_inter.2 ⟨hq, hqH⟩)) (hM0 p hp) hc
  rw [Finset.disjoint_left]
  intro q hq hqB
  rcases mem_union.1 (hsub hq) with h | h
  · exact Finset.disjoint_left.1 G.disjoint_H_B h hqB
  · exact Finset.disjoint_left.1 G.disjoint_Hnext_B h hqB

end

end Podc.SleepyTOB
