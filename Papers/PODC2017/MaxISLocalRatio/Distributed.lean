import Papers.PODC2017.MaxISLocalRatio.Coloring
import Cslib.Computability.Distributed.Local.Identifiers

/-!
# Algorithm 3 as a synchronous distributed algorithm (Section 2.3)

We implement Algorithm 3 in CSLib's synchronous locally-iterative model
(`Cslib.LocallyIterative.Algorithm`): in every round a node replaces its state by a function of the
round number, its own state and the set of its neighbours' states (= the messages it receives).
The `(Δ+1)`-colouring of line 1 is a black box: the colour is part of the local input (any proper
colouring `c` with `c v < k`).

A node state holds the identifier, the colour, a weight, the iteration at which the node became a
*candidate* (it was a local colour maximum and sent `reduce(w(v))`), and the candidate's decision.
A non-candidate with weight `≤ 0` is *removed* (`NotInIS`).

* round `2i` ("select", line 18): a remaining node whose colour exceeds the colours of all its
  remaining neighbours becomes a candidate of level `i` and keeps its current weight as the amount
  it reduces (lines 19–21);
* round `2i+1` ("reduce", lines 4–9): every non-candidate subtracts the amounts of its neighbours
  that became candidates of level `i`;
* every round ("addition stage", lines 12–17): an undecided candidate of level `j` decides
  `NotInIS` if a neighbour that became a candidate later decided `InIS`, and `InIS` if all its
  neighbours are removed, earlier candidates, or later candidates that decided `NotInIS`.

Main result (`algorithm_3`): after `3k` rounds every node has decided, the nodes that output `InIS`
form exactly the set returned by Algorithm 1 with the colouring rule — hence (`colorRule_isApprox`)
a `Δ`-approximate maximum-weight independent set — and every output is final and correct when it is
first produced. With the black-box `(Δ+1)`-colouring (`k = Δ+1`) this is `3Δ + 3` rounds after the
colouring, i.e. `O(Δ + log* n)` rounds with the colouring of [BEK14, Bar15].
-/

set_option linter.unusedSectionVars false

namespace Podc.MaxISLocalRatio

open Finset Cslib.LocallyIterative

/-- Local state of a node in Algorithm 3. -/
structure NState (V : Type*) where
  /-- identifier -/
  id : V
  /-- colour (output of the black-box colouring) -/
  col : ℕ
  /-- current weight; for a candidate, the amount it reduced from its neighbours -/
  w : ℝ
  /-- `some j` once the node became a candidate at iteration `j` -/
  cand : Option ℕ
  /-- decision of a candidate: `some true` = `InIS`, `some false` = `NotInIS` -/
  dec : Option Bool

variable {V : Type*}

open scoped Classical in
/-- One round of Algorithm 3 (see the module docstring). -/
noncomputable def alg3Step (t : ℕ) (s : NState V) (N : Set (NState V)) : NState V :=
  match s.cand with
  | some j =>
    if s.dec = none then
      if ∃ x ∈ N, (∃ j', x.cand = some j' ∧ j < j') ∧ x.dec = some true then
        { s with dec := some false }
      else if ∀ x ∈ N, (x.cand = none → x.w ≤ 0) ∧
          (∀ j', x.cand = some j' → j < j' → x.dec = some false) then
        { s with dec := some true }
      else s
    else s
  | none =>
    if t % 2 = 0 then
      if 0 < s.w ∧ ∀ x ∈ N, x.cand = none → 0 < x.w → x.col < s.col then
        { s with cand := some (t / 2) }
      else s
    else
      { s with w := s.w - ∑ᶠ x ∈ N, if x.cand = some (t / 2) then x.w else 0 }

/-- Algorithm 3 in the locally-iterative model. -/
noncomputable def alg3 : Algorithm (NState V) := ⟨alg3Step⟩

/-- Initial configuration: identifier, colour (black box) and weight. -/
def init3 (c : V → ℕ) (w : V → ℝ) (v : V) : NState V := ⟨v, c v, w v, none, none⟩

open scoped Classical in
/-- The output of a node: a candidate outputs its decision, a removed node `NotInIS`, a remaining
node nothing yet. -/
noncomputable def output (s : NState V) : Option Bool :=
  match s.cand with
  | some _ => s.dec
  | none => if s.w ≤ 0 then some false else none

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {c : V → ℕ}

section Invariant

variable (G) (hc : IsProper G c) (w : V → ℝ)

/-- The invariant of the run at round `t`, relative to the centralized iteration
`Wᵢ = (colorRule G c hc).iter w i`, `Uᵢ = (colorRule G c hc).U w i` and the output
`S = seqLR (colorRule G c hc) w` of Algorithm 1. -/
def Inv (t : ℕ) (cfg : V → NState V) : Prop :=
  ∀ v, (cfg v).id = v ∧ (cfg v).col = c v ∧
    (match (cfg v).cand with
      | none => (cfg v).w = (colorRule G c hc).iter w (t / 2) v ∧
          ∀ j, v ∈ (colorRule G c hc).U w j → (t + 1) / 2 ≤ j
      | some j => v ∈ (colorRule G c hc).U w j ∧ j < (t + 1) / 2 ∧
          (cfg v).w = (colorRule G c hc).iter w j v) ∧
    (∀ b, (cfg v).dec = some b → (cfg v).cand ≠ none ∧ (b = true ↔ v ∈ seqLR (colorRule G c hc) w))

end Invariant

variable {hc : IsProper G c} {w : V → ℝ}

theorem inv_zero : Inv G hc w 0 (init3 c w) := by
  intro v
  simp [init3]

/-- Neighbours' weights in the run: a candidate of level `j < i` has no weight left in `Wᵢ`. -/
theorem inv_pos_iff {t : ℕ} {cfg : V → NState V} (h : Inv G hc w t cfg) (i : ℕ) (hi : i = t / 2)
    (ht : t % 2 = 0) (u : V) :
    ((cfg u).cand = none ∧ 0 < (cfg u).w) ↔ 0 < (colorRule G c hc).iter w i u := by
  obtain ⟨-, -, hm, -⟩ := h u
  subst hi
  cases hcu : (cfg u).cand with
  | none =>
    rw [hcu] at hm
    simp [hm.1]
  | some j =>
    rw [hcu] at hm
    simp only [reduceCtorEq, false_and, false_iff, not_lt]
    obtain ⟨hU, hj, -⟩ := hm
    have h1 := (colorRule G c hc).iter_succ_of_mem_U w hU
    have h2 := (colorRule G c hc).iter_anti w (show j + 1 ≤ t / 2 by omega) u
    linarith

/-- A vertex of `Uⱼ` is a candidate of level `j` from round `2j+1` on. -/
theorem inv_cand_of_mem_U {t : ℕ} {cfg : V → NState V} (h : Inv G hc w t cfg) {j : ℕ} {v : V}
    (hv : v ∈ (colorRule G c hc).U w j) (ht : 2 * j + 1 ≤ t) : (cfg v).cand = some j := by
  obtain ⟨-, -, hm, -⟩ := h v
  cases hcv : (cfg v).cand with
  | none =>
    rw [hcv] at hm
    have := hm.2 j hv
    omega
  | some j' =>
    rw [hcv] at hm
    rw [(colorRule G c hc).U_inj w hm.1 hv]

/-- Soundness of a `NotInIS` decision (line 15–17): a later candidate neighbour is in the output. -/
theorem dec_false_sound {t : ℕ} {cfg : V → NState V} (h : Inv G hc w t cfg) {v : V} {j : ℕ}
    (hv : (cfg v).cand = some j)
    (hex : ∃ x ∈ nbrColors G cfg v, (∃ j', x.cand = some j' ∧ j < j') ∧ x.dec = some true) :
    v ∉ seqLR (colorRule G c hc) w := by
  obtain ⟨u, hadj, ⟨j', hj', hjj'⟩, hdec⟩ := exists_mem_nbrColors.1 hex
  have hvU : v ∈ (colorRule G c hc).U w j := by
    have := (h v).2.2.1; rw [hv] at this; exact this.1
  have huU : u ∈ (colorRule G c hc).U w j' := by
    have := (h u).2.2.1; rw [hj'] at this; exact this.1
  have huS := ((h u).2.2.2 true hdec).2.1 rfl
  rw [mem_seqLR_iff _ w hvU]
  intro hall
  exact hall u huS ⟨j', hjj', huU⟩ hadj

/-- Soundness of an `InIS` decision (lines 12–14): no later candidate neighbour is in the
output. -/
theorem dec_true_sound {t : ℕ} {cfg : V → NState V} (h : Inv G hc w t cfg) {v : V} {j : ℕ}
    (hv : (cfg v).cand = some j)
    (hall : ∀ x ∈ nbrColors G cfg v, (x.cand = none → x.w ≤ 0) ∧
      (∀ j', x.cand = some j' → j < j' → x.dec = some false)) :
    v ∈ seqLR (colorRule G c hc) w := by
  have hvU : v ∈ (colorRule G c hc).U w j := by
    have := (h v).2.2.1; rw [hv] at this; exact this.1
  rw [mem_seqLR_iff _ w hvU]
  rintro u huS ⟨j'', hjj'', huU⟩ hadj
  obtain ⟨h1, h2⟩ := forall_mem_nbrColors.1 hall u hadj
  have hm := (h u).2.2.1
  cases hcu : (cfg u).cand with
  | none =>
    rw [hcu] at hm
    have hle := h1 hcu
    have hpos := mem_pos.1 ((colorRule G c hc).U_subset_pos w j'' huU)
    have := (colorRule G c hc).iter_anti w (show t / 2 ≤ j'' by have := hm.2 j'' huU; omega) u
    linarith [hm.1]
  | some j' =>
    rw [hcu] at hm
    have := (colorRule G c hc).U_inj w hm.1 huU
    subst this
    have hdec := h2 j' hcu hjj''
    have := ((h u).2.2.2 false hdec).2
    simp only [Bool.false_eq_true, false_iff] at this
    exact this huS

/-- The reduction amount received in round `2i+1`: the sum over neighbours picked at level `i`. -/
theorem finsum_reduce {t : ℕ} {cfg : V → NState V} (h : Inv G hc w t cfg) (ht : t % 2 = 1)
    {v : V} (hv : (cfg v).cand = none) :
    (∑ᶠ x ∈ nbrColors G cfg v, if x.cand = some (t / 2) then x.w else 0) =
      red G ((colorRule G c hc).U w (t / 2)) ((colorRule G c hc).iter w (t / 2)) v := by
  classical
  have hid : ∀ u, (cfg u).id = u := fun u => (h u).1
  rw [finsum_nbrColors (c := cfg) NState.id hid]
  have hvU : v ∉ (colorRule G c hc).U w (t / 2) := by
    intro hU
    have := (h v).2.2.1; rw [hv] at this
    have := this.2 _ hU; omega
  have hcand : ∀ u, (cfg u).cand = some (t / 2) ↔ u ∈ (colorRule G c hc).U w (t / 2) := by
    intro u
    have hm := (h u).2.2.1
    cases hcu : (cfg u).cand with
    | none =>
      rw [hcu] at hm
      simp only [reduceCtorEq, false_iff]
      intro hU; have := hm.2 _ hU; omega
    | some j =>
      rw [hcu] at hm
      simp only [Option.some.injEq]
      exact ⟨fun e => e ▸ hm.1, fun hU => (colorRule G c hc).U_inj w hm.1 hU⟩
  rw [← sum_filter]
  unfold red
  refine sum_congr ?_ fun u hu => ?_
  · ext u
    simp only [mem_filter, SimpleGraph.mem_neighborFinset, mem_cl, hcand]
    constructor
    · rintro ⟨hadj, hU⟩; exact ⟨hU, Or.inr hadj.symm⟩
    · rintro ⟨hU, rfl | hadj⟩
      · exact absurd hU hvU
      · exact ⟨hadj.symm, hU⟩
  · have hcu := (hcand u).2 (mem_filter.1 hu).1
    have hm := (h u).2.2.1
    rw [hcu] at hm
    exact hm.2.2

/-- The invariant is preserved by every round. -/
theorem inv_succ {t : ℕ} {cfg : V → NState V} (h : Inv G hc w t cfg) :
    Inv G hc w (t + 1) (fun v => alg3Step t (cfg v) (nbrColors G cfg v)) := by
  intro v
  obtain ⟨hid, hcol, hm, hdec⟩ := h v
  cases hcv : (cfg v).cand with
  | some j =>
    rw [hcv] at hm
    obtain ⟨hU, hj, hw⟩ := hm
    simp only [alg3Step, hcv]
    split_ifs with h1 h2 h3
    · refine ⟨hid, hcol, ?_, ?_⟩
      · exact ⟨hU, by omega, hw⟩
      · intro b hb
        simp only [Option.some.injEq] at hb
        subst hb
        refine ⟨by simp, ?_⟩
        simpa using dec_false_sound h hcv h2
    · refine ⟨hid, hcol, ?_, ?_⟩
      · exact ⟨hU, by omega, hw⟩
      · intro b hb
        simp only [Option.some.injEq] at hb
        subst hb
        refine ⟨by simp, ?_⟩
        simpa using dec_true_sound h hcv h3
    · refine ⟨hid, hcol, ?_, hdec⟩
      rw [hcv]; exact ⟨hU, by omega, hw⟩
    · refine ⟨hid, hcol, ?_, hdec⟩
      rw [hcv]; exact ⟨hU, by omega, hw⟩
  | none =>
    rw [hcv] at hm
    obtain ⟨hw, hlev⟩ := hm
    have hdec' : (cfg v).dec = none := by
      cases hd : (cfg v).dec with
      | none => rfl
      | some b => exact absurd hcv ((hdec b hd).1)
    simp only [alg3Step, hcv]
    split_ifs with h1 h2
    · -- select round, `v` becomes a candidate of level `t / 2`
      have hmem : v ∈ (colorRule G c hc).U w (t / 2) := by
        refine mem_localMax.2 ⟨hw ▸ h2.1, fun u hu hadj => ?_⟩
        have := forall_mem_nbrColors.1 h2.2 u hadj
        rw [← (inv_pos_iff h (t / 2) rfl h1 u)] at hu
        have := this hu.1 hu.2
        rwa [(h u).2.1, hcol] at this
      refine ⟨hid, hcol, ⟨hmem, by omega, hw⟩, ?_⟩
      intro b hb; simp [hdec'] at hb
    · -- select round, `v` stays
      have hnot : v ∉ (colorRule G c hc).U w (t / 2) := by
        intro hmem
        obtain ⟨hpos, hmax⟩ := mem_localMax.1 hmem
        refine h2 ⟨hw ▸ hpos, forall_mem_nbrColors.2 fun u hadj hcu hwu => ?_⟩
        have hu := (inv_pos_iff h (t / 2) rfl h1 u).1 ⟨hcu, hwu⟩
        rw [(h u).2.1, hcol]
        exact hmax u hu hadj
      refine ⟨hid, hcol, ?_, ?_⟩
      · simp only [hcv]
        refine ⟨by rw [hw, show (t + 1) / 2 = t / 2 by omega], fun j hj => ?_⟩
        have := hlev j hj
        rcases Nat.lt_or_ge (t / 2) j with hlt | hge
        · omega
        · exact absurd (show j = t / 2 by omega ▸ hj) hnot
      · intro b hb; simp [hdec'] at hb
    · -- reduce round
      have ht : (t + 1) / 2 = t / 2 + 1 := by omega
      refine ⟨hid, hcol, ⟨?_, fun j hj => ?_⟩, ?_⟩
      · simp only
        rw [finsum_reduce h (by omega) hcv, hw, ht, Rule.iter_succ]
        simp [Rule.next, Rule.U]
      · have := hlev j hj; omega
      · intro b hb; simp [hdec'] at hb

variable (G c w) in
/-- The configuration of Algorithm 3 after `t` rounds. -/
noncomputable def cfg3 (t : ℕ) : V → NState V := (alg3 : Algorithm (NState V)).run G (init3 c w) t

theorem cfg3_succ (t : ℕ) (v : V) :
    cfg3 G c w (t + 1) v = alg3Step t (cfg3 G c w t v) (nbrColors G (cfg3 G c w t) v) := rfl

/-- The invariant holds in every round of the run. -/
theorem inv_cfg3 (t : ℕ) : Inv G hc w t (cfg3 G c w t) := by
  induction t with
  | zero => exact inv_zero
  | succ t ih => exact inv_succ ih

theorem alg3Step_cand {t : ℕ} {s : NState V} {N : Set (NState V)} {j : ℕ} (h : s.cand = some j) :
    (alg3Step t s N).cand = some j := by
  simp only [alg3Step, h]
  split_ifs <;> simp [h]

theorem alg3Step_dec {t : ℕ} {s : NState V} {N : Set (NState V)} {b : Bool} (h : s.dec = some b) :
    (alg3Step t s N).dec = some b := by
  unfold alg3Step
  cases hs : s.cand with
  | some j => simp [h]
  | none => simp only; split_ifs <;> simp [h]

theorem cfg3_cand_mono {t t' : ℕ} (htt' : t ≤ t') {v : V} {j : ℕ}
    (h : (cfg3 G c w t v).cand = some j) : (cfg3 G c w t' v).cand = some j := by
  induction htt' with
  | refl => exact h
  | step _ ih => rw [cfg3_succ]; exact alg3Step_cand ih

theorem cfg3_dec_mono {t t' : ℕ} (htt' : t ≤ t') {v : V} {b : Bool}
    (h : (cfg3 G c w t v).dec = some b) : (cfg3 G c w t' v).dec = some b := by
  induction htt' with
  | refl => exact h
  | step _ ih => rw [cfg3_succ]; exact alg3Step_dec ih

/-- After the removal stage (`2k` rounds) every non-candidate is removed. -/
theorem cfg3_removed (hc : IsProper G c) {k : ℕ} (hk : ∀ v, c v < k) {t : ℕ} (ht : 2 * k ≤ t) {v : V}
    (hv : (cfg3 G c w t v).cand = none) : (cfg3 G c w t v).w ≤ 0 := by
  have hm := (inv_cfg3 (hc := hc) (w := w) t v).2.2.1
  rw [hv] at hm
  rw [hm.1]
  by_contra hpos
  have h0 := colorRule_removal hc hk w
  have := (colorRule G c hc).iter_anti w (show k ≤ t / 2 by omega) v
  have hmem : v ∈ pos ((colorRule G c hc).iter w k) := mem_pos.2 (by linarith)
  rw [h0] at hmem
  simp at hmem

/-- **Addition stage**: a candidate of level `j < k` has decided by round `2k + (k - j)`. -/
theorem cfg3_decided {k : ℕ} (hk : ∀ v, c v < k) (m : ℕ) :
    ∀ j v, k ≤ j + m → v ∈ (colorRule G c hc).U w j →
      ∃ b, (cfg3 G c w (2 * k + m) v).dec = some b := by
  induction m with
  | zero =>
    intro j v hjm hv
    have := colorRule_level_lt hc hk w hv
    omega
  | succ m ih =>
    intro j v hjm hv
    have hjk := colorRule_level_lt hc hk w hv
    have h := inv_cfg3 (hc := hc) (w := w) (2 * k + m)
    have hcv : (cfg3 G c w (2 * k + m) v).cand = some j := inv_cand_of_mem_U h hv (by omega)
    rw [← add_assoc, cfg3_succ]
    cases hd : (cfg3 G c w (2 * k + m) v).dec with
    | some b => exact ⟨b, alg3Step_dec hd⟩
    | none =>
      simp only [alg3Step, hcv, hd, ite_true]
      split_ifs with h1 h2
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
      · exfalso
        refine h2 (forall_mem_nbrColors.2 fun u hadj => ⟨fun hcu => ?_, fun j' hcu hjj' => ?_⟩)
        · exact cfg3_removed hc hk (by omega) hcu
        · have huU : u ∈ (colorRule G c hc).U w j' := by
            have := (h u).2.2.1; rw [hcu] at this; exact this.1
          obtain ⟨b, hb⟩ := ih j' u (by omega) huU
          cases b with
          | false => exact hb
          | true =>
            exact absurd (exists_mem_nbrColors.2 ⟨u, hadj, ⟨j', hcu, hjj'⟩, hb⟩) h1

/-- Outputs are always correct: a node that outputs `InIS`/`NotInIS` in some round is
in/not in the output of Algorithm 1 (with the colouring rule). -/
theorem output_sound (hc : IsProper G c) (w : V → ℝ) {t : ℕ} {v : V} {b : Bool}
    (h : output (cfg3 G c w t v) = some b) :
    (b = true ↔ v ∈ seqLR (colorRule G c hc) w) := by
  have hI := inv_cfg3 (hc := hc) (w := w) t v
  cases hcv : (cfg3 G c w t v).cand with
  | some j =>
    simp only [output, hcv] at h
    exact (hI.2.2.2 b h).2
  | none =>
    simp only [output, hcv] at h
    split_ifs at h with hw
    cases h
    simp only [Bool.false_eq_true, false_iff]
    intro hS
    obtain ⟨j, hj⟩ := seqLR_subset_U _ w hS
    have hm := hI.2.2.1
    rw [hcv] at hm
    have hpos := mem_pos.1 ((colorRule G c hc).U_subset_pos w j hj)
    have := (colorRule G c hc).iter_anti w (show t / 2 ≤ j by have := hm.2 j hj; omega) v
    linarith [hm.1]

/-- Termination: from round `3k` on, every node has an output, and it is membership in the output
of Algorithm 1 with the colouring rule. -/
theorem output_eq (hc : IsProper G c) {k : ℕ} (hk : ∀ v, c v < k) (w : V → ℝ) {t : ℕ}
    (ht : 3 * k ≤ t) (v : V) :
    output (cfg3 G c w t v) = some (decide (v ∈ seqLR (colorRule G c hc) w)) := by
  have hI := inv_cfg3 (hc := hc) (w := w) t
  suffices hb : ∃ b, output (cfg3 G c w t v) = some b by
    obtain ⟨b, hb⟩ := hb
    rw [hb, Option.some.injEq]
    have := output_sound hc w hb
    cases b <;> simp_all
  by_cases hU : ∃ j, v ∈ (colorRule G c hc).U w j
  · obtain ⟨j, hj⟩ := hU
    have hjk := colorRule_level_lt hc hk w hj
    have hcv := inv_cand_of_mem_U hI hj (by omega)
    obtain ⟨b, hb⟩ := cfg3_decided (hc := hc) (w := w) hk k j v (by omega) hj
    refine ⟨b, ?_⟩
    simp only [output, hcv]
    exact cfg3_dec_mono (by omega) hb
  · have hcv : (cfg3 G c w t v).cand = none := by
      cases h : (cfg3 G c w t v).cand with
      | none => rfl
      | some j =>
        have := (hI v).2.2.1; rw [h] at this
        exact absurd ⟨j, this.1⟩ hU
    refine ⟨false, ?_⟩
    simp only [output, hcv, cfg3_removed hc hk (by omega) hcv, ite_true]

/-- **Algorithm 3 (Section 2.3).** Run on a graph with maximum degree `≤ Δ` (`Δ ≥ 1`), weights
`w`, and a black-box proper colouring `c` with `k` colours, the synchronous algorithm `alg3`
terminates after `3k` rounds, every output is final and correct when produced, and the set of
nodes that output `InIS` is a `Δ`-approximate maximum-weight independent set. With a
`(Δ+1)`-colouring this is `3Δ + 3` rounds after the colouring. -/
theorem algorithm_3 (hc : IsProper G c) {k : ℕ} (hk : ∀ v, c v < k) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (h1 : 1 ≤ Δ) (w : V → ℝ) :
    ∃ S : Finset V, IsApprox G Δ w S ∧
      (∀ t, 3 * k ≤ t → ∀ v, output (cfg3 G c w t v) = some (decide (v ∈ S))) ∧
      (∀ t v b, output (cfg3 G c w t v) = some b → (b = true ↔ v ∈ S)) :=
  ⟨seqLR (colorRule G c hc) w, colorRule_isApprox hc hΔ h1 w,
    fun _ ht v => output_eq hc hk w ht v, fun _ _ _ h => output_sound hc w h⟩

end Podc.MaxISLocalRatio
