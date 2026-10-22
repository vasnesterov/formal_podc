import Papers.PODC2012.LineTreeScheduling.TreeNetworks

/-!
# Appendix A: the sequential `3`-approximation for tree networks

The sequential algorithm of Figure 8: in every iteration, among the instances whose dual constraint
is unsatisfied, raise the one appearing earliest in a fixed order (tree networks one after the
other; inside a tree, by decreasing depth of the capture node `µ(d)` in the tree rooted at an
arbitrary node, ties broken arbitrarily), with critical set `π(d)` = the wings of `µ(d)` on
`path(d)` (at most `2` edges). By Observation A.1 the interference property holds; at the end all
constraints are satisfied (`λ = 1`); Lemma 3.1 gives the ratio `Δ + 1 = 3`.

* `seq_alg` — the generic sequential algorithm on an abstract instance: if the order key satisfies
  the layering property, the output `S` satisfies `LP ≤ (Δ+1) p(S)`.
* `appendix_A` — tree networks: `p(Opt) ≤ 3 · p(S)`.
-/

set_option linter.unusedSectionVars false

namespace Podc.LineTreeScheduling

open Finset

noncomputable section

namespace Inst

variable {A D E : Type*} [DecidableEq A] [DecidableEq D] [DecidableEq E] [Fintype D]
variable (I : Inst A D E) (R : Rule D E) (key : D → ℕ) (pick : Finset D → D)

/-- The instances whose dual constraint is unsatisfied. -/
def unsatSet (y : Duals A E) : Finset D := univ.filter fun d => I.lhs R.h y d < I.profit d

/-- The singleton raised by the sequential algorithm (empty once all constraints are
satisfied). -/
def seqPick (y : Duals A E) : Finset D :=
  if (I.unsatSet R y).Nonempty then {pick (I.unsatSet R y)} else ∅

/-- The dual assignment of the sequential algorithm after `t` iterations. -/
def seqState : ℕ → Duals A E
  | 0 => 0
  | t + 1 => I.raise R (seqState t) (I.seqPick R pick (seqState t))

/-- The set raised at iteration `t`. -/
def seqI (t : ℕ) : Finset D := I.seqPick R pick (I.seqState R pick t)

lemma seqState_eq_run (t : ℕ) : I.seqState R pick t = I.run R (I.seqI R pick) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [seqState, run_succ, seqI, ih]

variable {I R key pick}

/-- `pick U` is an element of `U` appearing earliest in the order `key`. -/
def IsEarliest (key : D → ℕ) (pick : Finset D → D) : Prop :=
  ∀ U : Finset D, U.Nonempty → pick U ∈ U ∧ ∀ d ∈ U, key (pick U) ≤ key d

lemma mem_seqI {t : ℕ} {d : D} (hd : d ∈ I.seqI R pick t) :
    I.unsatSet R (I.seqState R pick t) ≠ ∅ ∧ d = pick (I.unsatSet R (I.seqState R pick t)) := by
  unfold seqI seqPick at hd
  split_ifs at hd with h
  · exact ⟨h.ne_empty, Finset.mem_singleton.1 hd⟩
  · simp at hd

lemma seq_validRun (hp : IsEarliest key pick) (T : ℕ) : I.ValidRun R (I.seqI R pick) T := by
  refine ⟨fun t _ d₁ h₁ d₂ h₂ hne => absurd ((mem_seqI h₁).2.trans (mem_seqI h₂).2.symm) hne,
    fun t _ d hd => ?_⟩
  obtain ⟨hne, rfl⟩ := mem_seqI hd
  have := (hp _ (Finset.nonempty_iff_ne_empty.2 hne)).1
  rw [← seqState_eq_run]
  exact (Finset.mem_filter.1 this).2

/-- **The sequential algorithm** (Appendix A, generic form). Let `key` be an order on the instances
such that overlapping instances `d₁, d₂` with `key d₁ ≤ key d₂` satisfy
`π(d₁) ∩ path(d₂) ≠ ∅`, and `|π(d)| ≤ Δ`. After `|D|` iterations all dual constraints are satisfied
(`λ = 1`), and the output `S` is independent with `LP(x) ≤ (Δ+1) p(S)`. -/
theorem seq_alg [Fintype A] [Fintype E] {crit : D → Finset E} (hcrit : ∀ d, crit d ⊆ I.path d)
    {Δ : ℕ} (hΔ : ∀ d, (crit d).card ≤ Δ)
    (hkey : ∀ d₁ d₂, I.Overlap d₁ d₂ → key d₁ ≤ key d₂ → (crit d₁ ∩ I.path d₂).Nonempty)
    (hp : IsEarliest key pick) {x : D → ℝ} (hx : I.IsLPFeasible (fun _ => 1) x) :
    let S := I.solU (I.seqI (unitRule crit) pick) (Fintype.card D)
    I.IsIndep S ∧ 1 / (Δ + 1) * I.lpValue x ≤ I.profitOf S := by
  intro S
  set R := unitRule crit
  set N := Fintype.card D
  have hR := I.unitRule_wf hcrit
  have hv := seq_validRun (I := I) (R := R) hp N
  -- interference: the picked keys are nondecreasing on unsatisfied instances
  have hint : I.Interference R (I.seqI R pick) N := by
    intro s t hst htN d₁ h₁ d₂ h₂ hov
    refine hkey d₁ d₂ hov ?_
    obtain ⟨hne₁, rfl⟩ := mem_seqI h₁
    have hu₂ := hv.unsat t htN d₂ h₂
    have hd₂ : d₂ ∈ I.unsatSet R (I.seqState R pick s) := by
      rw [unsatSet, Finset.mem_filter, seqState_eq_run]
      exact ⟨Finset.mem_univ _, lt_of_le_of_lt (lhs_mono hR hv hst.le htN.le d₂) hu₂⟩
    exact (hp _ (Finset.nonempty_iff_ne_empty.2 hne₁)).2 d₂ hd₂
  -- `λ = 1`: after `|D|` iterations every instance is satisfied
  have hsat : ∀ d, 1 * I.profit d ≤ I.lhs (fun _ => 1) (I.run R (I.seqI R pick) N) d := by
    intro d
    rw [one_mul]
    by_contra hc
    push Not at hc
    have hunsat : ∀ t < N, d ∈ I.unsatSet R (I.seqState R pick t) := by
      intro t ht
      rw [unsatSet, Finset.mem_filter, seqState_eq_run]
      exact ⟨Finset.mem_univ _, lt_of_le_of_lt (lhs_mono hR hv ht.le le_rfl d) hc⟩
    set f : ℕ → D := fun t => pick (I.unsatSet R (I.seqState R pick t))
    have hfI : ∀ t < N, f t ∈ I.seqI R pick t := by
      intro t ht
      show f t ∈ I.seqPick R pick _
      unfold seqPick
      split_ifs with h
      · exact Finset.mem_singleton_self _
      · exact absurd ⟨d, hunsat t ht⟩ h
    have hinj : Set.InjOn f (Finset.range N) := by
      intro s hs t ht hst
      simp only [Finset.coe_range, Set.mem_Iio] at hs ht
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact not_mem_of_mem_of_lt hR hv h ht (hfI s hs) (hst ▸ hfI t ht)
      · exact not_mem_of_mem_of_lt hR hv h hs (hfI t ht) (hst ▸ hfI s hs)
    have himg : (Finset.range N).image f = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [Finset.card_image_of_injOn hinj, Finset.card_range])
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 (himg ▸ Finset.mem_univ d)
    have ht' := Finset.mem_range.1 ht
    have h1 := profit_le_lhs_of_mem hR hv ht' (hfI t ht')
    have h2 := lhs_mono hR hv (Nat.succ_le_of_lt ht') le_rfl (f t)
    exact absurd (h1.trans h2) (not_le.2 hc)
  have := lemma_3_1 hcrit hv hint (fun t _ d _ => hΔ d) hsat hx
  exact this

end Inst

/-! ### Tree networks: Observation A.1 gives the layering property of the order -/

variable {V A Q : Type*} [Fintype V] [DecidableEq V] [DecidableEq A] [DecidableEq Q]

namespace TreeInput

variable (P : TreeInput V A Q) [Fintype Q]

/-- The depth of the capture node `µ(d)` of `(a, b)` in the tree `T` rooted at `g`. -/
def rfDepth {T : SimpleGraph V} (hT : T.IsTree) (g a b : V) : ℕ :=
  (rootFixingTree hT g).depth (rfCapture T g a b)

lemma rfDepth_le {T : SimpleGraph V} (hT : T.IsTree) (g a b : V) :
    rfDepth hT g a b ≤ Fintype.card V :=
  (Finset.card_le_univ _)

/-- The order of Appendix A: tree networks one after the other (in the order of an enumeration of
`Q`), inside a tree by decreasing depth of the capture node. -/
def seqKey (hT : ∀ q, (P.T q).IsTree) (g : Q → V) (d : P.Inst') : ℕ :=
  (Fintype.equivFin Q d.1.2 : ℕ) * (Fintype.card V + 1) +
    (Fintype.card V - rfDepth (hT d.1.2) (g d.1.2) (P.src d.1.1) (P.dst d.1.1))

/-- The critical sets of Appendix A: the wings of `µ(d)` on `path(d)`. -/
def seqCrit (g : Q → V) (d : P.Inst') : Finset (Q × Sym2 V) :=
  (rfCrit (P.T d.1.2) (g d.1.2) (P.src d.1.1) (P.dst d.1.1)).map
    ⟨fun e => (d.1.2, e), fun _ _ h => by simpa using h⟩

/-- Within one tree, overlapping instances `d₁, d₂` with `µ(d₂)` not deeper than `µ(d₁)` satisfy
the interference condition (Observation A.1). -/
lemma seqKey_prop (hT : ∀ q, (P.T q).IsTree) (g : Q → V) (d₁ d₂ : P.Inst')
    (hov : P.toInst.Overlap d₁ d₂) (hk : P.seqKey hT g d₁ ≤ P.seqKey hT g d₂) :
    (P.seqCrit g d₁ ∩ P.toInst.path d₂).Nonempty := by
  obtain ⟨hq, hne⟩ := (P.overlap_iff).1 hov
  obtain ⟨⟨a₂, q₂⟩, h₂⟩ := d₂
  simp only at hq; subst hq
  obtain ⟨⟨a₁, q⟩, h₁⟩ := d₁
  simp only at hne ⊢
  have hTq := hT q
  -- depths: `µ(d₂)` is not deeper than `µ(d₁)`
  have hdep : rfDepth hTq (g q) (P.src a₂) (P.dst a₂) ≤ rfDepth hTq (g q) (P.src a₁) (P.dst a₁) := by
    have h1 := rfDepth_le hTq (g q) (P.src a₁) (P.dst a₁)
    have h2 := rfDepth_le hTq (g q) (P.src a₂) (P.dst a₂)
    unfold seqKey at hk
    simp only at hk
    omega
  -- a common vertex of the two paths
  obtain ⟨e, he⟩ := id hne
  obtain ⟨p, hp⟩ : ∃ p, p ∈ e := ⟨e.out.1, Sym2.out_fst_mem e⟩
  rw [Finset.mem_inter, mem_pathEdges, mem_pathEdges] at he
  have hp₁ := btw_rfCapture hTq (g := g q) (he.1.2 p hp)
  have hp₂ := btw_rfCapture hTq (g := g q) (he.2.2 p hp)
  have hanc : TreeAA.Btw (P.T q) (g q) (rfCapture (P.T q) (g q) (P.src a₂) (P.dst a₂))
      (rfCapture (P.T q) (g q) (P.src a₁) (P.dst a₁)) := by
    rcases btw_or_btw_of_btw hTq hp₂ hp₁ with h | h
    · exact h
    · have hmem : rfCapture (P.T q) (g q) (P.src a₂) (P.dst a₂) ∈ (rootFixingTree hTq (g q)).sub
          (rfCapture (P.T q) (g q) (P.src a₁) (P.dst a₁)) := (mem_rootFixingTree_sub hTq).2 h
      have := (rootFixingTree hTq (g q)).eq_of_mem_sub_of_depth_le hmem hdep
      rw [this]; exact TreeAA.btw_right _ _
  obtain ⟨e', he'⟩ := observation_A_1 hTq hne hanc
  rw [Finset.mem_inter] at he'
  exact ⟨(q, e'), Finset.mem_inter.2 ⟨Finset.mem_map.2 ⟨e', he'.1, rfl⟩,
    (P.mem_path (d := ⟨(a₂, q), h₂⟩)).2 ⟨rfl, he'.2⟩⟩⟩

variable [Fintype A]

/-- **Appendix A** (sequential algorithm for unit-height tree networks). Root every tree network at
an arbitrary node `g q`, order the instances tree by tree and inside a tree by decreasing depth of the
capture node (`pick` breaks ties arbitrarily), take `π(d)` = the wings of `µ(d)` (`Δ = 2`). The
sequential algorithm of Figure 8 (`|D|` iterations) outputs an independent set `S` with
`p(Opt) ≤ 3 · p(S)` (even `LP ≤ 3 p(S)`). -/
theorem appendix_A (hT : ∀ q, (P.T q).IsTree) (g : Q → V) {pick : Finset P.Inst' → P.Inst'}
    (hp : Inst.IsEarliest (P.seqKey hT g) pick) :
    let S := P.toInst.solU (P.toInst.seqI (unitRule (P.seqCrit g)) pick) (Fintype.card P.Inst')
    P.toInst.IsIndep S ∧ ∀ O, P.toInst.IsIndep O → P.toInst.profitOf O ≤ 3 * P.toInst.profitOf S := by
  intro S
  have hcrit : ∀ d, P.seqCrit g d ⊆ P.toInst.path d := by
    intro d e he
    simp only [seqCrit, Finset.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    exact (P.mem_path).2 ⟨rfl, wings_subset _ _ _ (by exact he')⟩
  have hΔ : ∀ d, (P.seqCrit g d).card ≤ 2 := fun d => by
    rw [seqCrit, Finset.card_map]; exact card_rfCrit_le (hT d.1.2) _ _ _
  have key := fun (x : P.Inst' → ℝ) (hx : P.toInst.IsLPFeasible (fun _ => 1) x) =>
    Inst.seq_alg (x := x) hcrit hΔ (P.seqKey_prop hT g) hp hx
  refine ⟨(key 0 ⟨fun _ => le_rfl, fun e => by simp, fun a => by simp⟩).1, fun O hO => ?_⟩
  have := (key _ (Inst.IsIndep.isLPFeasible _ hO)).2
  rw [Inst.lpValue_ind] at this
  norm_num at this
  linarith

end TreeInput

end

end Podc.LineTreeScheduling
