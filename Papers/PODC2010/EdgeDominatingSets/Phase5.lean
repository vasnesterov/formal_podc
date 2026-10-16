import Papers.PODC2010.EdgeDominatingSets.Phases

/-!
# The three phases of the algorithm of Theorem 5 (§7.1), as global processes

* Phase I (`matchStep`, `mphase1`): greedy matching along the matchings `M_G(i, j)`. Invariant:
  `M` is a matching (`isMatching_mphase1`); property (b) of §7.3 (`odd_cover_mphase1`).
* Phase II (`propStep`, iterated over pairs `(i, q)` with `i ≤ Δ`, `q < Δ`): in step `(i, q)`
  every *black* node (degree `i`, unmatched) proposes along its port `q` to a *white* neighbour
  (degree `< i`, unmatched); every white node accepts the proposal arriving at its smallest port.
  This is a variant of the proposal algorithm of §7.1 (a black node proposes along port `q` even if
  the neighbour there is not white; the step is then wasted); it preserves maximality.
  Invariant: matching (`isMatching_propStep`). Result (`maximal_mphase2`): afterwards no edge joins
  two unmatched nodes of different degrees, which gives property (c).
* Phase III (`phase3`): the 2-matching `P` of §7.1 (a variant of the paper's proposal algorithm
  that preserves its properties), a proposal algorithm on the subgraph `H` of
  edges with both endpoints unmatched: in step `q` every node that has no accepted proposal yet
  proposes along its port `q`; every node that has not accepted a proposal yet accepts the one
  arriving at its smallest port. `pin u = some p`: `u` accepted the proposal arriving at port `p`;
  `pout v = some q`: the proposal of `v` along port `q` was accepted. Invariants `phase3_inv`;
  every edge of `H` has an endpoint covered by `P` (`phase3_dominates`).
-/

namespace Podc.EdgeDominatingSets

open Podc.PortNumbering Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### First port with a property -/

/-- The smallest port `p < d` with property `P`, if any. -/
def firstPort (d : ℕ) (P : ℕ → Prop) [DecidablePred P] : Option ℕ :=
  (List.range d).find? fun p => decide (P p)

theorem firstPort_spec {d : ℕ} {P : ℕ → Prop} [DecidablePred P] {p : ℕ}
    (h : firstPort d P = some p) : p < d ∧ P p := by
  unfold firstPort at h
  exact ⟨List.mem_range.1 (List.mem_of_find?_eq_some h), by simpa using List.find?_some h⟩

theorem firstPort_isSome {d : ℕ} {P : ℕ → Prop} [DecidablePred P] {p : ℕ} (hp : p < d)
    (h : P p) : (firstPort d P).isSome := by
  unfold firstPort
  rw [List.find?_isSome]
  exact ⟨p, List.mem_range.2 hp, by simpa using h⟩

theorem firstPort_congr {d : ℕ} {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ p < d, P p ↔ Q p) : firstPort d P = firstPort d Q := by
  unfold firstPort
  apply List.find?_congr
  intro p hp
  rw [decide_eq_decide]
  exact h p (List.mem_range.1 hp)

/-! ### Matchings -/

/-- `Ms` is a matching: distinct edges have no common endpoint. -/
def IsMatching (Ms : Finset (Sym2 V)) : Prop :=
  ∀ e₁ ∈ Ms, ∀ e₂ ∈ Ms, e₁ ≠ e₂ → ∀ x ∈ e₁, x ∉ e₂

omit [Fintype V] in
theorem IsMatching.card_le_one {Ms : Finset (Sym2 V)} (h : IsMatching Ms) (v : V) :
    (Ms.filter (v ∈ ·)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hne
  exact h a (mem_filter.1 ha).1 b (mem_filter.1 hb).1 hne v (mem_filter.1 ha).2 (mem_filter.1 hb).2

theorem isMatching_matchStep {G : PNGraph V} {i j : ℕ} {Ms : Finset (Sym2 V)}
    (h : IsMatching Ms) : IsMatching (matchStep G i j Ms) := by
  classical
  intro e₁ h₁ e₂ h₂ hne x hx₁ hx₂
  simp only [matchStep, mem_union, mem_filter] at h₁ h₂
  rcases h₁ with h₁ | ⟨hM₁, hu₁⟩ <;> rcases h₂ with h₂ | ⟨hM₂, hu₂⟩
  · exact h e₁ h₁ e₂ h₂ hne x hx₁ hx₂
  · exact hu₂ x hx₂ ⟨e₁, h₁, hx₁⟩
  · exact hu₁ x hx₁ ⟨e₂, h₂, hx₂⟩
  · exact M_matching hM₁ hM₂ hne hx₁ hx₂

/-- The matching after phase I of Theorem 5. -/
noncomputable def mphase1 (G : PNGraph V) (Δ n : ℕ) : Finset (Sym2 V) :=
  iterPairs (matchStep G) Δ ∅ n

theorem isMatching_mphase1 (G : PNGraph V) (Δ n : ℕ) : IsMatching (mphase1 G Δ n) := by
  induction n with
  | zero => intro e h; simp [mphase1] at h
  | succ n ih => exact isMatching_matchStep ih

/-- Property (b) of §7.3, established by phase I: a node with a distinguishable neighbour is
covered by `M`, or its distinguishable neighbour is. -/
theorem odd_cover_mphase1 {G : PNGraph V} {Δ : ℕ} (hΔ : ∀ v, G.deg v ≤ Δ) {v : V} {i : ℕ}
    (hv : G.dn v = some i) :
    Covered (mphase1 G Δ (Δ * Δ)) v ∨ Covered (mphase1 G Δ (Δ * Δ)) (G.nbr v i) := by
  classical
  have he := edge_dn_mem_M hv
  obtain ⟨hi, hj⟩ := lt_of_mem_M hΔ he
  obtain ⟨h1, h2, h3⟩ := pair_step hi hj
  have hmono := iterPairs_mono (subset_matchStep G) Δ ∅ (Nat.succ_le_of_lt h3)
  set D := iterPairs (matchStep G) Δ ∅ (i * Δ + G.rport v i)
  have hstep : iterPairs (matchStep G) Δ ∅ (i * Δ + G.rport v i + 1) = matchStep G i (G.rport v i) D := by
    rw [iterPairs_succ, h1, h2]
  by_cases hc : ∀ x ∈ G.edge v i, ¬ Covered D x
  · left
    refine Covered.mono hmono ?_
    rw [hstep]
    exact ⟨G.edge v i, mem_union_right _ (mem_filter.2 ⟨he, hc⟩), Sym2.mem_mk_left _ _⟩
  · push Not at hc
    obtain ⟨x, hx, hcx⟩ := hc
    have hcx' : Covered (mphase1 G Δ (Δ * Δ)) x :=
      Covered.mono hmono (by rw [hstep]; exact Covered.mono (subset_matchStep G _ _ _) hcx)
    simp only [PNGraph.edge, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact Or.inl hcx'
    · exact Or.inr hcx'

/-! ### Phase II -/

/-- White nodes in step `(i, q)`: unmatched, degree `< i`. -/
def White (G : PNGraph V) (Ms : Finset (Sym2 V)) (i : ℕ) (u : V) : Prop :=
  G.deg u < i ∧ ¬ Covered Ms u

/-- Black nodes in step `(i, q)`: unmatched, degree `= i`. -/
def Black (G : PNGraph V) (Ms : Finset (Sym2 V)) (i : ℕ) (v : V) : Prop :=
  G.deg v = i ∧ ¬ Covered Ms v

open Classical in
/-- The port at which the white node `u` accepts a proposal in step `(i, q)`: the smallest port
`p` such that the neighbour behind `p` is black and reaches `u` through its port `q`. -/
noncomputable def accPort (G : PNGraph V) (Ms : Finset (Sym2 V)) (i q : ℕ) (u : V) : Option ℕ :=
  if White G Ms i u then
    firstPort (G.deg u) fun p => Black G Ms i (G.nbr u p) ∧ G.rport u p = q
  else none

open Classical in
/-- Step `(i, q)` of phase II: add the accepted proposals. -/
noncomputable def propStep (G : PNGraph V) (i q : ℕ) (Ms : Finset (Sym2 V)) : Finset (Sym2 V) :=
  Ms ∪ univ.filter fun e => ∃ u p, accPort G Ms i q u = some p ∧ G.edge u p = e

theorem subset_propStep (G : PNGraph V) (i q : ℕ) (Ms : Finset (Sym2 V)) :
    Ms ⊆ propStep G i q Ms := subset_union_left

omit [Fintype V] [DecidableEq V] in
theorem accPort_spec {G : PNGraph V} {Ms : Finset (Sym2 V)} {i q : ℕ} {u : V} {p : ℕ}
    (h : accPort G Ms i q u = some p) :
    White G Ms i u ∧ p < G.deg u ∧ Black G Ms i (G.nbr u p) ∧ G.rport u p = q := by
  classical
  unfold accPort at h
  split_ifs at h with hw
  obtain ⟨hp, hb, hr⟩ := firstPort_spec h
  exact ⟨hw, hp, hb, hr⟩

theorem mem_propStep {G : PNGraph V} {i q : ℕ} {Ms : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ propStep G i q Ms ↔ e ∈ Ms ∨ ∃ u p, accPort G Ms i q u = some p ∧ G.edge u p = e := by
  classical
  simp [propStep]

theorem isMatching_propStep {G : PNGraph V} {i q : ℕ} {Ms : Finset (Sym2 V)}
    (h : IsMatching Ms) : IsMatching (propStep G i q Ms) := by
  classical
  have key : ∀ e₁ ∈ Ms, ∀ u p, accPort G Ms i q u = some p → ∀ x ∈ e₁, x ∉ G.edge u p := by
    intro e₁ h₁ u p hp x hx₁ hx₂
    obtain ⟨hw, -, hb, -⟩ := accPort_spec hp
    simp only [PNGraph.edge, Sym2.mem_iff] at hx₂
    rcases hx₂ with rfl | rfl
    · exact hw.2 ⟨e₁, h₁, hx₁⟩
    · exact hb.2 ⟨e₁, h₁, hx₁⟩
  intro e₁ h₁ e₂ h₂ hne x hx₁ hx₂
  rcases mem_propStep.1 h₁ with h₁ | ⟨u, p, hp, rfl⟩ <;>
    rcases mem_propStep.1 h₂ with h₂ | ⟨u', p', hp', rfl⟩
  · exact h e₁ h₁ e₂ h₂ hne x hx₁ hx₂
  · exact key e₁ h₁ u' p' hp' x hx₁ hx₂
  · exact key e₂ h₂ u p hp x hx₂ hx₁
  · obtain ⟨hw, hpd, hb, hr⟩ := accPort_spec hp
    obtain ⟨hw', hpd', hb', hr'⟩ := accPort_spec hp'
    simp only [PNGraph.edge, Sym2.mem_iff] at hx₁ hx₂
    apply hne
    rcases hx₁ with rfl | rfl <;> rcases hx₂ with h2 | h2
    · subst h2; rw [hp] at hp'; cases hp'; rfl
    · have := hw.1; rw [h2, hb'.1] at this; exact absurd this (lt_irrefl _)
    · have := hw'.1; rw [← h2, hb.1] at this; exact absurd this (lt_irrefl _)
    · -- common black neighbour; its port `q` leads to both `u` and `u'`
      have e1 : G.nbr (G.nbr u p) q = u := by rw [← hr]; exact G.nbr_nbr hpd
      have e2 : G.nbr (G.nbr u' p') q = u' := by rw [← hr']; exact G.nbr_nbr hpd'
      rw [h2] at e1
      rw [e1] at e2
      subst e2
      rw [hp'] at hp; cases hp; rfl

theorem propStep_sub {G : PNGraph V} (hG : G.IsSimple) {i q : ℕ} {Ms : Finset (Sym2 V)}
    (h : ∀ e ∈ Ms, e ∈ G.toSimpleGraph.edgeSet) :
    ∀ e ∈ propStep G i q Ms, e ∈ G.toSimpleGraph.edgeSet := by
  intro e he
  rcases mem_propStep.1 he with he | ⟨u, p, hp, rfl⟩
  · exact h e he
  · exact G.edge_mem_edgeSet hG (accPort_spec hp).2.1

/-- The matching after `n` steps of phase II, starting from `M₀`. Step `n` processes
`(i, q) = (n / Δ, n % Δ)`; `(Δ + 1)Δ` steps cover all `i ≤ Δ`, `q < Δ`. -/
noncomputable def mphase2 (G : PNGraph V) (Δ : ℕ) (M₀ : Finset (Sym2 V)) (n : ℕ) :
    Finset (Sym2 V) :=
  iterPairs (propStep G) Δ M₀ n

theorem isMatching_mphase2 (G : PNGraph V) (Δ : ℕ) {M₀ : Finset (Sym2 V)} (h : IsMatching M₀)
    (n : ℕ) : IsMatching (mphase2 G Δ M₀ n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact isMatching_propStep ih

/-- **Maximality** (property (c) of §7.3): after phase II no edge joins two unmatched nodes of
different degrees. -/
theorem maximal_mphase2 {G : PNGraph V} {Δ : ℕ} (hΔ : ∀ v, G.deg v ≤ Δ) (M₀ : Finset (Sym2 V))
    {v : V} {q : ℕ} (hq : q < G.deg v) (hlt : G.deg (G.nbr v q) < G.deg v) :
    Covered (mphase2 G Δ M₀ ((Δ + 1) * Δ)) v ∨
      Covered (mphase2 G Δ M₀ ((Δ + 1) * Δ)) (G.nbr v q) := by
  classical
  set i := G.deg v
  have hiΔ : i ≤ Δ := hΔ v
  have hqΔ : q < Δ := lt_of_lt_of_le hq hiΔ
  have h1 : (i * Δ + q) / Δ = i := by
    rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hqΔ, zero_add]
  have h2 : (i * Δ + q) % Δ = q := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hqΔ]
  have h3 : i * Δ + q + 1 ≤ (Δ + 1) * Δ := by nlinarith
  have hmono := iterPairs_mono (subset_propStep G) Δ M₀ h3
  set D := iterPairs (propStep G) Δ M₀ (i * Δ + q)
  have hstep : iterPairs (propStep G) Δ M₀ (i * Δ + q + 1) = propStep G i q D := by
    rw [iterPairs_succ, h1, h2]
  have hD : D ⊆ propStep G i q D := subset_propStep G i q D
  by_cases hcv : Covered D v
  · exact Or.inl (Covered.mono hmono (by rw [hstep]; exact Covered.mono hD hcv))
  by_cases hcu : Covered D (G.nbr v q)
  · exact Or.inr (Covered.mono hmono (by rw [hstep]; exact Covered.mono hD hcu))
  -- `u = nbr v q` is white and receives the proposal of the black `v` at port `rport v q`
  right
  set u := G.nbr v q
  have hsome : (accPort G D i q u).isSome := by
    unfold accPort
    rw [ite_eq_left ⟨hlt, hcu⟩]
    refine firstPort_isSome (G.rport_lt hq) ⟨?_, G.rport_rport hq⟩
    rw [G.nbr_nbr hq]
    exact ⟨rfl, hcv⟩
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hsome
  refine Covered.mono hmono ?_
  rw [hstep]
  exact ⟨G.edge u p, mem_propStep.2 (Or.inr ⟨u, p, hp, rfl⟩), Sym2.mem_mk_left _ _⟩

/-! ### Phase III -/

/-- A node `t` proposes along its port `q`: it is unmatched (`U t`), none of its proposals has
been accepted yet, and the neighbour behind port `q` is unmatched. -/
def Eligible (G : PNGraph V) (U : V → Prop) (pout : V → Option ℕ) (q : ℕ) (t : V) : Prop :=
  U t ∧ pout t = none ∧ q < G.deg t ∧ U (G.nbr t q)

open Classical in
/-- Accepting proposals in step `q`. -/
noncomputable def accept3 (G : PNGraph V) (U : V → Prop) (q : ℕ) (pin pout : V → Option ℕ) :
    V → Option ℕ := fun u =>
  if pin u = none ∧ U u then
    firstPort (G.deg u) fun p => Eligible G U pout q (G.nbr u p) ∧ G.rport u p = q
  else pin u

open Classical in
/-- Proposers learn whether their proposal of step `q` was accepted. -/
noncomputable def commit3 (G : PNGraph V) (q : ℕ) (pin' pout : V → Option ℕ) : V → Option ℕ :=
  fun v => if pout v = none ∧ q < G.deg v ∧ pin' (G.nbr v q) = some (G.rport v q) then some q
    else pout v

/-- The state `(pin, pout)` after steps `0, …, Q - 1` of phase III. -/
noncomputable def phase3 (G : PNGraph V) (U : V → Prop) : ℕ → (V → Option ℕ) × (V → Option ℕ)
  | 0 => (fun _ => none, fun _ => none)
  | q + 1 =>
    ((accept3 G U q (phase3 G U q).1 (phase3 G U q).2),
      commit3 G q (accept3 G U q (phase3 G U q).1 (phase3 G U q).2) (phase3 G U q).2)

/-- Invariants of phase III. -/
structure Inv3 (G : PNGraph V) (U : V → Prop) (Q : ℕ) (pin pout : V → Option ℕ) : Prop where
  pin_spec : ∀ u p, pin u = some p →
    p < G.deg u ∧ U u ∧ U (G.nbr u p) ∧ pout (G.nbr u p) = some (G.rport u p)
  pout_spec : ∀ v r, pout v = some r → r < G.deg v ∧ pin (G.nbr v r) = some (G.rport v r)
  dom : ∀ v, U v → pout v = none → ∀ q < Q, q < G.deg v → U (G.nbr v q) →
    pin (G.nbr v q) ≠ none

omit [Fintype V] [DecidableEq V] in
theorem phase3_inv (G : PNGraph V) (U : V → Prop) (Q : ℕ) :
    Inv3 G U Q (phase3 G U Q).1 (phase3 G U Q).2 := by
  classical
  induction Q with
  | zero => exact ⟨by simp [phase3], by simp [phase3], fun _ _ _ q hq => absurd hq (by omega)⟩
  | succ Q ih =>
    obtain ⟨I1, I2, I3⟩ := ih
    set pin := (phase3 G U Q).1
    set pout := (phase3 G U Q).2
    have hpin' : (phase3 G U (Q + 1)).1 = accept3 G U Q pin pout := rfl
    have hpout' : (phase3 G U (Q + 1)).2 = commit3 G Q (accept3 G U Q pin pout) pout := rfl
    rw [hpin', hpout']
    set pin' := accept3 G U Q pin pout
    -- `pin'` extends `pin`
    have hext : ∀ u p, pin u = some p → pin' u = some p := by
      intro u p h
      simp only [pin', accept3, h, reduceCtorEq, false_and, ite_false]
    have hpout_ext : ∀ v r, pout v = some r → commit3 G Q pin' pout v = some r := by
      intro v r h
      simp only [commit3, h, reduceCtorEq, false_and, ite_false]
    refine ⟨?_, ?_, ?_⟩
    · intro u p hp
      by_cases hold : pin u = none ∧ U u
      · have hpu : pin' u = some p := hp
        simp only [pin', accept3, hold, and_self, ite_true] at hp
        obtain ⟨hpd, ⟨hU, hnone, hq, hUq⟩, hr⟩ := firstPort_spec hp
        refine ⟨hpd, hold.2, hU, ?_⟩
        have e1 : G.nbr (G.nbr u p) Q = u := by rw [← hr]; exact G.nbr_nbr hpd
        have e2 : G.rport (G.nbr u p) Q = p := by rw [← hr]; exact G.rport_rport hpd
        simp only [commit3, hnone, hq, e1, e2, true_and, hpu, ite_true, hr]
      · have hp' : pin u = some p := by
          simp only [pin', accept3, hold, ite_false] at hp; exact hp
        obtain ⟨a, b, c, d⟩ := I1 u p hp'
        exact ⟨a, b, c, hpout_ext _ _ d⟩
    · intro v r hr
      by_cases hc : pout v = none ∧ Q < G.deg v ∧ pin' (G.nbr v Q) = some (G.rport v Q)
      · simp only [commit3, hc, and_self, ite_true, Option.some.injEq] at hr
        subst hr
        exact ⟨hc.2.1, hc.2.2⟩
      · simp only [commit3, hc, ite_false] at hr
        obtain ⟨a, b⟩ := I2 v r hr
        exact ⟨a, hext _ _ b⟩
    · intro v hU hnone q hq hqd hUq
      have hnone' : pout v = none := by
        by_contra h
        obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 h
        rw [hpout_ext v r hr] at hnone
        cases hnone
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | rfl
      · intro h
        apply I3 v hU hnone' q hq hqd hUq
        by_contra h'
        obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 h'
        rw [hext _ _ hr] at h
        cases h
      · set u := G.nbr v q
        by_cases hu : pin u = none
        · have hsome : (pin' u).isSome := by
            simp only [pin', accept3, hu, hUq, and_self, ite_true]
            refine firstPort_isSome (G.rport_lt hqd) ⟨?_, G.rport_rport hqd⟩
            rw [G.nbr_nbr hqd]
            exact ⟨hU, hnone', hqd, hUq⟩
          intro h; rw [h] at hsome; cases hsome
        · intro h
          obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hu
          rw [hext _ _ hr] at h
          cases h

omit [Fintype V] [DecidableEq V] in
/-- After phase III (`Q ≥` all degrees), every edge of `H` (both endpoints unmatched) has an
endpoint `x` with `pin x ≠ none` or `pout x ≠ none`. -/
theorem phase3_dominates (G : PNGraph V) (U : V → Prop) {Q : ℕ} (hQ : ∀ v, G.deg v ≤ Q) {v : V}
    {q : ℕ} (hq : q < G.deg v) (hU : U v) (hUq : U (G.nbr v q)) :
    (phase3 G U Q).2 v ≠ none ∨ (phase3 G U Q).1 (G.nbr v q) ≠ none := by
  by_cases h : (phase3 G U Q).2 v = none
  · exact Or.inr ((phase3_inv G U Q).dom v hU h q (lt_of_lt_of_le hq (hQ v)) hq hUq)
  · exact Or.inl h

end Podc.EdgeDominatingSets
