import Papers.PODC2010.EdgeDominatingSets.Phases

/-!
# Theorem 4: a `(4 - 6/(d+1))`-approximation in `d`-regular graphs, `d` odd, in `O(d²)` rounds

The algorithm (§6 of the paper), as a local process (`Algorithm.ofLocal`) with `2 + 2d²` rounds:

* round 0: learn the remote port numbers, compute the distinguishable port `dn`;
* round 1: learn which neighbours chose this node as their distinguishable neighbour (`chosen`);
  now every node can decide locally which incident edges are in `M_G(i, j)` (`edge_mem_M_iff`);
* rounds `2 .. 2 + d² - 1`: phase I, one pair `(i, j)` per round (`addStep`);
* rounds `2 + d² .. 2 + 2d² - 1`: phase II, one pair per round (`remStep`).

The node data records the selected ports `inD`. We prove that the run simulates the global
processes `phase1`/`phase2` of `Phases.lean` (`inD_phase1`, `inD_phase2`), and then analyse the
latter: the output is an edge cover in which every edge has a private endpoint, hence has at most
`d|V|/(d+1)` edges.
-/

namespace Podc.EdgeDominatingSets

open Cslib.PortNumbering Finset

/-- Local data of a node in the algorithm of Theorem 4. -/
structure St4 where
  /-- own degree -/
  deg : ℕ
  /-- remote port numbers -/
  rp : ℕ → ℕ
  /-- own distinguishable port -/
  dn : Option ℕ
  /-- `chosen q`: the neighbour behind port `q` has this node as distinguishable neighbour -/
  chosen : ℕ → Bool
  /-- the incident edges currently in `D` -/
  inD : ℕ → Bool

namespace St4

/-- Initial (meaningless) data. -/
def init : St4 := ⟨0, fun _ => 0, none, fun _ => false, fun _ => false⟩

/-- The node is covered by `D`. -/
def cov (s : St4) : Bool := decide (∃ q < s.deg, s.inD q = true)

/-- The node is covered by an edge of `D` other than the one behind port `q`. -/
def covEx (s : St4) (q : ℕ) : Bool := decide (∃ q' < s.deg, q' ≠ q ∧ s.inD q' = true)

/-- The edge behind port `q` is in `M_G(i, j)` (decided locally, cf. `edge_mem_M_iff`). -/
def inM (s : St4) (i j q : ℕ) : Bool :=
  decide ((s.dn = some q ∧ q = i ∧ s.rp q = j) ∨ (s.chosen q = true ∧ s.rp q = i ∧ q = j))

end St4

/-- Remote port numbers from the received messages. -/
def rpOf {α : Type} (m : ℕ → Option (α × ℕ)) (i : ℕ) : ℕ := ((m i).map Prod.snd).getD 0

/-- The local rule of the algorithm of Theorem 4 with parameter `Δ` (the degree). -/
def rule4 (Δ : ℕ) : ℕ → ℕ → St4 → (ℕ → Option (St4 × ℕ)) → St4
  | 0, d, _, m => ⟨d, rpOf m, dnOf d (rpOf m), fun _ => false, fun _ => false⟩
  | 1, _, s, m => { s with chosen := fun q => match m q with
      | some (t, j) => decide (t.dn = some j)
      | none => false }
  | r + 2, _, s, m =>
    if r < Δ * Δ then
      { s with inD := fun q => s.inD q || (s.inM (r / Δ) (r % Δ) q && match m q with
          | some (t, _) => !(s.cov && t.cov)
          | none => false) }
    else if r < 2 * (Δ * Δ) then
      { s with inD := fun q => s.inD q && !(s.inM ((r - Δ * Δ) / Δ) ((r - Δ * Δ) % Δ) q &&
          match m q with
          | some (t, j) => s.covEx q && t.covEx j
          | none => false) }
    else s

/-- **The algorithm of Theorem 4** for degree `Δ`: running time `2 + 2Δ²` rounds. -/
def alg4 (Δ : ℕ) : Algorithm Unit (Set ℕ) :=
  ((Algorithm.ofFun fun _ _ => St4.init).seq 0 (Algorithm.ofLocal (rule4 Δ))).seq
    (2 + 2 * (Δ * Δ)) (Algorithm.ofFun fun _ s => {q | q < s.deg ∧ s.inD q = true})

variable {V : Type} [Fintype V] [DecidableEq V]

section Simulation

variable (G : PNGraph V) (Δ : ℕ)

/-- The run of the local process. -/
def run4 (r : ℕ) : V → St4 := Algorithm.localRun G (rule4 Δ) (fun _ => St4.init) r

omit [Fintype V] [DecidableEq V] in
theorem alg4_eval (v : V) :
    (alg4 Δ).eval G (2 + 2 * (Δ * Δ)) (fun _ => ()) v =
      {q | q < (run4 G Δ (2 + 2 * (Δ * Δ)) v).deg ∧ (run4 G Δ (2 + 2 * (Δ * Δ)) v).inD q = true} := by
  have h1 := congrFun (Algorithm.eval_seq ((Algorithm.ofFun fun _ _ => St4.init).seq 0
    (Algorithm.ofLocal (rule4 Δ))) (2 + 2 * (Δ * Δ))
    (Algorithm.ofFun fun _ (s : St4) => {q | q < s.deg ∧ s.inD q = true}) G 0 (fun _ => ())) v
  have h2 := Algorithm.eval_seq (Algorithm.ofFun fun _ _ => St4.init) 0
    (Algorithm.ofLocal (rule4 Δ)) G (2 + 2 * (Δ * Δ)) (fun _ : V => ())
  rw [Nat.add_zero] at h1
  rw [zero_add] at h2
  rw [alg4, h1, Algorithm.eval_ofFun, h2, Algorithm.eval_ofLocal]
  rfl

omit [Fintype V] [DecidableEq V] in
theorem run4_succ (r : ℕ) (v : V) :
    run4 G Δ (r + 1) v = rule4 Δ r (G.deg v) (run4 G Δ r v)
      (Algorithm.nbrInfo G (run4 G Δ r) v) := rfl

omit [Fintype V] [DecidableEq V] in
theorem nbrInfo_of_lt {α : Type} (x : V → α) {v : V} {q : ℕ} (hq : q < G.deg v) :
    Algorithm.nbrInfo G x v q = some (x (G.nbr v q), G.rport v q) := by
  simp [Algorithm.nbrInfo, hq]

omit [Fintype V] [DecidableEq V] in
/-- The static data is correct after round `0`. -/
theorem run4_static (r : ℕ) (v : V) :
    (run4 G Δ (r + 1) v).deg = G.deg v ∧ (∀ q < G.deg v, (run4 G Δ (r + 1) v).rp q = G.rport v q) ∧
      (run4 G Δ (r + 1) v).dn = G.dn v := by
  induction r generalizing v with
  | zero =>
    have hrp : ∀ q < G.deg v, rpOf (Algorithm.nbrInfo G (run4 G Δ 0) v) q = G.rport v q := by
      intro q hq; simp [rpOf, nbrInfo_of_lt G _ hq]
    refine ⟨rfl, hrp, ?_⟩
    exact dnOf_congr hrp
  | succ r ih =>
    rw [run4_succ]
    rcases r with _ | r
    · exact ih v
    · simp only [rule4]
      split_ifs <;> exact ih v

/-- Correct static data: degree, remote ports, distinguishable port, `chosen`. -/
def Stat (y : V → St4) : Prop :=
  ∀ v, (y v).deg = G.deg v ∧ (∀ q < G.deg v, (y v).rp q = G.rport v q) ∧ (y v).dn = G.dn v ∧
    ∀ q < G.deg v, (y v).chosen q = decide (G.dn (G.nbr v q) = some (G.rport v q))

/-- The data `inD` represents the edge set `D`. -/
def Repr (y : V → St4) (D : Finset (Sym2 V)) : Prop :=
  ∀ v, ∀ q < G.deg v, (y v).inD q = true ↔ G.edge v q ∈ D

omit [Fintype V] [DecidableEq V] in
theorem run4_stat (r : ℕ) : Stat G (run4 G Δ (r + 2)) := by
  intro v
  obtain ⟨h1, h2, h3⟩ := run4_static G Δ (r + 1) v
  refine ⟨h1, h2, h3, ?_⟩
  induction r generalizing v with
  | zero =>
    intro q hq
    rw [run4_succ]
    simp only [rule4, nbrInfo_of_lt G _ hq]
    rw [(run4_static G Δ 0 _).2.2]
  | succ r ih =>
    intro q hq
    rw [run4_succ]
    simp only [rule4]
    split_ifs
    · exact ih v (run4_static G Δ _ v).1 (run4_static G Δ _ v).2.1 (run4_static G Δ _ v).2.2 q hq
    · exact ih v (run4_static G Δ _ v).1 (run4_static G Δ _ v).2.1 (run4_static G Δ _ v).2.2 q hq
    · exact ih v (run4_static G Δ _ v).1 (run4_static G Δ _ v).2.1 (run4_static G Δ _ v).2.2 q hq

end Simulation

section Local

variable {G : PNGraph V} (hG : G.IsSimple)
include hG

omit [Fintype V] [DecidableEq V] hG in
/-- Every edge of a subgraph at `v` is the edge behind some port of `v`. -/
theorem exists_port_of_mem {D : Finset (Sym2 V)} (hD : ∀ e ∈ D, e ∈ G.toSimpleGraph.edgeSet)
    {v : V} {e : Sym2 V} (he : e ∈ D) (hv : v ∈ e) : ∃ q < G.deg v, G.edge v q = e := by
  obtain ⟨u, rfl⟩ : ∃ u, e = s(v, u) := ⟨_, (Sym2.other_spec hv).symm⟩
  obtain ⟨q, hq, hu⟩ := G.exists_port_of_adj (hD _ he)
  exact ⟨q, hq, by rw [PNGraph.edge, hu]⟩

omit [Fintype V] [DecidableEq V] hG in
theorem cov_iff {y : V → St4} (hy : Stat G y) {D : Finset (Sym2 V)}
    (hD : ∀ e ∈ D, e ∈ G.toSimpleGraph.edgeSet) (hR : Repr G y D) (v : V) :
    (y v).cov = true ↔ Covered D v := by
  simp only [St4.cov, decide_eq_true_eq, (hy v).1]
  constructor
  · rintro ⟨q, hq, h⟩
    exact ⟨_, (hR v q hq).1 h, Sym2.mem_mk_left _ _⟩
  · rintro ⟨e, he, hve⟩
    obtain ⟨q, hq, rfl⟩ := exists_port_of_mem hD he hve
    exact ⟨q, hq, (hR v q hq).2 he⟩

omit [Fintype V] [DecidableEq V] in
theorem covEx_iff {y : V → St4} (hy : Stat G y) {D : Finset (Sym2 V)}
    (hD : ∀ e ∈ D, e ∈ G.toSimpleGraph.edgeSet) (hR : Repr G y D) {v : V} {q : ℕ}
    (hq : q < G.deg v) :
    (y v).covEx q = true ↔ ∃ e' ∈ D, e' ≠ G.edge v q ∧ v ∈ e' := by
  simp only [St4.covEx, decide_eq_true_eq, (hy v).1]
  constructor
  · rintro ⟨q', hq', hne, h⟩
    refine ⟨_, (hR v q' hq').1 h, fun he => hne ?_, Sym2.mem_mk_left _ _⟩
    exact hG.2 v q' q hq' hq ((Sym2.congr_right).1 he)
  · rintro ⟨e, he, hne, hve⟩
    obtain ⟨q', hq', rfl⟩ := exists_port_of_mem hD he hve
    exact ⟨q', hq', fun h => hne (h ▸ rfl), (hR v q' hq').2 he⟩

omit [DecidableEq V] in
theorem inM_iff {y : V → St4} (hy : Stat G y) {v : V} {q : ℕ} (hq : q < G.deg v) (i j : ℕ) :
    (y v).inM i j q = true ↔ G.edge v q ∈ M G i j := by
  obtain ⟨-, hrp, hdn, hch⟩ := hy v
  simp only [St4.inM, decide_eq_true_eq, hrp q hq, hdn, hch q hq]
  rw [edge_mem_M_iff hG hq]

omit [Fintype V] [DecidableEq V] hG in
theorem forall_mem_edge {P : V → Prop} {v : V} {q : ℕ} :
    (∀ x ∈ G.edge v q, P x) ↔ P v ∧ P (G.nbr v q) := by
  simp [PNGraph.edge, Sym2.mem_iff, forall_eq_or_imp]

theorem phase1_sub (Δ n : ℕ) : ∀ e ∈ phase1 G Δ n, e ∈ G.toSimpleGraph.edgeSet := by
  intro e he
  obtain ⟨i, j, h⟩ := mem_M_of_mem_iterPairs (addStep_cases G) Δ (by simp) n e he
  exact mem_edgeSet_of_mem_M hG h

theorem inD_phase1 (Δ : ℕ) {n : ℕ} (hn : n ≤ Δ * Δ) :
    Repr G (run4 G Δ (n + 2)) (phase1 G Δ n) := by
  classical
  induction n with
  | zero =>
    intro v q hq
    simp [run4_succ, rule4, phase1]
  | succ n ih =>
    have hn' : n < Δ * Δ := by omega
    have ih := ih (by omega)
    intro v q hq
    rw [show n + 1 + 2 = (n + 2) + 1 by ring, run4_succ]
    simp only [rule4, ite_eq_left hn', nbrInfo_of_lt G _ hq]
    rw [phase1, iterPairs_succ, ← phase1, addStep, mem_union, mem_filter]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      ih v q hq, inM_iff hG (run4_stat G Δ n) hq]
    rw [← Bool.not_eq_true, ← Bool.not_eq_true, cov_iff (run4_stat G Δ n) (phase1_sub hG Δ n) ih,
      cov_iff (run4_stat G Δ n) (phase1_sub hG Δ n) ih, forall_mem_edge, not_and_or]

theorem phase2_sub (Δ n : ℕ) :
    ∀ e ∈ phase2 G Δ (phase1 G Δ (Δ * Δ)) n, e ∈ G.toSimpleGraph.edgeSet :=
  fun e he => phase1_sub hG Δ _ e (iterPairs_anti (remStep_subset G) Δ _ (Nat.zero_le n) he)

theorem inD_phase2 (Δ : ℕ) {n : ℕ} (hn : n ≤ Δ * Δ) :
    Repr G (run4 G Δ (Δ * Δ + n + 2)) (phase2 G Δ (phase1 G Δ (Δ * Δ)) n) := by
  classical
  induction n with
  | zero => exact inD_phase1 hG Δ le_rfl
  | succ n ih =>
    have hn' : n < Δ * Δ := by omega
    have ih := ih (by omega)
    have hst := run4_stat G Δ (Δ * Δ + n)
    have hsub := phase2_sub hG Δ n
    intro v q hq
    rw [show Δ * Δ + (n + 1) + 2 = (Δ * Δ + n) + 2 + 1 by ring, run4_succ]
    simp only [rule4, ite_eq_right (show ¬ Δ * Δ + n < Δ * Δ by omega),
      ite_eq_left (show Δ * Δ + n < 2 * (Δ * Δ) by omega), nbrInfo_of_lt G _ hq,
      show Δ * Δ + n - Δ * Δ = n by omega]
    rw [phase2, iterPairs_succ, ← phase2, remStep, mem_filter]
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, ih v q hq, not_and_or]
    simp only [← Bool.not_eq_true]
    rw [covEx_iff hG hst hsub ih hq,
      covEx_iff hG hst hsub ih (G.rport_lt hq), G.edge_nbr hq, forall_mem_edge, not_and_or,
      inM_iff hG hst hq]

end Local

/-- **Theorem 4.** For odd `d`, in every simple `d`-regular port-numbered graph, the algorithm
`alg4 d` finds a factor-`(4 - 6/(d+1))` approximation of a minimum edge dominating set in
`2 + 2d²` rounds. -/
theorem theorem_4 {d : ℕ} (hd : Odd d) (G : PNGraph V) (hG : G.IsSimple)
    (hreg : ∀ v, G.deg v = d) :
    Approximates (alg4 d) (2 + 2 * (d * d)) G (4 - 6 / (d + 1)) := by
  classical
  have hd1 : 1 ≤ d := hd.pos
  set D := phase2 G d (phase1 G d (d * d)) (d * d) with hDdef
  have hR := inD_phase2 hG d (le_refl (d * d))
  have hsub := phase2_sub hG d (d * d)
  have hX : ∀ v, (alg4 d).eval G (2 + 2 * (d * d)) (fun _ => ()) v =
      {q | q < G.deg v ∧ G.edge v q ∈ D} := by
    intro v
    rw [alg4_eval, show 2 + 2 * (d * d) = d * d + d * d + 2 by ring,
      (run4_stat G d (d * d + d * d) v).1]
    ext q
    simp only [Set.mem_ofPred_eq]
    exact and_congr_right fun hq => hR v q hq
  have hout : outEdges G ((alg4 d).eval G (2 + 2 * (d * d)) (fun _ => ())) = D := by
    ext e
    rw [mem_outEdges]
    constructor
    · rintro ⟨v, q, hq, hqX, rfl⟩
      rw [hX] at hqX
      exact hqX.2
    · intro he
      obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨e.out.1, Sym2.out_fst_mem e⟩
      obtain ⟨q, hq, rfl⟩ := exists_port_of_mem hsub he hv
      exact ⟨v, q, hq, by rw [hX]; exact ⟨hq, he⟩, rfl⟩
  have hcov : ∀ v, Covered D v := by
    intro v
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 (G.dn_isSome_of_odd (v := v) (by rw [hreg]; exact hd))
    exact covered_phase2 (covered_phase1 (fun v => (hreg v).le) hi) _
  refine ⟨?_, ?_, ?_⟩
  · intro v q hq hqX
    rw [hX] at hqX ⊢
    exact ⟨G.rport_lt hq, by rw [G.edge_nbr hq]; exact hqX.2⟩
  · rw [hout]
    exact isEDS_of_cover hsub Set.univ (fun v _ => hcov v) (fun u _ _ => Or.inl trivial)
  · rw [hout]
    have hdeg : ∀ v, (D.filter (v ∈ ·)).card ≤ d := by
      intro v
      calc (D.filter (v ∈ ·)).card ≤ (G.toSimpleGraph.incidenceFinset v).card := by
            apply card_le_card
            intro e he
            obtain ⟨he, hve⟩ := mem_filter.1 he
            rw [SimpleGraph.mem_incidenceFinset]
            exact ⟨hsub e he, hve⟩
        _ = d := by rw [SimpleGraph.card_incidenceFinset_eq_degree, G.degree_eq hG, hreg]
    have hcount := card_mul_le hd1 (fun e he => G.toSimpleGraph.not_isDiag_of_mem_edgeSet (hsub e he))
      hdeg (private_phase2 (fun v => (hreg v).le)
        (fun e he => mem_M_of_mem_iterPairs (addStep_cases G) d (by simp) _ e he))
    have hsum := sum_deg_add_le hG (d := d) (fun v => (hreg v).le)
    simp only [hreg, sum_const, card_univ, smul_eq_mul] at hsum
    set γ := edgeDomNum G.toSimpleGraph
    have key : (d + 1) * D.card + 2 * γ ≤ 4 * d * γ := by nlinarith
    have hdR : (0 : ℝ) < d + 1 := by positivity
    have keyR : ((d : ℝ) + 1) * D.card + 2 * γ ≤ 4 * d * γ := by exact_mod_cast key
    rw [show (4 - 6 / ((d : ℝ) + 1)) * γ = (4 * d * γ - 2 * γ) / (d + 1) by field_simp; ring,
      le_div_iff₀ hdR]
    linarith

end Podc.EdgeDominatingSets
