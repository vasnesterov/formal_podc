import Papers.PODC2026.ContentObliviousEulerian.Pairing

-- CSLib candidate: Cslib/Combinatorics/SimpleGraph/PortPairing.lean (circuit decomposition induced by a pairing)

/-!
# Lemma 2: a port pairing induces a unique circuit decomposition

Frei, Gelles, Ghazy, Nolin, PODC 2026, §2.1, Lemma 2 (and Kotzig 1968, Lemma 4, which the paper
cites: "every pairing of the edges incident to every node induces a unique circuit decomposition").

A closed walk *follows* a pairing `π` if it leaves every node through the port paired with the one
it entered by, including at the closing node (`Pairing.Follows`). For every dart `d` the walk
`π.circuitWalk d` starts with `d` and follows `π` until it first returns to `d`. We show:

* `circuitWalk d` is a circuit (a closed trail, `Walk.IsCircuit`) that follows `π`, and its edge set
  is the class `π.circuitEdges d`;
* these classes partition the edges of `G` (`Pairing.circuits_partition`);
* uniqueness: the edge set of *every* circuit that follows `π` is one of these classes.

`lemma2` packages this for the pairing `(1,2), (3,4), …` of every node (`stdPairing`).
-/

namespace Podc.ContentObliviousEulerian

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Pairing

variable (π : Pairing G)

set_option linter.unusedSectionVars false

/-- A closed walk *follows* `π` if consecutive darts `x, y` (cyclically, including the last and
the first dart) satisfy `y = π.pair x.symm`. -/
def Follows {u : V} (w : G.Walk u u) : Prop :=
  w.darts.IsChain (fun x y => π.next x = y) ∧
    ∀ x ∈ w.darts.getLast?, ∀ y ∈ w.darts.head?, π.next x = y

/-- The walk starting with `d` and following `π` for `n` darts. -/
def walkAux : (n : ℕ) → (d : G.Dart) → G.Walk d.fst ((⇑π.next)^[n] d).fst
  | 0, _ => Walk.nil
  | n + 1, d => Walk.cons d.adj ((walkAux n (π.next d)).copy (π.next_fst d) rfl)

lemma walkAux_darts (n : ℕ) (d : G.Dart) :
    (π.walkAux n d).darts = (List.range n).map (fun i => (π.next ^ i) d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [walkAux, Walk.darts_cons]
    erw [Walk.darts_copy]
    rw [ih, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, pow_zero, Equiv.Perm.one_apply]
    congr 1

/-- The period of `d` under `next`: the length of the circuit through `d`. -/
noncomputable def period (d : G.Dart) : ℕ := Function.minimalPeriod π.next d

lemma period_pos (d : G.Dart) : 0 < π.period d :=
  Function.minimalPeriod_pos_of_mem_periodicPts (π.next.injective.mem_periodicPts d)

lemma pow_period (d : G.Dart) : (π.next ^ π.period d) d = d := by
  rw [← Equiv.Perm.iterate_eq_pow]; exact Function.iterate_minimalPeriod

/-- The circuit through `d`: start with `d` and follow `π` until returning to `d`. -/
noncomputable def circuitWalk (d : G.Dart) : G.Walk d.fst d.fst :=
  (π.walkAux (π.period d) d).copy rfl (by
    rw [Equiv.Perm.iterate_eq_pow, π.pow_period])

lemma circuitWalk_darts (d : G.Dart) :
    (π.circuitWalk d).darts = (List.range (π.period d)).map (fun i => (π.next ^ i) d) := by
  simp [circuitWalk, walkAux_darts]

lemma circuitWalk_edges (d : G.Dart) :
    (π.circuitWalk d).edges = (List.range (π.period d)).map (fun i => ((π.next ^ i) d).edge) := by
  simp [Walk.edges, circuitWalk_darts, List.map_map, Function.comp_def]

lemma pow_mod_period (d : G.Dart) (n : ℕ) : (π.next ^ (n % π.period d)) d = (π.next ^ n) d := by
  simp only [← Equiv.Perm.iterate_eq_pow]
  exact Function.iterate_mod_minimalPeriod_eq

/-- The circuit through `d` is a closed trail. -/
theorem circuitWalk_isCircuit (d : G.Dart) : (π.circuitWalk d).IsCircuit := by
  refine ⟨⟨?_⟩, ?_⟩
  · rw [circuitWalk_edges]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro i hi j hj hij
    simp only [List.mem_range] at hi hj
    rcases (dart_edge_eq_iff _ _).1 hij with h | h
    · simp only [← Equiv.Perm.iterate_eq_pow] at h
      exact Function.iterate_injOn_Iio_minimalPeriod hi hj h
    · exfalso
      apply π.not_sameCycle_symm ((π.next ^ j) d)
      rw [← h]
      exact ⟨(i : ℤ) - j, by
        rw [zpow_sub, zpow_natCast, zpow_natCast, Equiv.Perm.mul_apply]; simp⟩
  · intro h
    have := congrArg (fun w => w.darts.length) h
    simp only [circuitWalk_darts, List.length_map, List.length_range] at this
    have h0 := π.period_pos d
    simp at this; omega

/-- The circuit through `d` follows `π`. -/
theorem circuitWalk_follows (d : G.Dart) : π.Follows (π.circuitWalk d) := by
  obtain ⟨m, hm⟩ : ∃ m, π.period d = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (π.period_pos d)).symm⟩
  rw [Follows, circuitWalk_darts, hm]
  refine ⟨?_, ?_⟩
  · rw [List.isChain_map, List.isChain_range_succ]
    intro i _
    simp [pow_succ', Equiv.Perm.mul_apply]
  · intro x hx y hy
    rw [List.getLast?_map, Option.mem_def, Option.map_eq_some_iff] at hx
    rw [List.head?_map, Option.mem_def, Option.map_eq_some_iff] at hy
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := hy
    rw [List.getLast?_range] at hi
    rw [List.head?_range] at hj
    simp at hi hj
    subst hi hj
    rw [← Equiv.Perm.mul_apply, ← pow_succ', ← hm, π.pow_period]; simp

/-- The edge set of the circuit through `d` is the class of `d`. -/
theorem circuitWalk_edges_toFinset (d : G.Dart) :
    (π.circuitWalk d).edges.toFinset = π.circuitEdges d := by
  ext e
  rw [List.mem_toFinset, circuitWalk_edges, mem_circuitEdges]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, -, h⟩; exact ⟨i, h⟩
  · rintro ⟨n, h⟩
    exact ⟨n % π.period d, Nat.mod_lt _ (π.period_pos d), by rw [pow_mod_period, h]⟩

/-- A chain of successive `f`-images is the orbit of its head. -/
lemma chain_eq_map {f : Equiv.Perm G.Dart} :
    ∀ (l : List G.Dart) (d : G.Dart), (d :: l).IsChain (fun x y => f x = y) →
      d :: l = (List.range (l.length + 1)).map (fun i => (f ^ i) d)
  | [], d, _ => by simp
  | y :: l, d, h => by
    rw [List.isChain_cons_cons] at h
    obtain ⟨rfl, h⟩ := h
    have ih := chain_eq_map l (f d) h
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, pow_zero,
      Equiv.Perm.one_apply, ih]
    congr 1

lemma pow_mod_apply_of_pow {f : Equiv.Perm G.Dart} {x : G.Dart} {m : ℕ} (h : (f ^ m) x = x)
    (n : ℕ) : (f ^ (n % m)) x = (f ^ n) x := by
  have hp : Function.IsPeriodicPt f m x := by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, Equiv.Perm.iterate_eq_pow]; exact h
  simpa only [Equiv.Perm.iterate_eq_pow] using hp.iterate_mod_apply n

/-- **Uniqueness of the induced decomposition.** The edge set of every circuit that follows `π`
is one of the classes of `π`. -/
theorem edges_of_follows {u : V} (w : G.Walk u u) (hw : w.IsCircuit) (hf : π.Follows w) :
    ∃ d, w.edges.toFinset = π.circuitEdges d := by
  obtain ⟨hchain, hwrap⟩ := hf
  cases hl : w.darts with
  | nil =>
    exfalso; apply hw.ne_nil
    cases w with
    | nil => rfl
    | cons h p => simp at hl
  | cons d l =>
    rw [hl] at hchain hwrap
    have hmap := chain_eq_map l d hchain
    set m := l.length + 1
    -- periodicity
    have hper : (π.next ^ m) d = d := by
      have hlast : (d :: l).getLast? = some ((π.next ^ (m - 1)) d) := by
        rw [hmap, List.getLast?_map, List.getLast?_range]; simp [m]
      have := hwrap _ (by rw [hlast]; rfl) d (by simp)
      calc (π.next ^ m) d = π.next ((π.next ^ (m - 1)) d) := by
            rw [← Equiv.Perm.mul_apply, ← pow_succ']; congr 2
        _ = d := this
    refine ⟨d, ?_⟩
    ext e
    rw [List.mem_toFinset, mem_circuitEdges, Walk.edges, hl, hmap]
    simp only [List.map_map, List.mem_map, List.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨i, -, h⟩; exact ⟨i, h⟩
    · rintro ⟨n, h⟩
      refine ⟨n % m, Nat.mod_lt _ (by omega), ?_⟩
      rw [← h, pow_mod_apply_of_pow hper]

/-- **Kotzig's Lemma 4** (cited in §2.1): every port pairing induces a circuit decomposition, and
this decomposition is unique. The classes `π.circuits` partition the edges, each is the edge set of
a circuit that follows `π`, and every circuit that follows `π` has one of them as edge set. -/
theorem pairing_circuit_decomposition :
    (∀ e ∈ G.edgeSet, ∃! C, C ∈ π.circuits ∧ e ∈ C) ∧
    (∀ C ∈ π.circuits, ∃ d : G.Dart,
      (π.circuitWalk d).IsCircuit ∧ π.Follows (π.circuitWalk d) ∧
        (π.circuitWalk d).edges.toFinset = C) ∧
    (∀ (u : V) (w : G.Walk u u), w.IsCircuit → π.Follows w → w.edges.toFinset ∈ π.circuits) := by
  refine ⟨π.circuits_partition, ?_, ?_⟩
  · intro C hC
    obtain ⟨d, -, rfl⟩ := mem_image.1 hC
    exact ⟨d, π.circuitWalk_isCircuit d, π.circuitWalk_follows d, π.circuitWalk_edges_toFinset d⟩
  · intro u w hw hf
    obtain ⟨d, hd⟩ := π.edges_of_follows w hw hf
    rw [hd]; exact mem_image.2 ⟨d, mem_univ _, rfl⟩

/-- A circuit that follows `π` and contains all edges is an Eulerian circuit. -/
lemma isEulerian_of_edges {u : V} (w : G.Walk u u) (hw : w.IsTrail)
    (he : w.edges.toFinset = G.edgeFinset) : w.IsEulerian := by
  rw [hw.isEulerian_iff]
  ext e
  have := congrArg (e ∈ ·) he
  simpa [Walk.edgeSet] using this

end Pairing

/-- **Lemma 2.** In a network all of whose nodes have even degree, fixing at every node `v` the
port pairing `(1,2), …, (deg v - 1, deg v)` (for any port numbering; no communication is needed)
yields a circuit decomposition: the induced circuits partition the edges, each is a circuit
(closed trail) following the pairing, and this decomposition is the only one compatible with the
pairing. -/
theorem lemma2 (port : PortNumbering G) (heven : ∀ v, Even (G.degree v)) :
    let π := stdPairing port heven
    (∀ e ∈ G.edgeSet, ∃! C, C ∈ π.circuits ∧ e ∈ C) ∧
    (∀ C ∈ π.circuits, ∃ d : G.Dart,
      (π.circuitWalk d).IsCircuit ∧ π.Follows (π.circuitWalk d) ∧
        (π.circuitWalk d).edges.toFinset = C) ∧
    (∀ (u : V) (w : G.Walk u u), w.IsCircuit → π.Follows w → w.edges.toFinset ∈ π.circuits) :=
  (stdPairing port heven).pairing_circuit_decomposition

end Podc.ContentObliviousEulerian
