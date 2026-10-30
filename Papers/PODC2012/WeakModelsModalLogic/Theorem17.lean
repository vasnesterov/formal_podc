import Papers.PODC2012.WeakModelsModalLogic.Fig9a

/-!
# Theorem 17 and Corollary 18 of Hella et al.: `VVc(1) ⊄ VV`

The class `𝒢` (`InClassG`): connected `k`-regular graphs with `k` odd and without a 1-factor.
The problem `Π` (`thm17Problem`): on `G ∈ 𝒢` output a non-constant `S : V → Bool`; on other
graphs anything goes.

* `thm17_mem : Π ∈ VVc(1)`: a two-round algorithm (`thm17Machine`). In round 1 every node sends
  `j` to its port `j`, so node `v` learns, for each of its ports `i`, the port number of the
  neighbour that its port `i` is connected to; this list is the *local type* `t(v)`
  (`thm17Type`, encoded as a natural number). In round 2 every node sends its type to all
  neighbours and outputs `true` iff no neighbour has a larger type. On `G ∈ 𝒢` with a consistent
  port numbering, if all types were equal then all nodes would be bisimilar in `K_{+,+}(G, p)`
  and Lemma 16 would give a 1-factor; so by connectivity some edge joins nodes of different
  types (the smaller one outputs `false`), and a node of maximum type outputs `true`.
* `thm17_not_mem : Π ∉ VV`: Lemma 15 on the graph of Figure 9a and Corollary 3 (a).
* `theorem17`, `corollary18`.
-/

namespace Podc.WeakModelsModalLogic

open Function

/-- The class `𝒢` of the paper: connected regular graphs of odd degree without a 1-factor. -/
def InClassG {V : Type*} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ (∃ k, Odd k ∧ ∀ v, deg G v = k) ∧ ¬ ∃ M : G.Subgraph, M.IsPerfectMatching

/-- The graph problem `Π` of Theorem 17: on `G ∈ 𝒢` the solutions are the non-constant
functions `V → {0, 1}`; on all other graphs every function is a solution. -/
def thm17Problem : GraphProblem Bool := fun _ G => {S | InClassG G → ∃ u v, S u ≠ S v}

/-- The graph of Figure 9a is in `𝒢`. -/
theorem fig9a_inClassG : InClassG fig9a :=
  ⟨fig9a_connected, ⟨3, by decide, fig9a_regular⟩, fig9a_no_perfectMatching⟩

/-! ### The algorithm -/

/-- Intermediate states of the algorithm of Theorem 17. -/
inductive Thm17State
  /-- Before round 1; remembers the degree. -/
  | start (d : ℕ)
  /-- Before round 2; remembers the (encoded) local type. -/
  | typed (t : ℕ)

/-- The two-round algorithm of Theorem 17 for degree bound `Δ`. Messages are `Option ℕ`
(`none` is the empty message). -/
def thm17Machine (Δ : ℕ) : Machine Δ Bool where
  Z := Thm17State
  M := Option ℕ
  m0 := none
  z0 d := .inr (.start d)
  μ z j := match z with
    | .start _ => some j
    | .typed t => some t
  δ z a := match z with
    | .start d => .inr (.typed (Encodable.encode ((List.ofFn a).take d)))
    | .typed t => .inl (decide (∀ i, (a i).all (fun s => decide (s ≤ t)) = true))

instance (Δ : ℕ) : Encodable (thm17Machine Δ).M := inferInstanceAs (Encodable (Option ℕ))

/-- The algorithm of Theorem 17. -/
def thm17Alg : Algorithm Bool := thm17Machine

section Execution

variable {Δ : ℕ} {V : Type*} {G : SimpleGraph V} (P : PortNumbering G)

/-- The (encoded) local type of `v` computed in round 1: the list of port numbers received on
the ports `0, …, deg v - 1`. -/
noncomputable def thm17Type (v : V) : ℕ :=
  Encodable.encode ((List.ofFn ((thm17Machine Δ).recv G P ((thm17Machine Δ).init G) v)).take
    (deg G v))

/-- The output of `v`. -/
noncomputable def thm17Out (v : V) : Bool :=
  decide (∀ i, ((thm17Machine Δ).recv G P ((thm17Machine Δ).state G P 1) v i).all
    (fun s => decide (s ≤ thm17Type (Δ := Δ) P v)) = true)

theorem thm17_state_one (v : V) :
    (thm17Machine Δ).state G P 1 v = .inr (.typed (thm17Type (Δ := Δ) P v)) := by
  rw [Machine.state_succ, Machine.state_zero]
  rfl

theorem thm17_state_two (v : V) :
    (thm17Machine Δ).state G P 2 v = .inl (thm17Out (Δ := Δ) P v) := by
  rw [Machine.state_succ]
  simp only [Machine.step, thm17_state_one]
  rfl

theorem thm17_recv_init (v : V) (i : Fin Δ) (hi : (i : ℕ) < deg G v) :
    (thm17Machine Δ).recv G P ((thm17Machine Δ).init G) v i =
      some ((P.p.symm ⟨v, ⟨i, hi⟩⟩).2 : ℕ) := by
  simp only [Machine.recv, hi, dite_true]
  rfl

theorem thm17_recv_one (v : V) (i : Fin Δ) (hi : (i : ℕ) < deg G v) :
    (thm17Machine Δ).recv G P ((thm17Machine Δ).state G P 1) v i =
      some (thm17Type (Δ := Δ) P (P.p.symm ⟨v, ⟨i, hi⟩⟩).1) := by
  simp only [Machine.recv, hi, dite_true, thm17_state_one]
  rfl

theorem thm17Type_length (hG : MaxDegLE G Δ) (v : V) :
    ((List.ofFn ((thm17Machine Δ).recv G P ((thm17Machine Δ).init G) v)).take
      (deg G v)).length = deg G v := by
  simp [hG v]

/-- Equal local types: equal degrees and equal remote port numbers. -/
theorem thm17Type_eq (hG : MaxDegLE G Δ) {v v' : V}
    (h : thm17Type (Δ := Δ) P v = thm17Type (Δ := Δ) P v') :
    deg G v = deg G v' ∧ ∀ i (hv : i < deg G v) (hv' : i < deg G v'),
      ((P.p.symm ⟨v, ⟨i, hv⟩⟩).2 : ℕ) = (P.p.symm ⟨v', ⟨i, hv'⟩⟩).2 := by
  have hL := Encodable.encode_injective h
  have hlen := congrArg List.length hL
  rw [thm17Type_length P hG, thm17Type_length P hG] at hlen
  refine ⟨hlen, fun i hv hv' => ?_⟩
  have hiΔ : i < Δ := lt_of_lt_of_le hv (hG v)
  have := congrArg (fun l => l[i]?) hL
  simp only [List.getElem?_take, hv, hv', ite_true, List.getElem?_ofFn, hiΔ, dite_true] at this
  rw [thm17_recv_init P v ⟨i, hiΔ⟩ hv, thm17_recv_init P v' ⟨i, hiΔ⟩ hv'] at this
  exact Option.some.inj (Option.some.inj this)

/-- If all local types are equal, all nodes are bisimilar in `K_{+,+}(G, p)`. -/
theorem thm17_bisim_of_types_eq (hG : MaxDegLE G Δ)
    (h : ∀ v v', thm17Type (Δ := Δ) P v = thm17Type (Δ := Δ) P v') :
    P.IsBisimPP (fun _ _ => True) := by
  have key : ∀ v v' i j w, P.R i j v w → ∃ w', P.R i j v' w' := by
    intro v v' i j w hR
    obtain ⟨hdeg, hport⟩ := thm17Type_eq P hG (h v v')
    obtain ⟨hi, -, hj⟩ := (P.R_iff _ _ _ _).1 hR
    have hi' : i < deg G v' := hdeg ▸ hi
    exact ⟨_, (P.R_iff _ _ _ _).2 ⟨hi', rfl, (hport i hi hi').symm.trans hj⟩⟩
  intro v v' _
  refine ⟨(thm17Type_eq P hG (h v v')).1, fun i j w hR => ?_, fun i j w' hR => ?_⟩
  · obtain ⟨w', hw'⟩ := key v v' i j w hR
    exact ⟨w', hw', trivial⟩
  · obtain ⟨w, hw⟩ := key v' v i j w' hR
    exact ⟨w, hw, trivial⟩

/-- The output of `v` is `true` iff no neighbour of `v` has a larger local type. -/
theorem thm17Out_iff (hG : MaxDegLE G Δ) (v : V) :
    thm17Out (Δ := Δ) P v = true ↔
      ∀ w, G.Adj v w → thm17Type (Δ := Δ) P w ≤ thm17Type (Δ := Δ) P v := by
  simp only [thm17Out, decide_eq_true_eq]
  constructor
  · intro h w hw
    obtain ⟨i, rfl⟩ := P.inNbr_surj v w hw
    have := h ⟨i, lt_of_lt_of_le i.2 (hG v)⟩
    rw [thm17_recv_one (Δ := Δ) P v ⟨i, _⟩ i.2] at this
    simpa [PortNumbering.inNbr] using this
  · intro h i
    by_cases hi : (i : ℕ) < deg G v
    · rw [thm17_recv_one P v i hi]
      simpa [PortNumbering.inNbr] using h _ (P.adj_inNbr v ⟨i, hi⟩)
    · rw [Machine.recv_eq_m0 _ P _ i hi]
      rfl

end Execution

/-- On a connected graph, a function that is constant along edges is constant. -/
theorem eq_of_connected {V : Type*} {G : SimpleGraph V} (hG : G.Connected) {β : Type*}
    (f : V → β) (hf : ∀ u w, G.Adj u w → f u = f w) (u v : V) : f u = f v := by
  obtain ⟨p⟩ := hG.preconnected u v
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hf _ _ h).trans ih

/-- `Π ∈ VVc(1)`: the algorithm `thm17Alg` solves `Π` in time `2` assuming consistency. -/
theorem thm17_mem : thm17Problem ∈ VVc1 Bool := by
  refine ⟨thm17Alg, fun _ => 2, fun Δ V _ G hG P hc => ?_⟩
  refine ⟨thm17Out (Δ := Δ) P, fun v => thm17_state_two P v, fun hG𝒢 => ?_⟩
  obtain ⟨hconn, ⟨k, hodd, hk⟩, hnpm⟩ := hG𝒢
  set t := thm17Type (Δ := Δ) P
  -- Not all local types are equal (Lemma 16).
  have hne : ¬ ∀ v v', t v = t v' := by
    intro h
    exact hnpm (lemma16 G k hodd hk P hc fun u v =>
      ⟨_, thm17_bisim_of_types_eq P hG h, trivial⟩)
  -- Hence some edge joins nodes of different types.
  obtain ⟨u, w, huw, htuw⟩ : ∃ u w, G.Adj u w ∧ t u < t w := by
    by_contra h
    push Not at h
    exact hne (eq_of_connected hconn t fun u w huw =>
      le_antisymm (h w u huw.symm) (h u w huw))
  have hu : thm17Out (Δ := Δ) P u = false := by
    by_contra h'
    rw [Bool.not_eq_false, thm17Out_iff P hG] at h'
    exact absurd (h' w huw) (not_le.2 htuw)
  -- A node of maximum type outputs `true`.
  have := hconn.nonempty
  obtain ⟨x, hx⟩ := Finite.exists_max t
  have hxo : thm17Out (Δ := Δ) P x = true := (thm17Out_iff P hG x).2 fun w _ => hx w
  exact ⟨x, u, by rw [hxo, hu]; decide⟩

/-- `Π ∉ VV`: Lemma 15 on the graph of Figure 9a and Corollary 3 (a) with `X = V`. -/
theorem thm17_not_mem : thm17Problem ∉ VV Bool := by
  obtain ⟨P, hP⟩ := lemma15 fig9a 3 fig9a_regular
  refine cor3a fig9a 3 (fun v => (fig9a_regular v).le) Set.univ thm17Problem
    (fun S hS => ?_) P (fun u _ v _ => hP u v)
  obtain ⟨u, v, h⟩ := hS fig9a_inClassG
  exact ⟨u, trivial, v, trivial, h⟩

/-- Theorem 17 of [Hella et al.]. There is a graph problem `Π` with `Π ∈ VVc(1)` and
`Π ∉ VV`. -/
theorem theorem17 : ∃ Pr : GraphProblem Bool, Pr ∈ VVc1 Bool ∧ Pr ∉ VV Bool :=
  ⟨thm17Problem, thm17_mem, thm17_not_mem⟩

/-- Corollary 18 of [Hella et al.]. `VVc ≠ VV` and `VVc(1) ≠ VV(1)`. -/
theorem corollary18 : VVc Bool ≠ VV Bool ∧ VVc1 Bool ≠ VV1 Bool := by
  obtain ⟨Pr, h1, h2⟩ := theorem17
  refine ⟨fun h => h2 (h ▸ VVc1_subset_VVc h1), fun h => h2 ?_⟩
  exact VV1_subset_VV (h ▸ h1)

end Podc.WeakModelsModalLogic
