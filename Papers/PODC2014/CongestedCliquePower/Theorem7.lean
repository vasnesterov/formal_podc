import Papers.PODC2014.CongestedCliquePower.Sketch
import Papers.PODC2014.CongestedCliquePower.Lemma13

/-!
# Theorem 7: `H`-detection in CLIQUE-BCAST in `O(ex(n, H) log n / (n b))` rounds

Drucker–Kuhn–Oshman, PODC 2014, Theorem 7: for every fixed `H`, `H`-subgraph detection can be
solved in CLIQUE-BCAST_{n,b} in `O(ex(n, H)/n · log n / b)` rounds.

Algorithm (paper: Claim 6 + the one-round reconstruction algorithm of Becker et al. [2], whose
`O(k log n)`-bit messages are cut into `b`-bit chunks). With `k = ⌊4 ex(n, H)/n⌋`, every node
broadcasts its degree and the `𝔽₂`-sketch of its neighbourhood (`Sketch.lean`), in total
`L = ⌈log₂(n+1)⌉ + 2k⌈log₂(n+1)⌉ + 1` bits, in `⌈L/b⌉` rounds (`Bcast.oneShot`). Then every node
checks whether some `k`-degenerate graph has these degrees and sketches. If yes, it is the input
graph (`eq_of_sketch`) and the node answers whether it is `H`-free; if not, the input graph is not
`k`-degenerate, hence contains `H` by Claim 6.

As Claim 6, the theorem is proved for connected `H` with at least one edge.
-/

namespace Podc.CongestedCliquePower

open SimpleGraph Finset Cslib.CongestedClique

variable {W : Type} {H : SimpleGraph W}

/-- The degeneracy bound `k = ⌊4 ex(n, H) / n⌋` of Claim 6. -/
noncomputable def degBound (H : SimpleGraph W) (n : ℕ) : ℕ := 4 * extremalNumber n H / n

/-- Sketch length `m = 2k⌈log₂(n+1)⌉ + 1`. -/
noncomputable def sketchLen (H : SimpleGraph W) (n : ℕ) : ℕ := 2 * degBound H n * Nat.clog 2 (n + 1) + 1

/-- Message length `L = ⌈log₂(n+1)⌉ + m` (degree and sketch). -/
noncomputable def msgLen (H : SimpleGraph W) (n : ℕ) : ℕ := Nat.clog 2 (n + 1) + sketchLen H n

lemma pow_lt_two_pow_sketchLen (n : ℕ) :
    (n + 1) ^ (2 * degBound H n) < 2 ^ sketchLen H n := by
  have h1 : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) := Nat.le_pow_clog (by norm_num) _
  calc (n + 1) ^ (2 * degBound H n) ≤ (2 ^ Nat.clog 2 (n + 1)) ^ (2 * degBound H n) :=
        Nat.pow_le_pow_left h1 _
    _ = 2 ^ (2 * degBound H n * Nat.clog 2 (n + 1)) := by rw [← pow_mul, mul_comm]
    _ < 2 ^ sketchLen H n := Nat.pow_lt_pow_right (by norm_num) (by simp [sketchLen])

variable (H) (V : Type) [Fintype V] [DecidableEq V]

/-- The data broadcast by a node: its degree and the sketch of its neighbourhood. -/
abbrev Data := Fin (Fintype.card V + 1) × (Fin (sketchLen H (Fintype.card V)) → ZMod 2)

omit [DecidableEq V] in
lemma card_data_le :
    Fintype.card (Data H V) ≤ Fintype.card (Fin (msgLen H (Fintype.card V)) → Bool) := by
  simp only [Data, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, ZMod.card,
    Fintype.card_bool]
  rw [msgLen, pow_add]
  exact Nat.mul_le_mul_right _ (Nat.le_pow_clog (b := 2) (by norm_num) _)

/-- An injective encoding of the data into `L` bits. -/
noncomputable def enc : Data H V ↪ (Fin (msgLen H (Fintype.card V)) → Bool) :=
  (Function.Embedding.nonempty_of_card_le (card_data_le H V)).some

/-- A sketch matrix as in `exists_independent`. -/
noncomputable def sketchMatrix : V → Fin (sketchLen H (Fintype.card V)) → ZMod 2 :=
  (exists_independent (V := V) (degBound H (Fintype.card V))
    (pow_lt_two_pow_sketchLen (Fintype.card V))).choose

lemma sketchMatrix_independent :
    Independent (sketchMatrix H V) (degBound H (Fintype.card V)) :=
  (exists_independent (V := V) (degBound H (Fintype.card V))
    (pow_lt_two_pow_sketchLen (Fintype.card V))).choose_spec

/-- The data of a node whose neighbourhood row is `r`: degree and sketch of the neighbourhood. -/
noncomputable def rowData (r : V → Bool) : Data H V :=
  (⟨(univ.filter fun w => r w = true).card, Nat.lt_succ_of_le (card_le_univ _)⟩,
    sketch (sketchMatrix H V) (univ.filter fun w => r w = true))

/-- The message of a node with neighbourhood row `r`. -/
noncomputable def thm7Msg (_ : V) (r : V → Bool) : Fin (msgLen H (Fintype.card V)) → Bool :=
  enc H V (rowData H V r)

/-- `G₂` is `k`-degenerate and has the degrees and sketches `d`. -/
def Matches (d : V → Data H V) (G₂ : SimpleGraph V) : Prop := by
  classical exact IsDegenerate G₂ (degBound H (Fintype.card V)) ∧
    ∀ w, rowData H V (adjInput G₂ w) = d w

/-- The decision of every node: if some `k`-degenerate graph matches the decoded data, answer
whether it is `H`-free; otherwise reject. -/
noncomputable def thm7Dec (_ : V) (_ : V → Bool) (ms : V → Fin (msgLen H (Fintype.card V)) → Bool) :
    Bool := by
  classical
  exact if h : ∃ G₂, Matches H V (fun w => Function.invFun (enc H V) (ms w)) G₂ then
    decide (H.Free h.choose) else false

/-- The algorithm of Theorem 7. -/
noncomputable def thm7Alg (b : ℕ) :=
  Bcast.Algorithm.oneShot (msgLen H (Fintype.card V)) b (thm7Msg H V) (thm7Dec H V)

/-- The number of rounds of Theorem 7: `⌈L / b⌉`. -/
noncomputable def thm7Rounds (b : ℕ) : ℕ := (msgLen H (Fintype.card V) + b - 1) / b

lemma rowData_adjInput (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    rowData H V (adjInput G v) =
      (⟨G.degree v, Nat.lt_succ_of_le (G.degree_lt_card_verts v).le⟩,
        sketch (sketchMatrix H V) (G.neighborFinset v)) := by
  have : (univ.filter fun w => adjInput G v w = true) = G.neighborFinset v := by
    ext w; simp [adjInput]
  simp only [rowData, this, card_neighborFinset_eq_degree]

/-- **Theorem 7** (for connected `H` with an edge). For `b ≥ 1`, the CLIQUE-BCAST_{n,b} algorithm
`thm7Alg` decides in `⌈L / b⌉` rounds whether the input graph is `H`-free, where
`L = ⌈log₂(n+1)⌉ + 2k⌈log₂(n+1)⌉ + 1` and `k = ⌊4 ex(n, H) / n⌋`; i.e. in
`O(ex(n, H)/n · log n / b + 1)` rounds. -/
theorem theorem_7 (hH : H.Connected) (hbot : H ≠ ⊥) (b : ℕ) (hb : 0 < b) (G : SimpleGraph V) :
    (thm7Alg H V b).Accepts (adjInput G) (thm7Rounds H V b) ↔ H.Free G := by
  classical
  have hT : msgLen H (Fintype.card V) ≤ thm7Rounds H V b * b := by
    unfold thm7Rounds
    have := Nat.div_add_mod (msgLen H (Fintype.card V) + b - 1) b
    have := Nat.mod_lt (msgLen H (Fintype.card V) + b - 1) hb
    rw [Nat.mul_comm]
    omega
  rw [thm7Alg, Bcast.Algorithm.oneShot_accepts _ _ _ _ _ _ hT]
  have hdec : (fun w => Function.invFun (enc H V) (thm7Msg H V w (adjInput G w))) =
      fun w => rowData H V (adjInput G w) := by
    funext w
    exact Function.leftInverse_invFun (enc H V).injective _
  have hM := sketchMatrix_independent H V
  -- matching graphs coincide with `G`
  have huniq : ∀ G₂, Matches H V (fun w => rowData H V (adjInput G w)) G₂ → G₂ = G := by
    intro G₂ ⟨hdeg, hd⟩
    refine eq_of_sketch hM G₂ G hdeg (fun v => ?_) (fun v => ?_)
    · have := congrArg (fun d : Data H V => (d.1 : ℕ)) (hd v)
      simpa [rowData_adjInput] using this
    · have := congrArg Prod.snd (hd v)
      simpa [rowData_adjInput] using this
  simp only [thm7Dec, hdec]
  by_cases hex : ∃ G₂, Matches H V (fun w => rowData H V (adjInput G w)) G₂
  · have e := huniq _ hex.choose_spec
    simp only [hex, ↓reduceDIte, e, decide_eq_true_eq]
    constructor
    · intro h
      by_cases hV : Nonempty V
      · obtain ⟨v⟩ := hV
        exact h v
      · intro hc
        obtain ⟨f⟩ := hc
        obtain ⟨a, b, hab⟩ : ∃ a b, H.Adj a b := by
          by_contra hno
          push Not at hno
          exact hbot (by ext a b; simpa using hno a b)
        exact hV ⟨f a⟩
    · intro h _
      exact h
  · simp only [hex, dite_false, Bool.false_eq_true]
    constructor
    · intro h
      by_cases hV : Nonempty V
      · obtain ⟨v⟩ := hV; exact absurd (h v) id
      · exact absurd ⟨G, by
          refine ⟨fun s hs => absurd ⟨hs.choose⟩ hV, fun w => rfl⟩⟩ hex
    · intro hfree
      exact absurd ⟨G, claim_6_isDegenerate hH hbot G hfree, fun w => rfl⟩ hex

omit [DecidableEq V] in
/-- The round count of Theorem 7 in closed form: `⌈L / b⌉ · b < L + b` with
`L = (2k + 1)⌈log₂(n+1)⌉ + 1`, `k = ⌊4 ex(n, H)/n⌋`. -/
lemma thm7Rounds_mul_le (b : ℕ) (hb : 0 < b) :
    thm7Rounds H V b * b ≤ (2 * degBound H (Fintype.card V) + 1) *
      Nat.clog 2 (Fintype.card V + 1) + b := by
  unfold thm7Rounds msgLen sketchLen
  have := Nat.div_mul_le_self (Nat.clog 2 (Fintype.card V + 1) +
    (2 * degBound H (Fintype.card V) * Nat.clog 2 (Fintype.card V + 1) + 1) + b - 1) b
  have e : (2 * degBound H (Fintype.card V) + 1) * Nat.clog 2 (Fintype.card V + 1) =
      2 * degBound H (Fintype.card V) * Nat.clog 2 (Fintype.card V + 1) +
        Nat.clog 2 (Fintype.card V + 1) := by ring
  omega

end Podc.CongestedCliquePower
