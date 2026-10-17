import Papers.PODC2026.SinklessOrientation.MinIdRun
import Papers.PODC2026.SinklessOrientation.Lemma22
import Papers.PODC2026.SinklessOrientation.Reorient

/-!
# Theorem 1.1 (deterministic part) of [Nolin, PODC'26]

Algorithm 1: with `c = ⌈log_{δ-1} n⌉`, `k = 4c`,

1. compute the `k`-sinksparse orientation of Theorem 2.1 (`minIdOrientation`);
2.–3. every `δ`-sink repairs its distance-`k/2` ball (Algorithm 2, `repairOrientation`).

## Main results

* `lemma_2_3` (**Lemma 2.3**, as stated in the paper: hypothesis "a node of degree `< δ` or a
  cycle in the distance-`k/2` neighbourhood of every `δ`-sink").
* `sinklessAlg_noDeltaSink`, `sinklessAlg_isLocal`, `theorem_1_1` (**Theorem 1.1**,
  deterministic part): for every `δ ≥ 3`, `sinklessAlg` produces on every graph an orientation
  without `δ`-sinks, and it is a deterministic LOCAL algorithm with `8⌈log_{δ-1} n⌉ + 2 ≤
  16⌈log_δ n⌉ + 2 = O(log_δ n)` rounds.
* `no_orientation_in_and_out_single_edge`: a remark on Section 3 — read literally for arbitrary
  graphs, "max(ε deg(v), 1) incoming and outgoing edges for every node" fails at degree-1 nodes
  (the paper works with minimum degree `δ ≥ 3`).

The randomized part of Theorem 1.1 and Corollary 1.2 rely on external results (shattering of
Ghaffari–Su, degree-splitting reductions) and are not formalized; CONGEST message sizes are only
discussed in docstrings (see `README.md` and `differencies.md`).
-/

namespace SinklessOrientation

open SimpleGraph

variable {V : Type*}

/-! ### Lemma 2.3 with the cycle hypothesis -/

lemma ntSet_nonempty_of_hasBackEdges {G : SimpleGraph V} {s : V} {h : ℕ}
    (hb : HasBackEdges G s h) : (ntSet G h s).Nonempty := by
  obtain ⟨x, y, y', hx, hxy, hxy', hne, hy, hy'⟩ := hb
  have hdy : ∀ z, G.edist s z ≤ G.edist s x → G.dist s z ≤ G.dist s x := by
    intro z hle
    simp only [SimpleGraph.dist]
    exact ENat.toNat_le_toNat hle (edist_ne_top_of_le_natCast hx)
  by_cases hpy : y = par G s x
  · exact ⟨(x, y'), hx, hxy', hdy y' hy', fun e => hne (hpy.trans e.symm)⟩
  · exact ⟨(x, y), hx, hxy, hdy y hy, hpy⟩

lemma containsCycle_mono {G : SimpleGraph V} {S S' : Set V} (hS : S ⊆ S')
    (h : ContainsCycle G S) : ContainsCycle G S' := by
  obtain ⟨x, c, hc, hsup⟩ := h
  exact ⟨x, c, hc, fun y hy => hS (hsup y hy)⟩

/-- **Lemma 2.3** of [Nolin, PODC'26]: given a `k`-sinksparse orientation in which every `δ`-sink
has a node of degree `< δ` or a cycle in its distance-`k/2` neighbourhood, Algorithm 2 transforms
it into an orientation without `δ`-sinks, changing only edges inside the distance-`k/2` balls of
the `δ`-sinks. Its round complexity, `2⌊k/2⌋ + 1 = O(k)` LOCAL rounds, is
`repairOrientation_isLocal`. -/
theorem lemma_2_3 {G : SimpleGraph V} {δ k : ℕ} (o : Orientation G) (hsp : o.IsSinkSparse k)
    (hgood : ∀ s, o.IsDeltaSink δ s →
      (∃ t ∈ cball G s (k / 2), deg G t < δ) ∨ ContainsCycle G (cball G s (k / 2))) :
    (repairOrientation δ (k / 2) o).NoDeltaSink δ ∧
      ∀ a b, ((repairOrientation δ (k / 2) o).out a b ↔ o.out a b) ∨
        ∃ s, o.IsDeltaSink δ s ∧ a ∈ cball G s (k / 2) ∧ b ∈ cball G s (k / 2) := by
  have key := lemma_2_3_core (h := k / 2) (sep_of_isSinkSparse (by omega) hsp) fun s hs => by
    rcases hgood s hs with ⟨t, ht, hdeg⟩ | hc
    · exact Or.inl ⟨t, mem_cball.1 ht, hdeg⟩
    · exact Or.inr (ntSet_nonempty_of_hasBackEdges (hasBackEdges_of_containsCycle hc))
  exact ⟨key.1, fun a b => (key.2 a b).imp_right fun ⟨s, hs, ha, hb⟩ =>
    ⟨s, hs, mem_cball.2 ha, mem_cball.2 hb⟩⟩

/-! ### Algorithm 1 -/

lemma IsLocal.mono {A : ∀ G : SimpleGraph V, Orientation G} {R R' : ℕ} (hA : IsLocal A R)
    (h : R ≤ R') : IsLocal A R' :=
  fun G G' u hG => hA G G' u (hG.mono_radius h)


section Algorithm

variable [Fintype V]

variable (V) in
/-- `⌈log_{δ-1} n⌉` for `n = |V|`. -/
noncomputable def logParam (δ : ℕ) : ℕ := Nat.clog (δ - 1) (Fintype.card V)

/-- **Algorithm 1** of [Nolin, PODC'26]: the `4⌈log_{δ-1} n⌉`-sinksparse orientation of Theorem 2.1,
followed by the repairs of Algorithm 2 within distance `2⌈log_{δ-1} n⌉` of every `δ`-sink. The
identifiers are `id : V → ℕ` (injective); `n = |V|` is known to all nodes. -/
noncomputable def sinklessAlg (id : V → ℕ) (hid : Function.Injective id) (δ : ℕ)
    (G : SimpleGraph V) : Orientation G :=
  repairOrientation δ (2 * logParam V δ) (minIdOrientation G id (4 * logParam V δ) hid)

variable {id : V → ℕ} (hid : Function.Injective id) {δ : ℕ}

/-- Correctness of Algorithm 1: no `δ`-sinks, for every graph on `V`. -/
theorem sinklessAlg_noDeltaSink (hδ : 3 ≤ δ) (G : SimpleGraph V) :
    (sinklessAlg id hid δ G).NoDeltaSink δ := by
  set c := logParam V δ
  refine (lemma_2_3_core (sep_of_isSinkSparse (k := 4 * c) (by omega)
    (minIdOrientation_isSinkSparse hid)) fun s _ => ?_).1
  rcases lemma_2_2_clog G hδ s with ⟨t, ht, hdeg⟩ | hc
  · exact Or.inl ⟨t, mem_cball.1 (closedBall_mono
      (Nat.cast_le.2 (by simp only [logParam]; omega)) ht), hdeg⟩
  · exact Or.inr (ntSet_nonempty_of_hasBackEdges (hasBackEdges_of_containsCycle
      (containsCycle_mono (closedBall_mono (Nat.cast_le.2 (by simp only [logParam]; omega))) hc)))

/-- Round complexity of Algorithm 1: `8⌈log_{δ-1} n⌉ + 2` LOCAL rounds. -/
theorem sinklessAlg_isLocal : IsLocal (sinklessAlg id hid δ) (8 * logParam V δ + 2) := by
  have := (minIdOrientation_isLocal (k := 4 * logParam V δ) hid).comp
    (repairOrientation_isLocal (δ := δ) (h := 2 * logParam V δ))
  exact this.mono (by omega)

lemma clog_pred_le (hδ : 3 ≤ δ) (n : ℕ) : Nat.clog (δ - 1) n ≤ 2 * Nat.clog δ n := by
  apply Nat.clog_le_of_le_pow
  have h1 : δ ≤ (δ - 1) ^ 2 := by
    obtain ⟨d, rfl⟩ : ∃ d, δ = d + 3 := ⟨δ - 3, by omega⟩
    simp only [show d + 3 - 1 = d + 2 by omega]; nlinarith
  calc n ≤ δ ^ Nat.clog δ n := Nat.le_pow_clog (by omega) n
    _ ≤ ((δ - 1) ^ 2) ^ Nat.clog δ n := Nat.pow_le_pow_left h1 _
    _ = (δ - 1) ^ (2 * Nat.clog δ n) := by rw [← pow_mul]

/-- **Theorem 1.1** of [Nolin, PODC'26], deterministic part: for every `δ ≥ 3` there is a
deterministic LOCAL algorithm computing an orientation without `δ`-sinks in
`16⌈log_δ n⌉ + 2 = O(log_δ n)` rounds on `n`-node graphs with unique identifiers. -/
theorem theorem_1_1 (hδ : 3 ≤ δ) :
    (∀ G : SimpleGraph V, (sinklessAlg id hid δ G).NoDeltaSink δ) ∧
      IsLocal (sinklessAlg id hid δ) (16 * Nat.clog δ (Fintype.card V) + 2) :=
  ⟨sinklessAlg_noDeltaSink hid hδ, (sinklessAlg_isLocal hid).mono (by
    have := clog_pred_le hδ (Fintype.card V); unfold logParam; omega)⟩

end Algorithm

/-! ### Section 3: in- and outgoing edges for every node -/

/-- Section 3 of the paper mentions orientations where "every node `v` [has] at least
`max(ε deg(v), 1)` outgoing edges and `max(ε deg(v), 1)` incoming edges". The paper works with
graphs of minimum degree `δ ≥ 3`; this remark only shows that the literal phrasing cannot be
extended to arbitrary graphs (a single edge). Corollary 1.2 itself (`⌊ε deg(v)⌋`) and the
"sinkless and sourceless for nodes of degree `≥ δ`" variant are unaffected. -/
theorem no_orientation_in_and_out_single_edge :
    ¬ ∃ o : Orientation (⊤ : SimpleGraph (Fin 2)), ∀ v, (∃ u, o.out v u) ∧ (∃ u, o.out u v) := by
  rintro ⟨o, ho⟩
  obtain ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ := ho 0
  have hu1 : u = 1 := by
    have := (o.adj_of_out hu).ne; revert this; fin_cases u <;> simp
  have hw1 : w = 1 := by
    have := (o.adj_of_out hw).ne; revert this; fin_cases w <;> simp
  subst hu1; subst hw1
  exact o.not_out_of_out hu hw

end SinklessOrientation
