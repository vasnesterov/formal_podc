import Papers.PODC2016.AnalysingSI.Model

/-!
# Dependency-graph characterisation of SI (Cerone–Gotsman, PODC 2016, §4)

* Proposition 7 / 23: `graph(X)` is a dependency graph.
* Proposition 14: anti-dependencies in terms of visibility.
* Lemma 12: `VIS ; RW ⊆ CO` in SI executions.
* Lemma 13: acyclic solutions of the system of Figure 3 give pre-executions in `PreExecSI`.
* **Theorem 10** (soundness and completeness) and **Theorem 9** (`HistSI` = histories of graphs in
  `GraphSI`).
* Theorem 8 (serializability, Adya) and Theorem 21 (parallel SI), which the paper cites from
  earlier work, proved with the same machinery.
-/

namespace Podc.AnalysingSI

open Relation

variable {Obj V : Type*} [DecidableEq Obj] {τ : Type*}

namespace Txn

theorem Writes.unique {T : Txn Obj V} {x : Obj} {n m : V} (h : T.Writes x n) (h' : T.Writes x m) :
    n = m := by
  unfold Writes at h h'
  rw [h] at h'
  simpa using h'

theorem Reads.unique {T : Txn Obj V} {x : Obj} {n m : V} (h : T.Reads x n) (h' : T.Reads x m) :
    n = m := by
  unfold Reads at h h'
  rw [h] at h'
  simpa using h'

end Txn

namespace Execution

variable (X : Execution τ Obj V)

/-- **Proposition 23** of Cerone–Gotsman (generalising Proposition 7): for an execution satisfying
EXT, `graph(X)` is a dependency graph. -/
theorem isDepGraph_graph (hX : X.IsExecution) (hext : X.Ext) : X.graph.IsDepGraph := by
  obtain ⟨⟨hvc, htr, hirr⟩, htot⟩ := hX
  constructor
  · rintro T S x ⟨⟨n, hn⟩, hmax⟩
    obtain ⟨M, hM, hMw⟩ := hext S x n hn
    have := IsMaxBy.unique hirr htr hmax hM
    subst this
    refine ⟨n, ?_, hMw, hn⟩
    rintro rfl
    exact hirr _ (hvc _ _ hmax.1.1)
  · rintro S x ⟨n, hn⟩
    obtain ⟨M, hM, -⟩ := hext S x n hn
    exact ⟨M, ⟨n, hn⟩, hM⟩
  · rintro T T' S x ⟨-, h⟩ ⟨-, h'⟩
    exact IsMaxBy.unique hirr htr h h'
  · rintro x T S ⟨-, hT, hS⟩
    exact ⟨hT, hS⟩
  · rintro x T S U ⟨h1, hT, -⟩ ⟨h2, -, hU⟩
    exact ⟨htr _ _ _ h1 h2, hT, hU⟩
  · rintro x T ⟨h, -⟩
    exact hirr _ h
  · intro x T S hT hS hne
    rcases htot T S hne with h | h
    · exact Or.inl ⟨h, hT, hS⟩
    · exact Or.inr ⟨h, hS, hT⟩

/-- **Proposition 7** of Cerone–Gotsman: for `X ∈ ExecSI`, `graph(X)` is a dependency graph. -/
theorem prop7 (hX : X.IsSI) : X.graph.IsDepGraph :=
  X.isDepGraph_graph hX.1 hX.2.2.1

/-- The "⇒" half of Proposition 14, valid in every pre-execution: an anti-dependency
`S —RW→ T` excludes `T —VIS→ S`. -/
theorem not_vis_of_rw (hX : X.IsPreExecution) {S T : τ} {x : Obj} (h : X.graph.RW x S T) :
    ¬ X.VIS T S := by
  obtain ⟨hvc, htr, hirr⟩ := hX
  obtain ⟨hne, T', ⟨-, hmax⟩, hco, -, hT⟩ := h
  intro hvis
  rcases hmax.2 T ⟨hvis, hT⟩ with rfl | h
  · exact hirr _ hco
  · exact hirr _ (htr _ _ _ h hco)

/-- **Proposition 14** of Cerone–Gotsman. -/
theorem prop14 (hX : X.IsSI) (S T : τ) :
    X.graph.RWu S T ↔ S ≠ T ∧ ∃ x, X.ReadsObj x S ∧ X.WriteTx x T ∧ ¬ X.VIS T S := by
  obtain ⟨⟨⟨hvc, htr, hirr⟩, htot⟩, -, hext, -, hpre, -⟩ := hX
  constructor
  · rintro ⟨x, h⟩
    refine ⟨h.1, x, ?_, ?_, X.not_vis_of_rw ⟨hvc, htr, hirr⟩ h⟩
    · obtain ⟨-, T', ⟨hr, -⟩, -⟩ := h
      exact hr
    · obtain ⟨-, T', -, -, -, hT⟩ := h
      exact hT
  · rintro ⟨hne, x, ⟨n, hn⟩, hT, hnv⟩
    obtain ⟨T', hmax, -⟩ := hext S x n hn
    refine ⟨x, hne, T', ⟨⟨n, hn⟩, hmax⟩, ?_, hmax.1.2, hT⟩
    by_cases hTT : T' = T
    · subst hTT
      exact absurd hmax.1.1 hnv
    rcases htot _ _ hTT with h | h
    · exact h
    · exact absurd (hpre _ _ _ h hmax.1.1) hnv

/-- **Lemma 12** of Cerone–Gotsman: `VIS ; RW ⊆ CO` in every SI execution. -/
theorem lemma12 (hX : X.IsSI) {S' S T : τ} (h1 : X.VIS S' S) (h2 : X.graph.RWu S T) :
    X.CO S' T := by
  have hX' := hX
  obtain ⟨⟨⟨hvc, htr, hirr⟩, htot⟩, -, -, -, hpre, -⟩ := hX
  obtain ⟨-, x, -, -, hnv⟩ := (X.prop14 hX' S T).1 h2
  by_cases hT : T = S'
  · subst hT; exact absurd h1 hnv
  rcases htot _ _ hT with h | h
  · exact absurd (hpre _ _ _ h h1) hnv
  · exact h

end Execution

/-! ### From solutions of the system of Figure 3 to pre-executions -/

namespace DepGraph

variable (G : DepGraph τ Obj V)

/-- Common core of Lemma 13 and of the soundness halves of Theorems 8 and 21: if
`SO ∪ WR ∪ WW ⊆ VIS ⊆ CO`, `CO` is a strict partial order and `VIS ; RW` is irreflexive, then the
execution `(𝒯, SO, VIS, CO)` satisfies EXT and NOCONFLICT and has dependency graph `G`. -/
theorem ext_and_graph_eq (hG : G.IsDepGraph) {VIS CO : τ → τ → Prop}
    (hB : G.B ≤ VIS) (hvc : VIS ≤ CO) (htr : ∀ a b c, CO a b → CO b c → CO a c)
    (hirr : ∀ a, ¬ CO a a) (hvr : ∀ U S, VIS U S → ¬ G.RWu S U) :
    (Execution.mk G.toHistory VIS CO).Ext ∧ (Execution.mk G.toHistory VIS CO).NoConflict ∧
      (Execution.mk G.toHistory VIS CO).graph = G := by
  set X := Execution.mk G.toHistory VIS CO with hXdef
  have hWWco : ∀ x T S, G.WW x T S → CO T S :=
    fun x T S h => hvc _ _ (hB _ _ (Or.inr (Or.inr ⟨x, h⟩)))
  -- the read dependency source is the maximum
  have hmax : ∀ T S x, G.WR x T S →
      IsMaxBy CO (fun U => VIS U S ∧ G.WriteTx x U) T := by
    intro T S x hTS
    obtain ⟨n, hne, hw, hr⟩ := hG.wr_val T S x hTS
    refine ⟨⟨hB _ _ (Or.inr (Or.inl ⟨x, hTS⟩)), n, hw⟩, ?_⟩
    rintro U ⟨hUS, hU⟩
    by_cases hUT : U = T
    · exact Or.inl hUT
    rcases hG.ww_total x U T hU ⟨n, hw⟩ hUT with h | h
    · exact Or.inr (hWWco _ _ _ h)
    · exfalso
      refine hvr U S hUS ⟨x, ?_, T, hTS, h⟩
      rintro rfl
      exact hirr _ (hvc _ _ hUS)
  refine ⟨?_, ?_, ?_⟩
  · intro S x n hn
    obtain ⟨T, hT⟩ := hG.wr_exists S x ⟨n, hn⟩
    obtain ⟨m, -, hw, hr⟩ := hG.wr_val T S x hT
    have : m = n := Txn.Reads.unique hr hn
    subst this
    exact ⟨T, hmax T S x hT, hw⟩
  · intro T S x hT hS hne
    rcases hG.ww_total x T S hT hS hne with h | h
    · exact Or.inl (hB _ _ (Or.inr (Or.inr ⟨x, h⟩)))
    · exact Or.inr (hB _ _ (Or.inr (Or.inr ⟨x, h⟩)))
  · obtain ⟨H, WR, WW⟩ := G
    simp only [Execution.graph, DepGraph.mk.injEq, true_and, X]
    constructor
    · funext x T S
      apply propext
      constructor
      · rintro ⟨⟨n, hn⟩, hm⟩
        obtain ⟨T', hT'⟩ := hG.wr_exists S x ⟨n, hn⟩
        have := IsMaxBy.unique hirr htr hm (hmax T' S x hT')
        subst this
        exact hT'
      · intro h
        obtain ⟨n, -, -, hr⟩ := hG.wr_val T S x h
        exact ⟨⟨n, hr⟩, hmax T S x h⟩
    · funext x T S
      apply propext
      constructor
      · rintro ⟨hco, hT, hS⟩
        have hne : T ≠ S := by rintro rfl; exact hirr _ hco
        rcases hG.ww_total x T S hT hS hne with h | h
        · exact h
        · exact absurd (htr _ _ _ hco (hWWco _ _ _ h)) (hirr _)
      · intro h
        exact ⟨hWWco _ _ _ h, hG.ww_writeTx x T S h⟩

/-- **Lemma 13** of Cerone–Gotsman: if `G` is a dependency graph with `𝒯 ⊨ INT` and `(VIS, CO)` is
a solution of the system of Figure 3 with `CO` acyclic, then `P = (𝒯, SO, VIS, CO) ∈ PreExecSI`
and `graph(P) = G`. (The paper also assumes `VIS` acyclic; this follows from (S3).) -/
theorem lemma13 (hG : G.IsDepGraph) (hint : G.IntAll) {VIS CO : τ → τ → Prop}
    (hsol : IsSolution G.B G.RWu VIS CO) (hacyc : Acyclic CO) :
    (Execution.mk G.toHistory VIS CO).IsPreSI ∧ (Execution.mk G.toHistory VIS CO).graph = G := by
  have hirr : ∀ a, ¬ CO a a := fun a h => hacyc a (TransGen.single h)
  obtain ⟨hext, hnc, hgr⟩ := G.ext_and_graph_eq hG hsol.s1 hsol.s3 hsol.s4 hirr
    (fun U S hUS hSU => hirr U (hsol.s5 _ _ _ hUS hSU))
  exact ⟨⟨⟨hsol.s3, hsol.s4, hirr⟩, hint, hext,
    fun a b h => hsol.s1 _ _ (Or.inl h), hsol.s2, hnc⟩, hgr⟩

end DepGraph

/-! ### Theorem 10 and Theorem 9 -/

/-- **Theorem 10 (i)** of Cerone–Gotsman (soundness): every dependency graph in `GraphSI` is the
dependency graph of an execution in `ExecSI` with the same history. -/
theorem theorem10_soundness (G : DepGraph τ Obj V) (hG : G.IsSI) :
    ∃ VIS CO, (Execution.mk G.toHistory VIS CO).IsSI ∧
      (Execution.mk G.toHistory VIS CO).graph = G := by
  obtain ⟨hdg, hint, hacyc⟩ := hG
  -- the least solution `CO₀` (Lemma 15 with `R = ∅`) is acyclic
  set CO₀ := coSol G.B G.RWu (fun _ _ => False) with hCO₀
  have hgen : ∀ a b, genRel G.B G.RWu (fun _ _ => False) a b → Comp G.B (ReflGen G.RWu) a b := by
    rintro a b (h | h)
    · exact h
    · exact h.elim
  have htr₀ : ∀ a b c, CO₀ a b → CO₀ b c → CO₀ a c := fun _ _ _ h1 h2 => h1.trans h2
  have hirr₀ : ∀ a, ¬ CO₀ a a := fun a h => hacyc a (TransGen.mono hgen a a h)
  -- extend it to a strict total order `L` and take the least solution with `L ⊆ CO`
  obtain ⟨L, hCL, htrL, hirrL, htotL⟩ := exists_strictTotal_extension CO₀ htr₀ hirr₀
  have hsol := (isSolution_sol (B := G.B) (A := G.RWu) (R := L))
  have hCOL : coSol G.B G.RWu L ≤ L := by
    intro a b h
    refine transGen_of_trans htrL (TransGen.mono ?_ a b h)
    rintro c d (h' | h')
    · exact hCL _ _ (TransGen.single (Or.inl h'))
    · exact h'
  have hacycL : Acyclic (coSol G.B G.RWu L) :=
    acyclic_of_le hCOL (acyclic_of_trans_irrefl htrL hirrL)
  obtain ⟨⟨hpre, hrest⟩, hgr⟩ := G.lemma13 hdg hint hsol hacycL
  refine ⟨_, _, ⟨⟨hpre, ?_⟩, hrest⟩, hgr⟩
  intro a b hab
  rcases htotL a b hab with h | h
  · exact Or.inl (TransGen.single (Or.inr h))
  · exact Or.inr (TransGen.single (Or.inr h))

/-- `graph(X)`'s inequalities: an SI execution solves the system of Figure 3 for its own
dependencies (used in Theorem 10 (ii)). -/
theorem Execution.isSolution_of_isSI (X : Execution τ Obj V) (hX : X.IsSI) :
    IsSolution X.graph.B X.graph.RWu X.VIS X.CO := by
  have hX' := hX
  obtain ⟨⟨⟨hvc, htr, hirr⟩, htot⟩, -, -, hses, hpre, hnc⟩ := hX
  refine ⟨?_, hpre, hvc, htr, fun a b c h1 h2 => X.lemma12 hX' h1 h2⟩
  rintro a b (h | ⟨x, h⟩ | ⟨x, hco, ha, hb⟩)
  · exact hses _ _ h
  · exact h.2.1.1
  · have hne : a ≠ b := by rintro rfl; exact hirr _ hco
    rcases hnc a b x ha hb hne with h | h
    · exact h
    · exact absurd (htr _ _ _ hco (hvc _ _ h)) (hirr _)

/-- **Theorem 10 (ii)** of Cerone–Gotsman (completeness): the dependency graph of every
execution in `ExecSI` is in `GraphSI`. -/
theorem theorem10_completeness (X : Execution τ Obj V) (hX : X.IsSI) : X.graph.IsSI := by
  refine ⟨X.prop7 hX, hX.2.1, ?_⟩
  have hle := (sol_le (R := fun _ _ => False) (X.isSolution_of_isSI hX) (fun _ _ h => h.elim)).2
  obtain ⟨⟨⟨hvc, htr, hirr⟩, -⟩, -⟩ := hX
  refine acyclic_of_le ?_ (acyclic_of_le hle (acyclic_of_trans_irrefl htr hirr))
  intro a b h
  exact TransGen.single (Or.inl h)

/-- **Theorem 10** of Cerone–Gotsman, both directions. -/
theorem theorem10 :
    (∀ G : DepGraph τ Obj V, G.IsSI →
      ∃ X : Execution τ Obj V, X.IsSI ∧ X.graph = G) ∧
    (∀ X : Execution τ Obj V, X.IsSI → X.graph.IsSI) := by
  refine ⟨fun G hG => ?_, theorem10_completeness⟩
  obtain ⟨VIS, CO, h1, h2⟩ := theorem10_soundness G hG
  exact ⟨_, h1, h2⟩

/-- **Theorem 9** of Cerone–Gotsman: `HistSI = {H | ∃ WR WW RW. (H, WR, WW, RW) ∈ GraphSI}`. -/
theorem theorem9 (H : History τ Obj V) :
    H ∈ HistSI ↔ ∃ WR WW : Obj → τ → τ → Prop, (DepGraph.mk H WR WW).IsSI := by
  constructor
  · rintro ⟨VIS, CO, hX⟩
    exact ⟨_, _, theorem10_completeness _ hX⟩
  · rintro ⟨WR, WW, hG⟩
    obtain ⟨VIS, CO, h1, -⟩ := theorem10_soundness _ hG
    exact ⟨VIS, CO, h1⟩

/-! ### Serializability (Theorem 8) and parallel SI (Theorem 21) -/

/-- **Theorem 8** (Adya; cited by Cerone–Gotsman), soundness with preservation of dependencies:
every graph in `GraphSER` is the dependency graph of an execution in `ExecSER`. -/
theorem theorem8_soundness (G : DepGraph τ Obj V) (hG : G.IsSER) :
    ∃ VIS CO, (Execution.mk G.toHistory VIS CO).IsSER ∧
      (Execution.mk G.toHistory VIS CO).graph = G := by
  obtain ⟨hdg, hint, hacyc⟩ := hG
  set U := fun T S => G.B T S ∨ G.RWu T S
  obtain ⟨L, hUL, htrL, hirrL, htotL⟩ := exists_strictTotal_extension (TransGen U)
    (fun _ _ _ h1 h2 => h1.trans h2) hacyc
  have hBL : G.B ≤ L := fun a b h => hUL _ _ (TransGen.single (Or.inl h))
  obtain ⟨hext, -, hgr⟩ := G.ext_and_graph_eq hdg hBL le_rfl htrL hirrL
    (fun a b hab hba => hirrL _ (htrL _ _ _ hab (hUL _ _ (TransGen.single (Or.inr hba)))))
  exact ⟨L, L, ⟨⟨⟨le_rfl, htrL, hirrL⟩, htotL⟩, hint, hext,
    fun a b h => hBL _ _ (Or.inl h), rfl⟩, hgr⟩

/-- **Theorem 8** (Adya), completeness: the dependency graph of an execution in `ExecSER` is in
`GraphSER`. -/
theorem theorem8_completeness (X : Execution τ Obj V) (hX : X.IsSER) : X.graph.IsSER := by
  obtain ⟨⟨⟨hvc, htr, hirr⟩, htot⟩, hint, hext, hses, htv⟩ := hX
  refine ⟨X.isDepGraph_graph ⟨⟨hvc, htr, hirr⟩, htot⟩ hext, hint, ?_⟩
  refine acyclic_of_le ?_ (acyclic_of_trans_irrefl htr hirr)
  rintro a b ((h | ⟨x, h⟩ | ⟨x, h⟩) | ⟨x, h⟩)
  · exact htv ▸ hses _ _ h
  · exact hvc _ _ h.2.1.1
  · exact h.1
  · have hnv := X.not_vis_of_rw ⟨hvc, htr, hirr⟩ h
    rcases htot a b h.1 with h' | h'
    · exact h'
    · exact absurd (htv ▸ h') hnv

/-- **Theorem 8** (Adya; cited by Cerone–Gotsman):
`HistSER = {H | ∃ WR WW RW. (H, WR, WW, RW) ∈ GraphSER}`. -/
theorem theorem8 (H : History τ Obj V) :
    H ∈ HistSER ↔ ∃ WR WW : Obj → τ → τ → Prop, (DepGraph.mk H WR WW).IsSER := by
  constructor
  · rintro ⟨VIS, CO, hX⟩
    exact ⟨_, _, theorem8_completeness _ hX⟩
  · rintro ⟨WR, WW, hG⟩
    obtain ⟨VIS, CO, h1, -⟩ := theorem8_soundness _ hG
    exact ⟨VIS, CO, h1⟩

/-- **Theorem 21** (parallel SI; cited by Cerone–Gotsman from their DISC 2015 paper), soundness
with preservation of dependencies. -/
theorem theorem21_soundness (G : DepGraph τ Obj V) (hG : G.IsPSI) :
    ∃ VIS CO, (Execution.mk G.toHistory VIS CO).IsPSI ∧
      (Execution.mk G.toHistory VIS CO).graph = G := by
  obtain ⟨hdg, hint, hirrP⟩ := hG
  have hacyc : ∀ a, ¬ TransGen G.B a a := fun a h => hirrP a ⟨a, h, ReflGen.refl⟩
  obtain ⟨L, hBL, htrL, hirrL, htotL⟩ := exists_strictTotal_extension (TransGen G.B)
    (fun _ _ _ h1 h2 => h1.trans h2) hacyc
  obtain ⟨hext, hnc, hgr⟩ := G.ext_and_graph_eq hdg (fun a b h => TransGen.single h) hBL htrL
    hirrL (fun U S hUS hSU => hirrP U ⟨S, hUS, ReflGen.single hSU⟩)
  exact ⟨TransGen G.B, L, ⟨⟨⟨hBL, htrL, hirrL⟩, htotL⟩, hint, hext,
    fun a b h => TransGen.single (Or.inl h), fun _ _ _ h1 h2 => h1.trans h2, hnc⟩, hgr⟩

/-- **Theorem 21**, completeness: the dependency graph of an execution in `ExecPSI` is in
`GraphPSI`. -/
theorem theorem21_completeness (X : Execution τ Obj V) (hX : X.IsPSI) : X.graph.IsPSI := by
  obtain ⟨⟨⟨hvc, htr, hirr⟩, htot⟩, hint, hext, hses, htv, hnc⟩ := hX
  refine ⟨X.isDepGraph_graph ⟨⟨hvc, htr, hirr⟩, htot⟩ hext, hint, ?_⟩
  have hB : X.graph.B ≤ X.VIS := by
    rintro a b (h | ⟨x, h⟩ | ⟨x, hco, ha, hb⟩)
    · exact hses _ _ h
    · exact h.2.1.1
    · have hne : a ≠ b := by rintro rfl; exact hirr _ hco
      rcases hnc a b x ha hb hne with h | h
      · exact h
      · exact absurd (htr _ _ _ hco (hvc _ _ h)) (hirr _)
  have hBt : ∀ a b, TransGen X.graph.B a b → X.VIS a b :=
    fun a b h => transGen_of_trans htv (TransGen.mono hB a b h)
  rintro T ⟨S, hTS, hST⟩
  rcases hST with _ | ⟨x, hST⟩
  · exact hirr _ (hvc _ _ (hBt _ _ hTS))
  · exact X.not_vis_of_rw ⟨hvc, htr, hirr⟩ hST (hBt _ _ hTS)

/-- **Theorem 21** (parallel SI): `HistPSI = {H | ∃ WR WW RW. (H, WR, WW, RW) ∈ GraphPSI}`. -/
theorem theorem21 (H : History τ Obj V) :
    H ∈ HistPSI ↔ ∃ WR WW : Obj → τ → τ → Prop, (DepGraph.mk H WR WW).IsPSI := by
  constructor
  · rintro ⟨VIS, CO, hX⟩
    exact ⟨_, _, theorem21_completeness _ hX⟩
  · rintro ⟨WR, WW, hG⟩
    obtain ⟨VIS, CO, h1, -⟩ := theorem21_soundness _ hG
    exact ⟨VIS, CO, h1⟩

end Podc.AnalysingSI
