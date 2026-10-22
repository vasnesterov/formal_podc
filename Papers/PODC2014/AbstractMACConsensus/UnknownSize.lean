import Podc.Computability.Distributed.AbstractMAC.Sync
import Cslib.Foundations.Combinatorics.SimpleGraph.PathGraph
import Papers.PODC2014.AbstractMACConsensus.TimeLB

/-!
# Theorem 3.9: consensus is impossible without knowledge of the network size

Newport, *Consensus with an abstract MAC layer*, PODC 2014, Section 3.3.

The network `K_D` (Figure 2): two lines `L¹_D`, `L²_D` of `D + 1` nodes and a line `L_{D-1}` of `D`
nodes, with every node of `L¹_D` and `L²_D` adjacent to the endpoint `e` of `L_{D-1}`; it has
diameter `D`, like the line `L_D` itself. In the *semi-synchronous* execution the broadcast of `e`
is held for `t` rounds: during them, `L¹_D` (inputs `0`) and `L²_D` (inputs `1`) behave exactly as
the line `L_D` alone with inputs `0`, resp. `1` (`syncLoc_comp`), where all nodes decided by round
`t` (Lemma 3.8). So agreement fails in `K_D`.

The algorithm may use unique ids (`id : V → ℕ` injective) and know `D`; only `n` is unknown.
-/

namespace Podc.AbstractMACConsensus

open Cslib.AbstractMAC Filter SimpleGraph

/-! ### Graph helpers -/

section GraphHelpers

variable {V : Type*} {G : SimpleGraph V}

/-- A function increasing by at most one along edges bounds walk lengths from below. -/
lemma walk_lipschitz (f : V → ℤ) (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1) {u v : V}
    (p : G.Walk u v) : f v ≤ f u + p.length := by
  induction p with
  | nil => simp
  | cons h p ih => have := hf _ _ h; simp only [Walk.length_cons]; push_cast; omega

/-- The diameter from explicit short walks and a pair that is far apart. -/
lemma diam_eq_of_walks {D : ℕ} (hup : ∀ u v, ∃ p : G.Walk u v, p.length ≤ D)
    (hlow : ∃ u v, ∀ p : G.Walk u v, D ≤ p.length) : G.diam = D := by
  have h1 : G.ediam ≤ D := ediam_le_iff.2 fun u v => by
    obtain ⟨p, hp⟩ := hup u v
    exact (edist_le p).trans (by exact_mod_cast hp)
  obtain ⟨u, v, hl⟩ := hlow
  have h2 : (D : ℕ∞) ≤ G.edist u v := by
    obtain ⟨p0, -⟩ := hup u v
    have hne : G.edist u v ≠ ⊤ := ne_top_of_le_ne_top (by simp) (edist_le p0)
    obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top hne
    rw [← hp]; exact_mod_cast hl p
  have he : G.ediam = D := le_antisymm h1 (h2.trans edist_le_ediam)
  have hne : G.ediam ≠ ⊤ := by rw [he]; simp
  exact_mod_cast (natCast_diam_eq_ediam_iff.2 hne).trans he

lemma connected_of_walks [Nonempty V] (h : ∀ u v, ∃ _ : G.Walk u v, True) : G.Connected :=
  ⟨fun u v => let ⟨p, _⟩ := h u v; ⟨p⟩⟩

end GraphHelpers

lemma pathGraph_walk_exists {n : ℕ} : ∀ (k i : ℕ) (h : i + k < n),
    ∃ p : (pathGraph n).Walk ⟨i, by omega⟩ ⟨i + k, h⟩, p.length = k := by
  intro k
  induction k with
  | zero => intro i h; exact ⟨.nil, rfl⟩
  | succ k ih =>
    intro i h
    obtain ⟨p, hp⟩ := ih (i + 1) (by omega)
    have hadj : (pathGraph n).Adj ⟨i, by omega⟩ ⟨i + 1, by omega⟩ := by
      rw [pathGraph_adj]; simp
    refine ⟨(Walk.cons hadj p).copy rfl (Fin.ext (by simp; omega)), ?_⟩
    simp [hp]

/-- Walks on the line between any two nodes, of length the difference of positions. -/
lemma pathGraph_walk (n : ℕ) (a b : Fin n) :
    ∃ p : (pathGraph n).Walk a b, p.length ≤ max (a : ℕ) b - min (a : ℕ) b := by
  rcases le_total (a : ℕ) b with h | h
  · obtain ⟨p, hp⟩ := pathGraph_walk_exists (n := n) (b - a) a (by omega)
    exact ⟨p.copy rfl (Fin.ext (by simp; omega)), by simp [hp]; omega⟩
  · obtain ⟨p, hp⟩ := pathGraph_walk_exists (n := n) (a - b) b (by omega)
    exact ⟨(p.copy rfl (Fin.ext (by simp; omega))).reverse, by simp [hp]; omega⟩

/-- The line `L_D` (`D + 1` nodes) has diameter `D`. -/
lemma pathGraph_diam (D : ℕ) : (pathGraph (D + 1)).diam = D := by
  refine diam_eq_of_walks (fun u v => ?_) ⟨0, Fin.last D, fun p => ?_⟩
  · obtain ⟨p, hp⟩ := pathGraph_walk (D + 1) u v
    exact ⟨p, by omega⟩
  · have := (pathGraph_walk_dist p).2
    simp at this; omega

/-! ### The network `K_D` -/

/-- Nodes of `K_D`: `L¹_D`, `L²_D`, `L_{D-1}`. -/
abbrev KV (D : ℕ) := Fin (D + 1) ⊕ Fin (D + 1) ⊕ Fin D

/-- The (oriented) edges of `K_D`. -/
def kRel {D : ℕ} : KV D → KV D → Bool
  | .inl i, .inl j => i.val + 1 = j.val
  | .inr (.inl i), .inr (.inl j) => i.val + 1 = j.val
  | .inr (.inr i), .inr (.inr j) => i.val + 1 = j.val
  | .inl _, .inr (.inr j) => j.val = 0
  | .inr (.inl _), .inr (.inr j) => j.val = 0
  | _, _ => false

/-- The network `K_D` of Figure 2. -/
def KD (D : ℕ) : SimpleGraph (KV D) := SimpleGraph.fromRel fun x y => kRel x y = true

instance (D : ℕ) : DecidableRel (KD D).Adj := fun _ _ =>
  decidable_of_iff' _ (SimpleGraph.fromRel_adj _ _ _)

lemma kd_adj_inl_inl {D : ℕ} (i j : Fin (D + 1)) :
    (KD D).Adj (.inl i) (.inl j) ↔ (pathGraph (D + 1)).Adj i j := by
  rw [KD, fromRel_adj, pathGraph_adj]; simp [kRel]; omega

lemma kd_adj_inl₂ {D : ℕ} (i j : Fin (D + 1)) :
    (KD D).Adj (.inr (.inl i)) (.inr (.inl j)) ↔ (pathGraph (D + 1)).Adj i j := by
  rw [KD, fromRel_adj, pathGraph_adj]; simp [kRel]; omega

lemma kd_adj_inr₂ {D : ℕ} (i j : Fin D) :
    (KD D).Adj (.inr (.inr i)) (.inr (.inr j)) ↔ (pathGraph D).Adj i j := by
  rw [KD, fromRel_adj, pathGraph_adj]; simp [kRel]; omega

/-- The endpoint `e` of `L_{D-1}`. -/
def kE (D : ℕ) (hD : 0 < D) : KV D := .inr (.inr ⟨0, hD⟩)

lemma kd_adj_e {D : ℕ} (hD : 0 < D) (x : KV D) (hx : x ∉ Set.range (Sum.inr ∘ Sum.inr)) :
    (KD D).Adj x (kE D hD) := by
  rcases x with i | i | i
  · rw [KD, fromRel_adj]; simp [kRel, kE]
  · rw [KD, fromRel_adj]; simp [kRel, kE]
  · exact absurd ⟨i, rfl⟩ hx

/-- `K_D` has diameter `D` (for `D ≥ 2`). -/
lemma kd_diam {D : ℕ} (hD : 2 ≤ D) : (KD D).diam = D := by
  have hD0 : 0 < D := by omega
  set e := kE D hD0
  -- walks inside `L_{D-1}` from `e`
  let ιm : pathGraph D →g KD D := ⟨Sum.inr ∘ Sum.inr, fun h => (kd_adj_inr₂ _ _).2 h⟩
  have hm : ∀ a b : Fin D, ∃ p : (KD D).Walk (.inr (.inr a)) (.inr (.inr b)), p.length ≤ D - 1 := by
    intro a b
    obtain ⟨p, hp⟩ := pathGraph_walk D a b
    exact ⟨p.map ιm, by simp; omega⟩
  have he : ∀ x : KV D, x ∉ Set.range (Sum.inr ∘ Sum.inr) →
      ∀ b : Fin D, ∃ p : (KD D).Walk x (.inr (.inr b)), p.length ≤ D := by
    intro x hx b
    obtain ⟨p, hp⟩ := pathGraph_walk D ⟨0, hD0⟩ b
    refine ⟨Walk.cons (v := ιm ⟨0, hD0⟩) (kd_adj_e hD0 x hx) (p.map ιm), ?_⟩
    show (p.map ιm).length + 1 ≤ D
    rw [Walk.length_map]; simp at hp; omega
  have hnr : ∀ i : Fin (D + 1), (Sum.inl i : KV D) ∉ Set.range (Sum.inr ∘ Sum.inr) := by simp
  have hnr2 : ∀ i : Fin (D + 1), (Sum.inr (Sum.inl i) : KV D) ∉ Set.range (Sum.inr ∘ Sum.inr) := by
    simp
  have htwo : ∀ x y : KV D, x ∉ Set.range (Sum.inr ∘ Sum.inr) →
      y ∉ Set.range (Sum.inr ∘ Sum.inr) → ∃ p : (KD D).Walk x y, p.length ≤ D := by
    intro x y hx hy
    by_cases hxy : x = y
    · subst hxy; exact ⟨.nil, by simp⟩
    · exact ⟨.cons (kd_adj_e hD0 x hx) (.cons ((kd_adj_e hD0 y hy).symm) .nil), by simp; omega⟩
  refine diam_eq_of_walks (fun u v => ?_) ⟨.inl 0, .inr (.inr ⟨D - 1, by omega⟩), fun p => ?_⟩
  · have hrev : ∀ x, x ∉ Set.range (Sum.inr ∘ Sum.inr) → ∀ b : Fin D,
        ∃ p : (KD D).Walk (.inr (.inr b)) x, p.length ≤ D := fun x hx b => by
      obtain ⟨p, hp⟩ := he x hx b; exact ⟨p.reverse, by simp; omega⟩
    rcases u with i | i | i <;> rcases v with j | j | j
    · exact htwo _ _ (hnr i) (hnr j)
    · exact htwo _ _ (hnr i) (hnr2 j)
    · exact he _ (hnr i) j
    · exact htwo _ _ (hnr2 i) (hnr j)
    · exact htwo _ _ (hnr2 i) (hnr2 j)
    · exact he _ (hnr2 i) j
    · exact hrev _ (hnr j) i
    · exact hrev _ (hnr2 j) i
    · obtain ⟨p, hp⟩ := hm i j; exact ⟨p, by omega⟩
  · -- a 1-Lipschitz potential: distance along `L_{D-1}` from the lines
    let f : KV D → ℤ := fun x => match x with
      | .inr (.inr j) => j.val + 1
      | _ => 0
    have hf : ∀ x y, (KD D).Adj x y → f y ≤ f x + 1 := by
      intro x y h
      rw [KD, fromRel_adj] at h
      rcases x with i | i | i <;> rcases y with j | j | j <;> simp [kRel] at h <;>
        simp only [f] <;> omega
    have := walk_lipschitz f hf p
    simp only [f] at this
    omega

/-! ### Theorem 3.9 -/

variable {M S : Type*}

/-- In the synchronous execution with all inputs `b` of an algorithm solving consensus on `G`,
all nodes have decided `b` after some number `t` of rounds (Lemmas 3.5 and 3.8). -/
lemma sync_decided {I V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (A : Algorithm I M S) (id : V → I) (H : SolvesConsensus A G id 0)
    (b : Bool) :
    ∃ t, ∀ v, (syncLoc A G (fun _ _ => false) (fun v => A.initNode (id v) b) t v).dec = some b := by
  let Hn : ℕ → V → Bool := fun _ _ => false
  let c₀ := Config.init A id fun _ => b
  have hfair := syncSched_fair Hn c₀ rfl (fun _ => rfl) 0 (fun _ _ _ => rfl) (A := A) (G := G)
  obtain ⟨T, hT, hT'⟩ := hfair.exists_timely
  obtain ⟨-, hV, hTm⟩ := H _ _ T 2 hT hT' (fun i => by rw [syncSched_down]; simp)
  have hdec : ∀ v, ∃ i, ((run A G c₀ (syncSched A G Hn c₀) i).loc v).dec = some b := by
    intro v
    obtain ⟨i, hi⟩ := hTm v (fun i => by rw [syncSched_down]; simp)
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 hi
    obtain ⟨w, hw⟩ := hV i v b' hb'
    exact ⟨i, hb'.trans (by rw [← hw])⟩
  choose J hJ using hdec
  refine ⟨Finset.univ.sup J, fun v => ?_⟩
  have := (mono_run A G v c₀ _ (Finset.le_sup (f := J) (Finset.mem_univ v))).dec_eq b (hJ v)
  rwa [syncSched_loc] at this

/-- **Lemma 3.8** (for the line `L_D` used in the proof): in the synchronous execution on the line
with all inputs `b`, all nodes have decided `b` after some number `t` of rounds. (The paper states
it uniformly for all line lengths `d`; only `d = D` is needed, and only that case follows from the
hypothesis, which concerns networks of diameter `D`.) -/
lemma lemma_3_8 {D : ℕ} (A : Algorithm ℕ M S) (id : Fin (D + 1) → ℕ)
    (H : SolvesConsensus A (pathGraph (D + 1)) id 0) (b : Bool) :
    ∃ t, ∀ v, (syncLoc A (pathGraph (D + 1)) (fun _ _ => false)
      (fun v => A.initNode (id v) b) t v).dec = some b :=
  sync_decided A id H b

/-- **Theorem 3.9.** For every `D > 1`, no algorithm (even with unique ids and knowledge of `D`)
solves consensus in all networks of diameter `D`. -/
theorem theorem_3_9 (D : ℕ) (hD : 1 < D) (A : Algorithm ℕ M S) :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (id : V → ℕ), Function.Injective id → G.Connected → G.diam = D →
        SolvesConsensus A G id 0 := by
  intro H
  have hD0 : 0 < D := by omega
  -- identities in `K_D` and on the two copies of `L_D`
  let idK : KV D → ℕ := fun x => match x with
    | .inl i => i.val
    | .inr (.inl i) => D + 1 + i.val
    | .inr (.inr i) => 2 * D + 2 + i.val
  have hidK : Function.Injective idK := by
    intro x y h
    rcases x with i | i | i <;> rcases y with j | j | j <;> simp only [idK] at h <;>
      first | omega | (congr 1; ext; omega) | (congr 2; ext; omega)
  have hP : ∀ id : Fin (D + 1) → ℕ, Function.Injective id →
      SolvesConsensus A (pathGraph (D + 1)) id 0 := fun id hid =>
    H (Fin (D + 1)) (pathGraph (D + 1)) id hid (pathGraph_connected D) (pathGraph_diam D)
  have hK : SolvesConsensus A (KD D) idK 0 := by
    have : Nonempty (KV D) := ⟨.inl 0⟩
    refine H (KV D) (KD D) idK hidK ?_ (kd_diam (by omega))
    exact SimpleGraph.connected_iff_diam_ne_zero.2 (by rw [kd_diam (by omega)]; omega)
  -- Lemma 3.8 for both copies
  obtain ⟨t0, ht0⟩ := lemma_3_8 A (fun i => idK (.inl i)) (hP _
    (hidK.comp Sum.inl_injective)) false
  obtain ⟨t1, ht1⟩ := lemma_3_8 A (fun i => idK (.inr (.inl i))) (hP _
    (hidK.comp (Sum.inr_injective.comp Sum.inl_injective))) true
  set t := max t0 t1
  -- the semi-synchronous execution of `K_D`
  let e := kE D hD0
  let Hk : ℕ → KV D → Bool := fun j x => decide (j < t ∧ x = e)
  let inp : KV D → Bool := fun x => match x with
    | .inr (.inl _) => true
    | _ => false
  let c₀ := Config.init A idK inp
  let Hn : ℕ → Fin (D + 1) → Bool := fun _ _ => false
  -- simulation of `L_D` by each copy
  have sim : ∀ (ι : Fin (D + 1) → KV D) (b : Bool),
      (∀ i j, (KD D).Adj (ι i) (ι j) ↔ (pathGraph (D + 1)).Adj i j) → Function.Injective ι →
      (∀ i, ι i ≠ e) → (∀ i (x : KV D), (KD D).Adj x (ι i) → x ≠ e → ∃ j, x = ι j) →
      (∀ i, inp (ι i) = b) →
      ∀ v, syncLoc A (KD D) Hk (fun v => A.initNode (idK v) (inp v)) t (ι v) =
        syncLoc A (pathGraph (D + 1)) Hn (fun v => A.initNode (idK (ι v)) b) t v := by
    intro ι b hadj hinj hne hnb hinp
    refine syncLoc_comp A ι Hk Hn _ _ t (fun j hj v' => ?_) (fun j _ v' => ?_)
      (fun v' => by simp [hinp]) t le_rfl
    · have : (Finset.univ.filter fun u => (KD D).Adj u (ι v') ∧ Hk j u = false) =
          (Finset.univ.filter fun u' => (pathGraph (D + 1)).Adj u' v' ∧ Hn j u' = false).map
            ⟨ι, hinj⟩ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
          Function.Embedding.coeFn_mk, Hk, Hn, and_true, decide_eq_false_iff_not, not_and]
        constructor
        · rintro ⟨h1, h2⟩
          obtain ⟨i, rfl⟩ := hnb v' x h1 (h2 hj)
          exact ⟨i, (hadj i v').1 h1, rfl⟩
        · rintro ⟨i, h1, rfl⟩
          exact ⟨(hadj i v').2 h1, fun _ => hne i⟩
      rw [this, Finset.map_val]
      rfl
    · simp [Hk, Hn, hne v']
  have hL1 := sim Sum.inl false (fun i j => kd_adj_inl_inl i j) Sum.inl_injective
    (fun i => by simp [e, kE]) (fun i x h hx => by
      rcases x with j | j | j
      · exact ⟨j, rfl⟩
      · rw [KD, fromRel_adj] at h; simp [kRel] at h
      · rw [KD, fromRel_adj] at h
        exact absurd (by simp [kRel] at h; simp [e, kE]; ext; omega) hx) (fun _ => rfl)
  have hL2 := sim (fun i => .inr (.inl i)) true (fun i j => kd_adj_inl₂ i j)
    (fun i j h => by simpa using h)
    (fun i => by simp [e, kE]) (fun i x h hx => by
      rcases x with j | j | j
      · rw [KD, fromRel_adj] at h; simp [kRel] at h
      · exact ⟨j, rfl⟩
      · rw [KD, fromRel_adj] at h
        exact absurd (by simp [kRel] at h; simp [e, kE]; ext; omega) hx) (fun _ => rfl)
  -- decisions after `t` rounds
  have d0 : (syncLoc A (KD D) Hk (fun v => A.initNode (idK v) (inp v)) t (.inl 0)).dec =
      some false := by
    rw [hL1]; exact syncLoc_dec_mono (ht0 0) (le_max_left _ _)
  have d1 : (syncLoc A (KD D) Hk (fun v => A.initNode (idK v) (inp v)) t (.inr (.inl 0))).dec =
      some true := by
    rw [hL2]; exact syncLoc_dec_mono (ht1 0) (le_max_right _ _)
  -- the semi-synchronous execution is admissible, so agreement must hold in it
  have hfair := syncSched_fair Hk c₀ rfl (fun _ => rfl) t
    (fun j hj x => by simp [Hk]; omega) (A := A) (G := KD D)
  obtain ⟨T, hT, hT'⟩ := hfair.exists_timely
  obtain ⟨hAg, -, -⟩ := hK inp _ T 2 hT hT' (fun i => by rw [syncSched_down]; simp)
  have := hAg t t (.inl 0) (.inr (.inl 0)) false true (by rw [syncSched_loc]; exact d0)
    (by rw [syncSched_loc]; exact d1)
  simp at this

end Podc.AbstractMACConsensus
