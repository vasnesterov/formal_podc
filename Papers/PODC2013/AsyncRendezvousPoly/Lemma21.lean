import Papers.PODC2013.AsyncRendezvousPoly.Ports

/-!
# Lemma 2.1: clean trajectories of `R(2m, v)` contain at least `m` nodes

Dieudonné, Pelc, Villain, *How to meet asynchronously at polynomial cost*, PODC 2013
(arXiv:1301.7119v2), Lemma 2.1.

If the trajectory `S` of an exploration procedure that explores all graphs of size `≤ 2m` is
*clean* (all its nodes have degree `≤ m - 1`) and has fewer than `m` nodes, then we build a graph
`H` of size `< 2m` in which the procedure follows the same trajectory, but which has extra nodes
attached to the *free* ports of `S` (ports never used by the trajectory). These extra nodes are not
visited, a contradiction.

The construction (`Lemma21.H`): node set `X ⊕ Fin d`, where `X` is the set of nodes of `S` and `d`
the maximal number of free ports at a node of `X`. Occupied ports keep their connections from `G`;
the `c`-th free port of `x ∈ X` (in an arbitrary fixed enumeration) leads to the extra node `c`,
whose ports enumerate (arbitrarily) the nodes `x` with more than `c` free ports.
-/

namespace Podc.AsyncRendezvousPoly

open Cslib.PortNumbering

namespace Lemma21

set_option linter.unusedSectionVars false

/-! ### Enumerating a finite set by an initial segment of `ℕ` -/

section Enum

variable {α : Type*} [DecidableEq α] (s : Finset α)

/-- Index of `a` in a fixed enumeration of `s` (`0` outside `s`). -/
noncomputable def enc (a : α) : ℕ := if h : a ∈ s then (s.equivFin ⟨a, h⟩ : ℕ) else 0

/-- The `c`-th element of `s` in the fixed enumeration (`a₀` if `c ≥ |s|`). -/
noncomputable def dec (a₀ : α) (c : ℕ) : α :=
  if h : c < s.card then (s.equivFin.symm ⟨c, h⟩).1 else a₀

variable {s}

theorem enc_lt {a : α} (h : a ∈ s) : enc s a < s.card := by
  simp only [enc, h, ↓reduceDIte]; exact Fin.isLt _

theorem dec_mem (a₀ : α) {c : ℕ} (h : c < s.card) : dec s a₀ c ∈ s := by
  simp only [dec, h, ↓reduceDIte]; exact Subtype.property _

theorem dec_enc (a₀ : α) {a : α} (h : a ∈ s) : dec s a₀ (enc s a) = a := by
  simp only [dec, enc_lt h, ↓reduceDIte]; simp [enc, h]

theorem enc_dec (a₀ : α) {c : ℕ} (h : c < s.card) : enc s (dec s a₀ c) = c := by
  simp only [enc, dec_mem a₀ h, ↓reduceDIte]; simp [dec, h]

end Enum

/-! ### The graph `H` -/

section Construction

open scoped Classical

variable {V : Type} [Fintype V] [DecidableEq V] (G : PNGraph V) (A : Proc) (v : V) (L : ℕ)

/-- The set `X` of nodes of the trajectory `walk G A v 0, …, walk G A v L`. -/
def Xs : Finset V := (Finset.range (L + 1)).image (walk G A v)

/-- `X` as a type. -/
abbrev XT := {x // x ∈ Xs G A v L}

/-- Port `j` of `x` is *occupied*: it is used by the trajectory (as exit or entry port). -/
def Occ (x : V) (j : ℕ) : Prop :=
  ∃ t < L, (walk G A v t = x ∧ j = exitPort G A v t) ∨
    (walk G A v (t + 1) = x ∧ j = G.rport (walk G A v t) (exitPort G A v t))

/-- The free ports of `x`. -/
noncomputable def free (x : V) : Finset ℕ :=
  (Finset.range (G.deg x)).filter (fun j => ¬ Occ G A v L x j)

/-- Number of free ports of `x`. -/
noncomputable def nfree (x : V) : ℕ := (free G A v L x).card

/-- Maximal number of free ports at a node of `X`. -/
noncomputable def d : ℕ := Finset.univ.sup (fun x : XT G A v L => nfree G A v L x.1)

/-- The nodes of `X` attached to the extra node `c`. -/
noncomputable def Y (c : ℕ) : Finset (XT G A v L) :=
  Finset.univ.filter (fun x => c < nfree G A v L x.1)

/-- The start node, as an element of `X`. -/
def base : XT G A v L := ⟨v, Finset.mem_image.2 ⟨0, by simp, rfl⟩⟩

/-- Nodes of `H`. -/
abbrev W := XT G A v L ⊕ Fin (d G A v L)

variable {G A v L}

theorem mem_free {x : V} {j : ℕ} : j ∈ free G A v L x ↔ j < G.deg x ∧ ¬ Occ G A v L x j := by
  simp [free]

theorem mem_Y {c : ℕ} {x : XT G A v L} : x ∈ Y G A v L c ↔ c < nfree G A v L x.1 := by
  simp [Y]

theorem nfree_le (x : V) : nfree G A v L x ≤ G.deg x :=
  (Finset.card_filter_le _ _).trans (Finset.card_range _).le

theorem enc_lt_d {x : XT G A v L} {j : ℕ} (h : j ∈ free G A v L x.1) :
    enc (free G A v L x.1) j < d G A v L :=
  lt_of_lt_of_le (enc_lt h)
    (Finset.le_sup (f := fun x : XT G A v L => nfree G A v L x.1) (Finset.mem_univ x))

theorem walk_mem {t : ℕ} (ht : t ≤ L) : walk G A v t ∈ Xs G A v L :=
  Finset.mem_image.2 ⟨t, by simp; omega, rfl⟩

theorem exists_of_mem {x : V} (hx : x ∈ Xs G A v L) : ∃ t ≤ L, walk G A v t = x := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
  exact ⟨t, by simp at ht; omega, rfl⟩

variable (hpos : ∀ x, 0 < G.deg x)
include hpos

theorem exitPort_lt' (t : ℕ) : exitPort G A v t < G.deg (walk G A v t) := Nat.mod_lt _ (hpos _)

theorem Occ.lt {x : V} {j : ℕ} (h : Occ G A v L x j) : j < G.deg x := by
  obtain ⟨t, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · exact exitPort_lt' hpos t
  · exact G.rport_lt (exitPort_lt' hpos t)

theorem Occ.nbr_mem {x : V} {j : ℕ} (h : Occ G A v L x j) : G.nbr x j ∈ Xs G A v L := by
  obtain ⟨t, ht, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · exact walk_mem (t := t + 1) (by omega)
  · rw [walk_succ, G.nbr_nbr (exitPort_lt' hpos t)]; exact walk_mem (by omega)

theorem Occ.symm {x : V} {j : ℕ} (h : Occ G A v L x j) :
    Occ G A v L (G.nbr x j) (G.rport x j) := by
  obtain ⟨t, ht, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · exact ⟨t, ht, Or.inr ⟨rfl, rfl⟩⟩
  · refine ⟨t, ht, Or.inl ⟨?_, ?_⟩⟩
    · rw [walk_succ, G.nbr_nbr (exitPort_lt' hpos t)]
    · rw [walk_succ, G.rport_rport (exitPort_lt' hpos t)]

omit hpos in
theorem occ_of_not_free {x : V} {j : ℕ} (hj : j < G.deg x) (h : j ∉ free G A v L x) :
    Occ G A v L x j := by
  by_contra h'; exact h (mem_free.2 ⟨hj, h'⟩)

omit hpos

variable (G A v L)

/-- Degrees in `H`. -/
noncomputable def degH : W G A v L → ℕ
  | .inl x => G.deg x.1
  | .inr c => (Y G A v L c).card

/-- Connections in `H`. -/
noncomputable def pH : W G A v L → ℕ → W G A v L × ℕ
  | .inl x, j =>
    if h : j ∈ free G A v L x.1 then
      (.inr ⟨enc (free G A v L x.1) j, enc_lt_d h⟩,
        enc (Y G A v L (enc (free G A v L x.1) j)) x)
    else if hn : G.nbr x.1 j ∈ Xs G A v L then (.inl ⟨G.nbr x.1 j, hn⟩, G.rport x.1 j)
    else (.inl x, j)
  | .inr c, k =>
    (.inl (dec (Y G A v L c) (base G A v L) k),
      dec (free G A v L (dec (Y G A v L c) (base G A v L) k).1) 0 c)

variable {G A v L}

theorem pH_inl_free {x : XT G A v L} {j : ℕ} (h : j ∈ free G A v L x.1) :
    pH G A v L (.inl x) j = (.inr ⟨enc (free G A v L x.1) j, enc_lt_d h⟩,
        enc (Y G A v L (enc (free G A v L x.1) j)) x) := by
  simp [pH, h]

theorem pH_inl_occ {x : XT G A v L} {j : ℕ} (h : j ∉ free G A v L x.1)
    (hn : G.nbr x.1 j ∈ Xs G A v L) :
    pH G A v L (.inl x) j = (.inl ⟨G.nbr x.1 j, hn⟩, G.rport x.1 j) := by
  simp [pH, h, hn]

include hpos

theorem pH_lt : ∀ w i, i < degH G A v L w → (pH G A v L w i).2 < degH G A v L (pH G A v L w i).1
  | .inl x, j, hj => by
    by_cases h : j ∈ free G A v L x.1
    · rw [pH_inl_free h]
      exact enc_lt (mem_Y.2 (enc_lt h))
    · have ho := occ_of_not_free hj h
      rw [pH_inl_occ h (ho.nbr_mem hpos)]
      exact G.rport_lt hj
  | .inr c, k, hk => by
    have hx := dec_mem (base G A v L) hk
    exact (mem_free.1 (dec_mem 0 (mem_Y.1 hx))).1

theorem pH_pH : ∀ w i, i < degH G A v L w →
    pH G A v L (pH G A v L w i).1 (pH G A v L w i).2 = (w, i)
  | .inl x, j, hj => by
    by_cases h : j ∈ free G A v L x.1
    · rw [pH_inl_free h]
      simp only [pH]
      rw [dec_enc _ (mem_Y.2 (enc_lt h)), dec_enc _ h]
    · have ho := occ_of_not_free hj h
      rw [pH_inl_occ h (ho.nbr_mem hpos)]
      have hs := ho.symm hpos
      have hn : G.rport x.1 j ∉ free G A v L (G.nbr x.1 j) := fun h' => (mem_free.1 h').2 hs
      have hm : G.nbr (G.nbr x.1 j) (G.rport x.1 j) ∈ Xs G A v L := by
        rw [G.nbr_nbr hj]; exact x.2
      rw [pH_inl_occ (x := ⟨G.nbr x.1 j, ho.nbr_mem hpos⟩) hn hm]
      ext
      · simp [G.nbr_nbr hj]
      · simp [G.rport_rport hj]
  | .inr c, k, hk => by
    have hx := dec_mem (base G A v L) hk
    have hf := dec_mem 0 (mem_Y.1 hx)
    change pH G A v L (.inl (dec (Y G A v L c) (base G A v L) k))
      (dec (free G A v L (dec (Y G A v L c) (base G A v L) k).1) 0 c) = _
    rw [pH_inl_free hf]
    have he : (⟨enc (free G A v L (dec (Y G A v L c) (base G A v L) k).1)
        (dec (free G A v L (dec (Y G A v L c) (base G A v L) k).1) 0 c), enc_lt_d hf⟩ :
          Fin (d G A v L)) = c := Fin.ext (enc_dec 0 (mem_Y.1 hx))
    rw [he, enc_dec 0 (mem_Y.1 hx), enc_dec _ hk]


variable (A v L) in
/-- The graph `H` of the proof of Lemma 2.1. -/
noncomputable def H : PNGraph (W G A v L) where
  deg := degH G A v L
  p := pH G A v L
  p_lt := pH_lt hpos
  p_p := pH_pH hpos

@[simp] theorem H_deg_inl (x : XT G A v L) : (H A v L hpos).deg (.inl x) = G.deg x.1 := rfl

theorem H_nbr_inl_free {x : XT G A v L} {j : ℕ} (h : j ∈ free G A v L x.1) :
    (H A v L hpos).nbr (.inl x) j = .inr ⟨enc (free G A v L x.1) j, enc_lt_d h⟩ := by
  simp [PNGraph.nbr, H, pH_inl_free h]

theorem H_nbr_inl_occ {x : XT G A v L} {j : ℕ} (h : j ∉ free G A v L x.1)
    (hn : G.nbr x.1 j ∈ Xs G A v L) :
    (H A v L hpos).nbr (.inl x) j = .inl ⟨G.nbr x.1 j, hn⟩ := by
  simp [PNGraph.nbr, H, pH_inl_occ h hn]

theorem H_simple (hS : G.IsSimple) : (H A v L hpos).IsSimple := by
  constructor
  · rintro (x | c) i hi
    · change i < G.deg x.1 at hi
      by_cases h : i ∈ free G A v L x.1
      · simp [H_nbr_inl_free hpos h]
      · have ho := occ_of_not_free hi h
        rw [H_nbr_inl_occ hpos h (ho.nbr_mem hpos)]
        simp only [ne_eq, Sum.inl.injEq, Subtype.ext_iff]
        exact hS.1 _ _ hi
    · simp [PNGraph.nbr, H, pH]
  · rintro (x | c) i j hi hj hij
    · change i < G.deg x.1 at hi
      change j < G.deg x.1 at hj
      by_cases h1 : i ∈ free G A v L x.1 <;> by_cases h2 : j ∈ free G A v L x.1
      · rw [H_nbr_inl_free hpos h1, H_nbr_inl_free hpos h2] at hij
        simp only [Sum.inr.injEq, Fin.mk.injEq] at hij
        rw [← dec_enc 0 h1, hij, dec_enc 0 h2]
      · rw [H_nbr_inl_free hpos h1,
          H_nbr_inl_occ hpos h2 ((occ_of_not_free hj h2).nbr_mem hpos)] at hij
        simp at hij
      · rw [H_nbr_inl_occ hpos h1 ((occ_of_not_free hi h1).nbr_mem hpos),
          H_nbr_inl_free hpos h2] at hij
        simp at hij
      · rw [H_nbr_inl_occ hpos h1 ((occ_of_not_free hi h1).nbr_mem hpos),
          H_nbr_inl_occ hpos h2 ((occ_of_not_free hj h2).nbr_mem hpos)] at hij
        simp only [Sum.inl.injEq, Subtype.mk.injEq] at hij
        exact hS.2 _ _ _ hi hj hij
    · change i < (Y G A v L c).card at hi
      change j < (Y G A v L c).card at hj
      simp only [PNGraph.nbr, H, pH, Sum.inl.injEq] at hij
      rw [← enc_dec (base G A v L) hi, hij, enc_dec _ hj]

theorem H_p_walk {t : ℕ} (ht : t < L) :
    (H A v L hpos).p (.inl ⟨walk G A v t, walk_mem ht.le⟩) (exitPort G A v t) =
      (.inl ⟨walk G A v (t + 1), walk_mem ht⟩, G.rport (walk G A v t) (exitPort G A v t)) := by
  have hocc : Occ G A v L (walk G A v t) (exitPort G A v t) := ⟨t, ht, Or.inl ⟨rfl, rfl⟩⟩
  have hnf : exitPort G A v t ∉ free G A v L (walk G A v t) := fun h => (mem_free.1 h).2 hocc
  exact pH_inl_occ (x := ⟨walk G A v t, walk_mem ht.le⟩) hnf (walk_mem ht)

/-- In `H`, the procedure follows the same trajectory (inside `X`) with the same observations. -/
theorem obsRun_H : ∀ t (ht : t ≤ L), obsRun (H A v L hpos) A (.inl (base G A v L)) t =
    (.inl ⟨walk G A v t, walk_mem ht⟩, (obsRun G A v t).2)
  | 0, _ => rfl
  | t + 1, ht => by
    have ih := obsRun_H t (by omega)
    have hp := H_p_walk (A := A) (v := v) hpos (t := t) ht
    simp only [obsRun]
    rw [ih]
    simp only [H_deg_inl]
    have hq : A (obsRun G A v t).2 % G.deg (walk G A v t) = exitPort G A v t := rfl
    rw [hq, PNGraph.nbr, PNGraph.rport, hp]
    rfl

theorem H_reach_walk (hS : G.IsSimple) : ∀ t (ht : t ≤ L),
    (H A v L hpos).toSimpleGraph.Reachable (.inl (base G A v L)) (.inl ⟨walk G A v t, walk_mem ht⟩)
  | 0, _ => SimpleGraph.Reachable.refl _
  | t + 1, ht => by
    refine (H_reach_walk hS t (by omega)).trans (SimpleGraph.Adj.reachable
      ⟨?_, exitPort G A v t, exitPort_lt' hpos t, by rw [PNGraph.nbr, H_p_walk hpos ht]⟩)
    simp only [ne_eq, Sum.inl.injEq, Subtype.mk.injEq]
    exact fun h => hS.1 _ _ (exitPort_lt' hpos t) (by rw [walk_succ] at h; exact h.symm)

theorem H_reach_inl (hS : G.IsSimple) (x : XT G A v L) :
    (H A v L hpos).toSimpleGraph.Reachable (.inl (base G A v L)) (.inl x) := by
  obtain ⟨t, ht, hx⟩ := exists_of_mem x.2
  have := H_reach_walk (A := A) (v := v) hpos hS t ht
  have e : (⟨walk G A v t, walk_mem ht⟩ : XT G A v L) = x := Subtype.ext hx
  rwa [e] at this

theorem H_connected (hS : G.IsSimple) : (H A v L hpos).toSimpleGraph.Connected := by
  have key : ∀ w, (H A v L hpos).toSimpleGraph.Reachable (.inl (base G A v L)) w := by
    rintro (x | c)
    · exact H_reach_inl hpos hS x
    · obtain ⟨x, -, hc⟩ := Finset.lt_sup_iff.1
        (show (c : ℕ) < Finset.univ.sup (fun x : XT G A v L => nfree G A v L x.1) from c.2)
      have hf := dec_mem 0 hc
      refine (H_reach_inl hpos hS x).trans (SimpleGraph.Adj.reachable
        ⟨Sum.inl_ne_inr, _, (mem_free.1 hf).1, ?_⟩)
      rw [H_nbr_inl_free hpos hf]
      simp [enc_dec 0 hc]
  have : Nonempty (W G A v L) := ⟨.inl (base G A v L)⟩
  exact ⟨fun a b => (key a).symm.trans (key b)⟩

end Construction

end Lemma21

open Lemma21 in
/-- **Lemma 2.1** of [DPV13]. Let `m ≤ n` and let `G` be a simple connected port-labelled graph of
size `n`. If the trajectory of `R(2m, v)` (procedure `A`, run for `L` steps, exploring all graphs of
size `≤ 2m`) is *clean* (all its nodes have degree `≤ m - 1`), then it contains at least `m`
different nodes. -/
theorem lemma_2_1 {V : Type} [Fintype V] [DecidableEq V] (G : PNGraph V) (hS : G.IsSimple)
    (hC : G.toSimpleGraph.Connected) (A : Proc) (L m : ℕ) (hm : m ≤ Fintype.card V)
    (hexp : ExploresUpTo A L (2 * m)) (v : V)
    (hclean : ∀ t ≤ L, G.deg (walk G A v t) ≤ m - 1) :
    m ≤ ((Finset.range (L + 1)).image (walk G A v)).card := by
  by_contra hlt
  push Not at hlt
  change (Xs G A v L).card < m at hlt
  have hv : v ∈ Xs G A v L := walk_mem (t := 0) (Nat.zero_le _)
  -- a node outside `X`
  obtain ⟨y, hy⟩ : ∃ y, y ∉ Xs G A v L := by
    by_contra h
    push Not at h
    have : Xs G A v L = Finset.univ := Finset.eq_univ_iff_forall.2 h
    rw [this, Finset.card_univ] at hlt
    omega
  -- all degrees are positive (`G` is connected with at least two nodes)
  have hpos : ∀ x, 0 < G.deg x := by
    intro x
    obtain ⟨z, hz⟩ : ∃ z, x ≠ z := by
      by_cases hx : x = y
      · subst hx; exact ⟨v, fun h => hy (h ▸ hv)⟩
      · exact ⟨y, hx⟩
    obtain ⟨p⟩ := hC.preconnected x z
    cases p with
    | nil => exact absurd rfl hz
    | cons h _ => obtain ⟨i, hi, -⟩ := h.2; omega
  -- some node of `X` has a free port, so `d ≥ 1`
  have hd : 0 < d G A v L := by
    obtain ⟨p⟩ := hC.preconnected v y
    obtain ⟨dd, -, h1, h2⟩ := p.exists_boundary_dart (Xs G A v L : Set V) hv hy
    obtain ⟨-, j, hj, hn⟩ := dd.adj
    have hf : j ∈ free G A v L dd.fst :=
      mem_free.2 ⟨hj, fun ho => h2 (by rw [Finset.mem_coe, ← hn]; exact ho.nbr_mem hpos)⟩
    have : 0 < nfree G A v L (⟨dd.fst, h1⟩ : XT G A v L).1 := Finset.card_pos.2 ⟨j, hf⟩
    exact lt_of_lt_of_le this
      (Finset.le_sup (f := fun x : XT G A v L => nfree G A v L x.1) (Finset.mem_univ _))
  -- cleanness: `d ≤ m - 1`
  have hdle : d G A v L ≤ m - 1 := by
    apply Finset.sup_le
    rintro ⟨x, hx⟩ -
    obtain ⟨t, ht, rfl⟩ := exists_of_mem hx
    exact (nfree_le _).trans (hclean t ht)
  have hcard : Fintype.card (W G A v L) ≤ 2 * m := by
    simp only [W, Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]
    omega
  obtain ⟨t, ht, heq⟩ := hexp (W G A v L) (H A v L hpos) (H_simple hpos hS) (H_connected hpos hS)
    hcard (.inl (base G A v L)) (.inr ⟨0, hd⟩)
  rw [walk, obsRun_H hpos t ht] at heq
  exact Sum.inl_ne_inr heq

end Podc.AsyncRendezvousPoly
