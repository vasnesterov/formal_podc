import Mathlib

-- CSLib candidate: Cslib/Combinatorics/SimpleGraph/PortPairing.lean (port pairings = Kotzig transition systems)

/-!
# Port pairings and the circuits they induce

Frei, Gelles, Ghazy, Nolin, *Brief Announcement: Toward Uniform Content-Oblivious Leader Election
on General Graphs*, PODC 2026, §2.1.

A network is a finite simple graph `G`. The ports of a node `v` are the darts `d : G.Dart` with
`d.fst = v` (the dart `d = (v, w)` is the port of `v` leading to `w`). A *port pairing*
(Kotzig's "transition system") partitions the ports of every node into pairs; we represent it by a
fixed-point-free involution `pair` on darts that preserves the node.

A pairing induces a successor map on darts, `next d = pair d.symm`: a walk entering `v` along `d`
leaves `v` through the port paired with the one it entered by. `next` is a permutation, and
conjugating it by `Dart.symm` inverts it. Two darts lie on the same *circuit* (`Pairing.Circ`) if
they lie on the same `next`-cycle up to reversal. This is the smallest equivalence relation
containing `d ~ pair d` and `d ~ d.symm` (`Circ.pair`, `Circ.symm_dart`, `Circ.closed`).

The key fact (`not_sameCycle_symm`): a dart and its reversal never lie on the same `next`-cycle,
so the two orientations of a circuit are two different `next`-cycles.
-/

namespace Podc.ContentObliviousEulerian

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A port pairing: the ports (darts) of every node are partitioned into pairs. -/
structure Pairing (G : SimpleGraph V) where
  /-- The port paired with a port. -/
  pair : G.Dart → G.Dart
  pair_pair : ∀ d, pair (pair d) = d
  pair_ne : ∀ d, pair d ≠ d
  fst_pair : ∀ d, (pair d).fst = d.fst

namespace Pairing

variable (π : Pairing G)

set_option linter.unusedSectionVars false

/-- The successor of a dart in the circuit decomposition induced by `π`: after traversing
`d = (u, v)`, leave `v` through the port paired with the port `(v, u)`. -/
def next : Equiv.Perm G.Dart where
  toFun d := π.pair d.symm
  invFun d := (π.pair d).symm
  left_inv d := by simp [π.pair_pair]
  right_inv d := by simp [π.pair_pair]

@[simp] lemma next_apply (d : G.Dart) : π.next d = π.pair d.symm := rfl

@[simp] lemma next_symm_apply (d : G.Dart) : π.next.symm d = (π.pair d).symm := rfl

@[simp] lemma next_inv_apply (d : G.Dart) : π.next⁻¹ d = (π.pair d).symm := rfl

lemma next_fst (d : G.Dart) : (π.next d).fst = d.snd := by
  simp [π.fst_pair]

/-- `Dart.symm` as a permutation. -/
def symmPerm : Equiv.Perm G.Dart where
  toFun d := d.symm
  invFun d := d.symm
  left_inv d := by simp
  right_inv d := by simp

/-- Reversal conjugates `next` to its inverse. -/
lemma symm_conj : symmPerm * π.next * symmPerm⁻¹ = π.next⁻¹ := by
  ext d
  simp [symmPerm, Equiv.Perm.mul_apply]
  rfl

lemma symm_zpow_apply (i : ℤ) (d : G.Dart) : ((π.next ^ i) d).symm = (π.next ^ (-i)) d.symm := by
  have h := congrArg (· ^ i) π.symm_conj
  simp only [conj_zpow] at h
  have := congrArg (fun f : Equiv.Perm G.Dart => f d.symm) h
  simp only [Equiv.Perm.mul_apply, inv_zpow', zpow_neg] at this
  simpa [symmPerm, zpow_neg] using this

lemma sameCycle_symm_symm {x y : G.Dart} (h : π.next.SameCycle x y) :
    π.next.SameCycle x.symm y.symm := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨-i, (π.symm_zpow_apply i x).symm⟩

lemma symm_pow_apply (n : ℕ) (d : G.Dart) :
    ((π.next ^ n) d).symm = (π.next ^ (-(n : ℤ))) d.symm := by
  rw [← π.symm_zpow_apply]; simp

/-- A dart and its reversal never lie on the same `next`-cycle. -/
theorem not_sameCycle_symm (d : G.Dart) : ¬ π.next.SameCycle d d.symm := by
  intro h
  obtain ⟨t, ht⟩ := h.exists_nat_pow_eq
  -- symm (next^s d) = next^(t-s) d
  have key : ∀ s : ℕ, s ≤ t → ((π.next ^ s) d).symm = (π.next ^ (t - s)) d := by
    intro s hs
    rw [π.symm_pow_apply, ← ht, ← Equiv.Perm.mul_apply, ← zpow_natCast, ← zpow_add,
      ← zpow_natCast]
    congr 2
    push_cast [Nat.cast_sub hs]; ring
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' t
  · have := key s (by omega)
    rw [show 2 * s - s = s by omega] at this
    exact Dart.symm_ne _ this
  · have := key s (by omega)
    rw [show 2 * s + 1 - s = s + 1 by omega, pow_succ', Equiv.Perm.mul_apply, next_apply] at this
    exact π.pair_ne _ this.symm

/-- Two darts lie on the same circuit of `π`: on the same `next`-cycle, up to reversal. -/
def Circ (d d' : G.Dart) : Prop := π.next.SameCycle d d' ∨ π.next.SameCycle d d'.symm

instance : DecidableRel π.Circ := fun _ _ => by unfold Circ; infer_instance

lemma Circ.refl (d : G.Dart) : π.Circ d d := Or.inl (Equiv.Perm.SameCycle.refl _ _)

variable {π} in
lemma Circ.symm {d d' : G.Dart} (h : π.Circ d d') : π.Circ d' d := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right; simpa using (π.sameCycle_symm_symm h).symm

variable {π} in
lemma Circ.trans {d₁ d₂ d₃ : G.Dart} (h₁ : π.Circ d₁ d₂) (h₂ : π.Circ d₂ d₃) : π.Circ d₁ d₃ := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Or.inl (h₁.trans h₂)
  · exact Or.inr (h₁.trans h₂)
  · exact Or.inr (h₁.trans (π.sameCycle_symm_symm h₂))
  · left; simpa using h₁.trans (π.sameCycle_symm_symm h₂)

lemma circ_equivalence : Equivalence π.Circ := ⟨Circ.refl π, Circ.symm, Circ.trans⟩

lemma Circ.pair (d : G.Dart) : π.Circ d (π.pair d) := by
  right
  have : π.next.SameCycle d.symm (π.pair d) := ⟨1, by simp⟩
  simpa using π.sameCycle_symm_symm this

lemma Circ.symm_dart (d : G.Dart) : π.Circ d d.symm := Or.inr (Equiv.Perm.SameCycle.refl _ _)

lemma Circ.next (d : G.Dart) : π.Circ d (π.next d) := Or.inl ⟨1, by simp⟩

lemma circ_iff_left {d₁ d₂ d : G.Dart} (h : π.Circ d₁ d₂) : π.Circ d₁ d ↔ π.Circ d₂ d :=
  ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

/-- Circuits are the smallest classes closed under pairing and reversal. -/
lemma Circ.closed {S : Set G.Dart} (hπ : ∀ x ∈ S, π.pair x ∈ S) (hs : ∀ x ∈ S, x.symm ∈ S)
    {d d' : G.Dart} (hd : d ∈ S) (h : π.Circ d d') : d' ∈ S := by
  have hn : ∀ x ∈ S, π.next x ∈ S := fun x hx => hπ _ (hs _ hx)
  have hpow : ∀ (n : ℕ), ∀ x ∈ S, (π.next ^ n) x ∈ S := by
    intro n; induction n with
    | zero => simp
    | succ n ih => intro x hx; rw [pow_succ', Equiv.Perm.mul_apply]; exact hn _ (ih x hx)
  rcases h with h | h
  · obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq; exact hpow n d hd
  · obtain ⟨n, hn'⟩ := h.exists_nat_pow_eq
    have := hpow n d hd
    rw [hn'] at this
    simpa using hs _ this

/-- A dart on the circuit of `d` is an iterate of `next` from `d`, or the reversal of one. -/
lemma circ_iff_exists (d d' : G.Dart) :
    π.Circ d d' ↔ ∃ n : ℕ, (π.next ^ n) d = d' ∨ (π.next ^ n) d = d'.symm := by
  constructor
  · rintro (h | h)
    · obtain ⟨n, hn⟩ := h.exists_nat_pow_eq; exact ⟨n, Or.inl hn⟩
    · obtain ⟨n, hn⟩ := h.exists_nat_pow_eq; exact ⟨n, Or.inr hn⟩
  · rintro ⟨n, h | h⟩
    · exact Or.inl ⟨n, by simpa using h⟩
    · exact Or.inr ⟨n, by simpa using h⟩

/-! ### Edge sets of circuits -/

/-- The edge set of the circuit through `d`. -/
def circuitEdges (d : G.Dart) : Finset (Sym2 V) :=
  (univ.filter (π.Circ d)).image Dart.edge

lemma mem_circuitEdges {d : G.Dart} {e : Sym2 V} :
    e ∈ π.circuitEdges d ↔ ∃ n : ℕ, ((π.next ^ n) d).edge = e := by
  simp only [circuitEdges, mem_image, mem_filter, mem_univ, true_and, circ_iff_exists]
  constructor
  · rintro ⟨x, ⟨n, hn | hn⟩, rfl⟩
    · exact ⟨n, by rw [hn]⟩
    · exact ⟨n, by rw [hn, Dart.edge_symm]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, ⟨n, Or.inl rfl⟩, rfl⟩

lemma circuitEdges_eq_of_circ {d d' : G.Dart} (h : π.Circ d d') :
    π.circuitEdges d = π.circuitEdges d' := by
  ext e
  simp only [circuitEdges, mem_image, mem_filter, mem_univ, true_and, π.circ_iff_left h]

lemma circ_of_edge_eq {d d' x x' : G.Dart} (hx : π.Circ d x) (hx' : π.Circ d' x')
    (he : x.edge = x'.edge) : π.Circ d d' := by
  rcases (dart_edge_eq_iff _ _).1 he with rfl | rfl
  · exact hx.trans hx'.symm
  · exact (hx.trans (Circ.symm_dart π _)).trans hx'.symm

lemma circ_of_mem_circuitEdges {d d' : G.Dart} {e : Sym2 V} (h : e ∈ π.circuitEdges d)
    (h' : e ∈ π.circuitEdges d') : π.Circ d d' := by
  simp only [circuitEdges, mem_image, mem_filter, mem_univ, true_and] at h h'
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨x', hx', he⟩ := h'
  exact π.circ_of_edge_eq hx hx' he.symm

/-- Every dart's edge lies on its own circuit. -/
lemma edge_mem_circuitEdges (d : G.Dart) : d.edge ∈ π.circuitEdges d :=
  mem_image.2 ⟨d, by simp [Circ.refl], rfl⟩

lemma circuitEdges_eq_iff {d d' : G.Dart} :
    π.circuitEdges d = π.circuitEdges d' ↔ π.Circ d d' :=
  ⟨fun h => π.circ_of_mem_circuitEdges (π.edge_mem_circuitEdges d) (h ▸ π.edge_mem_circuitEdges d),
    π.circuitEdges_eq_of_circ⟩

/-- The circuits of the decomposition induced by `π`, as edge sets. -/
def circuits : Finset (Finset (Sym2 V)) := univ.image π.circuitEdges

/-- Every edge of `G` is a dart's edge. -/
lemma exists_dart_of_mem_edgeSet {e : Sym2 V} (he : e ∈ G.edgeSet) : ∃ d : G.Dart, d.edge = e := by
  induction e using Sym2.ind with
  | _ u v => exact ⟨⟨(u, v), he⟩, rfl⟩

/-- The circuits partition the edge set of `G`. -/
theorem circuits_partition : ∀ e ∈ G.edgeSet, ∃! C, C ∈ π.circuits ∧ e ∈ C := by
  intro e he
  obtain ⟨d, rfl⟩ := exists_dart_of_mem_edgeSet he
  refine ⟨π.circuitEdges d, ⟨mem_image.2 ⟨d, mem_univ _, rfl⟩, π.edge_mem_circuitEdges d⟩, ?_⟩
  rintro C ⟨hC, hdC⟩
  obtain ⟨d', -, rfl⟩ := mem_image.1 hC
  exact π.circuitEdges_eq_of_circ (π.circ_of_mem_circuitEdges hdC (π.edge_mem_circuitEdges d))

lemma circuitEdges_subset_edgeFinset (d : G.Dart) : π.circuitEdges d ⊆ G.edgeFinset := by
  intro e he
  simp only [circuitEdges, mem_image] at he
  obtain ⟨x, -, rfl⟩ := he
  simp [x.edge_mem]

/-! ### Pairings exist iff all degrees are even -/

/-- The set of ports of `v`. -/
abbrev ports (v : V) : Finset G.Dart := univ.filter (fun d => d.fst = v)

lemma card_ports (v : V) : (ports (G := G) v).card = G.degree v :=
  dart_fst_fiber_card_eq_degree G v

/-- A port pairing forces every degree to be even. -/
theorem even_degree (π : Pairing G) (v : V) : Even (G.degree v) := by
  classical
  let σ : Equiv.Perm {d : G.Dart // d.fst = v} :=
    { toFun := fun d => ⟨π.pair d, by rw [π.fst_pair]; exact d.2⟩
      invFun := fun d => ⟨π.pair d, by rw [π.fst_pair]; exact d.2⟩
      left_inv := fun d => by simp [π.pair_pair]
      right_inv := fun d => by simp [π.pair_pair] }
  have h2 : σ ^ 2 = 1 := by
    refine Equiv.ext fun d => Subtype.ext ?_
    rw [sq, Equiv.Perm.mul_apply]; simp [σ, π.pair_pair]
  have hsupp : σ.support = univ := by
    ext d; simp only [Equiv.Perm.mem_support, mem_univ, iff_true]
    intro h; exact π.pair_ne d (congrArg Subtype.val h)
  have := Equiv.Perm.two_dvd_card_support h2
  rw [hsupp, card_univ, Fintype.card_subtype, dart_fst_fiber_card_eq_degree] at this
  exact even_iff_two_dvd.2 this

end Pairing

/-! ### The standard pairing of Lemma 2 -/

/-- The partner of a port number in the pairing `(0,1), (2,3), …` (the paper's `(1,2), (3,4), …`
with ports numbered from `1`). -/
def partner (j : ℕ) : ℕ := if j % 2 = 0 then j + 1 else j - 1

lemma partner_partner (j : ℕ) : partner (partner j) = j := by
  unfold partner; split_ifs <;> omega

lemma partner_ne (j : ℕ) : partner j ≠ j := by unfold partner; split_ifs <;> omega

lemma partner_lt {j n : ℕ} (hn : Even n) (hj : j < n) : partner j < n := by
  obtain ⟨m, rfl⟩ := hn
  unfold partner; split_ifs <;> omega

/-- A port numbering: the ports of `v` are numbered `0, …, deg v - 1`. -/
abbrev PortNumbering (G : SimpleGraph V) [DecidableRel G.Adj] :=
  (v : V) → {d : G.Dart // d.fst = v} ≃ Fin (G.degree v)

/-- Every graph has a port numbering. -/
lemma PortNumbering.exists : Nonempty (PortNumbering G) := by
  refine ⟨fun v => Fintype.equivFinOfCardEq ?_⟩
  rw [Fintype.card_subtype]; exact dart_fst_fiber_card_eq_degree G v

/-- **The pairing of Lemma 2.** If all degrees are even, pairing the ports `(0,1), (2,3), …`
of every node (for a given port numbering) is a port pairing. No communication is needed. -/
def stdPairing (port : PortNumbering G) (heven : ∀ v, Even (G.degree v)) : Pairing G where
  pair d := ((port d.fst).symm ⟨partner (port d.fst ⟨d, rfl⟩), partner_lt (heven _) (Fin.isLt _)⟩).1
  pair_pair d := by
    set e := (port d.fst).symm ⟨partner (port d.fst ⟨d, rfl⟩), partner_lt (heven _) (Fin.isLt _)⟩
    have he : e.1.fst = d.fst := e.2
    have key : ∀ (x : G.Dart) (v : V) (hx : x.fst = v),
        (port x.fst ⟨x, rfl⟩ : ℕ) = port v ⟨x, hx⟩ := by
      intro x v hx; subst hx; rfl
    have h1 : (port d.fst ⟨e.1, he⟩ : ℕ) = partner (port d.fst ⟨d, rfl⟩) := by
      simp [e]
    have h2 := key e.1 d.fst he
    rw [h1] at h2
    have h3 : ∀ (v : V) (hv : e.1.fst = v) (y : Fin (G.degree v)), (y : ℕ) =
        partner (port e.1.fst ⟨e.1, rfl⟩) → ((port v).symm y).1 = d := by
      intro v hv y hy; subst hv
      have : y = port e.1.fst ⟨d, he.symm ▸ rfl⟩ := by
        apply Fin.ext; rw [hy, h2, partner_partner]; exact key d e.1.fst he.symm ▸ rfl
      rw [this]; simp
    exact h3 _ rfl _ rfl
  pair_ne d := by
    intro h
    have hfst : ((port d.fst).symm ⟨partner (port d.fst ⟨d, rfl⟩),
        partner_lt (heven _) (Fin.isLt _)⟩).1 = d := h
    have := congrArg (fun x => ((port d.fst) x : ℕ))
      (Subtype.ext hfst : ((port d.fst).symm ⟨partner (port d.fst ⟨d, rfl⟩),
        partner_lt (heven _) (Fin.isLt _)⟩) = ⟨d, rfl⟩)
    simp only [Equiv.apply_symm_apply] at this
    exact partner_ne _ this
  fst_pair d := ((port d.fst).symm _).2

/-- Kotzig's Lemma 1 in the form used by the paper: a graph has a port pairing iff all degrees
are even (i.e. it is Eulerian in the paper's sense). -/
theorem nonempty_pairing_iff : Nonempty (Pairing G) ↔ ∀ v, Even (G.degree v) := by
  constructor
  · rintro ⟨π⟩; exact π.even_degree
  · intro h
    obtain ⟨port⟩ := PortNumbering.exists (G := G)
    exact ⟨stdPairing port h⟩

end Podc.ContentObliviousEulerian
