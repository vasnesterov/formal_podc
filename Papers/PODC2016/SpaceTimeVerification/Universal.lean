import Papers.PODC2016.SpaceTimeVerification.Basic
import Cslib.Foundations.Data.List.BitEncoding

/-!
# The universal `t`-PLS (Theorem 1, generic part)

Section 3.1 of *Space-Time Tradeoffs for Distributed Verification*: from any injective binary code
of configurations, a `t`-PLS whose labels are `|code| / k` bits plus an index of `log k` bits,
where `k ≈ t / 2` is the number of shares.

## The scheme (`universal`)

States are pairwise distinct (the states contain unique identifiers, Section 3.1). The prover
fixes a node `v₀` of eccentricity `≥ k - 1` (`center`), writes the code `c` of the whole
configuration (`toConf`, an enumeration of the nodes by `Fin n`), cuts it into `k` blocks of
length `⌈|c|/k⌉` (`Cslib.BitEncoding.chunk`), and gives the node at distance `d` from `v₀` the
label `lab k j (block j)` with `j = d mod k`.

The verifier at `u` (`verify`) accepts iff there are strings `s 0, …, s (k-1)` such that
1. every index `j < k` occurs, with share `s j`, at some node within distance `2k - 2` of `u`;
2. every node within distance `2k - 1` of `u` carries a label `lab k j (s j)` with `j < k`;
3. the concatenation `s 0 ++ ⋯ ++ s (k-1)` is the code of a configuration `c` that is connected,
   has pairwise distinct states, satisfies `P` (`Legal`), and is consistent with the local view
   of `u`: `c` has a node with the state of `u` whose neighbours have exactly the states of the
   neighbours of `u` (`LocalOK`).

Radius `2k - 1 ≤ t` suffices for locality (`verify_isLocal`, via `ballIso_edist`).

* Soundness (`verify_sound`): by 1–2, adjacent nodes have the same shares, so (connectivity) all
  nodes decode the same configuration `c`; by 3 and distinctness of the states, `u ↦` (its node in
  `c`) is an isomorphism `G ≃g c` preserving states, and `P` is isomorphism invariant.
* Completeness (`verify_complete`): a node at distance `d` from `v₀` finds every residue modulo
  `k` within distance `2k - 2`, on a shortest path to `v₀` or on a shortest path from `v₀` to a
  node at distance `≥ k - 1` (`exists_near_residue`).

## Deviations from the paper

* The paper's verifier collects the shares by pipelining along the BFS layers (orientation
  labels `d mod 3`, "first in block" and "`v`-indication" bits, `t/4` shares, `t/2` rounds) and
  then compares `g(u)` with its neighbours in `t/2` more rounds. Our model only records what a
  node sees in `t` rounds (the labelled `t`-ball), so the verifier is a property of the ball; the
  share index `j < k` is written in the label (`⌈log₂ (k+1)⌉` bits) instead of the `O(1)` bits of
  orientation, and agreement with the neighbours is replaced by condition 2 (all shares with the
  same index in the `(2k-1)`-ball agree). Message size is not modelled.
* The number of shares is a parameter `k` with `2k ≤ t + 1` (the paper: `t/4`).
-/

namespace Podc.SpaceTimeVerification

open SimpleGraph Cslib.BitEncoding

namespace Universal

/-! ### Ball isomorphisms preserve distances to the centre -/

section BallIsoDist

variable {V W : Type*} {t : ℕ} {G : SimpleGraph V} {G' : SimpleGraph W} {v : V} {φ : V → W}

/-- Walks starting near the centre are mapped forward. -/
lemma ballIso_forward
    (hadj : ∀ a, G.edist v a < t → ∀ b, G.Adj a b → G'.Adj (φ a) (φ b)) :
    ∀ {a b : V} (p : G.Walk a b) (d : ℕ), G.edist v a ≤ d → d + p.length ≤ t →
      G'.edist (φ a) (φ b) ≤ p.length := by
  intro a b p
  induction p with
  | nil => intro _ _ _; simp
  | @cons a b c h q ih =>
    intro d hd hlen
    simp only [Walk.length_cons] at hlen ⊢
    have hlt : G.edist v a < t := lt_of_le_of_lt hd (by exact_mod_cast (by omega : d < t))
    have h' := hadj a hlt b h
    have hb : G.edist v b ≤ (d + 1 : ℕ) := by
      calc G.edist v b ≤ G.edist v a + G.edist a b := G.edist_triangle
        _ ≤ d + 1 := by rw [edist_eq_one_iff_adj.2 h]; gcongr
        _ = (d + 1 : ℕ) := by push_cast; rfl
    have := ih (d + 1) hb (by omega)
    calc G'.edist (φ a) (φ c) ≤ G'.edist (φ a) (φ b) + G'.edist (φ b) (φ c) := G'.edist_triangle
      _ ≤ 1 + q.length := by rw [edist_eq_one_iff_adj.2 h']; gcongr
      _ = (q.length + 1 : ℕ) := by push_cast; ring

/-- Walks starting near the image of the centre are lifted back. -/
lemma ballIso_backward
    (hadj : ∀ a, G.edist v a < t → ∀ b', G'.Adj (φ a) b' → ∃ b, G.Adj a b ∧ φ b = b') :
    ∀ {a' b' : W} (q : G'.Walk a' b') (a : V) (d : ℕ), φ a = a' → G.edist v a ≤ d →
      d + q.length ≤ t → ∃ b, G.edist v b ≤ (d + q.length : ℕ) ∧ φ b = b' := by
  intro a' b' q
  induction q with
  | nil => intro a d ha hd _; exact ⟨a, by simpa using hd, ha⟩
  | @cons a' b' c' h q ih =>
    intro a d ha hd hlen
    simp only [Walk.length_cons] at hlen ⊢
    have hlt : G.edist v a < t := lt_of_le_of_lt hd (by exact_mod_cast (by omega : d < t))
    obtain ⟨b, hab, hb⟩ := hadj a hlt b' (ha ▸ h)
    have hbd : G.edist v b ≤ (d + 1 : ℕ) := by
      calc G.edist v b ≤ G.edist v a + G.edist a b := G.edist_triangle
        _ ≤ d + 1 := by rw [edist_eq_one_iff_adj.2 hab]; gcongr
        _ = (d + 1 : ℕ) := by push_cast; rfl
    obtain ⟨e, he, he'⟩ := ih b (d + 1) hb hbd (by omega)
    exact ⟨e, by rw [show d + (q.length + 1) = d + 1 + q.length by ring]; exact he, he'⟩

/-- A ball isomorphism preserves the distances to the centre, the labels, and is onto the ball
of the image; for `0 < t` it is a bijection between the neighbourhoods of the centres. -/
lemma ballIso_edist {α : Type*} {x : V → α} {x' : W → α} {w : W}
    (h : BallIso t G x v G' x' w) (ht : 0 < t) :
    ∃ φ : V → W, φ v = w ∧
      (∀ a, G.edist v a ≤ t → G'.edist w (φ a) = G.edist v a ∧ x' (φ a) = x a) ∧
      (∀ a', G'.edist w a' ≤ t → ∃ a, G.edist v a ≤ t ∧ φ a = a') ∧
      (∀ b, G.Adj v b → G'.Adj w (φ b)) ∧
      (∀ b', G'.Adj w b' → ∃ b, G.Adj v b ∧ φ b = b') := by
  obtain ⟨φ, hv, hinj, hx, hf, hb⟩ := h
  have h0 : G.edist v v < t := by simp [ht]
  have hv0 : G.edist v v ≤ ((0 : ℕ) : ℕ∞) := by simp
  -- lifting back
  have back : ∀ a', ∀ d' : ℕ, G'.edist w a' = d' → d' ≤ t →
      ∃ a, G.edist v a ≤ d' ∧ φ a = a' := by
    intro a' d' hd' hle
    obtain ⟨q, hq⟩ := exists_walk_of_edist_eq_coe hd'
    obtain ⟨a, ha, ha'⟩ := ballIso_backward hb q v 0 hv hv0 (by omega)
    exact ⟨a, by simpa [hq] using ha, ha'⟩
  refine ⟨φ, hv, fun a ha => ⟨?_, hx a ha⟩, fun a' ha' => ?_, fun b hvb => hv ▸ hf v h0 b hvb,
    fun b' hb' => hb v h0 b' (hv ▸ hb')⟩
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, G.edist v a = d :=
      ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by simp) ha) |>.imp fun _ h => h.symm
    have hdt : d ≤ t := by exact_mod_cast hd ▸ ha
    obtain ⟨p, hp⟩ := exists_walk_of_edist_eq_coe hd
    have h1 : G'.edist w (φ a) ≤ d := by
      have := ballIso_forward hf p 0 hv0 (by omega)
      rwa [hv, hp] at this
    obtain ⟨d', hd'⟩ : ∃ d' : ℕ, G'.edist w (φ a) = d' :=
      ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by simp) h1) |>.imp fun _ h => h.symm
    have hd'd : d' ≤ d := by exact_mod_cast hd' ▸ h1
    obtain ⟨b, hb1, hb2⟩ := back (φ a) d' hd' (by omega)
    have hbt : G.edist v b ≤ t := hb1.trans (by exact_mod_cast (by omega : d' ≤ t))
    have hba := hinj b a hbt ha hb2
    subst hba
    rw [hd', hd]
    have : (d : ℕ∞) ≤ d' := hd ▸ hb1
    exact_mod_cast le_antisymm hd'd (by exact_mod_cast this)
  · obtain ⟨d', hd'⟩ : ∃ d' : ℕ, G'.edist w a' = d' :=
      ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by simp) ha') |>.imp fun _ h => h.symm
    obtain ⟨a, ha, ha2⟩ := back a' d' hd' (by exact_mod_cast hd' ▸ ha')
    exact ⟨a, ha.trans (hd' ▸ ha'), ha2⟩

end BallIsoDist

/-! ### Labels: a fixed-width index followed by a share -/

-- CSLib candidate
/-- The `w` low bits of `j` (least significant first). -/
def bitsW (w j : ℕ) : List Bool := List.ofFn fun i : Fin w => j.testBit i

@[simp] lemma length_bitsW (w j : ℕ) : (bitsW w j).length = w := by simp [bitsW]

lemma bitsW_inj {w j j' : ℕ} (hj : j < 2 ^ w) (hj' : j' < 2 ^ w)
    (h : bitsW w j = bitsW w j') : j = j' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · have := congrFun (List.ofFn_injective h) ⟨i, hi⟩
    simpa using this
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hj' (Nat.pow_le_pow_right (by omega) (by omega)))]

/-- The label carrying share `x` with index `j` (for `k` shares). -/
def lab (k j : ℕ) (x : List Bool) : List Bool := bitsW (Nat.size k) j ++ x

lemma length_lab (k j : ℕ) (x : List Bool) : (lab k j x).length = Nat.size k + x.length := by
  simp [lab]

lemma lab_inj {k j j' : ℕ} {x x' : List Bool} (hj : j < k) (hj' : j' < k)
    (h : lab k j x = lab k j' x') : j = j' ∧ x = x' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  exact ⟨bitsW_inj ((hj.trans (Nat.lt_size_self k))) (hj'.trans (Nat.lt_size_self k)) h1, h2⟩

/-! ### Configurations on `Fin n` -/

/-- A configuration on the vertex set `Fin n`: the number of nodes, the graph and the states. -/
abbrev Conf (ι : Type) := Σ N : ℕ, SimpleGraph (Fin N) × (Fin N → ι)

/-- The configuration of `(G, I)`, with the nodes enumerated by `Finite.equivFin`. -/
noncomputable def toConf {ι V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι) : Conf ι :=
  ⟨Nat.card V, G.map (Finite.equivFin V).toEmbedding, I ∘ (Finite.equivFin V).symm⟩

/-- `P` is invariant under state-preserving graph isomorphisms. -/
def IsoInvariant {ι : Type} (P : CProp ι) : Prop :=
  ∀ {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) (I : V → ι),
    P V G I → P W H (I ∘ e.symm)

/-- A decoded configuration is legal: connected, with pairwise distinct states, satisfying `P`. -/
def Legal {ι : Type} (P : CProp ι) (c : Conf ι) : Prop :=
  c.2.1.Connected ∧ Function.Injective c.2.2 ∧ P (Fin c.1) c.2.1 c.2.2

/-- `c` is consistent with the local view of `u`: it has a node with the state of `u` whose
neighbours carry exactly the states of the neighbours of `u`. -/
def LocalOK {ι V : Type} (G : SimpleGraph V) (I : V → ι) (u : V) (c : Conf ι) : Prop :=
  ∃ i, c.2.2 i = I u ∧ (∀ b, G.Adj u b → ∃ i', c.2.1.Adj i i' ∧ c.2.2 i' = I b) ∧
    (∀ i', c.2.1.Adj i i' → ∃ b, G.Adj u b ∧ c.2.2 i' = I b)

/-! ### The scheme -/

variable {ι : Type} (code : Conf ι → List Bool) (P : CProp ι) (k : ℕ)

/-- The verifier of the universal scheme with `k` shares (see the module docstring). -/
def verify {V : Type} (G : SimpleGraph V) (I : V → ι) (ℓ : V → List Bool) (u : V) : Prop :=
  ∃ s : ℕ → List Bool,
    (∀ j < k, ∃ z, G.edist u z ≤ ↑(2 * k - 2) ∧ ℓ z = lab k j (s j)) ∧
    (∀ z, G.edist u z ≤ ↑(2 * k - 1) → ∃ j < k, ℓ z = lab k j (s j)) ∧
    ∃ c, code c = ((List.range k).map s).flatten ∧ Legal P c ∧ LocalOK G I u c

/-- The node from which the prover measures distances: one with a node at distance `≥ k - 1`
(it exists when the diameter is `≥ k - 1`). -/
noncomputable def center {V : Type} (G : SimpleGraph V) (u : V) : V := by
  classical
  exact if h : ∃ v x : V, k - 1 ≤ G.dist v x then h.choose else u

/-- The prover of the universal scheme with `k` shares. -/
noncomputable def prove {V : Type} (G : SimpleGraph V) (I : V → ι) (u : V) : List Bool := by
  classical
  exact if h : Finite V then
    let c := code (@toConf ι V h G I)
    let j := G.dist (center k G u) u % k
    lab k j (chunk c (c.length ⌈/⌉ k) j)
  else []

lemma prove_eq {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι) (u : V) :
    prove code k G I u =
      lab k (G.dist (center k G u) u % k)
        (chunk (code (toConf G I)) ((code (toConf G I)).length ⌈/⌉ k)
          (G.dist (center k G u) u % k)) := by
  simp only [prove, dite_eq_left_of_eq_true (eq_true (inferInstance : Finite V))]

/-! ### Locality -/

variable {code P k}

theorem verify_isLocal {t : ℕ} (hkt : 2 * k ≤ t + 1) (hk : 0 < k)
    {V W : Type} (G : SimpleGraph V) (I : V → ι) (ℓ : V → List Bool) (v : V)
    (G' : SimpleGraph W) (I' : W → ι) (ℓ' : W → List Bool) (w : W)
    (h : BallIso t G (fun u => (I u, ℓ u)) v G' (fun u => (I' u, ℓ' u)) w)
    (hv : verify code P k G I ℓ v) : verify code P k G' I' ℓ' w := by
  have ht : 0 < t := by omega
  obtain ⟨φ, hφv, hd, hsurj, hadj, hadj'⟩ := ballIso_edist h ht
  obtain ⟨s, h1, h2, c, hc, hleg, i, hi, hn1, hn2⟩ := hv
  have hle1 : ((2 * k - 2 : ℕ) : ℕ∞) ≤ t := by exact_mod_cast (by omega : 2 * k - 2 ≤ t)
  have hle2 : ((2 * k - 1 : ℕ) : ℕ∞) ≤ t := by exact_mod_cast (by omega : 2 * k - 1 ≤ t)
  have hle0 : ∀ b, G.Adj v b → G.edist v b ≤ t := fun b hb => by
    rw [edist_eq_one_iff_adj.2 hb]; exact_mod_cast ht
  refine ⟨s, fun j hj => ?_, fun z' hz' => ?_, c, hc, hleg, i, ?_, fun b' hb' => ?_,
    fun i' hi' => ?_⟩
  · obtain ⟨z, hz, hzl⟩ := h1 j hj
    obtain ⟨e1, e2⟩ := hd z (hz.trans hle1)
    exact ⟨φ z, e1 ▸ hz, by rw [← hzl]; exact congrArg Prod.snd e2⟩
  · obtain ⟨z, hz, rfl⟩ := hsurj z' (hz'.trans hle2)
    obtain ⟨e1, e2⟩ := hd z hz
    obtain ⟨j, hj, hjl⟩ := h2 z (e1 ▸ hz')
    exact ⟨j, hj, by rw [← hjl]; exact congrArg Prod.snd e2⟩
  · rw [hi, ← hφv]
    exact (congrArg Prod.fst (hd v (by simp)).2).symm
  · obtain ⟨b, hb, rfl⟩ := hadj' b' hb'
    obtain ⟨i', h1', h2'⟩ := hn1 b hb
    exact ⟨i', h1', by rw [h2']; exact (congrArg Prod.fst (hd b (hle0 b hb)).2).symm⟩
  · obtain ⟨b, hb, hbi⟩ := hn2 i' hi'
    exact ⟨φ b, hadj b hb, by rw [hbi]; exact (congrArg Prod.fst (hd b (hle0 b hb)).2).symm⟩

/-! ### Soundness -/

-- CSLib candidate
/-- A function that is constant along edges is constant on a connected graph. -/
lemma eq_of_adj_eq {V β : Type*} {G : SimpleGraph V} (hG : G.Connected) (f : V → β)
    (hf : ∀ a b, G.Adj a b → f a = f b) (a b : V) : f a = f b := by
  obtain ⟨p⟩ := hG a b
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hf _ _ h).trans ih

theorem verify_sound (hcode : Function.Injective code) (hP : IsoInvariant P) (hk : 0 < k)
    {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι) (hG : G.Connected)
    (hI : Function.Injective I) (ℓ : V → List Bool) (hacc : ∀ v, verify code P k G I ℓ v) :
    P V G I := by
  classical
  choose s h1 h2 c hc hleg hloc using hacc
  -- adjacent nodes have the same shares
  have hadj : ∀ a b, G.Adj a b → ((List.range k).map (s a)).flatten =
      ((List.range k).map (s b)).flatten := by
    intro a b hab
    congr 1
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    obtain ⟨z, hz, hzl⟩ := h1 b j hj
    have hza : G.edist a z ≤ ↑(2 * k - 1) := by
      calc G.edist a z ≤ G.edist a b + G.edist b z := G.edist_triangle
        _ ≤ 1 + ↑(2 * k - 2) := by rw [edist_eq_one_iff_adj.2 hab]; gcongr
        _ = ↑(2 * k - 1) := by
          rw [show 2 * k - 1 = 1 + (2 * k - 2) by omega]; push_cast; rfl
    obtain ⟨j', hj', hl⟩ := h2 a z hza
    obtain ⟨rfl, hx⟩ := lab_inj hj hj' (hzl.symm.trans hl)
    exact hx.symm
  obtain ⟨u₀⟩ := hG.nonempty
  have hc_eq : ∀ u, c u = c u₀ := fun u => hcode (by
    rw [hc, hc]; exact eq_of_adj_eq hG (fun u => ((List.range k).map (s u)).flatten) hadj u u₀)
  set C := c u₀ with hC
  obtain ⟨N, H, J⟩ := C
  obtain ⟨hHc, hJ, hPC⟩ := hC ▸ hleg u₀
  have hloc' : ∀ u, LocalOK G I u ⟨N, H, J⟩ := fun u => hc_eq u ▸ hloc u
  choose f hf1 hf2 hf3 using hloc'
  -- `f` is an isomorphism
  have hfinj : Function.Injective f := fun a b h => hI (by rw [← hf1 a, ← hf1 b, h])
  have hfadj : ∀ a b, H.Adj (f a) (f b) ↔ G.Adj a b := by
    intro a b
    constructor
    · intro hab
      obtain ⟨b', hb', hJb⟩ := hf3 a (f b) hab
      rw [hf1 b] at hJb
      exact hI hJb ▸ hb'
    · intro hab
      obtain ⟨i', hi', hJi⟩ := hf2 a b hab
      rw [← hf1 b] at hJi
      exact hJ hJi ▸ hi'
  have hfsurj : Function.Surjective f := by
    have hS : ∀ i ∈ Set.range f, ∀ i', H.Adj i i' → i' ∈ Set.range f := by
      rintro _ ⟨a, rfl⟩ i' hi'
      obtain ⟨b, -, hJb⟩ := hf3 a i' hi'
      rw [← hf1 b] at hJb
      exact ⟨b, (hJ hJb).symm⟩
    intro i
    exact mem_of_reachable hS ⟨u₀, rfl⟩ (hHc (f u₀) i)
  let e : G ≃g H := ⟨Equiv.ofBijective f ⟨hfinj, hfsurj⟩, fun {a b} => hfadj a b⟩
  have := hP H G e.symm J hPC
  convert this using 1
  funext u
  simp only [Function.comp_apply, RelIso.symm_symm]
  exact (hf1 u).symm

/-! ### Completeness -/

-- CSLib candidate
/-- In a connected graph, on a shortest path from `v` to `u` there is a node at any distance
`i ≤ dist v u` from `v`. -/
lemma exists_dist_between {V : Type*} {G : SimpleGraph V} (hG : G.Connected) {v u : V} {i : ℕ}
    (hi : i ≤ G.dist v u) : ∃ z, G.dist v z = i ∧ G.dist z u = G.dist v u - i := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v u
  refine ⟨p.getVert i, ?_⟩
  have h1 : G.dist v (p.getVert i) ≤ i := by
    have := dist_le (p.take i)
    rw [Walk.take_length] at this
    omega
  have h2 : G.dist (p.getVert i) u ≤ G.dist v u - i := by
    have := dist_le (p.drop i)
    rw [Walk.drop_length] at this
    omega
  have h3 := hG.dist_triangle (u := v) (v := p.getVert i) (w := u)
  omega

/-- Every residue modulo `k` occurs within distance `2k - 2` of every node `u`, if `v` has a node
at distance `≥ k - 1`. -/
lemma exists_near_residue {V : Type*} {G : SimpleGraph V} (hG : G.Connected) (hk : 0 < k)
    {v x : V} (hx : k - 1 ≤ G.dist v x) (u : V) {j : ℕ} (hj : j < k) :
    ∃ z, G.dist u z ≤ 2 * k - 2 ∧ G.dist v z % k = j := by
  set d := G.dist v u
  by_cases hjd : j ≤ d
  · have hq := Nat.mod_add_div (d - j) k
    have hm := Nat.mod_lt (d - j) hk
    obtain ⟨z, hz1, hz2⟩ := exists_dist_between hG (v := v) (u := u)
      (i := j + k * ((d - j) / k)) (by omega)
    refine ⟨z, ?_, ?_⟩
    · rw [dist_comm, hz2]; omega
    · rw [hz1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  · obtain ⟨z, hz1, -⟩ := exists_dist_between hG (v := v) (u := x) (i := j) (by omega)
    refine ⟨z, ?_, by rw [hz1, Nat.mod_eq_of_lt hj]⟩
    have := hG.dist_triangle (u := u) (v := v) (w := z)
    have h4 : G.dist u v = G.dist v u := dist_comm
    omega

lemma legal_toConf {V : Type} [Finite V] (hP : IsoInvariant P) (G : SimpleGraph V) (I : V → ι)
    (hG : G.Connected) (hI : Function.Injective I) (hPG : P V G I) : Legal P (toConf G I) := by
  refine ⟨(Iso.map (Finite.equivFin V) G).connected_iff.1 hG,
    hI.comp (Finite.equivFin V).symm.injective, hP _ _ (Iso.map (Finite.equivFin V) G) I hPG⟩

lemma localOK_toConf {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι) (u : V) :
    LocalOK G I u (toConf G I) := by
  unfold LocalOK toConf
  dsimp only
  set e := Finite.equivFin V
  have hadj : ∀ a b, (G.map e.toEmbedding).Adj (e a) (e b) ↔ G.Adj a b := fun a b =>
    (Iso.map e G).map_adj_iff
  refine ⟨e u, by simp, fun b hb => ⟨e b, (hadj u b).2 hb, by simp⟩,
    fun i' hi' => ⟨e.symm i', ?_, rfl⟩⟩
  rw [← hadj, e.apply_symm_apply]
  exact hi'

theorem verify_complete (hP : IsoInvariant P) (hk : 0 < k) {V : Type} [Finite V]
    (G : SimpleGraph V) (I : V → ι) (hG : G.Connected) (hI : Function.Injective I)
    (hD : k ≤ G.diam + 1) (hPG : P V G I) (u : V) :
    verify code P k G I (prove code k G I) u := by
  classical
  have hex : ∃ v x : V, k - 1 ≤ G.dist v x := by
    have := hG.nonempty
    obtain ⟨v, x, h⟩ := G.exists_dist_eq_diam
    exact ⟨v, x, by omega⟩
  have hcen : ∀ u, center k G u = hex.choose := fun u => by simp only [center, dite_eq_left_of_eq_true (eq_true hex)]
  set v := hex.choose
  obtain ⟨x, hx⟩ := hex.choose_spec
  set c := code (toConf G I)
  set L := c.length ⌈/⌉ k
  have hl : ∀ z, prove code k G I z = lab k (G.dist v z % k) (chunk c L (G.dist v z % k)) :=
    fun z => by rw [prove_eq, hcen]
  refine ⟨chunk c L, fun j hj => ?_, fun z _ => ⟨_, Nat.mod_lt _ hk, hl z⟩,
    toConf G I, (flatten_chunks c hk).symm, legal_toConf hP G I hG hI hPG,
    localOK_toConf G I u⟩
  obtain ⟨z, hz, hzj⟩ := exists_near_residue hG hk hx u hj
  refine ⟨z, ?_, by rw [hl z, hzj]⟩
  rw [← (hG u z).coe_dist_eq_edist]
  exact_mod_cast hz

end Universal

open Universal

/-- The universal `t`-PLS with `k` shares built from an injective code of configurations
(Section 3.1). The family `F` must consist of connected configurations with pairwise distinct
states (the states contain unique identifiers) and diameter `≥ k - 1`; `P` must be invariant
under state-preserving isomorphisms. -/
noncomputable def universal {ι : Type} (code : Conf ι → List Bool)
    (hcode : Function.Injective code) (F P : CProp ι) (hP : IsoInvariant P) (k t : ℕ)
    (hk : 0 < k) (hkt : 2 * k ≤ t + 1)
    (hF : ∀ {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι), F V G I →
      G.Connected ∧ Function.Injective I ∧ k ≤ G.diam + 1) :
    TPLS ι (List Bool) F P t where
  prove G I := Universal.prove code k G I
  verify := Universal.verify code P k
  isLocal G I ℓ v G' I' ℓ' w h := verify_isLocal hkt hk G I ℓ v G' I' ℓ' w h
  complete G I hFG hPG v :=
    verify_complete hP hk G I (hF G I hFG).1 (hF G I hFG).2.1 (hF G I hFG).2.2 hPG v
  sound G I hFG ℓ hacc := verify_sound hcode hP hk G I (hF G I hFG).1 (hF G I hFG).2.1 ℓ hacc

/-- The labels of the universal scheme: `⌈log₂ (k+1)⌉` bits of index plus `⌈|code|/k⌉` bits of
share. -/
theorem universal_length {ι : Type} (code : Conf ι → List Bool)
    (hcode : Function.Injective code) (F P : CProp ι) (hP : IsoInvariant P) (k t : ℕ)
    (hk : 0 < k) (hkt : 2 * k ≤ t + 1)
    (hF : ∀ {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι), F V G I →
      G.Connected ∧ Function.Injective I ∧ k ≤ G.diam + 1)
    {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι) (v : V) :
    ((universal code hcode F P hP k t hk hkt hF).prove G I v).length ≤
      Nat.size k + (code (toConf G I)).length ⌈/⌉ k := by
  show (Universal.prove code k G I v).length ≤ _
  rw [prove_eq, length_lab]
  exact Nat.add_le_add_left (length_chunk_le _ _ _) _

end Podc.SpaceTimeVerification
