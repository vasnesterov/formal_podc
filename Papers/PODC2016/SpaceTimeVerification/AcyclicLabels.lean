import Papers.PODC2016.SpaceTimeVerification.Basic
import Cslib.Foundations.Combinatorics.SimpleGraph.Arboricity
import Cslib.Foundations.Combinatorics.SimpleGraph.WalkParity
import Cslib.Foundations.Combinatorics.SimpleGraph.BFSTree

/-!
# Acyclicity labels (Section 4.2): Definitions 10–14, Proposition 16

The labels of the `t`-PLS for acyclicity of *Space-Time Tradeoffs for Distributed Verification*
(Ostrovsky, Perry, Rosenbaum; arXiv:1605.06814), Section 4.2.

An acyclicity label (`AcLab`) consists of
* an orientation label `a ∈ {0,1,2}` (`Fin 3`),
* a block label `b ∈ {head, mid, tail}` (`BLab`),
* a block colour `c ∈ {0,1}` (`Bool`),
* a distance label `d ∈ {0,1}*` (`List Bool`, a share of the distance of the block to the root).

Lists of vertices are written in the paper's order: an oriented path / block
`[v₀, v₁, …, v_{k-1}]` goes *down* the orientation (`v_i` is the parent of `v_{i+1}`).

## Definitions
* `IsPar G ℓ v u`: `u` is a parent of `v` (`u ~ v` and `a(u) ≡ a(v) - 1 (mod 3)`).
* `OrientCorrect`, `BlockCorrect`, `ColorCorrect`, `DistCorrect`: the four conditions of
  Definition 14. `BlockCorrect` is parametrised by the admissible lengths in condition 4.
* `Correct t` (condition 4 with `k ≤ t`, the intended reading) and `CorrectLiteral t` (condition 4
  as printed, `k < t`).
* `blockValue`: Definition 13, the integer whose binary expansion is `d(v_{t-1}) ⋯ d(v₀)`.

## Results
* `prop16`: Proposition 16 (corrected): for `t ≥ 2`, a finite graph is acyclic iff it admits a
  correct acyclicity labelling.
* `correctLiteral_two_no_edges`, `not_correctLiteral_path`: with condition 4 as printed
  (`k < t`), for `t = 2` no graph with an edge has a correct labelling, so Proposition 16 fails
  as printed (e.g. for the path on 2 vertices).
* `correct_one_isEmpty`: for `t = 1` no nonempty graph admits a correct labelling.
-/

namespace Podc.SpaceTimeVerification

open SimpleGraph

/-! ### Labels -/

/-- The block label `b(v)`: position of `v` within its block. -/
inductive BLab
  | head
  | mid
  | tail
  deriving DecidableEq

/-- An acyclicity label `ℓ(v) = (a(v), b(v), c(v), d(v))` (Section 4.2). -/
structure AcLab where
  /-- Orientation label `a(v) ∈ {0, 1, 2}`. -/
  a : Fin 3
  /-- Block label. -/
  b : BLab
  /-- Block colour `c(v) ∈ {0, 1}`. -/
  c : Bool
  /-- Distance label: a share of the distance of the block to the root. -/
  d : List Bool

/-! ### Binary values -/

/-- The integer whose binary expansion (most significant bit first) is `l`. -/
def bitsVal (l : List Bool) : ℕ := l.foldl (fun n b => 2 * n + b.toNat) 0

/-- `w`-bit binary expansion (most significant bit first) of `n mod 2^w`. -/
def toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, n => toBits w (n / 2) ++ [n % 2 == 1]

/-- Definition 13 (value of a block), on the list `[d(v₀), …, d(v_{t-1})]` of distance labels:
the integer whose binary expansion is the concatenation `d(v_{t-1}) d(v_{t-2}) ⋯ d(v₀)`. -/
def blockValue (ds : List (List Bool)) : ℕ := bitsVal ds.reverse.flatten

lemma foldl_bits (l : List Bool) (n : ℕ) :
    l.foldl (fun n b => 2 * n + b.toNat) n = n * 2 ^ l.length + bitsVal l := by
  induction l generalizing n with
  | nil => simp [bitsVal]
  | cons x l ih =>
    simp only [List.foldl_cons, bitsVal, List.length_cons] at ih ⊢
    rw [ih, ih (2 * 0 + x.toNat)]
    ring

lemma bitsVal_append (l₁ l₂ : List Bool) :
    bitsVal (l₁ ++ l₂) = bitsVal l₁ * 2 ^ l₂.length + bitsVal l₂ := by
  rw [bitsVal, List.foldl_append, foldl_bits]
  rfl

@[simp] lemma blockValue_nil : blockValue [] = 0 := rfl

lemma blockValue_cons (x : List Bool) (xs : List (List Bool)) :
    blockValue (x :: xs) = bitsVal x + 2 ^ x.length * blockValue xs := by
  simp only [blockValue, List.reverse_cons, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, bitsVal_append]
  ring

@[simp] lemma length_toBits (w n : ℕ) : (toBits w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [toBits, ih]

lemma bitsVal_toBits (w n : ℕ) : bitsVal (toBits w n) = n % 2 ^ w := by
  induction w generalizing n with
  | zero => simp [toBits, bitsVal, Nat.mod_one]
  | succ w ih =>
    rw [toBits, bitsVal_append, ih, pow_succ', Nat.mod_mul]
    simp only [List.length_singleton, pow_one]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [bitsVal, h] <;> ring

/-- Splitting `H` into `t` chunks of `w` bits (chunk `i` is held by `v_i`) and reading the block
value back gives `H mod 2^(w t)`. -/
lemma blockValue_chunks (w t H : ℕ) :
    blockValue ((List.range t).map fun i => toBits w (H / 2 ^ (w * i))) = H % 2 ^ (w * t) := by
  induction t generalizing H with
  | zero => simp [Nat.mod_one]
  | succ t ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, blockValue_cons, length_toBits,
      bitsVal_toBits]
    have : ((fun i => toBits w (H / 2 ^ (w * i))) ∘ Nat.succ) =
        fun i => toBits w (H / 2 ^ w / 2 ^ (w * i)) := by
      funext i
      simp [Nat.div_div_eq_div_mul, ← pow_add, Nat.mul_succ, Nat.add_comm]
    rw [this, ih, Nat.mul_succ, Nat.add_comm (w * t), pow_add, Nat.mod_mul]
    simp

/-! ### Correct acyclicity labels (Definition 14) -/

section Defs

variable {V : Type*} (t : ℕ) (G : SimpleGraph V) (ℓ : V → AcLab)

/-- `u` is a parent of `v`: a neighbour with `a(u) ≡ a(v) - 1 (mod 3)`. -/
def IsPar (v u : V) : Prop := G.Adj v u ∧ (ℓ u).a + 1 = (ℓ v).a

/-- `v` is a root: it has no parent (`P(v) = ∅`). -/
def IsRoot (v : V) : Prop := ¬ ∃ u, IsPar G ℓ v u

/-- An oriented path `[w₀, …, w_{k-1}]`: `w_i` is a parent of `w_{i+1}`. Its length is the number
`k` of vertices, as in the paper. -/
def OrientedPath (l : List V) : Prop := l.IsChain fun x y => IsPar G ℓ y x

/-- A block: an oriented path `[v₀, …, v_{t-1}]` of length `t` with `b(v₀) = head`
(condition 2 of correct block labels). -/
def IsBlock (B : List V) : Prop :=
  B.length = t ∧ OrientedPath G ℓ B ∧ ∃ h ∈ B.head?, (ℓ h).b = .head

/-- Definition 13: `B` is the parent of `B'` (and `B'` a child of `B`): the parent of the first
vertex of `B'` is the last vertex of `B`. -/
def IsParentBlock (B B' : List V) : Prop :=
  ∃ x ∈ B.getLast?, ∃ y ∈ B'.head?, IsPar G ℓ y x

/-- Definition 13: the value `D(B)` of a block `B = [v₀, …, v_{t-1}]`, the integer whose binary
expansion is `d(v_{t-1}) ⋯ d(v₀)`. -/
def blockVal (B : List V) : ℕ := blockValue (B.map fun x => (ℓ x).d)

/-- Correct orientation labels: at most one parent, all other neighbours are children
(`a(w) ≡ a(v) + 1`). -/
def OrientAt (v : V) : Prop :=
  (∀ u u', IsPar G ℓ v u → IsPar G ℓ v u' → u = u') ∧
    ∀ w, G.Adj v w → ¬ IsPar G ℓ v w → (ℓ w).a = (ℓ v).a + 1

/-- Condition 1 of correct block labels at `v`. -/
def HeadAt (v : V) : Prop :=
  (ℓ v).b = .head ↔ IsRoot G ℓ v ∨ ∃ u, IsPar G ℓ v u ∧ (ℓ u).b = .tail

/-- Condition 2 of correct block labels at `v`. -/
def TailAt (v : V) : Prop :=
  (ℓ v).b = .tail ↔ ∃ B, IsBlock t G ℓ B ∧ B.getLast? = some v

/-- Condition 3 of correct block labels at `v` ("in all other cases, `b(v) = mid`"). -/
def MidAt (v : V) : Prop :=
  (ℓ v).b = .mid ↔
    ¬ (IsRoot G ℓ v ∨ ∃ u, IsPar G ℓ v u ∧ (ℓ u).b = .tail) ∧
      ¬ ∃ B, IsBlock t G ℓ B ∧ B.getLast? = some v

/-- Condition 4 of correct block labels at `v`, with admissible path lengths `len`: there is an
oriented path `w₀, …, w_{k-1} = v` with `len k` and `b(w₀) = head`. -/
def HeadNear (len : ℕ → Prop) (v : V) : Prop :=
  ∃ l, OrientedPath G ℓ l ∧ l.getLast? = some v ∧ len l.length ∧ ∃ h ∈ l.head?, (ℓ h).b = .head

/-- Correct orientation labels. -/
def OrientCorrect : Prop := ∀ v, OrientAt G ℓ v

/-- Correct block labels (conditions 1–4), with admissible lengths `len` in condition 4. -/
def BlockCorrect (len : ℕ → Prop) : Prop :=
  ∀ v, HeadAt G ℓ v ∧ TailAt t G ℓ v ∧ MidAt t G ℓ v ∧ HeadNear G ℓ len v

/-- Correct block colouring. -/
def ColorCorrect : Prop :=
  (∀ B, IsBlock t G ℓ B → ∀ x ∈ B, ∀ y ∈ B, (ℓ x).c = (ℓ y).c) ∧
    ∀ B B', IsBlock t G ℓ B → IsBlock t G ℓ B' → IsParentBlock G ℓ B B' →
      ∀ x ∈ B, ∀ y ∈ B', (ℓ x).c ≠ (ℓ y).c

/-- Correct distance labels. -/
def DistCorrect : Prop :=
  (∀ B, IsBlock t G ℓ B → (blockVal ℓ B = 0 ↔ ∃ h ∈ B.head?, IsRoot G ℓ h)) ∧
    ∀ B B', IsBlock t G ℓ B → IsBlock t G ℓ B' → IsParentBlock G ℓ B B' →
      blockVal ℓ B' = blockVal ℓ B + t

/-- Definition 14 with condition 4 of the block labels for admissible lengths `len`. -/
def CorrectAux (len : ℕ → Prop) : Prop :=
  OrientCorrect G ℓ ∧ BlockCorrect t G ℓ len ∧ ColorCorrect t G ℓ ∧ DistCorrect t G ℓ

/-- Definition 14 (correct acyclicity labelling), with condition 4 of the block labels read as
`k ≤ t` (a tail is `t - 1` edges, i.e. `t` vertices, below its head; this is the reading used in
the proof of Lemma 17 and in Figure 1). -/
def Correct : Prop := CorrectAux t G ℓ (· ≤ t)

/-- Definition 14 taken literally: condition 4 of the block labels with `k < t`. -/
def CorrectLiteral : Prop := CorrectAux t G ℓ (· < t)

end Defs

/-! ### Basic facts -/

section Basic

variable {V : Type*} {t : ℕ} {G : SimpleGraph V} {ℓ : V → AcLab}

lemma fin3_not_both (x y : Fin 3) (h₁ : y + 1 = x) (h₂ : x + 1 = y) : False := by
  revert x y; decide

/-- Correct orientation labels orient every edge: one endpoint is the parent of the other. -/
lemma isPar_or_isPar (ho : OrientCorrect G ℓ) {u v : V} (h : G.Adj u v) :
    IsPar G ℓ u v ∨ IsPar G ℓ v u := by
  by_cases hp : IsPar G ℓ v u
  · exact Or.inr hp
  · exact Or.inl ⟨h, ((ho v).2 u h.symm hp).symm⟩

lemma not_isPar_both {u v : V} (h₁ : IsPar G ℓ u v) (h₂ : IsPar G ℓ v u) : False :=
  fin3_not_both _ _ h₁.2 h₂.2

/-- Conditions 1 and 2 of correct block labels imply condition 3. -/
lemma midAt_of {v : V} (h₁ : HeadAt G ℓ v) (h₂ : TailAt t G ℓ v) : MidAt t G ℓ v := by
  unfold HeadAt at h₁; unfold TailAt at h₂; unfold MidAt
  rw [← h₁, ← h₂]
  cases (ℓ v).b <;> simp

end Basic

/-! ### Soundness of correct labels (Proposition 16, `⇐`) -/

section Sound

variable {V : Type*} {t : ℕ} {G : SimpleGraph V} {ℓ : V → AcLab}

open Classical in
/-- The parent of `v` (or `v` itself if `v` is a root). -/
noncomputable def parFn (G : SimpleGraph V) (ℓ : V → AcLab) (v : V) : V :=
  if h : ∃ u, IsPar G ℓ v u then h.choose else v

lemma parFn_eq (ho : OrientCorrect G ℓ) {v u : V} (h : IsPar G ℓ v u) : parFn G ℓ v = u := by
  have hex : ∃ u, IsPar G ℓ v u := ⟨u, h⟩
  rw [parFn, dite_eq_left_of_eq_true (eq_true hex)]
  exact (ho v).1 _ _ hex.choose_spec h

/-- A chain of parents `a ← ⋯ ← b` (with `a` an ancestor of `b`) is obtained by iterating
`parFn`. -/
lemma transGen_parFn (ho : OrientCorrect G ℓ) {a b : V}
    (h : Relation.TransGen (fun u v => IsPar G ℓ v u) a b) :
    ∃ m, 0 < m ∧ (parFn G ℓ)^[m] b = a ∧
      ∀ i < m, IsPar G ℓ ((parFn G ℓ)^[i] b) ((parFn G ℓ)^[i + 1] b) := by
  induction h with
  | single h =>
    refine ⟨1, one_pos, by simp [parFn_eq ho h], fun i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    simpa [parFn_eq ho h] using h
  | tail _ hyz ih =>
    obtain ⟨m, hm, hma, hi⟩ := ih
    refine ⟨m + 1, by omega, ?_, fun i hi' => ?_⟩
    · rw [Function.iterate_succ_apply, parFn_eq ho hyz, hma]
    · rcases i with _ | i
      · simpa [parFn_eq ho hyz] using hyz
      · simp only [Function.iterate_succ_apply, parFn_eq ho hyz]
        exact hi i (by omega)

/-- Along a sequence of successive parents, an oriented path ending at `z s` is the segment
`z (s + n - 1), …, z s`. -/
lemma orientedPath_eq_of_parents (ho : OrientCorrect G ℓ) {z : ℕ → V}
    (hz : ∀ s, IsPar G ℓ (z s) (z (s + 1))) :
    ∀ (B : List V) (s : ℕ), OrientedPath G ℓ B → B.getLast? = some (z s) →
      B = (List.range B.length).map fun i => z (s + B.length - 1 - i)
  | [], _, _, h => by simp at h
  | [x], s, _, h => by simp at h; simp [h]
  | x :: y :: B, s, hB, h => by
    unfold OrientedPath at hB
    rw [List.isChain_cons_cons] at hB
    have ih := orientedPath_eq_of_parents ho hz (y :: B) s hB.2 (by simpa using h)
    have hy : y = z (s + (B.length + 1) - 1) := by
      have := congrArg List.head? ih
      simpa [List.range_succ_eq_map] using this
    have hx : x = z (s + B.length + 1) := by
      have := hz (s + (B.length + 1) - 1)
      rw [← hy] at this
      rw [(ho y).1 _ _ hB.1 this]
      congr 1
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, hx]
    simp only [List.length_cons] at ih
    rw [ih]
    simp only [List.length_map, List.length_range, List.cons.injEq]
    refine ⟨by congr 1, List.map_congr_left fun i hi => ?_⟩
    simp only [Function.comp_apply]
    congr 1; omega

/-- The segment of blocks above position `S`: `[z (S + t), …, z (S + 1)]`. -/
def segBlock (t : ℕ) (z : ℕ → V) (S : ℕ) : List V := (List.range t).map fun i => z (S + t - i)

lemma segBlock_orientedPath {z : ℕ → V} (hz : ∀ s, IsPar G ℓ (z s) (z (s + 1))) (S : ℕ) :
    OrientedPath G ℓ (segBlock t z S) := by
  unfold OrientedPath segBlock
  rw [List.isChain_map, List.isChain_range]
  intro i hi
  have := hz (S + t - (i + 1))
  rwa [show S + t - (i + 1) + 1 = S + t - i by omega] at this

/-- **No oriented cycle.** Under correct labels (in fact orientation, conditions 1, 2, 4 of the
block labels and condition 2 of the distance labels suffice), there is no periodic sequence of
successive parents. -/
lemma no_periodic_parents (ht : 1 ≤ t) (hc : Correct t G ℓ) {z : ℕ → V}
    (hz : ∀ s, IsPar G ℓ (z s) (z (s + 1))) {m : ℕ} (hm : 0 < m)
    (hper : ∀ s, z (s + m) = z s) : False := by
  obtain ⟨ho, hb, -, -, hd⟩ := hc
  have hpath := orientedPath_eq_of_parents ho hz
  -- a head on the cycle
  obtain ⟨l, hl, hlast, -, h, hh, hhead⟩ := (hb (z 0)).2.2.2
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, (ℓ (z s₀)).b = .head := by
    rw [hpath l 0 hl hlast] at hh
    cases hlen : l.length with
    | zero => simp [hlen] at hh
    | succ n =>
      rw [hlen] at hh
      simp [List.range_succ_eq_map] at hh
      exact ⟨_, hh ▸ hhead⟩
  -- heads repeat with period `t`
  have hheads : ∀ j, (ℓ (z (s₀ + j * t))).b = .head := by
    intro j
    induction j with
    | zero => simpa using hs₀
    | succ j ih =>
      set S := s₀ + j * t
      have htail : (ℓ (z (S + 1))).b = .tail := by
        obtain h1 | ⟨u, hu, hut⟩ := ((hb (z S)).1).1 ih
        · exact absurd ⟨_, hz S⟩ h1
        · rwa [(ho _).1 _ _ (hz S) hu]
      obtain ⟨B, ⟨hBl, hB, h, hh, hhead⟩, hBlast⟩ := ((hb (z (S + 1))).2.1).1 htail
      rw [hpath B (S + 1) hB hBlast, hBl] at hh
      cases t with
      | zero => omega
      | succ t =>
        simp [List.range_succ_eq_map] at hh
        rw [← hh] at hhead
        rwa [show s₀ + (j + 1) * (t + 1) = S + 1 + (t + 1) - 1 by simp [S]; ring_nf]
  -- the blocks `C j = segBlock t z (s₀ + j * t)`
  have hblock : ∀ j, IsBlock t G ℓ (segBlock t z (s₀ + j * t)) := by
    intro j
    refine ⟨by simp [segBlock], segBlock_orientedPath hz _, ?_⟩
    cases t with
    | zero => omega
    | succ t =>
      refine ⟨z (s₀ + (j + 1) * (t + 1)), ?_, hheads (j + 1)⟩
      simp [segBlock, List.range_succ_eq_map]
      congr 1; ring
  have hparent : ∀ j, IsParentBlock G ℓ (segBlock t z (s₀ + (j + 1) * t))
      (segBlock t z (s₀ + j * t)) := by
    intro j
    cases t with
    | zero => omega
    | succ t =>
      refine ⟨z (s₀ + (j + 1) * (t + 1) + 1), ?_, z (s₀ + (j + 1) * (t + 1)), ?_, hz _⟩
      · simp [segBlock, List.range_succ, List.getLast?_append]
        congr 1; omega
      · simp [segBlock, List.range_succ_eq_map]
        congr 1; ring
  have hval : ∀ j, blockVal ℓ (segBlock t z s₀) =
      blockVal ℓ (segBlock t z (s₀ + j * t)) + j * t := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [ih, hd _ _ (hblock (j + 1)) (hblock j) (hparent j)]
      ring
  have hperm : ∀ k s, z (s + k * m) = z s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => intro s; rw [show s + (k + 1) * m = s + k * m + m by ring, hper, ih]
  have hCm : segBlock t z (s₀ + m * t) = segBlock t z s₀ := by
    unfold segBlock
    refine List.map_congr_left fun i hi => ?_
    rw [show s₀ + m * t + t - i = s₀ + t - i + t * m by
      have := List.mem_range.1 hi; rw [Nat.mul_comm]; omega, hperm t]
  have := hval m
  rw [hCm] at this
  have : 0 < m * t := Nat.mul_pos hm ht
  omega

/-- **Proposition 16, `⇐`.** A finite graph admitting a correct acyclicity labelling (`t ≥ 1`) is
acyclic. Colours and condition 1 of the distance labels are not needed. -/
theorem isAcyclic_of_correct [Finite V] (ht : 1 ≤ t) (hc : Correct t G ℓ) : G.IsAcyclic := by
  have ho := hc.1
  set r : V → V → Prop := fun u v => IsPar G ℓ v u
  have hirr : ∀ x, ¬ Relation.TransGen r x x := by
    intro x hx
    obtain ⟨m, hm, hmx, hi⟩ := transGen_parFn ho hx
    have hper : Function.IsPeriodicPt (parFn G ℓ) m x := hmx
    refine no_periodic_parents ht hc (z := fun s => (parFn G ℓ)^[s] x) (fun s => ?_) hm
      (fun s => by rw [Function.iterate_add_apply, hmx])
    rw [← hper.iterate_mod_apply s, ← hper.iterate_mod_apply (s + 1)]
    have := hi (s % m) (Nat.mod_lt _ hm)
    rwa [show (s + 1) % m = (s % m + 1) % m by simp [Nat.add_mod],
      hper.iterate_mod_apply (s % m + 1)]
  -- rank: number of ancestors
  let f : V → ℕ := fun v => {u | Relation.TransGen r u v}.ncard
  have hlt : ∀ {v u}, IsPar G ℓ v u → f u < f v := by
    intro v u h
    refine Set.ncard_lt_ncard ⟨fun y hy => Relation.TransGen.tail hy h, fun hsub => ?_⟩
      (Set.toFinite _)
    exact hirr u (hsub (Relation.TransGen.single h))
  refine isAcyclic_of_rank f (fun u v h => ?_) (fun v u u' h h' hu hu' => ?_)
  · rcases isPar_or_isPar ho h with h | h
    · exact (hlt h).ne'
    · exact (hlt h).ne
  · have hp : ∀ {x}, G.Adj v x → f x < f v → IsPar G ℓ v x := fun {x} hx hfx => by
      rcases isPar_or_isPar ho hx with h | h
      · exact h
      · exact absurd (hlt h) (by omega)
    exact (ho v).1 _ _ (hp h hu) (hp h' hu')

end Sound

/-! ### Completeness: the honest labels (Proposition 16, `⇒`) -/

section Complete

variable {V : Type*} {t w : ℕ} {G : SimpleGraph V} {d0 : V → ℕ}

/-- `d0` is a depth function of a rooted spanning forest of `G` along which `G` is a forest:
adjacent nodes have depths differing by one, a node has at most one neighbour one level closer,
and every node of positive depth has such a neighbour. -/
structure IsDepth (G : SimpleGraph V) (d0 : V → ℕ) : Prop where
  adj : ∀ ⦃u v⦄, G.Adj u v → d0 u = d0 v + 1 ∨ d0 v = d0 u + 1
  uniq : ∀ ⦃u a b⦄, G.Adj u a → G.Adj u b → d0 a + 1 = d0 u → d0 b + 1 = d0 u → a = b
  exists_par : ∀ v, d0 v ≠ 0 → ∃ u, G.Adj v u ∧ d0 u + 1 = d0 v

/-- Honest block label of a node at depth `n`. -/
def honestB (t n : ℕ) : BLab :=
  if n % t = 0 then .head else if n % t = t - 1 then .tail else .mid

/-- The honest labels of the proof of Proposition 16, for a depth function `d0` and share width
`w`: `a = d0 mod 3`, `b` by `d0 mod t`, `c = ⌊d0 / t⌋ mod 2`, and `d(v)` is the
`(d0(v) mod t)`-th `w`-bit chunk (least significant first) of the depth of the head of `v`'s
block. -/
def honestLab (t w : ℕ) (d0 : V → ℕ) (v : V) : AcLab where
  a := ⟨d0 v % 3, Nat.mod_lt _ (by norm_num)⟩
  b := honestB t (d0 v)
  c := decide ((d0 v / t) % 2 = 1)
  d := toBits w (t * (d0 v / t) / 2 ^ (w * (d0 v % t)))

lemma add_mod_eq_self_iff {a i : ℕ} (hi : i < t) : (a + i) % t = i ↔ a % t = 0 := by
  have ht : 0 < t := by omega
  rw [Nat.add_mod, Nat.mod_eq_of_lt hi]
  have hr := Nat.mod_lt a ht
  constructor
  · intro h
    by_contra hne
    by_cases hlt : a % t + i < t
    · rw [Nat.mod_eq_of_lt hlt] at h; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h; omega
  · intro h; rw [h, Nat.zero_add, Nat.mod_eq_of_lt hi]

lemma add_div_eq_of_mod {a i : ℕ} (hi : i < t) (ha : a % t = 0) : (a + i) / t = a / t := by
  have ht : 0 < t := by omega
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero ha
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ ht, Nat.div_eq_of_lt hi,
    Nat.mul_div_cancel _ ht, Nat.zero_add]

lemma honestB_head {n : ℕ} : honestB t n = .head ↔ n % t = 0 := by
  unfold honestB; split_ifs <;> simp_all

lemma honestB_tail (ht : 2 ≤ t) {n : ℕ} : honestB t n = .tail ↔ n % t = t - 1 := by
  unfold honestB; split_ifs <;> simp_all; omega

variable (hd : IsDepth G d0)
include hd

lemma honest_isPar_iff {v u : V} :
    IsPar G (honestLab t w d0) v u ↔ G.Adj v u ∧ d0 u + 1 = d0 v := by
  constructor
  · rintro ⟨h, ha⟩
    refine ⟨h, ?_⟩
    rw [Fin.ext_iff, Fin.val_add] at ha
    simp only [honestLab, Fin.val_one] at ha
    rcases hd.adj h with h' | h' <;> omega
  · rintro ⟨h, e⟩
    refine ⟨h, ?_⟩
    rw [Fin.ext_iff, Fin.val_add]
    simp only [honestLab, Fin.val_one]
    omega

lemma honest_isRoot_iff {v : V} : IsRoot G (honestLab t w d0) v ↔ d0 v = 0 := by
  unfold IsRoot
  simp only [honest_isPar_iff hd, not_exists, not_and]
  constructor
  · intro h; by_contra hne
    obtain ⟨u, hu, e⟩ := hd.exists_par v hne
    exact h u hu e
  · intro h u _ e; omega

lemma honest_orientCorrect : OrientCorrect G (honestLab t w d0) := by
  intro v
  refine ⟨fun u u' hu hu' => ?_, fun x hx hnx => ?_⟩
  · rw [honest_isPar_iff hd] at hu hu'
    exact hd.uniq hu.1 hu'.1 hu.2 hu'.2
  · rw [honest_isPar_iff hd] at hnx
    rcases hd.adj hx with h | h
    · exact absurd ⟨hx, h.symm⟩ hnx
    · rw [Fin.ext_iff, Fin.val_add]
      simp only [honestLab, Fin.val_one]
      omega

/-- Depths along an oriented path increase by one. -/
lemma honest_map_depth :
    ∀ (l : List V) (h : V), OrientedPath G (honestLab t w d0) l → l.head? = some h →
      l.map d0 = (List.range l.length).map (d0 h + ·)
  | [], _, _, hh => by simp at hh
  | [x], h, _, hh => by simp at hh; simp [hh]
  | x :: y :: l, h, hl, hh => by
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    unfold OrientedPath at hl
    rw [List.isChain_cons_cons] at hl
    have hxy := ((honest_isPar_iff hd).1 hl.1).2
    have ih := honest_map_depth (y :: l) y hl.2 rfl
    rw [List.map_cons, ih]
    simp only [List.length_cons, List.range_succ_eq_map (n := l.length + 1), List.map_cons,
      List.map_map, Nat.add_zero, List.cons.injEq, true_and]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]; omega

lemma honest_mem_depth {l : List V} {h x : V} (hl : OrientedPath G (honestLab t w d0) l)
    (hh : l.head? = some h) (hx : x ∈ l) : ∃ i < l.length, d0 x = d0 h + i := by
  have := List.mem_map_of_mem (f := d0) hx
  rw [honest_map_depth hd l h hl hh] at this
  simpa [eq_comm] using this

lemma honest_last_depth {l : List V} {h x : V} (hl : OrientedPath G (honestLab t w d0) l)
    (hh : l.head? = some h) (hx : l.getLast? = some x) : d0 x = d0 h + (l.length - 1) := by
  have := congrArg List.getLast? (honest_map_depth hd l h hl hh)
  rw [List.getLast?_map, hx, List.getLast?_map, List.getLast?_range] at this
  split_ifs at this with h0
  · simp at this
  · simpa using this

/-- Oriented paths of length `k + 1` up to ancestors at depth `d0 v - k`. -/
lemma honest_exists_path :
    ∀ (k : ℕ) (v : V), k ≤ d0 v → ∃ l, OrientedPath G (honestLab t w d0) l ∧
      l.getLast? = some v ∧ l.length = k + 1 ∧ ∃ h ∈ l.head?, d0 h + k = d0 v
  | 0, v, _ => ⟨[v], List.isChain_singleton _, rfl, rfl, v, rfl, rfl⟩
  | k + 1, v, hk => by
    obtain ⟨u, hu, e⟩ := hd.exists_par v (by omega)
    obtain ⟨l, hl, hlast, hlen, h, hh, hdh⟩ := honest_exists_path k u (by omega)
    refine ⟨l ++ [v], ?_, by simp, by simp [hlen], h, ?_, by omega⟩
    · unfold OrientedPath at hl ⊢
      rw [List.isChain_append]
      refine ⟨hl, List.isChain_singleton _, fun x hx y hy => ?_⟩
      rw [hlast] at hx; cases hx; cases hy
      exact (honest_isPar_iff hd).2 ⟨hu, e⟩
    · rw [List.head?_append, hh]; rfl

/-- The block value of an honest block is the depth of its head (if it fits in `w t` bits). -/
lemma honest_blockVal (hb : ∀ v, d0 v < 2 ^ (w * t)) {B : List V} {h : V}
    (hB : OrientedPath G (honestLab t w d0) B) (hlen : B.length = t) (hh : B.head? = some h)
    (hh0 : d0 h % t = 0) : blockVal (honestLab t w d0) B = d0 h := by
  have hmap : (B.map fun x => (honestLab t w d0 x).d) =
      (B.map d0).map fun n => toBits w (t * (n / t) / 2 ^ (w * (n % t))) := by
    simp [honestLab]
  rw [blockVal, hmap, honest_map_depth hd B h hB hh, List.map_map, hlen]
  trans blockValue ((List.range t).map fun i => toBits w (d0 h / 2 ^ (w * i)))
  swap
  · rw [blockValue_chunks, Nat.mod_eq_of_lt (hb h)]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.1 hi
  simp only [Function.comp_apply]
  rw [add_div_eq_of_mod hi' hh0, (add_mod_eq_self_iff hi').2 hh0,
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hh0)]

/-- **Proposition 16, `⇒` (construction).** The honest labels of a depth function are correct,
for `t ≥ 2` and share width `w` with all depths `< 2^(w t)`. -/
theorem honest_correct (ht : 2 ≤ t) (hb : ∀ v, d0 v < 2 ^ (w * t)) :
    Correct t G (honestLab t w d0) := by
  have ht1 : 1 ≤ t := by omega
  have hbh : ∀ v, ((honestLab t w d0) v).b = .head ↔ d0 v % t = 0 := fun v => honestB_head
  have hbt : ∀ v, ((honestLab t w d0) v).b = .tail ↔ d0 v % t = t - 1 := fun v => honestB_tail ht
  -- blocks
  have hblock : ∀ {B}, IsBlock t G (honestLab t w d0) B → ∃ h ∈ B.head?, d0 h % t = 0 ∧
      ∀ x ∈ B, ∃ i < t, d0 x = d0 h + i := by
    rintro B ⟨hlen, hB, h, hh, hhead⟩
    exact ⟨h, hh, (hbh h).1 hhead, fun x hx => hlen ▸ honest_mem_depth hd hB hh hx⟩
  have hhead : ∀ v, HeadAt G (honestLab t w d0) v := by
    intro v
    unfold HeadAt
    rw [hbh, honest_isRoot_iff hd]
    simp only [honest_isPar_iff hd, hbt]
    constructor
    · intro h0
      by_cases hv : d0 v = 0
      · exact Or.inl hv
      · obtain ⟨u, hu, e⟩ := hd.exists_par v hv
        refine Or.inr ⟨u, ⟨hu, e⟩, ?_⟩
        have := (add_mod_eq_self_iff (t := t) (a := d0 u + 1) (i := t - 1) (by omega)).2 (e ▸ h0)
        rwa [show d0 u + 1 + (t - 1) = d0 u + t by omega, Nat.add_mod_right] at this
    · rintro (h0 | ⟨u, ⟨-, e⟩, hu⟩)
      · simp [h0]
      · have := (add_mod_eq_self_iff (t := t) (a := d0 u + 1) (i := t - 1) (by omega)).1
          (by rw [show d0 u + 1 + (t - 1) = d0 u + t by omega, Nat.add_mod_right, hu])
        rwa [e] at this
  have htail : ∀ v, TailAt t G (honestLab t w d0) v := by
    intro v
    unfold TailAt
    rw [hbt]
    constructor
    · intro hv
      obtain ⟨l, hl, hlast, hlen, h, hh, hdh⟩ :=
        honest_exists_path hd (t - 1) v (hv ▸ Nat.mod_le _ _)
      refine ⟨l, ⟨by omega, hl, h, hh, (hbh h).2 ?_⟩, hlast⟩
      rw [← add_mod_eq_self_iff (i := t - 1) (by omega), hdh, hv]
    · rintro ⟨B, ⟨hlen, hB, h, hh, hhd⟩, hlast⟩
      rw [honest_last_depth hd hB hh hlast, hlen]
      exact (add_mod_eq_self_iff (by omega)).2 ((hbh h).1 hhd)
  refine ⟨honest_orientCorrect hd, fun v => ⟨hhead v, htail v, midAt_of (hhead v) (htail v), ?_⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- condition 4
    obtain ⟨l, hl, hlast, hlen, h, hh, hdh⟩ :=
      honest_exists_path hd (d0 v % t) v (Nat.mod_le _ _)
    refine ⟨l, hl, hlast, ?_, h, hh, (hbh h).2 ?_⟩
    · have := Nat.mod_lt (d0 v) (show 0 < t by omega); simp only; omega
    · rw [← add_mod_eq_self_iff (Nat.mod_lt (d0 v) (show 0 < t by omega)), hdh]
  · -- colours inside a block
    intro B hB x hx y hy
    obtain ⟨h, -, hh0, hmem⟩ := hblock hB
    obtain ⟨i, hi, hxi⟩ := hmem x hx
    obtain ⟨j, hj, hyj⟩ := hmem y hy
    simp only [honestLab, hxi, hyj, add_div_eq_of_mod hi hh0, add_div_eq_of_mod hj hh0]
  · -- colours of parent and child blocks
    rintro B B' hB hB' ⟨x, hx, y, hy, hxy⟩ x' hx' y' hy'
    obtain ⟨h, hh, hh0, hmem⟩ := hblock hB
    obtain ⟨h', hh', hh0', hmem'⟩ := hblock hB'
    rw [hy] at hh'; cases hh'
    have hdx := honest_last_depth hd hB.2.1 hh hx
    have hdy := ((honest_isPar_iff hd).1 hxy).2
    rw [hB.1] at hdx
    obtain ⟨i, hi, hxi⟩ := hmem x' hx'
    obtain ⟨j, hj, hyj⟩ := hmem' y' hy'
    have hq : d0 y / t = d0 h / t + 1 := by
      rw [← hdy, hdx, show d0 h + (t - 1) + 1 = d0 h + t by omega, Nat.add_div_right _ (by omega)]
    simp only [honestLab, hxi, hyj, add_div_eq_of_mod hi hh0, add_div_eq_of_mod hj hh0', hq]
    simp only [ne_eq, decide_eq_decide]
    omega
  · -- distance labels, condition 1
    intro B hB
    obtain ⟨h, hh, hh0, -⟩ := hblock hB
    rw [honest_blockVal hd hb hB.2.1 hB.1 hh hh0]
    constructor
    · intro h0; exact ⟨h, hh, (honest_isRoot_iff hd).2 h0⟩
    · rintro ⟨h', hh', hr⟩
      rw [hh] at hh'; cases hh'
      exact (honest_isRoot_iff hd).1 hr
  · -- distance labels, condition 2
    rintro B B' hB hB' ⟨x, hx, y, hy, hxy⟩
    obtain ⟨h, hh, hh0, -⟩ := hblock hB
    obtain ⟨h', hh', hh0', -⟩ := hblock hB'
    rw [honest_blockVal hd hb hB.2.1 hB.1 hh hh0,
      honest_blockVal hd hb hB'.2.1 hB'.1 hh' hh0']
    rw [hy] at hh'; cases hh'
    have hdx := honest_last_depth hd hB.2.1 hh hx
    have hdy := ((honest_isPar_iff hd).1 hxy).2
    rw [hB.1] at hdx
    omega

end Complete

/-! ### Forests: depth to the root of the component, Proposition 16 -/

section Forest

variable {V : Type*} {G : SimpleGraph V}

/-- The depth of `v` in a BFS forest: distance to a fixed representative (root) of the connected
component of `v`. -/
noncomputable def forestDepth (G : SimpleGraph V) (v : V) : ℕ :=
  G.dist (G.connectedComponentMk v).out v

lemma reachable_out (v : V) : G.Reachable (G.connectedComponentMk v).out v :=
  ConnectedComponent.eq.1 (G.connectedComponentMk v).out_eq

lemma out_eq_of_adj {u v : V} (h : G.Adj u v) :
    (G.connectedComponentMk u).out = (G.connectedComponentMk v).out := by
  rw [ConnectedComponent.eq.2 h.reachable]

/-- In a forest, `forestDepth` is a depth function. -/
lemma isDepth_forestDepth (hG : G.IsAcyclic) : IsDepth G (forestDepth G) := by
  refine ⟨fun u v h => ?_, fun u a b ha hb hda hdb => ?_, fun v hv => ?_⟩
  · unfold forestDepth
    rw [out_eq_of_adj h]
    set s := (G.connectedComponentMk v).out
    have hv : G.Reachable s v := reachable_out v
    have hu : G.Reachable s u := hv.trans h.symm.reachable
    have h1 := hu.dist_le_dist_add_one_of_adj h
    have h2 := hv.dist_le_dist_add_one_of_adj h.symm
    have hp := mod_two_eq_of_colorable hG.colorable_two
      (mem_walkSet_succ_of_adj hu.mem_walkSet_dist h) hv.mem_walkSet_dist
    omega
  · unfold forestDepth at hda hdb
    rw [← out_eq_of_adj ha] at hda
    rw [← out_eq_of_adj hb] at hdb
    set s := (G.connectedComponentMk u).out
    have hu : G.Reachable s u := reachable_out u
    exact hG.eq_of_dist_add_one ha.symm hb.symm (hu.trans ha.reachable)
      (hu.trans hb.reachable) hda hdb
  · unfold forestDepth at hv ⊢
    set s := (G.connectedComponentMk v).out with hs
    have hr : G.Reachable s v := reachable_out v
    have hne : v ≠ s := fun he => hv (by rw [he, SimpleGraph.dist_self])
    obtain ⟨-, h⟩ := hr.bfsParent_spec
    obtain ⟨hadj, hd⟩ := h hne
    refine ⟨G.bfsParent s v, hadj, ?_⟩
    rw [← out_eq_of_adj hadj, ← hs]
    exact hd

lemma forestDepth_lt_card [Finite V] (v : V) : forestDepth G v < Nat.card V := by
  have := Fintype.ofFinite V
  obtain ⟨p, hp, hlen⟩ := (reachable_out (G := G) v).exists_path_of_dist
  rw [forestDepth, ← hlen, Nat.card_eq_fintype_card]
  exact hp.length_lt

/-- The share width `⌈⌈log₂ n⌉ / t⌉` of the honest labels on `n`-node graphs. -/
def shareWidth (t n : ℕ) : ℕ := (Nat.clog 2 n + t - 1) / t

lemma lt_two_pow_shareWidth (ht : 1 ≤ t) {n m : ℕ} (hm : m < n) :
    m < 2 ^ (shareWidth t n * t) := by
  have h1 : Nat.clog 2 n ≤ shareWidth t n * t := by
    have := Nat.lt_div_mul_add (a := Nat.clog 2 n + t - 1) (show 0 < t by omega)
    unfold shareWidth; omega
  exact lt_of_lt_of_le (lt_of_lt_of_le hm (Nat.le_pow_clog (by norm_num) n))
    (Nat.pow_le_pow_right (by norm_num) h1)

/-- The honest labelling of a forest (roots: fixed representatives of the components), with
share width `⌈⌈log₂ n⌉ / t⌉`. -/
noncomputable def honestLabels (t : ℕ) (G : SimpleGraph V) : V → AcLab :=
  honestLab t (shareWidth t (Nat.card V)) (forestDepth G)

lemma honestLabels_correct [Finite V] (ht : 2 ≤ t) (hG : G.IsAcyclic) :
    Correct t G (honestLabels t G) :=
  honest_correct (isDepth_forestDepth hG) ht fun v =>
    lt_two_pow_shareWidth (by omega) (forestDepth_lt_card v)

/-- **Proposition 16** (with condition 4 of the block labels read as `k ≤ t`, and `t ≥ 2`): a
finite graph is acyclic iff it admits a correct acyclicity labelling. -/
theorem prop16 [Finite V] {t : ℕ} (ht : 2 ≤ t) :
    G.IsAcyclic ↔ ∃ ℓ : V → AcLab, Correct t G ℓ :=
  ⟨fun hG => ⟨_, honestLabels_correct ht hG⟩,
    fun ⟨_, hc⟩ => isAcyclic_of_correct (by omega) hc⟩

end Forest

/-! ### Statement-level findings -/

section Findings

variable {V : Type*} {G : SimpleGraph V} {ℓ : V → AcLab}

/-- Condition 4 of the block labels as printed (`k < t`) is unsatisfiable for `t = 2` as soon as
there is an edge: it forces every node to be a head, while an edge makes one endpoint a non-root
child whose parent is a head, not a tail (condition 1). -/
theorem correctLiteral_two_no_edges (hc : CorrectLiteral 2 G ℓ) (u v : V) : ¬ G.Adj u v := by
  intro huv
  obtain ⟨ho, hb, -, -⟩ := hc
  have hhead : ∀ x, (ℓ x).b = .head := by
    intro x
    obtain ⟨l, -, hlast, hlen, h, hh, hhd⟩ := (hb x).2.2.2
    match l, hlen, hlast, hh with
    | [y], _, hlast, hh => simp at hlast hh; rw [← hlast, hh]; exact hhd
    | [], _, hlast, _ => simp at hlast
  have key : ∀ x y, IsPar G ℓ x y → False := by
    intro x y hxy
    rcases ((hb x).1).1 (hhead x) with hr | ⟨p, -, hp⟩
    · exact hr ⟨y, hxy⟩
    · rw [hhead p] at hp; cases hp
  rcases isPar_or_isPar ho huv with h | h
  · exact key _ _ h
  · exact key _ _ h

/-- **Proposition 16 fails as printed.** The path on two vertices is acyclic but has no
correct labelling in the literal sense (condition 4 with `k < t`) for `t = 2`. -/
theorem not_correctLiteral_path :
    (⊤ : SimpleGraph (Fin 2)).IsAcyclic ∧ ¬ ∃ ℓ, CorrectLiteral 2 (⊤ : SimpleGraph (Fin 2)) ℓ := by
  refine ⟨isAcyclic_of_rank (fun i => i.val) (fun u v h => ?_) (fun v u u' _ _ hu hu' => ?_), ?_⟩
  · exact fun e => h.ne (Fin.ext e)
  · ext; omega
  · rintro ⟨ℓ, hc⟩
    exact correctLiteral_two_no_edges hc 0 1 (by decide)

/-- For `t = 1` Proposition 16 fails even with the corrected condition 4: a node would have to be
both a head (condition 4: it is its own block of length 1) and a tail (condition 2). So no
nonempty graph has a correct labelling. -/
theorem correct_one_isEmpty (hc : Correct 1 G ℓ) : IsEmpty V := by
  refine ⟨fun v => ?_⟩
  obtain ⟨-, hb, -, -⟩ := hc
  obtain ⟨-, htail, -, l, hl, hlast, hlen, h, hh, hhd⟩ := hb v
  have hvh : (ℓ v).b = .head := by
    match l, hlen, hlast, hh with
    | [y], _, hlast, hh => simp at hlast hh; rw [← hlast, hh]; exact hhd
    | [], _, hlast, _ => simp at hlast
  have : (ℓ v).b = .tail :=
    htail.2 ⟨[v], ⟨rfl, List.isChain_singleton _, v, rfl, hvh⟩, rfl⟩
  rw [hvh] at this; cases this

end Findings

end Podc.SpaceTimeVerification
