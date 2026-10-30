import Papers.PODC2025.GraphAlgorithmsPredictions.Basic
import Cslib.Computability.Distributed.Local.Locality

-- CSLib candidate: Cslib/Computability/Distributed/Local/Line.lean (oriented line in the LOCAL model)

/-!
# The oriented line in the LOCAL model

Model of Section 6 of the full version (arXiv:2501.05267) of Boyar–Ellen–Larsen: `n` nodes connected
in a line; every node knows its own identifier and the identifiers of its left and right
neighbours (if they exist). Identifiers are arbitrary natural numbers (no bound `d` is fixed).

Following CSLib's LOCAL locality (`Cslib.Local.IsLocal`), nodes are named by their identifiers: an
instance is an injective placement `id : Fin n ↪ ℕ` of identifiers on positions `0, …, n - 1`
(left to right); the network is `lineG id : SimpleGraph ℕ` (the path, mapped along `id`) and the
input label of node `u` is `lineLab id u = (left neighbour, right neighbour)`. A `T`-round algorithm
is any `f : SimpleGraph ℕ → (ℕ → Lab) → ℕ → β` with `IsLocal T f`.

* `ix id k`: identifier at position `k`.
* `lineG_adj_ix`, `lineLab_ix`: adjacency and labels in terms of positions.
* `exists_pos_of_edist_le`, `exists_pos_of_edist_lt`: a node at distance `≤ m` from position `c`
  sits at a position within `m` of `c`.
* `viewEq_window`: two lines that carry the same identifiers on a window of `2T + 3` consecutive
  positions give the same radius-`T` view to the centre of the window.
-/

namespace Podc.GraphAlgorithmsPredictions

open SimpleGraph Cslib.Local

/-- The initial knowledge of a node of the line besides its own identifier: the identifiers of its
left and right neighbours (`none` at the ends). -/
abbrev Lab := Option ℕ × Option ℕ

section Line

variable {n : ℕ} (id : Fin n ↪ ℕ)

/-- The identifier at position `k` of the line (junk value `0` for `k ≥ n`). -/
def ix (k : ℕ) : ℕ := if h : k < n then id ⟨k, h⟩ else 0

lemma ix_of_lt {k : ℕ} (h : k < n) : ix id k = id ⟨k, h⟩ := by simp [ix, h]

@[simp] lemma ix_fin (i : Fin n) : ix id i = id i := ix_of_lt id i.2

lemma ix_inj {k l : ℕ} (hk : k < n) (hl : l < n) (h : ix id k = ix id l) : k = l := by
  rw [ix_of_lt id hk, ix_of_lt id hl] at h
  exact congrArg Fin.val (id.injective h)

/-- The oriented line with identifiers `id` (position `i` is adjacent to `i ± 1`), as a graph on the
identifiers. -/
def lineG : SimpleGraph ℕ := (pathGraph n).map id

lemma lineG_adj_ix {q : ℕ} (hq : q < n) (y : ℕ) :
    (lineG id).Adj (ix id q) y ↔
      (q + 1 < n ∧ y = ix id (q + 1)) ∨ (0 < q ∧ y = ix id (q - 1)) := by
  unfold lineG
  rw [map_adj]
  constructor
  · rintro ⟨u, v, huv, hu, rfl⟩
    rw [pathGraph_adj] at huv
    have hq' : u.val = q := ix_inj id u.2 hq (by rw [ix_fin, hu])
    rcases huv with h | h
    · exact Or.inl ⟨by omega, by rw [← ix_fin]; congr 1; omega⟩
    · exact Or.inr ⟨by omega, by rw [← ix_fin]; congr 1; omega⟩
  · rintro (⟨h1, rfl⟩ | ⟨h1, rfl⟩)
    · exact ⟨⟨q, hq⟩, ⟨q + 1, h1⟩, by rw [pathGraph_adj]; simp, (ix_of_lt id hq).symm,
        (ix_of_lt id h1).symm⟩
    · exact ⟨⟨q, hq⟩, ⟨q - 1, by omega⟩, by rw [pathGraph_adj]; simp; omega,
        (ix_of_lt id hq).symm, (ix_of_lt id (by omega)).symm⟩

lemma exists_pos_of_lineG_adj {u y : ℕ} (h : (lineG id).Adj u y) : ∃ q < n, u = ix id q := by
  unfold lineG at h
  obtain ⟨u', -, -, rfl, -⟩ := (map_adj _ _ _ _).1 h
  exact ⟨u', u'.2, (ix_fin id u').symm⟩

open Classical in
/-- The input label of node `u`: identifiers of its left and right neighbours. Nodes that are not on
the line get `(none, none)`. -/
noncomputable def lineLab (u : ℕ) : Lab :=
  if h : ∃ q, q < n ∧ ix id q = u then
    ((if 0 < Nat.find h then some (ix id (Nat.find h - 1)) else none),
      (if Nat.find h + 1 < n then some (ix id (Nat.find h + 1)) else none))
  else (none, none)

lemma lineLab_ix {q : ℕ} (hq : q < n) :
    lineLab id (ix id q) =
      ((if 0 < q then some (ix id (q - 1)) else none),
        (if q + 1 < n then some (ix id (q + 1)) else none)) := by
  classical
  have h : ∃ q', q' < n ∧ ix id q' = ix id q := ⟨q, hq, rfl⟩
  have hf : Nat.find h = q := ix_inj id (Nat.find_spec h).1 hq (Nat.find_spec h).2
  unfold lineLab
  simp only [h, ↓reduceDIte, hf]

/-- Positions along a walk change by at most one per step. -/
lemma exists_pos_of_walk {u w : ℕ} (p : (lineG id).Walk u w) :
    ∀ c < n, u = ix id c → ∃ q < n, w = ix id q ∧ q ≤ c + p.length ∧ c ≤ q + p.length := by
  induction p with
  | nil => intro c hc h; exact ⟨c, hc, h, by simp, by simp⟩
  | cons hadj p ih =>
    intro c hc h
    subst h
    rcases (lineG_adj_ix id hc _).1 hadj with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · obtain ⟨q, hq, rfl, h2, h3⟩ := ih (c + 1) h1 rfl
      exact ⟨q, hq, rfl, by simp; omega, by simp; omega⟩
    · obtain ⟨q, hq, rfl, h2, h3⟩ := ih (c - 1) (by omega) rfl
      exact ⟨q, hq, rfl, by simp; omega, by simp; omega⟩

lemma exists_pos_of_edist_le {c : ℕ} (hc : c < n) {w : ℕ} {m : ℕ}
    (h : (lineG id).edist (ix id c) w ≤ m) :
    ∃ q < n, w = ix id q ∧ q ≤ c + m ∧ c ≤ q + m := by
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top (edist_ne_top_of_le_natCast h)
  have hl : p.length ≤ m := by rw [← hp] at h; exact_mod_cast h
  obtain ⟨q, hq, h1, h2, h3⟩ := exists_pos_of_walk id p c hc rfl
  exact ⟨q, hq, h1, by omega, by omega⟩

lemma exists_pos_of_edist_lt {c : ℕ} (hc : c < n) {w : ℕ} {m : ℕ}
    (h : (lineG id).edist (ix id c) w < m) :
    ∃ q < n, w = ix id q ∧ q + 1 ≤ c + m ∧ c + 1 ≤ q + m := by
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top (ne_top_of_lt h)
  have hl : p.length < m := by rw [← hp] at h; exact_mod_cast h
  obtain ⟨q, hq, h1, h2, h3⟩ := exists_pos_of_walk id p c hc rfl
  exact ⟨q, hq, h1, by omega, by omega⟩

end Line

/-- **Window lemma.** If two lines carry the same identifiers on a window of `2T + 3` consecutive
positions (starting at `a` in the first and at `a'` in the second line), then the centre of the
window has the same radius-`T` view in both lines. -/
theorem viewEq_window {n n' : ℕ} (id : Fin n ↪ ℕ) (id' : Fin n' ↪ ℕ) (T a a' : ℕ)
    (ha : a + 2 * T + 2 < n) (ha' : a' + 2 * T + 2 < n')
    (hw : ∀ k ≤ 2 * T + 2, ix id (a + k) = ix id' (a' + k)) :
    ViewEq T (lineG id) (lineLab id) (lineG id') (lineLab id') (ix id (a + T + 1)) := by
  have hw' : ∀ q, a ≤ q → q ≤ a + 2 * T + 2 → ix id q = ix id' (a' + (q - a)) := by
    intro q h1 h2
    have := hw (q - a) (by omega)
    rwa [Nat.add_sub_cancel' h1] at this
  refine ⟨fun w hw0 y => ?_, fun w hw0 => ?_⟩
  · obtain ⟨q, hq, rfl, h1, h2⟩ := exists_pos_of_edist_lt id (c := a + T + 1) (by omega) hw0
    rw [lineG_adj_ix id hq, hw' q (by omega) (by omega), lineG_adj_ix id' (by omega),
      hw' (q + 1) (by omega) (by omega), hw' (q - 1) (by omega) (by omega)]
    have e1 : a' + (q + 1 - a) = a' + (q - a) + 1 := by omega
    have e2 : a' + (q - 1 - a) = a' + (q - a) - 1 := by omega
    rw [e1, e2]
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact Or.inl ⟨by omega, h⟩
      · exact Or.inr ⟨by omega, h⟩
    · rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact Or.inl ⟨by omega, h⟩
      · exact Or.inr ⟨by omega, h⟩
  · obtain ⟨q, hq, rfl, h1, h2⟩ := exists_pos_of_edist_le id (c := a + T + 1) (by omega) hw0
    have c1 : 0 < q := by omega
    have c2 : q + 1 < n := by omega
    have c3 : 0 < a' + (q - a) := by omega
    have c4 : a' + (q - a) + 1 < n' := by omega
    rw [lineLab_ix id hq, hw' q (by omega) (by omega), lineLab_ix id' (by omega),
      hw' (q + 1) (by omega) (by omega), hw' (q - 1) (by omega) (by omega)]
    simp only [c1, c2, c3, c4, ↓reduceIte]
    congr 3 <;> omega

end Podc.GraphAlgorithmsPredictions
