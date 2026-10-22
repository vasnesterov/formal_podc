import Papers.PODC2018.SparseColoringLB.Torus

/-!
# Theorem 1.5: no `o(n)`-round 4-colouring of planar graphs

The paper: the toroidal triangulations of Figure 3 (`torus w`, `n = 3w + 1` vertices) are not
4-colourable (Fisk), and their balls of radius `≤ (n-1)/6 - 3` are planar, so Observation 2.4 gives
Theorem 1.5.

We use, as planar graphs, the triangulated cylinders `cutTorus w c` obtained from `torus w` by deleting
the edges between two consecutive columns `c` and `c + 1` (a strip of `w + 1` nested triangles; it is
planar, see `differencies.md`: planarity itself is not formalized). Seen from a node at distance
`≥ r` from the cut (and `> r` on one side), `torus w` and `cutTorus w c` have the same `r`-ball.
Choosing the cut opposite to a given edge works as soon as `w ≥ 2r + 3`, i.e. `n ≥ 6r + 10`:
`theorem_1_5`.
-/

namespace Podc.SparseColoringLB

open SimpleGraph

variable {w : ℕ}

/-- The edges between column `c` and column `c + 1`. -/
def cutRel (c : ℕ) : TV w → TV w → Prop
  | some (_, j), some (_, j') => (j : ℕ) = c ∧ (j' : ℕ) = c + 1
  | _, _ => False

/-- The triangulated cylinder obtained from `torus w` by deleting the edges between columns `c`
and `c + 1` (`c + 2 ≤ w`). It is planar (a strip of nested triangles). -/
def cutTorus (w c : ℕ) : SimpleGraph (TV w) :=
  SimpleGraph.fromRel fun p q => torusRel w p q ∧ ¬ cutRel c p q

lemma cutTorus_le (w c : ℕ) : cutTorus w c ≤ torus w := by
  intro p q h
  rw [cutTorus, fromRel_adj] at h
  rw [torus, fromRel_adj]
  exact ⟨h.1, h.2.imp And.left And.left⟩

/-- The column of a vertex (`a_w` is put in column `w - 1`). -/
def colOf : TV w → ℕ
  | some (_, j) => j
  | none => w - 1

lemma colOf_lt (hw : 0 < w) (p : TV w) : colOf p < w := by
  cases p with
  | none => simp [colOf]; omega
  | some p => exact p.2.isLt

/-- Position along the cylinder `cutTorus w c`: columns `c + 1, …, w - 1, 0, …, c` get positions
`0, …, w - 1`. -/
def pos (c : ℕ) (p : TV w) : ℕ :=
  if c < colOf p then colOf p - c - 1 else colOf p + w - c - 1

lemma pos_lt (hc : c + 2 ≤ w) (p : TV w) : pos c p < w := by
  have := colOf_lt (by omega) p
  unfold pos; split_ifs <;> omega

/-- Adjacency in the torus, by columns: same column, next column, or `w - 1 → 0`. -/
def colStep (w : ℕ) (a b : ℕ) : Prop := b = a ∨ b = a + 1 ∨ (a + 1 = w ∧ b = 0)

lemma torusRel_colStep {p q : TV w} (h : torusRel w p q) : colStep w (colOf p) (colOf q) := by
  match p, q, h with
  | some (i, j), some (i', j'), h =>
    simp only [colOf, colStep]
    rcases h with ⟨rfl, -⟩ | ⟨h, -⟩ | ⟨h1, h2, -⟩
    · left; rfl
    · right; left; omega
    · right; right; omega
  | none, some (i, j), h =>
    simp only [colOf, colStep]
    rcases h with h | h
    · left; omega
    · right; right; have := j.isLt; omega

lemma torus_adj_colStep {p q : TV w} (h : (torus w).Adj p q) :
    colStep w (colOf p) (colOf q) ∨ colStep w (colOf q) (colOf p) := by
  rw [torus, fromRel_adj] at h
  rcases h.2 with h | h
  · exact Or.inl (torusRel_colStep h)
  · exact Or.inr (torusRel_colStep h)

lemma cutRel_pos {c : ℕ} (hc : c + 2 ≤ w) {p q : TV w} (h : cutRel c p q) :
    pos c p = w - 1 ∧ pos c q = 0 := by
  match p, q, h with
  | some (i, j), some (i', j'), h =>
    simp only [cutRel] at h
    obtain ⟨h1, h2⟩ := h
    have := j.isLt
    refine ⟨?_, ?_⟩
    · simp only [pos, colOf, h1, lt_irrefl, ite_false]; omega
    · simp only [pos, colOf, h2, lt_add_one, ite_true]; omega

/-- Along an edge of the torus that is not cut, the position changes by at most one. -/
lemma pos_colStep {c : ℕ} (hc : c + 2 ≤ w) {a b : ℕ} (ha : a < w) (hb : b < w)
    (h : colStep w a b) (hcut : ¬ (a = c ∧ b = c + 1)) :
    (if c < b then b - c - 1 else b + w - c - 1) ≤ (if c < a then a - c - 1 else a + w - c - 1) + 1 ∧
    (if c < a then a - c - 1 else a + w - c - 1) ≤ (if c < b then b - c - 1 else b + w - c - 1) + 1
    := by
  unfold colStep at h
  split_ifs <;> omega

lemma cutTorus_pos_lip (hc : c + 2 ≤ w) : ∀ p q : TV w, (cutTorus w c).Adj p q →
    pos c q ≤ pos c p + 1 ∧ pos c p ≤ pos c q + 1 := by
  intro p q h
  rw [cutTorus, fromRel_adj] at h
  have hp := colOf_lt (by omega) p
  have hq := colOf_lt (by omega) q
  rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := torusRel_colStep h1
    refine pos_colStep hc hp hq this ?_
    rintro ⟨ha, hb⟩
    apply h2
    match p, q with
    | some (i, j), some (i', j') => exact ⟨ha, hb⟩
    | none, some (i', j') =>
      simp only [colOf] at ha hb
      exfalso; omega
    | some _, none => simp [torusRel] at h1
    | none, none => simp [torusRel] at h1
  · have := torusRel_colStep h1
    refine (pos_colStep hc hq hp this ?_).symm
    rintro ⟨ha, hb⟩
    apply h2
    match q, p with
    | some (i, j), some (i', j') => exact ⟨ha, hb⟩
    | none, some (i', j') =>
      simp only [colOf] at ha hb
      exfalso; omega
    | some _, none => simp [torusRel] at h1
    | none, none => simp [torusRel] at h1

/-- Seen from a node `u` at position `r ≤ pos u ≤ w - 1 - r` (one inequality strict), the torus and
the cylinder cut between columns `c` and `c + 1` have the same labelled ball of radius `r`. -/
lemma ballAgree_torus_cut {c r : ℕ} (hc : c + 2 ≤ w) (u : TV w) (h₁ : r ≤ pos c u)
    (h₂ : r ≤ w - 1 - pos c u) (h₃ : r < pos c u ∨ r < w - 1 - pos c u) :
    BallAgree (torus w) (cutTorus w c) u r := by
  have hlip₁ : ∀ p q : TV w, (cutTorus w c).Adj p q → pos c q ≤ pos c p + 1 :=
    fun p q h => (cutTorus_pos_lip hc p q h).1
  have hlip₂ : ∀ p q : TV w, (cutTorus w c).Adj p q →
      w - 1 - pos c q ≤ w - 1 - pos c p + 1 := fun p q h => by
    have := (cutTorus_pos_lip hc p q h).2; omega
  have end0 : ∀ a : TV w, pos c a = 0 → ((pos c u : ℕ) : ℕ∞) ≤ (cutTorus w c).edist u a := by
    intro a ha
    have := le_add_edist_of_lipschitz hlip₁ a u
    rw [ha, edist_comm] at this
    simpa using this
  have endl : ∀ a : TV w, pos c a = w - 1 →
      ((w - 1 - pos c u : ℕ) : ℕ∞) ≤ (cutTorus w c).edist u a := by
    intro a ha
    have := le_add_edist_of_lipschitz hlip₂ a u
    rw [ha, Nat.sub_self, edist_comm] at this
    simpa using this
  -- a deleted edge joins positions `w - 1` and `0`
  have del : ∀ a b, (torus w).Adj a b → ¬ (cutTorus w c).Adj a b →
      (pos c a = w - 1 ∧ pos c b = 0) ∨ (pos c b = w - 1 ∧ pos c a = 0) := by
    intro a b hab hn
    rw [torus, fromRel_adj] at hab
    rcases hab.2 with h | h
    · by_cases hcut : cutRel c a b
      · exact Or.inl (cutRel_pos hc hcut)
      · exfalso
        rw [cutTorus, fromRel_adj] at hn
        exact hn ⟨hab.1, Or.inl ⟨h, hcut⟩⟩
    · by_cases hcut : cutRel c b a
      · exact Or.inr (cutRel_pos hc hcut)
      · exfalso
        rw [cutTorus, fromRel_adj] at hn
        exact hn ⟨hab.1, Or.inr ⟨h, hcut⟩⟩
  apply ballAgree_of_le (cutTorus_le w c)
  · intro a b hab hn
    rcases del a b hab hn with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact le_trans (by exact_mod_cast h₂) (endl a h1)
    · exact le_trans (by exact_mod_cast h₁) (end0 a h2)
  · intro a b hab hn
    rcases del a b hab hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases h₃ with h | h
      · exact Or.inr (lt_of_lt_of_le (by exact_mod_cast h) (end0 b h2))
      · exact Or.inl (lt_of_lt_of_le (by exact_mod_cast h) (endl a h1))
    · rcases h₃ with h | h
      · exact Or.inl (lt_of_lt_of_le (by exact_mod_cast h) (end0 a h2))
      · exact Or.inr (lt_of_lt_of_le (by exact_mod_cast h) (endl b h1))

/-- For an edge `{p, q}` of the torus with `q` in the same or the next column, there is a cut far
from it: `p` sits at position `r` or `r + 1`, `q` at most one further, and `{p, q}` is an edge of the
cylinder. -/
lemma exists_cut {r : ℕ} (hw : 2 * r + 3 ≤ w) {p q : TV w} (hpq : (torus w).Adj p q)
    (hstep : colStep w (colOf p) (colOf q)) :
    ∃ c, c + 2 ≤ w ∧ (pos c p = r ∨ pos c p = r + 1) ∧
      (pos c q = pos c p ∨ pos c q = pos c p + 1) ∧ (cutTorus w c).Adj p q := by
  have hp := colOf_lt (by omega) p
  have hq := colOf_lt (by omega) q
  obtain ⟨c, hc, hpp⟩ : ∃ c, c + 2 ≤ w ∧ (pos c p = r ∨ pos c p = r + 1) := by
    by_cases h1 : colOf p = r
    · refine ⟨w - 2, by omega, ?_⟩
      simp only [pos]; split_ifs <;> omega
    · by_cases h2 : r + 1 ≤ colOf p
      · refine ⟨colOf p - r - 1, by omega, ?_⟩
        simp only [pos]; split_ifs <;> omega
      · refine ⟨colOf p + w - r - 1, by omega, ?_⟩
        simp only [pos]; split_ifs <;> omega
  have hpq' : pos c q = pos c p ∨ pos c q = pos c p + 1 := by
    simp only [pos] at hpp ⊢
    unfold colStep at hstep
    split_ifs at hpp ⊢ <;> omega
  refine ⟨c, hc, hpp, hpq', ?_⟩
  rw [torus, fromRel_adj] at hpq
  rw [cutTorus, fromRel_adj]
  refine ⟨hpq.1, hpq.2.imp (fun h => ⟨h, fun hc' => ?_⟩) (fun h => ⟨h, fun hc' => ?_⟩)⟩
  · have := cutRel_pos hc hc'; omega
  · have := cutRel_pos hc hc'; omega

/-- **Theorem 1.5** of the paper ("no distributed algorithm can 4-colour every `n`-vertex planar
graph in `o(n)` rounds"), with explicit constants. Every `r`-round algorithm on `n ≥ 6r + 10`
identifiers fails to 4-colour some `n`-node network that is a copy of a triangulated cylinder
`cutTorus (2r + 3) c` (planar, `6r + 10` nodes) plus isolated nodes. Hence 4-colouring all `n`-node
planar graphs needs at least `(n - 10)/6` rounds. -/
theorem theorem_1_5 {n r : ℕ} (hn : 6 * r + 10 ≤ n) {V : Type*} [Fintype V]
    (hV : Fintype.card V = n) {A : SimpleGraph V → V → Fin 4} (hA : BallLocal r A) :
    ∃ c, ∃ G : SimpleGraph V, IsCopyOf (cutTorus (2 * r + 3) c) G ∧
      ∃ u v, G.Adj u v ∧ A G u = A G v := by
  by_contra hcon
  push Not at hcon
  set w := 2 * r + 3 with hw
  obtain ⟨e₂⟩ : Nonempty (TV w ↪ V) :=
    Function.Embedding.nonempty_of_card_le (by simp [hV]; omega)
  have := coloring_of_views_family hA (𝒢 := {G | ∃ c, IsCopyOf (cutTorus w c) G})
    (fun G ⟨c, hG⟩ u v huv => hcon c G hG u v huv) e₂ (K := torus w) fun x y hxy => ?_
  · exact (torus_not_colorable (w := w) (by omega)).false this.some
  have key : ∀ p q, (torus w).Adj p q → colStep w (colOf p) (colOf q) →
      ∃ G ∈ {G | ∃ c, IsCopyOf (cutTorus w c) G}, G.Adj (e₂ p) (e₂ q) ∧
        BallAgree G ((torus w).map e₂) (e₂ p) r ∧ BallAgree G ((torus w).map e₂) (e₂ q) r := by
    intro p q hpq hstep
    obtain ⟨c, hc, hp, hq, hadj⟩ := exists_cut (r := r) (by omega) hpq hstep
    have hpl := pos_lt hc p
    refine ⟨_, ⟨c, e₂, rfl⟩, (map_adj_apply (f := e₂)).2 hadj, ?_, ?_⟩
    · exact (BallAgree.map e₂ (ballAgree_torus_cut hc p (by omega) (by omega) (by omega))).symm
    · exact (BallAgree.map e₂ (ballAgree_torus_cut hc q (by omega) (by omega) (by omega))).symm
  rcases torus_adj_colStep hxy with h | h
  · exact key _ _ hxy h
  · obtain ⟨G, hG, hadj, h3, h4⟩ := key _ _ hxy.symm h
    exact ⟨G, hG, hadj.symm, h4, h3⟩

end Podc.SparseColoringLB
