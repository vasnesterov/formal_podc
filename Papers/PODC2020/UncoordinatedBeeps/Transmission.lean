import Papers.PODC2020.UncoordinatedBeeps.USICode
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Uncoordinated transmission scenarios (Sections 2.2 and 3.1, Theorem 2)

Dufoulon, Burman, Beauquier. *Can Uncoordinated Beeps tell Stories?* PODC 2020.

**Model.** Beeping model with uncoordinated starts on a static graph `G`. Global rounds are integers;
node `u` wakes up in global round `wake u`, and its local round `r_u ≥ 1` is the global round
`g_u(r_u) = wake u + r_u - 1`. In an *uncoordinated transmission scenario* every node `u` starts a
finite set `tx u` of codeword transmissions `(c, s)` (codeword `c` of length `l`, global start round
`s ≥ wake u`); `u` beeps in global round `r` iff some transmission `(c, s) ∈ tx u` has
`c[r - s] = 1`, i.e. a node transmitting several codewords beeps the bitwise OR of them. The
history `H_v` of `v` records in each local round whether `v` or a neighbour beeped. Since a beeping
node is awake and `v` listens only in its awake rounds, beeps are always delivered.

The *conflict* at `v` and global round `r` is the number of distinct codeword transmissions
`(c, s)` started in `v`'s closed neighbourhood within `l - 1` rounds of `r`
(`s ∈ {r - l + 1, …, r + l - 1}`).
-/

namespace Podc.UncoordinatedBeeps

open Word

/-- An uncoordinated transmission scenario with codewords of length `l` on the graph `G`. -/
structure Scenario (V : Type*) (l : ℕ) where
  /-- The (static) communication graph. -/
  G : SimpleGraph V
  /-- The global wake-up round of each node. -/
  wake : V → ℤ
  /-- The codeword transmissions `(codeword, global start round)` started by each node. -/
  tx : V → Finset (Word l × ℤ)
  /-- Nodes only transmit when awake. -/
  tx_awake : ∀ u, ∀ p ∈ tx u, wake u ≤ p.2

namespace Scenario

variable {V : Type*} {l : ℕ} (S : Scenario V l)

/-- The global round `g_v(r_v)` of local round `r_v` of `v` (local rounds start at `1`). -/
def g (v : V) (rv : ℤ) : ℤ := S.wake v + rv - 1

/-- Node `u` beeps in global round `r`. -/
def Beeps (u : V) (r : ℤ) : Prop := ∃ p ∈ S.tx u, p.1.getZ (r - p.2) = true

variable [Fintype V] [DecidableEq V] [DecidableRel S.G.Adj]

/-- The closed neighbourhood `N(v) = {v} ∪ {u | {v, u} ∈ E}`. -/
def nbhd (v : V) : Finset V := Finset.univ.filter fun u => u = v ∨ S.G.Adj v u

/-- The history `H_v[r_v]`: in local round `r_v`, `v` or one of its neighbours beeped. -/
def History (v : V) (rv : ℤ) : Prop := ∃ u ∈ S.nbhd v, S.Beeps u (S.g v rv)

open Classical in
/-- The history factor `H_v[r_v, r_v + l - 1]` as a word of length `l`. -/
noncomputable def historyFactor (v : V) (rv : ℤ) : Word l :=
  fun i => decide (S.History v (rv + (i : ℕ)))

/-- The distinct codeword transmissions started in `N(v)` within `l - 1` rounds of global round
`r`. -/
def windowTx (v : V) (r : ℤ) : Finset (Word l × ℤ) :=
  ((S.nbhd v).biUnion S.tx).filter fun p => r - l < p.2 ∧ p.2 < r + l

/-- The conflict `χ` at `v` and global round `r`. -/
def conflict (v : V) (r : ℤ) : ℕ := (S.windowTx v r).card

theorem mem_windowTx {v : V} {r : ℤ} {p : Word l × ℤ} :
    p ∈ S.windowTx v r ↔ (∃ u ∈ S.nbhd v, p ∈ S.tx u) ∧ r - l < p.2 ∧ p.2 < r + l := by
  simp [windowTx]

/-- The shifted window transmissions `X = {(c, s - r)}` of the proof of Theorem 2. -/
def windowPairs (v : V) (r : ℤ) : Finset (Word l × ℤ) :=
  (S.windowTx v r).image fun p => (p.1, p.2 - r)

theorem mem_windowPairs {v : V} {r : ℤ} {q : Word l × ℤ} :
    q ∈ S.windowPairs v r ↔ (∃ u ∈ S.nbhd v, (q.1, q.2 + r) ∈ S.tx u) ∧ -(l : ℤ) < q.2 ∧ q.2 < l := by
  simp only [windowPairs, Finset.mem_image, mem_windowTx]
  constructor
  · rintro ⟨p, ⟨⟨u, hu, hp⟩, h1, h2⟩, rfl⟩
    refine ⟨⟨u, hu, by simpa using hp⟩, by simp only; omega, by simp only; omega⟩
  · rintro ⟨⟨u, hu, hp⟩, h1, h2⟩
    exact ⟨(q.1, q.2 + r), ⟨⟨u, hu, hp⟩, by simp only; omega, by simp only; omega⟩, by simp⟩

open Classical in
/-- The history factor is the uncoordinated superposition of the window transmissions, shifted
relative to its first round. -/
theorem historyFactor_eq (v : V) (rv : ℤ) :
    S.historyFactor v rv = superpose (S.windowPairs v (S.g v rv)) fun p => shift p.1 p.2 := by
  have hg : ∀ j : ℤ, S.g v (rv + j) = S.g v rv + j := by intro j; simp only [g]; ring
  generalize hr : S.g v rv = r at hg
  funext i
  rw [Bool.eq_iff_iff, superpose_eq_true, historyFactor, decide_eq_true_iff]
  simp only [History, Beeps, mem_windowPairs, hg]
  constructor
  · rintro ⟨u, hu, p, hp, hpr⟩
    have hb := getZ_eq_true_bounds hpr
    refine ⟨(p.1, p.2 - r), ⟨⟨u, hu, by simpa using hp⟩, by simp only; omega,
      by simp only; omega⟩, ?_⟩
    simp only [shift]; convert hpr using 2; ring
  · rintro ⟨q, ⟨⟨u, hu, hq⟩, -⟩, hqr⟩
    refine ⟨u, hu, _, hq, ?_⟩
    simp only [shift] at hqr; convert hqr using 2; ring

/-- **Theorem 2** (with the code given by Definition 3). If all transmitted codewords come from a
`USI(h, k)`-code `C` and the conflict at `v` and local round `r_v` is at most `k`, then the history
factor `H_v[r_v, r_v + l - 1]` contains a codeword `c' ∈ C` iff `c'` was transmitted in `N(v)` starting
exactly in global round `g_v(r_v)`. -/
theorem theorem_2' {C : Finset (Word l)} {h k : ℕ} (hC : IsUSICode' C h k)
    (huses : ∀ u, ∀ p ∈ S.tx u, p.1 ∈ C) (v : V) (rv : ℤ) (hχ : S.conflict v (S.g v rv) ≤ k)
    {c : Word l} (hc : c ∈ C) :
    (S.historyFactor v rv).Contains c ↔ ∃ u ∈ S.nbhd v, (c, S.g v rv) ∈ S.tx u := by
  have hadm : Admissible C (S.windowPairs v (S.g v rv)) := by
    intro q hq
    obtain ⟨⟨u, -, hq⟩, h1, h2⟩ := S.mem_windowPairs.1 hq
    exact ⟨huses u (q.1, q.2 + S.g v rv) hq, by constructor <;> omega⟩
  have key := hC.2 (S.windowPairs v (S.g v rv)) (Finset.card_image_le.trans hχ) hadm c hc
  rw [shift_zero] at key
  rw [historyFactor_eq, key, mem_windowPairs]
  have hl := hC.2.length_pos hc
  simp only [zero_add]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, by omega, by omega⟩

/-- **Theorem 2.** A `USI(h, k)`-code `C` (Definition 2, codeword length `l ≥ 1`) solves an
uncoordinated transmission scenario with conflict `χ ≤ k`: the history factor
`H_v[r_v, r_v + l - 1]` contains `c' ∈ C` iff `c'` was transmitted in `v`'s neighbourhood starting in
global round `g_v(r_v)`. -/
theorem theorem_2 {C : Finset (Word l)} {h k : ℕ} (hl : 0 < l) (hC : IsUSICode C h k)
    (huses : ∀ u, ∀ p ∈ S.tx u, p.1 ∈ C) (v : V) (rv : ℤ) (hχ : S.conflict v (S.g v rv) ≤ k)
    {c : Word l} (hc : c ∈ C) :
    (S.historyFactor v rv).Contains c ↔ ∃ u ∈ S.nbhd v, (c, S.g v rv) ∈ S.tx u :=
  S.theorem_2' ((theorem_1 hl).1 hC) huses v rv hχ hc

end Scenario

end Podc.UncoordinatedBeeps
