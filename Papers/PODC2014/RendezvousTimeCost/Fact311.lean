import Papers.PODC2014.RendezvousTimeCost.Ring

/-!
# Fact 3.11 of [Miller–Pelc] is false as stated

In the proof of Theorem 3.2 the ring of size `n` is cut into 6 sectors
`P_j = {j n/6, …, (j+1) n/6 - 1}` and time into blocks of `n/6` rounds. Fact 3.11 claims: if at the
beginning of block `B_i` of `α(x, 0, y, n/2)` agent `x` is in `P_j` and `y` in `P_{j+3}`, and all
partial surpluses `surplus(Agg[i..k])` (`i ≤ k ≤ m`) of both aggregate vectors have absolute
value at most 1, then `x` and `y` do not meet between the beginning of `B_i` and of `B_{m+1}`.

The proof says that then `x` stays in `P_{j-1} ∪ P_j ∪ P_{j+1}`. This only holds at block
boundaries: an agent at the end of `P_{j+1}` can enter `P_{j+2}` in the middle of a block and come
back before the block ends. Counterexample with `n = 12` (sectors and blocks of size 2), `i = 1`,
`m = 2`, `j = 0`: `x` starts at node 0 and moves `+1, +1, +1, -1`; `y` starts at node 6 and moves
`-1, -1, -1, +1`. Sectors at the block boundaries (rounds 0, 2, 4): `x` is in `P_0, P_1, P_1`,
`y` in `P_3, P_2, P_2`, so `Agg_x = (1, 0)` and `Agg_y = (-1, 0)`, and all partial surpluses are
`±1`. Yet both agents are at node 3 at the end of round 3.

The behaviour vectors below belong to a correct algorithm for two labels (agent `1` explores the
ring clockwise from round 5 on, agent `0` stays idle from round 5 on), and the first four moves of
both agents survive trimming (`m_x, m_y ≥ 4`), so this is a counterexample in the paper's own
setting. Our proof of Theorem 3.2 (`LowerBoundTime.lean`) repairs the argument with 10 sectors.
-/

namespace Podc.RendezvousTimeCost

namespace Fact311

/-- Agent `0`: `+1, +1, +1, -1`, then idle. -/
def vx (j : ℕ) : SignType := if j < 3 then 1 else if j = 3 then -1 else 0

/-- Agent `1`: `-1, -1, -1, +1`, then explores clockwise for `n - 1 = 11` rounds. -/
def vy (j : ℕ) : SignType := if j < 3 then -1 else if j < 5 then (if j = 3 then 1 else 0)
  else if j < 16 then 1 else 0

/-- The two-label algorithm. -/
def V : Behaviour 2 := ![vx, vy]

/-- Sector index of a node of the 12-ring (sectors of size `n/6 = 2`). -/
def sector (p : ZMod 12) : ℕ := p.val / 2

/-- Position of agent `0` (started at node 0) after `t` rounds. -/
def posx (t : ℕ) : ZMod 12 := 0 + (disp vx t : ZMod 12)

/-- Position of agent `1` (started at node `n/2 = 6`) after `t` rounds. -/
def posy (t : ℕ) : ZMod 12 := 6 + (disp vy t : ZMod 12)

/-- The hypotheses of Fact 3.11 hold for `i = 1`, `m = 2`, `j = 0` (sectors at the beginnings
of blocks `B_1, B_2, B_3`, i.e. after rounds 0, 2, 4), but the agents meet in round 3. -/
theorem fact_3_11_false :
    (sector (posx 0) = 0 ∧ sector (posx 2) = 1 ∧ sector (posx 4) = 1) ∧
    (sector (posy 0) = 3 ∧ sector (posy 2) = 2 ∧ sector (posy 4) = 2) ∧
    Meets 12 V 0 0 1 6 3 := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩ <;> decide

/-- The two-label algorithm is a correct rendezvous algorithm in the 12-ring (every execution
meets within 16 rounds). -/
theorem V_correct : IsRendezvous 12 V := by
  have h : ∀ x y : Fin 2, x ≠ y → ∀ px py : ZMod 12, px ≠ py →
      ∃ t, t < 17 ∧ Meets 12 V x px y py t := by decide
  intro x y hxy px py hp
  obtain ⟨t, -, ht⟩ := h x y hxy px py hp
  exact ⟨t, ht⟩

/-- Some execution of each agent lasts at least 4 rounds, so trimming keeps the first four moves:
`m_0 ≥ 4` and `m_1 ≥ 4`. -/
theorem mx_ge_four : 4 ≤ mx 12 V 0 ∧ 4 ≤ mx 12 V 1 := by
  have hnm : ∀ t, t < 4 → ¬ Meets 12 V 0 0 1 1 t := by decide
  have hex : ∃ t, Meets 12 V 0 0 1 1 t := V_correct 0 1 (by decide) 0 1 (by decide)
  have h4 : 4 ≤ meetTime 12 V 0 0 1 1 := by
    by_contra h
    exact hnm _ (by omega) (meets_meetTime hex)
  constructor
  · exact h4.trans (meetTime_le_mx V (by decide) (by decide))
  · rw [meetTime_comm] at h4
    exact h4.trans (meetTime_le_mx V (by decide) (by decide))

end Fact311

end Podc.RendezvousTimeCost
