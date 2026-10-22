import Papers.PODC2017.PPVerification.Threshold

/-!
# Remarks on the proof of Proposition 18

The proof of Proposition 18 (appendix C.1) claims, citing Angluin et al., that the total absolute
value of the non-leaders, `aᵢ = ∑_{q non-leader} Cᵢ(q) · |val(q)|`, is non-increasing along every
execution of `P_thr[T₁]`. This is false: when two leaders meet, the responder becomes a non-leader
and keeps the overflow `g(n, n')`. Example (`c = 1`, `v = 2`, i.e. `v = vmax` whenever all `|aᵢ| ≤ 2`;
this is the case `c > 0` treated in the paper's full proof): `(1,2,0), (1,2,0) ↦ (1,2,0), (0,2,0)`
raises `a` from `0` to `2`. The argument is repaired by ordering the measures lexicographically
with the number of leaders first (which the proof also uses), see `Prop18T1.lean`.

The proof then claims that, once the number of leaders and `a` are constant and no leader is
inconsistent, every non-silent `T₁`-transition has the form `(1,x,1), (0,0,0) ↦ (1,x,1), (0,0,1)`.
This misses the *saturated* interactions `(1, v, 0), (0, n, 1) ↦ (1, v, 0), (0, n, 0)` (`n > 0`) and
`(1, -v, 1), (0, n, 0) ↦ (1, -v, 1), (0, n, 1)` (`n < 0`), which keep the leaders and `a` unchanged
(`saturated_flip`). They flip opinions in one direction only, so a further potential (our `F`)
repairs the argument.
-/

namespace Podc.PPVerification.Threshold

open Cslib.PopulationProtocol

/-- `a(C)`: the total absolute value of the non-leaders. -/
def nonleaderAbs {v : ℤ} (C : Multiset (St v)) : ℕ :=
  (C.map fun s => if s.1 = true then 0 else (valS s).natAbs).sum

/-- The leader `(1, 2, 0)` for `v = 2`. -/
def ldr : St 2 := (true, ⟨2, by norm_num⟩, false)

/-- The paper's claim "`a₀ ≥ a₁ ≥ ⋯`" fails: a single `T₁`-step of `P_thr` (`c = 1`, `v = 2`)
increases the total absolute value of the non-leaders. -/
theorem nonleaderAbs_not_antitone :
    ∃ C C' : Multiset (St 2), MStep (T1 1) C C' ∧ nonleaderAbs C < nonleaderAbs C' := by
  refine ⟨{ldr, ldr}, _, ⟨mainT 1 ldr ldr, ⟨mainT_mem 1 rfl, ?_⟩, le_rfl, rfl⟩, ?_⟩
  · rintro ⟨m, n, -, -, h⟩
    have : ((false, n, true) : St 2) ∈ (mainT 1 ldr ldr).pre := by rw [h]; simp
    simp [Transition.pre, mainT, ldr] at this
  · decide

/-- The non-leader `(0, 1, 1)` for `v = 2`. -/
def nl11 : St 2 := (false, ⟨1, by norm_num⟩, true)

/-- A non-silent `T₁`-transition (`c = 1`, `v = 2`) of a consistent leader `(1, 2, 0)` that keeps
the leaders and the value of the non-leader, and is not of the form claimed in the proof of
Proposition 18: `(1,2,0), (0,1,1) ↦ (1,2,0), (0,1,0)`. -/
theorem saturated_flip :
    mainT 1 ldr nl11 ∈ T1 1 ∧ ¬ (mainT 1 ldr nl11).Silent ∧
      (mainT 1 ldr nl11).post = {ldr, (false, ⟨1, by norm_num⟩, false)} := by
  refine ⟨⟨mainT_mem 1 rfl, ?_⟩, by unfold Transition.Silent; decide, by decide⟩
  rintro ⟨m, n, -, hn, h⟩
  have : ((false, n, true) : St 2) ∈ (mainT 1 ldr nl11).pre := by rw [h]; simp
  simp [Transition.pre, mainT, ldr, nl11] at this
  rw [this] at hn
  simp at hn

end Podc.PPVerification.Threshold
