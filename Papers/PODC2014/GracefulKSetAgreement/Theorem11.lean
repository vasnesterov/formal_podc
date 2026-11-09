import Papers.PODC2014.GracefulKSetAgreement.Alg4
import Papers.PODC2014.GracefulKSetAgreement.Concrete

/-!
# Theorem 11 is false

**Theorem 11** of the paper claims that Algorithm 4 (with Algorithm 1) solves `k`-set agreement
under `VSRC(n, 3D + H) + MAJINF(k)`. We give two concrete runs with `k = 1` in which two different
values are decided (`theorem11_false`, `theorem11_false'`). In both, the adversary conditions are
verified against the definitions of `Model.lean` (`VSRCkAll`, the strong reading of Definition 15)
and `MajInf.lean` (`MAJINF`, with the charitable reading of Definition 19), and the decisions are
computed by evaluating the algorithm `alg4` of `Alg4.lean` in the kernel.

Round indices are 0-based (index `t` = paper round `t + 1`).

* **Scenario 1** (`n = 5`, `D = H = 1`; processes `a, b, c, y, s` = `0..4`, inputs `1..5`).
  `{a}` is a root in paper rounds 1–3, `{b}` in 5–7, `{c}` in 5–8, `{s}` from round 10 on; all
  other root components last one round. `K = {{a}}`, `{a} ↪m {b}`, `{a} ↪m {c}`, `{b} ↪m {s}`.
  `a` decides `1`; `b` and `c` lock `({b}, 1, 7)` and `({c}, 1, 7)`. The lock of `c` reaches `s`
  via `y` in round 8, *during* the stability interval of `{c}`, which Definition 19 does not
  count, so `IS({c}, {s}) = ∅`. In `s`'s `GetLock` the two most recent locks tie (same
  multiplicity, same `τ = 7`), and the fallback of line 32 takes the maximum value of *all* known
  locks: `s` decides its own input `5`.
* **Scenario 2** (`n = 8`, `D = 2`, `H = 1`; processes `a, h, 1, 2, 3, x, y, z` = `0..7`, inputs
  `1..8`). `{a}` is a root in paper rounds 1–5 (`K = {{a}}`), `R_suc = {1, 2, 3}` (a directed
  3-cycle) from round 7 on, and `{a} ↪m R_suc` with `IS({a}, R_suc) = {1, 2}`. `a` decides `1`.
  The virtual lock of `h` is known to all three members of `R_suc`, the lock of `{a}` only to two;
  `GetLock` ranks by multiplicity first, so `R_suc` locks `h`'s input `2` (as the unique most
  frequent, most recent lock: no tie, no fallback) and decides `2`.
-/

namespace Podc.GracefulKSetAgreement

open Cslib.HeardOf Cslib.DynNet BoolPat

namespace Scenario1

/-- Edges `(u, v)` (`v` receives `u`) of round index `t`; processes `a, b, c, y, s` are
`0, 1, 2, 3, 4`; constant from index `9` (paper round 10) on. -/
def edgesAt : ℕ → List (ℕ × ℕ)
  | 0 | 1 | 2 => [(0, 1), (0, 2), (0, 3), (0, 4)]
  | 3 => [(0, 1), (0, 2), (0, 3), (0, 4), (3, 0)]
  | 4 | 5 | 6 => [(1, 3), (1, 4), (2, 3), (2, 4), (3, 0)]
  | 7 => [(4, 1), (1, 3), (2, 3), (3, 0), (3, 4)]
  | 8 => [(3, 4), (4, 3), (3, 0), (0, 2), (3, 1)]
  | _ => [(4, 0), (4, 1), (4, 2), (4, 3)]

/-- Boolean adjacency of the run. -/
def gB (t : ℕ) (u v : Fin 5) : Bool := (edgesAt t).contains (u.val, v.val)

/-- The communication pattern of Scenario 1. -/
abbrev ρ : ℕ → Graph (Fin 5) := ρB gB

theorem evConst : EvConst gB 9 where
  ge t ht := by
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 9 := ⟨t - 9, by omega⟩
    rfl
  closed t ht := by interval_cases t <;> decide

theorem roots_nine : rootsB (gB 9) = [{4}] := by decide

/-- `ρ ∈ VSRC(n, 3D + H)` for `n = 5`, `D = H = 1`: every root component is a clique in its round
(so all VSRCs are `1`-bounded); window: paper rounds `10..13`, root `{s}`. -/
theorem mem_VSRCkAll : ρ ∈ VSRCkAll 1 1 5 (3 * 1 + 1) :=
  mem_VSRCkAll_of evConst le_rfl le_rfl (by omega) roots_nine
    (by intro x hx; interval_cases x <;> decide) (by decide)

/-- The maximal VSRCs stable for at least two rounds: `{a}`, `{b}`, `{c}`, `{s}` in the paper
rounds `1..3`, `5..7`, `5..8`, `10..∞`. -/
def vs : List (FV 5) := [({0}, 0, some 2), ({1}, 4, some 6), ({2}, 4, some 7), ({4}, 9, none)]

theorem Vd_sub_vs : ∀ X ∈ Vd ρ (1 + 1), ∃ Z ∈ vs, X = toV Z :=
  Vd_sub evConst vs
    (by intro a ha m hm; interval_cases a <;> interval_cases m <;> decide)
    (by
      intro F hF a ha
      rw [roots_nine, List.mem_singleton] at hF
      subst hF
      interval_cases a <;> decide)

theorem vs_mem : ∀ Z ∈ vs, toV Z ∈ Vd ρ (2 * 1 + 1) := by
  intro Z hZ
  simp only [vs, List.mem_cons, List.not_mem_nil, or_false] at hZ
  rcases hZ with rfl | rfl | rfl | rfl
  · exact mem_Vd_fin evConst _ 0 2 (by omega) (by omega) (by decide) (by decide) (by decide)
  · exact mem_Vd_fin evConst _ 4 6 (by omega) (by omega) (by decide) (by decide) (by decide)
  · exact mem_Vd_fin evConst _ 4 7 (by omega) (by omega) (by decide) (by decide) (by decide)
  · exact mem_Vd_inf evConst _ 9 le_rfl (by decide) (by decide)

/-- `ρ ∈ MAJINF(1)` with `K = {{a}[1,3]}`: `{a} ↪m {b}`, `{a} ↪m {c}`, `{b} ↪m {s}`. -/
theorem mem_MAJINF : ρ ∈ MAJINF 1 1 :=
  mem_MAJINF_of vs_mem Vd_sub_vs [({0}, 0, some 2)] (by decide) le_rfl (by decide)

/-- Inputs `x_a = 1, x_b = 2, x_c = 3, x_y = 4, x_s = 5`. -/
def x : Fin 5 → ℕ := ![1, 2, 3, 4, 5]

/-- `a` decides `1` (in paper round `4`, via its lock `({a}, 1, 3)`). -/
theorem decides_a : (alg4 5 1).Decides x ρ 0 1 :=
  ⟨4, by rw [Alg.run_eq_cconf _ (hρB gB)]; decide +kernel⟩

/-- `s` decides `5` (in paper round `13`, via its lock `({s}, 5, 12)`). -/
theorem decides_s : (alg4 5 1).Decides x ρ 4 5 :=
  ⟨13, by rw [Alg.run_eq_cconf _ (hρB gB)]; decide +kernel⟩

/-- The lock of `s` (created in paper round 12) is `({s}, 5, 12)`: the fallback value. -/
example : (cconf (alg4 5 1).step gB ((alg4 5 1).initC x) 12 4).lock = some ⟨16, 5, 12⟩ := by
  decide +kernel

end Scenario1

namespace Scenario2

/-- Edges `(u, v)` of round index `t`; processes `a, h, 1, 2, 3, x, y, z` are `0, …, 7`;
constant from index `6` (paper round 7) on. -/
def edgesAt : ℕ → List (ℕ × ℕ)
  | 0 | 1 => [(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)]
  | 2 | 3 => [(5, 2), (6, 3), (7, 4), (5, 1)]
  | 4 => [(2, 5), (5, 2), (3, 6), (6, 3), (4, 7), (7, 4), (0, 1)]
  | 5 => [(1, 0), (0, 1), (0, 2), (2, 5), (3, 6), (6, 3), (4, 7), (7, 4)]
  | _ => [(2, 3), (3, 4), (4, 2), (2, 0), (2, 1), (2, 5), (3, 6), (4, 7)]

/-- Boolean adjacency of the run. -/
def gB (t : ℕ) (u v : Fin 8) : Bool := (edgesAt t).contains (u.val, v.val)

/-- The communication pattern of Scenario 2. -/
abbrev ρ : ℕ → Graph (Fin 8) := ρB gB

theorem evConst : EvConst gB 6 where
  ge t ht := by
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 6 := ⟨t - 6, by omega⟩
    rfl
  closed t ht := by interval_cases t <;> decide +kernel

theorem roots_six : rootsB (gB 6) = [{2, 3, 4}] := by decide +kernel

/-- `ρ ∈ VSRC(n, 3D + H)` for `n = 8`, `D = 2`, `H = 1`. -/
theorem mem_VSRCkAll : ρ ∈ VSRCkAll 2 1 8 (3 * 2 + 1) :=
  mem_VSRCkAll_of evConst (by omega) le_rfl (by omega) roots_six
    (by intro x hx; interval_cases x <;> decide +kernel) (by decide +kernel)

/-- The same run also lies in `VSRC(n, 3D + H)` with `H = D = 2`, so the counterexample does not
rely on `H < D` (the paper assumes `H ≥ D`, p. 23). -/
theorem mem_VSRCkAll_H2 : ρ ∈ VSRCkAll 2 2 8 (3 * 2 + 2) :=
  mem_VSRCkAll_of evConst (by omega) le_rfl (by omega) roots_six
    (by intro x hx; interval_cases x <;> decide +kernel) (by decide +kernel)

/-- The maximal VSRCs stable for at least three rounds: `{a}` in paper rounds `1..5` and
`{1, 2, 3}` from round `7` on. -/
def vs : List (FV 8) := [({0}, 0, some 4), ({2, 3, 4}, 6, none)]

set_option maxHeartbeats 1000000 in
/-- The finite part of `Vd_sub_vs` (36 cases of first and last round). -/
theorem Vd_sub_fin : ∀ a < 6, ∀ m < 6, a + (2 + 1) ≤ m + 1 → ∀ F ∈ rootsB (gB a),
    (∀ t < m + 1, a ≤ t → F ∈ rootsB (gB t)) → (a = 0 ∨ F ∉ rootsB (gB (a - 1))) →
    F ∉ rootsB (gB (m + 1)) → (F, a, some m) ∈ vs := by
  intro a ha m hm hlen
  interval_cases a <;> interval_cases m <;> first | omega | decide +kernel

theorem Vd_sub_vs : ∀ X ∈ Vd ρ (2 + 1), ∃ Z ∈ vs, X = toV Z :=
  Vd_sub evConst vs Vd_sub_fin
    (by
      intro F hF a ha
      rw [roots_six, List.mem_singleton] at hF
      subst hF
      interval_cases a <;> decide +kernel)

theorem vs_mem : ∀ Z ∈ vs, toV Z ∈ Vd ρ (2 * 2 + 1) := by
  intro Z hZ
  simp only [vs, List.mem_cons, List.not_mem_nil, or_false] at hZ
  rcases hZ with rfl | rfl
  · exact mem_Vd_fin evConst _ 0 4 (by omega) (by omega) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact mem_Vd_inf evConst _ 6 le_rfl (by decide +kernel) (by decide +kernel)

/-- `ρ ∈ MAJINF(1)` with `K = {{a}[1,5]}` and `{a} ↪m {1, 2, 3}`. -/
theorem mem_MAJINF : ρ ∈ MAJINF 2 1 :=
  mem_MAJINF_of vs_mem Vd_sub_vs [({0}, 0, some 4)] (by decide +kernel) le_rfl
    (by decide +kernel)

/-- Inputs `1, …, 8` (`x_a = 1`, `x_h = 2`). -/
def x : Fin 8 → ℕ := ![1, 2, 3, 4, 5, 6, 7, 8]

/-- `a` decides `1` (paper round 6). -/
theorem decides_a : (alg4 8 2).Decides x ρ 0 1 :=
  ⟨6, by rw [Alg.run_eq_cconf _ (hρB gB)]; decide +kernel⟩

/-- Process `1` (a member of `R_suc`) decides `2` (paper round 13). -/
theorem decides_1 : (alg4 8 2).Decides x ρ 2 2 :=
  ⟨13, by rw [Alg.run_eq_cconf _ (hρB gB)]; decide +kernel⟩

end Scenario2

open Scenario1 in
/-- **Theorem 11 of [Biely, Robinson, Schmid, Schwarz, Winkler] is false.** Algorithm 4 (with
Algorithm 1), for `n = 5` processes and `D = 1`, does not solve `1`-set agreement (consensus)
under the message adversary `VSRC(n, 3D + H) + MAJINF(1)` with `H = 1` (Definitions 15 and 21,
the latter with the charitable reading of Definition 19): in `Scenario1.ρ`, `a` decides `1` and
`s` decides `5`. -/
theorem theorem11_false :
    ¬ (alg4 5 1).SolvesKSet 1 (VSRCk 1 1 5 (3 * 1 + 1) ∩ MAJINF 1 1) := by
  intro h
  have hmem : ρ ∈ VSRCk 1 1 5 (3 * 1 + 1) ∩ MAJINF 1 1 :=
    ⟨VSRCkAll_subset _ _ _ _ mem_VSRCkAll, mem_MAJINF⟩
  have := (h x ρ hmem).1 {1, 5} (by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact ⟨0, decides_a⟩
    · exact ⟨4, decides_s⟩)
  simp at this

open Scenario2 in
/-- **Theorem 11 is false, without ties or the fallback of line 32**: for `n = 8`, `D = 2`,
`H = 1`, Algorithm 4 does not solve consensus under `VSRC(n, 3D + H) + MAJINF(1)`: in
`Scenario2.ρ`, `a` decides `1` and process `1` decides `2`. -/
theorem theorem11_false' :
    ¬ (alg4 8 2).SolvesKSet 1 (VSRCk 2 1 8 (3 * 2 + 1) ∩ MAJINF 2 1) := by
  intro h
  have hmem : ρ ∈ VSRCk 2 1 8 (3 * 2 + 1) ∩ MAJINF 2 1 :=
    ⟨VSRCkAll_subset _ _ _ _ mem_VSRCkAll, mem_MAJINF⟩
  have := (h x ρ hmem).1 {1, 2} (by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact ⟨0, decides_a⟩
    · exact ⟨2, decides_1⟩)
  simp at this

open Scenario2 in
/-- **Theorem 11 is false also with `H ≥ D`**: the run of `theorem11_false'` with `H = D = 2`
(Algorithm 4 does not depend on `H`). -/
theorem theorem11_false'_H2 :
    ¬ (alg4 8 2).SolvesKSet 1 (VSRCk 2 2 8 (3 * 2 + 2) ∩ MAJINF 2 1) := by
  intro h
  have hmem : ρ ∈ VSRCk 2 2 8 (3 * 2 + 2) ∩ MAJINF 2 1 :=
    ⟨VSRCkAll_subset _ _ _ _ mem_VSRCkAll_H2, mem_MAJINF⟩
  have := (h x ρ hmem).1 {1, 2} (by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact ⟨0, decides_a⟩
    · exact ⟨2, decides_1⟩)
  simp at this

end Podc.GracefulKSetAgreement
