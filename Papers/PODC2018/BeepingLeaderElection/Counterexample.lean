import Papers.PODC2018.BeepingLeaderElection.Algorithm

/-!
# Lemma 1 fails for Algorithm 1 as printed (rule 1 before rule 2)

On the path `0 — 1 — 2 — 3 — 4 — 5 — 6` with identifiers `152, 1, 3, 2, 144, 4, 148`, after 18
diffusion phases of Algorithm 1 with the paper's rule priority, the neighbours `2` and `3` hold

* `prefix_2 = 111111110100110`,
* `prefix_3 = 111111110100100`,

two words of the same length 15 which differ in their 14th bit: Lemma 1 claims that they may only
differ from the 15th bit on.

The mechanism: in phase 18 node `3` holds `1111111101001000` and sees a suspicious neighbour (`4`, holding
`111111110100100`, a proper prefix) and a neighbour (`2`, holding `11111111010011`) that branches higher
two letters before its end. Rule 1 (priority) deletes only one letter, rule 2 would delete two; meanwhile
node `2` appends a bit. With the rule of [Casteigts et al.] (largest deletion) node `3` would hold
`11111111010010`, and Lemma 1 holds (see `Lemma1.lean`).

The configurations after each phase are listed explicitly (`cfg`), and each phase is checked by `decide`.
-/

namespace Podc.BeepingLeaderElection.Counterexample

open Podc.BeepingLeaderElection

/-- The path graph on 7 nodes. -/
def P7 : SimpleGraph (Fin 7) := SimpleGraph.fromRel fun a b => a.val + 1 = b.val

instance : DecidableRel P7.Adj := fun a b => by unfold P7; infer_instance

theorem P7_eq_pathGraph : P7 = SimpleGraph.pathGraph 7 := by
  ext a b
  simp only [P7, SimpleGraph.fromRel_adj, SimpleGraph.pathGraph_adj]
  constructor
  · exact fun h => h.2
  · rintro h; exact ⟨by rintro rfl; omega, h⟩

theorem P7_connected : P7.Connected := P7_eq_pathGraph ▸ SimpleGraph.pathGraph_connected 6

/-- The identifiers. -/
def ids : Fin 7 → ℕ := ![152, 1, 3, 2, 144, 4, 148]

theorem ids_injective : Function.Injective ids := by decide

/-- The configurations after `t` phases (`t ≤ 18`). -/
def cfg : ℕ → Fin 7 → NState
  | 0 => ![⟨[], false, true⟩, ⟨[], false, true⟩, ⟨[], false, true⟩, ⟨[], false, true⟩, ⟨[], false, true⟩, ⟨[], false, true⟩, ⟨[], false, true⟩]
  | 1 => ![⟨[true], false, true⟩, ⟨[true], false, true⟩, ⟨[true], false, true⟩, ⟨[true], false, true⟩, ⟨[true], false, true⟩, ⟨[true], false, true⟩, ⟨[true], false, true⟩]
  | 2 => ![⟨[true, true], false, true⟩, ⟨[true, false], false, true⟩, ⟨[true, true], false, true⟩, ⟨[true, true], false, true⟩, ⟨[true, true], false, true⟩, ⟨[true, true], false, true⟩, ⟨[true, true], false, true⟩]
  | 3 => ![⟨[true, true, true], false, true⟩, ⟨[true, true], false, false⟩, ⟨[true, true, false], false, true⟩, ⟨[true, true, false], false, true⟩, ⟨[true, true, true], false, true⟩, ⟨[true, true, true], false, true⟩, ⟨[true, true, true], false, true⟩]
  | 4 => ![⟨[true, true, true, true], false, true⟩, ⟨[true, true, true], false, false⟩, ⟨[true, true, false, true], false, true⟩, ⟨[true, true, true], false, false⟩, ⟨[true, true, true, true], false, true⟩, ⟨[true, true, true, false], false, true⟩, ⟨[true, true, true, true], false, true⟩]
  | 5 => ![⟨[true, true, true, true, true], false, true⟩, ⟨[true, true, true, true], false, false⟩, ⟨[true, true, false], true, false⟩, ⟨[true, true, true, true], false, false⟩, ⟨[true, true, true, true, true], false, true⟩, ⟨[true, true, true, true], false, false⟩, ⟨[true, true, true, true, true], false, true⟩]
  | 6 => ![⟨[true, true, true, true, true, true], false, true⟩, ⟨[true, true, true, true, true], false, false⟩, ⟨[true, true, true], false, false⟩, ⟨[true, true, true, true, true], false, false⟩, ⟨[true, true, true, true, true, true], false, true⟩, ⟨[true, true, true, true, true], false, false⟩, ⟨[true, true, true, true, true, true], false, true⟩]
  | 7 => ![⟨[true, true, true, true, true, true, true], false, true⟩, ⟨[true, true, true, true, true, true], false, false⟩, ⟨[true, true, true, true], false, false⟩, ⟨[true, true, true, true, true, true], false, false⟩, ⟨[true, true, true, true, true, true, true], false, true⟩, ⟨[true, true, true, true, true, true], false, false⟩, ⟨[true, true, true, true, true, true, true], false, true⟩]
  | 8 => ![⟨[true, true, true, true, true, true, true, true], false, true⟩, ⟨[true, true, true, true, true, true, true], false, false⟩, ⟨[true, true, true, true, true], false, false⟩, ⟨[true, true, true, true, true, true, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true], false, true⟩, ⟨[true, true, true, true, true, true, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true], false, true⟩]
  | 9 => ![⟨[true, true, true, true, true, true, true, true, false], false, true⟩, ⟨[true, true, true, true, true, true, true, true], false, false⟩, ⟨[true, true, true, true, true, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false], false, true⟩, ⟨[true, true, true, true, true, true, true, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false], false, true⟩]
  | 10 => ![⟨[true, true, true, true, true, true, true, true, false, true], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false], false, false⟩, ⟨[true, true, true, true, true, true, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true], false, true⟩]
  | 11 => ![⟨[true, true, true, true, true, true, true, true, false, true, false], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false], false, true⟩]
  | 12 => ![⟨[true, true, true, true, true, true, true, true, false, true, false, false], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false], false, true⟩]
  | 13 => ![⟨[true, true, true, true, true, true, true, true, false, true, false, false, true], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true], false, true⟩]
  | 14 => ![⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, true], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false], false, true⟩]
  | 15 => ![⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, true, false], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false, false], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false, true], false, true⟩]
  | 16 => ![⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, true, false, false], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, true, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false, false, false], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false, true, false], false, true⟩]
  | 17 => ![⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, true, false, false, false], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, true, false, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false, false, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false, false], true, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false, true, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false, true, false, false], false, true⟩]
  | _ => ![⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, true, false, false, false], false, true⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, true, false, false, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, true, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false, false], true, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false, true], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false, true, false, false], false, false⟩, ⟨[true, true, true, true, true, true, true, true, false, true, false, false, true, false, true, false, false], false, true⟩]

theorem phase_cfg (t : ℕ) (ht : t < 18) : phase P7 .paper ids (cfg t) = cfg (t + 1) := by
  interval_cases t <;> decide

theorem run_eq_cfg (t : ℕ) (ht : t ≤ 18) : run P7 .paper ids t = cfg t := by
  induction t with
  | zero => funext v; fin_cases v <;> rfl
  | succ t ih => rw [run, ih (by omega), phase_cfg t (by omega)]

/-- The two neighbours `2` and `3` violate Lemma 1 after 18 phases. -/
theorem not_lemma1_at_18 :
    ¬ Lemma1Holds (run P7 .paper ids 18 2).pre (run P7 .paper ids 18 3).pre := by
  rw [run_eq_cfg 18 le_rfl]; decide

/-- **Lemma 1 is false** for Algorithm 1 as printed (rule 1 has priority over rule 2): there are a
connected network with unique positive identifiers, a phase `t` and two neighbours whose prefixes
violate the conclusion of Lemma 1. -/
theorem lemma_1_false : ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ident : Fin n → ℕ), G.Connected → Function.Injective ident → (∀ v, 0 < ident v) →
    ∀ t u v, G.Adj u v → Lemma1Holds (run G .paper ident t u).pre (run G .paper ident t v).pre :=
  fun h => not_lemma1_at_18 (h 7 P7 ids P7_connected ids_injective (by decide) 18 2 3 (by decide))

end Podc.BeepingLeaderElection.Counterexample
