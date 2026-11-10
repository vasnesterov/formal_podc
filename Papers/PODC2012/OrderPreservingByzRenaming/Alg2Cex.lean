import Papers.PODC2012.OrderPreservingByzRenaming.Alg2

/-!
# Algorithm 2 of arXiv:1205.0477v1/v2 fails

Both counterexamples are checked for arXiv v2 (`K = 4⌈log t⌉ + 2` vote epochs) and for arXiv v1
(`K = 4⌈log t⌉ + 1`).

**Order preservation and uniqueness fail for `N = 7`, `t = 2`** (`order_false`). The Byzantine
processes play Round 1 of Algorithm 1 as in `ConstTime.lemma_2_false_of_gt_3t` and are silent
afterwards. The initial values of the correct id `10` are `30` at process `0` and `16` elsewhere:
the skew is `14 > Skew₂ = 3t² = 12`. So process `0` rejects (`|newId − V[id].newId| > Skew`) the
votes of all other correct processes, and they reject its vote, in every vote epoch. Process `0`
keeps `newId[10] = 30`, process `1` keeps `newId[11] = 23`, and the outputs are `7` for id `10`
and `6` for id `11` (v2; `8` and `6` for v1). Process `2` (id `12`) also outputs `7`
(resp. `8`).

**The namespace `2N` fails for `N = 4`, `t = 1`** (`namespace_false`). The Byzantine process sends
the fake id `1` to every correct process in Round 1 and echoes `{10, 11, 1, 2}`. The correct
processes (ids `10, 11, 12`) all compute `newId = 4, 5, 9, 13, 17` for the ids `1, 2, 10, 11, 12`.
In each vote epoch the Byzantine process sends everybody the common vote shifted up by the current
`Skew` and echoes it; every correct process accepts it. Process `2` ends with `newId[12] = 145/8`
(v2) and outputs `⌈(145/8) / (4 − 1 − 3/4)⌉ = 9 > 2N = 8` (v1: `⌈(71/4) / (3/2)⌉ = 12`).
-/

namespace Podc.OrderPreservingByzRenaming.Alg2

open Cslib.Byzantine.LockStep

/-- If correct processes `p`, `q` with ids `x p < x q` decide `a ≥ b`, the protocol does not solve
order-preserving renaming. -/
lemma not_solves_of_decides {n t K M : ℕ} {s : Scenario (Fin n) ℕ Msg} (hs : s.Reliable)
    (hbyz : s.byz ∈ (atMost t : AdvStructure (Fin n))) (hinj : Set.InjOn s.input s.honest)
    {p q : Fin n} (hp : p ∉ s.byz) (hq : q ∉ s.byz) (hpq : s.input p < s.input q) {a b : ℕ}
    (ha : Decides ⊤ (alg2 n t K) s p a) (hb : Decides ⊤ (alg2 n t K) s q b) (hab : b ≤ a) :
    ¬ Solves (⊤ : SimpleGraph (Fin n)) (alg2 n t K) (atMost t) (OPRenaming M) := by
  intro h
  obtain ⟨-, -, -, hord⟩ := h s hbyz hs ⟨hinj, fun _ _ => trivial⟩
  have := hord p hp q hq a b ha hb hpq
  omega

namespace Cex7

/-- Byzantine processes. -/
def F : Finset (Fin 7) := {5, 6}

/-- Ids: process `j` has id `10 + j`. -/
def x (j : Fin 7) : ℕ := j.val + 10

/-- The adversary: Round 1 of Algorithm 1 as in `ConstTime.Cex7`, then silence. -/
def adv (r : ℕ) (b p : Fin 7) : Option Msg :=
  match r with
  | 0 => if b.val = 5 then (if p.val ≤ 2 then some (.base (.ident 1)) else some (.base (.ident 2)))
         else if p.val = 0 then some (.base (.ident 2))
         else if p.val ≤ 3 then some (.base (.ident 3)) else none
  | 1 => if p.val = 0 then some (.base (.echo {10, 11, 12, 1, 2, 3, 4})) else none
  | _ => none

/-- The scenario. -/
def scen : Scenario (Fin 7) ℕ Msg where
  byz := ↑F
  input := x
  adv := adv

lemma hF : ∀ j, j ∈ scen.byz ↔ j ∈ F := fun _ => Iff.rfl

/-- v2 (`K = 6`): processes `0` and `1` decide `7` and `6`. -/
lemma out_v2 :
    (Int.ceil ((run 7 2 F x adv 14 0).newId 10 / ((7 : ℕ) - (2 : ℕ) - skew 7 2 7))).toNat = 7 ∧
    (Int.ceil ((run 7 2 F x adv 14 1).newId 11 / ((7 : ℕ) - (2 : ℕ) - skew 7 2 7))).toNat = 6 := by
  decide +kernel

/-- v1 (`K = 5`): processes `0` and `1` decide `8` and `6`. -/
lemma out_v1 :
    (Int.ceil ((run 7 2 F x adv 12 0).newId 10 / ((7 : ℕ) - (2 : ℕ) - skew 7 2 6))).toNat = 8 ∧
    (Int.ceil ((run 7 2 F x adv 12 1).newId 11 / ((7 : ℕ) - (2 : ℕ) - skew 7 2 6))).toNat = 6 := by
  decide +kernel

end Cex7

/-- **Theorem 8 of arXiv:1205.0477v2 is false (order preservation).** For `N = 7 > 3t`, `t = 2`,
Algorithm 2 with the paper's number of epochs (v2: `K = 4⌈log 2⌉ + 2 = 6`; v1: `K = 5`) does not
solve order-preserving renaming, whatever the namespace: the correct processes with ids `10 < 11`
decide `7 ≥ 6` (v2) and `8 ≥ 6` (v1). -/
theorem order_false :
    7 > 3 * 2 ∧ ∀ M, ¬ Solves (⊤ : SimpleGraph (Fin 7)) (alg2 7 2 6) (atMost 2) (OPRenaming M) ∧
      ¬ Solves (⊤ : SimpleGraph (Fin 7)) (alg2 7 2 5) (atMost 2) (OPRenaming M) := by
  have hs : Cex7.scen.Reliable := fun _ _ _ h => h
  have hbyz : Cex7.scen.byz ∈ (atMost 2 : AdvStructure (Fin 7)) := by
    simp [Cex7.scen, Set.ncard_coe_finset, Cex7.F]
  have hinj : Set.InjOn Cex7.scen.input Cex7.scen.honest := fun p _ q _ h => by
    simpa [Cex7.scen, Cex7.x, Fin.ext_iff] using h
  have h0 : (0 : Fin 7) ∉ Cex7.scen.byz := by simp [Cex7.scen, Cex7.F]
  have h1 : (1 : Fin 7) ∉ Cex7.scen.byz := by simp [Cex7.scen, Cex7.F]
  have hx : Cex7.scen.input 0 < Cex7.scen.input 1 := by simp [Cex7.scen, Cex7.x]
  refine ⟨by norm_num, fun M => ⟨?_, ?_⟩⟩
  · refine not_solves_of_decides hs hbyz hinj h0 h1 hx (a := 7) (b := 6) ?_ ?_ (by norm_num)
    · rw [decides_iff hs Cex7.hF h0]; exact Cex7.out_v2.1.symm
    · rw [decides_iff hs Cex7.hF h1]; exact Cex7.out_v2.2.symm
  · refine not_solves_of_decides hs hbyz hinj h0 h1 hx (a := 8) (b := 6) ?_ ?_ (by norm_num)
    · rw [decides_iff hs Cex7.hF h0]; exact Cex7.out_v1.1.symm
    · rw [decides_iff hs Cex7.hF h1]; exact Cex7.out_v1.2.symm

namespace Cex4

/-- The Byzantine process. -/
def F : Finset (Fin 4) := {3}

/-- Ids: process `j` has id `10 + j`. -/
def x (j : Fin 4) : ℕ := j.val + 10

/-- The common vote after Algorithm 1, shifted by `d`. -/
def shifted (base : List (ℕ × ℚ)) (d : ℚ) : List (ℕ × ℚ) := base.map fun e => (e.1, e.2 + d)

/-- The Byzantine votes of vote epochs 1 and 2: the common vote shifted up by the current `Skew`. -/
def b1 : List (ℕ × ℚ) := shifted [(1, 4), (2, 5), (10, 9), (11, 13), (12, 17)] 3
/-- See `b1`. -/
def b2 : List (ℕ × ℚ) :=
  shifted [(1, 19 / 4), (2, 23 / 4), (10, 39 / 4), (11, 55 / 4), (12, 71 / 4)] (3 / 2)

/-- The adversary. -/
def adv (r : ℕ) (_b _p : Fin 4) : Option Msg :=
  match r with
  | 0 => some (.base (.ident 1))
  | 1 => some (.base (.echo {10, 11, 1, 2}))
  | 2 => some (.vote b1)
  | 3 => some (.echoVotes [b1])
  | 4 => some (.vote b2)
  | 5 => some (.echoVotes [b2])
  | _ => none

/-- The scenario. -/
def scen : Scenario (Fin 4) ℕ Msg where
  byz := ↑F
  input := x
  adv := adv

lemma hF : ∀ j, j ∈ scen.byz ↔ j ∈ F := fun _ => Iff.rfl

/-- v2 (`K = 2`): process `2` (id `12`) decides `9`. -/
lemma out_v2 :
    (Int.ceil ((run 4 1 F x adv 6 2).newId 12 / ((4 : ℕ) - (1 : ℕ) - skew 4 1 3))).toNat = 9 := by
  decide +kernel

/-- v1 (`K = 1`): process `2` decides `12`. -/
lemma out_v1 :
    (Int.ceil ((run 4 1 F x adv 4 2).newId 12 / ((4 : ℕ) - (1 : ℕ) - skew 4 1 2))).toNat = 12 := by
  decide +kernel

end Cex4

/-- **The namespace claim `2N` of arXiv:1205.0477v2 is false.** For `N = 4 > 3t`, `t = 1`,
Algorithm 2 (v2: `K = 2`; v1: `K = 1`) does not solve order-preserving renaming into
`{1, …, 2N}`: the correct process with id `12` decides `9` (v2), resp. `12` (v1). -/
theorem namespace_false :
    4 > 3 * 1 ∧ ¬ Solves (⊤ : SimpleGraph (Fin 4)) (alg2 4 1 2) (atMost 1) (OPRenaming (2 * 4)) ∧
      ¬ Solves (⊤ : SimpleGraph (Fin 4)) (alg2 4 1 1) (atMost 1) (OPRenaming (2 * 4)) := by
  have hs : Cex4.scen.Reliable := fun _ _ _ h => h
  have hbyz : Cex4.scen.byz ∈ (atMost 1 : AdvStructure (Fin 4)) := by
    simp [Cex4.scen, Set.ncard_coe_finset, Cex4.F]
  have hinj : Set.InjOn Cex4.scen.input Cex4.scen.honest := fun p _ q _ h => by
    simpa [Cex4.scen, Cex4.x, Fin.ext_iff] using h
  have h2 : (2 : Fin 4) ∉ Cex4.scen.byz := by simp [Cex4.scen, Cex4.F]
  refine ⟨by norm_num, fun h => ?_, fun h => ?_⟩
  · obtain ⟨-, hval, -⟩ := h Cex4.scen hbyz hs ⟨hinj, fun _ _ => trivial⟩
    have := hval 2 h2 9 ((decides_iff hs Cex4.hF h2 9).2 Cex4.out_v2.symm)
    omega
  · obtain ⟨-, hval, -⟩ := h Cex4.scen hbyz hs ⟨hinj, fun _ _ => trivial⟩
    have := hval 2 h2 12 ((decides_iff hs Cex4.hF h2 12).2 Cex4.out_v1.symm)
    omega

end Podc.OrderPreservingByzRenaming.Alg2
