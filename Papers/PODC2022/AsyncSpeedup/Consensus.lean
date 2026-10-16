import Papers.PODC2022.AsyncSpeedup.Local
import Mathlib.Data.Fintype.Card

/-!
# Impossibility of consensus via fixed points of the closure (Sections 3.3 and 4.3)

* `consensus_closure_subset` — the closure of binary consensus w.r.t. IIS is binary consensus
  (only the inclusion `Δ' ⊆ Δ` is needed; the other one is the Remark after Definition 2).
* `corollary1` — **Corollary 1**: binary consensus is not wait-free solvable in IIS (`n ≥ 2`).
* `consensus3` — the relaxed task of the proof of Corollary 2 (agreement only when at least three
  processes participate), `consensus3_closure_subset` — it is a fixed point of IIS + test&set.
* `corollary2` — **Corollary 2**: for `n ≥ 3`, binary consensus is not solvable in IIS + test&set.
* `twoConsensus_iisTS` — Figure 4 / Section 4.3: for two processes consensus *is* solvable in one
  round of IIS + test&set (so `n ≥ 3` is needed in Corollary 2, and the model is not vacuous).
-/

namespace AsyncSpeedup

open Podc.Iterated

variable {P : Type} [DecidableEq P]

/-- Binary consensus: every participant decides the input of some participant (validity), and all
participants decide the same value (agreement). This is the paper's task
(`Δ(σ) = {proj_I τ₀, proj_I τ₁}` for mixed inputs and `{σ}` otherwise). -/
def consensus (P : Type) : Task P Bool Bool where
  Inp := {σ | σ.1.Nonempty}
  Δ I x := {y | ∀ i ∈ I, (∃ j ∈ I, y i = x j) ∧ ∀ j ∈ I, y i = y j}

/-- The task `Π` of the proof of Corollary 2: validity, and agreement only if at least three
processes participate. -/
def consensus3 (P : Type) : Task P Bool Bool where
  Inp := {σ | σ.1.Nonempty}
  Δ I x := {y | ∀ i ∈ I, (∃ j ∈ I, y i = x j) ∧ (3 ≤ I.card → ∀ j ∈ I, y i = y j)}

/-- In zero rounds, a process decides its own input in consensus-like tasks. -/
lemma zero_round_valid {A B : Type} {M : Model P A B} {T : Task P Bool Bool}
    {alg : Alg P Bool A B Bool 0} (h : Solves M T alg)
    (hInp : ∀ (i : P) (x : P → Bool), ({i}, x) ∈ T.Inp)
    (hval : ∀ (i : P) x, ∀ y ∈ T.Δ {i} x, y i = x i) (i : P) (v : Bool) : alg.dec i v = v := by
  obtain ⟨y, hy, hdec⟩ := zero_round_solo h (hInp i (fun _ => v))
  exact hdec.trans (hval i _ y hy)

/-- The closure of binary consensus w.r.t. IIS is binary consensus (the inclusion needed). -/
theorem consensus_closure_subset (I : Finset P) (x : P → Bool) :
    (closure iis (consensus P)).Δ I x ⊆ (consensus P).Δ I x := by
  rintro τ ⟨hV, g, hg⟩ i hi
  refine ⟨?_, fun j hj => ?_⟩
  · obtain ⟨y, hy, hyi⟩ := hV i hi
    obtain ⟨j, hj, hyj⟩ := (hy i hi).1
    exact ⟨j, hj, hyi ▸ hyj⟩
  · by_cases hij : i = j
    · rw [hij]
    obtain ⟨b, c, ⟨y₁, hy₁, h₁i, h₁j⟩, ⟨y₂, hy₂, h₂j, h₂i⟩, ⟨y₃, hy₃, h₃i, h₃j⟩⟩ :=
      iis_local_path hg hi hj hij
    rw [← h₁i, (hy₁ i hi).2 j hj, h₁j, ← h₂j, (hy₂ j hj).2 i hi, h₂i, ← h₃i, (hy₃ i hi).2 j hj,
      h₃j]

/-- Binary consensus is a fixed point of the closure w.r.t. IIS: `CL_IIS(Π) = Π`. -/
theorem consensus_fixedPoint (I : Finset P) (x : P → Bool) :
    (closure iis (consensus P)).Δ I x = (consensus P).Δ I x :=
  Set.Subset.antisymm (consensus_closure_subset I x) (closure_contains iis _)

/-- **Corollary 1**: binary consensus is impossible to solve in the wait-free IIS model (for any
number of rounds), as soon as there are two processes. -/
theorem corollary1 (hP : ∃ p q : P, p ≠ q) (t : ℕ) : ¬ Solvable iis (consensus P) t := by
  intro h
  obtain ⟨alg, halg⟩ := solvable_zero_of_fixedPoint iis_wellFormed iis_allowsSolo iis_soloDet
    iis_extendable (fun I x _ => consensus_closure_subset I x) h
  obtain ⟨p, q, hpq⟩ := hP
  have hval := zero_round_valid halg (fun i x => Finset.singleton_nonempty i)
    (fun i x y hy => by
      obtain ⟨j, hj, hyj⟩ := (hy i (Finset.mem_singleton_self i)).1
      rw [Finset.mem_singleton] at hj; rwa [hj] at hyj)
  obtain ⟨y, hy, hdec⟩ := halg {p, q} (fun l => decide (l = q)) (Finset.insert_nonempty _ _) _
    Reach.zero
  have h1 := hdec p (by simp)
  have h2 := hdec q (by simp)
  have hag := (hy p (by simp)).2 q (by simp)
  rw [hval] at h1 h2
  simp [hpq] at h1 h2
  rw [h1, h2] at hag
  exact Bool.false_ne_true hag

/-- The relaxed task of Corollary 2 is a fixed point of IIS augmented with test&set. -/
theorem consensus3_closure_subset (I : Finset P) (x : P → Bool) :
    (closure iisTS (consensus3 P)).Δ I x ⊆ (consensus3 P).Δ I x := by
  rintro τ ⟨hV, g, hg⟩ i hi
  refine ⟨?_, fun hI j hj => ?_⟩
  · obtain ⟨y, hy, hyi⟩ := hV i hi
    obtain ⟨j, hj, hyj⟩ := (hy i hi).1
    exact ⟨j, hj, hyi ▸ hyj⟩
  · by_cases hij : i = j
    · rw [hij]
    obtain ⟨k, hk, hki, hkj⟩ := exists_third hI i j
    obtain ⟨γ, ⟨y₁, hy₁, h₁i, h₁k⟩, ⟨y₂, hy₂, h₂j, h₂k⟩⟩ :=
      local_triangle iisTS_allowsSolo iisTS_soloDet hg hi hj hk hij
        (tsPat_mem (rk := rank3 i j k) hi rank3_zero _) (tsPat_mem (rk := rank3 j i k) hj rank3_zero _)
        (rank3_solo hi) (rank3_solo hj) (rank3_third (Ne.symm hki) (Ne.symm hkj))
        (by simp [tsPat, hki, hkj])
    rw [← h₁i, (hy₁ i hi).2 hI k hk, h₁k, ← h₂k, ← (hy₂ j hj).2 hI k hk, h₂j]

/-- The relaxed task of Corollary 2 is a fixed point of IIS + test&set. -/
theorem consensus3_fixedPoint (I : Finset P) (x : P → Bool) :
    (closure iisTS (consensus3 P)).Δ I x = (consensus3 P).Δ I x :=
  Set.Subset.antisymm (consensus3_closure_subset I x) (closure_contains iisTS _)

/-- **Corollary 2**: for `n ≥ 3` processes, binary consensus is impossible to solve in the
wait-free IIS model augmented with test&set. -/
theorem corollary2 (hP : ∃ p q r : P, p ≠ q ∧ p ≠ r ∧ q ≠ r) (t : ℕ) :
    ¬ Solvable iisTS (consensus P) t := by
  intro h
  have h3 : Solvable iisTS (consensus3 P) t :=
    h.mono (Task.Easier.of_subset le_rfl fun I x _ y hy i hi =>
      ⟨(hy i hi).1, fun _ => (hy i hi).2⟩)
  obtain ⟨alg, halg⟩ := solvable_zero_of_fixedPoint iisTS_wellFormed iisTS_allowsSolo
    iisTS_soloDet iisTS_extendable (fun I x _ => consensus3_closure_subset I x) h3
  obtain ⟨p, q, r, hpq, hpr, hqr⟩ := hP
  have hval := zero_round_valid halg (fun i x => Finset.singleton_nonempty i)
    (fun i x y hy => by
      obtain ⟨j, hj, hyj⟩ := (hy i (Finset.mem_singleton_self i)).1
      rw [Finset.mem_singleton] at hj; rwa [hj] at hyj)
  obtain ⟨y, hy, hdec⟩ := halg {p, q, r} (fun l => decide (l = q)) (Finset.insert_nonempty _ _) _
    Reach.zero
  have hcard : 3 ≤ ({p, q, r} : Finset P).card := by
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr]),
      Finset.card_insert_of_notMem (by simp [hqr]), Finset.card_singleton]
  have h1 := hdec p (by simp)
  have h2 := hdec q (by simp)
  have hag := (hy p (by simp)).2 hcard q (by simp)
  rw [hval] at h1 h2
  simp [hpq] at h1 h2
  rw [h1, h2] at hag
  exact Bool.false_ne_true hag

/-! ### Figure 4: two-process consensus in one round with test&set -/

/-- In a two-element type, two elements different from `i` are equal. -/
lemma eq_of_card_two [Fintype P] (hP : Fintype.card P = 2) {i j w : P} (hj : j ≠ i)
    (hw : w ≠ i) : j = w := by
  by_contra hjw
  have : ({i, j, w} : Finset P).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hj.symm, hw.symm]),
      Finset.card_insert_of_notMem (by simp [hjw]), Finset.card_singleton]
  have := Finset.card_le_univ ({i, j, w} : Finset P)
  omega

/-- The algorithm of Figure 4: the winner of test&set decides its own input, the loser decides the
input of the other process (which it has necessarily seen). -/
def tsConsAlg [Fintype P] : Alg P Bool Unit Bool Bool 1 where
  inp _ _ _ := ()
  dec i w :=
    let w' : Bool × (P → Option Bool) := w
    if w'.1 then (w'.2 i).getD false else decide (∃ j, j ≠ i ∧ w'.2 j = some true)

/-- **Section 4.3 / Figure 4**: two-process (binary) consensus is solvable in one round of IIS
augmented with test&set. -/
theorem twoConsensus_iisTS [Fintype P] (hP : Fintype.card P = 2) :
    Solves iisTS (consensus P) (tsConsAlg (P := P)) := by
  intro I x _ W hW
  obtain ⟨V, p, hV, ⟨hIS, w, hw, hwI, hout⟩, rfl⟩ := reach_succ_iff.1 hW
  rw [reach_zero_iff] at hV
  subst V
  have hdec : ∀ i ∈ I, tsConsAlg.dec i (step (r := 0) (X := Bool) x p i) = x w := by
    intro i hi
    simp only [tsConsAlg, step, hout i hi]
    by_cases hiw : i = w
    · subst hiw; simp only [(hIS.1 i hi).1, decide_true, ite_true]; rfl
    · simp only [hiw, decide_false, Bool.false_eq_true, ite_false]
      have : (∃ j, j ≠ i ∧ (if j ∈ p.sees i then some (x j) else none) = some true) ↔
          x w = true := by
        constructor
        · rintro ⟨j, hji, hj⟩
          rw [eq_of_card_two hP hji (Ne.symm hiw)] at hj
          simpa [hwI i hi] using hj
        · intro h; exact ⟨w, Ne.symm hiw, by simp [hwI i hi, h]⟩
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact this
  refine ⟨fun _ => x w, fun i _ => ⟨⟨w, hw, rfl⟩, fun _ _ => rfl⟩, hdec⟩

end AsyncSpeedup
