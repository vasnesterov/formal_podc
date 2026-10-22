import Mathlib
import Papers.PODC2024.RecoverableConsensus.Defs

/-!
# `n`-recording and `n`-discerning types — combinatorics

Delporte-Gallet, Fatourou, Fauconnier, Ruppert, *When Is Recoverable Consensus Harder Than
Consensus?*, PODC 2022.

The definitions `IsRecording` (Definition 4) and `IsDiscerning` (Definition 2, Ruppert) are those
of `Papers/PODC2024/RecoverableConsensus/Defs.lean` (Ovens, PODC'24, who uses the same notions).
Here:

* `RecOn` — the `n`-recording conditions for the processes of a finite set `R ⊆ Fin n`
  (with the teams and operations of `Fin n`); `RecOn.isRecording` reindexes to `Fin R.card`;
* Observation 5 (`isDiscerning_of_isRecording`), Observation 6 (`IsRecording.pred`),
  Lemma 7 (`lemma7`), Theorem 16 (`theorem16`), Proposition 18, first part (`prop18`).
-/

namespace Podc.RecoverableHarder

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Cslib.SharedMemory.Recoverable.Ovens

variable {S : ObjSpec}

/-! ## `apply` -/

lemma apply_append {n : ℕ} (u : S.State) (o : Fin n → S.Op) (σ τ : List (Fin n)) :
    apply S u o (σ ++ τ) = apply S (apply S u o σ) o τ := by
  simp [apply, List.foldl_append]

lemma apply_map {m n : ℕ} (u : S.State) (o : Fin n → S.Op) (f : Fin m → Fin n)
    (σ : List (Fin m)) : apply S u (o ∘ f) σ = apply S u o (σ.map f) := by
  simp [apply, List.foldl_map]

lemma apply_singleton {n : ℕ} (u : S.State) (o : Fin n → S.Op) (p : Fin n) :
    apply S u o [p] = (S.δ u (o p)).1 := rfl

/-! ## Recording conditions on a set of processes -/

/-- The conditions of Definition 4 for the processes of `R` (teams `team`, operations `o`, initial
value `u`): both teams meet `R`; schedules of distinct processes of `R` starting on opposite teams
lead to different values; and if a schedule of `R` starting on team `x` returns to `u`, the other
team has exactly one member in `R`. -/
def RecOn {n : ℕ} (S : ObjSpec) (R : Finset (Fin n)) (u : S.State) (team : Fin n → Bool)
    (o : Fin n → S.Op) : Prop :=
  (∃ p ∈ R, team p = false) ∧ (∃ p ∈ R, team p = true) ∧
    (∀ p σ q τ, (∀ x ∈ p :: σ, x ∈ R) → (∀ x ∈ q :: τ, x ∈ R) → (p :: σ).Nodup →
      (q :: τ).Nodup → team p = false → team q = true →
      apply S u o (p :: σ) ≠ apply S u o (q :: τ)) ∧
    (∀ p σ, (∀ x ∈ p :: σ, x ∈ R) → (p :: σ).Nodup → apply S u o (p :: σ) = u →
      ∃! q, q ∈ R ∧ team q = !team p)

/-- Reindexing: the recording conditions on `R` give an `R.card`-recording type. -/
theorem RecOn.isRecording {n : ℕ} {R : Finset (Fin n)} {u : S.State} {team : Fin n → Bool}
    {o : Fin n → S.Op} (h : RecOn S R u team o) : IsRecording R.card S := by
  obtain ⟨⟨a, ha, hta⟩, ⟨b, hb, htb⟩, h1, h2⟩ := h
  set e : Fin R.card ≃ R := R.equivFin.symm
  set f : Fin R.card → Fin n := fun i => (e i).val with hf
  have finj : Function.Injective f := fun i j hij => e.injective (Subtype.ext hij)
  have fmem : ∀ i, f i ∈ R := fun i => (e i).2
  have hsurj : ∀ x ∈ R, ∃ i, f i = x := fun x hx => ⟨e.symm ⟨x, hx⟩, by simp [hf]⟩
  have hmap : ∀ σ : List (Fin R.card), ∀ x ∈ σ.map f, x ∈ R := by
    intro σ x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact fmem i
  refine ⟨u, team ∘ f, o ∘ f, ?_, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hsurj a ha; exact ⟨i, by simp [hi, hta]⟩
  · obtain ⟨i, hi⟩ := hsurj b hb; exact ⟨i, by simp [hi, htb]⟩
  · intro p σ q τ hp hq tp tq heq
    rw [apply_map, apply_map] at heq
    exact h1 (f p) (σ.map f) (f q) (τ.map f) (hmap (p :: σ)) (hmap (q :: τ))
      (by simpa using (List.Nodup.map finj hp)) (by simpa using (List.Nodup.map finj hq)) tp tq
      (by simpa using heq)
  · intro p σ hp heq
    rw [apply_map] at heq
    obtain ⟨q, ⟨hqR, hq⟩, huniq⟩ := h2 (f p) (σ.map f) (hmap (p :: σ))
      (by simpa using (List.Nodup.map finj hp)) (by simpa using heq)
    obtain ⟨i, rfl⟩ := hsurj q hqR
    refine ⟨i, by simpa using hq, fun j hj => finj ?_⟩
    exact huniq (f j) ⟨fmem j, by simpa using hj⟩

/-- `IsRecording` unfolds to `RecOn` on all processes. -/
theorem isRecording_iff {n : ℕ} : IsRecording n S ↔
    ∃ u team o, RecOn S (Finset.univ : Finset (Fin n)) u team o := by
  constructor
  · rintro ⟨u, team, o, ⟨a, ha⟩, ⟨b, hb⟩, h1, h2⟩
    refine ⟨u, team, o, ⟨a, by simp, ha⟩, ⟨b, by simp, hb⟩,
      fun p σ q τ _ _ => h1 p σ q τ, fun p σ _ hp heq => ?_⟩
    obtain ⟨q, hq, hu⟩ := h2 p σ hp heq
    exact ⟨q, ⟨by simp, hq⟩, fun r hr => hu r hr.2⟩
  · rintro ⟨u, team, o, h⟩
    simpa using h.isRecording

/-! ## Observation 5 -/

/-- **Observation 5.** An `n`-recording type is `n`-discerning. -/
theorem isDiscerning_of_isRecording {n : ℕ} (h : IsRecording n S) : IsDiscerning n S := by
  obtain ⟨u, team, o, hA, hB, h1, -⟩ := h
  refine ⟨u, team, o, hA, hB, ?_⟩
  intro σ τ j m m' hm hm' hσ hτ hσne hτne tσ tτ _ _ heq
  apply h1 (σ.head hσne) σ.tail (τ.head hτne) τ.tail (by simpa using hσ) (by simpa using hτ) tσ tτ
  have := congrArg Prod.snd heq
  simpa using this

/-! ## Lemma 7 -/

/-- **Lemma 7.** If `u ∉ Q_x` and a (nonempty) schedule of distinct processes takes the object
from `u` back to `u`, then every process of team `x` occurs in the schedule. Stated for the
recording conditions on a set `R` (the processes of the schedule and `j` in `R`). -/
theorem lemma7 {n : ℕ} {R : Finset (Fin n)} {u : S.State} {team : Fin n → Bool}
    {o : Fin n → S.Op} (h : RecOn S R u team o) {x : Bool}
    (hx : ∀ p σ, (∀ y ∈ p :: σ, y ∈ R) → (p :: σ).Nodup → team p = x → apply S u o (p :: σ) ≠ u)
    (p : Fin n) (σ : List (Fin n)) (hσR : ∀ y ∈ p :: σ, y ∈ R) (hσ : (p :: σ).Nodup)
    (hcyc : apply S u o (p :: σ) = u) (j : Fin n) (hjR : j ∈ R) (hj : team j = x) :
    j ∈ p :: σ := by
  by_contra hjσ
  have hp : team p ≠ x := fun hp => hx p σ hσR hσ hp hcyc
  have hnd : (p :: (σ ++ [j])).Nodup := by
    rw [← List.cons_append, List.nodup_append]; refine ⟨hσ, by simp, ?_⟩
    intro a ha b hb; simp at hb; subst hb; rintro rfl; exact hjσ ha
  have hR : ∀ y ∈ p :: (σ ++ [j]), y ∈ R := by
    intro y hy; simp at hy; rcases hy with rfl | hy | rfl
    · exact hσR _ (by simp)
    · exact hσR _ (by simp [hy])
    · exact hjR
  have heq : apply S u o (p :: (σ ++ [j])) = apply S u o [j] := by
    rw [← List.cons_append, apply_append, hcyc]
  rcases Bool.eq_false_or_eq_true x with rfl | rfl
  · exact h.2.2.1 p (σ ++ [j]) j [] hR (by simpa using hjR) hnd (by simp) (by simpa using hp)
      hj heq
  · exact h.2.2.1 j [] p (σ ++ [j]) (by simpa using hjR) hR (by simp) hnd hj
      (by simpa using hp) heq.symm

/-! ## Restricting the recording conditions; Observation 6 -/

/-- The recording conditions survive the removal of processes as long as both teams keep a
member. -/
theorem RecOn.mono {n : ℕ} {R R' : Finset (Fin n)} {u : S.State} {team : Fin n → Bool}
    {o : Fin n → S.Op} (h : RecOn S R u team o) (hR : R' ⊆ R) (hA : ∃ p ∈ R', team p = false)
    (hB : ∃ p ∈ R', team p = true) : RecOn S R' u team o := by
  refine ⟨hA, hB, fun p σ q τ hp hq => h.2.2.1 p σ q τ (fun x hx => hR (hp x hx))
    (fun x hx => hR (hq x hx)), fun p σ hp hnd heq => ?_⟩
  obtain ⟨q, ⟨hqR, hq⟩, huniq⟩ := h.2.2.2 p σ (fun x hx => hR (hp x hx)) hnd heq
  have hex : ∃ r ∈ R', team r = !team p := by
    rcases Bool.eq_false_or_eq_true (team p) with h' | h' <;> simp [h'] <;> assumption
  obtain ⟨r, hr, hrt⟩ := hex
  refine ⟨r, ⟨hr, hrt⟩, fun r' hr' => ?_⟩
  rw [huniq r' ⟨hR hr'.1, hr'.2⟩, huniq r ⟨hR hr, hrt⟩]

/-- **Observation 6.** For `n ≥ 3`, an `n`-recording type is `(n-1)`-recording (drop one process
of the larger team). -/
theorem IsRecording.pred {n : ℕ} (hn : 3 ≤ n) (h : IsRecording n S) : IsRecording (n - 1) S := by
  classical
  obtain ⟨u, team, o, hrec⟩ := isRecording_iff.1 h
  obtain ⟨⟨a, -, ha⟩, ⟨b, -, hb⟩, -⟩ := id hrec
  -- some team has two members
  have : ∃ r, ∃ r' ≠ r, team r' = team r := by
    by_contra hno
    push Not at hno
    have hinj : Function.Injective team := fun x y hxy => by
      by_contra hne; exact hno y x hne hxy
    have := Fintype.card_le_of_injective team hinj
    simp at this; omega
  obtain ⟨r, r', hr'r, hrt⟩ := this
  have hR := hrec.mono (R' := Finset.univ.erase r) (Finset.erase_subset _ _) ?_ ?_
  · simpa [Finset.card_erase_of_mem] using hR.isRecording
  · by_cases har : a = r
    · subst har
      exact ⟨r', by simp [hr'r], by rw [hrt, ha]⟩
    · exact ⟨a, by simp [har], ha⟩
  · by_cases hbr : b = r
    · subst hbr
      exact ⟨r', by simp [hr'r], by rw [hrt, hb]⟩
    · exact ⟨b, by simp [hbr], hb⟩

/-- Iterated Observation 6. -/
theorem IsRecording.mono {n m : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) (h : IsRecording n S) :
    IsRecording m S := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ k hk ih => exact ih (by simpa using IsRecording.pred (S := S) (by omega) h)

/-! ## Discerning conditions -/

/-- The third condition of Definition 2 (`n`-discerning) for given data. -/
def DiscCond {n : ℕ} (S : ObjSpec) (u : S.State) (team : Fin n → Bool) (o : Fin n → S.Op) :
    Prop :=
  ∀ (σ τ : List (Fin n)) (j : Fin n) (m m' : ℕ) (hm : m < σ.length) (hm' : m' < τ.length),
      σ.Nodup → τ.Nodup → (hσ : σ ≠ []) → (hτ : τ ≠ []) → team (σ.head hσ) = false →
      team (τ.head hτ) = true → σ[m] = j → τ[m'] = j →
      ((S.δ (apply S u o (σ.take m)) (o j)).2, apply S u o σ) ≠
        ((S.δ (apply S u o (τ.take m')) (o j)).2, apply S u o τ)

lemma isDiscerning_iff {n : ℕ} : IsDiscerning n S ↔
    ∃ (u : S.State) (team : Fin n → Bool) (o : Fin n → S.Op), (∃ p, team p = false) ∧ (∃ p, team p = true) ∧ DiscCond S u team o := Iff.rfl

/-- The basic violation of the discerning condition: two schedules starting on opposite teams
that reach the same value, followed by the same process `j`. -/
lemma DiscCond.false_of_last {n : ℕ} {u : S.State} {team : Fin n → Bool} {o : Fin n → S.Op}
    (h : DiscCond S u team o) (σ τ : List (Fin n)) (j : Fin n) (hσ : (σ ++ [j]).Nodup)
    (hτ : (τ ++ [j]).Nodup) (hσt : team ((σ ++ [j]).head (by simp)) = false)
    (hτt : team ((τ ++ [j]).head (by simp)) = true) (heq : apply S u o σ = apply S u o τ) :
    False := by
  apply h (σ ++ [j]) (τ ++ [j]) j σ.length τ.length (by simp) (by simp) hσ hτ (by simp) (by simp)
    hσt hτt (by simp) (by simp)
  simp [apply_append, heq, List.take_left']

/-! ## Theorem 16 and Proposition 18 -/

/-- From `n`-discerning data and two distinct reserve processes `r₁ r₂` such that the remaining
processes meet both teams and every team whose remaining part has two members has a reserve
process, the remaining processes satisfy the recording conditions. -/
theorem recOn_of_discCond {n : ℕ} {u : S.State} {team : Fin n → Bool} {o : Fin n → S.Op}
    (h : DiscCond S u team o) (R : Finset (Fin n)) (r₁ : Fin n) (hr₁ : r₁ ∉ R)
    (hA : ∃ p ∈ R, team p = false) (hB : ∃ p ∈ R, team p = true)
    (hres : ∀ x, (∃ p ∈ R, ∃ q ∈ R, p ≠ q ∧ team p = x ∧ team q = x) → ∃ r ∉ R, team r = x) :
    RecOn S R u team o := by
  classical
  refine ⟨hA, hB, fun p σ q τ hp hq hpn hqn tp tq heq => ?_, fun p σ hp hpn heq => ?_⟩
  · -- condition 1: append the reserve process `r₁`
    have hnd : ∀ (l : List (Fin n)), (∀ x ∈ l, x ∈ R) → l.Nodup → (l ++ [r₁]).Nodup := by
      intro l hl hn
      rw [List.nodup_append]
      refine ⟨hn, by simp, ?_⟩
      intro a ha b hb; simp at hb; subst hb; rintro rfl; exact hr₁ (hl _ ha)
    exact h.false_of_last (p :: σ) (q :: τ) r₁ (hnd _ hp hpn) (hnd _ hq hqn) (by simpa using tp)
      (by simpa using tq) heq
  · -- conditions 2 and 3
    set x := !team p with hx
    obtain ⟨q, hqR, hq⟩ : ∃ q ∈ R, team q = x := by
      rcases Bool.eq_false_or_eq_true (team p) with h' | h' <;> simp [hx, h'] <;> assumption
    refine ⟨q, ⟨hqR, hq⟩, fun q' ⟨hq'R, hq'⟩ => ?_⟩
    by_contra hne
    obtain ⟨r, hr, hrt⟩ := hres x ⟨q', hq'R, q, hqR, hne, hq', hq⟩
    have hnd : (p :: σ ++ [r]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hpn, by simp, ?_⟩
      intro a ha b hb; simp at hb; subst hb; rintro rfl; exact hr (hp _ ha)
    have heq' : apply S u o (p :: σ) = apply S u o [] := by simpa using heq
    rcases Bool.eq_false_or_eq_true (team p) with h' | h'
    · exact h.false_of_last [] (p :: σ) r (by simp) hnd (by simpa [hx, h'] using hrt)
        (by simpa using h') heq'.symm
    · exact h.false_of_last (p :: σ) [] r hnd (by simp) (by simpa using h')
        (by simpa [hx, h'] using hrt) heq'

/-- **Theorem 16.** For `n ≥ 4`, an `n`-discerning type is `(n-2)`-recording. -/
theorem theorem16 {n : ℕ} (hn : 4 ≤ n) (h : IsDiscerning n S) : IsRecording (n - 2) S := by
  classical
  obtain ⟨u, team, o, ⟨a, ha⟩, ⟨b, hb⟩, hd⟩ := h
  -- choose the two reserve processes
  obtain ⟨r₁, r₂, h12, hR⟩ : ∃ r₁ r₂ : Fin n, r₁ ≠ r₂ ∧
      let R := (Finset.univ.erase r₁).erase r₂
      (∃ p ∈ R, team p = false) ∧ (∃ p ∈ R, team p = true) ∧
      ∀ x, (∃ p ∈ R, ∃ q ∈ R, p ≠ q ∧ team p = x ∧ team q = x) → ∃ r ∉ R, team r = x := by
    -- sizes of the teams
    set F := Finset.univ.filter (fun p : Fin n => team p = false) with hF
    set Tt := Finset.univ.filter (fun p : Fin n => team p = true) with hT
    have hcard : F.card + Tt.card = n := by
      have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun p : Fin n => team p = false)
      simpa [hF, hT] using this
    have hF1 : a ∈ F := by simp [hF, ha]
    have hT1 : b ∈ Tt := by simp [hT, hb]
    by_cases hFc : 2 ≤ F.card
    · by_cases hTc : 2 ≤ Tt.card
      · -- one reserve on each team
        obtain ⟨a', ha'F, ha'⟩ := Finset.exists_mem_ne hFc a
        obtain ⟨b', hb'T, hb'⟩ := Finset.exists_mem_ne hTc b
        have tab : team a' = false := by simpa [hF] using ha'F
        have tbb : team b' = true := by simpa [hT] using hb'T
        refine ⟨a', b', fun h => by rw [h] at tab; simp [tab] at tbb, ?_, ?_, ?_⟩
        · exact ⟨a, by simp [Ne.symm ha', show a ≠ b' from fun h => by subst h; simp [ha] at tbb],
            ha⟩
        · exact ⟨b, by simp [Ne.symm hb', show b ≠ a' from fun h => by subst h; simp [hb] at tab],
            hb⟩
        · intro x _
          cases x
          · exact ⟨a', by simp, tab⟩
          · exact ⟨b', by simp, tbb⟩
      · -- team `true` is a singleton `{b}`; two reserves from team `false`
        have hT1' : Tt = {b} := by
          refine Finset.eq_singleton_iff_unique_mem.2 ⟨hT1, fun y hy => ?_⟩
          by_contra hyb
          have : 2 ≤ Tt.card := Finset.one_lt_card.2 ⟨y, hy, b, hT1, hyb⟩
          omega
        have hF3 : 3 ≤ F.card := by rw [hT1'] at hcard; simp at hcard; omega
        obtain ⟨a₁, ha₁, ha₁a⟩ := Finset.exists_mem_ne (by omega : 1 < F.card) a
        obtain ⟨a₂, ha₂, ha₂'⟩ := Finset.exists_mem_ne
          (by rw [Finset.card_erase_of_mem ha₁]; omega : 1 < (F.erase a₁).card) a
        have ha₂a₁ : a₂ ≠ a₁ := Finset.ne_of_mem_erase ha₂
        have ha₂F := Finset.mem_of_mem_erase ha₂
        have t1 : team a₁ = false := by simpa [hF] using ha₁
        have t2 : team a₂ = false := by simpa [hF] using ha₂F
        refine ⟨a₁, a₂, ha₂a₁.symm, ?_, ?_, ?_⟩
        · exact ⟨a, by simp [Ne.symm ha₁a, Ne.symm ha₂'], ha⟩
        · exact ⟨b, by simp [show b ≠ a₁ from fun h => by subst h; simp [hb] at t1,
            show b ≠ a₂ from fun h => by subst h; simp [hb] at t2], hb⟩
        · intro x ⟨p, hp, q, hq, hpq, tp, tq⟩
          cases x
          · exact ⟨a₁, by simp, t1⟩
          · exfalso
            have hp' : p ∈ Tt := by simp [hT, tp]
            have hq' : q ∈ Tt := by simp [hT, tq]
            rw [hT1'] at hp' hq'; simp at hp' hq'; exact hpq (hp'.trans hq'.symm)
    · -- team `false` is a singleton `{a}`; two reserves from team `true`
      have hF1' : F = {a} := by
        refine Finset.eq_singleton_iff_unique_mem.2 ⟨hF1, fun y hy => ?_⟩
        by_contra hya
        have : 2 ≤ F.card := Finset.one_lt_card.2 ⟨y, hy, a, hF1, hya⟩
        omega
      have hT3 : 3 ≤ Tt.card := by rw [hF1'] at hcard; simp at hcard; omega
      obtain ⟨b₁, hb₁, hb₁b⟩ := Finset.exists_mem_ne (by omega : 1 < Tt.card) b
      obtain ⟨b₂, hb₂, hb₂'⟩ := Finset.exists_mem_ne
        (by rw [Finset.card_erase_of_mem hb₁]; omega : 1 < (Tt.erase b₁).card) b
      have hb₂b₁ : b₂ ≠ b₁ := Finset.ne_of_mem_erase hb₂
      have hb₂T := Finset.mem_of_mem_erase hb₂
      have t1 : team b₁ = true := by simpa [hT] using hb₁
      have t2 : team b₂ = true := by simpa [hT] using hb₂T
      refine ⟨b₁, b₂, hb₂b₁.symm, ?_, ?_, ?_⟩
      · exact ⟨a, by simp [show a ≠ b₁ from fun h => by subst h; simp [ha] at t1,
            show a ≠ b₂ from fun h => by subst h; simp [ha] at t2], ha⟩
      · exact ⟨b, by simp [Ne.symm hb₁b, Ne.symm hb₂'], hb⟩
      · intro x ⟨p, hp, q, hq, hpq, tp, tq⟩
        cases x
        · exfalso
          have hp' : p ∈ F := by simp [hF, tp]
          have hq' : q ∈ F := by simp [hF, tq]
          rw [hF1'] at hp' hq'; simp at hp' hq'; exact hpq (hp'.trans hq'.symm)
        · exact ⟨b₁, by simp, t1⟩
  obtain ⟨hA, hB, hres⟩ := hR
  have hrec := recOn_of_discCond hd _ r₂ (by simp) hA hB hres
  have := hrec.isRecording
  rwa [Finset.card_erase_of_mem (by simp [Ne.symm h12]), Finset.card_erase_of_mem (by simp),
    Finset.card_univ, Fintype.card_fin, Nat.sub_sub] at this

/-- **Proposition 18** (combinatorial part). A `3`-discerning type is `2`-recording. -/
theorem prop18 (h : IsDiscerning 3 S) : IsRecording 2 S := by
  classical
  obtain ⟨u, team, o, ⟨a, ha⟩, ⟨b, hb⟩, hd⟩ := h
  have hab : a ≠ b := by rintro rfl; simp [ha] at hb
  -- the third process
  obtain ⟨c, hca, hcb⟩ : ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by
    by_contra hno; push Not at hno
    have : (Finset.univ : Finset (Fin 3)) ⊆ {a, b} := fun c _ => by
      by_cases h : c = a
      · simp [h]
      · simp [hno c h]
    have := Finset.card_le_card this
    simp at this
    have := Finset.card_insert_le a {b}
    simp at this; omega
  have hrec := recOn_of_discCond hd {a, b} c (by simp [hca, hcb]) ⟨a, by simp, ha⟩
    ⟨b, by simp, hb⟩ (fun x ⟨p, hp, q, hq, hpq, tp, tq⟩ => by
      exfalso
      simp at hp hq
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp_all)
  simpa [Finset.card_pair hab] using hrec.isRecording

/-! ## Two-process obstructions -/

/-- A finset with at least `m` elements contains a duplicate-free list of length `m`. -/
lemma Finset.exists_nodup_list {α : Type} {X : Finset α} {m : ℕ} (h : m ≤ X.card) :
    ∃ l : List α, l.Nodup ∧ l.length = m ∧ ∀ x ∈ l, x ∈ X := by
  obtain ⟨Y, hY, hcard⟩ := Finset.exists_subset_card_eq h
  exact ⟨Y.toList, Y.nodup_toList, by simp [hcard], fun x hx => hY (by simpa using hx)⟩

/-- The recording disjointness condition for heads on different teams (either order). -/
lemma recOn_ne {n : ℕ} {R : Finset (Fin n)} {u : S.State} {team : Fin n → Bool}
    {o : Fin n → S.Op} (h : RecOn S R u team o) (p : Fin n) (σ : List (Fin n)) (q : Fin n)
    (τ : List (Fin n)) (hp : ∀ x ∈ p :: σ, x ∈ R) (hq : ∀ x ∈ q :: τ, x ∈ R)
    (hpn : (p :: σ).Nodup) (hqn : (q :: τ).Nodup) (hpq : team p ≠ team q) :
    apply S u o (p :: σ) ≠ apply S u o (q :: τ) := by
  cases hp' : team p
  · exact h.2.2.1 p σ q τ hp hq hpn hqn hp' (by cases hq' : team q <;> simp_all)
  · exact Ne.symm (h.2.2.1 q τ p σ hq hp hqn hpn (by cases hq' : team q <;> simp_all) hp')

/-- In recording data, processes on different teams have operations that lead to different
values, do not overwrite each other, and do not commute. -/
lemma recOn_pair {n : ℕ} {R : Finset (Fin n)} {u : S.State} {team : Fin n → Bool}
    {o : Fin n → S.Op} (h : RecOn S R u team o) {i j : Fin n} (hi : i ∈ R) (hj : j ∈ R)
    (hij : team i ≠ team j) :
    (S.δ u (o i)).1 ≠ (S.δ u (o j)).1 ∧ (S.δ (S.δ u (o j)).1 (o i)).1 ≠ (S.δ u (o i)).1 ∧
      (S.δ (S.δ u (o i)).1 (o j)).1 ≠ (S.δ u (o j)).1 ∧
      (S.δ (S.δ u (o i)).1 (o j)).1 ≠ (S.δ (S.δ u (o j)).1 (o i)).1 := by
  have hne : i ≠ j := by rintro rfl; exact hij rfl
  have m1 : ∀ x ∈ [i], x ∈ R := by simpa using hi
  have m2 : ∀ x ∈ [j], x ∈ R := by simpa using hj
  have m3 : ∀ x ∈ [i, j], x ∈ R := by simp [hi, hj]
  have m4 : ∀ x ∈ [j, i], x ∈ R := by simp [hi, hj]
  refine ⟨fun e => recOn_ne h i [] j [] m1 m2 (by simp) (by simp) hij (by simpa using e),
    fun e => recOn_ne h j [i] i [] m4 m1 (by simp [Ne.symm hne]) (by simp) (Ne.symm hij)
      (by simpa using e),
    fun e => recOn_ne h i [j] j [] m3 m2 (by simp [hne]) (by simp) hij (by simpa using e),
    fun e => recOn_ne h i [j] j [i] m3 m4 (by simp [hne]) (by simp [Ne.symm hne]) hij
      (by simpa using e)⟩

/-- The basic discerning violation, for heads on different teams (either order). -/
lemma DiscCond.false_of_last_ne {n : ℕ} {u : S.State} {team : Fin n → Bool} {o : Fin n → S.Op}
    (h : DiscCond S u team o) (σ τ : List (Fin n)) (j : Fin n) (hσ : (σ ++ [j]).Nodup)
    (hτ : (τ ++ [j]).Nodup)
    (ht : team ((σ ++ [j]).head (by simp)) ≠ team ((τ ++ [j]).head (by simp)))
    (heq : apply S u o σ = apply S u o τ) : False := by
  cases h1 : team ((σ ++ [j]).head (by simp))
  · exact h.false_of_last σ τ j hσ hτ h1 (by rw [h1] at ht; simpa using Ne.symm ht) heq
  · exact h.false_of_last τ σ j hτ hσ (by rw [h1] at ht; simpa using Ne.symm ht) h1 heq.symm

/-- In discerning data, for processes `i`, `j` on different teams: the operation of `j` is not
absorbed by that of `i` (same value and response of `j` after `i j` as after `j`), and (with a
third process `k`) the two operations do not lead to the same value. -/
lemma DiscCond.pair {n : ℕ} {u : S.State} {team : Fin n → Bool} {o : Fin n → S.Op}
    (h : DiscCond S u team o) {i j : Fin n} (hij : team i ≠ team j) :
    S.δ (S.δ u (o i)).1 (o j) ≠ S.δ u (o j) ∧
      ¬ ((S.δ (S.δ u (o i)).1 (o j)).1 = (S.δ (S.δ u (o j)).1 (o i)).1 ∧
        (S.δ u (o i)).2 = (S.δ (S.δ u (o j)).1 (o i)).2) ∧
      ∀ k, k ≠ i → k ≠ j → (S.δ u (o i)).1 ≠ (S.δ u (o j)).1 := by
  have hne : i ≠ j := by rintro rfl; exact hij rfl
  refine ⟨fun e => ?_, fun ⟨e1, e2⟩ => ?_, fun k hki hkj e => ?_⟩
  · -- `i j` vs `j`, the pair of `j`
    cases hti : team i
    · exact h [i, j] [j] j 1 0 (by simp) (by simp) (by simp [hne]) (by simp)
        (by simp) (by simp) hti (by cases htj : team j <;> simp_all) (by simp) (by simp)
        (by simp [apply, e])
    · exact h [j] [i, j] j 0 1 (by simp) (by simp) (by simp) (by simp [hne])
        (by simp) (by simp) (by cases htj : team j <;> simp_all) hti (by simp) (by simp)
        (by simp [apply, e])
  · -- `i j` vs `j i`, the pair of `i`
    cases hti : team i
    · exact h [i, j] [j, i] i 0 1 (by simp) (by simp) (by simp [hne]) (by simp [Ne.symm hne])
        (by simp) (by simp) hti (by cases htj : team j <;> simp_all) (by simp) (by simp)
        (by simp [apply, e1, e2])
    · exact h [j, i] [i, j] i 1 0 (by simp) (by simp) (by simp [Ne.symm hne]) (by simp [hne])
        (by simp) (by simp) (by cases htj : team j <;> simp_all) hti (by simp) (by simp)
        (by simp [apply, e1, e2])
  · exact h.false_of_last_ne [i] [j] k (by simp [Ne.symm hki]) (by simp [Ne.symm hkj])
      (by simpa using hij) (by simpa using e)

end Podc.RecoverableHarder
