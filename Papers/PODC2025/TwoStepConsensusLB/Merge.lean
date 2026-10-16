import Papers.PODC2025.TwoStepConsensusLB.Model
-- CSLib candidate: merging two synchronous two-round prefixes (generic indistinguishability lemma).

/-!
# Merging two synchronous two-round prefixes (the indistinguishability step of §B)

All lower-bound proofs of the paper (Lemma 3, Theorem 1 "only if", Theorem 2 "only if") glue the
first two rounds of two synchronous runs:

* `σ` is an `X`-faulty synchronous run (invocations `i`, delivery order `o`) in which `d ∉ X`
  decides `v` by time `2Δ`;
* `σ'` is a `Y`-faulty synchronous run (invocations `i'`, order `o'`) in which `d' ∉ Y` decides
  `v'` by time `2Δ`;
* `X ∩ Y = ∅`, and the processes of `Z = Π \ (X ∪ Y)` start in the same way in both runs.

`mergeRun X Y i i' o o' d d' c` is the run in which `Π \ X` behaves as in `σ` during the first two
rounds (and `d` decides `v` at time `2Δ`), `X` behaves as in `σ'` during the first two rounds,
and the processes of `Z ∪ {d, d'}` crash at time `3`; all messages between the two groups are
delayed until time `3 = GST`, the last-round messages of the crashed processes are lost. The
symmetric run `mergeRun Y X i' i o' o d' d c` (with `Z` behaving as in `σ'`, `d'` deciding `v'`)
is indistinguishable from it for all correct processes (`mergeRun_st_symm`), forever. `c` gives
the invocations from time `3` on (used for the object version).

Consequences: `merge_task` / `merge_object`: if `|Z ∪ {d, d'}| ≤ f` and some process is correct,
an `f`-resilient protocol has `v = v'`.
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus

open Finset

variable {P V M S : Type*} [Fintype P] [DecidableEq P]

/-- The processes that crash in the merged runs: `Z ∪ {d, d'}` with `Z = Π \ (X ∪ Y)`. -/
def mergeFaulty (X Y : Finset P) (d d' : P) : Finset P := (X ∪ Y)ᶜ ∪ {d, d'}

theorem mergeFaulty_comm (X Y : Finset P) (d d' : P) :
    mergeFaulty Y X d' d = mergeFaulty X Y d d' := by
  unfold mergeFaulty; rw [union_comm Y X, pair_comm]

theorem mem_mergeFaulty {X Y : Finset P} {d d' x : P} :
    x ∈ mergeFaulty X Y d d' ↔ (x ∉ X ∧ x ∉ Y) ∨ x = d ∨ x = d' := by
  simp only [mergeFaulty, mem_union, mem_compl, mem_insert, mem_singleton]; tauto

/-- The merged run (see the module docstring). -/
def mergeRun (X Y : Finset P) (i i' : P → ℕ → Option V)
    (o o' : P → ℕ → List (P × M) → List (P × M)) (d d' : P) (c : P → ℕ → Option V) :
    Run P V M where
  crash x := if x ∈ mergeFaulty X Y d d' then some 3 else none
  gst := 3
  inv x τ := if τ < 3 then (if x ∈ X then i' x τ else i x τ) else c x τ
  ord x τ := if τ < 3 then (if x ∈ X then o' x τ else o x τ) else fun l => l
  dl q τ x :=
    if τ = 0 then
      (if (x ∈ X → q ∉ Y) ∧ (x ∉ X → q ∉ X) then 1
        else if q ∉ mergeFaulty X Y d d' ∧ x ∉ mergeFaulty X Y d d' then 3 else 0)
    else if τ = 1 then
      (if x = d ∧ q ∉ X then 2
        else if q ∉ mergeFaulty X Y d d' ∧ x ∉ mergeFaulty X Y d d' then 3 else 0)
    else if q ∉ mergeFaulty X Y d d' ∧ x ∉ mergeFaulty X Y d d' then τ + 1 else 0

section
variable (X Y : Finset P) (i i' : P → ℕ → Option V)
  (o o' : P → ℕ → List (P × M) → List (P × M)) (d d' : P) (c : P → ℕ → Option V)

theorem mergeRun_alive_lt (x : P) {τ : ℕ} (hτ : τ < 3) :
    (mergeRun X Y i i' o o' d d' c).alive x τ := by
  rw [Run.alive_iff]; intro c' hc
  simp only [mergeRun] at hc; split_ifs at hc; simp_all

theorem mergeRun_crash_of_not_mem {x : P} (hx : x ∉ mergeFaulty X Y d d') :
    (mergeRun X Y i i' o o' d d' c).crash x = none := by simp [mergeRun, hx]

theorem mergeRun_faulty : (mergeRun X Y i i' o o' d d' c).faulty = mergeFaulty X Y d d' := by
  ext x; by_cases h : x ∈ mergeFaulty X Y d d' <;> simp [Run.faulty, mergeRun, h]

theorem mergeRun_valid {f : ℕ} (hcard : (mergeFaulty X Y d d').card ≤ f) (ho : IsOrder o)
    (ho' : IsOrder o') : (mergeRun X Y i i' o o' d d' c).Valid f where
  card_faulty := by rw [mergeRun_faulty]; exact hcard
  ord_perm x τ l := by
    simp only [mergeRun]
    split_ifs
    · exact ho' x τ l
    · exact ho x τ l
    · exact List.Perm.refl _
  dl_ge q τ x hq hx := by
    simp only [mergeRun] at hq hx ⊢
    split_ifs at hq hx ⊢ <;> simp_all
  dl_le q τ x hq hx := by
    simp only [mergeRun] at hq hx ⊢
    split_ifs at hq hx ⊢ <;> simp_all

end

/-- The processes outside `X` behave in the merged run as in `σ = syncRun X i o` during the first
two rounds, and `d` also takes its step at time `2` as in `σ`. -/
theorem mergeRun_st_follow (A : Protocol P V M S) {X Y : Finset P} {i i' : P → ℕ → Option V}
    {o o' : P → ℕ → List (P × M) → List (P × M)} {d d' : P} (c : P → ℕ → Option V)
    (hd : d ∉ X) :
    (∀ τ ≤ 3, ∀ x ∉ X, τ ≤ 2 ∨ x = d →
      (mergeRun X Y i i' o o' d d' c).st A τ x = (syncRun X i o).st A τ x) := by
  set ρ := mergeRun X Y i i' o o' d d' c
  set σ : Run P V M := syncRun X i o
  have hσal : ∀ x ∉ X, ∀ τ, σ.alive x τ := fun x hx τ =>
    Run.alive_of_crash_none _ (syncRun_crash_of_not_mem hx) τ
  have hσnal : ∀ x ∈ X, ∀ τ, σ.alive x τ = false := fun x hx τ => by
    simp [Run.alive, σ, syncRun, hx]
  have hρal : ∀ x, ∀ τ < 3, ρ.alive x τ := fun x τ hτ => mergeRun_alive_lt _ _ _ _ _ _ _ _ _ x hτ
  -- first two rounds
  have h2 : ∀ τ ≤ 2, ∀ x ∈ {x | x ∉ X}, ρ.st A τ x = σ.st A τ x := by
    refine ρ.st_eq_of_inbox_eq A (ref := fun _ => σ) (T := 2) ?_ ?_ ?_
    · intro x hx τ hτ
      simp only [Set.mem_ofPred_eq] at hx
      rw [hρal x τ (by omega), hσal x hx τ]
    · intro x hx τ hτ _
      simp only [Set.mem_ofPred_eq] at hx
      simp [ρ, σ, mergeRun, syncRun, hx, show τ < 3 by omega]
    · intro τ hτ IH x hx _
      simp only [Set.mem_ofPred_eq] at hx
      refine ρ.inbox_eq_of_dlv_eq A ?_ ?_
      · simp [ρ, σ, mergeRun, syncRun, hx, show τ < 3 by omega]
      · intro q τ' hτ'
        obtain rfl : τ' = 0 := by omega
        obtain rfl : τ = 1 := by omega
        by_cases hq : q ∈ X
        · rw [ρ.dlv_eq_nil_of_ne A, Run.dlv, Run.out_of_not_alive A σ (hσnal q hq 0)]
          · simp
          · simp only [ρ, mergeRun]; split_ifs <;> simp_all
        · rw [ρ.dlv_of_eq A (by simp [ρ, mergeRun, hx, hq]),
            σ.dlv_of_eq A (by simp [σ, syncRun]),
            ρ.out_of_alive A (hρal q 0 (by omega)), σ.out_of_alive A (hσal q hq 0),
            IH q hq 1 le_rfl]
  intro τ hτ x hx hor
  rcases hor with hτ2 | rfl
  · exact h2 τ hτ2 x hx
  · rcases Nat.lt_or_ge τ 3 with hτ3 | hτ3
    · exact h2 τ (by omega) x hx
    obtain rfl : τ = 3 := by omega
    rw [ρ.st_succ_of_alive A (hρal _ 2 (by omega)), σ.st_succ_of_alive A (hσal _ hx 2),
      h2 2 le_rfl _ hx]
    congr 1
    · simp [ρ, σ, mergeRun, syncRun, hx]
    · refine ρ.inbox_eq_of_dlv_eq A ?_ ?_
      · simp [ρ, σ, mergeRun, syncRun, hx]
      · intro q τ' hτ'
        rcases (show τ' = 0 ∨ τ' = 1 by omega) with rfl | rfl
        · rw [ρ.dlv_eq_nil_of_ne A, σ.dlv_eq_nil_of_ne A]
          · simp [σ, syncRun]
          · simp only [ρ, mergeRun]; split_ifs <;> simp_all
        · by_cases hq : q ∈ X
          · rw [ρ.dlv_eq_nil_of_ne A, Run.dlv, Run.out_of_not_alive A σ (hσnal q hq 1)]
            · simp
            · simp only [ρ, mergeRun]; split_ifs <;> simp_all
          · rw [ρ.dlv_of_eq A (by simp [ρ, mergeRun, hq]),
              σ.dlv_of_eq A (by simp [σ, syncRun]),
              ρ.out_of_alive A (hρal q 1 (by omega)), σ.out_of_alive A (hσal q hq 1),
              h2 2 le_rfl q hq]

section symm
variable {X Y : Finset P} {i i' : P → ℕ → Option V}
  {o o' : P → ℕ → List (P × M) → List (P × M)} {d d' : P} {c : P → ℕ → Option V}

/-- Correct processes of the merged run belong to `X ∪ Y` and are not `d`, `d'`. -/
theorem not_mem_mergeFaulty {x : P} (hx : x ∉ mergeFaulty X Y d d') :
    (x ∈ X ∨ x ∈ Y) ∧ x ≠ d ∧ x ≠ d' := by
  rw [mem_mergeFaulty] at hx; push Not at hx
  refine ⟨?_, hx.2.1, hx.2.2⟩
  by_cases h : x ∈ X
  · exact Or.inl h
  · exact Or.inr (hx.1 h)

theorem mergeRun_inv_symm (hXY : Disjoint X Y) {x : P} (hx : x ∈ X ∨ x ∈ Y) (τ : ℕ) :
    (mergeRun X Y i i' o o' d d' c).inv x τ = (mergeRun Y X i' i o' o d' d c).inv x τ := by
  rcases hx with hx | hx
  · have : x ∉ Y := Finset.disjoint_left.mp hXY hx
    simp [mergeRun, hx, this]
  · have : x ∉ X := Finset.disjoint_right.mp hXY hx
    simp [mergeRun, hx, this]

theorem mergeRun_ord_symm (hXY : Disjoint X Y) {x : P} (hx : x ∈ X ∨ x ∈ Y) (τ : ℕ) :
    (mergeRun X Y i i' o o' d d' c).ord x τ = (mergeRun Y X i' i o' o d' d c).ord x τ := by
  rcases hx with hx | hx
  · have : x ∉ Y := Finset.disjoint_left.mp hXY hx
    simp [mergeRun, hx, this]
  · have : x ∉ X := Finset.disjoint_right.mp hXY hx
    simp [mergeRun, hx, this]

theorem mergeRun_dl_symm (hXY : Disjoint X Y) {x : P} (hx : x ∉ mergeFaulty X Y d d') (q : P)
    (τ : ℕ) : (mergeRun X Y i i' o o' d d' c).dl q τ x = (mergeRun Y X i' i o' o d' d c).dl q τ x := by
  obtain ⟨hxXY, hxd, hxd'⟩ := not_mem_mergeFaulty hx
  simp only [mergeRun, mergeFaulty_comm, hxd, hxd', false_and, ite_false]
  congr 1
  rcases hxXY with h | h
  · have : x ∉ Y := Finset.disjoint_left.mp hXY h
    simp [h, this]
  · have : x ∉ X := Finset.disjoint_right.mp hXY h
    simp [h, this]

/-- A batch sent at time `τ' ≥ 1` and delivered to a correct process comes from a correct
process. -/
theorem mergeRun_sender_correct {x q : P} (hx : x ∉ mergeFaulty X Y d d') {τ' τ : ℕ}
    (h1 : 1 ≤ τ') (hlt : τ' < τ) (hdl : (mergeRun X Y i i' o o' d d' c).dl q τ' x = τ) :
    q ∉ mergeFaulty X Y d d' := by
  obtain ⟨-, hxd, -⟩ := not_mem_mergeFaulty hx
  simp only [mergeRun] at hdl
  split_ifs at hdl with h0 h0' h2 h3 <;> first | omega | simp_all

/-- In the two merged runs, every process has the same state after the first step. -/
theorem mergeRun_st_one (A : Protocol P V M S) (hXY : Disjoint X Y)
    (hZ : ∀ z, z ∉ X → z ∉ Y → i z 0 = i' z 0) (ho : IsOrder o) (ho' : IsOrder o') (q : P) :
    (mergeRun X Y i i' o o' d d' c).st A 1 q = (mergeRun Y X i' i o' o d' d c).st A 1 q := by
  rw [Run.st_succ_of_alive _ _ (mergeRun_alive_lt _ _ _ _ _ _ _ _ _ q (by omega)),
    Run.st_succ_of_alive _ _ (mergeRun_alive_lt _ _ _ _ _ _ _ _ _ q (by omega))]
  congr 1
  · by_cases hqX : q ∈ X
    · exact mergeRun_inv_symm hXY (Or.inl hqX) 0
    · by_cases hqY : q ∈ Y
      · exact mergeRun_inv_symm hXY (Or.inr hqY) 0
      · simp [mergeRun, hqX, hqY, hZ q hqX hqY]
  · unfold Run.inbox
    rw [Run.canon_zero, Run.canon_zero]
    simp only [mergeRun, show (0 : ℕ) < 3 by omega, ite_true]
    split_ifs <;> simp [ho.nil, ho'.nil]

/-- **Indistinguishability of the two merged runs.** Every correct process has the same states
in `mergeRun X Y …` and in the symmetric `mergeRun Y X …`, at all times. -/
theorem mergeRun_st_symm (A : Protocol P V M S) (hXY : Disjoint X Y)
    (hZ : ∀ z, z ∉ X → z ∉ Y → i z 0 = i' z 0) (ho : IsOrder o) (ho' : IsOrder o') {x : P}
    (hx : x ∉ mergeFaulty X Y d d') (τ : ℕ) :
    (mergeRun X Y i i' o o' d d' c).st A τ x = (mergeRun Y X i' i o' o d' d c).st A τ x := by
  set ρ := mergeRun X Y i i' o o' d d' c
  set ρ' := mergeRun Y X i' i o' o d' d c
  have hcor : ∀ y ∉ mergeFaulty X Y d d', ρ.crash y = none ∧ ρ'.crash y = none := fun y hy =>
    ⟨mergeRun_crash_of_not_mem _ _ _ _ _ _ _ _ _ hy,
      mergeRun_crash_of_not_mem _ _ _ _ _ _ _ _ _ (by rwa [mergeFaulty_comm])⟩
  refine ρ.st_eq_of_inbox_eq A (ref := fun _ => ρ') (X := {y | y ∉ mergeFaulty X Y d d'})
    (T := τ) ?_ ?_ ?_ τ le_rfl x hx
  · intro y hy τ _
    rw [Run.alive_of_crash_none _ (hcor y hy).1, Run.alive_of_crash_none _ (hcor y hy).2]
  · intro y hy τ _ _
    exact mergeRun_inv_symm hXY (not_mem_mergeFaulty hy).1 τ
  · intro t _ IH y hy _
    refine ρ.inbox_eq_of_dlv_eq A (mergeRun_ord_symm hXY (not_mem_mergeFaulty hy).1 t) ?_
    intro q τ' hτ'
    have hdl := mergeRun_dl_symm (i := i) (i' := i') (o := o) (o' := o') (c := c) hXY hy q τ'
    unfold Run.dlv
    rw [← hdl]
    split_ifs with h
    · rcases Nat.eq_zero_or_pos τ' with rfl | hpos
      · rw [ρ.out_of_alive A (mergeRun_alive_lt _ _ _ _ _ _ _ _ _ q (by omega)),
          ρ'.out_of_alive A (mergeRun_alive_lt _ _ _ _ _ _ _ _ _ q (by omega)),
          mergeRun_st_one A hXY hZ ho ho' q]
      · have hq := mergeRun_sender_correct hy hpos hτ' h
        rw [ρ.out_of_alive A (Run.alive_of_crash_none _ (hcor q hq).1 _),
          ρ'.out_of_alive A (Run.alive_of_crash_none _ (hcor q hq).2 _),
          IH q hq (τ' + 1) (by omega)]
    · rfl

end symm

/-- **Merge lemma, task version.** Let `σ` be an `X`-faulty and `σ'` a `Y`-faulty synchronous run
of an `f`-resilient consensus task protocol, with `X ∩ Y = ∅` and the same inputs outside
`X ∪ Y`. If `d` decides `v` in `σ` and `d'` decides `v'` in `σ'` by time `2Δ`,
`|Π \ (X ∪ Y) ∪ {d, d'}| ≤ f` and some process lies outside this set, then `v = v'`. -/
theorem merge_task {A : Protocol P V M S} {f : ℕ} (hA : SolvesTask A f) {X Y : Finset P}
    (hXY : Disjoint X Y) {I I' : P → V} (hZ : ∀ z, z ∉ X → z ∉ Y → I z = I' z)
    {o o' : P → ℕ → List (P × M) → List (P × M)} (ho : IsOrder o) (ho' : IsOrder o')
    {d d' : P} (hd : d ∉ X) (hd' : d' ∉ Y) {τ τ' : ℕ} (hτ : τ ≤ 3) (hτ' : τ' ≤ 3) {v v' : V}
    (hv : (syncRun X (taskInv I) o).DecidesAt A d τ v)
    (hv' : (syncRun Y (taskInv I') o').DecidesAt A d' τ' v')
    (hcard : (mergeFaulty X Y d d').card ≤ f) (hx : ∃ x, x ∉ mergeFaulty X Y d d') : v = v' := by
  obtain ⟨x, hx⟩ := hx
  set c : P → ℕ → Option V := fun _ _ => none
  set ρ := mergeRun X Y (taskInv I) (taskInv I') o o' d d' c
  set ρ' := mergeRun Y X (taskInv I') (taskInv I) o' o d' d c
  have hρv : ρ.Valid f := mergeRun_valid _ _ _ _ _ _ _ _ _ hcard ho ho'
  have hρ'v : ρ'.Valid f := mergeRun_valid _ _ _ _ _ _ _ _ _ (by rwa [mergeFaulty_comm]) ho' ho
  have hρi : ρ.inv = taskInv (fun x => if x ∈ X then I' x else I x) := by
    funext y t; simp only [ρ, mergeRun, taskInv, c]; split_ifs <;> first | rfl | omega
  have hρ'i : ρ'.inv = taskInv (fun x => if x ∈ Y then I x else I' x) := by
    funext y t; simp only [ρ', mergeRun, taskInv, c]; split_ifs <;> first | rfl | omega
  have hZ' : ∀ z, z ∉ X → z ∉ Y → taskInv I z 0 = taskInv I' z 0 := fun z h1 h2 => by
    simp [taskInv, hZ z h1 h2]
  -- `x` decides some `w` in `ρ`, hence also in `ρ'`
  obtain ⟨t, w, hw⟩ := hA.termination ρ _ hρv hρi x (mergeRun_crash_of_not_mem _ _ _ _ _ _ _ _ _ hx)
  have hw' : ρ'.DecidesAt A x t w := by
    unfold Run.DecidesAt at hw ⊢; rw [← mergeRun_st_symm A hXY hZ' ho ho' hx]; exact hw
  -- `d` decides `v` in `ρ`, `d'` decides `v'` in `ρ'`
  have hdv : ρ.DecidesAt A d τ v := by
    unfold Run.DecidesAt at hv ⊢
    rw [mergeRun_st_follow A c hd τ hτ d hd (Or.inr rfl)]; exact hv
  have hdv' : ρ'.DecidesAt A d' τ' v' := by
    unfold Run.DecidesAt at hv' ⊢
    rw [mergeRun_st_follow A c hd' τ' hτ' d' hd' (Or.inr rfl)]; exact hv'
  have e1 := hA.agreement ρ _ hρv hρi d x τ t v w hdv hw
  have e2 := hA.agreement ρ' _ hρ'v hρ'i d' x τ' t v' w hdv' hw'
  rw [e1, e2]

/-- The invocations of the merged runs are well formed if those of `σ`, `σ'` are and the extra
process `r`, which invokes `propose(a)` at time `3`, never invokes in `σ`, `σ'`. -/
theorem mergeRun_wellFormed {X Y : Finset P} {i i' : P → ℕ → Option V}
    {o o' : P → ℕ → List (P × M) → List (P × M)} {d d' : P}
    (hwf : (syncRun (M := M) X i o).WellFormed) (hwf' : (syncRun (M := M) Y i' o').WellFormed)
    {r : P} (hri : ∀ t, i r t = none ∧ i' r t = none) (a : V) :
    (mergeRun X Y i i' o o' d d' (fun y t => if y = r ∧ t = 3 then some a else none)).WellFormed := by
  intro p t t' h h'
  simp only [mergeRun] at h h'
  have hr1 := fun t => (hri t).1
  have hr2 := fun t => (hri t).2
  split_ifs at h h' with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 <;>
    first
    | exact hwf' p t t' h h'
    | exact hwf p t t' h h'
    | omega
    | (obtain ⟨rfl, rfl⟩ := h4; simp_all)
    | (obtain ⟨rfl, rfl⟩ := h6; simp_all)
    | (obtain ⟨rfl, rfl⟩ := h7; simp_all)
    | simp_all

/-- **Merge lemma, object version.** As `merge_task`, for an `f`-resilient consensus object
protocol: `σ` (`X`-faulty, invocations `i`) and `σ'` (`Y`-faulty, invocations `i'`) are well
formed, the processes outside `X ∪ Y` invoke the same at time `0` in both, `d` returns `v` in `σ`
and `d'` returns `v'` in `σ'` by time `2Δ`. If `|Π \ (X ∪ Y) ∪ {d, d'}| ≤ f` and some process
`r ∉ Π \ (X ∪ Y) ∪ {d, d'}` never invokes in `σ`, `σ'`, then `v = v'`. (In the merged runs `r`
invokes `propose` at time `3`; by wait-freedom it returns.) -/
theorem merge_object {A : Protocol P V M S} {f : ℕ} (hA : SolvesObject A f) {X Y : Finset P}
    (hXY : Disjoint X Y) {i i' : P → ℕ → Option V} (hZ : ∀ z, z ∉ X → z ∉ Y → i z 0 = i' z 0)
    {o o' : P → ℕ → List (P × M) → List (P × M)} (ho : IsOrder o) (ho' : IsOrder o')
    (hwf : (syncRun (M := M) X i o).WellFormed) (hwf' : (syncRun (M := M) Y i' o').WellFormed)
    {d d' : P} (hd : d ∉ X) (hd' : d' ∉ Y) {τ τ' : ℕ} (hτ : τ ≤ 3) (hτ' : τ' ≤ 3) {v v' : V}
    (hv : (syncRun X i o).RespondsAt A d τ v) (hv' : (syncRun Y i' o').RespondsAt A d' τ' v')
    (hcard : (mergeFaulty X Y d d').card ≤ f) {r : P} (hr : r ∉ mergeFaulty X Y d d')
    (hri : ∀ t, i r t = none ∧ i' r t = none) : v = v' := by
  set c : P → ℕ → Option V := fun y t => if y = r ∧ t = 3 then some v else none
  set ρ := mergeRun X Y i i' o o' d d' c
  set ρ' := mergeRun Y X i' i o' o d' d c
  have hρv : ρ.Valid f := mergeRun_valid _ _ _ _ _ _ _ _ _ hcard ho ho'
  have hρ'v : ρ'.Valid f := mergeRun_valid _ _ _ _ _ _ _ _ _ (by rwa [mergeFaulty_comm]) ho' ho
  have hρw : ρ.WellFormed := mergeRun_wellFormed hwf hwf' hri v
  have hρ'w : ρ'.WellFormed :=
    mergeRun_wellFormed hwf' hwf (fun t => ⟨(hri t).2, (hri t).1⟩) v
  have hrXY := (not_mem_mergeFaulty hr).1
  -- `r` returns some `w` in `ρ`, hence also in `ρ'`
  obtain ⟨t, w, hw⟩ := hA.waitFree ρ hρv hρw r 3 v
    (mergeRun_crash_of_not_mem _ _ _ _ _ _ _ _ _ hr) (by simp [ρ, mergeRun, c])
  have hw' : ρ'.RespondsAt A r t w := by
    obtain ⟨⟨t₀, ht₀, hinv⟩, hdec⟩ := hw
    refine ⟨⟨t₀, ht₀, by rwa [← mergeRun_inv_symm hXY hrXY]⟩, ?_⟩
    unfold Run.DecidesAt at hdec ⊢; rw [← mergeRun_st_symm A hXY hZ ho ho' hr]; exact hdec
  -- `d` returns `v` in `ρ`, `d'` returns `v'` in `ρ'`
  have hdv : ρ.RespondsAt A d τ v := by
    obtain ⟨⟨t₀, ht₀, hinv⟩, hdec⟩ := hv
    refine ⟨⟨t₀, ht₀, ?_⟩, ?_⟩
    · simpa [ρ, mergeRun, syncRun, hd, show t₀ < 3 by omega] using hinv
    · unfold Run.DecidesAt at hdec ⊢
      rw [mergeRun_st_follow A c hd τ hτ d hd (Or.inr rfl)]; exact hdec
  have hdv' : ρ'.RespondsAt A d' τ' v' := by
    obtain ⟨⟨t₀, ht₀, hinv⟩, hdec⟩ := hv'
    refine ⟨⟨t₀, ht₀, ?_⟩, ?_⟩
    · simpa [ρ', mergeRun, syncRun, hd', show t₀ < 3 by omega] using hinv
    · unfold Run.DecidesAt at hdec ⊢
      rw [mergeRun_st_follow A c hd' τ' hτ' d' hd' (Or.inr rfl)]; exact hdec
  have e1 := hA.agreement ρ hρv hρw d r τ t v w hdv hw
  have e2 := hA.agreement ρ' hρ'v hρ'w d' r τ' t v' w hdv' hw'
  rw [e1, e2]

end TwoStepConsensus
