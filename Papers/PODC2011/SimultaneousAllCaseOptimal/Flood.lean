import Papers.PODC2011.SimultaneousAllCaseOptimal.Consensus
import Cslib.Computability.Distributed.SyncCrash.Floodset

/-!
# Flooding input values: FloodSet consensus and a continuous-consensus protocol for `t = 1`

Every process floods the set of `(process, input)` pairs it knows (`known`). Results:
* accuracy of the known sets, and their equality among processes alive after a round without
  crashes (`known_hist_eq_of_clean`, `known_hist_agree`);
* `floodSet R` (decide the minimum known value at time `R`) solves simultaneous consensus, with all
  processes alive at time `R` deciding at time `R`, when `t < R` or `n ≤ R + 1`
  (`floodSet_solvesSim`, `floodSet_decides`);
* for `t = 1`, `floodCC` (core = the known pairs from time `2 = t + 1 − W` on) has all the ConCon
  properties of §2.3 used by the paper (`floodCC_isConCon`).
-/

namespace Podc.SimultaneousAllCaseOptimal

open Cslib.SyncCrash Cslib.Byzantine.LockStep

variable {P I O : Type} [Fintype P] [DecidableEq P] [DecidableEq I]

/-- Messages of the flooding protocols: sets of `(process, input)` pairs. -/
abbrev FloodMsg (P I : Type) := Finset (P × I)

/-- The pairs known to `p` (input `x`) after the history `h`: its own pair and every pair received. -/
def known (p : P) (x : I) (h : History P (FloodMsg P I)) : Finset (P × I) :=
  h.foldl (fun S inbox => S ∪ Finset.univ.biUnion fun s => (inbox s).getD ∅) {(p, x)}

/-- FloodSet consensus: flood the known pairs; at time `R` decide the minimum known value. -/
def floodSet [LinearOrder I] (R : ℕ) : Protocol P I (FloodMsg P I) I where
  send p x h _ := some (known p x h)
  decide p x h := if R ≤ h.length then some ((known p x h).fold min x Prod.snd) else none

/-- The known pairs of `p` at time `m` of the run `r` (for any protocol with the flooding
messages, e.g. `floodSet R`). -/
noncomputable def knownAt [LinearOrder I] (r : Run P I) (m : ℕ) (p : P) : Finset (P × I) :=
  known p (r.input p) (hist (floodSet (I := I) 0) r m p)

/-- Histories of all flooding protocols coincide (they only differ in their decisions). -/
lemma hist_floodSet [LinearOrder I] (R R' : ℕ) (r : Run P I) (m : ℕ) (p : P) :
    hist (floodSet (P := P) (I := I) R) r m p = hist (floodSet R') r m p :=
  hist_eq_of_send (A := floodSet R) (B := floodSet R') rfl r m p

lemma knownAt_zero [LinearOrder I] (r : Run P I) (p : P) :
    knownAt r 0 p = {(p, r.input p)} := by
  simp [knownAt, known]

/-- One round of flooding: `p` adds the known pairs of every process whose message reaches it. -/
lemma mem_knownAt_succ [LinearOrder I] {r : Run P I} {m : ℕ} {p : P} {x : P × I} :
    x ∈ knownAt r (m + 1) p ↔
      x ∈ knownAt r m p ∨ ∃ s, s ≠ p ∧ r.Deliv s p m ∧ x ∈ knownAt r m s := by
  classical
  simp only [knownAt, known, Cslib.SyncCrash.hist_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  apply or_congr Iff.rfl
  apply exists_congr; intro s
  rw [msg_eq_deliv]
  split_ifs with h
  · simp [floodSet, h.1, h.2, known]
  · simp only [Option.getD_none, Finset.notMem_empty, false_iff]
    tauto

lemma knownAt_mono [LinearOrder I] (r : Run P I) {m m' : ℕ} (hm : m ≤ m') (p : P) :
    knownAt r m p ⊆ knownAt r m' p := by
  induction m', hm using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact fun x hx => mem_knownAt_succ.2 (Or.inl (ih hx))

/-- Accuracy: known pairs are actual inputs. -/
lemma mem_knownAt [LinearOrder I] {r : Run P I} {m : ℕ} {p q : P} {v : I}
    (h : (q, v) ∈ knownAt r m p) : r.input q = v := by
  induction m generalizing p with
  | zero =>
    rw [knownAt_zero, Finset.mem_singleton, Prod.mk.injEq] at h
    rw [h.1, h.2]
  | succ m ih =>
    rcases mem_knownAt_succ.1 h with h | ⟨s, -, -, h⟩
    · exact ih h
    · exact ih h

/-- Own pair, and pairs of processes whose round-1 message reached `p`, are known from time 1. -/
lemma self_mem_knownAt [LinearOrder I] (r : Run P I) (m : ℕ) (p : P) :
    (p, r.input p) ∈ knownAt r m p :=
  knownAt_mono r (Nat.zero_le m) p (by simp [knownAt_zero])

lemma mem_knownAt_of_deliv [LinearOrder I] {r : Run P I} {m : ℕ} {p q : P} (hm : 1 ≤ m)
    (hd : r.Deliv q p 0) : (q, r.input q) ∈ knownAt r m p := by
  refine knownAt_mono r hm p ?_
  by_cases hqp : q = p
  · subst hqp; exact self_mem_knownAt r 1 q
  · exact mem_knownAt_succ.2 (Or.inr ⟨q, hqp, hd, self_mem_knownAt r 0 q⟩)

/-- After a clean round `j + 1 ≤ m`, a process alive at time `m` knows exactly the pairs known at
time `j` by the processes alive at time `j`. -/
lemma mem_knownAt_of_clean [LinearOrder I] {r : Run P I} {j m : ℕ} (hjm : j < m)
    (hclean : ∀ s, r.crash s ≠ some (j + 1)) {p : P} (hp : r.Alive p m) {x : P × I} :
    x ∈ knownAt r m p ↔ ∃ s, r.Alive s j ∧ x ∈ knownAt r j s := by
  induction m, hjm using Nat.le_induction generalizing p with
  | base =>
    rw [mem_knownAt_succ]
    constructor
    · rintro (h | ⟨s, -, hs, h⟩)
      · exact ⟨p, hp.mono (by omega), h⟩
      · exact ⟨s, hs.1, h⟩
    · rintro ⟨s, hs, h⟩
      by_cases hsp : s = p
      · subst hsp; exact Or.inl h
      · exact Or.inr ⟨s, hsp, ⟨hs, fun hc => hclean s hc.1⟩, h⟩
  | succ m hm ih =>
    rw [mem_knownAt_succ, ih (hp.mono (by omega))]
    constructor
    · rintro (h | ⟨s, -, hs, h⟩)
      · exact h
      · exact (ih hs.1).1 h
    · exact Or.inl

/-- After a round `j + 1 ≤ m` in which nobody crashes, all processes alive at time `m` know the
same pairs. -/
lemma known_hist_eq_of_clean [LinearOrder I] {r : Run P I} {j m : ℕ} (hjm : j < m)
    (hclean : ∀ s, r.crash s ≠ some (j + 1)) {p q : P} (hp : r.Alive p m) (hq : r.Alive q m) :
    knownAt r m p = knownAt r m q := by
  ext x
  rw [mem_knownAt_of_clean hjm hclean hp, mem_knownAt_of_clean hjm hclean hq]

omit [DecidableEq P] [DecidableEq I] in
/-- With at most `t < R` crashes, one of the rounds `1, …, R` is clean. -/
lemma exists_clean_lt {r : Run P I} {t R : ℕ} (hr : r.Admissible t) (hR : t < R) :
    ∃ j < R, ∀ s, r.crash s ≠ some (j + 1) := by
  classical
  obtain ⟨j, -, hj, h⟩ := exists_clean_round (T := 0) (R := R) r <| by
    refine lt_of_le_of_lt (le_trans (Finset.card_le_card fun s hs => ?_) hr.1) hR
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Run.mem_faulty] at hs ⊢
    obtain ⟨c, hc, -⟩ := hs
    simp [Run.Faulty, hc]
  exact ⟨j, by omega, h⟩

/-- With at most `t` crashes and `t < R` or `n ≤ R + 1`, the processes alive at time `R` know the
same pairs (some round `≤ R` is clean, or a single process is alive). -/
lemma known_hist_agree [LinearOrder I] {r : Run P I} {t R : ℕ} (hr : r.Admissible t)
    (hR : t < R ∨ Fintype.card P ≤ R + 1) {p q : P} (hp : r.Alive p R) (hq : r.Alive q R) :
    knownAt r R p = knownAt r R q := by
  classical
  by_cases hpq : p = q
  · rw [hpq]
  have hclean : ∃ j < R, ∀ s, r.crash s ≠ some (j + 1) := by
    rcases hR with hR | hR
    · exact exists_clean_lt hr hR
    obtain ⟨j, -, hj, h⟩ := exists_clean_round (T := 0) (R := R) r <| by
      have hsub : (Finset.univ.filter
          (fun s => ∃ c, r.crash s = some c ∧ 0 < c ∧ c ≤ 0 + R)) ⊆
          (Finset.univ.erase p).erase q := by
        intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
        obtain ⟨c, hc, -, hcR⟩ := hs
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · subst h; have := hq c hc; omega
        · subst h; have := hp c hc; omega
      refine lt_of_le_of_lt (Finset.card_le_card hsub) ?_
      rw [Finset.card_erase_of_mem (by simp [Ne.symm hpq]), Finset.card_erase_of_mem (by simp),
        Finset.card_univ]
      have : 2 ≤ Fintype.card P := by
        rw [← Finset.card_pair hpq]; exact Finset.card_le_univ _
      omega
    exact ⟨j, by omega, h⟩
  obtain ⟨j, hj, h⟩ := hclean
  exact known_hist_eq_of_clean hj h hp hq

/-- The output register of `floodSet R`: empty before time `R`, the minimum known value from
time `R` on. -/
lemma raw_floodSet [LinearOrder I] (R : ℕ) (r : Run P I) (m : ℕ) (p : P) :
    raw (floodSet R) r p m =
      if R ≤ m then some ((knownAt r m p).fold min (r.input p) Prod.snd) else none := by
  rw [raw, hist_floodSet R 0]
  simp only [floodSet, Cslib.SyncCrash.length_hist, knownAt]

omit [Fintype P] [DecidableEq P] [DecidableEq I] in
/-- The minimum over a set of pairs does not depend on the initial value if it is in the set. -/
lemma fold_min_eq_of_mem [LinearOrder I] {S : Finset (P × I)} {a b : P × I} (ha : a ∈ S)
    (hb : b ∈ S) : S.fold min a.2 Prod.snd = S.fold min b.2 Prod.snd := by
  have key : ∀ {a b : P × I}, a ∈ S → b ∈ S → S.fold min a.2 Prod.snd ≤ S.fold min b.2 Prod.snd :=
    fun {a b} ha hb => (Finset.le_fold_min _).2
      ⟨(Finset.fold_min_le _).2 (Or.inr ⟨b, hb, le_rfl⟩),
        fun x hx => (Finset.fold_min_le _).2 (Or.inr ⟨x, hx, le_rfl⟩)⟩
  exact le_antisymm (key ha hb) (key hb ha)

omit [Fintype P] in
/-- The minimum is the initial value or the value of an element. -/
lemma fold_min_mem [LinearOrder I] (S : Finset (P × I)) (x : I) :
    S.fold min x Prod.snd = x ∨ ∃ y ∈ S, S.fold min x Prod.snd = y.2 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.fold_insert ha]
    rcases min_choice a.2 (S.fold min x Prod.snd) with h | h <;> rw [h]
    · exact Or.inr ⟨a, Finset.mem_insert_self _ _, rfl⟩
    · rcases ih with h' | ⟨y, hy, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨y, Finset.mem_insert_of_mem hy, h'⟩

/-- The minimum known value of `p` is some process's input. -/
lemma exists_input_fold_min [LinearOrder I] (r : Run P I) (m : ℕ) (p : P) :
    ∃ q, r.input q = (knownAt r m p).fold min (r.input p) Prod.snd := by
  rcases fold_min_mem (knownAt r m p) (r.input p) with h | ⟨y, hy, h⟩
  · exact ⟨p, h.symm⟩
  · exact ⟨y.1, by rw [h]; exact mem_knownAt (q := y.1) (v := y.2) hy⟩

/-- In `floodSet R` every process alive at time `R` decides at time `R`, on the minimum of its
known values. -/
lemma floodSet_decides [LinearOrder I] {R : ℕ} {r : Run P I} {p : P} (hp : r.Alive p R) :
    Decides (floodSet R) r p R ((knownAt r R p).fold min (r.input p) Prod.snd) := by
  refine decides_iff.2 ⟨hp, ?_, fun m' hm' => ?_⟩
  · rw [raw_floodSet, ite_eq_left le_rfl]
  · rw [raw_floodSet, ite_eq_right (by omega)]

/-- `floodSet R` decides only at time `R`. -/
lemma floodSet_decides_time [LinearOrder I] {R : ℕ} {r : Run P I} {p : P} {m : ℕ} {d : I}
    (h : Decides (floodSet R) r p m d) : m = R := by
  have h1 := h.raw_eq
  rw [raw_floodSet] at h1
  have hRm : R ≤ m := by by_contra hc; rw [ite_eq_right hc] at h1; simp at h1
  by_contra hne
  have h2 := h.raw_lt (lt_of_le_of_ne hRm (Ne.symm hne))
  rw [raw_floodSet, ite_eq_left le_rfl] at h2
  simp at h2

/-- FloodSet solves simultaneous consensus (decisions at time `R`) when `t < R` or `n ≤ R + 1`.
(`P` must be nonempty: with no processes there is no output vector allowed by `consensus`.) -/
theorem floodSet_solvesSim [LinearOrder I] [Nonempty P] {t R : ℕ}
    (hR : t < R ∨ Fintype.card P ≤ R + 1) :
    SolvesSim (floodSet R) (consensus P I) t where
  complete r _ p hp := ⟨R, _, floodSet_decides (Run.alive_of_not_faulty hp R)⟩
  correct r hr := by
    by_cases hex : ∃ p₀, r.Alive p₀ R
    · obtain ⟨p₀, hp₀⟩ := hex
      refine consensus_correct_of (exists_input_fold_min r R p₀) fun p m d hd => ?_
      rw [floodSet_decides_time hd] at hd
      have hpa := hd.alive
      rw [(hd.unique (floodSet_decides hpa)).2, known_hist_agree hr.1 hR hpa hp₀]
      exact fold_min_eq_of_mem (a := (p, r.input p)) (b := (p₀, r.input p₀))
        (by rw [← known_hist_agree hr.1 hR hpa hp₀]; exact self_mem_knownAt r R p)
        (self_mem_knownAt r R p₀)
    · obtain ⟨q⟩ := ‹Nonempty P›
      refine consensus_correct_of ⟨q, rfl⟩ fun p m d hd => ?_
      rw [floodSet_decides_time hd] at hd
      exact absurd ⟨p, hd.alive⟩ hex
  simultaneous r _ p q m m' d d' hp hq := by
    rw [floodSet_decides_time hp, floodSet_decides_time hq]

open Classical in
/-- The continuous-consensus protocol for `t = 1`: flood the known pairs; from time `2` on, the
core is the set of known pairs. -/
noncomputable def floodCC : CCProtocol P I (FloodMsg P I) where
  send p x h _ := some (known p x h)
  core p x h q := if hh : 2 ≤ h.length ∧ ∃ v, (q, v) ∈ known p x h then
    some (Classical.choose hh.2) else none

/-- The core of `floodCC`: from time `2` on, the known pairs (with their actual input values). -/
lemma floodCC_coreAt [LinearOrder I] (r : Run P I) (p : P) (m : ℕ) (q : P) :
    floodCC.coreAt r p m q =
      if 2 ≤ m ∧ (q, r.input q) ∈ knownAt r m p then some (r.input q) else none := by
  have hh : hist floodCC.toProtocol r m p = hist (floodSet (I := I) 0) r m p :=
    hist_eq_of_send (A := floodCC.toProtocol) (B := floodSet (I := I) 0) rfl r m p
  have key : ∀ (h : History P (FloodMsg P I)),
      (∀ q v, (q, v) ∈ known p (r.input p) h → r.input q = v) →
      floodCC.core p (r.input p) h q =
        if 2 ≤ h.length ∧ (q, r.input q) ∈ known p (r.input p) h then some (r.input q) else none := by
    intro h hacc
    simp only [floodCC]
    split_ifs with h1 h2 h2
    · rw [hacc q _ (Classical.choose_spec h1.2)]
    · exact absurd ⟨h1.1, by
        have := Classical.choose_spec h1.2; rwa [← hacc q _ this] at this⟩ h2
    · exact absurd ⟨h2.1, _, h2.2⟩ h1
    · rfl
  rw [CCProtocol.coreAt, key _ (fun q v hv => mem_knownAt (r := r) (m := m) (p := p)
    (by rw [knownAt, ← hh]; exact hv)), hh, Cslib.SyncCrash.length_hist]
  rfl

/-- With `t = 1` the waste of every run is `0`. -/
lemma waste_eq_zero {r : Run P I} (hr : r.Admissible 1) : r.waste = 0 := by
  have := waste_lt hr le_rfl; omega

/-- `floodCC_isConCon` for a given linear order on the inputs (used only to phrase `knownAt`). -/
theorem floodCC_isConCon_aux [LinearOrder I] (T : Task P I O) :
    IsConCon (floodCC (P := P) (I := I)) T 1 where
  accurate r _ p m q v _ h := by
    rw [floodCC_coreAt] at h
    split_ifs at h
    simpa using h
  consistent r hr p q m hp hq := by
    funext s
    rw [floodCC_coreAt, floodCC_coreAt]
    by_cases hm : 2 ≤ m
    · obtain ⟨j, hj, hc⟩ := exists_clean_lt hr.1 (show 1 < 2 by omega)
      rw [known_hist_eq_of_clean (by omega) hc hp hq]
    · simp [hm]
  empty r hr p m _ hm q := by
    rw [floodCC_coreAt, waste_eq_zero hr.1] at *
    rw [ite_eq_right (by omega)]
  full r hr p q hp hq := by
    rw [waste_eq_zero hr.1] at hp hq ⊢
    have hk : (q, r.input q) ∈ knownAt r (1 + 1 - 0) p :=
      mem_knownAt_of_deliv (by omega) ⟨hr.1.alive_zero q, fun hc => by have := hq 1 hc.1; omega⟩
    rw [floodCC_coreAt, ite_eq_left ⟨by omega, hk⟩]

/-- For `t = 1`, `floodCC` has the ConCon properties of §2.3 (for any task). -/
theorem floodCC_isConCon (T : Task P I O) : IsConCon (floodCC (P := P) (I := I)) T 1 := by
  -- `knownAt` is phrased via `floodSet`, which needs some linear order on `I`; any one will do.
  let _ : LinearOrder I := IsWellOrder.linearOrder WellOrderingRel
  exact floodCC_isConCon_aux T

end Podc.SimultaneousAllCaseOptimal
