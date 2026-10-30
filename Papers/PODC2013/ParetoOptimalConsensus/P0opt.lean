import Papers.PODC2013.ParetoOptimalConsensus.Consensus

/-!
# Corollary 1: the protocol `P0opt` of Halpern–Moses–Waarts is beatable (§3)

The paper describes `P0opt` of [HMW] as: decide `0` when `∃0` is known; "a process decides `1`
following a round in which it has not discovered a new failure". We read "discovering a failure"
as knowledge (full-information protocol): `i` knows at time `m` that `p` has crashed iff
`⟨p, m⟩` is guaranteed crashed at `⟨i, m⟩` (`GuarCrashed r i m p m`); the rule for `1` fires at
`m ≥ 1` if every failure known at `m` was already known at `m - 1` (`p0opt`).

* `opt0_dominates_p0opt`: `Opt0 ⪰ P0opt` (no new failure in round `m` ⇒ no hidden path at `m`).
* **Corollary 1** (`corollary1`): `P0opt` is not unbeatable if `t ≥ 2` and `n ≥ 4` (the paper's
  example: one failure discovered in each of rounds 1 and 2, all initial nodes seen at time 2),
  and if `2 ≤ n ≤ t + 1` (every other process crashes silently in round 1) — in particular for
  `n = 3, t = 2` and `n = 2, t = 1`.
* For `t ≤ 1` (and `n ≥ 3`, or `t = 0` and `n ≥ 2`), `P0opt` and `Opt0` take exactly the same
  decisions (`p0opt_sameDecisions`), so **`P0opt` is unbeatable there** (`p0opt_unbeatable`):
  Corollary 1 needs `t ≥ 2` (or `t = n - 1`).
-/

namespace Podc.ParetoOptimalConsensus

open Cslib Finset Podc.UnbeatableSetConsensus

variable {P : Type*} [Fintype P] {t : ℕ}

/-- No new failure is discovered in round `m` (`m ≥ 1`): every process known at `m` to have
crashed was known at `m - 1` to have crashed. -/
def NoNewFailure (r : Run P) (i : P) (m : ℕ) : Prop :=
  0 < m ∧ ∀ p, GuarCrashed r i m p m → GuarCrashed r i (m - 1) p (m - 1)

omit [Fintype P] in
lemma noNewFailure_iff_of_sameView {r r' : Run P} {i : P} {m : ℕ} (h : SameView r r' i m) :
    NoNewFailure r i m ↔ NoNewFailure r' i m := by
  unfold NoNewFailure
  simp only [h.guarCrashed_iff, (h.mono (Nat.sub_le m 1)).guarCrashed_iff]

open Classical in
/-- **Protocol `P0opt`** of [HMW] as described in §3. -/
noncomputable def p0opt : Protocol P where
  dec r i m := if 0 ∈ vals r i m then some 0 else if NoNewFailure r i m then some 1 else none
  dec_congr r r' i m h := by simp only [h.vals_eq, noNewFailure_iff_of_sameView h]

lemma p0opt_dec_eq_none {r : Run P} {i : P} {m : ℕ} :
    p0opt.dec r i m = none ↔ 0 ∉ vals r i m ∧ ¬ NoNewFailure r i m := by
  unfold p0opt; simp only
  split_ifs <;> simp_all

/-- No new failure in round `m` implies that no node at time `m - 1` is hidden. -/
lemma not_hiddenPath_of_noNewFailure {r : Run P} {i : P} {m : ℕ} (h : NoNewFailure r i m) :
    ¬ HiddenPath r i m := by
  obtain ⟨hm, h⟩ := h
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  refine not_hiddenPath_iff.2 ⟨M, Nat.le_succ M, fun q hq => ?_⟩
  have hqi : q ≠ i := hq.ne (Nat.le_succ M)
  have hnd : ¬ r.Deliv q i M := fun hd => hq.1 (seen_of_deliv hqi hd)
  have hg := h q ⟨i, M, Nat.lt_succ_self M, seen_self le_rfl, hqi.symm, hnd⟩
  simp only [Nat.add_sub_cancel] at hg
  obtain ⟨h', s, hs, hseen, hne, hd⟩ := hg
  exact hq.2 ⟨h', s, hs, hseen.mono_right (Nat.le_succ M), hne, hd⟩

lemma optA_dec_ne_none_of_p0opt {r : Run P} {i : P} {m : ℕ} (h : p0opt.dec r i m ≠ none) :
    (opt0 : Protocol P).dec r i m ≠ none := by
  rw [Ne, p0opt_dec_eq_none, not_and_or, not_not, not_not] at h
  rcases h with h | h
  · exact optA_dec_ne_none_of_mem h
  · exact optA_dec_ne_none_of_not_hiddenPath (not_hiddenPath_of_noNewFailure h)

/-- `Opt0 ⪰ P0opt`. -/
theorem opt0_dominates_p0opt : Dominates t bin (opt0 : Protocol P) p0opt := fun r _ i m _ hv =>
  decidesBy_of_dec hv.1 (optA_dec_ne_none_of_p0opt (by rw [hv.2.1]; simp))

/-- `P0opt` solves consensus (for every `t`), so `corollary1` concerns a genuine solution that is
strictly dominated, not a protocol that fails to solve the problem. -/
theorem p0opt_solves : SolvesSetConsensus 1 t bin (p0opt : Protocol P) where
  decision r hr i hi := by
    classical
    by_contra hne
    have hnone : ∀ m, p0opt.dec r i m = none := fun m => by
      by_contra h
      obtain ⟨m', -, v, hv⟩ := decidesBy_of_dec (SyncCrash.Run.alive_of_not_faulty hi m) h
      exact hne ⟨m', v, hv⟩
    -- without a round free of new failures, the set of known failures grows every round
    let S : ℕ → Finset P := fun m => univ.filter fun p => GuarCrashed r i m p m
    have hgrow : ∀ m, m ≤ (S m).card := by
      intro m
      induction m with
      | zero => exact Nat.zero_le _
      | succ m ih =>
        have hnn : ¬ NoNewFailure r i (m + 1) := (p0opt_dec_eq_none.1 (hnone (m + 1))).2
        have : ∃ p, GuarCrashed r i (m + 1) p (m + 1) ∧ ¬ GuarCrashed r i m p m := by
          by_contra h; push Not at h
          exact hnn ⟨Nat.succ_pos m, fun p hp => by simpa using h p hp⟩
        obtain ⟨p, hp1, hp2⟩ := this
        have hsub : S m ⊂ S (m + 1) := by
          refine (ssubset_iff_of_subset (fun q hq => ?_)).2
            ⟨p, by simpa [S] using hp1, by simpa [S] using hp2⟩
          obtain ⟨h, s, hs, hseen, hne, hd⟩ := (mem_filter.1 hq).2
          exact mem_filter.2 ⟨mem_univ _, h, s, by omega, hseen.mono_right (Nat.le_succ m), hne, hd⟩
        have := card_lt_card hsub
        omega
    have hle : (S (t + 1)).card ≤ t := by
      refine (card_le_card fun p hp => ?_).trans hr.1.1
      rw [SyncCrash.Run.mem_faulty]
      by_contra hpf
      exact not_guarCrashed_of_alive (SyncCrash.Run.alive_of_not_faulty hpf _) (mem_filter.1 hp).2
    have := hgrow (t + 1)
    omega
  validity r hr i m v hv := by
    have h2 := hv.2.1
    simp only [p0opt] at h2
    split_ifs at h2 with h3 h4 <;> cases h2
    · obtain ⟨j, -, hj⟩ := mem_vals.1 h3; exact ⟨j, hj⟩
    · obtain ⟨j, -, hj⟩ := mem_vals.1 (one_sub_mem_vals hr zero_mem_bin h3); exact ⟨j, hj⟩
  agreement r hr := by
    classical
    rw [Nat.cast_one, Set.encard_le_one_iff]
    have hval : ∀ {i m v}, DecidesAt p0opt r i m v →
        (0 ∈ vals r i m ∧ v = 0) ∨ (0 ∉ vals r i m ∧ NoNewFailure r i m ∧ v = 1) := by
      intro i m v hv
      have h2 := hv.2.1
      simp only [p0opt] at h2
      split_ifs at h2 with h3 h4 <;> cases h2
      · exact Or.inl ⟨h3, rfl⟩
      · exact Or.inr ⟨h3, h4, rfl⟩
    -- a decision on `1` (no new failure, hence no hidden path) excludes any correct holder of `0`
    have key : ∀ {i j m m'}, ¬ r.Faulty j → DecidesAt p0opt r i m 1 → DecidesAt p0opt r j m' 0 →
        False := by
      intro i j m m' hj hi hj0
      rcases hval hi with ⟨-, h⟩ | ⟨hn, hnf, -⟩
      · cases h
      rcases hval hj0 with ⟨hm, -⟩ | ⟨-, -, h⟩
      · obtain ⟨ℓ, hℓ, hnh⟩ := not_hiddenPath_iff.1 (not_hiddenPath_of_noNewFailure hnf)
        exact hn (vals_subset_of_not_hidden hℓ hnh hj m' hm)
      · cases h
    rintro v w ⟨i, m, hi, hv⟩ ⟨j, m', hj, hw⟩
    rcases hval hv with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> rcases hval hw with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
    · rfl
    · exact (key hi hw hv).elim
    · exact (key hj hv hw).elim
    · rfl

/-- If `Opt0` decides at a time by which `P0opt` has not decided, `P0opt` is not unbeatable. -/
lemma not_unbeatable_of_strict {r : Run P} (hr : Adm t bin r) {i : P} {m : ℕ}
    (hi : ¬ r.Faulty i) (ho : (opt0 : Protocol P).dec r i m ≠ none)
    (hp : ∀ m' ≤ m, p0opt.dec r i m' = none) : ¬ Unbeatable 1 t bin (p0opt : Protocol P) := by
  intro hu
  have hdom := hu.2 opt0 (optA_solves zero_mem_bin) opt0_dominates_p0opt
  obtain ⟨m', hm', v, hv⟩ := decidesBy_of_dec (SyncCrash.Run.alive_of_not_faulty hi m) ho
  obtain ⟨n, hn, w, hw⟩ := hdom r hr i m' v hv
  have := hp n (hn.trans hm')
  rw [hw.2.1] at this; cases this

/-! ### The examples -/

section Examples

variable (a b c : P)

open Classical in
/-- The paper's example: all inputs `1`; `a` crashes in round 1 reaching only `b`, `c` crashes in
round 2 reaching nobody. -/
noncomputable def exRun : Run P where
  input _ := 1
  crash p := if p = a then some 1 else if p = c then some 2 else none
  reach p := if p = a then {b} else ∅

variable {i a b c : P}

lemma exRun_adm (hd : [i, a, b, c].Nodup) (ht : 2 ≤ t) : Adm t bin (exRun a b c) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hia, hib, hic⟩, ⟨hab, hac⟩, hbc, -⟩ := hd
  refine ⟨⟨?_, fun p c' hc' => ?_⟩, fun _ => one_mem_bin⟩
  · have : (exRun a b c).faulty ⊆ {a, c} := by
      intro p hp
      simp only [SyncCrash.Run.mem_faulty, SyncCrash.Run.Faulty, exRun] at hp
      simp only [mem_insert, mem_singleton]
      by_contra h; push Not at h; simp [h.1, h.2] at hp
    exact (card_le_card this).trans ((card_le_two).trans ht)
  · simp only [exRun] at hc'
    split_ifs at hc' <;> cases hc' <;> omega

omit [Fintype P] in
lemma exRun_crash_a : (exRun a b c).crash a = some 1 := by simp [exRun]
omit [Fintype P] in
lemma exRun_crash_c (hac : a ≠ c) : (exRun a b c).crash c = some 2 := by
  simp [exRun, Ne.symm hac]
omit [Fintype P] in
lemma exRun_crash_other {p : P} (hpa : p ≠ a) (hpc : p ≠ c) : (exRun a b c).crash p = none := by
  simp [exRun, hpa, hpc]

lemma exRun_example (hd : [i, a, b, c].Nodup) (ht : 2 ≤ t) :
    ¬ Unbeatable 1 t bin (p0opt : Protocol P) := by
  classical
  have hd' := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd'
  obtain ⟨⟨hia, hib, hic⟩, ⟨hab, hac⟩, hbc, -⟩ := hd'
  set r := exRun a b c
  have hr := exRun_adm hd ht
  have hic' : ¬ r.Faulty i := by
    rw [not_faulty_iff]; exact exRun_crash_other hia hic
  have hbc' : ¬ r.Faulty b := by
    rw [not_faulty_iff]; exact exRun_crash_other (Ne.symm hab) hbc
  have hnv : ∀ m, 0 ∉ vals r i m := by
    intro m h; obtain ⟨_, -, h⟩ := mem_vals.1 h; simp [r, exRun] at h
  -- `a` reaches `b` in round 1, `c` reaches everybody in round 1
  have hab1 : r.Deliv a b 0 := by
    rw [deliv_of_crash_some exRun_crash_a]; right; simp [exRun]
  have hc1 : ∀ p, r.Deliv c p 0 := fun p => by
    rw [deliv_of_crash_some (exRun_crash_c hac)]; left; omega
  have hai : ¬ r.Deliv a i 0 := by
    rw [deliv_of_crash_some exRun_crash_a]; simp [exRun, hib]
  have hci : ¬ r.Deliv c i 1 := by
    rw [deliv_of_crash_some (exRun_crash_c hac)]; simp [exRun, Ne.symm hac]
  refine not_unbeatable_of_strict hr hic' (m := 2) ?_ ?_
  · -- at time 2 all initial nodes are seen, so there is no hidden path
    refine optA_dec_ne_none_of_not_hiddenPath (not_hiddenPath_iff.2 ⟨0, by omega, fun q hq => ?_⟩)
    apply hq.1
    by_cases hqi : q = i
    · subst hqi; exact seen_self (by omega)
    by_cases hqa : q = a
    · subst hqa
      exact (seen_of_deliv hab hab1).trans
        (seen_of_deliv (Ne.symm hib) (SyncCrash.Run.deliv_of_not_faulty hbc' i 1))
    by_cases hqc : q = c
    · subst hqc; exact (seen_of_deliv hqi (hc1 i)).mono_right (by omega)
    · exact (seen_of_deliv hqi (deliv_of_crash_none (exRun_crash_other hqa hqc) i 0)).mono_right
        (by omega)
  · intro m' hm'
    rw [p0opt_dec_eq_none]
    refine ⟨hnv m', ?_⟩
    rintro ⟨hpos, h⟩
    interval_cases m'
    · -- round 1: the failure of `a` is new
      have := h a ⟨i, 0, Nat.zero_lt_one, seen_self le_rfl, hia, hai⟩
      obtain ⟨_, s, hs, -⟩ := this; omega
    · -- round 2: the failure of `c` is new
      have := h c ⟨i, 1, Nat.lt_succ_self 1, seen_self le_rfl, hic, hci⟩
      obtain ⟨h', s, hs, hseen, -, hdd⟩ := this
      obtain rfl : s = 0 := by omega
      have := seen_same_time hseen
      subst this
      exact hdd (hc1 _)

open Classical in
/-- Every process other than `i` crashes in round 1 sending nothing; all inputs are `1`. -/
noncomputable def exRun2 (i : P) : Run P where
  input _ := 1
  crash p := if p = i then none else some 1
  reach _ := ∅

lemma exRun2_example (hn : 2 ≤ Fintype.card P) (ht : Fintype.card P ≤ t + 1) (i : P) :
    ¬ Unbeatable 1 t bin (p0opt : Protocol P) := by
  classical
  set r := exRun2 i
  have hr : Adm t bin r := by
    refine ⟨⟨?_, fun p c' hc' => ?_⟩, fun _ => one_mem_bin⟩
    · have : r.faulty ⊆ univ.erase i := by
        intro p hp
        simp only [SyncCrash.Run.mem_faulty, SyncCrash.Run.Faulty, r, exRun2] at hp
        simp only [mem_erase, mem_univ, and_true]
        rintro rfl; simp at hp
      have := card_le_card this
      rw [card_erase_of_mem (mem_univ i), card_univ] at this
      omega
    · simp only [r, exRun2] at hc'; split_ifs at hc' <;> cases hc'; omega
  have hic : ¬ r.Faulty i := by rw [not_faulty_iff]; simp [r, exRun2]
  have hnd : ∀ q, q ≠ i → ¬ r.Deliv q i 0 := by
    intro q hq
    rw [deliv_of_crash_some (show r.crash q = some 1 by simp [r, exRun2, hq])]
    simp [r, exRun2]
  obtain ⟨q, hq⟩ : ∃ q, q ≠ i := by
    by_contra h; push Not at h
    have : Fintype.card P ≤ 1 := Fintype.card_le_one_iff.2 fun x y => (h x).trans (h y).symm
    omega
  refine not_unbeatable_of_strict hr hic (m := 1) ?_ ?_
  · refine optA_dec_ne_none_of_not_hiddenPath (not_hiddenPath_iff.2 ⟨1, le_rfl, fun p hp => ?_⟩)
    by_cases hpi : p = i
    · subst hpi; exact hp.1 (seen_self le_rfl)
    · exact hp.2 ⟨i, 0, Nat.zero_lt_one, seen_self le_rfl, Ne.symm hpi, hnd p hpi⟩
  · intro m' hm'
    rw [p0opt_dec_eq_none]
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨_, -, h⟩ := mem_vals.1 h; simp [r, exRun2] at h
    · rintro ⟨hpos, h⟩
      obtain rfl : m' = 1 := by omega
      obtain ⟨_, s, hs, -⟩ := h q ⟨i, 0, Nat.zero_lt_one, seen_self le_rfl, Ne.symm hq, hnd q hq⟩
      omega

end Examples

/-- **Corollary 1.** The protocol `P0opt` of [HMW] is not unbeatable, when `t ≥ 2` and `n ≥ 4`,
or when `2 ≤ n ≤ t + 1`: `Opt0` strictly dominates it. -/
theorem corollary1 (h : (2 ≤ t ∧ 4 ≤ Fintype.card P) ∨ (2 ≤ Fintype.card P ∧ Fintype.card P ≤ t + 1)) :
    ¬ Unbeatable 1 t bin (p0opt : Protocol P) := by
  classical
  rcases h with ⟨ht, hn⟩ | ⟨hn, ht⟩
  · obtain ⟨l, hl, hnd⟩ : ∃ l : List P, l.length = 4 ∧ l.Nodup := by
      obtain ⟨s, hs⟩ := exists_subset_card_eq (s := (univ : Finset P)) (n := 4) (by simpa)
      exact ⟨s.toList, by simp [hs.2], s.nodup_toList⟩
    match l, hl, hnd with
    | [i, a, b, c], _, hnd => exact exRun_example hnd ht
  · have : Nonempty P := Fintype.card_pos_iff.1 (by omega)
    exact exRun2_example hn ht (Classical.arbitrary P)

/-! ### For `t ≤ 1`, `P0opt = Opt0` -/

/-- With `t ≤ 1` (and not `n = 2, t = 1`, and `n ≥ 2`), `P0opt` has fired by time `m` iff `Opt0`
has. -/
lemma p0opt_fired_iff (hn : 2 ≤ Fintype.card P) (ht : t ≤ 1)
    (hnt : ¬ (t = 1 ∧ Fintype.card P = 2)) {r : Run P} (hr : Adm t bin r) (i : P) (m : ℕ) :
    (∃ m' ≤ m, p0opt.dec r i m' ≠ none) ↔ ∃ m' ≤ m, (opt0 : Protocol P).dec r i m' ≠ none := by
  classical
  constructor
  · rintro ⟨m', hm', h⟩; exact ⟨m', hm', optA_dec_ne_none_of_p0opt h⟩
  rintro ⟨m', hm', h⟩
  rw [Ne, optA_dec_eq_none, not_and_or, not_not] at h
  rcases h with h | h
  · refine ⟨m', hm', ?_⟩; rw [Ne, p0opt_dec_eq_none]; tauto
  -- crashes known to `i` are crashes of the run; there is at most one
  have hgf : ∀ {s p}, GuarCrashed r i s p s → p ∈ r.faulty := by
    intro s p hg
    rw [SyncCrash.Run.mem_faulty]
    by_contra hp; exact not_guarCrashed_of_alive (SyncCrash.Run.alive_of_not_faulty hp s) hg
  have hcard : r.faulty.card ≤ 1 := hr.1.1.trans ht
  -- if no failure is known at time 1, `P0opt` fires at 1; otherwise it fires at 2
  have hfire : 2 ≤ m' → ∃ m'' ≤ m', p0opt.dec r i m'' ≠ none := by
    intro h2
    by_cases h1 : ∃ p, GuarCrashed r i 1 p 1
    · obtain ⟨p, hp⟩ := h1
      refine ⟨2, h2, ?_⟩
      simp only [Ne, p0opt_dec_eq_none, not_and_or, not_not]
      refine Or.inr ⟨by omega, fun q hq => ?_⟩
      have : q = p := card_le_one.1 hcard q (hgf hq) p (hgf hp)
      subst this; exact hp
    · push Not at h1
      refine ⟨1, by omega, ?_⟩
      simp only [Ne, p0opt_dec_eq_none, not_and_or, not_not]
      exact Or.inr ⟨Nat.zero_lt_one, fun q hq => absurd hq (h1 q)⟩
  rcases Nat.lt_or_ge m' 2 with hlt | hge
  · obtain ⟨ℓ, hℓ, hnh⟩ := not_hiddenPath_iff.1 h
    interval_cases m'
    · -- time 0: every other process is hidden
      obtain rfl : ℓ = 0 := by omega
      obtain ⟨q, hq⟩ : ∃ q, q ≠ i := by
        by_contra h; push Not at h
        have : Fintype.card P ≤ 1 := Fintype.card_le_one_iff.2 fun x y => (h x).trans (h y).symm
        omega
      exact absurd (hidden_zero_iff.2 fun hs => hq (seen_same_time hs)) (hnh q)
    · interval_cases ℓ
      · -- no hidden initial node: `i` heard from everybody in round 1
        refine ⟨1, hm', ?_⟩
        simp only [Ne, p0opt_dec_eq_none, not_and_or, not_not]
        refine Or.inr ⟨Nat.zero_lt_one, fun q hq => ?_⟩
        obtain ⟨h', s, hs, hseen, hne, hd⟩ := hq
        obtain rfl : s = 0 := by omega
        obtain rfl := seen_same_time hseen
        by_contra
        exact hnh q (hidden_zero_iff.2 fun hs' =>
          hd (Seen.deliv_of_succ hs' hne.symm))
      · -- no hidden node at time 1: every other process is known to have crashed
        exfalso
        have hsub : univ.erase i ⊆ r.faulty := by
          intro q hq
          have hqi := ne_of_mem_erase hq
          by_contra hqf
          rw [SyncCrash.Run.mem_faulty] at hqf
          exact hnh q (hidden_of_alive (SyncCrash.Run.alive_of_not_faulty hqf 1)
            fun hs => hqi (seen_same_time hs))
        have := card_le_card hsub
        rw [card_erase_of_mem (mem_univ i), card_univ] at this
        have := hr.1.1
        omega
  · obtain ⟨m'', hm'', h''⟩ := hfire hge
    exact ⟨m'', hm''.trans hm', h''⟩

/-- `P0opt` and `Opt0` take the same decisions when `t ≤ 1` (excluding `n = 2, t = 1`). -/
theorem p0opt_sameDecisions (hn : 2 ≤ Fintype.card P) (ht : t ≤ 1)
    (hnt : ¬ (t = 1 ∧ Fintype.card P = 2)) :
    SameDecisions t bin (opt0 : Protocol P) p0opt := by
  intro r hr i m v
  have hval : ∀ {Q : Protocol P} {n w}, (Q = opt0 ∨ Q = p0opt) → Q.dec r i n = some w →
      w = if 0 ∈ vals r i n then 0 else 1 := by
    rintro Q n w (rfl | rfl) h
    · simp only [optA] at h; split_ifs at h with h1 h2 <;> cases h <;> simp_all
    · simp only [p0opt] at h; split_ifs at h with h1 h2 <;> cases h <;> simp_all
  have hf := p0opt_fired_iff hn ht hnt hr i
  -- the first firing times coincide
  have key : ∀ n, (opt0 : Protocol P).dec r i n ≠ none → (∀ n' < n, (opt0 : Protocol P).dec r i n' = none) →
      p0opt.dec r i n ≠ none ∧ ∀ n' < n, p0opt.dec r i n' = none := by
    intro n hn1 hn2
    refine ⟨?_, fun n' hn' => ?_⟩
    · obtain ⟨n', hn', h⟩ := (hf n).2 ⟨n, le_rfl, hn1⟩
      rcases Nat.lt_or_eq_of_le hn' with hlt | rfl
      · exact absurd (hn2 n' hlt) (optA_dec_ne_none_of_p0opt h)
      · exact h
    · by_contra h
      exact optA_dec_ne_none_of_p0opt h (hn2 n' hn')
  have key' : ∀ n, p0opt.dec r i n ≠ none → (∀ n' < n, p0opt.dec r i n' = none) →
      (opt0 : Protocol P).dec r i n ≠ none ∧ ∀ n' < n, (opt0 : Protocol P).dec r i n' = none := by
    intro n hn1 hn2
    refine ⟨optA_dec_ne_none_of_p0opt hn1, fun n' hn' => ?_⟩
    by_contra h
    obtain ⟨n'', hn'', h''⟩ := (hf n').2 ⟨n', le_rfl, h⟩
    exact h'' (hn2 n'' (by omega))
  constructor
  · rintro ⟨hal, hd, hb⟩
    obtain ⟨h1, h2⟩ := key m (by rw [hd]; simp) hb
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 h1
    refine ⟨hal, ?_, h2⟩
    rw [hw, hval (Or.inr rfl) hw, ← hval (Or.inl rfl) hd]
  · rintro ⟨hal, hd, hb⟩
    obtain ⟨h1, h2⟩ := key' m (by rw [hd]; simp) hb
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 h1
    refine ⟨hal, ?_, h2⟩
    rw [hw, hval (Or.inl rfl) hw, ← hval (Or.inr rfl) hd]

/-- Consequently, for `t ≤ 1` (excluding `n = 2, t = 1`), `P0opt` **is** unbeatable: Corollary 1
needs `t ≥ 2` (or `t = n - 1`). -/
theorem p0opt_unbeatable (hn : 2 ≤ Fintype.card P) (ht : t ≤ 1)
    (hnt : ¬ (t = 1 ∧ Fintype.card P = 2)) : Unbeatable 1 t bin (p0opt : Protocol P) :=
  (p0opt_sameDecisions hn ht hnt).unbeatable theorem2

end Podc.ParetoOptimalConsensus
