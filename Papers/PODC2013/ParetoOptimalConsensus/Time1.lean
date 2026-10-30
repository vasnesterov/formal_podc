import Papers.PODC2013.ParetoOptimalConsensus.Majority

/-!
# Forcing decisions at time 1

The core argument of Lemma 7 (majority consensus) and of Lemma 14, Part 1 (uniform consensus):
in a protocol in which processes with enough copies of `v` in sight decide by time 1, such
processes cannot decide `1 - v`. The proof is the paper's induction on `n - |Z_i|` with its three
cases (a hidden initial node; a seen initial node with the other value; neither), each of which
builds a run indistinguishable to `i` at time 1 in which another process `j`, still correct and
seeing more (or as many) `v`s, is forced to decide `v` (`time1_forcing`).
-/

namespace Podc.ParetoOptimalConsensus

open Cslib Finset Podc.UnbeatableSetConsensus

variable {P : Type*} [Fintype P] {t : ℕ}

omit [Fintype P] in
/-- The time-`0` nodes seen at time `1`. -/
lemma seen_zero_one_iff {r : Run P} {q p : P} : Seen r q 0 p 1 ↔ q = p ∨ (q ≠ p ∧ r.Deliv q p 0) := by
  rw [seen_succ_iff le_rfl]
  constructor
  · rintro (h | ⟨x, hx, h⟩)
    · exact Or.inl (seen_same_time h)
    · obtain rfl := seen_same_time h; exact Or.inr hx
  · rintro (rfl | h)
    · exact Or.inl (seen_self le_rfl)
    · exact Or.inr ⟨q, h, seen_self le_rfl⟩

section Helpers

variable {Q : Protocol P} (hQ : SolvesSetConsensus 1 t bin Q)

include hQ in
lemma decides_of_no_opp {r : Run P} (hr : Adm t bin r) {j : P} {m v : ℕ} (hv : v ∈ bin)
    (hd : DecidesBy Q r j m) (hno : ∀ m' ≤ m, ¬ DecidesAt Q r j m' (1 - v)) :
    ∃ m' ≤ m, DecidesAt Q r j m' v := by
  obtain ⟨m', hm', u, hu⟩ := hd
  have hub : u ∈ bin := mem_bin_of_mem_vals hr (dec_mem_vals' hQ hr hu)
  rcases eq_or_eq_one_sub hv hub with rfl | rfl
  · exact ⟨m', hm', hu⟩
  · exact absurd hu (hno m' hm')

include hQ in
lemma no_opp_of_witness {r r' : Run P} (hr' : Adm t bin r') {i j : P} {M v : ℕ} (hv : v ∈ bin)
    (hsv : SameView r r' i M) (hi : ¬ r'.Faulty i) (hj : ¬ r'.Faulty j)
    (hw : ∃ m'', DecidesAt Q r' j m'' v) : ∀ m' ≤ M, ¬ DecidesAt Q r i m' (1 - v) := by
  intro m' hm' hd
  obtain ⟨m'', hw⟩ := hw
  have hd' : DecidesAt Q r' i m' (1 - v) :=
    (hsv.decidesAt_iff Q hm' ⟨fun _ => SyncCrash.Run.alive_of_not_faulty hi _, fun _ => hd.1⟩).1 hd
  exact one_sub_ne hv (agree_of_le_one hQ hr' hi hj hd' hw)


end Helpers

section Time1

variable {Q : Protocol P} (ht : 0 < t) (hQ : SolvesSetConsensus 1 t bin Q)
  {v : ℕ} (hv : v ∈ bin) {c : ℕ} (hc : 2 ≤ c)
  (hdec : ∀ r : Run P, Adm t bin r → ∀ p, r.Alive p 1 → r.input p = v →
    c ≤ (seenWith r p 1 v).card → DecidesBy Q r p 1)

/-- The time-1 forcing claim for `|Z_i| = ℓ`. -/
def T1Claim (t : ℕ) (Q : Protocol P) (v c ℓ : ℕ) : Prop :=
  ∀ r : Run P, Adm t bin r → ∀ i, r.Alive i 1 → (seenWith r i 1 v).card = ℓ →
    c ≤ ℓ → ∀ m' ≤ 1, ¬ DecidesAt Q r i m' (1 - v)

include ht hQ hv hc hdec in
/-- Case I of Lemma 7: some initial node is hidden from `⟨i, 1⟩`. -/
lemma t1_caseI {ℓ : ℕ} (ih : T1Claim t Q v c (ℓ + 1)) {r : Run P} (hr : Adm t bin r) {i : P}
    (hal : r.Alive i 1) (hcard : (seenWith r i 1 v).card = ℓ)
    (hthr : c ≤ ℓ) {k : P} (hk : ¬ Seen r k 0 i 1) :
    ∀ m' ≤ 1, ¬ DecidesAt Q r i m' (1 - v) := by
  classical
  obtain ⟨j, hjZ, hji⟩ := exists_mem_ne (by omega :
    1 < (seenWith r i 1 v).card) i
  have hjZ' := mem_seenWith.1 hjZ
  have hki : k ≠ i := fun h => hk (h ▸ seen_self (Nat.zero_le 1))
  have hkj : k ≠ j := fun h => hk (h ▸ hjZ'.1)
  have hjd : r.Deliv j i 0 := Seen.deliv_of_succ hjZ'.1 hji
  set r' : Run P :=
    { input := fun p => if p = k then v else r.input p
      crash := fun p => if p = i ∨ p = j then none else r.crash p
      reach := fun p => if r.crash p = some 1 then
          (if i ∈ r.reach p ∨ p = k then insert j (r.reach p) else r.reach p \ {j})
        else r.reach p }
  have hcr : ∀ p, p ≠ i → p ≠ j → r'.crash p = r.crash p := fun p h1 h2 => by
    simp [r', h1, h2]
  have hcij : ∀ p, (p = i ∨ p = j) → r'.crash p = none := fun p h => by simp [r', h]
  -- round-1 deliveries in `r'`
  have hdi : ∀ q, q ≠ i → (r'.Deliv q i 0 ↔ r.Deliv q i 0) := by
    intro q hqi
    by_cases hqj : q = j
    · subst hqj; simp only [deliv_of_crash_none (hcij q (Or.inr rfl)), hjd]
    cases hq : r.crash q with
    | none =>
      simp only [deliv_of_crash_none hq, deliv_of_crash_none ((hcr q hqi hqj).trans hq)]
    | some c =>
      rw [deliv_of_crash_some ((hcr q hqi hqj).trans hq), deliv_of_crash_some hq]
      by_cases hc1 : c = 1
      · subst hc1
        simp only [r', hq, ite_true]
        split_ifs <;> simp [Ne.symm hji]
      · simp [r', hq, hc1]
  have hdj : ∀ q, q ≠ i → q ≠ j → (r'.Deliv q j 0 ↔ r.Deliv q i 0 ∨ q = k) := by
    intro q h1 h2
    cases hq : r.crash q with
    | none =>
      simp only [deliv_of_crash_none hq, deliv_of_crash_none ((hcr q h1 h2).trans hq), true_or]
    | some c =>
      rw [deliv_of_crash_some ((hcr q h1 h2).trans hq), deliv_of_crash_some hq]
      by_cases hc1 : c = 1
      · subst hc1
        simp only [r', hq, ite_true, lt_irrefl, false_or, true_and]
        split_ifs with h
        · simp only [Set.mem_insert_iff, true_or, true_iff]
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr h
        · simp only [Set.mem_sdiff, Set.mem_singleton_iff, not_true_eq_false, and_false,
            false_iff]
          exact h
      · have := hr.1.2 q c hq
        have hlt : 1 < c := by omega
        simp [hlt]
  have hr' : Adm t bin r' := by
    refine ⟨⟨le_trans (card_le_card fun p hp => ?_) hr.1.1, fun p c hc => ?_⟩, fun p => ?_⟩
    · rw [SyncCrash.Run.mem_faulty] at hp ⊢
      by_cases h : p = i ∨ p = j
      · exact absurd (hcij p h) hp
      · push Not at h; unfold SyncCrash.Run.Faulty at hp ⊢; rwa [hcr p h.1 h.2] at hp
    · by_cases h : p = i ∨ p = j
      · rw [hcij p h] at hc; cases hc
      · push Not at h; rw [hcr p h.1 h.2] at hc; exact hr.1.2 p c hc
    · simp only [r']; split_ifs
      · exact hv
      · exact hr.2 p
  have hsv : SameView r r' i 1 := by
    refine sameView_of_agree (fun q hq => ?_) (fun q s hq w hw => ?_)
    · have : q ≠ k := fun h => hk (h ▸ hq)
      simp [r', this]
    · obtain rfl : s = 0 := by have := hq.le; omega
      obtain rfl := seen_same_time hq
      exact (hdi w hw).symm
  -- `Z_j = Z_i ∪ {k}` in `r'`
  have hZ : seenWith r' j 1 v = insert k (seenWith r i 1 v) := by
    ext q
    rw [mem_seenWith, mem_insert, mem_seenWith, seen_zero_one_iff, seen_zero_one_iff]
    by_cases hqk : q = k
    · subst hqk
      simp only [r', ite_true, true_or, iff_true, and_true]
      exact Or.inr ⟨hkj, (hdj q hki hkj).2 (Or.inr rfl)⟩
    have hin : r'.input q = r.input q := by simp [r', hqk]
    rw [hin]
    by_cases hqj : q = j
    · subst hqj; simp only [true_or, true_and, hqk, false_or]
      exact ⟨fun h => ⟨Or.inr ⟨hji, hjd⟩, h⟩, fun h => h.2⟩
    by_cases hqi : q = i
    · subst hqi
      simp only [hqk, false_or, true_or, true_and]
      refine ⟨fun h => h.2, fun h => ⟨Or.inr ⟨hqj, ?_⟩, h⟩⟩
      exact deliv_of_crash_none (hcij q (Or.inl rfl)) j 0
    simp only [hqj, hqi, false_or, hqk, ne_eq, not_false_eq_true, true_and]
    rw [hdj q hqi hqj]; simp [hqk]
  have hkZ : k ∉ seenWith r i 1 v := fun h => hk (mem_seenWith.1 h).1
  have hjc : ¬ r'.Faulty j := by rw [not_faulty_iff]; exact hcij j (Or.inr rfl)
  have hic : ¬ r'.Faulty i := by rw [not_faulty_iff]; exact hcij i (Or.inl rfl)
  have hcard' : (seenWith r' j 1 v).card = ℓ + 1 := by rw [hZ, card_insert_of_notMem hkZ, hcard]
  have hthr' : c ≤ ℓ + 1 := by omega
  have hno := ih r' hr' j (SyncCrash.Run.alive_of_not_faulty hjc 1) hcard' hthr'
  obtain ⟨m'', -, hw⟩ := decides_of_no_opp hQ hr' hv
    (hdec r' hr' j (SyncCrash.Run.alive_of_not_faulty hjc 1) (by simp [r', hkj.symm, hjZ'.2])
      (by rw [hcard']; exact hthr')) hno
  exact no_opp_of_witness hQ hr' hv hsv hic hjc ⟨m'', hw⟩

include ht hQ hv hc hdec in
/-- Case II of Lemma 7: all initial nodes are seen and some other process has input `1 - v`. -/
lemma t1_caseII {ℓ : ℕ} (ih : T1Claim t Q v c (ℓ + 1)) {r : Run P} (hr : Adm t bin r) {i : P}
    (hal : r.Alive i 1) (hcard : (seenWith r i 1 v).card = ℓ)
    (hthr : c ≤ ℓ) {k : P} (hki : k ≠ i) (hkv : r.input k = 1 - v) :
    ∀ m' ≤ 1, ¬ DecidesAt Q r i m' (1 - v) := by
  classical
  by_cases hun : ∃ k', ¬ Seen r k' 0 i 1
  · obtain ⟨k', hk'⟩ := hun
    exact t1_caseI ht hQ hv hc hdec ih hr hal hcard hthr hk'
  push Not at hun
  obtain ⟨j, hjZ, hji⟩ := exists_mem_ne (by omega :
    1 < (seenWith r i 1 v).card) i
  have hjv := (mem_seenWith.1 hjZ).2
  have hkj : k ≠ j := by rintro rfl; rw [hkv] at hjv; exact one_sub_ne hv hjv
  set r'' : Run P :=
    { input := r.input
      crash := fun p => if p = k then some 1 else none
      reach := fun _ => {x | x ≠ j} }
  have hr'' : Adm t bin r'' := by
    refine ⟨⟨?_, fun p c hc => ?_⟩, hr.2⟩
    · have : r''.faulty ⊆ {k} := by
        intro p hp
        simp only [SyncCrash.Run.mem_faulty, SyncCrash.Run.Faulty, r''] at hp
        simp only [mem_singleton]; by_contra h; simp [h] at hp
      exact (card_le_card this).trans (by rw [card_singleton]; omega)
    · simp only [r''] at hc; split_ifs at hc <;> cases hc; omega
  have hdel : ∀ q p, r''.Deliv q p 0 ↔ (q = k → p ≠ j) := by
    intro q p
    by_cases hq : q = k
    · subst hq
      rw [deliv_of_crash_some (show r''.crash q = some 1 by simp [r''])]
      simp [r'']
    · simp [hq, deliv_of_crash_none (show r''.crash q = none by simp [r'', hq])]
  have hsv : SameView r r'' i 1 := by
    refine sameView_of_agree (fun q _ => rfl) (fun q s hq w hw => ?_)
    obtain rfl : s = 0 := by have := hq.le; omega
    obtain rfl := seen_same_time hq
    rw [hdel]
    exact ⟨fun _ _ => Ne.symm hji, fun _ => Seen.deliv_of_succ (hun w) hw⟩
  have hjc : ¬ r''.Faulty j := by rw [not_faulty_iff]; simp [r'', Ne.symm hkj]
  have hic : ¬ r''.Faulty i := by rw [not_faulty_iff]; simp [r'', Ne.symm hki]
  -- `j` sees everything except `⟨k, 0⟩`, which has input `1 - v`
  have hZ : seenWith r'' j 1 v = seenWith r i 1 v := by
    ext q
    rw [mem_seenWith, mem_seenWith, seen_zero_one_iff]
    simp only [hdel]
    by_cases hqk : q = k
    · subst hqk
      rw [hkv]
      exact iff_of_false (fun h => one_sub_ne hv h.2) (fun h => one_sub_ne hv h.2)
    · simp only [hqk, IsEmpty.forall_iff, and_true]
      constructor
      · rintro ⟨-, h⟩; exact ⟨hun q, h⟩
      · rintro ⟨-, h⟩; refine ⟨?_, h⟩; by_cases hqj : q = j <;> simp [hqj]
  have hkn : ¬ Seen r'' k 0 j 1 := by
    rw [seen_zero_one_iff, hdel]; simp [hkj]
  have hcard' : (seenWith r'' j 1 v).card = ℓ := by rw [hZ, hcard]
  have hno := t1_caseI ht hQ hv hc hdec ih hr'' (SyncCrash.Run.alive_of_not_faulty hjc 1) hcard'
    hthr hkn
  obtain ⟨m'', -, hw⟩ := decides_of_no_opp hQ hr'' hv
    (hdec r'' hr'' j (SyncCrash.Run.alive_of_not_faulty hjc 1) hjv
      (by rw [hcard']; exact hthr)) hno
  exact no_opp_of_witness hQ hr'' hv hsv hic hjc ⟨m'', hw⟩

include ht hQ hv hc hdec in
lemma t1_step {ℓ : ℕ} (ih : T1Claim t Q v c (ℓ + 1)) (hℓ : ℓ < Fintype.card P) :
    T1Claim t Q v c ℓ := by
  classical
  intro r hr i hal hcard hthr
  by_cases hun : ∃ k', ¬ Seen r k' 0 i 1
  · obtain ⟨k', hk'⟩ := hun
    exact t1_caseI ht hQ hv hc hdec ih hr hal hcard hthr hk'
  push Not at hun
  by_cases hk : ∃ k, k ≠ i ∧ r.input k = 1 - v
  · obtain ⟨k, hki, hkv⟩ := hk
    exact t1_caseII ht hQ hv hc hdec ih hr hal hcard hthr hki hkv
  push Not at hk
  -- Case III: all other processes have input `v`, so `i` has `1 - v`
  have hothers : ∀ q, q ≠ i → r.input q = v := by
    intro q hq
    rcases eq_or_eq_one_sub hv (hr.2 q) with h | h
    · exact h
    · exact absurd h (hk q hq)
  have hiv : r.input i ≠ v := by
    intro h
    have : seenWith r i 1 v = univ := by
      ext q; simp only [mem_seenWith, mem_univ, iff_true]
      refine ⟨hun q, ?_⟩; by_cases hq : q = i
      · rw [hq, h]
      · exact hothers q hq
    rw [this, card_univ] at hcard; omega
  obtain ⟨j, -, hji⟩ := exists_mem_ne (by omega :
    1 < (seenWith r i 1 v).card) i
  set r''' : Run P := { input := r.input, crash := fun _ => none, reach := fun _ => ∅ }
  have hall : ∀ p, ¬ r'''.Faulty p := fun p => by simp [SyncCrash.Run.Faulty, r''']
  have hr''' : Adm t bin r''' :=
    ⟨⟨by simp [SyncCrash.Run.faulty, hall], fun p c hc => by simp [r'''] at hc⟩, hr.2⟩
  have hsv : SameView r r''' i 1 := by
    refine sameView_of_agree (fun q _ => rfl) (fun q s hq w hw => ?_)
    obtain rfl : s = 0 := by have := hq.le; omega
    obtain rfl := seen_same_time hq
    exact ⟨fun _ => SyncCrash.Run.deliv_of_not_faulty (hall w) q 0,
      fun _ => Seen.deliv_of_succ (hun w) hw⟩
  have hsj : ∀ q, Seen r''' q 0 j 1 := fun q => by
    rw [seen_zero_one_iff]
    by_cases hq : q = j
    · exact Or.inl hq
    · exact Or.inr ⟨hq, SyncCrash.Run.deliv_of_not_faulty (hall q) j 0⟩
  have hZ : seenWith r''' j 1 v = seenWith r i 1 v := by
    ext q; rw [mem_seenWith, mem_seenWith]
    exact ⟨fun h => ⟨hun q, h.2⟩, fun h => ⟨hsj q, h.2⟩⟩
  have hcard' : (seenWith r''' j 1 v).card = ℓ := by rw [hZ, hcard]
  have hiv' : r'''.input i = 1 - v := by
    rcases eq_or_eq_one_sub hv (hr.2 i) with h | h
    · exact absurd h hiv
    · exact h
  have hno := t1_caseII ht hQ hv hc hdec ih hr''' (SyncCrash.Run.alive_of_not_faulty (hall j) 1)
    hcard' hthr (Ne.symm hji) hiv'
  obtain ⟨m'', -, hw⟩ := decides_of_no_opp hQ hr''' hv
    (hdec r''' hr''' j (SyncCrash.Run.alive_of_not_faulty (hall j) 1) (hothers j hji)
      (by rw [hcard']; exact hthr)) hno
  exact no_opp_of_witness hQ hr''' hv hsv (hall i) (hall j) ⟨m'', hw⟩

include ht hQ hv hc hdec in
lemma t1_claim : ∀ d ℓ, ℓ + d = Fintype.card P → T1Claim t Q v c ℓ := by
  classical
  intro d
  induction d with
  | zero =>
    intro ℓ hℓ r hr i _ hcard _ m' _ hd
    have huniv : seenWith r i 1 v = univ := eq_univ_of_card _ (by rw [hcard]; omega)
    obtain ⟨j, hj⟩ := hQ.validity r hr i m' (1 - v) hd
    have := (mem_seenWith.1 (huniv ▸ mem_univ j : j ∈ seenWith r i 1 v)).2
    rw [hj] at this; exact one_sub_ne hv this
  | succ d ihd =>
    intro ℓ hℓ
    exact t1_step ht hQ hv hc hdec (ihd (ℓ + 1) (by omega)) (by omega)

include ht hQ hv hc hdec in
/-- **Forcing at time 1** (the common core of Lemma 7 and Lemma 14, Part 1). Let `Q` solve
consensus (`t > 0`), and assume that `Q` makes every live process `p` with input `v` that has
seen at least `c ≥ 2` processes with input `v` at time `1` decide by time `1`. Then a live
process that has seen at least `c` processes with input `v` at time `1` does not decide `1 - v`
by time `1`. Induction on `n - |Z_i|` with the cases I–III of the paper's proof of Lemma 7. -/
theorem time1_forcing {r : Run P} (hr : Adm t bin r) {i : P} (hal : r.Alive i 1)
    (hcZ : c ≤ (seenWith r i 1 v).card) : ∀ m' ≤ 1, ¬ DecidesAt Q r i m' (1 - v) :=
  t1_claim ht hQ hv hc hdec (Fintype.card P - (seenWith r i 1 v).card)
    (seenWith r i 1 v).card (by have := card_le_univ (seenWith r i 1 v); omega) r hr i hal rfl hcZ

end Time1

end Podc.ParetoOptimalConsensus
