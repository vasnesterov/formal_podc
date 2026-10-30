import Papers.PODC2013.ParetoOptimalConsensus.UOpt0

/-!
# Forced decisions on `0` in protocols dominating `U-P0`; Lemma 14 (Appendix C)

Throughout, `Q ⪰ U-P0` solves uniform consensus and `0 < t < n`.

* `decidesBy_of_kc`: a live process that knows `∃correct(0)` has decided (domination).
* `decides0_of_witness`: if `K_i ∃correct(0)` holds at `s` for the first time and some run that
  `i` cannot distinguish at `s` contains a decision on `0`, then `i` decides `0` at `s`.
* **Lemma 14** (`lemma14_part1`, `lemma14_part2`): decisions at time 1.
* `not_seen_of_inv`: a "speed of information" tool (nodes reachable from a closed region stay in
  it), used to show that some process never hears of a modification.
-/

namespace Podc.ParetoOptimalConsensus

open Cslib Finset Podc.UnbeatableSetConsensus

variable {P : Type*} [Fintype P] {t : ℕ}

omit [Fintype P] in
-- CSLib candidate: Cslib/Computability/Distributed/SyncCrash (full-information views)
/-- Nodes seen from a region of `(time, process)` pairs closed under message steps stay in it. -/
lemma not_seen_of_inv {r : Run P} {S : ℕ → P → Prop}
    (hstep : ∀ τ a b, S τ a → comm r τ a b → S (τ + 1) b) (hstay : ∀ τ a, S τ a → S (τ + 1) a)
    {j k : P} {ℓ s : ℕ} (h0 : S ℓ j) (hk : ¬ S s k) : ¬ Seen r j ℓ k s := fun hs =>
  hk (DynNet.Journey.of_inv (P := S) hs h0 fun τ a b _ _ ha hab => by
    rcases hab with rfl | hab
    · exact hstay τ a ha
    · exact hstep τ a b ha hab)

omit [Fintype P] in
-- CSLib candidate: Cslib/Computability/Distributed/SyncCrash (full-information views)
/-- Deliveries depend only on the crash round and on the reach set in the crashing round. -/
lemma deliv_congr {x y : Run P} {w h : P} {s : ℕ} (hc : x.crash w = y.crash w)
    (hR : x.crash w = some (s + 1) → (h ∈ x.reach w ↔ h ∈ y.reach w)) :
    x.Deliv w h s ↔ y.Deliv w h s := by
  rw [deliv_iff, deliv_iff]
  simp only [SyncCrash.Run.Alive, hc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun ⟨h3, h4⟩ => h2 ⟨h3, fun h5 => h4 ((hR (hc ▸ h3)).1 h5)⟩⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun ⟨h3, h4⟩ => h2 ⟨h3, fun h5 => h4 ((hR (hc ▸ h3)).2 h5)⟩⟩

section Forcing

variable {Q : Protocol P} (ht0 : 0 < t) (ht : t < Fintype.card P)
  (hQ : SolvesUniformSetConsensus 1 t bin Q) (hdom : Dominates t bin Q (uP0 t))

include hdom in
/-- A live process that knows `∃correct(0)` has decided in `Q ⪰ U-P0`. -/
lemma decidesBy_of_kc {r : Run P} (hr : Adm t bin r) {i : P} {m : ℕ} (hal : r.Alive i m)
    (hk : KCorrect t r i m 0) : DecidesBy Q r i m := by
  obtain ⟨n, hn, u, hu⟩ := decidesBy_of_dec hal (show (uP0 t : Protocol P).dec r i m ≠ none by
    rw [Ne, uP0_dec_eq_none]; tauto)
  exact DecidesBy.mono' (hdom r hr i n u hu) hn

include ht hQ hdom in
/-- **Forcing principle.** If `K_i ∃correct(0)` holds at `s` but not before, and in some run that
`i` cannot distinguish at `s` some process decides `0`, then `i` decides `0` at `s`. -/
lemma decides0_of_witness {r : Run P} (_hr : Adm t bin r) {i : P} {s : ℕ} (hal : r.Alive i s)
    (hk : KCorrect t r i s 0) (hnk : ∀ s' < s, ¬ KCorrect t r i s' 0) {r' : Run P}
    (hr' : Adm t bin r') (hsv : SameView r r' i s) (hal' : r'.Alive i s) {j : P} {m'' : ℕ}
    (hj : DecidesAt Q r' j m'' 0) : DecidesAt Q r i s 0 := by
  obtain ⟨s'', hs'', u, hu⟩ := decidesBy_of_kc hdom hr' hal' ((kCorrect_iff_of_sameView hsv).1 hk)
  obtain rfl : u = 0 := uagree hQ hr' hu hj
  have hk'' := lemma5 ht hQ hr' hu
  rw [← kCorrect_iff_of_sameView (hsv.mono hs'')] at hk''
  obtain rfl : s'' = s := by
    by_contra hne; exact hnk s'' (by omega) hk''
  exact (hsv.decidesAt_iff Q le_rfl ⟨fun _ => hal', fun _ => hal⟩).2 hu

include ht0 ht hQ hdom in
/-- A live process with input `0` that does not decide `1` by time `1` decides `0` at time `1`. -/
lemma decides0_at1 {r : Run P} (hr : Adm t bin r) {i : P} (hi0 : r.input i = 0)
    (hal : r.Alive i 1) (hno : ∀ m' ≤ 1, ¬ DecidesAt Q r i m' 1) : DecidesAt Q r i 1 0 := by
  have hk : KCorrect t r i 1 0 :=
    kCorrect_of_prev ht hr (M := 0) hal (by rw [vals_zero, hi0]; exact mem_singleton_self _)
  obtain ⟨m', hm', u, hu⟩ := decidesBy_of_kc hdom hr hal hk
  have hub : u ∈ bin := mem_bin_of_mem_vals hr (dec_mem_vals' (uniform_toSet hQ) hr hu)
  rcases mem_bin.1 hub with rfl | rfl
  · rcases Nat.lt_or_eq_of_le hm' with hlt | rfl
    · obtain rfl : m' = 0 := by omega
      exact absurd hu (lemma13 ht0 ht hQ hr i 0)
    · exact hu
  · exact absurd hu (hno m' hm')

include ht0 ht hQ hdom in
/-- **Lemma 14, Part 1.** If `t > 0`, a process `i` with input `0`, alive at time `1`, that has
seen another input `0` at time `1` decides `0` at time `1`. -/
theorem lemma14_part1 {r : Run P} (hr : Adm t bin r) {i : P} (hi0 : r.input i = 0)
    (hal : r.Alive i 1) (hj : ∃ j, j ≠ i ∧ r.input j = 0 ∧ Seen r j 0 i 1) :
    DecidesAt Q r i 1 0 := by
  classical
  have hdec : ∀ r : Run P, Adm t bin r → ∀ p, r.Alive p 1 → r.input p = 0 →
      2 ≤ (seenWith r p 1 0).card → DecidesBy Q r p 1 := by
    intro r hr p hp hp0 _
    exact decidesBy_of_kc hdom hr hp
      (kCorrect_of_prev ht hr (M := 0) hp (by rw [vals_zero, hp0]; exact mem_singleton_self _))
  obtain ⟨j, hji, hj0, hjs⟩ := hj
  have hZ : 2 ≤ (seenWith r i 1 0).card := by
    have : ({i, j} : Finset P) ⊆ seenWith r i 1 0 := by
      intro q hq
      rcases mem_insert.1 hq with rfl | hq
      · exact mem_seenWith.2 ⟨seen_self (Nat.zero_le 1), hi0⟩
      · rw [mem_singleton] at hq; subst hq; exact mem_seenWith.2 ⟨hjs, hj0⟩
    have := card_le_card this
    rwa [card_pair (Ne.symm hji)] at this
  exact decides0_at1 ht0 ht hQ hdom hr hi0 hal
    (time1_forcing ht0 (uniform_toSet hQ) zero_mem_bin le_rfl hdec hr hal hZ)

include ht0 ht hQ hdom in
/-- **Lemma 14, Part 2.** If `t > 1`, a process `i` with input `0`, alive at time `1`, that knows
of fewer than `t` failures at time `1` decides `0` at time `1`. -/
theorem lemma14_part2 (ht1 : 1 < t) {r : Run P} (hr : Adm t bin r) {i : P} (hi0 : r.input i = 0)
    (hal : r.Alive i 1) (hF : known r i 1 < t) : DecidesAt Q r i 1 0 := by
  classical
  refine decides0_at1 ht0 ht hQ hdom hr hi0 hal fun m' hm' hd1 => ?_
  by_cases hA : ∀ k, k ≠ i → ¬ Seen r k 0 i 1
  · -- `i` has seen only its own input
    have h1 := dec_mem_vals' (uniform_toSet hQ) hr hd1
    obtain ⟨q, hq, hq1⟩ := mem_vals.1 (vals_mono hm' h1)
    by_cases hqi : q = i
    · rw [hqi, hi0] at hq1; exact zero_ne_one hq1
    · exact hA q hqi hq
  push Not at hA
  obtain ⟨k, hki, hks⟩ := hA
  have hkd : r.Deliv k i 0 := Seen.deliv_of_succ hks hki
  have hKd : ∀ p, p ≠ i → (p ∈ knownSet r i 1 ↔ ¬ r.Deliv p i 0) := by
    intro p hp
    rw [mem_knownSet, guarCrashed_now_iff (by simpa using hal) Nat.zero_lt_one]
    simp [hp]
  have hkK : k ∉ knownSet r i 1 := fun h => ((hKd k hki).1 h) hkd
  -- a third process `j`, chosen among the known failures if there are any
  obtain ⟨j, hji, hjk, hjK⟩ : ∃ j, j ≠ i ∧ j ≠ k ∧ (0 < known r i 1 → j ∈ knownSet r i 1) := by
    by_cases hpos : 0 < known r i 1
    · rw [known_eq_card] at hpos
      obtain ⟨j, hj⟩ := card_pos.1 hpos
      refine ⟨j, fun h => ?_, fun h => hkK (h ▸ hj), fun _ => hj⟩
      exact not_guarCrashed_of_alive (h ▸ hal) (mem_knownSet.1 hj)
    · obtain ⟨j, hj⟩ : ∃ j, j ∉ ({i, k} : Finset P) := by
        by_contra h; push Not at h
        have := card_le_card (show (univ : Finset P) ⊆ {i, k} from fun x _ => h x)
        rw [card_univ] at this
        have := card_le_two (a := i) (b := k); omega
      simp only [mem_insert, mem_singleton, not_or] at hj
      exact ⟨j, hj.1, hj.2, fun h => absurd h hpos⟩
  set Kn := knownSet r i 1
  set r' : Run P :=
    { input := r.input
      crash := fun p => if p = i then some 2 else if p = j ∨ p ∈ Kn then some 1 else none
      reach := fun p => if p = j ∧ r.Deliv j i 0 then {i} else ∅ }
  set r'' : Run P :=
    { input := fun p => if p = j then 0 else r.input p
      crash := r'.crash
      reach := fun p => if p = j then {i} else ∅ }
  have hci : ∀ {x : Run P}, x.crash = r'.crash → x.crash i = some 2 := by
    intro x hx; rw [hx]; simp [r']
  have hcj : r'.crash j = some 1 := by simp [r', hji]
  have hcO : ∀ p, p ≠ i → p ≠ j → p ∉ Kn → r'.crash p = none := fun p h1 h2 h3 => by
    simp [r', h1, h2, h3]
  have hcK : ∀ p ∈ Kn, p ≠ i → r'.crash p = some 1 := fun p hp h1 => by simp [r', h1, hp]
  have hkc : ¬ r'.Faulty k := by rw [not_faulty_iff]; exact hcO k hki (Ne.symm hjk) hkK
  have hkc'' : ¬ r''.Faulty k := hkc
  have hadm : ∀ x : Run P, x.crash = r'.crash → (∀ p, x.input p ∈ bin) → Adm t bin x := by
    intro x hx hin
    refine ⟨⟨?_, fun p c hc => ?_⟩, hin⟩
    · have hsub : x.faulty ⊆ insert i (insert j Kn) := by
        intro p hp
        rw [SyncCrash.Run.mem_faulty, SyncCrash.Run.Faulty, hx] at hp
        simp only [mem_insert]
        by_contra h; push Not at h; exact hp (hcO p h.1 h.2.1 h.2.2)
      refine (card_le_card hsub).trans ?_
      by_cases hpos : 0 < known r i 1
      · rw [insert_eq_of_mem (hjK hpos)]
        have := card_insert_le i Kn; rw [← known_eq_card] at this; omega
      · have h1 := card_insert_le i (insert j Kn)
        have h2 := card_insert_le j Kn
        rw [← known_eq_card] at h2; omega
    · rw [hx] at hc; simp only [r'] at hc; split_ifs at hc <;> cases hc <;> omega
  have hr' : Adm t bin r' := hadm r' rfl hr.2
  have hr'' : Adm t bin r'' := hadm r'' rfl fun p => by
    simp only [r'']; split_ifs
    · exact zero_mem_bin
    · exact hr.2 p
  -- `i`'s view at time 1 is unchanged in `r'`
  have hsv : SameView r r' i 1 := by
    refine sameView_of_agree (fun _ _ => rfl) (fun h s hs w hw => ?_)
    obtain rfl : s = 0 := by have := hs.le; omega
    obtain rfl := seen_same_time hs
    by_cases hwj : w = j
    · subst hwj
      rw [deliv_of_crash_some hcj]
      simp only [lt_irrefl, true_and, false_or, r']
      by_cases hd : r.Deliv w h 0 <;> simp [hd]
    by_cases hwK : w ∈ Kn
    · rw [deliv_of_crash_some (hcK w hwK hw)]
      simp only [lt_irrefl, true_and, false_or, r', hwj, false_and, ite_false,
        Set.mem_empty_iff_false, iff_false]
      exact (hKd w hw).1 hwK
    · rw [iff_true_intro (deliv_of_crash_none (hcO w hw hwj hwK) h 0), iff_true]
      by_contra hd; exact hwK ((hKd w hw).2 hd)
  have hali' : r'.Alive i 1 := fun c hc => by rw [hci rfl] at hc; cases hc; omega
  -- in `r''`, `i` has seen `j`'s input `0`, so `i` decides `0` at time `1`
  have hd'' : DecidesAt Q r'' i 1 0 := by
    refine lemma14_part1 ht0 ht hQ hdom hr'' (by simp [r'', Ne.symm hji, hi0]) hali'
      ⟨j, hji, by simp [r''], seen_of_deliv hji ?_⟩
    rw [deliv_of_crash_some (show r''.crash j = some 1 from hcj)]; simp [r'']
  -- `k` cannot tell `r'` from `r''`: only `⟨j, 0⟩` and `⟨i, 1⟩` changed, and neither reaches `k`
  have hinv : ∀ {x : Run P}, x.crash = r'.crash → (∀ p, p ≠ j → x.reach p = ∅) →
      x.reach j ⊆ {i} → ∀ s, ¬ Seen x j 0 k s ∧ ¬ Seen x i 1 k s := by
    intro x hx hR hRj s
    have hcix : x.crash i = some 2 := hci hx
    have hcjx : x.crash j = some 1 := hx ▸ hcj
    set S : ℕ → P → Prop := fun τ a => a = j ∨ (a = i ∧ 1 ≤ τ)
    have hstep : ∀ τ a b, S τ a → comm x τ a b → S (τ + 1) b := by
      rintro τ a b (rfl | ⟨rfl, hτ⟩) ⟨hab, hd⟩
      · rw [deliv_of_crash_some hcjx] at hd
        rcases hd with h | ⟨h, hb⟩
        · omega
        · exact Or.inr ⟨hRj hb, by omega⟩
      · rw [deliv_of_crash_some hcix] at hd
        rcases hd with h | ⟨-, hb⟩
        · omega
        · rw [hR a hji.symm] at hb; exact absurd hb (Set.notMem_empty b)
    have hstay : ∀ τ a, S τ a → S (τ + 1) a := by
      rintro τ a (h | ⟨h, hτ⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h, by omega⟩
    have hk : ∀ τ, ¬ S τ k := by
      rintro τ (h | ⟨h, -⟩)
      · exact hjk h.symm
      · exact hki h
    exact ⟨not_seen_of_inv hstep hstay (Or.inl rfl) (hk s),
      not_seen_of_inv hstep hstay (Or.inr ⟨rfl, le_rfl⟩) (hk s)⟩
  have hR' : ∀ p, p ≠ j → r'.reach p = ∅ := fun p hp => by simp [r', hp]
  have hRj' : r'.reach j ⊆ {i} := by
    intro x hx; simp only [r'] at hx; split_ifs at hx
    · exact hx
    · exact absurd hx (Set.notMem_empty x)
  have hsvk : ∀ s, SameView r' r'' k s := by
    intro s
    have hns := hinv rfl hR' hRj' s
    refine sameView_of_agree (fun q hq => ?_) (fun h s' hs w hw => ?_)
    · have : q ≠ j := by rintro rfl; exact hns.1 hq
      simp [r'', r', this]
    · refine deliv_congr rfl fun hc => ?_
      by_cases hwj : w = j
      · subst hwj
        rw [hcj, Option.some.injEq] at hc
        obtain rfl : s' = 0 := by omega
        by_cases hd : r.Deliv w i 0
        · simp [r', r'', hd]
        · have hhi : h ≠ i := by rintro rfl; exact hns.2 hs
          simp [r', r'', hd, hhi]
      · simp [r', r'', hwj]
  -- `k` decides in `r'`; in `r''` it cannot decide `1`, so it decides `0` in both runs
  obtain ⟨mk, u, hu⟩ := hQ.decision r' hr' k hkc
  have hu'' : DecidesAt Q r'' k mk u :=
    ((hsvk mk).decidesAt_iff Q le_rfl ⟨fun _ => SyncCrash.Run.alive_of_not_faulty hkc'' _,
      fun _ => SyncCrash.Run.alive_of_not_faulty hkc _⟩).1 hu
  obtain rfl : u = 0 := uagree hQ hr'' hu'' hd''
  have hd1' : DecidesAt Q r' i m' 1 :=
    (hsv.decidesAt_iff Q hm' ⟨fun _ => hali'.mono hm', fun _ => hd1.1⟩).1 hd1
  exact zero_ne_one (uagree hQ hr' hu hd1')

end Forcing

end Podc.ParetoOptimalConsensus
