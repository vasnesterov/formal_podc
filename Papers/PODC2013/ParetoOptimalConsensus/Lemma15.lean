import Papers.PODC2013.ParetoOptimalConsensus.UniformForcing

/-!
# Lemma 15 (decisions at times later than 1, Appendix C)

Let `Q ⪰ U-P0` solve uniform consensus, `0 < t < n`, `m = M + 1 > 0`. Let `i` know `∃0` for the
first time at `m`, not know `∃correct(0)` at `m` (so `K_i ∃correct(0)` holds for the first time at
`m + 1`), and be alive at `m + 1`. Then `i` decides `0` at `m + 1` if

1. (Part 1) `F⟨i, m + 1⟩ < t`, some `z` with `K_z ∃0` at `m - 1` and `⟨z, m - 1⟩` seen by `⟨i, m⟩`
   has `⟨z, m⟩` not seen by `⟨i, m + 1⟩`, and some `j ≠ i` with `⟨j, m⟩` seen by `⟨i, m + 1⟩` has
   seen `⟨z, m - 1⟩`; or
2. (Part 2) `F⟨i, m + 1⟩ < t - 1`.

## Proof structure (repairing the paper's proof)

The paper proves both parts together, by induction on `m` and an inner induction on
`|C_i \ Z_i|` (Cases I and II), with a counting argument for Part 1. We follow its constructions
but organise the inner induction differently (`ic`): by induction on `n - |Z_i|`, where
`Z_i = {k | ⟨k, m⟩ seen by ⟨i, m + 1⟩ and ⟨z, m - 1⟩ seen by ⟨k, m⟩}`.

* (`ic_caseC`) If `⟨z, m⟩` is hidden from `⟨i, m + 1⟩`, a run indistinguishable to `i` lets `z`
  live through round `m`, hearing from everybody `i` heard from; then `z` satisfies Part 2 one
  level lower, so it decides `0` (outer induction), and so does `i`.
* (`ic_caseII`) Otherwise some `k` seen by `⟨i, m + 1⟩` missed `z`'s round-`m` message. The paper's
  Case II followed by its Case I gives two runs `x ~_i x' ~_j x''`: in `x'`, `k` crashes in round
  `m + 1` reaching only `i`; in `x''`, `k` also receives `z`'s message. In `x''` the set `Z_i` has
  grown by `k`, so `i` decides `0` (inner induction); hence `j` decides `0` in `x''`, hence in `x'`,
  hence `i` decides `0` in `x`.

The paper's measure `|C_i \ Z_i|` need not decrease in Case II (`C_j` may be larger than `C_i`),
and its counting argument for Part 1 is not needed: the number of known failures never exceeds
`F⟨i, m + 1⟩ + 1 ≤ t` in these runs. Part 2 additionally uses the paper's "`Z_i = {i}`" argument
(`g15_succ`, with the closure lemma `not_seen_of_inv` for the process `k` that never hears of the
modification), and the case where `z` itself reaches `⟨i, m + 1⟩`, which the paper treats inside its
base case.
-/

namespace Podc.ParetoOptimalConsensus

open Cslib Finset Podc.UnbeatableSetConsensus

variable {P : Type*} [Fintype P] {t : ℕ}

/-! ### Helpers -/

omit [Fintype P] in
-- CSLib candidate: Cslib/Computability/Distributed/SyncCrash (full-information views)
/-- The nodes seen one round later: oneself or a direct message. -/
lemma seen_succ_self_iff {r : Run P} {q p : P} {s : ℕ} :
    Seen r q s p (s + 1) ↔ q = p ∨ (q ≠ p ∧ r.Deliv q p s) := by
  rw [seen_succ_iff le_rfl]
  constructor
  · rintro (h | ⟨x, hx, h⟩)
    · exact Or.inl (seen_same_time h)
    · obtain rfl := seen_same_time h; exact Or.inr hx
  · rintro (rfl | h)
    · exact Or.inl (seen_self le_rfl)
    · exact Or.inr ⟨q, h, seen_self le_rfl⟩

omit [Fintype P] in
-- CSLib candidate: Cslib/Computability/Distributed/SyncCrash (full-information views)
/-- Same view at `L + 1` from agreement on the first `L` rounds and on round `L + 1` into `i`. -/
lemma sameView_succ_of {x x' : Run P} {i : P} {L : ℕ} (hI : ∀ q, x.input q = x'.input q)
    (hlt : ∀ s < L, ∀ w q, x.Deliv w q s ↔ x'.Deliv w q s)
    (hlast : ∀ w, w ≠ i → (x.Deliv w i L ↔ x'.Deliv w i L)) : SameView x x' i (L + 1) := by
  refine sameView_of_agree (fun q _ => hI q) (fun h s hs w hw => ?_)
  rcases Nat.lt_or_ge s L with hsL | hsL
  · exact hlt s hsL w h
  · obtain rfl : s = L := by have := hs.le; omega
    obtain rfl := seen_same_time hs
    exact hlast w hw

open Classical in
/-- The processes that `i` heard from in round `s + 1`, the known failures and `i` itself cover
all processes. -/
lemma card_senders {x : Run P} {i : P} {s : ℕ} (hal : x.Alive i (s + 1)) :
    (univ.filter fun q => q ≠ i ∧ x.Deliv q i s).card + known x i (s + 1) + 1 =
      Fintype.card P := by
  classical
  have hK : ∀ q, q ∈ knownSet x i (s + 1) ↔ q ≠ i ∧ ¬ x.Deliv q i s := fun q => by
    rw [mem_knownSet, guarCrashed_now_iff (by simpa using hal) (Nat.succ_pos s)]; simp
  rw [known_eq_card]
  have hu : (univ.filter fun q => q ≠ i ∧ x.Deliv q i s) ∪ knownSet x i (s + 1) = univ.erase i := by
    ext q; simp only [mem_union, mem_filter, mem_univ, true_and, hK, mem_erase, and_true]
    tauto
  have hd : Disjoint (univ.filter fun q => q ≠ i ∧ x.Deliv q i s) (knownSet x i (s + 1)) := by
    rw [disjoint_left]; intro q h1 h2
    exact (hK q).1 h2 |>.2 (mem_filter.1 h1).2.2
  rw [← card_union_of_disjoint hd, hu, card_erase_of_mem (mem_univ i), card_univ]
  have : 0 < Fintype.card P := Fintype.card_pos_iff.2 ⟨i⟩
  omega

/-- A node `⟨z, M⟩` that reached `⟨i, M + 1⟩`, but not `⟨i, M + 2⟩`, is a newly known failure. -/
lemma known_succ_lt {x : Run P} {i z : P} {M : ℕ} (_hal : x.Alive i (M + 2)) (hzi : z ≠ i)
    (hz1 : x.Deliv z i M) (hz2 : ¬ x.Deliv z i (M + 1)) :
    known x i (M + 1) + 1 ≤ known x i (M + 2) := by
  classical
  rw [known_eq_card, known_eq_card]
  have hsub : insert z (knownSet x i (M + 1)) ⊆ knownSet x i (M + 2) := by
    intro p hp
    rcases mem_insert.1 hp with rfl | hp
    · exact mem_knownSet.2 ⟨i, M + 1, Nat.lt_succ_self _, seen_self le_rfl, hzi.symm, hz2⟩
    · exact knownSet_mono_seen (seen_self (Nat.le_succ _)) hp
  have hz : z ∉ knownSet x i (M + 1) := fun h =>
    not_guarCrashed_of_seen_pred hz1.1 (seen_of_deliv hzi hz1) (mem_knownSet.1 h)
  have := card_le_card hsub
  rwa [card_insert_of_notMem hz] at this

/-! ### The induction -/

section Lemma15

variable {Q : Protocol P} (ht : t < Fintype.card P) (hQ : SolvesUniformSetConsensus 1 t bin Q)
  (hdom : Dominates t bin Q (uP0 t))

/-- Part 2 of Lemma 15 at level `s` (for `s = 0` this is Lemma 14, Part 2). -/
def G15 (t : ℕ) (Q : Protocol P) (s : ℕ) : Prop :=
  ∀ x : Run P, Adm t bin x → ∀ i, x.Alive i (s + 1) → FirstKnows x i s 0 →
    ¬ KCorrect t x i s 0 → known x i (s + 1) + 2 ≤ t → DecidesAt Q x i (s + 1) 0

include ht hQ hdom in
lemma g15_zero : G15 t Q 0 := by
  intro x hx i hal hf _ hkn
  have hi0 : x.input i = 0 := by
    have := hf.1; rw [vals_zero, mem_singleton] at this; exact this.symm
  simp only [zero_add] at hkn
  exact lemma14_part2 (by omega) ht hQ hdom (by omega) hx hi0 hal (by omega)

include ht hQ hdom in
/-- A process that knew `∃0` at `M`, alive at `M + 1`, whose node `⟨q, M⟩` is seen by a node
`⟨i, M + 1⟩` without `K_i ∃correct(0)`, and that knows of at most `t - 2` failures at `M + 1`,
decides `0` (by the induction hypothesis at its first-knowledge time). -/
lemma subG {M : ℕ} (hG : ∀ s ≤ M, G15 t Q s) {x : Run P} (hx : Adm t bin x) {i q : P}
    (hq0 : 0 ∈ vals x q M) (hqa : x.Alive q (M + 1)) (hqs : Seen x q M i (M + 1))
    (hnk : ¬ KCorrect t x i (M + 1) 0) (hkn : known x q (M + 1) + 2 ≤ t) :
    ∃ s, DecidesAt Q x q s 0 := by
  obtain ⟨s, hs, hf⟩ := exists_firstKnows hq0
  refine ⟨s + 1, hG s hs x hx q (hqa.mono (by omega)) hf (fun hk => hnk ?_) ?_⟩
  · exact hk.of_seen (hqs.mono_left hs)
  · have := known_mono (r := x) (i := q) (show s + 1 ≤ M + 1 by omega); omega

include ht hQ hdom in
/-- The forcing principle at `M + 2`. -/
lemma force_at {M : ℕ} {x : Run P} (hx : Adm t bin x) {i : P} (hal : x.Alive i (M + 2))
    (hf : 0 ∈ vals x i (M + 1)) (hnk : ¬ KCorrect t x i (M + 1) 0) {x' : Run P}
    (hx' : Adm t bin x') (hsv : SameView x x' i (M + 2)) (hal' : x'.Alive i (M + 2)) {q : P}
    {s : ℕ} (hq : DecidesAt Q x' q s 0) : DecidesAt Q x i (M + 2) 0 :=
  decides0_of_witness ht hQ hdom hx hal (kCorrect_of_prev ht hx hal hf)
    (fun s' hs' hk => hnk (hk.mono (by omega))) hx' hsv hal' hq

open Classical in
/-- `Z_i`: the processes `k` with `⟨k, M + 1⟩` seen by `⟨i, M + 2⟩` that have seen `⟨z, M⟩`. -/
noncomputable def zset (x : Run P) (i z : P) (M : ℕ) : Finset P :=
  univ.filter fun q => Seen x q (M + 1) i (M + 2) ∧ Seen x z M q (M + 1)

lemma mem_zset {x : Run P} {i z q : P} {M : ℕ} :
    q ∈ zset x i z M ↔ Seen x q (M + 1) i (M + 2) ∧ Seen x z M q (M + 1) := by
  classical simp [zset]

/-- The hypotheses of the inner induction (Part 1 of Lemma 15). -/
structure ICHyp (t : ℕ) (x : Run P) (i z j : P) (M : ℕ) : Prop where
  adm : Adm t bin x
  alive : x.Alive i (M + 2)
  first : FirstKnows x i (M + 1) 0
  nkc : ¬ KCorrect t x i (M + 1) 0
  z0 : 0 ∈ vals x z M
  zi : z ≠ i
  zdi : x.Deliv z i M
  zndi : ¬ x.Deliv z i (M + 1)
  ji : j ≠ i
  jdi : x.Deliv j i (M + 1)
  zdj : x.Deliv z j M
  known_lt : known x i (M + 2) < t

include ht hQ hdom in
/-- **Case C** of the inner induction: `⟨z, M + 1⟩` is hidden from `⟨i, M + 2⟩`. Then a run in which
`z` stays alive through round `M + 1`, hearing from everybody `i` heard from, is indistinguishable
to `i`; there `z` decides `0` by the outer induction hypothesis. -/
lemma ic_caseC {M : ℕ} (hG : ∀ s ≤ M, G15 t Q s) {x : Run P} {i z j : P}
    (H : ICHyp t x i z j M) (hhid : ¬ GuarCrashed x i (M + 2) z (M + 1)) :
    DecidesAt Q x i (M + 2) 0 := by
  classical
  have hza : x.Alive z M := H.zdi.1
  have hzf : x.Faulty z := faulty_of_not_deliv' H.zndi
  set x' : Run P :=
    { input := x.input
      crash := fun p => if p = z then some (M + 2) else x.crash p
      reach := fun p => if p = z then ∅
        else if x.crash p = some (M + 1) ∧ i ∈ x.reach p then insert z (x.reach p) else x.reach p }
  have hcz : x'.crash z = some (M + 2) := by simp [x']
  have hcO : ∀ p, p ≠ z → x'.crash p = x.crash p := fun p hp => by simp [x', hp]
  have hx' : Adm t bin x' := by
    refine ⟨⟨le_trans (card_le_card fun p hp => ?_) H.adm.1.1, fun p c hc => ?_⟩, H.adm.2⟩
    · rw [SyncCrash.Run.mem_faulty] at hp ⊢
      by_cases hpz : p = z
      · exact hpz ▸ hzf
      · unfold SyncCrash.Run.Faulty at hp ⊢; rwa [hcO p hpz] at hp
    · by_cases hpz : p = z
      · rw [hpz, hcz] at hc; cases hc; omega
      · rw [hcO p hpz] at hc; exact H.adm.1.2 p c hc
  have hnsz : ¬ Seen x z (M + 1) i (M + 2) := by
    rw [seen_succ_self_iff]; rintro (h | ⟨-, h⟩)
    · exact H.zi h
    · exact H.zndi h
  have hsv : SameView x x' i (M + 2) := by
    refine sameView_of_agree (fun _ _ => rfl) (fun h s hs w hw => ?_)
    have hsle := hs.le
    by_cases hwz : w = z
    · subst hwz
      rw [deliv_of_crash_some hcz]
      simp only [x', ite_true, Set.mem_empty_iff_false, and_false, or_false]
      rcases Nat.lt_trichotomy s M with hlt | rfl | hgt
      · exact iff_of_true (deliv_of_alive_succ (hza.mono (by omega)) h) (by omega)
      · refine iff_of_true ?_ (by omega)
        by_contra hnd
        exact hhid ⟨h, s, Nat.lt_succ_self _, hs, hw.symm, hnd⟩
      · obtain rfl : s = M + 1 := by omega
        obtain rfl := seen_same_time hs
        exact iff_of_false H.zndi (by omega)
    · refine deliv_congr (hcO w hwz).symm fun hc => ?_
      simp only [x', hwz, ite_false]
      split_ifs with h1
      · rw [Set.mem_insert_iff]
        have : h ≠ z := by
          rintro rfl
          rw [h1.1, Option.some.injEq] at hc
          obtain rfl : s = M := by omega
          exact hnsz hs
        simp [this]
      · rfl
  have hal' : x'.Alive i (M + 2) := fun c hc => H.alive c (by rwa [hcO i H.zi.symm] at hc)
  have hzs : Seen x z M i (M + 1) := seen_of_deliv H.zi H.zdi
  have hsvz : SameView x x' z M := hsv.of_seen (hzs.mono_right (Nat.le_succ _))
  -- `z` knows of no more failures at `M + 1` than `i` did
  have hkn : known x' z (M + 1) + 2 ≤ t := by
    have hza' : x'.Alive z (M + 1) := (alive_of_crash_some hcz).2 (by omega)
    have hsub : knownSet x' z (M + 1) ⊆ knownSet x i (M + 1) := by
      intro p hp
      rw [mem_knownSet, guarCrashed_now_iff (by simpa using hza') (Nat.succ_pos M)] at hp
      try simp only [Nat.add_sub_cancel] at hp
      obtain ⟨hpz, hnd⟩ := hp
      have hpi : p ≠ i := by
        rintro rfl; exact hnd (deliv_of_alive_succ (hal'.mono (by omega)) z)
      rw [mem_knownSet, guarCrashed_now_iff (by simpa using H.alive.mono (by omega))
        (Nat.succ_pos M)]
      try simp only [Nat.add_sub_cancel]
      refine ⟨hpi, fun hd => hnd ?_⟩
      cases hcp : x.crash p with
      | none => exact deliv_of_crash_none ((hcO p hpz).trans hcp) z M
      | some c =>
        rw [deliv_of_crash_some ((hcO p hpz).trans hcp)]
        rw [deliv_of_crash_some hcp] at hd
        rcases hd with hlt | ⟨rfl, hir⟩
        · exact Or.inl hlt
        · refine Or.inr ⟨rfl, ?_⟩
          simp [x', hpz, hcp, hir]
    have h1 := card_le_card hsub
    rw [← known_eq_card, ← known_eq_card] at h1
    have := known_succ_lt H.alive H.zi H.zdi H.zndi
    have := H.known_lt
    omega
  obtain ⟨s, hdz⟩ := subG ht hQ hdom hG hx' (q := z) (i := i) (hsvz.vals_eq ▸ H.z0)
    ((alive_of_crash_some hcz).2 (by omega)) ((hsv.mono (Nat.le_succ _)).seen hzs)
    (fun hk => H.nkc ((kCorrect_iff_of_sameView (hsv.mono (Nat.le_succ _))).2 hk)) hkn
  exact force_at ht hQ hdom H.adm H.alive H.first.1 H.nkc hx' hsv hal' hdz

include ht hQ hdom in
/-- **Case II** of the inner induction: some `k` heard by `⟨i, M + 2⟩` missed `z`'s round-`M + 1`
message. Runs `x ~_i x' ~_j x''`: in `x'`, `k` crashes in round `M + 2` reaching only `i` (all
processes not known by `⟨i, M + 2⟩` to have crashed, other than `k`, are correct); `x''` is `x'`
where `k` also receives `z`'s round-`M + 1` message. -/
lemma ic_caseII {M N : ℕ}
    (ih : ∀ (x : Run P) (i z j : P), ICHyp t x i z j M →
      Fintype.card P - (zset x i z M).card < N → DecidesAt Q x i (M + 2) 0)
    {x : Run P} {i z j : P} (H : ICHyp t x i z j M) (hN : Fintype.card P - (zset x i z M).card = N)
    {k : P} (hki : k ≠ i) (hkd : x.Deliv k i (M + 1)) (hzk : ¬ x.Deliv z k M) :
    DecidesAt Q x i (M + 2) 0 := by
  classical
  have hkj : k ≠ j := by rintro rfl; exact hzk H.zdj
  have hzkne : z ≠ k := by rintro rfl; exact H.zndi hkd
  have hzj : z ≠ j := by rintro rfl; exact H.zndi H.jdi
  have hcz : x.crash z = some (M + 1) := by
    have h1 := H.zdi; have h2 := hzk
    rw [deliv_iff] at h1 h2
    by_contra hc; exact h2 ⟨h1.1, fun h => hc h.1⟩
  have hKn : ∀ p, p ∈ knownSet x i (M + 2) ↔ p ≠ i ∧ ¬ x.Deliv p i (M + 1) := fun p => by
    rw [mem_knownSet, guarCrashed_now_iff (by simpa using H.alive) (Nat.succ_pos _)]; simp
  set Kn := knownSet x i (M + 2)
  have hzK : z ∈ Kn := (hKn z).2 ⟨H.zi, H.zndi⟩
  have hkK : k ∉ Kn := fun h => ((hKn k).1 h).2 hkd
  have hjK : j ∉ Kn := fun h => ((hKn j).1 h).2 H.jdi
  have hiK : i ∉ Kn := fun h => ((hKn i).1 h).1 rfl
  set x' : Run P :=
    { input := x.input
      crash := fun p => if p = k then some (M + 2) else if p ∈ Kn then x.crash p else none
      reach := fun p => if p = k then {i} else x.reach p }
  have hck : x'.crash k = some (M + 2) := by simp [x']
  have hcK : ∀ p ∈ Kn, x'.crash p = x.crash p := fun p hp => by
    simp [x', hp, show p ≠ k from fun h => hkK (h ▸ hp)]
  have hcO : ∀ p, p ≠ k → p ∉ Kn → x'.crash p = none := fun p h1 h2 => by simp [x', h1, h2]
  have hrO : ∀ p, p ≠ k → x'.reach p = x.reach p := fun p h => by simp [x', h]
  have hx' : Adm t bin x' := by
    refine ⟨⟨?_, fun p c hc => ?_⟩, H.adm.2⟩
    · have hsub : x'.faulty ⊆ insert k Kn := by
        intro p hp
        rw [SyncCrash.Run.mem_faulty, SyncCrash.Run.Faulty] at hp
        rw [mem_insert]; by_contra h; push Not at h; exact hp (hcO p h.1 h.2)
      refine (card_le_card hsub).trans ((card_insert_le _ _).trans ?_)
      rw [← known_eq_card]; have := H.known_lt; omega
    · by_cases hpk : p = k
      · rw [hpk, hck] at hc; cases hc; omega
      by_cases hpK : p ∈ Kn
      · rw [hcK p hpK] at hc; exact H.adm.1.2 p c hc
      · rw [hcO p hpk hpK] at hc; cases hc
  -- rounds `≤ M + 1` are unchanged; in round `M + 2`, `i` hears from the same processes
  have hlt : ∀ s < M + 1, ∀ w q, x.Deliv w q s ↔ x'.Deliv w q s := by
    intro s hs w q
    by_cases hwk : w = k
    · subst hwk
      rw [deliv_of_crash_some hck]
      exact iff_of_true (deliv_of_alive_succ (hkd.1.mono (by omega)) q) (Or.inl (by omega))
    by_cases hwK : w ∈ Kn
    · exact deliv_congr (hcK w hwK).symm fun _ => by rw [hrO w hwk]
    · rw [iff_true_intro (deliv_of_crash_none (hcO w hwk hwK) q s), iff_true]
      have hwa : x.Alive w (M + 1) := by
        by_cases hwi : w = i
        · rw [hwi]; exact H.alive.mono (by omega)
        · exact (not_not.1 fun h => hwK ((hKn w).2 ⟨hwi, h⟩)).1
      exact deliv_of_alive_succ (hwa.mono (by omega)) q
  have hlast : ∀ w, w ≠ i → (x.Deliv w i (M + 1) ↔ x'.Deliv w i (M + 1)) := by
    intro w hwi
    by_cases hwk : w = k
    · subst hwk
      rw [deliv_of_crash_some hck]
      exact iff_of_true hkd (Or.inr ⟨rfl, by simp [x']⟩)
    by_cases hwK : w ∈ Kn
    · exact deliv_congr (hcK w hwK).symm fun _ => by rw [hrO w hwk]
    · rw [iff_true_intro (deliv_of_crash_none (hcO w hwk hwK) i _), iff_true]
      exact not_not.1 fun h => hwK ((hKn w).2 ⟨hwi, h⟩)
  have hsv : SameView x x' i (M + 2) := sameView_succ_of (fun _ => rfl) hlt hlast
  have hic : ¬ x'.Faulty i := by rw [not_faulty_iff]; exact hcO i (Ne.symm hki) hiK
  have hjc : ¬ x'.Faulty j := by rw [not_faulty_iff]; exact hcO j (Ne.symm hkj) hjK
  have hnks : ¬ Seen x' k (M + 1) j (M + 2) := by
    rw [seen_succ_self_iff]; rintro (h | ⟨-, h⟩)
    · exact hkj h
    · rw [deliv_of_crash_some hck] at h
      rcases h with h | ⟨-, h⟩
      · omega
      · simp only [x', ite_true, Set.mem_singleton_iff] at h; exact H.ji h
  -- `x''`: `k` also gets `z`'s message
  set x'' : Run P :=
    { input := x.input
      crash := x'.crash
      reach := fun p => if p = z then insert k (x.reach p) else x'.reach p }
  have hcz' : x'.crash z = some (M + 1) := (hcK z hzK).trans hcz
  have hd'' : ∀ w h s, (w ≠ z ∨ h ≠ k ∨ s ≠ M) → (x''.Deliv w h s ↔ x'.Deliv w h s) := by
    intro w h s hc
    refine deliv_congr rfl fun hcs => ?_
    by_cases hwz : w = z
    · subst hwz
      rw [hcz', Option.some.injEq] at hcs
      have hhk : h ≠ k := by
        rcases hc with hc | hc | hc
        · exact absurd rfl hc
        · exact hc
        · omega
      simp [x'', x', hzkne, hhk]
    · simp [x'', hwz]
  have hdz'' : x''.Deliv z k M := by
    rw [deliv_of_crash_some (show x''.crash z = some (M + 1) from hcz')]
    exact Or.inr ⟨rfl, by simp [x'']⟩
  have hx'' : Adm t bin x'' := ⟨⟨hx'.1.1, hx'.1.2⟩, H.adm.2⟩
  have hsvj : SameView x' x'' j (M + 2) := by
    refine sameView_of_agree (fun _ _ => rfl) (fun h s hs w _ => (hd'' w h s ?_).symm)
    by_contra hc; push Not at hc; obtain ⟨rfl, rfl, rfl⟩ := hc; exact hnks hs
  have hsvi : SameView x x'' i (M + 1) := by
    refine (hsv.mono (Nat.le_succ _)).trans (sameView_of_agree (fun _ _ => rfl)
      (fun h s hs w _ => (hd'' w h s ?_).symm))
    by_contra hc; push Not at hc; obtain ⟨rfl, rfl, rfl⟩ := hc
    exact hki (seen_same_time hs)
  have hdl : ∀ w q s, s < M + 1 → (w ≠ z ∨ q ≠ k ∨ s ≠ M) → (x''.Deliv w q s ↔ x.Deliv w q s) :=
    fun w q s hs hc => (hd'' w q s hc).trans (hlt s hs w q).symm
  have hdl' : ∀ w, w ≠ i → (x''.Deliv w i (M + 1) ↔ x.Deliv w i (M + 1)) :=
    fun w hw => (hd'' w i (M + 1) (Or.inr (Or.inr (by omega)))).trans (hlast w hw).symm
  have hjc'' : ¬ x''.Faulty j := hjc
  have hic'' : ¬ x''.Faulty i := hic
  -- the hypotheses of the inner induction hold for `i` in `x''`, with a larger `Z_i`
  have H'' : ICHyp t x'' i z j M := by
    refine ⟨hx'', SyncCrash.Run.alive_of_not_faulty hic'' _,
      (SameView.firstKnows_iff hsvi).1 H.first,
      fun hk => H.nkc ((kCorrect_iff_of_sameView hsvi).2 hk), ?_, H.zi,
      (hdl z i M (by omega) (Or.inr (Or.inl hki.symm))).2 H.zdi, ?_, H.ji,
      SyncCrash.Run.deliv_of_not_faulty hjc'' i _,
      (hdl z j M (by omega) (Or.inr (Or.inl (Ne.symm hkj)))).2 H.zdj, ?_⟩
    · have := (hsvi.of_seen (seen_of_deliv H.zi H.zdi)).vals_eq
      rw [← this]; exact H.z0
    · intro h; have := h.1 (M + 1) hcz'; omega
    · have hal'' : x''.Alive i (M + 2 + 1 - 1) := SyncCrash.Run.alive_of_not_faulty hic'' _
      have : knownSet x'' i (M + 2) = Kn := by
        ext p
        rw [mem_knownSet, guarCrashed_now_iff hal'' (Nat.succ_pos _), hKn]
        try simp only [Nat.add_sub_cancel]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ((hdl' p h1).2 h)⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ((hdl' p h1).1 h)⟩
      rw [known_eq_card, this, ← known_eq_card]; exact H.known_lt
  have hsub : insert k (zset x i z M) ⊆ zset x'' i z M := by
    intro q hq
    rw [mem_zset]
    rcases mem_insert.1 hq with rfl | hq
    · refine ⟨?_, ?_⟩
      · rw [seen_succ_self_iff]
        exact Or.inr ⟨hki, (hd'' q i (M + 1) (Or.inr (Or.inr (by omega)))).2
          ((hlast q hki).1 hkd)⟩
      · rw [seen_succ_self_iff]; exact Or.inr ⟨hzkne, hdz''⟩
    · obtain ⟨h1, h2⟩ := mem_zset.1 hq
      rw [seen_succ_self_iff] at h1 h2 ⊢
      rw [seen_succ_self_iff]
      refine ⟨?_, ?_⟩
      · rcases h1 with rfl | ⟨hqi, hqd⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hqi, (hdl' q hqi).2 hqd⟩
      · rcases h2 with rfl | ⟨hzq, hzd⟩
        · exact Or.inl rfl
        · have hqk : q ≠ k := by rintro rfl; exact hzk hzd
          exact Or.inr ⟨hzq, (hdl z q M (by omega) (Or.inr (Or.inl hqk))).2 hzd⟩
  have hkZ : k ∉ zset x i z M := by
    intro h
    have h2 := (mem_zset.1 h).2
    rw [seen_succ_self_iff] at h2
    rcases h2 with h | ⟨-, h⟩
    · exact hzkne h
    · exact hzk h
  have hlt' : Fintype.card P - (zset x'' i z M).card < N := by
    have h1 := card_le_card hsub
    rw [card_insert_of_notMem hkZ] at h1
    have h2 := card_le_univ (zset x'' i z M)
    omega
  have hdi'' := ih x'' i z j H'' hlt'
  -- hence `j` decides `0` in `x''`, hence in `x'`, hence `i` decides `0` in `x`
  have hkcj : KCorrect t x'' j (M + 2) 0 := kCorrect_of_prev ht hx''
    (SyncCrash.Run.alive_of_not_faulty hjc'' _)
    (vals_subset_succ_of_comm ⟨hzj, (hdl z j M (by omega) (Or.inr (Or.inl (Ne.symm hkj)))).2 H.zdj⟩
      H''.z0)
  obtain ⟨mj, hmj, u, hu⟩ := decidesBy_of_kc hdom hx'' (SyncCrash.Run.alive_of_not_faulty hjc'' _)
    hkcj
  obtain rfl : u = 0 := uagree hQ hx'' hu hdi''
  have hu' : DecidesAt Q x' j mj 0 :=
    (hsvj.decidesAt_iff Q hmj ⟨fun _ => SyncCrash.Run.alive_of_not_faulty hjc'' _,
      fun _ => SyncCrash.Run.alive_of_not_faulty hjc _⟩).2 hu
  exact force_at ht hQ hdom H.adm H.alive H.first.1 H.nkc hx' hsv
    (SyncCrash.Run.alive_of_not_faulty hic _) hu'

include ht hQ hdom in
/-- **Inner induction** (Part 1 of Lemma 15 at level `M + 1`), by induction on `n - |Z_i|`. -/
lemma ic {M : ℕ} (hG : ∀ s ≤ M, G15 t Q s) : ∀ (N : ℕ) (x : Run P) (i z j : P),
    ICHyp t x i z j M → Fintype.card P - (zset x i z M).card = N →
    DecidesAt Q x i (M + 2) 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
  intro x i z j H hN
  by_cases hg : GuarCrashed x i (M + 2) z (M + 1)
  · obtain ⟨h, s, hs, hseen, hne, hnd⟩ := hg
    obtain rfl : s = M := by
      by_contra hsM
      exact hnd (deliv_of_alive_succ (H.zdi.1.mono (by omega)) h)
    have hhi : h ≠ i := by rintro rfl; exact hnd H.zdi
    rw [seen_succ_self_iff] at hseen
    rcases hseen with h' | ⟨-, hhd⟩
    · exact absurd h' hhi
    exact ic_caseII ht hQ hdom (fun x i z j H hlt => ihN _ (hN ▸ hlt) x i z j H rfl) H hN hhi hhd hnd
  · exact ic_caseC ht hQ hdom hG H hg

include ht hQ hdom in
/-- **Part 2 at level `M + 1`**, from Part 2 at the levels `≤ M`. -/
lemma g15_succ {M : ℕ} (hG : ∀ s ≤ M, G15 t Q s) : G15 t Q (M + 1) := by
  classical
  intro x hx i hal hf hnk hkn
  replace hkn : known x i (M + 2) + 2 ≤ t := hkn
  obtain hv | ⟨z, hz, hz0⟩ := mem_vals_succ.1 hf.1
  · exact absurd hv (hf.2 M rfl)
  have hzi : z ≠ i := hz.1
  have hzd : x.Deliv z i M := hz.2
  -- `z` reached `⟨i, M + 2⟩`: it decides `0` by the outer induction
  by_cases hz1 : x.Deliv z i (M + 1)
  · obtain ⟨s, hds⟩ := subG ht hQ hdom hG hx hz0 hz1.1 (seen_of_deliv hzi hzd) hnk
      (by have : known x z (M + 1) ≤ known x i (M + 2) := known_mono_seen (seen_of_deliv hzi hz1)
          omega)
    exact force_at ht hQ hdom hx hal hf.1 hnk hx (sameView_refl x i _) hal hds
  -- some `j` heard by `⟨i, M + 2⟩` received `z`'s message: the inner induction
  by_cases hj : ∃ j, j ≠ i ∧ x.Deliv j i (M + 1) ∧ x.Deliv z j M
  · obtain ⟨j, hji, hjd, hzj⟩ := hj
    exact ic ht hQ hdom hG _ x i z j ⟨hx, hal, hf, hnk, hz0, hzi, hzd, hz1, hji, hjd, hzj,
      by omega⟩ rfl
  push Not at hj
  -- otherwise (`Z_i = {i}`): two processes `j ≠ k` heard by `⟨i, M + 2⟩`
  have hT : 1 < (univ.filter fun q => q ≠ i ∧ x.Deliv q i (M + 1)).card := by
    have h1 : _ + known x i (M + 2) + 1 = _ := card_senders (x := x) (i := i) (s := M + 1) hal
    omega
  set T := univ.filter fun q => q ≠ i ∧ x.Deliv q i (M + 1)
  obtain ⟨j, hjT, k, hkT, hjk⟩ := one_lt_card.1 hT
  simp only [T, mem_filter, mem_univ, true_and] at hjT hkT
  obtain ⟨hji, hjd⟩ := hjT
  obtain ⟨hki, hkd⟩ := hkT
  have hzj : ¬ x.Deliv z j M := hj j hji hjd
  have hcz : x.crash z = some (M + 1) := by
    have h1 := hzd; have h2 := hzj
    rw [deliv_iff] at h1 h2
    by_contra hc; exact h2 ⟨h1.1, fun h => hc h.1⟩
  have hKn : ∀ p, p ∈ knownSet x i (M + 2) ↔ p ≠ i ∧ ¬ x.Deliv p i (M + 1) := fun p => by
    rw [mem_knownSet, guarCrashed_now_iff (by simpa using hal) (Nat.succ_pos _)]; simp
  set Kn := knownSet x i (M + 2)
  have hzK : z ∈ Kn := (hKn z).2 ⟨hzi, hz1⟩
  have hjK : j ∉ Kn := fun h => ((hKn j).1 h).2 hjd
  have hkK : k ∉ Kn := fun h => ((hKn k).1 h).2 hkd
  have hiK : i ∉ Kn := fun h => ((hKn i).1 h).1 rfl
  have hzjne : z ≠ j := fun h => hjK (h ▸ hzK)
  -- `x'`: `j` crashes in round `M + 2` reaching only `i`, `i` crashes in round `M + 3` silently,
  -- all processes not known to have crashed are otherwise correct
  set x' : Run P :=
    { input := x.input
      crash := fun p => if p = i then some (M + 3) else if p = j then some (M + 2)
        else if p ∈ Kn then x.crash p else none
      reach := fun p => if p = i then ∅ else if p = j then {i} else x.reach p }
  have hci : x'.crash i = some (M + 3) := by simp [x']
  have hcj : x'.crash j = some (M + 2) := by simp [x', hji]
  have hcK : ∀ p ∈ Kn, x'.crash p = x.crash p := fun p hp => by
    simp [x', hp, show p ≠ i from fun h => hiK (h ▸ hp), show p ≠ j from fun h => hjK (h ▸ hp)]
  have hcO : ∀ p, p ≠ i → p ≠ j → p ∉ Kn → x'.crash p = none := fun p h1 h2 h3 => by
    simp [x', h1, h2, h3]
  have hrK : ∀ p ∈ Kn, x'.reach p = x.reach p := fun p hp => by
    simp [x', show p ≠ i from fun h => hiK (h ▸ hp), show p ≠ j from fun h => hjK (h ▸ hp)]
  have hx' : Adm t bin x' := by
    refine ⟨⟨?_, fun p c hc => ?_⟩, hx.2⟩
    · have hsub : x'.faulty ⊆ insert i (insert j Kn) := by
        intro p hp
        rw [SyncCrash.Run.mem_faulty, SyncCrash.Run.Faulty] at hp
        simp only [mem_insert]; by_contra h; push Not at h; exact hp (hcO p h.1 h.2.1 h.2.2)
      refine (card_le_card hsub).trans ((card_insert_le _ _).trans ?_)
      have := card_insert_le j Kn
      rw [← known_eq_card] at this; omega
    · by_cases hpi : p = i
      · rw [hpi, hci] at hc; cases hc; omega
      by_cases hpj : p = j
      · rw [hpj, hcj] at hc; cases hc; omega
      by_cases hpK : p ∈ Kn
      · rw [hcK p hpK] at hc; exact hx.1.2 p c hc
      · rw [hcO p hpi hpj hpK] at hc; cases hc
  have hlt : ∀ s < M + 1, ∀ w q, x.Deliv w q s ↔ x'.Deliv w q s := by
    intro s hs w q
    by_cases hwi : w = i
    · subst hwi
      rw [deliv_of_crash_some hci]
      exact iff_of_true (deliv_of_alive_succ (hal.mono (by omega)) q) (Or.inl (by omega))
    by_cases hwj : w = j
    · subst hwj
      rw [deliv_of_crash_some hcj]
      exact iff_of_true (deliv_of_alive_succ (hjd.1.mono (by omega)) q) (Or.inl (by omega))
    by_cases hwK : w ∈ Kn
    · exact deliv_congr (hcK w hwK).symm fun _ => by rw [hrK w hwK]
    · rw [iff_true_intro (deliv_of_crash_none (hcO w hwi hwj hwK) q s), iff_true]
      have hwa : x.Alive w (M + 1) := (not_not.1 fun h => hwK ((hKn w).2 ⟨hwi, h⟩)).1
      exact deliv_of_alive_succ (hwa.mono (by omega)) q
  have hlast : ∀ w, w ≠ i → (x.Deliv w i (M + 1) ↔ x'.Deliv w i (M + 1)) := by
    intro w hwi
    by_cases hwj : w = j
    · subst hwj
      rw [deliv_of_crash_some hcj]
      exact iff_of_true hjd (Or.inr ⟨rfl, by simp [x', hwi]⟩)
    by_cases hwK : w ∈ Kn
    · exact deliv_congr (hcK w hwK).symm fun _ => by rw [hrK w hwK]
    · rw [iff_true_intro (deliv_of_crash_none (hcO w hwi hwj hwK) i _), iff_true]
      exact not_not.1 fun h => hwK ((hKn w).2 ⟨hwi, h⟩)
  have hsv : SameView x x' i (M + 2) := sameView_succ_of (fun _ => rfl) hlt hlast
  have hal' : x'.Alive i (M + 2) := (alive_of_crash_some hci).2 (by omega)
  have hkc : ¬ x'.Faulty k := by
    rw [not_faulty_iff]; exact hcO k hki (Ne.symm hjk) hkK
  -- `x''`: `j` also receives `z`'s round-`M + 1` message
  set x'' : Run P :=
    { input := x.input
      crash := x'.crash
      reach := fun p => if p = z then insert j (x.reach p) else x'.reach p }
  have hcz' : x'.crash z = some (M + 1) := (hcK z hzK).trans hcz
  have hd'' : ∀ w h s, (w ≠ z ∨ h ≠ j ∨ s ≠ M) → (x''.Deliv w h s ↔ x'.Deliv w h s) := by
    intro w h s hc
    refine deliv_congr rfl fun hcs => ?_
    by_cases hwz : w = z
    · subst hwz
      rw [hcz', Option.some.injEq] at hcs
      have hhj : h ≠ j := by
        rcases hc with hc | hc | hc
        · exact absurd rfl hc
        · exact hc
        · omega
      simp [x'', x', hzi, hzjne, hhj]
    · simp [x'', hwz]
  have hx'' : Adm t bin x'' := ⟨⟨hx'.1.1, hx'.1.2⟩, hx.2⟩
  have hsvi : SameView x x'' i (M + 1) := by
    refine (hsv.mono (Nat.le_succ _)).trans (sameView_of_agree (fun _ _ => rfl)
      (fun h s hs w _ => (hd'' w h s ?_).symm))
    by_contra hc; push Not at hc; obtain ⟨rfl, rfl, rfl⟩ := hc
    exact hji (seen_same_time hs)
  have hdl : ∀ w q s, s < M + 1 → (w ≠ z ∨ q ≠ j ∨ s ≠ M) → (x''.Deliv w q s ↔ x.Deliv w q s) :=
    fun w q s hs hc => (hd'' w q s hc).trans (hlt s hs w q).symm
  have hdl' : ∀ w, w ≠ i → (x''.Deliv w i (M + 1) ↔ x.Deliv w i (M + 1)) :=
    fun w hw => (hd'' w i (M + 1) (Or.inr (Or.inr (by omega)))).trans (hlast w hw).symm
  have hal'' : x''.Alive i (M + 2 + 1 - 1) := hal'
  have H'' : ICHyp t x'' i z j M := by
    refine ⟨hx'', hal', (SameView.firstKnows_iff hsvi).1 hf,
      fun hk => hnk ((kCorrect_iff_of_sameView hsvi).2 hk), ?_, hzi,
      (hdl z i M (by omega) (Or.inr (Or.inl hji.symm))).2 hzd, ?_, hji, ?_, ?_, ?_⟩
    · have := (hsvi.of_seen (seen_of_deliv hzi hzd)).vals_eq
      rw [← this]; exact hz0
    · intro h; have := h.1 (M + 1) hcz'; omega
    · rw [deliv_of_crash_some (show x''.crash j = some (M + 2) from hcj)]
      exact Or.inr ⟨rfl, by simp [x'', x', hzjne.symm, hji]⟩
    · rw [deliv_of_crash_some (show x''.crash z = some (M + 1) from hcz')]
      exact Or.inr ⟨rfl, by simp [x'']⟩
    · have : knownSet x'' i (M + 2) = Kn := by
        ext p
        rw [mem_knownSet, guarCrashed_now_iff hal'' (Nat.succ_pos _), hKn]
        try simp only [Nat.add_sub_cancel]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ((hdl' p h1).2 h)⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ((hdl' p h1).1 h)⟩
      rw [known_eq_card, this, ← known_eq_card]; omega
  have hdi'' := ic ht hQ hdom hG _ x'' i z j H'' rfl
  -- `k` cannot distinguish `x'` from `x''`
  have hnseen : ∀ s, ¬ Seen x' j (M + 1) k s := by
    intro s
    set S : ℕ → P → Prop := fun τ a => (a = j ∧ M + 1 ≤ τ) ∨ (a = i ∧ M + 2 ≤ τ)
    have hstep : ∀ τ a b, S τ a → comm x' τ a b → S (τ + 1) b := by
      rintro τ a b (⟨rfl, hτ⟩ | ⟨rfl, hτ⟩) ⟨-, hd⟩
      · rw [deliv_of_crash_some hcj] at hd
        rcases hd with h | ⟨h, hb⟩
        · omega
        · simp only [x', hji, ite_true, ite_false, Set.mem_singleton_iff] at hb
          exact Or.inr ⟨hb, by omega⟩
      · rw [deliv_of_crash_some hci] at hd
        rcases hd with h | ⟨-, hb⟩
        · omega
        · simp [x'] at hb
    have hstay : ∀ τ a, S τ a → S (τ + 1) a := by
      rintro τ a (⟨h, hτ⟩ | ⟨h, hτ⟩)
      · exact Or.inl ⟨h, by omega⟩
      · exact Or.inr ⟨h, by omega⟩
    exact not_seen_of_inv hstep hstay (Or.inl ⟨rfl, le_rfl⟩) (by
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact hjk h.symm
      · exact hki h)
  have hsvk : ∀ s, SameView x' x'' k s := by
    intro s
    refine sameView_of_agree (fun _ _ => rfl) (fun h s' hs w _ => (hd'' w h s' ?_).symm)
    by_contra hc; push Not at hc; obtain ⟨rfl, rfl, rfl⟩ := hc; exact hnseen s hs
  obtain ⟨mk, u, hu⟩ := hQ.decision x' hx' k hkc
  have hu'' : DecidesAt Q x'' k mk u :=
    ((hsvk mk).decidesAt_iff Q le_rfl ⟨fun _ => SyncCrash.Run.alive_of_not_faulty
      (show ¬ x''.Faulty k from hkc) _, fun _ => SyncCrash.Run.alive_of_not_faulty hkc _⟩).1 hu
  obtain rfl : u = 0 := uagree hQ hx'' hu'' hdi''
  exact force_at ht hQ hdom hx hal hf.1 hnk hx' hsv hal' hu

include ht hQ hdom in
/-- Part 2 of Lemma 15 at every level. -/
theorem g15_all : ∀ s, G15 t Q s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  rcases s with _ | M
  · exact g15_zero ht hQ hdom
  · exact g15_succ ht hQ hdom fun s' hs' => ih s' (by omega)

include ht hQ hdom in
/-- **Lemma 15, Part 2.** Let `m > 0`, let `i` know `∃0` for the first time at `m`, not know
`∃correct(0)` at `m` (so that `K_i ∃correct(0)` first holds at `m + 1`), and be alive at
`m + 1`. If `F⟨i, m + 1⟩ < t - 1`, then `i` decides `0` at `m + 1`. -/
theorem lemma15_part2 {x : Run P} (hx : Adm t bin x) {i : P} {m : ℕ} (_hm : 0 < m)
    (hf : FirstKnows x i m 0) (hnk : ¬ KCorrect t x i m 0) (hal : x.Alive i (m + 1))
    (hF : known x i (m + 1) + 1 < t) : DecidesAt Q x i (m + 1) 0 :=
  g15_all ht hQ hdom m x hx i hal hf hnk (by omega)

include ht hQ hdom in
/-- **Lemma 15, Part 1** (`m = M + 1`). Let `i` know `∃0` for the first time at `m`, not know
`∃correct(0)` at `m`, and be alive at `m + 1`. Assume `F⟨i, m + 1⟩ < t`, a process `z` with
`K_z ∃0` at `m - 1` and `⟨z, m - 1⟩` seen by `⟨i, m⟩` but `⟨z, m⟩` not seen by `⟨i, m + 1⟩`, and a
process `j ≠ i` with `⟨j, m⟩` seen by `⟨i, m + 1⟩` that has seen `⟨z, m - 1⟩`. Then `i` decides `0`
at `m + 1`. -/
theorem lemma15_part1 {x : Run P} (hx : Adm t bin x) {i : P} {M : ℕ}
    (hf : FirstKnows x i (M + 1) 0) (hnk : ¬ KCorrect t x i (M + 1) 0) (hal : x.Alive i (M + 2))
    (hF : known x i (M + 2) < t) {z : P} (hz0 : 0 ∈ vals x z M) (hzs : Seen x z M i (M + 1))
    (hzn : ¬ Seen x z (M + 1) i (M + 2)) {j : P} (hji : j ≠ i) (hjs : Seen x j (M + 1) i (M + 2))
    (hjz : Seen x z M j (M + 1)) : DecidesAt Q x i (M + 2) 0 := by
  have hzi : z ≠ i := by rintro rfl; exact hf.2 M rfl hz0
  rw [seen_succ_self_iff] at hzs hjs hjz hzn
  have hzd : x.Deliv z i M := by
    rcases hzs with h | ⟨-, h⟩
    · exact absurd h hzi
    · exact h
  have hzn' : ¬ x.Deliv z i (M + 1) := fun h => hzn (Or.inr ⟨hzi, h⟩)
  have hjd : x.Deliv j i (M + 1) := by
    rcases hjs with h | ⟨-, h⟩
    · exact absurd h hji
    · exact h
  have hzj : x.Deliv z j M := by
    rcases hjz with rfl | ⟨-, h⟩
    · exact absurd (Or.inr ⟨hji, hjd⟩) hzn
    · exact h
  exact ic ht hQ hdom (fun s _ => g15_all ht hQ hdom s) _ x i z j
    ⟨hx, hal, hf, hnk, hz0, hzi, hzd, hzn', hji, hjd, hzj, hF⟩ rfl

end Lemma15

end Podc.ParetoOptimalConsensus
