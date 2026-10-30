import Papers.PODC2013.ParetoOptimalConsensus.Lemma17Runs

/-!
# Lemma 17 (no earlier decisions when `¬K_i ∃0`, Appendix C)

Let `Q ⪰ U-P0` solve uniform consensus, `0 < t < n`. If there is a hidden path w.r.t. `⟨i, m⟩`
and `¬K_i ∃0` at `m`, then `i` does not decide at `m`.

Proof as in the paper, with the runs of `Lemma17Runs.lean` (`z = b M` is the hidden node at
`m - 1 = M`, `j = b (M + 1)` the hidden node at `m`, which reached `⟨i, m⟩`):

* `F⟨i, m⟩ < t`: in `r'`, `z` crashes in round `m` reaching everybody but `i`, and `i` crashes
  silently in round `m + 1`; `j` knows `∃correct(0)` at `m + 1`. In `r''` (indistinguishable to
  `j` at `m + 1`) `z` survives round `m`, and decides `0` by Lemma 15, Part 2 (Lemma 14, Part 2 if
  `m = 1`). So `j` decides `0`, and `i` cannot decide `1`.
* `F⟨i, m⟩ = t`: four runs `r' ~_j r'' ~_z r''' ~_j r''''`. In `r'''` the node `⟨i, m - 1⟩` has
  seen `⟨b (m - 2), m - 2⟩` (or `i` has input `0` if `m = 1`); in `r''''`, where `i` is correct,
  `z` decides `0` by Lemma 15, Part 1 (Lemma 14, Part 1 if `m = 1`), and the decision on `0`
  propagates back along the chain (`link`).
-/

namespace Podc.ParetoOptimalConsensus

open Cslib Finset Podc.UnbeatableSetConsensus

variable {P : Type*} [Fintype P] {t : ℕ}

/-- Discharge `∀ c, x = some c → k ≤ c` for a literal `x`. -/
local macro "opt_bound" : tactic =>
  `(tactic| (intro c hc; first | (cases hc; done) | (simp only [Option.some.injEq] at hc; omega)))

section Lemma17

variable {Q : Protocol P} (ht0 : 0 < t) (ht : t < Fintype.card P)
  (hQ : SolvesUniformSetConsensus 1 t bin Q) (hdom : Dominates t bin Q (uP0 t))

include hQ hdom in
/-- If `p` knows `∃correct(0)` at `T` in `rb`, and some process decides `0` in `rb`, then `p`
decides `0` by `T` in every run `ra` that `p` cannot distinguish from `rb` at `T`. -/
lemma link {ra rb : Run P} (hrb : Adm t bin rb) {p : P} {T : ℕ} (hsv : SameView ra rb p T)
    (hpa : ra.Alive p T) (hpb : rb.Alive p T) (hk : KCorrect t rb p T 0) {q : P} {s : ℕ}
    (hq : DecidesAt Q rb q s 0) : ∃ s' ≤ T, DecidesAt Q ra p s' 0 := by
  obtain ⟨s', hs', u, hu⟩ := decidesBy_of_kc hdom hrb hpb hk
  obtain rfl : u = 0 := uagree hQ hrb hu hq
  exact ⟨s', hs', (hsv.decidesAt_iff Q hs' ⟨fun _ => hpb.mono hs', fun _ => hpa.mono hs'⟩).2 hu⟩

omit [Fintype P] in
/-- Members of the family agree on the processes other than `b M`, `i` and `b (M - 1)`. -/
lemma l17_deliv_eq [Fintype P] {r : Run P} {i : P} {M : ℕ} {b : ℕ → P}
    {cz₁ cz₂ ci₁ ci₂ : Option ℕ} {Rz₁ Rz₂ Ri₁ Ri₂ R₁ R₂ : Set P} {in₁ in₂ : ℕ} {w q : P} {s : ℕ}
    (hwz : w ≠ b M) (hwi : w ≠ i)
    (hw' : w = b (M - 1) → (l17Run r i M b cz₁ Rz₁ ci₁ Ri₁ R₁ in₁).crash w = some (s + 1) →
      (q ∈ R₁ ↔ q ∈ R₂)) :
    (l17Run r i M b cz₁ Rz₁ ci₁ Ri₁ R₁ in₁).Deliv w q s ↔
      (l17Run r i M b cz₂ Rz₂ ci₂ Ri₂ R₂ in₂).Deliv w q s := by
  refine deliv_congr (by simp [l17Run, hwz, hwi]) fun hc => ?_
  by_cases h : w = b (M - 1)
  · have e1 : (l17Run r i M b cz₁ Rz₁ ci₁ Ri₁ R₁ in₁).reach w = R₁ := by
      simp only [l17Run]; rw [ite_eq_right hwz, ite_eq_right hwi, ite_eq_left h]
    have e2 : (l17Run r i M b cz₂ Rz₂ ci₂ Ri₂ R₂ in₂).reach w = R₂ := by
      simp only [l17Run]; rw [ite_eq_right hwz, ite_eq_right hwi, ite_eq_left h]
    rw [e1, e2]; exact hw' h hc
  · simp [l17Run, hwz, hwi, h]

include ht0 ht hQ hdom in
/-- **Lemma 17.** -/
theorem lemma17 {r : Run P} (hr : Adm t bin r) {i : P} {m : ℕ} (hp : HiddenPath r i m)
    (h0 : 0 ∉ vals r i m) (v : ℕ) : ¬ DecidesAt Q r i m v := by
  classical
  intro hd
  have hvv := dec_mem_vals' (uniform_toSet hQ) hr hd
  have hv1 : v = 1 := by
    rcases mem_bin.1 (mem_bin_of_mem_vals hr hvv) with rfl | rfl
    · exact absurd hvv h0
    · rfl
  subst hv1
  rcases m with _ | M
  · exact lemma13 ht0 ht hQ hr i 1 hd
  obtain ⟨b, hb⟩ := hp
  have hal := hd.1
  have hsv₀ := l17_base_sameView hb
  have H := l17_chainHyp hb
  have hzi : b M ≠ i := l17_b_ne_i hb (Nat.le_succ M)
  have hji : b (M + 1) ≠ i := l17_b_ne_i hb le_rfl
  have hjz : b (M + 1) ≠ b M := fun h => by
    have := (hb (M + 1) le_rfl).time_eq (h ▸ hb M (Nat.le_succ M)) le_rfl (Nat.le_succ M); omega
  have hzK : b M ∈ l17Kn r i M b := l17_b_mem hb hal le_rfl
  have hjd : (l17Base r i M b).Deliv (b (M + 1)) i M := by
    have hs := (hb (M + 1) le_rfl).seen_pred le_rfl
    rw [seen_succ_self_iff] at hs
    rcases hs with h | ⟨-, h⟩
    · exact absurd h hji
    · exact (hsv₀.deliv_iff hji).1 h
  have hjK : b (M + 1) ∉ l17Kn r i M b := fun h => ((l17_mem_Kn hb hal).1 h).2 hjd
  have hiK : i ∉ l17Kn r i M b := l17_i_notMem hb hal
  have hr₀ : Adm t bin (l17Base r i M b) := by
    refine ⟨⟨le_trans (card_le_card fun p hp => SyncCrash.Run.mem_faulty.2 ?_) hr.1.1,
      fun p c hc => H.crash_pos hr hc⟩, ChainHyp.input_mem hr (fun _ => zero_mem_bin)⟩
    have hp' := SyncCrash.Run.mem_faulty.1 hp
    rcases H.faulty_of hp' with h | ⟨_, rfl⟩
    · exact h
    · exact (hb M (Nat.le_succ M)).faulty (Nat.lt_succ_self M)
  have hFt : (l17Kn r i M b).card ≤ t := by
    have := known_le (t := t) (r := l17Base r i M b) (i := i) (m := M + 1) hr₀
    rw [known_eq_card] at this; exact this
  have hzf : FirstKnows (l17Base r i M b) (b M) M 0 := l17_z_first hb h0
  have hcar := l17_carriers_le hb h0
  set j := b (M + 1)
  set z := b M
  -- the run `r'` (with `i` crashing silently in round `M + 2`, or correct)
  have hr'_gen : ∀ ci : Option ℕ, (ci = none ∨ ci = some (M + 2)) →
      SameView r (l17Run r i M b (some (M + 1)) {p | p ≠ i} ci ∅ ((l17Base r i M b).reach (b (M - 1)))
        ((l17Base r i M b).input i)) i (M + 1) := by
    intro ci hci
    refine hsv₀.trans (sameView_succ_of (fun q => by by_cases hq : q = i <;> simp [l17Run, hq])
      (fun s hs w q => ?_) (fun w hw => (l17_deliv_last hb hal rfl (show i ∉ {p : P | p ≠ i} from fun h => h rfl) w hw).symm))
    by_cases hex : w = b (M - 1) ∧ q = i ∧ s + 1 = M
    · obtain ⟨rfl, rfl, hsM⟩ := hex
      have hM : 0 < M := by omega
      have hne : b (M - 1) ≠ b M := fun h => by
        have := (hb (M - 1) (by omega)).time_eq (h ▸ hb M (Nat.le_succ M)) (by omega)
          (Nat.le_succ M); omega
      refine (deliv_congr (l17_crash_K hb hal (l17_b_mem hb hal (by omega)) hne).symm
        fun _ => ?_)
      simp [l17Run, hne, l17_b_ne_i hb (show M - 1 ≤ M + 1 by omega)]
    · exact (l17_deliv_lt hb hal (by opt_bound) (by rintro c (h | h) <;> rcases hci with h' | h' <;>
        simp_all) (fun _ _ => Iff.rfl) (by omega) w q hex).symm
  -- facts about `z` and `j` common to the runs in which `z` reaches `j` in round `M + 1`
  have hz0 : ∀ {cz ci Rz Ri R ini}, (∀ c, cz = some c → M + 1 ≤ c) →
      (∀ c, ci = some c → M + 1 ≤ c) → (∀ q, q ≠ i → (q ∈ R ↔ q ∈ (l17Base r i M b).reach (b (M - 1)))) →
      (M = 0 ∨ ini = (l17Base r i M b).input i) → 0 ∈ vals (l17Run r i M b cz Rz ci Ri R ini) z M := by
    intro cz ci Rz Ri R ini h1 h2 h3 h4
    rw [← (l17_sameView_z hb hal h1 h2 h3 h4).vals_eq]; exact hzf.1
  have hR0 : ∀ q, q ≠ i → (q ∈ (l17Base r i M b).reach (b (M - 1)) ↔
      q ∈ (l17Base r i M b).reach (b (M - 1))) := fun _ _ => Iff.rfl
  have hI0 : (l17Base r i M b).input i ∈ bin := hr₀.2 i
  have hjc : ∀ {cz Rz ci Ri R ini}, ¬ (l17Run r i M b cz Rz ci Ri R ini).Faulty j := by
    intro cz Rz ci Ri R ini; rw [not_faulty_iff]; exact l17_crash_O hb hal hjK hji
  have hzj : ∀ {Rz ci Ri R ini}, j ∈ Rz → (l17Run r i M b (some (M + 1)) Rz ci Ri R ini).Deliv z j M := by
    intro Rz ci Ri R ini hj
    rw [deliv_of_crash_some l17_crash_z, l17_reach_z]; exact Or.inr ⟨rfl, hj⟩
  have hzj' : ∀ {Rz ci Ri R ini}, (l17Run r i M b none Rz ci Ri R ini).Deliv z j M := fun {_ _ _ _ _} =>
    deliv_of_crash_none l17_crash_z j M
  have hci' : ∀ {cz Rz Ri R ini}, (l17Run r i M b cz Rz none Ri R ini).Alive i (M + 2) :=
    fun {_ _ _ _ _} => alive_of_crash_none (l17_crash_i hb) _
  -- a run in which `j` hears `0` from `z` in round `M + 1` and the other known processes are silent:
  -- `j` knows `∃correct(0)` at `M + 1` when `F⟨i, M + 1⟩ = t`
  have hKCj : (l17Kn r i M b).card = t → ∀ {cz Rz ci Ri R ini},
      Adm t bin (l17Run r i M b cz Rz ci Ri R ini) →
      (l17Run r i M b cz Rz ci Ri R ini).Deliv z j M →
      0 ∈ vals (l17Run r i M b cz Rz ci Ri R ini) z M →
      KCorrect t (l17Run r i M b cz Rz ci Ri R ini) j (M + 1) 0 := by
    intro hFeq cz Rz ci Ri R ini hx hd hz
    have hja := SyncCrash.Run.alive_of_not_faulty (hjc (cz := cz) (Rz := Rz) (ci := ci) (Ri := Ri)
      (R := R) (ini := ini)) (M + 1)
    refine (lemma6 ht hx hja zero_mem_bin).2 ⟨vals_subset_succ_of_comm ⟨Ne.symm hjz, hd⟩ hz,
      Or.inr ?_⟩
    have hc1 : 1 ≤ carriers (l17Run r i M b cz Rz ci Ri R ini) j (M + 1) 0 := by
      rw [carriers_eq_card]
      exact card_pos.2 ⟨z, mem_carrierSet.2 ⟨Nat.succ_pos M,
        by simpa using seen_of_deliv (Ne.symm hjz) hd, by simpa using hz⟩⟩
    have hk1 : t - 1 ≤ known (l17Run r i M b cz Rz ci Ri R ini) j (M + 1) := by
      have hsub : (l17Kn r i M b).erase z ⊆ knownSet (l17Run r i M b cz Rz ci Ri R ini) j (M + 1) := by
        intro p hp
        obtain ⟨hpz, hpK⟩ := mem_erase.1 hp
        rw [mem_knownSet, guarCrashed_now_iff (by simpa using hja) (Nat.succ_pos M)]
        try simp only [Nat.add_sub_cancel]
        exact ⟨fun h => hjK (h ▸ hpK), l17_silent hb hal hpK hpz j⟩
      have := card_le_card hsub
      rw [card_erase_of_mem hzK, hFeq, ← known_eq_card] at this
      exact this
    omega
  rcases Nat.lt_or_ge (l17Kn r i M b).card t with hlt | hge
  · -- **Case `F⟨i, M + 1⟩ < t`**
    set ra := l17Run r i M b (some (M + 1)) {p | p ≠ i} (some (M + 2)) ∅
      ((l17Base r i M b).reach (b (M - 1))) ((l17Base r i M b).input i)
    set rb := l17Run r i M b (some (M + 2)) ∅ (some (M + 2)) ∅
      ((l17Base r i M b).reach (b (M - 1))) ((l17Base r i M b).input i)
    have hcard : ∀ {cz Rz Ri}, (l17Run r i M b cz Rz (some (M + 2)) Ri
        ((l17Base r i M b).reach (b (M - 1))) ((l17Base r i M b).input i)).faulty.card ≤ t := by
      intro cz Rz Ri
      refine (card_le_card (show _ ⊆ insert i (l17Kn r i M b) from fun p hp => ?_)).trans
        ((card_insert_le _ _).trans (by omega))
      rcases l17_faulty_subset hb hal (SyncCrash.Run.mem_faulty.1 hp) with h | h
      · exact h ▸ mem_insert_self _ _
      · exact mem_insert_of_mem h
    have hra : Adm t bin ra := l17_adm hb hal hr (by opt_bound) (by opt_bound) hI0 hcard
    have hrb : Adm t bin rb := l17_adm hb hal hr (by opt_bound) (by opt_bound) hI0 hcard
    have hala : ra.Alive i (M + 1) := (alive_of_crash_some (l17_crash_i hb)).2 (by omega)
    have hdi : DecidesAt Q ra i (M + 1) 1 :=
      ((hr'_gen _ (Or.inr rfl)).decidesAt_iff Q le_rfl ⟨fun _ => hala, fun _ => hal⟩).1 hd
    -- `z` decides `0` in `rb`
    have hzal : rb.Alive z (M + 1) := (alive_of_crash_some l17_crash_z).2 (by omega)
    have hsvz : SameView (l17Base r i M b) rb z M :=
      l17_sameView_z hb hal (by opt_bound) (by opt_bound) hR0 (Or.inr rfl)
    have hfz : FirstKnows rb z M 0 := (SameView.firstKnows_iff hsvz).1 hzf
    have hknz : known rb z (M + 1) + 2 ≤ t := by
      have hsub : knownSet rb z (M + 1) ⊆ (l17Kn r i M b).erase z := by
        intro p hp
        rw [mem_knownSet, guarCrashed_now_iff (by simpa using hzal) (Nat.succ_pos M)] at hp
        try simp only [Nat.add_sub_cancel] at hp
        obtain ⟨hpz, hnd⟩ := hp
        refine mem_erase.2 ⟨hpz, ?_⟩
        by_contra hpK
        by_cases hpi : p = i
        · rw [hpi] at hnd
          exact hnd (deliv_of_alive_succ ((alive_of_crash_some (l17_crash_i hb)).2 (by omega)) z)
        · exact hnd (deliv_of_crash_none (l17_crash_O hb hal hpK hpi) z M)
      have := card_le_card hsub
      rw [card_erase_of_mem hzK, ← known_eq_card] at this
      have := card_pos.2 ⟨z, hzK⟩
      omega
    have hnkz : ¬ KCorrect t rb z M 0 := by
      intro hk
      rw [lemma6 ht hrb (hzal.mono (Nat.le_succ M)) zero_mem_bin] at hk
      obtain ⟨-, ha | hb'⟩ := hk
      · exact hfz.2 (M - 1) (by omega) ha.2
      · rw [← carriers_eq_of_sameView hsvz] at hb'
        have : known rb z M ≤ known rb z (M + 1) := known_mono (Nat.le_succ M)
        omega
    have hdz : DecidesAt Q rb z (M + 1) 0 := g15_all ht hQ hdom M rb hrb z hzal hfz hnkz hknz
    -- `j` cannot distinguish `ra` from `rb` at `M + 2`
    have hsvj : SameView ra rb j (M + 2) := by
      refine sameView_of_agree (fun _ _ => rfl) (fun h s hs w hw => ?_)
      have hsle := hs.le
      by_cases hwz : w = z
      · rw [hwz, deliv_of_crash_some l17_crash_z, deliv_of_crash_some l17_crash_z, l17_reach_z,
          l17_reach_z]
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, and_false, or_false]
        rcases Nat.lt_trichotomy s M with h1 | rfl | h1
        · exact iff_of_true (Or.inl (by omega)) (by omega)
        · refine iff_of_true (Or.inr ⟨rfl, fun hhi => ?_⟩) (by omega)
          subst hhi
          rw [seen_succ_self_iff] at hs
          rcases hs with h' | ⟨-, h'⟩
          · exact hji h'.symm
          · rw [deliv_of_crash_some (l17_crash_i hb), l17_reach_i hb] at h'
            rcases h' with h' | ⟨-, h'⟩
            · omega
            · exact h'
        · exact iff_of_false (by omega) (by omega)
      by_cases hwi : w = i
      · rw [hwi]
        exact deliv_congr (by rw [l17_crash_i hb, l17_crash_i hb]) fun _ => by
          rw [l17_reach_i hb, l17_reach_i hb]
      · exact l17_deliv_eq hwz hwi fun _ _ => Iff.rfl
    have hkcj : KCorrect t ra j (M + 2) 0 :=
      kCorrect_of_prev ht hra (SyncCrash.Run.alive_of_not_faulty hjc _)
        (vals_subset_succ_of_comm ⟨Ne.symm hjz, hzj (show j ∈ {p | p ≠ i} from hji)⟩
          (hz0 (by opt_bound) (by opt_bound) hR0 (Or.inr rfl)))
    obtain ⟨s', -, hdj⟩ := link hQ hdom hrb hsvj (SyncCrash.Run.alive_of_not_faulty hjc _)
      (SyncCrash.Run.alive_of_not_faulty hjc _) ((kCorrect_iff_of_sameView hsvj).1 hkcj) hdz
    exact one_ne_zero (uagree hQ hra hdi hdj)
  · -- **Case `F⟨i, M + 1⟩ = t`**
    have hFeq : (l17Kn r i M b).card = t := le_antisymm hFt hge
    set R0 := (l17Base r i M b).reach (b (M - 1))
    set I0 := (l17Base r i M b).input i
    set R3 : Set P := if 0 < M then insert i R0 else R0
    set I3 : ℕ := if M = 0 then 0 else I0
    have hR3 : ∀ q, q ≠ i → (q ∈ R3 ↔ q ∈ R0) := by
      intro q hq; simp only [R3]; split_ifs <;> simp [hq]
    have hI3 : M = 0 ∨ I3 = I0 := by
      rcases Nat.eq_zero_or_pos M with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [I3, show M ≠ 0 by omega])
    have hI3b : I3 ∈ bin := by simp only [I3]; split_ifs; exacts [zero_mem_bin, hI0]
    set ra := l17Run r i M b (some (M + 1)) {p | p ≠ i} none ∅ R0 I0
    set rb := l17Run r i M b none ∅ (some (M + 1)) {j} R0 I0
    set rc := l17Run r i M b none ∅ (some (M + 1)) {j} R3 I3
    set rd := l17Run r i M b none ∅ none ∅ R3 I3
    have hcardK : ∀ {Rz R ini} {cz : Option ℕ},
        (l17Run r i M b cz Rz none ∅ R ini).faulty.card ≤ t := by
      intro Rz R ini cz
      refine (card_le_card fun p hp => ?_).trans hFeq.le
      rcases l17_faulty_subset hb hal (SyncCrash.Run.mem_faulty.1 hp) with h | h
      · exact absurd (h ▸ l17_crash_i hb) (SyncCrash.Run.mem_faulty.1 hp)
      · exact h
    have hcardi : ∀ {R ini}, (l17Run r i M b none ∅ (some (M + 1)) {j} R ini).faulty.card ≤ t := by
      intro R ini
      refine (card_le_card (show _ ⊆ insert i ((l17Kn r i M b).erase z) from fun p hp => ?_)).trans
        ((card_insert_le _ _).trans (by rw [card_erase_of_mem hzK]; omega))
      have hpf := SyncCrash.Run.mem_faulty.1 hp
      rcases l17_faulty_subset hb hal hpf with h | h
      · exact h ▸ mem_insert_self _ _
      · refine mem_insert_of_mem (mem_erase.2 ⟨fun hpz => ?_, h⟩)
        rw [hpz] at hpf; exact hpf l17_crash_z
    have hra : Adm t bin ra := l17_adm hb hal hr (by opt_bound) (by opt_bound) hI0 hcardK
    have hrb : Adm t bin rb := l17_adm hb hal hr (by opt_bound) (by opt_bound) hI0 hcardi
    have hrc : Adm t bin rc := l17_adm hb hal hr (by opt_bound) (by opt_bound) hI3b hcardi
    have hrd : Adm t bin rd := l17_adm hb hal hr (by opt_bound) (by opt_bound) hI3b hcardK
    have hdi : DecidesAt Q ra i (M + 1) 1 :=
      ((hr'_gen _ (Or.inl rfl)).decidesAt_iff Q le_rfl ⟨fun _ =>
        alive_of_crash_none (l17_crash_i hb) _, fun _ => hal⟩).1 hd
    have hzc : ∀ {R ini ci Ri}, ¬ (l17Run r i M b none ∅ ci Ri R ini).Faulty z :=
      fun {_ _ _ _} => by rw [not_faulty_iff]; exact l17_crash_z
    -- the views along the chain `ra ~_j rb ~_z rc ~_j rd`
    have hsvab : SameView ra rb j (M + 1) := by
      refine sameView_of_agree (fun _ _ => rfl) (fun h s hs w hw => ?_)
      have hsle := hs.le
      by_cases hwz : w = z
      · rw [hwz, deliv_of_crash_some l17_crash_z, l17_reach_z]
        refine iff_of_true ?_ (deliv_of_crash_none l17_crash_z h s)
        rcases Nat.lt_or_ge s M with h1 | h1
        · exact Or.inl (by omega)
        · obtain rfl : s = M := by omega
          obtain rfl := seen_same_time hs
          exact Or.inr ⟨rfl, hji⟩
      by_cases hwi : w = i
      · rw [hwi, iff_true_intro (deliv_of_crash_none (l17_crash_i hb) _ _),
          deliv_of_crash_some (l17_crash_i hb), l17_reach_i hb]
        refine iff_of_true trivial ?_
        rcases Nat.lt_or_ge s M with h1 | h1
        · exact Or.inl (by omega)
        · obtain rfl : s = M := by omega
          obtain rfl := seen_same_time hs
          exact Or.inr ⟨rfl, rfl⟩
      · exact l17_deliv_eq hwz hwi fun _ _ => Iff.rfl
    -- in `rb` and `rc`, `i` sends only to `j` in round `M + 1`
    have hiz : ∀ {R ini}, ¬ (l17Run r i M b none ∅ (some (M + 1)) {j} R ini).Deliv i z M := by
      intro R ini hd'
      rw [deliv_of_crash_some (l17_crash_i hb), l17_reach_i hb] at hd'
      rcases hd' with h' | ⟨-, h'⟩
      · omega
      · exact hjz (Set.mem_singleton_iff.1 h').symm
    have hbM : ∀ {R ini} {cz ci : Option ℕ} {Rz Ri : Set P}, 0 < M →
        (l17Run r i M b cz Rz ci Ri R ini).crash (b (M - 1)) = some M := by
      intro R ini cz ci Rz Ri hM
      have hne : b (M - 1) ≠ b M := fun h => by
        have := (hb (M - 1) (by omega)).time_eq (h ▸ hb M (Nat.le_succ M)) (by omega)
          (Nat.le_succ M); omega
      rw [l17_crash_K hb hal (l17_b_mem hb hal (by omega)) hne, l17_base_crash_b hb (by omega)]
      congr 1; omega
    have hsvbc : SameView rb rc z (M + 1) := by
      refine sameView_of_agree (fun q hq => ?_) (fun h s hs w hw => ?_)
      · by_cases hqi : q = i
        · subst hqi
          rcases Nat.eq_zero_or_pos M with hM | hM
          · exfalso
            subst hM
            rw [seen_succ_self_iff] at hq
            rcases hq with h' | ⟨-, h'⟩
            · exact hzi h'.symm
            · exact hiz h'
          · simp [rb, rc, l17Run, I3, show M ≠ 0 by omega]
        · simp [rb, rc, l17Run, hqi]
      · by_cases hwz : w = z
        · rw [hwz]; exact iff_of_true (deliv_of_crash_none l17_crash_z h s)
            (deliv_of_crash_none l17_crash_z h s)
        by_cases hwi : w = i
        · rw [hwi]
          exact deliv_congr (by rw [l17_crash_i hb, l17_crash_i hb]) fun _ => by
            rw [l17_reach_i hb, l17_reach_i hb]
        refine l17_deliv_eq hwz hwi fun hw' hc => ?_
        by_cases hhi : h = i
        · exfalso
          subst hhi
          have hM : 0 < M := by
            rcases Nat.eq_zero_or_pos M with h0' | h0'
            · have : b (M - 1) = b M := by rw [h0']
              exact absurd (hw'.trans this) hwz
            · exact h0'
          rw [hw', hbM hM, Option.some.injEq] at hc
          rw [← hc] at hs
          rw [seen_succ_self_iff] at hs
          rcases hs with h' | ⟨-, h'⟩
          · exact hzi h'.symm
          · exact hiz h'
        · exact (hR3 h hhi).symm
    have hsvcd : SameView rc rd j (M + 1) := by
      refine sameView_of_agree (fun _ _ => rfl) (fun h s hs w hw => ?_)
      have hsle := hs.le
      by_cases hwz : w = z
      · rw [hwz]; exact iff_of_true (deliv_of_crash_none l17_crash_z h s)
          (deliv_of_crash_none l17_crash_z h s)
      by_cases hwi : w = i
      · rw [hwi, deliv_of_crash_some (l17_crash_i hb),
          iff_true_intro (deliv_of_crash_none (l17_crash_i hb) _ _), l17_reach_i hb]
        refine iff_of_true ?_ trivial
        rcases Nat.lt_or_ge s M with h1 | h1
        · exact Or.inl (by omega)
        · obtain rfl : s = M := by omega
          obtain rfl := seen_same_time hs
          exact Or.inr ⟨rfl, rfl⟩
      · exact l17_deliv_eq hwz hwi fun _ _ => Iff.rfl
    -- knowledge of `∃correct(0)` along the chain
    have hz0b : 0 ∈ vals rb z M := hz0 (by opt_bound) (by opt_bound) hR0 (Or.inr rfl)
    have hz0c : 0 ∈ vals rc z M := hz0 (by opt_bound) (by opt_bound) hR3 hI3
    have hz0d : 0 ∈ vals rd z M := hz0 (by opt_bound) (by opt_bound) hR3 hI3
    have hkb : KCorrect t rb j (M + 1) 0 := hKCj hFeq hrb hzj' hz0b
    have hkc : KCorrect t rc z (M + 1) 0 :=
      kCorrect_of_prev ht hrc (SyncCrash.Run.alive_of_not_faulty hzc _) hz0c
    have hkd : KCorrect t rd j (M + 1) 0 := hKCj hFeq hrd hzj' hz0d
    -- `z` decides `0` in `rd`
    have hzal : rd.Alive z (M + 1) := SyncCrash.Run.alive_of_not_faulty hzc _
    have hsvz : SameView (l17Base r i M b) rd z M :=
      l17_sameView_z hb hal (by opt_bound) (by opt_bound) hR3 hI3
    have hdz : DecidesAt Q rd z (M + 1) 0 := by
      have hic : ¬ rd.Faulty i := by rw [not_faulty_iff]; exact l17_crash_i hb
      rcases M with _ | M'
      · -- `m = 1`: Lemma 14, Part 1, with `i` (input `0` in `rd`) seen by `z`
        refine lemma14_part1 ht0 ht hQ hdom hrd ?_ hzal ⟨i, Ne.symm hzi, ?_, ?_⟩
        · have : rd.input z = (l17Base r i 0 b).input (b 0) := by simp [rd, l17Run, hzi]; rfl
          rw [this]; exact H.input_w0 ()
        · simp [rd, l17Run, I3]
        · exact seen_of_deliv (Ne.symm hzi) (SyncCrash.Run.deliv_of_not_faulty hic z 0)
      · -- `m = M' + 2`: Lemma 15, Part 1, with `z' = b M'` and `j = i`
        have hne : b M' ≠ b (M' + 1) := fun h => by
          have := (hb M' (by omega)).time_eq (h ▸ hb (M' + 1) (by omega)) (by omega)
            (by omega); omega
        have hb'i : b M' ≠ i := l17_b_ne_i hb (by omega)
        have hsb : Seen (l17Base r i (M' + 1) b) (b M') M' z (M' + 1) :=
          seen_of_deliv hne ((l17_base_deliv_b hb (by omega) _).2 (Or.inr ⟨rfl, by omega, rfl⟩))
        have hsb' : Seen rd (b M') M' z (M' + 1) := hsvz.seen hsb
        have hcb : rd.crash (b M') = some (M' + 1) := by
          have := hbM (R := R3) (ini := I3) (cz := none) (ci := none) (Rz := ∅) (Ri := ∅)
            (Nat.succ_pos M')
          simpa using this
        have hfd : FirstKnows rd z (M' + 1) 0 := (SameView.firstKnows_iff hsvz).1 hzf
        -- `z` knows of at most `t - 2` failures at `M' + 1`
        have hfd_card : rd.faulty.card ≤ t - 1 := by
          refine (card_le_card fun p hp => ?_).trans (by rw [card_erase_of_mem hzK]; omega)
          have hpf := SyncCrash.Run.mem_faulty.1 hp
          rcases l17_faulty_subset hb hal hpf with h | h
          · exact absurd (h ▸ l17_crash_i hb) hpf
          · exact mem_erase.2 ⟨fun hpz => hzc (hpz ▸ hpf), h⟩
        have hbf : b M' ∈ rd.faulty := SyncCrash.Run.mem_faulty.2 (by
          unfold SyncCrash.Run.Faulty; rw [hcb]; simp)
        have hkz : known rd z (M' + 1) + 2 ≤ t := by
          have hsub : knownSet rd z (M' + 1) ⊆ rd.faulty.erase (b M') := by
            intro p hp
            refine mem_erase.2 ⟨fun hpb => ?_, knownSet_subset_faulty hp⟩
            subst hpb
            exact not_guarCrashed_of_seen_pred ((alive_of_crash_some hcb).2 (by omega)) hsb'
              (mem_knownSet.1 hp)
          have h1 := card_le_card hsub
          rw [card_erase_of_mem hbf, ← known_eq_card] at h1
          have h2 := card_pos.2 ⟨_, hbf⟩
          have h3 := hfd_card
          omega
        have hnk : ¬ KCorrect t rd z (M' + 1) 0 := by
          intro hk
          rw [lemma6 ht hrd (hzal.mono (Nat.le_succ _)) zero_mem_bin] at hk
          obtain ⟨-, ha | hb'⟩ := hk
          · exact hfd.2 M' rfl (by simpa using ha.2)
          · rw [← carriers_eq_of_sameView hsvz] at hb'
            omega
        have hF : known rd z (M' + 2) < t := by
          have := card_le_card (knownSet_subset_faulty (r := rd) (i := z) (m := M' + 2))
          rw [← known_eq_card] at this; omega
        have hz'0 : 0 ∈ vals rd (b M') M' := by
          rw [← (hsvz.of_seen hsb).vals_eq]; exact H.mem_vals (by omega) ()
        have hzn : ¬ Seen rd (b M') (M' + 1) z (M' + 2) := by
          rw [seen_succ_self_iff]; rintro (h | ⟨-, h⟩)
          · exact hne h
          · have := h.1 (M' + 1) hcb; omega
        have hjs : Seen rd i (M' + 1) z (M' + 2) :=
          seen_of_deliv (Ne.symm hzi) (SyncCrash.Run.deliv_of_not_faulty hic z _)
        have hjz' : Seen rd (b M') M' i (M' + 1) := by
          refine seen_of_deliv hb'i ?_
          rw [deliv_of_crash_some hcb]
          refine Or.inr ⟨rfl, ?_⟩
          have : rd.reach (b M') = R3 := by
            simp only [rd, l17Run]
            rw [ite_eq_right hne, ite_eq_right hb'i, ite_eq_left (by simp)]
          rw [this]; simp [R3]
        exact lemma15_part1 ht hQ hdom hrd hfd hnk hzal hF hz'0 hsb' hzn (Ne.symm hzi) hjs hjz'
    -- propagate the decision on `0` back along the chain
    have hja := SyncCrash.Run.alive_of_not_faulty (hjc (cz := none) (Rz := ∅) (ci := some (M + 1))
      (Ri := {j}) (R := R3) (ini := I3)) (M + 1)
    obtain ⟨_, -, hdjc⟩ := link hQ hdom hrd hsvcd hja
      (SyncCrash.Run.alive_of_not_faulty hjc _) hkd hdz
    obtain ⟨_, -, hdzb⟩ := link hQ hdom hrc hsvbc (SyncCrash.Run.alive_of_not_faulty hzc _)
      (SyncCrash.Run.alive_of_not_faulty hzc _) hkc hdjc
    obtain ⟨_, -, hdja⟩ := link hQ hdom hrb hsvab (SyncCrash.Run.alive_of_not_faulty hjc _)
      (SyncCrash.Run.alive_of_not_faulty hjc _) hkb hdzb
    exact one_ne_zero (uagree hQ hra hdi hdja)

end Lemma17

end Podc.ParetoOptimalConsensus
