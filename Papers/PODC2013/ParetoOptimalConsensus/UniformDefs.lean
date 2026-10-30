import Papers.PODC2013.ParetoOptimalConsensus.Time1

/-!
# Uniform consensus: `∃correct(v)`, Lemmas 5, 6 and 13 (§5, Appendix C)

* `ExCorrect v r m` (`∃correct(v)`): some correct process knows `∃v` at time `m`;
  `KCorrect t r i m v` is `K_i ∃correct(v)`.
* **Lemma 5** (`lemma5`): in a uniform consensus protocol (`t < n`), `K_i ∃correct(v)` is a
  precondition for deciding `v`.
* **Lemma 6** (`lemma6`): for a live `i` that knows of `d` failures at `m`,
  `K_i ∃correct(v)` iff `K_i ∃v` and either (a) `m > 0` and `K_i ∃v` at `m - 1`, or (b) `⟨i, m⟩`
  has seen at least `t - d` nodes `⟨j, m - 1⟩` that know `∃v`. **As stated in the paper (without
  `K_i ∃v`), Lemma 6 is false when `d = t`** (then (b) holds vacuously): `lemma6_literal_false`.
* **Lemma 13** (`lemma13`): for `0 < t < n`, no process decides at time `0` in a uniform consensus
  protocol.

The number of failures known to `⟨i, m⟩` (Definition 3, `F⟨i, m⟩`) is `known r i m` (the
processes `p` with `⟨p, m⟩` guaranteed crashed at `⟨i, m⟩`); for `m > 0` and `i` alive these are
exactly the processes from which `i` received no message in round `m` (`guarCrashed_now_iff`).
-/

namespace Podc.ParetoOptimalConsensus

open Cslib Finset Podc.UnbeatableSetConsensus

variable {P : Type*} [Fintype P] {t : ℕ}

/-! ### Known failures -/

section Known

variable {r : Run P} {i : P} {m : ℕ}

omit [Fintype P] in
-- CSLib candidate: Cslib/Computability/Distributed/SyncCrash (full-information views)
/-- For `m > 0` and `i` alive at `m`, `⟨p, m⟩` is guaranteed crashed at `⟨i, m⟩` iff `i` did not
receive `p`'s message in round `m`. -/
lemma guarCrashed_now_iff (hal : r.Alive i (m + 1 - 1)) {p : P} (hm : 0 < m) :
    GuarCrashed r i m p m ↔ p ≠ i ∧ ¬ r.Deliv p i (m - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hal ⊢
  constructor
  · intro hg
    refine ⟨fun h => not_guarCrashed_of_alive (h ▸ hal) hg, fun hd => ?_⟩
    obtain ⟨h, s, hs, hseen, hne, hnd⟩ := hg
    rcases Nat.lt_or_ge s M with hlt | hge
    · exact hnd (deliv_of_alive_succ (hd.1.mono (by omega)) h)
    · obtain rfl : s = M := by omega
      obtain rfl := seen_same_time hseen
      exact hnd hd
  · rintro ⟨hne, hnd⟩
    exact ⟨i, M, Nat.lt_succ_self M, seen_self le_rfl, hne.symm, hnd⟩

omit [Fintype P] in
lemma guarCrashed_mono_seen {j : P} {s s' : ℕ} (hs : Seen r j s i s') (hss : s ≤ s') {p : P}
    (hg : GuarCrashed r j s p s) : GuarCrashed r i s' p s' := by
  obtain ⟨h, s₀, h1, h2, h3, h4⟩ := hg
  exact ⟨h, s₀, by omega, h2.trans hs, h3, h4⟩

open Classical in
-- CSLib candidate: Cslib/Computability/Distributed/SyncCrash (full-information views)
/-- The set of processes known by `⟨i, m⟩` to have crashed. -/
noncomputable def knownSet (r : Run P) (i : P) (m : ℕ) : Finset P :=
  univ.filter fun p => GuarCrashed r i m p m

lemma mem_knownSet {p : P} : p ∈ knownSet r i m ↔ GuarCrashed r i m p m := by
  classical simp [knownSet]

lemma known_eq_card : known r i m = (knownSet r i m).card := by
  classical unfold known knownSet; congr

lemma knownSet_mono_seen {j : P} {s s' : ℕ} (hs : Seen r j s i s') :
    knownSet r j s ⊆ knownSet r i s' := fun _ hp =>
  mem_knownSet.2 (guarCrashed_mono_seen hs hs.le (mem_knownSet.1 hp))

lemma known_mono_seen {j : P} {s s' : ℕ} (hs : Seen r j s i s') : known r j s ≤ known r i s' := by
  rw [known_eq_card, known_eq_card]; exact card_le_card (knownSet_mono_seen hs)

lemma known_mono {s s' : ℕ} (hss : s ≤ s') : known r i s ≤ known r i s' :=
  known_mono_seen (seen_self hss)

lemma knownSet_subset_faulty : knownSet r i m ⊆ r.faulty := by
  intro p hp
  rw [SyncCrash.Run.mem_faulty]
  by_contra hpf
  exact not_guarCrashed_of_alive (SyncCrash.Run.alive_of_not_faulty hpf m) (mem_knownSet.1 hp)

lemma known_le (hr : Adm t bin r) : known r i m ≤ t := by
  rw [known_eq_card]; exact (card_le_card knownSet_subset_faulty).trans hr.1.1

lemma known_eq_of_sameView {r' : Run P} (h : SameView r r' i m) : known r i m = known r' i m := by
  rw [known_eq_card, known_eq_card]
  congr 1; ext p; rw [mem_knownSet, mem_knownSet]; exact h.guarCrashed_iff

open Classical in
/-- The carriers of `v` for `⟨i, m⟩`: nodes `⟨j, m - 1⟩` seen by `⟨i, m⟩` that know `∃v`. -/
noncomputable def carrierSet (r : Run P) (i : P) (m v : ℕ) : Finset P :=
  univ.filter fun p => 0 < m ∧ Seen r p (m - 1) i m ∧ v ∈ vals r p (m - 1)

lemma mem_carrierSet {p : P} {v : ℕ} :
    p ∈ carrierSet r i m v ↔ 0 < m ∧ Seen r p (m - 1) i m ∧ v ∈ vals r p (m - 1) := by
  classical simp [carrierSet]

lemma carriers_eq_card {v : ℕ} : carriers r i m v = (carrierSet r i m v).card := by
  classical unfold carriers carrierSet; congr

lemma carriers_eq_of_sameView {r' : Run P} {v : ℕ} (h : SameView r r' i m) :
    carriers r i m v = carriers r' i m v := by
  rw [carriers_eq_card, carriers_eq_card]
  congr 1; ext p; rw [mem_carrierSet, mem_carrierSet]
  constructor
  · rintro ⟨h0, hs, hv⟩; exact ⟨h0, h.seen hs, (h.of_seen hs).vals_eq ▸ hv⟩
  · rintro ⟨h0, hs, hv⟩; exact ⟨h0, h.symm.seen hs, (h.symm.of_seen hs).vals_eq ▸ hv⟩

-- CSLib candidate: Cslib/Computability/Distributed/SyncCrash (full-information views)
/-- A hidden path at `m` gives `m` known failures at `m + 1`: the hidden nodes at the times
`ℓ < m` belong to distinct processes that crashed by round `m`. -/
lemma le_known_of_hiddenPath (hp : HiddenPath r i m) : m ≤ known r i (m + 1) := by
  classical
  obtain ⟨b, hb⟩ := hp
  have hinj : Set.InjOn b ↑(range m) := by
    intro ℓ hℓ ℓ' hℓ' he
    simp only [coe_range, Set.mem_Iio] at hℓ hℓ'
    exact (hb ℓ (by omega)).time_eq (he ▸ hb ℓ' (by omega)) (by omega) (by omega)
  have hsub : (range m).image b ⊆ knownSet r i (m + 1) := by
    intro p hp
    obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.1 hp
    rw [mem_range] at hℓ
    have hh := hb ℓ (by omega)
    obtain ⟨c, hc, hcle⟩ := hh.crash_le hℓ
    refine mem_knownSet.2 ⟨i, m, Nat.lt_succ_self m, seen_self le_rfl, (hh.ne (by omega)).symm,
      fun hd => ?_⟩
    have := hd.1 c hc; omega
  rw [known_eq_card]
  have := card_le_card hsub
  rwa [card_image_of_injOn hinj, card_range] at this

end Known

/-! ### `∃correct(v)` -/

/-- `∃correct(v)` at time `m`: some correct process knows `∃v`. -/
def ExCorrect (v : ℕ) (r : Run P) (m : ℕ) : Prop := ∃ c, ¬ r.Faulty c ∧ v ∈ vals r c m

/-- `K_i ∃correct(v)` at time `m`. -/
def KCorrect (t : ℕ) (r : Run P) (i : P) (m v : ℕ) : Prop :=
  Knows t bin r i m fun r' => ExCorrect v r' m

section KCorrect

variable {r r' : Run P} {i : P} {m v : ℕ}

lemma kCorrect_iff_of_sameView (h : SameView r r' i m) :
    KCorrect t r i m v ↔ KCorrect t r' i m v := by
  unfold KCorrect Knows
  exact ⟨fun hk r'' hr'' hsv hal => hk r'' hr'' (h.trans hsv) hal,
   fun hk r'' hr'' hsv hal => hk r'' hr'' (h.symm.trans hsv) hal⟩

/-- `K_i ∃correct(v)` is persistent. -/
lemma KCorrect.mono {m' : ℕ} (hk : KCorrect t r i m v) (hm : m ≤ m') : KCorrect t r i m' v := by
  unfold KCorrect Knows at *
  intro r'' hr'' hsv hal
  obtain ⟨c, hc, hcv⟩ := hk r'' hr'' (hsv.mono hm) (hal.mono hm)
  exact ⟨c, hc, vals_mono hm hcv⟩

/-- `K_j ∃correct(v)` at a node seen by a live node `⟨i, m'⟩` gives `K_i ∃correct(v)` there. -/
lemma KCorrect.of_seen {j : P} {s m' : ℕ} (hk : KCorrect t r j s v) (hs : Seen r j s i m') :
    KCorrect t r i m' v := by
  unfold KCorrect Knows at *
  intro r'' hr'' hsv hal
  have hs'' := hsv.seen hs
  obtain ⟨c, hc, hcv⟩ := hk r'' hr'' (hsv.of_seen hs) (hs''.alive hal)
  exact ⟨c, hc, vals_mono hs.le hcv⟩

lemma KCorrect.holds (hr : Adm t bin r) (hal : r.Alive i m) (hk : KCorrect t r i m v) :
    ExCorrect v r m := hk r hr (sameView_refl r i m) hal

lemma KCorrect.vals_mem (hr : Adm t bin r) (hal : r.Alive i m) (hk : KCorrect t r i m v)
    (hv : v ∈ bin) : v ∈ vals r i m := by
  by_contra hn
  set r' := replaceUnseen r i m (1 - v)
  have hr' : Adm t bin r' := by
    refine ⟨hr.1, fun p => ?_⟩
    simp only [r', replaceUnseen]; split_ifs
    · exact hr.2 p
    · exact one_sub_mem_bin hv
  obtain ⟨c, -, hcv⟩ := hk r' hr' (replaceUnseen_sameView r i m (1 - v)) hal
  obtain ⟨q, -, hq⟩ := UnbeatableSetConsensus.mem_vals.1 hcv
  simp only [r', replaceUnseen] at hq
  split_ifs at hq with hs
  · exact hn (UnbeatableSetConsensus.mem_vals.2 ⟨q, hs, hq⟩)
  · exact one_sub_ne hv hq

end KCorrect

/-! ### Uniform consensus -/

/-- A uniform consensus protocol solves consensus. -/
lemma uniform_toSet {k : ℕ} {D : Set ℕ} {Q : Protocol P}
    (h : SolvesUniformSetConsensus k t D Q) : SolvesSetConsensus k t D Q where
  decision := h.decision
  validity := h.validity
  agreement r hr := by
    refine le_trans (Set.encard_le_encard ?_) (h.agreement r hr)
    rintro v ⟨i, m, -, hv⟩; exact ⟨i, m, hv⟩

lemma uagree {D : Set ℕ} {Q : Protocol P} (hQ : SolvesUniformSetConsensus 1 t D Q) {r : Run P}
    (hr : Adm t D r) {i j : P} {m m' v w : ℕ} (hv : DecidesAt Q r i m v)
    (hw : DecidesAt Q r j m' w) : v = w :=
  Set.encard_le_one_iff.1 (by simpa using hQ.agreement r hr) v w
    (show v ∈ {v | ∃ i m, DecidesAt Q r i m v} from ⟨i, m, hv⟩)
    (show w ∈ {v | ∃ i m, DecidesAt Q r i m v} from ⟨j, m', hw⟩)

/-- **Unbeatability** for uniform consensus. -/
def UUnbeatable (t : ℕ) (P' : Protocol P) : Prop :=
  SolvesUniformSetConsensus 1 t bin P' ∧
    ∀ Q, SolvesUniformSetConsensus 1 t bin Q → Dominates t bin Q P' → Dominates t bin P' Q

/-! ### Lemma 5 -/

section Lemma5

variable {Q : Protocol P}

open Classical in
/-- From time `m` on, the processes that are faulty and alive at `m` crash silently. -/
noncomputable def silence (r : Run P) (m : ℕ) : Run P where
  input := r.input
  crash p := if r.Faulty p ∧ r.Alive p m then some (m + 1) else r.crash p
  reach p := if r.Faulty p ∧ r.Alive p m then ∅ else r.reach p

omit [Fintype P] in
lemma silence_faulty_iff {r : Run P} {m : ℕ} {p : P} : (silence r m).Faulty p ↔ r.Faulty p := by
  unfold SyncCrash.Run.Faulty silence; simp only
  split_ifs with h
  · simpa [SyncCrash.Run.Faulty] using h.1
  · rfl

omit [Fintype P] in
lemma silence_deliv_lt {r : Run P} {m s : ℕ} (hs : s < m) (q p : P) :
    (silence r m).Deliv q p s ↔ r.Deliv q p s := by
  by_cases h : r.Faulty q ∧ r.Alive q m
  · have h1 : (silence r m).crash q = some (m + 1) := by simp [silence, h]
    rw [deliv_of_crash_some h1]
    simp only [show s + 1 < m + 1 by omega, true_or, true_iff]
    exact deliv_of_alive_succ (h.2.mono (by omega)) p
  · have h1 : (silence r m).crash q = r.crash q := by simp [silence, h]
    have h2 : (silence r m).reach q = r.reach q := by simp [silence, h]
    rw [deliv_iff, deliv_iff]; simp only [SyncCrash.Run.Alive, h1, h2]

omit [Fintype P] in
/-- After time `m`, only correct processes send messages. -/
lemma silence_deliv_ge {r : Run P} {m s : ℕ} (hs : m ≤ s) {q p : P}
    (hd : (silence r m).Deliv q p s) : ¬ r.Faulty q := by
  intro hf
  by_cases ha : r.Alive q m
  · have h1 : (silence r m).crash q = some (m + 1) := by simp [silence, hf, ha]
    rw [deliv_of_crash_some h1] at hd
    rcases hd with h | ⟨-, h⟩
    · omega
    · simp [silence, hf, ha] at h
  · have h1 : (silence r m).crash q = r.crash q := by simp [silence, ha]
    obtain ⟨c, hc, hcm⟩ : ∃ c, r.crash q = some c ∧ c ≤ m := by
      by_contra hn; push Not at hn; exact ha fun c hc => hn c hc
    have := hd.1 c (h1.trans hc); omega

/-- **Lemma 5.** In a protocol solving uniform consensus (`t < n`), `K_i ∃correct(v)` is a
precondition for `i` deciding `v`. -/
theorem lemma5 (ht : t < Fintype.card P) (hQ : SolvesUniformSetConsensus 1 t bin Q) {r : Run P}
    (_hr : Adm t bin r) {i : P} {m v : ℕ} (hd : DecidesAt Q r i m v) : KCorrect t r i m v := by
  intro r' hr' hsv hal
  by_contra hne
  set β := silence r' m
  have hβ : Adm t bin β := by
    refine ⟨⟨le_trans (card_le_card fun p hp => ?_) hr'.1.1, fun p c hc => ?_⟩, hr'.2⟩
    · rw [SyncCrash.Run.mem_faulty] at hp ⊢; exact silence_faulty_iff.1 hp
    · simp only [β, silence] at hc; split_ifs at hc
      · cases hc; omega
      · exact hr'.1.2 p c hc
  have hsvβ : ∀ x, SameView r' β x m :=
    sameView_of_prefix (fun _ => rfl) (fun s hs w q => (silence_deliv_lt hs w q).symm)
  -- correct processes never learn `v` in `β`
  have hnv : ∀ s, m ≤ s → ∀ c, ¬ β.Faulty c → v ∉ vals β c s := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
      intro c hc hcv
      rw [← (hsvβ c).vals_eq] at hcv
      exact hne ⟨c, silence_faulty_iff.not.1 hc, hcv⟩
    | succ s hs ih =>
      intro c hc hcv
      rcases mem_vals_succ.1 hcv with h | ⟨q, hq, h⟩
      · exact ih c hc h
      · exact ih q (silence_faulty_iff.not.2 (silence_deliv_ge hs hq.2)) h
  obtain ⟨c, hc⟩ := hβ.1.exists_correct ht
  obtain ⟨mc, u, hu⟩ := hQ.decision β hβ c hc
  have huv : u ≠ v := by
    rintro rfl
    have := dec_mem_vals' (uniform_toSet hQ) hβ hu
    exact hnv (max mc m) (le_max_right _ _) c hc (vals_mono (le_max_left _ _) this)
  have halβ : β.Alive i m := fun c' hc' => by
    simp only [β, silence] at hc'
    split_ifs at hc' with h
    · cases hc'; omega
    · exact hal c' hc'
  have hdi : DecidesAt Q β i m v :=
    ((hsv.trans (hsvβ i)).decidesAt_iff Q le_rfl ⟨fun _ => halβ, fun _ => hd.1⟩).1 hd
  exact huv (uagree hQ hβ hu hdi)

end Lemma5

/-! ### Lemma 6 -/

section Lemma6

variable {r : Run P} {i : P} {m v : ℕ}

/-- **Lemma 6** (with the implicit `K_i ∃v`). Let `t < n` and let `i` be alive at `m`, knowing of
`d = known r i m` failures. Then `K_i ∃correct(v)` holds iff `K_i ∃v` and (a) `m > 0` and `K_i ∃v`
held at `m - 1`, or (b) `⟨i, m⟩` has seen at least `t - d` nodes `⟨j, m - 1⟩` with `K_j ∃v`. -/
theorem lemma6 (ht : t < Fintype.card P) (hr : Adm t bin r) (hal : r.Alive i m) (hv : v ∈ bin) :
    KCorrect t r i m v ↔ v ∈ vals r i m ∧
      ((0 < m ∧ v ∈ vals r i (m - 1)) ∨ t - known r i m ≤ carriers r i m v) := by
  classical
  constructor
  · intro hk
    refine ⟨hk.vals_mem hr hal hv, ?_⟩
    by_contra hn
    push Not at hn
    obtain ⟨ha, hb⟩ := hn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- time `0`: `i` crashes in round 1, nobody else has `v`
      have ht0 : 0 < t := by
        have : carriers r i 0 v = 0 := by
          rw [carriers_eq_card, card_eq_zero, eq_empty_iff_forall_notMem]
          intro p hp; exact absurd (mem_carrierSet.1 hp).1 (lt_irrefl 0)
        omega
      set r' : Run P := ⟨fun p => if p = i then r.input i else 1 - v,
        fun p => if p = i then some 1 else none, fun _ => ∅⟩
      have hr' : Adm t bin r' := by
        refine ⟨⟨?_, fun p c hc => ?_⟩, fun p => ?_⟩
        · have : r'.faulty ⊆ {i} := by
            intro p hp
            simp only [SyncCrash.Run.mem_faulty, SyncCrash.Run.Faulty, r'] at hp
            simp only [mem_singleton]; by_contra h; simp [h] at hp
          exact (card_le_card this).trans (by rw [card_singleton]; omega)
        · simp only [r'] at hc; split_ifs at hc <;> cases hc; omega
        · simp only [r']; split_ifs
          · exact hr.2 i
          · exact one_sub_mem_bin hv
      obtain ⟨c, hc, hcv⟩ := hk r' hr' (show r.input i = r'.input i by simp [r'])
        (fun c hc => by simp only [r'] at hc; split_ifs at hc <;> simp_all <;> omega)
      have hci : c ≠ i := by rintro rfl; exact hc (by simp [SyncCrash.Run.Faulty, r'])
      rw [vals_zero, mem_singleton] at hcv
      simp only [r', hci, ite_false] at hcv
      exact one_sub_ne hv hcv.symm
    -- time `m = M + 1`: the carriers crash in round `m` reaching only `i`, `i` crashes in round
    -- `m + 1` sending nothing, every other process not known to have crashed is correct
    obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at ha hb
    have ha' : v ∉ vals r i M := ha (Nat.succ_pos M)
    set S := carrierSet r i (M + 1) v
    set Kn := knownSet r i (M + 1)
    have hSi : i ∉ S := by
      intro h; exact ha' (by simpa using (mem_carrierSet.1 h).2.2)
    have hKi : i ∉ Kn := fun h => not_guarCrashed_of_alive hal (mem_knownSet.1 h)
    have hSK : ∀ p ∈ S, p ∉ Kn := by
      intro p hp hpK
      have h := (mem_carrierSet.1 hp).2.1
      simp only [Nat.add_sub_cancel] at h
      exact not_guarCrashed_of_seen_pred (h.alive hal) h (mem_knownSet.1 hpK)
    have hKd : ∀ p, p ≠ i → (p ∈ Kn ↔ ¬ r.Deliv p i M) := by
      intro p hp
      rw [mem_knownSet, guarCrashed_now_iff (by simpa using hal) (Nat.succ_pos M)]
      simp [hp]
    set r' : Run P :=
      { input := r.input
        crash := fun p => if p = i then some (M + 2) else if p ∈ S then some (M + 1)
          else if p ∈ Kn then r.crash p else none
        reach := fun p => if p = i then ∅ else if p ∈ S then {i}
          else if p ∈ Kn ∧ r.crash p = some (M + 1) then ∅ else r.reach p }
    have hci : r'.crash i = some (M + 2) := by simp [r']
    have hcS : ∀ p ∈ S, r'.crash p = some (M + 1) := fun p hp => by
      simp [r', hp, show p ≠ i from fun h => hSi (h ▸ hp)]
    have hcK : ∀ p ∈ Kn, r'.crash p = r.crash p := fun p hp => by
      simp [r', hp, show p ≠ i from fun h => hKi (h ▸ hp)]
      intro h; exact absurd hp (hSK p h)
    have hcO : ∀ p, p ≠ i → p ∉ S → p ∉ Kn → r'.crash p = none := fun p h1 h2 h3 => by
      simp [r', h1, h2, h3]
    -- processes outside `Kn` reached `i` in round `m`
    have hdO : ∀ p, p ≠ i → p ∉ Kn → r.Deliv p i M := fun p h1 h2 => by
      by_contra h; exact h2 ((hKd p h1).2 h)
    have hS_alive : ∀ p ∈ S, r.Alive p M := by
      intro p hp
      have h := (mem_carrierSet.1 hp).2.1; simp only [Nat.add_sub_cancel] at h
      exact h.alive hal
    -- rounds `≤ M` are unchanged
    have hlt : ∀ s < M, ∀ q p, r'.Deliv q p s ↔ r.Deliv q p s := by
      intro s hs q p
      by_cases hqi : q = i
      · subst hqi
        rw [deliv_of_crash_some hci]
        simp only [show s + 1 < M + 2 by omega, true_or, true_iff]
        exact deliv_of_alive_succ (hal.mono (by omega)) p
      by_cases hqS : q ∈ S
      · rw [deliv_of_crash_some (hcS q hqS)]
        simp only [show s + 1 < M + 1 by omega, true_or, true_iff]
        exact deliv_of_alive_succ ((hS_alive q hqS).mono (by omega)) p
      by_cases hqK : q ∈ Kn
      · rw [deliv_iff, deliv_iff]
        simp only [SyncCrash.Run.Alive, hcK q hqK]
        have hreach : r'.reach q = if r.crash q = some (M + 1) then ∅ else r.reach q := by
          simp [r', hqi, hqS, hqK]
        rw [hreach]
        split_ifs with hc
        · rw [hc]; simp only [Option.some.injEq]; constructor <;> rintro ⟨h1, h2⟩
          · exact ⟨h1, fun ⟨h3, _⟩ => by omega⟩
          · exact ⟨h1, fun ⟨h3, _⟩ => by omega⟩
        · rfl
      · simp only [deliv_of_crash_none (hcO q hqi hqS hqK), true_iff]
        exact deliv_of_alive_succ ((hdO q hqi hqK).1.mono (by omega)) p
    -- round `m` to `i` is unchanged
    have hlast : ∀ q, q ≠ i → (r'.Deliv q i M ↔ r.Deliv q i M) := by
      intro q hqi
      by_cases hqS : q ∈ S
      · rw [deliv_of_crash_some (hcS q hqS)]
        have : r'.reach q = {i} := by simp [r', hqi, hqS]
        simp only [this, lt_irrefl, Set.mem_singleton_iff, and_true, false_or, true_iff]
        have h := (mem_carrierSet.1 hqS).2.1; simp only [Nat.add_sub_cancel] at h
        exact Seen.deliv_of_succ h hqi
      by_cases hqK : q ∈ Kn
      · rw [iff_false_intro ((hKd q hqi).1 hqK), iff_false]
        rw [deliv_iff]
        simp only [SyncCrash.Run.Alive, hcK q hqK]
        have hreach : r'.reach q = if r.crash q = some (M + 1) then ∅ else r.reach q := by
          simp [r', hqi, hqS, hqK]
        rw [hreach]
        have hnd := (hKd q hqi).1 hqK
        rw [deliv_iff] at hnd
        split_ifs with hc
        · rintro ⟨-, h⟩; exact h ⟨hc, Set.notMem_empty i⟩
        · exact hnd
      · simp only [deliv_of_crash_none (hcO q hqi hqS hqK), true_iff]
        exact hdO q hqi hqK
    have hsv : SameView r r' i (M + 1) := by
      refine sameView_of_agree (fun _ _ => rfl) (fun h s hs w hw => ?_)
      rcases Nat.lt_or_ge s M with hsM | hsM
      · exact (hlt s hsM w h).symm
      · obtain rfl : s = M := by have := hs.le; omega
        obtain rfl := seen_same_time hs
        exact (hlast w hw).symm
    have hsvM : ∀ x, SameView r r' x M :=
      sameView_of_prefix (fun _ => rfl) (fun s hs w q => (hlt s hs w q).symm)
    have hr' : Adm t bin r' := by
      refine ⟨⟨?_, fun p c hc => ?_⟩, hr.2⟩
      · have hsub : r'.faulty ⊆ insert i (S ∪ Kn) := by
          intro p hp
          rw [SyncCrash.Run.mem_faulty] at hp
          rw [mem_insert, mem_union]
          by_contra h; push Not at h
          exact hp (hcO p h.1 h.2.1 h.2.2)
        have hdisj : Disjoint S Kn := disjoint_left.2 hSK
        have := card_le_card hsub
        rw [card_insert_of_notMem (by simp [hSi, hKi]), card_union_of_disjoint hdisj] at this
        rw [← carriers_eq_card, ← known_eq_card] at this
        have := known_le (i := i) (m := M + 1) hr
        omega
      · by_cases hpi : p = i
        · rw [hpi, hci] at hc; cases hc; omega
        by_cases hpS : p ∈ S
        · rw [hcS p hpS] at hc; cases hc; omega
        by_cases hpK : p ∈ Kn
        · rw [hcK p hpK] at hc; exact hr.1.2 p c hc
        · rw [hcO p hpi hpS hpK] at hc; cases hc
    obtain ⟨c, hc, hcv⟩ := hk r' hr' hsv (fun c hc => by rw [hci] at hc; cases hc; omega)
    -- `c` is none of `i`, `S`, `Kn`, hence saw `i`'s view at `M` and is not a carrier
    have hcI : c ≠ i := by rintro rfl; exact hc (by simp [SyncCrash.Run.Faulty, hci])
    have hcS' : c ∉ S := fun h => hc (by simp [SyncCrash.Run.Faulty, hcS c h])
    have hcK' : c ∉ Kn := by
      intro h
      apply hc
      rw [SyncCrash.Run.Faulty, hcK c h]
      exact SyncCrash.Run.mem_faulty.1 (knownSet_subset_faulty h)
    have hnot : ∀ q, q ≠ i → q ∉ S → q ∉ Kn → v ∉ vals r q M := by
      intro q h1 h2 h3 hq
      exact h2 (mem_carrierSet.2 ⟨Nat.succ_pos M, by
        simpa using seen_of_deliv h1 (hdO q h1 h3), by simpa using hq⟩)
    rcases mem_vals_succ.1 hcv with h | ⟨q, hq, h⟩
    · rw [← (hsvM c).vals_eq] at h; exact hnot c hcI hcS' hcK' h
    · rw [← (hsvM q).vals_eq] at h
      have hd := hq.2
      by_cases hqi : q = i
      · subst hqi; exact ha' h
      by_cases hqS : q ∈ S
      · rw [deliv_of_crash_some (hcS q hqS)] at hd
        have : r'.reach q = {i} := by simp [r', hqi, hqS]
        rw [this] at hd
        rcases hd with h' | ⟨-, h'⟩
        · omega
        · exact hcI h'
      by_cases hqK : q ∈ Kn
      · have hnd := (hKd q hqi).1 hqK
        rw [deliv_iff] at hd hnd
        simp only [SyncCrash.Run.Alive, hcK q hqK] at hd
        have hreach : r'.reach q = if r.crash q = some (M + 1) then ∅ else r.reach q := by
          simp [r', hqi, hqS, hqK]
        rw [hreach] at hd
        split_ifs at hd with hcq
        · -- crashed in round `m` and reached nobody
          exact hd.2 ⟨hcq, Set.notMem_empty c⟩
        · apply hnd
          refine ⟨hd.1, fun ⟨h1, _⟩ => hcq h1⟩
      · exact hnot q hqi hqS hqK h
  · rintro ⟨hvi, hab⟩ r' hr' hsv hal'
    have hvi' : v ∈ vals r' i m := hsv.vals_eq ▸ hvi
    rcases hab with ⟨hm, ha⟩ | hb
    · -- (a): `i` sent `v` to everybody in round `m`
      obtain ⟨c, hc⟩ := hr'.1.exists_correct ht
      refine ⟨c, hc, ?_⟩
      by_cases hci : c = i
      · subst hci; exact hvi'
      obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at ha
      rw [(hsv.mono (Nat.le_succ M)).vals_eq] at ha
      exact vals_subset_succ_of_comm ⟨Ne.symm hci, deliv_of_alive_succ hal' c⟩ ha
    · -- (b): among `i` and the carriers some process is correct
      by_cases ha : 0 < m ∧ v ∈ vals r i (m - 1)
      · obtain ⟨hm, ha⟩ := ha
        obtain ⟨c, hc⟩ := hr'.1.exists_correct ht
        refine ⟨c, hc, ?_⟩
        by_cases hci : c = i
        · subst hci; exact hvi'
        obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at ha
        rw [(hsv.mono (Nat.le_succ M)).vals_eq] at ha
        exact vals_subset_succ_of_comm ⟨Ne.symm hci, deliv_of_alive_succ hal' c⟩ ha
      rw [carriers_eq_of_sameView hsv, known_eq_of_sameView hsv] at hb
      by_contra hne
      have hSf : ∀ p ∈ carrierSet r' i m v, r'.Faulty p := by
        intro p hp
        obtain ⟨h0, hs, hpv⟩ := mem_carrierSet.1 hp
        by_contra hpf
        exact hne ⟨p, hpf, vals_mono (Nat.sub_le m 1) hpv⟩
      have hif : r'.Faulty i := fun hif => hne ⟨i, not_faulty_iff.2 hif, hvi'⟩
      have hSi : i ∉ carrierSet r' i m v := by
        intro h
        obtain ⟨h0, -, hpv⟩ := mem_carrierSet.1 h
        exact ha ⟨h0, (hsv.mono (Nat.sub_le m 1)).vals_eq ▸ hpv⟩
      have hKi : i ∉ knownSet r' i m := fun h => not_guarCrashed_of_alive hal' (mem_knownSet.1 h)
      have hdisj : Disjoint (carrierSet r' i m v) (knownSet r' i m) := by
        rw [disjoint_left]; intro p hp hpK
        obtain ⟨h0, hs, -⟩ := mem_carrierSet.1 hp
        obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at hs
        exact not_guarCrashed_of_seen_pred (hs.alive hal') hs (mem_knownSet.1 hpK)
      have hsub : insert i (carrierSet r' i m v ∪ knownSet r' i m) ⊆ r'.faulty := by
        intro p hp
        rw [SyncCrash.Run.mem_faulty]
        rcases mem_insert.1 hp with rfl | hp
        · exact hif
        rcases mem_union.1 hp with hp | hp
        · exact hSf p hp
        · exact SyncCrash.Run.mem_faulty.1 (knownSet_subset_faulty hp)
      have := (card_le_card hsub).trans hr'.1.1
      rw [card_insert_of_notMem (by simp [hSi, hKi]), card_union_of_disjoint hdisj,
        ← carriers_eq_card, ← known_eq_card] at this
      have := known_le (i := i) (m := m) hr'
      omega

/-- **Lemma 6 as stated is false**: without `K_i ∃v`, condition (b) holds vacuously when `i` knows
of `d = t` failures. Here `n = 3`, `t = 1`: process `2` crashes in round 1 sending nothing, all
inputs are `1`; at time `1`, process `0` knows of `d = 1` failure, so (b) ("`t - d = 0` carriers")
holds, but `K_0 ∃correct(0)` is false (nobody has `0`). -/
theorem lemma6_literal_false :
    ∃ r : Run (Fin 3), Adm 1 bin r ∧ r.Alive 0 1 ∧
      1 - known r 0 1 ≤ carriers r 0 1 0 ∧ ¬ KCorrect 1 r 0 1 0 := by
  classical
  set r : Run (Fin 3) := ⟨fun _ => 1, fun p => if p = 2 then some 1 else none, fun _ => ∅⟩
  have hr : Adm 1 bin r := by
    refine ⟨⟨?_, fun p c hc => ?_⟩, fun _ => one_mem_bin⟩
    · have : r.faulty ⊆ {2} := by
        intro p hp
        simp only [SyncCrash.Run.mem_faulty, SyncCrash.Run.Faulty, r] at hp
        simp only [mem_singleton]; by_contra h; simp [h] at hp
      exact (card_le_card this).trans (by simp)
    · simp only [r] at hc; split_ifs at hc <;> cases hc; omega
  have hal : r.Alive 0 1 := fun c hc => by simp [r] at hc
  refine ⟨r, hr, hal, ?_, fun hk => ?_⟩
  · have : 1 ≤ known r 0 1 := by
      rw [known_eq_card]
      refine card_pos.2 ⟨2, mem_knownSet.2 ⟨0, 0, Nat.zero_lt_one, seen_self le_rfl, by decide, ?_⟩⟩
      rw [deliv_of_crash_some (show r.crash 2 = some 1 by simp [r])]; simp [r]
    omega
  · obtain ⟨c, -, hc⟩ := hk.holds hr hal
    obtain ⟨_, -, h⟩ := mem_vals.1 hc
    simp [r] at h

end Lemma6

/-! ### Lemma 13 -/

/-- **Lemma 13** (no decision at time 0). If `0 < t < n`, no process decides at time `0` in a
protocol solving uniform consensus. -/
theorem lemma13 (ht0 : 0 < t) (ht : t < Fintype.card P) {Q : Protocol P}
    (hQ : SolvesUniformSetConsensus 1 t bin Q) {r : Run P} (hr : Adm t bin r) (i : P) (v : ℕ) :
    ¬ DecidesAt Q r i 0 v := by
  intro hd
  have hv : v ∈ bin := mem_bin_of_mem_vals hr (dec_mem_vals' (uniform_toSet hQ) hr hd)
  have hk := lemma5 ht hQ hr hd
  rw [lemma6 ht hr hd.1 hv] at hk
  obtain ⟨-, h | h⟩ := hk
  · exact lt_irrefl 0 h.1
  · have : carriers r i 0 v = 0 := by
      rw [carriers_eq_card, card_eq_zero, eq_empty_iff_forall_notMem]
      intro p hp; exact absurd (mem_carrierSet.1 hp).1 (lt_irrefl 0)
    have h0 : known r i 0 = 0 := by
      rw [known_eq_card, card_eq_zero, eq_empty_iff_forall_notMem]
      intro p hp; obtain ⟨_, s, hs, -⟩ := mem_knownSet.1 hp; omega
    omega

end Podc.ParetoOptimalConsensus
