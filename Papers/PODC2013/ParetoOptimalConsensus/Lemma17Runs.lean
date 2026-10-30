import Papers.PODC2013.ParetoOptimalConsensus.Lemma16

/-!
# The runs of the proof of Lemma 17

Setting: a run `r`, a process `i` alive at `M + 1` that has not seen `0`, and a hidden path
`b 0, …, b (M + 1)` w.r.t. `⟨i, M + 1⟩`. The base run `r₀` is the chain run (Lemma 9) along
`b 0, …, b M` carrying the value `0` (`z = b M` knows `∃0` at time `M`, and it is the first time
it does). All runs of the proof of Lemma 17 are obtained from `r₀` by changing the crash rounds and
reach sets of `z = b M` and of `i`, the reach set of `z' = b (M - 1)` in round `M`, and possibly
`i`'s input, while making every process not known by `⟨i, M + 1⟩` to have crashed (other than
`i`) correct, and silencing the known ones in round `M + 1` (`l17Run`).
-/

namespace Podc.ParetoOptimalConsensus

open Cslib Finset Podc.UnbeatableSetConsensus

variable {P : Type*} [Fintype P] {t : ℕ}

section L17

variable {r : Run P} {i : P} {M : ℕ} {b : ℕ → P}

/-- The base run: the chain run along the hidden path, carrying `0`. -/
noncomputable def l17Base (r : Run P) (i : P) (M : ℕ) (b : ℕ → P) : Run P :=
  chainRun r i M (fun ℓ (_ : Unit) => b ℓ) (fun _ => 0)

/-- The processes known by `⟨i, M + 1⟩` (in the base run) to have crashed. -/
noncomputable def l17Kn (r : Run P) (i : P) (M : ℕ) (b : ℕ → P) : Finset P :=
  knownSet (l17Base r i M b) i (M + 1)

open Classical in
/-- The run family of Lemma 17. -/
noncomputable def l17Run (r : Run P) (i : P) (M : ℕ) (b : ℕ → P) (cz : Option ℕ) (Rz : Set P)
    (ci : Option ℕ) (Ri : Set P) (Rz' : Set P) (ini : ℕ) : Run P where
  input p := if p = i then ini else (l17Base r i M b).input p
  crash p := if p = b M then cz else if p = i then ci
    else if p ∈ l17Kn r i M b then (l17Base r i M b).crash p else none
  reach p := if p = b M then Rz else if p = i then Ri else if p = b (M - 1) then Rz'
    else if (l17Base r i M b).crash p = some (M + 1) then ∅ else (l17Base r i M b).reach p

variable (hb : ∀ ℓ ≤ M + 1, Hidden r i (M + 1) (b ℓ) ℓ) (hal : r.Alive i (M + 1))
include hb

lemma l17_chainHyp : ChainHyp r i (M + 1) M (fun ℓ (_ : Unit) => b ℓ) :=
  ⟨Nat.le_succ M, fun _ _ x y _ => Subsingleton.elim x y, fun ℓ hℓ _ => hb ℓ (by omega)⟩

lemma l17_base_sameView : SameView r (l17Base r i M b) i (M + 1) :=
  (l17_chainHyp hb).sameView

lemma l17_base_crash_b {ℓ : ℕ} (hℓ : ℓ ≤ M) : (l17Base r i M b).crash (b ℓ) = some (ℓ + 1) :=
  (l17_chainHyp hb).crash_w hℓ ()

lemma l17_base_deliv_b {ℓ s : ℕ} (hℓ : ℓ ≤ M) (q : P) :
    (l17Base r i M b).Deliv (b ℓ) q s ↔ s < ℓ ∨ (s = ℓ ∧ ℓ < M ∧ q = b (ℓ + 1)) :=
  (l17_chainHyp hb).deliv_w hℓ () q

lemma l17_b_ne_i {ℓ : ℕ} (hℓ : ℓ ≤ M + 1) : b ℓ ≠ i := (hb ℓ hℓ).ne (by omega)

include hal

lemma l17_base_alive_i : (l17Base r i M b).Alive i (M + 1) :=
  ((l17_chainHyp hb).alive_iff_of_seen (seen_self le_rfl) (Nat.le_succ M)).2 hal

lemma l17_mem_Kn {p : P} : p ∈ l17Kn r i M b ↔ p ≠ i ∧ ¬ (l17Base r i M b).Deliv p i M := by
  unfold l17Kn
  rw [mem_knownSet, guarCrashed_now_iff (by simpa using l17_base_alive_i hb hal)
    (Nat.succ_pos M)]
  simp

lemma l17_i_notMem : i ∉ l17Kn r i M b := fun h => ((l17_mem_Kn hb hal).1 h).1 rfl

lemma l17_b_mem {ℓ : ℕ} (hℓ : ℓ ≤ M) : b ℓ ∈ l17Kn r i M b := by
  rw [l17_mem_Kn hb hal, l17_base_deliv_b hb hℓ]
  refine ⟨l17_b_ne_i hb (by omega), ?_⟩
  omega

lemma l17_crash_le_of_mem {p : P} (hp : p ∈ l17Kn r i M b) :
    ∃ c, (l17Base r i M b).crash p = some c ∧ c ≤ M + 1 := by
  have hnd := ((l17_mem_Kn hb hal).1 hp).2
  cases hc : (l17Base r i M b).crash p with
  | none => exact absurd (deliv_of_crash_none hc i M) hnd
  | some c =>
    refine ⟨c, rfl, ?_⟩
    rw [deliv_of_crash_some hc] at hnd
    omega

lemma l17_alive_of_notMem {p : P} (hp : p ∉ l17Kn r i M b) (hpi : p ≠ i) :
    (l17Base r i M b).Deliv p i M := by
  by_contra h; exact hp ((l17_mem_Kn hb hal).2 ⟨hpi, h⟩)

/-! #### Crash data of the family -/

section Family

variable {cz : Option ℕ} {Rz : Set P} {ci : Option ℕ} {Ri : Set P} {Rz' : Set P} {ini : ℕ}

omit hb hal in
lemma l17_crash_z : (l17Run r i M b cz Rz ci Ri Rz' ini).crash (b M) = cz := by
  simp [l17Run]

omit hal in
lemma l17_crash_i : (l17Run r i M b cz Rz ci Ri Rz' ini).crash i = ci := by
  simp [l17Run, Ne.symm (l17_b_ne_i hb (Nat.le_succ M))]

lemma l17_crash_K {p : P} (hp : p ∈ l17Kn r i M b) (hpz : p ≠ b M) :
    (l17Run r i M b cz Rz ci Ri Rz' ini).crash p = (l17Base r i M b).crash p := by
  have hpi : p ≠ i := fun h => l17_i_notMem hb hal (h ▸ hp)
  simp [l17Run, hpz, hpi, hp]

lemma l17_crash_O {p : P} (hp : p ∉ l17Kn r i M b) (hpi : p ≠ i) :
    (l17Run r i M b cz Rz ci Ri Rz' ini).crash p = none := by
  have hpz : p ≠ b M := fun h => hp (h ▸ l17_b_mem hb hal le_rfl)
  simp [l17Run, hpz, hpi, hp]

omit hb hal in
lemma l17_reach_z : (l17Run r i M b cz Rz ci Ri Rz' ini).reach (b M) = Rz := by simp [l17Run]

omit hal in
lemma l17_reach_i : (l17Run r i M b cz Rz ci Ri Rz' ini).reach i = Ri := by
  simp [l17Run, Ne.symm (l17_b_ne_i hb (Nat.le_succ M))]

/-- Every known process other than `z` is silent in round `M + 1`. -/
lemma l17_silent {p : P} (hp : p ∈ l17Kn r i M b) (hpz : p ≠ b M) (q : P) :
    ¬ (l17Run r i M b cz Rz ci Ri Rz' ini).Deliv p q M := by
  intro hd
  obtain ⟨c, hc, hcle⟩ := l17_crash_le_of_mem hb hal hp
  have hc' := (l17_crash_K hb hal hp hpz (cz := cz) (Rz := Rz) (ci := ci) (Ri := Ri)
    (Rz' := Rz') (ini := ini)).trans hc
  rw [deliv_of_crash_some hc'] at hd
  rcases hd with h | ⟨rfl, hq⟩
  · omega
  · -- `p` crashes in round `M + 1`, so it is not `b (M - 1)` and its reach set is empty
    have hpi : p ≠ i := fun h => l17_i_notMem hb hal (h ▸ hp)
    have hpz' : p ≠ b (M - 1) := by
      intro hpe
      rcases Nat.eq_zero_or_pos M with hM | hM
      · exact hpz (by rw [hpe, hM])
      · rw [hpe, l17_base_crash_b hb (by omega), Option.some.injEq] at hc; omega
    simp [l17Run, hpz, hpi, hpz', hc] at hq

/-- The faulty processes: at most `i` and the known ones. -/
lemma l17_faulty_subset {p : P} (hp : (l17Run r i M b cz Rz ci Ri Rz' ini).Faulty p) :
    p = i ∨ p ∈ l17Kn r i M b := by
  by_contra h; push Not at h
  exact hp (l17_crash_O hb hal h.2 h.1)

/-- Admissibility from a bound on the faulty processes. -/
lemma l17_adm (hr : Adm t bin r) (hcz : ∀ c, cz = some c → 1 ≤ c) (hci : ∀ c, ci = some c → 1 ≤ c)
    (hini : ini ∈ bin) (hcard : (l17Run r i M b cz Rz ci Ri Rz' ini).faulty.card ≤ t) :
    Adm t bin (l17Run r i M b cz Rz ci Ri Rz' ini) := by
  refine ⟨⟨hcard, fun p c hc => ?_⟩, fun p => ?_⟩
  · by_cases hpz : p = b M
    · rw [hpz, l17_crash_z] at hc; exact hcz c hc
    by_cases hpi : p = i
    · rw [hpi, l17_crash_i hb] at hc; exact hci c hc
    by_cases hpK : p ∈ l17Kn r i M b
    · rw [l17_crash_K hb hal hpK hpz] at hc; exact (l17_chainHyp hb).crash_pos hr hc
    · rw [l17_crash_O hb hal hpK hpi] at hc; cases hc
  · simp only [l17Run]; split_ifs
    · exact hini
    · exact ChainHyp.input_mem (x := i) (L := M) hr (fun _ => zero_mem_bin) p

/-- The first `M` rounds are those of the base run, except possibly the message of `b (M - 1)` to
`i` in round `M`. -/
lemma l17_deliv_lt (hcz : ∀ c, cz = some c → M + 1 ≤ c) (hci : ∀ c, ci = some c → M + 1 ≤ c)
    (hRz' : ∀ q, q ≠ i → (q ∈ Rz' ↔ q ∈ (l17Base r i M b).reach (b (M - 1)))) {s : ℕ} (hs : s < M)
    (w q : P) (hex : ¬ (w = b (M - 1) ∧ q = i ∧ s + 1 = M)) :
    (l17Run r i M b cz Rz ci Ri Rz' ini).Deliv w q s ↔ (l17Base r i M b).Deliv w q s := by
  set x := l17Run r i M b cz Rz ci Ri Rz' ini
  set r₀ := l17Base r i M b
  have hfull : ∀ {c : Option ℕ}, (∀ c', c = some c' → M + 1 ≤ c') → ∀ (y : Run P) (w' : P),
      y.crash w' = c → y.Deliv w' q s := by
    intro c hc y w' hy
    cases hcc : c with
    | none => exact deliv_of_crash_none (hy.trans hcc) q s
    | some c' =>
      rw [deliv_of_crash_some (hy.trans hcc)]; left; have := hc c' hcc; omega
  by_cases hwz : w = b M
  · subst hwz
    exact iff_of_true (hfull hcz x _ l17_crash_z)
      (hfull (c := some (M + 1)) (fun c h => by cases h; omega) r₀ _
        (l17_base_crash_b hb le_rfl))
  by_cases hwi : w = i
  · subst hwi
    exact iff_of_true (hfull hci x _ (l17_crash_i hb))
      (deliv_of_alive_succ ((l17_base_alive_i hb hal).mono (by omega)) q)
  by_cases hwK : w ∈ l17Kn r i M b
  · refine deliv_congr (l17_crash_K hb hal hwK hwz) fun hc => ?_
    rw [l17_crash_K hb hal hwK hwz] at hc
    simp only [x, l17Run, hwz, hwi, ite_false]
    split_ifs with h1 h2
    · subst h1
      by_cases hqi : q = i
      · subst hqi
        -- `b (M - 1)` crashes in round `M`, so `s + 1 = M`
        have hM : 0 < M := by
          rcases Nat.eq_zero_or_pos M with h | h
          · exact absurd (by rw [h]) hwz
          · exact h
        rw [l17_base_crash_b hb (by omega)] at hc
        cases hc
        exact absurd ⟨rfl, rfl, by omega⟩ hex
      · exact hRz' q hqi
    · rw [h2] at hc; cases hc; omega
    · rfl
  · exact iff_of_true (deliv_of_crash_none (l17_crash_O hb hal hwK hwi) q s)
      (deliv_of_alive_succ ((l17_alive_of_notMem hb hal hwK hwi).1.mono (by omega)) q)

/-- Round `M + 1` into `i`, when `z` crashes in round `M + 1` without reaching `i`. -/
lemma l17_deliv_last (hcz : cz = some (M + 1)) (hRz : i ∉ Rz) (w : P) (hwi : w ≠ i) :
    (l17Run r i M b cz Rz ci Ri Rz' ini).Deliv w i M ↔ (l17Base r i M b).Deliv w i M := by
  by_cases hwz : w = b M
  · subst hwz
    refine iff_of_false ?_ ((l17_mem_Kn hb hal).1 (l17_b_mem hb hal le_rfl)).2
    rw [deliv_of_crash_some ((l17_crash_z).trans hcz), l17_reach_z]
    rintro (h | ⟨-, h⟩)
    · omega
    · exact hRz h
  by_cases hwK : w ∈ l17Kn r i M b
  · exact iff_of_false (l17_silent hb hal hwK hwz i) ((l17_mem_Kn hb hal).1 hwK).2
  · exact iff_of_true (deliv_of_crash_none (l17_crash_O hb hal hwK hwi) i M)
      (l17_alive_of_notMem hb hal hwK hwi)

/-- `z`'s view at `M` is that of the base run. -/
lemma l17_sameView_z (hcz : ∀ c, cz = some c → M + 1 ≤ c) (hci : ∀ c, ci = some c → M + 1 ≤ c)
    (hRz' : ∀ q, q ≠ i → (q ∈ Rz' ↔ q ∈ (l17Base r i M b).reach (b (M - 1))))
    (hini : M = 0 ∨ ini = (l17Base r i M b).input i) :
    SameView (l17Base r i M b) (l17Run r i M b cz Rz ci Ri Rz' ini) (b M) M := by
  have hzi := l17_b_ne_i hb (Nat.le_succ M)
  refine sameView_of_agree (fun q hq => ?_) (fun h s hs w _ => ?_)
  · by_cases hqi : q = i
    · subst hqi
      rcases hini with h0 | h0
      · subst h0; exact absurd (seen_same_time hq).symm hzi
      · simp [l17Run, h0]
    · simp [l17Run, hqi]
  · have hsM : s < M := by have := hs.le; omega
    refine (l17_deliv_lt hb hal hcz hci hRz' hsM w h ?_).symm
    rintro ⟨-, rfl, hsM'⟩
    rw [hsM'] at hs; exact hzi (seen_same_time hs).symm

omit hal in
/-- `z` knows `∃0` at `M` (in the base run), for the first time. -/
lemma l17_z_first (h0 : 0 ∉ vals r i (M + 1)) : FirstKnows (l17Base r i M b) (b M) M 0 := by
  have H := l17_chainHyp hb
  refine ⟨H.mem_vals le_rfl (), fun M' hM' hv => h0 ?_⟩
  subst hM'
  have hs : Seen r (b (M' + 1)) M' i (M' + 2) := (hb (M' + 1) (by omega)).seen_pred (by omega)
  rw [← ((l17_base_sameView hb).of_seen hs).vals_eq] at hv
  exact vals_subset_of_seen hs hv

omit hal in
/-- In the base run, the only carrier of `0` for `⟨z, M⟩` is `b (M - 1)`. -/
lemma l17_carriers_le (h0 : 0 ∉ vals r i (M + 1)) : carriers (l17Base r i M b) (b M) M 0 ≤ 1 := by
  classical
  have H := l17_chainHyp hb
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    rw [carriers_eq_card, card_eq_zero.2]
    · omega
    · rw [eq_empty_iff_forall_notMem]; intro p hp; exact absurd (mem_carrierSet.1 hp).1 (lt_irrefl 0)
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [carriers_eq_card]
  refine card_le_one.2 fun p hp q hq => ?_
  have key : ∀ p ∈ carrierSet (l17Base r i (M' + 1) b) (b (M' + 1)) (M' + 1) 0, p = b M' := by
    intro p hp
    obtain ⟨-, hs, hpv⟩ := mem_carrierSet.1 hp
    simp only [Nat.add_sub_cancel] at hs hpv
    have hfirst := l17_z_first hb (M := M' + 1) (b := b) h0
    rw [seen_succ_self_iff] at hs
    rcases hs with rfl | ⟨hpz, hd⟩
    · exact absurd hpv (hfirst.2 M' rfl)
    cases hpos : pos (M' + 1) (fun ℓ (_ : Unit) => b ℓ) p with
    | some ℓb =>
      obtain ⟨ℓ, u⟩ := ℓb
      obtain ⟨hℓ, rfl⟩ := H.pos_eq_some hpos
      rw [show (l17Base r i (M' + 1) b) = chainRun r i (M' + 1) (fun ℓ (_ : Unit) => b ℓ)
        (fun _ => 0) from rfl, H.deliv_w hℓ u] at hd
      rcases hd with h | ⟨rfl, -, -⟩
      · obtain rfl : ℓ = M' + 1 := by omega
        exact absurd rfl hpz
      · rfl
    | none =>
      exfalso
      rw [show (l17Base r i (M' + 1) b) = chainRun r i (M' + 1) (fun ℓ (_ : Unit) => b ℓ)
        (fun _ => 0) from rfl, H.deliv_of_none hpos, ite_eq_left ⟨(), le_rfl, rfl⟩] at hd
      -- `p` reached `i` in round `M' + 1`, so `⟨p, M'⟩` is in `i`'s view
      have hsp : Seen r p M' i (M' + 2) := by
        by_cases hpi : p = i
        · rw [hpi]; exact seen_self (by omega)
        · exact (seen_of_deliv hpi hd).mono_right (Nat.le_succ _)
      rw [← ((l17_base_sameView hb).of_seen hsp).vals_eq] at hpv
      exact h0 (vals_subset_of_seen hsp hpv)
  rw [key p hp, key q hq]

end Family

end L17

end Podc.ParetoOptimalConsensus
