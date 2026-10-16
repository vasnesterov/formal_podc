import Papers.PODC2018.Silence.Defs

/-!
# The Silent Choir Theorem (Theorem 2 of Goren–Moses)

If `K_i(v_j = 1)` holds at time `m` of a run `r` of any protocol in `γ_f`, and `r` contains no
message chain from `j` to `i`, then `m > 0` and `|F_r ∪ S_j^r(m − 1)| > f`.

Proof (as in the paper): otherwise build the run `r'` (`choirRun`) in which `v_j = 0` and every
process `h ∈ S_j^r(m − 1)` crashes, without sending anything, in the round right after the one in
which it first got a chain from `j` (if it has not crashed earlier anyway in `r`). Processes not yet
reached by a chain behave identically in both runs (`hist_choirRun`), so `r ≈ᵢᵐ r'`.
-/

namespace Papers.PODC2018.Silence

open Podc.SyncCrash Classical

variable {P M O : Type*} [Fintype P] {alg : Cslib.Byzantine.LockStep.Protocol P Bool M O}

section Construction

variable (alg) (r : Run P Bool) (j : P) (m : ℕ)

/-- The first time at which a chain from `(j, 0)` reaches `z` (`0` if never). -/
noncomputable def kk (z : P) : ℕ :=
  if h : ∃ t, Chain alg r j 0 z t then Nat.find h else 0

/-- The run `r'` of the proof of Theorem 2. -/
noncomputable def choirRun : Run P Bool where
  input := Function.update r.input j false
  crash z := if Chain alg r j 0 z (m - 1) then
      some (match r.crash z with
        | some c => min c (kk alg r j z + 1)
        | none => kk alg r j z + 1)
    else r.crash z
  reach z := if Chain alg r j 0 z (m - 1) ∧ ¬ (∃ c, r.crash z = some c ∧ c ≤ kk alg r j z) then ∅
    else r.reach z

end Construction

variable {r : Run P Bool} {j : P} {m : ℕ}

lemma chain_kk {z : P} {t : ℕ} (h : Chain alg r j 0 z t) :
    Chain alg r j 0 z (kk alg r j z) ∧ kk alg r j z ≤ t := by
  have he : ∃ t, Chain alg r j 0 z t := ⟨t, h⟩
  simp only [kk, dif_pos he]
  exact ⟨Nat.find_spec he, Nat.find_min' he h⟩

lemma lt_kk {z : P} {t t' : ℕ} (h : Chain alg r j 0 z t') (hn : ¬ Chain alg r j 0 z t) :
    t < kk alg r j z := by
  by_contra hle
  exact hn ((chain_kk h).1.trans_le (by omega))

/-- Processes not reached by time `ℓ` are alive at `ℓ` in `r'` iff they are in `r`. -/
lemma choirRun_alive_iff {z : P} {ℓ : ℕ} (hz : ¬ Chain alg r j 0 z ℓ) :
    (choirRun alg r j m).Alive z ℓ ↔ r.Alive z ℓ := by
  simp only [Run.Alive, choirRun]
  split_ifs with hS
  · have hk := lt_kk hS hz
    cases hc : r.crash z with
    | none => simp; omega
    | some c => simp; omega
  · rfl

lemma choirRun_crashRound_iff {y z : P} {ℓ : ℕ} (hy : ¬ Chain alg r j 0 y ℓ) :
    ((choirRun alg r j m).crash y = some (ℓ + 1) ∧ z ∉ (choirRun alg r j m).reach y) ↔
      (r.crash y = some (ℓ + 1) ∧ z ∉ r.reach y) := by
  simp only [choirRun]
  by_cases hS : Chain alg r j 0 y (m - 1)
  · have hk := lt_kk hS hy
    cases hc : r.crash y with
    | none => simp; omega
    | some c =>
      by_cases hck : c ≤ kk alg r j y
      · have : min c (kk alg r j y + 1) = c := by omega
        simp [hS, hc, hck, this]
      · simp [hS, hc, hck]; omega
  · simp [hS]

lemma choirRun_silent {y z : P} {ℓ : ℕ} (hℓ : ℓ ≤ m - 1) (hy : Chain alg r j 0 y ℓ) :
    ¬ ((choirRun alg r j m).Alive y ℓ ∧
      ¬ ((choirRun alg r j m).crash y = some (ℓ + 1) ∧ z ∉ (choirRun alg r j m).reach y)) := by
  have hS : Chain alg r j 0 y (m - 1) := hy.trans_le hℓ
  have hk := (chain_kk hy).2
  rintro ⟨ha, hn⟩
  simp only [Run.Alive, choirRun, if_pos hS] at ha hn
  cases hc : r.crash y with
  | none =>
    simp only [hc] at ha hn
    have := ha _ rfl
    exact hn ⟨by congr 1; omega, by simp [hS, hc]⟩
  | some c =>
    simp only [hc] at ha hn
    have := ha _ rfl
    have hck : ¬ c ≤ kk alg r j y := by omega
    exact hn ⟨by congr 1; omega, by simp [hS, hc, hck]⟩

lemma choirRun_msg {y z : P} {ℓ : ℕ} (hℓ : ℓ ≤ m - 1) (hz : ¬ Chain alg r j 0 z (ℓ + 1))
    (ih : ∀ x, ¬ Chain alg r j 0 x ℓ → r.Alive x ℓ →
      hist alg (choirRun alg r j m) ℓ x = hist alg r ℓ x) :
    msg alg (choirRun alg r j m) y z ℓ = msg alg r y z ℓ := by
  by_cases hy : Chain alg r j 0 y ℓ
  · have h1 : msg alg r y z ℓ = none := by
      by_contra hne; exact hz (Chain.step hy hne)
    rw [h1, msg_eq, if_neg (fun h => choirRun_silent hℓ hy h.2)]
  · have hyj : y ≠ j := fun h => hy (h ▸ Chain.refl (Nat.zero_le _))
    have hin : (choirRun alg r j m).input y = r.input y := by
      simp [choirRun, Function.update_of_ne hyj]
    rw [msg_eq, msg_eq]
    simp only [choirRun_alive_iff hy, choirRun_crashRound_iff hy, hin]
    split_ifs with hc
    · rw [ih y hy hc.2.1]
    · rfl

/-- Processes not reached by a chain from `j` by time `ℓ ≤ m` have the same history in `r` and
`r'` (the inductive claim of the paper's proof). -/
lemma hist_choirRun : ∀ ℓ ≤ m, ∀ z, ¬ Chain alg r j 0 z ℓ → r.Alive z ℓ →
    hist alg (choirRun alg r j m) ℓ z = hist alg r ℓ z := by
  intro ℓ
  induction ℓ with
  | zero => intros; rfl
  | succ ℓ ih =>
    intro hℓ z hz ha
    have hz' : ¬ Chain alg r j 0 z ℓ := fun h => hz (h.trans_le (by omega))
    rw [hist_succ, hist_succ, ih (by omega) z hz' (ha.mono (by omega))]
    congr 2
    funext y
    exact choirRun_msg (by omega) hz (ih (by omega))

lemma state_choirRun {i : P} (hi : ¬ Chain alg r j 0 i m) :
    state alg (choirRun alg r j m) i m = state alg r i m := by
  have hij : i ≠ j := fun h => hi (h ▸ Chain.refl (Nat.zero_le _))
  unfold state
  simp only [choirRun_alive_iff hi]
  split_ifs with ha
  · rw [hist_choirRun m le_rfl i hi ha]
    simp [choirRun, Function.update_of_ne hij]
  · rfl

lemma choirRun_faulty (z : P) :
    (choirRun alg r j m).Faulty z ↔ r.Faulty z ∨ Chain alg r j 0 z (m - 1) := by
  simp only [Run.Faulty, choirRun]
  split_ifs with h <;> simp [h]

lemma choirRun_admissible {f : ℕ} (hr : r.Admissible f)
    (hcard : (r.faulty ∪ S alg r j (m - 1)).card ≤ f) :
    (choirRun alg r j m).Admissible f := by
  refine ⟨?_, ?_⟩
  · have : (choirRun alg r j m).faulty = r.faulty ∪ S alg r j (m - 1) := by
      ext z; simp [choirRun_faulty]
    rwa [this]
  · intro z c hc
    simp only [choirRun] at hc
    split_ifs at hc with h
    · cases hrc : r.crash z with
      | none => simp [hrc] at hc; omega
      | some c' => have := hr.2 z c' hrc; simp [hrc] at hc; omega
    · exact hr.2 z c hc

/-- Theorem 2 with a weaker hypothesis (no chain from `j` *reaching `i` by time `m`*), which is
what the paper's proof actually uses. -/
theorem silent_choir_at {f : ℕ} (hr : r.Admissible f) {i : P}
    (hK : Knows alg f i m r (fun r' => r'.input j = true))
    (hno : ¬ Chain alg r j 0 i m) :
    0 < m ∧ f < (r.faulty ∪ S alg r j (m - 1)).card := by
  have hij : i ≠ j := fun h => hno (h ▸ Chain.refl (Nat.zero_le _))
  constructor
  · by_contra hm
    obtain rfl : m = 0 := by omega
    let r' : Run P Bool := { r with input := Function.update r.input j false }
    have hr' : r'.Admissible f := hr
    have hs : state alg r' i 0 = state alg r i 0 := by
      have h0 : ∀ x, hist alg r' 0 x = hist alg r 0 x := fun _ => rfl
      unfold state
      by_cases h : r.Alive i 0
      · rw [if_pos h, if_pos (show r'.Alive i 0 from h)]
        simp [r', h0, Function.update_of_ne hij]
      · rw [if_neg h, if_neg (show ¬ r'.Alive i 0 from h)]
    have := hK r' hr' hs
    simp [r'] at this
  · by_contra hc
    have := hK _ (choirRun_admissible hr (by omega)) (state_choirRun hno)
    simp [choirRun] at this

/-- **Theorem 2 (Silent Choir)** of Goren–Moses. Let `r` be a run of a protocol in `γ_f`. If
`K_i(v_j = 1)` holds at time `m` in `r` and `r` contains no message chain from `j` to `i`, then
`m > 0` and `|F_r ∪ S_j^r(m − 1)| > f`. -/
theorem silent_choir {f : ℕ} (hr : r.Admissible f) {i : P}
    (hK : Knows alg f i m r (fun r' => r'.input j = true))
    (hno : ∀ t, ¬ Chain alg r j 0 i t) :
    0 < m ∧ f < (r.faulty ∪ S alg r j (m - 1)).card :=
  silent_choir_at hr hK (hno m)

end Papers.PODC2018.Silence
