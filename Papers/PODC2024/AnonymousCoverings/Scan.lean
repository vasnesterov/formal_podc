import Papers.PODC2024.AnonymousCoverings.Model

/-!
# Structure of scans and fair writes

* `Exec.exists_completes_between`: between two writes, a processor completes a scan.
* `Exec.read_all_of_scan`: a scan that completes reads every register.
* `Exec.exists_completes_of_scanning`, `Exec.exists_write_of_live`: a live processor completes its
  scans and writes infinitely often.
* `Exec.exists_write_reg_of_live`: **fair writes** — a live processor writes *every* register
  infinitely often (consequence of the round-robin bookkeeping `written`).

The covering count (Lemma 4.5) built on these facts is `Exec.card_notWrittenBy_le` in
`Covering.lean`.
-/

namespace Podc.AnonymousCoverings

open Finset

variable {P R D X : Type*} [DecidableEq P] [DecidableEq R] [Fintype R]

namespace Exec

variable {A : Algo R D X} (e : Exec (P := P) A)

/-- `p` takes a non-idle step at time `t`. -/
def Moves (t : ℕ) (p : P) : Prop := ∃ r, e.act t = .write p r ∨ e.act t = .read p r

theorem loc_succ_of_not_moves {t : ℕ} {p : P} (h : ¬ e.Moves t p) :
    e.loc (t + 1) p = e.loc t p := by
  by_cases hp : (e.act t).proc = p
  · have hs := e.step t
    generalize ha : e.act t = a at hs hp
    cases a with
    | write q r => simp only [Act.proc] at hp; subst hp; exact absurd ⟨r, Or.inl ha⟩ h
    | read q r => simp only [Act.proc] at hp; subst hp; exact absurd ⟨r, Or.inr ha⟩ h
    | idle q => obtain ⟨-, -, h'⟩ := hs; unfold loc; rw [h']
  · exact e.loc_succ_of_ne hp

theorem loc_eq_of_not_moves {t t' : ℕ} {q : P} (htt : t ≤ t')
    (h : ∀ w, t ≤ w → w < t' → ¬ e.Moves w q) : e.loc t' q = e.loc t q := by
  induction t', htt using Nat.le_induction with
  | base => rfl
  | succ t' ht' ih =>
    rw [e.loc_succ_of_not_moves (h t' ht' (by omega)), ih fun w h1 h2 => h w h1 (by omega)]

theorem moves_of_scan_change {t : ℕ} {p : P}
    (h : (e.loc (t + 1) p).scan ≠ (e.loc t p).scan) : e.Moves t p := by
  by_contra hm
  exact h (by rw [e.loc_succ_of_not_moves hm])

/-- If `p`'s scan status goes from `some _` to `none` at time `t`, `p` completes a scan at `t`. -/
theorem completes_of_scan_none {t : ℕ} {p : P} (h1 : (e.loc t p).scan ≠ none)
    (h2 : (e.loc (t + 1) p).scan = none) : e.Completes t p := by
  obtain ⟨r, hr | hr⟩ := e.moves_of_scan_change (by rw [h2]; exact Ne.symm h1)
  · exact absurd (e.write_spec hr).1 h1
  · exact ⟨⟨r, hr⟩, h2⟩

theorem scan_after_write {w : ℕ} {p : P} {r : R} (h : e.act w = .write p r) :
    (e.loc (w + 1) p).scan = some ∅ := by
  rw [(e.write_spec h).2.2.2.2]

/-- Between two writes of `p`, `p` completes a scan. -/
theorem exists_completes_between {w₁ w₂ : ℕ} {p : P} (hw : w₁ < w₂) (h₁ : e.WritesAt w₁ p)
    (h₂ : e.WritesAt w₂ p) : ∃ c, w₁ < c ∧ c < w₂ ∧ e.Completes c p := by
  obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂
  have hs1 := e.scan_after_write hr₁
  have hs2 := e.scan_none_of_write hr₂
  have hne : w₁ + 1 ≠ w₂ := by rintro rfl; rw [hs1] at hs2; exact absurd hs2 (by simp)
  obtain ⟨c, hc1, hc2, hc3, hc4, -⟩ := Nat.exists_first_Ioc (Q := fun t => (e.loc t p).scan = none)
    (s := w₁ + 1) (B := w₂) (by rw [hs1]; simp) ⟨w₂, by omega, le_rfl, hs2⟩
  exact ⟨c, by omega, by omega, e.completes_of_scan_none hc3 hc4⟩

/-- Read-set invariant: while `p` keeps scanning after its write at `s`, every register in its
read set was read by `p` after `s`. -/
theorem read_set_spec {s c : ℕ} {p : P} {r₀ : R} (hw : e.act s = .write p r₀)
    (hnc : ∀ t, s < t → t ≤ c → (e.loc t p).scan ≠ none) :
    ∀ t, s < t → t ≤ c → ∃ S, (e.loc t p).scan = some S ∧
      ∀ r ∈ S, ∃ t', s < t' ∧ t' < t ∧ e.act t' = .read p r := by
  intro t hst htc
  induction t, (show s + 1 ≤ t by omega) using Nat.le_induction with
  | base => exact ⟨∅, e.scan_after_write hw, by simp⟩
  | succ t ht ih =>
    obtain ⟨S, hS, hSr⟩ := ih (by omega) (by omega)
    by_cases hm : e.Moves t p
    · obtain ⟨r, hr | hr⟩ := hm
      · rw [(e.write_spec hr).1] at hS; exact absurd hS (by simp)
      · obtain ⟨S', hS', hrS', hpost⟩ := e.read_spec hr
        rw [hS] at hS'; cases hS'
        have hne := hnc (t + 1) (by omega) htc
        rw [hpost] at hne ⊢
        split_ifs at hne ⊢ with hu
        · exact absurd rfl hne
        · refine ⟨insert r S, rfl, fun r' hr' => ?_⟩
          rcases mem_insert.1 hr' with rfl | hr'
          · exact ⟨t, by omega, by omega, hr⟩
          · obtain ⟨t', h1, h2, h3⟩ := hSr r' hr'
            exact ⟨t', h1, by omega, h3⟩
    · rw [e.loc_succ_of_not_moves hm]
      exact ⟨S, hS, fun r' hr' => (hSr r' hr').imp fun t' h => ⟨h.1, by omega, h.2.2⟩⟩

/-- A scan that starts with the write at time `s` and completes at time `c` (without completing
earlier) reads every register during `(s, c]`. -/
theorem read_all_of_scan {s c : ℕ} {p : P} {r₀ : R} (hw : e.act s = .write p r₀)
    (hc : e.Completes c p) (hsc : s < c)
    (hnc : ∀ t, s < t → t ≤ c → (e.loc t p).scan ≠ none) :
    ∀ r, ∃ t, s < t ∧ t ≤ c ∧ e.act t = .read p r := by
  obtain ⟨S, hS, hSr⟩ := e.read_set_spec hw hnc c hsc le_rfl
  obtain ⟨⟨rc, hrc⟩, hdone⟩ := hc
  obtain ⟨S', hS', hrS', hpost⟩ := e.read_spec hrc
  rw [hS] at hS'; cases hS'
  have hu : insert rc S = univ := by
    by_contra hu
    rw [hpost] at hdone; simp [hu] at hdone
  intro r
  have : r ∈ insert rc S := by rw [hu]; exact mem_univ r
  rcases mem_insert.1 this with rfl | hr
  · exact ⟨c, hsc, le_rfl, hrc⟩
  · obtain ⟨t', h1, h2, h3⟩ := hSr r hr
    exact ⟨t', h1, by omega, h3⟩

/-- A live processor takes a non-idle step at or after any time; we take the first one. -/
theorem exists_first_move {p : P} (hl : e.Live p) (T : ℕ) :
    ∃ t ≥ T, e.Moves t p ∧ ∀ w, T ≤ w → w < t → ¬ e.Moves w p := by
  classical
  have hex : ∃ t, T ≤ t ∧ e.Moves t p := by
    obtain ⟨t, ht, r, hr⟩ := hl T
    exact ⟨t, ht, r, hr⟩
  exact ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
    fun w h1 h2 hm => Nat.find_min hex h2 ⟨h1, hm⟩⟩

/-- A live processor that is scanning completes its scan, without leaving the scanning phase
before. -/
theorem exists_completes_of_scanning {p : P} (hl : e.Live p) :
    ∀ n t S, (e.loc t p).scan = some S → Fintype.card R - S.card ≤ n →
      ∃ c ≥ t, e.Completes c p ∧ ∀ t', t ≤ t' → t' ≤ c → (e.loc t' p).scan ≠ none := by
  intro n
  induction n with
  | zero =>
    intro t S hS hn
    obtain ⟨t1, ht1, ⟨r, hr | hr⟩, hno⟩ := e.exists_first_move hl t
    · have hl1 := e.loc_eq_of_not_moves ht1 hno
      have h' := (e.write_spec hr).1
      rw [hl1, hS] at h'; exact absurd h' (by simp)
    · have hl1 := e.loc_eq_of_not_moves ht1 hno
      obtain ⟨S', hS', hrS', -⟩ := e.read_spec hr
      rw [hl1, hS] at hS'; cases hS'
      have : S = univ := eq_univ_of_card S (by have := card_le_univ S; omega)
      exact absurd (this ▸ mem_univ r) hrS'
  | succ n ih =>
    intro t S hS hn
    obtain ⟨t1, ht1, ⟨r, hr | hr⟩, hno⟩ := e.exists_first_move hl t
    · have hl1 := e.loc_eq_of_not_moves ht1 hno
      have h' := (e.write_spec hr).1
      rw [hl1, hS] at h'; exact absurd h' (by simp)
    · have hl1 := e.loc_eq_of_not_moves ht1 hno
      obtain ⟨S', hS', hrS', hpost⟩ := e.read_spec hr
      rw [hl1, hS] at hS'; cases hS'
      have hstay : ∀ t', t ≤ t' → t' ≤ t1 → (e.loc t' p).scan ≠ none := by
        intro t' h1 h2
        rw [e.loc_eq_of_not_moves h1 fun w hw1 hw2 => hno w hw1 (by omega), hS]; simp
      by_cases hu : insert r S = univ
      · refine ⟨t1, ht1, ⟨⟨r, hr⟩, ?_⟩, hstay⟩
        rw [hpost]; simp [hu]
      · have hS2 : (e.loc (t1 + 1) p).scan = some (insert r S) := by rw [hpost]; simp [hu]
        obtain ⟨c, hc, hcc, hcs⟩ := ih (t1 + 1) (insert r S) hS2
          (by rw [card_insert_of_notMem hrS']; omega)
        refine ⟨c, by omega, hcc, fun t' h1 h2 => ?_⟩
        rcases Nat.lt_or_ge t' (t1 + 1) with h | h
        · exact hstay t' h1 (by omega)
        · exact hcs t' h h2

/-- After a write at time `s`, a live processor completes the scan it started. -/
theorem exists_completes_after_write {p : P} (hl : e.Live p) {s : ℕ} {r : R}
    (hw : e.act s = .write p r) :
    ∃ c > s, e.Completes c p ∧ ∀ t, s < t → t ≤ c → (e.loc t p).scan ≠ none := by
  obtain ⟨c, hc, hcc, hcs⟩ := e.exists_completes_of_scanning hl _ (s + 1) ∅
    (e.scan_after_write hw) le_rfl
  exact ⟨c, by omega, hcc, fun t h1 h2 => hcs t h1 h2⟩

/-- A live processor writes at some time after any given time. -/
theorem exists_write_of_live {p : P} (hl : e.Live p) (T : ℕ) : ∃ w ≥ T, e.WritesAt w p := by
  obtain ⟨t, ht, r, hr | hr⟩ := hl T
  · exact ⟨t, ht, r, hr⟩
  · obtain ⟨S, hS, -, -⟩ := e.read_spec hr
    obtain ⟨c, hc, ⟨-, hdone⟩, -⟩ := e.exists_completes_of_scanning hl _ t S hS le_rfl
    obtain ⟨t1, ht1, ⟨r', hr' | hr'⟩, hno⟩ := e.exists_first_move hl (c + 1)
    · exact ⟨t1, by omega, r', hr'⟩
    · have hl1 := e.loc_eq_of_not_moves ht1 hno
      obtain ⟨S', hS', -⟩ := e.read_spec hr'
      rw [hl1, hdone] at hS'; exact absurd hS' (by simp)

/-- Potential for the round-robin argument: decreases at every write of a register `≠ r`. -/
def rrPot (r : R) (w : Finset R) : ℕ :=
  if r ∈ w then 2 * Fintype.card R - w.card else Fintype.card R - w.card

theorem rrPot_lt {r r' : R} {w : Finset R} (hr : r' ≠ r) (hw : r' ∉ w) :
    rrPot r (nextWritten w r') < rrPot r w := by
  have hc : (insert r' w).card = w.card + 1 := card_insert_of_notMem hw
  have hle : (insert r' w).card ≤ Fintype.card R := card_le_univ _
  unfold rrPot nextWritten
  by_cases hrw : r ∈ w
  · by_cases hu : insert r' w = univ
    · have h1 : (insert r' w).card = Fintype.card R := by rw [hu, card_univ]
      simp only [hu, ite_true, notMem_empty, ite_false, hrw, card_empty]
      omega
    · simp only [hu, ite_false, mem_insert_of_mem hrw, ite_true, hrw]
      omega
  · have hu : insert r' w ≠ univ := fun hu => by
      have : r ∈ insert r' w := hu ▸ mem_univ r
      rcases mem_insert.1 this with h | h
      · exact hr h.symm
      · exact hrw h
    have hr2 : r ∉ insert r' w := by simp [Ne.symm hr, hrw]
    simp only [hu, ite_false, hr2, hrw]
    omega

/-- **Fair writes.** A live processor writes every register infinitely often. -/
theorem exists_write_reg_of_live {p : P} (hl : e.Live p) (r : R) (T : ℕ) :
    ∃ w ≥ T, e.act w = .write p r := by
  by_contra hne
  push Not at hne
  have hmono : ∀ m ≥ T, rrPot r (e.loc (m + 1) p).written ≤ rrPot r (e.loc m p).written := by
    intro m hm
    by_cases hmv : e.Moves m p
    · obtain ⟨r', hr' | hr'⟩ := hmv
      · have hne' : r' ≠ r := fun h => hne m hm (h ▸ hr')
        obtain ⟨-, hw, -, -, hpost⟩ := e.write_spec hr'
        rw [hpost]; exact (rrPot_lt hne' hw).le
      · obtain ⟨S, -, -, hpost⟩ := e.read_spec hr'
        rw [hpost]; split_ifs <;> exact le_rfl
    · rw [e.loc_succ_of_not_moves hmv]
  apply Nat.not_frequently_lt_of_succ_le (f := fun m => rrPot r (e.loc m p).written) hmono
  intro M
  obtain ⟨w, hw, r', hr'⟩ := e.exists_write_of_live hl (max M T)
  refine ⟨w, le_of_max_le_left hw, ?_⟩
  have hne' : r' ≠ r := fun h => hne w (le_of_max_le_right hw) (h ▸ hr')
  obtain ⟨-, hwr, -, -, hpost⟩ := e.write_spec hr'
  rw [hpost]; exact rrPot_lt hne' hwr

end Exec

end Podc.AnonymousCoverings
