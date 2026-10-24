import Papers.PODC2016.UnbeatableSetConsensus.Model

/-!
# Basic facts about full-information views in the synchronous crash model

* delivery and liveness in terms of the crash pattern (`deliv_iff`, `alive_iff`, …);
* seen nodes: reflexivity, transitivity, liveness of seen nodes (`Seen.alive`), splitting a chain
  at an intermediate time (`Seen.through`), the last round (`seen_succ_iff`);
* `Vals`: monotonicity, the one-round recursion `mem_vals_succ`, `Min`, low/high;
* hidden nodes: soundness of crash proofs (`not_guarCrashed_of_alive`), the predecessor of a
  hidden node is seen (`Hidden.seen_pred`), a node hidden at a time `< m` belongs to a faulty
  process that did not reach `i` (`Hidden.not_deliv`, `Hidden.faulty`) and a process is hidden at
  most at one time (`Hidden.time_eq`); monotonicity of the hidden capacity (`hc_mono`);
* same views: everything above is a function of the view (`SameView.seen_iff`, `.vals_eq`,
  `.hidden_iff`, `.hc_eq`, …), the locality lemma `sameView_of_agree`, and the transfer of
  decisions `SameView.decidesAt_iff`.
-/

-- CSLib candidate: Cslib/Computability/Distributed/SyncCrash/FullInfo.lean (seen nodes, views,
-- hidden nodes and locality for full-information protocols in the synchronous crash model)

namespace Podc.UnbeatableSetConsensus

open Cslib Cslib.DynNet Cslib.HeardOf Finset

variable {P : Type*}

/-! ### Delivery and liveness -/

section Crash

variable {r : Run P} {p q : P} {t m : ℕ}

lemma alive_iff : r.Alive p m ↔ ∀ c, r.crash p = some c → m < c := Iff.rfl

lemma deliv_iff : r.Deliv q p t ↔ r.Alive q t ∧ ¬ (r.crash q = some (t + 1) ∧ p ∉ r.reach q) :=
  Iff.rfl

lemma alive_of_crash_none (h : r.crash p = none) (m : ℕ) : r.Alive p m := by
  intro c hc; simp [h] at hc

lemma alive_of_crash_some {c : ℕ} (h : r.crash p = some c) : r.Alive p m ↔ m < c := by
  constructor
  · intro ha; exact ha c h
  · intro hm c' hc'; rw [h] at hc'; cases hc'; exact hm

lemma deliv_of_crash_none (h : r.crash q = none) (p : P) (t : ℕ) : r.Deliv q p t :=
  ⟨alive_of_crash_none h t, fun hc => by simp [h] at hc⟩

lemma deliv_of_crash_some {c : ℕ} (h : r.crash q = some c) :
    r.Deliv q p t ↔ t + 1 < c ∨ (t + 1 = c ∧ p ∈ r.reach q) := by
  rw [deliv_iff, alive_of_crash_some h, h]
  constructor
  · rintro ⟨h1, h2⟩
    rcases Nat.lt_or_ge (t + 1) c with h3 | h3
    · exact Or.inl h3
    · refine Or.inr ⟨by omega, ?_⟩
      by_contra hp; exact h2 ⟨by congr 1; omega, hp⟩
  · rintro (h1 | ⟨h1, h2⟩)
    · refine ⟨by omega, ?_⟩
      rintro ⟨h3, -⟩; simp at h3; omega
    · refine ⟨by omega, ?_⟩
      rintro ⟨-, h3⟩; exact h3 h2

lemma Deliv.alive (h : r.Deliv q p t) : r.Alive q t := h.1

/-- A process alive at time `t + 1` delivers its round-`t + 1` messages to everybody. -/
lemma deliv_of_alive_succ (h : r.Alive q (t + 1)) (p : P) : r.Deliv q p t := by
  refine ⟨h.mono (Nat.le_succ t), ?_⟩
  rintro ⟨hc, -⟩
  exact absurd (h _ hc) (lt_irrefl _)

lemma not_faulty_iff : ¬ r.Faulty p ↔ r.crash p = none := by
  simp [SyncCrash.Run.Faulty]

/-- An alive process at time `t` that does not crash in round `t + 1` delivers to everybody. -/
lemma deliv_of_alive_of_ne (h : r.Alive q t) (hc : r.crash q ≠ some (t + 1)) (p : P) :
    r.Deliv q p t :=
  ⟨h, fun h' => hc h'.1⟩

end Crash

/-! ### Seen nodes -/

section Seen

variable {r : Run P} {i j h : P} {ℓ m s : ℕ}

lemma comm_iff {t : ℕ} {q p : P} : comm r t q p ↔ q ≠ p ∧ r.Deliv q p t := Iff.rfl

lemma seen_self (hℓ : ℓ ≤ m) : Seen r i ℓ i m := Journey.self hℓ

lemma Seen.le (hs : Seen r j ℓ i m) : ℓ ≤ m := Journey.le hs

lemma Seen.trans {k : P} {n : ℕ} (h₁ : Seen r j ℓ k n) (h₂ : Seen r k n i m) : Seen r j ℓ i m :=
  Journey.trans h₁ h₂

lemma Seen.mono_right {m' : ℕ} (hs : Seen r j ℓ i m) (hm : m ≤ m') : Seen r j ℓ i m' :=
  Journey.mono_right hs hm

lemma Seen.mono_left {ℓ' : ℕ} (hs : Seen r j ℓ i m) (hℓ : ℓ' ≤ ℓ) : Seen r j ℓ' i m :=
  Journey.mono_left hs hℓ

lemma seen_same_time (hs : Seen r j m i m) : j = i := Journey.same_time hs

lemma seen_of_comm {t : ℕ} (hc : comm r t j i) : Seen r j t i (t + 1) := Journey.single hc

lemma seen_of_deliv {t : ℕ} (hne : j ≠ i) (hd : r.Deliv j i t) : Seen r j t i (t + 1) :=
  seen_of_comm ⟨hne, hd⟩

/-- The last round of a chain. -/
lemma seen_succ_iff (hℓ : ℓ ≤ m) :
    Seen r j ℓ i (m + 1) ↔ Seen r j ℓ i m ∨ ∃ q, comm r m q i ∧ Seen r j ℓ q m := by
  unfold Seen
  rw [journey_succ_iff hℓ]
  constructor
  · rintro ⟨y, hy, rfl | hy'⟩
    · exact Or.inl hy
    · exact Or.inr ⟨y, hy', hy⟩
  · rintro (hy | ⟨q, hq, hy⟩)
    · exact ⟨i, hy, Or.inl rfl⟩
    · exact ⟨q, hy, Or.inr hq⟩

/-- Seen nodes of a live node are live (messages are sent only by live processes). -/
lemma Seen.alive (hs : Seen r j ℓ i m) (hi : r.Alive i m) : r.Alive j ℓ := by
  unfold Seen at hs
  induction hs with
  | refl => exact hi
  | @step y z t _ hyz ih =>
    apply ih
    rcases hyz with rfl | hyz
    · exact hi.mono (Nat.le_succ t)
    · exact hyz.2.1

/-- A chain from time `ℓ` to time `m` passes through every intermediate time. -/
lemma Seen.through (hs : Seen r j ℓ i m) (h1 : ℓ ≤ s) (h2 : s ≤ m) :
    ∃ k, Seen r j ℓ k s ∧ Seen r k s i m := by
  induction m generalizing i with
  | zero =>
    obtain rfl : s = 0 := by omega
    exact ⟨i, hs, seen_self le_rfl⟩
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le h2 with rfl | h2
    · exact ⟨i, hs, seen_self le_rfl⟩
    · have hℓ : ℓ ≤ m := by omega
      rcases (seen_succ_iff hℓ).1 hs with hs | ⟨q, hq, hs⟩
      · obtain ⟨k, hk1, hk2⟩ := ih hs (by omega)
        exact ⟨k, hk1, hk2.mono_right (Nat.le_succ m)⟩
      · obtain ⟨k, hk1, hk2⟩ := ih hs (by omega)
        exact ⟨k, hk1, hk2.trans (seen_of_comm hq)⟩

/-- If `⟨j, ℓ⟩` is seen by `⟨i, m⟩` for `ℓ < m`, then some node `⟨q, ℓ + 1⟩` seen by `⟨i, m⟩`
received `j`'s round-`ℓ + 1` message (or `q = j`). -/
lemma Seen.exists_succ (hs : Seen r j ℓ i m) (hlt : ℓ < m) :
    ∃ q, (q = j ∨ comm r ℓ j q) ∧ Seen r q (ℓ + 1) i m := by
  obtain ⟨q, hq1, hq2⟩ := Journey.front hs hlt
  exact ⟨q, hq1.imp Eq.symm id, hq2⟩

end Seen

/-! ### Values, `Min`, low and high -/

section Vals

variable [Fintype P] {r : Run P} {i j : P} {ℓ m : ℕ} {k : ℕ}

lemma mem_vals {v : ℕ} : v ∈ vals r i m ↔ ∃ j, Seen r j 0 i m ∧ r.input j = v := by
  classical
  simp [vals]

lemma input_mem_vals (r : Run P) (i : P) (m : ℕ) : r.input i ∈ vals r i m :=
  mem_vals.2 ⟨i, seen_self (Nat.zero_le m), rfl⟩

lemma vals_subset_of_seen (hs : Seen r j ℓ i m) : vals r j ℓ ⊆ vals r i m := by
  intro v hv
  obtain ⟨q, hq, rfl⟩ := mem_vals.1 hv
  exact mem_vals.2 ⟨q, hq.trans hs, rfl⟩

lemma vals_mono {m' : ℕ} (hm : m ≤ m') : vals r i m ⊆ vals r i m' :=
  vals_subset_of_seen (seen_self hm)

lemma vals_zero : vals r i 0 = {r.input i} := by
  ext v
  rw [mem_vals, mem_singleton]
  constructor
  · rintro ⟨j, hj, rfl⟩; rw [seen_same_time hj]
  · rintro rfl; exact ⟨i, seen_self le_rfl, rfl⟩

lemma mem_vals_succ {v : ℕ} :
    v ∈ vals r i (m + 1) ↔ v ∈ vals r i m ∨ ∃ q, comm r m q i ∧ v ∈ vals r q m := by
  simp only [mem_vals]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases (seen_succ_iff (Nat.zero_le m)).1 hj with hj | ⟨q, hq, hj⟩
    · exact Or.inl ⟨j, hj, rfl⟩
    · exact Or.inr ⟨q, hq, j, hj, rfl⟩
  · rintro (⟨j, hj, rfl⟩ | ⟨q, hq, j, hj, rfl⟩)
    · exact ⟨j, hj.mono_right (Nat.le_succ m), rfl⟩
    · exact ⟨j, hj.trans (seen_of_comm hq), rfl⟩

lemma vals_subset_succ_of_comm (hc : comm r m j i) : vals r j m ⊆ vals r i (m + 1) :=
  vals_subset_of_seen (seen_of_comm hc)

/-- A value seen at time `m` was seen at every earlier time `ℓ` by some node of the view. -/
lemma exists_seen_of_mem_vals {v : ℕ} (hv : v ∈ vals r i m) (hℓ : ℓ ≤ m) :
    ∃ q, Seen r q ℓ i m ∧ v ∈ vals r q ℓ := by
  obtain ⟨j, hj, rfl⟩ := mem_vals.1 hv
  obtain ⟨q, hq1, hq2⟩ := hj.through (Nat.zero_le ℓ) hℓ
  exact ⟨q, hq2, mem_vals.2 ⟨j, hq1, rfl⟩⟩

lemma minVal_mem (r : Run P) (i : P) (m : ℕ) : minVal r i m ∈ vals r i m := min'_mem _ _

lemma minVal_le {v : ℕ} (hv : v ∈ vals r i m) : minVal r i m ≤ v := min'_le _ _ hv

lemma le_minVal_iff {v : ℕ} : v ≤ minVal r i m ↔ ∀ w ∈ vals r i m, v ≤ w := le_min'_iff _ _

lemma minVal_le_of_seen (hs : Seen r j ℓ i m) : minVal r i m ≤ minVal r j ℓ :=
  minVal_le (vals_subset_of_seen hs (minVal_mem r j ℓ))

lemma low_iff_minVal : Low k r i m ↔ minVal r i m < k := by
  constructor
  · rintro ⟨v, hv, hvk⟩; exact lt_of_le_of_lt (minVal_le hv) hvk
  · intro h; exact ⟨_, minVal_mem r i m, h⟩

lemma mem_lows {v : ℕ} : v ∈ lows k r i m ↔ v ∈ vals r i m ∧ v < k := mem_filter

lemma low_iff_lows_nonempty : Low k r i m ↔ (lows k r i m).Nonempty := by
  constructor
  · rintro ⟨v, hv, hvk⟩; exact ⟨v, mem_lows.2 ⟨hv, hvk⟩⟩
  · rintro ⟨v, hv⟩; exact ⟨v, (mem_lows.1 hv).1, (mem_lows.1 hv).2⟩

lemma not_low_iff : ¬ Low k r i m ↔ ∀ v ∈ vals r i m, k ≤ v := by
  simp [Low]

lemma Low.of_seen (hl : Low k r j ℓ) (hs : Seen r j ℓ i m) : Low k r i m := by
  obtain ⟨v, hv, hvk⟩ := hl
  exact ⟨v, vals_subset_of_seen hs hv, hvk⟩

lemma Low.mono {m' : ℕ} (hl : Low k r i m) (hm : m ≤ m') : Low k r i m' :=
  hl.of_seen (seen_self hm)

lemma lows_subset_of_seen (hs : Seen r j ℓ i m) : lows k r j ℓ ⊆ lows k r i m :=
  filter_subset_filter _ (vals_subset_of_seen hs)

lemma lows_mono {m' : ℕ} (hm : m ≤ m') : lows k r i m ⊆ lows k r i m' :=
  lows_subset_of_seen (seen_self hm)

lemma lows_eq_empty_of_not_low (h : ¬ Low k r i m) : lows k r i m = ∅ := by
  rw [← not_nonempty_iff_eq_empty, ← low_iff_lows_nonempty]; exact h

/-- If a process `z` is high at time `s + 1`, then every process that is low and alive at time `s`
crashes in round `s + 1` (otherwise its message would make `z` low). -/
lemma crash_eq_of_low_of_high {z y : P} {s : ℕ} (hz : ¬ Low k r z (s + 1)) (hy : r.Alive y s)
    (hl : Low k r y s) : r.crash y = some (s + 1) := by
  by_contra hc
  apply hz
  by_cases hyz : y = z
  · subst hyz; exact hl.mono (Nat.le_succ s)
  · exact hl.of_seen (seen_of_deliv hyz (deliv_of_alive_of_ne hy hc z))

end Vals

/-! ### Hidden nodes and the hidden capacity -/

section Hidden

variable {r : Run P} {i j : P} {ℓ m : ℕ}

/-- Crash proofs are sound: a node of a live process is never guaranteed crashed. -/
lemma not_guarCrashed_of_alive (hj : r.Alive j ℓ) : ¬ GuarCrashed r i m j ℓ := by
  rintro ⟨h, s, hs, -, -, hd⟩
  exact hd (deliv_of_alive_succ (hj.mono (by omega)) h)

lemma hidden_of_alive (hj : r.Alive j ℓ) (hs : ¬ Seen r j ℓ i m) : Hidden r i m j ℓ :=
  ⟨hs, not_guarCrashed_of_alive hj⟩

/-- Distinct processes at the current time are not seen; a live one is hidden. -/
lemma hidden_now_of_alive (hj : r.Alive j m) (hne : j ≠ i) : Hidden r i m j m :=
  hidden_of_alive hj (fun h => hne (seen_same_time h))

/-- The predecessor of a hidden node is seen (otherwise `⟨i, ℓ + 1⟩` proves the crash). -/
lemma Hidden.seen_pred (hh : Hidden r i m j (ℓ + 1)) (hℓ : ℓ + 1 ≤ m) : Seen r j ℓ i m := by
  by_contra hns
  apply hh.2
  have hne : i ≠ j := by
    rintro rfl; exact hns (seen_self (by omega))
  refine ⟨i, ℓ, Nat.lt_succ_self ℓ, seen_self hℓ, hne, fun hd => hns ?_⟩
  exact (seen_of_deliv (Ne.symm hne) hd).mono_right hℓ

/-- A hidden node `⟨j, ℓ⟩` delivered round `s + 1 ≤ ℓ` to every seen node `⟨h, s + 1⟩`. -/
lemma Hidden.deliv {h : P} {s : ℕ} (hh : Hidden r i m j ℓ) (hs : s < ℓ) (hseen : Seen r h (s + 1) i m)
    (hne : h ≠ j) : r.Deliv j h s := by
  by_contra hd
  exact hh.2 ⟨h, s, hs, hseen, hne, hd⟩

lemma Hidden.ne (hh : Hidden r i m j ℓ) (hℓ : ℓ ≤ m) : j ≠ i := by
  rintro rfl; exact hh.1 (seen_self hℓ)

/-- A node hidden at a time `ℓ < m` did not reach `i` in round `ℓ + 1`. -/
lemma Hidden.not_deliv (hh : Hidden r i m j ℓ) (hℓ : ℓ < m) : ¬ r.Deliv j i ℓ := by
  intro hd
  exact hh.1 ((seen_of_deliv (hh.ne hℓ.le) hd).mono_right hℓ)

/-- A node hidden at a time `ℓ < m` belongs to a process that crashes by round `ℓ + 1`. -/
lemma Hidden.crash_le (hh : Hidden r i m j ℓ) (hℓ : ℓ < m) :
    ∃ c, r.crash j = some c ∧ c ≤ ℓ + 1 := by
  have hd := hh.not_deliv hℓ
  cases hc : r.crash j with
  | none => exact absurd (deliv_of_crash_none hc i ℓ) hd
  | some c =>
    refine ⟨c, rfl, ?_⟩
    rw [deliv_of_crash_some hc] at hd
    omega

lemma Hidden.faulty (hh : Hidden r i m j ℓ) (hℓ : ℓ < m) : r.Faulty j := by
  obtain ⟨c, hc, -⟩ := hh.crash_le hℓ
  simp [SyncCrash.Run.Faulty, hc]

/-- A process is hidden from `⟨i, m⟩` at most at one time `≤ m`. -/
lemma Hidden.time_eq {ℓ' : ℕ} (hh : Hidden r i m j ℓ) (hh' : Hidden r i m j ℓ') (hℓ : ℓ ≤ m)
    (hℓ' : ℓ' ≤ m) : ℓ = ℓ' := by
  wlog hlt : ℓ < ℓ' generalizing ℓ ℓ'
  · rcases Nat.lt_or_ge ℓ' ℓ with h | h
    · exact (this hh' hh hℓ' hℓ h).symm
    · omega
  exfalso
  exact hh'.2 ⟨i, ℓ, hlt, seen_self (by omega), (hh.ne hℓ).symm, hh.not_deliv (by omega)⟩

/-- Hidden nodes stay hidden from earlier nodes of the same process. -/
lemma Hidden.mono {m' : ℕ} (hh : Hidden r i m j ℓ) (hm : m' ≤ m) : Hidden r i m' j ℓ := by
  refine ⟨fun hs => hh.1 (hs.mono_right hm), ?_⟩
  rintro ⟨h, s, hs, hseen, hne, hd⟩
  exact hh.2 ⟨h, s, hs, hseen.mono_right hm, hne, hd⟩

variable [Fintype P]

lemma mem_hiddenAt {ℓ : ℕ} : j ∈ hiddenAt r i m ℓ ↔ Hidden r i m j ℓ := by
  classical
  simp [hiddenAt]

lemma le_hc_iff {c : ℕ} : c ≤ hc r i m ↔ ∀ ℓ ≤ m, c ≤ (hiddenAt r i m ℓ).card := by
  unfold hc
  rw [le_inf'_iff]
  simp

lemma hc_lt_iff {c : ℕ} : hc r i m < c ↔ ∃ ℓ ≤ m, (hiddenAt r i m ℓ).card < c := by
  rw [← not_le, le_hc_iff]; push Not; rfl

lemma hiddenAt_mono {m' ℓ : ℕ} (hm : m' ≤ m) :
    hiddenAt r i m ℓ ⊆ hiddenAt r i m' ℓ := by
  intro j hj
  rw [mem_hiddenAt] at hj ⊢
  exact hj.mono hm

/-- The hidden capacity is non-increasing in time (Remark 1). -/
lemma hc_mono {m' : ℕ} (hm : m' ≤ m) : hc r i m ≤ hc r i m' := by
  rw [le_hc_iff]
  intro ℓ hℓ
  exact (le_hc_iff.1 le_rfl ℓ (by omega)).trans (card_le_card (hiddenAt_mono hm))

omit [Fintype P] in
/-- At time `0` nothing is guaranteed crashed: all other processes are hidden. -/
lemma hidden_zero_iff : Hidden r i m j 0 ↔ ¬ Seen r j 0 i m := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rintro ⟨_, s, hs, -⟩; omega

/-- From `c ≤ HC⟨i, m⟩`, a family of witnesses: for every `ℓ ≤ m`, an injective family of nodes at
time `ℓ` hidden from `⟨i, m⟩`, indexed by any type of size `c`. -/
lemma exists_witnesses {ι : Type*} [Fintype ι] (h : Fintype.card ι ≤ hc r i m) :
    ∃ w : ℕ → ι → P, ∀ ℓ ≤ m, Function.Injective (w ℓ) ∧ ∀ b, Hidden r i m (w ℓ b) ℓ := by
  classical
  have : ∀ ℓ, ∃ f : ι → P, ℓ ≤ m → Function.Injective f ∧ ∀ b, Hidden r i m (f b) ℓ := by
    intro ℓ
    by_cases hℓ : ℓ ≤ m
    · have hc := (le_hc_iff.1 h ℓ hℓ)
      rw [← Fintype.card_coe] at hc
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
      exact ⟨fun b => (e b).1, fun _ => ⟨fun a b hab => e.injective (Subtype.ext hab),
        fun b => mem_hiddenAt.1 (e b).2⟩⟩
    · by_cases hP : Nonempty P
      · exact ⟨fun _ => Classical.arbitrary P, fun h => absurd h hℓ⟩
      · exact ⟨fun _ => (hP ⟨i⟩).elim, fun h => absurd h hℓ⟩
  choose w hw using this
  exact ⟨w, fun ℓ hℓ => hw ℓ hℓ⟩

end Hidden

/-! ### Everything is a function of the view -/

section SameView

variable {r r' r'' : Run P} {i j : P} {ℓ m : ℕ}

lemma sameView_refl (r : Run P) (i : P) (m : ℕ) : SameView r r i m :=
  FIIndist.refl (fun _ => rfl) m i

lemma SameView.symm (h : SameView r r' i m) : SameView r' r i m :=
  FIIndist.symm (fun _ hp => hp.symm) h

lemma SameView.trans (h₁ : SameView r r' i m) (h₂ : SameView r' r'' i m) : SameView r r'' i m :=
  FIIndist.trans (fun _ h1 h2 => h1.trans h2) h₁ h₂

lemma SameView.mono {m' : ℕ} (h : SameView r r' i m) (hm : m' ≤ m) : SameView r r' i m' :=
  FIIndist.mono h hm

lemma SameView.input_eq (h : SameView r r' i m) : r.input i = r'.input i :=
  FIIndist.zero (I := fun q => r.input q = r'.input q) h

lemma SameView.of_seen (h : SameView r r' i m) (hs : Seen r j ℓ i m) : SameView r r' j ℓ :=
  (FIIndist.journey h hs).2

lemma SameView.seen (h : SameView r r' i m) (hs : Seen r j ℓ i m) : Seen r' j ℓ i m :=
  (FIIndist.journey h hs).1

lemma SameView.seen_iff (h : SameView r r' i m) : Seen r j ℓ i m ↔ Seen r' j ℓ i m :=
  ⟨h.seen, h.symm.seen⟩

lemma SameView.comm_iff {t : ℕ} (h : SameView r r' i (t + 1)) (q : P) :
    comm r t q i ↔ comm r' t q i := h.2.1 q

lemma SameView.deliv_iff {t : ℕ} (h : SameView r r' i (t + 1)) {q : P} (hq : q ≠ i) :
    r.Deliv q i t ↔ r'.Deliv q i t := by
  have := h.comm_iff q
  simp only [comm, ne_eq, hq, not_false_eq_true, true_and] at this
  exact this

lemma SameView.guarCrashed (h : SameView r r' i m) (hg : GuarCrashed r i m j ℓ) :
    GuarCrashed r' i m j ℓ := by
  obtain ⟨q, s, hs, hseen, hne, hd⟩ := hg
  refine ⟨q, s, hs, h.seen hseen, hne, fun hd' => hd ?_⟩
  exact ((h.of_seen hseen).deliv_iff (Ne.symm hne)).2 hd'

lemma SameView.hidden_iff (h : SameView r r' i m) : Hidden r i m j ℓ ↔ Hidden r' i m j ℓ := by
  unfold Hidden
  rw [h.seen_iff]
  exact ⟨fun ⟨a, b⟩ => ⟨a, fun hg => b (h.symm.guarCrashed hg)⟩,
    fun ⟨a, b⟩ => ⟨a, fun hg => b (h.guarCrashed hg)⟩⟩

variable [Fintype P] {k : ℕ}

lemma SameView.vals_eq (h : SameView r r' i m) : vals r i m = vals r' i m := by
  ext v
  simp only [mem_vals]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, h.seen hq, ((h.of_seen hq).input_eq).symm⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, h.symm.seen hq, ((h.symm.of_seen hq).input_eq).symm⟩

lemma SameView.minVal_eq (h : SameView r r' i m) : minVal r i m = minVal r' i m := by
  unfold minVal; congr 1; exact h.vals_eq

lemma SameView.lows_eq (h : SameView r r' i m) : lows k r i m = lows k r' i m := by
  unfold lows; rw [h.vals_eq]

lemma SameView.low_iff (h : SameView r r' i m) : Low k r i m ↔ Low k r' i m := by
  unfold Low; rw [h.vals_eq]

lemma SameView.hiddenAt_eq (h : SameView r r' i m) (ℓ : ℕ) :
    hiddenAt r i m ℓ = hiddenAt r' i m ℓ := by
  ext j; rw [mem_hiddenAt, mem_hiddenAt, h.hidden_iff]

lemma SameView.hc_eq (h : SameView r r' i m) : hc r i m = hc r' i m := by
  unfold hc; simp only [h.hiddenAt_eq]

omit [Fintype P] in
/-- **Locality.** Two adversaries give `⟨i, m⟩` the same view if they agree on the inputs of the
time-`0` nodes of the view and on the messages received by the nodes of the view. -/
lemma sameView_of_agree (hI : ∀ q, Seen r q 0 i m → r.input q = r'.input q)
    (hE : ∀ q s, Seen r q (s + 1) i m → ∀ w, w ≠ q → (r.Deliv w q s ↔ r'.Deliv w q s)) :
    SameView r r' i m := by
  refine FIIndist.of_agree hI fun q s hq w => ?_
  unfold comm
  by_cases hw : w = q
  · simp [hw]
  · simp only [ne_eq, hw, not_false_eq_true, true_and]; exact hE q s hq w hw

omit [Fintype P] in
/-- Adversaries that agree on the inputs and on the first `m` rounds give the same views at `m`. -/
lemma sameView_of_prefix (hI : ∀ q, r.input q = r'.input q)
    (hE : ∀ s < m, ∀ w q, r.Deliv w q s ↔ r'.Deliv w q s) (i : P) : SameView r r' i m :=
  sameView_of_agree (fun q _ => hI q) (fun q s hq w _ => hE s (by have := hq.le; omega) w q)

/-! ### Decisions are functions of the view -/

omit [Fintype P] in
lemma SameView.dec_eq (Q : Protocol P) {m' : ℕ} (h : SameView r r' i m) (hm : m' ≤ m) :
    Q.dec r i m' = Q.dec r' i m' :=
  Q.dec_congr r r' i m' (h.mono hm)

omit [Fintype P] in
lemma SameView.decidesAt_iff (Q : Protocol P) {m' v : ℕ} (h : SameView r r' i m) (hm : m' ≤ m)
    (ha : r.Alive i m' ↔ r'.Alive i m') : DecidesAt Q r i m' v ↔ DecidesAt Q r' i m' v := by
  unfold DecidesAt
  rw [ha, h.dec_eq Q hm]
  constructor
  · rintro ⟨a, b, c⟩
    exact ⟨a, b, fun n hn => (h.dec_eq Q (by omega)).symm.trans (c n hn)⟩
  · rintro ⟨a, b, c⟩
    exact ⟨a, b, fun n hn => (h.dec_eq Q (by omega)).trans (c n hn)⟩

omit [Fintype P] in
lemma SameView.decidesBy (Q : Protocol P) {m' : ℕ} (h : SameView r r' i m) (hm : m' ≤ m)
    (ha : r'.Alive i m) (hd : DecidesBy Q r i m') : DecidesBy Q r' i m' := by
  obtain ⟨n, hn, v, hv⟩ := hd
  exact ⟨n, hn, v, (h.decidesAt_iff Q (by omega)
    ⟨fun _ => ha.mono (by omega), fun _ => hv.1⟩).1 hv⟩

end SameView

/-! ### Decisions -/

section Decisions

variable {Q : Protocol P} {r : Run P} {i : P} {m v : ℕ}

lemma DecidesAt.unique {m' v' : ℕ} (h : DecidesAt Q r i m v) (h' : DecidesAt Q r i m' v') :
    m = m' ∧ v = v' := by
  have hm : m = m' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := h'.2.2 m hlt; rw [h.2.1] at this; cases this
    · have := h.2.2 m' hlt; rw [h'.2.1] at this; cases this
  subst hm
  refine ⟨rfl, ?_⟩
  have := h.2.1.symm.trans h'.2.1
  exact Option.some_injective _ this

/-- If the rule fires at a time when `i` is alive, `i` has decided by then. -/
lemma decidesBy_of_dec (ha : r.Alive i m) (hd : Q.dec r i m ≠ none) : DecidesBy Q r i m := by
  classical
  have hex : ∃ n, Q.dec r i n ≠ none := ⟨m, hd⟩
  let n := Nat.find hex
  have hn : Q.dec r i n ≠ none := Nat.find_spec hex
  have hnm : n ≤ m := Nat.find_min' hex hd
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hn
  refine ⟨n, hnm, v, ha.mono hnm, hv, fun n' hn' => ?_⟩
  by_contra h
  exact Nat.find_min hex hn' h

lemma DecidesBy.dec_ne_none_of_le {m' : ℕ} (h : DecidesBy Q r i m) (hm : m ≤ m') :
    ∃ n ≤ m', Q.dec r i n ≠ none := by
  obtain ⟨n, hn, v, hv⟩ := h
  exact ⟨n, by omega, by rw [hv.2.1]; simp⟩

end Decisions

end Podc.UnbeatableSetConsensus
