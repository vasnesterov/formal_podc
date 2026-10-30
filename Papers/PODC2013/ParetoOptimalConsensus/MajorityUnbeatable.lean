import Papers.PODC2013.ParetoOptimalConsensus.Time1

/-!
# Unbeatability of `OptMaj` (Lemmas 7, 8 and Theorem 3, Appendix A.1)

* **Lemma 7** (`lemma7`): `n > 2`, `t > 0`, `Q ⪰ OptMaj` solves consensus: if `K_i(Maj = v)` at
  time `1` (and `i` is alive then), `Q` makes `i` decide `v` by time `1`. Induction on
  `n - |Z_i|` (`Z_i` = processes with input `v` seen by `⟨i, 1⟩`) with the paper's three cases.
* **Lemma 8** (`lemma8`): `n > 2`, `t > 0`: if neither `K_i(Maj = 0)` nor `K_i(Maj = 1)` holds and
  there is a hidden path w.r.t. `⟨i, m⟩`, `i` does not decide at `m` in `Q`.
* **Theorem 3** (`theorem3`): for `t > 0`, `OptMaj` is unbeatable (`n = 1`: everybody decides at
  time `0`; `n = 2`: `OptMaj` coincides with `Opt1`; `n > 2`: Lemma 8).
-/

namespace Podc.ParetoOptimalConsensus

open Cslib Finset Podc.UnbeatableSetConsensus

variable {P : Type*} [Fintype P] {t : ℕ}


section Helpers

variable {Q : Protocol P} (hQ : SolvesSetConsensus 1 t bin Q) (hdom : Dominates t bin Q optMaj)

include hdom in
lemma decidesBy_of_kMaj {r : Run P} (hr : Adm t bin r) {j : P} {m v : ℕ} (hal : r.Alive j m)
    (hv : v ∈ bin) (hk : KMaj r j m v) : DecidesBy Q r j m := by
  obtain ⟨n, hn, u, hu⟩ := decidesBy_of_dec hal (optMaj_dec_ne_none_of_kMaj hv hk)
  exact DecidesBy.mono' (hdom r hr j n u hu) hn


end Helpers

/-! ### Lemma 7 -/

section Lemma7

variable {Q : Protocol P} (hn : 2 < Fintype.card P) (ht : 0 < t)
  (hQ : SolvesSetConsensus 1 t bin Q) (hdom : Dominates t bin Q optMaj)
  {v : ℕ} (hv : v ∈ bin)

/-- The threshold `c` with `Thr n v ℓ ↔ c ≤ ℓ`. -/
def thrMin (n v : ℕ) : ℕ := if v = 0 then n / 2 + 1 else (n + 1) / 2

lemma thr_iff {n v ℓ : ℕ} : Thr n v ℓ ↔ thrMin n v ≤ ℓ := by
  unfold Thr thrMin; split_ifs <;> omega

include hn ht hQ hdom hv in
/-- **Lemma 7** (decision at time 1). Let `n > 2`, `t > 0`, and let `Q ⪰ OptMaj` solve consensus.
If `K_i(Maj = v)` holds at time `1` (`i` alive), then `Q` makes `i` decide `v` by time `1`. -/
theorem lemma7 {r : Run P} (hr : Adm t bin r) {i : P} (hal : r.Alive i 1) (hk : KMaj r i 1 v) :
    ∃ m' ≤ 1, DecidesAt Q r i m' v := by
  have hc : 2 ≤ thrMin (Fintype.card P) v := by
    unfold thrMin; split_ifs <;> omega
  have hno := time1_forcing ht hQ hv hc (fun r hr p hp _ hZ =>
    decidesBy_of_kMaj hdom hr hp hv (thr_iff.2 hZ)) hr hal (thr_iff.1 hk)
  exact decides_of_no_opp hQ hr hv (decidesBy_of_kMaj hdom hr hal hv hk) hno

end Lemma7


/-! ### Lemma 8 -/

section RunSurgery

variable {r : Run P}

omit [Fintype P] in
/-- Changing only the round-1 reach sets does not change later rounds. -/
lemma modify_empty_deliv_succ {R : P → Set P} {q p : P} {s : ℕ} :
    (modify r ∅ R 0).Deliv q p (s + 1) ↔ r.Deliv q p (s + 1) := by
  have hc : (modify r ∅ R 0).crash q = r.crash q := modify_crash_of_not_mem (Set.notMem_empty q)
  rw [deliv_iff, deliv_iff]
  simp only [SyncCrash.Run.Alive, hc]
  have : (modify r ∅ R 0).reach q = if r.crash q = some 1 then R q else r.reach q := by
    simp [UnbeatableSetConsensus.modify]
  rw [this]
  split_ifs with h1
  · simp [h1]
  · rfl

omit [Fintype P] in
lemma chainRun_input_cases {ι : Type*} {x : P} {L : ℕ} {w : ℕ → ι → P} {u : ℕ} (p : P) :
    (chainRun r x L w (fun _ => u)).input p = u ∨ (chainRun r x L w (fun _ => u)).input p = r.input p := by
  simp only [chainRun]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

end RunSurgery

variable {Q : Protocol P} (hn : 2 < Fintype.card P) (ht : 0 < t)
  (hQ : SolvesSetConsensus 1 t bin Q) (hdom : Dominates t bin Q optMaj)

include hn ht hQ hdom in
/-- **Lemma 8** (no earlier decisions). Let `n > 2`, `t > 0`, and let `Q ⪰ OptMaj` solve consensus.
If neither `K_i(Maj = 0)` nor `K_i(Maj = 1)` holds at `m` and there is a hidden path w.r.t.
`⟨i, m⟩`, then `i` does not decide at `m` in `Q`. -/
theorem lemma8 {r : Run P} (hr : Adm t bin r) {i : P} {m : ℕ} (hal : r.Alive i m)
    (h0 : ¬ KMaj r i m 0) (h1 : ¬ KMaj r i m 1) (hp : HiddenPath r i m) (v : ℕ) :
    ¬ DecidesAt Q r i m v := by
  classical
  intro hd
  have hvb : v ∈ bin := mem_bin_of_mem_vals hr (dec_mem_vals' hQ hr hd)
  set w := 1 - v with hw
  have hwb : w ∈ bin := one_sub_mem_bin hvb
  have hww : 1 - w = v := by rcases hvb with rfl | rfl <;> rfl
  -- `Thr` for `w` when only `n - 1` processes are known to have it
  have hthr : ∀ c, Fintype.card P - (seenWith r i m v).card ≤ c → Thr (Fintype.card P) w c := by
    intro c hc
    unfold KMaj Thr at h0 h1
    unfold Thr
    rcases hvb with rfl | rfl
    · simp only [hw, Nat.sub_zero, one_ne_zero, ite_false, ite_true] at h0 h1 hc ⊢; omega
    · simp only [hw, Nat.sub_self, ite_true, one_ne_zero, ite_false] at h0 h1 hc ⊢; omega
  rcases m with _ | M
  · -- time `0`: a failure-free run in which everybody else has `w`
    set r' : Run P := ⟨fun p => if p = i then r.input i else w, fun _ => none, fun _ => ∅⟩
    have hall : ∀ p, ¬ r'.Faulty p := fun p => by simp [SyncCrash.Run.Faulty, r']
    have hr' : Adm t bin r' := ⟨⟨by simp [SyncCrash.Run.faulty, hall], fun p c hc => by
      simp [r'] at hc⟩, fun p => by simp only [r']; split_ifs; exacts [hr.2 i, hwb]⟩
    have hsv : SameView r r' i 0 := show r.input i = r'.input i by simp [r']
    have hk : KMaj r' i 1 w := by
      unfold KMaj
      refine hthr _ (le_trans ?_ (card_le_card (s := univ \ seenWith r i 0 v) fun q hq => ?_))
      · rw [card_sdiff_of_subset (subset_univ _), card_univ]
      · rw [mem_sdiff, mem_seenWith] at hq
        rw [mem_seenWith, seen_zero_one_iff]
        by_cases hqi : q = i
        · subst hqi
          refine ⟨Or.inl rfl, ?_⟩
          simp only [r', ite_true]
          rcases eq_or_eq_one_sub hvb (hr.2 q) with h | h
          · exact absurd ⟨seen_self le_rfl, h⟩ hq.2
          · exact h
        · refine ⟨Or.inr ⟨hqi, SyncCrash.Run.deliv_of_not_faulty (hall q) i 0⟩, ?_⟩
          simp [r', hqi]
    obtain ⟨m', -, hd'⟩ := lemma7 hn ht hQ hdom hwb hr' (SyncCrash.Run.alive_of_not_faulty (hall i) 1) hk
    have hd0 : DecidesAt Q r' i 0 v :=
      (hsv.decidesAt_iff Q le_rfl ⟨fun _ => SyncCrash.Run.alive_of_not_faulty (hall i) 0,
        fun _ => hd.1⟩).1 hd
    obtain ⟨-, h⟩ := hd0.unique hd'
    exact one_sub_ne hvb h.symm
  set m := M + 1 with hm
  -- unseen inputs become `w`
  set r₁ := replaceUnseen r i m w
  have hsv₁ : SameView r r₁ i m := replaceUnseen_sameView r i m w
  have hr₁ : Adm t bin r₁ := by
    refine ⟨hr.1, fun p => ?_⟩
    simp only [r₁, replaceUnseen]; split_ifs
    · exact hr.2 p
    · exact hwb
  obtain ⟨b, hb⟩ := (hiddenPath_iff_of_sameView hsv₁).1 hp
  set wc : ℕ → Unit → P := fun ℓ _ => b ℓ
  have H : ChainHyp r₁ i m m wc :=
    ⟨le_rfl, fun ℓ _ x y _ => Subsingleton.elim x y, fun ℓ hℓ _ => hb ℓ hℓ⟩
  -- the chain run along the hidden path, with value `w`
  set r₂ := chainRun r₁ i m wc (fun _ => w)
  have hsv₂ : SameView r₁ r₂ i m := H.sameView
  -- `⟨b 1, 1⟩` hears from everybody in round 1
  set r₃ := modify r₂ ∅ (fun p => insert (b 1) (r₂.reach p)) 0
  have hcr₃ : ∀ p, r₃.crash p = r₂.crash p := fun p => modify_crash_of_not_mem (Set.notMem_empty p)
  have hd₃0 : ∀ q p, p ≠ b 1 → (r₃.Deliv q p 0 ↔ r₂.Deliv q p 0) := by
    intro q p hp
    rw [modify_deliv_last, deliv_iff]
    simp only [Set.mem_empty_iff_false, false_or, Set.mem_insert_iff, hp, false_or]
  have hd₃b : ∀ q, r₃.Deliv q (b 1) 0 := by
    intro q
    rw [modify_deliv_last]
    refine Or.inr ⟨?_, fun h => h.2 (Set.mem_insert _ _)⟩
    intro c hc
    exact H.crash_pos hr₁ hc
  have hb1 : ¬ Seen r₁ (b 1) 1 i m := (hb 1 (by omega)).1
  have hsv₃ : SameView r₂ r₃ i m := by
    refine sameView_of_agree (fun q _ => rfl) (fun h s hs q _ => ?_)
    rcases s with _ | s
    · have hh : h ≠ b 1 := by rintro rfl; exact hb1 (hsv₂.symm.seen hs)
      exact (hd₃0 q h hh).symm
    · exact modify_empty_deliv_succ.symm
  -- make `i` and `b m` correct
  have hai₃ : r₃.Alive i m := by
    intro c hc; rw [hcr₃] at hc
    exact (H.alive_iff_of_seen (seen_self le_rfl) le_rfl).2 hal c hc
  have hab₃ : ∀ ℓ ≤ m, r₃.Alive (b ℓ) ℓ := by
    intro ℓ hℓ c hc; rw [hcr₃] at hc; exact H.alive_w hℓ () c hc
  set K : Set P := {i, b m}
  have hK : ∀ p ∈ K, r₃.Alive p m := by
    rintro p (rfl | rfl)
    · exact hai₃
    · exact hab₃ m le_rfl
  set r₄ := modify r₃ K r₃.reach m
  have hsv₄ : ∀ p, SameView r₃ r₄ p m := modify_sameView hK le_rfl
  have hsv : SameView r r₄ i m := ((hsv₁.trans hsv₂).trans hsv₃).trans (hsv₄ i)
  have hr₄ : Adm t bin r₄ := by
    refine ⟨⟨le_trans (card_le_card fun p hp => ?_) hr.1.1, fun p c hc => ?_⟩, fun p => ?_⟩
    · rw [SyncCrash.Run.mem_faulty] at hp ⊢
      have hpK : p ∉ K := fun hpK => modify_not_faulty hpK hp
      have hp₃ := modify_faulty hp
      have hp₂ : r₂.Faulty p := by unfold SyncCrash.Run.Faulty at hp₃ ⊢; rwa [hcr₃] at hp₃
      rcases H.faulty_of hp₂ with h | ⟨_, rfl⟩
      · exact h
      · exact absurd (Or.inr rfl) hpK
    · by_cases hpK : p ∈ K
      · rw [modify_crash_of_mem hpK] at hc; cases hc
      · rw [modify_crash_of_not_mem hpK, hcr₃] at hc; exact H.crash_pos hr₁ hc
    · exact ChainHyp.input_mem (x := i) (L := m) hr₁ (fun _ => hwb) p
  have hic : ¬ r₄.Faulty i := modify_not_faulty (Or.inl rfl)
  have hbc : ¬ r₄.Faulty (b m) := modify_not_faulty (Or.inr rfl)
  -- facts about `r₄`
  have hdl₄ : ∀ s < m, ∀ q p, r₄.Deliv q p s ↔ r₃.Deliv q p s := fun s hs q p =>
    modify_deliv_lt hK hs q p
  have hab₄ : ∀ ℓ ≤ m, r₄.Alive (b ℓ) ℓ := fun ℓ hℓ => modify_alive (hab₃ ℓ hℓ)
  have hchain : ∀ ℓ < m, r₄.Deliv (b ℓ) (b (ℓ + 1)) ℓ := by
    intro ℓ hℓ
    rw [hdl₄ ℓ hℓ]
    rcases ℓ with _ | ℓ
    · exact hd₃b _
    · rw [modify_empty_deliv_succ]
      exact (H.deliv_w (ℓ := ℓ + 1) hℓ.le () _).2 (Or.inr ⟨rfl, hℓ, rfl⟩)
  have hne : ∀ ℓ < m, b ℓ ≠ b (ℓ + 1) := fun ℓ hℓ => H.ne_succ hℓ ()
  have hseenb : ∀ ℓ₁ ℓ₂, ℓ₁ ≤ ℓ₂ → ℓ₂ ≤ m → Seen r₄ (b ℓ₁) ℓ₁ (b ℓ₂) ℓ₂ := by
    intro ℓ₁ ℓ₂ h12 h2
    induction ℓ₂ with
    | zero => obtain rfl : ℓ₁ = 0 := by omega
              exact seen_self le_rfl
    | succ ℓ ih =>
      rcases Nat.lt_or_eq_of_le h12 with hlt | rfl
      · exact (ih (by omega) (by omega)).trans
          (seen_of_deliv (hne ℓ (by omega)) (hchain ℓ (by omega)))
      · exact seen_self le_rfl
  -- `⟨b 1, 1⟩` knows `Maj = w`
  have hinput : ∀ q, r₄.input q ≠ w → q ∈ seenWith r i m v := by
    intro q hq
    have h₂ : r₂.input q = r₄.input q := rfl
    rcases chainRun_input_cases (r := r₁) (x := i) (L := m) (w := wc) (u := w) q with h | h
    · exact absurd (h₂ ▸ h) hq
    · rw [← h₂, h] at hq
      simp only [r₁, replaceUnseen] at hq
      split_ifs at hq with hs
      · rw [mem_seenWith]
        refine ⟨hs, ?_⟩
        rcases eq_or_eq_one_sub hvb (hr.2 q) with h' | h'
        · exact h'
        · exact absurd h' hq
      · exact absurd rfl hq
  have hk1 : KMaj r₄ (b 1) 1 w := by
    unfold KMaj
    refine hthr _ ?_
    have hsub : univ \ seenWith r i m v ⊆ seenWith r₄ (b 1) 1 w := by
      intro q hq
      rw [mem_sdiff] at hq
      rw [mem_seenWith, seen_zero_one_iff]
      refine ⟨?_, ?_⟩
      · by_cases hqb : q = b 1
        · exact Or.inl hqb
        · exact Or.inr ⟨hqb, (hdl₄ 0 (by omega) q (b 1)).2 (hd₃b q)⟩
      · by_contra h; exact hq.2 (hinput q h)
    have := card_le_card hsub
    rw [card_sdiff_of_subset (subset_univ _), card_univ] at this
    exact this
  have hkb : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ m → KMaj r₄ (b ℓ) ℓ w := fun ℓ h1 h2 =>
    hk1.of_seen (hseenb 1 ℓ h1 h2)
  -- every `b ℓ` (`1 ≤ ℓ ≤ m`) decides `w` by time `ℓ`
  have hdecb : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ m → ∃ m' ≤ ℓ, DecidesAt Q r₄ (b ℓ) m' w := by
    intro ℓ h1 h2
    induction ℓ with
    | zero => omega
    | succ ℓ ih =>
      rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
      · exact lemma7 hn ht hQ hdom hwb hr₄ (hab₄ 1 h2) hk1
      obtain ⟨n₁, hn₁, hd₁⟩ := ih hpos (by omega)
      set K' : Set P := {b ℓ, b (ℓ + 1)}
      have hK' : ∀ p ∈ K', r₄.Alive p ℓ := by
        rintro p (rfl | rfl)
        · exact hab₄ ℓ (by omega)
        · exact (hab₄ (ℓ + 1) h2).mono (Nat.le_succ ℓ)
      set r'' := modify r₄ K' r₄.reach ℓ
      have hr'' : Adm t bin r'' := modify_admissible hr₄
      have hsvb : SameView r₄ r'' (b (ℓ + 1)) (ℓ + 1) := by
        refine modify_sameView_last hK' (fun p hp hpb => ?_) (fun _ _ => Iff.rfl)
        rcases hp with rfl | rfl
        · exact hchain ℓ (by omega)
        · exact absurd rfl hpb
      have hsvb' : SameView r₄ r'' (b ℓ) ℓ := modify_sameView hK' le_rfl _
      have hc1 : ¬ r''.Faulty (b ℓ) := modify_not_faulty (Or.inl rfl)
      have hc2 : ¬ r''.Faulty (b (ℓ + 1)) := modify_not_faulty (Or.inr rfl)
      obtain ⟨n₂, hn₂, w₂, hd₂⟩ := hsvb'.decidesBy Q hn₁
        (SyncCrash.Run.alive_of_not_faulty hc1 ℓ) ⟨n₁, le_rfl, w, hd₁⟩
      have hd₂' : DecidesAt Q r'' (b ℓ) n₂ w := by
        have := (hsvb'.decidesAt_iff Q (hn₂.trans hn₁) ⟨fun _ =>
          SyncCrash.Run.alive_of_not_faulty hc1 _, fun _ => (hab₄ ℓ (by omega)).mono
          (hn₂.trans hn₁)⟩).2 hd₂
        obtain ⟨rfl, rfl⟩ := this.unique hd₁
        exact hd₂
      have hno := no_opp_of_witness hQ hr'' hwb (sameView_refl r'' (b (ℓ + 1)) (ℓ + 1)) hc2 hc1
        ⟨n₂, hd₂'⟩
      obtain ⟨m', hm', hd'⟩ := decides_of_no_opp hQ hr'' hwb
        (decidesBy_of_kMaj hdom hr'' (SyncCrash.Run.alive_of_not_faulty hc2 _) hwb
          ((SameView.kMaj_iff hsvb).1 (hkb (ℓ + 1) h1 h2))) hno
      exact ⟨m', hm', (hsvb.decidesAt_iff Q hm' ⟨fun _ => SyncCrash.Run.alive_of_not_faulty hc2 _,
        fun _ => (hab₄ (ℓ + 1) h2).mono hm'⟩).2 hd'⟩
  obtain ⟨m', -, hdm⟩ := hdecb m (by omega) le_rfl
  have := no_opp_of_witness hQ hr₄ hwb hsv hic hbc ⟨m', hdm⟩ m le_rfl
  rw [hww] at this
  exact this hd

/-! ### Theorem 3 -/

omit [Fintype P] in
lemma kMaj_card_two [Fintype P] (h2 : Fintype.card P = 2) {r : Run P} {i : P} {m : ℕ} :
    KMaj r i m 0 ↔ seenWith r i m 0 = univ := by
  unfold KMaj Thr
  simp only [ite_true, h2]
  constructor
  · intro h; exact eq_univ_of_card _ (by have := card_le_univ (seenWith r i m 0); omega)
  · intro h; rw [h, card_univ, h2]; omega

/-- For `n = 2`, `OptMaj` coincides with `Opt1`. -/
lemma optMaj_eq_opt1 (h2 : Fintype.card P = 2) : EqOnAdm t bin (optMaj : Protocol P) opt1 := by
  classical
  intro r hr i m
  have hk1 : KMaj r i m 1 ↔ 1 ∈ vals r i m := by
    unfold KMaj Thr; simp only [one_ne_zero, ite_false, h2]
    rw [mem_vals]
    constructor
    · intro h
      obtain ⟨q, hq⟩ := card_pos.1 (show 0 < (seenWith r i m 1).card by omega)
      exact ⟨q, (mem_seenWith.1 hq).1, (mem_seenWith.1 hq).2⟩
    · rintro ⟨q, hq, hq1⟩
      have := card_pos.2 ⟨q, mem_seenWith.2 ⟨hq, hq1⟩⟩; omega
  simp only [optMaj, optA, hk1]
  by_cases h0 : KMaj r i m 0
  · have huniv := (kMaj_card_two h2).1 h0
    have hall : ∀ q, Seen r q 0 i m ∧ r.input q = 0 := fun q => mem_seenWith.1 (huniv ▸ mem_univ q)
    have h1 : 1 ∉ vals r i m := by
      intro h; obtain ⟨q, -, hq⟩ := mem_vals.1 h; rw [(hall q).2] at hq; exact zero_ne_one hq
    have hnp : ¬ HiddenPath r i m := not_hiddenPath_iff.2 ⟨0, Nat.zero_le m, fun q hq =>
      hq.1 (hall q).1⟩
    simp [h0, h1, hnp]
  · simp only [h0, ite_false]
    by_cases h1 : 1 ∈ vals r i m
    · simp [h1]
    · simp only [h1, ite_false]
      by_cases hnp : HiddenPath r i m
      · simp [hnp]
      · simp only [hnp, not_false_eq_true, ite_true, Option.some.injEq]
        unfold majv
        have hc := card_seenAll (i := i) (m := m) hr
        have hz : (seenWith r i m 1).card = 0 := by
          rw [card_eq_zero, eq_empty_iff_forall_notMem]
          intro q hq; exact h1 (mem_vals.2 ⟨q, (mem_seenWith.1 hq).1, (mem_seenWith.1 hq).2⟩)
        have hpos : 0 < (seenAll r i m).card :=
          card_pos.2 ⟨i, mem_seenAll.2 (seen_self (Nat.zero_le m))⟩
        rw [ite_eq_left (by omega)]

omit hn hQ hdom in
include ht in
/-- **Theorem 3.** If `t > 0`, `OptMaj` is an unbeatable consensus protocol in `γ_cr` (every
`n ≥ 1`). -/
theorem theorem3 : Unbeatable 1 t bin (optMaj : Protocol P) := by
  classical
  rcases Nat.lt_or_ge (Fintype.card P) 3 with hlt | hge
  · rcases Nat.lt_or_ge (Fintype.card P) 2 with hlt' | hge'
    · -- `n = 1`: everybody decides at time `0`
      refine ⟨optMaj_solves, fun Q _ _ r hr i m v hv => ?_⟩
      have hall : ∀ q, q = i := fun q => by
        have := Fintype.card_le_one_iff.1 (by omega : Fintype.card P ≤ 1); exact this q i
      have hk : KMaj r i 0 (r.input i) := by
        unfold KMaj Thr
        have hs : seenWith r i 0 (r.input i) = univ := by
          ext q; rw [mem_seenWith, hall q]; simp [seen_self]
        rw [hs, card_univ]
        have : 0 < Fintype.card P := Fintype.card_pos_iff.2 ⟨i⟩
        split_ifs <;> omega
      exact DecidesBy.mono' (decidesBy_of_dec (hv.1.mono (Nat.zero_le m))
        (optMaj_dec_ne_none_of_kMaj (hr.2 i) hk)) (Nat.zero_le m)
    · -- `n = 2`: `OptMaj = Opt1`
      exact (optMaj_eq_opt1 (by omega)).symm.unbeatable opt1_unbeatable
  · refine ⟨optMaj_solves, fun Q hQ hdom r hr i m v hv => ?_⟩
    by_contra hn'
    have hnone : optMaj.dec r i m = none := by
      by_contra hne; exact hn' (decidesBy_of_dec hv.1 hne)
    obtain ⟨h0, h1, hp⟩ := optMaj_dec_eq_none.1 hnone
    exact lemma8 (by omega) ht hQ hdom hr hv.1 h0 h1 hp v hv

end Podc.ParetoOptimalConsensus

