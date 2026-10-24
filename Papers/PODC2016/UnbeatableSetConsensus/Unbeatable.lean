import Papers.PODC2016.UnbeatableSetConsensus.Lemma1
import Papers.PODC2016.UnbeatableSetConsensus.Optmin

/-!
# Unbeatability of `Optmin[k]` (Lemma 3, Theorem 1, Lemma 5, Theorem 2)

* **Lemma 3** (`lemma3`): if `Q` solves nonuniform `k`-set consensus and every low process decides
  by the time it is low, then no live high process with hidden capacity `≥ k` decides
  (`Q.dec r x m = none`). Proof as in the paper: the run of Lemma 2 for all `k` low values, with
  `x` and the last witnesses made correct, in which the corrected Lemma 1 applies to each last
  witness (hypothesis 5 holds there because `x` is high at `m`).
* **Theorem 1** (`theorem1`): `Optmin[k]` is unbeatable.
* **Lemma 5** (`lemma5`): a solution that last-decider dominates `Optmin[k]` makes every low
  process decide by the time it is low.
* **Theorem 2** (`theorem2`): `Optmin[k]` is last-decider unbeatable.
-/

namespace Podc.UnbeatableSetConsensus

open Cslib Finset

variable {P : Type*} [Fintype P] {k t : ℕ} {D : Set ℕ} {Q : Protocol P}

omit [Fintype P] in
lemma DecidesBy.mono {r : Run P} {i : P} {m m' : ℕ} (h : DecidesBy Q r i m) (hm : m ≤ m') :
    DecidesBy Q r i m' := by
  obtain ⟨n, hn, v, hv⟩ := h
  exact ⟨n, hn.trans hm, v, hv⟩

section Lemma3

variable (hk : 1 ≤ k) (hD : ∀ v ≤ k, v ∈ D) (hQ : SolvesSetConsensus k t D Q)
  (hlow : LowDecides k t D Q)
include hk hD hQ hlow

/-- **Lemma 3.** In a protocol solving nonuniform `k`-set consensus in which every low process
decides by the time it is low, a (live) high process with hidden capacity `≥ k` does not decide. -/
theorem lemma3 {r : Run P} (hr : Adm t D r) {x : P} {m : ℕ} (ha : r.Alive x m)
    (hhigh : ¬ Low k r x m) (hhc : k ≤ hc r x m) : Q.dec r x m = none := by
  classical
  set E := range k
  have hcardE : Fintype.card E = k := by rw [Fintype.card_coe, card_range]
  obtain ⟨w, hw⟩ := exists_witnesses (r := r) (i := x) (m := m) (ι := E) (hcardE ▸ hhc)
  have H : ChainHyp r x m m w := ⟨le_rfl, fun ℓ hℓ => (hw ℓ hℓ).1, fun ℓ hℓ => (hw ℓ hℓ).2⟩
  set r₀ := chainRun r x m w (fun b => b.1)
  have hsv₀ : SameView r r₀ x m := H.sameView
  have hxs : Seen r x m x m := seen_self le_rfl
  set K : Set P := insert x (Set.range (w m))
  have hK : ∀ p ∈ K, r₀.Alive p m := by
    rintro p (rfl | ⟨b, rfl⟩)
    · exact (H.alive_iff_of_seen hxs le_rfl).2 ha
    · exact H.alive_w le_rfl b
  set r₁ := modify r₀ K r₀.reach m
  have hsv₁ : ∀ p, SameView r₀ r₁ p m := modify_sameView hK le_rfl
  have hsv : SameView r r₁ x m := hsv₀.trans (hsv₁ x)
  have hr₁ : Adm t D r₁ := by
    refine ⟨⟨le_trans (card_le_card fun p hp => ?_) hr.1.1, fun p c hc => ?_⟩, fun p => ?_⟩
    · rw [SyncCrash.Run.mem_faulty] at hp ⊢
      have hpK : p ∉ K := fun hpK => modify_not_faulty hpK hp
      rcases H.faulty_of (modify_faulty hp) with h | ⟨b, rfl⟩
      · exact h
      · exact absurd (Or.inr ⟨b, rfl⟩) hpK
    · by_cases hpK : p ∈ K
      · rw [modify_crash_of_mem hpK] at hc; cases hc
      · rw [modify_crash_of_not_mem hpK] at hc; exact H.crash_pos hr hc
    · exact ChainHyp.input_mem (x := x) (L := m) hr (fun b => hD _ (mem_range.1 b.2).le) p
  have hcor : ∀ p ∈ K, ¬ r₁.Faulty p := fun p hp => modify_not_faulty hp
  have hxw : ∀ b, w m b ≠ x := fun b => H.not_w_of_seen hxs le_rfl b
  -- nodes of the last witnesses one round earlier are seen by `⟨x, m⟩`, hence high
  have hhighw : ∀ b M, m = M + 1 → ¬ Low k r₁ (w m b) M := by
    intro b M hM hl
    subst hM
    have hs := (H.hidden (M + 1) le_rfl b).seen_pred le_rfl
    rw [← ((hsv₁ _).mono (Nat.le_succ M)).low_iff, ← (hsv₀.of_seen (H.sameView.symm.seen
      (hsv₀.seen hs))).low_iff] at hl
    exact hhigh (hl.of_seen hs)
  have hhighx : ∀ M, m = M + 1 → ¬ Low k r₁ x M := by
    intro M hM hl
    rw [← (hsv.mono (by omega)).low_iff] at hl
    exact hhigh (hl.mono (by omega))
  -- every last witness decides its own low value
  have hdec : ∀ b : E, DecidesAt Q r₁ (w m b) m b.1 := by
    intro b
    -- the `k` processes `x` and `w m b'` (`b' ≠ b`)
    set e : Fin k ≃ E := (Fintype.equivFinOfCardEq hcardE).symm
    set j : Fin k → P := fun c => if e c = b then x else w m (e c)
    have hjinj : Function.Injective j := by
      intro c c' hcc
      simp only [j] at hcc
      split_ifs at hcc with h1 h2 h2
      · exact e.injective (h1.trans h2.symm)
      · exact absurd hcc.symm (hxw _)
      · exact absurd hcc (hxw _)
      · exact e.injective ((hw m le_rfl).1 hcc)
    refine lemma1 hk hD hQ hlow m r₁ (w m b) b.1 hr₁ ⟨⟨?_, hhighw b, ?_, ?_, ⟨j, hjinj,
      fun c => ⟨?_, ?_⟩⟩⟩, ?_⟩
    · exact SyncCrash.Run.alive_of_not_faulty (hcor _ (Or.inr ⟨b, rfl⟩)) m
    · rw [← (hsv₁ _).lows_eq]
      refine Subset.antisymm (fun y hy => ?_) (singleton_subset_iff.2
        (mem_lows.2 ⟨H.mem_vals le_rfl b, mem_range.1 b.2⟩))
      obtain ⟨hy1, hy2⟩ := mem_lows.1 hy
      rcases mem_insert.1 (H.vals_subset le_rfl b hy1) with h' | h'
      · exact mem_singleton.2 h'
      · exact absurd ⟨y, h', hy2⟩ hhigh
    · rw [← (hsv₁ _).hc_eq, le_hc_iff]
      intro ℓ hℓ
      have : k - 1 ≤ ((univ.erase b).image (w ℓ)).card := by
        rw [card_image_of_injective _ (hw ℓ hℓ).1, card_erase_of_mem (mem_univ _), card_univ,
          hcardE]
      refine this.trans (card_le_card fun p hp => ?_)
      obtain ⟨b', hb', rfl⟩ := mem_image.1 hp
      exact mem_hiddenAt.2 (H.hidden_col le_rfl hℓ (Ne.symm (ne_of_mem_erase hb')))
    · intro M hM
      simp only [j]; split_ifs
      · exact hhighx M hM
      · exact hhighw _ M hM
    · have hjK : j c ∈ K := by
        simp only [j]; split_ifs
        · exact Or.inl rfl
        · exact Or.inr ⟨_, rfl⟩
      refine hidden_now_of_alive (SyncCrash.Run.alive_of_not_faulty (hcor _ hjK) m) ?_
      simp only [j]; split_ifs with h1
      · exact (hxw b).symm
      · intro he; exact h1 ((hw m le_rfl).1 he)
    · intro M hM y hy hl
      rw [hM]
      exact crash_eq_of_low_of_high (z := x)
        (fun hlx => hhigh (hsv.low_iff.2 (by rw [hM]; exact hlx))) hy hl
  -- so all low values are decided by correct processes, and `x` cannot decide
  have hall : ∀ u < k, ∃ i m', ¬ r₁.Faulty i ∧ DecidesAt Q r₁ i m' u :=
    fun u hu => ⟨w m ⟨u, mem_range.2 hu⟩, m, hcor _ (Or.inr ⟨_, rfl⟩), hdec ⟨u, mem_range.2 hu⟩⟩
  by_contra hne
  rw [hsv.dec_eq Q le_rfl] at hne
  have hcx : ¬ r₁.Faulty x := hcor x (Or.inl rfl)
  obtain ⟨m', hm', u, hd⟩ := decidesBy_of_dec (SyncCrash.Run.alive_of_not_faulty hcx m) hne
  have huk := not_high_of_all_low hQ hr₁ hall hcx hd
  have hu : u ∈ vals r x m := by
    rw [hsv.vals_eq]; exact vals_mono hm' (dec_mem_vals hk hD hQ hr₁ hd)
  exact hhigh ⟨u, hu, huk⟩

/-- Consequently, such a protocol never decides earlier than `Optmin[k]`. -/
theorem optmin_dominates : Dominates t D (optmin k) Q := by
  intro r hr i m v hd
  by_contra hn
  have hnone : (optmin k).dec r i m = none := by
    by_contra hne; exact hn (decidesBy_of_dec hd.1 hne)
  obtain ⟨h1, h2⟩ := optmin_dec_eq_none.1 hnone
  have hhigh : ¬ Low k r i m := by rw [low_iff_minVal]; omega
  have hdec := hd.2.1
  rw [lemma3 hk hD hQ hlow hr hd.1 hhigh h2] at hdec
  exact absurd hdec (by simp)

end Lemma3

/-- A protocol that dominates `Optmin[k]` makes low processes decide at once. -/
lemma lowDecides_of_dominates (hdom : Dominates t D Q (optmin k)) : LowDecides k t D Q := by
  intro r hr i m ha hl
  obtain ⟨m', hm', v, hd⟩ := optmin_decidesBy_of_low ha hl
  exact (hdom r hr i m' v hd).mono hm'

/-- **Theorem 1.** `Optmin[k]` is an unbeatable protocol for nonuniform `k`-set consensus in the
synchronous crash failure model (for every `n`, every bound `t` on the number of crashes, and
every set `D ⊇ {0, …, k}` of initial values). -/
theorem theorem1 (hk : 1 ≤ k) (hD : ∀ v ≤ k, v ∈ D) :
    Unbeatable k t D (optmin k : Protocol P) :=
  ⟨optmin_solves hk, fun _ hQ hdom =>
    optmin_dominates hk hD hQ (lowDecides_of_dominates hdom)⟩

/-! ### Last-decider unbeatability -/

/-- Domination implies last-decider domination (Remark 2). -/
lemma ldDominates_of_dominates {Q' P' : Protocol P} (h : Dominates t D Q' P') :
    LDDominates t D Q' P' := by
  intro r hr m hall i hi
  obtain ⟨m', hm', v, hd⟩ := hall i hi
  exact (h r hr i m' v hd).mono hm'

/-- **Lemma 5.** A protocol that last-decider dominates `Optmin[k]` makes every low process decide
by the time it is low. -/
theorem lemma5 (hld : LDDominates t D Q (optmin k)) : LowDecides k t D Q := by
  classical
  intro r hr i m ha hl
  cases m with
  | zero =>
    -- all inputs equal to `i`'s low input, no failures
    set r' : Run P := { input := fun _ => r.input i, crash := fun _ => none, reach := fun _ => ∅ }
    have hcor : ∀ p, ¬ r'.Faulty p := fun p => by simp [SyncCrash.Run.Faulty, r']
    have hr' : Adm t D r' := ⟨⟨by simp [SyncCrash.Run.faulty, hcor], fun p c hc => by
      simp [r'] at hc⟩, fun _ => hr.2 i⟩
    have hsv : SameView r' r i 0 := show r'.input i = r.input i from rfl
    have hlow' : ∀ p, Low k r' p 0 := by
      intro p
      obtain ⟨v, hv, hvk⟩ := hl
      rw [vals_zero, mem_singleton] at hv
      exact ⟨r.input i, by rw [vals_zero]; exact mem_singleton_self _, hv ▸ hvk⟩
    have := hld r' hr' 0 (fun p hp => optmin_decidesBy_of_low
      (SyncCrash.Run.alive_of_not_faulty hp 0) (hlow' p)) i (hcor i)
    exact hsv.decidesBy Q le_rfl ha this
  | succ M =>
    -- a low process `z` whose time-`M` node is seen by `⟨i, M + 1⟩`
    obtain ⟨z, hzs, hzl, hza⟩ : ∃ z, Seen r z M i (M + 1) ∧ Low k r z M ∧ r.Alive z M := by
      by_cases hiM : Low k r i M
      · exact ⟨i, seen_self (Nat.le_succ M), hiM, ha.mono (Nat.le_succ M)⟩
      · obtain ⟨u, hu, huk⟩ := hl
        rcases mem_vals_succ.1 hu with hu | ⟨q, hq, hu⟩
        · exact absurd ⟨u, hu, huk⟩ hiM
        · exact ⟨q, seen_of_comm hq, ⟨u, hu, huk⟩, hq.2.1⟩
    set K : Set P := {i, z}
    have hK : ∀ p ∈ K, r.Alive p M := by
      rintro p (rfl | rfl)
      · exact ha.mono (Nat.le_succ M)
      · exact hza
    set r' := modify r K r.reach M
    have hsv : SameView r r' i (M + 1) := by
      refine modify_sameView_last hK (fun p hp hpi => ?_) (fun _ _ => Iff.rfl)
      rcases hp with rfl | rfl
      · exact absurd rfl hpi
      · exact hzs.deliv_of_succ hpi
    have hr' : Adm t D r' := modify_admissible hr
    have hzc : ¬ r'.Faulty z := modify_not_faulty (Or.inr rfl)
    have hzl' : Low k r' z M := by rw [← (modify_sameView hK le_rfl z).low_iff]; exact hzl
    have hall : ∀ p, ¬ r'.Faulty p → DecidesBy (optmin k) r' p (M + 1) := by
      intro p hp
      refine optmin_decidesBy_of_low (SyncCrash.Run.alive_of_not_faulty hp _) ?_
      by_cases hpz : p = z
      · rw [hpz]; exact hzl'.mono (Nat.le_succ M)
      · exact hzl'.of_seen (seen_of_deliv (Ne.symm hpz) (SyncCrash.Run.deliv_of_not_faulty hzc p M))
    have := hld r' hr' (M + 1) hall i (modify_not_faulty (Or.inl rfl))
    exact hsv.symm.decidesBy Q le_rfl ha this

/-- **Theorem 2.** `Optmin[k]` is last-decider unbeatable for nonuniform `k`-set consensus. -/
theorem theorem2 (hk : 1 ≤ k) (hD : ∀ v ≤ k, v ∈ D) :
    LDUnbeatable k t D (optmin k : Protocol P) :=
  ⟨optmin_solves hk, fun _ hQ hld =>
    ldDominates_of_dominates (optmin_dominates hk hD hQ (lemma5 hld))⟩

end Podc.UnbeatableSetConsensus
