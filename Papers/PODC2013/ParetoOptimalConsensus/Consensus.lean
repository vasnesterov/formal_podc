import Papers.PODC2013.ParetoOptimalConsensus.Defs

/-!
# Unbeatable consensus: Lemma 2, Lemma 3, Theorem 2 (§3)

* **Lemma 2** (`lemma2`): if `Q ⪰ P_a` solves consensus, every live process decides `a` in `Q` at
  the first time it knows `∃a`.
* The run of a hidden path (`exists_run_of_hiddenPath`, Lemma 9 of the paper for `c = 1`): if
  there is a hidden path w.r.t. `⟨i, m⟩`, some run with the same view for `i` has a correct
  process that knows `∃a` at `m`, and `i` correct.
* **Lemma 3** (`lemma3`): `K_i(never-known(∃a))` iff `¬K_i∃a` and there is no hidden path.
* **Theorem 2** (`theorem2`): `Opt0` (more generally `Opt_a`, `a ∈ {0, 1}`) is an unbeatable
  consensus protocol.

The paper states everything for `a = 0`; the case `a = 1` (the protocol `Opt1` of §3.1) is the
same proof with the values swapped, and is used for majority consensus with `n = 2`.
-/

namespace Podc.ParetoOptimalConsensus

open Cslib Finset Podc.UnbeatableSetConsensus

variable {P : Type*} [Fintype P] {t a : ℕ}

/-- `i` knows `∃a` at `m` for the first time. -/
def FirstKnows (r : Run P) (i : P) (m a : ℕ) : Prop :=
  a ∈ vals r i m ∧ ∀ M, m = M + 1 → a ∉ vals r i M

lemma FirstKnows.not_mem_of_lt {r : Run P} {i : P} {m a m' : ℕ} (h : FirstKnows r i m a)
    (hm : m' < m) : a ∉ vals r i m' := by
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  exact fun hv => h.2 M rfl (vals_mono (by omega) hv)

lemma SameView.firstKnows_iff {r r' : Run P} {i : P} {m a : ℕ} (h : SameView r r' i m) :
    FirstKnows r i m a ↔ FirstKnows r' i m a := by
  unfold FirstKnows
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h.vals_eq ▸ h1, fun M hM => ?_⟩
    rw [← (h.mono (by omega)).vals_eq]; exact h2 M hM
  · rintro ⟨h1, h2⟩
    refine ⟨h.vals_eq ▸ h1, fun M hM => ?_⟩
    rw [(h.mono (by omega)).vals_eq]; exact h2 M hM

/-- If `a` is known at `m`, it is known for the first time at some `m₀ ≤ m`. -/
lemma exists_firstKnows {r : Run P} {i : P} {m a : ℕ} (h : a ∈ vals r i m) :
    ∃ m₀ ≤ m, FirstKnows r i m₀ a := by
  classical
  have hex : ∃ n, a ∈ vals r i n := ⟨m, h⟩
  refine ⟨Nat.find hex, Nat.find_min' hex h, Nat.find_spec hex, fun M hM hM' => ?_⟩
  have := Nat.find_min hex (show M < Nat.find hex by omega)
  exact this hM'

/-- `P_a` decides `a` at the first time `i` knows `∃a` (first-knowledge times are `≤ f + 1`). -/
lemma pA_decidesAt_first {r : Run P} (hr : Adm t bin r) {i : P} {m : ℕ} (hal : r.Alive i m)
    (hf : FirstKnows r i m a) : DecidesAt (pA a t) r i m a := by
  have hmt : m ≤ t + 1 := by
    rcases m with _ | M
    · omega
    · have := first_le (hf.2 M rfl) hf.1; have := hr.1.1; omega
  refine ⟨hal, by simp [pA, hf.1], fun m' hm' => ?_⟩
  simp [pA, hf.not_mem_of_lt hm', show m' ≠ t + 1 by omega]

section Lemma2

variable {Q : Protocol P} (ha : a ∈ bin) (hQ : SolvesSetConsensus 1 t bin Q)
  (hdom : Dominates t bin Q (pA a t))
include ha hQ hdom

/-- **Lemma 2.** If `Q ⪰ P_a` solves consensus, then every live process decides `a` in `Q` at the
first time it knows `∃a`. -/
theorem lemma2 : ∀ (m : ℕ) (r : Run P), Adm t bin r → ∀ i, r.Alive i m → FirstKnows r i m a →
    DecidesAt Q r i m a := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro r hr i hal hf
  obtain ⟨m', hm', v, hv⟩ := hdom r hr i m a (pA_decidesAt_first hr hal hf)
  have hvv : v ∈ vals r i m' := dec_mem_vals' hQ hr hv
  -- it suffices to show `v = a`
  suffices hva : v = a by
    subst hva
    rcases Nat.lt_or_eq_of_le hm' with hlt | rfl
    · exact absurd hvv (hf.not_mem_of_lt hlt)
    · exact hv
  by_contra hne
  rcases m with _ | M
  · obtain rfl : m' = 0 := by omega
    rw [vals_zero, mem_singleton] at hvv
    have := hf.1; rw [vals_zero, mem_singleton] at this
    exact hne (hvv.trans this.symm)
  · -- `i` learnt `a` from some `j` in round `M + 1`
    obtain hv' | ⟨j, hj, hja⟩ := mem_vals_succ.1 hf.1
    · exact hf.2 M rfl hv'
    obtain ⟨mj, hmj, hfj⟩ := exists_firstKnows hja
    set K : Set P := {i, j}
    have hK : ∀ p ∈ K, r.Alive p M := by
      rintro p (rfl | rfl)
      · exact hal.mono (Nat.le_succ M)
      · exact hj.2.1
    set r' := modify r K r.reach M
    have hr' : Adm t bin r' := modify_admissible hr
    have hsv : SameView r r' i (M + 1) := by
      refine modify_sameView_last hK (fun p hp hpi => ?_) (fun _ _ => Iff.rfl)
      rcases hp with rfl | rfl
      · exact absurd rfl hpi
      · exact hj.2
    have hsvj : SameView r r' j mj := modify_sameView hK hmj j
    have hjc : ¬ r'.Faulty j := modify_not_faulty (Or.inr rfl)
    have hic : ¬ r'.Faulty i := modify_not_faulty (Or.inl rfl)
    have hdj : DecidesAt Q r' j mj a :=
      ih mj (by omega) r' hr' j (SyncCrash.Run.alive_of_not_faulty hjc _)
        ((SameView.firstKnows_iff hsvj).1 hfj)
    have hdi : DecidesAt Q r' i m' v :=
      (hsv.decidesAt_iff Q hm' ⟨fun _ => SyncCrash.Run.alive_of_not_faulty hic _,
        fun _ => hv.1⟩).1 hv
    exact hne (agree_of_le_one hQ hr' hic hjc hdi hdj)

end Lemma2

/-! ### The run of a hidden path -/

/-- **Lemma 9 for one hidden path.** If there is a hidden path w.r.t. a live `⟨i, m⟩`, there is a
run in which `i` has the same view at `m`, `i` is correct, and some correct process knows `∃a` at
time `m`. -/
theorem exists_run_of_hiddenPath {r : Run P} (hr : Adm t bin r) {i : P} {m : ℕ}
    (hal : r.Alive i m) (hp : HiddenPath r i m) (ha : a ∈ bin) :
    ∃ r', Adm t bin r' ∧ SameView r r' i m ∧ ¬ r'.Faulty i ∧
      ∃ j, ¬ r'.Faulty j ∧ a ∈ vals r' j m := by
  classical
  obtain ⟨b, hb⟩ := hp
  set w : ℕ → Unit → P := fun ℓ _ => b ℓ
  have H : ChainHyp r i m m w :=
    ⟨le_rfl, fun ℓ _ x y _ => Subsingleton.elim x y, fun ℓ hℓ _ => hb ℓ hℓ⟩
  set r₀ := chainRun r i m w (fun _ => a)
  have hsv₀ : SameView r r₀ i m := H.sameView
  have his : Seen r i m i m := seen_self le_rfl
  set K : Set P := {i, b m}
  have hK : ∀ p ∈ K, r₀.Alive p m := by
    rintro p (rfl | rfl)
    · exact (H.alive_iff_of_seen his le_rfl).2 hal
    · exact H.alive_w le_rfl ()
  set r₁ := modify r₀ K r₀.reach m
  have hsv₁ : ∀ p, SameView r₀ r₁ p m := modify_sameView hK le_rfl
  have hr₁ : Adm t bin r₁ := by
    refine ⟨⟨le_trans (card_le_card fun p hp => ?_) hr.1.1, fun p c hc => ?_⟩, fun p => ?_⟩
    · rw [SyncCrash.Run.mem_faulty] at hp ⊢
      have hpK : p ∉ K := fun hpK => modify_not_faulty hpK hp
      rcases H.faulty_of (modify_faulty hp) with h | ⟨_, rfl⟩
      · exact h
      · exact absurd (Or.inr rfl) hpK
    · by_cases hpK : p ∈ K
      · rw [modify_crash_of_mem hpK] at hc; cases hc
      · rw [modify_crash_of_not_mem hpK] at hc; exact H.crash_pos hr hc
    · exact ChainHyp.input_mem (x := i) (L := m) hr (fun _ => ha) p
  refine ⟨r₁, hr₁, hsv₀.trans (hsv₁ i), modify_not_faulty (Or.inl rfl), b m,
    modify_not_faulty (Or.inr rfl), ?_⟩
  rw [← (hsv₁ (b m)).vals_eq]
  exact H.mem_vals le_rfl ()

/-! ### Lemma 3 -/

/-- `never-known(∃a)`: no correct process ever knows `∃a`. -/
def NeverKnown (a : ℕ) (r : Run P) : Prop := ∀ j, ¬ r.Faulty j → ∀ m', a ∉ vals r j m'

/-- **Lemma 3.** For a live process `i` (in a full-information protocol, binary inputs),
`K_i(never-known(∃a))` holds at `m` iff `¬K_i∃a` and there is no hidden path w.r.t. `⟨i, m⟩`. -/
theorem lemma3 {r : Run P} (hr : Adm t bin r) {i : P} {m : ℕ} (hal : r.Alive i m) (ha : a ∈ bin) :
    Knows t bin r i m (NeverKnown a) ↔ a ∉ vals r i m ∧ ¬ HiddenPath r i m := by
  constructor
  · intro hk
    refine ⟨fun hai => ?_, fun hp => ?_⟩
    · -- make `i` correct
      set r' := modify r {i} r.reach m
      have hK : ∀ p ∈ ({i} : Set P), r.Alive p m := by rintro p rfl; exact hal
      have hsv : SameView r r' i m := modify_sameView hK le_rfl i
      have hic : ¬ r'.Faulty i := modify_not_faulty rfl
      exact hk r' (modify_admissible hr) hsv (SyncCrash.Run.alive_of_not_faulty hic m)
        i hic m (hsv.vals_eq ▸ hai)
    · obtain ⟨r', hr', hsv, hic, j, hj, hja⟩ := exists_run_of_hiddenPath hr hal hp ha
      exact hk r' hr' hsv (SyncCrash.Run.alive_of_not_faulty hic m) j hj m hja
  · rintro ⟨hna, hnp⟩ r' _ hsv _ j hj m' hja
    obtain ⟨ℓ, hℓ, hnh⟩ := not_hiddenPath_iff.1 ((hiddenPath_iff_of_sameView hsv).not.1 hnp)
    exact (hsv.vals_eq ▸ hna) (vals_subset_of_not_hidden hℓ hnh hj m' hja)

/-! ### Theorem 2 -/

/-- `Opt_a ⪰ P_a`. -/
lemma optA_dominates_pA : Dominates t bin (optA a : Protocol P) (pA a t) := by
  intro r hr i m v hv
  rcases decidesAt_pA hv with ⟨h1, -⟩ | ⟨-, rfl, -⟩
  · exact decidesBy_of_dec hv.1 (optA_dec_ne_none_of_mem h1)
  · have hf : r.faulty.card + 1 ≤ t + 1 := by have := hr.1.1; omega
    exact DecidesBy.mono' (optA_decidesBy_faulty (hv.1.mono hf)) hf

/-- **Theorem 2.** `Opt_a` (`a ∈ {0, 1}`; `Opt0` for `a = 0`) is an unbeatable consensus protocol in
the crash failure context `γ_cr` with binary inputs, for every `n` and every `t`. -/
theorem theorem2_optA (ha : a ∈ bin) : Unbeatable 1 t bin (optA a : Protocol P) := by
  refine ⟨optA_solves ha, fun Q hQ hdom => ?_⟩
  have hdomP : Dominates t bin Q (pA a t) := Dominates.trans hdom optA_dominates_pA
  intro r hr i m v hv
  by_contra hn
  have hnone : (optA a).dec r i m = none := by
    by_contra hne; exact hn (decidesBy_of_dec hv.1 hne)
  obtain ⟨hna, hp⟩ := optA_dec_eq_none.1 hnone
  have hvv : v ∈ vals r i m := dec_mem_vals' hQ hr hv
  have hva : v ≠ a := by rintro rfl; exact hna hvv
  obtain ⟨r', hr', hsv, hic, j, hj, hja⟩ := exists_run_of_hiddenPath hr hv.1 hp ha
  obtain ⟨mj, -, hfj⟩ := exists_firstKnows hja
  have hdj := lemma2 ha hQ hdomP mj r' hr' j (SyncCrash.Run.alive_of_not_faulty hj _) hfj
  have hdi : DecidesAt Q r' i m v :=
    (hsv.decidesAt_iff Q le_rfl ⟨fun _ => SyncCrash.Run.alive_of_not_faulty hic _,
      fun _ => hv.1⟩).1 hv
  exact hva (agree_of_le_one hQ hr' hic hj hdi hdj)

/-- **Theorem 2.** `Opt0` is an unbeatable consensus protocol in `γ_cr`. -/
theorem theorem2 : Unbeatable 1 t bin (opt0 : Protocol P) := theorem2_optA zero_mem_bin

/-- The symmetric protocol `Opt1` (§3.1) is unbeatable too. -/
theorem opt1_unbeatable : Unbeatable 1 t bin (opt1 : Protocol P) := theorem2_optA one_mem_bin

end Podc.ParetoOptimalConsensus
