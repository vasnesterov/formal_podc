import Papers.PODC2014.SignatureFreeBA.BVBroadcast

/-!
# The true parts of Lemma 5 (termination)

Mostéfaoui, Moumen, Raynal, PODC 2014, Lemma 5. Its proof has two parts:

1. no correct process blocks forever in a round (the waits of lines 03 and 05 terminate);
2. once all correct processes have the same estimate `v`, they all decide in the first later
   round whose coin is `v`.

Both are correct and proved here for every weakly fair execution and every coin sequence:
`Exec.no_blocking` and `Exec.decide_of_unanimous`. In particular, with unanimous inputs every
correct process decides in the first round whose coin is the common input
(`Exec.decide_of_unanimous_inputs`). The remaining step of the proof (the "Claim": with
probability 1 the correct processes eventually have the same estimate) is false against the
adversary of the paper's model; see `Counterexample.lean`.
-/

namespace Podc.SignatureFreeBA

open Cslib.Byzantine.AsyncBroadcast

variable {P : Type*} [Fintype P] [DecidableEq P] {t : ℕ} {coin : ℕ → Bool} {x : P → Bool}
  {k : FaultKind} {σ : State P Msg Bool}

/-- Consequence of Lemma 1: under its hypotheses, `¬v ∉ bin_values[r]` for `r ≥ r₀`. -/
theorem not_binVal_of_lemma_1 (h : Reachable (mmr t coin) x k t σ) {H : Set P}
    (hbad : σ.bad ⊆ Hᶜ) (hH : Hᶜ.ncard ≤ t) (ht : t < Fintype.card P) {r₀ : ℕ} (hr₀ : 1 ≤ r₀)
    {v : Bool} (hbase : ∀ p ∈ H, ∀ w d, (p, .bval r₀ w (some d)) ∈ σ.sent → w = v) {q : P}
    {r : ℕ} (hr : r₀ ≤ r) : ¬ BinVal t (σ.inbox q) r (!v) := fun hb => by
  obtain ⟨s, hs, d, hm⟩ := exists_bval_sender_mem (H := H) (c := 2 * t) (by omega) hb
  exact (lemma_1 h hbad hH ht hr₀ hbase s hs r hr).1 d (h.genuine hm fun hb => hbad hb hs)

namespace Exec

variable (E : Exec (mmr t coin) x k t) (hF : E.Fair)
include hF

/-- **Lemma 5, first part.** In a fair execution no correct process blocks forever: every
correct process starts every round `r ≥ 1` (broadcasts its estimate `B_VAL[r](est)`). -/
theorem no_blocking (ht : 3 * t < Fintype.card P) :
    ∀ r, 1 ≤ r → ∀ p, E.Correct p → ∃ i v d, (p, .bval r v (some d)) ∈ (E.σ i).sent := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    intro p hp
    obtain ⟨j, m', ⟨v, d, rfl⟩, hj⟩ := E.eventually_sent hF hp (φ := IsEst 1)
      (m := .bval 1 (x p) (some false)) ⟨_, _, rfl⟩ (i := 0)
      fun j _ hno => ⟨rfl, rfl, fun m hm hm' => hno m hm' hm⟩
    exact ⟨j, v, d, hj⟩
  | succ r hr ih =>
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    -- every correct process eventually broadcasts some `AUX[r+1](w)` (lines 03–04)
    have haux : ∀ q, E.Correct q → ∃ i w, (q, .aux (r + 1) w) ∈ (E.σ i).sent := by
      intro q hq
      obtain ⟨i₀, v₀, d₀, h₀⟩ := ih q hq
      obtain ⟨w, i₁, h₁⟩ := Exec.bv_termination E hF ht (r := r + 1) ih hq
      obtain ⟨j, m', ⟨w', rfl⟩, hj⟩ := E.eventually_sent hF hq (φ := IsAux (r + 1))
        (m := .aux (r + 1) w) ⟨_, rfl⟩ (i := max i₀ i₁)
        fun j hij hno => ⟨⟨v₀, d₀, E.sent_mono (le_of_max_le_left hij) h₀⟩,
          h₁ j (le_of_max_le_right hij), fun m hm hm' => hno m hm' hm⟩
      exact ⟨j, w', hj⟩
    choose iA wA hA using haux
    -- the values of these messages eventually enter `bin_values[r+1]` everywhere
    intro p hp
    have hev : ∀ q : {q // E.Correct q}, ∃ j, (p, (q : P), Msg.aux (r + 1) (wA q q.2)) ∈
        (E.σ j).rcv ∧ BinVal t ((E.σ j).inbox p) (r + 1) (wA q q.2) := by
      rintro ⟨q, hq⟩
      obtain ⟨j₁, h₁⟩ := hF.deliver p q _ (iA q hq) hp hq (hA q hq)
      obtain ⟨j₂, h₂⟩ := Exec.bv_uniformity E hF ht (aux_just (E.reachable _) (hA q hq)) hp
      exact ⟨max j₁ j₂, E.rcv_mono (le_max_left _ _) h₁, h₂ _ (le_max_right _ _)⟩
    obtain ⟨j, hj⟩ := exists_forall_of_mono
      (fun (q : {q // E.Correct q}) j => (p, (q : P), Msg.aux (r + 1) (wA q q.2)) ∈
        (E.σ j).rcv ∧ BinVal t ((E.σ j).inbox p) (r + 1) (wA q q.2))
      (fun q i j hij h => ⟨E.rcv_mono hij h.1, h.2.mono (E.inbox_mono hij p)⟩) hev
    -- a quorum of `n − t` correct senders (line 05)
    classical
    let f : P → Bool := fun q => if h : E.Correct q then wA q h else false
    have hC : Fintype.card P - t ≤ (Finset.univ.filter fun q => E.Correct q).card := by
      have := E.card_sub_le_ncard_correct
      rwa [← Set.ncard_coe_finset, Finset.coe_filter_univ]
    obtain ⟨S, hSC, hS⟩ := Finset.exists_subset_card_eq hC
    have hQ : ∀ j', j ≤ j' → AuxQuorum t ((E.σ j').inbox p) (r + 1) (S.image f) := by
      intro j' hj'
      refine ⟨S, f, hS, fun q hq => ?_, rfl⟩
      have hqc : E.Correct q := (Finset.mem_filter.1 (hSC hq)).2
      have := hj ⟨q, hqc⟩
      simp only [f, dite_eq_left_of_eq_true (eq_true hqc)]
      exact ⟨E.rcv_mono hj' this.1, this.2.mono (E.inbox_mono hj' p)⟩
    obtain ⟨j', m', ⟨v, d, rfl⟩, hj''⟩ := E.eventually_sent hF hp (φ := IsEst (r + 2))
      (m := .bval (r + 2) (nextEst (S.image f) (coin (r + 1))).1
        (some (nextEst (S.image f) (coin (r + 1))).2)) ⟨_, _, rfl⟩ (i := max j (iA p hp))
      fun j' hij hno => ⟨⟨wA p hp, E.sent_mono (le_of_max_le_right hij) (hA p hp)⟩,
        fun m hm hm' => hno m hm' hm, S.image f, hQ j' (le_of_max_le_left hij), rfl⟩
    exact ⟨j', v, d, hj''⟩

/-- **Lemma 5, second part.** If every correct process that starts round `r₀ ≥ 1` does so with
estimate `v`, and the coin of some round `r ≥ r₀` is `v`, every correct process decides. -/
theorem decide_of_unanimous (ht : 3 * t < Fintype.card P) {r₀ : ℕ} (hr₀ : 1 ≤ r₀) {v : Bool}
    (hbase : ∀ i p, E.Correct p → ∀ w d, (p, .bval r₀ w (some d)) ∈ (E.σ i).sent → w = v)
    {r : ℕ} (hr : r₀ ≤ r) (hc : coin r = v) {q : P} (hq : E.Correct q) :
    ∃ i, (E.σ i).dec q ≠ none := by
  have hH : {p | E.Correct p}ᶜ.ncard ≤ t := E.ncard_not_correct_le
  have hbad : ∀ i, (E.σ i).bad ⊆ {p | E.Correct p}ᶜ := fun i p hp hc => hc i hp
  obtain ⟨i, v', d', hi⟩ := no_blocking E hF ht (r + 1) (by omega) q hq
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨V, hV, hVe⟩ := est_just (E.reachable i) hi
  have hV1 : ∀ u ∈ V, u = v := by
    obtain ⟨S, f, -, hf, rfl⟩ := hV
    intro u hu
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hu
    by_contra hne
    have : f s = !v := by cases v <;> cases hfs : f s <;> simp_all
    exact not_binVal_of_lemma_1 (E.reachable i) (hbad i) hH (by omega) hr₀
      (fun p hp w d hm => hbase i p hp w d hm) hr (this ▸ (hf s hs).2)
  rw [nextEst_of_subset (hV.nonempty (by omega)) hV1] at hVe
  simp only [Prod.mk.injEq] at hVe
  obtain ⟨rfl, rfl⟩ := hVe
  exact E.eventually_dec hF hq (o := v) (i := i) fun j hij _ =>
    ⟨r + 1, E.sent_mono hij hi, hc⟩

/-- With unanimous inputs `v` (of the correct processes), every correct process decides as soon
as some coin equals `v`. -/
theorem decide_of_unanimous_inputs (ht : 3 * t < Fintype.card P) {v : Bool}
    (hx : ∀ p, E.Correct p → x p = v) {r : ℕ} (hr : 1 ≤ r) (hc : coin r = v) {q : P}
    (hq : E.Correct q) : ∃ i, (E.σ i).dec q ≠ none :=
  decide_of_unanimous E hF ht le_rfl (fun i p hp _ _ hm => (est1_just (E.reachable i) hm).1 ▸ hx p hp)
    hr hc hq

end Exec

/-- Non-vacuity: weakly fair executions of the algorithm exist, for all parameters, inputs and
coin sequences (round robin, from `Cslib.Byzantine.AsyncBroadcast.exists_fair`). -/
theorem Exec.exists_fair_mmr [Countable P] (t : ℕ) (coin : ℕ → Bool) (x : P → Bool) (k : FaultKind) :
    ∃ E : Exec (mmr (P := P) t coin) x k t, E.Fair ∧ ∀ i, (E.σ i).bad = ∅ :=
  exists_fair _ x k t

end Podc.SignatureFreeBA
