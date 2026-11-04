import Papers.PODC2013.EarlyDecidingExpensive.Byzantine

/-!
# Theorem 3.6 for every algorithm (Dolev–Lenzen, PODC 2013)

Theorem 3.6 claims, for *any* binary consensus algorithm tolerating `t` Byzantine faults and every
`0 ≤ f ≤ t - 1`, an execution with `f` faults in which some non-faulty node decides in round
`f + 2` or later. The paper proves it by iterating Lemma 3.5, whose proof needs the algorithm to
decide within `f' + 2` rounds in executions with `f' < f` faults (`theorem_3_6` in
`Critical.lean` has this hypothesis).

The statement holds without it. The repair: in the executions `E(W)` the Byzantine critical node
keeps equivocating *forever* (it sends to the nodes of `W` what it sends in `E₀` and to the others
what it sends in `E₁`, in every round from `r` on) instead of falling silent after round `r + 1`.
Then `E(V \ F_r)` and `E(∅)` are indistinguishable from `E₀` and `E₁` for *all* rounds, so their
outputs are those of `E₀`, `E₁` without any deadline. The resulting pairs satisfy a weaker form
of Definition 3.3 (`IsCriticalG`): instead of being silent after round `r`, the faulty nodes send
the same messages in both executions to every node other than the critical one.
-/

namespace Podc.EarlyDecidingExpensive

open Finset

variable {V M : Type*} [DecidableEq V] {A : Algorithm V M}

/-- A weaker form of Definition 3.3: the faulty nodes need not be silent after round `r`, but
they send the same messages in both executions to the nodes other than `v`. -/
structure IsCriticalG (A : Algorithm V M) (Adm : Execution V M → Prop) (r : ℕ)
    (E₀ E₁ : Execution V M) (v : V) (b : Bool) : Prop where
  adm₀ : Adm E₀
  adm₁ : Adm E₁
  F_eq : E₁.F = E₀.F
  fr_eq : ∀ p ∈ E₀.F, E₁.fr p = E₀.fr p
  card : E₀.F.card = r - 1
  fr_lt : ∀ p ∈ E₀.F, E₀.fr p < r
  not_mem : v ∉ E₀.F
  input_eq : ∀ q, q ≠ v → E₁.input q = E₀.input q
  msg_eq : ∀ k, 1 ≤ k → k ≤ r → ∀ p q, q ≠ v → (p ≠ v ∨ k < r) →
    msg A E₁ k p q = msg A E₀ k p q
  faulty_eq : ∀ p ∈ E₀.F, ∀ k, r < k → ∀ q, q ≠ v → msg A E₁ k p q = msg A E₀ k p q
  out₀ : Out A E₀ b
  out₁ : Out A E₁ (!b)

/-- The forever-equivocating `E(W)`. -/
def gpivot (A : Algorithm V M) (E₀ E₁ : Execution V M) (v : V) (r : ℕ) (W : Finset V) :
    Execution V M :=
  addFaults E₀ {v} r fun k _ q => if q ∈ W then msg A E₀ k v q else msg A E₁ k v q

/-- Transfer of eventual decisions between executions that look the same forever. -/
lemma decides_of_hist_forever {E E' : Execution V M} {q : V} {c : Bool} (hd : Decides A E q c)
    (hx : E.input q = E'.input q) (hh : ∀ k, hist A E k q = hist A E' k q) : Decides A E' q c := by
  obtain ⟨k, hk⟩ := hd
  exact (DecidedBy.transfer ⟨k, le_rfl, hk⟩ hx (hh k)).decides

section GPivot

variable [Fintype V] {t r : ℕ} {E₀ E₁ : Execution V M} {v : V} {b : Bool}
  (h : IsCriticalG A (byzAdm t) r E₀ E₁ v b)
include h

lemma gpivot_disjoint : Disjoint E₀.F {v} := by simpa using h.not_mem

lemma card_gpivot (W : Finset V) : (gpivot A E₀ E₁ v r W).F.card = r - 1 + 1 := by
  rw [gpivot, card_addFaults (gpivot_disjoint h), h.card, card_singleton]

lemma not_mem_gpivot_F {W : Finset V} {p : V} :
    p ∉ (gpivot A E₀ E₁ v r W).F ↔ p ∈ honest E₀ v := by
  simp [gpivot, honest, and_comm]

lemma gpivot_msg_v (W : Finset V) {k : ℕ} (hk : r ≤ k) {q : V} (hq : q ≠ v) :
    msg A (gpivot A E₀ E₁ v r W) k v q = if q ∈ W then msg A E₀ k v q else msg A E₁ k v q :=
  msg_addFaults_of_mem hk (mem_singleton_self v) (Ne.symm hq)

lemma gpivot_msg_F (W : Finset V) {p : V} (hp : p ∈ E₀.F) {k : ℕ} (hk : r ≤ k) (q : V) :
    msg A (gpivot A E₀ E₁ v r W) k p q = msg A E₀ k p q :=
  msg_addFaults_of_faultyAt (by simp only [mem_singleton]; rintro rfl; exact h.not_mem hp)
    ⟨hp, (h.fr_lt p hp).le.trans hk⟩ q

lemma gpivot_msg_lt (W : Finset V) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < r) (p q : V) :
    msg A (gpivot A E₀ E₁ v r W) k p q = msg A E₀ k p q :=
  msg_addFaults_of_lt (gpivot_disjoint h) hk1 hk p q

lemma gpivot_msg_r (W : Finset V) {p : V} (hp : p ≠ v) (q : V) :
    msg A (gpivot A E₀ E₁ v r W) r p q = msg A E₀ r p q :=
  msg_addFaults_of_not_mem (gpivot_disjoint h) le_rfl (by simpa using hp) q

/-- Nodes of `W` see `E₀` forever, if `W` contains all honest nodes. -/
lemma gpivot_hist_E₀ (hr : 1 ≤ r) (k : ℕ) {q : V} (hq : q ∈ honest E₀ v) :
    hist A (gpivot A E₀ E₁ v r (honest E₀ v)) k q = hist A E₀ k q := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
    rw [hist_succ, hist_succ, ih hq]
    congr 2; funext p
    have hq' := mem_honest.1 hq
    rcases Nat.lt_or_ge (k + 1) r with hk | hk
    · exact msg_addFaults_of_lt (gpivot_disjoint h) (by omega) hk p q
    by_cases hpv : p = v
    · subst hpv; rw [gpivot_msg_v h _ hk hq'.2]; simp [hq]
    by_cases hpF : p ∈ E₀.F
    · exact gpivot_msg_F h _ hpF hk q
    · have hp : p ∈ honest E₀ v := mem_honest.2 ⟨hpF, hpv⟩
      exact msg_congr (E := gpivot A E₀ E₁ v r (honest E₀ v)) (E' := E₀) (k := k + 1)
        (fun h' => (not_mem_gpivot_F h).2 hp h'.1) (fun h' => hpF h'.1) rfl (ih hp) q

/-- Honest nodes see `E₁` forever in `E(∅)`. -/
lemma gpivot_hist_E₁ (hr : 1 ≤ r) (k : ℕ) {q : V} (hq : q ∈ honest E₀ v) :
    hist A (gpivot A E₀ E₁ v r ∅) k q = hist A E₁ k q := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
    rw [hist_succ, hist_succ, ih hq]
    congr 2; funext p
    have hq' := mem_honest.1 hq
    rcases Nat.lt_or_ge (k + 1) r with hk | hk
    · rw [gpivot_msg_lt h _ (by omega) hk p q,
        h.msg_eq _ (by omega) hk.le p q hq'.2 (Or.inr hk)]
    by_cases hpv : p = v
    · subst hpv; rw [gpivot_msg_v h _ hk hq'.2]; simp
    by_cases hpF : p ∈ E₀.F
    · rw [gpivot_msg_F h _ hpF hk q]
      rcases Nat.lt_or_ge r (k + 1) with hk' | hk'
      · exact (h.faulty_eq p hpF _ hk' q hq'.2).symm
      · exact (h.msg_eq _ (by omega) hk' p q hq'.2 (Or.inl hpv)).symm
    · have hp : p ∈ honest E₀ v := mem_honest.2 ⟨hpF, hpv⟩
      exact msg_congr (E := gpivot A E₀ E₁ v r ∅) (E' := E₁) (k := k + 1)
        (fun h' => (not_mem_gpivot_F h).2 hp h'.1) (fun h' => hpF (h.F_eq ▸ h'.1))
        (h.input_eq p hpv).symm (ih hp) q

/-- In rounds `≤ r`, `E(W)` and `E(W ∪ {v'})` differ only in what `v'` receives. -/
lemma gpivot_msg_insert_le (W : Finset V) {v' : V} {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ r) (p : V)
    {q : V} (hq : q ≠ v') :
    msg A (gpivot A E₀ E₁ v r W) k p q = msg A (gpivot A E₀ E₁ v r (insert v' W)) k p q := by
  rcases Nat.lt_or_ge k r with hk' | hk'
  · rw [gpivot_msg_lt h W hk1 hk' p q,
      gpivot_msg_lt h _ hk1 hk' p q]
  obtain rfl : k = r := by omega
  by_cases hpv : p = v
  · subst hpv
    by_cases hqv : q = p
    · subst hqv; simp [msg_self]
    rw [gpivot_msg_v h W le_rfl hqv, gpivot_msg_v h _ le_rfl hqv]
    simp [hq]
  · rw [gpivot_msg_r h W hpv, gpivot_msg_r h _ hpv]

/-- Lemma 3.5 without decision deadlines: an `(r+1)`-critical pair (weak form). -/
theorem lemma_3_5_general (hA : Correct A (byzAdm t)) (hr : 1 ≤ r) (hrt : r ≤ t)
    (hn : r < Fintype.card V) :
    ∃ E₀' E₁' v', IsCriticalG A (byzAdm t) (r + 1) E₀' E₁' v' false := by
  have hadm : ∀ W, byzAdm t (gpivot A E₀ E₁ v r W) := fun W => by
    simp only [byzAdm, card_gpivot h]; omega
  have hout0 : Out A (gpivot A E₀ E₁ v r (honest E₀ v)) b := by
    intro q hq
    rw [not_mem_gpivot_F h] at hq
    exact decides_of_hist_forever (h.out₀ q (mem_honest.1 hq).1) rfl
      fun k => (gpivot_hist_E₀ h hr k hq).symm
  have hout1 : Out A (gpivot A E₀ E₁ v r ∅) (!b) := by
    intro q hq
    rw [not_mem_gpivot_F h] at hq
    exact decides_of_hist_forever (h.out₁ q (h.F_eq ▸ (mem_honest.1 hq).1))
      (h.input_eq q (mem_honest.1 hq).2) fun k => (gpivot_hist_E₁ h hr k hq).symm
  obtain ⟨q, hq⟩ : (honest E₀ v).Nonempty := by
    have : (honest E₀ v).card = Fintype.card V - r := by
      have e : honest E₀ v = univ \ (E₀.F ∪ {v}) := by ext p; simp [honest, and_comm]
      rw [e, card_sdiff_of_subset (subset_univ _), card_univ,
        card_union_of_disjoint (gpivot_disjoint h), h.card, card_singleton]
      omega
    rw [← card_pos, this]; omega
  have hnot : ¬ Out A (gpivot A E₀ E₁ v r (honest E₀ v)) (!b) := fun h' =>
    hout0.not_not (by simpa using h') ((not_mem_gpivot_F h).2 hq)
  obtain ⟨W, v', -, hW, hv', hv'W, hg, hg'⟩ :=
    exists_flip (fun W => Out A (gpivot A E₀ E₁ v r W) (!b)) (empty_subset _) hout1 hnot
  have hv'' := mem_honest.1 hv'
  have h₀ : Out A (gpivot A E₀ E₁ v r (insert v' W)) b := by
    simpa using hA.out_not (hadm _) hg'
  have hcrit : IsCriticalG A (byzAdm t) (r + 1) (gpivot A E₀ E₁ v r (insert v' W))
      (gpivot A E₀ E₁ v r W) v' b := {
    adm₀ := hadm _
    adm₁ := hadm _
    F_eq := rfl
    fr_eq := fun _ _ => rfl
    card := by rw [card_gpivot h]; omega
    fr_lt := by
      intro p hp
      simp only [gpivot, addFaults_F, mem_union, mem_singleton] at hp
      simp only [gpivot, addFaults, mem_singleton]
      split_ifs with hpv
      · omega
      · have := h.fr_lt p (hp.resolve_right hpv); omega
    not_mem := (not_mem_gpivot_F h).2 hv'
    input_eq := fun _ _ => rfl
    msg_eq := by
      intro k hk1 hk2 p q hqv' hp
      rcases Nat.lt_or_ge k (r + 1) with hk | hk
      · exact gpivot_msg_insert_le h W hk1 (by omega) p hqv'
      obtain rfl : k = r + 1 := by omega
      have hp : p ≠ v' := hp.resolve_right (by omega)
      by_cases hpv : p = v
      · subst hpv
        by_cases hqv : q = p
        · subst hqv; simp [msg_self]
        rw [gpivot_msg_v h W (by omega) hqv, gpivot_msg_v h _ (by omega) hqv]
        simp [hqv']
      by_cases hpF : p ∈ E₀.F
      · rw [gpivot_msg_F h _ hpF (by omega), gpivot_msg_F h _ hpF (by omega)]
      · have hph : p ∈ honest E₀ v := mem_honest.2 ⟨hpF, hpv⟩
        exact msg_congr (E := gpivot A E₀ E₁ v r W) (E' := gpivot A E₀ E₁ v r (insert v' W))
          (k := r + 1) (fun h' => (not_mem_gpivot_F h).2 hph h'.1)
          (fun h' => (not_mem_gpivot_F h).2 hph h'.1) rfl
          (hist_eq_iff.2 fun k hk1 hk p' => gpivot_msg_insert_le h W hk1 hk p' hp) q
    faulty_eq := by
      intro p hp k hk q hqv'
      simp only [gpivot, addFaults_F, mem_union, mem_singleton] at hp
      rcases hp with hp | rfl
      · rw [gpivot_msg_F h _ hp (by omega), gpivot_msg_F h _ hp (by omega)]
      · by_cases hqv : q = p
        · subst hqv; simp [msg_self]
        rw [gpivot_msg_v h W (by omega) hqv, gpivot_msg_v h _ (by omega) hqv]
        simp [hqv']
    out₀ := h₀
    out₁ := hg }
  cases b
  · exact ⟨_, _, _, hcrit⟩
  · exact ⟨_, _, _, {
      adm₀ := hcrit.adm₁, adm₁ := hcrit.adm₀, F_eq := hcrit.F_eq.symm
      fr_eq := fun p hp => (hcrit.fr_eq p (hcrit.F_eq ▸ hp)).symm
      card := hcrit.F_eq ▸ hcrit.card
      fr_lt := fun p hp => by
        rw [hcrit.fr_eq p (hcrit.F_eq ▸ hp)]; exact hcrit.fr_lt p (hcrit.F_eq ▸ hp)
      not_mem := hcrit.F_eq ▸ hcrit.not_mem
      input_eq := fun q hq => (hcrit.input_eq q hq).symm
      msg_eq := fun k hk1 hk2 p q hq hp => (hcrit.msg_eq k hk1 hk2 p q hq hp).symm
      faulty_eq := fun p hp k hk q hq => (hcrit.faulty_eq p (hcrit.F_eq ▸ hp) k hk q hq).symm
      out₀ := hcrit.out₁
      out₁ := by simpa using hcrit.out₀ }⟩

end GPivot

/-- **Theorem 3.6** (for every algorithm). Let `A` be a binary consensus algorithm tolerating
`t` Byzantine faults, `n > 3t`, and `0 ≤ f ≤ t - 1`. Then some execution with exactly `f` faulty
nodes has a never-faulty node that has not decided within `f + 1` rounds. In particular no
consensus algorithm tolerating `t ≥ 1` Byzantine faults is `(f+1)`-deciding. -/
theorem theorem_3_6_general [Fintype V] {t : ℕ} (hnt : 3 * t < Fintype.card V)
    (hA : Correct A (byzAdm t)) {f : ℕ} (hft : f + 1 ≤ t) :
    ∃ E, byzAdm t E ∧ E.F.card = f ∧ ∃ q ∉ E.F, ∀ b, ¬ DecidedBy A E q (f + 1) b := by
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  -- an `(f+1)`-critical pair (weak form)
  have key : ∀ r, 1 ≤ r → r ≤ f + 1 → ∃ E₀ E₁ v, IsCriticalG A (byzAdm t) r E₀ E₁ v false := by
    intro r hr hrf
    induction r, hr using Nat.le_induction with
    | base =>
      obtain ⟨E₀, E₁, v, h⟩ := exists_critical_one hA fun x => by simp [byzAdm, faultFree]
      have hF : E₀.F = ∅ := card_eq_zero.1 h.card
      exact ⟨E₀, E₁, v, { h with faulty_eq := by simp [hF] }⟩
    | succ r hr ih =>
      obtain ⟨E₀, E₁, v, h⟩ := ih (by omega)
      exact lemma_3_5_general h hA hr (by omega) (by omega)
  obtain ⟨E₀, E₁, v, h⟩ := key (f + 1) (by omega) le_rfl
  by_contra hcon
  push Not at hcon
  have hr : 1 ≤ f + 1 := by omega
  have hN : (honest E₀ v).card = Fintype.card V - (f + 1) := by
    have e : honest E₀ v = univ \ (E₀.F ∪ {v}) := by ext p; simp [honest, and_comm]
    rw [e, card_sdiff_of_subset (subset_univ _), card_univ,
      card_union_of_disjoint (gpivot_disjoint h), h.card, card_singleton]
    omega
  obtain ⟨w, hw, u, hu, hwu⟩ := Finset.one_lt_card.1 (show 1 < (honest E₀ v).card by
    rw [hN]; omega)
  have hw' := mem_honest.1 hw
  have hu' := mem_honest.1 hu
  let E := gpivot A E₀ E₁ v (f + 1) {w}
  have hE : byzAdm t E := by simp only [E, byzAdm, card_gpivot h]; omega
  have hc : E₀.F.card = f := by rw [h.card]; rfl
  have hdis := gpivot_disjoint h
  -- `w` sees `E₀`, `u` sees `E₁`, up to round `f + 1`
  have hhw : hist A E (f + 1) w = hist A E₀ (f + 1) w := by
    refine hist_eq_iff.2 fun k hk1 hk2 p => ?_
    rcases Nat.lt_or_ge k (f + 1) with hk | hk
    · exact gpivot_msg_lt h _ hk1 hk p w
    obtain rfl : k = f + 1 := by omega
    by_cases hpv : p = v
    · subst hpv; rw [gpivot_msg_v h _ le_rfl hw'.2]; simp
    · exact gpivot_msg_r h _ hpv w
  have hhu : hist A E (f + 1) u = hist A E₁ (f + 1) u := by
    refine hist_eq_iff.2 fun k hk1 hk2 p => ?_
    rcases Nat.lt_or_ge k (f + 1) with hk | hk
    · rw [gpivot_msg_lt h _ hk1 hk p u, h.msg_eq k hk1 hk2 p u hu'.2 (Or.inr hk)]
    obtain rfl : k = f + 1 := by omega
    by_cases hpv : p = v
    · subst hpv; rw [gpivot_msg_v h _ le_rfl hu'.2]; simp [Ne.symm hwu]
    · rw [gpivot_msg_r h _ hpv, h.msg_eq _ hk1 hk2 p u hu'.2 (Or.inl hpv)]
  have hfast : DecidingAt A (byzAdm t) f (f + 1) := fun E' hE' hc' q hq => hcon E' hE' hc' q hq
  have h0 : DecidedBy A E w (f + 1) false :=
    decidedBy_of_hist hfast h.adm₀ hc h.out₀ hw'.1 rfl hhw.symm
  have h1 : DecidedBy A E u (f + 1) true :=
    decidedBy_of_hist hfast h.adm₁ (h.F_eq ▸ hc) h.out₁ (h.F_eq ▸ hu'.1) (h.input_eq u hu'.2)
      hhu.symm
  have := hA.agreement E hE w ((not_mem_gpivot_F h).2 hw) u ((not_mem_gpivot_F h).2 hu) _ _
    h0.decides h1.decides
  simp at this

/-- No consensus algorithm tolerating `t ≥ 1` Byzantine faults (`n > 3t`) is `(f+1)`-deciding
(the remark after Lemma 3.5). -/
theorem not_deciding_succ [Fintype V] {t : ℕ} (hnt : 3 * t < Fintype.card V) (ht : 1 ≤ t)
    (hA : Correct A (byzAdm t)) : ¬ Deciding A (byzAdm t) (· + 1) := by
  intro hd
  obtain ⟨E, hE, hc, q, hq, hnd⟩ := theorem_3_6_general hnt hA (f := 0) (by omega)
  obtain ⟨b, hb⟩ := hd 0 E hE hc q hq
  exact hnd b hb

end Podc.EarlyDecidingExpensive
