import Papers.PODC2013.EarlyDecidingExpensive.Byzantine

/-!
# The crash-fault message lower bound (Dolev–Lenzen, PODC 2013, Lemma 4.2, Theorem 4.3)

`A` is a binary consensus algorithm resilient to `t` crash faults (Definition 4.1) and
`(f+1)`-deciding.

* `cpivot E₀ v r W` (the paper's `E(W)` in the proof of Lemma 4.2): the critical node `v`
  crashes in round `r`, delivering its round-`r` messages of `E₀` exactly to the nodes of `W`.
* `lemma_4_2`: from an `r`-critical pair (`r < t ≤ n - 2`) an `(r+1)`-critical pair in which the
  non-faulty nodes other than the new critical node send at least `(n - r - 1)²` messages in round
  `r + 1` of both executions.
* `theorem_4_3`: an execution with `f` crashes in which the non-faulty nodes send at least
  `∑_{i=1}^f (n - i - 1)² ≥ n f (n - f) + f³/3 - 3 n f` messages, for `f ≤ n - 3` (the range of the
  paper's proof).
* `theorem_4_3_all'`, `theorem_4_3_omega_all`: the closed-form and `Ω(n² f)` bounds for every
  `f < t`, including `f ≥ n - 2`.
-/

namespace Podc.EarlyDecidingExpensive

open Finset

variable {V M : Type*} [DecidableEq V] {A : Algorithm V M}

/-- Adding crash faults to a crash execution: a node of `S` sends a subset of its algorithm
messages in round `k₀` and nothing afterwards. -/
lemma crashBehaved_addFaults {E : Execution V M} {S : Finset V} {k₀ : ℕ}
    {γ : ℕ → V → V → Option M} (hE : CrashBehaved A E) (hS : Disjoint E.F S)
    (hfr : ∀ p ∈ E.F, E.fr p < k₀)
    (hγ : ∀ p ∈ S, ∀ q, p ≠ q → γ k₀ p q = none ∨ γ k₀ p q = hmsg A E k₀ p q)
    (hγ' : ∀ p ∈ S, ∀ k, k₀ < k → ∀ q, p ≠ q → γ k p q = none) :
    CrashBehaved A (addFaults E S k₀ γ) := by
  intro p hp k q
  by_cases hpq : p = q
  · subst hpq; simp [msg_self]
  by_cases hpS : p ∈ S
  · have hfr' : (addFaults E S k₀ γ).fr p = k₀ := by simp [addFaults, hpS]
    rw [hfr']
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · rw [msg_addFaults_of_mem hk.le hpS hpq]; exact hγ' p hpS k hk q hpq
    · subst hk
      rw [msg_addFaults_of_mem le_rfl hpS hpq,
        hmsg_congr (A := A) (E := addFaults E S k γ) (E' := E) (k := k) (p := p) rfl
          (hist_addFaults_of_le hS le_rfl p) q]
      exact hγ p hpS q hpq
  · have hpE : p ∈ E.F := by simpa [hpS] using hp
    have hfr' : (addFaults E S k₀ γ).fr p = E.fr p := by simp [addFaults, hpS]
    rw [hfr']
    have hmsg' : ∀ k, E.fr p ≤ k → msg A (addFaults E S k₀ γ) k p q = msg A E k p q :=
      fun k hk => msg_addFaults_of_faultyAt hpS ⟨hpE, hk⟩ q
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · rw [hmsg' k hk.le]; exact (hE p hpE k q).1 hk
    · subst hk
      rw [hmsg' _ le_rfl, hmsg_congr (A := A) (E := addFaults E S k₀ γ) (E' := E) (k := E.fr p)
        (p := p) rfl (hist_addFaults_of_le hS (by have := hfr p hpE; omega) p) q]
      exact (hE p hpE _ q).2 rfl

/-- Crash executions with fewer allowed faults are crash executions. -/
lemma crashAdm_mono {t t' : ℕ} (h : t ≤ t') {E : Execution V M} (hE : crashAdm A t E) :
    crashAdm A t' E := ⟨hE.1.trans h, hE.2⟩

/-! ### The executions `E(W)` of Lemma 4.2 -/

/-- The paper's `E(W)` in the proof of Lemma 4.2: built on `E₀`, `v` crashes in round `r` and
delivers its round-`r` messages exactly to `W`. -/
def cpivot (A : Algorithm V M) (E₀ : Execution V M) (v : V) (r : ℕ) (W : Finset V) :
    Execution V M :=
  addFaults E₀ {v} r fun k _ q => if k = r ∧ q ∈ W then msg A E₀ r v q else none

section CPivot

variable [Fintype V] {t r : ℕ} {E₀ E₁ : Execution V M} {v : V} {b : Bool}
  (h : IsCritical A (crashAdm A t) r E₀ E₁ v b)
include h

lemma cpivot_disjoint : Disjoint E₀.F {v} := by simpa using h.not_mem

lemma card_cpivot (W : Finset V) : (cpivot A E₀ v r W).F.card = r - 1 + 1 := by
  rw [cpivot, card_addFaults (cpivot_disjoint h), h.card, card_singleton]

lemma not_mem_cpivot_F {W : Finset V} {p : V} : p ∉ (cpivot A E₀ v r W).F ↔ p ∈ honest E₀ v := by
  simp [cpivot, honest, and_comm]

lemma cpivot_fr (W : Finset V) (p : V) :
    (cpivot A E₀ v r W).fr p = if p = v then r else E₀.fr p := by
  simp [cpivot, addFaults]

lemma cpivot_adm (hr : 1 ≤ r) (hrt : r ≤ t) (W : Finset V) : crashAdm A t (cpivot A E₀ v r W) := by
  refine ⟨by rw [card_cpivot h]; omega, ?_⟩
  refine crashBehaved_addFaults h.adm₀.2 (cpivot_disjoint h) h.fr_lt ?_ ?_
  · intro p hp q hpq
    obtain rfl : p = v := by simpa using hp
    simp only [true_and]
    split_ifs
    · right
      exact msg_of_not_faultyAt (Execution.not_faultyAt_of_not_mem h.not_mem) q
    · left; rfl
  · intro p _ k hk q _
    simp [show k ≠ r by omega]

lemma cpivot_msg_lt (W : Finset V) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < r) (p q : V) :
    msg A (cpivot A E₀ v r W) k p q = msg A E₀ k p q :=
  msg_addFaults_of_lt (cpivot_disjoint h) hk1 hk p q

lemma cpivot_msg_r (W : Finset V) {p : V} (hp : p ≠ v) (q : V) :
    msg A (cpivot A E₀ v r W) r p q = msg A E₀ r p q :=
  msg_addFaults_of_not_mem (cpivot_disjoint h) le_rfl (by simpa using hp) q

lemma cpivot_msg_v (W : Finset V) {k : ℕ} (hk : r ≤ k) {q : V} (hq : q ≠ v) :
    msg A (cpivot A E₀ v r W) k v q = if k = r ∧ q ∈ W then msg A E₀ r v q else none :=
  msg_addFaults_of_mem hk (mem_singleton_self v) (Ne.symm hq)

lemma cpivot_faultyAt {W : Finset V} {p : V} (hp : p ∈ (cpivot A E₀ v r W).F) {k : ℕ}
    (hk : r ≤ k) : (cpivot A E₀ v r W).FaultyAt k p := by
  refine ⟨hp, ?_⟩
  rw [cpivot_fr h]
  split_ifs with hpv
  · exact hk
  · simp only [cpivot, addFaults_F, mem_union, mem_singleton, hpv, or_false] at hp
    have := h.fr_lt p hp; omega

/-- Nodes that were faulty before `v` send in `E(W)` what they send in `E₀`, from round `r` on. -/
lemma cpivot_msg_F {W : Finset V} {p : V} (hp : p ∈ E₀.F) {k : ℕ} (hk : r ≤ k) (q : V) :
    msg A (cpivot A E₀ v r W) k p q = msg A E₀ k p q :=
  msg_addFaults_of_faultyAt (by
    simp only [mem_singleton]; rintro rfl; exact h.not_mem hp)
    ⟨hp, (h.fr_lt p hp).le.trans hk⟩ q

/-- After round `r`, a node `q ≠ v` has the same history in `E(W)` and `E(W')` if it lies in
both or in neither. -/
lemma cpivot_hist_r_congr (hr : 1 ≤ r) {W W' : Finset V} {q : V} (hqv : q ≠ v)
    (hW : q ∈ W ↔ q ∈ W') : hist A (cpivot A E₀ v r W) r q = hist A (cpivot A E₀ v r W') r q := by
  refine hist_eq_iff.2 fun k hk1 hk2 p => ?_
  rcases Nat.lt_or_ge k r with hk | hk
  · rw [cpivot_msg_lt h W hk1 hk, cpivot_msg_lt h W' hk1 hk]
  obtain rfl : k = r := by omega
  by_cases hpv : p = v
  · subst hpv; rw [cpivot_msg_v h W le_rfl hqv, cpivot_msg_v h W' le_rfl hqv]; simp [hW]
  · rw [cpivot_msg_r h W hpv, cpivot_msg_r h W' hpv]

/-- After round `r`, a node `q ≠ v` of `W` has its history of `E₀`. -/
lemma cpivot_hist_r_mem (hr : 1 ≤ r) {W : Finset V} {q : V} (hqv : q ≠ v) (hq : q ∈ W) :
    hist A (cpivot A E₀ v r W) r q = hist A E₀ r q := by
  refine hist_eq_iff.2 fun k hk1 hk2 p => ?_
  rcases Nat.lt_or_ge k r with hk | hk
  · exact cpivot_msg_lt h W hk1 hk p q
  obtain rfl : k = r := by omega
  by_cases hpv : p = v
  · subst hpv; rw [cpivot_msg_v h W le_rfl hqv]; simp [hq]
  · exact cpivot_msg_r h W hpv q

/-- In round `r + 1`, a sender `p` that lies in both or neither of `W, W'` sends the same
messages to the nodes `q ≠ v` in `E(W)` and `E(W')`. -/
lemma cpivot_msg_succ_congr (hr : 1 ≤ r) {W W' : Finset V} {p : V} (hpW : p ∈ W ↔ p ∈ W')
    {q : V} (hqv : q ≠ v) :
    msg A (cpivot A E₀ v r W) (r + 1) p q = msg A (cpivot A E₀ v r W') (r + 1) p q := by
  by_cases hpv : p = v
  · subst hpv; rw [cpivot_msg_v h W (by omega) hqv, cpivot_msg_v h W' (by omega) hqv]; simp
  by_cases hpF : p ∈ E₀.F
  · have hF : ∀ W, p ∈ (cpivot A E₀ v r W).F := fun W => by simp [cpivot, hpF]
    by_cases hpq : p = q
    · subst hpq; simp [msg_self]
    rw [msg_of_faultyAt (cpivot_faultyAt h (hF W) (by omega)) hpq,
      msg_of_faultyAt (cpivot_faultyAt h (hF W') (by omega)) hpq]
    simp [cpivot, addFaults, hpv]
  · exact msg_congr (E := cpivot A E₀ v r W) (E' := cpivot A E₀ v r W') (k := r + 1)
      (fun h' => (not_mem_cpivot_F h).2 (mem_honest.2 ⟨hpF, hpv⟩) h'.1)
      (fun h' => (not_mem_cpivot_F h).2 (mem_honest.2 ⟨hpF, hpv⟩) h'.1) rfl
      (cpivot_hist_r_congr h hr hpv hpW) q

end CPivot

/-! ### Lemma 4.2 -/

section Lemma42

variable [Fintype V] {t r : ℕ} {E₀ E₁ : Execution V M} {v : V} {b : Bool}

/-- The two cases of the claim in the proof of Lemma 4.2: if `E(W)` outputs `c` and `E(W')`
outputs `!c`, where `W, W'` differ at most at `p`, `w ∉ W ∪ W'`, and `p` sends nothing to `w` in
round `r + 1` of `E(W')`, then letting `p` crash in round `r + 1` of `E(W)` without its message
to `w` makes `w` see `E(W')` and a third node `u` see `E(W)`: contradiction. -/
lemma cpivot_claim (hA : Correct A (crashAdm A t)) (hd : Deciding A (crashAdm A t) (· + 1))
    (h : IsCritical A (crashAdm A t) r E₀ E₁ v b) (hr : 1 ≤ r) (hrt : r < t)
    {W W' : Finset V} {p w u : V} (hp : p ∈ honest E₀ v) (hw : w ∈ honest E₀ v)
    (hu : u ∈ honest E₀ v) (hpw : p ≠ w) (hpu : p ≠ u) (hwu : w ≠ u)
    (hWW' : ∀ x, x ≠ p → (x ∈ W ↔ x ∈ W')) (hwW : w ∉ W) (hwW' : w ∉ W') {c : Bool}
    (hc : Out A (cpivot A E₀ v r W) c) (hc' : Out A (cpivot A E₀ v r W') (!c))
    (hnone : msg A (cpivot A E₀ v r W') (r + 1) p w = none) : False := by
  have hp' := mem_honest.1 hp
  have hw' := mem_honest.1 hw
  have hu' := mem_honest.1 hu
  let B := cpivot A E₀ v r W
  have hdisj : Disjoint B.F {p} := by
    simpa using (not_mem_cpivot_F (A := A) (W := W) h).2 hp
  let E' := addFaults B {p} (r + 1) fun k _ q => if k = r + 1 ∧ q ≠ w then msg A B (r + 1) p q
    else none
  have hadm : crashAdm A t E' := by
    refine ⟨by simp only [E', card_addFaults hdisj, B, card_cpivot h, card_singleton]; omega, ?_⟩
    refine crashBehaved_addFaults (cpivot_adm h hr hrt.le W).2 hdisj ?_ ?_ ?_
    · intro x hx
      rw [cpivot_fr h]
      have : x ∈ E₀.F ∪ {v} := by simpa [B, cpivot] using hx
      split_ifs with hxv
      · omega
      · have := h.fr_lt x (by simpa [hxv] using this); omega
    · intro x hx q hxq
      obtain rfl : x = p := by simpa using hx
      simp only [true_and]
      split_ifs
      · right
        exact msg_of_not_faultyAt (fun h' => (not_mem_cpivot_F h).2 hp h'.1) q
      · left; rfl
    · intro x _ k hk q _
      simp [show k ≠ r + 1 by omega]
  have hd1 : DecidingAt A (crashAdm A t) r (r + 1) := hd r
  have hcB : B.F.card = r := by simp only [B, card_cpivot h]; omega
  have huF : u ∉ E'.F := by simp [E', B, (not_mem_cpivot_F h).2 hu, Ne.symm hpu]
  have hwF : w ∉ E'.F := by simp [E', B, (not_mem_cpivot_F h).2 hw, Ne.symm hpw]
  -- `u` sees `E(W)`
  have hhu : hist A E' (r + 1) u = hist A B (r + 1) u := by
    rw [hist_succ (A := A) E' r u, hist_succ (A := A) B r u, hist_addFaults_of_lt hdisj (by omega)]
    congr 2; funext x
    by_cases hx : x = p
    · subst hx
      rw [msg_addFaults_of_mem le_rfl (mem_singleton_self _) hpu]
      simp [Ne.symm hwu]
    · exact msg_addFaults_of_not_mem hdisj le_rfl (by simpa using hx) u
  -- `w` sees `E(W')`
  have hhw : hist A E' (r + 1) w = hist A (cpivot A E₀ v r W') (r + 1) w := by
    rw [hist_succ (A := A) E' r w, hist_succ (A := A) (cpivot A E₀ v r W') r w,
      hist_addFaults_of_lt hdisj (by omega),
      cpivot_hist_r_congr h hr (W := W) (W' := W') hw'.2 (by simp [hwW, hwW'])]
    congr 2; funext x
    by_cases hx : x = p
    · subst hx
      rw [msg_addFaults_of_mem le_rfl (mem_singleton_self _) hpw, hnone]
      simp
    · rw [msg_addFaults_of_not_mem hdisj le_rfl (by simpa using hx)]
      exact cpivot_msg_succ_congr h hr (hWW' x hx) hw'.2
  have hu0 : DecidedBy A E' u (r + 1) c :=
    decidedBy_of_hist (E' := E') hd1 (cpivot_adm h hr hrt.le W) hcB hc
      ((not_mem_cpivot_F h).2 hu) rfl hhu.symm
  have hw1 : DecidedBy A E' w (r + 1) (!c) :=
    decidedBy_of_hist (E' := E') hd1 (cpivot_adm h hr hrt.le W')
      (by simp only [card_cpivot h]; omega) hc' ((not_mem_cpivot_F h).2 hw) rfl hhw.symm
  have := hA.agreement E' hadm u huF w hwF _ _ hu0.decides hw1.decides
  cases c <;> simp at this

/-- The heart of Lemma 4.2: if `E(∅)` outputs `!b` (with `E₀` outputting `b`), every honest node
sends a message to every other honest node in round `r + 1` of every `E(W)`, and the chain from
`∅` to all honest nodes yields an `(r+1)`-critical pair. -/
theorem lemma_4_2_core (hA : Correct A (crashAdm A t)) (hd : Deciding A (crashAdm A t) (· + 1))
    (h : IsCritical A (crashAdm A t) r E₀ E₁ v b) (hr : 1 ≤ r) (hrt : r < t)
    (htn : t + 2 ≤ Fintype.card V) (hemp : Out A (cpivot A E₀ v r ∅) (!b)) :
    (∀ W, W ⊆ honest E₀ v → ∀ p ∈ honest E₀ v, ∀ w ∈ honest E₀ v, p ≠ w →
      (msg A (cpivot A E₀ v r W) (r + 1) p w).isSome) ∧
    ∃ W v', W ⊆ honest E₀ v ∧ v' ∈ honest E₀ v ∧ v' ∉ W ∧
      IsCritical A (crashAdm A t) (r + 1) (cpivot A E₀ v r (insert v' W)) (cpivot A E₀ v r W)
        v' b := by
  have hN : (honest E₀ v).card = Fintype.card V - r := card_honest h hr
  have hd0 : DecidingAt A (crashAdm A t) (r - 1) r := by
    have := hd (r - 1); simp only at this; rwa [show r - 1 + 1 = r by omega] at this
  -- `E(W)` for `W` containing the honest node `q` outputs `b` (via `q`, which sees `E₀`)
  have hout_mem : ∀ W q, q ∈ W → q ∈ honest E₀ v → Out A (cpivot A E₀ v r W) b := by
    intro W q hqW hq
    have hq' := mem_honest.1 hq
    have hdq : DecidedBy A (cpivot A E₀ v r W) q r b :=
      decidedBy_of_hist (E' := cpivot A E₀ v r W) hd0 h.adm₀ h.card h.out₀ hq'.1 rfl
        (cpivot_hist_r_mem h hr hq'.2 hqW).symm
    intro q' hq'
    exact hA.decides_of_decides (cpivot_adm h hr hrt.le W) ((not_mem_cpivot_F h).2 hq) hq'
      hdq.decides
  -- the claim: honest nodes send to each other in `E(∅)` and in `E({p})`
  have hclaim : ∀ p ∈ honest E₀ v, ∀ w ∈ honest E₀ v, p ≠ w →
      (msg A (cpivot A E₀ v r ∅) (r + 1) p w).isSome ∧
      (msg A (cpivot A E₀ v r {p}) (r + 1) p w).isSome := by
    intro p hp w hw hpw
    obtain ⟨u, hu, hup, huw⟩ : ∃ u ∈ honest E₀ v, u ≠ p ∧ u ≠ w := by
      by_contra hcon
      push Not at hcon
      have : honest E₀ v ⊆ {p, w} := fun x hx => by
        by_cases hxp : x = p
        · simp [hxp]
        · simp [hcon x hx hxp]
      have := card_le_card this
      rw [hN] at this
      have := card_le_two (a := p) (b := w)
      omega
    have hpE : Out A (cpivot A E₀ v r {p}) b := hout_mem {p} p (mem_singleton_self p) hp
    have hwp : w ∉ ({p} : Finset V) := by simpa using Ne.symm hpw
    have hsing : ∀ x, x ≠ p → (x ∈ ({p} : Finset V) ↔ x ∈ (∅ : Finset V)) := by simp
    refine ⟨?_, ?_⟩
    · by_contra hnone
      exact cpivot_claim hA hd h hr hrt hp hw hu hpw (Ne.symm hup) (Ne.symm huw) hsing hwp
        (by simp) hpE (by simpa using hemp) (by simpa using hnone)
    · by_contra hnone
      exact cpivot_claim hA hd h hr hrt hp hw hu hpw (Ne.symm hup) (Ne.symm huw)
        (fun x hx => (hsing x hx).symm) (by simp) hwp hemp (by simpa using hpE)
        (by simpa using hnone)
  refine ⟨fun W hW p hp w hw hpw => ?_, ?_⟩
  · have hw' := mem_honest.1 hw
    by_cases hpW : p ∈ W
    · rw [cpivot_msg_succ_congr h hr (W' := ({p} : Finset V)) (by simp [hpW]) hw'.2]
      exact (hclaim p hp w hw hpw).2
    · rw [cpivot_msg_succ_congr h hr (W' := (∅ : Finset V)) (by simp [hpW]) hw'.2]
      exact (hclaim p hp w hw hpw).1
  -- the chain
  obtain ⟨q, hq⟩ : (honest E₀ v).Nonempty := by rw [← card_pos, hN]; omega
  have hnot : ¬ Out A (cpivot A E₀ v r (honest E₀ v)) (!b) := fun h' =>
    (hout_mem _ q hq hq).not_not (by simpa using h') ((not_mem_cpivot_F h).2 hq)
  obtain ⟨W, v', -, hW, hv', hv'W, hg, hg'⟩ :=
    exists_flip (fun W => Out A (cpivot A E₀ v r W) (!b)) (empty_subset _) hemp hnot
  have hv'' := mem_honest.1 hv'
  have h₀ : Out A (cpivot A E₀ v r (insert v' W)) b := by
    simpa using hA.out_not (cpivot_adm h hr hrt.le _) hg'
  refine ⟨W, v', hW, hv', hv'W, ?_⟩
  exact {
    adm₀ := crashAdm_mono le_rfl (cpivot_adm h hr hrt.le _)
    adm₁ := cpivot_adm h hr hrt.le _
    F_eq := rfl
    fr_eq := fun _ _ => rfl
    card := by rw [card_cpivot h]; omega
    fr_lt := by
      intro p hp
      rw [cpivot_fr h]
      split_ifs with hpv
      · omega
      · simp only [cpivot, addFaults_F, mem_union, mem_singleton, hpv, or_false] at hp
        have := h.fr_lt p hp; omega
    not_mem := (not_mem_cpivot_F h).2 hv'
    input_eq := fun _ _ => rfl
    msg_eq := by
      intro k hk1 hk2 p x hx hp
      rcases Nat.lt_or_ge k (r + 1) with hk | hk
      · by_cases hxv : x = v
        · subst hxv
          rcases Nat.lt_or_ge k r with hkr | hkr
          · rw [cpivot_msg_lt h _ hk1 hkr, cpivot_msg_lt h _ hk1 hkr]
          · obtain rfl : k = r := by omega
            by_cases hpx : p = x
            · subst hpx; simp [msg_self]
            · rw [cpivot_msg_r h _ hpx, cpivot_msg_r h _ hpx]
        · exact (hist_eq_iff (A := A)).1 (cpivot_hist_r_congr h hr (W := W) (W' := insert v' W)
            hxv (by simp [hx])) k hk1 (by omega) p
      · obtain rfl : k = r + 1 := by omega
        have hp : p ≠ v' := hp.resolve_right (by omega)
        by_cases hxv : x = v
        · by_cases hpx : p = x
          · subst hpx; simp [msg_self]
          by_cases hpF : p ∈ E₀.F
          · rw [cpivot_msg_F h hpF (by omega), cpivot_msg_F h hpF (by omega)]
          · have hpv : p ≠ v := hxv ▸ hpx
            exact msg_congr (E := cpivot A E₀ v r W) (E' := cpivot A E₀ v r (insert v' W))
              (k := r + 1)
              (fun h' => (not_mem_cpivot_F h).2 (mem_honest.2 ⟨hpF, hpv⟩) h'.1)
              (fun h' => (not_mem_cpivot_F h).2 (mem_honest.2 ⟨hpF, hpv⟩) h'.1) rfl
              (cpivot_hist_r_congr h hr hpv (by simp [hp])) x
        · exact cpivot_msg_succ_congr h hr (by simp [hp]) hxv
    silent₀ := by
      intro p hp k hk x
      simp only [cpivot, addFaults_F, mem_union, mem_singleton] at hp
      rcases hp with hp | hpv
      · rw [cpivot_msg_F h hp (by omega)]
        exact (h.adm₀.2 p hp k x).1 (by have := h.fr_lt p hp; omega)
      · subst hpv
        by_cases hxp : x = p
        · subst hxp; simp [msg_self]
        rw [cpivot_msg_v h _ (by omega) hxp]; simp [show k ≠ r by omega]
    silent₁ := by
      intro p hp k hk x
      simp only [cpivot, addFaults_F, mem_union, mem_singleton] at hp
      rcases hp with hp | hpv
      · rw [cpivot_msg_F h hp (by omega)]
        exact (h.adm₀.2 p hp k x).1 (by have := h.fr_lt p hp; omega)
      · subst hpv
        by_cases hxp : x = p
        · subst hxp; simp [msg_self]
        rw [cpivot_msg_v h _ (by omega) hxp]; simp [show k ≠ r by omega]
    out₀ := h₀
    out₁ := hg }

/-- The output of `E(∅)` does not depend on which execution of the pair it is built on. -/
lemma out_cpivot_empty_swap (hd : Deciding A (crashAdm A t) (· + 1))
    (h : IsCritical A (crashAdm A t) r E₀ E₁ v b) (hr : 1 ≤ r) (hrt : r < t) {c : Bool}
    (hc : Out A (cpivot A E₀ v r ∅) c) : Out A (cpivot A E₁ v r ∅) c := by
  have hs := h.swap
  have hhr : ∀ q, q ≠ v → hist A (cpivot A E₀ v r ∅) r q = hist A (cpivot A E₁ v r ∅) r q := by
    intro q hqv
    refine hist_eq_iff.2 fun k hk1 hk2 p => ?_
    rcases Nat.lt_or_ge k r with hk | hk
    · rw [cpivot_msg_lt h _ hk1 hk, cpivot_msg_lt hs _ hk1 hk,
        h.msg_eq k hk1 hk2 p q hqv (Or.inr hk)]
    obtain rfl : k = r := by omega
    by_cases hpv : p = v
    · subst hpv; rw [cpivot_msg_v h _ le_rfl hqv, cpivot_msg_v hs _ le_rfl hqv]; simp
    · rw [cpivot_msg_r h _ hpv, cpivot_msg_r hs _ hpv, h.msg_eq k hk1 hk2 p q hqv (Or.inl hpv)]
  intro q hq
  have hq' : q ∈ honest E₀ v := by simpa [cpivot, honest, h.F_eq, and_comm] using hq
  have hq'' := mem_honest.1 hq'
  have hh : hist A (cpivot A E₀ v r ∅) (r + 1) q = hist A (cpivot A E₁ v r ∅) (r + 1) q := by
    rw [hist_succ (A := A) _ r q, hist_succ (A := A) _ r q, hhr q hq''.2]
    congr 2; funext p
    by_cases hpv : p = v
    · subst hpv
      rw [cpivot_msg_v h _ (by omega) hq''.2, cpivot_msg_v hs _ (by omega) hq''.2]; simp
    by_cases hpF : p ∈ E₀.F
    · rw [cpivot_msg_F h hpF (by omega), cpivot_msg_F hs (h.F_eq ▸ hpF) (by omega),
        h.silent₀ p hpF _ (by omega), h.silent₁ p hpF _ (by omega)]
    · have hp1 : p ∉ (cpivot A E₀ v r ∅).F := (not_mem_cpivot_F h).2 (mem_honest.2 ⟨hpF, hpv⟩)
      have hp2 : p ∉ (cpivot A E₁ v r ∅).F := by
        simpa [cpivot, h.F_eq] using hp1
      exact msg_congr (fun h' => hp1 h'.1) (fun h' => hp2 h'.1) (h.input_eq p hpv).symm
        (hhr p hpv) q
  have hcard : (cpivot A E₀ v r ∅).F.card = r := by rw [card_cpivot h]; omega
  have hq0 : q ∉ (cpivot A E₀ v r ∅).F := (not_mem_cpivot_F h).2 hq'
  exact (decidedBy_of_hist (E' := cpivot A E₁ v r ∅) (hd r) (cpivot_adm h hr hrt.le ∅) hcard hc
    hq0 (h.input_eq q hq''.2).symm hh).decides

/-- The counting of Lemma 4.2: in round `r + 1` of every `E(W')`, the non-faulty nodes other
than `v'` send at least `(n - r - 1)²` messages. -/
lemma cpivot_count (h : IsCritical A (crashAdm A t) r E₀ E₁ v b) (hr : 1 ≤ r)
    (hall : ∀ W, W ⊆ honest E₀ v → ∀ p ∈ honest E₀ v, ∀ w ∈ honest E₀ v, p ≠ w →
      (msg A (cpivot A E₀ v r W) (r + 1) p w).isSome)
    {W' : Finset V} (hW' : W' ⊆ honest E₀ v) {v' : V} (hv' : v' ∈ honest E₀ v) :
    (Fintype.card V - r - 1) ^ 2 ≤ roundCount A (cpivot A E₀ v r W') (r + 1)
      ((nonfaulty (cpivot A E₀ v r W') (r + 1)).erase v') := by
  have hN : (honest E₀ v).card = Fintype.card V - r := card_honest h hr
  unfold roundCount
  calc (Fintype.card V - r - 1) ^ 2
      = ∑ p ∈ (honest E₀ v).erase v', ((honest E₀ v).erase p).card := by
        rw [sum_congr rfl fun p hp => card_erase_of_mem (mem_of_mem_erase hp), sum_const,
          card_erase_of_mem hv', hN, smul_eq_mul, sq]
    _ ≤ ∑ p ∈ (honest E₀ v).erase v', (sentTo A (cpivot A E₀ v r W') (r + 1) p).card := by
        refine sum_le_sum fun p hp => card_le_card fun w hw => ?_
        simp only [sentTo, mem_filter, mem_univ, true_and]
        exact hall W' hW' p (mem_of_mem_erase hp) w (mem_of_mem_erase hw)
          (Ne.symm (ne_of_mem_erase hw))
    _ ≤ _ := by
        refine sum_le_sum_of_subset fun p hp => ?_
        simp only [mem_erase, nonfaulty, mem_filter, mem_univ, true_and] at hp ⊢
        exact ⟨hp.1, fun hf => (not_mem_cpivot_F h).2 hp.2 hf.1⟩

/-- Choosing the orientation of the pair ("w.l.o.g. `E(∅)` outputs `1`" in the paper). -/
lemma exists_orientation (hA : Correct A (crashAdm A t)) (hd : Deciding A (crashAdm A t) (· + 1))
    (h : IsCritical A (crashAdm A t) r E₀ E₁ v b) (hr : 1 ≤ r) (hrt : r < t) :
    ∃ F₀ F₁ c, IsCritical A (crashAdm A t) r F₀ F₁ v c ∧ (F₀ = E₀ ∨ F₀ = E₁) ∧
      Out A (cpivot A F₀ v r ∅) (!c) := by
  by_cases hc : Out A (cpivot A E₀ v r ∅) (!b)
  · exact ⟨E₀, E₁, b, h, Or.inl rfl, hc⟩
  · have hb : Out A (cpivot A E₀ v r ∅) b := by
      simpa using hA.out_not (cpivot_adm h hr hrt.le ∅) hc
    exact ⟨E₁, E₀, !b, h.swap, Or.inr rfl, by simpa using out_cpivot_empty_swap hd h hr hrt hb⟩

/-- **Lemma 4.2.** Let `A` be `(f+1)`-deciding and resilient to `t` crash faults, `t ≤ n - 2`.
From an `r`-critical pair (`1 ≤ r < t`) one obtains an `(r+1)`-critical pair in which the nodes
of `V \ (F_r ∪ {v_{r+1}})` send at least `(n - r - 1)²` messages in round `r + 1` of both
executions. -/
theorem lemma_4_2 (hA : Correct A (crashAdm A t)) (hd : Deciding A (crashAdm A t) (· + 1))
    (hr : 1 ≤ r) (hrt : r < t) (htn : t + 2 ≤ Fintype.card V)
    (h : IsCritical A (crashAdm A t) r E₀ E₁ v false) :
    ∃ E₀' E₁' v', IsCritical A (crashAdm A t) (r + 1) E₀' E₁' v' false ∧
      (Fintype.card V - r - 1) ^ 2 ≤
        roundCount A E₀' (r + 1) ((nonfaulty E₀' (r + 1)).erase v') ∧
      (Fintype.card V - r - 1) ^ 2 ≤
        roundCount A E₁' (r + 1) ((nonfaulty E₁' (r + 1)).erase v') := by
  obtain ⟨F₀, F₁, c, hF, -, hemp⟩ := exists_orientation hA hd h hr hrt
  obtain ⟨hall, W, v', hW, hv', hv'W, hcrit⟩ := lemma_4_2_core hA hd hF hr hrt htn hemp
  have h0 := cpivot_count hF hr hall (insert_subset hv' hW) hv'
  have h1 := cpivot_count hF hr hall hW hv'
  cases c
  · exact ⟨_, _, _, hcrit, h0, h1⟩
  · exact ⟨_, _, _, by simpa using hcrit.swap, h1, h0⟩

end Lemma42

/-! ### Theorem 4.3 -/

/-- The induction invariant of Theorem 4.3, for a bound `B k` on the messages of round `k`. -/
def HeavyB (A : Algorithm V M) [Fintype V] (B : ℕ → ℕ) (E : Execution V M) (v : V) (r : ℕ) :
    Prop :=
  ∀ k, 2 ≤ k → k ≤ r → B k ≤ roundCount A E k (sendersAt E r k v)

/-- Making `v` faulty from round `r` on keeps the invariant for the rounds `≤ r`. -/
lemma heavyB_addFaults [Fintype V] {B : ℕ → ℕ} {E₀ : Execution V M} {v : V} {r : ℕ}
    (hv : v ∉ E₀.F) (hH : HeavyB A B E₀ v r) (γ : ℕ → V → V → Option M) (v' : V)
    (hlast : B (r + 1) ≤ roundCount A (addFaults E₀ {v} r γ) (r + 1)
      ((nonfaulty (addFaults E₀ {v} r γ) (r + 1)).erase v')) :
    HeavyB A B (addFaults E₀ {v} r γ) v' (r + 1) := by
  have hdisj : Disjoint E₀.F {v} := by simpa using hv
  intro k hk2 hk
  rcases Nat.lt_or_ge k (r + 1) with hk' | hk'
  · have hfault : ∀ p, (addFaults E₀ {v} r γ).FaultyAt k p ↔
        E₀.FaultyAt k p ∨ (k = r ∧ p = v) := by
      intro p
      by_cases hpv : p = v
      · subst hpv
        rw [faultyAt_addFaults_of_mem (mem_singleton_self _)]
        simp only [Execution.FaultyAt, hv, false_and, false_or, and_true]
        omega
      · rw [faultyAt_addFaults_of_not_mem (by simpa using hpv)]
        simp [hpv]
    have hset : sendersAt (addFaults E₀ {v} r γ) (r + 1) k v' = sendersAt E₀ r k v := by
      ext p
      simp only [sendersAt, if_neg (show k ≠ r + 1 by omega)]
      split_ifs with hkr
      · subst hkr
        simp only [nonfaulty, mem_filter, mem_univ, true_and, mem_erase, hfault]
        tauto
      · simp only [nonfaulty, mem_filter, mem_univ, true_and, hfault]
        tauto
    have hmsg : ∀ p ∈ sendersAt E₀ r k v,
        sentTo A (addFaults E₀ {v} r γ) k p = sentTo A E₀ k p := by
      intro p hp
      apply sentTo_congr
      intro q
      rcases Nat.lt_or_ge k r with hkr | hkr
      · exact msg_addFaults_of_lt hdisj (by omega) hkr p q
      · obtain rfl : k = r := by omega
        have : p ≠ v := by simp [sendersAt] at hp; exact hp.1
        exact msg_addFaults_of_not_mem hdisj le_rfl (by simpa using this) q
    unfold roundCount
    rw [hset, sum_congr rfl fun p hp => by rw [hmsg p hp]]
    exact hH k hk2 (by omega)
  · obtain rfl : k = r + 1 := by omega
    simpa [sendersAt] using hlast

lemma Correct.mono {Adm Adm' : Execution V M → Prop} (hA : Correct A Adm)
    (h : ∀ E, Adm' E → Adm E) : Correct A Adm' :=
  ⟨fun E hE => hA.termination E (h E hE), fun E hE => hA.agreement E (h E hE),
    fun E hE => hA.validity E (h E hE)⟩

lemma Deciding.mono {Adm Adm' : Execution V M → Prop} {d : ℕ → ℕ} (hd : Deciding A Adm d)
    (h : ∀ E, Adm' E → Adm E) : Deciding A Adm' d :=
  fun f E hE => hd f E (h E hE)

lemma sum_Icc_two_succ (g : ℕ → ℕ) (f : ℕ) :
    ∑ k ∈ Icc 2 (f + 1), g k = ∑ i ∈ Icc 1 f, g (i + 1) := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_Icc_succ_top (by omega)]

/-- **Theorem 4.3.** Let `A` be `(f+1)`-deciding and resilient to `t` crash faults. For every
`f < t` with `f ≤ n - 3` there is a crash execution with exactly `f` faults in which the
non-faulty nodes send at least `∑_{i=1}^f (n - i - 1)²` messages (in its first `f + 1`
rounds). -/
theorem theorem_4_3 [Fintype V] {t : ℕ} (hA : Correct A (crashAdm A t))
    (hd : Deciding A (crashAdm A t) (· + 1)) {f : ℕ} (hft : f < t)
    (hfn : f + 3 ≤ Fintype.card V) :
    ∃ E : Execution V M, crashAdm A t E ∧ E.F.card = f ∧
      ∑ i ∈ Icc 1 f, (Fintype.card V - i - 1) ^ 2 ≤ msgCount A E (f + 1) := by
  set n := Fintype.card V
  -- "w.l.o.g. `t ≤ n - 2`"
  set t' := min t (n - 2)
  have hmono : ∀ E : Execution V M, crashAdm A t' E → crashAdm A t E :=
    fun E hE => crashAdm_mono (min_le_left _ _) hE
  have hA' := hA.mono hmono
  have hd' := hd.mono hmono
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  let B : ℕ → ℕ := fun k => (n - k) ^ 2
  have key : ∀ r, 1 ≤ r → r ≤ f + 1 → ∃ E₀ E₁ v, IsCritical A (crashAdm A t') r E₀ E₁ v false ∧
      HeavyB A B E₀ v r ∧ HeavyB A B E₁ v r := by
    intro r hr hrf
    induction r, hr using Nat.le_induction with
    | base =>
      obtain ⟨E₀, E₁, v, h⟩ := exists_critical_one hA' fun x =>
        ⟨by simp [faultFree], fun p hp => by simp [faultFree] at hp⟩
      exact ⟨E₀, E₁, v, h, fun k hk2 hk => by omega, fun k hk2 hk => by omega⟩
    | succ r hr ih =>
      obtain ⟨E₀, E₁, v, h, h0, h1⟩ := ih (by omega)
      have hrt : r < t' := by omega
      obtain ⟨F₀, F₁, c, hF, hFE, hemp⟩ := exists_orientation hA' hd' h hr hrt
      have hH : HeavyB A B F₀ v r := by rcases hFE with rfl | rfl <;> assumption
      obtain ⟨hall, W, v', hW, hv', hv'W, hcrit⟩ :=
        lemma_4_2_core hA' hd' hF hr hrt (by omega) hemp
      have hlast : ∀ W', W' ⊆ honest F₀ v → B (r + 1) ≤ roundCount A (cpivot A F₀ v r W') (r + 1)
          ((nonfaulty (cpivot A F₀ v r W') (r + 1)).erase v') := fun W' hW' => by
        have := cpivot_count hF hr hall hW' hv'
        simpa [B, Nat.sub_sub] using this
      have h0 := heavyB_addFaults hF.not_mem hH _ v' (hlast _ (insert_subset hv' hW))
      have h1 := heavyB_addFaults hF.not_mem hH _ v' (hlast _ hW)
      cases c
      · exact ⟨cpivot A F₀ v r (insert v' W), cpivot A F₀ v r W, v', hcrit, h0, h1⟩
      · exact ⟨cpivot A F₀ v r W, cpivot A F₀ v r (insert v' W), v', by simpa using hcrit.swap,
          h1, h0⟩
  obtain ⟨E₀, E₁, v, h, hH, -⟩ := key (f + 1) (by omega) le_rfl
  refine ⟨E₀, hmono _ h.adm₀, by rw [h.card]; rfl, ?_⟩
  unfold msgCount
  calc ∑ i ∈ Icc 1 f, (n - i - 1) ^ 2 = ∑ k ∈ Icc 2 (f + 1), B k := by
        rw [sum_Icc_two_succ]; simp [B, Nat.sub_sub]
    _ ≤ ∑ k ∈ Icc 2 (f + 1), roundCount A E₀ k (sendersAt E₀ (f + 1) k v) :=
        sum_le_sum fun k hk => by rw [mem_Icc] at hk; exact hH k hk.1 hk.2
    _ ≤ ∑ k ∈ Icc 2 (f + 1), roundCount A E₀ k (nonfaulty E₀ k) := by
        refine sum_le_sum fun k _ => sum_le_sum_of_subset ?_
        unfold sendersAt; split_ifs
        · exact erase_subset _ _
        · exact subset_rfl
    _ ≤ ∑ k ∈ Icc 1 (f + 1), roundCount A E₀ k (nonfaulty E₀ k) :=
        sum_le_sum_of_subset (Icc_subset_Icc (by omega) le_rfl)

/-- **Theorem 4.3**, closed form: at least `n f (n - f) + f³/3 - 3 n f` messages, i.e.
`Ω(n² f)`. -/
theorem theorem_4_3' [Fintype V] {t : ℕ} (hA : Correct A (crashAdm A t))
    (hd : Deciding A (crashAdm A t) (· + 1)) {f : ℕ} (hft : f < t)
    (hfn : f + 3 ≤ Fintype.card V) :
    ∃ E : Execution V M, crashAdm A t E ∧ E.F.card = f ∧
      6 * (Fintype.card V : ℤ) ^ 2 * f - 6 * Fintype.card V * f ^ 2 + 2 * (f : ℤ) ^ 3 -
        18 * Fintype.card V * f ≤ 6 * (msgCount A E (f + 1) : ℤ) := by
  obtain ⟨E, hE, hc, hm⟩ := theorem_4_3 hA hd hft hfn
  refine ⟨E, hE, hc, (sum_sq_bound _ f (by omega)).trans ?_⟩
  exact_mod_cast Nat.mul_le_mul_left 6 hm

/-- **Theorem 4.3**, asymptotic form `Ω(n² f)`: at least `n² f / 3 - 3 n f` messages. -/
theorem theorem_4_3_omega [Fintype V] {t : ℕ} (hA : Correct A (crashAdm A t))
    (hd : Deciding A (crashAdm A t) (· + 1)) {f : ℕ} (hft : f < t)
    (hfn : f + 3 ≤ Fintype.card V) :
    ∃ E : Execution V M, crashAdm A t E ∧ E.F.card = f ∧
      (Fintype.card V : ℤ) ^ 2 * f - 9 * Fintype.card V * f ≤ 3 * (msgCount A E (f + 1) : ℤ) := by
  obtain ⟨E, hE, hc, hm⟩ := theorem_4_3' hA hd hft hfn
  refine ⟨E, hE, hc, ?_⟩
  have hfn' : (f : ℤ) ≤ Fintype.card V := by exact_mod_cast (by omega : f ≤ Fintype.card V)
  have hf0 : (0 : ℤ) ≤ f := by positivity
  nlinarith [mul_nonneg (mul_nonneg hf0 (sub_nonneg.2 hfn')) (by linarith : (0 : ℤ) ≤
    2 * Fintype.card V - f)]

/-! ### Theorem 4.3 for every `f < t`

The paper's reduction "w.l.o.g. `t ≤ n - 2`" yields only `f ≤ n - 3`. For `f ≥ n - 2` (possible
only if `t ≥ n - 1`) we take the execution of `theorem_4_3'` for `n - 3` faults and let
`f - (n - 3)` further never-faulty nodes crash silently after the counted rounds. -/

/-- Adding faults from round `k₀` on does not change the messages counted in rounds `< k₀`. -/
lemma msgCount_addFaults [Fintype V] {E : Execution V M} {S : Finset V} {k₀ : ℕ}
    {γ : ℕ → V → V → Option M} (hS : Disjoint E.F S) {R : ℕ} (hR : R < k₀) :
    msgCount A (addFaults E S k₀ γ) R = msgCount A E R := by
  unfold msgCount
  refine sum_congr rfl fun k hk => ?_
  rw [mem_Icc] at hk
  have hnf : nonfaulty (addFaults E S k₀ γ) k = nonfaulty E k := by
    ext p
    by_cases hp : p ∈ S
    · have hpE : p ∉ E.F := fun h => disjoint_left.1 hS h hp
      simp only [nonfaulty, mem_filter, mem_univ, true_and, faultyAt_addFaults_of_mem hp,
        Execution.not_faultyAt_of_not_mem hpE, not_false_eq_true, iff_true]
      omega
    · simp [nonfaulty, faultyAt_addFaults_of_not_mem hp]
  unfold roundCount sentTo
  rw [hnf]
  refine sum_congr rfl fun p _ => ?_
  congr 1
  ext q
  have hk0 : k < k₀ := by omega
  simp [msg_addFaults_of_lt (A := A) (γ := γ) hS hk.1 hk0 p q]

/-- **Theorem 4.3**, closed form, for every `f < t` (also `f ≥ n - 2`, which the paper's proof
does not cover): an execution with exactly `f` crashes in which the non-faulty nodes send at
least `n f (n - f) + f³/3 - 3 n f` messages. -/
theorem theorem_4_3_all' [Fintype V] {t : ℕ} (hA : Correct A (crashAdm A t))
    (hd : Deciding A (crashAdm A t) (· + 1)) {f : ℕ} (hft : f < t)
    (hfn : f ≤ Fintype.card V) :
    ∃ E : Execution V M, crashAdm A t E ∧ E.F.card = f ∧
      6 * (Fintype.card V : ℤ) ^ 2 * f - 6 * Fintype.card V * f ^ 2 + 2 * (f : ℤ) ^ 3 -
        18 * Fintype.card V * f ≤ 6 * (msgCount A E (f + 1) : ℤ) := by
  by_cases h3 : f + 3 ≤ Fintype.card V
  · exact theorem_4_3' hA hd hft h3
  by_cases hn3 : 3 ≤ Fintype.card V
  · obtain ⟨E, hE, hc, hm⟩ := theorem_4_3' hA hd (f := Fintype.card V - 3) (by omega) (by omega)
    obtain ⟨S, hSsub, hScard⟩ := exists_subset_card_eq (s := univ \ E.F)
      (n := f - (Fintype.card V - 3)) (by rw [card_sdiff_of_subset (subset_univ _), card_univ, hc]; omega)
    have hS : Disjoint E.F S := disjoint_of_subset_right hSsub disjoint_sdiff
    refine ⟨addFaults E S (E.F.sup E.fr + f + 2) (fun _ _ _ => none), ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [card_addFaults hS]; have := hE.1; omega
    · refine crashBehaved_addFaults hE.2 hS (fun p hp => ?_) (by simp) (by simp)
      have := le_sup (f := E.fr) hp; omega
    · rw [card_addFaults hS]; omega
    · rw [msgCount_addFaults hS (by omega)]
      have hmono : msgCount A E (Fintype.card V - 3 + 1) ≤ msgCount A E (f + 1) :=
        sum_le_sum_of_subset (Icc_subset_Icc le_rfl (by omega))
      have hmz : (msgCount A E (Fintype.card V - 3 + 1) : ℤ) ≤ msgCount A E (f + 1) := by
        exact_mod_cast hmono
      have hcast : ((Fintype.card V - 3 : ℕ) : ℤ) = Fintype.card V - 3 := by omega
      rw [hcast] at hm
      have hn3' : (3 : ℤ) ≤ Fintype.card V := by exact_mod_cast hn3
      obtain ⟨d, hd2, hfd⟩ : ∃ d : ℕ, d ≤ 2 ∧ (f : ℤ) = Fintype.card V - d :=
        ⟨Fintype.card V - f, by omega, by omega⟩
      rw [hfd]
      interval_cases d <;> push_cast <;> nlinarith
  · -- `n ≤ 2`: the bound is `≤ 0`; any execution with `f` nodes silent from the start
    obtain ⟨S, -, hScard⟩ := exists_subset_card_eq (s := (univ : Finset V)) (n := f)
      (by rw [card_univ]; omega)
    refine ⟨⟨fun _ => false, S, fun _ => 0, fun _ _ _ => none⟩, ⟨by simp; omega, ?_⟩,
      hScard, ?_⟩
    · intro p hp k q
      have : msg A ⟨fun _ => false, S, fun _ => 0, fun _ _ _ => none⟩ k p q = none := by
        simp [msg, step, Execution.FaultyAt, hp]
      simp [this]
    · have key : ∀ a b : ℕ, a ≤ 2 → b ≤ a →
          6 * (a : ℤ) ^ 2 * b - 6 * a * b ^ 2 + 2 * (b : ℤ) ^ 3 - 18 * a * b ≤ 0 := by
        intro a b ha hb
        interval_cases a <;> interval_cases b <;> norm_num
      exact (key _ f (by omega) hfn).trans (by positivity)

/-- **Theorem 4.3**, asymptotic form `Ω(n² f)`, for every `f < t`: at least `n² f / 3 - 3 n f`
messages. -/
theorem theorem_4_3_omega_all [Fintype V] {t : ℕ} (hA : Correct A (crashAdm A t))
    (hd : Deciding A (crashAdm A t) (· + 1)) {f : ℕ} (hft : f < t)
    (hfn : f ≤ Fintype.card V) :
    ∃ E : Execution V M, crashAdm A t E ∧ E.F.card = f ∧
      (Fintype.card V : ℤ) ^ 2 * f - 9 * Fintype.card V * f ≤ 3 * (msgCount A E (f + 1) : ℤ) := by
  obtain ⟨E, hE, hc, hm⟩ := theorem_4_3_all' hA hd hft hfn
  refine ⟨E, hE, hc, ?_⟩
  have hfn' : (f : ℤ) ≤ Fintype.card V := by exact_mod_cast hfn
  have hf0 : (0 : ℤ) ≤ f := by positivity
  nlinarith [mul_nonneg (mul_nonneg hf0 (sub_nonneg.2 hfn')) (by linarith : (0 : ℤ) ≤
    2 * Fintype.card V - f)]

end Podc.EarlyDecidingExpensive
