import Papers.PODC2011.HomonymsBA.RestrictedAlg

/-!
# Proposition 18: the authenticated broadcast with multiplicity (Figure 6)

Lemmas 23–24, Propositions 25–28 (Theorem 29) and the witness counting Lemmas 30–31, for the
algorithm `Restricted.alg` in admissible partially synchronous runs with restricted Byzantine
processes.
-/

namespace Podc.HomonymsBA.Restricted

open Finset Classical

variable {n t ℓ : ℕ} {hℓ : 0 < ℓ} {V : Type} {P : Type} [Fintype P]

set_option linter.unusedSectionVars false

/-- Rewrite of `∑` of singletons as a `map`. -/
lemma sum_singleton_eq_map {α β : Type*} (s : Finset α) (g : α → β) :
    ∑ q ∈ s, ({g q} : Multiset β) = s.val.map g := by
  rw [Finset.sum_eq_multiset_sum]
  have := Multiset.map_map (fun b => ({b} : Multiset β)) g s.val
  rw [Function.comp_def] at this
  rw [← this, Multiset.sum_map_singleton]

lemma countP_mono' {α : Type*} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (s : Multiset α) (h : ∀ x, p x → q x) : s.countP p ≤ s.countP q := by
  rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
  exact Multiset.card_le_card (Multiset.monotone_filter_right s h)

lemma card_eq_sum_countP_fst {α : Type*} (s : Multiset (Fin ℓ × α)) :
    Multiset.card s = ∑ i : Fin ℓ, s.countP (fun x => x.1 = i) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    simp only [Multiset.card_cons, Multiset.countP_cons, Finset.sum_add_distrib, ← ih]
    simp

variable (R : Run P ℓ V (Msg ℓ V))

/-- Abbreviation for the states of the algorithm. -/
local notation "A" => alg n t hℓ V

lemma rnd_st (r : ℕ) (p : P) : (R.st A r p).rnd = r := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih => rw [Run.st_succ]; show (R.st A r p).rnd + 1 = _; rw [ih]

lemma id_st (r : ℕ) (p : P) : (R.st A r p).id = R.id p := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih => rw [Run.st_succ]; exact ih p

lemma st_succ' (r : ℕ) (p : P) :
    R.st A (r + 1) p = step n t hℓ (R.st A r p) (R.inbox A r p) := rfl

/-- The correct senders that reach `p` in round `r`. -/
noncomputable def snd (r : ℕ) (p : P) : Finset P :=
  univ.filter (fun q => q ∉ R.byz ∧ ¬ R.drop r q p)

/-- The correct processes. -/
noncomputable def cor : Finset P := univ.filter (· ∉ R.byz)

lemma inbox_alg (r : ℕ) (p : P) : R.inbox A r p =
    (snd R r p).val.map (fun q => (R.id q, out n t hℓ (R.st A r q))) + R.adv r p := by
  rw [Run.inbox_eq]
  congr 1
  rw [← sum_singleton_eq_map]
  rfl

lemma countP_inbox (Q : Fin ℓ × Msg ℓ V → Prop) [DecidablePred Q] (r : ℕ) (p : P) :
    (R.inbox A r p).countP Q =
      ((snd R r p).filter (fun q => Q (R.id q, out n t hℓ (R.st A r q)))).card +
        (R.adv r p).countP Q := by
  rw [inbox_alg, Multiset.countP_add, Multiset.countP_map, Finset.card, Finset.filter_val]

lemma snd_subset (r : ℕ) (p : P) : snd R r p ⊆ (cor R) := by
  intro q; simp only [snd, cor, mem_filter, mem_univ, true_and]; exact fun h => h.1

lemma snd_eq_cor {t' : ℕ} (hv : R.Valid t') {r : ℕ} (hr : R.gst ≤ r) {p : P} (hp : p ∉ R.byz) :
    snd R r p = (cor R) := by
  ext q
  simp only [snd, cor, mem_filter, mem_univ, true_and]
  exact ⟨fun h => h.1, fun h => ⟨h, hv.no_drop r q p hr h hp⟩⟩

lemma card_cor (hP : Fintype.card P = n) : (cor R).card = n - R.byz.card := by
  have : cor R = R.byzᶜ := by ext; simp [cor]
  rw [this, card_compl, hP]

/-- The number of Byzantine processes with identifier `i` (`fᵢ`). -/
noncomputable def fi (i : Fin ℓ) : ℕ := (R.byz.filter (R.id · = i)).card

lemma sum_fi : ∑ i, fi R i = R.byz.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := R.id) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))]
  rfl

lemma countP_adv_fst (hR : R.Restricted) (r : ℕ) (p : P) (i : Fin ℓ) (Q : Fin ℓ × Msg ℓ V → Prop) [DecidablePred Q] :
    (R.adv r p).countP (fun x => x.1 = i ∧ Q x) ≤ fi R i := by
  calc (R.adv r p).countP (fun x => x.1 = i ∧ Q x) ≤ (R.adv r p).countP (fun x => x.1 = i) :=
        countP_mono' _ fun x h => h.1
    _ = ((R.adv r p).filter (·.1 = i)).card := Multiset.countP_eq_card_filter _ _
    _ ≤ _ := hR r p i

lemma countP_inbox_le_id (hR : R.Restricted) (i : Fin ℓ) (Q : Fin ℓ × Msg ℓ V → Prop)
    [DecidablePred Q] (r : ℕ) (p : P) :
    (R.inbox A r p).countP (fun x => x.1 = i ∧ Q x) ≤
      ((cor R).filter (fun q => R.id q = i ∧ Q (R.id q, out n t hℓ (R.st A r q)))).card +
        fi R i := by
  rw [countP_inbox]
  exact add_le_add (card_le_card (filter_subset_filter _ (snd_subset R r p)))
    (countP_adv_fst R hR r p i Q)

lemma countP_adv_le (hR : R.Restricted) (r : ℕ) (p : P) (Q : Fin ℓ × Msg ℓ V → Prop) [DecidablePred Q] :
    (R.adv r p).countP Q ≤ R.byz.card := by
  calc (R.adv r p).countP Q ≤ Multiset.card (R.adv r p) := Multiset.countP_le_card _ _
    _ = ∑ i, (R.adv r p).countP (fun x => x.1 = i) := card_eq_sum_countP_fst _
    _ ≤ ∑ i, fi R i := Finset.sum_le_sum fun i _ => by
        simpa using countP_adv_fst R hR r p i (fun _ => True)
    _ = _ := sum_fi R

/-- Upper bound: received pairs satisfying `Q` come from correct senders satisfying `Q` or from
Byzantine processes. -/
lemma countP_inbox_le (hR : R.Restricted) (Q : Fin ℓ × Msg ℓ V → Prop) [DecidablePred Q] (r : ℕ) (p : P) :
    (R.inbox A r p).countP Q ≤
      ((cor R).filter (fun q => Q (R.id q, out n t hℓ (R.st A r q)))).card + R.byz.card := by
  rw [countP_inbox]
  exact add_le_add (card_le_card (filter_subset_filter _ (snd_subset R r p)))
    (countP_adv_le R hR r p Q)

/-- Lower bound after `gst`. -/
lemma countP_inbox_ge {t' : ℕ} (hv : R.Valid t') {r : ℕ} (hr : R.gst ≤ r) {p : P}
    (hp : p ∉ R.byz) (Q : Fin ℓ × Msg ℓ V → Prop) [DecidablePred Q] :
    ((cor R).filter (fun q => Q (R.id q, out n t hℓ (R.st A r q)))).card ≤
      (R.inbox A r p).countP Q := by
  rw [countP_inbox, snd_eq_cor R hv hr hp]; omega

/-- If more than `|byz|` received pairs satisfy `Q`, some correct sender satisfies `Q`. -/
lemma exists_cor_of_countP (hR : R.Restricted) {Q : Fin ℓ × Msg ℓ V → Prop} [DecidablePred Q] {r : ℕ} {p : P}
    {c : ℕ} (hc : c ≤ (R.inbox A r p).countP Q) (hf : R.byz.card < c) :
    ∃ q, q ∉ R.byz ∧ Q (R.id q, out n t hℓ (R.st A r q)) := by
  have := countP_inbox_le (n := n) (t := t) (hℓ := hℓ) R hR Q r p
  have hpos : 0 < ((cor R).filter (fun q => Q (R.id q, out n t hℓ (R.st A r q)))).card := by omega
  obtain ⟨q, hq⟩ := Finset.card_pos.1 hpos
  simp only [cor, mem_filter, mem_univ, true_and] at hq
  exact ⟨q, hq⟩

/-! ### Unfolding the transition -/

lemma a_succ (r : ℕ) (p : P) :
    (R.st A (r + 1) p).a = newA n t (R.st A r p) (R.inbox A r p) := rfl

lemma wit_succ (r : ℕ) (p : P) : (R.st A (r + 1) p).wit =
    if r % 2 = 1 then witnesses n t (R.inbox A r p) else (R.st A r p).wit := by
  rw [st_succ']; simp only [step, rnd_st]

lemma proper_succ (r : ℕ) (p : P) :
    (R.st A (r + 1) p).proper = newProper t (R.st A r p) (R.inbox A r p) := rfl

lemma locks_succ (r : ℕ) (p : P) :
    (R.st A (r + 1) p).locks = newLocks n t (R.st A r p) (R.inbox A r p) := rfl

lemma lockRcv_succ (r : ℕ) (p : P) : (R.st A (r + 1) p).lockRcv =
    if r % 8 = 2 then {v | ∃ x ∈ R.inbox A r p, x.1 = leader hℓ (r / 8) ∧ x.2.lock = some v}
    else (R.st A r p).lockRcv := by
  rw [st_succ']; simp only [step, rnd_st]

lemma ackVal_succ (r : ℕ) (p : P) : (R.st A (r + 1) p).ackVal =
    if r % 8 = 5 then pick (ackCand n t (R.st A r p) (R.inbox A r p))
    else (R.st A r p).ackVal := by
  rw [st_succ']; simp only [step, rnd_st]

lemma decided_succ (r : ℕ) (p : P) : (R.st A (r + 1) p).decided =
    (R.st A r p).decided.or
      (if r % 8 = 6 then pick (decCand n t (R.st A r p) (R.inbox A r p)) else none) := by
  rw [st_succ']; simp only [step, rnd_st]

/-! ### The threshold function -/

omit [Fintype P] in
lemma thr_le_n (c : ℕ) (I : Multiset (Fin ℓ × Msg ℓ V)) (g : Msg ℓ V → ℕ) : thr n c I g ≤ n :=
  Nat.findGreatest_le _

omit [Fintype P] in
lemma thr_spec {c : ℕ} {I : Multiset (Fin ℓ × Msg ℓ V)} {g : Msg ℓ V → ℕ}
    (h : 0 < thr n c I g) : c ≤ I.countP (fun x => thr n c I g ≤ g x.2) :=
  Nat.findGreatest_of_ne_zero (P := fun α => c ≤ I.countP (fun x => α ≤ g x.2)) rfl h.ne'

omit [Fintype P] in
lemma le_thr {c α : ℕ} {I : Multiset (Fin ℓ × Msg ℓ V)} {g : Msg ℓ V → ℕ} (hα : α ≤ n)
    (h : c ≤ I.countP (fun x => α ≤ g x.2)) : α ≤ thr n c I g :=
  Nat.le_findGreatest (P := fun α => c ≤ I.countP (fun x => α ≤ g x.2)) hα h

/-- If more than `|byz|` messages are needed, the threshold value is bounded by the values of
correct senders. -/
lemma thr_le_of_cor (hR : R.Restricted) {c : ℕ} (hc : R.byz.card < c) {g : Msg ℓ V → ℕ} {B r : ℕ}
    {p : P} (hB : ∀ q, q ∉ R.byz → g (out n t hℓ (R.st A r q)) ≤ B) :
    thr n c (R.inbox A r p) g ≤ B := by
  rcases Nat.eq_zero_or_pos (thr n c (R.inbox A r p) g) with h | h
  · omega
  obtain ⟨q, hq, hq'⟩ := exists_cor_of_countP R hR (thr_spec h) hc
  exact hq'.trans (hB q hq)

/-! ### Lemma 23: the echo values of correct processes are bounded -/

/-- `cᵢ(m, k)`: the number of correct processes with identifier `i` that perform
`Broadcast(i, m, k)` (i.e. put `m` in the `init` field of their round-`2k` message). -/
noncomputable def ci (i : Fin ℓ) (m : CM V) (k : ℕ) : ℕ :=
  ((cor R).filter (fun q => R.id q = i ∧ m ∈ initOut n t (R.st A (2 * k) q))).card

/-- `c(m, k)`: the number of correct processes that perform `Broadcast(∗, m, k)`. -/
noncomputable def cc (m : CM V) (k : ℕ) : ℕ :=
  ((cor R).filter (fun q => m ∈ initOut n t (R.st A (2 * k) q))).card

local notation "CI" => ci (n := n) (t := t) (hℓ := hℓ)
local notation "CC" => cc (n := n) (t := t) (hℓ := hℓ)

lemma sum_ci (m : CM V) (k : ℕ) : ∑ i, CI R i m k =
    CC R m k := by
  unfold cc ci
  rw [Finset.card_eq_sum_card_fiberwise (f := R.id) (t := univ)
    (fun _ _ => mem_coe.2 (mem_univ _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1; ext q; simp only [mem_filter]; tauto

/-- The bound of Lemma 23 (and `a = 0` before the broadcast round). -/
noncomputable def aBound (r : ℕ) (i : Fin ℓ) (m : CM V) (k : ℕ) : ℕ :=
  if r ≤ 2 * k then 0 else CI R i m k + fi R i

local notation "AB" => aBound (n := n) (t := t) (hℓ := hℓ)

lemma aBound_mono {r r' : ℕ} (h : r ≤ r') (i : Fin ℓ) (m : CM V) (k : ℕ) :
    AB R r i m k ≤ AB R r' i m k := by
  unfold aBound; split_ifs <;> omega

/-- **Lemma 23.** The echo value `a[i, m, k]` of a correct process never exceeds
`cᵢ(m, k) + fᵢ` (and is `0` up to round `2k`). -/
theorem a_le (hn : 3 * t < n) (hR : R.Admissible t .psync .restricted) (r : ℕ) {q : P}
    (hq : q ∉ R.byz) (i : Fin ℓ) (m : CM V) (k : ℕ) :
    (R.st A r q).a i m k ≤ AB R r i m k := by
  have hres : R.Restricted := hR.2.2 rfl
  have hf : R.byz.card ≤ t := hR.1.card_byz
  induction r generalizing q with
  | zero => simp [aBound]; rfl
  | succ r ih =>
    rw [a_succ]
    unfold newA
    refine max_le ((ih hq).trans (aBound_mono R (by omega) _ _ _)) (max_le ?_ ?_)
    · rw [rnd_st]
      split_ifs with hr
      · subst hr
        unfold initCount aBound
        rw [ite_eq_right (by omega)]
        exact countP_inbox_le_id R hres i (fun x => m ∈ x.2.init) (2 * k) q
      · exact Nat.zero_le _
    · refine (thr_le_of_cor R hres (by omega) fun q' hq' => ih hq').trans
        (aBound_mono R (by omega) _ _ _)

/-- **Unforgeability** (Proposition 28), for one identifier: the multiplicity `α₂` of an
`Accept(i, α₂, m, k)` is at most `cᵢ(m, k) + fᵢ`, and no accept happens up to round `2k`. -/
theorem thr_acc_le (hn : 3 * t < n) (hR : R.Admissible t .psync .restricted) (r : ℕ) (p : P)
    (i : Fin ℓ) (m : CM V) (k : ℕ) :
    thr n (n - t) (R.inbox A r p) (fun x => x.echo i m k) ≤ AB R r i m k :=
  thr_le_of_cor R (hR.2.2 rfl) (by have := hR.1.card_byz; omega)
    fun _ hq => a_le R hn hR r hq i m k

/-- Witness bound (core of Lemma 30). -/
theorem witnesses_le (hn : 3 * t < n) (hR : R.Admissible t .psync .restricted) (r : ℕ) (p : P)
    (m : CM V) (k : ℕ) :
    witnesses n t (R.inbox A r p) m k ≤ if r ≤ 2 * k then 0 else CC R m k + R.byz.card := by
  unfold witnesses
  calc ∑ i, thr n (n - t) (R.inbox A r p) (fun x => x.echo i m k) ≤ ∑ i, AB R r i m k :=
        sum_le_sum fun i _ => thr_acc_le R hn hR r p i m k
    _ = _ := by
        unfold aBound
        split_ifs
        · simp
        · rw [sum_add_distrib, sum_ci, sum_fi]

/-- **Lemma 30.** If a correct process has `n - t` witnesses for `(m, k)` (in round `r`), then
`2k < r` and at least `n - t - f` correct processes performed `Broadcast(∗, m, k)`. -/
theorem lemma30 (hn : 3 * t < n) (hR : R.Admissible t .psync .restricted) {r : ℕ} {p : P}
    {m : CM V} {k : ℕ} (h : n - t ≤ witnesses n t (R.inbox A r p) m k) :
    2 * k < r ∧ n - t - R.byz.card ≤ CC R m k := by
  have := witnesses_le (hℓ := hℓ) R hn hR r p m k
  split_ifs at this with hr
  · omega
  · omega

/-- **Lemma 31.** Two sets of `n - t` witnesses share a correct broadcaster. -/
theorem lemma31 (hn : 3 * t < n) (hP : Fintype.card P = n)
    (hR : R.Admissible t .psync .restricted) {r r' : ℕ} {p p' : P} {m m' : CM V} {k k' : ℕ}
    (h : n - t ≤ witnesses n t (R.inbox A r p) m k)
    (h' : n - t ≤ witnesses n t (R.inbox A r' p') m' k') :
    ∃ q, q ∉ R.byz ∧ m ∈ initOut n t (R.st A (2 * k) q) ∧
      m' ∈ initOut n t (R.st A (2 * k') q) := by
  have h1 := (lemma30 R hn hR h).2
  have h2 := (lemma30 R hn hR h').2
  have hf := hR.1.card_byz
  have hc := card_cor R hP
  unfold cc at h1 h2
  set X := (cor R).filter (fun q => m ∈ initOut n t (R.st A (2 * k) q))
  set Y := (cor R).filter (fun q => m' ∈ initOut n t (R.st A (2 * k') q))
  have hU : (X ∪ Y).card ≤ (cor R).card :=
    card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  have := card_union_add_card_inter X Y
  obtain ⟨q, hq⟩ := Finset.card_pos.1 (show 0 < (X ∩ Y).card by omega)
  simp only [X, Y, mem_inter, mem_filter, cor, mem_univ, true_and] at hq
  exact ⟨q, hq.1.1, hq.1.2, hq.2.2⟩

/-- Echo values never decrease. -/
lemma a_mono {r r' : ℕ} (h : r ≤ r') (q : P) (i : Fin ℓ) (m : CM V) (k : ℕ) :
    (R.st A r q).a i m k ≤ (R.st A r' q).a i m k := by
  induction r', h using Nat.le_induction with
  | base => exact le_rfl
  | succ r' _ ih => exact ih.trans (by rw [a_succ]; exact le_max_left _ _)

lemma ci_le_card (hP : Fintype.card P = n) (i : Fin ℓ) (m : CM V) (k : ℕ) : CI R i m k ≤ n :=
  hP ▸ (card_le_card (filter_subset _ _)).trans (card_le_univ _)

/-- After the broadcast round `2k ≥ gst`, every correct process has `a[i, m, k] ≥ cᵢ(m, k)`
(Lemma 24 (1),(3) at round `2k + 1`). -/
lemma ci_le_a (hR : R.Admissible t .psync .restricted) {k : ℕ} (hk : R.gst ≤ 2 * k) {q : P}
    (hq : q ∉ R.byz) (i : Fin ℓ) (m : CM V) : CI R i m k ≤ (R.st A (2 * k + 1) q).a i m k := by
  rw [a_succ]
  unfold newA
  refine le_max_of_le_right (le_max_of_le_left ?_)
  rw [rnd_st, ite_eq_left rfl]
  exact countP_inbox_ge R hR.1 hk hq (fun x => x.1 = i ∧ m ∈ x.2.init)

/-- **Correctness** (Proposition 26): if the broadcasts of `(m, k)` happen at or after `gst`,
every correct process has at least `c(m, k)` witnesses for `(m, k)` in round `2k + 1`. -/
theorem cc_le_witnesses (hP : Fintype.card P = n)
    (hR : R.Admissible t .psync .restricted) {k : ℕ} (hk : R.gst ≤ 2 * k) {p : P}
    (hp : p ∉ R.byz) (m : CM V) :
    CC R m k ≤ witnesses n t (R.inbox A (2 * k + 1) p) m k := by
  rw [← sum_ci]
  unfold witnesses
  refine sum_le_sum fun i _ => le_thr (ci_le_card R hP i m k) ?_
  refine le_trans ?_ (countP_inbox_ge R hR.1 (by omega) hp (fun x => CI R i m k ≤ x.2.echo i m k))
  have hf := hR.1.card_byz
  have hc := card_cor R hP
  rw [filter_true_of_mem]
  · omega
  · intro q hq; exact ci_le_a R hR hk (by simpa [cor] using hq) i m

/-- **Relay** (Proposition 27), for one identifier, in the persistent form needed later: if a
correct process accepts `(i, α, m, k)` in round `r`, then every correct process accepts
`(i, α', m, k)` with `α' ≥ α` in every round `s + 1` with `r ≤ s` and `gst ≤ s`. -/
theorem thr_relay (hP : Fintype.card P = n)
    (hR : R.Admissible t .psync .restricted) {r s : ℕ} (hrs : r ≤ s) (hs : R.gst ≤ s)
    {p p' : P} (hp' : p' ∉ R.byz) (i : Fin ℓ) (m : CM V) (k : ℕ) :
    thr n (n - t) (R.inbox A r p) (fun x => x.echo i m k) ≤
      thr n (n - t) (R.inbox A (s + 1) p') (fun x => x.echo i m k) := by
  set α := thr n (n - t) (R.inbox A r p) (fun x => x.echo i m k)
  have hf := hR.1.card_byz
  have hc := card_cor R hP
  have hres : R.Restricted := hR.2.2 rfl
  rcases Nat.eq_zero_or_pos α with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  have hαn : α ≤ n := thr_le_n _ _ _
  have h1 := (thr_spec hpos).trans (countP_inbox_le R hres (fun x => α ≤ x.2.echo i m k) r p)
  -- every correct process has `a[i, m, k] ≥ α` at round `s + 1`
  have h2 : ∀ q, q ∉ R.byz → α ≤ (R.st A (s + 1) q).a i m k := by
    intro q hq
    rw [a_succ]
    unfold newA
    refine le_max_of_le_right (le_max_of_le_right (le_thr hαn ?_))
    refine le_trans ?_ (countP_inbox_ge R hR.1 hs hq (fun x => α ≤ x.2.echo i m k))
    have h3 : ((cor R).filter (fun q => α ≤ (R.id q, out n t hℓ (R.st A r q)).2.echo i m k)).card
        ≤ ((cor R).filter (fun q => α ≤ (R.id q, out n t hℓ (R.st A s q)).2.echo i m k)).card :=
      card_le_card (fun q' hq' => by
        simp only [mem_filter] at hq' ⊢
        exact ⟨hq'.1, le_trans hq'.2 (a_mono R hrs q' i m k)⟩)
    omega
  refine le_thr hαn ?_
  refine le_trans ?_ (countP_inbox_ge R hR.1 (by omega) hp' (fun x => α ≤ x.2.echo i m k))
  rw [filter_true_of_mem]
  · omega
  · intro q hq; exact h2 q (by simpa [cor] using hq)

/-- **Relay** for witness counts. -/
theorem witnesses_relay (hP : Fintype.card P = n)
    (hR : R.Admissible t .psync .restricted) {r s : ℕ} (hrs : r ≤ s) (hs : R.gst ≤ s)
    {p p' : P} (hp' : p' ∉ R.byz) (m : CM V) (k : ℕ) :
    witnesses n t (R.inbox A r p) m k ≤ witnesses n t (R.inbox A (s + 1) p') m k :=
  sum_le_sum fun i _ => thr_relay R hP hR hrs hs hp' i m k

end Podc.HomonymsBA.Restricted
