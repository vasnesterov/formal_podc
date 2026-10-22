import Papers.PODC2018.FairLeaderElection.ALead

/-!
# When does a deviation from `A-LEADuni` succeed? (Lemmas 3.3–3.5 of [YM18])

Fix a coalition `C` and arbitrary (deterministic) strategies `A` for its members; honest
processors run `A-LEADuni` with secrets `d`. For an adversary `a ∈ C`, `gap C a` is the length of
the honest segment `I_a = a+1, …, a+gap` following it; `a` is *exposed* if `a + 1 ∉ C`.

If `a` has sent the messages `m` (at least `n` of them), the honest processor `a + s + 1` of its
segment ends with the history `seg m e s` (`e s` = the secret of `a + s + 1`):
`seg m e 0 = m.take n`, `seg m e (s+1) = (e s :: seg m e s).take n`.

* Lemma 3.5 (`lemma_3_5`): every processor of the segment passes validation iff the last messages of
  `a` (among its first `n`) are the secrets of the segment, in reverse order.
* Lemma 3.4 (`lemma_3_4`): then every processor of the segment computes the sum of the first `n`
  messages of `a`.
* Lemma 3.3 (`lemma_3_3`, `lemma_3_3_run`): all honest processors terminate with the common valid
  output `v` iff every exposed adversary sends at least `n` messages, the sum of its first `n`
  messages is `v`, and its messages `n - gap + 1, …, n` are the secrets of its segment in the
  appropriate order. (The paper states this with "the execution succeeds"; since `outcome` also
  depends on the adversaries' own outputs, the correct reading is about the honest processors.)
-/

namespace Podc.FairLeaderElection

open Cslib.UniRing
open Fin.NatCast Fin.CommRing

variable {n : ℕ} [NeZero n]

/-! ### The segment lists -/

/-- The history of the `s`-th honest processor after an adversary that sent `m`. -/
def seg (m : List (Fin n)) (e : ℕ → Fin n) : ℕ → List (Fin n)
  | 0 => m.take n
  | s + 1 => (e s :: seg m e s).take n

variable {m : List (Fin n)} {e : ℕ → Fin n}

theorem seg_length (hm : n ≤ m.length) (s : ℕ) : (seg m e s).length = n := by
  induction s with
  | zero => simp [seg, hm]
  | succ s ih => simp [seg, ih]

theorem seg_getElem? (hm : n ≤ m.length) {s k : ℕ} (hsk : s ≤ k) (hk : k < n) :
    (seg m e s)[k]? = m[k - s]? := by
  induction s generalizing k with
  | zero => simp [seg, List.getElem?_take, hk]
  | succ s ih =>
    simp only [seg, List.getElem?_take, hk, if_true]
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [List.getElem?_cons_succ, ih (by omega) (by omega)]
    congr 1; omega

theorem seg_last (hm : n ≤ m.length) {s : ℕ} (hs : s < n) :
    (seg m e s)[n - 1]? = m[n - 1 - s]? := seg_getElem? hm (by omega) (by omega)

/-- **Lemma 3.5** (list form): the first `L ≤ n` processors of the segment pass validation (their
`n`-th incoming message is their secret) iff the messages `n, n-1, …, n-L+1` of the adversary are
their secrets. -/
theorem lemma_3_5 (hm : n ≤ m.length) {L : ℕ} (hL : L ≤ n) :
    (∀ s < L, (seg m e s)[n - 1]? = some (e s)) ↔ ∀ s < L, m[n - 1 - s]? = some (e s) := by
  refine forall₂_congr fun s hs => ?_
  rw [seg_last hm (by omega)]

/-- **Lemma 3.4** (list form): if the segment processors before the `s`-th one pass validation,
the `s`-th one computes the sum of the first `n` messages of the adversary. -/
theorem lemma_3_4 (hm : n ≤ m.length) {s : ℕ} (hv : ∀ s' < s, (seg m e s')[n - 1]? = some (e s')) :
    (seg m e s).sum = (m.take n).sum := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [← ih (fun s' hs' => hv s' (by omega))]
    have hl := seg_length (e := e) hm s
    have hlast := hv s (by omega)
    set l := seg m e s
    have hn := NeZero.pos n
    have h1 : l = l.take (n - 1) ++ [e s] := by
      rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at hlast
      rw [← hlast, List.take_concat_get', List.take_of_length_le (by omega)]
    show ((e s :: l).take n).sum = l.sum
    rw [h1, List.take_cons hn, List.take_append_of_le_length (by simp; omega), List.take_take,
      min_self]
    simp [add_comm]

/-! ### Segments in executions -/

/-- The length of the honest segment after `a`. -/
noncomputable def gap (C : Finset (Fin n)) (a : Fin n) : ℕ :=
  open Classical in
  if h : ∃ t : ℕ, a + ((t + 1 : ℕ) : Fin n) ∈ C then Nat.find h else 0

theorem cast_succ_inj {s s' : ℕ} (hs : s < n) (hs' : s' < n)
    (h : ((s : ℕ) : Fin n) = ((s' : ℕ) : Fin n)) : s = s' := by
  have := congrArg Fin.val h
  simp only [Fin.val_natCast, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hs'] at this
  exact this

theorem gap_lt {C : Finset (Fin n)} {a : Fin n} (ha : a ∈ C) : gap C a < n := by
  classical
  have hex : ∃ t : ℕ, a + ((t + 1 : ℕ) : Fin n) ∈ C :=
    ⟨n - 1, by rw [Nat.sub_add_cancel (NeZero.pos n)]; simpa using ha⟩
  unfold gap
  rw [dif_pos hex]
  exact lt_of_le_of_lt (Nat.find_min' hex (show a + ((n - 1 + 1 : ℕ) : Fin n) ∈ C by
    rw [Nat.sub_add_cancel (NeZero.pos n)]; simpa using ha)) (by have := NeZero.pos n; omega)

theorem not_mem_of_lt_gap {C : Finset (Fin n)} {a : Fin n} (ha : a ∈ C) {s : ℕ}
    (hs : s < gap C a) : a + ((s + 1 : ℕ) : Fin n) ∉ C := by
  classical
  have hex : ∃ t : ℕ, a + ((t + 1 : ℕ) : Fin n) ∈ C :=
    ⟨n - 1, by rw [Nat.sub_add_cancel (NeZero.pos n)]; simpa using ha⟩
  unfold gap at hs
  rw [dif_pos hex] at hs
  exact Nat.find_min hex hs

theorem lt_gap_of_forall {C : Finset (Fin n)} {a : Fin n} {s : ℕ}
    (h : ∀ s' ≤ s, a + ((s' + 1 : ℕ) : Fin n) ∉ C) (ha : a ∈ C) : s < gap C a := by
  classical
  have hex : ∃ t : ℕ, a + ((t + 1 : ℕ) : Fin n) ∈ C :=
    ⟨n - 1, by rw [Nat.sub_add_cancel (NeZero.pos n)]; simpa using ha⟩
  unfold gap
  rw [dif_pos hex, Nat.lt_find_iff]
  intro t ht; exact h t ht

/-- The profile in which `C` deviates with `A` and the honest secrets are `d`. -/
abbrev dev (C : Finset (Fin n)) (A : Profile n (Fin n)) (d : Fin n → Fin n) : Profile n (Fin n) :=
  deviate aLead C A d

theorem dev_honest {C : Finset (Fin n)} {A : Profile n (Fin n)} {d : Fin n → Fin n} {i : Fin n}
    (hi : i ∉ C) : dev C A d i = aLead d i := by simp [dev, deviate, hi]

theorem dev_adv {C : Finset (Fin n)} {A : Profile n (Fin n)} {d : Fin n → Fin n} {i : Fin n}
    (hi : i ∈ C) : dev C A d i = A i := by simp [dev, deviate, hi]

/-- In reachable configurations, histories of honest processors have length at most `n`. -/
theorem honest_length_le {C : Finset (Fin n)} {A : Profile n (Fin n)} {d : Fin n → Fin n}
    {c : Config n (Fin n)} (hc : Reach (dev C A d) c) {i : Fin n} (hi : i ∉ C) :
    (c i).length ≤ n :=
  length_le_of_inv_validate (by
    have := (hc.inv i).2; rw [dev_honest hi, aLead_out] at this; exact this)

theorem pred_seg (a : Fin n) (s : ℕ) :
    a + ((s + 1 + 1 : ℕ) : Fin n) - 1 = a + ((s + 1 : ℕ) : Fin n) := by push_cast; ring

theorem pred_seg_zero (a : Fin n) : a + ((0 + 1 : ℕ) : Fin n) - 1 = a := by simp

variable {C : Finset (Fin n)} {A : Profile n (Fin n)} {d : Fin n → Fin n}

/-- The secret of the `s`-th processor of the segment after `a`. -/
def segSecret (d : Fin n → Fin n) (a : Fin n) (s : ℕ) : Fin n := d (a + ((s + 1 : ℕ) : Fin n))

/-- In a reachable configuration in which the first `L` processors of the segment after `a` have
full histories, these histories are the segment lists of the messages of `a`. -/
theorem segment_hist {c : Config n (Fin n)} (hc : Reach (dev C A d) c) {a : Fin n} (ha : a ∈ C)
    {L : ℕ} (hL : L ≤ gap C a) (hfull : ∀ s < L, (c (a + ((s + 1 : ℕ) : Fin n))).length = n) :
    ∀ s < L, c (a + ((s + 1 : ℕ) : Fin n)) = seg ((A a).sent (c a)) (segSecret d a) s := by
  intro s hs
  induction s with
  | zero =>
    have h1 := (hc.inv (a + ((0 + 1 : ℕ) : Fin n))).1
    rw [inbox, pred_seg_zero, dev_adv ha] at h1
    rw [seg, List.prefix_iff_eq_take.mp h1, hfull 0 hs]
  | succ s ih =>
    have h1 := (hc.inv (a + ((s + 1 + 1 : ℕ) : Fin n))).1
    rw [inbox, pred_seg, dev_honest (not_mem_of_lt_gap ha (by omega)),
      aLead_sent_full d _ (hfull s (by omega)), ih (by omega)] at h1
    have := List.prefix_iff_eq_take.mp h1
    rw [hfull (s + 1) hs, List.take_take, min_self] at this
    rw [this]; rfl

theorem seg_ne {a : Fin n} {s s' : ℕ} (hs : s < n - 1) (hs' : s' < n - 1) (h : s ≠ s') :
    a + ((s + 1 : ℕ) : Fin n) ≠ a + ((s' + 1 : ℕ) : Fin n) := by
  intro heq
  exact h (by have := cast_succ_inj (n := n) (by omega) (by omega) (add_left_cancel heq); omega)

theorem seg_ne_self {a : Fin n} {s : ℕ} (hs : s < n - 1) : a + ((s + 1 : ℕ) : Fin n) ≠ a := by
  intro heq
  have := cast_succ_inj (n := n) (s := s + 1) (s' := 0) (by omega) (NeZero.pos n)
    (by simpa using heq)
  omega

/-- **Pumping a segment.** If the adversary `a` has sent at least `n` messages, the processors of
its segment can process them: some reachable configuration (with the same history of `a`) gives
them their full segment histories. -/
theorem segment_pump {c : Config n (Fin n)} (hc : Reach (dev C A d) c) {a : Fin n} (ha : a ∈ C)
    (hm : n ≤ ((A a).sent (c a)).length) :
    ∃ c', Reach (dev C A d) c' ∧ c' a = c a ∧
      ∀ s < gap C a, c' (a + ((s + 1 : ℕ) : Fin n)) = seg ((A a).sent (c a)) (segSecret d a) s := by
  have hg := gap_lt ha
  suffices H : ∀ L ≤ gap C a, ∃ c', Reach (dev C A d) c' ∧ c' a = c a ∧
      ∀ s < L, c' (a + ((s + 1 : ℕ) : Fin n)) = seg ((A a).sent (c a)) (segSecret d a) s from
    H _ le_rfl
  intro L hL
  induction L with
  | zero => exact ⟨c, hc, rfl, fun s hs => absurd hs (by omega)⟩
  | succ L ih =>
    obtain ⟨c', hc', hca, hseg⟩ := ih (by omega)
    have hj : a + ((L + 1 : ℕ) : Fin n) ∉ C := not_mem_of_lt_gap ha (by omega)
    have hjL : seg ((A a).sent (c a)) (segSecret d a) L <+:
          inbox (dev C A d) c' (a + ((L + 1 : ℕ) : Fin n)) ∧
        c' (a + ((L + 1 : ℕ) : Fin n)) <+: seg ((A a).sent (c a)) (segSecret d a) L := by
      have hinv := (hc'.inv (a + ((L + 1 : ℕ) : Fin n))).1
      have hlen := honest_length_le hc' hj
      rcases L with _ | L
      · have e1 : inbox (dev C A d) c' (a + ((0 + 1 : ℕ) : Fin n)) = (A a).sent (c a) := by
          rw [inbox, pred_seg_zero, dev_adv ha, hca]
        rw [e1] at hinv ⊢
        exact ⟨List.take_prefix _ _, List.prefix_take_iff.mpr ⟨hinv, hlen⟩⟩
      · have hprev := hseg L (by omega)
        have e1 : inbox (dev C A d) c' (a + ((L + 1 + 1 : ℕ) : Fin n)) =
            seg ((A a).sent (c a)) (segSecret d a) (L + 1) := by
          rw [inbox, pred_seg, dev_honest (not_mem_of_lt_gap ha (show L < gap C a by omega)),
            hprev, aLead_sent_full d _ (seg_length hm L)]
          rfl
        rw [e1] at hinv ⊢
        exact ⟨List.prefix_refl _, hinv⟩
    set j := a + ((L + 1 : ℕ) : Fin n)
    refine ⟨Function.update c' j (seg ((A a).sent (c a)) (segSecret d a) L),
      reach_update hc' hjL.1 hjL.2 ?_, ?_, ?_⟩
    · intro p x hp
      rw [dev_honest hj, aLead_out]
      apply validate_eq_none
      have := hp.length_le; rw [seg_length hm] at this; simp at this; omega
    · rw [Function.update_of_ne (seg_ne_self (by omega)).symm, hca]
    · intro s hs
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
      · rw [Function.update_of_ne (seg_ne (by omega) (by omega) (by omega)), hseg s hs]
      · rw [Function.update_self]

/-- The conditions of Lemma 3.3 for the adversary `a` in configuration `c`: it sent at least `n`
messages (1), the sum of its first `n` messages is `v` (2), and its messages `n - s` are the
secrets of its segment (3). -/
def Cond (C : Finset (Fin n)) (A : Profile n (Fin n)) (d : Fin n → Fin n) (c : Config n (Fin n))
    (a : Fin n) (v : Fin n) : Prop :=
  n ≤ ((A a).sent (c a)).length ∧ (((A a).sent (c a)).take n).sum = v ∧
    ∀ s < gap C a, ((A a).sent (c a))[n - 1 - s]? = some (segSecret d a s)

theorem validate_eq_some {dd v : Fin n} {l : List (Fin n)} :
    validate dd l = some (some v) ↔ l.length = n ∧ l[n - 1]? = some dd ∧ l.sum = v := by
  unfold validate
  by_cases h1 : l.length = n
  · by_cases h2 : l[n - 1]? = some dd <;> simp [h1, h2]
  · simp [h1]

/-- Every honest processor lies in the segment of an exposed adversary. -/
theorem exists_adv_before (hC : C.Nonempty) {h : Fin n} (hh : h ∉ C) :
    ∃ a ∈ C, a + 1 ∉ C ∧ ∃ s < gap C a, h = a + ((s + 1 : ℕ) : Fin n) := by
  classical
  obtain ⟨c0, hc0⟩ := hC
  have hex : ∃ t : ℕ, h - ((t + 1 : ℕ) : Fin n) ∈ C := by
    have hpos : 0 < (h - c0 : Fin n).val := by
      rw [Nat.pos_iff_ne_zero, Ne, Fin.val_eq_zero_iff, sub_eq_zero]
      rintro rfl; exact hh hc0
    refine ⟨(h - c0 : Fin n).val - 1, ?_⟩
    rw [Nat.sub_add_cancel hpos, Fin.cast_val_eq_self, sub_sub_cancel]; exact hc0
  set t0 := Nat.find hex
  have ht0 : h - ((t0 + 1 : ℕ) : Fin n) ∈ C := Nat.find_spec hex
  set a := h - ((t0 + 1 : ℕ) : Fin n)
  have hall : ∀ s' ≤ t0, a + ((s' + 1 : ℕ) : Fin n) ∉ C := by
    intro s' hs'
    rcases eq_or_lt_of_le hs' with rfl | hlt
    · simpa [a] using hh
    · obtain ⟨r, hr⟩ : ∃ r, t0 = s' + r + 1 := ⟨t0 - s' - 1, by omega⟩
      have : a + ((s' + 1 : ℕ) : Fin n) = h - ((r + 1 : ℕ) : Fin n) := by
        simp only [a, hr]; push_cast; ring
      rw [this]
      exact Nat.find_min hex (show r < t0 by omega)
  refine ⟨a, ht0, ?_, t0, lt_gap_of_forall hall ht0, by simp only [a]; ring⟩
  simpa using hall 0 (Nat.zero_le _)

theorem gap_pos {a : Fin n} (ha : a ∈ C) (ha1 : a + 1 ∉ C) : 0 < gap C a :=
  lt_gap_of_forall (fun s' hs' => by
    obtain rfl : s' = 0 := by omega
    simpa using ha1) ha

/-- **Lemma 3.3.** For every deviation of a nonempty coalition from `A-LEADuni`, all honest
processors terminate with the common valid output `v` iff, in some reachable configuration, every
exposed adversary satisfies the conditions `Cond`: it has sent at least `n` messages, the sum of
its first `n` messages is `v`, and its last messages (among the first `n`) are the secrets of its
honest segment in the appropriate order. -/
theorem lemma_3_3 (hC : C.Nonempty) (v : Fin n) :
    (∀ h ∉ C, Terminates (dev C A d) h (some v)) ↔
      ∃ c, Reach (dev C A d) c ∧ ∀ a ∈ C, a + 1 ∉ C → Cond C A d c a v := by
  constructor
  · intro H
    choose g hg hgo using fun h : {h // h ∉ C} => H h.1 h.2
    obtain ⟨c, hc, hle⟩ := exists_reach_ge (P := dev C A d) g hg
    have hout : ∀ h (hh : h ∉ C), (dev C A d h).out (c h) = some (some v) := by
      intro h hh
      rw [eq_of_le_of_out hc.inv (hle ⟨h, hh⟩) (hgo ⟨h, hh⟩)]; exact hgo ⟨h, hh⟩
    have hval : ∀ h (hh : h ∉ C), (c h).length = n ∧ (c h)[n - 1]? = some (d h) ∧ (c h).sum = v :=
      fun h hh => by
        have := hout h hh; rw [dev_honest hh, aLead_out] at this; exact validate_eq_some.mp this
    refine ⟨c, hc, fun a ha ha1 => ?_⟩
    have hgap := gap_pos ha ha1
    have hfull : ∀ s < gap C a, (c (a + ((s + 1 : ℕ) : Fin n))).length = n :=
      fun s hs => (hval _ (not_mem_of_lt_gap ha hs)).1
    have hseg := segment_hist hc ha le_rfl hfull
    have hm : n ≤ ((A a).sent (c a)).length := by
      have h1 := (hc.inv (a + ((0 + 1 : ℕ) : Fin n))).1
      rw [inbox, pred_seg_zero, dev_adv ha] at h1
      have := h1.length_le; rw [hfull 0 hgap] at this; exact this
    refine ⟨hm, ?_, fun s hs => ?_⟩
    · have := (hval _ (not_mem_of_lt_gap ha hgap)).2.2
      rw [hseg 0 hgap] at this; exact this
    · have := (hval _ (not_mem_of_lt_gap ha hs)).2.1
      rw [hseg s hs, seg_last hm (by have := gap_lt ha; omega)] at this
      exact this
  · rintro ⟨c, hc, hcond⟩ h hh
    obtain ⟨a, ha, ha1, s, hs, rfl⟩ := exists_adv_before hC hh
    obtain ⟨hm, hsum, hsec⟩ := hcond a ha ha1
    obtain ⟨c', hc', -, hseg⟩ := segment_pump hc ha hm
    refine ⟨c', hc', ?_⟩
    rw [dev_honest hh, aLead_out, validate_eq_some, hseg s hs]
    have hgl := gap_lt ha
    refine ⟨seg_length hm s, ?_, ?_⟩
    · rw [seg_last hm (by omega)]; exact hsec s hs
    · rw [lemma_3_4 hm (fun s' hs' => by rw [seg_last hm (by omega)]; exact hsec s' (by omega))]
      exact hsum

theorem Cond.mono {c c' : Config n (Fin n)} (hcc : Le c c') {a v : Fin n} (h : Cond C A d c a v) :
    Cond C A d c' a v := by
  obtain ⟨hm, hsum, hsec⟩ := h
  have hp := (A a).sent_mono (hcc a)
  have htake : ((A a).sent (c' a)).take n = ((A a).sent (c a)).take n := by
    obtain ⟨t, ht⟩ := hp
    rw [← ht, List.take_append_of_le_length hm]
  refine ⟨hm.trans hp.length_le, htake ▸ hsum, fun s hs => getElem?_of_prefix hp (hsec s hs)⟩

/-- **Lemma 3.3**, for executions: in the execution under any fair oblivious schedule, all honest
processors terminate with output `v` iff at some time the conditions hold for every exposed
adversary. -/
theorem lemma_3_3_run (hC : C.Nonempty) {σ : ℕ → Fin n} (hσ : Fair σ) (v : Fin n) :
    (∀ h ∉ C, ∃ t, (dev C A d h).out (run (dev C A d) σ t h) = some (some v)) ↔
      ∃ t, ∀ a ∈ C, a + 1 ∉ C → Cond C A d (run (dev C A d) σ t) a v := by
  simp only [terminates_iff hσ]
  rw [lemma_3_3 hC]
  constructor
  · rintro ⟨c, hc, hcond⟩
    obtain ⟨T, hT⟩ := exists_le_run hσ hc
    exact ⟨T, fun a ha ha1 => (hcond a ha ha1).mono hT⟩
  · rintro ⟨t, ht⟩
    exact ⟨_, reach_run σ t, ht⟩

end Podc.FairLeaderElection
