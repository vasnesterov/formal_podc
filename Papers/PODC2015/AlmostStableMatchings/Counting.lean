import Papers.PODC2015.AlmostStableMatchings.Invariants

/-!
# Counting bad men: Lemma 4.5 (and the per-iteration facts used for Lemma 4.4)

We fix one iteration `j` of the outer loop of `ASM`, started in a reachable state `s₀` in which
every `A` is empty, with active set `act = {m | |Q^m| ≥ 2^j}`. Every state of the iteration is
reached from `s₀` by `IStep`s (a `ProposalRound`, or the initialization of `QuantileMatch` by the
men of `act`), and satisfies `IInv`: the invariants `Inv`, inactive men never propose, and
inactive men have `|Q| < 2^j`.

* A man is *good* if he is matched or has been rejected by all his acceptable partners
  (`Q = ∅`); otherwise he is *bad* (`badSet`).
* `card_bad_act_antitone`: the number of bad active men never increases (matched men never
  decrease in number, inactive men are never newly matched).
* `lemma_4_5`: with `ℓ` calls of `QuantileMatch`, at the end of the iteration
  `ℓ · #(bad ∩ act) ≤ 2k |act|`; for `ℓ ≥ 2k/δ` this is "at most a `δ`-fraction of the active men
  are bad". The proof is the paper's: every bad active man witnesses, in every call, a quantile
  rejection (a woman getting a strictly better partner, or one of his own quantiles being
  emptied), and there are at most `2k |act|` of those per iteration. We use the potential
  `Π = ∑_{m ∈ act} #(quantiles of Q^m) + ∑_w ψ_w`.
* `matched_inactive_le`: the inactive men displaced during an iteration are at most the bad active
  men at its start; with the potential of `BadMen.lean` (`reach_Fpot`) this is the step of
  Lemma 4.4 that the paper's proof misses.
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2015.AlmostStableMatchings

open Finset

variable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

/-- A bijection between the matched men and the matched women. -/
lemma card_matched_eq {f : M → Option W} {g : W → Option M}
    (h : ∀ m w, f m = some w ↔ g w = some m) :
    #({m | f m ≠ none} : Finset M) = #({w | g w ≠ none} : Finset W) := by
  refine Finset.card_bij' (fun m hm => (f m).get (Option.isSome_iff_ne_none.2 (by simpa using hm)))
    (fun w hw => (g w).get (Option.isSome_iff_ne_none.2 (by simpa using hw))) ?_ ?_ ?_ ?_
  · intro m hm
    have hs : (f m).isSome := Option.isSome_iff_ne_none.2 (by simpa using hm)
    have := (h m ((f m).get hs)).1 (Option.some_get hs).symm
    simp [this]
  · intro w hw
    have hs : (g w).isSome := Option.isSome_iff_ne_none.2 (by simpa using hw)
    have := (h ((g w).get hs) w).2 (Option.some_get hs).symm
    simp [this]
  · intro m hm
    have hs : (f m).isSome := Option.isSome_iff_ne_none.2 (by simpa using hm)
    have := (h m ((f m).get hs)).1 (Option.some_get hs).symm
    simp [this]
  · intro w hw
    have hs : (g w).isSome := Option.isSome_iff_ne_none.2 (by simpa using hw)
    have := (h ((g w).get hs) w).2 (Option.some_get hs).symm
    simp [this]

namespace Prefs

variable (P : Prefs M W) (k : ℕ)

/-- Bad men: unmatched and not rejected by all acceptable partners. -/
def badSet (s : St M W) : Finset M := univ.filter fun m => s.pm m = none ∧ (s.Q m).Nonempty

/-- One step inside an iteration of the outer loop. -/
def IStep (mm : MMOracle M W) (act : Finset M) (s s' : St M W) : Prop :=
  s' = P.prStep k mm s ∨ s' = P.initQM k act s

/-- Invariants inside iteration `j` with active set `act`. -/
structure IInv (j : ℕ) (act : Finset M) (s : St M W) : Prop where
  inv : P.Inv k s
  A_inact : ∀ m ∉ act, s.A m = ∅
  Q_inact : ∀ m ∉ act, (s.Q m).card < 2 ^ j

variable {P k} {mm : MMOracle M W} {act : Finset M} {j : ℕ}

lemma mem_badSet {s : St M W} {m : M} : m ∈ badSet s ↔ s.pm m = none ∧ (s.Q m).Nonempty := by
  simp [badSet]

lemma IInv.istep {s s' : St M W} (hI : P.IInv k j act s) (h : P.IStep k mm act s s') :
    P.IInv k j act s' := by
  rcases h with rfl | rfl
  · exact ⟨hI.inv.prStep, fun m hm => Finset.subset_empty.1
      ((A_prStep_subset (mm := mm) m).trans (hI.A_inact m hm).le),
      fun m hm => (Finset.card_le_card (Q_prStep_subset (mm := mm) m)).trans_lt (hI.Q_inact m hm)⟩
  · refine ⟨hI.inv.initQM, fun m hm => ?_, fun m hm => by simpa using hI.Q_inact m hm⟩
    rw [initQM_A, ite_eq_right (fun h => hm h.1)]; exact hI.A_inact m hm

lemma IInv.reach {s s' : St M W} (hI : P.IInv k j act s)
    (h : Relation.ReflTransGen (P.IStep k mm act) s s') : P.IInv k j act s' := by
  induction h with
  | refl => exact hI
  | tail _ hst ih => exact ih.istep hst

/-! ## Per-step monotonicity -/

lemma istep_Q {s s' : St M W} (h : P.IStep k mm act s s') (m : M) : s'.Q m ⊆ s.Q m := by
  rcases h with rfl | rfl
  · exact Q_prStep_subset (mm := mm) m
  · simp

lemma istep_pw {s s' : St M W} (hk : 1 ≤ k) (hI : P.Inv k s) (h : P.IStep k mm act s s')
    (w : W) : s.pw w ≠ none → s'.pw w ≠ none := by
  rcases h with rfl | rfl
  · exact (lemma_3_1 hk hI w).1
  · simp

lemma istep_inactive_pm {s s' : St M W} (hI : P.IInv k j act s) (h : P.IStep k mm act s s')
    {m : M} (hm : m ∉ act) : s.pm m = none → s'.pm m = none := by
  intro h0
  rcases h with rfl | rfl
  · by_contra h1
    have := A_nonempty_of_newly_matched h0 h1
    rw [hI.A_inact m hm] at this; simp at this
  · simpa using h0

lemma istep_new_partner {s s' : St M W} (hI : P.IInv k j act s) (h : P.IStep k mm act s s')
    {w : W} (hne : s'.pw w ≠ s.pw w) : ∃ m ∈ act, s'.pw w = some m := by
  rcases h with rfl | rfl
  · cases h0 : (P.mmOut k mm s).pw w with
    | none => exact absurd (by rw [pw_prStep, h0]; rfl) hne
    | some m =>
      have hm : (P.prStep k mm s).pw w = some m := by rw [pw_prStep, h0]; rfl
      refine ⟨m, ?_, hm⟩
      by_contra hma
      have := pw_prStep_new hm hne
      rw [hI.A_inact m hma] at this; simp at this
  · simp at hne

/-! ## Lifting to whole runs inside an iteration -/

section Reach

variable {s s' : St M W}

lemma reach_Q (h : Relation.ReflTransGen (P.IStep k mm act) s s') (m : M) : s'.Q m ⊆ s.Q m := by
  induction h with
  | refl => exact le_rfl
  | tail _ hst ih => exact (istep_Q hst m).trans ih

lemma reach_pw (hk : 1 ≤ k) (hI : P.IInv k j act s)
    (h : Relation.ReflTransGen (P.IStep k mm act) s s') (w : W) :
    s.pw w ≠ none → s'.pw w ≠ none := by
  induction h with
  | refl => exact id
  | tail hr hst ih => exact fun h0 => istep_pw hk (hI.reach hr).inv hst w (ih h0)

lemma reach_inactive_pm (hI : P.IInv k j act s)
    (h : Relation.ReflTransGen (P.IStep k mm act) s s') {m : M} (hm : m ∉ act) :
    s.pm m = none → s'.pm m = none := by
  induction h with
  | refl => exact id
  | tail hr hst ih => exact fun h0 => istep_inactive_pm (hI.reach hr) hst hm (ih h0)

lemma reach_new_partner (hI : P.IInv k j act s)
    (h : Relation.ReflTransGen (P.IStep k mm act) s s') {w : W} (hne : s'.pw w ≠ s.pw w) :
    ∃ m ∈ act, s'.pw w = some m := by
  induction h with
  | refl => exact absurd rfl hne
  | @tail b c hr hst ih =>
    by_cases hbc : c.pw w = b.pw w
    · rw [hbc]; exact ih (hbc ▸ hne)
    · exact istep_new_partner (hI.reach hr) hst hbc

end Reach

/-! ## Counting matched and bad men between two states of an iteration -/

section TwoStates

variable {s s' : St M W}

/-- Under `Inv`, the active men split into bad, matched and fully rejected ones. -/
lemma card_split (hI : P.Inv k s) (act : Finset M) :
    #(act.filter fun m => m ∈ badSet s) + #(act.filter fun m => s.pm m ≠ none) +
      #(act.filter fun m => s.Q m = ∅) = #act := by
  have h1 := Finset.card_filter_add_card_filter_not (s := act) (fun m => s.pm m = none)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := act.filter fun m => s.pm m = none) (fun m => (s.Q m).Nonempty)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : (act.filter fun m => s.pm m = none ∧ ¬ (s.Q m).Nonempty) =
      act.filter fun m => s.Q m = ∅ := by
    ext m
    simp only [Finset.mem_filter, Finset.not_nonempty_iff_eq_empty]
    constructor
    · rintro ⟨h, -, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      refine ⟨h, ?_, h'⟩
      cases hp : s.pm m with
      | none => rfl
      | some w => have := hI.p_mem m w hp; rw [h'] at this; simp at this
  have h4 : (act.filter fun m => m ∈ badSet s) =
      act.filter fun m => s.pm m = none ∧ (s.Q m).Nonempty := by
    ext m; simp [mem_badSet]
  rw [h3] at h2; rw [h4]
  simp only [ne_eq] at h1 ⊢
  omega

/-- The number of matched men never decreases. -/
lemma card_matched_le (hI : P.Inv k s) (hI' : P.Inv k s')
    (hpw : ∀ w, s.pw w ≠ none → s'.pw w ≠ none) :
    #({m | s.pm m ≠ none} : Finset M) ≤ #({m | s'.pm m ≠ none} : Finset M) := by
  rw [card_matched_eq hI.cons, card_matched_eq hI'.cons]
  exact Finset.card_le_card fun w hw => by simpa using hpw w (by simpa using hw)

/-- The number of matched men never decreases, split into active and inactive men. -/
lemma card_matched_act_le (hI : P.Inv k s) (hI' : P.Inv k s')
    (hpw : ∀ w, s.pw w ≠ none → s'.pw w ≠ none) :
    #(act.filter fun m => s.pm m ≠ none) + #(actᶜ.filter fun m => s.pm m ≠ none) ≤
      #(act.filter fun m => s'.pm m ≠ none) + #(actᶜ.filter fun m => s'.pm m ≠ none) := by
  have hall := card_matched_le hI hI' hpw
  have e1 := Finset.card_filter_add_card_filter_not (s := (univ.filter fun m => s.pm m ≠ none))
    (fun m => m ∈ act)
  have e2 := Finset.card_filter_add_card_filter_not (s := (univ.filter fun m => s'.pm m ≠ none))
    (fun m => m ∈ act)
  have r : ∀ (t : St M W), (univ.filter fun m => t.pm m ≠ none).filter (fun m => m ∈ act) =
      act.filter fun m => t.pm m ≠ none := fun t => by ext; simp [and_comm]
  have r' : ∀ (t : St M W), (univ.filter fun m => t.pm m ≠ none).filter (fun m => m ∉ act) =
      actᶜ.filter fun m => t.pm m ≠ none := fun t => by ext; simp [and_comm]
  rw [r, r'] at e1 e2
  omega

/-- **The number of bad active men never increases.** -/
lemma card_bad_act_le (hI : P.Inv k s) (hI' : P.Inv k s')
    (hpw : ∀ w, s.pw w ≠ none → s'.pw w ≠ none)
    (hin : ∀ m ∉ act, s.pm m = none → s'.pm m = none) (hQ : ∀ m, s'.Q m ⊆ s.Q m) :
    #(act.filter fun m => m ∈ badSet s') ≤ #(act.filter fun m => m ∈ badSet s) := by
  have h1 := card_split hI act
  have h2 := card_split hI' act
  have h3 := card_matched_act_le (act := act) hI hI' hpw
  have h4 : #(actᶜ.filter fun m => s'.pm m ≠ none) ≤ #(actᶜ.filter fun m => s.pm m ≠ none) :=
    Finset.card_le_card fun m hm => by
      simp only [Finset.mem_filter, Finset.mem_compl] at hm ⊢
      exact ⟨hm.1, fun h => hm.2 (hin m hm.1 h)⟩
  have h5 : #(act.filter fun m => s.Q m = ∅) ≤ #(act.filter fun m => s'.Q m = ∅) :=
    Finset.card_le_card fun m hm => by
      simp only [Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, Finset.subset_empty.1 (hm.2 ▸ hQ m)⟩
  omega

/-- The matched inactive men lost during an iteration are at most the bad active men at its
start. -/
lemma matched_inactive_le (hI : P.Inv k s) (hI' : P.Inv k s')
    (hpw : ∀ w, s.pw w ≠ none → s'.pw w ≠ none)
    (hin : ∀ m ∉ act, s.pm m = none → s'.pm m = none) (hQ : ∀ m, s'.Q m ⊆ s.Q m) :
    #(actᶜ.filter fun m => s.pm m ≠ none) ≤
      #(actᶜ.filter fun m => s'.pm m ≠ none) + #(act.filter fun m => m ∈ badSet s) := by
  have h1 := card_split hI act
  have h2 := card_split hI' act
  have h3 := card_matched_act_le (act := act) hI hI' hpw
  have h4 : #(actᶜ.filter fun m => s'.pm m ≠ none) ≤ #(actᶜ.filter fun m => s.pm m ≠ none) :=
    Finset.card_le_card fun m hm => by
      simp only [Finset.mem_filter, Finset.mem_compl] at hm ⊢
      exact ⟨hm.1, fun h => hm.2 (hin m hm.1 h)⟩
  have h5 : #(act.filter fun m => s.Q m = ∅) ≤ #(act.filter fun m => s'.Q m = ∅) :=
    Finset.card_le_card fun m hm => by
      simp only [Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, Finset.subset_empty.1 (hm.2 ▸ hQ m)⟩
  omega

end TwoStates

/-! ## The potential `Π` and Lemma 4.5 -/

variable (P k) in
/-- Number of nonempty quantiles of `Q^m`. -/
def Phi (s : St M W) (m : M) : ℕ := #((s.Q m).image (P.qM k m))

variable (P k) in
/-- `Π = ∑_{m ∈ act} Φ_m + ∑_w ψ_w`. -/
def Pot (act : Finset M) (s : St M W) : ℕ := ∑ m ∈ act, P.Phi k s m + ∑ w, P.psi k s w

/-- Number of men with `A ≠ ∅`. -/
def nA (s : St M W) : ℕ := #(univ.filter fun m => (s.A m).Nonempty)

lemma Phi_le (hk : 1 ≤ k) {s : St M W} (hI : P.Inv k s) (m : M) : P.Phi k s m ≤ k := by
  have : (s.Q m).image (P.qM k m) ⊆ Finset.Icc 1 k := fun c hc => by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hc
    exact P.qM_mem_Icc hk (hI.mem_NM hw)
  unfold Phi
  exact (Finset.card_le_card this).trans (by simp)

lemma mem_act_of_A {s : St M W} (hI : P.IInv k j act s) {m : M} (h : (s.A m).Nonempty) :
    m ∈ act := by
  by_contra hm; rw [hI.A_inact m hm] at h; simp at h

/-- One `ProposalRound`: every man whose `A` becomes empty either got matched (some woman gets a
strictly better partner) or saw one of his quantiles emptied. -/
lemma pot_prStep (hk : 1 ≤ k) {s : St M W} (hI : P.IInv k j act s) :
    P.Pot k act (P.prStep k mm s) + nA s ≤ P.Pot k act s + nA (P.prStep k mm s) := by
  set s' := P.prStep k mm s
  set μ := P.mmOut k mm s
  have hI0 := hI.inv
  set D1 := univ.filter fun m => (s.A m).Nonempty ∧ μ.pm m ≠ none
  set D2 := univ.filter fun m => (s.A m).Nonempty ∧ μ.pm m = none ∧ ¬ (s'.A m).Nonempty
  have hn : nA s ≤ nA s' + #D1 + #D2 := by
    have hsub : (univ.filter fun m => (s.A m).Nonempty) ⊆
        ((univ.filter fun m => (s'.A m).Nonempty) ∪ D1) ∪ D2 := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, D1, D2]
      by_cases h1 : (s'.A m).Nonempty
      · exact Or.inl (Or.inl h1)
      · by_cases h2 : μ.pm m = none
        · exact Or.inr ⟨hm, h2, h1⟩
        · exact Or.inl (Or.inr ⟨hm, h2⟩)
    have := Finset.card_le_card hsub
    have h2 := Finset.card_union_le ((univ.filter fun m => (s'.A m).Nonempty) ∪ D1) D2
    have h3 := Finset.card_union_le (univ.filter fun m => (s'.A m).Nonempty) D1
    unfold nA; omega
  have hD1 : #D1 ≤ #(univ.filter fun w => μ.pw w ≠ none) := by
    rw [← card_matched_eq (fun m w => P.mmOut_cons mm s (m := m) (w := w))]
    exact Finset.card_le_card fun m hm => by simp only [D1, Finset.mem_filter] at hm ⊢; exact ⟨hm.1, hm.2.2⟩
  have hW : ∑ w, P.psi k s' w + #(univ.filter fun w => μ.pw w ≠ none) ≤ ∑ w, P.psi k s w := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w _ => ?_
    split_ifs with h
    · obtain ⟨m0, hm0⟩ := Option.ne_none_iff_exists'.1 h
      have hne : s'.pw w ≠ s.pw w := by
        have e : s'.pw w = some m0 := by
          show (P.prStep k mm s).pw w = some m0
          rw [pw_prStep]; rw [show (P.mmOut k mm s).pw w = some m0 from hm0]; rfl
        rw [e]; intro e'
        have h1 := (hI0.cons m0 w).2 e'.symm
        have h2 := mmOut_pm_unmatched hI0 ((P.mmOut_cons mm s).2 hm0)
        rw [h1] at h2; cases h2
      exact (lemma_3_1 hk hI0 w).2 hne
    · simpa using psi_prStep_le hk hI0 w
  have hD2 : D2 ⊆ act := fun m hm => mem_act_of_A hI (Finset.mem_filter.1 hm).2.1
  have hM : ∑ m ∈ act, P.Phi k s' m + #D2 ≤ ∑ m ∈ act, P.Phi k s m := by
    have e : #D2 = ∑ m ∈ act, if m ∈ D2 then 1 else 0 := by
      rw [Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hD2]
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun m _ => ?_
    have hsub : (s'.Q m).image (P.qM k m) ⊆ (s.Q m).image (P.qM k m) :=
      Finset.image_subset_image (Q_prStep_subset (mm := mm) m)
    split_ifs with h
    · simp only [D2, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.not_nonempty_iff_eq_empty] at h
      obtain ⟨⟨w, hw⟩, hμ, hA'⟩ := h
      have hss : (s'.Q m).image (P.qM k m) ⊂ (s.Q m).image (P.qM k m) := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun heq => ?_⟩
        have hc : P.qM k m w ∈ (s'.Q m).image (P.qM k m) :=
          heq ▸ Finset.mem_image_of_mem _ (hI0.A_sub m hw)
        obtain ⟨w', hw', he⟩ := Finset.mem_image.1 hc
        have hw'Q := (mem_Q_prStep mm s).1 hw'
        have : w' ∈ s'.A m := (mem_A_prStep mm s).2
          ⟨hμ, hI0.A_closed m w hw w' hw'Q.1 he, hw'Q.2⟩
        rw [hA'] at this; simp at this
      have := Finset.card_lt_card hss
      unfold Phi; omega
    · have := Finset.card_le_card hsub
      unfold Phi; omega
  unfold Pot; omega

lemma reach_prIter {s : St M W} (t : ℕ) :
    Relation.ReflTransGen (P.IStep k mm act) s ((P.prStep k mm)^[t] s) := by
  induction t with
  | zero => exact Relation.ReflTransGen.refl
  | succ t ih => rw [Function.iterate_succ_apply']; exact ih.tail (Or.inl rfl)

lemma reach_qm {s : St M W} :
    Relation.ReflTransGen (P.IStep k mm act) s (P.quantileMatch k mm act s) :=
  (Relation.ReflTransGen.single (r := P.IStep k mm act) (Or.inr rfl)).trans (reach_prIter k)

lemma reach_qmIter {s : St M W} (ℓ : ℕ) :
    Relation.ReflTransGen (P.IStep k mm act) s ((P.quantileMatch k mm act)^[ℓ] s) := by
  induction ℓ with
  | zero => exact Relation.ReflTransGen.refl
  | succ t ih => rw [Function.iterate_succ_apply']; exact ih.trans reach_qm

lemma pot_prIter (hk : 1 ≤ k) {s : St M W} (hI : P.IInv k j act s) (t : ℕ) :
    P.Pot k act ((P.prStep k mm)^[t] s) + nA s ≤ P.Pot k act s + nA ((P.prStep k mm)^[t] s) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have := pot_prStep (mm := mm) hk (hI.reach (reach_prIter (mm := mm) (act := act) t))
    omega

lemma bestQ_nonempty {m : M} {Q : Finset W} (h : Q.Nonempty) : (P.bestQ k m Q).Nonempty := by
  obtain ⟨w, hw, hmin⟩ := Q.exists_min_image (P.qM k m) h
  exact ⟨w, mem_bestQ.2 ⟨hw, hmin⟩⟩

@[simp] lemma psi_initQM {s : St M W} (w : W) : P.psi k (P.initQM k act s) w = P.psi k s w := rfl

@[simp] lemma Phi_initQM {s : St M W} (m : M) : P.Phi k (P.initQM k act s) m = P.Phi k s m := by
  simp [Phi]

/-- One call of `QuantileMatch` decreases `Π` by at least the number of bad active men. -/
lemma pot_qm (hk : 1 ≤ k) {s : St M W} (hI : P.IInv k j act s) :
    P.Pot k act (P.quantileMatch k mm act s) + #(act.filter fun m => m ∈ badSet s) ≤
      P.Pot k act s := by
  have hI1 : P.IInv k j act (P.initQM k act s) := hI.istep (mm := mm) (Or.inr rfl)
  have h1 := pot_prIter (mm := mm) hk hI1 k
  have h2 : nA ((P.prStep k mm)^[k] (P.initQM k act s)) = 0 := by
    unfold nA
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _
    rw [lemma_3_2 hk hI1.inv m]; simp
  have h3 : #(act.filter fun m => m ∈ badSet s) ≤ nA (P.initQM k act s) := by
    refine Finset.card_le_card fun m hm => ?_
    simp only [Finset.mem_filter, mem_badSet] at hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [initQM_A, ite_eq_left ⟨hm.1, hm.2.1⟩]
    exact bestQ_nonempty hm.2.2
  have h4 : P.Pot k act (P.initQM k act s) = P.Pot k act s := by simp [Pot]
  unfold quantileMatch
  omega

/-- Bad active men never increase along an iteration. -/
lemma card_bad_reach (hk : 1 ≤ k) {s s' : St M W} (hI : P.IInv k j act s)
    (h : Relation.ReflTransGen (P.IStep k mm act) s s') :
    #(act.filter fun m => m ∈ badSet s') ≤ #(act.filter fun m => m ∈ badSet s) :=
  card_bad_act_le hI.inv (hI.reach h).inv (reach_pw hk hI h) (fun m hm => reach_inactive_pm hI h hm)
    (reach_Q h)

lemma pot_qmIter (hk : 1 ≤ k) {s : St M W} (hI : P.IInv k j act s) (ℓ : ℕ) :
    P.Pot k act ((P.quantileMatch k mm act)^[ℓ] s) +
      ℓ * #(act.filter fun m => m ∈ badSet ((P.quantileMatch k mm act)^[ℓ] s)) ≤
      P.Pot k act s := by
  induction ℓ generalizing s with
  | zero => simp
  | succ ℓ ih =>
    rw [Function.iterate_succ_apply]
    have h1 := ih (hI.reach (reach_qm (mm := mm)))
    have h2 := pot_qm (mm := mm) hk hI
    have h3 := card_bad_reach hk hI ((reach_qm (mm := mm)).trans (reach_qmIter (s :=
      P.quantileMatch k mm act s) ℓ))
    rw [Nat.succ_mul]
    omega

/-- Over a whole iteration `Π` decreases by at most `2k |act|`: active men have at most `k`
quantiles, and at most `|act|` women change partner, each improving by at most `k`. -/
lemma pot_le (hk : 1 ≤ k) {s s' : St M W} (hI : P.IInv k j act s)
    (h : Relation.ReflTransGen (P.IStep k mm act) s s') :
    P.Pot k act s ≤ P.Pot k act s' + 2 * k * #act := by
  have hI' := (hI.reach h).inv
  set C := univ.filter fun w => s'.pw w ≠ s.pw w
  have hC : #C ≤ #act := by
    rcases act.eq_empty_or_nonempty with he | ⟨m0, hm0⟩
    · have : C = ∅ := Finset.eq_empty_of_forall_notMem fun w hw => by
        obtain ⟨m, hm, -⟩ := reach_new_partner hI h (Finset.mem_filter.1 hw).2
        rw [he] at hm; simp at hm
      rw [this]; simp
    · refine Finset.card_le_card_of_injOn (fun w => (s'.pw w).getD m0) ?_ ?_
      · intro w hw
        obtain ⟨m, hm, e⟩ := reach_new_partner hI h (Finset.mem_filter.1 hw).2
        simp [e, hm]
      · intro w hw w' hw' he
        obtain ⟨m, -, e⟩ := reach_new_partner hI h (Finset.mem_filter.1 hw).2
        obtain ⟨m', -, e'⟩ := reach_new_partner hI h (Finset.mem_filter.1 hw').2
        simp only [e, e', Option.getD_some] at he
        subst he
        have h1 := (hI'.cons m w).2 e
        have h2 := (hI'.cons m w').2 e'
        rw [h1] at h2; exact Option.some_injective _ h2
  have hW : ∑ w, P.psi k s w ≤ ∑ w, P.psi k s' w + k * #C := by
    rw [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w _ => ?_
    split_ifs with hc
    · have := psi_le P k hk hI.inv w
      have := one_le_psi P k hk hI' w
      omega
    · have : P.psi k s' w = P.psi k s w := by unfold psi; rw [not_not.1 hc]
      omega
  have hM : ∑ m ∈ act, P.Phi k s m ≤ k * #act := by
    rw [Nat.mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun m _ => Phi_le hk hI.inv m
  unfold Pot
  have := Nat.mul_le_mul_left k hC
  have e : 2 * k * #act = k * #act + k * #act := by ring
  omega

/-- **Lemma 4.5 (few bad men).** After an iteration of the outer loop with `ℓ` calls of
`QuantileMatch`, `ℓ · #(bad active men) ≤ 2 k · #(active men)`; with `ℓ ≥ 2k/δ` at most a
`δ`-fraction of the active men are bad. -/
theorem lemma_4_5 (hk : 1 ≤ k) {s : St M W} (hI : P.IInv k j act s) (ℓ : ℕ) :
    ℓ * #(act.filter fun m => m ∈ badSet ((P.quantileMatch k mm act)^[ℓ] s)) ≤ 2 * k * #act := by
  have h1 := pot_qmIter (mm := mm) hk hI ℓ
  have h2 := pot_le hk hI (reach_qmIter (mm := mm) ℓ)
  omega

end Prefs

end Papers.PODC2015.AlmostStableMatchings
