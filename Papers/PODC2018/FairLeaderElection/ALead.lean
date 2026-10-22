import Papers.PODC2018.FairLeaderElection.Game

/-!
# The protocol `A-LEADuni` (Section 3 and Appendix A of [YM18])

Every processor `i` draws a secret `d i ∈ [n]` (here `Fin n`). The origin (processor `0`, the
paper's processor 1) sends its secret at initialization and then forwards its first `n - 1`
incoming messages; a normal processor buffers: upon each of its first `n` incoming messages it sends
the content of its one-message buffer (initially its own secret) and stores the new message. After
`n` incoming messages a processor checks that the `n`-th one is its own secret (else it aborts with
`⊥`) and outputs the sum of the `n` incoming messages modulo `n`.

As sequences, both kinds of processors send `d i` followed by their first `n - 1` incoming messages;
they differ only in timing (the origin is one message ahead).

Main results: the honest execution elects `∑ i, d i` (`outcome_aLead`), so `A-LEADuni` is a fair
leader election protocol (`isFLE_aLead`).
-/

namespace Podc.FairLeaderElection

open Cslib.UniRing
open Fin.NatCast Fin.CommRing

variable {n : ℕ} [NeZero n]

theorem take_cons_prefix {α : Type*} (d : α) {h h' : List α} (hh : h <+: h') {k k' : ℕ}
    (hk : k ≤ k') (hkh : k ≤ h.length + 1) : (d :: h).take k <+: (d :: h').take k' := by
  obtain ⟨t, rfl⟩ := hh
  have : (d :: h).take k = (d :: (h ++ t)).take k := by
    rw [← List.cons_append, List.take_append_of_le_length (by simpa using hkh)]
  rw [this]
  exact List.take_prefix_take_left hk

/-- Validation and output after `n` incoming messages: abort (`⊥ = none`) unless the `n`-th
incoming message is the own secret `d`; otherwise output the sum of the incoming messages. -/
def validate (d : Fin n) (h : List (Fin n)) : Option (Option (Fin n)) :=
  if h.length = n then some (if h[n - 1]? = some d then some h.sum else none) else none

/-- A normal processor of `A-LEADuni` with secret `d` (a one-message buffer). -/
def normal (d : Fin n) : Proc (Fin n) (Option (Fin n)) where
  sent h := (d :: h).take (min h.length n)
  sent_snoc h _ := take_cons_prefix d (List.prefix_append _ _)
    (by simp only [List.length_append, List.length_singleton]; omega) (by omega)
  out := validate d

/-- The origin of `A-LEADuni` with secret `d`: sends `d` at wake-up and forwards. -/
def origin (d : Fin n) : Proc (Fin n) (Option (Fin n)) where
  sent h := (d :: h).take (min (h.length + 1) n)
  sent_snoc h _ := take_cons_prefix d (List.prefix_append _ _)
    (by simp only [List.length_append, List.length_singleton]; omega) (by omega)
  out := validate d

/-- The honest profile of `A-LEADuni` for the secrets `d`; processor `0` is the origin. -/
def aLead (d : Fin n → Fin n) : Profile n (Fin n) :=
  fun i => if i = 0 then origin (d i) else normal (d i)

theorem aLead_out (d : Fin n → Fin n) (i : Fin n) : (aLead d i).out = validate (d i) := by
  unfold aLead; split_ifs <;> rfl

theorem aLead_sent_length (d : Fin n → Fin n) (i : Fin n) (h : List (Fin n)) :
    min h.length n ≤ ((aLead d i).sent h).length ∧ ((aLead d i).sent h).length ≤ n ∧
      (i = 0 → min (h.length + 1) n ≤ ((aLead d i).sent h).length) := by
  unfold aLead
  split_ifs with hi
  · simp only [origin, List.length_take, List.length_cons]; omega
  · simp only [normal, List.length_take, List.length_cons]; refine ⟨by omega, by omega, ?_⟩
    intro h0; exact absurd h0 hi

theorem aLead_sent_full (d : Fin n → Fin n) (i : Fin n) {h : List (Fin n)} (hh : h.length = n) :
    (aLead d i).sent h = (d i :: h).take n := by
  unfold aLead
  split_ifs
  · simp only [origin, hh]; congr 1; omega
  · simp only [normal, hh, min_self]

theorem validate_eq_none {d : Fin n} {h : List (Fin n)} (hh : h.length ≠ n) :
    validate d h = none := by simp [validate, hh]

theorem length_le_of_inv_validate {d : Fin n} {h : List (Fin n)}
    (hinv : ∀ p x, p ++ [x] <+: h → validate d p = none) : h.length ≤ n := by
  by_contra hlt
  push_neg at hlt
  have := hinv (h.take n) (h[n]'hlt) (by
    rw [List.take_concat_get']; exact List.take_prefix _ _)
  simp [validate, List.length_take, min_eq_left hlt.le] at this

/-! ### Counting on the ring -/

/-- A function on the ring that does not decrease along the ring is constant. -/
theorem ring_const (f : Fin n → ℕ) (hf : ∀ i, f (i - 1) ≤ f i) (i j : Fin n) : f i = f j := by
  have key : ∀ (i : Fin n) (t : ℕ), f (i - t) ≤ f i := by
    intro i t
    induction t with
    | zero => simp
    | succ t ih =>
      have := hf (i - t)
      rw [sub_sub, ← Nat.cast_succ] at this
      exact this.trans ih
  have h1 := key i (i - j : Fin n).val
  have h2 := key j (j - i : Fin n).val
  simp only [Fin.cast_val_eq_self, sub_sub_cancel] at h1 h2
  omega

/-! ### The honest execution -/

/-- `t`-th predecessor-of-predecessor index: `i - (t + 1)`. -/
def back (i : Fin n) (t : ℕ) : Fin n := i - ((t + 1 : ℕ) : Fin n)

/-- The final history of processor `i` in the honest execution: `d (i-1), d (i-2), …, d (i-n)`. -/
def honestHist (d : Fin n → Fin n) (i : Fin n) : List (Fin n) :=
  List.ofFn fun t : Fin n => d (back i t)

theorem honestHist_length (d : Fin n → Fin n) (i : Fin n) : (honestHist d i).length = n := by
  simp [honestHist]

theorem honestHist_succ (d : Fin n → Fin n) (i : Fin n) :
    honestHist d i = (d (i - 1) :: honestHist d (i - 1)).take n := by
  apply List.ext_getElem
  · simp [honestHist]
  · intro t h1 h2
    simp only [honestHist, List.getElem_ofFn, List.length_ofFn] at h1 ⊢
    rw [List.getElem_take]
    rcases t with _ | t
    · simp [back]
    · simp only [List.getElem_cons_succ, List.getElem_ofFn, back]
      congr 1; push_cast; ring

theorem honestHist_last (d : Fin n → Fin n) (i : Fin n) : (honestHist d i)[n - 1]? = some (d i) := by
  have hn := NeZero.pos n
  rw [List.getElem?_eq_getElem (by simp [honestHist]; omega)]
  simp only [honestHist, List.getElem_ofFn, back, Option.some.injEq]
  congr 1
  rw [sub_eq_self]
  ext
  simp [Nat.sub_add_cancel hn]

theorem honestHist_sum (d : Fin n → Fin n) (i : Fin n) : (honestHist d i).sum = ∑ j, d j := by
  rw [honestHist, List.sum_ofFn]
  have hinj : Function.Injective fun t : Fin n => back i t := by
    intro a b hab
    simp only [back, sub_right_inj] at hab
    have : ((a : ℕ) : Fin n) = ((b : ℕ) : Fin n) := by
      have := congrArg (· - 1) hab; push_cast at this; simpa using this
    simpa [Fin.cast_val_eq_self] using this
  exact Function.Bijective.sum_comp (Finite.injective_iff_bijective.mp hinj) d

/-- The honest execution of `A-LEADuni` terminates and every processor outputs `∑ i, d i`. -/
theorem outcome_aLead (d : Fin n → Fin n) : outcome (aLead d) = some (∑ j, d j) := by
  let X := honestHist d
  have hX : ∀ i, X i <+: inbox (aLead d) X i := by
    intro i
    show honestHist d i <+: _
    rw [inbox, aLead_sent_full d _ (honestHist_length d _), honestHist_succ d i]
  have hXo : ∀ i p x, p ++ [x] <+: X i → (aLead d i).out p = none := by
    intro i p x hp
    rw [aLead_out]
    apply validate_eq_none
    have := hp.length_le; simp [X, honestHist_length] at this; omega
  obtain ⟨c, hc, hcX, hst⟩ := exists_reach_le_of_consistent X hX hXo
  have hinv := hc.inv
  have hle : ∀ i, (c i).length ≤ n := fun i =>
    length_le_of_inv_validate (by simpa [aLead_out] using (hinv i).2)
  -- counting: the lengths do not decrease along the ring, hence are constant, hence full
  have hmono : ∀ i, (c (i - 1)).length ≤ (c i).length := by
    intro i
    rcases hst i with h | h
    · rw [h, honestHist_length]; exact hle _
    · have := (aLead_sent_length d (i - 1) (c (i - 1))).1
      have := hle (i - 1)
      simp only [inbox] at h; omega
  have hconst := ring_const (fun i => (c i).length) hmono
  have hfull : ∀ i, c i = X i := by
    intro i
    have h1 : (c 1).length = n := by
      rcases hst 1 with h | h
      · rw [h, honestHist_length]
      · have := (aLead_sent_length d (1 - 1) (c (1 - 1))).2.2 (by simp)
        have := hle 1
        simp only [inbox] at h
        have h0 := hconst 1 (1 - 1)
        omega
    exact (hcX i).eq_of_length (by
      have := hconst i 1; have := honestHist_length d i; simp only [X] at *; omega)
  have hcX' : c = X := funext hfull
  subst hcX'
  rw [outcome_eq_some]
  intro i
  refine ⟨_, hc, ?_⟩
  rw [aLead_out, validate, if_pos (honestHist_length d i), if_pos (honestHist_last d i),
    honestHist_sum]

/-- The number of secret vectors with a given sum does not depend on the sum. -/
theorem card_sum_eq (j : Fin n) :
    (Finset.univ.filter fun d : Fin n → Fin n => ∑ i, d i = j).card = n ^ n / n := by
  classical
  have hshift : ∀ j j' : Fin n, (Finset.univ.filter fun d : Fin n → Fin n => ∑ i, d i = j).card =
      (Finset.univ.filter fun d : Fin n → Fin n => ∑ i, d i = j').card := by
    intro j j'
    apply Finset.card_bij (fun d _ => d + Pi.single 0 (j' - j))
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
      simp [Finset.sum_add_distrib, hd]
    · intro a _ b _ h; simpa using h
    · intro d hd
      refine ⟨d - Pi.single 0 (j' - j), ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
      simp [Finset.sum_sub_distrib, hd]
  have htot : ∑ j : Fin n, (Finset.univ.filter fun d : Fin n → Fin n => ∑ i, d i = j).card =
      n ^ n := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
      (f := fun d : Fin n → Fin n => ∑ i, d i) (fun _ _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at this
    rw [this]
  rw [Finset.sum_congr rfl (fun j' _ => hshift j' j)] at htot
  simp at htot
  rw [← htot, Nat.mul_div_cancel_left _ (NeZero.pos n)]

/-- `A-LEADuni` is a fair leader election protocol. -/
theorem isFLE_aLead : IsFLE (n := n) aLead := by
  classical
  intro σ hσ j
  unfold prob
  simp only [outcomeUnder_eq _ hσ, outcome_aLead, Option.some.injEq]
  rw [card_sum_eq, Fintype.card_fun, Fintype.card_fin]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.pos n; omega⟩
  rw [pow_succ, Nat.mul_div_cancel _ (by omega)]
  push_cast
  field_simp

end Podc.FairLeaderElection
