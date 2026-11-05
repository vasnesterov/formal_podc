import Papers.PODC2014.DistributedUniversality.Basic

/-!
# Non-vacuity: the base objects are wait-free, every process can always move

The specifications `acOK` (adopt-commit) and `scOK` (`(k, ℓ)`-simultaneous consensus) of the model
are constraints on the responses chosen by the adversary.  We show that they never block a process:
in every reachable state every process has an enabled action (`enabled`), provided `1 ≤ ℓ ≤ k`.
Consequently there is an infinite execution in which all processes are correct (`exists_exec`).

The proof is by an inductive invariant `Inv`, which also carries the facts used for Lemma 5
(`Lemma5.lean`): agreement/validity of the base objects, the ghost `firstL`, and the program-counter
structure of a round.
-/

namespace Podc.DistributedUniversality.NonVacuity

open Podc.DistributedUniversality

variable {n k : ℕ}

/-! ### One adopt-commit object -/

/-- Invariant of one adopt-commit object (invocations `inv`, responses `resp`, ghost `free`). -/
structure ACInv (strong : Bool) (inv : Fin n → Option (Op n))
    (resp : Fin n → Option (Bool × Op n)) (free : Option (Op n)) : Prop where
  valid : ∀ q t w, resp q = some (t, w) → ∃ q', inv q' = some w
  freeValid : ∀ w, free = some w → ∃ q', inv q' = some w
  agree : ∀ q q' w t' w', resp q = some (true, w) → resp q' = some (t', w') → w' = w
  strongFree : strong = true → ∀ w, free = some w → ∀ q t' w', resp q = some (t', w') → w' = w

theorem acInv_empty (strong : Bool) :
    ACInv strong (fun _ : Fin n => none) (fun _ => none) none :=
  ⟨by simp, by simp, by simp, by simp⟩

theorem acInv_invoke {strong : Bool} {inv : Fin n → Option (Op n)}
    {resp : Fin n → Option (Bool × Op n)} {free : Option (Op n)} {i : Fin n}
    (h : ACInv strong inv resp free) (hi : inv i = none) (w : Op n) :
    ACInv strong (Function.update inv i (some w)) resp free := by
  have key : ∀ q' u, inv q' = some u → Function.update inv i (some w) q' = some u := by
    intro q' u hq'
    have : q' ≠ i := by rintro rfl; simp [hi] at hq'
    simp [Function.update_of_ne this, hq']
  refine ⟨?_, ?_, h.agree, h.strongFree⟩
  · intro q t w' hq
    obtain ⟨q', hq'⟩ := h.valid q t w' hq
    exact ⟨q', key _ _ hq'⟩
  · intro w' hw
    obtain ⟨q', hq'⟩ := h.freeValid w' hw
    exact ⟨q', key _ _ hq'⟩

theorem acInv_respond {strong : Bool} {inv : Fin n → Option (Op n)}
    {resp : Fin n → Option (Bool × Op n)} {free : Option (Op n)} {i : Fin n} {own : Op n}
    {t : Bool} {v : Op n}
    (h : ACInv strong inv resp free) (hi : inv i = some own)
    (hok : acOK strong inv resp free i own t v) :
    ACInv strong inv (Function.update resp i (some (t, v))) (freeUpd inv free i own) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hok
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q t' w hq
    by_cases hqi : q = i
    · subst hqi; simp at hq; obtain ⟨rfl, rfl⟩ := hq; exact h1
    · rw [Function.update_of_ne hqi] at hq; exact h.valid q t' w hq
  · intro w hw
    unfold freeUpd at hw
    split at hw
    · exact h.freeValid w (by simpa using hw)
    · split at hw
      · simp at hw; subst hw; exact ⟨i, hi⟩
      · simp at hw
  · intro q q' w t' w' hq hq'
    by_cases hqi : q = i
    · subst hqi
      simp at hq; obtain ⟨rfl, rfl⟩ := hq
      by_cases hq'i : q' = q
      · subst hq'i; simp at hq'; exact hq'.2.symm
      · rw [Function.update_of_ne hq'i] at hq'
        exact h3 rfl q' _ hq'
    · rw [Function.update_of_ne hqi] at hq
      by_cases hq'i : q' = i
      · subst hq'i; simp at hq'; obtain ⟨-, rfl⟩ := hq'
        exact (h2 q _ hq rfl).symm
      · rw [Function.update_of_ne hq'i] at hq'
        exact h.agree q q' w t' w' hq hq'
  · intro hs w hw q t' w' hq
    unfold freeUpd at hw
    split at hw
    · rename_i _ w₀
      obtain rfl : w₀ = w := by simpa using hw
      by_cases hqi : q = i
      · subst hqi; simp at hq; obtain ⟨-, rfl⟩ := hq
        exact (h5 hs _ rfl).2
      · rw [Function.update_of_ne hqi] at hq
        exact h.strongFree hs _ rfl q t' w' hq
    · split at hw
      · rename_i hP
        simp at hw; subst hw
        by_cases hqi : q = i
        · subst hqi; simp at hq; obtain ⟨-, rfl⟩ := hq
          exact (h4 hP).2
        · rw [Function.update_of_ne hqi] at hq
          obtain ⟨q', hq'⟩ := h.valid q t' w' hq
          by_cases hq'i : q' = i
          · subst hq'i; rw [hi] at hq'; exact (Option.some.inj hq').symm
          · exact hP q' hq'i w' hq'
      · simp at hw

/-- The adopt-commit specification never blocks a process that has invoked the object. -/
theorem acOK_exists {strong : Bool} {inv : Fin n → Option (Op n)}
    {resp : Fin n → Option (Bool × Op n)} {free : Option (Op n)} {i : Fin n} {own : Op n}
    (h : ACInv strong inv resp free) (hi : inv i = some own) :
    ∃ t v, acOK strong inv resp free i own t v := by
  by_cases hP : ∀ q, q ≠ i → ∀ w ∈ inv q, w = own
  · -- no conflict: commit the own value
    have hall : ∀ q t' w', resp q = some (t', w') → w' = own := by
      intro q t' w' hq
      obtain ⟨q', hq'⟩ := h.valid q t' w' hq
      by_cases hq'i : q' = i
      · subst hq'i; rw [hi] at hq'; exact (Option.some.inj hq').symm
      · exact hP q' hq'i w' hq'
    refine ⟨true, own, ⟨i, hi⟩, ?_, ?_, fun _ => ⟨rfl, rfl⟩, ?_⟩
    · rintro q ⟨b, w⟩ hq -; exact hall q b w hq
    · rintro - q ⟨b, w⟩ hq; exact hall q b w hq
    · intro hs w hw
      obtain ⟨q', hq'⟩ := h.freeValid w hw
      refine ⟨rfl, ?_⟩
      by_cases hq'i : q' = i
      · subst hq'i; rw [hi] at hq'; exact Option.some.inj hq'
      · exact (hP q' hq'i w hq').symm
  · by_cases hF : ∃ w, strong = true ∧ free = some w
    · obtain ⟨w, hs, hw⟩ := hF
      refine ⟨true, w, h.freeValid w hw, ?_, ?_, fun h' => absurd h' hP, ?_⟩
      · rintro q ⟨b, w'⟩ hq -; exact h.strongFree hs w hw q b w' hq
      · rintro - q ⟨b, w'⟩ hq; exact h.strongFree hs w hw q b w' hq
      · intro _ w' hw'; rw [hw] at hw'; exact ⟨rfl, Option.some.inj hw'⟩
    · have hF' : strong = true → free = none := by
        intro hs; cases hfr : free with
        | none => rfl
        | some w => exact absurd ⟨w, hs, hfr⟩ hF
      by_cases hC : ∃ q w, resp q = some (true, w)
      · obtain ⟨q, w, hq⟩ := hC
        refine ⟨false, w, h.valid q true w hq, ?_, by simp, fun h' => absurd h' hP, ?_⟩
        · rintro q' ⟨b, w'⟩ hq' (hb : b = true); subst hb
          exact (h.agree q' q w' true w hq' hq).symm
        · intro hs w' hw'; rw [hF' hs] at hw'; simp at hw'
      · refine ⟨false, own, ⟨i, hi⟩, ?_, by simp, fun h' => absurd h' hP, ?_⟩
        · rintro q' ⟨b, w'⟩ hq' (hb : b = true); subst hb
          exact absurd ⟨q', w', hq'⟩ hC
        · intro hs w' hw'; rw [hF' hs] at hw'; simp at hw'

/-! ### One `(k, ℓ)`-simultaneous consensus object -/

/-- Invariant of one `(k, ℓ)`-SC object. -/
structure SCInv (ℓ : ℕ) (inv : Fin n → Option (Fin k → Op n))
    (resp : Fin n → Option (Fin k → Option (Op n))) : Prop where
  card : ∀ q e, resp q = some e → (Finset.univ.filter (fun x => (e x).isSome)).card = ℓ
  valid : ∀ q e x v, resp q = some e → e x = some v → ∃ q' u, inv q' = some u ∧ u x = v
  agree : ∀ q q' e e' x v w, resp q = some e → resp q' = some e' → e x = some v →
    e' x = some w → v = w

theorem scInv_empty (ℓ : ℕ) :
    SCInv (n := n) (k := k) ℓ (fun _ => none) (fun _ => none) :=
  ⟨by simp, by simp, by simp⟩

theorem scInv_invoke {ℓ : ℕ} {inv : Fin n → Option (Fin k → Op n)}
    {resp : Fin n → Option (Fin k → Option (Op n))} {i : Fin n}
    (h : SCInv ℓ inv resp) (hi : inv i = none) (u : Fin k → Op n) :
    SCInv ℓ (Function.update inv i (some u)) resp := by
  refine ⟨h.card, ?_, h.agree⟩
  intro q e x v hq hx
  obtain ⟨q', u', hq', hu'⟩ := h.valid q e x v hq hx
  have : q' ≠ i := by rintro rfl; simp [hi] at hq'
  exact ⟨q', u', by simp [Function.update_of_ne this, hq'], hu'⟩

theorem scInv_respond {ℓ : ℕ} {inv : Fin n → Option (Fin k → Op n)}
    {resp : Fin n → Option (Fin k → Option (Op n))} {i : Fin n} {d : Fin k → Option (Op n)}
    (h : SCInv ℓ inv resp) (hok : scOK ℓ inv resp d) :
    SCInv ℓ inv (Function.update resp i (some d)) := by
  obtain ⟨h1, h2, h3⟩ := hok
  refine ⟨?_, ?_, ?_⟩
  · intro q e hq
    by_cases hqi : q = i
    · subst hqi; simp at hq; subst hq; exact h1
    · rw [Function.update_of_ne hqi] at hq; exact h.card q e hq
  · intro q e x v hq hx
    by_cases hqi : q = i
    · subst hqi; simp at hq; subst hq
      obtain ⟨q', u, hu, hux⟩ := h2 x v hx
      exact ⟨q', u, hu, hux⟩
    · rw [Function.update_of_ne hqi] at hq; exact h.valid q e x v hq hx
  · intro q q' e e' x v w hq hq' hx hx'
    by_cases hqi : q = i
    · subst hqi; simp at hq; subst hq
      by_cases hq'i : q' = q
      · subst hq'i; simp at hq'; subst hq'; rw [hx] at hx'; exact Option.some.inj hx'
      · rw [Function.update_of_ne hq'i] at hq'
        exact (h3 q' x e' hq' v hx w hx').symm
    · rw [Function.update_of_ne hqi] at hq
      by_cases hq'i : q' = i
      · subst hq'i; simp at hq'; subst hq'
        exact h3 q x e hq w hx' v hx
      · rw [Function.update_of_ne hq'i] at hq'
        exact h.agree q q' e e' x v w hq hq' hx hx'

theorem card_filter_val_lt {ℓ : ℕ} (h : ℓ ≤ k) :
    (Finset.univ.filter (fun x : Fin k => x.val < ℓ)).card = ℓ := by
  have : (Finset.univ.filter (fun x : Fin k => x.val < ℓ)) =
      (Finset.range ℓ).attachFin (fun m hm => by simp at hm; omega) := by
    ext x; simp
  rw [this, Finset.card_attachFin, Finset.card_range]

/-- The `(k, ℓ)`-SC specification never blocks a process that has invoked the object. -/
theorem scOK_exists {ℓ : ℕ} {inv : Fin n → Option (Fin k → Op n)}
    {resp : Fin n → Option (Fin k → Option (Op n))} {i : Fin n} {u : Fin k → Op n}
    (h : SCInv ℓ inv resp) (hi : inv i = some u) (hℓ : ℓ ≤ k) :
    ∃ d, scOK ℓ inv resp d := by
  by_cases hR : ∃ q e, resp q = some e
  · obtain ⟨q, e, hq⟩ := hR
    refine ⟨e, h.card q e hq, ?_, ?_⟩
    · intro x v hv
      obtain ⟨q', u', hu', hux⟩ := h.valid q e x v hq hv
      exact ⟨q', u', hu', hux⟩
    · intro q' x e' hq' v hv w hw
      exact h.agree q' q e' e x w v hq' hq hw hv
  · refine ⟨fun x => if x.val < ℓ then some (u x) else none, ?_, ?_, ?_⟩
    · convert card_filter_val_lt (k := k) hℓ using 2
      ext x; by_cases hx : x.val < ℓ <;> simp [hx]
    · intro x v hv
      dsimp only at hv
      split at hv
      · exact ⟨i, u, hi, Option.some.inj hv⟩
      · simp at hv
    · intro q x e he
      exact absurd ⟨q, e, he⟩ hR

/-! ### The order of lines 3M/4M -/

theorem ordOf_length (d : Fin k → Option (Op n)) : (ordOf d).length = k := by
  unfold ordOf
  have := List.length_eq_length_filter_add (l := List.finRange k) (fun x => (d x).isSome)
  simp only [List.length_finRange] at this
  rw [List.length_append]
  conv_rhs => rw [this]
  congr 3
  funext x; cases d x <;> rfl

theorem ordOf_nodup (d : Fin k → Option (Op n)) : (ordOf d).Nodup := by
  unfold ordOf
  refine List.Nodup.append ((List.nodup_finRange k).filter _)
    ((List.nodup_finRange k).filter _) ?_
  intro x hx hy
  simp [List.mem_filter] at hx hy
  simp_all

/-- The entries of `ordOf d`: first the decided objects, then the others. -/
theorem ordOf_get {d : Fin k → Option (Op n)} {j : ℕ} {x : Fin k}
    (hx : (ordOf d)[j]? = some x) :
    (j < (Finset.univ.filter (fun x => (d x).isSome)).card ∧ (d x).isSome) ∨
      ((Finset.univ.filter (fun x => (d x).isSome)).card ≤ j ∧ d x = none) := by
  have hl : ((List.finRange k).filter (fun x => (d x).isSome)).length =
      (Finset.univ.filter (fun x => (d x).isSome)).card := rfl
  unfold ordOf at hx
  rw [← hl]
  by_cases hj : j < ((List.finRange k).filter (fun x => (d x).isSome)).length
  · left
    rw [List.getElem?_append_left hj] at hx
    have := List.mem_of_getElem? hx
    simp [List.mem_filter] at this
    exact ⟨hj, this⟩
  · right
    rw [List.getElem?_append_right (by omega)] at hx
    have := List.mem_of_getElem? hx
    simp [List.mem_filter] at this
    exact ⟨by omega, this⟩

theorem ordOf_decided {d : Fin k → Option (Op n)} {x : Fin k} (hx : (d x).isSome) :
    ∃ j, j < (Finset.univ.filter (fun x => (d x).isSome)).card ∧ (ordOf d)[j]? = some x := by
  have hl : ((List.finRange k).filter (fun x => (d x).isSome)).length =
      (Finset.univ.filter (fun x => (d x).isSome)).card := rfl
  have hm : x ∈ (List.finRange k).filter (fun x => (d x).isSome) := by simp [hx]
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  have hjl : j < ((List.finRange k).filter (fun x => (d x).isSome)).length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hj; simp at hj
  refine ⟨j, hl ▸ hjl, ?_⟩
  unfold ordOf; rw [List.getElem?_append_left hjl, hj]

theorem getElem?_inj_of_nodup {l : List (Fin k)} (hl : l.Nodup) {j j' : ℕ} {x : Fin k}
    (h : l[j]? = some x) (h' : l[j']? = some x) : j = j' := by
  rw [List.getElem?_eq_some_iff] at h h'
  obtain ⟨hj, rfl⟩ := h
  obtain ⟨hj', h'⟩ := h'
  exact (hl.getElem_inj_iff).mp h'.symm

/-! ### The invariant -/

/-- Process `i` is done with the adopt-commit part of round `r`: it skipped lines 2M–4M, or some
process has finished its adopt-commit invocations on its decided objects (`firstL r` is set). -/
def Past (M : Mode) (s : St n k) (i : Fin n) (r : ℕ) : Prop :=
  skipped M s r i ∨ s.firstL r ≠ none

/-- Program counters after the `ℓ` adopt-commit invocations on the decided objects. -/
def PastL (ℓ : ℕ) : PC → Prop
  | .acInv j => ℓ ≤ j
  | .acResp j => ℓ ≤ j
  | .collect _ => True
  | .loc => True
  | .upd _ => True
  | .write => True
  | _ => False

/-- No adopt-commit object of lines 3–4 of the current round has been invoked by `i`. -/
def NoTrue (s : St n k) (i : Fin n) : Prop := ∀ x, s.acI (s.loc i).r true x i = none

/-- The responses of the first `m` objects of line N1 are stored in `tagᵢ`, `ac_opᵢ`. -/
def N1Tags (s : St n k) (i : Fin n) (m : ℕ) : Prop :=
  ∀ x : Fin k, x.val < m →
    s.acR (s.loc i).r false x i = some ((s.loc i).tag x, (s.loc i).acop x)

/-- While `firstL` is unset, all the adopt-commit invocations of `i` on decided objects
(the first `j` ones) returned commit with the decided value. -/
def Commits (s : St n k) (i : Fin n) (j : ℕ) : Prop :=
  s.firstL (s.loc i).r = none → ∀ j' x v, j' < j → (s.loc i).ord[j']? = some x →
    (s.loc i).scd x = some v → s.acR (s.loc i).r true x i = some (true, v)

/-- The invariant of a process, by program counter (current round `(s.loc i).r`). -/
def PCInv (M : Mode) (s : St n k) (i : Fin n) : PC → Prop
  | .init => (s.loc i).r = 0
  | .n1Inv m => M.ca = true ∧ m < k ∧ 1 ≤ (s.loc i).r ∧
      (∀ x : Fin k, m ≤ x.val → s.acI (s.loc i).r false x i = none) ∧ NoTrue s i ∧
      s.scI (s.loc i).r i = none ∧ N1Tags s i m
  | .n1Resp m => M.ca = true ∧
      (∃ hm : m < k, s.acI (s.loc i).r false ⟨m, hm⟩ i = some ((s.loc i).oper ⟨m, hm⟩)) ∧
      1 ≤ (s.loc i).r ∧
      (∀ x : Fin k, m < x.val → s.acI (s.loc i).r false x i = none) ∧ NoTrue s i ∧
      s.scI (s.loc i).r i = none ∧ N1Tags s i m
  | .scInv => 1 ≤ (s.loc i).r ∧ NoTrue s i ∧ s.scI (s.loc i).r i = none
  | .scResp => 1 ≤ (s.loc i).r ∧ NoTrue s i ∧ (s.scI (s.loc i).r i).isSome
  | .acInv j => 1 ≤ (s.loc i).r ∧ j < k ∧ s.scR (s.loc i).r i = some (s.loc i).scd ∧
      (s.loc i).ord = ordOf (s.loc i).scd ∧
      (∀ j' x, j ≤ j' → (s.loc i).ord[j']? = some x → s.acI (s.loc i).r true x i = none) ∧
      (M.ℓ ≤ j → s.firstL (s.loc i).r ≠ none) ∧ Commits s i j
  | .acResp j => 1 ≤ (s.loc i).r ∧ s.scR (s.loc i).r i = some (s.loc i).scd ∧
      (s.loc i).ord = ordOf (s.loc i).scd ∧
      (∃ x, (s.loc i).ord[j]? = some x ∧
        s.acI (s.loc i).r true x i = some (acVal M (s.loc i) x)) ∧
      (∀ j' x, j < j' → (s.loc i).ord[j']? = some x → s.acI (s.loc i).r true x i = none) ∧
      (M.ℓ ≤ j → s.firstL (s.loc i).r ≠ none) ∧ Commits s i j
  | .collect q => q < n ∧ 1 ≤ (s.loc i).r ∧ Past M s i (s.loc i).r
  | .loc => 1 ≤ (s.loc i).r ∧ Past M s i (s.loc i).r
  | .upd m => m < k ∧ 1 ≤ (s.loc i).r ∧ Past M s i (s.loc i).r
  | .write => 1 ≤ (s.loc i).r ∧ Past M s i (s.loc i).r

/-- The invariant of one process. -/
structure PInv (M : Mode) (s : St n k) (i : Fin n) : Prop where
  fut : ∀ r, (s.loc i).r < r → (∀ b x, s.acI r b x i = none) ∧ s.scI r i = none
  past : ∀ r, 1 ≤ r → r < (s.loc i).r → Past M s i r
  first : ∀ r, s.firstL r = some i →
    r < (s.loc i).r ∨ (r = (s.loc i).r ∧ PastL M.ℓ (s.loc i).pc)
  pc : PCInv M s i (s.loc i).pc

/-- The global inductive invariant. -/
structure Inv (M : Mode) (s : St n k) : Prop where
  ac : ∀ r b x, ACInv M.strongAC (s.acI r b x) (s.acR r b x) (s.acFree r b x)
  sc : ∀ r, SCInv M.ℓ (s.scI r) (s.scR r)
  /-- the first process to finish its decided block got commit on all its decided objects -/
  l1 : ∀ r q, s.firstL r = some q → ∃ d, s.scR r q = some d ∧
    ∀ x v, d x = some v → s.acR r true x q = some (true, v)
  /-- before that, every invocation of lines 3–4 is on a decided object, with the decided value -/
  l2 : ∀ r, s.firstL r = none → ∀ q x w, s.acI r true x q = some w →
    ∃ d, s.scR r q = some d ∧ d x = some w
  proc : ∀ i, PInv M s i

theorem inv_init (M : Mode) : Inv M (init : St n k) where
  ac _ _ _ := acInv_empty _
  sc _ := scInv_empty _
  l1 := by simp [init]
  l2 := by simp [init]
  proc i := ⟨by simp [init], by simp [init, initLoc], by simp [init], by
    simp [init, initLoc, PCInv]⟩

theorem pInv_frame {M : Mode} {s s' : St n k} {i : Fin n} (h : PInv M s i)
    (hloc : s'.loc i = s.loc i)
    (hacI : ∀ r b x, s'.acI r b x i = s.acI r b x i)
    (hacR : ∀ r b x, s'.acR r b x i = s.acR r b x i)
    (hscI : ∀ r, s'.scI r i = s.scI r i) (hscR : ∀ r, s'.scR r i = s.scR r i)
    (hfirst : ∀ r, s'.firstL r = s.firstL r ∨
      (s.firstL r = none ∧ ∃ q, q ≠ i ∧ s'.firstL r = some q)) :
    PInv M s' i := by
  have hsk : ∀ r, skipped M s' r i ↔ skipped M s r i := by
    intro r; simp only [skipped, hacR]
  have hne : ∀ r, s.firstL r ≠ none → s'.firstL r ≠ none := by
    intro r hr; rcases hfirst r with h' | ⟨h', -⟩
    · rwa [h']
    · exact absurd h' hr
  have hnone : ∀ r, s'.firstL r = none → s.firstL r = none := by
    intro r hr; rcases hfirst r with h' | ⟨h', -⟩
    · rwa [← h']
    · exact h'
  have hsome : ∀ r, s'.firstL r = some i → s.firstL r = some i := by
    intro r hr; rcases hfirst r with h' | ⟨-, q, hq, h'⟩
    · rwa [← h']
    · rw [hr] at h'; exact absurd (Option.some.inj h').symm hq
  have hpast : ∀ r, Past M s i r → Past M s' i r := by
    intro r hr; rcases hr with hr | hr
    · exact Or.inl ((hsk r).2 hr)
    · exact Or.inr (hne r hr)
  obtain ⟨hfut, hpst, hfst, hpc⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr; simp only [hloc, hacI, hscI] at hr ⊢; exact hfut r hr
  · intro r h1 hr; rw [hloc] at hr; exact hpast r (hpst r h1 hr)
  · intro r hr; rw [hloc]; exact hfst r (hsome r hr)
  · rw [hloc]
    revert hpc
    cases (s.loc i).pc <;>
      simp only [PCInv, NoTrue, N1Tags, Commits, hloc, hacI, hacR, hscI, hscR] <;> first
      | exact id
      | exact fun h => ⟨h.1, h.2.1, hpast _ h.2.2⟩
      | exact fun h => ⟨h.1, hpast _ h.2⟩
      | exact fun ⟨h1, h2, h3, h4, h5, h6, h7⟩ =>
          ⟨h1, h2, h3, h4, h5, fun hj => hne _ (h6 hj), fun hn => h7 (hnone _ hn)⟩

/-! ### Updates of whole families of base objects -/

theorem ac_invoke_all {strong : Bool} {I : ℕ → Bool → Fin k → Fin n → Option (Op n)}
    {R : ℕ → Bool → Fin k → Fin n → Option (Bool × Op n)} {F : ℕ → Bool → Fin k → Option (Op n)}
    (h : ∀ r b x, ACInv strong (I r b x) (R r b x) (F r b x)) {r₀ : ℕ} {b₀ : Bool} {x₀ : Fin k}
    {i : Fin n} (hnone : I r₀ b₀ x₀ i = none) (w : Op n) :
    ∀ r b x, ACInv strong
      ((fun r b y j => if r = r₀ ∧ b = b₀ ∧ y = x₀ ∧ j = i then some w else I r b y j) r b x)
      (R r b x) (F r b x) := by
  intro r b x
  by_cases hr : r = r₀ ∧ b = b₀ ∧ x = x₀
  · obtain ⟨rfl, rfl, rfl⟩ := hr
    convert acInv_invoke (h r b x) hnone w using 1
    funext j; by_cases hj : j = i <;> simp [hj]
  · convert h r b x using 1
    funext j; simp only [ite_eq_right_iff]; intro h'; exact absurd ⟨h'.1, h'.2.1, h'.2.2.1⟩ hr

theorem ac_respond_all {strong : Bool} {I : ℕ → Bool → Fin k → Fin n → Option (Op n)}
    {R : ℕ → Bool → Fin k → Fin n → Option (Bool × Op n)} {F : ℕ → Bool → Fin k → Option (Op n)}
    (h : ∀ r b x, ACInv strong (I r b x) (R r b x) (F r b x)) {r₀ : ℕ} {b₀ : Bool} {x₀ : Fin k}
    {i : Fin n} {own : Op n} {t : Bool} {v : Op n} (hi : I r₀ b₀ x₀ i = some own)
    (hok : acOK strong (I r₀ b₀ x₀) (R r₀ b₀ x₀) (F r₀ b₀ x₀) i own t v) :
    ∀ r b x, ACInv strong (I r b x)
      ((fun r b y j => if r = r₀ ∧ b = b₀ ∧ y = x₀ ∧ j = i then some (t, v) else R r b y j) r b x)
      ((fun r b y => if r = r₀ ∧ b = b₀ ∧ y = x₀ then freeUpd (I r₀ b₀ x₀) (F r₀ b₀ x₀) i own
        else F r b y) r b x) := by
  intro r b x
  by_cases hr : r = r₀ ∧ b = b₀ ∧ x = x₀
  · obtain ⟨rfl, rfl, rfl⟩ := hr
    convert acInv_respond (h r b x) hi hok using 1
    · funext j; by_cases hj : j = i <;> simp [hj]
    · simp
  · convert h r b x using 1
    · funext j; simp only [ite_eq_right_iff]; intro h'
      exact absurd ⟨h'.1, h'.2.1, h'.2.2.1⟩ hr
    · simp only [ite_eq_right_iff]; intro h'; exact absurd h' hr

theorem sc_invoke_all {ℓ : ℕ} {I : ℕ → Fin n → Option (Fin k → Op n)}
    {R : ℕ → Fin n → Option (Fin k → Option (Op n))} (h : ∀ r, SCInv ℓ (I r) (R r)) {r₀ : ℕ}
    {i : Fin n} (hnone : I r₀ i = none) (u : Fin k → Op n) :
    ∀ r, SCInv ℓ ((fun r j => if r = r₀ ∧ j = i then some u else I r j) r) (R r) := by
  intro r
  by_cases hr : r = r₀
  · subst hr
    convert scInv_invoke (h r) hnone u using 1
    funext j; by_cases hj : j = i <;> simp [hj]
  · convert h r using 1
    funext j; simp [hr]

theorem sc_respond_all {ℓ : ℕ} {I : ℕ → Fin n → Option (Fin k → Op n)}
    {R : ℕ → Fin n → Option (Fin k → Option (Op n))} (h : ∀ r, SCInv ℓ (I r) (R r)) {r₀ : ℕ}
    {i : Fin n} {d : Fin k → Option (Op n)} (hok : scOK ℓ (I r₀) (R r₀) d) :
    ∀ r, SCInv ℓ (I r) ((fun r j => if r = r₀ ∧ j = i then some d else R r j) r) := by
  intro r
  by_cases hr : r = r₀
  · subst hr
    convert scInv_respond (i := i) (h r) hok using 1
    funext j; by_cases hj : j = i <;> simp [hj]
  · convert h r using 1
    funext j; simp [hr]

/-- The invariant of the processes other than the one taking the step. -/
theorem pInv_others {M : Mode} {s s' : St n k} {i : Fin n} (hI : Inv M s)
    (hloc : ∀ j, j ≠ i → s'.loc j = s.loc j)
    (hacI : ∀ r b x j, j ≠ i → s'.acI r b x j = s.acI r b x j)
    (hacR : ∀ r b x j, j ≠ i → s'.acR r b x j = s.acR r b x j)
    (hscI : ∀ r j, j ≠ i → s'.scI r j = s.scI r j)
    (hscR : ∀ r j, j ≠ i → s'.scR r j = s.scR r j)
    (hfirst : ∀ r, s'.firstL r = s.firstL r ∨ (s.firstL r = none ∧ s'.firstL r = some i)) :
    ∀ j, j ≠ i → PInv M s' j := by
  intro j hj
  refine pInv_frame (hI.proc j) (hloc j hj) (fun r b x => hacI r b x j hj)
    (fun r b x => hacR r b x j hj) (fun r => hscI r j hj) (fun r => hscR r j hj) ?_
  intro r
  rcases hfirst r with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, i, Ne.symm hj, h2⟩

/-- Steps that do not touch the base objects nor `firstL`. -/
theorem inv_local {M : Mode} {s s' : St n k} {i : Fin n} (hI : Inv M s)
    (hacI : s'.acI = s.acI) (hacR : s'.acR = s.acR) (hacF : s'.acFree = s.acFree)
    (hscI : s'.scI = s.scI) (hscR : s'.scR = s.scR) (hfirst : s'.firstL = s.firstL)
    (hloc : ∀ j, j ≠ i → s'.loc j = s.loc j) (hi : PInv M s' i) : Inv M s' where
  ac := by rw [hacI, hacR, hacF]; exact hI.ac
  sc := by rw [hscI, hscR]; exact hI.sc
  l1 := by rw [hfirst, hscR, hacR]; exact hI.l1
  l2 := by rw [hfirst, hscR, hacI]; exact hI.l2
  proc j := by
    by_cases hj : j = i
    · subst hj; exact hi
    · exact pInv_others hI hloc (by simp [hacI]) (by simp [hacR]) (by simp [hscI])
        (by simp [hscR]) (by simp [hfirst]) j hj

/-- A step of a process that stays in its round, without touching the base objects. -/
theorem pInv_sameRound {M : Mode} {s s' : St n k} {i : Fin n} (h : PInv M s i)
    (hacI : s'.acI = s.acI) (hacR : s'.acR = s.acR) (hscI : s'.scI = s.scI)
    (hfirst : s'.firstL = s.firstL) (hr : (s'.loc i).r = (s.loc i).r)
    (hL : PastL M.ℓ (s.loc i).pc → PastL M.ℓ (s'.loc i).pc)
    (hpc : PCInv M s' i (s'.loc i).pc) : PInv M s' i := by
  have hpast : ∀ r, Past M s' i r ↔ Past M s i r := by
    intro r; simp only [Past, skipped, hacR, hfirst]
  refine ⟨?_, ?_, ?_, hpc⟩
  · intro r h'; rw [hacI, hscI]; rw [hr] at h'; exact h.fut r h'
  · intro r h1 h'; rw [hr] at h'; exact (hpast r).2 (h.past r h1 h')
  · intro r h'; rw [hfirst] at h'; rw [hr]
    rcases h.first r h' with h'' | ⟨h1, h2⟩
    · exact Or.inl h''
    · exact Or.inr ⟨h1, hL h2⟩

/-! ### The local steps -/

section Local
variable {M : Mode} {s : St n k} {i : Fin n}

theorem inv_collect (hI : Inv M s) {q : ℕ} (hq : q < n) (hpc : (s.loc i).pc = .collect q) :
    Inv M (tCollect s i q ⟨q, hq⟩) := by
  have h := hI.proc i
  have hp := h.pc; rw [hpc] at hp; obtain ⟨-, h1, h2⟩ := hp
  refine inv_local (i := i) hI rfl rfl rfl rfl rfl rfl
    (fun j (hj : j ≠ i) => by simp [tCollect, Function.update_of_ne hj]) ?_
  refine pInv_sameRound h rfl rfl rfl rfl (by simp [tCollect]) ?_ ?_
  · intro _; simp only [tCollect, Function.update_self]; split <;> trivial
  · simp only [tCollect, Function.update_self]
    split
    · exact ⟨by assumption, by simpa using h1, by simpa [Past, skipped] using h2⟩
    · exact ⟨by simpa using h1, by simpa [Past, skipped] using h2⟩

theorem inv_loc (hI : Inv M s) (hpc : (s.loc i).pc = .loc) : Inv M (tLoc s i) := by
  have h := hI.proc i
  have hp := h.pc; rw [hpc] at hp; obtain ⟨h1, h2⟩ := hp
  refine inv_local (i := i) hI rfl rfl rfl rfl rfl rfl
    (fun j (hj : j ≠ i) => by simp [tLoc, Function.update_of_ne hj]) ?_
  refine pInv_sameRound h rfl rfl rfl rfl (by simp [tLoc]) ?_ ?_
  · intro _; simp only [tLoc, Function.update_self]; split <;> trivial
  · simp only [tLoc, Function.update_self]
    split
    · exact ⟨by assumption, by simpa using h1, by simpa [Past, skipped] using h2⟩
    · exact ⟨by simpa using h1, by simpa [Past, skipped] using h2⟩

theorem pcInv_updPC (hpI : PCInv M s i (.upd m)) {s' : St n k} (hr : (s'.loc i).r = (s.loc i).r)
    (hP : Past M s' i (s'.loc i).r ↔ Past M s i (s.loc i).r) :
    PCInv M s' i (updPC (k := k) m) := by
  obtain ⟨-, h1, h2⟩ := hpI
  unfold updPC; split
  · exact ⟨by assumption, hr ▸ h1, hP.2 h2⟩
  · exact ⟨hr ▸ h1, hP.2 h2⟩

theorem pastL_updPC (ℓ m : ℕ) : PastL ℓ (updPC (k := k) m) := by
  unfold updPC; split <;> trivial

theorem inv_updIn (hI : Inv M s) {m : ℕ} (hm : m < k) (hpc : (s.loc i).pc = .upd m) :
    Inv M (tUpdIn M s i m ⟨m, hm⟩) := by
  have h := hI.proc i
  have hp := h.pc; rw [hpc] at hp
  refine inv_local (i := i) hI rfl rfl rfl rfl rfl rfl
    (fun j (hj : j ≠ i) => by simp [tUpdIn, Function.update_of_ne hj]) ?_
  refine pInv_sameRound h rfl rfl rfl rfl (by simp [tUpdIn]) ?_ ?_
  · intro _; simp only [tUpdIn, Function.update_self]; exact pastL_updPC _ _
  · simp only [tUpdIn, Function.update_self]
    exact pcInv_updPC hp (by simp) (by simp [Past, skipped])

theorem inv_updMine (hI : Inv M s) {m : ℕ} (hm : m < k) (hpc : (s.loc i).pc = .upd m) :
    Inv M (tUpdMine M s i m ⟨m, hm⟩) := by
  have h := hI.proc i
  have hp := h.pc; rw [hpc] at hp
  refine inv_local (i := i) hI rfl rfl rfl rfl rfl rfl
    (fun j (hj : j ≠ i) => by simp [tUpdMine, Function.update_of_ne hj]) ?_
  refine pInv_sameRound h rfl rfl rfl rfl (by simp [tUpdMine]) ?_ ?_
  · intro _; simp only [tUpdMine, Function.update_self]; exact pastL_updPC _ _
  · simp only [tUpdMine, Function.update_self]
    exact pcInv_updPC hp (by simp) (by simp [Past, skipped])

theorem inv_updOther (hI : Inv M s) {m : ℕ} (hm : m < k) (hpc : (s.loc i).pc = .upd m) :
    Inv M (tUpdOther M s i m ⟨m, hm⟩) := by
  have h := hI.proc i
  have hp := h.pc; rw [hpc] at hp
  refine inv_local (i := i) hI rfl rfl rfl rfl rfl rfl
    (fun j (hj : j ≠ i) => by simp [tUpdOther, Function.update_of_ne hj]) ?_
  refine pInv_sameRound h rfl rfl rfl rfl (by simp [tUpdOther]) ?_ ?_
  · intro _; simp only [tUpdOther, Function.update_self]; exact pastL_updPC _ _
  · simp only [tUpdOther, Function.update_self]
    exact pcInv_updPC hp (by simp) (by simp [Past, skipped])

theorem inv_updAdopt (hI : Inv M s) {m : ℕ} (hm : m < k) (hpc : (s.loc i).pc = .upd m) :
    Inv M (tUpdAdopt s i m ⟨m, hm⟩) := by
  have h := hI.proc i
  have hp := h.pc; rw [hpc] at hp
  refine inv_local (i := i) hI rfl rfl rfl rfl rfl rfl
    (fun j (hj : j ≠ i) => by simp [tUpdAdopt, Function.update_of_ne hj]) ?_
  refine pInv_sameRound h rfl rfl rfl rfl (by simp [tUpdAdopt]) ?_ ?_
  · intro _; simp only [tUpdAdopt, Function.update_self]; exact pastL_updPC _ _
  · simp only [tUpdAdopt, Function.update_self]
    exact pcInv_updPC hp (by simp) (by simp [Past, skipped])

/-- The first line of a round satisfies the invariant if nothing of the round has been invoked. -/
theorem pcInv_startPC (hk : 0 < k) {s : St n k} {i : Fin n} (hr : 1 ≤ (s.loc i).r)
    (hfut : (∀ b x, s.acI (s.loc i).r b x i = none) ∧ s.scI (s.loc i).r i = none) :
    PCInv M s i (startPC M) := by
  unfold startPC
  split
  · exact ⟨by assumption, hk, hr, fun x _ => hfut.1 _ x, fun x => hfut.1 _ x, hfut.2,
      fun x hx => absurd hx (Nat.not_lt_zero _)⟩
  · exact ⟨hr, fun x => hfut.1 _ x, hfut.2⟩

theorem pastL_startPC (ℓ : ℕ) : ¬ PastL ℓ (startPC M) := by
  unfold startPC; split <;> simp [PastL]

theorem inv_init_step (hk : 0 < k) (hI : Inv M s) (hpc : (s.loc i).pc = .init) :
    Inv M (tInit M s i) := by
  have h := hI.proc i
  have hp := h.pc; rw [hpc] at hp; simp only [PCInv] at hp
  refine inv_local (i := i) hI rfl rfl rfl rfl rfl rfl
    (fun j (hj : j ≠ i) => by simp [tInit, Function.update_of_ne hj]) ?_
  have hl : (tInit M s i).loc i =
      { s.loc i with pc := startPC M, r := 1, cnt := fun _ => 0, oper := fun _ => (i, 0) } := by
    simp [tInit]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr; rw [hl] at hr; exact h.fut r (by simp at hr; omega)
  · intro r h1 hr; rw [hl] at hr; simp at hr; omega
  · intro r hr
    rcases h.first r hr with h' | ⟨-, h'⟩
    · rw [hp] at h'; omega
    · rw [hpc] at h'; simp [PastL] at h'
  · rw [hl]
    exact pcInv_startPC hk (by simp [tInit]) (by
      simpa [tInit] using h.fut 1 (by omega))

theorem inv_write (hk : 0 < k) (hI : Inv M s) (hpc : (s.loc i).pc = .write) :
    Inv M (tWrite M s i) := by
  have h := hI.proc i
  have hp := h.pc; rw [hpc] at hp; obtain ⟨h1, h2⟩ := hp
  refine inv_local (i := i) hI rfl rfl rfl rfl rfl rfl
    (fun j (hj : j ≠ i) => by simp [tWrite, Function.update_of_ne hj]) ?_
  have hl : (tWrite M s i).loc i =
      { s.loc i with pc := startPC M, r := (s.loc i).r + 1, res := [] } := by
    simp [tWrite]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr; rw [hl] at hr; exact h.fut r (by simp at hr; omega)
  · intro r h1 hr; rw [hl] at hr; simp at hr
    rcases Nat.lt_or_eq_of_le hr with hr | rfl
    · exact h.past r h1 hr
    · exact h2
  · intro r hr; rw [hl]
    rcases h.first r hr with h' | ⟨h', -⟩
    · left; simp; omega
    · left; simp; omega
  · rw [hl]
    exact pcInv_startPC hk (by simp) (by simpa [tWrite] using h.fut _ (by omega))

end Local

/-! ### Steps on base objects -/

/-- A step of process `i` that stays in its round and changes the base objects (and `firstL`)
only in the current round. -/
theorem pInv_step {M : Mode} {s s' : St n k} {i : Fin n} (h : PInv M s i)
    (hr : (s'.loc i).r = (s.loc i).r)
    (hacI : ∀ r b x, r ≠ (s.loc i).r → s'.acI r b x i = s.acI r b x i)
    (hscI : ∀ r, r ≠ (s.loc i).r → s'.scI r i = s.scI r i)
    (hacR : ∀ r b x, r ≠ (s.loc i).r → s'.acR r b x i = s.acR r b x i)
    (hfirst : ∀ r, r ≠ (s.loc i).r → s'.firstL r = s.firstL r)
    (hL : s'.firstL (s.loc i).r = some i → PastL M.ℓ (s'.loc i).pc)
    (hpc : PCInv M s' i (s'.loc i).pc) : PInv M s' i := by
  refine ⟨?_, ?_, ?_, hpc⟩
  · intro r h'; rw [hr] at h'
    rw [hscI r (by omega)]
    refine ⟨fun b x => ?_, (h.fut r h').2⟩
    rw [hacI r b x (by omega)]; exact (h.fut r h').1 b x
  · intro r h1 h'; rw [hr] at h'
    have hne : r ≠ (s.loc i).r := by omega
    rcases h.past r h1 h' with hp | hp
    · left; refine ⟨hp.1, fun y => ?_⟩
      rw [hacR r false y hne]; exact hp.2 y
    · right; rwa [hfirst r hne]
  · intro r h'
    rw [hr]
    by_cases hre : r = (s.loc i).r
    · subst hre; exact Or.inr ⟨rfl, hL h'⟩
    · rw [hfirst r hre] at h'
      rcases h.first r h' with h'' | ⟨h'', -⟩
      · exact Or.inl h''
      · exact absurd h'' hre

section Shared
variable {M : Mode} {s : St n k} {i : Fin n}

theorem inv_n1Inv (hI : Inv M s) {m : ℕ} (hm : m < k) (hpc : (s.loc i).pc = .n1Inv m) :
    Inv M (tN1Inv s i m ⟨m, hm⟩) := by
  have h := hI.proc i
  have hp := h.pc; rw [hpc] at hp
  obtain ⟨hca, -, h1, hnoneF, hnoT, hscI, htags⟩ := hp
  refine ⟨ac_invoke_all hI.ac (hnoneF ⟨m, hm⟩ le_rfl) _, hI.sc, hI.l1, ?_, ?_⟩
  · intro r hr q y w hw
    exact hI.l2 r hr q y w (by simpa [tN1Inv] using hw)
  · intro j
    by_cases hj : j = i
    · subst hj
      refine pInv_step h (by simp [tN1Inv]) (fun r b x hr => by simp [tN1Inv, hr])
        (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ => rfl) ?_ ?_
      · intro h'; rcases h.first _ h' with h'' | ⟨-, h''⟩
        · omega
        · rw [hpc] at h''; exact absurd h'' (by simp [PastL])
      · simp only [tN1Inv, Function.update_self, PCInv, NoTrue, N1Tags]
        refine ⟨hca, ⟨hm, by simp⟩, h1, fun x hx => ?_, fun x => ?_, hscI, htags⟩
        · have : x ≠ ⟨m, hm⟩ := by intro h'; subst h'; simp at hx
          simp [this, hnoneF x (by omega)]
        · simp [hnoT x]
    · exact pInv_others (s' := tN1Inv s i m ⟨m, hm⟩) (i := i) hI
        (fun j' hj' => by simp [tN1Inv, Function.update_of_ne hj'])
        (by intro r b x j' hj'; simp [tN1Inv, hj']) (fun _ _ _ _ _ => rfl)
        (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => Or.inl rfl) j hj

theorem inv_n1Resp (hI : Inv M s) {m : ℕ} (hm : m < k) (hpc : (s.loc i).pc = .n1Resp m)
    {t : Bool} {v : Op n}
    (hok : acOK M.strongAC (s.acI (s.loc i).r false ⟨m, hm⟩) (s.acR (s.loc i).r false ⟨m, hm⟩)
      (s.acFree (s.loc i).r false ⟨m, hm⟩) i ((s.loc i).oper ⟨m, hm⟩) t v) :
    Inv M (tN1Resp s i m ⟨m, hm⟩ t v) := by
  have h := hI.proc i
  have hp := h.pc; rw [hpc] at hp
  obtain ⟨hca, ⟨_, hown⟩, h1, hnoneF, hnoT, hscI, htags⟩ := hp
  refine ⟨ac_respond_all hI.ac hown hok, hI.sc, ?_, hI.l2, ?_⟩
  · intro r q hq
    obtain ⟨d, hd, hc⟩ := hI.l1 r q hq
    exact ⟨d, hd, fun y w hy => by simpa [tN1Resp] using hc y w hy⟩
  · intro j
    by_cases hj : j = i
    · subst hj
      refine pInv_step h (by simp [tN1Resp]) (fun _ _ _ _ => rfl) (fun _ _ => rfl)
        (fun r b x hr => by simp [tN1Resp, hr]) (fun _ _ => rfl) ?_ ?_
      · intro h'; rcases h.first _ h' with h'' | ⟨-, h''⟩
        · omega
        · rw [hpc] at h''; exact absurd h'' (by simp [PastL])
      · simp only [tN1Resp, Function.update_self]
        split
        · simp only [PCInv, NoTrue, N1Tags, Function.update_self]
          refine ⟨hca, by assumption, h1, fun x hx => hnoneF x (by omega), hnoT, hscI,
            fun x hx => ?_⟩
          by_cases hx' : x = ⟨m, hm⟩
          · subst hx'; simp
          · have hxm : x.val ≠ m := fun h' => hx' (Fin.ext h')
            have := htags x (by omega)
            simp [hx', this]
        · unfold afterN1; split
          · rename_i hnlt hall
            simp only [PCInv, Past, skipped, Function.update_self]
            refine ⟨j.pos, h1, Or.inl ⟨hca, fun y => ?_⟩⟩
            have hally := hall y
            by_cases hy : y = ⟨m, hm⟩
            · subst hy; simp at hally; simp [hally]
            · have hym : y.val ≠ m := fun h' => hy (Fin.ext h')
              have := htags y (by omega)
              simp [hy] at hally
              simp [hy, this, hally]
          · simp only [PCInv, NoTrue, Function.update_self]
            exact ⟨h1, hnoT, hscI⟩
    · exact pInv_others (s' := tN1Resp s i m ⟨m, hm⟩ t v) (i := i) hI
        (fun j' hj' => by simp [tN1Resp, Function.update_of_ne hj'])
        (fun _ _ _ _ _ => rfl) (by intro r b x j' hj'; simp [tN1Resp, hj'])
        (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => Or.inl rfl) j hj

theorem inv_scInv (hI : Inv M s) (hpc : (s.loc i).pc = .scInv) : Inv M (tScInv M s i) := by
  have h := hI.proc i
  have hp := h.pc; rw [hpc] at hp
  obtain ⟨h1, hnoT, hscI⟩ := hp
  refine ⟨hI.ac, sc_invoke_all hI.sc hscI _, hI.l1, hI.l2, ?_⟩
  intro j
  by_cases hj : j = i
  · subst hj
    refine pInv_step h (by simp [tScInv]) (fun _ _ _ _ => rfl) (fun r hr => by simp [tScInv, hr])
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) ?_ ?_
    · intro h'; rcases h.first _ h' with h'' | ⟨-, h''⟩
      · omega
      · rw [hpc] at h''; exact absurd h'' (by simp [PastL])
    · simp only [tScInv, Function.update_self, PCInv, NoTrue]
      exact ⟨h1, hnoT, by simp⟩
  · exact pInv_others (s' := tScInv M s i) (i := i) hI
      (fun j' hj' => by simp [tScInv, Function.update_of_ne hj'])
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      (by intro r j' hj'; simp [tScInv, hj']) (fun _ _ _ => rfl) (fun _ => Or.inl rfl) j hj

theorem inv_scResp (hℓ : 1 ≤ M.ℓ) (hk : 0 < k) (hI : Inv M s) (hpc : (s.loc i).pc = .scResp)
    {d : Fin k → Option (Op n)} (hok : scOK M.ℓ (s.scI (s.loc i).r) (s.scR (s.loc i).r) d) :
    Inv M (tScResp s i d) := by
  have h := hI.proc i
  have hp := h.pc; rw [hpc] at hp
  obtain ⟨h1, hnoT, -⟩ := hp
  have hnf : s.firstL (s.loc i).r ≠ some i := by
    intro h'; rcases h.first _ h' with h'' | ⟨-, h''⟩
    · omega
    · rw [hpc] at h''; exact h''
  refine ⟨hI.ac, sc_respond_all hI.sc hok, ?_, ?_, ?_⟩
  · intro r q hq
    obtain ⟨d', hd', hc⟩ := hI.l1 r q hq
    refine ⟨d', ?_, hc⟩
    have : ¬ (r = (s.loc i).r ∧ q = i) := by
      rintro ⟨rfl, rfl⟩; exact hnf hq
    simp only [tScResp]; split
    · exact absurd ‹_› this
    · exact hd'
  · intro r hr q y w hw
    obtain ⟨d', hd', hc⟩ := hI.l2 r hr q y w hw
    refine ⟨d', ?_, hc⟩
    have : ¬ (r = (s.loc i).r ∧ q = i) := by
      rintro ⟨rfl, rfl⟩
      have hw' : s.acI (s.loc q).r true y q = some w := hw
      rw [hnoT y] at hw'; simp at hw'
    simp only [tScResp]; split
    · exact absurd ‹_› this
    · exact hd'
  · intro j
    by_cases hj : j = i
    · subst hj
      refine pInv_step h (by simp [tScResp]) (fun _ _ _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun h' => absurd h' hnf) ?_
      simp only [tScResp, Function.update_self, PCInv, Commits]
      refine ⟨h1, hk, by simp, trivial, fun j' x _ _ => hnoT x, fun h' => by omega,
        fun _ j' _ _ h' => by omega⟩
    · exact pInv_others (s' := tScResp s i d) (i := i) hI
        (fun j' hj' => by simp [tScResp, Function.update_of_ne hj'])
        (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ => rfl)
        (by intro r j' hj'; simp [tScResp, hj']) (fun _ => Or.inl rfl) j hj

theorem inv_acInv (hI : Inv M s) {j : ℕ} {x : Fin k} (hpc : (s.loc i).pc = .acInv j)
    (hx : (s.loc i).ord[j]? = some x) : Inv M (tAcInv M s i j x) := by
  have h := hI.proc i
  have hp := h.pc; rw [hpc] at hp
  obtain ⟨h1, hjk, hscR, hord, hnone, hfl, hcom⟩ := hp
  refine ⟨ac_invoke_all hI.ac (hnone j x le_rfl hx) _, hI.sc, hI.l1, ?_, ?_⟩
  · intro r hr q y w hw
    simp only [tAcInv] at hw
    split at hw
    · obtain ⟨rfl, -, rfl, rfl⟩ := ‹_ ∧ _›
      simp only [Option.some.injEq] at hw; subst hw
      refine ⟨_, hscR, ?_⟩
      have hjℓ : j < M.ℓ := by
        by_contra hc; exact hfl (by omega) hr
      rw [hord] at hx
      rcases ordOf_get hx with ⟨-, hs⟩ | ⟨hc, -⟩
      · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
        simp [acVal, hw]
      · rw [(hI.sc _).card _ _ hscR] at hc; omega
    · exact hI.l2 r hr q y w hw
  · intro j'
    by_cases hj : j' = i
    · subst hj
      refine pInv_step h (by simp [tAcInv]) (fun r b x hr => by simp [tAcInv, hr])
        (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ => rfl) ?_ ?_
      · intro h'; rcases h.first _ h' with h'' | ⟨-, h''⟩
        · omega
        · rw [hpc] at h''; simpa [tAcInv, PastL] using h''
      · simp only [tAcInv, Function.update_self, PCInv, Commits]
        refine ⟨h1, hscR, hord, ⟨x, hx, by simp [acVal]⟩, fun j'' y hj'' hy => ?_, hfl, hcom⟩
        have hyx : y ≠ x := by
          rintro rfl
          have := getElem?_inj_of_nodup (hord ▸ ordOf_nodup _) hx hy
          omega
        simp [hyx, hnone j'' y (by omega) hy]
    · exact pInv_others (s' := tAcInv M s i j x) (i := i) hI
        (fun j'' hj'' => by simp [tAcInv, Function.update_of_ne hj''])
        (by intro r b y j'' hj''; simp [tAcInv, hj'']) (fun _ _ _ _ _ => rfl)
        (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => Or.inl rfl) j' hj

theorem inv_acResp (hI : Inv M s) {j : ℕ} {x : Fin k} (hpc : (s.loc i).pc = .acResp j)
    (hx : (s.loc i).ord[j]? = some x) {t : Bool} {v : Op n}
    (hok : acOK M.strongAC (s.acI (s.loc i).r true x) (s.acR (s.loc i).r true x)
      (s.acFree (s.loc i).r true x) i (acVal M (s.loc i) x) t v) :
    Inv M (tAcResp M s i j x t v) := by
  have h := hI.proc i
  have hp := h.pc; rw [hpc] at hp
  obtain ⟨h1, hscR, hord, ⟨x', hx', hown⟩, hnone, hfl, hcom⟩ := hp
  have hxx : x' = x := by rw [hx] at hx'; exact (Option.some.inj hx').symm
  rw [hxx] at hown
  have hcard := (hI.sc _).card _ _ hscR
  have hlen : (s.loc i).ord.length = k := by rw [hord, ordOf_length]
  have hnd : (s.loc i).ord.Nodup := hord ▸ ordOf_nodup _
  -- the response is a commit of the decided value while `firstL` is unset
  have hcommit : s.firstL (s.loc i).r = none → ∀ w, (s.loc i).scd x = some w →
      t = true ∧ v = w := by
    intro hfn w hw
    have hval : acVal M (s.loc i) x = w := by simp [acVal, hw]
    have := hok.2.2.2.1 (by
      intro q _ w' hw'
      obtain ⟨d', hd', hdx⟩ := hI.l2 _ hfn q x w' hw'
      rw [hval]; exact (hI.sc _).agree q i d' _ x w' w hd' hscR hdx hw)
    rw [hval] at this; exact this
  have hfl' : M.ℓ ≤ j + 1 → (tAcResp M s i j x t v).firstL (s.loc i).r ≠ none := by
    intro hle
    simp only [tAcResp]
    split
    · simp
    · rename_i hc
      intro hn; apply hc; refine ⟨trivial, ?_, hn⟩
      by_contra hne; exact hfl (by omega) hn
  have hfn' : (tAcResp M s i j x t v).firstL (s.loc i).r = none →
      s.firstL (s.loc i).r = none := by
    simp only [tAcResp]; split
    · simp
    · exact id
  refine ⟨ac_respond_all hI.ac hown hok, hI.sc, ?_, ?_, ?_⟩
  · intro r q hq
    simp only [tAcResp] at hq
    split at hq
    · rename_i hc
      obtain ⟨rfl, hjℓ, hfn⟩ := hc
      obtain rfl := Option.some.inj hq
      refine ⟨_, hscR, fun y w hy => ?_⟩
      simp only [tAcResp]
      by_cases hyx : y = x
      · subst hyx
        obtain ⟨rfl, rfl⟩ := hcommit hfn w hy
        simp
      · simp only [hyx, false_and, and_false, ↓reduceIte]
        obtain ⟨j', hj', hj'y⟩ := ordOf_decided (d := (s.loc i).scd) (x := y) (by simp [hy])
        rw [← hord] at hj'y
        have hjj : j' ≠ j := by
          rintro rfl; rw [hx] at hj'y; exact hyx (Option.some.inj hj'y).symm
        exact hcom hfn j' y w (by omega) hj'y hy
    · obtain ⟨d, hd, hc⟩ := hI.l1 r q hq
      refine ⟨d, hd, fun y w hy => ?_⟩
      simp only [tAcResp]
      split
      · rename_i hc'
        obtain ⟨rfl, -, rfl, rfl⟩ := hc'
        exfalso
        rcases h.first _ hq with h'' | ⟨-, h''⟩
        · omega
        · rw [hpc] at h''
          simp only [PastL] at h''
          rw [hscR] at hd; obtain rfl := Option.some.inj hd
          rw [hord] at hx
          rcases ordOf_get hx with ⟨hc2, -⟩ | ⟨-, hc2⟩
          · omega
          · rw [hc2] at hy; simp at hy
      · exact hc y w hy
  · intro r hr q y w hw
    refine hI.l2 r ?_ q y w hw
    simp only [tAcResp] at hr; split at hr
    · simp at hr
    · exact hr
  · intro j'
    by_cases hj : j' = i
    · subst hj
      refine pInv_step h (by simp [tAcResp]) (fun _ _ _ _ => rfl) (fun _ _ => rfl)
        (fun r b y hr => by simp [tAcResp, hr]) (fun r hr => by simp [tAcResp, hr]) ?_ ?_
      · intro h'
        simp only [tAcResp, Function.update_self]
        split
        · simp only [PastL]
          simp only [tAcResp] at h'
          split at h'
          · omega
          · rcases h.first _ h' with h'' | ⟨-, h''⟩
            · omega
            · rw [hpc] at h''; simp only [PastL] at h''; omega
        · trivial
      · simp only [tAcResp, Function.update_self]
        split
        · rename_i hlt
          simp only [PCInv, Commits, Function.update_self]
          refine ⟨h1, by omega, hscR, hord, fun j'' y hj'' hy => hnone j'' y (by omega) hy,
            fun hle => by simpa [tAcResp] using hfl' hle, fun hfn j'' y w hj'' hy hw => ?_⟩
          have hfn0 := hfn' (by simpa [tAcResp] using hfn)
          by_cases hyx : y = x
          · subst hyx
            obtain ⟨rfl, rfl⟩ := hcommit hfn0 w hw
            simp
          · have hjj : j'' ≠ j := by
              rintro rfl; rw [hx] at hy; exact hyx (Option.some.inj hy).symm
            simp only [hyx, false_and, and_false, ↓reduceIte]
            exact hcom hfn0 j'' y w (by omega) hy hw
        · rename_i hlt
          simp only [PCInv, Past, Function.update_self]
          have hℓk : M.ℓ ≤ k := by
            rw [← hcard]; exact (Finset.card_le_univ _).trans (by simp)
          exact ⟨j'.pos, h1, Or.inr (by simpa [tAcResp] using hfl' (by omega))⟩
    · refine pInv_others (s' := tAcResp M s i j x t v) (i := i) hI
        (fun j'' hj'' => by simp [tAcResp, Function.update_of_ne hj''])
        (fun _ _ _ _ _ => rfl) (by intro r b y j'' hj''; simp [tAcResp, hj''])
        (fun _ _ _ => rfl) (fun _ _ _ => rfl) ?_ j' hj
      intro r
      simp only [tAcResp]
      split
      · rename_i hc; exact Or.inr ⟨hc.2.2, rfl⟩
      · exact Or.inl rfl

end Shared

/-! ### The invariant holds in every reachable state -/

theorem inv_step {M : Mode} (hℓ : 1 ≤ M.ℓ) (hk : 0 < k) {s s' : St n k} {a : Act n k}
    (hI : Inv M s) (h : stepFn M s a = some s') : Inv M s' := by
  rcases stepFn_cases h with ⟨hpc, rfl⟩ | ⟨m, hm, hpc, rfl⟩ | ⟨m, hm, t, v, hpc, -, hok, rfl⟩ |
    ⟨hpc, rfl⟩ | ⟨d, hpc, -, hok, rfl⟩ | ⟨j, x, hpc, hx, rfl⟩ |
    ⟨j, x, t, v, hpc, hx, -, hok, rfl⟩ | ⟨q, hq, hpc, rfl⟩ | ⟨hpc, rfl⟩ | ⟨m, hm, hpc, -, rfl⟩ |
    ⟨m, hm, hpc, -, -, -, rfl⟩ | ⟨m, hm, hpc, -, -, -, rfl⟩ | ⟨m, hm, hpc, -, -, rfl⟩ | ⟨hpc, rfl⟩
  · exact inv_init_step hk hI hpc
  · exact inv_n1Inv hI hm hpc
  · exact inv_n1Resp hI hm hpc hok
  · exact inv_scInv hI hpc
  · exact inv_scResp hℓ hk hI hpc hok
  · exact inv_acInv hI hpc hx
  · exact inv_acResp hI hpc hx hok
  · exact inv_collect hI hq hpc
  · exact inv_loc hI hpc
  · exact inv_updIn hI hm hpc
  · exact inv_updMine hI hm hpc
  · exact inv_updOther hI hm hpc
  · exact inv_updAdopt hI hm hpc
  · exact inv_write hk hI hpc

/-- The inductive invariant holds in every reachable state. -/
theorem inv_reachable {M : Mode} (hℓ : 1 ≤ M.ℓ) (hk : 0 < k) {s : St n k}
    (hs : Reachable M s) : Inv M s := by
  induction hs with
  | refl => exact inv_init M
  | tail _ hst ih => obtain ⟨a, ha⟩ := hst; exact inv_step hℓ hk ih ha

/-! ### Every process can always take a step -/

/-- **Non-vacuity of the base-object specifications.** If `1 ≤ ℓ ≤ k`, then in every reachable
state every process has an enabled action: the adopt-commit (`acOK`) and `(k, ℓ)`-SC (`scOK`)
specifications always admit a response (the base objects are wait-free), and the other lines
are always executable. -/
theorem enabled {M : Mode} (hℓ : 1 ≤ M.ℓ) (hℓk : M.ℓ ≤ k) {s : St n k} (hs : Reachable M s)
    (i : Fin n) : ∃ a : Act n k, a.proc = i ∧ (stepFn M s a).isSome := by
  have hk : 0 < k := by omega
  have hI := inv_reachable hℓ hk hs
  have hp := (hI.proc i).pc
  generalize hpc : (s.loc i).pc = pc at hp
  cases pc with
  | init => exact ⟨.go i, rfl, by simp [stepFn, hpc]⟩
  | n1Inv m =>
    obtain ⟨-, hm, -⟩ := hp
    exact ⟨.go i, rfl, by simp [stepFn, hpc, hm]⟩
  | n1Resp m =>
    obtain ⟨-, ⟨hm, hown⟩, -⟩ := hp
    obtain ⟨t, v, hok⟩ := acOK_exists (hI.ac _ _ _) hown
    exact ⟨.ac i t v, rfl, by simp [stepFn, hpc, hm, hok]⟩
  | scInv => exact ⟨.go i, rfl, by simp [stepFn, hpc]⟩
  | scResp =>
    obtain ⟨-, -, hu⟩ := hp
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hu
    obtain ⟨d, hok⟩ := scOK_exists (hI.sc _) hu hℓk
    exact ⟨.sc i d, rfl, by simp [stepFn, hpc, hok]⟩
  | acInv j =>
    obtain ⟨-, hjk, -, hord, -⟩ := hp
    have hj : j < (s.loc i).ord.length := by rw [hord, ordOf_length]; exact hjk
    obtain ⟨x, hx⟩ : ∃ x, (s.loc i).ord[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    exact ⟨.go i, rfl, by simp [stepFn, hpc, hx]⟩
  | acResp j =>
    obtain ⟨-, -, -, ⟨x, hx, hown⟩, -⟩ := hp
    obtain ⟨t, v, hok⟩ := acOK_exists (hI.ac _ _ _) hown
    exact ⟨.ac i t v, rfl, by simp [stepFn, hpc, hx, hok]⟩
  | collect q =>
    obtain ⟨hq, -⟩ := hp
    exact ⟨.go i, rfl, by simp [stepFn, hpc, hq]⟩
  | loc => exact ⟨.go i, rfl, by simp [stepFn, hpc]⟩
  | upd m =>
    obtain ⟨hm, -⟩ := hp
    refine ⟨.go i, rfl, ?_⟩
    simp only [stepFn, hpc, hm, dite_true]
    split_ifs <;> simp
  | write => exact ⟨.go i, rfl, by simp [stepFn, hpc]⟩

/-- **Non-vacuity of the execution model.** If `1 ≤ ℓ ≤ k` and there is at least one process,
there is an infinite execution (round-robin, with responses of the base objects chosen
arbitrarily among the allowed ones) in which every process is correct. -/
theorem exists_exec {M : Mode} (hℓ : 1 ≤ M.ℓ) (hℓk : M.ℓ ≤ k) (hn : 0 < n) :
    ∃ e : Exec M n k, ∀ i, e.Correct i := by
  choose act hproc hsome using
    fun (s : {s : St n k // Reachable M s}) (i : Fin n) => enabled hℓ hℓk s.2 i
  let p : ℕ → Fin n := fun t => ⟨t % n, Nat.mod_lt _ hn⟩
  let nxt : {s : St n k // Reachable M s} → ℕ → {s : St n k // Reachable M s} := fun s t =>
    ⟨(stepFn M s.1 (act s (p t))).get (hsome s (p t)),
      Relation.ReflTransGen.tail s.2 ⟨_, (Option.some_get _).symm⟩⟩
  let sq : ℕ → {s : St n k // Reachable M s} := fun t =>
    Nat.rec ⟨init, Relation.ReflTransGen.refl⟩ (fun t s => nxt s t) t
  refine ⟨⟨fun t => (sq t).1, fun t => act (sq t) (p t), rfl, fun t => ?_⟩, fun i N => ?_⟩
  · exact (Option.some_get _).symm
  · refine ⟨N * n + i.val, ?_, ?_⟩
    · have : N ≤ N * n := Nat.le_mul_of_pos_right _ hn
      omega
    · show (act _ (p _)).proc = i
      rw [hproc]
      ext
      simp only [p, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.isLt]

end Podc.DistributedUniversality.NonVacuity
