import Papers.PODC2018.FairLeaderElection.Characterization

/-!
# Rushing attacks on `A-LEADuni` (Section 4 of [YM18]): the generic attacker

The attacks of Lemma 4.1 and of the Cubic Attack (Theorem 4.3) are instances of one *rushing*
adversary strategy with parameters `F` (number of forwarded messages), `z` (number of zeros sent
after them) and the length `l` of its honest segment. An adversary `a` never draws a secret:

1. it forwards its first `F` incoming messages (immediately);
2. after its `F`-th incoming message (at wake-up if `F = 0`) it sends `z` zeros;
3. after its `(n-k)`-th incoming message (`k = |C|`; it then knows all `n-k` honest secrets) it
   sends `M = w - (sum of everything else it sends)`, then `n - F - z - 1 - l` zeros, then the last
   `l` of its incoming messages (the secrets of its own segment, in the right order), and
   terminates with output `w`.

Lemma 4.1 is `F = n - k`, `z = 0`; the Cubic Attack is `F = n - k - l`, `z = k - 1`.

This file proves the general theorem `rushing_outcome`: if the origin is honest and the parameters
satisfy the content conditions `n - k - l_a ≤ F_a ≤ n - k`, the budget `F_a + z_a + 1 + l_a ≤ n`,
and the liveness conditions (some adversary `a*` has `n - k ≤ F_{a*} + z_{a*}`, and every other
adversary `a` passes enough messages to the next one: `F_{next a} ≤ F_a + z_a`), then the outcome
is `w` for every choice of the honest secrets.

Preliminaries: `dist C x`, `prev C x` (the closest adversary before `x`), and the list `Back` of
honest secrets met when walking backwards around the ring.
-/

namespace Podc.FairLeaderElection

open Cslib.UniRing
open Fin.NatCast Fin.CommRing

variable {n : ℕ} [NeZero n]

/-! ### The closest adversary before a processor -/

section Prev

variable (C : Finset (Fin n))

open Classical in
/-- `dist C x + 1` is the distance from the closest adversary before `x` to `x`. -/
noncomputable def dist (x : Fin n) : ℕ :=
  if h : ∃ t : ℕ, x - ((t + 1 : ℕ) : Fin n) ∈ C then Nat.find h else 0

/-- The closest adversary strictly before `x` (going backwards around the ring; possibly `x`
itself if it is the only adversary). -/
noncomputable def prev (x : Fin n) : Fin n := x - ((dist C x + 1 : ℕ) : Fin n)

variable {C}

theorem exists_prev' (hC : C.Nonempty) (x : Fin n) :
    ∃ t : ℕ, t < n ∧ x - ((t + 1 : ℕ) : Fin n) ∈ C := by
  obtain ⟨c0, hc0⟩ := hC
  rcases eq_or_ne x c0 with rfl | hne
  · exact ⟨n - 1, by have := NeZero.pos n; omega,
      by rw [Nat.sub_add_cancel (NeZero.pos n)]; simpa using hc0⟩
  · have hpos : 0 < (x - c0 : Fin n).val := by
      rw [Nat.pos_iff_ne_zero, Ne, Fin.val_eq_zero_iff, sub_eq_zero]; exact hne
    refine ⟨(x - c0 : Fin n).val - 1, by have := (x - c0 : Fin n).isLt; omega, ?_⟩
    rw [Nat.sub_add_cancel hpos, Fin.cast_val_eq_self, sub_sub_cancel]; exact hc0

theorem exists_prev (hC : C.Nonempty) (x : Fin n) : ∃ t : ℕ, x - ((t + 1 : ℕ) : Fin n) ∈ C :=
  let ⟨t, _, ht⟩ := exists_prev' hC x; ⟨t, ht⟩

theorem prev_mem (hC : C.Nonempty) (x : Fin n) : prev C x ∈ C := by
  classical
  unfold prev dist
  rw [dif_pos (exists_prev hC x)]
  exact Nat.find_spec (exists_prev hC x)

theorem not_mem_of_lt_dist (hC : C.Nonempty) {x : Fin n} {t : ℕ} (ht : t < dist C x) :
    x - ((t + 1 : ℕ) : Fin n) ∉ C := by
  classical
  unfold dist at ht
  rw [dif_pos (exists_prev hC x)] at ht
  exact Nat.find_min (exists_prev hC x) ht

theorem dist_le (hC : C.Nonempty) {x : Fin n} {t : ℕ} (ht : x - ((t + 1 : ℕ) : Fin n) ∈ C) :
    dist C x ≤ t := by
  classical
  unfold dist
  rw [dif_pos (exists_prev hC x)]
  exact Nat.find_min' _ ht

theorem dist_lt (hC : C.Nonempty) (x : Fin n) : dist C x < n := by
  obtain ⟨t, ht, hm⟩ := exists_prev' hC x
  exact lt_of_le_of_lt (dist_le hC hm) ht

theorem dist_eq_iff (hC : C.Nonempty) {x : Fin n} {t : ℕ} :
    dist C x = t ↔ x - ((t + 1 : ℕ) : Fin n) ∈ C ∧ ∀ t' < t, x - ((t' + 1 : ℕ) : Fin n) ∉ C := by
  constructor
  · rintro rfl; exact ⟨prev_mem hC x, fun t' ht' => not_mem_of_lt_dist hC ht'⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm (dist_le hC h1) ?_
    by_contra hlt; push_neg at hlt
    exact h2 _ hlt (prev_mem hC x)

theorem prev_add (x : Fin n) : prev C x + ((dist C x + 1 : ℕ) : Fin n) = x := by
  simp [prev]

theorem dist_succ (hC : C.Nonempty) (j : Fin n) :
    dist C (j + 1) = if j ∈ C then 0 else dist C j + 1 := by
  split_ifs with hj
  · exact Nat.le_zero.mp (dist_le hC (by simpa using hj))
  · rw [dist_eq_iff hC]
    refine ⟨?_, fun t' ht' => ?_⟩
    · have := prev_mem hC j
      simp only [prev] at this
      convert this using 1; push_cast; ring
    · rcases t' with _ | t'
      · simpa using hj
      · have := not_mem_of_lt_dist hC (x := j) (t := t') (by omega)
        convert this using 1; push_cast; ring

theorem prev_succ (hC : C.Nonempty) (j : Fin n) :
    prev C (j + 1) = if j ∈ C then j else prev C j := by
  unfold prev
  rw [dist_succ hC]
  split_ifs <;> push_cast <;> ring

theorem gap_mem {a : Fin n} (ha : a ∈ C) : a + ((gap C a + 1 : ℕ) : Fin n) ∈ C := by
  classical
  have hex : ∃ t : ℕ, a + ((t + 1 : ℕ) : Fin n) ∈ C :=
    ⟨n - 1, by rw [Nat.sub_add_cancel (NeZero.pos n)]; simpa using ha⟩
  unfold gap; rw [dif_pos hex]; exact Nat.find_spec hex

/-- For an honest `x`, `dist C x` is its position in the segment of `prev C x`. -/
theorem dist_lt_gap (hC : C.Nonempty) {x : Fin n} (hx : x ∉ C) : dist C x < gap C (prev C x) := by
  apply lt_gap_of_forall _ (prev_mem hC x)
  intro s hs
  rcases eq_or_lt_of_le hs with rfl | hlt
  · rw [prev_add]; exact hx
  · have := not_mem_of_lt_dist hC (x := x) (t := dist C x - s - 1) (by omega)
    convert this using 1; simp only [prev]
    rw [show dist C x + 1 = (dist C x - s - 1 + 1) + (s + 1) by omega]; push_cast; ring

/-- For an adversary `x`, `dist C x` is the length of the segment of `prev C x`. -/
theorem gap_prev (hC : C.Nonempty) {x : Fin n} (hx : x ∈ C) : gap C (prev C x) = dist C x := by
  classical
  have hp := prev_mem hC x
  apply le_antisymm
  · unfold gap
    rw [dif_pos ⟨dist C x, by rw [prev_add]; exact hx⟩]
    exact Nat.find_min' _ (by rw [prev_add]; exact hx)
  · by_contra hlt; push_neg at hlt
    have h1 := gap_mem hp
    have h2 := not_mem_of_lt_dist hC (x := x) (t := dist C x - gap C (prev C x) - 1) (by omega)
    apply h2
    have hpx : prev C x = x - ((dist C x + 1 : ℕ) : Fin n) := rfl
    generalize gap C (prev C x) = g at h1 hlt h2 ⊢
    rw [hpx] at h1
    obtain ⟨r, hr⟩ : ∃ r, dist C x = r + g + 1 := ⟨dist C x - g - 1, by omega⟩
    rw [hr] at h1 ⊢
    convert h1 using 1
    rw [show r + g + 1 - g - 1 = r by omega]
    push_cast; ring

end Prev

/-! ### Walking backwards around the ring -/

section Back

variable (C : Finset (Fin n))

/-- The honest processors among `a - 1, a - 2, …, a - N`, in this order. -/
def backPos (a : Fin n) (N : ℕ) : List (Fin n) :=
  ((List.range N).map fun t => a - ((t + 1 : ℕ) : Fin n)).filter (· ∉ C)

variable {C}

theorem backPos_zero (a : Fin n) : backPos C a 0 = [] := by simp [backPos]

theorem backPos_add (a : Fin n) (N N' : ℕ) :
    backPos C a (N + N') = backPos C a N ++ backPos C (a - (N : Fin n)) N' := by
  unfold backPos
  rw [List.range_add, List.map_append, List.filter_append, List.map_map]
  congr 3
  funext t
  simp only [Function.comp_apply]
  push_cast; ring

theorem backPos_one_of_mem {a : Fin n} (h : a - 1 ∈ C) : backPos C a 1 = [] := by
  simp [backPos, h]

theorem backPos_of_forall {a : Fin n} {N : ℕ} (h : ∀ t < N, a - ((t + 1 : ℕ) : Fin n) ∉ C) :
    backPos C a N = (List.range N).map fun t => a - ((t + 1 : ℕ) : Fin n) := by
  unfold backPos
  rw [List.filter_eq_self]
  intro x hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  simpa using h t ht

theorem backPos_length (hC : C.Nonempty) {a : Fin n} (ha : a ∈ C) :
    (backPos C a (n - 1)).length = n - C.card := by
  classical
  set L := (List.range (n - 1)).map fun t => a - ((t + 1 : ℕ) : Fin n)
  have hnd : L.Nodup := by
    apply List.Nodup.map_on _ (List.nodup_range)
    intro x hx y hy hxy
    simp only [List.mem_range] at hx hy
    have := cast_succ_inj (n := n) (s := x + 1) (s' := y + 1) (by omega) (by omega)
      (by simpa using hxy)
    omega
  have hmem : ∀ x, x ∈ L ↔ x ≠ a := by
    intro x
    simp only [L, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨t, ht, rfl⟩ h
      have := cast_succ_inj (n := n) (s := t + 1) (s' := 0) (by omega) (NeZero.pos n)
        (by simpa using h)
      omega
    · intro hx
      have hpos : 0 < (a - x : Fin n).val := by
        rw [Nat.pos_iff_ne_zero, Ne, Fin.val_eq_zero_iff, sub_eq_zero]; exact fun h => hx h.symm
      refine ⟨(a - x : Fin n).val - 1, by have := (a - x : Fin n).isLt; omega, ?_⟩
      rw [Nat.sub_add_cancel hpos, Fin.cast_val_eq_self, sub_sub_cancel]
  have h1 : (backPos C a (n - 1)).length = ((Finset.univ.erase a).filter (· ∉ C)).card := by
    have hb : backPos C a (n - 1) = L.filter (fun x => decide (x ∉ C)) := rfl
    rw [hb, ← List.toFinset_card_of_nodup (hnd.filter _)]
    congr 1
    ext x
    simp only [List.mem_toFinset, List.mem_filter, hmem x, Finset.mem_filter, Finset.mem_erase,
      Finset.mem_univ, decide_eq_true_eq, and_true]
  rw [h1]
  have : (Finset.univ.erase a).filter (· ∉ C) = Finset.univ.filter (· ∉ C) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ]
    constructor
    · rintro ⟨⟨-, -⟩, h⟩; exact ⟨trivial, h⟩
    · rintro ⟨-, h⟩; exact ⟨⟨fun h' => h (h' ▸ ha), trivial⟩, h⟩
  rw [this, Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  simp

/-- The adversary after the segment of `a`. -/
noncomputable def next (C : Finset (Fin n)) (a : Fin n) : Fin n := a + ((gap C a + 1 : ℕ) : Fin n)

theorem backPos_seg {a : Fin n} (ha : a ∈ C) :
    backPos C (next C a) (gap C a) = (List.range (gap C a)).map
      fun t => a + ((gap C a - t : ℕ) : Fin n) := by
  rw [backPos_of_forall]
  · apply List.map_congr_left
    intro t ht
    simp only [List.mem_range] at ht
    simp only [next]
    rw [show gap C a + 1 = (gap C a - t) + (t + 1) by omega]
    push_cast; ring
  · intro t ht
    have := not_mem_of_lt_gap ha (s := gap C a - t - 1) (by omega)
    convert this using 1
    simp only [next]
    rw [show gap C a + 1 = (gap C a - t - 1 + 1) + (t + 1) by omega]
    push_cast; ring

theorem sub_cast_eq_next {a : Fin n} (h : gap C a + 2 ≤ n) :
    a - ((n - 2 - gap C a + 1 : ℕ) : Fin n) = next C a := by
  have h1 : ((n - 2 - gap C a + 1 : ℕ) : Fin n) + ((gap C a + 1 : ℕ) : Fin n) = 0 := by
    rw [← Nat.cast_add, show n - 2 - gap C a + 1 + (gap C a + 1) = n by omega, Fin.natCast_self]
  simp only [next]
  linear_combination (-1 : Fin n) * h1

/-- Walking back from an adversary `a`: first the processors before `a` up to `next C a`
(exclusive), then the segment of `a` (from its end). -/
theorem backPos_split₁ {a : Fin n} (ha : a ∈ C) :
    backPos C a (n - 1) = backPos C a (n - 2 - gap C a) ++ backPos C (next C a) (gap C a) := by
  have hg := gap_lt ha
  rcases Nat.lt_or_ge (gap C a) (n - 1) with hlt | hge
  · rw [show n - 1 = (n - 2 - gap C a) + 1 + gap C a by omega, backPos_add, backPos_add,
      backPos_one_of_mem, List.append_nil]
    · have key := sub_cast_eq_next (C := C) (a := a) (by omega)
      push_cast at key
      congr 1
      rw [← key]; congr 1; push_cast; ring
    · have key := sub_cast_eq_next (C := C) (a := a) (by omega)
      push_cast at key
      rw [sub_sub, key]; exact gap_mem ha
  · have hgap : gap C a = n - 1 := by omega
    have hnext : next C a = a := by
      simp only [next, hgap, Nat.sub_add_cancel (NeZero.pos n), Fin.natCast_self, add_zero]
    rw [hnext, hgap, show n - 2 - (n - 1) = 0 by omega, backPos_zero, List.nil_append]

/-- Walking back from `next C a`: first the segment of `a`, then from `a` on. -/
theorem backPos_split₂ {a : Fin n} (ha : a ∈ C) :
    backPos C (next C a) (n - 1) =
      backPos C (next C a) (gap C a) ++ backPos C a (n - 2 - gap C a) := by
  have hg := gap_lt ha
  rcases Nat.lt_or_ge (gap C a) (n - 1) with hlt | hge
  · rw [show n - 1 = gap C a + 1 + (n - 2 - gap C a) by omega, backPos_add, backPos_add,
      backPos_one_of_mem]
    · rw [List.append_nil]; congr 1; simp only [next]; push_cast; ring
    · simp only [next]; push_cast; ring_nf; exact ha
  · have hgap : gap C a = n - 1 := by omega
    have hnext : next C a = a := by
      simp only [next, hgap, Nat.sub_add_cancel (NeZero.pos n), Fin.natCast_self, add_zero]
    rw [hnext, hgap, show n - 2 - (n - 1) = 0 by omega, backPos_zero, List.append_nil]

end Back

/-! ### The rushing attacker -/

section Attacker

/-- The messages sent by a rushing attacker after receiving `h` (`|h| ≤ H`, `H` = number of honest
processors): the first `F` incoming messages, then (once `F` messages arrived) `z` zeros, then
(once `H` messages arrived) the compensating message, `n - F - z - 1 - l` zeros and the last `l`
incoming messages. -/
def rushSend (H F z l : ℕ) (w : Fin n) (h : List (Fin n)) : List (Fin n) :=
  h.take F ++ (if F ≤ h.length then List.replicate z 0 else []) ++
    (if H ≤ h.length then
      (w - (h.take F).sum - (h.drop (H - l)).sum) ::
        (List.replicate (n - F - z - 1 - l) 0 ++ h.drop (H - l))
     else [])

theorem rushSend_snoc (H F z l : ℕ) (w : Fin n) {h : List (Fin n)} (hh : h.length < H)
    (m : Fin n) : rushSend H F z l w h <+: rushSend H F z l w (h ++ [m]) := by
  unfold rushSend
  rw [if_neg (by omega : ¬ H ≤ h.length), List.append_nil]
  by_cases hF : F ≤ h.length
  · rw [List.take_append_of_le_length hF, if_pos hF, if_pos (by simp; omega)]
    exact List.prefix_append _ _
  · rw [if_neg hF, List.append_nil, List.take_of_length_le (by omega)]
    refine List.IsPrefix.trans ?_ (List.prefix_append _ _)
    refine List.IsPrefix.trans ?_ (List.prefix_append _ _)
    rw [List.take_append, List.take_of_length_le (by omega)]
    exact List.prefix_append _ _

/-- The rushing attacker (adversary strategy of Lemma 4.1 and of the Cubic Attack). It terminates
with output `w` after `H` incoming messages. -/
def rushing (H F z l : ℕ) (w : Fin n) : Proc (Fin n) (Option (Fin n)) where
  sent h := rushSend H F z l w (h.take H)
  sent_snoc h m := by
    by_cases hh : h.length < H
    · rw [List.take_of_length_le (by omega), List.take_of_length_le (by simp; omega)]
      exact rushSend_snoc H F z l w hh m
    · rw [List.take_append_of_le_length (by omega)]
  out h := if H ≤ h.length then some (some w) else none

theorem rushSend_length (H F z l : ℕ) (w : Fin n) (h : List (Fin n)) :
    (rushSend H F z l w h).length = min h.length F + (if F ≤ h.length then z else 0) +
      (if H ≤ h.length then 1 + (n - F - z - 1 - l) + (h.length - (H - l)) else 0) := by
  unfold rushSend
  simp only [List.length_append, List.length_take]
  split_ifs <;> simp <;> omega

theorem rushSend_full {H F z l : ℕ} (w : Fin n) {h : List (Fin n)} (hh : h.length = H)
    (hF : F ≤ H) (hl : H - l ≤ F) (hb : F + z + 1 + l ≤ n) (hlH : l ≤ H) :
    rushSend H F z l w h = h.take F ++ List.replicate z 0 ++
      ((w - (h.take F).sum - (h.drop (H - l)).sum) ::
        (List.replicate (n - F - z - 1 - l) 0 ++ h.drop (H - l))) := by
  unfold rushSend
  rw [if_pos (by omega), if_pos (by omega)]

end Attacker

/-! ### The attack -/

section Attack

variable (C : Finset (Fin n)) (F z : Fin n → ℕ) (w : Fin n) (d : Fin n → Fin n)

/-- The adversary profile of the rushing attack with parameters `F`, `z`, electing `w`. -/
noncomputable def rushProfile : Profile n (Fin n) :=
  fun a => rushing (n - C.card) (F a) (z a) (gap C a) w

/-- The honest secrets in the order in which an adversary `a` receives them. -/
def incoming (a : Fin n) : List (Fin n) := (backPos C a (n - 1)).map d

/-- The secrets of the segment of `a`, from its end. -/
noncomputable def secs (a : Fin n) : List (Fin n) := (backPos C (next C a) (gap C a)).map d

/-- The messages an adversary sends in the attack. -/
noncomputable def outMsgs (a : Fin n) : List (Fin n) :=
  rushSend (n - C.card) (F a) (z a) (gap C a) w (incoming C d a)

/-- Candidate final configuration of the attack. -/
noncomputable def finalCfg : Config n (Fin n) := fun j =>
  open Classical in
  if j ∈ C then incoming C d j
  else seg (outMsgs C F z w d (prev C j)) (segSecret d (prev C j)) (dist C j)

variable {C F z w d}

/-- Hypotheses on the parameters (content and budget). -/
structure Params (C : Finset (Fin n)) (F z : Fin n → ℕ) : Prop where
  F_le : ∀ a ∈ C, F a ≤ n - C.card
  le_F : ∀ a ∈ C, n - C.card - gap C a ≤ F a
  budget : ∀ a ∈ C, F a + z a + 1 + gap C a ≤ n

theorem gap_le_honest (hC : C.Nonempty) {a : Fin n} (ha : a ∈ C) : gap C a ≤ n - C.card := by
  have h1 := backPos_length hC ha
  rw [backPos_split₁ ha, List.length_append, backPos_seg ha, List.length_map,
    List.length_range] at h1
  omega

theorem secs_length {a : Fin n} (ha : a ∈ C) : (secs C d a).length = gap C a := by
  simp [secs, backPos_seg ha]

theorem incoming_length (hC : C.Nonempty) {a : Fin n} (ha : a ∈ C) :
    (incoming C d a).length = n - C.card := by
  simp [incoming, backPos_length hC ha]

theorem incoming_split (hC : C.Nonempty) {a : Fin n} (ha : a ∈ C) :
    incoming C d a = (backPos C a (n - 2 - gap C a)).map d ++ secs C d a ∧
      ((backPos C a (n - 2 - gap C a)).map d).length = n - C.card - gap C a := by
  have h := incoming_length (d := d) hC ha
  have e : incoming C d a = (backPos C a (n - 2 - gap C a)).map d ++ secs C d a := by
    simp [incoming, secs, backPos_split₁ ha]
  refine ⟨e, ?_⟩
  rw [e, List.length_append, secs_length ha] at h
  omega

theorem incoming_next (hC : C.Nonempty) {a : Fin n} (ha : a ∈ C) :
    incoming C d (next C a) = secs C d a ++ (incoming C d a).take (n - C.card - gap C a) := by
  obtain ⟨e, hl⟩ := incoming_split (d := d) hC ha
  rw [e, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  simp [incoming, secs, backPos_split₂ ha]

theorem secs_getElem? {a : Fin n} (ha : a ∈ C) {s : ℕ} (hs : s < gap C a) :
    (secs C d a)[gap C a - 1 - s]? = some (segSecret d a s) := by
  simp only [secs, backPos_seg ha, List.getElem?_map, List.getElem?_range (by omega : gap C a - 1 - s < gap C a),
    Option.map_some, segSecret]
  congr 2
  rw [show gap C a - (gap C a - 1 - s) = s + 1 by omega]

theorem drop_incoming (hC : C.Nonempty) {a : Fin n} (ha : a ∈ C) :
    (incoming C d a).drop (n - C.card - gap C a) = secs C d a := by
  obtain ⟨e, hl⟩ := incoming_split (d := d) hC ha
  rw [e, ← hl, List.drop_left]

theorem outMsgs_eq (hC : C.Nonempty) (hp : Params C F z) {a : Fin n} (ha : a ∈ C) :
    outMsgs C F z w d a = (incoming C d a).take (F a) ++ List.replicate (z a) 0 ++
      ((w - ((incoming C d a).take (F a)).sum - (secs C d a).sum) ::
        (List.replicate (n - F a - z a - 1 - gap C a) 0 ++ secs C d a)) := by
  unfold outMsgs
  rw [rushSend_full w (incoming_length hC ha) (hp.F_le a ha) (hp.le_F a ha) (hp.budget a ha)
    (gap_le_honest hC ha), drop_incoming hC ha]

theorem outMsgs_length (hC : C.Nonempty) (hp : Params C F z) {a : Fin n} (ha : a ∈ C) :
    (outMsgs C F z w d a).length = n := by
  rw [outMsgs_eq hC hp ha]
  have := hp.F_le a ha; have := hp.budget a ha
  simp [secs_length ha, incoming_length hC ha]
  omega

theorem outMsgs_sum (hC : C.Nonempty) (hp : Params C F z) {a : Fin n} (ha : a ∈ C) :
    (outMsgs C F z w d a).sum = w := by
  rw [outMsgs_eq hC hp ha]
  simp only [List.sum_append, List.sum_cons, List.sum_replicate, smul_zero, zero_add, add_zero]
  ring

theorem take_incoming_prefix (hC : C.Nonempty) (hp : Params C F z) {a : Fin n} (ha : a ∈ C) :
    (incoming C d a).take (n - C.card - gap C a) <+: outMsgs C F z w d a := by
  rw [outMsgs_eq hC hp ha]
  refine List.IsPrefix.trans ?_ (List.prefix_append _ _)
  refine List.IsPrefix.trans ?_ (List.prefix_append _ _)
  exact List.take_prefix_take_left (hp.le_F a ha)

theorem outMsgs_getElem? (hC : C.Nonempty) (hp : Params C F z) {a : Fin n} (ha : a ∈ C) {s : ℕ}
    (hs : s < gap C a) : (outMsgs C F z w d a)[n - 1 - s]? = some (segSecret d a s) := by
  have hlen := outMsgs_length (w := w) (d := d) hC hp ha
  set P := (incoming C d a).take (F a) ++ List.replicate (z a) 0 ++
      ((w - ((incoming C d a).take (F a)).sum - (secs C d a).sum) ::
        List.replicate (n - F a - z a - 1 - gap C a) 0)
  have e : outMsgs C F z w d a = P ++ secs C d a := by rw [outMsgs_eq hC hp ha]; simp [P]
  have hP : P.length = n - gap C a := by
    rw [e, List.length_append, secs_length ha] at hlen; omega
  rw [← secs_getElem? ha hs, e, List.getElem?_append_right (by omega), hP]
  congr 1; have := gap_lt ha; omega

/-- The segment lists in closed form. -/
theorem seg_eq {m : List (Fin n)} {e : ℕ → Fin n} (hm : n ≤ m.length) {s : ℕ} (hs : s ≤ n) :
    seg m e s = ((List.range s).map e).reverse ++ m.take (n - s) := by
  induction s with
  | zero => simp [seg]
  | succ s ih =>
    rw [seg, ih (by omega), List.take_cons (NeZero.pos n), List.take_append,
      List.take_of_length_le (by simp; omega), List.take_take, List.range_succ, List.map_append,
      List.reverse_append]
    simp only [List.length_reverse, List.length_map, List.length_range, List.map_cons,
      List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    congr 3
    omega

theorem secs_eq (hC : C.Nonempty) {a : Fin n} (ha : a ∈ C) :
    secs C d a = ((List.range (gap C a)).map (segSecret d a)).reverse := by
  apply List.ext_getElem?
  intro t
  by_cases ht : t < gap C a
  · have := secs_getElem? (d := d) ha (s := gap C a - 1 - t) (by omega)
    rw [show gap C a - 1 - (gap C a - 1 - t) = t by omega] at this
    rw [this, List.getElem?_reverse (by simpa using ht)]
    simp only [List.length_map, List.length_range, List.getElem?_map,
      List.getElem?_range (show gap C a - 1 - t < gap C a by omega), Option.map_some]
  · rw [List.getElem?_eq_none (by rw [secs_length ha]; omega),
      List.getElem?_eq_none (by simp; omega)]

theorem prev_dist_pred (hC : C.Nonempty) {j : Fin n} {s : ℕ} (h : dist C j = s + 1) :
    j - 1 ∉ C ∧ dist C (j - 1) = s ∧ prev C (j - 1) = prev C j := by
  have h1 := dist_succ hC (j - 1)
  have h2 := prev_succ hC (j - 1)
  rw [sub_add_cancel] at h1 h2
  have hj : j - 1 ∉ C := by intro hm; rw [if_pos hm] at h1; omega
  rw [if_neg hj] at h1 h2
  exact ⟨hj, by omega, h2.symm⟩

theorem prev_eq_pred (hC : C.Nonempty) {j : Fin n} (h : dist C j = 0) : prev C j = j - 1 := by
  simp [prev, h]

theorem next_prev (hC : C.Nonempty) {j : Fin n} (hj : j ∈ C) : next C (prev C j) = j := by
  rw [next, gap_prev hC hj, prev_add]

variable (C F z w d) in
/-- The adversary profile of the attack (abbreviation). -/
noncomputable abbrev atk : Profile n (Fin n) := dev C (rushProfile C F z w) d

theorem atk_sent_adv (hC : C.Nonempty) {a : Fin n} (ha : a ∈ C) :
    (atk C F z w d a).sent (incoming C d a) = outMsgs C F z w d a := by
  simp only [atk, dev_adv ha, rushProfile, rushing, outMsgs]
  rw [List.take_of_length_le (by rw [incoming_length hC ha])]

theorem atk_honest {j : Fin n} (hj : j ∉ C) : atk C F z w d j = aLead d j := dev_honest hj

theorem atk_adv {j : Fin n} (hj : j ∈ C) :
    atk C F z w d j = rushing (n - C.card) (F j) (z j) (gap C j) w := dev_adv hj

theorem finalCfg_adv {j : Fin n} (hj : j ∈ C) : finalCfg C F z w d j = incoming C d j := by
  simp [finalCfg, hj]

theorem finalCfg_honest {j : Fin n} (hj : j ∉ C) : finalCfg C F z w d j =
    seg (outMsgs C F z w d (prev C j)) (segSecret d (prev C j)) (dist C j) := by
  simp [finalCfg, hj]

theorem seg_prefix_inbox (hC : C.Nonempty) (hp : Params C F z) (j : Fin n) :
    seg (outMsgs C F z w d (prev C j)) (segSecret d (prev C j)) (dist C j) <+:
      inbox (atk C F z w d) (finalCfg C F z w d) j := by
  have hb := prev_mem hC j
  rcases hd : dist C j with _ | s
  · have e := prev_eq_pred hC hd
    rw [inbox, ← e, finalCfg_adv hb, atk_sent_adv hC hb]
    exact List.take_prefix _ _
  · obtain ⟨hj1, hds, hps⟩ := prev_dist_pred hC hd
    have hm := outMsgs_length (w := w) (d := d) hC hp hb
    rw [inbox, finalCfg_honest hj1, hds, hps, atk_honest hj1,
      aLead_sent_full d _ (seg_length hm.ge s)]
    have : segSecret d (prev C j) s = d (j - 1) := by
      simp only [segSecret]; congr 1
      have := prev_add (C := C) j; rw [hd] at this
      push_cast at this ⊢; linear_combination this
    rw [seg, this]

theorem finalCfg_consistent (hC : C.Nonempty) (hp : Params C F z) (j : Fin n) :
    finalCfg C F z w d j <+: inbox (atk C F z w d) (finalCfg C F z w d) j := by
  refine List.IsPrefix.trans ?_ (seg_prefix_inbox hC hp j)
  by_cases hj : j ∈ C
  · have hb := prev_mem hC j
    have hO := outMsgs_length (w := w) (d := d) hC hp hb
    rw [finalCfg_adv hj, ← next_prev hC hj, incoming_next hC hb, next_prev hC hj,
      ← gap_prev hC hj, seg_eq hO.ge (by have := gap_lt hb; omega), ← secs_eq hC hb]
    rw [List.prefix_append_right_inj]
    refine List.prefix_take_iff.mpr ⟨take_incoming_prefix hC hp hb, ?_⟩
    simp only [List.length_take]
    have := gap_le_honest hC hb
    omega
  · rw [finalCfg_honest hj]

theorem ring_induction {f : Fin n → Prop} {x : Fin n} (hx : f x) (h : ∀ j, f (j - 1) → f j)
    (j : Fin n) : f j := by
  have key : ∀ t : ℕ, f (x + (t : Fin n)) := by
    intro t
    induction t with
    | zero => simpa using hx
    | succ t ih =>
      apply h
      have e : x + ((t + 1 : ℕ) : Fin n) - 1 = x + (t : Fin n) := by push_cast; ring
      rw [e]; exact ih
  have := key (j - x : Fin n).val
  simpa using this

theorem prev_next (hC : C.Nonempty) {a : Fin n} (ha : a ∈ C) : prev C (next C a) = a := by
  have hd : dist C (next C a) = gap C a := by
    rw [dist_eq_iff hC]
    refine ⟨by simp [next, ha], fun t' ht' => ?_⟩
    have := not_mem_of_lt_gap ha (s := gap C a - t' - 1) (by omega)
    convert this using 1
    simp only [next]
    rw [show gap C a + 1 = (gap C a - t' - 1 + 1) + (t' + 1) by omega]
    push_cast; ring
  rw [prev, hd, next]; push_cast; ring

theorem next_mem {a : Fin n} (ha : a ∈ C) : next C a ∈ C := gap_mem ha

/-- Liveness conditions of the rushing attack. -/
structure Live (C : Finset (Fin n)) (F z : Fin n → ℕ) : Prop where
  star : ∃ a ∈ C, n - C.card ≤ F a + z a ∧
    ∀ j ∈ C, prev C j ≠ a → F j ≤ F (prev C j) + z (prev C j)

theorem finalCfg_out (hC : C.Nonempty) (hp : Params C F z) (j : Fin n) (p : List (Fin n))
    (x : Fin n) (hpx : p ++ [x] <+: finalCfg C F z w d j) : (atk C F z w d j).out p = none := by
  have hl := hpx.length_le
  simp only [List.length_append, List.length_singleton] at hl
  by_cases hj : j ∈ C
  · rw [finalCfg_adv hj, incoming_length hC hj] at hl
    rw [atk_adv hj]; simp [rushing]; omega
  · rw [finalCfg_honest hj, seg_length (outMsgs_length hC hp (prev_mem hC j)).ge] at hl
    rw [atk_honest hj, aLead_out]; exact validate_eq_none (by omega)

theorem finalCfg_length (hC : C.Nonempty) (hp : Params C F z) (j : Fin n) :
    (finalCfg C F z w d j).length = if j ∈ C then n - C.card else n := by
  split_ifs with hj
  · rw [finalCfg_adv hj, incoming_length hC hj]
  · rw [finalCfg_honest hj, seg_length (outMsgs_length hC hp (prev_mem hC j)).ge]

/-- **The rushing attack terminates** (generalizes Lemma 4.4): the candidate final configuration is
reachable. -/
theorem reach_finalCfg (hC : C.Nonempty) (h0 : (0 : Fin n) ∉ C) (hp : Params C F z)
    (hl : Live C F z) : Reach (atk C F z w d) (finalCfg C F z w d) := by
  classical
  set X := finalCfg C F z w d
  set P := atk C F z w d
  set H := n - C.card
  obtain ⟨c, hc, hcX, hst⟩ := exists_reach_le_of_consistent (P := P) X
    (finalCfg_consistent hC hp) (finalCfg_out hC hp)
  have hinv := hc.inv
  -- notation
  let r : Fin n → ℕ := fun j => (c j).length
  let cap : Fin n → ℕ := fun j => if j ∈ C then H else n
  let ι : Fin n → ℕ := fun j => (inbox P c j).length
  have hcap : ∀ j, (X j).length = cap j := fun j => finalCfg_length hC hp j
  have hr_cap : ∀ j, r j ≤ cap j := fun j => (hcX j).length_le.trans (hcap j).le
  have hr_ι : ∀ j, r j ≤ ι j := fun j => (hinv j).1.length_le
  let Full : Fin n → Prop := fun j => r j = cap j
  have hfull_iff : ∀ j, Full j ↔ c j = X j := fun j =>
    ⟨fun h => (hcX j).eq_of_length (by rw [hcap]; exact h),
     fun h => by simp only [Full, r, h, hcap]⟩
  have hst' : ∀ j, Full j ∨ r j = ι j := by
    intro j
    rcases hst j with h | h
    · exact Or.inl ((hfull_iff j).mpr h)
    · exact Or.inr (le_antisymm (hr_ι j) h)
  have hfull_of : ∀ j, cap j ≤ ι j → Full j := by
    intro j h
    rcases hst' j with h' | h'
    · exact h'
    · exact le_antisymm (hr_cap j) (h' ▸ h)
  -- the lengths of what processors send
  have hr_le_H : ∀ a ∈ C, r a ≤ H := fun a ha => by
    have := hr_cap a; simp only [cap, if_pos ha] at this; exact this
  have hι_adv : ∀ j, j - 1 ∈ C → ι j = (rushSend H (F (j - 1)) (z (j - 1)) (gap C (j - 1)) w
      (c (j - 1))).length := by
    intro j hj
    simp only [ι, inbox, P, atk_adv hj, rushing]
    rw [List.take_of_length_le (hr_le_H _ hj)]
  have hι_hon : ∀ j, j - 1 ∉ C → min (r (j - 1)) n ≤ ι j ∧
      (j - 1 = 0 → min (r (j - 1) + 1) n ≤ ι j) := by
    intro j hj
    have := aLead_sent_length d (j - 1) (c (j - 1))
    simp only [ι, inbox, P, atk_honest hj]
    exact ⟨this.1, this.2.2⟩
  -- (a) fullness propagates
  have hprop : ∀ j, Full (j - 1) → Full j := by
    intro j hj
    apply hfull_of
    have hcapn : cap j ≤ n := by simp only [cap]; split_ifs <;> omega
    by_cases hj1 : j - 1 ∈ C
    · rw [hι_adv j hj1, rushSend_length]
      have h1 : r (j - 1) = H := by simpa [Full, cap, hj1] using hj
      have := hp.budget _ hj1; have := hp.F_le _ hj1; have := gap_le_honest hC hj1
      simp only [r] at h1
      rw [h1, if_pos (hp.F_le _ hj1), if_pos le_rfl]
      omega
    · have h1 : r (j - 1) = n := by simpa [Full, cap, hj1] using hj
      have := (hι_hon j hj1).1; rw [h1, min_self] at this; omega
  by_cases hex : ∃ j, Full j
  · obtain ⟨x, hx⟩ := hex
    have hall := ring_induction hx hprop
    have : c = X := funext fun j => (hfull_iff j).mp (hall j)
    rw [← this]; exact hc
  exfalso
  push_neg at hex
  -- (b) the predicate `Q`
  let G : Fin n → ℕ := fun a => F a + z a
  let Q : Fin n → Prop := fun j => if j ∈ C then F j ≤ r j else G (prev C j) ≤ r j
  obtain ⟨as, has, hasH, hL1⟩ := hl.star
  -- lower bound on the next processor from a lower bound `G b ≤ (what j receives)`
  have hfinish : ∀ j, G (prev C j) ≤ r j ∨ Full j → Q j ∧ (j ∈ C → prev C j ≠ as) := by
    intro j h
    rcases h with h | h
    · by_cases hj : j ∈ C
      · by_cases hpj : prev C j = as
        · exfalso; apply hex j
          apply le_antisymm (hr_cap j)
          simp only [cap, if_pos hj]; rw [hpj] at h; exact hasH.trans h
        · exact ⟨by simp only [Q, if_pos hj]; exact (hL1 j hj hpj).trans h, fun _ => hpj⟩
      · exact ⟨by simp only [Q, if_neg hj]; exact h, fun h' => absurd h' hj⟩
    · exact absurd h (hex j)
  have hstep : ∀ j, Q (j - 1) → Q j ∧ (j ∈ C → prev C j ≠ as) := by
    intro j hq
    apply hfinish
    by_cases hj1 : j - 1 ∈ C
    · have hpj : prev C j = j - 1 := by
        have := prev_succ hC (j - 1); rw [sub_add_cancel, if_pos hj1] at this; exact this
      have hq' : F (j - 1) ≤ r (j - 1) := by simpa [Q, hj1] using hq
      have hlt : r (j - 1) < H := by
        rcases lt_or_eq_of_le (hr_le_H _ hj1) with h | h
        · exact h
        · exact absurd (by simp [Full, cap, hj1, h]) (hex (j - 1))
      rcases hst' j with h | h
      · exact Or.inr h
      · left
        rw [h, hι_adv j hj1, rushSend_length, hpj]
        simp only [r] at hq' hlt
        rw [if_pos hq', if_neg (by omega)]
        simp only [G]; omega
    · have hpj : prev C j = prev C (j - 1) := by
        have := prev_succ hC (j - 1); rw [sub_add_cancel, if_neg hj1] at this; exact this
      have hq' : G (prev C (j - 1)) ≤ r (j - 1) := by simpa [Q, hj1] using hq
      have hrn : r (j - 1) ≤ n := by simpa [cap, hj1] using hr_cap (j - 1)
      rcases hst' j with h | h
      · exact Or.inr h
      · left
        rw [hpj, h]
        have := (hι_hon j hj1).1
        rw [min_eq_left hrn] at this
        omega
  by_cases hQ : ∃ j, Q j
  · obtain ⟨x, hx⟩ := hQ
    have hall : ∀ j, Q j := ring_induction hx (fun j h => (hstep j h).1)
    have := (hstep (next C as) (hall _)).2 (next_mem has)
    exact this (prev_next hC has)
  push_neg at hQ
  -- (c) no `Q` anywhere: the lengths do not decrease along the ring, and grow after the origin
  have hpipe : ∀ j, r (j - 1) + (if j - 1 = 0 then 1 else 0) ≤ r j := by
    intro j
    rcases hst' j with h | h
    · exact absurd h (hex j)
    rw [h]
    by_cases hj1 : j - 1 ∈ C
    · have hq : r (j - 1) < F (j - 1) := by
        have := hQ (j - 1); simp only [Q, if_pos hj1] at this; omega
      have hne : j - 1 ≠ 0 := fun h' => h0 (h' ▸ hj1)
      rw [if_neg hne, hι_adv j hj1, rushSend_length]
      have := hp.F_le _ hj1
      simp only [r] at hq ⊢
      split_ifs <;> omega
    · have hrn : r (j - 1) < n := by
        have := hr_cap (j - 1); simp only [cap, if_neg hj1] at this
        rcases lt_or_eq_of_le this with h' | h'
        · exact h'
        · exact absurd (by simp [Full, cap, hj1, h']) (hex (j - 1))
      have h1 := hι_hon j hj1
      split_ifs with h0'
      · have := h1.2 h0'; omega
      · have := h1.1; omega
  have hconst := ring_const r (fun j => le_trans (Nat.le_add_right _ _) (hpipe j))
  have := hpipe 1
  simp only [sub_self, if_true] at this
  have := hconst 1 0
  omega

/-- **The rushing attack forces the outcome `w`** (Lemma 4.1 and Theorem 4.3 are instances):
if the origin is honest and the parameters satisfy the content, budget and liveness conditions,
then for every choice of the honest secrets all processors terminate with output `w`. -/
theorem rushing_outcome (hC : C.Nonempty) (h0 : (0 : Fin n) ∉ C) (hp : Params C F z)
    (hl : Live C F z) (d : Fin n → Fin n) : outcome (atk C F z w d) = some w := by
  have hR := reach_finalCfg (w := w) (d := d) hC h0 hp hl
  rw [outcome_eq_some]
  intro j
  by_cases hj : j ∈ C
  · refine ⟨_, hR, ?_⟩
    rw [atk_adv hj, finalCfg_adv hj]
    have := Finset.card_le_univ C; simp only [Fintype.card_fin] at this
    simp [rushing, incoming_length hC hj]
    omega
  · have := (lemma_3_3 (A := rushProfile C F z w) (d := d) hC w).mpr ⟨_, hR, fun a ha _ => ?_⟩
    · exact this j hj
    have hsent : (rushProfile C F z w a).sent (finalCfg C F z w d a) = outMsgs C F z w d a := by
      rw [finalCfg_adv ha]
      simp only [rushProfile, rushing, outMsgs]
      rw [List.take_of_length_le (by rw [incoming_length hC ha])]
    have hlen := outMsgs_length (w := w) (d := d) hC hp ha
    refine ⟨by rw [hsent, hlen], ?_, fun s hs => ?_⟩
    · rw [hsent, List.take_of_length_le hlen.le, outMsgs_sum hC hp ha]
    · rw [hsent]; exact outMsgs_getElem? hC hp ha hs

end Attack

end Podc.FairLeaderElection
