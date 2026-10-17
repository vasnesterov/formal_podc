import Papers.PODC2026.TreeAA.Spec
import Podc.Foundations.Count

/-!
# The 3-round gradecast of Ben-Or, Dolev and Hoch  -- CSLib candidate

Theorem 4 of the paper cites [Ben-Or, Dolev, Hoch, *Simple gradecast based algorithms*, 2010,
Theorem 1]: gradecast (Definition 4, `Gradecast`) is achievable for `t < n/3` Byzantine parties in
3 synchronous rounds without signatures. We implement the protocol in CSLib's lock-step model on
the complete network and verify it (`bdhGradecast_solves`).

Protocol `bdhGradecast t snd` (the history length is the current round number):
* round 0: the sender sends its input `v` to everybody;
* round 1: everybody echoes the value it received from the sender (the sender echoes `v`);
* round 2: a party that saw some `w` echoed by at least `n - t` parties (counting its own echo)
  sends `w` ("ready"), otherwise nothing;
* after round 2 (history of length 3): if some `w` has `≥ n - t` readies (counting its own), output
  `(w, 2)`; else if some `w` has `≥ t + 1` readies, output `(w, 1)`; else output `(x, 0)` (`x` is
  the own input, a dummy value).

A party does not receive its own messages on `⊤`; the counts use `gcView`, which inserts the own
message into the inbox.
-/

namespace TreeAA

open Cslib.Byzantine.LockStep

section BDH

variable {P : Type} [Fintype P] [DecidableEq P] {W : Type} [DecidableEq W]

/-! ### Local computations -/

/-- The number of parties `q` with `c q = some w`. -/
def gcCount (c : P → Option W) (w : W) : ℕ := Finset.univ.countEq c (some w)

/-- The inbox `ib` of `p`, completed with `p`'s own message `own`. -/
def gcView (p : P) (own : Option W) (ib : Inbox P W) : P → Option W :=
  fun q => if q = p then own else ib q

open Classical in
/-- The ready message: a value with at least `n - t` echoes. -/
noncomputable def gcReady (t : ℕ) (c : P → Option W) : Option W :=
  if h : ∃ w, Fintype.card P - t ≤ gcCount c w then some h.choose else none

open Classical in
/-- The output: grade 2 for a value with `≥ n - t` readies, grade 1 for one with `≥ t + 1`
readies, otherwise the dummy value `x` with grade 0. -/
noncomputable def gcGrade (t : ℕ) (x : W) (c : P → Option W) : W × Fin 3 :=
  if h : ∃ w, Fintype.card P - t ≤ gcCount c w then (h.choose, 2)
  else if h : ∃ w, t + 1 ≤ gcCount c w then (h.choose, 1) else (x, 0)

/-- The message of `p` (to everybody) after history `h`. -/
noncomputable def gcMsg (t : ℕ) (snd p : P) (x : W) : History P W → Option W
  | [] => if p = snd then some x else none
  | [ib₀] => if p = snd then some x else ib₀ snd
  | [ib₀, ib₁] => gcReady t (gcView p (if p = snd then some x else ib₀ snd) ib₁)
  | _ => none

/-- The 3-round gradecast of Ben-Or, Dolev and Hoch with sender `snd`, for `t` faults. -/
noncomputable def bdhGradecast (t : ℕ) (snd : P) : Protocol P W W (W × Fin 3) where
  send p x h _ := gcMsg t snd p x h
  decide p x h := match h with
    | [ib₀, ib₁, ib₂] => some (gcGrade t x (gcView p (gcMsg t snd p x [ib₀, ib₁]) ib₂))
    | _ => none

/-! ### Counting -/

section Counting

variable {B : Set P} {t : ℕ}

omit [DecidableEq P] in
open Classical in
/-- At least `n - t` supporters, hence at least `n - 2t` supporters outside `B`; they are seen by
everybody who agrees with `c` outside `B`. -/
lemma gcCount_transfer (hB : B.ncard ≤ t) {c c' : P → Option W}
    (hcc : ∀ q, q ∉ B → c q = c' q) {w : W} (h : Fintype.card P - t ≤ gcCount c w) :
    Fintype.card P - 2 * t ≤ gcCount c' w := by
  unfold gcCount Finset.countEq at *
  set S := Finset.univ.filter fun q => c q = some w
  have h1 := Finset.card_filter_add_card_filter_not (s := S) (· ∈ B)
  have h2 := Finset.card_filter_mem_le_ncard B S
  have h3 : (S.filter fun q => q ∉ B).card ≤ (Finset.univ.filter fun q => c' q = some w).card := by
    apply Finset.card_le_card
    intro q hq
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [← hcc q hq.2]; exact hq.1
  omega

omit [DecidableEq P] in
open Classical in
lemma gcCount_of_forall (hB : B.ncard ≤ t) {c : P → Option W} {w : W}
    (h : ∀ q, q ∉ B → c q = some w) : Fintype.card P - t ≤ gcCount c w := by
  unfold gcCount Finset.countEq
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset P)) (· ∈ B)
  have h2 := Finset.card_filter_mem_le_ncard B Finset.univ
  have h3 : (Finset.univ.filter fun q => q ∉ B).card ≤
      (Finset.univ.filter fun q => c q = some w).card :=
    Finset.card_le_card fun q hq => by simp at hq ⊢; exact h q hq
  rw [Finset.card_univ] at h1
  omega

omit [DecidableEq P] in
lemma eq_of_gcCount (ht : 3 * t < Fintype.card P) {c : P → Option W} {w w' : W}
    (h : Fintype.card P - t ≤ gcCount c w) (h' : Fintype.card P - t ≤ gcCount c w') : w = w' :=
  Option.some_injective _ <| Finset.eq_of_card_lt_countEq_add_countEq (s := .univ) (f := c) <| by
    rw [Finset.card_univ]; unfold gcCount at h h'; omega

omit [DecidableEq P] in
lemma gcReady_spec {c : P → Option W} {w : W} (h : gcReady t c = some w) :
    Fintype.card P - t ≤ gcCount c w := by
  unfold gcReady at h
  split_ifs at h with h0
  cases h
  exact h0.choose_spec

omit [DecidableEq P] in
lemma gcReady_eq (ht : 3 * t < Fintype.card P) {c : P → Option W} {w : W}
    (h : Fintype.card P - t ≤ gcCount c w) : gcReady t c = some w := by
  have h0 : ∃ w, Fintype.card P - t ≤ gcCount c w := ⟨w, h⟩
  unfold gcReady
  rw [dite_eq_left_of_eq_true (eq_true h0), eq_of_gcCount ht h0.choose_spec h]

omit [DecidableEq P] in
lemma gcGrade_eq (ht : 3 * t < Fintype.card P) (x : W) {c : P → Option W} {w : W}
    (h : Fintype.card P - t ≤ gcCount c w) : gcGrade t x c = (w, 2) := by
  have h0 : ∃ w, Fintype.card P - t ≤ gcCount c w := ⟨w, h⟩
  unfold gcGrade
  rw [dite_eq_left_of_eq_true (eq_true h0), eq_of_gcCount ht h0.choose_spec h]

omit [DecidableEq P] in
lemma gcGrade_two {x : W} {c : P → Option W} (h : (gcGrade t x c).2 = 2) :
    Fintype.card P - t ≤ gcCount c (gcGrade t x c).1 := by
  unfold gcGrade at *
  split_ifs at * with h0 h1
  · exact h0.choose_spec
  · simp at h
  · simp at h

omit [DecidableEq P] in
lemma gcGrade_pos (ht : 3 * t < Fintype.card P) {x : W} {c : P → Option W}
    (h : 0 < (gcGrade t x c).2) : t + 1 ≤ gcCount c (gcGrade t x c).1 := by
  unfold gcGrade at *
  split_ifs at * with h0 h1
  · have := h0.choose_spec; show t + 1 ≤ gcCount c h0.choose; omega
  · exact h1.choose_spec
  · simp at h

omit [DecidableEq P] in
lemma gcGrade_pos_of {x : W} {c : P → Option W} {w : W} (h : t + 1 ≤ gcCount c w) :
    0 < (gcGrade t x c).2 := by
  unfold gcGrade
  split_ifs with h0 h1
  · simp
  · simp
  · exact absurd ⟨w, h⟩ h1

end Counting

/-! ### Runs -/

section Runs

variable {t : ℕ} {snd : P} (s : Scenario P W W)

/-- The inbox of `p` in round `r`. -/
noncomputable abbrev gcIb (t : ℕ) (snd : P) (r : ℕ) (p : P) : Inbox P W :=
  fun q => deliver ⊤ (bdhGradecast t snd) s (hist ⊤ (bdhGradecast t snd) s r) r q p

/-- What `p` sees in round `r`, its own message included. -/
noncomputable abbrev gcC (t : ℕ) (snd : P) (r : ℕ) (p : P) : P → Option W :=
  gcView p (gcMsg t snd p (s.input p) (hist ⊤ (bdhGradecast t snd) s r p)) (gcIb s t snd r p)

lemma gc_hist_one (p : P) : hist ⊤ (bdhGradecast t snd) s 1 p = [gcIb s t snd 0 p] := by
  simp [hist_succ]

lemma gc_hist_two (p : P) :
    hist ⊤ (bdhGradecast t snd) s 2 p = [gcIb s t snd 0 p, gcIb s t snd 1 p] := by
  rw [hist_succ, gc_hist_one]; rfl

lemma gc_hist_three (p : P) : hist ⊤ (bdhGradecast t snd) s 3 p =
    [gcIb s t snd 0 p, gcIb s t snd 1 p, gcIb s t snd 2 p] := by
  rw [hist_succ, gc_hist_two]; rfl

lemma gc_msg_two (p : P) :
    gcMsg t snd p (s.input p) (hist ⊤ (bdhGradecast t snd) s 2 p) = gcReady t (gcC s t snd 1 p) := by
  rw [gc_hist_two, gcC, gc_hist_one]; rfl

lemma gc_status_three (p : P) :
    status ⊤ (bdhGradecast t snd) s 3 p = some (gcGrade t (s.input p) (gcC s t snd 2 p)) := by
  simp only [status, gc_hist_three, gcC, gc_hist_two]; rfl

lemma gc_decide_none (p : P) (x : W) (l : History P W) (hl : l.length ≠ 3) :
    (bdhGradecast t snd).decide p x l = none := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> first | rfl | simp at hl

lemma gc_decides_iff (p : P) (o : W × Fin 3) :
    Decides ⊤ (bdhGradecast t snd) s p o ↔ o = gcGrade t (s.input p) (gcC s t snd 2 p) := by
  have hd : Decides ⊤ (bdhGradecast t snd) s p (gcGrade t (s.input p) (gcC s t snd 2 p)) :=
    ⟨3, gc_status_three s p, fun r hr => gc_decide_none p _ _ (by simp; omega)⟩
  exact ⟨fun h => Decides.unique _ _ h hd, fun h => h ▸ hd⟩

variable {s}

/-- An honest party sees exactly the protocol message of every honest party. -/
lemma gcC_honest (hrel : s.Reliable) (r : ℕ) {p q : P} (hp : p ∉ s.byz) (hq : q ∉ s.byz) :
    gcC s t snd r p q = gcMsg t snd q (s.input q) (hist ⊤ (bdhGradecast t snd) s r q) := by
  by_cases hqp : q = p
  · subst hqp; simp [gcC, gcView]
  · simp [gcC, gcView, gcIb, deliver, hqp, hq, hrel r q p, bdhGradecast]

end Runs

/-! ### Correctness -/

/-- **Theorem 4** (Theorem 1 of Ben-Or–Dolev–Hoch): the 3-round protocol `bdhGradecast`
achieves gradecast (Definition 4) against `t < n/3` Byzantine parties on the complete network,
without signatures; every honest party decides at round 3. -/
theorem bdhGradecast_solves {t : ℕ} (ht : 3 * t < Fintype.card P) (snd : P) :
    SolvesAuthWithin ⊤ (bdhGradecast t snd) (Auth.none P W) (atMost t) noPre (Gradecast snd) 3 := by
  intro s hB hrel _ _
  have hB : s.byz.ncard ≤ t := hB
  -- honest views agree on honest parties
  have hagree : ∀ r p p', p ∉ s.byz → p' ∉ s.byz → ∀ q, q ∉ s.byz →
      gcC s t snd r p q = gcC s t snd r p' q := fun r p p' hp hp' q hq => by
    rw [gcC_honest hrel r hp hq, gcC_honest hrel r hp' hq]
  -- honest readies are consistent
  have hready : ∀ q q' w w', q ∉ s.byz → q' ∉ s.byz →
      gcMsg t snd q (s.input q) (hist ⊤ (bdhGradecast t snd) s 2 q) = some w →
      gcMsg t snd q' (s.input q') (hist ⊤ (bdhGradecast t snd) s 2 q') = some w' → w = w' := by
    intro q q' w w' hq hq' h h'
    rw [gc_msg_two] at h h'
    have h1 := gcReady_spec h
    have h2 := gcReady_spec h'
    unfold gcCount Finset.countEq at h1 h2
    obtain ⟨u, hu, hu', hub⟩ := Finset.exists_mem_inter_notMem_of_ncard_le hB (by omega :
      Fintype.card P + t < (Finset.univ.filter fun u => gcC s t snd 1 q u = some w).card +
      (Finset.univ.filter fun u => gcC s t snd 1 q' u = some w').card)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hu'
    rw [hagree 1 q q' hq hq' u hub, hu'] at hu
    exact (Option.some_injective _ hu).symm
  -- `t + 1` readies of `w` include an honest one
  have hready' : ∀ p w, p ∉ s.byz → t + 1 ≤ gcCount (gcC s t snd 2 p) w →
      ∃ q, q ∉ s.byz ∧
        gcMsg t snd q (s.input q) (hist ⊤ (bdhGradecast t snd) s 2 q) = some w := by
    intro p w hp h
    obtain ⟨u, hu, hub⟩ := Finset.exists_mem_notMem_of_ncard_le_of_lt hB
      (s := {u | gcC s t snd 2 p u = some w}) (by unfold gcCount Finset.countEq at h; omega)
    exact ⟨u, hub, by rw [← gcC_honest hrel 2 hp hub]; exact (Finset.mem_filter.1 hu).2⟩
  refine ⟨⟨fun p _ => ⟨_, (gc_decides_iff s p _).2 rfl⟩, ?_, ?_⟩, ?_⟩
  · -- integrity
    intro hsnd p hp
    rw [gc_decides_iff]
    have hecho : ∀ q, q ∉ s.byz →
        gcMsg t snd q (s.input q) (hist ⊤ (bdhGradecast t snd) s 1 q) = some (s.input snd) := by
      intro q hq
      by_cases hqs : q = snd
      · subst hqs; rw [gc_hist_one]; simp [gcMsg]
      · have := gcC_honest (t := t) (snd := snd) hrel 0 hq hsnd
        simp only [gcC, gcView, Ne.symm hqs, ↓reduceIte, hist_zero] at this
        rw [gc_hist_one]; simp only [gcMsg, hqs, ↓reduceIte, this]
    have hrd : ∀ q, q ∉ s.byz →
        gcMsg t snd q (s.input q) (hist ⊤ (bdhGradecast t snd) s 2 q) = some (s.input snd) := by
      intro q hq
      rw [gc_msg_two]
      exact gcReady_eq ht (gcCount_of_forall hB fun u hu => by
        rw [gcC_honest hrel 1 hq hu]; exact hecho u hu)
    exact (gcGrade_eq ht _ (gcCount_of_forall hB fun u hu => by
      rw [gcC_honest hrel 2 hp hu]; exact hrd u hu)).symm
  · -- consistency
    intro p hp q hq v w g g' h1 h2
    rw [gc_decides_iff] at h1 h2
    have hp' : p ∉ s.byz := hp
    have hq' : q ∉ s.byz := hq
    constructor
    · by_cases hg : g = 2
      · have hc := gcGrade_two (show (gcGrade t (s.input p) (gcC s t snd 2 p)).2 = 2 by
          rw [← h1]; exact hg)
        have hc' := gcCount_transfer hB (hagree 2 p q hp' hq') hc
        have := gcGrade_pos_of (t := t) (x := s.input q) (c := gcC s t snd 2 q) (w := (gcGrade t (s.input p) (gcC s t snd 2 p)).1) (by omega)
        rw [← h2] at this
        simp only at this
        omega
      · have := g.isLt
        have : (g : ℕ) ≠ 2 := fun h => hg (Fin.ext h)
        omega
    · intro hg hg'
      have c1 := gcGrade_pos ht (show 0 < (gcGrade t (s.input p) (gcC s t snd 2 p)).2 by
        rw [← h1]; exact hg)
      have c2 := gcGrade_pos ht (show 0 < (gcGrade t (s.input q) (gcC s t snd 2 q)).2 by
        rw [← h2]; exact hg')
      rw [← h1] at c1
      rw [← h2] at c2
      obtain ⟨a, ha, ha'⟩ := hready' p v hp' c1
      obtain ⟨b, hb, hb'⟩ := hready' q w hq' c2
      exact hready a b v w ha hb ha' hb'
  · -- termination
    intro p _
    exact ⟨3, le_rfl, _, gc_status_three s p⟩

end BDH

end TreeAA
