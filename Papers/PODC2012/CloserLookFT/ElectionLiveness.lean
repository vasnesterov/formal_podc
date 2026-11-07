import Papers.PODC2012.CloserLookFT.Election
import Podc.Computability.Distributed.SharedMemory.Resilience
import Cslib.Foundations.Data.Nat.Descent

/-!
# Liveness of the election algorithm: Theorems 2.2 and 2.5 (almost-wait-freedom)

For every infinite execution `e` of `electionImpl L` (crashes are processes that stop taking
steps while an operation is pending, see `Resilience.lean`; participation is not required):

* `starved_unique` (**Theorem 2.5**, second part): at most one correct participating process does
  not terminate — whatever the number of crashes;
* `not_starved_of_no_crash` (**Theorem 2.5**, first part): without crashes every participating
  process terminates;
* `exists_ret_true_of_no_crash` (**Theorem 2.2**): without crashes, if some process participates,
  some process returns `1`;
* `electionImpl_almostWaitFree`: hence the algorithm is almost-wait-free (for any number of
  levels `L`; safety needs `n ≤ 2^L`, see `election_safety`).

The proofs follow the paper: a started process that is not the last one to have written `turn`
("doomed") returns within a bounded number of its own steps (measure `dm`); `turn` changes only
when a process starts, so it eventually stays constant; without crashes all doomed processes
return, clean up their entries of `V`, and the last process to write `turn` is never blocked
again (measure `yMeasure`).
-/

namespace Podc.CloserLookFT

open Cslib.SharedMemory Cslib.SharedMemory.Impl

variable {P : Type} [DecidableEq P]

/-! ### A ghost-free invariant -/

/-- Simple invariant of reachable states. -/
structure SInv (s : ESys P) : Prop where
  clrTurn : ∀ x k b j, (s.loc x = .clr k b j ∨ s.loc x = .clw k b j) → s.m.turn ≠ some x
  doneOut : s.m.done = true → ∃ x a w c, s.loc x = .out true a w c
  outDone : ∀ x a w c, s.loc x = .out true a w c → s.m.done = true
  outFalse : ∀ x a w c, s.loc x = .out false a w c → c < w → s.m.done = true

lemma SInv.init : SInv (ESys.init P) := by
  constructor <;> simp [ESys.init, EMem.init]

lemma SInv.invoke {s : ESys P} (h : SInv s) (p : P) : SInv (s.invoke p) := by
  unfold ESys.invoke
  split_ifs with hp
  swap; · exact h
  have hne : ∀ x l, s.loc x = l → l ≠ .idle → x ≠ p := fun x l hx hl hxp => by
    subst hxp; rw [hp] at hx; exact hl hx.symm
  constructor
  · intro x k b j hx
    have : x ≠ p := by
      rcases hx with hx | hx <;> intro hxp <;> subst hxp <;> simp at hx
    exact h.clrTurn x k b j (by simpa [this] using hx)
  · intro hd
    obtain ⟨x, a, w, c, hx⟩ := h.doneOut hd
    exact ⟨x, a, w, c, by simp [hne x _ hx (by simp), hx]⟩
  · intro x a w c hx
    have : x ≠ p := by intro hxp; subst hxp; simp at hx
    exact h.outDone x a w c (by simpa [this] using hx)
  · intro x a w c hx
    have : x ≠ p := by intro hxp; subst hxp; simp at hx
    exact h.outFalse x a w c (by simpa [this] using hx)

lemma nextClr_cases (k b j : ℕ) :
    (nextClr k b j = .clr k b j) ∨ nextClr k b j = .out false k b b := by
  unfold nextClr; split_ifs <;> simp

lemma estep_clr {L : ℕ} {p : P} {m : EMem P} {l : ELoc} {k b j : ℕ}
    (h : (estep L p m l).2 = .clr k b j ∨ (estep L p m l).2 = .clw k b j) :
    ((∃ k b j, l = .clr k b j ∨ l = .clw k b j) ∨ m.turn ≠ some p) ∧
      (estep L p m l).1.turn = m.turn := by
  cases l with
  | rturn k' =>
    simp only [estep] at h ⊢
    split_ifs at h with h1
    · simp at h
    · exact ⟨Or.inr h1, trivial⟩
  | rturn2 k' =>
    simp only [estep] at h ⊢
    split_ifs at h with h1 h2 <;> try simp at h
    · exact ⟨Or.inr h1, trivial⟩
  | clr k' b' j' => exact ⟨Or.inl ⟨k', b', j', Or.inl rfl⟩, by simp [estep]⟩
  | clw k' b' j' => exact ⟨Or.inl ⟨k', b', j', Or.inr rfl⟩, by simp [estep]⟩
  | rdone k' =>
    simp only [estep] at h; split_ifs at h <;> simp at h
  | rv k' =>
    simp only [estep] at h; split_ifs at h <;> simp at h
  | start => simp only [estep] at h; split_ifs at h <;> simp at h
  | _ => simp [estep] at h

lemma estep_outTrue {L : ℕ} {p : P} {m : EMem P} {l : ELoc} {a w c : ℕ}
    (h : (estep L p m l).2 = .out true a w c) :
    (estep L p m l).1.done = true ∨ (l = .out true a w c ∧ (estep L p m l).1 = m) := by
  cases l with
  | wdone => left; simp [estep]
  | out r a' w' c' => right; simp only [estep] at h ⊢; exact ⟨h, trivial⟩
  | rturn k' =>
    simp only [estep] at h; split_ifs at h <;> rcases nextClr_cases k' k' 0 with e | e <;>
      simp_all
  | rturn2 k' =>
    simp only [estep] at h; split_ifs at h <;> (try simp at h) <;>
      rcases nextClr_cases k' (k' + 1) 0 with e | e <;> simp_all
  | clr k' b' j' =>
    simp only [estep] at h; split_ifs at h <;> (try simp at h) <;>
      rcases nextClr_cases k' b' (j' + 1) with e | e <;> simp_all
  | clw k' b' j' =>
    simp only [estep] at h; rcases nextClr_cases k' b' (j' + 1) with e | e <;> simp_all
  | rdone k' => simp only [estep] at h; split_ifs at h <;> simp at h
  | rv k' => simp only [estep] at h; split_ifs at h <;> simp at h
  | start => simp only [estep] at h; split_ifs at h <;> simp at h
  | _ => simp [estep] at h

lemma estep_outFalse {L : ℕ} {p : P} {m : EMem P} {l : ELoc} {a w c : ℕ}
    (h : (estep L p m l).2 = .out false a w c) (hcw : c < w) :
    (m.done = true ∧ (estep L p m l).1 = m) ∨ (l = .out false a w c ∧ (estep L p m l).1 = m) := by
  cases l with
  | out r a' w' c' => right; simp only [estep] at h ⊢; exact ⟨h, trivial⟩
  | rdone k' =>
    simp only [estep] at h ⊢; split_ifs at h with h1
    exact Or.inl ⟨h1, trivial⟩
  | rturn k' =>
    simp only [estep] at h; split_ifs at h <;> rcases nextClr_cases k' k' 0 with e | e <;>
      simp_all <;> omega
  | rturn2 k' =>
    simp only [estep] at h; split_ifs at h <;> (try simp at h) <;>
      rcases nextClr_cases k' (k' + 1) 0 with e | e <;> simp_all <;> omega
  | clr k' b' j' =>
    simp only [estep] at h; split_ifs at h <;> (try simp at h) <;>
      rcases nextClr_cases k' b' (j' + 1) with e | e <;> simp_all <;> omega
  | clw k' b' j' =>
    simp only [estep] at h; rcases nextClr_cases k' b' (j' + 1) with e | e <;> simp_all <;> omega
  | rv k' => simp only [estep] at h; split_ifs at h <;> simp at h
  | start => simp only [estep] at h; split_ifs at h <;> simp at h
  | _ => simp [estep] at h

lemma SInv.step {L : ℕ} {s : ESys P} (h : SInv s) (p : P) : SInv (s.step L p) := by
  -- other processes keep their local state; `done` is never reset
  have hother : ∀ x, x ≠ p → (s.step L p).loc x = s.loc x := fun x hx => by
    simp [ESys.step, hx]
  have hdone : s.m.done = true → (s.step L p).m.done = true := fun hd => by
    simp only [ESys.step]; cases s.loc p <;> simp [estep, hd]
  have hturn : ∀ x, x ≠ p → (s.step L p).m.turn = some x → s.m.turn = some x := fun x hx ht => by
    simp only [ESys.step] at ht
    cases hl : s.loc p <;> simp [estep, hl] at ht <;> first | exact ht | exact absurd ht.symm hx
  have hlocp : (s.step L p).loc p = (estep L p s.m (s.loc p)).2 := by simp [ESys.step]
  constructor
  · intro x k b j hx
    by_cases hxp : x = p
    · subst hxp
      rw [hlocp] at hx
      obtain ⟨h1 | h1, h2⟩ := estep_clr hx
      · obtain ⟨k', b', j', h1⟩ := h1
        simp only [ESys.step, h2]
        exact h.clrTurn x k' b' j' h1
      · simpa [ESys.step, h2] using h1
    · intro ht
      exact h.clrTurn x k b j (by simpa [hother x hxp] using hx) (hturn x hxp ht)
  · intro hd
    by_cases hd0 : s.m.done = true
    · obtain ⟨x, a, w, c, hx⟩ := h.doneOut hd0
      by_cases hxp : x = p
      · subst hxp; exact ⟨x, a, w, c, by simp [ESys.step, hx, estep]⟩
      · exact ⟨x, a, w, c, by rw [hother x hxp]; exact hx⟩
    · refine ⟨p, L, L, 0, ?_⟩
      simp only [ESys.step, Function.update_self]
      simp only [ESys.step] at hd
      cases hl : s.loc p <;> simp only [estep, hl] at hd ⊢ <;> simp_all
  · intro x a w c hx
    by_cases hxp : x = p
    · subst hxp
      rw [hlocp] at hx
      rcases estep_outTrue hx with h1 | ⟨h1, h2⟩
      · exact h1
      · simp only [ESys.step, h2]; exact h.outDone x a w c h1
    · exact hdone (h.outDone x a w c (by rwa [hother x hxp] at hx))
  · intro x a w c hx hcw
    by_cases hxp : x = p
    · subst hxp
      rw [hlocp] at hx
      rcases estep_outFalse hx hcw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [ESys.step, h2]; exact h1
      · simp only [ESys.step, h2]; exact h.outFalse x a w c h1 hcw
    · exact hdone (h.outFalse x a w c (by rwa [hother x hxp] at hx) hcw)

theorem EReach.sInv {L : ℕ} {s : ESys P} (hs : EReach L s) : SInv s := by
  induction hs with
  | init => exact SInv.init
  | step p _ ih => exact ih.step p
  | invoke p _ ih => exact ih.invoke p

/-! ### Facts about single steps -/

lemma estep_ne_idle {L : ℕ} {p : P} {m : EMem P} {l : ELoc} (h : l ≠ .idle) :
    (estep L p m l).2 ≠ .idle := by
  cases l <;> simp only [estep] <;> (try split_ifs) <;> simp_all [nextClr] <;>
    (try split_ifs) <;> simp

lemma estep_started {L : ℕ} {p : P} {m : EMem P} {l : ELoc} (h : l.Started) :
    (estep L p m l).2.Started := by
  obtain ⟨h1, h2⟩ := h
  cases l <;> simp_all only [estep, ne_eq, not_true_eq_false] <;> (try split_ifs) <;>
    simp [ELoc.Started, nextClr] <;> (try split_ifs) <;> simp

lemma estep_out {L : ℕ} {p : P} {m : EMem P} {r : Bool} {a w c : ℕ} :
    estep L p m (.out r a w c) = (m, .out r a w c) := rfl

/-- `turn` only changes when a process executes line 1. -/
lemma estep_turn {L : ℕ} {p x : P} {m : EMem P} {l : ELoc}
    (h : (estep L p m l).1.turn = some x) : m.turn = some x ∨ (l = .start ∧ x = p) := by
  cases l <;> simp only [estep] at h <;> (try exact Or.inl h)
  simp at h; exact Or.inr ⟨rfl, h.symm⟩

/-- The doomed measure: decreases at every step of a started process that is not the last one
to have written `turn`. -/
def dm : ELoc → ℕ
  | .idle | .start => 0
  | .rdone k => 2 * k + 2
  | .rturn k => 2 * k + 1
  | .rv k => 2 * k + 5
  | .wv k => 2 * k + 4
  | .rturn2 k => 2 * k + 3
  | .clr _ b j => 2 * (b - j)
  | .clw _ b j => 2 * (b - j) - 1
  | .wdone => 1
  | .out .. => 0

lemma dm_nextClr (k b j : ℕ) (hj : j ≤ b) : dm (nextClr k b j) ≤ 2 * (b - j) := by
  unfold nextClr; split_ifs <;> simp [dm]

lemma dm_step {L : ℕ} {p : P} {m : EMem P} {l : ELoc} (hst : l.Started) (hwf : l.WF L)
    (hout : ∀ r a w c, l ≠ .out r a w c) (ht : m.turn ≠ some p) :
    dm (estep L p m l).2 < dm l := by
  obtain ⟨h1, h2⟩ := hst
  cases l with
  | idle => exact absurd rfl h1
  | start => exact absurd rfl h2
  | out r a w c => exact absurd rfl (hout r a w c)
  | rdone k => simp only [estep, dm]; split_ifs <;> simp [dm]
  | rturn k =>
    simp only [estep, ht, ite_false]
    have := dm_nextClr k k 0 (by omega)
    have h0 : dm (.rturn k) = 2 * k + 1 := rfl
    omega
  | rv k => simp only [estep, dm]; split_ifs <;> simp [dm]
  | wv k => simp [estep, dm]
  | rturn2 k =>
    simp only [estep, ht, ite_false]
    have := dm_nextClr k (k + 1) 0 (by omega)
    have h0 : dm (.rturn2 k) = 2 * k + 3 := rfl
    omega
  | clr k b j =>
    simp only [ELoc.WF] at hwf
    have h0 : dm (.clr k b j) = 2 * (b - j) := rfl
    simp only [estep]; split_ifs
    · rw [h0]; simp [dm]; omega
    · have := dm_nextClr k b (j + 1) (by omega); omega
  | clw k b j =>
    simp only [ELoc.WF] at hwf
    have h0 : dm (.clw k b j) = 2 * (b - j) - 1 := rfl
    simp only [estep]
    have := dm_nextClr k b (j + 1) (by omega); omega
  | wdone => simp [estep, dm]


/-! ### The last process to write `turn` makes progress once it is alone -/

/-- Progress measure of the last process to write `turn` while `done = 0`. -/
def fY (L : ℕ) : ELoc → ℕ
  | .rdone k => 5 * (L - k) + 1
  | .rturn k => 5 * (L - k)
  | .rv k => 5 * (L - k) - 1
  | .wv k => 5 * (L - k) - 2
  | .rturn2 k => 5 * (L - k) - 3
  | .wdone => 1
  | _ => 0

/-- Progress measure of the last process to write `turn` once `done = 1`. -/
def gY : ELoc → ℕ
  | .rdone _ => 1
  | .rturn _ => 5
  | .rv _ => 4
  | .wv _ => 3
  | .rturn2 _ => 2
  | .wdone => 1
  | _ => 0

/-- The combined measure. -/
def yMeasure (L : ℕ) (l : ELoc) (d : Bool) : ℕ := if d then gY l else 6 * (L + 1) + fY L l

/-- When every other process is idle or has returned and `done = 0`, the register `V[k]` read by
the last process to write `turn` at level `k` is `0`. -/
lemma V_eq_none_of_alone {L : ℕ} [Fintype P] {s : ESys P} {g : Ghost P} (h : Inv L s g)
    (hs : SInv s) {Y : P} (hoth : ∀ x, x ≠ Y → s.loc x = .idle ∨ ∃ r a w c, s.loc x = .out r a w c)
    (hd : s.m.done = false) {k : ℕ} (hY : (s.loc Y).written L ≤ k) : s.m.V k = none := by
  by_contra hv
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hv
  obtain ⟨h1, h2⟩ := h.hold k x hx
  by_cases hxY : x = Y
  · subst hxY; omega
  · rcases hoth x hxY with hi | ⟨r, a, w, c, ho⟩
    · rw [hi] at h2; simp [ELoc.written] at h2
    · cases r
      · rw [ho] at h1 h2; simp only [ELoc.lo, ELoc.written] at h1 h2
        have := hs.outFalse x a w c ho (by omega); simp_all
      · have := hs.outDone x a w c ho; simp_all

lemma y_step {L : ℕ} [Fintype P] {s : ESys P} {g : Ghost P} (h : Inv L s g) (hs : SInv s) {Y : P}
    (ht : s.m.turn = some Y)
    (hoth : ∀ x, x ≠ Y → s.loc x = .idle ∨ ∃ r a w c, s.loc x = .out r a w c)
    (hst : (s.loc Y).Started) (hout : ∀ r a w c, s.loc Y ≠ .out r a w c) :
    yMeasure L ((s.step L Y).loc Y) (s.step L Y).m.done < yMeasure L (s.loc Y) s.m.done := by
  have hwf := h.wf Y
  simp only [ESys.step, Function.update_self]
  cases hl : s.loc Y with
  | idle => rw [hl] at hst; simp [ELoc.Started] at hst
  | start => rw [hl] at hst; simp [ELoc.Started] at hst
  | out r a w c => exact absurd hl (hout r a w c)
  | clr k b j => exact absurd ht (hs.clrTurn Y k b j (Or.inl hl))
  | clw k b j => exact absurd ht (hs.clrTurn Y k b j (Or.inr hl))
  | rdone k =>
    rw [hl] at hwf; simp only [ELoc.WF] at hwf
    cases hd : s.m.done <;> simp [estep, hd, yMeasure, gY, fY]
  | rturn k =>
    rw [hl] at hwf; simp only [ELoc.WF] at hwf
    cases hd : s.m.done <;> simp [estep, ht, hd, yMeasure, gY, fY] <;> omega
  | rv k =>
    rw [hl] at hwf; simp only [ELoc.WF] at hwf
    cases hd : s.m.done
    · have hv := V_eq_none_of_alone h hs hoth hd (k := k) (by rw [hl]; simp [ELoc.written])
      simp [estep, hv, hd, yMeasure, fY]; omega
    · simp only [estep, hd, yMeasure, ite_true]; split_ifs <;> simp [gY]
  | wv k =>
    rw [hl] at hwf; simp only [ELoc.WF] at hwf
    cases hd : s.m.done <;> simp [estep, hd, yMeasure, gY, fY] <;> omega
  | rturn2 k =>
    rw [hl] at hwf; simp only [ELoc.WF] at hwf
    cases hd : s.m.done <;> simp only [estep, ht, hd, yMeasure, ite_true, Bool.false_eq_true,
      ite_false] <;> split_ifs <;> simp [gY, fY] <;> omega
  | wdone =>
    cases hd : s.m.done <;> simp [estep, hd, yMeasure, gY, fY]

/-- The only way for the last process to write `turn` to return `0`. -/
lemma estep_outFalse_turn {L : ℕ} {p : P} {m : EMem P} {l : ELoc} {a w c : ℕ}
    (h : (estep L p m l).2 = .out false a w c) (ht : m.turn = some p) :
    m.done = true ∨ l = .out false a w c ∨ (∃ k b j, l = .clr k b j ∨ l = .clw k b j) := by
  cases l with
  | out r a' w' c' => simp only [estep] at h; exact Or.inr (Or.inl h)
  | rdone k' =>
    simp only [estep] at h; split_ifs at h with h1
    exact Or.inl h1
  | rturn k' => simp only [estep, ht, ite_true] at h; simp at h
  | rturn2 k' => simp only [estep, ht, ite_true] at h; split_ifs at h <;> simp at h
  | clr k' b' j' => exact Or.inr (Or.inr ⟨k', b', j', Or.inl rfl⟩)
  | clw k' b' j' => exact Or.inr (Or.inr ⟨k', b', j', Or.inr rfl⟩)
  | rv k' => simp only [estep] at h; split_ifs at h <;> simp at h
  | start => simp only [estep] at h; split_ifs at h <;> simp at h
  | _ => simp [estep] at h

lemma estep_turn_eq {L : ℕ} {p : P} {m : EMem P} {l : ELoc} (h : l ≠ .start) :
    (estep L p m l).1.turn = m.turn := by
  cases l <;> simp_all [estep]

lemma estep_done_mono {L : ℕ} {p : P} {m : EMem P} {l : ELoc} (h : m.done = true) :
    (estep L p m l).1.done = true := by
  cases l <;> simp_all [estep]

/-! ### Reachable configurations of the implementation -/

/-- A process with a pending operation is not idle. -/
lemma pend_ne_idle {L : ℕ} {C : Config ElectObj (Regs P) P ELoc}
    (hC : (electionImpl (P := P) L).Reachable C) (p : P) (hp : C.pend p ≠ none) :
    C.loc p ≠ .idle := by
  obtain ⟨α, hα⟩ := hC
  revert p
  refine Impl.run_induction (Q := fun _ C => ∀ p, C.pend p ≠ none → C.loc p ≠ .idle)
    (by intro p hp; simp [Impl.initCfg, electionImpl] at hp) ?_ hα
  intro α C ℓ C' _ ih h p hp
  cases ℓ with
  | inv q o =>
    obtain ⟨-, -, hpend, hloc, -⟩ := Impl.step_inv h
    rw [hloc]
    by_cases hqp : q = p
    · subst hqp; simp only [Function.update_self, electionImpl]; split_ifs <;> simp_all
    · rw [hpend, Function.update_of_ne (Ne.symm hqp)] at hp
      rw [Function.update_of_ne (Ne.symm hqp)]; exact ih p hp
  | ret q r =>
    obtain ⟨-, hpend, -, l, -, hloc⟩ := Impl.step_ret h
    by_cases hqp : q = p
    · subst hqp; simp [hpend] at hp
    · rw [hpend, Function.update_of_ne (Ne.symm hqp)] at hp
      rw [hloc, Function.update_of_ne (Ne.symm hqp)]; exact ih p hp
  | tau q =>
    obtain ⟨e1, hq, hqi, -⟩ := toSys_step_tau h
    obtain ⟨-, hpend, -⟩ := Impl.step_tau h
    have hl := congrArg ESys.loc e1
    simp only [toSys] at hl
    rw [hl]
    by_cases hqp : q = p
    · subst hqp; simp only [ESys.step, Function.update_self]; exact estep_ne_idle hqi
    · rw [hpend] at hp; simp only [ESys.step, Function.update_of_ne (Ne.symm hqp)]
      exact ih p hp


/-- A process that is neither idle nor returned has a pending operation. -/
lemma pend_of_active {L : ℕ} {C : Config ElectObj (Regs P) P ELoc}
    (hC : (electionImpl (P := P) L).Reachable C) (p : P) (hi : C.loc p ≠ .idle)
    (ho : ∀ r a w c, C.loc p ≠ .out r a w c) : C.pend p ≠ none := by
  obtain ⟨α, hα⟩ := hC
  revert p
  refine Impl.run_induction (Q := fun _ C => ∀ p, C.loc p ≠ .idle →
      (∀ r a w c, C.loc p ≠ .out r a w c) → C.pend p ≠ none)
    (by intro p hp; simp [Impl.initCfg, electionImpl] at hp) ?_ hα
  intro α C ℓ C' _ ih h p hi ho
  cases ℓ with
  | inv q o =>
    obtain ⟨-, -, hpend, hloc, -⟩ := Impl.step_inv h
    rw [hloc] at hi ho
    by_cases hqp : q = p
    · subst hqp; simp [hpend]
    · rw [Function.update_of_ne (Ne.symm hqp)] at hi ho
      rw [hpend, Function.update_of_ne (Ne.symm hqp)]; exact ih p hi ho
  | ret q r =>
    obtain ⟨-, hpend, -, l, -, hloc⟩ := Impl.step_ret h
    have e1 := (toSys_step_ret h).1
    have hl : C'.loc = C.loc := congrArg ESys.loc e1
    rw [hl] at hi ho
    by_cases hqp : q = p
    · subst hqp
      rcases (toSys_step_ret h).2 with ⟨h1, -⟩ | ⟨a, w, c, h1⟩
      · exact absurd h1 hi
      · exact absurd h1 (ho r a w c)
    · rw [hpend, Function.update_of_ne (Ne.symm hqp)]; exact ih p hi ho
  | tau q =>
    obtain ⟨e1, hq, -, -⟩ := toSys_step_tau h
    obtain ⟨-, hpend, -⟩ := Impl.step_tau h
    rw [hpend]
    by_cases hqp : q = p
    · subst hqp; exact hq
    · have hl := congrArg ESys.loc e1
      simp only [toSys] at hl
      rw [hl] at hi ho
      simp only [ESys.step, Function.update_of_ne (Ne.symm hqp)] at hi ho
      exact ih p hi ho

/-- A process in local state `out true` without pending operation has returned `1`. -/
lemma ret_true_of_outTrue {L : ℕ} {α : List (Label P ElectObj)}
    {C : Config ElectObj (Regs P) P ELoc} (hα : (electionImpl (P := P) L).run α = some C)
    (p : P) {a w c : ℕ} (hl : C.loc p = .out true a w c) (hp : C.pend p = none) :
    Label.ret p true ∈ α := by
  revert p a w c
  refine Impl.run_induction (Q := fun α C => ∀ p a w c, C.loc p = .out true a w c →
      C.pend p = none → Label.ret p true ∈ α)
    (by intro p a w c hp; simp [Impl.initCfg, electionImpl] at hp) ?_ hα
  intro α C ℓ C' _ ih h p a w c hl hp
  cases ℓ with
  | inv q o =>
    obtain ⟨-, -, hpend, hloc, -⟩ := Impl.step_inv h
    by_cases hqp : q = p
    · subst hqp; simp [hpend] at hp
    · rw [hloc, Function.update_of_ne (Ne.symm hqp)] at hl
      rw [hpend, Function.update_of_ne (Ne.symm hqp)] at hp
      exact List.mem_append_left _ (ih p a w c hl hp)
  | ret q r =>
    have e1 := (toSys_step_ret h).1
    have hlc : C'.loc = C.loc := congrArg ESys.loc e1
    rw [hlc] at hl
    by_cases hqp : q = p
    · subst hqp
      rcases (toSys_step_ret h).2 with ⟨h1, -⟩ | ⟨a', w', c', h1⟩
      · rw [h1] at hl; cases hl
      · rw [h1] at hl; cases hl; simp
    · obtain ⟨-, hpend, -⟩ := Impl.step_ret h
      rw [hpend, Function.update_of_ne (Ne.symm hqp)] at hp
      exact List.mem_append_left _ (ih p a w c hl hp)
  | tau q =>
    obtain ⟨e1, hq, -, -⟩ := toSys_step_tau h
    obtain ⟨-, hpend, -⟩ := Impl.step_tau h
    rw [hpend] at hp
    by_cases hqp : q = p
    · subst hqp; exact absurd hp hq
    · have hlc := congrArg ESys.loc e1
      simp only [toSys] at hlc
      rw [hlc] at hl
      simp only [ESys.step, Function.update_of_ne (Ne.symm hqp)] at hl
      exact List.mem_append_left _ (ih p a w c hl hp)

section Exec

variable [Fintype P] {L : ℕ} (e : (electionImpl (P := P) L).InfExec)

/-- The state of the transition system at time `t`. -/
def esys (t : ℕ) : ESys P := toSys (e.cfg t)

omit [Fintype P] in
lemma sys_reach (t : ℕ) : EReach L (esys e t) := reach_toSys (e.reachable_cfg t)

omit [Fintype P] in
lemma loc_succ_of_ne {t : ℕ} {q : P} (h : (e.lbl t).proc ≠ q) :
    (e.cfg (t + 1)).loc q = (e.cfg t).loc q ∧ (e.cfg (t + 1)).pend q = (e.cfg t).pend q :=
  Impl.step_other (e.step_eq t) h

omit [Fintype P] in
/-- `sys` evolves by steps of the transition system. -/
lemma sys_succ (t : ℕ) : esys e (t + 1) = esys e t ∨ esys e (t + 1) = (esys e t).step L (e.lbl t).proc ∨
    esys e (t + 1) = (esys e t).invoke (e.lbl t).proc := by
  have h := e.step_eq t
  cases hl : e.lbl t with
  | inv p o => rw [hl] at h; exact Or.inr (Or.inr (toSys_step_inv h))
  | ret p r => rw [hl] at h; exact Or.inl (toSys_step_ret h).1
  | tau p => rw [hl] at h; exact Or.inr (Or.inl (toSys_step_tau h).1)

omit [Fintype P] in
/-- Generic persistence along an execution. -/
lemma persist (Q : ESys P → Prop) (hstep : ∀ s q, EReach L s → Q s → Q (s.step L q))
    (hinv : ∀ s q, Q s → Q (s.invoke q)) {t₀ : ℕ} (h : Q (esys e t₀)) :
    ∀ t ≥ t₀, Q (esys e t) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact h
  | succ t _ ih =>
    rcases sys_succ e t with e1 | e1 | e1 <;> rw [e1]
    · exact ih
    · exact hstep _ _ (sys_reach e t) ih
    · exact hinv _ _ ih

omit [Fintype P] in
lemma started_persist {p : P} {t₀ : ℕ} (h : ((esys e t₀).loc p).Started) :
    ∀ t ≥ t₀, ((esys e t).loc p).Started := by
  refine persist e (fun s => (s.loc p).Started) (fun s q _ hs => ?_) (fun s q hs => ?_) h
  · by_cases hq : q = p
    · subst hq; simpa [ESys.step] using estep_started hs
    · simpa [ESys.step, Function.update_of_ne (Ne.symm hq)] using hs
  · unfold ESys.invoke; split_ifs with hq
    · by_cases hqp : q = p
      · subst hqp; rw [hq] at hs; simp [ELoc.Started] at hs
      · simpa [Function.update_of_ne (Ne.symm hqp)] using hs
    · exact hs

omit [Fintype P] in
lemma doomed_persist {p : P} {t₀ : ℕ} (h : ((esys e t₀).loc p).Started)
    (ht : (esys e t₀).m.turn ≠ some p) :
    ∀ t ≥ t₀, ((esys e t).loc p).Started ∧ (esys e t).m.turn ≠ some p := by
  refine persist e (fun s => (s.loc p).Started ∧ s.m.turn ≠ some p) (fun s q _ hs => ?_)
    (fun s q hs => ?_) ⟨h, ht⟩
  · refine ⟨?_, fun h' => ?_⟩
    · by_cases hq : q = p
      · subst hq; simpa [ESys.step] using estep_started hs.1
      · simpa [ESys.step, Function.update_of_ne (Ne.symm hq)] using hs.1
    · rcases estep_turn h' with h1 | ⟨h1, rfl⟩
      · exact hs.2 h1
      · exact hs.1.2 h1
  · unfold ESys.invoke; split_ifs with hq
    · refine ⟨?_, hs.2⟩
      by_cases hqp : q = p
      · subst hqp; rw [hq] at hs; simp [ELoc.Started] at hs
      · simpa [Function.update_of_ne (Ne.symm hqp)] using hs.1
    · exact hs

omit [Fintype P] in
lemma out_persist {p : P} {t₀ : ℕ} {r : Bool} {a w c : ℕ}
    (h : (esys e t₀).loc p = .out r a w c) : ∀ t ≥ t₀, (esys e t).loc p = .out r a w c := by
  refine persist e (fun s => s.loc p = .out r a w c) (fun s q _ hs => ?_) (fun s q hs => ?_) h
  · by_cases hq : q = p
    · subst hq; simp [ESys.step, hs, estep]
    · simpa [ESys.step, Function.update_of_ne (Ne.symm hq)] using hs
  · unfold ESys.invoke; split_ifs with hq
    · by_cases hqp : q = p
      · subst hqp; rw [hq] at hs; cases hs
      · simpa [Function.update_of_ne (Ne.symm hqp)] using hs
    · exact hs

omit [Fintype P] in
/-- The first step of a non-crashed pending process is taken in its current local state. -/
lemma first_step {p : P} (hnc : ¬ e.Crashed p) {t : ℕ} (hp : (e.cfg t).pend p ≠ none) :
    ∃ t' ≥ t, (e.lbl t').proc = p ∧ (e.cfg t').loc p = (e.cfg t).loc p ∧
      (e.cfg t').pend p = (e.cfg t).pend p := by
  classical
  have hex : ∃ k, (e.lbl (t + k)).proc = p := by
    obtain ⟨t₁, ht₁, hq⟩ := InfExec.exists_step_of_not_crashed hnc hp
    exact ⟨t₁ - t, by rw [Nat.add_sub_cancel' ht₁]; exact hq⟩
  have hc := e.cfg_add_of_proc_ne fun j hj => Nat.find_min hex hj
  exact ⟨t + Nat.find hex, by omega, Nat.find_spec hex, hc.1, hc.2⟩

omit [Fintype P] in
/-- A pending process whose local state is not `out` takes a memory step (it cannot return). -/
lemma step_is_tau {p : P} {t : ℕ} (hp : (e.cfg t).pend p ≠ none) (hq : (e.lbl t).proc = p)
    (hout : ∀ r a w c, (e.cfg t).loc p ≠ .out r a w c) : e.lbl t = .tau p := by
  have h := e.step_eq t
  cases hl : e.lbl t with
  | inv q o =>
    rw [hl] at h hq; simp only [Label.proc] at hq; subst hq
    exact absurd (Impl.step_inv h).1 hp
  | ret q r =>
    rw [hl] at h hq; simp only [Label.proc] at hq; subst hq
    rcases (toSys_step_ret h).2 with ⟨h1, -⟩ | ⟨a, w, c, h1⟩
    · exact absurd h1 (pend_ne_idle (e.reachable_cfg t) q hp)
    · exact absurd h1 (hout r a w c)
  | tau q => rw [hl] at hq; simp only [Label.proc] at hq; rw [hq]

omit [Fintype P] in
/-- Descent: a non-crashed pending process whose measure decreases at each of its steps (and
does not increase otherwise) eventually reaches an `out` state. -/
lemma reach_out {p : P} (hnc : ¬ e.Crashed p) {t₀ : ℕ} (hp : (e.cfg t₀).pend p ≠ none)
    (μ : ℕ → ℕ)
    (hμ : ∀ t ≥ t₀, (e.cfg t).pend p ≠ none → (∀ r a w c, (e.cfg t).loc p ≠ .out r a w c) →
      (e.lbl t = .tau p → μ (t + 1) < μ t) ∧ ((e.lbl t).proc ≠ p → μ (t + 1) ≤ μ t)) :
    ∃ t ≥ t₀, ∃ r a w c, (e.cfg t).loc p = .out r a w c := by
  by_contra H
  push Not at H
  -- `p` stays pending
  have hpend : ∀ t ≥ t₀, (e.cfg t).pend p ≠ none := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hp
    | succ t ht ih =>
      by_cases hq : (e.lbl t).proc = p
      · have := step_is_tau e ih hq (H t ht)
        have h := e.step_eq t
        rw [this] at h
        rw [(Impl.step_tau h).2.1]; exact ih
      · rw [(loc_succ_of_ne e hq).2]; exact ih
  have hmono : ∀ t ≥ t₀, μ (t + 1) ≤ μ t := fun t ht => by
    by_cases hq : (e.lbl t).proc = p
    · exact ((hμ t ht (hpend t ht) (H t ht)).1 (step_is_tau e (hpend t ht) hq (H t ht))).le
    · exact (hμ t ht (hpend t ht) (H t ht)).2 hq
  obtain ⟨T, hT, hc⟩ := Nat.eventually_not_of_succ_le hmono
    (p := fun t => (e.lbl t).proc = p) fun t ht hq =>
      (hμ t ht (hpend t ht) (H t ht)).1 (step_is_tau e (hpend t ht) hq (H t ht))
  obtain ⟨t', ht', hq⟩ := InfExec.exists_step_of_not_crashed hnc (hpend T hT)
  exact hc t' ht' hq

omit [Fintype P] in
/-- A non-crashed process that reaches an `out` state is not blocked. -/
lemma not_blocked_of_out {p : P} (hnc : ¬ e.Crashed p) {t₁ : ℕ} {r : Bool} {a w c : ℕ}
    (h1 : (e.cfg t₁).loc p = .out r a w c) : ¬ e.Blocked p := by
  rintro ⟨T, hT⟩
  obtain ⟨t', ht', hq⟩ := InfExec.exists_step_of_not_crashed hnc (hT (max T t₁) (le_max_left _ _))
  have hout : (e.cfg t').loc p = .out r a w c :=
    out_persist e (t₀ := t₁) h1 t' (le_trans (le_max_right _ _) ht')
  have hp := hT t' (le_trans (le_max_left _ _) ht')
  have h := e.step_eq t'
  cases hl : e.lbl t' with
  | inv q o =>
    rw [hl] at h hq; simp only [Label.proc] at hq; subst hq
    exact hp (Impl.step_inv h).1
  | ret q r' =>
    rw [hl] at h hq; simp only [Label.proc] at hq; subst hq
    exact hT (t' + 1) (by have := le_trans (le_max_left T t₁) ht'; omega) (by
      rw [(Impl.step_ret h).2.1]; simp)
  | tau q =>
    rw [hl] at h hq; simp only [Label.proc] at hq; subst hq
    exact (toSys_step_tau h).2.2.2 r a w c hout

omit [Fintype P] in
/-- A non-crashed process with a pending operation eventually executes line 1. -/
lemma eventually_started {p : P} (hnc : ¬ e.Crashed p) {t : ℕ} (hp : (e.cfg t).pend p ≠ none) :
    ∃ t' ≥ t, ((esys e t').loc p).Started := by
  have hi := pend_ne_idle (e.reachable_cfg t) p hp
  by_cases hs : (e.cfg t).loc p = .start
  · obtain ⟨t', ht', hq, hl, hpe⟩ := first_step e hnc hp
    have hpe' : (e.cfg t').pend p ≠ none := hpe ▸ hp
    have htau := step_is_tau e hpe' hq (by rw [hl, hs]; simp)
    have h := e.step_eq t'
    rw [htau] at h
    refine ⟨t' + 1, by omega, ?_⟩
    have e1 := (toSys_step_tau h).1
    simp only [esys, e1, ESys.step, Function.update_self]
    refine estep_ne_idle (by simp [toSys, hl, hs]) |> fun h' => ⟨h', ?_⟩
    simp only [toSys, hl, hs, estep]; split_ifs <;> simp
  · exact ⟨t, le_rfl, hi, hs⟩

/-- **Doomed processes terminate**: a non-crashed started process that is not the last one to
have written `turn` reaches an `out` state. -/
lemma doomed_reach_out {p : P} (hnc : ¬ e.Crashed p) {t₀ : ℕ} (hp : (e.cfg t₀).pend p ≠ none)
    (hst : ((esys e t₀).loc p).Started) (ht : (esys e t₀).m.turn ≠ some p) :
    ∃ t ≥ t₀, ∃ r a w c, (e.cfg t).loc p = .out r a w c := by
  refine reach_out e hnc hp (fun t => dm ((e.cfg t).loc p)) fun t ht' _ hout => ⟨fun hl => ?_,
    fun hq => ?_⟩
  · have h := e.step_eq t
    rw [hl] at h
    have e1 := (toSys_step_tau h).1
    have hl1 : (e.cfg (t + 1)).loc p = (estep L p (esys e t).m ((e.cfg t).loc p)).2 := by
      have := congrArg (fun s : ESys P => s.loc p) e1
      simpa [toSys, ESys.step, esys] using this
    rw [hl1]
    obtain ⟨g, hg⟩ := (sys_reach e t).inv
    obtain ⟨hs1, hs2⟩ := doomed_persist e hst ht t ht'
    exact dm_step hs1 (hg.wf p) hout hs2
  · rw [(loc_succ_of_ne e hq).1]

/-- **Theorem 2.5** (second part, almost-wait-freedom): whatever the number of crashes, at most
one correct participating process does not terminate. -/
theorem starved_unique {p q : P} (hp : e.Starved p) (hq : e.Starved q) : p = q := by
  by_contra hpq
  obtain ⟨⟨Tp, hTp⟩, hcp⟩ := hp
  obtain ⟨⟨Tq, hTq⟩, hcq⟩ := hq
  obtain ⟨tp, htp, hsp⟩ := eventually_started e hcp (hTp Tp le_rfl)
  obtain ⟨tq, htq, hsq⟩ := eventually_started e hcq (hTq Tq le_rfl)
  set T := max tp tq
  have hsp' := started_persist e hsp T (le_max_left _ _)
  have hsq' := started_persist e hsq T (le_max_right _ _)
  by_cases ht : (esys e T).m.turn = some p
  · have htq : (esys e T).m.turn ≠ some q := by rw [ht]; simpa using hpq
    obtain ⟨t, -, r, a, w, c, h⟩ :=
      doomed_reach_out e hcq (hTq T (by omega)) hsq' htq
    exact not_blocked_of_out e hcq h ⟨Tq, hTq⟩
  · obtain ⟨t, -, r, a, w, c, h⟩ :=
      doomed_reach_out e hcp (hTp T (by omega)) hsp' ht
    exact not_blocked_of_out e hcp h ⟨Tp, hTp⟩

/-! ### Executions without crashes -/

omit [Fintype P] in
lemma esys_loc (t : ℕ) : (esys e t).loc = (e.cfg t).loc := rfl

/-- Eventually no process executes line 1 any more. -/
lemma exists_stable : ∃ T₀, ∀ t ≥ T₀, ∀ q, e.lbl t = .tau q → (e.cfg t).loc q ≠ .start := by
  classical
  let cnt : ℕ → ℕ := fun t => (Finset.univ.filter fun x => ¬ ((e.cfg t).loc x).Started).card
  have hsub : ∀ t, (Finset.univ.filter fun x => ¬ ((e.cfg (t + 1)).loc x).Started) ⊆
      Finset.univ.filter fun x => ¬ ((e.cfg t).loc x).Started := by
    intro t x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact fun h => hx (started_persist e (t₀ := t) h (t + 1) (by omega))
  have hmono : ∀ t ≥ 0, cnt (t + 1) ≤ cnt t := fun t _ => Finset.card_le_card (hsub t)
  obtain ⟨T, -, hT⟩ := Nat.eventually_not_of_succ_le hmono
    (p := fun t => ∃ q, e.lbl t = .tau q ∧ (e.cfg t).loc q = .start) (by
      rintro t - ⟨q, hq, hs⟩
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.2 ⟨hsub t, fun heq => ?_⟩
      have hmem : q ∈ Finset.univ.filter fun x => ¬ ((e.cfg t).loc x).Started := by
        simp [hs, ELoc.Started]
      rw [← heq] at hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      apply hmem
      have h := e.step_eq t
      rw [hq] at h
      have e1 := (toSys_step_tau h).1
      have := congrArg (fun s : ESys P => s.loc q) e1
      simp only [toSys, ESys.step, Function.update_self] at this
      rw [this, hs]; simp only [estep]; split_ifs <;> simp [ELoc.Started])
  exact ⟨T, fun t ht q hq hs => hT t ht ⟨q, hq, hs⟩⟩

omit [Fintype P] in
lemma no_start (hnc : ∀ p, ¬ e.Crashed p) {T₀ : ℕ}
    (hT₀ : ∀ t ≥ T₀, ∀ q, e.lbl t = .tau q → (e.cfg t).loc q ≠ .start) :
    ∀ t ≥ T₀, ∀ x, (e.cfg t).loc x ≠ .start := by
  intro t ht x hs
  have hp := pend_of_active (e.reachable_cfg t) x (by rw [hs]; simp) (by rw [hs]; simp)
  obtain ⟨t', ht', hq, hl, hpe⟩ := first_step e (hnc x) hp
  have := step_is_tau e (hpe ▸ hp) hq (by rw [hl, hs]; simp)
  exact hT₀ t' (by omega) x this (by rw [hl, hs])

omit [Fintype P] in
lemma turn_const (hnc : ∀ p, ¬ e.Crashed p) {T₀ : ℕ}
    (hT₀ : ∀ t ≥ T₀, ∀ q, e.lbl t = .tau q → (e.cfg t).loc q ≠ .start) :
    ∀ t ≥ T₀, (esys e t).m.turn = (esys e T₀).m.turn := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    rw [← ih]
    rcases sys_succ e t with e1 | e1 | e1 <;> rw [e1]
    · simp only [ESys.step]
      exact estep_turn_eq (no_start e hnc hT₀ t ht _)
    · unfold ESys.invoke; split_ifs <;> rfl

/-- Common setup for executions without crashes: from some time `T` on, `turn` is constant
(`= Y`), nobody executes line 1, and `Y` has started. -/
lemma final_turn (hnc : ∀ p, ¬ e.Crashed p) {p : P} {t₀ : ℕ} (hp : (e.cfg t₀).pend p ≠ none) :
    ∃ T ≥ t₀, ∃ Y, ((esys e T).loc Y).Started ∧ (∀ t ≥ T, (esys e t).m.turn = some Y) ∧
      ∀ t ≥ T, ∀ x, (e.cfg t).loc x ≠ .start := by
  obtain ⟨T₀, hT₀⟩ := exists_stable e
  obtain ⟨tp, htp, hsp⟩ := eventually_started e (hnc p) hp
  set T := max T₀ tp
  have hsp' := started_persist e hsp T (le_max_right _ _)
  obtain ⟨g, hg⟩ := (sys_reach e T).inv
  have hturn : (esys e T).m.turn ≠ none := fun h0 =>
    ((hg.age0 p).1 (hg.turnNone h0 p)) hsp'
  obtain ⟨Y, hY⟩ := Option.ne_none_iff_exists'.1 hturn
  have hc := turn_const e hnc hT₀
  have hYst : ((esys e T).loc Y).Started := by
    have := (hg.turnSome Y hY).1
    by_contra h'; exact this ((hg.age0 Y).2 h')
  refine ⟨T, by omega, Y, hYst, fun t ht => ?_, fun t ht => no_start e hnc hT₀ t (by omega)⟩
  rw [hc t (by omega), ← hc T (le_max_left _ _), hY]

/-- After `T`, every process other than `Y` is eventually idle or returned forever. -/
lemma others_settle (hnc : ∀ p, ¬ e.Crashed p) {T : ℕ} {Y : P}
    (hturn : ∀ t ≥ T, (esys e t).m.turn = some Y) (hns : ∀ t ≥ T, ∀ x, (e.cfg t).loc x ≠ .start)
    (x : P) (hx : x ≠ Y) : ∃ tx ≥ T, ∀ t ≥ tx,
      (e.cfg t).loc x = .idle ∨ ∃ r a w c, (e.cfg t).loc x = .out r a w c := by
  by_cases hst : ((e.cfg T).loc x).Started
  · have hdoom : ∃ t ≥ T, ∃ r a w c, (e.cfg t).loc x = .out r a w c := by
      by_cases hout : ∃ r a w c, (e.cfg T).loc x = .out r a w c
      · exact ⟨T, le_rfl, hout⟩
      · push Not at hout
        exact doomed_reach_out e (hnc x) (pend_of_active (e.reachable_cfg T) x hst.1 hout) hst
          (by rw [hturn T le_rfl]; simpa using Ne.symm hx)
    obtain ⟨t₁, ht₁, r, a, w, c, h₁⟩ := hdoom
    exact ⟨t₁, ht₁, fun t ht => Or.inr ⟨r, a, w, c, out_persist e (t₀ := t₁) h₁ t ht⟩⟩
  · have hidle : (e.cfg T).loc x = .idle := by
      simp only [ELoc.Started, not_and_or, not_not] at hst
      rcases hst with h | h
      · exact h
      · exact absurd h (hns T le_rfl x)
    refine ⟨T, le_rfl, fun t ht => Or.inl ?_⟩
    induction t, ht using Nat.le_induction with
    | base => exact hidle
    | succ t ht ih =>
      rcases sys_succ e t with e1 | e1 | e1
      · rw [← esys_loc, e1, esys_loc]; exact ih
      · rw [← esys_loc, e1]
        by_cases hq : (e.lbl t).proc = x
        · simp only [ESys.step, hq, Function.update_self, esys_loc, ih, estep]
        · simp only [ESys.step, Function.update_of_ne (Ne.symm hq), esys_loc, ih]
      · have := hns (t + 1) (by omega) x
        rw [← esys_loc, e1] at this ⊢
        unfold ESys.invoke at this ⊢
        split_ifs at this ⊢ with hq
        · by_cases hqx : (e.lbl t).proc = x
          · rw [hqx] at this; simp at this
          · simp only [Function.update_of_ne (Ne.symm hqx), esys_loc, ih]
        · simp only [esys_loc, ih]

/-- **Theorem 2.5** (first part): in the absence of crashes every participating process
terminates. -/
theorem not_starved_of_no_crash (hnc : ∀ p, ¬ e.Crashed p) (p : P) : ¬ e.Starved p := by
  classical
  rintro ⟨⟨Tb, hTb⟩, -⟩
  obtain ⟨T, hT, Y, hYst, hturn, hns⟩ := final_turn e hnc (hTb Tb le_rfl)
  -- `p` must be `Y`, all others are doomed
  have hpY : p = Y := by
    by_contra hpY
    obtain ⟨tp, htp, hsp⟩ := eventually_started e (hnc p) (hTb Tb le_rfl)
    have hsp' := started_persist e hsp (max T tp) (le_max_right _ _)
    obtain ⟨t, -, r, a, w, c, h⟩ := doomed_reach_out e (hnc p) (hTb _ (by omega)) hsp'
      (by rw [hturn _ (le_max_left _ _)]; simpa using Ne.symm hpY)
    exact not_blocked_of_out e (hnc p) h ⟨Tb, hTb⟩
  subst hpY
  have hset := fun x (hx : x ≠ p) => others_settle e hnc hturn hns x hx
  choose tx htx hx using hset
  let T₁ : ℕ := max T (Finset.univ.sup fun x => if h : x ≠ p then tx x h else 0)
  have hT₁ : ∀ x (hx : x ≠ p), tx x hx ≤ T₁ := fun x hx => by
    refine le_trans ?_ (le_max_right _ _)
    have := Finset.le_sup (f := fun x => if h : x ≠ p then tx x h else 0) (Finset.mem_univ x)
    simpa [hx] using this
  let t₀ := max T₁ Tb
  have hoth : ∀ t ≥ t₀, ∀ x, x ≠ p →
      (esys e t).loc x = .idle ∨ ∃ r a w c, (esys e t).loc x = .out r a w c := fun t ht x hx' =>
    hx x hx' t (le_trans (hT₁ x hx') (le_trans (le_max_left _ _) ht))
  obtain ⟨t₂, -, r, a, w, c, h₂⟩ := reach_out e (hnc p) (hTb t₀ (le_max_right _ _))
    (fun t => yMeasure L ((e.cfg t).loc p) (esys e t).m.done) fun t ht hpt hout => by
    constructor
    · intro hl
      have h := e.step_eq t
      rw [hl] at h
      have e1 := (toSys_step_tau h).1
      obtain ⟨g, hg⟩ := (sys_reach e t).inv
      have := y_step hg (sys_reach e t).sInv (hturn t (by omega)) (hoth t ht)
        (started_persist e hYst t (by omega)) hout
      rw [← esys_loc, show esys e (t + 1) = (esys e t).step L p from e1]
      exact this
    · intro hq
      have hm : (esys e (t + 1)).m = (esys e t).m := by
        rcases sys_succ e t with e1 | e1 | e1 <;> rw [e1]
        · simp only [ESys.step]
          rcases hoth t ht _ (Ne.symm (Ne.symm hq)) with hi | ⟨r, a, w, c, ho⟩
          · rw [hi]; rfl
          · rw [ho]; rfl
        · unfold ESys.invoke; split_ifs <;> rfl
      rw [(loc_succ_of_ne e hq).1, hm]
  exact not_blocked_of_out e (hnc p) h₂ ⟨Tb, hTb⟩

/-- **Theorem 2.2** (liveness): in the absence of crashes, if some process participates then
some process returns `1` (a leader is elected). -/
theorem exists_ret_true_of_no_crash (hnc : ∀ p, ¬ e.Crashed p) {p : P}
    (hpart : e.Participates p) : ∃ t x, e.lbl t = .ret x true := by
  classical
  obtain ⟨t₀, ht₀⟩ := hpart
  obtain ⟨T, -, Y, hYst, hturn, -⟩ := final_turn e hnc ht₀
  -- the first time `Y` is started
  have hex : ∃ t, ((esys e t).loc Y).Started := ⟨T, hYst⟩
  set tY := Nat.find hex
  have htYT : tY ≤ T := Nat.find_min' hex hYst
  have hYst0 : ((esys e tY).loc Y).Started := Nat.find_spec hex
  -- `turn = Y` from `tY` on
  have hturnY : ∀ t ≥ tY, (esys e t).m.turn = some Y := by
    intro t ht
    by_contra h'
    have := (doomed_persist e (started_persist e hYst0 t ht) h' (max t T) (le_max_left _ _)).2
    exact this (hturn _ (le_max_right _ _))
  -- `Y` only returns `0` after `done = 1`
  have hgood : ∀ t ≥ tY, ∀ a w c, (esys e t).loc Y = .out false a w c →
      (esys e t).m.done = true := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      intro a w c hY
      have htY0 : tY ≠ 0 := by
        intro h0
        have := hYst0; rw [h0] at this
        simp [esys, toSys, e.cfg_zero, Impl.initCfg, electionImpl, ELoc.Started] at this
      obtain ⟨t', ht'⟩ := Nat.exists_eq_succ_of_ne_zero htY0
      have hns : ¬ ((esys e t').loc Y).Started := Nat.find_min hex (by omega)
      have hY' : (esys e (t' + 1)).loc Y = .out false a w c := by
        rw [show t' + 1 = tY by omega]; exact hY
      exfalso
      rcases sys_succ e t' with e1 | e1 | e1 <;> rw [e1] at hY'
      · exact hns (by rw [hY']; simp [ELoc.Started])
      · by_cases hq : (e.lbl t').proc = Y
        · simp only [ESys.step, hq, Function.update_self] at hY'
          simp only [ELoc.Started, not_and_or, not_not] at hns
          rcases hns with h | h <;> rw [h] at hY' <;> simp only [estep] at hY' <;>
            (try split_ifs at hY') <;> simp at hY'
        · simp only [ESys.step, Function.update_of_ne (Ne.symm hq)] at hY'
          exact hns (by rw [hY']; simp [ELoc.Started])
      · unfold ESys.invoke at hY'
        split_ifs at hY' with hq
        · by_cases hqY : (e.lbl t').proc = Y
          · rw [hqY] at hY'; simp at hY'
          · simp only [Function.update_of_ne (Ne.symm hqY)] at hY'
            exact hns (by rw [hY']; simp [ELoc.Started])
        · exact hns (by rw [hY']; simp [ELoc.Started])
    | succ t ht ih =>
      intro a w c hY
      have hs := (sys_reach e t).sInv
      rcases sys_succ e t with e1 | e1 | e1 <;> rw [e1] at hY ⊢
      · exact ih a w c hY
      · by_cases hq : (e.lbl t).proc = Y
        · simp only [ESys.step, hq, Function.update_self] at hY
          simp only [ESys.step, hq]
          rcases estep_outFalse_turn hY (hturnY t ht) with h1 | h1 | ⟨k, b, j, h1⟩
          · exact estep_done_mono h1
          · exact estep_done_mono (ih a w c h1)
          · exact absurd (hturnY t ht) (hs.clrTurn Y k b j h1)
        · simp only [ESys.step, Function.update_of_ne (Ne.symm hq)] at hY
          exact estep_done_mono (ih a w c hY)
      · unfold ESys.invoke at hY ⊢
        split_ifs at hY ⊢ with hq
        · by_cases hqY : (e.lbl t).proc = Y
          · rw [hqY] at hY; simp at hY
          · simp only [Function.update_of_ne (Ne.symm hqY)] at hY; exact ih a w c hY
        · exact ih a w c hY
  -- `Y` eventually returns, so `done = 1` at some point
  have hYnb : ¬ e.Blocked Y := fun hb => not_starved_of_no_crash e hnc Y ⟨hb, hnc Y⟩
  simp only [InfExec.Blocked, not_exists, not_forall] at hYnb
  obtain ⟨t₂, ht₂, hp₂⟩ := hYnb T
  simp only [ne_eq, not_not] at hp₂
  have hst₂ := started_persist e hYst t₂ ht₂
  have hout₂ : ∃ r a w c, (e.cfg t₂).loc Y = .out r a w c := by
    by_contra h'
    push Not at h'
    exact pend_of_active (e.reachable_cfg t₂) Y hst₂.1 h' hp₂
  obtain ⟨r, a, w, c, hY₂⟩ := hout₂
  have hd : (esys e t₂).m.done = true := by
    cases r
    · exact hgood t₂ (by omega) a w c hY₂
    · exact (sys_reach e t₂).sInv.outDone Y a w c hY₂
  obtain ⟨x, a', w', c', hx⟩ := (sys_reach e t₂).sInv.doneOut hd
  -- the elected process `x` returns `1`
  by_cases hpx : (e.cfg t₂).pend x = none
  · have := ret_true_of_outTrue (e.run_pre t₂) x hx hpx
    simp only [InfExec.pre, List.mem_map, List.mem_range] at this
    obtain ⟨t, -, ht⟩ := this
    exact ⟨t, x, ht⟩
  · obtain ⟨t', -, hq, hl, hpe⟩ := first_step e (hnc x) hpx
    have h := e.step_eq t'
    have hl' : (e.cfg t').loc x = .out true a' w' c' := by rw [hl]; exact hx
    cases hlb : e.lbl t' with
    | inv q o =>
      rw [hlb] at h hq; simp only [Label.proc] at hq; subst hq
      exact absurd (Impl.step_inv h).1 (hpe ▸ hpx)
    | tau q =>
      rw [hlb] at h hq; simp only [Label.proc] at hq; subst hq
      exact absurd hl' ((toSys_step_tau h).2.2.2 true a' w' c')
    | ret q r =>
      rw [hlb] at h hq; simp only [Label.proc] at hq; subst hq
      rcases (toSys_step_ret h).2 with ⟨h1, -⟩ | ⟨a, w, c, h1⟩
      · rw [h1] at hl'; cases hl'
      · rw [h1] at hl'
        have hr : r = true := by injection hl'
        subst hr
        exact ⟨t', q, hlb⟩

end Exec

/-! ### Almost-wait-freedom and Theorem 2.1 -/

/-- **Theorem 2.5** as a resilience statement: the election algorithm is almost-wait-free (for
any admissible set of infinite executions, participation not required). -/
theorem electionImpl_almostWaitFree [Fintype P] (L : ℕ)
    (Adm : (electionImpl (P := P) L).InfExec → Prop) :
    (electionImpl (P := P) L).AlmostWaitFree Adm := by
  intro e _ _
  show _ ≤ if _ = 0 then 0 else 1
  split_ifs with h0
  · have hc : ∀ p, ¬ e.Crashed p := fun p hp => by
      rw [Set.ncard_eq_zero (Set.toFinite _)] at h0
      exact (Set.eq_empty_iff_forall_notMem.1 h0) p hp
    have : {p | e.Starved p} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun p hp => not_starved_of_no_crash e hc p hp
    rw [this, Set.ncard_empty]
  · exact (Set.ncard_le_one_iff (Set.toFinite _)).2 fun hp hq => starved_unique e hp hq

/-- **Theorem 2.1.** For `n` processes and `L = ⌈log₂ n⌉` levels, the algorithm of Section 2.1
is an almost-wait-free election algorithm using the `L + 2` registers `turn`, `done`,
`V[0..L-1]`:
1. (safety, Theorem 2.4) in every execution at most one process returns `1`;
2. (Theorem 2.2) in every infinite execution without crashes in which some process
   participates, some process returns `1`;
3. (Theorem 2.5) it is almost-wait-free; in particular without crashes every participating
   process terminates;
4. every register access is to `turn`, `done` or `V[k]` with `k < L`.
The algorithm is symmetric: identifiers come from an arbitrary type and are only compared for
equality. -/
theorem theorem_2_1 [Fintype P] :
    let L := Nat.clog 2 (Fintype.card P)
    (∀ α, (electionImpl (P := P) L).Valid α → ∀ p q,
        Label.ret p true ∈ α → Label.ret q true ∈ α → p = q) ∧
    (∀ e : (electionImpl (P := P) L).InfExec, (∀ p, ¬ e.Crashed p) →
        (∃ p, e.Participates p) → ∃ t x, e.lbl t = .ret x true) ∧
    (∀ e : (electionImpl (P := P) L).InfExec, (∀ p, ¬ e.Crashed p) → ∀ p, ¬ e.Starved p) ∧
    (electionImpl (P := P) L).AlmostWaitFree (fun _ => True) ∧
    (∀ (p : P) (l : ELoc), l.WF L → ∀ (i : Reg) (o : (Regs P i).Op) (k : (Regs P i).Resp → ELoc),
        (electionImpl (P := P) L).act p l = .access i o k →
        i = .turn ∨ i = .done ∨ ∃ j < L, i = .v j) := by
  intro L
  refine ⟨fun α hα p q hp hq => election_safety card_le_two_pow_clog hα hp hq,
    fun e hnc ⟨p, hp⟩ => exists_ret_true_of_no_crash e hnc hp,
    fun e hnc p => not_starved_of_no_crash e hnc p, electionImpl_almostWaitFree L _,
    fun p l hl i o k h => electionImpl_accessed p l hl h⟩

end Podc.CloserLookFT
