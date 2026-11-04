import Papers.PODC2014.WritableObjects.Lemma48Queue

/-!
# Lemma 4.8, part 2: update clocks of `recycle()`

`stage pc` is the number of the three atomic steps of `recycle()` (lines 25–28, 29–30, 31–32)
already done in the current `Write`; `Loc.U l o` is the number of updates of queue `o` done so
far, and `nr l o q` is the next update time at which `p` reads the slot of `q` belonging to
queue `o` (`o = 1`: `Annc[q]`, `o = 2`: `H_p[q]`, `o = 3`: `H'_p[q]`). This is how Claims
4.16–4.17 ("`p` reads `X` within `n` calls of `recycle()`") are encoded.
-/

namespace Podc.WritableObjects.WF

open Cslib.SharedMemory

variable {n : ℕ} {T : ObjSpec}

/-- Number of atomic steps of `recycle()` done in the current `Write`. -/
def stage : PC n T → ℕ
  | .w29 .. => 1
  | .w31 .. => 2
  | .w13 .. | .wSW .. | .w14 .. | .w15 .. | .w16 .. | .w18 .. | .w19 .. | .w20 .. | .w21 ..
  | .w23 .. => 3
  | _ => 0

/-- The write-index of the current `Write` (once chosen). -/
def curF : PC n T → Option (Idx n)
  | .w29 _ f | .w31 _ f | .w13 _ f | .wSW _ f | .w14 _ f | .w15 _ f .. | .w16 _ f .. | .w18 _ f ..
  | .w19 _ f | .w20 _ f .. | .w21 _ f .. | .w23 _ f => some f
  | _ => none

/-- The current `Write` has chosen its write-index but not yet written it to `Ptr`. -/
def isPrePtr : PC n T → Prop
  | .w29 .. | .w31 .. | .w13 .. | .wSW .. | .w14 .. | .w15 .. | .w16 .. | .w18 .. | .w19 ..
  | .w20 .. | .w23 .. => True
  | _ => False

/-- Between lines 18 and 21 (`H_p[ctr]` written, `H'_p[ctr]` not yet). -/
def isW1921 : PC n T → Prop
  | .w19 .. | .w20 .. | .w21 .. => True
  | _ => False

/-- Number of updates of queue `o` done so far. -/
def Loc.U (l : Loc n T) (o : Fin 4) : ℕ := l.ctr + if max o.val 1 ≤ stage l.pc then 1 else 0

/-- The first update time `≥ 4 U + o` of queue `o` in a `recycle()` whose number is `≡ q`. -/
def nextR (n U o : ℕ) (q : ℕ) : ℕ := 4 * (U + (q + n - U % n) % n) + o

/-- Next time `p` reads the slot of `q` of queue `o`. -/
def Loc.nr (l : Loc n T) (o : Fin 4) (q : Fin n) : ℕ := nextR n (l.U o) o q

/-- Hold of `i` in the queues of `l`. -/
def Loc.Hold (l : Loc n T) (i : Idx n) (γ : ℕ) : Prop := WF.Hold l.qs l.U i γ

/-! ## Arithmetic of `nextR` -/

section arith

variable [NeZero n]

omit [NeZero n] in
lemma nextR_ge (U o q : ℕ) : 4 * U + o ≤ nextR n U o q := by unfold nextR; omega

/-- The distance to the next `recycle()` number `≡ q`. -/
lemma dist_spec (U q : ℕ) (hq : q < n) :
    (q + n - U % n) % n < n ∧ (U + (q + n - U % n) % n) % n = q := by
  have hn := Nat.pos_of_neZero n
  refine ⟨Nat.mod_lt _ hn, ?_⟩
  have h1 := Nat.mod_lt U hn
  rw [Nat.add_mod, Nat.mod_mod, Nat.add_mod_mod, show U % n + (q + n - U % n) = q + n by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hq]

omit [NeZero n] in
lemma dist_unique {U a b : ℕ} (ha : a < n) (hb : b < n) (h : (U + a) % n = (U + b) % n) :
    a = b := by
  rcases Nat.le_total a b with hab | hab
  · have := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    rw [show U + b - (U + a) = b - a by omega] at this
    rcases Nat.eq_zero_or_pos (b - a) with h0 | h0
    · omega
    · exact absurd (Nat.le_of_dvd h0 (Nat.dvd_of_mod_eq_zero this)) (by omega)
  · have := Nat.sub_mod_eq_zero_of_mod_eq h
    rw [show U + a - (U + b) = a - b by omega] at this
    rcases Nat.eq_zero_or_pos (a - b) with h0 | h0
    · omega
    · exact absurd (Nat.le_of_dvd h0 (Nat.dvd_of_mod_eq_zero this)) (by omega)

lemma dist_eq {U q d : ℕ} (hq : q < n) (hd : d < n) (h : (U + d) % n = q) :
    (q + n - U % n) % n = d :=
  dist_unique (dist_spec U q hq).1 hd (by rw [(dist_spec U q hq).2, h])

lemma nextR_eq_self {U o q : ℕ} (hq : q < n) (h : U % n = q) : nextR n U o q = 4 * U + o := by
  unfold nextR; rw [dist_eq hq (Nat.pos_of_neZero n) (by simpa using h)]; omega

lemma nextR_succ_of_ne {U o q : ℕ} (hq : q < n) (h : U % n ≠ q) :
    nextR n (U + 1) o q = nextR n U o q := by
  obtain ⟨h1, h2⟩ := dist_spec (n := n) U q hq
  set d := (q + n - U % n) % n with hd
  have d0 : d ≠ 0 := by intro h0; rw [h0] at h2; simp at h2; exact h h2
  have : (q + n - (U + 1) % n) % n = d - 1 :=
    dist_eq hq (by omega) (by rw [show U + 1 + (d - 1) = U + d by omega]; exact h2)
  unfold nextR; rw [this, ← hd]; omega

lemma nextR_succ_of_eq {U o q : ℕ} (hq : q < n) (h : U % n = q) :
    nextR n (U + 1) o q = 4 * U + o + 4 * n := by
  have hn := Nat.pos_of_neZero n
  have : (q + n - (U + 1) % n) % n = n - 1 :=
    dist_eq hq (by omega) (by rw [show U + 1 + (n - 1) = U + n by omega, Nat.add_mod_right, h])
  unfold nextR; rw [this]; omega

lemma nextR_le (U o q : ℕ) : nextR n U o q ≤ 4 * (U + n - 1) + o := by
  have hn := Nat.pos_of_neZero n
  have := Nat.mod_lt (q + n - U % n) hn
  unfold nextR; omega

lemma nextR_div (U o q : ℕ) (ho : o < 4) (hq : q < n) :
    nextR n U o q / 4 % n = q ∧ nextR n U o q % 4 = o := by
  unfold nextR
  constructor
  · rw [show (4 * (U + (q + n - U % n) % n) + o) / 4 = U + (q + n - U % n) % n by omega]
    exact (dist_spec U q hq).2
  · omega

end arith

end Podc.WritableObjects.WF
