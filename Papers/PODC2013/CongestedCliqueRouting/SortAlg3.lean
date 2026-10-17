import Papers.PODC2013.CongestedCliqueRouting.SortPrim
import Papers.PODC2013.CongestedCliqueRouting.Buckets

/-!
# Algorithm 3: sorting inside the groups

Every group `W` (of size `s = √n`) sorts the keys held by its members (at most `3 s²` per
member), in parallel for all groups, in 6 rounds (Steps 1–7 of Algorithm 3 of the paper; the
final redistribution, Step 8, is skipped as in the proof of Theorem 4.5):

* rounds 0–1: every member selects every `(3s)`-th of its keys and announces them to the group;
* local: delimiters = every `s`-th of the announced keys; bucket `y` of a key = number of
  delimiters below it;
* rounds 2–3: every member announces how many of its keys fall into each bucket;
* rounds 4–5: Corollary 3.3: bucket `y` is sent to member `y` (via intermediate nodes,
  pattern known inside the group, at most 6 keys per edge).

Afterwards member `y` holds bucket `y` (fewer than `6 s²` keys, Lemma 4.3) and knows the rank of
each of its keys among the keys of its group.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace CongestedCliqueRouting

open Finset

/-- Packet size used by the sorting algorithm. -/
abbrev SB : ℕ := (4 * (4 * 3)) * 2

variable {I V M : Type*} [Fintype V] [DecidableEq V] [LinearOrder M] [Nonempty V] {s : ℕ}
  [NeZero s] (e : V ≃ Fin s × Fin s)

/-- Node numbers. -/
def enc (v : V) : ℕ := (finProdFinEquiv (e v) : ℕ)

lemma enc_inj : Function.Injective (enc e) := by
  intro v w h
  exact e.injective (finProdFinEquiv.injective (Fin.ext h))

lemma enc_lt (v : V) : enc e v < s * s := (finProdFinEquiv (e v)).isLt

lemma one_le_s : 1 ≤ s := Nat.one_le_iff_ne_zero.2 (NeZero.ne s)

namespace Alg3

variable (A : I → V → Finset M)

/-- Selected keys of `v`: every `(3s)`-th. -/
def sel (d : I) (v : V) : Finset M := let _ := e; samples (A d v) (3 * s)

/-- The `j`-th selected key. -/
noncomputable def selAt (d : I) (v : V) (j : Fin s) : Option M :=
  pick ((sel e A d v).filter fun x => rk (sel e A d v) x = j)

/-- All keys selected in group `a`. -/
def U3 (d : I) (a : Fin s) : Finset M := univ.biUnion fun b => sel e A d (node e a b)

/-- Bucket of a key in group `a`. -/
def bk (d : I) (a : Fin s) (x : M) : ℕ := bucketOf (delims (U3 e A d a) s s) x

lemma bk_lt (d : I) (a : Fin s) (x : M) : bk e A d a x < s := by
  have := bucketOf_delims_le (U := U3 e A d a) (q := s) (k := s) x
  have := one_le_s (s := s)
  unfold bk; omega

/-- Number of keys of `v` in bucket `y`. -/
def cnt (d : I) (v : V) (y : Fin s) : ℕ := ((A d v).filter fun x => bk e A d (grp e v) x = y).card

/-- The count matrix of group `a`. -/
def Cm (d : I) (a : Fin s) (b y : Fin s) : ℕ := cnt e A d (node e a b) y

/-- König split of the count matrix: at most 6 keys per edge. -/
noncomputable def Rp (d : I) (a : Fin s) : V → Fin s → Fin s → ℕ := splitParts V (Cm e A d a) 6

/-- Target member of a key. -/
def tg (d : I) (v : V) (x : M) : V := node e (grp e v) ⟨bk e A d (grp e v) x, bk_lt e A d _ x⟩

/-- Intermediate node of a key. -/
noncomputable def via (d : I) (v : V) : M → V :=
  assign (A d v) (fun x => bk e A d (grp e v) x)
    (fun y c => if h : y < s then Rp e A d (grp e v) c (mem e v) ⟨y, h⟩ else 0)

noncomputable def Q0 (d : I) : V → V → Packet M SB := gak1 e (selAt e A d)
noncomputable def Q1 (d : I) : V → V → Packet M SB := fwdP e (Q0 e A d)
noncomputable def Q2 (d : I) : V → V → Packet M SB := gan1 e (cnt e A d)
noncomputable def Q3 (d : I) : V → V → Packet M SB := fwdP e (Q2 e A d)
noncomputable def Q4 (d : I) : V → V → Packet M SB :=
  fun v c => rr1 (enc e) (A d v) (via e A d v) (tg e A d v) c
noncomputable def Q5 (d : I) : V → V → Packet M SB := fun c w => rr2 (enc e) (fun u => Q4 e A d u c) w

/-- The packets of round `k` of Algorithm 3. -/
noncomputable def pkt (d : I) : ℕ → V → V → Packet M SB
  | 0 => Q0 e A d
  | 1 => Q1 e A d
  | 2 => Q2 e A d
  | 3 => Q3 e A d
  | 4 => Q4 e A d
  | _ => Q5 e A d

/-- Keys held by member `w` at the end: bucket `mem w` of its group. -/
noncomputable def Bk (d : I) (w : V) : Finset M := rcvd (Q5 e A d) w

/-- All keys of group `a`. -/
def GA (d : I) (a : Fin s) : Finset M := univ.biUnion fun b => A d (node e a b)

end Alg3

end CongestedCliqueRouting
