import Papers.PODC2026.FEATOrdering.Tree
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# The FEAT protocol (§5) and its correctness (§6: Lemmas 6.3, 6.5, Theorems 6.4, 6.6)

## Model

* `n = |R|` replicas, of which those in `H` are honest and at most `f` are Byzantine.
* `L r i` is the committed local ordering of replica `i` up to round `r` (all fragments committed
  in rounds `≤ r`, concatenated). Committed orderings only grow (`L r i <+: L (r+1) i`); a Byzantine
  replica's committed ordering is otherwise arbitrary. The committed ordering of an honest replica
  is a prefix of the order `recv i` in which it received transactions (consensus property (3)),
  and every transaction received by an honest replica is eventually committed by all honest
  replicas (property (4)).
* `W r a b` is the number of replicas whose committed ordering at round `r` *places `a` before
  `b`*: it contains `a`, and either not `b` or `b` after `a` (`Before`). This is the reading used
  in the proof of Lemma 6.3 ("committed `z` but not `m`").
* `pcmp r a b` is the weight-based round-`r` comparator (rules (1)–(4) of §5.1, with the tie-break
  `tb`); `W ≥ τ_dec = (n−f)/2` is written `n − f ≤ 2W`. `cmpT a b` is its value at the *first*
  round where it is defined (§4.1).
* Transactions are classified by a score; `solid` means `score ≥ τ_solid = n − f`, non-blank means
  `score ≥ τ_shaded = (n−f)/2`. The paper defines the score as the number of **honest** replicas
  whose committed orderings include the transaction (`scoreHonest`); we prove correctness for the
  score counting **all** replicas (`scoreAll`) and show in `Counterexample.lean` that the paper's
  definition breaks Lemma 6.3 and Theorems 6.4/6.6.

## Algorithm

`run` is FEAT with all comparisons answered by the global comparator `cmpT`. In the protocol every
comparison that FEAT acts on is answered by `pcmp^(r')`, which equals `cmpT` once defined
(monotone refinement), and an undefined answer only delays the action (deferral of a shaded
insertion, waiting in the merge). So FEAT's outputs are those of `run` for the order in which
insertions eventually succeed; we quantify over all insertion orders `ins r` (any order of the
transactions newly non-blank in round `r`) and over all in-order-preserving rebalancings `bal`.
Round `r` then: builds the BST of `ins r`, takes its in-order traversal `RO r`, merges it with the
tail list, finalizes the prefix up to the last transaction solid at round `r`, keeps the rest as
the new tail list.
-/

namespace Podc.FEATOrdering

open Finset

/-- `Before l a b`: the ordering `l` places `a` before `b` — it contains `a`, and `b` is either
absent or comes later. -/
def Before {X : Type*} [DecidableEq X] (l : List X) (a b : X) : Prop :=
  a ∈ l ∧ (b ∈ l → l.idxOf a < l.idxOf b)

instance {X : Type*} [DecidableEq X] (l : List X) (a b : X) : Decidable (Before l a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The system: replicas, committed local orderings, honest replicas and their receive orders. -/
structure Setup (R X : Type*) [Fintype R] [DecidableEq R] [DecidableEq X] where
  /-- Upper bound on the number of Byzantine replicas. -/
  f : ℕ
  /-- Committed local ordering of replica `i` up to round `r`. -/
  L : ℕ → R → List X
  /-- Committed orderings only grow. -/
  L_mono : ∀ r i, L r i <+: L (r + 1) i
  /-- Deterministic tie-breaker (hash), antisymmetric. -/
  tb : X → X → Bool
  tb_anti : ∀ a b, a ≠ b → tb a b = !tb b a
  /-- Honest replicas. -/
  H : Finset R
  card_byz : (univ \ H).card ≤ f
  /-- Order in which honest replica `i` receives transactions. -/
  recv : R → List X
  /-- (3) honest fragments are committed in receive order. -/
  L_prefix_recv : ∀ r, ∀ i ∈ H, L r i <+: recv i
  /-- (4) every transaction received by an honest replica is eventually committed by all honest
  replicas. -/
  eventually : ∀ i ∈ H, ∀ x ∈ recv i, ∃ r, ∀ j ∈ H, x ∈ L r j

namespace Setup

variable {R X : Type*} [Fintype R] [DecidableEq X] [DecidableEq R] (S : Setup R X)

/-- Number of replicas. -/
abbrev n (_S : Setup R X) : ℕ := Fintype.card R

/-- `W_r(a, b)`: number of committed local orderings (up to round `r`) placing `a` before `b`. -/
def W (r : ℕ) (a b : X) : ℕ := (univ.filter fun i => Before (S.L r i) a b).card

/-- `w ≥ τ_dec = (n − f)/2`. -/
def Heavy (w : ℕ) : Prop := S.n - S.f ≤ 2 * w

instance (w : ℕ) : Decidable (S.Heavy w) := inferInstanceAs (Decidable (_ ≤ _))

/-- The weight-based round-`r` comparator `pcmp^(r)` of §5.1 (`none` = `⊥`). By convention
`pcmp r a a = some true`. -/
def pcmp (r : ℕ) (a b : X) : Option Bool :=
  if a = b then some true
  else if ¬ S.Heavy (S.W r a b) ∧ ¬ S.Heavy (S.W r b a) then none
  else if S.W r b a < S.W r a b then some true
  else if S.W r a b < S.W r b a then some false
  else some (S.tb a b)

open Classical in
/-- The global comparator `cmp_T` (§4.1): the value of `pcmp` at the first round where it is
defined. (If a pair is never decided, we use the tie-breaker; this never happens under the
model's assumptions for transactions received by honest replicas.) -/
noncomputable def cmpT (a b : X) : Bool :=
  if h : ∃ r, (S.pcmp r a b).isSome then (S.pcmp (Nat.find h) a b).get (Nat.find_spec h)
  else S.tb a b

/-- The score of the paper: number of **honest** replicas whose committed ordering includes `x`. -/
def scoreHonest (r : ℕ) (x : X) : ℕ := (S.H.filter fun i => x ∈ S.L r i).card

/-- The repaired score: number of replicas whose committed ordering includes `x`. -/
def scoreAll (r : ℕ) (x : X) : ℕ := (univ.filter fun i => x ∈ S.L r i).card

/-- `γ`-fraction of the honest replicas receive `a` before `b`. -/
def GammaPrec (γ : ℝ) (a b : X) : Prop :=
  γ * S.H.card ≤ ((S.H.filter fun i => Before (S.recv i) a b).card : ℝ)

end Setup

/-- Split a merged list at its last element satisfying `p`: (finalized prefix, new tail list).
This is `LastSolidIndex` of Algorithm 3. -/
def cutLast {X : Type*} (p : X → Bool) : List X → List X × List X
  | [] => ([], [])
  | x :: xs =>
    let q := cutLast p xs
    if q.1 = [] then (if p x then ([x], q.2) else ([], x :: q.2)) else (x :: q.1, q.2)

theorem cutLast_append {X : Type*} (p : X → Bool) (l : List X) :
    (cutLast p l).1 ++ (cutLast p l).2 = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [cutLast]
    split_ifs with h1 h2 <;> simp_all

theorem cutLast_getLast {X : Type*} (p : X → Bool) (l : List X) :
    ∀ z ∈ (cutLast p l).1.getLast?, p z = true := by
  induction l with
  | nil => simp [cutLast]
  | cons x xs ih =>
    simp only [cutLast]
    split_ifs with h1 h2
    · simpa using h2
    · simp
    · intro z hz
      apply ih z
      rcases List.exists_cons_of_ne_nil h1 with ⟨a, t, ht⟩
      rw [ht] at hz ⊢
      simpa [List.getLast?_cons] using hz

namespace Setup

variable {R X : Type*} [Fintype R] [DecidableEq X] [DecidableEq R] (S : Setup R X)

/-- Classification: non-blank (solid or shaded) iff `score ≥ τ_shaded = (n−f)/2`. -/
def NonBlank (score : ℕ → X → ℕ) (r : ℕ) (x : X) : Prop := S.n - S.f ≤ 2 * score r x

/-- Classification: solid iff `score ≥ τ_solid = n − f`. -/
def Solid (score : ℕ → X → ℕ) (r : ℕ) (x : X) : Prop := S.n - S.f ≤ score r x

instance (score : ℕ → X → ℕ) (r : ℕ) (x : X) : Decidable (S.Solid score r x) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (score : ℕ → X → ℕ) (r : ℕ) (x : X) : Decidable (S.NonBlank score r x) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Round ordering `RO_r`: in-order traversal of the round-`r` AVL tree. -/
noncomputable def RO (ins : ℕ → List X) (bal : BTree X → BTree X) (r : ℕ) : List X :=
  (buildTree S.cmpT bal (ins r)).inorder

/-- One round of FEAT (Algorithm 3 after Algorithm 1): merge the tail list with `RO_r`, finalize
up to the last transaction solid at round `r`. State = (final ordering, tail list). -/
noncomputable def step (score : ℕ → X → ℕ) (ins : ℕ → List X) (bal : BTree X → BTree X)
    (r : ℕ) (st : List X × List X) : List X × List X :=
  let M := List.merge st.2 (S.RO ins bal r) S.cmpT
  let q := cutLast (fun x => decide (S.Solid score r x)) M
  (st.1 ++ q.1, q.2)

/-- The state of FEAT after round `r` (rounds are `1, 2, …`). -/
noncomputable def run (score : ℕ → X → ℕ) (ins : ℕ → List X) (bal : BTree X → BTree X) :
    ℕ → List X × List X
  | 0 => ([], [])
  | r + 1 => S.step score ins bal (r + 1) (run score ins bal r)

/-- `FO_r`: the final ordering after round `r`. -/
noncomputable def FO (score : ℕ → X → ℕ) (ins : ℕ → List X) (bal : BTree X → BTree X)
    (r : ℕ) : List X := (S.run score ins bal r).1

/-- Admissible insertion orders: in round `r + 1`, FEAT inserts each transaction that became
non-blank in this round, once (in any order: solids first, then shaded ones in the order in which
their insertions succeed). -/
structure InsOK (score : ℕ → X → ℕ) (ins : ℕ → List X) : Prop where
  nodup : ∀ r, (ins r).Nodup
  new : ∀ r x, x ∈ ins (r + 1) → S.NonBlank score (r + 1) x ∧ ¬ S.NonBlank score r x

/-! ### Basic facts -/

theorem before_mono {l m : List X} (h : l <+: m) {a b : X} (hb : Before l a b) : Before m a b := by
  obtain ⟨s, rfl⟩ := h
  refine ⟨List.mem_append_left _ hb.1, fun hbm => ?_⟩
  rw [List.idxOf_append_of_mem hb.1]
  by_cases hbl : b ∈ l
  · rw [List.idxOf_append_of_mem hbl]; exact hb.2 hbl
  · rw [List.idxOf_append_of_notMem hbl]
    exact lt_of_lt_of_le (List.idxOf_lt_length_of_mem hb.1) (Nat.le_add_right _ _)

theorem before_total {l : List X} {a b : X} (hab : a ≠ b) (h : a ∈ l ∨ b ∈ l) :
    Before l a b ∨ Before l b a := by
  by_cases ha : a ∈ l <;> by_cases hb : b ∈ l
  · rcases lt_trichotomy (l.idxOf a) (l.idxOf b) with h | h | h
    · exact Or.inl ⟨ha, fun _ => h⟩
    · exact absurd ((List.idxOf_inj ha).1 h) hab
    · exact Or.inr ⟨hb, fun _ => h⟩
  · exact Or.inl ⟨ha, fun h => absurd h hb⟩
  · exact Or.inr ⟨hb, fun h => absurd h ha⟩
  · tauto

/-- An honest committed prefix cannot place `b` before `a` if the full receive order places `a`
before `b`. -/
theorem not_before_of_prefix {l m : List X} (h : l <+: m) {a b : X} (hl : Before l b a) :
    ¬ Before m a b := by
  intro hm
  obtain ⟨s, rfl⟩ := h
  have hidx := hm.2 (List.mem_append_left _ hl.1)
  rw [List.idxOf_append_of_mem hl.1] at hidx
  by_cases ha : a ∈ l
  · rw [List.idxOf_append_of_mem ha] at hidx
    exact absurd (hl.2 ha) (not_lt.2 hidx.le)
  · rw [List.idxOf_append_of_notMem ha] at hidx
    exact absurd (List.idxOf_lt_length_of_mem hl.1) (not_lt.2 (le_trans (Nat.le_add_right _ _)
      hidx.le))

theorem L_prefix_of_le {r r' : ℕ} (h : r ≤ r') (i : R) : S.L r i <+: S.L r' i := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (S.L_mono _ i)

theorem W_mono {r r' : ℕ} (h : r ≤ r') (a b : X) : S.W r a b ≤ S.W r' a b :=
  card_le_card fun i hi => by
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact before_mono (S.L_prefix_of_le h i) hi

theorem scoreAll_mono {r r' : ℕ} (h : r ≤ r') (x : X) : S.scoreAll r x ≤ S.scoreAll r' x :=
  card_le_card fun i hi => by
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact (S.L_prefix_of_le h i).subset hi

theorem scoreHonest_mono {r r' : ℕ} (h : r ≤ r') (x : X) :
    S.scoreHonest r x ≤ S.scoreHonest r' x :=
  card_le_card fun i hi => by
    simp only [mem_filter] at hi ⊢
    exact ⟨hi.1, (S.L_prefix_of_le h i).subset hi.2⟩

theorem pcmp_self (r : ℕ) (a : X) : S.pcmp r a a = some true := by simp [pcmp]

/-- If `W_r(b, a) < τ_dec`, then `pcmp^(r)(a, b) ≠ False`. -/
theorem pcmp_ne_false {r : ℕ} {a b : X} (h : ¬ S.Heavy (S.W r b a)) :
    S.pcmp r a b ≠ some false := by
  unfold pcmp
  split_ifs with h1 h2 h3 h4
  · simp
  · simp
  · simp
  · exfalso; apply h2; refine ⟨fun hh => h ?_, h⟩
    unfold Heavy at hh ⊢; omega
  · exfalso; apply h2; refine ⟨fun hh => h ?_, h⟩
    unfold Heavy at hh ⊢; omega

/-- If `pcmp^(r)(a, b) = False`, then `W_r(b, a) ≥ τ_dec`. -/
theorem heavy_of_pcmp_false {r : ℕ} {a b : X} (h : S.pcmp r a b = some false) :
    S.Heavy (S.W r b a) := by
  by_contra h'
  exact S.pcmp_ne_false h' h

theorem pcmp_isSome_iff (r : ℕ) (a b : X) :
    (S.pcmp r a b).isSome ↔ a = b ∨ S.Heavy (S.W r a b) ∨ S.Heavy (S.W r b a) := by
  unfold pcmp
  split_ifs <;> simp_all <;> tauto

theorem pcmp_isSome_symm (r : ℕ) (a b : X) :
    (S.pcmp r a b).isSome = (S.pcmp r b a).isSome := by
  rw [Bool.eq_iff_iff, S.pcmp_isSome_iff, S.pcmp_isSome_iff]
  constructor <;> rintro (h | h | h) <;> simp_all [eq_comm]

theorem pcmp_symm {r : ℕ} {a b : X} (hab : a ≠ b) {v : Bool} (h : S.pcmp r a b = some v) :
    S.pcmp r b a = some (!v) := by
  have hba : b ≠ a := Ne.symm hab
  unfold pcmp at h ⊢
  simp only [hab, hba, if_false] at h ⊢
  by_cases hl : ¬ S.Heavy (S.W r a b) ∧ ¬ S.Heavy (S.W r b a)
  · rw [if_pos hl] at h; cases h
  · rw [if_neg hl] at h
    rw [if_neg (fun h' => hl ⟨h'.2, h'.1⟩)]
    split_ifs at h ⊢ <;> first | omega | (cases h; simp [S.tb_anti a b hab])

open Classical in
/-- `cmpT a b` is the value of `pcmp` at round `r` if no earlier-or-equal round gives the
opposite value. -/
theorem cmpT_eq_of {r : ℕ} {a b : X} {v : Bool} (h : S.pcmp r a b = some v)
    (hbefore : ∀ r' ≤ r, S.pcmp r' a b ≠ some (!v)) : S.cmpT a b = v := by
  have hex : ∃ r, (S.pcmp r a b).isSome := ⟨r, by simp [h]⟩
  unfold cmpT
  rw [dif_pos hex]
  have hle : Nat.find hex ≤ r := Nat.find_min' hex (by simp [h])
  have hs := Nat.find_spec hex
  have hw : S.pcmp (Nat.find hex) a b = some ((S.pcmp (Nat.find hex) a b).get hs) :=
    (Option.some_get hs).symm
  have hb := hbefore _ hle
  revert hb hw
  generalize (S.pcmp (Nat.find hex) a b).get hs = w
  intro hw hb
  cases v <;> cases w <;> simp_all

/-- `cmpT a b` is the value of `pcmp` at the first round where it is defined. -/
theorem cmpT_eq_first {r : ℕ} {a b : X} {v : Bool} (h : S.pcmp r a b = some v)
    (hbefore : ∀ r' < r, S.pcmp r' a b = none) : S.cmpT a b = v := by
  refine S.cmpT_eq_of h fun r' hr' => ?_
  rcases lt_or_eq_of_le hr' with h' | rfl
  · rw [hbefore r' h']; simp
  · rw [h]; cases v <;> simp

open Classical in
theorem cmpT_spec {a b : X} (hex : ∃ r, (S.pcmp r a b).isSome) :
    ∃ r, S.pcmp r a b = some (S.cmpT a b) := by
  refine ⟨Nat.find hex, ?_⟩
  unfold cmpT
  rw [dif_pos hex]
  simp

/-- The global comparator is a total tournament. -/
theorem cmpT_total : TotalCmp S.cmpT := by
  classical
  intro a b
  by_cases hab : a = b
  · subst hab
    left; exact S.cmpT_eq_of (r := 0) (S.pcmp_self 0 a) (fun r' _ => by simp [S.pcmp_self])
  by_cases hex : ∃ r, (S.pcmp r a b).isSome
  · set k := Nat.find hex
    have hs := Nat.find_spec hex
    have hw : S.pcmp k a b = some ((S.pcmp k a b).get hs) := (Option.some_get hs).symm
    have hbef : ∀ r' < k, S.pcmp r' a b = none := fun r' hr' => by
      have := Nat.find_min hex hr'
      simpa using this
    have h1 := S.cmpT_eq_first hw hbef
    have h2 := S.cmpT_eq_first (S.pcmp_symm hab hw) (fun r' hr' => by
      have := hbef r' hr'
      have e := S.pcmp_isSome_symm r' a b
      rw [this] at e
      cases h : S.pcmp r' b a
      · rfl
      · rw [h] at e; simp at e)
    rw [h1, h2]
    cases (S.pcmp k a b).get hs <;> simp
  · have hex' : ¬ ∃ r, (S.pcmp r b a).isSome := fun ⟨r, hr⟩ =>
      hex ⟨r, by rw [S.pcmp_isSome_symm]; exact hr⟩
    unfold cmpT
    rw [dif_neg hex, dif_neg hex', S.tb_anti a b hab]
    cases S.tb b a <;> simp

/-! ### Lemma 6.3 (boundary consistency), repaired score -/

/-- **Key step of Lemma 6.3, Case 2**, with the score counting all replicas: if `z` is solid and
`m` is blank at round `r`, then `cmp_T(z, m) = True`. -/
theorem cmpT_solid_blank {r : ℕ} {z m : X} (hz : S.Solid S.scoreAll r z)
    (hm : ¬ S.NonBlank S.scoreAll r m) : S.cmpT z m = true := by
  unfold Solid at hz; unfold NonBlank at hm
  have hzm : z ≠ m := by rintro rfl; omega
  -- `W_{r'}(m, z) ≤ score_r(m)` for `r' ≤ r`
  have hWmz : ∀ r' ≤ r, S.W r' m z ≤ S.scoreAll r m := fun r' hr' =>
    card_le_card fun i hi => by
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact (S.L_prefix_of_le hr' i).subset hi.1
  -- `W_r(z, m) ≥ score_r(z) - score_r(m)`
  have hWzm : S.scoreAll r z - S.scoreAll r m ≤ S.W r z m := by
    have hsub : (univ.filter fun i => z ∈ S.L r i) ⊆
        (univ.filter fun i => Before (S.L r i) z m) ∪ (univ.filter fun i => m ∈ S.L r i) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and, mem_union] at hi ⊢
      by_cases hmi : m ∈ S.L r i
      · exact Or.inr hmi
      · exact Or.inl ⟨hi, fun h => absurd h hmi⟩
    have := (card_le_card hsub).trans (card_union_le _ _)
    unfold scoreAll W; omega
  refine S.cmpT_eq_of (r := r) ?_ fun r' hr' => S.pcmp_ne_false (by
    unfold Heavy; have := hWmz r' hr'; omega)
  unfold pcmp
  have h1 := hWmz r le_rfl
  simp only [hzm, if_false]
  rw [if_neg (by unfold Heavy; omega), if_pos (by omega)]

/-! ### Theorem 6.4 -/

/-- The invariant maintained by FEAT after round `r` (state `(FO, Tail)`):
`FO ++ Tail` is consistent and duplicate-free, all its transactions are non-blank, and the last
finalized transaction is solid. -/
structure Inv (score : ℕ → X → ℕ) (r : ℕ) (st : List X × List X) : Prop where
  acc : AdjConsistent S.cmpT (st.1 ++ st.2)
  nodup : (st.1 ++ st.2).Nodup
  nonblank : ∀ x ∈ st.1 ++ st.2, S.NonBlank score r x
  last_solid : ∀ z ∈ st.1.getLast?, S.Solid score r z

variable {S}

theorem inv_step {score : ℕ → X → ℕ} (hmono : ∀ r x, score r x ≤ score (r + 1) x)
    (hcase2 : ∀ r z m, S.Solid score r z → ¬ S.NonBlank score r m → S.cmpT z m = true)
    {ins : ℕ → List X} (hins : S.InsOK score ins) {bal : BTree X → BTree X}
    (hbal : ∀ t, (bal t).inorder = t.inorder) {r : ℕ} {st : List X × List X}
    (hinv : S.Inv score r st) : S.Inv score (r + 1) (S.step score ins bal (r + 1) st) := by
  obtain ⟨FO, Tail⟩ := st
  obtain ⟨hacc, hnd, hnb, hlast⟩ := hinv
  simp only at hacc hnd hnb hlast
  set RO := S.RO ins bal (r + 1)
  set M := List.merge Tail RO S.cmpT
  have hROacc : AdjConsistent S.cmpT RO := lemma_6_1 S.cmpT_total bal hbal _
  have hROperm : RO.Perm (ins (r + 1)) := buildTree_perm _ bal hbal _
  have hROnew : ∀ x ∈ RO, S.NonBlank score (r + 1) x ∧ ¬ S.NonBlank score r x :=
    fun x hx => hins.new r x (hROperm.subset hx)
  have hTacc : AdjConsistent S.cmpT Tail := hacc.right_of_append
  have hFacc : AdjConsistent S.cmpT FO := hacc.left_of_append
  have hMperm : M.Perm (Tail ++ RO) := List.merge_perm_append _
  have hst : S.step score ins bal (r + 1) (FO, Tail) =
      (FO ++ (cutLast (fun x => decide (S.Solid score (r + 1) x)) M).1,
        (cutLast (fun x => decide (S.Solid score (r + 1) x)) M).2) := rfl
  have happ : (S.step score ins bal (r + 1) (FO, Tail)).1 ++
      (S.step score ins bal (r + 1) (FO, Tail)).2 = FO ++ M := by
    rw [hst]; simp only [List.append_assoc, cutLast_append]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ACC (Lemmas 6.2 and 6.3)
    rw [happ]
    rcases List.eq_nil_or_concat FO with hF | ⟨F, z, hF⟩
    · subst hF; simpa using lemma_6_2 S.cmpT_total hTacc hROacc
    · subst hF
      simp only [List.concat_eq_append] at *
      have hz : S.Solid score r z := hlast z (by simp)
      have hzT : ∀ a ∈ Tail.head?, S.cmpT z a = true := by
        intro a ha
        have := List.isChain_append.1 (show AdjConsistent S.cmpT ((F ++ [z]) ++ Tail) from hacc)
        exact this.2.2 z (by simp) a ha
      have hzR : ∀ b ∈ RO.head?, S.cmpT z b = true := by
        intro b hb
        exact hcase2 r z b hz (hROnew b (List.mem_of_mem_head? hb)).2
      have hzM := isChain_cons_merge S.cmpT_total Tail RO z hTacc hROacc hzT hzR
      have hF' : AdjConsistent S.cmpT (F ++ [z]) := hFacc
      unfold AdjConsistent at hzM hF' ⊢
      rw [List.append_assoc, List.singleton_append]
      refine List.isChain_append.2 ⟨hF'.left_of_append, hzM, ?_⟩
      intro x hx y hy
      simp at hy; subst hy
      exact (List.isChain_append.1 hF').2.2 x hx z (by simp)
  · -- no duplicates
    rw [happ]
    refine (List.Perm.nodup_iff ((hMperm.append_left FO).trans
      (show (FO ++ (Tail ++ RO)).Perm (FO ++ Tail ++ RO) by rw [List.append_assoc]))).2 ?_
    refine List.nodup_append.2 ⟨hnd, (hROperm.nodup_iff).2 (hins.nodup _), ?_⟩
    intro a ha b hb hab
    subst hab
    exact (hROnew a hb).2 (hnb a ha)
  · -- non-blank
    rw [happ]
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact le_trans (hnb x (List.mem_append_left _ h)) (by have := hmono r x; omega)
    · rcases List.mem_append.1 (hMperm.subset h) with h | h
      · exact le_trans (hnb x (List.mem_append_right _ h)) (by have := hmono r x; omega)
      · exact (hROnew x h).1
  · -- the last finalized transaction is solid
    rw [hst]
    intro z hz
    simp only at hz
    by_cases hq : (cutLast (fun x => decide (S.Solid score (r + 1) x)) M).1 = []
    · rw [hq, List.append_nil] at hz
      exact le_trans (hlast z hz) (hmono r z)
    · rw [List.getLast?_append_of_ne_nil _ hq] at hz
      simpa using cutLast_getLast _ M z hz

theorem inv_run {score : ℕ → X → ℕ} (hmono : ∀ r x, score r x ≤ score (r + 1) x)
    (hcase2 : ∀ r z m, S.Solid score r z → ¬ S.NonBlank score r m → S.cmpT z m = true)
    {ins : ℕ → List X} (hins : S.InsOK score ins) {bal : BTree X → BTree X}
    (hbal : ∀ t, (bal t).inorder = t.inorder) (r : ℕ) :
    S.Inv score r (S.run score ins bal r) := by
  induction r with
  | zero => exact ⟨by simp [AdjConsistent, run], by simp [run], by simp [run], by simp [run]⟩
  | succ r ih => exact inv_step hmono hcase2 hins hbal ih

/-- **Lemma 6.3 (boundary consistency), repaired.** With the score counting all replicas: if
`z` is the last transaction of `FO_r` and `m` the head of `Merged_{r+1}`, then
`cmp_T(z, m) = True`. -/
theorem lemma_6_3 {ins : ℕ → List X} (hins : S.InsOK S.scoreAll ins)
    {bal : BTree X → BTree X} (hbal : ∀ t, (bal t).inorder = t.inorder) (r : ℕ) :
    ∀ z ∈ (S.FO S.scoreAll ins bal r).getLast?,
    ∀ m ∈ (List.merge (S.run S.scoreAll ins bal r).2 (S.RO ins bal (r + 1)) S.cmpT).head?,
      S.cmpT z m = true := by
  intro z hz m hm
  have hinv := inv_step (fun r x => S.scoreAll_mono (Nat.le_succ r) x)
    (fun _ _ _ => S.cmpT_solid_blank) hins hbal
    (inv_run (fun r x => S.scoreAll_mono (Nat.le_succ r) x) (fun _ _ _ => S.cmpT_solid_blank)
      hins hbal r)
  have hacc := hinv.acc
  generalize hst : S.run S.scoreAll ins bal r = st at hz hm hacc
  obtain ⟨F₀, T₀⟩ := st
  simp only [Setup.FO, hst] at hz
  simp only [step] at hacc hm
  rw [List.append_assoc, cutLast_append] at hacc
  rcases List.eq_nil_or_concat F₀ with hF | ⟨F, z', hF⟩
  · subst hF; simp at hz
  · subst hF
    simp only [List.concat_eq_append] at *
    simp at hz; subst hz
    unfold AdjConsistent at hacc
    rw [List.append_assoc, List.singleton_append] at hacc
    exact (List.isChain_cons.1 (List.isChain_append.1 hacc).2.1).1 m hm

/-- **Theorem 6.4 (ACC of the final ordering), repaired.** With the score counting all replicas,
for every round `r`, every admissible insertion order and every in-order-preserving rebalancing,
the final ordering `FO_r` satisfies Adjacent-Comparator Consistency. -/
theorem theorem_6_4 {ins : ℕ → List X} (hins : S.InsOK S.scoreAll ins)
    {bal : BTree X → BTree X} (hbal : ∀ t, (bal t).inorder = t.inorder) (r : ℕ) :
    AdjConsistent S.cmpT (S.FO S.scoreAll ins bal r) :=
  (inv_run (fun r x => S.scoreAll_mono (Nat.le_succ r) x) (fun _ _ _ => S.cmpT_solid_blank)
    hins hbal r).acc.left_of_append

/-- The final ordering is duplicate-free. -/
theorem FO_nodup {ins : ℕ → List X} (hins : S.InsOK S.scoreAll ins)
    {bal : BTree X → BTree X} (hbal : ∀ t, (bal t).inorder = t.inorder) (r : ℕ) :
    (S.FO S.scoreAll ins bal r).Nodup :=
  (inv_run (fun r x => S.scoreAll_mono (Nat.le_succ r) x) (fun _ _ _ => S.cmpT_solid_blank)
    hins hbal r).nodup.sublist (List.sublist_append_left _ _)

/-- `FO` only grows: transactions are finalized permanently. -/
theorem FO_prefix (score : ℕ → X → ℕ) (ins : ℕ → List X) (bal : BTree X → BTree X) (r : ℕ) :
    S.FO score ins bal r <+: S.FO score ins bal (r + 1) := by
  simp only [FO, run, step]
  exact List.prefix_append _ _

/-! ### Lemma 6.5 and Theorem 6.6 -/

/-- **Lemma 6.5 (FEAT comparator is γ-induced).** If `1/2 < γ`, `n > (2γ+1)f/(2γ−1)` and at
least a `γ`-fraction of the honest replicas receive `a` before `b`, then `cmp_T(a, b) = True`.
(This does not depend on the score.) -/
theorem lemma_6_5 {γ : ℝ} (hγ : 1 / 2 < γ) (hn : (2 * γ + 1) * S.f / (2 * γ - 1) < S.n)
    {a b : X} (hG : S.GammaPrec γ a b) : S.cmpT a b = true := by
  classical
  by_cases hab : a = b
  · subst hab; exact S.cmpT_eq_of (r := 0) (S.pcmp_self 0 a) (fun r' _ => by simp [S.pcmp_self])
  have h2γ : 0 < 2 * γ - 1 := by linarith
  have hHc : S.n = S.H.card + (univ \ S.H).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ]
    have := card_le_univ S.H
    simp only [Setup.n]
    omega
  have hbyz := S.card_byz
  -- `n > f`
  have hnf : (S.f : ℝ) < S.n := by
    have : (S.f : ℝ) ≤ (2 * γ + 1) * S.f / (2 * γ - 1) := by
      rw [le_div_iff₀ h2γ]; nlinarith [(Nat.cast_nonneg S.f : (0 : ℝ) ≤ S.f)]
    linarith
  have hnf' : S.f < S.n := by exact_mod_cast hnf
  set cnt := (S.H.filter fun i => Before (S.recv i) a b).card
  have hHpos : 0 < S.H.card := by omega
  have hcnt : (0 : ℝ) < cnt := by
    have : (0 : ℝ) < γ * S.H.card := mul_pos (by linarith) (by exact_mod_cast hHpos)
    exact lt_of_lt_of_le this hG
  -- some honest replica receives `a`, hence eventually all honest replicas commit `a`
  obtain ⟨i, hi⟩ : (S.H.filter fun i => Before (S.recv i) a b).Nonempty := by
    rw [← card_pos]; exact_mod_cast hcnt
  rw [mem_filter] at hi
  obtain ⟨r₀, hr₀⟩ := S.eventually i hi.1 a hi.2.1
  -- so the pair is decided at round `r₀`
  have hdec : ∃ r, (S.pcmp r a b).isSome := by
    refine ⟨r₀, ?_⟩
    have hsum : S.H.card ≤ S.W r₀ a b + S.W r₀ b a := by
      have : S.H ⊆ (univ.filter fun j => Before (S.L r₀ j) a b) ∪
          (univ.filter fun j => Before (S.L r₀ j) b a) := by
        intro j hj
        simp only [mem_union, mem_filter, mem_univ, true_and]
        exact before_total hab (Or.inl (hr₀ j hj))
      exact (card_le_card this).trans (card_union_le _ _)
    unfold pcmp
    simp only [hab, if_false]
    rw [if_neg (by unfold Heavy; omega)]
    split_ifs <;> simp
  obtain ⟨r, hr⟩ := S.cmpT_spec hdec
  by_contra hne
  rw [Bool.not_eq_true] at hne
  rw [hne] at hr
  have hheavy := S.heavy_of_pcmp_false hr
  -- bound `W_r(b, a) ≤ n − cnt`
  have hW : S.W r b a ≤ S.n - cnt := by
    have hsub : (univ.filter fun j => Before (S.L r j) b a) ⊆
        (S.H.filter fun j => ¬ Before (S.recv j) a b) ∪ (univ \ S.H) := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_sdiff] at hj ⊢
      by_cases hjH : j ∈ S.H
      · exact Or.inl ⟨hjH, not_before_of_prefix (S.L_prefix_recv r j hjH) hj⟩
      · exact Or.inr hjH
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    have h2 := card_filter_add_card_filter_not (s := S.H) (fun j => Before (S.recv j) a b)
    unfold W; omega
  unfold Heavy at hheavy
  -- arithmetic contradiction with `n > (2γ+1)f/(2γ−1)`
  have hHr : ((S.n : ℝ) - S.f) ≤ S.H.card := by
    have : S.n - S.f ≤ S.H.card := by omega
    have := (Nat.cast_le (α := ℝ)).2 this
    rw [Nat.cast_sub hnf'.le] at this; exact this
  have hWr : ((S.n : ℝ) - S.f) ≤ 2 * ((S.n : ℝ) - cnt) := by
    have h1 : S.n - S.f ≤ 2 * (S.n - cnt) := le_trans hheavy (by omega)
    have hc : cnt ≤ S.n := by
      have := card_le_card (filter_subset (fun i => Before (S.recv i) a b) S.H); omega
    have := (Nat.cast_le (α := ℝ)).2 h1
    push_cast [Nat.cast_sub hnf'.le, Nat.cast_sub hc] at this
    exact this
  rw [div_lt_iff₀ h2γ] at hn
  unfold GammaPrec at hG
  have := mul_le_mul_of_nonneg_left hHr (by linarith : (0 : ℝ) ≤ γ)
  nlinarith

/-- **Theorem 6.6 (FEAT achieves γ-Batch-Order-Fairness), repaired.** With the score counting
all replicas, for every round `r` the final ordering `FO_r` satisfies comparator-based
γ-Batch-Order-Fairness (Definition 4.1) with respect to `cmp_T` and the relation "at least a
`γ`-fraction of honest replicas receive `a` before `b`". -/
theorem theorem_6_6 {γ : ℝ} (hγ : 1 / 2 < γ) (hn : (2 * γ + 1) * S.f / (2 * γ - 1) < S.n)
    {ins : ℕ → List X} (hins : S.InsOK S.scoreAll ins)
    {bal : BTree X → BTree X} (hbal : ∀ t, (bal t).inorder = t.inorder) (r : ℕ) :
    BatchOrderFair S.cmpT (S.GammaPrec γ) (S.FO S.scoreAll ins bal r) :=
  theorem_4_4 (fun a _ b _ _ => S.cmpT_total a b)
    (fun _ _ _ _ hG => lemma_6_5 hγ hn hG) (theorem_6_4 hins hbal r)

end Setup

end Podc.FEATOrdering
