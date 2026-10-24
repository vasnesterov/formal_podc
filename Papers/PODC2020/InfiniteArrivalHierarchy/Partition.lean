import Papers.PODC2020.InfiniteArrivalHierarchy.Objects

/-!
# Partitioned executions (Definition 4) for Proposition 4

Infrastructure for the proof of Proposition 4 of Perrin–Mostéfaoui–Bonin (PODC 2020): binary
consensus objects (`consObj Bool`, indexed by `ιc`) and window registers (`windowObj (W j) (w j)`,
indexed by `ιw`), processes `ℕ` with input `p` for process `p`.

A partition of the processes is given by class labels `cls : ℕ → ℕ`. A set `U` of processes is
*saturated* (`Sat cls U`) if it is a union of classes. The *restriction* of an execution `σ` to `U`
is `σ.filter (· ∈ U)` (`rexec A U σ` is its final configuration). Definition 4 of the paper
(`α` is `Π'`-partitioned: the restriction to every class is a valid execution in which the
processes of the class have the same local states) is strengthened here to the invariant `Inv`:

* `loc`: for **every** saturated `U` (union of classes), the processes of `U` have the same local
  states in the restriction to `U` as in the real execution. (The paper only asks this for single
  classes; unions are needed when classes are merged, see `differencies.md`.)
* `untouched`: the objects outside the set `X` of "used" objects are in their initial state in the
  real execution and in every restriction;
* `good`: every binary consensus object `j ∈ X` is undecided-as-initially or decided `dv j` (in the
  real execution and in every restriction), where `dv j` is the initial decision if any and the
  value `b j` proposed by the processes covering it otherwise.

Steps preserving the invariant (`Inv.step`): writes on window registers of `X`, proposals of `b j`
on consensus objects of `X`, and any operation on an object of `X` whose state is the same in the
real execution and in all restrictions containing the stepping process (and is decided, for
consensus objects).
-/

namespace Podc.InfiniteArrivalHierarchy.Prop4

open Cslib.SharedMemory Cslib.SharedMemory.Arrival Classical

set_option linter.unusedSectionVars false

/-- Binary consensus objects `ιc` and window registers `ιw` (value type `W j`, size `w j`). -/
abbrev CW (ιc : Type) {ιw : Type} (W : ιw → Type) (w : ιw → ℕ) : ιc ⊕ ιw → ObjSpec
  | .inl _ => consObj Bool
  | .inr j => windowObj (W j) (w j)

variable {ιc ιw : Type} [DecidableEq ιc] [DecidableEq ιw] {W : ιw → Type} {w : ιw → ℕ}

section Defs

variable (A : Alg (CW ιc W w) ℕ ℕ ℕ)

/-- The final configuration of the restriction of `σ` to the processes of `U` (inputs: process
`p` proposes `p`). -/
noncomputable def rexec (U : Set ℕ) (σ : List ℕ) : Cfg A :=
  A.exec id (σ.filter (fun q => decide (q ∈ U)))

/-- `U` is a union of classes of the partition `cls`. -/
def Sat (cls : ℕ → ℕ) (U : Set ℕ) : Prop := ∀ q q', cls q = cls q' → q ∈ U → q' ∈ U

/-- The value a consensus object `j` decides when the covering processes propose `b j`. -/
def dv (b : ιc → Bool) (j : ιc) : Bool := (A.mem₀ (.inl j) : Option Bool).getD (b j)

/-- Admissible states of the objects of `X`: consensus objects are in their initial state or
decided `dv b j`; no constraint on window registers. -/
def GoodY (b : ιc → Bool) : (y : ιc ⊕ ιw) → (CW ιc W w y).State → Prop
  | .inl j, s => s = A.mem₀ (.inl j) ∨ s = some (dv A b j)
  | .inr _, _ => True

/-- The partition invariant (strengthened Definition 4). -/
structure Inv (σ : List ℕ) (cls : ℕ → ℕ) (X : Finset (ιc ⊕ ιw)) (b : ιc → Bool) : Prop where
  loc : ∀ U, Sat cls U → ∀ q ∈ U, (rexec A U σ).loc q = (A.exec id σ).loc q
  untouched : ∀ y ∉ X, (A.exec id σ).mem y = A.mem₀ y ∧
    ∀ U, Sat cls U → (rexec A U σ).mem y = A.mem₀ y
  good : ∀ y ∈ X, GoodY A b y ((A.exec id σ).mem y) ∧
    ∀ U, Sat cls U → GoodY A b y ((rexec A U σ).mem y)

end Defs

variable {A : Alg (CW ιc W w) ℕ ℕ ℕ}

/-! ### Restrictions -/

lemma rexec_nil (U : Set ℕ) : rexec A U [] = A.initCfg id := rfl

lemma rexec_concat_mem {U : Set ℕ} {q : ℕ} (hq : q ∈ U) (σ : List ℕ) :
    rexec A U (σ ++ [q]) = (rexec A U σ).step q := by
  simp [rexec, List.filter_append, hq, Alg.exec_concat]

lemma rexec_concat_not_mem {U : Set ℕ} {q : ℕ} (hq : q ∉ U) (σ : List ℕ) :
    rexec A U (σ ++ [q]) = rexec A U σ := by
  simp [rexec, List.filter_append, hq]

lemma rexec_append_all {U : Set ℕ} {B : List ℕ} (hB : ∀ q ∈ B, q ∈ U) (σ : List ℕ) :
    rexec A U (σ ++ B) = A.run (rexec A U σ) B := by
  have : B.filter (fun q => decide (q ∈ U)) = B := List.filter_eq_self.2 (by simpa using hB)
  simp [rexec, List.filter_append, this, Alg.exec_append]

lemma rexec_append_none {U : Set ℕ} {B : List ℕ} (hB : ∀ q ∈ B, q ∉ U) (σ : List ℕ) :
    rexec A U (σ ++ B) = rexec A U σ := by
  have : B.filter (fun q => decide (q ∈ U)) = [] := List.filter_eq_nil_iff.2 (by simpa using hB)
  simp [rexec, List.filter_append, this]

lemma sat_class (cls : ℕ → ℕ) (c : ℕ) : Sat cls {q | cls q = c} := by
  intro q q' h hq; simp only [Set.mem_ofPred_eq] at hq ⊢; rw [← h, hq]

lemma Sat.coarsen {cls cls' : ℕ → ℕ} (h : ∀ q q', cls q = cls q' → cls' q = cls' q') {U : Set ℕ}
    (hU : Sat cls' U) : Sat cls U := fun q q' e hq => hU q q' (h q q' e) hq

/-! ### The invariant -/

namespace Inv

lemma nil (cls : ℕ → ℕ) (b : ιc → Bool) : Inv A [] cls ∅ b :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => ⟨rfl, fun _ _ => rfl⟩, fun _ h => by simp at h⟩

/-- Merging classes preserves the invariant. -/
lemma coarsen {σ : List ℕ} {cls cls' : ℕ → ℕ} {X : Finset (ιc ⊕ ιw)} {b : ιc → Bool}
    (h : Inv A σ cls X b) (hc : ∀ q q', cls q = cls q' → cls' q = cls' q') :
    Inv A σ cls' X b :=
  ⟨fun U hU => h.loc U (hU.coarsen hc), fun y hy => ⟨(h.untouched y hy).1,
    fun U hU => (h.untouched y hy).2 U (hU.coarsen hc)⟩,
   fun y hy => ⟨(h.good y hy).1, fun U hU => (h.good y hy).2 U (hU.coarsen hc)⟩⟩

/-- Adding an untouched object to `X` (fixing `b` on it). -/
lemma insert {σ : List ℕ} {cls : ℕ → ℕ} {X : Finset (ιc ⊕ ιw)} {b b' : ιc → Bool}
    (h : Inv A σ cls X b) {y : ιc ⊕ ιw} (hy : y ∉ X)
    (hb : ∀ j, (.inl j : ιc ⊕ ιw) ∈ X → b' j = b j) : Inv A σ cls (insert y X) b' := by
  have hgood : ∀ z ∈ X, ∀ s, GoodY A b z s → GoodY A b' z s := by
    intro z hz s hs
    cases z with
    | inl j => simpa [GoodY, dv, hb j hz] using hs
    | inr j => trivial
  have hinit : ∀ s, s = A.mem₀ y → GoodY A b' y s := by
    rintro s rfl; cases y with
    | inl j => left; rfl
    | inr j => trivial
  refine ⟨h.loc, fun z hz => h.untouched z (fun h' => hz (Finset.mem_insert_of_mem h')), ?_⟩
  intro z hz
  rcases Finset.mem_insert.1 hz with rfl | hz
  · exact ⟨hinit _ (h.untouched z hy).1, fun U hU => hinit _ ((h.untouched z hy).2 U hU)⟩
  · exact ⟨hgood z hz _ (h.good z hz).1, fun U hU => hgood z hz _ ((h.good z hz).2 U hU)⟩

/-- **Step lemma.** A step of `q` on an object `y ∈ X` preserves the invariant if its response is
the same in the real execution and in every restriction containing `q`, and the new states of `y`
are admissible. -/
lemma step {σ : List ℕ} {cls : ℕ → ℕ} {X : Finset (ιc ⊕ ιw)} {b : ιc → Bool}
    (h : Inv A σ cls X b) {q : ℕ} {y : ιc ⊕ ιw} {o : (CW ιc W w y).Op}
    {k : (CW ιc W w y).Resp → A.L} (hq : A.act ((A.exec id σ).loc q) = .access y o k)
    (hy : y ∈ X)
    (hresp : ∀ U, Sat cls U → q ∈ U →
      ((CW ιc W w y).δ ((rexec A U σ).mem y) o).2 = ((CW ιc W w y).δ ((A.exec id σ).mem y) o).2)
    (hgR : GoodY A b y ((CW ιc W w y).δ ((A.exec id σ).mem y) o).1)
    (hgU : ∀ U, Sat cls U → q ∈ U → GoodY A b y ((CW ιc W w y).δ ((rexec A U σ).mem y) o).1) :
    Inv A (σ ++ [q]) cls X b := by
  have hR : A.exec id (σ ++ [q]) = (A.exec id σ).step q := Alg.exec_concat _ _ _
  have hRmem : ∀ z, z ≠ y → (A.exec id (σ ++ [q])).mem z = (A.exec id σ).mem z := by
    intro z hz; rw [hR]; exact Cfg.step_mem_other hq hz
  have hRy : (A.exec id (σ ++ [q])).mem y = ((CW ιc W w y).δ ((A.exec id σ).mem y) o).1 := by
    rw [hR]; exact Cfg.step_mem_self_of_access hq
  have hRloc : (A.exec id (σ ++ [q])).loc q = k ((CW ιc W w y).δ ((A.exec id σ).mem y) o).2 := by
    rw [hR]; exact Cfg.step_loc_self_of_access hq
  have hRlocO : ∀ q', q' ≠ q → (A.exec id (σ ++ [q])).loc q' = (A.exec id σ).loc q' := by
    intro q' h'; rw [hR]; exact Cfg.step_loc_other _ h'
  -- restrictions containing `q`
  have hU : ∀ U, Sat cls U → q ∈ U →
      (∀ z, z ≠ y → (rexec A U (σ ++ [q])).mem z = (rexec A U σ).mem z) ∧
      (rexec A U (σ ++ [q])).mem y = ((CW ιc W w y).δ ((rexec A U σ).mem y) o).1 ∧
      (rexec A U (σ ++ [q])).loc q = k ((CW ιc W w y).δ ((rexec A U σ).mem y) o).2 ∧
      (∀ q', q' ≠ q → (rexec A U (σ ++ [q])).loc q' = (rexec A U σ).loc q') := by
    intro U hUs hqU
    have hq' : A.act ((rexec A U σ).loc q) = .access y o k := by rw [h.loc U hUs q hqU]; exact hq
    rw [rexec_concat_mem hqU]
    exact ⟨fun z hz => Cfg.step_mem_other hq' hz, Cfg.step_mem_self_of_access hq',
      Cfg.step_loc_self_of_access hq', fun q' h' => Cfg.step_loc_other _ h'⟩
  refine ⟨?_, ?_, ?_⟩
  · intro U hUs q' hq'U
    by_cases hqU : q ∈ U
    · obtain ⟨-, -, h3, h4⟩ := hU U hUs hqU
      by_cases e : q' = q
      · subst e; rw [h3, hRloc, hresp U hUs hqU]
      · rw [h4 q' e, hRlocO q' e, h.loc U hUs q' hq'U]
    · have e : q' ≠ q := fun e => hqU (e ▸ hq'U)
      rw [rexec_concat_not_mem hqU, hRlocO q' e, h.loc U hUs q' hq'U]
  · intro z hz
    have hzy : z ≠ y := fun e => hz (e ▸ hy)
    refine ⟨by rw [hRmem z hzy]; exact (h.untouched z hz).1, fun U hUs => ?_⟩
    by_cases hqU : q ∈ U
    · rw [(hU U hUs hqU).1 z hzy]; exact (h.untouched z hz).2 U hUs
    · rw [rexec_concat_not_mem hqU]; exact (h.untouched z hz).2 U hUs
  · intro z hz
    by_cases hzy : z = y
    · subst hzy
      refine ⟨by rw [hRy]; exact hgR, fun U hUs => ?_⟩
      by_cases hqU : q ∈ U
      · rw [(hU U hUs hqU).2.1]; exact hgU U hUs hqU
      · rw [rexec_concat_not_mem hqU]; exact (h.good z hz).2 U hUs
    · refine ⟨by rw [hRmem z hzy]; exact (h.good z hz).1, fun U hUs => ?_⟩
      by_cases hqU : q ∈ U
      · rw [(hU U hUs hqU).1 z hzy]; exact (h.good z hz).2 U hUs
      · rw [rexec_concat_not_mem hqU]; exact (h.good z hz).2 U hUs

/-- A write on a window register of `X` preserves the invariant. -/
lemma step_write {σ : List ℕ} {cls : ℕ → ℕ} {X : Finset (ιc ⊕ ιw)} {b : ιc → Bool}
    (h : Inv A σ cls X b) {q : ℕ} {j : ιw} {v : W j} {k : List (W j) → A.L}
    (hq : A.act ((A.exec id σ).loc q) = .access (.inr j) (.write v) k) (hy : .inr j ∈ X) :
    Inv A (σ ++ [q]) cls X b :=
  h.step hq hy (fun _ _ _ => rfl) trivial (fun _ _ _ => trivial)

lemma good_inl_iff {b : ιc → Bool} {j : ιc} {s : Option Bool} :
    GoodY A b (.inl j) s ↔ s = A.mem₀ (.inl j) ∨ s = some (dv A b j) := Iff.rfl

/-- On an admissible state, the proposal of `b j` returns `dv b j` and decides it. -/
lemma propose_good {b : ιc → Bool} {j : ιc} {s : Option Bool} (hs : GoodY A b (.inl j) s) :
    s.getD (b j) = dv A b j := by
  rcases hs with rfl | rfl
  · rfl
  · rfl

/-- A proposal of `b j` on a consensus object of `X` preserves the invariant. -/
lemma step_propose {σ : List ℕ} {cls : ℕ → ℕ} {X : Finset (ιc ⊕ ιw)} {b : ιc → Bool}
    (h : Inv A σ cls X b) {q : ℕ} {j : ιc} {k : Bool → A.L}
    (hq : A.act ((A.exec id σ).loc q) = .access (.inl j) (b j) k) (hy : .inl j ∈ X) :
    Inv A (σ ++ [q]) cls X b := by
  refine h.step hq hy (fun U hU _ => ?_) ?_ (fun U hU _ => ?_)
  · show ((rexec A U σ).mem (.inl j) : Option Bool).getD (b j) =
      ((A.exec id σ).mem (.inl j) : Option Bool).getD (b j)
    rw [Inv.propose_good ((h.good _ hy).2 U hU), Inv.propose_good (h.good _ hy).1]
  · right; show some (((A.exec id σ).mem (.inl j) : Option Bool).getD (b j)) = _
    rw [Inv.propose_good (h.good _ hy).1]
  · right; show some (((rexec A U σ).mem (.inl j) : Option Bool).getD (b j)) = _
    rw [Inv.propose_good ((h.good _ hy).2 U hU)]

end Inv

/-! ### Covering, blocks -/

section Block

variable (A) in
/-- `q` *covers* `y` in `C`: it is poised to write on the window register `y`, or to propose
`b j` on the consensus object `y = j` (Definition 5). -/
def Covers (C : Cfg A) (b : ιc → Bool) (q : ℕ) : (ιc ⊕ ιw) → Prop
  | .inl j => ∃ k, A.act (C.loc q) = .access (.inl j) (b j) k
  | .inr j => ∃ v k, A.act (C.loc q) = .access (.inr j) (.write v) k

lemma Covers.poised {C : Cfg A} {b : ιc → Bool} {q : ℕ} {y : ιc ⊕ ιw} (h : Covers A C b q y) :
    C.Poised q y := by
  cases y with
  | inl j => obtain ⟨k, hk⟩ := h; exact ⟨_, k, hk⟩
  | inr j => obtain ⟨v, k, hk⟩ := h; exact ⟨_, k, hk⟩

lemma Covers.of_loc {C D : Cfg A} {b : ιc → Bool} {q : ℕ} {y : ιc ⊕ ιw}
    (h : Covers A C b q y) (e : D.loc q = C.loc q) : Covers A D b q y := by
  cases y with
  | inl j => obtain ⟨k, hk⟩ := h; exact ⟨k, by rw [e]; exact hk⟩
  | inr j => obtain ⟨v, k, hk⟩ := h; exact ⟨v, k, by rw [e]; exact hk⟩

/-- The memory of the restriction to `U` is the real memory. -/
def MemEq (σ : List ℕ) (U : Set ℕ) : Prop := (rexec A U σ).mem = (A.exec id σ).mem

/-- All consensus objects of `X` are decided (`dv b j`) in the real execution. -/
def Decided (σ : List ℕ) (X : Finset (ιc ⊕ ιw)) (b : ιc → Bool) : Prop :=
  ∀ j, (.inl j : ιc ⊕ ιw) ∈ X → ((A.exec id σ).mem (.inl j) : Option Bool) = some (dv A b j)

variable {σ : List ℕ} {cls : ℕ → ℕ} {X : Finset (ιc ⊕ ιw)} {b : ιc → Bool}

/-- A block of covering steps preserves the invariant. -/
theorem Inv.block (h : Inv A σ cls X b) (Φ : List ℕ) (hnd : Φ.Nodup) (obj : ℕ → ιc ⊕ ιw)
    (hcov : ∀ q ∈ Φ, obj q ∈ X ∧ Covers A (A.exec id σ) b q (obj q)) :
    Inv A (σ ++ Φ) cls X b := by
  induction Φ generalizing σ with
  | nil => simpa using h
  | cons q Φ ih =>
    obtain ⟨hqΦ, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨hX, hc⟩ := hcov q (by simp)
    have h1 : Inv A (σ ++ [q]) cls X b := by
      revert hX hc
      cases obj q with
      | inl j => intro hX hc; obtain ⟨k, hk⟩ := hc; exact h.step_propose hk hX
      | inr j => intro hX hc; obtain ⟨v, k, hk⟩ := hc; exact h.step_write hk hX
    have := ih h1 hnd' (fun r hr => ⟨(hcov r (by simp [hr])).1,
      (hcov r (by simp [hr])).2.of_loc (by
        rw [Alg.exec_concat]; exact Cfg.step_loc_other _ (fun e => hqΦ (e ▸ hr)))⟩)
    simpa using this

lemma runOps_propose_good {j : ιc} {s : Option Bool} (hs : GoodY A b (.inl j) s) (n : ℕ) :
    (CW ιc W w (.inl j)).runOps s (List.replicate (n + 1) (b j)) = some (dv A b j) := by
  induction n generalizing s with
  | zero => show some (s.getD (b j)) = _; rw [Inv.propose_good hs]
  | succ n ih =>
    rw [List.replicate_succ, ObjSpec.runOps_cons]
    apply ih
    show GoodY A b (.inl j) (some (s.getD (b j)))
    right; rw [Inv.propose_good hs]

/-- After a block in which every object of `X` is covered at least once, and every window
register `j` of `X` at least `w j` times, the memory of every restriction containing the block
is the real memory, and all consensus objects of `X` are decided. -/
theorem Inv.block_memEq (h : Inv A σ cls X b) (Φ : List ℕ) (hnd : Φ.Nodup)
    (obj : ℕ → ιc ⊕ ιw) (hcov : ∀ q ∈ Φ, obj q ∈ X ∧ Covers A (A.exec id σ) b q (obj q))
    (hcnt : ∀ y ∈ X, 1 ≤ (Φ.filter (fun q => decide (obj q = y))).length ∧
      ∀ j, y = .inr j → w j ≤ (Φ.filter (fun q => decide (obj q = y))).length)
    (U : Set ℕ) (hU : Sat cls U) (hΦU : ∀ q ∈ Φ, q ∈ U) :
    MemEq (A := A) (σ ++ Φ) U ∧ Decided (A := A) (σ ++ Φ) X b := by
  have h' := h.block Φ hnd obj hcov
  have eR : A.exec id (σ ++ Φ) = A.run (A.exec id σ) Φ := Alg.exec_append _ _ _
  have eU : rexec A U (σ ++ Φ) = A.run (rexec A U σ) Φ := rexec_append_all hΦU σ
  have hcovU : ∀ q ∈ Φ, Covers A (rexec A U σ) b q (obj q) := fun q hq =>
    (hcov q hq).2.of_loc (h.loc U hU q (hΦU q hq))
  -- generic computation of the state of `y ∈ X` after the block
  have key : ∀ y ∈ X, (rexec A U (σ ++ Φ)).mem y = (A.exec id (σ ++ Φ)).mem y ∧
      ∀ j, y = .inl j →
        ((A.exec id (σ ++ Φ)).mem (.inl j) : Option Bool) = some (dv A b j) := by
    intro y hy
    obtain ⟨h1, h2⟩ := hcnt y hy
    obtain ⟨q₀, hq₀⟩ : ∃ q₀, q₀ ∈ Φ.filter (fun q => decide (obj q = y)) :=
      List.exists_mem_of_length_pos h1
    simp only [List.mem_filter, decide_eq_true_eq] at hq₀
    have hoff : ∀ C : Cfg A, (∀ q ∈ Φ, Covers A C b q (obj q)) →
        ∀ q ∈ Φ, ¬ obj q = y → ∃ z, z ≠ y ∧ C.Poised q z :=
      fun C hC q hq hne => ⟨obj q, hne, (hC q hq).poised⟩
    cases y with
    | inr j =>
      have hc₀ := (hcov q₀ hq₀.1).2
      rw [hq₀.2] at hc₀
      obtain ⟨v₀, k₀, -⟩ := hc₀
      have : Nonempty (W j) := ⟨v₀⟩
      have : Nonempty (List (W j) → A.L) := ⟨k₀⟩
      have hex : ∀ q, q ∈ Φ ∧ obj q = .inr j → ∃ v k,
          A.act ((A.exec id σ).loc q) = .access (.inr j) (.write v) k := by
        rintro q ⟨hq, he⟩; have := (hcov q hq).2; rw [he] at this; exact this
      choose! vv kk hvk using hex
      have hR := Alg.run_on (A.exec id σ) (.inr j) Φ hnd (fun q => obj q = .inr j)
        (fun q => .write (vv q)) [] kk (fun _ => True) trivial
        (fun _ _ _ _ _ => ⟨rfl, trivial⟩) (fun q hq he => hvk q ⟨hq, he⟩)
        (hoff _ (fun q hq => (hcov q hq).2))
      have hUr := Alg.run_on (rexec A U σ) (.inr j) Φ hnd (fun q => obj q = .inr j)
        (fun q => .write (vv q)) [] kk (fun _ => True) trivial
        (fun _ _ _ _ _ => ⟨rfl, trivial⟩)
        (fun q hq he => by rw [h.loc U hU q (hΦU q hq)]; exact hvk q ⟨hq, he⟩)
        (hoff _ hcovU)
      refine ⟨?_, fun j' e => by cases e⟩
      rw [eR, eU, hR.1, hUr.1]
      set L := (Φ.filter (fun q => decide (obj q = .inr j))).map vv with hL
      have hmap : (Φ.filter (fun q => decide (obj q = .inr j))).map
          (fun q => (WinOp.write (vv q) : WinOp (W j))) = L.map WinOp.write := by
        simp [hL]
      have hlen : w j ≤ L.length := by rw [hL, List.length_map]; exact h2 j rfl
      have hne : L ≠ [] := by
        rw [hL]; intro e
        rw [List.map_eq_nil_iff] at e
        rw [e] at h1; simp at h1
      obtain ⟨u, us, hu⟩ := List.exists_cons_of_ne_nil hne
      show (windowObj (W j) (w j)).runOps _ _ = (windowObj (W j) (w j)).runOps _ _
      rw [hmap, hu, windowObj_runOps_writes, windowObj_runOps_writes, ← hu,
        List.drop_length_sub_append_eq _ hlen, List.drop_length_sub_append_eq _ hlen]
    | inl j =>
      have hc₀ := (hcov q₀ hq₀.1).2
      rw [hq₀.2] at hc₀
      obtain ⟨k₀, -⟩ := hc₀
      have : Nonempty (Bool → A.L) := ⟨k₀⟩
      have hex : ∀ q, q ∈ Φ ∧ obj q = .inl j → ∃ k,
          A.act ((A.exec id σ).loc q) = .access (.inl j) (b j) k := by
        rintro q ⟨hq, he⟩; have := (hcov q hq).2; rw [he] at this; exact this
      choose! kk hvk using hex
      have hbl : ∀ q ∈ Φ, obj q = .inl j → ∀ s, GoodY A b (.inl j) s →
          ((CW ιc W w (.inl j)).δ s (b j)).2 = dv A b j ∧
            GoodY A b (.inl j) ((CW ιc W w (.inl j)).δ s (b j)).1 := by
        intro q _ _ s hs
        refine ⟨Inv.propose_good hs, ?_⟩
        show GoodY A b (.inl j) (some (s.getD (b j)))
        right; rw [Inv.propose_good hs]
      have hR := Alg.run_on (A.exec id σ) (.inl j) Φ hnd (fun q => obj q = .inl j)
        (fun _ => b j) (dv A b j) kk (GoodY A b (.inl j)) (h.good _ hy).1 hbl
        (fun q hq he => hvk q ⟨hq, he⟩) (hoff _ (fun q hq => (hcov q hq).2))
      have hUr := Alg.run_on (rexec A U σ) (.inl j) Φ hnd (fun q => obj q = .inl j)
        (fun _ => b j) (dv A b j) kk (GoodY A b (.inl j)) ((h.good _ hy).2 U hU) hbl
        (fun q hq he => by rw [h.loc U hU q (hΦU q hq)]; exact hvk q ⟨hq, he⟩)
        (hoff _ hcovU)
      have hlen := h1
      obtain ⟨n, hn⟩ : ∃ n, (Φ.filter (fun q => decide (obj q = .inl j))).length = n + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos h1).symm⟩
      have hrep : (Φ.filter (fun q => decide (obj q = .inl j))).map (fun _ => b j) =
          List.replicate (n + 1) (b j) := by
        rw [List.map_const', hn]
      have eRy : ((A.exec id (σ ++ Φ)).mem (.inl j) : Option Bool) = some (dv A b j) := by
        rw [eR, hR.1, hrep]; exact runOps_propose_good (h.good _ hy).1 n
      refine ⟨?_, fun j' e => by cases e; exact eRy⟩
      rw [eRy, eU, hUr.1, hrep]; exact runOps_propose_good ((h.good _ hy).2 U hU) n
  refine ⟨?_, fun j hj => (key _ hj).2 j rfl⟩
  funext y
  by_cases hy : y ∈ X
  · exact (key y hy).1
  · rw [(h'.untouched y hy).2 U (fun q q' e hq => hU q q' e hq), (h'.untouched y hy).1]

/-- A solo step of `p` on an object of `X`, when the memory of every restriction containing `p` is
the real one and the consensus objects of `X` are decided, preserves everything. -/
theorem Inv.solo_step (h : Inv A σ cls X b) {p : ℕ}
    (hM : ∀ U, Sat cls U → p ∈ U → MemEq (A := A) σ U) (hD : Decided (A := A) σ X b)
    {y : ιc ⊕ ιw} (hy : y ∈ X) (hp : (A.exec id σ).Poised p y) :
    Inv A (σ ++ [p]) cls X b ∧ (∀ U, Sat cls U → p ∈ U → MemEq (A := A) (σ ++ [p]) U) ∧
      Decided (A := A) (σ ++ [p]) X b := by
  obtain ⟨o, k, hk⟩ := hp
  have hgR : GoodY A b y ((CW ιc W w y).δ ((A.exec id σ).mem y) o).1 := by
    cases y with
    | inl j =>
      right; show some (((A.exec id σ).mem (.inl j) : Option Bool).getD o) = _
      rw [hD j hy]; rfl
    | inr j => trivial
  have hInv : Inv A (σ ++ [p]) cls X b :=
    h.step hk hy (fun U hU hpU => by rw [hM U hU hpU]) hgR
      (fun U hU hpU => by rw [hM U hU hpU]; exact hgR)
  refine ⟨hInv, fun U hU hpU => ?_, fun j hj => ?_⟩
  · unfold MemEq
    rw [rexec_concat_mem hpU, Alg.exec_concat]
    have hk' : A.act ((rexec A U σ).loc p) = .access y o k := by
      rw [h.loc U hU p hpU]; exact hk
    rw [Cfg.step_of_access hk, Cfg.step_of_access hk', hM U hU hpU]
  · rw [Alg.exec_concat]
    by_cases e : (.inl j : ιc ⊕ ιw) = y
    · subst e
      rw [Cfg.step_mem_self_of_access hk]
      show some (((A.exec id σ).mem (.inl j) : Option Bool).getD o) = _
      rw [hD j hj]; rfl
    · rw [Cfg.step_mem_other hk e]; exact hD j hj

/-- A read-only step (e.g. a read of any window register) whose response is the same in the real
execution and in every restriction containing the process preserves the invariant. -/
theorem Inv.step_readonly (h : Inv A σ cls X b) {q : ℕ} {y : ιc ⊕ ιw} {o : (CW ιc W w y).Op}
    {k : (CW ιc W w y).Resp → A.L} (hq : A.act ((A.exec id σ).loc q) = .access y o k)
    (hro : ∀ s, ((CW ιc W w y).δ s o).1 = s)
    (hresp : ∀ U, Sat cls U → q ∈ U →
      ((CW ιc W w y).δ ((rexec A U σ).mem y) o).2 = ((CW ιc W w y).δ ((A.exec id σ).mem y) o).2) :
    Inv A (σ ++ [q]) cls X b := by
  have hR : A.exec id (σ ++ [q]) = (A.exec id σ).step q := Alg.exec_concat _ _ _
  have hRmem : (A.exec id (σ ++ [q])).mem = (A.exec id σ).mem := by
    rw [hR, Cfg.step_of_access hq]; simp only [hro, Function.update_eq_self]
  have hUmem : ∀ U, Sat cls U → (rexec A U (σ ++ [q])).mem = (rexec A U σ).mem := by
    intro U hU
    by_cases hqU : q ∈ U
    · have hq'' : A.act ((rexec A U σ).loc q) = .access y o k := by
        rw [h.loc U hU q hqU]; exact hq
      rw [rexec_concat_mem hqU, Cfg.step_of_access hq'']
      simp only [hro, Function.update_eq_self]
    · rw [rexec_concat_not_mem hqU]
  refine ⟨fun U hU q' hq' => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · by_cases hqU : q ∈ U
    · have hq'' : A.act ((rexec A U σ).loc q) = .access y o k := by
        rw [h.loc U hU q hqU]; exact hq
      rw [rexec_concat_mem hqU, hR]
      by_cases e : q' = q
      · subst e
        rw [Cfg.step_loc_self_of_access hq, Cfg.step_loc_self_of_access hq'', hresp U hU hqU]
      · rw [Cfg.step_loc_other _ e, Cfg.step_loc_other _ e, h.loc U hU q' hq']
    · have e : q' ≠ q := fun e => hqU (e ▸ hq')
      rw [rexec_concat_not_mem hqU, hR, Cfg.step_loc_other _ e, h.loc U hU q' hq']
  · rw [hRmem]; exact ⟨(h.untouched z hz).1, fun U hU => by rw [hUmem U hU]; exact (h.untouched z hz).2 U hU⟩
  · rw [hRmem]; exact ⟨(h.good z hz).1, fun U hU => by rw [hUmem U hU]; exact (h.good z hz).2 U hU⟩

/-- A solo step of `p` reading a window register (anywhere), when the memory of every
restriction containing `p` is the real one, preserves everything. -/
theorem Inv.solo_read (h : Inv A σ cls X b) {p : ℕ}
    (hM : ∀ U, Sat cls U → p ∈ U → MemEq (A := A) σ U) (hD : Decided (A := A) σ X b)
    {j : ιw} {k : List (W j) → A.L}
    (hp : A.act ((A.exec id σ).loc p) = .access (.inr j) .read k) :
    Inv A (σ ++ [p]) cls X b ∧ (∀ U, Sat cls U → p ∈ U → MemEq (A := A) (σ ++ [p]) U) ∧
      Decided (A := A) (σ ++ [p]) X b := by
  have hInv : Inv A (σ ++ [p]) cls X b :=
    h.step_readonly hp (fun _ => rfl) (fun U hU hpU => by rw [hM U hU hpU])
  have hRmem : (A.exec id (σ ++ [p])).mem = (A.exec id σ).mem := by
    rw [Alg.exec_concat, Cfg.step_of_access hp]; simp
  refine ⟨hInv, fun U hU hpU => ?_, fun j' hj => by rw [hRmem]; exact hD j' hj⟩
  unfold MemEq
  have hp' : A.act ((rexec A U σ).loc p) = .access (.inr j) .read k := by
    rw [h.loc U hU p hpU]; exact hp
  rw [rexec_concat_mem hpU, Alg.exec_concat, Cfg.step_of_access hp, Cfg.step_of_access hp',
    hM U hU hpU]

/-- A no-op step of a process in an output state. -/
theorem Inv.append_out (h : Inv A σ cls X b) {p : ℕ} {v : ℕ} (hp : (A.exec id σ).Out p v) :
    Inv A (σ ++ [p]) cls X b ∧ A.exec id (σ ++ [p]) = A.exec id σ := by
  have e : A.exec id (σ ++ [p]) = A.exec id σ := by rw [Alg.exec_concat, Cfg.step_of_out hp]
  have eU : ∀ U, Sat cls U → rexec A U (σ ++ [p]) = rexec A U σ := by
    intro U hU
    by_cases hpU : p ∈ U
    · rw [rexec_concat_mem hpU]
      apply Cfg.step_of_out
      unfold Cfg.Out; rw [h.loc U hU p hpU]; exact hp
    · exact rexec_concat_not_mem hpU σ
  refine ⟨⟨fun U hU => by rw [eU U hU, e]; exact h.loc U hU, fun z hz => by
      rw [e]; exact ⟨(h.untouched z hz).1, fun U hU => by rw [eU U hU]; exact (h.untouched z hz).2 U hU⟩,
    fun z hz => by
      rw [e]; exact ⟨(h.good z hz).1, fun U hU => by rw [eU U hU]; exact (h.good z hz).2 U hU⟩⟩, e⟩

end Block

/-! ### Outputs are inputs of the class -/

section Out

variable {σ : List ℕ} {U : Set ℕ} {p : ℕ}

/-- If `p` has the same local state in the restriction to `U` as in the real execution, then a
value output by `p` is (by validity, applied to the restriction) the input — i.e. the
identifier — of a process of `U`. -/
theorem out_mem_of_loc (hval : Validity A anySched) (hpU : p ∈ U) (hpσ : p ∈ σ)
    (hloc : (rexec A U σ).loc p = (A.exec id σ).loc p) {v : ℕ} (hout : (A.exec id σ).Out p v) :
    v ∈ U := by
  have hout' : (rexec A U σ).Out p v := by unfold Cfg.Out; rw [hloc]; exact hout
  have hmem : p ∈ σ.filter (fun q => decide (q ∈ U)) := List.mem_filter.2 ⟨hpσ, by simpa using hpU⟩
  obtain ⟨q, hq, hqv⟩ := hval id _ trivial p hmem v hout'
  have := (List.mem_filter.1 hq).2
  simp only [decide_eq_true_eq] at this
  simpa [← hqv] using this

/-- Solo steps of `p ∈ U` (on any objects) preserve "same memory and same local state of `p` in
the restriction to `U`". -/
theorem solo_memEq (hpU : p ∈ U) (hM : MemEq (A := A) σ U)
    (hloc : (rexec A U σ).loc p = (A.exec id σ).loc p) (t : ℕ) :
    MemEq (A := A) (σ ++ List.replicate t p) U ∧
      (rexec A U (σ ++ List.replicate t p)).loc p = (A.exec id (σ ++ List.replicate t p)).loc p := by
  induction t with
  | zero => simpa using ⟨hM, hloc⟩
  | succ t ih =>
    rw [List.replicate_succ', ← List.append_assoc]
    obtain ⟨ih1, ih2⟩ := ih
    unfold MemEq
    rw [rexec_concat_mem hpU, Alg.exec_concat]
    unfold Cfg.step
    rw [ih2]
    split
    · unfold MemEq at ih1; rw [ih1]; exact ⟨rfl, by simp⟩
    · exact ⟨ih1, ih2⟩

end Out

end Podc.InfiniteArrivalHierarchy.Prop4
