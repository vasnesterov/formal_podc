import Papers.PODC2020.InfiniteArrivalHierarchy.Partition
import Mathlib

/-!
# Proposition 4: binary consensus and window registers are not universal in `M₂`

Perrin, Mostéfaoui, Bonin, *Extending the Wait-free Hierarchy to Multi-Threaded Systems*,
PODC 2020, Proposition 4: `M₂[cons⟨B⟩, WReg]` is not universal.

Model: finite arrival (`finArrival`: in every infinite execution only finitely many processes
take steps), finitely many shared objects allocated at set-up (`Fintype ιc`, `Fintype ιw`):
binary consensus objects and window registers of arbitrary (fixed) sizes. Multi-valued consensus
(process `p` proposes `p`) with agreement, validity and wait-freedom is impossible. Dynamic
(finite) allocation of further objects at run time is *not* modelled (see `differencies.md`).

The proof follows the paper's scheduler: an execution partitioned into classes of processes that
never communicated (`Partition.lean`), in which more and more objects are covered by many
processes of different classes.

* `iteration`: one round of the scheduler: a block write `β` by processes covering all used
  objects `X`, then a solo run `γ` of a process `p` until it covers an object outside `X`; if `p`
  decided instead, a second block by other classes and a solo run of another process produce two
  different decisions;
* `not_consensus` (**Proposition 4**).
-/

namespace Podc.InfiniteArrivalHierarchy.Prop4

open Cslib.SharedMemory Cslib.SharedMemory.Arrival Classical

set_option linter.unusedSectionVars false

variable {ιc ιw : Type} [DecidableEq ιc] [DecidableEq ιw] {W : ιw → Type} {w : ιw → ℕ}
  {A : Alg (CW ιc W w) ℕ ℕ ℕ}

/-- Merge the classes of the processes of `S` into the class of `p`. -/
noncomputable def merge (cls : ℕ → ℕ) (S : List ℕ) (p : ℕ) : ℕ → ℕ :=
  fun q => if cls q ∈ S.map cls then cls p else cls q

lemma merge_coarser (cls : ℕ → ℕ) (S : List ℕ) (p : ℕ) :
    ∀ q q', cls q = cls q' → merge cls S p q = merge cls S p q' := by
  intro q q' h; simp [merge, h]

lemma merge_mem {cls : ℕ → ℕ} {S : List ℕ} {p q : ℕ} (hq : q ∈ S) : merge cls S p q = cls p := by
  have : cls q ∈ S.map cls := List.mem_map_of_mem hq
  simp [merge, this]

lemma merge_of_not {cls : ℕ → ℕ} {S : List ℕ} {p q : ℕ} (h : ∀ r ∈ S, cls r ≠ cls q) :
    merge cls S p q = cls q := by
  have : cls q ∉ S.map cls := by
    simp only [List.mem_map, not_exists, not_and]; exact h
  simp [merge, this]

variable (A) in
/-- `q` is poised on `y` with an operation that is not a read of a window register. -/
def ModP (C : Cfg A) (q : ℕ) (y : ιc ⊕ ιw) : Prop :=
  C.Poised q y ∧ ¬ ∃ (j : ιw) (k : List (W j) → A.L), y = .inr j ∧
    A.act (C.loc q) = .access (.inr j) .read k

variable (A) in
/-- A block: distinct processes covering objects of `X`, at least once each object, window
register `j` at least `w j` times. -/
structure Block (σ : List ℕ) (X : Finset (ιc ⊕ ιw)) (b : ιc → Bool) (Φ : List ℕ)
    (obj : ℕ → ιc ⊕ ιw) : Prop where
  nodup : Φ.Nodup
  cov : ∀ q ∈ Φ, obj q ∈ X ∧ Covers A (A.exec id σ) b q (obj q)
  cnt : ∀ y ∈ X, 1 ≤ (Φ.filter (fun q => decide (obj q = y))).length ∧
    ∀ j, y = .inr j → w j ≤ (Φ.filter (fun q => decide (obj q = y))).length

lemma Block.of_loc {σ σ' : List ℕ} {X : Finset (ιc ⊕ ιw)} {b : ιc → Bool} {Φ : List ℕ}
    {obj : ℕ → ιc ⊕ ιw} (h : Block A σ X b Φ obj)
    (e : ∀ q ∈ Φ, (A.exec id σ').loc q = (A.exec id σ).loc q) : Block A σ' X b Φ obj :=
  ⟨h.nodup, fun q hq => ⟨(h.cov q hq).1, (h.cov q hq).2.of_loc (e q hq)⟩, h.cnt⟩

/-- **One round of the scheduler** of Proposition 4. From a partitioned execution `σ` in which
the objects `X` are covered by two disjoint blocks `Φ` and `Φ'` (of processes of different
classes), the block `Φ` is executed, the classes of `p :: Φ` are merged, and `p` runs solo until
it is poised to modify an object outside `X`. (If `p` decided instead, the block `Φ'` and a solo
run of `p'` would produce a different decision.) -/
theorem iteration (hag : Agreement A anySched) (hval : Validity A anySched)
    (hwf : WaitFree A finArrival) {σ : List ℕ} {cls : ℕ → ℕ} {X : Finset (ιc ⊕ ιw)}
    {b : ιc → Bool} (h : Inv A σ cls X b) {Φ : List ℕ} {obj : ℕ → ιc ⊕ ιw}
    (hΦ : Block A σ X b Φ obj) (p : ℕ) {Φ' : List ℕ} {obj' : ℕ → ιc ⊕ ιw}
    (hΦ' : Block A σ X b Φ' obj') (p' : ℕ)
    (hsep : ∀ q ∈ p :: Φ, ∀ q' ∈ p' :: Φ', cls q ≠ cls q') :
    ∃ t y, y ∉ X ∧ ModP A (A.exec id (σ ++ Φ ++ List.replicate t p)) p y ∧
      Inv A (σ ++ Φ ++ List.replicate t p) (merge cls (p :: Φ) p) X b := by
  have hwf' : WaitFree A (fun s => (Set.range s).Finite) := hwf
  set cls1 := merge cls (p :: Φ) p with hcls1
  have h1 : Inv A σ cls1 X b := h.coarsen (merge_coarser cls (p :: Φ) p)
  have hcls1p : cls1 p = cls p := merge_mem (by simp)
  have hΦU : ∀ U, Sat cls1 U → p ∈ U → ∀ q ∈ Φ, q ∈ U := by
    intro U hU hpU q hq
    exact hU p q (by rw [hcls1p]; exact (merge_mem (List.mem_cons_of_mem _ hq)).symm) hpU
  set σB := σ ++ Φ with hσB
  have hB : Inv A σB cls1 X b := h1.block Φ hΦ.nodup obj hΦ.cov
  have hME : ∀ U, Sat cls1 U → p ∈ U → MemEq (A := A) σB U :=
    fun U hU hpU => (h1.block_memEq Φ hΦ.nodup obj hΦ.cov hΦ.cnt U hU (hΦU U hU hpU)).1
  have hDec : Decided (A := A) σB X b := by
    have := h1.block_memEq Φ hΦ.nodup obj hΦ.cov hΦ.cnt {q | cls1 q = cls1 p} (sat_class _ _)
      (hΦU _ (sat_class _ _) rfl)
    exact this.2
  -- the solo run of `p`
  let Stop : ℕ → Prop := fun t =>
    (∃ v, (A.exec id (σB ++ List.replicate t p)).Out p v) ∨
      ∃ y, y ∉ X ∧ ModP A (A.exec id (σB ++ List.replicate t p)) p y
  have hex : ∃ t, Stop t := by
    obtain ⟨m, v, hv⟩ := hwf'.exists_solo_out id σB p
    exact ⟨m + 1, Or.inl ⟨v, hv⟩⟩
  let t₀ := Nat.find hex
  have hrun : ∀ t ≤ t₀, Inv A (σB ++ List.replicate t p) cls1 X b ∧
      (∀ U, Sat cls1 U → p ∈ U → MemEq (A := A) (σB ++ List.replicate t p) U) ∧
      Decided (A := A) (σB ++ List.replicate t p) X b := by
    intro t ht
    induction t with
    | zero => simpa using ⟨hB, hME, hDec⟩
    | succ t ih =>
      obtain ⟨i1, i2, i3⟩ := ih (Nat.le_of_succ_le ht)
      have hns : ¬ Stop t := Nat.find_min hex (Nat.lt_of_succ_le ht)
      simp only [Stop, not_or, not_exists, not_and] at hns
      rw [List.replicate_succ', ← List.append_assoc]
      rcases Cfg.out_or_poised (A.exec id (σB ++ List.replicate t p)) p with ⟨v, hv⟩ | ⟨y, hy⟩
      · exact absurd hv (hns.1 v)
      · by_cases hyX : y ∈ X
        · exact i1.solo_step i2 i3 hyX hy
        · have hrd := hns.2 y hyX
          simp only [ModP, hy, true_and, not_not] at hrd
          obtain ⟨j, k, rfl, hk⟩ := hrd
          exact i1.solo_read i2 i3 hk
  obtain ⟨i1, i2, i3⟩ := hrun t₀ le_rfl
  rcases Nat.find_spec hex with ⟨v, hv⟩ | ⟨y, hyX, hy⟩
  swap
  · exact ⟨t₀, y, hyX, hy, i1⟩
  exfalso
  -- `p` decided `v`: a value of its class
  set σ1 := σB ++ List.replicate t₀ p ++ [p] with hσ1
  obtain ⟨j1, e1⟩ := i1.append_out hv
  have hv1 : (A.exec id σ1).Out p v := by rw [e1]; exact hv
  have hpσ1 : p ∈ σ1 := by simp [hσ1]
  have hvU1 : v ∈ {q | cls1 q = cls1 p} :=
    out_mem_of_loc (U := {q | cls1 q = cls1 p}) hval rfl hpσ1
      (j1.loc _ (sat_class _ _) p rfl) hv1
  -- the second block and the solo run of `p'`
  have hnot : ∀ q' ∈ p' :: Φ', q' ∉ p :: Φ := fun q' hq' hq => hsep q' hq q' hq' rfl
  set cls2 := merge cls1 (p' :: Φ') p' with hcls2
  have hcls1' : ∀ r ∈ p' :: Φ', cls1 r = cls r := fun r hr =>
    merge_of_not (fun s hs => hsep s hs r hr)
  have j2 : Inv A σ1 cls2 X b := j1.coarsen (merge_coarser cls1 (p' :: Φ') p')
  have hloc1 : ∀ q' ∈ p' :: Φ', (A.exec id σ1).loc q' = (A.exec id σ).loc q' := by
    intro q' hq'
    have : σ1 = σ ++ (Φ ++ List.replicate t₀ p ++ [p]) := by simp [hσ1, hσB]
    rw [this, Alg.exec_append]
    apply Alg.run_loc_other
    have := hnot q' hq'
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton, not_or]
    simp only [List.mem_cons, not_or] at this
    exact ⟨⟨this.2, fun h' => this.1 h'.2⟩, this.1⟩
  have hΦ'1 : Block A σ1 X b Φ' obj' :=
    hΦ'.of_loc (fun q' hq' => hloc1 q' (List.mem_cons_of_mem _ hq'))
  have hcls2p' : cls2 p' = cls1 p' := merge_mem (by simp)
  set U2 := {q | cls2 q = cls2 p'} with hU2
  have hΦ'U2 : ∀ q ∈ Φ', q ∈ U2 := by
    intro q hq; show cls2 q = cls2 p'
    rw [hcls2p']; exact merge_mem (List.mem_cons_of_mem _ hq)
  set σ2 := σ1 ++ Φ' with hσ2
  have j3 : Inv A σ2 cls2 X b := j2.block Φ' hΦ'1.nodup obj' hΦ'1.cov
  have hM2 : MemEq (A := A) σ2 U2 :=
    (j2.block_memEq Φ' hΦ'1.nodup obj' hΦ'1.cov hΦ'1.cnt U2 (sat_class _ _) hΦ'U2).1
  obtain ⟨m, v', hv'⟩ := hwf'.exists_solo_out id σ2 p'
  set σ3 := σ2 ++ List.replicate (m + 1) p' with hσ3
  obtain ⟨-, hl3⟩ := solo_memEq (A := A) (show p' ∈ U2 from rfl) hM2
    (j3.loc U2 (sat_class _ _) p' rfl) (m + 1)
  have hp'σ3 : p' ∈ σ3 := by
    rw [hσ3]; exact List.mem_append_right _ (List.mem_replicate.2 ⟨Nat.succ_ne_zero _, rfl⟩)
  have hv'U2 : v' ∈ U2 := out_mem_of_loc (U := U2) hval rfl hp'σ3 hl3 hv'
  -- agreement fails
  have hv3 : (A.exec id σ3).Out p v := by
    have : σ3 = σ1 ++ (Φ' ++ List.replicate (m + 1) p') := by simp [hσ3, hσ2]
    rw [this, Alg.exec_append]; exact Alg.Cfg.Out.run hv1 _
  have hpσ3 : p ∈ σ3 := by simp [hσ3, hσ2, hσ1]
  have hvv : v = v' := hag id σ3 trivial p hpσ3 p' hp'σ3 v v' hv3 hv'
  subst hvv
  have hc1 : cls1 v = cls p := by rw [show cls1 v = cls1 p from hvU1, hcls1p]
  have hc2 : cls2 v = cls1 v := by
    apply merge_of_not
    intro r hr
    rw [hcls1' r hr, hc1]
    exact fun e => hsep p (by simp) r hr e.symm
  have : cls2 v = cls2 p' := hv'U2
  rw [hc2, hc1, hcls2p', hcls1' p' (by simp)] at this
  exact hsep p (by simp) p' (by simp) this

/-! ### The scheduler: iterations within a stage -/

lemma length_filter_toList (s : Finset ℕ) (P : ℕ → Prop) :
    (s.toList.filter (fun x => decide (P x))).length = (s.filter P).card := by
  rw [← List.toFinset_card_of_nodup ((s.nodup_toList).filter _)]
  congr 1; ext; simp

lemma ModP.of_loc {C D : Cfg A} {q : ℕ} {y : ιc ⊕ ιw} (h : ModP A C q y)
    (e : D.loc q = C.loc q) : ModP A D q y := by
  unfold ModP Cfg.Poised at *; rw [e]; exact h

lemma Covers.unique {C : Cfg A} {b : ιc → Bool} {q : ℕ} {y y' : ιc ⊕ ιw}
    (h : Covers A C b q y) (h' : Covers A C b q y') : y = y' :=
  Cfg.Poised.unique h.poised h'.poised

variable (A) in
/-- `q` covers `y` in the configuration after `σ₀`. -/
def covAt (σ₀ : List ℕ) (b : ιc → Bool) (y : ιc ⊕ ιw) (q : ℕ) : Prop :=
  Covers A (A.exec id σ₀) b q y

variable (A) in
/-- The state of the scheduler after `j` iterations of a stage that started at `σ₀` with the used
objects `X`: unmoved representatives `U0` (frozen since `σ₀`, covering `X`), moved
representatives `M` (each poised to modify an object outside `X`), all in different classes. -/
structure ISt (l : ℕ) (σ₀ : List ℕ) (X : Finset (ιc ⊕ ιw)) (b : ιc → Bool) (c j : ℕ) where
  σ : List ℕ
  cls : ℕ → ℕ
  inv : Inv A σ cls X b
  U0 : Finset ℕ
  M : Finset ℕ
  disj : Disjoint U0 M
  dist : ∀ q ∈ U0 ∪ M, ∀ q' ∈ U0 ∪ M, cls q = cls q' → q = q'
  frozen : ∀ q ∈ U0, (A.exec id σ).loc q = (A.exec id σ₀).loc q
  cov : X.Nonempty → ∀ q ∈ U0, ∃ y ∈ X, Covers A (A.exec id σ₀) b q y
  mod : ∀ q ∈ M, ∃ y ∉ X, ModP A (A.exec id σ) q y
  cardM : M.card = j
  cnt : ∀ y ∈ X, c ≤ (U0.filter (covAt A σ₀ b y)).card + j * (l + 1)
  size : X = ∅ → c ≤ U0.card + j

/-- One iteration of the scheduler (one more moved representative). -/
theorem ISt.next [Nonempty (ιc ⊕ ιw)] (hag : Agreement A anySched)
    (hval : Validity A anySched) (hwf : WaitFree A finArrival) {l : ℕ} (hl1 : 1 ≤ l)
    (hlw : ∀ j, w j ≤ l) {σ₀ : List ℕ} {X : Finset (ιc ⊕ ιw)} {b : ιc → Bool} {c j : ℕ}
    (st : ISt A l σ₀ X b c j) (hc : j * (l + 1) + 2 * l + 2 ≤ c) :
    Nonempty (ISt A l σ₀ X b c (j + 1)) := by
  have hjl : j ≤ j * (l + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hcnt : ∀ y ∈ X, 2 * l + 2 ≤ (st.U0.filter (covAt A σ₀ b y)).card := by
    intro y hy; have := st.cnt y hy; omega
  -- the first block
  have hS : ∀ y ∈ X, ∃ T ⊆ st.U0.filter (covAt A σ₀ b y), T.card = l := fun y hy =>
    Finset.exists_subset_card_eq (by have := hcnt y hy; omega)
  choose! S hSsub hScard using hS
  set Φs := X.biUnion S with hΦs
  have hΦsU : Φs ⊆ st.U0 := by
    intro q hq
    obtain ⟨y, hy, hq⟩ := Finset.mem_biUnion.1 hq
    exact (Finset.mem_filter.1 (hSsub y hy hq)).1
  have hΦs_cov : ∀ y ∈ X, Φs.filter (covAt A σ₀ b y) = S y := by
    intro y hy
    ext q
    simp only [Finset.mem_filter, hΦs, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨y', hy', hq⟩, hc⟩
      have := (Finset.mem_filter.1 (hSsub y' hy' hq)).2
      rw [Covers.unique hc this]; exact hq
    · intro hq
      exact ⟨⟨y, hy, hq⟩, (Finset.mem_filter.1 (hSsub y hy hq)).2⟩
  -- the stepping process `p`
  have hU0ne : st.U0.Nonempty := by
    by_cases hX : X = ∅
    · have := st.size hX
      exact Finset.card_pos.1 (by omega)
    · obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hX
      have := hcnt y hy
      exact Finset.card_pos.1 (lt_of_lt_of_le
        (show 0 < (st.U0.filter (covAt A σ₀ b y)).card by omega) (Finset.card_filter_le _ _))
  obtain ⟨p, hp⟩ := hU0ne
  set D := insert p Φs with hD
  have hDU : D ⊆ st.U0 := Finset.insert_subset hp hΦsU
  have hDcnt : ∀ y ∈ X, (D.filter (covAt A σ₀ b y)).card ≤ l + 1 := by
    intro y hy
    rw [hD, Finset.filter_insert]
    split_ifs
    · rw [Finset.card_insert_eq_ite]; split_ifs <;> rw [hΦs_cov y hy, hScard y hy] <;> omega
    · rw [hΦs_cov y hy, hScard y hy]; omega
  have hrest : ∀ y ∈ X, (st.U0.filter (covAt A σ₀ b y)).card ≤
      ((st.U0 \ D).filter (covAt A σ₀ b y)).card + (l + 1) := by
    intro y hy
    have h1 := Finset.card_le_card_sdiff_add_card (s := st.U0.filter (covAt A σ₀ b y)) (t := D.filter (covAt A σ₀ b y))
    have h2 : st.U0.filter (covAt A σ₀ b y) \ D.filter (covAt A σ₀ b y) = (st.U0 \ D).filter (covAt A σ₀ b y) := by
      ext q; simp only [Finset.mem_sdiff, Finset.mem_filter]; tauto
    rw [h2] at h1; have := hDcnt y hy; omega
  -- the second block
  have hS' : ∀ y ∈ X, ∃ T ⊆ (st.U0 \ D).filter (covAt A σ₀ b y), T.card = l := fun y hy =>
    Finset.exists_subset_card_eq (by have := hrest y hy; have := hcnt y hy; omega)
  choose! S' hS'sub hS'card using hS'
  set Φs' := X.biUnion S' with hΦs'
  have hΦs'U : Φs' ⊆ st.U0 \ D := by
    intro q hq
    obtain ⟨y, hy, hq⟩ := Finset.mem_biUnion.1 hq
    exact (Finset.mem_filter.1 (hS'sub y hy hq)).1
  have hΦs'_cov : ∀ y ∈ X, Φs'.filter (covAt A σ₀ b y) = S' y := by
    intro y hy
    ext q
    simp only [Finset.mem_filter, hΦs', Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨y', hy', hq⟩, hc⟩
      have := (Finset.mem_filter.1 (hS'sub y' hy' hq)).2
      rw [Covers.unique hc this]; exact hq
    · intro hq
      exact ⟨⟨y, hy, hq⟩, (Finset.mem_filter.1 (hS'sub y hy hq)).2⟩
  have hp'ex : (st.U0 \ D).Nonempty := by
    by_cases hX : X = ∅
    · have h1 := st.size hX
      have hΦe : Φs = ∅ := by rw [hΦs, hX]; simp
      have : (st.U0 \ D).card = st.U0.card - 1 := by
        rw [hD, hΦe, Finset.card_sdiff_of_subset (by simpa using hp)]; simp
      exact Finset.card_pos.1 (by omega)
    · obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hX
      have := hS'card y hy
      have hne : (S' y).Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨q, hq⟩ := hne
      exact ⟨q, (Finset.mem_filter.1 (hS'sub y hy hq)).1⟩
  obtain ⟨p', hp'⟩ := hp'ex
  -- objects
  let obj : ℕ → ιc ⊕ ιw := fun q =>
    if h : ∃ y ∈ X, covAt A σ₀ b y q then h.choose else Classical.arbitrary _
  have hobj : ∀ q y, y ∈ X → covAt A σ₀ b y q → obj q = y := by
    intro q y hy hq
    have hex : ∃ y ∈ X, covAt A σ₀ b y q := ⟨y, hy, hq⟩
    simp only [obj, hex, dite_true]
    exact Covers.unique hex.choose_spec.2 hq
  have hblock : ∀ (T : ιc ⊕ ιw → Finset ℕ), (∀ y ∈ X, T y ⊆ st.U0.filter (covAt A σ₀ b y)) →
      (∀ y ∈ X, T y = (X.biUnion T).filter (covAt A σ₀ b y)) → (∀ y ∈ X, (T y).card = l) →
      Block A st.σ X b (X.biUnion T).toList obj := by
    intro T hTsub hTcov hTcard
    refine ⟨Finset.nodup_toList _, fun q hq => ?_, fun y hy => ?_⟩
    · rw [Finset.mem_toList] at hq
      obtain ⟨y, hy, hqy⟩ := Finset.mem_biUnion.1 hq
      have h1 := Finset.mem_filter.1 (hTsub y hy hqy)
      rw [hobj q y hy h1.2]
      exact ⟨hy, h1.2.of_loc (st.frozen q h1.1)⟩
    · have : (X.biUnion T).toList.filter (fun q => decide (obj q = y)) =
          (X.biUnion T).toList.filter (fun q => decide (covAt A σ₀ b y q)) := by
        apply List.filter_congr
        intro q hq
        rw [Finset.mem_toList] at hq
        obtain ⟨y', hy', hqy'⟩ := Finset.mem_biUnion.1 hq
        have h1 := (Finset.mem_filter.1 (hTsub y' hy' hqy')).2
        rw [hobj q y' hy' h1]
        by_cases e : y' = y
        · subst e; simp [h1]
        · have : ¬ covAt A σ₀ b y q := fun h2 => e (Covers.unique h1 h2)
          simp [e, this]
      rw [this, length_filter_toList, ← hTcov y hy, hTcard y hy]
      exact ⟨hl1, fun j' e => by subst e; exact hlw j'⟩
  have hB1 : Block A st.σ X b Φs.toList obj :=
    hblock S (fun y hy => hSsub y hy) (fun y hy => (hΦs_cov y hy).symm) hScard
  have hB2 : Block A st.σ X b Φs'.toList obj :=
    hblock S' (fun y hy => (hS'sub y hy).trans (Finset.filter_subset_filter _ Finset.sdiff_subset))
      (fun y hy => (hΦs'_cov y hy).symm) hS'card
  have hsep : ∀ q ∈ p :: Φs.toList, ∀ q' ∈ p' :: Φs'.toList, st.cls q ≠ st.cls q' := by
    intro q hq q' hq' e
    have hqD : q ∈ D := by
      rcases List.mem_cons.1 hq with rfl | hq
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_toList.1 hq)
    have hq'R : q' ∈ st.U0 \ D := by
      rcases List.mem_cons.1 hq' with rfl | hq'
      · exact hp'
      · exact hΦs'U (Finset.mem_toList.1 hq')
    have := st.dist q (Finset.mem_union_left _ (hDU hqD)) q'
      (Finset.mem_union_left _ (Finset.mem_sdiff.1 hq'R).1) e
    subst this
    exact (Finset.mem_sdiff.1 hq'R).2 hqD
  obtain ⟨t, y, hyX, hmod, hinv⟩ :=
    iteration hag hval hwf st.inv hB1 p hB2 p' hsep
  -- the new state
  set σ' := st.σ ++ Φs.toList ++ List.replicate t p with hσ'
  have hlocO : ∀ q, q ∉ D → (A.exec id σ').loc q = (A.exec id st.σ).loc q := by
    intro q hq
    rw [hσ', List.append_assoc, Alg.exec_append]
    apply Alg.run_loc_other
    simp only [List.mem_append, Finset.mem_toList, List.mem_replicate, not_or]
    rw [hD, Finset.mem_insert, not_or] at hq
    exact ⟨hq.2, fun h' => hq.1 h'.2⟩
  have hclsEq : ∀ q ∈ (st.U0 \ D) ∪ insert p st.M,
      merge st.cls (p :: Φs.toList) p q = st.cls q := by
    intro q hq
    by_cases hin : st.cls q ∈ (p :: Φs.toList).map st.cls
    · obtain ⟨r, hr, e⟩ := List.mem_map.1 hin
      have hrD : r ∈ D := by
        rcases List.mem_cons.1 hr with rfl | hr
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_toList.1 hr)
      have hqU : q ∈ st.U0 ∪ st.M := by
        rcases Finset.mem_union.1 hq with hq | hq
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.1 hq).1
        · rcases Finset.mem_insert.1 hq with rfl | hq
          · exact Finset.mem_union_left _ hp
          · exact Finset.mem_union_right _ hq
      have hrq := st.dist r (Finset.mem_union_left _ (hDU hrD)) q hqU e
      subst hrq
      rcases Finset.mem_union.1 hq with hq | hq
      · exact absurd hrD (Finset.mem_sdiff.1 hq).2
      · rcases Finset.mem_insert.1 hq with rfl | hq
        · exact merge_mem (by simp)
        · exact absurd hq (Finset.disjoint_left.1 st.disj (hDU hrD))
    · exact merge_of_not (fun r hr e => hin (List.mem_map.2 ⟨r, hr, e⟩))
  have hpM : p ∉ st.M := Finset.disjoint_left.1 st.disj hp
  refine ⟨{
    σ := σ'
    cls := merge st.cls (p :: Φs.toList) p
    inv := hinv
    U0 := st.U0 \ D
    M := insert p st.M
    disj := by
      rw [Finset.disjoint_insert_right]
      exact ⟨fun h' => (Finset.mem_sdiff.1 h').2 (Finset.mem_insert_self _ _),
        Finset.disjoint_of_subset_left Finset.sdiff_subset st.disj⟩
    dist := by
      intro q hq q' hq' e
      rw [hclsEq q hq, hclsEq q' hq'] at e
      have sub : (st.U0 \ D) ∪ insert p st.M ⊆ st.U0 ∪ st.M := by
        intro r hr
        rcases Finset.mem_union.1 hr with hr | hr
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.1 hr).1
        · rcases Finset.mem_insert.1 hr with rfl | hr
          · exact Finset.mem_union_left _ hp
          · exact Finset.mem_union_right _ hr
      exact st.dist q (sub hq) q' (sub hq') e
    frozen := fun q hq => by
      rw [hlocO q (Finset.mem_sdiff.1 hq).2]; exact st.frozen q (Finset.mem_sdiff.1 hq).1
    cov := fun hX q hq => st.cov hX q (Finset.mem_sdiff.1 hq).1
    mod := by
      intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact ⟨y, hyX, hmod⟩
      · obtain ⟨y', hy', hm⟩ := st.mod q hq
        refine ⟨y', hy', hm.of_loc (hlocO q ?_)⟩
        intro hqD
        exact Finset.disjoint_left.1 st.disj (hDU hqD) hq
    cardM := by rw [Finset.card_insert_of_notMem hpM, st.cardM]
    cnt := by
      intro y' hy'
      have := st.cnt y' hy'; have := hrest y' hy'
      rw [Nat.succ_mul]; omega
    size := by
      intro hX
      have := st.size hX
      have hΦe : Φs = ∅ := by rw [hΦs, hX]; simp
      have : (st.U0 \ D).card = st.U0.card - 1 := by
        rw [hD, hΦe, Finset.card_sdiff_of_subset (by simpa using hp)]; simp
      have : 0 < st.U0.card := Finset.card_pos.2 ⟨p, hp⟩
      omega }⟩

/-! ### Stages -/

variable (A) in
/-- A stage of the scheduler: the objects `X` are covered at least `c` times each by
representatives `R` of pairwise different classes (Definition 5: `C(α)` is `(R, c, X)`-covered,
`α` is `R`-partitioned). -/
structure SSt (c : ℕ) where
  σ : List ℕ
  cls : ℕ → ℕ
  X : Finset (ιc ⊕ ιw)
  b : ιc → Bool
  inv : Inv A σ cls X b
  R : Finset ℕ
  dist : ∀ q ∈ R, ∀ q' ∈ R, cls q = cls q' → q = q'
  cov : X.Nonempty → ∀ q ∈ R, ∃ y ∈ X, covAt A σ b y q
  cnt : ∀ y ∈ X, c ≤ (R.filter (covAt A σ b y)).card
  size : c ≤ R.card

/-- The start of a stage. -/
def SSt.toISt {c : ℕ} (st : SSt A c) (l : ℕ) : ISt A l st.σ st.X st.b c 0 where
  σ := st.σ
  cls := st.cls
  inv := st.inv
  U0 := st.R
  M := ∅
  disj := Finset.disjoint_empty_right _
  dist := fun q hq q' hq' => st.dist q (by simpa using hq) q' (by simpa using hq')
  frozen := fun _ _ => rfl
  cov := st.cov
  mod := fun _ h => by simp at h
  cardM := rfl
  cnt := fun y hy => by simpa using st.cnt y hy
  size := fun _ => by simpa using st.size

/-- `v` iterations of the scheduler. -/
theorem ISt.iter [Nonempty (ιc ⊕ ιw)] (hag : Agreement A anySched)
    (hval : Validity A anySched) (hwf : WaitFree A finArrival) {l : ℕ} (hl1 : 1 ≤ l)
    (hlw : ∀ j, w j ≤ l) {σ₀ : List ℕ} {X : Finset (ιc ⊕ ιw)} {b : ιc → Bool} {c v : ℕ}
    (st : ISt A l σ₀ X b c 0) (hc : v * (l + 1) + 2 * l + 2 ≤ c + (l + 1)) :
    ∀ j ≤ v, Nonempty (ISt A l σ₀ X b c j) := by
  intro j hj
  induction j with
  | zero => exact ⟨st⟩
  | succ j ih =>
    obtain ⟨st'⟩ := ih (Nat.le_of_succ_le hj)
    exact st'.next hag hval hwf hl1 hlw (by
      have : (j + 1) * (l + 1) ≤ v * (l + 1) := Nat.mul_le_mul_right _ hj
      rw [Nat.succ_mul] at this; omega)

lemma Covers.congr_b {C : Cfg A} {b b' : ιc → Bool} {q : ℕ} {y : ιc ⊕ ιw}
    (h : Covers A C b q y) (hb : ∀ j, y = .inl j → b' j = b j) : Covers A C b' q y := by
  cases y with
  | inl j => obtain ⟨k, hk⟩ := h; exact ⟨k, by rw [hb j rfl]; exact hk⟩
  | inr j => exact h

/-- The end of a stage: by the pigeonhole principle, one object outside `X` is covered by many
moved representatives (with a common proposed value, for a consensus object). -/
theorem ISt.transition [Fintype ιc] [Fintype ιw] {l : ℕ} {σ₀ : List ℕ}
    {X : Finset (ιc ⊕ ιw)} {b : ιc → Bool} {c c' k : ℕ}
    (hk : (Finset.univ \ X).card = k) (st : ISt A l σ₀ X b c (2 * c' * k + 1))
    (hc : (2 * c' * k + 1) * (l + 1) + c' ≤ c) :
    ∃ st' : SSt A c', st'.X.card = X.card + 1 := by
  set v := 2 * c' * k + 1
  have : Nonempty (ιc ⊕ ιw) := by
    obtain ⟨q, hq⟩ : st.M.Nonempty := Finset.card_pos.1 (by rw [st.cardM]; omega)
    exact ⟨(st.mod q hq).choose⟩
  have hmod := st.mod
  choose! f hfX hfmod using hmod
  obtain ⟨y, hyX, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := st.M) (t := Finset.univ \ X) (f := f) (n := 2 * c')
    (fun q hq => Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hfX q hq⟩)
    (by rw [hk, st.cardM]; exact lt_of_eq_of_lt (by ring) (Nat.lt_succ_self (2 * c' * k)))
  have hyX' : y ∉ X := (Finset.mem_sdiff.1 hyX).2
  set F := st.M.filter (fun q => f q = y) with hF
  have hFmod : ∀ q ∈ F, ModP A (A.exec id st.σ) q y := by
    intro q hq; obtain ⟨hq, e⟩ := Finset.mem_filter.1 hq; rw [← e]; exact hfmod q hq
  -- the new covering set `G ⊆ F` and the value `b'`
  obtain ⟨G, b', hGF, hGcard, hb', hGcov⟩ : ∃ (G : Finset ℕ) (b' : ιc → Bool), G ⊆ F ∧
      c' < G.card ∧ (∀ j, (.inl j : ιc ⊕ ιw) ∈ X → b' j = b j) ∧
      ∀ q ∈ G, Covers A (A.exec id st.σ) b' q y := by
    cases y with
    | inr j =>
      refine ⟨F, b, subset_rfl, by omega, fun _ _ => rfl, fun q hq => ?_⟩
      obtain ⟨⟨o, k', hk'⟩, hnr⟩ := hFmod q hq
      cases o with
      | read => exact absurd ⟨j, k', rfl, hk'⟩ hnr
      | write v' => exact ⟨v', k', hk'⟩
    | inl j =>
      have hex : ∀ q ∈ F, ∃ (o : Bool) (k' : Bool → A.L),
          A.act ((A.exec id st.σ).loc q) = .access (.inl j) o k' := by
        intro q hq; obtain ⟨⟨o, k', hk'⟩, -⟩ := hFmod q hq; exact ⟨o, k', hk'⟩
      obtain ⟨q₀, hq₀⟩ : F.Nonempty := Finset.card_pos.1 (by omega)
      have : Nonempty (Bool → A.L) := ⟨(hex q₀ hq₀).choose_spec.choose⟩
      choose! g kk hg using hex
      obtain ⟨c0, -, hc0⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (s := F) (t := (Finset.univ : Finset Bool)) (f := g) (n := c')
        (fun _ _ => Finset.mem_univ _) (by simp; omega)
      refine ⟨F.filter (fun q => g q = c0), Function.update b j c0, Finset.filter_subset _ _, hc0,
        fun j' hj' => ?_, fun q hq => ?_⟩
      · have : j' ≠ j := by rintro rfl; exact hyX' hj'
        simp [Function.update_of_ne this]
      · obtain ⟨hq, e⟩ := Finset.mem_filter.1 hq
        refine ⟨kk q, ?_⟩
        rw [Function.update_self, ← e]; exact hg q hq
  have hGM : G ⊆ st.M := hGF.trans (Finset.filter_subset _ _)
  have hcovU : ∀ y' ∈ X, ∀ q ∈ st.U0, covAt A σ₀ b y' q → covAt A st.σ b' y' q := by
    intro y' hy' q hq hc'
    exact (hc'.of_loc (st.frozen q hq)).congr_b (fun j e => by subst e; exact hb' j hy')
  refine ⟨{
    σ := st.σ
    cls := st.cls
    X := insert y X
    b := b'
    inv := st.inv.insert hyX' hb'
    R := st.U0.filter (fun q => ∃ y' ∈ X, covAt A σ₀ b y' q) ∪ G
    dist := fun q hq q' hq' e => st.dist q
      (Finset.union_subset_union (Finset.filter_subset _ _) hGM hq) q'
      (Finset.union_subset_union (Finset.filter_subset _ _) hGM hq') e
    cov := by
      intro _ q hq
      rcases Finset.mem_union.1 hq with hq | hq
      · obtain ⟨hq, y', hy', hc'⟩ := Finset.mem_filter.1 hq
        exact ⟨y', Finset.mem_insert_of_mem hy', hcovU y' hy' q hq hc'⟩
      · exact ⟨y, Finset.mem_insert_self _ _, hGcov q hq⟩
    cnt := by
      intro y' hy'
      rcases Finset.mem_insert.1 hy' with rfl | hy'
      · calc c' ≤ G.card := hGcard.le
          _ ≤ _ := by
            apply Finset.card_le_card
            intro q hq
            exact Finset.mem_filter.2 ⟨Finset.mem_union_right _ hq, hGcov q hq⟩
      · have h1 := st.cnt y' hy'
        have h2 : (st.U0.filter (covAt A σ₀ b y')).card ≤
            ((st.U0.filter (fun q => ∃ y' ∈ X, covAt A σ₀ b y' q) ∪ G).filter
              (covAt A st.σ b' y')).card := by
          apply Finset.card_le_card
          intro q hq
          obtain ⟨hq, hc'⟩ := Finset.mem_filter.1 hq
          exact Finset.mem_filter.2 ⟨Finset.mem_union_left _
            (Finset.mem_filter.2 ⟨hq, y', hy', hc'⟩), hcovU y' hy' q hq hc'⟩
        have : v * (l + 1) ≤ c := by omega
        omega
    size := le_trans hGcard.le (Finset.card_le_card Finset.subset_union_right) }, ?_⟩
  exact Finset.card_insert_of_notMem hyX'

/-! ### Proposition 4 -/

/-- The coverage required at a stage with `k` objects not yet covered. (The paper uses
`uᵢ = (m - i + 1)! (2l)^(m-i+1)`; any sufficiently fast-growing sequence works.) -/
def need (l : ℕ) : ℕ → ℕ
  | 0 => 2 * l + 2
  | k + 1 => (2 * need l k * (k + 1) + 1) * (l + 1) + need l k + 2 * l + 2

/-- No stage of the scheduler can exist: by induction on the number of objects not yet covered,
the last stage would require `p` to cover an object outside the set of all objects. -/
theorem stage_false [Fintype ιc] [Fintype ιw] [Nonempty (ιc ⊕ ιw)]
    (hag : Agreement A anySched) (hval : Validity A anySched) (hwf : WaitFree A finArrival)
    {l : ℕ} (hl1 : 1 ≤ l) (hlw : ∀ j, w j ≤ l) :
    ∀ k (st : SSt A (need l k)), (Finset.univ \ st.X).card = k → False := by
  intro k
  induction k with
  | zero =>
    intro st hk
    obtain ⟨st1⟩ := (st.toISt l).next hag hval hwf hl1 hlw (by simp [need])
    obtain ⟨q, hq⟩ : st1.M.Nonempty := Finset.card_pos.1 (by rw [st1.cardM]; omega)
    obtain ⟨y, hy, -⟩ := st1.mod q hq
    have : y ∈ Finset.univ \ st.X := Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hy⟩
    rw [Finset.card_eq_zero.1 hk] at this
    simp at this
  | succ k ih =>
    intro st hk
    obtain ⟨st'⟩ := ISt.iter hag hval hwf hl1 hlw (st.toISt l)
      (v := 2 * need l k * (k + 1) + 1) (by simp only [need]; omega) _ le_rfl
    obtain ⟨st'', hcard⟩ := st'.transition hk (by simp only [need]; omega)
    apply ih st''
    have h1 := Finset.card_univ_sdiff st.X
    have h2 := Finset.card_univ_sdiff st''.X
    have h3 := Finset.card_le_univ st''.X
    omega

/-- **Proposition 4** (`M₂[cons⟨B⟩, WReg]` is not universal), for algorithms that use finitely many
objects allocated at set-up: no algorithm using finitely many binary consensus objects and window
registers (of any sizes) solves consensus (agreement, validity, wait-freedom) in the finite arrival
model. (Processes propose their identifiers.) -/
theorem not_consensus [Fintype ιc] [Fintype ιw] (A : Alg (CW ιc W w) ℕ ℕ ℕ)
    (hag : Agreement A anySched) (hval : Validity A anySched) (hwf : WaitFree A finArrival) :
    False := by
  rcases isEmpty_or_nonempty (ιc ⊕ ιw) with hE | hE
  · -- no objects at all: every process outputs at once, its own input
    have hout : ∀ (C : Cfg A) (p : ℕ), ∃ v, C.Out p v := by
      intro C p
      rcases Cfg.out_or_poised C p with h | ⟨i, -⟩
      · exact h
      · exact (hE.false i).elim
    have hrun : ∀ σ, A.exec id σ = A.initCfg id := fun σ =>
      Alg.run_of_out_all _ _ (fun p _ => hout _ p)
    obtain ⟨v0, h0⟩ := hout (A.initCfg id) 0
    obtain ⟨v1, h1⟩ := hout (A.initCfg id) 1
    have e0 : v0 = 0 := by
      obtain ⟨q, hq, e⟩ := hval id [0] trivial 0 (by simp) v0 (by rw [hrun]; exact h0)
      simp at hq; subst hq; exact e.symm
    have e1 : v1 = 1 := by
      obtain ⟨q, hq, e⟩ := hval id [1] trivial 1 (by simp) v1 (by rw [hrun]; exact h1)
      simp at hq; subst hq; exact e.symm
    have := hag id [0, 1] trivial 0 (by simp) 1 (by simp) v0 v1 (by rw [hrun]; exact h0)
      (by rw [hrun]; exact h1)
    omega
  · let l := Finset.univ.sup w + 1
    have hlw : ∀ j, w j ≤ l := fun j => Nat.le_succ_of_le (Finset.le_sup (Finset.mem_univ j))
    let st : SSt A (need l (Fintype.card (ιc ⊕ ιw))) := {
      σ := []
      cls := id
      X := ∅
      b := fun _ => false
      inv := Inv.nil id _
      R := Finset.range (need l (Fintype.card (ιc ⊕ ιw)))
      dist := fun q _ q' _ e => e
      cov := fun h => by simp at h
      cnt := fun y h => by simp at h
      size := by simp }
    exact stage_false hag hval hwf (by omega) hlw _ st (by simp [st])

end Podc.InfiniteArrivalHierarchy.Prop4
