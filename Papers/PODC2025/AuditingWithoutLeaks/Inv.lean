import Papers.PODC2025.AuditingWithoutLeaks.Alg1

/-!
# Invariants of Algorithm 1 (Lemmas 16–18 and the audit bookkeeping)

All invariants are properties of reachable configurations. The value associated with a sequence
number `t ≤ R.seq` is `hv C t` (`R.val` for `t = R.seq`, else the copy in `V[t]`; Lemma 18), and
reader `j` has *fetched at* `t` (applied fetch&xor to `R` while `R.seq = t`) iff `Fetched C j t`
(`B[t][j]` for `t < R.seq`, the deciphered tracking bit for `t = R.seq`).
-/

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au]

variable (m W Au V) in
/-- Configurations of Algorithm 1. -/
abbrev Cfg (v₀ : V) := Config (auditReg m V v₀) (BO m V v₀) (Proc m W Au) (Loc m V)

section
variable {v₀ : V}

/-- Contents of `R`. -/
def rOf (C : Cfg m W Au V v₀) : RVal m V := C.mem .R

/-- Contents of `SN`. -/
def snOf (C : Cfg m W Au V v₀) : ℕ := C.mem .SN

variable (v₀) in
/-- The value of sequence number `t` (meaningful for `t ≤ R.seq`). -/
def hv (C : Cfg m W Au V v₀) (t : ℕ) : V :=
  if t = (rOf C).seq then (rOf C).val else ((C.mem (.V t) : Option V)).getD v₀

variable (rnd : ℕ → Fin m → Bool)

/-- Reader `j` has applied fetch&xor to `R` while `R.seq = t`. -/
def Fetched (C : Cfg m W Au V v₀) (j : Fin m) (t : ℕ) : Prop :=
  (t < (rOf C).seq ∧ (C.mem (.B t j) : Bool) = true) ∨
  (t = (rOf C).seq ∧ (rOf C).bits j ≠ rnd t j)

/-- The sequence number of the last fetch&xor of a reader (from its local state). -/
def lastFx : Loc m V → Option ℕ
  | .rIdle prev | .rSN prev | .rFX prev _ | .rRet prev _ => prev.map Prod.fst
  | .rCAS _ sn _ => some sn
  | _ => none

/-- Correctness of a reader's `(prev_sn, prev_val)`. -/
def PrevOK (C : Cfg m W Au V v₀) (j : Fin m) (prev : Option (ℕ × V)) : Prop :=
  ∀ x v, prev = some (x, v) → x ≤ snOf C ∧ v = hv v₀ C x ∧ Fetched rnd C j x

/-- Upper bound for `prev_sn`. -/
def PrevLt (prev : Option (ℕ × V)) (y : ℕ) : Prop := ∀ x v, prev = some (x, v) → x < y

/-- Reader invariant. -/
def RInv (C : Cfg m W Au V v₀) (j : Fin m) : Prop :=
  ((rOf C).bits j ≠ rnd (rOf C).seq j ↔ lastFx (C.loc (.rd j)) = some (rOf C).seq) ∧
  match C.loc (.rd j) with
  | .rIdle prev => C.pend (.rd j) = none ∧ PrevOK rnd C j prev
  | .rSN prev => C.pend (.rd j) = some (.read j) ∧ PrevOK rnd C j prev
  | .rFX prev y => C.pend (.rd j) = some (.read j) ∧ PrevOK rnd C j prev ∧ PrevLt prev y ∧
      y ≤ snOf C
  | .rCAS prev sn val => C.pend (.rd j) = some (.read j) ∧ PrevOK rnd C j prev ∧ PrevLt prev sn ∧
      sn ≤ (rOf C).seq ∧ sn ≤ snOf C + 1 ∧ val = hv v₀ C sn ∧ Fetched rnd C j sn
  | .rRet prev val => C.pend (.rd j) = some (.read j) ∧ PrevOK rnd C j prev ∧
      ∃ x, prev = some (x, val)
  | _ => False

/-- Facts about a triple `r` read from `R` by a writer holding sequence number `sn`. -/
def WR (C : Cfg m W Au V v₀) (sn : ℕ) (r : RVal m V) : Prop :=
  r.seq + 1 = sn ∧ r.seq ≤ (rOf C).seq ∧ r.val = hv v₀ C r.seq ∧
  (∀ j, readersOf rnd r j → Fetched rnd C j r.seq) ∧ sn ≤ snOf C + 1

/-- Writer invariant. -/
def WInv (C : Cfg m W Au V v₀) (w : W) : Prop :=
  match C.loc (.wr w) with
  | .wIdle => C.pend (.wr w) = none
  | .wSN v => C.pend (.wr w) = some (.write v)
  | .wR v sn => C.pend (.wr w) = some (.write v) ∧ 1 ≤ sn ∧ sn ≤ snOf C + 1
  | .wV v sn r => C.pend (.wr w) = some (.write v) ∧ WR rnd C sn r
  | .wB v sn r todo => C.pend (.wr w) = some (.write v) ∧ WR rnd C sn r ∧
      (C.mem (.V r.seq) : Option V) = some r.val ∧ todo ≠ [] ∧
      (∀ j ∈ todo, readersOf rnd r j) ∧
      (∀ j, readersOf rnd r j → j ∉ todo → (C.mem (.B r.seq j) : Bool) = true)
  | .wCAS v sn r => C.pend (.wr w) = some (.write v) ∧ WR rnd C sn r ∧
      (C.mem (.V r.seq) : Option V) = some r.val ∧
      (∀ j, readersOf rnd r j → (C.mem (.B r.seq j) : Bool) = true)
  | .wHelp sn => (∃ v, C.pend (.wr w) = some (.write v)) ∧ 1 ≤ sn ∧ sn ≤ (rOf C).seq
  | .wRet => ∃ v, C.pend (.wr w) = some (.write v)
  | _ => False

/-- The response an audit computes from the triple `r` it read (lines 18–21). -/
def Target (C : Cfg m W Au V v₀) (r : RVal m V) : Set (Fin m × V) :=
  {x | (∃ t < r.seq, Fetched rnd C x.1 t ∧ x.2 = hv v₀ C t) ∨ (readersOf rnd r x.1 ∧ x.2 = r.val)}

/-- An idle auditor's audit set covers the fetches below `lsa` and only contains fetches up to
`lsa`. -/
def IdleA (C : Cfg m W Au V v₀) (A : Set (Fin m × V)) (lsa : ℕ) : Prop :=
  (∀ i t, t < lsa → Fetched rnd C i t → (i, hv v₀ C t) ∈ A) ∧
  (∀ x ∈ A, ∃ t ≤ lsa, Fetched rnd C x.1 t ∧ x.2 = hv v₀ C t)

/-- Facts about a triple `r` read from `R` by an auditor. -/
def AOK (C : Cfg m W Au V v₀) (r : RVal m V) : Prop :=
  r.seq ≤ (rOf C).seq ∧ r.val = hv v₀ C r.seq ∧ (∀ i, readersOf rnd r i → Fetched rnd C i r.seq)

/-- Auditor invariant. -/
def AInv (C : Cfg m W Au V v₀) (a : Au) : Prop :=
  match C.loc (.au a) with
  | .aIdle A lsa => C.pend (.au a) = none ∧ lsa ≤ (rOf C).seq ∧ IdleA rnd C A lsa
  | .aR A lsa => C.pend (.au a) = some .audit ∧ lsa ≤ (rOf C).seq ∧ IdleA rnd C A lsa
  | .aV A r s => C.pend (.au a) = some .audit ∧ AOK rnd C r ∧ s < r.seq ∧
      (∀ i t, t < s → Fetched rnd C i t → (i, hv v₀ C t) ∈ A) ∧ A ⊆ Target rnd C r
  | .aB A r s val j => C.pend (.au a) = some .audit ∧ AOK rnd C r ∧ s < r.seq ∧
      val = some (hv v₀ C s) ∧ (∀ i t, t < s → Fetched rnd C i t → (i, hv v₀ C t) ∈ A) ∧
      (∀ i : Fin m, i.val < j.val → Fetched rnd C i s → (i, hv v₀ C s) ∈ A) ∧
      A ⊆ Target rnd C r
  | .aCAS A r => C.pend (.au a) = some .audit ∧ AOK rnd C r ∧ A = Target rnd C r
  | .aRet A lsa => C.pend (.au a) = some .audit ∧ lsa ≤ (rOf C).seq ∧ IdleA rnd C A lsa
  | _ => False

/-- The invariant of Algorithm 1. -/
structure Inv (C : Cfg m W Au V v₀) : Prop where
  sn_le : snOf C ≤ (rOf C).seq
  seq_le : (rOf C).seq ≤ snOf C + 1
  vsome : ∀ t < (rOf C).seq, (C.mem (.V t) : Option V) ≠ none
  vcur : ∀ t x, (rOf C).seq ≤ t → (C.mem (.V t) : Option V) = some x → t = (rOf C).seq ∧ x = (rOf C).val
  rd : ∀ j, RInv rnd C j
  wr : ∀ w, WInv rnd C w
  au : ∀ a, AInv rnd C a

/-- Memory evolution facts between consecutive reachable configurations. -/
structure Evo (C C' : Cfg m W Au V v₀) : Prop where
  sn : snOf C ≤ snOf C'
  seq : (rOf C).seq ≤ (rOf C').seq
  hv : ∀ t ≤ (rOf C).seq, hv v₀ C' t = hv v₀ C t
  fet : ∀ i t, Fetched rnd C i t → Fetched rnd C' i t
  fet_iff : ∀ i t, t < (rOf C).seq → (Fetched rnd C' i t ↔ Fetched rnd C i t)
  b : ∀ t j, (C.mem (.B t j) : Bool) = true → (C'.mem (.B t j) : Bool) = true
  v : ∀ t x, t ≤ (rOf C).seq → (C.mem (.V t) : Option V) = some x →
    (C'.mem (.V t) : Option V) = some x

section Transfer

variable {rnd} {C C' : Cfg m W Au V v₀} (E : Evo rnd C C')
include E

lemma Evo.prevOK {j : Fin m} {prev : Option (ℕ × V)} (h : PrevOK rnd C j prev)
    (hle : snOf C ≤ (rOf C).seq) : PrevOK rnd C' j prev := by
  intro x v hx
  obtain ⟨h1, h2, h3⟩ := h x v hx
  exact ⟨h1.trans E.sn, by rw [E.hv x (h1.trans hle)]; exact h2, E.fet _ _ h3⟩

lemma Evo.wr' {sn : ℕ} {r : RVal m V} (h : WR rnd C sn r) : WR rnd C' sn r := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2.trans E.seq, by rw [E.hv _ h2]; exact h3, fun j hj => E.fet _ _ (h4 j hj),
    h5.trans (by have := E.sn; omega)⟩

lemma Evo.aok {r : RVal m V} (h : AOK rnd C r) : AOK rnd C' r := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.trans E.seq, by rw [E.hv _ h1]; exact h2, fun j hj => E.fet _ _ (h3 j hj)⟩

lemma Evo.target {r : RVal m V} (h : r.seq ≤ (rOf C).seq) : Target rnd C' r = Target rnd C r := by
  ext ⟨i, v⟩
  simp only [Target, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨t, ht, hf, hv'⟩ | h')
    · exact Or.inl ⟨t, ht, (E.fet_iff _ _ (by omega)).1 hf, by rw [hv', E.hv _ (by omega)]⟩
    · exact Or.inr h'
  · rintro (⟨t, ht, hf, hv'⟩ | h')
    · exact Or.inl ⟨t, ht, E.fet _ _ hf, by rw [hv', E.hv _ (by omega)]⟩
    · exact Or.inr h'

lemma Evo.idleA {A : Set (Fin m × V)} {lsa : ℕ} (h : IdleA rnd C A lsa)
    (hl : lsa ≤ (rOf C).seq) : IdleA rnd C' A lsa := by
  refine ⟨fun i t ht hf => ?_, fun x hx => ?_⟩
  · rw [E.hv _ (by omega)]; exact h.1 i t ht ((E.fet_iff _ _ (by omega)).1 hf)
  · obtain ⟨t, ht, hf, hv'⟩ := h.2 x hx
    exact ⟨t, ht, E.fet _ _ hf, by rw [hv', E.hv _ (by omega)]⟩

lemma Evo.below {A : Set (Fin m × V)} {s : ℕ}
    (h : ∀ i t, t < s → Fetched rnd C i t → (i, AuditingWithoutLeaks.hv v₀ C t) ∈ A)
    (hs : s ≤ (rOf C).seq) :
    ∀ i t, t < s → Fetched rnd C' i t → (i, AuditingWithoutLeaks.hv v₀ C' t) ∈ A := by
  intro i t ht hf
  rw [E.hv _ (by omega)]; exact h i t ht ((E.fet_iff _ _ (by omega)).1 hf)

end Transfer

section EvoLemmas

variable {rnd : ℕ → Fin m → Bool} {C C' : Cfg m W Au V v₀}

lemma Evo.of_eq (hR : C'.mem .R = C.mem .R) (hV : ∀ t, C'.mem (.V t) = C.mem (.V t))
    (hB : ∀ t j, C'.mem (.B t j) = C.mem (.B t j)) (hS : snOf C ≤ snOf C') : Evo rnd C C' := by
  have hr : rOf C' = rOf C := hR
  refine ⟨hS, by rw [hr], fun t _ => by simp [AuditingWithoutLeaks.hv, hr, hV],
    fun i t hf => by simpa [Fetched, hr, hB] using hf, fun i t _ => by simp [Fetched, hr, hB],
    fun t j hb => by simpa [hB] using hb, fun t x _ hx => by simpa [hV] using hx⟩

lemma Evo.of_fx {j : Fin m} (hR : (C'.mem .R : RVal m V) = { rOf C with bits := flip (rOf C).bits j })
    (hV : ∀ t, C'.mem (.V t) = C.mem (.V t)) (hB : ∀ t j, C'.mem (.B t j) = C.mem (.B t j))
    (hS : snOf C' = snOf C) (hj : (rOf C).bits j = rnd (rOf C).seq j) : Evo rnd C C' := by
  have hr : rOf C' = { rOf C with bits := flip (rOf C).bits j } := hR
  refine ⟨hS.ge, by rw [hr], fun t _ => by simp [AuditingWithoutLeaks.hv, hr, hV],
    fun i t hf => ?_, fun i t ht => by simp [Fetched, hr, hB, ht.ne], fun t j hb => by
      simpa [hB] using hb, fun t x _ hx => by simpa [hV] using hx⟩
  simp only [Fetched, hr, hB] at hf ⊢
  rcases hf with hf | ⟨rfl, hf⟩
  · exact Or.inl hf
  · refine Or.inr ⟨rfl, ?_⟩
    by_cases hij : i = j
    · subst hij; simp [flip, hj]
    · simpa [flip, Function.update_of_ne hij] using hf

lemma Evo.of_cas {v : V} (hR : (C'.mem .R : RVal m V) = ⟨(rOf C).seq + 1, v, rnd ((rOf C).seq + 1)⟩)
    (hV : ∀ t, C'.mem (.V t) = C.mem (.V t)) (hB : ∀ t j, C'.mem (.B t j) = C.mem (.B t j))
    (hS : snOf C' = snOf C) (hVs : (C.mem (.V (rOf C).seq) : Option V) = some (rOf C).val)
    (hBs : ∀ i, readersOf rnd (rOf C) i → (C.mem (.B (rOf C).seq i) : Bool) = true) :
    Evo rnd C C' := by
  have hr : rOf C' = ⟨(rOf C).seq + 1, v, rnd ((rOf C).seq + 1)⟩ := hR
  refine ⟨hS.ge, by rw [hr]; simp, fun t ht => ?_, fun i t hf => ?_, fun i t ht => ?_,
    fun t j hb => by simpa [hB] using hb, fun t x _ hx => by simpa [hV] using hx⟩
  · simp only [AuditingWithoutLeaks.hv, hr, hV]
    rcases Nat.lt_or_eq_of_le ht with ht | rfl
    · simp [ht.ne, (show t ≠ (rOf C).seq + 1 by omega)]
    · simp [hVs]
  · simp only [Fetched, hr, hB] at hf ⊢
    rcases hf with ⟨ht, hb⟩ | ⟨rfl, hb⟩
    · exact Or.inl ⟨by omega, hb⟩
    · exact Or.inl ⟨by omega, hBs i hb⟩
  · simp only [Fetched, hr, hB]
    constructor
    · rintro (⟨-, hb⟩ | ⟨h1, -⟩)
      · exact Or.inl ⟨ht, hb⟩
      · omega
    · rintro (⟨-, hb⟩ | ⟨h1, -⟩)
      · exact Or.inl ⟨by omega, hb⟩
      · omega

lemma Evo.of_vwrite (hI : Inv rnd C) {t : ℕ} (ht : t ≤ (rOf C).seq)
    (hR : C'.mem .R = C.mem .R)
    (hV : ∀ t', t' ≠ t → C'.mem (.V t') = C.mem (.V t'))
    (hVt : (C'.mem (.V t) : Option V) = some (AuditingWithoutLeaks.hv v₀ C t))
    (hB : ∀ t j, C'.mem (.B t j) = C.mem (.B t j)) (hS : snOf C' = snOf C) : Evo rnd C C' := by
  have hr : rOf C' = rOf C := hR
  have key : ∀ x, (C.mem (.V t) : Option V) = some x → x = AuditingWithoutLeaks.hv v₀ C t := by
    intro x hx
    rcases Nat.lt_or_eq_of_le ht with ht' | rfl
    · simp [AuditingWithoutLeaks.hv, ht'.ne, hx]
    · obtain ⟨-, rfl⟩ := hI.vcur _ x le_rfl hx; simp [AuditingWithoutLeaks.hv]
  refine ⟨hS.ge, by rw [hr], fun t' ht' => ?_, fun i t hf => by simpa [Fetched, hr, hB] using hf,
    fun i t _ => by simp [Fetched, hr, hB], fun t j hb => by simpa [hB] using hb,
    fun t' x _ hx => ?_⟩
  · by_cases h : t' = t
    · subst h
      by_cases h2 : t' = (rOf C).seq
      · simp [AuditingWithoutLeaks.hv, hr, h2]
      · have hne := hI.vsome t' (by omega)
        obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hne
        have := key x hx
        simp only [AuditingWithoutLeaks.hv, hr, h2, ite_false, hVt, Option.getD_some]
    · simp [AuditingWithoutLeaks.hv, hr, hV t' h]
  · by_cases h : t' = t
    · subst h; rw [hVt, ← key x hx]
    · rw [hV t' h]; exact hx

lemma Evo.of_bwrite {t : ℕ} {j : Fin m} (hf : Fetched rnd C j t)
    (hR : C'.mem .R = C.mem .R) (hV : ∀ t, C'.mem (.V t) = C.mem (.V t))
    (hB : ∀ t' j', (t', j') ≠ (t, j) → C'.mem (.B t' j') = C.mem (.B t' j'))
    (hBt : (C'.mem (.B t j) : Bool) = true) (hS : snOf C' = snOf C) : Evo rnd C C' := by
  have hr : rOf C' = rOf C := hR
  have hBiff : ∀ t' j', t' < (rOf C).seq →
      ((C'.mem (.B t' j') : Bool) = true ↔ (C.mem (.B t' j') : Bool) = true) := by
    intro t' j' ht'
    by_cases h : (t', j') = (t, j)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rcases hf with ⟨-, hb⟩ | ⟨rfl, -⟩
      · simp [hBt, hb]
      · omega
    · rw [hB t' j' h]
  have hBmono : ∀ t' j', (C.mem (.B t' j') : Bool) = true → (C'.mem (.B t' j') : Bool) = true := by
    intro t' j' hb
    by_cases h : (t', j') = (t, j)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hBt
    · rw [hB t' j' h]; exact hb
  refine ⟨hS.ge, by rw [hr], fun t' _ => by simp [AuditingWithoutLeaks.hv, hr, hV],
    fun i t' hf' => ?_, fun i t' ht' => ?_, hBmono, fun t x _ hx => by simpa [hV] using hx⟩
  · simp only [Fetched, hr] at hf' ⊢
    rcases hf' with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨h1, hBmono _ _ h2⟩
    · exact Or.inr h
  · simp only [Fetched, hr]
    rw [hBiff _ _ ht']

end EvoLemmas

section Steps

variable {rnd : ℕ → Fin m → Bool}

lemma Evo.of_mem {C C' : Cfg m W Au V v₀} (h : C'.mem = C.mem) : Evo rnd C C' := by
  have hr : rOf C' = rOf C := by simp [rOf, h]
  refine ⟨by simp [snOf, h], by rw [hr], fun t _ => by simp [AuditingWithoutLeaks.hv, hr, h],
    fun i t hf => by simpa [Fetched, hr, h] using hf, fun i t _ => by simp [Fetched, hr, h],
    fun t j hb => by simpa [h] using hb, fun t x _ hx => by simpa [h] using hx⟩

lemma lastFx_le {C : Cfg m W Au V v₀} (hI : Inv rnd C) {j : Fin m} {x : ℕ}
    (h : lastFx (C.loc (.rd j)) = some x) : x ≤ (rOf C).seq := by
  have hr := (hI.rd j).2
  have hsn := hI.sn_le
  revert h hr
  cases C.loc (.rd j) <;> simp only [lastFx, Option.map_eq_some_iff, Prod.exists,
    exists_and_right, exists_eq_right, reduceCtorEq, imp_true_iff, IsEmpty.forall_iff]
  · rintro ⟨v, rfl⟩ ⟨-, h2⟩; have := (h2 _ _ rfl).1; omega
  · rintro ⟨v, rfl⟩ ⟨-, h2⟩; have := (h2 _ _ rfl).1; omega
  · rintro ⟨v, rfl⟩ ⟨-, h2, -⟩; have := (h2 _ _ rfl).1; omega
  · rintro ⟨⟩ ⟨-, -, -, h4, -⟩; omega
  · rintro ⟨v, rfl⟩ ⟨-, h2, -⟩; have := (h2 _ _ rfl).1; omega

/-- Transfer of a reader invariant along a memory evolution, the reader not moving. -/
lemma RInv.transfer {C C' : Cfg m W Au V v₀} (hI : Inv rnd C) (E : Evo rnd C C') {j : Fin m}
    (hloc : C'.loc (.rd j) = C.loc (.rd j)) (hpend : C'.pend (.rd j) = C.pend (.rd j))
    (hbit : (rOf C').bits j ≠ rnd (rOf C').seq j ↔ lastFx (C.loc (.rd j)) = some (rOf C').seq) :
    RInv rnd C' j := by
  have h := (hI.rd j).2
  have hle := hI.sn_le
  unfold RInv
  rw [hloc, hpend]
  refine ⟨hbit, ?_⟩
  revert h
  cases C.loc (.rd j) <;> simp only [imp_self]
  · rintro ⟨h1, h2⟩; exact ⟨h1, E.prevOK h2 hle⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, E.prevOK h2 hle⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, E.prevOK h2 hle, h3, h4.trans E.sn⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h1, E.prevOK h2 hle, h3, h4.trans E.seq, h5.trans (by have := E.sn; omega),
      by rw [E.hv _ h4]; exact h6, E.fet _ _ h7⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, E.prevOK h2 hle, h3⟩

/-- Transfer of a writer invariant along a memory evolution, the writer not moving. -/
lemma WInv.transfer {C C' : Cfg m W Au V v₀} (hI : Inv rnd C) (E : Evo rnd C C') {w : W}
    (hloc : C'.loc (.wr w) = C.loc (.wr w)) (hpend : C'.pend (.wr w) = C.pend (.wr w)) :
    WInv rnd C' w := by
  have h := hI.wr w
  unfold WInv at h ⊢
  rw [hloc, hpend]
  revert h
  cases C.loc (.wr w) <;> simp only [imp_self]
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3.trans (by have := E.sn; omega)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, E.wr' h2⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, E.wr' h2, E.v _ _ h2.2.1 h3, h4, h5, fun j hj hn => E.b _ _ (h6 j hj hn)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, E.wr' h2, E.v _ _ h2.2.1 h3, fun j hj => E.b _ _ (h4 j hj)⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3.trans E.seq⟩

/-- Transfer of an auditor invariant along a memory evolution, the auditor not moving. -/
lemma AInv.transfer {C C' : Cfg m W Au V v₀} (hI : Inv rnd C) (E : Evo rnd C C') {a : Au}
    (hloc : C'.loc (.au a) = C.loc (.au a)) (hpend : C'.pend (.au a) = C.pend (.au a)) :
    AInv rnd C' a := by
  have h := hI.au a
  unfold AInv at h ⊢
  rw [hloc, hpend]
  revert h
  cases C.loc (.au a) <;> simp only [imp_self]
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2.trans E.seq, E.idleA h3 h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2.trans E.seq, E.idleA h3 h2⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, E.aok h2, h3, E.below h4 (by have := h2.1; omega), by rw [E.target h2.1]; exact h5⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨h1, E.aok h2, h3, by rw [E.hv _ (by have := h2.1; omega)]; exact h4,
      E.below h5 (by have := h2.1; omega), fun i hi hf => ?_, by rw [E.target h2.1]; exact h7⟩
    rw [E.hv _ (by have := h2.1; omega)]
    exact h6 i hi ((E.fet_iff _ _ (by have := h2.1; omega)).1 hf)
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, E.aok h2, by rw [E.target h2.1]; exact h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2.trans E.seq, E.idleA h3 h2⟩

end Steps

section Main

variable {rnd : ℕ → Fin m → Bool} {C C' : Cfg m W Au V v₀}

/-- Per-process invariant. -/
def PInv (rnd : ℕ → Fin m → Bool) (C : Cfg m W Au V v₀) : Proc m W Au → Prop
  | .rd j => RInv rnd C j
  | .wr w => WInv rnd C w
  | .au a => AInv rnd C a

lemma Inv.assemble (hI : Inv rnd C) (E : Evo rnd C C') (p : Proc m W Au)
    (hpend : ∀ q, q ≠ p → C'.pend q = C.pend q) (hloc : ∀ q, q ≠ p → C'.loc q = C.loc q)
    (hbit : ∀ j, Proc.rd j ≠ p →
      ((rOf C').bits j ≠ rnd (rOf C').seq j ↔ lastFx (C.loc (.rd j)) = some (rOf C').seq))
    (g1 : snOf C' ≤ (rOf C').seq) (g2 : (rOf C').seq ≤ snOf C' + 1)
    (g3 : ∀ t < (rOf C').seq, (C'.mem (.V t) : Option V) ≠ none)
    (g4 : ∀ t x, (rOf C').seq ≤ t → (C'.mem (.V t) : Option V) = some x →
      t = (rOf C').seq ∧ x = (rOf C').val)
    (hown : PInv rnd C' p) : Inv rnd C' := by
  refine ⟨g1, g2, g3, g4, fun j => ?_, fun w => ?_, fun a => ?_⟩
  · by_cases h : Proc.rd j = p
    · subst h; exact hown
    · exact RInv.transfer hI E (hloc _ h) (hpend _ h) (hbit j h)
  · by_cases h : Proc.wr w = p
    · subst h; exact hown
    · exact WInv.transfer hI E (hloc _ h) (hpend _ h)
  · by_cases h : Proc.au a = p
    · subst h; exact hown
    · exact AInv.transfer hI E (hloc _ h) (hpend _ h)


lemma RInv.idle {j : Fin m} (h : RInv rnd C j) (hp : C.pend (.rd j) = none) :
    ∃ prev, C.loc (.rd j) = .rIdle prev ∧ PrevOK rnd C j prev := by
  obtain ⟨-, h⟩ := h
  revert h
  cases C.loc (.rd j) <;> simp_all

lemma WInv.idle {w : W} (h : WInv rnd C w) (hp : C.pend (.wr w) = none) :
    C.loc (.wr w) = .wIdle := by
  unfold WInv at h
  revert h
  cases C.loc (.wr w) <;> simp_all

lemma AInv.idle {a : Au} (h : AInv rnd C a) (hp : C.pend (.au a) = none) :
    ∃ A lsa, C.loc (.au a) = .aIdle A lsa ∧ lsa ≤ (rOf C).seq ∧ IdleA rnd C A lsa := by
  unfold AInv at h
  revert h
  cases C.loc (.au a) <;> simp_all

/-- The reader bit clause when `R` does not change. -/
lemma bit_of_R_eq (hI : Inv rnd C) (hR : rOf C' = rOf C) (j : Fin m) :
    (rOf C').bits j ≠ rnd (rOf C').seq j ↔ lastFx (C.loc (.rd j)) = some (rOf C').seq := by
  rw [hR]; exact (hI.rd j).1

lemma Inv.init : Inv rnd ((alg1 rnd v₀ : Impl _ _ (Proc m W Au) _).initCfg) := by
  refine ⟨by simp [snOf, rOf, Impl.initCfg, alg1], by simp [snOf, rOf, Impl.initCfg, alg1],
    fun t ht => by simp [rOf, Impl.initCfg, alg1] at ht, fun t x _ hx => by
      simp [Impl.initCfg, alg1] at hx, fun j => ?_, fun w => ?_, fun a => ?_⟩
  · simp [RInv, Impl.initCfg, alg1, locInit, lastFx, rOf, PrevOK]
  · simp [WInv, Impl.initCfg, alg1, locInit]
  · simp [AInv, Impl.initCfg, alg1, locInit, rOf, IdleA]

end Main

section TauReader

variable {rnd : ℕ → Fin m → Bool} {C C' : Cfg m W Au V v₀}

lemma tau_rd (hI : Inv rnd C) {j : Fin m} (h0 : C.pend (.rd j) ≠ none)
    (hpend : C'.pend = C.pend) {i : Obj m} {o : (BO m V v₀ i).Op}
    {k : (BO m V v₀ i).Resp → Loc m V}
    (hact : (alg1 (W := W) (Au := Au) rnd v₀).act (.rd j) (C.loc (.rd j)) = .access i o k)
    (hmem : C'.mem = Function.update C.mem i ((BO m V v₀ i).δ (C.mem i) o).1)
    (hloc : C'.loc = Function.update C.loc (.rd j) (k ((BO m V v₀ i).δ (C.mem i) o).2)) :
    Inv rnd C' ∧ Evo rnd C C' := by
  have hle := hI.sn_le
  have hle2 := hI.seq_le
  obtain ⟨hb, hr⟩ := hI.rd j
  have hlq : ∀ q, q ≠ Proc.rd j → C'.loc q = C.loc q := fun q hq => by
    simp [hloc, Function.update_of_ne hq]
  have hpq : ∀ q, q ≠ Proc.rd j → C'.pend q = C.pend q := fun q _ => by simp [hpend]
  cases hl : C.loc (.rd j) <;> rw [hl] at hr hb <;>
    simp only [alg1, readerAct, hl, reduceCtorEq] at hact
  case rSN prev =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hm : C'.mem = C.mem := by simp [hmem]
    have E : Evo rnd C C' := Evo.of_mem hm
    have hR : rOf C' = rOf C := by simp [rOf, hm]
    have hS : snOf C' = snOf C := by simp [snOf, hm]
    refine ⟨hI.assemble E (.rd j) hpq hlq (fun j' _ => bit_of_R_eq hI hR j')
      (by rw [hS, hR]; exact hle) (by rw [hS, hR]; exact hle2)
      (by simpa [hm, hR] using hI.vsome) (by simpa [hm, hR] using hI.vcur) ?_, E⟩
    obtain ⟨hp1, hp2⟩ := hr
    have hp2' := E.prevOK hp2 hle
    have hp1' : C'.pend (.rd j) = some (.read j) := by rw [hpend]; exact hp1
    by_cases hsil : prev.map Prod.fst = some (snOf C)
    · obtain ⟨⟨x, pv⟩, rfl, hx⟩ := Option.map_eq_some_iff.1 hsil
      simp only at hx
      have hnew : C'.loc (.rd j) = .rRet (some (x, pv)) pv := by
        have hx' : x = C.mem .SN := hx
        simp [hloc, hx']
      simp only [PInv, RInv, hnew, hR, hp1']
      exact ⟨hb, trivial, hp2', x, rfl⟩
    · have hnew : C'.loc (.rd j) = .rFX prev (snOf C) := by
        have : ¬ prev.map Prod.fst = some (C.mem .SN) := hsil
        simp [hloc, this, snOf]
      simp only [PInv, RInv, hnew, hR, hp1']
      refine ⟨hb, trivial, hp2', fun x v hx => ?_, by rw [hS]⟩
      have := (hp2 x v hx).1
      have hne : x ≠ snOf C := fun h => hsil (by simp [hx, h])
      omega
  case rFX prev y =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hr
    have hbj : (rOf C).bits j = rnd (rOf C).seq j := by
      by_contra hc
      obtain ⟨⟨x, v⟩, hx, hxe⟩ := Option.map_eq_some_iff.1 (hb.1 hc)
      have := hp3 x v hx
      simp at hxe; omega
    have hRm : (C'.mem .R : RVal m V) = { rOf C with bits := flip (rOf C).bits j } := by
      simp [hmem, rOf]
    have hR : rOf C' = { rOf C with bits := flip (rOf C).bits j } := hRm
    have hRs : (rOf C').seq = (rOf C).seq := by rw [hR]
    have hRv : (rOf C').val = (rOf C).val := by rw [hR]
    have hS : snOf C' = snOf C := by simp [snOf, hmem]
    have hnew : C'.loc (.rd j) = .rCAS prev (rOf C).seq (rOf C).val := by
      simp [hloc, rOf]
    have hp1' : C'.pend (.rd j) = some (.read j) := by rw [hpend]; exact hp1
    have E : Evo rnd C C' := Evo.of_fx hRm (fun t => by simp [hmem]) (fun t j => by simp [hmem])
      hS hbj
    refine ⟨hI.assemble E (.rd j) hpq hlq (fun j' hj' => ?_)
      (by rw [hS, hRs]; exact hle) (by rw [hS, hRs]; exact hle2)
      (by simpa [hmem, hRs] using hI.vsome) (fun t x ht hx => ?_) ?_, E⟩
    · have hne : j' ≠ j := fun h => hj' (by rw [h])
      rw [hR]; simpa [flip, Function.update_of_ne hne] using (hI.rd j').1
    · rw [hRs, hRv]; exact hI.vcur t x (by rwa [hRs] at ht) (by simpa [hmem] using hx)
    · simp only [PInv, RInv, hnew, hp1', lastFx, hRs]
      refine ⟨by rw [hR]; simp [flip, hbj], trivial, E.prevOK hp2 hle, fun x v hx => ?_,
        le_rfl, by rw [hS]; exact hle2, ?_, ?_⟩
      · have := hp3 x v hx; omega
      · simp [AuditingWithoutLeaks.hv, hRs, hRv]
      · right; refine ⟨hRs.symm, ?_⟩; rw [hR]; simp [flip, hbj]
  case rCAS prev sn val =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hr
    have hR : rOf C' = rOf C := by simp [rOf, hmem]
    have hSv : snOf C' = if snOf C = sn - 1 then sn else snOf C := by
      simp [snOf, hmem, casObject]; split_ifs <;> simp_all
    have hS1 : snOf C ≤ snOf C' := by rw [hSv]; split_ifs <;> omega
    have hS2 : sn ≤ snOf C' := by rw [hSv]; split_ifs <;> omega
    have hS3 : snOf C' ≤ (rOf C).seq := by rw [hSv]; split_ifs <;> omega
    have hnew : C'.loc (.rd j) = .rRet (some (sn, val)) val := by simp [hloc]
    have hp1' : C'.pend (.rd j) = some (.read j) := by rw [hpend]; exact hp1
    have E : Evo rnd C C' := Evo.of_eq (by simp [hmem]) (fun t => by simp [hmem])
      (fun t j => by simp [hmem]) hS1
    refine ⟨hI.assemble E (.rd j) hpq hlq (fun j' _ => bit_of_R_eq hI hR j')
      (by rw [hR]; exact hS3) (by rw [hR]; omega)
      (by simpa [hmem, hR] using hI.vsome) (by simpa [hmem, hR] using hI.vcur) ?_, E⟩
    simp only [PInv, RInv, hnew, hp1', lastFx, Option.map_some, hR]
    refine ⟨hb, trivial, fun x v hx => ?_, sn, rfl⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨hS2, by rw [E.hv _ hp4]; exact hp6, E.fet _ _ hp7⟩

end TauReader

section TauWriter

variable {rnd : ℕ → Fin m → Bool} {C C' : Cfg m W Au V v₀}

lemma mem_readers_todoOf {r : RVal m V} {j : Fin m} :
    j ∈ todoOf rnd r ↔ readersOf rnd r j := by
  simp [todoOf, readersOf]

lemma tau_wr (hI : Inv rnd C) {w : W} (h0 : C.pend (.wr w) ≠ none)
    (hpend : C'.pend = C.pend) {i : Obj m} {o : (BO m V v₀ i).Op}
    {k : (BO m V v₀ i).Resp → Loc m V}
    (hact : (alg1 (W := W) (Au := Au) rnd v₀).act (.wr w) (C.loc (.wr w)) = .access i o k)
    (hmem : C'.mem = Function.update C.mem i ((BO m V v₀ i).δ (C.mem i) o).1)
    (hloc : C'.loc = Function.update C.loc (.wr w) (k ((BO m V v₀ i).δ (C.mem i) o).2)) :
    Inv rnd C' ∧ Evo rnd C C' := by
  have hle := hI.sn_le
  have hle2 := hI.seq_le
  have hr := hI.wr w
  unfold WInv at hr
  have hlq : ∀ q, q ≠ Proc.wr w → C'.loc q = C.loc q := fun q hq => by
    simp [hloc, Function.update_of_ne hq]
  have hpq : ∀ q, q ≠ Proc.wr w → C'.pend q = C.pend q := fun q _ => by simp [hpend]
  cases hl : C.loc (.wr w) <;> rw [hl] at hr <;>
    simp only [alg1, writerAct, hl, reduceCtorEq] at hact
  case wSN v =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hm : C'.mem = C.mem := by simp [hmem]
    have E : Evo rnd C C' := Evo.of_mem hm
    have hR : rOf C' = rOf C := by simp [rOf, hm]
    have hS : snOf C' = snOf C := by simp [snOf, hm]
    have hnew : C'.loc (.wr w) = .wR v (snOf C + 1) := by simp [hloc, snOf]
    refine ⟨hI.assemble E (.wr w) hpq hlq (fun j' _ => bit_of_R_eq hI hR j')
      (by rw [hS, hR]; exact hle) (by rw [hS, hR]; exact hle2)
      (by simpa [hm, hR] using hI.vsome) (by simpa [hm, hR] using hI.vcur) ?_, E⟩
    simp only [PInv, WInv, hnew, hpend, hS]
    exact ⟨hr, by omega, le_rfl⟩
  case wR v sn =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨hp1, hp2, hp3⟩ := hr
    have hm : C'.mem = C.mem := by simp [hmem]
    have E : Evo rnd C C' := Evo.of_mem hm
    have hR : rOf C' = rOf C := by simp [rOf, hm]
    have hS : snOf C' = snOf C := by simp [snOf, hm]
    refine ⟨hI.assemble E (.wr w) hpq hlq (fun j' _ => bit_of_R_eq hI hR j')
      (by rw [hS, hR]; exact hle) (by rw [hS, hR]; exact hle2)
      (by simpa [hm, hR] using hI.vsome) (by simpa [hm, hR] using hI.vcur) ?_, E⟩
    by_cases hb : sn ≤ (rOf C).seq
    · have hnew : C'.loc (.wr w) = .wHelp sn := by
        have : sn ≤ (C.mem .R : RVal m V).seq := hb
        simp [hloc, this]
      simp only [PInv, WInv, hnew, hpend, hR]
      exact ⟨⟨v, hp1⟩, hp2, hb⟩
    · have hnew : C'.loc (.wr w) = .wV v sn (rOf C) := by
        have : ¬ sn ≤ (C.mem .R : RVal m V).seq := hb
        simp [hloc, this, rOf]
      simp only [PInv, WInv, hnew, hpend, hR]
      refine ⟨hp1, by omega, by rw [hR], by simp [AuditingWithoutLeaks.hv, hR], fun j hj => ?_,
        by rw [hS]; exact hp3⟩
      right; exact ⟨hR.symm ▸ rfl, by rw [hR]; exact hj⟩
  case wV v sn r =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨hp1, hw1, hw2, hw3, hw4, hw5⟩ := hr
    have hR : rOf C' = rOf C := by simp [rOf, hmem]
    have hS : snOf C' = snOf C := by simp [snOf, hmem]
    have hVt : (C'.mem (.V r.seq) : Option V) = some (AuditingWithoutLeaks.hv v₀ C r.seq) := by
      simp [hmem, ← hw3]
    have hVo : ∀ t, t ≠ r.seq → C'.mem (.V t) = C.mem (.V t) := fun t ht => by
      simp [hmem, Function.update_of_ne (show Obj.V t ≠ Obj.V r.seq by simpa using ht)]
    have E : Evo rnd C C' := Evo.of_vwrite hI hw2 (by simp [hmem]) hVo hVt
      (fun t j => by simp [hmem]) hS
    have hw' : WR rnd C' sn r := E.wr' ⟨hw1, hw2, hw3, hw4, hw5⟩
    have hVr : (C'.mem (.V r.seq) : Option V) = some r.val := by rw [hVt, ← hw3]
    refine ⟨hI.assemble E (.wr w) hpq hlq (fun j' _ => bit_of_R_eq hI hR j')
      (by rw [hS, hR]; exact hle) (by rw [hS, hR]; exact hle2) (fun t ht => ?_)
      (fun t x ht hx => ?_) ?_, E⟩
    · rw [hR] at ht
      by_cases h : t = r.seq
      · subst h; rw [hVr]; simp
      · rw [hVo t h]; exact hI.vsome t ht
    · rw [hR] at ht ⊢
      by_cases h : t = r.seq
      · subst h; rw [hVr] at hx; cases hx
        refine ⟨by omega, ?_⟩
        rw [hw3]; simp [AuditingWithoutLeaks.hv, (show r.seq = (rOf C).seq by omega)]
      · rw [hVo t h] at hx; exact hI.vcur t x ht hx
    · simp only [PInv, WInv, hloc, Function.update_self]
      cases htd : todoOf rnd r with
      | nil =>
        simp only [wBnext, hpend]
        refine ⟨hp1, hw', hVr, fun j hj => ?_⟩
        have := mem_readers_todoOf.2 hj; rw [htd] at this; cases this
      | cons j rest =>
        simp only [wBnext, hpend]
        refine ⟨hp1, hw', hVr, by simp, fun j' hj' => ?_, fun j' hj' hn => ?_⟩
        · rw [← htd] at hj'; exact mem_readers_todoOf.1 hj'
        · rw [← htd] at hn; exact absurd (mem_readers_todoOf.2 hj') hn
  case wB v sn r todo =>
    cases todo with
    | nil => simp at hact
    | cons j rest =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨hp1, hw, hVr, -, hw6, hw7⟩ := hr
    have hR : rOf C' = rOf C := by simp [rOf, hmem]
    have hS : snOf C' = snOf C := by simp [snOf, hmem]
    have hBt : (C'.mem (.B r.seq j) : Bool) = true := by simp [hmem]
    have hBo : ∀ t' j', (t', j') ≠ (r.seq, j) → C'.mem (.B t' j') = C.mem (.B t' j') := by
      intro t' j' h
      have : Obj.B t' j' ≠ Obj.B r.seq j := by intro h'; cases h'; exact h rfl
      simp [hmem, Function.update_of_ne this]
    have E : Evo rnd C C' := Evo.of_bwrite (hw.2.2.2.1 j (hw6 j (by simp))) (by simp [hmem])
      (fun t => by simp [hmem]) hBo hBt hS
    have hw' : WR rnd C' sn r := E.wr' hw
    have hVr' := E.v _ _ hw.2.1 hVr
    refine ⟨hI.assemble E (.wr w) hpq hlq (fun j' _ => bit_of_R_eq hI hR j')
      (by rw [hS, hR]; exact hle) (by rw [hS, hR]; exact hle2)
      (by simpa [hmem, hR] using hI.vsome) (by simpa [hmem, hR] using hI.vcur) ?_, E⟩
    have hB' : ∀ j', readersOf rnd r j' → j' ∉ rest → (C'.mem (.B r.seq j') : Bool) = true := by
      intro j' hj' hn
      by_cases h : j' = j
      · subst h; exact hBt
      · exact E.b _ _ (hw7 j' hj' (by simp [h, hn]))
    simp only [PInv, WInv, hloc, Function.update_self]
    cases rest with
    | nil =>
      simp only [wBnext, hpend]
      exact ⟨hp1, hw', hVr', fun j' hj' => hB' j' hj' (by simp)⟩
    | cons j2 rest2 =>
      simp only [wBnext, hpend]
      exact ⟨hp1, hw', hVr', by simp, fun j' hj' => hw6 j' (by simp at hj' ⊢; tauto), hB'⟩
  case wCAS v sn r =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨hp1, ⟨hw1, hw2, hw3, hw4, hw5⟩, hVr, hBr⟩ := hr
    by_cases heq : rOf C = r
    · -- successful compare&swap: `ρ_sn`
      subst heq
      have hRm : (C'.mem .R : RVal m V) = ⟨(rOf C).seq + 1, v, rnd ((rOf C).seq + 1)⟩ := by
        have : (C.mem .R : RVal m V) = rOf C := rfl
        simp [hmem, this, ← hw1]
      have hR : rOf C' = ⟨(rOf C).seq + 1, v, rnd ((rOf C).seq + 1)⟩ := hRm
      have hS : snOf C' = snOf C := by simp [snOf, hmem]
      have E : Evo rnd C C' := Evo.of_cas hRm (fun t => by simp [hmem]) (fun t j => by simp [hmem])
        hS hVr hBr
      have hnew : C'.loc (.wr w) = .wHelp sn := by
        have : (C.mem .R : RVal m V) = rOf C := rfl
        simp [hloc, this]
      refine ⟨hI.assemble E (.wr w) hpq hlq (fun j' _ => ?_)
        (by rw [hS, hR]; simp; omega) (by rw [hS, hR]; simp; omega) (fun t ht => ?_)
        (fun t x ht hx => ?_) ?_, E⟩
      · rw [hR]
        simp only [ne_eq, not_true_eq_false, false_iff]
        intro h
        have := lastFx_le hI h
        omega
      · rw [hR] at ht; simp only at ht
        have : C'.mem (.V t) = C.mem (.V t) := by simp [hmem]
        rw [this]
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
        · exact hI.vsome t ht
        · rw [hVr]; simp
      · rw [hR] at ht; simp only at ht
        have : C'.mem (.V t) = C.mem (.V t) := by simp [hmem]
        rw [this] at hx
        have := (hI.vcur t x (by omega) hx).1
        omega
      · simp only [PInv, WInv, hnew, hpend, hR]
        exact ⟨⟨v, hp1⟩, by omega, by omega⟩
    · -- failed compare&swap
      have hne : (C.mem .R : RVal m V) ≠ r := heq
      have hm : C'.mem = C.mem := by simp [hmem, hne]
      have E : Evo rnd C C' := Evo.of_mem hm
      have hR : rOf C' = rOf C := by simp [rOf, hm]
      have hS : snOf C' = snOf C := by simp [snOf, hm]
      have hnew : C'.loc (.wr w) = .wR v sn := by simp [hloc, hne]
      refine ⟨hI.assemble E (.wr w) hpq hlq (fun j' _ => bit_of_R_eq hI hR j')
        (by rw [hS, hR]; exact hle) (by rw [hS, hR]; exact hle2)
        (by simpa [hm, hR] using hI.vsome) (by simpa [hm, hR] using hI.vcur) ?_, E⟩
      simp only [PInv, WInv, hnew, hpend, hS]
      exact ⟨hp1, by omega, hw5⟩
  case wHelp sn =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨hp1, hp2, hp3⟩ := hr
    have hR : rOf C' = rOf C := by simp [rOf, hmem]
    have hSv : snOf C' = if snOf C = sn - 1 then sn else snOf C := by
      simp [snOf, hmem, casObject]; split_ifs <;> simp_all
    have hS1 : snOf C ≤ snOf C' := by rw [hSv]; split_ifs <;> omega
    have hS3 : snOf C' ≤ (rOf C).seq := by rw [hSv]; split_ifs <;> omega
    have hnew : C'.loc (.wr w) = .wRet := by simp [hloc]
    have E : Evo rnd C C' := Evo.of_eq (by simp [hmem]) (fun t => by simp [hmem])
      (fun t j => by simp [hmem]) hS1
    refine ⟨hI.assemble E (.wr w) hpq hlq (fun j' _ => bit_of_R_eq hI hR j')
      (by rw [hR]; exact hS3) (by rw [hR]; omega)
      (by simpa [hmem, hR] using hI.vsome) (by simpa [hmem, hR] using hI.vcur) ?_, E⟩
    simp only [PInv, WInv, hnew, hpend]
    exact hp1

end TauWriter

section TauAuditor

variable {rnd : ℕ → Fin m → Bool} {C C' : Cfg m W Au V v₀}

/-- The two outcomes of `aNext`. -/
lemma aNext_cases {A : Set (Fin m × V)} {r : RVal m V} {s : ℕ} (hA : AOK rnd C r)
    (hbelow : ∀ i t, t < s → Fetched rnd C i t → (i, hv v₀ C t) ∈ A)
    (hsub : A ⊆ Target rnd C r) (hs : s ≤ r.seq) :
    (s < r.seq ∧ aNext rnd A r s = .aV A r s) ∨
    (aNext rnd A r s = .aCAS (A ∪ bitPairs rnd r) r ∧ A ∪ bitPairs rnd r = Target rnd C r) := by
  by_cases h : s < r.seq
  · exact Or.inl ⟨h, by simp [aNext, h]⟩
  · refine Or.inr ⟨by simp [aNext, h], ?_⟩
    have hsr : s = r.seq := by omega
    apply Set.Subset.antisymm
    · rintro x (hx | ⟨h1, h2⟩)
      · exact hsub hx
      · exact Or.inr ⟨h1, h2⟩
    · rintro ⟨i, v⟩ (⟨t, ht, hf, rfl⟩ | ⟨h1, h2⟩)
      · exact Or.inl (hbelow i t (by omega) hf)
      · exact Or.inr ⟨h1, h2⟩

lemma tau_au (hI : Inv rnd C) {a : Au} (h0 : C.pend (.au a) ≠ none)
    (hpend : C'.pend = C.pend) {i : Obj m} {o : (BO m V v₀ i).Op}
    {k : (BO m V v₀ i).Resp → Loc m V}
    (hact : (alg1 (W := W) (Au := Au) rnd v₀).act (.au a) (C.loc (.au a)) = .access i o k)
    (hmem : C'.mem = Function.update C.mem i ((BO m V v₀ i).δ (C.mem i) o).1)
    (hloc : C'.loc = Function.update C.loc (.au a) (k ((BO m V v₀ i).δ (C.mem i) o).2)) :
    Inv rnd C' ∧ Evo rnd C C' := by
  have hle := hI.sn_le
  have hle2 := hI.seq_le
  have hr := hI.au a
  unfold AInv at hr
  have hlq : ∀ q, q ≠ Proc.au a → C'.loc q = C.loc q := fun q hq => by
    simp [hloc, Function.update_of_ne hq]
  have hpq : ∀ q, q ≠ Proc.au a → C'.pend q = C.pend q := fun q _ => by simp [hpend]
  cases hl : C.loc (.au a) <;> rw [hl] at hr <;>
    simp only [alg1, auditorAct, hl, reduceCtorEq] at hact
  case aCAS A r =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨hp1, hA, hT⟩ := hr
    have hR : rOf C' = rOf C := by simp [rOf, hmem]
    have hSv : snOf C' = if snOf C = r.seq - 1 then r.seq else snOf C := by
      simp [snOf, hmem, casObject]; split_ifs <;> simp_all
    have hS1 : snOf C ≤ snOf C' := by rw [hSv]; split_ifs <;> omega
    have hS3 : snOf C' ≤ (rOf C).seq := by have := hA.1; rw [hSv]; split_ifs <;> omega
    have hnew : C'.loc (.au a) = .aRet A r.seq := by simp [hloc]
    have E : Evo rnd C C' := Evo.of_eq (by simp [hmem]) (fun t => by simp [hmem])
      (fun t j => by simp [hmem]) hS1
    refine ⟨hI.assemble E (.au a) (fun q hq => hpq q hq) hlq (fun j' _ => bit_of_R_eq hI hR j')
      (by rw [hR]; exact hS3) (by rw [hR]; omega)
      (by simpa [hmem, hR] using hI.vsome) (by simpa [hmem, hR] using hI.vcur) ?_, E⟩
    simp only [PInv, AInv, hnew, hpend, hR]
    have hidle : IdleA rnd C A r.seq := by
      refine ⟨fun i t ht hf => ?_, fun x hx => ?_⟩
      · rw [hT]; exact Or.inl ⟨t, ht, hf, rfl⟩
      · rw [hT] at hx
        rcases hx with ⟨t, ht, hf, h2⟩ | ⟨h1, h2⟩
        · exact ⟨t, ht.le, hf, h2⟩
        · exact ⟨r.seq, le_rfl, hA.2.2 _ h1, by rw [h2, hA.2.1]⟩
    exact ⟨hp1, hA.1, E.idleA hidle hA.1⟩
  all_goals
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hm : C'.mem = C.mem := by simp [hmem]
    have E : Evo rnd C C' := Evo.of_mem hm
    have hR : rOf C' = rOf C := by simp [rOf, hm]
    have hS : snOf C' = snOf C := by simp [snOf, hm]
    refine ⟨hI.assemble E (.au a) hpq hlq (fun j' _ => bit_of_R_eq hI hR j')
      (by rw [hS, hR]; exact hle) (by rw [hS, hR]; exact hle2)
      (by simpa [hm, hR] using hI.vsome) (by simpa [hm, hR] using hI.vcur) ?_, E⟩
  case aR A lsa =>
    obtain ⟨hp1, hl1, hl2⟩ := hr
    have hA : AOK rnd C (rOf C) := ⟨le_rfl, by simp [AuditingWithoutLeaks.hv],
      fun i hi => Or.inr ⟨rfl, hi⟩⟩
    have hsub : A ⊆ Target rnd C (rOf C) := by
      intro x hx
      obtain ⟨t, ht, hf, h2⟩ := hl2.2 x hx
      rcases Nat.lt_or_eq_of_le (ht.trans hl1) with h | h
      · exact Or.inl ⟨t, h, hf, h2⟩
      · subst h
        rcases hf with ⟨h, -⟩ | ⟨-, hf⟩
        · omega
        · exact Or.inr ⟨hf, by rw [h2]; simp [AuditingWithoutLeaks.hv]⟩
    have hnew : C'.loc (.au a) = aNext rnd A (rOf C) lsa := by simp [hloc, rOf]
    have hp1' : C'.pend (.au a) = some .audit := by rw [hpend]; exact hp1
    simp only [PInv, AInv, hnew, hR]
    rcases aNext_cases hA hl2.1 hsub hl1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]; rw [← hR] at hA
      exact ⟨hp1', E.aok (by rw [hR] at hA; exact hA), h1, E.below hl2.1 hl1,
        by rw [E.target le_rfl]; exact hsub⟩
    · rw [h1]
      exact ⟨hp1', E.aok hA, by rw [E.target le_rfl, h2]⟩
  case aV A r s =>
    obtain ⟨hp1, hA, hs, hbelow, hsub⟩ := hr
    have hval : (C.mem (.V s) : Option V) = some (hv v₀ C s) := by
      have hne := hI.vsome s (by have := hA.1; omega)
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hne
      have hs' : s ≠ (rOf C).seq := by have := hA.1; omega
      simp [AuditingWithoutLeaks.hv, hs', hx]
    have hnew : C'.loc (.au a) = aVnext rnd A r s (some (hv v₀ C s)) := by
      simp [hloc, hval]
    have hp1' : C'.pend (.au a) = some .audit := by rw [hpend]; exact hp1
    have hsr : s ≤ (rOf C).seq := by have := hA.1; omega
    simp only [PInv, AInv, hnew]
    by_cases hm0 : 0 < m
    · simp only [aVnext, hm0, dite_true]
      refine ⟨hp1', E.aok hA, hs, by rw [E.hv _ hsr], E.below hbelow hsr,
        fun i hi => absurd hi (Nat.not_lt_zero _), by rw [E.target hA.1]; exact hsub⟩
    · simp only [aVnext, hm0, dite_false]
      have hb' : ∀ i t, t < s + 1 → Fetched rnd C i t → (i, hv v₀ C t) ∈ A := by
        intro i t ht hf
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
        · exact hbelow i t ht hf
        · exact absurd i.2 (by omega)
      rcases aNext_cases hA hb' hsub (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]
        exact ⟨hp1', E.aok hA, h1, E.below hb' (by have := hA.1; omega), by rw [E.target hA.1]; exact hsub⟩
      · rw [h1]
        exact ⟨hp1', E.aok hA, by rw [E.target hA.1, h2]⟩
  case aB A r s val j =>
    obtain ⟨hp1, hA, hs, hval, hbelow, hj, hsub⟩ := hr
    have hsr : s < (rOf C).seq := by have := hA.1; omega
    set b : Bool := C.mem (.B s j) with hbdef
    have hbF : b = true ↔ Fetched rnd C j s := by
      simp only [Fetched, hbdef]
      constructor
      · intro h; exact Or.inl ⟨hsr, h⟩
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact h
        · omega
    have hnew : C'.loc (.au a) = aBnext rnd (addPair A j val b) r s val j := by
      simp [hloc, hbdef]
    have hp1' : C'.pend (.au a) = some .audit := by rw [hpend]; exact hp1
    have hAsub : A ⊆ addPair A j val b := by
      intro x hx; cases b <;> cases val <;> simp [addPair, hx]
    have hsub' : addPair A j val b ⊆ Target rnd C r := by
      intro x hx
      cases hb : b <;> cases hv' : val <;> simp only [addPair, hb, hv'] at hx
      · exact hsub hx
      · exact hsub hx
      · exact hsub hx
      · rcases hx with rfl | hx
        · rw [hv'] at hval; cases hval
          exact Or.inl ⟨s, hs, hbF.1 hb, rfl⟩
        · exact hsub hx
    have hj' : ∀ i : Fin m, i.val < j.val + 1 → Fetched rnd C i s →
        (i, hv v₀ C s) ∈ addPair A j val b := by
      intro i hi hf
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact hAsub (hj i hi hf)
      · have : i = j := Fin.ext hi
        subst this
        rw [hbF.2 hf, hval]; simp [addPair]
    have hbelow' : ∀ i t, t < s → Fetched rnd C i t → (i, hv v₀ C t) ∈ addPair A j val b :=
      fun i t ht hf => hAsub (hbelow i t ht hf)
    simp only [PInv, AInv, hnew]
    by_cases hjm : j.val + 1 < m
    · simp only [aBnext, hjm, dite_true]
      refine ⟨hp1', E.aok hA, hs, by rw [E.hv _ hsr.le]; exact hval, E.below hbelow' hsr.le,
        fun i hi hf => ?_, by rw [E.target hA.1]; exact hsub'⟩
      rw [E.hv _ hsr.le]; exact hj' i hi ((E.fet_iff _ _ hsr).1 hf)
    · simp only [aBnext, hjm, dite_false]
      have hb' : ∀ i t, t < s + 1 → Fetched rnd C i t → (i, hv v₀ C t) ∈ addPair A j val b := by
        intro i t ht hf
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
        · exact hbelow' i t ht hf
        · exact hj' i (by have := i.2; omega) hf
      rcases aNext_cases hA hb' hsub' (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]
        exact ⟨hp1', E.aok hA, h1, E.below hb' (by have := hA.1; omega), by rw [E.target hA.1]; exact hsub'⟩
      · rw [h1]
        exact ⟨hp1', E.aok hA, by rw [E.target hA.1, h2]⟩

end TauAuditor

section MainStep

variable {rnd : ℕ → Fin m → Bool} {C C' : Cfg m W Au V v₀}

theorem Inv.step (hI : Inv rnd C) {ℓ : Label (Proc m W Au) (auditReg m V v₀)}
    (hs : (alg1 rnd v₀).step C ℓ = some C') : Inv rnd C' ∧ Evo rnd C C' := by
  cases ℓ with
  | inv p o =>
    obtain ⟨h0, hal, hpend, hloc, hmem⟩ := Impl.step_inv hs
    have E : Evo rnd C C' := Evo.of_mem hmem
    have hR : rOf C' = rOf C := by simp [rOf, hmem]
    have hS : snOf C' = snOf C := by simp [snOf, hmem]
    refine ⟨hI.assemble E p (fun q hq => by simp [hpend, Function.update_of_ne hq])
      (fun q hq => by simp [hloc, Function.update_of_ne hq]) (fun j _ => bit_of_R_eq hI hR j)
      (by rw [hS, hR]; exact hI.sn_le) (by rw [hS, hR]; exact hI.seq_le)
      (by simpa [hmem, hR] using hI.vsome) (by simpa [hmem, hR] using hI.vcur) ?_, E⟩
    have hle := hI.sn_le
    cases p with
    | rd j =>
      cases o <;> simp only [alg1, allowed, reduceCtorEq] at hal
      subst hal
      rename_i j
      obtain ⟨prev, hl, hprev⟩ := (hI.rd _).idle h0
      simp only [PInv, RInv, hloc, hpend, Function.update_self, hl, alg1, invoke, hR, lastFx]
      have hb := (hI.rd j).1
      rw [hl] at hb
      exact ⟨hb, trivial, E.prevOK hprev hle⟩
    | wr w =>
      cases o <;> simp only [alg1, allowed, reduceCtorEq] at hal
      have hl := (hI.wr w).idle h0
      simp [PInv, WInv, hloc, hpend, hl, alg1, invoke]
    | au a =>
      cases o <;> simp only [alg1, allowed, reduceCtorEq] at hal
      obtain ⟨A, lsa, hl, h1, h2⟩ := (hI.au a).idle h0
      simp only [PInv, AInv, hloc, hpend, Function.update_self, hl, alg1, invoke, hR]
      exact ⟨trivial, h1, E.idleA h2 h1⟩
  | ret p r =>
    obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hs
    have E : Evo rnd C C' := Evo.of_mem hmem
    have hR : rOf C' = rOf C := by simp [rOf, hmem]
    have hS : snOf C' = snOf C := by simp [snOf, hmem]
    refine ⟨hI.assemble E p (fun q hq => by simp [hpend, Function.update_of_ne hq])
      (fun q hq => by simp [hloc, Function.update_of_ne hq]) (fun j _ => bit_of_R_eq hI hR j)
      (by rw [hS, hR]; exact hI.sn_le) (by rw [hS, hR]; exact hI.seq_le)
      (by simpa [hmem, hR] using hI.vsome) (by simpa [hmem, hR] using hI.vcur) ?_, E⟩
    have hle := hI.sn_le
    cases p with
    | rd j =>
      obtain ⟨hb, hr⟩ := hI.rd j
      cases hl : C.loc (.rd j) <;> rw [hl] at hr hb <;>
        simp only [alg1, readerAct, hl, Action.ret.injEq, reduceCtorEq] at hact <;>
        simp only [false_and, and_false, IsEmpty.forall_iff, not_true_eq_false] at hr
      · exact absurd hr.1 h0
      · obtain ⟨rfl, rfl⟩ := hact
        obtain ⟨-, h2, x, rfl⟩ := hr
        simp only [PInv, RInv, hloc, hpend, Function.update_self, hR, lastFx]
        exact ⟨hb, trivial, E.prevOK h2 hle⟩
    | wr w =>
      have hr := hI.wr w
      unfold WInv at hr
      cases hl : C.loc (.wr w) <;> rw [hl] at hr <;>
        simp only [alg1, writerAct, hl, Action.ret.injEq, reduceCtorEq] at hact <;>
        simp only [false_and, and_false, IsEmpty.forall_iff, not_true_eq_false] at hr
      · exact absurd hr h0
      · rename_i todo
        cases todo with
        | nil => exact absurd rfl hr.2.2.2.1
        | cons j rest => simp at hact
      · obtain ⟨rfl, rfl⟩ := hact
        simp [PInv, WInv, hloc, hpend]
    | au a =>
      have hr := hI.au a
      unfold AInv at hr
      cases hl : C.loc (.au a) <;> rw [hl] at hr <;>
        simp only [alg1, auditorAct, hl, Action.ret.injEq, reduceCtorEq] at hact <;>
        simp only [false_and, and_false, IsEmpty.forall_iff, not_true_eq_false] at hr
      · exact absurd hr.1 h0
      · obtain ⟨rfl, rfl⟩ := hact
        obtain ⟨-, h2, h3⟩ := hr
        simp only [PInv, AInv, hloc, hpend, Function.update_self, hR]
        exact ⟨trivial, h2, E.idleA h3 h2⟩
  | tau p =>
    obtain ⟨h0, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
    cases p with
    | rd j => exact tau_rd hI h0 hpend hact hmem hloc
    | wr w => exact tau_wr hI h0 hpend hact hmem hloc
    | au a => exact tau_au hI h0 hpend hact hmem hloc

/-- The invariant holds in every reachable configuration. -/
theorem Inv.of_run {α : List (Label (Proc m W Au) (auditReg m V v₀))}
    (h : (alg1 rnd v₀).run α = some C) : Inv rnd C :=
  Impl.invariant_of_run Inv.init (fun _ _ _ hC hs => (Inv.step hC hs).1) h

end MainStep

end

end Podc.AuditingWithoutLeaks

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au] {v₀ : V}
  {rnd : ℕ → Fin m → Bool} {C C' : Cfg m W Au V v₀}

/-- During a `D` phase (`R.seq = SN + 1`), the writer of the last successful compare&swap on `R`
is still poised to apply line 15. -/
def DInv (C : Cfg m W Au V v₀) : Prop :=
  (rOf C).seq = snOf C + 1 → ∃ w, C.loc (.wr w) = .wHelp (rOf C).seq

theorem DInv.step (hI : Inv rnd C) (hD : DInv C) {ℓ : Label (Proc m W Au) (auditReg m V v₀)}
    (hs : (alg1 rnd v₀).step C ℓ = some C') : DInv C' := by
  obtain ⟨hI', E⟩ := Inv.step hI hs
  intro hD'
  -- the sequence number of `R` did not change, or the step is a successful `ρ`
  by_cases hseq : (rOf C').seq = (rOf C).seq
  · have hsn : snOf C' = snOf C := by
      have := E.sn; have := hI.seq_le; omega
    obtain ⟨w, hw⟩ := hD (by rw [← hseq, hD', hsn])
    rw [hseq]
    refine ⟨w, ?_⟩
    cases ℓ with
    | inv p o =>
      obtain ⟨h0, -, -, hloc, -⟩ := Impl.step_inv hs
      have hne : Proc.wr w ≠ p := by
        rintro rfl
        have := hI.wr w; unfold WInv at this; rw [hw] at this
        obtain ⟨⟨v, hv⟩, -⟩ := this; rw [h0] at hv; cases hv
      rw [hloc, Function.update_of_ne hne]; exact hw
    | ret p r =>
      obtain ⟨-, -, -, l, hact, hloc⟩ := Impl.step_ret hs
      have hne : Proc.wr w ≠ p := by
        rintro rfl; rw [hw] at hact; simp [alg1, writerAct] at hact
      rw [hloc, Function.update_of_ne hne]; exact hw
    | tau p =>
      obtain ⟨-, -, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
      by_cases hne : Proc.wr w = p
      · subst hne
        rw [hw] at hact
        simp only [alg1, writerAct, Action.access.injEq] at hact
        obtain ⟨rfl, ho, -⟩ := hact
        obtain rfl := eq_of_heq ho
        exfalso
        have : snOf C' = (rOf C).seq := by
          have h1 : snOf C = (rOf C).seq - 1 := by omega
          simp only [snOf] at h1 ⊢
          simp [hmem, casObject, h1]
        omega
      · rw [hloc, Function.update_of_ne hne]; exact hw
  · -- `R.seq` changed: a writer applied a successful compare&swap
    cases ℓ with
    | inv p o =>
      obtain ⟨-, -, -, -, hmem⟩ := Impl.step_inv hs
      exact absurd (by simp [rOf, hmem]) hseq
    | ret p r =>
      obtain ⟨-, -, hmem, -⟩ := Impl.step_ret hs
      exact absurd (by simp [rOf, hmem]) hseq
    | tau p =>
      obtain ⟨-, -, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
      cases p with
      | rd j =>
        exfalso; apply hseq
        cases hl : C.loc (.rd j) <;> simp only [alg1, readerAct, hl, reduceCtorEq] at hact <;>
          simp only [Action.access.injEq] at hact <;> obtain ⟨rfl, ho, -⟩ := hact <;>
          obtain rfl := eq_of_heq ho <;> simp [rOf, hmem]
      | au a =>
        exfalso; apply hseq
        cases hl : C.loc (.au a) <;> simp only [alg1, auditorAct, hl, reduceCtorEq] at hact <;>
          simp only [Action.access.injEq] at hact <;> obtain ⟨rfl, ho, -⟩ := hact <;>
          obtain rfl := eq_of_heq ho <;> simp [rOf, hmem]
      | wr w =>
        refine ⟨w, ?_⟩
        cases hl : C.loc (.wr w) <;> simp only [alg1, writerAct, hl, reduceCtorEq] at hact
        case wCAS v sn r =>
          simp only [Action.access.injEq] at hact
          obtain ⟨rfl, ho, hk⟩ := hact
          obtain rfl := eq_of_heq ho
          obtain rfl := eq_of_heq hk
          by_cases heq : (C.mem .R : RVal m V) = r
          · have : (C'.mem .R : RVal m V) = ⟨sn, v, rnd sn⟩ := by simp [hmem, heq]
            simp [hloc, heq, rOf, this]
          · exact absurd (by simp [rOf, hmem, heq]) hseq
        case wB v sn r todo =>
          cases todo with
          | nil => simp at hact
          | cons j rest =>
            simp only [Action.access.injEq] at hact
            obtain ⟨rfl, -, -⟩ := hact
            exact absurd (by simp [rOf, hmem]) hseq
        all_goals
          simp only [Action.access.injEq] at hact
          obtain ⟨rfl, ho, -⟩ := hact
          obtain rfl := eq_of_heq ho
          exact absurd (by simp [rOf, hmem]) hseq

theorem DInv.of_run {α : List (Label (Proc m W Au) (auditReg m V v₀))}
    (h : (alg1 rnd v₀).run α = some C) : DInv C := by
  have := Impl.run_induction (I := alg1 rnd v₀) (Q := fun _ C => Inv rnd C ∧ DInv C)
    ⟨Inv.init, fun h => by simp [rOf, snOf, Impl.initCfg, alg1] at h⟩
    (fun _ _ _ _ _ hC hs => ⟨(Inv.step hC.1 hs).1, DInv.step hC.1 hC.2 hs⟩) h
  exact this.2

end Podc.AuditingWithoutLeaks
