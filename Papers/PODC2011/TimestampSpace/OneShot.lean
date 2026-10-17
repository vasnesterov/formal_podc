import Papers.PODC2011.TimestampSpace.Moves

/-!
# Theorem 1.2: the one-shot lower bound

Any one-shot timestamp implementation from read/write-like base objects satisfying
(non-deterministic) solo termination, for `n ≥ 3` processes, uses at least
`⌊√(2n)⌋ - ⌈log₂ n⌉ - 2` base objects (`theorem_1_2`).

The proof follows Section 4 of the paper (the "grid" construction), with the bookkeeping made
explicit through the invariant `Inv m n α C R ℓ` (with `m = ⌊√(2n)⌋`, `j = |R|`):
* `full`: every object of `R` is covered by at least `ℓ - j` processes;
* `sparse`: no nonempty set `S` of objects outside `R` has all its objects covered by at least
  `ℓ + 1 - j - |S|` processes (in the paper's grid picture: no new column reaches the diagonal);
* `nbound`: the number of processes that are not idle and do not cover an object outside `R` is
  at most `∑_{c=1}^{j} (m - c)` (this replaces the paper's "association" argument);
* `idleb`: `(#idle - 1) · 2^(m-ℓ) < n` (each decrease of `ℓ` halves the idle processes);
* `ℓ ≤ m` and `m - ℓ ≤ ⌈log₂ n⌉`.
One step (`step`) applies Lemma 4.1 and stops at the *first* move after which a new set `Q` of
columns reaches the diagonal (`HasFull`); then `R := R ∪ Q` and `ℓ` decreases by one only in the
paper's "Case 2". The construction stops when `ℓ < j + 3`, giving `j ≥ m - ⌈log₂ n⌉ - 2`.
Idle processes never run out (`idle_ge_two`), which is the paper's claim that
`|idle(C_last)| ≤ 1` is impossible.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp

open Cslib.SharedMemory Impl

variable {P : Type} [DecidableEq P] {T : Type} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec}
  {L : Type} {I : Impl (tsObj T) B P L}

/-! ### Block-write moves -/

/-- The moves of a block write (one `tau` step per process). -/
def bm (c : List (P × ι)) : List (P × List (Label P (tsObj T))) :=
  c.map (fun x => (x.1, [Label.tau x.1]))

lemma flat_bm (c : List (P × ι)) : flat (bm (T := T) c) = bw c := by
  induction c with
  | nil => rfl
  | cons x c ih =>
    show [Label.tau x.1] ++ flat (bm c) = _
    rw [ih]; rfl

lemma bm_owned (c : List (P × ι)) : Owned (bm (T := T) c) := by
  intro m hm ℓ hℓ
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hm
  simp only [List.mem_singleton] at hℓ; subst hℓ; rfl

@[simp] lemma bm_map_fst (c : List (P × ι)) : (bm (T := T) c).map Prod.fst = c.map Prod.fst := by
  simp [bm, Function.comp_def]

@[simp] lemma bm_length (c : List (P × ι)) : (bm (T := T) c).length = c.length := by simp [bm]

variable [Fintype P] [Fintype ι]

/-! ### Three disjoint block writes covering `R` -/

/-- If every object of `R` is covered by at least three processes, then `R` is covered by three
disjoint block writes, each with exactly one writer per object. -/
lemma exists_triple_ge (C : Config (tsObj T) B P L) (R : Finset ι)
    (h3 : ∀ r ∈ R, 3 ≤ sig I C r) :
    ∃ b₀ b₁ b₂, Triple I C (↑R : Set ι) b₀ b₁ b₂ ∧ (b₀.map Prod.snd).Nodup ∧
      (b₁.map Prod.snd).Nodup := by
  classical
  rcases isEmpty_or_nonempty P with hP | hP
  · have : R = ∅ := by
      ext r; simp only [Finset.notMem_empty, iff_false]; intro hr
      have := h3 r hr; rw [sig_eq_card] at this; simp [Finset.univ_eq_empty] at this
    subst this
    exact ⟨[], [], [], ⟨by simp, by simp, by simp, by simp, by simp⟩, by simp, by simp⟩
  have hf : ∀ i : ι, ∃ f : Fin 3 → P, i ∈ R →
      Function.Injective f ∧ ∀ j, I.Covers C (f j) i := by
    intro i
    by_cases hi : i ∈ R
    · have h := h3 i hi
      rw [sig_eq_card] at h
      obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq h
      obtain ⟨a, b, c, hab, hac, hbc, he⟩ := Finset.card_eq_three.1 htc
      have hmem : ∀ q ∈ ({a, b, c} : Finset P), I.Covers C q i := by
        intro q hq; rw [← he] at hq; have := ht hq; simpa using this
      refine ⟨![a, b, c], fun _ => ⟨?_, fun j => hmem _ ?_⟩⟩
      · intro x y hxy
        fin_cases x <;> fin_cases y <;> simp_all [eq_comm]
      · fin_cases j <;> simp
    · exact ⟨fun _ => Classical.arbitrary P, fun h => absurd h hi⟩
  choose f hf using hf
  set Rl := R.toList with hRl
  have hRl_nd : Rl.Nodup := Finset.nodup_toList _
  have hmemRl : ∀ i, i ∈ Rl ↔ i ∈ R := by intro i; simp [hRl]
  let b : Fin 3 → List (P × ι) := fun j => Rl.map (fun i => (f i j, i))
  have hcov : ∀ j, ∀ c ∈ b j, I.Covers C c.1 c.2 := by
    intro j c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    exact (hf i ((hmemRl i).1 hi)).2 j
  have hsnd : ∀ j, (b j).map Prod.snd = Rl := by intro j; simp [b, Function.comp_def]
  have hfst : ∀ j, (b j).map Prod.fst = Rl.map (fun i => f i j) := by
    intro j; simp [b, Function.comp_def]
  have hinj : ∀ j j' i i', i ∈ Rl → i' ∈ Rl → f i j = f i' j' → i = i' ∧ j = j' := by
    intro j j' i i' hi hi' he
    have h1 := (hf i ((hmemRl i).1 hi)).2 j
    have h2 := (hf i' ((hmemRl i').1 hi')).2 j'
    rw [he] at h1
    have hii := Covers.unique h1 h2
    subst hii
    exact ⟨rfl, (hf i ((hmemRl i).1 hi)).1 he⟩
  have hnd1 : ∀ j, (Rl.map (fun i => f i j)).Nodup := fun j =>
    hRl_nd.map_on (fun i hi i' hi' he => (hinj j j i i' hi hi' he).1)
  have hdisj : ∀ j j', j ≠ j' → ∀ x ∈ Rl.map (fun i => f i j), ∀ y ∈ Rl.map (fun i => f i j'),
      x ≠ y := by
    intro j j' hjj x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hy
    exact hjj (hinj j j' i i' hi hi' hxy).2
  refine ⟨b 0, b 1, b 2, ⟨?_, ?_, ?_, ?_, ?_⟩, by rw [hsnd]; exact hRl_nd,
    by rw [hsnd]; exact hRl_nd⟩
  · rw [hfst, hfst, hfst]
    refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨hnd1 0, hnd1 1, ?_⟩, hnd1 2, ?_⟩
    · exact hdisj 0 1 (by decide)
    · intro x hx y hy
      rcases List.mem_append.1 hx with hx | hx
      · exact hdisj 0 2 (by decide) x hx y hy
      · exact hdisj 1 2 (by decide) x hx y hy
  · intro c hc
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact hcov 0 c hc
    · exact hcov 1 c hc
    · exact hcov 2 c hc
  all_goals intro i; rw [hsnd, Finset.mem_coe, ← hmemRl]

/-! ### Idle processes, coverage outside `R` -/

open Classical in
/-- Processes that have not invoked anything in `α`. -/
noncomputable def idleSet (α : List (Label P (tsObj T))) : Finset P :=
  Finset.univ.filter (fun p => opsOf α p = [])

open Classical in
/-- Processes covering an object outside `R`. -/
noncomputable def outCov (I : Impl (tsObj T) B P L) (C : Config (tsObj T) B P L) (R : Finset ι) :
    Finset P :=
  Finset.univ.filter (fun p => ∃ r ∉ R, I.Covers C p r)

open Classical in
/-- Processes that are not idle and do not cover an object outside `R`. -/
noncomputable def NSet (I : Impl (tsObj T) B P L) (α : List (Label P (tsObj T)))
    (C : Config (tsObj T) B P L) (R : Finset ι) : Finset P :=
  Finset.univ.filter (fun p => opsOf α p ≠ [] ∧ ¬ ∃ r ∉ R, I.Covers C p r)

lemma mem_idleSet {α : List (Label P (tsObj T))} {p : P} : p ∈ idleSet α ↔ opsOf α p = [] := by
  classical
  simp [idleSet]

lemma mem_outCov {C : Config (tsObj T) B P L} {R : Finset ι} {p : P} :
    p ∈ outCov I C R ↔ ∃ r ∉ R, I.Covers C p r := by
  classical
  simp [outCov]

lemma mem_NSet {α : List (Label P (tsObj T))} {C : Config (tsObj T) B P L} {R : Finset ι} {p : P} :
    p ∈ NSet I α C R ↔ opsOf α p ≠ [] ∧ ¬ ∃ r ∉ R, I.Covers C p r := by
  classical
  simp [NSet]

lemma card_outCov (C : Config (tsObj T) B P L) (R : Finset ι) :
    (outCov I C R).card = ∑ r ∈ Rᶜ, sig I C r := by
  classical
  rw [sum_sig]
  congr 1; ext p; simp [outCov]

/-- The processes split into idle ones, `NSet` and `outCov`. -/
lemma card_partition {α : List (Label P (tsObj T))} {C : Config (tsObj T) B P L}
    (h : I.run α = some C) (R : Finset ι) :
    Fintype.card P = (idleSet α).card + (NSet I α C R).card + (outCov I C R).card := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun p => opsOf α p = [])
  have h2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p => ¬ opsOf α p = [])) (fun p => ∃ r ∉ R, I.Covers C p r)
  have e1 : (Finset.univ.filter (fun p => ¬ opsOf α p = [])).filter
      (fun p => ∃ r ∉ R, I.Covers C p r) = outCov I C R := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_outCov]
    constructor
    · exact fun h => h.2
    · intro hc
      obtain ⟨r, -, hr⟩ := id hc
      exact ⟨not_idle_of_pend h hr.1, hc⟩
  have e2 : (Finset.univ.filter (fun p => ¬ opsOf α p = [])).filter
      (fun p => ¬ ∃ r ∉ R, I.Covers C p r) = NSet I α C R := by
    ext p; simp [NSet]
  rw [e1, e2] at h2
  rw [Finset.card_univ] at h1
  simp only [idleSet]
  omega

/-! ### The invariant -/

variable (I) in
/-- Some nonempty set `Q` of objects outside `R` reaches the diagonal: each object of `Q` is
covered by at least `ℓ - |R| - |Q|` processes. -/
def HasFull (C : Config (tsObj T) B P L) (R : Finset ι) (ℓ : ℕ) : Prop :=
  ∃ Q : Finset ι, Q.Nonempty ∧ Disjoint Q R ∧ ∀ r ∈ Q, ℓ ≤ sig I C r + Q.card + R.card

variable (I) in
/-- The invariant of the construction of Section 4 (see the module docstring). -/
structure Inv (m n : ℕ) (α : List (Label P (tsObj T))) (C : Config (tsObj T) B P L)
    (R : Finset ι) (ℓ : ℕ) : Prop where
  run : I.run α = some C
  adm : Adm true α
  full : ∀ r ∈ R, ℓ ≤ sig I C r + R.card
  sparse : ∀ S : Finset ι, Disjoint S R → S.Nonempty → ∃ r ∈ S, sig I C r + S.card + R.card ≤ ℓ
  nbound : (NSet I α C R).card ≤ stair m R.card
  idleb : ((idleSet α).card - 1) * 2 ^ (m - ℓ) < n
  lem : ℓ ≤ m
  dclog : m - ℓ ≤ Nat.clog 2 n

lemma sum_sig_compl_le {m n : ℕ} {α : List (Label P (tsObj T))} {C : Config (tsObj T) B P L}
    {R : Finset ι} {ℓ : ℕ} (hInv : Inv I m n α C R ℓ) (S : Finset ι) (hS : Disjoint S R) :
    ∑ r ∈ S, sig I C r ≤ stair (ℓ - R.card) S.card := by
  refine sum_le_stair S (sig I C) (ℓ - R.card) (fun S' hS' hne => ?_) S le_rfl
  obtain ⟨r, hr, h⟩ := hInv.sparse S' (Finset.disjoint_of_subset_left hS' hS) hne
  exact ⟨r, hr, by omega⟩

/-- Idle processes never run out (the paper: `|idle(C_last)| ≤ 1` is impossible). -/
lemma idle_ge_two {α : List (Label P (tsObj T))} {C : Config (tsObj T) B P L} {R : Finset ι} {ℓ : ℕ}
    (hInv : Inv I (Nat.sqrt (2 * Fintype.card P)) (Fintype.card P) α C R ℓ)
    (hn : 3 ≤ Fintype.card P) (hι : Fintype.card ι ≤ Nat.sqrt (2 * Fintype.card P)) :
    2 ≤ (idleSet α).card := by
  set n := Fintype.card P
  set m := Nat.sqrt (2 * n)
  have hpart := card_partition hInv.run R
  have hout := card_outCov (I := I) C R
  have h1 := sum_sig_compl_le hInv Rᶜ disjoint_compl_left
  have hRc : (Rᶜ).card = Fintype.card ι - R.card := Finset.card_compl R
  have hRle : R.card ≤ Fintype.card ι := Finset.card_le_univ R
  have h2 : stair (ℓ - R.card) (Rᶜ).card ≤ stair (m - R.card) (m - R.card) :=
    (stair_mono_left (by have := hInv.lem; omega) _).trans (stair_mono_right _ (by omega))
  have h3 := stair_add m R.card (m - R.card)
  rw [show R.card + (m - R.card) = m by omega] at h3
  have h4 : stair m m + 2 ≤ n := stair_sqrt_le n hn
  have h5 := hInv.nbound
  omega

/-- The initial configuration satisfies the invariant (if there are at most `m` objects). -/
lemma inv_init (hn : 1 ≤ Fintype.card P) {m : ℕ} (hι : Fintype.card ι ≤ m) :
    Inv I m (Fintype.card P) [] I.initCfg ∅ m := by
  classical
  have hsig : ∀ r, sig I I.initCfg r = 0 := by
    intro r; rw [sig_eq_card]; simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ h; exact h.1 rfl
  refine ⟨rfl, fun _ p => by simp [getTSCount, opsOf], by simp, fun S _ hne => ?_, ?_, ?_,
    le_rfl, by simp⟩
  · obtain ⟨r, hr⟩ := hne
    refine ⟨r, hr, ?_⟩
    rw [hsig]; have := Finset.card_le_univ S; simp; omega
  · have : NSet I [] I.initCfg ∅ = ∅ := by
      ext p; simp [mem_NSet, opsOf]
    simp [this]
  · have : idleSet ([] : List (Label P (tsObj T))) = Finset.univ := by
      ext p; simp [mem_idleSet, opsOf]
    simp [this]; omega

end Cslib.SharedMemory.Timestamp
