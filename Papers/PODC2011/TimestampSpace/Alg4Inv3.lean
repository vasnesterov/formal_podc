import Papers.PODC2011.TimestampSpace.Alg4Correct

/-!
# Algorithm 4: the phase / charging invariant (Claims 6.6–6.13)

Ghost: phase `ph` (started at time `pst`), registers `wc` written in the current phase,
number `ninv` of invalidation writes, credits `cr`, `free` registers (see `Alg4.lean`).

* `count`: `ninv ≥ Σ_{ϕ < ph} ϕ + |wc|` — every completed phase `ϕ` contains (at least) `ϕ`
  invalidation writes (Claims 6.7–6.10: the getTS that starts phase `ϕ + 1` has seen all of
  `R[1..ϕ]` written in phase `ϕ`).
* `credit`: `ninv + ph + |cr| ≤ 2 · #getTS` — the charging argument of Claim 6.13: each getTS
  brings two credits; an invalidation write consumes one (the writer's "last write" credit for
  writes at lines 8, 15 and line-11 writes after `R[myrnd+1] ≠ ⊥` (`I₁ ∪ I₂`), the writer's
  "first invalidation" credit (`I₃`), or the "last write" credit of the writer of the
  overwritten value (`I₄`, that value is then `free`)); additionally the getTS that starts a
  phase burns its "first invalidation" credit (it never makes an `I₃` write), which is what makes
  the paper's bound `⌈2√M⌉` come out (the paper's own count `Σ_{ϕ ≤ Φ} ϕ ≤ 2M` silently treats
  the last, possibly incomplete phase as complete).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp.Alg4

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

/-- A process whose current operation will not write any more (or that is idle). -/
def Dead (R : Mem P) : PC P → Prop
  | .idle => True
  | .done _ => True
  | .loop k _ _ .s6 => R (k + 1) ≠ none
  | .scan k => R (k + 1) ≠ none
  | _ => False

lemma Dead.mono {R R' : Mem P} {pc : PC P} (h : Dead R pc) (hm : ∀ j, R j ≠ none → R' j ≠ none) :
    Dead R' pc := by
  unfold Dead at h ⊢
  cases pc with
  | loop k i v s => cases s <;> first | exact hm _ h | exact h
  | scan k => exact hm _ h
  | _ => exact h

/-- Per-process phase facts (Claims 6.7, 6.11 and the facts behind 6.13). -/
def PhOK (R : Mem P) (G : Gh P) (p : P) (l : Loc P) : Prop :=
  match l.pc with
  | .wh _ _ => ((p, l.cnt), false) ∈ G.cr
  | .loop k i _ s => (((p, l.cnt), false) ∉ G.cr → k + 1 ≤ G.ph) ∧
      (G.ph = k → (∀ j, 1 ≤ j → j < i → j ∈ G.wc ∧ (k ≤ rndOf (R j) ∨ G.free j = true)) ∧
        ((s = .s10 ∨ s = .s11) → i ∈ G.wc)) ∧
      (s = .s11 → ((p, l.cnt), false) ∉ G.cr → R (k + 1) = none → i ∈ G.wc ∨ rndOf (R i) < k)
  | .scan k => (((p, l.cnt), false) ∉ G.cr → k + 1 ≤ G.ph) ∧
      (G.ph = k → ∀ j, 1 ≤ j → j < k → j ∈ G.wc ∧ (k ≤ rndOf (R j) ∨ G.free j = true))
  | _ => True

/-- The writer of a `free` register: its last write, credit still available. -/
def FreeW (R : Mem P) (loc : P → Loc P) (G : Gh P) (j : ℕ) : Prop :=
  ∃ q c, lastId (R j) = some (q, c) ∧ ((q, c), true) ∈ G.cr ∧
    (c < (loc q).cnt ∨ (c = (loc q).cnt ∧ Dead R (loc q).pc))

/-- The phase / charging invariant. -/
structure Inv3 (C : ACfg P) (G : Gh P) : Prop where
  wc_iff : ∀ j, j ∈ G.wc ↔ G.pst < G.wt j
  count : (G.ph - 1) * G.ph + 2 * G.wc.card ≤ 2 * G.ninv
  credit : G.ninv + G.ph + G.cr.card ≤ 2 * G.nget
  crT : ∀ p, (((p, (C.loc p).cnt), true) ∉ G.cr) → Dead (Rg C) (C.loc p).pc
  free : ∀ j, G.free j = true → FreeW (Rg C) C.loc G j
  freeU : ∀ j j', G.free j = true → G.free j' = true → lastId (Rg C j) = lastId (Rg C j') →
    j = j'
  ph : ∀ p, PhOK (Rg C) G p (C.loc p)
  invis : 1 ≤ G.ph → Rg C G.ph = none → ∀ j, 1 ≤ j → j + 2 ≤ G.ph →
    j ∈ G.wc ∨ G.ph - 1 ≤ rndOf (Rg C j) ∨ G.free j = true

lemma inv3_init : Inv3 (alg4 (P := P)).initCfg Gh.init := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Impl.initCfg, alg4, Gh.init, PhOK, Dead]

lemma PhOK.transfer {R : Mem P} {G G' : Gh P} {p : P} {l : Loc P} (h : PhOK R G p l)
    (hcr : G.cr ⊆ G'.cr) (hph : G'.ph = G.ph) (hwc : G'.wc = G.wc) (hfree : G'.free = G.free) :
    PhOK R G' p l := by
  unfold PhOK at h ⊢
  rw [hph, hwc, hfree]
  rcases l with ⟨c, pc⟩
  cases pc with
  | wh j v => exact hcr h
  | loop k i v s =>
    exact ⟨fun h1 => h.1 (fun h2 => h1 (hcr h2)), h.2.1,
      fun h1 h2 => h.2.2 h1 (fun h3 => h2 (hcr h3))⟩
  | scan k => exact ⟨fun h1 => h.1 (fun h2 => h1 (hcr h2)), h.2⟩
  | _ => trivial

/-- Preservation by steps that write nothing and only add credits. -/
lemma Inv3.nowrite_step {C C' : ACfg P} {G G' : Gh P} {q : P} (hI : Inv3 C G)
    (hR : Rg C' = Rg C) (hloc : ∀ p, p ≠ q → C'.loc p = C.loc p)
    (hwt : G'.wt = G.wt) (hpst : G'.pst = G.pst) (hwc : G'.wc = G.wc) (hph : G'.ph = G.ph)
    (hninv : G'.ninv = G.ninv) (hfree : G'.free = G.free) (hcr : G.cr ⊆ G'.cr)
    (hcred : G'.ninv + G'.ph + G'.cr.card ≤ 2 * G'.nget)
    (hcrq : ((q, (C'.loc q).cnt), true) ∉ G'.cr → Dead (Rg C) (C'.loc q).pc)
    (hfr : ∀ j, G.free j = true → ∀ c, lastId (Rg C j) = some (q, c) →
      (c < (C.loc q).cnt ∨ (c = (C.loc q).cnt ∧ Dead (Rg C) (C.loc q).pc)) →
      (c < (C'.loc q).cnt ∨ (c = (C'.loc q).cnt ∧ Dead (Rg C) (C'.loc q).pc)))
    (hphq : PhOK (Rg C) G' q (C'.loc q)) : Inv3 C' G' := by
  refine ⟨?_, ?_, hcred, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hwc, hpst, hwt]; exact hI.wc_iff
  · rw [hph, hwc, hninv]; exact hI.count
  · intro p hp
    rw [hR]
    by_cases hpq : p = q
    · subst hpq; exact hcrq hp
    · rw [hloc p hpq] at hp ⊢; exact hI.crT p (fun h => hp (hcr h))
  · intro j hj
    rw [hfree] at hj
    obtain ⟨q', c, h1, h2, h3⟩ := hI.free j hj
    refine ⟨q', c, by rw [hR]; exact h1, hcr h2, ?_⟩
    rw [hR]
    by_cases hq : q' = q
    · subst hq; exact hfr j hj c h1 h3
    · rw [hloc q' hq]; exact h3
  · rw [hfree, hR]; exact hI.freeU
  · intro p
    rw [hR]
    by_cases hpq : p = q
    · subst hpq; exact hphq
    · rw [hloc p hpq]; exact (hI.ph p).transfer hcr hph hwc hfree
  · rw [hph, hwc, hfree, hR]; exact hI.invis

/-! ### Credits after a write -/

section CrAfter

variable {cr : Finset ((P × ℕ) × Bool)} {old : Option (Val P)} {id : P × ℕ} {inval dead : Bool}

lemma crAfter_sub : crAfter cr old id inval dead ⊆ cr := by
  unfold crAfter
  split_ifs
  · exact Finset.erase_subset _ _
  · exact Finset.erase_subset _ _
  · split
    · exact Finset.erase_subset _ _
    · exact subset_rfl
  · exact subset_rfl

lemma crAfter_removed {y : (P × ℕ) × Bool} (hy : y ∈ cr)
    (hn : y ∉ crAfter cr old id inval dead) :
    inval = true ∧ ((dead = true ∧ y = (id, true)) ∨ (dead = false ∧ y = (id, false)) ∨
      (dead = false ∧ (id, false) ∉ cr ∧ ∃ x, lastId old = some x ∧ y = (x, true))) := by
  unfold crAfter at hn
  split_ifs at hn with h1 h2 h3
  · refine ⟨h1, Or.inl ⟨h2, ?_⟩⟩
    by_contra h; exact hn (Finset.mem_erase.2 ⟨h, hy⟩)
  · refine ⟨h1, Or.inr (Or.inl ⟨by simpa using h2, ?_⟩)⟩
    by_contra h; exact hn (Finset.mem_erase.2 ⟨h, hy⟩)
  · split at hn
    · rename_i x hx
      refine ⟨h1, Or.inr (Or.inr ⟨by simpa using h2, h3, x, hx, ?_⟩)⟩
      by_contra h; exact hn (Finset.mem_erase.2 ⟨h, hy⟩)
    · exact absurd hy hn
  · exact absurd hy hn

lemma crAfter_card (hi : inval = true) (hd : dead = true → (id, true) ∈ cr)
    (hnd : dead = false → (id, false) ∉ cr → ∃ x, lastId old = some x ∧ (x, true) ∈ cr) :
    (crAfter cr old id inval dead).card + 1 = cr.card := by
  unfold crAfter
  simp only [hi, ite_true]
  split_ifs with h2 h3
  · exact Finset.card_erase_add_one (hd h2)
  · exact Finset.card_erase_add_one h3
  · obtain ⟨x, hx, hxc⟩ := hnd (by simpa using h2) h3
    rw [hx]; exact Finset.card_erase_add_one hxc

lemma crAfter_of_not (hi : inval = false) : crAfter cr old id inval dead = cr := by
  simp [crAfter, hi]

end CrAfter

@[simp] lemma gwrite_wc {G : Gh P} {R : Mem P} {id : P × ℕ} {j : ℕ} {dead : Bool}
    {sc : Option ℕ} : (gwrite G R id j dead sc).wc = insert j G.wc := rfl

@[simp] lemma gwrite_free {G : Gh P} {R : Mem P} {id : P × ℕ} {j : ℕ} {dead : Bool}
    {sc : Option ℕ} :
    (gwrite G R id j dead sc).free = Function.update G.free j (!decide (j ∉ G.wc) && dead) := rfl

@[simp] lemma gwrite_cr {G : Gh P} {R : Mem P} {id : P × ℕ} {j : ℕ} {dead : Bool}
    {sc : Option ℕ} :
    (gwrite G R id j dead sc).cr = crAfter G.cr (R j) id (decide (j ∉ G.wc)) dead := rfl

@[simp] lemma gwrite_ninv {G : Gh P} {R : Mem P} {id : P × ℕ} {j : ℕ} {dead : Bool}
    {sc : Option ℕ} :
    (gwrite G R id j dead sc).ninv = if j ∉ G.wc then G.ninv + 1 else G.ninv := by
  simp [gwrite]

lemma crAfter_false_iff {cr : Finset ((P × ℕ) × Bool)} {old : Option (Val P)} {id x : P × ℕ}
    {inval dead : Bool} (hx : x ≠ id) :
    (x, false) ∈ crAfter cr old id inval dead ↔ (x, false) ∈ cr := by
  constructor
  · intro h; exact crAfter_sub h
  · intro h; by_contra h3
    obtain ⟨-, h4⟩ := crAfter_removed h h3
    rcases h4 with ⟨-, h5⟩ | ⟨-, h5⟩ | ⟨-, -, y, -, h5⟩
    · simp at h5
    · simp only [Prod.mk.injEq] at h5; exact hx h5.1
    · simp at h5

/-- Phase facts of a process not taking the step survive a write by another process. -/
lemma PhOK.write {R : Mem P} {G : Gh P} {p q : P} {l : Loc P} {j c : ℕ} {v : Val P}
    {dead : Bool} {sc : Option ℕ} (h : PhOK R G p l) (h1 : PI1 R p l)
    (hpq : p ≠ q) (hdrnd : ∀ k', R k' ≠ none → v.rnd < k' → dead = true) :
    PhOK (Function.update R j (some v)) (gwrite G R (q, c) j dead sc) p l := by
  have hcrF : ((p, l.cnt), false) ∈ (gwrite G R (q, c) j dead sc).cr ↔
      ((p, l.cnt), false) ∈ G.cr := by
    rw [gwrite_cr]; exact crAfter_false_iff (by simp [hpq])
  have key : ∀ k j', R k ≠ none → j' ∈ G.wc → (k ≤ rndOf (R j') ∨ G.free j' = true) →
      (k ≤ rndOf (Function.update R j (some v) j') ∨
        Function.update G.free j (!decide (j ∉ G.wc) && dead) j' = true) := by
    intro k j' hk h7 h8
    by_cases hj : j' = j
    · subst hj
      rw [Function.update_self, Function.update_self]
      simp only [rndOf, h7, not_true_eq_false, decide_false, Bool.not_false, Bool.true_and]
      by_cases hr : k ≤ v.rnd
      · left; exact hr
      · right; exact hdrnd k hk (by omega)
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]; exact h8
  unfold PhOK at h ⊢
  unfold PI1 at h1
  rcases l with ⟨c', pc⟩
  cases pc with
  | wh j' v' => exact hcrF.2 h
  | loop k i v' s =>
    simp only [gwrite_ph, gwrite_wc, gwrite_free] at hcrF ⊢
    obtain ⟨hA, hB, hC⟩ := h
    refine ⟨fun h2 => hA (fun h3 => h2 (hcrF.2 h3)), fun h2 => ?_, fun h2 h3 h4 => ?_⟩
    · obtain ⟨hB1, hB2⟩ := hB h2
      refine ⟨fun j' h5 h6 => ?_, fun h5 => Finset.mem_insert_of_mem (hB2 h5)⟩
      obtain ⟨h7, h8⟩ := hB1 j' h5 h6
      exact ⟨Finset.mem_insert_of_mem h7, key k j' h1.2.2 h7 h8⟩
    · have h5 : R (k + 1) = none := (upd_eq_none h4).1
      rcases hC h2 (fun h6 => h3 (hcrF.2 h6)) h5 with h6 | h6
      · left; exact Finset.mem_insert_of_mem h6
      · by_cases hij : i = j
        · left; rw [hij]; exact Finset.mem_insert_self _ _
        · right; rw [Function.update_of_ne hij]; exact h6
  | scan k =>
    simp only [gwrite_ph, gwrite_wc, gwrite_free] at hcrF ⊢
    obtain ⟨hA, hB⟩ := h
    refine ⟨fun h2 => hA (fun h3 => h2 (hcrF.2 h3)), fun h2 j' h5 h6 => ?_⟩
    obtain ⟨h7, h8⟩ := hB h2 j' h5 h6
    exact ⟨Finset.mem_insert_of_mem h7, key k j' (h1 (by omega)) h7 h8⟩
  | _ => trivial

/-- Preservation of the phase / charging invariant by a write of `q` to `R[j]`. -/
lemma Inv3.write_step {α : List (Label P TS)} {C C' : ACfg P} {G : Gh P} {q : P} {c j : ℕ}
    {pc' : PC P} {v : Val P} {dead : Bool} {sc : Option ℕ}
    (hI : Inv3 C G) (h1 : Inv1 α C) (h2 : Inv2 C G) (hcq : (C.loc q).cnt = c)
    (hR : Rg C' = Function.update (Rg C) j (some v))
    (hloc : C'.loc = Function.update C.loc q ⟨c, pc'⟩)
    (hnd : ¬ Dead (Rg C) (C.loc q).pc) (hvid : lastId (some v) = some (q, c))
    (hdead : dead = true → Dead (Rg C') pc')
    (hdrnd : ∀ k', Rg C k' ≠ none → v.rnd < k' → dead = true)
    (hI4 : j ∉ G.wc → dead = false → ((q, c), false) ∉ G.cr → G.free j = true)
    (hphq : PhOK (Rg C') (gwrite G (Rg C) (q, c) j dead sc) q ⟨c, pc'⟩) :
    Inv3 C' (gwrite G (Rg C) (q, c) j dead sc) := by
  set G' := gwrite G (Rg C) (q, c) j dead sc with hG'
  have hm : ∀ i, Rg C i ≠ none → Rg C' i ≠ none := fun i h => by rw [hR]; exact upd_ne_none h
  have hcrq : ((q, c), true) ∈ G.cr := by
    by_contra h; exact hnd (hI.crT q (by rw [hcq]; exact h))
  have hlocq : C'.loc q = ⟨c, pc'⟩ := by rw [hloc, Function.update_self]
  have hloco : ∀ p, p ≠ q → C'.loc p = C.loc p := fun p hp => by
    rw [hloc, Function.update_of_ne hp]
  -- a free register is never written last by `q`'s current operation
  have hfree_ne : ∀ i, G.free i = true → lastId (Rg C i) ≠ some (q, c) := by
    intro i hi h
    obtain ⟨q', c', h3, -, h5⟩ := hI.free i hi
    rw [h] at h3; simp only [Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    rcases h5 with h5 | ⟨-, h5⟩
    · omega
    · exact hnd h5
  -- the I₄ case: the overwritten value is free
  have hI4' : j ∉ G.wc → dead = false → ((q, c), false) ∉ G.cr →
      ∃ x, lastId (Rg C j) = some x ∧ (x, true) ∈ G.cr ∧ x ≠ (q, c) := by
    intro h3 h4 h5
    have hf := hI4 h3 h4 h5
    obtain ⟨q', c', h6, h7, -⟩ := hI.free j hf
    exact ⟨(q', c'), h6, h7, fun h8 => hfree_ne j hf (h6.trans (by rw [h8]))⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- wc_iff
    intro i
    simp only [hG', gwrite_wc, gwrite_pst, Finset.mem_insert, gwrite_wt]
    have := h2.pst_le
    by_cases hij : i = j
    · subst hij; simp; omega
    · simp only [hij, false_or, ↓reduceIte]; exact hI.wc_iff i
  · -- count
    simp only [hG', gwrite_ph, gwrite_wc, gwrite_ninv]
    have := hI.count
    by_cases hj : j ∈ G.wc
    · simp only [hj, Finset.insert_eq_of_mem, not_true_eq_false, ↓reduceIte]; exact this
    · simp only [hj, not_false_eq_true, ↓reduceIte, Finset.card_insert_of_notMem]; omega
  · -- credit
    simp only [hG', gwrite_ph, gwrite_ninv, gwrite_cr, gwrite_nget]
    have := hI.credit
    by_cases hj : j ∈ G.wc
    · simp only [hj, not_true_eq_false, ↓reduceIte, decide_false]
      rw [crAfter_of_not rfl]; exact this
    · simp only [hj, not_false_eq_true, ↓reduceIte, decide_true]
      have hc := crAfter_card (cr := G.cr) (old := Rg C j) (id := (q, c)) (dead := dead) rfl
        (fun _ => hcrq) (fun h4 h5 => by
          obtain ⟨x, h6, h7, -⟩ := hI4' hj h4 h5; exact ⟨x, h6, h7⟩)
      omega
  · -- crT
    intro p hp
    by_cases hpq : p = q
    · rw [hpq] at hp ⊢
      rw [hlocq] at hp ⊢
      cases hd : dead
      · exfalso; apply hp
        simp only [hG', gwrite_cr]
        by_contra h3
        obtain ⟨-, h4⟩ := crAfter_removed hcrq h3
        rcases h4 with ⟨h5, -⟩ | ⟨-, h5⟩ | ⟨-, h5, x, h6, h7⟩
        · rw [hd] at h5; exact Bool.false_ne_true h5
        · simp at h5
        · simp only [Prod.mk.injEq, and_true] at h7
          rw [← h7] at h6
          have hj : j ∉ G.wc := by
            by_contra hj
            have := crAfter_of_not (cr := G.cr) (old := Rg C j) (id := (q, c)) (dead := dead)
              (inval := decide (j ∉ G.wc)) (by simp [hj])
            rw [this] at h3; exact h3 hcrq
          obtain ⟨y, hy, -, hy'⟩ := hI4' hj hd h5
          rw [h6] at hy; simp only [Option.some.injEq] at hy; exact hy' hy.symm
      · exact hdead hd
    · rw [hloco p hpq] at hp ⊢
      by_cases hp' : ((p, (C.loc p).cnt), true) ∈ G.cr
      · obtain ⟨-, h4⟩ := crAfter_removed hp' hp
        rcases h4 with ⟨-, h5⟩ | ⟨-, h5⟩ | ⟨hd5, hcf, x, h6, h7⟩
        · simp only [Prod.mk.injEq] at h5; exact absurd h5.1.1 hpq
        · simp at h5
        · simp only [Prod.mk.injEq, and_true] at h7
          have hj : j ∉ G.wc := by
            by_contra hj
            have := crAfter_of_not (cr := G.cr) (old := Rg C j) (id := (q, c)) (dead := dead)
              (inval := decide (j ∉ G.wc)) (by simp [hj])
            simp only [hG', gwrite_cr] at hp; rw [this] at hp; exact hp hp'
          have hf := hI4 hj hd5 hcf
          obtain ⟨q', c', h8, -, h9⟩ := hI.free j hf
          rw [h6, ← h7] at h8
          simp only [Option.some.injEq, Prod.mk.injEq] at h8
          obtain ⟨rfl, h10⟩ := h8
          rw [← h10] at h9
          rcases h9 with h9 | ⟨-, h9⟩
          · omega
          · exact h9.mono hm
      · exact (hI.crT p hp').mono hm
  · -- free
    intro i hi
    simp only [hG', gwrite_free] at hi
    by_cases hij : i = j
    · rw [hij, Function.update_self] at hi
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_not] at hi
      obtain ⟨hj, hd⟩ := hi
      refine ⟨q, c, ?_, ?_, ?_⟩
      · rw [hR, hij, Function.update_self]; exact hvid
      · simp only [hG', gwrite_cr]; rw [crAfter_of_not (by simp [hj])]; exact hcrq
      · right; rw [hlocq]; exact ⟨rfl, hdead hd⟩
    · rw [Function.update_of_ne hij] at hi
      obtain ⟨q', c', h3, h4, h5⟩ := hI.free i hi
      have hne : (q', c') ≠ (q, c) := fun h => hfree_ne i hi (by rw [h3, h])
      refine ⟨q', c', by rw [hR, Function.update_of_ne hij]; exact h3, ?_, ?_⟩
      · simp only [hG', gwrite_cr]
        by_contra h6
        obtain ⟨hinv, h7⟩ := crAfter_removed h4 h6
        rcases h7 with ⟨-, h8⟩ | ⟨-, h8⟩ | ⟨hd5, hcf, x, h9, h10⟩
        · simp only [Prod.mk.injEq, and_true] at h8; exact hne (by rw [h8.1, h8.2])
        · simp at h8
        · simp only [Prod.mk.injEq, and_true] at h10
          have hj : j ∉ G.wc := by simpa using hinv
          have hf := hI4 hj hd5 hcf
          exact hij (hI.freeU i j hi hf (by rw [h3, h9, h10]))
      · by_cases hq' : q' = q
        · rw [hq'] at h5 ⊢; rw [hlocq]
          rcases h5 with h5 | ⟨h5, -⟩
          · left; simp only; omega
          · exfalso; apply hne; rw [hq', h5, hcq]
        · rw [hloco q' hq']
          rcases h5 with h5 | ⟨h5, h6⟩
          · left; exact h5
          · right; exact ⟨h5, h6.mono hm⟩
  · -- freeU
    intro i i' hi hi' heq
    simp only [hG', gwrite_free] at hi hi'
    rw [hR] at heq
    by_cases hij : i = j <;> by_cases hi'j : i' = j
    · rw [hij, hi'j]
    · exfalso
      rw [Function.update_of_ne hi'j] at hi'
      rw [hij, Function.update_self, Function.update_of_ne hi'j, hvid] at heq
      exact hfree_ne i' hi' heq.symm
    · exfalso
      rw [Function.update_of_ne hij] at hi
      rw [hi'j, Function.update_self, Function.update_of_ne hij, hvid] at heq
      exact hfree_ne i hi heq
    · rw [Function.update_of_ne hij] at hi
      rw [Function.update_of_ne hi'j] at hi'
      rw [Function.update_of_ne hij, Function.update_of_ne hi'j] at heq
      exact hI.freeU i i' hi hi' heq
  · -- ph
    intro p
    by_cases hpq : p = q
    · rw [hpq, hlocq, hR]; rw [hR] at hphq; exact hphq
    · rw [hloco p hpq, hR]; exact (hI.ph p).write (h1.pi p) hpq hdrnd
  · -- invis
    intro h3 h4 i h5 h6
    simp only [hG', gwrite_ph, gwrite_wc, gwrite_free] at h3 h4 h6 ⊢
    rw [hR] at h4 ⊢
    obtain ⟨h7, -⟩ := upd_eq_none h4
    by_cases hij : i = j
    · left; rw [hij]; exact Finset.mem_insert_self _ _
    · rw [Function.update_of_ne hij, Function.update_of_ne hij]
      rcases hI.invis h3 h7 i h5 h6 with h9 | h9 | h9
      · left; exact Finset.mem_insert_of_mem h9
      · right; left; exact h9
      · right; right; exact h9

lemma TauEff.dead {q : P} {c : ℕ} {R R' : Mem P} {pc pc' : PC P}
    (h : TauEff q c R pc pc' R') (hd : Dead R pc) : Dead R' pc' := by
  cases h with
  | s6N hx => exact absurd hx hd
  | scN hx => exact absurd hx hd
  | s6S _ => trivial
  | scS _ => trivial
  | _ => exact hd.elim

lemma tri_step (k : ℕ) : (k + 1 - 1) * (k + 1) = (k - 1) * k + 2 * k := by
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel]; ring

/-- The scan that starts phase `k + 1`. -/
lemma Inv3.phase_step {α : List (Label P TS)} {C C' : ACfg P} {G : Gh P} {q : P} {c k : ℕ}
    {w : Val P} (hI : Inv3 C G) (h1 : Inv1 α C) (h2 : Inv2 C G)
    (hl : C.loc q = ⟨c, .scan k⟩) (hphk : G.ph = k) (hx : Rg C (k + 1) = none)
    (hR : Rg C' = Rg C) (hloc : C'.loc = Function.update C.loc q ⟨c, .fin k w⟩) :
    Inv3 C'
      { G with
        t := G.t + 1
        psc := Function.update G.psc q (G.t + 1)
        ph := k + 1
        pst := G.t + 1
        wc := ∅
        cr := G.cr.erase ((q, c), false) } := by
  have hpi1 := h1.pi q
  rw [hl] at hpi1; simp only [PI1] at hpi1
  have hphq := hI.ph q
  rw [hl] at hphq; simp only [PhOK] at hphq
  obtain ⟨hA, hB⟩ := hphq
  have hcrf : ((q, c), false) ∈ G.cr := by
    by_contra h; have := hA h; omega
  have hcrt : ((q, c), true) ∈ G.cr := by
    by_contra h
    have := hI.crT q (by rw [hl]; exact h)
    rw [hl] at this; exact this hx
  have hloco : ∀ p, p ≠ q → C'.loc p = C.loc p := fun p hp => by
    rw [hloc, Function.update_of_ne hp]
  have hlocq : C'.loc q = ⟨c, .fin k w⟩ := by rw [hloc, Function.update_self]
  have hmem : ∀ y : (P × ℕ) × Bool, y ≠ ((q, c), false) → (y ∈ G.cr.erase ((q, c), false) ↔ y ∈ G.cr) :=
    fun y hy => by simp [Finset.mem_erase, hy]
  have hwl := h2.wt_le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; simp only [Finset.notMem_empty, false_iff, not_lt]; exact (hwl j).trans (by omega)
  · -- every register `R[1..k]` was written in phase `k`
    have hsub : Finset.Icc 1 k ⊆ G.wc := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      rcases Nat.lt_or_ge j k with h3 | h3
      · exact (hB hphk j hj.1 h3).1
      · have hjk : j = k := by omega
        subst hjk
        have := h2.wph (by rw [hphk]; exact hpi1 hj.1)
        rw [hphk] at this
        exact (hI.wc_iff j).2 this
    have hcard := Finset.card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hcard
    have := hI.count
    rw [hphk] at this
    simp only [Finset.card_empty, mul_zero, add_zero]
    rw [tri_step]; omega
  · have := hI.credit
    have h3 := Finset.card_erase_add_one hcrf
    simp only; omega
  · intro p hp
    rw [hR]
    by_cases hpq : p = q
    · rw [hpq, hlocq] at hp ⊢
      exact absurd ((hmem _ (by simp)).2 hcrt) hp
    · rw [hloco p hpq] at hp ⊢
      exact hI.crT p (fun h => hp ((hmem _ (by simp [hpq])).2 h))
  · intro j hj
    obtain ⟨q', c', h3, h4, h5⟩ := hI.free j hj
    refine ⟨q', c', by rw [hR]; exact h3, (hmem _ (by simp)).2 h4, ?_⟩
    rw [hR]
    by_cases hq' : q' = q
    · rw [hq'] at h5 ⊢; rw [hlocq]
      rw [hl] at h5
      rcases h5 with h5 | ⟨-, h5⟩
      · left; exact h5
      · exact absurd hx h5
    · rw [hloco q' hq']; exact h5
  · rw [hR]; exact hI.freeU
  · intro p
    rw [hR]
    by_cases hpq : p = q
    · rw [hpq, hlocq]; trivial
    · rw [hloco p hpq]
      have hp1 := h1.pi p
      have hp3 := hI.ph p
      generalize C.loc p = l at hp1 hp3 ⊢
      obtain ⟨c', pc⟩ := l
      unfold PhOK at hp3 ⊢
      unfold PI1 at hp1
      have hmp : ∀ b, (((p, c'), b) ∈ G.cr.erase ((q, c), false) ↔ ((p, c'), b) ∈ G.cr) :=
        fun b => hmem _ (by simp [hpq])
      cases pc with
      | wh j v => exact (hmp false).2 hp3
      | loop k' i v s =>
        simp only at hp1 hp3 ⊢
        obtain ⟨hA', -, hC'⟩ := hp3
        refine ⟨fun h3 => ?_, fun h3 => ?_, fun h3 h4 h5 => ?_⟩
        · have := hA' (fun h4 => h3 ((hmp false).2 h4)); omega
        · subst h3; exact absurd hp1.2.2 (by simpa using hx)
        · exfalso
          have h6 := hA' (fun h7 => h4 ((hmp false).2 h7))
          exact h1.mem.contig k (k' + 1) (hpi1 (by omega)) (by omega) (by omega) h5
      | scan k' =>
        simp only at hp1 hp3 ⊢
        refine ⟨fun h3 => ?_, fun h3 => ?_⟩
        · have := hp3.1 (fun h4 => h3 ((hmp false).2 h4)); omega
        · subst h3; exact absurd (hp1 (by omega)) (by simpa using hx)
      | _ => trivial
  · intro _ _ j h3 h4
    simp only at h4
    rw [hR]
    simp only [Finset.notMem_empty, false_or, Nat.add_sub_cancel]
    exact (hB hphk j h3 (by omega)).2


/-- A reading step of `q` (no write, no new phase). -/
lemma Inv3.read_tau {C C' : ACfg P} {G G' : Gh P} {q : P} {c : ℕ} {pc pc' : PC P}
    (hI : Inv3 C G) (hl : C.loc q = ⟨c, pc⟩)
    (hloc : C'.loc = Function.update C.loc q ⟨c, pc'⟩) (hR : Rg C' = Rg C)
    (hdd : Dead (Rg C) pc → Dead (Rg C) pc')
    (hwt : G'.wt = G.wt) (hpst : G'.pst = G.pst) (hwc : G'.wc = G.wc) (hph : G'.ph = G.ph)
    (hninv : G'.ninv = G.ninv) (hfree : G'.free = G.free) (hcr : G'.cr = G.cr)
    (hnget : G'.nget = G.nget) (hphq : PhOK (Rg C) G' q ⟨c, pc'⟩) : Inv3 C' G' := by
  have hloco : ∀ p, p ≠ q → C'.loc p = C.loc p := fun p hp => by
    rw [hloc, Function.update_of_ne hp]
  have hlocq : C'.loc q = ⟨c, pc'⟩ := by rw [hloc, Function.update_self]
  refine hI.nowrite_step hR hloco hwt hpst hwc hph hninv hfree (by rw [hcr]) ?_ ?_ ?_ ?_
  · rw [hninv, hph, hcr, hnget]; exact hI.credit
  · rw [hlocq, hcr]; intro h
    have := hI.crT q
    rw [hl] at this; exact hdd (this h)
  · intro j _ c' _ h4
    rw [hlocq]; rw [hl] at h4
    rcases h4 with h4 | ⟨h4, h5⟩
    · left; exact h4
    · right; exact ⟨h4, hdd h5⟩
  · rw [hlocq]; exact hphq

/-- **Preservation of the phase / charging invariant.** -/
theorem Inv3.step {α : List (Label P TS)} {C C' : ACfg P} {G : Gh P} {ℓ : Label P TS}
    (hI : Inv3 C G) (h1 : Inv1 α C) (h2 : Inv2 C G)
    (hs : (alg4 (P := P)).step C ℓ = some C') : Inv3 C' (gstep G C ℓ) := by
  cases ℓ with
  | inv q o =>
    obtain ⟨h0, -, hloc, hmem⟩ := step_inv' hs
    have hidle := (h1.idle q).1 h0
    have hR : Rg C' = Rg C := by simp [Rg, hmem]
    have hloco : ∀ p, p ≠ q → C'.loc p = C.loc p := fun p hp => by
      rw [hloc, Function.update_of_ne hp]
    have hfr : ∀ j, G.free j = true → ∀ c, lastId (Rg C j) = some (q, c) →
        (c < (C.loc q).cnt ∨ (c = (C.loc q).cnt ∧ Dead (Rg C) (C.loc q).pc)) →
        (c < (C'.loc q).cnt ∨ (c = (C'.loc q).cnt ∧ Dead (Rg C) (C'.loc q).pc)) := by
      intro j _ c h3 _
      rcases h2.ids j q c h3 with h4 | ⟨-, h4⟩
      · left; rw [hloc, Function.update_self]; cases o <;> exact h4
      · rw [hidle] at h4; exact h4.elim
    cases o with
    | getTS =>
      refine hI.nowrite_step hR hloco rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ hfr ?_
      · intro x hx; simp [gstep, hx]
      · have := hI.credit
        have h3 := Finset.card_insert_le ((q, (C.loc q).cnt), true)
          (insert ((q, (C.loc q).cnt), false) G.cr)
        have h4 := Finset.card_insert_le ((q, (C.loc q).cnt), false) G.cr
        dsimp only [gstep]; omega
      · rw [hloc, Function.update_self]; simp [gstep, alg4]
      · rw [hloc, Function.update_self]; simp [gstep, alg4, PhOK]
    | compare a b =>
      refine hI.nowrite_step hR hloco rfl rfl rfl rfl rfl rfl (subset_refl _) ?_ ?_ hfr ?_
      · have := hI.credit; dsimp only [gstep]; omega
      · rw [hloc, Function.update_self]; simp [alg4, Dead]
      · rw [hloc, Function.update_self]; simp [alg4, PhOK]
  | ret q r =>
    obtain ⟨h0, -, hmem, h3⟩ := step_ret' hs
    rcases h3 with ⟨hpc, hloc⟩ | hpc
    swap
    · exact absurd ((h1.idle q).2 hpc) h0
    have hR : Rg C' = Rg C := by simp [Rg, hmem]
    have hloco : ∀ p, p ≠ q → C'.loc p = C.loc p := fun p hp => by
      rw [hloc, Function.update_of_ne hp]
    refine hI.nowrite_step hR hloco rfl rfl rfl rfl rfl rfl (subset_refl _) ?_ ?_ ?_ ?_
    · exact hI.credit
    · rw [hloc, Function.update_self]; simp [Dead]
    · intro j _ c _ h4
      left; rw [hloc, Function.update_self]
      rcases h4 with h4 | ⟨h4, -⟩ <;> simp <;> omega
    · rw [hloc, Function.update_self]; simp [PhOK]
  | tau q =>
    obtain ⟨pc', h0, -, hloc, hT⟩ := tau_step hs
    have hpi1 := h1.pi q
    have hpi2 := h2.pi q
    have hph3 := hI.ph q
    have hcrT := hI.crT q
    have hfreeq : ∀ j, G.free j = true → FreeW (Rg C) C.loc G j := hI.free
    generalize hl : C.loc q = l at hloc hT hpi1 hpi2 hph3 hcrT
    obtain ⟨c, pc⟩ := l
    generalize hR' : Rg C' = R' at hT
    simp only at hT hloc hcrT
    have hloco : ∀ p, p ≠ q → C'.loc p = C.loc p := fun p hp => by
      rw [hloc, Function.update_of_ne hp]
    have hlocq : C'.loc q = ⟨c, pc'⟩ := by rw [hloc, Function.update_self]
    have hdd := hT.dead
    cases hT with
    | @whS j v x hx =>
      have hg : gstep G C (.tau q) =
          { G with t := G.t + 1, psc := Function.update G.psc q (G.rsc j) } := by
        simp [gstep, hl, hx]
      rw [hg]
      refine hI.read_tau hl hloc hR' hdd rfl rfl rfl rfl rfl rfl rfl rfl ?_
      simp only [PhOK] at hph3 ⊢; exact hph3
    | @whN j v hx =>
      have hg : gstep G C (.tau q) = { G with t := G.t + 1 } := by simp [gstep, hl, hx]
      rw [hg]
      refine hI.read_tau hl hloc hR' hdd rfl rfl rfl rfl rfl rfl rfl rfl ?_
      simp only [PhOK] at hph3
      simp only [PI1] at hpi1
      unfold endWh; split_ifs with h3
      · simp only [PhOK]
        refine ⟨fun h => absurd hph3 h, fun _ => ⟨fun j' h4 h5 => by omega, by simp⟩, by simp⟩
      · simp only [PhOK]
        exact ⟨fun h => absurd hph3 h, fun _ j' h4 h5 => by omega⟩
    | @s6N k i v hx =>
      have hg : gstep G C (.tau q) = { G with t := G.t + 1 } := by simp [gstep, hl]
      rw [hg]
      refine hI.read_tau hl hloc hR' hdd rfl rfl rfl rfl rfl rfl rfl rfl ?_
      simp only [PhOK] at hph3 ⊢
      exact ⟨hph3.1, fun h => ⟨(hph3.2.1 h).1, by simp⟩, by simp⟩
    | @s6S k i v x hx =>
      have hg : gstep G C (.tau q) = { G with t := G.t + 1 } := by simp [gstep, hl]
      rw [hg]
      exact hI.read_tau hl hloc hR' hdd rfl rfl rfl rfl rfl rfl rfl rfl trivial
    | @s7T k i v hx =>
      have hg : gstep G C (.tau q) = { G with t := G.t + 1 } := by simp [gstep, hl]
      rw [hg]
      refine hI.read_tau hl hloc hR' hdd rfl rfl rfl rfl rfl rfl rfl rfl ?_
      simp only [PhOK] at hph3 ⊢
      exact ⟨hph3.1, fun h => ⟨(hph3.2.1 h).1, by simp⟩, by simp⟩
    | @s7F k i v hx =>
      have hg : gstep G C (.tau q) = { G with t := G.t + 1 } := by simp [gstep, hl]
      rw [hg]
      refine hI.read_tau hl hloc hR' hdd rfl rfl rfl rfl rfl rfl rfl rfl ?_
      simp only [PhOK] at hph3 ⊢
      simp only [PI1] at hpi1
      simp only [PI2] at hpi2
      refine ⟨hph3.1, fun h => ⟨(hph3.2.1 h).1, fun _ => ?_⟩, by simp⟩
      rw [hI.wc_iff]
      by_contra h5
      exact hx (hpi2.1.eq i hpi1.1 (by omega) ((not_lt.1 h5).trans (hpi2.1.pst h)))
    | @s10T k i v hx =>
      have hg : gstep G C (.tau q) = { G with t := G.t + 1 } := by simp [gstep, hl]
      rw [hg]
      refine hI.read_tau hl hloc hR' hdd rfl rfl rfl rfl rfl rfl rfl rfl ?_
      simp only [PhOK] at hph3 ⊢
      exact ⟨hph3.1, fun h => ⟨(hph3.2.1 h).1, fun _ => (hph3.2.1 h).2 (by simp)⟩,
        fun _ _ _ => Or.inr hx⟩
    | @s10F k i v hx =>
      have hg : gstep G C (.tau q) = { G with t := G.t + 1 } := by simp [gstep, hl]
      rw [hg]
      refine hI.read_tau hl hloc hR' hdd rfl rfl rfl rfl rfl rfl rfl rfl ?_
      simp only [PhOK] at hph3
      simp only [PI1] at hpi1
      have hnew : G.ph = k → ∀ j, 1 ≤ j → j < i + 1 →
          j ∈ G.wc ∧ (k ≤ rndOf (Rg C j) ∨ G.free j = true) := by
        intro h j h4 h5
        rcases Nat.lt_succ_iff_lt_or_eq.1 h5 with h6 | h6
        · exact (hph3.2.1 h).1 j h4 h6
        · subst h6; exact ⟨(hph3.2.1 h).2 (by simp), Or.inl (by omega)⟩
      unfold nextIt; split_ifs with h3
      · simp only [PhOK]
        exact ⟨hph3.1, fun h => ⟨hnew h, by simp⟩, by simp⟩
      · simp only [PhOK]
        exact ⟨hph3.1, fun h j h4 h5 => hnew h j h4 (by omega)⟩
    | @scN k hx =>
      simp only [PI1] at hpi1
      by_cases hph : G.ph ≤ k
      · have hg : gstep G C (.tau q) =
            { G with
              t := G.t + 1
              psc := Function.update G.psc q (G.t + 1)
              ph := k + 1
              pst := G.t + 1
              wc := ∅
              cr := G.cr.erase ((q, c), false) } := by simp [gstep, hl, hph]
        rw [hg]
        have hphk : G.ph = k := by
          rcases Nat.eq_zero_or_pos k with h3 | h3
          · omega
          · have := h2.ph_ge k (hpi1 h3); omega
        exact hI.phase_step h1 h2 hl hphk hx hR' hloc
      · have hg : gstep G C (.tau q) =
            { G with t := G.t + 1, psc := Function.update G.psc q (G.t + 1) } := by
          simp [gstep, hl, hph]
        rw [hg]
        exact hI.read_tau hl hloc hR' hdd rfl rfl rfl rfl rfl rfl rfl rfl trivial
    | @scS k x hx =>
      have hph : ¬ G.ph ≤ k := by
        have := h2.ph_ge (k + 1) (by simp [hx]); omega
      have hg : gstep G C (.tau q) =
          { G with t := G.t + 1, psc := Function.update G.psc q (G.t + 1) } := by
        simp [gstep, hl, hph]
      rw [hg]
      exact hI.read_tau hl hloc hR' hdd rfl rfl rfl rfl rfl rfl rfl rfl trivial
    | @s8 k i v =>
      have hg : gstep G C (.tau q) = gwrite G (Rg C) (q, c) i true none := by simp [gstep, hl]
      rw [hg]
      have hcq : (C.loc q).cnt = c := by rw [hl]
      exact hI.write_step h1 h2 hcq hR' hloc (by rw [hl]; simp [Dead]) (by simp [lastId])
        (fun _ => trivial) (fun _ _ _ => rfl) (fun _ h => absurd h (by simp)) trivial
    | @fin k w =>
      simp only [PI1] at hpi1
      have hg : gstep G C (.tau q) = gwrite G (Rg C) (q, c) (k + 1) true (some (G.psc q)) := by
        simp [gstep, hl]
      rw [hg]
      have hcq : (C.loc q).cnt = c := by rw [hl]
      exact hI.write_step h1 h2 hcq hR' hloc (by rw [hl]; simp [Dead]) hpi1.2.2
        (fun _ => trivial) (fun _ _ _ => rfl) (fun _ h => absurd h (by simp)) trivial
    | @s11 k i v =>
      simp only [PI1] at hpi1
      obtain ⟨hi1, hik, hk⟩ := hpi1
      simp only [PhOK] at hph3
      obtain ⟨hA, hB, hC⟩ := hph3
      have hg : gstep G C (.tau q) =
          gwrite G (Rg C) (q, c) i (Rg C (k + 1)).isSome none := by simp [gstep, hl]
      rw [hg]
      have hcq : (C.loc q).cnt = c := by rw [hl]
      have hm : ∀ j, Rg C j ≠ none → Rg C' j ≠ none := fun j h => by
        rw [hR']; exact upd_ne_none h
      refine hI.write_step h1 h2 hcq hR' hloc (by rw [hl]; simp [Dead]) (by simp [lastId])
        ?_ ?_ ?_ ?_
      · intro hd
        have h3 : Rg C' (k + 1) ≠ none := hm _ (by simpa [Option.isSome_iff_ne_none] using hd)
        unfold nextIt; split_ifs <;> exact h3
      · intro k' hk' hkk
        simpa [Option.isSome_iff_ne_none] using
          h1.mem.contig k' (k + 1) hk' (by omega) (by simp at hkk; omega)
      · intro hi hd hcf
        have hk1 : Rg C (k + 1) = none := by simpa [Option.isSome_iff_ne_none] using hd
        have hph1 := hA hcf
        have hph2 : G.ph = k + 1 := by
          by_contra h3
          have h4 := h2.ph_prev (by omega)
          exact h1.mem.contig _ (k + 1) h4 (by omega) (by omega) hk1
        have h5 := hC trivial hcf hk1
        have h6 := hI.invis (by omega) (by rw [hph2]; exact hk1) i hi1 (by omega)
        rw [hph2] at h6
        simp only [Nat.add_sub_cancel] at h6
        rcases h5 with h5 | h5
        · exact absurd h5 hi
        rcases h6 with h6 | h6 | h6
        · exact absurd h6 hi
        · omega
        · exact h6
      · have hnew : G.ph = k → ∀ j, 1 ≤ j → j < i + 1 →
            j ∈ insert i G.wc ∧ (k ≤ rndOf (Rg C' j) ∨
              Function.update G.free i (!decide (i ∉ G.wc) && (Rg C (k + 1)).isSome) j = true) := by
          intro h j h4 h5
          rw [hR']
          rcases Nat.lt_succ_iff_lt_or_eq.1 h5 with h6 | h6
          · have h7 := (hB h).1 j h4 h6
            refine ⟨Finset.mem_insert_of_mem h7.1, ?_⟩
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact h7.2
          · subst h6
            refine ⟨Finset.mem_insert_self _ _, Or.inl ?_⟩
            simp [rndOf]
        have hA' : ((q, c), false) ∉ crAfter G.cr (Rg C i) (q, c) (decide (i ∉ G.wc))
            (Rg C (k + 1)).isSome → k + 1 ≤ G.ph := by
          intro h3
          by_cases h4 : ((q, c), false) ∈ G.cr
          · obtain ⟨h5, -⟩ := crAfter_removed h4 h3
            have h6 : i ∉ G.wc := by simpa using h5
            have h7 : G.ph ≠ k := fun h8 => h6 ((hB h8).2 (by simp))
            have := h2.ph_ge k hk; omega
          · exact hA h4
        unfold nextIt; split_ifs with h3
        · simp only [PhOK, gwrite_ph, gwrite_wc, gwrite_free, gwrite_cr]
          exact ⟨hA', fun h => ⟨hnew h, by simp⟩, by simp⟩
        · simp only [PhOK, gwrite_ph, gwrite_wc, gwrite_free, gwrite_cr]
          exact ⟨hA', fun h j h4 h5 => hnew h j h4 (by omega)⟩

theorem inv3_of_run {α : List (Label P TS)} {C : ACfg P} (h : (alg4 (P := P)).run α = some C) :
    Inv3 C (ghostOf α) := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run, Impl.runFrom_nil, Option.some.injEq] at h
    subst h; exact inv3_init
  | append_singleton α ℓ ih =>
    obtain ⟨C₀, h₀, hs⟩ := run_append_singleton h
    rw [ghostOf_append h₀ hs]
    exact (ih h₀).step (inv1_of_run h₀) (inv2_of_run h₀) hs

end Cslib.SharedMemory.Timestamp.Alg4
