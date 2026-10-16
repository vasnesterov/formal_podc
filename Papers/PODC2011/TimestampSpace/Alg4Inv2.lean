import Papers.PODC2011.TimestampSpace.Alg4Inv1

/-!
# Algorithm 4: the timing invariant

With the ghost times `wt` (last write), `bt` (first write), scan times `rsc`/`psc` and the
phase `ph` started at time `pst`:

* `VI x k s` — the properties of a line-15 value `x` for `R[k]` produced by a scan at time `s`:
  `x.seq[j] = last(R[j].seq)` as long as `R[j]` has not been written after the scan, and
  `x.seq[j] ≠ last(R[j].seq)` once it has (every write of a getTS to a register writes a fresh id
  — Claim 6.1 (b), via `IdOK`), the scan preceded the first write to `R[k]`, and phase `k` had
  started at the scan (Claim 6.6 (b)).
* the ids stored in the registers belong to operations that already passed the register
  (`IdOK`), so a later write by them to the same register is impossible;
* a register `R[j]` holding `rnd > j` (written at line 8 or 11) was written after `R[rnd]`
  became non-`⊥`;
* the iteration counter of the for loop and returned timestamps `(k, t)` satisfy: all
  `R[1..t]` were written after `R[k]` became non-`⊥` (the key fact behind Lemma 6.4).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp.Alg4

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

/-- The current operation of a process with program counter `pc` has passed register `j`: it
will not write `R[j]` any more. -/
def beyond : PC P → ℕ → Prop
  | .idle, _ => False
  | .done _, _ => True
  | .wh _ _, _ => False
  | .loop _ i _ _, j => j < i
  | .scan k, j => j < k
  | .fin k _, j => j < k

/-- An id `x` stored for register `j` belongs to an operation that has already passed `j`. -/
def IdOK (loc : P → Loc P) (x : Option (P × ℕ)) (j : ℕ) : Prop :=
  ∀ q c, x = some (q, c) → c < (loc q).cnt ∨ (c = (loc q).cnt ∧ beyond (loc q).pc j)

/-- Local states only move forward. -/
def LocMono (loc loc' : P → Loc P) : Prop :=
  ∀ q, (loc q).cnt < (loc' q).cnt ∨
    ((loc' q).cnt = (loc q).cnt ∧ ∀ j, beyond (loc q).pc j → beyond (loc' q).pc j)

lemma LocMono.refl (loc : P → Loc P) : LocMono loc loc := fun _ => Or.inr ⟨rfl, fun _ h => h⟩

lemma LocMono.update {loc : P → Loc P} {p : P} {l : Loc P}
    (h : (loc p).cnt < l.cnt ∨ (l.cnt = (loc p).cnt ∧ ∀ j, beyond (loc p).pc j → beyond l.pc j)) :
    LocMono loc (Function.update loc p l) := by
  intro q
  by_cases hq : q = p
  · subst hq; simpa using h
  · rw [Function.update_of_ne hq]; exact Or.inr ⟨rfl, fun _ h => h⟩

lemma IdOK.mono {loc loc' : P → Loc P} {x : Option (P × ℕ)} {j : ℕ} (h : IdOK loc x j)
    (hm : LocMono loc loc') : IdOK loc' x j := by
  intro q c hx
  rcases h q c hx with h1 | ⟨h1, h2⟩
  · rcases hm q with h3 | ⟨h3, -⟩ <;> omega
  · rcases hm q with h3 | ⟨h3, h4⟩
    · left; omega
    · right; exact ⟨by omega, h4 j h2⟩

/-- Properties of a line-15 value `x` for `R[k]` produced by a scan at time `s`. -/
structure VI (R : Mem P) (loc : P → Loc P) (G : Gh P) (x : Option (Val P)) (k s : ℕ) : Prop where
  eq : ∀ j, 1 ≤ j → j < k → G.wt j ≤ s → seqAt x j = lastId (R j)
  ne : ∀ j, 1 ≤ j → j < k → s < G.wt j → seqAt x j ≠ lastId (R j)
  ids : ∀ j, 1 ≤ j → j < k → IdOK loc (seqAt x j) j
  bt : R k ≠ none → s < G.bt k
  ph : k ≤ G.ph
  pst : G.ph = k → G.pst ≤ s
  sle : s ≤ G.t

lemma VI.transfer {R : Mem P} {loc loc' : P → Loc P} {G G' : Gh P} {x : Option (Val P)}
    {k s : ℕ} (h : VI R loc G x k s) (hm : LocMono loc loc') (hwt : G'.wt = G.wt)
    (hbt : G'.bt = G.bt) (ht : G.t ≤ G'.t) (hph : k ≤ G'.ph)
    (hpst : G'.ph = k → G'.pst ≤ s) : VI R loc' G' x k s :=
  ⟨fun j h1 h2 h3 => h.eq j h1 h2 (hwt ▸ h3), fun j h1 h2 h3 => h.ne j h1 h2 (hwt ▸ h3),
    fun j h1 h2 => (h.ids j h1 h2).mono hm, fun h1 => hbt ▸ h.bt h1, hph, hpst,
    h.sle.trans ht⟩

/-- A step that changes neither the memory nor the times, phase. -/
lemma VI.same {R : Mem P} {loc loc' : P → Loc P} {G G' : Gh P} {x : Option (Val P)}
    {k s : ℕ} (h : VI R loc G x k s) (hm : LocMono loc loc') (hwt : G'.wt = G.wt)
    (hbt : G'.bt = G.bt) (ht : G.t ≤ G'.t) (hph : G'.ph = G.ph) (hpst : G'.pst = G.pst) :
    VI R loc' G' x k s :=
  h.transfer hm hwt hbt ht (hph ▸ h.ph) (fun h1 => hpst ▸ h.pst (hph ▸ h1))

/-- Effect of a write of `v` (with last id `id`, the writer not beyond `j`) on `VI`. -/
lemma VI.write {R : Mem P} {loc loc' : P → Loc P} {G : Gh P} {x : Option (Val P)}
    {k s j : ℕ} {v : Val P} {q : P} {dead : Bool} {sc : Option ℕ} (h : VI R loc G x k s)
    (hm : LocMono loc loc') (hnb : ¬ beyond (loc q).pc j)
    (hid : lastId (some v) = some (q, (loc q).cnt)) :
    VI (Function.update R j (some v)) loc' (gwrite G R (q, (loc q).cnt) j dead sc) x k s := by
  have hsle := h.sle
  refine ⟨?_, ?_, ?_, ?_, h.ph, h.pst, by simp [gwrite]; omega⟩
  · intro i h1 h2 h3
    simp only [gwrite] at h3
    by_cases hij : i = j
    · subst hij; simp at h3; omega
    · rw [Function.update_of_ne hij] at h3 ⊢; exact h.eq i h1 h2 h3
  · intro i h1 h2 h3
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, hid]
      intro hx
      rcases h.ids i h1 h2 q _ hx with h4 | ⟨-, h4⟩
      · omega
      · exact hnb h4
    · simp only [gwrite, Function.update_of_ne hij] at h3 ⊢; exact h.ne i h1 h2 h3
  · exact fun i h1 h2 => (h.ids i h1 h2).mono hm
  · intro hk
    simp only [gwrite]
    by_cases hkj : k = j
    · subst hkj
      cases hR : R k with
      | none => simp; omega
      | some w => simp only [Option.isNone_some, Bool.false_eq_true, ite_false]; exact h.bt (by simp [hR])
    · rw [Function.update_of_ne hkj] at hk
      split_ifs
      · rw [Function.update_of_ne hkj]; exact h.bt hk
      · exact h.bt hk

lemma VI.write' {R : Mem P} {loc loc' : P → Loc P} {G : Gh P} {x : Option (Val P)}
    {k s j c : ℕ} {v : Val P} {q : P} {dead : Bool} {sc : Option ℕ} (h : VI R loc G x k s)
    (hm : LocMono loc loc') (hc : (loc q).cnt = c) (hnb : ¬ beyond (loc q).pc j)
    (hid : lastId (some v) = some (q, c)) :
    VI (Function.update R j (some v)) loc' (gwrite G R (q, c) j dead sc) x k s := by
  subst hc; exact h.write hm hnb hid

/-- Per-process part of the timing invariant. -/
def PI2 (R : Mem P) (loc : P → Loc P) (G : Gh P) (p : P) (l : Loc P) : Prop :=
  match l.pc with
  | .wh j v => 2 ≤ j → R j = none → VI R loc G v (j - 1) (G.psc p)
  | .loop k i v _ => VI R loc G v k (G.psc p) ∧ ∀ j, 1 ≤ j → j < i → G.bt k < G.wt j
  | .fin k w => VI R loc G (some w) (k + 1) (G.psc p)
  | .done (.inl (k, t)) => ∀ j, 1 ≤ j → j ≤ t → G.bt k < G.wt j
  | _ => True

/-- The timing invariant. -/
structure Inv2 (C : ACfg P) (G : Gh P) : Prop where
  wt_le : ∀ j, G.wt j ≤ G.t
  wt0 : ∀ j, Rg C j = none → G.wt j = 0
  bt_pos : ∀ j, Rg C j ≠ none → 1 ≤ G.bt j ∧ G.bt j ≤ G.wt j
  bt_mono : ∀ j x, Rg C x ≠ none → 1 ≤ j → j < x → G.bt j < G.bt x
  k13 : ∀ j w, Rg C j = some w → j < w.rnd → G.bt w.rnd < G.wt j
  ids : ∀ j, IdOK C.loc (lastId (Rg C j)) j
  rvi : ∀ k, 1 ≤ k → Rg C k ≠ none → Rg C (k + 1) = none →
    VI (Rg C) C.loc G (Rg C k) k (G.rsc k)
  ph_ge : ∀ j, Rg C j ≠ none → j ≤ G.ph
  ph_prev : 2 ≤ G.ph → Rg C (G.ph - 1) ≠ none
  pst_le : G.pst ≤ G.t
  wph : Rg C G.ph ≠ none → G.pst < G.wt G.ph
  pi : ∀ p, PI2 (Rg C) C.loc G p (C.loc p)

lemma inv2_init : Inv2 (alg4 (P := P)).initCfg Gh.init := by
  refine ⟨fun _ => le_rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, le_rfl, ?_, ?_⟩ <;>
    simp [Impl.initCfg, alg4, Gh.init, IdOK, lastId, PI2, Rg]

lemma VI.transfer2 {R : Mem P} {loc loc' : P → Loc P} {G G' : Gh P} {x : Option (Val P)}
    {k s : ℕ} (h : VI R loc G x k s) (hm : LocMono loc loc') (hwt : G'.wt = G.wt)
    (hbt : G'.bt = G.bt) (ht : G.t ≤ G'.t)
    (hphc : (G'.ph = G.ph ∧ G'.pst = G.pst) ∨ G.ph < G'.ph) : VI R loc' G' x k s := by
  have h1 := h.ph
  have h2 := h.pst
  refine h.transfer hm hwt hbt ht ?_ ?_
  · rcases hphc with ⟨h3, -⟩ | h3 <;> omega
  · intro h4
    rcases hphc with ⟨h3, h5⟩ | h3
    · rw [h5]; exact h2 (by omega)
    · omega

/-! ### Ghost after a write -/

section GWrite

variable {G : Gh P} {R : Mem P} {id : P × ℕ} {j : ℕ} {dead : Bool} {sc : Option ℕ}

@[simp] lemma gwrite_t : (gwrite G R id j dead sc).t = G.t + 1 := rfl
@[simp] lemma gwrite_psc : (gwrite G R id j dead sc).psc = G.psc := rfl
@[simp] lemma gwrite_ph : (gwrite G R id j dead sc).ph = G.ph := rfl
@[simp] lemma gwrite_pst : (gwrite G R id j dead sc).pst = G.pst := rfl
@[simp] lemma gwrite_nget : (gwrite G R id j dead sc).nget = G.nget := rfl

lemma gwrite_wt (i : ℕ) :
    (gwrite G R id j dead sc).wt i = if i = j then G.t + 1 else G.wt i := by
  simp only [gwrite, Function.update_apply]

lemma gwrite_bt_of_ne_none {k : ℕ} (hk : R k ≠ none) :
    (gwrite G R id j dead sc).bt k = G.bt k := by
  simp only [gwrite]
  split_ifs with h
  · rw [Function.update_of_ne]; rintro rfl; simp_all
  · rfl

lemma gwrite_bt_of_ne {k : ℕ} (hk : k ≠ j) : (gwrite G R id j dead sc).bt k = G.bt k := by
  simp only [gwrite]; split_ifs <;> first | rfl | simp [Function.update_of_ne hk]

lemma gwrite_rsc_of_ne {k : ℕ} (hk : k ≠ j) : (gwrite G R id j dead sc).rsc k = G.rsc k := by
  simp only [gwrite]; cases sc <;> simp [Function.update_of_ne hk]

lemma gwrite_rsc_self {s : ℕ} : (gwrite G R id j dead (some s)).rsc j = s := by
  simp [gwrite]

end GWrite

lemma upd_eq_none {R : Mem P} {i j : ℕ} {v : Val P} (h : Function.update R j (some v) i = none) :
    R i = none ∧ i ≠ j := by
  by_cases hij : i = j
  · subst hij; simp at h
  · rw [Function.update_of_ne hij] at h; exact ⟨h, hij⟩

/-- Per-process timing facts survive steps that do not touch the memory or the times. -/
lemma PI2.transfer {R : Mem P} {loc loc' : P → Loc P} {G G' : Gh P} {p : P} {l : Loc P}
    (h : PI2 R loc G p l) (hm : LocMono loc loc') (hwt : G'.wt = G.wt) (hbt : G'.bt = G.bt)
    (ht : G.t ≤ G'.t) (hpsc : G'.psc p = G.psc p)
    (hphc : (G'.ph = G.ph ∧ G'.pst = G.pst) ∨ G.ph < G'.ph) : PI2 R loc' G' p l := by
  unfold PI2 at h ⊢
  rcases l with ⟨c, pc⟩
  cases pc with
  | wh j v => intro h1 h2; rw [hpsc]; exact (h h1 h2).transfer2 hm hwt hbt ht hphc
  | loop k i v s => rw [hpsc, hwt, hbt]; exact ⟨h.1.transfer2 hm hwt hbt ht hphc, h.2⟩
  | fin k w => rw [hpsc]; exact h.transfer2 hm hwt hbt ht hphc
  | done r =>
    rcases r with ⟨k, t⟩ | b
    · rw [hwt, hbt]; exact h
    · trivial
  | idle => trivial
  | scan k => trivial

/-- Per-process timing facts of a process not taking the step survive a write. -/
lemma PI2.write {R : Mem P} {loc loc' : P → Loc P} {G : Gh P} {p q : P} {l : Loc P}
    {j : ℕ} {v : Val P} {dead : Bool} {sc : Option ℕ}
    (h : PI2 R loc G p l) (h1 : PI1 R p l) (hm : LocMono loc loc') (hwl : ∀ i, G.wt i ≤ G.t)
    (hnb : ¬ beyond (loc q).pc j) (hid : lastId (some v) = some (q, (loc q).cnt)) :
    PI2 (Function.update R j (some v)) loc' (gwrite G R (q, (loc q).cnt) j dead sc) p l := by
  unfold PI2 at h ⊢
  unfold PI1 at h1
  rcases l with ⟨c, pc⟩
  cases pc with
  | wh j' v' =>
    intro h2 h3
    obtain ⟨h4, -⟩ := upd_eq_none h3
    exact (h h2 h4).write hm hnb hid
  | loop k i v' s =>
    refine ⟨h.1.write hm hnb hid, fun i' h2 h3 => ?_⟩
    rw [gwrite_bt_of_ne_none h1.2.2, gwrite_wt]
    have := h.2 i' h2 h3
    have := hwl i'
    split_ifs <;> omega
  | fin k w => exact h.write hm hnb hid
  | done r =>
    rcases r with ⟨k, t⟩ | b
    · intro i' h2 h3
      rw [gwrite_bt_of_ne_none h1.2, gwrite_wt]
      have := h i' h2 h3
      have := hwl i'
      split_ifs <;> omega
    · trivial
  | idle => trivial
  | scan k => trivial

/-- Preservation of the timing invariant by steps that do not write. -/
lemma Inv2.read_step {C C' : ACfg P} {G G' : Gh P} {q : P} (hI : Inv2 C G)
    (hR : Rg C' = Rg C) (hm : LocMono C.loc C'.loc) (hloc : ∀ p, p ≠ q → C'.loc p = C.loc p)
    (hwt : G'.wt = G.wt) (hbt : G'.bt = G.bt) (hrsc : G'.rsc = G.rsc) (ht : G'.t = G.t + 1)
    (hpsc : ∀ p, p ≠ q → G'.psc p = G.psc p)
    (hphc : (G'.ph = G.ph ∧ G'.pst = G.pst) ∨
      (G'.ph = G.ph + 1 ∧ G'.pst = G'.t ∧ Rg C G'.ph = none ∧
        (2 ≤ G'.ph → Rg C (G'.ph - 1) ≠ none)))
    (hq : PI2 (Rg C') C'.loc G' q (C'.loc q)) : Inv2 C' G' := by
  have hphc' : (G'.ph = G.ph ∧ G'.pst = G.pst) ∨ G.ph < G'.ph :=
    hphc.imp id (fun h => by omega)
  have hwl := hI.wt_le
  have hpl := hI.pst_le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; rw [hwt]; have := hwl j; omega
  · rw [hR, hwt]; exact hI.wt0
  · rw [hR, hwt, hbt]; exact hI.bt_pos
  · rw [hR, hbt]; exact hI.bt_mono
  · rw [hR, hwt, hbt]; exact hI.k13
  · intro j; rw [hR]; exact (hI.ids j).mono hm
  · intro k h1 h2 h3
    rw [hR] at h2 h3 ⊢; rw [hrsc]
    exact (hI.rvi k h1 h2 h3).transfer2 hm hwt hbt (by omega) hphc'
  · intro j hj; rw [hR] at hj; have := hI.ph_ge j hj; omega
  · intro h2; rw [hR]
    rcases hphc with ⟨h3, -⟩ | ⟨-, -, -, h3⟩
    · rw [h3] at h2 ⊢; exact hI.ph_prev h2
    · exact h3 h2
  · rcases hphc with ⟨-, h3⟩ | ⟨-, h3, -⟩ <;> omega
  · intro h2; rw [hR] at h2
    rcases hphc with ⟨h3, h4⟩ | ⟨-, -, h4, -⟩
    · rw [h3, h4, hwt]; rw [h3] at h2; exact hI.wph h2
    · exact absurd h4 h2
  · intro p
    by_cases hp : p = q
    · subst hp; exact hq
    · rw [hloc p hp, hR]
      exact (hI.pi p).transfer hm hwt hbt (by omega) (hpsc p hp) hphc'

/-- Preservation of the timing invariant by a write of `q` to `R[j]`. -/
lemma Inv2.write_step {α : List (Label P TS)} {C C' : ACfg P} {G : Gh P} {q : P} {c : ℕ}
    {pc' : PC P} {j : ℕ} {v : Val P} {dead : Bool} {sc : Option ℕ}
    (hI : Inv2 C G) (h1 : Inv1 α C) (hcq : (C.loc q).cnt = c)
    (hR : Rg C' = Function.update (Rg C) j (some v))
    (hloc : C'.loc = Function.update C.loc q ⟨c, pc'⟩)
    (hnb : ¬ beyond (C.loc q).pc j) (hb : ∀ i, beyond (C.loc q).pc i → beyond pc' i)
    (hbj : beyond pc' j) (hid : lastId (some v) = some (q, c))
    (hprev : ∀ i, 1 ≤ i → i < j → Rg C i ≠ none)
    (hrnd : j < v.rnd → Rg C v.rnd ≠ none) (hphj : j ≤ G.ph)
    (hrvi : Rg C (j + 1) = none →
      VI (Rg C') C'.loc (gwrite G (Rg C) (q, c) j dead sc) (some v) j
        ((gwrite G (Rg C) (q, c) j dead sc).rsc j))
    (hq : PI2 (Rg C') C'.loc (gwrite G (Rg C) (q, c) j dead sc) q ⟨c, pc'⟩) :
    Inv2 C' (gwrite G (Rg C) (q, c) j dead sc) := by
  subst hcq
  have hm : LocMono C.loc C'.loc := by
    rw [hloc]; exact LocMono.update (Or.inr ⟨rfl, hb⟩)
  have hwl := hI.wt_le
  have hpl := hI.pst_le
  set G' := gwrite G (Rg C) (q, (C.loc q).cnt) j dead sc with hG'
  have hbtj : ∀ i, Rg C i ≠ none → G'.bt i = G.bt i := fun i h => gwrite_bt_of_ne_none h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; rw [hG', gwrite_wt]; have := hwl i; split_ifs <;> (simp; try omega)
  · intro i hi; rw [hR] at hi
    obtain ⟨h2, h3⟩ := upd_eq_none hi
    rw [hG', gwrite_wt]; simp only [h3, ↓reduceIte]; exact hI.wt0 i h2
  · intro i hi
    rw [hG', gwrite_wt]
    by_cases hij : i = j
    · subst hij
      simp only [gwrite, ↓reduceIte]
      cases hRi : Rg C i with
      | none => simp
      | some w =>
        simp only [Option.isNone_some, Bool.false_eq_true, ite_false]
        have := hI.bt_pos i (by simp [hRi]); have := hwl i; omega
    · rw [hR, Function.update_of_ne hij] at hi
      simp only [hij, ↓reduceIte]; rw [hbtj i hi]; exact hI.bt_pos i hi
  · intro i x hx hi hix
    rw [hR] at hx
    have hRi : Rg C i ≠ none := by
      by_cases hxj : x = j
      · subst hxj; exact hprev i hi hix
      · rw [Function.update_of_ne hxj] at hx; exact h1.mem.contig x i hx hi hix.le
    rw [hbtj i hRi]
    by_cases hxj : x = j
    · subst hxj
      cases hRx : Rg C x with
      | none =>
        simp only [hG', gwrite, hRx, Option.isNone_none, ite_true, Function.update_self]
        have := (hI.bt_pos i hRi).2; have := hwl i; omega
      | some w =>
        rw [hbtj x (by simp [hRx])]; exact hI.bt_mono i x (by simp [hRx]) hi hix
    · rw [Function.update_of_ne hxj] at hx
      rw [hbtj x hx]; exact hI.bt_mono i x hx hi hix
  · intro i w hw hiw
    rw [hR] at hw
    rw [hG', gwrite_wt]
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self, Option.some.injEq] at hw; subst hw
      have h2 := hrnd hiw
      simp only [↓reduceIte]; rw [hbtj _ h2]
      have := (hI.bt_pos _ h2).2; have := hwl v.rnd; omega
    · rw [Function.update_of_ne hij] at hw
      simp only [hij, ↓reduceIte]
      have h2 := ((h1.mem.regs i w hw).2.2.resolve_left (by omega)).2
      rw [hbtj _ h2]; exact hI.k13 i w hw hiw
  · intro i
    rw [hR]
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, hid]
      intro q' c' h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      right; rw [hloc]; simp [hbj]
    · rw [Function.update_of_ne hij]; exact (hI.ids i).mono hm
  · intro m hm1 hm2 hm3
    rw [hR] at hm2 hm3 ⊢
    by_cases hmj : m = j
    · subst hmj
      rw [Function.update_self]
      have := hrvi (upd_eq_none hm3).1
      rw [hR] at this
      simpa using this
    · have hm4 : m + 1 ≠ j := by rintro rfl; simp at hm3
      rw [Function.update_of_ne hmj] at hm2 ⊢
      rw [Function.update_of_ne hm4] at hm3
      rw [hG', gwrite_rsc_of_ne hmj]
      have := (hI.rvi m hm1 hm2 hm3).write (dead := dead) (sc := sc) hm hnb hid
      exact this
  · intro i hi; rw [hR] at hi
    by_cases hij : i = j
    · subst hij; simpa [hG'] using hphj
    · rw [Function.update_of_ne hij] at hi; simpa [hG'] using hI.ph_ge i hi
  · intro h2; simp only [hG', gwrite_ph] at h2 ⊢; rw [hR]
    exact upd_ne_none (hI.ph_prev h2)
  · simp [hG']; omega
  · intro h2; simp only [hG', gwrite_ph, gwrite_pst] at h2 ⊢
    rw [gwrite_wt]
    split_ifs with h3
    · omega
    · rw [hR, Function.update_of_ne h3] at h2; exact hI.wph h2
  · intro p
    by_cases hp : p = q
    · subst hp
      have : C'.loc p = ⟨(C.loc p).cnt, pc'⟩ := by rw [hloc, Function.update_self]
      rw [this]; exact hq
    · have : C'.loc p = C.loc p := by rw [hloc, Function.update_of_ne hp]
      rw [this, hR]
      exact (hI.pi p).write (h1.pi p) hm hwl hnb hid

lemma TauEff.beyond {p : P} {c : ℕ} {R R' : Mem P} {pc pc' : PC P} (hpi : PI1 R p ⟨c, pc⟩)
    (h : TauEff p c R pc pc' R') : ∀ j, beyond pc j → beyond pc' j := by
  intro j hj
  cases h with
  | whS _ => exact hj.elim
  | whN _ => exact hj.elim
  | s10F _ | s11 =>
    simp only [PI1] at hpi
    change j < _ at hj
    unfold nextIt; split_ifs
    · change j < _ + 1; omega
    · change j < _; omega
  | _ => first | exact hj | trivial

lemma seqAt_newSeq (r : Mem P) (k : ℕ) (id : P × ℕ) (rnd j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ k) :
    seqAt (some (⟨newSeq r k id, rnd⟩ : Val P)) j = some ((lastId (r j)).getD id) := by
  simp only [seqAt, newSeq, Option.bind_some]
  rw [List.getElem?_append_left (by simp; omega)]
  simp only [List.getElem?_map, List.getElem?_range (show j - 1 < k by omega), Option.map_some]
  rw [Nat.sub_add_cancel h1]

/-- The value computed at line 15 after a scan at time `G.t + 1`. -/
lemma vi_scan {α : List (Label P TS)} {C : ACfg P} {G G' : Gh P} {loc' : P → Loc P} {q : P}
    {c k : ℕ} (h1 : Inv1 α C) (hI : Inv2 C G) (hm : LocMono C.loc loc')
    (hk : 1 ≤ k → Rg C k ≠ none) (hk1 : Rg C (k + 1) = none)
    (hwt : G'.wt = G.wt) (ht : G'.t = G.t + 1) (hph : k + 1 ≤ G'.ph)
    (hpst : G'.ph = k + 1 → G'.pst ≤ G.t + 1) :
    VI (Rg C) loc' G' (some ⟨newSeq (Rg C) k (q, c), k + 1⟩) (k + 1) (G.t + 1) := by
  have hl : ∀ j, 1 ≤ j → j < k + 1 →
      seqAt (some (⟨newSeq (Rg C) k (q, c), k + 1⟩ : Val P)) j = lastId (Rg C j) := by
    intro j hj1 hj2
    rw [seqAt_newSeq _ _ _ _ _ hj1 (by omega)]
    have hR : Rg C j ≠ none := h1.mem.contig k j (hk (by omega)) hj1 (by omega)
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hR
    have := (h1.mem.regs j w hw).1
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 this
    rw [hw, hx]; rfl
  refine ⟨fun j h2 h3 _ => hl j h2 h3, ?_, ?_, ?_, hph, hpst, by omega⟩
  · intro j h2 h3 h4; rw [hwt] at h4; have := hI.wt_le j; omega
  · intro j h2 h3; rw [hl j h2 h3]; exact (hI.ids j).mono hm
  · intro h; exact absurd hk1 h

/-- **Preservation of the timing invariant.** -/
theorem Inv2.step {α : List (Label P TS)} {C C' : ACfg P} {G : Gh P} {ℓ : Label P TS}
    (hI : Inv2 C G) (h1 : Inv1 α C) (hs : (alg4 (P := P)).step C ℓ = some C') :
    Inv2 C' (gstep G C ℓ) := by
  cases ℓ with
  | inv q o =>
    obtain ⟨h0, -, hloc, hmem⟩ := step_inv' hs
    have hidle := (h1.idle q).1 h0
    have hcnt : ((alg4 (P := P)).invoke q (C.loc q) o).cnt = (C.loc q).cnt := by
      cases o <;> rfl
    apply hI.read_step (q := q) (by simp [Rg, hmem])
    · rw [hloc]
      exact LocMono.update (Or.inr ⟨hcnt, fun j h => by rw [hidle] at h; exact h.elim⟩)
    · intro p hp; rw [hloc, Function.update_of_ne hp]
    all_goals first
      | (cases o <;> rfl)
      | (intro p hp; cases o <;> rfl)
      | (left; constructor <;> cases o <;> rfl)
      | skip
    rw [hloc, Function.update_self]
    cases o <;> simp [alg4, PI2]
  | ret q r =>
    obtain ⟨h0, -, hmem, h2⟩ := step_ret' hs
    rcases h2 with ⟨-, hloc⟩ | hpc
    swap
    · exact absurd ((h1.idle q).2 hpc) h0
    apply hI.read_step (q := q) (by simp [Rg, hmem])
    · rw [hloc]; exact LocMono.update (Or.inl (by simp))
    · intro p hp; rw [hloc, Function.update_of_ne hp]
    all_goals first
      | rfl
      | (intro p hp; rfl)
      | (left; constructor <;> rfl)
      | skip
    rw [hloc, Function.update_self]
    simp [PI2]
  | tau q =>
    obtain ⟨pc', h0, -, h2, hT⟩ := tau_step hs
    have hpi1 := h1.pi q
    have hpi2 := hI.pi q
    generalize hl : C.loc q = l at h2 hT hpi1 hpi2
    obtain ⟨c, pc⟩ := l
    generalize hR' : Rg C' = R' at hT
    simp only at hT
    have hb := hT.beyond hpi1
    have hm : LocMono C.loc C'.loc := by
      rw [h2]; exact LocMono.update (by rw [hl]; exact Or.inr ⟨rfl, hb⟩)
    have hloc : ∀ p, p ≠ q → C'.loc p = C.loc p := fun p hp => by
      rw [h2, Function.update_of_ne hp]
    have hlq : C'.loc q = ⟨c, pc'⟩ := by rw [h2, Function.update_self]
    have hwl := hI.wt_le
    cases hT with
    | @whS j v x hx =>
      have hg : gstep G C (.tau q) = { G with t := G.t + 1, psc := Function.update G.psc q (G.rsc j) } := by
        simp [gstep, hl, hx]
      rw [hg]
      refine hI.read_step hR' hm hloc rfl rfl rfl rfl
        (fun p hp => by simp [Function.update_of_ne hp]) (Or.inl ⟨rfl, rfl⟩) ?_
      rw [hlq, hR']
      simp only [PI2] at hpi1 ⊢
      intro _ h3
      have := hI.rvi j hpi1.1 (by simp [hx]) h3
      rw [hx] at this
      have h5 := this.same (G' := { G with t := G.t + 1, psc := Function.update G.psc q (G.rsc j) })
        hm rfl rfl (by simp) rfl rfl
      simpa using h5
    | @whN j v hx =>
      have hg : gstep G C (.tau q) = { G with t := G.t + 1 } := by simp [gstep, hl, hx]
      rw [hg]
      refine hI.read_step hR' hm hloc rfl rfl rfl rfl (fun p hp => rfl) (Or.inl ⟨rfl, rfl⟩) ?_
      rw [hlq, hR']
      simp only [PI2] at hpi1 hpi2 ⊢
      unfold endWh
      split_ifs with h3
      · simp only
        refine ⟨(hpi2 (by omega) hx).same hm rfl rfl (by simp) rfl rfl, fun j h4 h5 => by omega⟩
      · trivial
    | @s6N k i v hx =>
      have hg : gstep G C (.tau q) = { G with t := G.t + 1 } := by simp [gstep, hl]
      rw [hg]
      refine hI.read_step hR' hm hloc rfl rfl rfl rfl (fun p hp => rfl) (Or.inl ⟨rfl, rfl⟩) ?_
      rw [hlq, hR']
      simp only [PI2] at hpi2 ⊢
      exact ⟨hpi2.1.same hm rfl rfl (by simp) rfl rfl, hpi2.2⟩
    | @s6S k i v x hx =>
      have hg : gstep G C (.tau q) = { G with t := G.t + 1 } := by simp [gstep, hl]
      rw [hg]
      refine hI.read_step hR' hm hloc rfl rfl rfl rfl (fun p hp => rfl) (Or.inl ⟨rfl, rfl⟩) ?_
      rw [hlq, hR']
      simp only [PI2] at hpi2 ⊢
      intro j h3 h4; omega
    | s7T _ =>
      have hg : gstep G C (.tau q) = { G with t := G.t + 1 } := by simp [gstep, hl]
      rw [hg]
      refine hI.read_step hR' hm hloc rfl rfl rfl rfl (fun p hp => rfl) (Or.inl ⟨rfl, rfl⟩) ?_
      rw [hlq, hR']
      simp only [PI2] at hpi2 ⊢
      exact ⟨hpi2.1.same hm rfl rfl (by simp) rfl rfl, hpi2.2⟩
    | s7F _ =>
      have hg : gstep G C (.tau q) = { G with t := G.t + 1 } := by simp [gstep, hl]
      rw [hg]
      refine hI.read_step hR' hm hloc rfl rfl rfl rfl (fun p hp => rfl) (Or.inl ⟨rfl, rfl⟩) ?_
      rw [hlq, hR']
      simp only [PI2] at hpi2 ⊢
      exact ⟨hpi2.1.same hm rfl rfl (by simp) rfl rfl, hpi2.2⟩
    | s10T _ =>
      have hg : gstep G C (.tau q) = { G with t := G.t + 1 } := by simp [gstep, hl]
      rw [hg]
      refine hI.read_step hR' hm hloc rfl rfl rfl rfl (fun p hp => rfl) (Or.inl ⟨rfl, rfl⟩) ?_
      rw [hlq, hR']
      simp only [PI2] at hpi2 ⊢
      exact ⟨hpi2.1.same hm rfl rfl (by simp) rfl rfl, hpi2.2⟩
    | @s10F k i v hx =>
      simp only [PI1] at hpi1
      obtain ⟨hi1, hik, hk⟩ := hpi1
      have hstamp : G.bt k < G.wt i := by
        cases hRi : Rg C i with
        | none => simp [rndOf, hRi] at hx; omega
        | some w =>
          simp only [rndOf, hRi, not_lt] at hx
          have hr := h1.mem.regs i w hRi
          have h4 := hI.k13 i w hRi (by omega)
          rcases hr.2.2 with h5 | ⟨-, h5⟩
          · omega
          rcases eq_or_lt_of_le hx with h6 | h6
          · rw [h6]; exact h4
          · have := hI.bt_mono k w.rnd h5 (by omega) h6; omega
      have hg : gstep G C (.tau q) = { G with t := G.t + 1 } := by simp [gstep, hl]
      rw [hg]
      refine hI.read_step hR' hm hloc rfl rfl rfl rfl (fun p hp => rfl) (Or.inl ⟨rfl, rfl⟩) ?_
      rw [hlq, hR']
      simp only [PI2] at hpi2
      unfold nextIt; split_ifs with h3
      · simp only [PI2]
        refine ⟨hpi2.1.same hm rfl rfl (by simp) rfl rfl, fun j h4 h5 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h5 with h6 | h6
        · exact hpi2.2 j h4 h6
        · subst h6; exact hstamp
      · simp [PI2]
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
          · have := hI.ph_ge k (hpi1 h3); omega
        refine hI.read_step hR' hm hloc rfl rfl rfl rfl
          (fun p hp => by simp [Function.update_of_ne hp])
          (Or.inr ⟨by simp; omega, rfl, by simpa using hx,
            fun h3 => by simpa using hpi1 (by simp at h3; omega)⟩) ?_
        rw [hlq, hR']
        simp only [PI2, Function.update_self]
        exact vi_scan h1 hI hm hpi1 hx rfl rfl (by simp) (fun _ => by simp)
      · have hg : gstep G C (.tau q) =
            { G with t := G.t + 1, psc := Function.update G.psc q (G.t + 1) } := by
          simp [gstep, hl, hph]
        rw [hg]
        refine hI.read_step hR' hm hloc rfl rfl rfl rfl
          (fun p hp => by simp [Function.update_of_ne hp]) (Or.inl ⟨rfl, rfl⟩) ?_
        rw [hlq, hR']
        simp only [PI2, Function.update_self]
        exact vi_scan h1 hI hm hpi1 hx rfl rfl (by simp; omega)
          (fun h => by have := hI.pst_le; simp; omega)
    | @scS k x hx =>
      simp only [PI1] at hpi1
      have hph : ¬ G.ph ≤ k := by
        have := hI.ph_ge (k + 1) (by simp [hx]); omega
      have hg : gstep G C (.tau q) =
          { G with t := G.t + 1, psc := Function.update G.psc q (G.t + 1) } := by
        simp [gstep, hl, hph]
      rw [hg]
      refine hI.read_step hR' hm hloc rfl rfl rfl rfl
        (fun p hp => by simp [Function.update_of_ne hp]) (Or.inl ⟨rfl, rfl⟩) ?_
      rw [hlq, hR']
      simp only [PI2]
      intro j h3 h4; omega
    | @s8 k i v =>
      simp only [PI1] at hpi1
      obtain ⟨hi1, hik, hk⟩ := hpi1
      have hg : gstep G C (.tau q) = gwrite G (Rg C) (q, c) i true none := by simp [gstep, hl]
      rw [hg]
      have hcq : (C.loc q).cnt = c := by rw [hl]
      have hnb : ¬ beyond (C.loc q).pc i := by rw [hl]; exact lt_irrefl i
      have hid : lastId (some (⟨[(q, c)], k⟩ : Val P)) = some (q, c) := by simp [lastId]
      refine hI.write_step (pc' := .done (.inl (k, i))) h1 hcq hR' (by rw [h2]) hnb
        (by rw [hl]; exact hb) trivial hid
        (fun i' h3 h4 => h1.mem.contig k i' hk h3 (by omega)) (fun _ => hk)
        (by have := hI.ph_ge k hk; omega)
        (fun h3 => absurd h3 (h1.mem.contig k (i + 1) hk (by omega) (by omega))) ?_
      simp only [PI2]
      intro j h3 h4
      rw [gwrite_bt_of_ne_none hk, gwrite_wt]
      have := (hI.bt_pos k hk).2; have := hwl k
      split_ifs with h5
      · omega
      · exact hpi2.2 j h3 (by omega)
    | @s11 k i v =>
      simp only [PI1] at hpi1
      obtain ⟨hi1, hik, hk⟩ := hpi1
      have hg : gstep G C (.tau q) =
          gwrite G (Rg C) (q, c) i (Rg C (k + 1)).isSome none := by simp [gstep, hl]
      rw [hg]
      have hcq : (C.loc q).cnt = c := by rw [hl]
      have hnb : ¬ beyond (C.loc q).pc i := by rw [hl]; exact lt_irrefl i
      have hid : lastId (some (⟨[(q, c)], k⟩ : Val P)) = some (q, c) := by simp [lastId]
      have hbj : beyond (nextIt k i v) i := by
        unfold nextIt; split_ifs
        · change i < i + 1; omega
        · change i < k; omega
      refine hI.write_step h1 hcq hR' (by rw [h2]) hnb (by rw [hl]; exact hb) hbj hid
        (fun i' h3 h4 => h1.mem.contig k i' hk h3 (by omega)) (fun _ => hk)
        (by have := hI.ph_ge k hk; omega)
        (fun h3 => absurd h3 (h1.mem.contig k (i + 1) hk (by omega) (by omega))) ?_
      simp only [PI2] at hpi2
      unfold nextIt; split_ifs with h3
      · simp only [PI2]
        refine ⟨?_, fun j h4 h5 => ?_⟩
        · rw [hR']; exact hpi2.1.write' hm hcq hnb hid
        · rw [gwrite_bt_of_ne_none hk, gwrite_wt]
          have := (hI.bt_pos k hk).2; have := hwl k
          split_ifs with h6
          · omega
          · exact hpi2.2 j h4 (by omega)
      · simp [PI2]
    | @fin k w =>
      simp only [PI1] at hpi1
      obtain ⟨hk, hw, hlw⟩ := hpi1
      simp only [PI2] at hpi2
      have hg : gstep G C (.tau q) =
          gwrite G (Rg C) (q, c) (k + 1) true (some (G.psc q)) := by simp [gstep, hl]
      rw [hg]
      have hcq : (C.loc q).cnt = c := by rw [hl]
      have hnb : ¬ beyond (C.loc q).pc (k + 1) := by
        rw [hl]; change ¬ k + 1 < k; omega
      refine hI.write_step (pc' := .done (.inl (k + 1, 0))) h1 hcq hR' (by rw [h2]) hnb
        (by rw [hl]; exact hb) trivial hlw
        (fun i' h3 h4 => h1.mem.contig k i' (hk (by omega)) h3 (by omega))
        (fun h3 => by omega) hpi2.ph ?_ ?_
      · intro _
        rw [hR', gwrite_rsc_self]
        exact hpi2.write' hm hcq hnb hlw
      · simp only [PI2]; intro j h3 h4; omega

theorem inv2_of_run {α : List (Label P TS)} {C : ACfg P} (h : (alg4 (P := P)).run α = some C) :
    Inv2 C (ghostOf α) := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run, Impl.runFrom_nil, Option.some.injEq] at h
    subst h; exact inv2_init
  | append_singleton α ℓ ih =>
    obtain ⟨C₀, h₀, hs⟩ := run_append_singleton h
    rw [ghostOf_append h₀ hs]
    exact (ih h₀).step (inv1_of_run h₀) hs

end Cslib.SharedMemory.Timestamp.Alg4
