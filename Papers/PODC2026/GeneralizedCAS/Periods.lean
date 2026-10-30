import Papers.PODC2026.GeneralizedCAS.Facts

/-!
# Algorithm 1: the iterations of an operation (setting of Appendix B.2)

We fix a process `p` that executes line 3 of an operation `o` at time `n3`; `t` is the timestamp
it obtains and `k0` the index of `o` among the operations of `p`.

* `InOp m`: time `m` is inside `o` after line 3.
* `IsEnd i E`: at time `E`, `p` executes line 13 or line 15 of the `i`-th iteration of the loop
  in `o` (the end of a *complete, non-terminal* iteration, Definition B.2.1). Its start (line 5) is
  `start E = lt p l5` at time `E`.
* `SO`: the set `S(o)` of Definition B.2.3 (timestamps `≤ t` of operations pending at `n3`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Podc.GeneralizedCAS

open Cslib.SharedMemory

variable {T : ObjSpec} [LinearOrder T.Op] {P : Type} [DecidableEq P]
variable {cellInit : ℕ → CellVal T.Resp}

namespace Trace

variable (tr : Trace T P cellInit)

/-- Inside an operation (after line 3), a process stays pending with the same timestamp. -/
theorem stay {p : P} {a b : ℕ} (hab : a ≤ b) (hb : b ≤ tr.N) (hp : (tr.C a).pend p ≠ none)
    (h3 : ((tr.C a).loc p).pc.Past3) (hk : (tr.G b).k p = (tr.G a).k p) :
    (tr.C b).pend p ≠ none ∧ ((tr.C b).loc p).pc.Past3 ∧ ((tr.C b).loc p).t = ((tr.C a).loc p).t ∧
      ((tr.C b).loc p).ptr = ((tr.C a).loc p).ptr := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨hp, h3, rfl, rfl⟩
  | succ b hab ih =>
    have hkb : (tr.G b).k p = (tr.G a).k p :=
      le_antisymm (hk ▸ tr.k_mono (Nat.le_succ b) hb) (tr.k_mono hab (by omega))
    obtain ⟨i1, i2, i3, i4⟩ := ih (by omega) hkb
    by_cases hq : (tr.lbl b).proc = p
    · have hs := tr.stepC b (by omega)
      cases hl : tr.lbl b with
      | inv q o =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        exact absurd (step_inv_eff cellInit hs).1 i1
      | ret q r =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        exfalso
        have : (tr.G (b + 1)).k q = (tr.G b).k q + 1 := by
          rw [tr.stepG b (by omega), hl]; simp [augStep]
        omega
      | tau q =>
        rw [hl] at hq; simp only [Label.proc] at hq; subst hq
        obtain ⟨-, hmem, hpend, -, hloc⟩ := tr.step_tau (by omega) hl
        rw [hloc, hpend, Function.update_self]
        refine ⟨i1, ?_, ?_, ?_⟩
        · cases hpc : ((tr.C b).loc q).pc <;> simp [hpc, PC.Past3] at i2 ⊢ <;> simp [effect, hpc]
          all_goals first
            | (rcases pc5_cases ((tr.C b).loc q) (tr.C b).M with h | h | ⟨r, h⟩ <;> simp [h])
            | (split_ifs <;> simp)
            | exact absurd hpc (hmem _)
        · rw [← i3]
          cases hpc : ((tr.C b).loc q).pc <;> simp [hpc, PC.Past3] at i2 ⊢ <;> simp [effect, hpc]
          all_goals first
            | (rcases pc5_cases ((tr.C b).loc q) (tr.C b).M with h | h | ⟨r, h⟩ <;> simp [h])
            | (split_ifs <;> simp)
            | exact absurd hpc (hmem _)
        · rw [← i4]
          cases hpc : ((tr.C b).loc q).pc <;> simp [hpc, PC.Past3] at i2 ⊢ <;> simp [effect, hpc]
          all_goals first
            | (rcases pc5_cases ((tr.C b).loc q) (tr.C b).M with h | h | ⟨r, h⟩ <;> simp [h])
            | (split_ifs <;> simp)
            | exact absurd hpc (hmem _)
    · obtain ⟨e1, e2, -⟩ := tr.step_other (by omega) hq
      rw [e1, e2]; exact ⟨i1, i2, i3, i4⟩

open Classical in
/-- One step of the iteration counter inside an operation. -/
theorem it_step {p : P} {m : ℕ} (hm : m < tr.N) (hp : (tr.C m).pend p ≠ none)
    (hk : (tr.G (m + 1)).k p = (tr.G m).k p) :
    (tr.G (m + 1)).it p = (tr.G m).it p + (if tr.lbl m = .tau p ∧
      (((tr.C m).loc p).pc = .l13 ∨ ((tr.C m).loc p).pc = .l15) then 1 else 0) := by
  by_cases hq : (tr.lbl m).proc = p
  · have hs := tr.stepC m hm
    cases hl : tr.lbl m with
    | inv q o =>
      rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
      exact absurd (step_inv_eff cellInit hs).1 hp
    | ret q r =>
      rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
      exfalso
      have : (tr.G (m + 1)).k q = (tr.G m).k q + 1 := by
        rw [tr.stepG m hm, hl]; simp [augStep]
      omega
    | tau q =>
      rw [hl] at hq; simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, hit⟩ := tr.step_tau_ghost hm hl
      rw [hit]; split_ifs <;> simp_all
  · obtain ⟨-, -, -, e4, -⟩ := tr.step_other hm hq
    rw [e4]
    have : ¬ (tr.lbl m = .tau p) := fun h => hq (by rw [h]; rfl)
    simp [this]

/-- `Q τ m`: at time `m`, the operation with timestamp `τ` is done and not stored in `A`. -/
def Q (τ m : ℕ) : Prop := Done (tr.C m) (tr.G m) τ ∧ (tr.C m).M.A.time ≠ τ

/-- A *rise* of `Q τ` at time `m`: the step at time `m` makes `τ` "done and not in `A`". Every
useful period (Definition B.2.4) contains a rise for some operation of `S(o)`. -/
def RE (τ m : ℕ) : Prop := m < tr.N ∧ ¬ tr.Q τ m ∧ tr.Q τ (m + 1)

theorem re_of {τ a b : ℕ} (hab : a ≤ b) (hb : b ≤ tr.N) (ha : ¬ tr.Q τ a) (hQ : tr.Q τ b) :
    ∃ m, a ≤ m ∧ m < b ∧ tr.RE τ m := by
  obtain ⟨m, h1, h2, h3, h4⟩ := Trace.exists_rise (Q := tr.Q τ) hab ha hQ
  exact ⟨m, h1, h2, by omega, h3, h4⟩

end Trace

/-- The setting of Appendix B.2: `p` executes line 3 of an operation at time `n3`. -/
structure OpStart (tr : Trace T P cellInit) (p : P) (n3 : ℕ) : Prop where
  lt : n3 < tr.N
  lbl : tr.lbl n3 = .tau p
  pc : ((tr.C n3).loc p).pc = .l3

namespace OpStart

variable {tr : Trace T P cellInit} {p : P} {n3 : ℕ} (h : OpStart tr p n3)

/-- The timestamp `t(o)`. -/
def t (_h : OpStart tr p n3) : ℕ := (tr.C n3).M.cnt

/-- The index of the operation. -/
def k0 (_h : OpStart tr p n3) : ℕ := (tr.G n3).k p

/-- Time `m` is inside the operation, after line 3. -/
def InOp (m : ℕ) : Prop := n3 < m ∧ m ≤ tr.N ∧ (tr.G m).k p = h.k0

/-- At time `E`, `p` ends the `i`-th iteration of the loop in the operation (line 13 or 15). -/
def IsEnd (i E : ℕ) : Prop :=
  h.InOp E ∧ E < tr.N ∧ tr.lbl E = .tau p ∧
    (((tr.C E).loc p).pc = .l13 ∨ ((tr.C E).loc p).pc = .l15) ∧ (tr.G E).it p = i

/-- The start (line 5) of the iteration that ends at time `E`. -/
def start (_h : OpStart tr p n3) (E : ℕ) : ℕ := (tr.G E).lt p .l5

open Classical in
/-- **Definition B.2.3**: `S(o)`, the timestamps `≤ t(o)` of the operations pending when `p`
executes line 3 (including `o` itself). -/
noncomputable def SO (h : OpStart tr p n3) : Finset ℕ :=
  (Finset.Icc 1 h.t).filter fun τ => τ = h.t ∨ ∃ q o, (tr.G n3).ts τ = some (q, (tr.G n3).k q, o)

include h

theorem pend_n3 : (tr.C n3).pend p ≠ none := (tr.step_tau h.lt h.lbl).1

theorem after3 : (tr.C (n3 + 1)).pend p ≠ none ∧ ((tr.C (n3 + 1)).loc p).pc = .l4 ∧
    ((tr.C (n3 + 1)).loc p).t = h.t ∧ (tr.G (n3 + 1)).k p = h.k0 ∧ (tr.G (n3 + 1)).it p = 0 := by
  obtain ⟨hp, -, hpend, -, hloc⟩ := tr.step_tau h.lt h.lbl
  obtain ⟨-, hk, hit⟩ := tr.step_tau_ghost h.lt h.lbl
  have hit0 : (tr.G n3).it p = 0 := by
    have := (tr.inv2 h.lt.le).ns p hp; rw [h.pc] at this; exact this.2
  refine ⟨by rw [hpend]; exact hp, by simp [hloc, effect, h.pc], by simp [hloc, effect, h.pc, OpStart.t],
    hk, ?_⟩
  rw [hit, h.pc]; simpa using hit0

theorem inOp {m : ℕ} (hm : h.InOp m) :
    (tr.C m).pend p ≠ none ∧ ((tr.C m).loc p).pc.Past3 ∧ ((tr.C m).loc p).t = h.t ∧
      ((tr.C m).loc p).me = ((tr.C (n3 + 1)).loc p).me := by
  obtain ⟨a1, a2, a3, a4, -⟩ := h.after3
  obtain ⟨b1, b2, b3, b4⟩ := tr.stay (a := n3 + 1) (b := m) (by have := hm.1; omega) hm.2.1 a1
    (by rw [a2]; trivial) (by rw [hm.2.2, a4])
  exact ⟨b1, b2, b3.trans a3, by simp [Loc.me, b4]⟩

theorem k_eq {m m' : ℕ} (hm : h.InOp m) (h1 : n3 ≤ m') (h2 : m' ≤ m) : (tr.G m').k p = h.k0 :=
  le_antisymm (hm.2.2 ▸ tr.k_mono h2 hm.2.1) (tr.k_mono h1 (h2.trans hm.2.1))

theorem inOp_of_le {m m' : ℕ} (hm : h.InOp m) (h1 : n3 < m') (h2 : m' ≤ m) : h.InOp m' :=
  ⟨h1, h2.trans hm.2.1, h.k_eq hm h1.le h2⟩

theorem it_mono {a b : ℕ} (ha : h.InOp a) (hab : a ≤ b) (hb : h.InOp b) :
    (tr.G a).it p ≤ (tr.G b).it p := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    have hb' : h.InOp b := h.inOp_of_le hb (by have := ha.1; omega) (by omega)
    have := tr.it_step (m := b) (by have := hb.2.1; omega) (h.inOp hb').1
      (by rw [hb.2.2, hb'.2.2])
    rw [this]; exact (ih hb').trans (by omega)

theorem it_end {i E : ℕ} (hE : h.IsEnd i E) (h1 : E + 1 ≤ tr.N) : h.InOp (E + 1) ∧
    (tr.G (E + 1)).it p = i + 1 := by
  obtain ⟨hin, hlt, hl, hpc, hit⟩ := hE
  obtain ⟨-, hk, hit'⟩ := tr.step_tau_ghost hlt hl
  refine ⟨⟨by have := hin.1; omega, h1, by rw [hk, hin.2.2]⟩, ?_⟩
  rw [hit', if_pos hpc, hit]

theorem end_lt {i i' E E' : ℕ} (hE : h.IsEnd i E) (hE' : h.IsEnd i' E') (hii : i < i') : E < E' := by
  by_contra hc
  rcases eq_or_lt_of_le (not_lt.1 hc) with he | he
  · subst he; have := hE.2.2.2.2; rw [hE'.2.2.2.2] at this; omega
  have h1 := h.it_end hE' (by have := hE'.2.1; omega)
  have := h.it_mono h1.1 (by omega) hE.1
  rw [h1.2, hE.2.2.2.2] at this; omega

theorem start_spec {i E : ℕ} (hE : h.IsEnd i E) :
    n3 < h.start E ∧ h.start E < E ∧ h.InOp (h.start E) ∧ (tr.G (h.start E)).it p = i ∧
    tr.lbl (h.start E) = .tau p ∧ ((tr.C (h.start E)).loc p).pc = .l5 := by
  obtain ⟨hin, hlt, hl, hpc, hit⟩ := hE
  have hIT := tr.iterTimes hlt.le p
  obtain ⟨a1, a2, a3, a4, a5, -⟩ := hIT.a (by rcases hpc with h' | h' <;> simp [h', PC.Loop])
    (by rcases hpc with h' | h' <;> simp [h'])
  have hgt : n3 < h.start E := by
    by_contra hc
    have hle : h.start E ≤ n3 := by omega
    have hne : h.start E ≠ n3 := by
      intro he; rw [OpStart.start] at he; rw [he, h.pc] at a3; cases a3
    obtain ⟨-, b2, -, -⟩ := tr.stay (p := p) (a := h.start E) (b := n3) hle h.lt.le
      (tr.step_tau (by omega) a2).1 (by simp only [OpStart.start]; rw [a3]; trivial)
      (by simp only [OpStart.start]; rw [a5, hin.2.2]; rfl)
    rw [h.pc] at b2; exact b2
  have a1' : h.start E < E := a1
  refine ⟨hgt, a1, ⟨hgt, by omega, by simp only [OpStart.start]; rw [a5, hin.2.2]⟩, ?_, a2, a3⟩
  simp only [OpStart.start]; rw [a4, hit]

theorem start_gt {i E E' : ℕ} (hE : h.IsEnd i E) (hE' : h.IsEnd (i + 1) E') : E < h.start E' := by
  obtain ⟨-, -, hin', hit', -⟩ := h.start_spec hE'
  by_contra hc
  have := h.it_mono hin' (by omega) hE.1
  rw [hE.2.2.2.2, hit'] at this
  omega

theorem end_exists {m : ℕ} (hm : h.InOp m) {i : ℕ} (hi : i < (tr.G m).it p) :
    ∃ E, E < m ∧ h.IsEnd i E := by
  obtain ⟨m0, hm0⟩ : ∃ m0, m = n3 + 1 + m0 := ⟨m - (n3 + 1), by have := hm.1; omega⟩
  subst hm0
  induction m0 generalizing i with
  | zero => rw [h.after3.2.2.2.2] at hi; omega
  | succ m0 ih =>
    have e : n3 + 1 + (m0 + 1) = n3 + 1 + m0 + 1 := by omega
    rw [e] at hm hi ⊢
    have hm' : h.InOp (n3 + 1 + m0) := h.inOp_of_le hm (by omega) (by omega)
    have := tr.it_step (m := n3 + 1 + m0) (by have := hm.2.1; omega) (h.inOp hm').1
      (by rw [hm.2.2, hm'.2.2])
    rw [this] at hi
    by_cases hi' : i < (tr.G (n3 + 1 + m0)).it p
    · obtain ⟨E, hE1, hE2⟩ := ih hm' hi'; exact ⟨E, by omega, hE2⟩
    · split_ifs at hi with hc
      · refine ⟨n3 + 1 + m0, by omega, hm', by have := hm.2.1; omega, hc.1, hc.2, by omega⟩
      · omega

theorem end_lt_start {i i' E E' : ℕ} (hE : h.IsEnd i E) (hE' : h.IsEnd i' E') (hii : i < i') :
    E < h.start E' := by
  obtain ⟨-, -, hin', hit', -⟩ := h.start_spec hE'
  by_contra hc
  have := h.it_mono hin' (by omega) hE.1
  rw [hE.2.2.2.2, hit'] at this
  omega

theorem end_unique {i E E' : ℕ} (hE : h.IsEnd i E) (hE' : h.IsEnd i E') : E = E' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hl | hl
  · have h1 := h.it_end hE (by have := hE'.2.1; omega)
    have := h.it_mono h1.1 (by omega) hE'.1
    rw [h1.2, hE'.2.2.2.2] at this; omega
  · have h1 := h.it_end hE' (by have := hE.2.1; omega)
    have := h.it_mono h1.1 (by omega) hE.1
    rw [h1.2, hE.2.2.2.2] at this; omega

/-! ### `S(o)` and the old operations -/

theorem t_pos : 1 ≤ h.t := (tr.inv h.lt.le).cnt_pos

theorem t_mem : h.t ∈ h.SO := by simp [OpStart.SO, h.t_pos]

theorem mem_SO {τ : ℕ} (hτ : τ ∈ h.SO) : 1 ≤ τ ∧ τ ≤ h.t := by
  simp only [OpStart.SO, Finset.mem_filter, Finset.mem_Icc] at hτ; exact hτ.1

/-- An operation with timestamp `≤ t(o)` that is not in `S(o)` was complete when `p` executed
line 3 (Proposition B.2.5), or it is `Noop`. -/
theorem old_cases {τ : ℕ} (h1 : τ ≤ h.t) (h2 : τ ∉ h.SO) :
    τ = 0 ∨ ∃ q k o, (tr.G n3).ts τ = some (q, k, o) ∧ k < (tr.G n3).k q := by
  rcases Nat.eq_zero_or_pos τ with h0 | h0
  · exact Or.inl h0
  right
  have hne : τ ≠ h.t := fun e => h2 (e ▸ h.t_mem)
  have hlt : τ < (tr.C n3).M.cnt := lt_of_le_of_ne h1 hne
  obtain ⟨⟨q, k, o⟩, hx⟩ := Option.ne_none_iff_exists'.mp ((tr.inv h.lt.le).ts_range τ |>.2 ⟨h0, hlt⟩)
  refine ⟨q, k, o, hx, lt_of_le_of_ne ((tr.inv h.lt.le).ts_k τ q k o hx) fun e => h2 ?_⟩
  subst e
  simp only [OpStart.SO, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨h0, h1⟩, Or.inr ⟨q, o, hx⟩⟩

/-- Old operations are done. -/
theorem old_done {τ : ℕ} (h1 : τ ≤ h.t) (h2 : τ ∉ h.SO) {m : ℕ} (hm1 : n3 ≤ m) (hm2 : m ≤ tr.N) :
    Done (tr.C m) (tr.G m) τ := by
  rcases h.old_cases h1 h2 with h0 | ⟨q, k, o, hx, hk⟩
  · exact Or.inl h0
  · exact tr.done_mono hm1 hm2 (done_of_completed (tr.inv h.lt.le) hx hk)

/-- Old operations never enter `A` again (they are complete; `Noop` is never written). -/
theorem old_out {τ : ℕ} (h1 : τ ≤ h.t) (h2 : τ ∉ h.SO) {a b : ℕ} (ha : n3 ≤ a) (hab : a ≤ b)
    (hb : b ≤ tr.N) (h0 : (tr.C a).M.A.time ≠ τ) : (tr.C b).M.A.time ≠ τ := by
  induction b, hab using Nat.le_induction with
  | base => exact h0
  | succ m ham ih =>
    intro heq
    have hne := ih (by omega)
    have hm : m < tr.N := by omega
    have hch : (tr.C (m + 1)).M.A ≠ (tr.C m).M.A := fun e => hne (by rw [← e]; exact heq)
    obtain ⟨q, hl, hA, hcase⟩ := tr.A_change hm hch
    obtain ⟨hp, -⟩ := tr.step_tau hm hl
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hp
    have hI := tr.inv hm.le
    have hcur := hI.cur q o ho (by rcases hcase with ⟨hc, -⟩ | ⟨hc, -⟩ <;> simp [hc, PC.Past3])
    have htq : ((tr.C m).loc q).t = τ := by rw [← heq, hA]; rfl
    rw [htq] at hcur
    rcases h.old_cases h1 h2 with h0 | ⟨q', k', o', hx, hk⟩
    · have := (hI.ts_range τ).1 (by simp [hcur]); omega
    · rw [tr.ts_mono (by omega) hm.le hx] at hcur
      simp only [Option.some.injEq, Prod.mk.injEq] at hcur
      obtain ⟨rfl, rfl, -⟩ := hcur
      have := tr.k_mono (q := q') (show n3 ≤ m by omega) hm.le
      omega

/-! ### The iteration data -/

theorem endPast {i E : ℕ} (hE : h.IsEnd i E) :
    ((tr.C E).loc p).pc.Loop ∧ ((tr.C E).loc p).pc ≠ .l5 ∧ ((tr.C E).loc p).pc.HasSnap ∧
    ((tr.C E).loc p).pc.Copied ∧ ((tr.C E).loc p).pc.HasAnn := by
  rcases hE.2.2.2.1 with hpc | hpc <;> simp [hpc, PC.Loop, PC.HasSnap, PC.Copied, PC.HasAnn]

/-- **Lemmas B.2.6, B.2.7**: from line 8 of a non-first iteration on, every operation in `A` with
timestamp `≤ t(o)` is in `S(o)`; right after line 8, `A` holds such an operation. -/
theorem A_SO {i E₀ E₁ : ℕ} (h0 : h.IsEnd i E₀) (h1 : h.IsEnd (i + 1) E₁) :
    (∀ m, (tr.G E₁).lt p .l8 < m → m ≤ tr.N → (tr.C m).M.A.time ≤ h.t →
      (tr.C m).M.A.time ∈ h.SO) ∧ (tr.C ((tr.G E₁).lt p .l8 + 1)).M.A.time ≤ h.t := by
  have hN0 := h0.2.1
  have hIT0 := tr.iterTimes hN0.le p
  obtain ⟨hl0, hne0, hs0, hc0, ha0⟩ := h.endPast h0
  obtain ⟨-, -, -, -, -, -⟩ := hIT0.a hl0 hne0
  obtain ⟨e1, e2, e3, e4, e5⟩ := hIT0.e ha0
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hIT0.f h0.2.2.2.1
  obtain ⟨d1, -, -, -, -⟩ := hIT0.d (Or.inr ha0)
  obtain ⟨c1, -, -, -, -⟩ := hIT0.c hc0
  obtain ⟨b1, -, -, -, -⟩ := hIT0.b hs0
  obtain ⟨g1, -, -, -, -, -⟩ := h.start_spec h0
  have hstart : h.start E₀ = (tr.G E₀).lt p .l5 := rfl
  -- old operations are not in `A` right after `E₀`
  have key : ∀ τ, τ ≤ h.t → τ ∉ h.SO → (tr.C (E₀ + 1)).M.A.time ≠ τ := by
    intro τ hτt hτS
    set ann := ((tr.C E₀).loc p).ann with hann
    by_cases hτ : τ = ann.time
    · -- the operation `ann` is done, so `p` executed line 15 at `E₀`
      have hT10 : (tr.G E₀).lt p .l10 < tr.N := by omega
      have hI10 := tr.inv hT10.le
      have hp10 : (tr.C ((tr.G E₀).lt p .l10)).pend p ≠ none := (tr.step_tau hT10 f3).1
      have hd := h.old_done hτt hτS (m := (tr.G E₀).lt p .l10) (by omega) hT10.le
      have hcell : (tr.C ((tr.G E₀).lt p .l10)).M.cell ann.ptr ≠ ⟨ann.time, .null⟩ := by
        rw [← f5]
        by_cases hz : ((tr.C ((tr.G E₀).lt p .l10)).loc p).ann.time = 0
        · rw [hI10.ann_zero p hp10 (by simp [f4, PC.HasAnn]) hz, hI10.dummy]; simp
        · obtain ⟨q', k', o', x1, -, -, x4⟩ := hI10.ann_pos p hp10 (by simp [f4, PC.HasAnn]) hz
          rw [x4]
          have := hd.cell_ne (by rw [hτ, ← f5]; exact hz) (by rw [hτ, ← f5]; exact x1)
          rwa [hτ, ← f5] at this
      have hpc15 : ((tr.C E₀).loc p).pc = .l15 := by
        rcases h0.2.2.2.1 with hpc | hpc
        · exact absurd (f6.2 hpc) hcell
        · exact hpc
      obtain ⟨-, -, -, hM, -⟩ := tr.step_tau hN0 h0.2.2.1
      have hA : (tr.C (E₀ + 1)).M.A = if (tr.C E₀).M.A = ann then ((tr.C E₀).loc p).mine
          else (tr.C E₀).M.A := by rw [hM]; simp [effect, hpc15, hann]
      have ht := (h.inOp h0.1).2.2.1
      have hτne : τ ≠ h.t := fun e => hτS (e ▸ h.t_mem)
      rw [hA]; split_ifs with he
      · simp [Loc.mine, ht]; exact Ne.symm hτne
      · intro heq
        exact he (A_eq_ann (tr.inv hN0.le) (h.inOp h0.1).1 ha0 (heq.trans hτ))
    · refine h.old_out hτt hτS (a := (tr.G E₀).lt p .l9) (by omega) (by omega) (by omega) ?_
      rw [← e5]; exact Ne.symm hτ
  constructor
  · intro m hm1 hm2 hm3
    have hlt : E₀ < h.start E₁ := h.start_gt h0 h1
    have hIT1 := tr.iterTimes h1.2.1.le p
    obtain ⟨hl1, hne1, hs1, hc1, ha1⟩ := h.endPast h1
    obtain ⟨x1, -, -, -, -⟩ := hIT1.d (Or.inr ha1)
    obtain ⟨y1, -, -, -, -⟩ := hIT1.c hc1
    obtain ⟨z1, -, -, -, -⟩ := hIT1.b hs1
    have hstart1 : h.start E₁ = (tr.G E₁).lt p .l5 := rfl
    by_contra hS
    exact h.old_out hm3 hS (a := E₀ + 1) (by have := h0.1.1; omega) (by omega) hm2
      (key _ hm3 hS) rfl
  · have hIT1 := tr.iterTimes h1.2.1.le p
    obtain ⟨hl1, hne1, hs1, hc1, ha1⟩ := h.endPast h1
    obtain ⟨x1, x2, x3, x4, x5⟩ := hIT1.d (Or.inr ha1)
    have hT8 : (tr.G E₁).lt p .l8 < tr.N := by have := h1.2.1; omega
    obtain ⟨-, -, -, hM, -⟩ := tr.step_tau hT8 x3
    have ht := (h.inOp h1.1).2.2.1
    have hA : (tr.C ((tr.G E₁).lt p .l8 + 1)).M.A =
        if ((tr.C E₁).loc p).mine < (tr.C ((tr.G E₁).lt p .l8)).M.A then ((tr.C E₁).loc p).mine
        else (tr.C ((tr.G E₁).lt p .l8)).M.A := by rw [hM]; simp [effect, x4, x5]
    rw [hA]; split_ifs with hc
    · simp [Loc.mine, ht]
    · have := AVal.time_le_of_not_lt hc; simpa [Loc.mine, ht] using this

/-- A process executing line 15 removes a done operation from `A` (if it is still there). -/
theorem l15_done {m : ℕ} (hm : m < tr.N) {q : P} (hl : tr.lbl m = .tau q)
    (hpc : ((tr.C m).loc q).pc = .l15) : Done (tr.C m) (tr.G m) ((tr.C m).loc q).ann.time := by
  have hIT := tr.iterTimes hm.le q
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hIT.f (Or.inr hpc)
  have hT : (tr.G m).lt q .l10 < tr.N := by omega
  have hp := (tr.step_tau hT f3).1
  have hd := done_of_ann_cell (tr.inv hT.le) hp (by simp [f4, PC.HasAnn])
    (by rw [f5]; intro hc; have := f6.1 hc; rw [hpc] at this; cases this)
  rw [f5] at hd
  exact tr.done_mono (by omega) hm.le hd

/-- **Proposition B.2.8**: if, after line 8 of a non-first iteration, `A` holds an operation not in
`S(o)`, then some operation of `S(o)` rose (was done and removed from `A`) in between. -/
theorem re_not_SO {i E₀ E₁ : ℕ} (h0 : h.IsEnd i E₀) (h1 : h.IsEnd (i + 1) E₁) {m0 : ℕ}
    (hm0 : (tr.G E₁).lt p .l8 < m0) (hN : m0 ≤ tr.N) (hS : (tr.C m0).M.A.time ∉ h.SO) :
    ∃ τ ∈ h.SO, ∃ m, (tr.G E₁).lt p .l8 < m ∧ m < m0 ∧ tr.RE τ m := by
  obtain ⟨hA1, hA2⟩ := h.A_SO h0 h1
  have hst : (tr.C ((tr.G E₁).lt p .l8 + 1)).M.A.time ∈ h.SO := hA1 _ (by omega) (by omega) hA2
  obtain ⟨m1, hm1, hm1', hP1, hP2⟩ := Trace.exists_rise
    (Q := fun m => (tr.C m).M.A.time ∉ h.SO) (show (tr.G E₁).lt p .l8 + 1 ≤ m0 by omega)
    (by simpa using hst) hS
  simp only [not_not] at hP1
  have hm1N : m1 < tr.N := by omega
  have hch : (tr.C (m1 + 1)).M.A ≠ (tr.C m1).M.A := fun e => hP2 (by rw [e]; exact hP1)
  obtain ⟨q, hl, hA, hcase⟩ := tr.A_change hm1N hch
  rcases hcase with ⟨hpc, hlt⟩ | ⟨hpc, heq⟩
  · exfalso; apply hP2
    have hle := AVal.time_le_of_lt hlt
    refine hA1 (m1 + 1) (by omega) (by omega) ?_
    rw [hA]; exact le_trans hle (h.mem_SO hP1).2
  · refine ⟨_, hP1, m1, by omega, hm1', hm1N, ?_, ?_⟩
    · intro hQ; exact hQ.2 rfl
    · have hd := h.l15_done hm1N hl hpc
      rw [← heq] at hd
      refine ⟨tr.done_mono (Nat.le_succ m1) (by omega) hd, fun he => hP2 ?_⟩
      rw [he]; exact hP1

/-- After line 15, the announced operation is no longer in `A` (unless it is the own one). -/
theorem A_l15 {m : ℕ} (hm : m < tr.N) {q : P} (hl : tr.lbl m = .tau q)
    (hpc : ((tr.C m).loc q).pc = .l15) (hne : ((tr.C m).loc q).t ≠ ((tr.C m).loc q).ann.time) :
    (tr.C (m + 1)).M.A.time ≠ ((tr.C m).loc q).ann.time := by
  obtain ⟨hp, -, -, hM, -⟩ := tr.step_tau hm hl
  have hA : (tr.C (m + 1)).M.A = if (tr.C m).M.A = ((tr.C m).loc q).ann then ((tr.C m).loc q).mine
      else (tr.C m).M.A := by rw [hM]; simp [effect, hpc]
  rw [hA]; split_ifs with he
  · exact hne
  · intro heq
    exact he (A_eq_ann (tr.inv hm.le) hp (by simp [hpc, PC.HasAnn]) heq)

theorem lt8_le {i E₁ j E : ℕ} (h1 : h.IsEnd (i + 1) E₁) (hjE : h.IsEnd j E) (hj : i + 1 ≤ j) :
    (tr.G E₁).lt p .l8 ≤ (tr.G E).lt p .l8 := by
  rcases eq_or_lt_of_le hj with rfl | hj
  · rw [h.end_unique h1 hjE]
  · have h2 := h.end_lt_start h1 hjE hj
    have hIT1 := tr.iterTimes h1.2.1.le p
    obtain ⟨hl1, hne1, hs1, hc1, ha1⟩ := h.endPast h1
    obtain ⟨-, x2, -⟩ := hIT1.d (Or.inr ha1)
    have hIT := tr.iterTimes hjE.2.1.le p
    obtain ⟨hl, hne, hs, hc, ha⟩ := h.endPast hjE
    obtain ⟨b1, -⟩ := hIT.b hs
    obtain ⟨c1, -⟩ := hIT.c hc
    obtain ⟨d1, -⟩ := hIT.d (Or.inr ha)
    have : h.start E = (tr.G E).lt p .l5 := rfl
    omega

/-- **Proposition B.2.9**: if `p` executes line 15 in an iteration of the period that is followed
by another complete iteration, an operation of `S(o)` rises during the period. -/
theorem useful_l15 {i E₀ E₁ j E E' : ℕ} (h0 : h.IsEnd i E₀) (h1 : h.IsEnd (i + 1) E₁)
    (hjE : h.IsEnd j E) (hj : i + 1 ≤ j) (hpc : ((tr.C E).loc p).pc = .l15)
    (hnext : h.IsEnd (j + 1) E') :
    ∃ τ ∈ h.SO, ∃ m, (tr.G E₁).lt p .l8 < m ∧ m ≤ E ∧ tr.RE τ m := by
  have hEN := hjE.2.1
  have hIT := tr.iterTimes hEN.le p
  obtain ⟨hl, hne, hs, hc, ha⟩ := h.endPast hjE
  obtain ⟨e1, e2, e3, e4, e5⟩ := hIT.e ha
  have h8 := h.lt8_le h1 hjE hj
  have hd := h.l15_done hEN hjE.2.2.1 hpc
  set τ' := ((tr.C E).loc p).ann.time with hτ'
  by_cases hS : τ' ∈ h.SO
  swap
  · obtain ⟨τ, hτ, m, hm1, hm2, hre⟩ := h.re_not_SO h0 h1 (m0 := (tr.G E).lt p .l9)
      (by omega) (by omega) (by rw [← e5]; exact hS)
    exact ⟨τ, hτ, m, hm1, by omega, hre⟩
  have ht := (h.inOp hjE.1).2.2.1
  by_cases hτt : τ' = h.t
  · -- the own operation is done: the next iteration would be terminal
    exfalso
    obtain ⟨u1, u2, u3, u4, u5, u6⟩ := h.start_spec hnext
    have hlt := h.start_gt hjE hnext
    have hITn := tr.iterTimes hnext.2.1.le p
    obtain ⟨hln, hnen, -, -, -⟩ := h.endPast hnext
    obtain ⟨-, -, -, -, -, a6⟩ := hITn.a hln hnen
    have hu := h.inOp u3
    have huN := u3.2.1
    have hdu : Done (tr.C (h.start E')) (tr.G (h.start E')) h.t := by
      rw [← hτt]; exact tr.done_mono (by omega) (by omega) hd
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hu.1
    have := (done_cur_iff (tr.inv (by omega)) ho hu.2.1 (by rw [u6]; simp)).1 (by rw [hu.2.2.1]; exact hdu)
    apply this
    have hn := h.inOp hnext.1
    rw [hu.2.2.1, hu.2.2.2, ← hn.2.2.2, ← hn.2.2.1]
    exact a6
  · have hQ1 : ¬ tr.Q τ' ((tr.G E).lt p .l9) := fun hq => hq.2 (by rw [← e5])
    have hQ2 : tr.Q τ' (E + 1) := ⟨tr.done_mono (by omega) (by omega) hd,
      h.A_l15 hEN hjE.2.2.1 hpc (by rw [ht]; exact Ne.symm hτt)⟩
    obtain ⟨m, hm1, hm2, hre⟩ := tr.re_of (show (tr.G E).lt p .l9 ≤ E + 1 by omega) (by omega) hQ1 hQ2
    exact ⟨τ', hS, m, by omega, by omega, hre⟩

/-- An announced operation that is done fails the test of line 11: the process executes line 15. -/
theorem l15_of_done {j E : ℕ} (hjE : h.IsEnd j E)
    (hd : Done (tr.C ((tr.G E).lt p .l10)) (tr.G ((tr.G E).lt p .l10)) ((tr.C E).loc p).ann.time) :
    ((tr.C E).loc p).pc = .l15 := by
  have hIT := tr.iterTimes hjE.2.1.le p
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hIT.f hjE.2.2.2.1
  have hT : (tr.G E).lt p .l10 < tr.N := by have := hjE.2.1; omega
  have hI := tr.inv hT.le
  have hp := (tr.step_tau hT f3).1
  have hcell : (tr.C ((tr.G E).lt p .l10)).M.cell ((tr.C E).loc p).ann.ptr ≠
      ⟨((tr.C E).loc p).ann.time, .null⟩ := by
    rw [← f5]; rw [← f5] at hd
    by_cases hz : ((tr.C ((tr.G E).lt p .l10)).loc p).ann.time = 0
    · rw [hI.ann_zero p hp (by simp [f4, PC.HasAnn]) hz, hI.dummy]; simp
    · obtain ⟨q', k', o', x1, -, -, x4⟩ := hI.ann_pos p hp (by simp [f4, PC.HasAnn]) hz
      rw [x4]; exact hd.cell_ne hz x1
  rcases hjE.2.2.2.1 with hpc | hpc
  · exact absurd (f6.2 hpc) hcell
  · exact hpc

/-- The common end of Propositions B.2.10 and B.2.11: once an operation `τ'` of `S(o)` that was in
`A` (at time `w`) has been linearized (it is in `S` at time `s`), within the next two complete
iterations an operation of `S(o)` rises. -/
theorem useful_S {i E₀ E₁ j E E' τ' w s : ℕ} (h0 : h.IsEnd i E₀) (h1 : h.IsEnd (i + 1) E₁)
    (hjE : h.IsEnd j E) (hj : i + 1 ≤ j) (hnext : h.IsEnd (j + 1) E') (hτ : τ' ∈ h.SO)
    (hw : (tr.G E₁).lt p .l8 < w) (hwA : (tr.C w).M.A.time = τ') (hws : w ≤ s)
    (hsS : (tr.C s).M.S.time = τ') (hsE : s ≤ h.start E) :
    ∃ τ ∈ h.SO, ∃ m, (tr.G E₁).lt p .l8 < m ∧ m ≤ E ∧ tr.RE τ m := by
  have hEN := hjE.2.1
  have hIT := tr.iterTimes hEN.le p
  obtain ⟨hl, hne, hs, hc, ha⟩ := h.endPast hjE
  obtain ⟨b1, b2, b3, b4, b5⟩ := hIT.b hs
  obtain ⟨c1, c2, c3, c4, c5⟩ := hIT.c hc
  obtain ⟨d1, d2, d3, d4, d5⟩ := hIT.d (Or.inr ha)
  obtain ⟨e1, e2, e3, e4, e5⟩ := hIT.e ha
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hIT.f hjE.2.2.2.1
  have hstart : h.start E = (tr.G E).lt p .l5 := rfl
  have hτ0 : τ' ≠ 0 := by have := (h.mem_SO hτ).1; omega
  -- `τ'` is done after line 7 of the iteration
  have hd7 : Done (tr.C ((tr.G E).lt p .l7 + 1)) (tr.G ((tr.G E).lt p .l7 + 1)) τ' := by
    by_cases h6 : (tr.C ((tr.G E).lt p .l6)).M.S.time = τ'
    · have := tr.done_after_l7 (m := (tr.G E).lt p .l7) (by omega) c3 c4
      rwa [c5, b5, h6] at this
    · obtain ⟨e, he1, he2, he3, he4⟩ := Trace.exists_rise
        (Q := fun m => (tr.C m).M.S.time ≠ τ') (show s ≤ (tr.G E).lt p .l6 by omega)
        (by simpa using hsS) h6
      simp only [not_not] at he3
      have hch : (tr.C (e + 1)).M.S ≠ (tr.C e).M.S := fun x => he4 (by rw [x]; exact he3)
      have := tr.done_of_S_change (m := e) (by omega) hch
      rw [he3] at this
      exact tr.done_mono (by omega) (by omega) this
  by_cases h9 : (tr.C ((tr.G E).lt p .l9)).M.A.time = τ'
  · have hann : ((tr.C E).loc p).ann.time = τ' := by rw [e5]; exact h9
    have hd10 : Done (tr.C ((tr.G E).lt p .l10)) (tr.G ((tr.G E).lt p .l10))
        ((tr.C E).loc p).ann.time := by
      rw [hann]; exact tr.done_mono (by omega) (by omega) hd7
    exact h.useful_l15 h0 h1 hjE hj (h.l15_of_done hjE hd10) hnext
  · have hQ1 : ¬ tr.Q τ' w := fun hq => hq.2 hwA
    have hQ2 : tr.Q τ' ((tr.G E).lt p .l9) := ⟨tr.done_mono (by omega) (by omega) hd7, h9⟩
    obtain ⟨m, hm1, hm2, hre⟩ := tr.re_of (show w ≤ (tr.G E).lt p .l9 by omega) (by omega) hQ1 hQ2
    exact ⟨τ', hτ, m, by omega, by omega, hre⟩


/-- The value of `S` after a successful CAS on line 13. -/
theorem S_l13 {m : ℕ} (hm : m < tr.N) {q : P} (hl : tr.lbl m = .tau q)
    (hpc : ((tr.C m).loc q).pc = .l13) (hS : (tr.C m).M.S = ((tr.C m).loc q).snap) :
    (tr.C (m + 1)).M.S.time = ((tr.C m).loc q).ann.time := by
  obtain ⟨-, -, -, hM, -⟩ := tr.step_tau hm hl
  rw [hM]; simp [effect, hpc, hS, Loc.newS]

/-- **Proposition B.2.10**: a successful CAS on line 13, followed by two complete iterations. -/
theorem useful_succ {i E₀ E₁ j E E₂ E₃ : ℕ} (h0 : h.IsEnd i E₀) (h1 : h.IsEnd (i + 1) E₁)
    (hjE : h.IsEnd j E) (hj : i + 1 ≤ j) (hpc : ((tr.C E).loc p).pc = .l13)
    (hS : (tr.C E).M.S = ((tr.C E).loc p).snap) (hE₂ : h.IsEnd (j + 1) E₂)
    (hE₃ : h.IsEnd (j + 1 + 1) E₃) :
    ∃ τ ∈ h.SO, ∃ m, (tr.G E₁).lt p .l8 < m ∧ m ≤ E₃ ∧ tr.RE τ m := by
  have hEN := hjE.2.1
  have hIT := tr.iterTimes hEN.le p
  obtain ⟨hl, hne, hs, hc, ha⟩ := h.endPast hjE
  obtain ⟨e1, e2, e3, e4, e5⟩ := hIT.e ha
  obtain ⟨f1, -⟩ := hIT.f hjE.2.2.2.1
  have h8 := h.lt8_le h1 hjE hj
  have hEE := h.end_lt hE₂ hE₃ (by omega)
  by_cases hτ : ((tr.C E).loc p).ann.time ∈ h.SO
  · obtain ⟨τ, hτS, m, hm1, hm2, hre⟩ := h.useful_S h0 h1 hE₂ (by omega) hE₃ hτ
      (w := (tr.G E).lt p .l9) (s := E + 1) (by omega) (by rw [← e5]) (by omega)
      (h.S_l13 hEN hjE.2.2.1 hpc hS) (h.start_gt hjE hE₂)
    exact ⟨τ, hτS, m, hm1, by omega, hre⟩
  · obtain ⟨τ, hτS, m, hm1, hm2, hre⟩ := h.re_not_SO h0 h1 (m0 := (tr.G E).lt p .l9)
      (by omega) (by omega) (by rw [← e5]; exact hτ)
    have := h.end_lt hjE hE₂ (by omega)
    exact ⟨τ, hτS, m, hm1, by omega, hre⟩

/-- If `S` differs at the end of an iteration from the value read on line 6, it changed in
between. -/
theorem S_changed {j E : ℕ} (hjE : h.IsEnd j E) (hS : (tr.C E).M.S ≠ ((tr.C E).loc p).snap) :
    ∃ e, (tr.G E).lt p .l6 ≤ e ∧ e < E ∧ (tr.C (e + 1)).M.S ≠ (tr.C e).M.S := by
  have hIT := tr.iterTimes hjE.2.1.le p
  obtain ⟨-, -, hs, -, -⟩ := h.endPast hjE
  obtain ⟨b1, b2, -, -, b5⟩ := hIT.b hs
  obtain ⟨e, he1, he2, he3, he4⟩ := Trace.exists_rise
    (Q := fun m => (tr.C m).M.S ≠ (tr.C ((tr.G E).lt p .l6)).M.S) b2.le (by simp) (by rwa [← b5])
  simp only [not_not] at he3
  exact ⟨e, he1, he2, fun x => he4 (by rw [x, he3])⟩

/-- **Proposition B.2.11**: two consecutive unsuccessful CAS on line 13 (in the second and third
iterations of the period), followed by two complete iterations. -/
theorem useful_fail {i E₀ E₁ j E E₂ E₃ E₄ : ℕ} (h0 : h.IsEnd i E₀) (h1 : h.IsEnd (i + 1) E₁)
    (hjE : h.IsEnd j E) (hj : i + 2 ≤ j) (hS : (tr.C E).M.S ≠ ((tr.C E).loc p).snap)
    (hE₂ : h.IsEnd (j + 1) E₂) (hS₂ : (tr.C E₂).M.S ≠ ((tr.C E₂).loc p).snap)
    (hE₃ : h.IsEnd (j + 1 + 1) E₃) (hE₄ : h.IsEnd (j + 1 + 1 + 1) E₄) :
    ∃ τ ∈ h.SO, ∃ m, (tr.G E₁).lt p .l8 < m ∧ m ≤ E₄ ∧ tr.RE τ m := by
  obtain ⟨e2, he2a, he2b, he2c⟩ := h.S_changed hjE hS
  obtain ⟨e3, he3a, he3b, he3c⟩ := h.S_changed hE₂ hS₂
  -- ordering of the iterations
  have hIT := tr.iterTimes hjE.2.1.le p
  obtain ⟨-, -, hs, -, -⟩ := h.endPast hjE
  obtain ⟨b1, -⟩ := hIT.b hs
  have hIT' := tr.iterTimes hE₂.2.1.le p
  obtain ⟨-, -, hs', -, -⟩ := h.endPast hE₂
  obtain ⟨b1', -⟩ := hIT'.b hs'
  have hst : h.start E = (tr.G E).lt p .l5 := rfl
  have hst' : h.start E₂ = (tr.G E₂).lt p .l5 := rfl
  have hl1 := h.end_lt_start h1 hjE (by omega)
  have hl2 := h.start_gt hjE hE₂
  have hl3 := h.start_gt hE₂ hE₃
  have hl4 := h.end_lt hE₃ hE₄ (by omega)
  have hl5 := h.end_lt hE₂ hE₄ (by omega)
  have hIT1 := tr.iterTimes h1.2.1.le p
  obtain ⟨-, -, -, -, ha1⟩ := h.endPast h1
  obtain ⟨-, d2, -⟩ := hIT1.d (Or.inr ha1)
  -- the process `q` whose CAS on `S` succeeded at `e3`
  have he3N : e3 < tr.N := by have := hE₂.2.1; omega
  obtain ⟨q, hlq, hpcq, hSq, -⟩ := tr.S_change he3N he3c
  have hITq := tr.iterTimes he3N.le q
  obtain ⟨qb1, qb2, -, -, qb5⟩ := hITq.b (by simp [hpcq, PC.HasSnap])
  obtain ⟨qc1, -⟩ := hITq.c (by simp [hpcq, PC.Copied])
  obtain ⟨qd1, -⟩ := hITq.d (Or.inr (by simp [hpcq, PC.HasAnn]))
  obtain ⟨qe1, qe2, -, -, qe5⟩ := hITq.e (by simp [hpcq, PC.HasAnn])
  -- `q` read `S` after `e2` (`S` never takes the same value twice)
  have hq6 : e2 < (tr.G e3).lt q .l6 := by
    by_contra hc
    exact tr.S_ne_of_change (a := (tr.G e3).lt q .l6) (e := e2) (b := e3) (by omega) (by omega)
      he3N.le he2c (by rw [← qb5, hSq])
  by_cases hτ : ((tr.C e3).loc q).ann.time ∈ h.SO
  · obtain ⟨τ, hτS, m, hm1, hm2, hre⟩ := h.useful_S h0 h1 hE₃ (by omega) hE₄ hτ
      (w := (tr.G e3).lt q .l9) (s := e3 + 1) (by omega) (by rw [← qe5]) (by omega)
      (h.S_l13 he3N hlq hpcq hSq) (by omega)
    exact ⟨τ, hτS, m, hm1, by omega, hre⟩
  · obtain ⟨τ, hτS, m, hm1, hm2, hre⟩ := h.re_not_SO h0 h1 (m0 := (tr.G e3).lt q .l9)
      (by omega) (by omega) (by rw [← qe5]; exact hτ)
    exact ⟨τ, hτS, m, hm1, by omega, hre⟩

/-- **Lemma B.2.12**: every non-initial period is useful. A period is formed by five consecutive
complete, non-terminal iterations `i + 1, …, i + 5` (`i ≥ 0`, so the period does not start with the
first iteration); some operation of `S(o)` rises within it. -/
theorem useful {i E₀ E₁ E₂ E₃ E₄ E₅ : ℕ} (h0 : h.IsEnd i E₀) (h1 : h.IsEnd (i + 1) E₁)
    (h2 : h.IsEnd (i + 2) E₂) (h3 : h.IsEnd (i + 3) E₃) (h4 : h.IsEnd (i + 4) E₄)
    (h5 : h.IsEnd (i + 5) E₅) :
    ∃ τ ∈ h.SO, ∃ m, h.start E₁ < m ∧ m ≤ E₅ ∧ tr.RE τ m := by
  have hIT1 := tr.iterTimes h1.2.1.le p
  obtain ⟨hl1, hne1, hs1, hc1, ha1⟩ := h.endPast h1
  obtain ⟨b1, -⟩ := hIT1.b hs1
  obtain ⟨c1, -⟩ := hIT1.c hc1
  obtain ⟨d1, -⟩ := hIT1.d (Or.inr ha1)
  have hst : h.start E₁ = (tr.G E₁).lt p .l5 := rfl
  have l12 := h.end_lt h1 h2 (by omega)
  have l23 := h.end_lt h2 h3 (by omega)
  have l34 := h.end_lt h3 h4 (by omega)
  have l45 := h.end_lt h4 h5 (by omega)
  suffices ∃ τ ∈ h.SO, ∃ m, (tr.G E₁).lt p .l8 < m ∧ m ≤ E₅ ∧ tr.RE τ m by
    obtain ⟨τ, hτ, m, hm1, hm2, hre⟩ := this
    exact ⟨τ, hτ, m, by omega, hm2, hre⟩
  have lift : ∀ E, E ≤ E₅ → (∃ τ ∈ h.SO, ∃ m, (tr.G E₁).lt p .l8 < m ∧ m ≤ E ∧ tr.RE τ m) →
      ∃ τ ∈ h.SO, ∃ m, (tr.G E₁).lt p .l8 < m ∧ m ≤ E₅ ∧ tr.RE τ m := by
    rintro E hE ⟨τ, hτ, m, hm1, hm2, hre⟩; exact ⟨τ, hτ, m, hm1, by omega, hre⟩
  by_cases p1 : ((tr.C E₁).loc p).pc = .l15
  · exact lift _ (by omega) (h.useful_l15 h0 h1 h1 le_rfl p1 h2)
  by_cases p2 : ((tr.C E₂).loc p).pc = .l15
  · exact lift _ (by omega) (h.useful_l15 h0 h1 h2 (by omega) p2 h3)
  by_cases p3 : ((tr.C E₃).loc p).pc = .l15
  · exact lift _ (by omega) (h.useful_l15 h0 h1 h3 (by omega) p3 h4)
  have q1 : ((tr.C E₁).loc p).pc = .l13 := h1.2.2.2.1.resolve_right p1
  have q2 : ((tr.C E₂).loc p).pc = .l13 := h2.2.2.2.1.resolve_right p2
  have q3 : ((tr.C E₃).loc p).pc = .l13 := h3.2.2.2.1.resolve_right p3
  by_cases s1 : (tr.C E₁).M.S = ((tr.C E₁).loc p).snap
  · exact lift _ (by omega) (h.useful_succ h0 h1 h1 le_rfl q1 s1 h2 h3)
  by_cases s2 : (tr.C E₂).M.S = ((tr.C E₂).loc p).snap
  · exact lift _ (by omega) (h.useful_succ h0 h1 h2 (by omega) q2 s2 h3 h4)
  by_cases s3 : (tr.C E₃).M.S = ((tr.C E₃).loc p).snap
  · exact lift _ le_rfl (h.useful_succ h0 h1 h3 (by omega) q3 s3 h4 h5)
  exact lift _ le_rfl (h.useful_fail h0 h1 h2 le_rfl s2 h3 s3 h4 h5)

end OpStart

end Podc.GeneralizedCAS
