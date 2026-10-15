import Papers.PODC2019.AnonymousMutex.Alg2Live

/-!
# Algorithm 2: no inflation of non-atomic views

The read loop of line 3 is not atomic, so the view of a process `p` may count registers of a
process `q` that `q` held at different times. The key lemma (`no_inflation`) shows that this
cannot inflate the count of `q` beyond what `q` held *simultaneously* at some time of the scan,
provided `p` itself owns a register `y₀` during the scan:

* while `q` is in `lock()`'s first two loops (`cas`/`read`), its own registers only grow;
* while `q` erases (line 7), its own registers only shrink;
* after erasing, `q` waits for an all-`⊥` scan (lines 8–10); this scan reads `y₀`, which holds
  `p`'s identifier during the whole scan of `p`, so `q` cannot re-enter before `p`'s scan ends.

This argument is not in the paper (the paper's proof of Theorem 4 is an informal sketch).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ} {P : Type} [DecidableEq P]
  {ids : P → Id} {π : P → Equiv.Perm (Fin m)}

/-- The index of the read loop (`0` for other program counters). -/
def readIdx : PC → ℕ
  | .read i => i
  | _ => 0

/-- The physical registers that `p` has already read in its current scan and that held `a`. -/
def Seen (π : P → Equiv.Perm (Fin m)) (p : P) (v : Fin m → Option Id) (i : ℕ) (a : Id) :
    Finset (Fin m) :=
  (Finset.univ.filter (fun x : Fin m => x.val < i ∧ v x = some a)).map (π p).toEmbedding

omit [DecidableEq P] in
lemma mem_seen {p : P} {v : Fin m → Option Id} {i : ℕ} {a : Id} {y : Fin m} :
    y ∈ Seen π p v i a ↔ ((π p).symm y).val < i ∧ v ((π p).symm y) = some a := by
  simp only [Seen, Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]

omit [DecidableEq P] in
lemma seen_succ (p : P) (v : Fin m → Option Id) (i : ℕ) (hi : i < m) (a : Option Id) (b : Id) :
    Seen π p (Function.update v ⟨i, hi⟩ a) (i + 1) b =
      if a = some b then insert (π p ⟨i, hi⟩) (Seen π p v i b) else Seen π p v i b := by
  ext y
  obtain ⟨x, hx⟩ : ∃ x, x = (π p).symm y := ⟨_, rfl⟩
  have hy : y = π p x := by simp [hx]
  have key : y ∈ Seen π p (Function.update v ⟨i, hi⟩ a) (i + 1) b ↔
      (x = ⟨i, hi⟩ ∧ a = some b) ∨ (x.val < i ∧ v x = some b) := by
    rw [mem_seen, ← hx]
    by_cases hxi : x = ⟨i, hi⟩
    · rw [hxi]; simp
    · rw [Function.update_of_ne hxi]
      have : x.val ≠ i := fun h => hxi (Fin.ext h)
      constructor
      · rintro ⟨h1, h2⟩; exact Or.inr ⟨by omega, h2⟩
      · rintro (⟨h1, -⟩ | ⟨h1, h2⟩)
        · exact absurd h1 hxi
        · exact ⟨by omega, h2⟩
  rw [key]
  split_ifs with ha
  · rw [Finset.mem_insert, mem_seen, ← hx, hy]
    constructor
    · rintro (⟨h, -⟩ | h)
      · exact Or.inl (by rw [h])
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl ⟨(π p).injective h, ha⟩
      · exact Or.inr h
  · rw [mem_seen, ← hx]
    constructor
    · rintro (⟨-, h⟩ | h)
      · exact absurd h ha
      · exact h
    · exact Or.inr

section Scan

variable (hid : Function.Injective ids) (hm : 0 < m) (e : ((alg2 Id m).impl ids π).InfExec)
  (hwf : ∀ t, ClientWF (e.pre t))

/-- The phase invariant of `q` relative to the scan of `p` started at `σ` (`y₀` is a register
owned by `p` during the scan). -/
def Ph (p q : P) (σ t : ℕ) (y₀ : Fin m) : Prop :=
  let C := e.cfg t
  let S := Seen π p (C.loc p).view (readIdx (C.loc p).pc) (ids q)
  (((∃ i, (C.loc q).pc = .cas i) ∨ (∃ i, (C.loc q).pc = .read i)) ∧ S ⊆ own ids C q) ∨
  ((∃ j, (C.loc q).pc = .wr j) ∧ ∃ B : Finset (Fin m), S ⊆ B ∧ own ids C q ⊆ B ∧
    ∃ t'', σ ≤ t'' ∧ t'' ≤ t ∧ B.card ≤ (own ids (e.cfg t'') q).card) ∨
  ((∃ j ab, (C.loc q).pc = .wait j ab ∧ (ab = false ∨ j ≤ ((π q).symm y₀).val)) ∧
    ∃ t'', σ ≤ t'' ∧ t'' ≤ t ∧ S.card ≤ (own ids (e.cfg t'') q).card) ∨
  (((C.loc q).pc = .rem ∨ ∃ j ab, (C.loc q).pc = .wait j ab) ∧ S = ∅)

lemma Ph.bound {p q : P} {σ t : ℕ} {y₀ : Fin m} (h : Ph e p q σ t y₀) (hσ : σ ≤ t) :
    ∃ t'', σ ≤ t'' ∧ t'' ≤ t ∧
      (Seen π p ((e.cfg t).loc p).view (readIdx ((e.cfg t).loc p).pc) (ids q)).card ≤
        (own ids (e.cfg t'') q).card := by
  rcases h with ⟨-, h⟩ | ⟨-, B, hSB, -, t'', h1, h2, h3⟩ | ⟨-, t'', h1, h2, h3⟩ | ⟨-, h⟩
  · exact ⟨t, hσ, le_rfl, Finset.card_le_card h⟩
  · exact ⟨t'', h1, h2, (Finset.card_le_card hSB).trans h3⟩
  · exact ⟨t'', h1, h2, h3⟩
  · exact ⟨t, hσ, le_rfl, by rw [h]; simp⟩

/-- `Ph` only depends on the local states of `p` and `q` and on `q`'s registers. -/
lemma Ph.congr {p q : P} {σ t : ℕ} {y₀ : Fin m} (h : Ph e p q σ t y₀)
    (hp : (e.cfg (t + 1)).loc p = (e.cfg t).loc p) (hq : (e.cfg (t + 1)).loc q = (e.cfg t).loc q)
    (ho : own ids (e.cfg (t + 1)) q = own ids (e.cfg t) q) : Ph e p q σ (t + 1) y₀ := by
  unfold Ph at h ⊢
  simp only [hp, hq, ho]
  rcases h with h | ⟨h1, B, h2, h3, t'', h4, h5, h6⟩ | ⟨h1, t'', h4, h5, h6⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h1, B, h2, h3, t'', h4, by omega, h6⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, t'', h4, by omega, h6⟩))
  · exact Or.inr (Or.inr (Or.inr h))

/-- If `p` has seen nothing of `q`, the phase invariant holds trivially. -/
lemma Ph.of_empty {p q : P} {σ t : ℕ} {y₀ : Fin m} (hσ : σ ≤ t)
    (hS : Seen π p ((e.cfg t).loc p).view (readIdx ((e.cfg t).loc p).pc) (ids q) = ∅)
    (hq : ((e.cfg t).loc q).pc = .rem ∨ Busy ((e.cfg t).loc q).pc) : Ph e p q σ t y₀ := by
  unfold Ph
  simp only [hS]
  cases hpc : ((e.cfg t).loc q).pc with
  | cas i => exact Or.inl ⟨Or.inl ⟨i, rfl⟩, Finset.empty_subset _⟩
  | read i => exact Or.inl ⟨Or.inr ⟨i, rfl⟩, Finset.empty_subset _⟩
  | wr j => exact Or.inr (Or.inl ⟨⟨j, rfl⟩, own ids (e.cfg t) q, Finset.empty_subset _,
      subset_rfl, t, hσ, le_rfl, le_rfl⟩)
  | wait j ab => exact Or.inr (Or.inr (Or.inr ⟨Or.inr ⟨j, ab, rfl⟩, trivial⟩))
  | rem => exact Or.inr (Or.inr (Or.inr ⟨Or.inl rfl, trivial⟩))
  | _ => rw [hpc] at hq; simp [Busy] at hq

lemma Ph.empty_of_rem {p q : P} {σ t : ℕ} {y₀ : Fin m} (h : Ph e p q σ t y₀)
    (hr : ((e.cfg t).loc q).pc = .rem) :
    Seen π p ((e.cfg t).loc p).view (readIdx ((e.cfg t).loc p).pc) (ids q) = ∅ := by
  rcases h with ⟨⟨i, hi⟩ | ⟨i, hi⟩, -⟩ | ⟨⟨j, hj⟩, -⟩ | ⟨⟨j, ab, hj, -⟩, -⟩ | ⟨-, h⟩
  all_goals first | exact h | (rw [hr] at *; simp_all)

lemma Ph.of_casRead {p q : P} {σ t : ℕ} {y₀ : Fin m} (h : Ph e p q σ t y₀)
    (hpc : (∃ i, ((e.cfg t).loc q).pc = .cas i) ∨ (∃ i, ((e.cfg t).loc q).pc = .read i)) :
    Seen π p ((e.cfg t).loc p).view (readIdx ((e.cfg t).loc p).pc) (ids q) ⊆
      own ids (e.cfg t) q := by
  unfold Ph at h
  rcases h with ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h2
  all_goals exfalso
  · obtain ⟨j, hj⟩ := h1
    rcases hpc with ⟨i, hi⟩ | ⟨i, hi⟩ <;> rw [hi] at hj <;> cases hj
  · obtain ⟨j, ab, hj, -⟩ := h1
    rcases hpc with ⟨i, hi⟩ | ⟨i, hi⟩ <;> rw [hi] at hj <;> cases hj
  · rcases h1 with hj | ⟨j, ab, hj⟩ <;>
    rcases hpc with ⟨i, hi⟩ | ⟨i, hi⟩ <;> rw [hi] at hj <;> cases hj

lemma Ph.of_wr {p q : P} {σ t : ℕ} {y₀ : Fin m} (h : Ph e p q σ t y₀) {j : ℕ}
    (hpc : ((e.cfg t).loc q).pc = .wr j) :
    ∃ B : Finset (Fin m),
      Seen π p ((e.cfg t).loc p).view (readIdx ((e.cfg t).loc p).pc) (ids q) ⊆ B ∧
      own ids (e.cfg t) q ⊆ B ∧ ∃ t'', σ ≤ t'' ∧ t'' ≤ t ∧ B.card ≤ (own ids (e.cfg t'') q).card := by
  unfold Ph at h
  rcases h with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exfalso; rcases h1 with ⟨i, hi⟩ | ⟨i, hi⟩ <;> rw [hi] at hpc <;> cases hpc
  · exact h2
  · exfalso; obtain ⟨j', ab, hj, -⟩ := h1; rw [hj] at hpc; cases hpc
  · exfalso; rcases h1 with hj | ⟨j', ab, hj⟩ <;> rw [hj] at hpc <;> cases hpc

lemma Ph.of_wait {p q : P} {σ t : ℕ} {y₀ : Fin m} (h : Ph e p q σ t y₀) {j : ℕ} {ab : Bool}
    (hpc : ((e.cfg t).loc q).pc = .wait j ab) :
    ((ab = false ∨ j ≤ ((π q).symm y₀).val) ∧ ∃ t'', σ ≤ t'' ∧ t'' ≤ t ∧
      (Seen π p ((e.cfg t).loc p).view (readIdx ((e.cfg t).loc p).pc) (ids q)).card ≤
        (own ids (e.cfg t'') q).card) ∨
    Seen π p ((e.cfg t).loc p).view (readIdx ((e.cfg t).loc p).pc) (ids q) = ∅ := by
  unfold Ph at h
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, h2⟩ | ⟨-, h2⟩
  · exfalso; rcases h1 with ⟨i, hi⟩ | ⟨i, hi⟩ <;> rw [hi] at hpc <;> cases hpc
  · exfalso; obtain ⟨j', hj⟩ := h1; rw [hj] at hpc; cases hpc
  · obtain ⟨j', ab', hj, hab⟩ := h1
    rw [hj] at hpc
    simp only [PC.wait.injEq] at hpc
    obtain ⟨rfl, rfl⟩ := hpc
    exact Or.inl ⟨hab, h2⟩
  · exact Or.inr h2

variable {e}

section Steps

variable (hid : Function.Injective ids) (hm : 0 < m) {t₀ : ℕ} (H : Hyp e t₀)
  {p q : P} (hqp : q ≠ p) {σ τ : ℕ} {y₀ : Fin m} (hσ : t₀ ≤ σ)
  (hread : ∀ t, σ ≤ t → t ≤ τ → ∃ i, ((e.cfg t).loc p).pc = .read i)
  (hy : ∀ t, σ ≤ t → t ≤ τ → (e.cfg t).mem () y₀ = some (ids p))
include hid hm H hqp hσ hread hy

/-- Steps of processes other than `p` and `q` preserve the phase invariant. -/
lemma ph_succ_other {t : ℕ} (h1 : σ ≤ t) (h2 : t < τ) (hPh : Ph e p q σ t y₀)
    (hlp : e.lbl t ≠ .tau p) (hlq : e.lbl t ≠ .tau q) : Ph e p q σ (t + 1) y₀ := by
  obtain ⟨i, hpi⟩ := hread t h1 h2.le
  have hpend : (e.cfg t).pend p ≠ none := H.pend_of_busy hid hm (by omega) (by rw [hpi]; trivial)
  have hlocp : (e.cfg (t + 1)).loc p = (e.cfg t).loc p := by
    refine loc_of_not_step e hpend (fun ⟨hproc, hst⟩ => ?_)
    cases hl : e.lbl t with
    | inv r o => rw [hl] at hst; exact hst
    | ret r o => exact H.noret t (by omega) r o hl
    | tau r => rw [hl] at hproc; simp only [Label.proc] at hproc; rw [hproc] at hl; exact hlp hl
  have hown := H.own_frame hid hm hlq
  by_cases hinv : ∃ o, e.lbl t = .inv q o
  · obtain ⟨o, hl⟩ := hinv
    have hstep := e.step_eq t
    rw [hl] at hstep
    obtain ⟨hpq, hC⟩ := SymAlg.impl_step_inv_cases hstep
    have hrem : ((e.cfg t).loc q).pc = .rem := by
      rcases H.phase hid hm (show t₀ ≤ t by omega) q with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · rw [h] at hpq; cases hpq
    have hS := Ph.empty_of_rem e hPh hrem
    refine Ph.of_empty e (by omega) (by rw [hlocp]; exact hS) ?_
    rcases H.phase hid hm (show t₀ ≤ t + 1 by omega) q with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · have hlocq : (e.cfg (t + 1)).loc q = (e.cfg t).loc q := by
      have hpendq : ¬ ((e.lbl t).proc = q ∧ (e.lbl t).IsStep) := by
        rintro ⟨hproc, hst⟩
        cases hl : e.lbl t with
        | inv r o => rw [hl] at hst; exact hst
        | ret r o => exact H.noret t (by omega) r o hl
        | tau r => rw [hl] at hproc; simp only [Label.proc] at hproc; rw [hproc] at hl; exact hlq hl
      by_cases hq : (e.lbl t).proc = q
      · cases hl : e.lbl t with
        | inv r o =>
          rw [hl] at hq; simp only [Label.proc] at hq; subst hq; exact absurd ⟨o, hl⟩ hinv
        | ret r o => exact absurd hl (H.noret t (by omega) r o)
        | tau r => rw [hl] at hq; simp only [Label.proc] at hq; subst hq; exact absurd hl hlq
      · exact (loc_other e hq).1
    exact hPh.congr e hlocp hlocq hown

omit hqp hσ hread hy in
lemma own_empty_of_wait {t : ℕ} {q : P} {j : ℕ} {ab : Bool}
    (h : ((e.cfg t).loc q).pc = .wait j ab) : own ids (e.cfg t) q = ∅ := by
  have := (H.locInv hid hm t q).2
  rw [h] at this; exact this.2

omit hqp hσ hread hy in
lemma own_empty_of_rem {t : ℕ} {q : P} (h : ((e.cfg t).loc q).pc = .rem) :
    own ids (e.cfg t) q = ∅ := by
  have := (H.locInv hid hm t q).2
  rw [h] at this; exact this

omit hid hm H hqp hσ hread hy in
lemma afterRead_pc (s : St Id m) (w : Fin m → Option Id) :
    (∃ j, (afterRead s w).pc = .wr j) ∨ (afterRead s w).pc = .wait 0 true ∨
    (afterRead s w).pc = .retLock ∨ (afterRead s w).pc = .cas 0 := by
  unfold afterRead wrFrom
  split_ifs <;> simp

/-- A read step of `p` preserves the phase invariant of `q`. -/
lemma ph_succ_p {t : ℕ} (h1 : σ ≤ t) (h2 : t < τ) (hPh : Ph e p q σ t y₀)
    (hl : e.lbl t = .tau p) : Ph e p q σ (t + 1) y₀ := by
  obtain ⟨i, hpi⟩ := hread t h1 h2.le
  obtain ⟨i', hpi'⟩ := hread (t + 1) (by omega) h2
  obtain ⟨-, x, f, k, hact, hloc, hmem, -, hother⟩ := tau_step e hl
  have hi : i < m := by have := (H.locInv hid hm t p).2; rw [hpi] at this; exact this.1
  rw [act_read hpi hi] at hact
  simp only [SymAction.rmw.injEq] at hact
  obtain ⟨rfl, rfl, rfl⟩ := hact
  set v := (e.cfg t).mem () (π p ⟨i, hi⟩) with hv
  have hi1 : i + 1 < m := by
    by_contra hc
    rw [hloc] at hpi'
    simp only [hc, ite_false] at hpi'
    rcases afterRead_pc ((e.cfg t).loc p) (Function.update ((e.cfg t).loc p).view ⟨i, hi⟩ v)
      with ⟨j, h⟩ | h | h | h <;> rw [h] at hpi' <;> cases hpi'
  have hlocp : (e.cfg (t + 1)).loc p =
      { (e.cfg t).loc p with view := Function.update ((e.cfg t).loc p).view ⟨i, hi⟩ v,
                             pc := .read (i + 1) } := by
    rw [hloc]; simp [hi1]
  have hlocq := hother q hqp
  have hownq : own ids (e.cfg (t + 1)) q = own ids (e.cfg t) q :=
    H.own_frame hid hm (by rw [hl]; simp [Ne.symm hqp])
  have hSeq : Seen π p ((e.cfg (t + 1)).loc p).view (readIdx ((e.cfg (t + 1)).loc p).pc) (ids q) =
      if v = some (ids q) then insert (π p ⟨i, hi⟩)
        (Seen π p ((e.cfg t).loc p).view (readIdx ((e.cfg t).loc p).pc) (ids q))
      else Seen π p ((e.cfg t).loc p).view (readIdx ((e.cfg t).loc p).pc) (ids q) := by
    rw [hlocp, hpi]
    exact seen_succ p _ i hi v (ids q)
  have hnew : v = some (ids q) → π p ⟨i, hi⟩ ∈ own ids (e.cfg t) q := by
    intro h; simp [own, ← hv, h]
  unfold Ph
  dsimp only
  rw [hSeq, hlocq, hownq]
  rcases hPh with ⟨hpc, hS⟩ | ⟨hpc, B, hSB, hoB, t'', ht1, ht2, ht3⟩ | ⟨hpc, t'', ht1, ht2, ht3⟩ |
    ⟨hpc, hS⟩
  · refine Or.inl ⟨hpc, ?_⟩
    split_ifs with h
    · exact Finset.insert_subset (hnew h) hS
    · exact hS
  · refine Or.inr (Or.inl ⟨hpc, B, ?_, hoB, t'', ht1, by omega, ht3⟩)
    split_ifs with h
    · exact Finset.insert_subset (hoB (hnew h)) hSB
    · exact hSB
  · have hv' : ¬ v = some (ids q) := by
      obtain ⟨j, ab, hj, -⟩ := hpc
      intro h; have := hnew h; rw [own_empty_of_wait hid hm H hj] at this; simp at this
    simp only [hv', ite_false]
    exact Or.inr (Or.inr (Or.inl ⟨hpc, t'', ht1, by omega, ht3⟩))
  · have hv' : ¬ v = some (ids q) := by
      intro h; have := hnew h
      rcases hpc with hr | ⟨j, ab, hj⟩
      · rw [own_empty_of_rem hid hm H hr] at this; simp at this
      · rw [own_empty_of_wait hid hm H hj] at this; simp at this
    simp only [hv', ite_false]
    exact Or.inr (Or.inr (Or.inr ⟨hpc, hS⟩))

/-- A step of `q` preserves the phase invariant of `q`. -/
lemma ph_succ_q {t : ℕ} (h1 : σ ≤ t) (h2 : t < τ) (hPh : Ph e p q σ t y₀)
    (hl : e.lbl t = .tau q) : Ph e p q σ (t + 1) y₀ := by
  obtain ⟨-, x, f, k, hact, hloc, hmem, -, hother⟩ := tau_step e hl
  have hlocp := hother p (Ne.symm hqp)
  have hbusy := H.busy_of_tau hid hm (show t₀ ≤ t by omega) hl
  have hLq := (H.locInv hid hm t q).2
  have hph1 := H.phase hid hm (show t₀ ≤ t + 1 by omega) q
  have hyt := hy t h1 h2.le
  set S := Seen π p ((e.cfg t).loc p).view (readIdx ((e.cfg t).loc p).pc) (ids q) with hSdef
  have hS1 : Seen π p ((e.cfg (t + 1)).loc p).view (readIdx ((e.cfg (t + 1)).loc p).pc) (ids q)
      = S := by rw [hlocp]
  unfold Ph
  dsimp only
  rw [hS1]
  cases hpc : ((e.cfg t).loc q).pc with
  | cas j =>
    rw [hpc] at hLq
    rw [act_cas hpc hLq] at hact
    simp only [SymAction.rmw.injEq] at hact
    obtain ⟨rfl, rfl, rfl⟩ := hact
    have hS : S ⊆ own ids (e.cfg t) q := Ph.of_casRead e hPh (Or.inl ⟨j, hpc⟩)
    have hsub : own ids (e.cfg t) q ⊆ own ids (e.cfg (t + 1)) q := by
      intro y hy'
      simp only [own, Finset.mem_filter, Finset.mem_univ, true_and] at hy' ⊢
      rw [hmem, Function.update_apply]
      split_ifs with hyx
      · subst hyx; simp [hy']
      · exact hy'
    refine Or.inl ⟨?_, hS.trans hsub⟩
    rw [hloc]; dsimp only
    split_ifs
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
  | read j =>
    rw [hpc] at hLq
    rw [act_read hpc hLq.1] at hact
    simp only [SymAction.rmw.injEq] at hact
    obtain ⟨rfl, rfl, rfl⟩ := hact
    have hS : S ⊆ own ids (e.cfg t) q := Ph.of_casRead e hPh (Or.inr ⟨j, hpc⟩)
    have hmemeq : (e.cfg (t + 1)).mem () = (e.cfg t).mem () := by rw [hmem]; simp
    have hown : own ids (e.cfg (t + 1)) q = own ids (e.cfg t) q := by simp [own, hmemeq]
    rw [hown]
    rw [hloc]; dsimp only
    split_ifs with hj1
    · exact Or.inl ⟨Or.inr ⟨_, rfl⟩, hS⟩
    · rcases afterRead_pc ((e.cfg t).loc q)
        (Function.update ((e.cfg t).loc q).view ⟨j, hLq.1⟩ ((e.cfg t).mem () (π q ⟨j, hLq.1⟩)))
        with ⟨j', h⟩ | h | h | h <;> rw [h]
      · exact Or.inr (Or.inl ⟨⟨j', rfl⟩, own ids (e.cfg t) q, hS, subset_rfl, t, h1, by omega,
          le_rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨⟨0, true, rfl, Or.inr (Nat.zero_le _)⟩, t, h1, by omega,
          Finset.card_le_card hS⟩))
      · exfalso
        rw [hloc] at hph1; dsimp only at hph1
        simp only [hj1, ite_false, h] at hph1
        rcases hph1 with ⟨h', -⟩ | ⟨-, h'⟩
        · cases h'
        · exact h'
      · exact Or.inl ⟨Or.inl ⟨0, rfl⟩, hS⟩
  | wr j =>
    rw [hpc] at hLq
    obtain ⟨hj, -, -⟩ := hLq
    rw [act_wr hpc hj] at hact
    simp only [SymAction.rmw.injEq] at hact
    obtain ⟨rfl, rfl, rfl⟩ := hact
    obtain ⟨B, hSB, hoB, t'', ht1, ht2, ht3⟩ := Ph.of_wr e hPh hpc
    have hsub : own ids (e.cfg (t + 1)) q ⊆ own ids (e.cfg t) q := by
      intro y hy'
      simp only [own, Finset.mem_filter, Finset.mem_univ, true_and] at hy' ⊢
      rw [hmem, Function.update_apply] at hy'
      split_ifs at hy' with hyx <;> first | (simp at hy') | exact hy'
    rw [hloc]; dsimp only
    unfold wrFrom
    split_ifs
    · exact Or.inr (Or.inl ⟨⟨_, rfl⟩, B, hSB, hsub.trans hoB, t'', ht1, by omega, ht3⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨⟨0, true, rfl, Or.inr (Nat.zero_le _)⟩, t'', ht1, by omega,
        (Finset.card_le_card hSB).trans ht3⟩))
  | wait j ab =>
    rw [hpc] at hLq
    obtain ⟨hj, hempty⟩ := hLq
    rw [act_wait hpc hj] at hact
    simp only [SymAction.rmw.injEq] at hact
    obtain ⟨rfl, rfl, rfl⟩ := hact
    have hmemeq : (e.cfg (t + 1)).mem () = (e.cfg t).mem () := by rw [hmem]; simp
    have hown : own ids (e.cfg (t + 1)) q = own ids (e.cfg t) q := by simp [own, hmemeq]
    rw [hown]
    set v := (e.cfg t).mem () (π q ⟨j, hj⟩) with hv
    set idx := ((π q).symm y₀).val with hidx
    have hidx_lt : idx < m := ((π q).symm y₀).isLt
    have hy0 : j = idx → v ≠ none := by
      intro hji
      have : (⟨j, hj⟩ : Fin m) = (π q).symm y₀ := Fin.ext hji
      rw [hv, this, Equiv.apply_symm_apply, hyt]; simp
    rcases Ph.of_wait e hPh hpc with ⟨hab, t'', ht1, ht2, ht3⟩ | hS
    · rw [hloc]; dsimp only
      split_ifs with hj1 hab2
      · refine Or.inr (Or.inr (Or.inl ⟨⟨_, _, rfl, ?_⟩, t'', ht1, by omega, ht3⟩))
        by_cases hji : j = idx
        · left
          rcases Option.ne_none_iff_exists.1 (hy0 hji) with ⟨a, ha⟩
          rw [← ha]; simp
        · rcases hab with hab | hab
          · left; simp [hab]
          · right; omega
      · exfalso
        simp only [Bool.and_eq_true, beq_iff_eq] at hab2
        obtain ⟨rfl, hvn⟩ := hab2
        rcases hab with hab | hab
        · cases hab
        · exact hy0 (by omega) hvn
      · exact Or.inr (Or.inr (Or.inl ⟨⟨0, true, rfl, Or.inr (Nat.zero_le _)⟩, t'', ht1, by omega,
          ht3⟩))
    · rw [hloc]; dsimp only
      split_ifs
      · exact Or.inr (Or.inr (Or.inr ⟨Or.inr ⟨_, _, rfl⟩, hS⟩))
      · exact Or.inl ⟨Or.inl ⟨0, rfl⟩, by rw [hSdef, hS]; exact Finset.empty_subset _⟩
      · exact Or.inr (Or.inr (Or.inr ⟨Or.inr ⟨_, _, rfl⟩, hS⟩))
  | _ => rw [hpc] at hbusy; exact absurd hbusy id

/-- The phase invariant holds throughout the scan. -/
lemma ph_all (hσ0 : ((e.cfg σ).loc p).pc = .read 0) :
    ∀ t, σ ≤ t → t ≤ τ → Ph e p q σ t y₀ := by
  intro t h1 h2
  induction t, h1 using Nat.le_induction with
  | base =>
    refine Ph.of_empty e le_rfl ?_ ?_
    · rw [hσ0]; ext y; simp [Seen, readIdx]
    · rcases H.phase hid hm hσ q with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
  | succ t h1 ih =>
    have hPh := ih (by omega)
    by_cases hlp : e.lbl t = .tau p
    · exact ph_succ_p hid hm H hqp hσ hread hy h1 (by omega) hPh hlp
    · by_cases hlq : e.lbl t = .tau q
      · exact ph_succ_q hid hm H hqp hσ hread hy h1 (by omega) hPh hlq
      · exact ph_succ_other hid hm H hqp hσ hread hy h1 (by omega) hPh hlp hlq

/-- **No inflation.** At the end of a scan of `p` (during which `p` owns `y₀`), the number of
entries of `p`'s view equal to `q`'s identifier is at most the number of registers that `q`
owned at some time of the scan. -/
lemma no_inflation (hσ0 : ((e.cfg σ).loc p).pc = .read 0) (hστ : σ ≤ τ)
    (hτ : ((e.cfg τ).loc p).pc = .read (m - 1)) :
    ∃ t'', σ ≤ t'' ∧ t'' ≤ τ ∧
      (Finset.univ.filter (fun x : Fin m => Function.update ((e.cfg τ).loc p).view
        ⟨m - 1, by omega⟩ ((e.cfg τ).mem () (π p ⟨m - 1, by omega⟩)) x = some (ids q))).card ≤
        (own ids (e.cfg t'') q).card := by
  have hPh := ph_all hid hm H hqp hσ hread hy hσ0 τ hστ le_rfl
  set v := (e.cfg τ).mem () (π p ⟨m - 1, by omega⟩) with hv
  set S := Seen π p ((e.cfg τ).loc p).view (readIdx ((e.cfg τ).loc p).pc) (ids q) with hS
  have hcard : (Finset.univ.filter (fun x : Fin m => Function.update ((e.cfg τ).loc p).view
      ⟨m - 1, by omega⟩ v x = some (ids q))).card =
      (if v = some (ids q) then insert (π p ⟨m - 1, by omega⟩) S else S).card := by
    have := seen_succ (π := π) p ((e.cfg τ).loc p).view (m - 1) (by omega) v (ids q)
    rw [show m - 1 + 1 = m by omega] at this
    rw [hS, hτ]
    simp only [readIdx]
    rw [← this, Seen, Finset.card_map]
    congr 1
    ext x; simp [x.isLt]
  rw [hcard]
  have hnew : v = some (ids q) → π p ⟨m - 1, by omega⟩ ∈ own ids (e.cfg τ) q := by
    intro h; simp [own, ← hv, h]
  rcases H.phase hid hm (show t₀ ≤ τ by omega) q with ⟨hr, -⟩ | ⟨-, hb⟩
  · have hS0 : S = ∅ := Ph.empty_of_rem e hPh hr
    have hv' : ¬ v = some (ids q) := fun h => by
      have := hnew h; rw [own_empty_of_rem hid hm H hr] at this; simp at this
    refine ⟨τ, hστ, le_rfl, ?_⟩
    simp only [hv', ite_false, hS0]; simp
  · cases hpc : ((e.cfg τ).loc q).pc with
    | cas i =>
      have h := Ph.of_casRead e hPh (Or.inl ⟨i, hpc⟩)
      refine ⟨τ, hστ, le_rfl, Finset.card_le_card ?_⟩
      split_ifs with hq
      · exact Finset.insert_subset (hnew hq) h
      · exact h
    | read i =>
      have h := Ph.of_casRead e hPh (Or.inr ⟨i, hpc⟩)
      refine ⟨τ, hστ, le_rfl, Finset.card_le_card ?_⟩
      split_ifs with hq
      · exact Finset.insert_subset (hnew hq) h
      · exact h
    | wr j =>
      obtain ⟨B, hSB, hoB, t'', ht1, ht2, ht3⟩ := Ph.of_wr e hPh hpc
      refine ⟨t'', ht1, ht2, le_trans (Finset.card_le_card ?_) ht3⟩
      split_ifs with hq
      · exact Finset.insert_subset (hoB (hnew hq)) hSB
      · exact hSB
    | wait j ab =>
      have hv' : ¬ v = some (ids q) := fun h => by
        have := hnew h; rw [own_empty_of_wait hid hm H hpc] at this; simp at this
      simp only [hv', ite_false]
      rcases Ph.of_wait e hPh hpc with ⟨-, h⟩ | h
      · exact h
      · exact ⟨τ, hστ, le_rfl, by rw [hS, h]; simp⟩
    | _ => rw [hpc] at hb; exact absurd hb id

end Steps

end Scan

end AnonymousMutex.Alg2
