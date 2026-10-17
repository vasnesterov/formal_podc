import Papers.PODC2020.BezoutElection.Alg1Live
import Mathlib.Data.Finset.Max

/-!
# Algorithm 1: termination

Let `e` be a fair infinite execution in which every process invokes `elect()` once.

* **Electing phase** (`Ctx.phase1`): if no value `⟨id, D, ·⟩` with `|D| = n - 1` is ever decided
  (`NoLead` forever), we get a contradiction. The set of losers and the `discarded` sets
  `D_c` of the non-losers eventually stabilize; let `c₀` be a non-loser with `|D_c₀| = μ`
  minimal. Eventually every value with an identifier has `≥ μ` discarded identifiers, hence
  every `⊥`-value written by a loser (line 17) has `> μ` of them; so `c₀` can never again read
  a `⊥`-value (it would merge it into `D_c₀`), it stops writing, and the next write of another
  process hides `c₀`'s identifier forever — but `c₀` keeps reading and only reads its own
  identifier.
* **Leader phase** (`Ctx.phase2`): once `Lead L` holds, `L` eventually commits (`L` writes after
  every read, and the only other writes are line-8 values `⟨⊥, ∅, committing⟩`); then
  `D_L` grows and stabilizes. If `|D_L| = n - 1`, all other processes are quiet, eventually `REG`
  holds `⟨id_L, D_L, committing⟩` forever and every process returns. Otherwise some loser
  `j ∉ D_L` eventually writes `⟨⊥, D ∪ {j}, committing⟩`, which `L` cannot read without
  growing `D_L`; so `L` stops writing, `REG` eventually holds a `⊥`-value forever, and `L` reads
  it — contradiction.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection.Alg1

variable {Id : Type} [DecidableEq Id] {R : Type} [Inhabited R] {P : Type} [DecidableEq P]
  [Fintype P] {n : ℕ} {out : Id → Id → R} {ids : P → Id} {π : P → Equiv.Perm (Fin 1)}
  {e : ((alg1 Id n out).impl ids π).InfExec}

namespace Ctx

variable (X : Ctx e)
include X

lemma card_disc_le (t : ℕ) (c : P) : ((e.cfg t).loc c).disc.card ≤ n := by
  have hsub : ((e.cfg t).loc c).disc ⊆ Finset.univ.image ids := by
    intro x hx
    obtain ⟨j, rfl, -⟩ := (X.basic t).disc_loc c x hx
    exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
  calc _ ≤ (Finset.univ.image ids).card := Finset.card_le_card hsub
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = n := by rw [Finset.card_univ, X.hn]

/-- All processes but `c` are in `D` ⇒ `n - 1 ≤ |D|`. -/
lemma card_ge_of_all (D : Finset Id) (c : P) (h : ∀ j, j ≠ c → ids j ∈ D) : n - 1 ≤ D.card := by
  have hsub : (Finset.univ.erase c).image ids ⊆ D := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    exact h j (Finset.ne_of_mem_erase hj)
  have := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ X.hid, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, X.hn] at this

/-- "Eventually forever" from writes. -/
lemma ev_write (Q : ℕ → Prop) (T : ℕ) (hpres : ∀ t ≥ T, Q t → Q (t + 1))
    (hw : ∀ t ≥ T, WriteAt e t → Q (t + 1)) (hIW : ∀ t, ∃ t' ≥ t, WriteAt e t') :
    ∃ T' ≥ T, ∀ t ≥ T', Q t := by
  obtain ⟨t, ht, hwt⟩ := hIW T
  obtain ⟨T', hT', h⟩ := ev_forever Q T hpres ⟨t + 1, by omega, hw t ht hwt⟩
  exact ⟨T', hT', h⟩

/-! ### The electing phase cannot last forever -/

theorem phase1 [Nonempty P] (hN : ∀ t, NoLead n (e.lbls t) (e.cfg t)) : False := by
  -- all processes are active forever
  have hact0 : ∀ q, ∃ T, ∀ t ≥ T, (e.cfg t).pend q ≠ none ∧
      (((e.cfg t).loc q).pc = .read ∨ ∃ w, ((e.cfg t).loc q).pc = .write w) := by
    intro q
    obtain ⟨T, -, hT⟩ := X.pend_forever q 0 (fun t _ => (hN t).nofin q)
    exact ⟨T, fun t ht => ⟨(hT t ht).1, X.pc_cases (hT t ht).2.1 (hT t ht).2.2 ((hN t).noret q)⟩⟩
  obtain ⟨T0, -, hT0⟩ := ev_forall_fin _ hact0 0
  -- the losers stabilize
  obtain ⟨T1, hT1, hlos⟩ := stab_finset
    (fun t => Finset.univ.filter (fun q => ((e.cfg t).loc q).loser = true)) T0 (Fintype.card P)
    (fun t _ q hq => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact (X.mono t q).2.1 hq)
    (fun t => Finset.card_filter_le _ _)
  have hlos' : ∀ t ≥ T1, ∀ q, ((e.cfg t).loc q).loser = ((e.cfg T1).loc q).loser := by
    intro t ht q
    have := Finset.ext_iff.1 (hlos t ht) q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact Bool.eq_iff_iff.2 this
  -- the discarded sets of the non-losers stabilize
  have hdisc : ∀ c, ∃ T, ∀ t ≥ T, ((e.cfg T1).loc c).loser = false →
      ∀ t' ≥ t, ((e.cfg t').loc c).disc = ((e.cfg t).loc c).disc := by
    intro c
    by_cases hc : ((e.cfg T1).loc c).loser = false
    · obtain ⟨T, hT, hTc⟩ := stab_finset (fun t => ((e.cfg t).loc c).disc) T1 n
        (fun t ht => by
          by_cases hq : (e.lbl t).proc = c
          · rcases (hT0 t (by omega) c).2 with h1 | ⟨w, h1⟩
            · rw [(X.act_read hq h1).2.1]
              apply afterRead_disc_mono
              · rw [← (X.act_read hq h1).2.1, hlos' (t + 1) (by omega), hc]
              · rw [← (X.act_read hq h1).2.1, (hN (t + 1)).phase, (hN t).phase]
            · rw [(X.act_write hq h1).2.1]
          · rw [X.other hq])
        (fun t => X.card_disc_le t c)
      exact ⟨T, fun t ht _ t' ht' => by rw [hTc t' (by omega), hTc t ht]⟩
    · exact ⟨0, fun t _ h => absurd h hc⟩
  obtain ⟨T2, hT2, hT2'⟩ := ev_forall_fin _ hdisc T1
  set D : P → Finset Id := fun c => ((e.cfg T2).loc c).disc with hDdef
  have hD : ∀ t ≥ T2, ∀ c, ((e.cfg T1).loc c).loser = false → ((e.cfg t).loc c).disc = D c :=
    fun t ht c hc => hT2' T2 le_rfl c hc t ht
  -- a non-loser with a minimal discarded set
  set S := Finset.univ.filter (fun c => ((e.cfg T1).loc c).loser = false) with hS
  have hSne : S.Nonempty := by
    obtain ⟨c, hc⟩ := (X.basic T1).nl inferInstance
    exact ⟨c, by simp [hS, hc]⟩
  obtain ⟨c₀, hc₀S, hc₀min⟩ := S.exists_min_image (fun c => (D c).card) hSne
  have hc₀ : ((e.cfg T1).loc c₀).loser = false := by simpa [hS] using hc₀S
  set μ := (D c₀).card with hμ
  have hmin : ∀ c, ((e.cfg T1).loc c).loser = false → μ ≤ (D c).card :=
    fun c hc => hc₀min c (by simp [hS, hc])
  -- values with an identifier have at least `μ` discarded identifiers
  have F3 : ∀ t ≥ T2, ∀ q w, ((e.cfg t).loc q).pc = .write w → w.id ≠ none →
      μ ≤ w.disc.card := by
    intro t ht q w hw hid'
    obtain ⟨h1, h2⟩ := (X.basic t).wsome q w hw hid'
    have h3 : ((e.cfg T1).loc q).loser = false := by rw [← hlos' t (by omega)]; exact h2
    rw [h1]; simp only; rw [hD t ht q h3]; exact hmin q h3
  -- infinitely many writes
  have hIW : ∀ t, ∃ t' ≥ t, WriteAt e t' := by
    intro t
    by_contra hcon
    push Not at hcon
    set t₁ := max t T2 with ht₁
    have hnw : ∀ t' ≥ t₁, ¬ WriteAt e t' := fun t' ht' => hcon t' (by omega)
    have hrd := fun q => X.read_nowrite q t₁ (fun t' ht' => (hT0 t' (by omega) q).1)
      (fun t' ht' => (hT0 t' (by omega) q).2) hnw
    have hvE := (hN t₁).vals _ (InVals.reg_self _)
    cases hv : (reg (e.cfg t₁)).id with
    | none =>
      obtain ⟨t', ht', hpc, -, hreg, -, hnw'⟩ := hrd c₀
      have hl : ((e.cfg t').loc c₀).loser = false := by rw [hlos' t' (by omega)]; exact hc₀
      rw [hreg] at hnw'
      rcases afterRead_cases n ((e.cfg t').loc c₀) (reg (e.cfg t₁)) with ⟨hA1, -⟩ |
        ⟨-, a, ha, -⟩ | ⟨-, a, ha, -⟩ | ⟨-, -, -, hs'⟩ | ⟨-, a, ha, -⟩ | ⟨-, -, hE1, -⟩
      · rw [hvE.1] at hA1; cases hA1
      · rw [hv] at ha; cases ha
      · rw [hv] at ha; cases ha
      · exact hnw' _ (by rw [hs'])
      · rw [hv] at ha; cases ha
      · rw [hE1 hv] at hl; cases hl
    | some a =>
      obtain ⟨c, rfl, hc⟩ := (X.basic t₁).regsome _ hv
      have hall : ∀ q, q ≠ c → ids q ∈ (reg (e.cfg t₁)).disc := by
        intro q hqc
        obtain ⟨t', ht', hpc, -, hreg, -, hnw'⟩ := hrd q
        rw [hreg] at hnw'
        have hme := X.me t' q
        rcases afterRead_cases n ((e.cfg t').loc q) (reg (e.cfg t₁)) with ⟨hA1, -⟩ |
          ⟨-, a, ha, -, hph, -⟩ | ⟨-, a, ha, hc', -⟩ | ⟨-, ha, -⟩ | ⟨-, a, ha, -, -, -, hs'⟩ |
          ⟨-, -, -, hE2⟩
        · rw [hvE.1] at hA1; cases hA1
        · rw [hvE.1] at hph; cases hph
        · exact absurd hc' (hvE.2 (by rw [ha]; simp))
        · rw [hv] at ha; cases ha
        · exact (hnw' _ (by rw [hs'])).elim
        · rcases (hE2 _ hv).2 with h1 | h1
          · rw [hme] at h1; exact absurd (X.hid h1).symm hqc
          · rwa [hme] at h1
      have h1 := X.card_ge_of_all _ c hall
      have h2 : (reg (e.cfg t₁)).disc.card ≤ n - 1 := card_le_of_ids_ne X.hn _ c (fun x hx => by
        obtain ⟨j, hj, hl⟩ := (X.basic t₁).disc_val _ (InVals.reg_self _) x hx
        exact ⟨j, hj, by rintro rfl; rw [hc] at hl; cases hl⟩)
      exact hvE.2 (by rw [hv]; simp) (by omega)
  -- level 1: values with an identifier in `REG`
  obtain ⟨T3, hT3, hR1⟩ := X.ev_write
    (fun t => ∀ a, (reg (e.cfg t)).id = some a → μ ≤ (reg (e.cfg t)).disc.card) T2
    (fun t ht hR a ha => by
      rcases X.reg_step t with h1 | ⟨q, w, -, hw, h1⟩
      · rw [h1] at ha ⊢; exact hR a ha
      · rw [h1] at ha ⊢; exact F3 t ht q w hw (by rw [ha]; simp))
    (fun t ht ⟨q, w, hl, hw⟩ a ha => by
      have h1 := (X.act_write (by rw [hl]; rfl) hw).2.2
      rw [h1] at ha ⊢; exact F3 t ht q w hw (by rw [ha]; simp)) hIW
  -- level 2: pending `⊥`-writes
  have hQ2 : ∀ q, ∃ T, ∀ t ≥ T, ∀ w, ((e.cfg t).loc q).pc = .write w → w.id = none →
      μ < w.disc.card := by
    intro q
    refine X.ev_flush q T3 _ ?_ ?_ ?_
    · intro t ht hq w hw hwid
      rcases (hT0 t (by omega) q).2 with h1 | ⟨w', h1⟩
      · rw [(X.act_read hq h1).2.1] at hw
        obtain ⟨wid, Y, ph⟩ := w
        simp only at hwid; subst hwid
        rcases afterRead_write_none n _ _ hw with ⟨-, -, a, ha, hc, -⟩ | ⟨a, ha, -, hni, hY, -⟩
        · exact absurd hc ((hN t).vals _ (InVals.reg_self _) |>.2 (by rw [ha]; simp))
        · simp only; rw [hY, Finset.card_insert_of_notMem hni]
          have := hR1 t (by omega) a ha
          omega
      · rw [(X.act_write hq h1).2.1] at hw; cases hw
    · intro t ht hq hQ; rw [X.other hq]; exact hQ
    · intro hp; exact absurd hp (hT0 T3 (by omega) q).1
  obtain ⟨T4, hT4, hQ2'⟩ := ev_forall_fin _ hQ2 T3
  -- level 2: `⊥`-values in `REG`
  obtain ⟨T5, hT5, hR2⟩ := X.ev_write
    (fun t => (reg (e.cfg t)).id = none → μ < (reg (e.cfg t)).disc.card) T4
    (fun t ht hR ha => by
      rcases X.reg_step t with h1 | ⟨q, w, -, hw, h1⟩
      · rw [h1] at ha ⊢; exact hR ha
      · rw [h1] at ha ⊢; exact hQ2' t ht q w hw ha)
    (fun t ht ⟨q, w, hl, hw⟩ ha => by
      have h1 := (X.act_write (by rw [hl]; rfl) hw).2.2
      rw [h1] at ha ⊢; exact hQ2' t ht q w hw ha) hIW
  -- `c₀` only reads its own identifier
  have hc₀l : ∀ t ≥ T1, ((e.cfg t).loc c₀).loser = false := fun t ht => by
    rw [hlos' t ht]; exact hc₀
  have hread : ∀ t ≥ T5, (e.lbl t).proc = c₀ → ((e.cfg t).loc c₀).pc = .read →
      (reg (e.cfg t)).id = some (ids c₀) ∧
        (afterRead n ((e.cfg t).loc c₀) (reg (e.cfg t))).pc = .read := by
    intro t ht hq hpc
    obtain ⟨-, hloc, -⟩ := X.act_read hq hpc
    have hvE := (hN t).vals _ (InVals.reg_self _)
    have hme := X.me t c₀
    rcases afterRead_cases n ((e.cfg t).loc c₀) (reg (e.cfg t)) with ⟨hA1, -⟩ |
      ⟨-, a, ha, -, hph, -⟩ | ⟨-, a, ha, hc', -⟩ | ⟨-, hid0, -, hs'⟩ | ⟨-, a, ha, -, -, -, hs'⟩ |
      ⟨hs', -, hE1, hE2⟩
    · rw [hvE.1] at hA1; cases hA1
    · rw [hvE.1] at hph; cases hph
    · exact absurd hc' (hvE.2 (by rw [ha]; simp))
    · exfalso
      have h1 : ((e.cfg (t + 1)).loc c₀).disc = D c₀ := hD (t + 1) (by omega) c₀ hc₀
      have h2 : ((e.cfg t).loc c₀).disc = D c₀ := hD t (by omega) c₀ hc₀
      rw [hloc, hs'] at h1
      simp only at h1
      rw [ite_eq_left (by rw [hvE.1, (hN t).phase])] at h1
      have h3 : (reg (e.cfg t)).disc ⊆ D c₀ := by
        rw [← h1]; exact Finset.subset_union_right
      have h4 := Finset.card_le_card h3
      have h5 := hR2 t (by omega) hid0
      omega
    · exfalso
      have h1 := hc₀l (t + 1) (by omega)
      rw [hloc, hs'] at h1; cases h1
    · cases hv : (reg (e.cfg t)).id with
      | none => have := hE1 hv; rw [hc₀l t (by omega)] at this; cases this
      | some a =>
        refine ⟨?_, by rw [hs']⟩
        rcases (hE2 a hv).2 with h1 | h1
        · rw [h1, hme]
        · exfalso
          rw [hme] at h1
          obtain ⟨j, hj, hl⟩ := (X.basic t).disc_val _ (InVals.reg_self _) _ h1
          rw [X.hid hj, hc₀l t (by omega)] at hl; cases hl
  -- eventually `c₀` never writes
  obtain ⟨T6, hT6⟩ := X.ev_flush c₀ T5 (fun t => ∀ w, ((e.cfg t).loc c₀).pc ≠ .write w)
    (fun t ht hq w hw => by
      rcases (hT0 t (by omega) c₀).2 with h1 | ⟨w', h1⟩
      · rw [(X.act_read hq h1).2.1, (hread t ht hq h1).2] at hw; cases hw
      · rw [(X.act_write hq h1).2.1] at hw; cases hw)
    (fun t ht hq hQ => by rw [X.other hq]; exact hQ)
    (fun hp => absurd hp (hT0 T5 (by omega) c₀).1)
  -- a write of another process hides `c₀` forever
  obtain ⟨t₇, ht₇, q, w, hl, hw⟩ := hIW (max T6 T5)
  have hR3 : ∀ t ≥ t₇ + 1, (reg (e.cfg t)).id ≠ some (ids c₀) := by
    have hw3 : ∀ t ≥ max T6 T5, ∀ q w, e.lbl t = .tau q → ((e.cfg t).loc q).pc = .write w →
        w.id ≠ some (ids c₀) := by
      intro t ht q w hl hw hid'
      obtain ⟨h1, -⟩ := (X.basic t).wsome q w hw (by rw [hid']; simp)
      rw [h1] at hid'; simp only [Option.some.injEq] at hid'
      have := X.hid hid'; subst this
      exact hT6 t (by omega) w hw
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rw [(X.act_write (by rw [hl]; rfl) hw).2.2]; exact hw3 t₇ ht₇ q w hl hw
    | succ t ht ih =>
      rcases X.reg_step t with h1 | ⟨q', w', hl', hw', h1⟩
      · rw [h1]; exact ih
      · rw [h1]; exact hw3 t (by omega) q' w' hl' hw'
  obtain ⟨t, ht, hq⟩ := InfExec.acts e X.fair (fun t ht => (hT0 t ht c₀).1) (max (t₇ + 1) T0)
    (by omega)
  rcases (hT0 t (by omega) c₀).2 with h1 | ⟨w', h1⟩
  · exact hR3 t (by omega) (hread t (by omega) hq h1).1
  · exact hT6 t (by omega) w' h1


/-! ### The leader phase -/

lemma lead_forever {L : P} {t₀ : ℕ} (h : Lead ids n out (e.lbls t₀) (e.cfg t₀) L) :
    ∀ t ≥ t₀, Lead ids n out (e.lbls t) (e.cfg t) L := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact h
  | succ t _ ih =>
    have hB' := X.basic (t + 1)
    rw [Impl.InfExec.lbls_succ] at hB' ⊢
    exact lead_step X.hid X.hn (X.basic t) hB' ih (e.step_eq t)

end Ctx

/-- Measure for "the leader eventually commits". -/
def mu1 (s : St Id) (r : Reg Id) : ℕ :=
  match s.pc with
  | .write w => if w.id = none then 1 else 3
  | _ => if r.phase = .committing then 0 else if r.id = none then 4 else 2

lemma mu1_write {s : St Id} {w : Reg Id} (h : s.pc = .write w) (r : Reg Id) :
    mu1 s r = if w.id = none then 1 else 3 := by
  simp [mu1, h]

lemma mu1_nonwrite {s : St Id} (h : ∀ w, s.pc ≠ .write w) (r : Reg Id) :
    mu1 s r = if r.phase = .committing then 0 else if r.id = none then 4 else 2 := by
  unfold mu1
  split
  · rename_i w hw; exact absurd hw (h w)
  · rfl

/-- Measure for "a process at `read` reads, a process at `write` writes". -/
def mu2 (s : St Id) : ℕ :=
  match s.pc with
  | .write _ => 2
  | .read => 1
  | _ => 0

/-- Measure for "a process at `read` decides to write". -/
def mu3 (s : St Id) : ℕ :=
  match s.pc with
  | .write _ => 0
  | _ => 1

namespace Ctx

variable (X : Ctx e)
include X

theorem phase2 (L : P) (t₀ : ℕ) (hL0 : Lead ids n out (e.lbls t₀) (e.cfg t₀) L) (p₀ : P)
    (H : ∀ t r, e.lbl t ≠ .ret p₀ r) : False := by
  have hLd := X.lead_forever hL0
  have hlos : ∀ t ≥ t₀, ∀ j, ((e.cfg t).loc j).loser = true ↔ j ≠ L :=
    fun t ht => (hLd t ht).loser
  have hLnl : ∀ t ≥ t₀, ((e.cfg t).loc L).loser = false := fun t ht => by
    have := hlos t ht L; simpa using this
  have hwnone : ∀ t ≥ t₀, ∀ q w, q ≠ L → ((e.cfg t).loc q).pc = .write w → w.id = none := by
    intro t ht q w hq hw
    by_contra h
    have h1 := ((X.basic t).wsome q w hw h).2
    have h2 := (hlos t ht q).2 hq
    rw [h1] at h2; cases h2
  have hrv : ∀ t, InVals (e.cfg t) (reg (e.cfg t)) := fun t => InVals.reg_self _
  ------------------------------------------------------------------
  -- Step 1: the leader eventually commits
  have hA1 : ∃ t₁ ≥ t₀, ((e.cfg t₁).loc L).phase = .committing := by
    by_contra hcon
    push Not at hcon
    have hE : ∀ t ≥ t₀, ((e.cfg t).loc L).phase = .electing := fun t ht => by
      cases h : ((e.cfg t).loc L).phase
      · rfl
      · exact absurd h (hcon t ht)
    have hEl : ∀ t ≥ t₀, ElPart n (e.cfg t) L := fun t ht => (hLd t ht).el (hE t ht)
    obtain ⟨T, hT, hTL⟩ := X.pend_forever L t₀ (fun t ht => (hEl t ht).nofin L)
    have hQ : ∀ q, ∃ T', ∀ t ≥ T', ∀ w, ((e.cfg t).loc q).pc = .write w → w.id = none →
        w = ⟨none, ∅, .committing⟩ := by
      intro q
      refine X.ev_flush q t₀ _ ?_ ?_ ?_
      · intro t ht hq w hw hwid
        by_cases hpc : ((e.cfg t).loc q).pc = .read
        · rw [(X.act_read hq hpc).2.1] at hw
          obtain ⟨wid, Y, ph⟩ := w
          simp only at hwid; subst hwid
          rcases afterRead_write_none n _ _ hw with ⟨rfl, rfl, -⟩ | ⟨a, ha, hne, hni, -, -, -⟩
          · rfl
          · exfalso
            have haL := (hLd t ht).ids_val _ a (hrv t) ha
            have hqL : q ≠ L := by rintro rfl; exact hne (by rw [haL, X.me])
            have hc := ((hEl t ht).some_val _ (hrv t) (by rw [ha]; simp)).2
            have hmem := Lead.mem_of_card X.hid X.hn (hLd t ht) _
              ((X.basic t).disc_val _ (hrv t)) hc q hqL
            rw [X.me] at hni; exact hni hmem
        · exact absurd hw ((X.act_nonread hq hpc).2.2.2 w)
      · intro t ht hq hQ; rw [X.other hq]; exact hQ
      · intro hp w hw
        have h1 : ((e.cfg t₀).loc q).pc ≠ .idle := by rw [hw]; simp
        have h2 : ((e.cfg t₀).loc q).pc ≠ .fin := by rw [hw]; simp
        exact absurd hp ((X.basic t₀).busy q h1 h2)
    obtain ⟨T', hT', hQ'⟩ := ev_forall_fin _ hQ T
    refine InfExec.descent e X.fair L T' (fun t => mu1 ((e.cfg t).loc L) (reg (e.cfg t)))
      (fun t ht => (hTL t (by omega)).1) ?_ ?_
    · intro t ht hq
      show mu1 _ _ ≤ mu1 _ _
      rw [X.other hq]
      rcases X.reg_step t with h1 | ⟨q, w, hl, hw, h1⟩
      · rw [h1]
      · have hqL : q ≠ L := by rintro rfl; rw [hl] at hq; exact hq rfl
        have hw0 := hQ' t ht q w hw (hwnone t (by omega) q w hqL hw)
        rw [h1, hw0]
        by_cases hpw : ∃ w', ((e.cfg t).loc L).pc = .write w'
        · obtain ⟨w', hw'⟩ := hpw
          rw [mu1_write hw', mu1_write hw']
        · push Not at hpw
          rw [mu1_nonwrite hpw]; simp
    · intro t ht hq
      show mu1 _ _ < mu1 _ _
      have hEt := hE t (by omega)
      rcases X.pc_cases (hTL t (by omega)).2.1 (hTL t (by omega)).2.2
        ((hEl t (by omega)).noret L) with hpc | ⟨w, hpc⟩
      · obtain ⟨-, hloc, hreg⟩ := X.act_read hq hpc
        rw [hloc, hreg, mu1_nonwrite (s := (e.cfg t).loc L) (by rw [hpc]; simp)]
        have hEt1 := hE (t + 1) (by omega)
        rw [hloc] at hEt1
        rcases afterRead_cases n ((e.cfg t).loc L) (reg (e.cfg t)) with ⟨hA1, hA2, hs'⟩ |
          ⟨hnA, a, ha, hc, hph, hs'⟩ | ⟨hnA, a, ha, hc, hph, hs'⟩ | ⟨hnA, hid0, hlo0, hs'⟩ |
          ⟨hnA, a, ha, hc, hne, hni, hs'⟩ | ⟨hs', hnA, hE1, hE2⟩
        · rw [hs'] at hEt1; cases hEt1
        · exact absurd ⟨hph, hEt⟩ hnA
        · rw [hs', mu1_write rfl]; simp [hph, ha]
        · have hph : (reg (e.cfg t)).phase = .electing := by
            cases h : (reg (e.cfg t)).phase
            · rfl
            · exact absurd ⟨h, hEt⟩ hnA
          rw [hs', mu1_write rfl]; simp [hph, hid0]
        · have haL := (hLd t (by omega)).ids_val _ a (hrv t) ha
          exact absurd (by rw [haL, X.me]) hne
        · exfalso
          cases hv : (reg (e.cfg t)).id with
          | none => have := hE1 hv; rw [hLnl t (by omega)] at this; cases this
          | some a =>
            exact (hE2 a hv).1
              ((hEl t (by omega)).some_val _ (hrv t) (by rw [hv]; simp)).2
      · obtain ⟨-, hloc, hreg⟩ := X.act_write hq hpc
        rw [hloc, hreg, mu1_write hpc, mu1_nonwrite (by simp)]
        by_cases hwid : w.id = none
        · rw [hQ' t (by omega) L w hpc hwid]; simp
        · obtain ⟨h1, -⟩ := (X.basic t).wsome L w hpc hwid
          rw [h1]; simp [hEt]
  ------------------------------------------------------------------
  -- Step 2: the leader's committing discarded set stabilizes
  obtain ⟨t₁, ht₁, hC1⟩ := hA1
  have hC : ∀ t ≥ t₁, ((e.cfg t).loc L).phase = .committing := fun t ht => X.phase_mono ht hC1
  have hCo : ∀ t ≥ t₁, CoPart ids n (e.cfg t) L := fun t ht => (hLd t (by omega)).co (hC t ht)
  obtain ⟨T2a, hT2a, hDst⟩ := stab_finset (fun t => ((e.cfg t).loc L).disc) t₁ n
    (fun t ht => by
      by_cases hq : (e.lbl t).proc = L
      · by_cases hpc : ((e.cfg t).loc L).pc = .read
        · rw [(X.act_read hq hpc).2.1]
          apply afterRead_disc_mono
          · rw [← (X.act_read hq hpc).2.1]; exact hLnl (t + 1) (by omega)
          · rw [← (X.act_read hq hpc).2.1, hC (t + 1) (by omega), hC t ht]
        · rw [(X.act_nonread hq hpc).1]
      · rw [X.other hq])
    (fun t => X.card_disc_le t L)
  obtain ⟨T2, hT2, hPst⟩ := stab_finset
    (fun t => Finset.univ.filter (fun q => ((e.cfg t).loc q).phase = .committing)) T2a
    (Fintype.card P)
    (fun t _ q hq => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact (X.mono t q).2.2 hq)
    (fun t => Finset.card_filter_le _ _)
  have hDc : ∀ t ≥ T2, ((e.cfg t).loc L).disc = ((e.cfg T2).loc L).disc := fun t ht => by
    rw [hDst t (by omega), hDst T2 hT2]
  have hph : ∀ t ≥ T2, ∀ q, ((e.cfg t).loc q).phase = .committing ↔
      ((e.cfg T2).loc q).phase = .committing := by
    intro t ht q
    have := Finset.ext_iff.1 (hPst t ht) q
    simpa using this
  set D := ((e.cfg T2).loc L).disc with hD
  have hDle : D.card ≤ n - 1 :=
    Lead.card_le X.hn (hLd T2 (by omega)) D ((X.basic T2).disc_loc L)
  by_cases hfull : D.card = n - 1
  · ------------------------------------------------------------------
    -- Step 3a: all other processes are quiet; eventually `REG` holds the final value
    have hquiet : ∀ t ≥ T2, ∀ j, j ≠ L → ((e.cfg t).loc j).phase = .committing ∧
        (∀ w, ((e.cfg t).loc j).pc ≠ .write w) ∧
        ∀ v, InVals (e.cfg t) v → v.id ≠ none → ids j ∈ v.disc := by
      intro t ht j hj
      have hmem : ids j ∈ ((e.cfg t).loc L).disc := by
        rw [hDc t ht]
        exact Lead.mem_of_card X.hid X.hn (hLd T2 (by omega)) D ((X.basic T2).disc_loc L)
          hfull j hj
      exact (hCo t (by omega)).quiet j hmem
    have hA3 : ∃ T3 ≥ T2, (reg (e.cfg T3)).id ≠ none := by
      by_contra hcon
      push Not at hcon
      have hnr : ∀ t ≥ T2, ∀ q, (∀ a, ((e.cfg t).loc q).pc ≠ .ret a) ∧
          ((e.cfg t).loc q).pc ≠ .fin := by
        intro t ht q
        constructor
        · intro a ha; exact ((hCo t (by omega)).done ⟨q, Or.inl ⟨a, ha⟩⟩).1 (hcon t ht)
        · intro ha; exact ((hCo t (by omega)).done ⟨q, Or.inr ha⟩).1 (hcon t ht)
      obtain ⟨T, hT, hTL⟩ := X.pend_forever L T2 (fun t ht => (hnr t ht L).2)
      refine InfExec.descent e X.fair L T (fun t => mu3 ((e.cfg t).loc L))
        (fun t ht => (hTL t ht).1) ?_ ?_
      · intro t ht hq; show mu3 _ ≤ mu3 _; rw [X.other hq]
      · intro t ht hq
        show mu3 _ < mu3 _
        rcases X.pc_cases (hTL t ht).2.1 (hTL t ht).2.2 (hnr t (by omega) L).1 with hpc | ⟨w, hpc⟩
        · obtain ⟨-, hloc, -⟩ := X.act_read hq hpc
          rw [hloc]
          have hid0 := hcon t (by omega)
          rcases afterRead_cases n ((e.cfg t).loc L) (reg (e.cfg t)) with ⟨-, hA2, -⟩ |
            ⟨-, a, ha, -⟩ | ⟨-, a, ha, -⟩ | ⟨-, -, -, hs'⟩ | ⟨-, a, ha, -⟩ | ⟨-, -, hE1, -⟩
          · rw [hC t (by omega)] at hA2; cases hA2
          · rw [hid0] at ha; cases ha
          · rw [hid0] at ha; cases ha
          · rw [hs']; simp [mu3, hpc]
          · rw [hid0] at ha; cases ha
          · have := hE1 hid0; rw [hLnl t (by omega)] at this; cases this
        · exfalso
          have h1 := (X.act_write hq hpc).2.2
          exact (hCo t (by omega)).lw w hpc (by rw [← h1]; exact hcon (t + 1) (by omega))
    obtain ⟨T3, hT3, hT3'⟩ := hA3
    have hsome : ∀ t ≥ T3, (reg (e.cfg t)).id ≠ none := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => exact hT3'
      | succ t ht ih =>
        rcases X.reg_step t with h1 | ⟨q, w, -, hw, h1⟩
        · rw [h1]; exact ih
        · rw [h1]
          by_cases hqL : q = L
          · subst hqL; exact (hCo t (by omega)).lw w hw
          · exact absurd hw ((hquiet t (by omega) q hqL).2.1 w)
    have hfinal : ∀ t ≥ T3, (reg (e.cfg t)).disc.card = n - 1 ∧
        (reg (e.cfg t)).phase = .committing := by
      intro t ht
      obtain ⟨h1, h2⟩ := (hCo t (by omega)).some_val _ (hrv t) (hsome t ht)
      refine ⟨?_, h1⟩
      have h3 := Finset.card_le_card h2
      rw [hDc t (by omega)] at h3
      have h4 := X.card_ge_of_all _ L
        (fun j hj => (hquiet t (by omega) j hj).2.2 _ (hrv t) (hsome t ht))
      omega
    -- `p₀` eventually returns
    obtain ⟨T, hT, hTp⟩ := X.pend_forever p₀ T3 (fun t ht hfin => by
      obtain ⟨t', r, h⟩ := X.ret_of_outputs ((X.basic t).fin p₀ hfin)
      exact H t' r h)
    refine InfExec.descent e X.fair p₀ T (fun t => mu2 ((e.cfg t).loc p₀))
      (fun t ht => (hTp t ht).1) ?_ ?_
    · intro t ht hq; show mu2 _ ≤ mu2 _; rw [X.other hq]
    · intro t ht hq
      show mu2 _ < mu2 _
      cases hpc : ((e.cfg t).loc p₀).pc with
      | idle => exact absurd hpc (hTp t ht).2.1
      | fin => exact absurd hpc (hTp t ht).2.2
      | ret a =>
        obtain ⟨r, hr⟩ := X.act_ret hq hpc
        exact absurd hr (H t r)
      | write w =>
        rw [(X.act_write hq hpc).2.1]; simp [mu2, hpc]
      | read =>
        rw [(X.act_read hq hpc).2.1]
        have hphp : ((e.cfg t).loc p₀).phase = .committing := by
          by_cases hpL : p₀ = L
          · subst hpL; exact hC t (by omega)
          · exact (hquiet t (by omega) p₀ hpL).1
        obtain ⟨hcard, hrph⟩ := hfinal t (by omega)
        have hsm := hsome t (by omega)
        rcases afterRead_cases n ((e.cfg t).loc p₀) (reg (e.cfg t)) with ⟨-, hA2, -⟩ |
          ⟨-, a, ha, -, -, hs'⟩ | ⟨-, a, ha, -, hph', -⟩ | ⟨-, hid0, -⟩ |
          ⟨-, a, ha, hc, -⟩ | ⟨-, -, -, hE2⟩
        · rw [hphp] at hA2; cases hA2
        · rw [hs']; simp [mu2, hpc]
        · rw [hrph] at hph'; cases hph'
        · exact absurd hid0 hsm
        · exact absurd hcard hc
        · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hsm
          exact absurd hcard (hE2 a ha).1
  · ------------------------------------------------------------------
    -- Step 3b: `|D| < n - 1`
    have hlt : D.card < n - 1 := by omega
    have hnr : ∀ t ≥ T2, ∀ q, (∀ a, ((e.cfg t).loc q).pc ≠ .ret a) ∧
        ((e.cfg t).loc q).pc ≠ .fin := by
      intro t ht q
      have hne : ((e.cfg t).loc L).disc.card ≠ n - 1 := by rw [hDc t ht]; exact hfull
      constructor
      · intro a ha; exact hne ((hCo t (by omega)).done ⟨q, Or.inl ⟨a, ha⟩⟩).2
      · intro ha; exact hne ((hCo t (by omega)).done ⟨q, Or.inr ha⟩).2
    have hact0 : ∀ q, ∃ T, ∀ t ≥ T, (e.cfg t).pend q ≠ none ∧
        (((e.cfg t).loc q).pc = .read ∨ ∃ w, ((e.cfg t).loc q).pc = .write w) := by
      intro q
      obtain ⟨T, hT, hTq⟩ := X.pend_forever q T2 (fun t ht => (hnr t ht q).2)
      exact ⟨T, fun t ht => ⟨(hTq t ht).1,
        X.pc_cases (hTq t ht).2.1 (hTq t ht).2.2 (hnr t (by omega) q).1⟩⟩
    obtain ⟨T3, hT3, hT3'⟩ := ev_forall_fin _ hact0 T2
    obtain ⟨j₀, hj₀L, hj₀D⟩ : ∃ j, j ≠ L ∧ ids j ∉ D := by
      by_contra hcon
      push Not at hcon
      have := X.card_ge_of_all D L hcon
      omega
    -- pending `⊥`-writes are fresh
    have hQ : ∀ q, ∃ T', ∀ t ≥ T', ∀ w, ((e.cfg t).loc q).pc = .write w → w.id = none →
        w.phase = .committing ∧ ∃ j, ids j ∈ w.disc ∧ ids j ∉ D := by
      intro q
      refine X.ev_flush q T3 _ ?_ ?_ ?_
      · intro t ht hq w hw hwid
        by_cases hpc : ((e.cfg t).loc q).pc = .read
        · have hloc := (X.act_read hq hpc).2.1
          rw [hloc] at hw
          obtain ⟨wid, Y, ph⟩ := w
          simp only at hwid; subst hwid
          rcases afterRead_write_none n _ _ hw with ⟨-, -, a, ha, -, hph'⟩ |
            ⟨a, ha, hne, hni, hY, hph', hnA⟩
          · exfalso
            have := ((hCo t (by omega)).some_val _ (hrv t) (by rw [ha]; simp)).1
            rw [hph'] at this; cases this
          · have hrph := ((hCo t (by omega)).some_val _ (hrv t) (by rw [ha]; simp)).1
            have hsph : ((e.cfg t).loc q).phase = .committing := by
              cases h : ((e.cfg t).loc q).phase
              · exact absurd ⟨hrph, h⟩ hnA
              · rfl
            refine ⟨by rw [hph', hsph], q, by rw [hY, ← X.me t q]; exact Finset.mem_insert_self _ _,
              fun hmem => ?_⟩
            have hmem' : ids q ∈ ((e.cfg (t + 1)).loc L).disc := by
              rw [hDc (t + 1) (by omega)]; exact hmem
            exact ((hCo (t + 1) (by omega)).quiet q hmem').2.1 _ (by rw [hloc]; exact hw)
        · exact absurd hw ((X.act_nonread hq hpc).2.2.2 w)
      · intro t ht hq hQ; rw [X.other hq]; exact hQ
      · intro hp; exact absurd hp (hT3' T3 le_rfl q).1
    obtain ⟨T4, hT4, hQ'⟩ := ev_forall_fin _ hQ T3
    -- infinitely many writes
    have hIW : ∀ t, ∃ t' ≥ t, WriteAt e t' := by
      intro t
      by_contra hcon
      push Not at hcon
      set t₁ := max t T4 with ht₁
      have hnw : ∀ t' ≥ t₁, ¬ WriteAt e t' := fun t' ht' => hcon t' (by omega)
      have hrd := fun q => X.read_nowrite q t₁ (fun t' ht' => (hT3' t' (by omega) q).1)
        (fun t' ht' => (hT3' t' (by omega) q).2) hnw
      obtain ⟨t', ht', hpc, -, hreg, hloc, hnw'⟩ := hrd L
      have hvid : ∃ a, (reg (e.cfg t₁)).id = some a := by
        rcases afterRead_cases n ((e.cfg t').loc L) (reg (e.cfg t')) with ⟨-, hA2, -⟩ |
          ⟨-, a, ha, -⟩ | ⟨-, a, ha, -⟩ | ⟨-, -, -, hs'⟩ | ⟨-, a, ha, -⟩ | ⟨-, -, hE1, -⟩
        · rw [hC t' (by omega)] at hA2; cases hA2
        · exact ⟨a, by rw [← hreg]; exact ha⟩
        · exact ⟨a, by rw [← hreg]; exact ha⟩
        · exact absurd (by rw [hs']) (hnw' _)
        · exact ⟨a, by rw [← hreg]; exact ha⟩
        · cases hv : (reg (e.cfg t')).id with
          | none => have := hE1 hv; rw [hLnl t' (by omega)] at this; cases this
          | some a => exact ⟨a, by rw [← hreg]; exact hv⟩
      obtain ⟨a, ha⟩ := hvid
      obtain ⟨t'', ht'', hpc', -, hreg', hloc', hnw''⟩ := hrd j₀
      rw [hreg'] at hnw'' hloc'
      have hsub := ((hCo t₁ (by omega)).some_val _ (hrv t₁) (by rw [ha]; simp)).2
      rw [hDc t₁ (by omega)] at hsub
      have hcard : (reg (e.cfg t₁)).disc.card < n - 1 := by
        have := Finset.card_le_card hsub; omega
      have haL := (hLd t₁ (by omega)).ids_val _ a (hrv t₁) ha
      have hme := X.me t'' j₀
      rcases afterRead_cases n ((e.cfg t'').loc j₀) (reg (e.cfg t₁)) with ⟨-, hA2, hs'⟩ |
        ⟨-, b, hb, hc, -⟩ | ⟨-, b, hb, hc, -⟩ | ⟨-, hid0, -⟩ | ⟨-, b, hb, -, -, -, hs'⟩ |
        ⟨-, -, -, hE2⟩
      · have h1 := (hph (t'' + 1) (by omega) j₀).1 (by rw [hloc', hs'])
        rw [← hph t'' (by omega) j₀] at h1
        rw [h1] at hA2; cases hA2
      · omega
      · omega
      · rw [ha] at hid0; cases hid0
      · exact hnw'' _ (by rw [hs'])
      · rcases (hE2 a ha).2 with h1 | h1
        · rw [hme, haL] at h1; exact hj₀L (X.hid h1).symm
        · rw [hme] at h1; exact hj₀D (hsub h1)
    -- eventually every `⊥`-value in `REG` is fresh
    obtain ⟨T5, hT5, hR⟩ := X.ev_write
      (fun t => (reg (e.cfg t)).id = none → (reg (e.cfg t)).phase = .committing ∧
        ∃ j, ids j ∈ (reg (e.cfg t)).disc ∧ ids j ∉ D) T4
      (fun t ht hR ha => by
        rcases X.reg_step t with h1 | ⟨q, w, -, hw, h1⟩
        · rw [h1] at ha ⊢; exact hR ha
        · rw [h1] at ha ⊢; exact hQ' t ht q w hw ha)
      (fun t ht ⟨q, w, hl, hw⟩ ha => by
        have h1 := (X.act_write (by rw [hl]; rfl) hw).2.2
        rw [h1] at ha ⊢; exact hQ' t ht q w hw ha) hIW
    -- the leader never reads `⊥` again, hence stops writing
    have hreadL : ∀ t ≥ T5, (e.lbl t).proc = L → ((e.cfg t).loc L).pc = .read →
        (reg (e.cfg t)).id ≠ none ∧
          (afterRead n ((e.cfg t).loc L) (reg (e.cfg t))).pc = .read := by
      intro t ht hq hpc
      obtain ⟨-, hloc, -⟩ := X.act_read hq hpc
      have hCt := hC t (by omega)
      rcases afterRead_cases n ((e.cfg t).loc L) (reg (e.cfg t)) with ⟨-, hA2, -⟩ |
        ⟨-, a, ha, hc, -⟩ | ⟨-, a, ha, -, hph', -⟩ | ⟨-, hid0, -, hs'⟩ | ⟨-, a, ha, -, hne, -⟩ |
        ⟨hs', -, hE1, -⟩
      · rw [hCt] at hA2; cases hA2
      · exfalso
        have hsub := ((hCo t (by omega)).some_val _ (hrv t) (by rw [ha]; simp)).2
        rw [hDc t (by omega)] at hsub
        have := Finset.card_le_card hsub; omega
      · exfalso
        have := ((hCo t (by omega)).some_val _ (hrv t) (by rw [ha]; simp)).1
        rw [hph'] at this; cases this
      · exfalso
        obtain ⟨hrph, j, hj, hjD⟩ := hR t (by omega) hid0
        have h1 := hDc (t + 1) (by omega)
        rw [hloc, hs'] at h1
        simp only at h1
        rw [ite_eq_left (by rw [hrph, hCt])] at h1
        exact hjD (by rw [← h1]; exact Finset.mem_union_right _ hj)
      · exfalso
        have haL := (hLd t (by omega)).ids_val _ a (hrv t) ha
        exact hne (by rw [haL, X.me])
      · refine ⟨fun hid0 => ?_, by rw [hs']⟩
        have := hE1 hid0; rw [hLnl t (by omega)] at this; cases this
    obtain ⟨T6, hT6⟩ := X.ev_flush L T5 (fun t => ∀ w, ((e.cfg t).loc L).pc ≠ .write w)
      (fun t ht hq w hw => by
        rcases (hT3' t (by omega) L).2 with h1 | ⟨w', h1⟩
        · rw [(X.act_read hq h1).2.1, (hreadL t ht hq h1).2] at hw; cases hw
        · rw [(X.act_write hq h1).2.1] at hw; cases hw)
      (fun t ht hq hQ => by rw [X.other hq]; exact hQ)
      (fun hp => absurd hp (hT3' T5 (by omega) L).1)
    obtain ⟨t₇, ht₇, q, w, hl, hw⟩ := hIW (max T6 T5)
    have hnone : ∀ t ≥ t₇ + 1, (reg (e.cfg t)).id = none := by
      have hw3 : ∀ t ≥ max T6 T5, ∀ q w, ((e.cfg t).loc q).pc = .write w → w.id = none := by
        intro t ht q w hw
        have hqL : q ≠ L := by rintro rfl; exact hT6 t (by omega) w hw
        exact hwnone t (by omega) q w hqL hw
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => rw [(X.act_write (by rw [hl]; rfl) hw).2.2]; exact hw3 t₇ ht₇ q w hw
      | succ t ht ih =>
        rcases X.reg_step t with h1 | ⟨q', w', -, hw', h1⟩
        · rw [h1]; exact ih
        · rw [h1]; exact hw3 t (by omega) q' w' hw'
    obtain ⟨t, ht, hq⟩ := InfExec.acts e X.fair (fun t ht => (hT3' t ht L).1)
      (max (t₇ + 1) (max T6 T3)) (by omega)
    rcases (hT3' t (by omega) L).2 with h1 | ⟨w', h1⟩
    · exact (hreadL t (by omega) hq h1).1 (hnone t (by omega))
    · exact hT6 t (by omega) w' h1

/-- **Termination**: in a fair infinite execution in which every process invokes `elect()`,
every process returns. -/
theorem terminates (p : P) : ∃ t r, e.lbl t = .ret p r := by
  by_contra H
  push Not at H
  have : Nonempty P := ⟨p⟩
  by_cases hL : ∃ t L, Lead ids n out (e.lbls t) (e.cfg t) L
  · obtain ⟨t₀, L, hL⟩ := hL
    exact X.phase2 L t₀ hL p H
  · push Not at hL
    exact X.phase1 (fun t => (X.inv t).2.resolve_right (fun ⟨L, h⟩ => hL t L h))

end Ctx

end BezoutElection.Alg1
