import Papers.PODC2021.AllYouNeedIsDAG.DagLayer

/-!
# DAG-Rider: properties of the DAG construction layer (Algorithm 2)

Keidar, Kokoris-Kogias, Naor, Spiegelman, *All You Need is DAG*, PODC 2021, Sections 4 and 6.

**Invariants** (every run, every process, no validity hypothesis):
* `st_dag_closed` (Claim 1), `st_dag_valid` (line 25), `st_dag_round` (`1 ≤ v.1 ≤ rnd`),
  monotonicity `st_rnd_mono`, `st_dag_mono`, `st_rnd_succ_le`, `st_rnd_one`;
* snapshots at `wave_ready(w)`: `snap_closed`, `snap_valid`, `snap_eq` (the snapshot is the DAG
  right after advancing from round `4w` to `4w + 1`), `snap_subset`, `snap_layer_card`
  (`2f + 1` vertices in round `wround w 4`), `completed_of_wavesDone`.

**Liveness** (valid runs, `Run.Valid`):
* `round_liveness` / `wave_liveness`: every correct process reaches every round / completes every
  wave;
* `claim2` (Claim 2), `claim7` (Claim 7);
* `content_of_delivered`, `content_of_correct`: a vertex of a correct source has the contents
  computed by Algorithm 2.

Round liveness and Claim 2 are proved jointly (`roundLive_succ`, `histLive_of_roundLive`): Claim 2
for DAGs held at rounds `≤ r` is proved by strong induction on the *time* at which the vertex was
added (a Byzantine vertex may have weak edges to vertices of its own or higher rounds, so an
induction on rounds as in the paper does not go through literally).
-/

namespace DagRider

open Finset

variable {P : Type*} {B : Type*} [DecidableEq P]

/-! ### One step of Algorithm 2 -/

section lstep

variable {f : ℕ} {G0 : Finset P} {C : Content P B} {s : LState P} {new : Finset (Vtx P)}
  {v : Vtx P}

lemma mem_lstep_dag : v ∈ (lstep f G0 C s new).dag ↔ v ∈ s.dag ∨
    ((v ∈ s.buf ∨ (v ∈ new ∧ 2 * f + 1 ≤ (C.strong v).card)) ∧
      1 ≤ v.1 ∧ v.1 ≤ s.rnd ∧ PredsIn G0 C s.dag v) := by
  unfold lstep
  simp only [apply_ite LState.dag, ite_self]
  simp [Finset.mem_filter]

lemma mem_lstep_buf : v ∈ (lstep f G0 C s new).buf ↔
    (v ∈ s.buf ∨ (v ∈ new ∧ 2 * f + 1 ≤ (C.strong v).card)) ∧
      ¬ (1 ≤ v.1 ∧ v.1 ≤ s.rnd ∧ PredsIn G0 C s.dag v) := by
  unfold lstep
  simp only [apply_ite LState.buf, ite_self]
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter]
  tauto

lemma lstep_rnd :
    (lstep f G0 C s new).rnd = if s.rnd = 0 ∨ 2 * f + 1 ≤ (layer (lstep f G0 C s new).dag s.rnd).card
      then s.rnd + 1 else s.rnd := by
  unfold lstep
  simp only [apply_ite LState.dag, ite_self]
  split_ifs <;> simp_all

lemma lstep_rnd_ge : s.rnd ≤ (lstep f G0 C s new).rnd := by
  rw [lstep_rnd]; split_ifs <;> omega

lemma lstep_rnd_le : (lstep f G0 C s new).rnd ≤ s.rnd + 1 := by
  rw [lstep_rnd]; split_ifs <;> omega

lemma lstep_dag_mono : s.dag ⊆ (lstep f G0 C s new).dag :=
  fun _ hv => mem_lstep_dag.2 (Or.inl hv)

/-- A vertex in the buffer, already in the DAG, or delivered with enough strong edges stays in
the buffer or the DAG. -/
lemma lstep_keep (h : v ∈ s.buf ∨ v ∈ s.dag ∨ (v ∈ new ∧ 2 * f + 1 ≤ (C.strong v).card)) :
    v ∈ (lstep f G0 C s new).buf ∨ v ∈ (lstep f G0 C s new).dag := by
  rw [mem_lstep_buf, mem_lstep_dag]
  by_cases hc : 1 ≤ v.1 ∧ v.1 ≤ s.rnd ∧ PredsIn G0 C s.dag v <;> tauto

/-- Lines 6–9: a buffered vertex whose predecessors are present is added. -/
lemma lstep_add (h : v ∈ s.buf ∨ v ∈ s.dag) (h1 : 1 ≤ v.1) (h2 : v.1 ≤ s.rnd)
    (h3 : PredsIn G0 C s.dag v) : v ∈ (lstep f G0 C s new).dag := by
  rw [mem_lstep_dag]; tauto

omit [DecidableEq P] in
lemma PredsIn.mono {D D' : Finset (Vtx P)} (h : PredsIn G0 C D v) (hDD : D ⊆ D') :
    PredsIn G0 C D' v := by
  refine ⟨fun x hx => ?_, fun u hu => ?_⟩
  · have := h.1 x hx
    split_ifs at this ⊢
    · exact this
    · exact hDD this
  · rcases h.2 u hu with h' | h'
    · exact Or.inl h'
    · exact Or.inr (hDD h')

end lstep

omit [DecidableEq P] in
lemma layer_mono {D D' : Finset (Vtx P)} (h : D ⊆ D') (r : ℕ) : layer D r ⊆ layer D' r :=
  Finset.filter_subset_filter _ h

omit [DecidableEq P] in
lemma mem_layer {D : Finset (Vtx P)} {r : ℕ} {v : Vtx P} : v ∈ layer D r ↔ v ∈ D ∧ v.1 = r := by
  simp [layer]

/-- The vertex created when advancing from round `r` references only vertices of the local DAG
(or genesis vertices), so it passes the check of line 7 there. -/
lemma CreatedOK.predsIn {G0 : Finset P} {blk : P → ℕ → B} {C : Content P B} {q : P} {r : ℕ}
    {D : Finset (Vtx P)} (h : CreatedOK G0 blk C q r D) : PredsIn G0 C D (r + 1, q) := by
  refine ⟨fun s hs => ?_, fun u hu => Or.inr (h.2.2.1 hu)⟩
  rw [h.2.1] at hs
  by_cases hr : r = 0
  · subst hr; simpa using hs
  · simp only [hr, ite_false, Finset.mem_image, mem_layer] at hs
    obtain ⟨x, ⟨hx, hx1⟩, rfl⟩ := hs
    have : (r, x.2) = x := Prod.ext hx1.symm rfl
    simp only [Nat.add_eq_right, hr, ite_false, Nat.add_sub_cancel]
    rwa [this]

/-! ### Invariants of a run (Claim 1 and friends) -/

section run

variable {f : ℕ} {G0 : Finset P} (R : Run P B) (p : P)

lemma st_zero : R.st f G0 p 0 = ⟨0, ∅, ∅⟩ := rfl

lemma st_succ (t : ℕ) : R.st f G0 p (t + 1) = lstep f G0 R.C (R.st f G0 p t) (R.dl p t) := rfl

lemma st_rnd_one : (R.st f G0 p 1).rnd = 1 := by
  rw [st_succ, lstep_rnd]; simp [st_zero]

lemma st_rnd_zero : (R.st f G0 p 0).rnd = 0 := rfl

lemma st_rnd_succ_le (t : ℕ) : (R.st f G0 p (t + 1)).rnd ≤ (R.st f G0 p t).rnd + 1 := by
  rw [st_succ]; exact lstep_rnd_le

lemma st_rnd_le_succ (t : ℕ) : (R.st f G0 p t).rnd ≤ (R.st f G0 p (t + 1)).rnd := by
  rw [st_succ]; exact lstep_rnd_ge

lemma st_rnd_mono : Monotone (fun t => (R.st f G0 p t).rnd) :=
  monotone_nat_of_le_succ (st_rnd_le_succ R p)

lemma st_dag_mono : Monotone (fun t => (R.st f G0 p t).dag) :=
  monotone_nat_of_le_succ (fun t => by rw [st_succ]; exact lstep_dag_mono)

lemma st_rnd_le {t t' : ℕ} (h : t ≤ t') : (R.st f G0 p t).rnd ≤ (R.st f G0 p t').rnd :=
  st_rnd_mono R p h

lemma st_dag_subset {t t' : ℕ} (h : t ≤ t') : (R.st f G0 p t).dag ⊆ (R.st f G0 p t').dag :=
  st_dag_mono R p h

/-- Vertices of a local DAG have rounds between `1` and the current round. -/
lemma st_dag_round (t : ℕ) : ∀ v ∈ (R.st f G0 p t).dag, 1 ≤ v.1 ∧ v.1 ≤ (R.st f G0 p t).rnd := by
  induction t with
  | zero => simp [st_zero]
  | succ t ih =>
    intro v hv
    have hle := st_rnd_le_succ (f := f) (G0 := G0) R p t
    rw [st_succ, mem_lstep_dag] at hv
    rcases hv with hv | ⟨-, h1, h2, -⟩
    · exact ⟨(ih v hv).1, (ih v hv).2.trans hle⟩
    · exact ⟨h1, h2.trans hle⟩

/-- Buffered vertices were delivered earlier and passed the check of line 25. -/
lemma st_buf_delivered (t : ℕ) : ∀ v ∈ (R.st f G0 p t).buf,
    2 * f + 1 ≤ (R.C.strong v).card ∧ ∃ t' < t, v ∈ R.dl p t' := by
  induction t with
  | zero => simp [st_zero]
  | succ t ih =>
    intro v hv
    rw [st_succ, mem_lstep_buf] at hv
    rcases hv.1 with hv | ⟨hv, hc⟩
    · obtain ⟨hc, t', ht', h'⟩ := ih v hv
      exact ⟨hc, t', by omega, h'⟩
    · exact ⟨hc, t, by omega, hv⟩

/-- Every vertex of a local DAG was delivered earlier and passed the check of line 25. -/
lemma st_dag_delivered (t : ℕ) : ∀ v ∈ (R.st f G0 p t).dag,
    2 * f + 1 ≤ (R.C.strong v).card ∧ ∃ t' < t, v ∈ R.dl p t' := by
  induction t with
  | zero => simp [st_zero]
  | succ t ih =>
    intro v hv
    rw [st_succ, mem_lstep_dag] at hv
    rcases hv with hv | ⟨hv | ⟨hv, hc⟩, -⟩
    · obtain ⟨hc, t', ht', h'⟩ := ih v hv
      exact ⟨hc, t', by omega, h'⟩
    · obtain ⟨hc, t', ht', h'⟩ := st_buf_delivered R p t v hv
      exact ⟨hc, t', by omega, h'⟩
    · exact ⟨hc, t, by omega, hv⟩

/-- Line 25: local DAGs only contain vertices with at least `2f + 1` strong edges. -/
theorem st_dag_valid (t : ℕ) : Valid f R.C (R.st f G0 p t).dag :=
  fun v hv => (st_dag_delivered R p t v hv).1

/-- **Claim 1**: a local DAG contains the causal history of each of its vertices. -/
theorem st_dag_closed (t : ℕ) : Closed R.C (R.st f G0 p t).dag := by
  induction t with
  | zero => simp [Closed, st_zero]
  | succ t ih =>
    intro v hv u he
    have hsub := st_dag_subset (f := f) (G0 := G0) R p (Nat.le_succ t)
    rw [st_succ, mem_lstep_dag] at hv
    rcases hv with hv | ⟨-, -, -, hpred⟩
    · exact hsub (ih v hv u he)
    · obtain ⟨hs | hw, hu1⟩ := he
      · have := hpred.1 u.2 hs.2
        have hv1 : v.1 ≠ 1 := by omega
        rw [ite_eq_right hv1] at this
        have heq : (v.1 - 1, u.2) = u := Prod.ext (by simp; omega) rfl
        exact hsub (heq ▸ this)
      · rcases hpred.2 u hw with h | h
        · omega
        · exact hsub h

/-- Witness of the moment a vertex was added to a local DAG (lines 6–9). -/
lemma st_dag_added (t : ℕ) : ∀ v ∈ (R.st f G0 p t).dag, ∃ s < t,
    PredsIn G0 R.C (R.st f G0 p s).dag v ∧ 1 ≤ v.1 ∧ v.1 ≤ (R.st f G0 p s).rnd ∧
      2 * f + 1 ≤ (R.C.strong v).card ∧ ∃ s' ≤ s, v ∈ R.dl p s' := by
  induction t with
  | zero => simp [st_zero]
  | succ t ih =>
    intro v hv
    rw [st_succ, mem_lstep_dag] at hv
    rcases hv with hv | ⟨hv, h1, h2, hpred⟩
    · obtain ⟨s, hs, h⟩ := ih v hv
      exact ⟨s, by omega, h⟩
    · refine ⟨t, by omega, hpred, h1, h2, ?_⟩
      rcases hv with hv | ⟨hv, hc⟩
      · obtain ⟨hc, t', ht', h'⟩ := st_buf_delivered R p t v hv
        exact ⟨hc, t', by omega, h'⟩
      · exact ⟨hc, t, le_rfl, hv⟩

/-- A delivered vertex with `≥ 2f + 1` strong edges stays in the buffer until it is added. -/
lemma st_persist {v : Vtx P} {t : ℕ} (hv : v ∈ R.dl p t) (hc : 2 * f + 1 ≤ (R.C.strong v).card) :
    ∀ t', t < t' → v ∈ (R.st f G0 p t').buf ∨ v ∈ (R.st f G0 p t').dag := by
  intro t' ht'
  induction t', ht' using Nat.le_induction with
  | base => rw [st_succ]; exact lstep_keep (Or.inr (Or.inr ⟨hv, hc⟩))
  | succ t' _ ih => rw [st_succ]; exact lstep_keep (by tauto)

/-- If a delivered vertex's predecessors are eventually present and the process eventually
reaches its round, the vertex is eventually added. -/
lemma st_add_eventually {v : Vtx P} {t0 T1 T3 : ℕ} (hv : v ∈ R.dl p t0)
    (hc : 2 * f + 1 ≤ (R.C.strong v).card) (hpred : PredsIn G0 R.C (R.st f G0 p T1).dag v)
    (h1 : 1 ≤ v.1) (h3 : v.1 ≤ (R.st f G0 p T3).rnd) : ∃ T, v ∈ (R.st f G0 p T).dag := by
  set T := max (max (t0 + 1) T1) T3
  refine ⟨T + 1, ?_⟩
  rcases st_persist R p hv hc T (by omega) with h | h
  · rw [st_succ]
    exact lstep_add (Or.inl h) h1 (h3.trans (st_rnd_le R p (by omega)))
      (hpred.mono (st_dag_subset R p (by omega)))
  · exact st_dag_subset R p (Nat.le_succ T) h

/-- Every element of a finite set that is eventually in `p`'s DAG: the whole set eventually is. -/
lemma eventually_subset (D : Finset (Vtx P)) (h : ∀ u ∈ D, ∃ t, u ∈ (R.st f G0 p t).dag) :
    ∃ T, D ⊆ (R.st f G0 p T).dag := by
  induction D using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | insert a D _ ih =>
    obtain ⟨Ta, ha⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨TD, hD⟩ := ih (fun u hu => h u (Finset.mem_insert_of_mem hu))
    refine ⟨max Ta TD, Finset.insert_subset_iff.2 ⟨st_dag_subset R p (le_max_left _ _) ha,
      hD.trans (st_dag_subset R p (le_max_right _ _))⟩⟩

/-- Rounds advance one at a time, so every round `1 ≤ r ≤ rnd` was entered at some step. -/
lemma exists_advance {r t : ℕ} (hr : 1 ≤ r) (h : r ≤ (R.st f G0 p t).rnd) :
    ∃ t0, (R.st f G0 p t0).rnd + 1 = r ∧ (R.st f G0 p (t0 + 1)).rnd = r := by
  induction t with
  | zero => simp [st_zero] at h; omega
  | succ t ih =>
    by_cases h' : r ≤ (R.st f G0 p t).rnd
    · exact ih h'
    · have := st_rnd_succ_le (f := f) (G0 := G0) R p t
      exact ⟨t, by omega, by omega⟩

/-- Line 10: a process advances from a round `r ≥ 1` only with `2f + 1` vertices of round `r`. -/
lemma advance_layer {t : ℕ} (h : (R.st f G0 p (t + 1)).rnd = (R.st f G0 p t).rnd + 1)
    (h0 : (R.st f G0 p t).rnd ≠ 0) :
    2 * f + 1 ≤ (layer (R.st f G0 p (t + 1)).dag (R.st f G0 p t).rnd).card := by
  rw [st_succ] at h ⊢
  rw [lstep_rnd] at h
  split_ifs at h with hc
  · tauto
  · omega

lemma advance_of_layer {t : ℕ}
    (h : 2 * f + 1 ≤ (layer (R.st f G0 p (t + 1)).dag (R.st f G0 p t).rnd).card) :
    (R.st f G0 p (t + 1)).rnd = (R.st f G0 p t).rnd + 1 := by
  rw [st_succ] at h ⊢
  rw [lstep_rnd, ite_eq_left (Or.inr h)]

/-! ### Snapshots at `wave_ready` -/

theorem snap_closed (w : ℕ) : Closed R.C (R.snap f G0 p w) := by
  unfold Run.snap
  split_ifs
  · exact st_dag_closed R p _
  · simp [Closed]

theorem snap_valid (w : ℕ) : Valid f R.C (R.snap f G0 p w) := by
  unfold Run.snap
  split_ifs
  · exact st_dag_valid R p _
  · simp [Valid]

/-- If `p` completes wave `w`, its snapshot is its DAG right after the step advancing from round
`4w` to `4w + 1` (where `wave_ready(w)` is signalled). -/
theorem snap_eq {w : ℕ} (h : ∃ t, 4 * w < (R.st f G0 p t).rnd) :
    ∃ t, (R.st f G0 p t).rnd = 4 * w ∧ (R.st f G0 p (t + 1)).rnd = 4 * w + 1 ∧
      R.snap f G0 p w = (R.st f G0 p (t + 1)).dag := by
  classical
  unfold Run.snap
  rw [dite_eq_left h]
  obtain ⟨n, hn⟩ : ∃ n, Nat.find h = n := ⟨_, rfl⟩
  have hspec := Nat.find_spec h
  rw [hn] at hspec ⊢
  cases n with
  | zero => simp [st_zero] at hspec
  | succ m =>
    have hmin : ¬ 4 * w < (R.st f G0 p m).rnd := Nat.find_min h (by omega)
    have := st_rnd_succ_le (f := f) (G0 := G0) R p m
    exact ⟨m, by omega, by omega, rfl⟩

/-- The snapshot of a completed wave is contained in all later DAGs. -/
theorem snap_subset {w t : ℕ} (h : 4 * w < (R.st f G0 p t).rnd) :
    R.snap f G0 p w ⊆ (R.st f G0 p t).dag := by
  obtain ⟨t0, h0, -, hs⟩ := snap_eq R p ⟨t, h⟩
  rw [hs]
  apply st_dag_subset
  by_contra hlt
  have := st_rnd_le (f := f) (G0 := G0) R p (show t ≤ t0 by omega)
  omega

lemma wround_four_eq {w : ℕ} (hw : 1 ≤ w) : wround w 4 = 4 * w := by
  unfold wround; omega

/-- When `wave_ready(w)` is signalled, the last round of wave `w` has `2f + 1` vertices. -/
theorem snap_layer_card {w : ℕ} (hw : 1 ≤ w) (h : ∃ t, 4 * w < (R.st f G0 p t).rnd) :
    2 * f + 1 ≤ (layer (R.snap f G0 p w) (wround w 4)).card := by
  obtain ⟨t, h0, h1, hs⟩ := snap_eq R p h
  rw [hs, wround_four_eq hw, ← h0]
  exact advance_layer R p (by omega) (by omega)

/-- If `p` has completed `w ≥ 1` waves (`wavesDone`), it signalled `wave_ready(w)`. -/
theorem completed_of_wavesDone {w t : ℕ} (hw : 1 ≤ w) (h : w ≤ R.wavesDone f G0 p t) :
    4 * w < (R.st f G0 p t).rnd := by
  unfold Run.wavesDone at h
  omega

end run

/-! ### Liveness (Claims 2 and 7, round liveness) -/

section live

variable [Fintype P] {f : ℕ} {G0 : Finset P} {blk : P → ℕ → B} {R : Run P B}

/-- Every correct process reaches round `r`. -/
def RoundLive (f : ℕ) (G0 : Finset P) (R : Run P B) (r : ℕ) : Prop :=
  ∀ q, q ∉ R.byz → ∃ t, r ≤ (R.st f G0 q t).rnd

/-- The DAG of a correct process at a time when its round is `≤ r` is eventually contained in
the DAG of every correct process. -/
def HistLive (f : ℕ) (G0 : Finset P) (R : Run P B) (r : ℕ) : Prop :=
  ∀ p, p ∉ R.byz → ∀ t, (R.st f G0 p t).rnd ≤ r →
    ∀ q, q ∉ R.byz → ∃ T, (R.st f G0 p t).dag ⊆ (R.st f G0 q T).dag

/-- Claim 2 up to round `r`, assuming every correct process reaches round `r`. By strong induction
on the time at which `p` added the vertex (Byzantine vertices may have weak edges to vertices of
higher rounds, so an induction on rounds would not work). -/
lemma histLive_of_roundLive (hV : R.Valid f G0 blk) {r : ℕ} (hL : RoundLive f G0 R r) :
    HistLive f G0 R r := by
  intro p hp t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro hr q hq
  apply eventually_subset
  intro v hv
  obtain ⟨s, hs, hpred, h1, hvr, hc, s', -, hdl⟩ := st_dag_added R p t v hv
  have hst := st_rnd_le (f := f) (G0 := G0) R p hs.le
  obtain ⟨T1, hT1⟩ := ih s hs (hst.trans hr) q hq
  obtain ⟨t2, ht2⟩ := hV.rbcAgreement p hp q hq s' v hdl
  obtain ⟨T3, hT3⟩ := hL q hq
  exact st_add_eventually R q ht2 hc (hpred.mono hT1) h1 ((hvr.trans hst).trans (hr.trans hT3))

/-- A vertex created by a correct process has at least `2f + 1` strong edges. -/
lemma created_card (hV : R.Valid f G0 blk) {q : P} (hq : q ∉ R.byz) {t : ℕ}
    (ht : (R.st f G0 q (t + 1)).rnd = (R.st f G0 q t).rnd + 1) :
    2 * f + 1 ≤ (R.C.strong ((R.st f G0 q t).rnd + 1, q)).card := by
  rw [(hV.created q hq t ht).2.1]
  split_ifs with h0
  · exact hV.card_G0.ge
  · rw [Finset.card_image_of_injOn]
    · exact advance_layer R q ht h0
    · intro x hx y hy hxy
      simp only [coe_filter, layer, Set.mem_ofPred_eq] at hx hy
      exact Prod.ext (hx.2.trans hy.2.symm) hxy

/-- Claim 7 for round `r`, from round liveness and Claim 2 up to round `r`. -/
lemma claim7_aux (hV : R.Valid f G0 blk) {r : ℕ} (hL : RoundLive f G0 R r) (hB : HistLive f G0 R r)
    {p q : P} (hp : p ∉ R.byz) (hq : q ∉ R.byz) (hr1 : 1 ≤ r) {t : ℕ}
    (hrt : r ≤ (R.st f G0 q t).rnd) : ∃ T, (r, q) ∈ (R.st f G0 p T).dag := by
  obtain ⟨t0, h0, h1⟩ := exists_advance R q hr1 hrt
  have hadv : (R.st f G0 q (t0 + 1)).rnd = (R.st f G0 q t0).rnd + 1 := by omega
  have hcr := hV.created q hq t0 hadv
  have hc := created_card hV hq hadv
  rw [h0] at hc
  obtain ⟨t2, ht2⟩ := hV.rbcValidity p hp q hq (t0 + 1) r hr1 h1.ge
  obtain ⟨T1, hT1⟩ := hB q hq (t0 + 1) h1.le p hp
  obtain ⟨T3, hT3⟩ := hL p hp
  have hpred := hcr.predsIn
  rw [h0] at hpred
  exact st_add_eventually R p ht2 hc (hpred.mono hT1) hr1 hT3

lemma card_correct (hV : R.Valid f G0 blk) : 2 * f + 1 ≤ (univ \ R.byz).card := by
  rw [Finset.card_univ_sdiff, hV.card]
  have := hV.card_byz
  omega

lemma roundLive_succ (hV : R.Valid f G0 blk) {r : ℕ} (hr1 : 1 ≤ r) (hL : RoundLive f G0 R r)
    (hB : HistLive f G0 R r) : RoundLive f G0 R (r + 1) := by
  intro p hp
  obtain ⟨T1, hT1⟩ := eventually_subset R p ((univ \ R.byz).image (fun q => (r, q))) (by
    intro u hu
    simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and] at hu
    obtain ⟨q, hq, rfl⟩ := hu
    obtain ⟨tq, htq⟩ := hL q hq
    exact claim7_aux hV hL hB hp hq hr1 htq)
  obtain ⟨T3, hT3⟩ := hL p hp
  obtain ⟨T, hT1T, hT3T⟩ : ∃ T, T1 ≤ T ∧ T3 ≤ T := ⟨max T1 T3, le_max_left _ _, le_max_right _ _⟩
  by_cases hT : r + 1 ≤ (R.st f G0 p T).rnd
  · exact ⟨T, hT⟩
  have hrT : (R.st f G0 p T).rnd = r := by
    have := st_rnd_le (f := f) (G0 := G0) R p hT3T
    omega
  refine ⟨T + 1, le_of_eq ?_⟩
  rw [advance_of_layer R p, hrT]
  rw [hrT]
  calc 2 * f + 1 ≤ (univ \ R.byz).card := card_correct hV
    _ = ((univ \ R.byz).image (fun q => (r, q))).card :=
        (Finset.card_image_of_injective _ (Prod.mk_right_injective r)).symm
    _ ≤ _ := by
        apply Finset.card_le_card
        intro u hu
        rw [mem_layer]
        refine ⟨st_dag_subset R p (show T1 ≤ T + 1 by omega) (hT1 hu), ?_⟩
        simp only [Finset.mem_image] at hu
        obtain ⟨q, -, rfl⟩ := hu
        rfl

/-- **Round liveness**: every correct process reaches every round (in particular it completes
every wave), assuming a valid run (RBC properties, `n = 3f + 1`, at most `f` Byzantine). -/
theorem round_liveness (hV : R.Valid f G0 blk) (r : ℕ) {p : P} (hp : p ∉ R.byz) :
    ∃ t, r ≤ (R.st f G0 p t).rnd := by
  induction r generalizing p with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact ⟨1, (st_rnd_one R p).ge⟩
    · exact roundLive_succ hV hr (fun q hq => ih hq) (histLive_of_roundLive hV fun q hq => ih hq)
        p hp

/-- Every correct process signals `wave_ready(w)` for every wave `w`. -/
theorem wave_liveness (hV : R.Valid f G0 blk) (w : ℕ) {p : P} (hp : p ∉ R.byz) :
    ∃ t, 4 * w < (R.st f G0 p t).rnd :=
  round_liveness hV (4 * w + 1) hp

/-- **Claim 2**: a vertex in the DAG of a correct process is eventually in the DAG of every
correct process. -/
theorem claim2 (hV : R.Valid f G0 blk) {p q : P} (hp : p ∉ R.byz) (hq : q ∉ R.byz) {t : ℕ}
    {v : Vtx P} (hv : v ∈ (R.st f G0 p t).dag) : ∃ t', v ∈ (R.st f G0 q t').dag := by
  obtain ⟨T, hT⟩ := histLive_of_roundLive hV (fun _ hq => round_liveness hV _ hq) p hp t le_rfl
    q hq
  exact ⟨T, hT hv⟩

/-- **Claim 7**: the vertex `(r, q)` broadcast by a correct process `q` (when it entered round `r`)
is eventually in the DAG of every correct process. -/
theorem claim7 (hV : R.Valid f G0 blk) {p q : P} (hp : p ∉ R.byz) (hq : q ∉ R.byz) {r t : ℕ}
    (hr1 : 1 ≤ r) (hrt : r ≤ (R.st f G0 q t).rnd) : ∃ t', (r, q) ∈ (R.st f G0 p t').dag :=
  claim7_aux hV (fun _ hq => round_liveness hV _ hq)
    (histLive_of_roundLive hV fun _ hq => round_liveness hV _ hq) hp hq hr1 hrt

/-- The contents of a vertex of a correct source delivered to a correct process are the ones
computed by its source when it entered that round. -/
theorem content_of_delivered (hV : R.Valid f G0 blk) {p q : P} (hp : p ∉ R.byz) (hq : q ∉ R.byz)
    {r t : ℕ} (h : (r, q) ∈ R.dl p t) :
    ∃ t0, (R.st f G0 q t0).rnd + 1 = r ∧ (R.st f G0 q (t0 + 1)).rnd = r ∧
      CreatedOK G0 blk R.C q (r - 1) (R.st f G0 q (t0 + 1)).dag := by
  obtain ⟨hr1, t', ht'⟩ := hV.auth p hp q hq t _ h rfl
  obtain ⟨t0, h0, h1⟩ := exists_advance R q hr1 ht'
  have hcr := hV.created q hq t0 (by omega)
  rw [show (R.st f G0 q t0).rnd = r - 1 by omega] at hcr
  exact ⟨t0, h0, h1, hcr⟩

/-- The contents of a vertex of a correct source in the DAG of a correct process are the ones
computed by its source. -/
theorem content_of_correct (hV : R.Valid f G0 blk) {p q : P} (hp : p ∉ R.byz) (hq : q ∉ R.byz)
    {r t : ℕ} (h : (r, q) ∈ (R.st f G0 p t).dag) :
    ∃ t0, (R.st f G0 q t0).rnd + 1 = r ∧ (R.st f G0 q (t0 + 1)).rnd = r ∧
      CreatedOK G0 blk R.C q (r - 1) (R.st f G0 q (t0 + 1)).dag := by
  obtain ⟨-, t', -, ht'⟩ := st_dag_delivered R p t _ h
  exact content_of_delivered hV hp hq ht'

end live

end DagRider
