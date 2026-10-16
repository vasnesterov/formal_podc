import Papers.PODC2021.AllYouNeedIsDAG.DagLayerProofs
import Papers.PODC2021.AllYouNeedIsDAG.Safety
import Papers.PODC2021.AllYouNeedIsDAG.CommonCore

/-!
# DAG-Rider as Byzantine Atomic Broadcast (Definition 3.1, Propositions 1–4)

Keidar, Kokoris-Kogias, Naor, Spiegelman, *All You Need is DAG*, PODC 2021, Section 6.1.

We combine the asynchronous DAG layer (`DagLayer.lean`, RBC as hypotheses) with the ordering
layer (`Ordering.lean`) and prove, for every valid run:

* `run_integrity` (Proposition 1) and `run_total_order` (Proposition 2): no further assumption.
* `run_agreement` (Proposition 3) and `run_validity` (Proposition 4): under the hypothesis that
  infinitely many waves are *good* (`Run.GoodWave`: in the DAG of every correct process, every
  vertex of the last round of the wave has a strong path to the wave's leader vertex, so every
  correct process commits it).

The probabilistic part of the paper (Claim 6) is exactly what justifies this hypothesis with
probability 1: `goodWave_of_core` shows that wave `w` is good as soon as the coin elects a member
of the common core of any `2f + 1` vertices of round `(w, 3)` (which is fixed before the coin is
revealed, `core_congr`, and has `≥ 2f + 1` members, `core_card`), and `Coin.lean` shows that an
adaptive adversary cannot prevent a good wave with probability more than `(f/(3f+1))^k` during
`k` consecutive waves.
-/

namespace DagRider

open Finset

variable {P : Type*} {B : Type*} [Fintype P] [DecidableEq P]
variable {f : ℕ} {G0 : Finset P} {blk : P → ℕ → B} {R : Run P B} {coin : ℕ → P}
  {sortV : Finset (Vtx P) → List (Vtx P)}

/-- Wave `w` is good: in the DAG of every correct process at `wave_ready(w)`, every vertex of
round `(w, 4)` has a strong path to the leader vertex of wave `w`. -/
def Run.GoodWave (f : ℕ) (G0 : Finset P) (coin : ℕ → P) (R : Run P B) (w : ℕ) : Prop :=
  ∀ p, p ∉ R.byz → ∀ u ∈ R.snap f G0 p w, u.1 = wround w 4 → SPath R.C u (lv coin w)

/-- A wave whose coin falls into the (robust) common core is good. -/
theorem goodWave_of_core (hV : R.Valid f G0 blk) (w : ℕ) (E3 : Finset P)
    (h : coin w ∈ core f R.C w E3) : R.GoodWave f G0 coin w :=
  fun p _ u hu hu4 =>
    sPath_of_mem_core (by rw [hV.card]) R.C w E3 hu4 (snap_valid R p w u hu) h

lemma card_le_of_valid (hV : R.Valid f G0 blk) : Fintype.card P ≤ 4 * f + 1 := by
  rw [hV.card]; omega

omit [Fintype P] in
lemma snap_ok (p : P) : ∀ w, Closed R.C (R.snap f G0 p w) ∧ Valid f R.C (R.snap f G0 p w) :=
  fun w => ⟨snap_closed R p w, snap_valid R p w⟩

/-! ### Safety for runs -/

omit [Fintype P] in
/-- **Proposition 1 (Integrity).** -/
theorem run_integrity (hsort : SortSpec sortV) (p : P) (t : ℕ) :
    (R.delivered f G0 coin sortV p t).Nodup :=
  integrity hsort _ _

/-- **Proposition 2 (Total order).** If a process outputs `m` before `m'` (at some time), then
any process that outputs `m'` (at any time) has output `m` before. -/
theorem run_total_order (hV : R.Valid f G0 blk) (hsort : SortSpec sortV) (p q : P) (t t' : ℕ)
    {m m' : Vtx P} (h : List.Sublist [m, m'] (R.delivered f G0 coin sortV p t))
    (hm' : m' ∈ R.delivered f G0 coin sortV q t') :
    List.Sublist [m, m'] (R.delivered f G0 coin sortV q t') :=
  total_order (card_le_of_valid hV) hsort (snap_ok p) (snap_ok q) _ _ h hm'

omit [Fintype P] in
/-- The outputs of a process only grow. -/
theorem delivered_mono (p : P) {t t' : ℕ} (h : t ≤ t') :
    R.delivered f G0 coin sortV p t <+: R.delivered f G0 coin sortV p t' := by
  apply orun_mono
  unfold Run.wavesDone
  have := st_rnd_le R p (f := f) (G0 := G0) h
  omega

/-! ### Liveness for runs -/

omit [Fintype P] in
lemma orun_decided_le (D : ℕ → Finset (Vtx P)) (W : ℕ) :
    (orun f R.C coin sortV D W).decided ≤ W := by
  induction W with
  | zero => exact le_rfl
  | succ W ih =>
    simp only [orun, waveReady]
    split
    · omega
    · split_ifs <;> (try dsimp only) <;> omega

omit [Fintype P] in
lemma orun_decided_mono (D : ℕ → Finset (Vtx P)) {W W' : ℕ} (h : W ≤ W') :
    (orun f R.C coin sortV D W).decided ≤ (orun f R.C coin sortV D W').decided := by
  induction h with
  | refl => exact le_rfl
  | step h ih =>
    refine le_trans ih ?_
    rename_i m
    have := orun_decided_le (f := f) (R := R) (coin := coin) (sortV := sortV) D m
    simp only [orun, waveReady]
    split
    · exact le_rfl
    · split_ifs <;> (try dsimp only) <;> omega

/-- In a good wave every correct process directly commits the leader. -/
lemma decided_of_good (hV : R.Valid f G0 blk) {q : P} (hq : q ∉ R.byz) {w : ℕ} (hw : 1 ≤ w)
    (hg : R.GoodWave f G0 coin w) :
    (orun f R.C coin sortV (R.snap f G0 q) w).decided = w ∧
      lv coin w ∈ R.snap f G0 q w := by
  have hcomp := wave_liveness hV w hq
  have hlay := snap_layer_card R q hw hcomp
  obtain ⟨u, hu⟩ : (layer (R.snap f G0 q w) (wround w 4)).Nonempty := by
    rw [← Finset.card_pos]; omega
  rw [mem_layer] at hu
  have hmem : lv coin w ∈ R.snap f G0 q w :=
    (snap_closed R q w).mem_of_sPath hu.1 (hg q hq u hu.1 hu.2)
  have hl : leader coin (R.snap f G0 q w) w = some (lv coin w) := by
    unfold leader; rw [ite_eq_left (by exact hmem)]; rfl
  have hc : 2 * f + 1 ≤ commitCount R.C (R.snap f G0 q w) (lv coin w) w := by
    refine le_trans hlay (Finset.card_le_card ?_)
    intro x hx
    rw [mem_layer] at hx
    exact Finset.mem_filter.2 ⟨hx.1, hx.2, hg q hq x hx.1 hx.2⟩
  refine ⟨?_, hmem⟩
  obtain ⟨W, rfl⟩ : ∃ W, w = W + 1 := ⟨w - 1, by omega⟩
  simp only [orun, waveReady, hl, hc, ↓reduceIte]

omit [Fintype P] [DecidableEq P] in
lemma mem_deliverOne_of_hist (hsort : SortSpec sortV) {C : Content P B} {D : Finset (Vtx P)}
    {L : List (Vtx P)} {v y : Vtx P} (hy : y ∈ hist C D v) : y ∈ deliverOne C sortV D L v := by
  classical
  unfold deliverOne
  by_cases hyL : y ∈ L
  · exact List.mem_append_left _ hyL
  · exact List.mem_append_right _ ((hsort _).2 y |>.2 (Finset.mem_filter.2 ⟨hy, hyL⟩))

omit [Fintype P] [DecidableEq P] in
lemma mem_deliverAll_of_hist (hsort : SortSpec sortV) {C : Content P B} {D : Finset (Vtx P)}
    {v y : Vtx P} (hy : y ∈ hist C D v) :
    ∀ (ls L : List (Vtx P)), v ∈ ls → y ∈ deliverAll C sortV D L ls := by
  intro ls
  induction ls with
  | nil => intro L h; simp at h
  | cons x ls ih =>
    intro L h
    simp only [deliverAll, List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact (prefix_deliverAll D _ ls).subset (mem_deliverOne_of_hist hsort hy)
    · exact ih _ h

omit [Fintype P] in
/-- After a direct commit of `v` the output contains the causal history of `v`. -/
lemma mem_delivered_of_path (hsort : SortSpec sortV) {s : OState P}
    (hs : OInv f R.C coin sortV s) (hd : 1 ≤ s.decided) {y : Vtx P}
    (hy : Path R.C (lv coin s.decided) y) : y ∈ s.delivered := by
  rcases hs with ⟨h0, -⟩ | ⟨-, D, hD, -, hv, hdel⟩
  · omega
  rw [hdel]
  exact mem_deliverAll_of_hist hsort (mem_hist.2 ⟨hD.mem_of_path hv hy, hy⟩) _ _
    (by simp [fullChain])

/-- **Proposition 3 (Agreement).** If infinitely many waves are good, then every block output by a
correct process is eventually output by every correct process. -/
theorem run_agreement (hV : R.Valid f G0 blk)
    (hgood : ∀ w₀, ∃ w, w₀ ≤ w ∧ 1 ≤ w ∧ R.GoodWave f G0 coin w)
    {p q : P} (_hp : p ∉ R.byz) (hq : q ∉ R.byz) {t : ℕ} {x : Vtx P}
    (hx : x ∈ R.delivered f G0 coin sortV p t) :
    ∃ t', x ∈ R.delivered f G0 coin sortV q t' := by
  have hP := card_le_of_valid hV
  set W := R.wavesDone f G0 p t
  have hs := (orun_inv (coin := coin) (sortV := sortV) hP (snap_ok (R := R) (f := f) (G0 := G0) p)
    W).1
  obtain ⟨w, hw0, hw1, hg⟩ := hgood ((orun f R.C coin sortV (R.snap f G0 p) W).decided + 1)
  obtain ⟨t', ht'⟩ := wave_liveness hV w hq
  refine ⟨t', ?_⟩
  have hW' : w ≤ R.wavesDone f G0 q t' := by unfold Run.wavesDone; omega
  have hd := orun_decided_mono (f := f) (R := R) (coin := coin) (sortV := sortV) (R.snap f G0 q) hW'
  rw [(decided_of_good hV hq hw1 hg).1] at hd
  have hs' := (orun_inv (coin := coin) (sortV := sortV) hP (snap_ok (R := R) (f := f) (G0 := G0) q)
    (R.wavesDone f G0 q t')).1
  exact (prefix_of_inv hP hs hs' (by omega)).subset hx

/-- **Proposition 4 (Validity).** If infinitely many waves are good, then for every correct `p`
and round `r ≥ 1`, the vertex `(r, p)` carries the block `blk p r` that `p` `a_bcast` for round `r`,
and it is eventually output by every correct process. -/
theorem run_validity (hV : R.Valid f G0 blk) (hsort : SortSpec sortV)
    (hgood : ∀ w₀, ∃ w, w₀ ≤ w ∧ 1 ≤ w ∧ R.GoodWave f G0 coin w)
    {p q : P} (hp : p ∉ R.byz) (hq : q ∉ R.byz) {r : ℕ} (hr : 1 ≤ r) :
    R.C.block (r, p) = blk p r ∧ ∃ t, (r, p) ∈ R.delivered f G0 coin sortV q t := by
  classical
  have hP := card_le_of_valid hV
  -- `p` broadcasts `(r, p)`, which reaches every correct DAG
  obtain ⟨tp, htp⟩ := round_liveness hV r hp
  have hin : ∀ k, ∃ t, k ∉ R.byz → (r, p) ∈ (R.st f G0 k t).dag := by
    intro k
    by_cases hk : k ∉ R.byz
    · obtain ⟨t, ht⟩ := claim7 hV hk hp hr htp; exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose T hT using hin
  refine ⟨?_, ?_⟩
  · obtain ⟨t0, -, -, hc⟩ := content_of_correct hV hp hp (hT p hp)
    have := hc.1
    rwa [show r - 1 + 1 = r by omega] at this
  set R0 := (univ.sup fun k => (R.st f G0 k (T k)).rnd) + 1 with hR0
  have hTle : ∀ k, (R.st f G0 k (T k)).rnd < R0 := fun k => by
    have := Finset.le_sup (f := fun k => (R.st f G0 k (T k)).rnd) (Finset.mem_univ k); omega
  -- Lemma A: correct vertices of round `≥ R0` reach `(r, p)`
  have hA : ∀ k, k ∉ R.byz → ∀ ρ, R0 ≤ ρ → ∀ p', p' ∉ R.byz → ∀ t',
      (ρ, k) ∈ (R.st f G0 p' t').dag → Path R.C (ρ, k) (r, p) := by
    intro k hk ρ hρ p' hp' t' hmem
    obtain ⟨t0, h0, h1, hc⟩ := content_of_correct hV hp' hk hmem
    obtain ⟨-, hstrong, -, hpath⟩ := hc
    rw [show ρ - 1 + 1 = ρ by omega] at hstrong hpath
    have hTt : T k ≤ t0 + 1 := by
      by_contra hlt
      have := st_rnd_le R k (f := f) (G0 := G0) (show t0 + 1 ≤ T k by omega)
      have := hTle k
      omega
    have hrD : (r, p) ∈ (R.st f G0 k (t0 + 1)).dag := st_dag_subset R k hTt (hT k hk)
    have hrk := (st_dag_round R k (T k) _ (hT k hk)).2
    have := hTle k
    by_cases h2 : r + 2 ≤ ρ
    · exact hpath _ hrD h2
    · have hr' : r = ρ - 1 := by simp at hrk; omega
      have hps : p ∈ R.C.strong (ρ, k) := by
        simp only [hstrong, show ¬(ρ - 1 = 0) by omega, ↓reduceIte]
        exact Finset.mem_image.2 ⟨(r, p), mem_layer.2 ⟨hrD, by simp [hr']⟩, rfl⟩
      exact Relation.ReflTransGen.single ⟨Or.inl ⟨by simp; omega, hps⟩, hr⟩
  -- Lemma B: every vertex of a correct DAG of round `≥ R0 + 1` reaches `(r, p)`
  have hB : ∀ p', p' ∉ R.byz → ∀ t', ∀ u ∈ (R.st f G0 p' t').dag, R0 + 1 ≤ u.1 →
      Path R.C u (r, p) := by
    intro p' hp' t' u hu hu1
    have hcard := st_dag_valid R p' t' u hu
    obtain ⟨k, hks, hk⟩ : ∃ k ∈ R.C.strong u, k ∉ R.byz := by
      by_contra hcon
      push Not at hcon
      have := Finset.card_le_card (fun k hk => hcon k hk)
      have := hV.card_byz
      omega
    have e : Edge R.C u (u.1 - 1, k) := ⟨Or.inl ⟨by simp; omega, hks⟩, by simp; omega⟩
    have hmem := st_dag_closed R p' t' u hu _ e
    exact Relation.ReflTransGen.head e (hA k hk _ (by show R0 ≤ u.1 - 1; omega) p' hp' t' hmem)
  -- a good wave late enough
  obtain ⟨w, hw0, hw1, hg⟩ := hgood (R0 + 1)
  obtain ⟨hdec, hmem⟩ := decided_of_good (sortV := sortV) hV hq hw1 hg
  obtain ⟨ts, -, -, hsnap⟩ := snap_eq R q (wave_liveness hV w hq)
  have hpath : Path R.C (lv coin w) (r, p) :=
    hB q hq (ts + 1) _ (hsnap ▸ hmem) (by simp only [lv, wround]; omega)
  have hs := (orun_inv (coin := coin) (sortV := sortV) hP (snap_ok (R := R) (f := f) (G0 := G0) q)
    w).1
  have hdel := mem_delivered_of_path (R := R) hsort hs (by rw [hdec]; exact hw1)
    (by rw [hdec]; exact hpath)
  obtain ⟨t', ht'⟩ := wave_liveness hV w hq
  refine ⟨t', (orun_mono _ ?_).subset hdel⟩
  unfold Run.wavesDone; omega

end DagRider
