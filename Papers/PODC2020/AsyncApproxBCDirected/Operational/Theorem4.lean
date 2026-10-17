import Papers.PODC2020.AsyncApproxBCDirected.Operational.Rounds
import Papers.PODC2020.AsyncApproxBCDirected.Main

/-!
# Theorem 4, end to end

In the asynchronous Byzantine message-passing model of `AsyncModel.lean`, with inputs in a known
range `[0, K]` and `K > ε > 0`:

  some algorithm solves approximate Byzantine consensus on `G` with up to `f` faults
  **iff** `G` satisfies 3-reach (`theorem4`).

Sufficiency is witnessed by the operational Algorithm BW + Filter-and-Average run for
`outRound K ε` rounds (`bw_solves`; for `n ≤ 1` a trivial algorithm), necessity is
`threeReach_of_solvesOn`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

open Cslib.ApproxConsensus Cslib.ApproxConsensus.Async

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Decisions in runs -/

section Dec

variable {M S : Type*} (A : Algorithm V M S) (G : Digraph V) [DecidableRel G.Adj] (B : Finset V)
  (inp : V → ℝ) (ev : ℕ → Event V M)

theorem dec_step (C : Config V M S) (e : Event V M) (v : V) :
    ((step A G B C e).dec v = C.dec v ∧ (step A G B C e).st v = C.st v) ∨
      ∃ u m, (step A G B C e).st v = (A.recv v (C.st v) u m).1 ∧
        (step A G B C e).dec v = (C.dec v).or (A.out v (A.recv v (C.st v) u m).1) := by
  cases e with
  | deliver x y =>
    rcases hc : C.chan x y with _ | ⟨m, rest⟩
    · left; simp [step, hc]
    · by_cases hy : y ∈ B
      · left; simp [step, hc, hy]
      · by_cases hv : v = y
        · subst hv; right; exact ⟨x, m, by simp [step, hc, hy, process, Config.pop]⟩
        · left; simp [step, hc, hy, process, Config.pop, hv]
  | byz x y m =>
    by_cases h : x ∈ B ∧ y ∉ B ∧ G.Adj x y ∧ x ≠ y
    · by_cases hv : v = y
      · subst hv; right
        exact ⟨x, m, by rw [step, ite_eq_left_of_eq_true _ _ (eq_true h)]; simp [process]⟩
      · left; rw [step, ite_eq_left_of_eq_true _ _ (eq_true h)]; simp [process, hv]
    · left; simp [step, h]
  | skip => left; simp [step]

/-- A decision is an output of the node at some earlier time. -/
theorem dec_spec {t : ℕ} {v : V} {y : ℝ} (h : (run A G B inp ev t).dec v = some y) :
    ∃ t' ≤ t, A.out v ((run A G B inp ev t').st v) = some y := by
  induction t with
  | zero => exact ⟨0, le_rfl, h⟩
  | succ t ih =>
    rcases dec_step A G B (run A G B inp ev t) (ev t) v with ⟨h1, -⟩ | ⟨u, m, h1, h2⟩
    · simp only [run] at h; rw [h1] at h
      obtain ⟨t', ht', h'⟩ := ih h; exact ⟨t', by omega, h'⟩
    · simp only [run] at h; rw [h2] at h
      rcases hd : (run A G B inp ev t).dec v with _ | y'
      · rw [hd, Option.none_or] at h
        exact ⟨t + 1, le_rfl, by simp only [run]; rw [h1]; exact h⟩
      · rw [hd, Option.some_or] at h
        obtain ⟨t', ht', h'⟩ := ih (by rw [hd, h])
        exact ⟨t', by omega, h'⟩

/-- Once a node has an output, it has decided. -/
theorem dec_isSome {t : ℕ} {v : V} (h : (A.out v ((run A G B inp ev t).st v)).isSome) :
    ((run A G B inp ev t).dec v).isSome := by
  induction t with
  | zero => simpa [run, init] using h
  | succ t ih =>
    rcases dec_step A G B (run A G B inp ev t) (ev t) v with ⟨h1, h2⟩ | ⟨u, m, h1, h2⟩
    · simp only [run] at h ⊢; rw [h1]; rw [h2] at h; exact ih h
    · simp only [run] at h ⊢; rw [h2]; rw [h1] at h
      rcases hd : (run A G B inp ev t).dec v with _ | y'
      · simpa using h
      · simp

end Dec

/-! ## Algorithm BW solves approximate consensus -/

namespace BWOp

variable (G : Digraph V) [DecidableRel G.Adj] (f N : ℕ) (B : Finset V) (inp : V → ℝ)
  (ev : ℕ → Event V (BMsg V))

theorem Xr_zero {v : V} : Xr G f N B inp ev 0 v = inp v :=
  (xv_hst_eq G f N B inp ev (r := 0) (t := 0) (by simp [xv])).symm

/-- The round values of a fair run halve their spread in every round (Lemma 15, Theorem 16). -/
theorem interval (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) (hB : B.card ≤ f)
    (hfair : Fair (alg G f N) G B inp ev) {lo hi : ℝ} (hlh : lo ≤ hi)
    (h0 : ∀ w ∉ B, lo ≤ inp w ∧ inp w ≤ hi) :
    ∀ r ≤ N, ∃ lo' hi', lo ≤ lo' ∧ lo' ≤ hi' ∧ hi' ≤ hi ∧ hi' - lo' ≤ (hi - lo) / 2 ^ r ∧
      ∀ v ∉ B, lo' ≤ Xr G f N B inp ev r v ∧ Xr G f N B inp ev r v ≤ hi' := by
  classical
  intro r
  induction r with
  | zero =>
    intro _
    exact ⟨lo, hi, le_rfl, hlh, le_rfl, by simp, fun v hv => by
      rw [Xr_zero]; exact h0 v hv⟩
  | succ r ih =>
    intro hr
    obtain ⟨lo', hi', h1, h2, h3, h4, h5⟩ := ih (by omega)
    have hs := started_all G f N B inp ev hG hn hB hfair r (by omega)
    set E := mkRound (r := r) (by omega) hB hfair hs
    have hout : ∀ v ∉ B, E.Output v (Xr G f N B inp ev (r + 1) v) := by
      intro v hv
      obtain ⟨t, y, hy, ho⟩ := output_next G f N B inp ev hG hn (by omega) hB hfair hs hv
      rwa [← xv_hst_eq G f N B inp ev hy]
    have hx : ∀ w ∉ E.F, lo' ≤ E.x w ∧ E.x w ≤ hi' := h5
    set C := univ.filter fun v => v ∉ B
    by_cases hC : C.Nonempty
    · have hval : ∀ v ∉ B, lo' ≤ Xr G f N B inp ev (r + 1) v ∧
          Xr G f N B inp ev (r + 1) v ≤ hi' := fun v hv => E.output_valid hv (hout v hv) hx
      obtain ⟨a, ha, hae⟩ := C.exists_mem_eq_inf' hC (Xr G f N B inp ev (r + 1))
      obtain ⟨b, hb, hbe⟩ := C.exists_mem_eq_sup' hC (Xr G f N B inp ev (r + 1))
      have haF : a ∉ B := (mem_filter.mp ha).2
      have hbF : b ∉ B := (mem_filter.mp hb).2
      refine ⟨C.inf' hC (Xr G f N B inp ev (r + 1)), C.sup' hC (Xr G f N B inp ev (r + 1)),
        ?_, (C.inf'_le _ ha).trans (C.le_sup' _ ha), ?_, ?_, fun v hv => ?_⟩
      · rw [hae]; linarith [(hval a haF).1]
      · rw [hbe]; linarith [(hval b hbF).2]
      · rw [hae, hbe, pow_succ]
        have := (abs_le.mp (E.output_conv hG hn hbF haF (hout b hbF) (hout a haF) hx)).2
        calc Xr G f N B inp ev (r + 1) b - Xr G f N B inp ev (r + 1) a ≤ (hi' - lo') / 2 := this
          _ ≤ (hi - lo) / 2 ^ r / 2 := by linarith
          _ = (hi - lo) / (2 ^ r * 2) := by rw [div_div]
      · have hvC : v ∈ C := mem_filter.mpr ⟨mem_univ _, hv⟩
        exact ⟨C.inf'_le _ hvC, C.le_sup' _ hvC⟩
    · refine ⟨lo, lo, le_rfl, le_rfl, hlh, by
        simp only [sub_self]; exact div_nonneg (by linarith) (by positivity), fun v hv => ?_⟩
      exact absurd ⟨v, mem_filter.mpr ⟨mem_univ _, hv⟩⟩ hC

/-- Decisions are the round-`N` values. -/
theorem dec_eq {t : ℕ} {v : V} {y : ℝ}
    (h : (run (alg G f N) G B inp ev t).dec v = some y) : y = Xr G f N B inp ev N v := by
  obtain ⟨t', -, h'⟩ := dec_spec (alg G f N) G B inp ev h
  have : (alg G f N).out v ((run (alg G f N) G B inp ev t').st v) =
      xv G f N v (inp v) N (hst G f N B inp ev t' v) := by
    have e1 : (alg G f N).out v ((run (alg G f N) G B inp ev t').st v) =
        (spec G f N).out v ((run (spec G f N).toAlg G B inp ev t').st v).1
          ((run (spec G f N).toAlg G B inp ev t').st v).2 := rfl
    rw [e1, (spec G f N).fst_st G B inp ev t' v]; rfl
  rw [this] at h'
  exact xv_hst_eq G f N B inp ev h'

/-- **Sufficiency (Theorem 4)**: under 3-reach with `n ≥ 2`, the operational Algorithm BW +
Filter-and-Average with `outRound K ε` rounds solves approximate Byzantine consensus for inputs
in `[0, K]`. -/
theorem bw_solves (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {K ε : ℝ} (hε : 0 < ε) :
    SolvesOn (Set.Icc 0 K) (alg G f (Exec.outRound K ε)) G f ε := by
  classical
  intro B hB inp hinp ev
  set N := Exec.outRound K ε
  have hK : 0 ≤ K := by
    obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    exact (hinp v).1.trans (hinp v).2
  -- facts about fair runs
  have fairFacts : ∀ ev' : ℕ → Event V (BMsg V), Fair (alg G f N) G B inp ev' →
      (∀ v ∉ B, ∀ u ∉ B, |Xr G f N B inp ev' N v - Xr G f N B inp ev' N u| < ε) ∧
      (∀ v ∉ B, (∃ w ∉ B, inp w ≤ Xr G f N B inp ev' N v) ∧
        ∃ w ∉ B, Xr G f N B inp ev' N v ≤ inp w) := by
    intro ev' hfair
    refine ⟨fun v hv u hu => ?_, fun v hv => ?_⟩
    · obtain ⟨lo', hi', -, -, -, h4, h5⟩ := interval G f N B inp ev' hG hn hB hfair hK
        (fun w _ => hinp w) N le_rfl
      have h2 : (0 : ℝ) < 2 ^ N := by positivity
      have h3 : (K - 0) / 2 ^ N < ε := by
        rw [sub_zero, div_lt_iff₀ h2]; linarith [Exec.lt_outRound K ε hε]
      rw [abs_lt]; constructor <;> linarith [h5 v hv, h5 u hu]
    · set C := univ.filter fun w => w ∉ B
      have hC : C.Nonempty := ⟨v, mem_filter.mpr ⟨mem_univ _, hv⟩⟩
      obtain ⟨a, ha, hae⟩ := C.exists_mem_eq_inf' hC inp
      obtain ⟨b, hb, hbe⟩ := C.exists_mem_eq_sup' hC inp
      have h0 : ∀ w ∉ B, C.inf' hC inp ≤ inp w ∧ inp w ≤ C.sup' hC inp :=
        fun w hw => ⟨C.inf'_le _ (mem_filter.mpr ⟨mem_univ _, hw⟩),
          C.le_sup' _ (mem_filter.mpr ⟨mem_univ _, hw⟩)⟩
      obtain ⟨lo', hi', h1, -, h3, -, h5⟩ := interval G f N B inp ev' hG hn hB hfair
        ((C.inf'_le _ ha).trans (C.le_sup' _ ha)) h0 N le_rfl
      exact ⟨⟨a, (mem_filter.mp ha).2, by rw [← hae]; linarith [(h5 v hv).1]⟩,
        ⟨b, (mem_filter.mp hb).2, by rw [← hbe]; linarith [(h5 v hv).2]⟩⟩
  refine ⟨fun t v u y z hv hu hy hz => ?_, fun t v y hv hy => ?_, fun hfair v hv => ?_⟩
  · obtain ⟨ev', hfair', hrun⟩ := exists_fair_extension (alg G f N) G B inp ev t
    rw [← hrun t le_rfl] at hy hz
    rw [dec_eq G f N B inp ev' hy, dec_eq G f N B inp ev' hz]
    exact ((fairFacts ev' hfair').1 v hv u hu).le
  · obtain ⟨ev', hfair', hrun⟩ := exists_fair_extension (alg G f N) G B inp ev t
    rw [← hrun t le_rfl] at hy
    rw [dec_eq G f N B inp ev' hy]
    exact (fairFacts ev' hfair').2 v hv
  · obtain ⟨t, ht⟩ := started_all G f N B inp ev hG hn hB hfair N le_rfl v hv
    have hout : ((alg G f N).out v ((run (alg G f N) G B inp ev t).st v)).isSome := by
      have e1 : (alg G f N).out v ((run (alg G f N) G B inp ev t).st v) =
          (spec G f N).out v ((run (spec G f N).toAlg G B inp ev t).st v).1
            ((run (spec G f N).toAlg G B inp ev t).st v).2 := rfl
      rw [e1, (spec G f N).fst_st G B inp ev t v]; exact ht
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (dec_isSome (alg G f N) G B inp ev hout)
    exact ⟨t, y, hy⟩

end BWOp

/-! ## The trivial case `n ≤ 1` -/

/-- Decide the own input immediately. -/
def trivAlg (V : Type*) : Algorithm V Unit ℝ where
  start _ x := (x, [])
  recv _ s _ _ := (s, [])
  out _ s := some s

theorem trivAlg_solves (G : Digraph V) [DecidableRel G.Adj] (f : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) (hn : Fintype.card V ≤ 1) (I : Set ℝ) : SolvesOn I (trivAlg V) G f ε := by
  intro B _ inp _ ev
  have hst : ∀ t v, (run (trivAlg V) G B inp ev t).st v = inp v := by
    intro t v
    induction t with
    | zero => rfl
    | succ t ih =>
      rcases step_st (trivAlg V) G B (run (trivAlg V) G B inp ev t) (ev t) v with h | ⟨u, m, h⟩
      · simp only [run]; rw [h, ih]
      · simp only [run]; rw [h]; exact ih
  have hdec : ∀ t v y, (run (trivAlg V) G B inp ev t).dec v = some y → y = inp v := by
    intro t v y h
    obtain ⟨t', -, h'⟩ := dec_spec (trivAlg V) G B inp ev h
    rw [hst] at h'
    simp only [trivAlg, Option.some.injEq] at h'
    exact h'.symm
  refine ⟨fun t v u y z _ _ hy hz => ?_, fun t v y hv hy => ?_, fun _ v _ => ⟨0, inp v, rfl⟩⟩
  · have huv : u = v := Fintype.card_le_one_iff.mp hn u v
    subst huv
    rw [hdec t u y hy, hdec t u z hz]; simpa using hε
  · rw [hdec t v y hy]; exact ⟨⟨v, hv, le_rfl⟩, ⟨v, hv, le_rfl⟩⟩

/-! ## Theorem 4 -/

/-- **Theorem 4** (Sakavalas–Tseng–Vaidya, PODC 2020), end to end in the asynchronous Byzantine
message-passing model of `AsyncModel.lean`: for inputs in a known range `[0, K]` with
`0 < ε < K`, asynchronous approximate Byzantine consensus with up to `f` faults is solvable on the
directed graph `G` **iff** `G` satisfies 3-reach. -/
theorem theorem4 {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (f : ℕ) {K ε : ℝ} (hε : 0 < ε) (hεK : ε < K) :
    (∃ (M S : Type) (A : Algorithm V M S), SolvesOn (Set.Icc 0 K) A G f ε) ↔ ThreeReach G f := by
  constructor
  · rintro ⟨M, S, A, hA⟩
    exact threeReach_of_solvesOn (a := 0) (b := K) (by simp; linarith) (by simp; linarith)
      (by linarith) hA
  · intro hG
    by_cases hn : 2 ≤ Fintype.card V
    · exact ⟨_, _, _, BWOp.bw_solves G f hG hn hε⟩
    · exact ⟨_, _, trivAlg V, trivAlg_solves G f hε.le (by omega) _⟩

end AsyncApproxBCDirected
