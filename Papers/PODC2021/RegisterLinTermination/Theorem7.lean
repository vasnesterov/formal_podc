import Papers.PODC2021.RegisterLinTermination.Theorem7Core
import Cslib.Probability.CoinField

/-!
# Theorem 7: write strong-linearizability ensures termination

Hadzilacos, Hu and Toueg, *On Register Linearizability and Termination*, PODC 2021, Section 3.2
and Appendix A.

The coins are i.i.d. fair (`fairCoins`, CSLib's `coinMeasure` with `p = 1/2`). The deterministic
core (`Thm7.forever_subsingleton`, file `Theorem7Core.lean`) shows that against a fixed strong
adversary at most **one** coin sequence lets the game go on forever; a single point has measure
zero (`fairCoins_singleton`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Podc.RegisterLinTermination.Game

open Cslib.SharedMemory Cslib.Probability

/-- The bias `1/2`. -/
noncomputable def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- i.i.d. fair coins `ω : ℕ → Bool`. -/
noncomputable abbrev fairCoins : Measure (ℕ → Bool) := coinMeasure (ι := ℕ) half

lemma ber_half_singleton (b : Bool) : Ber(true, false, half) {b} = 2⁻¹ := by
  classical
  rw [bernoulliMeasure_apply _ (measurableSet_singleton _)]
  have h1 : ((unitInterval.toNNReal half : NNReal) : ℝ≥0∞) = 2⁻¹ := by
    rw [show (unitInterval.toNNReal half : NNReal) = 2⁻¹ from NNReal.eq (by simp [half])]; simp
  have h2 : ((unitInterval.toNNReal (unitInterval.symm half) : NNReal) : ℝ≥0∞) = 2⁻¹ := by
    rw [show (unitInterval.toNNReal (unitInterval.symm half) : NNReal) = 2⁻¹ from
      NNReal.eq (by simp [half]; norm_num)]
    simp
  cases b <;> simp [h1, h2]

/-- A single coin sequence has probability zero. -/
lemma fairCoins_singleton (w : ℕ → Bool) : fairCoins {w} = 0 := by
  have hK : ∀ K : ℕ, fairCoins {w} ≤ 2⁻¹ ^ K := by
    intro K
    calc fairCoins {w} ≤ fairCoins (Set.pi (Finset.range K : Set ℕ) (fun i => {w i})) :=
          measure_mono (by intro ω hω; rw [Set.mem_singleton_iff] at hω; subst hω; simp)
      _ = ∏ i ∈ Finset.range K, Ber(true, false, half) {w i} := by
          rw [fairCoins, coinMeasure,
            Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
      _ = 2⁻¹ ^ K := by simp [ber_half_singleton]
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num)) hK) bot_le

/-- **Theorem 7** of Hadzilacos–Hu–Toueg (PODC 2021). Let `σ` be a strong adversary for
Algorithm 1 (`n ≥ 3` processes) whose runs follow the code, have linearizable registers, and admit
a write strong-linearization function `f` for `R1` (along the runs of `σ`). Then, with fair i.i.d.
coins, with probability `1` some round is never entered (all processes return). -/
theorem theorem7 (n : ℕ) (hn : 3 ≤ n) (σ : List (Ev n) → Ev n)
    (hvalid : ∀ ω m, Valid (genRun σ ω m)) (hlin : ∀ ω m, LinRegs (genRun σ ω m))
    (hwsl : ∃ f : List (Label (Fin n) (RegObj .r1)) → List (OpId (Fin n) × RWOp Val),
      ∀ ω m m', m ≤ m' →
        IsLinearization (hist .r1 (genRun σ ω m')) (f (hist .r1 (genRun σ ω m'))) ∧
        opsFor RWOp.isWrite (f (hist .r1 (genRun σ ω m))) <+:
          opsFor RWOp.isWrite (f (hist .r1 (genRun σ ω m')))) :
    fairCoins {ω : ℕ → Bool | ∀ J, ∃ p m, Entered p J (genRun σ ω m)} = 0 := by
  obtain ⟨f, hf⟩ := hwsl
  have hs := Thm7.forever_subsingleton hn hvalid hlin hf
  rcases hs.eq_empty_or_singleton with h | ⟨w, h⟩
  · rw [show {ω : ℕ → Bool | ∀ J, ∃ p m, Entered p J (genRun σ ω m)} = Thm7.Forever σ from rfl,
      h, measure_empty]
  · rw [show {ω : ℕ → Bool | ∀ J, ∃ p m, Entered p J (genRun σ ω m)} = Thm7.Forever σ from rfl,
      h, fairCoins_singleton]

/-- Theorem 7, almost-sure form: almost surely some round `J` is entered by no process. -/
theorem theorem7_ae (n : ℕ) (hn : 3 ≤ n) (σ : List (Ev n) → Ev n)
    (hvalid : ∀ ω m, Valid (genRun σ ω m)) (hlin : ∀ ω m, LinRegs (genRun σ ω m))
    (hwsl : ∃ f : List (Label (Fin n) (RegObj .r1)) → List (OpId (Fin n) × RWOp Val),
      ∀ ω m m', m ≤ m' →
        IsLinearization (hist .r1 (genRun σ ω m')) (f (hist .r1 (genRun σ ω m'))) ∧
        opsFor RWOp.isWrite (f (hist .r1 (genRun σ ω m))) <+:
          opsFor RWOp.isWrite (f (hist .r1 (genRun σ ω m')))) :
    ∀ᵐ ω ∂fairCoins, ∃ J, ∀ p m, ¬ Entered p J (genRun σ ω m) := by
  rw [ae_iff]
  have := theorem7 n hn σ hvalid hlin hwsl
  refine le_antisymm (le_trans (measure_mono ?_) this.le) bot_le
  intro ω hω
  simp only [Set.mem_ofPred_eq, not_exists, not_forall, not_not] at hω ⊢
  exact hω

/-- **Corollary 8** of Hadzilacos–Hu–Toueg (PODC 2021): (1) with merely linearizable registers a
strong adversary prevents the termination of Algorithm 1 (`theorem6`); (2) if `R1` is write
strongly-linearizable (and all registers linearizable), Algorithm 1 terminates with probability 1
against every strong adversary (`theorem7`). -/
theorem corollary8 (n : ℕ) (hn : 3 ≤ n) :
    (∃ σ : List (Ev n) → Ev n, ∀ ω : ℕ → Bool,
      (∀ m, Valid (genRun σ ω m) ∧ LinRegs (genRun σ ω m)) ∧
        ∀ p j, 1 ≤ j → ∃ m, Entered p j (genRun σ ω m)) ∧
    ∀ σ : List (Ev n) → Ev n, (∀ ω m, Valid (genRun σ ω m)) → (∀ ω m, LinRegs (genRun σ ω m)) →
      (∃ f : List (Label (Fin n) (RegObj .r1)) → List (OpId (Fin n) × RWOp Val),
        ∀ ω m m', m ≤ m' →
          IsLinearization (hist .r1 (genRun σ ω m')) (f (hist .r1 (genRun σ ω m'))) ∧
          opsFor RWOp.isWrite (f (hist .r1 (genRun σ ω m))) <+:
            opsFor RWOp.isWrite (f (hist .r1 (genRun σ ω m')))) →
      fairCoins {ω : ℕ → Bool | ∀ J, ∃ p m, Entered p J (genRun σ ω m)} = 0 :=
  ⟨theorem6 n hn, fun σ => theorem7 n hn σ⟩

/-! ## Non-vacuity of the hypotheses of Theorem 7

For `n = 3`, the adversary `NV.adv` lets only the player `p₂` run, with atomic register
behaviour: it writes `⊥` to `R1` and `C`, reads `⊥, ⊥` from `R1` and `⊥` from `C`, returns
(line 25) and then takes `noop` steps forever. No coin is flipped. -/

namespace NV

open Thm6 List

/-- The player `p₂`. -/
def p2 : Fin 3 := 2

/-- The steps of `p₂`. -/
def script : List (Ev 3) :=
  [.inv p2 .r1 (.write .bot), .ret p2 .r1 .bot, .inv p2 .c (.write .bot), .ret p2 .c .bot,
    .inv p2 .r1 .read, .ret p2 .r1 .bot, .inv p2 .r1 .read, .ret p2 .r1 .bot,
    .inv p2 .c .read, .ret p2 .c .bot]

/-- The `i`-th event. -/
def ev (i : ℕ) : Ev 3 := script.getD i (.noop p2)

/-- The adversary. -/
def adv (α : List (Ev 3)) : Ev 3 := ev α.length

lemma ev_ge {i : ℕ} (h : 10 ≤ i) : ev i = .noop p2 := by
  unfold ev
  rw [List.getD_eq_getElem?_getD, getElem?_eq_none (by simp [script]; omega)]
  rfl

lemma coinify_ev (ω : ℕ → Bool) (α : List (Ev 3)) (i : ℕ) : coinify ω α (ev i) = ev i := by
  unfold ev
  rcases Nat.lt_or_ge i 10 with h | h
  · interval_cases i <;> rfl
  · rw [← ev, ev_ge h]; rfl

lemma genRun_adv (ω : ℕ → Bool) (m : ℕ) : genRun adv ω m = (range m).map ev := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [genRun, ih, range_succ, map_append, map_singleton, adv, length_map, length_range,
      coinify_ev]

lemma run_eq (k : ℕ) : (range (10 + k)).map ev = script ++ replicate k (.noop p2) := by
  rw [range_add, map_append, List.map_map]
  congr 1
  apply ext_getElem (by simp)
  intro i h1 h2
  simp only [getElem_map, Function.comp_apply, getElem_replicate, getElem_range]
  exact ev_ge (by omega)

lemma run_prefix (m : ℕ) : (range m).map ev <+: script ++ replicate m (.noop p2) := by
  rw [← run_eq, Nat.add_comm, range_add, map_append]; exact prefix_append _ _

lemma hist_noops (x : Reg) (k : ℕ) : hist x (replicate k (.noop p2) : List (Ev 3)) = [] := by
  simp [hist, Ev.toLabel]

lemma valid_adv (ω : ℕ → Bool) (m : ℕ) : Valid (genRun adv ω m) := by
  intro p
  rw [genRun_adv]
  apply procRun_isSome_of_prefix p (run_prefix m)
  rw [procRun_eq_pfold, pfold_append]
  by_cases hp : p = p2
  · subst hp
    have h1 : pfold p2 (some (.run (initLoc p2))) script = some (.run .done) := rfl
    rw [h1]
    suffices ∀ k, pfold p2 (some (.run .done)) (replicate k (.noop p2)) = some (.run .done) by
      rw [this]; rfl
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [replicate_succ, pfold_cons]; simpa [Ev.proc, pstep, code] using ih
  · rw [pfold_of_forall_ne p _ script (by decide +revert), pfold_of_forall_ne p _ _
      (by intro e he; rw [eq_of_mem_replicate he]; exact Ne.symm hp)]
    rfl

/-- Annotated histories of the three registers. -/
def ah : (x : Reg) → List (LPLabel (Fin 3) (RegObj x))
  | .r1 => [.inv p2 (.write .bot), .lin p2, .ret p2 .bot, .inv p2 .read, .lin p2, .ret p2 .bot,
      .inv p2 .read, .lin p2, .ret p2 .bot]
  | .c => [.inv p2 (.write .bot), .lin p2, .ret p2 .bot, .inv p2 .read, .lin p2, .ret p2 .bot]
  | .r2 => []

lemma hist_script (x : Reg) : hist x script = (ah x).filterMap LPLabel.erase := by
  cases x <;> rfl

lemma lpRun_ah (x : Reg) : ∃ c, lpRun ((RegObj x).init, fun _ => .idle) (ah x) = some c := by
  cases x
  · exact ⟨_, by
      simp only [ah]
      rw [lpRun_triple' (A := RegObj .r1) _ rfl rfl, lpRun_triple' (A := RegObj .r1) _ rfl rfl,
        lpRun_triple' (A := RegObj .r1) _ rfl rfl]
      rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, by
      simp only [ah]
      rw [lpRun_triple' (A := RegObj .c) _ rfl rfl, lpRun_triple' (A := RegObj .c) _ rfl rfl]
      rfl⟩

lemma hist_prefix (x : Reg) (m : ℕ) : hist x ((range m).map ev) <+: hist x script := by
  have := (run_prefix m).filterMap (Ev.toLabel x)
  rwa [← hist, ← hist, Thm7.hist_append, hist_noops, append_nil] at this

lemma linRegs_adv (ω : ℕ → Bool) (m : ℕ) : LinRegs (genRun adv ω m) := by
  intro x
  obtain ⟨c, hc⟩ := lpRun_ah x
  rw [genRun_adv]
  have h := hist_prefix x m
  rw [hist_script] at h
  exact isLinearization_of_lpRun hc h

/-- The history of `R1` in the script. -/
abbrev H : List (Label (Fin 3) (RegObj .r1)) := hist .r1 script

open Classical in
/-- Some linearization of each history of `R1` (`[]` if there is none). -/
noncomputable def fLin (h : List (Label (Fin 3) (RegObj .r1))) :
    List (OpId (Fin 3) × RWOp Val) :=
  if hex : ∃ L, IsLinearization h L then Classical.choose hex else []

lemma fLin_spec {h : List (Label (Fin 3) (RegObj .r1))} (hex : ∃ L, IsLinearization h L) :
    IsLinearization h (fLin h) := by
  rw [fLin, dite_eq_left_of_eq_true (eq_true hex)]; exact Classical.choose_spec hex

lemma opOf_prefix_H {g : List (Label (Fin 3) (RegObj .r1))} (hg : g <+: H) {a : OpId (Fin 3)}
    (ha : Invoked g a) : opOf g a = opOf H a := by
  obtain ⟨u, hu⟩ := hg; rw [← hu, opOf_append_of_invoked ha]

lemma opOf_H (a : OpId (Fin 3)) {o : RWOp Val} (h : opOf H a = some o) (ho : o.isWrite = true) :
    a = (p2, 0) ∧ o = .write .bot := by
  obtain ⟨p, k⟩ := a
  have hops : opsOf H p = if p = p2 then [.write .bot, .read, .read] else [] := by
    fin_cases p <;> rfl
  simp only [opOf, hops] at h
  split_ifs at h with hp
  · subst hp
    match k, h with
    | 0, h => simp at h; exact ⟨rfl, h.symm⟩
    | 1, h => simp at h; subst h; simp at ho
    | 2, h => simp at h; subst h; simp at ho
    | k + 3, h => simp at h
  · simp at h

lemma writes_cases {g : List (Label (Fin 3) (RegObj .r1))} (hg : g <+: H)
    {L : List (OpId (Fin 3) × RWOp Val)} (hL : IsLinearization g L) :
    opsFor RWOp.isWrite L = [] ∨ opsFor RWOp.isWrite L = [((p2, 0), .write .bot)] := by
  have hall : ∀ y ∈ opsFor RWOp.isWrite L, y = ((p2, 0), .write .bot) := by
    intro y hy
    obtain ⟨hyL, hyw⟩ := mem_filter.1 hy
    have h1 := hL.op_eq y hyL
    rw [opOf_prefix_H hg (hL.invoked_of_mem (mem_map_of_mem hyL))] at h1
    obtain ⟨e1, e2⟩ := opOf_H _ h1 hyw
    exact Prod.ext e1 e2
  have hnd : (opsFor RWOp.isWrite L).Nodup := (hL.nodup.of_map _).filter _
  rcases hl : opsFor RWOp.isWrite L with _ | ⟨a, _ | ⟨b, l⟩⟩
  · left; rfl
  · right; rw [hall a (by rw [hl]; simp)]
  · exfalso
    rw [hl] at hnd hall
    have := hall a (by simp); have := hall b (by simp)
    simp_all

lemma completed_H {g : List (Label (Fin 3) (RegObj .r1))} (hg : g <+: H) (h2 : 2 ≤ g.length) :
    Completed g (p2, 0) := by
  have h : H.take 2 <+: g := prefix_of_prefix_length_le (take_prefix 2 H) hg (by simp; omega)
  obtain ⟨u, rfl⟩ := h
  exact Completed.mono (by show 0 < (respsOf (H.take 2) p2).length; decide)

/-- Write strong-linearizability of `R1` along the runs of `NV.adv`. -/
lemma wsl_adv : ∀ (ω : ℕ → Bool) (m m' : ℕ), m ≤ m' →
    IsLinearization (hist .r1 (genRun adv ω m')) (fLin (hist .r1 (genRun adv ω m'))) ∧
    opsFor RWOp.isWrite (fLin (hist .r1 (genRun adv ω m))) <+:
      opsFor RWOp.isWrite (fLin (hist .r1 (genRun adv ω m'))) := by
  intro ω m m' hmm
  have hex : ∀ k, ∃ L, IsLinearization (hist .r1 (genRun adv ω k)) L :=
    fun k => linRegs_adv ω k .r1
  refine ⟨fLin_spec (hex m'), ?_⟩
  have hpre : hist .r1 (genRun adv ω m) <+: hist .r1 (genRun adv ω m') := by
    rw [genRun_adv, genRun_adv]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmm
    rw [range_add, map_append]
    exact (prefix_append _ _).filterMap _
  have hH : hist .r1 (genRun adv ω m') <+: H := by rw [genRun_adv]; exact hist_prefix .r1 m'
  have hH0 := hpre.trans hH
  rcases writes_cases hH0 (fLin_spec (hex m)) with e | e
  · rw [e]; exact nil_prefix
  · by_cases hl : 2 ≤ (hist .r1 (genRun adv ω m')).length
    · have hc := completed_H hH hl
      have hL' := fLin_spec (hex m')
      have hm := hL'.complete _ hc
      obtain ⟨⟨a, o⟩, hy, ha⟩ := mem_map.1 hm
      simp only at ha; subst ha
      have ho := hL'.op_eq _ hy
      rw [opOf_prefix_H hH (hL'.invoked_of_mem hm)] at ho
      have ho' : o = .write .bot := by
        have : opOf H (p2, 0) = some (.write .bot) := rfl
        rw [this] at ho; exact (Option.some.inj ho).symm
      subst ho'
      have hmem : ((p2, 0), RWOp.write Val.bot) ∈ opsFor RWOp.isWrite
          (fLin (hist .r1 (genRun adv ω m'))) := mem_filter.2 ⟨hy, rfl⟩
      rcases writes_cases hH hL' with e' | e'
      · rw [e'] at hmem; simp at hmem
      · rw [e, e']
    · have hinv : Invoked (hist .r1 (genRun adv ω m)) (p2, 0) :=
        (fLin_spec (hex m)).invoked_of_mem (by
          have : ((p2, 0), RWOp.write Val.bot) ∈ opsFor RWOp.isWrite
              (fLin (hist .r1 (genRun adv ω m))) := by rw [e]; simp
          exact mem_map_of_mem (mem_filter.1 this).1)
      have hne : 1 ≤ (hist .r1 (genRun adv ω m)).length := by
        rcases hh : hist .r1 (genRun adv ω m) with _ | ⟨_, _⟩
        · rw [hh] at hinv; simp [Invoked] at hinv
        · simp
      have heq := hpre.eq_of_length (by have := hpre.length_le; omega)
      rw [heq]

end NV

/-- **Non-vacuity of Theorem 7**: for `n = 3` there is an adversary whose runs are valid, have
linearizable registers, and admit a write strong-linearization function for `R1`. -/
theorem theorem7_hyps_satisfiable : ∃ σ : List (Ev 3) → Ev 3,
    (∀ ω m, Valid (genRun σ ω m)) ∧ (∀ ω m, LinRegs (genRun σ ω m)) ∧
    ∃ f : List (Label (Fin 3) (RegObj .r1)) → List (OpId (Fin 3) × RWOp Val),
      ∀ ω m m', m ≤ m' →
        IsLinearization (hist .r1 (genRun σ ω m')) (f (hist .r1 (genRun σ ω m'))) ∧
        opsFor RWOp.isWrite (f (hist .r1 (genRun σ ω m))) <+:
          opsFor RWOp.isWrite (f (hist .r1 (genRun σ ω m'))) :=
  ⟨NV.adv, NV.valid_adv, NV.linRegs_adv, NV.fLin, NV.wsl_adv⟩

end Podc.RegisterLinTermination.Game
