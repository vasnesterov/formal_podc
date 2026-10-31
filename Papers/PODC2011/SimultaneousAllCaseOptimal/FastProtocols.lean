import Papers.PODC2011.SimultaneousAllCaseOptimal.Constructions

/-!
# Theorems 2 and 3 (§3): fast simultaneous protocols

* `theorem2`: if `A` solves `T` and `C` has the ConCon properties of §2.3, then `ConCon(A)` solves
  `sim(T)`, and every process alive at time `t + 1 − W(F)` decides exactly then.
* `theorem3`: if moreover every nonfaulty process decides by time `k̂` in `A`, then
  `Opt(A, k̂) = Delay(A, k̂) else ConCon(A)` solves `sim(T)` and every process alive at time
  `min{k̂, t + 1 − W(F)}` decides exactly then.

The correctness argument of Theorem 2 in the paper ("all processes simulate the same run of `A`,
and hence choose output values consistent with the input values") only gives outputs consistent
with the *simulated* input vector, which differs from the real one on the processes outside the
core. The repair: the simulated run is indistinguishable, for the processes of the core, from the
run of `A` with the *real* inputs and the same (silent) failures (`hist_simRun`), and `A`'s
correctness in that run gives an output vector for the real inputs.
-/

namespace Podc.SimultaneousAllCaseOptimal

open Cslib.SyncCrash Cslib.Byzantine.LockStep

variable {P I M O MC : Type} [Fintype P]

/-- In the simulated run, a silent process delivers nothing. -/
lemma not_deliv_simRun {c : P → Option I} {ι : P → I} {s q : P} {m : ℕ} (hs : c s = none) :
    ¬ (simRun c ι).Deliv s q m := by
  rintro ⟨ha, hn⟩
  have h1 : (simRun c ι).crash s = some 1 := by simp [simRun, silentCrash, hs]
  have := ha 1 h1
  have hm : m = 0 := by omega
  subst hm
  exact hn ⟨h1, by simp [simRun]⟩

/-- Runs that differ only in the inputs of silent processes look the same to the others. -/
lemma hist_simRun (A : Protocol P I M O) (c : P → Option I) {ι ι' : P → I}
    (hι : ∀ q, c q ≠ none → ι q = ι' q) :
    ∀ m q, c q ≠ none → hist A (simRun c ι) m q = hist A (simRun c ι') m q := by
  intro m
  induction m with
  | zero => intros; rfl
  | succ m ih =>
    intro q hq
    have : (fun s => msg A (simRun c ι) s q m) = (fun s => msg A (simRun c ι') s q m) := by
      funext s
      rw [msg_eq_deliv, msg_eq_deliv]
      by_cases hs : c s = none
      · rw [if_neg (fun h => not_deliv_simRun hs h.2), if_neg (fun h => not_deliv_simRun hs h.2)]
      · by_cases hdd : s ≠ q ∧ (simRun c ι).Deliv s q m
        · rw [if_pos hdd, if_pos (show s ≠ q ∧ (simRun c ι').Deliv s q m from hdd), ih s hs]
          exact congrArg (fun x => A.send s x _ q) (hι s hs)
        · rw [if_neg hdd, if_neg (show ¬ (s ≠ q ∧ (simRun c ι').Deliv s q m) from hdd)]
    rw [Cslib.SyncCrash.hist_succ, Cslib.SyncCrash.hist_succ, ih q hq, this]

lemma decides_simRun {A : Protocol P I M O} {c : P → Option I} {ι ι' : P → I}
    (hι : ∀ q, c q ≠ none → ι q = ι' q) {q : P} (hq : c q ≠ none) {m : ℕ} {d : O}
    (h : Decides A (simRun c ι) q m d) : Decides A (simRun c ι') q m d :=
  decides_congr (hι q hq) (hist_simRun A c hι m q hq) h.alive h

/-- The simulated run is a legal run when the core contains every process alive at some time `K`
of a run `r` with at most `t` crashes. -/
lemma simRun_isRun {T : Task P I O} {t K : ℕ} {r : Run P I} (hr : T.IsRun t r)
    {c : P → Option I} (hc : ∀ q, r.Alive q K → c q ≠ none) {ι : P → I} (hι : ι ∈ T.inputs) :
    T.IsRun t (simRun c ι) := by
  refine ⟨⟨le_trans (Finset.card_le_card fun q hq => ?_) hr.1.1, fun p c' hc' => ?_⟩, hι⟩
  · simp only [Run.mem_faulty, Run.Faulty, simRun, silentCrash, ne_eq, ite_eq_right_iff,
      reduceCtorEq, imp_false, not_not] at hq ⊢
    intro hn
    exact hc q (Run.alive_of_not_faulty (by simpa [Run.Faulty] using hn) K) hq
  · simp only [simRun, silentCrash] at hc'
    split_ifs at hc' <;> simp_all

lemma raw_concon {C : CCProtocol P I MC} {A : Protocol P I M O} {T : Task P I O} {r : Run P I}
    {p : P} {m : ℕ} : raw (ConCon C A T) r p m =
      if ∃ q, C.coreAt r p m q ≠ none then simDecision A T (C.coreAt r p m) p else none := by
  have : hist (ConCon C A T) r m p = hist C.toProtocol r m p :=
    hist_eq_of_send (A := ConCon C A T) (B := C.toProtocol) rfl r m p
  simp only [raw, this]; rfl

/-- Before time `t + 1 − W(F)`, `ConCon(A)` has written nothing. -/
lemma raw_concon_lt {C : CCProtocol P I MC} {A : Protocol P I M O} {T : Task P I O} {t : ℕ}
    (hC : IsConCon C T t) {r : Run P I} (hr : T.IsRun t r) {p : P} {m : ℕ} (hp : r.Alive p m)
    (hm : m + r.waste < t + 1) : raw (ConCon C A T) r p m = none := by
  rw [raw_concon, if_neg]
  push Not
  exact hC.empty r hr p m hp hm

/-- **Theorem 2.** If `A` solves `T` and `C` has the ConCon properties of §2.3, then `ConCon(A)`
solves `sim(T)`, and in a run with failure pattern `F` every process alive at time
`t + 1 − W(F)` decides at that time (so all decisions happen at time `t + 1 − W(F)`). -/
theorem theorem2 {C : CCProtocol P I MC} {A : Protocol P I M O} {T : Task P I O} {t : ℕ}
    (hC : IsConCon C T t) (hA : Solves A T t) :
    SolvesSim (ConCon C A T) T t ∧
      (∀ r, T.IsRun t r → ∀ p, r.Alive p (t + 1 - r.waste) →
        ∃ d, Decides (ConCon C A T) r p (t + 1 - r.waste) d) ∧
      (∀ r, T.IsRun t r → ∀ p m d, Decides (ConCon C A T) r p m d → m = t + 1 - r.waste) := by
  classical
  -- the core at time `K = t + 1 − W` and its properties
  have hcore : ∀ r, T.IsRun t r → ∀ p, r.Alive p (t + 1 - r.waste) →
      (∀ q, r.Alive q (t + 1 - r.waste) → C.coreAt r p (t + 1 - r.waste) q ≠ none) ∧
      (∀ q v, C.coreAt r p (t + 1 - r.waste) q = some v → r.input q = v) := by
    intro r hr p hp
    refine ⟨fun q hq => by rw [hC.full r hr p q hp hq]; simp, fun q v hv =>
      hC.accurate r hr p _ q v hp hv⟩
  -- the register at time `K`
  have hK : ∀ r, T.IsRun t r → ∀ p, r.Alive p (t + 1 - r.waste) →
      ∃ ι, Extends T (C.coreAt r p (t + 1 - r.waste)) ι ∧
        raw (ConCon C A T) r p (t + 1 - r.waste) =
          decisionOf A (simRun (C.coreAt r p (t + 1 - r.waste)) ι) p ∧
        ∃ m d, Decides A (simRun (C.coreAt r p (t + 1 - r.waste)) ι) p m d := by
    intro r hr p hp
    obtain ⟨h1, h2⟩ := hcore r hr p hp
    set c := C.coreAt r p (t + 1 - r.waste)
    have hex : ∃ ι, Extends T c ι := ⟨r.input, hr.2, h2⟩
    refine ⟨Classical.choose hex, Classical.choose_spec hex, ?_, ?_⟩
    · rw [raw_concon, if_pos ⟨p, h1 p hp⟩, simDecision, dif_pos hex]
    · have hsr := simRun_isRun hr h1 (Classical.choose_spec hex).1
      refine hA.complete _ hsr p ?_
      simp [Run.Faulty, simRun, silentCrash, h1 p hp]
  have hlt : ∀ r, T.IsRun t r → ∀ p m, r.Alive p m → m < t + 1 - r.waste →
      raw (ConCon C A T) r p m = none := fun r hr p m hp hm =>
    raw_concon_lt hC hr hp (by omega)
  have hdecK : ∀ r, T.IsRun t r → ∀ p, r.Alive p (t + 1 - r.waste) →
      ∃ d, Decides (ConCon C A T) r p (t + 1 - r.waste) d := by
    intro r hr p hp
    obtain ⟨ι, -, hraw, m, d, hd⟩ := hK r hr p hp
    exact ⟨d, decides_iff.2 ⟨hp, hraw.trans (decisionOf_eq hd), fun m' hm' =>
      hlt r hr p m' (hp.mono hm'.le) hm'⟩⟩
  have htime : ∀ r, T.IsRun t r → ∀ p m d, Decides (ConCon C A T) r p m d →
      m = t + 1 - r.waste := by
    intro r hr p m d hd
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hlt r hr p m hd.alive h; rw [hd.raw_eq] at this; simp at this
    · obtain ⟨d', hd'⟩ := hdecK r hr p (hd.alive.mono h.le)
      have := (Decides.unique hd hd').1; omega
  refine ⟨{ complete := ?_, correct := ?_, simultaneous := ?_ }, hdecK, htime⟩
  · intro r hr p hp
    obtain ⟨d, hd⟩ := hdecK r hr p (Run.alive_of_not_faulty hp _)
    exact ⟨_, d, hd⟩
  · intro r hr
    by_cases hex : ∃ p m d, Decides (ConCon C A T) r p m d
    · obtain ⟨p0, m0, d0, hd0⟩ := hex
      have hm0 := htime r hr p0 m0 d0 hd0
      subst hm0
      have hp0 := hd0.alive
      set c := C.coreAt r p0 (t + 1 - r.waste)
      obtain ⟨h1, h2⟩ := hcore r hr p0 hp0
      have hreal := simRun_isRun hr h1 hr.2 (ι := r.input)
      obtain ⟨o, ho, hdec⟩ := hA.correct _ hreal
      refine ⟨o, ho, fun q m d hq => ?_⟩
      have hm := htime r hr q m d hq
      subst hm
      have hcq : C.coreAt r q (t + 1 - r.waste) = c := hC.consistent r hr q p0 _ hq.alive hp0
      obtain ⟨ι, hι, hraw, -⟩ := hK r hr q hq.alive
      rw [hcq] at hι hraw
      have := hraw.symm.trans hq.raw_eq
      obtain ⟨mq, hmq⟩ := decisionOf_spec this
      have hqc : c q ≠ none := h1 q hq.alive
      have := decides_simRun (ι' := r.input) (fun q' hq' => by
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hq'
        rw [hι.2 q' v hv, h2 q' v hv]) hqc hmq
      exact hdec q mq d this
    · push Not at hex
      obtain ⟨o, ho, -⟩ := hA.correct r hr
      exact ⟨o, ho, fun p m d hd => absurd hd (hex p m d)⟩
  · intro r hr p q m m' d d' hp hq
    rw [htime r hr p m d hp, htime r hr q m' d' hq]

/-- **Theorem 3.** If `A` solves `T` with every nonfaulty process deciding by time `k̂`, then
`Opt(A, k̂) = Delay(A, k̂) else ConCon(A)` solves `sim(T)`, and in a run with failure pattern `F`
every process alive at time `min{k̂, t + 1 − W(F)}` decides at that time. -/
theorem theorem3 {C : CCProtocol P I MC} {A : Protocol P I M O} {T : Task P I O} {t k : ℕ}
    (hC : IsConCon C T t) (hA : SolvesWithin A T t k) :
    SolvesSim (Opt C A T k) T t ∧
      ∀ r, T.IsRun t r → ∀ p, r.Alive p (min k (t + 1 - r.waste)) →
        ∃ d, Decides (Opt C A T k) r p (min k (t + 1 - r.waste)) d := by
  obtain ⟨h1, -, h1a⟩ := lemma1 hA
  obtain ⟨h2, h2a, -⟩ := theorem2 hC hA.toSolves
  refine ⟨else_solvesSim h1 h2, fun r hr p hp => ?_⟩
  rcases le_or_gt k (t + 1 - r.waste) with hle | hle
  · rw [min_eq_left hle] at hp ⊢
    obtain ⟨d, hd⟩ := h1a r hr p hp
    exact ⟨d, decides_else_of_left hd fun m' hm' =>
      raw_concon_lt hC hr (hp.mono hm'.le) (by omega)⟩
  · rw [min_eq_right hle.le] at hp ⊢
    obtain ⟨d, hd⟩ := h2a r hr p hp
    exact ⟨d, decides_else_of_right hd fun m' hm' => raw_delay_lt (by omega)⟩

end Podc.SimultaneousAllCaseOptimal
