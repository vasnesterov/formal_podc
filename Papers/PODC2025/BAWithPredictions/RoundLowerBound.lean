import Papers.PODC2025.BAWithPredictions.Defs
import Cslib.Computability.Distributed.Byzantine.LockStep.Agreement
import Cslib.Computability.Distributed.Byzantine.LockStep.Parallel
import Cslib.Foundations.Data.Finset.Quorum

/-!
# Byzantine Agreement with Predictions — round-complexity lower bound (Theorem 13)

Ben-David, Dzulfikar, Ellen, Gilbert, *Byzantine Agreement with Predictions*, PODC 2025
(arXiv:2505.01793), Section 10.1.

Model: CSLib's synchronous lock-step model (`Cslib.Byzantine.LockStep`) on the complete graph,
deterministic history-based protocols, static Byzantine adversary, reliable channels. A process'
input is a pair `(v, a)` of a value `v : V` and a classification prediction `a : P → Bool`
(`a j = true`: "`p_j` is predicted honest").

The paper reduces Theorem 13 to the early-deciding lower bound of Dolev–Reischuk–Strong for
algorithms *without* predictions, which it cites. We state that bound as an explicit hypothesis
(`EarlyDecidingLB`) — in the **Byzantine** model, see the docstring — and prove the reduction:

* `simProtocol X alg`: the prediction-free algorithm `S'` on the processes outside `X`, which run
  `alg` with the prediction "`X` is faulty, everyone else is honest"; the processes of `X` are
  silent Byzantine (`liftScenario`, `status_liftScenario`, `solves_simProtocol`).
* `padScenario` (shared, `Cslib/Computability/Distributed/Byzantine/LockStep/Basic.lean`): Byzantine
  processes that behave exactly as honest ones (used to reach exactly `f` faults).
* `roundLowerBound`: Theorem 13 conditional on `EarlyDecidingLB`, with the sharper bound
  `min (f' + 2) (t - f + f' + 1)` for `f' = min f ⌊B/(n-f)⌋`;
  `roundLowerBound_paper`: the paper's four-term bound.
-/

namespace BAWithPredictions

open Cslib.Byzantine.LockStep Finset

/-- **Byzantine agreement with predictions**: Byzantine agreement (termination, strong unanimity,
agreement) on the value component of the inputs; the prediction component is advice only. -/
def BAP {P V : Type*} : Spec P (V × (P → Bool)) V := fun x H dec => BA (fun p => (x p).1) H dec

/-! ### Simulating an algorithm with predictions on the processes outside `X` -/

section Sim

variable {P V M : Type*} [DecidableEq P] (X : Finset P)

/-- Extend an inbox of the processes outside `X` by "nothing from `X`". -/
def liftInbox (i : Inbox {p // p ∉ X} M) : Inbox P M :=
  fun p => if hp : p ∈ X then none else i ⟨p, hp⟩

/-- Extend a history of the processes outside `X` by "nothing from `X`". -/
def liftHist (h : History {p // p ∉ X} M) : History P M := h.map (liftInbox X)

/-- The paper's algorithm `S'` (proof of Theorem 13): process `q ∉ X` runs `alg` as `q`, with the
prediction that exactly the processes of `X` are faulty, treating the processes of `X` as silent. -/
def simProtocol (alg : Protocol P (V × (P → Bool)) M V) : Protocol {p // p ∉ X} V M V where
  send q v h q' := alg.send q.1 (v, correctPred X) (liftHist X h) q'.1
  decide q v h := alg.decide q.1 (v, correctPred X) (liftHist X h)

/-- The run of `alg` corresponding to a run `s` of `simProtocol X alg`: the processes of `X` are
silent Byzantine, the others behave as in `s` and get the prediction `correctPred X`. The values
`x0` are the (irrelevant) inputs of the processes of `X`. -/
def liftScenario (s : Scenario {p // p ∉ X} V M) (x0 : P → V) : Scenario P (V × (P → Bool)) M where
  byz := Subtype.val '' s.byz ∪ ↑X
  input p := (if hp : p ∈ X then x0 p else s.input ⟨p, hp⟩, correctPred X)
  adv r p q := if h : p ∉ X ∧ q ∉ X then s.adv r ⟨p, h.1⟩ ⟨q, h.2⟩ else none
  drop r p q := ∃ h : p ∉ X ∧ q ∉ X, s.drop r ⟨p, h.1⟩ ⟨q, h.2⟩

variable {X}

theorem val_mem_byz_liftScenario {s : Scenario {p // p ∉ X} V M} {x0 : P → V} {q : {p // p ∉ X}} :
    q.1 ∈ (liftScenario X s x0).byz ↔ q ∈ s.byz := by
  simp [liftScenario, q.2]

theorem mem_byz_liftScenario_of_mem {s : Scenario {p // p ∉ X} V M} {x0 : P → V} {p : P}
    (hp : p ∈ X) : p ∈ (liftScenario X s x0).byz := by
  simp [liftScenario, hp]

theorem input_liftScenario {s : Scenario {p // p ∉ X} V M} {x0 : P → V} (q : {p // p ∉ X}) :
    (liftScenario X s x0).input q.1 = (s.input q, correctPred X) := by
  simp [liftScenario, q.2]

/-- Histories correspond: the history of `q` in the lifted run of `alg` is its history in the run
of `simProtocol X alg`, with empty messages from `X`. -/
theorem hist_liftScenario (alg : Protocol P (V × (P → Bool)) M V)
    (s : Scenario {p // p ∉ X} V M) (x0 : P → V) :
    ∀ r (q : {p // p ∉ X}),
      hist ⊤ alg (liftScenario X s x0) r q.1 = liftHist X (hist ⊤ (simProtocol X alg) s r q) := by
  intro r
  induction r with
  | zero => intro q; rfl
  | succ r ih =>
    intro q
    rw [hist_succ, hist_succ, ih, liftHist, liftHist, List.map_append]
    congr 2
    funext p
    unfold liftInbox deliver
    by_cases hp : p ∈ X
    · have hne : p ≠ q.1 := fun h => q.2 (h ▸ hp)
      simp [hp, hne, liftScenario, q.2]
    · have hq := q.2
      by_cases hpq : p = q.1
      · subst hpq; simp
      · have hne : (⟨p, hp⟩ : {p // p ∉ X}) ≠ q := fun h => hpq (congrArg Subtype.val h)
        have hadv : (liftScenario X s x0).adv r p q.1 = s.adv r ⟨p, hp⟩ q := by
          simp [liftScenario, hp, hq]
        have hdrop : (liftScenario X s x0).drop r p q.1 ↔ s.drop r ⟨p, hp⟩ q := by
          simp [liftScenario, hp, hq]
        have hin := input_liftScenario (s := s) (x0 := x0) ⟨p, hp⟩
        have hh := ih ⟨p, hp⟩
        by_cases hb : (⟨p, hp⟩ : {p // p ∉ X}) ∈ s.byz
        · have hb' : p ∈ (liftScenario X s x0).byz := val_mem_byz_liftScenario.2 hb
          simp [hpq, hne, hb, hb', hadv, hp]
        · have hb' : p ∉ (liftScenario X s x0).byz := fun h => hb (val_mem_byz_liftScenario.1 h)
          by_cases hd : s.drop r ⟨p, hp⟩ q
          · simp [hpq, hne, hb, hb', hdrop, hd]
          · simp only at hin hh
            simp [hpq, hne, hb, hb', hdrop, hd, hin, hh, simProtocol, hp]

theorem status_liftScenario (alg : Protocol P (V × (P → Bool)) M V)
    (s : Scenario {p // p ∉ X} V M) (x0 : P → V) (r : ℕ) (q : {p // p ∉ X}) :
    status ⊤ alg (liftScenario X s x0) r q.1 = status ⊤ (simProtocol X alg) s r q := by
  simp only [status, input_liftScenario, hist_liftScenario]
  rfl

theorem decides_liftScenario (alg : Protocol P (V × (P → Bool)) M V)
    (s : Scenario {p // p ∉ X} V M) (x0 : P → V) (q : {p // p ∉ X}) (v : V) :
    Decides ⊤ alg (liftScenario X s x0) q.1 v ↔ Decides ⊤ (simProtocol X alg) s q v := by
  simp only [Decides, status_liftScenario]

theorem ncard_byz_liftScenario [Fintype P] (s : Scenario {p // p ∉ X} V M) (x0 : P → V) :
    (liftScenario X s x0).byz.ncard ≤ s.byz.ncard + X.card := by
  calc (liftScenario X s x0).byz.ncard ≤ (Subtype.val '' s.byz).ncard + (X : Set P).ncard :=
        Set.ncard_union_le _ _
    _ ≤ s.byz.ncard + X.card := by
        rw [Set.ncard_coe_finset]
        exact Nat.add_le_add_right (Set.ncard_image_le (Set.toFinite _)) _

/-- **Correctness of the simulation** (proof of Theorem 13): if `alg` solves Byzantine agreement
with predictions against `t` Byzantine faults, then the prediction-free algorithm `S'` on the
processes outside `X` solves Byzantine agreement against `t - |X|` Byzantine faults. -/
theorem solves_simProtocol [Fintype P] {alg : Protocol P (V × (P → Bool)) M V} {t : ℕ}
    (hA : Solves ⊤ alg {S | S.ncard ≤ t} BAP) (hX : X.card ≤ t) :
    Solves ⊤ (simProtocol X alg) {S | S.ncard ≤ t - X.card} BA := by
  intro s hs hrel
  rcases isEmpty_or_nonempty {p // p ∉ X} with hQ | ⟨⟨q0⟩⟩
  · exact ⟨fun p => (hQ.false p).elim, fun _ _ p => (hQ.false p).elim,
      fun p => (hQ.false p).elim⟩
  obtain ⟨x0⟩ : Nonempty (P → V) := ⟨fun _ => s.input q0⟩
  have hbyz : (liftScenario X s x0).byz ∈ {S : Set P | S.ncard ≤ t} := by
    have := ncard_byz_liftScenario s x0
    simp only [Set.mem_ofPred_eq] at hs ⊢
    omega
  have hrelA : (liftScenario X s x0).Reliable := fun r p q ⟨_, hd⟩ => hrel _ _ _ hd
  obtain ⟨h1, h2, h3⟩ := hA (liftScenario X s x0) hbyz hrelA
  have hon : ∀ q : {p // p ∉ X}, q ∈ s.honest ↔ q.1 ∈ (liftScenario X s x0).honest := fun q =>
    not_congr val_mem_byz_liftScenario.symm
  refine ⟨fun q hq => ?_, fun v hv q hq => ?_, fun q hq q' hq' v w hv hw => ?_⟩
  · obtain ⟨v, hv⟩ := h1 q.1 ((hon q).1 hq)
    exact ⟨v, (decides_liftScenario alg s x0 q v).1 hv⟩
  · refine (decides_liftScenario alg s x0 q v).1 (h2 v (fun p hp => ?_) q.1 ((hon q).1 hq))
    have hpX : p ∉ X := fun h => hp (mem_byz_liftScenario_of_mem h)
    have := input_liftScenario (s := s) (x0 := x0) ⟨p, hpX⟩
    simp only at this ⊢
    rw [this]
    exact hv ⟨p, hpX⟩ ((hon ⟨p, hpX⟩).2 hp)
  · exact h3 q.1 ((hon q).1 hq) q'.1 ((hon q').1 hq') v w
      ((decides_liftScenario alg s x0 q v).2 hv) ((decides_liftScenario alg s x0 q' w).2 hw)

end Sim

/-! ### Wrong bits of the simulated predictions -/

/-- If every honest process gets the prediction "exactly `X` is faulty" and the actual faulty set
is `F ⊇ X`, each honest process has `|F \ X|` wrong bits. -/
theorem wrongBits_correctPred_of_subset {P : Type*} [Fintype P] [DecidableEq P] {X F : Finset P}
    (hXF : X ⊆ F) :
    wrongBits F (fun _ => correctPred X) = (Fintype.card P - F.card) * (F \ X).card := by
  have h1 : wrongBitsOf F (correctPred X) = (F \ X).card := by
    unfold wrongBitsOf
    congr 1
    ext j
    by_cases hj : j ∈ X
    · simp [hj, hXF hj]
    · by_cases hjF : j ∈ F <;> simp [hj, hjF]
  rw [wrongBits, h1, sum_const, smul_eq_mul, card_filter_notMem_univ]

/-! ### The cited lower bound and Theorem 13 -/

/-- A lower bound `bound f' t'` on the decision round of Byzantine agreement *without predictions*
on the processes `Q`: every deterministic algorithm that solves Byzantine agreement against `t'`
Byzantine faults has, for every `f' ≤ t'`, a reliable execution with at most `f'` Byzantine
processes in which some honest process has not decided before round `bound f' t'`. -/
def EarlyDecidingLBWith (bound : ℕ → ℕ → ℕ) (Q V : Type*) (t' : ℕ) : Prop :=
  ∀ (M : Type) (alg' : Protocol Q V M V), Solves ⊤ alg' {S | S.ncard ≤ t'} BA →
    ∀ f' ≤ t', ∃ s : Scenario Q V M, s.Reliable ∧ s.byz.ncard ≤ f' ∧
      ∃ q ∉ s.byz, ∀ r < bound f' t', status ⊤ alg' s r q = none

/-- **The early-deciding lower bound cited by the paper** ([DRS90]: Dolev, Reischuk, Strong,
*Early stopping in Byzantine agreement*, J. ACM 37(4), 1990), stated for the **Byzantine** model:
every deterministic Byzantine agreement algorithm (without predictions) for the processes `Q` that
tolerates `t'` Byzantine faults has, for every `f' ≤ t'`, a (reliable) execution with at most `f'`
Byzantine processes in which some honest process has not decided before round
`min (f' + 2) (t' + 1)`.

Stated here as a hypothesis; it is proved for `Nontrivial V` in `RoundLowerBoundStrong.lean`
(`earlyDecidingLB_strong`, `drsBound`; `earlyDecidingLB_weak` is the `f' + 1` part). It is
needs `Nontrivial V` (for a subsingleton `V`, deciding at round 0 is correct); we prove it for
`t' + 2 ≤ |Q|`. The paper invokes it for algorithms tolerating *crash* faults, where it is false for
decision times (see `differencies.md`); our reduction produces a Byzantine-tolerant algorithm, for
which the cited bound is the Byzantine early-deciding bound of [DRS90]. -/
def EarlyDecidingLB (Q V : Type*) (t' : ℕ) : Prop :=
  EarlyDecidingLBWith (fun f' t' => min (f' + 2) (t' + 1)) Q V t'

/-- The cited bound for all finite process sets with `t' + 2 ≤ n'` (Byzantine model). -/
def DRSBound (V : Type*) : Prop :=
  ∀ (Q : Type) [Fintype Q] (t' : ℕ), t' + 2 ≤ Fintype.card Q → EarlyDecidingLB Q V t'

/-- **Theorem 13 of [BDEG25]**, the reduction (proof of Theorem 13), for any lower bound
`bound f' t'` on algorithms without predictions. Let `alg` solve Byzantine agreement with
classification predictions against `t` Byzantine faults (for *all* predictions), `f ≤ t`,
`t + 2 ≤ n`, and `Bd` a bound on the number of wrong prediction bits. If `bound` is a lower bound
for the prediction-free algorithms on `n - x` processes tolerating `t - x` faults (`x ≤ f`), there
is a reliable execution with exactly `f` Byzantine processes (the set `F`), at most `Bd` wrong
prediction bits given to honest processes, and an honest process that has not decided before round
`bound f' (t - f + f')`, where `f' = min f ⌊Bd / (n - f)⌋`. -/
theorem roundLowerBoundWith (bound : ℕ → ℕ → ℕ) {P V : Type*} [Fintype P] [DecidableEq P]
    {M : Type} {alg : Protocol P (V × (P → Bool)) M V} {t f : ℕ}
    (hA : Solves ⊤ alg {S | S.ncard ≤ t} BAP) (hft : f ≤ t) (htn : t + 2 ≤ Fintype.card P)
    (Bd : ℕ)
    (hLB : ∀ X : Finset P, X.card ≤ f → EarlyDecidingLBWith bound {p // p ∉ X} V (t - X.card)) :
    ∃ (s : Scenario P (V × (P → Bool)) M) (F : Finset P),
      s.Reliable ∧ s.byz = ↑F ∧ F.card = f ∧ wrongBits F (fun i => (s.input i).2) ≤ Bd ∧
      ∃ p ∉ F, ∀ r < bound (min f (Bd / (Fintype.card P - f)))
          (t - f + min f (Bd / (Fintype.card P - f))), status ⊤ alg s r p = none := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, n = Fintype.card P := ⟨_, rfl⟩
  rw [← hn] at htn ⊢
  obtain ⟨f', hf'⟩ : ∃ f', f' = min f (Bd / (n - f)) := ⟨_, rfl⟩
  rw [← hf']
  have hf'f : f' ≤ f := hf' ▸ min_le_left _ _
  have hf'B : f' ≤ Bd / (n - f) := hf' ▸ min_le_right _ _
  obtain ⟨X, -, hXc⟩ := exists_subset_card_eq (s := (univ : Finset P)) (n := f - f')
    (by rw [card_univ, ← hn]; omega)
  have hS := solves_simProtocol (X := X) hA (by omega)
  obtain ⟨s', hrel, hcard, q, hq, hslow⟩ :=
    hLB X (by omega) M (simProtocol X alg) hS f' (by omega)
  have hQ : Fintype.card {p // p ∉ X} = n - X.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hn]
  -- extend the Byzantine set of `s'` to exactly `f'` processes, avoiding `q`
  obtain ⟨Z, hBZ, hZq, hZc⟩ := exists_subsuperset_card_eq (s := s'.byz.toFinset)
    (t := univ.erase q) (n := f')
    (fun a ha => mem_erase.2 ⟨fun h => hq (h ▸ Set.mem_toFinset.1 ha), mem_univ _⟩)
    (by rw [← Set.ncard_eq_toFinset_card']; exact hcard)
    (by rw [card_erase_of_mem (mem_univ _), card_univ, hQ]; omega)
  set sA := liftScenario X s' (fun _ => s'.input q) with hsA
  set sF := padScenario ⊤ alg sA (Subtype.val '' (Z : Set {p // p ∉ X})) with hsF
  set F := X ∪ Z.map (Function.Embedding.subtype _) with hF
  have hdisj : Disjoint X (Z.map (Function.Embedding.subtype _)) := by
    rw [disjoint_left]
    intro p hpX hpZ
    obtain ⟨z, -, rfl⟩ := mem_map.1 hpZ
    exact z.2 hpX
  have hFX : F \ X = Z.map (Function.Embedding.subtype _) := by
    rw [hF, union_sdiff_left, sdiff_eq_self_of_disjoint hdisj.symm]
  refine ⟨sF, F, ?_, ?_, ?_, ?_, q.1, ?_, ?_⟩
  · intro r p p' hd
    exact hrel _ _ _ hd.1.2
  · ext p
    simp only [hsF, padScenario, hsA, liftScenario, hF, Set.mem_union, Set.mem_image,
      coe_union, coe_map, Function.Embedding.coe_subtype, mem_coe]
    constructor
    · rintro ((⟨z, hz, rfl⟩ | hp) | ⟨z, hz, rfl⟩)
      · exact Or.inr ⟨z, hBZ (Set.mem_toFinset.2 hz), rfl⟩
      · exact Or.inl hp
      · exact Or.inr ⟨z, hz, rfl⟩
    · rintro (hp | ⟨z, hz, rfl⟩)
      · exact Or.inl (Or.inr hp)
      · exact Or.inr ⟨z, hz, rfl⟩
  · rw [hF, card_union_of_disjoint hdisj, card_map, hXc, hZc]
    omega
  · have hin : (fun i => (sF.input i).2) = fun _ => correctPred X := rfl
    rw [hin, wrongBits_correctPred_of_subset subset_union_left, hFX, card_map, hZc]
    have hFc : F.card = f := by rw [hF, card_union_of_disjoint hdisj, card_map, hXc, hZc]; omega
    rw [hFc, mul_comm, ← hn]
    calc f' * (n - f) ≤ Bd / (n - f) * (n - f) := Nat.mul_le_mul_right _ hf'B
      _ ≤ Bd := Nat.div_mul_le_self _ _
  · simp only [hF, mem_union, mem_map, Function.Embedding.coe_subtype, not_or, not_exists,
      not_and]
    refine ⟨q.2, fun z hz hzq => ?_⟩
    have := hZq hz
    rw [Subtype.ext hzq] at this
    simp at this
  · intro r hr
    rw [hsF, status_padScenario, hsA, status_liftScenario]
    apply hslow
    rw [hXc]
    have : t - (f - f') = t - f + f' := by omega
    rw [this]
    exact hr

/-- **Theorem 13 of [BDEG25]**, conditional on the cited early-deciding lower bound
(`EarlyDecidingLB`), with the sharper bound of the paper's proof: some honest process has not
decided before round `min (f' + 2) (t - f + f' + 1)`, `f' = min f ⌊Bd / (n - f)⌋`, in a reliable
execution with exactly `f` Byzantine processes and at most `Bd` wrong prediction bits. -/
theorem roundLowerBound {P V : Type*} [Fintype P] [DecidableEq P] {M : Type}
    {alg : Protocol P (V × (P → Bool)) M V} {t f : ℕ}
    (hA : Solves ⊤ alg {S | S.ncard ≤ t} BAP) (hft : f ≤ t) (htn : t + 2 ≤ Fintype.card P)
    (Bd : ℕ) (hLB : ∀ X : Finset P, X.card ≤ f → EarlyDecidingLB {p // p ∉ X} V (t - X.card)) :
    ∃ (s : Scenario P (V × (P → Bool)) M) (F : Finset P),
      s.Reliable ∧ s.byz = ↑F ∧ F.card = f ∧ wrongBits F (fun i => (s.input i).2) ≤ Bd ∧
      ∃ p ∉ F, ∀ r < min (min f (Bd / (Fintype.card P - f)) + 2)
          (t - f + min f (Bd / (Fintype.card P - f)) + 1), status ⊤ alg s r p = none :=
  roundLowerBoundWith _ hA hft htn Bd hLB

/-- **Theorem 13 of [BDEG25]** (the paper's statement), conditional on the cited early-deciding lower
bound: for `f ≤ t < n - 1` there is a reliable execution with exactly `f` Byzantine processes and at
most `Bd` wrong prediction bits in which some honest process has not decided before round
`min {f + 2, t + 1, ⌊Bd/(n - f)⌋ + 2, ⌊Bd/(n - t)⌋ + 1}`. -/
theorem roundLowerBound_paper {P V : Type*} [Fintype P] [DecidableEq P] {M : Type}
    {alg : Protocol P (V × (P → Bool)) M V} {t f : ℕ}
    (hA : Solves ⊤ alg {S | S.ncard ≤ t} BAP) (hft : f ≤ t) (htn : t + 2 ≤ Fintype.card P)
    (Bd : ℕ) (hLB : ∀ X : Finset P, X.card ≤ f → EarlyDecidingLB {p // p ∉ X} V (t - X.card)) :
    ∃ (s : Scenario P (V × (P → Bool)) M) (F : Finset P),
      s.Reliable ∧ s.byz = ↑F ∧ F.card = f ∧ wrongBits F (fun i => (s.input i).2) ≤ Bd ∧
      ∃ p ∉ F, ∀ r < min (min (f + 2) (t + 1))
          (min (Bd / (Fintype.card P - f) + 2) (Bd / (Fintype.card P - t) + 1)),
        status ⊤ alg s r p = none := by
  obtain ⟨s, F, h1, h2, h3, h4, p, hp, hslow⟩ := roundLowerBound hA hft htn Bd hLB
  refine ⟨s, F, h1, h2, h3, h4, p, hp, fun r hr => hslow r (lt_of_lt_of_le hr ?_)⟩
  clear hslow hr
  rcases hft.lt_or_eq with hlt | rfl
  · generalize Bd / (Fintype.card P - f) = a
    generalize Bd / (Fintype.card P - t) = b
    omega
  · generalize Bd / (Fintype.card P - f) = a
    omega

/-- **Theorem 13 of [BDEG25]**, with the cited bound assumed in the form `DRSBound V` (for all process
sets). -/
theorem roundLowerBound_of_DRS {P V : Type} [Fintype P] [DecidableEq P] {M : Type}
    {alg : Protocol P (V × (P → Bool)) M V} {t f : ℕ}
    (hA : Solves ⊤ alg {S | S.ncard ≤ t} BAP) (hft : f ≤ t) (htn : t + 2 ≤ Fintype.card P)
    (Bd : ℕ) (hDRS : DRSBound V) :
    ∃ (s : Scenario P (V × (P → Bool)) M) (F : Finset P),
      s.Reliable ∧ s.byz = ↑F ∧ F.card = f ∧ wrongBits F (fun i => (s.input i).2) ≤ Bd ∧
      ∃ p ∉ F, ∀ r < min (min (f + 2) (t + 1))
          (min (Bd / (Fintype.card P - f) + 2) (Bd / (Fintype.card P - t) + 1)),
        status ⊤ alg s r p = none := by
  refine roundLowerBound_paper hA hft htn Bd fun X hX => hDRS _ _ ?_
  rw [Fintype.card_subtype_compl, Fintype.card_coe]
  omega

end BAWithPredictions
