import Papers.PODC2025.BAWithPredictions.UnauthPhase
import Papers.PODC2025.BAWithPredictions.RoundModel

/-!
# Unauthenticated Byzantine agreement with classification (Section 7.3)

**Algorithm 5** of [BDEG25] as a CSLib round algorithm `alg5 k`, and **Theorem 5**.

Process `p_i` gets as input its proposal `x_i` and its classification vector `c_i` (the output of
Algorithm 2, `classify`). The first `(2k+1)(3k+1)` positions of `π(c_i)` are split into `2k+1`
blocks of `3k+1` positions; in phase `φ` (0-indexed here, `φ = 0, …, 2k`) `p_i` listens to the
processes in block `φ` (`Lset k c_i φ`). Each phase has 5 rounds:

| round `5φ + t` | `t = 0`       | `t = 1`       | `t = 2`      | `t = 3`       | `t = 4`       |
|----------------|---------------|---------------|--------------|---------------|---------------|
| Algorithm 5    | line 6, GC r1 | line 6, GC r2 | line 7–8     | line 9, GC r1 | line 9, GC r2, lines 10–14 |

The honest `p_i` sends (to everybody, including itself) only in the phase with `i ∈ L_i`; the
message is always the pair `(value, L_i)` (the set is only used by conciliation).

**Deviation from the paper (no early return).** In the paper a process that decided in phase
`φ < 2k+1` takes part in phase `φ + 1` and then returns (line 10); here processes keep running
until the end of phase `2k+1`. This only adds honest participation, does not change the decision
(the decision is fixed at line 12) and does not change the message bound (an honest process
sends only in the phase in which it belongs to its own listening set). The output (`decide`) is
`decision_i`: it is set when the second graded consensus of a phase first returns grade `1`
(line 12), or, for a process that has not decided, to its current value at the end of phase
`2k+1` (line 14). After round `5(2k+1)` nobody sends and states do not change.

Main results (`E` a synchronous round execution with faulty set `F`, `|F| ≤ t`, `c i = (inp i).2`):

* `theorem5_agreement`, `theorem5_strongUnanimity` (Lemmas 20 and 16): if `|mis F c| ≤ k` and
  `(2k+1)(3k+1) ≤ n - t - k`, all honest processes output the same value, and the common input if
  all honest inputs coincide;
* `theorem5_termination`: unconditionally every process has output by round `5(2k+1)`;
* `theorem5_msgs_per_process`: unconditionally every honest process sends at most `5(n-1)`
  messages; `theorem5_msgs`: under the hypotheses, the honest processes send at most
  `5n((2k+1)(3k+1) + k)` messages in total.
-/

set_option linter.unusedSectionVars false

namespace BAWithPredictions.Unauth

open Finset Cslib.Byzantine.PartialSync

variable {P V : Type*} [Fintype P] [LinearOrder P] [LinearOrder V]

/-! ### Listening sets -/

/-- The listening set of a process with classification `c` in phase `φ` (0-indexed): the
processes in positions `φ(3k+1)+1, …, φ(3k+1)+3k+1` of `π(c)` (Algorithm 5, line 5). -/
def Lset (k : ℕ) (c : P → Bool) (φ : ℕ) : Finset P :=
  univ.filter fun j => φ * (3 * k + 1) + 1 ≤ pos c j ∧ pos c j ≤ φ * (3 * k + 1) + (3 * k + 1)

theorem card_Lset_le (k : ℕ) (c : P → Bool) (φ : ℕ) : (Lset k c φ).card ≤ 3 * k + 1 := by
  have h : (Lset k c φ).image (pos c) ⊆
      Icc (φ * (3 * k + 1) + 1) (φ * (3 * k + 1) + (3 * k + 1)) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    simp only [Lset, mem_filter, mem_univ, true_and] at hj
    exact mem_Icc.mpr hj
  rw [← card_image_of_injective _ (pos_injective c)]
  refine (card_le_card h).trans ?_
  simp

/-- A process belongs to the listening set of exactly one phase. -/
theorem mem_Lset_iff {k : ℕ} {c : P → Bool} {φ : ℕ} {j : P} :
    j ∈ Lset k c φ ↔ φ = (pos c j - 1) / (3 * k + 1) := by
  have h1 := one_le_pos c j
  simp only [Lset, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨ha, hb⟩
    refine (Nat.div_eq_of_lt_le (by omega) ?_).symm
    rw [Nat.add_mul, one_mul]; omega
  · intro h
    have e1 := Nat.div_mul_le_self (pos c j - 1) (3 * k + 1)
    have e2 : pos c j - 1 < (pos c j - 1) / (3 * k + 1) * (3 * k + 1) + (3 * k + 1) :=
      Nat.lt_div_mul_add (by omega)
    rw [← h] at e1 e2
    constructor <;> omega

/-! ### Algorithm 5 -/

/-- Local state of Algorithm 5: the classification vector, the current value `v_i`, the value
`b_i` of the running graded consensus, the grade `g_i` of the last graded consensus, and the
output `decision_i` (`none` while undecided). -/
structure St (P V : Type*) where
  /-- The classification vector `c_i`. -/
  c : P → Bool
  /-- The current value `v_i`. -/
  v : V
  /-- The value `b_i` after round 1 of the running graded consensus (`none` = `⊥`). -/
  b : Option V
  /-- The grade returned by the last graded consensus. -/
  g : Bool
  /-- The output. -/
  dec : Option V

/-- The number of rounds of Algorithm 5: `2k + 1` phases of 5 rounds. -/
def nRounds (k : ℕ) : ℕ := 5 * (2 * k + 1)

/-- **Algorithm 5 of [BDEG25]** (unauthenticated Byzantine agreement with classification), with
Algorithms 3 and 4 inlined, as a round algorithm. Input of `p_i`: `(x_i, c_i)`. Messages:
`(value, listening set)`. See the module docstring for the round structure and for the
deviation "no early return". -/
noncomputable def alg5 (k : ℕ) :
    RoundAlgorithm P (V × Finset P) (St P V) (V × (P → Bool)) V where
  init _ x := ⟨x.2, x.1, none, false, none⟩
  send r p s _ :=
    if r < nRounds k ∧ p ∈ Lset k s.c (r / 5) then
      (if r % 5 = 1 ∨ r % 5 = 4 then s.b else some s.v).map fun w => (w, Lset k s.c (r / 5))
    else none
  trans r _ s rcv :=
    if r < nRounds k then
      if r % 5 = 0 ∨ r % 5 = 3 then
        { s with b := gcB k (Lset k s.c (r / 5)) fun j => (rcv j).map Prod.fst }
      else if r % 5 = 1 then
        { s with
          v := (gcOut k (Lset k s.c (r / 5)) s.v s.b fun j => (rcv j).map Prod.fst).1
          g := (gcOut k (Lset k s.c (r / 5)) s.v s.b fun j => (rcv j).map Prod.fst).2 }
      else if r % 5 = 2 then
        if s.g then s else { s with v := conc (Lset k s.c (r / 5)) s.v rcv }
      else
        { s with
          v := (gcOut k (Lset k s.c (r / 5)) s.v s.b fun j => (rcv j).map Prod.fst).1
          g := (gcOut k (Lset k s.c (r / 5)) s.v s.b fun j => (rcv j).map Prod.fst).2
          dec := s.dec.or
            (if (gcOut k (Lset k s.c (r / 5)) s.v s.b fun j => (rcv j).map Prod.fst).2 = true ∨
                r / 5 = 2 * k
              then some (gcOut k (Lset k s.c (r / 5)) s.v s.b fun j => (rcv j).map Prod.fst).1
              else none) }
    else s
  decide _ s := s.dec

/-! ### The transition function -/

section Trans

variable {k r : ℕ} {p : P} {s : St P V} {rcv : P → Option (V × Finset P)}

theorem trans_b (hr : r < nRounds k) (h : r % 5 = 0 ∨ r % 5 = 3) :
    (alg5 k).trans r p s rcv =
      { s with b := gcB k (Lset k s.c (r / 5)) fun j => (rcv j).map Prod.fst } := by
  simp only [alg5]; rw [ite_eq_left hr, ite_eq_left h]

theorem trans_gc1 (hr : r < nRounds k) (h : r % 5 = 1) :
    (alg5 k).trans r p s rcv =
      { s with
        v := (gcOut k (Lset k s.c (r / 5)) s.v s.b fun j => (rcv j).map Prod.fst).1
        g := (gcOut k (Lset k s.c (r / 5)) s.v s.b fun j => (rcv j).map Prod.fst).2 } := by
  simp only [alg5]; rw [ite_eq_left hr, ite_eq_right (by omega), ite_eq_left h]

theorem trans_conc (hr : r < nRounds k) (h : r % 5 = 2) :
    (alg5 k).trans r p s rcv =
      if s.g then s else { s with v := conc (Lset k s.c (r / 5)) s.v rcv } := by
  simp only [alg5]
  rw [ite_eq_left hr, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]

theorem trans_gc2 (hr : r < nRounds k) (h : r % 5 = 4) :
    (alg5 k).trans r p s rcv =
      { s with
        v := (gcOut k (Lset k s.c (r / 5)) s.v s.b fun j => (rcv j).map Prod.fst).1
        g := (gcOut k (Lset k s.c (r / 5)) s.v s.b fun j => (rcv j).map Prod.fst).2
        dec := s.dec.or
          (if (gcOut k (Lset k s.c (r / 5)) s.v s.b fun j => (rcv j).map Prod.fst).2 = true ∨
              r / 5 = 2 * k
            then some (gcOut k (Lset k s.c (r / 5)) s.v s.b fun j => (rcv j).map Prod.fst).1
            else none) } := by
  simp only [alg5]
  rw [ite_eq_left hr, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem trans_ge (hr : nRounds k ≤ r) : (alg5 k).trans r p s rcv = s := by
  simp only [alg5]; rw [ite_eq_right (by omega)]

end Trans

/-! ### Executions -/

section Run

variable {k : ℕ} {F : Finset P} {inp : P → V × (P → Bool)}
  (E : RoundRun (alg5 (P := P) (V := V) k) F inp)

/-- The listening set of `p` in phase `φ`. -/
def Lph (inp : P → V × (P → Bool)) (k φ : ℕ) (p : P) : Finset P := Lset k (inp p).2 φ

/-- The values received by `p` in round `r`. -/
def rv (r : ℕ) (p : P) : P → Option V := fun j => (E.rcv r p j).map Prod.fst

theorem c_eq (r : ℕ) (p : P) : (E.s r p).c = (inp p).2 := by
  induction r with
  | zero => rw [E.s_zero]; rfl
  | succ r ih =>
    rw [E.s_succ]
    simp only [alg5]
    split_ifs <;> simp [ih]

theorem s_of_ge {r : ℕ} (hr : nRounds k ≤ r) (p : P) : E.s r p = E.s (nRounds k) p := by
  induction r, hr using Nat.le_induction with
  | base => rfl
  | succ r hr ih =>
    rw [E.s_succ, ← ih]
    simp only [alg5]
    rw [ite_eq_right (by omega)]

theorem dec_succ (r : ℕ) (p : P) {d : V} (h : (E.s r p).dec = some d) :
    (E.s (r + 1) p).dec = some d := by
  rw [E.s_succ]
  simp only [alg5]
  split_ifs <;> simp [h]

/-- Outputs are irrevocable. -/
theorem dec_mono {r r' : ℕ} (hr : r ≤ r') (p : P) {d : V} (h : (E.s r p).dec = some d) :
    (E.s r' p).dec = some d := by
  induction r', hr using Nat.le_induction with
  | base => exact h
  | succ r' _ ih => exact dec_succ E r' p ih

section Phase

variable {φ : ℕ} (hφ : φ < 2 * k + 1) (p : P)
include hφ

private theorem lt5 (t : ℕ) (ht : t < 5) : 5 * φ + t < nRounds k := by
  unfold nRounds; omega

theorem step0 :
    (E.s (5 * φ + 1) p).v = (E.s (5 * φ) p).v ∧
    (E.s (5 * φ + 1) p).b = gcB k (Lph inp k φ p) (rv E (5 * φ) p) ∧
    (E.s (5 * φ + 1) p).dec = (E.s (5 * φ) p).dec := by
  have h1 : 5 * φ < nRounds k := by unfold nRounds; omega
  have h3 : (5 * φ) / 5 = φ := by omega
  rw [E.s_succ, trans_b h1 (Or.inl (by omega))]
  refine ⟨rfl, ?_, rfl⟩
  simp only [h3, c_eq]; rfl

theorem step1 :
    (E.s (5 * φ + 2) p).v = (gcOut k (Lph inp k φ p) (E.s (5 * φ) p).v
      (gcB k (Lph inp k φ p) (rv E (5 * φ) p)) (rv E (5 * φ + 1) p)).1 ∧
    (E.s (5 * φ + 2) p).g = (gcOut k (Lph inp k φ p) (E.s (5 * φ) p).v
      (gcB k (Lph inp k φ p) (rv E (5 * φ) p)) (rv E (5 * φ + 1) p)).2 ∧
    (E.s (5 * φ + 2) p).dec = (E.s (5 * φ) p).dec := by
  have h1 := lt5 hφ 1 (by omega)
  have h3 : (5 * φ + 1) / 5 = φ := by omega
  obtain ⟨e1, e2, e3⟩ := step0 E hφ p
  rw [E.s_succ, trans_gc1 h1 (by omega)]
  simp only [h3, c_eq, e1, e2, e3]
  exact ⟨rfl, rfl, trivial⟩

theorem step2 :
    (E.s (5 * φ + 3) p).v = (if (E.s (5 * φ + 2) p).g then (E.s (5 * φ + 2) p).v
      else conc (Lph inp k φ p) (E.s (5 * φ + 2) p).v (E.rcv (5 * φ + 2) p)) ∧
    (E.s (5 * φ + 3) p).dec = (E.s (5 * φ) p).dec := by
  have h1 := lt5 hφ 2 (by omega)
  have h3 : (5 * φ + 2) / 5 = φ := by omega
  obtain ⟨-, -, e3⟩ := step1 E hφ p
  rw [E.s_succ, trans_conc h1 (by omega)]
  cases (E.s (5 * φ + 2) p).g <;> simp [h3, c_eq, Lph, e3]

theorem step3 :
    (E.s (5 * φ + 4) p).v = (E.s (5 * φ + 3) p).v ∧
    (E.s (5 * φ + 4) p).b = gcB k (Lph inp k φ p) (rv E (5 * φ + 3) p) ∧
    (E.s (5 * φ + 4) p).dec = (E.s (5 * φ) p).dec := by
  have h1 := lt5 hφ 3 (by omega)
  have h3 : (5 * φ + 3) / 5 = φ := by omega
  obtain ⟨-, e3⟩ := step2 E hφ p
  rw [E.s_succ, trans_b h1 (Or.inr (by omega))]
  refine ⟨rfl, ?_, e3⟩
  simp only [h3, c_eq]; rfl

theorem step4 :
    (E.s (5 * φ + 5) p).v = (gcOut k (Lph inp k φ p) (E.s (5 * φ + 3) p).v
      (gcB k (Lph inp k φ p) (rv E (5 * φ + 3) p)) (rv E (5 * φ + 4) p)).1 ∧
    (E.s (5 * φ + 5) p).g = (gcOut k (Lph inp k φ p) (E.s (5 * φ + 3) p).v
      (gcB k (Lph inp k φ p) (rv E (5 * φ + 3) p)) (rv E (5 * φ + 4) p)).2 ∧
    (E.s (5 * φ + 5) p).dec = (E.s (5 * φ) p).dec.or
      (if (gcOut k (Lph inp k φ p) (E.s (5 * φ + 3) p).v
            (gcB k (Lph inp k φ p) (rv E (5 * φ + 3) p)) (rv E (5 * φ + 4) p)).2 = true ∨
          φ = 2 * k
        then some (gcOut k (Lph inp k φ p) (E.s (5 * φ + 3) p).v
          (gcB k (Lph inp k φ p) (rv E (5 * φ + 3) p)) (rv E (5 * φ + 4) p)).1 else none) := by
  have h1 := lt5 hφ 4 (by omega)
  have h3 : (5 * φ + 4) / 5 = φ := by omega
  obtain ⟨e1, e2, e3⟩ := step3 E hφ p
  rw [E.s_succ, trans_gc2 h1 (by omega)]
  simp only [h3, c_eq, e1, e2, e3]
  exact ⟨rfl, rfl, rfl⟩

/-- Lines 10–14 of Algorithm 5: the output after phase `φ`. -/
theorem step4_dec : (E.s (5 * φ + 5) p).dec = (E.s (5 * φ) p).dec.or
    (if (E.s (5 * φ + 5) p).g = true ∨ φ = 2 * k then some (E.s (5 * φ + 5) p).v else none) := by
  rw [(step4 E hφ p).2.2, ← (step4 E hφ p).1, ← (step4 E hφ p).2.1]


/-! #### Receptions in a synchronous execution -/

variable {E} (hs : E.SyncFrom 0)
include hs

theorem rcv_eq {t : ℕ} (ht : t < 5) {i j : P} (hi : i ∉ F) (hj : j ∉ F) :
    E.rcv (5 * φ + t) i j = if j ∈ Lph inp k φ j then
      (if t = 1 ∨ t = 4 then (E.s (5 * φ + t) j).b else some (E.s (5 * φ + t) j).v).map
        fun w => (w, Lph inp k φ j)
      else none := by
  have h1 := lt5 hφ t ht
  have h2 : (5 * φ + t) % 5 = t := by omega
  have h3 : (5 * φ + t) / 5 = φ := by omega
  rw [hs _ (Nat.zero_le _) i j hi hj]
  simp only [alg5, h1, true_and, h2, h3, c_eq, Lph]

theorem rcv_eq_v {t : ℕ} (ht : t = 0 ∨ t = 2 ∨ t = 3) {i j : P} (hi : i ∉ F) (hj : j ∉ F) :
    E.rcv (5 * φ + t) i j = if j ∈ Lph inp k φ j then
      some ((E.s (5 * φ + t) j).v, Lph inp k φ j) else none := by
  rw [rcv_eq hφ hs (by omega) hi hj, ite_eq_right (c := t = 1 ∨ t = 4) (by omega)]
  rfl

theorem rcv_eq_b {t : ℕ} (ht : t = 1 ∨ t = 4) {i j : P} (hi : i ∉ F) (hj : j ∉ F) :
    E.rcv (5 * φ + t) i j = if j ∈ Lph inp k φ j then
      (E.s (5 * φ + t) j).b.map fun w => (w, Lph inp k φ j) else none := by
  rw [rcv_eq hφ hs (by omega) hi hj, ite_eq_left (c := t = 1 ∨ t = 4) ht]

theorem gc1_round1 : GCRound1 F (Lph inp k φ) (fun j => (E.s (5 * φ) j).v) (rv E (5 * φ)) := by
  intro i hi j hj
  have := rcv_eq_v hφ hs (t := 0) (by omega) hi hj
  simp only [Nat.add_zero] at this
  simp only [rv, this]
  split_ifs <;> rfl

theorem gc1_round2 : GCRound2 F k (Lph inp k φ) (rv E (5 * φ)) (rv E (5 * φ + 1)) := by
  intro i hi j hj
  have := rcv_eq_b hφ hs (t := 1) (by omega) hi hj
  simp only [rv, this, (step0 E hφ j).2.1]
  split_ifs <;> simp [Option.map_map, Function.comp_def]

theorem conc_round : CRound F (Lph inp k φ) (fun j => (E.s (5 * φ + 2) j).v)
    (E.rcv (5 * φ + 2)) := by
  intro i hi j hj
  exact rcv_eq_v hφ hs (t := 2) (by omega) hi hj

theorem gc2_round1 : GCRound1 F (Lph inp k φ) (fun j => (E.s (5 * φ + 3) j).v)
    (rv E (5 * φ + 3)) := by
  intro i hi j hj
  have := rcv_eq_v hφ hs (t := 3) (by omega) hi hj
  simp only [rv, this]
  split_ifs <;> rfl

theorem gc2_round2 : GCRound2 F k (Lph inp k φ) (rv E (5 * φ + 3)) (rv E (5 * φ + 4)) := by
  intro i hi j hj
  have := rcv_eq_b hφ hs (t := 4) (by omega) hi hj
  simp only [rv, this, (step3 E hφ j).2.1]
  split_ifs <;> simp [Option.map_map, Function.comp_def]

/-! #### One phase -/

variable {G : Finset P} (hC : CoreSet F k (Lph inp k φ) G)
include hC

omit p in
/-- If all honest processes enter the second graded consensus of a phase with `w`, they all
return `(w, 1)` (Lemma 8). -/
theorem gc2_unanimous {w : V} (hw : ∀ i ∉ F, (E.s (5 * φ + 3) i).v = w) :
    ∀ i ∉ F, (E.s (5 * φ + 5) i).v = w ∧ (E.s (5 * φ + 5) i).g = true := by
  have hB := lemma8 hC (gc2_round1 hφ hs) (gc2_round2 hφ hs) hw
  intro i hi
  obtain ⟨e1, e2, -⟩ := step4 E hφ i
  rw [e1, e2, hB i hi]
  exact ⟨rfl, rfl⟩

omit p in
/-- A phase that starts with all honest processes holding `w` ends with all of them holding `w`
with grade `1` (Lemma 8 twice; Lemmas 16 and 17 of [BDEG25]). -/
theorem phase_unanimous {w : V} (hw : ∀ i ∉ F, (E.s (5 * φ) i).v = w) :
    ∀ i ∉ F, (E.s (5 * φ + 5) i).v = w ∧ (E.s (5 * φ + 5) i).g = true := by
  have hA := lemma8 hC (gc1_round1 hφ hs) (gc1_round2 hφ hs) hw
  refine gc2_unanimous hφ hs hC fun i hi => ?_
  obtain ⟨e1, e2, -⟩ := step1 E hφ i
  rw [(step2 E hφ i).1, e2, e1, hA i hi]
  rfl

omit p in
/-- If an honest process gets grade `1` from the second graded consensus of a phase, all honest
processes end the phase with its value (Lemma 9; Lemma 17 of [BDEG25]). -/
theorem phase_coherent {i₀ : P} (hi₀ : i₀ ∉ F) (hg : (E.s (5 * φ + 5) i₀).g = true) :
    ∀ i ∉ F, (E.s (5 * φ + 5) i).v = (E.s (5 * φ + 5) i₀).v := by
  intro i hi
  rw [(step4 E hφ i).1, (step4 E hφ i₀).1]
  rw [(step4 E hφ i₀).2.1] at hg
  exact lemma9 hC (gc2_round1 hφ hs) (gc2_round2 hφ hs) hi₀ hg i hi

omit p in
/-- **Lemma 18 of [BDEG25]** (the phase part). If `L_i ⊆ H` for all honest `i` in phase `φ`, all
honest processes get grade `1` from the second graded consensus of the phase. -/
theorem phase_clean (hL : ∀ i ∉ F, ∀ j ∈ Lph inp k φ i, j ∉ F) :
    ∀ i ∉ F, (E.s (5 * φ + 5) i).g = true := by
  have hcr := conc_round hφ hs (E := E)
  -- all honest processes enter the second graded consensus with the same value
  have hsame : ∀ i ∉ F, ∀ i' ∉ F, (E.s (5 * φ + 3) i).v = (E.s (5 * φ + 3) i').v := by
    by_cases hex : ∃ i₀ ∉ F, (E.s (5 * φ + 2) i₀).g = true
    · obtain ⟨i₀, hi₀, hg⟩ := hex
      have hco : ∀ i ∉ F, (E.s (5 * φ + 2) i).v = (E.s (5 * φ + 2) i₀).v := by
        intro i hi
        rw [(step1 E hφ i).1, (step1 E hφ i₀).1]
        rw [(step1 E hφ i₀).2.1] at hg
        exact lemma9 hC (gc1_round1 hφ hs) (gc1_round2 hφ hs) hi₀ hg i hi
      have hconc := lemma14 hC hL hcr hco
      have : ∀ i ∉ F, (E.s (5 * φ + 3) i).v = (E.s (5 * φ + 2) i₀).v := by
        intro i hi
        rw [(step2 E hφ i).1]
        split_ifs
        · exact hco i hi
        · exact hconc i hi
      intro i hi i' hi'
      rw [this i hi, this i' hi']
    · push Not at hex
      have : ∀ i ∉ F, (E.s (5 * φ + 3) i).v =
          conc (Lph inp k φ i) (E.s (5 * φ + 2) i).v (E.rcv (5 * φ + 2) i) := by
        intro i hi
        rw [(step2 E hφ i).1, ite_eq_right (by simpa using hex i hi)]
      intro i hi i' hi'
      rw [this i hi, this i' hi']
      exact lemma13 hC hL hcr hi hi'
  intro i hi
  exact (gc2_unanimous hφ hs hC (fun i' hi' => hsame i' hi' i hi) i hi).2

end Phase

/-- Termination (unconditional): every process has an output after round `5(2k+1)`. -/
theorem dec_isSome (p : P) : (E.s (nRounds k) p).dec.isSome := by
  have := (step4 E (φ := 2 * k) (by omega) p).2.2
  rw [show nRounds k = 5 * (2 * k) + 5 by unfold nRounds; ring, this]
  cases (E.s (5 * (2 * k)) p).dec <;> simp

/-! ### Agreement and strong unanimity -/

variable {E} (hs : E.SyncFrom 0)

/-- `D φ w`: at the beginning of phase `φ` every honest process holds `w` and has output nothing
or `w`. -/
def Inv (E : RoundRun (alg5 (P := P) (V := V) k) F inp) (φ : ℕ) (w : V) : Prop :=
  ∀ i ∉ F, (E.s (5 * φ) i).v = w ∧ ((E.s (5 * φ) i).dec = none ∨ (E.s (5 * φ) i).dec = some w)

include hs in
theorem inv_step {φ : ℕ} (hφ : φ < 2 * k + 1) (hcore : ∃ G, CoreSet F k (Lph inp k φ) G) {w : V}
    (h : Inv E φ w) : Inv E (φ + 1) w := by
  obtain ⟨G, hC⟩ := hcore
  have hU := phase_unanimous hφ hs hC (fun i hi => (h i hi).1)
  intro i hi
  rw [show 5 * (φ + 1) = 5 * φ + 5 by ring]
  obtain ⟨hv, hg⟩ := hU i hi
  refine ⟨hv, Or.inr ?_⟩
  rw [step4_dec E hφ i]
  rcases (h i hi).2 with h' | h' <;> simp [h', hv, hg]

include hs in
theorem inv_final {φ : ℕ} (hφ : φ ≤ 2 * k + 1)
    (hcore : ∀ φ < 2 * k + 1, ∃ G, CoreSet F k (Lph inp k φ) G) {w : V} (h : Inv E φ w) :
    ∀ i ∉ F, (E.s (nRounds k) i).dec = some w := by
  have key : ∀ m, φ ≤ m → m ≤ 2 * k + 1 → Inv E m w := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => intro _; exact h
    | succ m hm ih => intro hm'; exact inv_step hs (by omega) (hcore m (by omega)) (ih (by omega))
  have hN := key _ hφ le_rfl
  intro i hi
  have := dec_isSome E i
  rcases (hN i hi).2 with h' | h'
  · unfold nRounds at this; rw [h'] at this; simp at this
  · exact h'

include hs in
/-- Agreement (from the core sets in every phase and a phase with `L_i ⊆ H`): all honest outputs
after round `5(2k+1)` coincide (Lemmas 17, 18, 20 of [BDEG25]). -/
theorem agreement_of
    (hcore : ∀ φ < 2 * k + 1, ∃ G, CoreSet F k (Lph inp k φ) G)
    (hclean : ∃ φ < 2 * k + 1, ∀ i ∉ F, ∀ j ∈ Lph inp k φ i, j ∉ F) :
    ∀ i ∉ F, ∀ i' ∉ F, (E.s (nRounds k) i).dec = (E.s (nRounds k) i').dec := by
  intro i₁ hi₁ i₂ hi₂
  classical
  obtain ⟨φs, hφs, hcl⟩ := hclean
  -- the first phase in which some honest process gets grade 1 in the second graded consensus
  have hex : ∃ φ, φ < 2 * k + 1 ∧ ∃ i ∉ F, (E.s (5 * φ + 5) i).g = true := by
    obtain ⟨G, hC⟩ := hcore φs hφs
    exact ⟨φs, hφs, i₁, hi₁, phase_clean hφs hs hC hcl i₁ hi₁⟩
  let φ₀ := Nat.find hex
  obtain ⟨hφ₀, i₀, hi₀, hg₀⟩ := Nat.find_spec hex
  have hmin : ∀ φ < φ₀, ∀ i ∉ F, (E.s (5 * φ + 5) i).g = false := by
    intro φ hφ i hi
    have := Nat.find_min hex hφ
    push Not at this
    simpa using this (by omega) i hi
  -- nobody has decided before phase `φ₀`
  have hnone : ∀ φ ≤ φ₀, ∀ i ∉ F, (E.s (5 * φ) i).dec = none := by
    intro φ hφ
    induction φ with
    | zero => intro i _; rw [Nat.mul_zero, E.s_zero]; rfl
    | succ φ ih =>
      intro i hi
      rw [show 5 * (φ + 1) = 5 * φ + 5 by ring, step4_dec E (φ := φ) (by omega) i,
        ih (by omega) i hi]
      simp [hmin φ (by omega) i hi, show φ ≠ 2 * k by omega]
  have hφ₀' : φ₀ < 2 * k + 1 := hφ₀
  obtain ⟨G, hC⟩ := hcore φ₀ hφ₀'
  have hco := phase_coherent hφ₀' hs hC hi₀ hg₀
  have hinv : Inv E (φ₀ + 1) (E.s (5 * φ₀ + 5) i₀).v := by
    intro i hi
    rw [show 5 * (φ₀ + 1) = 5 * φ₀ + 5 by ring]
    refine ⟨hco i hi, ?_⟩
    rw [step4_dec E hφ₀' i, hnone φ₀ le_rfl i hi]
    split_ifs <;> simp [hco i hi]
  have := inv_final hs (by omega) hcore hinv
  rw [this i₁ hi₁, this i₂ hi₂]

include hs in
/-- Strong unanimity from the core sets in every phase (Lemma 16 of [BDEG25]). -/
theorem unanimity_of (hcore : ∀ φ < 2 * k + 1, ∃ G, CoreSet F k (Lph inp k φ) G) {w : V}
    (hw : ∀ i ∉ F, (inp i).1 = w) : ∀ i ∉ F, (E.s (nRounds k) i).dec = some w := by
  refine inv_final hs (Nat.zero_le _) hcore fun i hi => ?_
  rw [Nat.mul_zero, E.s_zero]
  exact ⟨hw i hi, Or.inl rfl⟩

end Run

/-! ### Core sets and a clean phase from the classification (Lemmas 5, 15, 19) -/

section Classification

variable {k t : ℕ} {F : Finset P} {inp : P → V × (P → Bool)}

/-- Core sets (Lemma 5 of [BDEG25], as used in Section 7.3): in every phase there is a core set of
`2k + 1` honest processes in all honest listening sets. -/
theorem core_of_mis (hF : F.card ≤ t) (hk : (mis F fun i => (inp i).2).card ≤ k)
    (hn : (2 * k + 1) * (3 * k + 1) ≤ Fintype.card P - t - k) {φ : ℕ} (hφ : φ < 2 * k + 1) :
    ∃ G, CoreSet F k (Lph inp k φ) G := by
  have hle : (φ + 1) * (3 * k + 1) ≤ (2 * k + 1) * (3 * k + 1) := Nat.mul_le_mul_right _ hφ
  rw [Nat.add_mul, one_mul] at hle
  have hpos : 0 < (2 * k + 1) * (3 * k + 1) := Nat.mul_pos (by omega) (by omega)
  obtain ⟨G, hGF, hGc, hGpos⟩ := lemma5 (F := F) (c := fun i => (inp i).2)
    (ℓ := φ * (3 * k + 1) + 1) (r := φ * (3 * k + 1) + (3 * k + 1)) (by omega) (by omega)
  refine ⟨G, ⟨fun i _ => card_Lset_le _ _ _, hGF, by omega, fun i hi j hj => ?_⟩⟩
  simp only [Lph, Lset, mem_filter, mem_univ, true_and]
  exact hGpos i hi j hj

/-- **Lemma 19 of [BDEG25]** (via Lemma 15): there is a phase in which no honest process listens
to a faulty process. -/
theorem clean_of_mis (hF : F.card ≤ t) (hk : (mis F fun i => (inp i).2).card ≤ k)
    (hn : (2 * k + 1) * (3 * k + 1) ≤ Fintype.card P - t - k) :
    ∃ φ < 2 * k + 1, ∀ i ∉ F, ∀ j ∈ Lph inp k φ i, j ∉ F := by
  have h1 := card_le_card (filter_subset (· ∈ F) (mis F fun i => (inp i).2))
  obtain ⟨φ, hφ, h⟩ := exists_clean_block (c := fun i => (inp i).2) (s := 3 * k + 1)
    (m := 2 * k + 1) hF (by omega) (by omega) (by omega)
  refine ⟨φ, hφ, fun i hi j hj hjF => h i hi j hjF ?_⟩
  simpa [Lph, Lset] using hj

end Classification

/-! ### Theorem 5 -/

section Theorem5

variable {k t : ℕ} {F : Finset P} {inp : P → V × (P → Bool)}
  {E : RoundRun (alg5 (P := P) (V := V) k) F inp}

/-- **Theorem 5 of [BDEG25] (agreement).** If at most `k` processes are misclassified by the
honest processes (`|mis F c| ≤ k`, `c i = (inp i).2`) and `(2k+1)(3k+1) ≤ n - t - k`, then in
every synchronous execution with at most `t` faulty processes all honest processes output the same
value by round `5(2k+1)`. -/
theorem theorem5_agreement (hs : E.SyncFrom 0) (hF : F.card ≤ t)
    (hk : (mis F fun i => (inp i).2).card ≤ k)
    (hn : (2 * k + 1) * (3 * k + 1) ≤ Fintype.card P - t - k) :
    (∀ i, ((E.s (nRounds k) i).dec).isSome) ∧
      ∀ i ∉ F, ∀ i' ∉ F, (E.s (nRounds k) i).dec = (E.s (nRounds k) i').dec :=
  ⟨dec_isSome E, agreement_of hs (fun _ hφ => core_of_mis hF hk hn hφ) (clean_of_mis hF hk hn)⟩

/-- **Theorem 5 of [BDEG25] (strong unanimity).** Under the same hypotheses, if all honest
processes have input `w`, all honest processes output `w` by round `5(2k+1)`. -/
theorem theorem5_strongUnanimity (hs : E.SyncFrom 0) (hF : F.card ≤ t)
    (hk : (mis F fun i => (inp i).2).card ≤ k)
    (hn : (2 * k + 1) * (3 * k + 1) ≤ Fintype.card P - t - k) {w : V}
    (hw : ∀ i ∉ F, (inp i).1 = w) : ∀ i ∉ F, (E.s (nRounds k) i).dec = some w :=
  unanimity_of hs (fun _ hφ => core_of_mis hF hk hn hφ) hw

/-- **Theorem 5 of [BDEG25] (termination, unconditional).** In every execution (no assumption on
the classification or the synchrony), every process has an output after round `5(2k+1)`; outputs
never change (`dec_mono`). -/
theorem theorem5_termination (i : P) : ((E.s (nRounds k) i).dec).isSome := dec_isSome E i

end Theorem5

/-! ### Message complexity -/

section Messages

section Generic

variable {Q Msg S VI VO : Type*} [Fintype Q] [DecidableEq Q] {RA : RoundAlgorithm Q Msg S VI VO}
  {F : Finset Q} {inp : Q → VI}

-- CSLib candidate
/-- The number of messages sent by `p` to other processes in rounds `< M`. -/
def procMsgs (E : RoundRun RA F inp) (M : ℕ) (p : Q) : ℕ :=
  ∑ r ∈ range M, (univ.filter fun q => q ≠ p ∧ RA.send r p (E.s r p) q ≠ none).card

-- CSLib candidate
theorem roundMsgs_eq_sum (E : RoundRun RA F inp) (M : ℕ) :
    roundMsgs E M = ∑ p ∈ univ.filter (· ∉ F), procMsgs E M p := by
  unfold roundMsgs procMsgs; exact Finset.sum_comm

end Generic

variable {k t : ℕ} {F : Finset P} {inp : P → V × (P → Bool)}
  (E : RoundRun (alg5 (P := P) (V := V) k) F inp)

theorem send_ne_none {r : ℕ} {p q : P} {s : St P V} (h : (alg5 k).send r p s q ≠ none) :
    r < nRounds k ∧ p ∈ Lset k s.c (r / 5) := by
  by_contra h'
  exact h (by simp only [alg5]; exact ite_eq_right h')

/-- **Theorem 5 of [BDEG25]** (messages per process, unconditional): every process sends at most
`5(n-1)` messages to other processes (it broadcasts only in the 5 rounds of the phase in which it
belongs to its own listening set). -/
theorem theorem5_msgs_per_process (M : ℕ) (p : P) :
    procMsgs E M p ≤ 5 * (Fintype.card P - 1) := by
  set φp := (pos (inp p).2 p - 1) / (3 * k + 1)
  have hterm : ∀ r ∈ range M,
      (univ.filter fun q => q ≠ p ∧ (alg5 k).send r p (E.s r p) q ≠ none).card ≤
        if r ∈ Ico (5 * φp) (5 * φp + 5) then Fintype.card P - 1 else 0 := by
    intro r _
    split_ifs with hr
    · refine (card_le_card fun q hq => ?_).trans_eq (card_erase_of_mem (mem_univ p))
      · simp only [mem_filter, mem_univ, true_and] at hq
        exact mem_erase.mpr ⟨hq.1, mem_univ q⟩
    · refine le_of_eq (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun q _ hq => hr ?_))
      have h := (send_ne_none hq.2).2
      rw [c_eq, mem_Lset_iff] at h
      rw [mem_Ico]; omega
  calc procMsgs E M p ≤ ∑ r ∈ range M,
        (if r ∈ Ico (5 * φp) (5 * φp + 5) then Fintype.card P - 1 else 0) := sum_le_sum hterm
    _ = ∑ r ∈ range M ∩ Ico (5 * φp) (5 * φp + 5), (Fintype.card P - 1) := sum_ite_mem _ _ _
    _ ≤ 5 * (Fintype.card P - 1) := by
        rw [sum_const, smul_eq_mul]
        refine Nat.mul_le_mul_right _ ((card_le_card inter_subset_right).trans ?_)
        simp

/-- A process that does not belong to its own listening set in any phase sends nothing. -/
theorem procMsgs_eq_zero {M : ℕ} {p : P}
    (hp : (2 * k + 1) * (3 * k + 1) < pos (inp p).2 p) : procMsgs E M p = 0 := by
  refine sum_eq_zero fun r _ => card_eq_zero.mpr (filter_eq_empty_iff.mpr fun q _ hq => ?_)
  obtain ⟨hr, hL⟩ := send_ne_none hq.2
  rw [c_eq] at hL
  simp only [Lset, mem_filter, mem_univ, true_and] at hL
  have : (r / 5 + 1) * (3 * k + 1) ≤ (2 * k + 1) * (3 * k + 1) :=
    Nat.mul_le_mul_right _ (by unfold nRounds at hr; omega)
  rw [Nat.add_mul, one_mul] at this
  omega

/-- **Theorem 5 of [BDEG25]** (total message complexity `O(n k²)`). Under the hypotheses of
Theorem 5, the honest processes send at most `5 n ((2k+1)(3k+1) + k)` messages in total (by
Lemma 6, at most `(2k+1)(3k+1) + k_H` honest processes belong to their own listening set in some
phase). -/
theorem theorem5_msgs (hF : F.card ≤ t) (hk : (mis F fun i => (inp i).2).card ≤ k)
    (hn : (2 * k + 1) * (3 * k + 1) ≤ Fintype.card P - t - k) (M : ℕ) :
    roundMsgs E M ≤ 5 * Fintype.card P * ((2 * k + 1) * (3 * k + 1) + k) := by
  rw [roundMsgs_eq_sum]
  set R := (2 * k + 1) * (3 * k + 1)
  have hR : 0 < R := Nat.mul_pos (by omega) (by omega)
  rw [← sum_filter_of_ne (p := fun p => pos (inp p).2 p ≤ R) fun p _ h => by
    by_contra h'; exact h (procMsgs_eq_zero E (by omega))]
  have hA : ((univ.filter (· ∉ F)).filter fun p => pos (inp p).2 p ≤ R).card ≤ R + k := by
    have h6 := lemma6 (F := F) (c := fun i => (inp i).2) (r := R) (by omega)
    have h7 := card_le_card (filter_subset (· ∉ F) (mis F fun i => (inp i).2))
    refine (card_le_card fun p hp => ?_).trans (h6.trans (by omega))
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact ⟨hp.1, p, hp.1, hp.2⟩
  calc ∑ p ∈ (univ.filter (· ∉ F)).filter (fun p => pos (inp p).2 p ≤ R), procMsgs E M p
      ≤ ∑ _p ∈ (univ.filter (· ∉ F)).filter (fun p => pos (inp p).2 p ≤ R),
          5 * (Fintype.card P - 1) := sum_le_sum fun p _ => theorem5_msgs_per_process E M p
    _ = ((univ.filter (· ∉ F)).filter fun p => pos (inp p).2 p ≤ R).card *
          (5 * (Fintype.card P - 1)) := by rw [sum_const, smul_eq_mul]
    _ ≤ (R + k) * (5 * Fintype.card P) := Nat.mul_le_mul hA (by omega)
    _ = 5 * Fintype.card P * (R + k) := by ring

end Messages

/-! ### Non-vacuity -/

section NonVacuity

variable {Q Msg S VI VO : Type*} [DecidableEq Q]

-- CSLib candidate
/-- The states of the failure-free synchronous execution of a round algorithm. -/
def syncStates (RA : RoundAlgorithm Q Msg S VI VO) (inp : Q → VI) : ℕ → Q → S
  | 0 => fun p => RA.init p (inp p)
  | r + 1 => fun p => RA.trans r p (syncStates RA inp r p)
      (fun q => RA.send r q (syncStates RA inp r q) p)

-- CSLib candidate
/-- A synchronous round execution exists for every round algorithm, faulty set and inputs: the
one in which every process (also those in `F`) follows the algorithm. -/
def syncRun (RA : RoundAlgorithm Q Msg S VI VO) (F : Finset Q) (inp : Q → VI) :
    RoundRun RA F inp where
  s := syncStates RA inp
  rcv r p q := RA.send r q (syncStates RA inp r q) p
  s_zero _ := rfl
  s_succ _ _ := rfl
  honest _ _ _ _ _ h := h

-- CSLib candidate
theorem syncRun_syncFrom (RA : RoundAlgorithm Q Msg S VI VO) (F : Finset Q) (inp : Q → VI) :
    (syncRun RA F inp).SyncFrom 0 := fun _ _ _ _ _ _ => rfl

/-- Correct classifications misclassify nobody. -/
theorem mis_eq_empty_of_correct {F : Finset P} {c : P → P → Bool}
    (h : ∀ i ∉ F, c i = correctPred F) : mis F c = ∅ := by
  ext j
  simp only [mis, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_exists, not_and,
    not_not]
  intro i hi
  rw [h i hi]

/-- **Non-vacuity of Theorem 5.** With correct classifications, the hypotheses of Theorem 5 hold
with `k = 0` for every `t < n` (so Algorithm 5 then solves Byzantine agreement in 5 rounds for any
number of faults), and synchronous executions exist. -/
theorem theorem5_hyps_of_correct {t : ℕ} (ht : t < Fintype.card P) {F : Finset P}
    {inp : P → V × (P → Bool)} (hc : ∀ i ∉ F, (inp i).2 = correctPred F) :
    (syncRun (alg5 (P := P) (V := V) 0) F inp).SyncFrom 0 ∧
      (mis F fun i => (inp i).2).card ≤ 0 ∧
      (2 * 0 + 1) * (3 * 0 + 1) ≤ Fintype.card P - t - 0 := by
  refine ⟨syncRun_syncFrom _ _ _, ?_, by omega⟩
  rw [mis_eq_empty_of_correct hc]; rfl

/-- A concrete instance: `n = 4`, three faulty processes, `k = 0`; Theorem 5 applies. -/
example : ∀ i ∉ ({0, 1, 2} : Finset (Fin 4)),
    ∀ i' ∉ ({0, 1, 2} : Finset (Fin 4)),
    ((syncRun (alg5 (P := Fin 4) (V := Bool) 0) {0, 1, 2}
      fun i => (decide (i = 3), correctPred {0, 1, 2})).s (nRounds 0) i).dec =
    ((syncRun (alg5 (P := Fin 4) (V := Bool) 0) {0, 1, 2}
      fun i => (decide (i = 3), correctPred {0, 1, 2})).s (nRounds 0) i').dec := by
  obtain ⟨hs, hk, hn⟩ := theorem5_hyps_of_correct (V := Bool) (t := 3) (by simp)
    (F := ({0, 1, 2} : Finset (Fin 4)))
    (inp := fun i => (decide (i = 3), correctPred {0, 1, 2})) (fun _ _ => rfl)
  exact (theorem5_agreement hs (by decide) hk hn).2

end NonVacuity

end BAWithPredictions.Unauth
