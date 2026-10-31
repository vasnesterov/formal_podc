import Cslib.Computability.Distributed.Knowledge.Basic
import Papers.PODC2020.NullMessagesByzantine.Run

/-!
# Silent validation rounds (Definition 1.1, Theorem 1.2)

A deterministic protocol `alg` in the synchronous lock-step Byzantine model on the complete
network (`Cslib.Byzantine.LockStep`, graph `⊤`). Its runs are the reliable scenarios whose
Byzantine set belongs to the adversary structure `Z`; the local state of `i` at time `m` is its
input and its history (`systemOf`), the nonfaulty processes of a run are its honest processes.
Knowledge is CSLib's `Cslib.Knowledge.System.K`.

* `ImplementsSVR alg Z φ m` (Definition 1.1): in every run, every correct `i` sends a message to
  every other process in round `m + 1` if `φ i` fails at time `m`, and sends nothing if it holds.
* `theorem_1_2`: a process `j` that receives no message in round `m + 1` and for which `φ j` held
  at time `m` knows at time `m + 1` that `φ̄_c = ⋀_{correct i} φ_i` held at time `m`.
  `knows_others_of_noMsgs`: without the hypothesis on `φ j`, `j` knows `φ_i` for all correct
  `i ≠ j`.
* `theorem_1_2_literal_false`: the hypothesis on `φ j` is needed when a process does not receive
  its own broadcast (here: two processes, `φ_0` false, `φ_1` true).
* `smallCouncil_svr_round3`, `smallCouncil_svr_round4`: rounds 3 and 4 of SmallCouncil are silent
  validation rounds for "I have a unanimous recommendation" and "I have decided at time 3".
-/

namespace Podc.NullMessagesByzantine

open Cslib.Byzantine.LockStep Cslib.Knowledge

variable {P I M O : Type*}

-- CSLib candidate: `Runs`, `systemOf`, `ImplementsSVR`, `theorem_1_2` (LockStep → Knowledge bridge).
/-- The runs of a protocol against the adversary structure `Z`: reliable scenarios with an
admissible Byzantine set. -/
abbrev Runs (P I M : Type*) (Z : AdvStructure P) : Type _ :=
  {s : Scenario P I M // s.byz ∈ Z ∧ s.Reliable}

/-- The interpreted system of `alg` (complete network): the local state of `i` at time `m` is
`(input, history after m rounds)`; the nonfaulty processes are the honest ones. -/
noncomputable def systemOf (alg : Protocol P I M O) (Z : AdvStructure P) :
    System P (Runs P I M Z) (fun _ => I × History P M) where
  loc i r m := (r.1.input i, hist ⊤ alg r.1 m i)
  nf r := r.1.honest

/-- A family of local facts: `φ i x h` is a fact about the local state (input `x`, history `h`) of
process `i`. -/
abbrev LocalFacts (P I M : Type*) := P → I → History P M → Prop

/-- The global milestone `φ̄_c` at time `m`: `φ_i` held at time `m` for every correct `i`
(a fact about the run, evaluated at any point). -/
def milestone (alg : Protocol P I M O) {Z : AdvStructure P} (φ : LocalFacts P I M) (m : ℕ) :
    Fact (Runs P I M Z) :=
  fun r _ => ∀ i ∈ r.1.honest, φ i (r.1.input i) (hist ⊤ alg r.1 m i)

/-- **Definition 1.1.** `alg` implements a silent validation round for `φ̄_c` in round `m + 1`:
in every run each correct `i` sends a message to everyone (else) in round `m + 1` if `φ_i` does
not hold at time `m`, and sends no message to anyone if `φ_i` holds. -/
def ImplementsSVR (alg : Protocol P I M O) (Z : AdvStructure P) (φ : LocalFacts P I M)
    (m : ℕ) : Prop :=
  ∀ s : Scenario P I M, s.byz ∈ Z → s.Reliable → ∀ i, i ∉ s.byz →
    (¬ φ i (s.input i) (hist ⊤ alg s m i) →
        ∀ q, q ≠ i → (alg.send i (s.input i) (hist ⊤ alg s m i) q).isSome) ∧
    (φ i (s.input i) (hist ⊤ alg s m i) → ∀ q, alg.send i (s.input i) (hist ⊤ alg s m i) q = none)

/-- `j` received no message at all in round `m + 1` (a fact about its local state at
time `m + 1`). -/
def NoMsgs (h : History P M) (m : ℕ) : Prop := ∀ q, (h[m]?.bind fun ib => ib q) = none

/-- `j`, silent in round `m + 1`, knows `φ_i` for every correct `i ≠ j`. -/
theorem knows_others_of_noMsgs {alg : Protocol P I M O} {Z : AdvStructure P}
    {φ : LocalFacts P I M} {m : ℕ} (hsvr : ImplementsSVR alg Z φ m) (r : Runs P I M Z) (j : P)
    (hj : NoMsgs (hist ⊤ alg r.1 (m + 1) j) m) :
    (systemOf alg Z).K j
      (fun r' _ => ∀ i ∈ r'.1.honest, i ≠ j → φ i (r'.1.input i) (hist ⊤ alg r'.1 m i))
      r (m + 1) := by
  rw [System.K_iff]
  intro r' t' hloc i hi hij
  simp only [systemOf, Prod.mk.injEq] at hloc
  obtain ⟨-, hh⟩ := hloc
  have ht' : t' = m + 1 := by simpa using congrArg List.length hh
  subst ht'
  by_contra hφ
  have hsend := (hsvr r'.1 r'.2.1 r'.2.2 i hi).1 hφ j (Ne.symm hij)
  have := hj i
  rw [← hh, getElem?_hist _ _ _ (Nat.lt_succ_self m)] at this
  simp only [Option.bind_some] at this
  rw [deliver_honest _ _ _ r'.2.2 hi (by simpa using hij)] at this
  rw [this] at hsend
  simp at hsend

/-- **Theorem 1.2.** If `alg` implements `svr(φ̄_c)` in round `m + 1`, a process `j` that receives
no message whatsoever in round `m + 1`, and for which `φ_j` held at time `m` (a fact `j` can check
locally; automatic under the convention that a process receives its own broadcasts), knows at
time `m + 1` that `φ̄_c` was true at time `m`. -/
theorem theorem_1_2 {alg : Protocol P I M O} {Z : AdvStructure P} {φ : LocalFacts P I M}
    {m : ℕ} (hsvr : ImplementsSVR alg Z φ m) (r : Runs P I M Z) (j : P)
    (hj : NoMsgs (hist ⊤ alg r.1 (m + 1) j) m)
    (hφj : φ j (r.1.input j) ((hist ⊤ alg r.1 (m + 1) j).take m)) :
    (systemOf alg Z).K j (milestone alg φ m) r (m + 1) := by
  have hK := knows_others_of_noMsgs hsvr r j hj
  rw [System.K_iff] at hK ⊢
  intro r' t' hloc i hi
  by_cases hij : i = j
  · subst hij
    simp only [systemOf, Prod.mk.injEq] at hloc
    obtain ⟨hx, hh⟩ := hloc
    have ht' : t' = m + 1 := by simpa using congrArg List.length hh
    subst ht'
    rw [← take_hist ⊤ alg r'.1 (Nat.le_succ m), hh, hx]
    exact hφj
  · exact hK r' t' hloc i hi hij

/-- **Theorem 1.2 needs `φ_j`.** If a process does not receive its own messages, silence does
not tell `j` anything about its own `φ_j`: with two processes, `φ_i := (input = true)` and the
protocol "send to everyone iff `φ_i` fails", process `0` with input `false` receives nothing in
round 1 (process `1` has input `true`), but `φ̄_c` is false. -/
theorem theorem_1_2_literal_false :
    ∃ (alg : Protocol (Fin 2) Bool Unit Unit) (φ : LocalFacts (Fin 2) Bool Unit),
      ImplementsSVR alg (atMost 0) φ 0 ∧
      ∃ r : Runs (Fin 2) Bool Unit (atMost 0), NoMsgs (hist ⊤ alg r.1 1 0) 0 ∧
        ¬ (systemOf alg (atMost 0)).K 0 (milestone alg φ 0) r 1 := by
  let alg : Protocol (Fin 2) Bool Unit Unit :=
    { send := fun _ x _ _ => if x then none else some (), decide := fun _ _ _ => none }
  let s : Scenario (Fin 2) Bool Unit :=
    { byz := ∅, input := ![false, true], adv := fun _ _ _ => none }
  refine ⟨alg, fun _ x _ => x = true, ?_, ⟨s, by simp [s], fun _ _ _ h => h⟩, ?_, ?_⟩
  · intro s' _ _ i _
    constructor
    · intro h q _; simp [alg, h]
    · intro h q; simp [alg, h]
  · intro q
    rw [getElem?_hist _ _ _ (Nat.zero_lt_one)]
    fin_cases q
    · simp [deliver]
    · simp [deliver, s, alg]
  · intro hK
    have := System.K_iff.1 hK _ _ rfl 0 (by simp [s, Scenario.honest])
    simp [s] at this

/-! ### SmallCouncil's silent validation rounds -/

variable {n : ℕ} {M₂ : Type*}

/-- Round 3 of SmallCouncil is `svr` for "I received a unanimous recommendation" (`¬ Err`). -/
theorem smallCouncil_svr_round3 (sr : Bool) (t : ℕ) (B : Protocol (Fin n) Bool M₂ Bool)
    (Z : AdvStructure (Fin n)) :
    ImplementsSVR (smallCouncilGen sr t B) Z (fun p x h => ¬ Err t p x h) 2 := by
  intro s _ _ i _
  have hl : (hist ⊤ (smallCouncilGen sr t B) s 2 i).length = 2 := length_hist _ _ _ _ _
  constructor
  · intro h q _; rw [send_round2 _ _ _ hl, ite_eq_left (not_not.1 h)]; rfl
  · intro h q; rw [send_round2 _ _ _ hl, ite_eq_right h]

/-- Round 4 of SmallCouncil is `svr` for "I decided at time 3" (`¬ GotErr`). -/
theorem smallCouncil_svr_round4 (sr : Bool) (t : ℕ) (B : Protocol (Fin n) Bool M₂ Bool)
    (Z : AdvStructure (Fin n)) :
    ImplementsSVR (smallCouncilGen sr t B) Z (fun p x h => ¬ GotErr sr t p x h) 3 := by
  intro s _ _ i _
  have hl : (hist ⊤ (smallCouncilGen sr t B) s 3 i).length = 3 := length_hist _ _ _ _ _
  constructor
  · intro h q _; rw [send_round3 _ _ _ hl, ite_eq_left (not_not.1 h)]; rfl
  · intro h q; rw [send_round3 _ _ _ hl, ite_eq_right h]

end Podc.NullMessagesByzantine
