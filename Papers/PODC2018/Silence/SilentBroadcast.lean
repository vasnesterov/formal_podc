import Papers.PODC2018.Silence.Defs

/-!
# Silent information transfer: Lemmas 1, 2 and Corollary 2 of Goren–Moses (§3.1)

The hypothesis "`P` guarantees that if `¬K_j φ` at time `m − 1` then `j` sends a message to `i` in
round `m`" is formalized as `Prescribes`: in every admissible run in which `j` is alive at time
`m − 1` and does not know `φ`, the protocol's message function prescribes a message to `i`.

"`i` does not receive a round-`m` message from `j`" is `msg alg r j i (m - 1) = none`.

**Correction.** As literally stated, Lemma 2 and Corollary 2 also apply when `i` itself has crashed
by time `m` (a crashed process receives nothing). Then they are false: `i`'s local state is `⊥`, which
carries no information (`corollary2_literal_false`). We add the hypothesis that `i` is alive at time
`m` (`r.Alive i m`). Lemma 1 (reliable systems, `f = 0`) needs no correction.
-/

namespace Papers.PODC2018.Silence

open Podc.SyncCrash Classical

variable {P I M O : Type*} [Fintype P] {alg : Cslib.Byzantine.LockStep.Protocol P I M O}

/-- "`P` guarantees that if `¬K_j φ` at time `m − 1` then `j` sends a message to `i` in round `m`". -/
def Prescribes (alg : Cslib.Byzantine.LockStep.Protocol P I M O) (f : ℕ) (φ : Run P I → Prop)
    (j i : P) (m : ℕ) : Prop :=
  ∀ r' : Run P I, r'.Admissible f → r'.Alive j (m - 1) → ¬ Knows alg f j (m - 1) r' φ →
    alg.send j (r'.input j) (hist alg r' (m - 1) j) i ≠ none

/-- If `i` has the same (non-`⊥`) state at time `m > 0` in two runs, it received the same round-`m`
messages. -/
lemma msg_eq_of_state_eq {r r' : Run P I} {i : P} {m : ℕ} (hm : 0 < m) (hi : r.Alive i m)
    (hs : state alg r' i m = state alg r i m) (j : P) :
    msg alg r' j i (m - 1) = msg alg r j i (m - 1) := by
  rw [state_of_alive hi] at hs
  have hi' : r'.Alive i m := by
    by_contra h; rw [state_eq_none.2 h] at hs; simp at hs
  rw [state_of_alive hi'] at hs
  have hh : hist alg r' m i = hist alg r m i := (Prod.mk.inj (Option.some.inj hs)).2
  have := congrArg (fun h => h[m - 1]?) hh
  simp only [hist_getElem? _ i (show m - 1 < m by omega), Option.some.injEq] at this
  exact congrFun this j

/-- The core of Lemma 2: in a run where `i` (alive at `m`) got no round-`m` message from `j`, and `j`
is correct, `φ` holds. -/
lemma holds_of_silent {f : ℕ} {φ : Run P I → Prop} {i j : P} {m : ℕ} (hm : 0 < m) (hji : j ≠ i)
    (hP : Prescribes alg f φ j i m) {r : Run P I} (hr : r.Admissible f)
    (hno : msg alg r j i (m - 1) = none) (hj : ¬ r.Faulty j) : φ r := by
  by_contra hφ
  have ha := Run.alive_of_not_faulty hj (m - 1)
  have hK : ¬ Knows alg f j (m - 1) r φ := fun hK => hφ (hK.holds hr)
  apply hP r hr ha hK
  rw [msg_eq_deliv, if_pos ⟨hji, ha, fun h => hj (by simp [Run.Faulty, h.1])⟩] at hno
  exact hno

/-- **Lemma 2** of Goren–Moses (with the correction that `i` is alive at time `m`): if `P`
guarantees that `j` sends to `i` in round `m` unless `K_j φ` at time `m − 1`, and `i` receives no
round-`m` message from `j` in `r`, then `K_i(φ ∨ j is faulty)` holds at time `m`. -/
theorem lemma2 {f : ℕ} {φ : Run P I → Prop} {i j : P} {m : ℕ} (hm : 0 < m) (hji : j ≠ i)
    (hP : Prescribes alg f φ j i m) {r : Run P I} (hi : r.Alive i m)
    (hno : msg alg r j i (m - 1) = none) :
    Knows alg f i m r (fun r' => φ r' ∨ r'.Faulty j) := by
  intro r' hr' hs
  by_cases hj : r'.Faulty j
  · exact Or.inr hj
  · exact Or.inl (holds_of_silent hm hji hP hr' (by rw [msg_eq_of_state_eq hm hi hs]; exact hno) hj)

/-- **Corollary 2** of Goren–Moses (silent broadcast, rule S3; with the correction that `i` is alive
at time `m`): if every `j` in a set `S` with `|S| > f` is guaranteed to send to `i` in round `m` unless
`K_j φ` at time `m − 1`, and `i` receives no round-`m` message from any process of `S`, then `K_i φ`
holds at time `m`. -/
theorem corollary2 {f : ℕ} {φ : Run P I → Prop} {i : P} {S : Finset P} {m : ℕ} (hm : 0 < m)
    (hS : f < S.card) (hP : ∀ j ∈ S, j ≠ i ∧ Prescribes alg f φ j i m) {r : Run P I}
    (hi : r.Alive i m) (hno : ∀ j ∈ S, msg alg r j i (m - 1) = none) :
    Knows alg f i m r φ := by
  intro r' hr' hs
  obtain ⟨j, hjS, hj⟩ : ∃ j ∈ S, ¬ r'.Faulty j := by
    by_contra hc
    push Not at hc
    have : S ⊆ r'.faulty := fun j hj => by rw [Run.mem_faulty]; exact hc j hj
    have := (Finset.card_le_card this).trans hr'.1
    omega
  exact holds_of_silent hm (hP j hjS).1 (hP j hjS).2 hr'
    (by rw [msg_eq_of_state_eq hm hi hs]; exact hno j hjS) hj

/-- **Lemma 1** of Goren–Moses (reliable systems): with no failures (`f = 0`), if `P` guarantees
that `j` sends to `i` in round `m` unless `K_j φ` at time `m − 1`, and `i` does not receive a round-`m`
message from `j`, then `K_i φ` holds at time `m`. -/
theorem lemma1 {φ : Run P I → Prop} {i j : P} {m : ℕ} (hm : 0 < m) (hji : j ≠ i)
    (hP : Prescribes alg 0 φ j i m) {r : Run P I} (hr : r.Admissible 0)
    (hno : msg alg r j i (m - 1) = none) :
    Knows alg 0 i m r φ := by
  have hi : r.Alive i m := Run.alive_of_not_faulty (fun h => by
    have h1 : i ∈ r.faulty := by rw [Run.mem_faulty]; exact h
    have h2 : r.faulty.card = 0 := Nat.le_zero.1 hr.1
    rw [Finset.card_eq_zero] at h2; rw [h2] at h1; simp at h1) m
  exact corollary2 (S := {j}) hm (by simp) (by simpa using ⟨hji, hP⟩) hi (by simpa using hno)

/-! ### The literal statements are false when `i` has crashed -/

/-- The protocol of the counterexample: in round 1 every process with value `0` sends a message to
process `0`; nothing else is ever sent. -/
def cexAlg : Cslib.Byzantine.LockStep.Protocol (Fin 3) Bool Unit Decision where
  send _ x h q := if x = false ∧ h = [] ∧ q = 0 then some () else none
  decide _ _ _ := none

/-- The fact `v₁ = 1 ∨ v₂ = 1`. -/
def cexφ (r : Run (Fin 3) Bool) : Prop := r.input 1 = true ∨ r.input 2 = true

/-- The run of the counterexample: all values `1`; process `0` crashes in round 1. -/
def cexRun : Run (Fin 3) Bool := ⟨fun _ => true, fun z => if z = 0 then some 1 else none, fun _ => ∅⟩

/-- Another run, indistinguishable to the crashed process `0` at time 1: all values `0`. -/
def cexRun' : Run (Fin 3) Bool := ⟨fun _ => false, fun z => if z = 0 then some 1 else none, fun _ => ∅⟩

lemma cex_admissible (b : Bool) :
    (⟨fun _ => b, fun z => if z = 0 then some 1 else none, fun _ => ∅⟩ : Run (Fin 3) Bool).Admissible 1 := by
  refine ⟨?_, ?_⟩
  · have : (⟨fun _ => b, fun z => if z = 0 then some 1 else none, fun _ => ∅⟩ :
        Run (Fin 3) Bool).faulty ⊆ {0} := by
      intro z hz
      simp only [Run.mem_faulty, Run.Faulty] at hz
      simp only [Finset.mem_singleton]
      by_contra h; simp [h] at hz
    exact (Finset.card_le_card this).trans (by simp)
  · intro z c hc; simp only at hc; split_ifs at hc <;> simp_all

/-- **The literal Corollary 2 (and Lemma 2) is false**: in `γ_1` with three processes, both processes
of `S = {1, 2}` (`|S| = 2 > 1`) are guaranteed to send to `i = 0` in round 1 unless they know
`φ = (v₁ = 1 ∨ v₂ = 1)`, and in `cexRun` process `0` receives no round-1 message from `S` — but only
because it crashed in round 1; it does not know `φ` (nor `φ ∨ 1 is faulty`) at time 1. -/
theorem corollary2_literal_false :
    (∀ j ∈ ({1, 2} : Finset (Fin 3)), j ≠ 0 ∧ Prescribes cexAlg 1 cexφ j 0 1) ∧
    cexRun.Admissible 1 ∧
    (∀ j ∈ ({1, 2} : Finset (Fin 3)), msg cexAlg cexRun j 0 0 = none) ∧
    ¬ Knows cexAlg 1 0 1 cexRun cexφ ∧
    ¬ Knows cexAlg 1 0 1 cexRun (fun r' => cexφ r' ∨ r'.Faulty 1) := by
  have hs : state cexAlg cexRun' 0 1 = state cexAlg cexRun 0 1 := by
    rw [state_eq_none.2, state_eq_none.2]
    all_goals (intro h; have := h 1 (by simp [cexRun, cexRun']); omega)
  have hφ' : ¬ (cexφ cexRun' ∨ cexRun'.Faulty 1) := by
    simp [cexφ, cexRun', Run.Faulty]
  refine ⟨?_, cex_admissible true, ?_, ?_, ?_⟩
  · intro j hj
    refine ⟨by fin_cases hj <;> decide, ?_⟩
    intro r' hr' _ hK hsend
    apply hK
    intro r'' _ he
    simp only [Nat.sub_self] at he hsend
    have hin : r'.input j = true := by
      by_contra hf
      simp only [Bool.not_eq_true] at hf
      exact absurd hsend (by simp [cexAlg, hf])
    have h0 : r''.Alive j 0 := by
      by_contra hd
      rw [state_eq_none.2 hd, state_of_alive (hr'.alive_zero j)] at he
      simp at he
    rw [state_of_alive h0, state_of_alive (hr'.alive_zero j)] at he
    have : r''.input j = true := by
      have := (Prod.mk.inj (Option.some.inj he)).1; rw [this, hin]
    fin_cases hj
    · exact Or.inl this
    · exact Or.inr this
  · intro j hj
    rw [msg_eq_deliv]
    split_ifs
    · simp [cexAlg, cexRun]
    · rfl
  · intro hK
    exact hφ' (Or.inl (hK cexRun' (cex_admissible false) hs))
  · intro hK
    exact hφ' (hK cexRun' (cex_admissible false) hs)

end Papers.PODC2018.Silence
