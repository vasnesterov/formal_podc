import Cslib.Computability.Distributed.Byzantine.PartialSync.Model

/-!
# Memoised simulation of concrete PSync runs with arbitrary delays (CSLib candidate)

`Run.st` recomputes the whole history at every step, so evaluating it on a concrete run is
exponential. `simHist` computes the list of all global states up to time `τ` once; it handles
arbitrary delivery times `dl` (the zero-delay version is `simStates` in `Podc/PartialSync/Sim.lean`).
`Run.st_eq_simHist` identifies it with `Run.st`, so facts about a concrete finite run prefix can
be checked by `decide +kernel`.
-/

namespace TetraBFT

open Cslib.Byzantine.PartialSync

variable {n : ℕ} {M S VI VO : Type*}

/-- The global state at time `τ + 1`, given the history `hist` of global states at times `0..τ`. -/
def simNext (A : Algorithm (Fin n) M S VI VO) (bad : Fin n → Bool)
    (byz : Fin n → ℕ → Fin n → List M) (dl : Fin n → ℕ → Fin n → ℕ) (d : S)
    (hist : List (List S)) (τ : ℕ) : List S :=
  List.ofFn fun p => A.step p ((hist.getD τ []).getD p d) fun q =>
    (List.range (τ + 1)).flatMap fun τ' =>
      if dl q τ' p = τ then
        (if bad q then byz q τ' p else A.send q ((hist.getD τ' []).getD q d) p)
      else []

/-- Memoised history of global states at times `0..τ` (`d` is a dummy state). -/
def simHist (A : Algorithm (Fin n) M S VI VO) (inp : Fin n → VI) (bad : Fin n → Bool)
    (byz : Fin n → ℕ → Fin n → List M) (dl : Fin n → ℕ → Fin n → ℕ) (d : S) :
    ℕ → List (List S)
  | 0 => [List.ofFn fun p => A.init p (inp p)]
  | τ + 1 =>
    let h := simHist A inp bad byz dl d τ
    h ++ [simNext A bad byz dl d h τ]

section

variable (A : Algorithm (Fin n) M S VI VO) (inp : Fin n → VI) (bad : Fin n → Bool)
  (byz : Fin n → ℕ → Fin n → List M) (dl : Fin n → ℕ → Fin n → ℕ) (d : S)

theorem simHist_length : ∀ τ, (simHist A inp bad byz dl d τ).length = τ + 1
  | 0 => rfl
  | τ + 1 => by simp [simHist, simHist_length τ]

theorem simHist_getD_succ (τ σ : ℕ) (h : σ ≤ τ) :
    (simHist A inp bad byz dl d (τ + 1)).getD σ [] = (simHist A inp bad byz dl d τ).getD σ [] := by
  simp only [simHist, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by rw [simHist_length]; omega)]

theorem simHist_getD_le {σ τ : ℕ} (h : σ ≤ τ) :
    (simHist A inp bad byz dl d τ).getD σ [] = (simHist A inp bad byz dl d σ).getD σ [] := by
  induction τ with
  | zero => obtain rfl : σ = 0 := by omega
            rfl
  | succ τ ih =>
    rcases Nat.lt_or_ge σ (τ + 1) with h' | h'
    · rw [simHist_getD_succ _ _ _ _ _ _ _ _ (by omega), ih (by omega)]
    · obtain rfl : σ = τ + 1 := by omega
      rfl

theorem simHist_getD_self_succ (τ : ℕ) :
    (simHist A inp bad byz dl d (τ + 1)).getD (τ + 1) [] =
      simNext A bad byz dl d (simHist A inp bad byz dl d τ) τ := by
  simp only [simHist, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by rw [simHist_length])]
  simp [simHist_length]

end

theorem getD_ofFn {α : Type*} (f : Fin n → α) (p : Fin n) (d : α) :
    (List.ofFn f).getD p d = f p := by
  simp [List.getD_eq_getElem?_getD]

/-- **Memoised simulation.** In a run with faulty set `bad`, the states are given by `simHist`. -/
theorem Run.st_eq_simHist [DecidableEq (Fin n)] (A : Algorithm (Fin n) M S VI VO)
    (R : Run (Fin n) M VI) {bad : Fin n → Bool} (hbad : ∀ q, bad q = true ↔ q ∈ R.faulty)
    (d : S) : ∀ τ (p : Fin n),
      R.st A τ p = ((simHist A R.inp bad R.byz R.dl d τ).getD τ []).getD p d := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    intro p
    rcases τ with _ | τ
    · simp [simHist, List.getD_eq_getElem?_getD]
    · have hs : ∀ σ ≤ τ, ∀ q, R.st A σ q =
          ((simHist A R.inp bad R.byz R.dl d τ).getD σ []).getD q d := fun σ hσ q => by
        rw [ih σ (by omega), simHist_getD_le _ _ _ _ _ _ hσ]
      rw [Run.st_succ, simHist_getD_self_succ, simNext, getD_ofFn, hs τ le_rfl]
      congr 1
      funext q
      rw [Run.inbox_eq_flatMap]
      refine List.flatMap_congr fun σ hσ => ?_
      simp only [List.mem_range] at hσ
      simp only [Run.dlv]
      split_ifs with h1 h2
      · rw [Run.out_of_faulty _ _ ((hbad q).1 h2)]
      · rw [Run.out_of_correct _ _ (fun h => h2 ((hbad q).2 h)), hs σ (by omega)]
      · rfl

end TetraBFT
