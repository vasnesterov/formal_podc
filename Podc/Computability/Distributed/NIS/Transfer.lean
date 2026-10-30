import Podc.Computability.Distributed.NIS.Simulation

-- CSLib candidate: Cslib/Computability/Distributed/NIS/Transfer.lean (staged by Papers/PODC2021/ExtensionBasedReductions)
/-!
# Transferring a winning prover through a simulation

If each handler run answers a legal source move correctly, keeps its own moves legal and preserves an
invariant, then for every play of the simulating prover against a target protocol, the induced source
play is a correct play against the source protocol; hence it is won by the source prover, all its
moves are legal, and the invariant holds at every window boundary.
-/

namespace Cslib.NIS

variable {P X Y Q O : Type} [DecidableEq P]

/-- Game state after a history. -/
def statesOf [Inhabited X] (h : List (Move P X Q × Resp P X Y O)) : GState P X :=
  h.foldl (fun g e => g.next e.1) GState.start

lemma statesOf_append [Inhabited X] (h w : List (Move P X Q × Resp P X Y O)) :
    statesOf (h ++ w) = w.foldl (fun g e => g.next e.1) (statesOf h) := by
  simp [statesOf, List.foldl_append]

lemma states_eq_statesOf [Inhabited X] (pl : ℕ → Move P X Q × Resp P X Y O) (k : ℕ) :
    states pl k = statesOf (hist pl k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [hist_succ, statesOf_append, ← ih]; rfl

/-- All moves of `w` are legal when played from `gs`. -/
def LegalRun (spec : OracleSpec P X Y Q O) (δ : Protocol P X Y) :
    GState P X → List (Move P X Q × Resp P X Y O) → Prop
  | _, [] => True
  | gs, e :: w => Legal spec δ gs e.1 ∧ LegalRun spec δ (gs.next e.1) w

/-- Every oracle query has a correct answer. -/
def OracleSpec.Total (spec : OracleSpec P X Y Q O) : Prop := ∀ δ C o, ∃ a, spec.valid δ C o a

lemma exAnswer_total (δ : Protocol P X Y) (C : Config P X) (Ps : Finset P)
    (φ : Config P X → Prop) : ∃ a, ExAnswer δ C Ps φ a := by
  by_cases h : ∃ μ, GoodSched δ C Ps φ μ
  · obtain ⟨μ, hμ⟩ := h; exact ⟨some μ, hμ⟩
  · exact ⟨none, h⟩

lemma outputSpec_total : (outputSpec (P := P) (X := X) (Y := Y)).Total :=
  fun δ C o => exAnswer_total δ C o.1 _

lemma assignSpec_total : (assignSpec (P := P) (X := X) (Y := Y)).Total :=
  fun δ C o => exAnswer_total δ C o.1 _

lemma exists_validResp {spec : OracleSpec P X Y Q O} (ht : spec.Total) (δ : Protocol P X Y)
    (m : Move P X Q) : ∃ r, ValidResp spec δ m r := by
  cases m with
  | query C q => exact ⟨_, rfl⟩
  | oracle C o => obtain ⟨a, ha⟩ := ht δ C o; exact ⟨_, a, rfl, ha⟩
  | endPhase C => exact ⟨_, rfl⟩

/-- A correct consistent finite prefix extends to a correct consistent infinite play. -/
lemma exists_extension {spec : OracleSpec P X Y Q O} (htot : spec.Total) (σ : Prover P X Y Q O)
    (δ : Protocol P X Y) (pl : ℕ → Move P X Q × Resp P X Y O) (n : ℕ)
    (hc : ∀ k < n, (pl k).1 = σ (hist pl k)) (hv : ∀ k < n, ValidResp spec δ (pl k).1 (pl k).2) :
    ∃ pl', Consistent σ pl' ∧ ValidPlay spec δ pl' ∧ ∀ k < n, pl' k = pl k := by
  choose rf hrf using exists_validResp htot δ
  let e : List (Move P X Q × Resp P X Y O) → Move P X Q × Resp P X Y O := fun h =>
    if h.length < n then pl h.length else (σ h, rf (σ h))
  let L : ℕ → List (Move P X Q × Resp P X Y O) := fun k => Nat.rec [] (fun _ h => h ++ [e h]) k
  have hL : ∀ k, L (k + 1) = L k ++ [e (L k)] := fun k => rfl
  have hlen : ∀ k, (L k).length = k := fun k => by
    induction k with
    | zero => rfl
    | succ k ih => rw [hL]; simp [ih]
  let pl' : ℕ → Move P X Q × Resp P X Y O := fun k => e (L k)
  have hhist : ∀ k, hist pl' k = L k := fun k => by
    induction k with
    | zero => rfl
    | succ k ih => rw [hist_succ, ih, hL]
  have hagree : ∀ k < n, L k = hist pl k := fun k hk => by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [hL, hist_succ, ih (by omega)]
      simp [e, hlen, show k < n by omega]
  refine ⟨pl', fun k => ?_, fun k => ?_, fun k hk => ?_⟩
  · show (e (L k)).1 = σ (hist pl' k)
    rw [hhist]
    simp only [e, hlen]
    split_ifs with hk
    · rw [hc k hk, hagree k hk]
    · rfl
  · show ValidResp spec δ (e (L k)).1 (e (L k)).2
    simp only [e, hlen]
    split_ifs with hk
    · exact hv k hk
    · exact hrf _
  · show e (L k) = pl k
    simp [e, hlen, hk]

/-- The data of a simulation: a source prover, a handler, and an invariant on (source history,
target history) pairs that every handler run preserves. -/
structure SimData {P₁ X₁ Y₁ Q₁ O₁ P₂ X₂ Y₂ Q₂ O₂ : Type} [DecidableEq P₁] [DecidableEq P₂]
    [Inhabited X₁] [Inhabited X₂]
    (spec₁ : OracleSpec P₁ X₁ Y₁ Q₁ O₁) (spec₂ : OracleSpec P₂ X₂ Y₂ Q₂ O₂)
    (δ₁ : Protocol P₁ X₁ Y₁) (δ₂ : Protocol P₂ X₂ Y₂) where
  σ : Prover P₁ X₁ Y₁ Q₁ O₁
  H : List (Move P₁ X₁ Q₁ × Resp P₁ X₁ Y₁ O₁) → List (Move P₂ X₂ Q₂ × Resp P₂ X₂ Y₂ O₂) →
    Move P₁ X₁ Q₁ → Move P₂ X₂ Q₂ ×
      (List (Move P₂ X₂ Q₂ × Resp P₂ X₂ Y₂ O₂) → Prog (Move P₂ X₂ Q₂) (Resp P₂ X₂ Y₂ O₂) (Resp P₁ X₁ Y₁ O₁))
  I : List (Move P₁ X₁ Q₁ × Resp P₁ X₁ Y₁ O₁) → List (Move P₂ X₂ Q₂ × Resp P₂ X₂ Y₂ O₂) → Prop
  init : I [] []
  step : ∀ hs ht m w r, I hs ht → Legal spec₁ δ₁ (statesOf hs) m →
    ProgRun ht (.ask (H hs ht m).1 (H hs ht m).2) w r →
    (∀ e ∈ w, ValidResp spec₂ δ₂ e.1 e.2) →
    ValidResp spec₁ δ₁ m r ∧ LegalRun spec₂ δ₂ (statesOf ht) w ∧ I (hs ++ [(m, r)]) (ht ++ w)

section Transfer

variable {P₁ X₁ Y₁ Q₁ O₁ P₂ X₂ Y₂ Q₂ O₂ : Type} [DecidableEq P₁] [DecidableEq P₂]
    [Inhabited X₁] [Inhabited X₂]
    {spec₁ : OracleSpec P₁ X₁ Y₁ Q₁ O₁} {spec₂ : OracleSpec P₂ X₂ Y₂ Q₂ O₂}
    {δ₁ : Protocol P₁ X₁ Y₁} {δ₂ : Protocol P₂ X₂ Y₂}

lemma legal_of_legalRun {gs : GState P₂ X₂} {w : List (Move P₂ X₂ Q₂ × Resp P₂ X₂ Y₂ O₂)}
    (hw : LegalRun spec₂ δ₂ gs w) (i : ℕ) (hi : i < w.length) :
    Legal spec₂ δ₂ ((w.take i).foldl (fun g e => g.next e.1) gs) (w[i]).1 := by
  induction w generalizing gs i with
  | nil => simp at hi
  | cons e w ih =>
    cases i with
    | zero => exact hw.1
    | succ i => simpa using ih hw.2 i (by simpa using hi)

/-- **Transfer theorem.** Under a simulation whose source prover wins against `δ₁`, every correct play
of the simulating prover against `δ₂` has legal moves only, and induces a won play of the source
prover, with the invariant at all window boundaries. -/
theorem SimData.transfer (D : SimData spec₁ spec₂ δ₁ δ₂) (htot : spec₁.Total) (T₁ : Task P₁ X₁ Y₁)
    (hwin : ProverWins spec₁ D.σ T₁ δ₁)
    (pl : ℕ → Move P₂ X₂ Q₂ × Resp P₂ X₂ Y₂ O₂) (hc : Consistent (simulate D.σ D.H) pl)
    (hv : ValidPlay spec₂ δ₂ pl) :
    ∃ (ps : ℕ → Move P₁ X₁ Q₁ × Resp P₁ X₁ Y₁ O₁) (a : ℕ → ℕ), a 0 = 0 ∧ (∀ j, a j < a (j + 1)) ∧
      Wins spec₁ T₁ δ₁ ps ∧ (∀ k, Legal spec₂ δ₂ (states pl k) (pl k).1) ∧
      (∀ j, D.I (hist ps j) (hist pl (a j))) ∧
      (∀ j, ProgRun (hist pl (a j))
        (.ask (D.H (hist ps j) (hist pl (a j)) (ps j).1).1 (D.H (hist ps j) (hist pl (a j)) (ps j).1).2)
        (window pl (a j) (a (j + 1))) (ps j).2) := by
  obtain ⟨ps, a, ha0, hamono, hpc, hrun⟩ := simulate_spec D.σ D.H pl hc
  have hamono' : StrictMono a := strictMono_nat_of_lt_succ hamono
  have hwv : ∀ j, ∀ e ∈ window pl (a j) (a (j + 1)), ValidResp spec₂ δ₂ e.1 e.2 := by
    intro j e he
    simp only [window, List.mem_map, List.mem_range'] at he
    obtain ⟨i, -, rfl⟩ := he
    exact hv i
  have hhist : ∀ j, hist pl (a (j + 1)) = hist pl (a j) ++ window pl (a j) (a (j + 1)) :=
    fun j => hist_add_window pl (hamono j).le
  -- by induction: legality, validity and invariant
  have main : ∀ j, (∀ i < j, Legal spec₁ δ₁ (statesOf (hist ps i)) (ps i).1 ∧
      ValidResp spec₁ δ₁ (ps i).1 (ps i).2 ∧ LegalRun spec₂ δ₂ (statesOf (hist pl (a i)))
        (window pl (a i) (a (i + 1)))) ∧ D.I (hist ps j) (hist pl (a j)) := by
    intro j
    induction j with
    | zero => exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), by rw [ha0]; exact D.init⟩
    | succ j ih =>
      obtain ⟨hprev, hI⟩ := ih
      -- legality of the j-th source move, from a correct extension of the prefix
      have hleg : Legal spec₁ δ₁ (statesOf (hist ps j)) (ps j).1 := by
        obtain ⟨pl', hc', hv', hag⟩ := exists_extension htot D.σ δ₁ ps j
          (fun k _ => hpc k) (fun k hk => (hprev k hk).2.1)
        have hh : hist pl' j = hist ps j := by
          simp only [hist]; exact List.map_congr_left (fun k hk => hag k (by simpa using hk))
        have := (hwin pl' hc' hv').1 j
        rwa [states_eq_statesOf, hh, hc' j, hh, ← hpc j] at this
      obtain ⟨h1, h2, h3⟩ := D.step _ _ _ _ _ hI hleg (hrun j) (hwv j)
      refine ⟨fun i hi => ?_, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact hprev i hi
        · exact ⟨hleg, h1, h2⟩
      · rw [hist_succ, hhist]; exact h3
  have hvalid : ValidPlay spec₁ δ₁ ps := fun j => ((main (j + 1)).1 j (Nat.lt_succ_self j)).2.1
  refine ⟨ps, a, ha0, hamono, hwin ps hpc hvalid, fun k => ?_, fun j => (main j).2, hrun⟩
  -- target legality: locate `k` in its window
  have hex : ∃ j, k < a (j + 1) := ⟨k, by
    have := hamono'.le_apply (x := k + 1); omega⟩
  let j := Nat.find hex
  have hj : k < a (j + 1) := Nat.find_spec hex
  have hj' : a j ≤ k := by
    cases hjj : j with
    | zero => rw [ha0]; omega
    | succ j' =>
      have := Nat.find_min hex (show j' < j by omega)
      exact Nat.le_of_not_lt this
  have hlr := ((main (j + 1)).1 j (Nat.lt_succ_self j)).2.2
  have hi : k - a j < (window pl (a j) (a (j + 1))).length := by simp [window]; omega
  have := legal_of_legalRun hlr (k - a j) hi
  have hw : (window pl (a j) (a (j + 1)))[k - a j] = pl k := by
    simp [window]; congr 1; omega
  have hst : (List.take (k - a j) (window pl (a j) (a (j + 1)))).foldl (fun g e => g.next e.1)
      (statesOf (hist pl (a j))) = states pl k := by
    rw [states_eq_statesOf, ← statesOf_append]
    congr 1
    rw [hist_add_window pl hj']
    · have hsplit : List.range' (a j) (a (j + 1) - a j) =
          List.range' (a j) (k - a j) ++ List.range' (a j + 1 * (k - a j)) (a (j + 1) - k) := by
        rw [List.range'_append]; congr 1; omega
      simp only [window, ← List.map_take]
      rw [hsplit, List.take_left' (by simp)]
  rw [hw, hst] at this
  exact this

end Transfer

end Cslib.NIS
