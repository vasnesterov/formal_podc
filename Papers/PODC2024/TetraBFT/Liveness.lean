import Papers.PODC2024.TetraBFT.Safety

/-!
# The liveness lemmas of TetraBFT (Lemmas 1–4)

The combinatorial core of the liveness argument of Section 4.1, for abstract executions
(`Execution.SafetyHyp`), at a fixed view `v`:

* **Lemma 1** is `IsReport.claims_of_voted` (`Defs.lean`).
* **Lemma 2** (`lemma2`): a leader that holds honest suggest messages of all correct nodes
  determines some value safe by Rule 1.
* **Lemma 3** (`lemma3`): an honest claim in a suggest message is backed by one or two blocking
  sets of correct nodes whose proof messages (in any view `≥ v`) make the corresponding claims.
* **Lemma 4** (`lemma4`): if the leader determined `x` safe by Rule 1 (from *any* set of suggest
  messages whose correct senders are honest), then every correct node holding honest proof messages
  of all correct nodes determines `x` safe by Rule 3.

All reports are for the *same* view `v`, and "honest" means `IsReport` with respect to the votes
the node ever cast (in an implementation, a node's votes in views `< v` are final once it has
entered view `v`, see `Refinement.lean`).
-/

namespace TetraBFT

open Finset Cslib.Quorum

variable {P V : Type*} [Fintype P] [DecidableEq P]

namespace Execution

variable {E : Execution P V} {f : ℕ}

/-- The correct nodes form a quorum. -/
theorem card_correct (hE : E.SafetyHyp f) :
    Fintype.card P - f ≤ (univ.filter (· ∉ E.faulty)).card := by
  have h1 := card_filter_add_card_filter_not (s := (univ : Finset P)) (fun q => q ∉ E.faulty)
  have h2 : (univ.filter fun q : P => ¬ q ∉ E.faulty).card ≤ E.faulty.card :=
    card_le_card fun q hq => by simp only [mem_filter, not_not] at hq; exact hq.2
  have := hE.card_faulty
  rw [card_univ] at h1
  omega

/-- The correct voters of a quorum of vote-k messages form a blocking set of correct nodes. -/
theorem blocking_of_quorum (hn : 3 * f < Fintype.card P) (hE : E.SafetyHyp f) {Q : Finset P}
    (hQ : Fintype.card P - f ≤ Q.card) {w : Vote V} (hv : ∀ q ∈ Q, q ∉ E.faulty → E.voted q w) :
    ∃ B : Finset P, f + 1 ≤ B.card ∧ ∀ q ∈ B, q ∉ E.faulty ∧ E.voted q w :=
  ⟨Q.filter (· ∉ E.faulty), card_correct_quorum hn hE.card_faulty hQ, fun q hq => by
    rw [mem_filter] at hq; exact ⟨hq.2, hv q hq.1 hq.2⟩⟩

/-- **Lemma 2.** A leader holding honest suggest messages (for view `v`) from all correct nodes
determines some value safe by Rule 1. (The quorum used is the set of correct nodes; with Byzantine
members in the quorum the paper's argument would not apply, but Rule 1 only asks for *some*
quorum.) -/
theorem lemma2 (hn : 3 * f < Fintype.card P) (hE : E.SafetyHyp f) (x₀ : V) {v : ℕ}
    {S : Finset P} {rep : P → Report V} (hS : ∀ q ∉ E.faulty, q ∈ S)
    (hrep : ∀ q ∈ S, q ∉ E.faulty → IsReport (E.voted q) v 2 3 (rep q)) :
    ∃ x, Rule1 (Fintype.card P) f S rep x v := by
  set C := univ.filter (· ∉ E.faulty) with hC
  have hCS : C ⊆ S := fun q hq => hS q (by simpa [hC] using hq)
  have hCq := card_correct hE
  have hmemC : ∀ q ∈ C, q ∉ E.faulty := fun q hq => by simpa [hC] using hq
  by_cases hnone : ∀ q ∈ C, (rep q).top = none
  · exact ⟨x₀, Or.inr ⟨C, hCS, hCq, Or.inl hnone⟩⟩
  push Not at hnone
  -- the highest vote-3 view `w` among the correct nodes
  let T := C.filter fun q => (rep q).top ≠ none
  have hT : T.Nonempty := by
    obtain ⟨q, hq, hq'⟩ := hnone
    exact ⟨q, by simp [T, hq, hq']⟩
  let view : P → ℕ := fun q => ((rep q).top.map Prod.fst).getD 0
  obtain ⟨c, hcT, hcmax⟩ := T.exists_max_image view hT
  have hcC : c ∈ C := (mem_filter.1 hcT).1
  have hcF := hmemC c hcC
  obtain ⟨⟨w, x⟩, hctop⟩ := Option.ne_none_iff_exists'.1 (mem_filter.1 hcT).2
  have hcw : view c = w := by simp [view, hctop]
  obtain ⟨hwv, hcv⟩ := (hrep c (hCS hcC) hcF).top_sound w x hctop
  refine ⟨x, Or.inr ⟨C, hCS, hCq, Or.inr ⟨w, hwv, ?_, ?_⟩⟩⟩
  · intro q hq u y hqtop
    have hqF := hmemC q hq
    have hqT : q ∈ T := by simp [T, hq, hqtop]
    have hqw : u ≤ w := by
      have := hcmax q hqT
      simpa [view, hqtop, hcw] using this
    rcases hqw.lt_or_eq with h | rfl
    · exact Or.inl h
    · obtain ⟨-, hqv⟩ := (hrep q (hCS hq) hqF).top_sound u y hqtop
      exact Or.inr ⟨rfl, lemma6 hn hE (k := 3) (by omega) (by omega) hqF hcF hqv hcv⟩
  · -- the vote-2 quorum behind `c`'s vote-3 gives a blocking set claiming `x` safe at `w`
    obtain ⟨Q, hQ, hQv⟩ := hE.quorum_prev c hcF 3 w x (by omega) (by omega) hcv
    obtain ⟨B, hB, hBv⟩ := blocking_of_quorum hn hE hQ hQv
    exact Or.inl ⟨B, fun q hq => hS q (hBv q hq).1, hB, fun q hq =>
      (hrep q (hS q (hBv q hq).1) (hBv q hq).1).claims_of_voted hwv (hBv q hq).2 le_rfl⟩

/-- Every correct node's honest proof report for a view `r ≥ v` claims `x` safe at `w`. -/
def ClaimsFrom (E : Execution P V) (B : Finset P) (v : ℕ) (x : V) (w : ℕ) : Prop :=
  ∀ q ∈ B, q ∉ E.faulty ∧
    ∀ r, v ≤ r → ∀ rep : Report V, IsReport (E.voted q) r 1 4 rep → Claims rep x w

/-- **Lemma 3.** If a correct node claims in its honest suggest message for view `v` that `x` is
safe at `w < v`, then (1) there is a blocking set of correct nodes all of whose proof messages in
views `≥ v` claim `x` safe at `w`, or (2) there are two blocking sets of correct nodes whose proof
messages in views `≥ v` claim two different values safe at views `w₁ < w₂` with
`w ≤ w₁` and `w₂ < v`. -/
theorem lemma3 (hn : 3 * f < Fintype.card P) (hE : E.SafetyHyp f) {k : P} (hk : k ∉ E.faulty)
    {v w : ℕ} {repk : Report V} (hrepk : IsReport (E.voted k) v 2 3 repk) {x : V}
    (hc : Claims repk x w) (hwv : w < v) :
    (∃ B : Finset P, f + 1 ≤ B.card ∧ ClaimsFrom E B v x w) ∨
    (∃ x₁ x₂ w₁ w₂, x₁ ≠ x₂ ∧ w ≤ w₁ ∧ w₁ < w₂ ∧ w₂ < v ∧
      (∃ B : Finset P, f + 1 ≤ B.card ∧ ClaimsFrom E B v x₁ w₁) ∧
      (∃ B : Finset P, f + 1 ≤ B.card ∧ ClaimsFrom E B v x₂ w₂)) := by
  -- a vote-2 for `y` in view `u < v` gives a correct blocking set claiming `y` safe at any `w' ≤ u`
  have hblk : ∀ u y, u < v → E.voted k ⟨2, u, y⟩ → ∀ w', w' ≤ u →
      ∃ B : Finset P, f + 1 ≤ B.card ∧ ClaimsFrom E B v y w' := by
    intro u y huv hku w' hw'
    obtain ⟨Q, hQ, hQv⟩ := hE.quorum_prev k hk 2 u y le_rfl (by omega) hku
    obtain ⟨B, hB, hBv⟩ := blocking_of_quorum hn hE hQ hQv
    exact ⟨B, hB, fun q hq => ⟨(hBv q hq).1, fun r hr rep hrep =>
      hrep.claims_of_voted (by omega) (hBv q hq).2 hw'⟩⟩
  rcases hc with rfl | ⟨u, hu, hwu⟩ | ⟨u, y, hu, hwu⟩
  · -- Rule 2 item 1: every node claims everything safe at view 0
    have hC := card_correct hE
    refine Or.inl ⟨univ.filter (· ∉ E.faulty), by omega, fun q hq => ⟨by simpa using hq,
      fun _ _ _ _ => Or.inl rfl⟩⟩
  · obtain ⟨huv, hku⟩ := hrepk.hi_sound u x hu
    exact Or.inl (hblk u x huv hku w hwu)
  · obtain ⟨huv, hku, u', y', hhi, hyy', huu'⟩ := hrepk.prev_sound u y hu
    obtain ⟨hu'v, hku'⟩ := hrepk.hi_sound u' y' hhi
    have hlt : u < u' := by
      rcases huu'.lt_or_eq with h | rfl
      · exact h
      · exact absurd (hE.one_val k hk 2 u y y' hku hku') hyy'
    exact Or.inr ⟨y, y', u, u', hyy', hwu, hlt, hu'v, hblk u y huv hku u le_rfl,
      hblk u' y' hu'v hku' u' le_rfl⟩

omit [Fintype P] [DecidableEq P] in
/-- A blocking set given by `ClaimsFrom` is a blocking set of senders in the sense of Rule 3. -/
theorem blocking_of_claimsFrom {v : ℕ} {S : Finset P} {rep : P → Report V}
    (hS : ∀ q ∉ E.faulty, q ∈ S)
    (hrep : ∀ q ∈ S, q ∉ E.faulty → IsReport (E.voted q) v 1 4 (rep q)) {x : V} {w : ℕ}
    {B : Finset P} (hB : f + 1 ≤ B.card) (hc : ClaimsFrom E B v x w) : Blocking f S rep x w :=
  ⟨B, fun q hq => hS q (hc q hq).1, hB, fun q hq =>
    (hc q hq).2 v le_rfl (rep q) (hrep q (hS q (hc q hq).1) (hc q hq).1)⟩

/-- **Lemma 4.** If a leader determined `x` safe in view `v` by Rule 1, from suggest messages whose
correct senders are honest, then every correct node holding honest proof messages for view `v` from
all correct nodes determines `x` safe by Rule 3. -/
theorem lemma4 (hn : 3 * f < Fintype.card P) (hE : E.SafetyHyp f) {v : ℕ} {SL : Finset P}
    {repL : P → Report V} {x : V} (hL : Rule1 (Fintype.card P) f SL repL x v)
    (hrepL : ∀ q ∈ SL, q ∉ E.faulty → IsReport (E.voted q) v 2 3 (repL q))
    {S : Finset P} {rep : P → Report V} (hS : ∀ q ∉ E.faulty, q ∈ S)
    (hrep : ∀ q ∈ S, q ∉ E.faulty → IsReport (E.voted q) v 1 4 (rep q)) :
    Rule3 (Fintype.card P) f S rep x v := by
  rcases hL with h0 | ⟨QL, hQLS, hQL, hcase⟩
  · exact Or.inl h0
  set C := univ.filter (· ∉ E.faulty) with hC
  have hmemC : ∀ q ∈ C, q ∉ E.faulty := fun q hq => by simpa [hC] using hq
  have hCS : C ⊆ S := fun q hq => hS q (hmemC q hq)
  have hCq := card_correct hE
  -- a correct vote-4 of a view `u < v` is visible as a vote-3 in the leader's quorum
  have key : ∀ q ∈ C, ∀ u y, (rep q).top = some (u, y) → ∃ c ∈ QL, c ∉ E.faulty ∧
      ∃ u' y', (repL c).top = some (u', y') ∧ u ≤ u' ∧ E.voted c ⟨3, u, y⟩ := by
    intro q hq u y htop
    have hqF := hmemC q hq
    obtain ⟨huv, hqv⟩ := (hrep q (hCS hq) hqF).top_sound u y htop
    obtain ⟨Q3, hQ3, hQ3v⟩ := hE.quorum_prev q hqF 4 u y (by omega) le_rfl hqv
    obtain ⟨c, hc3, hcL, hcF⟩ := exists_mem_inter_notMem_of_three_mul_lt hn hE.card_faulty hQ3 hQL
    have hcv := hQ3v c hc3 hcF
    obtain ⟨u', y', htop', huu'⟩ := (hrepL c (hQLS hcL) hcF).top_max u y huv hcv
    exact ⟨c, hcL, hcF, u', y', htop', huu', hcv⟩
  refine Or.inr ⟨C, hCS, hCq, ?_⟩
  rcases hcase with hnone | ⟨w, hwv, hok, hiii⟩
  · refine Or.inl fun q hq => ?_
    by_contra hne
    obtain ⟨⟨u, y⟩, htop⟩ := Option.ne_none_iff_exists'.1 hne
    obtain ⟨c, hcL, -, u', y', htop', -⟩ := key q hq u y htop
    rw [hnone c hcL] at htop'
    exact absurd htop' (by simp)
  refine Or.inr ⟨w, hwv, ?_, ?_⟩
  · intro q hq u y htop
    obtain ⟨c, hcL, hcF, u', y', htop', huu', hcv⟩ := key q hq u y htop
    rcases Nat.lt_or_ge u w with h | h
    · exact Or.inl h
    · rcases hok c hcL u' y' htop' with h' | ⟨rfl, rfl⟩
      · omega
      · have hu : u = u' := by omega
        subst hu
        obtain ⟨-, hcv'⟩ := (hrepL c (hQLS hcL) hcF).top_sound u y' htop'
        exact Or.inr ⟨rfl, hE.one_val c hcF 3 u y y' hcv hcv'⟩
  · rcases hiii with ⟨B, hBS, hB, hBc⟩ | ⟨h, -⟩
    · obtain ⟨k, hkB, hkF⟩ := exists_mem_notMem_of_card_le_of_lt hE.card_faulty hB
      rcases lemma3 hn hE hkF (hrepL k (hBS hkB) hkF) (hBc k hkB) hwv with
        ⟨B', hB', hc⟩ | ⟨x₁, x₂, w₁, w₂, hx, hw₁, hw₁₂, hw₂, ⟨B₁, hB₁, hc₁⟩, ⟨B₂, hB₂, hc₂⟩⟩
      · exact Or.inl (blocking_of_claimsFrom hS hrep hB' hc)
      · exact Or.inr ⟨rfl, x₁, x₂, w₁, w₂, hx, hw₁, hw₁₂, hw₂,
          blocking_of_claimsFrom hS hrep hB₁ hc₁, blocking_of_claimsFrom hS hrep hB₂ hc₂⟩
    · exact absurd h (by simp)

end Execution

end TetraBFT
