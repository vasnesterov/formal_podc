import Papers.PODC2011.SimultaneousAllCaseOptimal.Consensus

/-!
# Lemma 5 is false for `t = n − 1`

The paper allows `t ≤ n − 1` (§2.1, and again at the start of §4). For `t = n − 1` Lemma 5 fails
already at time `1`, for every `n ≥ 2` and every complete set of input vectors: take the protocol in
which everybody sends a message in round 1, the failure-free run `r₀`, and the run `r⋆` in which all
processes but `p₀` crash in round 1 without sending anything. Round 1 is premature in both runs
(`W < t` always), but at time `1` the only process alive in `r⋆` is `p₀`, which sees that it
received nothing; every run that `p₀` cannot distinguish from `r⋆` at time 1 is again of this
form. So the connected component of `r⋆` at time 1 does not contain `r₀`.
-/

namespace Podc.SimultaneousAllCaseOptimal

open Cslib.SyncCrash Cslib.Byzantine.LockStep

variable {P I O : Type} [Fintype P]

/-- Everybody sends a (trivial) message in every round; nobody decides. -/
def pingProtocol (P I O : Type) : Protocol P I Unit O := ⟨fun _ _ _ _ => some (), fun _ _ _ => none⟩

/-- The run in which all processes but `p₀` crash silently in round 1. -/
def loneRun [DecidableEq P] (p₀ : P) (ι : P → I) : Run P I :=
  ⟨ι, fun q => if q = p₀ then none else some 1, fun _ => ∅⟩

/-- The invariant of the connected component of `loneRun`: `p₀` survives round 1 and receives no
round-1 message. -/
def LoneInv (p₀ : P) (r : Run P I) : Prop := r.Alive p₀ 1 ∧ ∀ q, q ≠ p₀ → ¬ r.Deliv q p₀ 0

lemma LoneInv.not_alive {p₀ : P} {r : Run P I} {t : ℕ} (hr : r.Admissible t) (h : LoneInv p₀ r)
    {q : P} (hq : q ≠ p₀) : ¬ r.Alive q 1 := by
  intro ha
  apply h.2 q hq
  refine ⟨hr.alive_zero q, fun hc => ?_⟩
  have := ha 1 hc.1
  omega

lemma LoneInv.step {T : Task P I O} {t : ℕ} {p₀ : P} {r₁ r₂ : Run P I} (hr₁ : T.IsRun t r₁)
    (h : LoneInv p₀ r₁) (hs : Similar (pingProtocol P I O) 1 r₁ r₂) : LoneInv p₀ r₂ := by
  classical
  obtain ⟨p, hp₁, hp₂, -, hh⟩ := hs
  have hp : p = p₀ := by
    by_contra hne
    exact h.not_alive hr₁.1 hne hp₁
  subst hp
  refine ⟨hp₂, fun q hq hd => ?_⟩
  have e1 := rcv_hist (alg := pingProtocol P I O) r₁ p q (show 0 < 1 by omega)
  have e2 := rcv_hist (alg := pingProtocol P I O) r₂ p q (show 0 < 1 by omega)
  rw [hh, e2] at e1
  rw [msg_eq_deliv, msg_eq_deliv, if_pos ⟨hq, hd⟩, if_neg (fun h' => h.2 q hq h'.2)] at e1
  simp [pingProtocol] at e1

/-- **Lemma 5 is false for `t = n − 1`** (any `n ≥ 2`, any complete set of input vectors, any
nonempty input set): there are two runs in which round `1` is premature that are not connected at
time `1` in the similarity graph of `pingProtocol`. -/
theorem lemma5_false [DecidableEq P] (hn : 2 ≤ Fintype.card P) {T : Task P I O}
    (hT : T.inputs = Set.univ) (ι : P → I) (p₀ : P) :
    let t := Fintype.card P - 1
    T.IsRun t (ffRun ι) ∧ T.IsRun t (loneRun p₀ ι) ∧ Premature (ffRun ι) t 1 ∧
      Premature (loneRun p₀ ι) t 1 ∧ ¬ Connected (pingProtocol P I O) T t 1 (loneRun p₀ ι) (ffRun ι) := by
  intro t
  have hι : ι ∈ T.inputs := by rw [hT]; trivial
  have h1 : T.IsRun t (ffRun ι) := ffRun_isRun t hι
  have h2 : T.IsRun t (loneRun p₀ ι) := by
    refine ⟨⟨?_, fun p c hc => ?_⟩, hι⟩
    · have : (loneRun p₀ ι).faulty ⊆ Finset.univ.erase p₀ := by
        intro q hq
        simp only [Run.mem_faulty, Run.Faulty, loneRun, ne_eq] at hq
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        rintro rfl; simp at hq
      refine (Finset.card_le_card this).trans ?_
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    · simp only [loneRun] at hc; split_ifs at hc <;> simp_all
  have ht : 1 ≤ t := by omega
  refine ⟨h1, h2, premature_one h1.1 ht, premature_one h2.1 ht, fun hc => ?_⟩
  have hinv : LoneInv p₀ (loneRun p₀ ι) := by
    refine ⟨fun c hc => by simp [loneRun] at hc, fun q hq hd => ?_⟩
    exact hd.2 ⟨by simp [loneRun, hq], by simp [loneRun]⟩
  have key : ∀ r', Connected (pingProtocol P I O) T t 1 (loneRun p₀ ι) r' → LoneInv p₀ r' := by
    intro r' h
    induction h with
    | refl => exact hinv
    | tail _ hstep ih => exact ih.step hstep.1 hstep.2.2
  obtain ⟨-, h3⟩ := key _ hc
  obtain ⟨q, hq⟩ : ∃ q, q ≠ p₀ := by
    by_contra hno
    push Not at hno
    have : Fintype.card P ≤ 1 := Fintype.card_le_one_iff.2 fun a b => (hno a).trans (hno b).symm
    omega
  exact h3 q hq (Run.deliv_of_not_faulty (ffRun_not_faulty q) _ _)

/-- The hypothesis `Lemma5Hyp` (Lemma 5 for all protocols) fails for `t = n − 1`. -/
theorem not_lemma5Hyp [DecidableEq P] [Nonempty I] (hn : 2 ≤ Fintype.card P) {T : Task P I O}
    (hT : T.inputs = Set.univ) : ¬ Lemma5Hyp T (Fintype.card P - 1) := by
  intro h
  have p₀ : P := Classical.choice (Fintype.card_pos_iff.1 (by omega))
  let ι : P → I := fun _ => Classical.arbitrary I
  obtain ⟨h1, h2, h3, h4, h5⟩ := lemma5_false (O := O) hn hT ι p₀
  exact h5 (h _ _ 1 _ _ h2 h1 h4 h3)

end Podc.SimultaneousAllCaseOptimal
