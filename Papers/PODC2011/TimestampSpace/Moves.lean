import Papers.PODC2011.TimestampSpace.Lemma41
import Papers.PODC2011.TimestampSpace.LongLivedBasic
import Papers.PODC2011.TimestampSpace.Stair

/-!
# Runs of moves and coverage counts

Infrastructure for the proof of Theorem 1.2: a list of *moves* `ms` (process, labels — every
label of a move belongs to its process) is run from a configuration `C`; `cfgAt C ms t` is the
configuration after the first `t` moves. A process that has not moved yet has its state in `C`;
a move changes only the state of its own process (`cfgAt_step_other`); a process that moved at
time `s` keeps its state afterwards (`cfgAt_frozen`, distinct movers).

Coverage counts are CSLib-style `sig I C r` (number of processes covering `r`, from
`LongLivedBasic.lean`); `sum_sig` turns a sum of counts into the number of processes covering
some object of a set (each process covers at most one object).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp

open Cslib.SharedMemory Impl

variable {P : Type} [DecidableEq P] {T : Type} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec}
  {L : Type} {I : Impl (tsObj T) B P L}

variable (I) in
/-- The configuration after the first `t` moves (`C` if the run is undefined). -/
noncomputable def cfgAt (C : Config (tsObj T) B P L) (ms : List (P × List (Label P (tsObj T))))
    (t : ℕ) : Config (tsObj T) B P L :=
  (I.runFrom C (flat (ms.take t))).getD C

/-- Moves whose labels all belong to the moving process. -/
def Owned (ms : List (P × List (Label P (tsObj T)))) : Prop := ∀ m ∈ ms, ∀ ℓ ∈ m.2, ℓ.proc = m.1

lemma flat_take_drop (ms : List (P × List (Label P (tsObj T)))) (t : ℕ) :
    flat ms = flat (ms.take t) ++ flat (ms.drop t) := by
  rw [← List.flatMap_append, List.take_append_drop]

lemma flat_take_succ (ms : List (P × List (Label P (tsObj T)))) {t : ℕ} (ht : t < ms.length) :
    flat (ms.take (t + 1)) = flat (ms.take t) ++ (ms[t]).2 := by
  rw [List.take_succ_eq_append_getElem ht]; unfold flat
  rw [List.flatMap_append, List.flatMap_singleton]

lemma runFrom_take {C X : Config (tsObj T) B P L} {ms : List (P × List (Label P (tsObj T)))}
    (h : I.runFrom C (flat ms) = some X) (t : ℕ) :
    I.runFrom C (flat (ms.take t)) = some (cfgAt I C ms t) := by
  rw [flat_take_drop ms t] at h
  obtain ⟨C₁, h1, -⟩ := I.runFrom_eq_some_of_append h
  simp [cfgAt, h1]

lemma cfgAt_zero (C : Config (tsObj T) B P L) (ms : List (P × List (Label P (tsObj T)))) :
    cfgAt I C ms 0 = C := by simp [cfgAt]

lemma cfgAt_succ {C X : Config (tsObj T) B P L} {ms : List (P × List (Label P (tsObj T)))}
    (h : I.runFrom C (flat ms) = some X) {t : ℕ} (ht : t < ms.length) :
    I.runFrom (cfgAt I C ms t) (ms[t]).2 = some (cfgAt I C ms (t + 1)) := by
  have h1 := runFrom_take h (t + 1)
  rw [flat_take_succ ms ht, runFrom_append_of_eq I (runFrom_take h t)] at h1
  exact h1

lemma flat_procs_take {ms : List (P × List (Label P (tsObj T)))} (hown : Owned ms) (t : ℕ) :
    ∀ ℓ ∈ flat (ms.take t), ℓ.proc ∈ (ms.take t).map Prod.fst :=
  flat_procs (fun m hm => hown m (List.mem_of_mem_take hm))

lemma cfgAt_other {C X : Config (tsObj T) B P L} {ms : List (P × List (Label P (tsObj T)))}
    (hown : Owned ms) (h : I.runFrom C (flat ms) = some X) {t : ℕ} {q : P}
    (hq : q ∉ (ms.take t).map Prod.fst) :
    (cfgAt I C ms t).loc q = C.loc q ∧ (cfgAt I C ms t).pend q = C.pend q :=
  I.runFrom_other (runFrom_take h t) (fun ℓ hℓ he => hq (he ▸ flat_procs_take hown t ℓ hℓ))

lemma cfgAt_step_other {C X : Config (tsObj T) B P L} {ms : List (P × List (Label P (tsObj T)))}
    (hown : Owned ms) (h : I.runFrom C (flat ms) = some X) {t : ℕ} (ht : t < ms.length) {q : P}
    (hq : q ≠ (ms[t]).1) :
    (cfgAt I C ms (t + 1)).loc q = (cfgAt I C ms t).loc q ∧
      (cfgAt I C ms (t + 1)).pend q = (cfgAt I C ms t).pend q :=
  I.runFrom_other (cfgAt_succ h ht)
    (fun ℓ hℓ he => hq (he.symm.trans (hown _ (List.getElem_mem ht) ℓ hℓ)))

lemma cfgAt_frozen {C X : Config (tsObj T) B P L} {ms : List (P × List (Label P (tsObj T)))}
    (hown : Owned ms) (hnd : (ms.map Prod.fst).Nodup) (h : I.runFrom C (flat ms) = some X)
    {s : ℕ} (hs : s < ms.length) :
    ∀ t, s < t → t ≤ ms.length →
      (cfgAt I C ms t).loc (ms[s]).1 = (cfgAt I C ms (s + 1)).loc (ms[s]).1 ∧
      (cfgAt I C ms t).pend (ms[s]).1 = (cfgAt I C ms (s + 1)).pend (ms[s]).1 := by
  intro t hst ht
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_or_ge s t with h1 | h1
    · have hne : (ms[s]).1 ≠ (ms[t]).1 := by
        intro he
        have := (List.Nodup.getElem_inj_iff hnd (i := s) (j := t) (hi := by simpa using hs)
          (hj := by simpa using ht)).1 (by simpa using he)
        omega
      have := cfgAt_step_other hown h (by omega) hne
      rw [this.1, this.2]; exact ih h1 (by omega)
    · have : t = s := by omega
      subst this; exact ⟨rfl, rfl⟩

lemma mem_take_map_fst {ms : List (P × List (Label P (tsObj T)))} {t : ℕ} {q : P}
    (h : q ∈ (ms.take t).map Prod.fst) : ∃ s < t, ∃ hs : s < ms.length, (ms[s]).1 = q := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
  obtain ⟨s, hs, he⟩ := List.getElem_of_mem hm
  simp only [List.length_take, lt_min_iff] at hs
  refine ⟨s, hs.1, hs.2, ?_⟩
  rw [← he, List.getElem_take]

/-! ### Coverage counts -/

section Counts

variable [Fintype P]

open Classical in
lemma sig_le_of_agree_except {X Y : Config (tsObj T) B P L} (p : P)
    (h : ∀ q, q ≠ p → X.loc q = Y.loc q ∧ X.pend q = Y.pend q) (r : ι) :
    sig I X r ≤ sig I Y r + (if I.Covers X p r then 1 else 0) := by
  classical
  rw [sig_eq_card, sig_eq_card]
  have hsub : Finset.univ.filter (fun q => I.Covers X q r) ⊆
      insert p (Finset.univ.filter (fun q => I.Covers Y q r)) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hq ⊢
    by_cases hqp : q = p
    · exact Or.inl hqp
    · exact Or.inr (covers_congr (h q hqp).1 (h q hqp).2 hq)
  split_ifs with hc
  · exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  · have hsub' : Finset.univ.filter (fun q => I.Covers X q r) ⊆
        Finset.univ.filter (fun q => I.Covers Y q r) := by
      intro q hq
      have := hsub hq
      rcases Finset.mem_insert.1 this with rfl | h'
      · simp at hq; exact absurd hq hc
      · exact h'
    simpa using Finset.card_le_card hsub'

lemma sig_le_of_subset {X Y : Config (tsObj T) B P L} {r : ι}
    (h : ∀ q, I.Covers Y q r → I.Covers X q r) : sig I Y r ≤ sig I X r := by
  classical
  rw [sig_eq_card, sig_eq_card]
  exact Finset.card_le_card (fun q hq => by simp at hq ⊢; exact h q hq)

/-- The sum of the coverage counts over a set of objects is the number of processes covering an
object of the set. -/
lemma sum_sig (C : Config (tsObj T) B P L) (S : Finset ι) [DecidablePred (fun p => ∃ r ∈ S, I.Covers C p r)] :
    ∑ r ∈ S, sig I C r = (Finset.univ.filter (fun p => ∃ r ∈ S, I.Covers C p r)).card := by
  classical
  simp_rw [sig_eq_card]
  rw [← Finset.card_biUnion]
  · congr 1; ext p; simp
  · intro r _ r' _ hrr'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    exact hrr' (covers_unique hp hp')

end Counts

end Cslib.SharedMemory.Timestamp
