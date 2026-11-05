import Papers.PODC2020.WhyExtensionBased.Chain
import Papers.PODC2020.WhyExtensionBased.Phase2
import Podc.Computability.Distributed.NIS.Transfer

/-!
# Theorem 5.7: no extension-based proof of the impossibility of `k`-set agreement

Alistarh, Aspnes, Ellen, Gelashvili, Zhu, *Why extension-based proofs fail*, Theorem 5.7: for
`k ≥ 2` there is no extension-based proof (in the NIS model) that `k`-set agreement is not
wait-free solvable.

The adversary plays against an arbitrary prover `σ`:
* in phase 1 it maintains an `AState` and answers queries with `qstep`, output queries with `oq`;
* when the prover ends phase 1 (or makes an illegal move) it fixes a complete protocol
  (`dstar`, resp. its current partial protocol) and answers all further moves correctly for it.
The protocol against which the play is valid is the fixed one, or, if phase 1 never ends, the limit
of the partial protocols (`limTerm`). The prover does not win (`not_wins`): no reached configuration
violates `k`-set agreement, there are only finitely many phases, and no infinite chain of queries
(Lemma 5.6 in phase 1, a depth bound afterwards).
-/

namespace Podc.WhyExtensionBased

open Cslib.NIS Cslib.NIS.Subdiv St
open scoped Classical

variable {P X : Type} [DecidableEq P]

/-- Moves and responses of extension-based proofs. -/
abbrev OMv (P X : Type) := Move P X (Finset P × X)
abbrev ORs (P X : Type) := Resp P X X (Option (List P))

/-- Mode of the adversary: phase 1 with a state, or a fixed protocol. -/
inductive Mode (P X : Type) where
  | p1 (A : AState P X)
  | fixed (δ : Protocol P X X)

/-- Some correct response for a fixed protocol. -/
noncomputable def anyResp (δ : Protocol P X X) (m : OMv P X) : ORs P X :=
  Classical.choose (exists_validResp (outputSpec_total (P := P) (X := X) (Y := X)) δ m)

lemma anyResp_spec (δ : Protocol P X X) (m : OMv P X) :
    ValidResp outputSpec δ m (anyResp δ m) :=
  Classical.choose_spec (exists_validResp (outputSpec_total (P := P) (X := X) (Y := X)) δ m)

/-- The protocol fixed when the prover ends phase 1 in `C`. -/
noncomputable def endProt (A : AState P X) (C : Config P X) : Protocol P X X :=
  if h : ∃ x : P → X, ∃ p : P, ∃ rest : List P, C = exec (initC x) (p :: rest) then
    dstar A ((Classical.choose h) (Classical.choose (Classical.choose_spec h)))
  else A.term

/-- One move of the adversary. -/
noncomputable def advStep (M : Mode P X) (gs : GState P X) (m : OMv P X) : Mode P X × ORs P X :=
  match M with
  | .fixed δ => (.fixed δ, anyResp δ m)
  | .p1 A =>
    if Legal outputSpec A.term gs m then
      match m with
      | .query C q => (.p1 (qstep A C q), .config (step C q) (outs (qstep A C q).term (step C q)))
      | .oracle C o => (.p1 (oq A C o.1 o.2).1, .answer (oq A C o.1 o.2).2)
      | .endPhase C => (.fixed (endProt A C), .ack)
    else (.fixed A.term, anyResp A.term m)

/-- The initial adversary state: nothing terminated, one subdivision. -/
def A0 : AState P X := ⟨fun _ => none, 1, []⟩

lemma ainv_A0 : AInv (A0 : AState P X) := by
  have hT : ∀ r (a : X), Tset (A0 : AState P X).term r a = ∅ := by
    intro r a; ext s; simp [Tset, A0, decided]; intro _ _; cases s <;> simp [decided]
  refine ⟨le_rfl, fun s hs => by cases s <;> simp_all [decided, A0], fun a => ?_, fun a b _ => ?_,
    fun r hr => by simp [A0] at hr⟩
  · rw [hT]; exact far_empty_left fun z hz => hz
  · rw [hT]; exact far_empty_left fun z hz => hz

variable [Inhabited X]

/-- The run of the adversary against the prover `σ`. -/
noncomputable def run (σ : Prover P X X (Finset P × X) (Option (List P))) :
    ℕ → Mode P X × List (OMv P X × ORs P X)
  | 0 => (.p1 A0, [])
  | n + 1 =>
    let x := run σ n
    let m := σ x.2
    let r := advStep x.1 (statesOf x.2) m
    (r.1, x.2 ++ [(m, r.2)])

/-- The play against `σ`. -/
noncomputable def play (σ : Prover P X X (Finset P × X) (Option (List P))) (n : ℕ) :
    OMv P X × ORs P X :=
  (σ (run σ n).2, (advStep (run σ n).1 (statesOf (run σ n).2) (σ (run σ n).2)).2)

variable (σ : Prover P X X (Finset P × X) (Option (List P)))

lemma run_hist (n : ℕ) : (run σ n).2 = hist (play σ) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [hist_succ, ← ih]; rfl

lemma play_consistent : Consistent σ (play σ) := fun n => by
  show σ (run σ n).2 = _; rw [run_hist]

lemma states_play (n : ℕ) : states (play σ) n = statesOf (run σ n).2 := by
  rw [states_eq_statesOf, run_hist]

/-- The mode at time `n`. -/
noncomputable def mode (n : ℕ) : Mode P X := (run σ n).1

lemma mode_succ (n : ℕ) :
    mode σ (n + 1) = (advStep (mode σ n) (states (play σ) n) (play σ n).1).1 := by
  rw [states_play]; rfl

lemma resp_eq (n : ℕ) :
    (play σ n).2 = (advStep (mode σ n) (states (play σ) n) (play σ n).1).2 := by
  rw [states_play]; rfl

lemma mode_zero : mode σ 0 = .p1 A0 := rfl

lemma mode_fixed_succ {n : ℕ} {δ : Protocol P X X} (h : mode σ n = .fixed δ) :
    mode σ (n + 1) = .fixed δ := by
  rw [mode_succ, h]; rfl

lemma mode_fixed_le {n m : ℕ} {δ : Protocol P X X} (h : mode σ n = .fixed δ) (hnm : n ≤ m) :
    mode σ m = .fixed δ := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact mode_fixed_succ σ ih

/-- What happens after a phase-1 mode. -/
lemma mode_p1_succ {n : ℕ} {A : AState P X} (h : mode σ n = .p1 A) :
    (Legal outputSpec A.term (states (play σ) n) (play σ n).1 ∧
      ((∃ C q, (play σ n).1 = .query C q ∧ mode σ (n + 1) = .p1 (qstep A C q) ∧
          (play σ n).2 = .config (step C q) (outs (qstep A C q).term (step C q))) ∨
       (∃ C Q y, (play σ n).1 = .oracle C (Q, y) ∧ mode σ (n + 1) = .p1 (oq A C Q y).1 ∧
          (play σ n).2 = .answer (oq A C Q y).2) ∨
       (∃ C, (play σ n).1 = .endPhase C ∧ mode σ (n + 1) = .fixed (endProt A C) ∧
          (play σ n).2 = .ack))) ∨
    (¬ Legal outputSpec A.term (states (play σ) n) (play σ n).1 ∧
      mode σ (n + 1) = .fixed A.term ∧ (play σ n).2 = anyResp A.term (play σ n).1) := by
  rw [mode_succ, resp_eq, h]
  by_cases hl : Legal outputSpec A.term (states (play σ) n) (play σ n).1
  · left
    refine ⟨hl, ?_⟩
    simp only [advStep, if_pos hl]
    rcases hm : (play σ n).1 with ⟨C, q⟩ | ⟨C, ⟨Q, y⟩⟩ | ⟨C⟩
    · exact Or.inl ⟨C, q, rfl, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨C, Q, y, rfl, rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨C, rfl, rfl, rfl⟩)
  · right
    refine ⟨hl, ?_⟩
    simp only [advStep, if_neg hl]
    exact ⟨trivial, trivial⟩


lemma mode_p1_prev {n : ℕ} {A' : AState P X} (h : mode σ (n + 1) = .p1 A') :
    ∃ A, mode σ n = .p1 A ∧ Legal outputSpec A.term (states (play σ) n) (play σ n).1 ∧
      ((∃ C q, (play σ n).1 = .query C q ∧ A' = qstep A C q ∧
          (play σ n).2 = .config (step C q) (outs (qstep A C q).term (step C q))) ∨
       (∃ C Q y, (play σ n).1 = .oracle C (Q, y) ∧ A' = (oq A C Q y).1 ∧
          (play σ n).2 = .answer (oq A C Q y).2)) := by
  rcases hn : mode σ n with A | δ
  · rcases mode_p1_succ σ hn with ⟨hl, ⟨C, q, hm, hA, hr⟩ | ⟨C, Q, y, hm, hA, hr⟩ | ⟨C, hm, hA, -⟩⟩ |
      ⟨-, hA, -⟩
    · rw [h] at hA; cases hA; exact ⟨A, rfl, hl, Or.inl ⟨C, q, hm, rfl, hr⟩⟩
    · rw [h] at hA; cases hA; exact ⟨A, rfl, hl, Or.inr ⟨C, Q, y, hm, rfl, hr⟩⟩
    · rw [h] at hA; cases hA
    · rw [h] at hA; cases hA
  · have := mode_fixed_succ σ hn; rw [h] at this; cases this

lemma states_succ (n : ℕ) :
    states (play σ) (n + 1) = (states (play σ) n).next (play σ n).1 := rfl

/-- Configurations reached in phase 1 are good. -/
lemma rc_of_reached {A : AState P X} (hA : AInv A) {gs : GState P X}
    (hbase : gs.base = initC default) (hresp : ∀ C ∈ gs.resp, RC A.term A.t C) {C : Config P X}
    (hC : gs.Reached C) : RC A.term A.t C := by
  rcases hC with ⟨u, rfl⟩ | hC
  · rw [hbase, reinit_initC]
    exact ⟨reach_initC u, fun j => Or.inl (by simp [initC, rounds]; exact hA.one_le)⟩
  · exact hresp C hC

variable [Fintype P]

/-- **Phase-1 invariant.** -/
lemma p1_inv (n : ℕ) : ∀ A, mode σ n = .p1 A → AInv A ∧
    (states (play σ) n).base = initC default ∧
    ∀ C ∈ (states (play σ) n).resp, RC A.term A.t C := by
  induction n with
  | zero =>
    intro A hA; rw [mode_zero] at hA; cases hA
    exact ⟨ainv_A0, rfl, fun C hC => by simp [states, GState.start] at hC⟩
  | succ n ih =>
    intro A' hA'
    obtain ⟨A, hA, hl, hcase⟩ := mode_p1_prev σ hA'
    obtain ⟨hinv, hbase, hresp⟩ := ih A hA
    rcases hcase with ⟨C, q, hm, rfl, -⟩ | ⟨C, Q, y, hm, rfl, -⟩
    · rw [hm] at hl
      obtain ⟨hR, hq⟩ := hl
      obtain ⟨h1, -, h3, h4⟩ := qstep_spec hinv (rc_of_reached hinv hbase hresp hR) hq
      refine ⟨h1, by rw [states_succ, hm]; exact hbase, fun C' hC' => ?_⟩
      rw [states_succ, hm] at hC'
      simp only [GState.next, Set.mem_insert_iff] at hC'
      rcases hC' with rfl | hC'
      · exact h3
      · exact h4 C' (hresp C' hC')
    · rw [hm] at hl
      obtain ⟨h1, -, h3, -⟩ := oq_spec hinv (rc_of_reached hinv hbase hresp hl.1) Q y
      refine ⟨h1, by rw [states_succ, hm]; exact hbase, fun C' hC' => ?_⟩
      rw [states_succ, hm] at hC'
      exact h3 C' (hresp C' hC')


lemma p1_step_le {n : ℕ} {A A' : AState P X} (hA : mode σ n = .p1 A)
    (hA' : mode σ (n + 1) = .p1 A') : Le A A' := by
  obtain ⟨A0', hA0, hl, hcase⟩ := mode_p1_prev σ hA'
  rw [hA] at hA0; cases hA0
  obtain ⟨hinv, hbase, hresp⟩ := p1_inv σ n A hA
  rcases hcase with ⟨C, q, hm, rfl, -⟩ | ⟨C, Q, y, hm, rfl, -⟩
  · rw [hm] at hl
    exact (qstep_spec hinv (rc_of_reached hinv hbase hresp hl.1) hl.2).2.1
  · rw [hm] at hl
    exact (oq_spec hinv (rc_of_reached hinv hbase hresp hl.1) Q y).2.1

lemma p1_le {n m : ℕ} {A B : AState P X} (hA : mode σ n = .p1 A) (hB : mode σ m = .p1 B)
    (hnm : n ≤ m) : Le A B := by
  induction m, hnm using Nat.le_induction generalizing B with
  | base => rw [hA] at hB; cases hB; exact Le.refl _
  | succ m hnm ih =>
    obtain ⟨B0, hB0, -⟩ := mode_p1_prev σ hB
    exact (ih hB0).trans (p1_step_le σ hB0 hB)

/-- The limit of the partial protocols of phase 1. -/
noncomputable def limTerm : Protocol P X X := fun s =>
  if h : ∃ n A, mode σ n = .p1 A ∧ A.term s ≠ none then
    (Classical.choose (Classical.choose_spec h)).term s
  else none

/-- The protocol against which the play is valid. -/
noncomputable def dfin : Protocol P X X :=
  if h : ∃ n δ, mode σ n = .fixed δ then Classical.choose (Classical.choose_spec h)
  else limTerm σ

lemma dfin_of_fixed {n : ℕ} {δ : Protocol P X X} (h : mode σ n = .fixed δ) : dfin σ = δ := by
  have hex : ∃ n δ, mode σ n = .fixed δ := ⟨n, δ, h⟩
  unfold dfin; rw [dif_pos hex]
  have h1 := Classical.choose_spec (Classical.choose_spec hex)
  have h2 := mode_fixed_le σ h1 (le_max_left _ n)
  have h3 := mode_fixed_le σ h (le_max_right (Classical.choose hex) n)
  rw [h2] at h3; cases h3; rfl

lemma dfin_of_never (h : ¬ ∃ n δ, mode σ n = .fixed δ) : dfin σ = limTerm σ := by
  unfold dfin; rw [dif_neg h]

lemma exists_p1_of_never (h : ¬ ∃ n δ, mode σ n = .fixed δ) (n : ℕ) : ∃ A, mode σ n = .p1 A := by
  rcases hm : mode σ n with A | δ
  · exact ⟨A, rfl⟩
  · exact absurd ⟨n, δ, hm⟩ h

lemma agree_lim (hnever : ¬ ∃ n δ, mode σ n = .fixed δ) {n : ℕ} {A : AState P X}
    (hA : mode σ n = .p1 A) : Agree A (limTerm σ) := by
  intro s hs
  cases s with
  | init => rfl
  | upd => rfl
  | scan s0 v =>
    show limTerm σ (scan s0 v) = A.term (scan s0 v)
    unfold limTerm
    split_ifs with h
    · have hspec := Classical.choose_spec (Classical.choose_spec h)
      set m := Classical.choose h
      set B := Classical.choose (Classical.choose_spec h)
      rcases le_total n m with hnm | hmn
      · exact (p1_le σ hA hspec.1 hnm).2.2 _ hs
      · exact ((p1_le σ hspec.1 hA hmn).2.2 _
          (Or.inr (show decided B.term (scan s0 v) ≠ none from hspec.2))).symm
    · by_contra hne
      exact h ⟨n, A, hA, fun h' => hne h'.symm⟩

/-- The fixed protocol at the end of phase 1 and the last phase-1 state. -/
lemma fixed_origin {m : ℕ} {δ : Protocol P X X} (hm : mode σ m = .fixed δ) :
    ∃ K B, mode σ K = .p1 B ∧ mode σ (K + 1) = .fixed δ ∧ (∀ n, n ≤ K → ∃ A, mode σ n = .p1 A) ∧
      ((δ = B.term ∧ ¬ Legal outputSpec B.term (states (play σ) K) (play σ K).1) ∨
        ∃ C, (play σ K).1 = .endPhase C ∧
        Legal outputSpec B.term (states (play σ) K) (play σ K).1 ∧ δ = endProt B C) := by
  have hex : ∃ m, ∃ δ, mode σ m = .fixed δ := ⟨m, δ, hm⟩
  obtain ⟨δ1, hδ1⟩ := Nat.find_spec hex
  have hmin : ∀ n < Nat.find hex, ¬ ∃ δ, mode σ n = .fixed δ := fun n hn => Nat.find_min hex hn
  generalize Nat.find hex = K1 at hδ1 hmin
  have hK1pos : K1 ≠ 0 := by intro h0; rw [h0, mode_zero] at hδ1; cases hδ1
  have hbefore : ∀ n, n < K1 → ∃ A, mode σ n = .p1 A := by
    intro n hn
    rcases hmn : mode σ n with A | δ'
    · exact ⟨A, rfl⟩
    · exact absurd ⟨δ', hmn⟩ (hmin n hn)
  obtain ⟨B, hB⟩ := hbefore (K1 - 1) (by omega)
  have hK : K1 - 1 + 1 = K1 := by omega
  have hδ : δ1 = δ := by
    have h2 := mode_fixed_le σ hδ1 (le_max_left K1 m)
    have h3 := mode_fixed_le σ hm (le_max_right K1 m)
    rw [h2] at h3; cases h3; rfl
  subst hδ
  refine ⟨K1 - 1, B, hB, by rw [hK]; exact hδ1, fun n hn => hbefore n (by omega), ?_⟩
  rcases mode_p1_succ σ hB with ⟨hl, ⟨C, q, -, h1, -⟩ | ⟨C, Q, y, -, h1, -⟩ | ⟨C, hmv, h1, -⟩⟩ |
    ⟨hnl, h1, -⟩
  · rw [hK, hδ1] at h1; cases h1
  · rw [hK, hδ1] at h1; cases h1
  · rw [hK, hδ1] at h1; cases h1; exact Or.inr ⟨C, hmv, hl, rfl⟩
  · rw [hK, hδ1] at h1; cases h1; exact Or.inl ⟨rfl, hnl⟩

lemma agree_endProt {B : AState P X} (hB : AInv B) (C : Config P X) : Agree B (endProt B C) := by
  unfold endProt; split_ifs
  · exact dstar_agree hB
  · exact fun _ _ => rfl

lemma agree_dfin {n : ℕ} {A : AState P X} (hA : mode σ n = .p1 A) : Agree A (dfin σ) := by
  by_cases hfix : ∃ n δ, mode σ n = .fixed δ
  · obtain ⟨m, δ, hm⟩ := hfix
    rw [dfin_of_fixed σ hm]
    obtain ⟨K, B, hB, hK1, hbef, hcase⟩ := fixed_origin σ hm
    have hnK : n ≤ K := by
      by_contra hlt; push_neg at hlt
      have := mode_fixed_le σ hK1 (show K + 1 ≤ n by omega); rw [hA] at this; cases this
    refine Agree.of_le (p1_le σ hA hB hnK) ?_
    rcases hcase with ⟨rfl, -⟩ | ⟨C, -, -, rfl⟩
    · exact fun _ _ => rfl
    · exact agree_endProt (p1_inv σ K B hB).1 C
  · rw [dfin_of_never σ hfix]; exact agree_lim σ hfix hA


/-- Answers `none` of phase 1 are correct for the final protocol. -/
lemma none_ok {n : ℕ} {A : AState P X} (hA : mode σ n = .p1 A) {rec : Config P X × Finset P × X}
    (hrec : rec ∈ A.recs) {μ : List P} (hμQ : ∀ p ∈ μ, p ∈ rec.2.1)
    (hμ : IsSched (dfin σ) rec.1 μ) : ∀ p ∈ rec.2.1, outs (dfin σ) (exec rec.1 μ) p ≠ some rec.2.2 := by
  intro p hp hout
  -- clause 1 of `RecOK` for a phase-1 state `B` after `A`
  have hclause : ∀ m B, mode σ m = .p1 B → n ≤ m → IsSched B.term rec.1 μ →
      decided B.term (exec rec.1 μ p) = some rec.2.2 → False := by
    intro m B hB hnm hsch hdec
    have hle := p1_le σ hA hB hnm
    exact ((p1_inv σ m B hB).1.recs rec (hle.2.1 hrec)).2 _ ⟨μ, hμQ, hsch, p, hp, rfl⟩ |>.1 hdec
  by_cases hfix : ∃ n δ, mode σ n = .fixed δ
  · obtain ⟨m, δ, hm⟩ := hfix
    rw [dfin_of_fixed σ hm] at hμ hout
    obtain ⟨K, B, hB, hK1, -, hcase⟩ := fixed_origin σ hm
    have hnK : n ≤ K := by
      by_contra hlt; push_neg at hlt
      have := mode_fixed_le σ hK1 (show K + 1 ≤ n by omega); rw [hA] at this; cases this
    have hBinv := (p1_inv σ K B hB).1
    have hrecB := (p1_le σ hA hB hnK).2.1 hrec
    have hterm : δ = B.term ∨ ∃ a, δ = dstar B a := by
      rcases hcase with ⟨rfl, -⟩ | ⟨C, -, -, rfl⟩
      · exact Or.inl rfl
      · unfold endProt; split_ifs
        · exact Or.inr ⟨_, rfl⟩
        · exact Or.inl rfl
    rcases hterm with rfl | ⟨a, rfl⟩
    · exact hclause K B hB hnK hμ hout
    · exact dstar_none hBinv hrecB hμQ hμ p hp hout
  · rw [dfin_of_never σ hfix] at hμ hout
    -- the output was decided at some time `m`
    have hx : (exec rec.1 μ p).Settled := by
      cases hxe : exec rec.1 μ p <;> simp_all [outs, decided]
    obtain ⟨m, B, hB, hBd⟩ : ∃ m B, mode σ m = .p1 B ∧
        decided B.term (exec rec.1 μ p) = some rec.2.2 := by
      have hlim : decided (limTerm σ) (exec rec.1 μ p) = some rec.2.2 := hout
      cases hxe : exec rec.1 μ p with
      | init => rw [hxe] at hlim; simp [decided] at hlim
      | upd => rw [hxe] at hx; exact absurd hx id
      | scan s0 v =>
        rw [hxe] at hlim
        simp only [decided, limTerm] at hlim
        split_ifs at hlim with h
        · exact ⟨_, _, (Classical.choose_spec (Classical.choose_spec h)).1, hlim⟩
    obtain ⟨B', hB'⟩ := exists_p1_of_never σ hfix (max n m)
    have hag := agree_lim σ hfix hB'
    refine hclause _ B' hB' (le_max_left _ _) (hμ.mono fun s hs => ?_) ?_
    · by_contra hne; rw [hag s (Or.inr hne)] at hs; exact hne hs
    · rw [(p1_le σ hB hB' (le_max_right _ _)).2.2 _ (Or.inr (by rw [hBd]; simp)), hBd]

/-- **The play is valid** for the final protocol. -/
lemma valid_play : ValidPlay outputSpec (dfin σ) (play σ) := by
  intro n
  rcases hmode : mode σ n with A | δ
  · rcases mode_p1_succ σ hmode with ⟨hl, ⟨C, q, hm, hA', hr⟩ | ⟨C, Q, y, hm, hA', hr⟩ |
      ⟨C, hm, hA', hr⟩⟩ | ⟨-, hA', hr⟩
    · rw [hm, hr]
      show _ = Resp.config (step C q) (outs (dfin σ) (step C q))
      obtain ⟨hinv, hbase, hresp⟩ := p1_inv σ n A hmode
      rw [hm] at hl
      obtain ⟨-, -, hRC, -⟩ := qstep_spec hinv (rc_of_reached hinv hbase hresp hl.1) hl.2
      have hag := agree_dfin σ hA'
      congr 1; funext j
      exact (hag _ (by rcases hRC.2 j with h | ⟨-, h⟩
                       · exact Or.inl h
                       · exact Or.inr h)).symm
    · rw [hm, hr]
      obtain ⟨hinv, hbase, hresp⟩ := p1_inv σ n A hmode
      rw [hm] at hl
      obtain ⟨-, -, -, hsome, hnone⟩ := oq_spec hinv (rc_of_reached hinv hbase hresp hl.1) Q y
      have hag := agree_dfin σ hA'
      refine ⟨_, rfl, ?_⟩
      rcases ha : (oq A C Q y).2 with _ | μ
      · intro ⟨μ, hμQ, hμ, p, hp, hout⟩
        exact none_ok σ hA' (rec := (C, Q, y)) (hnone ha) hμQ hμ p hp hout
      · obtain ⟨hμQ, hgood⟩ := hsome μ ha
        obtain ⟨hsch, p, hp, hout⟩ := hgood _ hag
        exact ⟨hμQ, hsch, p, hp, hout⟩
    · rw [hm, hr]; rfl
    · rw [hr, dfin_of_fixed σ hA']; exact anyResp_spec _ _
  · rw [resp_eq, hmode, dfin_of_fixed σ hmode]; exact anyResp_spec _ _


/-! ## The prover does not win -/

lemma legal_transfer {n : ℕ} {A : AState P X} (hA : mode σ n = .p1 A) {m : OMv P X}
    (hl : Legal outputSpec (dfin σ) (states (play σ) n) m) :
    Legal outputSpec A.term (states (play σ) n) m := by
  cases m with
  | query C q =>
    obtain ⟨hR, hq⟩ := hl
    obtain ⟨hinv, hbase, hresp⟩ := p1_inv σ n A hA
    have hRC := rc_of_reached hinv hbase hresp hR
    refine ⟨hR, ?_⟩
    have hfx : Fixd A (C q) := by
      rcases hRC.2 q with h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    show decided A.term (C q) = none
    rw [← agree_dfin σ hA _ hfx]; exact hq
  | oracle C o => exact hl
  | endPhase C => exact hl

/-- In phase 1, reached configurations do not violate `k`-set agreement. -/
lemma not_violates_p1 [Finite X] {k : ℕ} (hk : 1 ≤ k) {n : ℕ} {A : AState P X}
    (hA : mode σ n = .p1 A) {C : Config P X} (hC : (states (play σ) n).Reached C) :
    ¬ Violates (setAgreement X k) (dfin σ) C := by
  obtain ⟨hinv, hbase, hresp⟩ := p1_inv σ n A hA
  have hRC := rc_of_reached hinv hbase hresp hC
  have hag := agree_dfin σ hA
  have hout : ∀ q, outs (dfin σ) C q = outs A.term C q := fun q => by
    by_cases hd : decided A.term (C q) = none
    · rcases hRC.2 q with h | ⟨-, h⟩
      · exact hag _ (Or.inl h)
      · exact absurd hd h
    · exact hag _ (Or.inr hd)
  have hT : ∀ q z, outs A.term C q = some z → C q ∈ Tset A.term A.t z := by
    intro q z hz
    have hs : (C q).Settled := by cases hcq : C q <;> simp_all [outs, decided]
    refine ⟨⟨hs, ?_⟩, ⟨C, hRC.1, by rw [hRC.1.pid]⟩, hz⟩
    rcases hRC.2 q with h | ⟨h, -⟩
    · exact Or.inr ⟨h, by rw [show decided A.term (C q) = outs A.term C q from rfl, hz]; simp⟩
    · exact Or.inl h
  refine not_violates hk {z | ∃ q, outs A.term C q = some z} ?_ ?_ ?_
  · refine le_trans ?_ hk
    refine (Set.ncard_le_one_iff_subsingleton).2 ?_
    rintro z1 ⟨q1, h1⟩ z2 ⟨q2, h2⟩
    by_contra hne
    by_cases hq : q1 = q2
    · subst hq; rw [h1] at h2; exact hne (Option.some_injective _ h2)
    · have hT1 := hT q1 z1 h1
      have hT2 := hT q2 z2 h2
      exact far_not_adj (hinv.far5 z1 z2 hne) (by norm_num) hT1 hT2
        (hRC.1.adj hq hT1.1 hT2.1)
  · rintro z ⟨q, hq⟩
    have hT1 := hT q z hq
    refine Rch.seen_input hRC.1.rch (i := q) ?_
    by_contra hns
    exact far_not_mem (hinv.far4 z) (by norm_num) hT1 ⟨hT1.1, hT1.2.1, hns⟩
  · intro q z hz; rw [hout] at hz; exact ⟨q, hz⟩

/-- If the adversary never leaves phase 1 and the prover only plays legal moves, the prover never
ends a phase. -/
lemma no_end_of_never (hnever : ¬ ∃ n δ, mode σ n = .fixed δ)
    (hl : ∀ k, Legal outputSpec (dfin σ) (states (play σ) k) (play σ k).1) (k : ℕ) :
    ¬ IsEnd (play σ k).1 := by
  rintro ⟨C, hC⟩
  obtain ⟨A, hA⟩ := exists_p1_of_never σ hnever k
  rcases mode_p1_succ σ hA with ⟨-, ⟨C', q, hm, -⟩ | ⟨C', Q, y, hm, -⟩ | ⟨C', -, h1, -⟩⟩ |
      ⟨hnl, -⟩
  · rw [hC] at hm; cases hm
  · rw [hC] at hm; cases hm
  · exact hnever ⟨_, _, h1⟩
  · exact hnl (legal_transfer σ hA (hl k))

/-- If the adversary never leaves phase 1, there is no infinite chain of queries (Lemma 5.6). -/
lemma no_chain_of_never (hnever : ¬ ∃ n δ, mode σ n = .fixed δ)
    (hl : ∀ k, Legal outputSpec (dfin σ) (states (play σ) k) (play σ k).1) (K0 : ℕ)
    (hch : ∀ k ≥ K0, ChainLink (play σ k).1 (play σ (k + 1)).1) : False := by
  have hq : ∀ i, ∃ C q, (play σ (K0 + i)).1 = .query C q := by
    intro i; obtain ⟨C, q, q', h1, -⟩ := hch (K0 + i) (by omega); exact ⟨C, q, h1⟩
  let Cs : ℕ → Config P X := fun i => Classical.choose (hq i)
  let qs : ℕ → P := fun i => Classical.choose (Classical.choose_spec (hq i))
  have hCq : ∀ i, (play σ (K0 + i)).1 = .query (Cs i) (qs i) := fun i =>
    Classical.choose_spec (Classical.choose_spec (hq i))
  let As : ℕ → AState P X := fun i => Classical.choose (exists_p1_of_never σ hnever (K0 + i))
  have hAs : ∀ i, mode σ (K0 + i) = .p1 (As i) := fun i =>
    Classical.choose_spec (exists_p1_of_never σ hnever (K0 + i))
  have hlegal : ∀ i, Legal outputSpec (As i).term (states (play σ) (K0 + i)) (play σ (K0 + i)).1 :=
    fun i => legal_transfer σ (hAs i) (hl _)
  refine IsChain.false (A := As) (C := Cs) (q := qs) ⟨fun i => (p1_inv σ _ _ (hAs i)).1, fun i => ?_,
    fun i => ?_, fun i => ?_, fun i => ?_⟩
  · obtain ⟨hinv, hbase, hresp⟩ := p1_inv σ _ _ (hAs i)
    have := hlegal i; rw [hCq i] at this
    exact rc_of_reached hinv hbase hresp this.1
  · have := hlegal i; rw [hCq i] at this; exact this.2
  · rcases mode_p1_succ σ (hAs i) with ⟨-, ⟨C, q, hm, h1, -⟩ | ⟨C, Q, y, hm, -⟩ |
        ⟨C, hm, -⟩⟩ | ⟨hnl, -⟩
    · rw [hCq i] at hm; cases hm
      have h2 := hAs (i + 1); rw [show K0 + (i + 1) = K0 + i + 1 by omega, h1] at h2
      exact (Mode.p1.inj h2).symm
    · rw [hCq i] at hm; cases hm
    · rw [hCq i] at hm; cases hm
    · exact absurd (hlegal i) hnl
  · obtain ⟨C, q, q', h1, h2⟩ := hch (K0 + i) (by omega)
    rw [hCq i] at h1; cases h1
    have h3 := hCq (i + 1)
    rw [show K0 + (i + 1) = K0 + i + 1 by omega, h2] at h3
    exact (Move.query.inj h3).1.symm


/-! ### After phase 1 -/

/-- Configurations of phase 2 and later: reached by a `δ`-schedule starting with `p₀` from an initial
configuration in which `p₀` has input `a`. -/
def R2 (δ : Protocol P X X) (p₀ : P) (a : X) (C : Config P X) : Prop :=
  ∃ x γ, x p₀ = a ∧ IsSched δ (initC x) (p₀ :: γ) ∧ C = exec (initC x) (p₀ :: γ)

lemma isSched_initC_congr {δ : Protocol P X X} {x x' : P → X} {α α' : List P}
    (h : exec (initC x) α = exec (initC x') α') :
    IsSched δ (initC x) α ↔ IsSched δ (initC x') α' := by
  rw [isSched_iff, isSched_iff, h]; simp [initC, St.depth]

lemma R2.reinit {δ : Protocol P X X} {p₀ : P} {a : X} {C : Config P X} (h : R2 δ p₀ a C)
    (u : P → X) : R2 δ p₀ a (reinit C u) := by
  obtain ⟨x, γ, hxa, hsch, rfl⟩ := h
  set u' : P → X := fun j => if j ∈ p₀ :: γ then x j else u j with hu'
  have key := exec_reinit (δ := δ) (initC x) u' (α := p₀ :: γ) (fun j hj _ => by
    simp only [initC, hu']; rw [if_pos hj])
  rw [reinit_initC] at key
  refine ⟨u', γ, by simp [hu', hxa], key.2.2 hsch, ?_⟩
  rw [key.1]
  funext j
  by_cases hj : j ∈ p₀ :: γ
  · have hni := not_isInit_exec_of_mem (initC x) hj
    simp only [Cslib.NIS.reinit, if_neg hni]
  · simp only [Cslib.NIS.reinit, exec_apply_of_not_mem _ hj, hu', if_neg hj]

lemma R2.step {δ : Protocol P X X} {p₀ : P} {a : X} {C : Config P X} (h : R2 δ p₀ a C) {q : P}
    (hq : Active δ C q) : R2 δ p₀ a (step C q) := by
  obtain ⟨x, γ, hxa, hsch, rfl⟩ := h
  refine ⟨x, γ ++ [q], hxa, ?_, ?_⟩
  · rw [← List.cons_append, isSched_concat]; exact ⟨hsch, hq⟩
  · rw [← List.cons_append, exec_append]; rfl

/-- The situation after the prover ended phase 1 legally. -/
structure AfterP1 (σ : Prover P X X (Finset P × X) (Option (List P))) (K : ℕ) (B : AState P X)
    (p₀ : P) (a : X) : Prop where
  modeK : mode σ K = .p1 B
  fixed : ∀ m, K + 1 ≤ m → mode σ m = .fixed (dstar B a)
  before : ∀ n, n ≤ K → ∃ A, mode σ n = .p1 A
  dfin_eq : dfin σ = dstar B a
  inv : AInv B
  base : R2 (dfin σ) p₀ a (states (play σ) (K + 1)).base
  resp : (states (play σ) (K + 1)).resp = ∅

lemma exists_afterP1 (hl : ∀ k, Legal outputSpec (dfin σ) (states (play σ) k) (play σ k).1)
    (hfix : ∃ n δ, mode σ n = .fixed δ) : ∃ K B p₀ a, AfterP1 σ K B p₀ a := by
  obtain ⟨m, δ, hm⟩ := hfix
  obtain ⟨K, B, hB, hK1, hbef, hcase⟩ := fixed_origin σ hm
  have hdfin := dfin_of_fixed σ hm
  rcases hcase with ⟨rfl, hnl⟩ | ⟨C₂, hmv, hlB, rfl⟩
  · exact absurd (legal_transfer σ hB (hl K)) hnl
  have hl2 := hl K; rw [hmv] at hl2
  have hginv := ginv_states (spec := outputSpec) (δ := dfin σ) hl K
  obtain ⟨u, α, hα, hsch, hC₂⟩ := hginv.2 C₂ hl2
  have hbase := (p1_inv σ K B hB).2.1
  rw [hbase, reinit_initC] at hsch hC₂
  have hdec : ∃ x : P → X, ∃ p : P, ∃ rest : List P, C₂ = exec (initC x) (p :: rest) := by
    obtain ⟨p, rest, rfl⟩ := List.exists_cons_of_ne_nil hα; exact ⟨u, p, rest, hC₂⟩
  set x0 := Classical.choose hdec
  set p0 := Classical.choose (Classical.choose_spec hdec)
  obtain ⟨rest0, hrest0⟩ := Classical.choose_spec (Classical.choose_spec hdec)
  have hend : endProt B C₂ = dstar B (x0 p0) := by unfold endProt; rw [dif_pos hdec]
  rw [hend] at hK1 hm hdfin
  refine ⟨K, B, p0, x0 p0, hB, fun m' hm' => mode_fixed_le σ hK1 hm', fun n hn => hbef n hn,
    hdfin, (p1_inv σ K B hB).1, ?_, ?_⟩
  · rw [states_succ, hmv]
    refine ⟨x0, rest0, rfl, ?_, hrest0⟩
    rw [← isSched_initC_congr (hC₂.symm.trans hrest0)]; exact hsch
  · rw [states_succ, hmv]; rfl

lemma AfterP1.r2 {K : ℕ} {B : AState P X} {p₀ : P} {a : X} (hA : AfterP1 σ K B p₀ a)
    (hl : ∀ k, Legal outputSpec (dfin σ) (states (play σ) k) (play σ k).1) {k : ℕ}
    (hk : K + 1 ≤ k) : R2 (dfin σ) p₀ a (states (play σ) k).base ∧
      ∀ C ∈ (states (play σ) k).resp, R2 (dfin σ) p₀ a C := by
  induction k, hk using Nat.le_induction with
  | base => exact ⟨hA.base, fun C hC => by rw [hA.resp] at hC; simp at hC⟩
  | succ k hk ih =>
    obtain ⟨hb, hr⟩ := ih
    have hreached : ∀ C, (states (play σ) k).Reached C → R2 (dfin σ) p₀ a C := by
      rintro C (⟨u, rfl⟩ | hC)
      · exact hb.reinit u
      · exact hr C hC
    have hlk := hl k
    rw [states_succ]
    rcases hmk : (play σ k).1 with ⟨C, q⟩ | ⟨C, o⟩ | ⟨C⟩
    · rw [hmk] at hlk
      refine ⟨hb, fun C' hC' => ?_⟩
      simp only [GState.next, Set.mem_insert_iff] at hC'
      rcases hC' with rfl | hC'
      · exact (hreached C hlk.1).step hlk.2
      · exact hr C' hC'
    · exact ⟨hb, hr⟩
    · rw [hmk] at hlk
      exact ⟨hr C hlk, fun C' hC' => by simp [GState.next] at hC'⟩

lemma AfterP1.reached {K : ℕ} {B : AState P X} {p₀ : P} {a : X} (hA : AfterP1 σ K B p₀ a)
    (hl : ∀ k, Legal outputSpec (dfin σ) (states (play σ) k) (play σ k).1) {k : ℕ}
    (hk : K + 1 ≤ k) {C : Config P X} (hC : (states (play σ) k).Reached C) :
    R2 (dfin σ) p₀ a C := by
  obtain ⟨hb, hr⟩ := hA.r2 σ hl hk
  rcases hC with ⟨u, rfl⟩ | hC
  · exact hb.reinit u
  · exact hr C hC

lemma AfterP1.depth {K : ℕ} {B : AState P X} {p₀ : P} {a : X} (hA : AfterP1 σ K B p₀ a)
    {C : Config P X} (hC : R2 (dfin σ) p₀ a C) :
    totalDepth C ≤ Fintype.card P * (2 * (B.t + 1)) := by
  obtain ⟨x, γ, hxa, hsch, rfl⟩ := hC
  rw [hA.dfin_eq, ← hxa] at hsch
  unfold totalDepth
  calc ∑ j, (exec (initC x) (p₀ :: γ) j).depth ≤ ∑ _j : P, 2 * (B.t + 1) :=
        Finset.sum_le_sum fun j _ => depth_le hA.inv hsch j
    _ = _ := by simp


/-- The depth of the phase base never decreases, and strictly increases at the end of a phase. -/
lemma base_depth_succ (hl : ∀ k, Legal outputSpec (dfin σ) (states (play σ) k) (play σ k).1)
    (j : ℕ) : totalDepth (states (play σ) j).base ≤ totalDepth (states (play σ) (j + 1)).base ∧
      (IsEnd (play σ j).1 →
        totalDepth (states (play σ) j).base < totalDepth (states (play σ) (j + 1)).base) := by
  have hg := ginv_states (spec := outputSpec) (δ := dfin σ) hl j
  have hlj := hl j
  rw [states_succ]
  rcases hmj : (play σ j).1 with ⟨C, q⟩ | ⟨C, o⟩ | ⟨C⟩
  · exact ⟨le_rfl, fun ⟨_, h⟩ => by cases h⟩
  · exact ⟨le_rfl, fun ⟨_, h⟩ => by cases h⟩
  · rw [hmj] at hlj
    have := measure_lt_of_mem_resp hg hlj
    exact ⟨this.le, fun _ => this⟩

lemma base_depth_mono (hl : ∀ k, Legal outputSpec (dfin σ) (states (play σ) k) (play σ k).1)
    {j j' : ℕ} (h : j ≤ j') :
    totalDepth (states (play σ) j).base ≤ totalDepth (states (play σ) j').base := by
  induction j', h using Nat.le_induction with
  | base => exact le_rfl
  | succ j' _ ih => exact ih.trans (base_depth_succ σ hl j').1

/-- **The prover does not win.** -/
theorem not_wins [Finite X] {k : ℕ} (hk : 2 ≤ k) :
    ¬ Wins outputSpec (setAgreement X k) (dfin σ) (play σ) := by
  rintro ⟨hl, hW⟩
  by_cases hfix : ∃ n δ, mode σ n = .fixed δ
  · obtain ⟨K, B, p₀, a, hA⟩ := exists_afterP1 σ hl hfix
    set Bd := Fintype.card P * (2 * (B.t + 1)) with hBd
    rcases hW with ⟨n, C, hC, hv⟩ | hends | ⟨K0, hch⟩
    · by_cases hn : n ≤ K
      · obtain ⟨A, hAn⟩ := hA.before n hn
        exact not_violates_p1 σ (by omega) hAn hC hv
      · obtain ⟨x, γ, hxa, hsch, rfl⟩ := hA.reached σ hl (by omega) hC
        rw [hA.dfin_eq, ← hxa] at hsch hv
        exact not_violates_dstar hk hA.inv hsch hv
    · have hgrow : ∀ i, ∃ j, K + 1 ≤ j ∧ i ≤ totalDepth (states (play σ) j).base := by
        intro i
        induction i with
        | zero => exact ⟨K + 1, le_rfl, Nat.zero_le _⟩
        | succ i ih =>
          obtain ⟨j, hj, hij⟩ := ih
          obtain ⟨j', hj', hend⟩ := hends j
          refine ⟨j' + 1, by omega, ?_⟩
          have h1 := base_depth_mono σ hl hj'
          have h2 := (base_depth_succ σ hl j').2 hend
          omega
      obtain ⟨j, hj, hij⟩ := hgrow (Bd + 1)
      have := hA.depth σ (hA.r2 σ hl hj).1
      omega
    · set M := max (K + 1) K0
      have hgrow : ∀ i, ∃ C q, (play σ (M + i)).1 = .query C q ∧ i ≤ totalDepth C := by
        intro i
        induction i with
        | zero =>
          obtain ⟨C, q, q', h1, -⟩ := hch M (le_max_right _ _)
          exact ⟨C, q, h1, Nat.zero_le _⟩
        | succ i ih =>
          obtain ⟨C, q, hm, hi⟩ := ih
          obtain ⟨C', q1, q', h1, h2⟩ := hch (M + i) (by omega)
          rw [hm] at h1
          obtain ⟨rfl, rfl⟩ := Move.query.inj h1
          refine ⟨step C q, q', h2, ?_⟩
          rw [measure_step]; omega
      obtain ⟨C, q, hm, hi⟩ := hgrow (Bd + 1)
      have hlm := hl (M + (Bd + 1))
      rw [hm] at hlm
      have := hA.depth σ (hA.reached σ hl (by omega) hlm.1)
      omega
  · rcases hW with ⟨n, C, hC, hv⟩ | hends | ⟨K0, hch⟩
    · obtain ⟨A, hAn⟩ := exists_p1_of_never σ hfix n
      exact not_violates_p1 σ (by omega) hAn hC hv
    · obtain ⟨j, -, hj⟩ := hends 0
      exact no_end_of_never σ hfix hl j hj
    · exact no_chain_of_never σ hfix hl K0 hch

/-- **Theorem 5.7** (general form): for `k ≥ 2`, any finite set of processes and any finite input
set, there is no extension-based proof of the impossibility of `k`-set agreement in the NIS model.
-/
theorem not_hasEBProof_setAgreement [Finite X] {k : ℕ} (hk : 2 ≤ k) :
    ¬ HasEBProof (P := P) (setAgreement X k) := by
  rintro ⟨σ, hσ⟩
  exact not_wins σ hk (hσ (dfin σ) (play σ) (play_consistent σ) (valid_play σ))

/-- **Theorem 5.7** of Alistarh, Aspnes, Ellen, Gelashvili, Zhu, *Why extension-based proofs fail*:
no extension-based proof can show the impossibility of deterministically solving `k`-set agreement
(inputs `{0, …, k}`) in a wait-free manner in the NIS model, for `n > k ≥ 2` processes. -/
theorem theorem_5_7 {n k : ℕ} (hk : 2 ≤ k) (_hnk : k < n) :
    ¬ HasEBProof (P := Fin n) (setAgreement (Fin (k + 1)) k) :=
  not_hasEBProof_setAgreement hk

end Podc.WhyExtensionBased
