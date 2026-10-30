import Papers.PODC2022.InternetComputerConsensus.PresBeacon
import Papers.PODC2022.InternetComputerConsensus.PresFinish
import Papers.PODC2022.InternetComputerConsensus.PresPropose
import Papers.PODC2022.InternetComputerConsensus.PresEcho
import Papers.PODC2022.InternetComputerConsensus.PresFinal

/-!
# Safety of ICC0 (Lemma "Safety", Property P2) and consistency of the outputs

* `inv_of_reachable`: the global invariant holds in every reachable state.
* `safety`: Lemma (Safety) of the paper — at each round, if some block is finalized, then no other
  block of that round can be notarized. We state it for any two honest parties' pools, and at the
  level of signatures (`safety_cert`).
* `output_prefix`: the atomic-broadcast safety argument of Section 3.3 — the outputs of any two
  honest parties are prefixes of one another.

No synchrony assumption is used: the adversary schedules all deliveries and the clock arbitrarily.
-/

namespace Podc.InternetComputerConsensus

open Finset Cslib.Byzantine

set_option linter.unusedSectionVars false

variable {P V : Type*} [Fintype P] [DecidableEq P] {π : Params P} {F : Finset P}

/-- Every step preserves the invariant. -/
theorem Inv.step (hinj : ∀ k, Function.Injective (π.rank k)) (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {s s' : GState P V} (hI : Inv π F s)
    (h : Step π F s s') : Inv π F s' := by
  cases h with
  | deliver p m hp hm => exact hI.deliver hp hm
  | tick => exact hI.tick
  | act p l M hp hl =>
    cases hl with
    | beacon h1 h2 => exact hI.beacon hp h1
    | finish B h1 h2 h3 h4 => exact hI.finish hp B h1 h2 h3 h4
    | propose Bp pl h1 h2 h3 h4 h5 => exact hI.propose hp Bp pl h1 h2 h4 h5
    | echoShare B h1 h2 h3 h4 h5 h6 h7 h8 => exact hI.echoShare hinj hp B h1 h2 h3 h4 h6 h8
    | echoDisq B h1 h2 h3 h4 h5 h6 h7 h8 => exact hI.echoDisq hinj hp B h1 h2 h3 h4 h6 h8
    | final B h1 h2 h3 => exact hI.final hF hn hp B h1 h2 h3

/-- The invariant holds in every reachable state. -/
theorem inv_of_reachable (hinj : ∀ k, Function.Injective (π.rank k)) (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {s : GState P V} (hs : Reachable π F s) : Inv π F s := by
  induction hs with
  | refl => exact inv_init
  | tail _ h ih => exact ih.step hinj hF hn h

/-- **Lemma (Safety)**, signature level: if a finalization of `B` and a notarization of `B'` can
both exist (each has `n - t` signers, corrupt parties signing anything), and `B`, `B'` are blocks
of the same round, then `B' = B`. -/
theorem safety_cert (hinj : ∀ k, Function.Injective (π.rank k)) (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {s : GState P V} (hs : Reachable π F s)
    {B B' : Block P V} (hB : FinalCert π F s.sent B) (hB' : NotarCert π F s.sent B')
    (hr : B'.round = B.round) : B' = B :=
  (inv_of_reachable hinj hF hn hs).final_notar_eq hF hn hB hB' hr

/-- **Lemma (Safety)** of [ICC, Section 4] (Property P2). Assume at most `t < n/3` corrupt
parties (and idealized signatures and hashing). At each round, if some block is finalized (for
some honest party), then no other block of that round is notarized (for any honest party). -/
theorem safety (hinj : ∀ k, Function.Injective (π.rank k)) (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {s : GState P V} (hs : Reachable π F s)
    {p q : P} (hp : p ∉ F) (hq : q ∉ F) {B B' : Block P V}
    (hB : Finalized (s.loc p).pool B) (hB' : Notarized (s.loc q).pool B')
    (hr : B'.round = B.round) (hr1 : 1 ≤ B.round) : B' = B := by
  have hI := inv_of_reachable hinj hF hn hs
  have hB'root : B' ≠ .root := Block.ne_root_of_round (by omega)
  refine hI.final_notar_eq hF hn (hI.pool_avail p hp _ hB.2) ?_ hr
  exact (hI.pool_avail q hq _ (hB'.2.resolve_left hB'root)).resolve_left hB'root

/-- The output of an honest party is the chain of a block that is finalized (at the signature
level). -/
theorem output_eq_chain (hinj : ∀ k, Function.Injective (π.rank k)) (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {s : GState P V} (hs : Reachable π F s) {p : P}
    (hp : p ∉ F) : (s.loc p).out = [] ∨ ∃ B, Valid (s.loc p).pool B ∧
      FinalCert π F s.sent B ∧ (s.loc p).out = B.chain := by
  rcases (inv_of_reachable hinj hF hn hs).out_ok p hp with h | ⟨B, -, h2, h3, h4⟩
  · exact Or.inl h.2
  · exact Or.inr ⟨B, h2, h3, h4⟩

/-- Chains of two finalized blocks are prefixes of each other. -/
theorem chain_prefix_of_final {s : GState P V} (hI : Inv π F s) (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {q : P} (hq : q ∉ F) {B B' : Block P V}
    {pool : Set (Msg P V)} (hB : Valid pool B) (hBf : FinalCert π F s.sent B)
    (hB' : Valid (s.loc q).pool B') (hB'f : FinalCert π F s.sent B')
    (hle : B.round ≤ B'.round) : B.chain <+: B'.chain := by
  obtain ⟨A, hA1, hA2, hA3, hA4⟩ := hB'.chain_take B.round hle
  have hAB : A = B := by
    rcases Nat.eq_zero_or_pos B.round with h0 | h0
    · have e : ∀ {pool' : Set (Msg P V)} (C : Block P V), Valid pool' C → C.round = 0 →
          C = .root := by
        intro pool' C hC hC0
        cases C with
        | root => rfl
        | mk k α par pl => simp at hC0; have := hC.1; omega
      rw [e A hA2 (by omega), e B hB h0]
    · rcases hA3 with rfl | hA3
      · exact hI.final_notar_eq hF hn hBf (hI.notarCert_of_finalCert hF hn hB'f) (by omega)
      · have hAroot : A ≠ .root := Block.ne_root_of_round (by omega)
        have hAc : NotarCert π F s.sent A :=
          (hI.pool_avail q hq _ (hA3.2.resolve_left hAroot)).resolve_left hAroot
        exact hI.final_notar_eq hF hn hBf hAc (by omega)
  rw [← hAB, ← hA4]
  exact List.take_prefix _ _

/-- **Consistency of the outputs** (Section 3.3): at any time, the outputs (sequences of committed
blocks) of two honest parties are prefixes of one another. -/
theorem output_prefix (hinj : ∀ k, Function.Injective (π.rank k)) (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {s : GState P V} (hs : Reachable π F s) {p q : P}
    (hp : p ∉ F) (hq : q ∉ F) : (s.loc p).out <+: (s.loc q).out ∨ (s.loc q).out <+: (s.loc p).out := by
  have hI := inv_of_reachable hinj hF hn hs
  rcases hI.out_ok p hp with ⟨-, hp0⟩ | ⟨B, -, hB, hBf, hpB⟩
  · rw [hp0]; exact Or.inl (List.nil_prefix)
  rcases hI.out_ok q hq with ⟨-, hq0⟩ | ⟨B', -, hB', hB'f, hqB'⟩
  · rw [hq0]; exact Or.inr (List.nil_prefix)
  rw [hpB, hqB']
  rcases le_total B.round B'.round with h | h
  · exact Or.inl (chain_prefix_of_final hI hF hn hq hB hBf hB' hB'f h)
  · exact Or.inr (chain_prefix_of_final hI hF hn hp hB' hB'f hB hBf h)

end Podc.InternetComputerConsensus
