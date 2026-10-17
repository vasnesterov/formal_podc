import Podc.LockStep.Basic
import Podc.Agreement.Specs
import Mathlib

/-!
# The partially authenticated setting (Lenzen–Loss–Shi–Wagner, PODC 2026)

We use CSLib's synchronous lock-step Byzantine model (`Cslib.Byzantine.LockStep`) on the complete
network `⊤`, with ideal signatures given by abstract tokens (`Auth`). The *partially authenticated*
setting with registered parties `Reg` is the restriction that **only registered parties can sign**:
every token that occurs in a message has a registered signer (`RegisteredSigners`). Unregistered
parties may still put arbitrary data into messages, but anybody (in particular the adversary) can
produce such data, so it carries no authentication.

* `SolvablePA Reg Z spec`: some unforging protocol whose tokens all have registered signers solves
  `spec` against every unforgeability-respecting adversary corrupting a set in `Z`.
* `Gradecast snd`: Definition 2.3 of the paper (termination, validity, graded consistency), the
  shared binary gradecast `Cslib.Byzantine.Problem.BinaryGradecast`; `gradecast_iff`.
* `CoverSystem.scenario_authValid_pa`: the FLM covering adversary respects unforgeability as soon as
  every node listened to is an honest lift, a copy of a Byzantine party, or a copy of an
  *unregistered* party (unregistered parties never create tokens). -- CSLib candidate

The threshold adversary structure `atMost t` is the shared `Cslib.Byzantine.LockStep.atMost`.
-/

namespace PartialAuthBC

open Cslib.Byzantine.LockStep

variable {P I M O S Q : Type*}

/-- Only registered parties can sign: every signature token occurring in a message has a
registered signer. -/
def RegisteredSigners (Reg : Set P) (A : Auth P M S) : Prop :=
  ∀ m, ∀ τ ∈ A.tokens m, A.signer τ ∈ Reg

/-- `spec` is solvable in the partially authenticated setting with registered parties `Reg`
(synchronous, complete network, static adversary corrupting a set in `Z`). -/
def SolvablePA (Reg : Set P) (Z : AdvStructure P) (spec : Spec P I O) : Prop :=
  ∃ (M S : Type) (A : Auth P M S) (alg : Protocol P I M O),
    RegisteredSigners Reg A ∧ alg.Unforging A ∧ SolvesAuth ⊤ alg A Z spec

/-- **Gradecast** with sender `snd` (Definition 2.3): the binary-grade gradecast of the shared
library (`gradecast_iff` spells it out). -/
abbrev Gradecast {V : Type*} (snd : P) : Spec P V (V × Bool) :=
  Cslib.Byzantine.Problem.BinaryGradecast snd

/-- Definition 2.3 as stated in the paper: termination, validity (an honest sender's input is
output by every honest party with grade `1`), graded consistency (if an honest party outputs `v`
with grade `1`, every honest party outputs `v`). -/
theorem gradecast_iff {V : Type*} {snd : P} {x : P → V} {H : Set P} {dec : P → V × Bool → Prop} :
    Gradecast snd x H dec ↔
      (∀ p ∈ H, ∃ o, dec p o) ∧
      (snd ∈ H → ∀ p ∈ H, dec p (x snd, true)) ∧
      (∀ p ∈ H, ∀ q ∈ H, ∀ v w g, dec p (v, true) → dec q (w, g) → v = w) :=
  Cslib.Byzantine.Problem.binaryGradecast_iff

/-- Unauthenticated solvability gives partially authenticated solvability (no tokens at all). -/
lemma Solvable.solvablePA {Reg : Set P} {Z : AdvStructure P} {spec : Spec P I O}
    (h : Solvable ⊤ Z spec) : SolvablePA Reg Z spec := by
  obtain ⟨M, alg, h⟩ := h
  exact ⟨M, Empty, Auth.none P M, alg, fun _ τ => τ.elim, alg.unforging_none,
    h.solvesAuth _ alg _⟩

/-- Monotonicity in the adversary structure. -/
lemma SolvablePA.mono {Reg : Set P} {Z Z' : AdvStructure P} {spec : Spec P I O}
    (h : SolvablePA Reg Z spec) (hZ : Z' ⊆ Z) : SolvablePA Reg Z' spec := by
  obtain ⟨M, S, A, alg, hR, hU, h⟩ := h
  exact ⟨M, S, A, alg, hR, hU, fun s hs => h s (hZ hs)⟩

namespace CoverSystem

variable {G : SimpleGraph P} {alg : Protocol P I M O} {A : Auth P M S}
variable (C : Cslib.Byzantine.LockStep.CoverSystem P I Q) {B : Set P} {σ : P → Q}

/-- Variant of CSLib's `CoverSystem.scenario_authValid` for the partially authenticated setting:
nodes that copy an *unregistered* honest party may also be listened to, since unregistered parties
never create tokens; all tokens they relay come from the rest of the cover. -- CSLib candidate -/
theorem scenario_authValid_pa (Reg : Set P) (hR : RegisteredSigners Reg A)
    (hU : alg.Unforging A) (hL : C.Lift G B σ)
    (hφ : ∀ q p q', C.nbr q p = some q' → C.φ q' = p)
    (hsim : ∀ q p q', G.Adj p (C.φ q) → C.nbr q p = some q' →
      (∃ p', p' ∉ B ∧ q' = σ p') ∨ C.φ q' ∈ B ∨ C.φ q' ∉ Reg)
    (x₀ : P → I) : (C.scenario G alg B σ x₀).AuthValid G alg A := by
  set s := C.scenario G alg B σ x₀
  have key : ∀ r q, A.histTokens (C.hist G alg r q) ⊆
      {τ | A.signer τ ∈ B} ∪ honestTokens G alg A s r := by
    intro r
    induction r with
    | zero => intro q τ hτ; simp [Cslib.Byzantine.LockStep.CoverSystem.hist, Auth.histTokens] at hτ
    | succ r ih =>
      intro q τ hτ
      rw [Cslib.Byzantine.LockStep.CoverSystem.hist, Auth.histTokens_append] at hτ
      rcases hτ with hτ | hτ
      · rcases ih q hτ with h | h
        · exact Or.inl h
        · exact Or.inr (honestTokens_mono G alg A s (Nat.le_succ r) h)
      · obtain ⟨ib, hib, p, m, hm, hτm⟩ := hτ
        simp only [List.mem_singleton] at hib
        subst hib
        by_cases hadj : G.Adj p (C.φ q)
        · simp only [hadj, ite_true] at hm
          obtain ⟨q', hq', hm'⟩ := Option.bind_eq_some_iff.mp hm
          have hφq' := hφ q p q' hq'
          rcases hsim q p q' hadj hq' with ⟨p', hp', rfl⟩ | hB | hNR
          · have hpp' : p' = p := by rw [← hL.φ_σ p' hp']; exact hφq'
            subst hpp'
            refine Or.inr ⟨r, Nat.le_succ r, p', hp', C.φ q, hadj, m, ?_, hτm⟩
            rw [Cslib.Byzantine.LockStep.CoverSystem.hist_scenario C hL x₀ r p' hp',
              Cslib.Byzantine.LockStep.CoverSystem.scenario_input_of_not_mem C x₀ hp']
            rw [hL.φ_σ p' hp'] at hm'; exact hm'
          · rcases hU _ _ _ _ _ hm' τ hτm with hs | hs
            · exact Or.inl (show A.signer τ ∈ B by rw [hs]; exact hB)
            · rcases ih q' hs with h | h
              · exact Or.inl h
              · exact Or.inr (honestTokens_mono G alg A s (Nat.le_succ r) h)
          · rcases hU _ _ _ _ _ hm' τ hτm with hs | hs
            · exact absurd (hs ▸ hR m τ hτm) hNR
            · rcases ih q' hs with h | h
              · exact Or.inl h
              · exact Or.inr (honestTokens_mono G alg A s (Nat.le_succ r) h)
        · simp [hadj] at hm
  intro r b q m hb hq _ hm τ hτ
  simp only [s, Cslib.Byzantine.LockStep.CoverSystem.scenario] at hm
  obtain ⟨q', hq', hm⟩ := Option.bind_eq_some_iff.mp hm
  have hφq' : C.φ q' = b := hφ _ _ _ hq'
  rcases hU _ _ _ _ _ hm τ hτ with hs | hs
  · exact Or.inl (show A.signer τ ∈ _ by rw [hs, hφq']; exact hb)
  · exact key r q' hs

end CoverSystem

end PartialAuthBC
