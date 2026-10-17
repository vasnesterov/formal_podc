import Cslib.Computability.Distributed.ApproxConsensus.Async.Replay
import Papers.PODC2020.AsyncApproxBCDirected.Graph

/-!
# Necessity of 3-reach (Theorem 18, Appendix B)

If `G` violates 3-reach, no algorithm solves asynchronous Byzantine approximate consensus on `G`
(`threeReach_of_solves`).

Proof (the paper's indistinguishability argument, made precise). Let `F, Fu, Fv, u, v` witness the
failure of 3-reach and put `Rv = reach_v(F ∪ Fv)`, `Ru = reach_u(F ∪ Fu)` (disjoint). Every
in-neighbour of `Rv` outside `Rv` lies in `F ∪ Fv`.
* `e₁`: `Fv` Byzantine and silent, all inputs `0`, round-robin delivery (fair). By termination
  and validity, `v` decides `0` at some time `T₁`.
* `e₂`: `Fu` Byzantine and silent, all inputs `2ε`; `u` decides `2ε` at time `T₂`.
* `e₃`: `F` Byzantine; inputs `0` on `Rv` and `2ε` on `Ru`. First replay the first `T₁` events
  of `e₁` restricted to deliveries into `Rv` (messages from `F` are injected by the Byzantine
  nodes, messages from `Fv` are delayed), then the first `T₂` events of `e₂` restricted to `Ru`.
  Then `v` decided `0` and `u` decided `2ε`, violating convergence.
  The replay is the library lemma `exists_replay₂` (`Cslib/Computability/Distributed/ApproxConsensus/Async/Replay.lean`).

The paper uses inputs `0` and `ε`; with the non-strict reading of "within `ε`" of Definition 1
this gives no contradiction, so we use `2ε`. More generally (`threeReach_of_solvesOn`), any two
admissible inputs `a, b` with `b − a > ε` work; this covers the setting of Section 4.6 where the
inputs are known to lie in `[0, K]` (with `K > ε`; for `K ≤ ε` the problem is trivial).
-/

open Finset

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

open Cslib.ApproxConsensus Cslib.ApproxConsensus.Async

variable {V M S : Type*} [DecidableEq V] {A : Algorithm V M S} {G : Digraph V} [DecidableRel G.Adj]

/-- **Theorem 18** (necessity of 3-reach), for any input range containing two values more than
`ε` apart: if some algorithm solves asynchronous approximate Byzantine consensus on `G` with up
to `f` faults for inputs in `I`, then `G` satisfies 3-reach. -/
theorem threeReach_of_solvesOn [Fintype V] {f : ℕ} {ε : ℝ} {I : Set ℝ} {a b : ℝ} (ha : a ∈ I)
    (hb : b ∈ I) (hab : ε < b - a) (hA : SolvesOn I A G f ε) : ThreeReach G f := by
  classical
  intro F Fu Fv u v hF hFu hFv hu hv
  by_contra hcon
  push Not at hcon
  set Rv : Finset V := univ.filter fun w => Reaches G (F ∪ Fv) w v
  set Ru : Finset V := univ.filter fun w => Reaches G (F ∪ Fu) w u
  have hdis : Disjoint Rv Ru := disjoint_left.mpr fun w h1 h2 => by
    simp only [Rv, Ru, mem_filter, mem_univ, true_and] at h1 h2; exact hcon w h1 h2
  have hvR : v ∈ Rv := by simp [Rv, Reaches.refl hv]
  have huR : u ∈ Ru := by simp [Ru, Reaches.refl hu]
  have hRvF : ∀ y ∈ Rv, y ∉ Fv ∧ y ∉ F := fun y hy => by
    simp only [Rv, mem_filter, mem_univ, true_and] at hy
    exact ⟨fun h => hy.1 (mem_union_right _ h), fun h => hy.1 (mem_union_left _ h)⟩
  have hRuF : ∀ y ∈ Ru, y ∉ Fu ∧ y ∉ F := fun y hy => by
    simp only [Ru, mem_filter, mem_univ, true_and] at hy
    exact ⟨fun h => hy.1 (mem_union_right _ h), fun h => hy.1 (mem_union_left _ h)⟩
  have hclv : ∀ x y, G.Adj x y → x ≠ y → y ∈ Rv → x ∉ Rv → x ∈ Fv ∨ x ∈ F := by
    intro x y e _ hy hx
    by_contra h
    simp only [not_or] at h
    simp only [Rv, mem_filter, mem_univ, true_and] at hy hx
    exact hx (hy.head e (by simp [h.1, h.2]))
  have hclu : ∀ x y, G.Adj x y → x ≠ y → y ∈ Ru → x ∉ Ru → x ∈ Fu ∨ x ∈ F := by
    intro x y e _ hy hx
    by_contra h
    simp only [not_or] at h
    simp only [Ru, mem_filter, mem_univ, true_and] at hy hx
    exact hx (hy.head e (by simp [h.1, h.2]))
  -- execution e₁: `Fv` Byzantine and silent, all inputs `a`; `v` decides `a`
  obtain ⟨-, hval₁, hterm₁⟩ := hA Fv hFv (fun _ => a) (fun _ => ha) roundRobin
  obtain ⟨T₁, y₁, hy₁⟩ := hterm₁ (roundRobin_fair _) v (fun h => hv (mem_union_right _ h))
  have hy₁0 : y₁ = a := by
    obtain ⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ := hval₁ T₁ v y₁ (fun h => hv (mem_union_right _ h)) hy₁
    linarith
  -- execution e₂: `Fu` Byzantine and silent, all inputs `b`; `u` decides `b`
  obtain ⟨-, hval₂, hterm₂⟩ := hA Fu hFu (fun _ => b) (fun _ => hb) roundRobin
  obtain ⟨T₂, y₂, hy₂⟩ := hterm₂ (roundRobin_fair _) u (fun h => hu (mem_union_right _ h))
  have hy₂b : y₂ = b := by
    obtain ⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ := hval₂ T₂ u y₂ (fun h => hu (mem_union_right _ h)) hy₂
    linarith
  -- execution e₃: `F` Byzantine, inputs `b` on `Ru` and `a` elsewhere, replaying `e₁` on `Rv`
  -- and then `e₂` on `Ru`
  set inp₃ : V → ℝ := fun w => if w ∈ Ru then b else a
  obtain ⟨ev₃, -, h₁, h₂⟩ := exists_replay₂ (A := A) (B := F) hdis hRvF hRuF hclv hclu
    (inp₁ := fun _ => a) (inp₂ := fun _ => b) (inp := inp₃) (fun y hy => by simp [inp₃, disjoint_left.mp hdis hy])
    (fun y hy => by simp [inp₃, hy]) (fun t => roundRobin_ne_byz t) (fun t => roundRobin_ne_byz t)
    T₁ T₂
  obtain ⟨hconv₃, -, -⟩ := hA F hF inp₃ (fun w => by simp only [inp₃]; split_ifs <;> assumption)
    ev₃
  have := hconv₃ (T₁ + T₂) v u a b (fun h => hv (mem_union_left _ h))
    (fun h => hu (mem_union_left _ h)) (by rw [← (h₁.1 v hvR).2, hy₁, hy₁0])
    (by rw [← (h₂.1 u huR).2, hy₂, hy₂b])
  rw [abs_le] at this
  linarith [this.1]

/-- **Theorem 18** (necessity of 3-reach) for arbitrary real inputs. -/
theorem threeReach_of_solves [Fintype V] {f : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hA : Solves A G f ε) : ThreeReach G f :=
  threeReach_of_solvesOn (a := 0) (b := 2 * ε) (Set.mem_univ _) (Set.mem_univ _) (by linarith) hA

end AsyncApproxBCDirected
