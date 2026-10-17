import Papers.PODC2020.DetectableSpace.Alg2Defs

/-!
# Algorithm 2 is not linearizable when `Cas(v, v)` is allowed

Two processes `p ≠ q` both invoke `Cas(v₀, v₀)` on the initial object (value `v₀`). Both read
`C = ⟨v₀, 0…0⟩` at line 28; `p` completes its operation (its hardware CAS at line 35 succeeds,
flipping `vec[p]`, the value stays `v₀`) and returns `true`; then `q`'s hardware CAS fails because
`vec[p]` changed, and `q` returns `false`, although the value of the object was `v₀` throughout.
The (crash-free!) history is

  `inv₀ p Cas(v₀,v₀)`, `inv₁ q Cas(v₀,v₀)`, `res₀ true`, `res₁ false`,

and it has no linearization: every `Cas(v₀, v₀)` applied to the state `v₀` returns `true` and
leaves the state `v₀`. Hence Algorithm 2 is not even linearizable, contradicting Lemma 2 (its
proof claims "the CAS fails only if another process performed a successful CAS to C after p first
read it, hence the value of C after it must be other than old" — false when the successful CAS
wrote back the same value).
-/

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory Alg2

variable {P V : Type} [DecidableEq P] [DecidableEq V]

/-- The schedule of the counterexample. -/
def cexSched (p q : P) (v : V) : List (Ev P (RCOp V)) :=
  [.inv p (.cas v v), .inv q (.cas v v), .step p, .step q, .step p, .step p, .step p, .step p,
    .step p, .step q, .step q, .step q, .step q, .step q]

set_option linter.unusedSimpArgs false in
/-- The history of the counterexample schedule. -/
lemma cex_hist (p q : P) (hpq : p ≠ q) (v₀ : V) :
    ((alg2 (P := P) v₀).exec (alg2 v₀).init (cexSched p q v₀)).2 =
      [.inv 0 p (.cas v₀ v₀), .inv 1 q (.cas v₀ v₀), .res 0 (some (.inr true)) false,
        .res 1 (some (.inr false)) false] := by
  have hne : ((v₀, Function.update (fun _ : P => false) p true) : V × (P → Bool)) ≠
      (v₀, fun _ => false) := by
    intro h
    have := congrFun (Prod.mk.inj h).2 p
    simp at this
  simp only [RImpl.init, cexSched]
  repeat (rw [RImpl.exec_cons]; simp [RImpl.step1, act, start, hpq, Ne.symm hpq, hne])
  rfl

omit [DecidableEq P] in
/-- In a legal sequential order of `Cas(v, v)` operations from state `v`, every completed
operation returned `true`. -/
lemma legal_casSame (v₀ v : V) (h : List (HEv P (RCOp V) (V ⊕ Bool))) :
    ∀ L : List (ℕ × RCOp V), Legal (casRC V v₀) h v L → (∀ y ∈ L, y.2 = .cas v v) →
      ∀ y ∈ L, ∀ r c, HEv.res y.1 (some r) c ∈ h → r = .inr true := by
  intro L
  induction L with
  | nil => simp
  | cons x L ih =>
    obtain ⟨a, o⟩ := x
    intro hl hops y hy r c hr
    have ho : o = .cas v v := hops (a, o) List.mem_cons_self
    subst ho
    obtain ⟨h1, h2⟩ := hl
    simp only [casRC, ite_true] at h1 h2
    rcases List.mem_cons.1 hy with rfl | hy
    · simpa using h1 r c hr
    · exact ih h2 (fun z hz => hops z (by simp [hz])) y hy r c hr

/-- **Algorithm 2 is incorrect** (as soon as there are two processes): it is not durably
linearizable (indeed, not even linearizable — the counterexample has no crash). This refutes
Lemma 2 of the paper for operations `Cas(old, new)` with `old = new`. -/
theorem alg2_not_durLinDet (v₀ : V) (p q : P) (hpq : p ≠ q) :
    ¬ (alg2 (P := P) v₀).DurLinDet := by
  intro hcor
  obtain ⟨⟨L, hL⟩, -⟩ := hcor (cexSched p q v₀)
  rw [cex_hist p q hpq v₀] at hL
  have h1 : 1 ∈ L.map Prod.fst := hL.mem_of_res 1 (.inr false) false (by simp)
  obtain ⟨x, hx, hx1⟩ := List.mem_map.1 h1
  have hops : ∀ y ∈ L, y.2 = .cas v₀ v₀ := by
    intro y hy
    obtain ⟨p', hp'⟩ := hL.inv_of_mem y hy
    simp only [List.mem_cons, HEv.inv.injEq, reduceCtorEq, List.mem_nil_iff, or_false] at hp'
    rcases hp' with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> exact h
  have := legal_casSame v₀ v₀ _ L hL.legal hops x hx (.inr false) false (by rw [hx1]; simp)
  simp at this

end Papers.PODC2020.DetectableSpace
