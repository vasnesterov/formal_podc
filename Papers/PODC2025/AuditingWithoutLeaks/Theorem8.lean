import Papers.PODC2025.AuditingWithoutLeaks.Effective
import Papers.PODC2025.AuditingWithoutLeaks.RenameWrites
import Papers.PODC2025.AuditingWithoutLeaks.RemoveReader

/-!
# Theorem 8 of Attiya, Fernández Anta, Milani, Rapetti, Travers (PODC 2025)

"Algorithm 1 is a linearizable and wait-free implementation of an auditable multi-writer,
multi-reader register. Moreover, an audit reports `(j, v)` iff `p_j` has a `v`-effective read; a
write is uncompromised by a reader `p_j` unless `p_j` has a `v`-effective read; a read by `p_k`
is uncompromised by a reader `p_j ≠ p_k`."

The parts are, in this formalization:
* linearizability (even strong linearizability): `alg1_linearizable`, `alg1_stronglyLinearizable`;
* wait-freedom (Lemma 2): `alg1_waitFree`;
* audits report every read that was effective before the audit was invoked (Lemma 5): `lemma5`,
  and only reads that are effective when it returns: `audit_sound`;
* Lemma 6 (writes uncompromised): `lemma6`;
* Lemma 7 (reads uncompromised), in a strengthened form (in the indistinguishable execution,
  `p_k` invokes nothing at all): `lemma7`, and Definition 3 for reads: `read_uncompromised`.
-/

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au] {v₀ : V}
  {rnd : ℕ → Fin m → Bool}

/-- **Lemma 6.** For every value `v` and reader `p_j`, either `p_j` has a `v`-effective read in
`α`, or there is an execution indistinguishable from `α` to `p_j` in which no write has input `v`
(assuming some value other than `v` exists). -/
theorem lemma6 {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C : Cfg m W Au V v₀}
    (hα : (alg1 rnd v₀).run α = some C) (j : Fin m) {v v' : V} (hvv : v' ≠ v) :
    (∃ k, Invoked α (.rd j, k) ∧ Impl.EffectiveFam (alg1F W Au v₀) rnd α (.rd j, k) (.val v)) ∨
    ∃ α', (alg1 rnd v₀).Valid α' ∧ Impl.IndistFam (alg1F W Au v₀) (.rd j) (rnd, α) (rnd, α') ∧
      ∀ w, ∀ o ∈ opsOf α' (.wr w), o ≠ .write v := by
  by_cases h : ∃ t, Fetched rnd C j t ∧ hv v₀ C t = v
  · obtain ⟨t, hf, hvt⟩ := h
    exact Or.inl (effective_of_fetched hα hf hvt)
  · push Not at h
    exact Or.inr (rename_writes hα j hvv h)

/-- **Lemma 7** (strengthened). For readers `p_j ≠ p_k`, there is an execution indistinguishable
from `α` to `p_j` (with other one-time pads) in which `p_k` invokes no operation; in particular
no read by `p_k` is effective there. -/
theorem lemma7 {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C : Cfg m W Au V v₀}
    (hα : (alg1 rnd v₀).run α = some C) {j k : Fin m} (hjk : j ≠ k) :
    ∃ rnd' α', (alg1 rnd' v₀).Valid α' ∧
      Impl.IndistFam (alg1F W Au v₀) (.rd j) (rnd, α) (rnd', α') ∧ opsOf α' (.rd k) = [] ∧
      ∀ n v, ¬ (Invoked α' (.rd k, n) ∧
        Impl.EffectiveFam (alg1F W Au v₀) rnd' α' (.rd k, n) (.val v)) := by
  obtain ⟨rnd', α', h1, h2, h3, -⟩ := remove_reader hα hjk
  refine ⟨rnd', α', h1, h2, h3, fun n v hh => ?_⟩
  have hi := hh.1
  simp [Invoked, h3] at hi

/-- **Theorem 8** (reads are uncompromised by other readers, Definition 3): every read of `p_k`
invoked in `α` is uncompromised by any other reader `p_j`. -/
theorem read_uncompromised {α : List (Label (Proc m W Au) (auditReg m V v₀))}
    {C : Cfg m W Au V v₀} (hα : (alg1 rnd v₀).run α = some C) {j k : Fin m} (hjk : j ≠ k)
    (n : ℕ) : Impl.UncompromisedFam (alg1F W Au v₀) rnd α (.rd k, n) (.rd j) := by
  intro o _
  obtain ⟨rnd', α', h1, h2, h3, -⟩ := remove_reader hα hjk
  refine ⟨rnd', α', h1, h2, ?_⟩
  simp [opOf, h3]

end Podc.AuditingWithoutLeaks
