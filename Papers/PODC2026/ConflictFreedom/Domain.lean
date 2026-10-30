import Mathlib

/-!
# The order-theoretic structure of the trace domain (Section 4.1)

Kuznetsov, Sutra and Toyos-Marfurt, *Conflict-Freedom as a Progress Condition*, PODC 2026.

The generalized commit-adopt object (Section 4.2) and its implementation (Algorithm 2) only use
the following properties of the prefix order on traces, which we axiomatize in the class
`GCADomain`:

* it is a meet-semilattice (every pair has a greatest lower bound `⊓`);
* every *compatible* (bounded above, `Compat`) finite set `S` has a least upper bound `lub S`;
* it is *coherent*: a pairwise compatible finite set is compatible.

The paper states the first two facts (citing Aalbersberg–Rozenberg) and uses the third one
implicitly ("`A_i^co` contains only compatible traces", Section 5). The Mazurkiewicz traces of
duplicate-free schedules are an instance (`Papers.PODC2026.ConflictFreedom.Traces`).
-/

namespace Podc.ConflictFreedom

/-- A set is *compatible* if it has an upper bound (`comp(S)` in the paper). -/
def Compat {T : Type*} [LE T] (S : Set T) : Prop := ∃ z, ∀ x ∈ S, x ≤ z

/-- A meet-semilattice in which compatible finite sets have least upper bounds and which is
coherent (pairwise compatible finite sets are compatible). -/
class GCADomain (T : Type*) extends SemilatticeInf T where
  /-- The least upper bound of a compatible finite set (junk otherwise). -/
  lub : Finset T → T
  isLUB_lub : ∀ S : Finset T, Compat (S : Set T) → IsLUB (S : Set T) (lub S)
  compat_of_pairwise : ∀ S : Finset T, (∀ x ∈ S, ∀ y ∈ S, Compat ({x, y} : Set T)) →
    Compat (S : Set T)

end Podc.ConflictFreedom
