import Papers.PODC2020.BezoutElection.Alg2SymProof
import Papers.PODC2020.BezoutElection.Alg2Prog5

/-!
# Algorithm 2 is correct (Theorem 4)

Symmetry, read/write, safety (Lemma 2) and termination (Lemma 1) are proved.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {R : Type} [Inhabited R]
  {P : Type} [Fintype P] [DecidableEq P] {m : ℕ}

/-- **Algorithm 2 is symmetric** (for an output map that commutes with renamings) and uses only
reads and writes. -/
theorem alg2_symmetric (p : Params) (out : Id → Finset Id → R)
    (hout : ∀ (σ : Equiv.Perm Id) a L, out (σ a) (L.map σ.toEmbedding) = out a L) :
    (alg2 Id m p out).Symmetric :=
  alg2_symmetric' p out hout

theorem alg2_readWrite (p : Params) (out : Id → Finset Id → R) :
    (alg2 Id m p out).ReadWrite :=
  alg2_readWrite' p out

/-- **Lemma 2 (safety)**: all processes that return agree on one leader set `L`; if some process
returned, `L` consists of `U m − W n` identifiers of processes (`d = gcd(m,n) ℓ` for the paper's
parameters, see `Bezout.lean`). Hypotheses added w.r.t. the original target: `0 < m` (with `m = 0`
the model returns `default` at once) and `W n ≤ U m` (i.e. `d ≥ 0`; without it all competitions
can be solved before anybody sets `finishing`, and every process returns `∅`). The one-shot
hypothesis is not needed. -/
theorem alg2_agreement (p : Params) (out : Id → Finset Id → R) (ids : P → Id)
    (hid : Function.Injective ids) (hn : Fintype.card P = p.n) (π : P → Equiv.Perm (Fin m))
    (hm : 0 < m) (hd : p.W * p.n ≤ p.U * m)
    (α : List (Label P (elecObj R))) (hα : ((alg2 Id m p out).impl ids π).Valid α)
    (_h1 : OneShot α) :
    ∃ L : Finset Id, (∀ q r, outputs α q = some r → r = out (ids q) L) ∧
      ((∃ q, outputs α q ≠ none) → L.card + p.W * p.n = p.U * m ∧ ∀ a ∈ L, ∃ q, ids q = a) :=
  alg2_agreement' p out ids hid hn π hm hd α hα

/-- **Lemma 1 (termination)**: if `W n ≤ U m ≤ W n + n` (i.e. `0 ≤ d ≤ n`), every process
returns in every fair execution where all processes participate.
The levels never decrease and are bounded, and once all competitions are solved every process
returns (`alg2_terminates_of_progress`, `Alg2Live.lean`); as long as some competition is open,
some competition is eventually solved (`alg2_progress`, `Alg2Prog5.lean`). The one-shot
hypothesis of `Terminates` is not needed. -/
theorem alg2_terminates (p : Params) (out : Id → Finset Id → R) (ids : P → Id)
    (hid : Function.Injective ids) (hn : Fintype.card P = p.n) (π : P → Equiv.Perm (Fin m))
    (h1 : p.W * p.n ≤ p.U * m) (h2 : p.U * m ≤ p.W * p.n + p.n) :
    Terminates ((alg2 Id m p out).impl ids π) :=
  alg2_terminates' hid hn h1 h2

end BezoutElection.Alg2
