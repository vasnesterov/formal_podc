import Mathlib
import Podc.Foundations.InformationTheory.MDSCode
import Cslib.Computability.Distributed.Byzantine.Specs

/-!
# Algorithm 1 (one generation) and the multi-generation algorithm

Liang–Vaidya, *Error-Free Multi-Valued Consensus with Byzantine Failures*, PODC 2011
(arXiv:1101.3520), Section 3, Algorithm 1.

## Model

Synchronous, fully connected network of `n` processors `Fin n`; a static set `F` of at most `t`
Byzantine processors (the adversary is omniscient and the algorithm deterministic, so the paper's
adaptive corruption reduces to a static `F` = the processors that are ever corrupted). The
processors run Algorithm 1 once per *generation*; the only state carried between generations is the
**diagnosis graph** `G`, which is common knowledge of the fault-free processors.

All communication except the point-to-point symbols of step 1(a) goes through the black box
`Broadcast_Single_Bit` (error-free Byzantine broadcast). We use its specification: every fault-free
processor receives the same value, and this value is the source's value if the source is
fault-free. Hence a broadcast value of a faulty source is simply chosen by the adversary, and the
value of a fault-free source is the one prescribed by the algorithm. This is how every broadcast
quantity is modelled below (`M`, `Detected`, `R#`, `Trust`).

The adversary's choices for one generation are an `Adv`: the symbols sent by faulty processors to
each processor (step 1(a)), the broadcast values of faulty processors, and the choice of the sets
`P_match` and `P_decide` among the valid ones ("Find a set …" in steps 1(e), 3(h)). Letting the
adversary pick these sets is more general than any fixed deterministic selection rule.

`⊥` (step 1(b)): processor `i` ignores the symbol of an untrusted processor. The consistency check
`R_i/P_match ∈ C₂ₜ` of step 2(a) and the decoding of step 2(c) are therefore done on the trusted
members of `P_match` (`Gen.X`), as in the paper's proof of Lemma 4 (case 2(a)).

The code `C₂ₜ` is an abstract `Cslib.MDSCode n (n - 2t)`: any `n - 2t` symbols determine the data
(staged in `Podc/Foundations/InformationTheory/MDSCode.lean`, with the Reed–Solomon instance).

## The two variants

The pseudo-code lets *every* processor outside `P_match` announce `Detected` (step 2(b)), even a
processor whose vertex has already been isolated in the diagnosis graph. With this literal reading
(`Variant.literal`) an isolated faulty processor can force the diagnosis stage in every generation
(see `Counterexample.lean`). The prose says that isolated processors are no longer communicated
with; `Variant.repaired` implements this: the `Detected` announcements of processors without any
edge in the diagnosis graph are ignored.
-/

namespace Podc.ErrorFreeMultivaluedBC

open Finset Cslib

noncomputable section

/-! ### Graph operations -/

section Graph

variable {n : ℕ}

/-- Keep the edge `jk` of `G` iff `p j k` and `p k j`. -/
def keepEdges (G : SimpleGraph (Fin n)) (p : Fin n → Fin n → Prop) : SimpleGraph (Fin n) where
  Adj j k := G.Adj j k ∧ p j k ∧ p k j
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun j h => G.loopless.irrefl j h.1⟩

/-- Remove all edges at the vertices of `S`. -/
def isolate (G : SimpleGraph (Fin n)) (S : Set (Fin n)) : SimpleGraph (Fin n) :=
  keepEdges G fun j _ => j ∉ S

open Classical in
/-- The number of edges at `j` removed so far: the non-neighbours of `j` other than `j` (the
diagnosis graph starts complete). -/
def removed (G : SimpleGraph (Fin n)) (j : Fin n) : ℕ :=
  #{k | k ≠ j ∧ ¬G.Adj j k}

/-- `j` has no edge left in the diagnosis graph. -/
def Isolated (G : SimpleGraph (Fin n)) (j : Fin n) : Prop := ∀ k, ¬G.Adj j k

@[simp] theorem keepEdges_adj {G : SimpleGraph (Fin n)} {p : Fin n → Fin n → Prop} {j k : Fin n} :
    (keepEdges G p).Adj j k ↔ G.Adj j k ∧ p j k ∧ p k j := Iff.rfl

@[simp] theorem isolate_adj {G : SimpleGraph (Fin n)} {S : Set (Fin n)} {j k : Fin n} :
    (isolate G S).Adj j k ↔ G.Adj j k ∧ j ∉ S ∧ k ∉ S := Iff.rfl

end Graph

/-! ### Algorithm, adversary and one generation -/

/-- How the `Detected` announcements of processors outside `P_match` are used. -/
inductive Variant
  /-- Algorithm 1 as printed: every processor outside `P_match` is listened to. -/
  | literal
  /-- Announcements of processors already isolated in the diagnosis graph are ignored (the
  paper's prose: "the fault-free processors will not communicate with it anymore"). -/
  | repaired
  deriving DecidableEq

/-- The algorithm's parameters: the `(n, n - 2t)` code `C₂ₜ`, the default decision `d` and the
variant. -/
structure Alg (n t : ℕ) (α β : Type*) where
  /-- The code `C₂ₜ` (only its MDS property is used). -/
  C : MDSCode n (n - 2 * t) α β
  /-- The default value decided when no `P_match` exists (step 1(f)). -/
  d : α
  /-- Literal pseudo-code or the repaired version. -/
  var : Variant

/-- The adversary's choices in one generation. Entries concerning fault-free processors are
ignored. -/
structure Adv (n : ℕ) (α β : Type*) where
  /-- `sym j i`: the symbol that the faulty processor `j` sends to `i` in step 1(a). -/
  sym : Fin n → Fin n → β
  /-- The vector `M_j` broadcast by a faulty `j` in step 1(d). -/
  M : Fin n → Fin n → Prop
  /-- The bit `Detected_j` broadcast by a faulty `j` in step 2(b). -/
  det : Fin n → Prop
  /-- The symbol `R#[j]` broadcast by a faulty `j` in step 3(a). -/
  rs : Fin n → β
  /-- The vector `Trust_j` broadcast by a faulty `j` in step 3(d). -/
  trust : Fin n → Fin n → Prop
  /-- The set `P_match` chosen in step 1(e). -/
  pmatch : Finset (Fin n)
  /-- The set `P_decide` chosen in step 3(h). -/
  pdecide : Finset (Fin n)

/-- Everything that determines one generation: the algorithm, the faulty set, the diagnosis graph
at the start of the generation, the inputs of the generation and the adversary's choices. -/
structure Gen (n t : ℕ) (α β : Type*) where
  /-- The algorithm. -/
  A : Alg n t α β
  /-- The faulty processors. -/
  F : Finset (Fin n)
  /-- The diagnosis graph at the start of the generation. -/
  G : SimpleGraph (Fin n)
  /-- The inputs `v_i(g)` of the generation. -/
  v : Fin n → α
  /-- The adversary's choices. -/
  a : Adv n α β

namespace Gen

variable {n t : ℕ} {α β : Type*} (σ : Gen n t α β)

open Classical

/-- Step 1(a): the codeword `S_i = C₂ₜ(v_i(g))`. -/
def S (i : Fin n) : Fin n → β := σ.A.C.enc (σ.v i)

/-- Step 1(b): the symbol `R_i[j]` that `i` receives from `j` (meaningful when `i` trusts `j`, or
`j = i`). A fault-free `j` sends `S_j[j]`. -/
def R (i j : Fin n) : β := if j ∈ σ.F then σ.a.sym j i else σ.S j j

/-- Steps 1(c)–(d): the broadcast vector `M_j`; for fault-free `j`,
`M_j[k] = (j trusts k ∧ R_j[k] = S_j[k])`. -/
def M (j k : Fin n) : Prop := if j ∈ σ.F then σ.a.M j k else σ.G.Adj j k ∧ σ.R j k = σ.S j k

/-- Step 1(e): `P` is a matching set: `|P| = n - t` and `M_j[k] = M_k[j] = true` for all distinct
`j, k ∈ P`. -/
def IsMatch (P : Finset (Fin n)) : Prop := P.card = n - t ∧ ∀ j ∈ P, ∀ k ∈ P, j ≠ k → σ.M j k

/-- A matching set exists (otherwise step 1(f) decides the default value). -/
def MatchExists : Prop := ∃ P, σ.IsMatch P

/-- The chosen `P_match`. -/
abbrev Pm : Finset (Fin n) := σ.a.pmatch

/-- The members of `P` whose symbols `i` uses: those `i` trusts, and `i` itself. -/
def X (i : Fin n) (P : Finset (Fin n)) : Finset (Fin n) := P.filter fun j => j = i ∨ σ.G.Adj i j

/-- Steps 2(a)–(b): the broadcast bit `Detected_j`; for fault-free `j`,
`Detected_j = (R_j/P_match ∉ C₂ₜ)`, checked on the trusted members of `P_match`. -/
def Det (j : Fin n) : Prop :=
  if j ∈ σ.F then σ.a.det j else ¬σ.A.C.Consistent (σ.X j σ.Pm) (σ.R j)

/-- Whether the announcement of `j` is taken into account. -/
def Counted (j : Fin n) : Prop := σ.A.var = .literal ∨ ∃ k, σ.G.Adj j k

/-- Step 2(c): some processor outside `P_match` announced a detection, so the diagnosis stage is
entered. -/
def Diag : Prop := ∃ j ∉ σ.Pm, σ.Counted j ∧ σ.Det j

/-- Steps 3(a)–(b): the broadcast symbol `R#[j]`; a fault-free `j` broadcasts `S_j[j]`. -/
def Rs (j : Fin n) : β := if j ∈ σ.F then σ.a.rs j else σ.S j j

/-- Steps 3(c)–(d): `Trust_i[j]` (for `j ∈ P_match`); for fault-free `i`,
`Trust_i[j] = (i trusts j ∧ R_i[j] = R#[j])`. -/
def Trust (i j : Fin n) : Prop := if i ∈ σ.F then σ.a.trust i j else σ.G.Adj i j ∧ σ.R i j = σ.Rs j

/-- Step 3(e): remove every edge `jk` with `Trust_j[k] = false` (`k ∈ P_match`) or
`Trust_k[j] = false` (`j ∈ P_match`). -/
def G1 : SimpleGraph (Fin n) := keepEdges σ.G fun j k => k ∈ σ.Pm → σ.Trust j k

/-- The processors isolated in step 3(f) (if `R#/P_match ∈ C₂ₜ`): outside `P_match`, announced a
detection, and lost no edge in step 3(e). -/
def IsoF : Set (Fin n) :=
  {j | j ∉ σ.Pm ∧ σ.Counted j ∧ σ.Det j ∧ ∀ k, σ.G.Adj j k → σ.G1.Adj j k}

/-- Step 3(f). -/
def G2 : SimpleGraph (Fin n) := if σ.A.C.Consistent σ.Pm σ.Rs then isolate σ.G1 σ.IsoF else σ.G1

/-- Step 3(g): isolate every vertex with at least `t + 1` removed edges. -/
def G3 : SimpleGraph (Fin n) := isolate σ.G2 {j | t + 1 ≤ removed σ.G2 j}

/-- The diagnosis stage is performed in this generation. -/
def Diagnosed : Prop := σ.MatchExists ∧ σ.Diag

/-- The diagnosis graph at the end of the generation. -/
def next : SimpleGraph (Fin n) := if σ.Diagnosed then σ.G3 else σ.G

/-- The decision `v'_i(g)` of processor `i` (steps 1(f), 2(c), 3(i)). -/
def out (i : Fin n) : α :=
  if ¬σ.MatchExists then σ.A.d
  else if σ.Diag then σ.A.C.decode σ.A.d σ.a.pdecide σ.Rs
  else σ.A.C.decode σ.A.d (σ.X i σ.Pm) (σ.R i)

/-- The adversary's choices of `P_match` and `P_decide` are valid: `P_match` is a matching set
whenever one exists, and in the diagnosis stage `P_decide ⊆ P_match` has `n - 2t` pairwise
trusting members in the updated diagnosis graph. -/
def ChoicesValid : Prop :=
  (σ.MatchExists → σ.IsMatch σ.Pm) ∧
    (σ.Diagnosed → σ.a.pdecide ⊆ σ.Pm ∧ σ.a.pdecide.card = n - 2 * t ∧
      ∀ j ∈ σ.a.pdecide, ∀ k ∈ σ.a.pdecide, j ≠ k → σ.G3.Adj j k)

end Gen

/-! ### Runs -/

/-- A run: the faulty set, the inputs `inp g i = v_i(g)` of every generation and the adversary's
choices in every generation. -/
structure Run (n : ℕ) (α β : Type*) where
  /-- The faulty processors. -/
  F : Finset (Fin n)
  /-- `inp g i`: the input of processor `i` in generation `g` (the `g`-th `D`-bit part). -/
  inp : ℕ → Fin n → α
  /-- The adversary's choices in generation `g`. -/
  adv : ℕ → Adv n α β

namespace Run

variable {n t : ℕ} {α β : Type*} (A : Alg n t α β) (r : Run n α β)

/-- The diagnosis graph at the start of generation `g` (complete at the start). -/
def graph : ℕ → SimpleGraph (Fin n)
  | 0 => ⊤
  | g + 1 => (Gen.mk A r.F (graph g) (r.inp g) (r.adv g)).next

/-- Generation `g` of the run. -/
def gen (g : ℕ) : Gen n t α β := ⟨A, r.F, r.graph A g, r.inp g, r.adv g⟩

theorem graph_succ (g : ℕ) : r.graph A (g + 1) = (r.gen A g).next := rfl

/-- Admissible runs: at most `t` faulty processors and valid choices of `P_match`, `P_decide`. -/
def Valid : Prop := r.F.card ≤ t ∧ ∀ g, (r.gen A g).ChoicesValid

open Classical in
/-- The number of generations among the first `N` in which the diagnosis stage is performed. -/
def numDiag (N : ℕ) : ℕ := #{g ∈ range N | (r.gen A g).Diagnosed}

end Run

end

end Podc.ErrorFreeMultivaluedBC
