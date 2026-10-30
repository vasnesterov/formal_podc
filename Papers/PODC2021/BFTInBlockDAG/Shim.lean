import Papers.PODC2021.BFTInBlockDAG.Gossip
import Papers.PODC2021.BFTInBlockDAG.Link

/-!
# The shim (Algorithm 3): the user interface of the embedding

`shim(P)` at a correct server `s` passes the user's requests to `gossip` (recorded in the ghost
variable `reqs` of `Local`, see `Gossip.lean`) and indicates `(ℓ, i)` to the user when the
interpretation of `P` *for `s` itself* indicates `i` (Algorithm 3, lines 8–9), i.e. when `i` is
triggered at a block of `s`'s block DAG built by `s` (Algorithm 2, lines 13–14). Algorithm 2 runs
concurrently and eventually interprets every block of `G` (Lemma A.10), and the values it computes
do not depend on the order (Lemma 4.2), so we identify the indications of `shim(P)` at `s` with
those triggered at the blocks of `G_s` built by `s`.
-/

namespace Podc.BFTInBlockDAG

variable {S L R M I σ : Type} [DecidableEq S] [DecidableEq L] [DecidableEq R] [LinearOrder M]

/-- `shim(P)` at server `s` indicates `i` for instance `ℓ` (once Algorithm 2 has interpreted the
block DAG of state `σ`). -/
def ShimIndicates (P : Protocol S L R M I σ) (st : Sys S L R) (s : S) (ℓ : L) (i : I) : Prop :=
  ∃ B ∈ (st.loc s).log, B.n = s ∧ i ∈ (interp P ℓ B).ind

/-- Lemma A.18: if the interpretation of `P` indicates `i` for `s` at a block of `s`, then
`shim(P)` at `s` indicates `(ℓ, i)` (definitional in our model). -/
theorem lemma_A_18 (P : Protocol S L R M I σ) (st : Sys S L R) (s : S) (ℓ : L) (i : I)
    (B : Block S L R) (hB : B ∈ (st.loc s).log) (hn : B.n = s) (hi : i ∈ (interp P ℓ B).ind) :
    ShimIndicates P st s ℓ i :=
  ⟨B, hB, hn, hi⟩

end Podc.BFTInBlockDAG
