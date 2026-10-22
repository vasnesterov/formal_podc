# Differences between the formalization and the paper

Paper: Spiegelman, Cassuto, Chockler, Keidar. *Space Bounds for Reliable Storage: Fundamental Limits of Coding.*
PODC 2016. Formalized version: arXiv 1507.05169v1 (the only arXiv version); numbering follows it.

## Errors and gaps in the paper

1. **Theorem 1 is false as stated** (`theorem1_false`, `Coding.lean`). The claim "any write of `u_s ∈ U_s` adds at least
   `log₂|U_s|` bits" fails even when the object stores the minimum number of bits after every write. Take
   `|U₁| = 5` and `|U₂| = 3`: `⌈log₂ 5⌉ = 3` bits, then `⌈log₂ 15⌉ = 4` bits, so the second write adds `1 < log₂ 3`
   bits. With padding it can add 0 bits. The proof's "simple subtraction" of two lower bounds is invalid, and its
   induction hypothesis ("stores `log₂(|U₁|⋯|U_{s-1}|)` bits") is not justified. The statement holds only for
   minimal encodings and set sizes that are powers of two (the simplification made in the proof of Lemma 1); the
   counterexample relies on rounding, the padding variant on non-minimal storage. True in general is the
   cumulative bound `theorem1_cumulative`: after `s` writes the object stores `≥ ⌈log₂ ∏|U_i|⌉` bits.
2. **The storage model is not justified.** After Theorem 1 the paper concludes that "without loss of generality …
   each stored bit is associated with a particular write". This follows neither from Theorem 1 nor from its
   cumulative version. Lemma 1 / Theorem 1 are about one object that must keep *all* written values recoverable from
   its own contents. In a register emulation, old values may be discarded, a value may be spread over several
   objects, and an object may store a function of several values (e.g. `v₁ ⊕ v₂`). The whole Section 4 argument
   (`C⁺`, `F(t)`, Observation 1, Lemma 3) uses this "bits belong to writes" accounting. Section 4 explicitly
   adopts this model ("in the sequel …"), so our Theorem 2 is faithful to the paper's own model; what fails is
   the claim that the model is without loss of generality, i.e. the abstract's "any reliable storage algorithm".
   **We prove Theorem 2 and Corollary 2 for the class of algorithms where it holds by construction** (black-box
   model, see "Model" below): values are opaque, and stored data are blocks, each a function of a single written
   value. Whether the bound holds for algorithms that code across writes is not settled by the paper's argument
   and is not addressed here.
3. **Lemma 2's proof is wrong; its conclusion is trivially true** (`lemma2`, `lemma2_no_extra_bits`). The proof
   claims that choosing among `m` encoders forces storing `log₂ m` additional bits. That is false. Two encoders of
   `Fin 4` into 2 bits, chosen adaptively, decode without any extra bit. The lemma's actual content is simple: an
   adaptive choice of encoders is again a single function, so Lemma 1 applies to it.
4. **The storage measure is under-specified.** `C⁺(t)` counts writes with a bit stored "in one of the base objects
   or in one of the other correct clients". Observation 1 ("the storage is at least `|C⁺(t)|` bits") therefore
   needs the storage to also count copies of a write's data held by clients other than its writer. Our `storage` is
   bits in base objects plus such client-held copies (`Alg.storage`, `Alg.cliBits`). The theorem's hypothesis
   "storage `< S`" thus bounds both. The conclusion of Corollary 2 is about base objects only (`objBits`).
5. **Number of clients.** Theorem 2 starts `S` concurrent writes, and Observation 2 needs a further client to read.
   So the bound needs at least `S + 1` clients (hypothesis `hC : S + 1 ≤ card C`). The paper only says "some finite
   set Π"; its introduction says the bound is meant for an unbounded number of writers. We did not check whether the
   bound fails with few clients.
6. **Observation 2 is slightly misstated** (harmless). After a write completes, a read may also return the value of
   a *completed* write that was concurrent with it, not only one "in `C(t)`". Corollary 1 uses it at the first
   completion, where this does not matter. Our `reader_restore` concludes that the objects of `B` hold `D` bits of
   *some* write of the history, which covers both cases.
7. **Proof of Lemma 3 is a sketch.** "Unless `cᵢ` stores all `D` bits of its value in some base object it is
   impossible to reconstruct this value" ignores copies made by other clients. A client in `C⁻` may read the bits of
   `cᵢ` and store them elsewhere, possibly split over several objects. The argument is correct, but only because
   `Ad` never lets an RMW take effect on an object of `F(t)`. So a full batch of `D` bits is frozen in its object the
   moment it is stored, and smaller batches never reach `D` bits. Our invariant `Inv` (`Adversary.lean`) makes this
   precise: for every write, the blocks outside its writer are none, fewer than `D` bits, or all in one frozen object
   of `F(t)`.
8. **Lemma 4's proof simplified.** The paper grows `T_cᵢ` step by step (at most `f + 1` times). It suffices to take
   `T = F(t)`: while rule 1 does not fire, `F(t)` is constant and all pending RMWs of the quiet client are on `F(t)`.
   Lock-freedom in the solo run with `F(t)` crashed (`solo_progress`) then gives a return or a trigger outside
   `F(t)`.
9. **Theorem 2's final step.** The fair run `r'` is not "identical to `r`": the clients that receive finitely many
   responses must stop taking steps (crashed clients take finitely many steps). We replace their later steps by
   no-ops and prove by simulation (`Rel`, `Rel.step`, `Rel.skip`) that nothing else changes. That every RMW of a
   client with infinitely many responses is eventually served uses "longest pending first" together with the fact
   that such a client is in `C⁻` whenever it receives a response. We prove this with a shrinking set of older RMW
   indices.
10. **Algorithm 2 (Section 3.1), line 16, is unsafe for `k ≤ f`.** The reader may decode any timestamp with `≥ k`
    pieces among its `n − f` responses. Counterexample with replication (`n = 3`, `f = 1`, `k = 1`): `w₁` stores on
    objects 1 and 2 and returns. `w₂` reads objects 1 and 2, stores on 2 and 3, and returns. A later read gets
    objects 1 and 2 and may return `w₁`, although `w₂` precedes it and no write is concurrent. Lemma 9's proof
    ("`rd` reads at least `k` pieces of `v`, and thus restores and returns `v`") ignores that the reader may also see
    `k` pieces of an older write. We formalize the reader that decodes the **largest** qualifying timestamp
    (`Safe.alg`); with this choice Corollary 3 is proved (`Safe.corollary3`). Lean counterexample for the reader that
    decodes the *smallest* qualifying timestamp, a legitimate reading of line 16: the 31-event run in
    `SafeCounterexample.lean` gives `Safe.not_stronglySafe` and `Safe.not_weakRegular`.
11. **Theorem 3 / Corollary 4 (Section 5) are misstated** (not formalized). "In runs with at most `c < k` concurrent
    writes, the storage is bounded by `(c + 1)D/k` bits" is false as written. Even the initial configuration
    stores `n` pieces, i.e. `(2f + k)D/k > (c + 1)D/k` bits. Lemma 12 has the intended bound `(2f+k)(c+1)D/k`, and
    it assumes `c < k − 1`, not `c < k`.
12. **Typos.** Lemma 12's proof cites itself ("by Lemma 12"; meant Lemma 11) and writes `ts' ≥ ts₁ > ts₁`.
    Corollary 5 says "WF-termination" for FW-termination. Theorem 1 has "wih". In Observation 2's proof, `|B| = N − f`
    should be `n − f`.

## Modelling choices

- **System.** Clients `C` (finite), base objects `N` (finite), atomic RMWs given by `apply : R → O → O × Res`. An RMW
  is triggered by a client step and later applied, with its response delivered, by an `exec` event. Taking effect
  and responding form one event (the paper allows a gap). This only restricts the runs, so the lock-freedom and
  regularity hypotheses get weaker and the lower bound stronger. Clients act only while an operation is outstanding.
- **Failures** are not events. A failure pattern `(Fc, Fo)` with `|Fo| ≤ f` enters only the fairness predicate
  `Fair`. Crashed clients take finitely many steps, and RMWs on crashed objects take effect finitely often. A pending
  RMW of a crashed client may still take effect (the paper is silent).
- **Fairness** (`Fair`): every correct client is scheduled infinitely often, and every RMW of a correct client on a
  correct object eventually takes effect. **Lock-freedom** (`LockFree`): in every fair run, an operation of a correct
  client outstanding at time `t` implies that some operation returns at a time `≥ t`.
- **Weak regularity** (`WeakRegular`, MWRegWeak of Shao et al.): for every finite run, value assignment and
  completed read, there is a sequence of the read, all completed writes and possibly some pending writes, respecting
  real-time order, in which the read returns the value of the last write before it (`v₀` if none). Operation
  identifiers are `(client, index)`. The history records invocations and responses; a read's response records its
  output as a function of block contents.
- **Black-box storage model** (`Alg` fields). Written values are opaque; write `w` has value `val w` for an arbitrary
  value assignment `val`. Data are blocks `(w, j)` with contents `enc j (val w)` of `sz j ≥ 1` bits. Initial states
  hold no blocks. Blocks only flow: an RMW stores blocks the client holds, a response carries blocks the object
  holds, and a writer may create blocks of its current write. A read's output may depend only on the contents of the
  blocks it holds. In particular, a client cannot decode another write's value and re-encode it into new blocks
  (e.g. an erasure-coded write-back by a reader); it can only copy existing blocks. This is slightly stricter than
  "each stored bit is associated with a particular write". It keeps the model sound: a block's contents are
  `enc j (val w)` by definition, so letting a client create blocks of a write it cannot decode would give it
  information for free. Control flow and metadata (timestamps, etc.) are arbitrary but value-independent. This excludes
  compression and de-duplication, as the paper says, and also coding across different writes (see error 2).
- `D = ⌈log₂ |V|⌉` (`Nat.clog 2`); the paper writes `D = log₂|V|`. `F(t)` (`Full`) = objects storing `D` bits of
  one write. Requires `|V| ≥ 2`.
- **The adversary `Ad`** (`Adversary.lean`) follows Definition 1. `C⁻` is `Quiet`: no block of any write of the
  client is outside it. Rule 1 executes the oldest pending RMW of a quiet client on an object not in `F(t)`. Rule 2
  schedules clients in round-robin order using a step counter `tick` in the configuration, and a scheduled client
  with nothing to do makes a no-op.
- **Statement of Theorem 2** (`theorem2`): with at least `S + 1` clients, every lock-free weakly regular algorithm
  has a reachable configuration with storage `≥ S` or with more than `f` objects in `F`. This is the contrapositive
  of the paper's statement, and it is proved for the specific run of `Ad` (`theorem2_run`). `f < n/2` is not needed.
- **Corollary 2** (`corollary2`): if the storage is `< S` in all reachable configurations (and there are `> S`
  clients), some reachable configuration has `f + 1` objects each storing `D` bits of a single write, hence
  `objBits ≥ (f + 1) D`.
- Lemma 1 is formalized with `ℓ`-bit strings `Fin ℓ → Bool` and `⌈log₂⌉ = Nat.clog 2`. There is no power-of-2
  assumption (the paper assumes powers of 2 "for simplicity").

## Section 3.1 (Algorithm 2, `SafeAlgorithm.lean`)

- The erasure code is abstract: `n` pieces of `ℓ` bits, `enc : Fin n → V → Fin (2^ℓ)`, and the hypothesis
  `Decodable k enc` ("any `k` pieces determine the value"). The paper's "pieces of size `D/k`" become a parameter
  `ℓ`. Non-vacuity is shown by replication (`k = 1`, `n = 2f + 1`).
- `StronglySafe`: one write sequence `σ` per run, chosen before the value assignment. Every completed read
  without concurrent writes returns the value of the last write of `σ` that precedes it (`v₀` if none). `WaitFree`:
  in every fair run, every operation of a correct client returns.
- Timestamps are `⟨num, (c, i)⟩`, unique per write; the paper uses `⟨num, c⟩`. Objects start with timestamp 0 and
  no piece, because the model requires empty initial objects; the reader returns `v₀` for timestamp 0. RMWs carry a
  phase tag, and a response counts at most once per object and phase. The writer keeps a ghost record of its
  timestamps.
- Lemma 5 is the bound `objBits ≤ n ℓ`. Readers additionally hold copies of the pieces they read.
- `waitFree` only needs `n < 2(n − f)`; `stronglySafe` needs `n = 2f + k`, `k ≥ 1`.

## Not formalized

- Section 5 (Algorithms 3–4, Theorem 3, Lemmas 10–22): the strongly regular adaptive algorithm.
- Section 3.2 and Figure 1 (intuition only).
