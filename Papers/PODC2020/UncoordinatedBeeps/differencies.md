# Differences between the formalization and the paper

Paper: F. Dufoulon, J. Burman, J. Beauquier, *Can Uncoordinated Beeps tell Stories?*, PODC 2020 (proceedings
version; the extended version [7] was not available to us).

## Errors and imprecisions in the paper

1. **Lemma 4 is false as stated.** The paper says: "every non-zero element of {0,…,l−1} can be expressed at most
   once as a difference d₁ − d₂ mod l". Counterexample: the Erdős–Turán set for p = K = 3, D = {0, 7, 13}. It is a
   (14, 3) Sidon set (14 ≤ 2p² = 18), and 7 − 0 ≡ 0 − 7 ≡ 7 (mod 14) (`lemma_4_mod_false`). A smaller one is
   D = {0, 1}, l = 2. Both use a pair and its reverse. A counterexample with two different unordered pairs is
   D = {0, 1, 3}, l = 4: 1 ≡ 1 − 0 ≡ 0 − 3 (mod 4) (`lemma_4_mod_false'`). The proof establishes only the integer statement (`lemma_4`): d₁ − d₂ = d₃ − d₄ ≠ 0 implies
   d₁ = d₃ and d₂ = d₄. Only that version is used, in Lemma 6.
2. **Definition 4 (Sidon set) has to count the sums d + d.** Under the reading "sums of distinct elements are
   distinct", {0,1,2} is a (3,3) Sidon set but not a Golomb ruler (1−0 = 2−1). Its codeword overlaps its own shift
   by 1 in two positions, so Lemma 6 fails (`lemma_6_needs_strong_sidon`). We use the strong definition
   (`Cslib.IsSidon`). The Erdős–Turán sets satisfy it.
3. **Lemma 6 omits t ≠ t'.** For t = t' the two words coincide and share K ones. We add the hypothesis (`lemma_6`).
   We also prove a stronger lemma: two extended shifted words built from subsets P, Q of a Sidon set share at most
   one 1-position unless t = t' and P ∩ Q ≠ ∅ (`card_common_le_one`). This is the "slight modification" of the
   proof of Theorem 5 that the paper says gives Theorem 7, but does not write out.
4. **Theorem 1 needs l ≥ 1.** For l = 0 the admissible shift range {−l+1,…,l−1} is empty. Definition 2 then holds
   vacuously, while Definition 3 fails for any non-empty code (`theorem_1_length_zero`). The paper defines
   communication schemes only for l ≥ 1, so this is degenerate. We add `0 < l` to `theorem_1` and `theorem_2`
   (`theorem_2'` with Definition 3 needs nothing).
5. **Theorems 5 and 7 need K ≥ 1.** For K = 0, "USI(1, K−1)" is not meaningful (k = −1). We state Theorem 7 with
   `1 ≤ K`, and the general form `isUSICode_of_sidon` with parts of size k + 1.
6. **Corollary 8's derivation needs an odd prime p with K ≤ p ≤ 2K.** Bertrand's postulate, as quoted, may give
   p = 2, and for K = h(k+1) = 1 no odd prime exists in [1, 2]. For K ≥ 2 Bertrand gives a prime p > K ≥ 2, which
   is odd. For K ≤ 1 we use the trivial Sidon set {0} (`Cslib.SidonSet.exists_sidon_enum`). Corollary 8 also holds
   for h = 0 (length 0, empty code).
7. **Theorem 7 says "S₁,…,S_h as partitions of S".** We formalize this as pairwise disjoint sets of size K whose
   union is D (`theorem_7`). The general lemma only needs disjoint (k+1)-subsets of D.
8. **Codeword definitions say "c[p] = 1 if p ∈ S".** "Iff" is intended, and we use it (`indWord`).
9. **Footnote 4**, "σ̄(c,t₁′) ≠ σ̄(c,t₂′) iff t₁′ ≠ t₂′", fails for the all-zero codeword. This has no consequence,
   because USI codes with k ≥ 0 never contain the zero word.
10. **Theorem 10, last inequality (arithmetic check only).** f(Δ_up² + Δ_up + 2) ≤ f(Δ_up + 1)² holds only for Δ_up ≥ 1. For a single node
    (Δ_up = 0) a node relays its own c₁ (it hears its own beeps), so there can be 2f > f(Δ_up+1)² transmissions in
    a window. This is degenerate, since one can always take Δ_up ≥ 1. Not formalized.
11. **Algorithm 3 reads history bits before the wake-up (suspected gap; not formalized, not checked in Lean).** Lines 6 and 8–9 test
    windows H[r−l−(i−1), r−1−(i−1)] for all r ≥ 1 and i ≤ l, so their indices can be ≤ 0. The paper does not
    define these bits, and Lemma 11 covers only windows that start while the node is awake. Suppose they read as
    0 and c₁[1] = 0, which is possible because Theorem 7 and Corollary 8 do not say which part becomes c₁. Then a
    node u that wakes one round after its neighbour w started c₁ sees c₁ in its window starting at local round 0.
    It would relay c₂, and a neighbour v of u would record a 2-hop beep of w for a round in which u was asleep, so w ∉
    N₂ᵃ(v, ·). This would contradict Definition 5 and Remark 2. Either fix would close the gap: give c₁ the position of the Sidon element
    0 (c₁[1] = 1), or decode only windows inside the awake period. We did not formalize Section 4, so this was not
    checked in Lean.

## Modelling choices

* Words are `Fin n → Bool` with 0-based positions. The paper's σ(x,t)[i] = x[i−t] and
  σ̄(x,t) = 0^{l−1+t} x 0^{l−1−t} become `shift` and `extShift`, defined through the ℤ-indexed `Word.getZ`
  (0 outside the word). For admissible t they agree with the paper's words bit for bit.
* "Set of codeword and shift pairs" is a `Finset (Word l × ℤ)`, and "(c′,t) ∉ X" is membership of the pair. This
  is how the paper's proofs read it.
* A USI(h,k)-code is a `Finset` of h codewords (`C.card = h`). In Definitions 2 and 3 the codeword c′ and all
  pairs of X range over C, and the shifts range over {−l+1,…,l−1}.
* Theorem 2: the paper's "uncoordinated transmission scenario" is modelled by `Scenario`. It has a finite node
  type, a `SimpleGraph`, integer global rounds, wake-up rounds, and finite sets of transmissions (codeword, global
  start) per node, started while awake. A node's beeps are the OR of its transmissions, and H_v is "v or a
  neighbour beeps". Beeps are delivered only to awake nodes in the paper. In the model every beep comes from an
  awake transmitter and v listens only in local rounds ≥ 1, so delivery is automatic and the model agrees with the
  paper. "Solves" is formalized as "for every c′ ∈ C, H_v[r_v, r_v+l−1] contains c′ iff some u ∈ N(v) started c′
  in global round g_v(r_v)". This is the paper's conclusion in its proof. The conflict is the number of distinct
  (codeword, start) pairs started in N(v) within l−1 rounds of g_v(r_v). Counting per node instead would give a
  stronger hypothesis.
* Theorem 3 is stated with l = 2p², together with the bound 2p² ≤ 8K². `Cslib.SidonSet.erdosTuran_spec` also gives
  the sharper bound: all elements are below (2K−1)p.

## Not formalized

Section 4 (the BEEP2H/LISTEN2H specification, Algorithms 1–3, Remark 1, Lemma 9, Theorem 10, Lemma 11,
Theorem 12, Remark 2), Section 5 (2-hop desynchronization, a probabilistic algorithm and w.h.p. bounds) and
Section 6 (local message broadcast). The O(·) claims in the introduction were not formalized either.
