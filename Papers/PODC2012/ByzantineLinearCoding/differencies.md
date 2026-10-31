# Differences between the formalization and the paper

Paper: Liang–Vaidya, PODC 2012, arXiv 1106.1845v3. Verdict rules from `verdicts.md`.

## Statement-level issues in the paper

1. **Lemma 1 is false for small fields** (`lemma_1_false_small_field`). The bound
   `(1 − (n−f−1)/2^{L/ρ_k})^{ρ_k}` exceeds 1 when `2^{L/ρ_k} < (n−f−1)/2` and `ρ_k` is even. It equals 1 at
   `n−f−1 = 4`, `ρ_k = 2`, `L = 2` (GF(2)), for `H = K_5` with capacities 2. The all-zero coding is singular. The
   proof multiplies inequalities with a possibly negative factor.
   - Rule R4 (implied assumption), supported by R2 (parameter corner outside the interesting range). Classified
     ⚠️. The paper fixes the large-`L` regime explicitly: "The algorithm is intended to be used for sufficiently
     large L" (Section 2); Theorem 1 adds "when L is large enough, 1 − 2^{−L/ρ_k}C(n,n−f)(n−f−1)ρ_k > 0"; (17)
     concludes "→ 1 as L → ∞". Lemma 1's only use (Appendix C.2: "invertible with non-zero probability") needs its
     bound to be positive, i.e. `2^{L/ρ_k} > n−f−1`, where the lemma is true. Outside the proved range
     (`2^{L/ρ_k} < n−f−1`) Theorem 1's bound is `≤ 0`, so no claim of the paper rests on the false range.
   - Borderline: the lemma says "for any `ρ_k ≤ U_k/2`" with no condition on `L`, and `n = 7, f = 2` is not a
     degenerate network (R2 alone would not excuse it). The excuse is the field size, which the paper takes large
     throughout. The repaired statement assumes `n−f−1 ≤ |F|` (`TreePacking.lemma_1`).
2. **Lemma 2 field size** (`lemma_2`). The paper draws the entries from `GF(2^{ρ_k})` and gives the bound
   `1 − w/2^{ρ_k}`. The intended field `GF(2^{L/ρ_k})` is evident from its use in (16) and from the last sentence of
   Appendix C.4, which concludes with the bound `1 − (n−f−1)/2^{L/ρ_k}` (checked on the rendered page). Rule R3 (typo, local fix):
   ⚠️. We prove `1 − w/|F|` for any finite field.

## Proof-level issues (true statements)

3. **Appendix C.3** (`c3_argument_insufficient`, `TreePacking.det_A_ne_zero`). The argument for `det A_q = ±1`
   uses only properties that a singular cycle-incidence matrix also has. Repaired via connectivity: `D·A_q = 0`
   forces `D` to be constant on tree edges, hence 0. We prove `det A_q ≠ 0` over any field, which is all that is
   needed. We do not prove `det = ±1`. Proof repair (🛠️).
4. **Appendix C.2** uses Lemma 1 to conclude that `det M_H` is a nonzero polynomial. That inference needs
   Lemma 1's bound to be positive, i.e. `|F| > n−f−1`. We instead evaluate at an explicit coding (`specialCoding`,
   block-diagonal `M̃_H`), which works for every field. We use plain Schwartz–Zippel (total degree) instead of
   Lemma 1 of [8]. Both give the same final bound. Routine.
5. **Section 5.1 / eq. (6).** The proof sets `ρ_k = U_k/2` and `ρ* = U_1/2`, which can be non-integers, while
   Algorithm 1 needs an integer `ρ_k` dividing `L`. Fixed by rescaling the time unit, which the paper allows.
   Recorded only; the throughput argument is formalized at the level of the real-valued time bound.

## Modelling choices and scope

6. **`ρ_k ≤ U_k/2` replaced by a packing hypothesis.** The paper derives `ρ_k` edge-disjoint undirected spanning
   trees in every `H̄`, `H ∈ Ω_k`, from `U_k ≥ 2ρ_k` via the Nash-Williams–Tutte theorem (its ref. [16]). We assume
   the packing (`TreePacking`) directly; the packing theorem is not formalized. Non-vacuity: `TreePacking.star`
   (stars) and `theorem_1_complete` (all capacities `≥ ρ`).
7. **Equality Check only.** Phases 1 and 3, the 1-bit Byzantine broadcasts and the evolution of `G_k` are not
   modelled.
   - `G_k` is an arbitrary capacity function `z`, with node set `V_k` and dispute relation `disp`.
   - The properties dispute control guarantees are built into the admissible faulty sets: removed nodes are
     faulty, and every dispute contains a faulty node.
   - `Correct` is (EC) in contrapositive form ("no fault-free node flags ⇒ all fault-free values equal").
8. **`Ω_k`** = `(n−f)`-subsets of `V_k` without disputed pairs (`Omega`); the subgraphs are the induced ones.
   `|Ω_k| ≤ C(n, n−f)` (`card_Omega_le`).
9. **Field.** Theorem 1 is proved for any finite field `F`, with bound `1 − C(n,n−f)(n−f−1)ρ/|F|`.
   `theorem_1_galois` specializes to `GaloisField 2 (L/ρ)` (`ρ ∣ L`, `L > 0`).
10. **`f < n/3`** is used only to ensure `n − f ≥ 2`, so that any two fault-free nodes lie in a common `H`.
11. **Theorem 2** (capacity upper bound) is not formalized. Theorem 3 is proved from its conclusion
    `C_BB ≤ min(γ*, 2ρ*)` as a hypothesis, together with `T_NAB = γ*ρ*/(γ*+ρ*)`.
12. **Eq. (6)/(24)–(28).** The time bound (24) `t(Q) ≤ Q(L/γ + L/ρ + a) + b` is a hypothesis
    (`throughput_eventually_ge`). The limits `Q → ∞` and then `L → ∞` are proved (`tendsto_throughput_Q`,
    `tendsto_throughput_L`). The paper's `T(G, L, A) = lim_Q` is replaced by an "eventually ≥ … − ε" statement,
    because the limit need not exist.
13. **`M̃_H` indexing.** Rows are `(non-root node i, coordinate p)` and columns `(tree edge r, tree q)`; this is a
    row/column permutation of the paper's `M_H`. Lemma 1 is stated for `M̃_H` (as in the paper) and for the
    abstract block matrix `blockM`.
