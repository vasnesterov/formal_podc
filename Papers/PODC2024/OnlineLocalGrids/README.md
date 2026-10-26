# 3-colouring grids in Online-LOCAL — PODC 2024

Yi-Jun Chang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, Yu-Cheng Yeh. *A Tight Lower Bound for
3-Coloring Grids in the Online-LOCAL Model.* PODC 2024. DOI
[10.1145/3662158.3662794](https://doi.org/10.1145/3662158.3662794). Formalized version: the conference version
(everything formalized here is fully proved there; full version arXiv
[2312.01384](https://arxiv.org/abs/2312.01384)).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** Theorem 1.1 (`Ω(log n)` for grids) and Theorem 1.3 (`Ω(√n)` for cylinders and
tori) are proved, with explicit constants, together with Lemmas 3.3–3.6. No proof step fails, but Theorem 1.3 as
stated omits that `√n` must be odd (the proof chooses `√n` odd); read as a bound for all large `n`, it is false
for even `√n`.

## Mistakes in the paper

1. **Theorem 1.3 omits the parity condition (imprecise statement; false if `Ω` is read "for all large `n`").** The
   theorem and the abstract claim locality `Ω(√n)` for 3-colouring `√n × √n` toroidal and cylindrical grids, with
   no condition on `n`. The proof picks `√n` odd; outside the proof, only §2.1 (odd-column cylinders/tori are not
   bipartite) and the closing remark of §3.3 (the `Ω(a)` bound for `a × b` grids needs `b` odd) mention parity. For even `√n` these graphs are bipartite, and
   the `O(log n)` Online-LOCAL algorithm for bipartite graphs (the one behind Corollary 1.2) applies, so `Ω(√n)`
   cannot hold for all `n`. The correct reading is "for `√n` odd" (or "infinitely often"); we prove the general
   `a × b` form with `b ≥ 3` odd (`theorem_1_3_cylinder`, `theorem_1_3_torus`).
2. **Implicit assumptions and imprecisions in the proofs (no step fails).**
   - *Re-embedding.* The adversary "adjusts how the discovered region fits into G". This is sound only if moved
     pieces stay at distance `≥ 2T+2` from everything else and keep their radius-`T` balls away from the grid
     border (translating a piece that touches the border changes its view). The paper leaves these margins,
     including all vertical ones, unstated.
   - *Lemma 3.6* only makes sense if the algorithm colours the revealed segment properly (the parity argument of
     Lemma 3.5 fails otherwise); we state it as "if properly coloured, then a row path with `|b| ≥ k` exists".
     Concatenating `P_{u,v}`, `P_{v,s}`, `P_{s,t}` silently requires reflecting the second piece so that both
     large `b`-values point the same way, and the paper never says where `P_{s,t}` is built before being moved.
   - *Theorem 1.1:* "simply reverse the direction of `P_{s,t}`" must be a reflection about the midpoint of its
     column range, so that `s` stays above `v` and `t` above `u`.
   - *Lemma 3.4* sums cells "inside" a simple cycle, implicitly using a Jordan curve theorem for grids. We avoid
     it with a potential function and get the stronger statement that every closed walk has `b`-value 0.
   - *Constants.* Region length `5^{k+1}T` in Lemma 3.6 can be `2^k(2T+3)`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (CSLib, `Cslib/Computability/Distributed/Local/OnlineLocal.lean`, following §2.2 of the paper).
- Deterministic algorithms `View ι → L`; the algorithm may depend on `n` and the host graph arbitrarily. The input
  is an identifier placement `pos : ι ≃ V` on the host grid/cylinder/torus and a reveal order listing every node
  once. When `vᵢ` is revealed the algorithm sees the subgraph induced by `B({v₁,…,vᵢ}, T)` with identifiers and
  the reveal sequence, and irrevocably labels `vᵢ`. Correct = proper for every placement and every order.
- The identifier space has exactly `n` elements (the paper allows `poly(n)`): this weakens the adversary, so the
  lower bounds are stronger. The adversary chooses only `pos` and the order; re-embedding is *derived* from an
  indistinguishability lemma (`label_eq_of_agreeOn`), not assumed.
- `T = 0` is allowed (the paper assumes `T ≥ 1`). Colours `Fin 3`, our `2` is the paper's `3`. Grids are Mathlib's
  `pathGraph`/`cycleGraph` box products.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 3.3; Lemma 3.4 (all closed walks); Lemma 3.5 | `aval_cell`, `bval_four_cycle`; `grid_bval_closed`; `bval_parity` | `Defs.lean`, `BValue.lean` |
| Lemma 3.6 | `lemma36` | `Lemma36.lean` |
| Theorem 1.1: `2^(4T+5)(2T+3) ≤ m` ⇒ no locality-`T` algorithm 3-colours the `m × m` grid | `theorem_1_1` | `Theorem11.lean` |
| Theorem 1.1, `Ω(log n)` form: correct ⇒ `log₂(m²) < 12T + 14` | `theorem_1_1_log` | `Theorem11.lean` |
| Theorem 1.3, cylinder (`a ≥ 4T+3`, `b ≥ 3` odd) / square | `theorem_1_3_cylinder`, `theorem_1_3_cylinder_square` | `Theorem13.lean` |
| Theorem 1.3, torus (`a ≥ 4T+4`, `b ≥ 3` odd) / square | `theorem_1_3_torus`, `theorem_1_3_torus_square` | `Theorem13.lean` |
| Corollary 1.4, Online-LOCAL part (`Θ(√n)`) | `torus_square_tight`, `cylinder_square_tight` | `NonVacuity.lean` |

**Not formalized.** Corollary 1.2 and the other-model parts of Corollary 1.4 (they need the `O(log n)` algorithm of
Akbari et al. and model simulations); Theorem 1.5 / Corollary 1.6 (only sketched); Theorems 1.8, 1.10 and
Corollaries 1.9, 1.11 (proved only in the full version).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Proper colourings are CSLib's `Cslib.LocallyIterative.IsProper` (re-exported as `IsProper`). Non-vacuity: the "see everything" algorithm is correct once radius-`T` balls cover the graph (`seeAll_colors` in
CSLib), so locality `2m` suffices on the `m × m` grid (`grid_bounds`) and `O(√n)` on square cylinders and tori,
making Theorem 1.3 tight up to constants.
