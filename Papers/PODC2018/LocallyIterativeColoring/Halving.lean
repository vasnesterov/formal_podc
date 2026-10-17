import Cslib.Computability.Distributed.Local.Identifiers
import Mathlib

/-!
# One-bit AG halving reduction (Section 3.2 of [BEG18])

Barenboim, Elkin, Goldenberg, *Locally-Iterative Distributed (Δ+1)-Coloring below
Szegedy–Vishwanathan Barrier*, PODC 2018 (arXiv 1712.00285v2), Section 3.2, Algorithm 2.

Colours are pairs `⟨a, b⟩` with `a ∈ {0, 1}` and `b ∈ ℤ_q`; here `q` is an arbitrary positive
integer (no primality is needed). We encode `a` as a `Bool`: `true` stands for `a = 1` (a
*working* vertex) and `false` for `a = 0` (a *final* vertex). In every round a working vertex
`⟨1, b⟩` becomes final `⟨0, b⟩` if no neighbour has colour `⟨0, b⟩`, and moves to `⟨1, b + 1⟩`
otherwise; final vertices keep their colour.

## Main results

* `BEG18.Halving.isProper_run` — **Lemma 3.7**: a proper colouring stays proper in every round
  (for every `q`, with no assumption on `Δ` or on the number of colours).
* `BEG18.Halving.run_final` — **Lemma 3.8**: if all degrees are `≤ Δ` and `Δ + 1 ≤ q`, then after
  `Δ + 1` rounds every vertex is final (from an arbitrary, not even proper, initial colouring).
* `BEG18.Halving.halvingNat_run` — the halving step on `ℕ`-colours: a proper colouring with colours
  `< 2q` (encoded as `c ↦ ⟨⌊c/q⌋, c mod q⟩`) becomes a proper colouring with colours `< q` after
  `Δ + 1` rounds, provided `Δ + 1 ≤ q`.
* `BEG18.Halving.iterHalving_run` — core of **Corollary 3.9**: iterating `s` halving phases
  (`q_i = max ⌈k_i/2⌉ (Δ + 1)`) turns a proper colouring with `k ≤ 2^s (Δ + 1)` colours into a proper
  `(Δ + 1)`-colouring in `(Δ + 1)·s` rounds.
-/

namespace BEG18

open Cslib.LocallyIterative Finset

namespace Halving

variable {V : Type*} {G : SimpleGraph V} {q : ℕ}

open Classical in
/-- One round of Algorithm 2 of [BEG18] (one-bit AG halving reduction) at a vertex with colour `x`
whose neighbours have the set of colours `N`. -/
noncomputable def step (x : Bool × ZMod q) (N : Set (Bool × ZMod q)) : Bool × ZMod q :=
  if x.1 then (if (false, x.2) ∈ N then (true, x.2 + 1) else (false, x.2)) else x

/-- Algorithm 2 of [BEG18] as a (round-independent) locally-iterative algorithm. -/
noncomputable def algorithm (q : ℕ) : Algorithm (Bool × ZMod q) := Algorithm.ofStep step

/-- The key step of Lemma 3.7: adjacent vertices with distinct colours get distinct colours. -/
theorem step_ne {x y : Bool × ZMod q} {Nx Ny : Set (Bool × ZMod q)} (hy : y ∈ Nx) (hx : x ∈ Ny)
    (hne : x ≠ y) : step x Nx ≠ step y Ny := by
  obtain ⟨_ | _, bx⟩ := x <;> obtain ⟨_ | _, by'⟩ := y <;>
    simp only [step, Bool.false_eq_true, ite_false, ite_true] <;> try split_ifs
  all_goals intro e; simp only [Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false, false_and,
    add_left_inj, true_and] at e
  all_goals subst e; contradiction

theorem isProper_step {c : V → Bool × ZMod q} (hc : IsProper G c) :
    IsProper G (fun v => step (c v) (nbrColors G c v)) := fun _ _ huv =>
  step_ne (mem_nbrColors_of_adj c huv) (mem_nbrColors_of_adj c huv.symm) (hc huv)

/-- **Lemma 3.7 of [BEG18].** Algorithm 2 keeps a proper colouring proper in every round. -/
theorem isProper_run {c₀ : V → Bool × ZMod q} (h₀ : IsProper G c₀) (t : ℕ) :
    IsProper G ((algorithm q).run G c₀ t) :=
  Algorithm.run_induction (G := G) _ c₀ h₀
    (fun _ h => by rw [Algorithm.run_succ]; exact isProper_step h) t

/-! ### Lemma 3.8: every vertex is final after `Δ + 1` rounds -/

section Termination

variable (c₀ : V → Bool × ZMod q)

/-- A final vertex keeps its colour. -/
theorem run_succ_of_final {t : ℕ} {v : V} (h : ((algorithm q).run G c₀ t v).1 = false) :
    (algorithm q).run G c₀ (t + 1) v = (algorithm q).run G c₀ t v := by
  rw [Algorithm.run_succ_apply]
  show step _ _ = _
  simp [step, h]

theorem run_of_final_of_le {t s : ℕ} {v : V} (h : ((algorithm q).run G c₀ t v).1 = false)
    (hts : t ≤ s) : (algorithm q).run G c₀ s v = (algorithm q).run G c₀ t v :=
  Nat.eq_of_le_of_stable (x := fun s => (algorithm q).run G c₀ s v) (P := fun x => x.1 = false)
    (fun _ => run_succ_of_final c₀) h hts

/-- A vertex that is still working after round `t + 1` was working after round `t`, its second
coordinate increased by one, and some neighbour had the final colour `⟨0, b_v⟩`. -/
theorem run_succ_of_working {t : ℕ} {v : V}
    (h : ((algorithm q).run G c₀ (t + 1) v).1 = true) :
    ((algorithm q).run G c₀ t v).1 = true ∧
      ((algorithm q).run G c₀ (t + 1) v).2 = ((algorithm q).run G c₀ t v).2 + 1 ∧
      ∃ u, G.Adj v u ∧ (algorithm q).run G c₀ t u = (false, ((algorithm q).run G c₀ t v).2) := by
  rw [Algorithm.run_succ_apply] at h ⊢
  simp only [algorithm, Algorithm.ofStep, step] at h ⊢
  split_ifs at h ⊢ with h1 h2 <;> simp_all [mem_nbrColors]

/-- While a vertex is working, its second coordinate after `t` rounds is `b_v(0) + t`. -/
theorem run_of_working {t : ℕ} {v : V} (h : ((algorithm q).run G c₀ t v).1 = true) :
    ∀ s ≤ t, ((algorithm q).run G c₀ s v).1 = true ∧
      ((algorithm q).run G c₀ s v).2 = (c₀ v).2 + s := by
  induction t with
  | zero => intro s hs; obtain rfl := Nat.le_zero.mp hs; simpa using h
  | succ t ih =>
    obtain ⟨h1, h2, -⟩ := run_succ_of_working c₀ h
    intro s hs
    rcases Nat.of_le_succ hs with hs | rfl
    · exact ih h1 s (by omega)
    · refine ⟨h, ?_⟩
      rw [h2, (ih h1 t le_rfl).2]
      push_cast; ring

variable [G.LocallyFinite] {Δ : ℕ}

/-- **Lemma 3.8 of [BEG18].** If all degrees are at most `Δ` and `Δ + 1 ≤ q`, then after `Δ + 1`
rounds of Algorithm 2 every vertex has a final colour `⟨0, b⟩`. (No properness of the initial
colouring is needed.) -/
theorem run_final (hΔ : ∀ v, G.degree v ≤ Δ) (hq : Δ + 1 ≤ q) (v : V) :
    ((algorithm q).run G c₀ (Δ + 1) v).1 = false := by
  classical
  by_contra hv
  rw [Bool.not_eq_false] at hv
  have hw := run_of_working c₀ hv
  -- in every round `t ≤ Δ` some neighbour has the final colour `⟨0, b_v(0) + t⟩`
  have hblock : ∀ t ∈ range (Δ + 1), ∃ u ∈ G.neighborFinset v,
      (algorithm q).run G c₀ t u = (false, (c₀ v).2 + t) := by
    intro t ht
    rw [mem_range] at ht
    obtain ⟨-, -, u, hu, hut⟩ := run_succ_of_working c₀ (hw (t + 1) ht).1
    exact ⟨u, (G.mem_neighborFinset v u).2 hu, by rw [hut, (hw t ht.le).2]⟩
  -- each neighbour blocks at most one round
  have hone : ∀ u ∈ G.neighborFinset v,
      ((range (Δ + 1)).filter fun t =>
        (algorithm q).run G c₀ t u = (false, (c₀ v).2 + t)).card ≤ 1 := by
    intro u _
    rw [Finset.card_le_one]
    intro t ht t' ht'
    simp only [mem_filter, mem_range] at ht ht'
    have key : ∀ {t t'}, t < Δ + 1 → t' < Δ + 1 →
        (algorithm q).run G c₀ t u = (false, (c₀ v).2 + t) →
        (algorithm q).run G c₀ t' u = (false, (c₀ v).2 + t') → t ≤ t' → t = t' := by
      intro t t' ht ht' e e' hle
      have := run_of_final_of_le c₀ (by rw [e]) hle
      rw [this, e, Prod.mk.injEq, add_right_inj, ZMod.natCast_eq_natCast_iff',
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e'
      exact e'.2
    rcases le_total t t' with hle | hle
    · exact key ht.1 ht'.1 ht.2 ht'.2 hle
    · exact (key ht'.1 ht.1 ht'.2 ht.2 hle).symm
  have hsub : range (Δ + 1) ⊆ (G.neighborFinset v).biUnion
      fun u => (range (Δ + 1)).filter fun t =>
        (algorithm q).run G c₀ t u = (false, (c₀ v).2 + t) := by
    intro t ht
    obtain ⟨u, hu, hut⟩ := hblock t ht
    exact mem_biUnion.2 ⟨u, hu, mem_filter.2 ⟨ht, hut⟩⟩
  have := (card_le_card hsub).trans card_biUnion_le
  have := this.trans (sum_le_sum hone)
  simp only [card_range, sum_const, smul_eq_mul, mul_one,
    SimpleGraph.card_neighborFinset_eq_degree] at this
  have := hΔ v
  omega

/-- After `Δ + 1` rounds every vertex stays final in all later rounds. -/
theorem run_final_of_le (hΔ : ∀ v, G.degree v ≤ Δ) (hq : Δ + 1 ≤ q) {t : ℕ} (ht : Δ + 1 ≤ t)
    (v : V) : ((algorithm q).run G c₀ t v).1 = false := by
  rw [run_of_final_of_le c₀ (run_final c₀ hΔ hq v) ht, run_final c₀ hΔ hq v]

end Termination

/-! ### The halving step on natural-number colours -/

/-- The paper's encoding of a pair `⟨a, b⟩` as the colour `a·q + b`. -/
def encode (q : ℕ) (x : Bool × ZMod q) : ℕ := (if x.1 then q else 0) + x.2.val

/-- The paper's decoding of a colour `c < 2q` as the pair `⟨⌊c/q⌋, c mod q⟩`. -/
def decode (q : ℕ) (c : ℕ) : Bool × ZMod q := (decide (q ≤ c), (c : ZMod q))

theorem decode_encode [NeZero q] (x : Bool × ZMod q) : decode q (encode q x) = x := by
  obtain ⟨_ | _, b⟩ := x <;> simp [encode, decode, ZMod.val_lt]

theorem encode_decode {c : ℕ} (hc : c < 2 * q) : encode q (decode q c) = c := by
  simp only [encode, decode, decide_eq_true_eq, ZMod.val_natCast]
  split_ifs with h
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; simp

/-- Algorithm 2 of [BEG18] on colours `c ∈ ℕ`, each colour `c < 2q` being read as the pair
`⟨⌊c/q⌋, c mod q⟩` and a pair `⟨a, b⟩` being written back as `a·q + b`. -/
noncomputable def halvingNat (q : ℕ) : Algorithm ℕ := (algorithm q).comap (encode q) (decode q)

variable [G.LocallyFinite] {Δ : ℕ}

/-- **Lemmas 3.7 and 3.8 of [BEG18]** on natural-number colours: if all degrees are at most `Δ`,
`Δ + 1 ≤ q`, and `c₀` is a proper colouring with colours `< 2q` (the paper: a proper
`k`-colouring with `k ≥ 2Δ + 2` and `q = ⌈k/2⌉`), then after `Δ + 1` rounds of Algorithm 2 the
colouring is proper and uses only the colours `0, …, q - 1`. -/
theorem halvingNat_run (hΔ : ∀ v, G.degree v ≤ Δ) (hq : Δ + 1 ≤ q) {c₀ : V → ℕ}
    (h₀ : IsProper G c₀) (hc₀ : ∀ v, c₀ v < 2 * q) :
    IsProper G ((halvingNat q).run G c₀ (Δ + 1)) ∧ ∀ v, (halvingNat q).run G c₀ (Δ + 1) v < q := by
  have : NeZero q := ⟨by omega⟩
  have hc : encode q ∘ (decode q ∘ c₀) = c₀ := funext fun v => encode_decode (hc₀ v)
  have hrun := Algorithm.run_comap (G := G) (algorithm q) decode_encode (decode q ∘ c₀) (Δ + 1)
  rw [hc] at hrun
  rw [halvingNat, hrun]
  refine ⟨?_, fun v => ?_⟩
  · rw [isProper_comp_iff (Function.LeftInverse.injective decode_encode)]
    refine isProper_run (fun u v huv e => h₀ huv ?_) _
    have := congrArg (encode q) e
    simpa only [Function.comp_apply, encode_decode (hc₀ u), encode_decode (hc₀ v)] using this
  · simp only [Function.comp_apply, encode, run_final _ hΔ hq v, Bool.false_eq_true, ite_false,
      zero_add]
    exact ZMod.val_lt _

/-! ### Iterated halving (the core of Corollary 3.9) -/

/-- `s` phases of halving, each of `Δ + 1` rounds, starting from colours `< k`: phase `i` halves the
current palette size `k_i` to `q_i = max ⌈k_i / 2⌉ (Δ + 1)`. -/
noncomputable def iterHalving (Δ : ℕ) : ℕ → ℕ → Algorithm ℕ
  | 0, _ => Algorithm.ofStep fun x _ => x
  | s + 1, k =>
    (halvingNat (max ((k + 1) / 2) (Δ + 1))).seq (Δ + 1)
      (iterHalving Δ s (max ((k + 1) / 2) (Δ + 1)))

/-- **Corollary 3.9 of [BEG18] (core).** If all degrees are at most `Δ` and `c₀` is a proper
colouring with colours `< k`, where `k ≤ 2^s (Δ + 1)`, then `s` halving phases, i.e. `(Δ + 1)·s`
rounds, produce a proper colouring with colours `< Δ + 1`. -/
theorem iterHalving_run (hΔ : ∀ v, G.degree v ≤ Δ) (s : ℕ) {k : ℕ} (hk : k ≤ 2 ^ s * (Δ + 1))
    {c₀ : V → ℕ} (h₀ : IsProper G c₀) (hc₀ : ∀ v, c₀ v < k) :
    IsProper G ((iterHalving Δ s k).run G c₀ ((Δ + 1) * s)) ∧
      ∀ v, (iterHalving Δ s k).run G c₀ ((Δ + 1) * s) v < Δ + 1 := by
  induction s generalizing k c₀ with
  | zero =>
    have hr : ∀ t, (iterHalving Δ 0 k).run G c₀ t = c₀ := fun t =>
      (Algorithm.run_ofStep G _ c₀ t).trans (Function.iterate_fixed rfl t)
    rw [hr]
    exact ⟨h₀, fun v => by simp at hk; exact (hc₀ v).trans_le hk⟩
  | succ s ih =>
    set q' := max ((k + 1) / 2) (Δ + 1) with hq'
    have h1 := halvingNat_run (q := q') hΔ (le_max_right _ _) h₀ (fun v => by
      have := hc₀ v; have := le_max_left ((k + 1) / 2) (Δ + 1); omega)
    have hpow : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    have hq'k : q' ≤ 2 ^ s * (Δ + 1) := by
      rw [pow_succ] at hk
      refine max_le ?_ (by nlinarith)
      have : k ≤ 2 * (2 ^ s * (Δ + 1)) := by linarith
      omega
    have := ih hq'k h1.1 h1.2
    rwa [show (Δ + 1) * (s + 1) = (Δ + 1) + (Δ + 1) * s by ring, iterHalving,
      Algorithm.run_seq_add]

end Halving

end BEG18
