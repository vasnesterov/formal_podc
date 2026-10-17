import Papers.PODC2026.LocalComputable.ComputableEquiv
import Mathlib.Computability.PartrecCode
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The logical core of the separation (Lemmas 4.17, 4.18)

Section 4 constructs an LCL `Π = Π_tree ⊗ Π_row ⊗ Π_grid ⊗ Π_Turing ⊗ Π_consensus` on
"growing grids" and shows that computable-LOCAL needs locality `Ω(√n)` for it, while
uncomputable-LOCAL solves it in `O(log n)` rounds. We do **not** formalize the LCL (trees, rows,
grids, the Turing machine encoding). We formalize the diagonalization argument of Lemma 4.17
for an abstract *separation family*: instances `G_K(x)` (program `x`, `K` layers) with a node in
the layer holding `x`, such that

* (`forced`) if `x` halts with result `r`, then for all large `K` every valid labelling of
  `G_K(x)` outputs the bit `r ≠ 0` at the node (the halting configuration lies in the grid and the
  consensus constraints propagate it);
* (`stable`) the radius-`r` view of the node is the same in `G_K(x)` and `G_{K'}(x)` once
  `K, K' ≥ depth x r` (the node does not see the bottom of the grid);

with `inst`, `node`, `depth` computable. Programs are Mathlib's `Nat.Partrec.Code`, run on input
`0` (the universal machine `U` of the paper is `Code.eval`).

* `diagonalizer` (**Lemma 4.18**): for every computable total predictor `h` there is a program
  that halts with the opposite bit (Kleene's recursion theorem plays the role of the quine).
* `exists_far_of_computable` (**Lemma 4.17**, abstract): a computable algorithm that solves the
  problem must, on some `x`, stop beyond `depth` for every `K`.
* `not_littleO_sqrt`: with the size bound `|G_K(x)| ≤ C (K+1)²` and `depth x r ≤ r + D x`, its
  locality is not `o(√n)`.
-/

namespace LocalComputable

open Computable
open Nat.Partrec (Code)

/-- **Lemma 4.18** (diagonalizer). For every computable predictor `h` of the output bit of
programs, there is a program `c` that halts on input `0` with output `0` if `h c` predicts
"accept" (`true`) and `1` otherwise. -/
theorem diagonalizer {h : Code → Bool} (hh : Computable h) :
    ∃ c : Code, Code.eval c 0 = Part.some (if h c then 0 else 1) := by
  have hf : Computable₂ fun (c : Code) (_ : ℕ) => bif h c then 0 else 1 :=
    ((cond hh (const 0) (const 1)).comp fst).to₂
  obtain ⟨c, hc⟩ := Code.fixed_point₂ hf.partrec₂
  refine ⟨c, ?_⟩
  rw [hc]
  cases h c <;> rfl

variable {Net View Out : Type*}

namespace Model

variable {M : Model Net View}

theorem out_isSome_of {A : Alg View Out} {G : Net} {v r : ℕ} {b : Out}
    (h : A (M.view G v r) r = some b) : (M.out A G v r).isSome := by
  unfold out
  rw [Option.isSome_iff_exists]
  by_contra hc
  push Not at hc
  have : (List.range (r + 1)).findSome? (fun t => A (M.view G v t) t) = none := by
    cases e : (List.range (r + 1)).findSome? (fun t => A (M.view G v t) t) with
    | none => rfl
    | some a => exact absurd e (hc a)
  rw [List.findSome?_eq_none_iff] at this
  have := this r (List.mem_range.mpr (Nat.lt_succ_self r))
  rw [h] at this
  simp at this

theorem out_unique {A : Alg View Out} {G : Net} {v r r' : ℕ} {a b : Out}
    (h : M.out A G v r = some a) (h' : M.out A G v r' = some b) : a = b := by
  rcases le_total r r' with hr | hr
  · rw [out_mono A h hr] at h'; exact Option.some_injective _ h'
  · rw [out_mono A h' hr] at h; exact (Option.some_injective _ h).symm

variable (M)

/-- An abstract *separation family* for the problem `P` (see the module docstring). -/
structure SepFamily (P : M.Problem Out) where
  /-- the instance `G_K(x)` -/
  inst : Code → ℕ → Net
  /-- a node in the layer holding the input `x` -/
  node : Code → ℕ → ℕ
  node_lt : ∀ x K, node x K < M.size (inst x K)
  /-- the output bit encoded by a label -/
  bit : Out → Bool
  /-- `K ≥ depth x r` layers suffice for the radius-`r` view of the node to be stable -/
  depth : Code → ℕ → ℕ
  le_depth : ∀ x r, r ≤ depth x r
  depth_mono : ∀ x, Monotone (depth x)
  /-- validity forces the result of a halting program -/
  forced : ∀ x r, Code.eval x 0 = Part.some r → ∃ K₀, ∀ K ≥ K₀,
    ∀ lab, P (inst x K) lab → bit (lab ⟨node x K, node_lt x K⟩) = (r != 0)
  /-- the node cannot see the bottom of the grid -/
  stable : ∀ x r K K', depth x r ≤ K → K ≤ K' →
    M.view (inst x K) (node x K) r = M.view (inst x K') (node x K') r

variable [Primcodable Net] [Primcodable View] [Primcodable Out]

/-- Outputs of a computable algorithm are computable. -/
theorem out_computable (hview : Computable fun p : Net × ℕ × ℕ => M.view p.1 p.2.1 p.2.2)
    {A : Alg View Out} (hA : Computable₂ A) :
    Computable fun q : Net × ℕ × ℕ => M.out A q.1 q.2.1 q.2.2 := by
  unfold out
  refine computable_list_findSome? (Primrec.list_range.to_comp.comp (succ.comp (snd.comp snd))) ?_
  exact (hA.comp (hview.comp (pair (fst.comp fst) (pair (fst.comp (snd.comp fst)) snd))) snd).to₂

/-- **Lemma 4.17** (abstract form). If a *computable* algorithm `A` solves `P` with locality `T`,
then for some program `x` and every `K`, the node of `G_K(x)` may look beyond depth `K`, i.e.
`K < depth x (T |G_K(x)|)`. (Otherwise one could compute, for every `x`, the bit that `A`
outputs at the node of a deep enough instance, and the diagonalizer defeats it.) -/
theorem exists_far_of_computable {P : M.Problem Out} (F : M.SepFamily P)
    (hview : Computable fun p : Net × ℕ × ℕ => M.view p.1 p.2.1 p.2.2)
    (hinst : Computable₂ F.inst) (hnode : Computable₂ F.node) (hdepth : Computable₂ F.depth)
    (hbit : Computable F.bit)
    {T : ℕ → ℕ} {A : Alg View Out} (hA : Computable₂ A) (hsol : M.Solves P A T) :
    ∃ x, ∀ K, K < F.depth x (T (M.size (F.inst x K))) := by
  classical
  by_contra hcon
  push Not at hcon
  -- `goodK x K`: some radius `r` with `depth x r ≤ K` already has a non-`⊥` value
  let goodK : Code → ℕ → Bool := fun x K => (List.range (K + 1)).any fun r =>
    decide (F.depth x r ≤ K) && (A (M.view (F.inst x K) (F.node x K) r) r).isSome
  have hex : ∀ x, ∃ K, goodK x K = true := by
    intro x
    obtain ⟨K, hK⟩ := hcon x
    obtain ⟨lab, hlab, -⟩ := hsol (F.inst x K)
    have hs := hlab ⟨F.node x K, F.node_lt x K⟩
    unfold out at hs
    obtain ⟨r, hr, hrs⟩ := List.exists_of_findSome?_eq_some hs
    have hr' : r ≤ T (M.size (F.inst x K)) := Nat.lt_succ_iff.mp (List.mem_range.mp hr)
    have hdr : F.depth x r ≤ K := (F.depth_mono x hr').trans hK
    refine ⟨K, List.any_eq_true.mpr ⟨r, List.mem_range.mpr ?_, ?_⟩⟩
    · exact Nat.lt_succ_of_le ((F.le_depth x r).trans hdr)
    · simp [hdr, hrs]
  have hgoodK : Computable₂ goodK := by
    refine Computable₂.mk ((computable_list_any (f := fun a : Code × ℕ => List.range (a.2 + 1))
      (p := fun a r => decide (F.depth a.1 r ≤ a.2) &&
        (A (M.view (F.inst a.1 a.2) (F.node a.1 a.2) r) r).isSome)
      (Primrec.list_range.to_comp.comp (succ.comp snd)) ?_).of_eq fun a => rfl)
    have h1 : Computable fun c : (Code × ℕ) × ℕ => decide (F.depth c.1.1 c.2 ≤ c.1.2) :=
      Primrec.nat_le.decide.to_comp.comp (hdepth.comp (fst.comp fst) snd) (snd.comp fst)
    have hv : Computable fun c : (Code × ℕ) × ℕ =>
        M.view (F.inst c.1.1 c.1.2) (F.node c.1.1 c.1.2) c.2 :=
      hview.comp (pair (hinst.comp (fst.comp fst) (snd.comp fst))
        (pair (hnode.comp (fst.comp fst) (snd.comp fst)) snd))
    have h2 : Computable fun c : (Code × ℕ) × ℕ =>
        (A (M.view (F.inst c.1.1 c.1.2) (F.node c.1.1 c.1.2) c.2) c.2).isSome :=
      Primrec.option_isSome.to_comp.comp (hA.comp hv snd)
    exact (Primrec.and.to_comp.comp h1 h2).to₂
  let Kx : Code → ℕ := fun x => Nat.find (hex x)
  have hKx : Computable Kx := computable_nat_find hgoodK hex
  -- the predictor: the bit output by `A` at the node of `G_{Kx x}(x)`
  let h : Code → Bool := fun x =>
    ((M.out A (F.inst x (Kx x)) (F.node x (Kx x)) (Kx x)).map F.bit).getD false
  have hh : Computable h := by
    refine option_getD (option_map ((out_computable M hview hA).comp
      (pair (hinst.comp .id hKx) (pair (hnode.comp .id hKx) hKx))) (hbit.comp snd).to₂)
      (const false)
  obtain ⟨c, hc⟩ := diagonalizer hh
  obtain ⟨K₀, hK₀⟩ := F.forced c _ hc
  -- the good radius for `c`
  have hg : goodK c (Kx c) = true := Nat.find_spec (hex c)
  simp only [goodK, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨r, -, hdr, hrs⟩ := hg
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hrs
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (out_isSome_of (M := M) hb)
  have hhc : h c = F.bit a := by
    simp only [h, out_mono A ha ((F.le_depth c r).trans hdr), Option.map_some, Option.getD_some]
  -- a deep instance
  let K := max K₀ (Kx c)
  have hview' := F.stable c r (Kx c) K hdr (le_max_right _ _)
  have haK : M.out A (F.inst c K) (F.node c K) r = some a := by
    rw [← out_congr A hview']; exact ha
  obtain ⟨lab, hlab, hP⟩ := hsol (F.inst c K)
  have hlabv := hlab ⟨F.node c K, F.node_lt c K⟩
  have hla : a = lab ⟨F.node c K, F.node_lt c K⟩ := out_unique haK hlabv
  have hforced := hK₀ K (le_max_left _ _) lab hP
  rw [← hla] at hforced
  rw [← hhc] at hforced
  cases hhcv : h c <;> simp [hhcv] at hforced

/-- **Lemma 4.17** (`Ω(√n)` form). If moreover `|G_K(x)| ≤ C (K+1)²` and
`depth x r ≤ r + D x`, then no computable algorithm with locality `T(n) = o(√n)` solves `P`. -/
theorem not_littleO_sqrt {P : M.Problem Out} (F : M.SepFamily P)
    (hview : Computable fun p : Net × ℕ × ℕ => M.view p.1 p.2.1 p.2.2)
    (hinst : Computable₂ F.inst) (hnode : Computable₂ F.node) (hdepth : Computable₂ F.depth)
    (hbit : Computable F.bit) (C : ℕ) (D : Code → ℕ)
    (hsize : ∀ x K, M.size (F.inst x K) ≤ C * (K + 1) ^ 2)
    (hD : ∀ x r, F.depth x r ≤ r + D x)
    {T : ℕ → ℕ} (hT : (fun n => (T n : ℝ)) =o[Filter.atTop] fun n => Real.sqrt n)
    {A : Alg View Out} (hA : Computable₂ A) : ¬ M.Solves P A T := by
  intro hsol
  obtain ⟨x, hx⟩ := M.exists_far_of_computable F hview hinst hnode hdepth hbit hA hsol
  -- eventually `T n ≤ √n / (2 (C+1))`
  have hε : (0 : ℝ) < 1 / (2 * (C + 1)) := by positivity
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (hT.bound hε)
  -- a bound for small `n`
  let M₀ := ((Finset.range n₀).image T).sup id
  have hsmall : ∀ n < n₀, T n ≤ M₀ := fun n hn =>
    Finset.le_sup (f := id) (Finset.mem_image_of_mem T (Finset.mem_range.mpr hn))
  -- choose `K` large
  let K := 2 * (M₀ + D x) + 1
  have hK := hx K
  have hTK : T (M.size (F.inst x K)) + D x ≤ K := by
    by_cases hn : M.size (F.inst x K) < n₀
    · have := hsmall _ hn; omega
    · push Not at hn
      have h1 := hn₀ _ hn
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Nat.abs_cast] at h1
      have hs : (M.size (F.inst x K) : ℝ) ≤ C * ((K : ℝ) + 1) ^ 2 := by exact_mod_cast hsize x K
      have hsq : Real.sqrt (M.size (F.inst x K)) ≤ (C + 1) * ((K : ℝ) + 1) := by
        rw [Real.sqrt_le_left (by positivity)]
        calc (M.size (F.inst x K) : ℝ) ≤ C * ((K : ℝ) + 1) ^ 2 := hs
          _ ≤ ((C + 1) * ((K : ℝ) + 1)) ^ 2 := by
            have : (C : ℝ) ≤ ((C : ℝ) + 1) ^ 2 := by nlinarith
            nlinarith [sq_nonneg ((K : ℝ) + 1)]
      have h2 : (T (M.size (F.inst x K)) : ℝ) ≤ ((K : ℝ) + 1) / 2 := by
        calc (T (M.size (F.inst x K)) : ℝ) ≤ 1 / (2 * (C + 1)) *
              Real.sqrt (M.size (F.inst x K)) := h1
          _ ≤ 1 / (2 * (C + 1)) * ((C + 1) * ((K : ℝ) + 1)) := by gcongr
          _ = ((K : ℝ) + 1) / 2 := by field_simp
      have h3 : 2 * T (M.size (F.inst x K)) ≤ K + 1 := by
        have : (2 * T (M.size (F.inst x K)) : ℝ) ≤ K + 1 := by linarith
        exact_mod_cast this
      omega
  have := hD x (T (M.size (F.inst x K)))
  omega

end Model

end LocalComputable
