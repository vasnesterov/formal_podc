import Papers.PODC2026.LocalComputable.Separation

/-!
# A toy separation family (non-vacuity of `SepFamily`)

To check that the hypotheses of the abstract Lemma 4.17 (`Model.SepFamily`) are satisfiable, we
build a small instance: the network `(x, K)` is a path of `K + 1` nodes whose node `j` holds the
state of program `x` after `j` steps (`Code.evaln j x 0`); the problem asks node `0` to output
the result bit of `x` if `x` halts within `K` steps. Node `0`'s radius-`t` view consists of the
first `min t K + 1` entries and of whether it has reached the end of the path.

Unlike the paper's LCL, the trace is *promised* (not locally certified), and all networks have
this form; this is not a formalization of the paper's `Π`, only of the separation mechanism.
In this model:

* an uncomputable algorithm with locality `0` solves the problem (node `0` consults the
  halting oracle), `toy_uncomputable_solves`;
* every computable algorithm needs locality `T(n) ≥ n - 1` for all `n ≥ 1`
  (`toy_computable_lower`), via `exists_far_of_computable`.
-/

namespace LocalComputable

open Computable
open Nat.Partrec (Code)

/-- The first `m + 1` states of program `x` on input `0`. -/
def trace (x : Code) (m : ℕ) : List (Option ℕ) :=
  (List.range (m + 1)).map fun j => Code.evaln j x 0

theorem trace_length (x : Code) (m : ℕ) : (trace x m).length = m + 1 := by simp [trace]

/-- The toy model: networks `(x, K)` with `K + 1` nodes. -/
def toyModel : Model (Code × ℕ) (ℕ × Code × List (Option ℕ) × Bool) where
  size G := G.2 + 1
  view G v t := (v, G.1, trace G.1 (min t G.2), decide (G.2 ≤ t))
  restrict := by
    rintro ⟨x, K⟩ ⟨x', K'⟩ v v' t s hst h
    simp only [Prod.mk.injEq, decide_eq_decide] at h ⊢
    obtain ⟨rfl, rfl, htr, hfl⟩ := h
    have hlen : min t K = min t K' := by
      have := congrArg List.length htr
      simp only [trace_length] at this
      omega
    have hs : min s K = min s K' := by omega
    exact ⟨rfl, rfl, by rw [hs], by omega⟩

/-- The toy problem: node `0` outputs the result bit of `x` if `x` halts within `K` steps. -/
def toyP : toyModel.Problem Bool := fun G lab =>
  ∀ m, Code.evaln G.2 G.1 0 = some m → lab ⟨0, Nat.succ_pos _⟩ = (m != 0)

/-- The toy problem is a separation family. -/
def toyFamily : toyModel.SepFamily toyP where
  inst x K := (x, K)
  node _ _ := 0
  node_lt _ K := Nat.succ_pos K
  bit := id
  depth _ r := r + 1
  le_depth _ r := Nat.le_succ r
  depth_mono _ _ _ h := Nat.succ_le_succ h
  forced x r hr := by
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp (Part.eq_some_iff.mp hr)
    refine ⟨k, fun K hK lab hP => hP r (Code.evaln_mono hK hk)⟩
  stable x r K K' h1 h2 := by
    simp only [toyModel, Prod.mk.injEq, true_and]
    refine ⟨by rw [show min r K = r by omega, show min r K' = r by omega], ?_⟩
    simp only [decide_eq_decide]
    omega

/-- The toy views are computable. -/
theorem toy_view_computable : Computable fun p : (Code × ℕ) × ℕ × ℕ =>
    toyModel.view p.1 p.2.1 p.2.2 := by
  have htr : Primrec fun p : Code × ℕ => trace p.1 p.2 := by
    unfold trace
    exact Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
      (Code.primrec_evaln.comp (Primrec.pair (Primrec.pair Primrec.snd
        (Primrec.fst.comp Primrec.fst)) (Primrec.const 0))).to₂
  refine (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.pair (Primrec.fst.comp
    Primrec.fst) (Primrec.pair (htr.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.nat_min.comp (Primrec.snd.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))))
      (Primrec.nat_le.decide.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))))).to_comp

/-- In uncomputable-LOCAL the toy problem is solvable with locality `0` (halting oracle). -/
theorem toy_uncomputable_solves :
    ∃ B : Alg (ℕ × Code × List (Option ℕ) × Bool) Bool, toyModel.Solves toyP B fun _ => 0 := by
  classical
  refine ⟨fun w _ => some (decide (∃ m, Code.eval w.2.1 0 = Part.some m ∧ m ≠ 0)), ?_⟩
  rintro ⟨x, K⟩
  refine ⟨fun _ => decide (∃ m, Code.eval x 0 = Part.some m ∧ m ≠ 0), fun v => rfl, ?_⟩
  intro m hm
  have hm' : Code.eval x 0 = Part.some m := Part.eq_some_iff.mpr (Code.evaln_sound hm)
  by_cases h0 : m = 0
  · subst h0
    simp only [bne_self_eq_false, decide_eq_false_iff_not, not_exists, not_and]
    intro m' hm'' hne
    rw [hm'] at hm''
    exact hne (Part.some_injective hm'').symm
  · have : (m != 0) = true := by simpa using h0
    rw [this, decide_eq_true_eq]
    exact ⟨m, hm', h0⟩

/-- In computable-LOCAL the toy problem needs locality `T(n) ≥ n - 1` for every `n ≥ 1`. -/
theorem toy_computable_lower {A : Alg (ℕ × Code × List (Option ℕ) × Bool) Bool}
    (hA : Computable₂ A) {T : ℕ → ℕ} (hsol : toyModel.Solves toyP A T) :
    ∀ n, 1 ≤ n → n - 1 ≤ T n := by
  obtain ⟨x, hx⟩ := toyModel.exists_far_of_computable toyFamily toy_view_computable
    (pair fst snd) (const 0) (succ.comp snd).to₂ Computable.id hA hsol
  intro n hn
  have := hx (n - 1)
  simp only [toyFamily, toyModel] at this
  rw [show n - 1 + 1 = n by omega] at this
  omega

end LocalComputable
