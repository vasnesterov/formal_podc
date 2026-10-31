import Papers.PODC2020.IntermediateValueLin.CountMin
import Mathlib.Tactic.FinCases

/-!
# Example 2 of Rinberg–Keidar: the concurrent CountMin sketch is not linearizable

Rinberg, Keidar, *Intermediate Value Linearizability: A Quantitative Correctness Criterion*,
PODC 2020, full version arXiv:2006.12889, Example 2 (Section 5).

Elements `a`, `b`, `e`; `d = w = 2`; hash functions (0-based) `h₀(a) = h₁(a) = 0`, `h₀(b) = 1`,
`h₁(b) = 0`, `h₀(e) = h₁(e) = 1` (the paper's `h₁(a) = h₂(a) = 1`, `h₁(b) = 2`, `h₂(b) = 1`; the
paper does not need `e`). The paper starts from the matrix `[[1, 4], [2, 3]]`; we reach it from
the all-zero matrix of Algorithm 1 by the sequential updates `a, b, e, e, e` of process `p`.
Then (`σ` = `example2`):

* `p` invokes `U = update(a)`, increments `c[0][0]` (to `2`) and stalls;
* `q` runs `Q₁ = query(a)`, reading `c[0][0] = 2`, `c[1][0] = 2`, and returns `2`;
* `q` runs `Q₂ = query(b)`, reading `c[0][1] = 4`, `c[1][0] = 2`, and returns `2`;
* `p` increments `c[1][0]` (to `3`) and `U` returns.

The paper lets the *same* process `p` invoke `U`, `Q₁` and `Q₂`; since `U` is still pending
this is not a well-formed history, so we use a second process `q` for the queries.

`example2_valid`: this is an execution of `pcm hEx`. `example2_not_lin`: it is not linearizable
with respect to `cmSpec hEx`: `Q₁` returning `2` forces `U` before `Q₁`, `Q₂` returning `2`
forces `Q₂` before `U`, while `Q₁` precedes `Q₂` in real time.
-/

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

namespace Podc.IntermediateValueLin

/-! ### Counting updates -/

namespace CM

section Counting

variable {E : Type} [DecidableEq E] {d w : ℕ} {P : Type} [DecidableEq P]

/-- `o` is an update that increments the cell `(i, j)`. -/
def hits (h : Fin d → E → Fin w) (i : Fin d) (j : Fin w) : CMOp E → Bool
  | .update x => decide (h i x = j)
  | .query _ => false

lemma runOps_apply (h : Fin d → E → Fin w) (c : Fin d → Fin w → ℕ) (os : List (CMOp E))
    (i : Fin d) (j : Fin w) :
    (cmSpec h).obj.runOps c os i j = c i j + os.countP (hits h i j) := by
  induction os generalizing c with
  | nil => rfl
  | cons o os ih =>
    rw [ObjSpec.runOps_cons, ih, List.countP_cons]
    cases o with
    | update x => by_cases hx : h i x = j <;> simp [hits, hx]; omega
    | query x => simp [hits]

/-- The matrix of a sequential history counts the updates hashing to each cell. -/
lemma cnt_eq_countP (h : Fin d → E → Fin w) (L : List (OpId P × CMOp E)) (i : Fin d)
    (j : Fin w) : cnt h L i j = L.countP (fun y => hits h i j y.2) := by
  rw [cnt, runOps_apply, List.countP_map]; simp; rfl

end Counting

section Lists

variable {K X : Type} [DecidableEq K]

lemma length_le_countP (A : List (K × X)) (pr : X → Bool) (S : List K) (hS : S.Nodup)
    (h : ∀ s ∈ S, ∃ y ∈ A, y.1 = s ∧ pr y.2 = true) :
    S.length ≤ A.countP (fun y => pr y.2) := by
  have hsub : S ⊆ (A.filter (fun y => pr y.2)).map Prod.fst := fun s hs => by
    obtain ⟨y, hy, rfl, hp⟩ := h s hs
    exact List.mem_map_of_mem (List.mem_filter.2 ⟨hy, hp⟩)
  refine (List.subperm_of_subset hS hsub).length_le.trans ?_
  simp [List.countP_eq_length_filter]

lemma countP_le_length (A : List (K × X)) (pr : X → Bool) (S : List K)
    (hA : (A.map Prod.fst).Nodup) (h : ∀ y ∈ A, pr y.2 = true → y.1 ∈ S) :
    A.countP (fun y => pr y.2) ≤ S.length := by
  have hnd : ((A.filter (fun y => pr y.2)).map Prod.fst).Nodup :=
    hA.sublist ((List.filter_sublist).map _)
  have hsub : (A.filter (fun y => pr y.2)).map Prod.fst ⊆ S := fun s hs => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hs
    obtain ⟨hy, hp⟩ := List.mem_filter.1 hy
    exact h y hy hp
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa [List.countP_eq_length_filter] using this

lemma mem_left_of_sublist {l A B : List K} {x y : K} (hl : l = A ++ y :: B) (hnd : l.Nodup)
    (hxy : x ≠ y) (hs : [x, y].Sublist l) : x ∈ A := by
  subst hl
  obtain ⟨l₁, l₂, heq, h1, h2⟩ := List.sublist_append_iff.1 hs
  have hyA : y ∉ A := fun hy => by
    have := (List.nodup_append.1 hnd).2.2 y hy y (by simp)
    exact this rfl
  have hyB : y ∉ B := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
  match l₁, heq with
  | [], heq =>
    simp only [List.nil_append] at heq
    subst heq
    rcases List.sublist_cons_iff.1 h2 with h2 | ⟨r, hr, -⟩
    · exact absurd (h2.subset (by simp)) hyB
    · simp only [List.cons.injEq] at hr; exact absurd hr.1 hxy
  | [z], heq =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    exact h1.subset (by simp)
  | z :: z' :: r, heq =>
    simp only [List.cons_append, List.cons.injEq] at heq
    obtain ⟨-, rfl, -⟩ := heq
    exact absurd (h1.subset (by simp)) hyA

end Lists

end CM

open CM

namespace Example2

/-- The elements of Example 2 (`e` is used only to build the initial matrix). -/
inductive Elt where
  | a
  | b
  | e
  deriving DecidableEq

/-- Two processes. -/
inductive Proc where
  | p
  | q
  deriving DecidableEq

/-- The hash functions of Example 2 (0-based): `h₀(a) = h₁(a) = 0`, `h₀(b) = 1`, `h₁(b) = 0`,
`h₀(e) = h₁(e) = 1`. -/
def hEx : Fin 2 → Elt → Fin 2 := fun i x =>
  match x with
  | .a => 0
  | .b => if i = 0 then 1 else 0
  | .e => 1

/-- Labels of `σ`. -/
abbrev Lbl := Label Proc (cmIface Elt)

/-- A complete update of `x` by `p`: invocation, `d = 2` increments, response. -/
def updBy (x : Elt) : List Lbl := [.inv .p (.update x), .tau .p, .tau .p, .ret .p 0]

/-- The sequential prefix `a, b, e, e, e` by `p`, building the matrix `[[1, 4], [2, 3]]`. -/
def prefixEx : List Lbl := updBy .a ++ updBy .b ++ updBy .e ++ updBy .e ++ updBy .e

/-- The execution up to the end of `Q₁`: the prefix, the first increment of `U`, `Q₁`. -/
def beforeQ₂ : List Lbl :=
  prefixEx ++ [.inv .p (.update .a), .tau .p] ++
    [.inv .q (.query .a), .tau .q, .tau .q, .ret .q 2]

/-- The execution `σ` of Example 2. -/
def example2 : List Lbl :=
  beforeQ₂ ++ [.inv .q (.query .b), .tau .q, .tau .q, .ret .q 2] ++ [.tau .p, .ret .p 0]

/-- `σ` is an execution of `PCM` for the hash functions of the example. -/
theorem example2_valid : (pcm hEx Proc).Valid example2 :=
  Impl.valid_of_crun _ (by decide)

/-- The operation instances of `σ` with their operations. -/
def table : List (OpId Proc × CMOp Elt) :=
  [((.p, 0), .update .a), ((.p, 1), .update .b), ((.p, 2), .update .e), ((.p, 3), .update .e),
    ((.p, 4), .update .e), ((.p, 5), .update .a), ((.q, 0), .query .a), ((.q, 1), .query .b)]

lemma opOf_example2 {x : OpId Proc} {o : CMOp Elt} (hx : opOf example2 x = some o) :
    (x, o) ∈ table := by
  obtain ⟨r, n⟩ := x
  cases r with
  | p =>
    have hp : opsOf example2 .p = [.update .a, .update .b, .update .e, .update .e, .update .e,
        .update .a] := by decide
    simp only [opOf, hp] at hx
    rcases n with _ | _ | _ | _ | _ | _ | n <;> simp at hx <;> subst hx <;> decide
  | q =>
    have hq : opsOf example2 .q = [.query .a, .query .b] := by decide
    simp only [opOf, hq] at hx
    rcases n with _ | _ | n <;> simp at hx <;> subst hx <;> decide

/-- **Example 2** of [Rinberg–Keidar]: the execution `σ` of `PCM` is not linearizable with
respect to the CountMin sketch `CM(c⃗)` (for the hash functions of the example). -/
theorem example2_not_lin : ¬ IsLinFor (cmSpec hEx) example2 := by
  rintro ⟨L, hL, hresp⟩
  obtain ⟨hnd, hop, -, hrt⟩ := isSkelLin_iff.1 hL
  have hT : ∀ y ∈ L, y ∈ table := fun y hy => opOf_example2 (hop y hy)
  -- `Q₂ = (q, 1)` returns `2`
  obtain ⟨A, B, o₂, hLs, hval₂⟩ :=
    ObjSpec.exists_split_of_respIn_eq_some (hresp (.q, 1) 2 (by decide))
  have ho₂ : o₂ = .query .b := by
    have := hT ((.q, 1), o₂) (by rw [hLs]; simp)
    simpa [table] using this
  subst ho₂
  have hval₂' : (⨅ i, cnt hEx A i (hEx i .b)) = 2 := hval₂
  have hmapL : L.map Prod.fst = A.map Prod.fst ++ (.q, 1) :: B.map Prod.fst := by simp [hLs]
  have hrest : example2 = beforeQ₂ ++
      ([.inv .q (.query .b), .tau .q, .tau .q, .ret .q 2] ++ [.tau .p, .ret .p 0]) := by
    simp [example2]
  have hinA : ∀ x ∈ ([(.p, 0), (.p, 1), (.p, 2), (.p, 3), (.p, 4), (.q, 0)] : List (OpId Proc)),
      x ∈ A.map Prod.fst := by
    intro x hx
    have hprec : Precedes example2 x (.q, 1) :=
      ⟨_, _, hrest, by
        unfold Completed; simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide,
        by unfold Invoked; decide⟩
    refine mem_left_of_sublist hmapL hnd ?_ (hrt _ _ hprec (by simp [hmapL]))
    simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  -- `Q₁ = (q, 0)` returns `2`; it is linearized before `Q₂`
  obtain ⟨⟨x₁, o₁⟩, hy₁, hx₁⟩ := List.mem_map.1 (hinA (.q, 0) (by simp))
  simp only at hx₁
  subst hx₁
  obtain ⟨A₁, A₂, hA⟩ := List.append_of_mem hy₁
  have ho₁ : o₁ = .query .a := by
    have := hT ((.q, 0), o₁) (by rw [hLs, hA]; simp)
    simpa [table] using this
  subst ho₁
  have hval₁ : (⨅ i, cnt hEx A₁ i (hEx i .a)) = 2 := by
    have h1 := hresp (.q, 0) 2 (by decide)
    have h1' : tau (cmSpec hEx) L (.q, 0) =
        some ((cmSpec hEx).δ ((cmSpec hEx).obj.runOps (cmSpec hEx).init (A₁.map Prod.snd))
          (.query .a)).2 := by
      unfold tau
      exact ObjSpec.respIn_of_split (A := (cmSpec hEx).obj) (x := (.q, 0)) (o := .query .a)
        (L₁ := A₁)
        (L₂ := A₂ ++ ((.q, 1), .query .b) :: B) hnd (by simp [hLs, hA])
    rw [h1'] at h1
    exact Option.some.inj h1
  by_cases hU : ((.p, 5) : OpId Proc) ∈ A₁.map Prod.fst
  · -- `U` is linearized before `Q₁`, hence before `Q₂`: `Q₂` would return `3`
    have hUA : ((.p, 5) : OpId Proc) ∈ A.map Prod.fst := by rw [hA]; simp [hU]
    have hA' : ∀ y ∈ A, y ∈ table := fun y hy => hT y (by rw [hLs]; simp [hy])
    have hfind : ∀ s ∈ A.map Prod.fst, ∃ y ∈ A, y.1 = s := fun s hs => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hs; exact ⟨y, hy, rfl⟩
    have hge : ∀ (S : List (OpId Proc)) (i j : Fin 2), S.Nodup → (∀ s ∈ S, s ∈ A.map Prod.fst) →
        (∀ y ∈ table, y.1 ∈ S → hits hEx i j y.2 = true) → S.length ≤ cnt hEx A i j := by
      intro S i j hS hSA htab
      rw [cnt_eq_countP]
      refine length_le_countP A _ S hS fun s hs => ?_
      obtain ⟨y, hy, rfl⟩ := hfind s (hSA s hs)
      exact ⟨y, hy, rfl, htab y (hA' y hy) hs⟩
    have h10 := hge [(.p, 0), (.p, 1), (.p, 5)] 1 0 (by decide)
      (by intro s hs; simp at hs; rcases hs with rfl | rfl | rfl
          · exact hinA _ (by simp)
          · exact hinA _ (by simp)
          · exact hUA) (by decide)
    have h01 := hge [(.p, 1), (.p, 2), (.p, 3), (.p, 4)] 0 1 (by decide)
      (fun s hs => hinA s (by simp at hs ⊢; tauto)) (by decide)
    have : 3 ≤ ⨅ i, cnt hEx A i (hEx i .b) := by
      refine le_ciInf fun i => ?_
      fin_cases i
      · show 3 ≤ cnt hEx A 0 1
        simp at h01; omega
      · show 3 ≤ cnt hEx A 1 0
        simpa using h10
    rw [hval₂'] at this
    exact absurd this (by decide)
  · -- `U` is linearized after `Q₁`: `Q₁` would return `1`
    have hnd₁ : (A₁.map Prod.fst).Nodup := by
      rw [hLs, hA] at hnd; simp at hnd
      exact hnd.sublist (by simp)
    have hle : cnt hEx A₁ 0 0 ≤ 1 := by
      rw [cnt_eq_countP]
      refine countP_le_length A₁ _ [(.p, 0)] hnd₁ fun y hy hhit => ?_
      have hyT : y ∈ table := hT y (by rw [hLs, hA]; simp [hy])
      have hy5 : y.1 ≠ (.p, 5) := fun h5 => hU (List.mem_map.2 ⟨y, hy, h5⟩)
      have key : ∀ y ∈ table, hits hEx 0 0 y.2 = true → y.1 = (.p, 0) ∨ y.1 = (.p, 5) := by
        decide
      rcases key y hyT hhit with h0 | h5
      · simp [h0]
      · exact absurd h5 hy5
    have : (⨅ i, cnt hEx A₁ i (hEx i .a)) ≤ 1 :=
      le_trans (ciInf_le (OrderBot.bddBelow _) 0) hle
    rw [hval₁] at this
    exact absurd this (by decide)

/-- **Example 2** of [Rinberg–Keidar]: `PCM` is not a linearizable implementation of the
CountMin sketch: for the hash functions `hEx`, the execution `σ` of `pcm hEx` is not
linearizable with respect to `cmSpec hEx`. -/
theorem pcm_not_linearizable :
    ∃ α, (pcm hEx Proc).Valid α ∧ ¬ IsLinFor (cmSpec hEx) α :=
  ⟨example2, example2_valid, example2_not_lin⟩

end Example2

end Podc.IntermediateValueLin
