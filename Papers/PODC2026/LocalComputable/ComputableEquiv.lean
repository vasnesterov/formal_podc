import Papers.PODC2026.LocalComputable.Basic
import Cslib.Computability.Partrec.List

/-!
# Theorem 5.3: with a bound on `n`, uncomputable and computable LOCAL coincide

If nodes receive a number `N` subject to a promise `Adm N G` (e.g. `n ≤ N`, or `n ≤ N ≤ f(n)`)
such that, for every `N`, the legal networks form a finite list that can be computed from `N`,
then every (possibly uncomputable) algorithm family of locality `T` can be replaced by a
computable one of the same locality `T`, provided `T`, the views and the validity check are
computable.

Proof (simpler than the paper's): for a fixed `N`, there are finitely many pairs
(view, radius) that can be consulted in legal networks before the deadline `T(n)`. A *table*
assigning outputs to such pairs is a finite object, and whether a table solves the problem on
all legal networks is decidable. The restriction of the given algorithm `A_N` to these pairs is
such a table, so an unbounded search over (codes of) tables terminates. The computable
algorithm computes the first good table for its `N` and looks up its own view in it.
This avoids the paper's maximally safe neighbourhoods altogether (cf. `differencies.md`).
-/

namespace LocalComputable

open Computable Encodable

variable {Net View Out : Type*}

/-- Lists: `findSome?` only depends on the function on the list's elements. -/
theorem findSome?_congr' {α β : Type*} {l : List α} {f g : α → Option β}
    (h : ∀ x ∈ l, f x = g x) : l.findSome? f = l.findSome? g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.findSome?_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

namespace Model

variable (M : Model Net View)

/-- Two algorithms that agree on all views of radius `≤ r` of node `v` produce the same output
at `v` when grown up to radius `r`. -/
theorem out_congr_alg {A A' : Alg View Out} {G : Net} {v r : ℕ}
    (h : ∀ t ≤ r, A (M.view G v t) t = A' (M.view G v t) t) : M.out A G v r = M.out A' G v r :=
  findSome?_congr' fun t ht => h t (Nat.lt_succ_iff.mp (List.mem_range.mp ht))

/-! ### Tables -/

variable [DecidableEq View]

/-- A finite table of (view, radius) ↦ output. -/
abbrev Tab (View Out : Type*) := List ((View × ℕ) × Out)

/-- The algorithm that looks up its (view, radius) in a table (`⊥` if absent). -/
def runTab (L : Tab View Out) : Alg View Out := fun x t => L.lookup (x, t)

/-- The outputs of all nodes of `G` (in order), the ball being grown up to `T (size G)`. -/
def outs (T : ℕ → ℕ) (A : Alg View Out) (G : Net) : List (Option Out) :=
  (List.range (M.size G)).map fun v => M.out A G v (T (M.size G))

/-- Decidable check that `A` solves the problem (given by the checker `check`) on `G`. -/
def goodNet (T : ℕ → ℕ) (check : Net → List Out → Bool) (A : Alg View Out) (G : Net) : Bool :=
  (M.outs T A G).all Option.isSome && check G (M.outs T A G).reduceOption

/-- `filterMap` over `range n` with an everywhere-defined function is `ofFn`. -/
theorem filterMap_range_eq_ofFn {n : ℕ} (f : ℕ → Option Out) (lab : Fin n → Out)
    (h : ∀ v : Fin n, f v = some (lab v)) : (List.range n).filterMap f = List.ofFn lab := by
  rw [← List.map_coe_finRange_eq_range, List.filterMap_map, List.ofFn_eq_map]
  have : (f ∘ fun i : Fin n => (i : ℕ)) = some ∘ lab := funext fun v => h v
  rw [this, List.filterMap_eq_map]

omit [DecidableEq View] in
theorem goodNet_iff (T : ℕ → ℕ) (check : Net → List Out → Bool) {P : M.Problem Out}
    (hP : ∀ G lab, check G (List.ofFn lab) = true ↔ P G lab) (A : Alg View Out) (G : Net) :
    M.goodNet T check A G = true ↔ M.SolvesOn P A T G := by
  constructor
  · intro h
    simp only [goodNet, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hs, hc⟩ := h
    have hs' : ∀ v : Fin (M.size G), (M.out A G v (T (M.size G))).isSome := fun v =>
      hs _ (List.mem_map.mpr ⟨v, List.mem_range.mpr v.2, rfl⟩)
    let lab : Fin (M.size G) → Out := fun v => (M.out A G v (T (M.size G))).get (hs' v)
    have hlab : ∀ v : Fin (M.size G), M.out A G v (T (M.size G)) = some (lab v) := fun v => by
      simp [lab]
    refine ⟨lab, hlab, (hP G lab).mp ?_⟩
    rw [← filterMap_range_eq_ofFn (fun v => M.out A G v (T (M.size G))) lab hlab]
    simpa [outs, List.reduceOption, List.filterMap_map] using hc
  · rintro ⟨lab, hlab, hPG⟩
    simp only [goodNet, Bool.and_eq_true, List.all_eq_true]
    refine ⟨?_, ?_⟩
    · intro o ho
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ho
      rw [hlab ⟨v, List.mem_range.mp hv⟩]
      rfl
    · have : (M.outs T A G).reduceOption = List.ofFn lab := by
        rw [← filterMap_range_eq_ofFn (fun v => M.out A G v (T (M.size G))) lab hlab]
        simp [outs, List.reduceOption, List.filterMap_map]
      rw [this]
      exact (hP G lab).mpr hPG

/-- Looking up a key in a table built from a partial function on a list of keys. -/
theorem lookup_filterMap {κ β : Type*} [DecidableEq κ] (F : κ → Option β) (K : List κ) (k : κ) :
    (K.filterMap fun k => (F k).map fun b => (k, b)).lookup k = if k ∈ K then F k else none := by
  induction K with
  | nil => simp
  | cons k' K ih =>
    rw [List.filterMap_cons]
    rcases hF : F k' with _ | b
    · simp only [Option.map_none]
      rw [ih]
      by_cases hk : k = k'
      · subst hk; simp [hF]
      · simp [hk]
    · simp only [Option.map_some, List.lookup]
      by_cases hk : k = k'
      · subst hk; simp [hF]
      · have : (k == k') = false := by simpa using hk
        simp only [this, ih, List.mem_cons, hk, false_or]

/-! ### Theorem 5.3 -/

variable [Primcodable Net] [Primcodable View] [Primcodable Out]

/-- **Theorem 5.3** of [Cruciani et al., PODC 2026] (generalized). Assume that nodes receive a
number `N` subject to a promise `Adm`, where for every `N` the legal networks are exactly those
in a computable finite list `cand N`; that sizes, views, the locality bound `T` and the validity
of output labellings are computable. If some (possibly uncomputable) algorithm family solves
`P` with locality `T` under the promise, then some *computable* algorithm family does.

The paper's version is the promise `n ≤ N ≤ f(n)` (`sandwich_computable`), including
`f = ∞` (`upperBound_computable`). No monotonicity of `T` or `f` is needed. -/
theorem exists_computable_of_promise
    (hsize : Computable M.size) (hview : Computable fun p : Net × ℕ × ℕ => M.view p.1 p.2.1 p.2.2)
    {T : ℕ → ℕ} (hT : Computable T)
    {Adm : ℕ → Net → Prop} (cand : ℕ → List Net) (hcand : Computable cand)
    (hAdm : ∀ N G, Adm N G ↔ G ∈ cand N)
    {P : M.Problem Out} (check : Net → List Out → Bool) (hcheck : Computable₂ check)
    (hP : ∀ G lab, check G (List.ofFn lab) = true ↔ P G lab)
    (A : ℕ → Alg View Out) (hA : M.SolvesWith Adm P A T) :
    ∃ B : ℕ → Alg View Out, Computable (fun p : ℕ × View × ℕ => B p.1 p.2.1 p.2.2) ∧
      M.SolvesWith Adm P B T := by
  classical
  -- `good N L`: the table `L` solves `P` on all legal networks for `N`.
  let good : ℕ → Tab View Out → Bool := fun N L =>
    (cand N).all fun G => M.goodNet T check (runTab L) G
  let goodCode : ℕ → ℕ → Bool := fun N c => ((decode (α := Tab View Out) c).map (good N)).getD false
  -- Existence of a good table: the restriction of `A N`.
  have hex : ∀ N, ∃ c, goodCode N c = true := by
    intro N
    let K : List (View × ℕ) := (cand N).flatMap fun G => (List.range (M.size G)).flatMap
      fun v => (List.range (T (M.size G) + 1)).map fun t => (M.view G v t, t)
    let L : Tab View Out := K.filterMap fun k => (A N k.1 k.2).map fun b => (k, b)
    refine ⟨encode L, ?_⟩
    simp only [goodCode, encodek, Option.map_some, Option.getD_some, good, List.all_eq_true]
    intro G hG
    have hsolve := hA N G ((hAdm N G).mpr hG)
    rw [M.goodNet_iff T check hP]
    obtain ⟨lab, hlab, hPG⟩ := hsolve
    refine ⟨lab, fun v => ?_, hPG⟩
    rw [← hlab v]
    refine M.out_congr_alg fun t ht => ?_
    have hk : (M.view G v t, t) ∈ K := by
      simp only [K, List.mem_flatMap, List.mem_range, List.mem_map]
      exact ⟨G, hG, v, v.2, t, Nat.lt_succ_iff.mpr ht, rfl⟩
    simp only [runTab, L]
    rw [lookup_filterMap (fun k : View × ℕ => A N k.1 k.2) K]; simp [hk]
  -- Computability of the check.
  have hout : Computable fun q : Tab View Out × Net × ℕ =>
      M.out (runTab q.1) q.2.1 q.2.2 (T (M.size q.2.1)) := by
    unfold out runTab
    refine Computable.list_findSome?
      (Primrec.list_range.to_comp.comp (succ.comp (hT.comp (hsize.comp (fst.comp snd))))) ?_
    refine Primrec.listLookup.to_comp.comp
      (pair (hview.comp (pair (fst.comp (snd.comp fst)) (pair (snd.comp (snd.comp fst)) snd)))
        snd) (fst.comp fst) |>.to₂
  have houts : Computable fun q : Tab View Out × Net => M.outs T (runTab q.1) q.2 := by
    unfold outs
    exact Computable.list_map (Primrec.list_range.to_comp.comp (hsize.comp snd))
      (hout.comp (pair (fst.comp fst) (pair (snd.comp fst) snd))).to₂
  have hgoodNet : Computable fun q : Tab View Out × Net => M.goodNet T check (runTab q.1) q.2 := by
    unfold goodNet
    refine Primrec.and.to_comp.comp (Computable.list_all houts
      (Primrec.option_isSome.to_comp.comp snd).to₂) ?_
    refine hcheck.comp snd ?_
    exact (Computable.list_filterMap houts (Computable.snd).to₂).of_eq fun q => by
      simp [List.reduceOption]
  have hgood : Computable₂ good := by
    refine (Computable.list_all (f := fun q : ℕ × Tab View Out => cand q.1)
      (p := fun q G => M.goodNet T check (runTab q.2) G) (hcand.comp fst) ?_).to₂
    exact (hgoodNet.comp (pair (snd.comp fst) snd)).to₂
  have hgoodCode : Computable₂ goodCode := by
    refine (option_getD (option_map (Computable.decode.comp snd) (hgood.comp (fst.comp fst) snd).to₂)
      (const false)).to₂
  -- Unbounded search for a good table.
  let cstar : ℕ → ℕ := fun N => Nat.find (hex N)
  have hcstar : Computable cstar := by
    refine (Partrec.rfind (p := fun N c => (Part.some (goodCode N c))) hgoodCode.partrec₂).of_eq
      fun N => ?_
    refine Part.eq_some_iff.mpr (Nat.mem_rfind.mpr ⟨?_, fun {m} hm => ?_⟩)
    · simp only [Part.mem_some_iff]; exact (Nat.find_spec (hex N)).symm
    · simp only [Part.mem_some_iff]
      have := Nat.find_min (hex N) hm
      simpa using this
  let B : ℕ → Alg View Out := fun N => runTab ((decode (α := Tab View Out) (cstar N)).getD [])
  refine ⟨B, ?_, ?_⟩
  · simp only [B, runTab]
    exact Primrec.listLookup.to_comp.comp snd
      (option_getD (Computable.decode.comp (hcstar.comp fst)) (const []))
  · intro N G hG
    have hc : goodCode N (cstar N) = true := Nat.find_spec (hex N)
    simp only [goodCode] at hc
    rcases hdec : decode (α := Tab View Out) (cstar N) with _ | L
    · simp [hdec] at hc
    · simp only [hdec, Option.map_some, Option.getD_some, good, List.all_eq_true] at hc
      have := hc G ((hAdm N G).mp hG)
      rw [M.goodNet_iff T check hP] at this
      simpa [B, hdec] using this

/-! ### The promises of the paper -/

/-- `ℕ∞` as `Option ℕ` (`none` = `∞`), to state computability of `f : ℕ → ℕ∞`. -/
def enatToOption (x : ℕ∞) : Option ℕ := ENat.recTopCoe none some x

theorem le_iff_enatToOption (N : ℕ) (x : ℕ∞) :
    (N : ℕ∞) ≤ x ↔ ((enatToOption x).map (N ≤ ·)).getD True := by
  induction x using ENat.recTopCoe with
  | top => simp [enatToOption]
  | coe m => simp [enatToOption, ENat.natCast_le_natCast]

/-- **Theorem 5.3** as stated in the paper: promise `n ≤ N ≤ f(n)` with computable `f`
(`f n = ∞` allowed), computable `T`, networks of size `≤ N` computably listable. -/
theorem sandwich_computable
    (hsize : Computable M.size) (hview : Computable fun p : Net × ℕ × ℕ => M.view p.1 p.2.1 p.2.2)
    {T : ℕ → ℕ} (hT : Computable T) {f : ℕ → ℕ∞} (hf : Computable fun n => enatToOption (f n))
    (nets : ℕ → List Net) (hnets : Computable nets) (hnetsG : ∀ N G, G ∈ nets N ↔ M.size G ≤ N)
    {P : M.Problem Out} (check : Net → List Out → Bool) (hcheck : Computable₂ check)
    (hP : ∀ G lab, check G (List.ofFn lab) = true ↔ P G lab)
    (A : ℕ → Alg View Out) (hA : M.SolvesWith (M.Sandwich f) P A T) :
    ∃ B : ℕ → Alg View Out, Computable (fun p : ℕ × View × ℕ => B p.1 p.2.1 p.2.2) ∧
      M.SolvesWith (M.Sandwich f) P B T := by
  classical
  let fle : ℕ → Net → Bool := fun N G =>
    ((enatToOption (f (M.size G))).map (fun m => decide (N ≤ m))).getD true
  have hfle : Computable₂ fle :=
    (option_getD (option_map (hf.comp (hsize.comp snd))
      (Primrec.nat_le.decide.to_comp.comp (fst.comp fst) snd).to₂) (const true)).to₂
  refine M.exists_computable_of_promise hsize hview hT (fun N => (nets N).filter (fle N))
    ?_ ?_ check hcheck hP A hA
  · exact Computable.list_filter hnets hfle
  · intro N G
    simp only [List.mem_filter, hnetsG, Sandwich, fle, le_iff_enatToOption]
    rcases enatToOption (f (M.size G)) <;> simp

end Model

end LocalComputable
