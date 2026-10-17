import Cslib.Computability.Distributed.SharedMemory.Valency
import Papers.PODC2016.ComplexityHierarchy.Packing

/-!
# ℓ-buffers and multiple assignment (Sections 6–7 of Ellen–Gelashvili–Shavit–Zhu, PODC 2016)

An *ℓ-buffer* stores the inputs of its `ℓ` most recent `ℓ-buffer-write`s; `ℓ-buffer-read` returns
them. We represent its content as a list, most recent write first, of length `≤ ℓ` once it has
been written (the paper pads with `⊥`; the initial content is arbitrary here, `memInit`).

**Memory model.** To also cover *multiple assignment* (Section 7: a process atomically performs one
`ℓ-buffer-write` on each location of an arbitrary subset), the whole memory is modelled as a single
base object `multiBuffer R ℓ V` of the CSLib model (`ι = Unit`), with locations `R`:

* `MOp.read r`: returns the content of location `r`;
* `MOp.write w` (`w : R → Option V`): for every `r` with `w r = some x`, performs
  `ℓ-buffer-write(x)` on `r`; returns `[]` (nothing). Plain (single-location) writes are the `w`
  with at most one `some` (`SingleWrites`).

Section 6's per-location model (`ι` locations, each an `ℓ-buffer` base object) is reduced to this
one in `BufferLB.lean`.

## Main definitions

* `bufWrite`, `applyW`, `multiBuffer R ℓ V`, `MB R ℓ V` (the base-object family).
* `Impl.Poised C p w`, `Impl.MCovers C p r` (paper: `p` covers `r`), `Impl.WritesIn C p S`
  (`p`'s next step writes nowhere outside `S`), `Impl.SingleWrites`, `Impl.wOf`.

## Main results

* `foldl_bufWrite`, `foldl_bufWrite_eq`: `ℓ` writes obliterate an `ℓ-buffer`.
* `Impl.runFrom_block`: effect of a block of (multi-)writes (from the library's
  `Impl.runFrom_poised_block`).
* `Impl.block_agreeOn`: indistinguishability after a block that writes `≥ ℓ` times to every
  location on which two configurations differ.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory Impl

/-- Operations on a memory of locations `R` holding values `V`. -/
inductive MOp (R V : Type) where
  /-- `ℓ-buffer-read` of location `r`. -/
  | read (r : R)
  /-- Multiple assignment: `ℓ-buffer-write (x)` to every `r` with `w r = some x`. -/
  | write (w : R → Option V)

variable {R V : Type}

/-- Content of an `ℓ`-buffer after `ℓ-buffer-write v` (most recent first). -/
def bufWrite (ℓ : ℕ) (v : V) (b : List V) : List V := (v :: b).take ℓ

/-- Effect of a multiple assignment on the memory. -/
def applyW (ℓ : ℕ) (w : R → Option V) (m : R → List V) : R → List V := fun r =>
  match w r with
  | some v => bufWrite ℓ v (m r)
  | none => m r

/-- The memory: `ℓ`-buffers at locations `R`, with `ℓ-buffer-read` and multiple assignment. -/
abbrev multiBuffer (R : Type) (ℓ : ℕ) (V : Type) : ObjSpec where
  State := R → List V
  Op := MOp R V
  Resp := List V
  init := fun _ => []
  δ s o := match o with
    | .read r => (s, s r)
    | .write w => (applyW ℓ w s, [])

/-- The base-object family: a single object, the whole memory. -/
abbrev MB (R : Type) (ℓ : ℕ) (V : Type) : Unit → ObjSpec := fun _ => multiBuffer R ℓ V

/-! ### Buffers -/

lemma take_append_take (x y : List V) (n : ℕ) : (x ++ y.take n).take n = (x ++ y).take n := by
  simp [List.take_append, List.take_take]

lemma foldl_bufWrite (ℓ : ℕ) {vs : List V} (hvs : vs ≠ []) (a : List V) :
    vs.foldl (fun b v => bufWrite ℓ v b) a = (vs.reverse ++ a).take ℓ := by
  induction vs generalizing a with
  | nil => exact absurd rfl hvs
  | cons v vs ih =>
    rw [List.foldl_cons]
    by_cases h : vs = []
    · subst h; simp [bufWrite]
    · rw [ih h, bufWrite, take_append_take]; simp

/-- **`ℓ` writes obliterate an `ℓ`-buffer**: after at least `max ℓ 1` writes, the content does not
depend on the content before. -/
lemma foldl_bufWrite_eq {ℓ : ℕ} {vs : List V} (hvs : vs ≠ []) (h : ℓ ≤ vs.length) (a b : List V) :
    vs.foldl (fun b v => bufWrite ℓ v b) a = vs.foldl (fun b v => bufWrite ℓ v b) b := by
  rw [foldl_bufWrite ℓ hvs, foldl_bufWrite ℓ hvs,
    List.take_append_of_le_length (by simpa using h),
    List.take_append_of_le_length (by simpa using h)]

/-- The values written to location `r` by a list of multiple assignments, in order. -/
def wvals (ws : List (R → Option V)) (r : R) : List V := ws.filterMap (fun w => w r)

lemma foldl_applyW (ℓ : ℕ) (ws : List (R → Option V)) (m : R → List V) (r : R) :
    (ws.foldl (fun m w => applyW ℓ w m) m) r =
      (wvals ws r).foldl (fun b v => bufWrite ℓ v b) (m r) := by
  induction ws generalizing m with
  | nil => rfl
  | cons w ws ih =>
    rw [List.foldl_cons, ih]
    unfold wvals applyW
    cases h : w r with
    | none => simp [List.filterMap_cons, h]
    | some v => simp [List.filterMap_cons, h]

lemma wvals_append (ws ws' : List (R → Option V)) (r : R) :
    wvals (ws ++ ws') r = wvals ws r ++ wvals ws' r := by simp [wvals]

lemma wvals_eq_nil {ws : List (R → Option V)} {r : R} (h : ∀ w ∈ ws, w r = none) :
    wvals ws r = [] := by
  simp only [wvals, List.filterMap_eq_nil_iff]; exact h

/-! ### Processes accessing the memory -/

end Cslib.SharedMemory.ComplexityHierarchy

namespace Cslib.SharedMemory.Impl

open ComplexityHierarchy

variable {R V : Type} {ℓ : ℕ} {P L : Type} [DecidableEq P]

variable (I : Impl BinCons (MB R ℓ V) P L)

/-- In `C`, `p` is pending and poised to perform the multiple assignment `w` (the library's
`Impl.PoisedAt` for the memory object). -/
abbrev Poised (C : Config BinCons (MB R ℓ V) P L) (p : P) (w : R → Option V) : Prop :=
  I.PoisedAt C p () (.write w)

/-- In `C`, `p` covers location `r`: it is poised to perform a (multiple) assignment that writes
`r`. -/
def MCovers (C : Config BinCons (MB R ℓ V) P L) (p : P) (r : R) : Prop :=
  ∃ w, I.Poised C p w ∧ w r ≠ none

/-- `p`'s next step does not write any location outside `S` (it is a read, a return, or a
(multiple) assignment to locations of `S` only). -/
def WritesIn (C : Config BinCons (MB R ℓ V) P L) (p : P) (S : Set R) : Prop :=
  ∀ w k, I.act p (C.loc p) = .access () (.write w) k → ∀ r, w r ≠ none → r ∈ S

/-- The algorithm only uses single-location writes (no multiple assignment). -/
def SingleWrites : Prop :=
  ∀ p l w k, I.act p l = .access () (.write w) k → ∀ r r', w r ≠ none → w r' ≠ none → r = r'

/-- The assignment `p` is about to perform (nothing if it is not poised to write). -/
def wOf (C : Config BinCons (MB R ℓ V) P L) (p : P) : R → Option V :=
  match I.act p (C.loc p) with
  | .access _ (.write w) _ => w
  | _ => fun _ => none

/-- The local state of a process after its next step, if that step is a write. -/
def contOf (p : P) (l : L) : L :=
  match I.act p l with
  | .access _ _ k => k []
  | .ret _ l' => l'

variable {I}

lemma Poised.wOf_eq {C : Config BinCons (MB R ℓ V) P L} {p : P} {w : R → Option V}
    (h : I.Poised C p w) : I.wOf C p = w := by
  obtain ⟨-, k, hk⟩ := h; unfold wOf; rw [hk]

lemma MCovers.congr {C D : Config BinCons (MB R ℓ V) P L} {p : P} {r : R}
    (h : I.MCovers C p r) (hl : C.loc p = D.loc p) (hp : C.pend p = D.pend p) : I.MCovers D p r := by
  obtain ⟨w, hw, hr⟩ := h; exact ⟨w, hw.congr hl hp, hr⟩

lemma mCovers_iff_of_eq {C D : Config BinCons (MB R ℓ V) P L} {p : P} (hl : C.loc p = D.loc p)
    (hp : C.pend p = D.pend p) (r : R) : I.MCovers C p r ↔ I.MCovers D p r :=
  ⟨fun h => h.congr hl hp, fun h => h.congr hl.symm hp.symm⟩

lemma wOf_congr {C D : Config BinCons (MB R ℓ V) P L} {p : P} (hl : C.loc p = D.loc p) :
    I.wOf C p = I.wOf D p := by unfold wOf; rw [hl]

/-- The step of a poised writer. -/
lemma step_poised {C : Config BinCons (MB R ℓ V) P L} {p : P} {w : R → Option V}
    (h : I.Poised C p w) : ∃ C', I.step C (.tau p) = some C' ∧ C'.mem () = applyW ℓ w (C.mem ()) ∧
      C'.loc = Function.update C.loc p (I.contOf p (C.loc p)) ∧ C'.pend = C.pend := by
  obtain ⟨hp, k, hk⟩ := h
  refine ⟨{ C with mem := Function.update C.mem () (applyW ℓ w (C.mem ())),
                   loc := Function.update C.loc p (k []) },
    by simp [step, hp, hk], by simp, by simp [contOf, hk], rfl⟩

/-- What a single internal step does to the memory. -/
lemma step_tau_cases {C C' : Config BinCons (MB R ℓ V) P L} {q : P}
    (h : I.step C (.tau q) = some C') :
    (∃ r k, I.act q (C.loc q) = .access () (.read r) k ∧ C'.mem = C.mem) ∨
      (∃ w, I.Poised C q w ∧ C'.mem () = applyW ℓ w (C.mem ())) := by
  obtain ⟨hp, -, i, o, k, hact, hm, -⟩ := step_tau h
  cases i
  cases o with
  | read r =>
    left; refine ⟨r, k, hact, ?_⟩
    rw [hm]; funext i; cases i; simp
  | write w =>
    right; refine ⟨w, ⟨hp, k, hact⟩, ?_⟩
    rw [hm]; simp

omit [DecidableEq P] in
/-- Multiple assignments, as accesses of the memory object, act by `applyW`. -/
lemma applyAccesses_writes (ws : List (R → Option V)) (M : ∀ _ : Unit, R → List V) :
    applyAccesses (B := MB R ℓ V) M (ws.map fun w => ⟨(), .write w⟩) () =
      ws.foldl (fun m w => applyW ℓ w m) (M ()) := by
  induction ws generalizing M with
  | nil => rfl
  | cons w ws ih => simpa using ih (Function.update M () (applyW ℓ w (M ())))

/-- **Effect of a block** of distinct poised writers: each takes one step (a write). -/
theorem runFrom_block (ps : List P) (X : Config BinCons (MB R ℓ V) P L) (hnd : ps.Nodup)
    (hpo : ∀ p ∈ ps, ∃ w, I.Poised X p w) :
    ∃ X', I.runFrom X (blockWrite ps) = some X' ∧
      X'.mem () = (ps.map (I.wOf X)).foldl (fun m w => applyW ℓ w m) (X.mem ()) ∧
      X'.pend = X.pend ∧ (∀ q, q ∉ ps → X'.loc q = X.loc q) ∧
      (∀ p ∈ ps, X'.loc p = I.contOf p (X.loc p)) := by
  obtain ⟨X', h1, h2, h3, h4, h5⟩ := runFrom_poised_block (I := I)
    (es := ps.map fun p => (p, (⟨(), .write (I.wOf X p)⟩ : Σ _ : Unit, (multiBuffer R ℓ V).Op)))
    (by simpa [Function.comp_def] using hnd) (C := X) (by
      simp only [List.mem_map]
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨w, hw⟩ := hpo p hp
      rw [hw.wOf_eq]; exact hw)
  simp only [List.map_map, Function.comp_def, List.map_id'] at h1 h2 h4
  refine ⟨X', h1, by rw [h2, ← applyAccesses_writes, List.map_map]; rfl, h3, h4, fun p hp => ?_⟩
  obtain ⟨k, s, hk, hl⟩ := h5 _ (List.mem_map_of_mem (f := fun p => (p,
    (⟨(), .write (I.wOf X p)⟩ : Σ _ : Unit, (multiBuffer R ℓ V).Op))) hp)
  rw [hl]; simp only [contOf] at hk ⊢; rw [hk]

/-- **Indistinguishability after a block.** Let `X` and `Y` agree on the processes of `S`, and let
the distinct processes `ps ⊆ S` be poised to write in `X`. If at every location the memories of
`X` and `Y` agree or the block writes it at least `max ℓ 1` times, then after the block `X` and `Y`
agree on `S` and on the whole memory. -/
theorem block_agreeOn {S : Set P} {X Y : Config BinCons (MB R ℓ V) P L} (ps : List P)
    (hnd : ps.Nodup) (hpS : ∀ p ∈ ps, p ∈ S) (hpo : ∀ p ∈ ps, ∃ w, I.Poised X p w)
    (hloc : ∀ q ∈ S, X.loc q = Y.loc q) (hpend : ∀ q ∈ S, X.pend q = Y.pend q)
    (hmem : ∀ r, X.mem () r = Y.mem () r ∨
      (wvals (ps.map (I.wOf X)) r ≠ [] ∧ ℓ ≤ (wvals (ps.map (I.wOf X)) r).length)) :
    ∃ X' Y', I.runFrom X (blockWrite ps) = some X' ∧ I.runFrom Y (blockWrite ps) = some Y' ∧
      AgreeOn S X' Y' := by
  obtain ⟨X', h1, h2, h3, h4, h5⟩ := runFrom_block ps X hnd hpo
  obtain ⟨Y', g1, g2, g3, g4, g5⟩ := runFrom_block ps Y hnd (fun p hp => by
    obtain ⟨w, hw⟩ := hpo p hp
    exact ⟨w, hw.congr (hloc p (hpS p hp)) (hpend p (hpS p hp))⟩)
  have hws : ps.map (I.wOf Y) = ps.map (I.wOf X) :=
    List.map_congr_left (fun p hp => (wOf_congr (hloc p (hpS p hp))).symm)
  refine ⟨X', Y', h1, g1, ⟨?_, fun q hq => ?_, fun q hq => ?_⟩⟩
  · funext i r
    cases i
    rw [h2, g2, hws, foldl_applyW, foldl_applyW]
    rcases hmem r with h | ⟨hne, hle⟩
    · rw [h]
    · exact foldl_bufWrite_eq hne hle _ _
  · by_cases hqp : q ∈ ps
    · rw [h5 q hqp, g5 q hqp, hloc q hq]
    · rw [h4 q hqp, g4 q hqp, hloc q hq]
  · rw [h3, g3, hpend q hq]

end Cslib.SharedMemory.Impl
