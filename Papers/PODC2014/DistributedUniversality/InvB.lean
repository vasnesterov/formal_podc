import Papers.PODC2014.DistributedUniversality.Rounds

/-!
# The safety invariant (Lemmas 1–3 of the paper)

`InvB` states that all local histories, `GSTATE` registers and their copies are prefixes of a single
duplicate-free sequence `G m` per object (the paper's "valid histories": Lemma 3 and Lemma 2), and
the knowledge invariant behind it: once a process has completed round `ρ + 1`, it knows the
operation committed in round `ρ` (`know`).
-/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}

/-- After line 7 (lines 16–31). -/
def pastLoc : PC → Prop
  | .upd _ => True
  | .write => True
  | _ => False

/-- `GSTATE[q]` has been read in the current round. -/
def collected (pc : PC) (q : Fin n) : Prop :=
  match pc with
  | .collect q' => q.val < q'
  | .loc => True
  | .upd _ => True
  | .write => True
  | _ => False

/-- The process has executed lines 16–28 for object `m` in round `ρ`. -/
def passedUpd (l : Loc n k) (ρ : ℕ) (m : Fin k) : Prop :=
  ρ < l.r ∨ (ρ = l.r ∧ pastUpd l.pc m)

@[simp] lemma pastLoc_upd (m : ℕ) : pastLoc (.upd m) := trivial
@[simp] lemma pastLoc_write : pastLoc .write := trivial
@[simp] lemma not_pastLoc_init : ¬ pastLoc .init := id
@[simp] lemma not_pastLoc_n1Inv (m : ℕ) : ¬ pastLoc (.n1Inv m) := id
@[simp] lemma not_pastLoc_n1Resp (m : ℕ) : ¬ pastLoc (.n1Resp m) := id
@[simp] lemma not_pastLoc_scInv : ¬ pastLoc .scInv := id
@[simp] lemma not_pastLoc_scResp : ¬ pastLoc .scResp := id
@[simp] lemma not_pastLoc_acInv (j : ℕ) : ¬ pastLoc (.acInv j) := id
@[simp] lemma not_pastLoc_acResp (j : ℕ) : ¬ pastLoc (.acResp j) := id
@[simp] lemma not_pastLoc_collect (q : ℕ) : ¬ pastLoc (.collect q) := id
@[simp] lemma not_pastLoc_loc : ¬ pastLoc .loc := id

@[simp] lemma collected_collect (q' : ℕ) (q : Fin n) : collected (.collect q') q ↔ q.val < q' :=
  Iff.rfl
@[simp] lemma collected_loc (q : Fin n) : collected .loc q := trivial
@[simp] lemma collected_upd (m : ℕ) (q : Fin n) : collected (.upd m) q := trivial
@[simp] lemma collected_write (q : Fin n) : collected .write q := trivial

/-- The safety invariant. -/
structure InvB (M : Mode) (s : St n k) : Prop where
  G_nodup : ∀ m, (s.G m).Nodup
  born_len : ∀ m, (s.born m).length = (s.G m).length
  hist_G : ∀ i m, (s.loc i).hist m <+: s.G m
  gst_hist : ∀ i m, s.gst i m <+: (s.loc i).hist m
  gs_gst : ∀ i q m, (s.loc i).gs q m <+: s.gst q m
  hist_eq : ∀ i m, ¬ pastLoc (s.loc i).pc → (s.loc i).hist m = s.gst i m
  know : ∀ i ρ m V, Unif s ρ m V → passedUpd (s.loc i) (ρ + 1) m → V ∈ (s.loc i).hist m
  opPre : ∀ i m, 2 ≤ (s.loc i).r → ¬ pastUpd (s.loc i).pc m →
    ∃ b v, s.finR ((s.loc i).r - 1) m i = some (b, v) ∧ ((s.loc i).oper m = v ∨ v ∈ s.gst i m)
  opPost : ∀ i m, pastUpd (s.loc i).pc m →
    ∃ b v, s.finR (s.loc i).r m i = some (b, v) ∧
      ((s.loc i).oper m = v ∨ v ∈ (s.loc i).hist m)
  PIa : ∀ ρ m V j W, Unif s ρ m V → s.opRec (ρ + 1) m j = some W → W ≠ V →
    ∃ q, V ∈ s.gst q m
  CI : ∀ i m V, 2 ≤ (s.loc i).r → pastAC (s.loc i).pc → Unif s ((s.loc i).r - 1) m V →
    s.finR (s.loc i).r m i ≠ some (true, V) →
    (∃ q, V ∈ s.gst q m ∧ (collected (s.loc i).pc q → V ∈ (s.loc i).gs q m)) ∧
    (pastLoc (s.loc i).pc → V ∈ (s.loc i).hist m)
  GS1 : ∀ m (x β : ℕ) (e : Op n), (s.born m)[x]? = some β → (s.G m)[x]? = some e →
    ∃ j, s.finR β m j = some (true, e)
  GS3 : ∀ m (x β ρ : ℕ) V, (s.born m)[x]? = some β → ρ + 1 < β → Unif s ρ m V →
    V ∈ (s.G m).take x
  GS4 : ∀ m (x β ρ : ℕ) V, (s.born m)[x]? = some β → ρ + 1 = β → Unif s ρ m V →
    V ∈ (s.G m).take (x + 1)

theorem invB_init (M : Mode) : InvB M (init : St n k) := by
  constructor <;> simp [init, initLoc, Unif, passedUpd]

end Podc.DistributedUniversality
