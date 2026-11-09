import Papers.PODC2012.OptimismConcurrency.ImplModel

/-!
# Lemmas on histories (extension by one event)

How `clientSt`, the operations of a process (`splitOps`, `restrictPX`), the high-level history
`hl`, and the runs `seqRun`, `honRun` behave when one event is appended to a history.
-/

namespace Podc.OptimismConcurrency

open Cslib.SharedMemory

section General

variable {P X Op Res Obj Val : Type}

/-- The step function of `splitOps`. -/
def splitF (e : Ev P X Op Res Obj Val)
    (acc : Hist P X Op Res Obj Val × List (Hist P X Op Res Obj Val)) :
    Hist P X Op Res Obj Val × List (Hist P X Op Res Obj Val) :=
  if e.isInv then ([], (e :: acc.1) :: acc.2) else (e :: acc.1, acc.2)

lemma splitOps_eq (l : Hist P X Op Res Obj Val) : splitOps l = (l.foldr splitF ([], [])).2 := rfl

lemma modifyLast_id' {α : Type*} (S : List α) : S.modifyLast (fun x => x) = S := by
  rcases List.eq_nil_or_concat S with rfl | ⟨L, b, rfl⟩
  · rfl
  · rw [List.concat_eq_append, List.modifyLast_concat]

/-- Attach the partial segment `a` to the last segment, and the segments `b` after. -/
def glue (a : Hist P X Op Res Obj Val) (b : List (Hist P X Op Res Obj Val)) :
    Hist P X Op Res Obj Val × List (Hist P X Op Res Obj Val) →
      Hist P X Op Res Obj Val × List (Hist P X Op Res Obj Val)
  | (f, []) => (f ++ a, b)
  | (f, S) => (f, S.modifyLast (· ++ a) ++ b)

lemma splitF_glue (x : Ev P X Op Res Obj Val) (a : Hist P X Op Res Obj Val)
    (b : List (Hist P X Op Res Obj Val))
    (fs : Hist P X Op Res Obj Val × List (Hist P X Op Res Obj Val)) :
    splitF x (glue a b fs) = glue a b (splitF x fs) := by
  rcases fs with ⟨f, S⟩
  cases S with
  | nil =>
    by_cases hx : x.isInv
    · simp only [splitF, glue, hx, ↓reduceIte]
      rw [show [x :: f] = [] ++ [x :: f] from rfl, List.modifyLast_concat]; simp
    · simp [splitF, glue, hx]
  | cons s S =>
    by_cases hx : x.isInv
    · simp only [glue, splitF, hx, ↓reduceIte]
      rw [show ((x :: f) :: s :: S) = [x :: f] ++ (s :: S) from rfl,
        List.modifyLast_append_of_right_ne_nil _ _ _ (by simp)]
      simp
    · simp [splitF, glue, hx]

lemma foldr_splitF (l : Hist P X Op Res Obj Val) (a : Hist P X Op Res Obj Val)
    (b : List (Hist P X Op Res Obj Val)) :
    l.foldr splitF (a, b) = glue a b (l.foldr splitF ([], [])) := by
  induction l with
  | nil => simp [glue]
  | cons x l ih => simp only [List.foldr_cons, ih, splitF_glue]

lemma splitOps_append_inv (l : Hist P X Op Res Obj Val) (e : Ev P X Op Res Obj Val)
    (he : e.isInv = true) : splitOps (l ++ [e]) = splitOps l ++ [[e]] := by
  rw [splitOps_eq, List.foldr_append]
  simp only [List.foldr_cons, List.foldr_nil, splitF, he, ↓reduceIte]
  rw [foldr_splitF, splitOps_eq]
  rcases List.foldr splitF ([], []) l with ⟨f, _ | ⟨s, S⟩⟩
  · simp [glue]
  · simp only [glue, List.append_nil]
    rw [modifyLast_id' (s :: S)]

lemma splitOps_append_non (l : Hist P X Op Res Obj Val) (e : Ev P X Op Res Obj Val)
    (he : e.isInv = false) : splitOps (l ++ [e]) = (splitOps l).modifyLast (· ++ [e]) := by
  rw [splitOps_eq, List.foldr_append]
  simp only [List.foldr_cons, List.foldr_nil, splitF, he, Bool.false_eq_true, ↓reduceIte]
  rw [foldr_splitF, splitOps_eq]
  rcases List.foldr splitF ([], []) l with ⟨f, _ | ⟨s, S⟩⟩
  · simp [glue]; rfl
  · simp [glue]

/-- `S₀ ++ H|π ∈ Σ` follows from `S₀ ++ (events of π) ∈ Σ` for a prefix-closed `Σ`. -/
lemma dropAbort_prefix (l : Hist P X Op Res Obj Val) : dropAbort l <+: l := by
  unfold dropAbort
  split
  · exact (List.dropLast_prefix _).trans (List.dropLast_prefix _)
  · exact List.prefix_refl _

end General

variable {P : Type} [DecidableEq P]

lemma clientSt_append (H : LHist P) (e : LEv P) (p : P) :
    clientSt (H ++ [e]) p = if e.proc = p then cstep (clientSt H p) e else clientSt H p := by
  unfold clientSt; rw [List.filter_append]; by_cases h : e.proc = p <;> simp [h]

lemma restrictPX_append (H : LHist P) (e : LEv P) (p : P) :
    restrictPX (H ++ [e]) p () = restrictPX H p () ++ (if e.proc = p then [e] else []) := by
  unfold restrictPX; rw [List.filter_append]; by_cases h : e.proc = p <;> simp [h]

/-- The operations of `p` (lists of their events). -/
def opsP (H : LHist P) (p : P) : List (LHist P) := splitOps (restrictPX H p ())

/-- The events of the last operation of `p`. -/
def curOp (H : LHist P) (p : P) : LHist P := ((opsP H p).getLast?).getD []

lemma opsP_append (H : LHist P) (e : LEv P) (p : P) :
    opsP (H ++ [e]) p = if e.proc = p then
      (if e.isInv then opsP H p ++ [[e]] else (opsP H p).modifyLast (· ++ [e])) else opsP H p := by
  unfold opsP; rw [restrictPX_append]
  by_cases h : e.proc = p
  · simp only [h, ↓reduceIte]
    cases he : e.isInv
    · rw [splitOps_append_non _ _ he]; simp
    · rw [splitOps_append_inv _ _ he]; simp
  · simp [h]

lemma localView_eq (H : LHist P) (p : P) (k : ℕ) :
    localView H p () k = dropAbort ((opsP H p).getD k []) := rfl

lemma numOps_eq (H : LHist P) (p : P) : numOps H p () = (opsP H p).length := rfl

/-! ## Runs -/

lemma seqRun_append_la (c : SCfg P) (l₁ l₂ : LHist P) :
    seqRun c (l₁ ++ l₂) = (seqRun c l₁).bind (fun c' => seqRun c' l₂) := by
  induction l₁ generalizing c with
  | nil => simp [seqRun]
  | cons e l ih =>
    simp only [List.cons_append, seqRun, ih]
    cases seqStep c e <;> simp

lemma seqRun_singleton (c : SCfg P) (e : LEv P) : seqRun c [e] = seqStep c e := by
  simp only [seqRun]; cases seqStep c e <;> rfl

lemma sigLL_of_prefix {S T : LHist P} (h : S <+: T) (hT : T ∈ (SigLL : Set (LHist P))) :
    S ∈ (SigLL : Set (LHist P)) := by
  obtain ⟨U, rfl⟩ := h
  simp only [SigLL, Set.mem_ofPred_eq, seqRun_append_la] at hT ⊢
  cases h : seqRun scfg0 S <;> simp_all

lemma honRun_append_la (c : HCfg P) (l₁ l₂ : LHist P) :
    honRun c (l₁ ++ l₂) = (honRun c l₁).bind (fun c' => honRun c' l₂) := by
  induction l₁ generalizing c with
  | nil => simp [honRun]
  | cons e l ih =>
    simp only [List.cons_append, honRun, ih]
    cases honStep c e <;> simp

lemma honRun_concat (c : HCfg P) (l : LHist P) (e : LEv P) :
    honRun c (l ++ [e]) = (honRun c l).bind (fun c' => honStep c' e) := by
  rw [honRun_append_la]; cases honRun c l <;> simp [honRun]

lemma seqRun_concat (c : SCfg P) (l : LHist P) (e : LEv P) :
    seqRun c (l ++ [e]) = (seqRun c l).bind (fun c' => seqStep c' e) := by
  rw [seqRun_append_la]; cases seqRun c l <;> simp [seqRun_singleton]

/-! ## The high-level history without aborts -/

lemma hl_eq_of_noAbort (H : LHist P) (h : ∀ e ∈ H, e.isAbort = false) :
    hl H = H.filterMap toHW := by
  unfold hl
  induction H with
  | nil => rfl
  | cons e l ih =>
    have ih' := ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    simp only [lookFilter]
    split_ifs with hk
    · simp [List.filterMap_cons, ih']
    · rw [ih', List.filterMap_cons]
      cases e with
      | inv p x o =>
        exfalso; apply hk
        simp only [keepHL, Bool.not_eq_eq_eq_not, Bool.not_true, Option.any_eq_false]
        intro e' he'
        have := List.mem_of_find?_eq_some he'
        exact h e' (List.mem_cons_of_mem _ this)
      | res p x r => simp [keepHL] at hk
      | _ => rfl

lemma hl_concat (H : LHist P) (e : LEv P) (h : ∀ e' ∈ H ++ [e], e'.isAbort = false) :
    hl (H ++ [e]) = hl H ++ (toHW e).toList := by
  rw [hl_eq_of_noAbort _ h, hl_eq_of_noAbort _ (fun e' he' => h e' (by simp [he']))]
  rw [List.filterMap_append]
  cases he : toHW e <;> simp [he]

end Podc.OptimismConcurrency
