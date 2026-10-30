import Papers.PODC2025.AuditingWithoutLeaks.Inv

/-!
# Common tools for the indistinguishability arguments (Lemmas 6 and 7)

The proofs of Lemmas 6 and 7 of Attiya et al. (PODC 2025) transform an execution of Algorithm 1
into another one that a reader `p_j` cannot distinguish from it. The transformed execution is
built step by step along a *simulation relation* between configurations. Processes whose view
does not matter (auditors, other readers) only need to follow the same control flow; their
local states are compared through `skel`, which erases all values (audit sets, read values,
tracking bits of stored triples) and keeps the control data (sequence numbers, loop indices).
-/

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au]

section Skel

variable (d : V)

/-- Erase the value of a reader's `(prev_sn, prev_val)`. -/
def skP (prev : Option (ℕ × V)) : Option (ℕ × V) := prev.map (fun x => (x.1, d))

/-- Keep only the sequence number of a triple. -/
def skR (r : RVal m V) : RVal m V := ⟨r.seq, d, fun _ => false⟩

/-- The control skeleton of a local state: values (read values, audit sets, the value and the
tracking bits of triples held by auditors) are erased. Writer states are kept. -/
def skel : Loc m V → Loc m V
  | .rIdle prev => .rIdle (skP d prev)
  | .rSN prev => .rSN (skP d prev)
  | .rFX prev y => .rFX (skP d prev) y
  | .rCAS prev sn _ => .rCAS (skP d prev) sn d
  | .rRet prev _ => .rRet (skP d prev) d
  | .wIdle => .wIdle
  | .wSN v => .wSN v
  | .wR v sn => .wR v sn
  | .wV v sn r => .wV v sn r
  | .wB v sn r todo => .wB v sn r todo
  | .wCAS v sn r => .wCAS v sn r
  | .wHelp sn => .wHelp sn
  | .wRet => .wRet
  | .aIdle _ lsa => .aIdle ∅ lsa
  | .aR _ lsa => .aR ∅ lsa
  | .aV _ r s => .aV ∅ (skR d r) s
  | .aB _ r s _ i => .aB ∅ (skR d r) s none i
  | .aCAS _ r => .aCAS ∅ (skR d r)
  | .aRet _ lsa => .aRet ∅ lsa

lemma skP_map_fst {prev prev' : Option (ℕ × V)} (h : skP d prev' = skP d prev) :
    prev'.map Prod.fst = prev.map Prod.fst := by
  rcases prev with _ | ⟨a, b⟩ <;> rcases prev' with _ | ⟨a', b'⟩ <;> simp_all [skP]

/-- The continuation of a reader after reading `SN` (line 2). -/
lemma skel_rSN_next {prev prev' : Option (ℕ × V)} (h : skP d prev' = skP d prev) (y : ℕ) :
    skel (m := m) d (if prev'.map Prod.fst = some y then
        (match prev' with | some (_, pv) => Loc.rRet prev' pv | none => Loc.rFX prev' y)
      else Loc.rFX prev' y) =
    skel d (if prev.map Prod.fst = some y then
        (match prev with | some (_, pv) => Loc.rRet prev pv | none => Loc.rFX prev y)
      else Loc.rFX prev y) := by
  rcases prev with _ | ⟨a, b⟩ <;> rcases prev' with _ | ⟨a', b'⟩ <;> simp_all [skP, skel] <;>
    split_ifs <;> simp_all [skel, skP]

variable {rnd rnd' : ℕ → Fin m → Bool}

lemma skel_aNext {A A' : Set (Fin m × V)} {r r' : RVal m V} (h : r'.seq = r.seq) (s : ℕ) :
    skel d (aNext rnd' A' r' s) = skel d (aNext rnd A r s) := by
  simp only [aNext, h]; split_ifs <;> simp [skel, skR, h]

lemma skel_aVnext {A A' : Set (Fin m × V)} {r r' : RVal m V} (h : r'.seq = r.seq) (s : ℕ)
    (val val' : Option V) :
    skel d (aVnext rnd' A' r' s val') = skel d (aVnext rnd A r s val) := by
  simp only [aVnext]; split_ifs
  · simp [skel, skR, h]
  · exact skel_aNext d h _

lemma skel_aBnext {A A' : Set (Fin m × V)} {r r' : RVal m V} (h : r'.seq = r.seq) (s : ℕ)
    (val val' : Option V) (i : Fin m) :
    skel d (aBnext rnd' A' r' s val' i) = skel d (aBnext rnd A r s val i) := by
  simp only [aBnext]; split_ifs
  · simp [skel, skR, h]
  · exact skel_aNext d h _

end Skel

section Obs

variable {v₀ : V} {rnd : ℕ → Fin m → Bool}

lemma obsStep_tau_self {C : Cfg m W Au V v₀} {p : Proc m W Au} {i : Obj m}
    {o : (BO m V v₀ i).Op} {k : (BO m V v₀ i).Resp → Loc m V}
    (hact : (alg1 (W := W) (Au := Au) rnd v₀).act p (C.loc p) = .access i o k) :
    (alg1 (W := W) (Au := Au) rnd v₀).obsStep C p (.tau p) =
      some (.tau i ((BO m V v₀ i).δ (C.mem i) o).2) := by
  simp [Impl.obsStep, hact]

end Obs

end Podc.AuditingWithoutLeaks
