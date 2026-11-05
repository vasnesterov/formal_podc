import Papers.PODC2020.StoreCollectChurn.SnapshotGlobal

/-!
# High-level operations of an execution of Algorithm 7 and their positions

Operation instances are CSLib's `OpId P = P × ℕ` (`(p, n)` = `n`-th operation of `p` in
`hist E`).  We locate their invocation and response events in `E`.
-/

namespace Podc.StoreCollectChurn.Snap

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {P V : Type} [DecidableEq P]

/-- Is the node idle? -/
@[simp] def PC.isIdle : PC (P := P) (V := V) → Bool
  | .idle => true
  | _ => false

variable {E : List (Ev P V)}

/-- High-level invocations of `p` (as labels of `hist E`). -/
def invG (p : P) (e : Ev P V) : Option (snapSpec P V).Op := e.toLabel.invOf p

/-- High-level responses of `p`. -/
def retG (p : P) (e : Ev P V) : Option (snapSpec P V).Resp := e.toLabel.retOf p

lemma opsOf_hist (p : P) : opsOf (hist E) p = E.filterMap (invG p) := by
  simp only [opsOf, hist, List.filterMap_map]; rfl

lemma respsOf_hist (p : P) : respsOf (hist E) p = E.filterMap (retG p) := by
  simp only [respsOf, hist, List.filterMap_map]; rfl

lemma invG_eq_none_of_proc_ne {p : P} {e : Ev P V} (h : e.proc ≠ p) : invG p e = none := by
  unfold invG; exact Label.invOf_eq_none_of_proc_ne (by
    rcases e with ⟨q, _ | v⟩ | ⟨q, r⟩ | c <;> simpa [Ev.toLabel, Label.proc, Ev.proc] using h)

lemma retG_eq_none_of_proc_ne {p : P} {e : Ev P V} (h : e.proc ≠ p) : retG p e = none := by
  unfold retG; exact Label.retOf_eq_none_of_proc_ne (by
    rcases e with ⟨q, _ | v⟩ | ⟨q, r⟩ | c <;> simpa [Ev.toLabel, Label.proc, Ev.proc] using h)

@[simp] lemma invG_hinv_scan (p : P) : invG p (.hinv p .scan : Ev P V) = some .scan := by
  simp only [invG, Ev.toLabel, Label.invOf, ite_eq_left]
@[simp] lemma invG_hinv_update (p : P) (v : V) :
    invG p (.hinv p (.update v) : Ev P V) = some (.update p v) := by
  simp only [invG, Ev.toLabel, Label.invOf, ite_eq_left]
@[simp] lemma invG_hret (p q : P) (r : P → Option V) : invG p (.hret q r : Ev P V) = none := rfl
@[simp] lemma invG_sc (p : P) (c : SCEv P (SCVal P V)) : invG p (.sc c : Ev P V) = none := rfl
@[simp] lemma retG_hret (p : P) (r : P → Option V) : retG p (.hret p r : Ev P V) = some r := by
  simp only [retG, Ev.toLabel, Label.retOf, ite_eq_left]
@[simp] lemma retG_hinv (p q : P) (o : HOp V) : retG p (.hinv q o : Ev P V) = none := by
  rcases o <;> rfl
@[simp] lemma retG_sc (p : P) (c : SCEv P (SCVal P V)) : retG p (.sc c : Ev P V) = none := rfl

lemma isIdle_finishScan (s : LState P V) (emb : Option V) (W : P → Option V) :
    (finishScan s emb W).pc.isIdle = false := by
  cases emb <;> rfl

/-- Counting effect of one local step. -/
lemma lstep_count (pk : Pick P V) {p : P} {s s' : LState P V} {e : Ev P V}
    (hs : lstep pk p s e = some s') (hp : e.proc = p) :
    (invG p e).toList.length + (if s.pc.isIdle then 0 else 1) =
      (retG p e).toList.length + (if s'.pc.isIdle then 0 else 1) := by
  rcases hpc : s.pc with _ | emb | emb | emb | ⟨emb, _ | _⟩ | emb | W | v | v | _ | _ | _ <;>
    rcases e with ⟨q, _ | v'⟩ | ⟨q, r⟩ | ⟨⟨q, x⟩ | q | q | ⟨q, W'⟩⟩ <;>
    simp only [lstep, hpc, reduceCtorEq] at hs <;>
    simp only [Ev.proc, SCEv.proc] at hp <;> subst hp
  all_goals (try split_ifs at hs)
  all_goals (try split at hs)
  all_goals first
    | (obtain rfl := Option.some.inj hs
       first
        | (simp <;> rfl)
        | (cases emb <;> simp [finishScan]))
    | cases hs

/-- Each node alternates invocations and responses: it has one pending operation iff it is not
idle. -/
theorem count_of_run (pk : Pick P V) :
    ∀ i ≤ E.length, ∀ c, run pk (E.take i) = some c → ∀ p,
      fIdx (invG p) E i = fIdx (retG p) E i + (if (c p).pc.isIdle then 0 else 1) := by
  intro i
  induction i with
  | zero =>
    intro _ c hc p
    simp only [List.take_zero, run, List.foldl_nil, Option.some.injEq] at hc
    subst hc; simp [fIdx, LState.init, PC.isIdle]
  | succ i ih =>
    intro hi c' hc' p
    rw [run_take_succ pk (by omega)] at hc'
    rcases hc : run pk (E.take i) with _ | c
    · rw [hc] at hc'; simp at hc'
    rw [hc] at hc'
    have he : E[i]? = some E[i] := List.getElem?_eq_getElem (by omega)
    have IH := ih (by omega) c hc
    simp only [Option.bind_some, gstep, Option.map_eq_some_iff] at hc'
    obtain ⟨s', hs, rfl⟩ := hc'
    rw [fIdx_succ _ he, fIdx_succ _ he]
    by_cases hq : p = E[i].proc
    · subst hq
      rw [Function.update_self]
      have h1 := IH E[i].proc
      have h2 := lstep_count pk hs rfl
      omega
    · rw [Function.update_of_ne hq, invG_eq_none_of_proc_ne (Ne.symm hq),
        retG_eq_none_of_proc_ne (Ne.symm hq)]
      simpa using IH p

end Podc.StoreCollectChurn.Snap

