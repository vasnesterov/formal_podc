import Papers.PODC2020.StoreCollectChurn.SnapshotStep

/-!
# The invariant holds along every execution allowed by Algorithm 7

`past_of_run`: in an execution allowed by the code whose store-collect schedule is regular, every
store event and every response event satisfies `StoreFact` / `RetFact`.
-/

namespace Podc.StoreCollectChurn.Snap

set_option linter.unusedSectionVars false

variable {P V : Type} [DecidableEq P] {E : List (Ev P V)}

lemma foldl_none (pk : Pick P V) (l : List (Ev P V)) :
    l.foldl (fun c e => c.bind (gstep pk · e)) none = none := by
  induction l with
  | nil => rfl
  | cons e l ih => simpa using ih

lemma run_take_succ (pk : Pick P V) {i : ℕ} (hi : i < E.length) :
    run pk (E.take (i + 1)) = (run pk (E.take i)).bind (gstep pk · E[i]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [run, List.foldl_append, Option.toList_some, List.foldl_cons, List.foldl_nil]

lemma run_take_ne_none (pk : Pick P V) (h : run pk E ≠ none) {i : ℕ} (hi : i ≤ E.length) :
    run pk (E.take i) ≠ none := by
  intro h0
  apply h
  rw [← List.take_append_drop i E, run, List.foldl_append]
  rw [run] at h0
  rw [h0, foldl_none]

lemma NInv.init (p : P) : NInv E 0 p LState.init := by
  refine ⟨fun a ha => by omega, le_rfl, le_rfl, ⟨?_, fun _ => rfl, fun h => by
    simp [LState.init] at h⟩, ?_⟩
  · simp [LState.init, valOf]
  · simp [PCInv, LState.init, updCnt, fIdx]

/-- The invariant along every prefix of an allowed execution with a regular schedule. -/
theorem inv_of_run (pk : Pick P V) (hreg : Regular (scSched E)) :
    ∀ i ≤ E.length, ∀ c, run pk (E.take i) = some c → (∀ p, NInv E i p (c p)) ∧ Past E i := by
  intro i
  induction i with
  | zero =>
    intro _ c hc
    simp only [List.take_zero, run, List.foldl_nil, Option.some.injEq] at hc
    subst hc
    exact ⟨fun p => NInv.init p, fun a ha => by omega, fun h hh => by omega⟩
  | succ i ih =>
    intro hi c' hc'
    rw [run_take_succ pk (by omega)] at hc'
    rcases hc : run pk (E.take i) with _ | c
    · rw [hc] at hc'; simp at hc'
    rw [hc] at hc'
    obtain ⟨hI, hpast⟩ := ih (by omega) c hc
    have he : E[i]? = some E[i] := List.getElem?_eq_getElem (by omega)
    simp only [Option.bind_some, gstep, Option.map_eq_some_iff] at hc'
    obtain ⟨s', hs, rfl⟩ := hc'
    obtain ⟨h1, h2, h3⟩ := NInv.step pk hreg hpast (hI E[i].proc) he rfl hs
    refine ⟨fun q => ?_, fun a ha q x hx => ?_, fun h hh q r hr => ?_⟩
    · by_cases hq : q = E[i].proc
      · subst hq; simpa using h1
      · rw [Function.update_of_ne hq]
        exact (hI q).frame he (Ne.symm hq)
    · rcases Nat.lt_or_ge a i with hai | hai
      · exact hpast.1 a hai q x hx
      · obtain rfl : a = i := by omega
        have heq := hx.proc he
        have hq : q = E[a].proc := by rw [heq]; rfl
        subst hq; exact h2 x hx
    · rcases Nat.lt_or_ge h i with hhi | hhi
      · exact hpast.2 h hhi q r hr
      · obtain rfl : h = i := by omega
        have heq : E[h] = .hret q r := Option.some.inj (he.symm.trans hr)
        have hq : q = E[h].proc := by rw [heq]; rfl
        subst hq; exact h3 r hr

/-- Facts about all events of an allowed execution with a regular schedule. -/
theorem past_of_run (pk : Pick P V) (hreg : Regular (scSched E)) (hrun : run pk E ≠ none) :
    Past E E.length := by
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 (run_take_ne_none pk hrun le_rfl)
  exact (inv_of_run pk hreg _ le_rfl c hc).2

end Podc.StoreCollectChurn.Snap
