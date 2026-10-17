import Papers.PODC2025.TwoStepConsensusLB.Impl
import Papers.PODC2025.TwoStepConsensusLB.Fig1Protocol

/-!
# The concrete proposal (lines 26–38) refines the abstract relation `Fig1.Select`

`proposal_select`: if the concrete leader computes `proposal n f e L fb = some w` from a list `L`
of `1B` reports with pairwise distinct senders, then `Fig1.Select cfg Q rep fb w` holds for the
set `Q` of senders and their reports `rep` (provided `n - f - e ≥ 1`).
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus.Impl

open _root_.Cslib.CrashPartialSync

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder V]

/-- A concrete `1B` report as an abstract one. -/
def toSnap (d : OneB P V) : Fig1.Snap P V := ⟨d.vbal, d.val, d.prop, d.dec⟩

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 :=
  List.le_max_of_le' 0 h le_rfl

theorem card_toFinset_map_fst {L : List (P × OneB P V)} (hnd : (L.map Prod.fst).Nodup)
    (p : P × OneB P V → Bool) :
    ((L.filter p).map Prod.fst).toFinset.card = (L.filter p).length := by
  rw [List.toFinset_card_of_nodup]
  · simp
  · exact (hnd.sublist (List.Sublist.map _ (List.filter_sublist)))

section Select

variable (cfg : Fig1.Config P V) {L : List (P × OneB P V)} (hnd : (L.map Prod.fst).Nodup)
  {rep : P → Fig1.Snap P V} (hrep : ∀ x ∈ L, rep x.1 = toSnap x.2)
include hnd hrep

theorem rep_of_mem_Q {q : P} (hq : q ∈ (L.map Prod.fst).toFinset) :
    ∃ x ∈ L, x.1 = q ∧ rep q = toSnap x.2 := by
  simp only [List.mem_toFinset, List.mem_map] at hq
  obtain ⟨x, hx, rfl⟩ := hq
  exact ⟨x, hx, rfl, hrep x hx⟩

/-- The (maximal) set of voters for `w` in `R` (lines 28, 33, 35). -/
private def votersFin (L : List (P × OneB P V)) (w : V) : Finset P :=
  ((L.filter fun x => x.2.prop.all (fun r => r ∉ L.map Prod.fst) && decide (x.2.val = some w)).map
    Prod.fst).toFinset

theorem votersIn_iff {w : V} {S : Finset P} :
    Fig1.VotersIn (L.map Prod.fst).toFinset rep w S ↔ S ⊆ votersFin L w := by
  constructor
  · rintro ⟨hSQ, hS⟩ q hq
    obtain ⟨x, hx, rfl, hr⟩ := rep_of_mem_Q hnd hrep (hSQ hq)
    obtain ⟨hR, hv⟩ := hS _ hq
    rw [hr] at hR hv
    simp only [votersFin, List.mem_toFinset, List.mem_map, List.mem_filter, Bool.and_eq_true,
      decide_eq_true_eq]
    refine ⟨x, ⟨hx, ?_, hv⟩, rfl⟩
    rw [Option.all_eq_true]
    intro r hr'
    have := hR r hr'
    simpa using this
  · intro hS
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · have := hS hq
      simp only [votersFin, List.mem_toFinset, List.mem_map, List.mem_filter] at this
      obtain ⟨x, ⟨hx, -⟩, rfl⟩ := this
      simp only [List.mem_toFinset, List.mem_map]
      exact ⟨x, hx, rfl⟩
    · have := hS hq
      simp only [votersFin, List.mem_toFinset, List.mem_map, List.mem_filter, Bool.and_eq_true,
        decide_eq_true_eq] at this
      obtain ⟨x, ⟨hx, h1, h2⟩, rfl⟩ := this
      rw [hrep x hx]
      refine ⟨fun r hr' => ?_, h2⟩
      rw [Option.all_eq_true] at h1
      have := h1 r hr'
      simpa using this

theorem votersFin_card (w : V) :
    (votersFin L w).card =
      votes (L.filter fun x => x.2.prop.all fun r => r ∉ L.map Prod.fst) w := by
  unfold votersFin votes
  rw [card_toFinset_map_fst hnd, List.filter_filter]
  congr 2
  funext x
  simp [Bool.and_comm]

theorem cond33_iff {w : V} :
    Fig1.Cond33 cfg (L.map Prod.fst).toFinset rep w ↔
      Fintype.card P - cfg.f - cfg.e <
        votes (L.filter fun x => x.2.prop.all fun r => r ∉ L.map Prod.fst) w := by
  rw [← votersFin_card hnd hrep]
  constructor
  · rintro ⟨S, hS, hc⟩
    exact hc.trans_le (Finset.card_le_card ((votersIn_iff hnd hrep).1 hS))
  · intro h
    exact ⟨_, (votersIn_iff hnd hrep).2 subset_rfl, h⟩

theorem cond35_iff {w : V} :
    Fig1.Cond35 cfg (L.map Prod.fst).toFinset rep w ↔
      Fintype.card P - cfg.f - cfg.e ≤
        votes (L.filter fun x => x.2.prop.all fun r => r ∉ L.map Prod.fst) w := by
  rw [← votersFin_card hnd hrep]
  constructor
  · rintro ⟨S, hS, hc⟩
    exact hc ▸ Finset.card_le_card ((votersIn_iff hnd hrep).1 hS)
  · intro h
    obtain ⟨S, hS, hc⟩ := Finset.exists_subset_card_eq h
    exact ⟨S, (votersIn_iff hnd hrep).2 hS, hc⟩

theorem mem_cands_of_votes {w : V}
    (h : 0 < votes (L.filter fun x => x.2.prop.all fun r => r ∉ L.map Prod.fst) w) :
    w ∈ (L.filter fun x => x.2.prop.all fun r => r ∉ L.map Prod.fst).filterMap
      fun x => x.2.val := by
  unfold votes at h
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos h
  rw [List.mem_filter] at hx
  rw [List.mem_filterMap]
  exact ⟨x, hx.1, by simpa using hx.2⟩

/-- **The concrete proposal satisfies `Select`.** -/
theorem proposal_select (hN : 1 ≤ Fintype.card P - cfg.f - cfg.e) {fb : Option V} {w : V}
    (h : proposal (Fintype.card P) cfg.f cfg.e L fb = some w) :
    Fig1.Select cfg (L.map Prod.fst).toFinset rep fb w := by
  have hQ : ∀ x ∈ L, x.1 ∈ (L.map Prod.fst).toFinset := fun x hx => by
    simp only [List.mem_toFinset, List.mem_map]; exact ⟨x, hx, rfl⟩
  unfold proposal at h
  split at h
  · rename_i d hd
    obtain ⟨x, hx, hxd⟩ := List.exists_of_findSome?_eq_some hd
    cases h
    exact .l30 (hQ x hx) (by rw [hrep x hx]; exact hxd)
  · rename_i hd
    rw [List.findSome?_eq_none_iff] at hd
    have hdec : ∀ q ∈ (L.map Prod.fst).toFinset, (rep q).decided = none := by
      intro q hq
      obtain ⟨x, hx, rfl, hr⟩ := rep_of_mem_Q hnd hrep hq
      rw [hr]; exact hd x hx
    simp only at h
    split_ifs at h with hb
    · obtain ⟨z, hz, hzv⟩ := Option.bind_eq_some_iff.1 h
      have hz1 := List.mem_of_find?_eq_some hz
      have hz2 := List.find?_some hz
      simp only [decide_eq_true_eq] at hz2
      refine .l32 hdec (hQ z hz1) (fun q hq => ?_) ?_ ?_
      · obtain ⟨x, hx, rfl, hr⟩ := rep_of_mem_Q hnd hrep hq
        rw [hr, hrep z hz1]
        simp only [toSnap]
        rw [hz2]
        exact le_foldr_max (List.mem_map.2 ⟨x, hx, rfl⟩)
      · rw [hrep z hz1]; simp only [toSnap]; omega
      · rw [hrep z hz1]; exact hzv
    · have hvbal : ∀ q ∈ (L.map Prod.fst).toFinset, (rep q).vbal = 0 := by
        intro q hq
        obtain ⟨x, hx, rfl, hr⟩ := rep_of_mem_Q hnd hrep hq
        rw [hr]
        have := le_foldr_max (List.mem_map.2 ⟨x, hx, rfl⟩ : x.2.vbal ∈ L.map fun x => x.2.vbal)
        simp only [toSnap]; omega
      split at h
      · rename_i v hv
        cases h
        have := (List.max?_eq_some_iff.1 hv).1
        rw [List.mem_filter, decide_eq_true_eq] at this
        exact .l34 hdec hvbal ((cond33_iff cfg hnd hrep).2 this.2)
      · rename_i hv
        rw [List.max?_eq_none_iff, List.filter_eq_nil_iff] at hv
        have h33 : ∀ w', ¬ Fig1.Cond33 cfg (L.map Prod.fst).toFinset rep w' := by
          intro w' hw'
          rw [cond33_iff cfg hnd hrep] at hw'
          exact hv w' (mem_cands_of_votes hnd hrep (by omega)) (by simpa using hw')
        split at h
        · rename_i v hv'
          cases h
          have := List.max?_eq_some_iff.1 hv'
          have h1 := this.1
          rw [List.mem_filter, decide_eq_true_eq] at h1
          refine .l36 hdec hvbal h33 ((cond35_iff cfg hnd hrep).2 h1.2.ge) fun w' hw' => ?_
          rw [cond35_iff cfg hnd hrep] at hw'
          have h3 : ¬ Fintype.card P - cfg.f - cfg.e <
              votes (L.filter fun x => x.2.prop.all fun r => r ∉ L.map Prod.fst) w' := by
            intro h'; exact h33 w' ((cond33_iff cfg hnd hrep).2 h')
          refine this.2 w' (List.mem_filter.2 ⟨mem_cands_of_votes hnd hrep (by omega), ?_⟩)
          simp only [decide_eq_true_eq]; omega
        · rename_i hv'
          rw [List.max?_eq_none_iff, List.filter_eq_nil_iff] at hv'
          refine .l38 hdec hvbal h33 (fun w' hw' => ?_) h
          rw [cond35_iff cfg hnd hrep] at hw'
          have h3 : ¬ Fintype.card P - cfg.f - cfg.e <
              votes (L.filter fun x => x.2.prop.all fun r => r ∉ L.map Prod.fst) w' := by
            intro h'; exact h33 w' ((cond33_iff cfg hnd hrep).2 h')
          exact hv' w' (mem_cands_of_votes hnd hrep (by omega))
            (by simp only [decide_eq_true_eq]; omega)

end Select

end TwoStepConsensus.Impl
