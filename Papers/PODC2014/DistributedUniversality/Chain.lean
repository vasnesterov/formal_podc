import Papers.PODC2014.DistributedUniversality.InvB

/-!
# The core step of Lemma 3: appending a committed operation keeps histories in one chain

When a process appends the operation `W` committed in its round `ρ` (line 18) to a local history
`h` that is a proper prefix of the global sequence `G`, then `W` is the next element of `G`.
-/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s : St n k}

theorem take_getElem_not_mem {α : Type*} {G : List α} (hG : G.Nodup) {x : ℕ} (hx : x < G.length) :
    G[x] ∉ G.take x := by
  intro hmem
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hmem
  rw [List.getElem_take] at hix
  have hi' : i < x := by simp at hi; omega
  have := (List.Nodup.getElem_inj_iff hG).1 hix
  omega

theorem chain_next (I : InvA M s) (B : InvB M s) (hM : M.Good) {i : Fin n} {m : Fin k}
    {mm : ℕ} (hpc : (s.loc i).pc = .upd mm) (htag : (s.loc i).tag m = true)
    (hnin : (s.loc i).acop m ∉ (s.loc i).hist m)
    (hne : (s.loc i).hist m ≠ s.G m) :
    ∃ hx : ((s.loc i).hist m).length < (s.G m).length,
      (s.G m)[((s.loc i).hist m).length] = (s.loc i).acop m := by
  set h := (s.loc i).hist m with hh
  set W := (s.loc i).acop m with hW
  set ρ := (s.loc i).r with hρ
  have hpre : h <+: s.G m := B.hist_G i m
  have hlt : h.length < (s.G m).length := by
    rcases Nat.lt_or_ge h.length (s.G m).length with hl | hl
    · exact hl
    · exact absurd (hpre.eq_of_length (le_antisymm hpre.length_le hl)) hne
  refine ⟨hlt, ?_⟩
  set x := h.length with hxdef
  have hbx : x < (s.born m).length := by rw [B.born_len]; exact hlt
  have htake : h = (s.G m).take x := List.prefix_iff_eq_take.1 hpre
  have hnodup := B.G_nodup m
  set e := (s.G m)[x] with he
  have he_notin : e ∉ h := by rw [htake]; exact take_getElem_not_mem hnodup hlt
  have hfin : s.finR ρ m i = some (true, W) := by
    rw [I.finR_loc i (by simp [hpc]) m, htag]
  have hβ' : (s.born m)[x]? = some (s.born m)[x] := List.getElem?_eq_getElem hbx
  have he' : (s.G m)[x]? = some e := List.getElem?_eq_getElem hlt
  set β := (s.born m)[x] with hβ
  obtain ⟨j, hj⟩ := B.GS1 m x β e hβ' he'
  have hρ1 : 1 ≤ ρ := I.finR_pos _ _ _ _ hfin
  rcases lt_trichotomy β ρ with hlt' | heq | hgt
  · -- e was committed in an earlier round
    have hU : Unif s β m e := I.unif_of_commit hM hj
    rcases Nat.lt_or_ge (β + 1) ρ with h1 | h1
    · have := B.know i β m e hU (Or.inl h1)
      exact absurd this he_notin
    · have h2 : β + 1 = ρ := by omega
      have hr2 : 2 ≤ ρ := by have := I.finR_pos _ _ _ _ hj; omega
      have hU' : Unif s (ρ - 1) m e := by
        have : ρ - 1 = β := by omega
        rw [this]; exact hU
      by_contra hWe
      have hne' : s.finR ρ m i ≠ some (true, e) := by
        rw [hfin]; intro hh'; simp at hh'; exact hWe hh'.symm
      have := (B.CI i m e hr2 (by simp [hpc]) hU' hne').2 (by simp [hpc])
      exact he_notin this
  · -- same round: the committed operation is unique
    rw [heq] at hj
    exact (I.finR_agree hM hfin hj)
  · -- e was committed in a later round: then the appender of e already knew W
    have hU : Unif s ρ m W := I.unif_of_commit hM hfin
    rcases Nat.lt_or_ge (ρ + 1) β with h1 | h1
    · have := B.GS3 m x β ρ W hβ' h1 hU
      rw [← htake] at this
      exact absurd this hnin
    · have h2 : ρ + 1 = β := by omega
      have := B.GS4 m x β ρ W hβ' h2 hU
      rw [List.take_succ, List.getElem?_eq_getElem hlt, ← htake] at this
      simp only [Option.toList_some, List.mem_append, List.mem_singleton] at this
      rcases this with h3 | h3
      · exact absurd h3 hnin
      · exact h3.symm

end Podc.DistributedUniversality
