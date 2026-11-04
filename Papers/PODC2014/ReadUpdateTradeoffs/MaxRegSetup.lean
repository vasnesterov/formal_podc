import Papers.PODC2014.ReadUpdateTradeoffs.Blocks
import Papers.PODC2014.ReadUpdateTradeoffs.UpdateLB
import Cslib.Computability.Distributed.SharedMemory.Objects.MaxRegister

/-!
# Setting of the max-register lower bound (Section 4 of Hendler–Khait, PODC'14)

* `Ess I W val i α C G E H` — the paper's "execution `E_i` with an `i`-step essential set `E`"
  (Definition 7), with halted processes `H`, strengthened by the block invariant `BlockOK`
  (needed to repair the proofs of Lemmas 4 and 6, see `Blocks.lean`).
* `ess_zero` — the base case (`E₀ = ⊥`, every writer essential).
* `ess_erase` — erasing essential processes (a sound version of Claim 1).
* linearizability facts about max registers (`read_lt`, `read_ge`);
* `solo_transfer` — a solo run only depends on the objects it accesses.
-/

namespace Podc.ReadUpdateTradeoffs

open Cslib.SharedMemory Cslib.SharedMemory.Awareness

/-! ### Max registers -/

lemma maxReg_runOps_lt {c : ℕ} : ∀ (os : List MaxOp) (q : ℕ), q < c →
    (∀ o ∈ os, ∀ x, o = .writeMax x → x < c) → maxRegObj.runOps q os < c := by
  intro os
  induction os with
  | nil => intro q hq _; exact hq
  | cons o os ih =>
    intro q hq hos
    rw [ObjSpec.runOps_cons]
    apply ih _ _ (fun o' h' => hos o' (List.mem_cons_of_mem _ h'))
    cases o with
    | writeMax x => simpa using ⟨hq, hos _ List.mem_cons_self x rfl⟩
    | readMax => simpa using hq

lemma maxReg_runOps_ge_self : ∀ (os : List MaxOp) (q : ℕ), q ≤ maxRegObj.runOps q os := by
  intro os
  induction os with
  | nil => intro q; exact le_rfl
  | cons o os ih =>
    intro q
    rw [ObjSpec.runOps_cons]
    refine le_trans ?_ (ih _)
    cases o with
    | writeMax x => simp
    | readMax => simp

lemma maxReg_runOps_ge : ∀ (os : List MaxOp) (q x : ℕ), MaxOp.writeMax x ∈ os →
    x ≤ maxRegObj.runOps q os := by
  intro os
  induction os with
  | nil => intro q x h; simp at h
  | cons o os ih =>
    intro q x h
    rw [ObjSpec.runOps_cons]
    rcases List.mem_cons.1 h with rfl | h
    · refine le_trans ?_ (maxReg_runOps_ge_self _ _); simp
    · exact ih _ x h

variable {P : Type} [DecidableEq P]

/-- In an execution in which every operation other than the read `(r, 0)` is a `writeMax` of a
value below `c ≥ 1`, the read returns a value below `c`. -/
lemma read_lt {γ : List (Label P maxRegObj)} {L : List (OpId P × maxRegObj.Op)}
    (hL : IsLinearization γ L) {r : P} {v c : ℕ} (hv : respOf γ (r, 0) = some v)
    (hr : opOf γ (r, 0) = some .readMax) (hc : 0 < c)
    (hops : ∀ x o, x ≠ (r, 0) → opOf γ x = some o → ∃ y < c, o = .writeMax y) : v < c := by
  obtain ⟨L₁, L₂, o, rfl, hop, hres⟩ := lin_split hL hv
  rw [hr] at hop; cases hop
  have hnd := hL.nodup
  simp only [maxRegObj_readMax] at hres
  rw [← hres]
  apply maxReg_runOps_lt _ _ hc
  intro o' ho' y hy
  obtain ⟨⟨x', o''⟩, hmem, rfl⟩ := List.mem_map.1 ho'
  have hx' : x' ≠ (r, 0) := by
    intro h; subst h
    simp only [List.map_append, List.map_cons] at hnd
    exact List.disjoint_of_nodup_append hnd (List.mem_map_of_mem (f := Prod.fst) hmem)
      List.mem_cons_self
  obtain ⟨z, hz, hz'⟩ := hops x' _ hx' (hL.op_eq _ (List.mem_append_left _ hmem))
  simp only at hy; rw [hy] at hz'; cases hz'; exact hz

/-- A read that starts after a `writeMax c` completed returns at least `c`. -/
lemma read_ge {γ : List (Label P maxRegObj)} {L : List (OpId P × maxRegObj.Op)}
    (hL : IsLinearization γ L) {r z : P} {v c : ℕ} (hv : respOf γ (r, 0) = some v)
    (hr : opOf γ (r, 0) = some .readMax) (hz : opOf γ (z, 0) = some (.writeMax c))
    (hprec : Precedes γ (z, 0) (r, 0)) : c ≤ v := by
  obtain ⟨L₁, L₂, o, hLeq, hop, hres⟩ := lin_split hL hv
  rw [hr] at hop; cases hop
  have hL' := hL
  rw [hLeq] at hL'
  simp only [maxRegObj_readMax] at hres
  rw [← hres]
  have hrt := hL'.realtime (z, 0) (r, 0) hprec (by simp)
  simp only [List.map_append, List.map_cons] at hrt
  have hmem := mem_prefix_of_sublist (by simpa using hL'.nodup) hrt
  obtain ⟨⟨x', o'⟩, hmem', hx'⟩ := List.mem_map.1 hmem
  simp only at hx'; subst hx'
  have := hL'.op_eq _ (List.mem_append_left _ hmem')
  rw [hz] at this; cases this
  exact maxReg_runOps_ge _ _ _ (List.mem_map_of_mem (f := Prod.snd) hmem')

/-! ### Filtering executions by process -/

lemma opsOf_filter_of {A : ObjSpec} (α : List (Label P A)) (f : Label P A → Bool) (p : P)
    (hf : ∀ ℓ ∈ α, ℓ.proc = p → f ℓ = true) : opsOf (α.filter f) p = opsOf α p := by
  induction α with
  | nil => rfl
  | cons ℓ α ih =>
    have ih' := ih (fun ℓ' h' => hf ℓ' (List.mem_cons_of_mem _ h'))
    by_cases hfl : f ℓ = true
    · simp [List.filter_cons, hfl, ih']
    · have : ℓ.proc ≠ p := fun h => hfl (hf ℓ List.mem_cons_self h)
      simp [List.filter_cons, hfl, ih', Label.invOf_eq_none_of_proc_ne this]

lemma respsOf_filter_sublist {A : ObjSpec} (α : List (Label P A)) (f : Label P A → Bool) (p : P) :
    (respsOf (α.filter f) p).Sublist (respsOf α p) :=
  (List.filter_sublist).filterMap _

omit [DecidableEq P] in
lemma tauCount_filter_of [DecidableEq P] {A : ObjSpec} (α : List (Label P A)) (f : Label P A → Bool)
    (p : P) (hf : ∀ ℓ ∈ α, ℓ.proc = p → f ℓ = true) : tauCount (α.filter f) p = tauCount α p := by
  unfold tauCount
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro ℓ hℓ
  cases ℓ with
  | tau q =>
    by_cases hq : q = p
    · subst hq; simp [hf _ hℓ rfl]
    · simp [hq]
  | inv q o => simp
  | ret q x => simp

/-! ### Essential sets -/

variable {ι L V : Type} [DecidableEq ι] [DecidableEq V] {v₀ : V}
variable (I : Impl maxRegObj (RWC ι V v₀) P L) (W : Finset P) (val : P → ℕ)

/-- The state of the construction of Section 4 after `i` iterations: execution `α` (final
configuration `C`, ghost `G`), essential set `E` and halted set `H`. Only processes of `E ∪ H`
take steps; each invoked a single `WriteMax(val p)` and none returned; every essential process
is pending and took exactly `i` steps; halted processes have smaller values than essential
ones (`E` is supreme); `E` is hidden; and every object's block is owned by one process. -/
structure Ess (i : ℕ) (α : List (Label P maxRegObj)) (C : Config maxRegObj (RWC ι V v₀) P L)
    (G : Ghost P ι V) (E H : Finset P) : Prop where
  run : arun I α = some (C, G)
  subW : E ∪ H ⊆ W
  disj : Disjoint E H
  labels : ∀ ℓ ∈ α, ℓ.proc ∈ E ∪ H
  ops : ∀ p ∈ E ∪ H, opsOf α p = [MaxOp.writeMax (val p)]
  resps : ∀ p, respsOf α p = []
  pend : ∀ p ∈ E, C.pend p ≠ none
  supreme : ∀ h ∈ H, ∀ e ∈ E, val h < val e
  hidden : Hidden G E
  steps : ∀ e ∈ E, tauCount α e = i
  blocks : ∀ o, BlockOK E (G.hist o)

variable {I W val}

/-- Base case of the construction: all writers invoke their `WriteMax`, nobody takes a step. -/
lemma ess_zero [Fintype P] (hall : ∀ p ∈ W, I.allowed p (.writeMax (val p))) :
    ∃ α C G, Ess I W val 0 α C G W ∅ := by
  set ps := W.toList with hps
  have hnd : ps.Nodup := Finset.nodup_toList _
  obtain ⟨C, h1, h2, h3⟩ := arunFrom_invs (I := I) (fun p => MaxOp.writeMax (val p)) ps
    I.initCfg Ghost.init hnd (fun p hp => ⟨rfl, hall p (Finset.mem_toList.1 hp)⟩)
  refine ⟨ps.map (fun p => (.inv p (.writeMax (val p)) : Label P maxRegObj)), C, Ghost.init,
    ⟨h1, by simp, by simp, ?_, ?_, ?_, ?_, by simp, ?_, ?_, ?_⟩⟩
  · intro ℓ hℓ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hℓ
    simp only [Label.proc, Finset.union_empty]
    simpa [hps] using hp
  · intro p hp
    rw [opsOf_map_inv _ ps hnd, if_pos (by simpa [hps] using hp)]
  · intro p; exact respsOf_map_inv _ ps p
  · intro p hp; exact h2 p (by simpa [hps] using hp)
  · intro x _ q hq; simp [Ghost.init] at hq; exact hq.symm
  · intro e _; exact tauCount_map_inv _ ps e
  · intro o; simp [Ghost.init, blockOK_nil]

/-- **Erasing essential processes** (sound version of Claim 1): erasing `K ⊆ E` from an
execution with essential set `E` gives an execution with essential set `E \ K`; the other
processes keep their local states, pending operations and awareness sets, and histories are
filtered. -/
lemma ess_erase {i : ℕ} {α : List (Label P maxRegObj)} {C : Config maxRegObj (RWC ι V v₀) P L}
    {G : Ghost P ι V} {E H K : Finset P} (hE : Ess I W val i α C G E H) (hK : K ⊆ E) :
    ∃ C' G', Ess I W val i (α.filter (fun ℓ => decide (ℓ.proc ∉ K))) C' G' (E \ K) H ∧
      (∀ q, q ∉ K → C'.loc q = C.loc q ∧ C'.pend q = C.pend q ∧ G'.aw q = G.aw q) ∧
      (∀ q, G'.aw q ⊆ G.aw q) ∧
      (∀ o, G'.hist o = (G.hist o).filter (fun e => decide (e.proc ∉ K))) := by
  obtain ⟨C', G', h1, h2, h3, h4⟩ := arun_filter_hidden (I := I) hE.run (hE.hidden.mono hK)
  have hHK : ∀ p ∈ H, p ∉ K := fun p hp hpK =>
    Finset.disjoint_left.1 hE.disj (hK hpK) hp
  refine ⟨C', G', ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h2, h3, ?_⟩
  · exact (Finset.union_subset_union (Finset.sdiff_subset) le_rfl).trans hE.subW
  · exact Finset.disjoint_of_subset_left Finset.sdiff_subset hE.disj
  · intro ℓ hℓ
    obtain ⟨hℓ, hℓK⟩ := List.mem_filter.1 hℓ
    simp only [decide_eq_true_eq] at hℓK
    rcases Finset.mem_union.1 (hE.labels ℓ hℓ) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨h, hℓK⟩)
    · exact Finset.mem_union_right _ h
  · intro p hp
    have hpK : p ∉ K := by
      rcases Finset.mem_union.1 hp with h | h
      · exact (Finset.mem_sdiff.1 h).2
      · exact hHK p h
    rw [opsOf_filter_of α _ p (fun ℓ _ hℓ => by simp [hℓ, hpK])]
    exact hE.ops p (by
      rcases Finset.mem_union.1 hp with h | h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.1 h).1
      · exact Finset.mem_union_right _ h)
  · intro p
    have := respsOf_filter_sublist α (fun ℓ => decide (ℓ.proc ∉ K)) p
    rw [hE.resps p] at this
    exact List.eq_nil_of_sublist_nil this
  · intro p hp
    rw [(h2 p (Finset.mem_sdiff.1 hp).2).2.1]; exact hE.pend p (Finset.mem_sdiff.1 hp).1
  · intro h hh e he; exact hE.supreme h hh e (Finset.mem_sdiff.1 he).1
  · intro x hx q hq
    exact hE.hidden x (Finset.mem_sdiff.1 hx).1 q (h3 q hq)
  · intro e he
    rw [tauCount_filter_of α _ e (fun ℓ _ hℓ => by simp [hℓ, (Finset.mem_sdiff.1 he).2])]
    exact hE.steps e (Finset.mem_sdiff.1 he).1
  · intro o; rw [h4 o]; exact (hE.blocks o).filter hK
  · exact h4

end Podc.ReadUpdateTradeoffs
