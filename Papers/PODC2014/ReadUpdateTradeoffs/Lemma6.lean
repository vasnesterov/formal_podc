import Papers.PODC2014.ReadUpdateTradeoffs.MaxRegSetup

/-!
# Lemma 6 of Hendler–Khait (PODC'14): few essential processes can complete

If `ReadMax` completes within `m` solo steps, then at most `m` processes of an essential set
have finished their `WriteMax`.

The paper's proof erases, before each step of the reader, the (unique) completed hidden process
the accessed object is familiar with. Erasing the last writer of an object can however
*resurrect* an older write by another completed hidden process, which the reader then sees; the
paper does not account for this. We prove the lemma for executions satisfying the block invariant
(`Ess`, field `blocks`), by a single comparison: run the reader in the execution with *all*
essential processes erased, and keep exactly the completed processes owning none of the (at most
`m`) objects that the reader accesses there.
-/

namespace Podc.ReadUpdateTradeoffs

open Cslib.SharedMemory Cslib.SharedMemory.Awareness

section Transfer

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
variable (I : Impl A B P L)

/-- The base objects accessed by the internal steps of `σ` executed from `C`. -/
noncomputable def accFrom : Config A B P L → List (Label P A) → Finset ι
  | _, [] => ∅
  | C, ℓ :: σ =>
    match I.step C ℓ with
    | none => ∅
    | some C' =>
      (match ℓ with
        | .tau p => match I.act p (C.loc p) with
          | .access i _ _ => {i}
          | .ret _ _ => ∅
        | _ => ∅) ∪ accFrom C' σ

variable {I}

/-- At most one object per internal step. -/
lemma card_accFrom_le (C : Config A B P L) (σ : List (Label P A)) (r : P)
    (hσ : ∀ ℓ ∈ σ, ℓ.proc = r) : (accFrom I C σ).card ≤ tauCount σ r := by
  induction σ generalizing C with
  | nil => simp [accFrom]
  | cons ℓ σ ih =>
    simp only [accFrom]
    have htc : tauCount (ℓ :: σ) r = (if ℓ.isTauOf r then 1 else 0) + tauCount σ r := by
      simp only [tauCount, List.filter_cons]; split_ifs <;> simp [add_comm]
    rw [htc]
    split
    · simp
    · rename_i C' _
      have ih' := ih C' (fun ℓ' h' => hσ ℓ' (List.mem_cons_of_mem _ h'))
      refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ih')
      cases ℓ with
      | tau p =>
        have : p = r := hσ _ List.mem_cons_self
        subst this
        simp only [Label.isTauOf_tau, decide_true, if_true]
        split <;> simp
      | inv p o => simp
      | ret p x => simp

/-- **Solo runs depend only on the accessed objects.** If `D` agrees with `C` on the local
state and pending operation of `r` and on every base object that a solo run `σ` of `r` from `C`
accesses, then `σ` is also an execution from `D`. -/
lemma solo_transfer {r : P} {C C' D : Config A B P L} {σ : List (Label P A)}
    (h : I.runFrom C σ = some C') (hσ : ∀ ℓ ∈ σ, ℓ.proc = r) (hloc : D.loc r = C.loc r)
    (hpend : D.pend r = C.pend r) (hmem : ∀ i ∈ accFrom I C σ, D.mem i = C.mem i) :
    ∃ D', I.runFrom D σ = some D' := by
  induction σ generalizing C D with
  | nil => exact ⟨D, rfl⟩
  | cons ℓ σ ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      have hacc : ∀ i ∈ accFrom I C₁ σ, i ∈ accFrom I C (ℓ :: σ) := by
        intro i hi; simp only [accFrom, hs]; exact Finset.mem_union_right _ hi
      have hσ' : ∀ ℓ' ∈ σ, ℓ'.proc = r := fun ℓ' h' => hσ ℓ' (List.mem_cons_of_mem _ h')
      have hr : ℓ.proc = r := hσ ℓ List.mem_cons_self
      cases ℓ with
      | inv p o =>
        simp only [Label.proc] at hr; subst hr
        obtain ⟨h0, hal, hp, hl, hm⟩ := Impl.step_inv hs
        obtain ⟨D₁, hs'⟩ : ∃ D₁, I.step D (.inv p o) = some D₁ :=
          ⟨_, Impl.step_inv_eq_some (I := I) (C := D) (hpend.trans h0) hal⟩
        obtain ⟨-, -, hp', hl', hm'⟩ := Impl.step_inv hs'
        obtain ⟨D', hD'⟩ := ih h hσ' (D := D₁)
          (by rw [hl', hl]; simp [hloc]) (by rw [hp', hp]; simp [hpend]) (fun i hi => by
            rw [hm', hm]; exact hmem i (hacc i hi))
        exact ⟨D', by simp [hs', hD']⟩
      | ret p x =>
        simp only [Label.proc] at hr; subst hr
        obtain ⟨h0, hp, hm, l, hact, hl⟩ := Impl.step_ret hs
        obtain ⟨D₁, hs'⟩ : ∃ D₁, I.step D (.ret p x) = some D₁ :=
          ⟨_, Impl.step_ret_eq_some (I := I) (C := D) (by rw [hpend]; exact h0)
            (by rw [hloc]; exact hact)⟩
        obtain ⟨-, hp', hm', l', hact', hl'⟩ := Impl.step_ret hs'
        rw [hloc, hact] at hact'
        cases hact'
        obtain ⟨D', hD'⟩ := ih h hσ' (D := D₁)
          (by rw [hl', hl]; simp) (by rw [hp', hp]; simp [hpend]) (fun i hi => by
            rw [hm', hm]; exact hmem i (hacc i hi))
        exact ⟨D', by simp [hs', hD']⟩
      | tau p =>
        simp only [Label.proc] at hr; subst hr
        obtain ⟨h0, hp, i, o, k, hact, hm, hl⟩ := Impl.step_tau hs
        have hi : D.mem i = C.mem i := hmem i (by simp [accFrom, hs, hact])
        obtain ⟨D₁, hs'⟩ : ∃ D₁, I.step D (.tau p) = some D₁ :=
          ⟨_, Impl.step_tau_eq_some (I := I) (C := D) (by rw [hpend]; exact h0)
            (by rw [hloc]; exact hact)⟩
        obtain ⟨-, hp', i', o', k', hact', hm', hl'⟩ := Impl.step_tau hs'
        rw [hloc, hact] at hact'
        cases hact'
        obtain ⟨D', hD'⟩ := ih h hσ' (D := D₁)
          (by rw [hl', hl]; simp [hloc, hi]) (by rw [hp', hp, hpend]) (fun j hj => by
            rw [hm', hm]
            by_cases hji : j = i
            · subst hji; simp [hi]
            · simp only [Function.update_of_ne hji]
              exact hmem j (hacc j hj))
        exact ⟨D', by simp [hs', hD']⟩

end Transfer

variable {P : Type} [Fintype P] [DecidableEq P]
variable {ι L V : Type} [DecidableEq ι] [DecidableEq V] {v₀ : V}
variable {I : Impl maxRegObj (RWC ι V v₀) P L} {W : Finset P} {val : P → ℕ}

/-- The owner of the block of a history (if the block is nonempty). -/
def owner (E : Finset P) (h : List (Entry P V)) : Option P := (block E h).head?.map Entry.proc

lemma owner_eq_of_mem_block {E : Finset P} {h : List (Entry P V)} (hb : BlockOK E h)
    {y : Entry P V} (hy : y ∈ block E h) : owner E h = some y.proc := by
  unfold owner
  cases hbl : block E h with
  | nil => rw [hbl] at hy; simp at hy
  | cons z t =>
    simp only [List.head?_cons, Option.map_some, Option.some.injEq]
    exact hb z (by rw [hbl]; exact List.mem_cons_self) y hy

open Classical in
/-- **Lemma 6 of Hendler–Khait, PODC'14 (for executions with the block invariant).** If every
`ReadMax` of the reader `r` completes within `m` solo steps, then at most `m` essential
processes have finished their `WriteMax` (their next action is to return). -/
theorem lemma6 (hlin : I.Linearizable) {r : P} (hr : r ∉ W) (hval : ∀ p ∈ W, 1 ≤ val p)
    {m : ℕ} (hm : SoloBound I r MaxOp.readMax m) {i : ℕ} {α : List (Label P maxRegObj)}
    {C : Config maxRegObj (RWC ι V v₀) P L} {G : Ghost P ι V} {E H : Finset P}
    (hE : Ess I W val i α C G E H) :
    (E.filter (fun e => ∃ x l, I.act e (C.loc e) = Action.ret x l)).card ≤ m := by
  classical
  set Ec := E.filter (fun e => ∃ x l, I.act e (C.loc e) = Action.ret x l) with hEc
  by_contra hcon
  push_neg at hcon
  have hrEH : r ∉ E ∪ H := fun h => hr (hE.subW h)
  have hrE : r ∉ E := fun h => hrEH (Finset.mem_union_left _ h)
  have hrH : r ∉ H := fun h => hrEH (Finset.mem_union_right _ h)
  have hI := arun_inv hE.run
  -- world 0: all essential processes erased
  obtain ⟨C₀, G₀, hE₀, h0loc, -, h0hist⟩ := ess_erase hE (subset_refl E)
  set α₀ := α.filter (fun ℓ => decide (ℓ.proc ∉ E)) with hα₀
  have hrun₀ := arun_fst I hE₀.run
  have hα₀r : ∀ ℓ ∈ α₀, ℓ.proc ≠ r := fun ℓ hℓ h => hrEH (by
    have := hE₀.labels ℓ hℓ; rw [h] at this
    rcases Finset.mem_union.1 this with h' | h'
    · exact absurd (Finset.mem_sdiff.1 h').1 (by rw [h] at *; exact fun h'' => (Finset.mem_sdiff.1 h').2 h'')
    · exact Finset.mem_union_right _ h')
  have hpend₀ : C₀.pend r = none := (Impl.runFrom_other I hrun₀ (q := r) hα₀r).2
  obtain ⟨t, ht, v₀', γC, hγC⟩ := hm α₀ C₀ hrun₀ hpend₀
  set σ : List (Label P maxRegObj) :=
    .inv r .readMax :: (List.replicate t (.tau r) ++ [.ret r v₀']) with hσ
  have hσr : ∀ ℓ ∈ σ, ℓ.proc = r := by
    intro ℓ hℓ
    simp only [hσ, List.mem_cons, List.mem_append, List.mem_replicate, List.mem_singleton] at hℓ
    rcases hℓ with rfl | ⟨-, rfl⟩ | rfl | h <;> simp_all [Label.proc]
  obtain ⟨C₀', hC₀'⟩ : ∃ C₀', I.runFrom C₀ σ = some C₀' := by
    rw [I.run_append_of_eq hrun₀] at hγC; exact ⟨γC, hγC⟩
  set Acc := accFrom I C₀ σ with hAcc
  have hAcc_card : Acc.card ≤ m := by
    refine (card_accFrom_le C₀ σ r hσr).trans ?_
    have : tauCount σ r = t := by simp [hσ, tauCount, List.filter_append, List.filter_cons]
    omega
  -- the completed processes owning an accessed object
  set Y := Ec.filter (fun e => ∃ o ∈ Acc, owner E (G.hist o) = some e) with hY
  have hY_card : Y.card ≤ m := by
    refine le_trans ?_ hAcc_card
    refine le_trans ?_ (Finset.card_image_le (s := Acc) (f := fun o => owner E (G.hist o)))
    refine Finset.card_le_card_of_injOn (fun e => some e) (fun e he => ?_) (fun a _ b _ h => ?_)
    · obtain ⟨-, o, ho, hoe⟩ := Finset.mem_filter.1 he
      exact Finset.mem_image.2 ⟨o, ho, hoe⟩
    · exact Option.some.inj h
  set Z := Ec \ Y with hZ
  obtain ⟨z, hz⟩ : Z.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    have : Ec ⊆ Y := Finset.sdiff_eq_empty_iff_subset.1 h0
    have := Finset.card_le_card this
    omega
  have hZE : Z ⊆ E := fun e he => (Finset.mem_filter.1 (Finset.mem_sdiff.1 he).1).1
  have hzE : z ∈ E := hZE hz
  -- world Z: keep exactly the processes of `Z` among the essential ones
  set X := E \ Z with hX
  have hXE : X ⊆ E := Finset.sdiff_subset
  have hEX : E \ X = Z := Finset.sdiff_sdiff_eq_self hZE
  obtain ⟨C₁, G₁, hE₁, h1loc, -, h1hist⟩ := ess_erase hE hXE
  rw [hEX] at hE₁
  let f : P → ℕ := fun p => if h : ∃ x l, I.act p (C.loc p) = .ret x l then h.choose else 0
  have hf : ∀ p ∈ Z, C₁.pend p ≠ none ∧ ∃ l, I.act p (C₁.loc p) = .ret (f p) l := by
    intro p hp
    have hpX : p ∉ X := fun h => (Finset.mem_sdiff.1 h).2 hp
    have hex : ∃ x l, I.act p (C.loc p) = .ret x l := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hp).1).2
    refine ⟨hE₁.pend p hp, ?_⟩
    rw [(h1loc p hpX).1]
    simp only [f, dif_pos hex]
    exact hex.choose_spec
  obtain ⟨C₂, h2run, -, h2oth⟩ := arunFrom_rets (I := I) f Z.toList C₁ G₁ (Finset.nodup_toList _)
    (fun p hp => hf p (Finset.mem_toList.1 hp))
  set αZ := α.filter (fun ℓ => decide (ℓ.proc ∉ X)) ++ Z.toList.map (fun p => .ret p (f p))
    with hαZ
  have hrunZ : arun I αZ = some (C₂, G₁) := by rw [hαZ, arun_append_of_eq I hE₁.run]; exact h2run
  have hI₁ := arun_inv hE₁.run
  have hI₂ := arun_inv hrunZ
  have hI₀ := arun_inv hE₀.run
  -- the reader cannot tell the two worlds apart
  have hmemAcc : ∀ o ∈ Acc, C₂.mem o = C₀.mem o := by
    intro o ho
    rw [hI₂.mem_eq, hI₀.mem_eq, h1hist, h0hist]
    apply topVal_eq_of_head?
    apply head_filter_eq hXE
    intro y hy hyE
    have hyb := head_filter_mem_block hXE (Option.mem_def.1 hy) hyE
    have hown := owner_eq_of_mem_block (hE.blocks o) hyb
    have hyX : y.proc ∉ X := by
      have hmem : y ∈ (G.hist o).filter (fun e => decide (e.proc ∉ X)) := by
        cases hfl : (G.hist o).filter (fun e => decide (e.proc ∉ X)) with
        | nil => rw [hfl] at hy; simp at hy
        | cons a t => rw [hfl] at hy; simp only [List.head?_cons, Option.mem_def,
            Option.some.injEq] at hy; subst hy; exact List.mem_cons_self
      simpa using (List.mem_filter.1 hmem).2
    have hyZ : y.proc ∈ Z := by
      by_contra hyZ; exact hyX (Finset.mem_sdiff.2 ⟨hyE, hyZ⟩)
    have hyY : y.proc ∈ Y := Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hyZ).1, o, ho, hown⟩
    exact (Finset.mem_sdiff.1 hyZ).2 hyY
  have hrZ : r ∉ Z.toList := fun h => hrE (hZE (Finset.mem_toList.1 h))
  have hrX : r ∉ X := fun h => hrE (hXE h)
  obtain ⟨C₂', hC₂'⟩ := solo_transfer hC₀' hσr
    (by rw [(h2oth r hrZ).2, (h1loc r hrX).1, (h0loc r hrE).1])
    (by rw [(h2oth r hrZ).1, (h1loc r hrX).2.1, (h0loc r hrE).2.1]) hmemAcc
  -- the two executions
  have hval0 : I.Valid (α₀ ++ σ) := ⟨γC, hγC⟩
  have hvalZ : I.Valid (αZ ++ σ) :=
    ⟨C₂', by rw [I.run_append_of_eq (arun_fst I hrunZ)]; exact hC₂'⟩
  obtain ⟨hfun, hlinf⟩ := hlin
  have hopsσ : ∀ p, opsOf σ p = if p = r then [MaxOp.readMax] else [] := by
    intro p
    by_cases hp : p = r
    · subst hp; simp [hσ, opsOf_replicate]
    · simp [hσ, opsOf_replicate, Ne.symm hp, hp]
  have hrespsσ : respsOf σ r = [v₀'] := by simp [hσ, respsOf_replicate]
  have hα₀ops : opsOf α₀ r = [] := opsOf_eq_nil_of_proc_ne hα₀r
  have hα₀resps : respsOf α₀ r = [] := respsOf_eq_nil_of_proc_ne hα₀r
  -- (a) in world 0 the read returns less than `val z`
  have ha : v₀' < val z := by
    refine read_lt (hlinf _ hval0) (r := r) ?_ ?_ (hval z (hE.subW (Finset.mem_union_left _ hzE)))
      ?_
    · simp [respOf, hα₀resps, hrespsσ]
    · simp [opOf, hα₀ops, hopsσ]
    · rintro ⟨p, n⟩ o hx hop
      unfold opOf at hop
      simp only [opsOf_append, hopsσ] at hop
      by_cases hpr : p = r
      · subst hpr
        simp only [hα₀ops, if_true, List.nil_append] at hop
        have : n = 0 := by
          rcases n with _ | n
          · rfl
          · simp at hop
        exact absurd (by rw [this]) hx
      · simp only [hpr, if_false, List.append_nil] at hop
        by_cases hpH : p ∈ H
        · rw [hE₀.ops p (Finset.mem_union_right _ hpH)] at hop
          have : o = .writeMax (val p) := by
            rcases n with _ | n
            · simpa using hop.symm
            · simp at hop
          exact ⟨val p, hE.supreme p hpH z hzE, this⟩
        · have : opsOf α₀ p = [] := opsOf_eq_nil_of_proc_ne (fun ℓ hℓ h => by
            have := hE₀.labels ℓ hℓ; rw [h] at this
            rcases Finset.mem_union.1 this with h' | h'
            · exact (Finset.mem_sdiff.1 h').2 (Finset.mem_sdiff.1 h').1
            · exact hpH h')
          rw [this] at hop; simp at hop
  -- (b) in world `Z` it returns at least `val z`
  have hb : val z ≤ v₀' := by
    have hαZr : ∀ ℓ ∈ αZ, ℓ.proc ≠ r := by
      intro ℓ hℓ h
      rcases List.mem_append.1 hℓ with hℓ | hℓ
      · have := hE₁.labels ℓ hℓ; rw [h] at this
        rcases Finset.mem_union.1 this with h' | h'
        · exact hrE (hZE h')
        · exact hrH h'
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hℓ
        exact hrZ (by simp only [Label.proc] at h; rw [← h]; exact hp)
    have hαZops : opsOf αZ r = [] := opsOf_eq_nil_of_proc_ne hαZr
    have hαZresps : respsOf αZ r = [] := respsOf_eq_nil_of_proc_ne hαZr
    have hzr : z ≠ r := fun h => hrE (h ▸ hzE)
    refine read_ge (hlinf _ hvalZ) (r := r) (z := z) ?_ ?_ ?_ ?_
    · simp [respOf, hαZresps, hrespsσ]
    · simp [opOf, hαZops, hopsσ]
    · have := hE₁.ops z (Finset.mem_union_left _ hz)
      unfold opOf
      rw [opsOf_append, hαZ, opsOf_append, this, opsOf_map_ret, hopsσ, if_neg hzr]
      rfl
    · refine ⟨αZ, σ, rfl, ?_, ?_⟩
      · unfold Completed
        rw [hαZ, respsOf_append, hE₁.resps z,
          respsOf_map_ret (A := maxRegObj) f Z.toList (Finset.nodup_toList _) z,
          if_pos (Finset.mem_toList.2 hz)]
        simp
      · unfold Invoked; simp [hαZops]
  exact absurd hb (not_le.2 ha)

end Podc.ReadUpdateTradeoffs
