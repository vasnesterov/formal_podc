import Papers.PODC2016.ComplexityHierarchy.Buffer

/-!
# The key lemma for block (multi-)writes: Lemmas 6.5 and 7.3 of EGSZ'16

Setting: binary consensus algorithms over the memory `MB R ℓ V` (`ℓ`-buffers, possibly with
multiple assignment), see `Buffer.lean`.

A *block* `(T1, T2)` for a set of locations `Lset` in a configuration `C` (`IsBlock`) consists of
two lists of distinct processes, all poised in `C` to perform (multiple) assignments that only
write locations of `Lset`, such that

* `T1` writes every location of `Lset` at least `max ℓ 1` times (so it obliterates `Lset`), and
* either the algorithm only uses single-location writes, or `T2` also writes every location of
  `Lset` at least `max ℓ 1` times.

In Section 6 (single-location writes), `T1` = the processes `ℓ`-covering the locations of `Lset`
and `T2 = []`; in Section 7 (multiple assignment), `T1`/`T2` are the two halves `R1`/`R2` of a
`2ℓ`-packing of the fully packed locations (Lemma 7.2 guarantees that they only write `Lset`).

`key_lemma` is the common core of Lemma 6.5 and Lemma 7.3: if `Q` is bivalent from `C` and the
block processes and a process `p` belong to a set `Rs` disjoint from `Q`, then some `Q`-only
execution `ξ` leads to a configuration `Cξ` such that `Q ∪ Rs` is bivalent after the block write
`T1` from `Cξ`, and in `Cξ` some process of `Q` covers a location outside `Lset`.

Unlike the paper (which picks `p ∈ R`), we need `Rs` to contain *some* process `p`; the case
`R = ∅` (only possible for `n = 2`) is treated separately by the callers.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory Impl

variable {R V P L : Type} [DecidableEq P] {ℓ : ℕ} {I : Impl BinCons (MB R ℓ V) P L}

lemma steps_blockWrite {S : Set P} {ps : List P} (h : ∀ p ∈ ps, p ∈ S) :
    Steps S (blockWrite ps : List (Label P BinCons)) := by
  intro ℓ' hℓ
  simp only [blockWrite, List.mem_map] at hℓ
  obtain ⟨p, hp, rfl⟩ := hℓ
  exact ⟨h p hp, trivial⟩

lemma blockWrite_append (ps qs : List P) :
    (blockWrite (ps ++ qs) : List (Label P BinCons)) = blockWrite ps ++ blockWrite qs := by
  simp [blockWrite]

/-- A block `(T1, T2)` for the locations `Lset` in `C` (see the module docstring). -/
structure IsBlock (I : Impl BinCons (MB R ℓ V) P L) (C : Config BinCons (MB R ℓ V) P L)
    (Lset : Set R) (T1 T2 : List P) : Prop where
  nodup : (T1 ++ T2).Nodup
  poised : ∀ p ∈ T1 ++ T2, ∃ w, I.Poised C p w
  inside : ∀ p ∈ T1 ++ T2, I.WritesIn C p Lset
  cnt1 : ∀ r ∈ Lset, wvals (T1.map (I.wOf C)) r ≠ [] ∧ ℓ ≤ (wvals (T1.map (I.wOf C)) r).length
  cnt2 : I.SingleWrites ∨
    ∀ r ∈ Lset, wvals (T2.map (I.wOf C)) r ≠ [] ∧ ℓ ≤ (wvals (T2.map (I.wOf C)) r).length

lemma IsBlock.congr {C D : Config BinCons (MB R ℓ V) P L} {Lset : Set R} {T1 T2 : List P}
    (h : IsBlock I C Lset T1 T2) (hl : ∀ x ∈ T1 ++ T2, C.loc x = D.loc x)
    (hp : ∀ x ∈ T1 ++ T2, C.pend x = D.pend x) : IsBlock I D Lset T1 T2 := by
  have hm1 : T1.map (I.wOf D) = T1.map (I.wOf C) :=
    List.map_congr_left (fun x hx => (wOf_congr (hl x (by simp [hx]))).symm)
  have hm2 : T2.map (I.wOf D) = T2.map (I.wOf C) :=
    List.map_congr_left (fun x hx => (wOf_congr (hl x (by simp [hx]))).symm)
  refine ⟨h.nodup, fun x hx => ?_, fun x hx => ?_, by rw [hm1]; exact h.cnt1, by
    rw [hm2]; exact h.cnt2⟩
  · obtain ⟨w, hw⟩ := h.poised x hx; exact ⟨w, hw.congr (hl x hx) (hp x hx)⟩
  · intro w k hk; rw [← hl x hx] at hk; exact h.inside x hx w k hk

lemma IsBlock.wvals_nil_of_notMem {C : Config BinCons (MB R ℓ V) P L} {Lset : Set R} {T1 T2 : List P}
    (h : IsBlock I C Lset T1 T2) {T : List P} (hT : ∀ x ∈ T, x ∈ T1 ++ T2) {r : R} (hr : r ∉ Lset) :
    wvals (T.map (I.wOf C)) r = [] := by
  apply wvals_eq_nil
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨x, hx, rfl⟩ := hw
  obtain ⟨w', hw'⟩ := h.poised x (hT x hx)
  rw [hw'.wOf_eq]
  by_contra hne
  obtain ⟨-, k, hk⟩ := hw'
  exact hr (h.inside x (hT x hx) w' k hk r hne)

/-- **Key lemma (common core of Lemmas 6.5 and 7.3).** -/
theorem key_lemma (hS : I.Solves (weakConsensus P Bool)) (hof : I.OneShotOF)
    {C : Config BinCons (MB R ℓ V) P L} (hC : I.Reach C) {Q Rs : Finset P} (hQR : Disjoint Q Rs)
    (hQ : I.Bivalent Q C) {Lset : Set R} {T1 T2 : List P} (hB : IsBlock I C Lset T1 T2)
    (hT : ∀ x ∈ T1 ++ T2, x ∈ Rs) {p : P} (hp : p ∈ Rs) :
    ∃ ξ Cξ C₁, Steps Q ξ ∧ I.runFrom C ξ = some Cξ ∧ I.runFrom Cξ (blockWrite T1) = some C₁ ∧
      I.Bivalent (↑Q ∪ ↑Rs) C₁ ∧ ∃ q ∈ Q, ∃ r ∉ Lset, I.MCovers Cξ q r := by
  classical
  have hpend := hC.pend_of_bivalent hS hQ
  have hTQ : ∀ x ∈ T1 ++ T2, x ∉ Q := fun x hx hxQ =>
    Finset.disjoint_left.1 hQR hxQ (hT x hx)
  have hpQ : p ∉ Q := fun h => Finset.disjoint_left.1 hQR h hp
  have hsubR : (Rs : Set P) ⊆ ↑Q ∪ ↑Rs := Set.subset_union_right
  have hsubQ : (Q : Set P) ⊆ ↑Q ∪ ↑Rs := Set.subset_union_left
  -- blocks can be performed from every configuration reached by a `Q`-only execution
  have hblock : ∀ {Z : Config BinCons (MB R ℓ V) P L}, I.ReachBy Q C Z →
      IsBlock I Z Lset T1 T2 ∧ ∃ Z₁ Z₂, I.runFrom Z (blockWrite T1) = some Z₁ ∧
        I.runFrom Z₁ (blockWrite T2) = some Z₂ := by
    intro Z hZ
    have hB' : IsBlock I Z Lset T1 T2 := hB.congr
      (fun x hx => ((hZ.other (by simpa using hTQ x hx)).1).symm)
      (fun x hx => ((hZ.other (by simpa using hTQ x hx)).2).symm)
    refine ⟨hB', ?_⟩
    obtain ⟨Z₂, h₂, -⟩ := I.runFrom_block (T1 ++ T2) Z hB'.nodup hB'.poised
    rw [blockWrite, List.map_append] at h₂
    obtain ⟨Z₁, h1, h2⟩ := I.runFrom_eq_some_of_append h₂
    exact ⟨Z₁, Z₂, h1, h2⟩
  obtain ⟨-, D₁, D₂, hD₁, hD₂⟩ := hblock (ReachBy.refl _ C)
  have hT1R : ∀ x ∈ T1, x ∈ (Rs : Set P) := fun x hx => hT x (by simp [hx])
  have hT2R : ∀ x ∈ T2, x ∈ (Rs : Set P) := fun x hx => hT x (by simp [hx])
  have hstepsT : Steps (Rs : Set P) (blockWrite T1 ++ blockWrite T2 : List (Label P BinCons)) :=
    (steps_blockWrite hT1R).append (steps_blockWrite hT2R)
  have hreachB : ∀ {Z Z₁ Z₂ : Config BinCons (MB R ℓ V) P L}, I.ReachBy Q C Z →
      I.runFrom Z (blockWrite T1) = some Z₁ → I.runFrom Z₁ (blockWrite T2) = some Z₂ →
      I.Reach Z₂ ∧ Z₂.pend p ≠ none := by
    intro Z Z₁ Z₂ hZ h1 h2
    have hr : I.runFrom Z (blockWrite T1 ++ blockWrite T2) = some Z₂ := by
      rw [I.runFrom_append_of_eq h1, h2]
    refine ⟨(hC.reachBy hZ).extend hstepsT hr, ?_⟩
    rw [I.runFrom_pend_of_tau hr (fun ℓ' hℓ' => ?_), (hZ.other (by simpa using hpQ)).2]
    · exact hpend p
    · rcases List.mem_append.1 hℓ' with h | h <;>
      · simp only [blockWrite, List.mem_map] at h; obtain ⟨x, -, rfl⟩ := h; exact ⟨x, rfl⟩
  obtain ⟨hRD, hpD⟩ := hreachB (ReachBy.refl _ _) hD₁ hD₂
  obtain ⟨v, hv⟩ := hRD.exists_canDecide_self hof hpD
  have hQnv : I.CanDecide Q C (!v) := by cases v; exacts [hQ.2, hQ.1]
  obtain ⟨ζ, Y, hζ, hY, hdec⟩ := hQnv
  -- the configurations along `ζ`, and after the block
  have hZ : ∀ m ≤ ζ.length, ∃ Z, I.runFrom C (ζ.take m) = some Z := by
    intro m _
    obtain ⟨Z, hZ, -⟩ := I.runFrom_eq_some_of_append (α := ζ.take m) (β := ζ.drop m)
      (by rw [List.take_append_drop]; exact hY)
    exact ⟨Z, hZ⟩
  haveI : Nonempty (Config BinCons (MB R ℓ V) P L) := ⟨C⟩
  choose! Zf hZf using hZ
  have hZrb : ∀ m ≤ ζ.length, I.ReachBy Q C (Zf m) := fun m hm =>
    ⟨_, hζ.of_prefix (List.take_prefix _ _), hZf m hm⟩
  have hBl : ∀ m ≤ ζ.length, ∃ Z₁ Z₂, I.runFrom (Zf m) (blockWrite T1) = some Z₁ ∧
      I.runFrom Z₁ (blockWrite T2) = some Z₂ := fun m hm => (hblock (hZrb m hm)).2
  choose! B1 B2 hB1 hB2 using hBl
  have hZ0 : Zf 0 = C := by have := hZf 0 (Nat.zero_le _); simp at this; exact this.symm
  let f : ℕ → Prop := fun m => I.CanDecide {p} (B2 m) v
  have hf0 : f 0 := by
    have h1 := hB1 0 (Nat.zero_le _); rw [hZ0, hD₁] at h1; cases h1
    have h2 := hB2 0 (Nat.zero_le _); rw [hD₂] at h2; cases h2
    exact hv
  have hfend : ¬ f ζ.length := by
    intro h
    have hZY : Zf ζ.length = Y := by
      have := hZf _ le_rfl; rw [List.take_length, hY] at this; exact (Option.some.inj this).symm
    have := hC.decides_canDecide_eq hS (Q := ↑Q ∪ ↑Rs)
      (β := ζ ++ (blockWrite T1 ++ blockWrite T2))
      ((hζ.mono hsubQ).append (hstepsT.mono hsubR))
      (by rw [I.runFrom_append_of_eq hY, ← hZY, I.runFrom_append_of_eq (hB1 _ le_rfl),
            hB2 _ le_rfl])
      (hdec.mono (List.subset_append_left _ _)) h
    cases v <;> simp at this
  set m := Nat.findGreatest f ζ.length with hmdef
  have hfm : f m := Nat.findGreatest_spec (P := f) (m := 0) (Nat.zero_le _) hf0
  have hmlt : m < ζ.length :=
    lt_of_le_of_ne (Nat.findGreatest_le _) (fun e => hfend (e ▸ hfm))
  have hfm1 : ¬ f (m + 1) :=
    Nat.findGreatest_is_greatest (P := f) (n := ζ.length) (k := m + 1) (by omega) (by omega)
  have hstep : I.step (Zf m) ζ[m] = some (Zf (m + 1)) := by
    have e := hZf (m + 1) hmlt
    rw [List.take_succ_eq_append_getElem hmlt, I.runFrom_append_of_eq (hZf m hmlt.le),
      runFrom_singleton] at e
    exact e
  have hδQ : ζ[m].proc ∈ Q := hζ.proc (List.getElem_mem hmlt)
  have hδS : ζ[m].IsStep := (hζ _ (List.getElem_mem hmlt)).2
  obtain ⟨hR1, hp1⟩ := hreachB (hZrb (m + 1) hmlt) (hB1 _ hmlt) (hB2 _ hmlt)
  obtain ⟨hR0, hp0⟩ := hreachB (hZrb m hmlt.le) (hB1 _ hmlt.le) (hB2 _ hmlt.le)
  have hpnv : I.CanDecide {p} (B2 (m + 1)) (!v) :=
    hR1.canDecide_not_of_canDecide hof hp1 (Set.mem_singleton p) hfm1
  have hBm := (hblock (hZrb m hmlt.le)).1
  have hBm1 := (hblock (hZrb (m + 1) hmlt)).1
  have hrun2 : ∀ k ≤ ζ.length, I.runFrom (Zf k) (blockWrite (T1 ++ T2)) = some (B2 k) := by
    intro k hk; rw [blockWrite_append, I.runFrom_append_of_eq (hB1 k hk), hB2 k hk]
  have hothers : ∀ x ∈ Rs, (Zf (m + 1)).loc x = (Zf m).loc x ∧
      (Zf (m + 1)).pend x = (Zf m).pend x := fun x hx =>
    step_other hstep (fun e => Finset.disjoint_left.1 hQR (e ▸ hδQ) hx)
  -- steps of `Q` that only change `Lset` are invisible to `p` after the block
  have hinv : (∀ r, r ∉ Lset → (Zf (m + 1)).mem () r = (Zf m).mem () r) → False := by
    intro hmem
    obtain ⟨X', Y', h1, h2, hagr⟩ := I.block_agreeOn (S := ↑Rs) (X := Zf (m + 1)) (Y := Zf m)
      (T1 ++ T2) hBm1.nodup (fun x hx => hT x hx) hBm1.poised (fun x hx => (hothers x hx).1)
      (fun x hx => (hothers x hx).2) (fun r => by
        by_cases hr : r ∈ Lset
        · right
          obtain ⟨h1, h2⟩ := hBm1.cnt1 r hr
          rw [List.map_append, wvals_append]
          exact ⟨by simp [h1], by simp only [List.length_append]; omega⟩
        · left; exact hmem r hr)
    rw [hrun2 _ hmlt] at h1; cases h1
    rw [hrun2 _ hmlt.le] at h2; cases h2
    have h3 := canDecide_of_agreeOn (hagr.mono (by simpa using hp)) hpnv
    have := hR0.canDecide_self_unique hfm h3
    cases v <;> simp at this
  match hδ : ζ[m] with
  | .inv _ _ => rw [hδ] at hδS; exact absurd hδS (by simp [Label.IsStep])
  | .ret q u =>
    rw [hδ] at hstep
    exact (hinv (fun r _ => by rw [(step_ret hstep).2.2.1])).elim
  | .tau q =>
    rw [hδ] at hstep hδQ
    simp only [Label.proc] at hδQ
    rcases step_tau_cases hstep with ⟨r, k, -, hmem⟩ | ⟨w, hw, hmem⟩
    · exact (hinv (fun r _ => by rw [hmem])).elim
    by_cases hin : ∀ r, w r ≠ none → r ∈ Lset
    · exfalso; apply hinv; intro r hr
      have hwr : w r = none := by by_contra h; exact hr (hin r h)
      rw [hmem]; simp [applyW, hwr]
    obtain ⟨r₀, hr₀, hr₀L⟩ : ∃ r₀, w r₀ ≠ none ∧ r₀ ∉ Lset := by
      by_contra hc; apply hin; intro r hr; by_contra hrL; exact hc ⟨r, hr, hrL⟩
    refine ⟨ζ.take m, Zf m, B1 m, hζ.of_prefix (List.take_prefix _ _), hZf m hmlt.le,
      hB1 m hmlt.le, ?_, q, hδQ, r₀, hr₀L, ⟨w, hw, hr₀⟩⟩
    have hqT : q ∉ T1 ++ T2 := fun h => hTQ q h hδQ
    apply bivalent_of_canDecide_not (v := v)
    · exact CanDecide.of_reachBy ⟨blockWrite T2, (steps_blockWrite hT2R).mono hsubR,
        hB2 m hmlt.le⟩ (hfm.mono (by simpa using Or.inr hp))
    · -- commuting `δ` with the block `T1`
      have hpo : ∀ x ∈ T1 ++ q :: T2, ∃ w, I.Poised (Zf m) x w := by
        intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact hBm.poised x (by simp [h])
        · rcases List.mem_cons.1 h with rfl | h
          · exact ⟨w, hw⟩
          · exact hBm.poised x (by simp [h])
      have hnd1 : (T1 ++ q :: T2).Nodup := List.nodup_middle.2 (List.nodup_cons.2 ⟨hqT, hBm.nodup⟩)
      have hnd2 : (q :: (T1 ++ T2)).Nodup := List.nodup_cons.2 ⟨hqT, hBm.nodup⟩
      have hpo2 : ∀ x ∈ q :: (T1 ++ T2), ∃ w, I.Poised (Zf m) x w := by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | h
        · exact ⟨w, hw⟩
        · exact hBm.poised x h
      obtain ⟨E₁, e1, m1, p1, o1, c1⟩ := I.runFrom_block _ (Zf m) hnd1 hpo
      obtain ⟨E₂, e2, m2, p2, o2, c2⟩ := I.runFrom_block _ (Zf m) hnd2 hpo2
      have hE₂ : E₂ = B2 (m + 1) := by
        rw [blockWrite_cons, runFrom_cons, hstep, Option.bind_some, hrun2 _ hmlt] at e2
        exact (Option.some.inj e2).symm
      subst hE₂
      have hE₁ : I.runFrom (B1 m) (Label.tau q :: blockWrite T2) = some E₁ := by
        rw [blockWrite_append, blockWrite_cons, I.runFrom_append_of_eq (hB1 m hmlt.le)] at e1
        exact e1
      have hag : AgreeOn ({p} : Set P) E₁ (B2 (m + 1)) := by
        refine ⟨?_, fun x _ => ?_, fun x _ => by rw [p1, p2]⟩
        · funext i r
          cases i
          rw [m1, m2, foldl_applyW, foldl_applyW]
          have hwq : wvals [w] r = (w r).toList := by
            cases h : w r <;> simp [wvals, h]
          rw [show (T1 ++ q :: T2).map (I.wOf (Zf m)) =
                T1.map (I.wOf (Zf m)) ++ [w] ++ T2.map (I.wOf (Zf m)) by simp [hw.wOf_eq],
              show (q :: (T1 ++ T2)).map (I.wOf (Zf m)) =
                [w] ++ T1.map (I.wOf (Zf m)) ++ T2.map (I.wOf (Zf m)) by simp [hw.wOf_eq],
              wvals_append, wvals_append, wvals_append, wvals_append, hwq]
          cases hwr : w r with
          | none => simp
          | some x =>
            by_cases hrL : r ∈ Lset
            · rcases hBm.cnt2 with hsw | hcnt
              · exfalso
                obtain ⟨-, k, hk⟩ := hw
                exact hr₀L (hsw q _ w k hk r r₀ (by simp [hwr]) hr₀ ▸ hrL)
              · obtain ⟨hne, hle⟩ := hcnt r hrL
                simp only [Option.toList_some, List.foldl_append]
                exact foldl_bufWrite_eq hne hle _ _
            · rw [hBm.wvals_nil_of_notMem (T := T1) (fun x hx => by simp [hx]) hrL,
                hBm.wvals_nil_of_notMem (T := T2) (fun x hx => by simp [hx]) hrL]
              simp
        · by_cases hx : x ∈ T1 ++ q :: T2
          · rw [c1 x hx, c2 x (by simp at hx ⊢; tauto)]
          · rw [o1 x hx, o2 x (by simp at hx ⊢; tauto)]
      have := canDecide_of_agreeOn hag.symm hpnv
      exact CanDecide.of_reachBy ⟨Label.tau q :: blockWrite T2, fun ℓ' hℓ' => by
          rcases List.mem_cons.1 hℓ' with rfl | h
          · exact ⟨Or.inl hδQ, trivial⟩
          · exact ((steps_blockWrite hT2R).mono hsubR) ℓ' h, hE₁⟩
        (this.mono (by simpa using Or.inr hp))

end Cslib.SharedMemory.ComplexityHierarchy
