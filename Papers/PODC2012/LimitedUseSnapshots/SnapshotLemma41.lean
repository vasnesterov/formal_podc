import Papers.PODC2012.LimitedUseSnapshots.SnapshotMain

/-!
# Lemma 4.1 of Aspnes–Attiya–Censor-Hillel–Ellen: pointers grow

If `d` is the index stored at `root.mr` when an `Update` begins, the operation's own root
pointer `ptr` at Line 18 satisfies `ptr > d`; more generally, every pointer that the operation
tries to store into a component of a max array (Lines 8, 10) is larger than the value of that
component when the operation began.

The paper's inductive argument ("the pointer held at its sibling never decreases; since `ptr` is
the sum of these two indices, the claim is true at the parent") leaves implicit why the index
stored at the parent's component at the invocation is at most the sum of the two children's
pointers at that time; here this follows from the monotonicity of the `seq` arrays over the
chain of states of each max array (`SeqR.le`).
-/

namespace Podc.LimitedUseSnapshots.Snapshot

open Cslib.SharedMemory

variable {P V : Type} [DecidableEq P] {T : BTree P} {v₀ : P → V}

/-! ### Local bookkeeping: counters and the phases of an `Update` -/

lemma act_access_cnt {p : P} {l : Loc P V} {i : Obj} {o : (objSpec P V v₀ i).Op}
    {k : (objSpec P V v₀ i).Resp → Loc P V} (h : act T v₀ p l = .access i o k)
    (r : (objSpec P V v₀ i).Resp) : l.cnt ≤ (k r).cnt := by
  rcases l with ⟨n, pc⟩
  cases pc with
  | up a ptr => cases a <;> (simp only [act] at h; cases h; simp)
  | _ => simp only [act] at h; cases h <;> simp

lemma act_ret_cnt {p : P} {l l' : Loc P V} {r : Option (P → V)}
    (h : act T v₀ p l = .ret r l') : l'.cnt = l.cnt := by
  rcases l with ⟨n, pc⟩
  cases pc with
  | up a ptr => cases a <;> (simp only [act] at h; cases h)
  | _ => simp only [act] at h; cases h <;> rfl

/-- Counters never decrease. -/
lemma step_cnt_mono {C C' : Cfg v₀} {ℓ : Label P (swSnap P V v₀)}
    (h : (alg3 T v₀).step C ℓ = some C') : cntOf C ≤ cntOf C' := by
  intro j
  by_cases hj : ℓ.proc = j
  · cases ℓ with
    | inv q o =>
      obtain ⟨-, -, -, hloc, -⟩ := Impl.step_inv h
      simp only [Label.proc] at hj; subst hj
      simp only [cntOf, hloc, Function.update_self]; cases o <;> exact le_rfl
    | tau q =>
      obtain ⟨-, -, i, o, k, hact, -, hloc⟩ := Impl.step_tau h
      simp only [Label.proc] at hj; subst hj
      simp only [cntOf, hloc, Function.update_self]; exact act_access_cnt hact _
    | ret q r =>
      obtain ⟨-, -, -, l, hact, hloc⟩ := Impl.step_ret h
      simp only [Label.proc] at hj; subst hj
      simp only [cntOf, hloc, Function.update_self]; exact (act_ret_cnt hact).ge
  · simp [cntOf, (Impl.step_other h hj).1]

lemma runFrom_cnt_mono : ∀ (γ : List (Label P (swSnap P V v₀))) {C C' : Cfg v₀},
    (alg3 T v₀).runFrom C γ = some C' → cntOf C ≤ cntOf C'
  | [], _, _, h => by simp only [Impl.runFrom_nil, Option.some.injEq] at h; subst h; exact le_rfl
  | ℓ :: γ, C, C', h => by
    simp only [Impl.runFrom_cons] at h
    cases hs : (alg3 T v₀).step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      exact (step_cnt_mono hs).trans (runFrom_cnt_mono γ h)

/-- The program counters of an `Update` after Line 5. -/
def PC.IsUpd : PC P V → Prop
  | .up _ _ | .sc _ | .rl _ _ _ | .rr _ _ _ _ | .wv _ _ _ | .wm _ | .ackU => True
  | _ => False

/-- The local state of a process during an `Update` invoked with counter `c₀`. -/
def UpdPhase (c₀ : ℕ) (l : Loc P V) : Prop :=
  ((∃ v, l.pc = .lw v) ∧ l.cnt = c₀) ∨ (l.pc.IsUpd ∧ l.cnt = c₀ + 1)

lemma act_phase {p : P} {l : Loc P V} {i : Obj} {o : (objSpec P V v₀ i).Op}
    {k : (objSpec P V v₀ i).Resp → Loc P V} (h : act T v₀ p l = .access i o k) {c₀ : ℕ}
    (hl : UpdPhase c₀ l) (r : (objSpec P V v₀ i).Resp) : UpdPhase c₀ (k r) := by
  rcases l with ⟨n, pc⟩
  rcases hl with ⟨⟨v, hv⟩, hn⟩ | ⟨hu, hn⟩
  · simp only at hv hn; subst hv hn
    simp only [act] at h; cases h
    right; simp only [cont]; split_ifs <;> simp [PC.IsUpd]
  · simp only at hn; subst hn
    cases pc with
    | up a ptr =>
      cases a <;> simp only [act] at h <;> cases h <;> right <;> simp [PC.IsUpd]
    | wv q k' val =>
      simp only [act] at h; cases h
      right; simp only [cont]; split_ifs <;> simp [PC.IsUpd]
    | idle | ackU | retS _ => simp only [act] at h; cases h
    | lw _ | s0 | s1 _ => simp [PC.IsUpd] at hu
    | sc _ | rl _ _ _ | rr _ _ _ _ | wm _ =>
      simp only [act] at h; cases h; right; simp [PC.IsUpd]

/-- During an `Update` that has not returned, the process stays pending and in an `Update`
phase. -/
lemma phase_runFrom {p : P} {c₀ : ℕ} : ∀ (β : List (Label P (swSnap P V v₀))) {C C' : Cfg v₀},
    (alg3 T v₀).runFrom C β = some C' → (∀ r, .ret p r ∉ β) → C.pend p ≠ none →
    UpdPhase c₀ (C.loc p) → C'.pend p ≠ none ∧ UpdPhase c₀ (C'.loc p)
  | [], _, _, h, _, hp, hl => by
    simp only [Impl.runFrom_nil, Option.some.injEq] at h; subst h; exact ⟨hp, hl⟩
  | ℓ :: β, C, C', h, hr, hp, hl => by
    simp only [Impl.runFrom_cons] at h
    cases hs : (alg3 T v₀).step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      have hr' : ∀ r, .ret p r ∉ β := fun r hm => hr r (List.mem_cons_of_mem _ hm)
      refine phase_runFrom β h hr' ?_ ?_
      · by_cases hq : ℓ.proc = p
        · cases ℓ with
          | inv q o =>
            simp only [Label.proc] at hq; subst hq; exact absurd (Impl.step_inv hs).1 hp
          | tau q => rw [(Impl.step_tau hs).2.1]; exact hp
          | ret q r =>
            simp only [Label.proc] at hq; subst hq; exact absurd List.mem_cons_self (hr r)
        · rw [(Impl.step_other hs hq).2]; exact hp
      · by_cases hq : ℓ.proc = p
        · cases ℓ with
          | inv q o =>
            simp only [Label.proc] at hq; subst hq; exact absurd (Impl.step_inv hs).1 hp
          | tau q =>
            simp only [Label.proc] at hq; subst hq
            obtain ⟨-, -, i, o, k, hact, -, hloc⟩ := Impl.step_tau hs
            rw [hloc, Function.update_self]; exact act_phase hact hl _
          | ret q r =>
            simp only [Label.proc] at hq; subst hq; exact absurd List.mem_cons_self (hr r)
        · rw [(Impl.step_other hs hq).1]; exact hl

/-- The common setting of Lemma 4.1: an `Update` of `p` invoked after `α` (configuration `C₀`)
and not yet returned after `β` (configuration `C`). -/
lemma lemma_4_1_setup (hT : T.WF) {α β : List (Label P (swSnap P V v₀))} {p : P} {v : V}
    {C₀ C : Cfg v₀} (h₀ : (alg3 T v₀).run α = some C₀)
    (h : (alg3 T v₀).run (α ++ .inv p (.update p v) :: β) = some C)
    (hret : ∀ r, .ret p r ∉ β) :
    ∃ R₀ L₀ s₀₀ R L s₀, Inv T α C₀ R₀ L₀ s₀₀ ∧ Inv T (α ++ .inv p (.update p v) :: β) C R L s₀ ∧
      (∀ a, R₀ a ⊆ R a) ∧ cntOf C₀ ≤ cntOf C ∧ s₀₀ p = (C₀.loc p).cnt ∧
      UpdPhase (C₀.loc p).cnt (C.loc p) := by
  obtain ⟨R₀, L₀, s₀₀, hI₀⟩ := exists_inv hT h₀
  have hrun : (alg3 T v₀).runFrom C₀ (.inv p (.update p v) :: β) = some C := by
    rw [← h, (alg3 T v₀).run_append_of_eq h₀]
  obtain ⟨R, L, s₀, hI, hR⟩ := inv_runFrom hT _ h₀ hI₀ hrun
  simp only [Impl.runFrom_cons] at hrun
  cases hs : (alg3 T v₀).step C₀ (.inv p (.update p v)) with
  | none => simp [hs] at hrun
  | some C₁ =>
    simp only [hs, Option.bind_some] at hrun
    obtain ⟨hpend, -, hpend₁, hloc₁, -⟩ := Impl.step_inv hs
    have hidle := (hpend ▸ hI₀.proc p).pc_idle
    have hP := hI₀.proc p
    simp only [PInv, hidle] at hP
    have hph := phase_runFrom (c₀ := (C₀.loc p).cnt) β hrun hret
      (by simp [hpend₁]) (by left; simp [hloc₁])
    exact ⟨R₀, L₀, s₀₀, R, L, s₀, hI₀, hI, hR,
      (step_cnt_mono hs).trans (runFrom_cnt_mono β hrun), hP.2, hph.2⟩

/-- **Lemma 4.1** of [Aspnes–Attiya–Censor-Hillel–Ellen]: if `d₀` is the index stored at
`root.mr` when an `Update` operation begins (configuration `C₀`), then `ptr > d₀` when the
operation performs `WriteMax(root.mr, ptr)` on Line 18 (it is then poised at `wm ptr`). -/
theorem lemma_4_1 (hT : T.WF) {α β : List (Label P (swSnap P V v₀))} {p : P} {v : V}
    {C₀ C : Cfg v₀} (h₀ : (alg3 T v₀).run α = some C₀)
    (h : (alg3 T v₀).run (α ++ .inv p (.update p v) :: β) = some C)
    (hret : ∀ r, .ret p r ∉ β) {ptr : ℕ} (hpc : (C.loc p).pc = .wm ptr) :
    C₀.mem .mr < ptr := by
  obtain ⟨R₀, L₀, s₀₀, R, L, s₀, hI₀, hI, hR, hcnt, hs₀₀, hph⟩ := lemma_4_1_setup hT h₀ h hret
  have hP := hI.proc p
  simp only [PInv, hpc] at hP
  obtain ⟨-, s, hs, hsi, -⟩ := hP
  have hn : (C.loc p).cnt = (C₀.loc p).cnt + 1 := by
    rcases hph with ⟨⟨v, hv⟩, -⟩ | ⟨-, hn⟩
    · rw [hpc] at hv; cases hv
    · exact hn
  by_contra hle
  have hroot := SeqR.mono hR hcnt hI₀.g.root.1
  have : s p ≤ s₀₀ p := SeqR.le hI.g.chain hs hroot (not_lt.1 hle) p
  omega

/-- **Lemma 4.1**, the claim in its proof: when an `Update` tries to update (Line 8 or 10) the
component of `u.parent.ma` that holds the pointer of node `u` (address `b :: q`) to `ptr`, then
`ptr` is greater than the value of that component when the `Update` began. -/
theorem lemma_4_1_maxUpdate (hT : T.WF) {α β : List (Label P (swSnap P V v₀))} {p : P} {v : V}
    {C₀ C : Cfg v₀} (h₀ : (alg3 T v₀).run α = some C₀)
    (h : (alg3 T v₀).run (α ++ .inv p (.update p v) :: β) = some C)
    (hret : ∀ r, .ret p r ∉ β) {b : Bool} {q : List Bool} {ptr : ℕ}
    (hpc : (C.loc p).pc = .up (b :: q) ptr) :
    (if b then (C₀.mem (.ma q)).2 else (C₀.mem (.ma q)).1) < ptr := by
  obtain ⟨R₀, L₀, s₀₀, R, L, s₀, hI₀, hI, hR, hcnt, hs₀₀, hph⟩ := lemma_4_1_setup hT h₀ h hret
  have hP := hI.proc p
  simp only [PInv, hpc] at hP
  obtain ⟨-, -, hsuf, t, hsubt, s, hs, hsi, -⟩ := hP
  have hn : (C.loc p).cnt = (C₀.loc p).cnt + 1 := by
    rcases hph with ⟨⟨v, hv⟩, -⟩ | ⟨-, hn⟩
    · rw [hpc] at hv; cases hv
    · exact hn
  obtain ⟨-, lt, rt, hsubq, hchild⟩ := BTree.exists_parent (hT.mem p) hsuf
  obtain ⟨⟨s₁, h₁, -⟩, ⟨s₂, h₂, -⟩⟩ :=
    hI₀.g.reach q lt rt hsubq _ _ (hI₀.g.cur q)
  by_contra hle
  cases b with
  | false =>
    have ht : t = lt := by rw [hsubt] at hchild; exact (Option.some.inj hchild).symm
    subst ht
    have hc : s₁ p ≤ (C₀.loc p).cnt := seq_le_cnt hT (by simp [hsubq, BTree.child]) h₁ p
    have : s p ≤ s₁ p := SeqR.le hI.g.chain hs (SeqR.mono hR hcnt h₁) (by simpa using hle) p
    omega
  | true =>
    have ht : t = rt := by rw [hsubt] at hchild; exact (Option.some.inj hchild).symm
    subst ht
    have hc : s₂ p ≤ (C₀.loc p).cnt := seq_le_cnt hT (by simp [hsubq, BTree.child]) h₂ p
    have : s p ≤ s₂ p := SeqR.le hI.g.chain hs (SeqR.mono hR hcnt h₂) (by simpa using hle) p
    omega

end Podc.LimitedUseSnapshots.Snapshot
