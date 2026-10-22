import Papers.PODC2016.ReliableStorageSpace.Solo

/-!
# The adversary `Ad` (Section 4, Definition 1, Observations 1 and 3, Lemma 3)

For a write `w = (c, k)`, `Out X w` is the set of blocks of `w` stored outside its writer: in some base
object, or held (in the local state or in a pending RMW) by another client. A client is *quiet*
(`Quiet`, the paper's `C⁻`) if no block of any of its writes is outside it. The adversary `Ad`:

1. if some quiet client has a pending RMW on an object not in `F(t)` (`Full`), executes the oldest such
   RMW (it takes effect and responds);
2. otherwise schedules the next client in round-robin order (`rr`), so its next action (e.g. a
   trigger) happens without any RMW taking effect.

`Inv` is the invariant behind Lemma 3: for every write, the blocks outside its writer are either none,
or fewer than `D` bits, or all in a single object of `F(t)` (which `Ad` never touches again). It holds
along every run of `Ad` (`inv_Ad`), and gives Lemma 3 (`lemma3`): objects outside `F(t)` never hold
`D` bits of any single write.
-/

noncomputable section

namespace Podc.ReliableStorageSpace

open Finset Classical

variable {C N J V : Type}

namespace Alg

variable (A : Alg C N J V) [Fintype C] [Fintype N] [Fintype V]

/-- Blocks of `w` outside its writer. -/
def Out (X : A.Config) (w : OpId C) : Finset (Blk C J) :=
  ofW w ((univ.biUnion fun o => A.oblk (X.obj o)) ∪ (univ.filter (· ≠ w.1)).biUnion (A.held X))

theorem mem_Out {X : A.Config} {w : OpId C} {b : Blk C J} :
    b ∈ A.Out X w ↔ b.1 = w ∧ ((∃ o, b ∈ A.oblk (X.obj o)) ∨ ∃ c, c ≠ w.1 ∧ b ∈ A.held X c) := by
  simp [Out, mem_ofW, and_comm]

/-- The paper's `C⁻`: no block of any write of `c` is stored outside `c`. -/
def Quiet (X : A.Config) (c : C) : Prop := ∀ k, A.Out X (c, k) = ∅

/-- All blocks of `w` outside its writer are in the single object `o₀ ∈ F(t)`. -/
def Frozen (X : A.Config) (w : OpId C) : Prop :=
  ∃ o₀ ∈ A.Full X, (∀ o, o ≠ o₀ → ∀ b ∈ A.oblk (X.obj o), b.1 ≠ w) ∧
    (∀ c, c ≠ w.1 → ∀ b ∈ A.held X c, b.1 ≠ w)

/-- The invariant behind Lemma 3. -/
def Inv (X : A.Config) : Prop :=
  ∀ w, A.Out X w = ∅ ∨ A.bits (A.Out X w) < D (V := V) ∨ A.Frozen X w

/-- Candidates of rule 1 of `Ad`: pending RMWs of quiet clients on objects not in `F(t)`. -/
def cand (X : A.Config) (p : Pend C N A.R) : Bool := decide (A.Quiet X p.cl ∧ p.obj ∉ A.Full X)

/-- Round robin over the clients. -/
def rr [Nonempty C] (i : ℕ) : C :=
  (Fintype.equivFin C).symm ⟨i % Fintype.card C, Nat.mod_lt _ Fintype.card_pos⟩

/-- **The adversary `Ad`** (Definition 1). -/
def Ad [Nonempty C] (X : A.Config) : Event C :=
  match X.pend.find? (A.cand X) with
  | some p => .exec p.cl p.idx
  | none => .step (rr X.tick)

theorem Ad_cases [Nonempty C] (X : A.Config) :
    (∃ p ∈ X.pend, A.Quiet X p.cl ∧ p.obj ∉ A.Full X ∧ A.Ad X = .exec p.cl p.idx ∧
      ∃ as bs, X.pend = as ++ p :: bs ∧ ∀ a ∈ as, ¬ (A.Quiet X a.cl ∧ a.obj ∉ A.Full X)) ∨
    ((∀ p ∈ X.pend, ¬ (A.Quiet X p.cl ∧ p.obj ∉ A.Full X)) ∧ A.Ad X = .step (rr X.tick)) := by
  rcases h : X.pend.find? (A.cand X) with _ | p
  · right
    refine ⟨fun p hp => ?_, by rw [Ad, h]⟩
    have := List.find?_eq_none.1 h p hp
    simpa [cand] using this
  · left
    obtain ⟨h1, as, bs, h2, h3⟩ := List.find?_eq_some_iff_append.1 h
    simp only [cand, decide_eq_true_eq] at h1
    refine ⟨p, List.mem_of_find?_eq_some h, h1.1, h1.2, by rw [Ad, h], as, bs, h2, fun a ha => ?_⟩
    have := h3 a ha
    rintro ⟨h4, h5⟩
    simp [cand, h4, h5] at this

/-! ### Frame lemmas -/

theorem full_congr {X Y : A.Config} (h : X.obj = Y.obj) : A.Full X = A.Full Y := by
  simp [Full, h]

theorem mem_full_congr {X Y : A.Config} {o : N} (h : X.obj o = Y.obj o) :
    o ∈ A.Full X ↔ o ∈ A.Full Y := by
  simp [Full, h]

/-- An event that is not an effective `exec`. -/
def NoExec (X : A.Config) (e : Event C) : Prop := ¬ ∃ c m p, e = .exec c m ∧ A.findP X c m = some p

theorem obj_eq_of_noExec {X : A.Config} {e : Event C} (h : A.NoExec X e) :
    (A.step X e).obj = X.obj :=
  funext fun o => A.obj_step_of_not_exec X e o fun ⟨c, m, p, he, hp, _⟩ => h ⟨c, m, p, he, hp⟩

theorem held_noExec {X : A.Config} {e : Event C} (h : A.NoExec X e) {c : C} {b : Blk C J}
    (hb : b ∈ A.held (A.step X e) c) : b ∈ A.held X c ∨ b.1.1 = c := by
  rcases A.held_step X e c b hb with hb | ⟨-, hb⟩ | ⟨m, p, he, hp, -⟩
  · exact Or.inl hb
  · exact Or.inr (by rw [hb])
  · exact absurd ⟨c, m, p, he, hp⟩ h

theorem out_noExec {X : A.Config} {e : Event C} (h : A.NoExec X e) (w : OpId C) :
    A.Out (A.step X e) w ⊆ A.Out X w := by
  intro b hb
  rw [mem_Out] at hb ⊢
  refine ⟨hb.1, ?_⟩
  rcases hb with ⟨hbw, ⟨o, ho⟩ | ⟨c, hc, hbc⟩⟩
  · rw [A.obj_eq_of_noExec h] at ho
    exact Or.inl ⟨o, ho⟩
  · rcases A.held_noExec h hbc with hbc | hbc
    · exact Or.inr ⟨c, hc, hbc⟩
    · exact absurd (show c = w.1 by rw [← hbw, hbc]) hc

theorem inv_noExec {X : A.Config} {e : Event C} (h : A.NoExec X e) (hI : A.Inv X) :
    A.Inv (A.step X e) := by
  intro w
  have hsub := A.out_noExec h w
  rcases hI w with h0 | h1 | ⟨o₀, ho₀, hobj, hcl⟩
  · exact Or.inl (Finset.subset_empty.1 (h0 ▸ hsub))
  · exact Or.inr (Or.inl (lt_of_le_of_lt (A.bits_mono hsub) h1))
  · refine Or.inr (Or.inr ⟨o₀, ?_, ?_, ?_⟩)
    · rwa [A.full_congr (A.obj_eq_of_noExec h)]
    · intro o ho b hb
      rw [A.obj_eq_of_noExec h] at hb
      exact hobj o ho b hb
    · intro c hc b hb hbw
      rcases A.held_noExec h hb with hb | hb
      · exact hcl c hc b hb hbw
      · exact hc (hbw ▸ hb).symm

/-- Executing a candidate RMW preserves `Inv`: the core of Lemma 3. -/
theorem inv_exec {X : A.Config} (hI : A.Inv X) {p : Pend C N A.R}
    (hp : A.findP X p.cl p.idx = some p) (hq : A.Quiet X p.cl) (hF : p.obj ∉ A.Full X) :
    A.Inv (A.step X (.exec p.cl p.idx)) := by
  set X' := A.step X (.exec p.cl p.idx) with hX'
  set c := p.cl
  have hpX : p ∈ X.pend := (findP_spec hp).1
  have hobj : ∀ o, o ≠ p.obj → X'.obj o = X.obj o := by
    intro o ho
    rw [hX', step_exec_some hp]
    simp [Function.update_apply, ho]
  -- flow facts
  have hO : ∀ o b, b ∈ A.oblk (X'.obj o) →
      b ∈ A.oblk (X.obj o) ∨ (o = p.obj ∧ b ∈ A.held X c) := by
    intro o b hb
    rcases A.oblk_step X _ o b hb with hb | ⟨c', m, p', he, hp', hpo, hb⟩
    · exact Or.inl hb
    · simp only [Event.exec.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [hp] at hp'
      cases hp'
      exact Or.inr ⟨hpo.symm, A.mem_held.2 (Or.inr ⟨p, hpX, rfl, hb⟩)⟩
  have hHc : ∀ c' b, b ∈ A.held X' c' →
      b ∈ A.held X c' ∨ b.1.1 = c' ∨ (c' = c ∧ b ∈ A.oblk (X.obj p.obj)) := by
    intro c' b hb
    rcases A.held_step X _ c' b hb with hb | ⟨-, hb⟩ | ⟨m, p', he, hp', hb⟩
    · exact Or.inl hb
    · exact Or.inr (Or.inl (by rw [hb]))
    · simp only [Event.exec.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [hp] at hp'
      cases hp'
      exact Or.inr (Or.inr ⟨rfl, hb⟩)
  -- blocks of other writes outside their writer only shrink
  have hsub : ∀ w, w.1 ≠ c → A.Out X' w ⊆ A.Out X w := by
    intro w hw b hb
    rw [mem_Out] at hb ⊢
    refine ⟨hb.1, ?_⟩
    rcases hb with ⟨hbw, ⟨o, ho⟩ | ⟨c', hc', hb⟩⟩
    · rcases hO o b ho with ho | ⟨-, ho⟩
      · exact Or.inl ⟨o, ho⟩
      · exact Or.inr ⟨c, fun h => hw h.symm, ho⟩
    · rcases hHc c' b hb with hb | hb | ⟨-, hb2⟩
      · exact Or.inr ⟨c', hc', hb⟩
      · exact absurd (hbw ▸ hb).symm hc'
      · exact Or.inl ⟨_, hb2⟩
  intro w
  by_cases hw : w.1 = c
  · -- the executing client's own write: nothing of it was outside before
    have h0 : A.Out X w = ∅ := by
      have := hq w.2
      rwa [show ((c, w.2) : OpId C) = w from Prod.ext hw.symm rfl] at this
    have hin : ∀ b ∈ A.Out X' w, b ∈ A.oblk (X'.obj p.obj) := by
      intro b hb
      rw [mem_Out] at hb
      rcases hb with ⟨hbw, ⟨o, ho⟩ | ⟨c', hc', hb⟩⟩
      · by_cases hop : o = p.obj
        · exact hop ▸ ho
        · rw [hobj o hop] at ho
          have : b ∈ A.Out X w := A.mem_Out.2 ⟨hbw, Or.inl ⟨o, ho⟩⟩
          simp [h0] at this
      · rcases hHc c' b hb with hb | hb | ⟨hcc, -⟩
        · have : b ∈ A.Out X w := A.mem_Out.2 ⟨hbw, Or.inr ⟨c', hc', hb⟩⟩
          simp [h0] at this
        · exact absurd (hbw ▸ hb).symm hc'
        · exact absurd (hw.trans hcc.symm) (Ne.symm hc')
    by_cases hlt : A.bits (A.Out X' w) < D (V := V)
    · exact Or.inr (Or.inl hlt)
    · refine Or.inr (Or.inr ⟨p.obj, ?_, ?_, ?_⟩)
      · simp only [Full, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨w, le_trans (not_lt.1 hlt) (A.bits_mono fun b hb => ?_)⟩
        exact mem_ofW.2 ⟨hin b hb, (A.mem_Out.1 hb).1⟩
      · intro o ho b hb hbw
        rw [hobj o ho] at hb
        have : b ∈ A.Out X w := A.mem_Out.2 ⟨hbw, Or.inl ⟨o, hb⟩⟩
        simp [h0] at this
      · intro c' hc' b hb hbw
        rcases hHc c' b hb with hb | hb | ⟨hcc, -⟩
        · have : b ∈ A.Out X w := A.mem_Out.2 ⟨hbw, Or.inr ⟨c', hc', hb⟩⟩
          simp [h0] at this
        · exact hc' (hbw ▸ hb).symm
        · exact hc' (hcc.trans hw.symm)
  · rcases hI w with h0 | h1 | ⟨o₀, ho₀, hfo, hfc⟩
    · exact Or.inl (Finset.subset_empty.1 (h0 ▸ hsub w hw))
    · exact Or.inr (Or.inl (lt_of_le_of_lt (A.bits_mono (hsub w hw)) h1))
    · have hne : o₀ ≠ p.obj := fun h => hF (h ▸ ho₀)
      refine Or.inr (Or.inr ⟨o₀, (A.mem_full_congr (hobj o₀ hne)).2 ho₀, ?_, ?_⟩)
      · intro o ho b hb hbw
        rcases hO o b hb with hb | ⟨-, hb⟩
        · exact hfo o ho b hb hbw
        · exact hfc c (Ne.symm hw) b hb hbw
      · intro c' hc' b hb hbw
        rcases hHc c' b hb with hb | hb | ⟨-, hb⟩
        · exact hfc c' hc' b hb hbw
        · exact hc' (hbw ▸ hb).symm
        · exact hfo p.obj (Ne.symm hne) b hb hbw

/-! ### Runs of `Ad` -/

variable [Nonempty C]

/-- One step of `Ad` preserves `Inv`. -/
theorem inv_step_Ad {X : A.Config} (hok : A.PendOK X) (hI : A.Inv X) :
    A.Inv (A.step X (A.Ad X)) := by
  rcases A.Ad_cases X with ⟨p, hp, hq, hF, he, -⟩ | ⟨-, he⟩ <;> rw [he]
  · exact A.inv_exec hI (hok.findP_eq hp) hq hF
  · exact A.inv_noExec (fun ⟨c, m, p, h, _⟩ => by cases h) hI

/-- **Observation 3**: `Ad` never changes an object of `F(t)`, so `F(t)` only grows. -/
theorem full_step_Ad {X : A.Config} (hok : A.PendOK X) :
    A.Full X ⊆ A.Full (A.step X (A.Ad X)) := by
  intro o ho
  rcases A.Ad_cases X with ⟨p, hp, -, hF, he, -⟩ | ⟨-, he⟩ <;> rw [he]
  · have hne : o ≠ p.obj := fun h => hF (h ▸ ho)
    refine (A.mem_full_congr ?_).2 ho
    rw [step_exec_some (hok.findP_eq hp)]
    simp [Function.update_apply, hne]
  · rwa [A.full_congr (A.obj_eq_of_noExec (fun ⟨c, m, p, h, _⟩ => by cases h))]

theorem inv_init : A.Inv A.init := by
  intro w
  left
  ext b
  simp only [mem_Out, init, A.oinit_blk, Finset.notMem_empty, exists_false, false_or,
    Finset.notMem_empty, iff_false, not_and]
  intro _ ⟨c, _, hb⟩
  rw [mem_held] at hb
  simp [init, A.linit_blk] at hb

theorem inv_runFrom_noExec {X : A.Config} (hI : A.Inv X) (evs : List (Event C))
    (h : ∀ e ∈ evs, ∀ c m, e ≠ .exec c m) : A.Inv (A.runFrom X evs) := by
  induction evs generalizing X with
  | nil => exact hI
  | cons e evs ih =>
    exact ih (A.inv_noExec (fun ⟨c, m, p, he, _⟩ => h e (by simp) c m he) hI)
      (fun e' he' => h e' (by simp [he']))

theorem inv_srun_Ad {X : A.Config} (hok : A.PendOK X) (hI : A.Inv X) (t : ℕ) :
    A.Inv (A.srun X A.Ad t) := by
  induction t with
  | zero => exact hI
  | succ t ih => exact A.inv_step_Ad (A.pendOK_srun hok _ t) ih

/-- **Lemma 3** (information-theoretic form): under `Inv`, a set `B` of objects disjoint from `F(t)`
holds fewer than `D` bits of blocks of any single write. -/
theorem lemma3 {X : A.Config} (hI : A.Inv X) (hD : 0 < D (V := V)) (B : Finset N)
    (hB : ∀ o ∈ B, o ∉ A.Full X) (w : OpId C) :
    A.bits (ofW w (B.biUnion fun o => A.oblk (X.obj o))) < D (V := V) := by
  have hsub : ofW w (B.biUnion fun o => A.oblk (X.obj o)) ⊆ A.Out X w := by
    intro b hb
    rw [mem_ofW, Finset.mem_biUnion] at hb
    obtain ⟨⟨o, -, ho⟩, hbw⟩ := hb
    exact A.mem_Out.2 ⟨hbw, Or.inl ⟨o, ho⟩⟩
  rcases hI w with h0 | h1 | ⟨o₀, ho₀, hfo, -⟩
  · have h2 := Finset.subset_empty.1 (h0 ▸ hsub)
    rw [h2]
    simpa [bits] using hD
  · exact lt_of_le_of_lt (A.bits_mono hsub) h1
  · have : ofW w (B.biUnion fun o => A.oblk (X.obj o)) = ∅ := by
      ext b
      simp only [mem_ofW, Finset.mem_biUnion, Finset.notMem_empty, iff_false, not_and]
      rintro ⟨o, ho, hb⟩ hbw
      exact hfo o (fun h => hB o ho (h ▸ ho₀)) b hb hbw
    rw [this]
    simpa [bits] using hD

/-- **Observation 1**: every client that is not quiet contributes at least one bit to the storage. -/
theorem obs1 (X : A.Config) (W : Finset C) :
    (W.filter fun c => ¬ A.Quiet X c).card ≤ A.storage X := by
  set U := (univ.biUnion fun o => A.oblk (X.obj o)) ∪
    univ.biUnion (fun c => (A.held X c).filter (·.1.1 ≠ c))
  have h1 : U.card ≤ A.storage X := by
    refine le_trans (Finset.card_union_le _ _) (add_le_add ?_ ?_)
    · exact le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun o _ => A.card_le_bits _)
    · exact le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun c _ => A.card_le_bits _)
  refine le_trans ?_ h1
  have hpick : ∀ c ∈ W.filter (fun c => ¬ A.Quiet X c), ∃ b ∈ U, b.1.1 = c := by
    intro c hc
    simp only [Finset.mem_filter, Quiet, not_forall] at hc
    obtain ⟨k, hk⟩ := hc.2
    obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.2 hk
    rw [mem_Out] at hb
    obtain ⟨hbw, ⟨o, ho⟩ | ⟨c', hc', hbc⟩⟩ := hb
    · exact ⟨b, Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨o, Finset.mem_univ _, ho⟩),
        by rw [hbw]⟩
    · refine ⟨b, Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨c', Finset.mem_univ _, ?_⟩),
        by rw [hbw]⟩
      rw [Finset.mem_filter]
      exact ⟨hbc, by rw [hbw]; exact Ne.symm hc'⟩
  refine le_trans (Finset.card_le_card fun c hc => ?_) (Finset.card_image_le (s := U) (f := fun b => b.1.1))
  obtain ⟨b, hb, hbc⟩ := hpick c hc
  exact Finset.mem_image.2 ⟨b, hb, hbc⟩

end Alg

end Podc.ReliableStorageSpace

end
