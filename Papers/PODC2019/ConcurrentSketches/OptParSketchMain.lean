import Papers.PODC2019.ConcurrentSketches.OptParSketchStep

/-!
# Theorem 1: `OptParSketch` is strongly linearisable with respect to `SeqSketch_{2Nb}`

**Theorem 1** (PODC version, Section 5.2; full version Section 6.3). `OptParSketch`
instantiated with `SeqSketch` is strongly linearisable with regards to `SeqSketch_{2Nb}`.

The paper proves it by simulating `OptParSketch` with `ParSketch` running `2N` update threads.
We prove it directly (`theorem1`), by the ghost/invariant method used for Lemma 1: the strong
linearization function is again `l` (updates at their invocation, queries at their snapshot),
and the witness in `SeqSketch` is the visibility order `f` (accepted updates become visible when
the propagator merges the batch containing them). Every update thread has at most `2b`
unpropagated updates (its active buffer and the batch handed over to the propagator), which
gives the relaxation `2Nb`. As for `ParSketch`, we also prove the stronger property used by the
error analysis (`theorem1_pastOnly`): no query is dropped and queries see only the past.
-/

set_option linter.unusedSectionVars false

namespace Podc.ConcurrentSketches

open Cslib.SharedMemory

variable {S : Composable} {N : ℕ} {Q : Type} [NeZero N] [DecidableEq Q] {b : ℕ} {hint₀ : S.Hint}

/-- Every step is covered by one of the step lemmas. -/
theorem oinv_step (hb : 0 < b) {α : List (Lbl S N Q)} {C C' : OCfg S N Q} {g : OGhost S N Q}
    {ℓ : Lbl S N Q} (hC : (optParSketch S N Q b hint₀).run α = some C) (hI : OInv b α C g)
    (hs : (optParSketch S N Q b hint₀).step C ℓ = some C') :
    OInv b (α ++ [ℓ]) C' (ogstep α C g ℓ) := by
  cases ℓ with
  | inv p o => exact oinv_step_inv hC hI hs
  | ret p r => exact oinv_step_ret hI hs
  | tau p =>
    cases p with
    | upd j => exact oinv_step_tau_upd hb hI hs
    | prop => exact oinv_step_tau_prop hI hs
    | qry q => exact oinv_step_tau_qry hC hI hs

/-- The invariant holds along every execution. -/
theorem oinv_run (hb : 0 < b) (h₀ : S.Safe hint₀ []) {α : List (Lbl S N Q)} {C : OCfg S N Q}
    (hC : (optParSketch S N Q b hint₀).run α = some C) : OInv b α C (oghost b hint₀ α) :=
  Impl.run_induction (Q := fun α C => OInv b α C (oghost b hint₀ α)) (oinv_init hb h₀)
    (fun α C ℓ C' hC hI hs => by rw [oghost_concat _ _ _ _ hC]; exact oinv_step hb hC hI hs) hC

/-! ## The ghost run only grows -/

lemma ogstep_lin (α : List (Lbl S N Q)) (C : OCfg S N Q) (g : OGhost S N Q) (ℓ : Lbl S N Q) :
    ∃ c, (ogstep α C g ℓ).lin = g.lin ++ c ∧ c.length ≤ 1 := by
  rcases ℓ with ⟨p, o⟩ | ⟨p, r⟩ | p
  · rcases p with j | _ | q
    · rcases o with a | _ | _
      · simp only [ogstep]
        split
        · split <;> exact ⟨_, rfl, by simp⟩
        · exact ⟨[], by simp, by simp⟩
      all_goals exact ⟨[], by simp [ogstep], by simp⟩
    all_goals exact ⟨[], by simp [ogstep], by simp⟩
  · exact ⟨[], by simp [ogstep], by simp⟩
  · rcases p with j | _ | q
    · simp only [ogstep]; split <;> exact ⟨[], by simp, by simp⟩
    · simp only [ogstep]; split <;> exact ⟨[], by simp, by simp⟩
    · simp only [ogstep]; split
      · exact ⟨_, rfl, by simp⟩
      · exact ⟨[], by simp, by simp⟩

lemma ogstep_vis (α : List (Lbl S N Q)) (C : OCfg S N Q) (g : OGhost S N Q) (ℓ : Lbl S N Q) :
    ∃ d, (ogstep α C g ℓ).vis = g.vis ++ d := by
  rcases ℓ with ⟨p, o⟩ | ⟨p, r⟩ | p
  · rcases p with j | _ | q
    · rcases o with a | _ | _
      · simp only [ogstep]
        split
        · split
          · exact ⟨[], by simp⟩
          · exact ⟨_, rfl⟩
        · exact ⟨[], by simp⟩
      all_goals exact ⟨[], by simp [ogstep]⟩
    all_goals exact ⟨[], by simp [ogstep]⟩
  · exact ⟨[], by simp [ogstep]⟩
  · rcases p with j | _ | q
    · simp only [ogstep]; split <;> exact ⟨[], by simp⟩
    · simp only [ogstep]; split
      · exact ⟨_, rfl⟩
      · exact ⟨[], by simp⟩
    · simp only [ogstep]; split
      · exact ⟨_, rfl⟩
      · exact ⟨[], by simp⟩

lemma oghost_concat_lin (α : List (Lbl S N Q)) (ℓ : Lbl S N Q) :
    ∃ c, (oghost b hint₀ (α ++ [ℓ])).lin = (oghost b hint₀ α).lin ++ c ∧ c.length ≤ 1 := by
  cases hC : (optParSketch S N Q b hint₀).run α with
  | none => exact ⟨[], by simp [oghost, oghostRev, hC], by simp⟩
  | some C => rw [oghost_concat _ _ _ _ hC]; exact ogstep_lin _ _ _ _

lemma oghost_concat_vis (α : List (Lbl S N Q)) (ℓ : Lbl S N Q) :
    ∃ d, (oghost b hint₀ (α ++ [ℓ])).vis = (oghost b hint₀ α).vis ++ d := by
  cases hC : (optParSketch S N Q b hint₀).run α with
  | none => exact ⟨[], by simp [oghost, oghostRev, hC]⟩
  | some C => rw [oghost_concat _ _ _ _ hC]; exact ogstep_vis _ _ _ _

lemma oghost_lin_prefix {α β : List (Lbl S N Q)} (h : α <+: β) :
    (oghost b hint₀ α).lin <+: (oghost b hint₀ β).lin := by
  obtain ⟨γ, rfl⟩ := h
  induction γ using List.reverseRecOn with
  | nil => simp
  | append_singleton γ ℓ ih =>
    rw [← List.append_assoc]
    obtain ⟨c, hc, -⟩ := oghost_concat_lin (b := b) (hint₀ := hint₀) (α ++ γ) ℓ
    rw [hc]; exact ih.trans (List.prefix_append _ _)

lemma oghost_vis_prefix {α β : List (Lbl S N Q)} (h : α <+: β) :
    (oghost b hint₀ α).vis <+: (oghost b hint₀ β).vis := by
  obtain ⟨γ, rfl⟩ := h
  induction γ using List.reverseRecOn with
  | nil => simp
  | append_singleton γ ℓ ih =>
    rw [← List.append_assoc]
    obtain ⟨d, hd⟩ := oghost_concat_vis (b := b) (hint₀ := hint₀) (α ++ γ) ℓ
    rw [hd]; exact ih.trans (List.prefix_append _ _)

/-! ## Counting -/

/-- All but at most `2 N b` entries of `l(σ)` are in `f(σ)`. -/
lemma OInv.allButAtMost {α : List (Lbl S N Q)} {C : OCfg S N Q} {g : OGhost S N Q}
    (hI : OInv b α C g) : AllButAtMost (2 * N * b) g.lin g.vis := by
  refine ⟨(List.finRange N).flatMap g.buf, ?_, fun y hy => ?_⟩
  · have key : ∀ l : List (Fin N), (l.flatMap g.buf).length ≤ l.length * (2 * b) := by
      intro l
      induction l with
      | nil => simp
      | cons j l ih =>
        rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
        have := (hI.thr j).length_le
        have hb : (g.buf j).length = (g.bIn j).length + (g.bAct j).length := by
          simp [OGhost.buf]
        omega
    have := key (List.finRange N)
    simp only [List.length_finRange] at this
    calc _ ≤ N * (2 * b) := this
      _ = 2 * N * b := by rw [Nat.mul_assoc, Nat.mul_left_comm]
  · rcases hI.lin_cover y hy with h | ⟨j, hj⟩
    · exact Or.inl h
    · exact Or.inr (List.mem_flatMap.2 ⟨j, List.mem_finRange j, hj⟩)

/-- Queries enter `f(σ)` alone, at their linearization point. -/
lemma ogstep_vis_query {α : List (Lbl S N Q)} {C : OCfg S N Q} {g : OGhost S N Q}
    (hI : OInv b α C g) (ℓ : Lbl S N Q)
    (x : Entry (Proc N Q) S.toSketch) (hq : ∃ a, x.2.1 = .query a)
    (hx : x ∈ (ogstep α C g ℓ).vis) (hx' : x ∉ g.vis) :
    (ogstep α C g ℓ).vis = g.vis ++ [x] ∧ x ∉ g.lin := by
  obtain ⟨a₀, ha₀⟩ := hq
  rcases ℓ with ⟨p, o⟩ | ⟨p, r⟩ | p
  · rcases p with j | _ | q
    · rcases o with a | _ | _
      · simp only [ogstep] at hx ⊢
        split at hx
        · split at hx
          · exact absurd hx hx'
          · simp only [List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | rfl
            · exact absurd hx hx'
            · cases ha₀
        · exact absurd hx hx'
      all_goals exact absurd hx hx'
    all_goals exact absurd hx hx'
  · exact absurd hx hx'
  · rcases p with j | _ | q
    · simp only [ogstep] at hx; split at hx <;> exact absurd hx hx'
    · simp only [ogstep] at hx ⊢
      split at hx
      · rename_i j k s _
        simp only [List.mem_append] at hx
        rcases hx with hx | hx
        · exact absurd hx hx'
        · obtain ⟨-, a, ha⟩ := hI.buf_shape j x (List.mem_append_left _ hx)
          rw [ha] at ha₀; cases ha₀
      · exact absurd hx hx'
    · simp only [ogstep] at hx ⊢
      split at hx
      · rename_i a hl
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact absurd hx hx'
        · refine ⟨rfl, fun h => ?_⟩
          have hQ := hI.qry q
          rw [hl] at hQ
          exact hQ.2 (List.mem_map_of_mem (f := Prod.fst) h)
      · exact absurd hx hx'

/-! ## Theorem 1 -/

/-- **Theorem 1 (strong form).** `OptParSketch` is strongly linearisable with respect to
`SeqSketch_{2Nb}`; in the witnessing relaxations no query is dropped and queries are preceded
only by operations that precede them in the linearization. -/
theorem theorem1_pastOnly (hb : 0 < b) (h₀ : S.Safe hint₀ []) :
    (optParSketch S N Q b hint₀).HStronglyLinearizable (SeqSketchRPast (2 * N * b) S) := by
  have inv : ∀ α (hα : (optParSketch S N Q b hint₀).Valid α),
      OInv b α hα.choose (oghost b hint₀ α) := fun α hα => oinv_run hb h₀ hα.choose_spec
  refine Impl.hStronglyLinearizable_of_prefix (fun α => (oghost b hint₀ α).lin)
    (fun α β _ h => oghost_lin_prefix h) (fun α hα => (inv α hα).lin_nodup)
    (fun α hα => (inv α hα).lin_op) (fun α hα => (inv α hα).lin_resp)
    (fun α hα => (inv α hα).lin_comp) (fun α hα => ?_)
  -- the visibility order is the witness
  have hval : ∀ k, (optParSketch S N Q b hint₀).Valid (α.take k) := fun k =>
    (optParSketch S N Q b hint₀).valid_of_prefix hα (List.take_prefix k α)
  set L : ℕ → List (Entry (Proc N Q) S.toSketch) := fun k => (oghost b hint₀ (α.take k)).lin
  set V : ℕ → List (Entry (Proc N Q) S.toSketch) := fun k => (oghost b hint₀ (α.take k)).vis
  have hLn : L α.length = (oghost b hint₀ α).lin := by simp [L]
  have hVn : V α.length = (oghost b hint₀ α).vis := by simp [V]
  have htake : ∀ k (hk : k < α.length), α.take (k + 1) = α.take k ++ [α[k]'hk] := fun k hk => by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
  refine ⟨(oghost b hint₀ α).vis, (inv α hα).vis_legal, ?_, fun x hx ⟨a, ha⟩ => ?_, ?_⟩
  · rw [← hLn, ← hVn]
    refine isRelaxation_of_growing L V (by simp [L, OGhost.init]) (fun k hk => ?_)
      (fun k hk => oghost_vis_prefix (List.take_prefix_take_left hk))
      (fun k _ => (inv _ (hval k)).vis_lin) ?_ (fun k _ => (inv _ (hval k)).allButAtMost)
    · simp only [L]; rw [htake k hk]; exact oghost_concat_lin _ _
    · simp only [L, List.take_length]; exact List.Nodup.of_map _ (inv α hα).lin_nodup
  · rcases (inv α hα).lin_cover x hx with h | ⟨j, hj⟩
    · exact h
    · obtain ⟨-, a', ha'⟩ := (inv α hα).buf_shape j x hj
      rw [ha'] at ha; cases ha
  · rw [← hLn, ← hVn]
    refine pastOnly_of_growing IsQueryEntry L V (by simp [V, OGhost.init])
      (fun k hk => oghost_lin_prefix (List.take_prefix_take_left hk))
      (fun k hk => oghost_vis_prefix (List.take_prefix_take_left hk))
      (fun k _ => (inv _ (hval k)).vis_lin) (fun k hk x hq hx hx' => ?_)
      (by simpa [V] using (inv α hα).vis_nodup)
    obtain ⟨C, hC⟩ := hval k
    simp only [V, L, htake k hk, oghost_concat _ _ _ _ hC] at hx hx' ⊢
    exact ogstep_vis_query (oinv_run hb h₀ hC) _ x hq hx hx'

/-- **Theorem 1 of the paper.** `OptParSketch` instantiated with a (derandomised) composable
sketch `S` is strongly linearisable with regards to `SeqSketch_{2Nb}` (for `b ≥ 1` and an
initial hint that is safe for the empty stream, see `differencies.md`). -/
theorem theorem1 (hb : 0 < b) (h₀ : S.Safe hint₀ []) :
    (optParSketch S N Q b hint₀).HStronglyLinearizable (SeqSketchR (2 * N * b) S.toSketch) :=
  (theorem1_pastOnly hb h₀).mono fun _ ⟨H, h1, h2, _, _⟩ => ⟨H, h1, h2⟩

end Podc.ConcurrentSketches
