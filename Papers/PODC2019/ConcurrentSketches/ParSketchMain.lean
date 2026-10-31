import Papers.PODC2019.ConcurrentSketches.ParSketchStep

/-!
# Lemma 1: `ParSketch` is strongly linearisable with respect to `SeqSketch_{Nb}`

**Lemma 1** (PODC version, Section 5.2; full version Section 6.2). `ParSketch` instantiated with
`SeqSketch` is strongly linearisable with regards to `SeqSketch_{Nb}`.

We prove it (`lemma1`) for every composable sketch, `N ≥ 1` update threads, any number of query
threads, buffer size `b ≥ 1`, and an initial hint `hint₀` (the paper's `1`) that is safe for the
empty stream (`S.Safe hint₀ []`, e.g. `hint₀ = S.calcHint S.init`, `safe_init_hint`). The strong
linearization function is the paper's `l` (updates at their invocation, queries at their
snapshot), and the witness in `SeqSketch` is the paper's `f`. We also prove the stronger
property used by the error analysis of Section 6 (`lemma1_pastOnly`): in the relaxed history `f`,
a query is preceded only by operations that precede it in `l` (it misses at most `Nb` preceding
updates and sees no later ones).
-/

set_option linter.unusedSectionVars false

namespace Podc.ConcurrentSketches

open Cslib.SharedMemory

variable {S : Composable} {N : ℕ} {Q : Type} [NeZero N] [DecidableEq Q] {b : ℕ} {hint₀ : S.Hint}

/-- Every step is covered by one of the step lemmas. -/
theorem inv_step (hb : 0 < b) {α : List (Lbl S N Q)} {C C' : PCfg S N Q} {g : Ghost S N Q}
    {ℓ : Lbl S N Q} (hC : (parSketch S N Q b hint₀).run α = some C) (hI : Inv b α C g)
    (hs : (parSketch S N Q b hint₀).step C ℓ = some C') :
    Inv b (α ++ [ℓ]) C' (gstep α C g ℓ) := by
  cases ℓ with
  | inv p o => exact inv_step_inv hC hI hs
  | ret p r => exact inv_step_ret hI hs
  | tau p =>
    cases p with
    | upd j => exact inv_step_tau_upd hb hI hs
    | prop => exact inv_step_tau_prop hI hs
    | qry q => exact inv_step_tau_qry hC hI hs

/-- The invariant holds along every execution. -/
theorem inv_run (hb : 0 < b) (h₀ : S.Safe hint₀ []) {α : List (Lbl S N Q)} {C : PCfg S N Q}
    (hC : (parSketch S N Q b hint₀).run α = some C) : Inv b α C (ghost b hint₀ α) :=
  Impl.run_induction (Q := fun α C => Inv b α C (ghost b hint₀ α)) (inv_init hb h₀)
    (fun α C ℓ C' hC hI hs => by rw [ghost_concat _ _ _ _ hC]; exact inv_step hb hC hI hs) hC

/-! ## The ghost run only grows -/

lemma gstep_lin (α : List (Lbl S N Q)) (C : PCfg S N Q) (g : Ghost S N Q) (ℓ : Lbl S N Q) :
    ∃ c, (gstep α C g ℓ).lin = g.lin ++ c ∧ c.length ≤ 1 := by
  rcases ℓ with ⟨p, o⟩ | ⟨p, r⟩ | p
  · rcases p with j | _ | q
    · rcases o with a | _ | _
      · simp only [gstep]
        split
        · split <;> exact ⟨_, rfl, by simp⟩
        · exact ⟨[], by simp, by simp⟩
      all_goals exact ⟨[], by simp [gstep], by simp⟩
    all_goals exact ⟨[], by simp [gstep], by simp⟩
  · exact ⟨[], by simp [gstep], by simp⟩
  · rcases p with j | _ | q
    · exact ⟨[], by simp [gstep], by simp⟩
    · simp only [gstep]; split <;> exact ⟨[], by simp, by simp⟩
    · simp only [gstep]; split
      · exact ⟨_, rfl, by simp⟩
      · exact ⟨[], by simp, by simp⟩

lemma gstep_vis (α : List (Lbl S N Q)) (C : PCfg S N Q) (g : Ghost S N Q) (ℓ : Lbl S N Q) :
    ∃ d, (gstep α C g ℓ).vis = g.vis ++ d := by
  rcases ℓ with ⟨p, o⟩ | ⟨p, r⟩ | p
  · rcases p with j | _ | q
    · rcases o with a | _ | _
      · simp only [gstep]
        split
        · split
          · exact ⟨[], by simp⟩
          · exact ⟨_, rfl⟩
        · exact ⟨[], by simp⟩
      all_goals exact ⟨[], by simp [gstep]⟩
    all_goals exact ⟨[], by simp [gstep]⟩
  · exact ⟨[], by simp [gstep]⟩
  · rcases p with j | _ | q
    · exact ⟨[], by simp [gstep]⟩
    · simp only [gstep]; split
      · exact ⟨_, rfl⟩
      · exact ⟨[], by simp⟩
    · simp only [gstep]; split
      · exact ⟨_, rfl⟩
      · exact ⟨[], by simp⟩

lemma ghost_concat_lin (α : List (Lbl S N Q)) (ℓ : Lbl S N Q) :
    ∃ c, (ghost b hint₀ (α ++ [ℓ])).lin = (ghost b hint₀ α).lin ++ c ∧ c.length ≤ 1 := by
  cases hC : (parSketch S N Q b hint₀).run α with
  | none => exact ⟨[], by simp [ghost, ghostRev, hC], by simp⟩
  | some C => rw [ghost_concat _ _ _ _ hC]; exact gstep_lin _ _ _ _

lemma ghost_concat_vis (α : List (Lbl S N Q)) (ℓ : Lbl S N Q) :
    ∃ d, (ghost b hint₀ (α ++ [ℓ])).vis = (ghost b hint₀ α).vis ++ d := by
  cases hC : (parSketch S N Q b hint₀).run α with
  | none => exact ⟨[], by simp [ghost, ghostRev, hC]⟩
  | some C => rw [ghost_concat _ _ _ _ hC]; exact gstep_vis _ _ _ _

lemma ghost_lin_prefix {α β : List (Lbl S N Q)} (h : α <+: β) :
    (ghost b hint₀ α).lin <+: (ghost b hint₀ β).lin := by
  obtain ⟨γ, rfl⟩ := h
  induction γ using List.reverseRecOn with
  | nil => simp
  | append_singleton γ ℓ ih =>
    rw [← List.append_assoc]
    obtain ⟨c, hc, -⟩ := ghost_concat_lin (b := b) (hint₀ := hint₀) (α ++ γ) ℓ
    rw [hc]; exact ih.trans (List.prefix_append _ _)

lemma ghost_vis_prefix {α β : List (Lbl S N Q)} (h : α <+: β) :
    (ghost b hint₀ α).vis <+: (ghost b hint₀ β).vis := by
  obtain ⟨γ, rfl⟩ := h
  induction γ using List.reverseRecOn with
  | nil => simp
  | append_singleton γ ℓ ih =>
    rw [← List.append_assoc]
    obtain ⟨d, hd⟩ := ghost_concat_vis (b := b) (hint₀ := hint₀) (α ++ γ) ℓ
    rw [hd]; exact ih.trans (List.prefix_append _ _)

/-! ## Counting: Lemmas 5–6 of the full paper -/

/-- All but at most `N b` entries of `l(σ)` are in `f(σ)`. -/
lemma Inv.allButAtMost {α : List (Lbl S N Q)} {C : PCfg S N Q} {g : Ghost S N Q}
    (hI : Inv b α C g) : AllButAtMost (N * b) g.lin g.vis := by
  refine ⟨(List.finRange N).flatMap g.buf, ?_, fun y hy => ?_⟩
  · have key : ∀ l : List (Fin N), (l.flatMap g.buf).length ≤ l.length * b := by
      intro l
      induction l with
      | nil => simp
      | cons j l ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
        have := (hI.thr j).length_le
        omega
    simpa using key (List.finRange N)
  · rcases hI.lin_cover y hy with h | ⟨j, hj⟩
    · exact Or.inl h
    · exact Or.inr (List.mem_flatMap.2 ⟨j, List.mem_finRange j, hj⟩)

/-- Queries enter `f(σ)` alone, at their linearization point. -/
lemma gstep_vis_query {α : List (Lbl S N Q)} {C : PCfg S N Q} {g : Ghost S N Q}
    (hI : Inv b α C g) (ℓ : Lbl S N Q) (x : Entry (Proc N Q) S.toSketch)
    (hq : ∃ a, x.2.1 = .query a)
    (hx : x ∈ (gstep α C g ℓ).vis) (hx' : x ∉ g.vis) :
    (gstep α C g ℓ).vis = g.vis ++ [x] ∧ x ∉ g.lin := by
  obtain ⟨a₀, ha₀⟩ := hq
  rcases ℓ with ⟨p, o⟩ | ⟨p, r⟩ | p
  · rcases p with j | _ | q
    · rcases o with a | _ | _
      · simp only [gstep] at hx ⊢
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
    · exact absurd hx hx'
    · simp only [gstep] at hx ⊢
      split at hx
      · rename_i j s _
        simp only [List.mem_append] at hx
        rcases hx with hx | hx
        · exact absurd hx hx'
        · obtain ⟨-, a, ha⟩ := hI.buf_shape j x hx
          rw [ha] at ha₀; cases ha₀
      · exact absurd hx hx'
    · simp only [gstep] at hx ⊢
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

/-! ## Lemma 1 -/

/-- Query entries. -/
def IsQueryEntry (x : Entry (Proc N Q) S.toSketch) : Prop := ∃ a, x.2.1 = .query a

/-- `SeqSketch_r` with the extra properties used by the error analysis of Section 6: no query is
dropped by the relaxation, and queries see only the past. -/
def SeqSketchRPast (r : ℕ) (S : Composable) (H' : List (Entry (Proc N Q) S.toSketch)) : Prop :=
  ∃ H, SeqSketch S.toSketch H ∧ IsRelaxation r H H' ∧ (∀ x ∈ H', IsQueryEntry x → x ∈ H) ∧
    PastOnly IsQueryEntry H H'

/-- **Lemma 1 (strong form).** `ParSketch` is strongly linearisable with respect to
`SeqSketch_{Nb}`, and in the witnessing relaxations queries are preceded only by operations
that precede them in the linearization; no query is dropped. -/
theorem lemma1_pastOnly (hb : 0 < b) (h₀ : S.Safe hint₀ []) :
    (parSketch S N Q b hint₀).HStronglyLinearizable (SeqSketchRPast (N * b) S) := by
  have inv : ∀ α (hα : (parSketch S N Q b hint₀).Valid α),
      Inv b α hα.choose (ghost b hint₀ α) := fun α hα => inv_run hb h₀ hα.choose_spec
  refine Impl.hStronglyLinearizable_of_prefix (fun α => (ghost b hint₀ α).lin)
    (fun α β _ h => ghost_lin_prefix h) (fun α hα => (inv α hα).lin_nodup)
    (fun α hα => (inv α hα).lin_op) (fun α hα => (inv α hα).lin_resp)
    (fun α hα => (inv α hα).lin_comp) (fun α hα => ?_)
  -- the visibility order is the witness
  have hval : ∀ k, (parSketch S N Q b hint₀).Valid (α.take k) := fun k =>
    (parSketch S N Q b hint₀).valid_of_prefix hα (List.take_prefix k α)
  set L : ℕ → List (Entry (Proc N Q) S.toSketch) := fun k => (ghost b hint₀ (α.take k)).lin
  set V : ℕ → List (Entry (Proc N Q) S.toSketch) := fun k => (ghost b hint₀ (α.take k)).vis
  have hLn : L α.length = (ghost b hint₀ α).lin := by simp [L]
  have hVn : V α.length = (ghost b hint₀ α).vis := by simp [V]
  have htake : ∀ k (hk : k < α.length), α.take (k + 1) = α.take k ++ [α[k]'hk] := fun k hk => by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
  refine ⟨(ghost b hint₀ α).vis, (inv α hα).vis_legal, ?_, fun x hx ⟨a, ha⟩ => ?_, ?_⟩
  · rw [← hLn, ← hVn]
    refine isRelaxation_of_growing L V (by simp [L, Ghost.init]) (fun k hk => ?_)
      (fun k hk => ghost_vis_prefix (List.take_prefix_take_left hk))
      (fun k _ => (inv _ (hval k)).vis_lin) ?_ (fun k _ => (inv _ (hval k)).allButAtMost)
    · simp only [L]; rw [htake k hk]; exact ghost_concat_lin _ _
    · simp only [L, List.take_length]; exact List.Nodup.of_map _ (inv α hα).lin_nodup
  · rcases (inv α hα).lin_cover x hx with h | ⟨j, hj⟩
    · exact h
    · obtain ⟨-, a', ha'⟩ := (inv α hα).buf_shape j x hj
      rw [ha'] at ha; cases ha
  · rw [← hLn, ← hVn]
    refine pastOnly_of_growing IsQueryEntry L V (by simp [V, Ghost.init])
      (fun k hk => ghost_lin_prefix (List.take_prefix_take_left hk))
      (fun k hk => ghost_vis_prefix (List.take_prefix_take_left hk))
      (fun k _ => (inv _ (hval k)).vis_lin) (fun k hk x hq hx hx' => ?_)
      (by simpa [V] using (inv α hα).vis_nodup)
    obtain ⟨C, hC⟩ := hval k
    simp only [V, L, htake k hk, ghost_concat _ _ _ _ hC] at hx hx' ⊢
    exact gstep_vis_query (inv_run hb h₀ hC) _ x hq hx hx'

/-- **Lemma 1 of the paper.** `ParSketch` instantiated with a (derandomised) composable sketch
`S` is strongly linearisable with regards to `SeqSketch_{Nb}` (for `b ≥ 1` and an initial hint
that is safe for the empty stream, see `differencies.md`). -/
theorem lemma1 (hb : 0 < b) (h₀ : S.Safe hint₀ []) :
    (parSketch S N Q b hint₀).HStronglyLinearizable (SeqSketchR (N * b) S.toSketch) :=
  (lemma1_pastOnly hb h₀).mono fun _ ⟨H, h1, h2, _, _⟩ => ⟨H, h1, h2⟩

/-- The hint of the empty sketch is a safe initial hint (for the Θ sketch it is the paper's
`1`). -/
lemma safe_init_hint (S : Composable) : S.Safe (S.calcHint S.init) [] :=
  Composable.safe_calcHint (S := S) []

end Podc.ConcurrentSketches
