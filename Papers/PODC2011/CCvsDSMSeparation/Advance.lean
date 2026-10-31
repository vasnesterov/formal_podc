import Papers.PODC2011.CCvsDSMSeparation.Regular

/-!
# Letting processes perform their next RMRs

In each round of the construction of Lemma 6.10, each selected unstable process runs solo until it
is about to perform an RMR and then performs it. The local prefixes and next RMRs are computed once,
relative to a history `τ` (`NextData`), and are then replayed one process after the other on top of
another history `ρ` in which these processes have the same local histories and the same values in
their own memory modules (`advance`). If no selected process accesses the module of another
selected process, the replay is an execution (`advance_valid`) and each selected process performs
one more RMR (`rmrOf_advance`). `advance_regular` gives the regularity conditions of the result.
-/

namespace Podc.CCvsDSMSeparation

variable {N : ℕ} {V Val S : Type*}

namespace Algorithm

variable (A : Algorithm N V Val S)

/-- For every `p ∈ T`, `α p ++ [e p]` is the solo run of `p` after `τ` up to and including its next
RMR `e p`. -/
structure NextData (τ : List (Ev N V Val)) (T : Finset (Fin N))
    (α : Fin N → List (Ev N V Val)) (e : Fin N → Ev N V Val) : Prop where
  solo : ∀ p ∈ T, SoloPoll p (α p ++ [e p])
  valid : ∀ p ∈ T, A.Valid (τ ++ α p ++ [e p])
  loc : ∀ p ∈ T, A.rmr (α p) = 0
  remote : ∀ p ∈ T, (e p).remote A.home = true

namespace NextData

variable {A} {τ : List (Ev N V Val)} {T : Finset (Fin N)} {α : Fin N → List (Ev N V Val)}
  {e : Fin N → Ev N V Val}

lemma e_p (h : A.NextData τ T α e) {p : Fin N} (hp : p ∈ T) : (e p).p = p :=
  (h.solo p hp (e p) (by simp)).1

lemma α_p (h : A.NextData τ T α e) {p : Fin N} (hp : p ∈ T) : ∀ e' ∈ α p, e'.p = p :=
  fun e' he' => (h.solo p hp e' (by simp [he'])).1

lemma α_local (h : A.NextData τ T α e) {p : Fin N} (hp : p ∈ T) :
    ∀ e' ∈ α p, ∀ v, e'.op.var = some v → A.home v = p := by
  intro e' he' v hv
  rw [← h.α_p hp e' he']
  exact A.home_eq_of_not_remote ((A.rmr_eq_zero_iff).1 (h.loc p hp) e' he') hv

lemma var_e (h : A.NextData τ T α e) {p : Fin N} (hp : p ∈ T) :
    ∃ v, (e p).op.var = some v ∧ A.home v ≠ p := by
  have hr := h.remote p hp
  rcases hv : (e p).op.var with _ | v
  · simp [Ev.remote, Op.remoteFor, hv] at hr
  · exact ⟨v, rfl, by rw [← h.e_p hp]; exact A.home_ne_of_remote hr hv⟩

lemma α_not_writes (h : A.NextData τ T α e) {p : Fin N} (hp : p ∈ T) {v : V}
    (hv : A.home v ≠ p) : ∀ e' ∈ α p, ¬ e'.Writes v := by
  intro e' he' hw
  exact hv (h.α_local hp e' he' v hw.var)

end NextData

/-- Replay, for `p ∈ L` in order, the local prefix `α p` and then the next RMR `e p` (with the
value of a read re-evaluated in the current memory). -/
noncomputable def advance (α : Fin N → List (Ev N V Val)) (e : Fin N → Ev N V Val) :
    List (Ev N V Val) → List (Fin N) → List (Ev N V Val)
  | ρ, [] => ρ
  | ρ, p :: L => advance α e (ρ ++ α p ++ [⟨p, (e p).op.reval (A.memVal (ρ ++ α p))⟩]) L

/-- The step `p` performs in place of its next RMR. -/
noncomputable def stepAt (e : Fin N → Ev N V Val) (ρ : List (Ev N V Val)) (p : Fin N) :
    Ev N V Val := ⟨p, (e p).op.reval (A.memVal ρ)⟩

lemma advance_cons (α : Fin N → List (Ev N V Val)) (e : Fin N → Ev N V Val)
    (ρ : List (Ev N V Val)) (p : Fin N) (L : List (Fin N)) :
    A.advance α e ρ (p :: L) = A.advance α e (ρ ++ α p ++ [A.stepAt e (ρ ++ α p) p]) L := rfl

section

variable {A} {τ : List (Ev N V Val)} {T : Finset (Fin N)} {α : Fin N → List (Ev N V Val)}
  {e : Fin N → Ev N V Val}

/-- The target of the next RMR of `p`, as a function. -/
noncomputable def tgt (e : Fin N → Ev N V Val) (p : Fin N) : Option V := (e p).op.var

lemma stepAt_var (ρ : List (Ev N V Val)) (p : Fin N) :
    (A.stepAt e ρ p).op.var = (e p).op.var := by simp [stepAt]

lemma stepAt_writes_iff (ρ : List (Ev N V Val)) (p : Fin N) (v : V) :
    (A.stepAt e ρ p).Writes v ↔ (e p).Writes v := by
  unfold stepAt
  have := Ev.writes_reval_iff (A.memVal ρ) p (e p).op v
  rw [this]; simp [Ev.Writes]

/-- The step re-evaluated at `ρ` is legal after `ρ ++ ...` if the process has the same local
history. -/
lemma NextData.stepOK (h : A.NextData τ T α e) {p : Fin N} (hp : p ∈ T) {ρ : List (Ev N V Val)}
    (hpj : proj ρ p = proj τ p) :
    A.StepOK (ρ ++ α p) (A.stepAt e (ρ ++ α p) p) := by
  have hv := h.valid p hp
  have hs : A.StepOK (τ ++ α p) (e p) := ((A.valid_snoc _ _).1 hv).2
  have := A.stepOK_reval (τ' := ρ ++ α p) hs (by rw [h.e_p hp, proj_append, proj_append, hpj])
  rw [h.e_p hp] at this
  exact this

/-- The basic facts about one replayed process. -/
lemma NextData.step (h : A.NextData τ T α e) {p : Fin N} (hp : p ∈ T)
    {ρ : List (Ev N V Val)} (hρ : A.Valid ρ) (hpj : proj ρ p = proj τ p)
    (hmem : ∀ v, A.home v = p → A.memVal ρ v = A.memVal τ v) :
    A.Valid (ρ ++ α p ++ [A.stepAt e (ρ ++ α p) p]) := by
  have hα : A.Valid (ρ ++ α p) := by
    refine A.valid_transport (τ := τ) (Valid.of_prefix A (h.valid p hp) ⟨[e p], by simp⟩) hρ ?_ ?_
    · intro e' he'; rw [h.α_p hp e' he', hpj]
    · intro e' he' v hv; exact hmem v (h.α_local hp e' he' v hv)
  exact (A.valid_snoc _ _).2 ⟨hα, h.stepOK hp hpj⟩

/-- Shape of the replayed segment. -/
def SegShape (e : Fin N → Ev N V Val) (L : List (Fin N)) (σ : List (Ev N V Val)) : Prop :=
  ∀ e' ∈ σ, e'.p ∈ L ∧ e'.op.isSigInv = false ∧
    ((∀ v, e'.op.var = some v → A.home v = e'.p) ∨ ∃ m, e'.op = (e e'.p).op.reval m)

lemma advance_spec (h : A.NextData τ T α e)
    (hind : ∀ p ∈ T, ∀ v, (e p).op.var = some v → A.home v ∉ T) :
    ∀ (L : List (Fin N)) (ρ : List (Ev N V Val)), L.Nodup → (∀ p ∈ L, p ∈ T) → A.Valid ρ →
      (∀ q ∈ L, proj ρ q = proj τ q) →
      (∀ q ∈ L, ∀ v, A.home v = q → A.memVal ρ v = A.memVal τ v) →
      A.Valid (A.advance α e ρ L) ∧
      (∃ σ, A.advance α e ρ L = ρ ++ σ ∧ SegShape (A := A) e L σ) ∧
      (∀ q ∈ L, A.rmrOf (A.advance α e ρ L) q = A.rmrOf ρ q + 1)
  | [], ρ, _, _, hρ, _, _ => ⟨hρ, ⟨[], by simp [advance], by simp [SegShape]⟩, by simp⟩
  | p :: L, ρ, hnd, hLT, hρ, hpj, hmem => by
    have hp : p ∈ T := hLT p (by simp)
    have hpL : p ∉ L := (List.nodup_cons.1 hnd).1
    set ρ₂ := ρ ++ α p ++ [A.stepAt e (ρ ++ α p) p] with hρ₂
    have hv₂ : A.Valid ρ₂ := h.step hp hρ (hpj p (by simp)) (hmem p (by simp))
    obtain ⟨v₀, hv₀, hhome⟩ := h.var_e hp
    have hevents : ∀ e' ∈ α p ++ [A.stepAt e (ρ ++ α p) p], e'.p = p := by
      intro e' he'
      rcases List.mem_append.1 he' with he' | he'
      · exact h.α_p hp e' he'
      · simp at he'; subst he'; rfl
    obtain ⟨ih1, ⟨σ, hσ, hshape⟩, ih3⟩ := advance_spec h hind L ρ₂ (List.nodup_cons.1 hnd).2
      (fun q hq => hLT q (by simp [hq])) hv₂
      (by
        intro q hq
        have hqp : q ≠ p := fun h' => hpL (h' ▸ hq)
        rw [hρ₂, List.append_assoc, proj_append_of_forall _ _ _ (fun e' he' => by
          rw [hevents e' he']; exact Ne.symm hqp)]
        exact hpj q (by simp [hq]))
      (by
        intro q hq v hv
        have hqp : q ≠ p := fun h' => hpL (h' ▸ hq)
        rw [hρ₂, List.append_assoc, A.memVal_append_of_not_writes]
        · exact hmem q (by simp [hq]) v hv
        · intro e' he' hw
          rcases List.mem_append.1 he' with he' | he'
          · exact hqp (hv ▸ h.α_local hp e' he' v hw.var)
          · simp at he'; subst he'
            rw [stepAt_writes_iff] at hw
            exact hind p hp v hw.var (hv ▸ hLT q (by simp [hq])))
    refine ⟨ih1, ⟨α p ++ [A.stepAt e (ρ ++ α p) p] ++ σ, ?_, ?_⟩, ?_⟩
    · rw [advance_cons, hσ, hρ₂]; simp
    · intro e' he'
      rcases List.mem_append.1 he' with he' | he'
      · have hep := hevents e' he'
        refine ⟨by simp [hep], ?_, ?_⟩
        · rcases List.mem_append.1 he' with he' | he'
          · exact (h.solo p hp e' (by simp [he'])).2
          · simp at he'; subst he'
            simp [stepAt, (h.solo p hp (e p) (by simp)).2]
        · rcases List.mem_append.1 he' with he' | he'
          · left; intro v hv; rw [hep]; exact h.α_local hp e' he' v hv
          · simp at he'; subst he'; right; exact ⟨_, rfl⟩
      · obtain ⟨h1, h2, h3⟩ := hshape e' he'
        exact ⟨by simp [h1], h2, h3⟩
    · intro q hq
      rw [advance_cons]
      rcases List.mem_cons.1 hq with hqp | hq
      · rw [hqp, hσ, A.rmrOf_append]
        have : A.rmrOf σ p = 0 := A.rmrOf_eq_zero_of_forall (fun e' he' heq =>
          hpL (heq ▸ (hshape e' he').1))
        rw [this, hρ₂, A.rmrOf_append, A.rmrOf_append, A.rmrOf_eq_rmr_of_forall (h.α_p hp),
          h.loc p hp, A.rmrOf_eq_rmr_of_forall (σ := [_]) (by simp [stepAt]), A.rmr_singleton]
        have : (A.stepAt e (ρ ++ α p) p).remote A.home = true := by
          have h1 := h.remote p hp; have h2 := h.e_p hp
          unfold stepAt; rw [Ev.remote_reval]
          rcases hh : e p with ⟨p', op'⟩
          rw [hh] at h1 h2; simp only at h2 ⊢; subst h2; exact h1
        simp [this]
      · rw [ih3 q hq, hρ₂, List.append_assoc, A.rmrOf_append,
          A.rmrOf_eq_zero_of_forall (p := q) (σ := α p ++ [_])
          (fun e' he' heq => by rw [hevents e' he'] at heq; exact hpL (heq ▸ hq)), Nat.add_zero]

/-- Appending local steps of an active process preserves the regularity conditions. -/
lemma append_local {B : Finset (Fin N)} {p : Fin N} (hp : p ∈ B) :
    ∀ (σ ρ : List (Ev N V Val)), (∀ e' ∈ σ, e'.p = p ∧ ∀ v, e'.op.var = some v → A.home v = p) →
      NoSee B ρ → A.NoTouch B ρ →
      NoSee B (ρ ++ σ) ∧ A.NoTouch B (ρ ++ σ) ∧ ∀ u, SoleW B ρ u → SoleW B (ρ ++ σ) u
  | [], ρ, _, h1, h2 => ⟨by simpa using h1, by simpa using h2, fun u hu => by simpa using hu⟩
  | e' :: σ, ρ, hσ, h1, h2 => by
    obtain ⟨hep, hloc⟩ := hσ e' (by simp)
    have hT : A.NoTouch B (ρ ++ [e']) := by
      refine NoTouch.append A h2 ?_
      intro e'' he'' v hv; simp at he''; subst he''; rw [hloc v hv, hep]; exact okW_self _ _
    have hS : NoSee B (ρ ++ [e']) := by
      refine h1.snoc fun v x hx => ?_
      rw [hep]; exact A.okW_writer_of_home h2 hp (hloc v (by simp [hx, Op.var]))
    obtain ⟨r1, r2, r3⟩ := append_local hp σ (ρ ++ [e']) (fun e'' he'' => hσ e'' (by simp [he'']))
      hS hT
    refine ⟨by simpa using r1, by simpa using r2, fun u hu => ?_⟩
    have : SoleW B (ρ ++ [e']) u := by
      by_cases hw : e'.Writes u
      · exact hu.snoc_write fun _ => by
          rw [hep]; exact A.okW_writer_of_home h2 hp (hloc u hw.var)
      · exact hu.snoc_not_writes hw
    simpa using r3 u this

/-- Regularity of the replayed history, relative to the set `T` of replayed processes. -/
lemma advance_regular (h : A.NextData τ T α e)
    (hind : ∀ p ∈ T, ∀ v, (e p).op.var = some v → A.home v ∉ T) :
    ∀ (L : List (Fin N)) (ρ : List (Ev N V Val)), L.Nodup → (∀ p ∈ L, p ∈ T) →
      NoSee T ρ → A.NoTouch T ρ →
      (∀ p ∈ L, ∀ v x, (e p).op = .read v x → OkW T p (writer v ρ)) →
      (∀ p ∈ L, ∀ q ∈ L, ∀ v x, (e p).op = .read v x → ¬ (e q).Writes v) →
      NoSee T (A.advance α e ρ L) ∧ A.NoTouch T (A.advance α e ρ L) ∧
      (∀ v, (∀ p ∈ L, ¬ (e p).Writes v) → SoleW T ρ v → SoleW T (A.advance α e ρ L) v) ∧
      (∀ v p, p ∈ L → (e p).Writes v → (∀ q ∈ L, q ≠ p → ¬ (e q).Writes v) →
         OkW T p (writer v ρ) → SoleW T ρ v → SoleW T (A.advance α e ρ L) v)
  | [], ρ, _, _, h1, h2, _, _ =>
    ⟨h1, h2, fun _ _ h => h, fun _ _ hp => by simp at hp⟩
  | p :: L, ρ, hnd, hLT, h1, h2, hR, hRW => by
    have hp : p ∈ T := hLT p (by simp)
    have hpL : p ∉ L := (List.nodup_cons.1 hnd).1
    obtain ⟨v₀, hv₀, hhome⟩ := h.var_e hp
    -- the local prefix
    obtain ⟨l1, l2, l3⟩ := A.append_local hp (α p) ρ
      (fun e' he' => ⟨h.α_p hp e' he', h.α_local hp e' he'⟩) h1 h2
    set ρ₁ := ρ ++ α p with hρ₁
    set st := A.stepAt e ρ₁ p with hst
    have hwρ₁ : ∀ v, A.home v ≠ p → writer v ρ₁ = writer v ρ := fun v hv =>
      writer_append_of_not_writes v ρ (α p) (h.α_not_writes hp hv)
    have hvar : ∀ v, st.op.var = some v → v = v₀ := by
      intro v hv; rw [hst, stepAt_var, hv₀] at hv; cases hv; rfl
    have hT₂ : A.NoTouch T (ρ₁ ++ [st]) := by
      refine NoTouch.append A l2 ?_
      intro e' he' v hv; simp at he'; subst he'
      exact okW_of_not_mem (hind p hp v (by rw [← stepAt_var ρ₁ p]; exact hv))
    have hS₂ : NoSee T (ρ₁ ++ [st]) := by
      refine l1.snoc fun v x hx => ?_
      have hx' : ∃ y, (e p).op = .read v y := by
        rcases hep : (e p).op with o | ⟨u, y⟩ | ⟨u, y⟩ | b <;>
          simp [hst, stepAt, hep, Op.reval] at hx
        exact ⟨y, by rw [hx.1]⟩
      obtain ⟨y, hy⟩ := hx'
      have : st.p = p := rfl
      rw [this, hwρ₁ v (by have := hvar v (by simp [hx, Op.var]); subst this; exact hhome)]
      exact hR p (by simp) v y hy
    have hSt : ∀ v, SoleW T ρ v → ¬ (e p).Writes v → SoleW T (ρ₁ ++ [st]) v := by
      intro v hv hw
      exact (l3 v hv).snoc_not_writes (by rw [hst, stepAt_writes_iff]; exact hw)
    -- the induction hypothesis
    have hwρ₂ : ∀ v, A.home v ≠ p → ¬ (e p).Writes v → writer v (ρ₁ ++ [st]) = writer v ρ := by
      intro v hv hw
      have hw' : ¬ st.Writes v := by rw [hst, stepAt_writes_iff]; exact hw
      rw [writer_snoc]; simp only [hw', ↓reduceIte]; rw [hwρ₁ v hv]
    obtain ⟨i1, i2, i3, i4⟩ := advance_regular h hind L (ρ₁ ++ [st]) (List.nodup_cons.1 hnd).2
      (fun q hq => hLT q (by simp [hq])) hS₂ hT₂
      (by
        intro q hq v x hx
        obtain ⟨u, hu, -⟩ := h.var_e (hLT q (by simp [hq]))
        have hvT : A.home v ∉ T := hind q (hLT q (by simp [hq])) v (by simp [hx, Op.var])
        rw [hwρ₂ v (fun h' => hvT (h' ▸ hp)) (hRW q (by simp [hq]) p (by simp) v x hx)]
        exact hR q (by simp [hq]) v x hx)
      (fun q hq q' hq' => hRW q (by simp [hq]) q' (by simp [hq']))
    refine ⟨i1, i2, ?_, ?_⟩
    · intro v hno hv
      rw [advance_cons]
      exact i3 v (fun q hq => hno q (by simp [hq])) (hSt v hv (hno p (by simp)))
    · intro v p₀ hp₀ hw huniq hok hv
      rw [advance_cons]
      rcases List.mem_cons.1 hp₀ with rfl | hp₀L
      · -- `p` itself is the unique writer of `v`
        refine i3 v (fun q hq => huniq q (by simp [hq]) (fun h' => hpL (h' ▸ hq))) ?_
        have hvv : v = v₀ := by have := hw.var; rw [hv₀] at this; cases this; rfl
        refine (l3 v hv).snoc_write fun _ => ?_
        rw [hwρ₁ v (hvv ▸ hhome)]; exact hok
      · have hp₀p : p₀ ≠ p := fun h' => hpL (h' ▸ hp₀L)
        have hnw : ¬ (e p).Writes v := huniq p (by simp) (Ne.symm hp₀p)
        refine i4 v p₀ hp₀L hw (fun q hq hqp => huniq q (by simp [hq]) hqp) ?_ (hSt v hv hnw)
        have hvT : A.home v ∉ T := hind p₀ (hLT p₀ hp₀) v hw.var
        rw [hwρ₂ v (fun h' => hvT (h' ▸ hp)) hnw]; exact hok

end

end Algorithm

end Podc.CCvsDSMSeparation
