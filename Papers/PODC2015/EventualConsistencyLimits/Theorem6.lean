import Papers.PODC2015.EventualConsistencyLimits.Late

/-!
# Theorem 6: observable causal consistency (definitions and Lemma 7)

* `AE.OCC` is Definition 18 (observable causal consistency). The returned writes of a read are
  the maximal writes of its context (`rval(r) ⊇ {w₀, w₁}`); we require `w₀ ≠ w₁` (for `w₀ = w₁`
  conditions 1 and 3 contradict each other) and read the index `w_{i-1}` of condition 1 as
  `w_{1-i}` (typo, see the prose before the definition).
* `AE.Revealing` is the definition of Section 5.2.1.
* `lemma7` is Lemma 7 (proved only in the full version): in a causally consistent revealing
  abstract execution `A`, visibility between writes of the operation context of a read `r` is
  preserved in every causally consistent abstract execution `Â` that contains the writes and the
  revealing reads `r_w` with the same responses.
* `Theorem6Statement` is Theorem 6 (stated, not proved; see `README.md`).
-/

namespace Podc.EventualConsistencyLimits

variable {ι Obj V M St : Type*}

namespace AE

variable (A : AE ι Obj V)

/-- Definition 18: observably causally consistent abstract executions. -/
def OCC : Prop :=
  A.CC ∧ ∀ r w₀ w₁, A.dom r → (A.ev r).op = .read →
    w₀ ∈ A.ctxW r → (∀ b ∈ A.ctxW r, ¬ A.vis w₀ b) →
    w₁ ∈ A.ctxW r → (∀ b ∈ A.ctxW r, ¬ A.vis w₁ b) → w₀ ≠ w₁ →
    ∃ w₀' w₁', A.IsWrite w₀' ∧ A.IsWrite w₁' ∧
      -- 1. `w'_i` is visible to `w_{1-i}`, and is a write to another object
      A.vis w₀' w₁ ∧ A.vis w₁' w₀ ∧ (A.ev w₀').obj ≠ (A.ev r).obj ∧
      (A.ev w₁').obj ≠ (A.ev r).obj ∧
      -- 2. to different objects
      (A.ev w₀').obj ≠ (A.ev w₁').obj ∧
      -- 3. `w'_i` is not visible to `w_i`
      ¬ A.vis w₀' w₀ ∧ ¬ A.vis w₁' w₁ ∧
      -- 4. no write to `obj w'_i` concurrent with `w'_i` is visible to `w_i`
      (∀ ŵ, A.IsWrite ŵ → (A.ev ŵ).obj = (A.ev w₀').obj → A.vis ŵ w₀ → A.vis ŵ w₀') ∧
      (∀ ŵ, A.IsWrite ŵ → (A.ev ŵ).obj = (A.ev w₁').obj → A.vis ŵ w₁ → A.vis ŵ w₁')

/-- Section 5.2.1: `A` is revealing if every write `w` is immediately preceded, at its
replica, by a read `rev w` of the same object that is identical to `w` with respect to
visibility. -/
def Revealing (rev : ℕ → ℕ) : Prop :=
  ∀ w, A.dom w → A.IsWrite w →
    A.dom (rev w) ∧ A.rep (rev w) = A.rep w ∧ (A.ev (rev w)).obj = (A.ev w).obj ∧
    (A.ev (rev w)).op = .read ∧ A.ord (rev w) w ∧
    (∀ e, A.dom e → A.rep e = A.rep w → ¬ (A.ord (rev w) e ∧ A.ord e w)) ∧
    (∀ e, e ≠ w → A.vis (rev w) e → A.vis w e) ∧
    (∀ e, e ≠ rev w → A.vis e w → A.vis e (rev w))

/-- Two abstract executions are equivalent if they have the same per-replica sequences of
operations (up to renaming events, as in `AE.On`): here, if there is an order isomorphism
between their domains preserving replicas, operations, responses and per-replica order. -/
def Equiv (A B : AE ι Obj V) : Prop :=
  ∃ f : ℕ → ℕ, (∀ e, A.dom e → B.dom (f e)) ∧ (∀ e', B.dom e' → ∃ e, A.dom e ∧ f e = e') ∧
    (∀ e₁ e₂, A.dom e₁ → A.dom e₂ → f e₁ = f e₂ → e₁ = e₂) ∧
    (∀ e, A.dom e → B.rep (f e) = A.rep e ∧ B.ev (f e) = A.ev e) ∧
    (∀ e₁ e₂, A.dom e₁ → A.dom e₂ → A.rep e₁ = A.rep e₂ → (A.ord e₁ e₂ ↔ B.ord (f e₁) (f e₂)))

end AE

lemma transGen_of_trans {r : ℕ → ℕ → Prop} (h : ∀ a b c, r a b → r b c → r a c) {a b : ℕ}
    (hab : Relation.TransGen r a b) : r a b := by
  induction hab with
  | single h' => exact h'
  | tail _ h' ih => exact h _ _ _ ih h'

/-- The written value of a write. -/
def AE.wval (A : AE ι Obj V) (e : ℕ) (v : V) : Prop := (A.ev e).op = .write v

/-- **Lemma 7 of [AEM15].** Let `A` be a causally consistent revealing MVR abstract execution
and `r` a read of `A`. Let `Â` be a causally consistent MVR abstract execution, with pairwise
distinct written values, that contains the writes `w` of the operation context of `r` and their
revealing reads `r_w` (via `φ`, with the same replicas, operations and responses, and `r_w`
before `w`). Then visibility between writes of the operation context of `r` is preserved. -/
theorem lemma7 {A Â : AE ι Obj V} {rev : ℕ → ℕ} (hA : A.WF) (hAC : A.CC)
    (hrev : A.Revealing rev) (hÂ : Â.WF) (hÂC : Â.CC) {r : ℕ} (φ : ℕ → ℕ)
    (huniq : ∀ a b v, Â.dom a → Â.dom b → Â.wval a v → Â.wval b v → a = b)
    (hφ : ∀ w ∈ A.ctxW r, Â.dom (φ w) ∧ Â.ev (φ w) = A.ev w ∧ Â.dom (φ (rev w)) ∧
      Â.rep (φ (rev w)) = Â.rep (φ w) ∧ Â.ev (φ (rev w)) = A.ev (rev w) ∧
      Â.ord (φ (rev w)) (φ w)) :
    ∀ w' ∈ A.ctxW r, ∀ w ∈ A.ctxW r, A.vis w' w → Â.vis (φ w') (φ w) := by
  intro w' hw' w hw hvis
  induction hn : A.rank w using Nat.strong_induction_on generalizing w w' with
  | _ n ih =>
  subst hn
  obtain ⟨hdw, hEw, hdr, hrr, hEr, hord⟩ := hφ w hw
  have hwdom : A.dom w := (hA.vis_dom hw.1).1
  obtain ⟨hdrev, hreprev, hobjrev, hoprev, hordrev, -, -, hvisrev⟩ := hrev w hwdom hw.2.2
  -- `w'` is visible to `r_w`
  have hw'rev : A.vis w' (rev w) := by
    refine hvisrev w' (fun h => ?_) hvis
    obtain ⟨u, hu⟩ := hw'.2.2
    rw [h, hoprev] at hu
    cases hu
  have hw'ctx : w' ∈ A.ctxW (rev w) := ⟨hw'rev, by rw [hw'.2.1, hobjrev, hw.2.1], hw'.2.2⟩
  -- a maximal write above `w'` in the context of `r_w` is returned by `r_w`
  obtain ⟨c, hc, hrtg, hmax⟩ := hA.exists_max_above hw'ctx
  obtain ⟨u, hu⟩ := hc.2.2
  have hcw : A.vis c w := hA.vis_mono hc.1 hordrev hreprev
  have hcr : c ∈ A.ctxW r :=
    ⟨hAC.2 _ _ _ hcw hw.1, by rw [hc.2.1, hobjrev, hw.2.1], hc.2.2⟩
  -- the response of `r_w`
  obtain ⟨rS, hrS⟩ : ∃ rS, A.ev (rev w) = ⟨(A.ev (rev w)).obj, .read, rS⟩ :=
    ⟨(A.ev (rev w)).rv, by rw [← hoprev]⟩
  have hresp := AE.Correct.read' (hA := hAC.1) hdrev hrS
  have huS : u ∈ {v | ∃ a ∈ A.ctxW (rev w), (A.ev a).op = .write v ∧
      ∀ b ∈ A.ctxW (rev w), ¬ A.vis a b} := ⟨c, hc, hu, hmax⟩
  -- the same response in `Â`
  have hrS' : Â.ev (φ (rev w)) = ⟨(A.ev (rev w)).obj, .read, rS⟩ := by rw [hEr, ← hrS]
  have hresp' := AE.Correct.read' (hA := hÂC.1) hdr hrS'
  rw [hresp] at hresp'
  rw [Resp.vals.inj hresp'] at huS
  obtain ⟨a, ha, hau, -⟩ := huS
  obtain ⟨hdc, hEc, -⟩ := hφ c hcr
  have hac : a = φ c := huniq a (φ c) u (hÂ.vis_dom ha.1).1 hdc hau (by rw [AE.wval, hEc]; exact hu)
  subst hac
  -- `c →vis^ r_w`, hence `c →vis^ w` in `Â`
  have hcw' : Â.vis (φ c) (φ w) := hÂ.vis_mono ha.1 hord hrr
  rcases (Relation.reflTransGen_iff_eq_or_transGen.1 hrtg) with heq | htg
  · subst heq; exact hcw'
  · have hw'c : A.vis w' c := by
      exact transGen_of_trans hAC.2 htg
    have := ih (A.rank c) (hA.rank_lt (hA.vis_ord hcw)) w' hw' c hcr hw'c rfl
    exact hÂC.2 _ _ _ this hcw'

/-! ### Theorem 6 -/

variable [DecidableEq ι]

/-- An execution complies with an abstract execution: it is equivalent to an abstract execution
on the execution's own do-events (Definition 9). -/
def Complies (α : List (ι × Ev Obj V M)) (A : AE ι Obj V) : Prop :=
  ∃ B : AE ι Obj V, B.On (Store.seqL α) ∧ B.WF ∧ AE.Equiv B A

/-- A consistency model: prefix-closed (not needed below) and closed under equivalence. A data
store satisfies it if every finite execution complies with a member (Definition 11; we restrict
to finite executions). -/
def Store.Satisfies {St : Type*} (D : Store ι Obj V M St) (𝒞 : AE ι Obj V → Prop) : Prop :=
  ∀ α, D.IsExec α → ∃ A, 𝒞 A ∧ Complies α A

/-- **Theorem 6 of [AEM15]** (statement only): an eventually consistent data store providing
MVRs, with invisible reads and op-driven messages, does not satisfy a consistency model strictly
stronger than OCC. Formally: if `D` satisfies an equivalence-closed `𝒞 ⊆ OCC` then every finite
OCC abstract execution with pairwise distinct written values (the paper's standing assumption,
Section 4) is in `𝒞`. We do not prove it (see `README.md`). -/
def Theorem6Statement : Prop :=
  ∀ {St : Type} (D : Store ι Obj V M St) (P : AE ι Obj V → Prop) (𝒞 : AE ι Obj V → Prop),
    D.EventuallyConsistent P → D.InvisibleReads → D.OpDriven → D.Available → D.RecvEnabled →
    D.SendClears → D.Satisfies 𝒞 → (∀ A, 𝒞 A → A.OCC) →
    (∀ A B, 𝒞 A → AE.Equiv A B → 𝒞 B) →
    ∀ A : AE ι Obj V, A.WF → A.OCC → {e | A.dom e}.Finite →
      (∀ a b v, A.dom a → A.dom b → A.wval a v → A.wval b v → a = b) → 𝒞 A

end Podc.EventualConsistencyLimits
