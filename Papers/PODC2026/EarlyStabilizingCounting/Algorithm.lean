import Papers.PODC2026.EarlyStabilizingCounting.Template
import Papers.PODC2026.EarlyStabilizingCounting.KingConsensus
import Papers.PODC2026.EarlyStabilizingCounting.Filtering

/-!
# Algorithm 1 as a synchronous counting algorithm (Theorem 5.7)

The recursion template (Algorithm 1 of [LL26]) instantiated with the filtering Algorithm 8 and
the 3-round King Consensus Algorithm 10, as an algorithm in CSLib's self-stabilising Byzantine
state-broadcast model (`Cslib.Byzantine.SyncCounting`): complete network, lock-step rounds,
arbitrary initial states, Byzantine nodes that may send different states to different nodes.
Every message of the paper's algorithm is a function of the sender's state at the end of the
previous round (Section 4 convention), so broadcasting the whole state is no restriction.

* The node set `Fin n` is split into `V₀ = {v < n/2}` and `V₁ = {v ≥ n/2}` (balanced partition).
  `A₀`, `A₁` are counting algorithms on `V₀`, `V₁` modulo `k₀ n = 12 n` and `k₁ n = 15 n`.
* State of a node: `LS n` (output clock `cv`, the two filter states, the stage-2 and stage-3
  states of the two pipelined King Consensus instances) together with the states of both
  sub-algorithms (a node only uses the one of its own part).
* Per round, for `b ∈ {0, 1}`: a new King Consensus instance is started with input
  `(C_v + δ mod C, ℓ_v^b)`, where `ℓ_v^b` is read off the filter output `F_v^b` (line 2); the
  pipelined instances advance one stage; the instance started two rounds earlier outputs, and a
  non-`⊥` output replaces `C_v` (the `b = 1` instance last); then `C_v` is incremented (line 15).
  The filters (Algorithm 8 with `X = 48`) and sub-counters run as in lines 10–14.
* `δ` is the input offset of line 3. The paper writes `C_v + R` (`R = 3`); the correct value under
  the paper's own timing conventions is `R - 1 = 2` (`tmpl 2`). `Literal.lean` shows that `δ = 3`
  never counts.

Main result: `theorem_5_7`.
-/

set_option linter.unusedSectionVars false

namespace EarlyStabilizingCounting

open Finset Cslib.Byzantine.SyncCounting

/-- Number of rounds of the King Consensus subroutine (Algorithm 10). -/
def Dk : ℕ := 3

/-- The filtering parameter `X` (cooldown). -/
def Xf : ℕ := 48

/-- An early-stabilizing counter: every execution with `f` faulty nodes, `3 f < n`, stabilizes
within `T f` rounds. -/
def IsESCounter {n : ℕ} {X : Type*} {c : ℕ} (A : Algorithm (Fin n) X c) (T : ℕ → ℕ) : Prop :=
  ∀ F : Finset (Fin n), 3 * F.card < n → ∀ x, IsExec A F x → StabilisesIn A F x (T F.card)

/-- State of one level of the recursion. -/
structure LS (n : ℕ) where
  /-- the output clock `C_v` -/
  cv : ℕ
  /-- the two filter states -/
  filt : Bool → FS
  /-- stage-2 states of the two King Consensus pipelines -/
  k2 : Bool → KC2 n
  /-- stage-3 states of the two King Consensus pipelines -/
  k3 : Bool → KC3 n

instance (n : ℕ) : Nonempty (LS n) :=
  ⟨⟨0, fun _ => ⟨none, none, 0⟩, fun _ => ⟨0, none, false⟩, fun _ => ⟨0, false, none⟩⟩⟩

section Partition

variable {n : ℕ}

/-- The part of a node: `false` for `V₀ = {v < n/2}`, `true` for `V₁`. -/
def side (v : Fin n) : Bool := decide (n / 2 ≤ v.val)

/-- The clock set `V_b`. -/
def Tset (n : ℕ) (b : Bool) : Finset (Fin n) := univ.filter fun v => side v = b

/-- Embedding of `V₀`. -/
def e₀ (j : Fin (n / 2)) : Fin n := ⟨j, by omega⟩

/-- Embedding of `V₁`. -/
def e₁ (j : Fin (n - n / 2)) : Fin n := ⟨n / 2 + j, by omega⟩

/-- Index of a node of `V₀`. -/
def i₀ (v : Fin n) (h : v.val < n / 2) : Fin (n / 2) := ⟨v, h⟩

/-- Index of a node of `V₁`. -/
def i₁ (v : Fin n) (h : n / 2 ≤ v.val) : Fin (n - n / 2) := ⟨v - n / 2, by omega⟩

end Partition

variable {n C δ : ℕ} {X₀ X₁ : Type}

/-- The clock value of node `w` (state `s`) for the clock set `V_b`. -/
def subOut (A₀ : Algorithm (Fin (n / 2)) X₀ (kk Dk false * n))
    (A₁ : Algorithm (Fin (n - n / 2)) X₁ (kk Dk true * n)) (b : Bool) (w : Fin n)
    (s : LS n × X₀ × X₁) : ℕ :=
  if b then (if h : n / 2 ≤ w.val then (A₁.h (i₁ w h) s.2.2 : ℕ) else 0)
  else (if h : w.val < n / 2 then (A₀.h (i₀ w h) s.2.1 : ℕ) else 0)

/-- The leader input of node `w` (state `s`) for instance `b` (Algorithm 1, line 2). -/
def ldOf (n : ℕ) (b : Bool) (s : LS n) : Option (Fin n) :=
  leader (kk Dk b) n (filtOut (kk Dk b * n) (s.filt b))

/-- Algorithm 1 (recursion template) with input offset `δ`, Algorithm 8 filtering (`X = 48`) and
Algorithm 10 King Consensus (`R = 3`). -/
def tmpl (δ C : ℕ) [NeZero C] (A₀ : Algorithm (Fin (n / 2)) X₀ (kk Dk false * n))
    (A₁ : Algorithm (Fin (n - n / 2)) X₁ (kk Dk true * n)) :
    Algorithm (Fin n) (LS n × X₀ × X₁) C where
  g v m :=
    let own := m v
    let inp : Fin n → ℕ := fun w => ((m w).1.cv + δ) % C
    let out : Bool → Option ℕ := fun b => kcOut (own.1.k3 b) (fun w => (m w).1.k3 b)
    (⟨((((out true).orElse fun _ => out false).getD own.1.cv) + 1) % C,
      fun b => filtStep n (kk Dk b * n) Xf (Tset n b) (own.1.filt b)
        (fun w => subOut A₀ A₁ b w (m w)) (fun w => ((m w).1.filt b).m),
      fun b => kc2 n (inp v) (ldOf n b own.1) inp,
      fun b => kc3 (own.1.k2 b) (fun w => (m w).1.k2 b)⟩,
     if h : v.val < n / 2 then A₀.g (i₀ v h) (fun j => (m (e₀ j)).2.1) else own.2.1,
     if h : n / 2 ≤ v.val then A₁.g (i₁ v h) (fun j => (m (e₁ j)).2.2) else own.2.2)
  h _ s := ⟨s.1.cv % C, Nat.mod_lt _ (NeZero.pos C)⟩

/-! ### Received vectors of an execution -/

section Exec

variable [NeZero C] {A₀ : Algorithm (Fin (n / 2)) X₀ (kk Dk false * n)}
  {A₁ : Algorithm (Fin (n - n / 2)) X₁ (kk Dk true * n)} {F : Finset (Fin n)}
  {x : ℕ → Fin n → LS n × X₀ × X₁}

/-- The vector received by node `v` in round `t + 1` (for correct `v`). -/
noncomputable def rcv (hx : IsExec (tmpl δ C A₀ A₁) F x) (t : ℕ) (v : Fin n) :
    Fin n → LS n × X₀ × X₁ :=
  if h : v ∉ F then (hx t v h).choose else x t

theorem rcv_agree (hx : IsExec (tmpl δ C A₀ A₁) F x) {t : ℕ} {v : Fin n} (hv : v ∉ F) :
    ∀ w, w ∉ F → rcv hx t v w = x t w := by
  intro w hw
  unfold rcv; rw [dite_eq_left_of_eq_true (eq_true hv)]; exact (hx t v hv).choose_spec.1 w hw

theorem rcv_step (hx : IsExec (tmpl δ C A₀ A₁) F x) {t : ℕ} {v : Fin n} (hv : v ∉ F) :
    x (t + 1) v = (tmpl δ C A₀ A₁).g v (rcv hx t v) := by
  unfold rcv; rw [dite_eq_left_of_eq_true (eq_true hv)]; exact (hx t v hv).choose_spec.2

theorem rcv_self (hx : IsExec (tmpl δ C A₀ A₁) F x) {t : ℕ} {v : Fin n} (hv : v ∉ F) :
    rcv hx t v v = x t v := rcv_agree hx hv v hv

/-- The output of the `b`-th King Consensus instance started in round `τ + 1`, at node `v`. -/
noncomputable def kcOutT (hx : IsExec (tmpl δ C A₀ A₁) F x) (b : Bool) (τ : ℕ) (v : Fin n) :
    Option ℕ :=
  kcOut ((x (τ + 2) v).1.k3 b) (fun w => (rcv hx (τ + 2) v w).1.k3 b)

/-- Filter output trace. -/
def flT (x : ℕ → Fin n → LS n × X₀ × X₁) (b : Bool) (t : ℕ) (v : Fin n) : Option ℕ :=
  filtOut (kk Dk b * n) ((x t v).1.filt b)

/-- An execution of Algorithm 1 satisfies the trace hypotheses of `Template.lean`. -/
theorem traceHyp (hF : 3 * F.card < n) (hx : IsExec (tmpl δ C A₀ A₁) F x) :
    TraceHyp n C Dk δ F (fun t v => (x t v).1.cv)
      (fun b τ v => leader (kk Dk b) n (flT x b τ v)) (kcOutT hx) := by
  refine ⟨fun τ v hv => ?_, fun b τ => ?_⟩
  · show (x (τ + 2 + 1) v).1.cv = _
    rw [rcv_step hx hv]
    simp only [tmpl, rcv_self hx hv, kcOutT]
    rfl
  · refine kc_spec F hF _ _ (fun v w => ((rcv hx τ v w).1.cv + δ) % C)
      (fun v hv w hw => by simp only [rcv_agree hx hv w hw])
      (fun v => (x (τ + 1) v).1.k2 b) (fun v hv => ?_)
      (fun v w => (rcv hx (τ + 1) v w).1.k2 b)
      (fun v hv w hw => by simp only [rcv_agree hx hv w hw])
      (fun v => (x (τ + 2) v).1.k3 b) (fun v hv => ?_)
      (fun v w => (rcv hx (τ + 2) v w).1.k3 b)
      (fun v hv w hw => by simp only [rcv_agree hx hv w hw])
      _ (fun v hv => rfl)
    · rw [rcv_step hx hv]
      simp only [tmpl, rcv_self hx hv, ldOf, flT]
    · show (x (τ + 1 + 1) v).1.k3 b = _
      rw [rcv_step hx hv]
      simp only [tmpl, rcv_self hx hv]

/-- The `b`-th filter runs Algorithm 8 with clock set `V_b` and the sub-counter outputs as clocks. -/
theorem filtExec (hx : IsExec (tmpl δ C A₀ A₁) F x) (b : Bool) :
    IsFiltExec F (kk Dk b * n) Xf (Tset n b) (fun t w => subOut A₀ A₁ b w (x t w))
      (fun t v => (x t v).1.filt b) := by
  intro t v hv
  refine ⟨fun w => subOut A₀ A₁ b w (rcv hx t v w), fun w => ((rcv hx t v w).1.filt b).m,
    fun w hw => by simp only [rcv_agree hx hv w hw],
    fun w hw => by simp only [rcv_agree hx hv w hw], ?_⟩
  show (x (t + 1) v).1.filt b = _
  rw [rcv_step hx hv]
  simp only [tmpl, rcv_self hx hv]

/-- Faulty nodes of `V₀`, as indices. -/
def F₀ (F : Finset (Fin n)) : Finset (Fin (n / 2)) := univ.filter fun j => e₀ j ∈ F

/-- Faulty nodes of `V₁`, as indices. -/
def F₁ (F : Finset (Fin n)) : Finset (Fin (n - n / 2)) := univ.filter fun j => e₁ j ∈ F

/-- The sub-algorithm on `V₀` runs an execution of `A₀` with faulty set `F₀`. -/
theorem subExec₀ (hx : IsExec (tmpl δ C A₀ A₁) F x) :
    IsExec A₀ (F₀ F) (fun t j => (x t (e₀ j)).2.1) := by
  intro t j hj
  have hj' : e₀ j ∉ F := by simpa [F₀] using hj
  refine ⟨fun j' => (rcv hx t (e₀ j) (e₀ j')).2.1, fun j' hj'' => ?_, ?_⟩
  · have : e₀ j' ∉ F := by simpa [F₀] using hj''
    simp only [rcv_agree hx hj' _ this]
  · show (x (t + 1) (e₀ j)).2.1 = _
    rw [rcv_step hx hj']
    simp only [tmpl]
    rw [dite_eq_left_of_eq_true (eq_true (show (e₀ j : Fin n).val < n / 2 from j.isLt))]
    rfl

/-- The sub-algorithm on `V₁` runs an execution of `A₁` with faulty set `F₁`. -/
theorem subExec₁ (hx : IsExec (tmpl δ C A₀ A₁) F x) :
    IsExec A₁ (F₁ F) (fun t j => (x t (e₁ j)).2.2) := by
  intro t j hj
  have hj' : e₁ j ∉ F := by simpa [F₁] using hj
  refine ⟨fun j' => (rcv hx t (e₁ j) (e₁ j')).2.2, fun j' hj'' => ?_, ?_⟩
  · have : e₁ j' ∉ F := by simpa [F₁] using hj''
    simp only [rcv_agree hx hj' _ this]
  · show (x (t + 1) (e₁ j)).2.2 = _
    rw [rcv_step hx hj']
    simp only [tmpl]
    rw [dite_eq_left_of_eq_true (eq_true (show n / 2 ≤ (e₁ j : Fin n).val by simp [e₁]))]
    congr 1
    apply Fin.ext; simp [i₁, e₁]

end Exec

/-! ### Cardinalities of the parts -/

section Cards

variable {n : ℕ}

/-- `e₀` as an embedding. -/
def e₀Emb : Fin (n / 2) ↪ Fin n :=
  ⟨e₀, fun a b h => Fin.ext (by have := congrArg Fin.val h; simpa [e₀] using this)⟩

/-- `e₁` as an embedding. -/
def e₁Emb : Fin (n - n / 2) ↪ Fin n :=
  ⟨e₁, fun a b h => Fin.ext (by have := congrArg Fin.val h; simp [e₁] at this; omega)⟩

@[simp] theorem e₀Emb_apply (j : Fin (n / 2)) : e₀Emb j = e₀ j := rfl

@[simp] theorem e₁Emb_apply (j : Fin (n - n / 2)) : e₁Emb j = e₁ j := rfl

theorem Tset_false_inter (F : Finset (Fin n)) :
    Tset n false ∩ F = (F₀ F).map e₀Emb := by
  ext w
  simp only [Tset, side, F₀, mem_inter, mem_filter, mem_univ, true_and, mem_map,
    e₀Emb_apply, decide_eq_false_iff_not, not_le]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨w, h1⟩, by simpa [e₀] using h2, Fin.ext rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j.isLt, hj⟩

theorem Tset_true_inter (F : Finset (Fin n)) :
    Tset n true ∩ F = (F₁ F).map e₁Emb := by
  ext w
  simp only [Tset, side, F₁, mem_inter, mem_filter, mem_univ, true_and, mem_map,
    e₁Emb_apply, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨w - n / 2, by omega⟩, ?_, ?_⟩
    · have : e₁ ⟨w - n / 2, by omega⟩ = w := Fin.ext (by simp [e₁]; omega)
      rw [this]; exact h2
    · exact Fin.ext (by simp [e₁]; omega)
  · rintro ⟨j, hj, rfl⟩; exact ⟨by simp [e₁], hj⟩

theorem card_inter_false (F : Finset (Fin n)) : (Tset n false ∩ F).card = (F₀ F).card := by
  rw [Tset_false_inter, card_map]

theorem card_inter_true (F : Finset (Fin n)) : (Tset n true ∩ F).card = (F₁ F).card := by
  rw [Tset_true_inter, card_map]

theorem card_Tset_false : (Tset n false).card = n / 2 := by
  have := card_inter_false (n := n) univ
  rw [inter_univ] at this
  rw [this, F₀]; simp

theorem card_Tset_true : (Tset n true).card = n - n / 2 := by
  have := card_inter_true (n := n) univ
  rw [inter_univ] at this
  rw [this, F₁]; simp

theorem card_F₀_add_F₁ (F : Finset (Fin n)) : (F₀ F).card + (F₁ F).card = F.card := by
  rw [← card_inter_false, ← card_inter_true]
  have := card_filter_add_card_filter_not (s := F) (fun w => side w = false)
  have h1 : F.filter (fun w => side w = false) = Tset n false ∩ F := by
    ext w; simp [Tset, and_comm]
  have h2 : F.filter (fun w => ¬ side w = false) = Tset n true ∩ F := by
    ext w; simp [Tset, and_comm]
  rw [h1, h2] at this
  exact this

end Cards

/-! ### Theorem 5.7 -/

section Main

variable [NeZero C] {A₀ : Algorithm (Fin (n / 2)) X₀ (kk Dk false * n)}
  {A₁ : Algorithm (Fin (n - n / 2)) X₁ (kk Dk true * n)}

/-- Lemma 5.1: if the sub-counter of `V_b` counts from `s`, the `b`-th filter counts from
`s + X + 2`. -/
theorem lemma_5_1 {F : Finset (Fin n)} {x : ℕ → Fin n → LS n × X₀ × X₁}
    (hF : 3 * F.card < n) (hx : IsExec (tmpl δ C A₀ A₁) F x) (b : Bool)
    (hT : 2 * (Tset n b ∩ F).card < (Tset n b).card) (s c₀ : ℕ)
    (hc : ∀ j, ∀ w, w ∈ Tset n b → w ∉ F → subOut A₀ A₁ b w (x (s + j) w) = (c₀ + j) % (kk Dk b * n)) :
    OCountsFrom F (kk Dk b * n) (flT x b) (s + Xf + 2) :=
  filt_validity hF hT (filtExec hx b) s c₀ hc

/-- Theorem 5.7 (second statement), for Algorithm 1 with Algorithm 8 filtering (`X = 48`) and the
3-round King Consensus Algorithm 10 (`k₀ = 12`, `k₁ = 15`): if the sub-counters on `V₀`, `V₁` are
early-stabilizing with times `T₀`, `T₁`, then every execution with `3 f < n` stabilizes within
`T_b(f_b) + 50 + 60 (f + 1) + 3` for each part `b` with `3 f_b < |V_b|`. The filtering
stabilization time is `S_F = X + 2 = 50`. -/
theorem theorem_5_7 {T₀ T₁ : ℕ → ℕ} (h₀ : IsESCounter A₀ T₀) (h₁ : IsESCounter A₁ T₁)
    (F : Finset (Fin n)) (hF : 3 * F.card < n) (x : ℕ → Fin n → LS n × X₀ × X₁)
    (hx : IsExec (tmpl 2 C A₀ A₁) F x) :
    (3 * (F₀ F).card < n / 2 →
      StabilisesIn (tmpl 2 C A₀ A₁) F x (T₀ (F₀ F).card + 50 + 60 * (F.card + 1) + 3)) ∧
    (3 * (F₁ F).card < n - n / 2 →
      StabilisesIn (tmpl 2 C A₀ A₁) F x (T₁ (F₁ F).card + 50 + 60 * (F.card + 1) + 3)) := by
  have hcr : ∀ b, Crusader F (kk Dk b * n) (Xf - 1) Xf (flT x b) := fun b =>
    filt_crusader hF (by simp [Xf]) (filtExec hx b)
  have hth := traceHyp hF hx
  have fin : ∀ b (T : ℕ), OCountsFrom F (kk Dk b * n) (flT x b) (T + 50) →
      StabilisesIn (tmpl 2 C A₀ A₁) F x (T + 50 + 60 * (F.card + 1) + 3) := by
    intro b T hb
    have hb' := hcr (!b)
    have := theorem_5_7_trace (D := Dk) (W := Xf - 1) hF (by simp [Dk]) (by simp [Dk, Xf])
      hth b (T + 50) Xf hb hb'
    rw [show max (T + 50) Xf + 20 * Dk * (F.card + 1) + Dk = T + 50 + 60 * (F.card + 1) + 3 by
      simp only [Xf, Dk]; omega] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, fun r i hi => hc r i hi⟩
  constructor
  · intro h
    obtain ⟨v₀, hv₀⟩ := h₀ (F₀ F) h _ (subExec₀ hx)
    refine fin false _ (lemma_5_1 hF hx false ?_ _ v₀ fun j w hw hwF => ?_)
    · rw [card_inter_false, card_Tset_false]; omega
    · have hw' : w.val < n / 2 := by simpa [Tset, side] using hw
      have hj : i₀ w hw' ∉ F₀ F := by
        simp only [F₀, mem_filter, mem_univ, true_and]
        rwa [show e₀ (i₀ w hw') = w from Fin.ext rfl]
      have := hv₀ j _ hj
      simp only [subOut, Bool.false_eq_true, ite_false, dite_eq_left hw']
      rw [← this]
      rfl
  · intro h
    obtain ⟨v₀, hv₀⟩ := h₁ (F₁ F) h _ (subExec₁ hx)
    refine fin true _ (lemma_5_1 hF hx true ?_ _ v₀ fun j w hw hwF => ?_)
    · rw [card_inter_true, card_Tset_true]; omega
    · have hw' : n / 2 ≤ w.val := by simpa [Tset, side] using hw
      have he : e₁ (i₁ w hw') = w := Fin.ext (by simp [e₁, i₁]; omega)
      have hj : i₁ w hw' ∉ F₁ F := by
        simp only [F₁, mem_filter, mem_univ, true_and]
        rwa [he]
      have := hv₀ j _ hj
      simp only [subOut, ite_true, dite_eq_left hw']
      rw [← this]
      beta_reduce
      rw [he]

/-- Theorem 5.7 (first statement): every execution with `3 f < n` stabilizes within
`max_b (T_b(f_b) + S_F) + O(f + 1)`. -/
theorem theorem_5_7_max {T₀ T₁ : ℕ → ℕ} (h₀ : IsESCounter A₀ T₀) (h₁ : IsESCounter A₁ T₁)
    (F : Finset (Fin n)) (hF : 3 * F.card < n) (x : ℕ → Fin n → LS n × X₀ × X₁)
    (hx : IsExec (tmpl 2 C A₀ A₁) F x) :
    StabilisesIn (tmpl 2 C A₀ A₁) F x
      (max (T₀ (F₀ F).card) (T₁ (F₁ F).card) + 50 + 60 * (F.card + 1) + 3) := by
  have hsum := card_F₀_add_F₁ F
  obtain ⟨h0, h1⟩ := theorem_5_7 h₀ h₁ F hF x hx
  by_cases hb : 3 * (F₀ F).card < n / 2
  · exact (h0 hb).mono (by omega)
  · exact (h1 (by omega)).mono (by omega)

end Main

end EarlyStabilizingCounting
