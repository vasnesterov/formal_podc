import Papers.PODC2020.SSLERegular.EulerGood
import Papers.PODC2020.SSLERegular.EulerErrors
import Papers.PODC2020.SSLERegular.TokenRing

/-!
# Running the ring protocol and SS-Token on a virtual ring (Lemma 3.2, repaired protocol)

In a coherent configuration (`Base S C`, skeleton `S` with `InjCol` and `EdgeOK`), each cycle of
the virtual-ring permutation `σ` is a directed ring. Every step of the Ring-Protocol on it is
realised by one interaction (`lift_ring`), and stepping SS-Token along the ring realises the
abstract dynamics of `TokenRing` (`token_run`) — in both cases unless an error is raised
(tokens on two adjacent nodes), which is fine for Lemma 3.2. Virtual nodes outside the cycle are
untouched.
-/

set_option linter.unusedSectionVars false

open Finset

namespace SSLERegular

universe u

variable {RS : Type*} {k : ℕ} {V : Type u} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
  [DecidableRel G.Adj] {R : RingProtocol RS}

/-! ### Cycles of a permutation -/

section Cyc

variable {W : Type*} [Fintype W] [DecidableEq W] (σ : Equiv.Perm W) (w : W)

lemma mem_periodicPts_perm : w ∈ Function.periodicPts σ := by
  refine ⟨orderOf σ, orderOf_pos σ, ?_⟩
  show σ^[orderOf σ] w = w
  rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]; rfl

lemma period_pos : 0 < Function.minimalPeriod σ w :=
  Function.minimalPeriod_pos_of_mem_periodicPts (mem_periodicPts_perm σ w)

lemma pow_period : (σ ^ Function.minimalPeriod σ w) w = w := by
  rw [Equiv.Perm.coe_pow]; exact Function.iterate_minimalPeriod

lemma pow_mod_period (n : ℕ) : (σ ^ (n % Function.minimalPeriod σ w)) w = (σ ^ n) w := by
  rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow]; exact Function.iterate_mod_minimalPeriod_eq

lemma pow_inj_period {m n : ℕ} (hm : m < Function.minimalPeriod σ w)
    (hn : n < Function.minimalPeriod σ w) (h : (σ ^ m) w = (σ ^ n) w) : m = n := by
  rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow] at h
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hm hn).1 h

lemma apply_pow_succP (t : ℕ) (ht : t < Function.minimalPeriod σ w) :
    σ ((σ ^ t) w) = (σ ^ TokenRing.succP (Function.minimalPeriod σ w) t) w := by
  rw [← Equiv.Perm.mul_apply, ← pow_succ']
  unfold TokenRing.succP
  split_ifs with h
  · rw [h, pow_period, pow_zero]; rfl
  · rfl

lemma sameCycle_iff_exists_lt {w' : W} :
    σ.SameCycle w w' ↔ ∃ t < Function.minimalPeriod σ w, (σ ^ t) w = w' := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n % Function.minimalPeriod σ w, Nat.mod_lt _ (period_pos σ w),
      by rw [pow_mod_period, hn]⟩
  · rintro ⟨t, -, rfl⟩
    exact ⟨t, by simp⟩

end Cyc

/-! ### Lifting ring-protocol runs -/

section Lift

variable {S : V → Skel k} (hdeg : ∀ v, G.degree v = 2 * k) (hinj : InjCol G S) (hok : EdgeOK G S)
  {X : Type*} [DecidableEq X] (τ : Equiv.Perm X) (e : X → V × Fin k) (he : Function.Injective e)
  (hτ : ∀ x, vperm hdeg hinj hok (e x) = e (τ x))

open Classical in
/-- A choice whose ring selection returns `o` on the pair `(a, b)` and `RandBit1 = true`. -/
noncomputable def chWith (ch0 : EChoice k RS) (a b : RS) (o : RS × RS) : EChoice k RS :=
  { ch0 with ρ := (fun a' b' => if a' = a ∧ b' = b then o else ch0.ρ a' b'),
             b1 := true }

lemma chWith_valid {ch0 : EChoice k RS} (h : ch0.Valid R) {a b : RS} {o : RS × RS}
    (ho : o ∈ R.δ a b) : (chWith ch0 a b o).Valid R := by
  classical
  refine ⟨fun a' b' => ?_, h.2⟩
  simp only [chWith]
  split_ifs with hab
  · obtain ⟨rfl, rfl⟩ := hab; exact ho
  · exact h.1 a' b'

lemma vEdge_ringState (ρ : RS → RS → RS × RS) (a b : VNode k RS) :
    (vEdge R ρ a b).1.ringState = (ρ a.ringState b.ringState).1 ∧
    (vEdge R ρ a b).2.ringState = (ρ a.ringState b.ringState).2 := by
  unfold vEdge ssToken; dsimp only; split_ifs <;> simp

include he hτ in
/-- The ring configuration after one edge step on `e x → e (τ x)`. -/
lemma ring_vnAfter (C : V → EState k RS) (ρ : RS → RS → RS × RS) (x : X) :
    (fun y => (vnAfter hdeg hinj hok R C ρ (e x) (e y)).ringState) =
      Function.update (Function.update (fun y => (vn C (e y)).ringState) x
        (ρ (vn C (e x)).ringState (vn C (e (τ x))).ringState).1) (τ x)
        (ρ (vn C (e x)).ringState (vn C (e (τ x))).ringState).2 := by
  funext y
  obtain ⟨h1, h2⟩ := vEdge_ringState (R := R) ρ (vn C (e x)) (vn C (e (τ x)))
  simp only [vnAfter, Function.update_apply, hτ, he.eq_iff]
  split_ifs with a b <;> simp_all

include he hτ in
lemma vnAfter_outside (C : V → EState k RS) (ρ : RS → RS → RS × RS) (x : X) (w : V × Fin k)
    (hw : ∀ y, e y ≠ w) : vnAfter hdeg hinj hok R C ρ (e x) w = vn C w := by
  simp only [vnAfter, hτ]
  rw [Function.update_of_ne (hw _).symm, Function.update_of_ne (hw _).symm]

include he hτ in
/-- **Lifting the Ring-Protocol.** Every run of the ring protocol on the directed ring `(X, τ)`
embedded by `e` into the virtual ring is realised by interactions, unless an error is raised;
virtual nodes outside `e`'s range are unchanged. -/
lemma lift_ring (hR : ∀ a b, (R.δ a b).Nonempty) (C : V → EState k RS) (hC : Base G S C)
    (c' : X → RS)
    (h : Relation.ReflTransGen (RingStepOn R τ) (fun x => (vn C (e x)).ringState) c') :
    ∃ D, (ssEuler true k R).Reachable G C D ∧ (Err D ∨ (Base G S D ∧
      (fun x => (vn D (e x)).ringState) = c' ∧ ∀ w, (∀ y, e y ≠ w) → vn D w = vn C w)) := by
  classical
  induction h with
  | refl => exact ⟨C, Relation.ReflTransGen.refl, Or.inr ⟨hC, rfl, fun _ _ => rfl⟩⟩
  | @tail c1 c2 _ hst ih =>
    obtain ⟨D, hCD, hD⟩ := ih
    rcases hD with hE | ⟨hB, hring, hout⟩
    · obtain ⟨D', hCD'⟩ : ∃ D', (ssEuler true k R).Reachable G C D' ∧ Err D' := ⟨D, hCD, hE⟩
      exact ⟨D', hCD'.1, Or.inl hCD'.2⟩
    obtain ⟨x, o, ho, rfl⟩ := hst
    obtain ⟨ch0, hch0, -⟩ := exists_valid_choice R hR (D (e x).1).color (D (e x).1)
    set ch := chWith ch0 (c1 x) (c1 (τ x)) o
    have hch : ch.Valid R := chWith_valid hch0 ho
    obtain ⟨hT1, hT2⟩ := interact_fwd hdeg hinj hok R hB (e x) ch hch
    have hstep := step_of_choice true D (adj_vperm hdeg hinj hok (e x)) ch hch
    by_cases hT : TokBoth (vnAfter hdeg hinj hok R D ch.ρ (e x)) (e x).1
        (vperm hdeg hinj hok (e x)).1
    · exact ⟨_, hCD.tail hstep, Or.inl ⟨_, (hT1 hT).trans (by simp [ch, chWith])⟩⟩
    obtain ⟨hB', hvn⟩ := hT2 hT
    refine ⟨_, hCD.tail hstep, Or.inr ⟨hB', ?_, fun w hw => ?_⟩⟩
    · rw [hvn, ring_vnAfter hdeg hinj hok τ e he hτ D ch.ρ x]
      have hx : (vn D (e x)).ringState = c1 x := congrFun hring x
      have hτx : (vn D (e (τ x))).ringState = c1 (τ x) := congrFun hring (τ x)
      rw [hring, hx, hτx]
      simp [ch, chWith]
    · rw [hvn, vnAfter_outside hdeg hinj hok τ e he hτ D ch.ρ x w hw, hout w hw]

lemma vEdge_tok (ρ : RS → RS → RS × RS) (a b : VNode k RS) :
    ((R.lead (ρ a.ringState b.ringState).2 = false ∧ b.bit ≠ a.bit) ∨
        (R.lead (ρ a.ringState b.ringState).2 = true ∧ a.bit = b.bit) →
      (vEdge R ρ a b).1.token = false ∧ (vEdge R ρ a b).1.bit = a.bit ∧
      (vEdge R ρ a b).2.token = true ∧ (vEdge R ρ a b).2.bit = !b.bit) ∧
    (¬ ((R.lead (ρ a.ringState b.ringState).2 = false ∧ b.bit ≠ a.bit) ∨
        (R.lead (ρ a.ringState b.ringState).2 = true ∧ a.bit = b.bit)) →
      (vEdge R ρ a b).1.token = a.token ∧ (vEdge R ρ a b).1.bit = a.bit ∧
      (vEdge R ρ a b).2.token = b.token ∧ (vEdge R ρ a b).2.bit = b.bit) := by
  unfold vEdge ssToken
  cases hl : R.lead (ρ a.ringState b.ringState).2 <;> cases ha : a.bit <;> cases hb : b.bit <;>
    simp [hl, ha, hb]

include he hτ in
/-- **Lifting SS-Token.** On a directed ring `(X, τ)` embedded by `e` whose ring part is
valid-stable with leader `e xl`, stepping along the ring from the leader realises the abstract
SS-Token run `TokenRing.run` (positions `t < N` are the virtual nodes `σ^t (e xl)`), unless an
error is raised. -/
lemma token_run (hR : ∀ a b, (R.δ a b).Nonempty) (C : V → EState k RS) (hC : Base G S C)
    (hring : RingValidOn R τ (fun x => (vn C (e x)).ringState)) (xl : X)
    (hxl : R.lead (vn C (e xl)).ringState = true)
    (hcov : ∀ t : ℕ, ∃ x, e x = (vperm hdeg hinj hok ^ t) (e xl)) (n : ℕ) :
    ∃ D, (ssEuler true k R).Reachable G C D ∧ (Err D ∨ (Base G S D ∧
      RingValidOn R τ (fun x => (vn D (e x)).ringState) ∧
      (∀ x, R.lead (vn D (e x)).ringState = R.lead (vn C (e x)).ringState) ∧
      (∀ w, (∀ y, e y ≠ w) → vn D w = vn C w) ∧
      ∀ t < Function.minimalPeriod (vperm hdeg hinj hok) (e xl),
        (vn D ((vperm hdeg hinj hok ^ t) (e xl))).token =
          (TokenRing.run (Function.minimalPeriod (vperm hdeg hinj hok) (e xl))
            (fun t => (vn C ((vperm hdeg hinj hok ^ t) (e xl))).token,
             fun t => (vn C ((vperm hdeg hinj hok ^ t) (e xl))).bit) n).1 t ∧
        (vn D ((vperm hdeg hinj hok ^ t) (e xl))).bit =
          (TokenRing.run (Function.minimalPeriod (vperm hdeg hinj hok) (e xl))
            (fun t => (vn C ((vperm hdeg hinj hok ^ t) (e xl))).token,
             fun t => (vn C ((vperm hdeg hinj hok ^ t) (e xl))).bit) n).2 t)) := by
  classical
  set σ := vperm hdeg hinj hok with hσ
  set N := Function.minimalPeriod σ (e xl) with hN
  set pos : ℕ → V × Fin k := fun t => (σ ^ t) (e xl) with hpos
  have hNpos : 0 < N := period_pos σ (e xl)
  have hN2 : 2 ≤ N := by
    by_contra h
    have h1 : N = 1 := by omega
    have := pow_period σ (e xl)
    rw [← hN, h1, pow_one] at this
    exact node_ne_vperm hdeg hinj hok (e xl) (congrArg Prod.fst this).symm
  -- leaders on the ring
  obtain ⟨-, xl', -, huniq⟩ := id hring
  have hlead : ∀ s < N, ∀ x, e x = pos s → R.lead (vn C (e x)).ringState = decide (s = 0) := by
    intro s hs x hx
    by_cases h0 : s = 0
    · rw [h0] at hx
      have : x = xl := he (by rw [hx]; simp [hpos])
      rw [this, hxl]; simp [h0]
    · rw [decide_eq_false h0]
      by_contra hne
      have h1 : R.lead (vn C (e x)).ringState = true := by simpa using hne
      have : x = xl := (huniq x h1).trans (huniq xl hxl).symm
      rw [this] at hx
      exact h0 (pow_inj_period σ (e xl) hs hNpos (by simpa [hpos] using hx.symm))
  induction n with
  | zero => exact ⟨C, Relation.ReflTransGen.refl, Or.inr ⟨hC, hring, fun _ => rfl, fun _ _ => rfl,
      fun t _ => ⟨rfl, rfl⟩⟩⟩
  | succ n ih =>
    obtain ⟨D, hCD, hD⟩ := ih
    rcases hD with hE | ⟨hB, hringD, hleadD, hout, htok⟩
    · exact ⟨D, hCD, Or.inl hE⟩
    set t := n % N with ht
    have htN : t < N := Nat.mod_lt _ hNpos
    obtain ⟨xt, hxt⟩ := hcov t
    have hsucc : e (τ xt) = pos (TokenRing.succP N t) := by
      rw [← hτ, hxt]; exact apply_pow_succP σ (e xl) t htN
    have hsN : TokenRing.succP N t < N := by
      unfold TokenRing.succP; split_ifs <;> omega
    have hst : TokenRing.succP N t ≠ t := by
      unfold TokenRing.succP; split_ifs <;> omega
    obtain ⟨ch0, hch0, -⟩ := exists_valid_choice R hR (D (e xt).1).color (D (e xt).1)
    obtain ⟨o, ho⟩ := hR (vn D (e xt)).ringState (vn D (e (τ xt))).ringState
    set ch := chWith ch0 (vn D (e xt)).ringState (vn D (e (τ xt))).ringState o
    have hch : ch.Valid R := chWith_valid hch0 ho
    have hρ : ch.ρ (vn D (e xt)).ringState (vn D (e (τ xt))).ringState = o := by
      simp [ch, chWith]
    obtain ⟨hT1, hT2⟩ := interact_fwd hdeg hinj hok R hB (e xt) ch hch
    have hstep := step_of_choice true D (adj_vperm hdeg hinj hok (e xt)) ch hch
    by_cases hT : TokBoth (vnAfter hdeg hinj hok R D ch.ρ (e xt)) (e xt).1 (σ (e xt)).1
    · exact ⟨_, hCD.tail hstep, Or.inl ⟨_, (hT1 hT).trans (by simp [ch, chWith])⟩⟩
    obtain ⟨hB', hvn⟩ := hT2 hT
    -- the ring step
    have hrs : RingStepOn R τ (fun x => (vn D (e x)).ringState)
        (fun x => (vn (upd D (e xt).1 (σ (e xt)).1 (eulerStep true R ch (D (e xt).1)
          (D (σ (e xt)).1))) (e x)).ringState) := by
      refine ⟨xt, o, ho, ?_⟩
      rw [hvn, ring_vnAfter hdeg hinj hok τ e he hτ D ch.ρ xt, hρ]
    have hlead' : ∀ x, R.lead (vn (upd D (e xt).1 (σ (e xt)).1 (eulerStep true R ch (D (e xt).1)
        (D (σ (e xt)).1))) (e x)).ringState = R.lead (vn D (e x)).ringState :=
      hringD.1 _ (Relation.ReflTransGen.single hrs)
    refine ⟨_, hCD.tail hstep, Or.inr ⟨hB', hringD.step hrs, fun x => (hlead' x).trans (hleadD x),
      fun w hw => ?_, fun s hs => ?_⟩⟩
    · rw [hvn, vnAfter_outside hdeg hinj hok τ e he hτ D ch.ρ xt w hw, hout w hw]
    -- tokens and bits
    have hlb : R.lead o.2 = decide (TokenRing.succP N t = 0) := by
      have h1 := hlead' (τ xt)
      have hv2 : vnAfter hdeg hinj hok R D ch.ρ (e xt) (e (τ xt)) =
          (vEdge R ch.ρ (vn D (e xt)) (vn D (e (τ xt)))).2 := by
        rw [← hτ, hσ]; simp [vnAfter]
      rw [hvn, hv2, (vEdge_ringState (R := R) ch.ρ _ _).2, hρ] at h1
      rw [h1, hleadD, hlead _ hsN _ hsucc]
    obtain ⟨hF1, hF2⟩ := vEdge_tok (R := R) ch.ρ (vn D (e xt)) (vn D (e (τ xt)))
    rw [hρ, hlb] at hF1 hF2
    have hrun : TokenRing.run N (fun t => (vn C (pos t)).token, fun t => (vn C (pos t)).bit) (n + 1)
        = TokenRing.stepT N (TokenRing.run N (fun t => (vn C (pos t)).token,
          fun t => (vn C (pos t)).bit) n) t := rfl
    set st := TokenRing.run N (fun t => (vn C (pos t)).token, fun t => (vn C (pos t)).bit) n
    have hbt : ∀ s < N, st.2 s = (vn D (pos s)).bit := fun s hs => (htok s hs).2.symm
    have htk : ∀ s < N, st.1 s = (vn D (pos s)).token := fun s hs => (htok s hs).1.symm
    have hfires : TokenRing.Fires N st.2 t ↔
        ((decide (TokenRing.succP N t = 0) = false ∧
            (vn D (e (τ xt))).bit ≠ (vn D (e xt)).bit) ∨
          (decide (TokenRing.succP N t = 0) = true ∧ (vn D (e xt)).bit = (vn D (e (τ xt))).bit)) := by
      unfold TokenRing.Fires
      rw [hbt _ hsN, hbt _ htN, hsucc, hxt]
      simp [hpos]
    have hvs : vn (upd D (e xt).1 (σ (e xt)).1 (eulerStep true R ch (D (e xt).1)
        (D (σ (e xt)).1))) (pos s) = if pos s = e (τ xt) then
          (vEdge R ch.ρ (vn D (e xt)) (vn D (e (τ xt)))).2
        else if pos s = e xt then (vEdge R ch.ρ (vn D (e xt)) (vn D (e (τ xt)))).1
        else vn D (pos s) := by
      rw [hvn]; simp only [vnAfter, Function.update_apply]; rw [← hσ, hτ]
    have hinjp : ∀ a < N, ∀ b < N, pos a = pos b → a = b :=
      fun a ha b hb h => pow_inj_period σ (e xl) ha hb h
    rw [hvs, hrun]
    unfold TokenRing.stepT
    by_cases hf : TokenRing.Fires N st.2 t
    · have := hF1 (hfires.1 hf)
      rw [if_pos hf]
      simp only [Function.update_apply]
      by_cases h1 : s = TokenRing.succP N t
      · rw [if_pos (by rw [h1, hsucc]), if_pos h1, if_pos h1]
        refine ⟨this.2.2.1, ?_⟩
        rw [this.2.2.2, hbt _ hsN, hsucc]
      · rw [if_neg (fun h => h1 (hinjp s hs _ hsN (h.trans hsucc))), if_neg h1, if_neg h1]
        by_cases h2 : s = t
        · rw [if_pos (by rw [h2, hxt]), if_pos h2]
          refine ⟨this.1, ?_⟩
          rw [this.2.1, hbt _ hs, h2, hxt]
        · rw [if_neg (fun h => h2 (hinjp s hs t htN (h.trans hxt))), if_neg h2,
            htk s hs, hbt s hs]
          exact ⟨rfl, rfl⟩
    · have := hF2 (fun h => hf (hfires.2 h))
      rw [if_neg hf]
      by_cases h1 : s = TokenRing.succP N t
      · rw [if_pos (by rw [h1, hsucc]), this.2.2.1, this.2.2.2, htk _ hs, hbt _ hs, h1, hsucc]
        exact ⟨rfl, rfl⟩
      · rw [if_neg (fun h => h1 (hinjp s hs _ hsN (h.trans hsucc)))]
        by_cases h2 : s = t
        · rw [if_pos (by rw [h2, hxt]), this.1, this.2.1, htk _ hs, hbt _ hs, h2, hxt]
          exact ⟨rfl, rfl⟩
        · rw [if_neg (fun h => h2 (hinjp s hs t htN (h.trans hxt))), htk s hs, hbt s hs]
          exact ⟨rfl, rfl⟩

/-- One SS-Token step on the edge at position `t` of the cycle through `wl`, in terms of
`TokenRing.stepT` (the leader output of the successor's new ring state is given). -/
lemma vnAfter_tok (D : V → EState k RS) (ρ : RS → RS → RS × RS) (wl : V × Fin k) {t : ℕ}
    (ht : t < Function.minimalPeriod (vperm hdeg hinj hok) wl)
    (hlb : R.lead (ρ (vn D ((vperm hdeg hinj hok ^ t) wl)).ringState
      (vn D (vperm hdeg hinj hok ((vperm hdeg hinj hok ^ t) wl))).ringState).2 =
        decide (TokenRing.succP (Function.minimalPeriod (vperm hdeg hinj hok) wl) t = 0)) :
    ∀ s < Function.minimalPeriod (vperm hdeg hinj hok) wl,
      (vnAfter hdeg hinj hok R D ρ ((vperm hdeg hinj hok ^ t) wl)
        ((vperm hdeg hinj hok ^ s) wl)).token =
        (TokenRing.stepT (Function.minimalPeriod (vperm hdeg hinj hok) wl)
          (fun s => (vn D ((vperm hdeg hinj hok ^ s) wl)).token,
           fun s => (vn D ((vperm hdeg hinj hok ^ s) wl)).bit) t).1 s ∧
      (vnAfter hdeg hinj hok R D ρ ((vperm hdeg hinj hok ^ t) wl)
        ((vperm hdeg hinj hok ^ s) wl)).bit =
        (TokenRing.stepT (Function.minimalPeriod (vperm hdeg hinj hok) wl)
          (fun s => (vn D ((vperm hdeg hinj hok ^ s) wl)).token,
           fun s => (vn D ((vperm hdeg hinj hok ^ s) wl)).bit) t).2 s := by
  classical
  set σ := vperm hdeg hinj hok with hσ
  set N := Function.minimalPeriod σ wl with hN
  set pos : ℕ → V × Fin k := fun t => (σ ^ t) wl with hpos
  have hNpos : 0 < N := period_pos σ wl
  have hN2 : 2 ≤ N := by
    by_contra h
    have h1 : N = 1 := by omega
    have := pow_period σ wl
    rw [← hN, h1, pow_one] at this
    exact node_ne_vperm hdeg hinj hok wl (congrArg Prod.fst this).symm
  have hsucc : σ (pos t) = pos (TokenRing.succP N t) := apply_pow_succP σ wl t ht
  have hsN : TokenRing.succP N t < N := by
    unfold TokenRing.succP; split_ifs <;> omega
  have hinjp : ∀ a < N, ∀ b < N, pos a = pos b → a = b :=
    fun a ha b hb h => pow_inj_period σ wl ha hb h
  intro s hs
  obtain ⟨hF1, hF2⟩ := vEdge_tok (R := R) ρ (vn D (pos t)) (vn D (σ (pos t)))
  rw [hlb] at hF1 hF2
  have hfires : TokenRing.Fires N (fun s => (vn D (pos s)).bit) t ↔
      ((decide (TokenRing.succP N t = 0) = false ∧
          (vn D (σ (pos t))).bit ≠ (vn D (pos t)).bit) ∨
        (decide (TokenRing.succP N t = 0) = true ∧ (vn D (pos t)).bit = (vn D (σ (pos t))).bit)) := by
    unfold TokenRing.Fires
    rw [hsucc]
    simp
  have hvs : vnAfter hdeg hinj hok R D ρ (pos t) (pos s) = if pos s = σ (pos t) then
        (vEdge R ρ (vn D (pos t)) (vn D (σ (pos t)))).2
      else if pos s = pos t then (vEdge R ρ (vn D (pos t)) (vn D (σ (pos t)))).1
      else vn D (pos s) := by
    simp only [vnAfter, Function.update_apply]; rw [← hσ]
  rw [hvs]
  unfold TokenRing.stepT
  by_cases hf : TokenRing.Fires N (fun s => (vn D (pos s)).bit) t
  · have := hF1 (hfires.1 hf)
    rw [if_pos hf]
    simp only [Function.update_apply]
    by_cases h1 : s = TokenRing.succP N t
    · rw [if_pos (by rw [h1, hsucc]), if_pos h1, if_pos h1]
      refine ⟨this.2.2.1, ?_⟩
      rw [this.2.2.2, hsucc]
    · rw [if_neg (fun h => h1 (hinjp s hs _ hsN (h.trans hsucc))), if_neg h1, if_neg h1]
      by_cases h2 : s = t
      · rw [if_pos (by rw [h2]), if_pos h2]
        refine ⟨this.1, ?_⟩
        rw [this.2.1, h2]
      · rw [if_neg (fun h => h2 (hinjp s hs t ht h)), if_neg h2]
        exact ⟨rfl, rfl⟩
  · have := hF2 (fun h => hf (hfires.2 h))
    rw [if_neg hf]
    by_cases h1 : s = TokenRing.succP N t
    · rw [if_pos (by rw [h1, hsucc]), this.2.2.1, this.2.2.2, hsucc, h1]
      exact ⟨rfl, rfl⟩
    · rw [if_neg (fun h => h1 (hinjp s hs _ hsN (h.trans hsucc)))]
      by_cases h2 : s = t
      · rw [if_pos (by rw [h2]), this.1, this.2.1, h2]
        exact ⟨rfl, rfl⟩
      · rw [if_neg (fun h => h2 (hinjp s hs t ht h))]
        exact ⟨rfl, rfl⟩

end Lift

end SSLERegular
