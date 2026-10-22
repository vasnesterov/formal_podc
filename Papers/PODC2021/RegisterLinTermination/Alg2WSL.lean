import Papers.PODC2021.RegisterLinTermination.Alg2WSLInv

/-!
# Theorem 10: Algorithm 2 is write strongly-linearizable

Hadzilacos, Hu and Toueg, *On Register Linearizability and Termination*, PODC 2021, Theorem 10
and Appendix C.

The write strong-linearization function is `linFun α = mwmrLin α WS(α) rf_α`, where `WS(α)` is
the on-line write sequence of Algorithm 3 (computed in `Alg2WSLInv.lean`) and `rf_α` maps each
completed read to the position of the write whose timestamp it returned. The linearization
property follows from the MWMR reads-from criterion (`MWMRReadsFrom.isLinearization`); the
prefix property from the fact that `WS` only grows.

The proof follows Appendix C: temporal facts (`TQ`: memory, partial timestamps and read results
only grow, Observation 25 and Lemma 27), Observation 36, Lemma 38 and Claim 42.1 (`core`).
-/

namespace Podc.RegisterLinTermination.Alg2

open Cslib.SharedMemory List

set_option linter.unusedSectionVars false

namespace WSL

variable {V : Type} {v₀ : V} {n : ℕ} [NeZero n]

/-! ## Lexicographic order: `¬ b < a` is a total preorder -/

lemma not_lt_trans {a b c : List ℕ} (h₁ : ¬ b < a) (h₂ : ¬ c < b) : ¬ c < a := by
  intro h
  rcases Std.lt_trichotomy a b with h' | rfl | h'
  · exact h₂ (List.lt_trans h h')
  · exact h₂ h
  · exact h₁ h'

lemma newBest_ge_best (best c : Cell V) : ¬ (newBest best c).2 < best.2 := by
  unfold newBest; split_ifs with h
  · exact List.lt_asymm h
  · exact List.lt_irrefl _

lemma newBest_ge_c (best c : Cell V) : ¬ (newBest best c).2 < c.2 := by
  unfold newBest; split_ifs with h
  · exact List.lt_irrefl _
  · exact h

/-! ## Temporal facts -/

/-- The partial timestamp of the write `y` after `δ` (`[]` if `y` has not started or is not a
write in progress). -/
def preAt (δ : List (Lbl V v₀ n)) (Cδ : Cfg V v₀ n) (y : OpId (Fin n)) : List ℕ :=
  if curOp δ y.1 = y then (part (Cδ.loc y.1)).getD [] else []

lemma preAt_cur {δ : List (Lbl V v₀ n)} {Cδ : Cfg V v₀ n} {p : Fin n} {pre : List ℕ}
    (h : part (Cδ.loc p) = some pre) : preAt δ Cδ (curOp δ p) = pre := by
  simp [preAt, h]

lemma preAt_of_not_invoked {δ : List (Lbl V v₀ n)} {Cδ : Cfg V v₀ n} {g : GS V n}
    (hrun : (alg2 V v₀ n).run δ = some Cδ) (hI : Inv δ Cδ g) {y : OpId (Fin n)}
    (hy : ¬ Invoked δ y) : preAt δ Cδ y = [] := by
  unfold preAt
  split_ifs with h
  · cases hp : part (Cδ.loc y.1) with
    | none => rfl
    | some pre =>
      obtain ⟨v, hv⟩ := hI.locOK_pend hp
      exact absurd (h ▸ (Impl.run_pend_curOp hrun hv).1) hy
  · rfl

/-- Facts relating the state after `δ` with the state after a later `β`. -/
structure TQ (δ : List (Lbl V v₀ n)) (Cδ : Cfg V v₀ n) (gδ : GS V n) (β : List (Lbl V v₀ n))
    (C : Cfg V v₀ n) (g : GS V n) : Prop where
  mem : ∀ k, CwLe (Cδ.mem k).2 (C.mem k).2
  wts : ∀ x t, gδ.wts x = some t → g.wts x = some t
  rcell : ∀ x c, gδ.rcell x = some c → g.rcell x = some c
  /-- Observation 25 and the entries read after `δ`, for writes in progress -/
  wip : ∀ p pre, part (C.loc p) = some pre → preAt δ Cδ (curOp β p) <+: pre ∧
    ∀ l : Fin n, (preAt δ Cδ (curOp β p)).length ≤ l → l.val < pre.length →
      diag Cδ l ≤ pre.getD l 0
  /-- the same for writes that have written after `δ` -/
  written : ∀ y t, g.wts y = some t → gδ.wts y = none → preAt δ Cδ y <+: t ∧
    ∀ l : Fin n, (preAt δ Cδ y).length ≤ l → diag Cδ l ≤ t.getD l 0
  /-- Lemma 27 for reads in progress started after `δ` -/
  reading : ∀ p i best, C.loc p = .rRead i best → ¬ Invoked δ (curOp β p) →
    ∀ k : Fin n, k.val < i.val → ¬ best.2 < (Cδ.mem k).2
  /-- Lemma 27 for reads started after `δ` -/
  read : ∀ x c, g.rcell x = some c → ¬ Invoked δ x → ∀ k, ¬ c.2 < (Cδ.mem k).2

variable {δ : List (Lbl V v₀ n)} {Cδ : Cfg V v₀ n}

lemma tq_base (hrun : (alg2 V v₀ n).run δ = some Cδ) :
    TQ δ Cδ (ghost δ) δ Cδ (ghost δ) := by
  have hI := inv_run hrun
  refine ⟨fun k => CwLe.refl _, fun _ _ h => h, fun _ _ h => h, fun p pre hp => ?_,
    fun y t h h' => (by rw [h] at h'; cases h'), fun p i best hp hn => ?_,
    fun x c h hn => absurd (hI.rcellInv x c h).1 hn⟩
  · rw [preAt_cur hp]
    exact ⟨List.prefix_refl _, fun l h1 h2 => by omega⟩
  · have := hI.loc p; rw [hp] at this
    exact absurd (Impl.run_pend_curOp hrun this.1).1 hn

section GstepLemmas

variable {α : List (Lbl V v₀ n)} {C : Cfg V v₀ n} {g : GS V n} {q : Fin n}

lemma gstep_wRead {v : V} {i : Fin n} {pre : List ℕ} (hq : C.loc q = .wRead v i pre) :
    gstep α C g (.tau q) = g := by
  have hb : batch α C g.ws (.tau q) = [] := batch_of_not_wWrite (C := C) (by simp [hq])
  simp [gstep, hb, wtsStep, rcellStep, hq]

lemma gstep_wWrite {v : V} {ts : List ℕ} (hq : C.loc q = .wWrite v ts) :
    gstep α C g (.tau q) =
      ⟨g.ws ++ batch α C g.ws (.tau q), Function.update g.wts (curOp α q) (some ts), g.rcell⟩ := by
  simp [gstep, wtsStep, rcellStep, hq]

lemma gstep_rRead {i : Fin n} {best : Cell V} (hq : C.loc q = .rRead i best) :
    gstep α C g (.tau q) = ⟨g.ws, g.wts,
      if Alg4.next i = none then Function.update g.rcell (curOp α q) (some (newBest best (C.mem i)))
      else g.rcell⟩ := by
  have hb : batch α C g.ws (.tau q) = [] := batch_of_not_wWrite (C := C) (by simp [hq])
  simp [gstep, hb, wtsStep, rcellStep, hq]

lemma act_ret_idle {l₀ l : Loc V n} {r : V} (h : act v₀ q l₀ = .ret r l) : l = .idle := by
  cases l₀ <;> simp [act] at h <;> exact h.2.symm

end GstepLemmas

lemma TQ.step {β : List (Lbl V v₀ n)} {C C' : Cfg V v₀ n} {g : GS V n}
    (hrunδ : (alg2 V v₀ n).run δ = some Cδ) (hδβ : δ <+: β)
    (hrun : (alg2 V v₀ n).run β = some C) (hT : TQ δ Cδ (ghost δ) β C g) (hI : Inv β C g)
    {ℓ : Lbl V v₀ n} (hs : (alg2 V v₀ n).step C ℓ = some C') :
    TQ δ Cδ (ghost δ) (β ++ [ℓ]) C' (gstep β C g ℓ) := by
  have hIδ := inv_run hrunδ
  have hnotδ : ∀ x, ¬ Invoked β x → ¬ Invoked δ x := by
    obtain ⟨γ, rfl⟩ := hδβ; exact fun x h h' => h h'.mono
  cases ℓ with
  | inv q o =>
    rw [gstep_inv]
    obtain ⟨hpn, -, hpend, hloc, hmem⟩ := Impl.step_inv hs
    have hlocq : ∀ p, p ≠ q → C'.loc p = C.loc p := fun p hp => by simp [hloc, hp]
    have hnew : ¬ Invoked β (curOp β q) := Impl.not_invoked_curOp_of_idle hrun hpn
    refine ⟨fun k => hmem ▸ hT.mem k, hT.wts, hT.rcell, fun p pre hp => ?_, hT.written,
      fun p i best hp hn => ?_, hT.read⟩
    · rw [curOp_append_inv]
      by_cases hpq : p = q
      · subst hpq
        simp only [hloc, Function.update_self, alg2] at hp
        cases o <;> simp [invoke, part] at hp
        subst hp
        rw [preAt_of_not_invoked hrunδ hIδ (hnotδ _ hnew)]
        exact ⟨List.prefix_refl _, fun l h1 h2 => by simp at h2⟩
      · rw [hlocq p hpq] at hp; exact hT.wip p pre hp
    · rw [curOp_append_inv] at hn
      by_cases hpq : p = q
      · subst hpq
        simp only [hloc, Function.update_self, alg2] at hp
        cases o <;> simp [invoke] at hp
        obtain ⟨rfl, -⟩ := hp
        intro k hk; simp at hk
      · rw [hlocq p hpq] at hp; exact hT.reading p i best hp hn
  | ret q r =>
    rw [gstep_ret]
    obtain ⟨-, -, hmem, l, hact, hloc⟩ := Impl.step_ret hs
    have hl : l = .idle := act_ret_idle hact
    subst hl
    have hlocq : ∀ p, p ≠ q → C'.loc p = C.loc p := fun p hp => by simp [hloc, hp]
    have hcurq : ∀ p, p ≠ q → curOp (β ++ [.ret q r]) p = curOp β p := fun p hp =>
      curOp_append_ret_of_ne β r (Ne.symm hp)
    refine ⟨fun k => hmem ▸ hT.mem k, hT.wts, hT.rcell, fun p pre hp => ?_, hT.written,
      fun p i best hp hn => ?_, hT.read⟩
    · by_cases hpq : p = q
      · subst hpq; simp [hloc, part] at hp
      · rw [hlocq p hpq] at hp; rw [hcurq p hpq]; exact hT.wip p pre hp
    · by_cases hpq : p = q
      · subst hpq; simp [hloc] at hp
      · rw [hlocq p hpq] at hp; rw [hcurq p hpq] at hn; exact hT.reading p i best hp hn
  | tau q =>
    cases hq : C.loc q with
    | wRead v i pre =>
      have hpq : C.pend q = some (.write v) ∧ pre.length = i.val := by
        have := hI.loc q; rw [hq] at this; exact this
      rw [WSL.step_wRead (by simp [hpq.1]) hq, Option.some.injEq] at hs
      subst hs
      rw [gstep_wRead hq]
      have hlocq : ∀ p, p ≠ q →
          Function.update C.loc q (wReadNext v i pre (rv C q i)) p = C.loc p :=
        fun p hp => by simp [hp]
      refine ⟨hT.mem, hT.wts, hT.rcell, fun p pre' hp => ?_, hT.written,
        fun p i' best hp hn => ?_, hT.read⟩
      · simp only [curOp_append_tau]
        by_cases hpq' : p = q
        · subst hpq'
          have hp' : pre' = pre ++ [rv C p i] := by
            simp only [Function.update_self, wReadNext] at hp
            split at hp <;> simpa [part] using hp.symm
          subst hp'
          obtain ⟨h1, h2⟩ := hT.wip p pre (by simp [hq, part])
          refine ⟨h1.trans (List.prefix_append _ _), fun l hl1 hl2 => ?_⟩
          simp only [length_append, length_singleton] at hl2
          rcases Nat.lt_or_ge l.val pre.length with hl' | hl'
          · rw [List.getD_append _ _ _ _ hl']; exact h2 l hl1 hl'
          · have hli : l = i := Fin.ext (by omega)
            subst hli
            rw [List.getD_append_right _ _ _ _ hl', show (l : ℕ) - pre.length = 0 by omega]
            simp only [getD_cons_zero, rv, diag]
            have := hT.mem l l; omega
        · simp only [hlocq p hpq'] at hp; exact hT.wip p pre' hp
      · by_cases hpq' : p = q
        · subst hpq'; simp only [Function.update_self, wReadNext] at hp; split at hp <;> cases hp
        · simp only [hlocq p hpq'] at hp; simp only [curOp_append_tau] at hn ⊢
          exact hT.reading p i' best hp hn
    | wWrite v ts =>
      have hpq : C.pend q = some (.write v) ∧ ts.length = n := by
        have := hI.loc q; rw [hq] at this; exact this
      rw [WSL.step_wWrite (by simp [hpq.1]) hq, Option.some.injEq] at hs
      subst hs
      rw [gstep_wWrite hq]
      have hwq : g.wts (curOp β q) = none := (hI.partOK q ts (by simp [hq, part])).2
      have hlocq : ∀ p, p ≠ q → Function.update C.loc q (.wRet v) p = C.loc p :=
        fun p hp => by simp [hp]
      refine ⟨fun k => ?_, fun x t h => ?_, hT.rcell, fun p pre hp => ?_,
        fun y t h h' => ?_, fun p i best hp hn => ?_, hT.read⟩
      · by_cases hk : k = q
        · subst hk; simp only [Function.update_self]
          exact (hT.mem k).trans (hI.cwLe_wWrite hq)
        · simp only [Function.update_of_ne hk]; exact hT.mem k
      · have h1 := hT.wts x t h
        have : x ≠ curOp β q := by rintro rfl; rw [hwq] at h1; cases h1
        simp [this, h1]
      · by_cases hpq' : p = q
        · subst hpq'; simp [part] at hp
        · simp only [hlocq p hpq'] at hp; simp only [curOp_append_tau]; exact hT.wip p pre hp
      · simp only at h
        by_cases hy : y = curOp β q
        · subst hy
          simp only [Function.update_self, Option.some.injEq] at h
          subst h
          obtain ⟨h1, h2⟩ := hT.wip q ts (by simp [hq, part])
          exact ⟨h1, fun l hl => h2 l hl (by rw [hpq.2]; exact l.isLt)⟩
        · rw [Function.update_of_ne hy] at h; exact hT.written y t h h'
      · by_cases hpq' : p = q
        · subst hpq'; simp at hp
        · simp only [hlocq p hpq'] at hp; simp only [curOp_append_tau] at hn ⊢
          exact hT.reading p i best hp hn
    | rRead i best =>
      have hpq : C.pend q = some .read ∧ best.2.length = n := by
        have := hI.loc q; rw [hq] at this; exact this
      rw [WSL.step_rRead (by simp [hpq.1]) hq, Option.some.injEq] at hs
      subst hs
      rw [gstep_rRead hq]
      have hrq : g.rcell (curOp β q) = none := (hI.rRead q i best hq).2
      have hlocq : ∀ p, p ≠ q →
          Function.update C.loc q (rReadNext i (newBest best (C.mem i))) p = C.loc p :=
        fun p hp => by simp [hp]
      -- the new best cell dominates the snapshot entries `0, …, i`
      have hnb : ¬ Invoked δ (curOp β q) → ∀ k : Fin n, k.val ≤ i.val →
          ¬ (newBest best (C.mem i)).2 < (Cδ.mem k).2 := by
        intro hn k hk
        rcases Nat.lt_or_ge k.val i.val with hk' | hk'
        · exact not_lt_trans (hT.reading q i best hq hn k hk') (newBest_ge_best _ _)
        · have hki : k = i := Fin.ext (by omega)
          subst hki
          exact not_lt_trans
            (not_lt_of_cwLe (by rw [hIδ.memLen, hI.memLen]) (hT.mem k)) (newBest_ge_c _ _)
      refine ⟨hT.mem, hT.wts, fun x c h => ?_, fun p pre hp => ?_, hT.written,
        fun p i' best' hp hn => ?_, fun x c h hn => ?_⟩
      · have h1 := hT.rcell x c h
        have : x ≠ curOp β q := by rintro rfl; rw [hrq] at h1; cases h1
        simp only; split_ifs <;> simp [this, h1]
      · by_cases hpq' : p = q
        · subst hpq'; simp only [Function.update_self, rReadNext] at hp
          split at hp <;> simp [part] at hp
        · simp only [hlocq p hpq'] at hp; simp only [curOp_append_tau]; exact hT.wip p pre hp
      · simp only [curOp_append_tau] at hn ⊢
        by_cases hpq' : p = q
        · subst hpq'
          simp only [Function.update_self, rReadNext] at hp
          split at hp
          · rename_i j hj
            cases hp
            intro k hk
            exact hnb hn k (by have := next_some hj; omega)
          · cases hp
        · simp only [hlocq p hpq'] at hp; exact hT.reading p i' best' hp hn
      · simp only at h
        by_cases hx : x = curOp β q
        · subst hx
          split_ifs at h with hj
          · simp only [Function.update_self, Option.some.injEq] at h
            subst h
            intro k
            exact hnb hn k (by have := next_none hj; have := k.isLt; omega)
          · rw [hrq] at h; cases h
        · have : (if Alg4.next i = none then
              Function.update g.rcell (curOp β q) (some (newBest best (C.mem i)))
              else g.rcell) x = g.rcell x := by split_ifs <;> simp [hx]
          rw [this] at h
          exact hT.read x c h hn
    | idle =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
      simp [alg2, hq, act] at hact
    | wRet v =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
      simp [alg2, hq, act] at hact
    | rRet v =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
      simp [alg2, hq, act] at hact

/-- **Temporal facts** between `δ` and any extension `δ ++ γ`. -/
theorem tq_run (hrunδ : (alg2 V v₀ n).run δ = some Cδ) {γ : List (Lbl V v₀ n)}
    {C : Cfg V v₀ n} (h : (alg2 V v₀ n).run (δ ++ γ) = some C) :
    TQ δ Cδ (ghost δ) (δ ++ γ) C (ghost (δ ++ γ)) := by
  induction γ using List.reverseRecOn generalizing C with
  | nil =>
    simp only [append_nil] at h ⊢
    rw [hrunδ, Option.some.injEq] at h; subst h; exact tq_base hrunδ
  | append_singleton γ ℓ ih =>
    rw [← append_assoc] at h ⊢
    rw [Impl.run_concat] at h
    cases h' : (alg2 V v₀ n).run (δ ++ γ) with
    | none => rw [h'] at h; cases h
    | some C₁ =>
      rw [h', Option.bind_some] at h
      rw [ghost_concat h']
      exact (ih h').step hrunδ (List.prefix_append _ _) h' (inv_run h') h

/-! ## Positions in the write sequence -/

lemma idxOf_lt_of_prefix {X : Type} [DecidableEq X] {l₁ l : List X} {a b : X}
    (h : l₁ <+: l) (ha : a ∈ l₁) (hb : b ∉ l₁) : l.idxOf a < l.idxOf b := by
  obtain ⟨r, rfl⟩ := h
  rw [List.idxOf_append_of_mem ha, List.idxOf_append_of_notMem hb]
  have := List.idxOf_lt_length_of_mem ha
  omega

lemma run_of_prefix {α δ : List (Lbl V v₀ n)} {C : Cfg V v₀ n}
    (h : (alg2 V v₀ n).run α = some C) (hp : δ <+: α) : ∃ Cδ, (alg2 V v₀ n).run δ = some Cδ :=
  (alg2 V v₀ n).valid_of_prefix ⟨C, h⟩ hp

/-- Every member of `WS` was appended in a batch at some step. -/
lemma exists_batch {α : List (Lbl V v₀ n)} {C : Cfg V v₀ n} (h : (alg2 V v₀ n).run α = some C)
    {x : OpId (Fin n)} (hx : x ∈ (ghost α).ws) :
    ∃ δ ℓ Cδ, δ ++ [ℓ] <+: α ∧ (alg2 V v₀ n).run δ = some Cδ ∧ x ∉ (ghost δ).ws ∧
      x ∈ batch δ Cδ (ghost δ).ws ℓ := by
  induction α using List.reverseRecOn generalizing C with
  | nil => simp [ghost₀] at hx
  | append_singleton α ℓ ih =>
    rw [Impl.run_concat] at h
    cases h' : (alg2 V v₀ n).run α with
    | none => rw [h'] at h; cases h
    | some C₁ =>
      rw [ghost_concat h'] at hx
      simp only [gstep, mem_append] at hx
      by_cases hx' : x ∈ (ghost α).ws
      · obtain ⟨δ, ℓ', Cδ, h1, h2, h3, h4⟩ := ih h' hx'
        exact ⟨δ, ℓ', Cδ, h1.trans (List.prefix_append _ _), h2, h3, h4⟩
      · exact ⟨α, ℓ, C₁, List.prefix_refl _, h', hx', hx.resolve_left hx'⟩

/-- A nonempty batch ends with the writer that triggered it. -/
lemma batch_eq {δ : List (Lbl V v₀ n)} {C : Cfg V v₀ n} {ws : List (OpId (Fin n))}
    {ℓ : Lbl V v₀ n} {x : OpId (Fin n)} (hx : x ∈ batch δ C ws ℓ) :
    ∃ k v ts L, ℓ = .tau k ∧ C.loc k = .wWrite v ts ∧ batch δ C ws ℓ = L ++ [curOp δ k] ∧
      curOp δ k ∉ L := by
  obtain ⟨k, v, ts, rfl, hk, hnin, -⟩ := mem_batch hx
  refine ⟨k, v, ts, _, rfl, hk, by rw [batch_wWrite hk, ite_eq_right_of_eq_false _ _ (eq_false hnin)], ?_⟩
  simp only [mem_map, mem_filter, mem_finRange, true_and, Bool.and_eq_true, decide_eq_true_eq,
    not_exists, not_and]
  intro p hp h; exact hp.1.1 (curOp_injective δ h)

/-- The state and ghost state right after a batch step. -/
lemma after_wWrite {δ : List (Lbl V v₀ n)} {Cδ C' : Cfg V v₀ n} {k : Fin n} {v : V}
    {ts : List ℕ} (hδ : (alg2 V v₀ n).run δ = some Cδ) (hk : Cδ.loc k = .wWrite v ts)
    (h' : (alg2 V v₀ n).run (δ ++ [.tau k]) = some C') :
    C'.mem k = (v, ts) ∧ C'.loc k = .wRet v ∧ (∀ p, p ≠ k → C'.loc p = Cδ.loc p) ∧
      (ghost (δ ++ [.tau k])).wts (curOp δ k) = some ts ∧
      (ghost (δ ++ [.tau k])).ws = (ghost δ).ws ++ batch δ Cδ (ghost δ).ws (.tau k) := by
  have hpq : Cδ.pend k = some (.write v) := by
    have := (inv_run hδ).loc k; rw [hk] at this; exact this.1
  rw [Impl.run_concat, hδ, Option.bind_some, WSL.step_wWrite (by simp [hpq]) hk,
    Option.some.injEq] at h'
  subst h'
  rw [ghost_concat hδ, gstep_wWrite hk]
  refine ⟨by simp, by simp, fun p hp => by simp [hp], by simp, rfl⟩

/-! ## Observation 36 and Lemma 38 -/

/-- **Observation 36** (with Observations 33–35): a write `x` of the batch `B_i` triggered by
`p_k` writing timestamp `ts` ends up with a timestamp `≤ ts`, and `< ts` unless `x` is the
trigger `w_i` itself. -/
lemma obs36 {α δ : List (Lbl V v₀ n)} {C Cδ : Cfg V v₀ n} (hα : (alg2 V v₀ n).run α = some C)
    (hδ : (alg2 V v₀ n).run δ = some Cδ) {k : Fin n} {v : V} {ts : List ℕ}
    (hk : Cδ.loc k = .wWrite v ts) (hpre : δ ++ [.tau k] <+: α) {x : OpId (Fin n)}
    (hx : x ∈ batch δ Cδ (ghost δ).ws (.tau k)) {tx : List ℕ}
    (htx : (ghost α).wts x = some tx) : ¬ ts < tx ∧ (x ≠ curOp δ k → tx < ts) := by
  obtain ⟨C', h'⟩ := run_of_prefix hα hpre
  obtain ⟨-, -, -, hwts', -⟩ := after_wWrite hδ hk h'
  obtain ⟨γ, rfl⟩ := hpre
  by_cases hxk : x = curOp δ k
  · subst hxk
    have := (tq_run h' hα).wts _ _ hwts'
    rw [this, Option.some.injEq] at htx; subst htx
    exact ⟨List.lt_irrefl _, fun h => absurd rfl h⟩
  · obtain ⟨k', v', ts', hℓ, hk', -, h1 | ⟨p, -, hb, -, rfl⟩⟩ := mem_batch hx
    · cases hℓ; exact absurd h1 hxk
    · cases hℓ
      rw [hk] at hk'; cases hk'
      obtain ⟨pre, hp, hlt⟩ := below_iff.1 hb
      have hIδ := inv_run hδ
      have hw0 : (ghost δ).wts (curOp δ p) = none := (hIδ.partOK p pre hp).2
      have hα' : (alg2 V v₀ n).run (δ ++ (.tau k :: γ)) = some C := by simpa using hα
      have htx' : (ghost (δ ++ (.tau k :: γ))).wts (curOp δ p) = some tx := by simpa using htx
      have hpx := ((tq_run hδ hα').written _ _ htx' hw0).1
      rw [preAt_cur hp] at hpx
      have htxl : tx.length = n := ((inv_run hα').wtsInv _ _ htx').2.1
      have htsl : ts.length = n := by have := hIδ.loc k; rw [hk] at this; exact this.2
      have hprel : pre.length ≤ n := (hIδ.partOK p pre hp).1.1
      have hlt' : tx < ts := lt_of_take_lt (m := pre.length) (by rw [htxl, htsl])
        (by omega) (by rw [← List.prefix_iff_eq_take.1 hpx]; exact hlt)
      exact ⟨List.lt_asymm hlt', fun _ => hlt'⟩

/-- **Lemma 38**: if `x ∈ B_i`, `y ∈ B_j` with `i < j` and both write, then `ts_x < ts_y`. -/
lemma lemma38 {α δ₁ δ₂ : List (Lbl V v₀ n)} {C C₁ C₂ : Cfg V v₀ n}
    (hα : (alg2 V v₀ n).run α = some C) (hδ₁ : (alg2 V v₀ n).run δ₁ = some C₁)
    (hδ₂ : (alg2 V v₀ n).run δ₂ = some C₂) {ℓ₁ ℓ₂ : Lbl V v₀ n} (h12 : δ₁ ++ [ℓ₁] <+: δ₂)
    (h2α : δ₂ ++ [ℓ₂] <+: α) {x y : OpId (Fin n)} (hx : x ∈ batch δ₁ C₁ (ghost δ₁).ws ℓ₁)
    (hy : y ∈ batch δ₂ C₂ (ghost δ₂).ws ℓ₂) {tx ty : List ℕ}
    (htx : (ghost α).wts x = some tx) (hty : (ghost α).wts y = some ty) : tx < ty := by
  obtain ⟨k, v, ts, rfl, hk, hkn, -⟩ := mem_batch hx
  have hpre1 : δ₁ ++ [.tau k] <+: α := h12.trans ((List.prefix_append δ₂ [ℓ₂]).trans h2α)
  obtain ⟨C', h'⟩ := run_of_prefix hα hpre1
  obtain ⟨hmemk, hlock, hloco, hwts', hws'⟩ := after_wWrite hδ₁ hk h'
  have h36 := (obs36 hα hδ₁ hk hpre1 hx htx).1
  have hyδ' : y ∉ (ghost (δ₁ ++ [.tau k])).ws := by
    obtain ⟨γ₂, rfl⟩ := h12
    exact fun h => batch_disjoint hy ((ghost_ws_prefix _ γ₂).subset h)
  have hyδ₁ : y ∉ (ghost δ₁).ws := fun h => hyδ' (by rw [hws']; exact mem_append_left _ h)
  have hI' := inv_run h'
  have hIα := inv_run hα
  have hwy : (ghost (δ₁ ++ [.tau k])).wts y = none := by
    cases h : (ghost (δ₁ ++ [.tau k])).wts y with
    | none => rfl
    | some t => exact absurd (hI'.wtsInv y t h).1 hyδ'
  obtain ⟨γ, rfl⟩ := hpre1
  have hT' := tq_run h' hα
  obtain ⟨hpy, hry⟩ := hT'.written y ty hty hwy
  -- Claim: the partial timestamp of `y` at `t_i` is not below `ts` (else `y ∈ B_i`)
  have hA : ¬ preAt (δ₁ ++ [.tau k]) C' y <
      ts.take (preAt (δ₁ ++ [.tau k]) C' y).length := by
    unfold preAt
    split_ifs with hcur
    · by_cases hyk : y.1 = k
      · rw [hyk, hlock]; exact List.not_lt_nil _
      · rw [hloco _ hyk]
        cases hp : part (C₁.loc y.1) with
        | none => exact List.not_lt_nil _
        | some pre =>
          simp only [Option.getD_some]
          intro hlt
          apply hyδ'
          rw [hws', batch_wWrite hk, ite_eq_right_of_eq_false _ _ (eq_false hkn)]
          apply mem_append_right; apply mem_append_left
          simp only [curOp_append_tau] at hcur
          simp only [mem_map, mem_filter, mem_finRange, true_and, Bool.and_eq_true,
            decide_eq_true_eq]
          exact ⟨y.1, ⟨⟨hyk, below_iff.2 ⟨pre, hp, hlt⟩⟩, hcur ▸ hyδ₁⟩, hcur⟩
    · exact List.not_lt_nil _
  have htyl : ty.length = n := (hIα.wtsInv _ _ hty).2.1
  have htsl : ts.length = n := by have := (inv_run hδ₁).loc k; rw [hk] at this; exact this.2
  have hm : (preAt (δ₁ ++ [.tau k]) C' y).length ≤ ty.length := hpy.length_le
  have hnlt : ¬ ty < ts := by
    refine not_lt_of_take_not_lt (m := (preAt (δ₁ ++ [.tau k]) C' y).length)
      (by rw [htyl, htsl]) hm (by rw [← List.prefix_iff_eq_take.1 hpy]; exact hA) ?_
    intro l hl
    rcases Nat.lt_or_ge l n with hl' | hl'
    · have h1 := hI'.memLe k ⟨l, hl'⟩
      rw [hmemk] at h1
      exact h1.trans (hry ⟨l, hl'⟩ hl)
    · rw [getD_eq_default _ _ (by omega)]; exact Nat.zero_le _
  have hne : ty ≠ ts := by
    rintro rfl
    have h1 := hT'.wts _ _ hwts'
    have := hIα.wtsInj _ _ _ hty h1
    exact hyδ' (this ▸ (hI'.wtsInv _ _ hwts').1)
  have hts_ty : ts < ty := by
    rcases Std.lt_trichotomy ts ty with h | h | h
    · exact h
    · exact absurd h.symm hne
    · exact absurd h hnlt
  rcases Std.lt_trichotomy tx ty with h | rfl | h
  · exact h
  · exact absurd hts_ty h36
  · exact absurd (List.lt_trans hts_ty h) h36

/-! ## Claim 42.1 -/

lemma tq_of_prefix {δ α : List (Lbl V v₀ n)} {Cδ C : Cfg V v₀ n}
    (hδ : (alg2 V v₀ n).run δ = some Cδ) (hα : (alg2 V v₀ n).run α = some C) (h : δ <+: α) :
    TQ δ Cδ (ghost δ) α C (ghost α) := by
  obtain ⟨γ, rfl⟩ := h; exact tq_run hδ hα

lemma init_lt {t : List ℕ} (ht : t.length = n) {j : ℕ} (hj : 1 ≤ t.getD j 0) :
    replicate n 0 < t := by
  rcases Std.lt_trichotomy (replicate n 0) t with h | h | h
  · exact h
  · subst h; simp at hj
  · exact absurd h (not_lt_of_cwLe (by simp [ht]) (fun l => by simp))

/-- **Lemma 27 and Claim 42.1** (core of Lemmas 42 and 44): if the write `w` has written by the
end of `β` and the read `y` starts after `β` and returns the cell `c`, then `c` has a timestamp
`≥ ts_w`, it was written by some `w₀`, and `w₀ = w` or `w` is before `w₀` in `WS`. -/
lemma core {α β : List (Lbl V v₀ n)} {C Cβ : Cfg V v₀ n} (hα : (alg2 V v₀ n).run α = some C)
    (hβ : (alg2 V v₀ n).run β = some Cβ) (hβα : β <+: α) {w : OpId (Fin n)} {t : List ℕ}
    (hw : (ghost β).wts w = some t) {y : OpId (Fin n)} {c : Cell V} (hy : ¬ Invoked β y)
    (hc : (ghost α).rcell y = some c) :
    ¬ c.2 < t ∧ ∃ w₀, (ghost α).wts w₀ = some c.2 ∧
      (w₀ = w ∨ (ghost α).ws.idxOf w < (ghost α).ws.idxOf w₀) := by
  have hT := tq_of_prefix hβ hα hβα
  have hIβ := inv_run hβ
  have hIα := inv_run hα
  obtain ⟨-, htl, htcw, ht1⟩ := hIβ.wtsInv w t hw
  have h1 : ¬ c.2 < t :=
    not_lt_trans (not_lt_of_cwLe (by rw [htl, hIβ.memLen]) htcw) (hT.read y c hc hy w.1)
  have hwα := hT.wts w t hw
  rcases (hIα.rcellInv y c hc).2.1 with hinit | ⟨w₀, -, hw₀⟩
  · subst hinit; exact absurd (init_lt htl ht1) h1
  refine ⟨h1, w₀, hw₀, ?_⟩
  by_cases heq : c.2 = t
  · rw [heq] at hw₀; exact Or.inl (hIα.wtsInj _ _ _ hw₀ hwα)
  right
  have htc : t < c.2 := by
    rcases Std.lt_trichotomy t c.2 with h | h | h
    · exact h
    · exact absurd h.symm heq
    · exact absurd h h1
  obtain ⟨δ₁, ℓ₁, C₁, hp₁, hr₁, hn₁, hb₁⟩ := exists_batch hα (hIα.wtsInv w t hwα).1
  obtain ⟨δ₂, ℓ₂, C₂, hp₂, hr₂, hn₂, hb₂⟩ := exists_batch hα (hIα.wtsInv w₀ _ hw₀).1
  have hp₁' : δ₁ <+: α := (List.prefix_append _ _).trans hp₁
  have hp₂' : δ₂ <+: α := (List.prefix_append _ _).trans hp₂
  rcases Nat.lt_trichotomy δ₁.length δ₂.length with hlt | hle | hgt
  · -- `w` was appended at an earlier step
    have h12 : δ₁ ++ [ℓ₁] <+: δ₂ := List.prefix_of_prefix_length_le hp₁ hp₂' (by simp; omega)
    have hwδ₂ : w ∈ (ghost δ₂).ws := by
      obtain ⟨γ, rfl⟩ := h12
      refine (ghost_ws_prefix _ γ).subset ?_
      rw [ghost_concat hr₁]; exact mem_append_right _ hb₁
    obtain ⟨γ, rfl⟩ := hp₂'
    exact idxOf_lt_of_prefix (ghost_ws_prefix _ _) hwδ₂ hn₂
  · -- the same batch: `w₀` is its trigger, and `w` comes before it
    have hδ : δ₁ = δ₂ :=
      (List.prefix_of_prefix_length_le hp₁' hp₂' hle.le).eq_of_length hle
    subst hδ
    have hℓ : ℓ₁ = ℓ₂ := by
      have := (List.prefix_of_prefix_length_le hp₁ hp₂ (by simp)).eq_of_length (by simp)
      simpa using this
    subst hℓ
    rw [hr₁, Option.some.injEq] at hr₂; subst hr₂
    obtain ⟨k, v, ts, L, rfl, hk, hB, hkL⟩ := batch_eq hb₁
    obtain ⟨C', h'⟩ := run_of_prefix hα hp₁
    obtain ⟨hmemk, -, -, -, hws'⟩ := after_wWrite hr₁ hk h'
    -- `y` starts after `t_i`
    have hδ'β : δ₁ ++ [.tau k] <+: β := by
      rcases Nat.lt_or_ge δ₁.length β.length with h | h
      · exact List.prefix_of_prefix_length_le hp₁ hβα (by simp; omega)
      · exfalso
        have hβδ : β <+: δ₁ := List.prefix_of_prefix_length_le hβα hp₁' h
        obtain ⟨γ, rfl⟩ := hβδ
        exact hn₁ ((ghost_ws_prefix β γ).subset (hIβ.wtsInv w t hw).1)
    have hy' : ¬ Invoked (δ₁ ++ [.tau k]) y := by
      obtain ⟨γ, rfl⟩ := hδ'β; exact fun h => hy h.mono
    have hT' := tq_of_prefix h' hα hp₁
    have h2 := hT'.read y c hc hy' k
    rw [hmemk] at h2
    have h36 := obs36 hα hr₁ hk hp₁ hb₂ hw₀
    have hw₀k : w₀ = curOp δ₁ k := by
      by_contra hne; exact h2 (h36.2 hne)
    subst hw₀k
    have hwne : w ≠ curOp δ₁ k := by
      rintro rfl; rw [hwα, Option.some.injEq] at hw₀; exact heq hw₀.symm
    rw [hB] at hb₁
    have hwL : w ∈ L := by
      rcases mem_append.1 hb₁ with h | h
      · exact h
      · simp at h; exact absurd h hwne
    have hpre : (ghost δ₁).ws ++ L <+: (ghost α).ws := by
      obtain ⟨γ, hγ⟩ := hp₁
      have := ghost_ws_prefix (δ₁ ++ [.tau k]) γ
      rw [hγ, hws', hB, ← append_assoc] at this
      exact (List.prefix_append _ _).trans this
    exact idxOf_lt_of_prefix hpre (mem_append_right _ hwL)
      (by rw [mem_append, not_or]; exact ⟨hn₂, hkL⟩)
  · -- `w₀` was appended at an earlier step: impossible by Lemma 38
    have h21 : δ₂ ++ [ℓ₂] <+: δ₁ := List.prefix_of_prefix_length_le hp₂ hp₁' (by simp; omega)
    exact absurd (lemma38 hα hr₂ hr₁ h21 hp₁ hb₂ hb₁ hw₀ hwα) (List.lt_asymm htc)

/-! ## The reads-from criterion -/

lemma rfOf_spec {α : List (Lbl V v₀ n)} {C : Cfg V v₀ n} {g : GS V n} (hI : Inv α C g)
    {x : OpId (Fin n)} {c : Cell V} (hc : g.rcell x = some c) :
    (rfOf g x = 0 ∧ c.1 = v₀ ∧ ∀ w, g.wts w ≠ some c.2) ∨
      ∃ w₀, g.wts w₀ = some c.2 ∧ opOf α w₀ = some (.write c.1) ∧
        rfOf g x = g.ws.idxOf w₀ + 1 := by
  rcases (hI.rcellInv x c hc).2.1 with hinit | ⟨w₀, hop, hw₀⟩
  · subst hinit
    have hno : ∀ w, g.wts w ≠ some (replicate n 0) := by
      intro w hw
      have := (hI.wtsInv w _ hw).2.2.2
      simp at this
    refine Or.inl ⟨?_, rfl, hno⟩
    have hf : g.ws.find? (fun y => decide (g.wts y = some (replicate n 0))) = none :=
      List.find?_eq_none.2 (fun y _ => by simpa using hno y)
    simp [rfOf, hc, hf]
  · right
    refine ⟨w₀, hw₀, hop, ?_⟩
    cases hf : g.ws.find? (fun y => decide (g.wts y = some c.2)) with
    | none =>
      exact absurd (by simpa using hw₀) (List.find?_eq_none.1 hf w₀ (hI.wtsInv w₀ _ hw₀).1)
    | some w' =>
      have hw' : g.wts w' = some c.2 := by simpa using List.find?_some hf
      have := hI.wtsInj _ _ _ hw' hw₀
      subst this
      simp [rfOf, hc, hf]

lemma opOf_of_completed {β γ : List (Lbl V v₀ n)} {C : Cfg V v₀ n}
    (h : (alg2 V v₀ n).run β = some C) {x : OpId (Fin n)} (hx : Completed β x) :
    opOf (β ++ γ) x = opOf β x :=
  opOf_append_of_invoked ((Impl.Valid.wellFormed _ ⟨C, h⟩).invoked_of_completed hx)

/-- A completed write of `β` has written `Val[-]`, so it has a timestamp. -/
lemma wts_of_completed {β γ : List (Lbl V v₀ n)} {C : Cfg V v₀ n}
    (h : (alg2 V v₀ n).run β = some C) {x : OpId (Fin n)} {v : V}
    (hop : opOf (β ++ γ) x = some (.write v)) (hx : Completed β x) :
    ∃ t, (ghost β).wts x = some t := by
  rw [opOf_of_completed h hx] at hop
  exact Option.ne_none_iff_exists'.1 ((inv_run h).complW x v hop hx)

/-- The ghost write sequence and reads-from map satisfy the MWMR reads-from criterion
(Lemmas 39, 41, 42–44 and 46 of the paper). -/
theorem readsFrom {α : List (Lbl V v₀ n)} {C : Cfg V v₀ n} (hα : (alg2 V v₀ n).run α = some C) :
    MWMRReadsFrom α (ghost α).ws (rfOf (ghost α)) := by
  have hI := inv_run hα
  refine ⟨Impl.Valid.wellFormed _ ⟨C, hα⟩, hI.wsNodup, fun x hx => (hI.wsInv x hx).2,
    fun x v h hc => ?_, hI.writeResp, fun x h hc => ?_, fun x h hc => ?_,
    fun i j hi hj hp => ?_, fun i hi x hx hcx hp => ?_, fun x i hi hx hcx hp => ?_,
    fun x y hx hcx hy hcy hp => ?_⟩
  · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 (hI.complW x v h hc)
    exact (hI.wtsInv x t ht).1
  · obtain ⟨c, hc', -⟩ := hI.complR x h hc
    rcases rfOf_spec hI hc' with ⟨h0, -⟩ | ⟨w₀, hw₀, -, h1⟩
    · omega
    · rw [h1]; exact List.idxOf_lt_length_of_mem (hI.wtsInv w₀ _ hw₀).1
  · obtain ⟨c, hc', hr⟩ := hI.complR x h hc
    rw [hr]
    rcases rfOf_spec hI hc' with ⟨h0, h1, -⟩ | ⟨w₀, hw₀, hop, h1⟩
    · rw [h0, h1]; rfl
    · rw [h1]
      simp [wsVal, List.getElem?_idxOf (hI.wtsInv w₀ _ hw₀).1, hop]
  · -- Lemma 39
    obtain ⟨β, γ, rfl, hcβ, hnβ⟩ := hp
    obtain ⟨Cβ, hβ⟩ := run_of_prefix hα (List.prefix_append β γ)
    have hIβ := inv_run hβ
    obtain ⟨v, hv⟩ := (hI.wsInv _ (getElem_mem hi)).2
    obtain ⟨t, ht⟩ := wts_of_completed hβ hv hcβ
    have h1 := idxOf_lt_of_prefix (ghost_ws_prefix β γ) (hIβ.wtsInv _ t ht).1
      (fun h => hnβ (hIβ.wsInv _ h).1)
    rwa [hI.wsNodup.idxOf_getElem, hI.wsNodup.idxOf_getElem] at h1
  · -- Corollary 43
    obtain ⟨β, γ, rfl, hcβ, hnβ⟩ := hp
    obtain ⟨Cβ, hβ⟩ := run_of_prefix hα (List.prefix_append β γ)
    obtain ⟨v, hv⟩ := (hI.wsInv _ (getElem_mem hi)).2
    obtain ⟨t, ht⟩ := wts_of_completed hβ hv hcβ
    obtain ⟨c, hc', -⟩ := hI.complR x hx hcx
    obtain ⟨-, w₀, hw₀, hord⟩ := core hα hβ (List.prefix_append β γ) ht hnβ hc'
    rcases rfOf_spec hI hc' with ⟨-, -, hno⟩ | ⟨w₁, hw₁, -, h1⟩
    · exact absurd hw₀ (hno w₀)
    · have := hI.wtsInj _ _ _ hw₁ hw₀
      subst this
      rw [h1]
      rcases hord with rfl | h
      · rw [hI.wsNodup.idxOf_getElem]; omega
      · rw [hI.wsNodup.idxOf_getElem] at h; omega
  · -- Lemma 41
    obtain ⟨β, γ, rfl, hcβ, hnβ⟩ := hp
    obtain ⟨Cβ, hβ⟩ := run_of_prefix hα (List.prefix_append β γ)
    have hIβ := inv_run hβ
    rw [opOf_of_completed hβ hcβ] at hx
    obtain ⟨c, hcβ', -⟩ := hIβ.complR x hx hcβ
    have hc' := (tq_of_prefix hβ hα (List.prefix_append β γ)).rcell x c hcβ'
    rcases rfOf_spec hI hc' with ⟨h0, -⟩ | ⟨w₀, hw₀, -, h1⟩
    · omega
    · rw [h1]
      rcases (hIβ.rcellInv x c hcβ').2.1 with hinit | ⟨w, -, hw⟩
      · subst hinit; have := (hI.wtsInv w₀ _ hw₀).2.2.2; simp at this
      · have := hI.wtsInj _ _ _ ((tq_of_prefix hβ hα (List.prefix_append β γ)).wts _ _ hw) hw₀
        subst this
        have h2 := idxOf_lt_of_prefix (ghost_ws_prefix β γ) (hIβ.wtsInv _ _ hw).1
          (fun h => hnβ (hIβ.wsInv _ h).1)
        rw [hI.wsNodup.idxOf_getElem] at h2; omega
  · -- Lemma 44
    obtain ⟨β, γ, rfl, hcβ, hnβ⟩ := hp
    obtain ⟨Cβ, hβ⟩ := run_of_prefix hα (List.prefix_append β γ)
    have hIβ := inv_run hβ
    have hT := tq_of_prefix hβ hα (List.prefix_append β γ)
    rw [opOf_of_completed hβ hcβ] at hx
    obtain ⟨c, hcβ', -⟩ := hIβ.complR x hx hcβ
    have hc' := hT.rcell x c hcβ'
    rcases rfOf_spec hI hc' with ⟨h0, -⟩ | ⟨w₀, hw₀, -, h1⟩
    · omega
    · rw [h1]
      rcases (hIβ.rcellInv x c hcβ').2.1 with hinit | ⟨w, -, hw⟩
      · subst hinit; have := (hI.wtsInv w₀ _ hw₀).2.2.2; simp at this
      · have := hI.wtsInj _ _ _ (hT.wts _ _ hw) hw₀
        subst this
        obtain ⟨d, hd, -⟩ := hI.complR y hy hcy
        obtain ⟨-, w₁, hw₁, hord⟩ := core hα hβ (List.prefix_append β γ) hw hnβ hd
        rcases rfOf_spec hI hd with ⟨-, -, hno⟩ | ⟨w₂, hw₂, -, h2⟩
        · exact absurd hw₁ (hno w₁)
        · have := hI.wtsInj _ _ _ hw₂ hw₁
          subst this
          rw [h2]
          rcases hord with rfl | h
          · exact le_rfl
          · omega

end WSL

open WSL in
/-- **Theorem 10** (Hadzilacos–Hu–Toueg, PODC 2021). Algorithm 2 is a write strongly-linearizable
implementation of a MWMR register from SWMR registers: the function
`α ↦ mwmrLin α WS(α) rf_α`, with the on-line write sequence `WS` of Algorithm 3, is a
linearization function whose sequence of writes on a prefix of an execution is a prefix of its
sequence of writes on the execution. -/
theorem alg2_writeStronglyLinearizable (V : Type) (v₀ : V) (n : ℕ) [NeZero n] :
    (alg2 V v₀ n).WriteStronglyLinearizable := by
  refine ⟨fun α => mwmrLin α (ghost α).ws (rfOf (ghost α)),
    fun α ⟨C, hC⟩ => (readsFrom hC).isLinearization, fun α β hβ hαβ => ?_⟩
  obtain ⟨C, hC⟩ := hβ
  obtain ⟨Cα, hCα⟩ := run_of_prefix hC hαβ
  have hIα := inv_run hCα
  simp only [opsFor_mwmrLin]
  obtain ⟨γ, rfl⟩ := hαβ
  obtain ⟨T, hT⟩ := ghost_ws_prefix α γ
  rw [← hT, filter_append, map_append]
  have hop : ∀ x ∈ (ghost α).ws, opOrRead (α ++ γ) x = opOrRead α x := fun x hx => by
    simp [opOrRead, opOf_append_of_invoked (hIα.wsInv x hx).1]
  have e : ((ghost α).ws.filter (fun x => (opOrRead (α ++ γ) x).isWrite)).map
        (fun x => (x, opOrRead (α ++ γ) x)) =
      ((ghost α).ws.filter (fun x => (opOrRead α x).isWrite)).map (fun x => (x, opOrRead α x)) := by
    rw [List.filter_congr (fun x hx => by rw [hop x hx])]
    exact List.map_congr_left (fun x hx => by rw [hop x (List.mem_filter.1 hx).1])
  rw [e]
  exact List.prefix_append _ _

end Podc.RegisterLinTermination.Alg2
