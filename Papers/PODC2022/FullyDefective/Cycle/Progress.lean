import Papers.PODC2022.FullyDefective.Cycle.Invariant

/-!
# Lemma 5(1) of [CCGS22]: progress of Algorithm 1 (ring layer)

* `cdist T x`: position of `x` counterclockwise from `T` (`1, …, n`, with `T` itself at `n`).
* `Inv2`: two further invariants needed for progress. If some node has sent its `request` pulse
  of the current token phase, some queue is non-empty (`origin`); and the `token` pulse, once
  released by `T`, has not passed some node with a non-empty queue (`token`) — so it is caught
  after at most `n` hops (the paper: "a node `v` with a non-empty `Q_v`, which must exist").
* `Inv.enabled_or_quiet`: deadlock freedom — in every reachable configuration some step of the
  ring layer is enabled, unless the ring is quiet (every node idle at line 1 with an empty queue,
  no pulse in transit).
* `rank`, `μ`: every step of the ring layer either moves the system to a later stage
  (`rank` increases: token stage → data stage → end stage → next token stage) or strictly
  decreases the potential `μ` (`progress_step`); pushes change neither.
-/

namespace Podc.FullyDefective.Cycle

variable {n : ℕ} [NeZero n]

/-! ### Counterclockwise positions -/

/-- The position of `x` counterclockwise from `T`: `T - 1` is at `1`, `T - 2` at `2`, …,
`T` itself at `n`. -/
def cdist (T x : ZMod n) : ℕ := if x = T then n else (T - x).val

lemma cdist_pos (T x : ZMod n) : 1 ≤ cdist T x := by
  unfold cdist; split_ifs with h
  · exact Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  · rw [Nat.one_le_iff_ne_zero, Ne, ZMod.val_eq_zero, sub_eq_zero]; exact fun h' => h h'.symm

lemma cdist_le (T x : ZMod n) : cdist T x ≤ n := by
  unfold cdist; split_ifs
  · exact le_rfl
  · exact (ZMod.val_lt _).le

lemma cdist_self (T : ZMod n) : cdist T T = n := by simp [cdist]

lemma cdist_injective (T : ZMod n) : Function.Injective (cdist T) := by
  intro x y h
  unfold cdist at h
  split_ifs at h with hx hy hy
  · rw [hx, hy]
  · have := ZMod.val_lt (T - y); omega
  · have := ZMod.val_lt (T - x); omega
  · have := ZMod.val_injective n h
    calc x = T - (T - x) := by ring
      _ = T - (T - y) := by rw [this]
      _ = y := by ring

lemma subsingleton_of_one (h : n = 1) (x y : ZMod n) : x = y := by
  subst h; exact Subsingleton.elim x y

lemma cdist_sub_one {T x : ZMod n} (hx : x ≠ T) : cdist T (x - 1) = cdist T x + 1 := by
  have hn : n ≠ 1 := fun h => hx (subsingleton_of_one h x T)
  have hn2 : 1 < n := by have := NeZero.ne n; omega
  have hone : (1 : ZMod n).val = 1 := by
    haveI : Fact (1 < n) := ⟨hn2⟩; exact ZMod.val_one n
  have key : T - (x - 1) = (T - x) + 1 := by ring
  have hlt := ZMod.val_lt (T - x)
  unfold cdist
  rw [if_neg hx]
  split_ifs with h1
  · -- `x - 1 = T`: then `T - x = -1`
    have h2 : (T - x) + 1 = 0 := by rw [← key, h1, sub_self]
    have h3 := ZMod.val_add (T - x) 1
    rw [h2, ZMod.val_zero, hone] at h3
    have : (T - x).val + 1 = n := by
      rcases Nat.lt_or_ge ((T - x).val + 1) n with h | h
      · rw [Nat.mod_eq_of_lt h] at h3; omega
      · omega
    omega
  · rw [key, ZMod.val_add, hone]
    have h4 : (T - x).val + 1 ≠ n := by
      intro h4
      apply h1
      have : (T - x) + 1 = 0 := by
        rw [← ZMod.val_eq_zero, ZMod.val_add, hone, h4, Nat.mod_self]
      calc x - 1 = T - ((T - x) + 1) := by ring
        _ = T := by rw [this, sub_zero]
    exact Nat.mod_eq_of_lt (by omega)

lemma cdist_sub_one_self (T : ZMod n) : cdist T (T - 1) = 1 := by
  by_cases hn : n = 1
  · have : T - 1 = T := subsingleton_of_one hn _ _
    rw [this, cdist_self, hn]
  · have hn2 : 1 < n := by have := NeZero.ne n; omega
    haveI : Fact (1 < n) := ⟨hn2⟩
    have h : T - 1 ≠ T := by
      intro h; have : (1 : ZMod n) = 0 := by
        calc (1 : ZMod n) = T - (T - 1) := by ring
          _ = 0 := by rw [h, sub_self]
      exact one_ne_zero this
    simp [cdist, h, ZMod.val_one]

/-! ### Stage lemmas -/

variable {c : Config n}

lemma Inv.tokStage_iff (h : Inv c) : TokStage c ↔ (c.node c.hold).ph.IsTok := by
  rcases h.2 with ⟨pre, d, r, H⟩ | ⟨pre, d, H⟩ | H
  · rw [H.ph_hold]; simp only [Phase.IsTok, iff_false]
    intro H'; have := H'.isTok c.hold; rw [H.ph_hold] at this; exact this
  · rw [H.ph_hold]; simp only [Phase.IsTok, iff_false]
    intro H'; have := H'.isTok c.hold; rw [H.ph_hold] at this; exact this
  · exact ⟨fun _ => H.isTok _, fun _ => H⟩

lemma base_lt_base {ds : List ℕ} {e e' : ℕ} (h : e < e') (h' : e' ≤ ds.length) :
    base ds e < base ds e' := by
  unfold base
  rw [← List.take_append_drop e (ds.take e'), List.take_take, min_eq_left h.le, List.map_append,
    List.sum_append]
  have : (List.drop e (List.take e' ds)) ≠ [] := by
    simp only [ne_eq, List.drop_eq_nil_iff, List.length_take]; omega
  obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil this
  rw [hal]; simp

/-- A node that has sent its `request` pulse of the current token phase (`waitReq` or `ready`
after completing all started epochs). -/
def ReqSent (c : Config n) : Prop :=
  ∃ u, ((c.node u).ph = .waitReq ∨ (c.node u).ph = .ready) ∧ c.ep u = c.ds.length

/-- If `u` has completed all epochs and a clockwise pulse is in transit to it, its predecessor
has sent its `request` pulse. -/
lemma Inv.reqSent_of_cwIn (h : Inv c) {u : ZMod n} (hu : c.ep u = c.ds.length)
    (hph : (c.node u).ph = .idle) (hin : c.cwIn u) : ReqSent c := by
  obtain ⟨hC, hS⟩ := h
  have hR := hC.cwR u; rw [hu, hph] at hR; simp only [Phase.rOff, add_zero] at hR
  have hS1 := hC.cwS (u - 1)
  simp only [Config.cwIn] at hin
  refine ⟨u - 1, ?_⟩
  rcases hS with ⟨pre, d, r, H⟩ | ⟨pre, d, H⟩ | H
  · exfalso
    have := hC.ep_le u; rw [H.ds_eq] at hu this; simp at hu
    by_cases hT : u = c.hold
    · rw [hT, H.ep_hold] at hu; omega
    · rw [(H.others u hT).1] at hu; omega
  · have hlen : c.ds.length = pre.length + 1 := by rw [H.ds_eq]; simp
    have hb := base_ds H.ds_eq
    by_cases h1 : u - 1 = c.hold
    · exfalso
      have h2 := hC.cwS c.hold; rw [H.ep_hold, H.ph_hold] at h2; simp only [Phase.sOff] at h2
      rw [h1] at hin; rw [hlen] at hR; omega
    · rcases H.others _ h1 with ⟨he, hp⟩ | ⟨he, hp⟩
      · exfalso; rw [he, hp] at hS1; simp only [Phase.sOff] at hS1; rw [hlen] at hR; omega
      · rw [he] at hS1; rw [hlen] at hR
        refine ⟨?_, by rw [he, hlen]⟩
        revert hp hS1; cases (c.node (u - 1)).ph <;> simp [Phase.IsTok, Phase.sOff] <;> omega
  · have he := H.ep_all (u - 1)
    rw [he] at hS1
    refine ⟨?_, he⟩
    have hp := H.isTok (u - 1)
    revert hp hS1; cases (c.node (u - 1)).ph <;> simp [Phase.IsTok, Phase.sOff] <;> omega

/-- Further invariants for progress. -/
structure Inv2 (c : Config n) : Prop where
  /-- A `request` pulse of the current token phase was initiated by a node with a non-empty
  queue, which still holds its messages. -/
  origin : ReqSent c → ∃ w, (c.node w).q ≠ []
  /-- The released `token` pulse has not passed some node with a non-empty queue. -/
  token : TokStage c → (c.node c.hold).tok = false →
    ∃ p, c.ccwIn p ∧ ∃ w, (c.node w).q ≠ [] ∧ cdist c.hold p ≤ cdist c.hold w

lemma inv2_init (T₀ : ZMod n) (qs : ZMod n → List ℕ) : Inv2 (init T₀ qs) := by
  refine ⟨fun ⟨u, hu, _⟩ => ?_, fun _ ht => ?_⟩
  · simp [init] at hu
  · simp [init] at ht

lemma inv2_push (h2 : Inv2 c) (u : ZMod n) (a : ℕ) : Inv2 (next c (.push u a)) := by
  have hq : ∀ w, (c.node w).q ≠ [] → ((next c (.push u a)).node w).q ≠ [] := by
    intro w hw; by_cases hwu : w = u
    · subst hwu; simp
    · simpa [hwu] using hw
  have hn : ∀ v, ((next c (.push u a)).node v).ph = (c.node v).ph ∧
      ((next c (.push u a)).node v).tok = (c.node v).tok ∧
      ((next c (.push u a)).node v).log = (c.node v).log := by
    intro v; by_cases hv : v = u <;> simp [hv]
  have hep : ∀ v, (next c (.push u a)).ep v = c.ep v := fun v => by rw [Config.ep, (hn v).2.2]
  have hc : (next c (.push u a)).ccwIn = c.ccwIn := rfl
  refine ⟨fun ⟨v, hv, he⟩ => ?_, fun H ht => ?_⟩
  · rw [(hn v).1] at hv; rw [hep] at he
    obtain ⟨w, hw⟩ := h2.origin ⟨v, hv, he⟩; exact ⟨w, hq w hw⟩
  · have H' : TokStage c := ⟨fun v => by rw [← hep]; exact H.ep_all v,
      fun v => by rw [← (hn v).1]; exact H.isTok v,
      fun h' => by rw [← hc]; exact H.held (by rw [(hn _).2.1]; exact h'),
      fun h' => by rw [← hc]; exact H.released (by rw [(hn _).2.1]; exact h')⟩
    rw [(hn _).2.1] at ht
    obtain ⟨p, hp, w, hw, hd⟩ := h2.token H' ht
    exact ⟨p, hp, w, hq w hw, hd⟩

lemma inv2_start (h : Inv c) (h2 : Inv2 c) {u : ZMod n} (hen : Enabled c (.start u)) :
    Inv2 (next c (.start u)) := by
  obtain ⟨hidle, hqu⟩ := hen
  have hq : ∀ w, ((next c (.start u)).node w).q = (c.node w).q := by
    intro w; by_cases hwu : w = u <;> simp [hwu]
  have hh : (next c (.start u)).hold = c.hold := rfl
  refine ⟨fun _ => ⟨u, by rw [hq]; exact hqu⟩, fun H ht => ?_⟩
  have h' := inv_start h hidle
  have hTok : TokStage c := by
    rw [h.tokStage_iff]; rw [h'.tokStage_iff, hh] at H
    by_cases hTu : c.hold = u
    · rw [hTu, hidle]; trivial
    · simpa [hTu] using H
  have htok : (c.node c.hold).tok = false := by
    rw [hh] at ht; by_cases hTu : c.hold = u
    · simpa [hTu] using ht
    · simpa [hTu] using ht
  obtain ⟨p, hp, w, hw, hd⟩ := h2.token hTok htok
  exact ⟨p, hp, w, by rw [hq]; exact hw, hd⟩

lemma inv2_cw (h : Inv c) (h2 : Inv2 c) {u : ZMod n} (hen : Enabled c (.cw u)) :
    Inv2 (next c (.cw u)) := by
  have h' := inv_cw h hen
  obtain ⟨hr, hin⟩ := hen
  set c' := next c (.cw u)
  have hq : ∀ w, (c'.node w).q = (c.node w).q := by
    intro w; by_cases hwu : w = u <;> simp [c', hwu]
  have hep : ∀ v, c'.ep v = c.ep v := fun v => cw_ep v
  have hds : c'.ds = c.ds := rfl
  have hh : c'.hold = c.hold := rfl
  have hnode : ∀ v, v ≠ u → c'.node v = c.node v := fun v hv => cw_node_ne hv
  -- request origin
  have horig : ReqSent c' → ReqSent c := by
    rintro ⟨v, hv, he⟩
    rw [hep, hds] at he
    by_cases hvu : v = u
    · subst hvu
      have hv' := hv
      simp only [c', next_cw_node, ↓reduceIte] at hv'
      rcases hs : (c.node v).ph with _ | _ | _ | k | ⟨d, r⟩ | d
      · exact h.reqSent_of_cwIn he hs hin
      · exact ⟨v, Or.inl hs, he⟩
      · simp [onCW, hs] at hv'
      · simp [onCW, hs] at hv'
      · simp only [onCW, hs] at hv'; split_ifs at hv' <;> simp at hv'
      · simp [Phase.cwReady, hs] at hr
    · rw [hnode v hvu] at hv; exact ⟨v, hv, he⟩
  refine ⟨fun hR => ?_, fun H ht => ?_⟩
  · obtain ⟨w, hw⟩ := h2.origin (horig hR); exact ⟨w, by rw [hq]; exact hw⟩
  · -- the token stage before the step
    have hTok : TokStage c := by
      rw [h.tokStage_iff]; rw [h'.tokStage_iff, hh] at H
      by_cases hTu : c.hold = u
      · rw [hTu] at H ⊢
        simp only [c', next_cw_node, ↓reduceIte] at H
        rcases hs : (c.node u).ph with _ | _ | _ | k | ⟨d, r⟩ | d <;>
          simp only [onCW, hs] at H <;> simp [Phase.IsTok] at H ⊢
        split_ifs at H <;> exact H
      · rwa [hnode _ hTu] at H
    rw [hh] at ht
    cases htok : (c.node c.hold).tok
    · obtain ⟨p, hp, w, hw, hd⟩ := h2.token hTok htok
      exact ⟨p, cw_ccwIn_of hp, w, by rw [hq]; exact hw, hd⟩
    · -- the token is released now, by `T = u`
      have hTu : c.hold = u := by
        by_contra hTu; rw [hnode _ hTu, htok] at ht; cases ht
      have hph : (c.node u).ph = .idle ∨ (c.node u).ph = .waitReq := by
        have h1 := hTok.isTok u
        have h2 := ((h.1.tok u).1 (hTu ▸ htok)).2
        revert h1 h2; rcases (c.node u).ph <;> simp [Phase.IsTok, Phase.Holding]
      have hRS : ReqSent c := by
        rcases hph with hp | hp
        · exact h.reqSent_of_cwIn (hTok.ep_all u) hp hin
        · exact ⟨u, Or.inl hp, hTok.ep_all u⟩
      obtain ⟨w, hw⟩ := h2.origin hRS
      refine ⟨c.hold - 1, ?_, w, by rw [hq]; exact hw, ?_⟩
      · have h1 : (onCW (c.node u)).2.2 = 1 := by
          rw [← hTu] at hph ⊢; rcases hph with hp | hp <;> simp [onCW, hp, htok]
        simp only [Config.ccwIn, c', next_cw_ccwS, next_cw_ccwR, sub_add_cancel, hTu,
          ↓reduceIte, h1]
        have h4 := h.1.ccwChan (u - 1); simp only [sub_add_cancel] at h4; omega
      · rw [hh, cdist_sub_one_self]; exact cdist_pos _ _

lemma inv2_ccw (h : Inv c) (h2 : Inv2 c) {u : ZMod n} (hen : Enabled c (.ccw u)) :
    Inv2 (next c (.ccw u)) := by
  have h' := inv_ccw h hen
  obtain ⟨hr, hin⟩ := hen
  set c' := next c (.ccw u)
  have hnode : ∀ v, v ≠ u → c'.node v = c.node v := fun v hv => ccw_node_ne hv
  by_cases hcap : ∃ a, capture? (c.node u) = some a
  · -- a capture: the new stage is a data stage, where both clauses are vacuous
    obtain ⟨a, ha⟩ := hcap
    have hph : (c.node u).ph = .ready := by
      unfold capture? at ha; split at ha
      · assumption
      · cases ha
    have hq : (c.node u).q ≠ [] := by
      unfold capture? at ha; split at ha
      · simp_all
      · cases ha
    have hds : c'.ds = c.ds ++ [a] := by simp only [c', next_ccw_ds, ha]
    have hh : c'.hold = u := by simp only [c', next_ccw_hold, ha]
    have hphu : (c'.node u).ph = .send a 0 := by
      obtain ⟨a', q', hq'⟩ : ∃ a' q', (c.node u).q = a' :: q' := by
        cases hq' : (c.node u).q with
        | nil => exact absurd hq' hq
        | cons a' q' => exact ⟨a', q', rfl⟩
      have : a' = a := by unfold capture? at ha; rw [hph, hq'] at ha; simpa using ha
      simp [c', onCCW, hph, hq', this]
    have hnot : ¬ TokStage c' := by
      rw [h'.tokStage_iff, hh, hphu]; simp [Phase.IsTok]
    refine ⟨fun ⟨v, hv, he⟩ => ?_, fun H _ => absurd H hnot⟩
    exfalso
    rw [hds] at he
    rcases h'.2 with ⟨pre, d, r, H⟩ | ⟨pre, d, H⟩ | H
    · have hl := congrArg List.length H.ds_eq; rw [hds] at hl; simp at hl
      by_cases hvT : v = c'.hold
      · have := H.ep_hold; rw [← hvT] at this; simp at he; omega
      · have := (H.others v hvT).1; simp at he; omega
    · have := H.ph_hold; rw [hh, hphu] at this; cases this
    · have := H.isTok u; rw [hphu] at this; exact this
  · -- no capture: queues, `ds` and `hold` are unchanged
    have hcap' : capture? (c.node u) = none := by
      cases hc : capture? (c.node u) with
      | none => rfl
      | some a => exact absurd ⟨a, hc⟩ hcap
    have hds : c'.ds = c.ds := by simp only [c', next_ccw_ds, hcap']
    have hh : c'.hold = c.hold := by simp only [c', next_ccw_hold, hcap']
    have hqu : (onCCW (c.node u)).1.q = (c.node u).q := by
      rcases hs : (c.node u).ph <;> simp [onCCW, hs]
      cases hq : (c.node u).q
      · simp [hq]
      · simp [capture?, hs, hq] at hcap'
    have hq : ∀ w, (c'.node w).q = (c.node w).q := by
      intro w; by_cases hwu : w = u
      · subst hwu; simp [c', hqu]
      · rw [hnode w hwu]
    refine ⟨fun ⟨v, hv, he⟩ => ?_, fun H ht => ?_⟩
    · rw [hds] at he
      have hRS : ReqSent c := by
        by_cases hvu : v = u
        · subst hvu
          have hv' := hv; simp only [c', next_ccw_node, ↓reduceIte] at hv'
          have he' := he; simp only [c', Config.ep, next_ccw_node, ↓reduceIte] at he'
          rcases hs : (c.node v).ph with _ | _ | _ | k | ⟨d, r⟩ | d
          · simp [Phase.ccwReady, hs] at hr
          · simp [Phase.ccwReady, hs] at hr
          · have hqe : (c.node v).q = [] := by
              cases hq : (c.node v).q
              · rfl
              · simp [capture?, hs, hq] at hcap'
            have ho : onCCW (c.node v) = (c.node v, 0, 1) := by simp [onCCW, hs, hqe]
            rw [ho] at he'; exact ⟨v, Or.inr hs, he'⟩
          · simp [onCCW, hs] at hv'
          · simp [Phase.ccwReady, hs] at hr
          · simp [onCCW, hs] at hv'
        · rw [hnode v hvu] at hv; refine ⟨v, hv, ?_⟩; rwa [Config.ep, ← hnode v hvu]
      obtain ⟨w, hw⟩ := h2.origin hRS; exact ⟨w, by rw [hq]; exact hw⟩
    · -- only a forwarded `token` keeps the token stage
      rw [h'.tokStage_iff, hh] at H
      rcases h.2 with ⟨pre, d, r, H0⟩ | ⟨pre, d, H0⟩ | H0
      · exact absurd hin (H0.noIn u)
      · exfalso
        by_cases hTu : c.hold = u
        · -- the `end` pulse is back: the holder keeps its token
          have ho : (onCCW (c.node u)).1.tok = (c.node u).tok := by
            rw [← hTu]; simp [onCCW, H0.ph_hold]
          have ht' : (c'.node u).tok = false := by rw [← hTu, ← hh]; exact ht
          simp only [c', next_ccw_node, ↓reduceIte, ho] at ht'
          have := (h.1.tok c.hold).2 ⟨rfl, by rw [H0.ph_hold]; trivial⟩
          rw [hTu] at this; rw [this] at ht'; cases ht'
        · rw [hnode _ hTu, H0.ph_hold] at H; exact H
      · have hphu : (c.node u).ph = .ready := by
          have := H0.isTok u; revert this hr
          rcases (c.node u).ph <;> simp [Phase.IsTok, Phase.ccwReady]
        have hqe : (c.node u).q = [] := by
          cases hq : (c.node u).q
          · rfl
          · simp [capture?, hphu, hq] at hcap'
        have htokT : (c.node c.hold).tok = false := by
          cases ht' : (c.node c.hold).tok
          · rfl
          · exact absurd hin (H0.held ht' u)
        obtain ⟨p, hp, w, hw, hd⟩ := h2.token H0 htokT
        have hpu : p = u := h.1.ccwUniq p u hp hin
        subst hpu
        have hwp : w ≠ p := by rintro rfl; exact hw hqe
        have hlt : cdist c.hold p < cdist c.hold w :=
          lt_of_le_of_ne hd (fun e => hwp (cdist_injective _ e).symm)
        have hpT : p ≠ c.hold := by
          rintro rfl; have := cdist_le c.hold w; rw [cdist_self] at hlt; omega
        have h1 : (onCCW (c.node p)).2.2 = 1 := by simp [onCCW, hphu, hqe]
        refine ⟨p - 1, ccw_send_in h.1 hin h1, w, by rw [hq]; exact hw, ?_⟩
        rw [hh, cdist_sub_one hpT]; omega

theorem inv2_step (h : Inv c) (h2 : Inv2 c) {l : Label n} (hen : Enabled c l) :
    Inv2 (next c l) := by
  cases l with
  | push u a => exact inv2_push h2 u a
  | start u => exact inv2_start h h2 hen
  | cw u => exact inv2_cw h h2 hen
  | ccw u => exact inv2_ccw h h2 hen

theorem Reach.inv2 {T₀ : ZMod n} {qs : ZMod n → List ℕ} (hqs : ∀ u, ∀ a ∈ qs u, 0 < a)
    (h : Reach T₀ qs c) : Inv c ∧ Inv2 c := by
  induction h with
  | refl => exact ⟨inv_init T₀ hqs, inv2_init T₀ qs⟩
  | tail _ hs ih =>
    obtain ⟨l, hen, rfl⟩ := hs
    exact ⟨inv_step ih.1 hen, inv2_step ih.1 ih.2 hen⟩

/-! ### Deadlock freedom -/

/-- The ring layer is quiet: every node idles at line 1 with an empty queue, after completing all
started epochs, and no pulse is in transit. Nothing happens until a new message is pushed. -/
structure Quiet (c : Config n) : Prop where
  tok : TokStage c
  idle : ∀ u, (c.node u).ph = .idle
  empty : ∀ u, (c.node u).q = []
  noCw : ∀ u, ¬ c.cwIn u
  noCcw : ∀ u, ¬ c.ccwIn u

/-- **Deadlock freedom.** In every configuration satisfying the invariant, some step of the ring
layer (other than a push) is enabled, unless the ring layer is quiet. -/
theorem Inv.enabled_or_quiet (h : Inv c) :
    (∃ l, (∀ u a, l ≠ .push u a) ∧ Enabled c l) ∨ Quiet c := by
  by_contra hcon
  simp only [not_or, not_exists, not_and] at hcon
  obtain ⟨hno, hq⟩ := hcon
  have hcw : ∀ u, (c.node u).ph.cwReady = true → ¬ c.cwIn u := fun u hr hin =>
    hno (.cw u) (by intro _ _ h; cases h) ⟨hr, hin⟩
  have hccw : ∀ u, (c.node u).ph.ccwReady = true → ¬ c.ccwIn u := fun u hr hin =>
    hno (.ccw u) (by intro _ _ h; cases h) ⟨hr, hin⟩
  have hst : ∀ u, (c.node u).ph = .idle → (c.node u).q = [] := fun u hi => by
    by_contra hne; exact hno (.start u) (by intro _ _ h; cases h) ⟨hi, hne⟩
  obtain ⟨hC, hS⟩ := h
  have hcw' : ∀ u, (c.node u).ph.cwReady = true → c.cwS (u - 1) ≤ c.cwR u := fun u hr => by
    have := hcw u hr; simp only [Config.cwIn, not_lt] at this; exact this
  rcases hS with ⟨pre, d, r, H⟩ | ⟨pre, d, H⟩ | H
  · -- data stage: the holder would wait forever
    have hready : ∀ u, (c.node u).ph.cwReady = true := by
      intro u; by_cases hu : u = c.hold
      · rw [hu, H.ph_hold]; rfl
      · rcases (H.others u hu).2 with h1 | ⟨k, hk, -⟩
        · revert h1; cases (c.node u).ph <;> simp [Phase.IsTok, Phase.cwReady]
        · rw [hk]; rfl
    set B := base c.ds pre.length
    have hd := H.r_lt
    have hR : c.cwR c.hold = B + r + 1 := by
      rw [hC.cwR, H.ep_hold, H.ph_hold]; simp [Phase.rOff]; ring
    have hT : c.cwS c.hold = B + d + 1 := by
      rw [hC.cwS, H.ep_hold, H.ph_hold]; simp [Phase.sOff]; ring
    -- a non-holder that has received all data pulses has sent them all
    have hstep : ∀ v, v ≠ c.hold → B + d + 1 ≤ c.cwR v → B + d + 1 ≤ c.cwS v := by
      intro v hv hle
      obtain ⟨he, hp⟩ := H.others v hv
      have h1 := hC.cwR v; have h2 := hC.cwS v
      rw [he] at h1 h2
      rcases hp with hp | ⟨k, hk, -, -⟩
      · exfalso; revert hp h1; cases (c.node v).ph <;> simp [Phase.IsTok, Phase.rOff] <;> omega
      · rw [hk] at h1 h2; simp only [Phase.rOff, Phase.sOff] at h1 h2; omega
    by_cases hn1 : c.hold - 1 = c.hold
    · have := hcw' c.hold (hready _); rw [hn1, hT, hR] at this; omega
    · have key : ∀ v, v = c.hold ∨ B + d + 1 ≤ c.cwS v := by
        refine ZMod.chain_cw_all _ c.hold (fun v hv hS => ?_) ?_
        · rcases hS with hS | hS
          · exact absurd hS hv
          · by_cases hv1 : v + 1 = c.hold
            · exact Or.inl hv1
            · have := hcw' (v + 1) (hready _); rw [add_sub_cancel_right] at this
              exact Or.inr (hstep _ hv1 (hS.trans this))
        · by_cases hv1 : c.hold + 1 = c.hold
          · exact Or.inl hv1
          · have := hcw' (c.hold + 1) (hready _); rw [add_sub_cancel_right, hT] at this
            exact Or.inr (hstep _ hv1 this)
      rcases key (c.hold - 1) with h1 | h1
      · exact hn1 h1
      · have := hcw' c.hold (hready _); rw [hR] at this; omega
  · -- end stage: the `end` pulse can be read
    obtain ⟨v, hv⟩ := H.someIn
    rcases (H.target v hv).2 with h1 | h1
    · exact hccw v (by rw [h1, H.ph_hold]; rfl) hv
    · by_cases hvT' : v = c.hold
      · exact hccw v (by rw [hvT', H.ph_hold]; rfl) hv
      · rcases H.others v hvT' with ⟨-, h2⟩ | ⟨h2, -⟩
        · exact hccw v (by rw [h2]; rfl) hv
        · omega
  · -- token stage: everybody idles
    have hready : ∀ u, (c.node u).ph.cwReady = true := by
      intro u; have := H.isTok u; revert this
      cases (c.node u).ph <;> simp [Phase.IsTok, Phase.cwReady]
    have hK : ∀ u, c.cwS u = base c.ds c.ds.length + (c.node u).ph.sOff ∧
        c.cwR u = base c.ds c.ds.length + (c.node u).ph.rOff := fun u => by
      rw [hC.cwS, hC.cwR, H.ep_all]; exact ⟨rfl, rfl⟩
    have hidle : ∀ u, (c.node u).ph = .idle := by
      by_contra hne; push_neg at hne; obtain ⟨u, hu⟩ := hne
      have hprop : ∀ v, (c.node v).ph ≠ .idle → (c.node (v + 1)).ph = .ready := by
        intro v hv
        have h1 := hcw' (v + 1) (hready _); rw [add_sub_cancel_right] at h1
        have h2 := (hK v).1; have h3 := (hK (v + 1)).2
        have h4 := H.isTok v; have h5 := H.isTok (v + 1)
        revert hv h4 h1 h2; rcases (c.node v).ph <;> simp [Phase.IsTok, Phase.sOff] <;>
          revert h5 h3 <;> rcases (c.node (v + 1)).ph <;> simp [Phase.IsTok, Phase.rOff] <;> omega
      have hall : ∀ v, (c.node v).ph ≠ .idle :=
        ZMod.chain_cw_all _ (u - 1) (fun v _ hv => by rw [hprop v hv]; simp)
          (by rw [sub_add_cancel]; exact hu)
      have hT : (c.node c.hold).ph = .ready := by
        have := hprop (c.hold - 1) (hall _); rwa [sub_add_cancel] at this
      have htok : (c.node c.hold).tok = false := by
        cases ht : (c.node c.hold).tok
        · rfl
        · have := ((hC.tok c.hold).1 ht).2; rw [hT] at this; exact this.elim
      obtain ⟨p, hp⟩ := H.released htok
      have := hprop (p - 1) (hall _); rw [sub_add_cancel] at this
      exact hccw p (by rw [this]; rfl) hp
    have htok : (c.node c.hold).tok = true :=
      (hC.tok c.hold).2 ⟨rfl, by rw [hidle]; exact H.ep_all _⟩
    exact hq ⟨H, hidle, fun u => hst u (hidle u), fun u => hcw u (hready u),
      fun u => H.held htok u⟩

/-! ### Stage rank and potential -/

/-- Class of the holder's program point: data stage (`0`), end stage (`1`), token stage (`2`). -/
def Phase.cls : Phase → ℕ
  | .send _ _ => 0
  | .waitEnd _ => 1
  | _ => 2

/-- The stage rank: the data stage of epoch `K = |ds|` has rank `3K`, its end stage `3K + 1`,
the following token stage `3K + 2`. -/
def rank (c : Config n) : ℕ := 3 * c.ds.length + (c.node c.hold).ph.cls

/-- Upper bound of the clockwise counters in the current stage. -/
def cwTop (c : Config n) : ℕ :=
  base c.ds c.ds.length + if (c.node c.hold).ph.cls = 0 then 0 else 1

open Classical in
/-- Remaining hops of the counterclockwise pulse in transit (`token` or `end`). -/
noncomputable def ccwPot (c : Config n) : ℕ :=
  ∑ u, if c.ccwIn u then n - cdist c.hold u else 0

/-- The potential: remaining clockwise receptions and sends, remaining counterclockwise hops, and
`n + 1` while the token has not been released. -/
noncomputable def μ (c : Config n) : ℕ :=
  (∑ u, (2 * cwTop c - (c.cwS u + c.cwR u))) + ccwPot c +
    if (c.node c.hold).ph.cls = 2 ∧ (c.node c.hold).tok = true then n + 1 else 0

lemma ccwPot_eq_zero (h : ∀ v, ¬ c.ccwIn v) : ccwPot c = 0 := by
  classical
  unfold ccwPot; exact Finset.sum_eq_zero fun v _ => by simp [h v]

lemma ccwPot_eq_single {p : ZMod n} (h : ∀ v, c.ccwIn v ↔ v = p) :
    ccwPot c = n - cdist c.hold p := by
  classical
  unfold ccwPot
  rw [Finset.sum_eq_single p]
  · simp [(h p).2 rfl]
  · intro v _ hv; simp [(h v).not.2 hv]
  · simp

lemma Inv.cw_le_top (h : Inv c) (u : ZMod n) : c.cwS u ≤ cwTop c ∧ c.cwR u ≤ cwTop c := by
  obtain ⟨hC, hS⟩ := h
  unfold cwTop
  rcases hS with ⟨pre, d, r, H⟩ | ⟨pre, d, H⟩ | H
  · rw [H.ph_hold]; simp only [Phase.cls, ↓reduceIte, add_zero]
    have hlen : c.ds.length = pre.length + 1 := by rw [H.ds_eq]; simp
    rw [hlen, base_ds H.ds_eq, hC.cwS, hC.cwR]
    have := H.r_lt
    by_cases hu : u = c.hold
    · rw [hu, H.ep_hold, H.ph_hold]; simp [Phase.sOff, Phase.rOff]; omega
    · obtain ⟨he, hp⟩ := H.others u hu; rw [he]
      rcases hp with hp | ⟨k, hk, -, hkd⟩
      · revert hp; cases (c.node u).ph <;> simp [Phase.IsTok, Phase.sOff, Phase.rOff] <;> omega
      · rw [hk]; simp [Phase.sOff, Phase.rOff]; omega
  · rw [H.ph_hold]; simp only [Phase.cls]; simp only [one_ne_zero, ↓reduceIte]
    have hlen : c.ds.length = pre.length + 1 := by rw [H.ds_eq]; simp
    rw [hlen, hC.cwS, hC.cwR]
    have hb := base_ds H.ds_eq
    by_cases hu : u = c.hold
    · rw [hu, H.ep_hold, H.ph_hold]; simp [Phase.sOff, Phase.rOff]; omega
    · rcases H.others u hu with ⟨he, hp⟩ | ⟨he, hp⟩
      · rw [he, hp]; simp [Phase.sOff, Phase.rOff]; omega
      · rw [he]; revert hp
        cases (c.node u).ph <;> simp [Phase.IsTok, Phase.sOff, Phase.rOff]
  · have hT := H.isTok c.hold
    have hcls : (c.node c.hold).ph.cls = 2 := by
      revert hT; cases (c.node c.hold).ph <;> simp [Phase.IsTok, Phase.cls]
    rw [hcls]; simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
    rw [hC.cwS, hC.cwR, H.ep_all]
    have := H.isTok u; revert this
    cases (c.node u).ph <;> simp [Phase.IsTok, Phase.sOff, Phase.rOff]

/-- Strict decrease of a sum of slacks. -/
lemma sum_slack_lt {f g : ZMod n → ℕ} {M : ℕ} (hfg : ∀ v, f v ≤ g v) (hg : ∀ v, g v ≤ M)
    {u : ZMod n} (hu : f u < g u) : ∑ v, (M - g v) < ∑ v, (M - f v) := by
  apply Finset.sum_lt_sum
  · intro v _; have := hfg v; omega
  · exact ⟨u, Finset.mem_univ _, by have := hg u; omega⟩

lemma sum_slack_le {f g : ZMod n → ℕ} {M : ℕ} (hfg : ∀ v, f v ≤ g v) :
    ∑ v, (M - g v) ≤ ∑ v, (M - f v) :=
  Finset.sum_le_sum fun v _ => by have := hfg v; omega

lemma rank_push (u : ZMod n) (a : ℕ) : rank (next c (.push u a)) = rank c := by
  have : ((next c (.push u a)).node c.hold).ph = (c.node c.hold).ph := by
    by_cases h : c.hold = u <;> simp [h]
  simp only [rank, next_push_ds, next_push_hold, this]

lemma μ_push (u : ZMod n) (a : ℕ) : μ (next c (.push u a)) = μ c := by
  have h1 : ((next c (.push u a)).node c.hold).ph = (c.node c.hold).ph := by
    by_cases h : c.hold = u <;> simp [h]
  have h2 : ((next c (.push u a)).node c.hold).tok = (c.node c.hold).tok := by
    by_cases h : c.hold = u <;> simp [h]
  have h3 : cwTop (next c (.push u a)) = cwTop c := by simp only [cwTop, next_push_ds, next_push_hold, h1]
  unfold μ ccwPot
  rw [h3]; simp only [next_push_cwS, next_push_cwR, next_push_hold, h1, h2]; rfl

lemma cw_release_ccwIn {u : ZMod n} (hno : ∀ w, ¬ c.ccwIn w) (h1 : (onCW (c.node u)).2.2 = 1)
    (hC : Common c) (v : ZMod n) : (next c (.cw u)).ccwIn v ↔ v = u - 1 := by
  constructor
  · intro hv
    simp only [Config.ccwIn, next_cw_ccwS, next_cw_ccwR] at hv
    by_contra hvu
    have : v + 1 ≠ u := fun e => hvu (by rw [← e]; ring)
    simp only [this, ↓reduceIte, add_zero] at hv
    exact hno v hv
  · rintro rfl
    simp only [Config.ccwIn, next_cw_ccwS, next_cw_ccwR, sub_add_cancel, ↓reduceIte, h1]
    have h4 := hC.ccwChan (u - 1); simp only [sub_add_cancel] at h4; omega

lemma ccw_fwd_ccwIn {u : ZMod n} (hC : Common c) (hin : c.ccwIn u)
    (h1 : (onCCW (c.node u)).2.2 = 1) (v : ZMod n) : (next c (.ccw u)).ccwIn v ↔ v = u - 1 := by
  constructor
  · intro hv; have := ccw_in_imp hC hin hv; rw [← this]; ring
  · rintro rfl; exact ccw_send_in hC hin h1

lemma progress_cw (h : Inv c) {u : ZMod n} (hen : Enabled c (.cw u)) :
    rank c < rank (next c (.cw u)) ∨
      (rank (next c (.cw u)) = rank c ∧ μ (next c (.cw u)) < μ c) := by
  have h' := inv_cw h hen
  obtain ⟨hr, hin⟩ := hen
  set c' := next c (.cw u)
  have hds : c'.ds = c.ds := rfl
  have hh : c'.hold = c.hold := rfl
  -- a node in `send` is the holder
  have hsendT : ∀ d r, (c.node u).ph = .send d r → u = c.hold := by
    intro d r hs
    rcases h.2 with ⟨pre, d', r', H⟩ | ⟨pre, d', H⟩ | H
    · by_contra hu; rcases (H.others u hu).2 with h1 | ⟨k, hk, -⟩
      · rw [hs] at h1; exact h1
      · rw [hs] at hk; cases hk
    · by_contra hu; rcases H.others u hu with ⟨-, h1⟩ | ⟨-, h1⟩
      · rw [hs] at h1; cases h1
      · rw [hs] at h1; exact h1
    · have := H.isTok u; rw [hs] at this; exact this.elim
  by_cases hA : ∃ d r, (c.node u).ph = .send d r ∧ ¬ r + 1 < d
  · obtain ⟨d, r, hs, hlt⟩ := hA
    have hu := hsendT d r hs
    left
    have e1 : (c'.node c.hold).ph = .waitEnd d := by
      rw [← hu]; simp [c', onCW, hs, hlt]
    have e2 : (c.node c.hold).ph = .send d r := by rw [← hu]; exact hs
    unfold rank; rw [hds, hh, e1, e2]; simp only [Phase.cls]; omega
  · push_neg at hA
    have hcls : (c'.node c.hold).ph.cls = (c.node c.hold).ph.cls := by
      by_cases hT : c.hold = u
      · rw [hT]; simp only [c', next_cw_node, ↓reduceIte]
        rcases hs : (c.node u).ph with _ | _ | _ | k | ⟨d, r⟩ | d <;> simp [onCW, hs, Phase.cls]
        rw [if_pos (hA d r hs)]
      · simp [c', hT]
    have hrank : rank c' = rank c := by simp only [rank, hds, hh, hcls]
    have htop : cwTop c' = cwTop c := by simp only [cwTop, hds, hh, hcls]
    refine Or.inr ⟨hrank, ?_⟩
    have hsum := sum_slack_lt (M := 2 * cwTop c) (u := u)
      (f := fun v => c.cwS v + c.cwR v) (g := fun v => c'.cwS v + c'.cwR v)
      (fun v => by simp only [c', next_cw_cwS, next_cw_cwR]; omega)
      (fun v => by have := h'.cw_le_top v; rw [htop] at this; omega)
      (by simp only [c', next_cw_cwS, next_cw_cwR, ↓reduceIte]; omega)
    have hrest : ccwPot c' + (if (c'.node c'.hold).ph.cls = 2 ∧ (c'.node c'.hold).tok = true
        then n + 1 else 0) ≤ ccwPot c + (if (c.node c.hold).ph.cls = 2 ∧
        (c.node c.hold).tok = true then n + 1 else 0) := by
      rw [hh, hcls]
      by_cases h0 : (onCW (c.node u)).2.2 = 0
      · have hpot : ccwPot c' = ccwPot c := by
          classical
          unfold ccwPot; rw [hh]
          exact Finset.sum_congr rfl fun v _ => by rw [if_congr (cw_ccwIn_iff h0) rfl rfl]
        have htok : (c'.node c.hold).tok = (c.node c.hold).tok := by
          by_cases hT : c.hold = u
          · rw [hT]; simp only [c', next_cw_node, ↓reduceIte]
            rcases hs : (c.node u).ph with _ | _ | _ | k | ⟨d, r⟩ | d <;> simp [onCW, hs] at h0 ⊢
            · exact h0
            · exact h0
            · rw [if_pos (hA d r hs)]
          · simp [c', hT]
        rw [hpot, htok]
      · -- the holder releases the token
        have hT : (c.node u).tok = true ∧ ((c.node u).ph = .idle ∨ (c.node u).ph = .waitReq) := by
          rcases hs : (c.node u).ph with _ | _ | _ | k | ⟨d, r⟩ | d <;> simp [onCW, hs] at h0 ⊢
          · exact h0
          · exact h0
          · rw [if_pos (hA d r hs)] at h0; exact h0 rfl
        have hu : u = c.hold := ((h.1.tok u).1 hT.1).1
        have hTok : TokStage c := by
          rw [h.tokStage_iff, ← hu]; rcases hT.2 with h1 | h1 <;> rw [h1] <;> trivial
        have hno := hTok.held (hu ▸ hT.1)
        have h1 : (onCW (c.node u)).2.2 = 1 := by
          rcases hT.2 with h1 | h1 <;> simp [onCW, h1, hT.1]
        have hpot' : ccwPot c' = n - cdist c.hold (c.hold - 1) := by
          rw [← hh]; refine ccwPot_eq_single fun v => ?_
          rw [cw_release_ccwIn hno h1 h.1 v, hh, hu]
        have hpot : ccwPot c = 0 := ccwPot_eq_zero hno
        have htok' : (c'.node c.hold).tok = false := by
          rw [← hu]; simp only [c', next_cw_node, ↓reduceIte]
          rcases hT.2 with h1 | h1 <;> simp [onCW, h1]
        have hcls2 : (c.node c.hold).ph.cls = 2 := by
          have := hTok.isTok c.hold; revert this
          cases (c.node c.hold).ph <;> simp [Phase.IsTok, Phase.cls]
        have htokT : (c.node c.hold).tok = true := hu ▸ hT.1
        rw [hpot', hpot, cdist_sub_one_self, htok']
        simp only [hcls2, htokT, Bool.false_eq_true, and_false, and_self, ↓reduceIte]; omega
    unfold μ; rw [htop]; omega

lemma progress_ccw (h : Inv c) (h2 : Inv2 c) {u : ZMod n} (hen : Enabled c (.ccw u)) :
    rank c < rank (next c (.ccw u)) ∨
      (rank (next c (.ccw u)) = rank c ∧ μ (next c (.ccw u)) < μ c) := by
  have h' := inv_ccw h hen
  obtain ⟨hr, hin⟩ := hen
  set c' := next c (.ccw u)
  by_cases hcap : ∃ a, capture? (c.node u) = some a
  · -- a capture: from the token stage to the next data stage
    obtain ⟨a, ha⟩ := hcap
    left
    have hph : (c.node u).ph = .ready := by
      unfold capture? at ha; split at ha
      · assumption
      · cases ha
    have hds : c'.ds = c.ds ++ [a] := by simp only [c', next_ccw_ds, ha]
    have hTok : TokStage c := by
      rcases h.2 with ⟨pre, d, r, H⟩ | ⟨pre, d, H⟩ | H
      · exact absurd hin (H.noIn u)
      · exfalso; rcases (H.target u hin).2 with h1 | h1
        · rw [h1, H.ph_hold] at hph; cases hph
        · by_cases hu : u = c.hold
          · rw [hu, H.ph_hold] at hph; cases hph
          · rcases H.others u hu with ⟨-, h3⟩ | ⟨h3, -⟩
            · rw [hph] at h3; cases h3
            · omega
      · exact H
    have hcls : (c.node c.hold).ph.cls = 2 := by
      have := hTok.isTok c.hold; revert this
      cases (c.node c.hold).ph <;> simp [Phase.IsTok, Phase.cls]
    unfold rank; rw [hds, hcls]; simp; omega
  · have hcap' : capture? (c.node u) = none := by
      cases hc : capture? (c.node u) with
      | none => rfl
      | some a => exact absurd ⟨a, hc⟩ hcap
    have hds : c'.ds = c.ds := by simp only [c', next_ccw_ds, hcap']
    have hh : c'.hold = c.hold := by simp only [c', next_ccw_hold, hcap']
    rcases h.2 with ⟨pre, d, r, H⟩ | ⟨pre, d, H⟩ | H
    · exact absurd hin (H.noIn u)
    · by_cases hu : u = c.hold
      · -- the `end` pulse is back: to the token stage
        left
        have e1 : (c'.node c.hold).ph = .idle := by
          rw [← hu]; simp [c', onCCW, hu, H.ph_hold]
        unfold rank; rw [hds, hh, e1, H.ph_hold]; simp only [Phase.cls]; omega
      · -- the `end` pulse is forwarded
        right
        have hep := (H.target u hin).2.resolve_left hu
        have hfwd : (c.node u).ph = .fwd d := by
          rcases H.others u hu with ⟨-, h3⟩ | ⟨h3, -⟩
          · exact h3
          · omega
        have h1 : (onCCW (c.node u)).2.2 = 1 := by simp [onCCW, hfwd]
        have hT : (c'.node c.hold).ph = (c.node c.hold).ph := by
          rw [ccw_node_ne (Ne.symm hu)]
        have hTt : (c'.node c.hold).tok = (c.node c.hold).tok := by
          rw [ccw_node_ne (Ne.symm hu)]
        have hrank : rank c' = rank c := by simp only [rank, hds, hh, hT]
        refine ⟨hrank, ?_⟩
        have htop : cwTop c' = cwTop c := by simp only [cwTop, hds, hh, hT]
        have hcw : ∀ v, c'.cwS v = c.cwS v ∧ c'.cwR v = c.cwR v := fun v => by
          simp [c', onCCW, hfwd]
        have hpot' : ccwPot c' = n - cdist c.hold (u - 1) := by
          rw [← hh]; exact ccwPot_eq_single fun v => ccw_fwd_ccwIn h.1 hin h1 v
        have hpot : ccwPot c = n - cdist c.hold u :=
          ccwPot_eq_single fun v => ⟨fun hv => h.1.ccwUniq v u hv hin, fun e => e ▸ hin⟩
        have hlt : cdist c.hold u < n := by
          have := cdist_le c.hold u
          rcases this.lt_or_eq with h3 | h3
          · exact h3
          · exact absurd (cdist_injective _ (h3.trans (cdist_self c.hold).symm)) hu
        unfold μ; rw [htop, hpot', hpot, cdist_sub_one hu, hh, hT, hTt]
        simp only [hcw]; omega
    · -- the token stage: the token is forwarded
      right
      have hph : (c.node u).ph = .ready := by
        have := H.isTok u; revert hr this
        rcases (c.node u).ph <;> simp [Phase.IsTok, Phase.ccwReady]
      have hqe : (c.node u).q = [] := by
        cases hq : (c.node u).q
        · rfl
        · simp [capture?, hph, hq] at hcap'
      have htokH : (c.node c.hold).tok = false := by
        cases ht' : (c.node c.hold).tok
        · rfl
        · exact absurd hin (H.held ht' u)
      obtain ⟨p, hp, w, hw, hd⟩ := h2.token H htokH
      have hpu : p = u := h.1.ccwUniq p u hp hin
      subst hpu
      have hwp : w ≠ p := by rintro rfl; exact hw hqe
      have hlt' : cdist c.hold p < cdist c.hold w :=
        lt_of_le_of_ne hd (fun e => hwp (cdist_injective _ e).symm)
      have hpT : p ≠ c.hold := by
        rintro rfl; have := cdist_le c.hold w; rw [cdist_self] at hlt'; omega
      have ho : onCCW (c.node p) = (c.node p, 0, 1) := by simp [onCCW, hph, hqe]
      have hnd : ∀ v, c'.node v = c.node v := by
        intro v; by_cases hv : v = p
        · subst hv; simp [c', ho]
        · exact ccw_node_ne hv
      have hrank : rank c' = rank c := by simp only [rank, hds, hh, hnd]
      refine ⟨hrank, ?_⟩
      have htop : cwTop c' = cwTop c := by simp only [cwTop, hds, hh, hnd]
      have hcw : ∀ v, c'.cwS v = c.cwS v ∧ c'.cwR v = c.cwR v := fun v => by simp [c', ho]
      have h1 : (onCCW (c.node p)).2.2 = 1 := by rw [ho]
      have hpot' : ccwPot c' = n - cdist c.hold (p - 1) := by
        rw [← hh]; exact ccwPot_eq_single fun v => ccw_fwd_ccwIn h.1 hin h1 v
      have hpot : ccwPot c = n - cdist c.hold p :=
        ccwPot_eq_single fun v => ⟨fun hv => h.1.ccwUniq v p hv hin, fun e => e ▸ hin⟩
      have hle := cdist_le c.hold w
      unfold μ; rw [htop, hpot', hpot, cdist_sub_one hpT, hh, hnd]
      simp only [hcw]; omega

/-- **Progress.** Every step of the ring layer other than a push either moves to a later stage
or strictly decreases the potential `μ`. -/
theorem progress_step (h : Inv c) (h2 : Inv2 c) {l : Label n} (hl : ∀ u a, l ≠ .push u a)
    (hen : Enabled c l) :
    rank c < rank (next c l) ∨ (rank (next c l) = rank c ∧ μ (next c l) < μ c) := by
  cases l with
  | push u a => exact absurd rfl (hl u a)
  | start u =>
    have h' := inv_start h hen.1
    obtain ⟨hidle, -⟩ := hen
    set c' := next c (.start u)
    have hph : (c'.node c.hold).ph.cls = (c.node c.hold).ph.cls := by
      by_cases hT : c.hold = u
      · rw [hT]; simp [c', hidle, Phase.cls]
      · simp [c', hT]
    have htok : (c'.node c.hold).tok = (c.node c.hold).tok := by
      by_cases hT : c.hold = u <;> simp [c', hT]
    have hrank : rank c' = rank c := by
      simp only [rank, c', next_start_ds, next_start_hold]; rw [← hph]
    have htop : cwTop c' = cwTop c := by
      unfold cwTop; rw [show c'.ds = c.ds from rfl, show c'.hold = c.hold from rfl, hph]
    refine Or.inr ⟨hrank, ?_⟩
    have hpot : ccwPot c' = ccwPot c := rfl
    have := sum_slack_lt (M := 2 * cwTop c) (u := u)
      (f := fun v => c.cwS v + c.cwR v) (g := fun v => c'.cwS v + c'.cwR v)
      (fun v => by simp only [c', next_start_cwS, next_start_cwR]; omega)
      (fun v => by have := h'.cw_le_top v; rw [htop] at this; omega)
      (by simp [c'])
    unfold μ; rw [hpot, show c'.hold = c.hold from rfl, hph, htok, htop]
    omega
  | cw u => exact progress_cw h hen
  | ccw u => exact progress_ccw h h2 hen

end Podc.FullyDefective.Cycle
