import Papers.PODC2023.PPDoubleExpThresholds.MachineToProtocolFwd
import Papers.PODC2023.PPDoubleExpThresholds.MachineToProtocolValid

/-!
# Correctness of the conversion (proof of Proposition 16)

* `reach_inv`: from a configuration with `≥ |F|` agents in the initial state, every reachable
  configuration satisfies the election invariant, and if it is elected (one agent per pointer) it
  represents a machine configuration reachable from an initial one with `|c| - |F|` units.
* `reach_good`: from every reachable configuration such a "good" configuration is reachable
  (Lemma 15 applied to reachable configurations).
* `bcast_large`: with `≥ |F|` agents in the initial state (and arbitrary other agents) the broadcast
  protocol can always reach a configuration that is stable with output `φ(n - |F|)`.
* `bcast_small`: with `n < |F|` agents, all in the initial state, every reachable configuration
  has output `false` (no `IP` agent is ever created).
-/

set_option linter.unusedSectionVars false

namespace Podc.PPDoubleExpThresholds

open Cslib Cslib.PopulationProtocol Cslib.TransitionSystem M2P

namespace Machine

variable {Q F : Type*} [Fintype Q] [Fintype F] [DecidableEq Q] [DecidableEq F]
variable (A : Machine Q F)

/-- `c` represents a machine configuration reachable from an initial one with `N` units. -/
def Good (N : ℕ) (c : Multiset (St Q F)) : Prop :=
  ∃ C C₀, A.Rep c C ∧ A.IsInitial C₀ ∧ Reach A.Step C₀ C ∧ total C₀ = N

theorem good_pi {C₀ : Cfg Q F} (h : A.IsInitial C₀) : A.Good (total C₀) (pi C₀) :=
  ⟨C₀, C₀, .idle (A.wf_of_initial h), h, .refl, rfl⟩

theorem good_step {N : ℕ} {c c' : Multiset (St Q F)} (h : A.Good N c)
    (hs : MStep {t | A.Tr t} c c') : A.Good N c' := by
  obtain ⟨C, C₀, hR, h0, hr, hN⟩ := h
  obtain ⟨C', hR', hr'⟩ := A.rep_step hR hs
  exact ⟨C', C₀, hR', h0, hr.trans hr', hN⟩

/-- The invariant of all reachable configurations (base protocol). -/
theorem reach_inv (hdom : ∀ X, (A.dom X).Nonempty) {c₀ : Multiset (St Q F)}
    (hc₀ : Fintype.card F ≤ c₀.count A.initS) :
    ∀ c, A.PReach c₀ c → A.Inv c ∧
      (Elected c → A.Good (Multiset.card c₀ - Fintype.card F) c) := by
  intro c hr
  induction hr with
  | refl => exact ⟨A.inv_init hc₀, fun he => absurd he (A.not_elected_init hc₀)⟩
  | @tail c c' hr hs ih =>
    rcases hs with rfl | ⟨t, ht, hf⟩
    · exact ih
    · refine ⟨A.inv_step ih.1 ht hf, fun he' => ?_⟩
      by_cases he : Elected c
      · exact A.good_step (ih.2 he) ⟨t, ht, hf⟩
      · obtain ⟨C₀, hC₀, rfl⟩ := A.piInit_of_step hdom ih.1 he ht hf he'
        have hcard := A.basePP.reach_card_eq (hr.tail (.inr ⟨t, ht, hf⟩))
        rw [card_pi] at hcard
        have := A.good_pi hC₀
        rwa [show total C₀ = Multiset.card c₀ - Fintype.card F by omega] at this

/-- From every reachable configuration a good one is reachable. -/
theorem reach_good (hdom : ∀ X, (A.dom X).Nonempty) {c₀ : Multiset (St Q F)}
    (hc₀ : Fintype.card F ≤ c₀.count A.initS) {c : Multiset (St Q F)} (hr : A.PReach c₀ c) :
    ∃ e, A.PReach c e ∧ A.Good (Multiset.card c₀ - Fintype.card F) e := by
  obtain ⟨hinv, hG⟩ := A.reach_inv hdom hc₀ c hr
  by_cases he : Elected c
  · exact ⟨c, .refl, hG he⟩
  · obtain ⟨c', hr', C₀, hC₀, rfl⟩ := A.exists_reach_piInit hdom hinv he
    have hcard := A.basePP.reach_card_eq (hr.trans (A.basePP.reach_of_mreach hr'))
    rw [card_pi] at hcard
    have := A.good_pi hC₀
    rw [show total C₀ = Multiset.card c₀ - Fintype.card F by omega] at this
    exact ⟨_, A.basePP.reach_of_mreach hr', this⟩

/-! ### The output flag in clean configurations -/

theorem ofv_eq_some {s : St Q F} {b : Bool} (h : A.ofv s = some b) :
    ∃ st, s = .ptr A.OF (.bool b) st := by
  unfold ofv at h
  split at h
  · next X b' st =>
    split_ifs at h with hX
    · cases h; subst hX; exact ⟨st, rfl⟩
  · cases h

theorem rep_gOF {c : Multiset (St Q F)} {C : Cfg Q F} (h : A.Rep c C) :
    ∃ r g, c = render r g ∧ OwnerResp g ∧
      ((∃ st, g A.OF = .ptr A.OF (C.ptr A.OF) st) ∨ ∃ i, g A.OF = .map A.OF i) := by
  cases h with
  | idle => exact ⟨_, _, rfl, ownerResp_idleG _, .inl ⟨_, rfl⟩⟩
  | mvEmit =>
    exact ⟨_, _, rfl, A.ownerResp_gW _ _ rfl, .inl ⟨.none, by simp [gW, idleG]⟩⟩
  | mvDone =>
    exact ⟨_, _, rfl, A.ownerResp_gW _ _ rfl, .inl ⟨.none, by simp [gW, idleG]⟩⟩
  | mvHalf => exact ⟨_, _, rfl, A.ownerResp_gH _ _, .inl ⟨.none, by simp [gH, idleG]⟩⟩
  | mvTake =>
    exact ⟨_, _, rfl, A.ownerResp_gW _ _ rfl, .inl ⟨.none, by simp [gW, idleG]⟩⟩
  | mvFin =>
    exact ⟨_, _, rfl, A.ownerResp_gW _ _ rfl, .inl ⟨.none, by simp [gW, idleG]⟩⟩
  | tsTest =>
    exact ⟨_, _, rfl, A.ownerResp_gW _ _ rfl, .inl ⟨.none, by simp [gW, idleG]⟩⟩
  | tsRes =>
    exact ⟨_, _, rfl, A.ownerResp_gW _ _ rfl, .inl ⟨.none, by simp [gW, idleG]⟩⟩
  | tsFin =>
    exact ⟨_, _, rfl, A.ownerResp_gW _ _ rfl, .inl ⟨.none, by simp [gW, idleG]⟩⟩
  | @asMap C i X Y f hw hi hI hXY hX hY =>
    refine ⟨_, _, rfl, A.ownerResp_gW _ _ rfl, ?_⟩
    by_cases hO : A.OF = X
    · subst hO; exact .inr ⟨i, by simp [gW]⟩
    · exact .inl ⟨.none, by simp [gW, idleG, hO]⟩
  | @asFin C i X Y f hw hi hI hXY hX hY =>
    refine ⟨_, _, rfl, A.ownerResp_gW _ _ rfl, ?_⟩
    by_cases hO : A.OF = X
    · subst hO; exact .inl ⟨.done, by simp [gW]⟩
    · exact .inl ⟨.none, by simp [gW, idleG, hO]⟩

/-- In a clean configuration representing `C`, an agent showing the output flag shows `C(OF)`. -/
theorem rep_ofv {c : Multiset (St Q F)} {C : Cfg Q F} (h : A.Rep c C) {s : St Q F}
    (hs : s ∈ c) {b : Bool} (hb : A.ofv s = some b) : C.ptr A.OF = .bool b := by
  obtain ⟨r, g, rfl, hg, hOF⟩ := A.rep_gOF h
  obtain ⟨st, rfl⟩ := A.ofv_eq_some hb
  rcases mem_render.1 hs with ⟨q, hq, -⟩ | ⟨X, hX⟩
  · cases hq
  · have : X = A.OF := by
      have := hg X; rw [← hX] at this; exact (Option.some_injective _ this).symm
    subst this
    rcases hOF with ⟨st', h'⟩ | ⟨i, h'⟩
    · rw [h'] at hX; simp only [St.ptr.injEq, true_and] at hX; exact hX.1.symm
    · rw [h'] at hX; cases hX

theorem settled_OF {d : Multiset (St Q F)} {C : Cfg Q F} (h : A.Settled d C) :
    (.ptr A.OF (C.ptr A.OF) .none : St Q F) ∈ d := by
  obtain ⟨-, rfl | ⟨i, x, y, u, -, -, -, -, rfl⟩⟩ := h
  · exact mem_render.2 (.inr ⟨A.OF, rfl⟩)
  · exact mem_render.2 (.inr ⟨A.OF, by simp [gW, idleG]⟩)

theorem settled_rep {d : Multiset (St Q F)} {C : Cfg Q F} (h : A.Settled d C) : A.Rep d C := by
  obtain ⟨hw, rfl | ⟨i, x, y, u, hi, hI, hu, -, rfl⟩⟩ := h
  · exact .idle hw
  · exact .mvEmit hw hi hI hu

theorem out_eq_some {C : Cfg Q F} {b : Bool} (h : A.out C = some b) :
    C.ptr A.OF = .bool b := by
  unfold out at h
  split at h
  · next b' h' => cases h; exact h'
  · cases h

/-! ### The broadcast protocol -/

theorem bcast_reach_fst' {c c' : Multiset (St Q F × Bool)} (h : Reach A.bcastPP.Step c c') :
    A.PReach (c.map Prod.fst) (c'.map Prod.fst) := bcast_reach_fst h

theorem bcast_lift' {c : Multiset (St Q F × Bool)} {d : Multiset (St Q F)}
    (h : A.PReach (c.map Prod.fst) d) :
    ∃ c', Reach A.bcastPP.Step c c' ∧ c'.map Prod.fst = d := bcast_lift_reach h

open Classical in
theorem bcastPP_out {e : Multiset (St Q F × Bool)} (he : e ≠ 0) {b : Bool}
    (h : ∀ x ∈ e, x.2 = b) : A.bcastPP.out e = some b := by
  obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero he
  unfold PProtocol.out
  cases b
  · have h1 : ¬ ∀ q ∈ e, q ∈ A.bcastPP.O := fun h' => by
      have := h' y hy; simp [bcastPP, h y hy] at this
    rw [if_neg h1, if_pos (fun q hq => by simp [bcastPP, h q hq])]
  · rw [if_pos (fun q hq => by simp [bcastPP, h q hq])]

/-- The stability invariant: all opinions are `b`, and the underlying configuration represents a
configuration reachable from the stable configuration `Cs`. -/
theorem bcast_stable {b : Bool} {Cs : Cfg Q F} (hst : StableOut A.Step A.out b Cs)
    {e : Multiset (St Q F × Bool)} (he : e ≠ 0) (hbits : ∀ x ∈ e, x.2 = b)
    {C : Cfg Q F} (hR : A.Rep (e.map Prod.fst) C) (hC : Reach A.Step Cs C) :
    StableOut A.bcastPP.Step A.bcastPP.out b e := by
  suffices ∀ e', Reach A.bcastPP.Step e e' → (∀ x ∈ e', x.2 = b) ∧
      ∃ C', A.Rep (e'.map Prod.fst) C' ∧ Reach A.Step Cs C' by
    intro e' he'
    refine A.bcastPP_out ?_ (this e' he').1
    intro h0
    have := A.bcastPP.reach_card_eq he'
    rw [h0] at this; simp at this; exact he (Multiset.card_eq_zero.1 this.symm)
  intro e' he'
  induction he' with
  | refl => exact ⟨hbits, C, hR, hC⟩
  | @tail e₁ e₂ _ hs ih =>
    obtain ⟨hb₁, C₁, hR₁, hC₁⟩ := ih
    rcases hs with rfl | hs
    · exact ⟨hb₁, C₁, hR₁, hC₁⟩
    obtain ⟨C₂, hR₂, hC₂⟩ : ∃ C₂, A.Rep (e₂.map Prod.fst) C₂ ∧ Reach A.Step Cs C₂ := by
      rcases bcast_step_fst hs with heq | hs'
      · exact ⟨C₁, heq ▸ hR₁, hC₁⟩
      · obtain ⟨C₂, hR₂, h₂⟩ := A.rep_step hR₁ hs'
        exact ⟨C₂, hR₂, hC₁.trans h₂⟩
    refine ⟨?_, C₂, hR₂, hC₂⟩
    obtain ⟨t, ⟨-, hbit⟩, hf⟩ := hs
    have hOFb : ∀ s ∈ e₂.map Prod.fst, ∀ b', A.ofv s = some b' → b' = b := by
      intro s hs b' hb'
      have h1 := A.rep_ofv hR₂ hs hb'
      have h2 := A.out_eq_some (hst C₂ hC₂)
      rw [h1] at h2; cases h2; rfl
    have hp' : t.p'.1 ∈ e₂.map Prod.fst := Multiset.mem_map_of_mem _ (fires_p'_mem hf)
    have hq' : t.q'.1 ∈ e₂.map Prod.fst := Multiset.mem_map_of_mem _ (fires_q'_mem hf)
    intro x hx
    rcases fires_mem_of_mem hf hx with hx | rfl | rfl
    · exact hb₁ x hx
    · rcases hbit with ⟨b', hb', h1, -⟩ | ⟨-, -, h1, -⟩
      · rcases hb' with hb' | hb'
        · rw [h1]; exact hOFb _ hp' b' hb'
        · rw [h1]; exact hOFb _ hq' b' hb'
      · rw [h1]; exact hb₁ _ (fires_p_mem hf)
    · rcases hbit with ⟨b', hb', -, h1⟩ | ⟨-, -, -, h1⟩
      · rcases hb' with hb' | hb'
        · rw [h1]; exact hOFb _ hp' b' hb'
        · rw [h1]; exact hOFb _ hq' b' hb'
      · rw [h1]; exact hb₁ _ (fires_q_mem hf)

/-- **Correctness with at least `|F|` agents in the initial state** (and arbitrary other agents). -/
theorem bcast_large {φ : ℕ → Bool} (hA : A.Decides φ) (hdom : ∀ X, (A.dom X).Nonempty)
    {c₀ : Multiset (St Q F × Bool)}
    (hc₀ : Fintype.card F ≤ (c₀.map Prod.fst).count A.initS) :
    ∀ c, Reach A.bcastPP.Step c₀ c → ∃ d, Reach A.bcastPP.Step c d ∧
      StableOut A.bcastPP.Step A.bcastPP.out (φ (Multiset.card c₀ - Fintype.card F)) d := by
  intro c hc
  have hcard : Multiset.card c = Multiset.card c₀ := A.bcastPP.reach_card_eq hc
  have hk2 : 2 ≤ Fintype.card F := by
    have := Fintype.card_le_of_injective (fun b : Bool => if b then A.OF else A.CF)
      (by intro a b; cases a <;> cases b <;> simp [A.OF_ne_CF, A.OF_ne_CF.symm])
    simpa using this
  have hk : Fintype.card F ≤ Multiset.card c₀ := by
    have := Multiset.count_le_card A.initS (c₀.map Prod.fst)
    simp at this; omega
  -- a good configuration
  obtain ⟨e, he, C, C₀, hR, h0, hr0, hN⟩ :=
    A.reach_good hdom (by simpa using hc₀) (A.bcast_reach_fst' hc)
  rw [Multiset.card_map] at hN
  -- finish the instruction in progress
  obtain ⟨C₁, d, hC₁, hd, hS⟩ := A.rep_complete hR
  -- a stable machine configuration
  obtain ⟨Cs, hCs, hst⟩ := A.reach_stable_of_decides hA h0 C₁ (hr0.trans hC₁)
  rw [hN] at hst
  obtain ⟨d', hd', hS'⟩ := A.settled_reach hS hCs
  -- lift to the broadcast protocol
  obtain ⟨c₁, hc₁, hc₁d⟩ := A.bcast_lift' (he.trans (hd.trans hd'))
  -- broadcast the output
  have hOF := A.settled_OF hS'
  rw [A.out_eq_some (hst Cs .refl)] at hOF
  rw [← hc₁d] at hOF
  obtain ⟨⟨s, β⟩, hsβ, rfl⟩ := Multiset.mem_map.1 hOF
  have hcard₁ : Multiset.card c₁ = Multiset.card c₀ := (A.bcastPP.reach_card_eq hc₁).trans hcard
  obtain ⟨c₂, hc₂, hc₂d, hbits⟩ := bcast_spread (δ := {t | A.Tr t}) (ofv := A.ofv)
    (b := φ (Multiset.card c₀ - Fintype.card F)) hsβ
    (by simp [ofv]) (by omega)
  refine ⟨c₂, hc₁.trans hc₂, A.bcast_stable hst ?_ hbits (C := Cs) ?_ .refl⟩
  · intro h0'
    have := A.bcastPP.reach_card_eq hc₂
    rw [h0'] at this; simp at this; omega
  · rw [hc₂d, hc₁d]; exact A.settled_rep hS'

/-! ### Fewer than `|F|` agents -/

/-- With only fresh non-`IP` pointer agents, the only enabled transitions are `⟨elect⟩`. -/
theorem tr_fresh {t : Transition (St Q F)} (ht : A.Tr t) {X : F} (hX : X ≠ A.IP)
    (hp : t.p = .ptr X (A.v0 X) .none) :
    t.q.owner = some X ∧ t.p' = .ptr X (A.v0 X) .none ∧
      t.q' = .ptr (A.nxt X) (A.v0 (A.nxt X)) .none := by
  cases ht with
  | elect hY ha hb =>
    simp only at hp; subst hp; simp only [St.owner_ptr, Option.some.injEq] at ha
    subst ha; exact ⟨hb, rfl, rfl⟩
  | electIP ha hb => simp only at hp; subst hp; simp at ha; exact absurd ha hX
  | tsSet b hI hv => simp only at hp; cases b <;> simp at hp
  | _ => simp_all

theorem ofv_fresh (X : F) {b : Bool} (h : A.ofv (.ptr X (A.v0 X) .none) = some b) : b = false := by
  obtain ⟨st, hst⟩ := A.ofv_eq_some h
  simp only [St.ptr.injEq] at hst
  obtain ⟨rfl, h2, -⟩ := hst
  rw [A.v0_OF] at h2; cases h2; rfl

/-- **Fewer than `|F|` agents**: every reachable configuration consists of fresh non-`IP` pointer
agents with opinion `false`. -/
theorem bcast_small {n : ℕ} (hn : n < Fintype.card F) :
    ∀ c, Reach A.bcastPP.Step (Multiset.replicate n (A.initS, false)) c →
      (∀ x ∈ c, x.2 = false ∧ ∃ X, X ≠ A.IP ∧ x.1 = .ptr X (A.v0 X) .none) ∧
      ∀ l ≤ n, l ≤ A.below (c.map Prod.fst) l := by
  have hX1 : A.X1 ≠ A.IP := by
    intro h
    have := A.lvl_X1; rw [h, A.lvl_IP] at this
    have := Fintype.card_le_of_injective (fun b : Bool => if b then A.OF else A.CF)
      (by intro a b; cases a <;> cases b <;> simp [A.OF_ne_CF, A.OF_ne_CF.symm])
    simp at this; omega
  intro c hc
  induction hc with
  | refl =>
    refine ⟨fun x hx => ?_, fun l hl => ?_⟩
    · rw [Multiset.eq_of_mem_replicate hx]; exact ⟨rfl, A.X1, hX1, rfl⟩
    · rcases Nat.eq_zero_or_pos l with rfl | hl0
      · simp
      · unfold below
        rw [Multiset.map_replicate, Multiset.countP_eq_card.2 (fun s hs => by
          rw [Multiset.eq_of_mem_replicate hs]; simp [initS, A.lvl_X1, hl0])]
        simpa using hl
  | @tail c c' hr hs ih =>
    obtain ⟨hfresh, hJ⟩ := ih
    rcases hs with rfl | ⟨t, ⟨hδ, hbit⟩, hf⟩
    · exact ⟨hfresh, hJ⟩
    have hcard : Multiset.card c = n := by
      have := A.bcastPP.reach_card_eq hr; simpa using this
    obtain ⟨Xp, hXp, hpX⟩ := (hfresh _ (fires_p_mem hf)).2
    have hff := fires_map hf Prod.fst
    -- the underlying transition: `⟨elect⟩` at `Xp`, or the identity
    have key : (t.q'.1 = t.q.1 ∧ t.p'.1 = t.p.1) ∨ (t.q.1.owner = some Xp ∧
        t.p'.1 = .ptr Xp (A.v0 Xp) .none ∧ t.q'.1 = .ptr (A.nxt Xp) (A.v0 (A.nxt Xp)) .none) := by
      rcases hδ with hδ | ⟨h1, h2⟩
      · exact .inr (A.tr_fresh hδ hXp hpX)
      · exact .inl ⟨h2, h1⟩
    rcases key with ⟨h1, h2⟩ | ⟨hqo, hp', hq'⟩
    · -- identity on states: only the opinions may change
      have heq : c'.map Prod.fst = c.map Prod.fst := by
        have hs : (trMap Prod.fst t).Silent := by
          simp [Transition.Silent, Transition.pre, Transition.post, trMap, h1, h2]
        exact hff.eq_of_silent hs
      refine ⟨fun x hx => ?_, by rw [heq]; exact hJ⟩
      have hx1 : x.1 ∈ c.map Prod.fst := heq ▸ Multiset.mem_map_of_mem _ hx
      obtain ⟨y, hy, hyx⟩ := Multiset.mem_map.1 hx1
      refine ⟨?_, hyx ▸ (hfresh y hy).2⟩
      rcases fires_mem_of_mem hf hx with hx' | rfl | rfl
      · exact (hfresh _ hx').1
      · rcases hbit with ⟨b, hb, hb1, -⟩ | ⟨-, -, hb1, -⟩
        · rw [hb1]
          rcases hb with hb | hb
          · rw [h2, hpX] at hb; exact A.ofv_fresh _ hb
          · obtain ⟨Xq, -, hqX⟩ := (hfresh _ (fires_q_mem hf)).2
            rw [h1, hqX] at hb; exact A.ofv_fresh _ hb
        · rw [hb1]; exact (hfresh _ (fires_p_mem hf)).1
      · rcases hbit with ⟨b, hb, -, hb1⟩ | ⟨-, -, -, hb1⟩
        · rw [hb1]
          rcases hb with hb | hb
          · rw [h2, hpX] at hb; exact A.ofv_fresh _ hb
          · obtain ⟨Xq, -, hqX⟩ := (hfresh _ (fires_q_mem hf)).2
            rw [h1, hqX] at hb; exact A.ofv_fresh _ hb
        · rw [hb1]; exact (hfresh _ (fires_q_mem hf)).1
    · -- `⟨elect⟩` at `Xp`
      have hpo : (trMap Prod.fst t).p.owner = some Xp := by simp [trMap, hpX]
      have hqo' : (trMap Prod.fst t).q.owner = some Xp := hqo
      have e := below_elect (A := A) hff hXp hpo hqo' hp' hq'
      have h2 := two_le_cnt hff hpo hqo'
      have hall : A.below (c.map Prod.fst) n = n := by
        have := hJ n le_rfl
        have h' : A.below (c.map Prod.fst) n ≤ n := by
          unfold below; exact (Multiset.countP_le_card _ _).trans (by simp [hcard])
        omega
      -- the level of `Xp` is below `n - 1`
      have hlvl : A.lvl Xp + 2 ≤ n := by
        by_contra hcon
        have h3 := A.below_lvl_succ (c.map Prod.fst) Xp
        by_cases hle : A.lvl Xp ≤ n
        · have h4 := hJ _ hle
          have h5 : A.below (c.map Prod.fst) (A.lvl Xp + 1) ≤ n := by
            unfold below; exact (Multiset.countP_le_card _ _).trans (by simp [hcard])
          omega
        · -- all agents are at levels `< n`, so none is at the level of `Xp`
          have h6 : cnt (c.map Prod.fst) Xp = 0 := by
            unfold cnt
            rw [Multiset.countP_eq_zero]
            intro s hs hso
            have : A.lvlOf s < n := by
              by_contra h7
              have h8 : A.below (c.map Prod.fst) n < Multiset.card (c.map Prod.fst) := by
                unfold below
                exact lt_of_le_of_ne (Multiset.countP_le_card _ _)
                  (fun h => h7 (Multiset.countP_eq_card.1 h s hs))
              simp [hcard] at h8; omega
            rw [A.lvlOf_of_owner hso] at this; omega
          omega
      have hnxt : A.nxt Xp ≠ A.IP := by
        intro h
        have := A.lvl_nxt hXp; rw [h, A.lvl_IP] at this; omega
      refine ⟨fun x hx => ?_, fun l hl => ?_⟩
      · rcases fires_mem_of_mem hf hx with hx' | rfl | rfl
        · exact hfresh _ hx'
        · refine ⟨?_, Xp, hXp, hp'⟩
          rcases hbit with ⟨b, hb, hb1, -⟩ | ⟨-, -, hb1, -⟩
          · rw [hb1]
            rcases hb with hb | hb
            · rw [hp'] at hb; exact A.ofv_fresh _ hb
            · rw [hq'] at hb; exact A.ofv_fresh _ hb
          · rw [hb1]; exact (hfresh _ (fires_p_mem hf)).1
        · refine ⟨?_, A.nxt Xp, hnxt, hq'⟩
          rcases hbit with ⟨b, hb, -, hb1⟩ | ⟨-, -, -, hb1⟩
          · rw [hb1]
            rcases hb with hb | hb
            · rw [hp'] at hb; exact A.ofv_fresh _ hb
            · rw [hq'] at hb; exact A.ofv_fresh _ hb
          · rw [hb1]; exact (hfresh _ (fires_q_mem hf)).1
      · have e' := e l
        have h3 := A.below_lvl_succ (c.map Prod.fst) Xp
        have h4 := hJ (A.lvl Xp) (by omega)
        have h5 := hJ l hl
        split_ifs at e' with hl'
        · subst hl'; omega
        · omega

end Machine

end Podc.PPDoubleExpThresholds
