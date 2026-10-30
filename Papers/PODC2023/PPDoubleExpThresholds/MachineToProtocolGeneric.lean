import Papers.PODC2023.PPDoubleExpThresholds.Protocol

-- CSLib candidate (with `PProtocol`): `trMap`/`fires_map`, `restrictTo`, `bcast` and its lemmas.

/-!
# Generic tools for population protocols (used for Proposition 16)

* `Transition.map`, `Fires.map`, `fires_iff_add`: transitions under maps of states.
* `PProtocol.reach_finite`: finitely many configurations are reachable (finite state space).
* `PProtocol.decides_of_reach`, `PProtocol.stabilises_of_reach`: the reachability
  characterization of stable computation for protocols (via `forall_fair_iff_reach`).
* `PProtocol.restrictTo`: the protocol induced on a finite set `U` of states that is closed under
  the transitions; reachability and outputs transfer (`restrictTo_reach_stable`).
* `bcast`: the standard *output broadcast* construction (Appendix B.3): every state gets an
  opinion bit; agents meeting the output flag adopt its value. Steps project to steps
  (`bcast_step_fst`), steps lift (`bcast_lift_reach`), and the value of the output flag spreads
  (`bcast_spread`).
-/

namespace Podc.PPDoubleExpThresholds

open Cslib Cslib.PopulationProtocol Cslib.TransitionSystem

section Fires

variable {T T' : Type*} [DecidableEq T] [DecidableEq T']

/-- The image of a transition under a map of states. -/
def trMap (f : T → T') (t : Transition T) : Transition T' :=
  ⟨f t.p, f t.q, f t.p', f t.q'⟩

omit [DecidableEq T] [DecidableEq T'] in
@[simp] theorem trMap_pre (f : T → T') (t : Transition T) :
    (trMap f t).pre = t.pre.map f := by
  simp [trMap, Transition.pre]

omit [DecidableEq T] [DecidableEq T'] in
@[simp] theorem trMap_post (f : T → T') (t : Transition T) :
    (trMap f t).post = t.post.map f := by
  simp [trMap, Transition.post]

theorem fires_iff_add {t : Transition T} {C C' : Multiset T} :
    t.Fires C C' ↔ t.pre ≤ C ∧ C' + t.pre = C + t.post := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h2, add_right_comm, tsub_add_cancel_of_le h1]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have : C' + t.pre = C - t.pre + t.post + t.pre := by
      rw [h2, add_right_comm, tsub_add_cancel_of_le h1]
    exact add_right_cancel this

theorem fires_map {t : Transition T} {C C' : Multiset T} (h : t.Fires C C')
    (f : T → T') : (trMap f t).Fires (C.map f) (C'.map f) := by
  rw [fires_iff_add] at h ⊢
  refine ⟨by simpa using Multiset.map_le_map h.1, ?_⟩
  simp only [trMap_pre, trMap_post, ← Multiset.map_add, h.2]

theorem fires_unique {t : Transition T} {C C₁ C₂ : Multiset T} (h₁ : t.Fires C C₁)
    (h₂ : t.Fires C C₂) : C₁ = C₂ := h₁.2.trans h₂.2.symm

theorem fires_mem_of_mem {t : Transition T} {C C' : Multiset T} (h : t.Fires C C')
    {x : T} (hx : x ∈ C') : x ∈ C ∨ x = t.p' ∨ x = t.q' := by
  rw [h.2] at hx
  rcases Multiset.mem_add.1 hx with hx | hx
  · exact .inl (Multiset.mem_of_le (Multiset.sub_le_self _ _) hx)
  · right; simpa [Transition.post] using hx

theorem fires_p_mem {t : Transition T} {C C' : Multiset T} (h : t.Fires C C') : t.p ∈ C :=
  Multiset.mem_of_le h.1 (by simp [Transition.pre])

theorem fires_q_mem {t : Transition T} {C C' : Multiset T} (h : t.Fires C C') : t.q ∈ C :=
  Multiset.mem_of_le h.1 (by simp [Transition.pre])

theorem fires_p'_mem {t : Transition T} {C C' : Multiset T} (h : t.Fires C C') : t.p' ∈ C' := by
  rw [h.2]; exact Multiset.mem_add.2 (.inr (by simp [Transition.post]))

theorem fires_q'_mem {t : Transition T} {C C' : Multiset T} (h : t.Fires C C') : t.q' ∈ C' := by
  rw [h.2]; exact Multiset.mem_add.2 (.inr (by simp [Transition.post]))

end Fires

namespace PProtocol

variable {T : Type*} [DecidableEq T] (PP : PProtocol T)

theorem Step.card_eq {C C' : Multiset T} (h : PP.Step C C') :
    Multiset.card C' = Multiset.card C := by
  rcases h with rfl | h
  · rfl
  · exact h.card_eq

theorem reach_card_eq {C C' : Multiset T} (h : Reach PP.Step C C') :
    Multiset.card C' = Multiset.card C := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (Step.card_eq PP hs).trans ih

/-- Finitely many configurations are reachable from any configuration. -/
theorem reach_finite [Fintype T] (C : Multiset T) : {C' | Reach PP.Step C C'}.Finite := by
  refine (Set.finite_range (fun s : Sym T (Multiset.card C) => (s : Multiset T))).subset ?_
  intro C' hC'
  exact ⟨⟨C', PP.reach_card_eq hC'⟩, rfl⟩

theorem reach_of_mreach {C C' : Multiset T} (h : MReach PP.δ C C') : Reach PP.Step C C' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (.inr hs)

/-- Reachability characterization of stabilisation (finite state space). -/
theorem stabilises_of_reach [Fintype T] {C₀ : Multiset T} {b : Bool}
    (h : ∀ C, Reach PP.Step C₀ C → ∃ D, Reach PP.Step C D ∧ StableOut PP.Step PP.out b D)
    (E : Run PP.Step) (hE0 : E.st 0 = C₀) (hE : E.GloballyFair) : StabilisesTo PP.out E b :=
  (forall_fair_iff_reach (PP.reach_finite C₀) (fun x _ => ⟨x, .inl rfl⟩)).2 h E hE0 hE

/-! ### Restriction to a closed finite set of states -/

/-- The protocol induced on a set `U` of states: transitions between states of `U`. -/
def restrictTo (U : Finset T) : PProtocol U where
  δ := {t | trMap Subtype.val t ∈ PP.δ}
  I := Subtype.val ⁻¹' PP.I
  O := Subtype.val ⁻¹' PP.O

variable {PP} {U : Finset T}

theorem restrictTo_step_map {C C' : Multiset U} (h : (PP.restrictTo U).Step C C') :
    PP.Step (C.map Subtype.val) (C'.map Subtype.val) := by
  rcases h with rfl | ⟨t, ht, hf⟩
  · exact .inl rfl
  · exact .inr ⟨_, ht, fires_map hf _⟩

theorem restrictTo_reach_map {C C' : Multiset U} (h : Reach (PP.restrictTo U).Step C C') :
    Reach PP.Step (C.map Subtype.val) (C'.map Subtype.val) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (restrictTo_step_map hs)

/-- `U` is closed under the transitions. -/
def Closed (PP : PProtocol T) (U : Finset T) : Prop :=
  ∀ t ∈ PP.δ, t.p ∈ U → t.q ∈ U → t.p' ∈ U ∧ t.q' ∈ U

theorem restrictTo_lift_step (hU : Closed PP U) {C : Multiset U} {D : Multiset T}
    (h : PP.Step (C.map Subtype.val) D) :
    ∃ C', D = C'.map Subtype.val ∧ (PP.restrictTo U).Step C C' := by
  rcases h with rfl | ⟨t, ht, hf⟩
  · exact ⟨C, rfl, .inl rfl⟩
  · have hp : t.p ∈ C.map Subtype.val :=
      Multiset.mem_of_le hf.1 (by simp [Transition.pre])
    have hq : t.q ∈ C.map Subtype.val :=
      Multiset.mem_of_le hf.1 (by simp [Transition.pre])
    have hpU : t.p ∈ U := by
      obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 hp; exact ha ▸ a.2
    have hqU : t.q ∈ U := by
      obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 hq; exact ha ▸ a.2
    obtain ⟨hp'U, hq'U⟩ := hU t ht hpU hqU
    let t' : Transition U := ⟨⟨t.p, hpU⟩, ⟨t.q, hqU⟩, ⟨t.p', hp'U⟩, ⟨t.q', hq'U⟩⟩
    have htt' : trMap Subtype.val t' = t := rfl
    have hpre : t'.pre ≤ C := by
      rw [← Multiset.map_le_map_iff Subtype.val_injective, ← trMap_pre, htt']
      exact hf.1
    let C' := C - t'.pre + t'.post
    have hf' : t'.Fires C C' := ⟨hpre, rfl⟩
    refine ⟨C', ?_, .inr ⟨t', by simpa [restrictTo, htt'] using ht, hf'⟩⟩
    have := fires_map hf' Subtype.val
    rw [htt'] at this
    exact fires_unique hf this

theorem restrictTo_lift_reach (hU : Closed PP U) {C : Multiset U} {D : Multiset T}
    (h : Reach PP.Step (C.map Subtype.val) D) :
    ∃ C', D = C'.map Subtype.val ∧ Reach (PP.restrictTo U).Step C C' := by
  induction h with
  | refl => exact ⟨C, rfl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨C₁, rfl, h₁⟩ := ih
    obtain ⟨C₂, rfl, h₂⟩ := restrictTo_lift_step hU hs
    exact ⟨C₂, rfl, h₁.tail h₂⟩

open Classical in
theorem restrictTo_out (C : Multiset U) :
    (PP.restrictTo U).out C = PP.out (C.map Subtype.val) := by
  simp [out, restrictTo]

/-- Transfer of the reachability characterization to the restricted protocol. -/
theorem restrictTo_reach_stable (hU : Closed PP U) {C₀ : Multiset U} {b : Bool}
    (h : ∀ c, Reach PP.Step (C₀.map Subtype.val) c →
      ∃ d, Reach PP.Step c d ∧ StableOut PP.Step PP.out b d) :
    ∀ C, Reach (PP.restrictTo U).Step C₀ C →
      ∃ D, Reach (PP.restrictTo U).Step C D ∧
        StableOut (PP.restrictTo U).Step (PP.restrictTo U).out b D := by
  intro C hC
  obtain ⟨d, hd, hst⟩ := h _ (restrictTo_reach_map hC)
  obtain ⟨D, rfl, hD⟩ := restrictTo_lift_reach hU hd
  refine ⟨D, hD, fun E hE => ?_⟩
  rw [restrictTo_out]
  exact hst _ (restrictTo_reach_map hE)

end PProtocol

/-! ### Output broadcast -/

section Bcast

variable {T : Type*} [DecidableEq T]

/-- The underlying transition of a transition with opinion bits. -/
def trFst (t : Transition (T × Bool)) : Transition T := trMap Prod.fst t

/-- The output broadcast construction of Appendix B.3: for every transition
`(q₁, q₂ ↦ q₁', q₂')` of `δ`, and for `(q₁, q₂) = (q₁', q₂')`, we have
`(q₁, ∗), (q₂, ∗) ↦ (q₁', b), (q₂', b)` if the output flag with value `b` is among `q₁', q₂'`
(`ofv` reads the value of the output flag from a state), and otherwise
`(q₁, b₁), (q₂, b₂) ↦ (q₁', b₁), (q₂', b₂)`. -/
def bcast (δ : Set (Transition T)) (ofv : T → Option Bool) : Set (Transition (T × Bool)) :=
  {t | (trFst t ∈ δ ∨ (t.p'.1 = t.p.1 ∧ t.q'.1 = t.q.1)) ∧
    ((∃ b, (ofv t.p'.1 = some b ∨ ofv t.q'.1 = some b) ∧ t.p'.2 = b ∧ t.q'.2 = b) ∨
      (ofv t.p'.1 = none ∧ ofv t.q'.1 = none ∧ t.p'.2 = t.p.2 ∧ t.q'.2 = t.q.2))}

variable {δ : Set (Transition T)} {ofv : T → Option Bool}

/-- Steps of the broadcast protocol project to steps (or stutters) of the base protocol. -/
theorem bcast_step_fst {c c' : Multiset (T × Bool)} (h : MStep (bcast δ ofv) c c') :
    c.map Prod.fst = c'.map Prod.fst ∨ MStep δ (c.map Prod.fst) (c'.map Prod.fst) := by
  obtain ⟨t, ⟨hδ | ⟨h1, h2⟩, -⟩, hf⟩ := h
  · exact .inr ⟨_, hδ, fires_map hf _⟩
  · left
    have := fires_map hf Prod.fst
    have hs : (trMap Prod.fst t).Silent := by
      simp [Transition.Silent, Transition.pre, Transition.post, trMap, h1, h2]
    exact (this.eq_of_silent hs).symm

theorem bcast_reach_fst {c c' : Multiset (T × Bool)}
    (h : Relation.ReflTransGen (fun c c' => c = c' ∨ MStep (bcast δ ofv) c c') c c') :
    Relation.ReflTransGen (fun c c' => c = c' ∨ MStep δ c c') (c.map Prod.fst)
      (c'.map Prod.fst) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    rcases hs with rfl | hs
    · exact ih
    · rcases bcast_step_fst hs with he | hs
      · exact he ▸ ih
      · exact ih.tail (.inr hs)

/-- Choice of opinion bits for the post-states of a lifted transition. -/
def bcastBits (ofv : T → Option Bool) (p' q' : T) (b₁ b₂ : Bool) : Bool × Bool :=
  match ofv p', ofv q' with
  | some b, _ => (b, b)
  | none, some b => (b, b)
  | none, none => (b₁, b₂)

omit [DecidableEq T] in
theorem bcastBits_mem (t : Transition T) (ht : t ∈ δ ∨ (t.p' = t.p ∧ t.q' = t.q)) (b₁ b₂ : Bool) :
    (⟨(t.p, b₁), (t.q, b₂), (t.p', (bcastBits ofv t.p' t.q' b₁ b₂).1),
      (t.q', (bcastBits ofv t.p' t.q' b₁ b₂).2)⟩ : Transition (T × Bool)) ∈ bcast δ ofv := by
  refine ⟨ht, ?_⟩
  simp only [bcastBits]
  split
  · next b h => exact .inl ⟨b, .inl h, rfl, rfl⟩
  · next b h1 h2 => exact .inl ⟨b, .inr h2, rfl, rfl⟩
  · next h1 h2 => exact .inr ⟨h1, h2, rfl, rfl⟩

theorem exists_le_map_fst {c : Multiset (T × Bool)} {x y : T}
    (h : ({x, y} : Multiset T) ≤ c.map Prod.fst) :
    ∃ b₁ b₂, ({(x, b₁), (y, b₂)} : Multiset (T × Bool)) ≤ c := by
  have hx : x ∈ c.map Prod.fst := Multiset.mem_of_le h (by simp)
  obtain ⟨⟨x', b₁⟩, hx1, rfl⟩ := Multiset.mem_map.1 hx
  have h2 : ({y} : Multiset T) ≤ (c.erase (x', b₁)).map Prod.fst := by
    rw [Multiset.map_erase_of_mem _ _ hx1]
    rw [← Multiset.cons_erase hx, Multiset.insert_eq_cons] at h
    exact (Multiset.cons_le_cons_iff _).1 h
  obtain ⟨⟨y', b₂⟩, hy1, rfl⟩ := Multiset.mem_map.1 (Multiset.singleton_le.1 h2)
  refine ⟨b₁, b₂, ?_⟩
  rw [Multiset.insert_eq_cons, ← Multiset.cons_erase hx1, Multiset.cons_le_cons_iff]
  exact Multiset.singleton_le.2 hy1

/-- Base steps (and stutters) lift to the broadcast protocol (with some choice of bits). -/
theorem bcast_lift_trans {c : Multiset (T × Bool)} {d' : Multiset T} (t : Transition T)
    (ht : t ∈ δ ∨ (t.p' = t.p ∧ t.q' = t.q)) (hf : t.Fires (c.map Prod.fst) d') :
    ∃ c', MStep (bcast δ ofv) c c' ∧ c'.map Prod.fst = d' := by
  obtain ⟨b₁, b₂, hle⟩ := exists_le_map_fst (x := t.p) (y := t.q) hf.1
  let t' : Transition (T × Bool) := ⟨(t.p, b₁), (t.q, b₂),
    (t.p', (bcastBits ofv t.p' t.q' b₁ b₂).1), (t.q', (bcastBits ofv t.p' t.q' b₁ b₂).2)⟩
  have hf' : t'.Fires c (c - t'.pre + t'.post) := ⟨hle, rfl⟩
  refine ⟨_, ⟨t', bcastBits_mem t ht b₁ b₂, hf'⟩, ?_⟩
  exact fires_unique (fires_map hf' Prod.fst) hf

theorem bcast_lift_step {c : Multiset (T × Bool)} {d' : Multiset T}
    (h : MStep δ (c.map Prod.fst) d') :
    ∃ c', MStep (bcast δ ofv) c c' ∧ c'.map Prod.fst = d' := by
  obtain ⟨t, ht, hf⟩ := h
  exact bcast_lift_trans t (.inl ht) hf

theorem bcast_lift_reach {c : Multiset (T × Bool)} {d' : Multiset T}
    (h : Relation.ReflTransGen (fun c c' => c = c' ∨ MStep δ c c') (c.map Prod.fst) d') :
    ∃ c', Relation.ReflTransGen (fun c c' => c = c' ∨ MStep (bcast δ ofv) c c') c c' ∧
      c'.map Prod.fst = d' := by
  induction h with
  | refl => exact ⟨c, .refl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨c₁, h₁, rfl⟩ := ih
    rcases hs with he | hs
    · exact ⟨c₁, h₁, he⟩
    · obtain ⟨c₂, h₂, rfl⟩ := bcast_lift_step hs
      exact ⟨c₂, h₁.tail (.inr h₂), rfl⟩

/-- If some agent holds the output flag with value `b`, then `b` can be spread to all agents
without changing the underlying configuration. -/
theorem bcast_spread {c : Multiset (T × Bool)} {s : T} {β b : Bool} (hs : (s, β) ∈ c)
    (hof : ofv s = some b) (hc : 2 ≤ Multiset.card c) :
    ∃ c', Relation.ReflTransGen (fun c c' => c = c' ∨ MStep (bcast δ ofv) c c') c c' ∧
      c'.map Prod.fst = c.map Prod.fst ∧ ∀ x ∈ c', x.2 = b := by
  -- one spreading step with partner `y`
  have step : ∀ (c : Multiset (T × Bool)) (β : Bool) (y : T × Bool),
      ({(s, β), y} : Multiset (T × Bool)) ≤ c → ∃ c', MStep (bcast δ ofv) c c' ∧
        c'.map Prod.fst = c.map Prod.fst ∧ (s, b) ∈ c' ∧
        c'.countP (fun x => x.2 ≠ b) + (({(s, β), y} : Multiset (T × Bool)).countP
          (fun x => x.2 ≠ b)) = c.countP (fun x => x.2 ≠ b) := by
    intro c β y hle
    let t : Transition (T × Bool) := ⟨(s, β), y, (s, b), (y.1, b)⟩
    have ht : t ∈ bcast δ ofv := ⟨.inr ⟨rfl, rfl⟩, .inl ⟨b, .inl hof, rfl, rfl⟩⟩
    obtain ⟨c', hc'⟩ : ∃ c', c' = c - t.pre + t.post := ⟨_, rfl⟩
    have hf : t.Fires c c' := ⟨hle, hc'⟩
    have hadd := (fires_iff_add.1 hf).2
    refine ⟨c', ⟨t, ht, hf⟩, ?_, ?_, ?_⟩
    · have hs : (trMap Prod.fst t).Silent := by
        simp [Transition.Silent, Transition.pre, Transition.post, trMap, t]
      exact (fires_map hf Prod.fst).eq_of_silent hs
    · rw [hc']; exact Multiset.mem_add.2 (.inr (by simp [t, Transition.post]))
    · have := congrArg (Multiset.countP (fun x : T × Bool => x.2 ≠ b)) hadd
      rw [Multiset.countP_add, Multiset.countP_add] at this
      have h0 : t.post.countP (fun x : T × Bool => x.2 ≠ b) = 0 := by
        simp [t, Transition.post, Multiset.countP_eq_zero]
      rw [h0, add_zero] at this
      exact this
  -- induction on the number of agents with the wrong bit
  suffices ∀ m (c : Multiset (T × Bool)) (β : Bool), c.countP (fun x => x.2 ≠ b) = m →
      (s, β) ∈ c → 2 ≤ Multiset.card c →
      ∃ c', Relation.ReflTransGen (fun c c' => c = c' ∨ MStep (bcast δ ofv) c c') c c' ∧
        c'.map Prod.fst = c.map Prod.fst ∧ ∀ x ∈ c', x.2 = b from this _ c β rfl hs hc
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro c β hm hs hc
    by_cases hall : ∀ x ∈ c, x.2 = b
    · exact ⟨c, .refl, rfl, hall⟩
    push Not at hall
    obtain ⟨x, hx, hxb⟩ := hall
    -- choose a partner `y` with `{(s, β), y} ≤ c` such that one of them has the wrong bit
    obtain ⟨y, hle, hwrong⟩ : ∃ y, ({(s, β), y} : Multiset (T × Bool)) ≤ c ∧
        (β ≠ b ∨ y.2 ≠ b) := by
      by_cases hxs : x = (s, β)
      · subst hxs
        have hne : c.erase (s, β) ≠ 0 := by
          intro h0
          have := Multiset.card_erase_of_mem hs
          rw [h0] at this; simp at this; omega
        obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hne
        refine ⟨y, ?_, .inl hxb⟩
        rw [Multiset.insert_eq_cons, ← Multiset.cons_erase hs, Multiset.cons_le_cons_iff]
        exact Multiset.singleton_le.2 hy
      · refine ⟨x, ?_, .inr hxb⟩
        rw [Multiset.insert_eq_cons, ← Multiset.cons_erase hs, Multiset.cons_le_cons_iff]
        exact Multiset.singleton_le.2 ((Multiset.mem_erase_of_ne hxs).2 hx)
    obtain ⟨c₁, hst, hmap, hs₁, hcnt⟩ := step c β y hle
    have hpos : 0 < ({(s, β), y} : Multiset (T × Bool)).countP (fun x => x.2 ≠ b) := by
      rcases hwrong with h | h <;> simp [Multiset.countP_pos, h]
    have hcard : Multiset.card c₁ = Multiset.card c := by
      obtain ⟨t, -, hf⟩ := hst; exact hf.card_eq
    obtain ⟨c', h', hmap', hall'⟩ := ih _ (by omega) c₁ b rfl hs₁ (hcard ▸ hc)
    exact ⟨c', Relation.ReflTransGen.head (.inr hst) h', hmap'.trans hmap, hall'⟩

end Bcast

end Podc.PPDoubleExpThresholds
