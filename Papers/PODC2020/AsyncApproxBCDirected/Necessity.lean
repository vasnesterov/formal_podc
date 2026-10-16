import Papers.PODC2020.AsyncApproxBCDirected.AsyncModel
import Papers.PODC2020.AsyncApproxBCDirected.Graph

/-!
# Necessity of 3-reach (Theorem 18, Appendix B)

If `G` violates 3-reach, no algorithm solves asynchronous Byzantine approximate consensus on `G`
(`threeReach_of_solves`).

Proof (the paper's indistinguishability argument, made precise). Let `F, Fu, Fv, u, v` witness the
failure of 3-reach and put `Rv = reach_v(F ∪ Fv)`, `Ru = reach_u(F ∪ Fu)` (disjoint). Every
in-neighbour of `Rv` outside `Rv` lies in `F ∪ Fv`.
* `e₁`: `Fv` Byzantine and silent, all inputs `0`, round-robin delivery (fair). By termination
  and validity, `v` decides `0` at some time `T₁`.
* `e₂`: `Fu` Byzantine and silent, all inputs `2ε`; `u` decides `2ε` at time `T₂`.
* `e₃`: `F` Byzantine; inputs `0` on `Rv` and `2ε` on `Ru`. First replay the first `T₁` events
  of `e₁` restricted to deliveries into `Rv` (messages from `F` are injected by the Byzantine
  nodes, messages from `Fv` are delayed), then the first `T₂` events of `e₂` restricted to `Ru`.
  Then `v` decided `0` and `u` decided `2ε`, violating convergence.

The paper uses inputs `0` and `ε`; with the non-strict reading of "within `ε`" of Definition 1
this gives no contradiction, so we use `2ε`. More generally (`threeReach_of_solvesOn`), any two
admissible inputs `a, b` with `b − a > ε` work; this covers the setting of Section 4.6 where the
inputs are known to lie in `[0, K]` (with `K > ε`; for `K ≤ ε` the problem is trivial).
-/

open Finset

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

variable {V M S : Type*} [DecidableEq V] {A : Algorithm V M S} {G : Digraph V} [DecidableRel G.Adj]

/-- Two configurations agree on the node set `R`: states, decisions, and the channels inside `R`. -/
def Agree (R : Finset V) (C C' : Config V M S) : Prop :=
  (∀ y ∈ R, C.st y = C'.st y ∧ C.dec y = C'.dec y) ∧ ∀ x ∈ R, ∀ y ∈ R, C.chan x y = C'.chan x y

/-- Two configurations agree outside `R`. -/
def AgreeOut (R : Finset V) (C C' : Config V M S) : Prop :=
  (∀ y ∉ R, C.st y = C'.st y ∧ C.dec y = C'.dec y) ∧ ∀ x ∉ R, ∀ y ∉ R, C.chan x y = C'.chan x y

theorem AgreeOut.refl {R : Finset V} (C : Config V M S) : AgreeOut R C C :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl⟩

theorem AgreeOut.trans {R : Finset V} {C₁ C₂ C₃ : Config V M S} (h₁ : AgreeOut R C₁ C₂)
    (h₂ : AgreeOut R C₂ C₃) : AgreeOut R C₁ C₃ :=
  ⟨fun y hy => ⟨(h₁.1 y hy).1.trans (h₂.1 y hy).1, (h₁.1 y hy).2.trans (h₂.1 y hy).2⟩,
    fun x hx y hy => (h₁.2 x hx y hy).trans (h₂.2 x hx y hy)⟩

/-- Agreement on `R'` is transported along agreement outside `R` when `R' ∩ R = ∅`. -/
theorem Agree.of_agreeOut {R R' : Finset V} {C C₁ C₂ : Config V M S} (h : Agree R' C C₁)
    (h' : AgreeOut R C₁ C₂) (hd : Disjoint R' R) : Agree R' C C₂ :=
  ⟨fun y hy => ⟨(h.1 y hy).1.trans (h'.1 y (disjoint_left.mp hd hy)).1,
      (h.1 y hy).2.trans (h'.1 y (disjoint_left.mp hd hy)).2⟩,
    fun x hx y hy => (h.2 x hx y hy).trans (h'.2 x (disjoint_left.mp hd hx) y
      (disjoint_left.mp hd hy))⟩

/-- The event of the target execution simulating the source event `e` (from configuration `C`)
on the node set `R`: deliveries into `R` are replayed, those from Byzantine (in the target)
senders are injected by the adversary; everything else is skipped. -/
def proj (R B' : Finset V) (C : Config V M S) : Event V M → Event V M
  | .deliver x y =>
    if y ∈ R then
      match C.chan x y with
      | [] => .skip
      | m :: _ => if x ∈ B' then .byz x y m else .deliver x y
    else .skip
  | _ => .skip

/-- Source invariant: only correct nodes have non-empty channels, and only along links. -/
def ChanOK (G : Digraph V) (B : Finset V) (C : Config V M S) : Prop :=
  ∀ x y, C.chan x y ≠ [] → x ∉ B ∧ G.Adj x y ∧ x ≠ y

theorem sendTo_ne_nil {B : Finset V} {y b : V} {outs : List (V × M)}
    (h : sendTo G B y outs b ≠ []) : b ∉ B ∧ G.Adj y b ∧ y ≠ b := by
  unfold sendTo at h; split_ifs at h with h'
  · exact h'
  · exact absurd rfl h

theorem chanOK_process {B : Finset V} {C : Config V M S} (hC : ChanOK G B C) {y x : V} {m : M}
    (hy : y ∉ B) : ChanOK G B (process A G B C y x m) := by
  intro a b h
  simp only [process] at h
  split_ifs at h with hay
  · subst hay
    by_cases h1 : C.chan a b = []
    · rw [h1, List.nil_append] at h
      exact ⟨hy, (sendTo_ne_nil h).2⟩
    · exact hC a b h1
  · exact hC a b h

theorem chanOK_pop {B : Finset V} {C : Config V M S} (hC : ChanOK G B C) {x y : V} {m : M}
    {rest : List M} (hxy : C.chan x y = m :: rest) : ChanOK G B (C.pop x y rest) := by
  intro a b h
  simp only [Config.pop] at h
  split_ifs at h with hab
  · obtain ⟨rfl, rfl⟩ := hab; exact hC a b (by simp [hxy])
  · exact hC a b h

theorem chanOK_step {B : Finset V} {C : Config V M S} (hC : ChanOK G B C) (e : Event V M) :
    ChanOK G B (step A G B C e) := by
  cases e with
  | deliver x y =>
    simp only [step]
    split
    · exact hC
    · rename_i m rest hxy
      split_ifs with hy
      · exact hC
      · exact chanOK_process (chanOK_pop hC hxy) hy
  | byz x y m =>
    simp only [step]
    split_ifs with h
    · exact chanOK_process hC h.2.1
    · exact hC
  | skip => exact hC

theorem chanOK_init {B : Finset V} (inp : V → ℝ) : ChanOK G B (init A G B inp) := by
  intro x y h
  simp only [init] at h
  split_ifs at h with hx
  · exact absurd rfl h
  · exact ⟨hx, (sendTo_ne_nil h).2⟩

theorem chanOK_run {B : Finset V} (inp : V → ℝ) (ev : ℕ → Event V M) (t : ℕ) :
    ChanOK G B (run A G B inp ev t) := by
  induction t with
  | zero => exact chanOK_init inp
  | succ t ih => exact chanOK_step ih _

section Sim

variable {B B' R : Finset V}

theorem agree_process (hRB : ∀ y ∈ R, y ∉ B) (hRB' : ∀ y ∈ R, y ∉ B') {C C' : Config V M S}
    (h : Agree R C C') {y x : V} (hy : y ∈ R) (m : M) :
    Agree R (process A G B C y x m) (process A G B' C' y x m) := by
  have hst := (h.1 y hy).1
  refine ⟨fun z hz => ?_, fun a ha b hb => ?_⟩
  · by_cases hzy : z = y
    · subst hzy; simp [process, hst, (h.1 z hz).2]
    · simp [process, hzy, (h.1 z hz).1, (h.1 z hz).2]
  · simp only [process]
    split_ifs with hay
    · subst hay
      rw [h.2 a ha b hb, hst]
      congr 1
      simp only [sendTo, hRB b hb, hRB' b hb, not_false_eq_true, true_and]
    · exact h.2 a ha b hb

theorem agreeOut_process {C : Config V M S} {y x : V} (hy : y ∈ R) (m : M) :
    AgreeOut R C (process A G B' C y x m) := by
  refine ⟨fun z hz => ?_, fun a ha b _ => ?_⟩
  · have : z ≠ y := fun h => hz (h ▸ hy)
    simp [process, this]
  · have : a ≠ y := fun h => ha (h ▸ hy)
    simp [process, this]

theorem agree_pop_right {C C' : Config V M S} (h : Agree R C C') {x y : V} (hy : x ∉ R)
    (rest : List M) : Agree R C (C'.pop x y rest) :=
  ⟨h.1, fun a ha b hb => by
    have : ¬ (a = x ∧ b = y) := fun h' => hy (h'.1 ▸ ha)
    simp [Config.pop, this, h.2 a ha b hb]⟩

theorem agree_pop_left {C C' : Config V M S} (h : Agree R C C') {x y : V} (hy : x ∉ R)
    (rest : List M) : Agree R (C.pop x y rest) C' :=
  ⟨h.1, fun a ha b hb => by
    have : ¬ (a = x ∧ b = y) := fun h' => hy (h'.1 ▸ ha)
    simp [Config.pop, this, h.2 a ha b hb]⟩

/-- One simulation step: the source executes a non-Byzantine event, the target executes its
projection on `R`. Agreement on `R` is preserved, provided every in-neighbour of `R` outside `R`
is Byzantine in the source (hence silent) or in the target (hence simulable). -/
theorem agree_step (hRB : ∀ y ∈ R, y ∉ B) (hRB' : ∀ y ∈ R, y ∉ B')
    (hcl : ∀ x y, G.Adj x y → x ≠ y → y ∈ R → x ∉ R → x ∈ B ∨ x ∈ B')
    {C C' : Config V M S} (hC : ChanOK G B C) (h : Agree R C C') (e : Event V M)
    (he : ∀ x y m, e ≠ .byz x y m) :
    Agree R (step A G B C e) (step A G B' C' (proj R B' C e)) := by
  cases e with
  | byz x y m => exact absurd rfl (he x y m)
  | skip => exact h
  | deliver x y =>
    by_cases hy : y ∈ R
    · simp only [proj, hy, ite_true]
      rcases hxy : C.chan x y with _ | ⟨m, rest⟩
      · simp only [step, hxy]; exact h
      · have hyB : y ∉ B := hRB y hy
        have hyB' : y ∉ B' := hRB' y hy
        simp only [step, hxy, hyB, ite_false]
        by_cases hx : x ∈ R
        · have hxB' : x ∉ B' := hRB' x hx
          simp only [hxB', ite_false, ← h.2 x hx y hy, hxy, hyB', ite_false]
          apply agree_process hRB hRB' _ hy
          exact ⟨h.1, fun a ha b hb => by
            simp only [Config.pop]
            split_ifs
            · rfl
            · exact h.2 a ha b hb⟩
        · obtain ⟨hxB, hadj, hne⟩ := hC x y (by simp [hxy])
          have hxB' : x ∈ B' := (hcl x y hadj hne hy hx).resolve_left hxB
          simp only [hxB', ite_true, hyB', not_false_eq_true, hadj, ne_eq, hne,
            and_self, ite_true]
          exact agree_process hRB hRB' (agree_pop_left h hx rest) hy m
    · simp only [proj, hy, ite_false, step]
      refine ⟨fun z hz => ?_, fun a ha b hb => ?_⟩
      · split
        · exact h.1 z hz
        · split_ifs
          · exact h.1 z hz
          · have hzy : z ≠ y := fun h' => hy (h' ▸ hz)
            simp [process, Config.pop, hzy, h.1 z hz]
      · split
        · exact h.2 a ha b hb
        · split_ifs
          · exact h.2 a ha b hb
          · have hay : a ≠ y := fun h' => hy (h' ▸ ha)
            have hby : ¬ (a = x ∧ b = y) := fun h' => hy (h'.2 ▸ hb)
            simp [process, Config.pop, hay, hby, h.2 a ha b hb]

/-- The projected target step changes nothing outside `R`. -/
theorem agreeOut_step_proj {C C' : Config V M S} (e : Event V M) :
    AgreeOut R C' (step A G B' C' (proj R B' C e)) := by
  cases e with
  | byz => exact AgreeOut.refl _
  | skip => exact AgreeOut.refl _
  | deliver x y =>
    by_cases hy : y ∈ R
    · simp only [proj, hy, ite_true]
      rcases C.chan x y with _ | ⟨m, rest⟩
      · exact AgreeOut.refl _
      · split_ifs with hx
        · simp only [step]
          split_ifs
          · exact agreeOut_process hy m
          · exact AgreeOut.refl _
        · simp only [step]
          split
          · exact AgreeOut.refl _
          · split_ifs
            · exact AgreeOut.refl _
            · rename_i m' rest' _ _
              refine AgreeOut.trans (C₂ := C'.pop x y rest')
                ⟨fun z _ => ⟨rfl, rfl⟩, fun a _ b hb => ?_⟩ (agreeOut_process hy m')
              have : ¬ (a = x ∧ b = y) := fun h' => hb (h'.2 ▸ hy)
              simp [Config.pop, this]
    · simp only [proj, hy, ite_false]; exact AgreeOut.refl _

/-- A whole simulation phase: if the target events at times `T₀ + k` (`k < K`) are the
projections of the source events, agreement on `R` propagates from time `0`/`T₀` to `K`/`T₀+K`,
and nothing outside `R` changes in the target. -/
theorem sim_phase (hRB : ∀ y ∈ R, y ∉ B) (hRB' : ∀ y ∈ R, y ∉ B')
    (hcl : ∀ x y, G.Adj x y → x ≠ y → y ∈ R → x ∉ R → x ∈ B ∨ x ∈ B')
    (inp inp' : V → ℝ) (ev ev' : ℕ → Event V M) (hev : ∀ t x y m, ev t ≠ .byz x y m)
    (T₀ K : ℕ) (hproj : ∀ k < K, ev' (T₀ + k) = proj R B' (run A G B inp ev k) (ev k))
    (h0 : Agree R (run A G B inp ev 0) (run A G B' inp' ev' T₀)) :
    Agree R (run A G B inp ev K) (run A G B' inp' ev' (T₀ + K)) ∧
      AgreeOut R (run A G B' inp' ev' T₀) (run A G B' inp' ev' (T₀ + K)) := by
  induction K with
  | zero => exact ⟨h0, AgreeOut.refl _⟩
  | succ K ih =>
    obtain ⟨ih1, ih2⟩ := ih fun k hk => hproj k (by omega)
    have e := hproj K (by omega)
    have hrun : run A G B' inp' ev' (T₀ + (K + 1)) =
        step A G B' (run A G B' inp' ev' (T₀ + K)) (ev' (T₀ + K)) := rfl
    rw [hrun, e]
    exact ⟨agree_step hRB hRB' hcl (chanOK_run inp ev K) ih1 (ev K) (hev K),
      ih2.trans (agreeOut_step_proj _)⟩

end Sim

/-- Round-robin delivery over all ordered pairs: a fair schedule without Byzantine events. -/
noncomputable def roundRobin [Fintype V] : ℕ → Event V M := fun t =>
  let e := (Fintype.equivFin (V × V)).symm
  let N := Fintype.card (V × V)
  if h : 0 < N then
    let p := e ⟨t % N, Nat.mod_lt _ h⟩
    .deliver p.1 p.2
  else .skip

theorem roundRobin_fair [Fintype V] {B : Finset V} (inp : V → ℝ) :
    Fair A G B inp (roundRobin (V := V) (M := M)) := by
  intro x y _ _ t _
  have hN : 0 < Fintype.card (V × V) := Fintype.card_pos_iff.mpr ⟨(x, y)⟩
  set i := (Fintype.equivFin (V × V) (x, y)).val
  have hi : i < Fintype.card (V × V) := (Fintype.equivFin (V × V) (x, y)).isLt
  refine ⟨Fintype.card (V × V) * t + i, by nlinarith, ?_⟩
  have hmod : (Fintype.card (V × V) * t + i) % Fintype.card (V × V) = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  have h' : (Fintype.equivFin (V × V)).symm
      ⟨(Fintype.card (V × V) * t + i) % Fintype.card (V × V), Nat.mod_lt _ hN⟩ = (x, y) := by
    rw [Equiv.symm_apply_eq]; exact Fin.ext hmod
  simp only [roundRobin, hN, ↓reduceDIte, h']

theorem roundRobin_ne_byz [Fintype V] (t : ℕ) (x y : V) (m : M) :
    roundRobin (V := V) (M := M) t ≠ .byz x y m := by
  simp only [roundRobin]; split <;> simp

/-- **Theorem 18** (necessity of 3-reach), for any input range containing two values more than
`ε` apart: if some algorithm solves asynchronous approximate Byzantine consensus on `G` with up
to `f` faults for inputs in `I`, then `G` satisfies 3-reach. -/
theorem threeReach_of_solvesOn [Fintype V] {f : ℕ} {ε : ℝ} {I : Set ℝ} {a b : ℝ} (ha : a ∈ I)
    (hb : b ∈ I) (hab : ε < b - a) (hA : SolvesOn I A G f ε) : ThreeReach G f := by
  classical
  intro F Fu Fv u v hF hFu hFv hu hv
  by_contra hcon
  push Not at hcon
  set Rv : Finset V := univ.filter fun w => Reaches G (F ∪ Fv) w v
  set Ru : Finset V := univ.filter fun w => Reaches G (F ∪ Fu) w u
  have hdis : Disjoint Rv Ru := disjoint_left.mpr fun w h1 h2 => by
    simp only [Rv, Ru, mem_filter, mem_univ, true_and] at h1 h2; exact hcon w h1 h2
  have hvR : v ∈ Rv := by simp [Rv, Reaches.refl hv]
  have huR : u ∈ Ru := by simp [Ru, Reaches.refl hu]
  have hRvF : ∀ y ∈ Rv, y ∉ F ∧ y ∉ Fv := fun y hy => by
    simp only [Rv, mem_filter, mem_univ, true_and] at hy
    exact ⟨fun h => hy.1 (mem_union_left _ h), fun h => hy.1 (mem_union_right _ h)⟩
  have hRuF : ∀ y ∈ Ru, y ∉ F ∧ y ∉ Fu := fun y hy => by
    simp only [Ru, mem_filter, mem_univ, true_and] at hy
    exact ⟨fun h => hy.1 (mem_union_left _ h), fun h => hy.1 (mem_union_right _ h)⟩
  have hclv : ∀ x y, G.Adj x y → x ≠ y → y ∈ Rv → x ∉ Rv → x ∈ Fv ∨ x ∈ F := by
    intro x y e _ hy hx
    by_contra h
    simp only [not_or] at h
    simp only [Rv, mem_filter, mem_univ, true_and] at hy hx
    exact hx (hy.head e (by simp [h.1, h.2]))
  have hclu : ∀ x y, G.Adj x y → x ≠ y → y ∈ Ru → x ∉ Ru → x ∈ Fu ∨ x ∈ F := by
    intro x y e _ hy hx
    by_contra h
    simp only [not_or] at h
    simp only [Ru, mem_filter, mem_univ, true_and] at hy hx
    exact hx (hy.head e (by simp [h.1, h.2]))
  -- execution e₁
  set inp₁ : V → ℝ := fun _ => a
  set ev₁ : ℕ → Event V M := roundRobin
  obtain ⟨-, hval₁, hterm₁⟩ := hA Fv hFv inp₁ (fun _ => ha) ev₁
  obtain ⟨T₁, y₁, hy₁⟩ := hterm₁ (roundRobin_fair inp₁) v (fun h => hv (mem_union_right _ h))
  have hy₁0 : y₁ = a := by
    obtain ⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ := hval₁ T₁ v y₁ (fun h => hv (mem_union_right _ h)) hy₁
    simp only [inp₁] at h1 h2; linarith
  -- execution e₂
  set inp₂ : V → ℝ := fun _ => b
  set ev₂ : ℕ → Event V M := roundRobin
  obtain ⟨-, hval₂, hterm₂⟩ := hA Fu hFu inp₂ (fun _ => hb) ev₂
  obtain ⟨T₂, y₂, hy₂⟩ := hterm₂ (roundRobin_fair inp₂) u (fun h => hu (mem_union_right _ h))
  have hy₂ε : y₂ = b := by
    obtain ⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ := hval₂ T₂ u y₂ (fun h => hu (mem_union_right _ h)) hy₂
    simp only [inp₂] at h1 h2; linarith
  -- execution e₃
  set inp₃ : V → ℝ := fun w => if w ∈ Ru then b else a
  set ev₃ : ℕ → Event V M := fun t =>
    if t < T₁ then proj Rv F (run A G Fv inp₁ ev₁ t) (ev₁ t)
    else if t < T₁ + T₂ then proj Ru F (run A G Fu inp₂ ev₂ (t - T₁)) (ev₂ (t - T₁))
    else .skip
  obtain ⟨hconv₃, -, -⟩ := hA F hF inp₃ (fun w => by simp only [inp₃]; split_ifs <;> assumption)
    ev₃
  -- initial agreements
  have h0v : Agree Rv (run A G Fv inp₁ ev₁ 0) (run A G F inp₃ ev₃ 0) := by
    refine ⟨fun y hy => ?_, fun x hx y hy => ?_⟩
    · have : y ∉ Ru := disjoint_left.mp hdis hy
      simp [run, init, inp₃, inp₁, this]
    · have hxu : x ∉ Ru := disjoint_left.mp hdis hx
      simp [run, init, inp₃, inp₁, hxu, (hRvF x hx).1, (hRvF x hx).2, sendTo, (hRvF y hy).1,
        (hRvF y hy).2]
  have h0u : Agree Ru (run A G Fu inp₂ ev₂ 0) (run A G F inp₃ ev₃ 0) := by
    refine ⟨fun y hy => ?_, fun x hx y hy => ?_⟩
    · simp [run, init, inp₃, inp₂, hy]
    · simp [run, init, inp₃, inp₂, hx, (hRuF x hx).1, (hRuF x hx).2, sendTo, (hRuF y hy).1,
        (hRuF y hy).2]
  -- phase 1
  obtain ⟨p1a, p1b⟩ := sim_phase (A := A) (fun y hy => (hRvF y hy).2) (fun y hy => (hRvF y hy).1) hclv
    inp₁ inp₃ ev₁ ev₃ (fun t => roundRobin_ne_byz t) 0 T₁
    (fun k hk => by simp only [ev₃, Nat.zero_add, hk, ite_true]) (by simpa using h0v)
  -- phase 2
  have h1u : Agree Ru (run A G Fu inp₂ ev₂ 0) (run A G F inp₃ ev₃ T₁) :=
    h0u.of_agreeOut (by simpa using p1b) hdis.symm
  obtain ⟨p2a, p2b⟩ := sim_phase (A := A) (fun y hy => (hRuF y hy).2) (fun y hy => (hRuF y hy).1) hclu
    inp₂ inp₃ ev₂ ev₃ (fun t => roundRobin_ne_byz t) T₁ T₂
    (fun k hk => by
      simp only [ev₃, show ¬ (T₁ + k < T₁) by omega, ite_false,
        show T₁ + k < T₁ + T₂ by omega, ite_true, Nat.add_sub_cancel_left]) h1u
  have h2v : Agree Rv (run A G Fv inp₁ ev₁ T₁) (run A G F inp₃ ev₃ (T₁ + T₂)) :=
    (by simpa using p1a : Agree Rv _ _).of_agreeOut p2b hdis
  have hdv : (run A G F inp₃ ev₃ (T₁ + T₂)).dec v = some a := by
    rw [← (h2v.1 v hvR).2, hy₁, hy₁0]
  have hdu : (run A G F inp₃ ev₃ (T₁ + T₂)).dec u = some b := by
    rw [← (p2a.1 u huR).2, hy₂, hy₂ε]
  have := hconv₃ (T₁ + T₂) v u a b (fun h => hv (mem_union_left _ h))
    (fun h => hu (mem_union_left _ h)) hdv hdu
  rw [abs_le] at this
  linarith [this.1]

/-- **Theorem 18** (necessity of 3-reach) for arbitrary real inputs. -/
theorem threeReach_of_solves [Fintype V] {f : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hA : Solves A G f ε) : ThreeReach G f :=
  threeReach_of_solvesOn (a := 0) (b := 2 * ε) (Set.mem_univ _) (Set.mem_univ _) (by linarith) hA

end AsyncApproxBCDirected
