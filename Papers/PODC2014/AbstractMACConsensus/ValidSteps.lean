import Podc.Computability.Distributed.AbstractMAC.Sync

/-!
# Valid steps on a single-hop network (Section 3.1 of Newport, PODC 2014)

On the clique `⊤`, the *next valid step* of a node `u` (`validStep c u`) is: nothing if `u` is
crashed or idle; otherwise the delivery of its current message to some (deterministically chosen)
node that has not received it yet; otherwise its acknowledgment. The paper fixes "the smallest
such node"; any deterministic choice depending only on `got u` works, we use `Classical.choose`.
Unlike the paper we do not assume that nodes always broadcast: the valid step of an idle node is a
no-op.

* `runV c vs`: valid steps of the nodes `vs`, in order; `eventsV` the corresponding events.
* `Rel w c c'`: configurations that agree except for the local data of `w` and for whether `w` is
  crashed. Valid steps of nodes `≠ w` preserve it (`Rel.runV`).
* `stepV_comm`: valid steps of two distinct broadcasting nodes commute up to `Rel w` for one node
  `w` (the node both steps affect, if any) — the case analysis of Lemma 3.1.
* `fair_of_blocks`: executions whose blocks are valid steps of all non-crashed nodes are fair.
-/

namespace Podc.AbstractMACConsensus

open Cslib.AbstractMAC Filter

variable {I M S V : Type*} [DecidableEq V] (A : Algorithm I M S)

open Classical in
/-- The next valid step of a node `u` that is crashed iff `dn`, broadcasts `cur`, and whose
message was received by `g`. -/
noncomputable def validStepAux (dn : Prop) (cur : Option M) (g : Set V) (u : V) : Event V :=
  if dn ∨ cur = none then .skip
  else if h : ∃ v, v ≠ u ∧ v ∉ g then .recv u h.choose else .ack u

/-- The next valid step of `u` on the clique. -/
noncomputable def validStep (c : Config V M S) (u : V) : Event V :=
  validStepAux (u ∈ c.down) (c.loc u).cur (c.got u) u

/-- Taking the next valid step of `u`. -/
noncomputable def stepV (c : Config V M S) (u : V) : Config V M S :=
  step A ⊤ c (validStep c u)

/-- Valid steps of the nodes `vs`, in order. -/
noncomputable def runV (c : Config V M S) (vs : List V) : Config V M S :=
  vs.foldl (stepV A) c

/-- The events of `runV c vs`. -/
noncomputable def eventsV : Config V M S → List V → List (Event V)
  | _, [] => []
  | c, v :: vs => validStep c v :: eventsV (stepV A c v) vs

lemma foldl_eventsV (c : Config V M S) (vs : List V) :
    (eventsV A c vs).foldl (step A ⊤) c = runV A c vs := by
  induction vs generalizing c with
  | nil => rfl
  | cons v vs ih => exact ih _

@[simp] lemma runV_nil (c : Config V M S) : runV A c [] = c := rfl

lemma runV_cons (c : Config V M S) (v : V) (vs : List V) :
    runV A c (v :: vs) = runV A (stepV A c v) vs := rfl

lemma runV_append (c : Config V M S) (vs ws : List V) :
    runV A c (vs ++ ws) = runV A (runV A c vs) ws := List.foldl_append

open Classical in
/-- The effect of delivering the message `m` of `u` to `x`. -/
noncomputable def recvEff (c : Config V M S) (u x : V) (m : M) : Config V M S :=
  { c with
    loc := if x ∈ c.down then c.loc else Function.update c.loc x (A.recvNode (c.loc x) m)
    got := Function.update c.got u (insert x (c.got u)) }

/-- The effect of acknowledging `u`. -/
noncomputable def ackEff (c : Config V M S) (u : V) : Config V M S :=
  { c with
    loc := Function.update c.loc u (A.ackNode (c.loc u))
    got := Function.update c.got u ∅
    acks := Function.update c.acks u (c.acks u + 1) }

/-- The three shapes of a valid step. -/
lemma stepV_cases (c : Config V M S) (u : V) :
    (validStep c u = .skip ∧ stepV A c u = c ∧ (u ∈ c.down ∨ (c.loc u).cur = none)) ∨
    (∃ m x, u ∉ c.down ∧ (c.loc u).cur = some m ∧ x ≠ u ∧ x ∉ c.got u ∧
      validStep c u = .recv u x ∧ stepV A c u = recvEff A c u x m) ∨
    (u ∉ c.down ∧ (c.loc u).cur.isSome ∧ (∀ x, x ≠ u → x ∈ c.got u) ∧
      validStep c u = .ack u ∧ stepV A c u = ackEff A c u) := by
  classical
  by_cases h1 : u ∈ c.down ∨ (c.loc u).cur = none
  · left
    have : validStep c u = .skip := by simp [validStep, validStepAux, h1]
    exact ⟨this, by simp [stepV, this, step], h1⟩
  · push Not at h1
    obtain ⟨hd, hc⟩ := h1
    obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1 hc
    by_cases h2 : ∃ v, v ≠ u ∧ v ∉ c.got u
    · right; left
      have hv : validStep c u = .recv u h2.choose := by
        simp [validStep, validStepAux, hd, hc, h2]
      obtain ⟨hx1, hx2⟩ := h2.choose_spec
      refine ⟨m, h2.choose, hd, hm, hx1, hx2, hv, ?_⟩
      simp [stepV, hv, step, hm, hd, hx1.symm, hx2, recvEff]
    · right; right
      push Not at h2
      have h2' : ∀ x, ¬x = u → x ∈ c.got u := h2
      have hne : ¬ ∃ v, v ≠ u ∧ v ∉ c.got u := by push Not; exact h2
      have hv : validStep c u = .ack u := by
        simp only [validStep, validStepAux]
        split_ifs with h1
        · exact absurd h1 (by simp [hd, hc])
        · rfl
      have hl : (c.loc u).cur.isSome := by simp [hm]
      refine ⟨hd, hl, h2', hv, ?_⟩
      simp only [stepV, hv, step]
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by simp [hm], hd,
        fun v hv' => h2 v hv'.ne.symm⟩)]
      rfl

lemma stepV_of_not_live {c : Config V M S} {u : V} (h : u ∈ c.down ∨ (c.loc u).cur = none) :
    stepV A c u = c := by
  rcases stepV_cases A c u with h' | ⟨m, x, hd, hm, -⟩ | ⟨hd, hl, -⟩
  · exact h'.2.1
  · rcases h with h | h <;> simp_all
  · rcases h with h | h <;> simp_all

omit [DecidableEq V] in
/-- `validStep c u` only depends on whether `u` crashed, on its current message, and on
`got u`. -/
lemma validStep_congr {c c' : Config V M S} {u : V} (hd : u ∈ c.down ↔ u ∈ c'.down)
    (hc : (c.loc u).cur = (c'.loc u).cur) (hg : c.got u = c'.got u) :
    validStep c u = validStep c' u := by
  rw [validStep, validStep, hc, hg, propext hd]

lemma stepV_down (c : Config V M S) (u : V) : (stepV A c u).down = c.down := by
  rcases stepV_cases A c u with ⟨-, h, -⟩ | ⟨m, x, -, -, -, -, -, h⟩ | ⟨-, -, -, -, h⟩ <;>
    rw [h] <;> rfl

lemma runV_down (c : Config V M S) (vs : List V) : (runV A c vs).down = c.down := by
  induction vs generalizing c with
  | nil => rfl
  | cons v vs ih => rw [runV_cons, ih, stepV_down]

/-- A valid step of `v` does not touch `got u`, `acks u`, nor the broadcast of `u`, for
`u ≠ v`. -/
lemma stepV_other {c : Config V M S} {u v : V} (huv : u ≠ v) :
    (stepV A c v).got u = c.got u ∧ (stepV A c v).acks u = c.acks u ∧
      ((c.loc u).cur.isSome → ((stepV A c v).loc u).cur = (c.loc u).cur) := by
  rcases stepV_cases A c v with ⟨-, h, -⟩ | ⟨m, x, -, -, -, -, -, h⟩ | ⟨-, -, -, -, h⟩ <;>
    rw [h]
  · exact ⟨rfl, rfl, fun _ => rfl⟩
  · refine ⟨by simp [recvEff, huv], rfl, fun hl => ?_⟩
    simp only [recvEff]
    split_ifs
    · rfl
    · by_cases hux : u = x
      · subst hux; simp [A.recvNode_cur_of_isSome hl]
      · simp [hux]
  · exact ⟨by simp [ackEff, huv], by simp [ackEff, huv], fun _ => by simp [ackEff, huv]⟩

lemma validStep_stepV_other {c : Config V M S} {u v : V} (huv : u ≠ v)
    (hl : (c.loc u).cur.isSome) : validStep (stepV A c v) u = validStep c u := by
  obtain ⟨h1, -, h3⟩ := stepV_other A (c := c) huv
  exact validStep_congr (by rw [stepV_down]) (h3 hl) h1

/-! ### Configurations agreeing off one node -/

/-- `c` and `c'` agree except for the local data of `w` and whether `w` is crashed. -/
structure Rel (w : V) (c c' : Config V M S) : Prop where
  got : c.got = c'.got
  loc : ∀ x, x ≠ w → c.loc x = c'.loc x
  down : ∀ x, x ≠ w → (x ∈ c.down ↔ x ∈ c'.down)

omit [DecidableEq V] in
lemma Rel.validStep {w v : V} {c c' : Config V M S} (h : Rel w c c') (hv : v ≠ w) :
    validStep c v = validStep c' v :=
  validStep_congr (h.down v hv) (by rw [h.loc v hv]) (by rw [h.got])

lemma Rel.stepV {w v : V} {c c' : Config V M S} (h : Rel w c c') (hv : v ≠ w) :
    Rel w (stepV A c v) (stepV A c' v) := by
  have he := h.validStep hv
  rcases stepV_cases A c v with ⟨h1, h2, h3⟩ | ⟨m, x, hd, hm, hxv, hg, h1, h2⟩ |
      ⟨hd, hl, hg, h1, h2⟩
  · rw [h2, stepV_of_not_live A (c := c') ?_]
    · exact h
    · rcases h3 with h3 | h3
      · exact Or.inl ((h.down v hv).1 h3)
      · exact Or.inr (by rw [← h.loc v hv]; exact h3)
  · rcases stepV_cases A c' v with ⟨h1', -, -⟩ | ⟨m', x', hd', hm', -, -, h1', h2'⟩ |
        ⟨-, -, -, h1', -⟩
    · rw [h1, h1'] at he; cases he
    · rw [h1, h1'] at he
      cases he
      have hmm : m' = m := by
        rw [← h.loc v hv, hm] at hm'; exact (Option.some.inj hm').symm
      subst hmm
      rw [h2, h2']
      refine ⟨by simp [recvEff, h.got], fun y hy => ?_, fun y hy => ?_⟩
      swap
      · simpa [recvEff] using h.down y hy
      simp only [recvEff]
      by_cases hxw : x = w
      · subst hxw
        have hyx : y ≠ x := hy
        split_ifs <;> simp [Function.update_of_ne hyx, h.loc y hy]
      · have := h.down x hxw
        by_cases hyx : y = x
        · subst hyx
          have hl := h.loc y hy
          split_ifs <;> simp_all
        · split_ifs <;> simp [Function.update_of_ne hyx, h.loc y hy]
    · rw [h1, h1'] at he; cases he
  · rcases stepV_cases A c' v with ⟨h1', -, -⟩ | ⟨m', x', -, -, -, -, h1', -⟩ |
        ⟨-, -, -, -, h2'⟩
    · rw [h1, h1'] at he; cases he
    · rw [h1, h1'] at he; cases he
    · rw [h2, h2']
      refine ⟨by simp [ackEff, h.got], fun y hy => ?_, fun y hy => h.down y hy⟩
      by_cases hyv : y = v
      · subst hyv; simp [ackEff, h.loc y hy]
      · simp [ackEff, hyv, h.loc y hy]

lemma Rel.runV {w : V} {c c' : Config V M S} (h : Rel w c c') (vs : List V) (hvs : w ∉ vs) :
    Rel w (runV A c vs) (runV A c' vs) := by
  induction vs generalizing c c' with
  | nil => exact h
  | cons v vs ih =>
    simp only [List.mem_cons, not_or] at hvs
    exact ih (h.stepV A (Ne.symm hvs.1)) hvs.2

omit [DecidableEq V] in
lemma Rel.refl (w : V) (c : Config V M S) : Rel w c c :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => Iff.rfl⟩

lemma stepV_eq_recv {c : Config V M S} {v y : V} {n : M} (h : validStep c v = .recv v y)
    (hn : (c.loc v).cur = some n) : stepV A c v = recvEff A c v y n := by
  rcases stepV_cases A c v with ⟨h1, -, -⟩ | ⟨m, x, -, hm, -, -, h1, h2⟩ | ⟨-, -, -, h1, -⟩
  · rw [h] at h1; cases h1
  · rw [h] at h1; cases h1; rw [hn] at hm; cases hm; exact h2
  · rw [h] at h1; cases h1

lemma stepV_eq_ack {c : Config V M S} {v : V} (h : validStep c v = .ack v) :
    stepV A c v = ackEff A c v := by
  rcases stepV_cases A c v with ⟨h1, -, -⟩ | ⟨m, x, -, -, -, -, h1, -⟩ | ⟨-, -, -, -, h2⟩
  · rw [h] at h1; cases h1
  · rw [h] at h1; cases h1
  · exact h2

/-- **Commutation (case analysis of Lemma 3.1).** In a crash-free configuration, valid steps of
two distinct broadcasting nodes commute, up to the local data of one node `w`. -/
lemma stepV_comm {c : Config V M S} {u v : V} (huv : u ≠ v) (hdown : c.down = ∅)
    (hu : (c.loc u).cur.isSome) (hv : (c.loc v).cur.isSome) :
    ∃ w, Rel w (stepV A (stepV A c v) u) (stepV A (stepV A c u) v) := by
  have eu : validStep (stepV A c v) u = validStep c u := validStep_stepV_other A huv hu
  have ev : validStep (stepV A c u) v = validStep c v := validStep_stepV_other A huv.symm hv
  have cu := (stepV_other A (c := c) huv).2.2 hu
  have cv := (stepV_other A (c := c) huv.symm).2.2 hv
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hu
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hv
  have hd : ∀ z, z ∉ c.down := by simp [hdown]
  rcases stepV_cases A c u with ⟨-, -, h3⟩ | ⟨-, x, -, -, hxu, -, h1, -⟩ | ⟨-, -, -, h1, -⟩
  · exact absurd h3 (by simp [hd u, hm])
  all_goals rcases stepV_cases A c v with ⟨-, -, k3⟩ | ⟨-, y, -, -, -, -, k1, -⟩ | ⟨-, -, -, k1, -⟩
  all_goals try (exact absurd k3 (by simp [hd v, hn]))
  · rw [stepV_eq_recv A (eu.trans h1) (cu.trans hm), stepV_eq_recv A (ev.trans k1) (cv.trans hn),
      stepV_eq_recv A h1 hm, stepV_eq_recv A k1 hn]
    refine ⟨x, ?_, fun z hz => ?_, fun z _ => by simp [recvEff]⟩
    · simp only [recvEff, Function.update_of_ne huv, Function.update_of_ne huv.symm]
      exact (Function.update_comm huv _ _ _).symm
    · simp only [recvEff, hdown, Set.mem_empty_iff_false, ite_false, Function.update_apply]
      split_ifs <;> first | rfl | (subst_vars; simp_all only [ne_eq, not_true_eq_false])
  · rw [stepV_eq_recv A (eu.trans h1) (cu.trans hm), stepV_eq_ack A (ev.trans k1),
      stepV_eq_recv A h1 hm, stepV_eq_ack A k1]
    refine ⟨x, ?_, fun z hz => ?_, fun z _ => by simp [recvEff, ackEff]⟩
    · simp only [recvEff, ackEff, Function.update_of_ne huv]
      exact (Function.update_comm huv _ _ _).symm
    · simp only [recvEff, ackEff, hdown, Set.mem_empty_iff_false, ite_false,
        Function.update_apply]
      split_ifs <;> first | rfl | (subst_vars; simp_all only [ne_eq, not_true_eq_false])
  · rw [stepV_eq_ack A (eu.trans h1), stepV_eq_recv A (ev.trans k1) (cv.trans hn),
      stepV_eq_ack A h1, stepV_eq_recv A k1 hn]
    refine ⟨u, ?_, fun z hz => ?_, fun z _ => by simp [recvEff, ackEff]⟩
    · simp only [recvEff, ackEff, Function.update_of_ne huv.symm]
      exact (Function.update_comm huv _ _ _).symm
    · simp only [recvEff, ackEff, hdown, Set.mem_empty_iff_false, ite_false,
        Function.update_apply]
      split_ifs <;> first | rfl | (subst_vars; simp_all only [ne_eq, not_true_eq_false])
  · rw [stepV_eq_ack A (eu.trans h1), stepV_eq_ack A (ev.trans k1), stepV_eq_ack A h1,
      stepV_eq_ack A k1]
    refine ⟨u, ?_, fun z hz => ?_, fun z _ => by simp [ackEff]⟩
    · simp only [ackEff, Function.update_of_ne huv, Function.update_of_ne huv.symm]
      exact (Function.update_comm huv _ _ _).symm
    · simp only [ackEff, Function.update_apply]
      split_ifs <;> first | rfl | (subst_vars; simp_all only [ne_eq, not_true_eq_false])

end Podc.AbstractMACConsensus

namespace Podc.AbstractMACConsensus

open Cslib.AbstractMAC

variable {I M S V : Type*} [DecidableEq V] (A : Algorithm I M S)

/-! ### Fairness of executions made of valid steps -/

lemma mono_runV (u : V) (c : Config V M S) (vs : List V) : Mono u c (runV A c vs) := by
  rw [← foldl_eventsV]; exact mono_foldl A ⊤ u _ _

/-- One valid step, seen by a broadcasting node `u` that is not acknowledged: `got u` grows,
strictly if the step is `u`'s own. -/
lemma got_stepV {d : Config V M S} {u v : V} (hl : (d.loc u).cur.isSome) (hd : u ∉ d.down)
    (ha : (stepV A d v).acks u = d.acks u) :
    d.got u ⊆ (stepV A d v).got u ∧ (v = u → d.got u ⊂ (stepV A d v).got u) := by
  by_cases hvu : v = u
  · subst hvu
    refine ⟨?_, fun _ => ?_⟩ <;>
    rcases stepV_cases A d v with ⟨-, -, h3⟩ | ⟨m, x, -, -, -, hx, -, h2⟩ | ⟨-, -, -, -, h2⟩
    all_goals first
      | (rcases h3 with h3 | h3 <;> simp_all)
      | (rw [h2] at ha ⊢; simp [ackEff] at ha)
      | skip
    · rw [h2]; simp [recvEff]
    · rw [h2]; simp only [recvEff, Function.update_self]
      exact Set.ssubset_insert hx
  · exact ⟨(stepV_other A (c := d) (Ne.symm hvu)).1.symm.subset, fun h => absurd h hvu⟩

lemma got_runV {d : Config V M S} {u : V} (hl : (d.loc u).cur.isSome) (hd : u ∉ d.down)
    (L : List V) (ha : (runV A d L).acks u = d.acks u) :
    d.got u ⊆ (runV A d L).got u ∧ (u ∈ L → d.got u ⊂ (runV A d L).got u) := by
  induction L generalizing d with
  | nil => exact ⟨subset_rfl, by simp⟩
  | cons v L ih =>
    rw [runV_cons] at ha ⊢
    have m1 := mono_step A ⊤ u d (validStep d v)
    have m2 := mono_runV A u (stepV A d v) L
    have ha1 : (stepV A d v).acks u = d.acks u :=
      le_antisymm (ha ▸ m2.acks_le) m1.acks_le
    have hl1 : ((stepV A d v).loc u).cur.isSome := by
      have := m1.cur_eq hl ha1; unfold stepV; rw [this]; exact hl
    have hd1 : u ∉ (stepV A d v).down := by rw [stepV_down]; exact hd
    obtain ⟨g1, g2⟩ := got_stepV A hl hd ha1
    obtain ⟨g3, g4⟩ := ih hl1 hd1 (ha.trans ha1.symm)
    refine ⟨g1.trans g3, fun hu => ?_⟩
    rcases List.mem_cons.1 hu with rfl | hu
    · exact (g2 rfl).trans_subset g3
    · exact g1.trans_ssubset (g4 hu)

/-- Executions whose blocks (from `j₀` on) are valid steps of lists containing all non-crashed
nodes are fair. -/
theorem fair_of_blocks [Fintype V] (c₀ : Config V M S) (σ : ℕ → List (Event V)) (j₀ : ℕ)
    (ℓ : ℕ → List V) (hσ : ∀ j ≥ j₀, σ j = eventsV A (run A ⊤ c₀ σ j) (ℓ j))
    (hℓ : ∀ j ≥ j₀, ∀ u, u ∉ (run A ⊤ c₀ σ j).down → u ∈ ℓ j) : Fair A ⊤ c₀ σ := by
  intro u i hl
  by_contra hne
  push Not at hne
  have hst : ∀ j ≥ i, (run A ⊤ c₀ σ j).Live u ∧
      (run A ⊤ c₀ σ j).acks u = (run A ⊤ c₀ σ i).acks u ∧ u ∉ (run A ⊤ c₀ σ j).down := by
    intro j hj
    have hp : ¬ Prog A ⊤ c₀ σ u i j := hne j hj
    obtain ⟨h1, h2⟩ := live_of_not_prog hj hl hp
    exact ⟨h1, h2, fun h => hp (Or.inr h)⟩
  set i' := max i j₀
  have hrun : ∀ j ≥ j₀, run A ⊤ c₀ σ (j + 1) = runV A (run A ⊤ c₀ σ j) (ℓ j) := by
    intro j hj; rw [run_succ, hσ j hj, foldl_eventsV]
  have key : ∀ k, k ≤ ((run A ⊤ c₀ σ (i' + k)).got u).ncard := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hj : i' + k ≥ i := by omega
      obtain ⟨h1, h2, h3⟩ := hst _ hj
      obtain ⟨-, -, -⟩ := hst _ (show i' + (k + 1) ≥ i by omega)
      have ha : (runV A (run A ⊤ c₀ σ (i' + k)) (ℓ (i' + k))).acks u =
          (run A ⊤ c₀ σ (i' + k)).acks u := by
        rw [← hrun _ (by omega), (hst _ (show i' + k + 1 ≥ i by omega)).2.1, h2]
      have hss := (got_runV A h1 h3 _ ha).2 (hℓ _ (by omega) u h3)
      rw [← hrun _ (by omega)] at hss
      have := Set.ncard_lt_ncard hss (Set.toFinite _)
      rw [show i' + (k + 1) = i' + k + 1 by omega]
      omega
  have := key (Fintype.card V + 1)
  have hle : ((run A ⊤ c₀ σ (i' + (Fintype.card V + 1))).got u).ncard ≤ Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]; exact Set.ncard_le_ncard (Set.subset_univ _)
  omega

end Podc.AbstractMACConsensus
