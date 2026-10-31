import Papers.PODC2015.WeakestFDEventualConsistency.Specs

/-!
# Lemma 3 is false: Algorithm 5 (`ETOB` from `Ω`) violates ETOB-Stability

Algorithm 5 of [DGKPS15]. Process `p_i` keeps a causality graph `CG_i`, a promotion sequence
`promote_i` and the output `d_i`:
* on `broadcastETOB(m, C(m))`: `UpdateCG(m, C(m))`; send `update(CG_i)` to all;
* on reception of `update(CG_j)`: `UnionCG(CG_j)`; `UpdatePromote()`;
* on reception of `promote(promote_j)` from `p_j`: if `Ω_i = p_j` then `d_i := promote_j`;
* on a local time-out: if `Ω_i = p_i` then send `promote(promote_i)` to all.

`UpdatePromote()` replaces `promote_i` by *one of* the sequences `s` such that `promote_i` is a
prefix of `s`, `s` contains each message of `CG_i` exactly once, and `s` respects the edges of
`CG_i`. We model the choice by an arbitrary function `upd` that returns such a sequence whenever
one exists (`UpdValid`); the counterexample works for every such `upd`.

**The flaw.** Links are reliable but not FIFO (the paper's model: a step receives *a* message
in transit), and a receiver overwrites `d_i` with *every* promotion of its leader, so an old,
shorter promotion that is overtaken by a newer one and arrives later makes `d_i` shrink. With infinitely many broadcasts this can happen infinitely often, even if `Ω`
outputs the same correct leader at all processes from the very beginning: ETOB-Stability (and
TOB-Stability) fails for every `τ`. The proof of Lemma 3 assumes that the promotions adopted at
times `t₁ ≤ t₂` were *sent* in that order (`t₃ ≤ t₄`), and bounds message delays by a "longest
communication delay `Δc`", which need not exist in an asynchronous run.
-/

namespace Podc.WeakestFDEventualConsistency

open Cslib.FailureDetectors

namespace Alg5

variable {P M : Type*} [DecidableEq P] [DecidableEq M]

/-- A causality graph. -/
@[ext] structure CG (M : Type*) where
  /-- The messages. -/
  nodes : Finset M
  /-- Causal edges `(m', m)`: `m'` precedes `m`. -/
  edges : Finset (M × M)

/-- `UnionCG`. -/
def CG.union (a b : CG M) : CG M := ⟨a.nodes ∪ b.nodes, a.edges ∪ b.edges⟩

/-- `UpdateCG(m, C)`. -/
def CG.add (g : CG M) (m : M) (C : Finset M) : CG M :=
  ⟨insert m g.nodes, g.edges ∪ C.image fun m' => (m', m)⟩

/-- The sequences `UpdatePromote` may choose: `promote` is a prefix, every message of the graph
occurs exactly once (and nothing else), and the causal edges are respected. -/
def UpdSpec (promote : List M) (g : CG M) (s : List M) : Prop :=
  promote <+: s ∧ s.Nodup ∧ (∀ m, m ∈ s ↔ m ∈ g.nodes) ∧
    ∀ m₁ m₂, (m₁, m₂) ∈ g.edges → Before m₁ m₂ s

/-- `upd` implements `UpdatePromote`: it returns an admissible sequence whenever one exists. -/
def UpdValid (upd : List M → CG M → List M) : Prop :=
  ∀ pr g, (∃ s, UpdSpec pr g s) → UpdSpec pr g (upd pr g)

/-- Messages. -/
inductive Msg (M : Type*) where
  /-- `update(CG)`. -/
  | update (g : CG M)
  /-- `promote(seq)`. -/
  | promote (l : List M)

/-- Local state. -/
structure State (M : Type*) where
  /-- Output variable. -/
  d : List M
  /-- Promotion sequence. -/
  promote : List M
  /-- Causality graph. -/
  cg : CG M

/-- **Algorithm 5** of [DGKPS15] (`Ω` gives the failure-detector values; inputs are
`broadcastETOB(m, C(m))`). -/
def alg (upd : List M → CG M → List M) :
    Algorithm P P (Msg M) (M × Finset M) Empty (State M) where
  init _ := ⟨[], [], ⟨∅, ∅⟩⟩
  step p d s e :=
    match e with
    | .input (m, C) =>
      let g := s.cg.add m C
      ({ s with cg := g }, some (.update g), [])
    | .recv _ (.update g) =>
      let g' := s.cg.union g
      ({ s with cg := g', promote := upd s.promote g' }, none, [])
    | .recv q (.promote l) => if d = q then ({ s with d := l }, none, []) else (s, none, [])
    | .tick => if d = p then (s, some (.promote s.promote), []) else (s, none, [])

/-- The ETOB history of a run of Algorithm 5. -/
def tobHist (upd : List M → CG M → List M) (r : Run P P (M × Finset M)) : TOBHist P M where
  bcast p m t := ∃ C, r.σ t = some (p, .input (m, C))
  d p t := ((alg upd).st r p t).d

/-! ### The counterexample run

Two processes `0` (the leader) and `1`, no crashes, `Ω` constantly outputs `0`. The run consists
of blocks of 10 time units; in block `b`:
* `10b`: `0` broadcasts message `b` (no causal dependencies);
* `10b+1`, `10b+3`: `0` and `1` receive this `update`;
* `10b+2`: time-out at `0`, which sends `promote([0, …, b])`;
* `10b+4`: time-out at `1`;
* if `b` is odd: `0` and `1` receive first the promotion of block `b` and then the (delayed)
  promotion of block `b - 1`, so `d_0` goes from `[0, …, b]` back to `[0, …, b-1]`.
-/

/-- The step at offset `k` of block `b`. -/
def blockStep (b k : ℕ) : Option (Fin 2 × Choice (Fin 2) (ℕ × Finset ℕ)) :=
  match k with
  | 0 => some (0, .input (b, ∅))
  | 1 => some (0, .recv 0 (10 * b))
  | 2 => some (0, .tick)
  | 3 => some (1, .recv 0 (10 * b))
  | 4 => some (1, .tick)
  | 5 => if b % 2 = 1 then some (0, .recv 0 (10 * b + 2)) else none
  | 6 => if b % 2 = 1 then some (0, .recv 0 (10 * b - 8)) else none
  | 7 => if b % 2 = 1 then some (1, .recv 0 (10 * b + 2)) else none
  | 8 => if b % 2 = 1 then some (1, .recv 0 (10 * b - 8)) else none
  | _ => none

/-- The schedule. -/
def sched (t : ℕ) : Option (Fin 2 × Choice (Fin 2) (ℕ × Finset ℕ)) := blockStep (t / 10) (t % 10)

/-- The counterexample run. -/
def run : Run (Fin 2) (Fin 2) (ℕ × Finset ℕ) := ⟨FailurePattern.noCrash, fun _ _ => 0, sched⟩

lemma sched_block (b k : ℕ) (hk : k < 10) : sched (10 * b + k) = blockStep b k := by
  simp only [sched]
  congr 1
  · omega
  · omega

lemma run_σ (b k : ℕ) (hk : k < 10) : run.σ (10 * b + k) = blockStep b k := sched_block b k hk

lemma run_H (p : Fin 2) (t : ℕ) : run.H p t = 0 := rfl

/-! #### `UpdatePromote` is forced in the run -/

lemma eq_singleton_of_nodup {l : List ℕ} {b : ℕ} (hn : l.Nodup) (hall : ∀ x ∈ l, x = b)
    (hb : b ∈ l) : l = [b] := by
  rcases l with _ | ⟨x, l⟩
  · simp at hb
  · have hx := hall x (by simp)
    subst hx
    rcases l with _ | ⟨y, l⟩
    · rfl
    · have hy := hall y (by simp)
      subst hy
      simp at hn

lemma updSpec_range (b : ℕ) :
    UpdSpec (List.range b) (⟨Finset.range (b + 1), ∅⟩ : CG ℕ) (List.range (b + 1)) := by
  refine ⟨?_, List.nodup_range, fun m => by simp, fun _ _ h => by simp at h⟩
  rw [List.range_succ]; exact List.prefix_append _ _

lemma upd_forced {upd : List ℕ → CG ℕ → List ℕ} (hupd : UpdValid upd) (b : ℕ) :
    upd (List.range b) ⟨Finset.range (b + 1), ∅⟩ = List.range (b + 1) := by
  obtain ⟨⟨rest, hrest⟩, hn, hmem, -⟩ := hupd _ _ ⟨_, updSpec_range b⟩
  rw [← hrest] at hn hmem ⊢
  have hrest1 : rest = [b] := by
    refine eq_singleton_of_nodup (List.Nodup.of_append_right hn) (fun x hx => ?_) ?_
    · have h1 := (hmem x).1 (List.mem_append_right _ hx)
      simp only [Finset.mem_range] at h1
      have h2 : x ∉ List.range b := fun h => List.disjoint_of_nodup_append hn h hx
      simp only [List.mem_range, not_lt] at h2
      omega
    · have h1 := (hmem b).2 (by simp)
      rcases List.mem_append.1 h1 with h | h
      · simp at h
      · exact h
  rw [hrest1, List.range_succ]

/-! #### One block of the run -/

variable {upd : List ℕ → CG ℕ → List ℕ}

lemma st_other {t : ℕ} {q : Fin 2} (h : ∀ c, run.σ t ≠ some (q, c)) :
    (alg upd).st run q (t + 1) = (alg upd).st run q t :=
  Algorithm.loc_succ_of_ne run t q h

@[simp] lemma step_input (p d : Fin 2) (s : State ℕ) (m : ℕ) (C : Finset ℕ) :
    (alg upd).step p d s (.input (m, C)) =
      (⟨s.d, s.promote, s.cg.add m C⟩, some (.update (s.cg.add m C)), []) := rfl

@[simp] lemma step_update (p d q : Fin 2) (s : State ℕ) (g : CG ℕ) :
    (alg upd).step p d s (.recv q (.update g)) =
      (⟨s.d, upd s.promote (s.cg.union g), s.cg.union g⟩, none, []) := rfl

@[simp] lemma step_tick_self (p : Fin 2) (s : State ℕ) :
    (alg upd).step p p s .tick = (s, some (.promote s.promote), []) := by
  simp [alg]

lemma step_promote (p d q : Fin 2) (s : State ℕ) (l : List ℕ) :
    ((alg upd).step p d s (.recv q (.promote l))).1.promote = s.promote ∧
    ((alg upd).step p d s (.recv q (.promote l))).1.cg = s.cg ∧
    ((alg upd).step p d s (.recv q (.promote l))).1.d = (if d = q then l else s.d) := by
  simp only [alg]; split_ifs <;> simp

/-- A step of `0` receiving a promotion changes only `d_0`. -/
lemma st_recv_promote {t s₀ : ℕ} {l : List ℕ}
    (hσ : run.σ t = some (0, .recv 0 s₀))
    (hm : ((alg upd).cfg run t).msg s₀ = some (0, .promote l)) :
    ((alg upd).st run 0 (t + 1)).promote = ((alg upd).st run 0 t).promote ∧
    ((alg upd).st run 0 (t + 1)).cg = ((alg upd).st run 0 t).cg ∧
    ((alg upd).st run 0 (t + 1)).d = l := by
  rw [(Algorithm.cfg_succ_of_event run t 0 _ _ hσ (Algorithm.event_recv hm)).1]
  have := step_promote (upd := upd) 0 (run.H 0 t) 0 ((alg upd).st run 0 t) l
  simpa [run_H] using this

lemma block (hupd : UpdValid upd) (b : ℕ)
    (hpr : ((alg upd).st run 0 (10 * b)).promote = List.range b)
    (hcg : ((alg upd).st run 0 (10 * b)).cg = ⟨Finset.range b, ∅⟩)
    (hprev : b % 2 = 1 →
      ((alg upd).cfg run (10 * b)).msg (10 * b - 8) = some (0, .promote (List.range b))) :
    ((alg upd).cfg run (10 * b + 1)).msg (10 * b) =
        some (0, .update ⟨Finset.range (b + 1), ∅⟩) ∧
    ((alg upd).cfg run (10 * b + 3)).msg (10 * b + 2) = some (0, .promote (List.range (b + 1))) ∧
    ((alg upd).st run 0 (10 * b + 10)).promote = List.range (b + 1) ∧
    ((alg upd).st run 0 (10 * b + 10)).cg = ⟨Finset.range (b + 1), ∅⟩ ∧
    (b % 2 = 1 → ((alg upd).st run 0 (10 * b + 6)).d = List.range (b + 1) ∧
      ((alg upd).st run 0 (10 * b + 7)).d = List.range b) := by
  -- step 0: broadcast `b`
  have hσ0 : run.σ (10 * b) = some (0, .input (b, ∅)) := by
    simpa [blockStep] using run_σ b 0 (by omega)
  obtain ⟨h0s, h0m, -⟩ := Algorithm.cfg_succ_of_event run (10 * b) 0 _ _ hσ0
    (Algorithm.event_input _ _)
  have hadd : ((alg upd).st run 0 (10 * b)).cg.add b ∅ = ⟨Finset.range (b + 1), ∅⟩ := by
    rw [hcg]; ext x <;> simp [CG.add, Finset.range_add_one]
  have hm0 : ((alg upd).cfg run (10 * b + 1)).msg (10 * b) =
      some (0, .update ⟨Finset.range (b + 1), ∅⟩) := by
    rw [h0m, step_input, hadd]; rfl
  have hs1 : ((alg upd).st run 0 (10 * b + 1)) =
      ⟨((alg upd).st run 0 (10 * b)).d, ((alg upd).st run 0 (10 * b)).promote,
        ⟨Finset.range (b + 1), ∅⟩⟩ := by
    rw [h0s, step_input, hadd]
  -- step 1: `0` receives the update
  have hσ1 : run.σ (10 * b + 1) = some (0, .recv 0 (10 * b)) := by
    simpa [blockStep] using run_σ b 1 (by omega)
  obtain ⟨h1s, h1m, -⟩ := Algorithm.cfg_succ_of_event run (10 * b + 1) 0 _ _ hσ1
    (Algorithm.event_recv hm0)
  have hs2 : ((alg upd).st run 0 (10 * b + 2)) =
      ⟨((alg upd).st run 0 (10 * b)).d, List.range (b + 1), ⟨Finset.range (b + 1), ∅⟩⟩ := by
    rw [h1s, hs1, step_update]
    have hu : (⟨Finset.range (b + 1), ∅⟩ : CG ℕ).union ⟨Finset.range (b + 1), ∅⟩ =
        ⟨Finset.range (b + 1), ∅⟩ := by ext x <;> simp [CG.union]
    simp only [hu, hpr, upd_forced hupd b]
  -- step 2: time-out at `0`
  have hσ2 : run.σ (10 * b + 2) = some (0, .tick) := by
    simpa [blockStep] using run_σ b 2 (by omega)
  obtain ⟨h2s, h2m, -⟩ := Algorithm.cfg_succ_of_event run (10 * b + 2) 0 _ _ hσ2
    (Algorithm.event_tick _)
  have hs3 : (alg upd).st run 0 (10 * b + 3) = (alg upd).st run 0 (10 * b + 2) := by
    rw [h2s, run_H, step_tick_self]
  have hm2 : ((alg upd).cfg run (10 * b + 3)).msg (10 * b + 2) =
      some (0, .promote (List.range (b + 1))) := by
    rw [h2m, run_H, step_tick_self, hs2]; rfl
  -- steps 3, 4: process `1`
  have hs4 : (alg upd).st run 0 (10 * b + 4) = (alg upd).st run 0 (10 * b + 3) :=
    st_other (by intro c; rw [run_σ b 3 (by omega)]; simp [blockStep])
  have hs5 : (alg upd).st run 0 (10 * b + 5) = (alg upd).st run 0 (10 * b + 4) :=
    st_other (by intro c; rw [run_σ b 4 (by omega)]; simp [blockStep])
  -- steps 7, 8, 9: not `0`
  have hs8 : (alg upd).st run 0 (10 * b + 8) = (alg upd).st run 0 (10 * b + 7) :=
    st_other (by intro c; rw [run_σ b 7 (by omega)]; simp only [blockStep]; split_ifs <;> simp)
  have hs9 : (alg upd).st run 0 (10 * b + 9) = (alg upd).st run 0 (10 * b + 8) :=
    st_other (by intro c; rw [run_σ b 8 (by omega)]; simp only [blockStep]; split_ifs <;> simp)
  have hs10 : (alg upd).st run 0 (10 * b + 10) = (alg upd).st run 0 (10 * b + 9) :=
    st_other (by intro c; rw [run_σ b 9 (by omega)]; simp [blockStep])
  -- steps 5, 6
  by_cases hb : b % 2 = 1
  · have hσ5 : run.σ (10 * b + 5) = some (0, .recv 0 (10 * b + 2)) := by
      simpa [blockStep, hb] using run_σ b 5 (by omega)
    have hm5 : ((alg upd).cfg run (10 * b + 5)).msg (10 * b + 2) =
        some (0, .promote (List.range (b + 1))) := by
      rw [Algorithm.msg_mono run (show 10 * b + 2 < 10 * b + 3 by omega) (by omega)]; exact hm2
    obtain ⟨h5p, h5c, h5d⟩ := st_recv_promote hσ5 hm5
    have hσ6 : run.σ (10 * b + 6) = some (0, .recv 0 (10 * b - 8)) := by
      simpa [blockStep, hb] using run_σ b 6 (by omega)
    have hm6 : ((alg upd).cfg run (10 * b + 6)).msg (10 * b - 8) =
        some (0, .promote (List.range b)) := by
      rw [Algorithm.msg_mono run (show 10 * b - 8 < 10 * b by omega) (by omega)]; exact hprev hb
    obtain ⟨h6p, h6c, h6d⟩ := st_recv_promote hσ6 hm6
    have hs7 : (alg upd).st run 0 (10 * b + 7) = (alg upd).st run 0 (10 * b + 6 + 1) := rfl
    refine ⟨hm0, hm2, ?_, ?_, fun _ => ⟨h5d, h6d⟩⟩
    · rw [hs10, hs9, hs8, hs7, h6p, h5p, hs5, hs4, hs3, hs2]
    · rw [hs10, hs9, hs8, hs7, h6c, h5c, hs5, hs4, hs3, hs2]
  · have hs6 : (alg upd).st run 0 (10 * b + 6) = (alg upd).st run 0 (10 * b + 5) :=
      st_other (by intro c; rw [run_σ b 5 (by omega)]; simp [blockStep, hb])
    have hs7 : (alg upd).st run 0 (10 * b + 7) = (alg upd).st run 0 (10 * b + 6) :=
      st_other (by intro c; rw [run_σ b 6 (by omega)]; simp [blockStep, hb])
    refine ⟨hm0, hm2, ?_, ?_, fun h => absurd h hb⟩
    · rw [hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2]
    · rw [hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2]

lemma blocks (hupd : UpdValid upd) : ∀ b,
    ((alg upd).st run 0 (10 * b)).promote = List.range b ∧
    ((alg upd).st run 0 (10 * b)).cg = ⟨Finset.range b, ∅⟩ ∧
    (1 ≤ b → ((alg upd).cfg run (10 * b)).msg (10 * b - 8) = some (0, .promote (List.range b))) := by
  intro b
  induction b with
  | zero => exact ⟨rfl, rfl, fun h => absurd h (by omega)⟩
  | succ b ih =>
    obtain ⟨-, hm2, hpr, hcg, -⟩ := block hupd b ih.1 ih.2.1 (fun hb => ih.2.2 (by omega))
    refine ⟨by rw [show 10 * (b + 1) = 10 * b + 10 by ring]; exact hpr,
      by rw [show 10 * (b + 1) = 10 * b + 10 by ring]; exact hcg, fun _ => ?_⟩
    rw [show 10 * (b + 1) - 8 = 10 * b + 2 by omega,
      Algorithm.msg_mono run (show 10 * b + 2 < 10 * b + 3 by omega) (by omega)]
    exact hm2

lemma msg_update (hupd : UpdValid upd) {b t : ℕ} (ht : 10 * b < t) :
    ((alg upd).cfg run t).msg (10 * b) = some (0, .update ⟨Finset.range (b + 1), ∅⟩) := by
  have := (block hupd b (blocks hupd b).1 (blocks hupd b).2.1
    (fun hb => (blocks hupd b).2.2 (by omega))).1
  rw [Algorithm.msg_mono run (show 10 * b < 10 * b + 1 by omega) (by omega)]; exact this

lemma msg_promote (hupd : UpdValid upd) {b t : ℕ} (ht : 10 * b + 2 < t) :
    ((alg upd).cfg run t).msg (10 * b + 2) = some (0, .promote (List.range (b + 1))) := by
  have := (block hupd b (blocks hupd b).1 (blocks hupd b).2.1
    (fun hb => (blocks hupd b).2.2 (by omega))).2.1
  rw [Algorithm.msg_mono run (show 10 * b + 2 < 10 * b + 3 by omega) (by omega)]; exact this

/-- In odd blocks, `d_0` shrinks. -/
lemma d_shrinks (hupd : UpdValid upd) {b : ℕ} (hb : b % 2 = 1) :
    ((alg upd).st run 0 (10 * b + 6)).d = List.range (b + 1) ∧
    ((alg upd).st run 0 (10 * b + 7)).d = List.range b :=
  (block hupd b (blocks hupd b).1 (blocks hupd b).2.1
    (fun hb => (blocks hupd b).2.2 (by omega))).2.2.2.2 hb

/-! #### Decoding the schedule -/

lemma sched_eq (t : ℕ) : run.σ t = blockStep (t / 10) (t % 10) := rfl

lemma decode_recv {t s : ℕ} {p q : Fin 2} (h : run.σ t = some (p, .recv q s)) :
    q = 0 ∧ ((t % 10 = 1 ∧ p = 0 ∧ s = 10 * (t / 10)) ∨ (t % 10 = 3 ∧ p = 1 ∧ s = 10 * (t / 10)) ∨
      ((t / 10) % 2 = 1 ∧
        ((t % 10 = 5 ∧ p = 0 ∧ s = 10 * (t / 10) + 2) ∨ (t % 10 = 6 ∧ p = 0 ∧ s = 10 * (t / 10) - 8) ∨
          (t % 10 = 7 ∧ p = 1 ∧ s = 10 * (t / 10) + 2) ∨
          (t % 10 = 8 ∧ p = 1 ∧ s = 10 * (t / 10) - 8)))) := by
  rw [sched_eq] at h
  have hk : t % 10 < 10 := Nat.mod_lt _ (by omega)
  generalize t % 10 = k at h hk ⊢
  generalize t / 10 = b at h ⊢
  interval_cases k <;> simp only [blockStep] at h <;> (try split_ifs at h) <;>
    simp_all [Prod.ext_iff, eq_comm]

lemma decode_input {t : ℕ} {p : Fin 2} {i : ℕ × Finset ℕ} (h : run.σ t = some (p, .input i)) :
    t % 10 = 0 ∧ p = 0 ∧ i = (t / 10, ∅) := by
  rw [sched_eq] at h
  have hk : t % 10 < 10 := Nat.mod_lt _ (by omega)
  generalize t % 10 = k at h hk ⊢
  generalize t / 10 = b at h ⊢
  interval_cases k <;> simp only [blockStep] at h <;> (try split_ifs at h) <;>
    simp_all [Prod.ext_iff, eq_comm]

lemma decode_some {t : ℕ} {p : Fin 2} {c} (h : run.σ t = some (p, c)) :
    (t % 10 = 0 ∧ p = 0 ∧ c = .input (t / 10, ∅)) ∨ (t % 10 = 2 ∧ p = 0 ∧ c = .tick) ∨
      (t % 10 = 4 ∧ p = 1 ∧ c = .tick) ∨ ∃ q s, c = .recv q s := by
  rw [sched_eq] at h
  have hk : t % 10 < 10 := Nat.mod_lt _ (by omega)
  generalize t % 10 = k at h hk ⊢
  generalize t / 10 = b at h ⊢
  interval_cases k <;> simp only [blockStep] at h <;> (try split_ifs at h) <;>
    simp_all [Prod.ext_iff, eq_comm]

lemma step_recv_bcast (p d q : Fin 2) (s : State ℕ) (m : Msg ℕ) :
    ((alg upd).step p d s (.recv q m)).2.1 = none := by
  cases m with
  | update g => rfl
  | promote l => simp only [alg]; split_ifs <;> rfl

/-- Only the input steps (offset 0) and the leader's time-outs (offset 2) send messages. -/
lemma msg_time {t s : ℕ} {q : Fin 2} {m : Msg ℕ} (h : ((alg upd).cfg run t).msg s = some (q, m)) :
    q = 0 ∧ (s % 10 = 0 ∨ s % 10 = 2) := by
  obtain ⟨c, e, hσ, he, hb⟩ := Algorithm.msg_spec run h
  rcases decode_some hσ with ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ | ⟨h1, rfl, rfl⟩ | ⟨q', s', rfl⟩
  · exact ⟨rfl, Or.inl h1⟩
  · exact ⟨rfl, Or.inr h1⟩
  · rw [Algorithm.event_tick] at he
    cases he
    simp [alg, run_H] at hb
  · obtain ⟨m', rfl, -⟩ := Algorithm.event_of_recv he
    rw [step_recv_bcast] at hb
    exact absurd hb (by simp)

/-! #### The run is admissible -/

lemma recv_valid (hupd : UpdValid upd) (t : ℕ) (p q : Fin 2) (s : ℕ)
    (h : run.σ t = some (p, .recv q s)) :
    s < t ∧ ∃ m, ((alg upd).cfg run t).msg s = some (q, m) := by
  obtain ⟨rfl, hd⟩ := decode_recv h
  have ht := Nat.div_add_mod t 10
  rcases hd with ⟨h1, -, rfl⟩ | ⟨h1, -, rfl⟩ | ⟨hb, ⟨h1, -, rfl⟩ | ⟨h1, -, rfl⟩ | ⟨h1, -, rfl⟩ |
      ⟨h1, -, rfl⟩⟩
  · exact ⟨by omega, _, msg_update hupd (by omega)⟩
  · exact ⟨by omega, _, msg_update hupd (by omega)⟩
  · exact ⟨by omega, _, msg_promote hupd (by omega)⟩
  · refine ⟨by omega, ?_⟩
    rw [show 10 * (t / 10) - 8 = 10 * (t / 10 - 1) + 2 by omega]
    exact ⟨_, msg_promote hupd (by omega)⟩
  · exact ⟨by omega, _, msg_promote hupd (by omega)⟩
  · refine ⟨by omega, ?_⟩
    rw [show 10 * (t / 10) - 8 = 10 * (t / 10 - 1) + 2 by omega]
    exact ⟨_, msg_promote hupd (by omega)⟩

lemma recv_once (t t' : ℕ) (p q : Fin 2) (s : ℕ) (h : run.σ t = some (p, .recv q s))
    (h' : run.σ t' = some (p, .recv q s)) : t = t' := by
  obtain ⟨-, hd⟩ := decode_recv h
  obtain ⟨-, hd'⟩ := decode_recv h'
  have ht := Nat.div_add_mod t 10
  have ht' := Nat.div_add_mod t' 10
  rcases hd with ⟨h1, hp, hs⟩ | ⟨h1, hp, hs⟩ | ⟨hb, ⟨h1, hp, hs⟩ | ⟨h1, hp, hs⟩ | ⟨h1, hp, hs⟩ |
      ⟨h1, hp, hs⟩⟩ <;>
  rcases hd' with ⟨h1', hp', hs'⟩ | ⟨h1', hp', hs'⟩ | ⟨hb', ⟨h1', hp', hs'⟩ | ⟨h1', hp', hs'⟩ |
      ⟨h1', hp', hs'⟩ | ⟨h1', hp', hs'⟩⟩ <;>
  first
  | (rw [hp] at hp'; exact absurd hp' (by decide))
  | omega

lemma delivery (p : Fin 2) (t s : ℕ) (q : Fin 2) (m : Msg ℕ)
    (h : ((alg upd).cfg run t).msg s = some (q, m)) : ∃ t', run.σ t' = some (p, .recv q s) := by
  obtain ⟨rfl, hs⟩ := msg_time h
  have hs' := Nat.div_add_mod s 10
  rcases hs with hs | hs
  · -- an update, received at offsets 1 and 3 of the same block
    fin_cases p
    · refine ⟨10 * (s / 10) + 1, ?_⟩
      rw [run_σ _ 1 (by omega)]; simp only [blockStep]; congr 3; omega
    · refine ⟨10 * (s / 10) + 3, ?_⟩
      rw [run_σ _ 3 (by omega)]; simp only [blockStep]; congr 3; omega
  · rcases Nat.mod_two_eq_zero_or_one (s / 10) with hb | hb
    · -- even block: received in the next (odd) block, at offsets 6 and 8
      have hb' : (s / 10 + 1) % 2 = 1 := by omega
      fin_cases p
      · refine ⟨10 * (s / 10 + 1) + 6, ?_⟩
        rw [run_σ _ 6 (by omega)]; simp only [blockStep, hb', ↓reduceIte]; congr 3; omega
      · refine ⟨10 * (s / 10 + 1) + 8, ?_⟩
        rw [run_σ _ 8 (by omega)]; simp only [blockStep, hb', ↓reduceIte]; congr 3; omega
    · -- odd block: received in the same block, at offsets 5 and 7
      fin_cases p
      · refine ⟨10 * (s / 10) + 5, ?_⟩
        rw [run_σ _ 5 (by omega)]; simp only [blockStep, hb, ↓reduceIte]; congr 3; omega
      · refine ⟨10 * (s / 10) + 7, ?_⟩
        rw [run_σ _ 7 (by omega)]; simp only [blockStep, hb, ↓reduceIte]; congr 3; omega

lemma admissible (hupd : UpdValid upd) : (alg upd).Admissible run where
  alive _ _ _ _ := fun h => h
  recv_valid := recv_valid hupd
  recv_once := recv_once
  ticks p _ T := by
    fin_cases p
    · exact ⟨10 * T + 2, by omega, by rw [run_σ T 2 (by omega)]; rfl⟩
    · exact ⟨10 * T + 4, by omega, by rw [run_σ T 4 (by omega)]; rfl⟩
  delivery p _ t s q m h := delivery p t s q m h

lemma distinct : (tobHist upd run).Distinct := by
  rintro p q m t t' ⟨C, h⟩ ⟨C', h'⟩
  obtain ⟨h1, rfl, h2⟩ := decode_input h
  obtain ⟨h1', rfl, h2'⟩ := decode_input h'
  simp only [Prod.mk.injEq] at h2 h2'
  refine ⟨rfl, ?_⟩
  have := Nat.div_add_mod t 10
  have := Nat.div_add_mod t' 10
  omega

/-- In the run, ETOB-Stability fails for every `τ`. -/
lemma not_stability (hupd : UpdValid upd) (τ : ℕ) :
    ¬ ETOBStability run.F (tobHist upd run) τ := by
  intro h
  have hb : (2 * τ + 1) % 2 = 1 := by omega
  obtain ⟨h6, h7⟩ := d_shrinks hupd hb
  have := h 0 (FailurePattern.noCrash_correct 0) (10 * (2 * τ + 1) + 6) (10 * (2 * τ + 1) + 7)
    (by omega) (by omega)
  simp only [tobHist, h6, h7] at this
  have := this.length_le
  simp at this

/-- **Lemma 3 of [DGKPS15] is false** (and so is the claim that Algorithm 5 implements total order
broadcast when `Ω` outputs the same leader everywhere from the beginning). For every
implementation `upd` of `UpdatePromote`, there is an admissible run of Algorithm 5 with two
processes, no crashes, distinct broadcasts and `Ω` permanently outputting the same correct
process `0` at every process, in which ETOB-Stability fails for every `τ`, so the run does not
satisfy ETOB. -/
theorem lemma_3_false (upd : List ℕ → CG ℕ → List ℕ) (hupd : UpdValid upd) :
    ∃ r : Run (Fin 2) (Fin 2) (ℕ × Finset ℕ),
      (∀ p, r.F.Correct p) ∧ r.H ∈ Omega (Fin 2) r.F ∧ (∀ p t, r.H p t = 0) ∧
      (alg upd).Admissible r ∧ (tobHist upd r).Distinct ∧
      (∀ τ, ¬ ETOBStability r.F (tobHist upd r) τ) ∧ ¬ ETOB r.F (tobHist upd r) := by
  refine ⟨run, FailurePattern.noCrash_correct, const_mem_Omega _ 0 (FailurePattern.noCrash_correct 0),
    fun _ _ => rfl, admissible hupd, distinct, not_stability hupd, ?_⟩
  rintro ⟨-, -, -, -, τ, hτ, -⟩
  exact not_stability hupd τ hτ

/-- `UpdatePromote` can be implemented: when an admissible sequence exists, pick one (so
`lemma_3_false` is not vacuous). -/
lemma exists_updValid : ∃ upd : List ℕ → CG ℕ → List ℕ, UpdValid upd := by
  classical
  exact ⟨fun pr g => if h : ∃ s, UpdSpec pr g s then h.choose else pr, fun pr g h => by
    simp only [h, ↓reduceDIte]; exact h.choose_spec⟩

end Alg5

end Podc.WeakestFDEventualConsistency
