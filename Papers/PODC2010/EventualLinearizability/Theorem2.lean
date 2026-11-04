import Papers.PODC2010.EventualLinearizability.Runs
import Mathlib.Tactic.FinCases
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.SeqLin

/-!
# Theorem 2: no eventually linearizable register on top of Eventual Consistency

**Theorem 2** of the paper: there is no implementation of an eventually linearizable
single-writer single-reader binary register that uses only an eventually consistent layer.
We prove a stronger statement (`not_eventuallyLinearizable_eCons`): the impossibility holds
even on top of **Eventual Consensus** (Eventual Consistency + Eventual Stability), and even for
our weakened Eventual Linearizability (one `t_l` for all runs, `t_l`-linearizability required
only in runs without crashes, see `ImplModel.lean`). This **refutes the sufficiency part of
Theorem 3** of the paper (Eventual Consensus suffices to implement an eventually linearizable
object): with Eventual Consensus as the layer specification, no terminating implementation of a
register is eventually linearizable. `theorem2` (the paper's statement, for Eventual
Consistency) follows since Eventual Consensus implies Eventual Consistency.

The model is the one of `ImplModel.lean`: deterministic process automata reacting to
invocations, deliveries of the layer and ticks; the adversary schedules the actions and plays
the layer; termination (`Terminates`) is a hypothesis (without it, an implementation that never
responds would be vacuously eventually linearizable). `localImpl_terminates` shows that the
hypothesis is satisfiable.

## The argument (the paper's proof, with infinite admissible runs)

Fix `I`, `t_l` and termination. `w` = the write(true) of `p0`, `r` = the read of `p1`. All runs
end with the round-robin layer of `Runs.lean` (snapshots of the log), so they satisfy Eventual
Consensus.

* `R0` (`soloAdv 0 (write true) t_l`, only `p0` correct): idle up to `t_l`, `w` is invoked at
  `t_l + 1`, then round robin for `p0`. By termination `w` completes, by some time `t_w`.
* `R1` (`soloAdv 1 read t_w`, only `p1` correct): idle up to `t_w`, `r` is invoked at
  `t_w + 1`, then round robin for `p1`. By termination `r` completes, by some time `t_r`; by
  weak consistency `r` returns `false` (`resOf_read`): its `τ(r)` contains only `r`.
* `R2` (`glue`, no crash): copies `R0` up to `t_w` and `R1` from `t_w` to `t_r`, then round robin
  for both processes. Since every action of `R1` in `[t_w, t_r)` is an action of `p1`, and the
  reaction of `p1` depends only on its local state, `p1` behaves in `R2` as in `R1`
  (`glue_sim`): the history of `R2` at `t_r` is `H(R0, t_w) ++ H(R1, t_r)`. `R2` is admissible:
  before `t_r` deliveries are snapshots of `R0`'s log or of `R1`'s log (a part of `R2`'s log),
  and from `t_r` on the round-robin layer gives Eventual Consensus (stable from the end of the
  first round after `t_r`).
* In `R2`, `w` completes before `r` is invoked and `r` is invoked after `t_l`, so a
  `t_l`-linearization orders `w` before `r` and gives `r` its result `false`; but a legal
  sequential history with `write(true)` before `read` makes the read return `true`
  (`no_tlin`). Contradiction.
-/

namespace Podc.EventualLinearizability

open Cslib.SharedMemory.HerlihyWing Runs

namespace Theorem2

/-! ### Solo runs -/

section Solo

variable {P Op Res Msg : Type} [DecidableEq P] (I : Impl P Op Res Msg)

/-- The adversary of a solo run: idle up to time `t₀`, then `p_i` invokes `op` (at time
`t₀ + 1`), then the round-robin layer for `p_i` alone. -/
def soloAdv (i : P) (op : Op) (t₀ : ℕ) : Adversary I := fun t C =>
  if t < t₀ then .idle else if t = t₀ then .invoke i op else rrAct [i] (t₀ + 1) t C

variable {I} {i : P} {op : Op} {t₀ : ℕ}

lemma soloAdv_lt {t : ℕ} (h : t < t₀) : actAt I (soloAdv I i op t₀) t = .idle := by
  simp [actAt, soloAdv, h]

lemma soloAdv_eq : actAt I (soloAdv I i op t₀) t₀ = .invoke i op := by
  simp [actAt, soloAdv]

lemma soloAdv_rrTail : RRTail (soloAdv I i op t₀) [i] (t₀ + 1) where
  ne := by simp
  tail t ht := by
    simp [actAt, soloAdv, show ¬ t < t₀ by omega, show t ≠ t₀ by omega]
  pre t ht j s hd := by
    exfalso
    rcases Nat.lt_or_ge t t₀ with h | h
    · rw [soloAdv_lt h] at hd; cases hd
    · rw [show t = t₀ by omega, soloAdv_eq] at hd; cases hd

lemma soloAdv_proc (t : ℕ) :
    (actAt I (soloAdv I i op t₀) t).proc = none ∨ (actAt I (soloAdv I i op t₀) t).proc = some i := by
  rcases Nat.lt_or_ge t t₀ with h | h
  · left; rw [soloAdv_lt h]; rfl
  rcases Nat.eq_or_lt_of_le h with h | h
  · right; rw [← h, soloAdv_eq]; rfl
  · cases hp : (actAt I (soloAdv I i op t₀) t).proc with
    | none => exact Or.inl rfl
    | some k =>
      right
      by_contra hk
      exact soloAdv_rrTail.proc_ne (i := k) (by simpa [eq_comm] using hk) (by omega) hp

lemma soloAdv_proc_ne {j : P} (hj : j ≠ i) (t : ℕ) :
    (actAt I (soloAdv I i op t₀) t).proc ≠ some j := by
  rcases soloAdv_proc (I := I) (op := op) (t₀ := t₀) t with h | h <;> rw [h] <;> simp [Ne.symm hj]

lemma soloAdv_hist_nil {t : ℕ} (h : t ≤ t₀) : hist I (soloAdv I i op t₀) t = [] := by
  rw [hist, run_eq_init _ (fun t' ht' => soloAdv_lt (by omega))]; rfl

lemma soloAdv_opsOf (t : ℕ) (x : Unit) :
    opsOf (hist I (soloAdv I i op t₀) t) i x = if t₀ < t then [op] else [] := by
  split_ifs with h
  · rw [opsOf_hist_const _ (s := t₀ + 1) (by omega)
      (fun t' h1 _ => soloAdv_rrTail.ne_invoke h1), opsOf_hist_succ, soloAdv_eq,
      soloAdv_hist_nil le_rfl]
    simp [invOps]
  · rw [soloAdv_hist_nil (by omega)]; rfl

/-- Solo runs are admissible, with only `p_i` correct. -/
lemma soloAdv_admissible {spec : LayerRun P (Item P Msg) → Prop}
    (hspec : ∀ R, R.EventualConsensus → spec R) {allowed : P → Op → Prop} (hal : allowed i op) :
    Admissible I spec allowed (soloAdv I i op t₀) {i} where
  crash j hj := ⟨0, fun t _ => soloAdv_proc_ne (by simpa using hj) t⟩
  fair j hj := by
    obtain rfl : j = i := by simpa using hj
    exact soloAdv_rrTail.fair (by simp)
  env t j op' hact := by
    rcases Nat.lt_or_ge t t₀ with h | h
    · rw [soloAdv_lt h] at hact; cases hact
    rcases Nat.eq_or_lt_of_le h with h | h
    · subst h
      rw [soloAdv_eq] at hact
      cases hact
      exact ⟨hal, [], by rw [soloAdv_hist_nil le_rfl]; rfl⟩
    · exact absurd hact (soloAdv_rrTail.ne_invoke (by omega) j op')
  layer := hspec _ (soloAdv_rrTail.eventualConsensus (by simp))

end Solo

/-! ### Gluing two runs -/

section Glue

variable {P Op Res Msg : Type} [DecidableEq P] (I : Impl P Op Res Msg)

/-- Copy the actions of the run `A` up to time `tw`, then the actions of the run `B` up to time
`tr`, then the round-robin layer for `ps`. -/
def glue (A B : Adversary I) (tw tr : ℕ) (ps : List P) : Adversary I := fun t C =>
  if t < tw then actAt I A t else if t < tr then actAt I B t else rrAct ps tr t C

variable {I} {A B : Adversary I} {tw tr : ℕ} {ps : List P}

lemma glue_lt {t : ℕ} (h : t < tw) : actAt I (glue I A B tw tr ps) t = actAt I A t := by
  simp only [actAt, glue, h, ite_true]

lemma glue_mid {t : ℕ} (h1 : tw ≤ t) (h2 : t < tr) :
    actAt I (glue I A B tw tr ps) t = actAt I B t := by
  simp only [actAt, glue, show ¬ t < tw by omega, h2, ite_true, ite_false]

lemma glue_tail {t : ℕ} (htwr : tw ≤ tr) (h : tr ≤ t) :
    actAt I (glue I A B tw tr ps) t = rrAct ps tr t (run I (glue I A B tw tr ps) t) := by
  simp only [actAt, glue, show ¬ t < tw by omega, show ¬ t < tr by omega, ite_false]

lemma glue_run_le : ∀ t ≤ tw, run I (glue I A B tw tr ps) t = run I A t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, run_succ, glue_lt (by omega), ih (by omega)]

/-- The simulation relation between the glued run and the run `B` on `[tw, tr]`: process `j`
behaves as in `B`, the other processes are frozen at their state in `A` at time `tw`, and the
history and the log are those of `A` at `tw` followed by those of `B`. -/
structure GlueRel (A B : Adversary I) (j : P) (tw t : ℕ) (C : Cfg I) : Prop where
  loc : C.loc j = (run I B t).loc j
  nsub : C.nsub j = (run I B t).nsub j
  dlv : C.dlv j = (run I B t).dlv j
  loc_ne : ∀ k ≠ j, C.loc k = (run I A tw).loc k
  nsub_ne : ∀ k ≠ j, C.nsub k = (run I A tw).nsub k
  dlv_ne : ∀ k ≠ j, C.dlv k = (run I A tw).dlv k
  hist : C.hist = (run I A tw).hist ++ (run I B t).hist
  log : C.log = (run I A tw).log ++ (run I B t).log

/-- **Simulation**: if `B` is idle up to `tw` and only `p_j` acts in `B` on `[tw, tr)`, and `p_j`
has not acted in `A` before `tw`, then the glued run is related to `B` on `[tw, tr]`. -/
lemma glue_sim (j : P)
    (hB : ∀ t, tw ≤ t → t < tr → (actAt I B t).proc = none ∨ (actAt I B t).proc = some j)
    (hAj : (run I A tw).loc j = I.init j ∧ (run I A tw).nsub j = 0 ∧ (run I A tw).dlv j = [])
    (hBinit : run I B tw = Cfg.init I) :
    ∀ t, tw ≤ t → t ≤ tr → GlueRel A B j tw t (run I (glue I A B tw tr ps) t) := by
  intro t h1 h2
  induction t, h1 using Nat.le_induction with
  | base =>
    rw [glue_run_le tw le_rfl]
    refine ⟨?_, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_⟩ <;>
      rw [hBinit] <;>
      first | exact hAj.1 | exact hAj.2.1 | exact hAj.2.2 | exact (List.append_nil _).symm
  | succ t ht ih =>
    have ih := ih (by omega)
    have hact := glue_mid (A := A) (B := B) (ps := ps) ht (show t < tr by omega)
    have hp := hB t ht (by omega)
    obtain ⟨h1, h2, h3, ⟨δ, hδ1, hδ2⟩, ⟨new, hn1, hn2⟩⟩ :=
      step_congr (t := t + 1) hp ih.loc ih.nsub ih.dlv
    have hne : ∀ k ≠ j, (actAt I B t).proc ≠ some k := by
      intro k hk; rcases hp with hp | hp <;> rw [hp] <;> simp [Ne.symm hk]
    rw [run_succ, hact]
    refine ⟨h1, h2, h3, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
    · rw [step_loc_of_ne (hne k hk)]; exact ih.loc_ne k hk
    · rw [step_nsub_of_ne (hne k hk)]; exact ih.nsub_ne k hk
    · rw [step_dlv_of_ne (fun s hs => hne k hk (by rw [hs]; rfl))]; exact ih.dlv_ne k hk
    · rw [hδ1, run_succ, hδ2, ih.hist, List.append_assoc]
    · rw [hn1, run_succ, hn2, ih.log, List.append_assoc]

/-- The glued run is admissible, without crashes. -/
lemma glue_admissible {spec : LayerRun P (Item P Msg) → Prop}
    (hspec : ∀ R, R.EventualConsensus → spec R) {allowed : P → Op → Prop} (j : P)
    {cA cB : Set P} {psA psB : List P} {TA TB : ℕ}
    (hA : Admissible I spec allowed A cA) (hB : Admissible I spec allowed B cB)
    (hArr : RRTail A psA TA) (hBrr : RRTail B psB TB)
    (hBproc : ∀ t, tw ≤ t → t < tr → (actAt I B t).proc = none ∨ (actAt I B t).proc = some j)
    (hAj : (run I A tw).loc j = I.init j ∧ (run I A tw).nsub j = 0 ∧ (run I A tw).dlv j = [] ∧
      restrictP (hist I A tw) j = [])
    (hBinit : run I B tw = Cfg.init I) (htwr : tw ≤ tr) (hps : ps ≠ []) (hall : ∀ k, k ∈ ps) :
    Admissible I spec allowed (glue I A B tw tr ps) Set.univ := by
  have hsim := glue_sim (ps := ps) (tr := tr) j hBproc ⟨hAj.1, hAj.2.1, hAj.2.2.1⟩ hBinit
  have hrr : RRTail (glue I A B tw tr ps) ps tr :=
    { ne := hps
      tail := fun t ht => glue_tail htwr ht
      pre := fun t ht k s hd => by
        by_cases h : t < tw
        · rw [glue_lt h] at hd
          have := hArr.goodDeliv hd
          simpa only [GoodDeliv, items, glue_run_le t h.le] using this
        · rw [glue_mid (by omega) ht] at hd
          obtain rfl : k = j := by
            rcases hBproc t (by omega) ht with hp | hp <;> rw [hd] at hp <;>
              simp [Act.proc] at hp
            exact hp
          obtain ⟨g1, g2, g3⟩ := hBrr.goodDeliv hd
          have hs := hsim t (by omega) ht.le
          refine ⟨g1, fun o ho => ?_, fun o ho => g3 o (hs.dlv ▸ ho)⟩
          simp only [items, hs.log, List.map_append, List.mem_append]
          exact Or.inr (g2 o ho) }
  refine ⟨fun k hk => absurd (Set.mem_univ k) hk, fun k _ => hrr.fair (hall k), ?_,
    hspec _ (hrr.eventualConsensus fun k _ => hall k)⟩
  intro t k op hact
  by_cases h1 : t < tw
  · rw [glue_lt h1] at hact
    obtain ⟨hal, M, hM⟩ := hA.env t k op hact
    exact ⟨hal, M, by rw [hist, glue_run_le t h1.le]; exact hM⟩
  by_cases h2 : t < tr
  · rw [glue_mid (by omega) h2] at hact
    obtain ⟨hal, M, hM⟩ := hB.env t k op hact
    obtain rfl : k = j := by
      rcases hBproc t (by omega) h2 with hp | hp <;> rw [hact] at hp <;>
        simp [Act.proc] at hp
      exact hp
    refine ⟨hal, M, ?_⟩
    rw [hist, (hsim t (by omega) h2.le).hist, restrictP_append]
    rw [hist] at hM
    have := hAj.2.2.2
    rw [hist] at this
    rw [this, hM, List.nil_append]
  · exact absurd hact (hrr.ne_invoke (by omega) k op)

end Glue

/-! ### The register: concrete facts -/

/-- The write(true) of `p0`. -/
def wId : OpId (Fin 2) Unit := ⟨0, (), 0⟩

/-- The read of `p1`. -/
def rId : OpId (Fin 2) Unit := ⟨1, (), 0⟩

lemma legal_reg {M : List (OpRec (Fin 2) Unit RWOp (Option Bool))} :
    Legal regSpec (seqHist M) ↔ runOK rwδ false M := by
  rw [legal_seqHist_iff_of_subsingleton ()]
  exact seqHist_mem_detSpec

lemma invoked_two {H : History (Fin 2) Unit RWOp (Option Bool)}
    (h0 : (opsOf H 0 ()).length ≤ 1) (h1 : (opsOf H 1 ()).length ≤ 1) {a : OpId (Fin 2) Unit}
    (ha : Invoked H a) : a = wId ∨ a = rId := by
  obtain ⟨p, x, k⟩ := a
  have h0' : (opsOf H 0 x).length ≤ 1 := h0
  have h1' : (opsOf H 1 x).length ≤ 1 := h1
  simp only [Invoked] at ha
  obtain rfl | rfl : p = 0 ∨ p = 1 := by fin_cases p <;> simp
  · left; obtain rfl : k = 0 := by omega
    rfl
  · right; obtain rfl : k = 0 := by omega
    rfl

/-- Weak consistency forces a read that is the only operation invoked to return `false`. -/
lemma resOf_read {H : History (Fin 2) Unit RWOp (Option Bool)} (h0 : opsOf H 0 () = [])
    (h1 : opsOf H 1 () = [.read]) (hc : Completed H rId) (hwc : WeaklyConsistent regSpec H) :
    resOf H rId = some (some false) := by
  obtain ⟨τ, hτ⟩ := hwc
  obtain ⟨hseq, ⟨e, hlast, hres⟩, -, -⟩ := hτ rId hc
  have hall : ∀ ae ∈ τ rId, ae.1 = rId := by
    intro ae hae
    have hi := Invoked.of_opOf (hseq.ofHist ae hae).2.2
    rcases invoked_two (by simp [h0]) (by simp [h1]) hi with h | h
    · rw [h] at hi; simp [Invoked, wId, h0] at hi
    · exact h
  have hlen : (τ rId).length ≤ 1 := by
    have hsub : (τ rId).ids ⊆ [rId] := fun a ha => by
      obtain ⟨ae, hae, rfl⟩ := List.mem_map.1 ha
      simp [hall ae hae]
    simpa [IdSeq.ids] using (hseq.nodup.subperm hsub).length_le
  have hτeq : τ rId = [(rId, e)] := by
    rcases h : τ rId with _ | ⟨x, _ | ⟨y, l⟩⟩
    · rw [h] at hlast; simp at hlast
    · rw [h] at hlast; simpa using hlast
    · rw [h] at hlen; simp at hlen
  have hof := (hseq.ofHist (rId, e) (by simp [hτeq])).2.2
  have hop : opOf H rId = some .read := by simp [opOf, rId, h1]
  rw [hop, Option.some.injEq] at hof
  have hleg := legal_reg.1 hseq.legal
  rw [hτeq] at hleg
  obtain ⟨p, x, o, r⟩ := e
  simp only at hof
  subst hof
  simp [IdSeq.recs, runOK, rwδ] at hleg
  rw [hres, ← hleg]

/-- In a history where `w = write(true)` precedes `r = read`, `r` returns `false` and `r` is
late, there is no `t`-linearization. -/
lemma no_tlin {H : History (Fin 2) Unit RWOp (Option Bool)} (h0 : opsOf H 0 () = [.write true])
    (h1 : opsOf H 1 () = [.read]) (hres : resOf H rId = some (some false))
    (hprec : Precedes H wId rId) {A : Set (OpId (Fin 2) Unit)} (hA : rId ∈ A)
    {L : IdSeq (Fin 2) Unit RWOp (Option Bool)} (hL : IsTLin regSpec H A L) : False := by
  have hinv_r : Invoked H rId := by simp [Invoked, rId, h1]
  have hord := hL.order wId rId ⟨hA, hinv_r, hprec⟩
  have hsub : L.ids ⊆ [wId, rId] := fun a ha => by
    obtain ⟨ae, hae, rfl⟩ := List.mem_map.1 ha
    rcases invoked_two (by simp [h0]) (by simp [h1]) (Invoked.of_opOf (hL.ofHist ae hae).2.2)
      with h | h <;> simp [h]
  have hlen : L.ids.length ≤ 2 := by simpa using (hL.nodup.subperm hsub).length_le
  have hids : L.ids = [wId, rId] := (hord.eq_of_length_le (by simpa using hlen)).symm
  rcases L with _ | ⟨⟨a1, e1⟩, _ | ⟨⟨a2, e2⟩, _ | ⟨z, l⟩⟩⟩ <;> simp [IdSeq.ids] at hids
  obtain ⟨rfl, rfl⟩ := hids
  have hw := (hL.ofHist (wId, e1) (by simp)).2.2
  have hr := (hL.ofHist (rId, e2) (by simp)).2.2
  rw [show opOf H wId = some (.write true) by simp [opOf, wId, h0], Option.some.injEq] at hw
  rw [show opOf H rId = some .read by simp [opOf, rId, h1], Option.some.injEq] at hr
  have hleg := legal_reg.1 hL.legal
  have hres' := hL.results rId e2 (by simp) hA (Completed.of_resOf hres)
  obtain ⟨p1, x1, o1, r1⟩ := e1
  obtain ⟨p2, x2, o2, r2⟩ := e2
  simp only at hw hr hres'
  subst hw hr
  simp [IdSeq.recs, runOK, rwδ] at hleg
  rw [hres, ← hleg.2] at hres'
  simp at hres'

end Theorem2

open Theorem2

/-- **Theorem 2, strengthened** (and refutation of the sufficiency part of Theorem 3): no
terminating implementation of a single-writer single-reader binary register on top of a
consistency layer satisfying **Eventual Consensus** is eventually linearizable. -/
theorem not_eventuallyLinearizable_eCons {Msg : Type}
    (I : Impl (Fin 2) RWOp (Option Bool) Msg) (hterm : Terminates I eConsSpec swsr) :
    ¬ EventuallyLinearizable I eConsSpec swsr regSpec := by
  rintro ⟨tl, hEL⟩
  have hspec : ∀ R : LayerRun (Fin 2) (Item (Fin 2) Msg), R.EventualConsensus → eConsSpec R :=
    fun _ h => h
  -- Run `R0`: `p0` writes `true` at time `tl + 1`, alone.
  let A := soloAdv I (0 : Fin 2) (.write true) tl
  have hadmA : Admissible I eConsSpec swsr A {0} := soloAdv_admissible hspec trivial
  have hopsA : ∀ t, opsOf (hist I A t) 0 () = if tl < t then [.write true] else [] :=
    fun t => soloAdv_opsOf t ()
  have hA1 : ∀ t, (run I A t).loc 1 = I.init 1 ∧ (run I A t).nsub 1 = 0 ∧
      (run I A t).dlv 1 = [] ∧ restrictP (hist I A t) 1 = [] :=
    fun t => not_acted A (fun t' _ => soloAdv_proc_ne (by decide) t')
  obtain ⟨tw0, htw0⟩ := hterm A {0} hadmA wId (tl + 1) rfl (by simp [Invoked, hopsA, wId])
  set tw := max tw0 (tl + 1) with htw
  have hw : Completed (hist I A tw) wId := completed_mono A (le_max_left _ _) htw0
  -- Run `R1`: `p1` reads at time `tw + 1`, alone.
  let B := soloAdv I (1 : Fin 2) .read tw
  have hadmB : Admissible I eConsSpec swsr B {1} := soloAdv_admissible hspec trivial
  have hopsB : ∀ t, opsOf (hist I B t) 1 () = if tw < t then [.read] else [] :=
    fun t => soloAdv_opsOf t ()
  have hB0 : ∀ t, restrictP (hist I B t) 0 = [] :=
    fun t => (not_acted B (fun t' _ => soloAdv_proc_ne (by decide) t')).2.2.2
  obtain ⟨tr0, htr0⟩ := hterm B {1} hadmB rId (tw + 1) rfl (by simp [Invoked, hopsB, rId])
  set tr := max tr0 (tw + 1) with htr
  have hr : Completed (hist I B tr) rId := completed_mono B (le_max_left _ _) htr0
  -- In `R1`, the read returns `false`.
  have hresB : resOf (hist I B tr) rId = some (some false) :=
    resOf_read (opsOf_eq_nil_of_restrictP (hB0 tr) ()) (by rw [hopsB, ite_eq_left (by omega)]) hr
      (hEL B {1} hadmB tr).1
  -- Run `R2`: `R0` up to `tw`, then `R1` up to `tr`, then round robin for both processes.
  let G := glue I A B tw tr [0, 1]
  have hBproc : ∀ t, tw ≤ t → t < tr →
      (actAt I B t).proc = none ∨ (actAt I B t).proc = some 1 := fun t _ _ => soloAdv_proc t
  have hBinit : run I B tw = Cfg.init I := run_eq_init B (fun t' ht' => soloAdv_lt ht')
  have hadmG : Admissible I eConsSpec swsr G Set.univ :=
    glue_admissible hspec 1 hadmA hadmB soloAdv_rrTail soloAdv_rrTail hBproc (hA1 tw) hBinit
      (by omega) (by simp) (fun k => by fin_cases k <;> simp)
  have hsim := glue_sim (A := A) (B := B) (ps := [0, 1]) (tr := tr) (1 : Fin 2) hBproc
    ⟨(hA1 tw).1, (hA1 tw).2.1, (hA1 tw).2.2.1⟩ hBinit tr (by omega) le_rfl
  have hG : hist I G tr = hist I A tw ++ hist I B tr := hsim.hist
  -- The history of `R2` at `tr`.
  have h0 : opsOf (hist I G tr) 0 () = [.write true] := by
    rw [hG, opsOf_append, hopsA, ite_eq_left (by omega), opsOf_eq_nil_of_restrictP (hB0 tr)]; rfl
  have h1 : opsOf (hist I G tr) 1 () = [.read] := by
    rw [hG, opsOf_append, hopsB, ite_eq_left (by omega), opsOf_eq_nil_of_restrictP (hA1 tw).2.2.2]
    rfl
  have hres : resOf (hist I G tr) rId = some (some false) := by
    rw [← hresB, hG]
    simp only [resOf, rId, ressOf_append, ressOf_eq_nil_of_restrictP (hA1 tw).2.2.2,
      List.nil_append]
  have hprec : Precedes (hist I G tr) wId rId :=
    ⟨hist I A tw, hist I B tr, hG, hw, by
      simp [Invoked, rId, opsOf_eq_nil_of_restrictP (hA1 tw).2.2.2]⟩
  have hlate : rId ∈ {a | ¬ Invoked (hist I G tl) a} := by
    have : hist I G tl = hist I A tl := by
      rw [hist, hist, glue_run_le tl (by omega)]
    simp [this, Invoked, rId, opsOf_eq_nil_of_restrictP (hA1 tl).2.2.2]
  obtain ⟨L, hL⟩ := (hEL G Set.univ hadmG tr).2 rfl
  exact no_tlin h0 h1 hres hprec hlate hL

/-- Admissibility is monotone in the layer specification. -/
lemma Admissible.mono_spec {P Op Res Msg : Type} [DecidableEq P] {I : Impl P Op Res Msg}
    {spec spec' : LayerRun P (Item P Msg) → Prop} (hs : ∀ R, spec R → spec' R)
    {allowed : P → Op → Prop} {adv : Adversary I} {correct : Set P}
    (h : Admissible I spec allowed adv correct) : Admissible I spec' allowed adv correct :=
  { h with layer := hs _ h.layer }

/-- **Theorem 2** of the paper: no terminating implementation of a single-writer single-reader
binary register on top of an eventually consistent layer is eventually linearizable. -/
theorem theorem2 {Msg : Type} (I : Impl (Fin 2) RWOp (Option Bool) Msg)
    (hterm : Terminates I ecSpec swsr) : ¬ EventuallyLinearizable I ecSpec swsr regSpec := by
  have hs : ∀ R : LayerRun (Fin 2) (Item (Fin 2) Msg), eConsSpec R → ecSpec R := fun _ h => h.1
  intro ⟨tl, hEL⟩
  refine not_eventuallyLinearizable_eCons I (fun adv correct h => hterm adv correct
    (h.mono_spec hs)) ⟨tl, fun adv correct h => hEL adv correct (h.mono_spec hs)⟩

/-! ### Non-vacuity: termination is satisfiable -/

/-- A trivial implementation: every process answers immediately from a local copy of the
register and never uses the layer. -/
def localImpl : Impl (Fin 2) RWOp (Option Bool) Unit where
  State := Bool
  init _ := false
  onInvoke _ s op := ((rwδ s op).1, [], some (rwδ s op).2)
  onDeliver _ s _ := (s, [], none)
  onTick _ s := (s, [], none)

lemma localImpl_ops_eq_ress (adv : Adversary localImpl) (t : ℕ) (p : Fin 2) (x : Unit) :
    (opsOf (hist localImpl adv t) p x).length = (ressOf (hist localImpl adv t) p x).length := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hI : ∀ i s op, localImpl.onInvoke i s op = ((rwδ s op).1, [], some (rwδ s op).2) :=
      fun _ _ _ => rfl
    have hD : ∀ i s l, localImpl.onDeliver i s l = (s, [], none) := fun _ _ _ => rfl
    have hT : ∀ i s, localImpl.onTick i s = (s, [], none) := fun _ _ => rfl
    simp only [hist, run_succ] at ih ⊢
    cases actAt localImpl adv t with
    | idle => exact ih
    | invoke i op =>
      by_cases h : i = p
      · subst h; cases x; simp [Cfg.step, Cfg.apply, hI, ih]
      · cases x; simp [Cfg.step, Cfg.apply, hI, h, ih]
    | deliver i s => simp [Cfg.step, Cfg.apply, hD, ih]
    | tick i => simp [Cfg.step, Cfg.apply, hT, ih]

/-- The hypothesis `Terminates` of Theorem 2 is satisfiable (for any layer specification). -/
theorem localImpl_terminates (spec : LayerRun (Fin 2) (Item (Fin 2) Unit) → Prop) :
    Terminates localImpl spec swsr := by
  intro adv correct _ a t _ ha
  refine ⟨t, ?_⟩
  simp only [Completed, Invoked] at ha ⊢
  rw [← localImpl_ops_eq_ress]; exact ha

end Podc.EventualLinearizability
