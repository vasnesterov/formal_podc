import Cslib.Computability.Distributed.Byzantine.LockStep.Agreement
import Papers.PODC2013.CubicBitsBA.Counterexample

/-!
# The protocol in CSLib's synchronous lock-step model

`protocol t v0` is the Kowalski–Mostéfaoui protocol as a CSLib `LockStep.Protocol` on the complete
graph `⊤` (deterministic, history-based, unauthenticated Byzantine adversary; CSLib histories
contain no self-messages, so a process recomputes its own messages from its history: `fullView`).

* `execOf`: every reliable lock-step run is an `Exec` with the same decisions (`decides_iff`).
* `validity_termination`: in every reliable run with `≤ t` Byzantine parties and `n > 3t`, all honest
  parties decide in round `t + 1`, and validity holds (from `theorem_1`).
* `not_solves_BA`: for `n = 7`, `t = 2` and either default value, the protocol does **not** solve
  Byzantine agreement (`Cslib.Byzantine.LockStep.BA`) against `≤ 2` Byzantine parties.
-/

namespace Podc.CubicBitsBA

open Cslib.Byzantine.LockStep

variable {n : ℕ} {V : Type} [DecidableEq V]

/-- Rounds `1..k` of the view of `p` rebuilt from its lock-step history `h`; the messages `p` sent
to itself are recomputed with `out`. -/
def fullView (t : ℕ) (p : Fin n) (x : V) (h : History (Fin n) (Msg n V)) : ℕ → View n V
  | 0 => fun _ _ => none
  | k + 1 => fun r j =>
    if r = k + 1 then
      (if j = p then some (out t x (fullView t p x h k) (k + 1)) else (h[k]?).bind (· j))
    else fullView t p x h k r j

/-- The protocol as a CSLib lock-step protocol: broadcast `out` of the current view; decide
`decision` after `t + 1` rounds. -/
def protocol (t : ℕ) (v0 : V) : Protocol (Fin n) V (Msg n V) V where
  send p x h _ := some (out t x (fullView t p x h h.length) (h.length + 1))
  decide p x h := if h.length = t + 1 then some (decision t v0 (fullView t p x h h.length)) else none

lemma fullView_out_of_range (t : ℕ) (p : Fin n) (x : V) (h : History (Fin n) (Msg n V)) :
    ∀ k r, (r = 0 ∨ k < r) → fullView t p x h k r = fun _ => none
  | 0, _, _ => rfl
  | k + 1, r, hr => by
    funext j
    simp only [fullView]
    rw [ite_eq_right (by omega), fullView_out_of_range t p x h k r (by omega)]

lemma fullView_mono (t : ℕ) (p : Fin n) (x : V) (h : History (Fin n) (Msg n V)) {r k : ℕ}
    (hrk : r ≤ k) : ∀ K, k ≤ K → fullView t p x h K r = fullView t p x h k r
  | 0, hK => by obtain rfl : k = 0 := by omega
                rfl
  | K + 1, hK => by
    rcases Nat.eq_or_lt_of_le hK with rfl | hK'
    · rfl
    · funext j
      simp only [fullView]
      rw [ite_eq_right (by omega), fullView_mono t p x h hrk K (by omega)]

lemma fullView_congr (t : ℕ) (p : Fin n) (x : V) {h h' : History (Fin n) (Msg n V)} :
    ∀ k, (∀ k' < k, h[k']? = h'[k']?) → fullView t p x h k = fullView t p x h' k
  | 0, _ => rfl
  | k + 1, hh => by
    have ih := fullView_congr t p x k (fun k' hk' => hh k' (by omega))
    funext r j
    simp only [fullView, ih, hh k (by omega)]

section Run

variable (t : ℕ) (v0 : V) (s : Scenario (Fin n) V (Msg n V))

/-- The view of `p` after the `t + 1` rounds of the lock-step run. -/
noncomputable def runView (p : Fin n) : View n V :=
  fullView t p (s.input p) (hist ⊤ (protocol t v0) s (t + 1) p) (t + 1)

lemma getElem?_hist_bind {k R : ℕ} (hk : k < R) (q p : Fin n) :
    ((hist ⊤ (protocol (n := n) t v0) s R p)[k]?).bind (· q) =
      deliver ⊤ (protocol t v0) s (hist ⊤ (protocol t v0) s k) k q p := by
  rw [getElem?_hist _ _ _ hk]
  rfl

lemma runView_succ {k : ℕ} (hk : k ≤ t) (p : Fin n) :
    runView t v0 s p (k + 1) = fun j =>
      if j = p then some (out t (s.input p) (runView t v0 s p) (k + 1))
      else deliver ⊤ (protocol t v0) s (hist ⊤ (protocol t v0) s k) k j p := by
  funext j
  have e : runView t v0 s p (k + 1) = fullView t p (s.input p) (hist ⊤ (protocol t v0) s (t + 1) p)
      (k + 1) (k + 1) := fullView_mono t p _ _ le_rfl (t + 1) (by omega)
  rw [e]
  show (if k + 1 = k + 1 then _ else _) = _
  rw [ite_eq_left rfl]
  split_ifs with hj
  · congr 1
    apply out_congr
    intro r' _ hr'
    rw [runView, fullView_mono t p _ _ (show r' ≤ k by omega) (t + 1) (by omega)]
  · exact getElem?_hist_bind t v0 s (by omega) j p

/-- Every reliable lock-step run of `protocol t v0` is an execution (`Exec`). -/
noncomputable def execOf (hrel : s.Reliable) : Exec n t V where
  byz := (Set.toFinite s.byz).toFinset
  input := s.input
  view := runView t v0 s
  honest := by
    intro j hj i r h1 hr
    rw [Set.Finite.mem_toFinset] at hj
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    rw [runView_succ t v0 s (by omega)]
    beta_reduce
    split_ifs with hji
    · subst hji; rfl
    · rw [deliver_honest _ _ _ hrel hj ((SimpleGraph.top_adj j i).mpr hji)]
      simp only [protocol, length_hist]
      congr 1
      apply out_congr
      intro r' _ hr'
      rw [runView, fullView_mono t j _ _ (show r' ≤ k by omega) (t + 1) (by omega)]
      have hc := fullView_congr t j (s.input j) (h := hist ⊤ (protocol t v0) s (t + 1) j)
        (h' := hist ⊤ (protocol t v0) s k j) k (fun k' hk' => by
          rw [← take_hist _ _ _ (show k ≤ t + 1 by omega) j, List.getElem?_take_of_lt hk'])
      rw [hc]
      rfl

/-- Decisions in the lock-step run are the decisions of the execution. -/
lemma decides_iff (hrel : s.Reliable) (p : Fin n) (o : V) :
    Decides ⊤ (protocol t v0) s p o ↔ o = (execOf t v0 s hrel).decide v0 p := by
  have hst : ∀ r, status ⊤ (protocol t v0) s r p =
      if r = t + 1 then some ((execOf t v0 s hrel).decide v0 p) else none := by
    intro r
    simp only [status, protocol, length_hist]
    split_ifs with hr
    · subst hr; rfl
    · rfl
  constructor
  · rintro ⟨r, hr, -⟩
    rw [hst] at hr
    split_ifs at hr
    exact (Option.some_injective _ hr).symm
  · rintro rfl
    refine ⟨t + 1, by rw [hst, ite_eq_left rfl], fun r' hr' => by rw [hst, ite_eq_right (by omega)]⟩

lemma card_execOf_byz (hrel : s.Reliable) :
    (execOf t v0 s hrel).byz.card = s.byz.ncard := by
  rw [Set.ncard_eq_toFinset_card s.byz]
  rfl

/-- In every reliable lock-step run with at most `t` Byzantine parties and `n > 3t`, every honest
party decides (in round `t + 1`), and validity holds (Theorem 1 of the paper). -/
theorem validity_termination (hn : 3 * t < n) (hrel : s.Reliable) (hb : s.byz.ncard ≤ t) :
    (∀ p ∈ s.honest, ∃ v, Decides ⊤ (protocol t v0) s p v) ∧
    (∀ v, (∀ p ∈ s.honest, s.input p = v) → ∀ p ∈ s.honest, Decides ⊤ (protocol t v0) s p v) := by
  have hb' : (execOf t v0 s hrel).byz.card ≤ t := by rw [card_execOf_byz]; exact hb
  have hmem : ∀ p, p ∉ (execOf t v0 s hrel).byz ↔ p ∈ s.honest := by
    intro p
    simp [execOf, Set.Finite.mem_toFinset, Scenario.honest]
  refine ⟨fun p _ => ⟨_, (decides_iff t v0 s hrel p _).mpr rfl⟩, fun v hv p hp => ?_⟩
  rw [decides_iff t v0 s hrel]
  exact (theorem_1 (execOf t v0 s hrel) hn hb' v0 v
    (fun j hj => hv j ((hmem j).mp hj)) ((hmem p).mpr hp)).symm

end Run

/-! ### Uniqueness of executions -/

/-- Two executions with the same Byzantine set, the same correct inputs and the same Byzantine
messages to correct processes agree on the views of the correct processes in rounds `1..t+1`. -/
lemma Exec.view_eq {t : ℕ} {E E' : Exec n t V} (hbyz : E.byz = E'.byz)
    (hin : ∀ j ∉ E.byz, E.input j = E'.input j)
    (hadv : ∀ i ∉ E.byz, ∀ b ∈ E.byz, ∀ r, 1 ≤ r → r ≤ t + 1 → E.view i r b = E'.view i r b) :
    ∀ r, 1 ≤ r → r ≤ t + 1 → ∀ i ∉ E.byz, E.view i r = E'.view i r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro h1 hr i hi
    funext j
    by_cases hj : j ∈ E.byz
    · exact hadv i hi j hj r h1 hr
    · rw [E.honest j hj i r h1 hr, E'.honest j (hbyz ▸ hj) i r h1 hr, hin j hj]
      congr 1
      exact out_congr t _ fun r' h1' hr' => ih r' hr' h1' (by omega) j hj

/-! ### The counterexample as a lock-step run -/

namespace Counterexample

/-- The lock-step scenario of `exec f`: Byzantine set `{5, 6}`, Byzantine messages read off
`exec f`. -/
def scen (f : Bool) : Scenario (Fin 7) Bool (Msg 7 Bool) where
  byz := {5, 6}
  input := inp f
  adv r p q := (exec f).view q (r + 1) p

lemma scen_reliable (f : Bool) : (scen f).Reliable := fun _ _ _ h => h

lemma view_out_of_range (f : Bool) (i : Fin 7) (r : ℕ) (hr : r = 0 ∨ 2 + 1 < r) :
    (exec f).view i r = fun _ => none := by
  funext j
  simp only [exec, V3, V2, V1]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

lemma runView_scen (f : Bool) (v0 : Bool) (i : Fin 7) (hi : i ∉ (exec f).byz) :
    (execOf 2 v0 (scen f) (scen_reliable f)).view i = (exec f).view i := by
  have hbyz : (execOf 2 v0 (scen f) (scen_reliable f)).byz = (exec f).byz := by
    ext b; simp [execOf, scen, exec]
  have key := Exec.view_eq (E := execOf 2 v0 (scen f) (scen_reliable f)) (E' := exec f) hbyz
    (fun _ _ => rfl) (by
      intro i hi b hb r h1 hr
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
      have hib : b ≠ i := fun e => hi (e ▸ hb)
      change runView 2 v0 (scen f) i (k + 1) b = _
      rw [runView_succ 2 v0 (scen f) (by omega)]
      beta_reduce
      rw [ite_eq_right hib]
      rw [hbyz] at hb
      rw [deliver_byz _ _ _ (by simpa [exec, scen] using hb) ((SimpleGraph.top_adj b i).mpr hib)]
      rfl)
  funext r
  by_cases hr : 1 ≤ r ∧ r ≤ 2 + 1
  · exact key r hr.1 hr.2 i (hbyz ▸ hi)
  · rw [view_out_of_range f i r (by omega)]
    exact fullView_out_of_range 2 i _ _ (2 + 1) r (by omega)

/-- **Theorem 2 refuted in CSLib's model**: for `n = 7`, `t = 2` and either default value, the
Kowalski–Mostéfaoui protocol does not solve Byzantine agreement against `≤ 2` Byzantine parties
on reliable synchronous channels. -/
theorem not_solves_BA (v0 : Bool) :
    ¬ Solves (⊤ : SimpleGraph (Fin 7)) (protocol 2 v0) (atMost 2) BA := by
  intro h
  have hrel := scen_reliable (!v0)
  have hZ : (scen (!v0)).byz ∈ (atMost 2 : AdvStructure (Fin 7)) := by
    show Set.ncard ({5, 6} : Set (Fin 7)) ≤ 2
    rw [Set.ncard_pair (by decide)]
  obtain ⟨-, -, hagr⟩ := h (scen (!v0)) hZ hrel
  have hdec : ∀ i : Fin 7, i ∉ (exec (!v0)).byz →
      Decides ⊤ (protocol 2 v0) (scen (!v0)) i ((exec (!v0)).decide v0 i) := by
    intro i hi
    rw [decides_iff 2 v0 _ hrel, Exec.decide, Exec.decide, runView_scen _ v0 i hi]
  have h0 := decide_exec (!v0) 0 (by decide)
  have h3 := decide_exec (!v0) 3 (by decide)
  rw [Bool.not_not] at h0 h3
  have := hagr 0 (by simp [scen, Scenario.honest]) 3 (by simp [scen, Scenario.honest]) _ _
    (hdec 0 (correct_0 _)) (hdec 3 (correct_3 _))
  rw [h0, h3] at this
  revert this
  cases v0 <;> decide

end Counterexample

end Podc.CubicBitsBA
