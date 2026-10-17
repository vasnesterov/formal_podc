import Papers.PODC2025.ByzantineStableMatching.Lemma1
import Papers.PODC2025.ByzantineStableMatching.Hypotheses
import Podc.LockStep.Basic
import Podc.Foundations.Count

/-!
# The protocol `ΠbSM` (Section 5.2, Lemmas 9, 11, 12) — before channel simulation

The paper's `ΠbSM` for the bipartite authenticated network with `tL < k/3` (`R` possibly entirely
Byzantine) consists of
1. `R`-parties send their lists to all of `L`;
2. `L`-parties run one `ΠBB` per `L`-party (its own list) and one `ΠBA` per `R`-party (the list
   received from it), among themselves, over channels simulated through `R` (Lemma 10: delay `2Δ`,
   omissions only if all of `R` is Byzantine);
3. `L`-parties decide nobody if some instance output `⊥`, otherwise run Gale–Shapley on the agreed
   lists, decide accordingly and tell every `R`-party its partner;
4. `R`-parties decide the most common suggestion.

Here we define and verify the protocol `Φ` of steps 1–4 on the network `oneSidedR k` (`L` fully
connected, `L–R` edges, no `R–R` edges), where `L–L` messages may be *omitted* provided all of `R` is
Byzantine. The signature relay (Lemma 10, `Cslib.Byzantine.LockStep.Relay`) then turns `Φ` into a protocol
on the bipartite (or one-sided) network.

Differences: `R`-parties decide by strict majority of the suggestions (`none` if there is none)
instead of plurality — under the protocol's assumptions the honest suggestion is a strict majority, so
the two rules agree whenever it matters.
-/

namespace Papers.PODC2025.ByzantineStableMatching

open Cslib.Byzantine.LockStep Sum Cslib.StableMatching

namespace PiBSM

variable {k : ℕ}

/-- Preference lists. -/
abbrev Pref (k : ℕ) := Equiv.Perm (Fin k)

/-- The specification of instance `i` of the `L`-protocol: BB with sender `inl s` for `i = inl s`,
BA (on the list received from `inr j`) for `i = inr j`. -/
def instSpec : Party k → Spec (Party k) (Pref k) (Pref k)
  | inl s => BB (inl s)
  | inr _ => BA

/-- The building blocks: one protocol per instance, all terminating within `T` rounds. -/
structure LData (k tL : ℕ) where
  /-- Message types. -/
  M : Party k → Type
  /-- Instance protocols. -/
  alg : (i : Party k) → Protocol (Party k) (Pref k) (M i) (Option (Pref k))
  /-- Common round bound. -/
  T : ℕ
  /-- Theorems 8/9. -/
  solves : ∀ i, SolvesWithOmissions (lClique k) (alg i) (thresholds k tL k)
    (onL (SomeSpec (instSpec i))) (onL WeakAgreement) T

variable {tL : ℕ} (D : LData k tL)

/-- Messages of the `L`-protocol. -/
abbrev LMsg := (i : Party k) → Option (D.M i)

/-- The `L`-protocol: all instances in parallel; the input of instance `i` is the `i`-th entry. -/
noncomputable def lam : Protocol (Party k) (Party k → Pref k) (LMsg D) (Party k → Option (Pref k)) :=
  Protocol.parallel fun i => (D.alg i).comapInput (fun v => v i)

/-- Messages of `Φ`. -/
inductive Msg (k : ℕ) (N : Type) where
  | list : Pref k → Msg k N
  | inner : N → Msg k N
  | suggest : Fin k → Msg k N

variable {N : Type}

/-- Extract an inner message. -/
def Msg.getInner : Msg k N → Option N
  | .inner m => some m
  | _ => none

/-- Extract a list. -/
def Msg.getList : Msg k N → Option (Pref k)
  | .list π => some π
  | _ => none

/-- Extract a suggestion. -/
def Msg.getSuggest : Msg k N → Option (Fin k)
  | .suggest i => some i
  | _ => none

/-- Inner messages from `L`-parties. -/
def decodeIb (ib : Inbox (Party k) (Msg k N)) : Inbox (Party k) N :=
  fun p => if p.isLeft then (ib p).bind Msg.getInner else none

/-- The `L`-protocol history inside a `Φ` history (rounds `1, 2, …`). -/
def decodeH (h : History (Party k) (Msg k N)) : History (Party k) N := h.map decodeIb

/-- Inputs of the `L`-protocol instances, from the own list and the round-`0` inbox. -/
def inputL (π : Pref k) (ib0 : Inbox (Party k) (Msg k N)) : Party k → Pref k
  | inl _ => π
  | inr j => ((ib0 (inr j)).bind Msg.getList).getD 1

/-- The agreed vector of lists, if every instance output a non-`⊥` value. -/
noncomputable def lVector (p : Party k) (π : Pref k) (ib0 : Inbox (Party k) (Msg k (LMsg D)))
    (rest : History (Party k) (Msg k (LMsg D))) : Option (Party k → Pref k) :=
  ((lam D).firstDecide p (inputL π ib0) (decodeH rest)).bind allSome

/-- The suggestion of a strict majority of `L`, if any. -/
noncomputable def majority (ib : Inbox (Party k) (Msg k N)) : Option (Fin k) :=
  Finset.univ.majority? fun l : Fin k => (ib (inl l)).bind Msg.getSuggest

open Classical in
/-- `majority` in the paper's words: some suggestion `i` made by more than half of the `k`
parties of `L`, if one exists. -/
theorem majority_eq (ib : Inbox (Party k) (Msg k N)) :
    majority ib =
      if h : ∃ i, k < 2 * (Finset.univ.filter fun l : Fin k =>
          (ib (inl l)).bind Msg.getSuggest = some i).card
      then some h.choose else none := by
  split_ifs with h
  · rw [majority, Finset.majority?_eq_some_iff, Finset.card_univ, Fintype.card_fin]
    exact h.choose_spec
  · rw [majority, Finset.majority?_eq_none_iff]
    intro b
    rw [Finset.card_univ, Fintype.card_fin]
    push Not at h
    exact h b

/-- The protocol `Φ`. -/
noncomputable def phi : Protocol (Party k) (Pref k) (Msg k (LMsg D)) (Option (Fin k)) where
  send p π h q := match h with
    | [] => match p with
      | inr _ => some (.list π)
      | inl _ => none
    | ib0 :: rest =>
      if rest.length < D.T then
        (if p.isLeft && q.isLeft then
          ((lam D).send p (inputL π ib0) (decodeH rest) q).map .inner else none)
      else if rest.length = D.T then
        (match p, q with
          | inl _, inr j => (lVector D p π ib0 rest).map fun v => .suggest ((gsOfVector v).symm j)
          | _, _ => none)
      else none
  decide p π h := match p, h with
    | inl i, ib0 :: rest =>
      if rest.length = D.T then some ((lVector D (inl i) π ib0 rest).map fun v => gsOfVector v i)
      else none
    | inr _, h => if h.length = D.T + 2 then some (majority (h.getLastD fun _ => none)) else none
    | inl _, [] => none

/-! ## Analysis of `Φ` -/

lemma phi_send_inner {p q : Party k} {π : Pref k} {ib : Inbox (Party k) (Msg k (LMsg D))}
    {rest : History (Party k) (Msg k (LMsg D))} (h : rest.length < D.T) :
    (phi D).send p π (ib :: rest) q = if p.isLeft && q.isLeft then
      ((lam D).send p (inputL π ib) (decodeH rest) q).map .inner else none := by
  simp [phi, h]

lemma phi_send_suggest {i j : Fin k} {π : Pref k} {ib : Inbox (Party k) (Msg k (LMsg D))}
    {rest : History (Party k) (Msg k (LMsg D))} (h : rest.length = D.T) :
    (phi D).send (inl i) π (ib :: rest) (inr j) =
      (lVector D (inl i) π ib rest).map fun v => .suggest ((gsOfVector v).symm j) := by
  simp [phi, h]

lemma phi_decide_inl {i : Fin k} {π : Pref k} {ib : Inbox (Party k) (Msg k (LMsg D))}
    {rest : History (Party k) (Msg k (LMsg D))} :
    (phi D).decide (inl i) π (ib :: rest) = if rest.length = D.T then
      some ((lVector D (inl i) π ib rest).map fun v => gsOfVector v i) else none := rfl

lemma phi_decide_inr {j : Fin k} {π : Pref k} {h : History (Party k) (Msg k (LMsg D))} :
    (phi D).decide (inr j) π h = if h.length = D.T + 2 then
      some (majority (h.getLastD fun _ => none)) else none := rfl

section Analysis

variable (s : Scenario (Party k) (Pref k) (Msg k (LMsg D)))

/-- The round-`0` inbox of `p`. -/
noncomputable def ib0 (p : Party k) : Inbox (Party k) (Msg k (LMsg D)) :=
  (hist (oneSidedR k) (phi D) s 1 p).headD fun _ => none

/-- The scenario of the embedded `L`-protocol. -/
noncomputable def sL : Scenario (Party k) (Party k → Pref k) (LMsg D) where
  byz := s.byz
  input p := inputL (s.input p) (ib0 D s p)
  adv r p q := (s.adv (r + 1) p q).bind Msg.getInner
  drop r p q := s.drop (r + 1) p q

lemma hist_one (p : Party k) : hist (oneSidedR k) (phi D) s 1 p = [ib0 D s p] := by
  simp [hist_succ, ib0]

lemma hist_succ_cons (r : ℕ) (p : Party k) :
    hist (oneSidedR k) (phi D) s (r + 1) p =
      ib0 D s p :: (hist (oneSidedR k) (phi D) s (r + 1) p).drop 1 := by
  conv_lhs => rw [← List.take_append_drop 1 (hist (oneSidedR k) (phi D) s (r + 1) p)]
  rw [take_hist _ _ _ (by omega), hist_one]
  rfl

/-- **The embedded run**: up to round `T`, the `L`-protocol part of an honest `L`-party's history is
its history in the run `sL` of the `L`-protocol on the `L`-clique. -/
theorem decodeH_hist (r : ℕ) (hr : r ≤ D.T) (q : Party k) (hq : q ∉ s.byz) (hqL : q.isLeft) :
    decodeH ((hist (oneSidedR k) (phi D) s (r + 1) q).drop 1) =
      hist (lClique k) (lam D) (sL D s) r q := by
  induction r generalizing q with
  | zero => rw [hist_one]; rfl
  | succ r ih =>
    rw [hist_succ (r := r + 1), List.drop_append_of_le_length (by simp), decodeH, List.map_append,
      ← decodeH, ih (by omega) q hq hqL, hist_succ (r := r)]
    congr 1
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    funext p'
    rcases p' with l | j
    · simp only [decodeIb, Sum.isLeft_inl, ite_true, deliver]
      by_cases hadj : (inl l : Party k) = q
      · subst hadj
        simp
      · have h1 : (oneSidedR k).Adj (inl l) q := ⟨hadj, Or.inl rfl⟩
        have h2 : (lClique k).Adj (inl l) q := ⟨hadj, rfl, hqL⟩
        simp only [h1, h2, ite_true]
        by_cases hb : inl l ∈ s.byz
        · simp [hb, sL]
        · have hb' : inl l ∉ (sL D s).byz := hb
          simp only [hb, hb', ite_false]
          by_cases hd : s.drop (r + 1) (inl l) q
          · have hd' : (sL D s).drop r (inl l) q := hd
            simp [hd, hd']
          · have hd' : ¬ (sL D s).drop r (inl l) q := hd
            simp only [hd, hd', ite_false]
            rw [hist_succ_cons D s r (inl l), phi_send_inner D (by simp; omega)]
            simp only [Sum.isLeft_inl, hqL, Bool.and_self, ite_true]
            rw [ih (by omega) (inl l) hb rfl]
            rw [show ∀ x : Option (LMsg D), (x.map Msg.inner).bind Msg.getInner = x from
              fun x => by cases x <;> rfl]
            rfl
    · simp [decodeIb, deliver]

end Analysis

/-! ### The embedded `L`-protocol and its instances -/

section Instances

variable (s : Scenario (Party k) (Pref k) (Msg k (LMsg D)))

/-- The scenario seen by instance `i` of the `L`-protocol. -/
noncomputable def sI (i : Party k) : Scenario (Party k) (Pref k) (D.M i) :=
  ((sL D s).proj i).mapInput fun v => v i

@[simp] lemma sI_byz (i : Party k) : (sI D s i).byz = s.byz := rfl
@[simp] lemma sI_input (i p : Party k) : (sI D s i).input p = (sL D s).input p i := rfl

lemma sI_reliable (h : s.Reliable) (i : Party k) : (sI D s i).Reliable :=
  fun r p q => h (r + 1) p q

lemma lam_decides_iff (p : Party k) (d : Party k → Option (Pref k)) :
    Decides (lClique k) (lam D) (sL D s) p d ↔
      ∀ i, Decides (lClique k) (D.alg i) (sI D s i) p (d i) := by
  rw [lam, decides_parallel_iff]
  exact forall_congr' fun i => decides_comapInput _ _ _ _ _ _

lemma status_lam (r : ℕ) (p : Party k) :
    status (lClique k) (lam D) (sL D s) r p =
      allSome fun i => firstUpTo (fun j => status (lClique k) (D.alg i) (sI D s i) j p) r := by
  rw [lam, status_parallel]
  congr 1; funext i
  exact firstUpTo_congr fun j _ => status_comapInput _ _ _ _ _ _

variable {s}

/-- Honest parties have decided in the `L`-protocol by round `T`; `firstDecide` at round `T` gives
the (first) decision. -/
lemma lam_first (hZ : s.byz ∈ thresholds k tL k) (p : Party k) (hp : p ∉ s.byz) :
    ∃ d, Decides (lClique k) (lam D) (sL D s) p d ∧
      (lam D).firstDecide p ((sL D s).input p) (hist (lClique k) (lam D) (sL D s) D.T p) = some d := by
  have hT : ∀ i, ∃ o, firstUpTo (fun j => status (lClique k) (D.alg i) (sI D s i) j p) D.T = some o := by
    intro i
    obtain ⟨r, hr, o, ho⟩ := ((D.solves i) (sI D s i) hZ).2.2 p hp
    rcases h : firstUpTo (fun j => status (lClique k) (D.alg i) (sI D s i) j p) D.T with _ | o'
    · rw [firstUpTo_eq_none] at h; rw [h r hr] at ho; cases ho
    · exact ⟨o', rfl⟩
  choose o ho using hT
  have hst : status (lClique k) (lam D) (sL D s) D.T p = some o := by
    rw [status_lam]; exact allSome_eq_some.2 ho
  have hfirst : (lam D).firstDecide p ((sL D s).input p) (hist (lClique k) (lam D) (sL D s) D.T p) =
      firstUpTo (fun j => status (lClique k) (lam D) (sL D s) j p) D.T := by
    rw [Protocol.firstDecide, length_hist]
    exact firstUpTo_congr fun j hj => by rw [take_hist _ _ _ hj]; rfl
  rcases h : firstUpTo (fun j => status (lClique k) (lam D) (sL D s) j p) D.T with _ | d
  · rw [firstUpTo_eq_none] at h; rw [h D.T le_rfl] at hst; cases hst
  · exact ⟨d, FirstSome.of_firstUpTo h, hfirst.trans h⟩

end Instances

/-! ### Decisions in `Φ` -/

section Decisions

variable {s : Scenario (Party k) (Pref k) (Msg k (LMsg D))}

lemma lVector_honest (hZ : s.byz ∈ thresholds k tL k) (p : Party k) (hp : p ∉ s.byz)
    (hpL : p.isLeft) {d : Party k → Option (Pref k)}
    (hd : Decides (lClique k) (lam D) (sL D s) p d) :
    lVector D p (s.input p) (ib0 D s p) ((hist (oneSidedR k) (phi D) s (D.T + 1) p).drop 1) =
      allSome d := by
  obtain ⟨d', hd', hfirst⟩ := lam_first D hZ p hp
  obtain rfl := Decides.unique _ _ hd hd'
  rw [lVector, decodeH_hist D s D.T le_rfl p hp hpL]
  change ((lam D).firstDecide p ((sL D s).input p) _).bind allSome = _
  rw [hfirst]; rfl

/-- Decision of an honest `L`-party in `Φ`. -/
lemma phi_decides_inl (hZ : s.byz ∈ thresholds k tL k) (i : Fin k) (hi : inl i ∉ s.byz) :
    ∃ d, Decides (lClique k) (lam D) (sL D s) (inl i) d ∧ ∀ o,
      Decides (oneSidedR k) (phi D) s (inl i) o ↔ o = (allSome d).map fun v => gsOfVector v i := by
  obtain ⟨d, hd, -⟩ := lam_first D hZ (inl i) hi
  refine ⟨d, hd, fun o => ?_⟩
  rw [decides_iff_firstSome, firstSome_iff_of_ne (D.T + 1)]
  · rw [status, hist_succ_cons, phi_decide_inl, ite_eq_left (by simp), lVector_honest D hZ _ hi rfl hd]
    exact ⟨fun h => (Option.some.inj h).symm, fun h => by rw [h]⟩
  · intro r hr
    cases r with
    | zero => rfl
    | succ r =>
      rw [status, hist_succ_cons, phi_decide_inl, ite_eq_right (by simp; omega)]

/-- The last inbox of an `R`-party, at round `T + 1`. -/
lemma phi_decides_inr (j : Fin k) (o : Option (Fin k)) :
    Decides (oneSidedR k) (phi D) s (inr j) o ↔
      o = majority (fun p => deliver (oneSidedR k) (phi D) s (hist (oneSidedR k) (phi D) s (D.T + 1))
        (D.T + 1) p (inr j)) := by
  rw [decides_iff_firstSome, firstSome_iff_of_ne (D.T + 2)]
  · rw [status, phi_decide_inr, ite_eq_left (by simp), hist_succ]
    simp only [List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_singleton,
      Option.some_or, Option.getD_some, Option.some.injEq]
    exact eq_comm
  · intro r hr
    rw [status, phi_decide_inr, ite_eq_right (by simpa using hr)]

end Decisions

/-! ### Correctness of `Φ` (Lemmas 11 and 12) -/

section Correctness

variable {s : Scenario (Party k) (Pref k) (Msg k (LMsg D))}

lemma bSM_congr {x : Party k → Pref k} {H : Set (Party k)} {dec dec' : Party k → Option (Fin k) → Prop}
    (hd : ∀ p ∈ H, ∀ o, dec p o ↔ dec' p o) (h : bSM k x H dec) : bSM k x H dec' := by
  obtain ⟨⟨hT, hS, hN⟩, hSt⟩ := h
  refine ⟨⟨fun p hp => ?_, fun i j hi hj => ?_, fun p q hp hq hpq z z' h1 h2 => ?_⟩,
    fun i j oi oj hi hj h1 h2 => ?_⟩
  · obtain ⟨o, ho⟩ := hT p hp; exact ⟨o, (hd p hp o).1 ho⟩
  · rw [← hd _ hi, ← hd _ hj]; exact hS i j hi hj
  · exact hN p q hp hq hpq z z' ((hd p hp _).2 h1) ((hd q hq _).2 h2)
  · exact hSt i j oi oj hi hj ((hd _ hi _).2 h1) ((hd _ hj _).2 h2)

lemma instSpec_agree {i : Party k} {x : Party k → Pref k} {H : Set (Party k)}
    {dec : Party k → Pref k → Prop} (h : instSpec i x H dec) :
    ∀ p ∈ H, ∀ q ∈ H, ∀ v w, dec p v → dec q w → v = w := by
  cases i with
  | inl _ => exact h.2.2
  | inr _ => exact h.2.2

lemma ib0_inl_inr (hD1 : ∀ r p q, s.drop r p q → p.isLeft ∧ q.isLeft) (i j : Fin k)
    (hj : inr j ∉ s.byz) : ib0 D s (inl i) (inr j) = some (.list (s.input (inr j))) := by
  have hnd : ¬ s.drop 0 (inr j) (inl i) := fun h => by simpa using (hD1 _ _ _ h).1
  simp [ib0, hist_succ, deliver, hj, hnd, phi]

open Classical in
lemma card_honestL (hZ : s.byz ∈ thresholds k tL k) :
    k - tL ≤ (Finset.univ.filter fun l : Fin k => inl l ∉ s.byz).card := by
  have h1 := hZ.1
  rw [Set.ncard_eq_toFinset_card'] at h1
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (fun l => inl l ∈ s.byz)
  have h3 : (Set.toFinset (inl ⁻¹' s.byz : Set (Fin k))) =
      Finset.univ.filter fun l : Fin k => inl l ∈ s.byz := by ext; simp
  rw [h3] at h1
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  omega

open Classical in
/-- **Lemmas 11 and 12** (for `Φ`): if `tL < k/3`, omissions only affect `L–L` messages, and there are
no omissions as soon as some `R`-party is honest, then `Φ` achieves bSM. -/
theorem phi_bSM (h3 : 3 * tL < k) (hZ : s.byz ∈ thresholds k tL k)
    (hD1 : ∀ r p q, s.drop r p q → p.isLeft ∧ q.isLeft)
    (hD2 : (∃ j, inr j ∉ s.byz) → s.Reliable) :
    bSM k s.input s.honest (Decides (oneSidedR k) (phi D) s) := by
  -- decisions of honest `L`-parties
  have hdL : ∀ i, inl i ∉ s.byz → ∃ d, Decides (lClique k) (lam D) (sL D s) (inl i) d ∧ ∀ o,
      Decides (oneSidedR k) (phi D) s (inl i) o ↔ o = (allSome d).map fun v => gsOfVector v i :=
    fun i hi => phi_decides_inl D hZ i hi
  have hHL : ∀ p, p ∈ s.honest → p.isLeft → p ∈ {p | p ∈ (sI D s p).honest ∧ p.isLeft} :=
    fun p hp hpL => ⟨hp, hpL⟩
  by_cases hR : ∃ j, inr j ∉ s.byz
  · -- Lemma 12: some `R`-party is honest, no omissions
    have hrel := hD2 hR
    have hspec := fun i => ((D.solves i) (sI D s i) hZ).1 (sI_reliable D s hrel i)
    -- an honest `L`-party exists
    obtain ⟨i0, hi0⟩ : ∃ i0, inl i0 ∉ s.byz := by
      have := card_honestL D hZ
      obtain ⟨i0, hi0⟩ :=
        (Finset.card_pos (s := Finset.univ.filter fun l : Fin k => inl l ∉ s.byz)).1 (by omega)
      exact ⟨i0, (Finset.mem_filter.1 hi0).2⟩
    obtain ⟨d0, hd0, -⟩ := hdL i0 hi0
    have hd0i := (lam_decides_iff D s _ _).1 hd0
    have hsome : ∀ i, ∃ w, d0 i = some w := by
      intro i
      rcases h : d0 i with _ | w
      · exact absurd (h ▸ hd0i i) ((hspec i).1 _ ⟨hi0, rfl⟩)
      · exact ⟨w, rfl⟩
    choose v hv using hsome
    -- every honest `L`-party has the vector `v`
    have hall : ∀ i, inl i ∉ s.byz → ∀ d, Decides (lClique k) (lam D) (sL D s) (inl i) d →
        d = fun j => some (v j) := by
      intro i hi d hd
      have hdi := (lam_decides_iff D s _ _).1 hd
      funext j
      rcases h : d j with _ | w
      · exact absurd (h ▸ hdi j) ((hspec j).1 _ ⟨hi, rfl⟩)
      · have := instSpec_agree (hspec j).2 _ ⟨hi, rfl⟩ _ ⟨hi0, rfl⟩ w (v j) (h ▸ hdi j)
          (hv j ▸ hd0i j)
        rw [this]
    -- validity
    have hval : ∀ q ∈ s.honest, v q = s.input q := by
      intro q hq
      rcases q with i' | j
      · have hBB := (hspec (inl i')).2.2.1 ⟨hq, rfl⟩ _ ⟨hi0, rfl⟩
        exact (instSpec_agree (hspec (inl i')).2 _ ⟨hi0, rfl⟩ _ ⟨hi0, rfl⟩ _ _
          (hv (inl i') ▸ hd0i (inl i')) hBB)
      · have hBA := (hspec (inr j)).2.2.1 (s.input (inr j)) (by
          rintro p ⟨hp, hpL⟩
          rcases p with l | l
          · simp only [sI_input, sL, inputL]
            rw [ib0_inl_inr D hD1 l j hq]; rfl
          · cases hpL) _ ⟨hi0, rfl⟩
        exact instSpec_agree (hspec (inr j)).2 _ ⟨hi0, rfl⟩ _ ⟨hi0, rfl⟩ _ _
          (hv (inr j) ▸ hd0i (inr j)) hBA
    have hav : allSome (fun j => some (v j)) = some v := allSome_eq_some.2 fun _ => rfl
    -- decisions are the offline ones on `v`
    have hdec : ∀ p ∈ s.honest, ∀ o, (∃ d, d = v ∧ offline p d = o) ↔
        Decides (oneSidedR k) (phi D) s p o := by
      intro p hp o
      simp only [exists_eq_left]
      rcases p with i | j
      · obtain ⟨d, hd, hiff⟩ := hdL i hp
        rw [hiff, hall i hp d hd, hav]
        simp [eq_comm]
      · rw [phi_decides_inr, offline_inr, majority,
          Finset.majority?_eq_of_notMem (F := Finset.univ.filter fun l : Fin k => inl l ∈ s.byz)
            (o := some ((gsOfVector v).symm j))]
        · exact eq_comm
        · rw [← Finset.filter_not, Finset.card_univ, Fintype.card_fin]
          have := card_honestL D hZ
          omega
        · intro l _ hl
          have hl : inl l ∉ s.byz := by simpa using hl
          obtain ⟨d, hd, -⟩ := hdL l hl
          rw [deliver_honest _ _ _ hrel hl (by simp), hist_succ_cons, phi_send_suggest D (by simp),
            lVector_honest D hZ _ hl rfl hd, hall l hl d hd, hav]
          rfl
    refine bSM_congr hdec (offlineMatch s.input s.honest (fun _ d => d = v) ⟨?_, ?_, ?_⟩)
    · exact fun p _ => ⟨v, rfl⟩
    · rintro p _ d rfl q hq; exact hval q hq
    · rintro p _ q _ d e rfl rfl; rfl
  · -- Lemma 11: all of `R` is Byzantine
    push Not at hR
    have hwa := fun i => ((D.solves i) (sI D s i) hZ).2.1
    have hnoR : ∀ j, inr j ∉ s.honest := fun j h => h (hR j)
    refine ⟨⟨fun p hp => ?_, fun i j _ hj => absurd hj (hnoR j), ?_⟩,
      fun i j _ _ _ hj => absurd hj (hnoR j)⟩
    · rcases p with i | j
      · obtain ⟨d, -, hiff⟩ := hdL i hp
        exact ⟨_, (hiff _).2 rfl⟩
      · exact absurd hp (hnoR j)
    · intro p q hp hq hpq z z' hz hz' hpart
      rcases p with i | j
      swap; · exact hnoR j hp
      rcases q with i' | j'
      swap; · exact hnoR j' hq
      obtain ⟨d, hd, hiff⟩ := hdL i hp
      obtain ⟨d', hd', hiff'⟩ := hdL i' hq
      rw [hiff] at hz; rw [hiff'] at hz'
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hz.symm
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.1 hz'.symm
      have hdi := (lam_decides_iff D s _ _).1 hd
      have hdi' := (lam_decides_iff D s _ _).1 hd'
      have hww : w = w' := by
        funext j
        exact (hwa j) _ ⟨hp, rfl⟩ _ ⟨hq, rfl⟩ _ _ (allSome_eq_some.1 hw j ▸ hdi j)
          (allSome_eq_some.1 hw' j ▸ hdi' j)
      subst hww
      simp only [partner, inr.injEq, EmbeddingLike.apply_eq_iff_eq] at hpart
      exact hpq (by rw [hpart])

end Correctness

end PiBSM

end Papers.PODC2025.ByzantineStableMatching
