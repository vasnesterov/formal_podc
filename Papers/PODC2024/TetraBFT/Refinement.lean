import Papers.PODC2024.TetraBFT.Protocol
import Papers.PODC2024.TetraBFT.Safety
import Podc.Computability.Distributed.Byzantine.PartialSync.Log

/-!
# The protocol refines the abstract execution model

Every run of `tetra prm` (any delivery schedule, any Byzantine behaviour, no timing assumption)
yields an abstract `Execution` satisfying `Execution.SafetyHyp`: one vote per phase and view,
quorums behind vote-2/3/4 and decisions, Rule 3 on honest proof reports behind vote-1. Hence
Theorem 1 (agreement) holds for the message-level protocol in all runs (`tetra_agreement`).

Structure: a local invariant `Inv` of every correct node's state (preserved by `step`, stage by
stage), the authenticity of received messages from correct senders (`rcv_authentic`), and the
fact that a correct node never casts a vote in a view below its current one, so the report sent
when entering view `r` is final for the views `< r` (`voted_below_iff`).
-/

set_option linter.unusedSectionVars false

namespace TetraBFT

open Finset Cslib.Byzantine.PartialSync

variable {n : ℕ} {V : Type} [DecidableEq V]

/-! ### `best`, `phaseVotes`, `mkReport` -/

theorem best_mem : ∀ {l : List (ℕ × V)} {e : ℕ × V}, best l = some e → e ∈ l
  | [], e, h => by simp [best] at h
  | a :: l, e, h => by
    simp only [best] at h
    rcases hb : best l with _ | e'
    · rw [hb] at h; simp only [Option.some.injEq] at h; subst h; simp
    · rw [hb] at h
      simp only at h
      split_ifs at h with hle
      · simp only [Option.some.injEq] at h; subst h; simp
      · simp only [Option.some.injEq] at h; subst h; exact List.mem_cons_of_mem _ (best_mem hb)

theorem best_max : ∀ {l : List (ℕ × V)} {e : ℕ × V}, e ∈ l → ∃ e', best l = some e' ∧ e.1 ≤ e'.1
  | [], e, h => by simp at h
  | a :: l, e, h => by
    simp only [best]
    rcases hb : best l with _ | e'
    · simp only [Option.some.injEq, exists_eq_left']
      rcases List.mem_cons.1 h with rfl | h
      · exact le_rfl
      · obtain ⟨e'', he'', -⟩ := best_max h; rw [hb] at he''; simp at he''
    · simp only
      split_ifs with hle
      · refine ⟨a, rfl, ?_⟩
        rcases List.mem_cons.1 h with rfl | h
        · exact le_rfl
        · obtain ⟨e'', he'', hle'⟩ := best_max h; rw [hb] at he''
          simp only [Option.some.injEq] at he''; subst he''; omega
      · refine ⟨e', rfl, ?_⟩
        rcases List.mem_cons.1 h with rfl | h
        · omega
        · obtain ⟨e'', he'', hle'⟩ := best_max h; rw [hb] at he''
          simp only [Option.some.injEq] at he''; subst he''; exact hle'

theorem mem_phaseVotes {votes : List (Vote V)} {a r u : ℕ} {y : V} :
    (u, y) ∈ phaseVotes votes a r ↔ u < r ∧ (⟨a, u, y⟩ : Vote V) ∈ votes := by
  simp only [phaseVotes, List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a', u', y'⟩, ⟨hm, rfl, hu⟩, rfl, rfl⟩
    exact ⟨hu, hm⟩
  · rintro ⟨hu, hm⟩
    exact ⟨⟨a, u, y⟩, ⟨hm, rfl, hu⟩, rfl, rfl⟩

/-- The computed report is honest. -/
theorem mkReport_isReport (votes : List (Vote V)) (r a b : ℕ) :
    IsReport (fun w => w ∈ votes) r a b (mkReport votes r a b) where
  hi_sound u y h := mem_phaseVotes.1 (best_mem h)
  hi_max u y hu hv := by
    obtain ⟨⟨u', y'⟩, h, hle⟩ := best_max (mem_phaseVotes.2 ⟨hu, hv⟩)
    exact ⟨u', y', h, hle⟩
  prev_sound u y h := by
    simp only [mkReport] at h
    rcases hb : best (phaseVotes votes a r) with _ | ⟨u', y'⟩
    · rw [hb] at h; simp at h
    · rw [hb] at h
      have hm := best_mem h
      rw [List.mem_filter] at hm
      obtain ⟨hu, hv⟩ := mem_phaseVotes.1 hm.1
      obtain ⟨e', he', hle⟩ := best_max hm.1
      rw [hb] at he'
      simp only [Option.some.injEq] at he'
      subst he'
      exact ⟨hu, hv, u', y', by simpa [mkReport] using hb, by simpa using hm.2, hle⟩
  prev_max u y u' y' hu hv hhi hne := by
    simp only [mkReport] at hhi ⊢
    rw [hhi]
    have hm : (u, y) ∈ (phaseVotes votes a r).filter fun e => decide (e.2 ≠ y') := by
      rw [List.mem_filter]; exact ⟨mem_phaseVotes.2 ⟨hu, hv⟩, by simpa using hne⟩
    obtain ⟨⟨u'', y''⟩, h, hle⟩ := best_max hm
    exact ⟨u'', y'', h, hle⟩
  top_sound u y h := mem_phaseVotes.1 (best_mem h)
  top_max u y hu hv := by
    obtain ⟨⟨u', y'⟩, h, hle⟩ := best_max (mem_phaseVotes.2 ⟨hu, hv⟩)
    exact ⟨u', y', h, hle⟩

/-- Honesty of a report only depends on the votes of views `< r`. -/
theorem IsReport.congr {voted voted' : Vote V → Prop} {r a b : ℕ} {rep : Report V}
    (h : ∀ w : Vote V, w.view < r → (voted w ↔ voted' w)) (hr : IsReport voted r a b rep) :
    IsReport voted' r a b rep where
  hi_sound u y hh := by
    obtain ⟨hu, hv⟩ := hr.hi_sound u y hh
    exact ⟨hu, (h _ hu).1 hv⟩
  hi_max u y hu hv := hr.hi_max u y hu ((h _ hu).2 hv)
  prev_sound u y hh := by
    obtain ⟨hu, hv, rest⟩ := hr.prev_sound u y hh
    exact ⟨hu, (h _ hu).1 hv, rest⟩
  prev_max u y u' y' hu hv := hr.prev_max u y u' y' hu ((h _ hu).2 hv)
  top_sound u y hh := by
    obtain ⟨hu, hv⟩ := hr.top_sound u y hh
    exact ⟨hu, (h _ hu).1 hv⟩
  top_max u y hu hv := hr.top_max u y hu ((h _ hu).2 hv)

theorem phaseVotes_append {votes l : List (Vote V)} {a r : ℕ} (hl : ∀ w ∈ l, r ≤ w.view) :
    phaseVotes (votes ++ l) a r = phaseVotes votes a r := by
  have h : l.filter (fun w => decide (w.phase = a) && decide (w.view < r)) = [] :=
    List.filter_eq_nil_iff.2 (fun w hw => by have := hl w hw; simp; omega)
  simp only [phaseVotes, List.filter_append, h, List.append_nil]

theorem mkReport_append {votes l : List (Vote V)} {r a b : ℕ} (hl : ∀ w ∈ l, r ≤ w.view) :
    mkReport (votes ++ l) r a b = mkReport votes r a b := by
  simp only [mkReport, phaseVotes_append hl]

/-! ### Monotonicity of the rule checks in the received messages -/

section Mono

variable {P : Type*} [DecidableEq P]

theorem Blocking.mono {f : ℕ} {S S' : Finset P} {rep rep' : P → Report V} {x : V} {w : ℕ}
    (hS : S ⊆ S') (hrep : ∀ q ∈ S, rep q = rep' q) (h : Blocking f S rep x w) :
    Blocking f S' rep' x w := by
  obtain ⟨B, hBS, hB, hc⟩ := h
  exact ⟨B, hBS.trans hS, hB, fun q hq => hrep q (hBS hq) ▸ hc q hq⟩

theorem ShowsSafe.mono {m f : ℕ} {bB : Bool} {S S' : Finset P} {rep rep' : P → Report V}
    {x : V} {v : ℕ} (hS : S ⊆ S') (hrep : ∀ q ∈ S, rep q = rep' q)
    (h : ShowsSafe m f bB S rep x v) : ShowsSafe m f bB S' rep' x v := by
  rcases h with h0 | ⟨Q, hQS, hQ, hcase⟩
  · exact Or.inl h0
  refine Or.inr ⟨Q, hQS.trans hS, hQ, ?_⟩
  rcases hcase with hnone | ⟨w, hwv, hok, hiii⟩
  · exact Or.inl fun q hq => hrep q (hQS hq) ▸ hnone q hq
  refine Or.inr ⟨w, hwv, fun q hq => hrep q (hQS hq) ▸ hok q hq, ?_⟩
  rcases hiii with hA | ⟨hb, x₁, x₂, w₁, w₂, h₁, h₂, h₃, h₄, hB₁, hB₂⟩
  · exact Or.inl (hA.mono hS hrep)
  · exact Or.inr ⟨hb, x₁, x₂, w₁, w₂, h₁, h₂, h₃, h₄, hB₁.mono hS hrep, hB₂.mono hS hrep⟩

end Mono

theorem firstFrom_append {α : Type} {rcv l : List (Fin n × Msg V)} {q : Fin n}
    {g : Msg V → Option α} {a : α} (h : firstFrom rcv q g = some a) :
    firstFrom (rcv ++ l) q g = some a := by
  simp only [firstFrom, List.findSome?_append] at h ⊢
  rw [h]; rfl

theorem repSenders_append {rcv l : List (Fin n × Msg V)} {g : Msg V → Option (Report V)} :
    repSenders rcv g ⊆ repSenders (rcv ++ l) g := by
  intro q hq
  simp only [repSenders, mem_filter, mem_univ, true_and, Option.isSome_iff_exists] at hq ⊢
  obtain ⟨a, ha⟩ := hq
  exact ⟨a, firstFrom_append ha⟩

theorem repOf_append {rcv l : List (Fin n × Msg V)} {g : Msg V → Option (Report V)} {q : Fin n}
    (hq : q ∈ repSenders rcv g) : repOf (rcv ++ l) g q = repOf rcv g q := by
  simp only [repSenders, mem_filter, mem_univ, true_and, Option.isSome_iff_exists] at hq
  obtain ⟨a, ha⟩ := hq
  simp [repOf, ha, firstFrom_append ha]

theorem senders_append {rcv l : List (Fin n × Msg V)} {m : Msg V} :
    senders rcv m ⊆ senders (rcv ++ l) m := by
  intro q hq
  simp only [senders, mem_filter, mem_univ, true_and] at hq ⊢
  exact List.mem_append_left _ hq

/-- The first proof message from `q` in the received messages was received from `q`. -/
theorem mem_of_repSenders {rcv : List (Fin n × Msg V)} {v : ℕ} {q : Fin n}
    (hq : q ∈ repSenders rcv (getProof v)) : (q, Msg.proof v (repOf rcv (getProof v) q)) ∈ rcv := by
  simp only [repSenders, mem_filter, mem_univ, true_and, Option.isSome_iff_exists] at hq
  obtain ⟨a, ha⟩ := hq
  have hrep : repOf rcv (getProof v) q = a := by simp [repOf, ha]
  rw [hrep]
  obtain ⟨⟨q', m⟩, hm, he⟩ := List.exists_of_findSome?_eq_some ha
  simp only at he
  split_ifs at he with hq'
  subst hq'
  cases m with
  | proof v' rep =>
    simp only [getProof] at he
    split_ifs at he with hv
    · subst hv; simp only [Option.some.injEq] at he; subst he; exact hm
  | _ => simp [getProof] at he

theorem mem_of_firstFrom_proposal {rcv : List (Fin n × Msg V)} {q : Fin n} {v : ℕ} {x : V}
    (h : firstFrom rcv q (getProposal v) = some x) : (q, Msg.proposal v x) ∈ rcv := by
  obtain ⟨⟨q', m⟩, hm, he⟩ := List.exists_of_findSome?_eq_some h
  simp only at he
  split_ifs at he with hq'
  subst hq'
  cases m with
  | proposal v' x' =>
    simp only [getProposal] at he
    split_ifs at he with hv
    · subst hv; simp only [Option.some.injEq] at he; subst he; exact hm
  | _ => simp [getProposal] at he

/-! ### The local invariant -/

variable (prm : Params n)

/-- Justification of a cast vote by the received messages. -/
def Just (rcv : List (Fin n × Msg V)) (w : Vote V) : Prop :=
  1 ≤ w.phase ∧ w.phase ≤ 4 ∧
  (w.phase = 1 → w.view = 0 ∨
    Rule3 n prm.f (repSenders rcv (getProof w.view)) (repOf rcv (getProof w.view)) w.val w.view) ∧
  (2 ≤ w.phase → n - prm.f ≤ (senders rcv (.vote (w.phase - 1) w.view w.val)).card) ∧
  (w.phase = 1 → (prm.leader w.view, Msg.proposal w.view w.val) ∈ rcv)

/-- What the messages in the outbox say about the sender's state. -/
def OutOK (s : St n V) : Msg V → Prop
  | .vote k v x => ⟨k, v, x⟩ ∈ s.votes
  | .proposal v x =>
      (v = 0 ∨ Rule1 n prm.f (repSenders s.rcv (getSuggest v)) (repOf s.rcv (getSuggest v)) x v) ∧
      (x = s.inp ∨
        ¬ Rule1 n prm.f (repSenders s.rcv (getSuggest v)) (repOf s.rcv (getSuggest v)) s.inp v)
  | .proof v rep => v ≤ s.view ∧ rep = mkReport s.votes v 1 4
  | .suggest v rep => v ≤ s.view ∧ rep = mkReport s.votes v 2 3
  | _ => True

/-- The local invariant of a correct node. -/
structure Inv (s : St n V) : Prop where
  view_ge : ∀ w ∈ s.votes, w.view ≤ s.view
  one : ∀ w ∈ s.votes, ∀ w' ∈ s.votes, w.phase = w'.phase → w.view = w'.view → w.val = w'.val
  just : ∀ w ∈ s.votes, Just prm s.rcv w
  out : ∀ m ∈ s.out, OutOK prm s m
  dec : ∀ x v, s.dec = some (x, v) → n - prm.f ≤ (senders s.rcv (.vote 4 v x)).card

/-! ### Specifications of the helper functions -/

theorem maxVC_spec {rcv : List (Fin n × Msg V)} {th lo w : ℕ} (h : maxVC rcv th lo = some w) :
    lo < w ∧ th ≤ (senders rcv (.viewChange w)).card := by
  have hm := List.max?_mem h
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hm
  exact hm.2

theorem quorumVal_spec {f : ℕ} {rcv : List (Fin n × Msg V)} {k v : ℕ} {x : V}
    (h : quorumVal f rcv k v = some x) : n - f ≤ (senders rcv (.vote k v x)).card := by
  have := List.find?_some h
  simpa using this

theorem not_hasVoted {votes : List (Vote V)} {k v : ℕ} (h : hasVoted votes k v = false) :
    ∀ w ∈ votes, w.phase = k → w.view ≠ v := by
  intro w hw hk hv
  have : hasVoted votes k v = true := List.any_eq_true.2 ⟨w, hw, by simp [hk, hv]⟩
  rw [h] at this
  exact absurd this (by simp)

/-! ### Preservation of the invariant -/

theorem Just.append {rcv l : List (Fin n × Msg V)} {w : Vote V} (h : Just prm rcv w) :
    Just prm (rcv ++ l) w := by
  obtain ⟨h1, h4, hr, hq, hpr⟩ := h
  refine ⟨h1, h4, fun hp => ?_, fun hp => le_trans (hq hp) (card_le_card senders_append),
    fun hp => List.mem_append_left _ (hpr hp)⟩
  rcases hr hp with h0 | hr
  · exact Or.inl h0
  · exact Or.inr (hr.mono repSenders_append fun q hq => (repOf_append hq).symm)

theorem OutOK.mono {s s' : St n V} {m : Msg V}
    (hv : ∃ l, s'.votes = s.votes ++ l ∧ ∀ w ∈ l, s.view ≤ w.view) (hview : s.view ≤ s'.view)
    (hrcv : s'.rcv = s.rcv) (hinp : s'.inp = s.inp) (h : OutOK prm s m) : OutOK prm s' m := by
  obtain ⟨l, hl, hlv⟩ := hv
  cases m with
  | vote k v x => simp only [OutOK, hl] at h ⊢; exact List.mem_append_left _ h
  | proof v rep =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨le_trans h1 hview, ?_⟩
    rw [hl, mkReport_append (fun w hw => le_trans h1 (hlv w hw)), h2]
  | suggest v rep =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨le_trans h1 hview, ?_⟩
    rw [hl, mkReport_append (fun w hw => le_trans h1 (hlv w hw)), h2]
  | proposal v x => simpa only [OutOK, hrcv, hinp] using h
  | viewChange => trivial

/-- Invariant preservation for a stage that does not touch the votes, received messages and
decision, may increase the view, and only adds harmless messages to the outbox. -/
theorem Inv.of_eq {s s' : St n V} (h : Inv prm s) (hvotes : s'.votes = s.votes)
    (hrcv : s'.rcv = s.rcv) (hdec : s'.dec = s.dec) (hinp : s'.inp = s.inp)
    (hview : s.view ≤ s'.view)
    (hout : ∀ m ∈ s'.out, m ∈ s.out ∨ OutOK prm s' m) : Inv prm s' where
  view_ge w hw := le_trans (h.view_ge w (hvotes ▸ hw)) hview
  one w hw w' hw' := h.one w (hvotes ▸ hw) w' (hvotes ▸ hw')
  just w hw := hrcv ▸ h.just w (hvotes ▸ hw)
  out m hm := (hout m hm).elim
    (fun hm => (h.out m hm).mono prm ⟨[], by simp [hvotes], by simp⟩ hview hrcv hinp) id
  dec x v hd := hrcv ▸ h.dec x v (hdec ▸ hd)

theorem Inv.recvSt {s : St n V} (h : Inv prm s) (ib : Fin n → List (Msg V)) :
    Inv prm (recvSt s ib) where
  view_ge := h.view_ge
  one := h.one
  just w hw := (h.just w hw).append prm
  out m hm := by simp [TetraBFT.recvSt] at hm
  dec x v hd := le_trans (h.dec x v hd) (card_le_card senders_append)

theorem Inv.echoSt {s : St n V} (h : Inv prm s) : Inv prm (echoSt prm s) := by
  unfold TetraBFT.echoSt
  split
  · exact h.of_eq prm rfl rfl rfl rfl le_rfl fun m hm => by
      simp only [List.mem_append, List.mem_map] at hm
      rcases hm with hm | ⟨w, -, rfl⟩
      · exact Or.inl hm
      · exact Or.inr trivial
  · split
    · exact h.of_eq prm rfl rfl rfl rfl le_rfl fun m hm => by
        simp only [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · exact Or.inl hm
        · exact Or.inr trivial
    · exact h

theorem Inv.viewSt {s : St n V} (h : Inv prm s) : Inv prm (viewSt prm s) := by
  unfold TetraBFT.viewSt
  split
  · rename_i w hw
    have hlt := (maxVC_spec hw).1
    refine h.of_eq prm rfl rfl rfl rfl (by simp; omega) fun m hm => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | rfl | rfl
    · exact Or.inl hm
    · exact Or.inr ⟨le_rfl, rfl⟩
    · exact Or.inr ⟨le_rfl, rfl⟩
  · split
    · exact h.of_eq prm rfl rfl rfl rfl le_rfl fun m hm => by
        simp only [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · exact Or.inl hm
        · exact Or.inr trivial
    · exact h.of_eq prm rfl rfl rfl rfl le_rfl fun m hm => Or.inl hm

theorem proposeVal_spec {s : St n V} {x : V} (h : proposeVal prm s = some x) :
    (s.view = 0 ∨ leaderSafe prm s x) ∧ (x = s.inp ∨ ¬ leaderSafe prm s s.inp) := by
  unfold proposeVal at h
  split_ifs at h with h0 h1
  · exact ⟨Or.inl h0, Or.inl (Option.some.inj h).symm⟩
  · obtain rfl := Option.some.inj h
    exact ⟨Or.inr h1, Or.inl rfl⟩
  · rename_i hex
    refine ⟨Or.inr ?_, Or.inr h1⟩
    rw [← Option.some.inj h]
    exact Classical.choose_spec hex

theorem Inv.proposeSt {s : St n V} (h : Inv prm s) (p : Fin n) : Inv prm (proposeSt prm p s) := by
  unfold TetraBFT.proposeSt
  split
  · split
    · exact h
    · split
      · rename_i x hx
        exact h.of_eq prm rfl rfl rfl rfl le_rfl fun m hm => by
          simp only [List.mem_append, List.mem_singleton] at hm
          rcases hm with hm | rfl
          · exact Or.inl hm
          · exact Or.inr (proposeVal_spec prm hx)
      · exact h
  · exact h

theorem Inv.castVote {s : St n V} (h : Inv prm s) {k : ℕ} {x : V}
    (hnot : hasVoted s.votes k s.view = false) (hj : Just prm s.rcv ⟨k, s.view, x⟩) :
    Inv prm (castVote s k x) where
  view_ge w hw := by
    simp only [TetraBFT.castVote, List.mem_append, List.mem_singleton] at hw ⊢
    rcases hw with hw | rfl
    · exact h.view_ge w hw
    · exact le_rfl
  one w hw w' hw' hph hv := by
    simp only [TetraBFT.castVote, List.mem_append, List.mem_singleton] at hw hw'
    rcases hw with hw | rfl <;> rcases hw' with hw' | rfl
    · exact h.one w hw w' hw' hph hv
    · exact absurd hv (not_hasVoted hnot w hw hph)
    · exact absurd hv.symm (not_hasVoted hnot w' hw' hph.symm)
    · rfl
  just w hw := by
    simp only [TetraBFT.castVote, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact h.just w hw
    · exact hj
  out m hm := by
    simp only [TetraBFT.castVote, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact (h.out m hm).mono prm ⟨[⟨k, s.view, x⟩], rfl, by simp⟩ le_rfl rfl rfl
    · simp [OutOK, TetraBFT.castVote]
  dec := h.dec

theorem Inv.vote1St {s : St n V} (h : Inv prm s) : Inv prm (vote1St prm s) := by
  unfold TetraBFT.vote1St
  split
  · exact h
  · rename_i hnot
    split
    · exact h
    · rename_i x hx
      have hmem := mem_of_firstFrom_proposal hx
      split
      · rename_i h0
        exact h.castVote prm (by simpa using hnot) ⟨le_rfl, by simp, fun _ => Or.inl h0,
          fun h => absurd h (by simp), fun _ => hmem⟩
      · split
        · rename_i hs
          exact h.castVote prm (by simpa using hnot) ⟨le_rfl, by simp, fun _ => Or.inr hs,
            fun h => absurd h (by simp), fun _ => hmem⟩
        · exact h

theorem Inv.voteKSt {s : St n V} (h : Inv prm s) {k : ℕ} (hk2 : 2 ≤ k) (hk4 : k ≤ 4) :
    Inv prm (voteKSt prm k s) := by
  unfold TetraBFT.voteKSt
  split
  · exact h
  · rename_i hnot
    split
    · exact h
    · rename_i x hx
      exact h.castVote prm (by simpa using hnot) ⟨show 1 ≤ k by omega, hk4,
        fun h => absurd (show k = 1 from h) (by omega), fun _ => quorumVal_spec hx,
        fun h => absurd (show k = 1 from h) (by omega)⟩

theorem Inv.decideSt {s : St n V} (h : Inv prm s) : Inv prm (decideSt prm s) := by
  unfold TetraBFT.decideSt
  split
  · exact h
  · split
    · exact h
    · rename_i x hx
      refine ⟨h.view_ge, h.one, h.just, h.out, fun y v hd => ?_⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      exact quorumVal_spec hx

theorem Inv.step {s : St n V} (h : Inv prm s) (p : Fin n) (ib : Fin n → List (Msg V)) :
    Inv prm (step prm p s ib) :=
  ((((((((h.recvSt prm ib).echoSt prm).viewSt prm).proposeSt prm p).vote1St prm).voteKSt prm
    le_rfl (by omega)).voteKSt prm (by omega) (by omega)).voteKSt prm (by omega) le_rfl).decideSt
    prm

theorem Inv.init (x : V) : Inv prm ({ inp := x } : St n V) where
  view_ge := by simp
  one := by simp
  just := by simp
  out := by simp
  dec := by simp

/-! ### How a step changes the state -/

/-- A stage that only casts votes in the current view (and may decide or propose). -/
structure VoteExt (s s' : St n V) : Prop where
  view : s'.view = s.view
  rcv : s'.rcv = s.rcv
  inp : s'.inp = s.inp
  votes : ∃ l, s'.votes = s.votes ++ l ∧ ∀ w ∈ l, w.view = s.view
  dec : ∀ d, s.dec = some d → s'.dec = some d

theorem VoteExt.refl (s : St n V) : VoteExt s s :=
  ⟨rfl, rfl, rfl, ⟨[], by simp, by simp⟩, fun _ h => h⟩

theorem VoteExt.trans {s s' s'' : St n V} (h : VoteExt s s') (h' : VoteExt s' s'') :
    VoteExt s s'' := by
  obtain ⟨l, hl, hlv⟩ := h.votes
  obtain ⟨l', hl', hlv'⟩ := h'.votes
  refine ⟨h'.view.trans h.view, h'.rcv.trans h.rcv, h'.inp.trans h.inp, ⟨l ++ l', ?_, ?_⟩,
    fun d hd => h'.dec d (h.dec d hd)⟩
  · rw [hl', hl, List.append_assoc]
  · intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact hlv w hw
    · rw [hlv' w hw, h.view]

theorem VoteExt.castVote (s : St n V) (k : ℕ) (x : V) : VoteExt s (castVote s k x) :=
  ⟨rfl, rfl, rfl, ⟨[⟨k, s.view, x⟩], rfl, by simp⟩, fun _ h => h⟩

theorem VoteExt.proposeSt (p : Fin n) (s : St n V) : VoteExt s (proposeSt prm p s) := by
  unfold TetraBFT.proposeSt
  split
  · split
    · exact .refl s
    · split
      · exact ⟨rfl, rfl, rfl, ⟨[], by simp, by simp⟩, fun _ h => h⟩
      · exact .refl s
  · exact .refl s

theorem VoteExt.vote1St (s : St n V) : VoteExt s (vote1St prm s) := by
  unfold TetraBFT.vote1St
  split
  · exact .refl s
  · split
    · exact .refl s
    · split
      · exact .castVote s _ _
      · split
        · exact .castVote s _ _
        · exact .refl s

theorem VoteExt.voteKSt (k : ℕ) (s : St n V) : VoteExt s (voteKSt prm k s) := by
  unfold TetraBFT.voteKSt
  split
  · exact .refl s
  · split
    · exact .refl s
    · exact .castVote s _ _

theorem VoteExt.decideSt (s : St n V) : VoteExt s (decideSt prm s) := by
  unfold TetraBFT.decideSt
  split
  · exact .refl s
  · split
    · exact .refl s
    · exact ⟨rfl, rfl, rfl, ⟨[], by simp, by simp⟩, fun d hd => by simp_all⟩

theorem echoSt_fields (s : St n V) : (echoSt prm s).votes = s.votes ∧ (echoSt prm s).rcv = s.rcv ∧
    (echoSt prm s).dec = s.dec ∧ (echoSt prm s).inp = s.inp ∧ (echoSt prm s).view = s.view := by
  unfold TetraBFT.echoSt; split
  · simp
  · split <;> simp

theorem viewSt_fields (s : St n V) : (viewSt prm s).votes = s.votes ∧ (viewSt prm s).rcv = s.rcv ∧
    (viewSt prm s).dec = s.dec ∧ (viewSt prm s).inp = s.inp ∧ s.view ≤ (viewSt prm s).view := by
  unfold TetraBFT.viewSt
  split
  · rename_i w hw
    have := (maxVC_spec hw).1
    simp; omega
  · split <;> simp

/-- The state after the receive, echo and view-change stages. -/
def preVote (s : St n V) (ib : Fin n → List (Msg V)) : St n V :=
  viewSt prm (echoSt prm (recvSt s ib))

theorem preVote_votes (s : St n V) (ib) : (preVote prm s ib).votes = s.votes := by
  simp only [preVote, (viewSt_fields prm _).1, (echoSt_fields prm _).1, TetraBFT.recvSt]

theorem preVote_rcv (s : St n V) (ib) : (preVote prm s ib).rcv =
    s.rcv ++ (List.finRange n).flatMap (fun q => (ib q).map fun m => (q, m)) := by
  simp only [preVote, (viewSt_fields prm _).2.1, (echoSt_fields prm _).2.1, TetraBFT.recvSt]

theorem preVote_dec (s : St n V) (ib) : (preVote prm s ib).dec = s.dec := by
  simp only [preVote, (viewSt_fields prm _).2.2.1, (echoSt_fields prm _).2.2.1, TetraBFT.recvSt]

theorem preVote_inp (s : St n V) (ib) : (preVote prm s ib).inp = s.inp := by
  simp only [preVote, (viewSt_fields prm _).2.2.2.1, (echoSt_fields prm _).2.2.2.1,
    TetraBFT.recvSt]

theorem preVote_view (s : St n V) (ib) : s.view ≤ (preVote prm s ib).view := by
  have h1 := (viewSt_fields prm (echoSt prm (recvSt s ib))).2.2.2.2
  have h2 := (echoSt_fields prm (recvSt s ib)).2.2.2.2
  simp only [preVote]
  rw [h2] at h1
  exact h1

theorem step_voteExt (p : Fin n) (s : St n V) (ib) :
    VoteExt (preVote prm s ib) (step prm p s ib) :=
  (((((VoteExt.proposeSt prm p _).trans (.vote1St prm _)).trans (.voteKSt prm 2 _)).trans
    (.voteKSt prm 3 _)).trans (.voteKSt prm 4 _)).trans (.decideSt prm _)

theorem step_rcv (p : Fin n) (s : St n V) (ib) : (step prm p s ib).rcv =
    s.rcv ++ (List.finRange n).flatMap (fun q => (ib q).map fun m => (q, m)) := by
  rw [(step_voteExt prm p s ib).rcv, preVote_rcv]

theorem step_view (p : Fin n) (s : St n V) (ib) : s.view ≤ (step prm p s ib).view := by
  rw [(step_voteExt prm p s ib).view]; exact preVote_view prm s ib

theorem step_votes (p : Fin n) (s : St n V) (ib) : ∃ l, (step prm p s ib).votes = s.votes ++ l ∧
    ∀ w ∈ l, w.view = (step prm p s ib).view := by
  obtain ⟨l, hl, hlv⟩ := (step_voteExt prm p s ib).votes
  refine ⟨l, by rw [hl, preVote_votes], fun w hw => ?_⟩
  rw [hlv w hw, (step_voteExt prm p s ib).view]

theorem step_dec (p : Fin n) (s : St n V) (ib) {d : V × ℕ} (h : s.dec = some d) :
    (step prm p s ib).dec = some d :=
  (step_voteExt prm p s ib).dec d (by rw [preVote_dec, h])

theorem step_inp (p : Fin n) (s : St n V) (ib) : (step prm p s ib).inp = s.inp := by
  rw [(step_voteExt prm p s ib).inp, preVote_inp]

/-! ### Run-level facts -/

section Run

variable {prm} (R : Run (Fin n) (Msg V) V)

local notation "A" => tetra (V := V) prm

theorem st_succ' (τ : ℕ) (p : Fin n) :
    R.st A (τ + 1) p = step prm p (R.st A τ p) (R.inbox A p τ) := R.st_succ A τ p

/-- The invariant holds in every state (of every node, by construction of `Run.st`). -/
theorem st_inv (τ : ℕ) (p : Fin n) : Inv prm (R.st A τ p) := by
  induction τ with
  | zero => exact Inv.init prm _
  | succ τ ih => rw [st_succ']; exact ih.step prm p _

theorem st_view_mono {τ τ' : ℕ} (h : τ ≤ τ') (p : Fin n) :
    (R.st A τ p).view ≤ (R.st A τ' p).view := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [st_succ']; exact le_trans ih (step_view prm _ _ _)

/-- Votes are only appended, and in views at least the current one. -/
theorem st_votes_later {τ τ' : ℕ} (h : τ ≤ τ') (p : Fin n) : ∃ l,
    (R.st A τ' p).votes = (R.st A τ p).votes ++ l ∧ ∀ w ∈ l, (R.st A τ p).view ≤ w.view := by
  induction h with
  | refl => exact ⟨[], by simp, by simp⟩
  | step hle ih =>
    obtain ⟨l, hl, hlv⟩ := ih
    obtain ⟨l', hl', hlv'⟩ := step_votes prm p (R.st A _ p) (R.inbox A p _)
    refine ⟨l ++ l', ?_, fun w hw => ?_⟩
    · rw [st_succ', hl', hl, List.append_assoc]
    · rcases List.mem_append.1 hw with hw | hw
      · exact hlv w hw
      · rw [hlv' w hw, ← st_succ']
        exact st_view_mono R (Nat.le_succ_of_le hle) p

theorem st_votes_mono {τ τ' : ℕ} (h : τ ≤ τ') (p : Fin n) {w : Vote V}
    (hw : w ∈ (R.st A τ p).votes) : w ∈ (R.st A τ' p).votes := by
  obtain ⟨l, hl, -⟩ := st_votes_later R h p
  rw [hl]; exact List.mem_append_left _ hw

theorem st_dec_mono {τ τ' : ℕ} (h : τ ≤ τ') (p : Fin n) {d : V × ℕ}
    (hd : (R.st A τ p).dec = some d) : (R.st A τ' p).dec = some d := by
  induction h with
  | refl => exact hd
  | step _ ih => rw [st_succ']; exact step_dec prm p _ _ ih

/-- The lists of received messages are message logs: every step appends the inbox. -/
theorem tetra_logs : (tetra (V := V) prm).Logs St.rcv where
  log_init _ _ := rfl
  log_step p s ib := ⟨_, step_rcv prm p s ib, fun q m => by simp⟩

/-- **Authenticity**: a message received from a correct node was in its outbox earlier. -/
theorem rcv_authentic {τ : ℕ} {p q : Fin n} {m : Msg V} (hq : q ∉ R.faulty)
    (h : (q, m) ∈ (R.st A τ p).rcv) : ∃ τ' < τ, m ∈ (R.st A τ' q).out :=
  tetra_logs.exists_mem_send_of_mem_log R hq h

/-- The abstract execution of a run: the votes ever cast and the decisions. -/
def toExec : Execution (Fin n) V where
  faulty := R.faulty
  voted q w := ∃ τ, w ∈ (R.st A τ q).votes
  decided q x v := ∃ τ, (R.st A τ q).dec = some (x, v)

/-- A proof/suggest report sent by a node is honest with respect to all the votes it ever casts:
votes of views below the report's view are final once the view is entered. -/
theorem voted_below_iff {τ : ℕ} {q : Fin n} {r : ℕ} (hr : r ≤ (R.st A τ q).view) {w : Vote V}
    (hw : w.view < r) : (toExec (prm := prm) R).voted q w ↔ w ∈ (R.st A τ q).votes := by
  constructor
  · rintro ⟨τ'', h''⟩
    rcases le_total τ'' τ with hle | hle
    · exact st_votes_mono R hle q h''
    · obtain ⟨l, hl, hlv⟩ := st_votes_later R hle q
      rw [hl] at h''
      rcases List.mem_append.1 h'' with h | h
      · exact h
      · have := hlv w h; omega
  · intro h; exact ⟨τ, h⟩

theorem proof_honest {τ : ℕ} {q : Fin n} {r : ℕ} {rep : Report V}
    (h : Msg.proof r rep ∈ (R.st A τ q).out) :
    IsReport ((toExec (prm := prm) R).voted q) r 1 4 rep := by
  obtain ⟨hr, hrep⟩ := (st_inv R τ q).out _ h
  rw [hrep]
  exact (mkReport_isReport _ r 1 4).congr fun w hw => (voted_below_iff R hr hw).symm

theorem suggest_honest {τ : ℕ} {q : Fin n} {r : ℕ} {rep : Report V}
    (h : Msg.suggest r rep ∈ (R.st A τ q).out) :
    IsReport ((toExec (prm := prm) R).voted q) r 2 3 rep := by
  obtain ⟨hr, hrep⟩ := (st_inv R τ q).out _ h
  rw [hrep]
  exact (mkReport_isReport _ r 2 3).congr fun w hw => (voted_below_iff R hr hw).symm

/-- A quorum of received vote messages yields a quorum of cast votes. -/
theorem quorum_of_senders {τ : ℕ} {p : Fin n} {k v : ℕ} {x : V} :
    ∀ q ∈ senders (R.st A τ p).rcv (.vote k v x), q ∉ R.faulty →
      (toExec (prm := prm) R).voted q ⟨k, v, x⟩ := by
  intro q hq hqF
  simp only [senders, mem_filter, mem_univ, true_and] at hq
  obtain ⟨τ', -, hm⟩ := rcv_authentic R hqF hq
  exact ⟨τ', (st_inv R τ' q).out _ hm⟩

/-- **Refinement.** Every run of the protocol with at most `f` faulty nodes is an abstract
execution satisfying the safety hypotheses. -/
theorem toExec_safetyHyp (hR : R.faulty.card ≤ prm.f) :
    (toExec (prm := prm) R).SafetyHyp prm.f where
  card_faulty := hR
  one_val p _ k r x y := by
    rintro ⟨τ₁, h₁⟩ ⟨τ₂, h₂⟩
    have h₁' := st_votes_mono R (le_max_left τ₁ τ₂) p h₁
    have h₂' := st_votes_mono R (le_max_right τ₁ τ₂) p h₂
    exact (st_inv R _ p).one _ h₁' _ h₂' rfl rfl
  quorum_prev p _ k r x hk2 hk4 := by
    rintro ⟨τ, h⟩
    obtain ⟨-, -, -, hq, -⟩ := (st_inv R τ p).just _ h
    exact ⟨senders (R.st A τ p).rcv (.vote (k - 1) r x), by simpa using hq hk2,
      quorum_of_senders R (τ := τ) (p := p)⟩
  rule3 p _ r x := by
    rintro ⟨τ, h⟩
    obtain ⟨-, -, hr, -, -⟩ := (st_inv R τ p).just _ h
    rcases hr rfl with h0 | hr
    · exact ⟨∅, fun _ => ⟨none, none, none⟩, by simp, Or.inl h0⟩
    · refine ⟨_, _, fun q hq hqF => ?_, by simpa using hr⟩
      obtain ⟨τ', -, hm⟩ := rcv_authentic R hqF (mem_of_repSenders hq)
      exact proof_honest R hm
  decided_committed p _ x v := by
    rintro ⟨τ, h⟩
    exact ⟨senders (R.st A τ p).rcv (.vote 4 v x), by simpa using (st_inv R τ p).dec x v h,
      quorum_of_senders R (τ := τ) (p := p)⟩

/-- **Theorem 1 (agreement)** for the message-level protocol: in every run with at most `f`
faulty nodes, `3f < n`, no two correct nodes decide different values. No synchrony assumption is
needed. -/
theorem tetra_agreement (hn : 3 * prm.f < n) (hR : R.faulty.card ≤ prm.f) {p q : Fin n}
    (hp : p ∉ R.faulty) (hq : q ∉ R.faulty) {x y : V} (hx : R.Decides A p x)
    (hy : R.Decides A q y) : x = y := by
  obtain ⟨τ₁, h₁⟩ := hx
  obtain ⟨τ₂, h₂⟩ := hy
  simp only [tetra, Option.map_eq_some_iff] at h₁ h₂
  obtain ⟨⟨x', v⟩, h₁, rfl⟩ := h₁
  obtain ⟨⟨y', v'⟩, h₂, rfl⟩ := h₂
  exact Execution.agreement (by simpa using hn) (toExec_safetyHyp R hR) hp hq ⟨τ₁, h₁⟩ ⟨τ₂, h₂⟩

end Run

end TetraBFT
