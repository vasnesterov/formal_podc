import Papers.PODC2015.WeakestFDEventualConsistency.Specs

/-!
# Lemma 3 repaired: Algorithm 5 with sequence numbers on promotions implements ETOB from `Ω`

`ETOBAlgorithm.lean` shows that Lemma 3 of [DGKPS15] is false: links are not FIFO, and a process
adopts *every* promotion of its current leader, so a delayed older promotion can make `d_i`
shrink infinitely often. Here we repair Algorithm 5 and prove that the repaired algorithm
implements ETOB in every environment (with finitely many processes).

**The repair.** The leader tags each promotion with a counter (the number of promotions it has sent
so far, the current one included): on a time-out with `Ω_i = p_i`, `p_i` sends
`promote(cnt_i + 1, promote_i)` and sets `cnt_i := cnt_i + 1`. Process `p_i` keeps
`last_i : P → ℕ` (initially `0`) and, on reception of `promote(n, seq)` from `p_j`, adopts it
(`d_i := seq`, `last_i[j] := n`) only if `Ω_i = p_j` **and** `last_i[j] < n`. Everything else is
as in Algorithm 5.

**Simplification.** Broadcasts carry no causal dependencies (`C(m) = ∅`), so the causality graph is
a `Finset` of messages and `UpdatePromote` replaces `promote_i` by *some* duplicate-free sequence
having `promote_i` as a prefix and containing exactly the messages of `CG_i`. As in
`ETOBAlgorithm.lean`, the choice is an arbitrary function `upd` satisfying `UpdValid`
(`exists_updValid` shows one exists); the theorem holds for every such choice.

**The proof.** Let `ℓ` be the final leader and `T_Ω` the time from which every correct process
trusts `ℓ`. Promotions of `ℓ` with larger counters were sent later, and `promote_ℓ` only grows by
appending, so promotions of `ℓ` are prefix-ordered by their counters (`prefix_of_counter_le`).
After `T_Ω`, a correct process only adopts promotions of `ℓ`, and only with increasing counters.
Every correct process `p` adopts at least one promotion of `ℓ` at some time `≥ T_Ω`
(`exists_good`): `ℓ` sends a promotion after `T_Ω` whose counter exceeds everything adopted from
`ℓ` before `T_Ω`, and `p` receives it. From then on `d_p` is the payload of the promotion of `ℓ`
with counter `last_p[ℓ]` (`Good`). The paper's `τ = τ_Ω + Δt + Δc` (which uses a "longest
communication delay", which need not exist in an asynchronous run) is replaced by the maximum
over the correct processes of these adoption times (`P` finite).
-/

namespace Podc.WeakestFDEventualConsistency

open Cslib.FailureDetectors

namespace Alg5Fixed

/-! ### Generic facts about the model -/

section Model

variable {P R M I O S : Type*} [DecidableEq P] {A : Algorithm P R M I O S} (r : Run P R I)

-- Model candidate
/-- A local state changes only by a resolved step of its owner. -/
lemma st_succ_cases (t : ℕ) (p : P) :
    A.st r p (t + 1) = A.st r p t ∨ ∃ c e, r.σ t = some (p, c) ∧ (A.cfg r t).event c = some e ∧
      A.st r p (t + 1) = (A.step p (r.H p t) (A.st r p t) e).1 := by
  rcases hσ : r.σ t with _ | ⟨p', c⟩
  · left; exact Algorithm.loc_succ_of_ne r t p (by simp [hσ])
  · by_cases hp : p = p'
    · subst hp
      rcases he : (A.cfg r t).event c with _ | e
      · left; rw [Algorithm.st, (Algorithm.cfg_succ_of_event_none r t p c hσ he).1]
      · right; exact ⟨c, e, rfl, he, (Algorithm.cfg_succ_of_event r t p c e hσ he).1⟩
    · left; exact Algorithm.loc_succ_of_ne r t p (by
        intro c' h; rw [hσ] at h; simp at h; exact hp h.1.symm)

-- Model candidate
lemma event_eq_input {C : Config P M S} {c : Choice P I} {i : I}
    (h : C.event c = some (.input i)) : c = .input i := by
  cases c with
  | recv q' s =>
    simp only [Config.event] at h
    rcases hs : C.msg s with _ | ⟨q'', m'⟩
    · simp [hs] at h
    · simp only [hs] at h; split_ifs at h; simp at h
  | tick => simp [Config.event] at h
  | input i' => simp only [Config.event, Option.some.injEq, Event.input.injEq] at h; rw [h]

-- Model candidate
/-- A stored message was sent strictly before the current time. -/
lemma lt_of_msg {t s : ℕ} {q : P} {m : M} (h : (A.cfg r t).msg s = some (q, m)) : s < t := by
  by_contra hc
  rw [Algorithm.msg_eq_none_of_le r t s (by omega)] at h
  exact absurd h (by simp)

end Model

/-! ### The repaired algorithm -/

variable {P M : Type*} [DecidableEq P] [DecidableEq M]

/-- `upd` implements `UpdatePromote` without causal dependencies: from a duplicate-free `promote`
whose messages are in the graph `g`, it returns a duplicate-free extension of `promote` whose
messages are exactly those of `g`. -/
def UpdValid (upd : List M → Finset M → List M) : Prop :=
  ∀ pr g, pr.Nodup → (∀ m ∈ pr, m ∈ g) →
    pr <+: upd pr g ∧ (upd pr g).Nodup ∧ ∀ m, m ∈ upd pr g ↔ m ∈ g

/-- `UpdatePromote` can be implemented (append the new messages in any order). -/
lemma exists_updValid : ∃ upd : List M → Finset M → List M, UpdValid upd := by
  refine ⟨fun pr g => pr ++ (g.filter (· ∉ pr)).toList, fun pr g hn hsub =>
    ⟨List.prefix_append _ _, ?_, fun m => ?_⟩⟩
  · rw [List.nodup_append]
    refine ⟨hn, Finset.nodup_toList _, fun a ha b hb => ?_⟩
    simp only [Finset.mem_toList, Finset.mem_filter] at hb
    rintro rfl; exact hb.2 ha
  · simp only [List.mem_append, Finset.mem_toList, Finset.mem_filter]
    constructor
    · rintro (h | h)
      · exact hsub m h
      · exact h.1
    · intro h; by_cases hm : m ∈ pr
      · exact Or.inl hm
      · exact Or.inr ⟨h, hm⟩

/-- Messages. -/
inductive Msg (M : Type*) where
  /-- `update(CG)`. -/
  | update (g : Finset M)
  /-- `promote(n, seq)`: the `n`-th promotion of its sender. -/
  | promote (n : ℕ) (l : List M)

/-- Local state. -/
structure State (P M : Type*) where
  /-- Output variable. -/
  d : List M
  /-- Promotion sequence. -/
  promote : List M
  /-- Causality graph (no edges: just the known messages). -/
  cg : Finset M
  /-- Number of promotions sent so far. -/
  cnt : ℕ
  /-- `last q`: the counter of the last promotion adopted from `q` (`0`: none). -/
  last : P → ℕ

/-- **Algorithm 5** of [DGKPS15], repaired with sequence numbers on promotions (`Ω` gives the
failure-detector values; inputs are `broadcastETOB(m)`, without causal dependencies). -/
def alg (upd : List M → Finset M → List M) : Algorithm P P (Msg M) M Empty (State P M) where
  init _ := ⟨[], [], ∅, 0, fun _ => 0⟩
  step p d s e :=
    match e with
    | .input m => ({ s with cg := insert m s.cg }, some (.update (insert m s.cg)), [])
    | .recv _ (.update g) =>
      ({ s with cg := s.cg ∪ g, promote := upd s.promote (s.cg ∪ g) }, none, [])
    | .recv q (.promote n l) =>
      if d = q ∧ s.last q < n then ({ s with d := l, last := Function.update s.last q n }, none, [])
      else (s, none, [])
    | .tick =>
      if d = p then ({ s with cnt := s.cnt + 1 }, some (.promote (s.cnt + 1) s.promote), [])
      else (s, none, [])

/-- The ETOB history of a run of the repaired Algorithm 5. -/
def tobHist (upd : List M → Finset M → List M) (r : Run P P M) : TOBHist P M where
  bcast p m t := r.σ t = some (p, .input m)
  d p t := ((alg upd).st r p t).d

/-! ### Facts about one step -/

variable (upd : List M → Finset M → List M)

lemma step_bcast {p d : P} {s : State P M} {e : Event P (Msg M) M} {b : Msg M}
    (h : ((alg upd).step p d s e).2.1 = some b) :
    (∃ m, e = .input m ∧ b = .update (insert m s.cg)) ∨
      (e = .tick ∧ d = p ∧ b = .promote (s.cnt + 1) s.promote ∧
        ((alg upd).step p d s e).1.cnt = s.cnt + 1) := by
  rcases e with ⟨q, g | ⟨n, l⟩⟩ | _ | m
  · simp [alg] at h
  · simp only [alg] at h; split_ifs at h
  · simp only [alg] at h ⊢; split_ifs at h ⊢ with hd
    · simp only [Option.some.injEq] at h; exact Or.inr ⟨trivial, hd, h.symm, rfl⟩
  · simp only [alg, Option.some.injEq] at h; exact Or.inl ⟨m, rfl, h.symm⟩

lemma step_promote (p d : P) (s : State P M) (e : Event P (Msg M) M) :
    ((alg upd).step p d s e).1.promote = s.promote ∨ ∃ q g, e = .recv q (.update g) ∧
      ((alg upd).step p d s e).1.promote = upd s.promote (s.cg ∪ g) ∧
      ((alg upd).step p d s e).1.cg = s.cg ∪ g := by
  rcases e with ⟨q, g | ⟨n, l⟩⟩ | _ | m
  · exact Or.inr ⟨q, g, rfl, rfl, rfl⟩
  · left; simp only [alg]; split_ifs <;> rfl
  · left; simp only [alg]; split_ifs <;> rfl
  · left; rfl

lemma step_cg_mem (p d : P) (s : State P M) (e : Event P (Msg M) M) (m : M) :
    (m ∈ s.cg → m ∈ ((alg upd).step p d s e).1.cg) ∧
    (m ∈ ((alg upd).step p d s e).1.cg → m ∈ s.cg ∨ e = .input m ∨
      ∃ q g, e = .recv q (.update g) ∧ m ∈ g) := by
  rcases e with ⟨q, g | ⟨n, l⟩⟩ | _ | m'
  · simp only [alg, Finset.mem_union]
    exact ⟨Or.inl, fun h => h.elim Or.inl fun h => Or.inr (Or.inr ⟨q, g, rfl, h⟩)⟩
  · simp only [alg]; split_ifs <;> exact ⟨id, Or.inl⟩
  · simp only [alg]; split_ifs <;> exact ⟨id, Or.inl⟩
  · simp only [alg, Finset.mem_insert]
    exact ⟨Or.inr, fun h => h.elim (fun h => Or.inr (Or.inl (by rw [h]))) Or.inl⟩

lemma step_cnt_le (p d : P) (s : State P M) (e : Event P (Msg M) M) :
    s.cnt ≤ ((alg upd).step p d s e).1.cnt := by
  rcases e with ⟨q, g | ⟨n, l⟩⟩ | _ | m'
  · exact le_rfl
  · simp only [alg]; split_ifs <;> exact le_rfl
  · simp only [alg]; split_ifs
    · exact Nat.le_succ _
    · exact le_rfl
  · exact le_rfl

/-- How `d` and `last` change in a step: not at all, or by adopting a promotion of the trusted
process `d` with a larger counter. -/
lemma step_last (p d : P) (s : State P M) (e : Event P (Msg M) M) :
    (((alg upd).step p d s e).1.d = s.d ∧ ((alg upd).step p d s e).1.last = s.last) ∨
    ∃ n l, e = .recv d (.promote n l) ∧ s.last d < n ∧ ((alg upd).step p d s e).1.d = l ∧
      ((alg upd).step p d s e).1.last = Function.update s.last d n := by
  rcases e with ⟨q, g | ⟨n, l⟩⟩ | _ | m'
  · left; exact ⟨rfl, rfl⟩
  · simp only [alg]; split_ifs with h
    · obtain ⟨rfl, h⟩ := h; right; exact ⟨n, l, rfl, h, rfl, rfl⟩
    · left; exact ⟨rfl, rfl⟩
  · left; simp only [alg]; split_ifs <;> exact ⟨rfl, rfl⟩
  · left; exact ⟨rfl, rfl⟩

lemma step_recv_promote (p q : P) (s : State P M) (n : ℕ) (l : List M) :
    n ≤ ((alg upd).step p q s (.recv q (.promote n l))).1.last q ∧
      (s.last q < n → ((alg upd).step p q s (.recv q (.promote n l))).1.d = l ∧
        ((alg upd).step p q s (.recv q (.promote n l))).1.last q = n) := by
  simp only [alg, true_and]
  split_ifs with h
  · simp
  · exact ⟨by simp only; omega, fun h' => absurd h' h⟩

/-! ### Invariants of runs -/

variable {upd} {r : Run P P M}

/-- What a promotion in transit is: the `n`-th promotion of its sender, sent on a time-out,
carrying the sender's `promote` sequence. -/
lemma msg_promote_spec {t s₀ : ℕ} {q : P} {n : ℕ} {l : List M}
    (h : ((alg upd).cfg r t).msg s₀ = some (q, .promote n l)) :
    s₀ < t ∧ n = ((alg upd).st r q s₀).cnt + 1 ∧ l = ((alg upd).st r q s₀).promote ∧
      ((alg upd).st r q (s₀ + 1)).cnt = n := by
  obtain ⟨c, e, hσ, he, hb⟩ := Algorithm.msg_spec r h
  rcases step_bcast upd hb with ⟨m, -, hb'⟩ | ⟨-, -, hb', hc⟩
  · cases hb'
  · simp only [Msg.promote.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    refine ⟨lt_of_msg r h, rfl, rfl, ?_⟩
    rw [(Algorithm.cfg_succ_of_event r s₀ q c e hσ he).1, hc]

/-- What an update in transit is: sent by a broadcast step. -/
lemma msg_update_spec {t s₀ : ℕ} {q : P} {g : Finset M}
    (h : ((alg upd).cfg r t).msg s₀ = some (q, .update g)) :
    s₀ < t ∧ ∃ m, r.σ s₀ = some (q, .input m) ∧ g = insert m ((alg upd).st r q s₀).cg := by
  obtain ⟨c, e, hσ, he, hb⟩ := Algorithm.msg_spec r h
  rcases step_bcast upd hb with ⟨m, rfl, hb'⟩ | ⟨-, -, hb', -⟩
  · simp only [Msg.update.injEq] at hb'
    refine ⟨lt_of_msg r h, m, ?_, hb'⟩
    rw [hσ, event_eq_input he]
  · cases hb'

/-- The promotion broadcast by a time-out of a process trusting itself. -/
lemma tick_msg {t : ℕ} {ℓ : P} (hσ : r.σ t = some (ℓ, .tick)) (hH : r.H ℓ t = ℓ) :
    ((alg upd).cfg r (t + 1)).msg t =
      some (ℓ, .promote (((alg upd).st r ℓ t).cnt + 1) ((alg upd).st r ℓ t).promote) := by
  rw [(Algorithm.cfg_succ_of_event r t ℓ _ _ hσ (Algorithm.event_tick _)).2.1, hH]
  simp [alg]

lemma cnt_mono {p : P} {t t' : ℕ} (h : t ≤ t') :
    ((alg upd).st r p t).cnt ≤ ((alg upd).st r p t').cnt :=
  Algorithm.st_rel_of_step r (fun _ (a b : State P M) => a.cnt ≤ b.cnt) (fun _ _ => le_rfl)
    (fun _ _ _ _ h1 h2 => h1.trans h2) (fun _ p _ e _ _ => step_cnt_le upd p _ _ e) p t t' h

lemma last_mono {p q : P} {t t' : ℕ} (h : t ≤ t') :
    ((alg upd).st r p t).last q ≤ ((alg upd).st r p t').last q :=
  Algorithm.st_rel_of_step r (fun _ (a b : State P M) => ∀ q, a.last q ≤ b.last q)
    (fun _ _ _ => le_rfl) (fun _ _ _ _ h1 h2 q => (h1 q).trans (h2 q)) (fun t p _ e _ _ q => by
      rcases step_last upd p (r.H p t) _ e with ⟨-, h⟩ | ⟨n, l, -, hlt, -, h⟩
      · rw [h]
      · rw [h]
        by_cases hq : q = r.H p t
        · subst hq; simp only [Function.update_self]; omega
        · simp [Function.update_of_ne hq]) p t t' h q

/-- Promotions of the same sender with larger counters were sent later. -/
lemma time_le_of_counter_le {t₁ t₂ s₁ s₂ n₁ n₂ : ℕ} {q : P} {l₁ l₂ : List M}
    (h₁ : ((alg upd).cfg r t₁).msg s₁ = some (q, .promote n₁ l₁))
    (h₂ : ((alg upd).cfg r t₂).msg s₂ = some (q, .promote n₂ l₂)) (hn : n₁ ≤ n₂) : s₁ ≤ s₂ := by
  by_contra hs
  obtain ⟨-, hn₁, -, -⟩ := msg_promote_spec h₁
  obtain ⟨-, -, -, hc₂⟩ := msg_promote_spec h₂
  have := cnt_mono (upd := upd) (r := r) (p := q) (show s₂ + 1 ≤ s₁ by omega)
  omega

/-- **No creation** at the level of causality graphs: every message of a graph was broadcast
earlier. -/
lemma cg_known : ∀ t p m, m ∈ ((alg upd).st r p t).cg →
    ∃ q t', t' < t ∧ r.σ t' = some (q, .input m) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro p m hm
  rcases t with _ | t
  · exact absurd hm (by simp [Algorithm.st, Algorithm.initCfg, alg])
  rcases st_succ_cases r t p with h | ⟨c, e, hσ, he, h⟩
  · rw [h] at hm
    obtain ⟨q, t', ht', h'⟩ := ih t (by omega) p m hm
    exact ⟨q, t', by omega, h'⟩
  · rw [h] at hm
    rcases (step_cg_mem upd p _ _ e m).2 hm with hm | rfl | ⟨q, g, rfl, hmg⟩
    · obtain ⟨q, t', ht', h'⟩ := ih t (by omega) p m hm
      exact ⟨q, t', by omega, h'⟩
    · exact ⟨p, t, by omega, by rw [hσ, event_eq_input he]⟩
    · obtain ⟨s₀, -, hm₀⟩ := Algorithm.event_eq_recv he
      obtain ⟨hs₀, m', hσ', rfl⟩ := msg_update_spec hm₀
      rcases Finset.mem_insert.1 hmg with rfl | hmg
      · exact ⟨q, s₀, by omega, hσ'⟩
      · obtain ⟨q', t', ht', h'⟩ := ih s₀ (by omega) q m hmg
        exact ⟨q', t', by omega, h'⟩

/-- `d` is empty or a `promote` sequence of some process at an earlier time. -/
lemma d_inv : ∀ t p, ((alg upd).st r p t).d = [] ∨
    ∃ q s₀, s₀ < t ∧ ((alg upd).st r p t).d = ((alg upd).st r q s₀).promote := by
  refine Algorithm.st_induction_time r (fun t _ (s : State P M) => s.d = [] ∨
    ∃ q s₀, s₀ < t ∧ s.d = ((alg upd).st r q s₀).promote) ?_ ?_ ?_
  · intro p; left; rfl
  · rintro t p s (h | ⟨q, s₀, hs, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q, s₀, by omega, h⟩
  · rintro t p c e - he ih
    rcases step_last upd p (r.H p t) _ e with ⟨h, -⟩ | ⟨n, l, rfl, -, h, -⟩
    · rw [h]
      rcases ih with h' | ⟨q, s₀, hs, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨q, s₀, by omega, h'⟩
    · obtain ⟨s₁, -, hm⟩ := Algorithm.event_eq_recv he
      obtain ⟨hs₁, -, rfl, -⟩ := msg_promote_spec hm
      exact Or.inr ⟨_, s₁, by omega, h⟩

/-- A positive `last q` is the counter of a promotion of `q` sent earlier. -/
lemma last_inv : ∀ t p q, 0 < ((alg upd).st r p t).last q →
    ∃ s₀ < t, ∃ l, ((alg upd).cfg r (s₀ + 1)).msg s₀ =
      some (q, .promote (((alg upd).st r p t).last q) l) := by
  refine Algorithm.st_induction_time r (fun t _ (s : State P M) => ∀ q, 0 < s.last q → ∃ s₀ < t, ∃ l,
    ((alg upd).cfg r (s₀ + 1)).msg s₀ = some (q, .promote (s.last q) l)) ?_ ?_ ?_
  · intro p q h; simp [alg] at h
  · intro t p s ih q hq
    obtain ⟨s₀, hs, l, h⟩ := ih q hq
    exact ⟨s₀, by omega, l, h⟩
  · rintro t p c e - he ih q hq
    rcases step_last upd p (r.H p t) _ e with ⟨-, h⟩ | ⟨n, l, rfl, -, -, h⟩
    · rw [h] at hq ⊢
      obtain ⟨s₀, hs, l, h⟩ := ih q hq
      exact ⟨s₀, by omega, l, h⟩
    · rw [h] at hq ⊢
      by_cases hqd : q = r.H p t
      · subst hqd
        obtain ⟨s₁, -, hm⟩ := Algorithm.event_eq_recv he
        have hs₁ := lt_of_msg r hm
        refine ⟨s₁, by omega, l, ?_⟩
        rw [Function.update_self, ← Algorithm.msg_eq_succ r hs₁]
        exact hm
      · rw [Function.update_of_ne hqd] at hq ⊢
        obtain ⟨s₀, hs, l, h⟩ := ih q hq
        exact ⟨s₀, by omega, l, h⟩

lemma last_le_cnt (t : ℕ) (p q : P) :
    ((alg upd).st r p t).last q ≤ ((alg upd).st r q t).cnt := by
  rcases Nat.eq_zero_or_pos (((alg upd).st r p t).last q) with h | h
  · rw [h]; exact Nat.zero_le _
  · obtain ⟨s₀, hs, l, hm⟩ := last_inv t p q h
    obtain ⟨-, -, -, hc⟩ := msg_promote_spec hm
    rw [← hc]; exact cnt_mono (by omega)

/-! ### Adoption of the leader's promotions -/

variable (upd r) in
/-- `d_p` is the payload of the promotion of `q` with counter `last_p[q]`. -/
def Good (p q : P) (t : ℕ) : Prop :=
  ∃ s₀, ((alg upd).cfg r (s₀ + 1)).msg s₀ =
    some (q, .promote (((alg upd).st r p t).last q) ((alg upd).st r p t).d)

/-- Receiving a promotion of the trusted process. -/
lemma recv_promote {t s₀ n : ℕ} {p q : P} {l : List M} (hσ : r.σ t = some (p, .recv q s₀))
    (hm : ((alg upd).cfg r t).msg s₀ = some (q, .promote n l)) (hH : r.H p t = q) :
    n ≤ ((alg upd).st r p (t + 1)).last q ∧
      (((alg upd).st r p t).last q < n → Good upd r p q (t + 1)) := by
  have hst := (Algorithm.cfg_succ_of_event r t p _ _ hσ (Algorithm.event_recv hm)).1
  rw [hH] at hst
  obtain ⟨h1, h2⟩ := step_recv_promote upd p q ((alg upd).st r p t) n l
  refine ⟨by rw [hst]; exact h1, fun hlt => ⟨s₀, ?_⟩⟩
  obtain ⟨hd, hl⟩ := h2 hlt
  rw [hst, hd, hl, ← Algorithm.msg_eq_succ r (lt_of_msg r hm)]
  exact hm

/-- If `last_p[q]` increased between `t₀` and `t`, then `p` adopted a promotion of `q` in
between. -/
lemma last_change {p q : P} {t₀ t : ℕ} (h : t₀ ≤ t)
    (hlt : ((alg upd).st r p t₀).last q < ((alg upd).st r p t).last q) :
    ∃ t', t₀ ≤ t' ∧ t' < t ∧ Good upd r p q (t' + 1) := by
  induction t, h using Nat.le_induction with
  | base => omega
  | succ t ht ih =>
    by_cases h' : ((alg upd).st r p t₀).last q < ((alg upd).st r p t).last q
    · obtain ⟨t', h1, h2, h3⟩ := ih h'
      exact ⟨t', h1, by omega, h3⟩
    · rcases st_succ_cases r t p with h | ⟨c, e, hσ, he, h⟩
      · rw [h] at hlt; exact absurd hlt h'
      · rw [h] at hlt
        rcases step_last upd p (r.H p t) _ e with ⟨-, h2⟩ | ⟨n, l, rfl, hn, -, h2⟩
        · rw [h2] at hlt; exact absurd hlt h'
        · by_cases hq : q = r.H p t
          · subst hq
            obtain ⟨s₀, rfl, hm⟩ := Algorithm.event_eq_recv he
            exact ⟨t, ht, by omega, (recv_promote hσ hm rfl).2 hn⟩
          · rw [h2, Function.update_of_ne hq] at hlt; exact absurd hlt h'

/-- While `p` trusts `ℓ`, `Good p ℓ` is preserved. -/
lemma good_step {p ℓ : P} {t : ℕ} (hg : Good upd r p ℓ t) (hH : r.H p t = ℓ) :
    Good upd r p ℓ (t + 1) := by
  rcases st_succ_cases r t p with h | ⟨c, e, hσ, he, h⟩
  · unfold Good; rw [h]; exact hg
  · rcases step_last upd p (r.H p t) _ e with ⟨hd, hl⟩ | ⟨n, l, rfl, hn, -, -⟩
    · obtain ⟨s₀, hs⟩ := hg
      exact ⟨s₀, by rw [h, hd, hl]; exact hs⟩
    · obtain ⟨s₀, rfl, hm⟩ := Algorithm.event_eq_recv he
      have := (recv_promote hσ hm rfl).2 hn
      rwa [hH] at this

lemma good_forever {p ℓ : P} {T t t' : ℕ} (hH : ∀ t ≥ T, r.H p t = ℓ) (hT : T ≤ t)
    (hg : Good upd r p ℓ t) (h : t ≤ t') : Good upd r p ℓ t' := by
  induction t', h using Nat.le_induction with
  | base => exact hg
  | succ t' ht ih => exact good_step ih (hH t' (by omega))

/-- Every correct process adopts a promotion of the final leader `ℓ` after `Ω` has stabilized. -/
lemma exists_good (hA : (alg upd).Admissible r) {p ℓ : P} (hp : r.F.Correct p)
    (hℓ : r.F.Correct ℓ) {T : ℕ} (hT : ∀ t ≥ T, ∀ q, r.F.Correct q → r.H q t = ℓ) :
    ∃ t ≥ T, Good upd r p ℓ t := by
  obtain ⟨tℓ, htℓ, hσℓ⟩ := hA.ticks ℓ hℓ T
  have hm := tick_msg (upd := upd) hσℓ (hT tℓ htℓ ℓ hℓ)
  obtain ⟨t', hσ'⟩ := hA.delivery p hp (tℓ + 1) tℓ ℓ _ hm
  obtain ⟨hlt', -⟩ := hA.recv_valid t' p ℓ tℓ hσ'
  rw [← Algorithm.msg_eq_succ r hlt'] at hm
  have hH : r.H p t' = ℓ := hT t' (by omega) p hp
  by_cases hlast : ((alg upd).st r p t').last ℓ < ((alg upd).st r ℓ tℓ).cnt + 1
  · exact ⟨t' + 1, by omega, (recv_promote hσ' hm hH).2 hlast⟩
  · have h1 := last_le_cnt (upd := upd) (r := r) T p ℓ
    have h2 := cnt_mono (upd := upd) (r := r) (p := ℓ) htℓ
    obtain ⟨t'', h3, -, h5⟩ := last_change (upd := upd) (r := r) (p := p) (q := ℓ)
      (show T ≤ t' by omega) (by omega)
    exact ⟨t'' + 1, by omega, h5⟩

/-! ### Properties that use `UpdValid` -/

variable (hupd : UpdValid upd)
include hupd

lemma promote_inv : ∀ t p, ((alg upd).st r p t).promote.Nodup ∧
    ∀ m ∈ ((alg upd).st r p t).promote, m ∈ ((alg upd).st r p t).cg := by
  refine Algorithm.st_induction r (fun _ (s : State P M) => s.promote.Nodup ∧ ∀ m ∈ s.promote, m ∈ s.cg) ?_ ?_
  · intro p; simp [alg]
  · rintro t p c e - - ⟨hn, hs⟩
    rcases step_promote upd p (r.H p t) _ e with h | ⟨q, g, -, h, hcg⟩
    · rw [h]; exact ⟨hn, fun m hm => (step_cg_mem upd p _ _ e m).1 (hs m hm)⟩
    · rw [h, hcg]
      have := hupd _ (_ ∪ g) hn (fun m hm => Finset.mem_union_left _ (hs m hm))
      exact ⟨this.2.1, fun m hm => (this.2.2 m).1 hm⟩

/-- `promote` only grows by appending. -/
lemma promote_mono {p : P} {t t' : ℕ} (h : t ≤ t') :
    ((alg upd).st r p t).promote <+: ((alg upd).st r p t').promote :=
  Algorithm.st_rel_of_step r (fun _ (a b : State P M) => a.promote <+: b.promote)
    (fun _ _ => List.prefix_refl _) (fun _ _ _ _ h1 h2 => h1.trans h2) (fun t p _ e _ _ => by
      rcases step_promote upd p (r.H p t) _ e with h | ⟨q, g, -, h, -⟩
      · rw [h]
      · rw [h]
        obtain ⟨hn, hs⟩ := promote_inv hupd t p
        exact (hupd _ _ hn (fun m hm => Finset.mem_union_left _ (hs m hm))).1) p t t' h

/-- Promotions of the same sender are prefix-ordered by their counters. -/
lemma prefix_of_counter_le {t₁ t₂ s₁ s₂ n₁ n₂ : ℕ} {q : P} {l₁ l₂ : List M}
    (h₁ : ((alg upd).cfg r t₁).msg s₁ = some (q, .promote n₁ l₁))
    (h₂ : ((alg upd).cfg r t₂).msg s₂ = some (q, .promote n₂ l₂)) (hn : n₁ ≤ n₂) :
    l₁ <+: l₂ := by
  have hs := time_le_of_counter_le h₁ h₂ hn
  obtain ⟨-, -, rfl, -⟩ := msg_promote_spec h₁
  obtain ⟨-, -, rfl, -⟩ := msg_promote_spec h₂
  exact promote_mono hupd hs

/-- Once a message is in the final leader's `promote`, every correct process eventually stably
delivers it. -/
lemma eventually_in (hA : (alg upd).Admissible r) {p ℓ : P} (hp : r.F.Correct p)
    (hℓ : r.F.Correct ℓ) {T : ℕ} (hT : ∀ t ≥ T, ∀ q, r.F.Correct q → r.H q t = ℓ) {m : M}
    {s : ℕ} (hm : m ∈ ((alg upd).st r ℓ s).promote) :
    ∃ T', ∀ t ≥ T', m ∈ ((alg upd).st r p t).d := by
  obtain ⟨tg, htg, hg⟩ := exists_good hA hp hℓ hT
  obtain ⟨tℓ, htℓ, hσℓ⟩ := hA.ticks ℓ hℓ (max T s)
  have hmℓ := tick_msg (upd := upd) hσℓ (hT tℓ (by omega) ℓ hℓ)
  obtain ⟨t', hσ'⟩ := hA.delivery p hp (tℓ + 1) tℓ ℓ _ hmℓ
  obtain ⟨hlt', -⟩ := hA.recv_valid t' p ℓ tℓ hσ'
  have hm' := hmℓ
  rw [← Algorithm.msg_eq_succ r hlt'] at hm'
  have hn := (recv_promote hσ' hm' (hT t' (by omega) p hp)).1
  refine ⟨max tg (t' + 1), fun t ht => ?_⟩
  obtain ⟨s₀, hs₀⟩ := good_forever (fun t ht => hT t ht p hp) htg hg (show tg ≤ t by omega)
  have hle := hn.trans (last_mono (upd := upd) (r := r) (p := p) (q := ℓ) (show t' + 1 ≤ t by omega))
  exact (prefix_of_counter_le hupd hmℓ hs₀ hle).subset
    ((promote_mono hupd (show s ≤ tℓ by omega)).subset hm)

/-! ### The ETOB properties -/

/-- TOB-No-creation. -/
theorem noCreation : TOBNoCreation (tobHist upd r) := by
  intro p t m hm
  rcases d_inv (upd := upd) (r := r) t p with h | ⟨q, s₀, hs, h⟩
  · simp only [tobHist, h] at hm; simp at hm
  · simp only [tobHist, h] at hm
    have hm' := (promote_inv hupd s₀ q).2 m hm
    obtain ⟨q', t', ht', h'⟩ := cg_known s₀ q m hm'
    exact ⟨q', t', by omega, h'⟩

/-- TOB-No-duplication. -/
theorem noDup : TOBNoDup (tobHist upd r) := by
  intro p t
  rcases d_inv (upd := upd) (r := r) t p with h | ⟨q, s₀, -, h⟩
  · simp [tobHist, h]
  · simp only [tobHist, h]; exact (promote_inv hupd s₀ q).1

/-- TOB-Validity. -/
theorem validity (hA : (alg upd).Admissible r) (hΩ : r.H ∈ Omega P r.F) :
    TOBValidity r.F (tobHist upd r) := by
  intro p m t hp hb
  obtain ⟨ℓ, hℓ, T, hT⟩ := hΩ ⟨p, hp⟩
  have hm' : ((alg upd).cfg r (t + 1)).msg t =
      some (p, .update (insert m ((alg upd).st r p t).cg)) := by
    rw [(Algorithm.cfg_succ_of_event r t p _ _ hb (Algorithm.event_input _ m)).2.1]; rfl
  obtain ⟨t₁, hσ₁⟩ := hA.delivery ℓ hℓ (t + 1) t p _ hm'
  obtain ⟨hlt₁, -⟩ := hA.recv_valid t₁ ℓ p t hσ₁
  rw [← Algorithm.msg_eq_succ r hlt₁] at hm'
  have hin : m ∈ ((alg upd).st r ℓ (t₁ + 1)).promote := by
    rw [(Algorithm.cfg_succ_of_event r t₁ ℓ _ _ hσ₁ (Algorithm.event_recv hm')).1]
    obtain ⟨hn, hs⟩ := promote_inv hupd t₁ ℓ
    have := hupd _ (((alg upd).st r ℓ t₁).cg ∪ insert m ((alg upd).st r p t).cg) hn
      (fun x hx => Finset.mem_union_left _ (hs x hx))
    exact (this.2.2 m).2 (by simp)
  obtain ⟨T', hT'⟩ := eventually_in hupd hA hp hℓ hT hin
  exact ⟨max T' (t + 1), by omega, fun t'' ht'' => hT' t'' (by omega)⟩

/-- TOB-Agreement. -/
theorem agreement (hA : (alg upd).Admissible r) (hΩ : r.H ∈ Omega P r.F) :
    TOBAgreement r.F (tobHist upd r) := by
  rintro p q m hp hq ⟨t₀, ht₀⟩
  obtain ⟨ℓ, hℓ, T, hT⟩ := hΩ ⟨p, hp⟩
  obtain ⟨tg, htg, hg⟩ := exists_good hA hp hℓ hT
  obtain ⟨s₀, hs₀⟩ := good_forever (fun t ht => hT t ht p hp) htg hg (le_max_left tg t₀)
  obtain ⟨-, -, hl, -⟩ := msg_promote_spec hs₀
  have hm : m ∈ ((alg upd).st r ℓ s₀).promote := by
    rw [← hl]; exact ht₀ _ (le_max_right _ _)
  exact eventually_in hupd hA hq hℓ hT hm

omit hupd [DecidableEq M] in
lemma before_of_prefix {m₁ m₂ : M} {a b : List M} (ha : a.Nodup) (hab : a <+: b ∨ b <+: a)
    (h₁ : m₁ ∈ b) (h₂ : m₂ ∈ b) (h : Before m₁ m₂ a) : Before m₁ m₂ b := by
  rcases hab with hab | ⟨x, rfl⟩
  · exact h.trans hab.sublist
  · obtain ⟨l₁, l₂, heq, hl₁, hl₂⟩ := List.sublist_append_iff.1 h
    have hdis := List.disjoint_of_nodup_append ha
    rcases l₁ with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, l₁⟩⟩⟩
    · simp only [List.nil_append] at heq
      subst heq
      exact absurd (hl₂.subset (by simp)) (hdis h₁)
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact absurd (hl₂.subset (by simp)) (hdis h₂)
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      obtain ⟨rfl, rfl, rfl, -⟩ := heq
      exact hl₁
    · simp at heq

/-- Outputs that are promotions of the same process are prefix-ordered by their counters. -/
lemma good_prefix {p q ℓ : P} {t t' : ℕ} (h₁ : Good upd r p ℓ t) (h₂ : Good upd r q ℓ t')
    (hle : ((alg upd).st r p t).last ℓ ≤ ((alg upd).st r q t').last ℓ) :
    ((alg upd).st r p t).d <+: ((alg upd).st r q t').d := by
  obtain ⟨s₁, h₁⟩ := h₁
  obtain ⟨s₂, h₂⟩ := h₂
  exact prefix_of_counter_le hupd h₁ h₂ hle

/-- ETOB-Stability and ETOB-Total-order from some time `τ` on. -/
theorem eventual [Finite P] (hA : (alg upd).Admissible r) (hΩ : r.H ∈ Omega P r.F) :
    ∃ τ, ETOBStability r.F (tobHist upd r) τ ∧ ETOBTotalOrder r.F (tobHist upd r) τ := by
  classical
  have := Fintype.ofFinite P
  by_cases hc : ∃ c, r.F.Correct c
  · obtain ⟨ℓ, hℓ, T, hT⟩ := hΩ hc
    have hex : ∀ p, r.F.Correct p → ∃ t ≥ T, Good upd r p ℓ t :=
      fun p hp => exists_good hA hp hℓ hT
    let τp : P → ℕ := fun p => if hp : r.F.Correct p then (hex p hp).choose else 0
    have hgood : ∀ p, r.F.Correct p → ∀ t ≥ Finset.univ.sup τp, Good upd r p ℓ t := by
      intro p hp t ht
      have h1 : τp p ≤ Finset.univ.sup τp := Finset.le_sup (Finset.mem_univ p)
      have h1' : τp p = (hex p hp).choose := by simp only [τp, hp, ↓reduceDIte]
      obtain ⟨h2, h3⟩ := (hex p hp).choose_spec
      exact good_forever (fun t ht => hT t ht p hp) h2 h3 (by omega)
    have hcmp := fun p q t t' => good_prefix hupd (r := r) (p := p) (q := q) (ℓ := ℓ) (t := t) (t' := t')
    refine ⟨Finset.univ.sup τp, ?_, ?_⟩
    · intro p hp t₁ t₂ ht₁ ht₂
      exact hcmp p p t₁ t₂ (hgood p hp t₁ ht₁) (hgood p hp t₂ (by omega)) (last_mono ht₂)
    · intro p q hp hq t ht m₁ m₂ h₁ h₂ hb
      have hab : ((alg upd).st r p t).d <+: ((alg upd).st r q t).d ∨
          ((alg upd).st r q t).d <+: ((alg upd).st r p t).d := by
        rcases le_total (((alg upd).st r p t).last ℓ) (((alg upd).st r q t).last ℓ) with h | h
        · exact Or.inl (hcmp p q t t (hgood p hp t ht) (hgood q hq t ht) h)
        · exact Or.inr (hcmp q p t t (hgood q hq t ht) (hgood p hp t ht) h)
      exact before_of_prefix (noDup hupd p t) hab h₁ h₂ hb
  · exact ⟨0, fun p hp => absurd ⟨p, hp⟩ hc, fun p _ hp => absurd ⟨p, hp⟩ hc⟩

omit hupd in
/-- **Lemma 3 of [DGKPS15], repaired (sequence numbers on promotions).** In every environment
(every failure pattern), with finitely many processes, the repaired Algorithm 5 implements
eventual total order broadcast using `Ω`: every admissible run satisfies ETOB, for every
implementation `upd` of `UpdatePromote`. (The paper's assumption that broadcast messages are
distinct is not needed.) -/
theorem lemma_3_fixed [Finite P] (upd : List M → Finset M → List M) (hupd : UpdValid upd)
    (r : Run P P M) (hΩ : r.H ∈ Omega P r.F) (hA : (alg upd).Admissible r) :
    ETOB r.F (tobHist upd r) :=
  ⟨validity hupd hA hΩ, noCreation hupd, noDup hupd, agreement hupd hA hΩ, eventual hupd hA hΩ⟩

/-! ### A stable leader from the start gives total order broadcast

The paper also claims (§5) that Algorithm 5 implements TOB (stability and total order from time
`0`) if `Ω` outputs the same leader at all processes from the very beginning; the counterexample
of `ETOBAlgorithm.lean` refutes this for the original algorithm. With the repair, it holds. -/

omit hupd in
lemma init_or_good {p ℓ : P} (hH : ∀ t, r.H p t = ℓ) : ∀ t,
    (((alg upd).st r p t).d = [] ∧ ((alg upd).st r p t).last ℓ = 0) ∨ Good upd r p ℓ t := by
  intro t
  induction t with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ t ih =>
    rcases ih with ⟨hd, hl⟩ | hg
    · rcases st_succ_cases r t p with h | ⟨c, e, hσ, he, h⟩
      · rw [h]; exact Or.inl ⟨hd, hl⟩
      · rcases step_last upd p (r.H p t) _ e with ⟨hd', hl'⟩ | ⟨n, l, rfl, hn, -, -⟩
        · rw [h, hd', hl']; exact Or.inl ⟨hd, hl⟩
        · obtain ⟨s₀, rfl, hm⟩ := Algorithm.event_eq_recv he
          have := (recv_promote hσ hm rfl).2 hn
          rw [hH] at this
          exact Or.inr this
    · exact Or.inr (good_step hg (hH t))

/-- With the repair, if `Ω` outputs the same process `ℓ` at all correct processes from the very
beginning, then TOB-Stability and TOB-Total-order hold (from time `0`), as claimed in §5 of
[DGKPS15] (that claim is false for the original Algorithm 5: see `Alg5.lemma_3_false`). -/
theorem tob_of_const_leader {ℓ : P} (hH : ∀ p t, r.F.Correct p → r.H p t = ℓ) :
    ETOBStability r.F (tobHist upd r) 0 ∧ ETOBTotalOrder r.F (tobHist upd r) 0 := by
  constructor
  · intro p hp t₁ t₂ _ ht
    rcases init_or_good (upd := upd) (fun t => hH p t hp) t₁ with ⟨hd, -⟩ | hg
    · simp only [tobHist, hd]; exact List.nil_prefix
    · exact good_prefix hupd hg (good_forever (fun t _ => hH p t hp) (Nat.zero_le _) hg ht)
        (last_mono ht)
  · intro p q hp hq t _ m₁ m₂ h₁ h₂ hb
    rcases init_or_good (upd := upd) (fun t => hH p t hp) t with ⟨hd, -⟩ | hgp
    · simp only [tobHist, hd] at hb; exact absurd (hb.subset (List.mem_cons_self ..)) (by simp)
    rcases init_or_good (upd := upd) (fun t => hH q t hq) t with ⟨hd, -⟩ | hgq
    · simp only [tobHist, hd] at h₁; simp at h₁
    have hab : ((alg upd).st r p t).d <+: ((alg upd).st r q t).d ∨
        ((alg upd).st r q t).d <+: ((alg upd).st r p t).d := by
      rcases le_total (((alg upd).st r p t).last ℓ) (((alg upd).st r q t).last ℓ) with h | h
      · exact Or.inl (good_prefix hupd hgp hgq h)
      · exact Or.inr (good_prefix hupd hgq hgp h)
    exact before_of_prefix (noDup hupd p t) hab h₁ h₂ hb

end Alg5Fixed

end Podc.WeakestFDEventualConsistency
