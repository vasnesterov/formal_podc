import Mathlib

/-!
# Executions of a lock object with helping, and the safety properties (S1), (S2)

Section 2.2 of Aeini, Bencivenga, Giakkoupis, Woelfel, *Simple and Efficient Randomized
Wait-Free Locks* (PODC 2026).

An execution is recorded as the list of its *events* (`Ev`), one per step:

* `inv p d` — process `p` invokes `TryLock(d)` / `Lock(d)` (its first shared-memory step);
* `resp p d r` — the call responds (its last shared-memory step) with return value `r`
  (for a non-abortable `Lock` the value is always `true`);
* `exS d` — some `d.execute()` call is invoked;
* `exE d` — some `d.execute()` call responds;
* `tau` — any other step.

The *execution interval* of `d`'s thunk begins with the first `exS d` and ends with the first
`exE d` (or with the end of the execution).  `InInterval es d t` says that the event with index
`t` lies in it.

* `S1 es` — (S1) mutual exclusion: the execution intervals of distinct thunks are disjoint.
* `S2 es` — (S2): the execution interval of `d`'s thunk lies within a single call on `d`
  (there is an invocation `inv p d` before it and `p` does not respond before the interval
  ends), and a call returns `true` iff it responds after `d`'s thunk has been executed.

The second half of the file is a generic *bridge*: for a transition system with ghost flags
`started`/`done` and a "current call" map, three state invariants imply (S1) and (S2) for all
its executions (`s1_s2_of_invariants`).
-/

namespace Podc.RandomizedWaitFreeLocks

/-- Events of an execution of a lock object. -/
inductive Ev (P D : Type*) where
  | inv (p : P) (d : D)
  | resp (p : P) (d : D) (r : Bool)
  | exS (d : D)
  | exE (d : D)
  | tau
  deriving DecidableEq

variable {P D : Type*}

/-- The event with index `t` lies in the execution interval of `d`'s thunk. -/
def InInterval (es : List (Ev P D)) (d : D) (t : ℕ) : Prop :=
  t < es.length ∧ (∃ s ≤ t, es[s]? = some (.exS d)) ∧ ∀ e < t, es[e]? ≠ some (.exE d)

/-- `e` is a response of process `p`. -/
def IsRespOf (p : P) : Ev P D → Prop
  | .resp q _ _ => q = p
  | _ => False

/-- (S1) Mutual exclusion: execution intervals of distinct thunks are disjoint. -/
def S1 (es : List (Ev P D)) : Prop :=
  ∀ d₁ d₂ t, d₁ ≠ d₂ → InInterval es d₁ t → ¬ InInterval es d₂ t

/-- (S2) The execution interval of `d`'s thunk lies within a single call on `d`, and a call
returns `true` iff it responds after `d`'s thunk has been executed. -/
def S2 (es : List (Ev P D)) : Prop :=
  (∀ d t₀, InInterval es d t₀ → ∃ p i, es[i]? = some (.inv p d) ∧
      ∀ t, InInterval es d t → i < t ∧
        ∀ j, i < j → j ≤ t → ∀ e, es[j]? = some e → ¬ IsRespOf p e) ∧
  (∀ (j : ℕ) (p : P) (d : D) (r : Bool), es[j]? = some (Ev.resp p d r) → (r = true ↔ ∃ e < j, es[e]? = some (Ev.exE d)))

/-! ## Runs of a transition system -/

section Run

variable {Cfg Act : Type*} (init : Cfg) (step : Cfg → Act → Bool → Cfg × Ev P D)

/-- The configuration and the events after a list of (action, coin) pairs. -/
def run (xs : List (Act × Bool)) : Cfg × List (Ev P D) :=
  xs.foldl (fun ce x => ((step ce.1 x.1 x.2).1, ce.2 ++ [(step ce.1 x.1 x.2).2])) (init, [])

@[simp] lemma run_nil : run init step [] = (init, []) := rfl

lemma run_concat (xs : List (Act × Bool)) (x : Act × Bool) :
    run init step (xs ++ [x]) =
      ((step (run init step xs).1 x.1 x.2).1,
        (run init step xs).2 ++ [(step (run init step xs).1 x.1 x.2).2]) := by
  simp [run, List.foldl_append]

lemma run_length (xs : List (Act × Bool)) : (run init step xs).2.length = xs.length := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih => simp [run_concat, ih]

/-- Reachable configurations. -/
def Reachable (c : Cfg) : Prop := ∃ xs, (run init step xs).1 = c

lemma reachable_init : Reachable init step init := ⟨[], rfl⟩

lemma Reachable.of_step {c : Cfg} (h : Reachable init step c) (a : Act) (b : Bool) :
    Reachable init step (step c a b).1 := by
  obtain ⟨xs, rfl⟩ := h
  exact ⟨xs ++ [(a, b)], by simp [run_concat]⟩

/-- Induction principle for reachable configurations. -/
lemma Reachable.induction {Q : Cfg → Prop} (h0 : Q init)
    (hs : ∀ c a b, Reachable init step c → Q c → Q (step c a b).1) {c : Cfg}
    (h : Reachable init step c) : Q c := by
  obtain ⟨xs, rfl⟩ := h
  induction xs using List.reverseRecOn with
  | nil => simpa using h0
  | append_singleton xs x ih =>
    rw [run_concat]; exact hs _ _ _ ⟨xs, rfl⟩ ih

/-- Prefix configurations of a run. -/
lemma run_take_succ (xs : List (Act × Bool)) (t : ℕ) (ht : t < xs.length) :
    (run init step (xs.take (t + 1))).1 =
      (step (run init step (xs.take t)).1 xs[t].1 xs[t].2).1 ∧
    (run init step xs).2[t]? = some (step (run init step (xs.take t)).1 xs[t].1 xs[t].2).2 := by
  have htake : xs.take (t + 1) = xs.take t ++ [xs[t]] := by
    rw [List.take_succ, List.getElem?_eq_getElem ht]; rfl
  refine ⟨by rw [htake, run_concat], ?_⟩
  have hsplit : xs = xs.take (t + 1) ++ xs.drop (t + 1) := (List.take_append_drop _ _).symm
  have hpre : ∀ ys zs : List (Act × Bool),
      (run init step ys).2 <+: (run init step (ys ++ zs)).2 := by
    intro ys zs
    induction zs using List.reverseRecOn with
    | nil => simp
    | append_singleton zs z ih =>
      rw [← List.append_assoc, run_concat]
      exact ih.trans (List.prefix_append _ _)
  have h1 := hpre (xs.take (t + 1)) (xs.drop (t + 1))
  rw [← hsplit] at h1
  obtain ⟨u, hu⟩ := h1
  rw [← hu, List.getElem?_append_left (by rw [run_length]; simp; omega)]
  rw [htake, run_concat]
  simp [run_length, ht.le]

end Run

/-! ## The bridge from state invariants to (S1), (S2) -/

section Bridge

variable {Cfg Act : Type*} (init : Cfg) (step : Cfg → Act → Bool → Cfg × Ev P D)

/-- Ghost observations of a lock system and their coherence with the events of the steps. -/
structure Coherent (started done : Cfg → D → Prop) (call : Cfg → P → Option D)
    (callIdx : Cfg → P → ℕ) (clock : Cfg → ℕ) : Prop where
  clock_init : clock init = 0
  clock_step : ∀ c a b, Reachable init step c → clock (step c a b).1 = clock c + 1
  started_init : ∀ d, ¬ started init d
  started_step : ∀ c a b d, Reachable init step c →
    (started (step c a b).1 d ↔ started c d ∨ (step c a b).2 = .exS d)
  done_init : ∀ d, ¬ done init d
  done_step : ∀ c a b d, Reachable init step c →
    (done (step c a b).1 d ↔ done c d ∨ (step c a b).2 = .exE d)
  call_init : ∀ p, call init p = none
  call_inv : ∀ c a b p d, Reachable init step c → (step c a b).2 = .inv p d →
    call c p = none ∧ call (step c a b).1 p = some d ∧ callIdx (step c a b).1 p = clock c
  call_resp : ∀ c a b p d r, Reachable init step c → (step c a b).2 = .resp p d r →
    call c p = some d ∧ call (step c a b).1 p = none ∧ (r = true ↔ done c d)
  call_other : ∀ c a b p, Reachable init step c → (∀ d, (step c a b).2 ≠ .inv p d) →
    (∀ d r, (step c a b).2 ≠ .resp p d r) →
    call (step c a b).1 p = call c p ∧ callIdx (step c a b).1 p = callIdx c p

variable {init step} {started done : Cfg → D → Prop} {call : Cfg → P → Option D}
  {callIdx : Cfg → P → ℕ} {clock : Cfg → ℕ}

section Lemmas

variable (H : Coherent init step started done call callIdx clock)
include H

lemma Coherent.clock_run (xs : List (Act × Bool)) : clock (run init step xs).1 = xs.length := by
  induction xs using List.reverseRecOn with
  | nil => simpa using H.clock_init
  | append_singleton xs x ih =>
    rw [run_concat, H.clock_step _ _ _ ⟨xs, rfl⟩, ih]; simp

lemma Coherent.started_run (xs : List (Act × Bool)) (t : ℕ) (ht : t ≤ xs.length) (d : D) :
    started (run init step (xs.take t)).1 d ↔ ∃ s < t, (run init step xs).2[s]? = some (.exS d) := by
  induction t with
  | zero => simpa using H.started_init d
  | succ t ih =>
    obtain ⟨h1, h2⟩ := run_take_succ init step xs t (by omega)
    rw [h1, H.started_step _ _ _ _ ⟨_, rfl⟩, ih (by omega)]
    constructor
    · rintro (⟨s, hs, h⟩ | h)
      · exact ⟨s, by omega, h⟩
      · exact ⟨t, by omega, by rw [h2, h]⟩
    · rintro ⟨s, hs, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · exact Or.inl ⟨s, hs, h⟩
      · rw [h2] at h; exact Or.inr (Option.some_injective _ h)

lemma Coherent.done_run (xs : List (Act × Bool)) (t : ℕ) (ht : t ≤ xs.length) (d : D) :
    done (run init step (xs.take t)).1 d ↔ ∃ s < t, (run init step xs).2[s]? = some (.exE d) := by
  induction t with
  | zero => simpa using H.done_init d
  | succ t ih =>
    obtain ⟨h1, h2⟩ := run_take_succ init step xs t (by omega)
    rw [h1, H.done_step _ _ _ _ ⟨_, rfl⟩, ih (by omega)]
    constructor
    · rintro (⟨s, hs, h⟩ | h)
      · exact ⟨s, by omega, h⟩
      · exact ⟨t, by omega, by rw [h2, h]⟩
    · rintro ⟨s, hs, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · exact Or.inl ⟨s, hs, h⟩
      · rw [h2] at h; exact Or.inr (Option.some_injective _ h)

/-- A pending call was invoked at index `callIdx` and has not responded since. -/
lemma Coherent.call_run (xs : List (Act × Bool)) (u : ℕ) (hu : u ≤ xs.length) (p : P) (d : D)
    (hc : call (run init step (xs.take u)).1 p = some d) :
    callIdx (run init step (xs.take u)).1 p < u ∧
    (run init step xs).2[callIdx (run init step (xs.take u)).1 p]? = some (.inv p d) ∧
    ∀ j, callIdx (run init step (xs.take u)).1 p < j → j < u →
      ∀ e, (run init step xs).2[j]? = some e → ¬ IsRespOf p e := by
  induction u generalizing d with
  | zero => simp [H.call_init] at hc
  | succ u ih =>
    obtain ⟨h1, h2⟩ := run_take_succ init step xs u (by omega)
    have hR : Reachable init step (run init step (xs.take u)).1 := ⟨_, rfl⟩
    set c := (run init step (xs.take u)).1
    set ev := (step c xs[u].1 xs[u].2).2 with hev
    rw [h1] at hc ⊢
    by_cases hinv : ∃ d', ev = .inv p d'
    · obtain ⟨d', hd'⟩ := hinv
      obtain ⟨-, hc', hidx⟩ := H.call_inv _ _ _ _ _ hR hd'
      rw [hc'] at hc; cases hc
      have hclk : clock c = u := by
        simp only [c]; rw [H.clock_run]; simp; omega
      rw [hidx, hclk]
      refine ⟨by omega, by rw [h2, hd'], fun j hj1 hj2 => by omega⟩
    by_cases hresp : ∃ d' r, ev = .resp p d' r
    · obtain ⟨d', r, hd'⟩ := hresp
      have := (H.call_resp _ _ _ _ _ _ hR hd').2.1
      rw [this] at hc; cases hc
    push_neg at hinv hresp
    obtain ⟨hcall, hidx⟩ := H.call_other _ _ _ _ hR hinv hresp
    rw [hcall] at hc
    obtain ⟨ih1, ih2, ih3⟩ := ih (by omega) d hc
    rw [hidx]
    refine ⟨by omega, ih2, fun j hj1 hj2 e he => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj2 with hj2 | rfl
    · exact ih3 j hj1 hj2 e he
    · rw [h2] at he; obtain rfl := Option.some_injective _ he
      intro hr
      cases hev' : ev with
      | resp q d' r =>
        rw [hev'] at hr; simp only [IsRespOf] at hr; subst hr
        exact hresp d' r hev'
      | _ => rw [hev'] at hr; exact hr

end Lemmas

/-- **Bridge.** Three invariants of reachable configurations imply (S1) and (S2):
mutual exclusion of *active* thunks (started and not done), every active thunk belongs to a
pending call, and a call responds only if its thunk is done or was never started. -/
theorem s1_s2_of_invariants (H : Coherent init step started done call callIdx clock)
    (hmutex : ∀ c, Reachable init step c → ∀ d₁ d₂, d₁ ≠ d₂ → started c d₁ → ¬ done c d₁ →
      started c d₂ → ¬ done c d₂ → False)
    (hcall : ∀ c, Reachable init step c → ∀ d, started c d → ¬ done c d → ∃ p, call c p = some d)
    (hresp : ∀ c a b p d r, Reachable init step c → (step c a b).2 = .resp p d r →
      started c d → done c d)
    (xs : List (Act × Bool)) :
    S1 (run init step xs).2 ∧ S2 (run init step xs).2 := by
  set es := (run init step xs).2 with hes
  have hlen : es.length = xs.length := run_length _ _ _
  -- `InInterval` in terms of configurations
  have key : ∀ d t, InInterval es d t ↔ t < xs.length ∧
      started (run init step (xs.take (t + 1))).1 d ∧ ¬ done (run init step (xs.take t)).1 d := by
    intro d t
    unfold InInterval
    rw [hlen]
    constructor
    · rintro ⟨ht, ⟨s, hs, h⟩, h2⟩
      refine ⟨ht, (H.started_run xs (t + 1) (by omega) d).2 ⟨s, by omega, h⟩, ?_⟩
      rw [H.done_run xs t (by omega)]
      rintro ⟨e, he, h'⟩; exact h2 e he h'
    · rintro ⟨ht, h1, h2⟩
      rw [H.started_run xs (t + 1) (by omega)] at h1
      rw [H.done_run xs t (by omega)] at h2
      obtain ⟨s, hs, h⟩ := h1
      exact ⟨ht, ⟨s, by omega, h⟩, fun e he h' => h2 ⟨e, he, h'⟩⟩
  -- the event at index `t`
  have hev : ∀ t (ht : t < xs.length), es[t]? =
      some (step (run init step (xs.take t)).1 xs[t].1 xs[t].2).2 :=
    fun t ht => (run_take_succ init step xs t ht).2
  have hcfg : ∀ t (ht : t < xs.length), (run init step (xs.take (t + 1))).1 =
      (step (run init step (xs.take t)).1 xs[t].1 xs[t].2).1 :=
    fun t ht => (run_take_succ init step xs t ht).1
  have hR : ∀ t, Reachable init step (run init step (xs.take t)).1 := fun t => ⟨_, rfl⟩
  -- active before the step if the step is the end event, after it otherwise
  have active : ∀ d t, InInterval es d t →
      (es[t]? ≠ some (.exE d) ∧ started (run init step (xs.take (t + 1))).1 d ∧
        ¬ done (run init step (xs.take (t + 1))).1 d) ∨
      (es[t]? = some (.exE d) ∧ started (run init step (xs.take t)).1 d ∧
        ¬ done (run init step (xs.take t)).1 d) := by
    intro d t hI
    obtain ⟨ht, h1, h2⟩ := (key d t).1 hI
    have hst := H.started_step _ xs[t].1 xs[t].2 d (hR t)
    have hdn := H.done_step _ xs[t].1 xs[t].2 d (hR t)
    rw [← hcfg t ht] at hst hdn
    by_cases hE : es[t]? = some (.exE d)
    · right
      refine ⟨hE, ?_, h2⟩
      rcases hst.1 h1 with h | h
      · exact h
      · rw [hev t ht, h] at hE; cases hE
    · left
      refine ⟨hE, h1, fun h => ?_⟩
      rcases hdn.1 h with h | h
      · exact h2 h
      · exact hE (by rw [hev t ht, h])
  refine ⟨?_, ?_, ?_⟩
  · -- (S1)
    intro d₁ d₂ t hne h₁ h₂
    have ht := ((key d₁ t).1 h₁).1
    rcases active d₁ t h₁ with ⟨hE₁, a₁, b₁⟩ | ⟨hE₁, a₁, b₁⟩ <;>
      rcases active d₂ t h₂ with ⟨hE₂, a₂, b₂⟩ | ⟨hE₂, a₂, b₂⟩
    · exact hmutex _ ⟨_, rfl⟩ d₁ d₂ hne a₁ b₁ a₂ b₂
    · -- step `t` ends `d₂`; `d₁` was already active before
      have hst := (H.started_step _ xs[t].1 xs[t].2 d₁ (hR t))
      rw [← hcfg t ht] at hst
      have hdn := (H.done_step _ xs[t].1 xs[t].2 d₁ (hR t))
      rw [← hcfg t ht] at hdn
      have hev' := hev t ht
      rw [hE₂] at hev'
      refine hmutex _ (hR t) d₁ d₂ hne ?_ (fun h => b₁ (hdn.2 (Or.inl h))) a₂ b₂
      rcases hst.1 a₁ with h | h
      · exact h
      · rw [h] at hev'; cases hev'
    · have hst := (H.started_step _ xs[t].1 xs[t].2 d₂ (hR t))
      rw [← hcfg t ht] at hst
      have hdn := (H.done_step _ xs[t].1 xs[t].2 d₂ (hR t))
      rw [← hcfg t ht] at hdn
      have hev' := hev t ht
      rw [hE₁] at hev'
      refine hmutex _ (hR t) d₁ d₂ hne a₁ b₁ ?_ (fun h => b₂ (hdn.2 (Or.inl h)))
      rcases hst.1 a₂ with h | h
      · exact h
      · rw [h] at hev'; cases hev'
    · rw [hE₁] at hE₂; cases hE₂; exact absurd rfl hne
  · -- (S2), first part
    intro d t₀ h₀
    -- the first start
    have hex : ∃ s : ℕ, es[s]? = some (Ev.exS d) := by
      obtain ⟨-, ⟨s, -, h⟩, -⟩ := h₀; exact ⟨s, h⟩
    classical
    let s₀ := Nat.find hex
    have hs₀ : es[s₀]? = some (.exS d) := Nat.find_spec hex
    have hs₀min : ∀ s < s₀, es[s]? ≠ some (.exS d) := fun s hs => Nat.find_min hex hs
    have hs₀len : s₀ < xs.length := by
      rw [← hlen]; by_contra h; push_neg at h; rw [List.getElem?_eq_none h] at hs₀; cases hs₀
    have hs₀le : ∀ t, InInterval es d t → s₀ ≤ t := by
      intro t ⟨_, ⟨s, hs, h⟩, _⟩; exact (Nat.find_min' hex h).trans hs
    have hnoE : ∀ e ≤ s₀, es[e]? ≠ some (.exE d) := by
      intro e he h
      rcases he.lt_or_eq with he | rfl
      · exact h₀.2.2 e (lt_of_lt_of_le he (hs₀le t₀ h₀)) h
      · rw [hs₀] at h; cases h
    have hact₀ : started (run init step (xs.take (s₀ + 1))).1 d ∧
        ¬ done (run init step (xs.take (s₀ + 1))).1 d := by
      refine ⟨(H.started_run xs _ (by omega) d).2 ⟨s₀, by omega, hs₀⟩, ?_⟩
      rw [H.done_run xs _ (by omega)]
      rintro ⟨e, he, h⟩; exact hnoE e (by omega) h
    obtain ⟨p, hp⟩ := hcall _ (hR _) d hact₀.1 hact₀.2
    set i := callIdx (run init step (xs.take (s₀ + 1))).1 p with hi
    -- the call persists while `d` is active
    have persist : ∀ u, s₀ + 1 ≤ u → u ≤ xs.length →
        ¬ done (run init step (xs.take u)).1 d →
        call (run init step (xs.take u)).1 p = some d ∧
          callIdx (run init step (xs.take u)).1 p = i := by
      intro u hu hulen
      induction u, hu using Nat.le_induction with
      | base => intro _; exact ⟨hp, rfl⟩
      | succ u hu ih =>
        intro hnd
        have hdn := H.done_step _ xs[u].1 xs[u].2 d (hR u)
        rw [← hcfg u (by omega)] at hdn
        have hnd' : ¬ done (run init step (xs.take u)).1 d := fun h => hnd (hdn.2 (Or.inl h))
        obtain ⟨ih1, ih2⟩ := ih (by omega) hnd'
        have hstu : started (run init step (xs.take u)).1 d :=
          (H.started_run xs u (by omega) d).2 ⟨s₀, by omega, hs₀⟩
        have hinv : ∀ d', (step (run init step (xs.take u)).1 xs[u].1 xs[u].2).2 ≠ .inv p d' := by
          intro d' h
          have := (H.call_inv _ _ _ _ _ (hR u) h).1
          rw [ih1] at this; cases this
        have hresp' : ∀ d' r,
            (step (run init step (xs.take u)).1 xs[u].1 xs[u].2).2 ≠ .resp p d' r := by
          intro d' r h
          have h1 := (H.call_resp _ _ _ _ _ _ (hR u) h).1
          rw [ih1] at h1; cases h1
          exact hnd' (hresp _ _ _ _ _ _ (hR u) h hstu)
        obtain ⟨h1, h2⟩ := H.call_other _ _ _ _ (hR u) hinv hresp'
        rw [hcfg u (by omega), h1, h2]
        exact ⟨ih1, ih2⟩
    obtain ⟨hi1, hi2, -⟩ := H.call_run xs (s₀ + 1) (by omega) p d hp
    rw [← hi] at hi1 hi2
    have his₀ : i < s₀ := by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi1 with h | h
      · exact h
      · rw [h, hs₀] at hi2; cases hi2
    refine ⟨p, i, hi2, fun t ht => ⟨lt_of_lt_of_le his₀ (hs₀le t ht), ?_⟩⟩
    have htlen := ((key d t).1 ht).1
    rcases active d t ht with ⟨hE, -, hnd⟩ | ⟨hE, -, hnd⟩
    · obtain ⟨hc, hidx⟩ := persist (t + 1) (by have := hs₀le t ht; omega) (by omega) hnd
      obtain ⟨-, -, h3⟩ := H.call_run xs (t + 1) (by omega) p d hc
      rw [hidx] at h3
      exact fun j hj1 hj2 => h3 j hj1 (by omega)
    · have hts : s₀ + 1 ≤ t := by
        rcases (hs₀le t ht).lt_or_eq with h | h
        · omega
        · rw [← h, hs₀] at hE; cases hE
      obtain ⟨hc, hidx⟩ := persist t hts (by omega) hnd
      obtain ⟨-, -, h3⟩ := H.call_run xs t (by omega) p d hc
      rw [hidx] at h3
      intro j hj1 hj2 e he
      rcases hj2.lt_or_eq with hj2 | rfl
      · exact h3 j hj1 hj2 e he
      · rw [hE] at he; cases he; exact id
  · -- (S2), second part
    intro j p d r hj
    have hjlen : j < xs.length := by
      rw [← hlen]; by_contra h; push_neg at h; rw [List.getElem?_eq_none h] at hj; cases hj
    rw [hev j hjlen] at hj
    have := (H.call_resp _ _ _ _ _ _ (hR j) (Option.some_injective _ hj)).2.2
    rw [this, H.done_run xs j (by omega)]

end Bridge

end Podc.RandomizedWaitFreeLocks
