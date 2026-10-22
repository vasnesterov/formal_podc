import Papers.PODC2019.CRDTReplication.Statements

/-!
# Step lemmas for Algorithm 2

Every step of `alg V QS` either leaves the local states and the sent messages unchanged
(`drop`, `crash`, `skip`), or is a local transition `Trans` of one process `p`: the local state of
`p` changes from `C.loc p` to `l`, the messages `out` are sent, and the label `ℓ` is appended to
the history.
-/

set_option linter.unusedSectionVars false

namespace Podc.CRDTReplication

open Cslib.SharedMemory Cslib.AsyncMP

variable {P : Type} [Fintype P] [DecidableEq P] {D : CRDT}
variable {V : Variant D} {QS : Finset (Finset P)}

/-- The local transitions of process `p` (from local state `l₀` to `l`, sending `out`, with
history label `ℓ`); `sent` is the set of messages sent so far. -/
inductive Trans (V : Variant D) (QS : Finset (Finset P)) (sent : Multiset (P × P × Msg P D))
    (p : P) (l₀ : Loc P D) : Loc P D → Multiset (P × Msg P D) → Option (Label P D.spec) → Prop
  | inv {o l out} : invokeStep p o l₀ = some (l, out) → Trans V QS sent p l₀ l out (some (.inv p o))
  | internal {a l out r} : internalStep V QS p a l₀ = some (l, out, r) →
      Trans V QS sent p l₀ l out (r.map (Label.ret p))
  | recv {src m} : (src, p, m) ∈ sent →
      Trans V QS sent p l₀ (receiveStep V p src m l₀).1 (receiveStep V p src m l₀).2 none

/-- Classification of the steps of Algorithm 2. -/
lemma step_cases {C C' : Config P (Loc P D) (Msg P D)} {st : Step P D.spec (Msg P D) Act}
    {ℓ : Option (Label P D.spec)} (hnet : ∀ x ∈ C.net, x ∈ C.sent)
    (h : (alg V QS).step C st = some (C', ℓ)) :
    (C'.loc = C.loc ∧ C'.sent = C.sent ∧ ℓ = none ∧ ∀ x ∈ C'.net, x ∈ C.net) ∨
    ∃ p l out, Trans V QS C.sent p (C.loc p) l out ℓ ∧ C'.loc = Function.update C.loc p l ∧
      C'.sent = C.sent + outMsgs p out ∧ ∀ x ∈ C'.net, x ∈ C.net ∨ x ∈ outMsgs p out := by
  cases st with
  | inv p o =>
    simp only [Protocol.step, alg] at h
    split_ifs at h
    obtain ⟨⟨l, out⟩, h1, hx⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
    refine Or.inr ⟨p, l, out, .inv h1, rfl, rfl, fun x hx => ?_⟩
    simpa [Config.apply] using hx
  | internal p a =>
    simp only [Protocol.step, alg] at h
    split_ifs at h
    obtain ⟨⟨l, out, r⟩, h1, hx⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
    refine Or.inr ⟨p, l, out, .internal h1, rfl, rfl, fun x hx => ?_⟩
    simpa [Config.apply] using hx
  | recv src dst m =>
    simp only [Protocol.step, alg] at h
    split_ifs at h with hc
    push Not at hc
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine Or.inr ⟨dst, _, _, .recv (hnet _ hc.2), rfl, rfl, fun x hx => ?_⟩
    simp only [Config.apply, Multiset.mem_add] at hx
    exact hx.imp_left (Multiset.mem_of_mem_erase)
  | drop src dst m =>
    simp only [Protocol.step] at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl, rfl, fun x hx => Multiset.mem_of_mem_erase hx⟩
  | crash p =>
    simp only [Protocol.step] at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl, rfl, fun x hx => hx⟩
  | skip =>
    simp only [Protocol.step, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl, rfl, fun x hx => hx⟩

/-- In-transit messages have been sent. -/
lemma net_sub_sent {C : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)}
    (hr : (alg V QS).Reach C h) : ∀ x ∈ C.net, x ∈ C.sent := by
  induction hr with
  | init => simp [Protocol.initCfg]
  | step hr hs ih =>
    rcases step_cases ih hs with ⟨-, hsent, -, hn⟩ | ⟨p, l, out, -, -, hsent, hn⟩
    · rw [hsent]; exact fun x hx => ih x (hn x hx)
    · rw [hsent]; intro x hx
      rcases hn x hx with hx | hx
      · exact Multiset.mem_add.2 (Or.inl (ih x hx))
      · exact Multiset.mem_add.2 (Or.inr hx)

/-- Steps of a reachable configuration. -/
lemma reach_step_cases {C C' : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)}
    {st : Step P D.spec (Msg P D) Act} {ℓ : Option (Label P D.spec)}
    (hr : (alg V QS).Reach C h) (hs : (alg V QS).step C st = some (C', ℓ)) :
    (C'.loc = C.loc ∧ C'.sent = C.sent ∧ ℓ = none) ∨
    ∃ p l out, Trans V QS C.sent p (C.loc p) l out ℓ ∧ C'.loc = Function.update C.loc p l ∧
      C'.sent = C.sent + outMsgs p out := by
  rcases step_cases (net_sub_sent hr) hs with ⟨h1, h2, h3, -⟩ | ⟨p, l, out, h1, h2, h3, -⟩
  · exact Or.inl ⟨h1, h2, h3⟩
  · exact Or.inr ⟨p, l, out, h1, h2, h3⟩

/-! ## Sent messages -/

lemma mem_outMsgs {p : P} {out : Multiset (P × Msg P D)} {x : P × P × Msg P D} :
    x ∈ outMsgs p out ↔ x.1 = p ∧ (x.2.1, x.2.2) ∈ out := by
  obtain ⟨a, b, c⟩ := x
  simp only [outMsgs, Multiset.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨b', c'⟩, h, rfl, rfl, rfl⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨_, h, rfl, rfl, rfl⟩

@[simp] lemma mem_toAll {m m' : Msg P D} {a : P} : (a, m') ∈ toAll m ↔ m' = m := by
  simp [toAll, eq_comm]

@[simp] lemma mem_toOthers {p : P} {m m' : Msg P D} {a : P} :
    (a, m') ∈ toOthers p m ↔ a ≠ p ∧ m' = m := by
  simp [toOthers, eq_comm]

end Podc.CRDTReplication

namespace Podc.CRDTReplication

open Cslib.SharedMemory Cslib.AsyncMP

variable {P : Type} [Fintype P] [DecidableEq P] {D : CRDT}
variable {V : Variant D} {QS : Finset (Finset P)}

/-- Messages sent by acceptors (`ACK`, `VOTED`). -/
def Msg.IsAcc : Msg P D → Prop
  | .ack .. => True
  | .voted .. => True
  | _ => False

/-- The acceptor part of a local transition: either the acceptor variables only grow and no
acceptor message is sent, or an `ACK` is sent (accepted `PREPARE`), or a `VOTED` is sent. -/
lemma trans_acc {sent : Multiset (P × P × Msg P D)} {p : P} {l₀ l : Loc P D}
    {out : Multiset (P × Msg P D)} {ℓ : Option (Label P D.spec)}
    (htr : Trans V QS sent p l₀ l out ℓ) :
    (l.rnr = l₀.rnr ∧ l₀.s ≤ l.s ∧ (l.rid = l₀.rid ∨ l.rid = none) ∧ ∀ x ∈ out, ¬ x.2.IsAcc) ∨
    (∃ src i n s', (src, p, Msg.prepare i n s') ∈ sent ∧ l₀.rnr < n.getD (l₀.rnr + 1) ∧
      l.s = l₀.s ⊔ s' ∧ l.rnr = n.getD (l₀.rnr + 1) ∧ l.rid = some i ∧
      out = {(src, Msg.ack (n.getD (l₀.rnr + 1)) i (l₀.s ⊔ s'))}) ∨
    (∃ src n i s', (src, p, Msg.vote n i s') ∈ sent ∧ l₀.rnr = n ∧ l₀.rid = some i ∧
      (V.fix = true → l₀.s ≤ s') ∧ l.s = l₀.s ⊔ s' ∧ l.rnr = l₀.rnr ∧ l.rid = l₀.rid ∧
      out = {(src, Msg.voted n i s')}) := by
  cases htr with
  | inv h =>
    left
    rename_i o
    unfold invokeStep at h
    split at h
    · cases o with
      | upd u =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, D.le_app _ _, Or.inr rfl, ?_⟩
        intro x hx; obtain ⟨a, m⟩ := x
        rw [mem_toOthers] at hx; rw [hx.2]; simp [Msg.IsAcc]
      | qry q =>
        simp only [startAttempt, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, le_rfl, Or.inl rfl, ?_⟩
        intro x hx; obtain ⟨a, m⟩ := x
        rw [mem_toAll] at hx; rw [hx]; simp [Msg.IsAcc]
    · simp at h
  | internal h =>
    left
    unfold internalStep at h
    split at h <;> (try split_ifs at h) <;>
      simp only [startAttempt, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
      (try obtain ⟨rfl, rfl, -⟩ := h) <;>
      refine ⟨rfl, le_rfl, Or.inl rfl, ?_⟩ <;> intro x hx <;> obtain ⟨a, m⟩ := x <;>
      simp_all [Msg.IsAcc]
  | recv hm =>
    rename_i src m
    cases m with
    | merge k s' =>
      left
      refine ⟨rfl, le_sup_left, Or.inr rfl, ?_⟩
      intro x hx; rw [show (receiveStep V p src (.merge k s') l₀).2 = {(src, .merged k)} from rfl,
        Multiset.mem_singleton] at hx; subst hx; simp [Msg.IsAcc]
    | prepare i n s' =>
      simp only [receiveStep]
      split_ifs with hc
      · right; left; exact ⟨src, i, n, s', hm, hc, rfl, rfl, rfl, rfl⟩
      · left; exact ⟨rfl, le_sup_left, Or.inl rfl, by simp⟩
    | vote n i s' =>
      simp only [receiveStep]
      split_ifs with hc
      · right; right; exact ⟨src, n, i, s', hm, hc.1, hc.2.1, hc.2.2, rfl, rfl, rfl, rfl⟩
      · left; exact ⟨rfl, le_sup_left, Or.inl rfl, by simp⟩
    | merged k =>
      left; simp only [receiveStep]; split <;> (try split_ifs) <;> exact ⟨rfl, le_rfl, Or.inl rfl, by simp⟩
    | ack n i s' =>
      left; simp only [receiveStep]; split <;> (try split_ifs) <;> exact ⟨rfl, le_rfl, Or.inl rfl, by simp⟩
    | voted n i s' =>
      left; simp only [receiveStep]; split <;> (try split_ifs) <;> exact ⟨rfl, le_rfl, Or.inl rfl, by simp⟩

end Podc.CRDTReplication
