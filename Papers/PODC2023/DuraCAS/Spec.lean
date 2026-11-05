import Papers.PODC2023.DuraCAS.Model

/-!
# Writable CAS: sequential specification, durable linearizability, detectability

* `seqStep`: the sequential specification of (a family `K` of) writable CAS objects
  (`READ` returns the value, `CAS(old, new)` succeeds iff the value is `old`, `WRITE` sets the value
  and returns `ack = true`).
* `DurLin H L` (durable linearizability, Izraelevitz et al. / Attiya et al. for individual crashes):
  `L` lists distinct invoked operations; every operation that returned is in `L` with the response
  the sequential specification gives it at its position; if an operation *ended* (returned, or its
  `RECOVER` completed) before another one was invoked, and both are in `L`, they are in this order.
  A crashed operation thus either is absent from `L` (no effect) or takes effect between its
  invocation and the completion of its recovery; a pending (not yet recovered) one may be placed
  anywhere after its invocation.
* `Detectable H L` (the two-property contract of Section 2 / the brief announcement): with `d₁`,
  `d₂` the values of `DETECT` just before the invocation and just after the end of an operation,
  `d₁ ≤ d₂`; if `d₂ > d₁` the operation took effect (is in `L`) with response `true` (= the second
  component `r₂` of `DETECT`); if `d₂ = d₁` and the operation was completed by `RECOVER`, it did not
  take effect (is not in `L`), so it is safe to repeat.
-/

namespace Podc.DuraCAS

variable {P K V : Type} [DecidableEq K] [DecidableEq V]

/-- Sequential specification of writable CAS objects (one value per object `k`). -/
def seqStep (σ : K → V) (k : K) : Op V → (K → V) × Resp V
  | .read => (σ, .val (σ k))
  | .cas old new => if σ k = old then (Function.update σ k new, .ok true) else (σ, .ok false)
  | .write v => (Function.update σ k v, .ok true)

/-- Run a sequence of operations `(id, k, op)` from state `σ`. -/
def runSeq (σ : K → V) : List (ℕ × K × Op V) → K → V
  | [] => σ
  | e :: L => runSeq (seqStep σ e.2.1 e.2.2).1 L

/-- Operation `id` was invoked as `op` on `k`. -/
def Invoked (H : List (Ev P K V)) (id : ℕ) (k : K) (op : Op V) : Prop :=
  ∃ p d, Ev.inv id p k op d ∈ H

/-- Event `e` ends operation `id`. -/
def Ev.Ends (id : ℕ) : Ev P K V → Prop
  | .ret i _ _ => i = id
  | .rdone i _ => i = id
  | _ => False

/-- Operation `a` ended before operation `b` was invoked. -/
def EndsBefore (H : List (Ev P K V)) (a b : ℕ) : Prop :=
  ∃ i j : ℕ, ∃ hi : i < H.length, ∃ hj : j < H.length, i < j ∧ H[i].Ends a ∧
    ∃ p k op d, H[j] = Ev.inv b p k op d

/-- Durable linearizability of the history `H` witnessed by `L` (initial values `init`). -/
structure DurLin (init : K → V) (H : List (Ev P K V)) (L : List (ℕ × K × Op V)) : Prop where
  nodup : (L.map Prod.fst).Nodup
  invoked : ∀ e ∈ L, Invoked H e.1 e.2.1 e.2.2
  complete : ∀ id r d, Ev.ret id r d ∈ H → id ∈ L.map Prod.fst
  resp : ∀ L₁ e L₂, L = L₁ ++ e :: L₂ → ∀ r d, Ev.ret e.1 r d ∈ H →
    (seqStep (runSeq init L₁) e.2.1 e.2.2).2 = r
  realTime : ∀ a b, EndsBefore H a.1 b.1 → a ∈ L → b ∈ L → a ≠ b → [a, b].Sublist L

/-- Detectability of the history `H` w.r.t. the linearization `L`. -/
structure Detectable (init : K → V) (H : List (Ev P K V)) (L : List (ℕ × K × Op V)) : Prop where
  mono_ret : ∀ id p k op d₁ r d₂, Ev.inv id p k op d₁ ∈ H → Ev.ret id r d₂ ∈ H → d₁ ≤ d₂
  mono_rdone : ∀ id p k op d₁ d₂, Ev.inv id p k op d₁ ∈ H → Ev.rdone id d₂ ∈ H → d₁ ≤ d₂
  /-- `d₂ > d₁`: the operation took effect, with response `true`. -/
  took_effect : ∀ id p k op d₁ d₂, Ev.inv id p k op d₁ ∈ H →
    (Ev.rdone id d₂ ∈ H ∨ ∃ r, Ev.ret id r d₂ ∈ H) → d₁ < d₂ →
    ∃ L₁ L₂, L = L₁ ++ (id, k, op) :: L₂ ∧ (seqStep (runSeq init L₁) k op).2 = .ok true
  /-- `d₂ = d₁` after a recovery: the operation did not take effect. -/
  no_effect : ∀ id p k op d, Ev.inv id p k op d ∈ H → Ev.rdone id d ∈ H → id ∉ L.map Prod.fst

/-- The history `H` is durably linearizable and detectable. -/
def DurLinDet (init : K → V) (H : List (Ev P K V)) : Prop :=
  ∃ L, DurLin init H L ∧ Detectable init H L

/-- Durable linearizability alone. -/
def DurLinearizable (init : K → V) (H : List (Ev P K V)) : Prop := ∃ L, DurLin init H L

/-- The value of object `k` after a sequence of operations is its initial value or the argument
of one of the `CAS`/`WRITE` operations on `k` in the sequence. -/
theorem runSeq_mem (σ : K → V) (L : List (ℕ × K × Op V)) (k : K) :
    runSeq σ L k = σ k ∨
      ∃ e ∈ L, e.2.1 = k ∧ ((∃ old, e.2.2 = .cas old (runSeq σ L k)) ∨
        e.2.2 = .write (runSeq σ L k)) := by
  induction L generalizing σ with
  | nil => left; rfl
  | cons e L ih =>
    obtain ⟨id, k', op⟩ := e
    simp only [runSeq]
    rcases ih (seqStep σ k' op).1 with h | ⟨e', he', hk, hop⟩
    · rw [h]
      cases op with
      | read => left; rfl
      | cas old new =>
        simp only [seqStep]
        split_ifs with h1
        · by_cases hk : k = k'
          · subst hk; right; exact ⟨_, List.mem_cons_self, rfl, Or.inl ⟨old, by simp⟩⟩
          · left; simp [Function.update_of_ne hk]
        · left; rfl
      | write v =>
        simp only [seqStep]
        by_cases hk : k = k'
        · subst hk; right; exact ⟨_, List.mem_cons_self, rfl, Or.inr (by simp)⟩
        · left; simp [Function.update_of_ne hk]
    · right; exact ⟨e', List.mem_cons_of_mem _ he', hk, hop⟩

/-- In a durably linearizable history, a `READ` of `k` returns the initial value of `k` or a value
proposed to `k` by some invoked `CAS`/`WRITE` on `k`. -/
theorem read_val_of_durLin {init : K → V} {H : List (Ev P K V)} (hH : DurLinearizable init H)
    {id : ℕ} {k : K} {v : V} {d : ℕ} (hinv : Invoked H id k .read) (hret : Ev.ret id (.val v) d ∈ H)
    (huniq : ∀ k' op', Invoked H id k' op' → k' = k ∧ op' = .read) :
    v = init k ∨ ∃ id' p' d', (∃ old, Ev.inv id' p' k (.cas old v) d' ∈ H) ∨
      Ev.inv id' p' k (.write v) d' ∈ H := by
  obtain ⟨L, hL⟩ := hH
  have hmem := hL.complete _ _ _ hret
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hmem
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem he
  have hr := hL.resp L₁ e L₂ hsplit _ _ hret
  obtain ⟨hk, hop⟩ := huniq _ _ (hL.invoked e he)
  obtain ⟨id0, k0, op0⟩ := e
  simp only at hk hop hr; subst hk hop
  simp only [seqStep, Resp.val.injEq] at hr
  rcases runSeq_mem init L₁ k0 with h | ⟨e', he', hk', hop'⟩
  · left; rw [← hr, h]
  · right
    have hinv' := hL.invoked e' (by rw [hsplit]; exact List.mem_append_left _ he')
    obtain ⟨p', d', hp'⟩ := hinv'
    rw [hk'] at hp'
    rcases hop' with ⟨old, hold⟩ | hw
    · rw [hold, hr] at hp'; exact ⟨_, p', d', Or.inl ⟨old, hp'⟩⟩
    · rw [hw, hr] at hp'; exact ⟨_, p', d', Or.inr hp'⟩

end Podc.DuraCAS
