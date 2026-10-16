import Podc.ContentOblivious.Splice

/-!
# Interface traces of ring intervals and splicing (§10, Observation 27, Lemma 28)

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026, Section 10.

Model: the oriented ring `oriented n` on `ZMod n` (`Port1 = true` of `v` is linked to
`Port0 = false` of `v + 1`), asynchronous, content-oblivious, deterministic algorithms (`Algo`),
adversarial scheduler. An execution is a list of deliveries (`ValidSteps`, `runSteps`).

The interval `I = (s, s+1, …, s+a-1)` has boundary edges `e_L = {s-1, s}` and
`e_R = {s+a-1, s+a}`; its *interface trace* `ringTrace n s a l` is the word over
`Σ = {Lin, Lout, Rin, Rout}` of the deliveries on these edges, in execution order:
* `Lin`: delivery at `s` of a pulse from `s-1` (port `(s, false)`),
* `Lout`: delivery at `s-1` of a pulse from `s` (port `(s-1, true)`),
* `Rin`: delivery at `s+a-1` of a pulse from `s+a` (port `(s+a-1, true)`),
* `Rout`: delivery at `s+a` of a pulse from `s+a-1` (port `(s+a, false)`).
-/

namespace Podc.ContentOblivious.Counting

open Podc.ContentOblivious Finset

/-- The alphabet `Σ = {Lin, Lout, Rin, Rout}` of interface traces. -/
inductive Letter
  | Lin
  | Lout
  | Rin
  | Rout
  deriving DecidableEq, Repr

open Letter

instance : Fintype Letter := ⟨{Lin, Lout, Rin, Rout}, fun x => by cases x <;> simp⟩

@[simp] lemma Letter.card : Fintype.card Letter = 4 := by decide

/-- The boundary labelling of the interval `(s, …, s+a-1)` of the ring of size `n`: the label of
the receiving port of a delivery on a boundary edge. -/
def ringLab (n : ℕ) (s : ZMod n) (a : ℕ) (p : ZMod n × Bool) : Option Letter :=
  if p = (s, false) then some Lin
  else if p = (s - 1, true) then some Lout
  else if p = (s + a - 1, true) then some Rin
  else if p = (s + a, false) then some Rout
  else none

/-- The interface trace `trace_E(I)` of the interval `I = (s, …, s+a-1)` in the execution `l`. -/
def ringTrace (n : ℕ) (s : ZMod n) (a : ℕ) (l : List (ZMod n × Bool)) : List Letter :=
  l.filterMap (ringLab n s a)

/-- `M(e)` for the edge `e = {u, u+1}`: the number of pulses delivered across it, in both
directions. -/
def edgeLoad {S : Type*} {n : ℕ} (c : Config (ZMod n) S) (u : ZMod n) : ℕ :=
  c.recvd (u, true) + c.recvd (u + 1, false)

/-! ### Offsets -/

section offsets

variable {n : ℕ} [NeZero n]

/-- The clockwise distance from `s` to `u`. -/
def ofs (s u : ZMod n) : ℕ := (u - s).val

lemma ofs_lt (s u : ZMod n) : ofs s u < n := ZMod.val_lt _

lemma eq_of_ofs {s u u' : ZMod n} (h : ofs s u = ofs s u') : u = u' := by
  have := ZMod.val_injective n h; simpa using this

omit [NeZero n] in
lemma ofs_add_nat (s : ZMod n) {k : ℕ} (hk : k < n) : ofs s (s + (k : ZMod n)) = k := by
  simp [ofs, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

lemma eq_add_ofs (s u : ZMod n) : u = s + ((ofs s u : ℕ) : ZMod n) := by simp [ofs]

lemma ofs_eq_iff {s u : ZMod n} {k : ℕ} (hk : k < n) : ofs s u = k ↔ u = s + (k : ZMod n) :=
  ⟨fun h => by rw [eq_add_ofs s u, h], fun h => by rw [h, ofs_add_nat s hk]⟩

lemma ofs_add_one (s u : ZMod n) :
    ofs s (u + 1) = if ofs s u + 1 = n then 0 else ofs s u + 1 := by
  have h1 : u + 1 = s + (((ofs s u + 1 : ℕ)) : ZMod n) := by
    conv_lhs => rw [eq_add_ofs s u]
    push_cast; ring
  have hlt := ofs_lt s u
  split_ifs with h
  · rw [h1, h, ZMod.natCast_self]; simp [ofs]
  · rw [h1, ofs_add_nat s (by omega)]

lemma ofs_sub_one (s u : ZMod n) :
    ofs s (u - 1) = if ofs s u = 0 then n - 1 else ofs s u - 1 := by
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hlt := ofs_lt s u
  split_ifs with h
  · rw [ofs_eq_iff (by omega)]
    rw [(ofs_eq_iff (by omega)).1 h]; push_cast [hn]; simp; ring
  · rw [ofs_eq_iff (by omega)]
    conv_lhs => rw [eq_add_ofs s u]
    push_cast [show 1 ≤ ofs s u by omega]; ring

omit [NeZero n] in
lemma ofs_self (s : ZMod n) : ofs s s = 0 := by simp [ofs]

lemma val_add_one' (v : ZMod n) : (v + 1).val = if v.val + 1 = n then 0 else v.val + 1 := by
  simpa [ofs] using ofs_add_one 0 v

lemma val_sub_one' (v : ZMod n) : (v - 1).val = if v.val = 0 then n - 1 else v.val - 1 := by
  simpa [ofs] using ofs_sub_one 0 v

lemma port_eq_iff (s : ZMod n) (p q : ZMod n × Bool) :
    p = q ↔ ofs s p.1 = ofs s q.1 ∧ p.2 = q.2 := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h1, h2⟩; exact Prod.ext (eq_of_ofs h1) h2

/-- The labelling in terms of offsets from `s`. -/
def offLab (n a : ℕ) (j : Bool) (k : ℕ) : Option Letter :=
  if j then (if k = n - 1 then some Lout else if k = a - 1 then some Rin else none)
  else (if k = 0 then some Lin else if k = a then some Rout else none)

lemma ringLab_eq {a : ℕ} (ha : 1 ≤ a) (han : a < n) (s u : ZMod n) (j : Bool) :
    ringLab n s a (u, j) = offLab n a j (ofs s u) := by
  have hlt := ofs_lt s u
  have e1 : (s, false) = (s + ((0 : ℕ) : ZMod n), false) := by simp
  have e2 : (s - 1, true) = (s + ((n - 1 : ℕ) : ZMod n), true) := by
    push_cast [show 1 ≤ n by omega]; simp; ring
  have e3 : (s + a - 1, true) = (s + ((a - 1 : ℕ) : ZMod n), true) := by
    rw [Nat.cast_sub ha, Nat.cast_one, add_sub_assoc]
  have e4 : (s + (a : ZMod n), false) = (s + ((a : ℕ) : ZMod n), false) := rfl
  unfold ringLab offLab
  rw [e1, e2, e3]
  simp only [Prod.mk.injEq, ← ofs_eq_iff (show 0 < n by omega),
    ← ofs_eq_iff (show n - 1 < n by omega),
    ← ofs_eq_iff (show a - 1 < n by omega), ← ofs_eq_iff han]
  cases j <;> simp

lemma offLab_eq_some {n a : ℕ} (ha : 1 ≤ a) (han : a < n) {j : Bool} {k : ℕ} {μ : Letter} :
    offLab n a j k = some μ ↔
      (μ = Lin ∧ j = false ∧ k = 0) ∨ (μ = Lout ∧ j = true ∧ k = n - 1) ∨
      (μ = Rin ∧ j = true ∧ k = a - 1) ∨ (μ = Rout ∧ j = false ∧ k = a) := by
  unfold offLab
  cases j <;> simp only [Bool.false_eq_true, ↓reduceIte, true_and, false_and] <;>
    split_ifs <;> simp <;> first | omega | (cases μ <;> simp <;> omega)

end offsets

/-! ### Splicing an oriented ring -/

section splice

/-- The original of a node of the spliced ring `R'`: the ring of size `n` with the nodes
`s+a, …, s+b-1` (that is, `I₂ \ I₁` for `I₁ = (s, …, s+a-1)`, `I₂ = (s, …, s+b-1)`) removed.
Node `k` of `R'` (`0 ≤ k < n - (b - a)`) is node `s + k` of `R` if `k < a`, and node
`s + k + (b - a)` otherwise. -/
def spliceEmb (n a b : ℕ) (s : ZMod n) (v : ZMod (n - (b - a))) : ZMod n :=
  s + ((if v.val < a then v.val else v.val + (b - a) : ℕ) : ZMod n)

/-- Owner of a boundary label: `Lin`, `Rin` are received inside the interval. -/
def ownL : Letter → Bool
  | Lin => true
  | Lout => false
  | Rin => true
  | Rout => false

variable {n a b : ℕ} [NeZero n] (ha : 1 ≤ a) (hab : a < b) (hbn : b < n) (s : ZMod n)

include ha hab hbn

omit [NeZero n] in
lemma ofs_spliceEmb (v : ZMod (n - (b - a))) :
    ofs s (spliceEmb n a b s v) = if v.val < a then v.val else v.val + (b - a) := by
  have : NeZero (n - (b - a)) := ⟨by omega⟩
  have := ZMod.val_lt v
  unfold spliceEmb
  rw [ofs_add_nat]
  split_ifs <;> omega

lemma exists_spliceEmb (β : Bool) (u : ZMod n) :
    (∃ v : ZMod (n - (b - a)), decide (v.val < a) = β ∧ spliceEmb n a b s v = u) ↔
      if β then ofs s u < a else b ≤ ofs s u := by
  have : NeZero (n - (b - a)) := ⟨by omega⟩
  have hu := ofs_lt s u
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [ofs_spliceEmb ha hab hbn]
    have := ZMod.val_lt v
    by_cases h : v.val < a <;> cases β <;> simp [h] at hv ⊢
    all_goals omega
  · intro h
    cases β
    · simp at h
      refine ⟨((ofs s u - (b - a) : ℕ) : ZMod (n - (b - a))), ?_, ?_⟩
      · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]; simp; omega
      · apply eq_of_ofs (s := s)
        rw [ofs_spliceEmb ha hab hbn, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
        split_ifs <;> omega
    · simp at h
      refine ⟨((ofs s u : ℕ) : ZMod (n - (b - a))), ?_, ?_⟩
      · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]; simpa using h
      · apply eq_of_ofs (s := s)
        rw [ofs_spliceEmb ha hab hbn, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
        simp [h]

/-- The splice of the ring of size `n` replacing `I₂ = (s, …, s+b-1)` by
`I₁ = (s, …, s+a-1)`: nodes `k < a` of `R'` come from the inside of `I₁`, the others from the
outside of `I₂`. -/
def ringSpliceData : SpliceData (oriented n) (oriented (n - (b - a))) Letter where
  side v := decide (v.val < a)
  f := spliceEmb n a b s
  lab β := ringLab n s (if β then a else b)
  own := ownL
  f_inj v w hs he := by
    have : NeZero (n - (b - a)) := ⟨by omega⟩
    have h := congrArg (ofs s) he
    rw [ofs_spliceEmb ha hab hbn, ofs_spliceEmb ha hab hbn] at h
    apply ZMod.val_injective
    by_cases hv : v.val < a <;> by_cases hw : w.val < a <;> simp [hv, hw] at hs h ⊢ <;> omega
  lab_inj β p q μ hp hq := by
    obtain ⟨u, j⟩ := p
    obtain ⟨u', j'⟩ := q
    have h1 : 1 ≤ (if β then a else b) := by split_ifs <;> omega
    have h2 : (if β then a else b) < n := by split_ifs <;> omega
    rw [ringLab_eq h1 h2, offLab_eq_some h1 h2] at hp hq
    rw [port_eq_iff s]
    simp only
    rcases hp with ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩ <;>
      rcases hq with ⟨hμ, rfl, hk'⟩ | ⟨hμ, rfl, hk'⟩ | ⟨hμ, rfl, hk'⟩ | ⟨hμ, rfl, hk'⟩ <;>
      (try cases hμ) <;> exact ⟨by omega, rfl⟩
  internal v j := by
    have : NeZero (n - (b - a)) := ⟨by omega⟩
    have hv := ZMod.val_lt v
    by_cases hva : v.val < a
    · simp only [hva, decide_true, ↓reduceIte]
      rw [ringLab_eq ha (by omega), ofs_spliceEmb ha hab hbn]
      cases j
      · simp only [oriented_peer_false, val_sub_one', offLab, hva, ↓reduceIte, Bool.false_eq_true,
          ↓reduceIte]
        split_ifs <;> simp <;> omega
      · simp only [oriented_peer_true, val_add_one', offLab, hva, ↓reduceIte]
        split_ifs <;> simp <;> omega
    · simp only [hva, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [ringLab_eq (by omega) hbn, ofs_spliceEmb ha hab hbn]
      cases j
      · simp only [oriented_peer_false, val_sub_one', offLab, hva, ↓reduceIte, Bool.false_eq_true]
        split_ifs <;> simp <;> omega
      · simp only [oriented_peer_true, val_add_one', offLab, hva, ↓reduceIte]
        split_ifs <;> simp <;> omega
  peer_int v j hs := by
    have : NeZero (n - (b - a)) := ⟨by omega⟩
    have hv := ZMod.val_lt v
    rw [port_eq_iff s]
    cases j
    · simp only [oriented_peer_false] at hs ⊢
      rw [ofs_sub_one, ofs_spliceEmb ha hab hbn, ofs_spliceEmb ha hab hbn, val_sub_one']
      simp only [val_sub_one'] at hs
      refine ⟨?_, trivial⟩
      by_cases hva : v.val < a <;> split_ifs at hs ⊢ <;> simp_all <;> omega
    · simp only [oriented_peer_true] at hs ⊢
      rw [ofs_add_one, ofs_spliceEmb ha hab hbn, ofs_spliceEmb ha hab hbn, val_add_one']
      simp only [val_add_one'] at hs
      refine ⟨?_, trivial⟩
      by_cases hva : v.val < a <;> split_ifs at hs ⊢ <;> simp_all <;> omega
  own_iff β p μ hp := by
    obtain ⟨u, j⟩ := p
    have h1 : 1 ≤ (if β then a else b) := by split_ifs <;> omega
    have h2 : (if β then a else b) < n := by split_ifs <;> omega
    rw [ringLab_eq h1 h2, offLab_eq_some h1 h2] at hp
    simp only
    rw [exists_spliceEmb ha hab hbn]
    rcases hp with ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩ <;>
      cases β <;> simp [ownL] at hk ⊢ <;> omega
  cross v j μ q hl ho hq := by
    have : NeZero (n - (b - a)) := ⟨by omega⟩
    have hv := ZMod.val_lt v
    obtain ⟨u, i⟩ := q
    rw [port_eq_iff s]
    by_cases hva : v.val < a
    · simp only [hva, decide_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true] at hl ho hq
      rw [ringLab_eq ha (by omega), offLab_eq_some ha (by omega), ofs_spliceEmb ha hab hbn] at hl
      rw [ringLab_eq (by omega) hbn, offLab_eq_some (by omega) hbn] at hq
      simp only [hva, ↓reduceIte] at hl
      rcases hl with ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩ <;>
        simp [ownL] at ho <;>
        rcases hq with ⟨hμ, rfl, hk'⟩ | ⟨hμ, rfl, hk'⟩ | ⟨hμ, rfl, hk'⟩ | ⟨hμ, rfl, hk'⟩ <;>
        (try cases hμ) <;>
        simp only [oriented_peer_false, oriented_peer_true, ofs_add_one, ofs_sub_one,
          ofs_spliceEmb ha hab hbn, val_add_one', val_sub_one', and_true] <;>
        split_ifs <;> omega
    · simp only [hva, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hl ho hq
      rw [ringLab_eq (by omega) hbn, offLab_eq_some (by omega) hbn, ofs_spliceEmb ha hab hbn] at hl
      rw [ringLab_eq ha (by omega), offLab_eq_some ha (by omega)] at hq
      simp only [hva, ↓reduceIte] at hl
      rcases hl with ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩ <;>
        simp [ownL] at ho <;>
        rcases hq with ⟨hμ, rfl, hk'⟩ | ⟨hμ, rfl, hk'⟩ | ⟨hμ, rfl, hk'⟩ | ⟨hμ, rfl, hk'⟩ <;>
        (try cases hμ) <;>
        simp only [oriented_peer_false, oriented_peer_true, ofs_add_one, ofs_sub_one,
          ofs_spliceEmb ha hab hbn, val_add_one', val_sub_one', and_true] <;>
        split_ifs <;> omega

omit [NeZero n] in
lemma spliceEmb_injective : Function.Injective (spliceEmb n a b s) := by
  have : NeZero n := ⟨by omega⟩
  have : NeZero (n - (b - a)) := ⟨by omega⟩
  intro v w he
  have h := congrArg (ofs s) he
  rw [ofs_spliceEmb ha hab hbn, ofs_spliceEmb ha hab hbn] at h
  apply ZMod.val_injective
  have := ZMod.val_lt v; have := ZMod.val_lt w
  by_cases hv : v.val < a <;> by_cases hw : w.val < a <;> simp [hv, hw] at h <;> omega

/-- The nodes of `R'` are exactly the nodes of `R` outside `I₂ \ I₁ = (s+a, …, s+b-1)`. -/
lemma exists_spliceEmb_iff (u : ZMod n) :
    (∃ v, spliceEmb n a b s v = u) ↔ ofs s u < a ∨ b ≤ ofs s u := by
  constructor
  · rintro ⟨v, rfl⟩
    cases h : decide (v.val < a)
    · exact Or.inr (by simpa using (exists_spliceEmb ha hab hbn s false _).1 ⟨v, h, rfl⟩)
    · exact Or.inl (by simpa using (exists_spliceEmb ha hab hbn s true _).1 ⟨v, h, rfl⟩)
  · rintro (h | h)
    · obtain ⟨v, -, hv⟩ := (exists_spliceEmb ha hab hbn s true u).2 (by simpa using h)
      exact ⟨v, hv⟩
    · obtain ⟨v, -, hv⟩ := (exists_spliceEmb ha hab hbn s false u).2 (by simpa using h)
      exact ⟨v, hv⟩

/-- **Lemma 28 (splicing with a shared boundary)** of [Chalopin–Chang–Di Luna–Zhou, PODC 2026].
Let `l` be an execution of a (deterministic, content-oblivious) algorithm `A` on the oriented ring
`R` of size `n` with IDs `id`, and let `I₁ = (s, …, s+a-1) ⊂ I₂ = (s, …, s+b-1)`
(`1 ≤ a < b < n`), which share their left boundary edge `{s-1, s}`. If `I₁` and `I₂` have the
same interface trace in `l`, then on the ring `R'` obtained by replacing `I₂` with `I₁`
(the oriented ring of size `n - (b - a)`, whose node `v` is node `spliceEmb n a b s v` of `R`,
with the same ID) there is an execution at the end of which *every* node has the same local state
and pulse counters as its counterpart at the end of `l`.

(The paper concludes that every process outside `I₂` has the same local history; we prove that the
final local states agree, for the processes of `I₁` too. The hypothesis "the leader is not in `I₂`"
is not needed for the lemma itself.) -/
theorem lemma28 (A : Algo) (id : ZMod n → ℕ) (l : List (ZMod n × Bool))
    (hl : ValidSteps (oriented n) A (initCfg A id) l)
    (htr : ringTrace n s a l = ringTrace n s b l) :
    ∃ c', Reach (oriented (n - (b - a))) A (id ∘ spliceEmb n a b s) c' ∧
      ∀ v, NodeAgree (runSteps A (initCfg A id) l) (spliceEmb n a b s v) c' v :=
  splice (ringSpliceData ha hab hbn s) (fun _ => id) _ (fun _ => rfl) (fun _ => l) (fun _ => hl)
    (by simpa [ringSpliceData, ringTrace] using htr)

end splice

/-! ### Equation (1): trace length -/

section traceLength

variable {n : ℕ} [NeZero n]

lemma ringLab_isSome {a : ℕ} (ha : 1 ≤ a) (han : a < n) (s : ZMod n) (p : ZMod n × Bool) :
    (if (ringLab n s a p).isSome then 1 else 0) =
      (if p = (s - 1, true) then 1 else 0) + (if p = (s, false) then 1 else 0) +
      ((if p = (s + a - 1, true) then 1 else 0) + (if p = (s + a, false) then 1 else 0)) := by
  obtain ⟨u, j⟩ := p
  have e1 : (s, false) = (s + ((0 : ℕ) : ZMod n), false) := by simp
  have e2 : (s - 1, true) = (s + ((n - 1 : ℕ) : ZMod n), true) := by
    push_cast [show 1 ≤ n by omega]; simp; ring
  have e3 : (s + a - 1, true) = (s + ((a - 1 : ℕ) : ZMod n), true) := by
    rw [Nat.cast_sub ha, Nat.cast_one, add_sub_assoc]
  rw [ringLab_eq ha han, e1, e2, e3]
  simp only [Prod.mk.injEq, ← ofs_eq_iff (show 0 < n by omega),
    ← ofs_eq_iff (show n - 1 < n by omega), ← ofs_eq_iff (show a - 1 < n by omega),
    ← ofs_eq_iff han, offLab]
  have := ofs_lt s u
  clear e1 e2 e3
  generalize ofs s u = k at *
  cases j
  · have : a ≠ 0 := by omega
    by_cases h0 : k = 0 <;> by_cases h1 : k = a <;> simp [h0, h1, this] <;> omega
  · have : a - 1 ≠ n - 1 := by omega
    by_cases h0 : k = n - 1 <;> by_cases h1 : k = a - 1 <;> simp [h0, h1, this] <;> omega

/-- **Equation (1)** of the paper: `|trace_E(I)| = M(e_L(I)) + M(e_R(I))`. -/
theorem ringTrace_length {S : Algo} {a : ℕ} (ha : 1 ≤ a) (han : a < n) (s : ZMod n)
    (id : ZMod n → ℕ) (l : List (ZMod n × Bool)) :
    (ringTrace n s a l).length =
      edgeLoad (runSteps S (initCfg S id) l) (s - 1) +
        edgeLoad (runSteps S (initCfg S id) l) (s + a - 1) := by
  simp only [ringTrace, List.length_filterMap_eq_countP, edgeLoad, runSteps_initCfg_recvd,
    sub_add_cancel]
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.countP_cons, List.count_cons, ih, beq_iff_eq]
    have := ringLab_isSome ha han s p
    omega

end traceLength

/-! ### Observation 27 -/

/-- The words over `Σ` of length at most `k`. -/
def wordsUpTo (k : ℕ) : Finset (List Letter) :=
  (Finset.range (k + 1)).biUnion fun i =>
    (Finset.univ : Finset (List.Vector Letter i)).image List.Vector.toList

lemma mem_wordsUpTo {k : ℕ} {w : List Letter} : w ∈ wordsUpTo k ↔ w.length ≤ k := by
  simp only [wordsUpTo, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨i, hi, v, rfl⟩; simp; omega
  · intro h; exact ⟨w.length, by omega, ⟨w, rfl⟩, rfl⟩

lemma geom_four_le (k : ℕ) : ∑ i ∈ Finset.range (k + 1), 4 ^ i ≤ 4 ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ 4 (k + 1)]; omega

lemma card_wordsUpTo (k : ℕ) : (wordsUpTo k).card = ∑ i ∈ Finset.range (k + 1), 4 ^ i := by
  rw [wordsUpTo, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.card_image_of_injective _ List.Vector.toList_injective, Finset.card_univ,
      card_vector, Letter.card]
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    rintro _ ⟨v, rfl⟩ w hw
    exact hij (by rw [← v.toList_length, ← w.toList_length, hw])

lemma card_wordsUpTo_le (k : ℕ) : (wordsUpTo k).card ≤ 4 ^ (k + 1) :=
  (card_wordsUpTo k).trans_le (geom_four_le k)

/-- **Observation 27** of [Chalopin–Chang–Di Luna–Zhou, PODC 2026]: the number of words over
`Σ = {Lin, Lout, Rin, Rout}` of length at most `k` is `∑_{i=0}^k 4^i ≤ 4^(k+1)`. -/
theorem observation27 (k : ℕ) :
    {w : List Letter | w.length ≤ k}.ncard = ∑ i ∈ Finset.range (k + 1), 4 ^ i ∧
      {w : List Letter | w.length ≤ k}.ncard ≤ 4 ^ (k + 1) := by
  have hset : {w : List Letter | w.length ≤ k} = ↑(wordsUpTo k) := by
    ext w; simp [mem_wordsUpTo]
  rw [hset, Set.ncard_coe_finset, card_wordsUpTo]
  exact ⟨rfl, geom_four_le k⟩

end Podc.ContentOblivious.Counting
