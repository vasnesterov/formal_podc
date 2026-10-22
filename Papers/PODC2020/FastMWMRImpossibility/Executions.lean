import Papers.PODC2020.FastMWMRImpossibility.Steps
import Mathlib.Tactic.Abel

/-!
# The executions of the impossibility proof

All executions used in the proof of Theorem 1 have the same shape: two writers `w₁, w₂` write
`a` and `b` (each writer's first operation), then two readers `r₁, r₂` read (each reader's first
operation), after both writes returned.

* **Write phase.** Either concurrently, where server `s` receives `W₁` first iff `x s`
  (`reach_writes_conc`), or sequentially, `W₁` before `W₂` or `W₂` before `W₁`
  (`reach_write_solo`). The server logs are then `wlog x s`.
* **Read phase** (`reach_reads`). Both readers invoke `read()`; every server receives the
  first-round message `q₁` of `r₁`, then the one `q₂` of `r₂`; `r₁` collects the replies of all
  servers and `r₂` the replies of all servers except `j` (if `j = some s`, the reply of `s` is
  delayed until the end of the execution: the request *was* delivered, which is the point where
  our proof deviates from the paper's informal "skip"). Then the second-round messages `p₁`, `p₂`
  are delivered according to a per-server pattern `pat s : Pat` (`p₁` then `p₂`, `p₂` then `p₁`,
  only one of them, or none), and both readers collect all second-round replies that exist and
  return.

The returned values are given by the explicit formulas `ret₁`, `ret₂` (functions of the server logs
after the write phase, `j` and `pat`), which makes the indistinguishability arguments of the
chain argument purely algebraic.
-/

namespace Podc.FastMWMR

open Cslib.SharedMemory Cslib.AsyncMP

/-! ### Multiset bookkeeping -/

lemma coe_map_filter_le {α β : Type} (l : List α) (f : α → β) (q : α → Bool) :
    (((l.filter q).map f : List β) : Multiset β) ≤ (l.map f : List β) :=
  Multiset.coe_le.2 ((List.filter_sublist).map f).subperm

lemma coe_map_filter_or {α β : Type} (l : List α) (f : α → β) (q₁ q₂ : α → Bool)
    (hd : ∀ a, ¬ (q₁ a = true ∧ q₂ a = true)) :
    (((l.filter fun a => q₁ a || q₂ a).map f : List β) : Multiset β) =
      ((l.filter q₁).map f : List β) + ((l.filter q₂).map f : List β) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have := hd a
    cases h1 : q₁ a <;> cases h2 : q₂ a <;>
      simp_all [← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons]

lemma coe_map_filter_add_le {α β : Type} (l : List α) (f : α → β) (q₁ q₂ : α → Bool)
    (hd : ∀ a, ¬ (q₁ a = true ∧ q₂ a = true)) :
    (((l.filter q₁).map f : List β) : Multiset β) + ((l.filter q₂).map f : List β) ≤
      (l.map f : List β) := by
  rw [← coe_map_filter_or l f q₁ q₂ hd]; exact coe_map_filter_le _ _ _

section
variable {n : ℕ} {W R Msg Rep : Type}

/-- Replies coming from two disjoint waves. -/
lemma reps_split (c : Node n W R) (k i : ℕ) (rr rr₁ rr₂ : Fin n → Rep) (L : List (Fin n))
    (q₁ q₂ : Fin n → Bool) (hd : ∀ s, ¬ (q₁ s = true ∧ q₂ s = true))
    (h₁ : ∀ s, q₁ s = true → rr s = rr₁ s) (h₂ : ∀ s, q₂ s = true → rr s = rr₂ s) :
    reps (Msg := Msg) c k i rr (L.filter fun s => q₁ s || q₂ s) =
      reps c k i rr₁ (L.filter q₁) + reps c k i rr₂ (L.filter q₂) := by
  unfold reps
  rw [coe_map_filter_or _ _ _ _ hd]
  congr 2
  · exact List.map_congr_left fun s hs => by rw [h₁ s (List.mem_filter.1 hs).2]
  · exact List.map_congr_left fun s hs => by rw [h₂ s (List.mem_filter.1 hs).2]

lemma reqs_filter_le (c : Node n W R) (k i : ℕ) (m : Fin n → Msg) (L : List (Fin n))
    (q : Fin n → Bool) : reqs (Rep := Rep) c k i m (L.filter q) ≤ reqs c k i m L :=
  coe_map_filter_le _ _ _

lemma reps_filter_le (c : Node n W R) (k i : ℕ) (rr : Fin n → Rep) (L : List (Fin n))
    (q : Fin n → Bool) : reps (Msg := Msg) c k i rr (L.filter q) ≤ reps c k i rr L :=
  coe_map_filter_le _ _ _

lemma reqs_filter_add_le (c : Node n W R) (k i : ℕ) (m : Fin n → Msg) (L : List (Fin n))
    (q₁ q₂ : Fin n → Bool) (hd : ∀ s, ¬ (q₁ s = true ∧ q₂ s = true)) :
    reqs (Rep := Rep) c k i m (L.filter q₁) + reqs c k i m (L.filter q₂) ≤ reqs c k i m L :=
  coe_map_filter_add_le _ _ _ _ hd

end

variable {n : ℕ} {W R V Msg Rep LW LR : Type}
variable [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep]
variable (A : W1R2Alg n W R V Msg Rep LW LR) (t : ℕ) (v₀ : V)

namespace W1R2Alg

/-- A write executed alone: delivered to all servers, all replies collected. -/
lemma reach_write_solo {C : Cfg n W R V Msg Rep LW LR}
    {h : List (Label (Node n W R) (register V v₀))}
    (hR : (A.protocol t v₀).Reach C h) (hc : C.crashed = ∅) {w : W} {st : LW} {k : ℕ} (v : V)
    (hl : C.loc (.wr w) = .wr st k none) (lg : Fin n → List (Node n W R × Msg))
    (hlog : ∀ s, C.loc (.srv s) = .srv (lg s)) :
    ∃ C' : Cfg n W R V Msg Rep LW LR,
      (A.protocol t v₀).Reach C' (h ++ [.inv (.wr w) (.write v), .ret (.wr w) v]) ∧
      C'.crashed = ∅ ∧
      (∀ s, C'.loc (.srv s) = .srv (lg s ++ [(.wr w, A.wMsg w st v s)])) ∧
      (∀ p, (∀ s, p ≠ .srv s) → p ≠ .wr w → C'.loc p = C.loc p) := by
  obtain ⟨C₁, hR₁, hc₁, hl₁, hn₁⟩ := A.reach_inv_wr t v₀ hR hc v hl
  obtain ⟨C₂, hR₂, hc₂, hl₂, ho₂, hn₂⟩ := A.reach_wave t v₀ hR₁ hc₁ (.wr w) (k + 1) 1
    (A.wMsg w st v) lg (List.finRange n) (List.nodup_finRange n)
    (fun s _ => by rw [hl₁, Function.update_of_ne (by simp)]; exact hlog s) 0
    (by rw [hn₁, add_zero]; exact Multiset.le_add_left _ _)
  have hw₂ : C₂.loc (.wr w) = .wr st (k + 1) (some (v, [])) := by
    rw [ho₂ _ (by simp), hl₁]; simp
  obtain ⟨C₃, hR₃, hc₃, hl₃, ho₃, -⟩ := A.reach_collect t v₀ hR₂ hc₂ (.wr w) (by simp) (k + 1) 1
    _ (List.finRange n) 0 hn₂
  rw [hw₂, foldl_absorb_wr] at hl₃
  obtain ⟨C₄, hR₄, hc₄, hl₄, -⟩ := A.reach_end_wr t v₀ hR₃ hc₃ hl₃ (by simp)
  refine ⟨C₄, by simpa using hR₄, hc₄, fun s => ?_, fun p hp hpw => ?_⟩
  · rw [hl₄, Function.update_of_ne (by simp), ho₃ _ (by simp)]
    exact hl₂ s (List.mem_finRange s)
  · rw [hl₄, Function.update_of_ne hpw, ho₃ _ hpw, ho₂ _ (fun s _ => hp s), hl₁,
      Function.update_of_ne hpw]

/-- Server logs after the writes `W₁ = write(a)` by `w₁` and `W₂ = write(b)` by `w₂` (first
operations of both writers): server `s` received `W₁` first iff `x s`. -/
def wlog (w₁ w₂ : W) (a b : V) (x : Fin n → Bool) (s : Fin n) : List (Node n W R × Msg) :=
  if x s then [(.wr w₁, A.wMsg w₁ (A.initW w₁) a s), (.wr w₂, A.wMsg w₂ (A.initW w₂) b s)]
  else [(.wr w₂, A.wMsg w₂ (A.initW w₂) b s), (.wr w₁, A.wMsg w₁ (A.initW w₁) a s)]

omit [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep] in
lemma initCfg_loc (p : Node n W R) : (A.protocol t v₀).initCfg.loc p = (A.protocol t v₀).init p :=
  rfl

/-- Two concurrent writes; server `s` receives `W₁` first iff `x s`. -/
lemma reach_writes_conc {w₁ w₂ : W} (hw : w₁ ≠ w₂) (a b : V) (x : Fin n → Bool) :
    ∃ C : Cfg n W R V Msg Rep LW LR,
      (A.protocol t v₀).Reach C [.inv (.wr w₁) (.write a), .inv (.wr w₂) (.write b),
        .ret (.wr w₁) a, .ret (.wr w₂) b] ∧ C.crashed = ∅ ∧
      (∀ s, C.loc (.srv s) = .srv (A.wlog w₁ w₂ a b x s)) ∧
      (∀ r, C.loc (.rd r) = .rd (A.initR r) 0 .idle) := by
  set m₁ := A.wMsg w₁ (A.initW w₁) a
  set m₂ := A.wMsg w₂ (A.initW w₂) b
  have hww : (Node.wr w₂ : Node n W R) ≠ .wr w₁ := by simpa using hw.symm
  have hR₀ := Protocol.Reach.init (Pr := A.protocol t v₀)
  obtain ⟨C₁, hR₁, hc₁, hl₁, hn₁⟩ := A.reach_inv_wr t v₀ hR₀ rfl a (w := w₁) (st := A.initW w₁)
    (k := 0) rfl
  obtain ⟨C₂, hR₂, hc₂, hl₂, hn₂⟩ := A.reach_inv_wr t v₀ hR₁ hc₁ b (w := w₂) (st := A.initW w₂)
    (k := 0) (by rw [hl₁, Function.update_of_ne hww]; rfl)
  have hs₂ : ∀ s, C₂.loc (.srv s) = .srv [] := fun s => by
    rw [hl₂, Function.update_of_ne (by simp), hl₁, Function.update_of_ne (by simp)]; rfl
  have hdx : ∀ s, ¬ (x s = true ∧ (!x s) = true) := fun s => by cases x s <;> simp
  -- wave a: `m₁` to the servers with `x s`
  obtain ⟨C₃, hR₃, hc₃, hl₃, ho₃, hn₃⟩ := A.reach_wave t v₀ hR₂ hc₂ (.wr w₁) 1 1 m₁ (fun _ => [])
    ((List.finRange n).filter x) ((List.nodup_finRange n).filter _) (fun s _ => hs₂ s)
    (reqs (.wr w₁) 1 1 m₁ ((List.finRange n).filter fun s => !x s) + reqs (.wr w₂) 1 1 m₂
      (List.finRange n))
    (by
      rw [hn₂, hn₁]; simp only [Protocol.initCfg, zero_add]; rw [← add_assoc]
      exact add_le_add (coe_map_filter_add_le _ _ _ _ hdx) le_rfl)
  set lg₄ : Fin n → List (Node n W R × Msg) := fun s => if x s then [(.wr w₁, m₁ s)] else []
  -- wave b: `m₂` to all servers
  obtain ⟨C₄, hR₄, hc₄, hl₄, ho₄, hn₄⟩ := A.reach_wave t v₀ hR₃ hc₃ (.wr w₂) 1 1 m₂ lg₄
    (List.finRange n) (List.nodup_finRange n)
    (fun s _ => by
      by_cases hx : x s = true
      · rw [hl₃ s (by simp [hx])]; simp [lg₄, hx]
      · rw [ho₃ _ (fun s' hs' he => by cases he; simp_all), hs₂ s]; simp [lg₄, hx])
    (reqs (.wr w₁) 1 1 m₁ ((List.finRange n).filter fun s => !x s) +
      reps (.wr w₁) 1 1 (fun s => A.reply s [] (.wr w₁) (m₁ s)) ((List.finRange n).filter x))
    (by convert hn₃ using 1; abel)
  -- wave c: `m₁` to the servers with `¬ x s`
  obtain ⟨C₅, hR₅, hc₅, hl₅, ho₅, hn₅⟩ := A.reach_wave t v₀ hR₄ hc₄ (.wr w₁) 1 1 m₁
    (fun s => [(.wr w₂, m₂ s)]) ((List.finRange n).filter fun s => !x s)
    ((List.nodup_finRange n).filter _)
    (fun s hs => by
      have hx : x s = false := by simpa using (List.mem_filter.1 hs).2
      rw [hl₄ s (List.mem_finRange s)]; simp [lg₄, hx])
    (reps (.wr w₁) 1 1 (fun s => A.reply s [] (.wr w₁) (m₁ s)) ((List.finRange n).filter x) +
      reps (.wr w₂) 1 1 (fun s => A.reply s (lg₄ s) (.wr w₂) (m₂ s)) (List.finRange n))
    (by convert hn₄ using 1; abel)
  -- `w₁` collects its replies and returns
  have hw₁₅ : C₅.loc (.wr w₁) = .wr (A.initW w₁) 1 (some (a, [])) := by
    rw [ho₅ _ (by simp), ho₄ _ (by simp), ho₃ _ (by simp), hl₂, Function.update_of_ne hww.symm,
      hl₁]
    simp
  set rr₁ : Fin n → Rep := fun s =>
    A.reply s (if x s then [] else [(.wr w₂, m₂ s)]) (.wr w₁) (m₁ s)
  set rr₁ : Fin n → Rep := fun s =>
    A.reply s (if x s then [] else [(.wr w₂, m₂ s)]) (.wr w₁) (m₁ s)
  have hsplit : reps (Msg := Msg) (Node.wr w₁ : Node n W R) 1 1 rr₁ (List.finRange n) =
      reps (.wr w₁) 1 1 (fun s => A.reply s [] (.wr w₁) (m₁ s)) ((List.finRange n).filter x) +
      reps (.wr w₁) 1 1 (fun s => A.reply s [(.wr w₂, m₂ s)] (.wr w₁) (m₁ s))
        ((List.finRange n).filter fun s => !x s) := by
    rw [← reps_split _ _ _ rr₁ _ _ _ _ _ hdx (fun s hs => by simp [rr₁, hs])
      (fun s hs => by simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hs; simp [rr₁, hs])]
    congr 1; simp
  obtain ⟨C₆, hR₆, hc₆, hl₆, ho₆, hn₆⟩ := A.reach_collect t v₀ hR₅ hc₅ (.wr w₁) (by simp) 1 1
    rr₁ (List.finRange n)
    (reps (.wr w₂) 1 1 (fun s => A.reply s (lg₄ s) (.wr w₂) (m₂ s)) (List.finRange n))
    (by rw [hsplit]; convert hn₅ using 1; abel)
  rw [hw₁₅, foldl_absorb_wr] at hl₆
  obtain ⟨C₇, hR₇, hc₇, hl₇, hn₇⟩ := A.reach_end_wr t v₀ hR₆ hc₆ hl₆ (by simp)
  have hw₂₇ : C₇.loc (.wr w₂) = .wr (A.initW w₂) 1 (some (b, [])) := by
    rw [hl₇, Function.update_of_ne hww, ho₆ _ hww, ho₅ _ (by simp), ho₄ _ (by simp),
      ho₃ _ (by simp), hl₂]
    simp
  obtain ⟨C₈, hR₈, hc₈, hl₈, ho₈, -⟩ := A.reach_collect t v₀ hR₇ hc₇ (.wr w₂) (by simp) 1 1 _
    (List.finRange n) 0 (by rw [hn₇, add_zero]; exact hn₆)
  rw [hw₂₇, foldl_absorb_wr] at hl₈
  obtain ⟨C₉, hR₉, hc₉, hl₉, -⟩ := A.reach_end_wr t v₀ hR₈ hc₈ hl₈ (by simp)
  refine ⟨C₉, by simpa using hR₉, hc₉, fun s => ?_, fun r => ?_⟩
  · rw [hl₉, Function.update_of_ne (by simp), ho₈ _ (by simp), hl₇,
      Function.update_of_ne (by simp), ho₆ _ (by simp)]
    by_cases hx : x s = true
    · rw [ho₅ _ (fun s' hs' he => by cases he; simp_all), hl₄ s (List.mem_finRange s)]
      simp [wlog, lg₄, hx, m₁, m₂]
    · rw [hl₅ s (by simpa using hx)]; simp [wlog, hx, m₁, m₂]
  · rw [hl₉, Function.update_of_ne (by simp), ho₈ _ (by simp), hl₇,
      Function.update_of_ne (by simp), ho₆ _ (by simp), ho₅ _ (by simp), ho₄ _ (by simp),
      ho₃ _ (by simp), hl₂, Function.update_of_ne (by simp), hl₁, Function.update_of_ne (by simp)]
    rfl

end W1R2Alg

/-- Order of the second-round messages `p₁` (of `r₁`) and `p₂` (of `r₂`) at a server. -/
inductive Pat where
  /-- neither is delivered -/
  | none
  /-- only `p₁` is delivered -/
  | only1
  /-- only `p₂` is delivered -/
  | only2
  /-- `p₁`, then `p₂` -/
  | first1
  /-- `p₂`, then `p₁` -/
  | first2
  deriving DecidableEq

namespace Pat

/-- `p₁` is delivered. -/
def del1 : Pat → Bool
  | .only1 | .first1 | .first2 => true
  | _ => false

/-- `p₂` is delivered. -/
def del2 : Pat → Bool
  | .only2 | .first1 | .first2 => true
  | _ => false

/-- `p₂` is delivered before `p₁` (or alone). -/
def waveA : Pat → Bool
  | .first2 | .only2 => true
  | _ => false

/-- `p₂` is delivered after `p₁`. -/
def waveC : Pat → Bool
  | .first1 => true
  | _ => false

lemma del2_eq (p : Pat) : p.del2 = (p.waveA || p.waveC) := by cases p <;> rfl

lemma waveA_waveC (p : Pat) : ¬ (p.waveA = true ∧ p.waveC = true) := by cases p <;> simp [waveA, waveC]

end Pat

namespace W1R2Alg

section Formulas

variable (r₁ r₂ : R) (ℓ : Fin n → List (Node n W R × Msg)) (j : Option (Fin n))
  (pat : Fin n → Pat)

/-- First-round view of `r₁` (replies of all servers). -/
def V₁ : View n Rep :=
  (List.finRange n).map fun s => (s, A.reply s (ℓ s) (.rd r₁) (A.rMsg1 r₁ (A.initR r₁) s))

/-- First-round view of `r₂` (replies of all servers but `j`; `r₁`'s request came first). -/
def U₁ : View n Rep :=
  ((List.finRange n).filter fun s => decide (j ≠ some s)).map fun s =>
    (s, A.reply s (ℓ s ++ [(.rd r₁, A.rMsg1 r₁ (A.initR r₁) s)]) (.rd r₂)
      (A.rMsg1 r₂ (A.initR r₂) s))

/-- Server logs after both first round-trips. -/
def base (s : Fin n) : List (Node n W R × Msg) :=
  ℓ s ++ [(.rd r₁, A.rMsg1 r₁ (A.initR r₁) s), (.rd r₂, A.rMsg1 r₂ (A.initR r₂) s)]

/-- Second-round message of `r₁`. -/
def p₁ (s : Fin n) : Msg := A.rMsg2 r₁ (A.initR r₁) (A.V₁ r₁ ℓ) s

/-- Second-round message of `r₂`. -/
def p₂ (s : Fin n) : Msg := A.rMsg2 r₂ (A.initR r₂) (A.U₁ r₁ r₂ ℓ j) s

/-- Second-round view of `r₁`. -/
def V₂ : View n Rep :=
  ((List.finRange n).filter fun s => (pat s).del1).map fun s =>
    (s, A.reply s (A.base r₁ r₂ ℓ s ++
      (if pat s = .first2 then [(.rd r₂, A.p₂ r₁ r₂ ℓ j s)] else [])) (.rd r₁) (A.p₁ r₁ ℓ s))

/-- Second-round view of `r₂`. -/
def U₂ : View n Rep :=
  ((List.finRange n).filter fun s => (pat s).del2).map fun s =>
    (s, A.reply s (A.base r₁ r₂ ℓ s ++
      (if pat s = .first1 then [(.rd r₁, A.p₁ r₁ ℓ s)] else [])) (.rd r₂) (A.p₂ r₁ r₂ ℓ j s))

/-- The value returned by `r₁`. -/
def ret₁ : V := (A.rEnd r₁ (A.initR r₁) (A.V₁ r₁ ℓ) (A.V₂ r₁ r₂ ℓ j pat)).1

/-- The value returned by `r₂`. -/
def ret₂ : V := (A.rEnd r₂ (A.initR r₂) (A.U₁ r₁ r₂ ℓ j) (A.U₂ r₁ r₂ ℓ j pat)).1

end Formulas

/-- Admissible schedules of the read phase: each round-trip gets at least `n - t` replies. -/
def ReadValid (n t : ℕ) (j : Option (Fin n)) (pat : Fin n → Pat) : Prop :=
  n ≤ ((List.finRange n).filter fun s => (pat s).del1).length + t ∧
  n ≤ ((List.finRange n).filter fun s => (pat s).del2).length + t ∧
  n ≤ ((List.finRange n).filter fun s => decide (j ≠ some s)).length + t

/-- **The read phase.** From a configuration where the server logs are `ℓ` and both readers are
idle (before their first operation), both readers read with the schedule `(j, pat)`. -/
lemma reach_reads {C : Cfg n W R V Msg Rep LW LR} {h : List (Label (Node n W R) (register V v₀))}
    (hR : (A.protocol t v₀).Reach C h) (hc : C.crashed = ∅) {r₁ r₂ : R} (hr : r₁ ≠ r₂)
    (ℓ : Fin n → List (Node n W R × Msg)) (hlog : ∀ s, C.loc (.srv s) = .srv (ℓ s))
    (h₁ : C.loc (.rd r₁) = .rd (A.initR r₁) 0 .idle) (h₂ : C.loc (.rd r₂) = .rd (A.initR r₂) 0 .idle)
    (j : Option (Fin n)) (pat : Fin n → Pat) (hv : ReadValid n t j pat) :
    ∃ C' : Cfg n W R V Msg Rep LW LR, (A.protocol t v₀).Reach C' (h ++
      [.inv (.rd r₁) .read, .inv (.rd r₂) .read, .ret (.rd r₁) (A.ret₁ r₁ r₂ ℓ j pat),
        .ret (.rd r₂) (A.ret₂ r₁ r₂ ℓ j pat)]) := by
  set q₁ := A.rMsg1 r₁ (A.initR r₁)
  set q₂ := A.rMsg1 r₂ (A.initR r₂)
  set F := List.finRange n
  have hrr : (Node.rd r₂ : Node n W R) ≠ .rd r₁ := by simpa using hr.symm
  obtain ⟨C₁, hR₁, hc₁, hl₁, hn₁⟩ := A.reach_inv_rd t v₀ hR hc h₁
  obtain ⟨C₂, hR₂, hc₂, hl₂, hn₂⟩ := A.reach_inv_rd t v₀ hR₁ hc₁
    (by rw [hl₁, Function.update_of_ne hrr]; exact h₂)
  simp only [zero_add] at hl₁ hl₂ hn₁ hn₂
  have hs₂ : ∀ s, C₂.loc (.srv s) = .srv (ℓ s) := fun s => by
    rw [hl₂, Function.update_of_ne (by simp), hl₁, Function.update_of_ne (by simp)]; exact hlog s
  -- first round-trips: `q₁` everywhere, then `q₂` everywhere
  obtain ⟨C₃, hR₃, hc₃, hl₃, ho₃, hn₃⟩ := A.reach_wave t v₀ hR₂ hc₂ (.rd r₁) 1 1 q₁ ℓ F
    (List.nodup_finRange n) (fun s _ => hs₂ s) (reqs (.rd r₂) 1 1 q₂ F)
    (by rw [hn₂, hn₁, add_assoc]; exact Multiset.le_add_left _ _)
  obtain ⟨C₄, hR₄, hc₄, hl₄, ho₄, hn₄⟩ := A.reach_wave t v₀ hR₃ hc₃ (.rd r₂) 1 1 q₂
    (fun s => ℓ s ++ [(.rd r₁, q₁ s)]) F (List.nodup_finRange n)
    (fun s hs => hl₃ s hs)
    (reps (.rd r₁) 1 1 (fun s => A.reply s (ℓ s) (.rd r₁) (q₁ s)) F)
    (by rw [add_comm]; exact hn₃)
  have hs₄ : ∀ s, C₄.loc (.srv s) = .srv (A.base r₁ r₂ ℓ s) := fun s => by
    rw [hl₄ s (List.mem_finRange s)]; simp [base, q₁, q₂]
  -- `r₁` collects all first-round replies and sends `p₁`
  obtain ⟨C₅, hR₅, hc₅, hl₅, ho₅, hn₅⟩ := A.reach_collect t v₀ hR₄ hc₄ (.rd r₁) (by simp) 1 1
    (fun s => A.reply s (ℓ s) (.rd r₁) (q₁ s)) F
    (reps (.rd r₂) 1 1 (fun s => A.reply s (ℓ s ++ [(.rd r₁, q₁ s)]) (.rd r₂) (q₂ s)) F)
    (by rw [add_comm]; exact hn₄)
  rw [ho₄ _ (by simp), ho₃ _ (by simp), hl₂, Function.update_of_ne hrr.symm, hl₁,
    Function.update_self, foldl_absorb_one, List.nil_append] at hl₅
  obtain ⟨C₆, hR₆, hc₆, hl₆, hn₆⟩ := A.reach_mid_rd t v₀ hR₅ hc₅ hl₅ (by simp [F])
  -- `r₂` collects the first-round replies of all servers but `j` and sends `p₂`
  obtain ⟨C₇, hR₇, hc₇, hl₇, ho₇, hn₇⟩ := A.reach_collect t v₀ hR₆ hc₆ (.rd r₂) (by simp) 1 1
    (fun s => A.reply s (ℓ s ++ [(.rd r₁, q₁ s)]) (.rd r₂) (q₂ s))
    (F.filter fun s => decide (j ≠ some s)) (reqs (.rd r₁) 1 2 (A.p₁ r₁ ℓ) F)
    (by rw [hn₆]; exact add_le_add ((reps_filter_le _ _ _ _ _ _).trans hn₅) le_rfl)
  rw [hl₆, Function.update_of_ne hrr, ho₅ _ hrr, ho₄ _ (by simp), ho₃ _ (by simp), hl₂,
    Function.update_self, foldl_absorb_one, List.nil_append] at hl₇
  obtain ⟨C₈, hR₈, hc₈, hl₈, hn₈⟩ := A.reach_mid_rd t v₀ hR₇ hc₇ hl₇ (by simpa using hv.2.2)
  have hs₈ : ∀ s, C₈.loc (.srv s) = .srv (A.base r₁ r₂ ℓ s) := fun s => by
    rw [hl₈, Function.update_of_ne (by simp), ho₇ _ (by simp), hl₆,
      Function.update_of_ne (by simp), ho₅ _ (by simp)]
    exact hs₄ s
  -- second round-trips: wave A (`p₂` first or alone), wave B (`p₁`), wave C (`p₂` after `p₁`)
  set fA := F.filter fun s => (pat s).waveA
  set fB := F.filter fun s => (pat s).del1
  set fC := F.filter fun s => (pat s).waveC
  set P₁ := A.p₁ r₁ ℓ
  set P₂ := A.p₂ r₁ r₂ ℓ j
  obtain ⟨C₉, hR₉, hc₉, hl₉, ho₉, hn₉⟩ := A.reach_wave t v₀ hR₈ hc₈ (.rd r₂) 1 2 P₂
    (A.base r₁ r₂ ℓ) fA ((List.nodup_finRange n).filter _) (fun s _ => hs₈ s)
    (reqs (.rd r₁) 1 2 P₁ F + reqs (.rd r₂) 1 2 P₂ fC)
    (by
      rw [hn₈]
      have hA := reqs_filter_add_le (Rep := Rep) (Node.rd r₂ : Node n W R) 1 2 P₂ F
        (fun s => (pat s).waveA) (fun s => (pat s).waveC) (fun s => Pat.waveA_waveC _)
      calc _ = reqs (.rd r₁) 1 2 P₁ F + (reqs (.rd r₂) 1 2 P₂ fA + reqs (.rd r₂) 1 2 P₂ fC) := by
            abel
        _ ≤ _ := add_le_add hn₇ hA)
  set lgB : Fin n → List (Node n W R × Msg) := fun s =>
    A.base r₁ r₂ ℓ s ++ (if (pat s).waveA then [(.rd r₂, P₂ s)] else [])
  have hsB : ∀ s, C₉.loc (.srv s) = .srv (lgB s) := fun s => by
    by_cases ha : (pat s).waveA = true
    · rw [hl₉ s (List.mem_filter.2 ⟨List.mem_finRange s, ha⟩)]; simp [lgB, ha]
    · rw [ho₉ _ (fun s' hs' he => by cases he; exact ha (List.mem_filter.1 hs').2), hs₈ s]
      simp [lgB, ha]
  set RA := reps (Msg := Msg) (Node.rd r₂ : Node n W R) 1 2
    (fun s => A.reply s (A.base r₁ r₂ ℓ s) (.rd r₂) (P₂ s)) fA
  obtain ⟨C₁₀, hR₁₀, hc₁₀, hl₁₀, ho₁₀, hn₁₀⟩ := A.reach_wave t v₀ hR₉ hc₉ (.rd r₁) 1 2 P₁
    lgB fB ((List.nodup_finRange n).filter _) (fun s _ => hsB s)
    (RA + reqs (.rd r₂) 1 2 P₂ fC)
    (by
      refine le_trans ?_ hn₉
      calc _ = RA + (reqs (.rd r₁) 1 2 P₁ fB + reqs (.rd r₂) 1 2 P₂ fC) := by abel
        _ ≤ _ := add_le_add le_rfl (add_le_add (reqs_filter_le _ _ _ _ _ _) le_rfl))
  set lgC : Fin n → List (Node n W R × Msg) := fun s =>
    lgB s ++ (if (pat s).del1 then [(.rd r₁, P₁ s)] else [])
  have hsC : ∀ s, C₁₀.loc (.srv s) = .srv (lgC s) := fun s => by
    by_cases hb : (pat s).del1 = true
    · rw [hl₁₀ s (List.mem_filter.2 ⟨List.mem_finRange s, hb⟩)]; simp [lgC, hb]
    · rw [ho₁₀ _ (fun s' hs' he => by cases he; exact hb (List.mem_filter.1 hs').2), hsB s]
      simp [lgC, hb]
  set RB := reps (Msg := Msg) (Node.rd r₁ : Node n W R) 1 2
    (fun s => A.reply s (lgB s) (.rd r₁) (P₁ s)) fB
  obtain ⟨C₁₁, hR₁₁, hc₁₁, -, ho₁₁, hn₁₁⟩ := A.reach_wave t v₀ hR₁₀ hc₁₀ (.rd r₂) 1 2 P₂
    lgC fC ((List.nodup_finRange n).filter _) (fun s _ => hsC s) (RA + RB)
    (by convert hn₁₀ using 1; abel)
  set RC := reps (Msg := Msg) (Node.rd r₂ : Node n W R) 1 2
    (fun s => A.reply s (lgC s) (.rd r₂) (P₂ s)) fC
  -- `r₁` collects its second-round replies and returns
  obtain ⟨C₁₂, hR₁₂, hc₁₂, hl₁₂, ho₁₂, hn₁₂⟩ := A.reach_collect t v₀ hR₁₁ hc₁₁ (.rd r₁)
    (by simp) 1 2 (fun s => A.reply s (lgB s) (.rd r₁) (P₁ s)) fB (RA + RC)
    (by convert hn₁₁ using 1; abel)
  rw [ho₁₁ _ (by simp), ho₁₀ _ (by simp), ho₉ _ (by simp), hl₈, Function.update_of_ne hrr.symm,
    ho₇ _ hrr.symm, hl₆, Function.update_self, foldl_absorb_two, List.nil_append] at hl₁₂
  obtain ⟨C₁₃, hR₁₃, hc₁₃, hl₁₃, hn₁₃⟩ := A.reach_end_rd t v₀ hR₁₂ hc₁₂ hl₁₂
    (by simpa using hv.1)
  -- `r₂` collects its second-round replies and returns
  set rrU : Fin n → Rep := fun s => A.reply s (A.base r₁ r₂ ℓ s ++
    (if pat s = .first1 then [(.rd r₁, P₁ s)] else [])) (.rd r₂) (P₂ s)
  have hfD : F.filter (fun s => (pat s).del2) =
      F.filter (fun s => (pat s).waveA || (pat s).waveC) :=
    List.filter_congr fun s _ => Pat.del2_eq _
  have hsplit : reps (Msg := Msg) (Node.rd r₂ : Node n W R) 1 2 rrU
      (F.filter fun s => (pat s).del2) = RA + RC := by
    rw [hfD]
    refine reps_split _ _ _ _ _ _ _ _ _ (fun s => Pat.waveA_waveC _) (fun s hs => ?_)
      (fun s hs => ?_)
    · have : pat s ≠ .first1 := by intro he; rw [he] at hs; simp [Pat.waveA] at hs
      simp [rrU, this]
    · have : pat s = .first1 := by cases h : pat s <;> simp_all [Pat.waveC]
      simp [rrU, lgC, lgB, this, Pat.waveA, Pat.del1]
  obtain ⟨C₁₄, hR₁₄, hc₁₄, hl₁₄, -, -⟩ := A.reach_collect t v₀ hR₁₃ hc₁₃ (.rd r₂)
    (by simp) 1 2 rrU (F.filter fun s => (pat s).del2) 0
    (by rw [hn₁₃, add_zero, hsplit]; exact hn₁₂)
  rw [hl₁₃, Function.update_of_ne hrr, ho₁₂ _ hrr, ho₁₁ _ (by simp), ho₁₀ _ (by simp),
    ho₉ _ (by simp), hl₈, Function.update_self, foldl_absorb_two, List.nil_append] at hl₁₄
  obtain ⟨C₁₅, hR₁₅, -⟩ := A.reach_end_rd t v₀ hR₁₄ hc₁₄ hl₁₄ (by simpa using hv.2.1)
  have hV₂ : fB.map (fun s => (s, A.reply s (lgB s) (.rd r₁) (P₁ s))) = A.V₂ r₁ r₂ ℓ j pat := by
    refine List.map_congr_left fun s hs => ?_
    have hb := (List.mem_filter.1 hs).2
    have : (pat s).waveA = decide (pat s = .first2) := by
      cases h : pat s <;> simp_all [Pat.waveA, Pat.del1]
    simp only [lgB, this, decide_eq_true_eq]; rfl
  have e₁ : A.ret₁ r₁ r₂ ℓ j pat = (A.rEnd r₁ (A.initR r₁) (A.V₁ r₁ ℓ)
      (fB.map fun s => (s, A.reply s (lgB s) (.rd r₁) (P₁ s)))).1 := by rw [hV₂]; rfl
  rw [e₁]
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hR₁₅
  exact ⟨C₁₅, hR₁₅⟩

end W1R2Alg

end Podc.FastMWMR
