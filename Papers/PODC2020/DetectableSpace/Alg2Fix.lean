import Papers.PODC2020.DetectableSpace.Alg2Defs
import Papers.PODC2020.DetectableSpace.Alg2LinTools

/-!
# The corrected Algorithm 2 is durably linearizable and detectable

`alg2fix` (Algorithm 2 where `Cas(v, v)` only reads `C`) satisfies durable linearizability and
detectability (`alg2fix_durLinDet`), and it is wait-free. Together with the counterexample in
`Alg2Counter.lean` this gives a corrected Lemma 2.

## Linearization

We maintain, along every execution, a linearization `L` of the history so far
(`durLinDet_of_inv`) such that the state after `L` is the value stored in `C`, and for every
running process `p` with current operation `a` the response `linResp L a` of `a` in `L`
(`none` if `a ∉ L`) is described by the per-process invariant `PI` (a case analysis on the
program counter of `p`):

* `Read`, and `Cas` whose line 28 finds `val ≠ old` (or, in the fix, `old = new`) are linearized
  at line 28 (pushed at the end of `L`);
* a successful hardware CAS (line 35) is the linearization point of its `Cas`; at that moment,
  every other process `p` between lines 33 and 35 that is not yet linearized (it then holds
  `C = ⟨val, vec⟩` as its snapshot, so `val = old`) gets a *speculative failed* entry pushed right
  after (the new value differs from `old`, as the fix guarantees `old ≠ new` at line 35);
* if later `p`'s own hardware CAS succeeds (`C` returned exactly to `p`'s snapshot), its
  speculative entry is removed (`DLin.filter`) and its success is pushed;
* at a crash, the entries of crashed processes that did not persist their response and whose
  recovery will not return `true` are removed (they are reads or failed CASes, so they do not
  change the state).
-/

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory Alg2

namespace Alg2Fix

variable {P V : Type} [DecidableEq P] [DecidableEq V]

/-- The sequential response `r` of `o` determines that `o` does not change the state. -/
def Ok : RCOp V → (V ⊕ Bool) → Prop
  | .read, _ => True
  | .cas old new, r => old = new ∨ r = .inr false

lemma Ok.pres {v₀ : V} {o : RCOp V} {r : V ⊕ Bool} (h : Ok o r) (τ : V)
    (hr : ((casRC V v₀).δ τ o).2 = r) : ((casRC V v₀).δ τ o).1 = τ := by
  cases o with
  | read => rfl
  | cas old new =>
    simp only [Ok] at h
    simp only [casRC] at hr ⊢
    split_ifs at hr ⊢ with hτ
    · rcases h with rfl | rfl
      · exact hτ.symm
      · simp at hr
    · rfl

lemma ok_false (o : RCOp V) : Ok o (.inr false) := by
  cases o <;> simp [Ok]

/-- `Ann_p.CP = 1` only during a `Cas(old, new)` with `old ≠ new`. -/
def CPok (A : Ann V) : RCOp V → Prop
  | .read => A.CP = false
  | .cas old new => A.CP = true → old ≠ new

/-- The invariant of `Cas.Recover`. -/
def RecOK (p : P) (C : V × (P → Bool)) (A : Ann V) (o : RCOp V) (ρ : Option (V ⊕ Bool)) :
    Prop :=
  (∃ old new, o = .cas old new) ∧ (∀ r, A.result = some r → ρ = some r) ∧
  (A.result = none → A.CP = false → ρ = none) ∧
  (A.result = none → A.CP = true → (ρ.isSome ↔ C.2 p = A.RD) ∧ ∀ r, ρ = some r → r = .inr true)

/-- The per-process invariant: process `p` (shared variable `C`, private memory `A`, current
operation `o`, in recovery iff `rc`) at program counter `l`, its operation having response `ρ`
in the linearization. -/
def PI (p : P) (C : V × (P → Bool)) (A : Ann V) (o : RCOp V) (rc : Bool) :
    Loc P V → Option (V ⊕ Bool) → Prop
  | .c28 old new, ρ => o = .cas old new ∧ A.CP = false ∧ A.result = none ∧ ρ = none
  | .c33 new s, ρ => o = .cas s.1 new ∧ s.1 ≠ new ∧ A.CP = false ∧ A.result = none ∧
      C.2 p = s.2 p ∧ (ρ = none → C = s) ∧ (ρ = none ∨ ρ = some (.inr false))
  | .c34 new s, ρ => o = .cas s.1 new ∧ s.1 ≠ new ∧ A.CP = false ∧ A.result = none ∧
      A.RD = !s.2 p ∧ C.2 p = s.2 p ∧ (ρ = none → C = s) ∧ (ρ = none ∨ ρ = some (.inr false))
  | .c35 new s, ρ => o = .cas s.1 new ∧ s.1 ≠ new ∧ A.CP = true ∧ A.result = none ∧
      A.RD = !s.2 p ∧ C.2 p = s.2 p ∧ (ρ = none → C = s) ∧ (ρ = none ∨ ρ = some (.inr false))
  | .wres r, ρ => A.result = none ∧ ρ = some r ∧
      (A.CP = true → r = .inr (decide (C.2 p = A.RD))) ∧ (A.CP = false → Ok o r)
  | .ret none, ρ => rc = true ∧ (∃ old new, o = .cas old new) ∧ A.result = none ∧ ρ = none ∧
      (A.CP = true → C.2 p ≠ A.RD)
  | .ret (some r), ρ => A.result = some r ∧ ρ = some r
  | .r38, ρ => rc = true ∧ RecOK p C A o ρ
  | .r40, ρ => rc = true ∧ A.result = none ∧ RecOK p C A o ρ
  | .r42, ρ => rc = true ∧ A.result = none ∧ A.CP = true ∧ RecOK p C A o ρ
  | .r43 b, ρ => rc = true ∧ A.result = none ∧ A.CP = true ∧ b = C.2 p ∧ RecOK p C A o ρ
  | .d0, ρ => o = .read ∧ A.result = none ∧ ρ = none
  | .dr, ρ => o = .read ∧ (A.result = none → ρ = none) ∧ (∀ r, A.result = some r → ρ = some r)

/-- Program counters between lines 33 and 35. -/
def _root_.Papers.PODC2020.DetectableSpace.Alg2.Loc.pre : Loc P V → Bool
  | .c33 .. | .c34 .. | .c35 .. => true
  | _ => false

/-! ### Per-process facts -/

section PIfacts

variable {p : P} {C : V × (P → Bool)} {A : Ann V} {o : RCOp V} {rc : Bool} {l : Loc P V}
  {ρ : Option (V ⊕ Bool)}

/-- What a crash preserves. -/
lemma PI.crashFacts (h : PI p C A o rc l ρ) (hcp : CPok A o) :
    (∀ r, A.result = some r → ρ = some r) ∧
      (A.result = none → A.CP = true → C.2 p = A.RD → ρ = some (.inr true)) := by
  cases l with
  | c28 old new => obtain ⟨-, h2, h3, -⟩ := h; simp [h2, h3]
  | c33 new s => obtain ⟨-, -, h2, h3, -⟩ := h; simp [h2, h3]
  | c34 new s => obtain ⟨-, -, h2, h3, -⟩ := h; simp [h2, h3]
  | c35 new s =>
    obtain ⟨-, -, -, h3, h4, h5, -⟩ := h
    refine ⟨by simp [h3], fun _ _ he => ?_⟩
    rw [h4, h5] at he; cases s.2 p <;> simp at he
  | wres r =>
    obtain ⟨h1, h2, h3, -⟩ := h
    refine ⟨by simp [h1], fun _ hc he => ?_⟩
    rw [h2, h3 hc]; simp [he]
  | ret r =>
    cases r with
    | none =>
      obtain ⟨-, -, h1, h2, h3⟩ := h
      exact ⟨by simp [h1], fun _ hc he => absurd he (h3 hc)⟩
    | some r =>
      obtain ⟨h1, h2⟩ := h
      exact ⟨by simp [h1, h2], fun h' => by simp [h1] at h'⟩
  | r38 =>
    obtain ⟨-, -, h1, -, h3⟩ := h
    refine ⟨h1, fun hr hc he => ?_⟩
    obtain ⟨h4, h5⟩ := h3 hr hc
    obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.1 (h4.2 he)
    rw [hr', h5 r hr']
  | r40 =>
    obtain ⟨-, -, -, h1, -, h3⟩ := h
    refine ⟨h1, fun hr hc he => ?_⟩
    obtain ⟨h4, h5⟩ := h3 hr hc
    obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.1 (h4.2 he)
    rw [hr', h5 r hr']
  | r42 =>
    obtain ⟨-, -, -, -, h1, -, h3⟩ := h
    refine ⟨h1, fun hr hc he => ?_⟩
    obtain ⟨h4, h5⟩ := h3 hr hc
    obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.1 (h4.2 he)
    rw [hr', h5 r hr']
  | r43 b =>
    obtain ⟨-, -, -, -, -, h1, -, h3⟩ := h
    refine ⟨h1, fun hr hc he => ?_⟩
    obtain ⟨h4, h5⟩ := h3 hr hc
    obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.1 (h4.2 he)
    rw [hr', h5 r hr']
  | d0 =>
    obtain ⟨rfl, h1, -⟩ := h
    simp only [CPok] at hcp
    simp [h1, hcp]
  | dr =>
    obtain ⟨rfl, -, h2⟩ := h
    simp only [CPok] at hcp
    exact ⟨h2, by simp [hcp]⟩

/-- Entries removed at a crash do not change the state. -/
lemma PI.dropOk (h : PI p C A o rc l ρ) (hres : A.result = none)
    (hk : ¬ (A.CP = true ∧ C.2 p = A.RD)) : ∀ r, ρ = some r → Ok o r := by
  intro r hr
  subst hr
  cases l with
  | c28 old new => obtain ⟨-, -, -, h⟩ := h; simp at h
  | c33 new s =>
    obtain ⟨-, -, -, -, -, -, h⟩ := h
    simp only [reduceCtorEq, Option.some.injEq, false_or] at h; rw [h]; exact ok_false o
  | c34 new s =>
    obtain ⟨-, -, -, -, -, -, -, h⟩ := h
    simp only [reduceCtorEq, Option.some.injEq, false_or] at h; rw [h]; exact ok_false o
  | c35 new s =>
    obtain ⟨-, -, -, -, -, -, -, h⟩ := h
    simp only [reduceCtorEq, Option.some.injEq, false_or] at h; rw [h]; exact ok_false o
  | wres r' =>
    obtain ⟨-, h2, h3, h4⟩ := h
    simp only [Option.some.injEq] at h2; subst h2
    cases hc : A.CP
    · exact h4 hc
    · rw [h3 hc]
      have : ¬ C.2 p = A.RD := fun he => hk ⟨hc, he⟩
      simp only [this, decide_false]; exact ok_false o
  | ret r' =>
    cases r' with
    | none => obtain ⟨-, -, -, h, -⟩ := h; simp at h
    | some r' => obtain ⟨h, -⟩ := h; simp [hres] at h
  | r38 =>
    obtain ⟨-, -, -, h2, h3⟩ := h
    cases hc : A.CP
    · simpa using h2 hres hc
    · have := (h3 hres hc).1; simp only [Option.isSome_some, true_iff] at this
      exact absurd ⟨hc, this⟩ hk
  | r40 =>
    obtain ⟨-, -, -, -, h2, h3⟩ := h
    cases hc : A.CP
    · simpa using h2 hres hc
    · have := (h3 hres hc).1; simp only [Option.isSome_some, true_iff] at this
      exact absurd ⟨hc, this⟩ hk
  | r42 =>
    obtain ⟨-, -, -, -, -, h2, h3⟩ := h
    cases hc : A.CP
    · simpa using h2 hres hc
    · have := (h3 hres hc).1; simp only [Option.isSome_some, true_iff] at this
      exact absurd ⟨hc, this⟩ hk
  | r43 b =>
    obtain ⟨-, -, -, -, -, -, h2, h3⟩ := h
    cases hc : A.CP
    · simpa using h2 hres hc
    · have := (h3 hres hc).1; simp only [Option.isSome_some, true_iff] at this
      exact absurd ⟨hc, this⟩ hk
  | d0 => obtain ⟨-, -, h⟩ := h; simp at h
  | dr => obtain ⟨-, h1, -⟩ := h; exact absurd (h1 hres) (by simp)

/-- The invariant after a crash. -/
lemma PI.crash (h : PI p C A o rc l ρ) (hcp : CPok A o) :
    PI p C A o true (recov o)
      (if A.result ≠ none ∨ (A.CP = true ∧ C.2 p = A.RD) then ρ else none) := by
  obtain ⟨hf1, hf2⟩ := h.crashFacts hcp
  have hop : o = .read ∨ ∃ old new, o = .cas old new := by
    cases o with
    | read => exact .inl rfl
    | cas old new => exact .inr ⟨old, new, rfl⟩
  rcases hop with rfl | ⟨old, new, rfl⟩
  · simp only [CPok] at hcp
    simp only [recov, PI, true_and, hcp, Bool.false_eq_true, false_and, or_false]
    refine ⟨fun hr => by simp [hr], fun r hr => ?_⟩
    simp [hr, hf1 r hr]
  · simp only [recov, PI, true_and, RecOK]
    refine ⟨⟨old, new, rfl⟩, fun r hr => ?_, fun hr hc => by simp [hr, hc], fun hr hc => ?_⟩
    · simp [hr, hf1 r hr]
    · by_cases he : C.2 p = A.RD
      · simp [hr, hc, he, hf2 hr hc he]
      · simp [hr, he]

/-- A process at lines 33–35 that is not linearized holds the current `C` as its snapshot. -/
lemma PI.pre_facts (h : PI p C A o rc l ρ) (hl : l.pre = true) (hρ : ρ = none) :
    ∃ new, o = .cas C.1 new := by
  cases l with
  | c33 new s => obtain ⟨h1, -, -, -, -, h6, -⟩ := h; rw [h6 hρ]; exact ⟨new, h1⟩
  | c34 new s => obtain ⟨h1, -, -, -, -, -, h6, -⟩ := h; rw [h6 hρ]; exact ⟨new, h1⟩
  | c35 new s => obtain ⟨h1, -, -, -, -, -, h6, -⟩ := h; rw [h6 hρ]; exact ⟨new, h1⟩
  | _ => simp [Loc.pre] at hl

/-- The invariant of another process when the shared variable changes (by a successful CAS)
and the linearization is updated. -/
lemma PI.frame {C' : V × (P → Bool)} {ρ' : Option (V ⊕ Bool)} (h : PI p C A o rc l ρ)
    (hC : C'.2 p = C.2 p) (h1 : ρ ≠ none → ρ' = ρ) (h2 : ρ = none → l.pre = true →
      ρ' = some (.inr false)) (h3 : ρ = none → l.pre = false → ρ' = none) :
    PI p C' A o rc l ρ' := by
  by_cases hρ : ρ = none
  · subst hρ
    cases l with
    | c33 new s =>
      obtain ⟨a1, a2, a3, a4, a5, -, -⟩ := h
      rw [h2 rfl rfl]
      exact ⟨a1, a2, a3, a4, hC.trans a5, by simp, by simp⟩
    | c34 new s =>
      obtain ⟨a1, a2, a3, a4, a5, a6, -, -⟩ := h
      rw [h2 rfl rfl]
      exact ⟨a1, a2, a3, a4, a5, hC.trans a6, by simp, by simp⟩
    | c35 new s =>
      obtain ⟨a1, a2, a3, a4, a5, a6, -, -⟩ := h
      rw [h2 rfl rfl]
      exact ⟨a1, a2, a3, a4, a5, hC.trans a6, by simp, by simp⟩
    | ret r => rw [h3 rfl rfl]; cases r <;> simpa [PI, RecOK, hC] using h
    | _ =>
      rw [h3 rfl rfl]
      simpa [PI, RecOK, hC] using h
  · rw [h1 hρ]
    cases l with
    | c33 new s =>
      obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := h
      exact ⟨a1, a2, a3, a4, hC.trans a5, fun h => absurd h hρ, a7⟩
    | c34 new s =>
      obtain ⟨a1, a2, a3, a4, a5, a6, -, a8⟩ := h
      exact ⟨a1, a2, a3, a4, a5, hC.trans a6, fun h => absurd h hρ, a8⟩
    | c35 new s =>
      obtain ⟨a1, a2, a3, a4, a5, a6, -, a8⟩ := h
      exact ⟨a1, a2, a3, a4, a5, hC.trans a6, fun h => absurd h hρ, a8⟩
    | ret r => cases r <;> simpa [PI, RecOK, hC] using h
    | _ => simpa [PI, RecOK, hC] using h

end PIfacts

/-! ### Linearization lemmas specific to CAS -/

/-- Operations `Cas(old, _)` applied to a state `τ ≠ old` all fail and leave the state. -/
lemma runOps_fail (v₀ old : V) :
    ∀ (M : List (ℕ × RCOp V)) (τ : V), (∀ x ∈ M, ∃ n, x.2 = .cas old n) → τ ≠ old →
      (casRC V v₀).runOps τ (M.map Prod.snd) = τ ∧
        ∀ b ∈ M.map Prod.fst, linResp (casRC V v₀) τ M b = some (.inr false) := by
  intro M
  induction M with
  | nil => intro τ _ _; exact ⟨rfl, by simp⟩
  | cons x M ih =>
    intro τ hM hτ
    obtain ⟨n, hn⟩ := hM x (by simp)
    have hδ : (casRC V v₀).δ τ x.2 = (τ, .inr false) := by
      rw [hn]; simp [casRC, hτ]
    obtain ⟨h1, h2⟩ := ih τ (fun y hy => hM y (by simp [hy])) hτ
    refine ⟨by rw [List.map_cons, ObjSpec.runOps_cons, hδ]; exact h1, ?_⟩
    intro b hb
    rw [linResp_cons, hδ]
    split_ifs with hxb
    · rfl
    · simp only [List.map_cons, List.mem_cons] at hb
      rcases hb with hb | hb
      · exact absurd hb.symm hxb
      · exact h2 b hb

lemma linResp_push_ne {O : ObjSpec} (σ : O.State) (L : List (ℕ × O.Op)) (a b : ℕ) (o : O.Op)
    (h : a ≠ b) : linResp O σ (L ++ [(a, o)]) b = linResp O σ L b := by
  rw [linResp_append, linResp_singleton]; simp only [h, ite_false]; cases linResp O σ L b <;> rfl

/-! ### The global invariant -/

section Main

variable (v₀ : V)

/-- The global invariant. -/
structure Inv (C : (alg2fix (P := P) v₀).Cfg) (h : List (HEv P (RCOp V) (V ⊕ Bool)))
    (L : List (ℕ × RCOp V)) : Prop where
  lin : DLin (casRC V v₀) h v₀ L
  val : (casRC V v₀).runOps v₀ (L.map Prod.snd) = C.sh.1
  run : ∀ p a o rc l, C.ps p = .run a o rc l → HEv.inv a p o ∈ h ∧ (∀ r c, HEv.res a r c ∉ h) ∧
    CPok (C.pv p) o ∧ PI p C.sh (C.pv p) o rc l (linResp (casRC V v₀) v₀ L a)
  invlt : ∀ a p o, HEv.inv a p o ∈ h → a < C.cnt
  invu : ∀ a p o p' o', HEv.inv a p o ∈ h → HEv.inv a p' o' ∈ h → p = p' ∧ o = o'
  resinv : ∀ a r c, HEv.res a r c ∈ h → ∃ p o, HEv.inv a p o ∈ h
  pend : ∀ x ∈ L, (∀ r c, HEv.res x.1 r c ∉ h) → ∃ p rc l, C.ps p = .run x.1 x.2 rc l
  nofail : ∀ a, HEv.res a none false ∉ h

variable {v₀}

lemma Inv.uniq {C : (alg2fix (P := P) v₀).Cfg} {h L} (hI : Inv v₀ C h L) {p p' : P} {a : ℕ}
    {o o' : RCOp V} {rc rc' : Bool} {l l' : Loc P V} (hp : C.ps p = .run a o rc l)
    (hp' : C.ps p' = .run a o' rc' l') : p = p' ∧ o = o' :=
  hI.invu a p o p' o' (hI.run p a o rc l hp).1 (hI.run p' a o' rc' l' hp').1

lemma Inv.op_of_mem {C : (alg2fix (P := P) v₀).Cfg} {h L} (hI : Inv v₀ C h L) {x : ℕ × RCOp V}
    (hx : x ∈ L) {p : P} {o : RCOp V} {rc : Bool} {l : Loc P V}
    (hp : C.ps p = .run x.1 o rc l) : x.2 = o := by
  obtain ⟨p', hp'⟩ := hI.lin.inv_of_mem x hx
  exact (hI.invu x.1 p' x.2 p o hp' (hI.run p x.1 o rc l hp).1).2

lemma Inv.lt_cnt {C : (alg2fix (P := P) v₀).Cfg} {h L} (hI : Inv v₀ C h L) {a : ℕ}
    (ha : a ∈ L.map Prod.fst) : a < C.cnt := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  obtain ⟨p, hp⟩ := hI.lin.inv_of_mem x hx
  exact hI.invlt _ _ _ hp

/-- A step of process `q` touching only its own local state and private memory (and possibly
linearizing its operation at the end of `L`, without changing the state). -/
lemma Inv.local {C C' : (alg2fix (P := P) v₀).Cfg} {h L} (hI : Inv v₀ C h L) {q : P} {a : ℕ}
    {o : RCOp V} {rc : Bool} {l : Loc P V} (hq : C.ps q = .run a o rc l) {l' : Loc P V}
    {L' : List (ℕ × RCOp V)}
    (hsh : C'.sh = C.sh) (hcnt : C'.cnt = C.cnt) (hpv : ∀ x, x ≠ q → C'.pv x = C.pv x)
    (hps : C'.ps q = .run a o rc l') (hps' : ∀ x, x ≠ q → C'.ps x = C.ps x)
    (hL : L' = L ∨ (L' = L ++ [(a, o)] ∧ a ∉ L.map Prod.fst ∧
      ((casRC V v₀).δ C.sh.1 o).1 = C.sh.1))
    (hcp : CPok (C'.pv q) o) (hpi : PI q C.sh (C'.pv q) o rc l' (linResp (casRC V v₀) v₀ L' a)) :
    Inv v₀ C' h L' := by
  obtain ⟨hinvq, hpendq, -, -⟩ := hI.run q a o rc l hq
  have hlr : ∀ b, b ≠ a → linResp (casRC V v₀) v₀ L' b = linResp (casRC V v₀) v₀ L b := by
    intro b hb
    rcases hL with rfl | ⟨rfl, -, -⟩
    · rfl
    · exact linResp_push_ne _ _ _ _ _ (Ne.symm hb)
  refine ⟨?_, ?_, ?_, hcnt ▸ hI.invlt, hI.invu, hI.resinv, ?_, hI.nofail⟩
  · rcases hL with rfl | ⟨rfl, ha, -⟩
    · exact hI.lin
    · exact hI.lin.push a q o hinvq hpendq ha
  · rcases hL with rfl | ⟨rfl, -, hδ⟩
    · rw [hsh]; exact hI.val
    · rw [List.map_append, ObjSpec.runOps_append, hI.val, hsh]
      exact hδ
  · intro p a' o' rc' l'' hp
    by_cases hpq : p = q
    · subst hpq
      rw [hps] at hp
      simp only [PSt.run.injEq] at hp
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
      exact ⟨hinvq, hpendq, hcp, hsh ▸ hpi⟩
    · rw [hps' p hpq] at hp
      obtain ⟨h1, h2, h3, h4⟩ := hI.run p a' o' rc' l'' hp
      have hne : a' ≠ a := by
        rintro rfl; exact hpq (hI.uniq hp hq).1
      rw [hpv p hpq, hsh, hlr a' hne]
      exact ⟨h1, h2, h3, h4⟩
  · intro x hx hxp
    have hx' : x ∈ L ∨ x = (a, o) := by
      rcases hL with rfl | ⟨rfl, -, -⟩
      · exact .inl hx
      · simpa using hx
    rcases hx' with hx' | rfl
    · obtain ⟨p, rc', l'', hp⟩ := hI.pend x hx' hxp
      by_cases hpq : p = q
      · subst hpq
        have := hp.symm.trans hq
        simp only [PSt.run.injEq] at this
        obtain ⟨h1, h2, -, -⟩ := this
        exact ⟨p, rc, l', by rw [hps, h1, h2]⟩
      · exact ⟨p, rc', l'', by rw [hps' p hpq, hp]⟩
    · exact ⟨q, rc, l', hps⟩

/-- Process `q` returns. -/
lemma Inv.ret {C C' : (alg2fix (P := P) v₀).Cfg} {h L} (hI : Inv v₀ C h L) {q : P} {a : ℕ}
    {o : RCOp V} {rc : Bool} {r : Option (V ⊕ Bool)} (hq : C.ps q = .run a o rc (.ret r))
    (hsh : C'.sh = C.sh) (hcnt : C'.cnt = C.cnt) (hpv : C'.pv = C.pv)
    (hps : C'.ps q = .idle) (hps' : ∀ x, x ≠ q → C'.ps x = C.ps x) :
    Inv v₀ C' (h ++ [.res a r rc]) L := by
  obtain ⟨hinvq, hpendq, -, hpi⟩ := hI.run q a o rc _ hq
  have hρ : ∀ r', r = some r' → linResp (casRC V v₀) v₀ L a = some r' := by
    rintro r' rfl; exact hpi.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hI.lin.append_res a r rc ?_ (hresp_of_linResp hI.lin.nodup hρ)
    rw [← linResp_isSome (O := casRC V v₀) v₀]
    cases r with
    | none => simp [hpi.2.2.2.1]
    | some r' => simp [hρ r' rfl]
  · rw [hsh]; exact hI.val
  · intro p a' o' rc' l' hp
    have hpq : p ≠ q := by rintro rfl; rw [hps] at hp; cases hp
    rw [hps' p hpq] at hp
    obtain ⟨h1, h2, h3, h4⟩ := hI.run p a' o' rc' l' hp
    have hne : a' ≠ a := by rintro rfl; exact hpq (hI.uniq hp hq).1
    refine ⟨List.mem_append_left _ h1, fun r' c hr => ?_, hpv ▸ h3, hpv ▸ hsh ▸ h4⟩
    rcases List.mem_append.1 hr with hr | hr
    · exact h2 r' c hr
    · simp only [List.mem_singleton, HEv.res.injEq] at hr; exact hne hr.1
  · intro a' p o' ha
    rw [hcnt]
    rcases List.mem_append.1 ha with ha | ha
    · exact hI.invlt _ _ _ ha
    · simp at ha
  · intro a' p o' p' o'' h1 h2
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h1 h2
    exact hI.invu _ _ _ _ _ h1 h2
  · intro a' r' c ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨p, o', hp⟩ := hI.resinv a' r' c ha
      exact ⟨p, o', List.mem_append_left _ hp⟩
    · simp only [List.mem_singleton, HEv.res.injEq] at ha
      obtain ⟨rfl, -, -⟩ := ha
      exact ⟨q, o, List.mem_append_left _ hinvq⟩
  · intro x hx hxp
    obtain ⟨p, rc', l', hp⟩ := hI.pend x hx (fun r' c hr => hxp r' c (List.mem_append_left _ hr))
    have hpq : p ≠ q := by
      rintro rfl
      have := hp.symm.trans hq
      simp only [PSt.run.injEq] at this
      exact hxp r rc (by simp [this.1])
    exact ⟨p, rc', l', by rw [hps' p hpq, hp]⟩
  · intro a' ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hI.nofail a' ha
    · simp only [List.mem_singleton, HEv.res.injEq] at ha
      obtain ⟨-, rfl, rfl⟩ := ha
      exact absurd hpi.1 (by simp)

/-- Process `q` invokes `o`. -/
lemma Inv.invoke {C C' : (alg2fix (P := P) v₀).Cfg} {h L} (hI : Inv v₀ C h L) {q : P}
    {o : RCOp V} (hq : C.ps q = .idle)
    (hsh : C'.sh = C.sh) (hcnt : C'.cnt = C.cnt + 1)
    (hpvq : C'.pv q = { C.pv q with CP := false, result := none })
    (hpv : ∀ x, x ≠ q → C'.pv x = C.pv x)
    (hps : C'.ps q = .run C.cnt o false (start o)) (hps' : ∀ x, x ≠ q → C'.ps x = C.ps x) :
    Inv v₀ C' (h ++ [.inv C.cnt q o]) L := by
  have hnL : C.cnt ∉ L.map Prod.fst := fun h => lt_irrefl _ (hI.lt_cnt h)
  have hnres : ∀ r c, HEv.res C.cnt r c ∉ h := by
    intro r c hr
    obtain ⟨p, o', hp⟩ := hI.resinv _ _ _ hr
    exact lt_irrefl _ (hI.invlt _ _ _ hp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hI.lin.append_noRes _ (by simp) ?_
    intro a p o' ha
    simp only [List.mem_singleton, HEv.inv.injEq] at ha
    rw [ha.1]; exact hnL
  · rw [hsh]; exact hI.val
  · intro p a o' rc l hp
    by_cases hpq : p = q
    · subst hpq
      rw [hps] at hp
      simp only [PSt.run.injEq] at hp
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
      refine ⟨by simp, fun r c hr => ?_, ?_, ?_⟩
      · rcases List.mem_append.1 hr with hr | hr
        · exact hnres r c hr
        · simp at hr
      · rw [hpvq]; cases o <;> simp [CPok]
      · rw [hpvq, (linResp_eq_none _ _ _).2 hnL]
        cases o <;> simp [start, PI]
    · rw [hps' p hpq] at hp
      obtain ⟨h1, h2, h3, h4⟩ := hI.run p a o' rc l hp
      refine ⟨List.mem_append_left _ h1, fun r c hr => ?_, hpv p hpq ▸ h3,
        hpv p hpq ▸ hsh ▸ h4⟩
      rcases List.mem_append.1 hr with hr | hr
      · exact h2 r c hr
      · simp at hr
  · intro a p o' ha
    rw [hcnt]
    rcases List.mem_append.1 ha with ha | ha
    · have := hI.invlt _ _ _ ha; omega
    · simp only [List.mem_singleton, HEv.inv.injEq] at ha; omega
  · intro a p o' p' o'' h1 h2
    rcases List.mem_append.1 h1 with h1 | h1 <;> rcases List.mem_append.1 h2 with h2 | h2
    · exact hI.invu _ _ _ _ _ h1 h2
    · simp only [List.mem_singleton, HEv.inv.injEq] at h2
      have := hI.invlt _ _ _ h1; omega
    · simp only [List.mem_singleton, HEv.inv.injEq] at h1
      have := hI.invlt _ _ _ h2; omega
    · simp only [List.mem_singleton, HEv.inv.injEq] at h1 h2
      exact ⟨h1.2.1.trans h2.2.1.symm, h1.2.2.trans h2.2.2.symm⟩
  · intro a r c ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨p, o', hp⟩ := hI.resinv a r c ha
      exact ⟨p, o', List.mem_append_left _ hp⟩
    · simp at ha
  · intro x hx hxp
    obtain ⟨p, rc, l, hp⟩ := hI.pend x hx (fun r c hr => hxp r c (List.mem_append_left _ hr))
    have hpq : p ≠ q := by rintro rfl; rw [hq] at hp; cases hp
    exact ⟨p, rc, l, by rw [hps' p hpq, hp]⟩
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hI.nofail a ha
    · simp at ha

lemma mem_append_crash {h : List (HEv P (RCOp V) (V ⊕ Bool))} {e : HEv P (RCOp V) (V ⊕ Bool)}
    (he : e ≠ .crash) : e ∈ h ++ [.crash] ↔ e ∈ h := by
  simp [he]

/-- A system-wide crash: entries of crashed processes that did not persist their response and
whose recovery will not return `true` are removed. -/
lemma Inv.crash {C C' : (alg2fix (P := P) v₀).Cfg} {h L} (hI : Inv v₀ C h L)
    (hsh : C'.sh = C.sh) (hcnt : C'.cnt = C.cnt) (hpv : C'.pv = C.pv)
    (hps : ∀ x, C'.ps x = (alg2fix v₀).crashPS x (C.ps x)) :
    ∃ L', Inv v₀ C' (h ++ [.crash]) L' := by
  classical
  let cond : P → Prop := fun p =>
    (C.pv p).result ≠ none ∨ ((C.pv p).CP = true ∧ C.sh.2 p = (C.pv p).RD)
  let K : ℕ → Prop := fun a =>
    (∃ r c, HEv.res a r c ∈ h) ∨ ∃ p o rc l, C.ps p = .run a o rc l ∧ cond p
  let f : ℕ → Bool := fun a => decide (K a)
  have hK : ∀ p a o rc l, C.ps p = .run a o rc l → (K a ↔ cond p) := by
    intro p a o rc l hp
    have hpend := (hI.run p a o rc l hp).2.1
    constructor
    · rintro (⟨r, c, hr⟩ | ⟨p', o', rc', l', hp', hc⟩)
      · exact absurd hr (hpend r c)
      · rw [(hI.uniq hp hp').1]; exact hc
    · intro hc; exact .inr ⟨p, o, rc, l, hp, hc⟩
  have hdrop_pend : ∀ x ∈ L, f x.1 = false → ∀ r c, HEv.res x.1 r c ∉ h := by
    intro x hx hf r c hr
    simp only [f, decide_eq_false_iff_not, K, not_or] at hf
    exact hf.1 ⟨r, c, hr⟩
  have hdrop_pres : ∀ x ∈ L, f x.1 = false → ∀ r, linResp (casRC V v₀) v₀ L x.1 = some r →
      ∀ τ, ((casRC V v₀).δ τ x.2).2 = r → ((casRC V v₀).δ τ x.2).1 = τ := by
    intro x hx hf r hr τ hτ
    obtain ⟨p, rc, l, hp⟩ := hI.pend x hx (hdrop_pend x hx hf)
    have hnc : ¬ cond p := by
      intro hc; simp only [f, decide_eq_false_iff_not] at hf; exact hf ((hK p _ _ _ _ hp).2 hc)
    simp only [cond, not_or, not_not] at hnc
    obtain ⟨-, -, -, hpi⟩ := hI.run p _ _ _ _ hp
    exact (hpi.dropOk hnc.1 hnc.2 r hr).pres τ hτ
  obtain ⟨hfp1, hfp2, -⟩ := filter_pres (O := casRC V v₀) h f v₀ L hI.lin.nodup hdrop_pres
  refine ⟨L.filter (fun x => f x.1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hI.lin.filter f hdrop_pend hdrop_pres).append_noRes [.crash] (by simp) (by simp)
  · rw [hsh, hfp1]; exact hI.val
  · intro p a o rc' l' hp
    rw [hps] at hp
    cases hc : C.ps p with
    | idle => rw [hc] at hp; cases hp
    | run a0 o0 rc0 l0 =>
      rw [hc] at hp
      simp only [RImpl.crashPS, PSt.run.injEq] at hp
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
      obtain ⟨h1, h2, h3, h4⟩ := hI.run p _ _ _ _ hc
      refine ⟨List.mem_append_left _ h1, fun r c' hr => ?_, hpv ▸ h3, ?_⟩
      · rw [mem_append_crash (by simp)] at hr; exact h2 r c' hr
      · have key : linResp (casRC V v₀) v₀ (L.filter (fun x => f x.1)) a0 =
            if (C.pv p).result ≠ none ∨ ((C.pv p).CP = true ∧ C.sh.2 p = (C.pv p).RD) then
              linResp (casRC V v₀) v₀ L a0 else none := by
          split_ifs with hcd
          · exact hfp2 a0 (by simpa [f] using (hK p _ _ _ _ hc).2 hcd)
          · rw [linResp_eq_none]
            intro hm
            obtain ⟨x, hx, hxa⟩ := List.mem_map.1 hm
            have := (List.mem_filter.1 hx).2
            simp only [f, decide_eq_true_eq, hxa] at this
            exact hcd ((hK p _ _ _ _ hc).1 this)
        rw [hpv, hsh, key]
        exact h4.crash h3
  · intro a p o ha
    rw [mem_append_crash (by simp)] at ha
    rw [hcnt]; exact hI.invlt a p o ha
  · intro a p o p' o' h1 h2
    rw [mem_append_crash (by simp)] at h1 h2
    exact hI.invu a p o p' o' h1 h2
  · intro a r c ha
    rw [mem_append_crash (by simp)] at ha
    obtain ⟨p, o, hp⟩ := hI.resinv a r c ha
    exact ⟨p, o, List.mem_append_left _ hp⟩
  · intro x hx hxp
    have hx' := (List.mem_filter.1 hx).1
    obtain ⟨p, rc, l, hp⟩ := hI.pend x hx' (fun r c hr => hxp r c (List.mem_append_left _ hr))
    exact ⟨p, true, recov x.2, by rw [hps, hp]; rfl⟩
  · intro a ha
    rw [mem_append_crash (by simp)] at ha
    exact hI.nofail a ha

/-- A successful hardware CAS (line 35) by `q`: its operation is linearized; every other process
between lines 33 and 35 that is not linearized yet gets a speculative failed entry. -/
lemma Inv.casSucc {C C' : (alg2fix (P := P) v₀).Cfg} {h L} (hI : Inv v₀ C h L) {q : P} {a : ℕ}
    {o : RCOp V} {rc : Bool} {new : V} {s : V × (P → Bool)}
    (hq : C.ps q = .run a o rc (.c35 new s)) (hs : C.sh = s)
    (hsh : C'.sh = (new, Function.update s.2 q (!s.2 q))) (hcnt : C'.cnt = C.cnt)
    (hpv : C'.pv = C.pv) (hps : C'.ps q = .run a o rc (.wres (.inr true)))
    (hps' : ∀ x, x ≠ q → C'.ps x = C.ps x) :
    ∃ L', Inv v₀ C' h L' := by
  classical
  obtain ⟨hinvq, hpendq, hcpq, hpiq⟩ := hI.run q a o rc _ hq
  obtain ⟨ho, hne, hCP, hres, hRD, -, -, h7⟩ := hpiq
  -- the processes to be linearized speculatively
  let Q : ℕ × RCOp V → Prop := fun x => linResp (casRC V v₀) v₀ L x.1 = none ∧
    ∃ p, p ≠ q ∧ ∃ rc' l', C.ps p = .run x.1 x.2 rc' l' ∧ l'.pre = true
  obtain ⟨M, hMnd, hM⟩ := exists_list_of_bounded Q C.cnt
    (by
      rintro x ⟨-, p, -, rc', l', hp, -⟩
      exact hI.invlt _ _ _ (hI.run p _ _ _ _ hp).1)
    (by
      rintro x y ⟨-, p, -, rc', l', hp, -⟩ ⟨-, p', -, rc'', l'', hp', -⟩ hxy
      rw [hxy] at hp
      exact Prod.ext hxy (hI.uniq hp hp').2)
  have hMops : ∀ x ∈ M, ∃ n, x.2 = .cas s.1 n := by
    intro x hx
    obtain ⟨hl, p, -, rc', l', hp, hpre⟩ := (hM x).1 hx
    obtain ⟨-, -, -, hpi⟩ := hI.run p _ _ _ _ hp
    have := hpi.pre_facts hpre hl
    rwa [hs] at this
  have hMq : ∀ x ∈ M, x.1 ≠ a := by
    intro x hx hxa
    obtain ⟨-, p, hpq, rc', l', hp, -⟩ := (hM x).1 hx
    rw [hxa] at hp
    exact hpq (hI.uniq hp hq).1
  have hML : ∀ x ∈ M, x.1 ∉ L.map Prod.fst := by
    intro x hx
    exact (linResp_eq_none _ _ _).1 ((hM x).1 hx).1
  -- removing `q`'s own speculative entry
  let f : ℕ → Bool := fun b => decide (b ≠ a)
  have hdrop_pend : ∀ x ∈ L, f x.1 = false → ∀ r c, HEv.res x.1 r c ∉ h := by
    intro x hx hf
    simp only [f, decide_eq_false_iff_not, not_not] at hf
    rw [hf]; exact hpendq
  have hdrop_pres : ∀ x ∈ L, f x.1 = false → ∀ r, linResp (casRC V v₀) v₀ L x.1 = some r →
      ∀ τ, ((casRC V v₀).δ τ x.2).2 = r → ((casRC V v₀).δ τ x.2).1 = τ := by
    intro x hx hf r hr
    simp only [f, decide_eq_false_iff_not, not_not] at hf
    rw [hf] at hr
    have hr' : r = .inr false := by
      rcases h7 with h7 | h7 <;> rw [h7] at hr <;> simp at hr; exact hr.symm
    subst hr'
    exact (ok_false x.2).pres
  obtain ⟨hfp1, hfp2, -⟩ := filter_pres (O := casRC V v₀) h f v₀ L hI.lin.nodup hdrop_pres
  set L₁ := L.filter (fun x => f x.1) with hL₁
  have hd₁ : DLin (casRC V v₀) h v₀ L₁ := hI.lin.filter f hdrop_pend hdrop_pres
  have haL₁ : a ∉ L₁.map Prod.fst := by
    intro hm
    obtain ⟨x, hx, hxa⟩ := List.mem_map.1 hm
    have := (List.mem_filter.1 hx).2
    simp [f, hxa] at this
  have hsubL : ∀ b ∈ L₁.map Prod.fst, b ∈ L.map Prod.fst :=
    fun b hb => ((List.filter_sublist (l := L)).map Prod.fst).subset hb
  have hd₂ := hd₁.push a q o hinvq hpendq haL₁
  have hnd : ((L₁ ++ [(a, o)] ++ M).map Prod.fst).Nodup := by
    rw [List.map_append]
    refine List.nodup_append.2 ⟨hd₂.nodup, hMnd, ?_⟩
    intro b hb b' hb' hbb
    subst hbb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb'
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_singleton] at hb
    rcases hb with hb | hb
    · exact hML x hx (hsubL _ hb)
    · exact hMq x hx hb
  have hd₃ := DLin.append_pending (O := casRC V v₀) M (L₁ ++ [(a, o)]) hd₂ hnd
    (fun x hx => by
      obtain ⟨-, p, -, rc', l', hp, -⟩ := (hM x).1 hx
      exact ⟨p, (hI.run p _ _ _ _ hp).1⟩)
    (fun x hx => by
      obtain ⟨-, p, -, rc', l', hp, -⟩ := (hM x).1 hx
      exact (hI.run p _ _ _ _ hp).2.1)
  -- states
  have hst₁ : (casRC V v₀).runOps v₀ (L₁.map Prod.snd) = s.1 := by
    rw [hfp1, hI.val, hs]
  have hδq : (casRC V v₀).δ s.1 o = (new, .inr true) := by
    rw [ho]; simp [casRC]
  obtain ⟨hMst, hMresp⟩ := runOps_fail v₀ s.1 M new hMops (Ne.symm hne)
  have hassoc : L₁ ++ [(a, o)] ++ M = L₁ ++ ((a, o) :: M) := by simp
  have hlinq : linResp (casRC V v₀) v₀ (L₁ ++ [(a, o)] ++ M) a = some (.inr true) := by
    rw [hassoc, linResp_append_of_not_mem _ _ _ _ haL₁, hst₁, linResp_cons]
    simp only [↓reduceIte]
    simp [ho]
  have hlinp : ∀ b, b ≠ a → b ∉ L₁.map Prod.fst →
      linResp (casRC V v₀) v₀ (L₁ ++ [(a, o)] ++ M) b = linResp (casRC V v₀) new M b := by
    intro b hba hb
    rw [hassoc, linResp_append_of_not_mem _ _ _ _ hb, hst₁, linResp_cons_of_ne _ _ _ _ (Ne.symm hba),
      hδq]
  refine ⟨L₁ ++ [(a, o)] ++ M, hd₃, ?_, ?_, hcnt ▸ hI.invlt, hI.invu, hI.resinv, ?_, hI.nofail⟩
  · rw [hassoc, List.map_append, ObjSpec.runOps_append, hst₁, List.map_cons, ObjSpec.runOps_cons,
      hδq, hMst, hsh]
  · intro p a' o' rc' l' hp
    by_cases hpq : p = q
    · subst hpq
      rw [hps] at hp
      simp only [PSt.run.injEq] at hp
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
      refine ⟨hinvq, hpendq, hpv ▸ hcpq, ?_⟩
      rw [hpv, hlinq, hsh]
      refine ⟨hres, rfl, fun _ => ?_, fun h => absurd hCP (by simp [h])⟩
      simp [hRD]
    · rw [hps' p hpq] at hp
      obtain ⟨h1, h2, h3, h4⟩ := hI.run p a' o' rc' l' hp
      have hne' : a' ≠ a := by rintro rfl; exact hpq (hI.uniq hp hq).1
      refine ⟨h1, h2, hpv ▸ h3, ?_⟩
      rw [hpv]
      have hfa : f a' = true := by simp [f, hne']
      refine h4.frame (by rw [hsh, hs]; simp [Function.update_of_ne hpq]) ?_ ?_ ?_
      · intro hρ
        have hm : a' ∈ L₁.map Prod.fst := by
          rw [← linResp_isSome (O := casRC V v₀) v₀, hfp2 a' hfa]
          exact Option.isSome_iff_ne_none.2 hρ
        rw [linResp_append_of_mem _ _ _ _ (by simp [hm]), linResp_append_of_mem _ _ _ _ hm,
          hfp2 a' hfa]
      · intro hρ hpre
        have hm₁ : a' ∉ L₁.map Prod.fst := by
          rw [← linResp_eq_none (O := casRC V v₀) v₀, hfp2 a' hfa]; exact hρ
        rw [hlinp a' hne' hm₁]
        exact hMresp a' (List.mem_map.2 ⟨(a', o'), (hM _).2 ⟨hρ, p, hpq, rc', l', hp, hpre⟩, rfl⟩)
      · intro hρ hpre
        have hm₁ : a' ∉ L₁.map Prod.fst := by
          rw [← linResp_eq_none (O := casRC V v₀) v₀, hfp2 a' hfa]; exact hρ
        rw [hlinp a' hne' hm₁, linResp_eq_none]
        intro hm
        obtain ⟨x, hx, hxa⟩ := List.mem_map.1 hm
        obtain ⟨-, p', -, rc'', l'', hp', hpre'⟩ := (hM x).1 hx
        rw [hxa] at hp'
        have := (hI.uniq hp hp').1
        subst this
        rw [hp] at hp'
        simp only [PSt.run.injEq] at hp'
        rw [hp'.2.2.2] at hpre
        rw [hpre] at hpre'
        exact absurd hpre' (by simp)
  · intro x hx hxp
    rw [hassoc] at hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨p, rc', l', hp⟩ := hI.pend x (List.mem_of_mem_filter hx) hxp
      by_cases hpq : p = q
      · subst hpq
        have := hp.symm.trans hq
        simp only [PSt.run.injEq] at this
        exact ⟨p, rc, _, by rw [hps, this.1, this.2.1]⟩
      · exact ⟨p, rc', l', by rw [hps' p hpq, hp]⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨q, rc, _, hps⟩
      · obtain ⟨-, p, hpq, rc', l', hp, -⟩ := (hM x).1 hx
        exact ⟨p, rc', l', by rw [hps' p hpq, hp]⟩

lemma Inv.linResp_push {C : (alg2fix (P := P) v₀).Cfg} {h L} (hI : Inv v₀ C h L) {a : ℕ}
    {o : RCOp V} (ha : a ∉ L.map Prod.fst) :
    linResp (casRC V v₀) v₀ (L ++ [(a, o)]) a = some ((casRC V v₀).δ C.sh.1 o).2 := by
  rw [linResp_append_of_not_mem _ _ _ _ ha, hI.val, linResp_singleton]; simp only [↓reduceIte]

/-- The invariant is preserved by every event. -/
theorem Inv.step {C : (alg2fix (P := P) v₀).Cfg} {h L} (hI : Inv v₀ C h L)
    (e : Ev P (RCOp V)) :
    ∃ L', Inv v₀ ((alg2fix v₀).step1 C e).1 (h ++ ((alg2fix v₀).step1 C e).2) L' := by
  cases e with
  | inv q o =>
    cases hq : C.ps q with
    | run a' o' rc' l' => simp only [RImpl.step1, hq, List.append_nil]; exact ⟨L, hI⟩
    | idle =>
      simp only [RImpl.step1, hq]
      exact ⟨L, hI.invoke hq rfl rfl (by simp) (fun x hx => by simp [Function.update_of_ne hx])
        (by simp) (fun x hx => by simp [Function.update_of_ne hx])⟩
  | crash =>
    simp only [RImpl.step1]
    exact hI.crash rfl rfl rfl (fun x => rfl)
  | step q =>
    cases hq : C.ps q with
    | idle => simp only [RImpl.step1, hq, List.append_nil]; exact ⟨L, hI⟩
    | run a o rc l =>
      obtain ⟨hinv, hpend, hcp, hpi⟩ := hI.run q a o rc l hq
      have hupd : ∀ x, x ≠ q → ∀ (y : PSt (RCOp V) (Loc P V)),
          Function.update C.ps q y x = C.ps x := fun x hx y => Function.update_of_ne hx _ _
      have hupdv : ∀ x, x ≠ q → ∀ (y : Ann V),
          Function.update C.pv q y x = C.pv x := fun x hx y => Function.update_of_ne hx _ _
      cases l with
      | c28 old new =>
        obtain ⟨rfl, hCP, hres, hρ⟩ := hpi
        have haL : a ∉ L.map Prod.fst := (linResp_eq_none _ _ _).1 hρ
        by_cases h1 : C.sh.1 = old
        · by_cases h2 : old = new
          · subst h2
            simp only [RImpl.step1, hq, act, h1, ne_eq, not_true_eq_false,
              and_self, ite_true, ite_false, List.append_nil]
            refine ⟨L ++ [(a, .cas old old)], hI.local hq rfl rfl (fun _ _ => rfl) (Function.update_self _ _ _)
              (fun x hx => hupd x hx _) (.inr ⟨rfl, haL, by simp [h1]⟩) hcp ?_⟩
            rw [hI.linResp_push haL]
            simp [PI, hres, hCP, h1, Ok]
          · simp only [RImpl.step1, hq, act, h1, ne_eq, not_true_eq_false,
              ite_false, h2, and_false, List.append_nil]
            refine ⟨L, hI.local hq rfl rfl (fun _ _ => rfl) (Function.update_self _ _ _)
              (fun x hx => hupd x hx _) (.inl rfl) hcp ?_⟩
            rw [hρ]
            exact ⟨by rw [h1], by rw [h1]; exact h2, hCP, hres, rfl, fun _ => rfl, .inl rfl⟩
        · simp only [RImpl.step1, hq, act, h1, ne_eq, not_false_eq_true, ite_true,
            List.append_nil]
          refine ⟨L ++ [(a, .cas old new)], hI.local hq rfl rfl (fun _ _ => rfl) (Function.update_self _ _ _)
            (fun x hx => hupd x hx _) (.inr ⟨rfl, haL, by simp [h1]⟩) hcp ?_⟩
          rw [hI.linResp_push haL]
          simp [PI, hres, hCP, h1, Ok]
      | c33 new s =>
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hpi
        simp only [RImpl.step1, hq, act, List.append_nil]
        refine ⟨L, hI.local hq rfl rfl (fun x hx => hupdv x hx _) (Function.update_self _ _ _)
          (fun x hx => hupd x hx _) (.inl rfl) ?_ ?_⟩
        · simp only [Function.update_self]; exact hcp
        · simp only [Function.update_self]
          exact ⟨h1, h2, h3, h4, rfl, h5, h6, h7⟩
      | c34 new s =>
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpi
        simp only [RImpl.step1, hq, act, List.append_nil]
        refine ⟨L, hI.local hq rfl rfl (fun x hx => hupdv x hx _) (Function.update_self _ _ _)
          (fun x hx => hupd x hx _) (.inl rfl) ?_ ?_⟩
        · simp only [Function.update_self]; rw [h1]; exact fun _ => h2
        · simp only [Function.update_self]
          exact ⟨h1, h2, rfl, h4, h5, h6, h7, h8⟩
      | c35 new s =>
        by_cases hs : C.sh = s
        · simp only [RImpl.step1, hq, act, hs, ite_true, List.append_nil]
          exact hI.casSucc hq hs rfl rfl rfl (by simp) (fun x hx => hupd x hx _)
        · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpi
          simp only [RImpl.step1, hq, act, hs, ite_false, List.append_nil]
          have hρ : linResp (casRC V v₀) v₀ L a = some (.inr false) := by
            rcases h8 with h8 | h8
            · exact absurd (h7 h8) hs
            · exact h8
          refine ⟨L, hI.local hq rfl rfl (fun _ _ => rfl) (Function.update_self _ _ _)
            (fun x hx => hupd x hx _) (.inl rfl) hcp ?_⟩
          rw [hρ]
          refine ⟨h4, rfl, fun _ => ?_, fun hc => absurd (h3.symm.trans hc) (by simp)⟩
          rw [h6, h5]; cases s.2 q <;> simp
      | wres r =>
        obtain ⟨h1, h2, -, -⟩ := hpi
        simp only [RImpl.step1, hq, act, List.append_nil]
        refine ⟨L, hI.local hq rfl rfl (fun x hx => hupdv x hx _) (Function.update_self _ _ _)
          (fun x hx => hupd x hx _) (.inl rfl) ?_ ?_⟩
        · simp only [Function.update_self]; exact hcp
        · simp only [Function.update_self]
          exact ⟨rfl, h2⟩
      | ret r =>
        simp only [RImpl.step1, hq, act]
        exact ⟨L, hI.ret hq rfl rfl rfl (by simp) (fun x hx => hupd x hx _)⟩
      | r38 =>
        obtain ⟨hrc, hrec⟩ := hpi
        cases hr : (C.pv q).result with
        | some r =>
          simp only [RImpl.step1, hq, act, hr, List.append_nil]
          refine ⟨L, hI.local hq rfl rfl (fun x hx => hupdv x hx _) (Function.update_self _ _ _)
            (fun x hx => hupd x hx _) (.inl rfl) ?_ ?_⟩
          · simpa using hcp
          · simp only [Function.update_self]
            exact ⟨hr, hrec.2.1 r hr⟩
        | none =>
          simp only [RImpl.step1, hq, act, hr, List.append_nil]
          refine ⟨L, hI.local hq rfl rfl (fun x hx => hupdv x hx _) (Function.update_self _ _ _)
            (fun x hx => hupd x hx _) (.inl rfl) ?_ ?_⟩
          · simpa using hcp
          · simp only [Function.update_self]
            exact ⟨hrc, hr, hrec⟩
      | r40 =>
        obtain ⟨hrc, hr, hrec⟩ := hpi
        cases hc : (C.pv q).CP with
        | true =>
          simp only [RImpl.step1, hq, act, hc, ite_true, List.append_nil]
          refine ⟨L, hI.local hq rfl rfl (fun x hx => hupdv x hx _) (Function.update_self _ _ _)
            (fun x hx => hupd x hx _) (.inl rfl) ?_ ?_⟩
          · simpa using hcp
          · simp only [Function.update_self]
            exact ⟨hrc, hr, hc, hrec⟩
        | false =>
          simp only [RImpl.step1, hq, act, hc, Bool.false_eq_true, ite_false,
            List.append_nil]
          refine ⟨L, hI.local hq rfl rfl (fun x hx => hupdv x hx _) (Function.update_self _ _ _)
            (fun x hx => hupd x hx _) (.inl rfl) ?_ ?_⟩
          · simpa using hcp
          · simp only [Function.update_self]
            exact ⟨hrc, hrec.1, hr, hrec.2.2.1 hr hc, fun h => absurd hc (by simp [h])⟩
      | r42 =>
        obtain ⟨hrc, hr, hc, hrec⟩ := hpi
        simp only [RImpl.step1, hq, act, List.append_nil]
        exact ⟨L, hI.local hq rfl rfl (fun _ _ => rfl) (Function.update_self _ _ _)
          (fun x hx => hupd x hx _) (.inl rfl) hcp ⟨hrc, hr, hc, rfl, hrec⟩⟩
      | r43 b =>
        obtain ⟨hrc, hr, hc, hb, hrec⟩ := hpi
        obtain ⟨hiff, htrue⟩ := hrec.2.2.2 hr hc
        by_cases hbr : b = (C.pv q).RD
        · simp only [RImpl.step1, hq, act, hbr, ite_true, List.append_nil]
          refine ⟨L, hI.local hq rfl rfl (fun x hx => hupdv x hx _) (Function.update_self _ _ _)
            (fun x hx => hupd x hx _) (.inl rfl) ?_ ?_⟩
          · simpa using hcp
          · simp only [Function.update_self]
            have hsome := hiff.2 (hb ▸ hbr)
            obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.1 hsome
            rw [hr', htrue r hr']
            exact ⟨hr, rfl, fun _ => by simp [← hb, hbr], fun h => absurd hc (by simp [h])⟩
        · simp only [RImpl.step1, hq, act, hbr, ite_false, List.append_nil]
          refine ⟨L, hI.local hq rfl rfl (fun x hx => hupdv x hx _) (Function.update_self _ _ _)
            (fun x hx => hupd x hx _) (.inl rfl) ?_ ?_⟩
          · simpa using hcp
          · simp only [Function.update_self]
            have hnone : linResp (casRC V v₀) v₀ L a = none := by
              by_contra hne
              exact hbr (hb.trans (hiff.1 (Option.isSome_iff_ne_none.2 hne)))
            exact ⟨hrc, hrec.1, hr, hnone, fun _ => hb ▸ hbr⟩
      | d0 =>
        obtain ⟨rfl, hr, hρ⟩ := hpi
        have haL : a ∉ L.map Prod.fst := (linResp_eq_none _ _ _).1 hρ
        simp only [RImpl.step1, hq, act, List.append_nil]
        refine ⟨L ++ [(a, .read)], hI.local hq rfl rfl (fun _ _ => rfl) (Function.update_self _ _ _)
          (fun x hx => hupd x hx _) (.inr ⟨rfl, haL, rfl⟩) hcp ?_⟩
        rw [hI.linResp_push haL]
        simp only [CPok] at hcp
        exact ⟨hr, rfl, fun h => absurd (h.symm.trans hcp) (by simp), fun _ => trivial⟩
      | dr =>
        obtain ⟨rfl, h1, h2⟩ := hpi
        cases hr : (C.pv q).result with
        | some r =>
          simp only [RImpl.step1, hq, act, hr, List.append_nil]
          refine ⟨L, hI.local hq rfl rfl (fun x hx => hupdv x hx _) (Function.update_self _ _ _)
            (fun x hx => hupd x hx _) (.inl rfl) ?_ ?_⟩
          · simpa using hcp
          · simp only [Function.update_self]
            exact ⟨hr, h2 r hr⟩
        | none =>
          simp only [RImpl.step1, hq, act, hr, List.append_nil]
          refine ⟨L, hI.local hq rfl rfl (fun x hx => hupdv x hx _) (Function.update_self _ _ _)
            (fun x hx => hupd x hx _) (.inl rfl) ?_ ?_⟩
          · simpa using hcp
          · simp only [Function.update_self]
            exact ⟨rfl, hr, h1 hr⟩

end Main

end Alg2Fix

open Alg2Fix

variable {P V : Type} [DecidableEq P] [DecidableEq V]

/-- **Lemma 2 (corrected).** The corrected Algorithm 2 is durably linearizable and detectable. -/
theorem alg2fix_durLinDet (v₀ : V) : (alg2fix (P := P) v₀).DurLinDet := by
  refine (alg2fix v₀).durLinDet_of_inv (Inv v₀) ?_ (fun C h L e _ hI => hI.step e)
    (fun C h L hI => hI.lin) (fun C h L hI => hI.nofail)
  refine ⟨DLin.mk (by simp) (by simp) (by simp) (by simp) (by simp) trivial, rfl, ?_,
    by simp, by simp, by simp, by simp, by simp⟩
  intro p a o rc l hp
  cases hp

/-- **Lemma 2 (corrected), wait-freedom.** -/
theorem alg2fix_boundedSteps (v₀ : V) : (alg2fix (P := P) v₀).BoundedSteps Alg2.μ :=
  alg2Gen_boundedSteps true v₀

theorem alg2fix_obstructionFree (v₀ : V) : (alg2fix (P := P) v₀).ObstructionFree :=
  alg2Gen_obstructionFree true v₀

/-- **Non-vacuity of Theorem 1.** The corrected Algorithm 2 satisfies the hypotheses of the
paper's Theorem 1 (an obstruction-free, durably linearizable and detectable implementation of
the read/CAS object). -/
theorem alg2fix_thm1_hyps (v₀ : V) :
    (alg2fix (P := P) v₀).ObstructionFree ∧ (alg2fix (P := P) v₀).DurLinDet :=
  ⟨alg2fix_obstructionFree v₀, alg2fix_durLinDet v₀⟩

end Papers.PODC2020.DetectableSpace
