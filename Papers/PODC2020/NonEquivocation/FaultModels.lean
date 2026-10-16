import Papers.PODC2020.NonEquivocation.Model

/-!
# The space of fault models (Sections 3, 4, 7.2 and Fig. 4)

Madsen–Debois, *On the Subject of Non-Equivocation* (PODC 2020).

Besides `byzantine`, `wne`, `sne` and `omission` (`Model.lean`) we define, in the same message-map
framework,

* `crash`: a faulty `y` has a *crash round* `c`; before round `c` it relays truthfully, after round
  `c` it is silent, and in round `c` every receiver gets either all or none of `y`'s round-`c`
  reports (in the full-information protocol they form one message);
* `authByzLiteral`: the authenticated Byzantine fault model of Section 7.2 *exactly as printed*:
  `∀ p ∈ N, ∀ w' w, σ(w'|p|w) = σ(p|w) ∨ σ(w'|p|w) = ⊥`;
* `authByzRep`: the first natural repair, comparing with what `p` *reports* (`rep σ(p|w)`);
* `authByz`: the repaired model we use: a value about a route through a correct `p` is absent, the
  value `p` reported, or the omission marker `⟨⊥⟩` (nobody can forge `p`'s signature, but anybody can
  claim not to have received a message).

All fault models include Definition 2.1 (`NonFaulty`) and constrain only routes without consecutive
duplicates and of at most `k` rounds.

## Results (Fig. 4)

Inclusions (for all `k F σ`): `omission_of_crash`, `wne_of_omission` (in `Model.lean`),
`authByz_of_omission`, `wne_of_sne`, and the trivial `byzantine_of_wne`, `byzantine_of_authByz`.

Separations (explicit message maps built with `mkσ`, `P = Fin 3` or `Fin 5`, values `Val`):

* `crash_not_le_sne`: a crash during the round-1 broadcast is not strong non-equivocation;
* `sne_crash_silent`: a silent faulty process is in `sne ∩ crash`;
* `omission_not_le_crash`;
* `sne_inter_authByz_not_le_omission` (a faulty process consistently lies about its own value; hence
  also `wne ⊄ omission`, `sne ⊄ crash`, `(wne ∩ authByz) ⊄ omission`);
* `sne_not_le_authByz` (example (1) of §7.2; hence `wne ⊄ authByz`);
* `authByz_not_le_wne` (example (2) of §7.2);
* `paperEx3` (example (3) of §7.2 with `n = 5`, `t = 2`: in `wne ∩ authByz`, not in `omission`).

Defects of the printed definition of Section 7.2:

* `silentσ_not_authByzLiteral`: a crash execution (`k ≥ 2`, all private values present) in which a
  correct process reports an observed omission is **not** in the literal model, contradicting
  "Omission ⊆ AB" of Fig. 4 (a correct `p` reports `⟨⊥⟩ ≠ ⊥ = σ(p|w)`);
* `silentσ_not_authByzRep`: the repair `authByzRep` still excludes crash executions for `k ≥ 3`
  (a correct process relays the `⟨⊥⟩` it observed on a route through another correct process).
-/

namespace NonEquivocation

variable {P V : Type*}

section Defs

variable [OmitVal V]

/-- The faulty process `y` crashes in round `c` (for `k` rounds): it relays truthfully in rounds
`< c`, is silent in rounds `> c`, and in round `c` each receiver gets either all or none of its
round-`c` reports. (`c = 0` means: silent from the start; `c > k`: never crashes.) -/
def CrashesAt (k : ℕ) (σ : MsgMap P V) (y : P) (c : ℕ) : Prop :=
  (∀ x w, Seq (x :: y :: w) → w.length < k → w.length + 1 < c →
      σ (x :: y :: w) = some (rep (σ (y :: w)))) ∧
  (∀ x w, Seq (x :: y :: w) → w.length < k → c < w.length + 1 → σ (x :: y :: w) = none) ∧
  (∀ x,
    (∀ w, Seq (x :: y :: w) → w.length < k → w.length + 1 = c →
      σ (x :: y :: w) = some (rep (σ (y :: w)))) ∨
    (∀ w, Seq (x :: y :: w) → w.length < k → w.length + 1 = c → σ (x :: y :: w) = none))

/-- "`o` is an admissible report about a route through a correct process that reported `rep s`":
absent, the reported value, or the omission marker `⟨⊥⟩`. -/
def Allowed (s o : Option V) : Prop := o = none ∨ o = some (rep s) ∨ o = some omitted

/-- The authenticated Byzantine guarantee **as printed** in Section 7.2:
`∀ p ∈ N : ∀ w', w ∈ P* : σ(w'|p|w) = σ(p|w) ∨ σ(w'|p|w) = ⊥` (routes of at most `k` rounds). -/
def AuthByzLiteral (k : ℕ) (F : Finset P) (σ : MsgMap P V) : Prop :=
  ∀ p, p ∉ F → ∀ w' w : List P, Seq (w' ++ p :: w) → (w' ++ p :: w).length ≤ k + 1 →
    σ (w' ++ p :: w) = σ (p :: w) ∨ σ (w' ++ p :: w) = none

/-- First repair of the authenticated Byzantine guarantee: compare with what the correct `p`
*reports* (`rep σ(p|w)`), not with what it received. Still too strong (`silentσ_not_authByzRep`). -/
def AuthByzRep (k : ℕ) (F : Finset P) (σ : MsgMap P V) : Prop :=
  ∀ p, p ∉ F → ∀ w' w : List P, w' ≠ [] → Seq (w' ++ p :: w) → (w' ++ p :: w).length ≤ k + 1 →
    σ (w' ++ p :: w) = none ∨ σ (w' ++ p :: w) = some (rep (σ (p :: w)))

/-- The authenticated Byzantine guarantee (Section 7.2, repaired): nobody can forge what a correct
`p` reported about `p|w`; a relayed value about `w'|p|w` is absent, `p`'s report, or `⟨⊥⟩` (some
process on the chain claims an omission). -/
def AuthByz (k : ℕ) (F : Finset P) (σ : MsgMap P V) : Prop :=
  ∀ p, p ∉ F → ∀ w' w : List P, w' ≠ [] → Seq (w' ++ p :: w) → (w' ++ p :: w).length ≤ k + 1 →
    σ (w' ++ p :: w) = none ∨ σ (w' ++ p :: w) = some (rep (σ (p :: w))) ∨
      σ (w' ++ p :: w) = some omitted

variable [Fintype P]

/-- The crash fault model (Fig. 4), with Definition 2.1. -/
def crash : FaultModel P V := fun k F σ =>
  NonFaulty k Finset.univ F σ ∧ ∀ y ∈ F, ∃ c, CrashesAt k σ y c

/-- The authenticated Byzantine fault model of Section 7.2, literal reading. -/
def authByzLiteral : FaultModel P V := fun k F σ =>
  NonFaulty k Finset.univ F σ ∧ AuthByzLiteral k F σ

/-- The authenticated Byzantine fault model of Section 7.2, first repair (`rep σ(p|w)`). -/
def authByzRep : FaultModel P V := fun k F σ =>
  NonFaulty k Finset.univ F σ ∧ AuthByzRep k F σ

/-- The authenticated Byzantine fault model of Section 7.2 (repaired; see `AuthByz`). -/
def authByz : FaultModel P V := fun k F σ =>
  NonFaulty k Finset.univ F σ ∧ AuthByz k F σ

end Defs

/-! ### Inclusions -/

section Inclusions

variable [Fintype P] [OmitVal V] {k : ℕ} {F : Finset P} {σ : MsgMap P V}

/-- Fig. 4: Crash ⊆ Omission. -/
theorem omission_of_crash (h : crash k F σ) : omission k F σ := by
  refine ⟨h.1, fun x y w hs hw => ?_⟩
  by_cases hy : y ∈ F
  · obtain ⟨c, h1, h2, h3⟩ := h.2 y hy
    rcases lt_trichotomy (w.length + 1) c with hc | hc | hc
    · exact Or.inr (h1 x w hs hw hc)
    · rcases h3 x with h3 | h3
      · exact Or.inr (h3 w hs hw hc)
      · exact Or.inl (h3 w hs hw hc)
    · exact Or.inl (h2 x w hs hw hc)
  · exact Or.inr (h.1 y (Finset.mem_univ _) hy x (Finset.mem_univ _) w (by simp) hs hw)

/-- Fig. 4 / Section 4: Crash ⊆ WNE. -/
theorem wne_of_crash (h : crash k F σ) : wne k F σ := wne_of_omission (omission_of_crash h)

/-- Fig. 4 (caption): SNE ⊆ WNE. -/
theorem wne_of_sne (h : sne k F σ) : wne k F σ :=
  ⟨h.1, fun p hp r hr r' hr' w hw h₁ h₂ hl _ _ => h.2 p hp r hr r' hr' w hw h₁ h₂ hl⟩

/-- Fig. 4: WNE ⊆ Byzantine. -/
theorem byzantine_of_wne (h : wne k F σ) : byzantine k F σ := h.1

/-- Fig. 4: AB ⊆ Byzantine. -/
theorem byzantine_of_authByz (h : authByz k F σ) : byzantine k F σ := h.1

lemma Allowed.trans {s o o' : Option V} (h : Allowed s o) (h' : Allowed o o') : Allowed s o' := by
  rcases h' with rfl | rfl | rfl
  · exact Or.inl rfl
  · rcases h with rfl | rfl | rfl <;> simp [Allowed]
  · exact Or.inr (Or.inr rfl)

/-- Sufficient condition for the (repaired) authenticated Byzantine model: Definition 2.1, and every
report about a route `y|l` in which some correct process occurs in `l` is admissible (absent, truthful,
or `⟨⊥⟩`). -/
theorem authByz_of (hN : NonFaulty k Finset.univ F σ)
    (h : ∀ x y l, Seq (x :: y :: l) → l.length < k → (∃ p ∈ l, p ∉ F) →
      Allowed (σ (y :: l)) (σ (x :: y :: l))) : authByz k F σ := by
  refine ⟨hN, ?_⟩
  intro p hp w' w hne hs hlen
  show Allowed _ _
  induction w' with
  | nil => exact absurd rfl hne
  | cons x w'' ih =>
    cases w'' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.length_cons] at hs hlen ⊢
      exact Or.inr (Or.inl
        (hN p (Finset.mem_univ _) hp x (Finset.mem_univ _) w (by simp) hs (by omega)))
    | cons y w''' =>
      simp only [List.cons_append, List.length_cons, List.length_append] at hs hlen ⊢
      have hs' : Seq (y :: (w''' ++ p :: w)) := hs.tail
      have h1 := ih (by simp) hs' (by simp; omega)
      exact h1.trans (h x y _ hs (by simp; omega) ⟨p, by simp, hp⟩)

/-- Fig. 4: Omission ⊆ AB (for the repaired `authByz`). -/
theorem authByz_of_omission (h : omission k F σ) : authByz k F σ :=
  authByz_of h.1 fun x y l hs hl _ => by
    rcases h.2 x y l hs hl with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)

/-- Fig. 4: Crash ⊆ AB (for the repaired `authByz`). -/
theorem authByz_of_crash (h : crash k F σ) : authByz k F σ :=
  authByz_of_omission (omission_of_crash h)

end Inclusions

/-! ### Memoryless executions

`mkσ input f`: process `y` sends to `x`, about the route `y :: l`, the value `f x y l o`, where `o`
is what `y` received for `y :: l`. Honest behaviour is `f x y l o = some (rep o)`. -/

section Mk

/-- The message map of a memoryless execution. -/
def mkσ (input : P → Option V) (f : P → P → List P → Option V → Option V) : MsgMap P V
  | [] => none
  | [y] => input y
  | x :: y :: l => f x y l (mkσ input f (y :: l))

variable {input : P → Option V} {f : P → P → List P → Option V → Option V}

@[simp] lemma mkσ_nil : mkσ input f [] = none := rfl
@[simp] lemma mkσ_single (y : P) : mkσ input f [y] = input y := rfl
@[simp] lemma mkσ_cons_cons (x y : P) (l : List P) :
    mkσ input f (x :: y :: l) = f x y l (mkσ input f (y :: l)) := rfl

lemma weakNE_mkσ {k : ℕ} {S : Finset P}
    (h : ∀ x x' y l o, f x y l o ≠ none → f x' y l o ≠ none → f x y l o = f x' y l o) :
    WeakNE k S (mkσ input f) := by
  intro p _ r _ r' _ w _ _ _ _ h₁ h₂
  simp only [mkσ_cons_cons] at h₁ h₂ ⊢
  exact h _ _ _ _ _ h₁ h₂

lemma strongNE_mkσ {k : ℕ} {S : Finset P} (h : ∀ x x' y l o, f x y l o = f x' y l o) :
    StrongNE k S (mkσ input f) := by
  intro p _ r _ r' _ w _ _ _ _
  simp only [mkσ_cons_cons]
  exact h _ _ _ _ _

variable [OmitVal V]

lemma nonFaulty_mkσ {k : ℕ} {S F : Finset P}
    (hN : ∀ x y l o, y ∉ F → f x y l o = some (rep o)) : NonFaulty k S F (mkσ input f) := by
  intro q _ hq p _ w _ _ _
  simp [hN _ _ _ _ hq]

variable [Fintype P] {k : ℕ} {F : Finset P}

lemma omission_mkσ (hN : ∀ x y l o, y ∉ F → f x y l o = some (rep o))
    (h : ∀ x y l o, f x y l o = none ∨ f x y l o = some (rep o)) : omission k F (mkσ input f) :=
  ⟨nonFaulty_mkσ hN, fun x y w _ _ => by simpa using h x y w _⟩

lemma crash_mkσ (hN : ∀ x y l o, y ∉ F → f x y l o = some (rep o))
    (h : ∀ y ∈ F, ∃ c, (∀ x l o, l.length + 1 < c → f x y l o = some (rep o)) ∧
      (∀ x l o, c < l.length + 1 → f x y l o = none) ∧
      ∀ x, (∀ l o, l.length + 1 = c → f x y l o = some (rep o)) ∨
        (∀ l o, l.length + 1 = c → f x y l o = none)) : crash k F (mkσ input f) := by
  refine ⟨nonFaulty_mkσ hN, fun y hy => ?_⟩
  obtain ⟨c, h1, h2, h3⟩ := h y hy
  refine ⟨c, fun x w _ _ hc => by simpa using h1 x w _ hc,
    fun x w _ _ hc => by simpa using h2 x w _ hc, fun x => ?_⟩
  rcases h3 x with h3 | h3
  · exact Or.inl fun w _ _ hc => by simpa using h3 w _ hc
  · exact Or.inr fun w _ _ hc => by simpa using h3 w _ hc

lemma authByz_mkσ (hN : ∀ x y l o, y ∉ F → f x y l o = some (rep o))
    (h : ∀ x y l o, (∃ p ∈ l, p ∉ F) → Allowed o (f x y l o)) : authByz k F (mkσ input f) :=
  authByz_of (nonFaulty_mkσ hN) fun x y l _ _ hp => by simpa using h x y l _ hp

end Mk

/-! ### Separating examples -/

/-- Example values: `omit = ⟨⊥⟩`, and two ordinary values `a ≠ b`. -/
inductive Val
  | omit
  | a
  | b
  deriving DecidableEq, Repr

instance : OmitVal Val := ⟨Val.omit⟩

@[simp] lemma omitted_val : (omitted : Val) = Val.omit := rfl

section Examples

/-- Process `2` is faulty and **silent** from the start (crash round `0`); private values are `a`. -/
def silentσ : MsgMap (Fin 3) Val :=
  mkσ (fun _ => some .a) fun _ y _ o => if y = 2 then none else some (rep o)

/-- Section 3 / Fig. 4: SNE and Crash overlap — a crashed (silent) faulty process. -/
theorem sne_crash_silent (k : ℕ) :
    sne k {2} silentσ ∧ crash k {2} silentσ ∧ ∀ x : Fin 3, silentσ [x, 2] = none := by
  have hN : ∀ (x y : Fin 3) (l : List (Fin 3)) (o : Option Val), y ∉ ({2} : Finset (Fin 3)) →
      (if y = 2 then none else some (rep o)) = some (rep o) := by
    intro x y l o hy; simp_all
  refine ⟨⟨nonFaulty_mkσ hN, strongNE_mkσ fun _ _ _ _ _ => rfl⟩,
    crash_mkσ hN fun y hy => ⟨0, by simp, by simp_all, fun _ => Or.inr (by simp)⟩,
    fun x => by simp [silentσ]⟩

/-- Process `2` crashes **during its round-1 broadcast**: its value reaches `1` but not `0`. -/
def crashBcastσ : MsgMap (Fin 3) Val :=
  mkσ (fun _ => some .a) fun x y l o =>
    if y = 2 then (if l = [] ∧ x ≠ 0 then some (rep o) else none) else some (rep o)

/-- Section 3: Crash ⊄ SNE ("a faulty process can fail during its broadcast"). -/
theorem crash_not_le_sne {k : ℕ} (hk : 1 ≤ k) :
    crash k {2} crashBcastσ ∧ ¬ sne k {2} crashBcastσ := by
  constructor
  · refine crash_mkσ (fun x y l o hy => by simp_all) fun y hy => ⟨1, by simp, ?_, ?_⟩
    · intro x l o hl
      simp at hy; subst hy
      have : l ≠ [] := by rintro rfl; simp at hl
      simp [this]
    · intro x
      simp at hy; subst hy
      by_cases hx : x = 0
      · exact Or.inr fun l o _ => by simp [hx]
      · exact Or.inl fun l o hl => by
          have : l = [] := List.length_eq_zero_iff.mp (by omega)
          simp [this, hx]
  · intro h
    have := h.2 2 (by simp) 0 (by simp) 1 (by simp) [] (by simp) (by simp [Seq])
      (by simp [Seq]) (by simp; omega)
    simp [crashBcastσ] at this

/-- Process `2` omits only its round-1 message to `0` and is otherwise correct. -/
def omitσ : MsgMap (Fin 3) Val :=
  mkσ (fun _ => some .a) fun x y l o => if y = 2 ∧ l = [] ∧ x = 0 then none else some (rep o)

/-- Fig. 4: Omission ⊄ Crash. -/
theorem omission_not_le_crash {k : ℕ} (hk : 2 ≤ k) :
    omission k {2} omitσ ∧ ¬ crash k {2} omitσ := by
  constructor
  · refine omission_mkσ (fun x y l o hy => by simp_all) fun x y l o => ?_
    by_cases h : y = 2 ∧ l = [] ∧ x = 0 <;> simp [h]
  · rintro ⟨-, h⟩
    obtain ⟨c, h1, h2, -⟩ := h 2 (by simp)
    by_cases hc : 2 ≤ c
    · have := h1 0 [] (by simp [Seq]) (by simp; omega) (by simp; omega)
      simp [omitσ] at this
    · have := h2 0 [1] (by simp [Seq]) (by simp; omega) (by simp; omega)
      simp [omitσ] at this

/-- Process `2` consistently lies about its own private value `a`, claiming `b` to everybody. -/
def liarσ : MsgMap (Fin 3) Val :=
  mkσ (fun _ => some .a) fun _ y l o => if y = 2 ∧ l = [] then some .b else some (rep o)

/-- Section 3 / Fig. 4: SNE ⊄ Omission ("a faulty process may lie consistently"); the same σ is in
the (repaired) authenticated Byzantine model. Hence also WNE ⊄ Omission, SNE ⊄ Crash,
(WNE ∩ AB) ⊄ Omission. -/
theorem sne_inter_authByz_not_le_omission {k : ℕ} (hk : 1 ≤ k) :
    sne k {2} liarσ ∧ authByz k {2} liarσ ∧ ¬ omission k {2} liarσ := by
  have hN : ∀ (x y : Fin 3) (l : List (Fin 3)) (o : Option Val), y ∉ ({2} : Finset (Fin 3)) →
      (if y = 2 ∧ l = [] then some Val.b else some (rep o)) = some (rep o) := by
    intro x y l o hy; simp_all
  refine ⟨⟨nonFaulty_mkσ hN, strongNE_mkσ fun _ _ _ _ _ => rfl⟩, authByz_mkσ hN ?_, ?_⟩
  · rintro x y l o ⟨p, hp, -⟩
    have : l ≠ [] := List.ne_nil_of_mem hp
    simp [this, Allowed]
  · rintro ⟨-, h⟩
    have := h 0 2 [] (by simp [Seq]) (by simp; omega)
    simp [liarσ] at this

/-- Corollary: SNE ⊄ Crash (Fig. 4 caption: SNE is "not contained in the crash fault model"). -/
theorem sne_not_le_crash {k : ℕ} (hk : 1 ≤ k) : sne k {2} liarσ ∧ ¬ crash k {2} liarσ :=
  ⟨(sne_inter_authByz_not_le_omission hk).1,
    fun h => (sne_inter_authByz_not_le_omission hk).2.2 (omission_of_crash h)⟩

/-- Example (1) of Section 7.2 (`n = 3`, `t = 1`): the correct source `2` broadcasts `a`; the faulty
`1` reports (to everybody) that it received `b`. -/
def lieAboutCorrectσ : MsgMap (Fin 3) Val :=
  mkσ (fun _ => some .a) fun _ y l o => if y = 1 ∧ l = [2] then some .b else some (rep o)

/-- Section 7.2, example (1): WNE ⊄ AB (even SNE ⊄ AB). -/
theorem sne_not_le_authByz {k : ℕ} (hk : 2 ≤ k) :
    sne k {1} lieAboutCorrectσ ∧ ¬ authByz k {1} lieAboutCorrectσ := by
  refine ⟨⟨nonFaulty_mkσ fun x y l o hy => by simp_all, strongNE_mkσ fun _ _ _ _ _ => rfl⟩, ?_⟩
  rintro ⟨-, h⟩
  have := h 2 (by simp) [0, 1] [] (by simp) (by simp [Seq]) (by simp; omega)
  simp [lieAboutCorrectσ] at this

/-- Example (2) of Section 7.2 (`n = 3`, `t = 1`): the faulty source `2` sends `a` to `0` and `b`
to `1` in round 1; afterwards everybody relays truthfully. -/
def equivσ : MsgMap (Fin 3) Val :=
  mkσ (fun _ => some .a) fun x y l o =>
    if y = 2 ∧ l = [] then (if x = 0 then some .a else some .b) else some (rep o)

/-- Section 7.2, example (2): AB ⊄ WNE. -/
theorem authByz_not_le_wne {k : ℕ} (hk : 1 ≤ k) :
    authByz k {2} equivσ ∧ ¬ wne k {2} equivσ := by
  refine ⟨authByz_mkσ (fun x y l o hy => by simp_all) ?_, ?_⟩
  · rintro x y l o ⟨p, hp, -⟩
    have : l ≠ [] := List.ne_nil_of_mem hp
    simp [this, Allowed]
  · rintro ⟨-, h⟩
    have := h 2 (by simp) 0 (by simp) 1 (by simp) [] (by simp) (by simp [Seq]) (by simp [Seq])
      (by simp; omega) (by simp [equivσ]) (by simp [equivσ])
    simp [equivσ] at this

/-- Example (3) of Section 7.2 (`n = 5`, `t = 2`, correct `p, q, r = 0, 1, 2`, faulty `s, x = 3, 4`):
the source `s` sends its value `a` only to `p` (nothing to `q`, `r`, `x`); `x` acts as if it had
received `b` from `s`; everything else is truthful. -/
def paperEx3σ : MsgMap (Fin 5) Val :=
  mkσ (fun _ => some .a) fun x y l o =>
    if y = 3 ∧ l = [] then (if x = 0 then some (rep o) else none)
    else if y = 4 ∧ l = [3] then some .b else some (rep o)

/-- Section 7.2, example (3): a σ in WNE ∩ AB but not in Omission. -/
theorem paperEx3 {k : ℕ} (hk : 2 ≤ k) :
    wne k {3, 4} paperEx3σ ∧ authByz k {3, 4} paperEx3σ ∧ ¬ omission k {3, 4} paperEx3σ := by
  have hN : ∀ (x y : Fin 5) (l : List (Fin 5)) (o : Option Val),
      y ∉ ({3, 4} : Finset (Fin 5)) →
      (if y = 3 ∧ l = [] then (if x = 0 then some (rep o) else none)
        else if y = 4 ∧ l = [3] then some Val.b else some (rep o)) = some (rep o) := by
    intro x y l o hy
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    simp [hy.1, hy.2]
  refine ⟨⟨nonFaulty_mkσ hN, weakNE_mkσ ?_⟩, authByz_mkσ hN ?_, ?_⟩
  · intro x x' y l o h₁ h₂
    split_ifs at h₁ h₂ ⊢ <;> simp_all
  · rintro x y l o ⟨p, hp, hpF⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpF
    have h1 : l ≠ [] := List.ne_nil_of_mem hp
    have h2 : l ≠ [3] := by rintro rfl; simp at hp; exact hpF.1 hp
    simp [h1, h2, Allowed]
  · rintro ⟨-, h⟩
    have := h 0 4 [3] (by simp [Seq]) (by simp; omega)
    simp [paperEx3σ] at this

/-! ### Defects of the printed authenticated Byzantine model -/

/-- Section 7.2 vs Fig. 4: the literal definition excludes crash executions. In `silentσ` (process `2`
silent, all private values present), the correct `0` observes the omission `σ(0|2) = ⊥` and reports
`⟨⊥⟩` to `1`: `σ(1|0|2) = ⟨⊥⟩`, which is neither `σ(0|2) = ⊥` nor `⊥`. So "Crash ⊆ Omission ⊆ AB"
fails for the literal reading as soon as `k ≥ 2`. -/
theorem silentσ_not_authByzLiteral {k : ℕ} (hk : 2 ≤ k) :
    crash k {2} silentσ ∧ ¬ authByzLiteral k {2} silentσ := by
  refine ⟨(sne_crash_silent k).2.1, ?_⟩
  rintro ⟨-, h⟩
  have := h 0 (by simp) [1] [2] (by simp [Seq]) (by simp; omega)
  simp [silentσ] at this

/-- The first repair `authByzRep` (compare with `rep σ(p|w)`) still excludes crash executions when
`k ≥ 3`: `1` relays the `⟨⊥⟩` it observed on the route `1|2|0` through the correct source `0`, so
`σ(0|1|2|0) = ⟨⊥⟩ ∉ {⊥, a}`. -/
theorem silentσ_not_authByzRep {k : ℕ} (hk : 3 ≤ k) :
    crash k {2} silentσ ∧ ¬ authByzRep k {2} silentσ := by
  refine ⟨(sne_crash_silent k).2.1, ?_⟩
  rintro ⟨-, h⟩
  have := h 0 (by simp) [0, 1, 2] [] (by simp) (by simp [Seq]) (by simp; omega)
  simp [silentσ] at this

/-- For contrast: the repaired `authByz` contains `silentσ` (as every crash execution,
`authByz_of_crash`). -/
example (k : ℕ) : authByz k {2} silentσ := authByz_of_crash (sne_crash_silent k).2.1

/-- For `k = 1` the literal reading is harmless when private values are present: e.g. the round-1
equivocation `equivσ` satisfies it (only routes `x|p` with correct `p` are constrained). -/
theorem equivσ_authByzLiteral_one : authByzLiteral 1 {2} equivσ := by
  refine ⟨nonFaulty_mkσ fun x y l o hy => by simp_all, ?_⟩
  intro p hp w' w hs hlen
  rcases w' with _ | ⟨x, _ | ⟨y, w''⟩⟩
  · simp
  · have hw : w = [] := List.length_eq_zero_iff.mp (by
      simp only [List.length_append, List.length_cons] at hlen; omega)
    subst hw
    simp at hp
    simp [equivσ, hp]
  · exfalso
    simp only [List.length_append, List.length_cons] at hlen; omega

end Examples

end NonEquivocation
