import Papers.PODC2026.PartialAuthBC.Broadcast
import Cslib.Computability.Distributed.Byzantine.LockStep.Parallel

/-!
# The simple BA protocol Π_SBA (Figure 3): Theorem 5.1 and Corollary 5.2

Π_SBA reduces Byzantine agreement in the partially authenticated setting to *authenticated*
Byzantine agreement among the `s` registered parties:

1. the registered parties run a black-box authenticated BA protocol `pa` among themselves (on the
   complete graph of `Reg`) for `R` rounds, where `R` bounds the termination time of `pa`;
2. in round `R` every registered party sends its `pa` decision to every unregistered party
   (no signature: the point-to-point channels are authenticated);
3. unregistered parties output (at round `R + 1`) the majority of the values received from
   registered parties (tie → `false`); registered parties output (at round `R`) their `pa` decision.

* `BoundedAuthBA pa Aa Z R`: the black box (unforging, solves authenticated BA against `Z`, all
  honest parties decide within `R` rounds).
* `sba`, `liftAuth`: Π_SBA and its signature structure (tokens of `pa`, signer lifted to `P`);
  `liftAuth_registered`, `sba_unforging`.
* `sba_BA`: the core statement — Π_SBA solves BA whenever the Byzantine registered parties form an
  admissible set for `pa` and are a strict minority of `Reg`; unregistered parties may be corrupted
  arbitrarily.
* `theorem51`: **Theorem 5.1** (`2t < s`); `theorem51_unreg`: the stronger form with any number of
  Byzantine unregistered parties; `theorem51_solvable`: solvability form.
* `corollary52`: **Corollary 5.2** (`t ≤ max{⌈s/2⌉, ⌈n/3⌉} - 1`), with `paper_bound_iff`.
* `theorem51_small`: non-vacuity (for `s ≤ 2` the black box is discharged by `orBA`).
-/

namespace PartialAuthBC

open Cslib.Byzantine.LockStep

/-! ### The black box -/

/-- A deterministic authenticated Byzantine agreement protocol `pa` on parties `N` (complete
network) with signature structure `Aa`, correct against every Byzantine set in `Z`, in which every
honest party decides within `R` rounds. -/
structure BoundedAuthBA {N Ma Sa : Type} (pa : Protocol N Bool Ma Bool) (Aa : Auth N Ma Sa)
    (Z : AdvStructure N) (R : ℕ) : Prop where
  /-- Honest parties only emit their own and relayed signatures. -/
  unforging : pa.Unforging Aa
  /-- Termination, validity, agreement against every admissible unforgeability-respecting
  adversary. -/
  solves : SolvesAuth ⊤ pa Aa Z BA
  /-- Every honest party decides within `R` rounds. -/
  terminates : ∀ sc : Scenario N Bool Ma, sc.byz ∈ Z → sc.Reliable → sc.AuthValid ⊤ pa Aa →
    TerminatesBy ⊤ pa sc R

variable {P : Type} {Ma Sa : Type}

/-! ### The protocol -/

section Defs

variable (Reg : Set P) (pa : Protocol (↥Reg) Bool Ma Bool) (R : ℕ)

/-- The `pa` part of an inbox, restricted to registered senders. -/
def decA (ib : Inbox P (Ma ⊕ Bool)) : Inbox (↥Reg) Ma := fun q => (ib q.1).bind Sum.getLeft?

/-- The first decision of `pa` of the registered party `p` within the first `R` inboxes of `h`. -/
def authOut (p : ↥Reg) (x : Bool) (h : History P (Ma ⊕ Bool)) : Option Bool :=
  firstUpTo (fun r => pa.decide p x ((h.take r).map (decA Reg))) R

open Classical in
/-- Majority of the values received from registered parties (tie → `false`). -/
noncomputable def maj (ib : Inbox P (Ma ⊕ Bool)) : Bool :=
  decide ({q | q ∈ Reg ∧ ib q = some (Sum.inr false)}.ncard <
    {q | q ∈ Reg ∧ ib q = some (Sum.inr true)}.ncard)

open Classical in
/-- **Π_SBA** (Figure 3) with the black-box authenticated BA protocol `pa` among the registered
parties, which terminates within `R` rounds. -/
noncomputable def sba : Protocol P Bool (Ma ⊕ Bool) Bool where
  send p x h q :=
    if hp : p ∈ Reg then
      if h.length < R then
        if hq : q ∈ Reg then (pa.send ⟨p, hp⟩ x (h.map (decA Reg)) ⟨q, hq⟩).map Sum.inl else none
      else if h.length = R ∧ q ∉ Reg then (authOut Reg pa R ⟨p, hp⟩ x h).map Sum.inr
      else none
    else none
  decide p x h :=
    if hp : p ∈ Reg then
      if R ≤ h.length then authOut Reg pa R ⟨p, hp⟩ x h else none
    else (h[R]?).map (maj Reg)

/-- Tokens of Π_SBA: those of the `pa` messages (signer lifted to `P`); the output messages of
step 2 carry none. -/
def liftAuth (Aa : Auth (↥Reg) Ma Sa) : Auth P (Ma ⊕ Bool) Sa where
  signer τ := (Aa.signer τ).1
  tokens m := match m with
    | Sum.inl m => Aa.tokens m
    | Sum.inr _ => ∅

/-- Only registered parties sign. -/
lemma liftAuth_registered (Aa : Auth (↥Reg) Ma Sa) : RegisteredSigners Reg (liftAuth Reg Aa) :=
  fun _ τ _ => (Aa.signer τ).2

variable {Reg pa R}

lemma sba_send_lt {p q : P} {x : Bool} {h : History P (Ma ⊕ Bool)} (hl : h.length < R)
    (hp : p ∈ Reg) (hq : q ∈ Reg) :
    (sba Reg pa R).send p x h q = (pa.send ⟨p, hp⟩ x (h.map (decA Reg)) ⟨q, hq⟩).map Sum.inl := by
  simp [sba, hp, hl, hq]

lemma sba_send_R {p q : P} {x : Bool} {h : History P (Ma ⊕ Bool)} (hl : h.length = R)
    (hp : p ∈ Reg) (hq : q ∉ Reg) :
    (sba Reg pa R).send p x h q = (authOut Reg pa R ⟨p, hp⟩ x h).map Sum.inr := by
  simp [sba, hp, hl, hq]

lemma sba_send_inl {p q : P} {x : Bool} {h : History P (Ma ⊕ Bool)} {m : Ma}
    (hm : (sba Reg pa R).send p x h q = some (Sum.inl m)) :
    ∃ (hp : p ∈ Reg) (hq : q ∈ Reg), h.length < R ∧
      pa.send ⟨p, hp⟩ x (h.map (decA Reg)) ⟨q, hq⟩ = some m := by
  simp only [sba] at hm
  split_ifs at hm with hp hl hq hl'
  · obtain ⟨m', hm', he⟩ := Option.map_eq_some_iff.mp hm
    cases he
    exact ⟨hp, hq, hl, hm'⟩
  · obtain ⟨m', -, he⟩ := Option.map_eq_some_iff.mp hm
    cases he

lemma sba_decide_reg {p : P} {x : Bool} {h : History P (Ma ⊕ Bool)} (hp : p ∈ Reg) :
    (sba Reg pa R).decide p x h = if R ≤ h.length then authOut Reg pa R ⟨p, hp⟩ x h else none := by
  simp [sba, hp]

lemma sba_decide_unreg {p : P} {x : Bool} {h : History P (Ma ⊕ Bool)} (hp : p ∉ Reg) :
    (sba Reg pa R).decide p x h = (h[R]?).map (maj Reg) := by
  simp [sba, hp]

lemma histTokens_decA {Aa : Auth (↥Reg) Ma Sa} {h : History P (Ma ⊕ Bool)} {τ : Sa}
    (hτ : τ ∈ Aa.histTokens (h.map (decA Reg))) : τ ∈ (liftAuth Reg Aa).histTokens h := by
  obtain ⟨ib, hib, q, m, hm, hτm⟩ := hτ
  obtain ⟨ib', hib', rfl⟩ := List.mem_map.mp hib
  simp only [decA, Option.bind_eq_some_iff, Sum.getLeft?_eq_some_iff] at hm
  obtain ⟨_, hq, rfl⟩ := hm
  exact ⟨ib', hib', q.1, Sum.inl m, hq, hτm⟩

/-- Π_SBA is unforging (given that `pa` is). -/
theorem sba_unforging {Aa : Auth (↥Reg) Ma Sa} (hU : pa.Unforging Aa) :
    (sba Reg pa R).Unforging (liftAuth Reg Aa) := by
  intro p x h q m hm τ hτ
  cases m with
  | inl m =>
    obtain ⟨hp, hq, -, hm'⟩ := sba_send_inl hm
    rcases hU _ _ _ _ _ hm' τ hτ with h1 | h1
    · left; show (Aa.signer τ).1 = p; rw [h1]
    · exact Or.inr (histTokens_decA h1)
  | inr b => exact absurd hτ (Set.notMem_empty τ)

end Defs

/-! ### The derived run of `pa` -/

section Run

variable {Reg : Set P} {pa : Protocol (↥Reg) Bool Ma Bool} {R : ℕ}
  (s : Scenario P Bool (Ma ⊕ Bool))

/-- The scenario of `pa` among the registered parties induced by a run of Π_SBA. -/
def scA (Reg : Set P) (s : Scenario P Bool (Ma ⊕ Bool)) : Scenario (↥Reg) Bool Ma where
  byz := {q | q.1 ∈ s.byz}
  input q := s.input q.1
  adv r b q := (s.adv r b.1 q.1).bind Sum.getLeft?
  drop r b q := s.drop r b.1 q.1

@[simp] lemma scA_byz (q : ↥Reg) : q ∈ (scA Reg s).byz ↔ q.1 ∈ s.byz := Iff.rfl
@[simp] lemma scA_input (q : ↥Reg) : (scA Reg s).input q = s.input q.1 := rfl
@[simp] lemma scA_drop (r : ℕ) (b q : ↥Reg) : (scA Reg s).drop r b q = s.drop r b.1 q.1 := rfl
lemma scA_adv (r : ℕ) (b q : ↥Reg) :
    (scA Reg s).adv r b q = (s.adv r b.1 q.1).bind Sum.getLeft? := rfl

lemma scA_reliable (hrel : s.Reliable) : (scA Reg s).Reliable := fun r b q => hrel r b.1 q.1

/-- The first `R` rounds of Π_SBA, seen by a registered party, are a run of `pa`. -/
lemma hist_decA {r : ℕ} (hr : r ≤ R) (p : ↥Reg) :
    (hist ⊤ (sba Reg pa R) s r p.1).map (decA Reg) = hist ⊤ pa (scA Reg s) r p := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    rw [hist_succ, hist_succ, List.map_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil]
    congr 2
    funext q
    by_cases hqp : q = p
    · subst hqp; simp [deliver, decA]
    have hqp' : q.1 ≠ p.1 := fun h => hqp (Subtype.ext h)
    by_cases hqb : q.1 ∈ s.byz
    · simp [deliver, decA, hqp, hqp', hqb, scA_adv]
    by_cases hd : s.drop r q.1 p.1
    · simp [deliver, decA, hqp, hqp', hqb, hd]
    · simp only [deliver, decA, SimpleGraph.top_adj, ne_eq, hqp, hqp', not_false_eq_true,
        ite_true, hqb, ite_false, hd, scA_byz, scA_drop, scA_input]
      rw [sba_send_lt (by rw [length_hist]; omega) q.2 p.2, ih (by omega) q]
      cases pa.send _ _ _ _ <;> rfl

/-- Unforgeability of the adversary transfers to the derived run of `pa`. -/
lemma scA_authValid {Aa : Auth (↥Reg) Ma Sa}
    (hV : s.AuthValid ⊤ (sba Reg pa R) (liftAuth Reg Aa)) :
    (scA Reg s).AuthValid ⊤ pa Aa := by
  intro r b q m hb hq _ hm τ hτ
  rw [scA_adv] at hm
  obtain ⟨m', hm', hm''⟩ := Option.bind_eq_some_iff.mp hm
  obtain ⟨m', rfl⟩ : ∃ m₀, m' = Sum.inl m₀ := by
    cases m' with
    | inl m₀ => exact ⟨m₀, rfl⟩
    | inr _ => simp at hm''
  simp only [Sum.getLeft?_inl, Option.some.injEq] at hm''
  subst hm''
  have hbq : b.1 ≠ q.1 := fun h => hq (show q.1 ∈ s.byz by rw [← h]; exact hb)
  rcases hV r b.1 q.1 _ hb hq (by simpa using hbq) hm' τ hτ with h | ⟨r', hr', p', hp', q', hadj', m₁, hm₁, hτ₁⟩
  · exact Or.inl h
  · right
    cases m₁ with
    | inr _ => exact absurd hτ₁ (Set.notMem_empty τ)
    | inl m₂ =>
      obtain ⟨hpR, hqR, hl, hm₂⟩ := sba_send_inl hm₁
      rw [length_hist] at hl
      have hpq : (⟨p', hpR⟩ : ↥Reg) ≠ ⟨q', hqR⟩ := fun h =>
        hadj'.ne (congrArg Subtype.val h)
      refine ⟨r', hr', ⟨p', hpR⟩, hp', ⟨q', hqR⟩, by simpa using hpq, m₂, ?_, hτ₁⟩
      rw [← hist_decA (R := R) s (by omega)]; exact hm₂

/-- The `k`-th inbox of a history is the inbox delivered in round `k`. -- CSLib candidate -/
lemma hist_getElem? {P I M O : Type*} (G : SimpleGraph P) (alg : Protocol P I M O)
    (s : Scenario P I M) {k r : ℕ} (hk : k < r) (p : P) :
    (hist G alg s r p)[k]? = some (fun q => deliver G alg s (hist G alg s k) k q p) := by
  rw [← List.getElem?_take_of_lt (l := hist G alg s r p) (j := k + 1) (by omega),
    hist_take G alg s (show k + 1 ≤ r by omega), hist_succ, List.getElem?_append_right (by simp)]
  simp

/-- The output of a registered party, computed from its history after round `R`, is the first
decision of `pa` within `R` rounds of the derived run. -/
lemma authOut_hist {r : ℕ} (hr : R ≤ r) {p : P} (hp : p ∈ Reg) :
    authOut Reg pa R ⟨p, hp⟩ (s.input p) (hist ⊤ (sba Reg pa R) s r p) =
      firstUpTo (fun j => status ⊤ pa (scA Reg s) j ⟨p, hp⟩) R := by
  unfold authOut
  apply firstUpTo_congr
  intro j hj
  rw [hist_take _ _ _ (by omega), hist_decA s hj ⟨p, hp⟩]
  rfl

lemma sba_status_reg_lt {r : ℕ} (hr : r < R) {p : P} (hp : p ∈ Reg) :
    status ⊤ (sba Reg pa R) s r p = none := by
  rw [status, sba_decide_reg hp, length_hist]
  simp [show ¬ R ≤ r by omega]

/-- Registered parties decide the first decision of `pa` within `R` rounds. -/
lemma sba_decides_reg {p : P} (hp : p ∈ Reg) (o : Bool) :
    Decides ⊤ (sba Reg pa R) s p o ↔
      firstUpTo (fun j => status ⊤ pa (scA Reg s) j ⟨p, hp⟩) R = some o := by
  rw [decides_iff_firstSome, firstSome_shift R (fun r hr => sba_status_reg_lt s hr hp)]
  have hst : ∀ r, status ⊤ (sba Reg pa R) s (R + r) p =
      firstUpTo (fun j => status ⊤ pa (scA Reg s) j ⟨p, hp⟩) R := by
    intro r
    rw [status, sba_decide_reg hp, length_hist, authOut_hist s (by omega) hp]
    simp
  simp only [hst]
  constructor
  · rintro ⟨r, hr, -⟩; exact hr
  · intro h; exact ⟨0, h, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- Unregistered parties decide the majority of the values received in round `R`. -/
lemma sba_decides_unreg {p : P} (hp : p ∉ Reg) (o : Bool) :
    Decides ⊤ (sba Reg pa R) s p o ↔
      o = maj Reg (fun q => deliver ⊤ (sba Reg pa R) s (hist ⊤ (sba Reg pa R) s R) R q p) := by
  rw [decides_iff_firstSome, firstSome_shift (R + 1) (fun r hr => by
    rw [status, sba_decide_unreg hp]; simp [show r ≤ R by omega])]
  have hst : ∀ r, status ⊤ (sba Reg pa R) s (R + 1 + r) p =
      some (maj Reg (fun q => deliver ⊤ (sba Reg pa R) s (hist ⊤ (sba Reg pa R) s R) R q p)) := by
    intro r
    rw [status, sba_decide_unreg hp, hist_getElem? _ _ _ (by omega)]
    rfl
  simp only [hst]
  constructor
  · rintro ⟨r, hr, -⟩; exact (Option.some_injective _ hr).symm
  · rintro rfl; exact ⟨0, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

end Run

/-! ### Theorem 5.1 -/

section Main

variable [Finite P] {Reg : Set P} {pa : Protocol (↥Reg) Bool Ma Bool} {R : ℕ}

/-- If every honest registered party sends `b` and the Byzantine registered parties are a strict
minority of `Reg`, the majority is `b` (the tie-breaking rule is never used). -/
lemma maj_eq {ib : Inbox P (Ma ⊕ Bool)} {B : Set P} {b : Bool}
    (hB : 2 * (B ∩ Reg).ncard < Reg.ncard)
    (hib : ∀ q ∈ Reg, q ∉ B → ib q = some (Sum.inr b)) : maj Reg ib = b := by
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard Reg B
  have hBR : (Reg ∩ B).ncard = (B ∩ Reg).ncard := by rw [Set.inter_comm]
  have hgood : (Reg \ B).ncard ≤ {q | q ∈ Reg ∧ ib q = some (Sum.inr b)}.ncard :=
    Set.ncard_le_ncard (fun q ⟨hq, hqB⟩ => ⟨hq, hib q hq hqB⟩)
  have hbad : {q | q ∈ Reg ∧ ib q = some (Sum.inr (!b))}.ncard ≤ (B ∩ Reg).ncard := by
    refine Set.ncard_le_ncard (fun q ⟨hq, hqc⟩ => ⟨?_, hq⟩)
    by_contra hqB
    rw [hib q hq hqB] at hqc
    cases b <;> simp at hqc
  unfold maj
  cases b
  · simp only [Bool.not_false] at hbad
    simp only [decide_eq_false_iff_not, not_lt]
    omega
  · simp only [Bool.not_true] at hbad
    simp only [decide_eq_true_eq]
    omega

/-- The core of Theorem 5.1: Π_SBA solves Byzantine agreement as soon as the Byzantine registered
parties form an admissible set for `pa` and a strict minority of `Reg`. The unregistered parties may
be corrupted arbitrarily. -/
theorem sba_BA {Aa : Auth (↥Reg) Ma Sa} {Z : AdvStructure ↥Reg} (hpa : BoundedAuthBA pa Aa Z R)
    (s : Scenario P Bool (Ma ⊕ Bool)) (hZ : {q : ↥Reg | q.1 ∈ s.byz} ∈ Z)
    (hmin : 2 * (s.byz ∩ Reg).ncard < Reg.ncard) (hrel : s.Reliable)
    (hV : s.AuthValid ⊤ (sba Reg pa R) (liftAuth Reg Aa)) :
    BA s.input s.honest (Decides ⊤ (sba Reg pa R) s) := by
  have hrelA := scA_reliable (Reg := Reg) s hrel
  have hVA := scA_authValid s hV
  obtain ⟨-, hval, hagr⟩ := hpa.solves (scA Reg s) hZ hrelA hVA
  have hT := hpa.terminates (scA Reg s) hZ hrelA hVA
  -- the output of an honest registered party is its `pa` decision
  have hout : ∀ p (hp : p ∈ Reg), p ∉ s.byz → ∃ o,
      firstUpTo (fun j => status ⊤ pa (scA Reg s) j ⟨p, hp⟩) R = some o ∧
        Decides ⊤ pa (scA Reg s) ⟨p, hp⟩ o := by
    intro p hp hpb
    obtain ⟨r, hr, o, ho⟩ := hT ⟨p, hp⟩ hpb
    cases hF : firstUpTo (fun j => status ⊤ pa (scA Reg s) j ⟨p, hp⟩) R with
    | none => rw [firstUpTo_eq_none.1 hF r hr] at ho; cases ho
    | some o' => exact ⟨o', rfl, FirstSome.of_firstUpTo hF⟩
  -- some registered party is honest
  obtain ⟨p₀, hp₀R, hp₀⟩ : ∃ p, p ∈ Reg ∧ p ∉ s.byz := by
    by_contra hcon
    push Not at hcon
    rw [Set.inter_eq_right.mpr hcon] at hmin
    omega
  obtain ⟨b, -, hdb₀⟩ := hout p₀ hp₀R hp₀
  -- all honest registered parties output `b`
  have hregb : ∀ p (hp : p ∈ Reg), p ∉ s.byz →
      firstUpTo (fun j => status ⊤ pa (scA Reg s) j ⟨p, hp⟩) R = some b := by
    intro p hp hpb
    obtain ⟨o, ho, hdo⟩ := hout p hp hpb
    rw [ho, hagr ⟨p, hp⟩ hpb ⟨p₀, hp₀R⟩ hp₀ o b hdo hdb₀]
  have hdec : ∀ p ∉ s.byz, ∀ o, Decides ⊤ (sba Reg pa R) s p o ↔ o = b := by
    intro p hpb o
    by_cases hp : p ∈ Reg
    · rw [sba_decides_reg s hp, hregb p hp hpb, Option.some.injEq, eq_comm]
    · rw [sba_decides_unreg s hp, maj_eq hmin]
      intro q hq hqB
      have hqp : q ≠ p := fun h => hp (h ▸ hq)
      rw [deliver_honest ⊤ _ s hrel hqB (by simpa using hqp), sba_send_R (length_hist _ _ _ _ _) hq hp,
        authOut_hist s le_rfl hq, hregb q hq hqB]
      rfl
  refine ⟨fun p hp => ⟨b, (hdec p hp b).2 rfl⟩, fun v hv p hp => (hdec p hp v).2 ?_,
    fun p hp q hq v w hv hw => by rw [(hdec p hp v).1 hv, (hdec q hq w).1 hw]⟩
  exact (Decides.unique _ _ hdb₀ (hval v (fun q hq => hv q.1 hq) ⟨p₀, hp₀R⟩ hp₀)).symm

omit [Finite P] in
lemma ncard_scA_byz (B : Set P) : ({q : ↥Reg | q.1 ∈ B}).ncard = (B ∩ Reg).ncard := by
  have h1 : Subtype.val '' {q : ↥Reg | q.1 ∈ B} = B ∩ Reg := by
    ext x; constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨hq, q.2⟩
    · rintro ⟨hx, hxR⟩; exact ⟨⟨x, hxR⟩, hx, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, h1]

/-- Theorem 5.1 for an arbitrary adversary structure `Z` of the black box. -/
theorem theorem51_general {Aa : Auth (↥Reg) Ma Sa} {Z : AdvStructure ↥Reg}
    (hpa : BoundedAuthBA pa Aa Z R) :
    SolvesAuth ⊤ (sba Reg pa R) (liftAuth Reg Aa)
      {B | {q : ↥Reg | q.1 ∈ B} ∈ Z ∧ 2 * (B ∩ Reg).ncard < Reg.ncard} BA :=
  fun s hs hrel hV => sba_BA hpa s hs.1 hs.2 hrel hV

/-- Theorem 5.1, strengthened: Π_SBA tolerates any Byzantine set containing fewer than `s/2`
registered parties, **with any number of Byzantine unregistered parties**. -/
theorem theorem51_unreg {Aa : Auth (↥Reg) Ma Sa}
    (hpa : BoundedAuthBA pa Aa {B | 2 * B.ncard < Nat.card ↥Reg} R) :
    SolvesAuth ⊤ (sba Reg pa R) (liftAuth Reg Aa) {B | 2 * (B ∩ Reg).ncard < Reg.ncard} BA := by
  intro s hs hrel hV
  refine sba_BA hpa s ?_ hs hrel hV
  show 2 * _ < _
  rw [ncard_scA_byz, Nat.card_coe_set_eq]
  exact hs

/-- **Theorem 5.1.** If `pa` is a deterministic authenticated Byzantine agreement protocol among the
`s` registered parties, tolerating every Byzantine set `B` with `2|B| < s` and terminating within `R`
rounds, then Π_SBA solves Byzantine agreement in the partially authenticated setting against up to
`t` corruptions whenever `2t < s`. -/
theorem theorem51 {Aa : Auth (↥Reg) Ma Sa}
    (hpa : BoundedAuthBA pa Aa {B | 2 * B.ncard < Nat.card ↥Reg} R) {t : ℕ}
    (ht : 2 * t < Reg.ncard) :
    SolvesAuth ⊤ (sba Reg pa R) (liftAuth Reg Aa) (atMost t) BA := by
  intro s hs hrel hV
  refine theorem51_unreg hpa s ?_ hrel hV
  have h1 : (s.byz ∩ Reg).ncard ≤ s.byz.ncard := Set.ncard_inter_le_ncard_left _ _
  have h2 : s.byz.ncard ≤ t := hs
  show 2 * _ < _
  omega

/-- Theorem 5.1 in solvability form. -/
theorem theorem51_solvable (Reg : Set P)
    (h : ∃ (Ma Sa : Type) (pa : Protocol (↥Reg) Bool Ma Bool) (Aa : Auth (↥Reg) Ma Sa) (R : ℕ),
      BoundedAuthBA pa Aa {B | 2 * B.ncard < Nat.card ↥Reg} R)
    {t : ℕ} (ht : 2 * t < Reg.ncard) :
    SolvablePA Reg (atMost t) (BA (V := Bool)) := by
  obtain ⟨Ma, Sa, pa, Aa, R, hpa⟩ := h
  exact ⟨_, _, liftAuth Reg Aa, sba Reg pa R, liftAuth_registered Reg Aa,
    sba_unforging hpa.unforging, theorem51 hpa ht⟩

end Main

/-! ### Corollary 5.2 -/

/-- `t ≤ max{⌈s/2⌉, ⌈n/3⌉} - 1` iff `2t < s` or `3t < n`. -/
lemma paper_bound_iff (s n t : ℕ) :
    t + 1 ≤ max ((s + 1) / 2) ((n + 2) / 3) ↔ 2 * t < s ∨ 3 * t < n := by
  rw [le_max_iff]
  omega

/-- **Corollary 5.2.** Given an authenticated BA protocol among the registered parties for `2t < s`
(e.g. Dolev–Strong-based) and an unauthenticated BA protocol among all parties for `3t < n` (e.g.
phase king), Byzantine agreement is solvable in the partially authenticated setting whenever
`t ≤ max{⌈s/2⌉, ⌈n/3⌉} - 1`. -/
theorem corollary52 [Finite P] (Reg : Set P) (t : ℕ)
    (hauth : 2 * t < Reg.ncard → ∃ (Ma Sa : Type) (pa : Protocol (↥Reg) Bool Ma Bool)
      (Aa : Auth (↥Reg) Ma Sa) (R : ℕ), BoundedAuthBA pa Aa {B | 2 * B.ncard < Nat.card ↥Reg} R)
    (hunauth : 3 * t < Nat.card P → Solvable (⊤ : SimpleGraph P) (atMost t) (BA (V := Bool)))
    (ht : t + 1 ≤ max ((Reg.ncard + 1) / 2) ((Nat.card P + 2) / 3)) :
    SolvablePA Reg (atMost t) (BA (V := Bool)) := by
  rcases (paper_bound_iff _ _ _).1 ht with h | h
  · exact theorem51_solvable Reg (hauth h) h
  · exact Solvable.solvablePA (hunauth h)

/-! ### Non-vacuity -/

/-- For `s ≤ 2` the black box is discharged by `orBA` (the only admissible Byzantine set among the
registered parties is `∅`), with `R = 1`. -/
theorem orBA_boundedAuthBA [Finite P] (Reg : Set P) (hs : Reg.ncard ≤ 2) :
    BoundedAuthBA (orBA ↥Reg) (Auth.none ↥Reg Bool) {B | 2 * B.ncard < Nat.card ↥Reg} 1 := by
  have hB : ∀ B : Set ↥Reg, 2 * B.ncard < Nat.card ↥Reg → B = ∅ := by
    intro B hB
    rw [Nat.card_coe_set_eq] at hB
    exact (Set.ncard_eq_zero (Set.toFinite _)).mp (by omega)
  refine ⟨(orBA _).unforging_none, fun sc hsc hrel _ => orBA_BA sc hrel (hB _ hsc),
    fun sc _ _ _ p _ => ⟨1, le_rfl, ?_⟩⟩
  simp [status, hist_succ, orBA]

/-- Non-vacuity of Theorem 5.1 (strong form): with one or two registered parties, Π_SBA over `orBA`
solves Byzantine agreement against every Byzantine set containing no registered party, i.e. with
**all** `n - s` unregistered parties possibly Byzantine. -/
theorem theorem51_unreg_small [Finite P] (Reg : Set P) (hs : Reg.ncard ≤ 2) :
    SolvesAuth ⊤ (sba Reg (orBA ↥Reg) 1) (liftAuth Reg (Auth.none ↥Reg Bool))
      {B | 2 * (B ∩ Reg).ncard < Reg.ncard} BA :=
  theorem51_unreg (orBA_boundedAuthBA Reg hs)

end PartialAuthBC
