import Papers.PODC2026.PartialAuthBC.Broadcast

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

Π_SBA is the sequential composition (`Protocol.seq`) of `pa`, run among the registered parties by
the committee simulation `Protocol.extend`, with the output step `sbaOut` (steps 2 and 3).

* `BoundedAuthBA pa Aa Z R`: the black box (unforging, solves authenticated BA against `Z`, all
  honest parties decide within `R` rounds).
* `sba`, `liftAuth`: Π_SBA and its signature structure (tokens of `pa`, signer lifted to `P`);
  `liftAuth_registered`, `sba_unforging`; `sba_send_decide`: the composed protocol, spelled out as
  in Figure 3.
* `sba_BA`: the core statement — Π_SBA solves BA whenever the Byzantine registered parties form an
  admissible set for `pa` and are a strict minority of `Reg`; unregistered parties may be corrupted
  arbitrarily.
* `theorem51`: **Theorem 5.1** (`2t < s`); `theorem51_unreg`: the stronger form with any number of
  Byzantine unregistered parties; `theorem51_solvable`: solvability form.
* `corollary52`: **Corollary 5.2** (`t ≤ max{⌈s/2⌉, ⌈n/3⌉} - 1`), with `paper_bound_iff`.
* `theorem51_unreg_small`: non-vacuity (for `s ≤ 2` the black box is discharged by `orBA`).
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

open Classical in
/-- Majority of the values received from registered parties (tie → `false`). -/
noncomputable def maj (ib : Inbox P Bool) : Bool :=
  decide ({q | q ∈ Reg ∧ ib q = some false}.ncard < {q | q ∈ Reg ∧ ib q = some true}.ncard)

open Classical in
/-- Steps 2 and 3 of Π_SBA, on input `o` (the `pa` decision of a registered party, if any): in
its first round every registered party sends `o` to every unregistered party; registered parties
output `o`, unregistered parties output (after one round) the majority of the values received from
registered parties. -/
noncomputable def sbaOut : Protocol P (Option Bool) Bool Bool where
  send p x h q := if p ∈ Reg ∧ q ∉ Reg ∧ h.length = 0 then x else none
  decide p x h := if p ∈ Reg then x else (h[0]?).map (maj Reg)

/-- **Π_SBA** (Figure 3) with the black-box authenticated BA protocol `pa` among the registered
parties, which terminates within `R` rounds: `pa` among the registered parties for `R` rounds,
then `sbaOut` on the first `pa` decision (sequential composition). -/
noncomputable def sba : Protocol P Bool (Ma ⊕ Bool) Bool :=
  (pa.extend Reg).seq R (fun _ _ o => o) (sbaOut Reg)

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

/-- Π_SBA is unforging (given that `pa` is). -/
theorem sba_unforging {Aa : Auth (↥Reg) Ma Sa} (hU : pa.Unforging Aa) :
    (sba Reg pa R).Unforging (liftAuth Reg Aa) :=
  Protocol.Unforging.seq_of_left_right hU.extend
    fun _ _ _ _ _ _ τ hτ => absurd hτ (Set.notMem_empty τ)

/-- The first decision of `pa` (run on the histories of `h`) within `R` rounds. -/
lemma firstDecide_extend {p : P} (hp : p ∈ Reg) (x : Bool) (h : History P (Ma ⊕ Bool))
    (hl : R ≤ h.length) :
    (pa.extend Reg).firstDecide p x (histL (h.take R)) =
      firstUpTo (fun r => pa.decide ⟨p, hp⟩ x (restrictHist Reg (histL (h.take r)))) R := by
  rw [Protocol.firstDecide, show (histL (h.take R)).length = R by simp [histL]; omega]
  refine firstUpTo_congr fun r hr => ?_
  rw [Protocol.extend_decide_of_mem pa hp, histL, ← List.map_take, List.take_take,
    min_eq_left hr]
  rfl

open Classical in
/-- **Π_SBA is the protocol of Figure 3.** A registered party runs `pa` with the registered
parties during the first `R` rounds (on the `pa` messages from registered senders), sends in round
`R` its first `pa` decision `out` to every unregistered party and outputs `out` from round `R`
on; an unregistered party outputs the majority of the values received in round `R`. -/
theorem sba_send_decide (p q : P) (x : Bool) (h : History P (Ma ⊕ Bool)) :
    let out := fun hp : p ∈ Reg =>
      firstUpTo (fun r => pa.decide ⟨p, hp⟩ x (restrictHist Reg (histL (h.take r)))) R
    (sba Reg pa R).send p x h q =
      (if hp : p ∈ Reg then
        if h.length < R then
          if hq : q ∈ Reg then
            (pa.send ⟨p, hp⟩ x (restrictHist Reg (histL h)) ⟨q, hq⟩).map Sum.inl
          else none
        else if h.length = R ∧ q ∉ Reg then (out hp).map Sum.inr else none
      else none) ∧
    (sba Reg pa R).decide p x h =
      (if hp : p ∈ Reg then (if R ≤ h.length then out hp else none)
       else (h[R]?).map fun ib => maj Reg (inboxR ib)) := by
  intro out
  constructor
  · by_cases hl : h.length < R
    · rw [sba, seq_send_lt _ _ _ _ hl]
      by_cases hp : p ∈ Reg
      · by_cases hq : q ∈ Reg
        · simp [hp, hq, hl, Protocol.extend_send_of_mem pa hp hq]
        · simp [Protocol.extend, hp, hq, hl]
      · simp [Protocol.extend, hp]
    · rw [sba, seq_send_ge _ _ _ _ (not_lt.1 hl)]
      by_cases hp : p ∈ Reg
      · simp only [hp, ↓reduceDIte, hl, ↓reduceIte, sbaOut, true_and, List.length_drop,
          Protocol.seqInput, firstDecide_extend hp x h (not_lt.1 hl), histR, List.length_map]
        by_cases hR : h.length = R
        · by_cases hq : q ∈ Reg <;> simp [hR, out, hq]
        · simp [hR, show h.length - R ≠ 0 by omega]
      · simp [sbaOut, hp]
  · by_cases hp : p ∈ Reg
    · by_cases hl : R ≤ h.length
      · simp only [sba, Protocol.seq, not_lt.2 hl, ↓reduceIte, sbaOut, hp, ↓reduceDIte, hl,
          Protocol.seqInput, firstDecide_extend hp x h hl, out]
      · simp [sba, Protocol.seq, lt_of_not_ge hl, hp, hl]
    · by_cases hl : R ≤ h.length
      · simp only [sba, Protocol.seq, not_lt.2 hl, ↓reduceIte, sbaOut, hp, ↓reduceDIte, histR,
          List.getElem?_map, List.getElem?_drop, Nat.add_zero, Option.map_map]
        rfl
      · simp [sba, Protocol.seq, lt_of_not_ge hl, hp,
          List.getElem?_eq_none (by omega : h.length ≤ R)]

end Defs

/-! ### The derived runs -/

section Run

variable {Reg : Set P} {pa : Protocol (↥Reg) Bool Ma Bool} {R : ℕ}
  (s : Scenario P Bool (Ma ⊕ Bool))

/-- The scenario of `pa` among the registered parties induced by a run of Π_SBA. -/
abbrev scA (Reg : Set P) (R : ℕ) (s : Scenario P Bool (Ma ⊕ Bool)) : Scenario (↥Reg) Bool Ma :=
  (s.seqFst R).restrict Reg

lemma scA_reliable (hrel : s.Reliable) : (scA Reg R s).Reliable := fun r b q => hrel r b.1 q.1

/-- Unforgeability of the adversary transfers to the derived run of `pa`. -/
lemma scA_authValid {Aa : Auth (↥Reg) Ma Sa}
    (hV : s.AuthValid ⊤ (sba Reg pa R) (liftAuth Reg Aa)) : (scA Reg R s).AuthValid ⊤ pa Aa :=
  (hV.seqFst_left ⊤ (pa.extend Reg) R _ _).restrict (by simp) pa

/-- The inputs of the second phase: the first `pa` decisions within `R` rounds. -/
local notation "X" => seqInputs ⊤ (pa.extend Reg) R (fun _ _ o => o) s

/-- A registered party starts the second phase with its first `pa` decision within `R` rounds. -/
lemma sba_input {p : P} (hp : p ∈ Reg) :
    X p = firstUpTo (fun j => status ⊤ pa (scA Reg R s) j ⟨p, hp⟩) R := by
  rw [seqInputs_eq_firstUpTo]
  exact firstUpTo_congr fun j _ => status_extend (G' := ⊤) (by simp) pa _ j ⟨p, hp⟩

/-- Registered parties decide the first decision of `pa` within `R` rounds. -/
lemma sba_decides_reg {p : P} (hp : p ∈ Reg) (o : Bool) :
    Decides ⊤ (sba Reg pa R) s p o ↔
      firstUpTo (fun j => status ⊤ pa (scA Reg R s) j ⟨p, hp⟩) R = some o := by
  rw [sba, decides_seq_iff, ← sba_input s hp]
  have hst : ∀ r, status ⊤ (sbaOut Reg) (s.seqSnd R X) r p = X p := fun r => by
    simp [status, sbaOut, hp]
  rcases h : X p with _ | v
  · simp only [reduceCtorEq, iff_false]
    rintro ⟨r, hr, -⟩
    rw [hst, h] at hr
    cases hr
  · rw [Option.some.injEq, eq_comm]
    exact firstSome_iff_of_forall fun r => (hst r).trans h

/-- Unregistered parties decide the majority of the values received in the first round of the
second phase. -/
lemma sba_decides_unreg {p : P} (hp : p ∉ Reg) (o : Bool) :
    Decides ⊤ (sba Reg pa R) s p o ↔ o = maj Reg fun q =>
      deliver ⊤ (sbaOut Reg) (s.seqSnd R X) (hist ⊤ (sbaOut Reg) (s.seqSnd R X) 0) 0 q p := by
  rw [sba, decides_seq_iff, decides_iff_firstSome, firstSome_shift 1 fun r hr => by
    obtain rfl : r = 0 := by omega
    simp [status, sbaOut, hp]]
  refine firstSome_iff_of_forall fun r => ?_
  simp only [status, sbaOut, hp, ↓reduceIte]
  rw [getElem?_hist ⊤ _ _ (by omega)]
  rfl

end Run

/-! ### Theorem 5.1 -/

section Main

variable [Finite P] {Reg : Set P} {pa : Protocol (↥Reg) Bool Ma Bool} {R : ℕ}

/-- If every honest registered party sends `b` and the Byzantine registered parties are a strict
minority of `Reg`, the majority is `b` (the tie-breaking rule is never used). -/
lemma maj_eq {ib : Inbox P Bool} {B : Set P} {b : Bool}
    (hB : 2 * (B ∩ Reg).ncard < Reg.ncard)
    (hib : ∀ q ∈ Reg, q ∉ B → ib q = some b) : maj Reg ib = b := by
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard Reg B
  have hBR : (Reg ∩ B).ncard = (B ∩ Reg).ncard := by rw [Set.inter_comm]
  have hgood : (Reg \ B).ncard ≤ {q | q ∈ Reg ∧ ib q = some b}.ncard :=
    Set.ncard_le_ncard (fun q ⟨hq, hqB⟩ => ⟨hq, hib q hq hqB⟩)
  have hbad : {q | q ∈ Reg ∧ ib q = some (!b)}.ncard ≤ (B ∩ Reg).ncard := by
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
  have hrelA := scA_reliable (Reg := Reg) (R := R) s hrel
  have hVA := scA_authValid s hV
  obtain ⟨-, hval, hagr⟩ := hpa.solves (scA Reg R s) hZ hrelA hVA
  have hT := hpa.terminates (scA Reg R s) hZ hrelA hVA
  -- the output of an honest registered party is its `pa` decision
  have hout : ∀ p (hp : p ∈ Reg), p ∉ s.byz → ∃ o,
      firstUpTo (fun j => status ⊤ pa (scA Reg R s) j ⟨p, hp⟩) R = some o ∧
        Decides ⊤ pa (scA Reg R s) ⟨p, hp⟩ o := by
    intro p hp hpb
    obtain ⟨r, hr, o, ho⟩ := hT ⟨p, hp⟩ hpb
    cases hF : firstUpTo (fun j => status ⊤ pa (scA Reg R s) j ⟨p, hp⟩) R with
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
      firstUpTo (fun j => status ⊤ pa (scA Reg R s) j ⟨p, hp⟩) R = some b := by
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
      rw [deliver_honest ⊤ _ _ (hrel.seqSnd R _) hqB (by simpa using hqp)]
      simp only [sbaOut, hq, hp, not_false_eq_true, hist_zero, List.length_nil, and_self,
        ↓reduceIte, Scenario.seqSnd_input]
      rw [sba_input s hq, hregb q hq hqB]
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
