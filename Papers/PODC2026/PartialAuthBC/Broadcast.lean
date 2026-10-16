import Papers.PODC2026.PartialAuthBC.Gradecast

/-!
# The broadcast protocol Π_BC (Figure 2): Theorems 3.13 and 3.14

Π_BC runs Π_GC for `4s` rounds; then the unregistered parties `N = Regᶜ` run a black-box
unauthenticated Byzantine agreement protocol `ba` among themselves (on the complete graph of `N`)
with their gradecast values as inputs. Output rule: registered parties and unregistered parties with
grade `1` output their gradecast value (at round `4s`); unregistered parties with grade `0` output
the decision of `ba`. All parties keep participating in `ba` (registered parties stay silent).

* `bc_decides_*`: decisions of Π_BC in terms of the gradecast run `s₁` and the `ba` run `s₂`.
* `bc_bb_of_honest_reg`, `bc_bb_of_ba`: the two cases of Lemma 3.12 (and Lemma 3.11).
* `theorem313`: Π_BC solves Byzantine broadcast with a registered sender against
  `t ≤ s + ⌈(n - s)/3⌉ - 1` Byzantine parties, if `ba` solves unauthenticated BA among `N` against
  every Byzantine set `B` with `3|B| < |N|`.
* `theorem314`: if `n - s ≤ 2`, Π_BC with the "OR of the values" exchange (`orBA`) solves Byzantine
  broadcast with a registered sender against any number of Byzantine parties (Figure 4).
-/

namespace PartialAuthBC

open Cslib.Byzantine.LockStep

variable {P : Type}

/-- The unregistered parties as a type. -/
abbrev Unreg (Reg : Set P) := ↥(Regᶜ)

section Defs

variable (Reg : Set P) (snd : P) {M' : Type} (ba : Protocol (Unreg Reg) Bool M' Bool)

/-- Gradecast part of an inbox. -/
def dec₁ {M' : Type} (ib : Inbox P (GMsg P ⊕ M')) : Inbox P (GMsg P) :=
  fun q => (ib q).bind Sum.getLeft?

/-- Agreement part of an inbox, restricted to unregistered senders. -/
def dec₂ {M' : Type} (ib : Inbox P (GMsg P ⊕ M')) : Inbox (Unreg Reg) M' :=
  fun q => (ib q.1).bind Sum.getRight?

/-- The gradecast state of `p` (after the first `4s` rounds of `h`). -/
noncomputable def gcOut {M' : Type} (p : P) (x : Bool) (h : History P (GMsg P ⊕ M')) : GSt P :=
  gstOf Reg snd p x ((h.take (4 * Reg.ncard)).map dec₁)

open Classical in
/-- **Π_BC** (Figure 2) with the black-box agreement protocol `ba` among the unregistered parties. -/
noncomputable def bc : Protocol P Bool (GMsg P ⊕ M') Bool where
  send p x h q :=
    if h.length < 4 * Reg.ncard then ((gc Reg snd).send p x (h.map dec₁) q).map Sum.inl
    else if hp : p ∈ Regᶜ then
      if hq : q ∈ Regᶜ then
        (ba.send ⟨p, hp⟩ (gcOut Reg snd p x h).v ((h.drop (4 * Reg.ncard)).map (dec₂ Reg))
          ⟨q, hq⟩).map Sum.inr
      else none
    else none
  decide p x h :=
    if 4 * Reg.ncard ≤ h.length then
      if hp : p ∈ Regᶜ then
        (if (gcOut Reg snd p x h).g then some (gcOut Reg snd p x h).v
         else ba.decide ⟨p, hp⟩ (gcOut Reg snd p x h).v ((h.drop (4 * Reg.ncard)).map (dec₂ Reg)))
      else some (gcOut Reg snd p x h).v
    else none

/-- Tokens of Π_BC: those of the gradecast messages; agreement messages carry none. -/
def bcAuth (M' : Type) : Auth P (GMsg P ⊕ M') (List P) where
  signer := (gAuth Reg snd).signer
  tokens m := match m with
    | Sum.inl m => (gAuth Reg snd).tokens m
    | Sum.inr _ => ∅

lemma bcAuth_registered (M' : Type) : RegisteredSigners Reg (bcAuth Reg snd M') := by
  rintro (m | m) τ hτ
  · exact gAuth_registered Reg snd m τ hτ
  · exact absurd hτ (Set.notMem_empty τ)

lemma histTokens_dec₁ {h : History P (GMsg P ⊕ M')} {τ : List P}
    (hτ : τ ∈ (gAuth Reg snd).histTokens (h.map dec₁)) : τ ∈ (bcAuth Reg snd M').histTokens h := by
  obtain ⟨ib, hib, q, m, hm, hτm⟩ := hτ
  obtain ⟨ib', hib', rfl⟩ := List.mem_map.mp hib
  simp only [dec₁, Option.bind_eq_some_iff, Sum.getLeft?_eq_some_iff] at hm
  obtain ⟨_, hq, rfl⟩ := hm
  exact ⟨ib', hib', q, Sum.inl m, hq, hτm⟩

theorem bc_unforging : (bc Reg snd ba).Unforging (bcAuth Reg snd M') := by
  intro p x h q m hm τ hτ
  simp only [bc] at hm
  split_ifs at hm
  · obtain ⟨m', hm', rfl⟩ := Option.map_eq_some_iff.mp hm
    rcases gc_unforging p x _ q m' hm' τ hτ with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (histTokens_dec₁ Reg snd h1)
  · obtain ⟨m', -, rfl⟩ := Option.map_eq_some_iff.mp hm
    exact absurd hτ (Set.notMem_empty τ)

variable {Reg snd ba}

lemma bc_send_lt {p q : P} {x : Bool} {h : History P (GMsg P ⊕ M')} (hl : h.length < 4 * Reg.ncard) :
    (bc Reg snd ba).send p x h q = ((gc Reg snd).send p x (h.map dec₁) q).map Sum.inl := by
  simp [bc, hl]

lemma bc_send_ge {p q : P} {x : Bool} {h : History P (GMsg P ⊕ M')} (hl : 4 * Reg.ncard ≤ h.length)
    (hp : p ∈ Regᶜ) (hq : q ∈ Regᶜ) :
    (bc Reg snd ba).send p x h q = (ba.send ⟨p, hp⟩ (gcOut Reg snd p x h).v
      ((h.drop (4 * Reg.ncard)).map (dec₂ Reg)) ⟨q, hq⟩).map Sum.inr := by
  simp [bc, Nat.not_lt.mpr hl, hp, hq]

open Classical in
lemma bc_decide_ge {p : P} {x : Bool} {h : History P (GMsg P ⊕ M')} (hl : 4 * Reg.ncard ≤ h.length) :
    (bc Reg snd ba).decide p x h =
      if hp : p ∈ Regᶜ then
        (if (gcOut Reg snd p x h).g then some (gcOut Reg snd p x h).v
         else ba.decide ⟨p, hp⟩ (gcOut Reg snd p x h).v ((h.drop (4 * Reg.ncard)).map (dec₂ Reg)))
      else some (gcOut Reg snd p x h).v := by
  simp [bc, hl]

end Defs

/-! ### The derived runs -/

section Runs

variable {Reg : Set P} {snd : P} {M' : Type} {ba : Protocol (Unreg Reg) Bool M' Bool}
  (s : Scenario P Bool (GMsg P ⊕ M'))

local notation "T" => 4 * Reg.ncard

/-- The gradecast scenario (first `4s` rounds). -/
noncomputable def sc₁ (Reg : Set P) (s : Scenario P Bool (GMsg P ⊕ M')) : Scenario P Bool (GMsg P) where
  byz := s.byz
  input := s.input
  adv r b q := if r < 4 * Reg.ncard then (s.adv r b q).bind Sum.getLeft? else none
  drop := s.drop

/-- The agreement scenario among the unregistered parties (rounds `≥ 4s`). -/
noncomputable def sc₂ (Reg : Set P) (snd : P) (s : Scenario P Bool (GMsg P ⊕ M')) :
    Scenario (Unreg Reg) Bool M' where
  byz := {q | q.1 ∈ s.byz}
  input q := (gS (sc₁ Reg s) Reg snd (4 * Reg.ncard) q.1).v
  adv r b q := (s.adv (4 * Reg.ncard + r) b.1 q.1).bind Sum.getRight?
  drop r b q := s.drop (4 * Reg.ncard + r) b.1 q.1

@[simp] lemma sc₁_byz : (sc₁ Reg s).byz = s.byz := rfl
@[simp] lemma sc₁_input : (sc₁ Reg s).input = s.input := rfl
@[simp] lemma sc₁_drop : (sc₁ Reg s).drop = s.drop := rfl
lemma sc₁_adv (r : ℕ) (b q : P) : (sc₁ Reg s).adv r b q =
    if r < 4 * Reg.ncard then (s.adv r b q).bind Sum.getLeft? else none := rfl
@[simp] lemma sc₂_byz (q : Unreg Reg) : q ∈ (sc₂ Reg snd s).byz ↔ q.1 ∈ s.byz := Iff.rfl
@[simp] lemma sc₂_drop (r : ℕ) (b q : Unreg Reg) :
    (sc₂ Reg snd s).drop r b q = s.drop (4 * Reg.ncard + r) b.1 q.1 := rfl
lemma sc₂_adv (r : ℕ) (b q : Unreg Reg) :
    (sc₂ Reg snd s).adv r b q = (s.adv (4 * Reg.ncard + r) b.1 q.1).bind Sum.getRight? := rfl
lemma sc₂_input (q : Unreg Reg) :
    (sc₂ Reg snd s).input q = (gS (sc₁ Reg s) Reg snd (4 * Reg.ncard) q.1).v := rfl

/-- The first `4s` rounds of Π_BC are a run of Π_GC. -/
lemma hist_dec₁ {r : ℕ} (hr : r ≤ T) (p : P) :
    (hist ⊤ (bc Reg snd ba) s r p).map dec₁ = hist ⊤ (gc Reg snd) (sc₁ Reg s) r p := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    rw [hist_succ, hist_succ, List.map_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil]
    congr 2
    funext q
    by_cases hqp : q = p
    · subst hqp; simp [deliver, dec₁]
    by_cases hqb : q ∈ s.byz
    · simp [deliver, dec₁, hqp, hqb, sc₁_adv, show r < T by omega]
    by_cases hd : s.drop r q p
    · simp [deliver, dec₁, hqp, hqb, hd]
    · simp only [deliver, dec₁, SimpleGraph.top_adj, ne_eq, hqp, not_false_eq_true, ite_true,
        hqb, ite_false, hd, sc₁_byz, sc₁_drop, sc₁_input]
      rw [bc_send_lt (by rw [length_hist]; omega), ih (by omega)]
      cases (gc Reg snd).send _ _ _ _ <;> rfl

lemma gcOut_hist {r : ℕ} (hr : T ≤ r) (p : P) :
    gcOut Reg snd p (s.input p) (hist ⊤ (bc Reg snd ba) s r p) = gS (sc₁ Reg s) Reg snd T p := by
  unfold gcOut gS
  rw [hist_take _ _ _ hr, hist_dec₁ s le_rfl]; rfl

lemma sc₁_reliable (hrel : s.Reliable) : (sc₁ Reg s).Reliable := hrel

lemma sc₁_authValid (hV : s.AuthValid ⊤ (bc Reg snd ba) (bcAuth Reg snd M')) :
    (sc₁ Reg s).AuthValid ⊤ (gc Reg snd) (gAuth Reg snd) := by
  intro r b q m hb hq hadj hm τ hτ
  simp only [sc₁] at hm
  split_ifs at hm with hr
  obtain ⟨m', hm', hm''⟩ := Option.bind_eq_some_iff.mp hm
  obtain ⟨m', rfl⟩ : ∃ m₀, m' = Sum.inl m₀ := by
    cases m' with
    | inl m₀ => exact ⟨m₀, rfl⟩
    | inr _ => simp at hm''
  simp only [Sum.getLeft?_inl, Option.some.injEq] at hm''
  subst hm''
  rcases hV r b q _ hb hq hadj hm' τ hτ with h | ⟨r', hr', p', hp', q', hadj', m₁, hm₁, hτ₁⟩
  · exact Or.inl h
  · right
    simp only [bc, length_hist, show r' < T by omega, ite_true] at hm₁
    obtain ⟨m₂, hm₂, rfl⟩ := Option.map_eq_some_iff.mp hm₁
    refine ⟨r', hr', p', hp', q', hadj', m₂, ?_, hτ₁⟩
    rw [← hist_dec₁ s (by omega)]; exact hm₂

/-- Rounds `≥ 4s` of Π_BC are a run of `ba` among the unregistered parties. -/
lemma hist_dec₂ (r : ℕ) (p : Unreg Reg) :
    ((hist ⊤ (bc Reg snd ba) s (T + r) p.1).drop T).map (dec₂ Reg) =
      hist ⊤ ba (sc₂ Reg snd s) r p := by
  induction r generalizing p with
  | zero => simp
  | succ r ih =>
    rw [← add_assoc, hist_succ, hist_succ, List.drop_append_of_le_length (by simp),
      List.map_append, ih]
    simp only [List.map_cons, List.map_nil]
    congr 2
    funext q
    by_cases hqp : q = p
    · subst hqp; simp [deliver, dec₂]
    have hqp' : q.1 ≠ p.1 := fun h => hqp (Subtype.ext h)
    by_cases hqb : q.1 ∈ s.byz
    · simp [deliver, dec₂, hqp, hqp', hqb, sc₂_adv]
    by_cases hd : s.drop (T + r) q.1 p.1
    · simp [deliver, dec₂, hqp, hqp', hqb, hd]
    · simp only [deliver, dec₂, SimpleGraph.top_adj, ne_eq, hqp, hqp', not_false_eq_true,
        ite_true, hqb, ite_false, hd, sc₂_byz, sc₂_drop, sc₂_input]
      rw [bc_send_ge (by rw [length_hist]; omega) q.2 p.2, gcOut_hist s (by omega), ih q]
      cases ba.send _ _ _ _ <;> rfl

/-- `FirstSome` after `n` silent steps. -- CSLib candidate -/
lemma firstSome_shift {O : Type*} {f : ℕ → Option O} (n : ℕ) (hf : ∀ r < n, f r = none) (o : O) :
    FirstSome f o ↔ FirstSome (fun r => f (n + r)) o := by
  constructor
  · rintro ⟨r, hr, hlt⟩
    have hnr : n ≤ r := by by_contra h; rw [hf r (by omega)] at hr; simp at hr
    exact ⟨r - n, by simp [Nat.add_sub_cancel' hnr, hr], fun r' hr' => hlt _ (by omega)⟩
  · rintro ⟨r, hr, hlt⟩
    refine ⟨n + r, hr, fun r' hr' => ?_⟩
    rcases Nat.lt_or_ge r' n with h | h
    · exact hf r' h
    · have := hlt (r' - n) (by omega); simp only at this; rwa [Nat.add_sub_cancel' h] at this

lemma bc_status_lt {r : ℕ} (hr : r < T) (p : P) : status ⊤ (bc Reg snd ba) s r p = none := by
  simp [status, bc, length_hist, show ¬ T ≤ r by omega]

/-- Registered parties and parties with grade `1` decide their gradecast value. -/
lemma bc_decides_of_g {p : P} (hp : p ∈ Reg ∨ (gS (sc₁ Reg s) Reg snd T p).g = true) (o : Bool) :
    Decides ⊤ (bc Reg snd ba) s p o ↔ o = (gS (sc₁ Reg s) Reg snd T p).v := by
  rw [decides_iff_firstSome, firstSome_shift T (fun r hr => bc_status_lt s hr p)]
  have hst : ∀ r, status ⊤ (bc Reg snd ba) s (T + r) p = some (gS (sc₁ Reg s) Reg snd T p).v := by
    intro r
    rw [status, bc_decide_ge (by rw [length_hist]; omega), gcOut_hist s (by omega)]
    split_ifs with h1 h2
    · rfl
    · rcases hp with hp | hp
      · exact absurd hp h1
      · simp_all
    · rfl
  constructor
  · rintro ⟨r, hr, -⟩; simp only [hst] at hr; exact (Option.some_injective _ hr).symm
  · rintro rfl; exact ⟨0, hst 0, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- Unregistered parties with grade `0` decide what `ba` decides. -/
lemma bc_decides_of_g0 (p : Unreg Reg) (hp : (gS (sc₁ Reg s) Reg snd T p.1).g = false) (o : Bool) :
    Decides ⊤ (bc Reg snd ba) s p.1 o ↔ Decides ⊤ ba (sc₂ Reg snd s) p o := by
  rw [decides_iff_firstSome, firstSome_shift T (fun r hr => bc_status_lt s hr p.1)]
  apply FirstSome.congr
  intro r
  rw [status, bc_decide_ge (by rw [length_hist]; omega)]
  simp only [p.2, ↓reduceDIte]
  rw [gcOut_hist s (by omega), hp, hist_dec₂ s r p]
  rfl

end Runs

/-! ### Lemmas 3.11 and 3.12 -/

section Main

variable [Finite P] {Reg : Set P} {snd : P} {M' : Type} {ba : Protocol (Unreg Reg) Bool M' Bool}
  (s : Scenario P Bool (GMsg P ⊕ M')) (hsR : snd ∈ Reg) (hrel : s.Reliable)
  (hV : s.AuthValid ⊤ (bc Reg snd ba) (bcAuth Reg snd M'))

local notation "T" => 4 * Reg.ncard

include hsR hrel hV

/-- Lemmas 3.11/3.12, case 1: if some registered party is honest, Π_BC satisfies broadcast. -/
theorem bc_bb_of_honest_reg {k : P} (hk : k ∉ s.byz) (hkR : k ∈ Reg) :
    BB snd s.input s.honest (Decides ⊤ (bc Reg snd ba) s) := by
  have hrel₁ := sc₁_reliable (Reg := Reg) s hrel
  have hV₁ := sc₁_authValid s hV
  have hdec : ∀ p ∉ s.byz, ∀ o, Decides ⊤ (bc Reg snd ba) s p o ↔
      o = (gS (sc₁ Reg s) Reg snd T p).v := fun p hp o =>
    bc_decides_of_g s (Or.inr (lemma310 (sc₁ Reg s) hrel₁ hV₁ hsR hk hkR hp)) o
  refine ⟨fun p hp => ⟨_, (hdec p hp _).2 rfl⟩, fun hsnd p hp => ?_, fun p hp q hq v w hv hw => ?_⟩
  · rw [hdec p hp]; exact ((lemma36 (sc₁ Reg s) hrel₁ hV₁ hsR hsnd hp).1).symm
  · rw [hdec p hp] at hv; rw [hdec q hq] at hw
    rw [hv, hw, lemma35 (sc₁ Reg s) hrel₁ hV₁ hsR hk hkR hp,
      lemma35 (sc₁ Reg s) hrel₁ hV₁ hsR hk hkR hq]

/-- Lemma 3.12, case 2: if all registered parties are Byzantine and `ba` satisfies Byzantine
agreement among the unregistered parties, Π_BC satisfies broadcast. -/
theorem bc_bb_of_ba (hReg : Reg ⊆ s.byz)
    (hba : BA (sc₂ Reg snd s).input (sc₂ Reg snd s).honest (Decides ⊤ ba (sc₂ Reg snd s))) :
    BB snd s.input s.honest (Decides ⊤ (bc Reg snd ba) s) := by
  have hrel₁ := sc₁_reliable (Reg := Reg) s hrel
  have hV₁ := sc₁_authValid s hV
  have hN : ∀ p ∉ s.byz, p ∈ Regᶜ := fun p hp hpR => hp (hReg hpR)
  obtain ⟨hterm, hval, hagr⟩ := hba
  -- every honest party decides `v` if it has grade `1`, otherwise the `ba` decision
  have hdec : ∀ p (hp : p ∉ s.byz), ∀ o, Decides ⊤ (bc Reg snd ba) s p o ↔
      ((gS (sc₁ Reg s) Reg snd T p).g = true ∧ o = (gS (sc₁ Reg s) Reg snd T p).v) ∨
      ((gS (sc₁ Reg s) Reg snd T p).g = false ∧ Decides ⊤ ba (sc₂ Reg snd s) ⟨p, hN p hp⟩ o) := by
    intro p hp o
    rcases Bool.eq_false_or_eq_true (gS (sc₁ Reg s) Reg snd T p).g with hg | hg
    · rw [bc_decides_of_g s (Or.inr hg)]; simp [hg]
    · have := bc_decides_of_g0 (ba := ba) s ⟨p, hN p hp⟩ hg o
      rw [this]; simp [hg]
  refine ⟨fun p hp => ?_, fun hsnd => absurd (hReg hsR) hsnd, fun p hp q hq v w hv hw => ?_⟩
  · rcases Bool.eq_false_or_eq_true (gS (sc₁ Reg s) Reg snd T p).g with hg | hg
    · exact ⟨_, (hdec p hp _).2 (Or.inl ⟨hg, rfl⟩)⟩
    · obtain ⟨o, ho⟩ := hterm ⟨p, hN p hp⟩ hp
      exact ⟨o, (hdec p hp _).2 (Or.inr ⟨hg, ho⟩)⟩
  · rw [hdec p hp] at hv; rw [hdec q hq] at hw
    by_cases hj : ∃ j, j ∉ s.byz ∧ (gS (sc₁ Reg s) Reg snd T j).g = true
    · -- Case 2a: some honest party has grade 1; all honest values agree and `ba` keeps them
      obtain ⟨j, hj, hgj⟩ := hj
      have hall : ∀ p ∉ s.byz, (gS (sc₁ Reg s) Reg snd T p).v = (gS (sc₁ Reg s) Reg snd T j).v :=
        fun p hp => lemma37 (sc₁ Reg s) hrel₁ hV₁ hsR hj hp hgj
      have hbaval := hval (gS (sc₁ Reg s) Reg snd T j).v (fun p hp => hall p.1 hp)
      have key : ∀ p (hp : p ∉ s.byz) o,
          ((gS (sc₁ Reg s) Reg snd T p).g = true ∧ o = (gS (sc₁ Reg s) Reg snd T p).v) ∨
          ((gS (sc₁ Reg s) Reg snd T p).g = false ∧
            Decides ⊤ ba (sc₂ Reg snd s) ⟨p, hN p hp⟩ o) → o = (gS (sc₁ Reg s) Reg snd T j).v := by
        rintro p hp o (⟨-, rfl⟩ | ⟨-, ho⟩)
        · exact hall p hp
        · exact Decides.unique _ _ ho (hbaval ⟨p, hN p hp⟩ hp)
      rw [key p hp v hv, key q hq w hw]
    · push Not at hj
      rcases hv with ⟨hg, -⟩ | ⟨-, hv⟩
      · exact absurd hg (by simp [hj p hp])
      rcases hw with ⟨hg, -⟩ | ⟨-, hw⟩
      · exact absurd hg (by simp [hj q hq])
      exact hagr ⟨p, hN p hp⟩ hp ⟨q, hN q hq⟩ hq v w hv hw

omit [Finite P] hsR hrel hV in
/-- Termination of a party with grade `0` needs only the termination of `ba`. -/
lemma bc_terminates {p : P}
    (hterm : ∀ hpN : p ∈ Regᶜ, ∃ o, Decides ⊤ ba (sc₂ Reg snd s) ⟨p, hpN⟩ o) :
    ∃ o, Decides ⊤ (bc Reg snd ba) s p o := by
  by_cases h : p ∈ Reg ∨ (gS (sc₁ Reg s) Reg snd T p).g = true
  · exact ⟨_, (bc_decides_of_g s h _).2 rfl⟩
  · push Not at h
    obtain ⟨o, ho⟩ := hterm h.1
    exact ⟨o, (bc_decides_of_g0 s ⟨p, h.1⟩ (by simpa using h.2) o).2 ho⟩

end Main

/-! ### The "OR" exchange among the unregistered parties (Figure 4) -/

section OrBA

variable (N : Type)

open Classical in
/-- Every party sends its value; after one round it decides the OR of its own value and the values
received. With no Byzantine party this is Byzantine agreement. -/
noncomputable def orBA : Protocol N Bool Bool Bool where
  send _ x _ _ := some x
  decide _ x h := match h with
    | [] => none
    | ib :: _ => some (x || decide (∃ q, ib q = some true))

variable {N}

open Classical in
lemma orBA_decides (s : Scenario N Bool Bool) (p : N) (o : Bool) :
    Decides ⊤ (orBA N) s p o ↔ o = (s.input p || decide (∃ q,
      deliver ⊤ (orBA N) s (hist ⊤ (orBA N) s 0) 0 q p = some true)) := by
  have hst : ∀ r, status ⊤ (orBA N) s (r + 1) p = some (s.input p || decide (∃ q,
      deliver ⊤ (orBA N) s (hist ⊤ (orBA N) s 0) 0 q p = some true)) := by
    intro r
    have h1 := hist_take ⊤ (orBA N) s (show 1 ≤ r + 1 by omega) p
    obtain ⟨ib, l, hl⟩ : ∃ ib l, hist ⊤ (orBA N) s (r + 1) p = ib :: l := by
      cases h : hist ⊤ (orBA N) s (r + 1) p with
      | nil => have := length_hist ⊤ (orBA N) s (r + 1) p; rw [h] at this; simp at this
      | cons ib l => exact ⟨ib, l, rfl⟩
    rw [hl] at h1
    simp only [List.take_succ_cons, List.take_zero, hist_succ, hist_zero, List.nil_append,
      List.cons.injEq, and_true] at h1
    subst h1; rw [status, hl]; rfl
  constructor
  · rintro ⟨r, hr, -⟩
    cases r with
    | zero => simp [status, orBA] at hr
    | succ r => rw [hst] at hr; exact (Option.some_injective _ hr).symm
  · rintro rfl
    exact ⟨1, hst 0, fun r hr => by
      obtain rfl : r = 0 := by omega
      simp [status, orBA]⟩

lemma orBA_terminates (s : Scenario N Bool Bool) (p : N) : ∃ o, Decides ⊤ (orBA N) s p o :=
  ⟨_, (orBA_decides s p _).2 rfl⟩

/-- Without Byzantine parties, `orBA` solves Byzantine agreement. -/
lemma orBA_BA (s : Scenario N Bool Bool) (hrel : s.Reliable) (hB : s.byz = ∅) :
    BA s.input s.honest (Decides ⊤ (orBA N) s) := by
  classical
  have key : ∀ p o, Decides ⊤ (orBA N) s p o ↔ o = decide (∃ q, s.input q = true) := by
    intro p o
    rw [orBA_decides]
    have hdel : ∀ q, q ≠ p → deliver ⊤ (orBA N) s (hist ⊤ (orBA N) s 0) 0 q p = some (s.input q) := by
      intro q hqp
      rw [deliver_honest ⊤ _ s hrel (by simp [hB]) hqp]; rfl
    have hself : deliver ⊤ (orBA N) s (hist ⊤ (orBA N) s 0) 0 p p = none := by simp [deliver]
    suffices (s.input p || decide (∃ q, deliver ⊤ (orBA N) s (hist ⊤ (orBA N) s 0) 0 q p = some true))
        = decide (∃ q, s.input q = true) by rw [this]
    rcases Bool.eq_false_or_eq_true (s.input p) with h | h
    · simp only [h, Bool.true_or]; exact (decide_eq_true ⟨p, h⟩).symm
    · simp only [h, Bool.false_or, decide_eq_decide]
      constructor
      · rintro ⟨q, hq⟩
        by_cases hqp : q = p
        · subst hqp; rw [hself] at hq; simp at hq
        · rw [hdel q hqp] at hq; exact ⟨q, Option.some_injective _ hq⟩
      · rintro ⟨q, hq⟩
        have hqp : q ≠ p := by rintro rfl; simp_all
        exact ⟨q, by rw [hdel q hqp, hq]⟩
  refine ⟨fun p _ => ⟨_, (key p _).2 rfl⟩, fun v hv p hp => (key p v).2 ?_,
    fun p _ q _ v w hv hw => by rw [(key p v).1 hv, (key q w).1 hw]⟩
  have hall : ∀ q, s.input q = v := fun q => hv q (by simp [Scenario.honest, hB])
  rcases Bool.eq_false_or_eq_true v with h | h
  · subst h; exact (decide_eq_true ⟨p, hall p⟩).symm
  · subst h; simp [hall]

end OrBA

/-! ### Theorems 3.13 and 3.14 -/

section Theorems

variable [Finite P] {Reg : Set P} {snd : P}

omit [Finite P] in
lemma sc₂_reliable {M' : Type} {s : Scenario P Bool (GMsg P ⊕ M')} (hrel : s.Reliable) :
    (sc₂ Reg snd s).Reliable := fun _ _ _ => hrel _ _ _

lemma ncard_sc₂_byz {M' : Type} (s : Scenario P Bool (GMsg P ⊕ M')) (hReg : Reg ⊆ s.byz) :
    (sc₂ Reg snd s).byz.ncard + Reg.ncard = s.byz.ncard := by
  have h1 : Subtype.val '' (sc₂ Reg snd s).byz = s.byz \ Reg := by
    ext x; constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨hq, q.2⟩
    · rintro ⟨hx, hxR⟩; exact ⟨⟨x, hxR⟩, hx, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, h1]
  exact Set.ncard_sdiff_add_ncard_of_subset hReg

lemma nat_card_unreg : Nat.card (Unreg Reg) = Nat.card P - Reg.ncard := by
  rw [Nat.card_coe_set_eq, Set.ncard_compl]

omit [Finite P] in
/-- The bound of Theorem 3.13 in the paper's equivalent form `3t < n + 2s` (abstract). -/
lemma resilience_iff {n s t : ℕ} (hs : s ≤ n) : t < s + (n - s + 2) / 3 ↔ 3 * t < n + 2 * s := by
  omega

/-- **Theorem 3.13.** Π_BC is a Byzantine broadcast protocol for a registered sender tolerating
`t ≤ s + ⌈(n - s)/3⌉ - 1` Byzantine parties (written `t < s + ⌈(n-s)/3⌉`), given a black-box
unauthenticated Byzantine agreement protocol among the `n - s` unregistered parties tolerating every
Byzantine set `B` with `3|B| < n - s`. -/
theorem theorem313 (hsR : snd ∈ Reg) {M' : Type} (ba : Protocol (Unreg Reg) Bool M' Bool)
    (hba : Solves ⊤ ba {B | 3 * B.ncard < Nat.card (Unreg Reg)} BA) (t : ℕ)
    (ht : t < Reg.ncard + (Nat.card P - Reg.ncard + 2) / 3) :
    SolvesAuth ⊤ (bc Reg snd ba) (bcAuth Reg snd M') (atMost t) (BB snd) := by
  intro s hs hrel hV
  by_cases hk : ∃ k, k ∉ s.byz ∧ k ∈ Reg
  · obtain ⟨k, hk, hkR⟩ := hk
    exact bc_bb_of_honest_reg s hsR hrel hV hk hkR
  · push Not at hk
    have hReg : Reg ⊆ s.byz := fun k hkR => by by_contra h; exact hk k h hkR
    refine bc_bb_of_ba s hsR hrel hV hReg (hba _ ?_ (sc₂_reliable hrel))
    have h1 := ncard_sc₂_byz (snd := snd) s hReg
    have h2 : s.byz.ncard ≤ t := hs
    show 3 * (sc₂ Reg snd s).byz.ncard < Nat.card (Unreg Reg)
    rw [nat_card_unreg]
    omega

/-- Theorem 3.13 in solvability form: Byzantine broadcast with a registered sender is solvable in
the partially authenticated setting for `t < s + ⌈(n-s)/3⌉`, provided unauthenticated Byzantine
agreement among `n - s` parties against `3|B| < n - s` is solvable. -/
theorem theorem313_solvable (hsR : snd ∈ Reg)
    (hba : Solvable (⊤ : SimpleGraph (Unreg Reg)) {B | 3 * B.ncard < Nat.card (Unreg Reg)}
      (BA (V := Bool)))
    (t : ℕ) (ht : t < Reg.ncard + (Nat.card P - Reg.ncard + 2) / 3) :
    SolvablePA Reg (atMost t) (BB (V := Bool) snd) := by
  obtain ⟨M', ba, hba⟩ := hba
  exact ⟨_, _, bcAuth Reg snd M', bc Reg snd ba, bcAuth_registered Reg snd M', bc_unforging Reg snd ba,
    theorem313 hsR ba hba t ht⟩

/-- Non-vacuity of Theorem 3.13: for at most three unregistered parties the black box is
discharged by `orBA` (the only admissible Byzantine set among `N` is `∅`). -/
theorem theorem313_small (hsR : snd ∈ Reg) (hn : Nat.card P ≤ Reg.ncard + 3) (t : ℕ)
    (ht : t < Reg.ncard + (Nat.card P - Reg.ncard + 2) / 3) :
    SolvablePA Reg (atMost t) (BB (V := Bool) snd) := by
  refine theorem313_solvable hsR ⟨Bool, orBA _, fun s hs hrel => orBA_BA s hrel ?_⟩ t ht
  have hs' : 3 * s.byz.ncard < Nat.card (Unreg Reg) := hs
  rw [nat_card_unreg] at hs'
  exact (Set.ncard_eq_zero (Set.toFinite _)).mp (by omega)

/-- **Theorem 3.14** (Figure 4, Lemma 6.1). If `n - s ≤ 2`, Π_BC with the OR-exchange among the
unregistered parties solves Byzantine broadcast with a registered sender against **any** set of
Byzantine parties. -/
theorem theorem314 (hsR : snd ∈ Reg) (hn : Nat.card P ≤ Reg.ncard + 2) :
    SolvesAuth ⊤ (bc Reg snd (orBA (Unreg Reg))) (bcAuth Reg snd Bool) Set.univ (BB snd) := by
  intro s _ hrel hV
  by_cases hk : ∃ k, k ∉ s.byz ∧ k ∈ Reg
  · obtain ⟨k, hk, hkR⟩ := hk
    exact bc_bb_of_honest_reg s hsR hrel hV hk hkR
  push Not at hk
  have hReg : Reg ⊆ s.byz := fun k hkR => by by_contra h; exact hk k h hkR
  by_cases hN : (sc₂ Reg snd s).byz = ∅
  · exact bc_bb_of_ba s hsR hrel hV hReg (orBA_BA _ (sc₂_reliable hrel) hN)
  -- some unregistered party is Byzantine: at most one honest party
  obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.mpr hN
  have hone : ∀ p q, p ∉ s.byz → q ∉ s.byz → p = q := by
    intro p q hp hq
    by_contra hpq
    have hpu : p ≠ u.1 := by rintro rfl; exact hp hu
    have hqu : q ≠ u.1 := by rintro rfl; exact hq hu
    have h3 : ({p, q, u.1} : Set P).ncard = 3 := Set.ncard_eq_three.mpr ⟨p, q, u.1, hpq, hpu, hqu, rfl⟩
    have hsub : ({p, q, u.1} : Set P) ⊆ Regᶜ := by
      rintro x (rfl | rfl | rfl)
      · exact fun h => hp (hReg h)
      · exact fun h => hq (hReg h)
      · exact u.2
    have := Set.ncard_le_ncard hsub
    rw [Set.ncard_compl] at this
    omega
  refine ⟨fun p hp => bc_terminates s (fun _ => orBA_terminates _ _),
    fun hsnd => absurd (hReg hsR) hsnd, fun p hp q hq v w hv hw => ?_⟩
  obtain rfl := hone p q hp hq
  exact Decides.unique _ _ hv hw

theorem theorem314_solvable (hsR : snd ∈ Reg) (hn : Nat.card P ≤ Reg.ncard + 2) :
    SolvablePA Reg Set.univ (BB (V := Bool) snd) :=
  ⟨_, _, bcAuth Reg snd Bool, bc Reg snd (orBA _), bcAuth_registered Reg snd Bool,
    bc_unforging Reg snd _, theorem314 hsR hn⟩

end Theorems

/-- **Theorem 4.1 needs the hypothesis "unregistered sender".** With `n = s = 3` (everybody
registered, sender `0`) and `t = 2 ≥ max{⌈s/2⌉, ⌈n/3⌉} = 2`, Byzantine broadcast *is* solvable
(Theorem 3.14), although Theorem 4.1 as printed (without the sender hypothesis) claims it is not. -/
theorem theorem41_false_registered_sender :
    max (((Set.univ : Set (Fin 3)).ncard + 1) / 2) ((Nat.card (Fin 3) + 2) / 3) ≤ 2 ∧
    SolvablePA (Set.univ : Set (Fin 3)) (atMost 2) (BB (V := Bool) (0 : Fin 3)) := by
  refine ⟨by simp, (theorem314_solvable (Set.mem_univ _) (by simp)).mono (Set.subset_univ _)⟩

end PartialAuthBC
