import Papers.PODC2020.UnknownParticipantsBA.Layer

/-!
# Repaired Theorem 1: the rotor-coordinator with a correct termination rule

Algorithm 1 of the BA with line 19 (`if p ∈ S_v then break`) replaced by
"`if 2r > n_v then break`" (`fixedRule`). With `n > 3f`:

* some iteration `r ≤ f` is a good round: every correct node selects the same correct
  coordinator `p` (in fact the smallest correct id), and in iteration `r + 1` every correct node
  accepts exactly `p`'s opinion;
* no correct node terminates before iteration `f + 1`, and every correct node terminates by
  iteration `⌊n/2⌋ + 1` — `O(n)` rounds, as claimed in the paper.

The node cannot detect the good round itself, but since `n_v ≥ g > 2f`, waiting until
`2r > n_v` is enough.
-/

namespace UnknownBA

variable {I X : Type*} [DecidableEq I] [LinearOrder I] [DecidableEq X]

omit [LinearOrder I] in
lemma mem_opinionsFrom {P : Finset I} {B : Finset (I × Msg I X)} {x : X} :
    x ∈ opinionsFrom P B ↔ ∃ q ∈ P, (q, Msg.app x) ∈ B := by
  simp only [opinionsFrom, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨q, m⟩, hm, h⟩
    by_cases hq : q ∈ P
    · simp only [hq, ite_true, Option.mem_toFinset] at h
      cases m <;> simp [Msg.appVal] at h
      subst h; exact ⟨q, hq, hm⟩
    · simp [hq] at h
  · rintro ⟨q, hq, hm⟩
    exact ⟨_, hm, by simp [hq, Msg.appVal]⟩

lemma rotorExt_step_id (rule : Rule I) (t : ℕ) (c : Core I) (st : RState I X)
    (B : Finset (I × Msg I X)) :
    ((rotorExt rule).step t c st B).id = st.id ∧ ((rotorExt rule).step t c st B).op = st.op := by
  rcases t with _ | r
  · exact ⟨rfl, rfl⟩
  · simp only [rotorExt]; split_ifs <;> exact ⟨rfl, rfl⟩

lemma rotorExt_step_succ' (rule : Rule I) (r : ℕ) (c : Core I) (st : RState I X)
    (B : Finset (I × Msg I X)) (hst : st.halted = false) :
    ((rotorExt rule).step (r + 1) c st B).sel = selSet c.C r ∧
      ((rotorExt rule).step (r + 1) c st B).acc = opinionsFrom st.sel B ∧
      ((rotorExt rule).step (r + 1) c st B).halted = rule r c st.S (selSet c.C r) ∧
      (((rotorExt rule).step (r + 1) c st B).halted = false →
        ((rotorExt rule).step (r + 1) c st B).out =
          if st.id ∈ selSet c.C r then {st.op} else ∅) ∧
      (((rotorExt rule).step (r + 1) c st B).halted = false →
        ((rotorExt rule).step (r + 1) c st B).S = st.S ∪ selSet c.C r) := by
  simp only [rotorExt]
  by_cases hr : rule r c st.S (selSet c.C r) = true
  · simp [hr]
  · simp only [Bool.not_eq_true] at hr
    simp [hr, hst]

variable (rule : Rule I) (E : Env I X (Msg I X))

lemma hinit_rotor : ∀ (v : I) (x : X), (rotorExt rule).halted ((rotorExt rule).init v x) = false :=
  fun _ _ => rfl

local notation "R" => run (rotor rule) E

lemma rotor_id (s : ℕ) (v : I) : (R s v).ext.id = v ∧ (R s v).ext.op = E.input v := by
  induction s with
  | zero => exact ⟨rfl, rfl⟩
  | succ s ih =>
    by_cases h : (rotorExt rule).halted (R s v).ext = true
    · have := run_add_of_halted (rotorExt rule) E h 1
      rw [rotor] at *; rw [this]; exact ih
    · simp only [Bool.not_eq_true] at h
      have := ext_succ (Ex := rotorExt rule) (E := E) (s := s) (v := v) h
      rw [rotor] at *; rw [this, (rotorExt_step_id _ _ _ _ _).1, (rotorExt_step_id _ _ _ _ _).2]
      exact ih

/-- One loop iteration `r` (step `r + 2`) of a node running at its start. -/
lemma rotor_iter {r : ℕ} {v : I} (h : Alive (rotorExt rule) E (r + 1) v) :
    let c := (R (r + 2) v).core
    let st := (R (r + 1) v).ext
    let p := selSet c.C r
    (R (r + 2) v).ext.sel = p ∧
      (R (r + 2) v).ext.acc = opinionsFrom st.sel (inbox (rotor rule) E (R (r + 1)) (r + 1) v) ∧
      (R (r + 2) v).ext.halted = rule r c st.S p ∧
      ((R (r + 2) v).ext.halted = false → (R (r + 2) v).ext.out =
        if v ∈ p then {E.input v} else ∅) ∧
      ((R (r + 2) v).ext.halted = false → (R (r + 2) v).ext.S = st.S ∪ p) := by
  intro c st p
  have he := ext_succ (Ex := rotorExt rule) (E := E) h
  have hid := rotor_id rule E (r + 1) v
  have hst : st.halted = false := h
  have key := rotorExt_step_succ' (X := X) rule r (run (rotor rule) E (r + 1 + 1) v).core st
    (inbox (rotor rule) E (run (rotor rule) E (r + 1)) (r + 1) v) hst
  have he' : (R (r + 2) v).ext = _ := he
  rw [show st.id = v from hid.1, show st.op = E.input v from hid.2] at key
  rw [he']
  exact key

lemma rotor_one (v : I) : (R 1 v).ext = (R 0 v).ext :=
  ext_succ (Ex := rotorExt rule) (E := E) (s := 0) (v := v) rfl

lemma rotor_alive_one (v : I) : Alive (rotorExt rule) E 1 v := by
  unfold Alive
  change (run (rotor rule) E 1 v).ext.halted = false
  rw [rotor_one]; rfl

variable (hres : 2 * E.F.card < E.G.card)
include hres

/-- With the repaired rule no correct node stops before iteration `f + 1`. -/
lemma fixed_alive (v : I) (_hv : v ∈ E.G) : ∀ s ≤ E.F.card + 2, Alive (rotorExt fixedRule) E s v := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    have ha := ih (by omega)
    rcases s with _ | r
    · have := ext_succ (Ex := rotorExt (X := X) fixedRule) (E := E) ha
      unfold Alive; rw [this]; exact ha
    · have hit := (rotor_iter fixedRule E ha).2.2.1
      have hG := G_sub_heard_succ (hinit_rotor (I := I) (X := X) fixedRule) ha
      have := Finset.card_le_card hG
      unfold Alive
      change (run (rotor fixedRule) E (r + 2) v).ext.halted = false
      rw [hit]
      simp only [fixedRule, decide_eq_false_iff_not, not_lt]
      change 2 * r ≤ (run (withRotor (rotorExt fixedRule)) E (r + 1 + 1) v).core.heard.card
      omega

/-- **Repaired Theorem 1 (BA) / Theorem 2 (full version).** With `n > 3f` and the termination
rule `2r > n_v`: (1) there is an iteration `r ≤ f` in which every correct node selects the same
correct coordinator `p`, and in iteration `r + 1` every correct node accepts exactly `p`'s
opinion; (2) every correct node terminates in some iteration `r` with `f + 1 ≤ r ≤ ⌊n/2⌋ + 1`. -/
theorem rotor_fixed :
    (∃ r ≤ E.F.card, ∃ p ∈ E.G, ∀ v ∈ E.G,
      Selects fixedRule E v r p ∧ Accepts fixedRule E v (r + 1) (E.input p) ∧
        (run (rotor fixedRule) E (r + 3) v).ext.acc = {E.input p}) ∧
    (∀ v ∈ E.G, ∃ r, E.F.card + 1 ≤ r ∧ r ≤ (E.G.card + E.F.card) / 2 + 1 ∧
      HaltsAt fixedRule E v r) := by
  have hinit := hinit_rotor (I := I) (X := X) fixedRule
  have alive := fixed_alive E hres
  constructor
  · obtain ⟨r, hr, p, hp, hsel⟩ := layer_good hinit hres (fun r => r + 2) le_rfl
      (fun r => by omega) (fun q hq => alive q hq _ le_rfl)
    refine ⟨r, hr, p, hp, fun v hv => ?_⟩
    have hv1 := alive v hv (r + 1) (by omega)
    have hv2 := alive v hv (r + 2) (by omega)
    have hp2 := alive p hp (r + 2) (by omega)
    have hselv : (run (rotor fixedRule) E (r + 2) v).ext.sel = {p} := by
      rw [(rotor_iter fixedRule E hv1).1]; exact hsel v hv
    have hacc : (run (rotor fixedRule) E (r + 3) v).ext.acc = {E.input p} := by
      rw [(rotor_iter fixedRule E (r := r + 1) hv2).2.1, hselv]
      ext x
      rw [mem_opinionsFrom, Finset.mem_singleton]
      simp only [Finset.mem_singleton, exists_eq_left]
      rw [mem_inbox_correct _ _ _ _ _ hp]
      have hout : (run (rotor fixedRule) E (r + 2) p).ext.out = {E.input p} := by
        have hp1 := alive p hp (r + 1) (by omega)
        rw [(rotor_iter fixedRule E hp1).2.2.2.1 hp2]
        have h' : selSet (run (rotor fixedRule) E (r + 2) p).core.C r = {p} := hsel p hp
        rw [h']; simp
      have := mem_out_app (Ex := rotorExt fixedRule) (E := E) (s := r + 2) (q := p) (a := x)
      simp only [rotor] at hout ⊢
      rw [this]
      change Alive _ E (r + 2) p ∧ x ∈ (run (withRotor (rotorExt fixedRule)) E (r + 2) p).ext.out ↔ _
      rw [hout]; simp [hp2]
    refine ⟨⟨hv1, hselv⟩, ⟨hv2, ?_⟩, hacc⟩
    rw [show r + 1 + 2 = r + 3 by omega, hacc]; exact Finset.mem_singleton_self _
  · intro v hv
    classical
    set N := (E.G.card + E.F.card) / 2 + 1
    have hex : ∃ s, ¬ Alive (rotorExt fixedRule) E s v := by
      refine ⟨N + 2, fun hN => ?_⟩
      have hN1 := alive_of_succ hN
      have hit := (rotor_iter fixedRule E hN1).2.2.1
      have hH := Finset.card_le_card (heard_sub_succ hN1)
      have hGF := Finset.card_union_le E.G E.F
      unfold Alive at hN
      change (run (rotor fixedRule) E (N + 2) v).ext.halted = false at hN
      rw [hit] at hN
      simp only [fixedRule, decide_eq_false_iff_not, not_lt] at hN
      change 2 * N ≤ (run (withRotor (rotorExt fixedRule)) E (N + 1 + 1) v).core.heard.card at hN
      omega
    have hspec := Nat.find_spec hex
    have hmin : ∀ s < Nat.find hex, Alive (rotorExt fixedRule) E s v := fun s hs => by
      have := Nat.find_min hex hs; simpa using this
    have hle : Nat.find hex ≤ N + 2 := Nat.find_min' hex (by
      intro hN
      have hN1 := alive_of_succ hN
      have hit := (rotor_iter fixedRule E hN1).2.2.1
      have hH := Finset.card_le_card (heard_sub_succ hN1)
      have hGF := Finset.card_union_le E.G E.F
      unfold Alive at hN
      change (run (rotor fixedRule) E (N + 2) v).ext.halted = false at hN
      rw [hit] at hN
      simp only [fixedRule, decide_eq_false_iff_not, not_lt] at hN
      change 2 * N ≤ (run (withRotor (rotorExt fixedRule)) E (N + 1 + 1) v).core.heard.card at hN
      omega)
    have hge : E.F.card + 3 ≤ Nat.find hex := by
      by_contra hlt
      exact hspec (alive v hv _ (by omega))
    obtain ⟨r, hr⟩ : ∃ r, Nat.find hex = r + 2 := ⟨Nat.find hex - 2, by omega⟩
    refine ⟨r, by omega, by omega, hmin (r + 1) (by omega), ?_⟩
    have := hspec
    rw [hr] at this
    unfold Alive at this
    simp only [Bool.not_eq_false] at this
    exact this

/-- **The termination half of Theorem 1 does hold for the paper's rule**: every correct node
executes `break` in some iteration `r ≤ n` (each iteration selects a new element of
`C_v ⊆ G ∪ F`). What fails is the good-round half (`Cex.theorem1_false`). -/
theorem paper_terminates (v : I) (hv : v ∈ E.G) :
    ∃ r ≤ E.G.card + E.F.card, HaltsAt paperRule E v r := by
  classical
  have hinit := hinit_rotor (I := I) (X := X) paperRule
  have hall1 : ∀ q ∈ E.G, Alive (rotorExt paperRule) E 1 q := fun q _ => rotor_alive_one _ E q
  have hGne : E.G.Nonempty := Finset.card_pos.mp (by omega)
  -- invariant: after surviving iteration `r - 1`, `|S_v| = r` and `S_v ⊆ C_v`
  have inv : ∀ r, Alive (rotorExt paperRule) E (r + 1) v →
      (run (rotor paperRule) E (r + 1) v).ext.S.card = r ∧
        (run (rotor paperRule) E (r + 1) v).ext.S ⊆ (run (rotor paperRule) E (r + 1) v).core.C := by
    intro r
    induction r with
    | zero =>
      intro _
      rw [rotor_one]
      exact ⟨rfl, Finset.empty_subset _⟩
    | succ r ih =>
      intro ha
      have ha1 := alive_of_succ ha
      obtain ⟨ih1, ih2⟩ := ih ha1
      have hit := rotor_iter paperRule E ha1
      have hnh : (run (rotor paperRule) E (r + 2) v).ext.halted = false := ha
      have hS := hit.2.2.2.2 hnh
      have hhalt := hit.2.2.1
      rw [hnh] at hhalt
      have hCne : (run (rotor paperRule) E (r + 2) v).core.C.Nonempty :=
        hGne.mono (G_sub_C hinit hres hall1 ha le_add_self)
      obtain ⟨x, hxC, hx⟩ := selSet_singleton hCne r
      simp only [paperRule] at hhalt
      rw [hx] at hhalt hS
      have hxS : x ∉ (run (rotor paperRule) E (r + 1) v).ext.S := by
        intro hxS
        have : ({x} ∩ (run (rotor paperRule) E (r + 1) v).ext.S).Nonempty := ⟨x, by simp [hxS]⟩
        simp [this] at hhalt
      have hCm := C_mono_succ (Ex := rotorExt paperRule) (E := E) ha
      change (run (rotor paperRule) E (r + 1 + 1) v).ext.S.card = r + 1 ∧
        (run (rotor paperRule) E (r + 1 + 1) v).ext.S ⊆
          (run (rotor paperRule) E (r + 1 + 1) v).core.C
      change (run (rotor paperRule) E (r + 1 + 1) v).ext.S = _ at hS
      rw [hS, Finset.union_comm, Finset.card_union_of_disjoint (by simpa using hxS), ih1]
      refine ⟨by simp; omega, Finset.union_subset (by simpa using hxC) (ih2.trans hCm)⟩
  -- hence the node cannot survive iteration `n`
  have hbound : ∀ r, Alive (rotorExt paperRule) E (r + 1) v → r ≤ E.G.card + E.F.card := by
    intro r ha
    obtain ⟨h1, h2⟩ := inv r ha
    have := Finset.card_le_card (h2.trans (C_real hinit hres hv ha))
    have := Finset.card_union_le E.G E.F
    omega
  have hex : ∃ s, ¬ Alive (rotorExt paperRule) E s v :=
    ⟨E.G.card + E.F.card + 2, fun h => by have := hbound _ h; omega⟩
  have hspec := Nat.find_spec hex
  have hmin : ∀ s < Nat.find hex, Alive (rotorExt paperRule) E s v := fun s hs => by
    have := Nat.find_min hex hs; simpa using this
  have hle : Nat.find hex ≤ E.G.card + E.F.card + 2 :=
    Nat.find_min' hex (fun h => by have := hbound _ h; omega)
  have hge : 2 ≤ Nat.find hex := by
    by_contra hlt
    interval_cases h : Nat.find hex
    · exact hspec rfl
    · exact hspec (rotor_alive_one _ E v)
  obtain ⟨r, hr⟩ : ∃ r, Nat.find hex = r + 2 := ⟨Nat.find hex - 2, by omega⟩
  refine ⟨r, by omega, hmin (r + 1) (by omega), ?_⟩
  have := hspec
  rw [hr] at this
  unfold Alive at this
  simp only [Bool.not_eq_false] at this
  exact this

end UnknownBA
