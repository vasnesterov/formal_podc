import Podc.Computability.Distributed.NIS.Transfer

-- CSLib candidate: Cslib/Computability/Distributed/NIS/OutputQueries.lean (staged by Papers/PODC2021/ExtensionBasedReductions)
/-!
# Extension-based proofs are augmented extension-based proofs

Brusse–Ellen, PODC 2021, Section 4: "Any task that has an extension-based impossibility proof also
has an augmented extension-based impossibility proof": an output query `(C, P, y)` is simulated by the
assignment queries `(C, P, gₚ)`, `p ∈ P`, where `gₚ : {p} → {y}`.

Every other move is forwarded unchanged. Since our handler programs must issue at least one move, an
output query is preceded by a harmless assignment query `(C, ∅, ∅)` (needed when `P = ∅`).
-/

namespace Cslib.NIS

variable {P X Y : Type} [DecidableEq P]

instance {O : Type} : Inhabited (Resp P X Y O) := ⟨.ack⟩

/-- The response of the last move of a history. -/
def lastResp {M R : Type} [Inhabited R] (h : List (M × R)) : R := (h.getLast?.map Prod.snd).getD default

lemma lastResp_concat {M R : Type} [Inhabited R] (h : List (M × R)) (e : M × R) :
    lastResp (h ++ [e]) = e.2 := by simp [lastResp]

/-- The assignment `{p} → {y}`. -/
def single (p : P) (y : Y) : P → Option Y := fun q => if q = p then some y else none

abbrev OMove (P X Y : Type) := Move P X (Finset P × Y)
abbrev AMove (P X Y : Type) := Move P X (Finset P × (P → Option Y))
abbrev ResO (P X Y : Type) := Resp P X Y (Option (List P))

/-- Ask the assignment queries `(C, Ps, single p y)` for `p` in a list, until one succeeds. -/
def outLoop (C : Config P X) (y : Y) (Ps : Finset P) :
    List P → Prog (AMove P X Y) (ResO P X Y) (ResO P X Y)
  | [] => .done (.answer none)
  | p :: ps => .ask (.oracle C (Ps, single p y)) fun h =>
      match lastResp h with
      | .answer (some μ) => .done (.answer (some μ))
      | _ => outLoop C y Ps ps

/-- The handler of the simulation. -/
noncomputable def outH (_ : List (OMove P X Y × ResO P X Y)) (_ : List (AMove P X Y × ResO P X Y)) :
    OMove P X Y → AMove P X Y × (List (AMove P X Y × ResO P X Y) → Prog (AMove P X Y) (ResO P X Y) (ResO P X Y))
  | .query C q => (.query C q, fun h => .done (lastResp h))
  | .endPhase C => (.endPhase C, fun _ => .done .ack)
  | .oracle C o => (.oracle C (∅, fun _ => none), fun _ => outLoop C o.2 o.1 o.1.toList)

lemma progRun_single {M R A : Type} [Inhabited R] {h : List (M × R)} {m : M} {w : List (M × R)} {r : R}
    (hr : ProgRun h (.ask m (fun h => (.done (lastResp h) : Prog M R R))) w r) : w = [(m, r)] := by
  cases hr with
  | ask _ _ _ r' w' _ hr' =>
    simp only [lastResp_concat] at hr'
    cases hr'; rfl

lemma progRun_const {M R A : Type} {h : List (M × R)} {m : M} {w : List (M × R)} {a b : A}
    (hr : ProgRun h (.ask m (fun _ => (.done b : Prog M R A))) w a) : ∃ r, w = [(m, r)] ∧ a = b := by
  cases hr with
  | ask _ _ _ r' w' _ hr' => cases hr'; exact ⟨r', rfl, rfl⟩

section Loop
variable [Inhabited X] {δ : Protocol P X Y}

lemma statesOf_oracles {Q : Type} (gs : GState P X) (w : List (Move P X Q × ResO P X Y))
    (hw : ∀ e ∈ w, ∃ C o, e.1 = .oracle C o) : w.foldl (fun g e => g.next e.1) gs = gs := by
  induction w generalizing gs with
  | nil => rfl
  | cons e w ih =>
    obtain ⟨C, o, he⟩ := hw e (by simp)
    simp only [List.foldl_cons, he, GState.next]
    exact ih gs (fun e' he' => hw e' (by simp [he']))

lemma outLoop_spec (gs : GState P X) (C : Config P X) (hC : gs.Reached C) (y : Y) (Ps : Finset P) :
    ∀ (l : List P), (∀ p ∈ l, p ∈ Ps) → ∀ h w r, ProgRun h (outLoop C y Ps l) w r →
      (∀ e ∈ w, ValidResp (assignSpec (P := P)) δ e.1 e.2) →
      LegalRun (assignSpec (P := P)) δ gs w ∧ (∀ e ∈ w, ∃ C o, e.1 = .oracle C o) ∧
      ∃ a, r = .answer a ∧
        (∀ μ, a = some μ → ∃ p ∈ l, GoodSched δ C Ps (fun D => Satisfies δ D (single p y)) μ) ∧
        (a = none → ∀ p ∈ l, ¬ ∃ μ, GoodSched δ C Ps (fun D => Satisfies δ D (single p y)) μ) := by
  intro l
  induction l with
  | nil =>
    intro _ h w r hr _
    cases hr
    exact ⟨trivial, by simp, none, rfl, by simp, by simp⟩
  | cons p l ih =>
    intro hl h w r hr hv
    cases hr with
    | ask _ _ _ r' w' _ hr' =>
      have hv0 := hv _ (List.mem_cons.2 (Or.inl rfl))
      obtain ⟨a', hr'eq, ha'⟩ := hv0
      simp only at hr'eq
      subst hr'eq
      have hleg : Legal (assignSpec (P := P)) δ gs (.oracle C (Ps, single p y)) :=
        ⟨hC, fun q hq => by simp [single] at hq; rw [hq]; exact hl p (by simp)⟩
      simp only [lastResp_concat] at hr'
      cases a' with
      | some μ =>
        simp only at hr'
        cases hr'
        refine ⟨⟨hleg, trivial⟩, by simp, some μ, rfl, fun μ' hμ' => ?_, by simp⟩
        cases hμ'; exact ⟨p, by simp, ha'⟩
      | none =>
        simp only at hr'
        obtain ⟨h1, h2, a, rfl, h3, h4⟩ := ih (fun q hq => hl q (by simp [hq])) _ _ _ hr'
          (fun e he => hv e (by simp [he]))
        refine ⟨⟨hleg, by simpa [GState.next] using h1⟩, ?_, a, rfl, ?_, ?_⟩
        · intro e he; simp at he; rcases he with rfl | he
          · exact ⟨_, _, rfl⟩
          · exact h2 e he
        · intro μ hμ; obtain ⟨q, hq, h⟩ := h3 μ hμ; exact ⟨q, by simp [hq], h⟩
        · intro ha q hq; simp at hq; rcases hq with rfl | hq
          · exact ha'
          · exact h4 ha q hq

end Loop

/-- Section 4: every task with an extension-based impossibility proof has an augmented
extension-based impossibility proof. -/
theorem hasAugEBProof_of_hasEBProof [Inhabited X] [Fintype P] {T : Task P X Y}
    (h : HasEBProof T) : HasAugEBProof T := by
  obtain ⟨σs, hσ⟩ := h
  refine ⟨simulate σs outH, fun δ pl hc hv => ?_⟩
  let D : SimData (outputSpec (P := P)) (assignSpec (P := P)) δ δ :=
    { σ := σs, H := outH, I := fun hs ht => statesOf hs = statesOf ht, init := rfl,
      step := by
        intro hs ht m w r hI hleg hr hvw
        cases m with
        | query C q =>
          simp only [outH] at hr hvw ⊢
          have hw := progRun_single (A := ResO P X Y) hr
          subst hw
          have := hvw _ (List.mem_singleton_self _)
          refine ⟨this, ⟨by rw [← hI]; exact hleg, trivial⟩, ?_⟩
          rw [statesOf_append, statesOf_append, hI]; rfl
        | endPhase C =>
          simp only [outH] at hr hvw ⊢
          obtain ⟨r', hw, rfl⟩ := progRun_const hr
          subst hw
          refine ⟨rfl, ⟨by rw [← hI]; exact hleg, trivial⟩, ?_⟩
          rw [statesOf_append, statesOf_append, hI]; rfl
        | oracle C o =>
          simp only [outH] at hr hvw ⊢
          cases hr with
          | ask _ _ _ r0 w' _ hr' =>
            obtain ⟨hC, -⟩ := hleg
            rw [hI] at hC
            obtain ⟨h1, h2, a, rfl, h3, h4⟩ := outLoop_spec (δ := δ) (statesOf ht) C hC o.2 o.1
              o.1.toList (fun p hp => by simpa using hp) _ _ _ hr' (fun e he => hvw e (by simp [he]))
            refine ⟨⟨a, rfl, ?_⟩, ⟨⟨hC, by intro q hq; simp at hq⟩, by simpa [GState.next] using h1⟩, ?_⟩
            · cases a with
              | some μ =>
                obtain ⟨p, hp, hμ1, hμ2, hμ3⟩ := h3 μ rfl
                refine ⟨hμ1, hμ2, p, by simpa using hp, hμ3 p o.2 (by simp [single])⟩
              | none =>
                rintro ⟨μ, hμ1, hμ2, p, hp, hpy⟩
                refine h4 rfl p (by simpa using hp) ⟨μ, hμ1, hμ2, fun q z hq => ?_⟩
                simp [single] at hq; obtain ⟨rfl, rfl⟩ := hq; exact hpy
            · rw [statesOf_append, statesOf_append, hI]
              simp only [List.foldl_cons, List.foldl_nil, GState.next]
              exact (statesOf_oracles _ _ h2).symm }
  obtain ⟨ps, a, ha0, hamono, hwin, hleg, hI, hrun⟩ := D.transfer outputSpec_total T (hσ δ) pl hc hv
  have hst : ∀ j, states ps j = states pl (a j) := fun j => by
    rw [states_eq_statesOf, states_eq_statesOf]; exact hI j
  -- windows of queries and phase ends are single moves
  have hq : ∀ j C q, (ps j).1 = .query C q →
      a (j + 1) = a j + 1 ∧ (pl (a j)).1 = .query C q := by
    intro j C q hj
    have := hrun j
    rw [hj] at this
    have hw := progRun_single (A := ResO P X Y) this
    have hlen := congrArg List.length hw
    simp [window] at hlen
    refine ⟨by have := hamono j; omega, ?_⟩
    have h0 : (window pl (a j) (a (j + 1)))[0]'(by rw [hw]; simp) = pl (a j) := by
      simp [window]
    have : (window pl (a j) (a (j + 1)))[0]'(by rw [hw]; simp) = (Move.query C q, (ps j).2) := by
      simp only [hw]; rfl
    rw [← h0, this]
  have he : ∀ j C, (ps j).1 = .endPhase C → (pl (a j)).1 = .endPhase C := by
    intro j C hj
    have := hrun j
    rw [hj] at this
    obtain ⟨r', hw, -⟩ := progRun_const this
    have h0 : (window pl (a j) (a (j + 1)))[0]'(by rw [hw]; simp) = pl (a j) := by
      simp [window]
    have : (window pl (a j) (a (j + 1)))[0]'(by rw [hw]; simp) = (Move.endPhase C, r') := by
      simp only [hw]; rfl
    rw [← h0, this]
  have hamono' : StrictMono a := strictMono_nat_of_lt_succ hamono
  refine ⟨hleg, ?_⟩
  rcases hwin.2 with ⟨k, C, hC, hvi⟩ | hinf | ⟨K, hK⟩
  · exact Or.inl ⟨a k, C, by rwa [← hst], hvi⟩
  · refine Or.inr (Or.inl fun N => ?_)
    obtain ⟨k, hk, C, hkC⟩ := hinf N
    exact ⟨a k, le_trans hk (hamono'.le_apply), C, he k C hkC⟩
  · refine Or.inr (Or.inr ⟨a K, fun t ht => ?_⟩)
    -- from `K` on every window is a single query
    have hK' : ∀ k ≥ K, ∃ C q, (ps k).1 = .query C q := fun k hk => by
      obtain ⟨C, q, _, h1, _⟩ := hK k hk; exact ⟨C, q, h1⟩
    have hlin : ∀ i, a (K + i) = a K + i := fun i => by
      induction i with
      | zero => rfl
      | succ i ih =>
        obtain ⟨C, q, h⟩ := hK' (K + i) (by omega)
        rw [← add_assoc, (hq _ C q h).1, ih]; ring
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le ht
    obtain ⟨C, q, q', h1, h2⟩ := hK (K + i) (by omega)
    refine ⟨C, q, q', ?_, ?_⟩
    · rw [← hlin, (hq _ C q h1).2]
    · rw [show a K + i + 1 = a (K + (i + 1)) by rw [hlin]; ring, ← add_assoc,
        (hq _ _ q' h2).2]

end Cslib.NIS
