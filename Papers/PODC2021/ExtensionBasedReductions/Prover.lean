import Papers.PODC2021.ExtensionBasedReductions.Projection
import Podc.Computability.Distributed.NIS.OutputQueries

/-!
# The prover of Theorem 1

Brusse–Ellen, PODC 2021, Section 7. Given an augmented extension-based prover `𝒫_T` for `T`, the
prover `𝒫` for `S` simulates `𝒫_T` against the composed protocol `h ∘ A ∘ A₁`, where `A` is the
protocol it plays against. It answers the moves of `𝒫_T` as follows (`toA C` is the `A`-part of `C`):

* a query `(C, q)` where `q` takes a step of `A`: the query `(toA C, q)`;
* a query `(C, q)` where `q` takes a step of `A₁`: a chain of queries re-reaching `toA (C q)` (whose
  inputs may differ from those of `toA C`) from the start of the phase;
* an assignment query `(C, P, f)`: for every `P`-only schedule `μ₁` of `A₁` from the `A₁`-part of `C`
  after which all of `P` has finished `A₁`, and every assignment `g` of outputs of `A` with
  `h ∘ g = f`, it re-reaches `toA (C μ₁)` and asks `(toA (C μ₁), P, g)`; the first positive answer
  `μ'` gives the answer `μ₁ μ'`;
* ending a phase at `C`: ends its own phase at `toA C` if it reached `toA C` by a query in its current
  phase, and does nothing otherwise.

Every handler run starts with a harmless move (the assignment query `(base, ∅, ∅)`) except the
single query of the first case, so that chains of `𝒫_T` made of steps of `A` become chains of `𝒫`.
-/

namespace Podc.ExtensionBasedReductions

open Cslib.NIS

open St

variable {P XT M ZS ZT : Type} [DecidableEq P] [Inhabited XT] [Inhabited M]

abbrev YQ (P ZT : Type) := Finset P × (P → Option ZT)
abbrev YMv (P XT ZT : Type) := Move P XT (YQ P ZT)
abbrev YRp (P XT ZT : Type) := Resp P XT ZT (Option (List P))
abbrev AMv (P M ZS : Type) := Move P M (YQ P ZS)
abbrev ARp (P M ZS : Type) := Resp P M ZS (Option (List P))

/-- A chain of queries along a schedule; returns the history at its end. -/
def chain : Config P M → List P → List (AMv P M ZS × ARp P M ZS) →
    Prog (AMv P M ZS) (ARp P M ZS) (List (AMv P M ZS × ARp P M ZS))
  | _, [], h => .done h
  | C, q :: β, _ => .ask (.query C q) (fun h' => chain (step C q) β h')

/-- The history `ht` reveals that the decision function has value `z` on the state `s`. -/
def Reveals (ht : List (AMv P M ZS × ARp P M ZS)) (s : St P M) (z : Option ZS) : Prop :=
  ∃ e ∈ ht, ∃ D o j, e.2 = .config D o ∧ D j = s ∧ o j = z

open Classical in
/-- What the prover knows about the decision function on a state. -/
noncomputable def know (ht : List (AMv P M ZS × ARp P M ZS)) (s : St P M) : Option ZS :=
  if h : ∃ z, Reveals ht s z then h.choose else none

open Classical in
/-- A schedule re-reaching `D` from the start of the phase (based at `B`). -/
noncomputable def rsched (B D : Config P M) : List P :=
  if hex : ∃ β, exec (reinit B (inputs D)) β = D then hex.choose else []

/-- Re-reach `D` by a chain from the start of the phase. -/
noncomputable def reachP (B D : Config P M) (h : List (AMv P M ZS × ARp P M ZS)) :=
  chain (reinit B (inputs D)) (rsched B D) h

/-- The harmless move. -/
def dummy (B : Config P M) : AMv P M ZS := .oracle B (∅, fun _ => none)

section Defs
variable (δ1 : Protocol P XT M) (t : ℕ) (post : P → ZS → ZT)

/-- The response to `𝒫_T` for the configuration `C'`: outputs computed from what is known about `A`. -/
noncomputable def yResp (C' : Config P XT) (ht : List (AMv P M ZS × ARp P M ZS)) : YRp P XT ZT :=
  .config C' (fun j => (know ht (toA δ1 t C' j)).map (post j))

/-- Candidates for an assignment query `(C, Ps, f)`. -/
def candSet (C : Config P XT) (Ps : Finset P) (f : P → Option ZT) :
    Set (List P × (P → Option ZS)) :=
  {c | (∀ p ∈ c.1, p ∈ Ps) ∧ IsSched δ1 (trunc t C) c.1 ∧
    (∀ p ∈ Ps, (decided δ1 (exec (trunc t C) c.1 p)).isSome) ∧
    ∀ q, (f q = none ↔ c.2 q = none) ∧ ∀ z, c.2 q = some z → f q = some (post q z)}

open Classical in
/-- The list of candidates (empty if, unexpectedly, infinite). -/
noncomputable def cands (C : Config P XT) (Ps : Finset P) (f : P → Option ZT) :
    List (List P × (P → Option ZS)) :=
  if hfin : (candSet δ1 t post C Ps f).Finite then hfin.toFinset.toList else []

/-- Try the candidates in turn. -/
noncomputable def aloop (B : Config P M) (C : Config P XT) (Ps : Finset P) :
    List (List P × (P → Option ZS)) → List (AMv P M ZS × ARp P M ZS) →
      Prog (AMv P M ZS) (ARp P M ZS) (YRp P XT ZT)
  | [], _ => .done (.answer none)
  | (μ1, g) :: cs, hcur =>
    (reachP B (toA δ1 t (exec C μ1)) hcur).bind fun _ =>
      .ask (.oracle (toA δ1 t (exec C μ1)) (Ps, g)) fun h3 =>
        match lastResp h3 with
        | .answer (some μ') => .done (.answer (some (μ1 ++ μ')))
        | _ => aloop B C Ps cs h3

open Classical in
/-- The handler of `𝒫`. -/
noncomputable def handler (_ : List (YMv P XT ZT × YRp P XT ZT)) (ht : List (AMv P M ZS × ARp P M ZS)) :
    YMv P XT ZT → AMv P M ZS × (List (AMv P M ZS × ARp P M ZS) → Prog (AMv P M ZS) (ARp P M ZS) (YRp P XT ZT))
  | .query C q =>
    if (decided δ1 (trunc t C q)).isSome then
      (.query (toA δ1 t C) q, fun h' => .done (yResp δ1 t post (step C q) h'))
    else
      (dummy (statesOf ht).base, fun h' =>
        (reachP (statesOf ht).base (toA δ1 t (step C q)) h').bind fun h'' =>
          .done (yResp δ1 t post (step C q) h''))
  | .oracle C o => (dummy (statesOf ht).base, fun h' =>
      aloop δ1 t (statesOf ht).base C o.1 (cands δ1 t post C o.1 o.2) h')
  | .endPhase C =>
    if toA δ1 t C ∈ (statesOf ht).resp then (.endPhase (toA δ1 t C), fun _ => .done .ack)
    else (dummy (statesOf ht).base, fun _ => .done .ack)

/-- The prover `𝒫` built from `𝒫_T`. -/
noncomputable def proverS (σT : Prover P XT ZT (YQ P ZT) (Option (List P))) :
    Prover P M ZS (YQ P ZS) (Option (List P)) :=
  simulate σT (handler δ1 t post)

end Defs

/-! ## Program lemmas -/

section ProgLemmas
variable {δA : Protocol P M ZS}

lemma reveals_mono {ht : List (AMv P M ZS × ARp P M ZS)} {s : St P M} {z : Option ZS}
    (h : Reveals ht s z) (w : List (AMv P M ZS × ARp P M ZS)) : Reveals (ht ++ w) s z := by
  obtain ⟨e, he, rest⟩ := h; exact ⟨e, by simp [he], rest⟩

lemma know_eq {ht : List (AMv P M ZS × ARp P M ZS)}
    (hv : ∀ e ∈ ht, ∀ D o, e.2 = .config D o → o = outs δA D) {s : St P M}
    (hs : s.IsInit ∨ ∃ z, Reveals ht s z) : know ht s = decided δA s := by
  unfold know
  split_ifs with h
  · obtain ⟨e, he, D, o, j, h1, h2, h3⟩ := h.choose_spec
    rw [← h3, hv e he D o h1]; unfold outs; rw [h2]
  · rcases hs with hs | hs
    · obtain ⟨i, x, rfl⟩ := (St.isInit_iff _).1 hs; rfl
    · exact absurd hs h

variable [Inhabited M]

/-- Running a chain from a reached configuration along a schedule. -/
lemma chain_spec : ∀ (β : List P) (C : Config P M) (gs : GState P M) (h w hEnd),
    ProgRun h (chain C β h) w hEnd → gs.Reached C → IsSched δA C β →
    (∀ e ∈ w, ValidResp (assignSpec (P := P)) δA e.1 e.2) →
    hEnd = h ++ w ∧ LegalRun (assignSpec (P := P)) δA gs w ∧
      (w.foldl (fun g e => g.next e.1) gs).base = gs.base ∧
      (∀ D, gs.Reached D → (w.foldl (fun g e => g.next e.1) gs).Reached D) ∧
      (w.foldl (fun g e => g.next e.1) gs).Reached (exec C β) ∧
      (∀ D ∈ (w.foldl (fun g e => g.next e.1) gs).resp, D ∈ gs.resp ∨
        ∃ e ∈ w, ∃ o, e.2 = .config D o) ∧
      (∀ e ∈ w, ∃ C' q', e.1 = .query C' q') ∧
      (β ≠ [] → ∃ e ∈ w, ∃ o, e.2 = .config (exec C β) o)
  | [], C, gs, h, w, hEnd, hr, hC, _, _ => by
    cases hr
    exact ⟨by simp, trivial, rfl, fun D hD => hD, hC, fun D hD => Or.inl hD, by simp, by simp⟩
  | q :: β, C, gs, h, w, hEnd, hr, hC, hβ, hv => by
    cases hr with
    | ask _ _ _ r w' _ hr' =>
      have hr0 := hv _ (List.mem_cons.2 (Or.inl rfl))
      simp only [ValidResp] at hr0
      subst hr0
      obtain ⟨hq, hβ'⟩ := hβ
      set gs1 : GState P M := gs.next (.query C q)
      have hgs1 : gs1.Reached (step C q) := Or.inr (Set.mem_insert _ _)
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := chain_spec β (step C q) gs1 _ w' hEnd hr' hgs1 hβ'
        (fun e he => hv e (List.mem_cons_of_mem _ he))
      refine ⟨by rw [h1]; simp, ⟨⟨hC, hq⟩, h2⟩, by simpa [gs1, GState.next] using h3, fun D hD => ?_, by simpa using h5,
        fun D hD => ?_, ?_, fun _ => ?_⟩
      · simp only [List.foldl_cons]
        refine h4 D ?_
        rcases hD with ⟨u, hu⟩ | hD
        · exact Or.inl ⟨u, hu⟩
        · exact Or.inr (Set.mem_insert_of_mem _ hD)
      · simp only [List.foldl_cons] at hD
        rcases h6 D hD with hD' | ⟨e, he, o, heo⟩
        · rcases hD' with rfl | hD'
          · exact Or.inr ⟨_, List.mem_cons.2 (Or.inl rfl), _, rfl⟩
          · exact Or.inl hD'
        · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, o, heo⟩
      · intro e he; simp at he; rcases he with rfl | he
        · exact ⟨_, _, rfl⟩
        · exact h7 e he
      · by_cases hb : β = []
        · subst hb; exact ⟨_, List.mem_cons.2 (Or.inl rfl), _, rfl⟩
        · obtain ⟨e, he, o, heo⟩ := h8 hb
          exact ⟨e, List.mem_cons_of_mem _ he, o, by simpa using heo⟩

/-- Re-reaching `reinit D₀ u` for a reached `D₀`. -/
lemma rsched_spec {gs : GState P M} (hg : GInv δA gs) {D0 : Config P M} (hD0 : gs.Reached D0)
    (u : P → M) :
    exec (reinit gs.base (inputs (reinit D0 u))) (rsched gs.base (reinit D0 u)) = reinit D0 u ∧
      IsSched δA (reinit gs.base (inputs (reinit D0 u))) (rsched gs.base (reinit D0 u)) := by
  obtain ⟨x, β0, hβ0, rfl⟩ := hg.reached hD0
  set D := reinit (exec (reinit gs.base x) β0) u
  have key := exec_reinit (δ := δA) (reinit gs.base x) (inputs D) (α := β0) (fun j hj hi => by
    rw [reinit_of_isInit ((isInit_reinit_iff _ _ _).1 hi)]
    have h1 : D j = exec (reinit gs.base x) β0 j :=
      reinit_of_not_isInit (not_isInit_exec_of_mem _ hj) u
    have h2 := input_exec (reinit gs.base x) β0 j
    rw [reinit_of_isInit ((isInit_reinit_iff _ _ _).1 hi)] at h2
    simp only [inputs, h1, h2, St.input])
  rw [reinit_reinit] at key
  have hex : exec (reinit gs.base (inputs D)) β0 = D := by
    rw [key.1, reinit_inputs_reinit]
  have hβ0' : IsSched δA (reinit gs.base (inputs D)) β0 := key.2.2 hβ0
  have hc : ∃ β, exec (reinit gs.base (inputs D)) β = D := ⟨β0, hex⟩
  have hspec : exec (reinit gs.base (inputs D)) (rsched gs.base D) = D := by
    unfold rsched; rw [dif_pos hc]; exact hc.choose_spec
  exact ⟨hspec, isSched_of_exec_eq (hex.trans hspec.symm) hβ0'⟩

end ProgLemmas

end Podc.ExtensionBasedReductions
