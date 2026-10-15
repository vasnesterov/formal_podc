import Papers.PODC2025.ByzantineStableMatching.Problem

/-!
# Lemma 3: scaling down by group simulation

Constantinescu, Dufay, Ghinea, Wattenhofer, *Byzantine Stable Matching*, PODC 2025 (arXiv 2502.05889),
Lemma 3 (proof in Appendix A.2).

A protocol for many parties is turned into a protocol for few parties: every party `q` of the small
system simulates the group `grp ⁻¹' {q}` of the large system. Messages between simulated parties of
the same group are computed locally; messages between groups are bundled (`Bundle P M`: for every
simulated sender and receiver, a message). The core is `GroupSim.hist_bigScenario`: a run of the
simulator against a Byzantine set `B` corresponds to a run of the simulated protocol against the
Byzantine set `grp ⁻¹' B` (with the induced adversary), in which every simulated party of an honest
group has exactly the history its simulator reconstructs.

* `GroupSim.Solvable.of_groupSim`: generic reduction (any party types, any specifications);
* `solvable_sSM_of_groups`: the reduction for sSM with sidewise group maps;
* `lemma3`: the paper's statement for the threshold adversary;
* `lemma3_auth` / `GroupSim.SolvableAuth.of_groupSim`: the authenticated versions.
-/

namespace Papers.PODC2025.ByzantineStableMatching

open Cslib.Byzantine.LockStep Sum Classical

/-! ## Generic group simulation -/

namespace GroupSim

/-- What a simulator sends to another simulator: for every simulated sender and receiver, a
message (or nothing). -/
abbrev Bundle (P M : Type*) := P → P → Option M

variable {P Q I J O O' M : Type*}
variable (G : SimpleGraph P) (alg : Protocol P I M O) (grp : P → Q) (inp : Q → J → P → I)

/-- The histories of the simulated parties as reconstructed after `n` rounds by the simulator `q`
with input `x` and (own) history `h`. Messages from simulated parties of the own group are computed
locally, the others are read from the bundles received. -/
noncomputable def simHist (q : Q) (x : J) (h : History Q (Bundle P M)) : ℕ → P → History P M
  | 0, _ => []
  | n + 1, p => simHist q x h n p ++ [fun p₀ => if G.Adj p₀ p then
      (if grp p₀ = q then alg.send p₀ (inp q x p₀) (simHist q x h n p₀) p
       else (h[n]?).bind fun ib => (ib (grp p₀)).bind fun b => b p₀ p)
    else none]

/-- The simulating protocol: party `q` simulates the group `grp ⁻¹' {q}`, the simulated party of
`p` has input `inp q x p`; `q` decides (via `out q`) what its representative `rep q` decides. -/
noncomputable def proto (rep : Q → P) (out : Q → O → O') : Protocol Q J (Bundle P M) O' where
  send q x h q' := some fun p p' => if grp p = q ∧ grp p' = q' ∧ G.Adj p p' then
      alg.send p (inp q x p) (simHist G alg grp inp q x h h.length p) p' else none
  decide q x h := (alg.decide (rep q) (inp q x (rep q))
      (simHist G alg grp inp q x h h.length (rep q))).map (out q)

/-- The run of the simulated protocol induced by a run of the simulator: the Byzantine set is the
union of the Byzantine groups, and Byzantine simulated parties send what the bundles say. -/
def bigScenario (s : Scenario Q J (Bundle P M)) : Scenario P I M where
  byz := grp ⁻¹' s.byz
  input p := inp (grp p) (s.input (grp p)) p
  adv r p p' := (s.adv r (grp p) (grp p')).bind fun b => b p p'

lemma bigScenario_reliable (s : Scenario Q J (Bundle P M)) :
    (bigScenario grp inp s).Reliable := fun _ _ _ h => h

lemma simHist_append (q : Q) (x : J) (h : History Q (Bundle P M)) (ib : Inbox Q (Bundle P M)) :
    ∀ n ≤ h.length, simHist G alg grp inp q x (h ++ [ib]) n = simHist G alg grp inp q x h n := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    funext p
    simp only [simHist, ih (by omega), List.getElem?_append_left (show n < h.length by omega)]

lemma simHist_append_succ (q : Q) (x : J) (h : History Q (Bundle P M)) (ib : Inbox Q (Bundle P M))
    {n : ℕ} (hn : h.length = n) (p : P) :
    simHist G alg grp inp q x (h ++ [ib]) (n + 1) p = simHist G alg grp inp q x h n p ++
      [fun p₀ => if G.Adj p₀ p then
        (if grp p₀ = q then alg.send p₀ (inp q x p₀) (simHist G alg grp inp q x h n p₀) p
         else (ib (grp p₀)).bind fun b => b p₀ p)
      else none] := by
  rw [simHist, simHist_append G alg grp inp q x h ib n hn.ge]
  subst hn
  simp

variable {G alg grp inp} {GQ : SimpleGraph Q} (rep : Q → P) (out : Q → O → O')

/-- **Simulation lemma**: in the induced run, every simulated party of an honest group has the
history reconstructed by its simulator. -/
theorem hist_bigScenario (hadj : ∀ p p', G.Adj p p' → grp p ≠ grp p' → GQ.Adj (grp p) (grp p'))
    (s : Scenario Q J (Bundle P M)) (hrel : s.Reliable) :
    ∀ r p, grp p ∉ s.byz → hist G alg (bigScenario grp inp s) r p =
      simHist G alg grp inp (grp p) (s.input (grp p))
        (hist GQ (proto G alg grp inp rep out) s r (grp p)) r p := by
  intro r
  induction r with
  | zero => intro p _; rfl
  | succ r ih =>
    intro p hp
    rw [hist_succ, hist_succ, simHist_append_succ G alg grp inp _ _ _ _ (length_hist _ _ _ _ _),
      ih p hp]
    congr 1
    refine congrArg (fun f => [f]) (funext fun p₀ => ?_)
    by_cases hA : G.Adj p₀ p
    · by_cases hg : grp p₀ = grp p
      · have hp₀ : grp p₀ ∉ s.byz := hg ▸ hp
        simp only [deliver, hA, hg, ↓reduceIte,
          show p₀ ∉ (bigScenario grp inp s).byz from hp₀, bigScenario_reliable grp inp s r p₀ p,
          ih p₀ hp₀]
        simp only [bigScenario, hg]
      · have hQ := hadj p₀ p hA hg
        simp only [deliver, hA, hg, hQ, ↓reduceIte]
        by_cases hb : grp p₀ ∈ s.byz
        · simp only [show p₀ ∈ (bigScenario grp inp s).byz from hb, hb, ↓reduceIte]
          rfl
        · simp only [show p₀ ∉ (bigScenario grp inp s).byz from hb, hb, ↓reduceIte,
            bigScenario_reliable grp inp s r p₀ p, hrel _ _ _, ih p₀ hb]
          simp [proto, hA, bigScenario]
    · simp [deliver, hA]

lemma firstSome_map {O O' : Type*} {f : ℕ → Option O} {g : O → O'} {o' : O'} :
    FirstSome (fun r => (f r).map g) o' ↔ ∃ o, FirstSome f o ∧ g o = o' := by
  constructor
  · rintro ⟨r, hr, hlt⟩
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hr
    exact ⟨o, ⟨r, ho, fun r' h => Option.map_eq_none_iff.mp (hlt r' h)⟩, rfl⟩
  · rintro ⟨o, ⟨r, ho, hlt⟩, rfl⟩
    exact ⟨r, by simp [ho], fun r' h => by simp [hlt r' h]⟩

/-- An honest simulator decides what its representative decides in the induced run. -/
theorem decides_proto (hrep : ∀ q, grp (rep q) = q)
    (hadj : ∀ p p', G.Adj p p' → grp p ≠ grp p' → GQ.Adj (grp p) (grp p'))
    (s : Scenario Q J (Bundle P M)) (hrel : s.Reliable) {q : Q} (hq : q ∉ s.byz) (o' : O') :
    Decides GQ (proto G alg grp inp rep out) s q o' ↔
      ∃ o, Decides G alg (bigScenario grp inp s) (rep q) o ∧ out q o = o' := by
  have key : ∀ r, status GQ (proto G alg grp inp rep out) s r q =
      (status G alg (bigScenario grp inp s) r (rep q)).map (out q) := by
    intro r
    have := hist_bigScenario (alg := alg) (inp := inp) rep out hadj s hrel r (rep q)
      (by rw [hrep]; exact hq)
    rw [hrep] at this
    simp only [status]
    rw [this]
    simp only [proto, length_hist, bigScenario, hrep]
  rw [decides_iff_firstSome, FirstSome.congr key, firstSome_map]
  rfl

end GroupSim

namespace GroupSim

variable {P Q : Type} {I J O O' : Type*}

/-- **Generic group-simulation reduction.** If every simulated run against `grp ⁻¹' B` (`B ∈ ZQ`) is
admissible and the specification transfers along the simulation (honest groups, inputs `inp`,
decisions of the representatives translated by `out`), then solvability transfers from the large
system to the small one. -/
theorem Solvable.of_groupSim {GP : SimpleGraph P} {GQ : SimpleGraph Q} {ZP : AdvStructure P}
    {ZQ : AdvStructure Q} {specP : Spec P I O} {specQ : Spec Q J O'}
    (grp : P → Q) (rep : Q → P) (hrep : ∀ q, grp (rep q) = q) (inp : Q → J → P → I)
    (out : Q → O → O')
    (hadj : ∀ p p', GP.Adj p p' → grp p ≠ grp p' → GQ.Adj (grp p) (grp p'))
    (hZ : ∀ B ∈ ZQ, grp ⁻¹' B ∈ ZP)
    (hspec : ∀ (x : Q → J) (B : Set Q) (dec : P → O → Prop) (dec' : Q → O' → Prop),
      specP (fun p => inp (grp p) (x (grp p)) p) (grp ⁻¹' B)ᶜ dec →
      (∀ q ∉ B, ∀ o', dec' q o' ↔ ∃ o, dec (rep q) o ∧ out q o = o') →
      specQ x Bᶜ dec')
    (h : Solvable GP ZP specP) : Solvable GQ ZQ specQ := by
  obtain ⟨M, alg, halg⟩ := h
  exact ⟨Bundle P M, proto GP alg grp inp rep out, fun s hs hrel =>
    hspec s.input s.byz _ _
      (halg (bigScenario grp inp s) (hZ _ hs) (bigScenario_reliable grp inp s))
      fun q hq o' => decides_proto rep out hrep hadj s hrel hq o'⟩

end GroupSim

/-! ### Authenticated setting -/

namespace GroupSim

variable {P Q I J O O' M S : Type*}

/-- Signatures on bundles: a bundle contains the tokens of all its messages; the signer of a token
is (the simulator of) the group of its original signer. -/
def authBundle (A : Auth P M S) (grp : P → Q) : Auth Q (Bundle P M) S where
  signer τ := grp (A.signer τ)
  tokens b := {τ | ∃ p p' m, b p p' = some m ∧ τ ∈ A.tokens m}

variable {G : SimpleGraph P} {alg : Protocol P I M O} {grp : P → Q} {inp : Q → J → P → I}
  {A : Auth P M S}

/-- Tokens in reconstructed histories are signed by the own group or were received. -/
lemma histTokens_simHist (hU : alg.Unforging A) (q : Q) (x : J) (h : History Q (Bundle P M)) :
    ∀ n p, A.histTokens (simHist G alg grp inp q x h n p) ⊆
      {τ | grp (A.signer τ) = q} ∪ (authBundle A grp).histTokens h := by
  intro n
  induction n with
  | zero => intro p τ hτ; simp [simHist, Auth.histTokens] at hτ
  | succ n ih =>
    intro p τ hτ
    rw [simHist, Auth.histTokens_append] at hτ
    rcases hτ with hτ | ⟨ib, hib, p₀, m, hm, hτm⟩
    · exact ih p hτ
    · simp only [List.mem_singleton] at hib
      subst hib
      by_cases hA : G.Adj p₀ p
      · by_cases hg : grp p₀ = q
        · simp only [hA, hg, ↓reduceIte] at hm
          rcases hU _ _ _ _ _ hm τ hτm with hs | hs
          · exact Or.inl (show grp (A.signer τ) = q by rw [hs, hg])
          · exact ih p₀ hs
        · simp only [hA, hg, ↓reduceIte] at hm
          obtain ⟨ib, hib, hm⟩ := Option.bind_eq_some_iff.mp hm
          obtain ⟨b, hb, hm⟩ := Option.bind_eq_some_iff.mp hm
          exact Or.inr ⟨ib, List.mem_of_getElem? hib, grp p₀, b, hb, p₀, p, m, hm, hτm⟩
      · simp [hA] at hm

variable (rep : Q → P) (out : Q → O → O')

lemma unforging_proto (hU : alg.Unforging A) :
    (proto G alg grp inp rep out).Unforging (authBundle A grp) := by
  intro q x h q' b hb τ ⟨p, p', m, hm, hτm⟩
  simp only [proto, Option.some.injEq] at hb
  subst hb
  by_cases hc : grp p = q ∧ grp p' = q' ∧ G.Adj p p'
  · simp only [hc, and_self, ↓reduceIte] at hm
    rcases hU _ _ _ _ _ hm τ hτm with hs | hs
    · exact Or.inl (show grp (A.signer τ) = q by rw [hs, hc.1])
    · exact histTokens_simHist hU q x h _ p hs
  · simp [hc] at hm

variable {GQ : SimpleGraph Q}

lemma honestTokens_proto
    (hadj : ∀ p p', G.Adj p p' → grp p ≠ grp p' → GQ.Adj (grp p) (grp p'))
    (s : Scenario Q J (Bundle P M)) (hrel : s.Reliable) (r : ℕ) :
    honestTokens GQ (proto G alg grp inp rep out) (authBundle A grp) s r ⊆
      honestTokens G alg A (bigScenario grp inp s) r := by
  rintro τ ⟨r', hr', q₀, hq₀, q₁, -, b, hb, p, p', m, hm, hτm⟩
  simp only [proto, Option.some.injEq] at hb
  subst hb
  by_cases hc : grp p = q₀ ∧ grp p' = q₁ ∧ G.Adj p p'
  · simp only [hc, and_self, ↓reduceIte, length_hist] at hm
    obtain ⟨rfl, -, hpp'⟩ := hc
    refine ⟨r', hr', p, hq₀, p', hpp', m, ?_, hτm⟩
    rw [hist_bigScenario (inp := inp) rep out hadj s hrel r' p hq₀]
    exact hm
  · simp [hc] at hm

/-- The induced run respects unforgeability if the simulator's run does. -/
lemma authValid_bigScenario
    (hadj : ∀ p p', G.Adj p p' → grp p ≠ grp p' → GQ.Adj (grp p) (grp p'))
    (s : Scenario Q J (Bundle P M)) (hrel : s.Reliable)
    (hV : s.AuthValid GQ (proto G alg grp inp rep out) (authBundle A grp)) :
    (bigScenario grp inp s).AuthValid G alg A := by
  intro r b p m hb hp hbp hm τ hτ
  obtain ⟨bd, hbd, hm⟩ := Option.bind_eq_some_iff.mp hm
  have hg : grp b ≠ grp p := fun e => hp (show grp p ∈ s.byz from e ▸ hb)
  rcases hV r (grp b) (grp p) bd hb hp (hadj b p hbp hg) hbd τ ⟨b, p, m, hm, hτ⟩ with h | h
  · exact Or.inl h
  · exact Or.inr (honestTokens_proto rep out hadj s hrel r h)

end GroupSim

namespace GroupSim

variable {P Q : Type} {I J O O' : Type*}

/-- **Generic group-simulation reduction**, authenticated setting (same token type; a token's
signer is the group of its original signer). -/
theorem SolvableAuth.of_groupSim {GP : SimpleGraph P} {GQ : SimpleGraph Q} {ZP : AdvStructure P}
    {ZQ : AdvStructure Q} {specP : Spec P I O} {specQ : Spec Q J O'}
    (grp : P → Q) (rep : Q → P) (hrep : ∀ q, grp (rep q) = q) (inp : Q → J → P → I)
    (out : Q → O → O')
    (hadj : ∀ p p', GP.Adj p p' → grp p ≠ grp p' → GQ.Adj (grp p) (grp p'))
    (hZ : ∀ B ∈ ZQ, grp ⁻¹' B ∈ ZP)
    (hspec : ∀ (x : Q → J) (B : Set Q) (dec : P → O → Prop) (dec' : Q → O' → Prop),
      specP (fun p => inp (grp p) (x (grp p)) p) (grp ⁻¹' B)ᶜ dec →
      (∀ q ∉ B, ∀ o', dec' q o' ↔ ∃ o, dec (rep q) o ∧ out q o = o') →
      specQ x Bᶜ dec')
    (h : SolvableAuth GP ZP specP) : SolvableAuth GQ ZQ specQ := by
  obtain ⟨M, S, A, alg, hU, halg⟩ := h
  exact ⟨Bundle P M, S, authBundle A grp, proto GP alg grp inp rep out,
    unforging_proto rep out hU, fun s hs hrel hV =>
    hspec s.input s.byz _ _
      (halg (bigScenario grp inp s) (hZ _ hs) (bigScenario_reliable grp inp s)
        (authValid_bigScenario rep out hadj s hrel hV))
      fun q hq o' => decides_proto rep out hrep hadj s hrel hq o'⟩

end GroupSim


/-! ## Sidewise group maps: the reduction for sSM -/

section Sidewise

variable {k d : ℕ} (gL gR : Fin k → Fin d) (repL repR : Fin d → Fin k)

/-- The sidewise group map: `inl i ↦ inl (gL i)`, `inr j ↦ inr (gR j)`. -/
def grpMap : Party k → Party d := Sum.map gL gR

/-- The representatives, sidewise. -/
def repMap : Party d → Party k := Sum.map repL repR

/-- Inputs of the simulated parties: the translated favourite of the simulator (it is the
representative's favourite; the other simulated parties get the same, arbitrary, favourite). -/
def simInput : Party d → Fin d → Party k → Fin k :=
  fun _ x p => Sum.elim (fun _ => repR x) (fun _ => repL x) p

/-- Output translation: if the representative matches the representative of a group of the other
side, output that group, otherwise nobody. -/
def simOutput : Party d → Option (Fin k) → Option (Fin d)
  | inl _, o => o.bind fun j => if repR (gR j) = j then some (gR j) else none
  | inr _, o => o.bind fun i => if repL (gL i) = i then some (gL i) else none

variable {gL gR repL repR}

lemma grpMap_repMap (hL : ∀ i, gL (repL i) = i) (hR : ∀ j, gR (repR j) = j) (q : Party d) :
    grpMap gL gR (repMap repL repR q) = q := by
  rcases q with i | j <;> simp [grpMap, repMap, hL, hR]

lemma simOutput_inl (hR : ∀ j, gR (repR j) = j) (i : Fin d) (o : Option (Fin k)) (j : Fin d) :
    simOutput gL gR repL repR (inl i) o = some j ↔ o = some (repR j) := by
  rcases o with _ | j₀
  · simp [simOutput]
  · simp only [simOutput, Option.bind_some, Option.some.injEq]
    constructor
    · intro h
      split_ifs at h with h₀
      · rw [← Option.some_injective _ h, h₀]
    · rintro rfl
      simp [hR]

lemma simOutput_inr (hL : ∀ i, gL (repL i) = i) (j : Fin d) (o : Option (Fin k)) (i : Fin d) :
    simOutput gL gR repL repR (inr j) o = some i ↔ o = some (repL i) := by
  rcases o with _ | i₀
  · simp [simOutput]
  · simp only [simOutput, Option.bind_some, Option.some.injEq]
    constructor
    · intro h
      split_ifs at h with h₀
      · rw [← Option.some_injective _ h, h₀]
    · rintro rfl
      simp [hL]

/-- The specification transfer for sSM: the representatives' decisions in the simulated run,
translated by `simOutput`, solve sSM on the small system. -/
lemma sSM_groupSim (hL : ∀ i, gL (repL i) = i) (hR : ∀ j, gR (repR j) = j)
    (x : Party d → Fin d) (B : Set (Party d)) (dec : Party k → Option (Fin k) → Prop)
    (dec' : Party d → Option (Fin d) → Prop)
    (h : sSM k (fun p => simInput repL repR (grpMap gL gR p) (x (grpMap gL gR p)) p)
      (grpMap gL gR ⁻¹' B)ᶜ dec)
    (hdec : ∀ q ∉ B, ∀ o', dec' q o' ↔
      ∃ o, dec (repMap repL repR q) o ∧ simOutput gL gR repL repR q o = o') :
    sSM d x Bᶜ dec' := by
  obtain ⟨hc, hst⟩ := h
  have hon : ∀ q, q ∈ Bᶜ → repMap repL repR q ∈ (grpMap gL gR ⁻¹' B)ᶜ := by
    intro q hq
    simpa [grpMap_repMap hL hR] using hq
  have decL : ∀ i, inl i ∈ Bᶜ → ∀ j, dec' (inl i) (some j) ↔ dec (inl (repL i)) (some (repR j)) := by
    intro i hi j
    rw [hdec _ hi]
    simp only [simOutput_inl hR, repMap, Sum.map_inl]
    exact ⟨fun ⟨o, ho, he⟩ => he ▸ ho, fun ho => ⟨_, ho, rfl⟩⟩
  have decR : ∀ j, inr j ∈ Bᶜ → ∀ i, dec' (inr j) (some i) ↔ dec (inr (repR j)) (some (repL i)) := by
    intro j hj i
    rw [hdec _ hj]
    simp only [simOutput_inr hL, repMap, Sum.map_inr]
    exact ⟨fun ⟨o, ho, he⟩ => he ▸ ho, fun ho => ⟨_, ho, rfl⟩⟩
  have injL : Function.Injective repL := fun a b e => by rw [← hL a, e, hL b]
  have injR : Function.Injective repR := fun a b e => by rw [← hR a, e, hR b]
  refine ⟨⟨fun q hq => ?_, fun i j hi hj => ?_, fun p q hp hq hpq z z' hz hz' => ?_⟩,
    fun i j hi hj hxi hxj => ?_⟩
  · obtain ⟨o, ho⟩ := hc.termination _ (hon q hq)
    exact ⟨_, (hdec q hq _).mpr ⟨o, ho, rfl⟩⟩
  · rw [decL i hi, decR j hj]
    exact hc.symmetry _ _ (hon _ hi) (hon _ hj)
  · rcases p with i | j <;> rcases q with i' | j'
    · rw [decL i hp] at hz
      rw [decL i' hq] at hz'
      have hne : inl (repL i) ≠ (inl (repL i') : Party k) := by
        simpa using fun e => hpq (by rw [injL e])
      have := hc.nonCompetition _ _ (hon _ hp) (hon _ hq) hne _ _ hz hz'
      simp only [repMap, Sum.map_inl, partner, ne_eq, Sum.inr.injEq] at this ⊢
      exact fun e => this (by rw [e])
    · simp [partner]
    · simp [partner]
    · rw [decR j hp] at hz
      rw [decR j' hq] at hz'
      have hne : inr (repR j) ≠ (inr (repR j') : Party k) := by
        simpa using fun e => hpq (by rw [injR e])
      have := hc.nonCompetition _ _ (hon _ hp) (hon _ hq) hne _ _ hz hz'
      simp only [repMap, Sum.map_inr, partner, ne_eq, Sum.inl.injEq] at this ⊢
      exact fun e => this (by rw [e])
  · rw [decL i hi, decR j hj]
    apply hst _ _ (hon _ hi) (hon _ hj)
    · simp [simInput, grpMap, hL, hxi]
    · simp [simInput, grpMap, hR, hxj]

/-- **Lemma 3, general form** (unauthenticated): with sidewise surjective group maps `gL`, `gR` with
representatives `repL`, `repR`, if cross-group edges of `Gk` are edges of `Gd` and the union of the
groups of an admissible Byzantine set of the small system is admissible in the large system, then
solvability of sSM transfers from `2k` to `2d` parties. -/
theorem solvable_sSM_of_groups {Gk : SimpleGraph (Party k)} {Gd : SimpleGraph (Party d)}
    {Zk : AdvStructure (Party k)} {Zd : AdvStructure (Party d)}
    (hL : ∀ i, gL (repL i) = i) (hR : ∀ j, gR (repR j) = j)
    (hadj : ∀ p q, Gk.Adj p q → grpMap gL gR p ≠ grpMap gL gR q →
      Gd.Adj (grpMap gL gR p) (grpMap gL gR q))
    (hZ : ∀ B ∈ Zd, grpMap gL gR ⁻¹' B ∈ Zk)
    (h : Solvable Gk Zk (sSM k)) : Solvable Gd Zd (sSM d) :=
  GroupSim.Solvable.of_groupSim (grpMap gL gR) (repMap repL repR) (grpMap_repMap hL hR)
    (simInput repL repR) (simOutput gL gR repL repR) hadj hZ
    (fun x B dec dec' h hdec => sSM_groupSim hL hR x B dec dec' h hdec) h

/-- **Lemma 3, general form** (authenticated). -/
theorem solvableAuth_sSM_of_groups {Gk : SimpleGraph (Party k)} {Gd : SimpleGraph (Party d)}
    {Zk : AdvStructure (Party k)} {Zd : AdvStructure (Party d)}
    (hL : ∀ i, gL (repL i) = i) (hR : ∀ j, gR (repR j) = j)
    (hadj : ∀ p q, Gk.Adj p q → grpMap gL gR p ≠ grpMap gL gR q →
      Gd.Adj (grpMap gL gR p) (grpMap gL gR q))
    (hZ : ∀ B ∈ Zd, grpMap gL gR ⁻¹' B ∈ Zk)
    (h : SolvableAuth Gk Zk (sSM k)) : SolvableAuth Gd Zd (sSM d) :=
  GroupSim.SolvableAuth.of_groupSim (grpMap gL gR) (repMap repL repR) (grpMap_repMap hL hR)
    (simInput repL repR) (simOutput gL gR repL repR) hadj hZ
    (fun x B dec dec' h hdec => sSM_groupSim hL hR x B dec dec' h hdec) h

end Sidewise

/-! ## Lemma 3 for the threshold adversary -/

section Threshold

variable {k d : ℕ}

/-- The concrete partition used for Lemma 3: `i ↦ i mod d`. For `0 < d ≤ k` its groups are nonempty
(`j` is in group `j`) and have size at most `⌈k/d⌉ = (k + d - 1) / d`.
(The partition `i ↦ i / ⌈k/d⌉` would not do: e.g. for `k = 4`, `d = 3` it has only 2 groups.) -/
def modGroup (hd : 0 < d) (i : Fin k) : Fin d := ⟨i % d, Nat.mod_lt _ hd⟩

lemma modGroup_castLE (hd : 0 < d) (hdk : d ≤ k) (i : Fin d) :
    modGroup hd (Fin.castLE hdk i) = i := by
  ext; simp [modGroup, Nat.mod_eq_of_lt i.2]

/-- Groups of `modGroup` have at most `⌈k/d⌉` elements. -/
lemma ncard_preimage_modGroup_le (hd : 0 < d) (S : Set (Fin d)) :
    (modGroup (k := k) hd ⁻¹' S).ncard ≤ (k + d - 1) / d * S.ncard := by
  set c := (k + d - 1) / d with hc_def
  have hc : ∀ i : Fin k, i.val / d < c := by
    intro i
    rw [Nat.div_lt_iff_lt_mul hd]
    have h1 : k + d - 1 < c * d + d := Nat.lt_div_mul_add hd
    have h2 := i.2
    omega
  calc (modGroup hd ⁻¹' S).ncard ≤ (S ×ˢ (Set.univ : Set (Fin c))).ncard :=
        Set.ncard_le_ncard_of_injOn (fun i => (modGroup hd i, (⟨i.val / d, hc i⟩ : Fin c)))
          (fun i hi => ⟨hi, trivial⟩) (by
            intro i _ j _ e
            simp only [Prod.mk.injEq, modGroup, Fin.mk.injEq] at e
            ext
            rw [← Nat.div_add_mod i.val d, ← Nat.div_add_mod j.val d, e.1, e.2])
    _ = c * S.ncard := by
        rw [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, mul_comm]

lemma preimage_grpMap_mem_thresholds (hd : 0 < d) {tL tR : ℕ} {B : Set (Party d)}
    (hB : B ∈ thresholds d (tL / ((k + d - 1) / d)) (tR / ((k + d - 1) / d))) :
    grpMap (modGroup (k := k) hd) (modGroup hd) ⁻¹' B ∈ thresholds k tL tR := by
  obtain ⟨hBL, hBR⟩ := hB
  have eL : inl ⁻¹' (grpMap (modGroup (k := k) hd) (modGroup hd) ⁻¹' B) =
      modGroup hd ⁻¹' (inl ⁻¹' B) := by ext; simp [grpMap]
  have eR : inr ⁻¹' (grpMap (modGroup (k := k) hd) (modGroup hd) ⁻¹' B) =
      modGroup hd ⁻¹' (inr ⁻¹' B) := by ext; simp [grpMap]
  refine ⟨?_, ?_⟩
  · rw [eL]
    calc _ ≤ (k + d - 1) / d * (inl ⁻¹' B).ncard := ncard_preimage_modGroup_le hd _
      _ ≤ (k + d - 1) / d * (tL / ((k + d - 1) / d)) := Nat.mul_le_mul_left _ hBL
      _ ≤ tL := Nat.mul_div_le _ _
  · rw [eR]
    calc _ ≤ (k + d - 1) / d * (inr ⁻¹' B).ncard := ncard_preimage_modGroup_le hd _
      _ ≤ (k + d - 1) / d * (tR / ((k + d - 1) / d)) := Nat.mul_le_mul_left _ hBR
      _ ≤ tR := Nat.mul_div_le _ _

/-- The four networks of the paper are compatible with sidewise group maps. -/
lemma adj_grpMap {G : (n : ℕ) → SimpleGraph (Party n)}
    (hG : G = fully ∨ G = oneSided ∨ G = oneSidedR ∨ G = bipartite) (gL gR : Fin k → Fin d)
    (p q : Party k) (hpq : (G k).Adj p q) (hne : grpMap gL gR p ≠ grpMap gL gR q) :
    (G d).Adj (grpMap gL gR p) (grpMap gL gR q) := by
  rcases hG with rfl | rfl | rfl | rfl <;>
    rcases p with p | p <;> rcases q with q | q <;> simp_all [grpMap]

/-- **Lemma 3** of [Constantinescu–Dufay–Ghinea–Wattenhofer, PODC 2025] (unauthenticated): if sSM on
`2k` parties is solvable against `tL` Byzantine parties in `L` and `tR` in `R`, then for any
`0 < d ≤ k`, sSM on `2d` parties is solvable against `⌊tL / ⌈k/d⌉⌋` and `⌊tR / ⌈k/d⌉⌋` Byzantine
parties, on the same kind of network (fully connected, one-sided, or bipartite). -/
theorem lemma3 {G : (n : ℕ) → SimpleGraph (Party n)}
    (hG : G = fully ∨ G = oneSided ∨ G = oneSidedR ∨ G = bipartite) {k d tL tR : ℕ}
    (hd : 0 < d) (hdk : d ≤ k) (h : Solvable (G k) (thresholds k tL tR) (sSM k)) :
    Solvable (G d) (thresholds d (tL / ((k + d - 1) / d)) (tR / ((k + d - 1) / d))) (sSM d) :=
  solvable_sSM_of_groups (repL := Fin.castLE hdk) (repR := Fin.castLE hdk)
    (modGroup_castLE hd hdk) (modGroup_castLE hd hdk) (adj_grpMap hG _ _)
    (fun _ hB => preimage_grpMap_mem_thresholds hd hB) h

/-- **Lemma 3** of [Constantinescu–Dufay–Ghinea–Wattenhofer, PODC 2025], authenticated setting. -/
theorem lemma3_auth {G : (n : ℕ) → SimpleGraph (Party n)}
    (hG : G = fully ∨ G = oneSided ∨ G = oneSidedR ∨ G = bipartite) {k d tL tR : ℕ}
    (hd : 0 < d) (hdk : d ≤ k) (h : SolvableAuth (G k) (thresholds k tL tR) (sSM k)) :
    SolvableAuth (G d) (thresholds d (tL / ((k + d - 1) / d)) (tR / ((k + d - 1) / d))) (sSM d) :=
  solvableAuth_sSM_of_groups (repL := Fin.castLE hdk) (repR := Fin.castLE hdk)
    (modGroup_castLE hd hdk) (modGroup_castLE hd hdk) (adj_grpMap hG _ _)
    (fun _ hB => preimage_grpMap_mem_thresholds hd hB) h

/-- Remark: Lemma 3 does not give what the paper's Lemma 13 needs. Scaling from `k = 4` to `d = 3`
with `tR = k = 4` only yields `tR' = ⌊4 / ⌈4/3⌉⌋ = 2 < 3 = d` Byzantine parties on the right, so the
paper's appeal to Lemma 3 in Lemma 13 is not valid for such `k`. -/
lemma lemma3_not_enough_for_lemma13 : (4 : ℕ) / ((4 + 3 - 1) / 3) = 2 := by norm_num

end Threshold

end Papers.PODC2025.ByzantineStableMatching
