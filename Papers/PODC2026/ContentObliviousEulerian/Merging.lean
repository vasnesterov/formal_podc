import Papers.PODC2026.ContentObliviousEulerian.Repair
import Papers.PODC2026.ContentObliviousEulerian.PointerForest

/-!
# Lemma 5: merging the circuits into one Eulerian circuit (combinatorial core)

Frei, Gelles, Ghazy, Nolin, PODC 2026, §2.2, Lemma 5.

We formalize the circuit-level effect of the merging phases (not the pulse-level protocol that
implements them). A *state* is a pairing `π` together with a leader map `lead : G.Dart → V` such
that two darts are on the same circuit iff their circuits have the same leader, and the leader of a
circuit is a node of it (`LeaderInv`). Circuits are identified with their leaders (`Ldr lead`); two
circuits are adjacent if they share a node (`CircAdj`).

**One phase** (`PhaseStep`). Every circuit `C` determines the adjacent circuit `ptr C` whose leader
has the largest ID. Every circuit `C` merges into `ptr C`, *except* the larger circuit of a mutually
pointing pair (`Pointer.IsRoot`). Each merge is done by a node common to `C` and `ptr C` that
re-pairs one of its pairs on (the current circuit containing) `C` with one on `ptr C`, as in
Lemma 4 with two pairs (`Pairing.join`); the merges are executed one after the other, in any order
and at any common nodes. The new leader of a merged circuit is its root (the largest ID).

The exception for mutual pairs is our repair of the paper's sketch, which lets *every* circuit
merge into its neighbour: in a mutual pair both merges would be executed, the second one inside a
single circuit, which can split it again (`DoubleMerge.lean`).

Results: a phase keeps the invariant and at least halves the number of circuits
(`phaseStep_spec`); a phase is possible as long as there are at least two circuits
(`exists_phaseStep`, using connectivity); with a single circuit no phase is possible and that
circuit is an Eulerian circuit (`single_circuit_eulerian`). Hence after at most `log₂ n` phases a
single Eulerian circuit with a single leader remains (`lemma5`).
-/

namespace Podc.ContentObliviousEulerian

open Finset SimpleGraph Pointer

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

set_option linter.unusedSectionVars false

namespace Pairing

variable (π : Pairing G)

lemma two_dist {a a' : G.Dart} (hc : ¬ π.Circ a a') :
    ∀ i j : Fin 2, i ≠ j → ¬ π.Circ (![a, a'] i) (![a, a'] j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · exact hc
  · exact fun h => hc h.symm

/-- Merge the circuits through the darts `a` and `a'` (at the same node, on different circuits):
the node re-pairs `(a, b), (a', b')` as `(b, a'), (b', a)` (Lemma 4 with two pairs). -/
noncomputable def join (a a' : G.Dart) (h : a.fst = a'.fst) (hc : ¬ π.Circ a a') : Pairing G :=
  π.repair ![a, a'] (v := a.fst) (by intro i; fin_cases i <;> simp [h])
    (π.injective_of_dist (π.two_dist hc)) (π.ne_pair_of_dist (π.two_dist hc))

/-- After a join, the two circuits are merged and nothing else changes. -/
theorem join_circ {a a' : G.Dart} (h : a.fst = a'.fst) (hc : ¬ π.Circ a a') (d d' : G.Dart) :
    (π.join a a' h hc).Circ d d' ↔
      π.Circ d d' ∨ ((π.Circ a d ∨ π.Circ a' d) ∧ (π.Circ a d' ∨ π.Circ a' d')) := by
  unfold join
  rw [π.lemma4 _ _ _ (π.two_dist hc)]
  simp [Pairing.U, Fin.exists_fin_two]

open Classical in
/-- A join that is performed only if its two darts are at the same node and on different
circuits (otherwise nothing happens). -/
noncomputable def joinIf (a a' : G.Dart) : Pairing G :=
  if h : a.fst = a'.fst ∧ ¬ π.Circ a a' then π.join a a' h.1 h.2 else π

/-- Execute a list of joins one after the other. -/
noncomputable def execLinks (L : List (G.Dart × G.Dart)) : Pairing G :=
  L.foldl (fun σ p => σ.joinIf p.1 p.2) π

end Pairing

/-! ### States: pairings with circuit leaders -/

/-- The leader map `lead` labels the circuits of `π`: two darts are on the same circuit iff their
leaders coincide (distinct circuits have distinct leaders), and the leader is a node of the
circuit. -/
structure LeaderInv (π : Pairing G) (lead : G.Dart → V) : Prop where
  circ_iff : ∀ d d', π.Circ d d' ↔ lead d = lead d'
  mem : ∀ d, ∃ x, π.Circ d x ∧ x.fst = lead d

/-- The set of circuit leaders. -/
def leaders (lead : G.Dart → V) : Finset V := univ.image lead

/-- Circuits, identified with their leaders. -/
abbrev Ldr (lead : G.Dart → V) := {ℓ : V // ℓ ∈ leaders lead}

/-- The circuit of a dart. -/
def ldr (lead : G.Dart → V) (d : G.Dart) : Ldr lead := ⟨lead d, mem_image_of_mem _ (mem_univ _)⟩

/-- Two (distinct) circuits are adjacent if they share a node. -/
def CircAdj (lead : G.Dart → V) (ℓ ℓ' : Ldr lead) : Prop :=
  ℓ ≠ ℓ' ∧ ∃ d d' : G.Dart, lead d = ℓ.1 ∧ lead d' = ℓ'.1 ∧ d.fst = d'.fst

/-- The circuit graph with the leaders' IDs, as a setting for the pointer argument. -/
def setting (lead : G.Dart → V) (ID : V → ℕ) (hID : Function.Injective ID)
    (hadj : ∀ ℓ : Ldr lead, ∃ ℓ', CircAdj lead ℓ ℓ') : Setting (Ldr lead) where
  adj := CircAdj lead
  symm := by
    rintro x y ⟨hne, d, d', h1, h2, h3⟩; exact ⟨hne.symm, d', d, h2, h1, h3.symm⟩
  irrefl x h := h.1 rfl
  id ℓ := ID ℓ.1
  id_inj x y h := Subtype.ext (hID h)
  exists_adj := hadj

/-- **One merging phase** (Lemma 5). Every circuit that is not a root (the larger one of a mutually
pointing pair) merges into the adjacent circuit with the largest leader ID: the links are executed
one by one (`l` lists the non-roots in any order), each at some node common to both circuits
(`pick s` = a dart of circuit `s` and a dart of circuit `ptr s` at a common node). The merged
circuit is led by its root. -/
def PhaseStep (ID : V → ℕ) (hID : Function.Injective ID) (π : Pairing G) (lead : G.Dart → V)
    (π' : Pairing G) (lead' : G.Dart → V) : Prop :=
  ∃ (hadj : ∀ ℓ : Ldr lead, ∃ ℓ', CircAdj lead ℓ ℓ') (l : List (Ldr lead))
    (pick : Ldr lead → G.Dart × G.Dart),
    (∀ x, x ∈ l ↔ ¬ IsRoot (setting lead ID hID hadj) x) ∧ l.Nodup ∧
    (∀ s, lead (pick s).1 = s.1 ∧ lead (pick s).2 = (ptr (setting lead ID hID hadj) s).1 ∧
      (pick s).1.fst = (pick s).2.fst) ∧
    π' = π.execLinks (l.map pick) ∧
    ∀ d, lead' d = (top (setting lead ID hID hadj) (ldr lead d)).1

section phase

variable {π : Pairing G} {lead : G.Dart → V} (hinv : LeaderInv π lead)
  {ID : V → ℕ} (hID : Function.Injective ID)

include hinv in
lemma ldr_eq_iff (d d' : G.Dart) : ldr lead d = ldr lead d' ↔ π.Circ d d' := by
  rw [hinv.circ_iff]; exact Subtype.ext_iff

include hinv in
/-- Executing a prefix of the links of a phase: the circuits are exactly the classes of the links
executed so far (each link joins two different circuits, by the forest property). -/
lemma execLinks_prefix (hadj : ∀ ℓ : Ldr lead, ∃ ℓ', CircAdj lead ℓ ℓ') {l : List (Ldr lead)}
    (hl : ∀ x ∈ l, ¬ IsRoot (setting lead ID hID hadj) x) (hnd : l.Nodup)
    {pick : Ldr lead → G.Dart × G.Dart}
    (hpick : ∀ s, lead (pick s).1 = s.1 ∧ lead (pick s).2 = (ptr (setting lead ID hID hadj) s).1 ∧
      (pick s).1.fst = (pick s).2.fst) :
    ∀ l₁ l₂, l = l₁ ++ l₂ → ∀ d d', (π.execLinks (l₁.map pick)).Circ d d' ↔
      linkRel (setting lead ID hID hadj) l₁ (ldr lead d) (ldr lead d') := by
  intro l₁
  induction l₁ using List.reverseRecOn with
  | nil =>
    intro l₂ _ d d'
    simp only [List.map_nil, Pairing.execLinks, List.foldl_nil, linkRel]
    exact (ldr_eq_iff hinv d d').symm
  | append_singleton l₁ s ih =>
    intro l₂ hl₁ d d'
    have hl' : l = l₁ ++ s :: l₂ := by rw [hl₁]; simp
    have ih' := ih (s :: l₂) hl'
    set S := setting lead ID hID hadj
    set σ := π.execLinks (l₁.map pick)
    have hσ : π.execLinks ((l₁ ++ [s]).map pick) = σ.joinIf (pick s).1 (pick s).2 := by
      simp [Pairing.execLinks, σ, List.foldl_append]
    have hs1 : ldr lead (pick s).1 = s := Subtype.ext (hpick s).1
    have hs2 : ldr lead (pick s).2 = ptr S s := Subtype.ext (hpick s).2.1
    have hnc : ¬ σ.Circ (pick s).1 (pick s).2 := by
      rw [ih', hs1, hs2]
      exact not_linkRel_of_nodup S hnd hl hl'
    rw [hσ, Pairing.joinIf, dite_eq_left ⟨(hpick s).2.2, hnc⟩, σ.join_circ, linkRel_append_singleton,
      addLink, ih', ih', ih', ih', ih', hs1, hs2]

include hinv in
/-- **A phase keeps the invariant and at least halves the number of circuits.** The new circuits
are the trees of merge links, each led by its root, which has the largest leader ID of the tree. -/
theorem phaseStep_spec {π' : Pairing G} {lead' : G.Dart → V}
    (h : PhaseStep ID hID π lead π' lead') :
    LeaderInv π' lead' ∧ 2 * (leaders lead').card ≤ (leaders lead).card := by
  obtain ⟨hadj, l, pick, hmem, hnd, hpick, rfl, hlead⟩ := h
  set S := setting lead ID hID hadj
  have hfin : ∀ d d', (π.execLinks (l.map pick)).Circ d d' ↔
      top S (ldr lead d) = top S (ldr lead d') := by
    intro d d'
    rw [execLinks_prefix hinv hID hadj (fun x hx => (hmem x).1 hx) hnd hpick l [] (by simp),
      linkRel_iff_top S hmem]
  refine ⟨⟨fun d d' => by rw [hfin, hlead, hlead, Subtype.ext_iff], fun d => ?_⟩, ?_⟩
  · set r := top S (ldr lead d)
    obtain ⟨y, -, hy⟩ := mem_image.1 r.2
    obtain ⟨x, hyx, hx⟩ := hinv.mem y
    refine ⟨x, ?_, by rw [hx, hlead, hy]⟩
    rw [hfin]
    have : ldr lead x = r := by
      apply Subtype.ext
      simp only [ldr]; rw [← (hinv.circ_iff y x).1 hyx, hy]
    rw [this, top_of_isRoot S (isRoot_top S _)]
  · have hsub : leaders lead' ⊆ (univ.image (top S)).map (Function.Embedding.subtype _) := by
      intro v hv
      obtain ⟨d, -, rfl⟩ := mem_image.1 hv
      rw [hlead]
      exact mem_map.2 ⟨_, mem_image_of_mem _ (mem_univ _), rfl⟩
    have := card_le_card hsub
    rw [card_map] at this
    have h2 := two_mul_card_image_top_le S
    rw [Fintype.card_coe] at h2
    omega

include hinv in
/-- If the network is connected and there are at least two circuits, every circuit is adjacent to
another one. -/
lemma exists_circAdj (hconn : G.Connected) (h2 : 1 < (leaders lead).card) (ℓ : Ldr lead) :
    ∃ ℓ', CircAdj lead ℓ ℓ' := by
  by_contra hno
  push Not at hno
  have hsame : ∀ d d' : G.Dart, lead d = ℓ.1 → d.fst = d'.fst → lead d' = ℓ.1 := by
    intro d d' hd hdd'
    by_contra hne
    exact hno (ldr lead d') ⟨fun h => hne (by rw [h]; rfl), d, d', hd, rfl, hdd'⟩
  let P : V → Prop := fun u => ∃ d : G.Dart, lead d = ℓ.1 ∧ d.fst = u
  have hstep : ∀ u w, G.Adj u w → P u → P w := by
    rintro u w huw ⟨d, hd, rfl⟩
    let e : G.Dart := ⟨(d.fst, w), huw⟩
    have he : lead e = ℓ.1 := hsame d e hd rfl
    refine ⟨e.symm, ?_, rfl⟩
    rw [← (hinv.circ_iff e e.symm).1 (Pairing.Circ.symm_dart π e), he]
  have hwalk : ∀ {u w} (p : G.Walk u w), P u → P w := by
    intro u w p
    induction p with
    | nil => exact id
    | cons h _ ih => exact fun hu => ih (hstep _ _ h hu)
  obtain ⟨d₀, -, hd₀⟩ := mem_image.1 ℓ.2
  have hall : ∀ d : G.Dart, lead d = ℓ.1 := by
    intro d
    obtain ⟨p⟩ := hconn.preconnected d₀.fst d.fst
    obtain ⟨x, hx, hxd⟩ := hwalk p ⟨d₀, hd₀, rfl⟩
    exact hsame x d hx hxd
  have : leaders lead ⊆ {ℓ.1} := by
    intro v hv; obtain ⟨d, -, rfl⟩ := mem_image.1 hv; simp [hall d]
  have := card_le_card this
  simp at this; omega

include hinv in
/-- A phase is possible as long as there are at least two circuits (connected network). -/
theorem exists_phaseStep (hconn : G.Connected) (h2 : 1 < (leaders lead).card) :
    ∃ π' lead', PhaseStep ID hID π lead π' lead' := by
  classical
  have hadj := exists_circAdj hinv hconn h2
  set S := setting lead ID hID hadj
  have hpick : ∀ s : Ldr lead, ∃ p : G.Dart × G.Dart, lead p.1 = s.1 ∧
      lead p.2 = (ptr S s).1 ∧ p.1.fst = p.2.fst := by
    intro s
    obtain ⟨-, d, d', h1, h2, h3⟩ := adj_ptr S s
    exact ⟨(d, d'), h1, h2, h3⟩
  choose pick hpick using hpick
  let l := (univ.filter (fun x => ¬ IsRoot S x)).toList
  exact ⟨_, _, hadj, l, pick, fun x => by simp [l, S], nodup_toList _, hpick, rfl, fun _ => rfl⟩

include hinv in
/-- With a single circuit no phase is possible, and every circuit walk is an Eulerian circuit. -/
theorem single_circuit_eulerian (h1 : (leaders lead).card = 1) :
    (∀ π' lead', ¬ PhaseStep ID hID π lead π' lead') ∧
    ∀ d : G.Dart, (π.circuitWalk d).IsCircuit ∧ (π.circuitWalk d).IsEulerian := by
  obtain ⟨ℓ, hℓ⟩ := card_eq_one.1 h1
  have hall : ∀ d : G.Dart, lead d = ℓ := fun d => by
    have : lead d ∈ leaders lead := mem_image_of_mem _ (mem_univ _)
    rw [hℓ] at this; simpa using this
  refine ⟨?_, fun d => ⟨π.circuitWalk_isCircuit d, ?_⟩⟩
  · rintro π' lead' ⟨hadj, -⟩
    obtain ⟨v, hv⟩ := card_pos.1 (h1 ▸ Nat.one_pos : 0 < (leaders lead).card)
    obtain ⟨⟨w, hw⟩, hne, -⟩ := hadj ⟨v, hv⟩
    apply hne; apply Subtype.ext
    obtain ⟨d, -, rfl⟩ := mem_image.1 hv
    obtain ⟨d', -, rfl⟩ := mem_image.1 hw
    show lead d = lead d'
    rw [hall, hall]
  · apply Pairing.isEulerian_of_edges _ (π.circuitWalk_isCircuit d).isTrail
    rw [π.circuitWalk_edges_toFinset]
    apply subset_antisymm (π.circuitEdges_subset_edgeFinset d)
    intro e he
    obtain ⟨x, rfl⟩ := Pairing.exists_dart_of_mem_edgeSet (mem_edgeFinset.1 he)
    have : π.Circ d x := (hinv.circ_iff d x).2 (by rw [hall, hall])
    rw [π.circuitEdges_eq_of_circ this]
    exact π.edge_mem_circuitEdges x

end phase

/-- Runs of `T` merging phases. -/
inductive PhaseRun (ID : V → ℕ) (hID : Function.Injective ID) :
    ℕ → Pairing G → (G.Dart → V) → Pairing G → (G.Dart → V) → Prop
  | refl (π lead) : PhaseRun ID hID 0 π lead π lead
  | step {T π lead π' lead' π'' lead''} : PhaseStep ID hID π lead π' lead' →
      PhaseRun ID hID T π' lead' π'' lead'' → PhaseRun ID hID (T + 1) π lead π'' lead''

lemma PhaseRun.spec {ID : V → ℕ} {hID : Function.Injective ID} {T : ℕ} {π π' : Pairing G}
    {lead lead' : G.Dart → V} (h : PhaseRun ID hID T π lead π' lead') (hinv : LeaderInv π lead) :
    LeaderInv π' lead' ∧ 2 ^ T * (leaders lead').card ≤ (leaders lead).card := by
  induction h with
  | refl => exact ⟨hinv, by simp⟩
  | step hs _ ih =>
    obtain ⟨hinv', h2⟩ := phaseStep_spec hinv _ hs
    obtain ⟨hinv'', h3⟩ := ih hinv'
    refine ⟨hinv'', ?_⟩
    rw [pow_succ]; nlinarith

/-- **Lemma 5 (circuit level).** In a connected network, starting from circuits with distinct
leaders: every run of merging phases has at most `log₂ n` phases (as long as a circuit remains);
a further phase is possible whenever at least two circuits remain; and when no phase is possible,
a single circuit with a single leader remains and it is an Eulerian circuit. -/
theorem lemma5 (hconn : G.Connected) (ID : V → ℕ) (hID : Function.Injective ID)
    {π : Pairing G} {lead : G.Dart → V} (hinv : LeaderInv π lead) :
    (∀ T π' lead', PhaseRun ID hID T π lead π' lead' →
      LeaderInv π' lead' ∧ (0 < (leaders lead').card → T ≤ Nat.log 2 (Fintype.card V)) ∧
      (1 < (leaders lead').card → ∃ π'' lead'', PhaseStep ID hID π' lead' π'' lead'') ∧
      ((leaders lead').card = 1 →
        (∀ π'' lead'', ¬ PhaseStep ID hID π' lead' π'' lead'') ∧
        ∀ d : G.Dart, (π'.circuitWalk d).IsCircuit ∧ (π'.circuitWalk d).IsEulerian)) := by
  intro T π' lead' hrun
  obtain ⟨hinv', hcard⟩ := hrun.spec hinv
  refine ⟨hinv', fun hpos => ?_, fun h2 => exists_phaseStep hinv' hID hconn h2,
    fun h1 => single_circuit_eulerian hinv' hID h1⟩
  have hle : (leaders lead).card ≤ Fintype.card V := card_le_univ _
  have : 2 ^ T ≤ Fintype.card V := by nlinarith
  exact Nat.le_log_of_pow_le (by norm_num) this

end Podc.ContentObliviousEulerian
