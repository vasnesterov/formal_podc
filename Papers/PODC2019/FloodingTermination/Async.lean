import Papers.PODC2019.FloodingTermination.Examples

/-!
# Round-asynchronous amnesiac flooding (Section 4 of Hussak–Trehan)

Model (§1.1.1): computation still proceeds in global rounds, but the adversary decides, for every
message, in which round it is delivered (never lost, never earlier than in the synchronous model).
A node that receives the message in round `r` (from the set `I` of senders delivered in round `r`)
sends it in round `r + 1` to all its neighbours outside `I`.

We describe the adversary by a delay function `δ : ℕ → V → V → ℕ`: the message sent by `u` to `v`
in round `r` is delivered in round `r + δ r u v` (`δ = 0` is the synchronous model, see
`asends_zero_delay`). Since the process is deterministic and at most one message is sent on a
directed edge per round, an *adaptive* adversary's choices in a run are exactly such a function,
so quantifying over all `δ` covers adaptive adversaries.

* `asyncAF_triangle_nonterminating` — the paper's example: on the triangle the adversary can keep
  the message circulating forever (Figure 8).
* `asyncAF_terminates_of_isAcyclic` — on a finite forest (in particular on a single edge) every
  adversary's run terminates, so the adversary cannot *always* force non-termination.
-/

namespace FloodingTermination

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (s : V)

/-- `asends G s δ r u v`: in round `r` of round-asynchronous amnesiac flooding with delays `δ`,
node `u` sends the message to `v`. -/
def asends (δ : ℕ → V → V → ℕ) : ℕ → V → V → Prop
  | 0 => fun _ _ => False
  | 1 => fun u v => u = s ∧ G.Adj u v
  | r + 2 => fun v w => G.Adj v w ∧
      (∃ u, ∃ r' : Fin (r + 2), asends δ r' u v ∧ (r' : ℕ) + δ r' u v = r + 1) ∧
      ¬ ∃ r' : Fin (r + 2), asends δ r' w v ∧ (r' : ℕ) + δ r' w v = r + 1

/-- `areceives G s δ r u v`: in round `r`, `v` receives a message from `u` (sent in some round
`r' ≤ r` and delayed by `r - r'`). -/
def areceives (δ : ℕ → V → V → ℕ) (r : ℕ) (u v : V) : Prop :=
  ∃ r' ≤ r, asends G s δ r' u v ∧ r' + δ r' u v = r

/-- The asynchronous process terminates: from some round on, no messages are sent. -/
def ATerminates (δ : ℕ → V → V → ℕ) : Prop :=
  ∃ R, ∀ r, R < r → ∀ u v, ¬ asends G s δ r u v

variable {G s}

@[simp] lemma asends_zero (δ : ℕ → V → V → ℕ) (u v : V) : ¬ asends G s δ 0 u v := by
  simp [asends]

@[simp] lemma asends_one {δ : ℕ → V → V → ℕ} {u v : V} :
    asends G s δ 1 u v ↔ u = s ∧ G.Adj u v := by
  simp [asends]

lemma asends_add_two {δ : ℕ → V → V → ℕ} {r : ℕ} {v w : V} :
    asends G s δ (r + 2) v w ↔ G.Adj v w ∧ (∃ u, areceives G s δ (r + 1) u v) ∧
      ¬ areceives G s δ (r + 1) w v := by
  rw [asends]
  simp only [areceives]
  constructor
  · rintro ⟨h, ⟨u, r', h1, h2⟩, h3⟩
    exact ⟨h, ⟨u, r', by omega, h1, h2⟩, fun ⟨r'', hr'', h4, h5⟩ =>
      h3 ⟨⟨r'', by omega⟩, h4, h5⟩⟩
  · rintro ⟨h, ⟨u, r', hr', h1, h2⟩, h3⟩
    exact ⟨h, ⟨u, ⟨r', by omega⟩, h1, h2⟩, fun ⟨r'', h4, h5⟩ =>
      h3 ⟨r'', by omega, h4, h5⟩⟩

lemma asends_pos {δ : ℕ → V → V → ℕ} {r : ℕ} {u v : V} (h : asends G s δ r u v) : 0 < r := by
  rcases r with _ | r
  · exact absurd h (asends_zero δ u v)
  · omega

lemma asends_adj {δ : ℕ → V → V → ℕ} {r : ℕ} {u v : V} (h : asends G s δ r u v) : G.Adj u v := by
  match r, h with
  | 0, h => exact absurd h (asends_zero δ u v)
  | 1, h => exact (asends_one.1 h).2
  | r + 2, h => exact (asends_add_two.1 h).1

/-- With zero delays the round-asynchronous process is the synchronous one. -/
theorem asends_zero_delay (r : ℕ) (u v : V) :
    asends G s (fun _ _ _ => 0) r u v ↔ sends G s r u v := by
  induction r using Nat.strong_induction_on generalizing u v with
  | _ r ih =>
    match r, ih with
    | 0, _ => simp
    | 1, _ => simp
    | r + 2, ih =>
      have hrec : ∀ a b, areceives G s (fun _ _ _ => 0) (r + 1) a b ↔ sends G s (r + 1) a b := by
        intro a b
        simp only [areceives, add_zero]
        constructor
        · rintro ⟨r', -, h, he⟩
          subst he
          exact (ih (r + 1) (by omega) a b).1 h
        · intro h; exact ⟨r + 1, le_rfl, (ih (r + 1) (by omega) a b).2 h, rfl⟩
      rw [asends_add_two, sends_add_two]
      simp only [hrec]

/-! ### Non-termination on the triangle (Figure 8) -/

section Triangle

open Examples

/-- The adversary of Figure 8 (source `b = 0`, `a = 1`, `c = 2`): from round 3 on, every message
sent by `c = 2` in an odd round is held for one extra round. -/
def triangleDelay (r : ℕ) (u _v : Fin 3) : ℕ := if u = 2 ∧ r % 2 = 1 ∧ 3 ≤ r then 1 else 0

lemma triangleDelay_le (r : ℕ) (u v : Fin 3) : triangleDelay r u v ≤ 1 := by
  unfold triangleDelay; split <;> omega

/-- With delays `≤ 1`, the messages received in round `r + 1` are those sent in round `r + 1`
without delay and those sent in round `r` with delay one. -/
lemma areceives_succ_of_le_one {G : SimpleGraph V} {s : V} {δ : ℕ → V → V → ℕ}
    (hδ : ∀ r u v, δ r u v ≤ 1) {r : ℕ} {u v : V} :
    areceives G s δ (r + 1) u v ↔
      (asends G s δ (r + 1) u v ∧ δ (r + 1) u v = 0) ∨ (asends G s δ r u v ∧ δ r u v = 1) := by
  unfold areceives
  constructor
  · rintro ⟨r', hr', h, he⟩
    have := hδ r' u v
    rcases Nat.lt_or_ge r' r with hlt | hge
    · omega
    · rcases Nat.eq_or_lt_of_le hge with rfl | hlt
      · exact Or.inr ⟨h, by omega⟩
      · have : r' = r + 1 := by omega
        subst this; exact Or.inl ⟨h, by omega⟩
  · rintro (⟨h, he⟩ | ⟨h, he⟩)
    · exact ⟨r + 1, le_rfl, h, by omega⟩
    · exact ⟨r, by omega, h, by omega⟩

/-- One round with delays `≤ 1`, given the messages of the two previous rounds. -/
lemma asends_step {G : SimpleGraph V} {s : V} {δ : ℕ → V → V → ℕ} (hδ : ∀ r u v, δ r u v ≤ 1)
    {r : ℕ} {A B : V → V → Prop} (hA : ∀ u v, asends G s δ r u v ↔ A u v)
    (hB : ∀ u v, asends G s δ (r + 1) u v ↔ B u v) (v w : V) :
    asends G s δ (r + 2) v w ↔ G.Adj v w ∧
      (∃ u, (B u v ∧ δ (r + 1) u v = 0) ∨ (A u v ∧ δ r u v = 1)) ∧
      ¬ ((B w v ∧ δ (r + 1) w v = 0) ∨ (A w v ∧ δ r w v = 1)) := by
  rw [asends_add_two]
  simp only [areceives_succ_of_le_one hδ, hA, hB]

/-- The messages of the four phases of the periodic run: `{a→b, c→b}`, `{b→c}`, `{b→a, c→a}`,
`{a→c}`. -/
def pat3 (u v : Fin 3) : Prop := (u = 1 ∨ u = 2) ∧ v = 0
def pat0 (u v : Fin 3) : Prop := u = 0 ∧ v = 2
def pat1 (u v : Fin 3) : Prop := (u = 0 ∨ u = 2) ∧ v = 1
def pat2 (u v : Fin 3) : Prop := u = 1 ∧ v = 2

instance : DecidableRel pat3 := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidableRel pat0 := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidableRel pat1 := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidableRel pat2 := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

lemma triangleDelay_odd {r : ℕ} (h1 : r % 2 = 1) (h3 : 3 ≤ r) (u v : Fin 3) :
    triangleDelay r u v = if u = 2 then 1 else 0 := by
  simp [triangleDelay, h1, h3]

lemma triangleDelay_even {r : ℕ} (h0 : r % 2 = 0) (u v : Fin 3) : triangleDelay r u v = 0 := by
  simp [triangleDelay, h0]

/-- Rounds `4k + 3` and `4k + 4` of the adversarial run follow the periodic pattern (and hence so
do rounds `4k + 5`, `4k + 6`, see the proof). -/
lemma triangle_pattern (k : ℕ) :
    (∀ u v, asends triangle 0 triangleDelay (4 * k + 3) u v ↔ pat3 u v) ∧
    (∀ u v, asends triangle 0 triangleDelay (4 * k + 4) u v ↔ pat0 u v) := by
  induction k with
  | zero =>
    have h0 : ∀ u v, asends triangle 0 triangleDelay 0 u v ↔ False :=
      fun u v => iff_false_intro (asends_zero _ u v)
    have h1 : ∀ u v, asends triangle 0 triangleDelay 1 u v ↔ (u = 0 ∧ triangle.Adj u v) :=
      fun u v => asends_one
    have h2 : ∀ u v, asends triangle 0 triangleDelay 2 u v ↔ (u = 1 ∧ v = 2 ∨ u = 2 ∧ v = 1) := by
      intro v w; rw [asends_step triangleDelay_le h0 h1]; revert v w; decide
    have h3 : ∀ u v, asends triangle 0 triangleDelay 3 u v ↔ pat3 u v := by
      intro v w; rw [asends_step triangleDelay_le h1 h2]; revert v w; decide
    have h4 : ∀ u v, asends triangle 0 triangleDelay 4 u v ↔ pat0 u v := by
      intro v w; rw [asends_step triangleDelay_le h2 h3]; revert v w; decide
    exact ⟨h3, h4⟩
  | succ k ih =>
    obtain ⟨h3, h4⟩ := ih
    have h5 : ∀ u v, asends triangle 0 triangleDelay (4 * k + 5) u v ↔ pat1 u v := by
      intro v w
      rw [asends_step triangleDelay_le h3 h4]
      simp only [triangleDelay_odd (r := 4 * k + 3) (by omega) (by omega),
        triangleDelay_even (r := 4 * k + 3 + 1) (by omega)]
      revert v w; decide
    have h6 : ∀ u v, asends triangle 0 triangleDelay (4 * k + 6) u v ↔ pat2 u v := by
      intro v w
      rw [asends_step triangleDelay_le h4 h5]
      simp only [triangleDelay_even (r := 4 * k + 4) (by omega),
        triangleDelay_odd (r := 4 * k + 4 + 1) (by omega) (by omega)]
      revert v w; decide
    have h7 : ∀ u v, asends triangle 0 triangleDelay (4 * k + 7) u v ↔ pat3 u v := by
      intro v w
      rw [asends_step triangleDelay_le h5 h6]
      simp only [triangleDelay_odd (r := 4 * k + 5) (by omega) (by omega),
        triangleDelay_even (r := 4 * k + 5 + 1) (by omega)]
      revert v w; decide
    have h8 : ∀ u v, asends triangle 0 triangleDelay (4 * k + 8) u v ↔ pat0 u v := by
      intro v w
      rw [asends_step triangleDelay_le h6 h7]
      simp only [triangleDelay_even (r := 4 * k + 6) (by omega),
        triangleDelay_odd (r := 4 * k + 6 + 1) (by omega) (by omega)]
      revert v w; decide
    exact ⟨fun u v => by rw [show 4 * (k + 1) + 3 = 4 * k + 7 by ring]; exact h7 u v,
      fun u v => by rw [show 4 * (k + 1) + 4 = 4 * k + 8 by ring]; exact h8 u v⟩

/-- **Section 4** of [Hussak–Trehan, PODC'19] (Figure 8). In the round-asynchronous model, the
adversary can make amnesiac flooding on the triangle non-terminating: with the delays
`triangleDelay`, some message is sent in every round. -/
theorem asyncAF_triangle_nonterminating :
    (∀ r, ∃ u v, asends triangle 0 triangleDelay (r + 1) u v) ∧
    ¬ ATerminates triangle 0 triangleDelay := by
  have hall : ∀ r, ∃ u v, asends triangle 0 triangleDelay (r + 1) u v := by
    intro r
    rcases (by omega : r = 0 ∨ r = 1 ∨ 2 ≤ r) with rfl | rfl | hr
    · exact ⟨0, 1, by rw [asends_one]; decide⟩
    · refine ⟨1, 2, ?_⟩
      have h0 : ∀ u v, asends triangle 0 triangleDelay 0 u v ↔ False :=
        fun u v => iff_false_intro (asends_zero _ u v)
      have h1 : ∀ u v, asends triangle 0 triangleDelay 1 u v ↔ (u = 0 ∧ triangle.Adj u v) :=
        fun u v => asends_one
      rw [asends_step triangleDelay_le h0 h1]; decide
    · -- `r + 1 = 4k + 3 + i` with `i < 4`; rounds `4k+3`, `4k+4` are given, `4k+5`, `4k+6` follow
      obtain ⟨g3, g4⟩ := triangle_pattern ((r - 2) / 4)
      set k := (r - 2) / 4 with hk
      have hi : r + 1 = 4 * k + 3 ∨ r + 1 = 4 * k + 4 ∨ r + 1 = 4 * k + 5 ∨ r + 1 = 4 * k + 6 := by
        omega
      have g5 : ∀ u v, asends triangle 0 triangleDelay (4 * k + 5) u v ↔ pat1 u v := by
        intro v w
        rw [asends_step triangleDelay_le g3 g4]
        simp only [triangleDelay_odd (r := 4 * k + 3) (by omega) (by omega),
          triangleDelay_even (r := 4 * k + 3 + 1) (by omega)]
        revert v w; decide
      have g6 : ∀ u v, asends triangle 0 triangleDelay (4 * k + 6) u v ↔ pat2 u v := by
        intro v w
        rw [asends_step triangleDelay_le g4 g5]
        simp only [triangleDelay_even (r := 4 * k + 4) (by omega),
          triangleDelay_odd (r := 4 * k + 4 + 1) (by omega) (by omega)]
        revert v w; decide
      rcases hi with hi | hi | hi | hi <;> rw [hi]
      · exact ⟨1, 0, (g3 1 0).2 (by decide)⟩
      · exact ⟨0, 2, (g4 0 2).2 (by decide)⟩
      · exact ⟨0, 1, (g5 0 1).2 (by decide)⟩
      · exact ⟨1, 2, (g6 1 2).2 (by decide)⟩
  refine ⟨hall, fun ⟨R, hR⟩ => ?_⟩
  obtain ⟨u, v, h⟩ := hall R
  exact hR (R + 1) (by omega) u v h

end Triangle

/-! ### Termination on forests: the adversary cannot always prevent termination -/

section Forest

variable {G : SimpleGraph V} {s : V} {δ : ℕ → V → V → ℕ}

/-- On a forest every message moves one step away from the source. -/
lemma asends_dist (hG : G.IsAcyclic) (r : ℕ) :
    ∀ u v, asends G s δ r u v → G.Reachable s u ∧ G.dist s v = G.dist s u + 1 := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro u v h
    match r, ih, h with
    | 0, _, h => exact absurd h (asends_zero δ u v)
    | 1, _, h =>
      obtain ⟨rfl, hadj⟩ := asends_one.1 h
      exact ⟨Reachable.refl _, by rw [dist_eq_one_iff_adj.2 hadj, dist_self]⟩
    | r + 2, ih, h =>
      obtain ⟨hadj, ⟨x, r', hr', hx, he⟩, hnot⟩ := asends_add_two.1 h
      obtain ⟨hrx, hdx⟩ := ih r' (by omega) x u hx
      have hru : G.Reachable s u := hrx.trans (asends_adj hx).reachable
      have hrv : G.Reachable s v := hru.trans hadj.reachable
      refine ⟨hru, ?_⟩
      have hvx : v ≠ x := by
        rintro rfl
        exact hnot ⟨r', hr', hx, he⟩
      have h1 := hru.dist_le_dist_add_one_of_adj hadj
      have h2 := hrv.dist_le_dist_add_one_of_adj hadj.symm
      have hpar : G.dist s u % 2 ≠ G.dist s v % 2 := by
        intro hp
        have := mod_two_eq_of_colorable hG.colorable_two hru.mem_walkSet_dist
          (mem_walkSet_succ_of_adj hrv.mem_walkSet_dist hadj.symm)
        omega
      by_contra hne
      have hpar' : G.dist s v + 1 = G.dist s u := by omega
      exact hvx (hG.eq_of_dist_add_one hadj.symm (asends_adj hx) hrv hrx hpar' hdx.symm)

lemma areceives_dist (hG : G.IsAcyclic) {t : ℕ} {x u : V} (h : areceives G s δ t x u) :
    G.Reachable s x ∧ G.dist s u = G.dist s x + 1 := by
  obtain ⟨r, -, hr, -⟩ := h
  exact asends_dist hG r x u hr

lemma not_areceives_source (hG : G.IsAcyclic) {t : ℕ} {x : V} : ¬ areceives G s δ t x s := by
  intro h
  have := (areceives_dist hG h).2
  simp at this

/-- If `x` receives messages in at most one round, then it sends messages in at most one round. -/
lemma asends_round_eq (hG : G.IsAcyclic) {x : V}
    (hx : ∀ t t' a b, areceives G s δ t a x → areceives G s δ t' b x → t = t')
    {r r' : ℕ} {u u' : V} (h : asends G s δ r x u) (h' : asends G s δ r' x u') : r = r' := by
  match r, r', h, h' with
  | 0, _, h, _ => exact absurd h (asends_zero δ x u)
  | _, 0, _, h' => exact absurd h' (asends_zero δ x u')
  | 1, 1, _, _ => rfl
  | 1, r' + 2, h, h' =>
    obtain ⟨rfl, -⟩ := asends_one.1 h
    obtain ⟨-, ⟨a, ha⟩, -⟩ := asends_add_two.1 h'
    exact absurd ha (not_areceives_source hG)
  | r + 2, 1, h, h' =>
    obtain ⟨rfl, -⟩ := asends_one.1 h'
    obtain ⟨-, ⟨a, ha⟩, -⟩ := asends_add_two.1 h
    exact absurd ha (not_areceives_source hG)
  | r + 2, r' + 2, h, h' =>
    obtain ⟨-, ⟨a, ha⟩, -⟩ := asends_add_two.1 h
    obtain ⟨-, ⟨b, hb⟩, -⟩ := asends_add_two.1 h'
    have := hx _ _ a b ha hb
    omega

/-- On a forest every node receives messages in at most one round. -/
lemma areceives_round_eq (hG : G.IsAcyclic) (n : ℕ) :
    ∀ u, G.dist s u = n → ∀ t t' a b, areceives G s δ t a u → areceives G s δ t' b u → t = t' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u hu t t' a b ha hb
    obtain ⟨hra, hda⟩ := areceives_dist hG ha
    obtain ⟨hrb, hdb⟩ := areceives_dist hG hb
    obtain ⟨r, -, hr, rfl⟩ := ha
    obtain ⟨r', -, hr', rfl⟩ := hb
    have hab : a = b := hG.eq_of_dist_add_one (asends_adj hr) (asends_adj hr') hra hrb
      hda.symm hdb.symm
    subst hab
    have := asends_round_eq hG (ih (G.dist s a) (by omega) a rfl) hr hr'
    subst this
    rfl

/-- On a forest, messages are sent over each directed edge in at most one round. -/
lemma asends_round_unique (hG : G.IsAcyclic) {r r' : ℕ} {u v : V} (h : asends G s δ r u v)
    (h' : asends G s δ r' u v) : r = r' :=
  asends_round_eq hG (areceives_round_eq hG _ u rfl) h h'

/-- **The adversary cannot always prevent termination.** On every finite forest (e.g. a single
edge), round-asynchronous amnesiac flooding terminates for every choice of delays. -/
theorem asyncAF_terminates_of_isAcyclic [Finite V] (hG : G.IsAcyclic) (s : V)
    (δ : ℕ → V → V → ℕ) : ATerminates G s δ := by
  classical
  have := Fintype.ofFinite V
  let f : V × V → ℕ := fun p => if h : ∃ r, asends G s δ r p.1 p.2 then Nat.find h else 0
  refine ⟨Finset.univ.sup f, fun r hr u v h => ?_⟩
  have hex : ∃ r, asends G s δ r u v := ⟨r, h⟩
  have hf : f (u, v) = Nat.find hex := by simp only [f, hex, dite_true]
  have hle : f (u, v) ≤ Finset.univ.sup f := Finset.le_sup (Finset.mem_univ _)
  have := asends_round_unique hG h (Nat.find_spec hex)
  omega

/-- The simplest instance: on a single edge (the complete graph on two nodes) every adversary's run
terminates. -/
theorem asyncAF_terminates_single_edge (s : Fin 2) (δ : ℕ → Fin 2 → Fin 2 → ℕ) :
    ATerminates (⊤ : SimpleGraph (Fin 2)) s δ := by
  refine asyncAF_terminates_of_isAcyclic ?_ s δ
  have h := (isTree_iff_connected_and_card (G := (⊤ : SimpleGraph (Fin 2)))).2
  refine (h ⟨connected_top, ?_⟩).isAcyclic
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, card_edgeFinset_top_eq_card_choose_two]
  simp

end Forest

end FloodingTermination
