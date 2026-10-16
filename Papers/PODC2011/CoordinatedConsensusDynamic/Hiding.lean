import Papers.PODC2011.CoordinatedConsensusDynamic.Model

/-!
# The hiding lemma (proof of Theorem 5.1)

Fix a node set `V` with `n = |V|` and the a-priori information `N`; we work in the system
`SV V N` of all valid executions on exactly the node set `V`. Two statements are proved by a joint
induction on `k`:

* `HideP k` ("hiding", the paper's induction claim): for every `t ≥ k`, every set `X ⊆ V` with
  `|X| + k + 1 ≤ n` and every `u ∉ X`, we can move inside the similarity component of `(G, t)`
  to an execution `G'` that agrees with `G` on the inputs and on all rounds `r ≤ t - k`, and in
  which no node of `X` at time `t - k` causally influences `(u, t)`.
* `FreeP k` ("freedom"): if `k + 2 ≤ n`, any two executions with the same inputs that agree on
  rounds `1, …, t - k` are in the same similarity component at time `t`.

`FreeP (k+1)` follows from `FreeP k` and `HideP k` by changing round `t - k` one edge at a time:
to add or remove the edge `{a, b}` we first hide `{a, b}` at time `t - k` from some third node
(this is where the paper's "remove edges by first hiding both endpoints" is made precise; it needs
`k + 3 ≤ n`). `HideP (k+1)` follows from `FreeP (k+1)` and `HideP k` exactly as in the paper's
sketch, except that we replace round `t - k` by a star centred at a fresh node `w` (any connected
graph in which `X` only talks to `X ∪ {w}` works).
-/

namespace CoordCons

open Relation

variable {α : Type*}

namespace DGraph

/-! ### Operations on executions -/

/-- Replace the communication graph of round `r` by `E`. -/
def setRound (G : DGraph α) (r : ℕ) (E : ℕ → ℕ → Prop) : DGraph α :=
  { G with adj := fun r' => if r' = r then E else G.adj r' }

@[simp] theorem setRound_V (G : DGraph α) (r : ℕ) (E : ℕ → ℕ → Prop) :
    (G.setRound r E).V = G.V := rfl
@[simp] theorem setRound_N (G : DGraph α) (r : ℕ) (E : ℕ → ℕ → Prop) :
    (G.setRound r E).N = G.N := rfl
@[simp] theorem setRound_input (G : DGraph α) (r : ℕ) (E : ℕ → ℕ → Prop) :
    (G.setRound r E).input = G.input := rfl
@[simp] theorem setRound_adj_self (G : DGraph α) (r : ℕ) (E : ℕ → ℕ → Prop) :
    (G.setRound r E).adj r = E := by simp [setRound]
theorem setRound_adj_ne (G : DGraph α) {r r' : ℕ} (h : r' ≠ r) (E : ℕ → ℕ → Prop) :
    (G.setRound r E).adj r' = G.adj r' := by simp [setRound, h]

theorem setRound_setRound (G : DGraph α) (r : ℕ) (E E' : ℕ → ℕ → Prop) :
    (G.setRound r E).setRound r E' = G.setRound r E' := by
  simp only [setRound]
  congr 1
  funext r'
  split_ifs <;> rfl

theorem setRound_self (G : DGraph α) (r : ℕ) : G.setRound r (G.adj r) = G := by
  cases G
  simp only [setRound, mk.injEq, true_and]
  funext r'
  split_ifs with h <;> simp [h]

/-- Change the input of one node. -/
def setInput (G : DGraph α) (a : ℕ) (c : α) : DGraph α :=
  { G with input := Function.update G.input a c }

/-- Rename the nodes along a permutation of `ℕ`. -/
def rename (G : DGraph α) (e : ℕ ≃ ℕ) : DGraph α where
  V := G.V.map e.toEmbedding
  input := G.input ∘ e.symm
  N := G.N
  adj r x y := G.adj r (e.symm x) (e.symm y)

theorem mem_rename_V {G : DGraph α} {e : ℕ ≃ ℕ} {x : ℕ} : x ∈ (G.rename e).V ↔ e.symm x ∈ G.V := by
  simp only [rename, Finset.mem_map_equiv]

/-- Attach a new node `x` as a leaf of `w` in every round `≥ 1`. -/
def addLeaf (G : DGraph α) (x w : ℕ) : DGraph α where
  V := insert x G.V
  input := G.input
  N := G.N
  adj r y z := G.adj r y z ∨ (1 ≤ r ∧ ((y = x ∧ z = w) ∨ (y = w ∧ z = x)))

/-! ### Valid rounds -/

/-- A legal communication graph on `V`: undirected, loopless, connected. -/
structure RoundOK (V : Finset ℕ) (E : ℕ → ℕ → Prop) : Prop where
  mem : ∀ x y, E x y → x ∈ V ∧ y ∈ V
  symm : ∀ x y, E x y → E y x
  irrefl : ∀ x, ¬ E x x
  conn : ∀ x ∈ V, ∀ y ∈ V, ReflTransGen E x y

theorem Valid.roundOK {G : DGraph α} (hG : G.Valid) {r : ℕ} (hr : 1 ≤ r) :
    RoundOK G.V (G.adj r) :=
  ⟨hG.mem r, hG.symm r, hG.irrefl r, hG.conn r hr⟩

theorem Valid.setRound {G : DGraph α} (hG : G.Valid) {E : ℕ → ℕ → Prop} (hE : RoundOK G.V E)
    (r : ℕ) : (G.setRound r E).Valid := by
  refine ⟨hG.nonempty, fun r' => ?_, fun r' => ?_, fun r' => ?_, fun r' hr' => ?_⟩ <;>
  · by_cases h : r' = r
    · subst h; simp only [setRound_adj_self, setRound_V]
      first | exact hE.mem | exact hE.symm | exact hE.irrefl | exact hE.conn
    · simp only [setRound_adj_ne G h, setRound_V]
      first | exact hG.mem r' | exact hG.symm r' | exact hG.irrefl r' | exact hG.conn r' hr'

theorem Valid.setInput {G : DGraph α} (hG : G.Valid) (a : ℕ) (c : α) : (G.setInput a c).Valid :=
  ⟨hG.nonempty, hG.mem, hG.symm, hG.irrefl, hG.conn⟩

theorem Valid.rename {G : DGraph α} (hG : G.Valid) (e : ℕ ≃ ℕ) : (G.rename e).Valid := by
  refine ⟨hG.nonempty.map, fun r x y h => ?_, fun r x y h => hG.symm r _ _ h,
    fun r x h => hG.irrefl r _ h, fun r hr x hx y hy => ?_⟩
  · exact ⟨mem_rename_V.2 (hG.mem r _ _ h).1, mem_rename_V.2 (hG.mem r _ _ h).2⟩
  · have := hG.conn r hr _ (mem_rename_V.1 hx) _ (mem_rename_V.1 hy)
    have key : ∀ a b, ReflTransGen (G.adj r) a b →
        ReflTransGen ((G.rename e).adj r) (e a) (e b) := by
      intro a b h
      induction h with
      | refl => exact .refl
      | tail _ h ih => exact ih.tail (show G.adj r (e.symm (e _)) (e.symm (e _)) by simpa using h)
    simpa using key _ _ this

theorem Valid.addLeaf {G : DGraph α} (hG : G.Valid) {x w : ℕ} (hx : x ∉ G.V) (hw : w ∈ G.V) :
    (G.addLeaf x w).Valid := by
  refine ⟨⟨x, Finset.mem_insert_self _ _⟩, fun r y z h => ?_, fun r y z h => ?_,
    fun r y h => ?_, fun r hr y hy z hz => ?_⟩
  · simp only [DGraph.addLeaf, Finset.mem_insert] at h ⊢
    rcases h with h | ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨Or.inr (hG.mem _ _ _ h).1, Or.inr (hG.mem _ _ _ h).2⟩
    · exact ⟨Or.inl rfl, Or.inr hw⟩
    · exact ⟨Or.inr hw, Or.inl rfl⟩
  · simp only [DGraph.addLeaf] at h ⊢
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (hG.symm _ _ _ h)
    · exact Or.inr ⟨h1, by tauto⟩
  · simp only [DGraph.addLeaf] at h
    rcases h with h | ⟨-, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
    · exact hG.irrefl _ _ h
    · exact hx (h ▸ hw)
    · exact hx (h ▸ hw)
  · -- every node is connected to `w`
    have key : ∀ y ∈ (G.addLeaf x w).V, ReflTransGen ((G.addLeaf x w).adj r) y w := by
      intro y hy
      simp only [DGraph.addLeaf, Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact ReflTransGen.single (Or.inr ⟨hr, Or.inl ⟨rfl, rfl⟩⟩)
      · exact ReflTransGen.mono (fun a b h => Or.inl h) _ _ (hG.conn r hr y hy w hw)
    have hsymm : ∀ a b, (G.addLeaf x w).adj r a b → (G.addLeaf x w).adj r b a := by
      intro a b h
      simp only [DGraph.addLeaf] at h ⊢
      rcases h with h | ⟨h1, h2⟩
      · exact Or.inl (hG.symm _ _ _ h)
      · exact Or.inr ⟨h1, by tauto⟩
    exact (key y hy).trans ((key z hz).symm_of hsymm)

/-! ### Indistinguishability of the elementary moves -/

/-- Changing round `r` is invisible to `(u, t)` if no time-node `(w, r)` whose incoming edges
change lies in the causal past of `(u, t)`. -/
theorem indist_setRound {G : DGraph α} (hG : G.Valid) {u t r : ℕ} (hu : u ∈ G.V)
    {E : ℕ → ℕ → Prop} (hE : ∀ w, G.Reach w r u t → ∀ x, G.adj r x w ↔ E x w) :
    Indist G (G.setRound r E) u t := by
  refine indist_of_agree hG hu rfl (fun w hw => ⟨(hw.mem_iff hG).2 hu, rfl⟩) ?_
  intro w s hw x
  by_cases h : s + 1 = r
  · subst h; simp only [setRound_adj_self]; exact hE w hw x
  · simp [setRound_adj_ne G h]

theorem indist_setInput {G : DGraph α} (hG : G.Valid) {u t a : ℕ} (hu : u ∈ G.V) (c : α)
    (ha : ¬ G.Reach a 0 u t) : Indist G (G.setInput a c) u t := by
  refine indist_of_agree hG hu rfl (fun w hw => ⟨(hw.mem_iff hG).2 hu, ?_⟩)
    (fun _ _ _ _ => Iff.rfl)
  have : w ≠ a := fun h => ha (h ▸ hw)
  simp [setInput, Function.update_of_ne this]

/-- Renaming a node `a` that is completely hidden from `(u, t)` into a fresh name `b`. -/
theorem indist_rename_swap {G : DGraph α} (hG : G.Valid) {u t a b : ℕ} (hu : u ∈ G.V)
    (ha : ¬ G.Reach a 0 u t) (hb : b ∉ G.V) : Indist G (G.rename (Equiv.swap a b)) u t := by
  have hw : ∀ w s, G.Reach w s u t → w ≠ a ∧ w ≠ b := by
    intro w s hw
    refine ⟨fun h => ha (h ▸ hw.of_le (Nat.zero_le s)), fun h => hb (h ▸ (hw.mem_iff hG).2 hu)⟩
  have hsw : ∀ w s, G.Reach w s u t → Equiv.swap a b w = w := fun w s h =>
    Equiv.swap_apply_of_ne_of_ne (hw w s h).1 (hw w s h).2
  refine indist_of_agree hG hu rfl (fun w hr => ⟨?_, ?_⟩) ?_
  · rw [mem_rename_V, Equiv.symm_swap, hsw w 0 hr]; exact (hr.mem_iff hG).2 hu
  · simp [rename, hsw w 0 hr]
  · intro w s hr x
    simp only [rename, Equiv.symm_swap, hsw w _ hr]
    -- an edge from `a` or `b` into the causal past is impossible
    have hxa : ¬ G.adj (s + 1) a w := fun h => ha ((Reach.cons (Or.inr h) hr).of_le (by omega))
    have hxb : ¬ G.adj (s + 1) b w := fun h => hb (hG.mem _ _ _ h).1
    by_cases h1 : x = a
    · subst h1; simp [hxa, hxb]
    · by_cases h2 : x = b
      · subst h2; simp [hxa, hxb]
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem indist_addLeaf {G : DGraph α} (hG : G.Valid) {u t x w : ℕ} (hu : u ∈ G.V)
    (hx : x ∉ G.V) (hw : ¬ G.Reach w 1 u t) : Indist G (G.addLeaf x w) u t := by
  refine indist_of_agree hG hu rfl
    (fun y hy => ⟨Finset.mem_insert_of_mem ((hy.mem_iff hG).2 hu), rfl⟩) ?_
  intro y s hy z
  have hyw : y ≠ w := fun h => hw (h ▸ hy.of_le (by omega))
  have hyx : y ≠ x := fun h => hx (h ▸ (hy.mem_iff hG).2 hu)
  simp [addLeaf, hyw, hyx]

end DGraph

open DGraph

/-! ### The induction -/

/-- All valid executions on the node set `V` with a-priori information `N`. -/
def SV (V : Finset ℕ) (N : ℕ) (G : DGraph α) : Prop := G.Valid ∧ G.V = V ∧ G.N = N

theorem SV.setRound {V : Finset ℕ} {N : ℕ} {G : DGraph α} (h : SV V N G) {E : ℕ → ℕ → Prop}
    (hE : RoundOK V E) (r : ℕ) : SV V N (G.setRound r E) :=
  ⟨h.1.setRound (h.2.1 ▸ hE) r, h.2.1, h.2.2⟩

/-- `FreeP k`: rounds after time `t - k` can be changed freely within the similarity component. -/
def FreeP (α : Type*) (V : Finset ℕ) (N k : ℕ) : Prop :=
  ∀ t (G H : DGraph α), SV V N G → SV V N H → (∀ w ∈ V, G.input w = H.input w) →
    (∀ r, 1 ≤ r → r + k ≤ t → G.adj r = H.adj r) → Sim (SV V N) t G H

/-- `HideP k`: the paper's hiding claim. -/
def HideP (α : Type*) (V : Finset ℕ) (N k : ℕ) : Prop :=
  ∀ t, k ≤ t → ∀ G : DGraph α, SV V N G → ∀ X : Finset ℕ, X ⊆ V → X.card + k + 1 ≤ V.card →
    ∀ u ∈ V, u ∉ X → ∃ G', SV V N G' ∧ G'.input = G.input ∧
      (∀ r, r + k ≤ t → G'.adj r = G.adj r) ∧ Sim (SV V N) t G G' ∧
      ∀ x ∈ X, ¬ G'.Reach x (t - k) u t

variable {V : Finset ℕ} {N : ℕ}

theorem freeP_zero : FreeP α V N 0 := by
  intro t G H hG hH hin hadj
  obtain ⟨u, hu⟩ := hG.1.nonempty
  refine Sim.single hG hH (u := u) (indist_of_agree hG.1 hu (hG.2.2.trans hH.2.2.symm)
    (fun w hw => ?_) (fun w s hw x => ?_))
  · have hwV := (hw.mem_iff hG.1).2 hu
    exact ⟨hH.2.1 ▸ hG.2.1 ▸ hwV, hin w (hG.2.1 ▸ hwV)⟩
  · rw [hadj (s + 1) (by omega) (by have := hw.le; omega)]

theorem hideP_zero : HideP α V N 0 := by
  intro t _ G hG X _ _ u _ huX
  refine ⟨G, hG, rfl, fun _ _ => rfl, ReflTransGen.refl, fun x hx h => ?_⟩
  rw [Nat.sub_zero] at h
  exact huX (h.same_time ▸ hx)

section Step

variable {k : ℕ} (hF : FreeP α V N k) (hH : HideP α V N k) (h3 : k + 3 ≤ V.card)
include hF hH h3

/-- Adding or removing a single edge `{a, b}` in round `t - k`. -/
theorem sim_single_edge {t : ℕ} (hkt : k < t) {G : DGraph α} (hG : SV V N G)
    {E : ℕ → ℕ → Prop} (hE : RoundOK V E) {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V)
    (hdiff : ∀ x y, ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) → (G.adj (t - k) x y ↔ E x y)) :
    Sim (SV V N) t G (G.setRound (t - k) E) := by
  classical
  -- a third node
  obtain ⟨u, hu, huab⟩ : ∃ u ∈ V, u ∉ ({a, b} : Finset ℕ) := by
    by_contra hcon
    push Not at hcon
    have := Finset.card_le_card hcon
    have := Finset.card_le_two (a := a) (b := b)
    omega
  have hX : ({a, b} : Finset ℕ) ⊆ V := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hXc : ({a, b} : Finset ℕ).card + k + 1 ≤ V.card := by
    have := Finset.card_le_two (a := a) (b := b); omega
  obtain ⟨G', hG', hin, hagree, hsim, hhid⟩ := hH t hkt.le G hG {a, b} hX hXc u hu huab
  have hr0 : t - k + k ≤ t := by omega
  have hG'r : G'.adj (t - k) = G.adj (t - k) := hagree _ hr0
  -- change the round in `G'`, invisible to `u`
  have hstep : Indist G' (G'.setRound (t - k) E) u t := by
    refine indist_setRound hG'.1 (hG'.2.1 ▸ hu) (fun w hw x => ?_)
    have hwa : w ≠ a := fun h => hhid a (by simp) (h ▸ hw)
    have hwb : w ≠ b := fun h => hhid b (by simp) (h ▸ hw)
    rw [hG'r]
    exact hdiff x w (by tauto)
  have h1 : Sim (SV V N) t G' (G'.setRound (t - k) E) :=
    Sim.single hG' (hG'.setRound hE _) hstep
  -- and go back with `FreeP k`
  have h2 : Sim (SV V N) t (G'.setRound (t - k) E) (G.setRound (t - k) E) := by
    refine hF t _ _ (hG'.setRound hE _) (hG.setRound hE _) (fun w _ => by simp [hin])
      (fun r hr hrt => ?_)
    by_cases h : r = t - k
    · subst h; simp
    · rw [setRound_adj_ne _ h, setRound_adj_ne _ h, hagree r hrt]
  exact hsim.trans (h1.trans h2)

open Classical in
/-- Adding edges to round `t - k` one at a time. -/
theorem sim_add_edges {t : ℕ} (hkt : k < t) :
    ∀ (m : ℕ) {G : DGraph α} (hG : SV V N G) {E : ℕ → ℕ → Prop} (hE : RoundOK V E),
      (∀ x y, G.adj (t - k) x y → E x y) →
      ((V ×ˢ V).filter (fun p : ℕ × ℕ => E p.1 p.2 ∧ ¬ G.adj (t - k) p.1 p.2)).card ≤ m →
      Sim (SV V N) t G (G.setRound (t - k) E) := by
  classical
  intro m
  induction m with
  | zero =>
    intro G hG E hE hsub hcard
    have : E = G.adj (t - k) := by
      funext x y
      apply propext
      refine ⟨fun h => ?_, hsub x y⟩
      by_contra hn
      have hmem : (x, y) ∈ (V ×ˢ V).filter (fun p : ℕ × ℕ => E p.1 p.2 ∧ ¬ G.adj (t - k) p.1 p.2) := by
        simp only [Finset.mem_filter, Finset.mem_product]
        exact ⟨hE.mem x y h, h, hn⟩
      have := Finset.card_pos.2 ⟨_, hmem⟩
      omega
    rw [this, setRound_self]
    exact ReflTransGen.refl
  | succ m ih =>
    intro G hG E hE hsub hcard
    by_cases hall : ∀ x y, E x y → G.adj (t - k) x y
    · have : E = G.adj (t - k) := by
        funext x y; exact propext ⟨hall x y, hsub x y⟩
      rw [this, setRound_self]
      exact ReflTransGen.refl
    push Not at hall
    obtain ⟨a, b, hab, hnab⟩ := hall
    have hk1 : 1 ≤ t - k := by omega
    have hGr := hG.1.roundOK hk1
    rw [hG.2.1] at hGr
    let E1 : ℕ → ℕ → Prop := fun x y => G.adj (t - k) x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)
    have hE1 : RoundOK V E1 := by
      refine ⟨fun x y h => ?_, fun x y h => ?_, fun x h => ?_, fun x hx y hy => ?_⟩
      · rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hGr.mem x y h
        · exact hE.mem _ _ hab
        · exact (hE.mem _ _ hab).symm
      · rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (hGr.symm x y h)
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hGr.irrefl x h
        · subst h1; subst h2; exact hE.irrefl _ hab
        · subst h1; subst h2; exact hE.irrefl _ hab
      · exact ReflTransGen.mono (fun p q h => Or.inl h) _ _ (hGr.conn x hx y hy)
    have hstep1 : Sim (SV V N) t G (G.setRound (t - k) E1) := by
      refine sim_single_edge hF hH h3 hkt hG hE1 (hE.mem _ _ hab).1 (hE.mem _ _ hab).2
        (fun x y hxy => ?_)
      simp only [E1]; tauto
    have hstep2 : Sim (SV V N) t (G.setRound (t - k) E1)
        ((G.setRound (t - k) E1).setRound (t - k) E) := by
      refine ih (hG.setRound hE1 _) hE (fun x y h => ?_) ?_
      · simp only [setRound_adj_self] at h
        rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hsub x y h
        · exact hab
        · exact hE.symm _ _ hab
      · simp only [setRound_adj_self]
        refine Nat.le_of_lt_succ (lt_of_lt_of_le (Finset.card_lt_card ?_) hcard)
        refine Finset.ssubset_iff_of_subset (fun p hp => ?_) |>.2 ⟨(a, b), ?_, ?_⟩
        · simp only [Finset.mem_filter, E1] at hp ⊢; tauto
        · simp only [Finset.mem_filter, Finset.mem_product]
          exact ⟨hE.mem _ _ hab, hab, hnab⟩
        · simp [E1]
    rw [setRound_setRound] at hstep2
    exact hstep1.trans hstep2

/-- Round `t - k` can be replaced by any legal graph. -/
theorem sim_setRound {t : ℕ} (hkt : k < t) {G : DGraph α} (hG : SV V N G)
    {E : ℕ → ℕ → Prop} (hE : RoundOK V E) : Sim (SV V N) t G (G.setRound (t - k) E) := by
  classical
  have hk1 : 1 ≤ t - k := by omega
  have hGr := hG.1.roundOK hk1
  rw [hG.2.1] at hGr
  let U : ℕ → ℕ → Prop := fun x y => G.adj (t - k) x y ∨ E x y
  have hU : RoundOK V U := by
    refine ⟨fun x y h => ?_, fun x y h => ?_, fun x h => ?_, fun x hx y hy => ?_⟩
    · rcases h with h | h
      · exact hGr.mem x y h
      · exact hE.mem x y h
    · rcases h with h | h
      · exact Or.inl (hGr.symm x y h)
      · exact Or.inr (hE.symm x y h)
    · rcases h with h | h
      · exact hGr.irrefl x h
      · exact hE.irrefl x h
    · exact ReflTransGen.mono (fun p q h => Or.inl h) _ _ (hGr.conn x hx y hy)
  have h1 := sim_add_edges hF hH h3 hkt _ hG hU (fun x y h => Or.inl h) le_rfl
  have h2 := sim_add_edges hF hH h3 hkt _ (hG.setRound hE (t - k)) hU
    (fun x y h => by simp only [setRound_adj_self] at h; exact Or.inr h) le_rfl
  rw [setRound_setRound] at h2
  exact h1.trans h2.symm

theorem freeP_succ : FreeP α V N (k + 1) := by
  intro t G H hG hH' hin hadj
  by_cases hkt : t ≤ k
  · exact hF t G H hG hH' hin (fun r hr hrt => hadj r hr (by omega))
  push Not at hkt
  -- first make round `t - k` agree, then use `FreeP k`
  have hk1 : 1 ≤ t - k := by omega
  have hGr := hG.1.roundOK hk1
  rw [hG.2.1] at hGr
  have h1 : Sim (SV V N) t H (H.setRound (t - k) (G.adj (t - k))) :=
    sim_setRound hF hH h3 hkt hH' hGr
  have h2 : Sim (SV V N) t G (H.setRound (t - k) (G.adj (t - k))) := by
    refine hF t _ _ hG (hH'.setRound hGr _) (fun w hw => by simp [hin w hw])
      (fun r hr hrt => ?_)
    by_cases h : r = t - k
    · subst h; simp
    · rw [setRound_adj_ne _ h]; exact hadj r hr (by omega)
  exact h2.trans h1.symm

end Step

theorem hideP_succ {k : ℕ} (hF : k + 3 ≤ V.card → FreeP α V N (k + 1)) (hH : HideP α V N k) :
    HideP α V N (k + 1) := by
  classical
  intro t hkt G hG X hXV hXc u hu huX
  rcases X.eq_empty_or_nonempty with rfl | hXne
  · exact ⟨G, hG, rfl, fun _ _ => rfl, ReflTransGen.refl, by simp⟩
  have hX1 := hXne.card_pos
  have hF := hF (by omega)
  -- a fresh centre `w ∉ X ∪ {u}`
  obtain ⟨w, hw, hwX⟩ : ∃ w ∈ V, w ∉ insert u X := by
    by_contra hcon
    push Not at hcon
    have := Finset.card_le_card hcon
    have := Finset.card_insert_le u X
    omega
  rw [Finset.mem_insert, not_or] at hwX
  let E : ℕ → ℕ → Prop := fun x y => x ∈ V ∧ y ∈ V ∧ x ≠ y ∧ (x = w ∨ y = w)
  have hE : RoundOK V E := by
    refine ⟨fun x y h => ⟨h.1, h.2.1⟩, fun x y h => ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩,
      fun x h => h.2.2.1 rfl, fun x hx y hy => ?_⟩
    have toW : ∀ z ∈ V, ReflTransGen E z w := by
      intro z hz
      by_cases hzw : z = w
      · subst hzw; exact ReflTransGen.refl
      · exact ReflTransGen.single ⟨hz, hw, hzw, Or.inr rfl⟩
    have fromW : ∀ z ∈ V, ReflTransGen E w z := by
      intro z hz
      by_cases hzw : z = w
      · subst hzw; exact ReflTransGen.refl
      · exact ReflTransGen.single ⟨hw, hz, Ne.symm hzw, Or.inl rfl⟩
    exact (toW x hx).trans (fromW y hy)
  have hr0 : 1 ≤ t - k := by omega
  set G1 := G.setRound (t - k) E with hG1def
  have hG1 : SV V N G1 := hG.setRound hE _
  have hs1 : Sim (SV V N) t G G1 := by
    refine hF t G G1 hG hG1 (fun _ _ => rfl) (fun r hr hrt => ?_)
    rw [hG1def, setRound_adj_ne _ (by omega)]
  have hX'V : insert w X ⊆ V := Finset.insert_subset hw hXV
  have hX'c : (insert w X).card + k + 1 ≤ V.card := by
    have := Finset.card_insert_le w X; omega
  have huX' : u ∉ insert w X := by
    rw [Finset.mem_insert, not_or]; exact ⟨fun h => hwX.1 h.symm, huX⟩
  obtain ⟨G2, hG2, hin2, hag2, hs2, hhid2⟩ :=
    hH t (by omega) G1 hG1 (insert w X) hX'V hX'c u hu huX'
  refine ⟨G2, hG2, hin2, fun r hrt => ?_, hs1.trans hs2, fun x hx hr => ?_⟩
  · rw [hag2 r (by omega), hG1def, setRound_adj_ne _ (by omega)]
  · have hlt : t - (k + 1) < t := by omega
    obtain ⟨y, hxy, hy⟩ := hr.front hlt
    have e : t - (k + 1) + 1 = t - k := by omega
    rw [e] at hxy hy
    have hG2r : G2.adj (t - k) = E := by
      rw [hag2 (t - k) (by omega), hG1def, setRound_adj_self]
    rw [hG2r] at hxy
    have hxw : x ≠ w := fun h => hwX.2 (h ▸ hx)
    have hyX' : y ∈ insert w X := by
      rcases hxy with rfl | ⟨-, -, -, h | h⟩
      · exact Finset.mem_insert_of_mem hx
      · exact absurd h hxw
      · rw [h]; exact Finset.mem_insert_self _ _
    exact hhid2 y hyX' hy

/-- The joint induction. -/
theorem freeP_hideP (k : ℕ) : (k + 2 ≤ V.card → FreeP α V N k) ∧ HideP α V N k := by
  induction k with
  | zero => exact ⟨fun _ => freeP_zero, hideP_zero⟩
  | succ k ih =>
    have hF1 : k + 3 ≤ V.card → FreeP α V N (k + 1) := fun h =>
      freeP_succ (ih.1 (by omega)) ih.2 h
    exact ⟨fun h => hF1 (by omega), hideP_succ hF1 ih.2⟩

theorem hideP (k : ℕ) : HideP α V N k := (freeP_hideP k).2

/-- **Theorem 5.1 (1), fixed node set.** At any time `t ≤ n - 2`, all executions on the node set
`V` (`|V| = n`) with the same `N` are in one similarity component, whatever their inputs and
communication graphs. -/
theorem sim_SV {t : ℕ} (ht : t + 2 ≤ V.card) {G H : DGraph α} (hG : SV V N G) (hH : SV V N H) :
    Sim (SV V N) t G H := by
  classical
  have hF : FreeP α V N t := (freeP_hideP t).1 ht
  -- change the inputs one node at a time
  suffices ∀ m (G : DGraph α), SV V N G →
      (V.filter fun w => G.input w ≠ H.input w).card ≤ m → Sim (SV V N) t G H from
    this _ G hG le_rfl
  intro m
  induction m with
  | zero =>
    intro G hG hc
    refine hF t G H hG hH (fun w hw => ?_) (fun r hr hrt => by omega)
    by_contra hne
    have : w ∈ V.filter fun w => G.input w ≠ H.input w := Finset.mem_filter.2 ⟨hw, hne⟩
    have := Finset.card_pos.2 ⟨_, this⟩
    omega
  | succ m ih =>
    intro G hG hc
    by_cases hall : ∀ w ∈ V, G.input w = H.input w
    · exact hF t G H hG hH hall (fun r hr hrt => by omega)
    push Not at hall
    obtain ⟨a, ha, hne⟩ := hall
    obtain ⟨u, hu, hua⟩ : ∃ u ∈ V, u ∉ ({a} : Finset ℕ) := by
      by_contra hcon
      push Not at hcon
      have := Finset.card_le_card hcon
      simp at this; omega
    obtain ⟨G', hG', hin', -, hs, hhid⟩ := hideP t t le_rfl G hG {a}
      (Finset.singleton_subset_iff.2 ha) (by simp; omega) u hu hua
    have ha' : ¬ G'.Reach a 0 u t := by simpa using hhid a (by simp)
    have hG'' : SV V N (G'.setInput a (H.input a)) :=
      ⟨hG'.1.setInput _ _, hG'.2.1, hG'.2.2⟩
    have h1 : Sim (SV V N) t G' (G'.setInput a (H.input a)) :=
      Sim.single hG' hG'' (indist_setInput hG'.1 (hG'.2.1 ▸ hu) _ ha')
    refine hs.trans (h1.trans (ih _ hG'' ?_))
    refine Nat.le_of_lt_succ (lt_of_lt_of_le (Finset.card_lt_card ?_) hc)
    refine Finset.ssubset_iff_of_subset (fun p hp => ?_) |>.2 ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_filter, setInput, hin'] at hp ⊢
      refine ⟨hp.1, fun h => hp.2 ?_⟩
      by_cases hpa : p = a
      · subst hpa; simp
      · rw [Function.update_of_ne hpa]; exact h
    · simp [ha, hne]
    · intro h
      rw [Finset.mem_filter] at h
      exact h.2 (by simp [setInput])

/-- Executions of the same size `m` and with the same `N` (node sets may differ). -/
def SameCard (m N : ℕ) (G : DGraph α) : Prop := G.Valid ∧ G.V.card = m ∧ G.N = N

theorem SV.sameCard {G : DGraph α} (h : SV V N G) : SameCard V.card N G :=
  ⟨h.1, h.2.1 ▸ rfl, h.2.2⟩

/-- **Theorem 5.1 (1)** (general form): at time `t ≤ m - 2`, all executions of size `m` with the
same `N` are in one similarity component (also changing UIDs). -/
theorem sim_sameCard {m t : ℕ} (ht : t + 2 ≤ m) {G H : DGraph α} (hG : SameCard m N G)
    (hH : SameCard m N H) : Sim (SameCard m N) t G H := by
  classical
  suffices ∀ d (G : DGraph α), SameCard m N G → (G.V \ H.V).card ≤ d →
      Sim (SameCard m N) t G H from this _ G hG le_rfl
  intro d
  induction d with
  | zero =>
    intro G hG hd
    have hsub : G.V ⊆ H.V := Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 (by omega))
    have heq : G.V = H.V := Finset.eq_of_subset_of_card_le hsub (by rw [hG.2.1, hH.2.1])
    have hG' : SV G.V N G := ⟨hG.1, rfl, hG.2.2⟩
    have hH' : SV G.V N H := ⟨hH.1, heq.symm, hH.2.2⟩
    exact (sim_SV (by rw [hG.2.1]; exact ht) hG' hH').mono
      (fun K hK => ⟨hK.1, hK.2.1 ▸ hG.2.1, hK.2.2⟩)
  | succ d ih =>
    intro G hG hd
    by_cases h0 : (G.V \ H.V).card = 0
    · exact ih G hG (by omega)
    obtain ⟨a, ha⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h0)
    rw [Finset.mem_sdiff] at ha
    have hcard : (H.V \ G.V).card = (G.V \ H.V).card := by
      have h1 := Finset.card_sdiff_add_card_inter G.V H.V
      have h2 := Finset.card_sdiff_add_card_inter H.V G.V
      rw [Finset.inter_comm] at h2
      rw [hG.2.1] at h1; rw [hH.2.1] at h2; omega
    obtain ⟨b, hb⟩ := Finset.card_pos.1 (by omega : 0 < (H.V \ G.V).card)
    rw [Finset.mem_sdiff] at hb
    obtain ⟨u, hu, hua⟩ : ∃ u ∈ G.V, u ∉ ({a} : Finset ℕ) := by
      by_contra hcon
      push Not at hcon
      have := Finset.card_le_card hcon
      rw [Finset.card_singleton, hG.2.1] at this; omega
    have hGS : SV G.V N G := ⟨hG.1, rfl, hG.2.2⟩
    obtain ⟨G', hG', -, -, hs, hhid⟩ := hideP (α := α) t t le_rfl G hGS {a}
      (Finset.singleton_subset_iff.2 ha.1) (by rw [Finset.card_singleton, hG.2.1]; omega) u hu hua
    have ha' : ¬ G'.Reach a 0 u t := by simpa using hhid a (by simp)
    have hbG' : b ∉ G'.V := hG'.2.1 ▸ hb.2
    set G'' := G'.rename (Equiv.swap a b)
    have hG'' : SameCard m N G'' := by
      refine ⟨hG'.1.rename _, ?_, hG'.2.2⟩
      simp only [G'', rename, Finset.card_map]; rw [hG'.2.1, hG.2.1]
    have h1 : Sim (SameCard m N) t G' G'' :=
      Sim.single ⟨hG'.1, by rw [hG'.2.1, hG.2.1], hG'.2.2⟩ hG''
        (indist_rename_swap hG'.1 (hG'.2.1 ▸ hu) ha' hbG')
    have hs' : Sim (SameCard m N) t G G' := hs.mono
      (fun K hK => ⟨hK.1, by rw [hK.2.1, hG.2.1], hK.2.2⟩)
    refine hs'.trans (h1.trans (ih G'' hG'' ?_))
    -- the new node set has one more node in common with `H`
    have hV'' : G''.V = insert b (G.V.erase a) := by
      ext x
      simp only [G'', mem_rename_V, Equiv.symm_swap, hG'.2.1, Finset.mem_insert,
        Finset.mem_erase]
      have hab : a ≠ b := fun h => hb.2 (h ▸ ha.1)
      by_cases hxa : x = a
      · subst hxa; simp [Equiv.swap_apply_left, hb.2, hab]
      · by_cases hxb : x = b
        · subst hxb; simp [Equiv.swap_apply_right, ha.1]
        · simp [Equiv.swap_apply_of_ne_of_ne hxa hxb, hxa, hxb]
    have : G''.V \ H.V = (G.V \ H.V).erase a := by
      rw [hV'']
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨rfl | ⟨hxa, hx⟩, hxH⟩
        · exact absurd hb.1 hxH
        · exact ⟨hxa, hx, hxH⟩
      · rintro ⟨hxa, hx, hxH⟩
        exact ⟨Or.inr ⟨hxa, hx⟩, hxH⟩
    rw [this, Finset.card_erase_of_mem (Finset.mem_sdiff.2 ha)]
    omega

/-- **Theorem 5.1 (1)**: when `n` is known a priori, at every time `t ≤ n - 2` all executions are
in one similarity component; in particular nothing non-trivial about the inputs is common
knowledge before time `n - 1`. -/
theorem theorem_5_1_known {n t : ℕ} (ht : t + 2 ≤ n) {G H : DGraph α} (hG : KnownN n G)
    (hH : KnownN n H) : Sim (KnownN n) t G H :=
  sim_sameCard ht hG hH

/-- Adding a node: any execution of size `m ≥ t + 1` is similar at time `t` (in the unknown-`n`
system) to an execution of size `m + 1`. -/
theorem exists_sim_succ_card {t : ℕ} {G : DGraph α} (hG : UnknownN G) (ht : t + 1 ≤ G.V.card) :
    ∃ G', UnknownN G' ∧ G'.V.card = G.V.card + 1 ∧ Sim UnknownN t G G' := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset G.V
  -- hide some node `w ≠ u` at time `1` from `(u, t)`
  obtain ⟨G', hG', hs, u, hu, w, hw, hhid⟩ : ∃ G' : DGraph α, SV G.V 0 G' ∧
      Sim (SV G.V 0) t G G' ∧ ∃ u ∈ G.V, ∃ w ∈ G.V, ¬ G'.Reach w 1 u t := by
    obtain ⟨u, hu⟩ := hG.1.nonempty
    rcases Nat.eq_zero_or_pos t with rfl | htp
    · exact ⟨G, ⟨hG.1, rfl, hG.2⟩, ReflTransGen.refl, u, hu, u, hu, fun h => by
        have := h.le; omega⟩
    obtain ⟨w, hw, hwu⟩ : ∃ w ∈ G.V, w ≠ u := by
      by_contra hcon
      push Not at hcon
      have : G.V ⊆ {u} := fun y hy => Finset.mem_singleton.2 (hcon y hy)
      have := Finset.card_le_card this
      simp at this; omega
    obtain ⟨G', hG', -, -, hs, hhid⟩ := hideP (α := α) (V := G.V) (N := 0) (t - 1) t (by omega)
      G ⟨hG.1, rfl, hG.2⟩ {w} (Finset.singleton_subset_iff.2 hw) (by simp; omega) u hu
      (by simpa using hwu.symm)
    refine ⟨G', hG', hs, u, hu, w, hw, ?_⟩
    have := hhid w (by simp)
    rwa [show t - (t - 1) = 1 by omega] at this
  have hxG' : x ∉ G'.V := hG'.2.1 ▸ hx
  refine ⟨G'.addLeaf x w, ⟨hG'.1.addLeaf hxG' (hG'.2.1 ▸ hw), hG'.2.2⟩, ?_, ?_⟩
  · show (insert x G'.V).card = _
    rw [Finset.card_insert_of_notMem hxG', hG'.2.1]
  · refine (hs.mono (fun K hK => ⟨hK.1, hK.2.2⟩)).trans (Sim.single ⟨hG'.1, hG'.2.2⟩
      ⟨hG'.1.addLeaf hxG' (hG'.2.1 ▸ hw), hG'.2.2⟩
      (indist_addLeaf hG'.1 (hG'.2.1 ▸ hu) hxG' hhid))

theorem exists_sim_card {t : ℕ} {G : DGraph α} (hG : UnknownN G) (ht : t + 1 ≤ G.V.card) :
    ∀ d, ∃ G', UnknownN G' ∧ G'.V.card = G.V.card + d ∧ Sim UnknownN t G G' := by
  intro d
  induction d with
  | zero => exact ⟨G, hG, rfl, ReflTransGen.refl⟩
  | succ d ih =>
    obtain ⟨G', hG', hc, hs⟩ := ih
    obtain ⟨G'', hG'', hc', hs'⟩ := exists_sim_succ_card (t := t) hG' (by omega)
    exact ⟨G'', hG'', by omega, hs.trans hs'⟩

/-- **Theorem 5.1 (2)**: when `n` is not known a priori, at time `t` all executions with at least
`t + 1` nodes are in one similarity component. In particular, in an execution with `n` nodes,
nothing non-trivial about time `0` (e.g. the inputs, or `n` itself) is common knowledge at time
`n - 1`. -/
theorem theorem_5_1_unknown {t : ℕ} {G H : DGraph α} (hG : UnknownN G) (hH : UnknownN H)
    (htG : t + 1 ≤ G.V.card) (htH : t + 1 ≤ H.V.card) : Sim UnknownN t G H := by
  set m := max G.V.card H.V.card + 1
  obtain ⟨G', hG', hcG, hsG⟩ := exists_sim_card hG htG (m - G.V.card)
  obtain ⟨H', hH', hcH, hsH⟩ := exists_sim_card hH htH (m - H.V.card)
  have hm1 : G'.V.card = m := by omega
  have hm2 : H'.V.card = m := by omega
  have := sim_sameCard (N := 0) (m := m) (t := t) (by omega) ⟨hG'.1, hm1, hG'.2⟩
    ⟨hH'.1, hm2, hH'.2⟩
  exact hsG.trans ((this.mono (fun K hK => ⟨hK.1, hK.2.2⟩)).trans hsH.symm)

end CoordCons
