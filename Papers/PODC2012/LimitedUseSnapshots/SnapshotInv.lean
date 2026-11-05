import Papers.PODC2012.LimitedUseSnapshots.SnapshotSeq

/-!
# Algorithm 3: the invariant

The invariant behind Theorem 4.2. The ghost state consists of

* `R a`: the set of all states taken so far by the max array of the node `a` (a chain);
* `L`: the linearization built so far;
* `s₀`: the vector of leaf pointers represented by the current value of `root.mr`
  (the paper's `root.seq[root.mr]`).

**Linearization points.** A `Scan` is linearized at its `ReadMax(root.mr)` (as in the paper). An
`Update` of process `j` with counter value `m` is linearized at the first `WriteMax(root.mr, d)`
after which `root.seq[root.mr]_j ≥ m`, i.e. as soon as the root pointer represents its leaf
pointer. (The paper linearizes it at the first `WriteMax(root.mr, d')` with `d' ≥ d`, where `d` is
the operation's own root pointer; that is too late, see `SnapshotCounterexample.lean`.)
-/

namespace Podc.LimitedUseSnapshots.Snapshot

open Cslib.SharedMemory

variable {P V : Type} [DecidableEq P] (T : BTree P) (v₀ : P → V)

/-- Memories of Algorithm 3. -/
abbrev Mem (v₀ : P → V) := (o : Obj) → (objSpec P V v₀ o).State

/-- Configurations of Algorithm 3. -/
abbrev Cfg (v₀ : P → V) := Config (swSnap P V v₀) (objSpec P V v₀) P (Loc P V)

/-- Linearizations. -/
abbrev Lin (v₀ : P → V) := List (OpId P × (swSnap P V v₀).Op)

variable {v₀}

/-- The leaf counters of a configuration. -/
def cntOf (C : Cfg v₀) : P → ℕ := fun j => (C.loc j).cnt

/-- `leaf_j.view[m]`, the `m`-th value written by `j` (`m ≤ count_j`). -/
def lvM (M : Mem v₀) (j : P) (m : ℕ) : V := M (.view (T.path j) m) j

/-- The partial snapshot `val` of the subtree `t` is the one given by the leaf pointers `s`
(the paper's third invariant). -/
def Agr (M : Mem v₀) (t : BTree P) (s : P → ℕ) (val : P → V) : Prop :=
  ∀ j ∈ t.leaves, val j = lvM T M j (s j)

/-- Index `k` of the node `a` (subtree `t`) is represented by some `seq`, and `view[k]` of the
node holds the corresponding partial snapshot. -/
def Corr (M : Mem v₀) (R : List Bool → Set (ℕ × ℕ)) (c : P → ℕ) (t : BTree P) (a : List Bool)
    (k : ℕ) : Prop :=
  ∃ s, SeqR R c t a k s ∧ Agr T M t s (M (.view a k))

/-- The global part of the invariant. -/
structure GInv (M : Mem v₀) (c : P → ℕ) (R : List Bool → Set (ℕ × ℕ)) (L : Lin v₀)
    (s₀ : P → ℕ) : Prop where
  chain : Chain R
  cur : ∀ a, M (.ma a) ∈ R a
  le_cur : ∀ a, ∀ q ∈ R a, q ≤ M (.ma a)
  reach : ∀ a l r, T.sub a = some (.node l r) → ∀ x y, (x, y) ∈ R a →
    Corr T M R c l (false :: a) x ∧ Corr T M R c r (true :: a) y
  root : SeqR R c T [] (M .mr) s₀ ∧ Agr T M T s₀ (M (.view [] (M .mr)))
  state : linState (A := swSnap P V v₀) L = fun j => lvM T M j (s₀ j)

/-- The part of the invariant common to the program counters of an `Update` after Line 5. -/
def UpdLin (M : Mem v₀) (L : Lin v₀) (s₀ : P → ℕ) (l : Loc P V) (pd : Option (SOp P V))
    (x : OpId P) (i : P) : Prop :=
  pd = some (.update i (lvM T M i l.cnt)) ∧ 1 ≤ l.cnt ∧ l.cnt ≤ s₀ i + 1 ∧
    (x ∈ L.map Prod.fst ↔ s₀ i = l.cnt)

/-- The per-process part of the invariant (`l` local state, `pd` pending operation, `x` current
instance of process `i`). -/
def PInv (M : Mem v₀) (c : P → ℕ) (R : List Bool → Set (ℕ × ℕ)) (L : Lin v₀) (s₀ : P → ℕ)
    (l : Loc P V) (pd : Option (SOp P V)) (x : OpId P) (i : P) : Prop :=
  match l.pc with
  | .idle => pd = none ∧ s₀ i = l.cnt
  | .lw v => pd = some (.update i v) ∧ s₀ i = l.cnt ∧ x ∉ L.map Prod.fst
  | .up a ptr => UpdLin T M L s₀ l pd x i ∧ a ≠ [] ∧ a <:+ T.path i ∧
      ∃ t, T.sub a = some t ∧ ∃ s, SeqR R c t a ptr s ∧ s i = l.cnt ∧ Agr T M t s (M (.view a ptr))
  | .sc p => UpdLin T M L s₀ l pd x i ∧ p <:+ T.path i ∧ ∃ lt rt, T.sub p = some (.node lt rt) ∧
      ∃ u w, (u, w) ∈ R p ∧ ∃ s₁ s₂, SeqR R c lt (false :: p) u s₁ ∧
        SeqR R c rt (true :: p) w s₂ ∧ s₁ i + s₂ i = l.cnt
  | .rl p u w => UpdLin T M L s₀ l pd x i ∧ p <:+ T.path i ∧
      ∃ lt rt, T.sub p = some (.node lt rt) ∧ (u, w) ∈ R p ∧ ∃ s₁ s₂,
        SeqR R c lt (false :: p) u s₁ ∧ SeqR R c rt (true :: p) w s₂ ∧ s₁ i + s₂ i = l.cnt
  | .rr p u w lv => UpdLin T M L s₀ l pd x i ∧ p <:+ T.path i ∧
      ∃ lt rt, T.sub p = some (.node lt rt) ∧ (u, w) ∈ R p ∧ ∃ s₁ s₂,
        SeqR R c lt (false :: p) u s₁ ∧ SeqR R c rt (true :: p) w s₂ ∧ s₁ i + s₂ i = l.cnt ∧
        Agr T M lt s₁ lv
  | .wv p k val => UpdLin T M L s₀ l pd x i ∧ p <:+ T.path i ∧
      ∃ lt rt, T.sub p = some (.node lt rt) ∧ ∃ s, SeqR R c (.node lt rt) p k s ∧ s i = l.cnt ∧
        Agr T M (.node lt rt) s val
  | .wm d => UpdLin T M L s₀ l pd x i ∧
      ∃ s, SeqR R c T [] d s ∧ s i = l.cnt ∧ Agr T M T s (M (.view [] d))
  | .ackU => UpdLin T M L s₀ l pd x i ∧ s₀ i = l.cnt
  | .s0 => pd = some .scan ∧ s₀ i = l.cnt ∧ x ∉ L.map Prod.fst
  | .s1 d => pd = some .scan ∧ s₀ i = l.cnt ∧ ∃ s, SeqR R c T [] d s ∧
      Agr T M T s (M (.view [] d)) ∧
      (swSnap P V v₀).respIn (swSnap P V v₀).init L x = some (some (fun j => lvM T M j (s j)))
  | .retS val => pd = some .scan ∧ s₀ i = l.cnt ∧
      (swSnap P V v₀).respIn (swSnap P V v₀).init L x = some (some val)

/-- **The invariant of Algorithm 3.** -/
structure Inv (α : List (Label P (swSnap P V v₀))) (C : Cfg v₀) (R : List Bool → Set (ℕ × ℕ))
    (L : Lin v₀) (s₀ : P → ℕ) : Prop where
  lin : IsLinearization α L
  g : GInv T C.mem (cntOf C) R L s₀
  proc : ∀ i, PInv T C.mem (cntOf C) R L s₀ (C.loc i) (C.pend i) (curOp α i) i

/-! ### Frames: what a step of another process preserves -/

/-- The memory/counter/ghost changes of a step preserve all facts about views. -/
structure Frame (M M' : Mem v₀) (c c' : P → ℕ) (R R' : List Bool → Set (ℕ × ℕ)) : Prop where
  hR : ∀ a, R a ⊆ R' a
  chain : Chain R'
  cnt : c ≤ c'
  lv : ∀ j m, m ≤ c j → lvM T M' j m = lvM T M j m
  view : ∀ a k t s, T.sub a = some t → SeqR R c t a k s → Agr T M t s (M (.view a k)) →
    Agr T M' t s (M' (.view a k))

variable {T}

namespace Frame

variable {M M' : Mem v₀} {c c' : P → ℕ} {R R' : List Bool → Set (ℕ × ℕ)}

lemma seq (hF : Frame T M M' c c' R R') {t a k s} (h : SeqR R c t a k s) :
    SeqR R' c' t a k s := SeqR.mono hF.hR hF.cnt h

lemma agr (hF : Frame T M M' c c' R R') {t s val} (hs : s ≤ c) (h : Agr T M t s val) :
    Agr T M' t s val :=
  fun j hj => (h j hj).trans (hF.lv j (s j) (hs j)).symm

lemma lvfun (hF : Frame T M M' c c' R R') {s : P → ℕ} (hs : s ≤ c) :
    (fun j => lvM T M' j (s j)) = fun j => lvM T M j (s j) :=
  funext fun j => hF.lv j (s j) (hs j)

lemma corr (hF : Frame T M M' c c' R R') {t a k} (hsub : T.sub a = some t)
    (h : Corr T M R c t a k) : Corr T M' R' c' t a k :=
  let ⟨s, hs, hag⟩ := h; ⟨s, hF.seq hs, hF.view a k t s hsub hs hag⟩

end Frame

lemma seq_le_cnt (hT : T.WF) {R : List Bool → Set (ℕ × ℕ)} {c : P → ℕ} {t a k s}
    (hsub : T.sub a = some t) (h : SeqR R c t a k s) : s ≤ c :=
  SeqR.le_cnt (BTree.nodup_of_sub hsub hT.nodup) h

lemma seq_le_cnt_root (hT : T.WF) {R : List Bool → Set (ℕ × ℕ)} {c : P → ℕ} {k s}
    (h : SeqR R c T [] k s) : s ≤ c := seq_le_cnt hT rfl h

/-- Preservation of the `Update` part by steps of other processes. -/
lemma UpdLin.frame {M M' : Mem v₀} {L L' : Lin v₀} {s₀ s₀' : P → ℕ} {l : Loc P V}
    {pd : Option (SOp P V)} {x : OpId P} {i : P} (h : UpdLin T M L s₀ l pd x i)
    (hlv : lvM T M' i l.cnt = lvM T M i l.cnt) (hs₀ : s₀ i ≤ s₀' i) (hs₀c : s₀' i ≤ l.cnt)
    (hL : x ∈ L'.map Prod.fst ↔ x ∈ L.map Prod.fst ∨ s₀ i < s₀' i) :
    UpdLin T M' L' s₀' l pd x i := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [hlv]; exact h1, h2, by omega, ?_⟩
  rw [hL, h4]; omega

/-- **Frame lemma**: a step that does not change the local state and pending operation of `i`
preserves its per-process invariant. -/
lemma PInv.frame (hT : T.WF) {M M' : Mem v₀} {c c' : P → ℕ} {R R' : List Bool → Set (ℕ × ℕ)}
    {L L' : Lin v₀} {s₀ s₀' : P → ℕ} {l : Loc P V} {pd : Option (SOp P V)} {x : OpId P} {i : P}
    (h : PInv T M c R L s₀ l pd x i) (hF : Frame T M M' c c' R R') (hci : l.cnt ≤ c i)
    (hs₀ : s₀ ≤ s₀') (hs₀c : s₀' i ≤ l.cnt)
    (hL : x ∈ L'.map Prod.fst ↔ x ∈ L.map Prod.fst ∨ s₀ i < s₀' i)
    (hresp : ∀ y ∈ L.map Prod.fst, (swSnap P V v₀).respIn (swSnap P V v₀).init L' y =
      (swSnap P V v₀).respIn (swSnap P V v₀).init L y) :
    PInv T M' c' R' L' s₀' l pd x i := by
  have hlv : lvM T M' i l.cnt = lvM T M i l.cnt := hF.lv i l.cnt hci
  unfold PInv at h ⊢
  split at h
  · rename_i hpc
    exact ⟨h.1, le_antisymm hs₀c (h.2 ▸ hs₀ i)⟩
  · rename_i v hpc
    have : s₀' i = l.cnt := le_antisymm hs₀c (h.2.1 ▸ hs₀ i)
    refine ⟨h.1, this, ?_⟩
    rw [hL]; rintro (h' | h'); exact h.2.2 h'; omega
  · rename_i a ptr hpc
    obtain ⟨hu, ha, hsuf, t, hsub, s, hs, hsi, hag⟩ := h
    exact ⟨hu.frame hlv (hs₀ i) hs₀c hL, ha, hsuf, t, hsub, s, hF.seq hs, hsi,
      hF.view a ptr t s hsub hs hag⟩
  · rename_i p hpc
    obtain ⟨hu, hsuf, lt, rt, hsub, x', y', hxy, s₁, s₂, h₁, h₂, hsi⟩ := h
    exact ⟨hu.frame hlv (hs₀ i) hs₀c hL, hsuf, lt, rt, hsub, x', y', hF.hR p hxy, s₁, s₂,
      hF.seq h₁, hF.seq h₂, hsi⟩
  · rename_i p x' y' hpc
    obtain ⟨hu, hsuf, lt, rt, hsub, hxy, s₁, s₂, h₁, h₂, hsi⟩ := h
    exact ⟨hu.frame hlv (hs₀ i) hs₀c hL, hsuf, lt, rt, hsub, hF.hR p hxy, s₁, s₂,
      hF.seq h₁, hF.seq h₂, hsi⟩
  · rename_i p x' y' lv hpc
    obtain ⟨hu, hsuf, lt, rt, hsub, hxy, s₁, s₂, h₁, h₂, hsi, hag⟩ := h
    have hsub' : T.sub (false :: p) = some lt := by simp [hsub, BTree.child]
    exact ⟨hu.frame hlv (hs₀ i) hs₀c hL, hsuf, lt, rt, hsub, hF.hR p hxy, s₁, s₂,
      hF.seq h₁, hF.seq h₂, hsi, hF.agr (seq_le_cnt hT hsub' h₁) hag⟩
  · rename_i p k val hpc
    obtain ⟨hu, hsuf, lt, rt, hsub, s, hs, hsi, hag⟩ := h
    exact ⟨hu.frame hlv (hs₀ i) hs₀c hL, hsuf, lt, rt, hsub, s, hF.seq hs, hsi,
      hF.agr (seq_le_cnt hT hsub hs) hag⟩
  · rename_i d hpc
    obtain ⟨hu, s, hs, hsi, hag⟩ := h
    exact ⟨hu.frame hlv (hs₀ i) hs₀c hL, s, hF.seq hs, hsi, hF.view [] d T s rfl hs hag⟩
  · rename_i hpc
    obtain ⟨hu, h2⟩ := h
    exact ⟨hu.frame hlv (hs₀ i) hs₀c hL, le_antisymm hs₀c (h2 ▸ hs₀ i)⟩
  · rename_i hpc
    have : s₀' i = l.cnt := le_antisymm hs₀c (h.2.1 ▸ hs₀ i)
    refine ⟨h.1, this, ?_⟩
    rw [hL]; rintro (h' | h'); exact h.2.2 h'; omega
  · rename_i d hpc
    obtain ⟨h1, h2, s, hs, hag, hr⟩ := h
    have hx : x ∈ L.map Prod.fst := ObjSpec.mem_of_respIn_eq_some hr
    refine ⟨h1, le_antisymm hs₀c (h2 ▸ hs₀ i), s, hF.seq hs, hF.view [] d T s rfl hs hag, ?_⟩
    rw [hresp x hx, hr, hF.lvfun (seq_le_cnt_root hT hs)]
  · rename_i val hpc
    obtain ⟨h1, h2, hr⟩ := h
    have hx : x ∈ L.map Prod.fst := ObjSpec.mem_of_respIn_eq_some hr
    exact ⟨h1, le_antisymm hs₀c (h2 ▸ hs₀ i), by rw [hresp x hx, hr]⟩

end Podc.LimitedUseSnapshots.Snapshot
