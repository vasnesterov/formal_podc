import Papers.PODC2022.DynamicRootedTrees.Defs

/-!
# Exact broadcast times `t*(𝒯ₙ)` for small `n`, computed in the kernel

A verified exhaustive search. A relation on `Fin n` is encoded as a bit mask `m : ℕ` (bit
`x * n + y` set iff `x → y`, i.e. row `x` is the `x`-th block of width `n`); all operations
are on `ℕ` via `Nat.land`/`Nat.lor`/`Nat.shiftRight`/…, which the kernel evaluates with GMP.

* `trees n`: masks of all rooted trees with self-loops on `Fin n` (enumerated as root + parent
  list, filtered by a decidable "reaches the root within `n` steps" test, deduplicated).
  `exists_mem_trees`/`rel_mem_of_mem_trees`: it encodes exactly `treesWithLoops n`.
* `frontier n k`: `F₀ = {id} \ B`, `F_{k+1} = dedup {P ∘ E | P ∈ F_k, E ∈ trees n} \ B`, where
  `B` are the broadcast states. Composition `P ∘ E` uses a precomputed table
  `S ↦ ⋃_{z ∈ S} E(z)` of `E` (`tab`, `compT`); deduplication uses a bit set (`dedupAux`).
* `frontier_sound`: if `G₁, G₂, … ∈ 𝒯ₙ` has not broadcast after `k` rounds, then the mask of
  `G₁ ∘ ⋯ ∘ G_k` is in `frontier n k`. Hence `frontier n K = []` gives `t*(𝒯ₙ) ≤ K`
  (`advBroadcastTime_le_of_frontier`); explicit sequences give lower bounds
  (`le_advBroadcastTime_of_seq`).

## Main results

`advBroadcastTime_trees_one/two/three/four`: `t*(𝒯ₙ) = 0, 1, 2, 4` for `n = 1, 2, 3, 4`
(frontier sizes for `n = 4`: `1, 60, 528, 48, 0`; the kernel check takes ≈ 15 s).

An (unverified) Python search gives `t*(𝒯₅) = 5` (frontier sizes `620, 94380, 119640, 12360, 0`),
which is out of reach of this kernel computation (≈ 1.4 · 10⁸ compositions).
-/

namespace DynamicRootedTrees

open Cslib.DynNet Relation

namespace FrontierSearch

/-- The bit mask with bits `i < N` set according to `f`. -/
def mkMask (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | N + 1 => mkMask f N ||| (if f N then 2 ^ N else 0)

variable (n : ℕ)

/-- All-ones mask of width `w`. -/
def ones (w : ℕ) : ℕ := Nat.sub (Nat.shiftLeft 1 w) 1

/-- The `i`-th block of width `w` of `m`. -/
def blk (w m i : ℕ) : ℕ := Nat.land (Nat.shiftRight m (Nat.mul i w)) (ones w)

/-- Pack `f 0, …, f (N-1)` (truncated to width `w`) as consecutive blocks of width `w`. -/
def pack (w : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => Nat.lor (pack w f N) (Nat.shiftLeft (Nat.land (f N) (ones w)) (Nat.mul N w))

/-- `∃ k' < k, f k'`. -/
def anyUpTo (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => f k || anyUpTo f k

/-- Encoding of a relation on `Fin n` given by a Boolean function (row `x` = block `x`). -/
def ofRel (f : ℕ → ℕ → Bool) : ℕ := pack n (fun x => mkMask (f x) n) n

/-- The identity relation. -/
def idM : ℕ := ofRel n (fun x y => x == y)

/-- For a relation `E`, the table `S ↦ ⋃_{z ∈ S} E(z)` indexed by subsets `S` of `Fin n`. -/
def orRows (E S : ℕ) : ℕ → ℕ
  | 0 => 0
  | z + 1 => Nat.lor (orRows E S z) (if Nat.testBit S z then blk n E z else 0)

/-- The table of `E`: block `S` is `⋃_{z ∈ S} E(z)`. -/
def tab (E : ℕ) : ℕ := pack n (fun S => orRows n E S n) (2 ^ n)

/-- Composition `P ∘ E`, given the table of `E`. -/
def compT (T P : ℕ) : ℕ := pack n (fun x => blk n T (blk n P x)) n

/-- Some row of `m` is full: some process has reached everybody. -/
def bcM (m : ℕ) : Bool := anyUpTo (fun x => Nat.beq (blk n m x) (ones n)) n

/-- The parent function of `(r, l)`, made idempotent at `r`. -/
def parentFn (r : ℕ) (l : List ℕ) (v : ℕ) : ℕ := if v = r then r else l.getD v 0

/-- Every vertex reaches `r` within `n` steps. -/
def treeOK (r : ℕ) (l : List ℕ) : Bool := (List.range n).all fun v => (parentFn r l)^[n] v == r

/-- The tree with self-loops with root `r` and parent list `l`. -/
def treeM (r : ℕ) (l : List ℕ) : ℕ :=
  ofRel n (fun x y => x == y || (y != r && l.getD y 0 == x))

/-- All lists of length `k` with entries `< n`. -/
def lists : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (lists k).flatMap fun l => (List.range n).map (· :: l)

/-- Deduplication with a bit set `s` of the elements already in `acc`. -/
def dedupAux : List ℕ → List ℕ → ℕ → List ℕ
  | [], acc, _ => acc
  | m :: ms, acc, s =>
    if s.testBit m then dedupAux ms acc s else dedupAux ms (m :: acc) (s ||| 2 ^ m)

/-- The masks of all rooted trees with self-loops on `Fin n`. -/
def trees : List ℕ :=
  dedupAux ((List.range n).flatMap fun r => ((lists n n).filter (treeOK n r)).map (treeM n r)) [] 0

/-- One step of the frontier search (`TT` = tables of the trees). -/
def step (TT F : List ℕ) : List ℕ :=
  dedupAux ((F.flatMap fun P => TT.map fun T => compT n T P).filter (fun m => !bcM n m)) [] 0

/-- `frontier n k`: all products of `k` trees that have not broadcast (up to the soundness
theorem `frontier_sound`, which only needs `⊇`). -/
def frontier : ℕ → List ℕ
  | 0 => [idM n].filter (fun m => !bcM n m)
  | k + 1 => step n ((trees n).map (tab n)) (frontier k)

/-- The product of the masks `f 1, …, f k`. -/
def prodSeq (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => idM n
  | k + 1 => compT n (tab n (f (1 + k))) (prodSeq f k)

/-- The sequence `l₁, l₂, …, then d, d, …` (rounds are 1-indexed). -/
def seqF (l : List ℕ) (d i : ℕ) : ℕ := l.getD (i - 1) d

/-! ### Bit-level lemmas -/

theorem testBit_mkMask (f : ℕ → Bool) (N i : ℕ) :
    (mkMask f N).testBit i = (decide (i < N) && f i) := by
  induction N with
  | zero => simp [mkMask]
  | succ N ih =>
    rw [mkMask, Nat.testBit_or, ih]
    by_cases hi : i = N
    · subst hi; cases h : f i <;> simp
    · have : (if f N = true then 2 ^ N else 0).testBit i = false := by
        split_ifs <;> simp [Ne.symm hi]
      rw [this, Bool.or_false]
      by_cases h : i < N
      · simp [h, show i < N + 1 by omega]
      · simp [h, show ¬ i < N + 1 by omega]

theorem ones_eq (w : ℕ) : ones w = 2 ^ w - 1 := by
  show 1 <<< w - 1 = _; rw [Nat.one_shiftLeft]

theorem testBit_ones (w i : ℕ) : (ones w).testBit i = decide (i < w) := by
  rw [ones_eq, Nat.testBit_two_pow_sub_one]

theorem testBit_blk (w m i j : ℕ) :
    (blk w m i).testBit j = (decide (j < w) && m.testBit (i * w + j)) := by
  show ((m >>> (i * w)) &&& ones w).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones, Bool.and_comm]

theorem blk_lt (w m i : ℕ) : blk w m i < 2 ^ w := by
  show (m >>> (i * w)) &&& ones w < 2 ^ w
  refine lt_of_le_of_lt Nat.and_le_right ?_
  rw [ones_eq]; exact Nat.sub_lt (Nat.two_pow_pos w) one_pos

theorem testBit_pack (w : ℕ) (f : ℕ → ℕ) (N i j : ℕ) (hj : j < w) :
    (pack w f N).testBit (i * w + j) = (decide (i < N) && (f i).testBit j) := by
  induction N with
  | zero => simp [pack]
  | succ N ih =>
    show ((pack w f N) ||| ((f N &&& ones w) <<< (N * w))).testBit (i * w + j) = _
    rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft, Nat.testBit_and, testBit_ones]
    rcases lt_trichotomy i N with h | rfl | h
    · have h2 : (i + 1) * w ≤ N * w := Nat.mul_le_mul_right _ h
      rw [Nat.add_mul, one_mul] at h2
      have h1 : ¬ (i * w + j ≥ N * w) := by omega
      simp [h, h1, show i < N + 1 by omega]
    · simp [hj]
    · have h2 : (N + 1) * w ≤ i * w := Nat.mul_le_mul_right _ h
      rw [Nat.add_mul, one_mul] at h2
      have h1 : i * w + j ≥ N * w := by omega
      have h3 : ¬ (i * w + j - N * w < w) := by omega
      simp [h3, show ¬ i < N by omega, show ¬ i < N + 1 by omega]

theorem testBit_orRows (E S z y : ℕ) :
    (orRows n E S z).testBit y = true ↔
      ∃ z' < z, S.testBit z' = true ∧ (blk n E z').testBit y = true := by
  induction z with
  | zero => simp [orRows]
  | succ z ih =>
    show (orRows n E S z ||| (if S.testBit z then blk n E z else 0)).testBit y = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨z', hz', h⟩ | h)
      · exact ⟨z', by omega, h⟩
      · split_ifs at h with hS
        · exact ⟨z, by omega, hS, h⟩
        · simp at h
    · rintro ⟨z', hz', h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hz' with hz' | rfl
      · exact Or.inl ⟨z', hz', h1, h2⟩
      · right; simpa [h1] using h2

theorem anyUpTo_iff (f : ℕ → Bool) (k : ℕ) : anyUpTo f k = true ↔ ∃ x < k, f x = true := by
  induction k with
  | zero => simp [anyUpTo]
  | succ k ih =>
    rw [anyUpTo, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨x, hx, h⟩)
      · exact ⟨k, by omega, h⟩
      · exact ⟨x, by omega, h⟩
    · rintro ⟨x, hx, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
      · exact Or.inr ⟨x, hx, h⟩
      · exact Or.inl h

/-! ### Decoding masks as relations -/

/-- The relation on `Fin n` encoded by the mask `m`: bit `x * n + y` is `x → y`. -/
def rel (m : ℕ) (x y : Fin n) : Prop := m.testBit (x * n + y) = true

theorem testBit_blk_fin (m x : ℕ) (y : Fin n) : (blk n m x).testBit y = m.testBit (x * n + y) := by
  rw [testBit_blk]; simp [y.2]

theorem rel_ofRel (f : ℕ → ℕ → Bool) (x y : Fin n) : rel n (ofRel n f) x y ↔ f x y = true := by
  unfold rel ofRel
  rw [testBit_pack _ _ _ _ _ y.2, testBit_mkMask]; simp [x.2, y.2]

theorem rel_idM : rel n (idM n) = (· = ·) := by
  funext x y; apply propext
  rw [idM, rel_ofRel]; simp [Fin.ext_iff]

theorem rel_compT (E P : ℕ) : rel n (compT n (tab n E) P) = Relation.Comp (rel n P) (rel n E) := by
  funext x y; apply propext
  unfold rel compT
  rw [testBit_pack _ _ _ _ _ y.2, testBit_blk_fin, tab, testBit_pack _ _ _ _ _ y.2]
  simp only [x.2, blk_lt, decide_true, Bool.true_and]
  rw [testBit_orRows]
  constructor
  · rintro ⟨z, hz, h1, h2⟩
    refine ⟨⟨z, hz⟩, ?_, ?_⟩
    · rw [testBit_blk] at h1; simpa [hz] using h1
    · rw [testBit_blk_fin] at h2; exact h2
  · rintro ⟨z, h1, h2⟩
    refine ⟨z, z.2, ?_, ?_⟩
    · rw [testBit_blk_fin]; exact h1
    · rw [testBit_blk_fin]; exact h2

theorem bcM_iff (m : ℕ) : bcM n m = true ↔ ∃ x : Fin n, ∀ y : Fin n, rel n m x y := by
  rw [bcM, anyUpTo_iff]
  constructor
  · rintro ⟨x, hx, h⟩
    have h := Nat.eq_of_beq_eq_true h
    refine ⟨⟨x, hx⟩, fun y => ?_⟩
    have := congrArg (fun a => Nat.testBit a y) h
    simp only [testBit_blk_fin, testBit_ones, y.2, decide_true] at this
    exact this
  · rintro ⟨x, h⟩
    refine ⟨x, x.2, ?_⟩
    suffices hb : blk n m x = ones n by rw [hb]; exact Nat.beq_refl _
    apply Nat.eq_of_testBit_eq
    intro j
    rw [testBit_blk, testBit_ones]
    by_cases hj : j < n
    · have h1 : m.testBit (x * n + j) = true := h ⟨j, hj⟩
      simpa [hj] using h1
    · simp [hj]

/-! ### Enumerating rooted trees -/

theorem mem_lists {l : List ℕ} {k : ℕ} : l ∈ lists n k ↔ l.length = k ∧ ∀ a ∈ l, a < n := by
  induction k generalizing l with
  | zero => cases l <;> simp [lists]
  | succ k ih =>
    cases l with
    | nil => simp [lists]
    | cons a l =>
      simp only [lists, List.mem_flatMap, List.mem_map, List.mem_range, List.cons.injEq,
        List.length_cons, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨l', hl', a', ha', rfl, rfl⟩
        exact ⟨by rw [(ih.1 hl').1], ha', (ih.1 hl').2⟩
      · rintro ⟨hlen, ha, hl⟩
        exact ⟨l, ih.2 ⟨by omega, hl⟩, a, ha, rfl, rfl⟩

/-- If `f r = r` and some iterate of `f` maps `v` to `r`, then already `f^[n] v = r`. -/
theorem iterate_card_eq {n : ℕ} (f : Fin n → Fin n) (r : Fin n) (hr : f r = r) :
    ∀ k (v : Fin n), f^[k] v = r → f^[n] v = r := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro v hk
  by_cases hkn : k ≤ n
  · obtain ⟨d, rfl⟩ : ∃ d, n = d + k := ⟨n - k, by omega⟩
    rw [Function.iterate_add_apply, hk, Function.iterate_fixed hr]
  · have key : ∀ a b : Fin (n + 1), (a : ℕ) < b → f^[a] v = f^[b] v → f^[n] v = r := by
      intro a b hab he
      have hb := b.2
      apply ih (k - b + a) (by omega) v
      have : k = (k - b) + b := by omega
      rw [this, Function.iterate_add_apply] at hk
      rw [Function.iterate_add_apply, he]; exact hk
    obtain ⟨a, b, hab, he⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (fun a : Fin (n + 1) => f^[a] v) (by simp)
    rcases lt_or_gt_of_ne hab with h | h
    · exact key a b h he
    · exact key b a h he.symm

/-- The parent function made idempotent at the root. -/
def qfn {n : ℕ} (T : RootedTree n) (v : Fin n) : Fin n := if v = T.root then T.root else T.parent v

theorem exists_iterate_qfn {n : ℕ} (T : RootedTree n) :
    ∀ k (v : Fin n), T.parent^[k] v = T.root → ∃ k', (qfn T)^[k'] v = T.root := by
  intro k
  induction k with
  | zero => intro v h; exact ⟨0, h⟩
  | succ k ih =>
    intro v h
    by_cases hv : v = T.root
    · exact ⟨0, hv⟩
    · rw [Function.iterate_succ_apply] at h
      obtain ⟨k', hk'⟩ := ih _ h
      exact ⟨k' + 1, by rw [Function.iterate_succ_apply, qfn]; simpa [hv] using hk'⟩

/-- The parent list of a tree. -/
def parentList {n : ℕ} (T : RootedTree n) : List ℕ := List.ofFn fun i => (T.parent i : ℕ)

theorem getD_parentList {n : ℕ} (T : RootedTree n) (v : Fin n) :
    (parentList T).getD v 0 = T.parent v := by
  simp [parentList, List.getD_eq_getElem?_getD]

theorem treeOK_parentList (T : RootedTree n) : treeOK n T.root (parentList T) = true := by
  have hsemi : Function.Semiconj Fin.val (qfn T) (parentFn T.root (parentList T)) := by
    intro v
    unfold qfn parentFn
    by_cases h : v = T.root
    · simp [h]
    · have h' : (v : ℕ) ≠ T.root := fun e => h (Fin.ext e)
      simp only [h, h', ↓reduceIte]; rw [getD_parentList]
  unfold treeOK
  rw [List.all_eq_true]
  intro v hv
  rw [List.mem_range] at hv
  have h := (hsemi.iterate_right n) ⟨v, hv⟩
  obtain ⟨k, hk⟩ := T.reach_root ⟨v, hv⟩
  obtain ⟨k', hk'⟩ := exists_iterate_qfn T k _ hk
  rw [beq_iff_eq]
  simp only at h
  rw [← h, iterate_card_eq (qfn T) T.root (by simp [qfn]) k' _ hk']

theorem rel_treeM_parentList (T : RootedTree n) : rel n (treeM n T.root (parentList T)) = T.adj := by
  funext x y; apply propext
  rw [treeM, rel_ofRel, getD_parentList]
  simp [RootedTree.adj, Fin.ext_iff]

theorem mem_dedupAux : ∀ (ms acc : List ℕ) (s : ℕ), (∀ a, s.testBit a = true → a ∈ acc) →
    ∀ m, m ∈ ms ∨ m ∈ acc → m ∈ dedupAux ms acc s
  | [], acc, s, _, m, h => by simpa [dedupAux] using h
  | a :: ms, acc, s, hs, m, h => by
    rw [dedupAux]
    split_ifs with ha
    · apply mem_dedupAux ms acc s hs
      rcases h with h | h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr (hs _ ha)
        · exact Or.inl h
      · exact Or.inr h
    · apply mem_dedupAux ms (a :: acc)
      · intro b hb
        rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at hb
        rcases hb with hb | hb
        · exact List.mem_cons_of_mem _ (hs _ hb)
        · rw [decide_eq_true_eq] at hb; subst hb; exact List.mem_cons_self
      · rcases h with h | h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inr List.mem_cons_self
          · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_of_mem_dedupAux : ∀ (ms acc : List ℕ) (s m : ℕ), m ∈ dedupAux ms acc s → m ∈ ms ∨ m ∈ acc
  | [], acc, s, m, h => by simpa [dedupAux] using h
  | a :: ms, acc, s, m, h => by
    rw [dedupAux] at h
    split_ifs at h with ha
    · rcases mem_of_mem_dedupAux ms acc s m h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h
    · rcases mem_of_mem_dedupAux ms _ _ m h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h

/-- Every rooted tree (with self-loops) on `Fin n` is encoded by some mask in `trees n`. -/
theorem exists_mem_trees (T : RootedTree n) : ∃ m ∈ trees n, rel n m = T.adj := by
  refine ⟨_, mem_dedupAux _ _ _ (by simp) _ (Or.inl ?_), rel_treeM_parentList n T⟩
  rw [List.mem_flatMap]
  refine ⟨T.root, List.mem_range.2 T.root.2, List.mem_map.2 ⟨parentList T, ?_, rfl⟩⟩
  rw [List.mem_filter, mem_lists]
  refine ⟨⟨by simp [parentList], ?_⟩, treeOK_parentList n T⟩
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
  exact (T.parent i).2

theorem getD_lt {l : List ℕ} (hl : ∀ a ∈ l, a < n) (v : Fin n) : l.getD v 0 < n := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[(v : ℕ)]? with
  | none => exact Nat.lt_of_le_of_lt (Nat.zero_le _) v.2
  | some a => exact hl a (List.mem_of_getElem? h)

theorem exists_iterate_of_parentFn {r : Fin n} {l : List ℕ} (p : Fin n → Fin n)
    (hp : ∀ v, (p v : ℕ) = l.getD v 0) :
    ∀ j (v : Fin n), (parentFn r l)^[j] v = r → ∃ k, p^[k] v = r := by
  intro j
  induction j with
  | zero => intro v h; exact ⟨0, Fin.ext h⟩
  | succ j ih =>
    intro v h
    rw [Function.iterate_succ_apply] at h
    by_cases hv : (v : ℕ) = r
    · exact ⟨0, Fin.ext hv⟩
    · simp only [parentFn, hv, ↓reduceIte] at h; rw [← hp] at h
      obtain ⟨k, hk⟩ := ih _ h
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-- Conversely, every mask in `trees n` encodes a rooted tree with self-loops. -/
theorem rel_mem_of_mem_trees {m : ℕ} (hm : m ∈ trees n) : rel n m ∈ treesWithLoops n := by
  rcases mem_of_mem_dedupAux _ _ _ _ hm with hm | hm
  · obtain ⟨r, hr, hm⟩ := List.mem_flatMap.1 hm
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hm
    rw [List.mem_filter, mem_lists] at hl
    obtain ⟨⟨-, hl⟩, hok⟩ := hl
    rw [List.mem_range] at hr
    let p : Fin n → Fin n := fun v => ⟨l.getD v 0, getD_lt n hl v⟩
    refine ⟨⟨⟨r, hr⟩, p, fun v => ?_⟩, ?_⟩
    · unfold treeOK at hok
      rw [List.all_eq_true] at hok
      have := hok v (List.mem_range.2 v.2)
      rw [beq_iff_eq] at this
      exact exists_iterate_of_parentFn n (r := ⟨r, hr⟩) p (fun _ => rfl) n v this
    · funext x y; apply propext
      rw [treeM, rel_ofRel]
      simp [RootedTree.adj, Fin.ext_iff, p]
  · simp at hm

/-! ### Soundness of the frontier search -/

/-- **Soundness.** If a sequence of rooted trees has not broadcast after `k` rounds, then its
product `G₁ ∘ ⋯ ∘ G_k` is (encoded by a mask) in the `k`-th frontier. -/
theorem frontier_sound {G : ℕ → Fin n → Fin n → Prop} (hG : ∀ i, G i ∈ treesWithLoops n) :
    ∀ k, ¬ Broadcasts G k → ∃ m ∈ frontier n k, rel n m = prod G 1 k
  | 0, h => by
    refine ⟨idM n, ?_, by rw [rel_idM, prod_zero]⟩
    simp only [frontier, List.mem_filter, List.mem_singleton, true_and, Bool.not_eq_true']
    cases hb : bcM n (idM n)
    · rfl
    · exfalso; apply h
      obtain ⟨x, hx⟩ := (bcM_iff n _).1 hb
      exact ⟨x, fun y => by rw [prod_zero, ← rel_idM n]; exact hx y⟩
  | k + 1, h => by
    have hk : ¬ Broadcasts G k := fun hb =>
      h (hb.mono (fun i => refl_of_mem_treesWithLoops (hG i)) (Nat.le_succ k))
    obtain ⟨m, hm, hmr⟩ := frontier_sound hG k hk
    obtain ⟨T, hT⟩ := hG (1 + k)
    obtain ⟨e, he, her⟩ := exists_mem_trees n T
    have hrel : rel n (compT n (tab n e) m) = prod G 1 (k + 1) := by
      rw [rel_compT, hmr, her, hT, prod_succ]
    refine ⟨compT n (tab n e) m, ?_, hrel⟩
    apply mem_dedupAux _ _ _ (by simp) _ (Or.inl _)
    rw [List.mem_filter]
    refine ⟨List.mem_flatMap.2 ⟨m, hm, List.mem_map.2 ⟨tab n e, List.mem_map_of_mem he, rfl⟩⟩, ?_⟩
    rw [Bool.not_eq_true']
    cases hb : bcM n (compT n (tab n e) m)
    · rfl
    · exfalso; apply h
      obtain ⟨x, hx⟩ := (bcM_iff n _).1 hb
      exact ⟨x, fun y => by rw [← hrel]; exact hx y⟩

/-- An empty `K`-th frontier certifies that every sequence of rooted trees broadcasts by round
`K`. -/
theorem broadcasts_of_frontier_eq_nil {K : ℕ} (h : frontier n K = [])
    (G : ℕ → Fin n → Fin n → Prop) (hG : ∀ i, G i ∈ treesWithLoops n) : Broadcasts G K := by
  by_contra hb
  obtain ⟨m, hm, -⟩ := frontier_sound n hG K hb
  simp [h] at hm

theorem advBroadcastTime_le_of_frontier {K : ℕ} (h : frontier n K = []) :
    advBroadcastTime (treesWithLoops n) ≤ K :=
  advBroadcastTime_le (broadcasts_of_frontier_eq_nil n h)

/-! ### Explicit sequences (lower bounds) -/

theorem rel_prodSeq (f : ℕ → ℕ) : ∀ k, rel n (prodSeq n f k) = prod (fun i => rel n (f i)) 1 k
  | 0 => rel_idM n
  | k + 1 => by rw [prodSeq, rel_compT, rel_prodSeq f k, prod_succ]

theorem le_advBroadcastTime_of_seq {K t : ℕ} (hK : frontier n K = []) (f : ℕ → ℕ)
    (hf : ∀ i, f i ∈ trees n) (ht : ∀ s < t, bcM n (prodSeq n f s) = false) :
    t ≤ advBroadcastTime (treesWithLoops n) := by
  refine le_advBroadcastTime (broadcasts_of_frontier_eq_nil n hK) (G := fun i => rel n (f i))
    (fun i => rel_mem_of_mem_trees n (hf i)) (fun s hs hb => ?_)
  obtain ⟨x, hx⟩ := hb
  have := ht s hs
  rw [← Bool.not_eq_true, bcM_iff] at this
  exact this ⟨x, fun y => by rw [rel_prodSeq]; exact hx y⟩

theorem seqF_mem {l : List ℕ} {d : ℕ} (h : ∀ m ∈ d :: l, m ∈ trees n) (i : ℕ) :
    seqF l d i ∈ trees n := by
  unfold seqF
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i - 1]? with
  | none => exact h d List.mem_cons_self
  | some a => exact h a (List.mem_cons_of_mem _ (List.mem_of_getElem? hi))

/-! ### Kernel computations -/

theorem frontier_one : frontier 1 0 = [] := by decide +kernel

theorem frontier_two : frontier 2 1 = [] := by decide +kernel

theorem frontier_three : frontier 3 2 = [] := by decide +kernel

/-- The frontiers for `n = 4` have sizes `1, 60, 528, 48, 0`; checking this takes ≈ 15 s in
the kernel. -/
theorem frontier_four : frontier 4 4 = [] := by decide +kernel

end FrontierSearch

open FrontierSearch

/-- `t*(𝒯₁) = 0`. -/
theorem advBroadcastTime_trees_one : advBroadcastTime (treesWithLoops 1) = 0 :=
  Nat.le_zero.1 (advBroadcastTime_le_of_frontier 1 frontier_one)

/-- `t*(𝒯₂) = 1`. -/
theorem advBroadcastTime_trees_two : advBroadcastTime (treesWithLoops 2) = 1 :=
  le_antisymm (advBroadcastTime_le_of_frontier 2 frontier_two)
    (le_advBroadcastTime_of_seq 2 frontier_two (seqF [] 13) (seqF_mem 2 (by decide +kernel))
      (by decide +kernel))

/-- `t*(𝒯₃) = 2`: a path rooted at an endpoint does not broadcast in one round. -/
theorem advBroadcastTime_trees_three : advBroadcastTime (treesWithLoops 3) = 2 :=
  le_antisymm (advBroadcastTime_le_of_frontier 3 frontier_three)
    (le_advBroadcastTime_of_seq 3 frontier_three (seqF [] 409) (seqF_mem 3 (by decide +kernel))
      (by decide +kernel))

/-- `t*(𝒯₄) = 4`. -/
theorem advBroadcastTime_trees_four : advBroadcastTime (treesWithLoops 4) = 4 :=
  le_antisymm (advBroadcastTime_le_of_frontier 4 frontier_four)
    (le_advBroadcastTime_of_seq 4 frontier_four (seqF [50737, 54307, 40033] 50737)
      (seqF_mem 4 (by decide +kernel)) (by decide +kernel))

end DynamicRootedTrees
