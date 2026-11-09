import Papers.PODC2012.OptimismConcurrency.ListSet

/-!
# Sequential correctness of `LL` (Algorithm 2)

The memory `m : Mem` *represents* the set `q` (`Rep m q`) if, starting from `head`, the `next`
pointers lead through nodes with keys `-∞, z₁, …, zₖ` to a `+∞` node, where
`z₁ < ⋯ < zₖ` and `q = {z₁, …, zₖ}` (`Chain m [z₁, …, zₖ]`). Unreachable garbage is allowed.

`LLI zs o m s` is the invariant of a solo run of the operation `o` of `LL` started from a memory
representing the sorted list `zs`: `s` is the control state, `m` the current memory. We show
* `LLI.start`: it holds initially;
* `LLI.read`, `LLI.write`, `LLI.alloc`: it is preserved by every action of `LL` (a read of an
  allocated location; a write; a write of a new node to an unallocated location), and every action
  strictly decreases `rank`;
* `LLI.done`: when the operation returns `r`, the memory represents `(setδ q o).1` and
  `r = (setδ q o).2` (`q = zs.toFinset`);
* `LLI.act_read`, `LLI.act_write`: reads and writes only access allocated locations;
* `LLI.readOnly`: if the set is not modified by `o` (`(setδ q o).1 = q`), `LL` performs no
  write;
* `soloStep_correct`: a solo run from a chain representing `q` returning `r` leaves a chain
  representing `(setδ q o).1` and `r = (setδ q o).2`; `soloSteps_le`: a solo run takes at most
  `q.card + 4` actions.
-/

namespace Podc.OptimismConcurrency

/-! ## Order on keys -/

/-- Keys embedded in `WithBot (WithTop ℤ)`. -/
def Key.toW : Key → WithBot (WithTop ℤ)
  | .ninf => ⊥
  | .fin z => ((z : WithTop ℤ) : WithBot (WithTop ℤ))
  | .pinf => ((⊤ : WithTop ℤ) : WithBot (WithTop ℤ))

lemma Key.toW_injective : Function.Injective Key.toW := by
  intro a b h
  cases a <;> cases b <;> simp_all [Key.toW]

instance Key.linearOrder : LinearOrder Key := LinearOrder.lift' Key.toW Key.toW_injective

lemma Key.lt_iff (a b : Key) : a < b ↔ a.toW < b.toW := Iff.rfl

@[simp] lemma Key.fin_lt_fin {a b : ℤ} : Key.fin a < Key.fin b ↔ a < b := by
  simp [Key.lt_iff, Key.toW]

@[simp] lemma Key.ninf_lt_fin (a : ℤ) : Key.ninf < Key.fin a := by
  simp [Key.lt_iff, Key.toW, WithBot.bot_lt_coe]

@[simp] lemma Key.fin_lt_pinf (a : ℤ) : Key.fin a < Key.pinf := by
  simp only [Key.lt_iff, Key.toW, WithBot.coe_lt_coe]; exact WithTop.coe_lt_top a

@[simp] lemma Key.ninf_lt_pinf : Key.ninf < Key.pinf := by
  simp [Key.lt_iff, Key.toW]

@[simp] lemma Key.not_pinf_lt (a : Key) : ¬ Key.pinf < a := by
  cases a <;> simp [Key.lt_iff, Key.toW]

@[simp] lemma Key.not_lt_ninf (a : Key) : ¬ a < Key.ninf := by
  cases a <;> simp [Key.lt_iff, Key.toW]

lemma Key.ltZ_iff (k : Key) (v : ℤ) : k.ltZ v = true ↔ k < .fin v := by
  cases k <;> simp [Key.ltZ]

/-! ## Chains in memory -/

/-- `Seg m a ks b`: starting at location `a`, the nodes carry the keys `ks` (in this order) and
the last of them points to `b` (`a = b` if `ks = []`). -/
def Seg (m : Mem) : Loc → List Key → Loc → Prop
  | a, [], b => a = b
  | a, k :: ks, b => ∃ a', m a = some ⟨k, a'⟩ ∧ Seg m a' ks b

/-- From `a` on, nodes with the keys `zs`, then a `+∞` node. -/
def SufFrom (m : Mem) (a : Loc) (zs : List ℤ) : Prop :=
  ∃ b c, Seg m a (zs.map .fin) b ∧ m b = some ⟨.pinf, c⟩

/-- `m` contains the list `head → z₁ → ⋯ → zₖ → (+∞)` for `zs = [z₁, …, zₖ]`. -/
def Chain (m : Mem) (zs : List ℤ) : Prop :=
  ∃ b c, Seg m headL (.ninf :: zs.map .fin) b ∧ m b = some ⟨.pinf, c⟩

/-- `m` represents the set `q`: it contains a sorted list with the elements of `q`. -/
def Rep (m : Mem) (q : Finset ℤ) : Prop :=
  ∃ zs : List ℤ, zs.Pairwise (· < ·) ∧ zs.toFinset = q ∧ Chain m zs

/-- The node `prev` stored at `old` is the last node of the prefix `head → pre` of the list. -/
def PrefixTo (m : Mem) (pre : List ℤ) (old : Loc) (prev : NodeV) : Prop :=
  ∃ ks, ks ++ [prev.key] = .ninf :: pre.map .fin ∧ Seg m headL ks old ∧ m old = some prev

lemma Seg.append {m : Mem} {a c : Loc} {ks₁ ks₂ : List Key} :
    Seg m a (ks₁ ++ ks₂) c ↔ ∃ b, Seg m a ks₁ b ∧ Seg m b ks₂ c := by
  induction ks₁ generalizing a with
  | nil => simp [Seg]
  | cons k ks₁ ih =>
    simp only [List.cons_append, Seg, ih]
    constructor
    · rintro ⟨a', h, b, h1, h2⟩; exact ⟨b, ⟨a', h, h1⟩, h2⟩
    · rintro ⟨b, ⟨a', h, h1⟩, h2⟩; exact ⟨a', h, b, h1, h2⟩

@[simp] lemma Seg.single {m : Mem} {a b : Loc} {k : Key} :
    Seg m a [k] b ↔ m a = some ⟨k, b⟩ := by
  simp [Seg]

/-- Frame: updating a location whose current node carries a key not in `ks`. -/
lemma Seg.update {m : Mem} {a b y : Loc} {ks : List Key} (h : Seg m a ks b) (w : Option NodeV)
    (hy : ∀ n, m y = some n → n.key ∉ ks) : Seg (Function.update m y w) a ks b := by
  induction ks generalizing a with
  | nil => exact h
  | cons k ks ih =>
    obtain ⟨a', ha, h'⟩ := h
    refine ⟨a', ?_, ih h' (fun n hn hk => hy n hn (List.mem_cons_of_mem _ hk))⟩
    have hay : a ≠ y := by
      rintro rfl; exact hy _ ha (by simp)
    rw [Function.update_of_ne hay]; exact ha

lemma SufFrom.update {m : Mem} {a y : Loc} {zs : List ℤ} (h : SufFrom m a zs) (w : Option NodeV)
    (hy : ∀ n, m y = some n → n.key ∉ zs.map .fin ∧ n.key ≠ .pinf) :
    SufFrom (Function.update m y w) a zs := by
  obtain ⟨b, c, hs, hb⟩ := h
  refine ⟨b, c, hs.update w (fun n hn => (hy n hn).1), ?_⟩
  have hby : b ≠ y := by rintro rfl; exact (hy _ hb).2 rfl
  rw [Function.update_of_ne hby]; exact hb

lemma PrefixTo.update {m : Mem} {pre : List ℤ} {old y : Loc} {prev : NodeV}
    (h : PrefixTo m pre old prev) (w : Option NodeV)
    (hy : ∀ n, m y = some n → n.key ∉ (.ninf :: pre.map .fin : List Key)) :
    PrefixTo (Function.update m y w) pre old prev := by
  obtain ⟨ks, hks, hs, hold⟩ := h
  refine ⟨ks, hks, hs.update w (fun n hn hk => hy n hn (by rw [← hks]; simp [hk])), ?_⟩
  have : old ≠ y := by
    rintro rfl; exact hy _ hold (by rw [← hks]; simp)
  rw [Function.update_of_ne this]; exact hold

lemma chain_of_prefix_suf {m : Mem} {pre suf : List ℤ} {old : Loc} {prev : NodeV}
    (hp : PrefixTo m pre old prev) (hs : SufFrom m prev.next suf) : Chain m (pre ++ suf) := by
  obtain ⟨ks, hks, hseg, hold⟩ := hp
  obtain ⟨b, c, hsuf, hb⟩ := hs
  refine ⟨b, c, ?_, hb⟩
  have : (Key.ninf :: (pre ++ suf).map Key.fin) = ks ++ [prev.key] ++ suf.map .fin := by
    rw [hks]; simp
  rw [this, Seg.append]
  exact ⟨prev.next, Seg.append.2 ⟨old, hseg, by simp [hold]⟩, hsuf⟩

/-! ## Sortedness facts -/

lemma keys_pairwise {zs : List ℤ} (h : zs.Pairwise (· < ·)) :
    (Key.ninf :: zs.map .fin).Pairwise (· < ·) := by
  refine List.pairwise_cons.2 ⟨by simp, ?_⟩
  exact List.pairwise_map.2 (h.imp (fun hab => by simpa using hab))

/-- Keys of the prefix are smaller than every key of the suffix. -/
lemma key_lt_of_pre {pre suf : List ℤ} (h : (pre ++ suf).Pairwise (· < ·)) {k : Key}
    (hk : k ∈ (Key.ninf :: pre.map .fin : List Key)) {z : ℤ} (hz : z ∈ suf) : k < .fin z := by
  simp only [List.mem_cons, List.mem_map] at hk
  rcases hk with rfl | ⟨w, hw, rfl⟩
  · simp
  · exact Key.fin_lt_fin.2 ((List.pairwise_append.1 h).2.2 w hw z hz)

lemma PrefixTo.key_mem {m : Mem} {pre : List ℤ} {old : Loc} {prev : NodeV}
    (h : PrefixTo m pre old prev) : prev.key ∈ (Key.ninf :: pre.map .fin : List Key) := by
  obtain ⟨ks, hks, -, -⟩ := h
  rw [← hks]; simp

lemma key_not_mem_init {pre : List ℤ} {k : Key} (hpre : pre.Pairwise (· < ·)) :
    ∀ ks, ks ++ [k] = .ninf :: pre.map .fin → k ∉ ks := by
  intro ks hks hk
  have hp := keys_pairwise hpre
  rw [← hks, List.pairwise_append] at hp
  exact lt_irrefl _ (hp.2.2 _ hk _ (by simp))

/-! ## The invariant of a solo run -/

/-- Invariant of a solo run of the operation `o` of `LL` started from a memory containing the
sorted list `zs`; `m` is the current memory, the argument the current control state. -/
def LLI (zs : List ℤ) (o : SetOp) (m : Mem) : St → Prop
  | .start => Chain m zs
  | .trav old prev => ∃ pre suf, zs = pre ++ suf ∧ (∀ z ∈ pre, z < o.arg) ∧
      PrefixTo m pre old prev ∧ SufFrom m prev.next suf
  | .alloc old prev n => ∃ v pre suf, o = .insert v ∧ n = ⟨.fin v, prev.next⟩ ∧ zs = pre ++ suf ∧
      (∀ z ∈ pre, z < v) ∧ (∀ z ∈ suf, v < z) ∧ PrefixTo m pre old prev ∧
      SufFrom m prev.next suf
  | .wr old n r => (setδ zs.toFinset o).1 ≠ zs.toFinset ∧ ∃ pre suf, (pre ++ suf).Pairwise (· < ·) ∧
      (pre ++ suf).toFinset = (setδ zs.toFinset o).1 ∧ r = (setδ zs.toFinset o).2 ∧
      ∃ prev, PrefixTo m pre old prev ∧ n.key = prev.key ∧ SufFrom m n.next suf
  | .done r => Rep m (setδ zs.toFinset o).1 ∧ r = (setδ zs.toFinset o).2

/-- A bound on the number of remaining actions of `LL` (for a run from a list representing
`q`). -/
def rank (q : Finset ℤ) : St → ℕ
  | .start => q.card + 4
  | .trav _ prev => (q.filter (fun z => prev.key.ltZ z)).card + 3
  | .alloc .. => 2
  | .wr .. => 1
  | .done _ => 0

lemma LLI.start {zs : List ℤ} {o : SetOp} {m : Mem} (h : Chain m zs) : LLI zs o m .start := h

lemma LLI.done {zs : List ℤ} {o : SetOp} {m : Mem} {r : Bool} (h : LLI zs o m (.done r)) :
    Rep m (setδ zs.toFinset o).1 ∧ r = (setδ zs.toFinset o).2 := h

lemma rank_trav_le (q : Finset ℤ) (old : Loc) (prev : NodeV) :
    rank q (.trav old prev) ≤ q.card + 3 := by
  simp only [rank]; have := Finset.card_filter_le q (fun z => prev.key.ltZ z = true); omega

/-- `LL` reads only allocated locations. -/
lemma LLI.act_read {zs : List ℤ} {o : SetOp} {m : Mem} {s : St} {y : Loc}
    (h : LLI zs o m s) (ha : act o s = .read y) : ∃ n, m y = some n := by
  cases s with
  | start =>
    simp only [act, Act.read.injEq] at ha; subst ha
    obtain ⟨b, c, ⟨a', h1, -⟩, -⟩ := h; exact ⟨_, h1⟩
  | trav old prev =>
    simp only [act, Act.read.injEq] at ha; subst ha
    obtain ⟨pre, suf, -, -, -, b, c, hs, hb⟩ := h
    cases suf with
    | nil => simp only [List.map_nil, Seg] at hs; rw [hs]; exact ⟨_, hb⟩
    | cons z suf => obtain ⟨a', h1, -⟩ := hs; exact ⟨_, h1⟩
  | alloc => simp [act] at ha
  | wr => simp [act] at ha
  | done => simp [act] at ha

/-- `LL` writes only to allocated locations (except for `new-node`). -/
lemma LLI.act_write {zs : List ℤ} {o : SetOp} {m : Mem} {s : St} {y : Loc} {n : NodeV}
    (h : LLI zs o m s) (ha : act o s = .write y n) : ∃ n', m y = some n' := by
  cases s with
  | wr old n r =>
    simp only [act, Act.write.injEq] at ha; obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨-, pre, suf, -, -, -, prev, ⟨ks, -, -, hold⟩, -⟩ := h
    exact ⟨_, hold⟩
  | _ => simp [act] at ha

/-- If `o` does not modify the set, `LL` performs no write. -/
lemma LLI.readOnly {zs : List ℤ} {o : SetOp} {m : Mem} {s : St}
    (h : LLI zs o m s) (ha : (∃ y n, act o s = .write y n) ∨ (∃ n, act o s = .alloc n)) :
    (setδ zs.toFinset o).1 ≠ zs.toFinset := by
  cases s with
  | alloc old prev n =>
    obtain ⟨v, pre, suf, rfl, -, rfl, hpre, hsuf, -⟩ := h
    simp only [setδ, ne_eq, Finset.insert_eq_self, List.mem_toFinset, List.mem_append, not_or]
    exact ⟨fun hv => lt_irrefl v (hpre v hv), fun hv => lt_irrefl v (hsuf v hv)⟩
  | wr old n r => exact h.1
  | _ => simp [act] at ha

lemma toFinset_erase_of_not_mem {l : List ℤ} {v : ℤ} (h : v ∉ l) :
    l.toFinset.erase v = l.toFinset := by
  simpa using h

/-- Reads preserve the invariant and decrease the rank. -/
lemma LLI.read {zs : List ℤ} (hzs : zs.Pairwise (· < ·)) {o : SetOp} {m : Mem} {s : St} {y : Loc}
    {n : NodeV} (h : LLI zs o m s) (ha : act o s = .read y) (hy : m y = some n) :
    LLI zs o m (onRead o s y n) ∧ rank zs.toFinset (onRead o s y n) < rank zs.toFinset s := by
  cases s with
  | start =>
    simp only [act, Act.read.injEq] at ha; subst ha
    obtain ⟨b, c, ⟨a', h1, hs⟩, hb⟩ := h
    rw [hy] at h1; cases h1
    refine ⟨⟨[], zs, rfl, by simp, ⟨[], rfl, rfl, hy⟩, b, c, hs, hb⟩, ?_⟩
    have := rank_trav_le zs.toFinset headL ⟨.ninf, a'⟩
    simp only [onRead, rank] at this ⊢; omega
  | trav old prev =>
    simp only [act, Act.read.injEq] at ha; subst ha
    obtain ⟨pre, suf, rfl, hpre, hP, b, c, hs, hb⟩ := h
    have hrank : ∀ s', rank (pre ++ suf).toFinset s' ≤ 2 →
        rank (pre ++ suf).toFinset s' < rank (pre ++ suf).toFinset (.trav old prev) := by
      intro s' h'
      have : rank (pre ++ suf).toFinset (.trav old prev) =
        ((pre ++ suf).toFinset.filter (fun z => prev.key.ltZ z)).card + 3 := rfl
      omega
    have hchain : Chain m (pre ++ suf) := chain_of_prefix_suf hP ⟨b, c, hs, hb⟩
    have hrep : Rep m (pre ++ suf).toFinset := ⟨_, hzs, rfl, hchain⟩
    cases suf with
    | nil =>
      simp only [List.map_nil, Seg] at hs; subst hs
      rw [hb] at hy; cases hy
      have hv : o.arg ∉ pre ++ [] := fun hv => lt_irrefl _ (hpre _ (by simpa using hv))
      cases o with
      | contains v =>
        simp only [SetOp.arg] at hv
        refine ⟨⟨by simpa [setδ] using hrep, by simpa [setδ] using hv⟩,
          hrank _ (by simp [onRead, finish, Key.ltZ, rank])⟩
      | insert v =>
        simp only [SetOp.arg] at hpre
        refine ⟨⟨v, pre, [], rfl, rfl, rfl, hpre, by simp, hP, prev.next, c, rfl, hb⟩,
          hrank _ (by simp [onRead, finish, Key.ltZ, rank])⟩
      | remove v =>
        have hv' : v ∉ pre ++ [] := hv
        refine ⟨⟨?_, by simp only [SetOp.arg] at hv; simpa [setδ] using hv⟩,
          hrank _ (by simp [onRead, finish, Key.ltZ, rank])⟩
        simp only [setδ]
        rwa [toFinset_erase_of_not_mem hv']
    | cons z suf =>
      obtain ⟨a', h1, hs⟩ := hs
      rw [h1] at hy; cases hy
      have hzk : prev.key < .fin z := key_lt_of_pre hzs hP.key_mem (by simp)
      by_cases hzv : z < o.arg
      · have hlt : (Key.fin z).ltZ o.arg = true := by simpa [Key.ltZ] using hzv
        simp only [onRead, hlt, ↓reduceIte]
        refine ⟨⟨pre ++ [z], suf, by simp, ?_, ?_, b, c, hs, hb⟩, ?_⟩
        · intro w hw; simp only [List.mem_append, List.mem_singleton] at hw
          rcases hw with hw | rfl
          · exact hpre w hw
          · exact hzv
        · obtain ⟨ks, hks, hseg, hold⟩ := hP
          refine ⟨ks ++ [prev.key], ?_, Seg.append.2 ⟨old, hseg, ?_⟩, h1⟩
          · simp [hks]
          · simp [hold]
        · simp only [rank, add_lt_add_iff_right]
          apply Finset.card_lt_card
          refine (Finset.ssubset_iff_of_subset ?_).2 ⟨z, ?_, ?_⟩
          · intro w hw
            simp only [Finset.mem_filter, Key.ltZ_iff] at hw ⊢
            exact ⟨hw.1, hzk.trans hw.2⟩
          · simp [Key.ltZ_iff, hzk]
          · simp [Key.ltZ]
      · have hlt : (Key.fin z).ltZ o.arg = false := by simpa [Key.ltZ] using hzv
        have hsort := (List.pairwise_append.1 hzs)
        have hsuf : ∀ w ∈ suf, z < w := (List.pairwise_cons.1 hsort.2.1).1
        have hnot : o.arg ∉ pre := fun hv => lt_irrefl _ (hpre _ hv)
        have hmem : o.arg ∈ pre ++ z :: suf ↔ z = o.arg := by
          simp only [List.mem_append, hnot, false_or, List.mem_cons]
          constructor
          · rintro (h | h)
            · exact h.symm
            · exact absurd (hsuf _ h) (by omega)
          · intro h; exact Or.inl h.symm
        simp only [onRead, hlt, Bool.false_eq_true, ↓reduceIte]
        cases o with
        | contains v =>
          simp only [SetOp.arg] at hmem
          refine ⟨⟨by simpa [setδ] using hrep, ?_⟩, hrank _ (by simp [finish, rank])⟩
          simp only [setδ, List.mem_toFinset, hmem]; simp
        | insert v =>
          simp only [SetOp.arg] at hmem hzv
          by_cases hzv' : z = v
          · subst hzv'
            simp only [finish, ↓reduceIte]
            refine ⟨⟨?_, by simp [setδ]⟩, hrank _ (by simp [rank])⟩
            simpa [setδ] using hrep
          · simp only [finish, Key.fin.injEq, hzv', ↓reduceIte]
            refine ⟨⟨v, pre, z :: suf, rfl, rfl, rfl, hpre, ?_, hP, b, c, ⟨a', h1, hs⟩, hb⟩,
              hrank _ (by simp [rank])⟩
            intro w hw; simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · omega
            · exact lt_of_lt_of_le (by omega) (hsuf w hw).le
        | remove v =>
          simp only [SetOp.arg] at hmem hzv hnot
          by_cases hzv' : z = v
          · subst hzv'
            simp only [finish, ↓reduceIte]
            refine ⟨⟨?_, pre, suf, ?_, ?_, by simp [setδ], prev, hP, rfl, b, c, hs, hb⟩,
              hrank _ (by simp [rank])⟩
            · intro h
              have := congrArg (z ∈ ·) h
              simp [setδ] at this
            · exact List.Pairwise.sublist (by simp) hzs
            · have hns : z ∉ suf := fun h => lt_irrefl _ (hsuf z h)
              ext w; simp only [setδ, Finset.mem_erase, List.mem_toFinset, List.mem_append,
                List.mem_cons]
              constructor
              · rintro (h | h)
                · exact ⟨fun e => hnot (e ▸ h), Or.inl h⟩
                · exact ⟨fun e => hns (e ▸ h), Or.inr (Or.inr h)⟩
              · rintro ⟨hne, h | h | h⟩
                · exact Or.inl h
                · exact absurd h hne
                · exact Or.inr h
          · simp only [finish, Key.fin.injEq, hzv', ↓reduceIte]
            refine ⟨⟨?_, by simp only [setδ, List.mem_toFinset, hmem]; simp [hzv']⟩,
              hrank _ (by simp [rank])⟩
            have : v ∉ pre ++ z :: suf := by rw [hmem]; exact hzv'
            simp only [setδ]; rwa [toFinset_erase_of_not_mem this]
  | alloc => simp [act] at ha
  | wr => simp [act] at ha
  | done => simp [act] at ha

/-- `new-node` (a write of the new node to an unallocated location) preserves the invariant and
decreases the rank. -/
lemma LLI.alloc {zs : List ℤ} (hzs : zs.Pairwise (· < ·)) {o : SetOp} {m : Mem} {s : St}
    {y : Loc} {n : NodeV} (h : LLI zs o m s) (ha : act o s = .alloc n) (hy : m y = none) :
    LLI zs o (Function.update m y (some n)) (onWrite s y) ∧
      rank zs.toFinset (onWrite s y) < rank zs.toFinset s := by
  cases s with
  | alloc old prev n' =>
    simp only [act, Act.alloc.injEq] at ha; subst ha
    obtain ⟨v, pre, suf, rfl, rfl, rfl, hpre, hsuf, hP, b, c, hs, hb⟩ := h
    have hnone : ∀ n₀, m y = some n₀ → False := by simp [hy]
    refine ⟨⟨?_, pre, v :: suf, ?_, ?_, ?_, prev, hP.update _ (fun n₀ h => (hnone n₀ h).elim),
      rfl, b, c, ?_, ?_⟩, by simp [onWrite, rank]⟩
    · simp only [setδ, ne_eq, Finset.insert_eq_self, List.mem_toFinset, List.mem_append, not_or]
      exact ⟨fun hv => lt_irrefl v (hpre v hv), fun hv => lt_irrefl v (hsuf v hv)⟩
    · rw [List.pairwise_append] at hzs ⊢
      refine ⟨hzs.1, List.pairwise_cons.2 ⟨hsuf, hzs.2.1⟩, ?_⟩
      intro a ha b hb; simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hpre a ha
      · exact hzs.2.2 a ha b hb
    · ext w; simp [setδ]
    · simp only [setδ, List.mem_toFinset, List.mem_append, not_or]
      exact (decide_eq_true ⟨fun hv => lt_irrefl v (hpre v hv),
        fun hv => lt_irrefl v (hsuf v hv)⟩).symm
    · refine ⟨prev.next, by simp, ?_⟩
      exact hs.update _ (fun n₀ h => (hnone n₀ h).elim)
    · have : b ≠ y := by rintro rfl; simp [hy] at hb
      rw [Function.update_of_ne this]; exact hb
  | _ => simp [act] at ha

/-- Writes preserve the invariant and decrease the rank. -/
lemma LLI.write {zs : List ℤ} {o : SetOp} {m : Mem} {s : St}
    {y : Loc} {n : NodeV} (h : LLI zs o m s) (ha : act o s = .write y n) :
    LLI zs o (Function.update m y (some n)) (onWrite s y) ∧
      rank zs.toFinset (onWrite s y) < rank zs.toFinset s := by
  cases s with
  | wr old n' r =>
    simp only [act, Act.write.injEq] at ha; obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨-, pre, suf, hsort, hset, hr, prev, ⟨ks, hks, hseg, hold⟩, hkey, b, c, hs, hb⟩ := h
    refine ⟨⟨⟨pre ++ suf, hsort, hset, ?_⟩, hr⟩, by simp [onWrite, rank]⟩
    have hpre : pre.Pairwise (· < ·) := List.Pairwise.sublist (by simp) hsort
    have hmem : prev.key ∈ (Key.ninf :: pre.map .fin : List Key) := by rw [← hks]; simp
    have hP' : PrefixTo (Function.update m old (some n')) pre old n' := by
      refine ⟨ks, by rw [hkey]; exact hks, ?_, by simp⟩
      refine hseg.update _ (fun n₀ h₀ => ?_)
      rw [hold] at h₀; cases h₀
      exact key_not_mem_init hpre ks hks
    refine chain_of_prefix_suf hP' ⟨b, c, ?_, ?_⟩
    · refine hs.update _ (fun n₀ h₀ hk => ?_)
      rw [hold] at h₀; cases h₀
      obtain ⟨z, hz, hz'⟩ := List.mem_map.1 hk
      exact lt_irrefl _ (hz' ▸ key_lt_of_pre hsort hmem hz)
    · have : b ≠ old := by
        rintro rfl; rw [hold] at hb; cases hb
        simp at hmem
      rw [Function.update_of_ne this]; exact hb
  | _ => simp [act] at ha

/-! ## Solo runs -/

/-- One action of a solo run of the operation `o` of `LL`: a read of an allocated location, a
write, or `new-node` (a write to an unallocated location). -/
inductive SoloStep (o : SetOp) : Mem × St → Mem × St → Prop
  | read {m : Mem} {s : St} {y : Loc} {n : NodeV} :
      act o s = .read y → m y = some n → SoloStep o (m, s) (m, onRead o s y n)
  | write {m : Mem} {s : St} {y : Loc} {n : NodeV} :
      act o s = .write y n → SoloStep o (m, s) (Function.update m y (some n), onWrite s y)
  | alloc {m : Mem} {s : St} {y : Loc} {n : NodeV} :
      act o s = .alloc n → m y = none →
        SoloStep o (m, s) (Function.update m y (some n), onWrite s y)

/-- Every action preserves the invariant and decreases the rank. -/
lemma LLI.soloStep {zs : List ℤ} (hzs : zs.Pairwise (· < ·)) {o : SetOp} {c c' : Mem × St}
    (h : LLI zs o c.1 c.2) (hc : SoloStep o c c') :
    LLI zs o c'.1 c'.2 ∧ rank zs.toFinset c'.2 < rank zs.toFinset c.2 := by
  cases hc with
  | read ha hy => exact h.read hzs ha hy
  | write ha => exact h.write ha
  | alloc ha hy => exact h.alloc hzs ha hy

/-- Progress: before returning, `LL` can always take a step (given an unallocated location for
`new-node`). -/
lemma LLI.progress {zs : List ℤ} {o : SetOp} {m : Mem} {s : St} (h : LLI zs o m s)
    (hs : ∀ r, s ≠ .done r) (hfresh : ∃ y, m y = none) : ∃ c', SoloStep o (m, s) c' := by
  cases hact : act o s with
  | read y => obtain ⟨n, hn⟩ := h.act_read hact; exact ⟨_, .read hact hn⟩
  | write y n => exact ⟨_, .write hact⟩
  | alloc n => obtain ⟨y, hy⟩ := hfresh; exact ⟨_, .alloc hact hy⟩
  | ret r => cases s <;> simp [act] at hact; exact absurd rfl (hs _)

lemma LLI.soloSteps {zs : List ℤ} (hzs : zs.Pairwise (· < ·)) {o : SetOp} {c c' : Mem × St}
    (h : LLI zs o c.1 c.2) (hc : Relation.ReflTransGen (SoloStep o) c c') : LLI zs o c'.1 c'.2 := by
  induction hc with
  | refl => exact h
  | tail _ hst ih => exact (ih.soloStep hzs hst).1

/-- **Sequential correctness of `LL`.** A solo run of `o` from a memory containing the sorted
list `zs` that returns `r` leaves a memory representing `(setδ q o).1`, and
`r = (setδ q o).2`, where `q = zs.toFinset`. -/
theorem soloRun_correct {zs : List ℤ} (hzs : zs.Pairwise (· < ·)) {o : SetOp} {m m' : Mem}
    {r : Bool} (hm : Chain m zs)
    (hrun : Relation.ReflTransGen (SoloStep o) (m, .start) (m', .done r)) :
    Rep m' (setδ zs.toFinset o).1 ∧ r = (setδ zs.toFinset o).2 :=
  LLI.done (LLI.soloSteps (c := (m, .start)) hzs (LLI.start hm) hrun)

/-- **Termination of `LL`.** A solo run of `o` from a memory containing the sorted list `zs`
takes at most `|zs| + 4` actions. -/
theorem soloRun_length_le {zs : List ℤ} (hzs : zs.Pairwise (· < ·)) {o : SetOp} {m : Mem}
    (hm : Chain m zs) (l : List (Mem × St)) (hl : List.IsChain (SoloStep o) ((m, .start) :: l)) :
    l.length ≤ zs.length + 4 := by
  suffices ∀ (l : List (Mem × St)) (c : Mem × St), LLI zs o c.1 c.2 →
      List.IsChain (SoloStep o) (c :: l) → l.length ≤ rank zs.toFinset c.2 by
    have := this l (m, .start) (LLI.start hm) hl
    simp only [rank] at this
    have hcard := List.toFinset_card_le zs
    omega
  intro l
  induction l with
  | nil => intro _ _ _; simp
  | cons c' l ih =>
    intro c h hl
    rw [List.isChain_cons_cons] at hl
    have := h.soloStep hzs hl.1
    have := ih c' this.1 hl.2
    simp only [List.length_cons]; omega

end Podc.OptimismConcurrency
