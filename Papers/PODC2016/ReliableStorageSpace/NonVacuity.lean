import Papers.PODC2016.ReliableStorageSpace.LowerBound

/-!
# Non-vacuity of Theorem 2: a lock-free, atomic register in the black-box storage model

The hypotheses of `Alg.theorem2` (lock-freedom and weak regularity) are satisfiable together: with
a single reliable base object (`f = 0`) holding the block of the last write, the trivial algorithm
`atomicAlg`

* **write `(c, k)`:** one RMW "put block `((c, k), .one)`" (the object is overwritten with it), wait for
  the acknowledgement, return;
* **read:** one RMW "get" (the response carries the object's block), wait for the response, return the
  decoding of the block received (`v₀` if none);

is lock-free with `f = 0` (`atomicAlg_lockFree`) and weakly regular (`atomicAlg_weakRegular`). The only
block kind `Kind.one` has `|V|` bits and the code is injective (`dec_encV`). `theorem2_atomicAlg`
instantiates `Alg.theorem2` on it (3 clients, Boolean values, `S = 2`).

The weak regularity proof uses a ghost history `G` of the RMWs that took effect, in order, with the
length `tau` of the history at the time each took effect (`Good`). The linearization of a read `rd` is
`G` restricted to the writes and `rd`.
-/

noncomputable section

namespace Podc.ReliableStorageSpace.NonVacuity

open Finset Classical Podc.ReliableStorageSpace

variable {C V : Type} [Fintype V]

/-- The single block kind. (Deliberately without a `DecidableEq` instance: the model's finsets of
blocks use classical decidability, and a canonical instance would clash with it.) -/
inductive Kind
  | one

/-- The RMW of operation `(c, k)`: a write puts its block, a read (`none`) gets the object's block. -/
def rmwOf (c : C) (k : ℕ) : Op → Option (Blk C Kind)
  | .write => some ((c, k), .one)
  | .read => none

/-- The code: a value is stored as its index in `Fin |V|`, in `|V|` bits. -/
def encV (v : V) : Fin (2 ^ Fintype.card V) :=
  ⟨Fintype.equivFin V v, lt_trans (Fintype.equivFin V v).2 Nat.lt_two_pow_self⟩

/-- Decoding (`v₀` on invalid codewords). -/
def dec (v₀ : V) (x : Fin (2 ^ Fintype.card V)) : V :=
  if h : (x : ℕ) < Fintype.card V then (Fintype.equivFin V).symm ⟨x, h⟩ else v₀

theorem dec_encV (v₀ v : V) : dec v₀ (encV v) = v := by
  simp [dec, encV]

/-- The output of a read holding the block `o`. -/
def rdf (v₀ : V) (o : Option (Blk C Kind)) (g : (b : Blk C Kind) → Fin (2 ^ Fintype.card V)) : V :=
  match o with
  | some b => dec v₀ (g b)
  | none => v₀

/-- The trivial atomic register over one base object. Local state: (block received, phase), where
phase `0` = about to trigger the RMW, `1` = waiting for its response, `2` = about to return. -/
@[reducible] def atomicAlg (v₀ : V) : Alg C Unit Kind V where
  L := Option (Blk C Kind) × ℕ
  O := Option (Blk C Kind)
  R := Option (Blk C Kind)
  Res := Option (Blk C Kind)
  linit _ := (none, 0)
  oinit _ := none
  invoke _ _ _ _ := (none, 0)
  act c k op l :=
    if l.2 = 0 then .trigger () (rmwOf c k op) (l.1, 1)
    else if l.2 = 2 then .ret (none, 0) else .idle
  apply r o :=
    match r with
    | some b => (some b, none)
    | none => (o, o)
  recv _ _ _ res := (res, 2)
  sz _ := Fintype.card V
  enc _ v := encV v
  rdout _ l g := rdf v₀ l.1 g
  lblk l := l.1.toFinset
  oblk o := o.toFinset
  rblk r := r.toFinset
  resblk r := r.toFinset
  sz_pos _ := Fintype.card_pos_iff.2 ⟨v₀⟩
  linit_blk _ := rfl
  oinit_blk _ := rfl
  invoke_blk := by intro c k op l b hb; simp at hb
  act_trigger_blk := by
    intro c k op l o r l' h b hb
    split_ifs at h with h0
    · cases h
      rcases Finset.mem_union.1 hb with hb | hb
      · cases op <;> simp [rmwOf] at hb
        subst hb; exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl hb
  act_ret_blk := by
    intro c k op l l' h
    split_ifs at h with h0 h2
    cases h
    simp
  apply_blk := by intro r ob; cases r <;> simp
  recv_blk := by intro c l o res; simp
  rdout_congr := by
    intro c l g g' h
    rcases l with ⟨_ | b, n⟩
    · rfl
    · simp only [rdf]
      rw [h b (by simp)]

/-! ### Basic facts about `atomicAlg` -/

section Facts

variable (v₀ : V)

theorem act_trigger {c : C} {k : ℕ} {op : Op} {l : Option (Blk C Kind) × ℕ} {o : Unit}
    {r : Option (Blk C Kind)} {l' : Option (Blk C Kind) × ℕ}
    (h : (atomicAlg v₀).act c k op l = .trigger o r l') :
    l.2 = 0 ∧ r = rmwOf c k op ∧ l' = (l.1, 1) := by
  simp only [atomicAlg] at h
  split_ifs at h with h0 h2
  cases h
  exact ⟨h0, rfl, rfl⟩

theorem act_ret {c : C} {k : ℕ} {op : Op} {l : Option (Blk C Kind) × ℕ}
    {l' : Option (Blk C Kind) × ℕ}
    (h : (atomicAlg v₀).act c k op l = .ret l') : l.2 = 2 ∧ l' = (none, 0) := by
  simp only [atomicAlg] at h
  split_ifs at h with h0 h2
  cases h
  exact ⟨h2, rfl⟩

theorem act_zero {c : C} {k : ℕ} {op : Op} {l : Option (Blk C Kind) × ℕ} (h : l.2 = 0) :
    (atomicAlg v₀).act c k op l = .trigger () (rmwOf c k op) (l.1, 1) := by
  simp [atomicAlg, h]

theorem act_two {c : C} {k : ℕ} {op : Op} {l : Option (Blk C Kind) × ℕ} (h : l.2 = 2) :
    (atomicAlg v₀).act c k op l = .ret (none, 0) := by
  simp [atomicAlg, h]

end Facts

/-! ### The invariant -/

section Invariant

variable (v₀ : V)

/-- Pending RMWs of client `c`. -/
def pc (X : (atomicAlg (C := C) v₀).Config) (c : C) : List (Pend C Unit (Option (Blk C Kind))) :=
  X.pend.filter (fun p => decide (p.cl = c))

/-- The last write of a ghost history. -/
def lastW (G : List (OpId C × Op)) : Option (OpId C) :=
  ((G.filter (fun e => decide (e.2 = Op.write))).getLast?).map Prod.fst

/-- The block of a write. -/
def blkOf (o : Option (OpId C)) : Option (Blk C Kind) := o.map (fun w => (w, Kind.one))

/-- The invariant of `atomicAlg`, relating a configuration to the ghost history `G` of the operations
whose RMW took effect (in effect order, with their kinds) and the history length `tau x` at the time
the RMW of `x` took effect. -/
structure Good (X : (atomicAlg (C := C) v₀).Config) (G : List (OpId C × Op)) (tau : OpId C → ℕ) :
    Prop where
  none_pc : ∀ c, X.cur c = none → pc v₀ X c = []
  some_ok : ∀ c op, X.cur c = some op →
    ((X.loc c).2 = 0 ∧ pc v₀ X c = [] ∧ (c, X.cnt c) ∉ G.map Prod.fst) ∨
    ((X.loc c).2 = 1 ∧ (∃ m, pc v₀ X c = [⟨c, m, (), rmwOf c (X.cnt c) op⟩]) ∧
      (c, X.cnt c) ∉ G.map Prod.fst) ∨
    ((X.loc c).2 = 2 ∧ pc v₀ X c = [] ∧ ∃ pre rest, G = pre ++ ((c, X.cnt c), op) :: rest ∧
      (op = .read → (X.loc c).1 = blkOf (lastW pre)))
  obj_eq : X.obj () = blkOf (lastW G)
  nodup : (G.map Prod.fst).Nodup
  cur_inv : ∀ c op, X.cur c = some op → Label.inv c (X.cnt c) op ∈ X.hist
  G_inv : ∀ e ∈ G, Label.inv e.1.1 e.1.2 e.2 ∈ X.hist
  inv_uniq : ∀ c k op op', Label.inv c k op ∈ X.hist → Label.inv c k op' ∈ X.hist → op = op'
  inv_cnt : ∀ c k op, Label.inv c k op ∈ X.hist → k < X.cnt c ∨ (k = X.cnt c ∧ X.cur c = some op)
  ret_G : ∀ c k out, Label.ret c k out ∈ X.hist → k < X.cnt c ∧ ∃ op, ((c, k), op) ∈ G
  ret_rd : ∀ c k out, Label.ret c k (some out) ∈ X.hist →
    ∃ pre rest, G = pre ++ ((c, k), Op.read) :: rest ∧ out = rdf v₀ (blkOf (lastW pre))
  sorted : G.Pairwise (fun a b => tau a.1 ≤ tau b.1)
  tau_le : ∀ e ∈ G, tau e.1 ≤ X.hist.length
  tau_ret : ∀ e ∈ G, ∀ i out, X.hist[i]? = some (Label.ret e.1.1 e.1.2 out) → tau e.1 ≤ i
  tau_inv : ∀ e ∈ G, ∀ j op, X.hist[j]? = some (Label.inv e.1.1 e.1.2 op) → j < tau e.1

theorem good_init : Good v₀ (atomicAlg (C := C) v₀).init [] (fun _ => 0) := by
  constructor <;> simp [Alg.init, pc, lastW, blkOf, atomicAlg]

theorem getElem?_concat_some {α : Type*} {l : List α} {a x : α} {i : ℕ}
    (h : (l ++ [a])[i]? = some x) : l[i]? = some x ∨ (i = l.length ∧ a = x) := by
  rcases lt_trichotomy i l.length with hi | rfl | hi
  · left; rwa [List.getElem?_append_left hi] at h
  · right; simpa using h
  · exfalso
    have := (List.getElem?_eq_some_iff.1 h).1
    simp at this; omega

variable {v₀}

theorem Good.not_mem_of_none {X : (atomicAlg (C := C) v₀).Config} {G tau} (h : Good v₀ X G tau)
    {c : C} (hc : X.cur c = none) : (c, X.cnt c) ∉ G.map Prod.fst := by
  intro hm
  obtain ⟨e, he, he1⟩ := List.mem_map.1 hm
  have := h.inv_cnt c (X.cnt c) e.2 (by simpa [he1] using h.G_inv e he)
  simp [hc] at this

theorem good_inv {X : (atomicAlg (C := C) v₀).Config} {G tau} (h : Good v₀ X G tau) {c : C} {op : Op}
    (hc : X.cur c = none) :
    Good v₀ { X with loc := Function.update X.loc c ((atomicAlg v₀).invoke c (X.cnt c) op (X.loc c))
                     cur := Function.update X.cur c (some op)
                     hist := X.hist ++ [.inv c (X.cnt c) op] } G tau := by
  have hG := h.not_mem_of_none hc
  constructor
  · intro c' hc'
    have hne : c' ≠ c := by rintro rfl; simp at hc'
    simp only [Function.update_apply, hne, ite_false] at hc'
    exact h.none_pc c' hc'
  · intro c' op' hc'
    by_cases hne : c' = c
    · subst hne
      simp only [Function.update_self, Option.some.injEq] at hc'
      subst hc'
      left
      exact ⟨by simp [atomicAlg], h.none_pc _ hc, hG⟩
    · simp only [Function.update_apply, hne, ite_false] at hc' ⊢
      exact h.some_ok c' op' hc'
  · exact h.obj_eq
  · exact h.nodup
  · intro c' op' hc'
    by_cases hne : c' = c
    · subst hne
      simp only [Function.update_self, Option.some.injEq] at hc'
      subst hc'; simp
    · simp only [Function.update_apply, hne, ite_false] at hc'
      exact List.mem_append_left _ (h.cur_inv c' op' hc')
  · intro e he; exact List.mem_append_left _ (h.G_inv e he)
  · intro c' k o1 o2 h1 h2
    simp only [List.mem_append, List.mem_singleton, Label.inv.injEq] at h1 h2
    rcases h1 with h1 | ⟨rfl, rfl, rfl⟩ <;> rcases h2 with h2 | ⟨h2c, h2k, rfl⟩
    · exact h.inv_uniq _ _ _ _ h1 h2
    · subst h2c h2k; have := h.inv_cnt _ _ _ h1; simp [hc] at this
    · have := h.inv_cnt _ _ _ h2; simp [hc] at this
    · rfl
  · intro c' k o1 h1
    simp only [List.mem_append, List.mem_singleton, Label.inv.injEq] at h1
    rcases h1 with h1 | ⟨rfl, rfl, rfl⟩
    · rcases h.inv_cnt _ _ _ h1 with h2 | ⟨h2, h3⟩
      · exact Or.inl h2
      · right
        by_cases hne : c' = c
        · subst hne; simp [hc] at h3
        · simp [hne, h2, h3]
    · right; simp
  · intro c' k out h1
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h1
    exact h.ret_G _ _ _ h1
  · intro c' k out h1
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h1
    exact h.ret_rd _ _ _ h1
  · exact h.sorted
  · intro e he; have := h.tau_le e he; simp; omega
  · intro e he i out hi
    rcases getElem?_concat_some hi with hi | ⟨-, hi⟩
    · exact h.tau_ret e he i out hi
    · cases hi
  · intro e he j o hj
    rcases getElem?_concat_some hj with hj | ⟨-, hj⟩
    · exact h.tau_inv e he j o hj
    · simp only [Label.inv.injEq] at hj
      obtain ⟨h1, h2, -⟩ := hj
      exact absurd (List.mem_map.2 ⟨e, he, by subst h1; exact Prod.ext rfl h2.symm⟩) hG

theorem lastW_append_write (G : List (OpId C × Op)) (w : OpId C) :
    lastW (G ++ [(w, Op.write)]) = some w := by
  simp [lastW, List.filter_append]

theorem lastW_append_read (G : List (OpId C × Op)) (w : OpId C) :
    lastW (G ++ [(w, Op.read)]) = lastW G := by
  simp [lastW, List.filter_append]

theorem good_trigger {X : (atomicAlg (C := C) v₀).Config} {G tau} (h : Good v₀ X G tau) {c : C}
    {op : Op} {o : Unit} {r : Option (Blk C Kind)} {l : Option (Blk C Kind) × ℕ}
    (hc : X.cur c = some op) (ha : (atomicAlg v₀).act c (X.cnt c) op (X.loc c) = .trigger o r l) :
    Good v₀ { X with loc := Function.update X.loc c l
                     pend := X.pend ++ [⟨c, X.nrmw c, o, r⟩]
                     nrmw := Function.update X.nrmw c (X.nrmw c + 1)
                     tick := X.tick + 1 } G tau := by
  obtain ⟨h0, rfl, rfl⟩ := act_trigger v₀ ha
  cases o
  have hpc : ∀ c', c' ≠ c → (X.pend ++ [(⟨c, X.nrmw c, (), rmwOf c (X.cnt c) op⟩ :
      Pend C Unit (Option (Blk C Kind)))]).filter
      (fun p : Pend C Unit (Option (Blk C Kind)) => decide (p.cl = c')) = pc v₀ X c' := by
    intro c' hne
    simp [pc, List.filter_append, Ne.symm hne]
  constructor
  · intro c' hc'
    have hne : c' ≠ c := by rintro rfl; simp [hc] at hc'
    exact (hpc c' hne).trans (h.none_pc c' hc')
  · intro c' op' hc'
    by_cases hne : c' = c
    · subst hne
      rw [hc, Option.some.injEq] at hc'
      subst hc'
      rcases h.some_ok c' op hc with ⟨-, hp, hG⟩ | ⟨h1, -⟩ | ⟨h2, -⟩
      · right; left
        refine ⟨by simp, ⟨X.nrmw c', ?_⟩, hG⟩
        simp only [pc] at hp ⊢
        simp [List.filter_append, hp]
      · omega
      · omega
    · simp only [Function.update_apply, hne, ite_false]
      have := h.some_ok c' op' hc'
      simp only [pc] at hpc this ⊢
      rw [hpc c' hne]
      exact this
  · exact h.obj_eq
  · exact h.nodup
  · exact h.cur_inv
  · exact h.G_inv
  · exact h.inv_uniq
  · exact h.inv_cnt
  · exact h.ret_G
  · exact h.ret_rd
  · exact h.sorted
  · exact h.tau_le
  · exact h.tau_ret
  · exact h.tau_inv

theorem good_ret {X : (atomicAlg (C := C) v₀).Config} {G tau} (h : Good v₀ X G tau) {c : C}
    {op : Op} {l : Option (Blk C Kind) × ℕ}
    (hc : X.cur c = some op) (ha : (atomicAlg v₀).act c (X.cnt c) op (X.loc c) = .ret l) :
    Good v₀ { X with loc := Function.update X.loc c l
                     cur := Function.update X.cur c none
                     cnt := Function.update X.cnt c (X.cnt c + 1)
                     tick := X.tick + 1
                     hist := X.hist ++ [.ret c (X.cnt c)
                       (if op = .read then some ((atomicAlg v₀).rdout c (X.loc c)) else none)] }
      G tau := by
  obtain ⟨h2, rfl⟩ := act_ret v₀ ha
  obtain ⟨hp, pre, rest, hGe, hrd⟩ : pc v₀ X c = [] ∧ ∃ pre rest, G = pre ++ ((c, X.cnt c), op) :: rest ∧
      (op = .read → (X.loc c).1 = blkOf (lastW pre)) := by
    rcases h.some_ok c op hc with ⟨h0, -⟩ | ⟨h1, -⟩ | ⟨-, hp, hr⟩
    · omega
    · omega
    · exact ⟨hp, hr⟩
  have hmem : ((c, X.cnt c), op) ∈ G := by rw [hGe]; simp
  constructor
  · intro c' hc'
    by_cases hne : c' = c
    · subst hne; exact hp
    · simp only [Function.update_apply, hne, ite_false] at hc'
      exact h.none_pc c' hc'
  · intro c' op' hc'
    by_cases hne : c' = c
    · subst hne; simp at hc'
    · simp only [Function.update_of_ne hne] at hc' ⊢
      exact h.some_ok c' op' hc'
  · exact h.obj_eq
  · exact h.nodup
  · intro c' op' hc'
    by_cases hne : c' = c
    · subst hne; simp at hc'
    · simp only [Function.update_of_ne hne] at hc' ⊢
      exact List.mem_append_left _ (h.cur_inv c' op' hc')
  · intro e he; exact List.mem_append_left _ (h.G_inv e he)
  · intro c' k o1 o2 h1 h2
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h1 h2
    exact h.inv_uniq _ _ _ _ h1 h2
  · intro c' k o1 h1
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h1
    by_cases hne : c' = c
    · subst hne
      left
      rcases h.inv_cnt _ _ _ h1 with h3 | ⟨h3, -⟩ <;> simp <;> omega
    · simp only [Function.update_apply, hne, ite_false]
      exact h.inv_cnt _ _ _ h1
  · intro c' k out h1
    simp only [List.mem_append, List.mem_singleton, Label.ret.injEq] at h1
    rcases h1 with h1 | ⟨rfl, rfl, -⟩
    · obtain ⟨h3, h4⟩ := h.ret_G _ _ _ h1
      refine ⟨?_, h4⟩
      by_cases hne : c' = c
      · subst hne; simp; omega
      · simp [hne, h3]
    · exact ⟨by simp, op, hmem⟩
  · intro c' k out h1
    simp only [List.mem_append, List.mem_singleton, Label.ret.injEq] at h1
    rcases h1 with h1 | ⟨rfl, rfl, h3⟩
    · exact h.ret_rd _ _ _ h1
    · split_ifs at h3 with hop
      · subst hop
        cases h3
        refine ⟨pre, rest, hGe, ?_⟩
        funext g
        simp only [atomicAlg]
        rw [hrd rfl]
  · exact h.sorted
  · intro e he; have := h.tau_le e he; simp; omega
  · intro e he i out hi
    rcases getElem?_concat_some hi with hi | ⟨rfl, -⟩
    · exact h.tau_ret e he i out hi
    · exact h.tau_le e he
  · intro e he j o hj
    rcases getElem?_concat_some hj with hj | ⟨-, hj⟩
    · exact h.tau_inv e he j o hj
    · cases hj

theorem filter_comm' {α : Type*} (l : List α) (p q : α → Bool) :
    (l.filter p).filter q = (l.filter q).filter p := by
  simp [List.filter_filter, Bool.and_comm]

theorem good_exec {X : (atomicAlg (C := C) v₀).Config} {G tau} (h : Good v₀ X G tau) {c : C}
    {m : ℕ} {p : Pend C Unit (Option (Blk C Kind))} (hp : (atomicAlg v₀).findP X c m = some p) :
    ∃ G' tau', Good v₀ { X with
      obj := Function.update X.obj p.obj ((atomicAlg v₀).apply p.rmw (X.obj p.obj)).1
      loc := Function.update X.loc c
        ((atomicAlg v₀).recv c (X.loc c) p.obj ((atomicAlg v₀).apply p.rmw (X.obj p.obj)).2)
      pend := X.pend.filter (fun q => !decide (q.cl = c ∧ q.idx = m)) } G' tau' := by
  obtain ⟨hpm, hpc, hpi⟩ := Alg.findP_spec hp
  have hppc : p ∈ pc v₀ X c := by simp [pc, hpm, hpc]
  obtain ⟨op, hc⟩ : ∃ op, X.cur c = some op := by
    rcases hcur : X.cur c with _ | op
    · rw [h.none_pc c hcur] at hppc; simp at hppc
    · exact ⟨op, rfl⟩
  obtain ⟨h1, ⟨m', hm'⟩, hG⟩ : (X.loc c).2 = 1 ∧
      (∃ m, pc v₀ X c = [⟨c, m, (), rmwOf c (X.cnt c) op⟩]) ∧ (c, X.cnt c) ∉ G.map Prod.fst := by
    rcases h.some_ok c op hc with ⟨-, hp0, -⟩ | h1 | ⟨-, hp0, -⟩
    · rw [hp0] at hppc; simp at hppc
    · exact h1
    · rw [hp0] at hppc; simp at hppc
  rw [hm', List.mem_singleton] at hppc
  subst hppc
  simp only at hpi
  subst hpi
  have hfilt : ∀ c', List.filter (fun q : Pend C Unit (Option (Blk C Kind)) => decide (q.cl = c'))
      (X.pend.filter (fun q => !decide (q.cl = c ∧ q.idx = m'))) =
      (pc v₀ X c').filter (fun q => !decide (q.cl = c ∧ q.idx = m')) := by
    intro c'; simp only [pc]; exact filter_comm' _ _ _
  have hfc : (pc v₀ X c).filter (fun q => !decide (q.cl = c ∧ q.idx = m')) = [] := by
    rw [hm']; simp
  have hfo : ∀ c', c' ≠ c → (pc v₀ X c').filter (fun q => !decide (q.cl = c ∧ q.idx = m')) =
      pc v₀ X c' := by
    intro c' hne
    apply List.filter_eq_self.2
    intro a ha
    simp only [pc, List.mem_filter, decide_eq_true_eq] at ha
    simp [ha.2, hne]
  have hnil : ∀ c', pc v₀ X c' = [] →
      (pc v₀ X c').filter (fun q => !decide (q.cl = c ∧ q.idx = m')) = [] := by
    intro c' h0; rw [h0]; rfl
  refine ⟨G ++ [((c, X.cnt c), op)], Function.update tau (c, X.cnt c) X.hist.length, ?_⟩
  have htau : ∀ e ∈ G, Function.update tau (c, X.cnt c) X.hist.length e.1 = tau e.1 := by
    intro e he
    rw [Function.update_of_ne]
    rintro heq; exact hG (List.mem_map.2 ⟨e, he, heq⟩)
  constructor
  · intro c' hc'
    simp only [pc]
    rw [hfilt]
    exact hnil c' (h.none_pc c' hc')
  · intro c' op' hc'
    by_cases hne : c' = c
    · subst hne
      rw [hc, Option.some.injEq] at hc'
      subst hc'
      right; right
      refine ⟨by simp, ?_, G, [], by simp, ?_⟩
      · simp only [pc]; rw [hfilt]; exact hfc
      · rintro rfl
        simp [h.obj_eq, rmwOf]
    · simp only [Function.update_of_ne hne]
      have hpc' : pc v₀ { X with
          obj := Function.update X.obj () ((atomicAlg v₀).apply (rmwOf c (X.cnt c) op) (X.obj ())).1
          loc := Function.update X.loc c ((atomicAlg v₀).recv c (X.loc c) ()
            ((atomicAlg v₀).apply (rmwOf c (X.cnt c) op) (X.obj ())).2)
          pend := X.pend.filter (fun q => !decide (q.cl = c ∧ q.idx = m')) } c' =
          (pc v₀ X c').filter (fun q => !decide (q.cl = c ∧ q.idx = m')) := hfilt c'
      rw [hpc']
      have hnot : ∀ k, (c', k) ∉ (G ++ [((c, X.cnt c), op)]).map Prod.fst ↔
          (c', k) ∉ G.map Prod.fst := by
        intro k
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_singleton, Prod.mk.injEq, hne, false_and, or_false]
      rcases h.some_ok c' op' hc' with ⟨h0, hp0, hg⟩ | ⟨h0, ⟨m'', hp0⟩, hg⟩ | ⟨h0, hp0, pre, rest, hge, hr⟩
      · exact Or.inl ⟨h0, hnil c' hp0, (hnot _).2 hg⟩
      · exact Or.inr (Or.inl ⟨h0, ⟨m'', by rw [hfo c' hne, hp0]⟩, (hnot _).2 hg⟩)
      · exact Or.inr (Or.inr ⟨h0, hnil c' hp0, pre, rest ++ [((c, X.cnt c), op)],
          by rw [hge]; simp, hr⟩)
  · cases op
    · simp [lastW_append_write, blkOf, rmwOf]
    · simp [lastW_append_read, h.obj_eq, rmwOf]
  · rw [List.map_append, List.nodup_append]
    refine ⟨h.nodup, by simp, ?_⟩
    simp only [List.map_cons, List.map_nil, List.mem_singleton]
    rintro a ha b rfl rfl
    exact hG ha
  · exact h.cur_inv
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact h.G_inv e he
    · rw [List.mem_singleton] at he; subst he; exact h.cur_inv c op hc
  · exact h.inv_uniq
  · exact h.inv_cnt
  · intro c' k out h1
    obtain ⟨h2, op', h3⟩ := h.ret_G c' k out h1
    exact ⟨h2, op', List.mem_append_left _ h3⟩
  · intro c' k out h1
    obtain ⟨pre, rest, hge, hr⟩ := h.ret_rd c' k out h1
    exact ⟨pre, rest ++ [((c, X.cnt c), op)], by rw [hge]; simp, hr⟩
  · rw [List.pairwise_append]
    refine ⟨h.sorted.imp_of_mem ?_, List.pairwise_singleton _ _, ?_⟩
    · intro a b ha hb hab
      rw [htau a ha, htau b hb]; exact hab
    · intro a ha b hb
      rw [List.mem_singleton] at hb; subst hb
      rw [htau a ha]; simpa using h.tau_le a ha
  · intro e he
    rcases List.mem_append.1 he with he | he
    · rw [htau e he]; exact h.tau_le e he
    · rw [List.mem_singleton] at he; subst he; simp
  · intro e he i out hi
    rcases List.mem_append.1 he with he | he
    · rw [htau e he]; exact h.tau_ret e he i out hi
    · rw [List.mem_singleton] at he; subst he
      have := (h.ret_G _ _ _ (List.mem_of_getElem? hi)).1
      simp at this
  · intro e he j o hj
    rcases List.mem_append.1 he with he | he
    · rw [htau e he]; exact h.tau_inv e he j o hj
    · rw [List.mem_singleton] at he; subst he
      simpa using (List.getElem?_eq_some_iff.1 hj).1

theorem good_tick {X : (atomicAlg (C := C) v₀).Config} {G tau} (h : Good v₀ X G tau) (t : ℕ) :
    Good v₀ { X with tick := t } G tau := by
  cases h; constructor <;> assumption

theorem good_step {X : (atomicAlg (C := C) v₀).Config} {G tau} (h : Good v₀ X G tau)
    (e : Event C) : ∃ G' tau', Good v₀ ((atomicAlg v₀).step X e) G' tau' := by
  rcases Alg.step_cases X e with h1 | h1 | ⟨c, op, -, hc, h1⟩ | ⟨c, op, o, r, l, -, hc, ha, h1⟩ |
    ⟨c, op, l, -, hc, ha, h1⟩ | ⟨c, m, p, -, hp, h1⟩ <;> rw [h1]
  · exact ⟨G, tau, h⟩
  · exact ⟨G, tau, good_tick h _⟩
  · exact ⟨G, tau, good_inv h hc⟩
  · exact ⟨G, tau, good_trigger h hc ha⟩
  · exact ⟨G, tau, good_ret h hc ha⟩
  · convert good_exec h hp

theorem good_runFrom (evs : List (Event C)) : ∀ (X : (atomicAlg (C := C) v₀).Config) G tau,
    Good v₀ X G tau → ∃ G' tau', Good v₀ ((atomicAlg v₀).runFrom X evs) G' tau' := by
  induction evs with
  | nil => intro X G tau h; exact ⟨G, tau, h⟩
  | cons e evs ih =>
    intro X G tau h
    obtain ⟨G', tau', h'⟩ := good_step h e
    exact ih _ G' tau' h'

theorem good_reach (evs : List (Event C)) :
    ∃ G tau, Good v₀ ((atomicAlg (C := C) v₀).runFrom (atomicAlg v₀).init evs) G tau :=
  good_runFrom evs _ _ _ (good_init v₀)

end Invariant

/-! ### Weak regularity -/

theorem idxOf_lt_of_pairwise {α : Type*} [BEq α] [LawfulBEq α] {R : α → α → Prop}
    (hR : ∀ x, R x x) {l : List α} (hl : l.Pairwise R) {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hab : ¬ R b a) : l.idxOf a < l.idxOf b := by
  rcases lt_trichotomy (l.idxOf a) (l.idxOf b) with h | h | h
  · exact h
  · rw [List.idxOf_inj ha] at h
    subst h; exact absurd (hR a) hab
  · exfalso; apply hab
    have := List.pairwise_iff_getElem.1 hl _ _ (List.idxOf_lt_length_iff.2 hb)
      (List.idxOf_lt_length_iff.2 ha) h
    rwa [List.getElem_idxOf, List.getElem_idxOf] at this

/-- The register `atomicAlg v₀` is weakly regular (it is in fact atomic). -/
theorem atomicAlg_weakRegular (v₀ : V) : (atomicAlg (C := C) v₀).WeakRegular v₀ := by
  intro evs val rd out hrd
  obtain ⟨G, tau, h⟩ := good_reach (v₀ := v₀) evs
  dsimp only
  obtain ⟨pre, rest, hGe, hout⟩ := h.ret_rd rd.1 rd.2 out hrd
  set hist := ((atomicAlg (C := C) v₀).runFrom (atomicAlg v₀).init evs).hist with hhist
  let P : OpId C × Op → Bool := fun e => decide (e.2 = .write ∨ e.1 = rd)
  have hmemL : ∀ a, a ∈ (G.filter P).map Prod.fst ↔ ∃ op, (a, op) ∈ G ∧ (op = .write ∨ a = rd) := by
    intro a
    simp [P]
  refine ⟨(G.filter P).map Prod.fst, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.nodup.sublist ((List.filter_sublist).map _)
  · exact (hmemL rd).2 ⟨.read, by rw [hGe]; simp, Or.inr rfl⟩
  · intro a ha hne
    obtain ⟨op, hop, hw⟩ := (hmemL a).1 ha
    rcases hw with rfl | rfl
    · exact h.G_inv _ hop
    · exact absurd rfl hne
  · rintro a hw ⟨o, hc⟩
    obtain ⟨-, op, hop⟩ := h.ret_G a.1 a.2 o hc
    have := h.inv_uniq _ _ _ _ (h.G_inv _ hop) hw
    exact (hmemL a).2 ⟨op, hop, Or.inl this⟩
  · rintro a ha b hb ⟨i, j, hij, ⟨o1, hi⟩, ⟨o2, hj⟩⟩
    obtain ⟨opa, hopa, -⟩ := (hmemL a).1 ha
    obtain ⟨opb, hopb, -⟩ := (hmemL b).1 hb
    have h1 := h.tau_ret _ hopa i o1 hi
    have h2 := h.tau_inv _ hopb j o2 hj
    have hs : ((G.filter P).map Prod.fst).Pairwise (fun x y => tau x ≤ tau y) :=
      List.pairwise_map.2 (h.sorted.filter _)
    exact idxOf_lt_of_pairwise (R := fun x y => tau x ≤ tau y) (fun x => le_rfl) hs ha hb
      (by simp only at h1 h2 ⊢; omega)
  · have hnd := h.nodup
    rw [hGe] at hnd
    simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons,
      List.mem_cons] at hnd
    have hrdpre : rd ∉ pre.map Prod.fst := fun hm => hnd.2.2 rd hm rd (Or.inl rfl) rfl
    have hfp : pre.filter P = pre.filter (fun e => decide (e.2 = .write)) := by
      apply List.filter_congr
      intro e he
      have : e.1 ≠ rd := fun heq => hrdpre (List.mem_map.2 ⟨e, he, heq⟩)
      simp [P, this]
    have hL : (G.filter P).map Prod.fst = (pre.filter (fun e => decide (e.2 = .write))).map
        Prod.fst ++ rd :: (rest.filter P).map Prod.fst := by
      rw [hGe, List.filter_append, hfp, List.filter_cons]
      simp [P]
    have hrd' : rd ∉ (pre.filter (fun e => decide (e.2 = .write))).map Prod.fst := by
      intro hm
      exact hrdpre (List.map_subset _ (List.filter_subset_self _) hm)
    rw [hL, List.idxOf_append_of_notMem hrd', List.idxOf_cons_self, add_zero,
      List.take_left' rfl, hout]
    simp only [Alg.lastVal, lastW, blkOf, List.getLast?_map]
    have key : ∀ o : Option (OpId C), rdf v₀ (o.map (fun w => (w, Kind.one)))
        ((atomicAlg v₀).contents val) = (o.map val).getD v₀ := by
      rintro (_ | w)
      · rfl
      · exact dec_encV v₀ (val w)
    exact key _

/-! ### Lock-freedom -/

section LockFree

variable {v₀ : V}

theorem Good.phase_le {X : (atomicAlg (C := C) v₀).Config} {G tau} (h : Good v₀ X G tau) {c : C}
    {op : Op} (hc : X.cur c = some op) : (X.loc c).2 ≤ 2 := by
  rcases h.some_ok c op hc with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ <;> omega

theorem Good.pc_nil {X : (atomicAlg (C := C) v₀).Config} {G tau} (h : Good v₀ X G tau) {c : C}
    {op : Op} (hc : X.cur c = some op) (h1 : (X.loc c).2 ≠ 1) : pc v₀ X c = [] := by
  rcases h.some_ok c op hc with ⟨-, hp, -⟩ | ⟨h0, -⟩ | ⟨-, hp, -⟩
  · exact hp
  · exact absurd h0 h1
  · exact hp

/-- In a step that does not complete the operation of `c`, the phase of `c` does not decrease, and if
it stays the same, so do the pending RMWs of `c`. -/
theorem phase_step {X : (atomicAlg (C := C) v₀).Config} {G tau} (h : Good v₀ X G tau) {c : C}
    {op : Op} (hc : X.cur c = some op) (e : Event C)
    (hc' : ((atomicAlg v₀).step X e).cur c ≠ none) :
    (X.loc c).2 ≤ (((atomicAlg v₀).step X e).loc c).2 ∧
      ((((atomicAlg v₀).step X e).loc c).2 = (X.loc c).2 →
        pc v₀ ((atomicAlg v₀).step X e) c = pc v₀ X c) := by
  rcases Alg.step_cases X e with h1 | h1 | ⟨c', op', -, hc0, h1⟩ | ⟨c', op', o, r, l, -, hc0, ha, h1⟩ |
    ⟨c', op', l, -, hc0, ha, h1⟩ | ⟨c', m, p, -, hp, h1⟩ <;> rw [h1] at hc' ⊢
  · exact ⟨le_rfl, fun _ => rfl⟩
  · exact ⟨le_rfl, fun _ => rfl⟩
  · have hne : c ≠ c' := by rintro rfl; simp [hc] at hc0
    simp only [Function.update_of_ne hne]
    exact ⟨le_rfl, fun _ => rfl⟩
  · by_cases hne : c = c'
    · subst hne
      obtain ⟨h0, -, rfl⟩ := act_trigger v₀ ha
      simp [h0]
    · simp only [Function.update_of_ne hne]
      refine ⟨le_rfl, fun _ => ?_⟩
      simp [pc, List.filter_append, Ne.symm hne]
  · by_cases hne : c = c'
    · subst hne; simp at hc'
    · simp only [Function.update_of_ne hne]
      exact ⟨le_rfl, fun _ => rfl⟩
  · obtain ⟨hpm, hpc, -⟩ := Alg.findP_spec hp
    by_cases hne : c = c'
    · subst hne
      have h2 := h.phase_le hc
      simp only [Function.update_self]
      refine ⟨by simp only [atomicAlg]; omega, fun heq => ?_⟩
      have heq2 : (X.loc c).2 = 2 := by simp only [atomicAlg] at heq; omega
      have := h.pc_nil hc (by omega)
      have hmem : p ∈ pc v₀ X c := by simp [pc, hpm, hpc]
      rw [this] at hmem; simp at hmem
    · simp only [Function.update_of_ne hne]
      refine ⟨le_rfl, fun _ => ?_⟩
      simp only [pc]
      rw [filter_comm']
      apply List.filter_eq_self.2
      intro a ha
      simp only [List.mem_filter, decide_eq_true_eq] at ha
      simp [ha.2, hne]

/-- A step of `c` in phase `0` or `2` changes its phase (or completes its operation). -/
theorem phase_step_self {X : (atomicAlg (C := C) v₀).Config} {G tau} (h : Good v₀ X G tau)
    {c : C} {op : Op} (hc : X.cur c = some op)
    (hc' : ((atomicAlg v₀).step X (.step c)).cur c ≠ none) (h1 : (X.loc c).2 ≠ 1) :
    (((atomicAlg v₀).step X (.step c)).loc c).2 ≠ (X.loc c).2 := by
  have h2 := h.phase_le hc
  rcases (show (X.loc c).2 = 0 ∨ (X.loc c).2 = 2 by omega) with h0 | h0
  · rw [Alg.step_step_trigger hc (act_zero v₀ h0)]
    simp [h0]
  · rw [Alg.step_step_ret hc (act_two v₀ h0)] at hc'
    simp at hc'

end LockFree

/-- The register `atomicAlg v₀` is lock-free (indeed wait-free) when no base object crashes. -/
theorem atomicAlg_lockFree (v₀ : V) : (atomicAlg (C := C) v₀).LockFree 0 := by
  intro ev Fc Fo hF t c hcF hcur
  by_contra hno
  push Not at hno
  have hFo : Fo = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hF.card_le)
  have good : ∀ s, ∃ G tau, Good v₀ ((atomicAlg v₀).cfg ev s) G tau := fun s => by
    rw [Alg.cfg_eq_runFrom]; exact good_reach _
  have hcur' : ∀ s ≥ t, ((atomicAlg v₀).cfg ev s).cur c ≠ none := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => exact hcur
    | succ s hs ih => intro hn; exact hno s hs c ⟨ih, hn⟩
  have hsome : ∀ s ≥ t, ∃ op, ((atomicAlg v₀).cfg ev s).cur c = some op :=
    fun s hs => Option.ne_none_iff_exists'.1 (hcur' s hs)
  let ph := fun s => (((atomicAlg v₀).cfg ev s).loc c).2
  have hstep : ∀ s ≥ t, ph s ≤ ph (s + 1) ∧
      (ph (s + 1) = ph s → pc v₀ ((atomicAlg v₀).cfg ev (s + 1)) c = pc v₀ ((atomicAlg v₀).cfg ev s) c) := by
    intro s hs
    obtain ⟨G, tau, hg⟩ := good s
    obtain ⟨op, hop⟩ := hsome s hs
    exact phase_step hg hop (ev s) (hcur' (s + 1) (by omega))
  have hmono : ∀ s ≥ t, ∀ s' ≥ s, ph s ≤ ph s' := by
    intro s hs s' hs'
    induction s', hs' using Nat.le_induction with
    | base => exact le_rfl
    | succ s' hs' ih => exact ih.trans (hstep s' (by omega)).1
  have hle2 : ∀ s ≥ t, ph s ≤ 2 := by
    intro s hs
    obtain ⟨G, tau, hg⟩ := good s
    obtain ⟨op, hop⟩ := hsome s hs
    exact hg.phase_le hop
  have key : ∀ n, ∀ s ≥ t, 2 - ph s = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hs hn
      by_cases hconst : ∀ s' ≥ s, ph s' = ph s
      · have hpcc : ∀ s' ≥ s, pc v₀ ((atomicAlg v₀).cfg ev s') c = pc v₀ ((atomicAlg v₀).cfg ev s) c := by
          intro s' hs'
          induction s', hs' using Nat.le_induction with
          | base => rfl
          | succ s' hs' ih' =>
            rw [(hstep s' (by omega)).2 (by rw [hconst _ hs', hconst _ (by omega)]), ih']
        obtain ⟨G, tau, hg⟩ := good s
        obtain ⟨op, hop⟩ := hsome s hs
        by_cases h1 : ph s = 1
        · rcases hg.some_ok c op hop with ⟨h0, -⟩ | ⟨-, ⟨m, hm⟩, -⟩ | ⟨h0, -⟩
          · exact absurd h0 (by simp only [ph] at h1; omega)
          · have hq : (⟨c, m, (), rmwOf c (((atomicAlg v₀).cfg ev s).cnt c) op⟩ :
                Pend C Unit (Option (Blk C Kind))) ∈ ((atomicAlg v₀).cfg ev s).pend := by
              have : _ ∈ pc v₀ ((atomicAlg v₀).cfg ev s) c := hm ▸ List.mem_singleton_self _
              exact (List.mem_filter.1 this).1
            obtain ⟨s', hs', hq'⟩ := hF.rmw_live s _ hq hcF (by simp [hFo])
            have : _ ∈ pc v₀ ((atomicAlg v₀).cfg ev s') c := (hpcc s' hs').symm ▸ hm ▸
              List.mem_singleton_self _
            exact hq' (List.mem_filter.1 this).1
          · exact absurd h0 (by simp only [ph] at h1; omega)
        · obtain ⟨s', hs', hev⟩ := hF.cl_live c hcF s
          obtain ⟨G', tau', hg'⟩ := good s'
          obtain ⟨op', hop'⟩ := hsome s' (by omega)
          have hc1 := hcur' (s' + 1) (by omega)
          have e1 : (atomicAlg v₀).cfg ev (s' + 1) = (atomicAlg v₀).step ((atomicAlg v₀).cfg ev s')
            (.step c) := by rw [← hev]; rfl
          rw [e1] at hc1
          have h3 := hconst _ hs'
          have h4 := hconst (s' + 1) (by omega)
          simp only [ph] at h1 h3 h4
          have := phase_step_self hg' hop' hc1 (by omega)
          rw [← e1] at this
          exact this (by omega)
      · push Not at hconst
        obtain ⟨s', hs', hne⟩ := hconst
        have := hmono s hs s' hs'
        have := hle2 s' (by omega)
        exact ih (2 - ph s') (by omega) s' (by omega) rfl
  exact key _ t le_rfl rfl

/-! ### The hypotheses of Theorem 2 are satisfiable together -/

/-- Non-vacuity of `Alg.theorem2` / `Alg.corollary2`: for every value set there is a lock-free (with
`f = 0`), weakly regular algorithm in the black-box storage model. -/
theorem theorem2_hyps_satisfiable (v₀ : V) :
    ∃ A : Alg C Unit Kind V, A.LockFree 0 ∧ A.WeakRegular v₀ :=
  ⟨atomicAlg v₀, atomicAlg_lockFree v₀, atomicAlg_weakRegular v₀⟩

/-- `Alg.theorem2` instantiated on `atomicAlg` with three clients, Boolean values and `S = 2`. -/
theorem theorem2_atomicAlg : ∃ X, (atomicAlg (C := Fin 3) false).Reachable X ∧
    (2 ≤ (atomicAlg (C := Fin 3) false).storage X ∨
      0 < ((atomicAlg (C := Fin 3) false).Full X).card) :=
  (atomicAlg false).theorem2 (by simp) (by simp) (atomicAlg_lockFree false)
    (atomicAlg_weakRegular false)

end Podc.ReliableStorageSpace.NonVacuity

end
