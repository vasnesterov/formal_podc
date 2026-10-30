import Papers.PODC2026.GirthApproxCongest.Gadget
import Cslib.Foundations.Data.Nat.ModCount

/-!
# Minimum weight cycles of the lower-bound graphs (Claims 6.1 and 6.2)

* `dGraph_mwc_of_inter`, `dGraph_mwc_of_disj`: Claim 6.1 — if the inputs intersect, the directed
  graph `G_{x,y}` has a directed cycle of length `2q`, and every directed cycle has length at least
  `2q`; if they are disjoint and `H` has girth `≥ 2k`, every directed cycle has length `≥ 2kq`.
* `uGraph_mwc_of_inter`, `uGraph_mwc_of_disj`: Claim 6.2 — the same for the undirected weighted
  graph of §6.1, with bounds `2(q-1) + 2 Win` and `2k · Win`.

## Proof outline

* Tree and padding vertices lie on no directed cycle (a potential strictly decreases along the
  arcs leaving them), and in a directed cycle the potential `ψ` (`r w c ↦ c`, `l u c ↦ 2q-1-c`)
  increases by `1` modulo `2q` along every arc, so `2q` divides the length.
* An undirected cycle through layer vertices only projects (forgetting the columns) to a closed
  walk in `H` with "stutters" at the pipe steps; removing the stutters gives a circuit of `H`
  whose length is the number of input edges of the cycle (`egirth_le_card_of_stutter`). Distinct
  input edges of the cycle have distinct images in `H` because `x` and `y` are disjoint.
-/

namespace Podc.GirthApproxCongest

open Finset Podc.MinWeightCycleCongest Vtx TNode
open scoped ENNReal

/-! ### Closed walks with stutters -/

section Stutter

variable {α : Type*} [DecidableEq α] (G : SimpleGraph α) (f : ℕ → α)

/-- The walk `f 0, f 1, …, f n` in `G` with the stutters `f i = f (i + 1)` removed. -/
-- CSLib candidate
def stutterWalk (hf : ∀ i, f i ≠ f (i + 1) → G.Adj (f i) (f (i + 1))) :
    (n : ℕ) → G.Walk (f 0) (f n)
  | 0 => .nil
  | n + 1 =>
    if h : f n = f (n + 1) then (stutterWalk hf n).copy rfl h
    else (stutterWalk hf n).concat (hf n h)

lemma stutterWalk_edges (hf : ∀ i, f i ≠ f (i + 1) → G.Adj (f i) (f (i + 1))) (n : ℕ) :
    (stutterWalk G f hf n).edges =
      ((List.range n).filter (fun i => f i ≠ f (i + 1))).map (fun i => s(f i, f (i + 1))) := by
  induction n with
  | zero => simp [stutterWalk]
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append]
    by_cases h : f n = f (n + 1)
    · simp [stutterWalk, h, ih]
    · simp [stutterWalk, h, ih, SimpleGraph.Walk.edges_concat]

lemma stutterWalk_length (hf : ∀ i, f i ≠ f (i + 1) → G.Adj (f i) (f (i + 1))) (n : ℕ) :
    (stutterWalk G f hf n).length = #{i ∈ range n | f i ≠ f (i + 1)} := by
  induction n with
  | zero => simp [stutterWalk]
  | succ n ih =>
    rw [range_add_one, filter_insert]
    by_cases h : f n = f (n + 1)
    · simp [stutterWalk, h, ih]
    · simp only [stutterWalk, h, dite_false, SimpleGraph.Walk.length_concat, ih, ne_eq,
        not_false_eq_true, ite_true]
      rw [card_insert_of_notMem (by simp)]

/-- A closed sequence `f 0, …, f len = f 0` in which consecutive entries are equal or adjacent,
with at least one non-stutter step and pairwise distinct non-stutter edges, gives a circuit of
length the number of non-stutter steps; hence the girth is at most that number. -/
-- CSLib candidate
lemma egirth_le_card_of_stutter (hf : ∀ i, f i ≠ f (i + 1) → G.Adj (f i) (f (i + 1)))
    {len : ℕ} (hper : f len = f 0)
    (hinj : ∀ i < len, ∀ j < len, f i ≠ f (i + 1) → f j ≠ f (j + 1) →
      s(f i, f (i + 1)) = s(f j, f (j + 1)) → i = j)
    (hne : ∃ i < len, f i ≠ f (i + 1)) :
    G.egirth ≤ #{i ∈ range len | f i ≠ f (i + 1)} := by
  let w : G.Walk (f 0) (f 0) := (stutterWalk G f hf len).copy rfl hper
  have hlen : w.length = #{i ∈ range len | f i ≠ f (i + 1)} := by
    simp [w, stutterWalk_length]
  have hc : w.IsCircuit := by
    refine ⟨⟨?_⟩, ?_⟩
    · simp only [w, SimpleGraph.Walk.edges_copy, stutterWalk_edges]
      refine List.Nodup.map_on ?_ (List.nodup_range.filter _)
      intro i hi j hj he
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi hj
      exact hinj i hi.1 j hj.1 hi.2 hj.2 he
    · intro h
      have : w.length = 0 := by rw [h]; rfl
      rw [hlen, card_eq_zero, filter_eq_empty_iff] at this
      obtain ⟨i, hi, hne⟩ := hne
      exact this (mem_range.2 hi) hne
  rw [← hlen]
  exact hc.egirth_le_length

end Stutter

/-! ### Layer vertices -/

variable {L R : Type*} {q d p : ℕ} {E : Finset (L × R)} {x y : E → Bool}

/-- The copy of a vertex of `H` in column `c`. -/
def lay : L ⊕ R → Fin q → Vtx L R q d p
  | .inl u, c => .l u c
  | .inr w, c => .r w c

lemma lay_inj {a b : L ⊕ R} {c c' : Fin q} :
    (lay a c : Vtx L R q d p) = lay b c' ↔ a = b ∧ c = c' := by
  cases a <;> cases b <;> simp [lay]

lemma exists_lay {v : Vtx L R q d p} (h : v.isLayer) : ∃ a c, v = lay a c := by
  cases v with
  | l u c => exact ⟨.inl u, c, rfl⟩
  | r w c => exact ⟨.inr w, c, rfl⟩
  | t z => simp [isLayer] at h
  | pad i => simp [isLayer] at h

@[simp] lemma col_lay (a : L ⊕ R) (c : Fin q) : (lay a c : Vtx L R q d p).col = c := by
  cases a <;> rfl

@[simp] lemma isLayer_lay (a : L ⊕ R) (c : Fin q) : (lay a c : Vtx L R q d p).isLayer := by
  cases a <;> rfl

/-- An edge between two layer vertices is a pipe (same vertex of `H`, adjacent columns) or an
input edge (column `0` with Alice's bit, or column `q-1` with Bob's bit). -/
lemma adj_lay {a b : L ⊕ R} {c c' : Fin q}
    (h : darc E x y (lay a c : Vtx L R q d p) (lay b c') ∨
      darc E x y (lay b c' : Vtx L R q d p) (lay a c)) :
    (a = b ∧ ((c' : ℕ) = c + 1 ∨ (c : ℕ) = c' + 1)) ∨
    (a ≠ b ∧ c = c' ∧ ∃ u w, s(a, b) = s(.inl u, .inr w) ∧
      (((c : ℕ) = 0 ∧ inSet E x u w) ∨ ((c : ℕ) + 1 = q ∧ inSet E y u w))) := by
  cases a with
  | inl u =>
    cases b with
    | inl u' =>
      simp only [lay, darc] at h
      left
      rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp [h]
    | inr w =>
      simp only [lay, darc] at h
      right
      refine ⟨by simp, Fin.ext (by omega), u, w, rfl, ?_⟩
      rcases h with ⟨h1, -, h⟩ | ⟨-, h1, h⟩
      · exact .inl ⟨h1, h⟩
      · exact .inr ⟨h1, h⟩
  | inr w =>
    cases b with
    | inl u =>
      simp only [lay, darc] at h
      right
      refine ⟨by simp, Fin.ext (by omega), u, w, Sym2.eq_swap, ?_⟩
      rcases h with ⟨h1, -, h⟩ | ⟨-, h1, h⟩
      · exact .inr ⟨h1, h⟩
      · exact .inl ⟨h1, h⟩
    | inr w' =>
      simp only [lay, darc] at h
      left
      rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp [h]


lemma succ_mod_cases {i len : ℕ} (h : i < len) :
    ((i + 1) % len = i + 1 ∧ i + 1 < len) ∨ ((i + 1) % len = 0 ∧ i + 1 = len) := by
  rcases Nat.lt_or_ge (i + 1) len with h' | h'
  · exact .inl ⟨Nat.mod_eq_of_lt h', h'⟩
  · right
    have : i + 1 = len := by omega
    exact ⟨by rw [this, Nat.mod_self], this⟩

lemma inSet_disj (hxy : ∀ e, ¬ (x e = true ∧ y e = true)) {u : L} {w : R}
    (hx : inSet E x u w) (hy : inSet E y u w) : False := by
  obtain ⟨h1, hx⟩ := hx
  obtain ⟨h2, hy⟩ := hy
  exact hxy ⟨_, h1⟩ ⟨hx, hy⟩

variable [DecidableEq L] [DecidableEq R]

/-- **Key lemma.** A cycle (in the undirected sense) of length `≥ 3` through layer vertices only
uses at least `2k` input edges (edges inside a column) when `H` has girth `≥ 2k` and the inputs
are disjoint: its projection to `H` is a circuit made of the images of the input edges. -/
lemma two_mul_le_card_input {s : ℕ → Vtx L R q d p} {len : ℕ} (h3 : 3 ≤ len)
    (hper : ∀ i, s (i + len) = s i) (hinj : ∀ i < len, ∀ j < len, s i = s j → i = j)
    (hlay : ∀ i, (s i).isLayer)
    (hadj : ∀ i, darc E x y (s i) (s (i + 1)) ∨ darc E x y (s (i + 1)) (s i))
    {k : ℕ} (hk : ((2 * k : ℕ) : ℕ∞) ≤ (bipGraph E).egirth)
    (hxy : ∀ e, ¬ (x e = true ∧ y e = true)) :
    2 * k ≤ #{i ∈ range len | (s i).col = (s (i + 1)).col} := by
  choose f g hs using fun i => exists_lay (hlay i)
  have hstep : ∀ i, (f i = f (i + 1) ∧ (((g (i + 1)) : ℕ) = g i + 1 ∨ (g i : ℕ) = g (i + 1) + 1)) ∨
      (f i ≠ f (i + 1) ∧ g i = g (i + 1) ∧ ∃ u w, s(f i, f (i + 1)) = s(.inl u, .inr w) ∧
        (((g i : ℕ) = 0 ∧ inSet E x u w) ∨ ((g i : ℕ) + 1 = q ∧ inSet E y u w))) := by
    intro i
    have := hadj i
    rw [hs i, hs (i + 1)] at this
    exact adj_lay this
  have hcol : ∀ i, (s i).col = (s (i + 1)).col ↔ f i ≠ f (i + 1) := by
    intro i
    rw [hs i, hs (i + 1), col_lay, col_lay]
    rcases hstep i with ⟨h1, h2⟩ | ⟨h1, h2, -⟩
    · simp only [h1, ne_eq, not_true_eq_false, iff_false]
      omega
    · simp [h1, h2]
  have hfper : ∀ i, f (i + len) = f i ∧ g (i + len) = g i := fun i =>
    lay_inj.1 (by rw [← hs, ← hs, hper])
  rw [filter_congr (fun i _ => hcol i)]
  have hne : ∃ i < len, f i ≠ f (i + 1) := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ i, f i = f (i + 1) := by
      intro i
      have := periodic_mod (vtx := fun i => (f i, f (i + 1))) (L := len)
        (fun i => Prod.ext (hfper i).1 (by rw [Nat.add_right_comm]; exact (hfper (i + 1)).1)) i
      simp only [Prod.mk.injEq] at this
      rw [this.1, this.2]
      exact hcon _ (Nat.mod_lt _ (by omega))
    have hconst : ∀ i, f i = f 0 := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [← hall, ih]
    have hpipe : ∀ i, ((g (i + 1)) : ℕ) = g i + 1 ∨ (g i : ℕ) = g (i + 1) + 1 := by
      intro i
      rcases hstep i with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (hall i) h
    obtain ⟨i0, -, hmax⟩ := exists_max_image (range len) (fun i => (g i : ℕ))
      ⟨0, mem_range.2 (by omega)⟩
    have hgle : ∀ n, (g n : ℕ) ≤ g i0 := by
      intro n
      rw [periodic_mod (vtx := g) (fun i => (hfper i).2) n]
      exact hmax _ (mem_range.2 (Nat.mod_lt _ (by omega)))
    have h1 : (g (i0 + 1) : ℕ) + 1 = g i0 := by
      have := hgle (i0 + 1)
      rcases hpipe i0 with h | h <;> omega
    set j := i0 + len - 1 with hj
    have hj1 : j + 1 = i0 + len := by omega
    have h2 : (g j : ℕ) + 1 = g i0 := by
      have := hgle j
      have h := hpipe j
      rw [hj1, (hfper i0).2] at h
      omega
    have hsj : s j = s (i0 + 1) := by
      rw [hs j, hs (i0 + 1), hconst j, hconst (i0 + 1), Fin.ext (by omega : (g j : ℕ) = g (i0 + 1))]
    apply ne_add_two hper hinj h3 j
    rw [hsj, show j + 2 = i0 + 1 + len by omega, hper]
  have hinjE : ∀ i < len, ∀ j < len, f i ≠ f (i + 1) → f j ≠ f (j + 1) →
      s(f i, f (i + 1)) = s(f j, f (j + 1)) → i = j := by
    intro i hi j hj hfi hfj he
    obtain ⟨-, hgi, u, w, hei, hbi⟩ := (hstep i).resolve_left (fun h => hfi h.1)
    obtain ⟨-, hgj, u', w', hej, hbj⟩ := (hstep j).resolve_left (fun h => hfj h.1)
    by_cases hg : g i = g j
    · rcases Sym2.eq_iff.1 he with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact hinj i hi j hj (by rw [hs i, hs j, e1, hg])
      · exfalso
        have m1 := mod_eq_of_eq hper hinj (by omega)
          (show s i = s (j + 1) by rw [hs i, hs (j + 1), e1, hg, hgj])
        have m2 := mod_eq_of_eq hper hinj (by omega)
          (show s (i + 1) = s j by rw [hs (i + 1), hs j, e2, ← hgi, hg])
        rw [Nat.mod_eq_of_lt hi] at m1
        rw [Nat.mod_eq_of_lt hj] at m2
        rcases succ_mod_cases hi with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
          rcases succ_mod_cases hj with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega
    · exfalso
      rw [he, hej] at hei
      simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
        or_false] at hei
      obtain ⟨rfl, rfl⟩ := hei
      have hg' : (g i : ℕ) ≠ g j := fun h => hg (Fin.ext h)
      rcases hbi with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hbj with ⟨b1, b2⟩ | ⟨b1, b2⟩
      · omega
      · exact inSet_disj hxy a2 b2
      · exact inSet_disj hxy b2 a2
      · omega
  have hadjH : ∀ i, f i ≠ f (i + 1) → (bipGraph E).Adj (f i) (f (i + 1)) := by
    intro i hi
    obtain ⟨-, -, u, w, he, hb⟩ := (hstep i).resolve_left (fun h => hi h.1)
    have hm : (u, w) ∈ E := by rcases hb with ⟨-, hm, -⟩ | ⟨-, hm, -⟩ <;> exact hm
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simpa using hm
  have := hk.trans (egirth_le_card_of_stutter (bipGraph E) f hadjH (by simpa using (hfper 0).1)
    hinjE hne)
  exact_mod_cast this

/-! ### Directed cycles -/

/-- A potential that strictly decreases along arcs leaving tree and padding vertices. -/
def phi : Vtx L R q d p → ℕ
  | .t z => z.h + 1
  | _ => 0

/-- The potential `ψ`, increasing by one modulo `2q` along every arc between layer vertices. -/
def psi : Vtx L R q d p → ℕ
  | .r _ c => c
  | .l _ c => 2 * q - 1 - c
  | _ => 0

omit [DecidableEq L] [DecidableEq R] in
lemma phi_darc {u v : Vtx L R q d p} (h : darc E x y u v) (hu : ¬ u.isLayer) :
    ¬ v.isLayer ∧ phi v < phi u := by
  cases u <;> cases v <;> simp_all [darc, isLayer, phi, Child]

omit [DecidableEq L] [DecidableEq R] in
lemma psi_darc {u v : Vtx L R q d p} (h : darc E x y u v) (hu : u.isLayer) (hv : v.isLayer) :
    (psi v = psi u + 1 ∨ (psi v = 0 ∧ psi u + 1 = 2 * q)) ∧
      (u.col = v.col ↔ (psi u = q - 1 ∨ psi u = 2 * q - 1)) := by
  cases u <;> cases v <;> simp_all [darc, isLayer, psi, col] <;> omega

omit [DecidableEq L] [DecidableEq R] in
/-- Tree and padding vertices lie on no closed directed walk. -/
lemma isLayer_of_darc_periodic {s : ℕ → Vtx L R q d p} {len : ℕ} (hlen : 0 < len)
    (hper : ∀ i, s (i + len) = s i) (harc : ∀ i, darc E x y (s i) (s (i + 1))) (i : ℕ) :
    (s i).isLayer := by
  by_contra hi
  have key : ∀ n, ¬ (s (i + n)).isLayer ∧ phi (s (i + n)) + n ≤ phi (s i) := by
    intro n
    induction n with
    | zero => exact ⟨hi, le_refl _⟩
    | succ n ih =>
      have := phi_darc (harc (i + n)) ih.1
      rw [← add_assoc]
      exact ⟨this.1, by omega⟩
  have := (key len).2
  rw [hper] at this
  omega

omit [DecidableEq L] [DecidableEq R] in
lemma psi_modEq {s : ℕ → Vtx L R q d p} (hlay : ∀ i, (s i).isLayer)
    (harc : ∀ i, darc E x y (s i) (s (i + 1))) (i : ℕ) :
    psi (s i) ≡ psi (s 0) + i [MOD 2 * q] := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rcases (psi_darc (harc i) (hlay i) (hlay (i + 1))).1 with h | ⟨h1, h2⟩
    · rw [h, ← add_assoc]
      exact ih.add_right 1
    · rw [h1, ← add_assoc]
      calc 0 ≡ 2 * q [MOD 2 * q] := (Nat.modEq_zero_iff_dvd.2 dvd_rfl).symm
        _ = psi (s i) + 1 := h2.symm
        _ ≡ psi (s 0) + i + 1 [MOD 2 * q] := ih.add_right 1

variable {W : ℕ}

/-- Facts about a directed cycle of `G_{x,y}`: it uses layer vertices only, its length is a
multiple of `2q`, and its weight is its length. -/
lemma dGraph_cycle (C : (dGraph (q := q) (d := d) (p := p) W x y).Cycle) :
    (∀ i, (C.vtx i).isLayer) ∧ 2 * q ∣ C.len ∧ C.weight = C.len := by
  have harc : ∀ i, darc E x y (C.vtx i) (C.vtx (i + 1)) := fun i => dGraph_isSome.1 (C.arc i)
  have hl : ∀ i, (C.vtx i).isLayer :=
    isLayer_of_darc_periodic (by have := C.two_le_len; omega) C.periodic harc
  refine ⟨hl, ?_, ?_⟩
  · have h := psi_modEq hl harc C.len
    rw [show C.vtx C.len = C.vtx 0 by simpa using C.periodic 0] at h
    have h' : psi (C.vtx 0) + 0 ≡ psi (C.vtx 0) + C.len [MOD 2 * q] := by simpa using h
    exact Nat.modEq_zero_iff_dvd.1 (Nat.ModEq.add_left_cancel' _ h').symm
  · simp [WDigraph.Cycle.weight, dGraph_w (harc _)]

/-- The `2q`-cycle `r w 0 → … → r w (q-1) → l u (q-1) → … → l u 0 → r w 0`. -/
def icyc (hq : 0 < q) (u : L) (w : R) (i : ℕ) : Vtx L R q d p :=
  if h : i % (2 * q) < q then .r w ⟨i % (2 * q), h⟩
  else .l u ⟨2 * q - 1 - i % (2 * q), by omega⟩

omit [DecidableEq L] [DecidableEq R] in
lemma icyc_periodic (hq : 0 < q) (u : L) (w : R) (i : ℕ) :
    (icyc (d := d) (p := p) hq u w (i + 2 * q)) = icyc hq u w i := by
  simp [icyc, Nat.add_mod_right]

omit [DecidableEq L] [DecidableEq R] in
lemma icyc_inj (hq : 0 < q) (u : L) (w : R) :
    ∀ i < 2 * q, ∀ j < 2 * q, (icyc (d := d) (p := p) hq u w i) = icyc hq u w j → i = j := by
  intro i hi j hj h
  simp only [icyc, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
  split_ifs at h <;> simp at h <;> omega

omit [DecidableEq L] [DecidableEq R] in
lemma icyc_congr (hq : 0 < q) (u : L) (w : R) {i j : ℕ} (h : i % (2 * q) = j % (2 * q)) :
    (icyc (d := d) (p := p) hq u w i) = icyc hq u w j := by
  simp only [icyc, h]

omit [DecidableEq L] [DecidableEq R] in
lemma icyc_isLayer (hq : 0 < q) (u : L) (w : R) (i : ℕ) :
    (icyc (d := d) (p := p) hq u w i).isLayer := by
  unfold icyc; split <;> rfl

omit [DecidableEq L] [DecidableEq R] in
lemma icyc_col (hq : 0 < q) (u : L) (w : R) (i : ℕ) :
    (icyc (d := d) (p := p) hq u w i).col =
      if i % (2 * q) < q then i % (2 * q) else 2 * q - 1 - i % (2 * q) := by
  unfold icyc; split <;> rfl

omit [DecidableEq L] [DecidableEq R] in
lemma mod_succ_cases (hq : 0 < q) (i : ℕ) :
    ((i + 1) % (2 * q) = i % (2 * q) + 1 ∧ i % (2 * q) + 1 < 2 * q) ∨
      ((i + 1) % (2 * q) = 0 ∧ i % (2 * q) + 1 = 2 * q) := by
  have e : (i + 1) % (2 * q) = (i % (2 * q) + 1) % (2 * q) :=
    ((Nat.mod_modEq i (2 * q)).add_right 1).symm
  rw [e]
  exact succ_mod_cases (Nat.mod_lt _ (by omega))

omit [DecidableEq L] [DecidableEq R] in
/-- The weights of the edges of `icyc` in the undirected graph. -/
lemma icyc_ew (hq : 0 < q) (u : L) (w : R) (Win Wt i : ℕ) :
    ew Win Wt (icyc (d := d) (p := p) hq u w i) (icyc hq u w (i + 1)) =
      if i % (2 * q) = q - 1 ∨ i % (2 * q) = 2 * q - 1 then Win else 1 := by
  simp only [ew, icyc_isLayer, and_self, ite_true]
  rw [icyc_col, icyc_col]
  have hj : i % (2 * q) < 2 * q := Nat.mod_lt _ (by omega)
  rcases mod_succ_cases hq i with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rw [a1] <;>
    generalize i % (2 * q) = j at * <;> split_ifs <;> omega

omit [DecidableEq L] [DecidableEq R] in
/-- The arcs of `icyc`. -/
lemma icyc_arc (hq : 0 < q) {u : L} {w : R} (hx : inSet E x u w) (hy : inSet E y u w) (i : ℕ) :
    darc E x y (icyc (d := d) (p := p) hq u w i) (icyc hq u w (i + 1)) := by
  have hj : i % (2 * q) < 2 * q := Nat.mod_lt _ (by omega)
  rcases mod_succ_cases hq i with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    by_cases h1 : i % (2 * q) < q <;> by_cases h2 : (i + 1) % (2 * q) < q <;>
    simp only [icyc, h1, h2, dite_true, dite_false] <;> simp [darc, hx, hy] <;> omega

omit [DecidableEq L] [DecidableEq R] in
lemma sum_icyc_ew (hq : 0 < q) (u : L) (w : R) (Win Wt : ℕ) :
    ∑ i ∈ range (2 * q), ew Win Wt (icyc (d := d) (p := p) hq u w i) (icyc hq u w (i + 1)) =
      2 * (q - 1) + 2 * Win := by
  rw [sum_congr rfl fun i _ => icyc_ew hq u w Win Wt i, sum_ite]
  simp only [sum_const, smul_eq_mul, mul_one]
  have hf : filter (fun i => i % (2 * q) = q - 1 ∨ i % (2 * q) = 2 * q - 1) (range (2 * q)) =
      {q - 1, 2 * q - 1} := by
    ext i
    simp only [mem_filter, mem_range, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hi, h⟩
      rwa [Nat.mod_eq_of_lt hi] at h
    · rintro (h | h) <;> refine ⟨by omega, ?_⟩ <;> rw [Nat.mod_eq_of_lt (by omega)] <;> omega
  have hc := card_filter_add_card_filter_not (s := range (2 * q))
    (p := fun i => i % (2 * q) = q - 1 ∨ i % (2 * q) = 2 * q - 1)
  rw [hf, card_pair (by omega), card_range] at hc
  rw [hf, card_pair (by omega)]
  omega

variable {Wm Win Wt : ℕ}

/-- The cycle `icyc` as a directed cycle of `G_{x,y}` (when `(u, w) ∈ x ∩ y`). -/
def icycD (hq : 2 ≤ q) {u : L} {w : R} (hx : inSet E x u w) (hy : inSet E y u w) :
    (dGraph (q := q) (d := d) (p := p) W x y).Cycle where
  len := 2 * q
  two_le_len := by omega
  vtx := icyc (by omega) u w
  periodic := icyc_periodic _ u w
  inj := icyc_inj _ u w
  arc i := dGraph_isSome.2 (icyc_arc _ hx hy i)

/-- The cycle `icyc` as a cycle of the undirected graph (when `(u, w) ∈ x ∩ y`). -/
def icycU (hq : 2 ≤ q) {u : L} {w : R} (hx : inSet E x u w) (hy : inSet E y u w) :
    (uGraph (q := q) (d := d) (p := p) Wm Win Wt x y).Cycle where
  len := 2 * q
  three_le_len := by omega
  vtx := icyc (by omega) u w
  periodic := icyc_periodic _ u w
  inj := icyc_inj _ u w
  adj i := uGraph_isSome.2 (.inl (icyc_arc _ hx hy i))

/-- Claim 6.1(1) of [Chechik–Lifshitz–Mukhtar]: if Alice's and Bob's inputs intersect, the
minimum weight (= length) of a directed cycle of `G_{x,y}` is `2q`. -/
theorem dGraph_mwc_of_inter (W : ℕ) (hq : 2 ≤ q) (h : ∃ e, x e = true ∧ y e = true) :
    (dGraph (q := q) (d := d) (p := p) W x y).mwc = 2 * q := by
  obtain ⟨⟨⟨u, w⟩, he⟩, hx, hy⟩ := h
  apply le_antisymm
  · refine iInf_le_of_le (icycD (W := W) hq (u := u) (w := w) ⟨he, hx⟩ ⟨he, hy⟩) ?_
    rw [(dGraph_cycle _).2.2]
    simp [icycD]
  · refine le_iInf fun C => ?_
    obtain ⟨-, hdvd, hw⟩ := dGraph_cycle C
    rw [hw]
    have := Nat.le_of_dvd (by have := C.two_le_len; omega) hdvd
    exact_mod_cast this

/-- Claim 6.1(2) of [Chechik–Lifshitz–Mukhtar], generalized as in §6.2: if the inputs are
disjoint and `H` has girth at least `2k`, every directed cycle of `G_{x,y}` has length at least
`2kq` (the paper's case is `k = 2`, any bipartite `H`). -/
theorem dGraph_mwc_of_disj (W k : ℕ) (hq : 2 ≤ q)
    (hk : ((2 * k : ℕ) : ℕ∞) ≤ (bipGraph E).egirth) (h : ∀ e, ¬ (x e = true ∧ y e = true)) :
    ((2 * k * q : ℕ) : ℝ≥0∞) ≤ (dGraph (q := q) (d := d) (p := p) W x y).mwc := by
  refine le_iInf fun C => ?_
  obtain ⟨hl, hdvd, hw⟩ := dGraph_cycle C
  have hlen : 2 * q ≤ C.len := Nat.le_of_dvd (by have := C.two_le_len; omega) hdvd
  have harc : ∀ i, darc E x y (C.vtx i) (C.vtx (i + 1)) := fun i => dGraph_isSome.1 (C.arc i)
  have hm := two_mul_le_card_input (by omega) C.periodic C.inj hl (fun i => .inl (harc i)) hk h
  have hqdvd : q ∣ C.len := (Dvd.intro_left 2 rfl).trans hdvd
  have hcnt : #{i ∈ range C.len | (C.vtx i).col = (C.vtx (i + 1)).col} ≤ C.len / q := by
    have hsub : {i ∈ range C.len | (C.vtx i).col = (C.vtx (i + 1)).col} ⊆ Ico 0 C.len := by
      intro i hi
      simpa using (mem_filter.1 hi).1
    have hmod : ∀ i, (C.vtx i).col = (C.vtx (i + 1)).col →
        psi (C.vtx 0) + i ≡ q - 1 [MOD q] := by
      intro i hi
      have h1 := ((psi_modEq hl harc i).of_mul_left 2).symm
      refine h1.trans ?_
      rcases ((psi_darc (harc i) (hl i) (hl (i + 1))).2.1 hi) with h2 | h2 <;> rw [h2]
      show (2 * q - 1) % q = (q - 1) % q
      rw [show 2 * q - 1 = q - 1 + q by omega, Nat.add_mod_right]
    have := Nat.card_le_ceilDiv_of_subset_Ico (q := q) (by omega) hsub (fun a ha b hb =>
      Nat.ModEq.add_left_cancel' _
        ((hmod a (mem_filter.1 ha).2).trans (hmod b (mem_filter.1 hb).2).symm))
    refine this.trans (Nat.ceilDiv_le_of_le_mul (by omega) ?_)
    rw [Nat.sub_zero, Nat.mul_div_cancel' hqdvd]
  rw [hw]
  have h2 : 2 * k ≤ C.len / q := hm.trans hcnt
  have h3 : 2 * k * q ≤ C.len := (Nat.le_div_iff_mul_le (by omega)).1 h2
  exact_mod_cast h3

/-- Claim 6.2(1) of [Chechik–Lifshitz–Mukhtar]: if the inputs intersect, the undirected graph has
a cycle of weight `2(q-1) + 2 Win` (the paper writes `2q + 2 Win`, counting `q` edges per pipe;
a pipe through `q` columns has `q - 1` edges). -/
theorem uGraph_mwc_of_inter (hq : 2 ≤ q) (hW : Win ≤ Wm) (hWt : Wt ≤ Wm) (hW1 : 1 ≤ Wm)
    (h : ∃ e, x e = true ∧ y e = true) :
    (uGraph (q := q) (d := d) (p := p) Wm Win Wt x y).mwc ≤
      ((2 * (q - 1) + 2 * Win : ℕ) : ℝ≥0∞) := by
  obtain ⟨⟨⟨u, w⟩, he⟩, hx, hy⟩ := h
  refine iInf_le_of_le (icycU (Wm := Wm) (Win := Win) (Wt := Wt) hq (u := u) (w := w)
    ⟨he, hx⟩ ⟨he, hy⟩) (le_of_eq ?_)
  have : (icycU (Wm := Wm) (Win := Win) (Wt := Wt) (d := d) (p := p) hq (u := u) (w := w)
      ⟨he, hx⟩ ⟨he, hy⟩).weight = 2 * (q - 1) + 2 * Win := by
    rw [WGraph.Cycle.weight, ← sum_icyc_ew (d := d) (p := p) (by omega) u w Win Wt]
    exact sum_congr rfl fun i _ =>
      uGraph_w hW hWt hW1 (.inl (icyc_arc (by omega) ⟨he, hx⟩ ⟨he, hy⟩ i))
  rw [this]

/-- Claim 6.2(2) of [Chechik–Lifshitz–Mukhtar], generalized as in §6.2: if the inputs are
disjoint, `H` has girth at least `2k` and the tree edges weigh at least `k · Win`, every cycle of
the undirected graph weighs at least `2k · Win`. -/
theorem uGraph_mwc_of_disj (k : ℕ) (_hq : 2 ≤ q) (hW : Win ≤ Wm) (hWt : Wt ≤ Wm)
    (hW1 : 1 ≤ Wm) (hk : ((2 * k : ℕ) : ℕ∞) ≤ (bipGraph E).egirth) (hkW : k * Win ≤ Wt)
    (h : ∀ e, ¬ (x e = true ∧ y e = true)) :
    ((2 * k * Win : ℕ) : ℝ≥0∞) ≤ (uGraph (q := q) (d := d) (p := p) Wm Win Wt x y).mwc := by
  refine le_iInf fun C => ?_
  have hadj : ∀ i, darc E x y (C.vtx i) (C.vtx (i + 1)) ∨ darc E x y (C.vtx (i + 1)) (C.vtx i) :=
    fun i => uGraph_isSome.1 (C.adj i)
  have hw : C.weight = ∑ i ∈ range C.len, ew Win Wt (C.vtx i) (C.vtx (i + 1)) :=
    sum_congr rfl fun i _ => uGraph_w hW hWt hW1 (hadj i)
  suffices 2 * k * Win ≤ C.weight by exact_mod_cast this
  have h3 := C.three_le_len
  rw [hw]
  by_cases hl : ∀ i, (C.vtx i).isLayer
  · have hm := two_mul_le_card_input h3 C.periodic C.inj hl hadj hk h
    calc 2 * k * Win ≤ #{i ∈ range C.len | (C.vtx i).col = (C.vtx (i + 1)).col} * Win :=
          Nat.mul_le_mul_right _ hm
      _ = ∑ i ∈ range C.len with (C.vtx i).col = (C.vtx (i + 1)).col, Win := by
          rw [sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ range C.len with (C.vtx i).col = (C.vtx (i + 1)).col,
            ew Win Wt (C.vtx i) (C.vtx (i + 1)) := by
          refine sum_le_sum fun i hi => ?_
          simp only [ew, hl i, hl (i + 1), (mem_filter.1 hi).2, and_self, ite_true, le_refl]
      _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)
  · push Not at hl
    obtain ⟨i, hi⟩ := hl
    have hg : ∀ n, (fun n => ew Win Wt (C.vtx n) (C.vtx (n + 1))) (n + C.len) =
        (fun n => ew Win Wt (C.vtx n) (C.vtx (n + 1))) n := by
      intro n
      simp only [C.periodic, Nat.add_right_comm n C.len 1]
    rw [← sum_shift _ hg (i + C.len - 1)]
    have h0 : ew Win Wt (C.vtx (i + C.len - 1 + 0)) (C.vtx (i + C.len - 1 + 0 + 1)) = Wt := by
      rw [show i + C.len - 1 + 0 + 1 = i + C.len by omega, C.periodic]
      rw [ew_comm]
      simp [ew, hi]
    have h1 : ew Win Wt (C.vtx (i + C.len - 1 + 1)) (C.vtx (i + C.len - 1 + 1 + 1)) = Wt := by
      rw [show i + C.len - 1 + 1 = i + C.len by omega, C.periodic]
      simp [ew, hi]
    have := Finset.add_le_sum (f := fun n => ew Win Wt (C.vtx (i + C.len - 1 + n))
      (C.vtx (i + C.len - 1 + n + 1))) (s := range C.len) (i := 0) (j := 1)
      (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega)) (mem_range.2 (by omega)) (by omega)
    rw [h0, h1] at this
    calc 2 * k * Win = 2 * (k * Win) := by ring
      _ ≤ Wt + Wt := by omega
      _ ≤ _ := this

end Podc.GirthApproxCongest
