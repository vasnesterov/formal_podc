import Papers.PODC2013.AsyncRendezvousPoly.Trajectories

/-!
# Algorithm RV-asynch-poly and the structure of its route

Dieudonné, Pelc, Villain, *How to meet asynchronously at polynomial cost*, PODC 2013
(arXiv:1301.7119v2), §3.1–3.2.

The agent with modified label `M(x) = (b₁ … b_s)` and start node `v` follows, for `k = 1, 2, …`
(iteration `k` of the `repeat` loop), for `i = 1, …, min(k, s)`: the segment `S_i(k)` (two atoms
`B(2k, v)` if `bᵢ = 1`, `A(4k, v)` if `bᵢ = 0`), followed by the border `K(k, v)` if `i < min(k, s)`
and by the fence `Ω(k, v)` otherwise. Its route is the infinite concatenation of these iterations
(`route`). Before the meeting the route of an agent depends only on the graph, its start node and
its label (the agent learns nothing else), so it is a fixed sequence of nodes.

In Lean, segments are indexed from `0` (`i = 0, …, min(k, s) - 1` is the paper's `i + 1`), and
iterations (= pieces/fences) from `1` as in the paper. Index functions (positions in the route,
in edge traversals from the start): `iS k` (start of the `k`-th piece `T(k)`), `segS k i` (start of
segment `S_{i+1}(k)`), `fS k` (start of the `k`-th fence `Ω(k)` = end of `T(k)`), and
`iS (k+1)` (end of `Ω(k)`).
-/

namespace Podc.AsyncRendezvousPoly

open Traj Finset

/-! ### Modified labels -/

/-- The length `|L|` of the binary representation of `L`. -/
def binLen (L : ℕ) : ℕ := (Nat.digits 2 L).length

/-- The binary representation of `L`, most significant bit first (`true` = 1). -/
def binDigits (L : ℕ) : List Bool := ((Nat.digits 2 L).map (fun d => decide (d = 1))).reverse

/-- The modified label `M(x) = (c₁c₁c₂c₂ … c_r c_r 0 1)` for `x = (c₁ … c_r)` the binary
representation of `L`. -/
def modLabel (L : ℕ) : List Bool := (binDigits L).flatMap (fun c => [c, c]) ++ [false, true]

/-! ### Infinite concatenation of closed trajectories -/

section InfConcat

variable {V : Type*}

/-- Offsets of an infinite sequence of blocks. -/
def offs (B : ℕ → Traj V) (t : ℕ) : ℕ := ∑ s ∈ range t, (B s).len

/-- The infinite concatenation `B 0 B 1 B 2 …` (of blocks with at least one edge). -/
def infConcat (B : ℕ → Traj V) (i : ℕ) : V :=
  (B (Nat.findGreatest (fun t => offs B t ≤ i) i)).f (i - offs B (Nat.findGreatest (fun t => offs B t ≤ i) i))

variable {B : ℕ → Traj V}

theorem offs_succ (t : ℕ) : offs B (t + 1) = offs B t + (B t).len := by
  simp [offs, sum_range_succ]

theorem le_offs (hpos : ∀ t, 1 ≤ (B t).len) (t : ℕ) : t ≤ offs B t := by
  induction t with
  | zero => simp [offs]
  | succ t ih => rw [offs_succ]; have := hpos t; omega

theorem offs_mono {t t' : ℕ} (h : t ≤ t') : offs B t ≤ offs B t' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [offs_succ]; omega

theorem findGreatest_offs (hpos : ∀ t, 1 ≤ (B t).len) {t i : ℕ} (h1 : offs B t ≤ i)
    (h2 : i < offs B (t + 1)) : Nat.findGreatest (fun t => offs B t ≤ i) i = t := by
  rw [Nat.findGreatest_eq_iff]
  refine ⟨le_trans (le_offs hpos t) h1, fun _ => h1, fun n hn _ hn' => ?_⟩
  have := offs_mono (B := B) (show t + 1 ≤ n by omega); omega

theorem occ_infConcat {v : V} (hB : ∀ t, (B t).ClosedAt v) (hpos : ∀ t, 1 ≤ (B t).len) (t : ℕ) :
    Occ (B t) (infConcat B) (offs B t) := fun δ hδ => by
  rcases hδ.lt_or_eq with hδ | rfl
  · unfold infConcat
    rw [findGreatest_offs (t := t) hpos (by omega) (by rw [offs_succ]; omega)]; congr 1; omega
  · unfold infConcat
    have h3 := hpos (t + 1)
    rw [findGreatest_offs (t := t + 1) hpos (by rw [offs_succ])
      (by rw [offs_succ, offs_succ]; omega)]
    rw [offs_succ, Nat.sub_self, (hB _).1, (hB _).2]

theorem isRoute_infConcat {G : SimpleGraph V} {v : V} (hB : ∀ t, (B t).ClosedAt v)
    (hpos : ∀ t, 1 ≤ (B t).len) (hw : ∀ t, (B t).IsWalk G) : IsRoute G (infConcat B) := by
  intro i
  set t := Nat.findGreatest (fun t => offs B t ≤ i) i
  have h1 : offs B t ≤ i := by
    have := Nat.findGreatest_spec (P := fun t => offs B t ≤ i) (m := 0) (Nat.zero_le i)
      (by simp [offs])
    exact this
  have h2 : i < offs B (t + 1) := by
    by_contra h
    by_cases ht : t + 1 ≤ i
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self t) ht (not_lt.1 h)
    · have := le_offs hpos (t + 1); omega
  rw [offs_succ] at h2
  have e1 := occ_infConcat hB hpos t (i - offs B t) (by omega)
  have e2 := occ_infConcat hB hpos t (i - offs B t + 1) (by omega)
  rw [show offs B t + (i - offs B t) = i by omega] at e1
  rw [show offs B t + (i - offs B t + 1) = i + 1 by omega] at e2
  rw [e1, e2]; exact hw t _ (by omega)

end InfConcat

/-! ### The iterations of the algorithm -/

section Lengths

variable (P : ℕ → ℕ) (bs : List Bool)

/-- Number of segments in iteration `k`: `min(k, s)`. -/
def nSeg (k : ℕ) : ℕ := min k bs.length

/-- The bit processed by segment `i` (`0`-indexed). -/
def bit (i : ℕ) : Bool := bs.getD i false

/-- Length of an atom: `|B(2k)|` for bit 1, `|A(4k)|` for bit 0. -/
def lenAtom (b : Bool) (k : ℕ) : ℕ := if b then lenB P (2 * k) else lenA P (4 * k)

/-- Length of the trajectory following segment `i`: border `K(k)` or fence `Ω(k)`. -/
def lenSep (k i : ℕ) : ℕ := if i + 1 < nSeg bs k then lenK P k else lenOm P k

/-- Length of segment `i` with the following border/fence. -/
def lenUnit (k i : ℕ) : ℕ := 2 * lenAtom P (bit bs i) k + lenSep P bs k i

/-- Length of iteration `k` (piece `T(k)` and fence `Ω(k)`). -/
def lenIt (k : ℕ) : ℕ := ∑ i ∈ range (nSeg bs k), lenUnit P bs k i

/-- Start of the `k`-th piece `T(k)` (`k ≥ 1`). -/
def iS (k : ℕ) : ℕ := ∑ t ∈ range (k - 1), lenIt P bs (t + 1)

/-- Start of segment `i` of iteration `k`. -/
def segS (k i : ℕ) : ℕ := iS P bs k + ∑ j ∈ range i, lenUnit P bs k j

/-- Start of the `k`-th fence `Ω(k)` (= end of the piece `T(k)`). -/
def fS (k : ℕ) : ℕ :=
  segS P bs k (nSeg bs k - 1) + 2 * lenAtom P (bit bs (nSeg bs k - 1)) k

theorem lenA_pos (hP : ∀ k, 1 ≤ P k) (k : ℕ) : 1 ≤ lenA P k := by
  unfold lenA lenA'; have := hP k; omega

theorem lenY_pos (hP : ∀ k, 1 ≤ P k) (k : ℕ) : 1 ≤ lenY P k := by
  unfold lenY lenY'; have := hP k; omega

theorem lenX_pos (hP : ∀ k, 1 ≤ P k) (k : ℕ) : 1 ≤ lenX P k := by
  unfold lenX; have := hP k; omega

theorem lenB_pos (hP : ∀ k, 1 ≤ P k) (k : ℕ) : 1 ≤ lenB P k := by
  unfold lenB; have := lenA_pos P hP (4 * k); have := lenY_pos P hP k
  exact one_le_mul (by omega) (by omega)

theorem lenAtom_pos (hP : ∀ k, 1 ≤ P k) (b : Bool) (k : ℕ) : 1 ≤ lenAtom P b k := by
  unfold lenAtom; split_ifs
  · exact lenB_pos P hP _
  · exact lenA_pos P hP _

theorem lenIt_pos (hP : ∀ k, 1 ≤ P k) (hbs : bs ≠ []) {k : ℕ} (hk : 1 ≤ k) : 1 ≤ lenIt P bs k := by
  unfold lenIt
  have hm : 0 < nSeg bs k := by
    unfold nSeg; have := List.length_pos_of_ne_nil hbs; omega
  calc 1 ≤ lenUnit P bs k 0 := by
          unfold lenUnit; have := lenAtom_pos P hP (bit bs 0) k; omega
    _ ≤ _ := single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.2 hm)

end Lengths

namespace Explorer

variable {V : Type*} {G : SimpleGraph V} {P : ℕ → ℕ} (E : Explorer G P)

/-- An atom: `B(2k, v)` for bit 1, `A(4k, v)` for bit 0. -/
def atom (b : Bool) (k : ℕ) (v : V) : Traj V := if b then E.B (2 * k) v else E.A (4 * k) v

/-- The border `K(k, v)` or the fence `Ω(k, v)` after segment `i`. -/
def sep (bs : List Bool) (k : ℕ) (v : V) (i : ℕ) : Traj V :=
  if i + 1 < nSeg bs k then E.K k v else E.Om k v

/-- Segment `i` of iteration `k` (two atoms) followed by its border/fence. -/
def unit (bs : List Bool) (k : ℕ) (v : V) (i : ℕ) : Traj V :=
  (E.atom (bit bs i) k v).append ((E.atom (bit bs i) k v).append (E.sep bs k v i))

/-- Iteration `k` of the `repeat` loop. -/
def It (bs : List Bool) (k : ℕ) (v : V) : Traj V := concatFn v (E.unit bs k v) (nSeg bs k)

/-- The route of an agent with modified label `bs` starting at `v`. -/
def route (bs : List Bool) (v : V) : ℕ → V := infConcat (fun t => E.It bs (t + 1) v)

theorem atom_closed (b : Bool) (k : ℕ) (v : V) : (E.atom b k v).ClosedAt v := by
  unfold atom; split_ifs
  · exact E.B_closed _ _
  · exact E.A_closed _ _

theorem atom_len (b : Bool) (k : ℕ) (v : V) : (E.atom b k v).len = lenAtom P b k := by
  unfold atom lenAtom; split_ifs
  · exact E.B_len _ _
  · exact E.A_len _ _

theorem atom_walk (b : Bool) (k : ℕ) (v : V) : (E.atom b k v).IsWalk G := by
  unfold atom; split_ifs
  · exact E.B_walk _ _
  · exact E.A_walk _ _

theorem sep_closed (bs : List Bool) (k : ℕ) (v : V) (i : ℕ) : (E.sep bs k v i).ClosedAt v := by
  unfold sep; split_ifs
  · exact E.K_closed _ _
  · exact E.Om_closed _ _

theorem sep_len (bs : List Bool) (k : ℕ) (v : V) (i : ℕ) :
    (E.sep bs k v i).len = lenSep P bs k i := by
  unfold sep lenSep; split_ifs
  · exact E.K_len _ _
  · exact E.Om_len _ _

theorem sep_walk (bs : List Bool) (k : ℕ) (v : V) (i : ℕ) : (E.sep bs k v i).IsWalk G := by
  unfold sep; split_ifs
  · exact E.K_walk _ _
  · exact E.Om_walk _ _

theorem unit_closed (bs : List Bool) (k : ℕ) (v : V) (i : ℕ) : (E.unit bs k v i).ClosedAt v := by
  have ha := E.atom_closed (bit bs i) k v
  have hs := E.sep_closed bs k v i
  refine ⟨by simp [unit, ha.1], ?_⟩
  unfold unit
  rw [append_f_len _ _ (by simp [ha.1, ha.2]), append_f_len _ _ (by rw [hs.1, ha.2]), hs.2]

theorem unit_len (bs : List Bool) (k : ℕ) (v : V) (i : ℕ) :
    (E.unit bs k v i).len = lenUnit P bs k i := by
  simp [unit, lenUnit, atom_len, sep_len]; ring

theorem unit_walk (bs : List Bool) (k : ℕ) (v : V) (i : ℕ) : (E.unit bs k v i).IsWalk G := by
  have ha := E.atom_closed (bit bs i) k v
  have hs := E.sep_closed bs k v i
  exact (E.atom_walk _ _ _).append ((E.atom_walk _ _ _).append (E.sep_walk _ _ _ _)
    (by rw [hs.1, ha.2])) (by simp [ha.1, ha.2])

theorem It_closed (bs : List Bool) (k : ℕ) (v : V) : (E.It bs k v).ClosedAt v :=
  concatFn_closed _ (E.unit_closed bs k v) _

theorem It_len (bs : List Bool) (k : ℕ) (v : V) : (E.It bs k v).len = lenIt P bs k := by
  simp [It, lenIt, concatFn_len, unit_len]

theorem It_walk (bs : List Bool) (k : ℕ) (v : V) : (E.It bs k v).IsWalk G :=
  IsWalk.concatFn (fun _ => v) _ (fun i => (E.unit_closed bs k v i).1)
    (fun i => (E.unit_closed bs k v i).2) _ (fun i _ => E.unit_walk bs k v i)

/-! ### Occurrences in the route -/

variable (bs : List Bool) (hbs : bs ≠ []) (v : V)
include hbs

omit hbs in
theorem iS_eq_offs (k : ℕ) :
    iS P bs k = offs (fun t => E.It bs (t + 1) v) (k - 1) := by
  simp [iS, offs, It_len]

theorem occ_It {k : ℕ} (hk : 1 ≤ k) : Occ (E.It bs k v) (E.route bs v) (iS P bs k) := by
  have := occ_infConcat (B := fun t => E.It bs (t + 1) v) (fun t => E.It_closed bs (t + 1) v)
    (fun t => by rw [It_len]; exact lenIt_pos P bs E.P_pos hbs (by omega)) (k - 1)
  rw [show k - 1 + 1 = k by omega] at this
  rwa [E.iS_eq_offs bs v k]

theorem isRoute_route : IsRoute G (E.route bs v) :=
  isRoute_infConcat (fun t => E.It_closed bs (t + 1) v)
    (fun t => by rw [It_len]; exact lenIt_pos P bs E.P_pos hbs (by omega)) (fun t => E.It_walk bs _ v)

theorem occ_unit {k i : ℕ} (hk : 1 ≤ k) (hi : i < nSeg bs k) :
    Occ (E.unit bs k v i) (E.route bs v) (segS P bs k i) := by
  have := (occIn_concatFn_closed (E.unit bs k v) (E.unit_closed bs k v) hi).occ
    (E.occ_It bs hbs v hk)
  simpa [segS, unit_len] using this

/-- The first atom of segment `i` of iteration `k`. -/
theorem occ_atom1 {k i : ℕ} (hk : 1 ≤ k) (hi : i < nSeg bs k) :
    Occ (E.atom (bit bs i) k v) (E.route bs v) (segS P bs k i) := by
  have := (occIn_append_left _ _).occ (E.occ_unit bs hbs v hk hi); simpa using this

/-- The second atom of segment `i` of iteration `k`. -/
theorem occ_atom2 {k i : ℕ} (hk : 1 ≤ k) (hi : i < nSeg bs k) :
    Occ (E.atom (bit bs i) k v) (E.route bs v) (segS P bs k i + lenAtom P (bit bs i) k) := by
  have ha := E.atom_closed (bit bs i) k v
  have := ((occIn_append_left _ (E.sep bs k v i)).trans
    (occIn_append_right _ _ (by simp [ha.1, ha.2]))).occ (E.occ_unit bs hbs v hk hi)
  simpa [atom_len] using this

theorem occ_sep {k i : ℕ} (hk : 1 ≤ k) (hi : i < nSeg bs k) :
    Occ (E.sep bs k v i) (E.route bs v) (segS P bs k i + 2 * lenAtom P (bit bs i) k) := by
  have ha := E.atom_closed (bit bs i) k v
  have hs := E.sep_closed bs k v i
  have := ((occIn_append_right _ _ (by rw [hs.1, ha.2])).trans
    (occIn_append_right _ _ (by simp [ha.1, ha.2]))).occ (E.occ_unit bs hbs v hk hi)
  rw [show segS P bs k i + ((E.atom (bit bs i) k v).len + (E.atom (bit bs i) k v).len)
    = segS P bs k i + 2 * lenAtom P (bit bs i) k by rw [atom_len]; ring] at this
  exact this

/-- The border `K_{i,i+1}(k)` (paper's numbering) repeats `X(k, v)`. -/
theorem rep_border {k i : ℕ} (hk : 1 ≤ k) (hi : i + 1 < nSeg bs k) :
    RepOcc (E.R k v) (2 * (lenB P (4 * k) + lenA P (8 * k)))
      (segS P bs k i + 2 * lenAtom P (bit bs i) k) (E.route bs v) := by
  have := E.occ_sep bs hbs v hk (by omega : i < nSeg bs k)
  simp only [sep, hi, ↓reduceIte] at this
  exact E.K_rep this

/-- The fence `Ω(k)` repeats `X(k, v)`. -/
theorem rep_fence {k : ℕ} (hk : 1 ≤ k) :
    RepOcc (E.R k v) ((2 * k - 1) * lenK P k) (fS P bs k) (E.route bs v) := by
  have hm : 0 < nSeg bs k := by
    unfold nSeg; have := List.length_pos_of_ne_nil hbs; omega
  have := E.occ_sep bs hbs v hk (show nSeg bs k - 1 < nSeg bs k by omega)
  simp only [sep, show ¬ (nSeg bs k - 1 + 1 < nSeg bs k) by omega, ↓reduceIte] at this
  exact E.Om_rep this

end Explorer

end Podc.AsyncRendezvousPoly
