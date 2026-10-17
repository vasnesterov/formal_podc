import Papers.PODC2013.CongestedCliqueRouting.SortAlg3Spec
import Papers.PODC2013.CongestedCliqueRouting.RoutingBox

/-!
# The sorting algorithm (Algorithm 4 of the paper) on `s²` nodes

Node set `V ≃ Fin s × Fin s`, `N = s²`. Every node holds at most `N` keys (pairwise distinct).
The key of global rank `r` must end up at node `out r` (for Problem 4.1: the node with index
`⌊r / n⌋`). The algorithm takes 32 rounds:

* round 0 (Step 2): every node selects every `s`-th of its keys (Step 1) and sends its `i`-th
  selected key to member `i` of group 0;
* rounds 1–6 (Step 3): group 0 sorts the samples with Algorithm 3;
* round 7 (Step 4): every `N`-th sample (in sorted order) is a delimiter; its holder broadcasts it;
* local (Step 5): every node splits its keys into `s` buckets by the delimiters;
* rounds 8–22 (Step 6): the keys of bucket `j` are spread evenly over the members of group `j`
  using the routing algorithm (Theorem 3.7, as a subroutine on a virtual clique of `4N` nodes,
  since a node may receive up to `3N` keys);
* rounds 23–28 (Step 7): every group sorts its keys with Algorithm 3;
* round 29: every node announces how many keys it holds;
* rounds 30–31 (Step 8): every key is sent to `out` of its global rank (Corollary 3.3 with a
  known pattern).
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace CongestedCliqueRouting

open Finset

/-- Parameters of the sorting algorithm. -/
structure SortSetup (I V M : Type*) (s : ℕ) where
  e : V ≃ Fin s × Fin s
  inp : I → V → Finset M
  out : ℕ → V

instance {s : ℕ} [NeZero s] : NeZero (2 * s) := ⟨by have := NeZero.ne s; omega⟩

namespace SortSetup

variable {I V M : Type*} [Fintype V] [DecidableEq V] [LinearOrder M] [Nonempty V] {s : ℕ}
  [NeZero s] (τ : SortSetup I V M s)

/-- All keys. -/
def U (d : I) : Finset M := univ.biUnion (τ.inp d)

/-- Hypotheses: at most `N` keys per node, distinct keys, at most `N` ranks per output node. -/
structure Good : Prop where
  card_le : ∀ d v, (τ.inp d v).card ≤ s * s
  disj : ∀ d u v, u ≠ v → Disjoint (τ.inp d u) (τ.inp d v)
  out_le : ∀ d w, ((range (τ.U d).card).filter fun r => τ.out r = w).card ≤ s * s

/-! ### Rounds 0–6 -/

/-- Samples of `v`: every `s`-th key. -/
def smp (d : I) (v : V) : Finset M := samples (τ.inp d v) s

/-- The `i`-th sample of `v`. -/
noncomputable def smpAt (d : I) (v : V) (i : Fin s) : Option M :=
  pick ((τ.smp d v).filter fun x => rk (τ.smp d v) x = i)

noncomputable def P0 (d : I) : V → V → Packet M SB := fun v w =>
  if grp τ.e w = 0 then ofList ((τ.smpAt d v (mem τ.e w)).toList.map Item.msg) else ofList []

/-- Keys held at the start of the first Algorithm 3. -/
noncomputable def A1 (d : I) (w : V) : Finset M := rcvd (τ.P0 d) w

/-! ### Round 7 -/

/-- All samples. -/
def Sig (d : I) : Finset M := univ.biUnion (τ.smp d)

/-- The delimiters: every `N`-th sample. -/
def G (d : I) : Finset M := delims (τ.Sig d) (s * s) s

noncomputable def B1 (d : I) (v : V) : Finset M := Alg3.Bk τ.e τ.A1 d v

/-- The delimiters among keys `H` of member `y`, computed from the group's count matrix `C`. -/
def loc7 (H : Finset M) (C : Fin s → Fin s → ℕ) (y : Fin s) : Finset M :=
  H.filter fun x =>
    ((∑ y' ∈ univ.filter (· < y), ∑ b, C b y') + rk H x) % (s * s) = s * s - 1 ∧
      (∑ y' ∈ univ.filter (· < y), ∑ b, C b y') + rk H x < (s - 1) * (s * s)

noncomputable def P7 (d : I) : V → V → Packet M SB := fun v _ =>
  ofList ((loc7 (τ.B1 d v) (Alg3.Cm τ.e τ.A1 d (grp τ.e v)) (mem τ.e v)).toList.map Item.msg)

/-! ### Rounds 8–22: routing -/

/-- Bucket of a key w.r.t. the delimiters. -/
def gam (d : I) (x : M) : ℕ := bucketOf (τ.G d) x

lemma gam_lt (d : I) (x : M) : τ.gam d x < s := by
  have := bucketOf_delims_le (U := τ.Sig d) (q := s * s) (k := s) x
  have := one_le_s (s := s)
  unfold gam G; omega

/-- Keys of `v` in bucket `j`. -/
def K (d : I) (v : V) (j : ℕ) : Finset M := (τ.inp d v).filter fun x => τ.gam d x = j

/-- Target of a key: member `(rank in its bucket) mod s` of the group of its bucket. -/
def tgt (d : I) (v : V) (x : M) : V :=
  node τ.e ⟨τ.gam d x, τ.gam_lt d x⟩
    ⟨rk (τ.K d v (τ.gam d x)) x % s, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne s))⟩

/-- Node numbering `V ≃ Fin N`. -/
def eV : V ≃ Fin (s * s) := τ.e.trans finProdFinEquiv

lemma hNpos : 0 < s * s := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne s))
  (Nat.pos_of_ne_zero (NeZero.ne s))
lemma hNle : s * s ≤ (2 * s) * (2 * s) := by nlinarith
lemma hFle : (2 * s) * (2 * s) ≤ 4 * (s * s) := by nlinarith

/-- The routing subroutine. -/
noncomputable def box : Run I V M SB :=
  boxRun τ.eV hNpos hNle hFle τ.inp τ.tgt

/-- Keys held at the start of the second Algorithm 3. -/
def A2 (d : I) (w : V) : Finset M := Recv τ.inp τ.tgt d w

/-! ### Rounds 23–31 -/

noncomputable def B2 (d : I) (v : V) : Finset M := Alg3.Bk τ.e τ.A2 d v

noncomputable def P29 (d : I) : V → V → Packet M SB := fun v _ =>
  ofList [Item.num (τ.B2 d v).card]

/-- Offset of node `v`: number of keys held by nodes with smaller number. -/
def offOf (L : V → ℕ) (v : V) : ℕ := ∑ w ∈ univ.filter (fun w => enc τ.e w < enc τ.e v), L w

/-- Number of keys `v` sends to `w` in the final step, computed from the counts `L`. -/
def fROf (L : V → ℕ) (v w : V) : ℕ :=
  ((Ico (τ.offOf L v) (τ.offOf L v + L v)).filter fun r => τ.out r = w).card

noncomputable def L (d : I) (v : V) : ℕ := (τ.B2 d v).card

noncomputable def fRp (d : I) : V → V → V → ℕ := splitParts V (τ.fROf (τ.L d)) 6

/-- Final target of a key held by `v`. -/
noncomputable def tgF (d : I) (v : V) (x : M) : V := τ.out (τ.offOf (τ.L d) v + rk (τ.B2 d v) x)

noncomputable def viaF (d : I) (v : V) : M → V :=
  assign (τ.B2 d v) (τ.tgF d v) fun w c => τ.fRp d c v w

noncomputable def P30 (d : I) : V → V → Packet M SB :=
  fun v c => rr1 (enc τ.e) (τ.B2 d v) (τ.viaF d v) (τ.tgF d v) c

noncomputable def P31 (d : I) : V → V → Packet M SB :=
  fun c w => rr2 (enc τ.e) (fun u => τ.P30 d u c) w

/-- Keys held at the end. -/
noncomputable def HF (d : I) (w : V) : Finset M := rcvd (τ.P31 d) w

/-- The intended run of the 32-round sorting algorithm. -/
noncomputable def run : Run I V M SB := fun d t =>
  if t = 0 then τ.P0 d
  else if t < 7 then Alg3.pkt τ.e τ.A1 d (t - 1)
  else if t = 7 then τ.P7 d
  else if t < 23 then τ.box d (t - 8)
  else if t < 29 then Alg3.pkt τ.e τ.A2 d (t - 23)
  else if t = 29 then τ.P29 d
  else if t = 30 then τ.P30 d
  else if t = 31 then τ.P31 d
  else fun _ _ => ofList []

lemma run_0 (d : I) : τ.run d 0 = τ.P0 d := by simp [run]
lemma run_alg1 (d : I) (k : ℕ) (hk : k < 6) : τ.run d (1 + k) = Alg3.pkt τ.e τ.A1 d k := by
  simp only [run]; rw [if_neg (by omega), if_pos (by omega)]; congr 1; omega
lemma run_7 (d : I) : τ.run d 7 = τ.P7 d := by simp [run]
lemma run_box (d : I) (r : ℕ) (hr : r < 15) : τ.run d (8 + r) = τ.box d r := by
  simp only [run]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega
lemma run_alg2 (d : I) (k : ℕ) (hk : k < 6) : τ.run d (23 + k) = Alg3.pkt τ.e τ.A2 d k := by
  simp only [run]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  congr 1; omega
lemma run_29 (d : I) : τ.run d 29 = τ.P29 d := by simp [run]
lemma run_30 (d : I) : τ.run d 30 = τ.P30 d := by simp [run]
lemma run_31 (d : I) : τ.run d 31 = τ.P31 d := by simp [run]

end SortSetup

end CongestedCliqueRouting
