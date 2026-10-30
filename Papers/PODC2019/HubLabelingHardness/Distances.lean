import Papers.PODC2019.HubLabelingHardness.Degree

/-!
# Distances in `G_{b,ℓ}`

* `edist_main_le_wlen`: distances in `G_{b,ℓ}` between vertices of `H_{b,ℓ}` are at most the
  weighted `H`-distances (every `H`-edge of weight `w` becomes a `G`-path of length `w`).
* `pot x`: an integer potential on `G_{b,ℓ}` changing by at most `1` along every edge, with
  `pot x v_{0,x} = 0` and `pot x v_{ℓ,j} = ℓA + Σ_k (j_k - x_k)²`; it lower-bounds the distance from
  `v_{0,x}`. Composing with the level reflection `refl` (a graph homomorphism) gives the potential
  for the top vertex `v_{2ℓ,z}`.
* The level-`ℓ` vertices separate the bottom from the top (`exists_mem_support_midLevel`).
* `lopt_le_length`, `midl_mem_support_G`: every `v_{0,x}`–`v_{2ℓ,z}` walk of `G_{b,ℓ}` has length
  `≥ Lopt x z`, and each one of length `≤ Lopt x z` visits `v_{ℓ,(x+z)/2}` (Lemma 2.2 for `G`).
-/

namespace Podc.HubLabelingHardness

open SimpleGraph Finset GV

variable {b ℓ : ℕ}

/-! ## Basic facts -/

lemma side_ge (b : ℕ) : b + 1 ≤ side b := Nat.lt_two_pow_self

lemma sqd_le_int (a c : Fin (side b)) : (sqd a c : ℤ) ≤ ((side b : ℤ) - 1) ^ 2 := by
  rw [sqd_cast]
  have ha := a.2; have hc := c.2
  have h1 : ((a : ℕ) : ℤ) - c ≤ (side b : ℤ) - 1 := by omega
  have h2 : -((side b : ℤ) - 1) ≤ ((a : ℕ) : ℤ) - c := by omega
  nlinarith

/-- `A ≥ 2b + 4`: the paths replacing edges have at least two edges. -/
lemma bigA_ge (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) : 2 * b + 4 ≤ bigA b ℓ := by
  have hs := side_ge b
  have h3 : 3 * side b ^ 2 ≤ bigA b ℓ := by
    unfold bigA; nlinarith
  nlinarith

lemma plen_add (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) (i : Fin (2 * ℓ)) (j : Vec b ℓ) (t : Fin (side b)) :
    plen b ℓ i j t + 2 * b + 2 = bigA b ℓ + sqd (j (cc i)) t := by
  have := bigA_ge hb hℓ; unfold plen; omega

lemma E.ne {a c : GV b ℓ} (h : E b ℓ a c) : a ≠ c := by
  cases h with
  | inChild i j n m h => intro h'; cases h'; omega
  | outChild i j n m h => intro h'; cases h'; omega
  | pathStep i j t p q h => intro h'; cases h'; omega
  | _ => intro h'; cases h'

lemma E.adj {a c : GV b ℓ} (h : E b ℓ a c) : (G b ℓ).Adj a c := ⟨h.ne, Or.inl h⟩

lemma edist_le_one_of_E {a c : GV b ℓ} (h : E b ℓ a c) : (G b ℓ).edist a c ≤ 1 := by
  simpa using (Walk.cons h.adj Walk.nil).edist_le

/-! ## Upper bounds -/

/-- Depth of heap node `n`. -/
def dep (n : ℕ) : ℕ := Nat.log 2 (n + 1)

lemma dep_child {n m : ℕ} (h : m = 2 * n + 1 ∨ m = 2 * n + 2) : dep m = dep n + 1 := by
  unfold dep
  have h2 : (m + 1) / 2 = n + 1 := by omega
  have hpos : 0 < Nat.log 2 (m + 1) := Nat.log_pos (by norm_num) (by omega)
  have := Nat.log_div_base 2 (m + 1)
  rw [h2] at this
  omega

lemma dep_leaf (t : Fin (side b)) : dep (leaf t).val = b := by
  unfold dep leaf
  simp only
  rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, by omega⟩)]
  have := t.2
  have h1 := one_le_side b
  constructor
  · simp only [side] at *; omega
  · simp only [side] at *; rw [pow_succ]; omega

@[simp] lemma dep_root : dep (root b).val = 0 := by simp [dep, root]

lemma edist_tin_root_le (i : Fin (2 * ℓ)) (j : Vec b ℓ) (n : Fin (2 * side b - 1)) :
    (G b ℓ).edist (tin i j (root b)) (tin i j n) ≤ dep n := by
  obtain ⟨n, hn⟩ := n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [root]
    · set m : Fin (2 * side b - 1) := ⟨(n - 1) / 2, by omega⟩
      have hm : n = 2 * m.val + 1 ∨ n = 2 * m.val + 2 := by simp only [m]; omega
      have hE : E b ℓ (tin i j m) (tin i j ⟨n, hn⟩) := E.inChild i j m ⟨n, hn⟩ hm
      calc (G b ℓ).edist (tin i j (root b)) (tin i j ⟨n, hn⟩)
          ≤ (G b ℓ).edist (tin i j (root b)) (tin i j m) + (G b ℓ).edist (tin i j m) (tin i j ⟨n, hn⟩) :=
            SimpleGraph.edist_triangle
        _ ≤ dep m + 1 := add_le_add (ih _ (by show (n - 1) / 2 < n; omega) _) (edist_le_one_of_E hE)
        _ = dep n := by rw [dep_child hm]; push_cast; rfl

lemma edist_tout_root_le (i : Fin (2 * ℓ)) (j : Vec b ℓ) (n : Fin (2 * side b - 1)) :
    (G b ℓ).edist (tout i j (root b)) (tout i j n) ≤ dep n := by
  obtain ⟨n, hn⟩ := n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [root]
    · set m : Fin (2 * side b - 1) := ⟨(n - 1) / 2, by omega⟩
      have hm : n = 2 * m.val + 1 ∨ n = 2 * m.val + 2 := by simp only [m]; omega
      have hE : E b ℓ (tout i j m) (tout i j ⟨n, hn⟩) := E.outChild i j m ⟨n, hn⟩ hm
      calc (G b ℓ).edist (tout i j (root b)) (tout i j ⟨n, hn⟩)
          ≤ (G b ℓ).edist (tout i j (root b)) (tout i j m) +
              (G b ℓ).edist (tout i j m) (tout i j ⟨n, hn⟩) := SimpleGraph.edist_triangle
        _ ≤ dep m + 1 := add_le_add (ih _ (by show (n - 1) / 2 < n; omega) _) (edist_le_one_of_E hE)
        _ = dep n := by rw [dep_child hm]; push_cast; rfl

lemma edist_mid_le (i : Fin (2 * ℓ)) (j : Vec b ℓ) (t : Fin (side b))
    (p q : Fin (plen b ℓ i j t - 1)) (hpq : p.val ≤ q.val) :
    (G b ℓ).edist (mid i j t p) (mid i j t q) ≤ (q.val - p.val : ℕ) := by
  obtain ⟨q, hq⟩ := q
  induction q with
  | zero =>
    have : p = ⟨0, hq⟩ := Fin.ext (by simp at hpq; omega)
    subst this; simp
  | succ q ih =>
    rcases Nat.eq_or_lt_of_le hpq with h | h
    · have : p = ⟨q + 1, hq⟩ := Fin.ext h
      subst this; simp
    · have hE : E b ℓ (mid i j t ⟨q, by omega⟩) (mid i j t ⟨q + 1, hq⟩) :=
        E.pathStep i j t _ _ rfl
      calc (G b ℓ).edist (mid i j t p) (mid i j t ⟨q + 1, hq⟩)
          ≤ (G b ℓ).edist (mid i j t p) (mid i j t ⟨q, by omega⟩) +
              (G b ℓ).edist (mid i j t ⟨q, by omega⟩) (mid i j t ⟨q + 1, hq⟩) := SimpleGraph.edist_triangle
        _ ≤ ((q - p.val : ℕ) : ℕ∞) + 1 :=
            add_le_add (ih (by omega) (Nat.lt_succ_iff.mp h)) (edist_le_one_of_E hE)
        _ = ((q + 1 - p.val : ℕ) : ℕ∞) := by
            simp only at h; rw [show q + 1 - p.val = (q - p.val) + 1 by omega]; push_cast; rfl

/-- An `H`-edge from `v_{i,j}` up to `v_{i+1,j[c ↦ t]}` of weight `w` is a `G`-path of length `w`. -/
lemma edist_up_le (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) (i : Fin (2 * ℓ)) (j : Vec b ℓ) (t : Fin (side b)) :
    (G b ℓ).edist (main i.castSucc j) (main i.succ (Function.update j (cc i) t)) ≤
      (bigA b ℓ + sqd (j (cc i)) t : ℕ) := by
  have h2 := two_le_plen hb hℓ i j t
  have hadd := plen_add hb hℓ i j t
  set j' := Function.update j (cc i) t
  set p0 : Fin (plen b ℓ i j t - 1) := ⟨0, by omega⟩
  set pl : Fin (plen b ℓ i j t - 1) := ⟨plen b ℓ i j t - 2, by omega⟩
  have e1 := edist_le_one_of_E (E.outRoot i j)
  have e2 := edist_tout_root_le i j (leaf t)
  have e3 := edist_le_one_of_E (E.pathStart i j t p0 rfl)
  have e4 := edist_mid_le i j t p0 pl (by simp [p0])
  have e5 := edist_le_one_of_E (E.pathEnd i j t pl (by simp only [pl]; omega))
  have e6 := edist_tin_root_le i j' (leaf (j (cc i)))
  rw [SimpleGraph.edist_comm] at e6
  have e7 := edist_le_one_of_E (E.inRoot i j')
  rw [SimpleGraph.edist_comm] at e7
  rw [dep_leaf] at e2 e6
  have := ((SimpleGraph.edist_triangle).trans (add_le_add e1 ((SimpleGraph.edist_triangle).trans (add_le_add e2
    ((SimpleGraph.edist_triangle).trans (add_le_add e3 ((SimpleGraph.edist_triangle).trans (add_le_add e4
    ((SimpleGraph.edist_triangle).trans (add_le_add e5 ((SimpleGraph.edist_triangle).trans (add_le_add e6 e7))))))))))))
  refine this.trans (le_of_eq ?_)
  simp only [p0, pl]
  rw [← hadd]
  norm_cast
  omega

/-- `G`-distances between vertices of `H` are at most the weighted `H`-distances. -/
theorem edist_main_le_wlen (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) {u v : Main b ℓ} (q : (H b ℓ).Walk u v) :
    (G b ℓ).edist (main u.1 u.2) (main v.1 v.2) ≤ wlen q := by
  induction q with
  | nil => simp
  | @cons u v w h q ih =>
    refine (SimpleGraph.edist_triangle (v := main v.1 v.2)).trans ?_
    rw [wlen_cons, Nat.cast_add]
    refine add_le_add ?_ ih
    -- one edge
    have key : ∀ u v : Main b ℓ, v.1.val = u.1.val + 1 →
        (∀ k : Fin ℓ, k.val ≠ cnat ℓ u.1.val → v.2 k = u.2 k) →
        (G b ℓ).edist (main u.1 u.2) (main v.1 v.2) ≤ hw b ℓ u v := by
      rintro ⟨ui, uj⟩ ⟨vi, vj⟩ hlev hagree
      simp only at hlev hagree ⊢
      set i : Fin (2 * ℓ) := ⟨ui.val, by omega⟩
      have hu : ui = i.castSucc := Fin.ext rfl
      have hv : vi = i.succ := Fin.ext (by simp [i, hlev])
      have hvj : vj = Function.update uj (cc i) (vj (cc i)) := by
        funext k
        by_cases hk : k = cc i
        · subst hk; simp
        · rw [Function.update_of_ne hk]
          exact hagree k (fun h => hk (Fin.ext (by simp [i, h])))
      have hw' : hw b ℓ (ui, uj) (vi, vj) = bigA b ℓ + sqd (uj (cc i)) (vj (cc i)) := by
        unfold hw
        congr 1
        rw [Finset.sum_eq_single (cc i)]
        · intro k _ hk
          simp only; rw [hvj, Function.update_of_ne hk, sqd_self]
        · simp
      rw [hw', hu, hv, hvj]
      have := edist_up_le hb hℓ i uj (vj (cc i))
      simpa using this
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key u v h1 h2
    · rw [SimpleGraph.edist_comm, hw_comm]; exact key v u h1 h2

/-! ## The potential -/

lemma iteT {α : Type*} {p : Prop} [Decidable p] {a c : α} (h : p) : (if p then a else c) = a := by
  simp [h]

lemma iteF {α : Type*} {p : Prop} [Decidable p] {a c : α} (h : ¬ p) : (if p then a else c) = c := by
  simp [h]

/-- `d_k = j_k - x_k`. -/
def dd (x j : Vec b ℓ) (k : Fin ℓ) : ℤ := ((j k : ℕ) : ℤ) - ((x k : ℕ) : ℤ)

/-- The correction term for coordinates that still have to change: `g(d) = 2(s-1)|d| - d²`. -/
def gf (b : ℕ) (d : ℤ) : ℤ := 2 * ((side b : ℤ) - 1) * |d| - d ^ 2

/-- The potential on vertices of `H`: `min(i,ℓ)·A + Σ_{k<i} d_k² + Σ_{k≥i} g(d_k)`. -/
def phi (x : Vec b ℓ) (i : ℕ) (j : Vec b ℓ) : ℤ :=
  ((min i ℓ : ℕ) : ℤ) * (bigA b ℓ : ℤ) +
    ∑ k : Fin ℓ, if k.val < i then dd x j k ^ 2 else gf b (dd x j k)

/-- The potential on `G_{b,ℓ}` (a lower bound on the distance from `v_{0,x}`). -/
def pot (x : Vec b ℓ) : GV b ℓ → ℤ
  | main i j => phi x i j
  | tin i j n => phi x (i + 1) j - (dep n + 1)
  | tout i j n => phi x i j + (dep n + 1)
  | mid i j t p => min (phi x i j + b + 1 + (p + 1))
      (phi x (i + 1) (Function.update j (cc i) t) - (b + 1) + ((plen b ℓ i j t : ℤ) - 1 - p))

lemma phi_zero (x : Vec b ℓ) : phi x 0 x = 0 := by
  simp [phi, dd, gf]

lemma phi_ell (x j : Vec b ℓ) : phi x ℓ j = (ℓ : ℤ) * bigA b ℓ + ∑ k, dd x j k ^ 2 := by
  simp [phi]

lemma dd_bound (x j : Vec b ℓ) (k : Fin ℓ) :
    -((side b : ℤ) - 1) ≤ dd x j k ∧ dd x j k ≤ (side b : ℤ) - 1 := by
  have := (x k).2; have := (j k).2; unfold dd; omega

/-- The difference of the potential across an `H`-edge (as a single coordinate change). -/
lemma phi_step (x : Vec b ℓ) (i : Fin (2 * ℓ)) (j : Vec b ℓ) (t : Fin (side b)) :
    phi x (i + 1) (Function.update j (cc i) t) - phi x i j =
      (if i.val < ℓ then (bigA b ℓ : ℤ) + dd x (Function.update j (cc i) t) (cc i) ^ 2 - gf b (dd x j (cc i))
       else dd x (Function.update j (cc i) t) (cc i) ^ 2 - dd x j (cc i) ^ 2) := by
  set j' := Function.update j (cc i) t
  have hj' : ∀ k, k ≠ cc i → dd x j' k = dd x j k := by
    intro k hk; simp [j', dd, Function.update_of_ne hk]
  unfold phi
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (cc i)),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (cc i))]
  have hrest : ∑ k ∈ univ.erase (cc i), (if k.val < i.val + 1 then dd x j' k ^ 2 else gf b (dd x j' k)) =
      ∑ k ∈ univ.erase (cc i), (if k.val < i.val then dd x j k ^ 2 else gf b (dd x j k)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.ne_of_mem_erase hk
    rw [hj' k hk']
    have : k.val ≠ i.val ∨ ¬ i.val < ℓ := by
      by_contra hc
      push Not at hc
      exact hk' (Fin.ext (by simp [cnat, hc.2, hc.1]))
    by_cases h1 : k.val < i.val
    · rw [iteT (by omega), iteT h1]
    · rcases this with h | h
      · rw [iteF (by omega), iteF h1]
      · exfalso; have := k.2; omega
  rw [hrest]
  have hc := cc_val i
  by_cases hi : i.val < ℓ
  · have hci : (cc i).val = i.val := by simp [cnat, hi]
    rw [iteT hi, iteT (by omega), iteF (by omega)]
    rw [show min (i.val + 1) ℓ = i.val + 1 by omega, show min i.val ℓ = i.val by omega]
    push_cast; ring
  · have hci : (cc i).val < ℓ := (cc i).2
    rw [iteF hi, iteT (by omega), iteT (by omega)]
    rw [show min (i.val + 1) ℓ = ℓ by omega, show min i.val ℓ = ℓ by omega]
    ring

/-- (K1) and (K2): the potential changes across an `H`-edge of weight `w` by at most `w` upwards
and at most `w - 4b - 4` downwards. -/
lemma phi_step_bounds (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) (x : Vec b ℓ) (i : Fin (2 * ℓ)) (j : Vec b ℓ)
    (t : Fin (side b)) :
    phi x (i + 1) (Function.update j (cc i) t) - phi x i j ≤ bigA b ℓ + sqd (j (cc i)) t ∧
    phi x i j - phi x (i + 1) (Function.update j (cc i) t) ≤
      (bigA b ℓ : ℤ) + sqd (j (cc i)) t - 4 * b - 4 := by
  have hstep := phi_step x i j t
  have hd := dd_bound x j (cc i)
  have hd' := dd_bound x (Function.update j (cc i) t) (cc i)
  have hsq : (sqd (j (cc i)) t : ℤ) = (dd x (Function.update j (cc i) t) (cc i) - dd x j (cc i)) ^ 2 := by
    rw [sqd_cast]; simp [dd]; ring
  set d := dd x j (cc i)
  set d' := dd x (Function.update j (cc i) t) (cc i)
  have hs : ((b : ℤ) + 1) ≤ side b := by exact_mod_cast side_ge b
  have hA : (bigA b ℓ : ℤ) = 3 * ℓ * (side b : ℤ) ^ 2 := by simp [bigA]
  have hℓ' : (1 : ℤ) ≤ ℓ := by exact_mod_cast hℓ
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hA3 : 3 * (side b : ℤ) ^ 2 ≤ bigA b ℓ := by rw [hA]; nlinarith
  rw [hsq]
  split_ifs at hstep with hi
  · unfold gf at hstep
    rcases abs_cases d with ⟨had, _⟩ | ⟨had, _⟩ <;> rw [had] at hstep <;> constructor <;> nlinarith
  · constructor <;> nlinarith

lemma abs_min_sub_le {X Y : ℤ} (h : X - 1 ≤ Y) : |X - min (X + 1) Y| ≤ 1 := by
  rw [abs_le]; constructor <;> [skip; skip] <;> rcases min_cases (X + 1) Y with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rw [h1] <;> omega

/-- The potential changes by at most one along every edge of `G_{b,ℓ}`. -/
lemma abs_pot_sub_le (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) (x : Vec b ℓ) {a c : GV b ℓ} (h : E b ℓ a c) :
    |pot x a - pot x c| ≤ 1 := by
  cases h with
  | inRoot i j => simp [pot]
  | outRoot i j => simp [pot]
  | inChild i j n m h => simp only [pot]; rw [dep_child h]; push_cast; rw [abs_le]; omega
  | outChild i j n m h => simp only [pot]; rw [dep_child h]; push_cast; rw [abs_le]; omega
  | pathStart i j t p hp =>
    simp only [pot, dep_leaf, hp]
    have := (phi_step_bounds hb hℓ x i j t).2
    have hpl := plen_add hb hℓ i j t
    have hpl' : (plen b ℓ i j t : ℤ) + 2 * b + 2 = bigA b ℓ + sqd (j (cc i)) t := by exact_mod_cast hpl
    push_cast
    rw [abs_le]; constructor <;> omega
  | pathStep i j t p q h =>
    simp only [pot, h]
    push_cast
    rw [abs_le]; constructor <;>
    rcases min_cases (phi x (↑i) j + ↑b + 1 + (↑↑p + 1))
      (phi x (↑i + 1) (Function.update j (cc i) t) - (↑b + 1) + (↑(plen b ℓ i j t) - 1 - ↑↑p)) with
      ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases min_cases (phi x (↑i) j + ↑b + 1 + (↑↑p + 1 + 1))
      (phi x (↑i + 1) (Function.update j (cc i) t) - (↑b + 1) + (↑(plen b ℓ i j t) - 1 - (↑↑p + 1))) with
      ⟨h2, _⟩ | ⟨h2, _⟩ <;> rw [h1, h2] <;> omega
  | pathEnd i j t p hp =>
    simp only [pot, dep_leaf]
    have := (phi_step_bounds hb hℓ x i j t).1
    have hpl := plen_add hb hℓ i j t
    have hpl' : (plen b ℓ i j t : ℤ) + 2 * b + 2 = bigA b ℓ + sqd (j (cc i)) t := by exact_mod_cast hpl
    have hp' : (p.val : ℤ) + 2 = plen b ℓ i j t := by exact_mod_cast hp
    rw [abs_le]; constructor <;> rcases min_cases (phi x (↑i) j + ↑b + 1 + (↑↑p + 1))
      (phi x (↑i + 1) (Function.update j (cc i) t) - (↑b + 1) + (↑(plen b ℓ i j t) - 1 - ↑↑p)) with
      ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> omega

lemma pot_le_of_adj (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) (x : Vec b ℓ) {a c : GV b ℓ} (h : (G b ℓ).Adj a c) :
    pot x c ≤ pot x a + 1 := by
  rcases h.2 with h | h
  · have := abs_pot_sub_le hb hℓ x h; rw [abs_le] at this; omega
  · have := abs_pot_sub_le hb hℓ x h; rw [abs_le] at this; omega

/-- A potential growing by at most one per edge bounds walk lengths from below (`ℤ`-valued). -/
lemma Walk.le_add_length_of_lipschitz_int {V : Type*} {G' : SimpleGraph V} {f : V → ℤ}
    (hf : ∀ a c, G'.Adj a c → f c ≤ f a + 1) {a c : V} (p : G'.Walk a c) :
    f c ≤ f a + p.length := by
  induction p with
  | nil => simp
  | cons h p ih => have := hf _ _ h; simp only [Walk.length_cons]; push_cast; omega

/-! ## The level reflection `i ↦ 2ℓ - i` -/

lemma cc_rev (i : Fin (2 * ℓ)) : cc i.rev = cc i := by
  ext; simp only [cc_val, Fin.val_rev, cnat]; split_ifs <;> omega

lemma plen_rev (i : Fin (2 * ℓ)) (j : Vec b ℓ) (t : Fin (side b)) :
    plen b ℓ i.rev (Function.update j (cc i) t) (j (cc i)) = plen b ℓ i j t := by
  simp [plen, cc_rev, sqd_comm]

/-- The reflection of `G_{b,ℓ}` exchanging levels `i` and `2ℓ - i` (and in- and out-trees). -/
def refl : GV b ℓ → GV b ℓ
  | main i j => main i.rev j
  | tin i j n => tout i.rev j n
  | tout i j n => tin i.rev j n
  | mid i j t p => mid i.rev (Function.update j (cc i) t) (j (cc i))
      ⟨plen b ℓ i j t - 2 - p, by rw [plen_rev]; have := p.2; omega⟩

/-- The reflection is a graph homomorphism. -/
lemma refl_adj_of_E {a c : GV b ℓ} (h : E b ℓ a c) : (G b ℓ).Adj (refl a) (refl c) := by
  cases h with
  | inRoot i j =>
    simp only [refl]; rw [Fin.rev_succ]; exact (E.outRoot i.rev j).adj
  | outRoot i j =>
    simp only [refl]; rw [Fin.rev_castSucc]; exact (E.inRoot i.rev j).adj
  | inChild i j n m h => exact (E.outChild i.rev j n m h).adj
  | outChild i j n m h => exact (E.inChild i.rev j n m h).adj
  | pathStart i j t p hp =>
    simp only [refl]
    have hE := E.pathEnd i.rev (Function.update j (cc i) t) (j (cc i))
      ⟨plen b ℓ i j t - 2 - p, by rw [plen_rev]; have := p.2; omega⟩
      (by simp only; rw [plen_rev]; have := p.2; omega)
    have key : tin i.rev (Function.update (Function.update j (cc i) t) (cc i.rev) (j (cc i)))
        (leaf ((Function.update j (cc i) t) (cc i.rev))) = tin i.rev j (leaf t) := by
      simp [cc_rev]
    rw [key] at hE
    exact hE.adj.symm
  | pathStep i j t p q h =>
    simp only [refl]
    refine (E.pathStep _ _ _ _ _ ?_).adj.symm
    simp only; have := q.2; omega
  | pathEnd i j t p hp =>
    simp only [refl]
    exact (E.pathStart i.rev (Function.update j (cc i) t) (j (cc i))
      ⟨plen b ℓ i j t - 2 - p, by rw [plen_rev]; have := p.2; omega⟩ (by simp only; omega)).adj.symm

lemma refl_adj {a c : GV b ℓ} (h : (G b ℓ).Adj a c) : (G b ℓ).Adj (refl a) (refl c) := by
  rcases h.2 with h | h
  · exact refl_adj_of_E h
  · exact (refl_adj_of_E h).symm

/-! ## Lower bounds from the potentials -/

/-- Distance lower bound from `v_{0,x}`: `ℓA + Σ_k (j_k - x_k)² ≤` any walk length to `v_{ℓ,j}`. -/
lemma pot_bot_le (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) (x j : Vec b ℓ)
    (p : (G b ℓ).Walk (main 0 x) (main ⟨ℓ, by omega⟩ j)) :
    (ℓ : ℤ) * bigA b ℓ + ∑ k, dd x j k ^ 2 ≤ p.length := by
  have := Walk.le_add_length_of_lipschitz_int (f := pot x) (fun a c h => pot_le_of_adj hb hℓ x h) p
  simpa [pot, phi_zero, phi_ell] using this

/-- Distance lower bound to `v_{2ℓ,z}`, via the reflection. -/
lemma pot_top_le (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) (z j : Vec b ℓ)
    (p : (G b ℓ).Walk (main ⟨ℓ, by omega⟩ j) (main (Fin.last _) z)) :
    (ℓ : ℤ) * bigA b ℓ + ∑ k, dd z j k ^ 2 ≤ p.length := by
  have := Walk.le_add_length_of_lipschitz_int (f := fun a => pot z (refl a))
    (fun a c h => pot_le_of_adj hb hℓ z (refl_adj h)) p.reverse
  have h1 : (Fin.last (2 * ℓ)).rev = 0 := by ext; simp
  have h2 : (⟨ℓ, by omega⟩ : Fin (2 * ℓ + 1)).rev = ⟨ℓ, by omega⟩ := by ext; simp; omega
  simpa [refl, pot, h1, h2, phi_zero, phi_ell] using this

/-! ## The level-`ℓ` vertices separate the bottom from the top -/

/-- Lower side of the cut at level `ℓ`. -/
def low : GV b ℓ → Prop
  | main i _ => i.val ≤ ℓ
  | tin i _ _ => i.val < ℓ
  | tout i _ _ => i.val < ℓ
  | mid i _ _ _ => i.val < ℓ

lemma low_iff_of_E {a c : GV b ℓ} (h : E b ℓ a c) :
    (low a ↔ low c) ∨ ∃ j, a = main ⟨ℓ, by omega⟩ j := by
  cases h with
  | outRoot i j =>
    by_cases hi : i.val = ℓ
    · right; exact ⟨j, by congr 1; ext; simp [hi]⟩
    · left; simp only [low, Fin.val_castSucc]; omega
  | inRoot i j => left; simp only [low, Fin.val_succ]; omega
  | _ => left; simp [low]

lemma exists_mem_support_midLevel {a c : GV b ℓ} (p : (G b ℓ).Walk a c) (ha : low a)
    (hc : ¬ low c) : ∃ j, main ⟨ℓ, by omega⟩ j ∈ p.support := by
  induction p with
  | nil => exact absurd ha hc
  | @cons a a' c h p ih =>
    by_cases ha' : low a'
    · obtain ⟨j, hj⟩ := ih ha' hc
      exact ⟨j, by simp [hj]⟩
    · rcases h.2 with h | h
      · rcases low_iff_of_E h with h' | ⟨j, rfl⟩
        · exact absurd (h'.1 ha) ha'
        · exact ⟨j, by simp⟩
      · rcases low_iff_of_E h with h' | ⟨j, rfl⟩
        · exact absurd (h'.2 ha) ha'
        · exact ⟨j, by simp⟩

/-! ## Lemma 2.2 for `G_{b,ℓ}` -/

lemma two_midpt_eq {x z : Vec b ℓ} (hxz : EvenDiff x z) (k : Fin ℓ) :
    2 * ((midpt x z k : ℕ) : ℤ) = (x k : ℕ) + (z k : ℕ) := by
  obtain ⟨r, hr⟩ := hxz k
  simp only [midpt]
  omega

/-- The core inequality: through a level-`ℓ` vertex `v_{ℓ,j}` the two potential bounds add up to
`Lopt x z + 2 Σ_k (j_k - m_k)²`, `m = (x + z)/2`. -/
lemma pot_sum_eq {x z : Vec b ℓ} (hxz : EvenDiff x z) (j : Vec b ℓ) :
    ((ℓ : ℤ) * bigA b ℓ + ∑ k, dd x j k ^ 2) + ((ℓ : ℤ) * bigA b ℓ + ∑ k, dd z j k ^ 2) =
      (Lopt x z : ℤ) + 2 * ∑ k, (((j k : ℕ) : ℤ) - (midpt x z k : ℕ)) ^ 2 := by
  simp only [Lopt]
  push_cast
  simp only [sqd_cast]
  have : ∀ k, dd x j k ^ 2 + dd z j k ^ 2 =
      2 * (((x k : ℕ) : ℤ) - (midpt x z k : ℕ)) ^ 2 + 2 * (((j k : ℕ) : ℤ) - (midpt x z k : ℕ)) ^ 2 := by
    intro k
    have h2 := two_midpt_eq hxz k
    simp only [dd]
    have : ((z k : ℕ) : ℤ) = 2 * (midpt x z k : ℕ) - (x k : ℕ) := by omega
    rw [this]; ring
  have hs : ∑ k, dd x j k ^ 2 + ∑ k, dd z j k ^ 2 = ∑ k, (2 * (((x k : ℕ) : ℤ) - (midpt x z k : ℕ)) ^ 2 +
      2 * (((j k : ℕ) : ℤ) - (midpt x z k : ℕ)) ^ 2) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ => this k
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  linear_combination hs

/-- Every walk of `G_{b,ℓ}` from `v_{0,x}` to `v_{2ℓ,z}` has length `≥ Lopt x z`, and if its length is
`≤ Lopt x z` it passes through `v_{ℓ,(x+z)/2}`. -/
theorem lopt_le_length_and (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) {x z : Vec b ℓ} (hxz : EvenDiff x z)
    (p : (G b ℓ).Walk (main 0 x) (main (Fin.last _) z)) :
    Lopt x z ≤ p.length ∧ (p.length ≤ Lopt x z → main ⟨ℓ, by omega⟩ (midpt x z) ∈ p.support) := by
  obtain ⟨j, hj⟩ := exists_mem_support_midLevel p (by simp [low])
    (by simp [low]; omega)
  have hsplit := congrArg Walk.length (p.take_spec hj)
  rw [Walk.length_append] at hsplit
  have h1 := pot_bot_le hb hℓ x j (p.takeUntil _ hj)
  have h2 := pot_top_le hb hℓ z j (p.dropUntil _ hj)
  have heq := pot_sum_eq hxz j
  have hnn : 0 ≤ ∑ k, (((j k : ℕ) : ℤ) - (midpt x z k : ℕ)) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hlen : ((p.takeUntil _ hj).length : ℤ) + (p.dropUntil _ hj).length = p.length := by
    exact_mod_cast hsplit
  refine ⟨by zify; linarith, fun hp => ?_⟩
  have hzero : ∑ k, (((j k : ℕ) : ℤ) - (midpt x z k : ℕ)) ^ 2 = 0 := by
    have : (p.length : ℤ) ≤ Lopt x z := by exact_mod_cast hp
    linarith
  have hjm : j = midpt x z := by
    funext k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg _)).1 hzero k (mem_univ _)
    have : ((j k : ℕ) : ℤ) = (midpt x z k : ℕ) := by nlinarith
    exact Fin.ext (by exact_mod_cast this)
  rw [← hjm]; exact hj

end Podc.HubLabelingHardness
