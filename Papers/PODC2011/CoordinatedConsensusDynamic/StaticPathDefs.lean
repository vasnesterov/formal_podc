import Papers.PODC2011.CoordinatedConsensusDynamic.Coordination

/-!
# Cycles, paths and executions for the static-line lower bound (Section 6.1)

Nodes are `u_0, …, u_{n-1}` (UIDs `0, …, n-1`, indices mod `n`).

* `cyc n` is the cycle `C = u_0, u_1, …, u_{n-1}, u_0`.
* `path n k` is the path `P_k = u_{k+1}, …, u_{k+n}`, i.e. `C` minus the edge `{u_k, u_{k+1}}`.
  It is defined through the *position* `pos n k x` of `x` on `P_k` (`u_{k+1}` has position `0`,
  `u_k` has position `n - 1`), so that all reasoning about it is linear arithmetic.
* `exec n σ g` is the execution with node set `{0, …, n-1}`, inputs `σ`, `N = n` and
  communication graph `g r` in round `r`; `IsCP n g` says that every round graph is `C` or
  some `P_k`. Such executions are admissible in the system `KnownN n` when `n ≥ 3`.

We also record the generic tools used for the "speed of information" arguments: a forward
invariant principle for causal chains (`reach_inv`) and padding of walks in the similarity graph.
-/

namespace CoordCons

namespace StaticPath

open DGraph Relation

/-! ### Positions, the cycle and the paths -/

/-- Position of node `x` on the path `P_k = u_{k+1}, …, u_{k+n}` (`u_{k+1}` has position `0`). -/
def pos (n k x : ℕ) : ℕ := (x + (n - 1 - k % n)) % n

/-- The cycle `C = u_0, …, u_{n-1}, u_0`. -/
def cyc (n : ℕ) (x y : ℕ) : Prop :=
  x < n ∧ y < n ∧ (x + 1 = y ∨ y + 1 = x ∨ (x = 0 ∧ y + 1 = n) ∨ (y = 0 ∧ x + 1 = n))

/-- The path `P_k = u_{k+1}, …, u_{k+n}` (the cycle without the edge `{u_k, u_{k+1}}`). -/
def path (n k : ℕ) (x y : ℕ) : Prop :=
  x < n ∧ y < n ∧ (pos n k x + 1 = pos n k y ∨ pos n k y + 1 = pos n k x)

/-- Every round graph is the cycle or one of the paths. -/
def IsCP (n : ℕ) (g : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ r, g r = cyc n ∨ ∃ k, g r = path n k

/-- The execution on `{u_0, …, u_{n-1}}` with inputs `σ`, `N = n` and round graphs `g`. -/
def exec (n : ℕ) (σ : ℕ → Bool) (g : ℕ → ℕ → ℕ → Prop) : DGraph Bool where
  V := Finset.range n
  input := σ
  N := n
  adj := g

/-- The static line `P_k` with inputs `σ` (the same path in every round). -/
def staticLine (n k : ℕ) (σ : ℕ → Bool) : DGraph Bool := exec n σ fun _ => path n k

theorem mod_eq_ite {a n : ℕ} (h : a < 2 * n) : a % n = if a < n then a else a - n := by
  split_ifs with h'
  · exact Nat.mod_eq_of_lt h'
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem pos_eq {n k x : ℕ} (hx : x < n) :
    pos n k x = if k % n < x then x - k % n - 1 else x + n - 1 - k % n := by
  have hj : k % n < n := Nat.mod_lt _ (by omega)
  unfold pos
  rw [mod_eq_ite (by omega)]
  split_ifs <;> omega

theorem pos_lt {n k x : ℕ} (hn : 0 < n) : pos n k x < n := Nat.mod_lt _ hn

theorem mod_add_eq {n k c : ℕ} (hn : 0 < n) (hc : c ≤ n) :
    (k + c) % n = if k % n + c < n then k % n + c else k % n + c - n := by
  have hj : k % n < n := Nat.mod_lt _ hn
  rw [← Nat.mod_add_mod, mod_eq_ite (by omega)]

/-- Rotating the path by `c` shifts all positions by `-c` (mod `n`). -/
theorem pos_add {n k c x : ℕ} (hx : x < n) (hc : c ≤ n) :
    pos n (k + c) x = if c ≤ pos n k x then pos n k x - c else pos n k x + n - c := by
  have hj : k % n < n := Nat.mod_lt _ (by omega)
  rw [pos_eq hx, pos_eq hx, mod_add_eq (by omega) hc]
  split_ifs <;> omega

/-- `u_{k+1}` is the first node of `P_k`. -/
theorem pos_first {n k : ℕ} (hn : 0 < n) : pos n k ((k + 1) % n) = 0 := by
  have hj : k % n < n := Nat.mod_lt _ hn
  rw [pos_eq (Nat.mod_lt _ hn), mod_add_eq hn (by omega)]
  split_ifs <;> omega

/-- `u_k` is the last node of `P_k`. -/
theorem pos_last {n k : ℕ} (hn : 0 < n) : pos n k (k % n) = n - 1 := by
  have hj : k % n < n := Nat.mod_lt _ hn
  rw [pos_eq hj]
  split_ifs <;> omega

theorem pos_inj {n k x y : ℕ} (hx : x < n) (hy : y < n) (h : pos n k x = pos n k y) : x = y := by
  have hj : k % n < n := Nat.mod_lt _ (by omega)
  rw [pos_eq hx, pos_eq hy] at h
  split_ifs at h <;> omega

/-- The cycle seen from any cut point `k`: consecutive positions, or the two ends of `P_k`. -/
theorem cyc_iff {n : ℕ} (k : ℕ) (hn : 3 ≤ n) {x y : ℕ} :
    cyc n x y ↔ x < n ∧ y < n ∧ (pos n k x + 1 = pos n k y ∨ pos n k y + 1 = pos n k x ∨
      (pos n k x = 0 ∧ pos n k y + 1 = n) ∨ (pos n k y = 0 ∧ pos n k x + 1 = n)) := by
  have hj : k % n < n := Nat.mod_lt _ (by omega)
  unfold cyc
  by_cases hx : x < n
  · by_cases hy : y < n
    · rw [pos_eq hx, pos_eq hy]
      split_ifs <;> omega
    · simp [hy]
  · simp [hx]

theorem path_cyc {n k x y : ℕ} (hn : 3 ≤ n) (h : path n k x y) : cyc n x y := by
  rw [cyc_iff k hn]
  obtain ⟨hx, hy, h⟩ := h
  exact ⟨hx, hy, by omega⟩

/-- Away from the missing edge, `C` and `P_k` have the same edges. -/
theorem cyc_iff_path {n k x w : ℕ} (hn : 3 ≤ n) (h0 : pos n k w ≠ 0) (h1 : pos n k w ≠ n - 1) :
    cyc n x w ↔ path n k x w := by
  rw [cyc_iff k hn]
  unfold path
  have := pos_lt (n := n) (k := k) (x := x) (by omega)
  constructor
  · rintro ⟨hx, hw, h⟩; exact ⟨hx, hw, by omega⟩
  · rintro ⟨hx, hw, h⟩; exact ⟨hx, hw, by omega⟩

theorem path_pos_le {n k x y : ℕ} (h : path n k x y) : pos n k x ≤ pos n k y + 1 := by
  obtain ⟨-, -, h⟩ := h; omega

theorem path_pos_le' {n k x y : ℕ} (h : path n k x y) : pos n k y ≤ pos n k x + 1 := by
  obtain ⟨-, -, h⟩ := h; omega

/-! ### Validity -/

theorem path_symm {n k x y : ℕ} (h : path n k x y) : path n k y x := by
  obtain ⟨hx, hy, h⟩ := h; exact ⟨hy, hx, by omega⟩

theorem cyc_symm {n x y : ℕ} (h : cyc n x y) : cyc n y x := by
  obtain ⟨hx, hy, h⟩ := h; exact ⟨hy, hx, by omega⟩

theorem path_conn_first {n k : ℕ} (hn : 0 < n) :
    ∀ p x, x < n → pos n k x = p → ReflTransGen (path n k) ((k + 1) % n) x := by
  have hj : k % n < n := Nat.mod_lt _ hn
  intro p
  induction p with
  | zero =>
    intro x hx hp
    rw [pos_inj hx (Nat.mod_lt _ hn) (hp.trans (pos_first hn).symm)]
  | succ p ih =>
    intro x hx hp
    have hx' : (if x = 0 then n - 1 else x - 1) < n := by split_ifs <;> omega
    have hp' : pos n k (if x = 0 then n - 1 else x - 1) = p := by
      rw [pos_eq hx'] ; rw [pos_eq hx] at hp
      split_ifs at hp ⊢ <;> omega
    refine (ih _ hx' hp').tail ⟨hx', hx, ?_⟩
    rw [hp']; omega

theorem path_conn {n k : ℕ} (hn : 0 < n) {x y : ℕ} (hx : x < n) (hy : y < n) :
    ReflTransGen (path n k) x y := by
  have : Std.Symm (path n k) := ⟨fun _ _ h => path_symm h⟩
  exact (Std.Symm.symm (r := ReflTransGen (path n k)) _ _ (path_conn_first hn _ x hx rfl)).trans
    (path_conn_first hn _ y hy rfl)

theorem IsCP.lt {n : ℕ} {g : ℕ → ℕ → ℕ → Prop} (hg : IsCP n g) {r x y : ℕ} (h : g r x y) :
    x < n ∧ y < n := by
  rcases hg r with e | ⟨k, e⟩ <;> rw [e] at h
  · exact ⟨h.1, h.2.1⟩
  · exact ⟨h.1, h.2.1⟩

theorem exec_valid {n : ℕ} (σ : ℕ → Bool) {g : ℕ → ℕ → ℕ → Prop} (hn : 3 ≤ n) (hg : IsCP n g) :
    (exec n σ g).Valid where
  nonempty := ⟨0, Finset.mem_range.2 (by omega)⟩
  mem r x y h := by
    have := hg.lt h
    simp only [exec, Finset.mem_range]; exact this
  symm r x y h := by
    change g r x y at h
    change g r y x
    rcases hg r with e | ⟨k, e⟩ <;> rw [e] at h ⊢
    · exact cyc_symm h
    · exact path_symm h
  irrefl r x h := by
    change g r x x at h
    rcases hg r with e | ⟨k, e⟩ <;> rw [e] at h
    · obtain ⟨-, -, h⟩ := h; omega
    · obtain ⟨-, -, h⟩ := h; omega
  conn r _ x hx y hy := by
    simp only [exec, Finset.mem_range] at hx hy
    change ReflTransGen (g r) x y
    rcases hg r with e | ⟨k, e⟩ <;> rw [e]
    · exact ReflTransGen.mono (fun _ _ h => path_cyc hn h) _ _ (path_conn (k := 0) (by omega) hx hy)
    · exact path_conn (by omega) hx hy

theorem exec_knownN {n : ℕ} (σ : ℕ → Bool) {g : ℕ → ℕ → ℕ → Prop} (hn : 3 ≤ n)
    (hg : IsCP n g) : KnownN n (exec n σ g) :=
  ⟨exec_valid σ hn hg, Finset.card_range n, rfl⟩

theorem isCP_const_path (n k : ℕ) : IsCP n fun _ => path n k := fun _ => Or.inr ⟨k, rfl⟩

theorem staticLine_knownN {n : ℕ} (k : ℕ) (σ : ℕ → Bool) (hn : 3 ≤ n) :
    KnownN n (staticLine n k σ) :=
  exec_knownN σ hn (isCP_const_path n k)

/-! ### Generic tools -/

/-- Forward invariants along causal chains ("speed of information" arguments). -/
theorem reach_inv {α : Type*} {G : DGraph α} {P : ℕ → ℕ → Prop} {v s u t : ℕ}
    (h : G.Reach v s u t) (h0 : P s v)
    (hstep : ∀ τ x y, s ≤ τ → τ < t → P τ x → (x = y ∨ G.adj (τ + 1) x y) → P (τ + 1) y) :
    P t u := by
  induction h with
  | refl => exact h0
  | @step w u t hr hwu ih =>
    exact hstep t w u hr.le (by omega) (ih fun τ x y h1 h2 => hstep τ x y h1 (by omega)) hwu

/-- An admissible execution is similar to itself (some node exists). -/
theorem simStep_self {n t : ℕ} {H : DGraph Bool} (hH : KnownN n H) : SimStep (KnownN n) t H H := by
  obtain ⟨u, hu⟩ := hH.1.nonempty
  exact ⟨hH, hH, u, Indist.refl hH.1 hu t⟩

/-- Walks can be padded with self-loops. -/
theorem Walk.pad {n t ℓ ℓ' : ℕ} {G H : DGraph Bool} (h : Walk (KnownN n) t ℓ G H)
    (hH : KnownN n H) (hℓ : ℓ ≤ ℓ') : Walk (KnownN n) t ℓ' G H := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  induction j with
  | zero => exact h
  | succ j ih => exact .snoc (ih (by omega)) (simStep_self hH)

theorem Walk.cast {S : DGraph Bool → Prop} {t ℓ ℓ' : ℕ} {G H : DGraph Bool} (h : Walk S t ℓ G H)
    (e : ℓ = ℓ') : Walk S t ℓ' G H := e ▸ h

end StaticPath

end CoordCons
