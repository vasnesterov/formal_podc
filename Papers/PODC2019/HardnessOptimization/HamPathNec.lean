import Papers.PODC2019.HardnessOptimization.HamPathGraph

/-!
# Claim 2.2: a Hamiltonian path in `D_{x,y}` forces `DISJ(x, y) = FALSE`

We follow positions along the path (`HP.pos`, `HP.Nx u v` = "`v` comes right after `u`").
The argument (a reorganisation of the paper's Claims 2.3–2.5):

1. `claimB` (Claim 2.3): a detour `ℓ → wheel` continues `wheel → β → σ → forward`.
2. `isR_before`: all box vertices come before `s¹₁`.
3. `suffix`: after `s¹₁` the path is `a^i_1, a^j_2, s²₁, s¹₂, b^{i'}_1, b^{j'}_2, s²₂, end`.
4. `row_pred`, `beta_pred`: a row visited before `s¹₁` is entered from a launch vertex.
5. Every position `(c, q, d)` is a *block* entered at `ℓ` and left forward (`BlockF`) or backward
   (`BlockB`); no forward block is followed by a backward one (`no_FB`).
6. `line`, `box`: in every box one line is traversed forward from `g_c`, the other one backward
   from `r_c` (so the backward line has no wheel detours).
7. Hence the rows `a^ī_1, b^ī_1, a^j̄_2, b^j̄_2` (`ī`, `j̄` = complements of the forward choices)
   are not visited before `s¹₁`, so they are the four rows of the suffix: `x(ī, j̄) = y(ī, j̄) = 1`.

Only the wheel property `(W c q d).2 (bit c) = q` is used (rows on line `q` of box `c` have bit
`bit c` equal to `q`); neither injectivity of the wheel nor the "A-half / B-half" order matter.
-/

namespace HardnessOptimization.HamPath

open HV

variable {L : ℕ} {W : Wheel L} {x y : Idx L → Idx L → Bool}

/-- A Hamiltonian path of `D_{x,y}`, given as an enumeration `e : Fin n ≃ V` of the vertices. -/
structure HP (W : Wheel L) (x y : Idx L → Idx L → Bool) where
  /-- Number of vertices. -/
  n : ℕ
  /-- The `i`-th vertex of the path. -/
  e : Fin n ≃ HV L
  arc : ∀ i (h : i + 1 < n), Arc W x y (e ⟨i, by omega⟩) (e ⟨i + 1, h⟩)

namespace HP

variable (P : HP W x y)

/-- The position of `v` on the path. -/
def pos (v : HV L) : ℕ := (P.e.symm v).val

/-- `v` comes right after `u`. -/
def Nx (u v : HV L) : Prop := P.pos v = P.pos u + 1

lemma pos_lt (v : HV L) : P.pos v < P.n := (P.e.symm v).isLt

lemma pos_inj {u v : HV L} (h : P.pos u = P.pos v) : u = v := by
  have : P.e.symm u = P.e.symm v := Fin.ext h
  simpa using congrArg P.e this

lemma e_pos (v : HV L) : P.e ⟨P.pos v, P.pos_lt v⟩ = v := by simp [pos]

variable {P}

lemma Nx.arc {u v : HV L} (h : P.Nx u v) : Arc W x y u v := by
  have h1 : P.pos u + 1 < P.n := h ▸ P.pos_lt v
  have := P.arc _ h1
  rwa [P.e_pos, show (⟨P.pos u + 1, h1⟩ : Fin P.n) = ⟨P.pos v, P.pos_lt v⟩ from Fin.ext h.symm,
    P.e_pos] at this

lemma Nx.inj_l {u u' v : HV L} (h : P.Nx u v) (h' : P.Nx u' v) : u = u' :=
  P.pos_inj (by unfold Nx at h h'; omega)

lemma Nx.inj_r {u v v' : HV L} (h : P.Nx u v) (h' : P.Nx u v') : v = v' :=
  P.pos_inj (by unfold Nx at h h'; omega)

lemma Nx.lt {u v : HV L} (h : P.Nx u v) : P.pos u < P.pos v := by unfold Nx at h; omega

variable (P)

lemma pos_stop : P.pos .stop + 1 = P.n := by
  have := P.pos_lt .stop
  by_contra hne
  have h1 : P.pos .stop + 1 < P.n := by omega
  have := P.arc _ h1
  rw [P.e_pos] at this
  exact not_arc_from_stop _ this

lemma pos_start : P.pos .start = 0 := by
  by_contra hne
  have h1 : P.pos .start - 1 + 1 < P.n := by have := P.pos_lt .start; omega
  have := P.arc _ h1
  rw [show (⟨P.pos .start - 1 + 1, h1⟩ : Fin P.n) = ⟨P.pos .start, P.pos_lt _⟩ from
    Fin.ext (by simp; omega), P.e_pos] at this
  exact not_arc_into_start _ this

lemma exists_succ {v : HV L} (hv : v ≠ .stop) : ∃ w, P.Nx v w := by
  have h1 : P.pos v + 1 < P.n := by
    have := P.pos_stop
    have := P.pos_lt v
    have : P.pos v ≠ P.pos .stop := fun h => hv (P.pos_inj h)
    omega
  exact ⟨P.e ⟨P.pos v + 1, h1⟩, by simp [Nx, pos]⟩

lemma exists_pred {v : HV L} (hv : v ≠ .start) : ∃ u, P.Nx u v := by
  have h1 : 0 < P.pos v := by
    have := P.pos_start
    have : P.pos v ≠ P.pos .start := fun h => hv (P.pos_inj h)
    omega
  refine ⟨P.e ⟨P.pos v - 1, by have := P.pos_lt v; omega⟩, ?_⟩
  have : P.pos (P.e ⟨P.pos v - 1, by have := P.pos_lt v; omega⟩) = P.pos v - 1 := by simp [pos]
  unfold Nx; rw [this]; omega

/-! ### Claim 2.3 -/

/-- **Claim 2.3.** If the path goes from `ℓ^{c,d}_q` to a vertex other than `σ^{c,d}_q` (i.e. to
the wheel), it continues `wheel → β^{c,d}_q → σ^{c,d}_q → forward target`. -/
lemma claimB {c q d} {w : HV L} (h : P.Nx (.la c q d) w) (hw : w ≠ .si c q d) :
    w = wrow W c q d ∧ P.Nx w (.be c q d) ∧ P.Nx (.be c q d) (.si c q d) ∧
      ∃ v, IsFwd c q d v ∧ P.Nx (.si c q d) v := by
  have hw' : w = wrow W c q d := by
    rcases arc_from_la.1 h.arc with h1 | h1
    · exact absurd h1 hw
    · exact h1
  subst hw'
  refine ⟨rfl, ?_⟩
  obtain ⟨u, hu⟩ := P.exists_pred (v := .si c q d) (by simp)
  have hsi : P.Nx (.be c q d) (.si c q d) := by
    rcases arc_into_si.1 hu.arc with rfl | rfl
    · exact absurd (h.inj_r hu) hw
    · exact hu
  obtain ⟨u', hu'⟩ := P.exists_pred (v := .be c q d) (by simp)
  have hbe : P.Nx (wrow W c q d) (.be c q d) := by
    rcases arc_into_be.1 hu'.arc with rfl | rfl
    · exfalso; unfold Nx at hsi hu'; omega
    · exact hu'
  obtain ⟨v, hv⟩ := P.exists_succ (v := .si c q d) (by simp)
  rcases arc_from_si.1 hv.arc with rfl | hf
  · exact absurd (hv.inj_l hbe) (by simp [wrow])
  · exact ⟨hbe, hsi, v, hf, hv⟩

/-! ### All box vertices come before `s¹₁` -/

/-- Box vertices `g, r, ℓ, σ, β`. -/
def isR : HV L → Bool
  | .g _ | .r _ | .la _ _ _ | .si _ _ _ | .be _ _ _ => true
  | _ => false

lemma isR_of_isFwd {c q d} {v : HV L} (h : IsFwd c q d v) : isR v = true := by
  cases v <;> simp_all [IsFwd, isR]

lemma isR_of_isBwd {c q d} {v : HV L} (h : IsBwd c q d v) : isR v = true ∨ v = .sA1 := by
  cases v <;> simp_all [IsBwd, isR]

lemma isR_before {v : HV L} (hv : isR v = true) : P.pos v < P.pos .sA1 := by
  by_contra hcon
  have hne : P.pos v ≠ P.pos .sA1 := fun h => by
    have := P.pos_inj h; subst this; simp [isR] at hv
  let S := Finset.univ.filter (fun v : HV L => isR v = true ∧ P.pos .sA1 < P.pos v)
  have hS : S.Nonempty := ⟨v, by simp [S, hv]; omega⟩
  obtain ⟨z, hzS, hmax⟩ := S.exists_max_image P.pos hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hzS hmax
  obtain ⟨hzR, hz⟩ := hzS
  have key : ∀ t, P.pos z < P.pos t → isR t = true → False := fun t h1 h2 => by
    have := hmax t ⟨h2, by omega⟩; omega
  have hzs : z ≠ .stop := by rintro rfl; simp [isR] at hzR
  obtain ⟨t, ht⟩ := P.exists_succ hzs
  cases z <;> simp [isR] at hzR
  case g c =>
    obtain ⟨q, d, -, rfl⟩ := arc_from_g.1 ht.arc
    exact key _ ht.lt rfl
  case r c =>
    obtain ⟨q, d, -, rfl⟩ := arc_from_r.1 ht.arc
    exact key _ ht.lt rfl
  case la c q d =>
    by_cases hts : t = .si c q d
    · subst hts; exact key _ ht.lt rfl
    · obtain ⟨-, h2, -⟩ := P.claimB ht hts
      exact key (.be c q d) (by have := ht.lt; have := h2.lt; omega) rfl
  case si c q d =>
    rcases arc_from_si.1 ht.arc with rfl | hf
    · exact key _ ht.lt rfl
    · exact key _ ht.lt (isR_of_isFwd hf)
  case be c q d =>
    rcases arc_from_be.1 ht.arc with rfl | hf | hb
    · exact key _ ht.lt rfl
    · exact key _ ht.lt (isR_of_isFwd hf)
    · rcases isR_of_isBwd hb with h | rfl
      · exact key _ ht.lt h
      · have := ht.lt; omega

/-! ### The suffix after `s¹₁` -/

/-- The path ends with `s¹₁, a^i_1, a^j_2, s²₁, s¹₂, b^{i'}_1, b^{j'}_2, s²₂, end`, where
`x(i, j) = y(i', j') = 1`. -/
lemma suffix : ∃ i j i' j', x i j = true ∧ y i' j' = true ∧
    P.Nx .sA1 (.row false false i) ∧ P.Nx (.row false false i) (.row false true j) ∧
    P.Nx (.row false true j) .sA2 ∧ P.Nx .sA2 .sB1 ∧ P.Nx .sB1 (.row true false i') ∧
    P.Nx (.row true false i') (.row true true j') ∧ P.Nx (.row true true j') .sB2 ∧
    P.Nx .sB2 .stop := by
  -- a row visited after `s¹₁` never goes to a burn vertex
  have nob : ∀ (w : HV L) c q d, P.pos .sA1 < P.pos w → ¬ P.Nx w (.be c q d) := by
    intro w c q d h1 h2
    have := P.isR_before (v := .be c q d) rfl
    have := h2.lt
    omega
  obtain ⟨t1, h1⟩ := P.exists_succ (v := .sA1) (by simp)
  obtain ⟨i, rfl⟩ := arc_from_sA1.1 h1.arc
  obtain ⟨t2, h2⟩ := P.exists_succ (v := .row false false i) (by simp)
  obtain ⟨j, rfl, hx⟩ : ∃ j, t2 = .row false true j ∧ x i j = true := by
    rcases arc_from_row h2.arc with ⟨h, -⟩ | ⟨c, q, d, rfl, -⟩ | ⟨-, j, h, hx⟩
    · simp at h
    · exact absurd h2 (nob _ c q d h1.lt)
    · exact ⟨j, h, by simpa using hx⟩
  obtain ⟨t3, h3⟩ := P.exists_succ (v := .row false true j) (by simp)
  have e3 : t3 = .sA2 := by
    rcases arc_from_row h3.arc with ⟨-, h⟩ | ⟨c, q, d, rfl, -⟩ | ⟨h, -⟩
    · simpa using h
    · exact absurd h3 (nob _ c q d (by have := h1.lt; have := h2.lt; omega))
    · simp at h
  subst e3
  obtain ⟨t4, h4⟩ := P.exists_succ (v := .sA2) (by simp)
  have e4 := arc_from_sA2.1 h4.arc
  subst e4
  obtain ⟨t5, h5⟩ := P.exists_succ (v := .sB1) (by simp)
  obtain ⟨i', rfl⟩ := arc_from_sB1.1 h5.arc
  have l5 : P.pos .sA1 < P.pos (.row true false i') := by
    have := h1.lt; have := h2.lt; have := h3.lt; have := h4.lt; have := h5.lt; omega
  obtain ⟨t6, h6⟩ := P.exists_succ (v := .row true false i') (by simp)
  obtain ⟨j', rfl, hy⟩ : ∃ j', t6 = .row true true j' ∧ y i' j' = true := by
    rcases arc_from_row h6.arc with ⟨h, -⟩ | ⟨c, q, d, rfl, -⟩ | ⟨-, j, h, hy⟩
    · simp at h
    · exact absurd h6 (nob _ c q d l5)
    · exact ⟨j, h, by simpa using hy⟩
  obtain ⟨t7, h7⟩ := P.exists_succ (v := .row true true j') (by simp)
  have e7 : t7 = .sB2 := by
    rcases arc_from_row h7.arc with ⟨-, h⟩ | ⟨c, q, d, rfl, -⟩ | ⟨h, -⟩
    · simpa using h
    · exact absurd h7 (nob _ c q d (by have := h6.lt; omega))
    · simp at h
  subst e7
  obtain ⟨t8, h8⟩ := P.exists_succ (v := .sB2) (by simp)
  have e8 := arc_from_sB2.1 h8.arc
  subst e8
  exact ⟨i, j, i', j', hx, hy, h1, h2, h3, h4, h5, h6, h7, h8⟩

lemma sA1_lt_sB1 : P.pos .sA1 < P.pos .sB1 := by
  obtain ⟨i, j, i', j', -, -, h1, h2, h3, h4, -⟩ := P.suffix
  have := h1.lt; have := h2.lt; have := h3.lt; have := h4.lt; omega

/-! ### Rows before `s¹₁` are entered from launch vertices -/

lemma row_pred {s ℓ i} (hrow : P.pos (.row s ℓ i) < P.pos .sA1) :
    ∃ c q d, P.Nx (.la c q d) (.row s ℓ i) := by
  have hB := P.sA1_lt_sB1
  have aux : ∀ s i, P.pos (.row s false i) < P.pos .sA1 →
      ∃ c q d, P.Nx (.la c q d) (.row s false i) := by
    intro s i h
    obtain ⟨u, hu⟩ := P.exists_pred (v := .row s false i) (by simp)
    rcases arc_into_row hu.arc with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨c, q, d, rfl, -⟩ | ⟨h', -⟩
    · unfold Nx at hu; omega
    · have := hu.lt; omega
    · exact ⟨c, q, d, hu⟩
    · simp at h'
  cases ℓ
  · exact aux s i hrow
  obtain ⟨u, hu⟩ := P.exists_pred (v := .row s true i) (by simp)
  rcases arc_into_row hu.arc with ⟨-, h', -⟩ | ⟨-, h', -⟩ | ⟨c, q, d, rfl, -⟩ | ⟨-, i', rfl⟩
  · simp at h'
  · simp at h'
  · exact ⟨c, q, d, hu⟩
  · obtain ⟨c, q, d, h'⟩ := aux s i' (by have := hu.lt; omega)
    obtain ⟨-, h2, -⟩ := P.claimB h' (by simp)
    exact absurd (hu.inj_r h2) (by simp)

/-- A burn vertex entered from its wheel row: the row was entered from the launch vertex. -/
lemma beta_pred {c q d} (h : P.Nx (wrow W c q d) (.be c q d)) :
    P.Nx (.la c q d) (wrow W c q d) := by
  have hlt : P.pos (wrow W c q d) < P.pos .sA1 := by
    have := P.isR_before (v := .be c q d) rfl; have := h.lt; omega
  obtain ⟨c', q', d', h'⟩ := P.row_pred hlt
  obtain ⟨-, h2, -⟩ := P.claimB h' (by simp)
  have := h.inj_r h2
  simp only [HV.be.injEq] at this
  obtain ⟨rfl, rfl, rfl⟩ := this
  exact h'

/-! ### Blocks -/

/-- Position `(c, q, d)` is left forward (from `σ` or `β`). -/
def BlockF (c : Fin (2 * L)) (q : Bool) (d : Fin (2 ^ L)) : Prop :=
  ∃ v, IsFwd c q d v ∧ (P.Nx (.si c q d) v ∨ P.Nx (.be c q d) v)

/-- Position `(c, q, d)` is left backward (from `β`). -/
def BlockB (c : Fin (2 * L)) (q : Bool) (d : Fin (2 ^ L)) : Prop :=
  ∃ v, IsBwd c q d v ∧ P.Nx (.be c q d) v

/-- Each position is traversed as `ℓ → σ → β` or `ℓ → wheel → β → σ → forward`. -/
lemma block (c q d) :
    (P.Nx (.la c q d) (.si c q d) ∧ P.Nx (.si c q d) (.be c q d)) ∨
      (P.Nx (.la c q d) (wrow W c q d) ∧ P.Nx (wrow W c q d) (.be c q d) ∧
        P.Nx (.be c q d) (.si c q d) ∧ ∃ v, IsFwd c q d v ∧ P.Nx (.si c q d) v) := by
  obtain ⟨t, ht⟩ := P.exists_succ (v := .la c q d) (by simp)
  by_cases hts : t = .si c q d
  · subst hts
    left
    refine ⟨ht, ?_⟩
    obtain ⟨u, hu⟩ := P.exists_pred (v := .be c q d) (by simp)
    rcases arc_into_be.1 hu.arc with rfl | rfl
    · exact hu
    · exact absurd ((P.beta_pred hu).inj_r ht) (by simp [wrow])
  · right
    obtain ⟨rfl, h2, h3, h4⟩ := P.claimB ht hts
    exact ⟨ht, h2, h3, h4⟩

lemma block_pos (c q d) : P.pos (.la c q d) < P.pos (.si c q d) ∧
    P.pos (.la c q d) < P.pos (.be c q d) := by
  rcases P.block c q d with ⟨h1, h2⟩ | ⟨h1, h2, h3, -⟩
  · have := h1.lt; have := h2.lt; omega
  · have := h1.lt; have := h2.lt; have := h3.lt; omega

lemma blockF_or_blockB (c q d) : P.BlockF c q d ∨ P.BlockB c q d := by
  rcases P.block c q d with ⟨h1, h2⟩ | ⟨-, -, -, v, hv, h⟩
  · obtain ⟨t, ht⟩ := P.exists_succ (v := .be c q d) (by simp)
    rcases arc_from_be.1 ht.arc with rfl | hf | hb
    · exfalso; unfold Nx at h2 ht; omega
    · exact Or.inl ⟨t, hf, Or.inr ht⟩
    · exact Or.inr ⟨t, hb, ht⟩
  · exact Or.inl ⟨v, hv, Or.inl h⟩

lemma not_blockF_blockB {c q d} (hF : P.BlockF c q d) (hB : P.BlockB c q d) : False := by
  obtain ⟨v', hb, hv'⟩ := hB
  obtain ⟨v, hf, hv⟩ := hF
  rcases P.block c q d with ⟨-, h2⟩ | ⟨-, -, h3, -⟩
  · rcases hv with hv | hv
    · have := hv.inj_r h2; subst this; simp [IsFwd] at hf
    · have := hv.inj_r hv'; subst this; exact not_isFwd_isBwd hf hb
  · have := hv'.inj_r h3; subst this; simp [IsBwd] at hb

lemma blockF_of_detour {c q d} (h : P.Nx (.la c q d) (wrow W c q d)) : P.BlockF c q d := by
  obtain ⟨-, -, -, v, hv, h'⟩ := P.claimB h (by simp [wrow])
  exact ⟨v, hv, Or.inl h'⟩

/-- No forward block is followed by a backward block. -/
lemma no_FB {c q} {d d' : Fin (2 ^ L)} (hd : d'.val = d.val + 1) (hF : P.BlockF c q d)
    (hB : P.BlockB c q d') : False := by
  obtain ⟨v, hf, hv⟩ := hF
  obtain ⟨v', hb, hv'⟩ := hB
  have e1 : v = .la c q d' := isFwd_unique hf (by simp [IsFwd, hd])
  have e2 : v' = .la c q d := isBwd_unique hb (by simp [IsBwd, hd])
  subst e1 e2
  have p1 := P.block_pos c q d
  have p2 := P.block_pos c q d'
  have := hv'.lt
  rcases hv with hv | hv <;> have := hv.lt <;> omega

lemma blockB_down {c q} : ∀ (t : ℕ) (d d' : Fin (2 ^ L)), d'.val = d.val + t →
    P.BlockB c q d' → P.BlockB c q d
  | 0, d, d', h, hB => by
    have : d = d' := Fin.ext (by omega)
    subst this; exact hB
  | t + 1, d, d', h, hB => by
    let d₁ : Fin (2 ^ L) := ⟨d.val + t, by omega⟩
    have hB₁ : P.BlockB c q d₁ := by
      rcases P.blockF_or_blockB c q d₁ with hf | hb
      · exact absurd (P.no_FB (d' := d') (by simp [d₁]; omega) hf hB) id
      · exact hb
    exact blockB_down t d d₁ rfl hB₁

lemma blockF_up {c q} : ∀ (t : ℕ) (d d' : Fin (2 ^ L)), d'.val = d.val + t →
    P.BlockF c q d → P.BlockF c q d'
  | 0, d, d', h, hF => by
    have : d = d' := Fin.ext (by omega)
    subst this; exact hF
  | t + 1, d, d', h, hF => by
    let d₁ : Fin (2 ^ L) := ⟨d.val + 1, by omega⟩
    have hF₁ : P.BlockF c q d₁ := by
      rcases P.blockF_or_blockB c q d₁ with hf | hb
      · exact hf
      · exact absurd (P.no_FB (d := d) (by simp [d₁]) hF hb) id
    exact blockF_up t d₁ d' (by simp [d₁]; omega) hF₁

/-! ### Lines and boxes -/

/-- Line `q` of box `c` is entered from `g_c`. -/
def EG (c : Fin (2 * L)) (q : Bool) : Prop := ∃ d : Fin (2 ^ L), d.val = 0 ∧ P.Nx (.g c) (.la c q d)

/-- Line `q` of box `c` is entered from `r_c`. -/
def ER (c : Fin (2 * L)) (q : Bool) : Prop :=
  ∃ d : Fin (2 ^ L), d.val + 1 = 2 ^ L ∧ P.Nx (.r c) (.la c q d)

lemma line (hL : 0 < L) (c : Fin (2 * L)) (q : Bool) :
    ((∀ d, P.BlockF c q d) ∧ P.EG c q) ∨ ((∀ d, P.BlockB c q d) ∧ P.ER c q) ∨
      (P.EG c q ∧ P.ER c q) := by
  have hK : 2 ≤ 2 ^ L := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  let d0 : Fin (2 ^ L) := ⟨0, by omega⟩
  let dK : Fin (2 ^ L) := ⟨2 ^ L - 1, by omega⟩
  by_cases h0 : P.BlockF c q d0
  · have hall : ∀ d, P.BlockF c q d := fun d => P.blockF_up d.val d0 d (by simp [d0]) h0
    left
    refine ⟨hall, ?_⟩
    obtain ⟨u, hu⟩ := P.exists_pred (v := .la c q d0) (by simp)
    rcases arc_into_la.1 hu.arc with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨d', h, -⟩ | ⟨d', h, rfl⟩
    · exact ⟨d0, rfl, hu⟩
    · simp [d0] at h; omega
    · simp [d0] at h
    · exact absurd (P.not_blockF_blockB (hall d') ⟨_, by simp [IsBwd, d0, h], hu⟩) id
  by_cases hK' : P.BlockB c q dK
  · have hall : ∀ d, P.BlockB c q d := fun d =>
      P.blockB_down (dK.val - d.val) d dK (by simp [dK]; omega) hK'
    right; left
    refine ⟨hall, ?_⟩
    obtain ⟨u, hu⟩ := P.exists_pred (v := .la c q dK) (by simp)
    rcases arc_into_la.1 hu.arc with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨d', h, hu'⟩ | ⟨d', h, rfl⟩
    · simp [dK] at h; omega
    · exact ⟨dK, by simp [dK]; omega, hu⟩
    · refine absurd (P.not_blockF_blockB ⟨.la c q dK, ⟨rfl, rfl, h⟩, ?_⟩ (hall d')) id
      rcases hu' with rfl | rfl
      · exact Or.inl hu
      · exact Or.inr hu
    · simp [dK] at h; omega
  right; right
  have hB0 : P.BlockB c q d0 := (P.blockF_or_blockB c q d0).resolve_left h0
  have hFK : P.BlockF c q dK := (P.blockF_or_blockB c q dK).resolve_right hK'
  have hex : ∃ t, ∃ h : t < 2 ^ L, P.BlockF c q ⟨t, h⟩ := ⟨dK.val, dK.isLt, hFK⟩
  classical
  let t := Nat.find hex
  obtain ⟨htK, hFt⟩ : ∃ h : t < 2 ^ L, P.BlockF c q ⟨t, h⟩ := Nat.find_spec hex
  have hmin : ∀ t' (h : t' < 2 ^ L), t' < t → ¬ P.BlockF c q ⟨t', h⟩ :=
    fun t' h ht' hF => Nat.find_min hex ht' ⟨h, hF⟩
  have ht0 : t ≠ 0 := fun h => h0 (by simpa [d0, h] using hFt)
  let dt : Fin (2 ^ L) := ⟨t, htK⟩
  let dt1 : Fin (2 ^ L) := ⟨t - 1, by omega⟩
  have hBt1 : P.BlockB c q dt1 :=
    (P.blockF_or_blockB c q dt1).resolve_left (hmin _ _ (by omega))
  constructor
  · obtain ⟨u, hu⟩ := P.exists_pred (v := .la c q dt1) (by simp)
    rcases arc_into_la.1 hu.arc with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨d', h, hu'⟩ | ⟨d', h, rfl⟩
    · exact ⟨dt1, h, hu⟩
    · simp [dt1] at h; omega
    · refine absurd ?_ (hmin d'.val d'.isLt (by simp [dt1] at h; omega))
      refine ⟨.la c q dt1, ⟨rfl, rfl, h⟩, ?_⟩
      rcases hu' with rfl | rfl
      · exact Or.inl hu
      · exact Or.inr hu
    · have : d' = dt := Fin.ext (by simp [dt1, dt] at h ⊢; omega)
      subst this
      exact absurd (P.not_blockF_blockB hFt ⟨_, by simp [IsBwd, dt1]; omega, hu⟩) id
  · obtain ⟨u, hu⟩ := P.exists_pred (v := .la c q dt) (by simp)
    rcases arc_into_la.1 hu.arc with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨d', h, hu'⟩ | ⟨d', h, rfl⟩
    · simp [dt] at h; omega
    · exact ⟨dt, h, hu⟩
    · refine absurd ?_ (hmin d'.val d'.isLt (by simp [dt] at h; omega))
      refine ⟨.la c q dt, ⟨rfl, rfl, h⟩, ?_⟩
      rcases hu' with rfl | rfl
      · exact Or.inl hu
      · exact Or.inr hu
    · exact absurd (P.no_FB (d := dt) h hFt ⟨_, by simp [IsBwd, dt]; omega, hu⟩) id

lemma EG_unique {c q q'} (h : P.EG c q) (h' : P.EG c q') : q = q' := by
  obtain ⟨d, hd, h⟩ := h
  obtain ⟨d', hd', h'⟩ := h'
  have := h.inj_r h'
  simp only [HV.la.injEq] at this
  exact this.2.1

lemma ER_unique {c q q'} (h : P.ER c q) (h' : P.ER c q') : q = q' := by
  obtain ⟨d, hd, h⟩ := h
  obtain ⟨d', hd', h'⟩ := h'
  have := h.inj_r h'
  simp only [HV.la.injEq] at this
  exact this.2.1

/-- In every box, one line is traversed forward, the other one backward. -/
lemma box (hL : 0 < L) (c : Fin (2 * L)) :
    ∃ q, (∀ d, P.BlockF c q d) ∧ (∀ d, P.BlockB c (!q) d) := by
  rcases P.line hL c true with ⟨hF1, hG1⟩ | ⟨hB1, hR1⟩ | ⟨hG1, hR1⟩ <;>
  rcases P.line hL c false with ⟨hF0, hG0⟩ | ⟨hB0, hR0⟩ | ⟨hG0, hR0⟩
  all_goals first
    | exact absurd (P.EG_unique hG1 hG0) (by simp)
    | exact absurd (P.ER_unique hR1 hR0) (by simp)
    | exact ⟨true, hF1, hB0⟩
    | exact ⟨false, hF0, hB1⟩

end HP

/-- From a list-Hamiltonian path to an enumeration. -/
def HP.ofList {l : List (HV L)} (hnd : l.Nodup) (hall : ∀ v, v ∈ l) (hc : l.IsChain (Arc W x y)) :
    HP W x y where
  n := l.length
  e := List.Nodup.getEquivOfForallMemList l hnd hall
  arc i h := by
    simpa using List.isChain_iff_getElem.1 hc i h

/-- **Claim 2.2** (contrapositive form): if `D_{x,y}` has a directed Hamiltonian path, then
`DISJ(x, y) = FALSE`, i.e. `x(i, j) = y(i, j) = 1` for some `(i, j)`. Only needs that every row
on line `q` of box `c` has bit `bit c` equal to `q`. -/
theorem claim_2_2 (hL : 0 < L) (hW : ∀ c q d, (W c q d).2 (bit c) = q)
    (h : HasHamPath (Arc W x y)) : ∃ i j, x i j = true ∧ y i j = true := by
  obtain ⟨l, hnd, hall, hc⟩ := h
  let P := HP.ofList hnd hall hc
  choose q hq using P.box hL
  let ι : Bool → Idx L := fun ℓ h => !q (boxOf ℓ h)
  -- the rows `a^ī_1, …` are visited after `s¹₁`
  have key : ∀ s ℓ, P.pos .sA1 < P.pos (.row s ℓ (ι ℓ)) := by
    intro s ℓ
    by_contra hcon
    have hne : P.pos (.row s ℓ (ι ℓ)) ≠ P.pos .sA1 := fun h => by
      have := P.pos_inj h; simp at this
    obtain ⟨c, q', d, hn⟩ := P.row_pred (s := s) (ℓ := ℓ) (i := ι ℓ) (by omega)
    have hw : HV.row s ℓ (ι ℓ) = wrow W c q' d := by
      rcases arc_from_la.1 hn.arc with h | h
      · simp at h
      · exact h
    rw [hw] at hn
    have hF := P.blockF_of_detour hn
    have hq' : q' = q c := by
      by_contra hne'
      have : q' = !q c := by cases q' <;> cases h : q c <;> simp_all
      subst this
      exact P.not_blockF_blockB hF ((hq c).2 d)
    subst hq'
    simp only [wrow, HV.row.injEq] at hw
    obtain ⟨-, hℓ, hi⟩ := hw
    have := hW c (q c) d
    rw [← hi, hℓ] at this
    simp [ι] at this
  obtain ⟨i, j, i', j', hx, hy, h1, h2, h3, h4, h5, h6, h7, h8⟩ := P.suffix
  have hn := P.pos_stop
  -- every vertex after `s¹₁` is one of the eight suffix vertices
  have hsuf : ∀ v, P.pos .sA1 < P.pos v → v = .row false false i ∨ v = .row false true j ∨
      v = .sA2 ∨ v = .sB1 ∨ v = .row true false i' ∨ v = .row true true j' ∨ v = .sB2 ∨
      v = .stop := by
    intro v hv
    have := P.pos_lt v
    unfold HP.Nx at h1 h2 h3 h4 h5 h6 h7 h8
    have hk : P.pos v = P.pos (.row false false i) ∨ P.pos v = P.pos (.row false true j) ∨
        P.pos v = P.pos .sA2 ∨ P.pos v = P.pos .sB1 ∨ P.pos v = P.pos (.row true false i') ∨
        P.pos v = P.pos (.row true true j') ∨ P.pos v = P.pos .sB2 ∨
        P.pos v = P.pos .stop := by omega
    rcases hk with h | h | h | h | h | h | h | h <;> have := P.pos_inj h <;> simp [this]
  have ei : ι false = i := by
    rcases hsuf _ (key false false) with h | h | h | h | h | h | h | h <;> simp_all
  have ej : ι true = j := by
    rcases hsuf _ (key false true) with h | h | h | h | h | h | h | h <;> simp_all
  have ei' : ι false = i' := by
    rcases hsuf _ (key true false) with h | h | h | h | h | h | h | h <;> simp_all
  have ej' : ι true = j' := by
    rcases hsuf _ (key true true) with h | h | h | h | h | h | h | h <;> simp_all
  refine ⟨i, j, hx, ?_⟩
  rw [← ei, ← ej, ei', ej']
  exact hy

end HardnessOptimization.HamPath
