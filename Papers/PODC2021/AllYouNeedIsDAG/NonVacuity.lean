import Papers.PODC2021.AllYouNeedIsDAG.DagLayerProofs

/-!
# DAG-Rider: a concrete valid run (non-vacuity of `Run.Valid`)

`n = 4` processes (`f = 1`), no Byzantine process, genesis `G0 = {0, 1, 2}`, lock-step schedule:
before its step `t ≥ 1` every process delivers the four vertices of round `t`. Every vertex of
round `1` has strong edges to `G0`, every vertex of round `r ≥ 2` to all four vertices of round
`r - 1`, no weak edges, and block `r`.

We compute the states in closed form (`st_eq`: after `t + 1` steps a process is in round `t + 1`
and its DAG consists of all vertices of rounds `1..t`), show `R.Valid 1 G0 blk` (`valid`), and that
every wave is "good": every vertex of round `wround w 4` has a strong path to every vertex of
round `wround w 1` (`good_waves`).
-/

namespace DagRider.NonVacuity

open Finset

/-- Genesis sources. -/
def G0 : Finset (Fin 4) := {0, 1, 2}

/-- Blocks: `blk k r = r`. -/
def blk : Fin 4 → ℕ → ℕ := fun _ r => r

/-- Global contents. -/
def C : Content (Fin 4) ℕ where
  strong v := if v.1 = 1 then G0 else univ
  weak _ := ∅
  block v := v.1

/-- The lock-step run. -/
def R : Run (Fin 4) ℕ where
  C := C
  byz := ∅
  dl _ t := if t = 0 then ∅ else univ.image (fun k => (t, k))

/-- All vertices of rounds `1..t`. -/
def upto (t : ℕ) : Finset (Vtx (Fin 4)) := Icc 1 t ×ˢ univ

lemma mem_upto {t : ℕ} {v : Vtx (Fin 4)} : v ∈ upto t ↔ 1 ≤ v.1 ∧ v.1 ≤ t := by
  simp [upto]

lemma mem_dl {p : Fin 4} {t : ℕ} {v : Vtx (Fin 4)} : v ∈ R.dl p t ↔ t ≠ 0 ∧ v.1 = t := by
  rcases v with ⟨r, k⟩
  by_cases ht : t = 0
  · simp [R, ht]
  · simp [R, ht, eq_comm]

lemma card_strong (v : Vtx (Fin 4)) : 3 ≤ (C.strong v).card := by
  simp only [C]
  split_ifs <;> decide

lemma predsIn_upto (t : ℕ) (k : Fin 4) : PredsIn G0 C (upto t) (t + 1, k) := by
  refine ⟨fun s hs => ?_, fun u hu => by simp [C] at hu⟩
  by_cases ht : t = 0
  · subst ht
    simpa [C] using hs
  · simp only [Nat.add_eq_right, ht, ite_false, Nat.add_sub_cancel, mem_upto]
    omega

lemma layer_upto (t : ℕ) (ht : 1 ≤ t) : layer (upto t) t = {t} ×ˢ univ := by
  ext ⟨r, k⟩
  simp only [mem_layer, mem_upto, mem_product, mem_singleton, mem_univ, and_true]
  omega

lemma lstate_eq {s : LState (Fin 4)} {a : ℕ} {D E : Finset (Vtx (Fin 4))} (h1 : s.rnd = a)
    (h2 : s.dag = D) (h3 : s.buf = E) : s = ⟨a, D, E⟩ := by
  cases s; simp_all

/-- Closed form of the local states. -/
theorem st_eq (p : Fin 4) (t : ℕ) : R.st 1 G0 p (t + 1) = ⟨t + 1, upto t, ∅⟩ := by
  induction t with
  | zero =>
    apply lstate_eq (st_rnd_one R p)
    · ext v
      rw [st_succ, mem_lstep_dag]
      simp [st_zero, upto]
      omega
    · ext v
      rw [st_succ, mem_lstep_buf]
      simp [st_zero, R]
  | succ t ih =>
    have hdag : (R.st 1 G0 p (t + 1 + 1)).dag = upto (t + 1) := by
      ext v
      rw [st_succ, mem_lstep_dag, ih, mem_dl]
      simp only [mem_upto, notMem_empty, false_or]
      constructor
      · rintro (h | ⟨-, h1, h2, -⟩) <;> omega
      · intro h
        by_cases hv : v.1 ≤ t
        · exact Or.inl ⟨h.1, hv⟩
        · right
          have hv1 : v.1 = t + 1 := by omega
          refine ⟨⟨⟨by omega, hv1⟩, card_strong v⟩, h.1, h.2, ?_⟩
          have : v = (t + 1, v.2) := Prod.ext hv1 rfl
          rw [this]; exact predsIn_upto t v.2
    apply lstate_eq _ hdag
    · ext v
      rw [st_succ, mem_lstep_buf, ih, mem_dl]
      simp only [notMem_empty, false_or, iff_false, not_and]
      rintro ⟨⟨-, hv1⟩, -⟩ hn
      have : v = (t + 1, v.2) := Prod.ext hv1 rfl
      exact hn (by omega) (by omega) (by rw [this]; exact predsIn_upto t v.2)
    · have h3 : 2 * 1 + 1 ≤ (layer (R.st 1 G0 p (t + 1 + 1)).dag (R.st 1 G0 p (t + 1)).rnd).card := by
        rw [hdag, ih]
        dsimp only
        rw [layer_upto _ (by omega)]
        simp
      rw [advance_of_layer R p h3, ih]

lemma st_rnd (p : Fin 4) (t : ℕ) : (R.st 1 G0 p t).rnd = t := by
  cases t with
  | zero => rfl
  | succ t => rw [st_eq]

/-- Strong paths go down through all rounds `≥ 1`. -/
lemma sPath_down {r : ℕ} (hr : 1 ≤ r) (k : ℕ) (a b : Fin 4) : SPath C (r + k + 1, a) (r, b) := by
  induction k generalizing a with
  | zero =>
    refine Relation.ReflTransGen.single ⟨rfl, ?_, hr⟩
    simp [C, show r ≠ 0 by omega]
  | succ k ih =>
    refine Relation.ReflTransGen.head (b := (r + k + 1, a)) ⟨by simp; omega, ?_, by simp⟩ (ih a)
    simp [C]

lemma createdOK (p : Fin 4) (t : ℕ) : CreatedOK G0 blk C p t (upto t) := by
  refine ⟨rfl, ?_, by simp [C], ?_⟩
  · by_cases ht : t = 0
    · subst ht; simp [C]
    · rw [ite_eq_right ht, layer_upto t (by omega)]
      simp only [C, Nat.add_eq_right, ht, ite_false]
      ext k; simp
  · intro u hu h2
    rw [mem_upto] at hu
    have h := sPath_down hu.1 (t - u.1 - 1) p u.2
    rw [show u.1 + (t - u.1 - 1) + 1 = t by omega] at h
    have := (sPath_down hu.1 (t - u.1) p u.2).path
    rwa [show u.1 + (t - u.1) + 1 = t + 1 by omega] at this

/-- The lock-step run is a valid run of the DAG layer with `n = 4`, `f = 1`. -/
theorem valid : R.Valid 1 G0 blk where
  card := rfl
  card_G0 := by decide
  card_byz := by simp [R]
  created p _ t _ := by
    rw [st_rnd]
    cases t with
    | zero =>
      have h := createdOK p 0
      rw [show upto 0 = ∅ by simp [upto]] at h
      rw [show (R.st 1 G0 p 1).dag = ∅ by rw [st_eq]; simp [upto]]
      exact h
    | succ t =>
      rw [st_eq]
      exact createdOK p (t + 1)
  auth p _ q _ t v hv _ := by
    rw [mem_dl] at hv
    exact ⟨by omega, t, by rw [st_rnd]; omega⟩
  rbcValidity p _ q _ t r hr _ := ⟨r, mem_dl.2 ⟨by omega, rfl⟩⟩
  rbcAgreement p _ q _ t v hv := ⟨t, mem_dl.2 (mem_dl.1 hv)⟩

/-- In this run every wave is good: every vertex of round `wround w 4` (in particular every such
vertex of every local DAG) has a strong path to every vertex of round `wround w 1`. -/
theorem good_waves (w : ℕ) (u : Vtx (Fin 4)) (hu1 : u.1 = wround w 4) (c : Fin 4) :
    SPath R.C u (wround w 1, c) := by
  have h := sPath_down (r := wround w 1) (by unfold wround; omega) 2 u.2 c
  have : u = (wround w 1 + 2 + 1, u.2) := Prod.ext (by rw [hu1]; unfold wround; omega) rfl
  rw [this]; exact h

end DagRider.NonVacuity
