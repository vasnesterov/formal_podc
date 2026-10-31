import Papers.PODC2025.HidingColoringCertification.ModCounter

/-!
# The theta graph `θ(5,5,5)` and hiding of the counter LCP

`thetaG` is the graph on `Fin 14` made of three internally disjoint paths of length 5 between
the endpoints `4` and `5` (a watermelon graph): `4–0–1–2–3–5`, `4–6–7–8–9–5`, `4–10–11–12–13–5`.
It is bipartite, connected, has minimum degree 2, is not a cycle, and has girth 10.

`thetaPG s N` equips it with a port numbering (inner path nodes: port 0 towards `4`, port 1
towards `5`; endpoints: port `j` to path `j`) and identifiers that *rotate* on `{0,…,4}`:
node `i < 5` gets identifier `(s + i) mod 5`, the other nodes keep their index.

`thetaLabel t` (for `t : ZMod M`) is the counter labelling `v ↦ t + h v`, where `h` is the
"height" (`-1` at node 4, positions `0..3` on the paths, `4` at node 5).

Key fact (`view_shift`): the view of node `2` for the parameter `t` equals the view of node `1`
for the parameter `t + 1` — including identifiers, ports, labels and degrees. Since `1` and `2`
are adjacent, an extraction algorithm `A` that succeeds everywhere satisfies
`A(view_{t+1} 1) ≠ A(view_t 1)` for all `t ∈ ZMod M`, impossible for odd `M`
(`counterLCP_hiding`). So the counter LCP is hiding even against identifier-aware algorithms.
-/

namespace Podc.HidingColoringCertification

open SimpleGraph

/-- The graph on `Fin n` with the given (undirected) edge list. -/
def edgeGraph (n : ℕ) (es : List (ℕ × ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => (a.val, b.val) ∈ es

instance (n : ℕ) (es : List (ℕ × ℕ)) : DecidableRel (edgeGraph n es).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ ((a.val, b.val) ∈ es ∨ (b.val, a.val) ∈ es)))

/-- `θ(5,5,5)`. -/
def thetaG : SimpleGraph (Fin 14) :=
  edgeGraph 14 [(4,0),(0,1),(1,2),(2,3),(3,5),(4,6),(6,7),(7,8),(8,9),(9,5),
    (4,10),(10,11),(11,12),(12,13),(13,5)]

instance : DecidableRel thetaG.Adj := inferInstanceAs (DecidableRel (edgeGraph _ _).Adj)

/-- Height of a node of `θ(5,5,5)`. -/
def thetaH (v : Fin 14) : ℤ :=
  if v.val = 4 then -1 else if v.val = 5 then 4 else if v.val < 4 then v.val
  else if v.val < 10 then v.val - 6 else v.val - 10

lemma thetaH_adj : ∀ v w : Fin 14, thetaG.Adj v w → thetaH w = thetaH v + 1 ∨ thetaH w = thetaH v - 1 := by
  decide

lemma thetaG_degree : ∀ v : Fin 14, thetaG.degree v = if v.val = 4 ∨ v.val = 5 then 3 else 2 := by
  decide


/-- Index of the path containing an inner node. -/
def thetaPath (w : Fin 14) : ℕ := if w.val < 4 then 0 else if w.val < 10 then 1 else 2

/-- Port numbering of `θ(5,5,5)`. -/
def thetaPort (v w : Fin 14) : ℕ :=
  if v.val = 4 ∨ v.val = 5 then thetaPath w else if thetaH w < thetaH v then 0 else 1

lemma thetaPort_lt : ∀ v w : Fin 14, thetaG.Adj v w → thetaPort v w < thetaG.degree v := by
  intro v w h
  rw [thetaG_degree]
  revert v w h
  decide

lemma thetaPort_inj : ∀ v w w' : Fin 14, thetaG.Adj v w → thetaG.Adj v w' →
    thetaPort v w = thetaPort v w' → w = w' := by
  decide

/-- Rotating identifiers. -/
def thetaId (s : ℕ) (v : Fin 14) : ℕ := if v.val < 5 then (s + v.val) % 5 else v.val

lemma thetaId_inj (s : ℕ) : Function.Injective (thetaId s) := by
  intro a b h
  unfold thetaId at h
  apply Fin.ext
  split_ifs at h <;> omega

lemma thetaId_lt (s : ℕ) (v : Fin 14) : thetaId s v < 14 := by
  unfold thetaId; split_ifs <;> omega

/-- `θ(5,5,5)` with ports and rotating identifiers (rotation `s`), and the value `N ≥ 14`. -/
abbrev thetaPG (s N : ℕ) (hN : 14 ≤ N) : PortGraph where
  V := Fin 14
  G := thetaG
  port := thetaPort
  port_lt := fun {v w} h => thetaPort_lt v w h
  port_inj := fun {v w w'} h h' e => thetaPort_inj v w w' h h' e
  id := thetaId s
  id_inj := thetaId_inj s
  N := N
  id_lt v := lt_of_lt_of_le (thetaId_lt s v) hN

/-- The counter labelling `v ↦ t + h v`. -/
def thetaLabel {M : ℕ} [NeZero M] (t : ZMod M) (v : Fin 14) : ℕ := (t + (thetaH v : ZMod M)).val


lemma val_add_one_mod_five (N : ℕ) (t : ZMod (modulus N)) (i : ℕ) :
    ((t + 1).val + i) % 5 = (t.val + 1 + i) % 5 := by
  have h1 : (1 : ZMod (modulus N)).val = 1 := ZMod.val_one_eq_one_mod _ ▸ by
    unfold modulus; rw [Nat.mod_eq_of_lt (by omega)]
  rw [ZMod.val_add, h1]
  have h5 : 5 ∣ modulus N := ⟨_, rfl⟩
  rw [Nat.add_mod ((t.val + 1) % modulus N), Nat.mod_mod_of_dvd _ h5, ← Nat.add_mod]

lemma thetaG_adj1 : ∀ w : Fin 14, thetaG.Adj 1 w ↔ w ∈ ({0, 2} : Finset (Fin 14)) := by decide
lemma thetaG_adj2 : ∀ w : Fin 14, thetaG.Adj 2 w ↔ w ∈ ({1, 3} : Finset (Fin 14)) := by decide

/-- The view of node `2` at parameter `t` equals the view of node `1` at parameter `t + 1`. -/
lemma view_shift (N : ℕ) (hN : 14 ≤ N) (t : ZMod (modulus N)) :
    (thetaPG (t + 1).val N hN).view (thetaLabel (t + 1)) (1 : Fin 14) =
      (thetaPG t.val N hN).view (thetaLabel t) (2 : Fin 14) := by
  rw [PortGraph.view_eq_mk (P := thetaPG (t + 1).val N hN) ({0, 2} : Finset (Fin 14))
      thetaG_adj1,
    PortGraph.view_eq_mk (P := thetaPG t.val N hN) ({1, 3} : Finset (Fin 14)) thetaG_adj2]
  simp only [PortGraph.nbrInfo, thetaPG, View.mk.injEq, true_and]
  have hid : ∀ i : ℕ, ((t + 1).val + i) % 5 = (t.val + (i + 1)) % 5 := fun i => by
    rw [val_add_one_mod_five]; ring_nf
  have hlab : ∀ a b : Fin 14, thetaH b = thetaH a + 1 → thetaLabel (t + 1) a = thetaLabel t b :=
    fun a b h => by
      unfold thetaLabel; rw [h]; congr 1; push_cast; ring
  refine ⟨?_, hlab 1 2 (by decide), ?_⟩
  · simpa [thetaId] using hid 1
  · refine ⟨by decide, ?_⟩
    rw [show ({0, 2} : Finset (Fin 14)).val = (0 : Fin 14) ::ₘ {2} by decide,
      show ({1, 3} : Finset (Fin 14)).val = (1 : Fin 14) ::ₘ {3} by decide]
    simp only [Multiset.map_cons, Multiset.map_singleton, PortGraph.nbrInfo]
    have e1 : thetaId (t + 1).val 0 = thetaId t.val 1 := by simpa [thetaId] using hid 0
    have e2 : thetaId (t + 1).val 2 = thetaId t.val 3 := by simpa [thetaId] using hid 2
    rw [e1, e2, hlab 0 1 (by decide), hlab 2 3 (by decide)]
    simp only [show thetaPort 1 0 = 0 by decide, show thetaPort 2 1 = 0 by decide,
      show thetaPort 0 1 = 1 by decide, show thetaPort 1 2 = 1 by decide,
      show thetaPort 2 3 = 1 by decide, show thetaPort 3 2 = 0 by decide,
      show thetaG.degree 0 = 2 by decide, show thetaG.degree 1 = 2 by decide,
      show thetaG.degree 2 = 2 by decide, show thetaG.degree 3 = 2 by decide]


variable {bound : ℕ → ℕ}

lemma thetaPG_admissible (t : ℕ) (hb : 14 ≤ bound 14) :
    (thetaPG t (bound 14) hb).Admissible bound := by
  simp [PortGraph.Admissible]

lemma thetaLabel_sizeOK (hb : 14 ≤ bound 14) (s : ℕ) (t : ZMod (modulus (bound 14))) :
    (counterLCP bound).SizeOK (thetaPG s (bound 14) hb) (thetaLabel t) := by
  intro v
  show thetaLabel t v < modulus (bound (Fintype.card (Fin 14)))
  rw [Fintype.card_fin]
  exact ZMod.val_lt _

lemma thetaLabel_acc (N : ℕ) (hN : 14 ≤ N) (s : ℕ) (t : ZMod (modulus N)) (v : Fin 14) :
    (counterLCP bound).Acc (thetaPG s N hN) (thetaLabel t) v := by
  rw [counterLCP_acc_iff]
  intro w hw
  unfold CounterStep
  simp only [thetaPG, thetaLabel, ZMod.natCast_zmod_val]
  rcases thetaH_adj v w hw with h | h
  · left; rw [h]; push_cast; ring
  · right; rw [h]; push_cast; ring

lemma fin_two_eq_add_one {a b : Fin 2} (h : a ≠ b) : a = b + 1 := by
  revert a b; decide

/-- **Shift argument.** Let `I t` (`t ∈ ZMod M`, `M` odd) be accepted, admissible instances of
`H` with adjacent nodes `a t ~ b t` such that the view of `b t` in `I t` equals the view of
`a (t+1)` in `I (t+1)`. Then the LCP is hiding (against every extraction algorithm): an
algorithm succeeding everywhere would flip its output at `a t` with every step `t ↦ t + 1`. -/
theorem hiding_of_shift {L : Type} (S : LCP L) (bound : ℕ → ℕ) (H : GraphClass) (M : ℕ)
    [NeZero M] (hM : Odd M) (I : ZMod M → PortGraph) (ℓ : ∀ t, (I t).V → L)
    (hadm : ∀ t, (I t).Admissible bound) (hH : ∀ t, H (I t).V (I t).G)
    (hsz : ∀ t, S.SizeOK (I t) (ℓ t)) (hacc : ∀ t v, S.Acc (I t) (ℓ t) v)
    (a b : ∀ t, (I t).V) (hab : ∀ t, (I t).G.Adj (a t) (b t))
    (hshift : ∀ t, (I (t + 1)).view (ℓ (t + 1)) (a (t + 1)) = (I t).view (ℓ t) (b t)) :
    S.Hiding bound H 2 := by
  intro A
  by_contra hcon
  push Not at hcon
  let g : ZMod M → Fin 2 := fun t => A ((I t).view (ℓ t) (a t))
  have step : ∀ t, g (t + 1) = g t + 1 := by
    intro t
    apply fin_two_eq_add_one
    intro h
    apply hcon _ (hadm t) (hH t) _ (hsz t) (hacc t)
    refine ⟨a t, b t, hab t, ?_⟩
    simp only [g] at h
    rw [hshift t] at h
    exact h.symm
  have hn : ∀ n : ℕ, g ((n : ℕ) : ZMod M) = if n % 2 = 0 then g 0 else g 0 + 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast; rw [step, ih]
      generalize g 0 = a
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · rw [ite_eq_left h, ite_eq_right (by omega)]
      · rw [ite_eq_right (by omega), ite_eq_left (by omega)]; revert a; decide
  have hM' := hn M
  rw [ZMod.natCast_self, ite_eq_right (by exact Nat.odd_iff.1 hM ▸ by decide)] at hM'
  revert hM'; generalize g 0 = a; revert a; decide

/-- **The counter LCP is hiding** on every class containing `θ(5,5,5)`, against every extraction
algorithm (identifier-aware or not). -/
theorem counterLCP_hiding (hb : 14 ≤ bound 14) (H : GraphClass) (hH : H (Fin 14) thetaG) :
    (counterLCP bound).Hiding bound H 2 :=
  hiding_of_shift (counterLCP bound) bound H (modulus (bound 14)) (modulus_odd _)
    (fun t => thetaPG t.val (bound 14) hb) (fun t => thetaLabel t)
    (fun t => thetaPG_admissible _ hb) (fun _ => hH) (fun t => thetaLabel_sizeOK hb _ t)
    (fun t => thetaLabel_acc _ hb _ t) (fun _ => (1 : Fin 14)) (fun _ => (2 : Fin 14))
    (fun _ => show thetaG.Adj 1 2 by decide) (fun t => view_shift (bound 14) hb t)

end Podc.HidingColoringCertification
