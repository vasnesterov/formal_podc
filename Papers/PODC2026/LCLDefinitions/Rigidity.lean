import Papers.PODC2026.LCLDefinitions.Gadget

/-!
# Rigidity of edge-consistent distance-2 colourings of gadgeted graphs

The graph-theoretic core of (our repaired) Theorem 5.1 of *It does not matter how you define
locally checkable labelings* (Cruciani, Das, Raevskaya, Suomela; PODC 2026). Throughout, `χ` is a
distance-2 colouring of the gadgeted graph `B.graph` that is edge-consistent everywhere
(`IsEdgeConsistent`).

* `orig_ne_gad`: an original vertex never has the colour of a gadget vertex (paper: Lemma 5.9,
  Corollary 5.10).
* `rigid`: if two expanded edges leave vertices of the same colour and their first vertices have
  the same colour, then they have the same length, their far ends have the same colour, and the
  colours along them agree gadget by gadget up to the symmetry of the A-gadget (paper: the
  inductions in Lemmas 5.12 and 5.13).
* `match_pos`: a vertex `b` with the colour of position `k` of an expanded edge `d` *is* the
  corresponding position of an expanded edge `d'` whose start has the colour of `start d`.
-/

namespace Podc.LCLDefinitions

namespace Base

variable {B : Base} {C : Type*} {χ : B.Vert → C}

lemma prevV_zero (d : B.Dir) : prevV d 0 = .orig (start d) := by simp [prevV]

/-- The neighbours of an original vertex are first vertices of gadgets hanging at it. -/
lemma orig_hO (o : B.V) : ∀ y, B.graph.Adj (.orig o) y →
    ∃ p1 p2 p3 p4 p5 nx, BlockFacts B.graph (.orig o) y p1 p2 p3 p4 p5 nx := by
  intro y hy
  obtain ⟨d, rfl, hL, rfl⟩ := (adj_orig_iff o y).1 hy
  have := blockFacts d (i := 0) hL
  simp only [mul_zero, zero_add, prevV_zero] at this
  exact ⟨_, _, _, _, _, _, this⟩

/-- Every gadget vertex lies in a triangle. -/
lemma gad_triangle (e : B.E) (k : Fin (6 * B.len e)) :
    ∃ c1 c2, B.graph.Adj (.gad e k) c1 ∧ B.graph.Adj (.gad e k) c2 ∧ B.graph.Adj c1 c2 := by
  rw [gad_eq_pos]
  set d : B.Dir := (e, true)
  have hk : k.val < 6 * B.len d.1 := k.isLt
  have bf := blockFacts d (i := k.val / 6) (by simp [d]; omega)
  have hk' : k.val = 6 * (k.val / 6) + k.val % 6 := by omega
  have hm : k.val % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rw [hk']
  interval_cases h : k.val % 6
  · exact ⟨_, _, bf.a01, bf.a02, bf.a12⟩
  · exact ⟨_, _, bf.a01.symm, bf.a12, bf.a02⟩
  · exact ⟨_, _, bf.a02.symm, bf.a12.symm, bf.a01⟩
  · exact ⟨_, _, bf.a34, bf.a35, bf.a45⟩
  · exact ⟨_, _, bf.a34.symm, bf.a45, bf.a35⟩
  · exact ⟨_, _, bf.a35.symm, bf.a45.symm, bf.a34⟩

/-- An original vertex never has the colour of a gadget vertex (paper: Lemma 5.9 and
Corollary 5.10, for globally edge-consistent colourings). -/
theorem orig_ne_gad (hD : B.IsDist2Coloring χ) (hC : B.IsEdgeConsistent χ) (o : B.V) (e : B.E)
    (k : Fin (6 * B.len e)) : χ (.orig o) ≠ χ (.gad e k) := by
  obtain ⟨c1, c2, h1, h2, h12⟩ := gad_triangle e k
  exact ne_of_triangle hD hC (orig_hO o) h1 h2 h12

theorem orig_ne_pos (hD : B.IsDist2Coloring χ) (hC : B.IsEdgeConsistent χ) (o : B.V) (d : B.Dir)
    {k : ℕ} (hk : k < 6 * B.len d.1) : χ (.orig o) ≠ χ (pos d k) := by
  obtain ⟨m, hm⟩ := pos_eq_gad d hk
  rw [hm]; exact orig_ne_gad hD hC o _ _

/-- Colours along `d` and `d'` agree on the `i`-th gadget, possibly up to the symmetry
`1 ↔ 2, 3 ↔ 4` of the A-gadget. -/
def BlockMatch (χ : B.Vert → C) (d d' : B.Dir) (i : ℕ) : Prop :=
  χ (pos d (6 * i)) = χ (pos d' (6 * i)) ∧ χ (pos d (6 * i + 5)) = χ (pos d' (6 * i + 5)) ∧
  ((χ (pos d (6 * i + 1)) = χ (pos d' (6 * i + 1)) ∧ χ (pos d (6 * i + 2)) = χ (pos d' (6 * i + 2)) ∧
    χ (pos d (6 * i + 3)) = χ (pos d' (6 * i + 3)) ∧ χ (pos d (6 * i + 4)) = χ (pos d' (6 * i + 4))) ∨
   (χ (pos d (6 * i + 1)) = χ (pos d' (6 * i + 2)) ∧ χ (pos d (6 * i + 2)) = χ (pos d' (6 * i + 1)) ∧
    χ (pos d (6 * i + 3)) = χ (pos d' (6 * i + 4)) ∧ χ (pos d (6 * i + 4)) = χ (pos d' (6 * i + 3))))

lemma prevV_succ (d : B.Dir) (i : ℕ) : prevV d (6 * (i + 1)) = pos d (6 * i + 5) := by
  simp only [prevV]; rw [if_neg (by omega)]; congr 1

lemma nextV_of_lt (d : B.Dir) {i : ℕ} (h : i + 1 < B.len d.1) :
    nextV d (6 * i + 5) = pos d (6 * (i + 1)) := by
  simp only [nextV]; rw [if_neg (by omega)]; congr 1

lemma nextV_last (d : B.Dir) {i : ℕ} (h : i + 1 = B.len d.1) :
    nextV d (6 * i + 5) = .orig (stop d) := by
  simp only [nextV]; rw [if_pos (by omega)]

/-- Rigidity of expanded edges (paper: the inductions of Lemmas 5.12–5.13, for globally
edge-consistent colourings). -/
theorem rigid (hD : B.IsDist2Coloring χ) (hC : B.IsEdgeConsistent χ) {d d' : B.Dir}
    (hL : 0 < B.len d.1) (hL' : 0 < B.len d'.1)
    (hs : χ (.orig (start d)) = χ (.orig (start d'))) (h0 : χ (pos d 0) = χ (pos d' 0)) :
    B.len d.1 = B.len d'.1 ∧ χ (.orig (stop d)) = χ (.orig (stop d')) ∧
      ∀ i < B.len d.1, BlockMatch χ d d' i := by
  -- invariant at the start of block `i`
  have Q : ∀ i, i < B.len d.1 → i < B.len d'.1 →
      χ (prevV d (6 * i)) = χ (prevV d' (6 * i)) ∧ χ (pos d (6 * i)) = χ (pos d' (6 * i)) := by
    intro i
    induction i with
    | zero => intro _ _; simpa [prevV_zero] using ⟨hs, h0⟩
    | succ i ih =>
      intro hi hi'
      obtain ⟨a, b⟩ := ih (by omega) (by omega)
      obtain ⟨-, h5, hx⟩ := block_step hD hC (blockFacts d (i := i) (by omega))
        (blockFacts d' (i := i) (by omega)) a b
      rw [nextV_of_lt d hi, nextV_of_lt d' hi'] at hx
      exact ⟨by rw [prevV_succ, prevV_succ]; exact h5, hx⟩
  have step : ∀ i, i < B.len d.1 → i < B.len d'.1 → BlockMatch χ d d' i ∧
      χ (nextV d (6 * i + 5)) = χ (nextV d' (6 * i + 5)) := by
    intro i hi hi'
    obtain ⟨a, b⟩ := Q i hi hi'
    obtain ⟨m, h5, hx⟩ := block_step hD hC (blockFacts d (i := i) hi) (blockFacts d' (i := i) hi') a b
    exact ⟨⟨b, h5, m⟩, hx⟩
  have hlen : B.len d.1 = B.len d'.1 := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨-, hx⟩ := step (B.len d.1 - 1) (by omega) (by omega)
      rw [nextV_last d (by omega), nextV_of_lt d' (by omega)] at hx
      exact orig_ne_pos hD hC _ d' (by omega) hx
    · obtain ⟨-, hx⟩ := step (B.len d'.1 - 1) (by omega) (by omega)
      rw [nextV_of_lt d (by omega), nextV_last d' (by omega)] at hx
      exact orig_ne_pos hD hC _ d (by omega) hx.symm
  refine ⟨hlen, ?_, fun i hi => (step i hi (hlen ▸ hi)).1⟩
  obtain ⟨-, hx⟩ := step (B.len d.1 - 1) (by omega) (by omega)
  rwa [nextV_last d (by omega), nextV_last d' (by omega)] at hx

/-- The symmetry `1 ↔ 2, 3 ↔ 4` of the A-gadget (in our numbering). -/
def tau (j : ℕ) : ℕ := if j = 1 then 2 else if j = 2 then 1 else if j = 3 then 4 else if j = 4 then 3 else j

lemma tau_lt {j : ℕ} (h : j < 6) : tau j < 6 := by unfold tau; split_ifs <;> omega

lemma innerAdj_tau {s t : ℕ} (h : InnerAdj s t) : InnerAdj (tau s) (tau t) := by
  unfold InnerAdj at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [tau, InnerAdj]

open Classical in
/-- The position on `d'` matching position `k` on `d` (identity, or the symmetry `tau` on the
gadget if the colours of the gadget are matched with a flip). -/
noncomputable def psi (χ : B.Vert → C) (d d' : B.Dir) (k : ℕ) : ℕ :=
  6 * (k / 6) + if χ (pos d (6 * (k / 6) + 1)) = χ (pos d' (6 * (k / 6) + 1)) then k % 6 else tau (k % 6)

lemma psi_eq (d d' : B.Dir) {p s : ℕ} (hs : s < 6) :
    ∃ f : Bool, psi χ d d' (6 * p + s) = 6 * p + (if f then tau s else s) ∧
      ∀ t < 6, psi χ d d' (6 * p + t) = 6 * p + (if f then tau t else t) := by
  classical
  have e1 : ∀ t < 6, (6 * p + t) / 6 = p := fun t ht => by omega
  have e2 : ∀ t < 6, (6 * p + t) % 6 = t := fun t ht => by omega
  refine ⟨!decide (χ (pos d (6 * p + 1)) = χ (pos d' (6 * p + 1))), ?_, ?_⟩ <;>
  · intros
    simp only [psi, e1 _ (by assumption), e2 _ (by assumption)]
    by_cases h : χ (pos d (6 * p + 1)) = χ (pos d' (6 * p + 1)) <;> simp [h]

lemma psi_lt (d d' : B.Dir) {k L : ℕ} (hk : k < 6 * L) : psi χ d d' k < 6 * L := by
  obtain ⟨p, s, hs, rfl⟩ : ∃ p s, s < 6 ∧ k = 6 * p + s := ⟨k / 6, k % 6, by omega, by omega⟩
  obtain ⟨f, hf, -⟩ := psi_eq (χ := χ) d d' (p := p) hs
  rw [hf]; have := tau_lt hs; split_ifs <;> omega

lemma psi_zero (d d' : B.Dir) : psi χ d d' 0 = 0 := by
  simp [psi, tau]

lemma psi_cadj (d d' : B.Dir) {k k' : ℕ} (h : CAdj k k') : CAdj (psi χ d d' k) (psi χ d d' k') := by
  obtain ⟨p, s, hs, rfl⟩ : ∃ p s, s < 6 ∧ k = 6 * p + s := ⟨k / 6, k % 6, by omega, by omega⟩
  obtain ⟨q, t, ht, rfl⟩ : ∃ q t, t < 6 ∧ k' = 6 * q + t := ⟨k' / 6, k' % 6, by omega, by omega⟩
  obtain ⟨f, hf, hf'⟩ := psi_eq (χ := χ) d d' (p := p) hs
  obtain ⟨g, hg, -⟩ := psi_eq (χ := χ) d d' (p := q) ht
  rw [cadj_iff hs ht] at h
  rcases h with ⟨rfl, hi⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [hf, hf' t ht]
    apply cadj_in
    cases f
    · simpa using hi
    · simpa using innerAdj_tau hi
  · rw [hf, hg]
    have : (if f = true then tau 5 else 5) = 5 := by simp [tau]
    have h2 : (if g = true then tau 0 else 0) = 0 := by simp [tau]
    rw [this, h2, show 6 * (p + 1) + 0 = 6 * p + 5 + 1 by ring]
    exact cadj_succ _
  · rw [hf, hg]
    have : (if f = true then tau 0 else 0) = 0 := by simp [tau]
    have h2 : (if g = true then tau 5 else 5) = 5 := by simp [tau]
    rw [this, h2, show 6 * (q + 1) + 0 = 6 * q + 5 + 1 by ring]
    exact cadj_symm (cadj_succ _)

lemma psi_spec (hD : B.IsDist2Coloring χ) {d d' : B.Dir} {i : ℕ} (hi' : i < B.len d'.1)
    (hm : BlockMatch χ d d' i) {j : ℕ} (hj : j < 6) :
    χ (pos d (6 * i + j)) = χ (pos d' (psi χ d d' (6 * i + j))) := by
  have e1 : (6 * i + j) / 6 = i := by omega
  have e2 : (6 * i + j) % 6 = j := by omega
  obtain ⟨m0, m5, hm⟩ := hm
  have bf := blockFacts d' hi'
  simp only [psi, e2]
  split_ifs with hc
  · rw [e1] at hc ⊢
    rcases hm with ⟨m1, m2, m3, m4⟩ | ⟨m1, m2, m3, m4⟩
    · interval_cases j <;> first | assumption | simpa using m0
    · exact absurd (m1.symm.trans hc) (hD.ne_adj bf.a12.symm)
  · rw [e1] at hc ⊢
    rcases hm with ⟨m1, m2, m3, m4⟩ | ⟨m1, m2, m3, m4⟩
    · exact absurd m1 hc
    · interval_cases j <;> simp only [tau] <;> first | assumption | simpa using m0 | (norm_num; assumption)

/-- A vertex with the colour of position `k` of an expanded edge `d` is the matching position of an
expanded edge `d'` whose start has the colour of `start d` (paper: Corollary 5.15 and the end of
the proof of Lemma 5.13, for globally edge-consistent colourings). -/
theorem match_pos (hD : B.IsDist2Coloring χ) (hC : B.IsEdgeConsistent χ) (d : B.Dir) :
    ∀ k < 6 * B.len d.1, ∀ b, χ b = χ (pos d k) →
      ∃ d' : B.Dir, 0 < B.len d'.1 ∧ χ (.orig (start d')) = χ (.orig (start d)) ∧
        χ (pos d' 0) = χ (pos d 0) ∧ b = pos d' (psi χ d d' k) := by
  intro k
  induction k with
  | zero =>
    intro hk b hb
    obtain ⟨β, hβ, hβc⟩ := hC.step hb (adj_prevV d hk).symm
    rw [prevV_zero] at hβc
    cases β with
    | gad e m => exact absurd hβc.symm (orig_ne_gad hD hC _ e m)
    | orig o =>
      obtain ⟨d', rfl, hL', rfl⟩ := (adj_orig_iff o b).1 hβ.symm
      exact ⟨d', hL', hβc, hb, by rw [psi_zero]⟩
  | succ k ih =>
    intro hk b hb
    obtain ⟨b', hb', hb'c⟩ := hC.step hb (adj_pp d hk (by omega) (cadj_symm (cadj_succ k)))
    obtain ⟨d', hL', hs, h0, rfl⟩ := ih (by omega) b' hb'c
    obtain ⟨hlen, -, hmatch⟩ := rigid hD hC (by omega) hL' hs.symm h0.symm
    refine ⟨d', hL', hs, h0, ?_⟩
    -- `b` and the matching position of `k + 1` are neighbours of `b'` with the same colour
    have hk1 : k + 1 = 6 * ((k + 1) / 6) + (k + 1) % 6 := by omega
    have hspec := psi_spec hD (d := d) (d' := d') (i := (k + 1) / 6) (by rw [← hlen]; omega)
      (hmatch _ (by omega)) (j := (k + 1) % 6) (Nat.mod_lt _ (by norm_num))
    rw [← hk1] at hspec
    have hadj : B.graph.Adj (pos d' (psi χ d d' k)) (pos d' (psi χ d d' (k + 1))) :=
      adj_pp d' (psi_lt d d' (by rw [← hlen]; omega)) (psi_lt d d' (by rw [← hlen]; omega))
        (psi_cadj d d' (cadj_succ k))
    exact hD.eq_of_common hb'.symm hadj (hb.trans hspec)

end Base

end Podc.LCLDefinitions
