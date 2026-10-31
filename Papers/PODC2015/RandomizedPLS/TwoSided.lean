import Papers.PODC2015.RandomizedPLS.LowerBound

/-!
# Lower bounds for two-sided edge-independent RPLS (Proposition 4.6, Theorem 4.7)

M. Baruch, P. Fraigniaud, B. Patt-Shamir. *Randomized Proof-Labeling Schemes.* PODC 2015 [BFP15].

The proof follows the paper's idea (round the certificate distributions of the copies, pigeonhole,
hybrid argument over the arcs of the two crossed copies) with a cleaner bookkeeping:

* `EIScheme.accProb_eq_sum` (edge independence): the acceptance probability is the expectation of
  the acceptance event `accEvent` under a product distribution over the *receiving slots*
  `(x, q)` (`Config.Ports`); slot `(x, q)` independently receives a certificate distributed as the
  certificates that the neighbour `sender (x, q)` sends on its port towards `x` (`slotDist`).
  The event only depends on states, labels and degrees, so it is the same in `c` and in the
  crossing; only the slot distributions change, and only on the `≤ 4s` slots on arcs of the two
  crossed copies (`Copies.slotDist_cross`, `Copies.card_arcSlots_le`).
* `abs_sum_mul_prod_sub_le` (hybrid argument): two product distributions give expectations of a
  `[-1, 1]`-valued function that differ by at most `∑_slots ‖μ_slot - ν_slot‖₁`.
* Pigeonhole on the `1/m`-rounded *marginal* distributions of the `2s` arcs of each copy
  (`m = 12 s 2^(κ+1) + 1`), instead of the paper's rounding of the joint distribution over all
  `2^(2sκ)` certificate vectors of a copy.

## Main statements

* `prop_4_6`: if `r > crossingBound κ s = (12 s 2^(κ+1) + 2)^(2 s 2^(κ+1))`, two copies can be
  crossed changing the acceptance probability by less than `1/3`.
* `thm_4_7_correct`: for a two-sided edge-independent RPLS, a legal configuration whose crossings
  are all illegal has `r ≤ crossingBound (κ c) s`; `thm_4_7_loglog`:
  `log log r ≤ 2 κ + 5 + 2 log s`, i.e. `κ = Ω(log log r)` for bounded `s` (the paper states
  `Ω(log log r / s)`; our bound is stronger in `s`).
-/

namespace Podc.RandomizedPLS

open Classical Finset Cslib.Probability

/-! ### Product distributions: changing the factors -/

section ProductBound

variable {ι B : Type*} [Fintype ι] [DecidableEq ι] [Fintype B]

-- CSLib candidate
/-- Changing one factor of a product distribution changes the expectation of a `[-1, 1]`-valued
function by at most the `ℓ¹` distance between the old and the new factor. -/
theorem abs_sum_mul_prod_update_sub_le (μ : ι → B → ℝ) (hμ0 : ∀ i b, 0 ≤ μ i b)
    (hμ1 : ∀ i, ∑ b, μ i b = 1) (a : ι) (ν : B → ℝ) (g : (ι → B) → ℝ) (hg : ∀ y, |g y| ≤ 1) :
    |∑ y, g y * ∏ i, μ i (y i) - ∑ y, g y * ∏ i, Function.update μ a ν i (y i)| ≤
      ∑ b, |μ a b - ν b| := by
  set h : ι → B → ℝ := Function.update μ a (fun b => |μ a b - ν b|) with hh
  have key : ∀ y : ι → B,
      |∏ i, μ i (y i) - ∏ i, Function.update μ a ν i (y i)| = ∏ i, h i (y i) := by
    intro y
    rw [← Finset.mul_prod_erase univ (fun i => μ i (y i)) (mem_univ a),
      ← Finset.mul_prod_erase univ (fun i => Function.update μ a ν i (y i)) (mem_univ a),
      ← Finset.mul_prod_erase univ (fun i => h i (y i)) (mem_univ a)]
    have e1 : ∏ i ∈ univ.erase a, Function.update μ a ν i (y i) =
        ∏ i ∈ univ.erase a, μ i (y i) :=
      prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)]
    have e2 : ∏ i ∈ univ.erase a, h i (y i) = ∏ i ∈ univ.erase a, μ i (y i) :=
      prod_congr rfl fun i hi => by rw [hh, Function.update_of_ne (ne_of_mem_erase hi)]
    rw [e1, e2, hh]
    simp only [Function.update_self]
    rw [← sub_mul, abs_mul, abs_of_nonneg (prod_nonneg fun i _ => hμ0 i _)]
  calc _ = |∑ y, g y * (∏ i, μ i (y i) - ∏ i, Function.update μ a ν i (y i))| := by
        rw [← sum_sub_distrib]; simp_rw [mul_sub]
    _ ≤ ∑ y, |g y * (∏ i, μ i (y i) - ∏ i, Function.update μ a ν i (y i))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, ∏ i, h i (y i) := sum_le_sum fun y _ => by
        rw [abs_mul, key]
        exact mul_le_of_le_one_left (prod_nonneg fun i _ => by
          rw [hh]; by_cases hi : i = a
          · subst hi; simp
          · rw [Function.update_of_ne hi]; exact hμ0 _ _) (hg y)
    _ = ∏ i, ∑ b, h i b := (Fintype.prod_sum h).symm
    _ = ∑ b, |μ a b - ν b| := by
        rw [← Finset.mul_prod_erase univ (fun i => ∑ b, h i b) (mem_univ a),
          prod_eq_one fun i hi => by rw [hh, Function.update_of_ne (ne_of_mem_erase hi)]; exact hμ1 i]
        simp [hh]

-- CSLib candidate
/-- **Hybrid argument for product distributions.** For two product distributions on `ι → B` and a
`[-1, 1]`-valued function `g`, the expectations of `g` differ by at most the sum over the
coordinates of the `ℓ¹` distances between the factors. -/
theorem abs_sum_mul_prod_sub_le (μ ν : ι → B → ℝ) (hμ0 : ∀ i b, 0 ≤ μ i b)
    (hμ1 : ∀ i, ∑ b, μ i b = 1) (hν0 : ∀ i b, 0 ≤ ν i b) (hν1 : ∀ i, ∑ b, ν i b = 1)
    (g : (ι → B) → ℝ) (hg : ∀ y, |g y| ≤ 1) :
    |∑ y, g y * ∏ i, μ i (y i) - ∑ y, g y * ∏ i, ν i (y i)| ≤ ∑ i, ∑ b, |μ i b - ν i b| := by
  suffices H : ∀ T : Finset ι, ∀ μ : ι → B → ℝ, (∀ i b, 0 ≤ μ i b) → (∀ i, ∑ b, μ i b = 1) →
      (∀ i ∉ T, μ i = ν i) →
      |∑ y, g y * ∏ i, μ i (y i) - ∑ y, g y * ∏ i, ν i (y i)| ≤
        ∑ i ∈ T, ∑ b, |μ i b - ν i b| from
    H univ μ hμ0 hμ1 (fun i hi => absurd (mem_univ i) hi)
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro μ _ _ hμ
    have : μ = ν := funext fun i => hμ i (notMem_empty i)
    subst this; simp
  | insert a T haT ih =>
    intro μ hμ0 hμ1 hμ
    set ρ := Function.update μ a (ν a) with hρdef
    have hρ0 : ∀ i b, 0 ≤ ρ i b := by
      intro i b; by_cases h : i = a
      · subst h; simp [ρ, hν0]
      · rw [hρdef, Function.update_of_ne h]; exact hμ0 i b
    have hρ1 : ∀ i, ∑ b, ρ i b = 1 := by
      intro i; by_cases h : i = a
      · subst h; simp [ρ, hν1]
      · rw [hρdef, Function.update_of_ne h]; exact hμ1 i
    have hρ : ∀ i ∉ T, ρ i = ν i := by
      intro i hi; by_cases h : i = a
      · subst h; simp [ρ]
      · rw [hρdef, Function.update_of_ne h]; exact hμ i (by simp [h, hi])
    have h1 := abs_sum_mul_prod_update_sub_le μ hμ0 hμ1 a (ν a) g hg
    have h2 := ih ρ hρ0 hρ1 hρ
    have h3 : ∑ i ∈ T, ∑ b, |ρ i b - ν i b| = ∑ i ∈ T, ∑ b, |μ i b - ν i b| :=
      sum_congr rfl fun i hi => by
        rw [hρdef, Function.update_of_ne (ne_of_mem_of_not_mem hi haT)]
    rw [sum_insert haT]
    rw [h3] at h2
    calc _ ≤ |∑ y, g y * ∏ i, μ i (y i) - ∑ y, g y * ∏ i, ρ i (y i)| +
          |∑ y, g y * ∏ i, ρ i (y i) - ∑ y, g y * ∏ i, ν i (y i)| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add h1 h2

end ProductBound

/-! ### Uniform probability of an event of finitely many independent observations -/

section Representation

-- CSLib candidate
/-- `uprob` is invariant under a bijection of the sample space. -/
theorem uprob_comp_equiv_eq {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (f : Ω ≃ Ω') (E : Ω' → Prop) :
    uprob (fun ω => E (f ω)) = uprob E := by
  unfold uprob
  rw [Fintype.card_congr f, Nat.card_congr (f.subtypeEquiv fun _ => Iff.rfl)]

variable {ι ι' B : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype B]
  {α : ι → Type*}
  [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]

-- CSLib candidate
/-- **Independent observations.** Under the uniform distribution on `∀ i, α i`, observe the
coordinates `h s` (`h` injective) through `g s`. Any event `E` of the observations has
probability `∑_y [E y] ∏_s Pr[g s = y s]`: the observations are independent. -/
theorem uprob_comp_eq_sum (h : ι' → ι) (hh : Function.Injective h) (g : ∀ s, α (h s) → B)
    (E : (ι' → B) → Prop) :
    uprob (fun ω : ∀ i, α i => E fun s => g s (ω (h s))) =
      ∑ y : ι' → B, (if E y then 1 else 0) * ∏ s, uprob (fun a => g s a = y s) := by
  set t : (∀ i, α i) → ι' → B := fun ω s => g s (ω (h s)) with ht
  -- step 1: the probability of a point `y`
  have hpt : ∀ y : ι' → B, uprob (fun ω => t ω = y) = ∏ s, uprob (fun a => g s a = y s) := by
    intro y
    let P : ∀ i, α i → Prop := fun i a =>
      ∀ s (hs : h s = i), g s (cast (congrArg α hs).symm a) = y s
    have hP : (fun ω => t ω = y) = fun ω => ∀ i, P i (ω i) := by
      funext ω
      apply propext
      constructor
      · intro hω i s hs
        subst hs
        exact congrFun hω s
      · intro hω
        funext s
        exact hω (h s) s rfl
    rw [hP, uprob_pi]
    have h1 : ∀ i ∉ univ.image h, uprob (P i) = 1 := by
      intro i hi
      have : P i = fun _ => True := by
        funext a
        apply propext
        refine ⟨fun _ => trivial, fun _ s hs => absurd (mem_image.2 ⟨s, mem_univ _, hs⟩) hi⟩
      rw [this, uprob_true, ite_eq_right_iff.2 fun h => absurd h Fintype.card_ne_zero]
    rw [← Finset.prod_subset (subset_univ (univ.image h)) fun i _ hi => h1 i hi,
      prod_image fun s _ s' _ hs => hh hs]
    refine prod_congr rfl fun s _ => ?_
    congr 1
    funext a
    apply propext
    constructor
    · intro ha
      exact ha s rfl
    · intro ha s' hs'
      obtain rfl := hh hs'
      simpa using ha
  -- step 2: sum over the points of the event
  have hcard : (0 : ℝ) < Fintype.card (∀ i, α i) := by exact_mod_cast Fintype.card_pos
  simp_rw [← hpt, uprob_eq_card_filter, natCast_card_filter]
  simp_rw [← mul_div_assoc]
  rw [← sum_div]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  simp [ht]

end Representation

/-! ### Receiving slots and the certificates they carry -/

lemma ofFn_getElem_eq_map_of_eq {α β : Type*} (l : List α) (f : α → β) {n : ℕ}
    (hn : n = l.length) :
    List.ofFn (fun q : Fin n => f (l[q.1]'(hn ▸ q.2))) = l.map f := by
  subst hn
  exact List.ofFn_getElem_eq_map l f

namespace Config

variable {S : Type} (c : Config S)

/-- The ports of a configuration: pairs `(x, q)` with `q < deg x`. A port `(x, q)` is both the
slot where `x` receives a certificate from its neighbour at port `q` and the slot where `x` sends a
certificate on its port `q`. -/
abbrev Ports := Σ v : c.V, Fin (c.deg v)

/-- The neighbour of `x` at port `q`: the sender of the certificate received at slot `(x, q)`. -/
def sender (s : c.Ports) : c.V :=
  (c.nbrs s.1)[s.2.1]'(by rw [← c.deg_eq]; exact s.2.2)

lemma sender_mem (s : c.Ports) : c.sender s ∈ c.nbrs s.1 := List.getElem_mem _

lemma port_sender_lt (s : c.Ports) : c.port (c.sender s) s.1 < c.deg (c.sender s) := by
  rw [c.deg_eq, port, List.idxOf_lt_length_iff]
  exact c.symm _ _ (c.sender_mem s)

/-- The sending port feeding the receiving slot `s`: the port of the sender towards `s.1`. -/
def senderPort (s : c.Ports) : c.Ports :=
  ⟨c.sender s, ⟨c.port (c.sender s) s.1, c.port_sender_lt s⟩⟩

lemma senderPort_injective : Function.Injective c.senderPort := by
  rintro ⟨x, q⟩ ⟨x', q'⟩ h
  have hw : c.sender ⟨x, q⟩ = c.sender ⟨x', q'⟩ := congrArg Sigma.fst h
  have hp : c.port (c.sender ⟨x, q⟩) x = c.port (c.sender ⟨x', q'⟩) x' :=
    congrArg (fun p : c.Ports => (p.2 : ℕ)) h
  rw [← hw] at hp
  have hx : x = x' := by
    have h1 := c.symm _ _ (c.sender_mem ⟨x, q⟩)
    have h2 := c.symm _ _ (c.sender_mem ⟨x', q'⟩)
    rw [← hw] at h2
    exact (List.idxOf_inj h1).1 hp
  subst hx
  have : q = q' := by
    have := hw
    simp only [sender] at this
    exact Fin.ext ((c.nodup x).getElem_inj_iff.1 this)
  rw [this]

end Config

/-- Bit strings of length at most `κ`, as a finite type. -/
abbrev BStr (κ : ℕ) := {l : List Bool // l ∈ bitStrings κ}

lemma card_bStr_le (κ : ℕ) : Fintype.card (BStr κ) ≤ 2 ^ (κ + 1) := by
  rw [Fintype.card_coe]
  exact (card_bitStrings κ).trans (Nat.sub_le _ _)

namespace EIScheme

variable {S L : Type} (e : EIScheme S L)

/-- All certificates that the nodes of `c` with labels `ℓ` can send on their ports have at most
`κ` bits. -/
def CertLe (c : Config S) (ℓ : c.V → L) (κ : ℕ) : Prop :=
  ∀ v i, i < c.deg v → ∀ a, (e.cert (c.state v) (ℓ v) (c.deg v) i a).length ≤ κ

/-- The acceptance event, as a function of the vector `y` of received certificates indexed by
the receiving slots. It only depends on the states, the labels and the degrees. -/
def accEvent (c : Config S) (ℓ : c.V → L) {κ : ℕ} (y : c.Ports → BStr κ) : Prop :=
  ∀ x, e.dec (c.state x) (ℓ x) (List.ofFn fun q : Fin (c.deg x) => (y ⟨x, q⟩).1) = true

/-- The probability that node `w` sends the certificate `γ` on its port `p`. -/
noncomputable def certProb (c : Config S) (ℓ : c.V → L) (w : c.V) (p : ℕ) (γ : List Bool) : ℝ :=
  uprob fun a : e.Ω₀ (c.state w) (ℓ w) (c.deg w) => e.cert (c.state w) (ℓ w) (c.deg w) p a = γ

/-- The distribution of the certificate received at slot `s`. -/
noncomputable def slotDist (c : Config S) (ℓ : c.V → L) (κ : ℕ) (s : c.Ports) (γ : BStr κ) : ℝ :=
  e.certProb c ℓ (c.sender s) (c.port (c.sender s) s.1) γ.1

lemma certProb_nonneg (c : Config S) (ℓ : c.V → L) (w : c.V) (p : ℕ) (γ : List Bool) :
    0 ≤ e.certProb c ℓ w p γ := uprob_nonneg _

lemma certProb_le_one (c : Config S) (ℓ : c.V → L) (w : c.V) (p : ℕ) (γ : List Bool) :
    e.certProb c ℓ w p γ ≤ 1 := uprob_le_one _

lemma sum_slotDist {c : Config S} {ℓ : c.V → L} {κ : ℕ} (hκ : e.CertLe c ℓ κ) (s : c.Ports) :
    ∑ γ, e.slotDist c ℓ κ s γ = 1 := by
  set w := c.sender s
  set p := c.port w s.1
  have hp : p < c.deg w := c.port_sender_lt s
  let g : e.Ω₀ (c.state w) (ℓ w) (c.deg w) → BStr κ := fun a =>
    ⟨e.cert _ _ _ p a, mem_bitStrings (hκ w p hp a)⟩
  have : ∀ γ : BStr κ, e.slotDist c ℓ κ s γ = uprob fun a => g a = γ := fun γ => by
    simp only [slotDist, certProb, g, Subtype.ext_iff]; rfl
  simp_rw [this, uprob_eq_card_filter, ← sum_div]
  rw [div_eq_one_iff_eq (by exact_mod_cast Fintype.card_ne_zero)]
  exact_mod_cast (card_eq_sum_card_fiberwise (f := g) (t := univ) (fun _ _ => mem_univ _)).symm.trans
    (by simp)

/-- **Edge independence.** The acceptance probability is an expectation over a product
distribution of the received certificates: slot `s` independently receives a certificate with the
distribution of the certificates sent by `sender s` on its port towards `s.1`. -/
theorem accProb_eq_sum {c : Config S} {ℓ : c.V → L} {κ : ℕ} (hκ : e.CertLe c ℓ κ) :
    e.toRScheme.accProb c ℓ = ∑ y : c.Ports → BStr κ,
      (if e.accEvent c ℓ y then 1 else 0) * ∏ s, e.slotDist c ℓ κ s (y s) := by
  let α : c.Ports → Type := fun h => e.Ω₀ (c.state h.1) (ℓ h.1) (c.deg h.1)
  let g : ∀ s, α (c.senderPort s) → BStr κ := fun s a =>
    ⟨e.cert _ _ _ (c.port (c.sender s) s.1) a,
      mem_bitStrings (hκ _ _ (c.port_sender_lt s) a)⟩
  let f : (∀ h : c.Ports, α h) ≃ e.toRScheme.Coins c ℓ :=
    Equiv.piCurry (fun v (_ : Fin (c.deg v)) => e.Ω₀ (c.state v) (ℓ v) (c.deg v))
  have hacc : ∀ η, e.toRScheme.AcceptsAll c ℓ (f η) ↔
      e.accEvent c ℓ (fun s => g s (η (c.senderPort s))) := by
    intro η
    refine forall_congr' fun x => ?_
    change e.dec (c.state x) (ℓ x) (e.toRScheme.received c ℓ (f η) x) = true ↔ _
    rw [RScheme.received, ← ofFn_getElem_eq_map_of_eq _ _ (c.deg_eq x)]
    refine Iff.of_eq (congrArg (fun l => e.dec (c.state x) (ℓ x) l = true) ?_)
    refine congrArg List.ofFn (funext fun q => ?_)
    change e.toRScheme.cert _ _ _ (f η (c.sender ⟨x, q⟩)) (c.port (c.sender ⟨x, q⟩) x) = _
    simp only [EIScheme.toRScheme, dite_eq_left (c.port_sender_lt ⟨x, q⟩)]
    rfl
  rw [RScheme.accProb, ← uprob_comp_equiv_eq f]
  simp_rw [hacc]
  rw [uprob_comp_eq_sum (α := α) c.senderPort c.senderPort_injective g (e.accEvent c ℓ)]
  refine sum_congr rfl fun y _ => ?_
  congr 1
  refine prod_congr rfl fun s _ => ?_
  simp only [slotDist, certProb, g, Subtype.ext_iff]
  rfl

end EIScheme

/-! ### Crossing two copies: which slots change -/

namespace Copies

variable {S : Type} {c : Config S} {r : ℕ} (K : Copies c r)

lemma cross_sender {i j : Fin r} (hij : i ≠ j) (s : c.Ports) :
    (K.cross i j hij).sender s = K.newNbr i j s.1 (c.sender s) := by
  simp only [Config.sender, List.getElem_map]

/-- In the crossing, slot `s` receives the certificate that the new neighbour sends on the port
number that the old neighbour used. -/
lemma slotDist_cross {L : Type} (e : EIScheme S L) (ℓ : c.V → L) (κ : ℕ) {i j : Fin r}
    (hij : i ≠ j) (s : c.Ports) (γ : BStr κ) :
    e.slotDist (K.cross i j hij) ℓ κ s γ =
      e.certProb c ℓ (K.newNbr i j s.1 (c.sender s)) (c.port (c.sender s) s.1) γ.1 := by
  unfold EIScheme.slotDist
  rw [K.cross_sender hij, cross_port_newNbr hij (c.sender_mem s)]
  rfl

/-- Only the slots on the arcs of the two crossed copies change: at most `4 s` of them. -/
lemma card_arcSlots_le (i j : Fin r) :
    #(univ.filter fun s : c.Ports => K.IsArc i j s.1 (c.sender s)) ≤ 4 * K.s := by
  have hlt : ∀ (k : Fin r) (d : K.H.Dart),
      c.port (K.emb k d.snd) (K.emb k d.fst) < c.deg (K.emb k d.snd) := by
    intro k d
    rw [c.deg_eq, Config.port, List.idxOf_lt_length_iff]
    exact K.hom k d.snd d.fst d.adj.symm
  let f : Fin r × K.H.Dart → c.Ports := fun p =>
    ⟨K.emb p.1 p.2.snd, ⟨c.port (K.emb p.1 p.2.snd) (K.emb p.1 p.2.fst), hlt _ _⟩⟩
  have hsub : (univ.filter fun s : c.Ports => K.IsArc i j s.1 (c.sender s)) ⊆
      (({i, j} : Finset (Fin r)) ×ˢ (univ : Finset K.H.Dart)).image f := by
    rintro ⟨x, q⟩ hs
    obtain ⟨k, hk, a, b, hab, hx, hw⟩ := (mem_filter.1 hs).2
    refine mem_image.2 ⟨(k, ⟨(b, a), hab.symm⟩), mem_product.2 ⟨?_, mem_univ _⟩, ?_⟩
    · rcases hk with rfl | rfl <;> simp
    subst hx
    have hq : c.port (K.emb k a) (K.emb k b) = q := by
      rw [hw, Config.port, Config.sender]
      exact (c.nodup _).idxOf_getElem _ _
    simp only [f]
    congr 1
    exact Fin.ext hq
  calc _ ≤ #((({i, j} : Finset (Fin r)) ×ˢ (univ : Finset K.H.Dart)).image f) :=
        card_le_card hsub
    _ ≤ #(({i, j} : Finset (Fin r)) ×ˢ (univ : Finset K.H.Dart)) := card_image_le
    _ ≤ 2 * (2 * K.s) := by
        rw [card_product, card_univ, SimpleGraph.dart_card_eq_twice_card_edges]
        refine Nat.mul_le_mul (card_le_two) (le_of_eq ?_)
        unfold Copies.s
        congr 2
    _ = 4 * K.s := by ring

end Copies

/-! ### Proposition 4.6 and Theorem 4.7 -/

/-- If two numbers in `[0, ∞)` have the same rounding down to a multiple of `1 / m`, they differ
by at most `1 / m`. -/
lemma abs_sub_le_of_floor_mul_eq {x y : ℝ} {m : ℕ} (hm : 0 < m) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ⌊x * m⌋₊ = ⌊y * m⌋₊) : |x - y| ≤ 1 / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := Nat.floor_le (mul_nonneg hx hm'.le)
  have h2 := Nat.lt_floor_add_one (x * m)
  have h3 := Nat.floor_le (mul_nonneg hy hm'.le)
  have h4 := Nat.lt_floor_add_one (y * m)
  rw [h] at h1 h2
  rw [abs_sub_le_iff, le_div_iff₀ hm', le_div_iff₀ hm']
  constructor <;> nlinarith

/-- The number of copies beyond which two of them can be crossed without changing the acceptance
probability by `1/3`, for certificates of at most `κ` bits and a pattern with `s` edges. -/
def crossingBound (κ s : ℕ) : ℕ := (12 * s * 2 ^ (κ + 1) + 2) ^ (2 * s * 2 ^ (κ + 1))

variable {S L : Type}

/-- **Proposition 4.6 of [BFP15]** (quantitative form). Let `e` be an edge-independent randomized
verifier, `c` a configuration with labels `ℓ` such that every certificate sent on a port has at
most `κ` bits, and `K` a family of `r` pairwise independent, port-preserving copies of a pattern
with `s` edges. If `r > (12 s 2^(κ+1) + 2)^(2 s 2^(κ+1))`, then two copies `i ≠ j` can be crossed
so that the acceptance probability changes by less than `1/3`. (The paper assumes
`κ < (1/(2s) - o(1)) log log r`, which implies our hypothesis for large `r`.) -/
theorem prop_4_6 (e : EIScheme S L) (c : Config S) (ℓ : c.V → L) {r : ℕ} (K : Copies c r)
    (κ : ℕ) (hκ : ∀ v i, i < c.deg v → ∀ a, (e.cert (c.state v) (ℓ v) (c.deg v) i a).length ≤ κ)
    (hr : crossingBound κ K.s < r) :
    ∃ i j, ∃ hij : i ≠ j,
      |e.toRScheme.accProb c ℓ - e.toRScheme.accProb (K.cross i j hij) ℓ| < 1 / 3 := by
  set m : ℕ := 12 * K.s * 2 ^ (κ + 1) + 1 with hm
  have hm0 : 0 < m := Nat.succ_pos _
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  -- the `1/m`-rounded certificate distributions of the arcs of each copy
  let R : Fin r → K.H.Dart → BStr κ → Fin (m + 1) := fun k d γ =>
    ⟨⌊e.certProb c ℓ (K.emb k d.fst) (c.port (K.emb k d.fst) (K.emb k d.snd)) γ.1 * m⌋₊,
      Nat.lt_succ_of_le (Nat.floor_le_of_le (by
        have := e.certProb_le_one c ℓ (K.emb k d.fst)
          (c.port (K.emb k d.fst) (K.emb k d.snd)) γ.1
        nlinarith))⟩
  have hcard : Fintype.card (K.H.Dart → BStr κ → Fin (m + 1)) < Fintype.card (Fin r) := by
    rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
      SimpleGraph.dart_card_eq_twice_card_edges, ← pow_mul]
    refine lt_of_le_of_lt ?_ hr
    unfold crossingBound
    have : Fintype.card (BStr κ) * (2 * #K.H.edgeFinset) ≤ 2 * K.s * 2 ^ (κ + 1) := by
      rw [mul_comm]
      unfold Copies.s
      exact Nat.mul_le_mul (by convert le_refl _) (card_bStr_le κ)
    have hm1 : m + 1 = 12 * K.s * 2 ^ (κ + 1) + 2 := by omega
    rw [← hm1]
    exact Nat.pow_le_pow_right (Nat.succ_pos _) this
  -- pigeonhole: two copies with the same rounded distributions
  obtain ⟨i, j, hij, hR⟩ := Fintype.exists_ne_map_eq_of_card_lt R hcard
  refine ⟨i, j, hij, ?_⟩
  have hclose : ∀ (d : K.H.Dart) (γ : BStr κ),
      |e.certProb c ℓ (K.emb i d.fst) (c.port (K.emb i d.fst) (K.emb i d.snd)) γ.1 -
        e.certProb c ℓ (K.emb j d.fst) (c.port (K.emb j d.fst) (K.emb j d.snd)) γ.1| ≤ 1 / m :=
    fun d γ => abs_sub_le_of_floor_mul_eq hm0 (e.certProb_nonneg _ _ _ _ _)
      (e.certProb_nonneg _ _ _ _ _) (congrArg Fin.val (congrFun (congrFun hR d) γ))
  -- per-slot distances
  have hκ' : e.CertLe c ℓ κ := hκ
  have hκ'' : e.CertLe (K.cross i j hij) ℓ κ := hκ
  have hslot : ∀ s : c.Ports, ∑ γ, |e.slotDist c ℓ κ s γ - e.slotDist (K.cross i j hij) ℓ κ s γ| ≤
      if K.IsArc i j s.1 (c.sender s) then (Fintype.card (BStr κ) : ℝ) * (1 / (m : ℝ)) else 0 := by
    intro s
    simp_rw [K.slotDist_cross e ℓ κ hij s]
    split_ifs with ha
    · refine (sum_le_sum (g := fun _ => (1 / (m : ℝ))) fun γ _ => ?_).trans
        (by rw [sum_const, card_univ, nsmul_eq_mul])
      obtain ⟨a, b, hab, H⟩ := K.isArc_cases hij ha
      rcases H with ⟨hx, hw, hn⟩ | ⟨hx, hw, hn⟩ <;> rw [hn] <;>
        simp only [EIScheme.slotDist] <;> rw [← hw, ← hx]
      · have := hclose ⟨(b, a), hab.symm⟩ γ
        dsimp only at this
        rwa [← K.port_eq i j b a hab.symm] at this
      · have := hclose ⟨(b, a), hab.symm⟩ γ
        dsimp only at this
        rwa [K.port_eq i j b a hab.symm, abs_sub_comm] at this
    · rw [K.newNbr_of_not_isArc ha]
      simp [EIScheme.slotDist]
  have hsum : ∑ s : c.Ports, ∑ γ, |e.slotDist c ℓ κ s γ - e.slotDist (K.cross i j hij) ℓ κ s γ| ≤
      (4 * K.s : ℕ) * (2 ^ (κ + 1) * (1 / m)) := by
    refine (sum_le_sum fun s _ => hslot s).trans ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    gcongr
    · exact_mod_cast K.card_arcSlots_le i j
    · exact_mod_cast card_bStr_le κ
  have hg : ∀ y : c.Ports → BStr κ, |(if e.accEvent c ℓ y then (1 : ℝ) else 0)| ≤ 1 :=
    fun y => by split_ifs <;> simp
  have h0 : ∀ s γ, 0 ≤ e.slotDist c ℓ κ s γ := fun s γ => uprob_nonneg _
  have h0' : ∀ s γ, 0 ≤ e.slotDist (K.cross i j hij) ℓ κ s γ := fun s γ => uprob_nonneg _
  have h1 : ∀ s, ∑ γ, e.slotDist c ℓ κ s γ = 1 := e.sum_slotDist hκ'
  have h1' : ∀ s, ∑ γ, e.slotDist (K.cross i j hij) ℓ κ s γ = 1 := e.sum_slotDist hκ''
  have hmain := abs_sum_mul_prod_sub_le (e.slotDist c ℓ κ) (e.slotDist (K.cross i j hij) ℓ κ)
    h0 h1 h0' h1' _ hg
  rw [e.accProb_eq_sum hκ', e.accProb_eq_sum hκ'']
  refine lt_of_le_of_lt (hmain.trans hsum) ?_
  have hT : (0 : ℝ) ≤ K.s * 2 ^ (κ + 1) := by positivity
  rw [hm]
  push_cast
  rw [mul_one_div, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- Certificate bound of an RPLS on legal configurations, restated for the edge-independent
certificate function. -/
lemma EIScheme.certLe_of_certBound {e : EIScheme S L} {prover : ∀ c : Config S, c.V → L}
    {F P : Config S → Prop} {κ : Config S → ℕ} (hκ : CertBound e.toRScheme prover F P κ)
    {c : Config S} (hF : F c) (hP : P c) : e.CertLe c (prover c) (κ c) := by
  intro v i hi a
  have := hκ c hF hP v (fun _ => a) i hi
  simpa [EIScheme.toRScheme, hi] using this

/-- **Theorem 4.7 of [BFP15]** (quantitative form, for configurations `c` with `P c`). Let
`(e, prover)` be a two-sided edge-independent RPLS for `(F, P)` with verification complexity `κ`.
If a legal configuration `c ∈ F` contains `r` pairwise independent port-preserving copies of a
pattern with `s` edges such that every crossing of two copies is in `F` and illegal, then
`r ≤ (12 s 2^(κ c + 1) + 2)^(2 s 2^(κ c + 1))`. -/
theorem thm_4_7_correct {e : EIScheme S L} {prover : ∀ c : Config S, c.V → L}
    {F P : Config S → Prop} {κ : Config S → ℕ} (hσ : IsTwoSided e.toRScheme prover F P)
    (hκ : CertBound e.toRScheme prover F P κ) {c : Config S} (hF : F c) (hP : P c) {r : ℕ}
    (K : Copies c r)
    (hcross : ∀ i j (hij : i ≠ j), Refuted F P (K.cross i j hij)) :
    r ≤ crossingBound (κ c) K.s := by
  by_contra h
  push Not at h
  obtain ⟨i, j, hij, hlt⟩ :=
    prop_4_6 e c (prover c) K (κ c) (EIScheme.certLe_of_certBound hκ hF hP) h
  have h1 := hσ.1 c hF hP
  have h2 : 2 / 3 ≤ 1 - e.toRScheme.accProb (K.cross i j hij) (prover c) := by
    rcases hcross i j hij with ⟨hF', hP'⟩ | ⟨U, hU, hF', hP'⟩
    · exact hσ.2 _ hF' hP' (prover c)
    · have := hσ.2 _ hF' hP' (fun v => prover c v.1)
      have := e.toRScheme.accProb_le_restrict hU (prover c)
      linarith
  rw [abs_sub_lt_iff] at hlt
  linarith [hlt.1, hlt.2]

lemma twelve_mul_add_two_le_sixteen_pow {T : ℕ} (hT : 1 ≤ T) : 12 * T + 2 ≤ 16 ^ T := by
  induction T, hT using Nat.le_induction with
  | base => norm_num
  | succ T hT ih =>
    rw [pow_succ]
    have : 1 ≤ 16 ^ T := Nat.one_le_pow _ _ (by norm_num)
    omega

/-- A doubly exponential form of the bound: `crossingBound κ s ≤ 2 ^ (2 ^ (2κ + 5) s²)`. -/
lemma crossingBound_le (κ s : ℕ) : crossingBound κ s ≤ 2 ^ (2 ^ (2 * κ + 5) * s ^ 2) := by
  set T := s * 2 ^ (κ + 1) with hTdef
  have e1 : crossingBound κ s = (12 * T + 2) ^ (2 * T) := by
    unfold crossingBound; rw [hTdef]; ring_nf
  have e2 : 2 ^ (2 * κ + 5) * s ^ 2 = 4 * T * (2 * T) := by
    rw [hTdef]; ring
  rw [e1, e2]
  rcases Nat.eq_zero_or_pos T with h0 | hpos
  · simp [h0]
  calc (12 * T + 2) ^ (2 * T) ≤ (16 ^ T) ^ (2 * T) :=
        Nat.pow_le_pow_left (twelve_mul_add_two_le_sixteen_pow hpos) _
    _ = 2 ^ (4 * T * (2 * T)) := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul]
        congr 1
        ring

/-- **Theorem 4.7 of [BFP15]**, asymptotic form: the verification complexity satisfies
`κ ≥ (log log r) / 2 - log s - 5/2` (logarithms in base 2), i.e. `Ω(log log r)` for patterns
of bounded size. -/
theorem thm_4_7_loglog {e : EIScheme S L} {prover : ∀ c : Config S, c.V → L}
    {F P : Config S → Prop} {κ : Config S → ℕ} (hσ : IsTwoSided e.toRScheme prover F P)
    (hκ : CertBound e.toRScheme prover F P κ) {c : Config S} (hF : F c) (hP : P c) {r : ℕ}
    (hr : 2 ≤ r) (K : Copies c r)
    (hcross : ∀ i j (hij : i ≠ j), Refuted F P (K.cross i j hij)) :
    Real.logb 2 (Real.logb 2 r) ≤ 2 * κ c + 5 + 2 * Real.logb 2 K.s := by
  have hb := (thm_4_7_correct hσ hκ hF hP K hcross).trans (crossingBound_le (κ c) K.s)
  have hs : 0 < K.s := by
    rcases Nat.eq_zero_or_pos K.s with h0 | h0
    · rw [h0] at hb; simp at hb; omega
    · exact h0
  set M : ℕ := 2 ^ (2 * κ c + 5) * K.s ^ 2 with hM
  have h1 : (r : ℝ) ≤ (2 : ℝ) ^ M := by exact_mod_cast hb
  have hrR : (1 : ℝ) < r := by exact_mod_cast hr
  have hlog : Real.logb 2 r ≤ M := by
    calc Real.logb 2 r ≤ Real.logb 2 ((2 : ℝ) ^ M) :=
          Real.logb_le_logb_of_le (by norm_num) (by linarith) h1
      _ = M := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  have hpos : 0 < Real.logb 2 r := Real.logb_pos (by norm_num) hrR
  calc Real.logb 2 (Real.logb 2 r) ≤ Real.logb 2 (M : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num) hpos hlog
    _ = 2 * κ c + 5 + 2 * Real.logb 2 K.s := by
        have hsR : (0 : ℝ) < K.s := by exact_mod_cast hs
        rw [hM]
        push_cast
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
          Real.logb_self_eq_one (by norm_num)]
        push_cast
        ring

end Podc.RandomizedPLS
