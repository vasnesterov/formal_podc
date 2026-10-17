import Papers.PODC2013.CongestedCliqueRouting.Model

/-!
# Knowledge-based construction of algorithms

Instead of writing the local algorithm of every node directly, we describe the *intended run*
`S d t u v` (the packet from `u` to `v` in round `t` on instance `d`) by global formulas, and show
that it is *local*: what node `v` sends in round `t` is determined by its own input and the packets
it has received before round `t` (`IsLocal`). A local intended run is the run of a deterministic
full-information algorithm (`synth`, `synth_sent`).
-/

namespace CongestedCliqueRouting

open Finset

/-- An intended run: `S d t u v` is the packet from `u` to `v` in round `t` on instance `d`. -/
abbrev Run (I V M : Type*) (B : ℕ) := I → ℕ → V → V → Packet M B

section Knowledge

variable {I V K M : Type*} {B : ℕ}

/-- Node `v` cannot distinguish instances `d` and `d'` at the beginning of round `t`. -/
def SameView (inp : I → V → K) (S : Run I V M B) (d d' : I) (t : ℕ) (v : V) : Prop :=
  inp d v = inp d' v ∧ ∀ r < t, ∀ u, S d r u v = S d' r u v

/-- `g` is known to `v` at the beginning of round `t`. -/
def Determined (inp : I → V → K) (S : Run I V M B) (t : ℕ) (v : V) {α : Sort*}
    (g : I → α) : Prop :=
  ∀ d d', SameView inp S d d' t v → g d = g d'

/-- The intended run is implementable: every packet is determined by the sender's view. -/
def IsLocal (inp : I → V → K) (S : Run I V M B) : Prop :=
  ∀ t v, Determined inp S t v (fun d => S d t v)

variable {inp : I → V → K} {S : Run I V M B}

lemma Determined.mono {t t' : ℕ} {v : V} {α : Sort*} {g : I → α}
    (h : Determined inp S t v g) (ht : t ≤ t') : Determined inp S t' v g :=
  fun d d' hv => h d d' ⟨hv.1, fun r hr u => hv.2 r (lt_of_lt_of_le hr ht) u⟩

lemma Determined.map {t : ℕ} {v : V} {α β : Sort*} {g : I → α}
    (h : Determined inp S t v g) (f : α → β) : Determined inp S t v (fun d => f (g d)) :=
  fun d d' hv => by simp only [h d d' hv]

lemma Determined.pair {t : ℕ} {v : V} {α β : Type*} {g₁ : I → α} {g₂ : I → β}
    (h₁ : Determined inp S t v g₁) (h₂ : Determined inp S t v g₂) :
    Determined inp S t v (fun d => (g₁ d, g₂ d)) :=
  fun d d' hv => by simp only [h₁ d d' hv, h₂ d d' hv]

lemma Determined.pi {t : ℕ} {v : V} {ι : Type*} {α : ι → Type*} {g : I → (i : ι) → α i}
    (h : ∀ i, Determined inp S t v (fun d => g d i)) : Determined inp S t v g :=
  fun d d' hv => funext fun i => h i d d' hv

lemma Determined.congr {t : ℕ} {v : V} {α : Sort*} {g g' : I → α}
    (h : Determined inp S t v g) (heq : ∀ d, g' d = g d) : Determined inp S t v g' :=
  fun d d' hv => by rw [heq, heq, h d d' hv]

lemma determined_inp (t : ℕ) (v : V) : Determined inp S t v (fun d => inp d v) :=
  fun _ _ hv => hv.1

lemma determined_const (t : ℕ) (v : V) {α : Sort*} (c : α) :
    Determined inp S t v (fun _ => c) :=
  fun _ _ _ => rfl

lemma determined_recv {t r : ℕ} (hr : r < t) (v : V) :
    Determined inp S t v (fun d => fun u => S d r u v) :=
  fun _ _ hv => funext fun u => hv.2 r hr u

open Classical in
/-- The full-information algorithm that follows a local intended run. -/
noncomputable def synth (inp : I → V → K) (S : Run I V M B) : Algorithm V K M B :=
  fun t v k h =>
    if hd : ∃ d, inp d v = k ∧ h = (List.range t).map (fun r u => S d r u v) then
      S (Classical.choose hd) t v
    else fun _ _ => none

lemma synth_hist (hS : IsLocal inp S) (d : I) :
    ∀ t v, (synth inp S).hist (inp d) t v = (List.range t).map (fun r u => S d r u v) := by
  intro t
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    simp only [Algorithm.hist, ih, List.range_succ, List.map_append, List.map_cons,
      List.map_nil]
    congr 2
    funext u
    have hd : ∃ d', inp d' u = inp d u ∧
        (List.range t).map (fun r u' => S d r u' u) =
          (List.range t).map (fun r u' => S d' r u' u) := ⟨d, rfl, rfl⟩
    simp only [synth]
    simp only [hd, ↓reduceDIte]
    obtain ⟨h1, h2⟩ := Classical.choose_spec hd
    have hsame : SameView inp S (Classical.choose hd) d t u := by
      refine ⟨h1, fun r hr u' => ?_⟩
      have := congrArg (fun l => l[r]?) h2
      simp only [List.getElem?_map, List.getElem?_range hr, Option.map_some,
        Option.some.injEq] at this
      exact (congrFun this u').symm
    exact congrFun (hS t u _ _ hsame) v

/-- The synthesized algorithm realizes the intended run. -/
theorem synth_sent (hS : IsLocal inp S) (d : I) (t : ℕ) (u v : V) :
    (synth inp S).sent (inp d) t u v = S d t u v := by
  simp only [Algorithm.sent, synth_hist hS]
  have hd : ∃ d', inp d' u = inp d u ∧
      (List.range t).map (fun r u' => S d r u' u) =
        (List.range t).map (fun r u' => S d' r u' u) := ⟨d, rfl, rfl⟩
  simp only [synth]
  simp only [hd, ↓reduceDIte]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hd
  have hsame : SameView inp S (Classical.choose hd) d t u := by
    refine ⟨h1, fun r hr u' => ?_⟩
    have := congrArg (fun l => l[r]?) h2
    simp only [List.getElem?_map, List.getElem?_range hr, Option.map_some,
      Option.some.injEq] at this
    exact (congrFun this u').symm
  exact congrFun (hS t u _ _ hsame) v

end Knowledge

/-! ## Messages in packets, holding, and the routing specification -/

section Routing

variable {I V M : Type*} {B : ℕ} [Fintype V] [DecidableEq M]

/-- The routed messages contained in a packet. -/
def msgsOf (p : Packet M B) : Finset M :=
  univ.biUnion fun i => match p i with
    | some (Item.msg m) => {m}
    | _ => ∅

lemma mem_msgsOf {p : Packet M B} {m : M} : m ∈ msgsOf p ↔ ∃ i, p i = some (Item.msg m) := by
  simp only [msgsOf, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rcases h : p i with _ | ⟨m' | k⟩ <;> simp_all
  · rintro ⟨i, hi⟩
    exact ⟨i, by simp [hi]⟩

/-- Messages received by `v` in round `r`. -/
def received (S : Run I V M B) (d : I) (r : ℕ) (v : V) : Finset M :=
  univ.biUnion fun u => msgsOf (S d r u v)

lemma mem_received {S : Run I V M B} {d : I} {r : ℕ} {v : V} {m : M} :
    m ∈ received S d r v ↔ ∃ u i, S d r u v i = some (Item.msg m) := by
  simp [received, mem_msgsOf]

lemma card_received_le {S : Run I V M B} {d : I} {r : ℕ} {v : V}
    (h : ∀ u, (msgsOf (S d r u v)).card ≤ 1) : (received S d r v).card ≤ Fintype.card V := by
  calc (received S d r v).card ≤ ∑ u, (msgsOf (S d r u v)).card := card_biUnion_le
    _ ≤ ∑ _u : V, 1 := sum_le_sum fun u _ => h u
    _ = Fintype.card V := by simp

lemma determined_received {K : Type*} {inp : I → V → K} {S : Run I V M B} {t r : ℕ}
    (hr : r < t) (v : V) : Determined inp S t v (fun d => received S d r v) :=
  ((determined_recv hr v).map fun f => univ.biUnion fun u => msgsOf (f u))

/-- Node `v` holds message `m` at the beginning of round `t` of the intended run. -/
def HoldsS (msgs : I → V → Finset M) (S : Run I V M B) (d : I) (t : ℕ) (v : V) (m : M) :
    Prop :=
  m ∈ msgs d v ∨ ∃ r < t, ∃ u i, S d r u v i = some (Item.msg m)

omit [Fintype V] [DecidableEq M] in
lemma HoldsS.mono {msgs : I → V → Finset M} {S : Run I V M B} {d : I} {t t' : ℕ} {v : V}
    {m : M} (h : HoldsS msgs S d t v m) (ht : t ≤ t') : HoldsS msgs S d t' v m := by
  rcases h with h | ⟨r, hr, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨r, lt_of_lt_of_le hr ht, h⟩

lemma holdsS_of_mem_received {msgs : I → V → Finset M} {S : Run I V M B} {d : I} {r t : ℕ}
    {v : V} {m : M} (h : m ∈ received S d r v) (hr : r < t) : HoldsS msgs S d t v m :=
  Or.inr ⟨r, hr, mem_received.1 h⟩

/-- Specification of a routing algorithm given as an intended run: within `T` rounds, numbers
are at most `C`, only held messages are sent, and every message reaches its destination. -/
structure Routes (msgs : I → V → Finset M) (dst : I → M → V) (S : Run I V M B) (T C : ℕ) :
    Prop where
  num_le : ∀ d, ∀ t < T, ∀ u v i k, S d t u v i = some (Item.num k) → k ≤ C
  valid : ∀ d, ∀ t < T, ∀ u v i m, S d t u v i = some (Item.msg m) → HoldsS msgs S d t u m
  deliver : ∀ d v, ∀ m ∈ msgs d v, HoldsS msgs S d T (dst d m) m

end Routing

end CongestedCliqueRouting
