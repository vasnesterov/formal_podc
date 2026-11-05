import Papers.PODC2014.DistributedUniversality.InvBStep3

/-!
# Invocations, returns and linearization points (Lemmas 1 and 4)

`InvC`: every operation present anywhere in the system has been invoked (`invAt`, Lemma 1), and the
ghost linearization points `lin` (the first write of a `GSTATE` register containing the operation,
as in Lemma 4) lie between invocation and return and respect the order of the global sequence `G`.
-/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}

theorem mem_merge {cands : Fin n → List (Op n)} {h : List (Op n)} {x : Op n}
    (hx : x ∈ merge cands h) : x ∈ h ∨ ∃ q, x ∈ cands q := by
  unfold merge at hx
  suffices H : ∀ (qs : List (Fin n)) (acc : List (Op n)),
      x ∈ qs.foldl (fun acc q => if acc.isPrefixOf (cands q) then cands q else acc) acc →
      x ∈ acc ∨ ∃ q, x ∈ cands q by
    exact H _ _ hx
  intro qs
  induction qs with
  | nil => intro acc hacc; exact Or.inl hacc
  | cons q qs ih =>
    intro acc hacc
    simp only [List.foldl_cons] at hacc
    rcases ih _ hacc with h1 | h1
    · split_ifs at h1
      · exact Or.inr ⟨q, h1⟩
      · exact Or.inl h1
    · exact Or.inr h1

/-- Operation `o` on object `m` has been invoked. -/
def IV (s : St n k) (m : Fin k) (o : Op n) : Prop := ∃ t, s.invAt o.1 m o.2 = some t

/-- Invocation and linearization invariant. -/
structure InvC (M : Mode) (s : St n k) : Prop where
  time_inv : ∀ i m c t, s.invAt i m c = some t → t < s.time
  inv_cnt : ∀ i m c t, s.invAt i m c = some t → c ≤ (s.loc i).cnt m
  inv_init : ∀ i m c, (s.loc i).pc = .init → s.invAt i m c = none
  v_lastOp : ∀ j m c, s.lastOp j m = some c → IV s m (j, c)
  v_loc : ∀ i m, (s.loc i).pc ≠ .init → IV s m ((s.loc i).oper m) ∧ IV s m (i, (s.loc i).cnt m)
  v_acI : ∀ r b y j w, s.acI r b y j = some w → IV s y w
  v_scI : ∀ r j u y, s.scI r j = some u → IV s y (u y)
  v_opRec : ∀ r m j w, s.opRec r m j = some w → IV s m w
  v_hist : ∀ i m o, o ∈ (s.loc i).hist m → IV s m o
  v_G : ∀ m o, o ∈ s.G m → IV s m o
  lin_gst : ∀ q m o, o ∈ s.gst q m → ∃ t, s.lin m o = some t
  lin_inv : ∀ m o t, s.lin m o = some t → t < s.time ∧ ∃ ti, s.invAt o.1 m o.2 = some ti ∧ ti ≤ t
  lin_pre : ∀ m o t, s.lin m o = some t → ∃ h, h <+: s.G m ∧ o ∈ h ∧
    ∀ o' ∈ h, ∃ t', s.lin m o' = some t' ∧ t' ≤ t
  res_hist : ∀ i m c, (m, c) ∈ (s.loc i).res → (i, c) ∈ (s.loc i).hist m ∧
    ∃ h, s.retH i m c = some h
  ret_lin : ∀ i m c t, s.retAt i m c = some t → ∃ tl, s.lin m (i, c) = some tl ∧ tl ≤ t
  ret_H : ∀ i m c h, s.retH i m c = some h → h <+: s.G m ∧ (i, c) ∈ h

theorem invC_init (M : Mode) : InvC M (init : St n k) := by
  constructor <;> simp [init, initLoc, IV]

end Podc.DistributedUniversality
