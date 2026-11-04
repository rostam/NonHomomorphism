import NonHom.LineExact

/-!
# Triangular graphs into `K_r`

* **Lower bound with parity.** For odd `n` with `n - 1 = q·r` and `q` odd,
  `|L(K_n), K_r| ≥ n·r·C(q,2) + r/2`, which exceeds the Turán bound `n·(C(n-1,2) - t(n-1,r))`
  by `r/2`.
* **Even `n`.** A 1-factorization of `K_n` makes the Turán bound exact for every target:
  `|L(K_n), H| = n·(C(n-1,2) - t(n-1,ω(H)))`.
-/

open SimpleGraph Finset

namespace NonHom

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Number of edges of colour `i` at `v`. -/
def dcol {r : ℕ} (c : G.edgeSet → Fin r) (v : V) (i : Fin r) : ℕ :=
  (univ.filter fun e : At G v => c e.1 = i).card

theorem sum_dcol {r : ℕ} {d : ℕ} (hreg : G.IsRegularOfDegree d) (c : G.edgeSet → Fin r) (v : V) :
    ∑ i, dcol c v i = d := by
  classical
  have := card_eq_sum_card_fiberwise (f := fun e : At G v => c e.1) (s := univ) (t := univ)
    (fun _ _ => mem_univ _)
  rw [card_univ, card_At hreg] at this
  rw [this]; rfl

/-- Ordered pairs with different colours. -/
theorem card_diff_pairs_r {T : Type*} [Fintype T] [DecidableEq T] {r : ℕ} (c : T → Fin r) :
    (univ.filter fun p : T × T => c p.1 ≠ c p.2).card =
      ∑ i, (univ.filter fun x => c x = i).card * (Fintype.card T - (univ.filter fun x => c x = i).card) := by
  classical
  rw [card_filter, Fintype.sum_prod_type]
  have h : ∀ x : T, (∑ y : T, if c x ≠ c y then 1 else 0) =
      Fintype.card T - (univ.filter fun y => c y = c x).card := by
    intro x
    have := card_filter_add_card_filter_not (s := (univ : Finset T)) (fun y => c y = c x)
    rw [card_univ] at this
    rw [← card_filter]
    have e : (univ.filter fun y => c x ≠ c y) = univ.filter fun y => ¬ c y = c x := by
      ext y; simp [eq_comm]
    rw [e]; omega
  rw [sum_congr rfl fun x _ => h x]
  rw [← Finset.sum_fiberwise univ c (fun x => Fintype.card T - (univ.filter fun y => c y = c x).card)]
  apply sum_congr rfl; intro i _
  rw [sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2]), sum_const, smul_eq_mul]

/-- Monochromatic pairs at `v` number `∑_i C(d_i, 2)`. -/
theorem card_mono_r {d r : ℕ} (hreg : G.IsRegularOfDegree d) (c : G.edgeSet → Fin r) (v : V)
    [Fintype ((⊤ : SimpleGraph (At G v)) \ (⊤ : SimpleGraph (Fin r)).comap (fun e => c e.1)).edgeSet] :
    ((⊤ : SimpleGraph (At G v)) \ (⊤ : SimpleGraph (Fin r)).comap (fun e => c e.1)).edgeFinset.card =
      ∑ i, (dcol c v i).choose 2 := by
  classical
  let Dv : SimpleGraph (At G v) := (⊤ : SimpleGraph (Fin r)).comap (fun e => c e.1)
  have hD : 2 * Dv.edgeFinset.card = ∑ i, dcol c v i * (d - dcol c v i) := by
    rw [two_mul_card_edgeFinset]
    have := card_diff_pairs_r (fun e : At G v => c e.1)
    rw [card_At hreg] at this
    have e : (univ.filter fun p : At G v × At G v => Dv.Adj p.1 p.2) =
        univ.filter fun p : At G v × At G v => c p.1.1 ≠ c p.2.1 := by
      ext p; simp [Dv]
    rw [e, this]; rfl
  have hsd : ((⊤ : SimpleGraph (At G v)) \ Dv).edgeFinset =
      (⊤ : SimpleGraph (At G v)).edgeFinset \ Dv.edgeFinset := by
    ext z
    rw [mem_edgeFinset, mem_sdiff, mem_edgeFinset, mem_edgeFinset]
    simp only [edgeSet_sdiff, Set.mem_diff]
  have hle : Dv.edgeFinset.card ≤ (⊤ : SimpleGraph (At G v)).edgeFinset.card :=
    card_le_card (edgeFinset_mono le_top)
  show (((⊤ : SimpleGraph (At G v)) \ Dv).edgeFinset).card = _
  rw [hsd, card_sdiff_of_subset (edgeFinset_mono le_top)]
  rw [card_edgeFinset_top_eq_card_choose_two, card_At hreg] at hle ⊢
  have hsum := sum_dcol hreg c v
  -- `2 C(d,2) - ∑ d_i (d - d_i) = 2 ∑ C(d_i,2)`
  have key : 2 * d.choose 2 = ∑ i, dcol c v i * (d - dcol c v i) + 2 * ∑ i, (dcol c v i).choose 2 := by
    have hz : (2 * d.choose 2 : ℤ) = ∑ i, ((dcol c v i : ℤ) * (d - dcol c v i)) +
        2 * ∑ i, ((dcol c v i).choose 2 : ℤ) := by
      have h2 : ∀ x : ℕ, (2 * x.choose 2 : ℤ) = x * (x - 1) := by
        intro x
        have hn : 2 * x.choose 2 = x * (x - 1) := by
          rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self x).two_dvd
        rcases Nat.eq_zero_or_pos x with rfl | hx
        · simp
        · have : ((2 * x.choose 2 : ℕ) : ℤ) = ((x * (x - 1) : ℕ) : ℤ) := by rw [hn]
          push_cast [Nat.cast_sub hx] at this; linarith
      rw [h2, mul_sum, sum_congr rfl (fun i _ => h2 (dcol c v i)), ← sum_add_distrib]
      have hs : (∑ i, (dcol c v i : ℤ)) = d := by exact_mod_cast hsum
      have : ∑ i, ((dcol c v i : ℤ) * (d - dcol c v i) + dcol c v i * (dcol c v i - 1)) =
          (d : ℤ) * ∑ i, (dcol c v i : ℤ) - ∑ i, (dcol c v i : ℤ) := by
        rw [mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro i _; ring
      rw [this, hs]; ring
    have hle' : ∀ i, dcol c v i ≤ d := fun i => by
      rw [← hsum]; exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    have : (∑ i, (dcol c v i * (d - dcol c v i) : ℕ) : ℤ) = ∑ i, ((dcol c v i : ℤ) * (d - dcol c v i)) := by
      push_cast; apply sum_congr rfl; intro i _; rw [Nat.cast_sub (hle' i)]
    have hz' : ((2 * d.choose 2 : ℕ) : ℤ) =
        ((∑ i, dcol c v i * (d - dcol c v i) + 2 * ∑ i, (dcol c v i).choose 2 : ℕ) : ℤ) := by
      push_cast; rw [← this] at hz; push_cast at hz ⊢; linarith
    exact_mod_cast hz'
  omega

/-- **Lower bound** from any map to `K_r`: all monochromatic pairs must be deleted. -/
theorem line_lower_r {d r : ℕ} (hreg : G.IsRegularOfDegree d) (S : Finset (Sym2 G.edgeSet))
    (g : G.lineGraph.deleteEdges ↑S →g (⊤ : SimpleGraph (Fin r))) :
    ∑ v, ∑ i, (dcol (fun e => g e) v i).choose 2 ≤ S.card := by
  classical
  let c : G.edgeSet → Fin r := fun e => g e
  let Mv : ∀ v, SimpleGraph (At G v) := fun v =>
    (⊤ : SimpleGraph (At G v)) \ (⊤ : SimpleGraph (Fin r)).comap (fun e => c e.1)
  let ι : ∀ v, Sym2 (At G v) → Sym2 G.edgeSet := fun v => Sym2.map Subtype.val
  have hsub : ∀ v, (Mv v).edgeFinset.image (ι v) ⊆ S := by
    intro v z hz
    obtain ⟨z, hzM, rfl⟩ := mem_image.mp hz
    rw [mem_edgeFinset] at hzM
    induction z using Sym2.ind with
    | _ a b =>
      obtain ⟨hab, hcol⟩ := hzM
      have hab' : a ≠ b := hab
      have hcab : c a.1 = c b.1 := by by_contra h; exact hcol h
      by_contra hS
      have hadj : (G.lineGraph.deleteEdges ↑S).Adj a.1 b.1 := by
        rw [deleteEdges_adj, lineGraph_adj_iff_exists]
        exact ⟨⟨fun h => hab' (Subtype.ext h), v, a.2, b.2⟩, hS⟩
      exact g.map_rel hadj hcab
  have hdisj : ∀ v ∈ (univ : Finset V), ∀ w ∈ (univ : Finset V), v ≠ w →
      Disjoint ((Mv v).edgeFinset.image (ι v)) ((Mv w).edgeFinset.image (ι w)) := by
    intro v _ w _ hvw
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨z₁, hz₁, rfl⟩ := mem_image.mp hz
    obtain ⟨z₂, -, hz₂⟩ := mem_image.mp hz'
    rw [mem_edgeFinset] at hz₁
    induction z₁ using Sym2.ind with
    | _ a b =>
      induction z₂ using Sym2.ind with
      | _ a' b' =>
        have hab : a ≠ b := hz₁.1
        simp only [ι, Sym2.map_mk, Sym2.eq_iff] at hz₂
        have hw : w ∈ (a.1 : Sym2 V) ∧ w ∈ (b.1 : Sym2 V) := by
          rcases hz₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨h1 ▸ a'.2, h2 ▸ b'.2⟩
          · exact ⟨h2 ▸ b'.2, h1 ▸ a'.2⟩
        have e1 := (Sym2.mem_and_mem_iff hvw).mp ⟨a.2, hw.1⟩
        have e2 := (Sym2.mem_and_mem_iff hvw).mp ⟨b.2, hw.2⟩
        exact hab (Subtype.ext (Subtype.ext (e1.trans e2.symm)))
  have hcard := card_le_card (biUnion_subset.mpr fun v _ => hsub v :
    (univ.biUnion fun v => (Mv v).edgeFinset.image (ι v)) ⊆ S)
  rw [card_biUnion hdisj] at hcard
  refine le_trans ?_ hcard
  apply sum_le_sum
  intro v _
  rw [card_image_of_injective _ (Sym2.map.injective Subtype.val_injective), card_mono_r hreg c v]

/-- Handshake within one colour class: `∑_v d_i(v)` is even. -/
theorem sum_dcol_even {r : ℕ} (c : G.edgeSet → Fin r) (i : Fin r) : (∑ v, dcol c v i) % 2 = 0 := by
  classical
  have h : ∀ v, dcol c v i = (univ.filter fun e : G.edgeSet => v ∈ (e : Sym2 V) ∧ c e = i).card := by
    intro v
    unfold dcol
    apply card_bij (fun e _ => e.1)
    · intro e he; simp only [mem_filter, mem_univ, true_and] at he ⊢; exact ⟨e.2, he⟩
    · intro e₁ _ e₂ _ h; exact Subtype.ext h
    · intro e he
      simp only [mem_filter, mem_univ, true_and] at he
      exact ⟨⟨e, he.1⟩, by simpa using he.2, rfl⟩
  simp only [h, card_filter]
  rw [sum_comm]
  have h2 : ∀ e : G.edgeSet, (∑ v, if v ∈ (e : Sym2 V) ∧ c e = i then 1 else 0) =
      2 * (if c e = i then 1 else 0) := by
    intro e
    obtain ⟨e, he⟩ := e
    induction e using Sym2.ind with
    | _ u w =>
      have huw : u ≠ w := he.ne
      by_cases hc : c ⟨s(u, w), he⟩ = i
      · simp only [hc, and_true, if_true, mul_one]
        rw [← card_filter]
        have : (univ.filter fun v => v ∈ s(u, w)) = {u, w} := by ext v; simp
        rw [this, card_pair huw]
      · simp [hc]
  rw [sum_congr rfl (fun e _ => h2 e), ← mul_sum]
  omega

/-- `2·∑ C(d_i,2) = 2r·C(q,2) + ∑ (d_i - q)²` when `∑ d_i = r q`. -/
theorem two_sum_choose {r q : ℕ} (d : Fin r → ℕ) (hs : ∑ i, d i = r * q) :
    (2 * ∑ i, (d i).choose 2 : ℤ) = 2 * r * q.choose 2 + ∑ i, ((d i : ℤ) - q) ^ 2 := by
  have h2 : ∀ x : ℕ, (2 * x.choose 2 : ℤ) = x * (x - 1) := by
    intro x
    have hn : 2 * x.choose 2 = x * (x - 1) := by
      rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self x).two_dvd
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · have : ((2 * x.choose 2 : ℕ) : ℤ) = ((x * (x - 1) : ℕ) : ℤ) := by rw [hn]
      push_cast [Nat.cast_sub hx] at this; linarith
  have hz : (∑ i, (d i : ℤ)) = r * q := by exact_mod_cast hs
  push_cast
  rw [mul_sum, sum_congr rfl (fun i _ => h2 (d i)), mul_assoc,
    show (2:ℤ) * (↑r * ↑(q.choose 2)) = ↑r * (2 * ↑(q.choose 2)) by ring, h2 q]
  have : ∑ i, ((d i : ℤ) * ((d i : ℤ) - 1)) = ∑ i, (((d i : ℤ) - q) ^ 2) + 2 * q * ∑ i, (d i : ℤ)
      - r * q ^ 2 - ∑ i, (d i : ℤ) := by
    rw [sum_congr rfl (fun i _ => show (d i : ℤ) * ((d i : ℤ) - 1) =
      ((d i : ℤ) - q) ^ 2 + 2 * q * (d i : ℤ) - (q : ℤ) ^ 2 - (d i : ℤ) by ring)]
    simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← mul_sum]
  rw [this, hz]; ring

local notation "Kn" n => (⊤ : SimpleGraph (Fin n))

/-- **Triangular graphs, parity excess.** If `n` is odd and `n - 1 = q·r` with `q` odd, then
`|L(K_n), K_r| ≥ n·r·C(q,2) + r/2`. -/
theorem tri_lower_parity (n q r : ℕ) (hn : n % 2 = 1) (hqr : n - 1 = q * r) (hq : q % 2 = 1) :
    ((n * (r * q.choose 2) + r / 2 : ℕ) : ℕ∞) ≤ nhf (Kn n).lineGraph (⊤ : SimpleGraph (Fin r)) := by
  apply le_nhf
  intro S ⟨g⟩
  have h := line_lower_r (top_regular n) S g
  set D := dcol (G := Kn n) (fun e => g e) with hD
  have hsum : ∀ v, ∑ i, D v i = r * q := by
    intro v; rw [hD, sum_dcol (top_regular n), hqr, mul_comm]
  -- each colour has an odd deviation somewhere
  have hdev : ∀ i, 1 ≤ ∑ v, ((D v i : ℤ) - q) ^ 2 := by
    intro i
    by_contra hlt
    push Not at hlt
    have hz : ∀ v, ((D v i : ℤ) - q) ^ 2 = 0 := by
      intro v
      have hnn : ∀ w ∈ (univ : Finset (Fin n)), (0 : ℤ) ≤ ((D w i : ℤ) - q) ^ 2 := fun w _ => sq_nonneg _
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (by
        have := Finset.sum_nonneg hnn; omega) v (mem_univ v)
      exact this
    have hall : ∀ v, D v i = q := by
      intro v; have := hz v; nlinarith [sq_nonneg ((D v i : ℤ) - q)]
    have he := sum_dcol_even (G := Kn n) (fun e => g e) i
    rw [← hD, sum_congr rfl (fun v _ => hall v), sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul, Nat.mul_mod, hn, hq] at he
    simp at he
  have htot : (2 * ∑ v, ∑ i, (D v i).choose 2 : ℤ) ≥ 2 * n * (r * q.choose 2) + r := by
    push_cast
    rw [mul_sum]
    have : ∀ v, (2 * ∑ i, ((D v i).choose 2 : ℤ)) = 2 * r * q.choose 2 + ∑ i, ((D v i : ℤ) - q) ^ 2 :=
      fun v => by have := two_sum_choose (D v) (hsum v); push_cast at this; exact this
    rw [sum_congr rfl (fun v _ => this v), sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, sum_comm]
    have : (r : ℤ) ≤ ∑ i, ∑ v, ((D v i : ℤ) - q) ^ 2 := by
      calc (r : ℤ) = ∑ _i : Fin r, (1 : ℤ) := by simp
        _ ≤ _ := sum_le_sum fun i _ => hdev i
    nlinarith
  have : n * (r * q.choose 2) + r / 2 ≤ ∑ v, ∑ i, (D v i).choose 2 := by
    have : (2 * (n * (r * q.choose 2)) + r : ℤ) ≤ 2 * ∑ v, ∑ i, (D v i).choose 2 := by
      push_cast at htot ⊢; linarith
    have : 2 * (n * (r * q.choose 2)) + r ≤ 2 * ∑ v, ∑ i, (D v i).choose 2 := by exact_mod_cast this
    omega
  exact_mod_cast this.trans h

/-! ### Even `n`: a 1-factorization -/

theorem mod_two_range (a N : ℕ) (h : a < 2 * N) : a % N = if a < N then a else a - N := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Colour of the edge `{u,w}` of `K_{2m}`, with `∞ = 2m-1`. -/
def oneFactCol (m : ℕ) (u w : Fin (2 * m)) : ℕ :=
  if u.val = 2 * m - 1 then (2 * w.val) % (2 * m - 1)
  else if w.val = 2 * m - 1 then (2 * u.val) % (2 * m - 1)
  else (u.val + w.val) % (2 * m - 1)

theorem oneFactCol_symm (m : ℕ) (u w : Fin (2 * m)) (huw : u ≠ w) :
    oneFactCol m u w = oneFactCol m w u := by
  have : u.val ≠ w.val := fun h => huw (Fin.ext h)
  unfold oneFactCol
  split_ifs <;> first | omega | (rw [add_comm])

/-- Proper: at every vertex the colours are distinct. -/
theorem oneFactCol_proper (m : ℕ) (hm : 1 ≤ m) (x y z : Fin (2 * m)) (hy : y ≠ x) (hz : z ≠ x)
    (h : oneFactCol m x y = oneFactCol m x z) : y = z := by
  apply Fin.ext
  have hxv := x.isLt; have hyv := y.isLt; have hzv := z.isLt
  have hy' : y.val ≠ x.val := fun e => hy (Fin.ext e)
  have hz' : z.val ≠ x.val := fun e => hz (Fin.ext e)
  unfold oneFactCol at h
  have e1 := mod_two_range (2 * y.val) (2 * m - 1)
  have e2 := mod_two_range (2 * z.val) (2 * m - 1)
  have e3 := mod_two_range (2 * x.val) (2 * m - 1)
  have e4 := mod_two_range (x.val + y.val) (2 * m - 1)
  have e5 := mod_two_range (x.val + z.val) (2 * m - 1)
  split_ifs at h <;> first
    | omega
    | (rw [e1 (by omega), e2 (by omega)] at h; split_ifs at h <;> omega)
    | (rw [e3 (by omega), e5 (by omega)] at h; split_ifs at h <;> omega)
    | (rw [e4 (by omega), e3 (by omega)] at h; split_ifs at h <;> omega)
    | (rw [e4 (by omega), e5 (by omega)] at h; split_ifs at h <;> omega)

/-- The 1-factorization as an edge colouring of `K_{2m}` by `2m-1` colours. -/
def oneFact (m : ℕ) (hm : 1 ≤ m) : (Kn (2 * m)).edgeSet → Fin (2 * m - 1) := fun e =>
  ⟨Sym2.lift ⟨fun u w => if u = w then 0 else oneFactCol m u w, fun u w => by
      by_cases h : u = w
      · subst h; rfl
      · show (if u = w then 0 else oneFactCol m u w) = (if w = u then 0 else oneFactCol m w u)
        rw [if_neg h, if_neg (Ne.symm h), oneFactCol_symm m u w h]⟩ e.1 % (2 * m - 1),
    Nat.mod_lt _ (by omega)⟩

/-- **Triangular graphs, even `n`.** For every `H` with clique number `r ≥ 1`,
`|L(K_{2m}), H| = 2m·(C(2m-1,2) - t(2m-1, r))`. -/
theorem nhf_triangular_even (m : ℕ) (hm : 1 ≤ m) {W : Type*} {H : SimpleGraph W} [DecidableEq W]
    {r : ℕ} (hr : 0 < r) (hcf : H.CliqueFree (r + 1)) (hK : (⊤ : SimpleGraph (Fin r)) →g H) :
    nhf (Kn (2 * m)).lineGraph H =
      ((2 * m * ((2 * m - 1).choose 2 - turanNumber (2 * m - 1) r) : ℕ) : ℕ∞) := by
  have h := nhf_line_class1 (top_regular (2 * m)) hr (oneFact m hm) ?_ hcf hK
  · rwa [Fintype.card_fin] at h
  · intro v e f hef
    obtain ⟨⟨e, he⟩, hve⟩ := e
    obtain ⟨⟨f, hf⟩, hvf⟩ := f
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hve
    obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hvf
    have hy : y ≠ v := fun h => ((SimpleGraph.mem_edgeSet _).mp he).ne h.symm
    have hz : z ≠ v := fun h => ((SimpleGraph.mem_edgeSet _).mp hf).ne h.symm
    simp only [oneFact, Fin.mk.injEq, Sym2.lift_mk, if_neg (Ne.symm hy), if_neg (Ne.symm hz)] at hef
    have hlt : ∀ a b : Fin (2 * m), oneFactCol m a b < 2 * m - 1 := by
      intro a b; unfold oneFactCol; split_ifs <;> exact Nat.mod_lt _ (by omega)
    rw [Nat.mod_eq_of_lt (hlt _ _), Nat.mod_eq_of_lt (hlt _ _)] at hef
    have := oneFactCol_proper m hm v y z hy hz hef
    subst this; rfl

end NonHom
