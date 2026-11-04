import NonHom.LineGraph
import NonHom.Families
import NonHom.OddCycles

/-!
# Triangular graphs `L(K_n)`

**Theorem.** `|L(K_n), K₂| = n·⌊(n-2)²/4⌋ + [n ≡ 3 (mod 4)]` for `n ≥ 2`.

General part (any `d`-regular `G`): a 2-colouring `c` of `E(G)` with `a_v` colour-0 edges at `v`
forces exactly `∑_v (C(d,2) - a_v(d - a_v))` deletions, and this is attained.
For `K_n`, `a_v(d - a_v) ≤ ⌊d²/4⌋`, with equality at every vertex impossible when
`n ≡ 3 (mod 4)` by handshake parity; explicit colourings attain the bound.
-/

open SimpleGraph Finset

namespace NonHom

section general

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Number of colour-0 edges at `v`. -/
def acnt (c : G.edgeSet → Fin 2) (v : V) : ℕ := (univ.filter fun e : At G v => c e.1 = 0).card

/-- Monochromatic pairs of edges at `v`, as a graph on the edges at `v`. -/
def monoAt (c : G.edgeSet → Fin 2) (v : V) : SimpleGraph (At G v) :=
  (⊤ : SimpleGraph (At G v)) \ (⊤ : SimpleGraph (Fin 2)).comap (fun e => c e.1)

theorem card_monoAt {d : ℕ} (hreg : G.IsRegularOfDegree d) (c : G.edgeSet → Fin 2) (v : V)
    [Fintype (monoAt c v).edgeSet] :
    (monoAt c v).edgeFinset.card = d.choose 2 - acnt c v * (d - acnt c v) := by
  classical
  unfold acnt
  set a := (univ.filter fun e : At G v => c e.1 = 0).card
  set b := (univ.filter fun e : At G v => c e.1 = 1).card
  have hab : a + b = d := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (At G v)))
      (fun e : At G v => c e.1 = 0)
    have hnot : (univ.filter fun e : At G v => ¬ c e.1 = 0) = univ.filter fun e => c e.1 = 1 := by
      ext e; simp only [mem_filter, mem_univ, true_and]; omega
    rw [hnot, card_univ, card_At hreg v] at h
    exact h
  let Dv : SimpleGraph (At G v) := (⊤ : SimpleGraph (Fin 2)).comap (fun e => c e.1)
  have hD : 2 * Dv.edgeFinset.card = 2 * (a * b) := by
    rw [two_mul_card_edgeFinset, ← card_diff_pairs (fun e : At G v => c e.1)]
    congr 1
  have hsd : (monoAt c v).edgeFinset = (⊤ : SimpleGraph (At G v)).edgeFinset \ Dv.edgeFinset := by
    ext z
    rw [mem_edgeFinset, mem_sdiff, mem_edgeFinset, mem_edgeFinset]
    simp only [monoAt, Dv, edgeSet_sdiff, Set.mem_diff]
  rw [hsd, card_sdiff_of_subset (edgeFinset_mono le_top), card_edgeFinset_top_eq_card_choose_two,
    card_At hreg, show d - a = b by omega]
  omega

/-- **Upper bound** from any 2-colouring. -/
theorem line_upper_gen {d : ℕ} (hreg : G.IsRegularOfDegree d) (c : G.edgeSet → Fin 2) :
    nhf G.lineGraph (⊤ : SimpleGraph (Fin 2)) ≤
      ((∑ v, (d.choose 2 - acnt c v * (d - acnt c v)) : ℕ) : ℕ∞) := by
  classical
  let Mono : SimpleGraph G.edgeSet := G.lineGraph ⊓ SimpleGraph.fromRel fun a b => c a = c b
  let S : Finset (Sym2 G.edgeSet) := Mono.edgeFinset
  have hhom : Nonempty (G.lineGraph.deleteEdges ↑S →g (⊤ : SimpleGraph (Fin 2))) := by
    refine ⟨⟨c, fun {a b} h => ?_⟩⟩
    rw [deleteEdges_adj] at h
    intro hab
    apply h.2
    simp only [S, coe_edgeFinset]
    exact ⟨h.1, h.1.ne, Or.inl hab⟩
  refine (nhf_le_card S hhom).trans ?_
  norm_cast
  let ι : ∀ v, Sym2 (At G v) → Sym2 G.edgeSet := fun v => Sym2.map Subtype.val
  have hcover : S ⊆ univ.biUnion fun v => (monoAt c v).edgeFinset.image (ι v) := by
    intro z hz
    simp only [S, mem_edgeFinset] at hz
    induction z using Sym2.ind with
    | _ a b =>
      obtain ⟨hL, -, hcol⟩ := hz
      rw [lineGraph_adj_iff_exists] at hL
      obtain ⟨hne, v, hva, hvb⟩ := hL
      have hcab : c a = c b := hcol.elim id Eq.symm
      rw [mem_biUnion]
      refine ⟨v, mem_univ _, mem_image.mpr ⟨s(⟨a, hva⟩, ⟨b, hvb⟩), ?_, rfl⟩⟩
      rw [mem_edgeFinset]
      show (monoAt c v).Adj ⟨a, hva⟩ ⟨b, hvb⟩
      exact ⟨fun h => hne (congrArg Subtype.val h), fun h => h hcab⟩
  calc S.card ≤ (univ.biUnion fun v => (monoAt c v).edgeFinset.image (ι v)).card := card_le_card hcover
    _ ≤ ∑ v, ((monoAt c v).edgeFinset.image (ι v)).card := card_biUnion_le
    _ ≤ ∑ v, (d.choose 2 - acnt c v * (d - acnt c v)) :=
        sum_le_sum fun v _ => card_image_le.trans (card_monoAt hreg c v).le

/-- **Lower bound**: a deletion set compatible with `g` contains all monochromatic pairs. -/
theorem line_lower_gen {d : ℕ} (hreg : G.IsRegularOfDegree d) (S : Finset (Sym2 G.edgeSet))
    (g : G.lineGraph.deleteEdges ↑S →g (⊤ : SimpleGraph (Fin 2))) :
    ∑ v, (d.choose 2 - acnt (fun e => g e) v * (d - acnt (fun e => g e) v)) ≤ S.card := by
  classical
  let c : G.edgeSet → Fin 2 := fun e => g e
  let ι : ∀ v, Sym2 (At G v) → Sym2 G.edgeSet := fun v => Sym2.map Subtype.val
  have hsub : ∀ v, (monoAt c v).edgeFinset.image (ι v) ⊆ S := by
    intro v z hz
    obtain ⟨z, hzM, rfl⟩ := mem_image.mp hz
    rw [mem_edgeFinset] at hzM
    induction z using Sym2.ind with
    | _ a b =>
      obtain ⟨hab, hcol⟩ := hzM
      have hab' : a ≠ b := hab
      have hcab : c a.1 = c b.1 := by
        by_contra h; exact hcol h
      by_contra hS
      have hadj : (G.lineGraph.deleteEdges ↑S).Adj a.1 b.1 := by
        rw [deleteEdges_adj, lineGraph_adj_iff_exists]
        exact ⟨⟨fun h => hab' (Subtype.ext h), v, a.2, b.2⟩, hS⟩
      exact g.map_rel hadj hcab
  have hdisj : ∀ v ∈ (univ : Finset V), ∀ w ∈ (univ : Finset V), v ≠ w →
      Disjoint ((monoAt c v).edgeFinset.image (ι v)) ((monoAt c w).edgeFinset.image (ι w)) := by
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
  have hbig : (univ.biUnion fun v => (monoAt c v).edgeFinset.image (ι v)) ⊆ S :=
    biUnion_subset.mpr fun v _ => hsub v
  have hcard := card_le_card hbig
  rw [card_biUnion hdisj] at hcard
  refine le_trans ?_ hcard
  apply sum_le_sum
  intro v _
  rw [card_image_of_injective _ (Sym2.map.injective Subtype.val_injective), card_monoAt hreg c v]

/-- Handshake: `∑_v a_v` is even. -/
theorem sum_acnt_even (c : G.edgeSet → Fin 2) : (∑ v, acnt c v) % 2 = 0 := by
  classical
  have h : ∀ v, acnt c v = (univ.filter fun e : G.edgeSet => v ∈ (e : Sym2 V) ∧ c e = 0).card := by
    intro v
    unfold acnt
    apply card_bij (fun e _ => e.1)
    · intro e he; simp only [mem_filter, mem_univ, true_and] at he ⊢; exact ⟨e.2, he⟩
    · intro e₁ _ e₂ _ h; exact Subtype.ext h
    · intro e he
      simp only [mem_filter, mem_univ, true_and] at he
      exact ⟨⟨e, he.1⟩, by simpa using he.2, rfl⟩
  simp only [h, card_filter]
  rw [sum_comm]
  have h2 : ∀ e : G.edgeSet, (∑ v, if v ∈ (e : Sym2 V) ∧ c e = 0 then 1 else 0) =
      2 * (if c e = 0 then 1 else 0) := by
    intro e
    obtain ⟨e, he⟩ := e
    induction e using Sym2.ind with
    | _ u w =>
      have huw : u ≠ w := he.ne
      by_cases hc : c ⟨s(u, w), he⟩ = 0
      · simp only [hc, and_true, if_true, mul_one]
        rw [← card_filter]
        have : (univ.filter fun v => v ∈ s(u, w)) = {u, w} := by ext v; simp
        rw [this, card_pair huw]
      · simp [hc]
  rw [sum_congr rfl (fun e _ => h2 e), ← mul_sum]
  omega

end general

/-! ### `K_n` -/

theorem prod_le_sq_div (a d : ℕ) (ha : a ≤ d) : a * (d - a) ≤ d ^ 2 / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  obtain ⟨b, rfl⟩ : ∃ b, d = a + b := ⟨d - a, by omega⟩
  rw [Nat.add_sub_cancel_left]
  nlinarith [sq_nonneg ((a : ℤ) - b)]

theorem prod_le_sq_div_sub (a d : ℕ) (ha : a ≤ d) (hd : d % 2 = 0) (hne : a ≠ d / 2) :
    a * (d - a) + 1 ≤ d ^ 2 / 4 := by
  obtain ⟨t, rfl⟩ : ∃ t, d = 2 * t := ⟨d / 2, by omega⟩
  rw [show (2 * t) ^ 2 / 4 = t * t by rw [show (2 * t) ^ 2 = 4 * (t * t) by ring]; omega]
  have hne' : a ≠ t := by omega
  rcases Nat.lt_or_gt_of_ne hne' with h | h
  · obtain ⟨s, rfl⟩ : ∃ s, t = a + s + 1 := ⟨t - a - 1, by omega⟩
    rw [show 2 * (a + s + 1) - a = a + 2 * s + 2 by omega]; nlinarith
  · obtain ⟨s, rfl⟩ : ∃ s, a = t + s + 1 := ⟨a - t - 1, by omega⟩
    rw [show 2 * t - (t + s + 1) = t - s - 1 by omega]
    rcases Nat.lt_or_ge t (s + 1) with h' | h'
    · rw [show t - s - 1 = 0 by omega]; nlinarith
    · obtain ⟨u, rfl⟩ : ∃ u, t = s + 1 + u := ⟨t - s - 1, by omega⟩
      rw [show s + 1 + u - s - 1 = u by omega]; nlinarith

local notation "Kn" n => (⊤ : SimpleGraph (Fin n))

theorem top_regular (n : ℕ) : (Kn n).IsRegularOfDegree (n - 1) := by
  simpa using (IsRegularOfDegree.top (V := Fin n))

theorem acnt_le {n : ℕ} (c : (Kn n).edgeSet → Fin 2) (v : Fin n) : acnt c v ≤ n - 1 := by
  unfold acnt
  calc _ ≤ (univ : Finset (At (Kn n) v)).card := card_filter_le _ _
    _ = n - 1 := by rw [card_univ, card_At (top_regular n)]

/-- **Lower bound** for triangular graphs. -/
theorem tri_lower (n : ℕ) (hn : 2 ≤ n) :
    ((n * ((n - 2) ^ 2 / 4) + (if n % 4 = 3 then 1 else 0) : ℕ) : ℕ∞) ≤
      nhf (Kn n).lineGraph (⊤ : SimpleGraph (Fin 2)) := by
  apply le_nhf
  intro S ⟨g⟩
  have h := line_lower_gen (top_regular n) S g
  set a := acnt (fun e => g e)
  set T := (n - 2) ^ 2 / 4
  have hT : (n - 1).choose 2 - (n - 1) ^ 2 / 4 = T := by
    rw [choose_two_sub]; simp only [T]; congr 2
  have hsq : (n - 1) ^ 2 / 4 ≤ (n - 1).choose 2 := by
    rw [Nat.choose_two_right]
    obtain ⟨d, hd⟩ : ∃ d, n - 1 = d + 1 := ⟨n - 2, by omega⟩
    rw [hd, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp
    · calc (d + 1) ^ 2 / 4 ≤ (2 * ((d + 1) * d)) / (2 * 2) := Nat.div_le_div_right (by nlinarith)
        _ = (d + 1) * d / 2 := Nat.mul_div_mul_left _ 2 (by norm_num)
  have term : ∀ v, T ≤ (n - 1).choose 2 - a v * (n - 1 - a v) := by
    intro v
    have := prod_le_sq_div (a v) (n - 1) (acnt_le _ v)
    omega
  have base : n * T ≤ ∑ v, ((n - 1).choose 2 - a v * (n - 1 - a v)) := by
    calc n * T = ∑ _v : Fin n, T := by simp
      _ ≤ _ := sum_le_sum fun v _ => term v
  norm_cast
  split_ifs with h3
  · -- some vertex is unbalanced
    have hex : ∃ v, a v ≠ (n - 1) / 2 := by
      by_contra hall
      push Not at hall
      have he := sum_acnt_even (fun e => g e)
      rw [show (∑ v, acnt (fun e => g e) v) = n * ((n - 1) / 2) by
        rw [sum_congr rfl (fun v _ => hall v)]; simp] at he
      have : n % 2 = 1 := by omega
      have : ((n - 1) / 2) % 2 = 1 := by omega
      rw [Nat.mul_mod] at he
      simp_all
    obtain ⟨v₀, hv₀⟩ := hex
    have t0 : T + 1 ≤ (n - 1).choose 2 - a v₀ * (n - 1 - a v₀) := by
      have := prod_le_sq_div_sub (a v₀) (n - 1) (acnt_le _ v₀) (by omega) hv₀
      omega
    rw [← Finset.add_sum_erase _ _ (mem_univ v₀)] at h
    have rest : (n - 1) * T ≤ ∑ v ∈ univ.erase v₀, ((n - 1).choose 2 - a v * (n - 1 - a v)) := by
      calc (n - 1) * T = ∑ _v ∈ univ.erase v₀, T := by
            rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, smul_eq_mul]
        _ ≤ _ := sum_le_sum fun v _ => term v
    have : n * T = (n - 1) * T + T := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp [add_mul]
    omega
  · omega

/-! #### Constructions -/

/-- Colouring from a symmetric predicate: colour 0 iff `P`. -/
def colOf {n : ℕ} (P : Fin n → Fin n → Prop) [DecidableRel P] (hP : ∀ u w, P u w ↔ P w u)
    (e : (Kn n).edgeSet) : Fin 2 :=
  if Sym2.lift ⟨fun u w => decide (P u w), fun u w => by simp [hP u w]⟩ e.1 then 0 else 1

theorem acnt_colOf {n : ℕ} (P : Fin n → Fin n → Prop) [DecidableRel P] (hP : ∀ u w, P u w ↔ P w u)
    (v : Fin n) : acnt (colOf P hP) v = (univ.filter fun u => u ≠ v ∧ P v u).card := by
  unfold acnt
  symm
  apply card_bij (fun u hu => (⟨⟨s(v, u), by
      simp only [mem_filter, mem_univ, true_and] at hu
      exact (top_adj v u).mpr (Ne.symm hu.1)⟩, Sym2.mem_mk_left v u⟩ : At (Kn n) v))
  · intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu ⊢
    simp [colOf, hu.2]
  · intro u hu u' hu' h
    have h' := congrArg (fun z : At (Kn n) v => (z.1 : Sym2 (Fin n))) h
    exact Sym2.congr_right.mp h'
  · rintro ⟨⟨e, he⟩, hv⟩ hcol
    simp only [mem_filter, mem_univ, true_and] at hcol
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hv
    refine ⟨u, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨fun h => ((SimpleGraph.mem_edgeSet _).mp he).ne h.symm, ?_⟩
    by_contra hP'
    simp [colOf, hP'] at hcol

/-- Per-vertex cost of a balanced vertex: `C(d,2) - ⌊d²/4⌋ = ⌊(d-1)²/4⌋`. -/
theorem cost_balanced (d a : ℕ) (ha : a * (d - a) = d ^ 2 / 4) :
    d.choose 2 - a * (d - a) = (d - 1) ^ 2 / 4 := by
  rw [ha, choose_two_sub]

theorem sum_parity_count (v m : ℕ) :
    ∑ x ∈ range (2 * m), (if (v + x) % 2 = 1 then 1 else 0) = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    split_ifs <;> omega

/-- Even `n = 2m`: colour `uw` by the parity of `u + w`. -/
theorem tri_upper_even (m : ℕ) (hm : 1 ≤ m) :
    nhf (Kn (2 * m)).lineGraph (⊤ : SimpleGraph (Fin 2)) ≤
      ((2 * m * ((2 * m - 2) ^ 2 / 4) : ℕ) : ℕ∞) := by
  have : NeZero (2 * m) := ⟨by omega⟩
  let P : Fin (2 * m) → Fin (2 * m) → Prop := fun u w => (u.val + w.val) % 2 = 1
  have hP : ∀ u w, P u w ↔ P w u := fun u w => by simp only [P, add_comm]
  refine (line_upper_gen (top_regular (2 * m)) (colOf P hP)).trans ?_
  have ha : ∀ v, acnt (colOf P hP) v = m := by
    intro v
    rw [acnt_colOf]
    have : (univ.filter fun u : Fin (2 * m) => u ≠ v ∧ P v u) =
        univ.filter fun u : Fin (2 * m) => (v.val + u.val) % 2 = 1 := by
      ext u; simp only [mem_filter, mem_univ, true_and, P]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨fun e => by subst e; omega, h⟩
    rw [this, card_filter, Fin.sum_univ_eq_sum_range (fun x => if (v.val + x) % 2 = 1 then 1 else 0),
      sum_parity_count]
  have hcost : ∀ v, (2 * m - 1).choose 2 - acnt (colOf P hP) v * (2 * m - 1 - acnt (colOf P hP) v) =
      (2 * m - 2) ^ 2 / 4 := by
    intro v
    rw [ha, cost_balanced]
    · congr 2
    · obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
      rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega, show 2 * t + 1 - (t + 1) = t by omega,
        show (2 * t + 1) ^ 2 = 4 * ((t + 1) * t) + 1 by ring]
      omega
  rw [sum_congr rfl (fun v _ => hcost v)]
  simp

theorem sum_ite_all (k : ℕ) (p : ℕ → Prop) [DecidablePred p] (h : ∀ x < k, p x) :
    ∑ x ∈ range k, (if p x then 1 else 0) = k := by
  rw [sum_congr rfl (fun x hx => if_pos (h x (mem_range.mp hx)))]; simp

theorem sum_ite_none (k : ℕ) (p : ℕ → Prop) [DecidablePred p] (h : ∀ x < k, ¬ p x) :
    ∑ x ∈ range k, (if p x then 1 else 0) = 0 := by
  rw [sum_congr rfl (fun x hx => if_neg (h x (mem_range.mp hx)))]; simp

theorem count_near (n k : ℕ) (hk : 2 * k < n) :
    ∑ x ∈ range n, (if x ≠ 0 ∧ min (n - x) x ≤ k then 1 else 0) = 2 * k := by
  have hsplit : n = (k + 1) + (n - 2 * k - 1) + k := by omega
  rw [hsplit, sum_range_add, sum_range_add, sum_range_succ']
  rw [← hsplit]
  rw [sum_ite_all k _ (fun x hx => by constructor <;> omega),
    sum_ite_none (n - 2 * k - 1) _ (fun x hx => by omega),
    sum_ite_all k _ (fun x hx => by constructor <;> omega)]
  simp; ring

/-- Odd `n = 2m+1`: circulant distance `≤ ⌈m/2⌉`, minus a near-perfect matching if `m` is odd. -/
theorem tri_upper_odd (m : ℕ) (hm : 1 ≤ m) :
    nhf (Kn (2 * m + 1)).lineGraph (⊤ : SimpleGraph (Fin 2)) ≤
      (((2 * m + 1) * ((2 * m - 1) ^ 2 / 4) + (if m % 2 = 1 then 1 else 0) : ℕ) : ℕ∞) := by
  set n := 2 * m + 1 with hn
  set k := (m + 1) / 2 with hk
  let dm : Fin n → Fin n → ℕ := fun u w => min ((u - w).val) ((w - u).val)
  let Mt : Fin n → Fin n → Prop := fun u w =>
    m % 2 = 1 ∧ u.val < 2 * m ∧ w.val < 2 * m ∧ u.val / 2 = w.val / 2 ∧ u ≠ w
  let P : Fin n → Fin n → Prop := fun u w => u ≠ w ∧ dm u w ≤ k ∧ ¬ Mt u w
  have hP : ∀ u w, P u w ↔ P w u := by
    intro u w
    simp only [P, dm, Mt, ne_comm, min_comm, eq_comm (a := u.val / 2)]
    tauto
  haveI : DecidableRel P := fun u w => by simp only [P, dm, Mt]; infer_instance
  refine (line_upper_gen (top_regular n) (colOf P hP)).trans ?_
  -- number of `u ≠ v` at circular distance `≤ k`
  have hdm : ∀ u v : Fin n, (u ≠ v ∧ dm v u ≤ k) ↔
      ((u - v).val ≠ 0 ∧ min (n - (u - v).val) (u - v).val ≤ k) := by
    intro u v
    simp only [dm, ne_eq, Fin.ext_iff]
    rw [fin_sub_val v u, fin_sub_val u v]
    have := u.isLt; have := v.isLt
    split_ifs <;> omega
  have hA : ∀ v : Fin n, (univ.filter fun u : Fin n => u ≠ v ∧ dm v u ≤ k).card = 2 * k := by
    intro v
    have hbij : (univ.filter fun u : Fin n => u ≠ v ∧ dm v u ≤ k).card =
        (univ.filter fun x : Fin n => x.val ≠ 0 ∧ min (n - x.val) x.val ≤ k).card := by
      apply card_bij (fun u _ => u - v)
      · intro u hu
        simp only [mem_filter, mem_univ, true_and] at hu ⊢
        exact (hdm u v).mp hu
      · intro u _ u' _ h
        simpa using h
      · intro x hx
        refine ⟨x + v, ?_, by simp⟩
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        rw [hdm]; simpa using hx
    rw [hbij, card_filter,
      Fin.sum_univ_eq_sum_range (fun x => if x ≠ 0 ∧ min (n - x) x ≤ k then 1 else 0) n]
    exact count_near n k (by omega)
  -- matched partners
  have hB : ∀ v : Fin n, (univ.filter fun u : Fin n => Mt v u).card =
      if m % 2 = 1 ∧ v.val < 2 * m then 1 else 0 := by
    intro v
    split_ifs with h
    · rw [card_eq_one]
      refine ⟨⟨if v.val % 2 = 0 then v.val + 1 else v.val - 1, by split_ifs <;> omega⟩, ?_⟩
      ext u
      simp only [mem_filter, mem_univ, true_and, mem_singleton, Mt, Fin.ext_iff, ne_eq]
      have := u.isLt
      split_ifs <;> omega
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro u - ⟨h1, h2, -⟩
      exact h ⟨h1, h2⟩
  have hMsub : ∀ u v : Fin n, Mt v u → u ≠ v ∧ dm v u ≤ k := by
    intro u v hM
    rw [hdm]
    simp only [Mt, ne_eq, Fin.ext_iff] at hM
    rw [fin_sub_val]
    have := u.isLt; have := v.isLt
    split_ifs <;> omega
  have ha : ∀ v : Fin n, acnt (colOf P hP) v = 2 * k - (if m % 2 = 1 ∧ v.val < 2 * m then 1 else 0) := by
    intro v
    rw [acnt_colOf, ← hB, ← hA v]
    have htot := card_filter_add_card_filter_not
      (s := univ.filter fun u : Fin n => u ≠ v ∧ dm v u ≤ k) (fun u => Mt v u)
    have e1 : ((univ.filter fun u : Fin n => u ≠ v ∧ dm v u ≤ k).filter fun u => Mt v u) =
        univ.filter fun u => Mt v u := by
      ext u; simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hMsub u v h, h⟩⟩
    have e2 : ((univ.filter fun u : Fin n => u ≠ v ∧ dm v u ≤ k).filter fun u => ¬ Mt v u) =
        univ.filter fun u => u ≠ v ∧ P v u := by
      ext u; simp only [mem_filter, mem_univ, true_and, P]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, Ne.symm h1, h2, h3⟩
      · rintro ⟨h1, -, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    rw [e1, e2] at htot
    omega
  set T := (2 * m - 1) ^ 2 / 4 with hT
  have hcost : ∀ v : Fin n, (n - 1).choose 2 - acnt (colOf P hP) v * (n - 1 - acnt (colOf P hP) v) =
      if m % 2 = 1 ∧ v.val = 2 * m then T + 1 else T := by
    intro v
    rw [ha, show n - 1 = 2 * m by omega]
    have hv := v.isLt
    have hc : (2 * m).choose 2 = m * (2 * m - 1) := by
      rw [Nat.choose_two_right]
      obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
      rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega,
        show 2 * (t + 1) * (2 * t + 1) = 2 * ((t + 1) * (2 * t + 1)) by ring]
      simp
    have hTv : T = m * m - m := by
      rw [hT]
      obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
      rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega, show (2 * t + 1) ^ 2 = 4 * ((t + 1) * (t + 1) - (t + 1)) + 1 by
        rw [show (t + 1) * (t + 1) - (t + 1) = t * (t + 1) by
          rw [Nat.sub_eq_iff_eq_add (by nlinarith)]; ring]; ring]
      omega
    rw [hc, hTv]
    rcases Nat.mod_two_eq_zero_or_one m with hpar | hpar
    · have h2k : 2 * k = m := by omega
      simp only [hpar, show (0 : ℕ) ≠ 1 by norm_num, false_and, if_false, Nat.sub_zero, h2k]
      rw [show 2 * m - m = m by omega]
      have : m * (2 * m - 1) = m * m + (m * m - m) := by
        obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
        rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega]
        rw [show (t + 1) * (t + 1) - (t + 1) = t * (t + 1) by
          rw [Nat.sub_eq_iff_eq_add (by nlinarith)]; ring]; ring
      omega
    · have h2k : 2 * k = m + 1 := by omega
      rw [h2k]
      have key : m * (2 * m - 1) = m * m + (m * m - m) := by
        obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
        rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega]
        rw [show (t + 1) * (t + 1) - (t + 1) = t * (t + 1) by
          rw [Nat.sub_eq_iff_eq_add (by nlinarith)]; ring]; ring
      by_cases hv2 : v.val = 2 * m
      · rw [if_neg (by omega), if_pos ⟨hpar, hv2⟩, Nat.sub_zero,
          show 2 * m - (m + 1) = m - 1 by omega]
        have : (m + 1) * (m - 1) + 1 = m * m := by
          obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
          rw [Nat.add_sub_cancel]; ring
        omega
      · rw [if_pos ⟨hpar, by omega⟩, if_neg (fun h => hv2 h.2), show m + 1 - 1 = m by omega,
          show 2 * m - m = m by omega]
        omega
  rw [sum_congr rfl (fun v _ => hcost v)]
  norm_cast
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last]
  rw [sum_congr rfl (fun i _ => if_neg (fun h => by have := i.isLt; omega))]
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  split_ifs with h1 h2 h2 <;> simp_all <;> ring_nf <;> exact le_rfl

/-- **Triangular graphs.** `|L(K_n), K₂| = n·⌊(n-2)²/4⌋ + [n ≡ 3 (mod 4)]` for `n ≥ 2`. -/
theorem nhf_triangular (n : ℕ) (hn : 2 ≤ n) :
    nhf (Kn n).lineGraph (⊤ : SimpleGraph (Fin 2)) =
      ((n * ((n - 2) ^ 2 / 4) + (if n % 4 = 3 then 1 else 0) : ℕ) : ℕ∞) := by
  apply le_antisymm _ (tri_lower n hn)
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · refine (tri_upper_even m (by omega)).trans ?_
    rw [if_neg (by omega), add_zero]
  · refine (tri_upper_odd m (by omega)).trans ?_
    rw [show 2 * m + 1 - 2 = 2 * m - 1 by omega]
    have : (if m % 2 = 1 then 1 else 0) = (if (2 * m + 1) % 4 = 3 then 1 else 0) := by
      split_ifs <;> omega
    rw [this]

end NonHom
