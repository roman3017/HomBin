module

public import HomBin.Defs

@[expose] public section

open Finset MvPolynomial

namespace HomBin

lemma exists_det_submatrix_ne_zero {K : Type*} [Field K] {k n : ℕ}
    (B : Matrix (Fin k) (Fin n) K) (hB : LinearIndependent K B.row) :
    ∃ g : Fin k → Fin n, Function.Injective g ∧ (B.submatrix id g).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K B.col
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = k := by
    have h1 := finrank_span_eq_card hli
    rw [hspan, ← Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_row,
      finrank_span_eq_card hB] at h1
    simpa using h1.symm
  let e : Fin k ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hli' : LinearIndependent K (B.submatrix id (a ∘ e)).col := hli.comp e e.injective
  rw [Matrix.linearIndependent_col_iff_isUnit, Matrix.isUnit_iff_isUnit_det] at hli'
  exact hli'.ne_zero

lemma rank_le_of_minors_zero {K : Type*} [Field K] {s t r : ℕ} (M : Matrix (Fin s) (Fin t) K)
    (hminor : ∀ f : Fin (r + 1) → Fin s, ∀ g : Fin (r + 1) → Fin t,
      Function.Injective f → Function.Injective g → (M.submatrix f g).det = 0) :
    M.rank ≤ r := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K M.row
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hrk : M.rank = Fintype.card κ := by
    rw [Matrix.rank_eq_finrank_span_row, ← hspan, finrank_span_eq_card hli]
  rw [hrk]
  by_contra h
  push Not at h
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin (r + 1)) (β := κ)
    (by simpa using h)
  have hli' : LinearIndependent K (M.submatrix (a ∘ e) id).row := hli.comp e e.injective
  obtain ⟨g, hg, hdet⟩ := exists_det_submatrix_ne_zero _ hli'
  exact hdet (by simpa using hminor (a ∘ e) g (ha.comp e.injective) hg)

theorem exists_prime_rank_le {m r s t : ℕ} (P : Matrix (Fin s) (Fin t) ℤ) (c : ZMod m)
    (hc : c ≠ 0) (E : Matrix (Fin s) (Fin r) (ZMod m)) (H : Matrix (Fin r) (Fin t) (ZMod m))
    (hEH : E * H = c • P.map (Int.cast : ℤ → ZMod m)) :
    ∃ p : ℕ, p.Prime ∧ (P.map (Int.cast : ℤ → ZMod p)).rank ≤ r := by
  classical
  set E' : Matrix (Fin s) (Fin r) ℤ := E.map (fun z => (z.cast : ℤ)) with hE'
  set H' : Matrix (Fin r) (Fin t) ℤ := H.map (fun z => (z.cast : ℤ)) with hH'
  set c' : ℤ := c.cast with hc'
  have hdiv : ∀ i l, (m : ℤ) ∣ (E' * H') i l - c' * P i l := by
    intro i l
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congrFun (congrFun hEH i) l
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    simp [E', H', c', Matrix.mul_apply, this]
  have hcm : ¬ (m : ℤ) ∣ c' := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hc', ZMod.intCast_zmod_cast]; exact hc

  obtain ⟨p, e, hp, hpm, c'', hu, hpu⟩ : ∃ p e : ℕ, p.Prime ∧ (p : ℤ) ^ (e + 1) ∣ m ∧
      ∃ c'' : ℤ, c' = (p : ℤ) ^ e * c'' ∧ ¬ (p : ℤ) ∣ c'' := by
    have hc0 : c' ≠ 0 := by intro h; apply hcm; rw [h]; exact dvd_zero _
    have hmc : ¬ m ∣ c'.natAbs := by rwa [← Int.natCast_dvd]
    rw [Nat.dvd_iff_prime_pow_dvd_dvd] at hmc
    push Not at hmc
    obtain ⟨p, k, hp, hpm, hpc⟩ := hmc
    have : Fact p.Prime := ⟨hp⟩
    have hne : c'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc0
    set e := multiplicity p c'.natAbs with he
    have hek : e < k := by
      by_contra h
      push Not at h
      exact hpc ((pow_dvd_pow p h).trans (pow_multiplicity_dvd p _))
    obtain ⟨c'', hu⟩ : (p : ℤ) ^ e ∣ c' := by
      rw [← Int.natCast_pow, Int.natCast_dvd]; exact pow_multiplicity_dvd p _
    refine ⟨p, e, hp, ?_, c'', hu, ?_⟩
    · exact_mod_cast (pow_dvd_pow p (by omega : e + 1 ≤ k)).trans hpm
    · rintro ⟨v, hv⟩
      apply pow_succ_multiplicity_not_dvd (p := p) hne
      rw [← he, ← Int.natCast_dvd_natCast, Int.natCast_natAbs, dvd_abs, hu, hv]
      exact ⟨v, by push_cast; ring⟩
  have : Fact p.Prime := ⟨hp⟩
  have hD : ∀ i l, ∃ d : ℤ, (E' * H') i l - c' * P i l = (p : ℤ) ^ (e + 1) * d :=
    fun i l => (hpm.trans (hdiv i l))
  choose D hD using hD
  set B : Matrix (Fin s) (Fin t) ℤ := Matrix.of fun i l => c'' * P i l + p * D i l with hBdef
  have hB : E' * H' = ((p : ℤ) ^ e) • B := by
    ext i l
    simp only [Matrix.smul_apply, smul_eq_mul, B, Matrix.of_apply]
    linear_combination hD i l + P i l * hu
  have hBminor : ∀ f : Fin (r + 1) → Fin s, ∀ g : Fin (r + 1) → Fin t,
      (B.submatrix f g).det = 0 := by
    intro f g

    have h1 : ((E' * H').submatrix f g).det = 0 := by
      rw [Matrix.submatrix_mul _ _ f id g Function.bijective_id]
      set A := E'.submatrix f id
      set A' := H'.submatrix id g
      have hq : ((A * A').map (Int.cast : ℤ → ℚ)).det = 0 := by
        by_contra h
        have h1 := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit h))
        have h2 : ((A * A').map (Int.cast : ℤ → ℚ)).rank ≤ r := by
          have hm : (A * A').map (Int.cast : ℤ → ℚ) =
              A.map (Int.castRingHom ℚ) * A'.map (Int.castRingHom ℚ) := by
            ext i j; simp [Matrix.mul_apply]
          rw [hm]
          exact (Matrix.rank_mul_le_right _ _).trans ((Matrix.rank_le_card_height _).trans (by simp))
        simp at h1
        omega
      have := RingHom.map_det (Int.castRingHom ℚ) (A * A')
      rw [RingHom.mapMatrix_apply] at this
      simp only [Int.coe_castRingHom] at this
      rw [← this] at hq
      exact_mod_cast hq
    have h2 : (E' * H').submatrix f g = ((p : ℤ) ^ e) • B.submatrix f g := by rw [hB]; rfl
    rw [h2, Matrix.det_smul] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exfalso
      exact pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)) h
    · exact h
  have hBp : (B.map (Int.cast : ℤ → ZMod p)).rank ≤ r := by
    apply rank_le_of_minors_zero
    intro f g _ _
    have := RingHom.map_det (Int.castRingHom (ZMod p)) (B.submatrix f g)
    rw [hBminor f g, map_zero] at this
    rw [this]
    rfl
  have hc''0 : (c'' : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpu
  have hPB : P.map (Int.cast : ℤ → ZMod p) =
      ((c'' : ZMod p)⁻¹ • (1 : Matrix (Fin s) (Fin s) (ZMod p))) * B.map (Int.cast : ℤ → ZMod p) := by
    rw [Matrix.smul_mul, Matrix.one_mul]
    ext i l
    simp [B, inv_mul_cancel_left₀ hc''0]
  refine ⟨p, hp, ?_⟩
  rw [hPB]
  exact (Matrix.rank_mul_le_right _ _).trans hBp

theorem rank_criterion {X Y Z : Type*} [DecidableEq Z] (f : X → Y → Z) (r m : ℕ)
    {s t : ℕ} (x₀ : X) (x : Fin s → X) (y : Fin t → Y) (u w : Z) (huw : u ≠ w)
    (hx₀ : ∀ l, f x₀ (y l) = u) (hval : ∀ i l, f (x i) (y l) = u ∨ f (x i) (y l) = w)
    (hrank : ∀ p : ℕ, p.Prime →
      r < (Matrix.of fun i l => if f (x i) (y l) = w then (1 : ZMod p) else 0).rank)
    (j : Z → ZMod m) (hj : Function.Injective j)
    (G : Fin r → X → ZMod m) (H : Fin r → Y → ZMod m) (H₀ : Y → ZMod m) :
    ¬ ∀ a b, j (f a b) = H₀ b + ∑ k, G k a * H k b := by
  intro hrep
  have hc : j u - j w ≠ 0 := sub_ne_zero.mpr (fun h => huw (hj h))
  obtain ⟨p, hp, hle⟩ := exists_prime_rank_le
    (Matrix.of fun i l => if f (x i) (y l) = w then (1 : ℤ) else 0) (j u - j w) hc
    (Matrix.of fun i k => G k x₀ - G k (x i)) (Matrix.of fun k l => H k (y l)) (by
      ext i l

      have h1 := hrep x₀ (y l)
      have h2 := hrep (x i) (y l)
      rw [hx₀] at h1
      simp only [Matrix.mul_apply, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
        Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      rcases hval i l with h | h
      · rw [h] at h2 ⊢; rw [ite_eq_right huw]; simp only [Int.cast_zero, mul_zero]
        linear_combination h2 - h1
      · rw [h] at h2 ⊢; rw [ite_eq_left rfl]; simp only [Int.cast_one, mul_one]
        linear_combination h2 - h1)
  have heq : (Matrix.of fun i l => if f (x i) (y l) = w then (1 : ℤ) else 0).map
      (Int.cast : ℤ → ZMod p) =
      Matrix.of fun i l => if f (x i) (y l) = w then (1 : ZMod p) else 0 := by
    ext i l; simp only [Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp
  rw [heq] at hle
  exact absurd (hrank p hp) (not_lt.mpr hle)

theorem shiftInd_not_sum (n r : ℕ) (hr : r + 2 ≤ n) (m : ℕ)
    (j : ZMod n → ZMod m) (hj : Function.Injective j) (G H : Fin r → ZMod n → ZMod m)
    (H₀ : ZMod n → ZMod m) :
    ¬ ∀ a b, j (shiftInd n a b) = H₀ b + ∑ k, G k a * H k b := by
  have : NeZero n := ⟨by omega⟩
  have : Fact (1 < n) := ⟨by omega⟩
  have hxv : ∀ i : Fin (n - 1), ((((i : ℕ) + 1 : ℕ) : ZMod n)).val = i + 1 := fun i =>
    ZMod.val_cast_of_lt (by omega)
  have hyv : ∀ l : Fin (n - 1), (((l : ℕ) : ZMod n)).val = l := fun l =>
    ZMod.val_cast_of_lt (by omega)
  have hf : ∀ i l : Fin (n - 1),
      shiftInd n (((i : ℕ) + 1 : ℕ) : ZMod n) ((l : ℕ) : ZMod n) =
        if i = l then 1 else 0 := by
    intro i l
    simp only [shiftInd, hxv, hyv, add_left_inj, Fin.val_inj]
  refine rank_criterion (shiftInd n) r m (0 : ZMod n)
    (fun i : Fin (n - 1) => (((i : ℕ) + 1 : ℕ) : ZMod n))
    (fun l : Fin (n - 1) => ((l : ℕ) : ZMod n))
    0 1 zero_ne_one ?_ ?_ ?_ j hj G H H₀
  · intro l
    simp [shiftInd, hyv]
  · intro i l
    simp only [hf]; split_ifs <;> simp
  · intro p hp
    have : Fact (1 < p) := ⟨hp.one_lt⟩
    have : (Matrix.of fun i l : Fin (n - 1) =>
        if shiftInd n (((i : ℕ) + 1 : ℕ) : ZMod n) ((l : ℕ) : ZMod n) = 1
        then (1 : ZMod p) else 0) = 1 := by
      ext i l
      simp only [hf, Matrix.of_apply, Matrix.one_apply]
      split_ifs <;> simp_all
    simp only [this, Matrix.rank_one, Fintype.card_fin]
    omega

theorem eqInd_not_sum (n r : ℕ) (hr : r + 2 ≤ n) (m : ℕ)
    (j : ZMod n → ZMod m) (hj : Function.Injective j) (G H : Fin r → ZMod n → ZMod m)
    (H₀ : ZMod n → ZMod m) :
    ¬ ∀ a b, j (eqInd n a b) = H₀ b + ∑ k, G k a * H k b := by
  have : NeZero n := ⟨by omega⟩
  have : Fact (1 < n) := ⟨by omega⟩
  have hv : ∀ i : Fin (n - 1), ((((i : ℕ) + 1 : ℕ) : ZMod n)).val = i + 1 := fun i =>
    ZMod.val_cast_of_lt (by omega)
  have hx : ∀ i l : Fin (n - 1),
      ((((i : ℕ) + 1 : ℕ) : ZMod n) = (((l : ℕ) + 1 : ℕ) : ZMod n)) ↔ i = l := by
    intro i l
    constructor
    · intro h
      have := congrArg ZMod.val h
      rw [hv, hv] at this
      exact Fin.ext (by omega)
    · rintro rfl; rfl
  have h0 : ∀ l : Fin (n - 1), (0 : ZMod n) ≠ (((l : ℕ) + 1 : ℕ) : ZMod n) := by
    intro l h
    have := congrArg ZMod.val h
    rw [hv, ZMod.val_zero] at this
    omega
  have hf : ∀ i l : Fin (n - 1),
      eqInd n (((i : ℕ) + 1 : ℕ) : ZMod n) (((l : ℕ) + 1 : ℕ) : ZMod n) =
        if i = l then 1 else 0 := by
    intro i l
    show (if (((i : ℕ) + 1 : ℕ) : ZMod n) = (((l : ℕ) + 1 : ℕ) : ZMod n) then 1 else 0) = _
    simp only [hx]
  refine rank_criterion (eqInd n) r m
    (0 : ZMod n) (fun i : Fin (n - 1) => (((i : ℕ) + 1 : ℕ) : ZMod n))
    (fun l : Fin (n - 1) => (((l : ℕ) + 1 : ℕ) : ZMod n))
    0 1 zero_ne_one ?_ ?_ ?_ j hj G H H₀
  · intro l
    show (if (0 : ZMod n) = (((l : ℕ) + 1 : ℕ) : ZMod n) then 1 else 0) = 0
    rw [ite_eq_right (h0 l)]
  · intro i l
    simp only [hf]; split_ifs <;> simp
  · intro p hp
    have : Fact (1 < p) := ⟨hp.one_lt⟩
    have : (Matrix.of fun i l : Fin (n - 1) =>
        if eqInd n (((i : ℕ) + 1 : ℕ) : ZMod n) (((l : ℕ) + 1 : ℕ) : ZMod n) = 1
        then (1 : ZMod p) else 0) = 1 := by
      ext i l
      simp only [hf, Matrix.of_apply, Matrix.one_apply]
      split_ifs <;> simp_all
    simp only [this, Matrix.rank_one, Fintype.card_fin]
    omega

lemma exists_injective_zmod {S : Type*} [Fintype S] (m : ℕ)
    (hm : m = 0 ∨ Fintype.card S ≤ m) : ∃ j : S → ZMod m, Function.Injective j := by
  refine ⟨fun x => ((Fintype.equivFin S x : ℕ) : ZMod m), fun x y hxy => ?_⟩
  have hx := (Fintype.equivFin S x).isLt
  have hy := (Fintype.equivFin S y).isLt
  rw [ZMod.natCast_eq_natCast_iff'] at hxy
  rcases hm with rfl | hm
  · simpa [Fin.val_inj] using hxy
  · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hxy
    exact (Fintype.equivFin S).injective (Fin.ext hxy)

theorem separable_card {S : Type*} [Fintype S] [DecidableEq S] (f : S → S → S) (m : ℕ)
    (hm : m = 0 ∨ Fintype.card S ≤ m) : RepresentedSeparable m (Fintype.card S) f := by
  obtain ⟨j, hj⟩ := exists_injective_zmod (S := S) m hm
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨j, fun _ _ => 0, fun _ _ => 0, hj, fun x => isEmptyElim x⟩
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨j, fun k a => if a = j (e k) then 1 else 0,
    fun k b => j (f (e k) (Function.invFun j b)), hj, fun x y => ?_⟩
  rw [Finset.sum_eq_single (e.symm x)]
  · simp [Function.leftInverse_invFun hj y]
  · intro k _ hk
    have hne : j x ≠ j (e k) := fun h' => hk (by rw [hj h', Equiv.symm_apply_apply])
    simp [hne]
  · simp

theorem shiftInd_not_separable (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    ¬ RepresentedSeparable m (n - 2) (shiftInd n) := by
  rintro ⟨j, g, h, hj, hrep⟩
  exact shiftInd_not_sum n (n - 2) (by omega) m j hj (fun k a => g k (j a))
    (fun k b => h k (j b)) (fun _ => 0) (fun a b => by simp only [zero_add]; exact hrep a b)

theorem eqInd_not_separable (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    ¬ RepresentedSeparable m (n - 2) (eqInd n) := by
  rintro ⟨j, g, h, hj, hrep⟩
  exact eqInd_not_sum n (n - 2) (by omega) m j hj (fun k a => g k (j a))
    (fun k b => h k (j b)) (fun _ => 0) (fun a b => by simp only [zero_add]; exact hrep a b)

theorem eval_fin2_eq_sum {R : Type*} [CommRing R]
    (q : MvPolynomial (Fin 2) R) (a b : R) :
    MvPolynomial.eval ![a, b] q =
    q.support.sum (fun m => q.coeff m * a ^ (m 0) * b ^ (m 1)) := by
  rw [ MvPolynomial.eval_eq' ];
  simp +decide [ mul_assoc, Fin.prod_univ_two ]

lemma eval_eq_sum_pow_first {R : Type*} [CommRing R] (N : ℕ) (q : MvPolynomial (Fin 2) R)
    (hq : ∀ s ∈ q.support, s 0 < N) (a b : R) :
    eval ![a, b] q = ∑ k : Fin N, a ^ (k : ℕ) *
      ∑ s ∈ q.support with s 0 = (k : ℕ), q.coeff s * b ^ (s 1) := by
  rw [eval_fin2_eq_sum,
    ← Finset.sum_fiberwise_of_maps_to (g := fun s : Fin 2 →₀ ℕ => s 0)
      (t := Finset.range N) (fun s hs => Finset.mem_range.2 (hq s hs)),
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [(Finset.mem_filter.1 hs).2]
  ring

lemma first_le_of_totalDegree_le {R : Type*} [CommRing R] {q : MvPolynomial (Fin 2) R} {D : ℕ}
    (hq : q.totalDegree ≤ D) : ∀ s ∈ q.support, s 0 < D + 1 := by
  intro s hs
  have h := le_totalDegree hs
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at h
  omega

theorem shiftInd_not_lowDegree (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (j : ZMod n → ZMod m)
    (q : MvPolynomial (Fin 2) (ZMod m)) (hq : q.totalDegree ≤ n - 2) :
    ¬ IsBinaryEmbedding (shiftInd n) j q := by
  rintro ⟨hj, h⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  have hs := first_le_of_totalDegree_le hq
  set qk : Fin (r + 1) → ZMod m → ZMod m :=
    fun k b => ∑ s ∈ q.support with s 0 = (k : ℕ), q.coeff s * b ^ (s 1)
  refine shiftInd_not_sum (r + 2) r le_rfl m j hj (fun k a => j a ^ ((k : ℕ) + 1))
    (fun k b => qk k.succ (j b)) (fun b => qk 0 (j b)) fun a b => ?_
  rw [h a b, eval_eq_sum_pow_first (r + 1) q (by simpa using hs), Fin.sum_univ_succ]
  simp [qk]

theorem eqInd_not_lowDegree (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (j : ZMod n → ZMod m)
    (q : MvPolynomial (Fin 2) (ZMod m)) (hq : q.totalDegree ≤ n - 2) :
    ¬ IsBinaryEmbedding (eqInd n) j q := by
  rintro ⟨hj, h⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  have hs := first_le_of_totalDegree_le hq
  set qk : Fin (r + 1) → ZMod m → ZMod m :=
    fun k b => ∑ s ∈ q.support with s 0 = (k : ℕ), q.coeff s * b ^ (s 1)
  refine eqInd_not_sum (r + 2) r le_rfl m j hj (fun k a => j a ^ ((k : ℕ) + 1))
    (fun k b => qk k.succ (j b)) (fun b => qk 0 (j b)) fun a b => ?_
  rw [h a b, eval_eq_sum_pow_first (r + 1) q (by simpa using hs), Fin.sum_univ_succ]
  simp [qk]

end HomBin
