module

public import HomBin.Separable

@[expose] public section

open MvPolynomial Matrix Finset

namespace HomBin

theorem nilpotent_cancel {R : Type*} [CommRing R] {z t : R}
    (hn : IsNilpotent t) (h : z * (1 + t) = 0) : z = 0 := by
  have hu : IsUnit (1 + t) := hn.isUnit_one_add
  rw [mul_comm] at h
  rwa [IsUnit.mul_right_eq_zero hu] at h

theorem det_mul_eq_zero_of_card_lt {R : Type*} [CommRing R]
    {n m : Type*} [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m]
    (hlt : Fintype.card m < Fintype.card n)
    (A : Matrix n m R) (B : Matrix m n R) :
    (A * B).det = 0 := by
  have h_det : Matrix.det (A * B) = ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ) * ∑ f : n → m,
      (∏ i, A i (f i)) * (∏ i, B (f i) (σ i)) := by
    have h_det : Matrix.det (A * B) = ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ) *
        ∏ i, (∑ k, A i k * B k (σ i)) := by
      rw [Matrix.det_apply']
      refine Finset.sum_bij (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_ <;> simp +decide
      · exact fun b => ⟨b⁻¹, inv_inv b⟩
      · intro σ; rw [← Equiv.prod_comp σ⁻¹]; simp +decide [Matrix.mul_apply]
    simp +decide only [h_det, Finset.prod_sum, ← Finset.prod_mul_distrib]
    refine Finset.sum_congr rfl fun σ _ => congr_arg _ (Finset.sum_bij
      (fun f _ => fun i => f i (Finset.mem_univ i)) ?_ ?_ ?_ ?_) <;> simp +decide
    · simp +decide [funext_iff]
    · exact fun b => ⟨fun i _ => b i, rfl⟩
  have h_exchange : Matrix.det (A * B) = ∑ f : n → m, (∏ i, A i (f i)) *
      ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ) * (∏ i, B (f i) (σ i)) := by
    simp +decide only [h_det, Finset.mul_sum _ _ _, mul_left_comm]
    exact Finset.sum_comm
  have h_inner_det : ∀ f : n → m, ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ) *
      (∏ i, B (f i) (σ i)) = Matrix.det (Matrix.of (fun i j => B (f i) j)) := by
    intro f; rw [Matrix.det_apply']
    refine Finset.sum_bij (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_ <;> simp +decide
    · exact fun b => ⟨b⁻¹, inv_inv b⟩
    · intro σ; rw [← Equiv.prod_comp σ.symm]; simp +decide
  have h_noninjective : ∀ f : n → m, ∃ i j : n, i ≠ j ∧ f i = f j := by
    exact fun f => not_forall_not.mp fun h => hlt.not_ge <|
      Fintype.card_le_of_injective f fun i j hij =>
        Classical.not_not.1 fun hi => h i <| by tauto
  rw [h_exchange, Finset.sum_eq_zero]
  intro f _; obtain ⟨i, j, hij, h⟩ := h_noninjective f
  rw [h_inner_det f, Matrix.det_zero_of_row_eq hij]
  · simp
  · exact funext fun k => by simp +decide [h]

theorem nilpotent_eq_zero {R : Type*} [CommRing R] {δ e : R} {k : ℕ}
    (hdelta : δ ^ 2 * e = δ)
    (hnil : δ ^ k = 0) :
    δ = 0 := by
  have h_eq : δ * (1 - δ * e) = 0 := by linear_combination -hdelta
  set t : R := -δ * e
  have h_t : δ * (1 + t) = 0 := by grind
  have h_t_nil : t ^ k = 0 := by rw [mul_pow, neg_pow, hnil]; norm_num
  exact nilpotent_cancel ⟨k, h_t_nil⟩ h_t

theorem det_nilpotent {R : Type*} [CommRing R]
    {n m : Type*} [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m]
    (hlt : Fintype.card m < Fintype.card n)
    {Φ : Matrix n m R} {Q : Matrix m m R}
    {D F : Matrix n n R} {δ : R}
    (hmat : D * (Φ * Q * Φᵀ) * D = δ • F)
    (hdet_F : IsUnit F.det) :
    δ ^ Fintype.card n = 0 := by
  apply_fun Matrix.det at hmat;
  simp_all +decide [Matrix.det_mul];
  rw [ ← hdet_F.mul_left_inj ];
  rw [ ← hmat, det_mul_eq_zero_of_card_lt hlt ] ; ring

noncomputable section

def σ {R : Type*} [CommRing R] (u₀ u₁ : R) (k : ℕ) : R :=
  ∑ i ∈ Finset.range k, u₁ ^ i * u₀ ^ (k - 1 - i)

theorem pow_sub_eq_mul_σ {R : Type*} [CommRing R] (u₀ u₁ : R) (k : ℕ) :
    u₁ ^ k - u₀ ^ k = (u₁ - u₀) * σ u₀ u₁ k := by
  unfold σ
  rw [mul_comm]
  exact (geom_sum₂_mul u₁ u₀ k).symm

theorem eval_mixed_diff_eq {R : Type*} [CommRing R]
    (q : MvPolynomial (Fin 2) R) (u₀ u₁ v₀ v₁ : R) :
    MvPolynomial.eval ![u₁, v₁] q - MvPolynomial.eval ![u₀, v₁] q -
    MvPolynomial.eval ![u₁, v₀] q + MvPolynomial.eval ![u₀, v₀] q =
    q.support.sum (fun m =>
      q.coeff m * (u₁ ^ (m 0) - u₀ ^ (m 0)) * (v₁ ^ (m 1) - v₀ ^ (m 1))) := by
  rw [ eval_fin2_eq_sum, eval_fin2_eq_sum, eval_fin2_eq_sum, eval_fin2_eq_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib ]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem eval_mixed_diff_factored {R : Type*} [CommRing R]
    (q : MvPolynomial (Fin 2) R) (u₀ u₁ v₀ v₁ : R) :
    MvPolynomial.eval ![u₁, v₁] q - MvPolynomial.eval ![u₀, v₁] q -
    MvPolynomial.eval ![u₁, v₀] q + MvPolynomial.eval ![u₀, v₀] q =
    (u₁ - u₀) * (v₁ - v₀) *
    q.support.sum (fun m =>
      q.coeff m * σ u₀ u₁ (m 0) * σ v₀ v₁ (m 1)) := by
  rw [ eval_mixed_diff_eq ];
  simp +decide only [mul_assoc, mul_comm, mul_left_comm, mul_sum];
  exact Finset.sum_congr rfl fun x hx => by rw [ pow_sub_eq_mul_σ u₀ u₁ ( x 0 ), pow_sub_eq_mul_σ v₀ v₁ ( x 1 ) ] ; ring;

theorem mixed_difference {R : Type*} [CommRing R]
    {N : ℕ} (q : MvPolynomial (Fin 2) R) (hdeg : q.totalDegree ≤ N + 1) (u₀ u₁ v₀ v₁ : R) :
    MvPolynomial.eval ![u₁, v₁] q - MvPolynomial.eval ![u₀, v₁] q -
    MvPolynomial.eval ![u₁, v₀] q + MvPolynomial.eval ![u₀, v₀] q =
    (u₁ - u₀) * (v₁ - v₀) *
    ∑ k₁ : Fin N, ∑ k₂ : Fin N,
      q.coeff (Finsupp.single 0 (k₁.val + 1) + Finsupp.single 1 (k₂.val + 1)) *
      σ u₀ u₁ (k₁.val + 1) * σ v₀ v₁ (k₂.val + 1) := by
  rw [ eval_mixed_diff_factored ];
  have h_sum : ∑ m ∈ q.support, q.coeff m * σ u₀ u₁ (m 0) * σ v₀ v₁ (m 1) = ∑ m ∈ Finset.filter (fun m => m 0 > 0 ∧ m 1 > 0) q.support, q.coeff m * σ u₀ u₁ (m 0) * σ v₀ v₁ (m 1) := by
    rw [ Finset.sum_filter_of_ne ];
    intro m hm h; constructor <;> contrapose! h <;> simp_all +decide [ σ ] ;
  rw [ h_sum, Finset.sum_subset ( show q.support.filter ( fun m => m 0 > 0 ∧ m 1 > 0 ) ⊆ Finset.image ( fun k : Fin N × Fin N => Finsupp.single 0 ( k.1.val + 1 ) + Finsupp.single 1 ( k.2.val + 1 ) ) ( Finset.univ ) from ?_ ) ];
  · rw [ Finset.sum_image ] <;> simp +decide;
    · rw [ Finset.sum_sigma' ];
      refine' congr_arg _ ( Finset.sum_bij ( fun x _ => ⟨ ⟨ x.1, by
        exact x.1.2 ⟩, ⟨ x.2, by
        exact x.2.2 ⟩ ⟩ ) _ _ _ _ ) <;> simp +decide;
    · intro k l hkl; replace hkl := congr_arg ( fun f => ( f 0, f 1 ) ) hkl; aesop;
  · aesop;
  · intro m hm; simp_all +decide [ Finsupp.ext_iff, Fin.forall_fin_two ] ;
    have h_deg : m 0 + m 1 ≤ N + 1 := by
      have h_sum : m.sum (fun _ e => e) ≤ N + 1 :=
        le_trans ( Finset.le_sup ( f := fun s => s.sum fun x e => e ) ( Finsupp.mem_support_iff.mpr hm.1 ) ) hdeg
      have h_eq : m.sum (fun _ e => e) = m 0 + m 1 :=
        (Finsupp.sum_fintype m (fun _ e => e) fun _ => rfl).trans (Fin.sum_univ_two (fun i => m i))
      rw [h_eq] at h_sum; exact h_sum
    exact ⟨ ⟨ ⟨ m 0 - 1, by omega ⟩, by simp +decide [ Nat.sub_add_cancel hm.2.1 ] ⟩, ⟨ ⟨ m 1 - 1, by omega ⟩, by simp +decide [ Nat.sub_add_cancel hm.2.2 ] ⟩ ⟩

theorem invInd_not_lowDegree {R : Type*} [CommRing R] (p : ℕ) (hp : p.Prime)
    (j : ZMod p → R) (q : MvPolynomial (Fin 2) R) (hdeg : q.totalDegree ≤ p - 1) :
    ¬ IsBinaryEmbedding (invInd p) j q := by
  rintro ⟨hj, hemb⟩
  have heval : ∀ x y : ZMod p,
      MvPolynomial.eval ![j x, j y] q = j (if x * y = 1 then 1 else 0) :=
    fun x y => (hemb x y).symm
  have := Fact.mk hp
  have hp2 := hp.two_le
  have hdeg' : q.totalDegree ≤ (p - 2) + 1 := by omega
  obtain ⟨e, he⟩ : ∃ e : (ZMod p)ˣ → (ZMod p)ˣ → R, ∀ x y, e x y =
      ∑ k₁ : Fin (p - 2), ∑ k₂ : Fin (p - 2),
        q.coeff (Finsupp.single 0 (k₁.val + 1) + Finsupp.single 1 (k₂.val + 1)) *
        σ (j 0) (j x) (k₁.val + 1) * σ (j 0) (j y) (k₂.val + 1) :=
    ⟨_, fun _ _ => rfl⟩
  have hentry : ∀ x y : (ZMod p)ˣ, (j x - j 0) * (j y - j 0) * e x y =
      (j 1 - j 0) * (if (x : ZMod p) * y = 1 then 1 else 0) := by
    intro x y
    have h := mixed_difference q hdeg' (j 0) (j x) (j 0) (j y)
    rw [heval, heval, heval, heval, ← he] at h
    simp only [zero_mul, mul_zero, zero_ne_one, ite_false] at h
    by_cases hxy : (x : ZMod p) * y = 1
    · rw [ite_eq_left hxy] at h ⊢
      linear_combination (-1 : R) * h
    · rw [ite_eq_right hxy] at h ⊢
      linear_combination (-1 : R) * h
  have hmat : Matrix.diagonal (fun x : (ZMod p)ˣ => j x - j 0) *
      ((Matrix.of fun (x : (ZMod p)ˣ) (k : Fin (p - 2)) => σ (j 0) (j x) (k.val + 1)) *
        (Matrix.of fun (k₁ k₂ : Fin (p - 2)) =>
          q.coeff (Finsupp.single 0 (k₁.val + 1) + Finsupp.single 1 (k₂.val + 1))) *
        (Matrix.of fun (x : (ZMod p)ˣ) (k : Fin (p - 2)) =>
          σ (j 0) (j x) (k.val + 1))ᵀ) *
      Matrix.diagonal (fun x : (ZMod p)ˣ => j x - j 0) =
      (j 1 - j 0) • (Equiv.inv (ZMod p)ˣ).permMatrix R := by
    ext x y
    have hM : ((Matrix.of fun (x : (ZMod p)ˣ) (k : Fin (p - 2)) =>
          σ (j 0) (j x) (k.val + 1)) *
        (Matrix.of fun (k₁ k₂ : Fin (p - 2)) =>
          q.coeff (Finsupp.single 0 (k₁.val + 1) + Finsupp.single 1 (k₂.val + 1))) *
        (Matrix.of fun (x : (ZMod p)ˣ) (k : Fin (p - 2)) =>
          σ (j 0) (j x) (k.val + 1))ᵀ) x y = e x y := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul, he]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have hcond : ((x : ZMod p) * y = 1) ↔ x⁻¹ = y := by
      rw [← Units.val_mul, ← Units.val_one, Units.val_inj, mul_eq_one_iff_inv_eq]
    have h := hentry x y
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some_inj,
      Equiv.inv_apply, hM, smul_eq_mul]
    by_cases hxy : x⁻¹ = y
    · rw [ite_eq_left (hcond.2 hxy)] at h
      rw [ite_eq_left hxy]
      linear_combination h
    · rw [ite_eq_right (fun h' => hxy (hcond.1 h'))] at h
      rw [ite_eq_right hxy]
      linear_combination h
  have hdet : IsUnit ((Equiv.inv (ZMod p)ˣ).permMatrix R).det := by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.inv (ZMod p)ˣ)) with h | h <;>
      simp [h]
  have hcard : Fintype.card (Fin (p - 2)) < Fintype.card (ZMod p)ˣ := by
    rw [Fintype.card_fin, ZMod.card_units p]
    omega
  have hnil := det_nilpotent hcard hmat hdet
  have hdelta : (j 1 - j 0) ^ 2 * e 1 1 = j 1 - j 0 := by
    have h := hentry 1 1
    simp only [Units.val_one, mul_one, ite_true] at h
    linear_combination h
  have h10 := nilpotent_eq_zero hdelta hnil
  exact one_ne_zero (hj (sub_eq_zero.mp h10))
end

end HomBin
