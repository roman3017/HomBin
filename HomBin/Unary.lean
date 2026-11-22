module

public import HomBin.Defs

@[expose] public section

open scoped BigOperators
open Matrix Polynomial

namespace HomBin

def Sidon {S R : Type*} [AddGroup R] (φ : S → R) : Prop :=
  ∀ x y x' y' : S, x ≠ y → x' ≠ y' → φ x - φ y = φ x' - φ y' → x = x' ∧ y = y'

theorem Sidon.injective {S R : Type*} [AddGroup R] {j : S → R} (h : Sidon j) :
    Function.Injective j := by
  intro x y hxy
  by_contra hne
  exact hne (h x y y x hne (fun e => hne e.symm) (by rw [hxy])).1

lemma sidon_pow_two {i i' l l' : ℕ} (hab : i ≠ i') (hcd : l ≠ l')
    (h : (2 : ℤ) ^ i - 2 ^ i' = 2 ^ l - 2 ^ l') : i = l ∧ i' = l' := by
  suffices h_symm : ∀ {i i' : ℕ}, i > i' → ∀ {l l' : ℕ}, l > l' → (2^i - 2^i' = 2^l - 2^l') → (i = l ∧ i' = l') by
    cases lt_or_gt_of_ne hab <;> cases lt_or_gt_of_ne hcd;
    · grind;
    · linarith [ pow_lt_pow_right₀ ( by decide : 1 < 2 ) ‹i < i'›, pow_lt_pow_right₀ ( by decide : 1 < 2 ) ‹l' < l› ];
    · linarith [ pow_lt_pow_right₀ ( show 1 < 2 by decide ) ‹i' < i›, pow_lt_pow_right₀ ( show 1 < 2 by decide ) ‹l < l'› ];
    · grind;
  intros i i' hab l l' hcd h_eq
  have h_factor : 2^i' * (2^(i-i') - 1) = 2^l' * (2^(l-l') - 1) := by
    simp +decide [ mul_tsub, ← pow_add, add_tsub_cancel_of_le hab.le, add_tsub_cancel_of_le hcd.le, h_eq ];
  have h_b_eq_d : i' = l' := by
    have hodd : ∀ k : ℕ, 0 < k → ¬ 2 ∣ 2 ^ k - 1 := by
      intro k hk h2
      have h3 : 2 ∣ 2 ^ k := dvd_pow_self 2 hk.ne'
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    have key : ∀ {i' l' x y : ℕ}, i' < l' → ¬ 2 ∣ x → 2 ^ i' * x ≠ 2 ^ l' * y := by
      intro i' l' x y hbd hx hxy
      obtain ⟨e, rfl⟩ : ∃ e, l' = i' + (e + 1) := ⟨l' - i' - 1, by omega⟩
      rw [pow_add, mul_assoc] at hxy
      have hx' := Nat.eq_of_mul_eq_mul_left (by positivity) hxy
      exact hx ⟨2 ^ e * y, by rw [hx', pow_succ]; ring⟩
    rcases lt_trichotomy i' l' with hbd | hbd | hbd
    · exact absurd h_factor (key hbd (hodd _ (by omega)))
    · exact hbd
    · exact absurd h_factor.symm (key hbd (hodd _ (by omega)))
  cases le_iff_exists_add'.mp hab.le ; cases le_iff_exists_add'.mp hcd.le ; simp_all +decide [ pow_add ];
  zify at * ; simp_all +decide

variable {s : ℕ}

def graphMatrix (f : Fin s → Fin s) : Matrix (Fin s) (Fin s) ℤ :=
  fun i j => if f i = j then 1 else 0

def β (s : ℕ) : Fin s → ℤ := fun i => 2 ^ (i : ℕ)

noncomputable def χ (f : Fin s → Fin s) : Polynomial ℤ := (graphMatrix f).charpoly

noncomputable def w (f : Fin s → Fin s) : Fin s → Polynomial ℤ :=
  fun i => (adjugate (charmatrix (graphMatrix f)) *ᵥ (fun j => Polynomial.C (β s j))) i

lemma graphMatrix_mapC_mulVec (f : Fin s → Fin s) (z : Fin s → Polynomial ℤ) (i : Fin s) :
    ((graphMatrix f).map Polynomial.C *ᵥ z) i = z (f i) := by
  simp +decide [ Matrix.mulVec, dotProduct, graphMatrix ]

lemma χ_monic (f : Fin s → Fin s) : (χ f).Monic :=
  Matrix.charpoly_monic (graphMatrix f)

lemma χ_natDegree (f : Fin s → Fin s) : (χ f).natDegree = s := by
  unfold χ
  rw [Matrix.charpoly_natDegree_eq_dim]
  exact Fintype.card_fin s

lemma w_intertwine (f : Fin s → Fin s) (i : Fin s) :
    w f (f i) = Polynomial.X * w f i - χ f * Polynomial.C (β s i) := by

  have h_def : (charmatrix (graphMatrix f)).mulVec (w f) = χ f • (fun j => Polynomial.C (β s j)) := by
    unfold w χ;
    simp +decide [ Matrix.mulVec_mulVec, Matrix.mul_adjugate ];
    ext; simp +decide [ Matrix.smul_eq_diagonal_mul ] ;
    exact Or.inl rfl;
  convert congr_arg ( fun x => X * w f i - x i ) h_def using 1
  · simp +decide [ Matrix.mulVec, dotProduct ]
    simp +decide [ Matrix.charmatrix, graphMatrix ]
    simp +decide [ Finset.sum_sub_distrib, sub_mul, Matrix.diagonal ]

lemma adjugate_charmatrix_natDegree_le (f : Fin s → Fin s) (i j : Fin s) :
    (adjugate (charmatrix (graphMatrix f)) i j).natDegree ≤ s - 1 := by
  rcases s with ( _ | s ) <;> simp_all +decide [ Matrix.adjugate_apply, Matrix.det_apply' ];
  refine' le_trans ( Polynomial.natDegree_sum_le _ _ ) ( Finset.sup_le _ );
  intro σ _; refine' le_trans ( Polynomial.natDegree_mul_le .. ) _ ; ring_nf ;
  refine' le_trans ( add_le_add ( Polynomial.natDegree_C _ |> le_of_eq ) ( Polynomial.natDegree_prod_le _ _ ) ) _ ; norm_num;
  refine' le_trans ( Finset.sum_le_sum fun x _ => show Polynomial.natDegree _ ≤ if σ x = j then 0 else 1 from _ ) _;
  · split_ifs <;> simp_all +decide [ Matrix.updateRow_apply ];
    · by_cases hi : i = x <;> aesop;
    · by_cases h : σ x = x <;> simp_all +decide [ Matrix.charmatrix ];
      exact le_trans ( Polynomial.natDegree_sub_le _ _ ) ( by norm_num );
  · norm_num [ Finset.sum_ite ];
    exact Nat.le_of_lt_succ ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.filter_ssubset.mpr ⟨ σ.symm j, by aesop ⟩ ) ) ( by norm_num ) )

lemma w_natDegree_le (f : Fin s → Fin s) (i : Fin s) :
    (w f i).natDegree ≤ s - 1 := by
  unfold w;
  simp +decide only [mulVec, dotProduct];
  refine' le_trans ( Polynomial.natDegree_sum_le _ _ ) ( Finset.sup_le _ );
  exact fun j _ => le_trans ( Polynomial.natDegree_mul_le .. ) ( by simp [ adjugate_charmatrix_natDegree_le ] )

lemma w_coeff (f : Fin s → Fin s) (hn : 1 ≤ s) (i : Fin s) :
    (w f i).coeff (s - 1) = β s i := by

  have h_coeff : (X * w f i).coeff s - (χ f * Polynomial.C (β s i)).coeff s = (w f (f i)).coeff s := by
    rw [ ← Polynomial.coeff_sub, ← w_intertwine ];
  rcases s <;> simp_all +decide [ sub_eq_iff_eq_add ];
  rw [ show (χ f).coeff ( _ + 1 ) = 1 from ?_ ];
  · rw [ Polynomial.coeff_eq_zero_of_natDegree_lt ] <;> norm_num;
    exact Nat.le_of_lt_succ ( Nat.lt_succ_of_le ( w_natDegree_le _ _ ) );
  · convert χ_monic f |> Polynomial.Monic.coeff_natDegree using 1;
    rw [ χ_natDegree ]

lemma wdiff_natDegree_lt (f : Fin s → Fin s) (hn : 1 ≤ s) (x y x' y' : Fin s) :
    (w f x - w f y - (w f x' - w f y')).natDegree < s := by
  refine' lt_of_le_of_lt ( Polynomial.natDegree_sub_le _ _ ) ( max_lt _ _ ); all_goals exact lt_of_le_of_lt ( Polynomial.natDegree_sub_le _ _ ) ( max_lt ( lt_of_le_of_lt ( w_natDegree_le _ _ ) ( Nat.pred_lt ( ne_bot_of_gt hn ) ) ) ( lt_of_le_of_lt ( w_natDegree_le _ _ ) ( Nat.pred_lt ( ne_bot_of_gt hn ) ) ) )

lemma wdiff_ne_zero (f : Fin s → Fin s) (hn : 2 ≤ s) (x y x' y' : Fin s)
    (hxy : x ≠ y) (hxy' : x' ≠ y') (hne : (x, y) ≠ (x', y')) :
    (w f x - w f y - (w f x' - w f y')) ≠ 0 := by
  by_contra h_contra
  have h_coeff : (w f x - w f y - (w f x' - w f y')).coeff (s - 1) ≠ 0 := by
    simp_all +decide [ sub_eq_zero ];
    apply_fun fun p => p.coeff ( s - 1 ) at h_contra;
    simp_all +decide [ w_coeff ( f := f ) ( by linarith ) ];
    have := sidon_pow_two ( show ( x : ℕ ) ≠ y from by simpa [ Fin.ext_iff ] using hxy ) ( show ( x' : ℕ ) ≠ y' from by simpa [ Fin.ext_iff ] using hxy' ) ( by simpa [ β ] using h_contra ) ; simp_all +decide [ Fin.ext_iff ] ;
  aesop

lemma eventually_eval_pos (p : Polynomial ℤ) (hlc : 0 < p.leadingCoeff) :
    ∀ᶠ X : ℤ in Filter.atTop, 0 < p.eval X := by
  by_cases h_deg : p.natDegree = 0;
  · simp_all +decide [ Polynomial.eval_eq_sum_range ];
    exact ⟨ 0, fun _ _ => by rw [ Polynomial.leadingCoeff, h_deg ] at hlc; exact hlc ⟩;
  ·
    have h_tendsto : Filter.Tendsto (fun x : ℝ => (p.map (algebraMap ℤ ℝ)).eval x) Filter.atTop Filter.atTop := by
      rw [ Polynomial.tendsto_atTop_iff_leadingCoeff_nonneg ];
      rw [ Polynomial.degree_map_eq_of_leadingCoeff_ne_zero, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero ] <;> norm_num [ hlc.ne', h_deg ];
      exact ⟨ Polynomial.natDegree_pos_iff_degree_pos.mp ( Nat.pos_of_ne_zero h_deg ), le_of_lt hlc ⟩;
    have h_tendsto_int : Filter.Tendsto (fun X : ℤ => (p.map (algebraMap ℤ ℝ)).eval (X : ℝ)) Filter.atTop Filter.atTop := by
      exact h_tendsto.comp tendsto_intCast_atTop_atTop;
    filter_upwards [ h_tendsto_int.eventually_gt_atTop 0 ] with X hX using by simpa [ Polynomial.eval_map ] using hX;

lemma exists_good_t₀ (s : ℕ) (hn : 2 ≤ s) (f : Fin s → Fin s) (d₀ : ℕ) :
    ∃ X : ℤ, (d₀ : ℤ) ≤ X ∧ (2 : ℤ) ≤ X ∧ 0 < (χ f).eval X ∧
      ∀ x y x' y' : Fin s, x ≠ y → x' ≠ y' → (x, y) ≠ (x', y') →
        (w f x - w f y - (w f x' - w f y')).eval X ≠ 0 ∧
        |(w f x - w f y - (w f x' - w f y')).eval X| < (χ f).eval X := by

  have h_eventually_pos : ∀ p : Polynomial ℤ, 0 < p.leadingCoeff → ∀ᶠ X : ℤ in Filter.atTop, 0 < p.eval X :=
    eventually_eval_pos
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : ℤ, ∀ x y x' y' : Fin s, x ≠ y → x' ≠ y' → (x, y) ≠ (x', y') → ∀ᶠ X : ℤ in Filter.atTop, 0 < (χ f - (w f x - w f y - (w f x' - w f y'))).eval X ∧ 0 < (χ f + (w f x - w f y - (w f x' - w f y'))).eval X ∧ 0 < ((w f x - w f y - (w f x' - w f y'))^2).eval X := by
    have h_leading_coeff : ∀ x y x' y' : Fin s, x ≠ y → x' ≠ y' → (x, y) ≠ (x', y') → Polynomial.leadingCoeff (χ f - (w f x - w f y - (w f x' - w f y'))) = 1 ∧ Polynomial.leadingCoeff (χ f + (w f x - w f y - (w f x' - w f y'))) = 1 ∧ 0 < Polynomial.leadingCoeff ((w f x - w f y - (w f x' - w f y'))^2) := by
      intros x y x' y' hxy hxy' hne
      have h_deg : Polynomial.degree (w f x - w f y - (w f x' - w f y')) < Polynomial.degree (χ f) := by
        refine' lt_of_le_of_lt ( Polynomial.degree_le_natDegree ) _;
        rw [ Polynomial.degree_eq_natDegree ] <;> norm_cast;
        · rw [ χ_natDegree ] ; exact wdiff_natDegree_lt f ( by linarith ) x y x' y';
        · exact Polynomial.Monic.ne_zero ( χ_monic f );
      refine' ⟨ _, _, _ ⟩;
      · rw [ Polynomial.leadingCoeff_sub_of_degree_lt ] <;> norm_num [ χ_monic ];
        exact h_deg;
      · rw [ add_comm, Polynomial.leadingCoeff_add_of_degree_lt ];
        · exact χ_monic f;
        · exact h_deg;
      · simp +zetaDelta at *;
        exact sq_pos_of_ne_zero ( Polynomial.leadingCoeff_ne_zero.mpr <| by exact fun h => by have := wdiff_ne_zero f hn x y x' y' hxy hxy' ( by aesop ) ; aesop );
    exact ⟨ 0, fun x y x' y' hxy hxy' hne => by filter_upwards [ h_eventually_pos _ ( h_leading_coeff x y x' y' hxy hxy' hne |>.1.symm ▸ zero_lt_one ), h_eventually_pos _ ( h_leading_coeff x y x' y' hxy hxy' hne |>.2.1.symm ▸ zero_lt_one ), h_eventually_pos _ ( h_leading_coeff x y x' y' hxy hxy' hne |>.2.2 ) ] with X hX₁ hX₂ hX₃ using ⟨ hX₁, hX₂, hX₃ ⟩ ⟩;
  obtain ⟨X₂, hX₂⟩ : ∃ X₂ : ℤ, ∀ x y x' y' : Fin s, x ≠ y → x' ≠ y' → (x, y) ≠ (x', y') → ∀ X : ℤ, X ≥ X₂ → 0 < (χ f - (w f x - w f y - (w f x' - w f y'))).eval X ∧ 0 < (χ f + (w f x - w f y - (w f x' - w f y'))).eval X ∧ 0 < ((w f x - w f y - (w f x' - w f y'))^2).eval X := by
    choose! X₂ hX₂ using fun x y x' y' hxy hxy' hne => Filter.eventually_atTop.mp ( hX₁ x y x' y' hxy hxy' hne );
    use sSup (Set.range (fun p : Fin s × Fin s × Fin s × Fin s => X₂ p.1 p.2.1 p.2.2.1 p.2.2.2));
    exact fun x y x' y' hxy hxy' hne X hX => hX₂ x y x' y' hxy hxy' hne X <| le_trans ( le_csSup ( Set.finite_range _ |> Set.Finite.bddAbove ) <| Set.mem_range_self ( x, y, x', y' ) ) hX;
  obtain ⟨X₃, hX₃⟩ : ∃ X₃ : ℤ, ∀ X : ℤ, X ≥ X₃ → 0 < (χ f).eval X := by
    exact Filter.eventually_atTop.mp ( h_eventually_pos _ ( by rw [ χ_monic f |> Polynomial.Monic.leadingCoeff ] ; norm_num ) );
  refine' ⟨ Max.max ( Max.max ( X₂ : ℤ ) X₃ ) ( Max.max ( d₀ : ℤ ) 2 ), _, _, _, _ ⟩ <;> norm_num;
  · exact hX₃ _ ( le_max_of_le_right ( le_max_left _ _ ) );
  · intro x y x' y' hxy hxy' hne; specialize hX₂ x y x' y' hxy hxy' ( by aesop ) ( Max.max X₂ ( Max.max X₃ ( Max.max ( d₀ : ℤ ) 2 ) ) ) ( le_max_left _ _ ) ; simp_all +decide [ abs_lt ] ;
    exact ⟨ by rintro h; norm_num [ h ] at hX₂, by linarith ⟩

lemma construction (s : ℕ) (f : Fin s → Fin s) (d₀ : ℕ) :
    ∃ (n : ℕ) (_ : 0 < n) (d : ℕ) (j : Fin s → ZMod n),
      d₀ ≤ d ∧ 2 ≤ d ∧ Function.Injective j ∧
      (∀ i, j (f i) = (d : ZMod n) * j i) ∧
      (∀ i i' k k', i ≠ k → i' ≠ k' → j i - j k = j i' - j k' → i = i' ∧ k = k') := by
  rcases s with ( _ | _ | s ) <;> norm_num at *;
  · exact ⟨ 1, by norm_num, d₀ + 2, by linarith, by linarith, by simp +decide ⟩;
  · refine' ⟨ 1, by norm_num, d₀ + 2, by linarith, by linarith, fun _ => 0, _, _, _ ⟩ <;> simp +decide;
  ·
    obtain ⟨X, hX⟩ := exists_good_t₀ (s + 1 + 1) (by linarith) f d₀
    set M := (χ f).eval X
    set n := M.toNat
    have hN_pos : 0 < n := by
      grind
    have hN : (n : ℤ) = M := by
      grind
    generalize_proofs at *; (
    refine' ⟨ n, hN_pos, X.toNat, _, _, fun i => ( w f i |> Polynomial.eval X |> Int.cast : ZMod n ), _, _, _ ⟩ <;> norm_num at *;
    · linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ X ) ];
    · linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ X ) ];
    · intro i j hij; have := hX.2.2.2 i j j i; simp_all +decide [ sub_eq_iff_eq_add ] ;
      contrapose! hij; simp_all +decide [ ZMod.intCast_eq_intCast_iff' ] ;
      intro H; have := hX.2.2.2 i j j i; simp_all +decide [ Int.emod_eq_emod_iff_emod_sub_eq_zero ] ;
      have := hX.2.2.2 i j j i hij ( by tauto ) ; simp_all +decide [ abs_lt ] ;
      obtain ⟨ k, hk ⟩ := H; exact this.1 ( by nlinarith [ show k = 0 by nlinarith ] ) ;
    ·
      intro i
      have h_eval : (w f (f i)).eval X = X * (w f i).eval X - M * (β (s + 1 + 1) i) := by
        have := w_intertwine f i; replace := congr_arg ( Polynomial.eval X ) this; norm_num at * ; linarith;
      generalize_proofs at *; (
      simp_all +decide;
      norm_cast ; simp +decide [ Int.toNat_of_nonneg ( by linarith : 0 ≤ X ) ];
      norm_num [ ← hN ]);
    ·
      intro i i' k k' hi hk h; have := hX.2.2.2 i k i' k' hi hk; simp_all +decide [ sub_eq_iff_eq_add ] ;
      by_cases h_cases : (i, k) = (i', k') <;> simp_all +decide;
      have h_div : (n : ℤ) ∣ (eval X (w f i) - eval X (w f k) - (eval X (w f i') - eval X (w f k'))) := by
        erw [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ; aesop;
      generalize_proofs at *; (
      have := hX.2.2.2 i k i' k' hi hk; simp_all +decide [ abs_lt ] ;
      exact False.elim <| hX.2.2.2 i k i' k' hi hk ( by tauto ) |>.1 <| by obtain ⟨ a, ha ⟩ := h_div; nlinarith [ show a = 0 by nlinarith [ hX.2.2.2 i k i' k' hi hk ( by tauto ) ] ] ;))

lemma sidon_representation (s : ℕ) (f : Fin s → Fin s) (d₀ : ℕ) :
    ∃ (n : ℕ) (_ : 0 < n) (d : ℕ) (φ : Fin s → ZMod n),
      d₀ ≤ d ∧ Sidon φ ∧ ∀ i, φ (f i) = (d : ZMod n) * φ i := by
  obtain ⟨n, hN, d, j, hDd, _, _, hdelta, hdiff⟩ := construction s f d₀
  exact ⟨n, hN, d, j, hDd, fun x y x' y' hxy hxy' h => hdiff x x' y y' hxy hxy' h, hdelta⟩

theorem unary_linear {S : Type*} [Fintype S] (f : S → S) :
    ∃ (m : ℕ) (_ : 0 < m) (c : ZMod m) (j : S → ZMod m),
      IsEmbedding (fun x : Fin 1 → S => f (x 0)) j (MvPolynomial.C c * MvPolynomial.X 0) := by
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  obtain ⟨m, hm, d, φ, _, hφ, hfφ⟩ :=
    sidon_representation (Fintype.card S) (fun i => e (f (e.symm i))) 0
  refine ⟨m, hm, (d : ZMod m), fun x => φ (e x), fun x y hxy => e.injective (hφ.injective hxy),
    fun x => ?_⟩
  simpa using hfφ (e (x 0))

end HomBin
