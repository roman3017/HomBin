module

public import HomBin.Unary

@[expose] public section

open scoped BigOperators
open Matrix Polynomial

namespace HomBin

lemma exists_unit_orderOf_eq {p : ℕ} [Fact p.Prime] {n : ℕ} (hN : 0 < n) (hdvd : n ∣ p - 1) :
    ∃ h : (ZMod p)ˣ, orderOf h = n := by

  obtain ⟨g, hg⟩ : ∃ g : (ZMod p)ˣ, orderOf g = p - 1 := by
    obtain ⟨ g, hg ⟩ := IsCyclic.exists_generator ( α := ( ZMod p ) ˣ );
    exact ⟨ g, by rw [ orderOf_eq_card_of_forall_mem_zpowers hg ] ; simp +decide [ Nat.totient_prime Fact.out ] ⟩;
  use g ^ ((p - 1) / n);
  rw [ orderOf_pow' ] <;> norm_num [ hg, hdvd ];
  · rw [ Nat.gcd_eq_right ( Nat.div_dvd_of_dvd hdvd ), Nat.div_div_self hdvd ( Nat.sub_ne_zero_of_lt ( Fact.out : p > 1 ) ) ];
  · exact ⟨ hN.ne', Nat.le_of_dvd ( Nat.sub_pos_of_lt ( Fact.out : p > 1 ) ) hdvd ⟩

lemma realization {S : Type*} [Fintype S] [DecidableEq S] (f : S → S) (d₀ : ℕ) :
    ∃ (p : ℕ) (_ : p.Prime) (d : ℕ) (j : S → ZMod p),
      d₀ ≤ d ∧ Function.Injective j ∧ (∀ x, j x ≠ 0) ∧
      (∀ x, j (f x) = (j x) ^ d) ∧
      (∀ x y x' y', x ≠ y → x' ≠ y' → j x * j y' = j x' * j y → x = x' ∧ y = y') := by

  set s := Fintype.card S with hn;

  obtain ⟨n, hN_pos, d, a, hd_ge_D, ha_sidon, ha_delta⟩ := sidon_representation s (fun i => (Fintype.equivFinOfCardEq rfl) (f ((Fintype.equivFinOfCardEq rfl).symm i))) d₀;
  have ha_injective : Function.Injective a := ha_sidon.injective

  obtain ⟨p, hp_prime, hp_mod, hp_gt⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ≡ 1 [MOD n] ∧ p > Finset.univ.sup (fun i => (a i).val) := by
    exact Exists.imp ( by tauto ) ( Nat.exists_prime_gt_modEq_one ( Finset.univ.sup fun i => ( a i |> ZMod.val ) ) hN_pos.ne' );

  obtain ⟨h, hh_order⟩ : ∃ h : (ZMod p)ˣ, orderOf h = n := by
    have h_unit : n ∣ p - 1 := by
      simpa [ ← Int.natCast_dvd_natCast, hp_prime.pos ] using hp_mod.symm.dvd;
    have := Fact.mk hp_prime; exact exists_unit_orderOf_eq hN_pos h_unit;

  refine' ⟨ p, hp_prime, d, fun x => h ^ ( a ( Fintype.equivFinOfCardEq rfl x ) |> ZMod.val ), hd_ge_D, _, _, _, _ ⟩ <;> simp +decide [ Function.Injective ];
  · intro x y hxy
    have h_eq : (a (Fintype.equivFinOfCardEq rfl x)).val ≡ (a (Fintype.equivFinOfCardEq rfl y)).val [MOD n] := by
      have h_exp : h ^ (a (Fintype.equivFinOfCardEq rfl x)).val = h ^ (a (Fintype.equivFinOfCardEq rfl y)).val := by
        exact Units.ext hxy;
      rw [ pow_eq_pow_iff_modEq ] at h_exp;
      rwa [ hh_order ] at h_exp
    generalize_proofs at *; (
    have h_eq : a (Fintype.equivFinOfCardEq rfl x) = a (Fintype.equivFinOfCardEq rfl y) := by
      cases n <;> simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ]
    generalize_proofs at *; (
    exact Fintype.equivFinOfCardEq rfl |>.injective ( ha_injective h_eq )));
  · have := Fact.mk hp_prime; simp +decide ;
  ·

    intro x; specialize ha_delta ( Fintype.equivFinOfCardEq rfl x ) ; simp_all +decide ;
    rw [ ZMod.val_mul ] ; norm_cast ; simp +decide [ pow_mul', hh_order.symm ] ;
  ·

    intro x y x' y' hxy hxy' h_eq
    have h_exp : (a (Fintype.equivFinOfCardEq rfl x)).val + (a (Fintype.equivFinOfCardEq rfl y')).val ≡ (a (Fintype.equivFinOfCardEq rfl x')).val + (a (Fintype.equivFinOfCardEq rfl y)).val [MOD n] := by
      have h_exp : h ^ ((a (Fintype.equivFinOfCardEq rfl x)).val + (a (Fintype.equivFinOfCardEq rfl y')).val) = h ^ ((a (Fintype.equivFinOfCardEq rfl x')).val + (a (Fintype.equivFinOfCardEq rfl y)).val) := by
        simp_all +decide [ pow_add, Units.ext_iff ];
      rw [ pow_eq_pow_iff_modEq ] at h_exp;
      rwa [ hh_order ] at h_exp;
    have h_exp : a (Fintype.equivFinOfCardEq rfl x) - a (Fintype.equivFinOfCardEq rfl y) = a (Fintype.equivFinOfCardEq rfl x') - a (Fintype.equivFinOfCardEq rfl y') := by
      simp +decide [ ← ZMod.natCast_eq_natCast_iff ] at h_exp ⊢;
      cases n <;> simp +decide at * ; linear_combination h_exp;
    specialize ha_sidon ( Fintype.equivFinOfCardEq rfl x ) ( Fintype.equivFinOfCardEq rfl y ) ( Fintype.equivFinOfCardEq rfl x' ) ( Fintype.equivFinOfCardEq rfl y' ) ; aesop

theorem homogeneous {S : Type*} [Fintype S] [DecidableEq S] {k : ℕ} (hk : 0 < k)
    (f : (Fin k → S) → S) :
    ∃ (p : ℕ) (_ : p.Prime) (d : ℕ) (j : S → ZMod p) (q : MvPolynomial (Fin k) (ZMod p)),
      q.IsHomogeneous d ∧ IsEmbedding f j q := by
  classical
  set s := Fintype.card S
  obtain ⟨p, hp, d, j, hd, hj_inj, hj_ne, hj_diag, hj_cross⟩ :=
    realization (fun a => f (fun _ => a)) (s ^ k)
  have := Fact.mk hp
  have hdiag : ∀ a, j (f (fun _ => a)) = j a ^ d := hj_diag
  set i₀ : Fin k := ⟨0, hk⟩
  set P : (Fin k → S) → (Fin k → ZMod p) := fun x i => j (x i) / j (x i₀)
  set V : (Fin k → S) → ZMod p := fun x => j (f x) * (j (x i₀))⁻¹ ^ d
  have hV : ∀ y : Fin k → S, (∀ i, y i = y i₀) → V y = 1 := by
    intro y hy
    have hf : f y = f (fun _ => y i₀) := congrArg f (funext hy)
    simp only [V, hf, hdiag, inv_pow]
    exact mul_inv_cancel₀ (pow_ne_zero _ (hj_ne _))
  have hcoll : ∀ x x', P x = P x' → V x = V x' := by
    intro x x' h
    have hi : ∀ i, j (x i) * j (x' i₀) = j (x' i) * j (x i₀) := by
      intro i
      have := congrFun h i
      simp only [P] at this
      rwa [div_eq_div_iff (hj_ne _) (hj_ne _)] at this
    by_cases h0 : x i₀ = x' i₀
    · have : x = x' := by
        funext i
        have := hi i
        rw [h0] at this
        exact hj_inj (mul_right_cancel₀ (hj_ne _) this)
      rw [this]
    · have hconst : ∀ i, x i = x i₀ ∧ x' i = x' i₀ := by
        intro i
        have hne : x i ≠ x' i := by
          intro he
          have := hi i
          rw [he] at this
          exact h0 (hj_inj (mul_left_cancel₀ (hj_ne _) this).symm)
        exact hj_cross (x i) (x' i) (x i₀) (x' i₀) hne h0 (by linear_combination hi i)
      rw [hV x (fun i => (hconst i).1), hV x' (fun i => (hconst i).2)]
  set T : Finset (Fin k → ZMod p) := Finset.univ.image P
  have hT : T.card ≤ s ^ k := by
    calc T.card ≤ (Finset.univ : Finset (Fin k → S)).card := Finset.card_image_le
      _ = s ^ k := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  set c : (Fin k → ZMod p) → (Fin k → ZMod p) → Fin k := fun a b =>
    if h : a = b then i₀ else Classical.choose (Function.ne_iff.mp h)
  have hc : ∀ a b : Fin k → ZMod p, a ≠ b → a (c a b) ≠ b (c a b) := by
    intro a b h
    simp only [c, dite_eq_right h]
    exact Classical.choose_spec (Function.ne_iff.mp h)
  set L : (Fin k → ZMod p) → (Fin k → ZMod p) → MvPolynomial (Fin k) (ZMod p) := fun a b =>
    (MvPolynomial.X (c a b) - MvPolynomial.C (b (c a b)) * MvPolynomial.X i₀) *
      MvPolynomial.C (a (c a b) - b (c a b))⁻¹
  set B : (Fin k → ZMod p) → MvPolynomial (Fin k) (ZMod p) := fun a => ∏ b ∈ T.erase a, L a b
  set vT : (Fin k → ZMod p) → ZMod p := fun a => if h : ∃ x, P x = a then V h.choose else 0
  have hvT : ∀ x, vT (P x) = V x := by
    intro x
    have h : ∃ y, P y = P x := ⟨x, rfl⟩
    simp only [vT, dite_eq_left h]
    exact hcoll _ _ h.choose_spec
  set q : MvPolynomial (Fin k) (ZMod p) :=
    ∑ a ∈ T, MvPolynomial.C (vT a) * MvPolynomial.X i₀ ^ (d - (T.card - 1)) * B a
  have hL : ∀ a b, (L a b).IsHomogeneous 1 := by
    intro a b
    have h1 : (MvPolynomial.X (c a b) - MvPolynomial.C (b (c a b)) * MvPolynomial.X i₀ :
        MvPolynomial (Fin k) (ZMod p)).IsHomogeneous 1 :=
      (MvPolynomial.isHomogeneous_X _ _).sub (MvPolynomial.isHomogeneous_C_mul_X _ _)
    simpa using h1.mul (MvPolynomial.isHomogeneous_C (Fin k) (a (c a b) - b (c a b))⁻¹)
  have hB : ∀ a ∈ T, (B a).IsHomogeneous (T.card - 1) := by
    intro a ha
    have := MvPolynomial.IsHomogeneous.prod (T.erase a) (L a) (fun _ => 1) (fun b _ => hL a b)
    simpa [Finset.card_erase_of_mem ha] using this
  have hq : q.IsHomogeneous d := by
    apply MvPolynomial.IsHomogeneous.sum
    intro a ha
    have h1 := ((MvPolynomial.isHomogeneous_C (Fin k) (vT a)).mul
      ((MvPolynomial.isHomogeneous_X (ZMod p) i₀).pow (d - (T.card - 1)))).mul (hB a ha)
    convert h1 using 1
    omega
  refine ⟨p, hp, d, j, q, hq, hj_inj, fun x => ?_⟩
  have he : j (x i₀) ≠ 0 := hj_ne _
  have hdiv : ∀ t, j (x i₀) * (t / j (x i₀)) = t := fun t => by field_simp
  have hLev : ∀ a b : Fin k → ZMod p, MvPolynomial.eval (j ∘ x) (L a b) =
      j (x i₀) * (P x (c a b) - b (c a b)) * (a (c a b) - b (c a b))⁻¹ := by
    intro a b
    simp only [L, P, map_mul, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
      Function.comp_apply]
    linear_combination (-(a (c a b) - b (c a b))⁻¹) * hdiv (j (x (c a b)))
  have hPT : P x ∈ T := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hBev : ∀ a ∈ T, MvPolynomial.eval (j ∘ x) (B a) =
      if P x = a then j (x i₀) ^ (T.card - 1) else 0 := by
    intro a ha
    simp only [B, map_prod, hLev]
    split_ifs with hPa
    · rw [Finset.prod_congr rfl (g := fun _ => j (x i₀)) ?_, Finset.prod_const,
        Finset.card_erase_of_mem ha]
      intro b hb
      have hab : a ≠ b := (Finset.ne_of_mem_erase hb).symm
      rw [hPa, mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr (hc a b hab)), mul_one]
    · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hPa, hPT⟩) (by simp)
  simp only [q, map_sum, map_mul, MvPolynomial.eval_C, map_pow, MvPolynomial.eval_X,
    Function.comp_apply]
  rw [Finset.sum_eq_single (P x)]
  · rw [hBev _ hPT, ite_eq_left rfl, hvT]
    have hpow : j (x i₀) ^ (d - (T.card - 1)) * j (x i₀) ^ (T.card - 1) = j (x i₀) ^ d := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    simp only [V]
    rw [mul_assoc, hpow, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ he), mul_one]
  · intro a ha hne
    rw [hBev a ha, ite_eq_right (Ne.symm hne), mul_zero]
  · intro h; exact absurd hPT h

end HomBin
