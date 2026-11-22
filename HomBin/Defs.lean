module

public import Mathlib

@[expose] public section

namespace HomBin

open MvPolynomial

def IsBinaryEmbedding {S R : Type*} [CommRing R] (f : S → S → S) (j : S → R)
    (q : MvPolynomial (Fin 2) R) : Prop :=
  Function.Injective j ∧ ∀ x y, j (f x y) = eval ![j x, j y] q

def IsEmbedding {S R : Type*} [CommRing R] {k : ℕ} (f : (Fin k → S) → S) (j : S → R)
    (q : MvPolynomial (Fin k) R) : Prop :=
  Function.Injective j ∧ ∀ x, j (f x) = eval (j ∘ x) q

theorem isBinaryEmbedding_iff {S R : Type*} [CommRing R] (f : S → S → S) (j : S → R)
    (q : MvPolynomial (Fin 2) R) :
    IsBinaryEmbedding f j q ↔ IsEmbedding (fun x => f (x 0) (x 1)) j q := by
  refine and_congr_right fun _ => ⟨fun h x => ?_, fun h x y => ?_⟩
  · have hx : j ∘ x = ![j (x 0), j (x 1)] := by
      funext i; fin_cases i <;> rfl
    rw [hx]; exact h _ _
  · have hx : j ∘ ![x, y] = ![j x, j y] := by
      funext i; fin_cases i <;> rfl
    have := h ![x, y]
    rw [hx] at this
    exact this

def RepresentedSeparable {S : Type*} (m r : ℕ) (f : S → S → S) : Prop :=
  ∃ (j : S → ZMod m) (g h : Fin r → ZMod m → ZMod m),
    Function.Injective j ∧ ∀ x y, j (f x y) = ∑ k, g k (j x) * h k (j y)

def shiftInd (n : ℕ) (x y : ZMod n) : ZMod n := if x.val = y.val + 1 then 1 else 0

def eqInd (n : ℕ) (x y : ZMod n) : ZMod n := if x = y then 1 else 0

def invInd (n : ℕ) (x y : ZMod n) : ZMod n := if x * y = 1 then 1 else 0

end HomBin
