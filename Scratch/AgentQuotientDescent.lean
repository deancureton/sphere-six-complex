import SphereSixComplex.Periods.EstablishedOrbifoldAffineTorsorDescent
import SphereSixComplex.TriangleGroup.EstablishedFuchsianEllipticStabilizers
import SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
import Mathlib.Topology.ContinuousMap.Basic

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

/-- Local packaging of the normalization repair, independent of the finite-chart construction. -/
def HasCompatibleCuspNormalization
    (P : OrbifoldAffineLineTorsorDescentProblem) : Prop :=
  (∀ z u v, P.cuspNormalize z u - P.cuspNormalize z v = u - v) ∧
    (∀ z u, P.cuspNormalize (fuchsianSourceAction g₀ • z) (P.affineCusp z u) =
      P.cuspNormalize z u)

namespace HasCompatibleCuspNormalization

variable {P : OrbifoldAffineLineTorsorDescentProblem}

theorem normalize_eq_add_zero (h : HasCompatibleCuspNormalization P)
    (z : UpperHalfPlane) (u : ℂ) :
    P.cuspNormalize z u = u + P.cuspNormalize z 0 := by
  have hsub := h.1 z u 0
  linear_combination hsub

theorem normalize_injective (h : HasCompatibleCuspNormalization P)
    (z : UpperHalfPlane) : Function.Injective (P.cuspNormalize z) := by
  intro u v huv
  have hsub := h.1 z u v
  rw [huv] at hsub
  exact sub_eq_zero.mp (by simpa using hsub.symm)

/-- The two normalization laws force the parabolic substitution to be a translation. -/
theorem affineCusp_eq_translation (h : HasCompatibleCuspNormalization P)
    (z : UpperHalfPlane) (u : ℂ) :
    P.affineCusp z u =
      u + P.cuspNormalize z 0 -
        P.cuspNormalize (fuchsianSourceAction g₀ • z) 0 := by
  calc
    P.affineCusp z u =
        P.cuspNormalize (fuchsianSourceAction g₀ • z) (P.affineCusp z u) -
          P.cuspNormalize (fuchsianSourceAction g₀ • z) 0 := by
      symm
      simpa using h.1 (fuchsianSourceAction g₀ • z) (P.affineCusp z u) 0
    _ = P.cuspNormalize z u -
          P.cuspNormalize (fuchsianSourceAction g₀ • z) 0 := by rw [h.2 z u]
    _ = u + P.cuspNormalize z 0 -
          P.cuspNormalize (fuchsianSourceAction g₀ • z) 0 := by
      rw [normalize_eq_add_zero h]

theorem affineCusp_sub (h : HasCompatibleCuspNormalization P)
    (z : UpperHalfPlane) (u v : ℂ) :
    P.affineCusp z u - P.affineCusp z v = u - v := by
  rw [affineCusp_eq_translation h, affineCusp_eq_translation h]
  ring

theorem affineCusp_injective (h : HasCompatibleCuspNormalization P)
    (z : UpperHalfPlane) : Function.Injective (P.affineCusp z) := by
  intro u v huv
  have hsub := affineCusp_sub h z u v
  rw [huv] at hsub
  exact sub_eq_zero.mp (by simpa using hsub.symm)

end HasCompatibleCuspNormalization

namespace QuotientDescent

variable (P : OrbifoldAffineLineTorsorDescentProblem)

theorem affineOne_eq_linear_add (z : UpperHalfPlane) (u : ℂ) :
    P.affineOne z u = P.linearOne z * u + P.affineOne z 0 := by
  have h := P.affineOne_sub z u 0
  linear_combination h

theorem affineTwo_eq_linear_add (z : UpperHalfPlane) (u : ℂ) :
    P.affineTwo z u = P.linearTwo z * u + P.affineTwo z 0 := by
  have h := P.affineTwo_sub z u 0
  linear_combination h

theorem affineOne_injective (z : UpperHalfPlane) : Function.Injective (P.affineOne z) := by
  intro u v huv
  calc
    u = P.affineOne (fuchsianSourceAction (g₁ ^ 2) • z)
          (P.affineOne (fuchsianSourceAction g₁ • z) (P.affineOne z u)) :=
      (P.affineOne_cycle z u).symm
    _ = P.affineOne (fuchsianSourceAction (g₁ ^ 2) • z)
          (P.affineOne (fuchsianSourceAction g₁ • z) (P.affineOne z v)) := by rw [huv]
    _ = v := P.affineOne_cycle z v

theorem affineTwo_injective (z : UpperHalfPlane) : Function.Injective (P.affineTwo z) := by
  intro u v huv
  calc
    u = P.affineTwo (fuchsianSourceAction (g₂ ^ 3) • z)
          (P.affineTwo (fuchsianSourceAction (g₂ ^ 2) • z)
            (P.affineTwo (fuchsianSourceAction g₂ • z) (P.affineTwo z u))) :=
      (P.affineTwo_cycle z u).symm
    _ = P.affineTwo (fuchsianSourceAction (g₂ ^ 3) • z)
          (P.affineTwo (fuchsianSourceAction (g₂ ^ 2) • z)
            (P.affineTwo (fuchsianSourceAction g₂ • z) (P.affineTwo z v))) := by rw [huv]
    _ = v := P.affineTwo_cycle z v

theorem linearOne_ne_zero (z : UpperHalfPlane) : P.linearOne z ≠ 0 := by
  intro hzero
  have heq : P.affineOne z (0 : ℂ) = P.affineOne z 1 := by
    apply sub_eq_zero.mp
    rw [P.affineOne_sub, hzero]
    ring
  exact (zero_ne_one : (0 : ℂ) ≠ 1) (affineOne_injective P z heq)

theorem linearTwo_ne_zero (z : UpperHalfPlane) : P.linearTwo z ≠ 0 := by
  intro hzero
  have heq : P.affineTwo z (0 : ℂ) = P.affineTwo z 1 := by
    apply sub_eq_zero.mp
    rw [P.affineTwo_sub, hzero]
    ring
  exact (zero_ne_one : (0 : ℂ) ≠ 1) (affineTwo_injective P z heq)

theorem linearOne_holomorphic : MDiff P.linearOne := by
  have hfun : P.linearOne = fun z ↦ P.affineOne z 1 - P.affineOne z 0 := by
    funext z
    simpa using (P.affineOne_sub z 1 0).symm
  rw [hfun]
  exact (P.affineOne_holomorphic (fun _ ↦ 1) mdifferentiable_const).sub
    (P.affineOne_holomorphic (fun _ ↦ 0) mdifferentiable_const)

theorem linearTwo_holomorphic : MDiff P.linearTwo := by
  have hfun : P.linearTwo = fun z ↦ P.affineTwo z 1 - P.affineTwo z 0 := by
    funext z
    simpa using (P.affineTwo_sub z 1 0).symm
  rw [hfun]
  exact (P.affineTwo_holomorphic (fun _ ↦ 1) mdifferentiable_const).sub
    (P.affineTwo_holomorphic (fun _ ↦ 0) mdifferentiable_const)

private def totalOne (x : UpperHalfPlane × ℂ) : UpperHalfPlane × ℂ :=
  (fuchsianSourceAction g₁ • x.1, P.affineOne x.1 x.2)

private def totalTwo (x : UpperHalfPlane × ℂ) : UpperHalfPlane × ℂ :=
  (fuchsianSourceAction g₂ • x.1, P.affineTwo x.1 x.2)

private theorem totalOne_three (x : UpperHalfPlane × ℂ) :
    totalOne P (totalOne P (totalOne P x)) = x := by
  apply Prod.ext
  · change fuchsianSourceAction g₁ •
        (fuchsianSourceAction g₁ • (fuchsianSourceAction g₁ • x.1)) = x.1
    rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul,
      show g₁ * g₁ * g₁ = g₁ ^ 3 by
        simp only [pow_succ, pow_zero, one_mul],
      g₁_pow_three, map_one, one_smul]
  · change P.affineOne
        (fuchsianSourceAction g₁ • (fuchsianSourceAction g₁ • x.1))
        (P.affineOne (fuchsianSourceAction g₁ • x.1) (P.affineOne x.1 x.2)) = x.2
    have h2 : fuchsianSourceAction g₁ • (fuchsianSourceAction g₁ • x.1) =
        fuchsianSourceAction (g₁ ^ 2) • x.1 := by
      rw [← mul_smul, ← map_mul, pow_two]
    rw [h2]
    exact P.affineOne_cycle x.1 x.2

private theorem totalTwo_four (x : UpperHalfPlane × ℂ) :
    totalTwo P (totalTwo P (totalTwo P (totalTwo P x))) = x := by
  apply Prod.ext
  · change fuchsianSourceAction g₂ • (fuchsianSourceAction g₂ •
        (fuchsianSourceAction g₂ • (fuchsianSourceAction g₂ • x.1))) = x.1
    rw [← mul_smul, ← mul_smul, ← mul_smul, ← map_mul, ← map_mul,
      ← map_mul, show g₂ * g₂ * g₂ * g₂ = g₂ ^ 4 by
        simp only [pow_succ, pow_zero, one_mul],
      g₂_pow_four, map_one, one_smul]
  · change P.affineTwo
        (fuchsianSourceAction g₂ • (fuchsianSourceAction g₂ •
          (fuchsianSourceAction g₂ • x.1)))
        (P.affineTwo (fuchsianSourceAction g₂ • (fuchsianSourceAction g₂ • x.1))
          (P.affineTwo (fuchsianSourceAction g₂ • x.1) (P.affineTwo x.1 x.2))) = x.2
    have h2 : fuchsianSourceAction g₂ • (fuchsianSourceAction g₂ • x.1) =
        fuchsianSourceAction (g₂ ^ 2) • x.1 := by
      rw [← mul_smul, ← map_mul, pow_two]
    have h3 : fuchsianSourceAction g₂ • (fuchsianSourceAction (g₂ ^ 2) • x.1) =
        fuchsianSourceAction (g₂ ^ 3) • x.1 := by
      rw [← mul_smul, ← map_mul, show g₂ * g₂ ^ 2 = g₂ ^ 3 by
        simp only [pow_succ', pow_zero, mul_one]]
    rw [h2, h3]
    exact P.affineTwo_cycle x.1 x.2

private noncomputable def totalOneEquiv : (UpperHalfPlane × ℂ) ≃ (UpperHalfPlane × ℂ) where
  toFun := totalOne P
  invFun := totalOne P ∘ totalOne P
  left_inv := totalOne_three P
  right_inv := totalOne_three P

private noncomputable def totalTwoEquiv : (UpperHalfPlane × ℂ) ≃ (UpperHalfPlane × ℂ) where
  toFun := totalTwo P
  invFun := totalTwo P ∘ totalTwo P ∘ totalTwo P
  left_inv := totalTwo_four P
  right_inv := totalTwo_four P

private theorem totalOneEquiv_pow_three : totalOneEquiv P ^ 3 = 1 := by
  apply Equiv.ext
  intro x
  change totalOne P (totalOne P (totalOne P x)) = x
  exact totalOne_three P x

private theorem totalTwoEquiv_pow_four : totalTwoEquiv P ^ 4 = 1 := by
  apply Equiv.ext
  intro x
  change totalTwo P (totalTwo P (totalTwo P (totalTwo P x))) = x
  exact totalTwo_four P x

/-- The cycle hypotheses extend the substitutions to an action of the full free product. -/
noncomputable def affineTotalAction : Delta →* Equiv.Perm (UpperHalfPlane × ℂ) :=
  Monoid.Coprod.lift
    (cyclicRepresentation 3 (totalOneEquiv P) (totalOneEquiv_pow_three P))
    (cyclicRepresentation 4 (totalTwoEquiv P) (totalTwoEquiv_pow_four P))

@[simp] theorem affineTotalAction_gOne (x : UpperHalfPlane × ℂ) :
    affineTotalAction P g₁ x = totalOne P x := by
  simp [affineTotalAction, g₁, totalOneEquiv]

@[simp] theorem affineTotalAction_gTwo (x : UpperHalfPlane × ℂ) :
    affineTotalAction P g₂ x = totalTwo P x := by
  simp [affineTotalAction, g₂, totalTwoEquiv]

private theorem affineTotalAction_inl_base (a : CyclicThree) (x : UpperHalfPlane × ℂ) :
    (affineTotalAction P (Monoid.Coprod.inl a) x).1 =
      fuchsianSourceAction (Monoid.Coprod.inl a) • x.1 := by
  fin_cases a
  · change (affineTotalAction P (Monoid.Coprod.inl
        (Multiplicative.ofAdd (0 : ZMod 3))) x).1 =
      fuchsianSourceAction (Monoid.Coprod.inl (Multiplicative.ofAdd (0 : ZMod 3))) • x.1
    simp
  · change (affineTotalAction P g₁ x).1 = fuchsianSourceAction g₁ • x.1
    rw [affineTotalAction_gOne]
    rfl
  · change (affineTotalAction P (Monoid.Coprod.inl
        (Multiplicative.ofAdd (2 : ZMod 3))) x).1 =
      fuchsianSourceAction (Monoid.Coprod.inl (Multiplicative.ofAdd (2 : ZMod 3))) • x.1
    have hg : Monoid.Coprod.inl (Multiplicative.ofAdd (2 : ZMod 3)) = g₁ ^ 2 := by
      unfold g₁
      rw [pow_two, ← map_mul]
      congr
    rw [hg, map_pow, map_pow]
    change (affineTotalAction P g₁ (affineTotalAction P g₁ x)).1 =
      fuchsianSourceAction g₁ • (fuchsianSourceAction g₁ • x.1)
    rw [affineTotalAction_gOne, affineTotalAction_gOne]
    rfl

private theorem affineTotalAction_inr_base (a : CyclicFour) (x : UpperHalfPlane × ℂ) :
    (affineTotalAction P (Monoid.Coprod.inr a) x).1 =
      fuchsianSourceAction (Monoid.Coprod.inr a) • x.1 := by
  fin_cases a
  · change (affineTotalAction P (Monoid.Coprod.inr
        (Multiplicative.ofAdd (0 : ZMod 4))) x).1 =
      fuchsianSourceAction (Monoid.Coprod.inr (Multiplicative.ofAdd (0 : ZMod 4))) • x.1
    simp
  · change (affineTotalAction P g₂ x).1 = fuchsianSourceAction g₂ • x.1
    rw [affineTotalAction_gTwo]
    rfl
  · change (affineTotalAction P (Monoid.Coprod.inr
        (Multiplicative.ofAdd (2 : ZMod 4))) x).1 =
      fuchsianSourceAction (Monoid.Coprod.inr (Multiplicative.ofAdd (2 : ZMod 4))) • x.1
    have hg : Monoid.Coprod.inr (Multiplicative.ofAdd (2 : ZMod 4)) = g₂ ^ 2 := by
      unfold g₂
      rw [pow_two, ← map_mul]
      congr
    rw [hg, map_pow, map_pow]
    change (affineTotalAction P g₂ (affineTotalAction P g₂ x)).1 =
      fuchsianSourceAction g₂ • (fuchsianSourceAction g₂ • x.1)
    rw [affineTotalAction_gTwo, affineTotalAction_gTwo]
    rfl
  · change (affineTotalAction P (Monoid.Coprod.inr
        (Multiplicative.ofAdd (3 : ZMod 4))) x).1 =
      fuchsianSourceAction (Monoid.Coprod.inr (Multiplicative.ofAdd (3 : ZMod 4))) • x.1
    have hg : Monoid.Coprod.inr (Multiplicative.ofAdd (3 : ZMod 4)) = g₂ ^ 3 := by
      unfold g₂
      rw [pow_succ, pow_two, ← map_mul, ← map_mul]
      congr
    rw [hg, map_pow, map_pow]
    change (affineTotalAction P g₂
      (affineTotalAction P g₂ (affineTotalAction P g₂ x))).1 =
        fuchsianSourceAction g₂ •
          (fuchsianSourceAction g₂ • (fuchsianSourceAction g₂ • x.1))
    rw [affineTotalAction_gTwo, affineTotalAction_gTwo, affineTotalAction_gTwo]
    rfl

theorem affineTotalAction_base (g : Delta) (x : UpperHalfPlane × ℂ) :
    (affineTotalAction P g x).1 = fuchsianSourceAction g • x.1 := by
  induction g using Monoid.Coprod.induction_on generalizing x with
  | inl a => exact affineTotalAction_inl_base P a x
  | inr a => exact affineTotalAction_inr_base P a x
  | mul g h ihg ihh =>
      calc
        (affineTotalAction P (g * h) x).1 =
            (affineTotalAction P g (affineTotalAction P h x)).1 := by
          rw [map_mul]
          rfl
        _ = fuchsianSourceAction g • (affineTotalAction P h x).1 :=
          ihg (affineTotalAction P h x)
        _ = fuchsianSourceAction g • (fuchsianSourceAction h • x.1) := by rw [ihh]
        _ = fuchsianSourceAction (g * h) • x.1 := by rw [map_mul, mul_smul]

private theorem totalOne_fixes_ellipticOne :
    totalOne P (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint) =
      (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint) := by
  apply Prod.ext
  · exact fuchsianOneFixedPoint_fixed
  · change P.affineOne fuchsianOneFixedPoint (P.ellipticOne fuchsianOneFixedPoint) =
      P.ellipticOne fuchsianOneFixedPoint
    have h := P.ellipticOne_equivariant fuchsianOneFixedPoint
    rw [fuchsianOneFixedPoint_fixed] at h
    exact h.symm

private theorem totalTwo_fixes_ellipticTwo :
    totalTwo P (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint) =
      (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint) := by
  apply Prod.ext
  · exact fuchsianTwoFixedPoint_fixed
  · change P.affineTwo fuchsianTwoFixedPoint (P.ellipticTwo fuchsianTwoFixedPoint) =
      P.ellipticTwo fuchsianTwoFixedPoint
    have h := P.ellipticTwo_equivariant fuchsianTwoFixedPoint
    rw [fuchsianTwoFixedPoint_fixed] at h
    exact h.symm

private theorem affineTotalAction_gOne_fixes_ellipticOne :
    affineTotalAction P g₁
        (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint) =
      (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint) := by
  rw [affineTotalAction_gOne]
  exact totalOne_fixes_ellipticOne P

private theorem affineTotalAction_gTwo_fixes_ellipticTwo :
    affineTotalAction P g₂
        (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint) =
      (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint) := by
  rw [affineTotalAction_gTwo]
  exact totalTwo_fixes_ellipticTwo P

private theorem affineTotalAction_inl_fixes_ellipticOne (a : CyclicThree) :
    affineTotalAction P (Monoid.Coprod.inl a)
        (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint) =
      (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint) := by
  fin_cases a
  · change affineTotalAction P (Monoid.Coprod.inl
        (Multiplicative.ofAdd (0 : ZMod 3))) _ = _
    simp
  · change affineTotalAction P g₁ _ = _
    exact affineTotalAction_gOne_fixes_ellipticOne P
  · change affineTotalAction P (Monoid.Coprod.inl
        (Multiplicative.ofAdd (2 : ZMod 3))) _ = _
    have hg : Monoid.Coprod.inl (Multiplicative.ofAdd (2 : ZMod 3)) = g₁ ^ 2 := by
      unfold g₁
      rw [pow_two, ← map_mul]
      congr
    rw [hg, map_pow]
    change affineTotalAction P g₁ (affineTotalAction P g₁ _) = _
    rw [affineTotalAction_gOne_fixes_ellipticOne,
      affineTotalAction_gOne_fixes_ellipticOne]

private theorem affineTotalAction_inr_fixes_ellipticTwo (a : CyclicFour) :
    affineTotalAction P (Monoid.Coprod.inr a)
        (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint) =
      (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint) := by
  fin_cases a
  · change affineTotalAction P (Monoid.Coprod.inr
        (Multiplicative.ofAdd (0 : ZMod 4))) _ = _
    simp
  · change affineTotalAction P g₂ _ = _
    exact affineTotalAction_gTwo_fixes_ellipticTwo P
  · change affineTotalAction P (Monoid.Coprod.inr
        (Multiplicative.ofAdd (2 : ZMod 4))) _ = _
    have hg : Monoid.Coprod.inr (Multiplicative.ofAdd (2 : ZMod 4)) = g₂ ^ 2 := by
      unfold g₂
      rw [pow_two, ← map_mul]
      congr
    rw [hg, map_pow]
    change affineTotalAction P g₂ (affineTotalAction P g₂ _) = _
    rw [affineTotalAction_gTwo_fixes_ellipticTwo,
      affineTotalAction_gTwo_fixes_ellipticTwo]
  · change affineTotalAction P (Monoid.Coprod.inr
        (Multiplicative.ofAdd (3 : ZMod 4))) _ = _
    have hg : Monoid.Coprod.inr (Multiplicative.ofAdd (3 : ZMod 4)) = g₂ ^ 3 := by
      unfold g₂
      rw [pow_succ, pow_two, ← map_mul, ← map_mul]
      congr
    rw [hg, map_pow]
    change affineTotalAction P g₂
      (affineTotalAction P g₂ (affineTotalAction P g₂ _)) = _
    rw [affineTotalAction_gTwo_fixes_ellipticTwo,
      affineTotalAction_gTwo_fixes_ellipticTwo,
      affineTotalAction_gTwo_fixes_ellipticTwo]

private theorem transportedEllipticOne_fixed (c h : Delta)
    (hfixed : fuchsianSourceAction h •
        (fuchsianSourceAction c • fuchsianOneFixedPoint) =
      fuchsianSourceAction c • fuchsianOneFixedPoint) :
    affineTotalAction P h (affineTotalAction P c
        (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint)) =
      affineTotalAction P c
        (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint) := by
  let k : Delta := c⁻¹ * h * c
  have hkfixed : fuchsianSourceAction k • fuchsianOneFixedPoint =
      fuchsianOneFixedPoint := by
    dsimp only [k]
    rw [map_mul, map_mul, map_inv, mul_smul, mul_smul, hfixed, inv_smul_smul]
  obtain ⟨a, ha⟩ := (establishedFuchsianOneStabilizerExact k).mp hkfixed
  have hlocal : affineTotalAction P k
      (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint) =
        (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint) := by
    rw [ha]
    exact affineTotalAction_inl_fixes_ellipticOne P a
  have hgroup : h * c = c * k := by
    simp only [k]
    group
  calc
    affineTotalAction P h (affineTotalAction P c
        (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint)) =
      affineTotalAction P (h * c)
        (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint) := by
          rw [map_mul]
          rfl
    _ = affineTotalAction P (c * k)
        (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint) := by rw [hgroup]
    _ = affineTotalAction P c (affineTotalAction P k
        (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint)) := by
          rw [map_mul]
          rfl
    _ = affineTotalAction P c
        (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint) := by rw [hlocal]

private theorem transportedEllipticTwo_fixed (c h : Delta)
    (hfixed : fuchsianSourceAction h •
        (fuchsianSourceAction c • fuchsianTwoFixedPoint) =
      fuchsianSourceAction c • fuchsianTwoFixedPoint) :
    affineTotalAction P h (affineTotalAction P c
        (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint)) =
      affineTotalAction P c
        (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint) := by
  let k : Delta := c⁻¹ * h * c
  have hkfixed : fuchsianSourceAction k • fuchsianTwoFixedPoint =
      fuchsianTwoFixedPoint := by
    dsimp only [k]
    rw [map_mul, map_mul, map_inv, mul_smul, mul_smul, hfixed, inv_smul_smul]
  obtain ⟨a, ha⟩ := (establishedFuchsianTwoStabilizerExact k).mp hkfixed
  have hlocal : affineTotalAction P k
      (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint) =
        (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint) := by
    rw [ha]
    exact affineTotalAction_inr_fixes_ellipticTwo P a
  have hgroup : h * c = c * k := by
    simp only [k]
    group
  calc
    affineTotalAction P h (affineTotalAction P c
        (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint)) =
      affineTotalAction P (h * c)
        (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint) := by
          rw [map_mul]
          rfl
    _ = affineTotalAction P (c * k)
        (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint) := by rw [hgroup]
    _ = affineTotalAction P c (affineTotalAction P k
        (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint)) := by
          rw [map_mul]
          rfl
    _ = affineTotalAction P c
        (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint) := by rw [hlocal]

structure StableTotalLiftAt (z : UpperHalfPlane) where
  point : UpperHalfPlane × ℂ
  point_fst : point.1 = z
  fixed : ∀ g : Delta, fuchsianSourceAction g • z = z → affineTotalAction P g point = point

noncomputable def stableTotalLiftAt (z : UpperHalfPlane) : StableTotalLiftAt P z := by
  classical
  by_cases hOne : ∃ c : Delta, fuchsianSourceAction c • fuchsianOneFixedPoint = z
  · let c : Delta := Classical.choose hOne
    have hc : fuchsianSourceAction c • fuchsianOneFixedPoint = z := Classical.choose_spec hOne
    refine { point := (affineTotalAction P c
      (fuchsianOneFixedPoint, P.ellipticOne fuchsianOneFixedPoint)), point_fst := ?_, fixed := ?_ }
    · rw [affineTotalAction_base, hc]
    · intro g hg
      apply transportedEllipticOne_fixed P c g
      simpa only [hc] using hg
  · by_cases hTwo : ∃ c : Delta, fuchsianSourceAction c • fuchsianTwoFixedPoint = z
    · let c : Delta := Classical.choose hTwo
      have hc : fuchsianSourceAction c • fuchsianTwoFixedPoint = z := Classical.choose_spec hTwo
      refine { point := (affineTotalAction P c
        (fuchsianTwoFixedPoint, P.ellipticTwo fuchsianTwoFixedPoint)), point_fst := ?_, fixed := ?_ }
      · rw [affineTotalAction_base, hc]
      · intro g hg
        apply transportedEllipticTwo_fixed P c g
        simpa only [hc] using hg
    · have hzregular :
          SphereSixComplex.TriangleGroup.FreeProductTorsion.IsFuchsianRegularPoint z := by
        intro g
        constructor
        · intro hg
          apply hOne
          refine ⟨g⁻¹, ?_⟩
          calc
            fuchsianSourceAction g⁻¹ • fuchsianOneFixedPoint =
                fuchsianSourceAction g⁻¹ • (fuchsianSourceAction g • z) :=
              congrArg (fun w ↦ fuchsianSourceAction g⁻¹ • w) hg.symm
            _ = z := by rw [map_inv, inv_smul_smul]
        · intro hg
          apply hTwo
          refine ⟨g⁻¹, ?_⟩
          calc
            fuchsianSourceAction g⁻¹ • fuchsianTwoFixedPoint =
                fuchsianSourceAction g⁻¹ • (fuchsianSourceAction g • z) :=
              congrArg (fun w ↦ fuchsianSourceAction g⁻¹ • w) hg.symm
            _ = z := by rw [map_inv, inv_smul_smul]
      refine { point := (z, 0), point_fst := rfl, fixed := ?_ }
      intro g hg
      have hgone : g = 1 :=
        SphereSixComplex.TriangleGroup.FuchsianProperFreeness.fuchsian_fixed_regular_eq_one
          SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination.fuchsianSourceAction_properlyDiscontinuous
          hzregular hg
      subst g
      simp

private noncomputable def quotientRepresentative (q : ℂ) : UpperHalfPlane :=
  Classical.choose (P.quotient.coordinate_isQuotientMap.surjective q)

private theorem quotientRepresentative_coordinate (q : ℂ) :
    P.quotient.coordinate (quotientRepresentative P q) = q :=
  Classical.choose_spec (P.quotient.coordinate_isQuotientMap.surjective q)

private noncomputable def orbitTransporter (z : UpperHalfPlane) : Delta :=
  Classical.choose
    ((P.quotient.coordinate_eq_iff_orbit
      (quotientRepresentative P (P.quotient.coordinate z)) z).mp
        (quotientRepresentative_coordinate P (P.quotient.coordinate z)))

private theorem orbitTransporter_spec (z : UpperHalfPlane) :
    fuchsianSourceAction (orbitTransporter P z) •
      quotientRepresentative P (P.quotient.coordinate z) = z :=
  Classical.choose_spec
    ((P.quotient.coordinate_eq_iff_orbit
      (quotientRepresentative P (P.quotient.coordinate z)) z).mp
        (quotientRepresentative_coordinate P (P.quotient.coordinate z)))

/-- Choice gives a section of the affine total-orbit map.  The stabilizer calculation makes the
result independent of the chosen transporter.  No continuity is asserted. -/
noncomputable def setTheoreticTotalSection (z : UpperHalfPlane) : UpperHalfPlane × ℂ :=
  affineTotalAction P (orbitTransporter P z)
    (stableTotalLiftAt P
      (quotientRepresentative P (P.quotient.coordinate z))).point

theorem setTheoreticTotalSection_fst (z : UpperHalfPlane) :
    (setTheoreticTotalSection P z).1 = z := by
  rw [setTheoreticTotalSection, affineTotalAction_base,
    (stableTotalLiftAt P _).point_fst, orbitTransporter_spec]

private theorem stable_transport_unique (z : UpperHalfPlane) (g : Delta)
    (hg : fuchsianSourceAction g •
      quotientRepresentative P (P.quotient.coordinate z) = z) :
    affineTotalAction P g
        (stableTotalLiftAt P
          (quotientRepresentative P (P.quotient.coordinate z))).point =
      setTheoreticTotalSection P z := by
  let r := quotientRepresentative P (P.quotient.coordinate z)
  let t := orbitTransporter P z
  let k : Delta := t⁻¹ * g
  have ht : fuchsianSourceAction t • r = z := orbitTransporter_spec P z
  have hk : fuchsianSourceAction k • r = r := by
    dsimp only [k]
    rw [map_mul, map_inv, mul_smul, hg, ← ht, inv_smul_smul]
  have hkpoint := (stableTotalLiftAt P r).fixed k hk
  have hgroup : g = t * k := by
    simp only [k]
    group
  rw [setTheoreticTotalSection]
  change affineTotalAction P g (stableTotalLiftAt P r).point =
    affineTotalAction P t (stableTotalLiftAt P r).point
  rw [hgroup, map_mul]
  change affineTotalAction P t
    (affineTotalAction P k (stableTotalLiftAt P r).point) = _
  rw [hkpoint]

/-- The choice-based section is nevertheless exactly equivariant under the full group. -/
theorem setTheoreticTotalSection_equivariant (g : Delta) (z : UpperHalfPlane) :
    setTheoreticTotalSection P (fuchsianSourceAction g • z) =
      affineTotalAction P g (setTheoreticTotalSection P z) := by
  have hcoord : P.quotient.coordinate (fuchsianSourceAction g • z) =
      P.quotient.coordinate z := P.quotient.coordinate_invariant g z
  have hrep : quotientRepresentative P
      (P.quotient.coordinate (fuchsianSourceAction g • z)) =
        quotientRepresentative P (P.quotient.coordinate z) := by rw [hcoord]
  have hcand : fuchsianSourceAction (g * orbitTransporter P z) •
      quotientRepresentative P
        (P.quotient.coordinate (fuchsianSourceAction g • z)) =
      fuchsianSourceAction g • z := by
    rw [hrep, map_mul, mul_smul, orbitTransporter_spec]
  have hu := stable_transport_unique P (fuchsianSourceAction g • z)
    (g * orbitTransporter P z) hcand
  rw [← hu, map_mul]
  change affineTotalAction P g
      (affineTotalAction P (orbitTransporter P z)
        (stableTotalLiftAt P (quotientRepresentative P
          (P.quotient.coordinate (fuchsianSourceAction g • z)))).point) = _
  rw [hrep]
  rfl

/-- Fibre coordinate of the set-theoretic total section. -/
noncomputable def setTheoreticSection (z : UpperHalfPlane) : ℂ :=
  (setTheoreticTotalSection P z).2

theorem setTheoreticSection_one (z : UpperHalfPlane) :
    setTheoreticSection P (fuchsianSourceAction g₁ • z) =
      P.affineOne z (setTheoreticSection P z) := by
  have h := congrArg Prod.snd (setTheoreticTotalSection_equivariant P g₁ z)
  rw [affineTotalAction_gOne] at h
  simpa [setTheoreticSection, totalOne, setTheoreticTotalSection_fst] using h

theorem setTheoreticSection_two (z : UpperHalfPlane) :
    setTheoreticSection P (fuchsianSourceAction g₂ • z) =
      P.affineTwo z (setTheoreticSection P z) := by
  have h := congrArg Prod.snd (setTheoreticTotalSection_equivariant P g₂ z)
  rw [affineTotalAction_gTwo] at h
  simpa [setTheoreticSection, totalTwo, setTheoreticTotalSection_fst] using h

/-! The quotient map has exactly the expected universal property for functions for which
regularity on the source is already known.  These lemmas deliberately do not claim that the
choice-based section above is continuous. -/

theorem factorsThrough_coordinate_of_invariant
    (C : ExactFuchsianOrbifoldCoordinate)
    (f : UpperHalfPlane → ℂ)
    (hinv : ∀ g z, f (fuchsianSourceAction g • z) = f z) :
    Function.FactorsThrough f C.coordinate := by
  intro z w hzw
  obtain ⟨g, rfl⟩ := (C.coordinate_eq_iff_orbit z w).mp hzw
  exact (hinv g z).symm

private noncomputable def coordinateContinuousMap
    (C : ExactFuchsianOrbifoldCoordinate) : C(UpperHalfPlane, ℂ) :=
  ⟨C.coordinate, C.coordinate_holomorphic.continuous⟩

private theorem coordinateContinuousMap_isQuotientMap
    (C : ExactFuchsianOrbifoldCoordinate) :
    Topology.IsQuotientMap (coordinateContinuousMap C) :=
  C.coordinate_isQuotientMap

/-- A continuous invariant scalar function descends continuously to the exact quotient. -/
noncomputable def descendInvariantContinuous
    (C : ExactFuchsianOrbifoldCoordinate)
    (f : UpperHalfPlane → ℂ)
    (hf : Continuous f)
    (hinv : ∀ g z, f (fuchsianSourceAction g • z) = f z) : ℂ → ℂ :=
  (coordinateContinuousMap_isQuotientMap C).lift ⟨f, hf⟩
    (factorsThrough_coordinate_of_invariant C f hinv)

theorem descendInvariantContinuous_continuous
    (C : ExactFuchsianOrbifoldCoordinate)
    (f : UpperHalfPlane → ℂ)
    (hf : Continuous f)
    (hinv : ∀ g z, f (fuchsianSourceAction g • z) = f z) :
    Continuous (descendInvariantContinuous C f hf hinv) :=
  ((coordinateContinuousMap_isQuotientMap C).lift ⟨f, hf⟩
    (factorsThrough_coordinate_of_invariant C f hinv)).continuous

@[simp] theorem descendInvariantContinuous_comp_coordinate
    (C : ExactFuchsianOrbifoldCoordinate)
    (f : UpperHalfPlane → ℂ)
    (hf : Continuous f)
    (hinv : ∀ g z, f (fuchsianSourceAction g • z) = f z)
    (z : UpperHalfPlane) :
    descendInvariantContinuous C f hf hinv (C.coordinate z) = f z := by
  exact DFunLike.congr_fun
    ((coordinateContinuousMap_isQuotientMap C).lift_comp ⟨f, hf⟩
      (factorsThrough_coordinate_of_invariant C f hinv)) z

theorem descendInvariantContinuous_unique
    (C : ExactFuchsianOrbifoldCoordinate)
    (f : UpperHalfPlane → ℂ)
    (hf : Continuous f)
    (hinv : ∀ g z, f (fuchsianSourceAction g • z) = f z)
    (F : ℂ → ℂ)
    (hF : ∀ z, F (C.coordinate z) = f z) :
    F = descendInvariantContinuous C f hf hinv := by
  funext q
  obtain ⟨z, rfl⟩ := C.coordinate_isQuotientMap.surjective q
  rw [hF, descendInvariantContinuous_comp_coordinate]

end QuotientDescent

#print axioms QuotientDescent.affineOne_injective
#print axioms QuotientDescent.linearOne_ne_zero
#print axioms QuotientDescent.linearOne_holomorphic
#print axioms QuotientDescent.affineTotalAction
#print axioms QuotientDescent.affineTotalAction_base
#print axioms QuotientDescent.stableTotalLiftAt
#print axioms QuotientDescent.setTheoreticTotalSection_equivariant
#print axioms QuotientDescent.setTheoreticSection_one
#print axioms QuotientDescent.setTheoreticSection_two
#print axioms QuotientDescent.descendInvariantContinuous

end SphereSixComplex.Periods
