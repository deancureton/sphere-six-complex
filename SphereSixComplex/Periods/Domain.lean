module

public import SphereSixComplex.Periods.Invariant
public import SphereSixComplex.TriangleGroup.Representation
import all SphereSixComplex.TriangleGroup.Representation

/-!
# The period domain

The triangle group acts on the parameter triples satisfying the period-lattice inequalities.
-/

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

/-- Parameter triples for which the four period columns form a real basis of `ℂ²`. -/
public abbrev PeriodDomain := {x : Parameters // SetupInequalities x}

public theorem PeriodDomain.tau_ne_zero (x : PeriodDomain) : x.1.tau ≠ 0 := by
  intro h
  simpa [h] using x.2.tau_im_pos.ne'

public theorem PeriodDomain.tau_ne_one (x : PeriodDomain) : x.1.tau ≠ 1 := by
  intro h
  simpa [h] using x.2.tau_im_pos.ne'

@[expose] public noncomputable def transformOneDomain (x : PeriodDomain) : PeriodDomain :=
  ⟨transformOne x.1, setupInequalities_transformOne x.1 x.2⟩

@[expose] public noncomputable def transformTwoDomain (x : PeriodDomain) : PeriodDomain :=
  ⟨transformTwo x.1, setupInequalities_transformTwo x.1 x.2⟩

@[expose] public noncomputable def transformCuspDomain (x : PeriodDomain) : PeriodDomain :=
  ⟨transformCusp x.1, setupInequalities_transformCusp x.1 x.2⟩

public noncomputable def transformOneEquiv : Equiv.Perm PeriodDomain where
  toFun := transformOneDomain
  invFun x := transformOneDomain (transformOneDomain x)
  left_inv x := by
    apply Subtype.ext
    exact transformOne_order_three x.1 x.tau_ne_zero x.tau_ne_one
  right_inv x := by
    apply Subtype.ext
    exact transformOne_order_three x.1 x.tau_ne_zero x.tau_ne_one

public noncomputable def transformTwoEquiv : Equiv.Perm PeriodDomain where
  toFun := transformTwoDomain
  invFun x := transformTwoDomain (transformTwoDomain (transformTwoDomain x))
  left_inv x := by
    apply Subtype.ext
    exact transformTwo_order_four x.1 x.tau_ne_zero
  right_inv x := by
    apply Subtype.ext
    exact transformTwo_order_four x.1 x.tau_ne_zero

public theorem transformOneEquiv_pow_three : transformOneEquiv ^ 3 = 1 := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact transformOne_order_three x.1 x.tau_ne_zero x.tau_ne_one

public theorem transformTwoEquiv_pow_four : transformTwoEquiv ^ 4 = 1 := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact transformTwo_order_four x.1 x.tau_ne_zero

/-- The triangle-group action on the nondegenerate period domain. -/
public noncomputable def rhoParameters : Delta →* Equiv.Perm PeriodDomain :=
  Monoid.Coprod.lift
    (cyclicRepresentation 3 transformOneEquiv transformOneEquiv_pow_three)
    (cyclicRepresentation 4 transformTwoEquiv transformTwoEquiv_pow_four)

@[simp]
public theorem rhoParameters_g₁ : rhoParameters g₁ = transformOneEquiv := by
  simp [rhoParameters, g₁]

@[simp]
public theorem rhoParameters_g₂ : rhoParameters g₂ = transformTwoEquiv := by
  simp [rhoParameters, g₂]

/-- The parameter-space cusp transformation as the inverse product of the elliptic generators. -/
public noncomputable def transformCuspEquiv : Equiv.Perm PeriodDomain :=
  (transformOneEquiv * transformTwoEquiv)⁻¹

@[simp]
public theorem transformCuspEquiv_apply (x : PeriodDomain) :
    transformCuspEquiv x = transformCuspDomain x := by
  apply (transformOneEquiv * transformTwoEquiv).injective
  rw [show (transformOneEquiv * transformTwoEquiv) (transformCuspEquiv x) = x by
    exact Equiv.apply_symm_apply _ x]
  change x = transformOneDomain (transformTwoDomain (transformCuspDomain x))
  apply Subtype.ext
  exact (transformOne_transformTwo_transformCusp x.1 x.tau_ne_one).symm

@[simp]
public theorem rhoParameters_g₀ : rhoParameters g₀ = transformCuspEquiv := by
  rw [g₀, map_inv, map_mul, rhoParameters_g₁, rhoParameters_g₂]
  rfl

@[simp]
public theorem rhoParameters_g₁_apply (x : PeriodDomain) :
    rhoParameters g₁ x = transformOneDomain x := by
  rw [rhoParameters_g₁]
  rfl

@[simp]
public theorem rhoParameters_g₂_apply (x : PeriodDomain) :
    rhoParameters g₂ x = transformTwoDomain x := by
  rw [rhoParameters_g₂]
  rfl

@[simp]
public theorem rhoParameters_g₀_apply (x : PeriodDomain) :
    rhoParameters g₀ x = transformCuspDomain x := by
  rw [rhoParameters_g₀, transformCuspEquiv_apply]

end SphereSixComplex.Periods
