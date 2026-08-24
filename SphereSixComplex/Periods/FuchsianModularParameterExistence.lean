module

public import SphereSixComplex.Periods.FuchsianUniformizationBridge
public import SphereSixComplex.Periods.LocalOrbifoldCompatibility
public import SphereSixComplex.TriangleGroup.FreeProductTorsion
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.Covering.Basic
import all SphereSixComplex.Periods.FuchsianUniformizationBridge

/-!
# The normalized modular-parameter lifting problem

This file isolates the analytic input in Theorem 3.4(i).  The prescribed function on the
Fuchsian upper half-plane is the pullback of the coordinate on the orbifold quotient.  A solution
is a holomorphic lift through the normalized modular invariant, together with the monodromy of
the two explicit generators.

The monodromy fields are essential: the modular-invariant equation alone cannot distinguish
lifts related by the modular group.  They are also the precise replacement for the branched
covering-space theorem that is not presently available in Mathlib.  No separate elliptic-value or
cusp-translation hypotheses are needed.  Those normalizations follow from the generator laws and
the uniqueness of the relevant fixed points in the upper half-plane.
-/

open Matrix UpperHalfPlane
open scoped Manifold MatrixGroups

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FreeProductTorsion

/-- A prescribed holomorphic coordinate pulled back from the `(3, 4, ∞)` orbifold quotient. -/
public structure FuchsianOrbifoldCoordinate where
  /-- The pullback of the quotient coordinate to the source upper half-plane. -/
  coordinate : UpperHalfPlane → ℂ
  /-- Holomorphicity of the pulled-back quotient coordinate. -/
  coordinate_holomorphic : MDiff coordinate
  /-- Invariance of the coordinate under the explicit Fuchsian deck action. -/
  coordinate_invariant : ∀ g z,
    coordinate (fuchsianSourceAction g • z) = coordinate z

/-- Exact local ramification of a holomorphic function, expressed using a holomorphic local
uniformizer and a nonvanishing holomorphic unit. -/
public structure HasExactHolomorphicBranchAt (f : UpperHalfPlane → ℂ)
    (center : UpperHalfPlane) (value : ℂ) (order : ℕ) where
  /-- The asserted ramification order is positive. -/
  order_pos : 0 < order
  /-- A local complex coordinate centered at the ramification point. -/
  uniformizer : UpperHalfPlane → ℂ
  /-- The local coordinate vanishes at the distinguished point. -/
  uniformizer_center : uniformizer center = 0
  /-- The uniformizer is a complex local diffeomorphism at the center. -/
  uniformizer_isLocalDiffeomorph :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ⊤
      uniformizer center
  /-- The nonvanishing factor in the local ramification formula. -/
  unit : UpperHalfPlane → ℂ
  /-- The local factor is holomorphic at the center. -/
  unit_holomorphic : MDiffAt unit center
  /-- The local factor is a unit at the center, making the order exact. -/
  unit_ne_zero : unit center ≠ 0
  /-- Locally, the function is the asserted power of the uniformizer times a unit. -/
  factorization : ∀ᶠ z in nhds center,
    f z - value = uniformizer z ^ order * unit z

/-- The filter on the upper half-plane in which the imaginary part tends to positive infinity. -/
@[expose] public def upperHalfPlaneAtInfinity : Filter UpperHalfPlane :=
  Filter.comap UpperHalfPlane.im Filter.atTop

/-- The canonical local parameter at the explicit Fuchsian cusp. -/
@[expose] public noncomputable def fuchsianSourceCuspQ (z : UpperHalfPlane) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / sourceCuspWidth)

/-- The canonical source cusp parameter is invariant under the parabolic generator. -/
public theorem fuchsianSourceCuspQ_invariant (z : UpperHalfPlane) :
    fuchsianSourceCuspQ (fuchsianSourceAction g₀ • z) = fuchsianSourceCuspQ z := by
  change fuchsianSourceCuspQ ((fuchsianSourceAction g₀) z) = fuchsianSourceCuspQ z
  rw [fuchsianSourceCuspQ, fuchsianSourceCuspQ, sourceCusp_translation]
  have hw : (sourceCuspWidth : ℂ) ≠ 0 := by
    exact_mod_cast sourceCuspWidth_pos.ne'
  have harg :
      2 * Real.pi * Complex.I * ((z : ℂ) - sourceCuspWidth) / sourceCuspWidth =
        2 * Real.pi * Complex.I * (z : ℂ) / sourceCuspWidth -
          2 * Real.pi * Complex.I := by
    field_simp [hw]
  rw [harg]
  exact Complex.exp_periodic.sub_eq _

/-- Exact simple-cusp behavior of the reciprocal quotient coordinate.  The unit is a holomorphic
function of the completed cusp parameter and remains nonzero at the added point. -/
public structure HasExactFuchsianCusp (C : FuchsianOrbifoldCoordinate) where
  /-- The holomorphic unit in the completed cusp coordinate. -/
  cuspUnit : ℂ → ℂ
  /-- Radius of a completed cusp-coordinate neighbourhood. -/
  cuspRadius : ℝ
  /-- The completed cusp-coordinate neighbourhood is nontrivial. -/
  cuspRadius_pos : 0 < cuspRadius
  /-- The unit is holomorphic on a neighbourhood of the completed cusp. -/
  cuspUnit_holomorphic : ∀ q, q ∈ Metric.ball 0 cuspRadius → MDiffAt cuspUnit q
  /-- The extending factor is nonzero at the added cusp point. -/
  cuspUnit_zero_ne : cuspUnit 0 ≠ 0
  /-- The canonical source cusp parameter eventually lies in the unit's domain. -/
  cuspParameter_eventually_mem :
    ∀ᶠ z in upperHalfPlaneAtInfinity,
      fuchsianSourceCuspQ z ∈ Metric.ball 0 cuspRadius
  /-- The quotient coordinate has no zero sufficiently far into the cusp. -/
  coordinate_eventually_ne_zero :
    ∀ᶠ z in upperHalfPlaneAtInfinity, C.coordinate z ≠ 0
  /-- The reciprocal coordinate has a simple zero in the canonical source cusp parameter. -/
  reciprocal_factorization : ∀ᶠ z in upperHalfPlaneAtInfinity,
    (C.coordinate z)⁻¹ =
      fuchsianSourceCuspQ z * cuspUnit (fuchsianSourceCuspQ z)

/-- The paper's full normalized `(3, 4, ∞)` quotient-coordinate contract.

Besides holomorphic invariance, this says that the map is the actual orbit quotient, is a covering
away from the two elliptic values, has exact ramification orders three and four there, and has a
single simple completed cusp. -/
public structure ExactFuchsianOrbifoldCoordinate extends FuchsianOrbifoldCoordinate where
  /-- The coordinate realizes the quotient topology on the affine base. -/
  coordinate_isQuotientMap : Topology.IsQuotientMap coordinate
  /-- Equality of coordinate values is exactly the explicit Fuchsian orbit relation. -/
  coordinate_eq_iff_orbit : ∀ z w,
    coordinate z = coordinate w ↔
      ∃ g : Delta, fuchsianSourceAction g • z = w
  /-- The order-three elliptic orbit maps to the normalized value zero. -/
  coordinate_at_one : coordinate fuchsianOneFixedPoint = 0
  /-- The order-four elliptic orbit maps to the normalized value one. -/
  coordinate_at_two : coordinate fuchsianTwoFixedPoint = 1
  /-- Away from the elliptic values, the quotient coordinate is an ordinary covering map. -/
  regular_covering : IsCoveringMapOn coordinate ({0, 1} : Set ℂ)ᶜ
  /-- The quotient coordinate has exact order-three ramification at the first elliptic point. -/
  branch_one : HasExactHolomorphicBranchAt coordinate fuchsianOneFixedPoint 0 3
  /-- The quotient coordinate has exact order-four ramification at the second elliptic point. -/
  branch_two : HasExactHolomorphicBranchAt coordinate fuchsianTwoFixedPoint 1 4
  /-- The affine quotient has exactly the simple cusp prescribed in the paper. -/
  cusp : HasExactFuchsianCusp toFuchsianOrbifoldCoordinate

/-- The normalized modular invariant as a coordinate on the target modular quotient. -/
@[expose] public noncomputable def normalizedModularJCoordinate
    (z : UpperHalfPlane) : ℂ :=
  normalizedJ z / 1728

/-- The normalized modular quotient coordinate is holomorphic. -/
public theorem normalizedModularJCoordinate_holomorphic :
    MDiff normalizedModularJCoordinate := by
  exact normalizedJ_mdifferentiable.div mdifferentiable_const (by norm_num)

/-- The normalized modular quotient coordinate is invariant under the full modular group. -/
public theorem normalizedModularJCoordinate_invariant
    (g : ModularMatrix) (z : UpperHalfPlane) :
    normalizedModularJCoordinate (Matrix.SpecialLinearGroup.mapGL ℝ g • z) =
      normalizedModularJCoordinate z := by
  rw [normalizedModularJCoordinate, normalizedModularJCoordinate,
    normalizedJ_modular_invariant]

/-- The canonical parameter at the target modular cusp. -/
@[expose] public noncomputable def modularCuspQ (z : UpperHalfPlane) : ℂ :=
  Function.Periodic.qParam 1 z

/-- Exact simple-cusp behavior of the normalized modular invariant. -/
public structure HasExactNormalizedModularJCusp where
  /-- The holomorphic unit in the target completed cusp coordinate. -/
  cuspUnit : ℂ → ℂ
  /-- Radius of a completed target-cusp neighbourhood. -/
  cuspRadius : ℝ
  /-- The completed target-cusp neighbourhood is nontrivial. -/
  cuspRadius_pos : 0 < cuspRadius
  /-- The target cusp unit is holomorphic on a neighbourhood of zero. -/
  cuspUnit_holomorphic : ∀ q, q ∈ Metric.ball 0 cuspRadius → MDiffAt cuspUnit q
  /-- The target cusp unit remains nonzero at zero. -/
  cuspUnit_zero_ne : cuspUnit 0 ≠ 0
  /-- The canonical target cusp parameter eventually lies in the unit's domain. -/
  cuspParameter_eventually_mem :
    ∀ᶠ z in upperHalfPlaneAtInfinity, modularCuspQ z ∈ Metric.ball 0 cuspRadius
  /-- The normalized modular coordinate is eventually nonzero at the cusp. -/
  coordinate_eventually_ne_zero : ∀ᶠ z in upperHalfPlaneAtInfinity,
    normalizedModularJCoordinate z ≠ 0
  /-- The reciprocal modular coordinate has a simple zero in the target cusp parameter. -/
  reciprocal_factorization : ∀ᶠ z in upperHalfPlaneAtInfinity,
    (normalizedModularJCoordinate z)⁻¹ =
      modularCuspQ z * cuspUnit (modularCuspQ z)

/-- The exact target uniformization theorem for the normalized modular invariant.

Mathlib currently supplies holomorphicity and modular invariance, but the quotient-fibre,
ramification, special-value, and completed-cusp assertions below are additional analytic input. -/
public structure ExactNormalizedModularJUniformization where
  /-- The normalized modular invariant realizes the quotient topology. -/
  coordinate_isQuotientMap :
    Topology.IsQuotientMap normalizedModularJCoordinate
  /-- Its fibres are exactly the level-one modular-group orbits. -/
  coordinate_eq_iff_orbit : ∀ z w,
    normalizedModularJCoordinate z = normalizedModularJCoordinate w ↔
      ∃ g : ModularMatrix, Matrix.SpecialLinearGroup.mapGL ℝ g • z = w
  /-- The order-three modular elliptic point has normalized value zero. -/
  coordinate_at_three : normalizedModularJCoordinate ellipticThreeParameter = 0
  /-- The order-two modular elliptic point has normalized value one. -/
  coordinate_at_two : normalizedModularJCoordinate UpperHalfPlane.I = 1
  /-- Away from the elliptic values, the modular quotient is an ordinary covering. -/
  regular_covering :
    IsCoveringMapOn normalizedModularJCoordinate ({0, 1} : Set ℂ)ᶜ
  /-- The normalized modular coordinate has exact order-three ramification at the first point. -/
  branch_three : HasExactHolomorphicBranchAt normalizedModularJCoordinate
    ellipticThreeParameter 0 3
  /-- The normalized modular coordinate has exact order-two ramification at the second point. -/
  branch_two : HasExactHolomorphicBranchAt normalizedModularJCoordinate
    UpperHalfPlane.I 1 2
  /-- The normalized modular quotient has its standard simple completed cusp. -/
  cusp : HasExactNormalizedModularJCusp

/-- The exact analytic lifting obligation for Theorem 3.4(i).

The two monodromy identities encode the choices of branches at the order-three and order-four
points.  In particular, merely assuming the modular-invariant equation and values at the branch
points would be insufficient to recover these identities. -/
public structure NormalizedFuchsianModularJLift (C : FuchsianOrbifoldCoordinate) where
  /-- The upper-half-plane-valued lift of the prescribed quotient coordinate. -/
  tau : UpperHalfPlane → UpperHalfPlane
  /-- Holomorphicity of the modular-parameter lift. -/
  tau_holomorphic : MDiff tau
  /-- The normalized modular-invariant lifting equation. -/
  modularJ_equation : ∀ z, normalizedJ (tau z) = 1728 * C.coordinate z
  /-- Monodromy of the lift around the order-three orbifold point. -/
  monodromy_one : FuchsianTauEquivariant tau g₁
  /-- Monodromy of the lift around the order-four orbifold point. -/
  monodromy_two : FuchsianTauEquivariant tau g₂

/-- The precise future classical existence theorem for the normalized branched modular lift.

This is a proposition naming the remaining theorem, not an assumption or an inhabitant.  In
particular, it quantifies only over exact quotient coordinates and makes no claim about arbitrary
invariant holomorphic functions. -/
@[expose] public def NormalizedFuchsianModularJLiftingExistence : Prop :=
  ∀ _J : ExactNormalizedModularJUniformization,
    ∀ C : ExactFuchsianOrbifoldCoordinate,
    Nonempty (NormalizedFuchsianModularJLift C.toFuchsianOrbifoldCoordinate)

/-- The source and target order-three fixed points coincide. -/
public theorem fuchsianOneFixedPoint_eq_ellipticThreeParameter :
    fuchsianOneFixedPoint = ellipticThreeParameter := by
  apply UpperHalfPlane.coe_injective
  apply Complex.ext <;>
    norm_num [fuchsianOneFixedPoint, ellipticThreeParameter, UpperHalfPlane.ρ]

/-- The modular order-three transformation has a unique fixed point in the upper half-plane. -/
public theorem rhoTauReal_gOne_fixed_iff (z : UpperHalfPlane) :
    rhoTauReal g₁ • z = z ↔ z = ellipticThreeParameter := by
  change targetOnePerm • z = z ↔ _
  rw [← fuchsianOnePerm_eq_targetOnePerm]
  simpa only [fuchsianSourceAction_g₁,
    fuchsianOneFixedPoint_eq_ellipticThreeParameter] using
    fuchsianSourceAction_gOne_fixed_iff z

/-- The modular order-two transformation has a unique fixed point in the upper half-plane. -/
public theorem rhoTauReal_gTwo_fixed_iff (z : UpperHalfPlane) :
    rhoTauReal g₂ • z = z ↔ z = UpperHalfPlane.I := by
  constructor
  · intro h
    have hc := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ)) h
    rw [rhoTauReal_g₂_smul] at hc
    have hmul : -(1 : ℂ) = (z : ℂ) * z := (div_eq_iff z.ne_zero).mp hc
    have him := congrArg Complex.im hmul
    have hre := congrArg Complex.re hmul
    have hx : z.re = 0 := by
      norm_num [Complex.mul_im] at him
      have him' : z.re * z.im = 0 := by nlinarith
      rcases mul_eq_zero.mp him' with hx | hy
      · exact hx
      · exact False.elim ((ne_of_gt z.im_pos) hy)
    have hy : z.im = 1 := by
      norm_num [Complex.mul_re, hx] at hre
      nlinarith [z.im_pos]
    apply UpperHalfPlane.coe_injective
    apply Complex.ext
    · simpa [UpperHalfPlane.I] using hx
    · simpa [UpperHalfPlane.I] using hy
  · rintro rfl
    exact targetTwoFixedPoint_fixed

namespace NormalizedFuchsianModularJLift

variable {C : FuchsianOrbifoldCoordinate} (L : NormalizedFuchsianModularJLift C)

/-- Forgetting the prescribed quotient coordinate gives the modular-parameter interface used by
the rest of the period construction. -/
@[expose] public def toFuchsianModularParameter : FuchsianModularParameter where
  tau := L.tau
  tau_holomorphic := L.tau_holomorphic
  transform_one := L.monodromy_one
  transform_two := L.monodromy_two

@[simp]
public theorem toFuchsianModularParameter_tau :
    L.toFuchsianModularParameter.tau = L.tau :=
  rfl

/-- The lift is equivariant for the whole free product, not just its two generators. -/
public theorem equivariant (g : Delta) : FuchsianTauEquivariant L.tau g :=
  L.toFuchsianModularParameter.equivariant g

/-- The order-three value is forced by equivariance and the source fixed point. -/
public theorem tau_at_fuchsianOneFixedPoint :
    L.tau fuchsianOneFixedPoint = ellipticThreeParameter := by
  apply (rhoTauReal_gOne_fixed_iff (L.tau fuchsianOneFixedPoint)).mp
  calc
    rhoTauReal g₁ • L.tau fuchsianOneFixedPoint =
        L.tau (fuchsianSourceAction g₁ • fuchsianOneFixedPoint) :=
      (L.monodromy_one fuchsianOneFixedPoint).symm
    _ = L.tau fuchsianOneFixedPoint := congrArg L.tau fuchsianOneFixedPoint_fixed

/-- The order-four source point maps to the order-two modular elliptic point. -/
public theorem tau_at_fuchsianTwoFixedPoint :
    L.tau fuchsianTwoFixedPoint = UpperHalfPlane.I := by
  apply (rhoTauReal_gTwo_fixed_iff (L.tau fuchsianTwoFixedPoint)).mp
  calc
    rhoTauReal g₂ • L.tau fuchsianTwoFixedPoint =
        L.tau (fuchsianSourceAction g₂ • fuchsianTwoFixedPoint) :=
      (L.monodromy_two fuchsianTwoFixedPoint).symm
    _ = L.tau fuchsianTwoFixedPoint := congrArg L.tau fuchsianTwoFixedPoint_fixed

/-- The square of the order-four source stabilizer is killed by the modular lift.  This is the
local degree-two branching forced by the `(4 → 2)` orbifold monodromy. -/
public theorem tau_invariant_under_two_square (z : UpperHalfPlane) :
    L.tau (fuchsianSourceAction (g₂ ^ 2) • z) = L.tau z := by
  rw [map_pow, pow_two, mul_smul, L.monodromy_two, L.monodromy_two]
  change targetTwoPerm (targetTwoPerm (L.tau z)) = L.tau z
  apply UpperHalfPlane.coe_injective
  rw [targetTwoPerm_apply, targetTwoPerm_apply]
  field_simp [(L.tau z).ne_zero]

/-- The inverse product generator gives the normalized cusp translation. -/
public theorem tau_transform_cusp (z : UpperHalfPlane) :
    ((L.tau (fuchsianSourceAction g₀ • z) : UpperHalfPlane) : ℂ) = L.tau z - 1 := by
  have h := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ)) (L.equivariant g₀ z)
  exact h.trans (rhoTauReal_g₀_smul (L.tau z))

/-- The exponential cusp parameter associated to the normalized lift. -/
@[expose] public def cuspQ (z : UpperHalfPlane) : ℂ :=
  Function.Periodic.qParam 1 (L.tau z)

/-- The normalized cusp parameter descends through the parabolic source action. -/
public theorem cuspQ_invariant (z : UpperHalfPlane) :
    L.cuspQ (fuchsianSourceAction g₀ • z) = L.cuspQ z := by
  rw [cuspQ, cuspQ, L.tau_transform_cusp]
  simpa [Function.Periodic.qParam, mul_sub] using
    Complex.exp_periodic.sub_eq (2 * Real.pi * Complex.I * (L.tau z : ℂ))

/-- The coordinate induced from the constructed lift is the prescribed quotient coordinate. -/
public theorem induced_coordinate_eq (z : UpperHalfPlane) :
    L.toFuchsianModularParameter.coordinate z = C.coordinate z := by
  change normalizedJ (L.tau z) / 1728 = C.coordinate z
  rw [L.modularJ_equation]
  ring

/-- The lift satisfies all local orbifold compatibility conditions, including the cusp law. -/
public theorem isLocallyOrbifoldCompatible : IsLocallyOrbifoldCompatible L.tau where
  mapOneFixedPoint := by
    rw [commonOneFixedPoint, L.tau_at_fuchsianOneFixedPoint,
      fuchsianOneFixedPoint_eq_ellipticThreeParameter]
  mapTwoFixedPoint := L.tau_at_fuchsianTwoFixedPoint
  equivariantOne := L.monodromy_one
  equivariantTwo := L.monodromy_two
  equivariantCusp := L.equivariant g₀

/-- A solution of the normalized modular-lifting obligation is sufficient for the
`FuchsianModularParameter` existence statement, with both elliptic normalizations certified. -/
public theorem exists_fuchsianModularParameter_with_normalization
    (L : NormalizedFuchsianModularJLift C) :
    ∃ P : FuchsianModularParameter,
      P.tau fuchsianOneFixedPoint = ellipticThreeParameter ∧
      P.tau fuchsianTwoFixedPoint = UpperHalfPlane.I ∧
      ∀ z, P.coordinate z = C.coordinate z := by
  refine ⟨toFuchsianModularParameter L, tau_at_fuchsianOneFixedPoint L,
    tau_at_fuchsianTwoFixedPoint L, ?_⟩
  exact induced_coordinate_eq L

end NormalizedFuchsianModularJLift

/-- The exact classical lifting statement, if proved, supplies the normalized modular parameter
needed by the existing period construction for every exact Fuchsian quotient coordinate. -/
public theorem exists_fuchsianModularParameter_of_normalizedLiftingExistence
    (h : NormalizedFuchsianModularJLiftingExistence)
    (J : ExactNormalizedModularJUniformization)
    (C : ExactFuchsianOrbifoldCoordinate) :
    ∃ P : FuchsianModularParameter,
      P.tau fuchsianOneFixedPoint = ellipticThreeParameter ∧
      P.tau fuchsianTwoFixedPoint = UpperHalfPlane.I ∧
      ∀ z, P.coordinate z = C.coordinate z := by
  obtain ⟨L⟩ := h J C
  exact L.exists_fuchsianModularParameter_with_normalization

end SphereSixComplex.Periods
