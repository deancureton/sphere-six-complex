module

public import SphereSixComplex.Paper.Geometry.EllipticWholeFiberTrivialization
import all SphereSixComplex.Prerequisites.Geometry.Quotient
import all SphereSixComplex.Paper.Geometry.TorusFamily

/-!
# Compact covers of the elliptic fibres

The central torus fibre is the image of a compact real period cube.  Consequently the pointwise
local inverse charts admit a finite subcover.  The transition formula below identifies the exact
lattice condition required for their fixed-torus-valued maps to agree off the central fibre.
-/

open scoped Manifold ContDiff

namespace SphereSixComplex.Geometry.EllipticWholeFiberCompactCover

open Filter Set SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticLocalTrivialization
open SphereSixComplex.Geometry.EllipticWholeFiberTrivialization
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.TriangleGroup SphereSixComplex.Periods

noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- Fibrewise period translations preserve the base coordinate. -/
public theorem familyTotalSpaceBase_respects
    (p q : UpperHalfPlane × ComplexTwoSpace)
    (h : MulAction.orbitRel (FamilyPeriodGroup (parameterMap F)) _ p q) :
    p.1 = q.1 := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  simpa only [family_smul_fst] using congrArg Prod.fst hg.symm

/-- The base point of the global varying-torus quotient. -/
@[expose] public noncomputable def familyTotalSpaceBase :
    TotalSpace (parameterMap F) → UpperHalfPlane :=
  Quotient.lift Prod.fst (familyTotalSpaceBase_respects F)

@[simp]
public theorem familyTotalSpaceBase_mk (p : UpperHalfPlane × ComplexTwoSpace) :
    familyTotalSpaceBase F (Quotient.mk _ p) = p.1 :=
  rfl

@[simp]
public theorem familyTotalSpaceBase_projection (p : UpperHalfPlane × ComplexTwoSpace) :
    familyTotalSpaceBase F (projection (parameterMap F) p) = p.1 := by
  rw [projection.eq_def]
  exact familyTotalSpaceBase_mk F p

/-- The fibre of the varying torus quotient over a specified base point. -/
@[expose] public def familyFiber (z : UpperHalfPlane) :
    Set (TotalSpace (parameterMap F)) :=
  Set.range fun v : ComplexTwoSpace ↦ projection (parameterMap F) (z, v)

/-- Parametrization of one fibre by the real coordinates of its period basis. -/
@[expose] public noncomputable def familyFiberRealParam (z : UpperHalfPlane) :
    RealPeriods → TotalSpace (parameterMap F) := fun r ↦
  projection (parameterMap F)
    (z, (fullRankDomain (parameterMap F z)).realEquiv r)


/-- The closed unit cube in real period coordinates covers the entire quotient fibre. -/
public theorem familyFiber_eq_image_unitCube (z : UpperHalfPlane) :
    familyFiber F z = familyFiberRealParam F z '' Set.Icc 0 1 := by
  apply Set.Subset.antisymm
  · rintro q ⟨v, rfl⟩
    let hfull := fullRankDomain (parameterMap F z)
    let r : RealPeriods := hfull.realEquiv.symm v
    let a : IntegerPeriods := fun i ↦ ⌊ r i ⌋
    let u : RealPeriods := r - integerToReal a
    have hu : u ∈ Set.Icc (0 : RealPeriods) 1 := by
      constructor
      · intro i
        exact sub_nonneg.mpr (Int.floor_le (r i))
      · intro i
        change r i - integerToReal a i ≤ (1 : ℝ)
        rw [show integerToReal a i = (a i : ℝ) by rfl]
        exact le_of_lt (sub_lt_iff_lt_add.mpr <| by
          simpa [add_comm] using Int.lt_floor_add_one (r i))
    refine ⟨u, hu, ?_⟩
    change projection (parameterMap F) (z, hfull.realEquiv u) =
      projection (parameterMap F) (z, v)
    rw [projection.eq_def, quotientProjection.eq_def]
    apply Quotient.sound
    change (MulAction.orbitRel (FamilyPeriodGroup (parameterMap F))
      (UpperHalfPlane × ComplexTwoSpace))
      (z, hfull.realEquiv u) (z, v)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    let g : FamilyPeriodGroup (parameterMap F) := Multiplicative.ofAdd (-a)
    refine ⟨g, ?_⟩
    apply Prod.ext
    · rfl
    · change periodVector (parameterMap F z).1 (-a) + v = hfull.realEquiv u
      rw [show periodVector (parameterMap F z).1 (-a) =
          -periodVector (parameterMap F z).1 a by
        have ha := periodVector_add (parameterMap F z).1 (-a) a
        rw [neg_add_cancel, periodVector_zero] at ha
        exact eq_neg_of_add_eq_zero_left ha.symm]
      rw [← hfull.map_integer]
      change -hfull.realEquiv (integerToReal a) + v =
        hfull.realEquiv (r - integerToReal a)
      rw [map_sub, hfull.realEquiv.apply_symm_apply]
      abel
  · rintro q ⟨r, _hr, rfl⟩
    exact ⟨(fullRankDomain (parameterMap F z)).realEquiv r, rfl⟩



end

end SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
