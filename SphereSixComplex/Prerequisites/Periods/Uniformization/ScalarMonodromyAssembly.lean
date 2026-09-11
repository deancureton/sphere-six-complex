module

public import SphereSixComplex.Prerequisites.Periods.Uniformization.ScalarContinuationCover
import all SphereSixComplex.Prerequisites.Periods.Uniformization.ScalarContinuationCover
public import TauCeti.Analysis.Complex.Conformal.GlobalBranch
import all TauCeti.Analysis.Complex.Conformal.GlobalBranch

@[expose] public section

/-!
# Monodromy assembly of the global scalar branch

This file isolates the remaining analytic-continuation obligation.  Once the scalar chamber germ
continues along every path in the upper half-plane, Tau Ceti's global-branch theorem produces a
single holomorphic scalar function there.  The identity principle then identifies that branch
with the original seed throughout the open source chamber.
-/

open Complex Filter Metric Set Topology UpperHalfPlane
open scoped ComplexConjugate

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.Periods.TriangleReflections










/-! ## The right reflection law -/










/-! ## The left reflection law -/












/-! ## The circular reflection law -/










/-! ## Algebraic orbit-representative assembly

This construction avoids arbitrary pairwise compatibility of a translated atlas.  It chooses one
representative of every source orbit in the explicit doubled fundamental region and evaluates the
right Schwarz double there.  One boundary-pairing consistency theorem makes the value independent
of the representative.  Local equality with the translated regular/corner patches is then the
only analytic obligation left.
-/

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover

/-- A chosen group element carrying an upper-half-plane point into the doubled fundamental
region. -/
noncomputable def sourceFundamentalTransport (z : UpperHalfPlane) : Delta :=
  Classical.choose (exists_smul_mem_orientedFundamentalRegion z)

/-- The corresponding chosen representative in the doubled fundamental region. -/
noncomputable def sourceFundamentalRepresentative (z : UpperHalfPlane) : UpperHalfPlane :=
  fuchsianSourceAction (sourceFundamentalTransport z) • z

theorem sourceFundamentalRepresentative_mem (z : UpperHalfPlane) :
    sourceFundamentalRepresentative z ∈ orientedFundamentalRegion :=
  Classical.choose_spec (exists_smul_mem_orientedFundamentalRegion z)


/-- The exact missing boundary-pairing statement for the orbit-representative construction.
The converse is `sourceScalarRightDoubleMap_fundamental_fibres`. -/
def SourceFundamentalScalarConsistent
    (S : ChamberCaratheodorySeed sourceBoundedChamber) : Prop :=
  ∀ {z w : UpperHalfPlane}, z ∈ orientedFundamentalRegion →
    w ∈ orientedFundamentalRegion →
    (∃ g : Delta, fuchsianSourceAction g • z = w) →
      sourceScalarRightDoubleMap S (z : ℂ) = sourceScalarRightDoubleMap S (w : ℂ)

/-- The algebraically assembled scalar, extended by zero outside the upper half-plane. -/
noncomputable def orbitAssembledScalar
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (z : ℂ) : ℂ :=
  if hz : 0 < z.im then
    sourceScalarRightDoubleMap S
      (sourceFundamentalRepresentative (⟨z, hz⟩ : UpperHalfPlane) : ℂ)
  else 0

@[simp] theorem orbitAssembledScalar_apply_coe
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (z : UpperHalfPlane) :
    orbitAssembledScalar S (z : ℂ) =
      sourceScalarRightDoubleMap S (sourceFundamentalRepresentative z : ℂ) := by
  simp [orbitAssembledScalar, z.im_pos]

/-- Consistency makes the choice construction agree with the explicit double on the entire
closed doubled fundamental region. -/
theorem orbitAssembledScalar_eq_rightDouble_on_fundamental
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S)
    {z : UpperHalfPlane} (hz : z ∈ orientedFundamentalRegion) :
    orbitAssembledScalar S (z : ℂ) = sourceScalarRightDoubleMap S (z : ℂ) := by
  rw [orbitAssembledScalar_apply_coe]
  apply hconsistent (sourceFundamentalRepresentative_mem z) hz
  refine ⟨(sourceFundamentalTransport z)⁻¹, ?_⟩
  simp [sourceFundamentalRepresentative]

/-- The choice construction is source-group invariant before any analytic argument. -/
theorem orbitAssembledScalar_invariant
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) (g : Delta)
    (z : UpperHalfPlane) :
    orbitAssembledScalar S ((fuchsianSourceAction g • z : UpperHalfPlane) : ℂ) =
      orbitAssembledScalar S (z : ℂ) := by
  rw [orbitAssembledScalar_apply_coe, orbitAssembledScalar_apply_coe]
  apply hconsistent
    (sourceFundamentalRepresentative_mem (fuchsianSourceAction g • z))
    (sourceFundamentalRepresentative_mem z)
  refine ⟨sourceFundamentalTransport z * g⁻¹ *
    (sourceFundamentalTransport (fuchsianSourceAction g • z))⁻¹, ?_⟩
  simp [sourceFundamentalRepresentative, map_mul, mul_smul]

/-- The explicit fundamental-region range calculation makes the orbit-assembled scalar
surjective. -/
theorem orbitAssembledScalar_surjective
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    Function.Surjective (fun z : UpperHalfPlane => orbitAssembledScalar S (z : ℂ)) := by
  intro q
  obtain ⟨z, hz, hq⟩ :=
    sourceScalarRightDoubleMap_surjective_on_orientedFundamentalRegion S q
  refine ⟨z, ?_⟩
  change orbitAssembledScalar S (z : ℂ) = q
  rw [orbitAssembledScalar_eq_rightDouble_on_fundamental S hconsistent hz]
  exact hq

/-- Fundamental fibre separation plus consistency gives exact source-orbit fibres globally. -/
theorem orbitAssembledScalar_eq_iff_orbit
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) (z w : UpperHalfPlane) :
    orbitAssembledScalar S (z : ℂ) = orbitAssembledScalar S (w : ℂ) ↔
      ∃ g : Delta, fuchsianSourceAction g • z = w := by
  constructor
  · intro hzw
    have hrep : sourceScalarRightDoubleMap S (sourceFundamentalRepresentative z : ℂ) =
        sourceScalarRightDoubleMap S (sourceFundamentalRepresentative w : ℂ) := by
      simpa only [orbitAssembledScalar_apply_coe] using hzw
    obtain ⟨k, hk⟩ := sourceScalarRightDoubleMap_fundamental_fibers S
      (sourceFundamentalRepresentative_mem z) (sourceFundamentalRepresentative_mem w) hrep
    refine ⟨(sourceFundamentalTransport w)⁻¹ * k * sourceFundamentalTransport z, ?_⟩
    simp only [map_mul, mul_smul, sourceFundamentalRepresentative] at hk ⊢
    rw [hk]
    simp
  · rintro ⟨g, rfl⟩
    exact (orbitAssembledScalar_invariant S hconsistent g z).symm

theorem orbitAssembledScalar_fuchsianOne
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    orbitAssembledScalar S (fuchsianOneFixedPoint : ℂ) = 0 := by
  rw [orbitAssembledScalar_eq_rightDouble_on_fundamental S hconsistent
    (Or.inl fuchsianOneFixedPoint_mem_fundamentalTriangle)]
  rw [sourceScalarRightDoubleMap_eq_seed_of_re_le_public S
    fuchsianOneFixedPoint_mem_fundamentalTriangle.2.1]
  exact sourceScalarTriangleMap_fuchsianOne S

theorem orbitAssembledScalar_fuchsianTwo
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    orbitAssembledScalar S (fuchsianTwoFixedPoint : ℂ) = 1 := by
  rw [orbitAssembledScalar_eq_rightDouble_on_fundamental S hconsistent
    (Or.inl fuchsianTwoFixedPoint_mem_fundamentalTriangle)]
  rw [sourceScalarRightDoubleMap_eq_seed_of_re_le_public S
    fuchsianTwoFixedPoint_mem_fundamentalTriangle.2.1]
  exact sourceScalarTriangleMap_fuchsianTwo S


end SphereSixComplex.Periods.SourceChamberTopology
