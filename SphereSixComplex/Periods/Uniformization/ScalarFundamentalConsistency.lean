module

public import SphereSixComplex.Periods.Uniformization.ScalarMonodromyAssembly
import all SphereSixComplex.Periods.Uniformization.ScalarMonodromyAssembly

@[expose] public section

/-!
# Scalar consistency from the geometric side-pairing classification

The scalar argument and the fundamental-polygon argument are separated here.  The only geometric
input is that two orbit-equivalent points in the doubled closed polygon are either equal or are
the two mirror images of one boundary point of the original reflection triangle.  The explicit
right Schwarz double then gives equal values on every listed pair.

`ScalarMonodromyAssembly` transitively imports Tau Ceti's complex continuation and Schwarz
reflection APIs.  This file adds no new Tau Ceti import.
-/

open Complex Metric Set Topology UpperHalfPlane
open scoped ComplexConjugate

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover
open SphereSixComplex.Periods.TriangleReflections

/-- Purely geometric form of uniqueness for the doubled closed fundamental polygon.  Its only
nontrivial identifications are a point of the boundary of the original reflection triangle and
its image under reflection in the right side. -/
def SourceOrientedFundamentalPairingClassification : Prop :=
  ∀ {z w : UpperHalfPlane}, z ∈ orientedFundamentalRegion →
    w ∈ orientedFundamentalRegion →
    (∃ g : Delta, fuchsianSourceAction g • z = w) →
      z = w ∨
        ∃ u : UpperHalfPlane, u ∈ fundamentalTriangle ∧
          (u : ℂ) ∉ sourceOpenChamber ∧
          ((z = u ∧ w = sourceRightUHP u) ∨
            (z = sourceRightUHP u ∧ w = u))

/-- Every finite boundary point of the closed source reflection triangle has real scalar value. -/
theorem sourceScalarTriangleMap_im_eq_zero_of_mem_fundamental_not_open_public
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    {z : UpperHalfPlane} (hz : z ∈ fundamentalTriangle)
    (hnot : (z : ℂ) ∉ sourceOpenChamber) :
    (sourceScalarTriangleMap S (z : ℂ)).im = 0 := by
  rcases hz with ⟨hl, hr, hn⟩
  by_cases hcircle : normSq (z : ℂ) = 1
  · exact sourceScalarTriangleMap_im_eq_zero_of_circleSide S hl hr z.im_pos hcircle
  have hn' : 1 < normSq (z : ℂ) := lt_of_le_of_ne hn (Ne.symm hcircle)
  by_cases hleft : (z : ℂ).re = -Real.sqrt 2 / 2
  · exact sourceScalarTriangleMap_im_eq_zero_of_leftSide S hleft z.im_pos hn'
  by_cases hright : (z : ℂ).re = 1 / 2
  · exact sourceScalarTriangleMap_im_eq_zero_of_rightSide S hright z.im_pos hn'
  exact (hnot ⟨lt_of_le_of_ne hl (Ne.symm hleft),
    lt_of_le_of_ne hr hright, z.im_pos, hn'⟩).elim

/-- The total right Schwarz double takes the right reflection of every point in the closed
source triangle to the conjugate scalar value, including the fixed right side itself. -/
theorem sourceScalarRightDoubleMap_reflected_fundamental_public
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    {z : UpperHalfPlane} (hz : z ∈ fundamentalTriangle) :
    sourceScalarRightDoubleMap S (sourceRight (z : ℂ)) =
      (starRingEnd ℂ) (sourceScalarTriangleMap S (z : ℂ)) := by
  rcases lt_or_eq_of_le hz.2.1 with hright | hright
  · change (z : ℂ).re < 1 / 2 at hright
    have hcoord : (((sourceRight (z : ℂ)) - (1 / 2 : ℂ)) / Complex.I).im < 0 := by
      rw [sourceRight_coord_im, sourceRight_re]
      linarith
    rw [sourceScalarRightDoubleMap]
    rw [TauCeti.lineSchwarzReflection_of_coord_im_neg
      (f := sourceScalarTriangleMap S) hcoord]
    simp only [sub_zero, div_one, one_mul, zero_add]
    rw [sourceRight_affineReflection, sourceRight_involutive]
  · have hnot : (z : ℂ) ∉ sourceOpenChamber := by
      intro h
      exact (ne_of_lt h.2.1) hright
    have him :=
      sourceScalarTriangleMap_im_eq_zero_of_mem_fundamental_not_open_public S hz hnot
    change (z : ℂ).re = 1 / 2 at hright
    have hfix : sourceRight (z : ℂ) = z := by
      apply Complex.ext
      · rw [sourceRight_re, hright]
        norm_num
      · simp [sourceRight]
    rw [hfix, sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hz.2.1]
    rw [starRingEnd_apply, Complex.star_def]
    exact (Complex.conj_eq_iff_im.mpr him).symm

/-- The scalar double identifies a boundary point of the original triangle with its reflection
in the right side. -/
theorem sourceScalarRightDoubleMap_eq_sourceRight_of_mem_fundamental_not_open
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    {z : UpperHalfPlane} (hz : z ∈ fundamentalTriangle)
    (hnot : (z : ℂ) ∉ sourceOpenChamber) :
    sourceScalarRightDoubleMap S (z : ℂ) =
      sourceScalarRightDoubleMap S (sourceRightUHP z : ℂ) := by
  have hleft : sourceScalarRightDoubleMap S (z : ℂ) =
      sourceScalarTriangleMap S (z : ℂ) :=
    sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hz.2.1
  have hright := sourceScalarRightDoubleMap_reflected_fundamental_public S hz
  have him :=
    sourceScalarTriangleMap_im_eq_zero_of_mem_fundamental_not_open_public S hz hnot
  rw [hleft]
  change sourceScalarTriangleMap S (z : ℂ) =
    sourceScalarRightDoubleMap S (sourceRight (z : ℂ))
  rw [hright, starRingEnd_apply, Complex.star_def,
    Complex.conj_eq_iff_im.mpr him]

/-- The pure fundamental-polygon pairing classification is sufficient for scalar consistency. -/
theorem sourceFundamentalScalarConsistent_of_pairingClassification
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hclass : SourceOrientedFundamentalPairingClassification) :
    SourceFundamentalScalarConsistent S := by
  intro z w hz hw horbit
  rcases hclass hz hw horbit with hzw | ⟨u, hu, hunopen, hpair⟩
  · simpa [hzw]
  have hscalar :=
    sourceScalarRightDoubleMap_eq_sourceRight_of_mem_fundamental_not_open S hu hunopen
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hscalar
  · exact hscalar.symm


end SphereSixComplex.Periods.SourceChamberTopology
