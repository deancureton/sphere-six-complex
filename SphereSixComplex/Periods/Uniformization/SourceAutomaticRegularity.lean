module

public import SphereSixComplex.Periods.Uniformization.ExactSourceAssembly
import all SphereSixComplex.Periods.Uniformization.ExactSourceAssembly
public import SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
import all SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

@[expose] public section

/-!
# Automatic regularity of an exact-orbit scalar coordinate

For the explicit Fuchsian action, proper discontinuity and exact orbit fibres force a globally
open invariant coordinate to be a local homeomorphism away from the two elliptic values.  This
removes the ordinary-locus local-homeomorphism field from the analytic Schwarz construction.
-/

open Set Topology

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FreeProductTorsion
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.Periods.ExactSourceAssembly

/-- Exact orbit fibres and proper discontinuity make the coordinate locally injective on the
ordinary locus; openness then upgrades this to a local homeomorphism. -/
theorem regular_localHomeomorph_of_exact_orbits
    (coordinate : UpperHalfPlane → ℂ)
    (hcontinuous : Continuous coordinate)
    (hopen : IsOpenMap coordinate)
    (hinvariant : ∀ g z,
      coordinate (fuchsianSourceAction g • z) = coordinate z)
    (hfibres : ∀ z w,
      coordinate z = coordinate w ↔
        ∃ g : Delta, fuchsianSourceAction g • z = w)
    (hone : coordinate fuchsianOneFixedPoint = 0)
    (htwo : coordinate fuchsianTwoFixedPoint = 1) :
    IsLocalHomeomorph
      (sourceRegularValueSet.restrictPreimage coordinate) := by
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g ↦ (fuchsianSourceAction_contMDiff g 0).continuous⟩
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    fuchsianSourceAction_properlyDiscontinuous
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro x
  obtain ⟨U, hU_nhds, hU⟩ :=
    ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self Delta x.1
  let V : Set {z : UpperHalfPlane // coordinate z ∈ sourceRegularValueSet} :=
    ((↑) : {z : UpperHalfPlane // coordinate z ∈ sourceRegularValueSet} →
      UpperHalfPlane) ⁻¹' interior U
  have hxU : x.1 ∈ interior U := mem_interior_iff_mem_nhds.mpr hU_nhds
  have hV_nhds : V ∈ 𝓝 x := by
    exact (isOpen_interior.preimage continuous_subtype_val).mem_nhds hxU
  refine ⟨V, hV_nhds, ?_⟩
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (hcontinuous.restrictPreimage :
      Continuous (sourceRegularValueSet.restrictPreimage coordinate)).comp
        continuous_subtype_val
  · intro z w hzw
    apply Subtype.ext
    apply Subtype.ext
    have hcoord : coordinate z.1 = coordinate w.1 :=
      congrArg Subtype.val hzw
    obtain ⟨g, hg⟩ := (hfibres z.1 w.1).mp hcoord
    have hregular : IsFuchsianRegularPoint x.1 := by
      intro k
      constructor
      · intro hk
        have hzero : coordinate x.1 = 0 := by
          rw [← hone, ← hk]
          exact (hinvariant k x.1).symm
        have hxreg := x.2
        change coordinate x.1 ∉ ({0, 1} : Set ℂ) at hxreg
        exact hxreg (by simp [hzero])
      · intro hk
        have hone' : coordinate x.1 = 1 := by
          rw [← htwo, ← hk]
          exact (hinvariant k x.1).symm
        have hxreg := x.2
        change coordinate x.1 ∉ ({0, 1} : Set ℂ) at hxreg
        exact hxreg (by simp [hone'])
    have hinter : (((g • ·) '' U) ∩ U).Nonempty := by
      refine ⟨w.1, ?_, interior_subset w.2⟩
      refine ⟨z.1, interior_subset z.2, ?_⟩
      change (fuchsianSourceAction g) z.1 = w.1
      exact hg
    have hgfix : (fuchsianSourceAction g) x.1 = x.1 := by
      exact hU g hinter
    have gone : g = 1 :=
      fuchsian_fixed_regular_eq_one fuchsianSourceAction_properlyDiscontinuous
        hregular hgfix
    simpa [gone] using hg
  · exact (hopen.restrictPreimage sourceRegularValueSet).domRestrict
      (isOpen_interior.preimage continuous_subtype_val)


end SphereSixComplex.Periods.SourceChamberTopology
