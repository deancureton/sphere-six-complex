module

public import SphereSixComplex.Topology.EstablishedEquivariantUniversalCover
public import SphereSixComplex.Topology.PaperVanKampenAlgebraAdapter
public import SphereSixComplex.Topology.PaperActualCuspCentralBaseMap

/-!
# The affine fundamental-group data of the paper's central family

The generic punctured-Fuchsian universal-cover classification specializes to the period family
selected by the paper.  Its free meridians have precisely the two integral monodromy matrices
used by the final van Kampen calculation.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open ComplexTorus GlobalTorusFamily
open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup

variable (A : PaperAnalyticData)

/-- The chosen affine universal cover of the paper's punctured central family. -/
public noncomputable def centralAffineUniversalCover :=
  establishedPuncturedGlobalFamilyEquivariantUniversalCover A.periods

/-- A chosen point of the affine universal cover above the actual cusp-overlap base. -/
public noncomputable def centralAffineUniversalCoverPoint :
    A.centralAffineUniversalCover.Cover := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  exact Classical.choose (D.data.quotientCovering.surjective A.actualCuspCentralBase)

@[simp]
public theorem centralAffineUniversalCoverPoint_projects :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    D.data.projection A.centralAffineUniversalCoverPoint = A.actualCuspCentralBase := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  exact Classical.choose_spec
    (D.data.quotientCovering.surjective A.actualCuspCentralBase)

/-- The induced base point in the actual central family. -/
public noncomputable def centralAffineBase : A.CentralFamily := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  exact D.data.projection A.centralAffineUniversalCoverPoint

@[simp]
public theorem centralAffineBase_eq_actualCuspCentralBase :
    A.centralAffineBase = A.actualCuspCentralBase := by
  exact A.centralAffineUniversalCoverPoint_projects

/-- The two free meridians and the period lattice give the actual central-family
fundamental-group presentation. -/
public noncomputable def centralAffineCorePiOneData :
    AffineTorusCorePiOneData (FundamentalGroup A.CentralFamily A.centralAffineBase)
      Lattice paperMonodromyOne paperMonodromyTwo := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let C := D.data.fundamentalGroupCorePiOneData A.centralAffineUniversalCoverPoint
  have hOne :
      firstFreeMonodromy
          (freeTwoMeridianMonodromy (twoMeridianOrbifoldMap g₁ g₂)
            integralOrbifoldPeriodMonodromy) =
        paperMonodromyOne := by
    apply AddMonoidHom.ext
    intro a
    simp [firstFreeMonodromy, freeTwoMeridianMonodromy,
      integralOrbifoldPeriodMonodromy, paperMonodromyOne]
  have hTwo :
      secondFreeMonodromy
          (freeTwoMeridianMonodromy (twoMeridianOrbifoldMap g₁ g₂)
            integralOrbifoldPeriodMonodromy) =
        paperMonodromyTwo := by
    apply AddMonoidHom.ext
    intro a
    simp [secondFreeMonodromy, freeTwoMeridianMonodromy,
      integralOrbifoldPeriodMonodromy, paperMonodromyTwo]
  change AffineTorusCorePiOneData
    (FundamentalGroup (PuncturedGlobalFamily A.periods)
      (D.data.projection A.centralAffineUniversalCoverPoint))
    Lattice paperMonodromyOne paperMonodromyTwo
  exact {
    translation := C.translation
    rhoOne := C.rhoOne
    rhoTwo := C.rhoTwo
    conjugate_one := fun a ↦ by simpa only [hOne] using C.conjugate_one a
    conjugate_two := fun a ↦ by simpa only [hTwo] using C.conjugate_two a
    generators_generate := C.generators_generate
  }

/-- The lattice marking in the central fundamental-group presentation is the lattice subgroup
of the selected affine deck group. -/
public theorem centralAffineCorePiOneData_translation_deck (a : Lattice) :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.centralAffineUniversalCoverPoint, rfl⟩
        (Additive.toMul (A.centralAffineCorePiOneData.translation a)) =
      MulOpposite.op
        (Additive.toMul
          (freeAffineTranslation (M := freeTwoMeridianMonodromy
            (twoMeridianOrbifoldMap g₁ g₂) integralOrbifoldPeriodMonodromy) a)) := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  change D.data.quotientCovering.fundamentalGroupEquiv
      ⟨A.centralAffineUniversalCoverPoint, rfl⟩
      ((D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.centralAffineUniversalCoverPoint, rfl⟩).symm
        (MulOpposite.op
          (Additive.toMul
            (freeAffineTranslation (M := freeTwoMeridianMonodromy
              (twoMeridianOrbifoldMap g₁ g₂) integralOrbifoldPeriodMonodromy) a)))) = _
  exact (D.data.quotientCovering.fundamentalGroupEquiv
    ⟨A.centralAffineUniversalCoverPoint, rfl⟩).apply_symm_apply _

/-- The first marked core meridian is the inverse first free deck lift, in covering-space
orientation. -/
public theorem centralAffineCorePiOneData_rhoOne_deck :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.centralAffineUniversalCoverPoint, rfl⟩
        A.centralAffineCorePiOneData.rhoOne =
      MulOpposite.op
        (freeAffineLift (M := freeTwoMeridianMonodromy
          (twoMeridianOrbifoldMap g₁ g₂) integralOrbifoldPeriodMonodromy)
          firstMeridian)⁻¹ := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  change D.data.quotientCovering.fundamentalGroupEquiv
      ⟨A.centralAffineUniversalCoverPoint, rfl⟩
      ((D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.centralAffineUniversalCoverPoint, rfl⟩).symm
        (MulOpposite.op
          (freeAffineLift (M := freeTwoMeridianMonodromy
            (twoMeridianOrbifoldMap g₁ g₂) integralOrbifoldPeriodMonodromy)
            firstMeridian)⁻¹)) = _
  exact (D.data.quotientCovering.fundamentalGroupEquiv
    ⟨A.centralAffineUniversalCoverPoint, rfl⟩).apply_symm_apply _

/-- The second marked core meridian is the inverse second free deck lift, in covering-space
orientation. -/
public theorem centralAffineCorePiOneData_rhoTwo_deck :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.centralAffineUniversalCoverPoint, rfl⟩
        A.centralAffineCorePiOneData.rhoTwo =
      MulOpposite.op
        (freeAffineLift (M := freeTwoMeridianMonodromy
          (twoMeridianOrbifoldMap g₁ g₂) integralOrbifoldPeriodMonodromy)
          secondMeridian)⁻¹ := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  change D.data.quotientCovering.fundamentalGroupEquiv
      ⟨A.centralAffineUniversalCoverPoint, rfl⟩
      ((D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.centralAffineUniversalCoverPoint, rfl⟩).symm
        (MulOpposite.op
          (freeAffineLift (M := freeTwoMeridianMonodromy
            (twoMeridianOrbifoldMap g₁ g₂) integralOrbifoldPeriodMonodromy)
            secondMeridian)⁻¹)) = _
  exact (D.data.quotientCovering.fundamentalGroupEquiv
    ⟨A.centralAffineUniversalCoverPoint, rfl⟩).apply_symm_apply _

end SphereSixComplex.Geometry.PaperAnalyticData

end
