module

public import SphereSixComplex.Topology.CuspFiniteFiberSpecializationGeometricReduction
public import SphereSixComplex.Topology.PaperCuspMarkedFiberAngularVanishingProof

/-!
# The degree-two cusp specialization fields

The degree-two part of the remaining cusp specialization geometry is reduced to four literal
marked-fibre images.  Once these four classes are the selected cellular basis of the toric
filling, the fibre restriction is an isomorphism.  Surjectivity of total specialization and a
killed Wang section are then formal consequences of Wang exactness.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex
open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  {W : ActualPuncturedCuspCollarWitness N M}

namespace CuspFiberSpecializationNormalization

/-- The selected cellular coordinates on the second homology of the actual cusp filling. -/
public noncomputable def degreeTwoCuspFillingCoordinates
    (_G : ActualCuspRadialClutchingData W) :
    IntegralSingularHomology 2 (actualLocalCuspFilling W) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (actualLocalCuspFillingHomologyTwoEquiv W
    (UnnormalizedCuspRadialClutchingData.radialCentralFiberRetractionData W)).toIntLinearEquiv

/-- The exact point-set residue in degree two: the four standard marked-torus classes map to
the four selected cellular classes of the toric filling. -/
public def DegreeTwoMarkedFiberBasisImages
    (G : ActualCuspRadialClutchingData W) : Prop :=
  let _ := G.fiberTopology
  ∀ j : Fin 4,
    degreeTwoCuspFillingCoordinates G
        (integralSingularHomologyMap 2 G.markedFiberToCuspFilling
          (G.degreeTwoFiberGenerator j)) =
      (Pi.single j 1 : Fin 4 → ℤ)

private theorem linearMap_ext_of_equiv_pi_single_one
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] {n : ℕ}
    (e : A ≃ₗ[ℤ] (Fin n → ℤ)) (f g : A →ₗ[ℤ] B)
    (h : ∀ i, f (e.symm (Pi.single i 1)) = g (e.symm (Pi.single i 1))) :
    f = g := by
  apply LinearMap.ext
  intro x
  let y := e x
  have hx : x = e.symm y := by simp [y]
  rw [hx]
  apply Pi.single_induction (M := fun _ : Fin n ↦ ℤ)
    (p := fun z ↦ f (e.symm z) = g (e.symm z)) y
  · simp
  · intro a b ha hb
    simpa using congrArg₂ (· + ·) ha hb
  · intro i z
    have hz : (Pi.single i z : Fin n → ℤ) =
        z • (Pi.single i 1 : Fin n → ℤ) := by
      ext k
      classical
      by_cases hki : k = i
      · subst k
        simp
      · simp [hki]
    calc
      f (e.symm (Pi.single i z)) =
          f (e.symm (z • (Pi.single i 1 : Fin n → ℤ))) := by rw [hz]
      _ = z • f (e.symm (Pi.single i 1)) := by rw [map_zsmul, map_zsmul]
      _ = z • g (e.symm (Pi.single i 1)) := congrArg (z • ·) (h i)
      _ = g (e.symm (z • (Pi.single i 1 : Fin n → ℤ))) := by
        rw [map_zsmul, map_zsmul]
      _ = g (e.symm (Pi.single i z)) := by rw [hz]

/-- The four literal marked-fibre images determine the entire restriction of degree-two
specialization to Wang coinvariants. -/
public theorem rawDegreeTwoFiberSpecialization_eq_of_markedFiberBasisImages
    (G : ActualCuspRadialClutchingData W)
    (h : DegreeTwoMarkedFiberBasisImages G) :
    let _ := G.fiberTopology
    rawDegreeTwoFiberSpecialization G =
      (degreeTwoCuspFillingCoordinates G).symm.toLinearMap.comp
        G.degreeTwoCoinvariantsEquiv.toLinearMap := by
  let _ := G.fiberTopology
  let P := circleMappingTorusHTwoPresentation G.clutching
  apply linearMap_ext_of_equiv_pi_single_one G.degreeTwoCoinvariantsEquiv
  intro j
  apply (degreeTwoCuspFillingCoordinates G).injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [G.degreeTwoCoinvariantsEquiv.apply_symm_apply,
    (degreeTwoCuspFillingCoordinates G).apply_symm_apply]
  change degreeTwoCuspFillingCoordinates G
      (rawDegreeTwoFiberSpecialization G
        (G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1))) =
    (Pi.single j 1 : Fin 4 → ℤ)
  change degreeTwoCuspFillingCoordinates G
      (rawDegreeTwoTotalSpecialization G
        (P.coinvariantsToTotal
          (G.degreeTwoCoinvariantsEquiv.symm (Pi.single j 1)))) = _
  rw [G.degreeTwoCoinvariantsEquiv_symm_single]
  change degreeTwoCuspFillingCoordinates G
      (rawDegreeTwoTotalSpecialization G
        (integralSingularHomologyMap 2
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
          (G.degreeTwoFiberGenerator j))) = _
  change G.specializationHomologyTwoMap
      (integralSingularHomologyMap 2
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
        (G.degreeTwoFiberGenerator j)) = _
  rw [G.specializationHomologyTwoMap_fiberInclusion]
  exact h j

/-- The four literal marked-fibre images make the degree-two fibre restriction bijective. -/
public theorem rawDegreeTwoFiberSpecialization_bijective_of_markedFiberBasisImages
    (G : ActualCuspRadialClutchingData W)
    (h : DegreeTwoMarkedFiberBasisImages G) :
    let _ := G.fiberTopology
    Function.Bijective (rawDegreeTwoFiberSpecialization G) := by
  let _ := G.fiberTopology
  rw [rawDegreeTwoFiberSpecialization_eq_of_markedFiberBasisImages G h]
  exact (degreeTwoCuspFillingCoordinates G).symm.bijective.comp
    G.degreeTwoCoinvariantsEquiv.bijective

/-- Surjectivity of the fibre restriction already implies surjectivity of total degree-two
specialization. -/
public theorem rawDegreeTwoTotalSpecialization_surjective_of_fiber_surjective
    (G : ActualCuspRadialClutchingData W)
    (h : Function.Surjective (rawDegreeTwoFiberSpecialization G)) :
    Function.Surjective (rawDegreeTwoTotalSpecialization G) := by
  let _ := G.fiberTopology
  intro y
  obtain ⟨x, hx⟩ := h y
  exact ⟨(circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal x, hx⟩

/-- A bijective fibre restriction lets one correct any Wang section by a coinvariant class so
that the resulting section is killed by total specialization. -/
public theorem degreeTwo_section_of_fiberSpecialization_bijective
    (G : ActualCuspRadialClutchingData W)
    (h : Function.Bijective (rawDegreeTwoFiberSpecialization G)) :
    let _ := G.fiberTopology
    ∃ S : (circleMappingTorusHTwoPresentation G.clutching).GeometricSection,
      (rawDegreeTwoTotalSpecialization G).comp S.lift = 0 := by
  let _ := G.fiberTopology
  let P := circleMappingTorusHTwoPresentation G.clutching
  let S := EstablishedCircleMappingTorusGeometricSections.sections G.monodromyCoordinates
  let c : P.Coinvariants ≃ₗ[ℤ]
      IntegralSingularHomology 2 (actualLocalCuspFilling W) :=
    LinearEquiv.ofBijective (rawDegreeTwoFiberSpecialization G) h
  refine ⟨UnnormalizedCuspRadialClutchingData.geometricSectionInMapKernel P S.degreeTwo c
    (rawDegreeTwoTotalSpecialization G), ?_⟩
  apply UnnormalizedCuspRadialClutchingData.geometricSectionInMapKernel_lift
  rfl

/-- The four marked-fibre images supply both remaining degree-two fields. -/
public theorem degreeTwo_fields_of_markedFiberBasisImages
    (G : ActualCuspRadialClutchingData W)
    (h : DegreeTwoMarkedFiberBasisImages G) :
    Function.Surjective (rawDegreeTwoTotalSpecialization G) ∧
      (let _ := G.fiberTopology
      ∃ S : (circleMappingTorusHTwoPresentation G.clutching).GeometricSection,
        (rawDegreeTwoTotalSpecialization G).comp S.lift = 0) := by
  let _ := G.fiberTopology
  have hb := rawDegreeTwoFiberSpecialization_bijective_of_markedFiberBasisImages G h
  exact ⟨rawDegreeTwoTotalSpecialization_surjective_of_fiber_surjective G hb.2,
    degreeTwo_section_of_fiberSpecialization_bijective G hb⟩

/-- After the degree-one angular calculation, the four marked degree-two fibre images are the
only remaining input for all three fields of `RemainingFiberSpecializationGeometry`. -/
public theorem remainingFiberSpecializationGeometry_of_degreeTwoMarkedFiberBasisImages
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W)
    (h : DegreeTwoMarkedFiberBasisImages G) :
    RemainingFiberSpecializationGeometry G := by
  obtain ⟨hsurj, hsection⟩ := degreeTwo_fields_of_markedFiberBasisImages G h
  exact
    { degreeOne_section := actualCuspDegreeOne_section G b
      degreeTwo_surjective := hsurj
      degreeTwo_section := hsection }

end CuspFiberSpecializationNormalization

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end

end
