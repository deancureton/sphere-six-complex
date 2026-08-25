module

public import SphereSixComplex.Topology.GeometricOrientedHCobordismSixGluing
public import SphereSixComplex.Topology.FramedBordismSixReduction

/-!
# The unconditional genuine geometric `Theta₆` endpoint

Smooth closed-boundary gluing is now constructed, so the representative-level route to
`Theta₆ = 0` can use the one-step relation of actual oriented smooth h-cobordisms directly.
This file specializes the earlier conditional quotient adapters to that unconditional relation.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

namespace OrientedMarkedSmoothHomotopySixSphere

/-- Genuine oriented smooth h-cobordism is now an equivalence relation: composition is supplied
by the constructed smooth gluing. -/
public theorem smoothHCobordant_equivalence (D : SixSphereDegreeTheory) :
    Equivalence (SmoothHCobordant D) where
  refl := SmoothHCobordant.refl D
  symm := fun h ↦ SmoothHCobordant.symm h
  trans := fun h₀₁ h₁₂ ↦ by
    obtain ⟨B₀₁⟩ := h₀₁
    obtain ⟨B₁₂⟩ := h₁₂
    exact ⟨SmoothHCobordism.glue B₀₁ B₁₂⟩

/-- Consequently the equivalence closure presentation and the one-step presentation have exactly
the same setoid, rather than merely maps between their quotients. -/
public theorem generatedGeometric_setoid_eq_unconditionalGeometric
    (D : SixSphereDegreeTheory) :
    (generatedGeometricSmoothHCobordismRelation D).setoid =
      (unconditionalGeometricSmoothHCobordismRelation D).setoid := by
  apply Setoid.ext
  intro X Y
  exact (smoothHCobordant_equivalence D).eqvGen_iff

/-- Triviality of the generated and one-step quotients is literally the same proposition after
the completed gluing theorem. -/
public theorem generatedGeometricThetaSixVanishes_iff_unconditionalGeometric
    (D : SixSphereDegreeTheory) :
    (generatedGeometricSmoothHCobordismRelation D).ThetaSixVanishes ↔
      (unconditionalGeometricSmoothHCobordismRelation D).ThetaSixVanishes := by
  change Subsingleton (Quotient
      (generatedGeometricSmoothHCobordismRelation D).setoid) ↔
    Subsingleton (Quotient
      (unconditionalGeometricSmoothHCobordismRelation D).setoid)
  rw [generatedGeometric_setoid_eq_unconditionalGeometric D]

/-- The one-step genuine relation forgets the auxiliary marking choice by the same explicit
marking-change cylinder used for the generated presentation. -/
public theorem unconditionalGeometric_markingIndependence
    (D : SixSphereDegreeTheory) :
    (unconditionalGeometricSmoothHCobordismRelation D).MarkingIndependenceObligation D := by
  intro X e h
  exact ⟨SmoothHCobordism.cylinderChangeMarking D X e h⟩

/-- Genuine h-cobordisms from all representatives to the standard sphere kill the unconditional
one-step geometric quotient. -/
public theorem unconditionalGeometricThetaSixVanishes_of_hCobordant_standard
    (D : SixSphereDegreeTheory)
    (hStandard : ∀ X : OrientedMarkedSmoothHomotopySixSphere.{0},
      SmoothHCobordant D X OrientedMarkedSmoothHomotopySixSphere.standard) :
    (unconditionalGeometricSmoothHCobordismRelation D).ThetaSixVanishes :=
  geometricThetaSixVanishes_of_hCobordant_standard D
    (smoothHCobordismGluingTheorem D) hStandard

/-- The same representative theorem discharges the repository's compatibility quotient through
the genuine one-step relation. -/
public theorem unconditionalGeometricThetaSixVanishesAdapter_of_hCobordant_standard
    (D : SixSphereDegreeTheory)
    (hStandard : ∀ X : OrientedMarkedSmoothHomotopySixSphere.{0},
      SmoothHCobordant D X OrientedMarkedSmoothHomotopySixSphere.standard) :
    SmoothHCobordismRelation.ThetaSixVanishes
      (unconditionalGeometricSmoothHCobordismRelation D).toSmoothHCobordismRelation :=
  OrientedSmoothHCobordismRelation.thetaSixVanishes_toSmoothHCobordismRelation
    (unconditionalGeometricSmoothHCobordismRelation D)
    (unconditionalGeometricThetaSixVanishes_of_hCobordant_standard D hStandard)

/-- Stable framing, framed null-bordism, surgery, and puncturing kill the actual one-step
geometric h-cobordism quotient; no generated closure or gluing hypothesis remains. -/
public theorem unconditionalGeometricThetaSixVanishes_of_framedBordism_and_surgery
    (D : SixSphereDegreeTheory)
    (hStable : HomotopySixSpheresStablyParallelizable)
    (hPT : StableFramingsBoundParallelizableSevenManifolds)
    (hSurgery : ParallelizableFillingSurgeryToContractible)
    (hPuncture : ContractibleFillingPuncturesToHCobordism D) :
    (unconditionalGeometricSmoothHCobordismRelation D).ThetaSixVanishes :=
  unconditionalGeometricThetaSixVanishes_of_hCobordant_standard D
    (hCobordant_standard_of_framedBordism_and_surgery
      D hStable hPT hSurgery hPuncture)

/-- End-to-end adapter from the four remaining representative-level geometric inputs to the
public compatibility endpoint, now using the actual one-step h-cobordism relation. -/
public theorem unconditionalGeometricThetaSixVanishesAdapter_of_framedBordism_and_surgery
    (D : SixSphereDegreeTheory)
    (hStable : HomotopySixSpheresStablyParallelizable)
    (hPT : StableFramingsBoundParallelizableSevenManifolds)
    (hSurgery : ParallelizableFillingSurgeryToContractible)
    (hPuncture : ContractibleFillingPuncturesToHCobordism D) :
    SmoothHCobordismRelation.ThetaSixVanishes
      (unconditionalGeometricSmoothHCobordismRelation D).toSmoothHCobordismRelation :=
  unconditionalGeometricThetaSixVanishesAdapter_of_hCobordant_standard D
    (hCobordant_standard_of_framedBordism_and_surgery
      D hStable hPT hSurgery hPuncture)

end OrientedMarkedSmoothHomotopySixSphere

end SphereSixComplex
