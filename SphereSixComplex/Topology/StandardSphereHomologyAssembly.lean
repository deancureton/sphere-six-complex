/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Topology.StandardSphereHomologyZero
public import SphereSixComplex.Topology.StandardSpherePositiveHomology

/-!
# Assembly of the standard sphere's Section 7 homology realization

The degree-zero comparison is already unconditional. The positive-degree Mayer--Vietoris output
then supplies the top class and all remaining vanishing statements. This file packages those
facts using the graded algebra from `SectionSevenLerayRealization`.
-/

namespace SphereSixComplex

noncomputable section

/-- The positive-degree calculation, together with the proved degree-zero comparison, realizes
the Section 7 graded group as the integral singular homology of the standard six-sphere. -/
public theorem SixSpherePositiveHomologyInputs.sectionSevenHomologyRealization
    (h : SixSpherePositiveHomologyInputs) : SectionSevenHomologyRealization SixSphere := by
  intro k
  by_cases hkZero : k = 0
  · subst k
    exact sixSphere_sectionSevenHomologyRealization_zero
  by_cases hkSix : k = 6
  · subst k
    obtain ⟨e⟩ := h.degreeSix
    exact ⟨e.trans sectionSevenComputedHomologySixEquivInteger.symm⟩
  · let _ : Subsingleton (IntegralSingularHomology k SixSphere) :=
      h.otherDegrees k hkZero hkSix
    let _ : Subsingleton (SectionSevenComputedHomology k) :=
      sectionSevenComputedHomology_middle_subsingleton k hkZero hkSix
    exact ⟨sectionSevenSubsingletonAddEquiv _ _⟩

/-- The exact standard hemisphere Mayer--Vietoris outputs imply the former broad sphere-side
Section 7 realization assumption. -/
public theorem StandardSphereMayerVietorisInputs.sectionSevenHomologyRealization
    (h : StandardSphereMayerVietorisInputs) : SectionSevenHomologyRealization SixSphere :=
  (sixSpherePositiveHomologyInputs_of_mayerVietorisInputs h).sectionSevenHomologyRealization

/-- A propositionally packaged standard hemisphere calculation also supplies the sphere-side
Section 7 realization. -/
public theorem sixSphere_sectionSevenHomologyRealization_of_mayerVietorisInputs
    (h : Nonempty StandardSphereMayerVietorisInputs) :
    SectionSevenHomologyRealization SixSphere := by
  obtain ⟨h⟩ := h
  exact h.sectionSevenHomologyRealization

end

end SphereSixComplex
