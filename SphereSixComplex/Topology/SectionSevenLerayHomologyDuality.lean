module

public import SphereSixComplex.Topology.SectionSevenLerayChainDuality

/-!
# Homology duality of the finite Leray model

The chain self-duality of the finite Section 7 model induces isomorphisms on homology in every
degree.  The morphisms of these isomorphisms are the actual `homologyMap`s of the complementary
chain maps.  They transport the sphere-shaped homology calculation to the reversed-transpose
model without any topological realization hypothesis.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

/-- The homology isomorphism induced by the explicit degree-complement chain self-duality. -/
public noncomputable def SectionSevenLerayAlgebraicDuality.homologyDegreeComplementIso
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) (k : ℕ) :
    (sectionSevenLerayChainModel top).homology k ≅
      (sectionSevenReversedDualChainModel top).homology k where
  hom := (sectionSevenLerayChainModel top).homologyMap h.chainSelfDualityIso.hom k
  inv := (sectionSevenReversedDualChainModel top).homologyMap h.chainSelfDualityIso.inv k
  hom_inv_id := by
    rw [← HomologicalComplex.homologyMap_comp, h.chainSelfDualityIso.hom_inv_id,
      HomologicalComplex.homologyMap_id]
  inv_hom_id := by
    rw [← HomologicalComplex.homologyMap_comp, h.chainSelfDualityIso.inv_hom_id,
      HomologicalComplex.homologyMap_id]

@[simp]
public theorem SectionSevenLerayAlgebraicDuality.homologyDegreeComplementIso_hom
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) (k : ℕ) :
    (h.homologyDegreeComplementIso k).hom =
      (sectionSevenLerayChainModel top).homologyMap h.chainSelfDualityIso.hom k :=
  rfl

@[simp]
public theorem SectionSevenLerayAlgebraicDuality.homologyDegreeComplementIso_inv
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) (k : ℕ) :
    (h.homologyDegreeComplementIso k).inv =
      (sectionSevenReversedDualChainModel top).homologyMap h.chainSelfDualityIso.inv k :=
  rfl

/-- The induced homology map transports middle-degree vanishing to the reversed-transpose
complex. -/
public theorem SectionSevenLerayAlgebraicDuality.reversed_middle_homology_isZero
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) (k : ℕ)
    (h1 : 1 ≤ k) (h5 : k ≤ 5) :
    IsZero ((sectionSevenReversedDualChainModel top).homology k) :=
  IsZero.of_iso (h.middle_homology_isZero k h1 h5) (h.homologyDegreeComplementIso k).symm

/-- Degree zero of the reversed-transpose model is infinite cyclic, transported along the
induced homology map. -/
public noncomputable def SectionSevenLerayAlgebraicDuality.reversed_homology_zero_equiv
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) :
    (sectionSevenReversedDualChainModel top).homology 0 ≃+ ℤ :=
  (h.homologyDegreeComplementIso 0).symm.addCommGroupIsoToAddEquiv.trans
    (sectionSevenLerayChainModel_homology_zero_equiv top)

/-- Degree six of the reversed-transpose model is infinite cyclic, transported along the
induced homology map. -/
public noncomputable def SectionSevenLerayAlgebraicDuality.reversed_homology_six_equiv
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) :
    (sectionSevenReversedDualChainModel top).homology 6 ≃+ ℤ :=
  (h.homologyDegreeComplementIso 6).symm.addCommGroupIsoToAddEquiv.trans
    (sectionSevenLerayChainModel_homology_six_equiv top)

/-- Sphere-shaped homology of the reversed-transpose finite model, obtained entirely by applying
the induced homology isomorphisms. -/
public theorem SectionSevenLerayAlgebraicDuality.reversed_sphere_shaped_model_homology
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) :
    Nonempty ((sectionSevenReversedDualChainModel top).homology 0 ≃+ ℤ) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 5 →
        IsZero ((sectionSevenReversedDualChainModel top).homology k)) ∧
      Nonempty ((sectionSevenReversedDualChainModel top).homology 6 ≃+ ℤ) :=
  ⟨⟨h.reversed_homology_zero_equiv⟩, h.reversed_middle_homology_isZero,
    ⟨h.reversed_homology_six_equiv⟩⟩

end SphereSixComplex
