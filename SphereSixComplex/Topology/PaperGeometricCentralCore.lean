module

public import SphereSixComplex.Topology.PaperGeometricCentralMonodromy

/-!
# Geometric generators for the actual central family

The marked zero section already supplies geometric lattice translations and two concrete
finite-puncture meridians.  This file transports them to the selected actual cusp point and
proves, without a chosen universal cover, that they generate the full central fundamental group.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData SphereSixComplex.Topology

variable (A : PaperAnalyticData)

/-- The marked lattice translations transported to the selected actual cusp point. -/
public noncomputable def geometricCentralTranslation :
    Lattice →+ Additive
      (FundamentalGroup A.CentralFamily A.actualCuspCentralBase) :=
  A.markedCentralToActualCuspEquiv.toMonoidHom.toAdditive.comp
    A.markedCentralTranslation

/-- At the marked zero-section point, the geometric translations and the two concrete finite
meridians generate the central fundamental group. -/
public theorem markedCentralFundamentalGroup_generated_by_translations_and_meridians :
    Subgroup.closure
      (Set.range (fun a ↦ Additive.toMul (A.markedCentralTranslation a)) ∪
        {A.markedZeroCentralMeridianClass⁻¹,
          A.markedOneCentralMeridianClass⁻¹}) = ⊤ := by
  let K := Subgroup.closure
    (Set.range (fun a ↦ Additive.toMul (A.markedCentralTranslation a)) ∪
      {A.markedZeroCentralMeridianClass⁻¹,
        A.markedOneCentralMeridianClass⁻¹})
  have hzeroInv : A.markedZeroCentralMeridianClass⁻¹ ∈ K := by
    apply Subgroup.subset_closure
    simp
  have honeInv : A.markedOneCentralMeridianClass⁻¹ ∈ K := by
    apply Subgroup.subset_closure
    simp
  have hzero : A.markedZeroCentralMeridianClass ∈ K := by
    simpa using K.inv_mem hzeroInv
  have hone : A.markedOneCentralMeridianClass ∈ K := by
    simpa using K.inv_mem honeInv
  have hfinite :
      Subgroup.closure ({A.markedZeroCentralMeridianClass,
        A.markedOneCentralMeridianClass} :
          Set (FundamentalGroup A.CentralFamily
            (A.centralZeroSection A.markedPuncturedBasepoint))) ≤ K := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with rfl | rfl
    · exact hzero
    · exact hone
  have hle :
      Subgroup.closure
        (Set.range (fun a ↦ Additive.toMul (A.markedCentralTranslation a)) ∪
          Set.range A.centralZeroSectionFundamentalGroupMap) ≤ K := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with hg | hg
    · apply Subgroup.subset_closure
      exact Or.inl hg
    · exact hfinite
        (A.centralZeroSectionFundamentalGroupMap_range_le_markedClosure hg)
  change K = ⊤
  apply top_unique
  intro g _
  apply hle
  rw [A.markedCentralFundamentalGroup_generated_by_translations_and_zeroSection]
  trivial

/-- At the actual cusp point, the transported lattice translations and the two concrete finite
meridians generate the full central fundamental group. -/
public theorem geometricCentralFundamentalGroup_generated :
    Subgroup.closure
      (Set.range (fun a ↦ Additive.toMul (A.geometricCentralTranslation a)) ∪
        {A.geometricCentralRhoOne, A.geometricCentralRhoTwo}) = ⊤ := by
  let E := A.markedCentralToActualCuspEquiv
  let K := Subgroup.closure
    (Set.range (fun a ↦ Additive.toMul (A.geometricCentralTranslation a)) ∪
      {A.geometricCentralRhoOne, A.geometricCentralRhoTwo})
  let S : Set (FundamentalGroup A.CentralFamily
      (A.centralZeroSection A.markedPuncturedBasepoint)) :=
    Set.range (fun a ↦ Additive.toMul (A.markedCentralTranslation a)) ∪
      {A.markedZeroCentralMeridianClass⁻¹,
        A.markedOneCentralMeridianClass⁻¹}
  have hle : Subgroup.closure S ≤ K.comap E.toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change E g ∈ K
    apply Subgroup.subset_closure
    rcases hg with ⟨a, rfl⟩ | hg
    · apply Or.inl
      refine ⟨a, ?_⟩
      rfl
    · rcases hg with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  change K = ⊤
  apply top_unique
  intro g _
  obtain ⟨δ, rfl⟩ := E.surjective g
  apply hle
  rw [A.markedCentralFundamentalGroup_generated_by_translations_and_meridians]
  trivial

end SphereSixComplex.Geometry.PaperAnalyticData

end
