module

public import SphereSixComplex.Topology.SphereSimplyConnected
public import SphereSixComplex.Topology.StableFramingHomotopySixSphereClutching
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

/-!
# The standard stereographic two-patch cover of the six-sphere

This file constructs the topological part of the hemispherical clutching presentation for the
standard `S⁶`.  The two patches are complements of antipodal poles, hence stereographically
homeomorphic to `ℝ⁶`; their overlap is stereographically homeomorphic to punctured `ℝ⁶`, and polar
coordinates identify that overlap up to homotopy with `S⁵`.

The construction deliberately stops before choosing local frames of `TS⁶ ⊕ ε¹`.  It is the first
independent geometric component of the rank-seven clutching proof and fixes the exact overlap model
that the later smooth collar and transition calculations must use.
-/

@[expose] public section

noncomputable section

open Bundle ContinuousMap Metric Set
open scoped Bundle ContDiff Manifold

namespace SphereSixComplex

/-- A chosen pole of the standard six-sphere. -/
public noncomputable def sixSphereNorthPole : SixSphere := by
  refine ⟨PiLp.single 2 (0 : Fin 7) 1, ?_⟩
  simp

/-- The antipodal pole. -/
public noncomputable def sixSphereSouthPole : SixSphere :=
  -sixSphereNorthPole

@[simp]
public theorem sixSphereSouthPole_eq_neg :
    sixSphereSouthPole = -sixSphereNorthPole :=
  rfl

public theorem sixSphereNorthPole_ne_southPole :
    sixSphereNorthPole ≠ sixSphereSouthPole := by
  intro h
  have hval := congrArg (fun x : SixSphere ↦ x.1 (0 : Fin 7)) h
  norm_num [sixSphereNorthPole, sixSphereSouthPole] at hval

/-- Stereographic projection from one pole sends the antipodal pole to the origin. -/
@[simp]
public theorem sixSphereStereographic_apply_antipode (v : SixSphere) :
    sixSphereStereographic v (-v) = 0 := by
  unfold sixSphereStereographic
  simp only [stereographic']
  simp

/-- The stereographic patch omitting the north pole. -/
public def standardSixSphereNorthPatch : Set SixSphere :=
  {sixSphereNorthPole}ᶜ

/-- The stereographic patch omitting the south pole. -/
public def standardSixSphereSouthPatch : Set SixSphere :=
  {sixSphereSouthPole}ᶜ

public theorem standardSixSphereNorthPatch_isOpen :
    IsOpen standardSixSphereNorthPatch := by
  exact isOpen_compl_singleton

public theorem standardSixSphereSouthPatch_isOpen :
    IsOpen standardSixSphereSouthPatch := by
  exact isOpen_compl_singleton

public theorem standardSixSpherePatch_cover :
    standardSixSphereNorthPatch ∪ standardSixSphereSouthPatch = Set.univ := by
  ext x
  simp only [standardSixSphereNorthPatch, standardSixSphereSouthPatch, mem_union,
    mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
  by_cases hx : x = sixSphereNorthPole
  · exact Or.inr fun hxSouth ↦
      sixSphereNorthPole_ne_southPole (hx.symm.trans hxSouth)
  · exact Or.inl hx

/-- Every one-pole complement in `S⁶` is contractible by stereographic projection. -/
public theorem sixSphere_compl_singleton_contractible (v : SixSphere) :
    ContractibleSpace ({v}ᶜ : Set SixSphere) := by
  let e := (sixSphereStereographic v).toHomeomorphSourceTarget
  rw [← sixSphereStereographic_source v]
  rw [e.toHomotopyEquiv.contractibleSpace_iff]
  rw [sixSphereStereographic_target]
  exact (Homeomorph.Set.univ RealModel).contractibleSpace

/-- The chosen north patch is contractible. -/
public theorem standardSixSphereNorthPatch_contractible :
    ContractibleSpace standardSixSphereNorthPatch := by
  exact sixSphere_compl_singleton_contractible sixSphereNorthPole

/-- The chosen south patch is contractible. -/
public theorem standardSixSphereSouthPatch_contractible :
    ContractibleSpace standardSixSphereSouthPatch := by
  exact sixSphere_compl_singleton_contractible sixSphereSouthPole

/-- Stereographic projection identifies the two-pole complement with punctured `ℝ⁶`. -/
public noncomputable def standardSixSphereOverlapHomeomorph :
    {x : SixSphere //
      x ∈ standardSixSphereNorthPatch ∩ standardSixSphereSouthPatch} ≃ₜ
      ({0}ᶜ : Set RealModel) := by
  let e := sixSphereStereographic sixSphereNorthPole
  apply e.homeomorphOfImageSubsetSource
  · intro x hx
    simpa [e, standardSixSphereNorthPatch] using hx.1
  · apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩ hy0
      have hxSource : x ∈ e.source := by
        simpa [e, standardSixSphereNorthPatch] using hx.1
      have hsouthSource : sixSphereSouthPole ∈ e.source := by
        simpa [e, standardSixSphereNorthPatch, sixSphereSouthPole] using
          sixSphereNorthPole_ne_southPole.symm
      have heq : x = sixSphereSouthPole :=
        e.injOn hxSource hsouthSource (by
          rw [Set.mem_singleton_iff.mp hy0]
          simp [e, sixSphereSouthPole])
      exact hx.2 (by simp [heq])
    · intro y hy
      have hyTarget : y ∈ e.target := by simp [e]
      let x : SixSphere := e.symm y
      have hxSource : x ∈ e.source := e.map_target hyTarget
      have hxy : e x = y := e.right_inv hyTarget
      refine ⟨x, ?_, hxy⟩
      constructor
      · simpa [e, standardSixSphereNorthPatch] using hxSource
      · simp only [standardSixSphereSouthPatch, mem_compl_iff, mem_singleton_iff]
        intro hxSouth
        have : y = 0 := by
          rw [← hxy, hxSouth]
          simp [e, sixSphereSouthPole]
        exact hy this

/-- Punctured real six-space deformation-retracts, up to homotopy equivalence, onto its unit
five-sphere. -/
public noncomputable def puncturedRealModelHomotopyEquivFiveSphere :
    ({0}ᶜ : Set RealModel) ≃ₕ StableClutchingEquatorFiveSphere := by
  letI : ContractibleSpace (Set.Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).contractibleSpace nonempty_Ioi
  let radial : ({0}ᶜ : Set RealModel) ≃ₕ
      StableClutchingEquatorFiveSphere × Set.Ioi (0 : ℝ) :=
    (homeomorphUnitSphereProd RealModel).toHomotopyEquiv
  let radialFactor : Set.Ioi (0 : ℝ) ≃ₕ Unit :=
    Classical.choice (ContractibleSpace.hequiv (Set.Ioi (0 : ℝ)) Unit)
  exact radial.trans
    ((ContinuousMap.HomotopyEquiv.refl StableClutchingEquatorFiveSphere).prodCongr radialFactor) |>.trans
      (Homeomorph.prodUnique StableClutchingEquatorFiveSphere Unit).toHomotopyEquiv

/-- The overlap of the two standard stereographic patches has the homotopy type of `S⁵`. -/
public noncomputable def standardSixSphereOverlapEquatorMarking :
    {x : SixSphere //
      x ∈ standardSixSphereNorthPatch ∩ standardSixSphereSouthPatch} ≃ₕ
      StableClutchingEquatorFiveSphere :=
  standardSixSphereOverlapHomeomorph.toHomotopyEquiv.trans
    puncturedRealModelHomotopyEquivFiveSphere

/-- The standard six-sphere has the topological open-cover geometry required by a hemispherical
rank-seven clutching presentation. -/
public noncomputable def standardSixSphereHemisphericalOpenCover :
    SmoothHemisphericalOpenCoverSix SixSphere where
  north := standardSixSphereNorthPatch
  south := standardSixSphereSouthPatch
  north_isOpen := standardSixSphereNorthPatch_isOpen
  south_isOpen := standardSixSphereSouthPatch_isOpen
  cover := standardSixSpherePatch_cover
  north_contractible := standardSixSphereNorthPatch_contractible
  south_contractible := standardSixSphereSouthPatch_contractible
  equatorMarking := standardSixSphereOverlapEquatorMarking

/-- The tangent-bundle chart over the north patch, stabilized by the trivial real line. -/
public noncomputable def standardSixSphereNorthStableTrivialization :
    Trivialization (RealModel × ℝ)
      (TotalSpace.proj : TotalSpace (RealModel × ℝ)
        (StabilizedTangentFiberSix SixSphere) → SixSphere) :=
  (trivializationAt RealModel
      (TangentSpace 𝓘(ℝ, RealModel)) sixSphereSouthPole).prod
    (Bundle.Trivial.trivialization SixSphere ℝ)

/-- The tangent-bundle chart over the south patch, stabilized by the trivial real line. -/
public noncomputable def standardSixSphereSouthStableTrivialization :
    Trivialization (RealModel × ℝ)
      (TotalSpace.proj : TotalSpace (RealModel × ℝ)
        (StabilizedTangentFiberSix SixSphere) → SixSphere) :=
  (trivializationAt RealModel
      (TangentSpace 𝓘(ℝ, RealModel)) sixSphereNorthPole).prod
    (Bundle.Trivial.trivialization SixSphere ℝ)

public noncomputable instance standardSixSphereTrivialLineTrivialization_memAtlas :
    MemTrivializationAtlas (Bundle.Trivial.trivialization SixSphere ℝ) where
  out := by simp

public noncomputable instance standardSixSphereNorthStableTrivialization_memAtlas :
    MemTrivializationAtlas standardSixSphereNorthStableTrivialization := by
  unfold standardSixSphereNorthStableTrivialization
  infer_instance

public noncomputable instance standardSixSphereSouthStableTrivialization_memAtlas :
    MemTrivializationAtlas standardSixSphereSouthStableTrivialization := by
  unfold standardSixSphereSouthStableTrivialization
  infer_instance

@[simp]
public theorem standardSixSphereNorthStableTrivialization_baseSet :
    standardSixSphereNorthStableTrivialization.baseSet = standardSixSphereNorthPatch := by
  simp [standardSixSphereNorthStableTrivialization, standardSixSphereNorthPatch,
    sixSphereSouthPole, chartAt, ChartedSpace.chartAt]

@[simp]
public theorem standardSixSphereSouthStableTrivialization_baseSet :
    standardSixSphereSouthStableTrivialization.baseSet = standardSixSphereSouthPatch := by
  simp [standardSixSphereSouthStableTrivialization, standardSixSphereSouthPatch,
    chartAt, ChartedSpace.chartAt]

/-- The canonical stabilized tangent frame induced by the north stereographic chart. -/
public noncomputable def standardSixSphereNorthStableSections :
    Fin 7 → (x : SixSphere) → StabilizedTangentFiberSix SixSphere x :=
  standardSixSphereNorthStableTrivialization.localFrame stabilizedRealModelBasisSix

/-- The canonical stabilized tangent frame induced by the south stereographic chart. -/
public noncomputable def standardSixSphereSouthStableSections :
    Fin 7 → (x : SixSphere) → StabilizedTangentFiberSix SixSphere x :=
  standardSixSphereSouthStableTrivialization.localFrame stabilizedRealModelBasisSix

/-- The north stereographic sections form a smooth local stable frame. -/
public theorem standardSixSphereNorthStableFrame :
    IsLocalFrameOn 𝓘(ℝ, RealModel) (RealModel × ℝ) ∞
      standardSixSphereNorthStableSections standardSixSphereNorthPatch := by
  simpa only [standardSixSphereNorthStableSections,
    standardSixSphereNorthStableTrivialization_baseSet] using
    standardSixSphereNorthStableTrivialization.isLocalFrameOn_localFrame_baseSet
      𝓘(ℝ, RealModel) ∞ stabilizedRealModelBasisSix

/-- The south stereographic sections form a smooth local stable frame. -/
public theorem standardSixSphereSouthStableFrame :
    IsLocalFrameOn 𝓘(ℝ, RealModel) (RealModel × ℝ) ∞
      standardSixSphereSouthStableSections standardSixSphereSouthPatch := by
  simpa only [standardSixSphereSouthStableSections,
    standardSixSphereSouthStableTrivialization_baseSet] using
    standardSixSphereSouthStableTrivialization.isLocalFrameOn_localFrame_baseSet
      𝓘(ℝ, RealModel) ∞ stabilizedRealModelBasisSix

/-- The complete two-chart rank-seven clutching presentation for the standard six-sphere. -/
public noncomputable def standardSixSphereRankSevenClutchingPresentation :
    SmoothRankSevenClutchingPresentationSix SixSphere where
  north := standardSixSphereNorthPatch
  south := standardSixSphereSouthPatch
  north_isOpen := standardSixSphereNorthPatch_isOpen
  south_isOpen := standardSixSphereSouthPatch_isOpen
  cover := standardSixSpherePatch_cover
  northSections := standardSixSphereNorthStableSections
  southSections := standardSixSphereSouthStableSections
  northFrame := standardSixSphereNorthStableFrame
  southFrame := standardSixSphereSouthStableFrame

/-- The standard sphere satisfies every field of the hemispherical clutching presentation. -/
public noncomputable def standardSixSphereHemisphericalRankSevenClutchingPresentation :
    SmoothHemisphericalRankSevenClutchingPresentationSix SixSphere where
  toClutchingPresentation := standardSixSphereRankSevenClutchingPresentation
  north_contractible := standardSixSphereNorthPatch_contractible
  south_contractible := standardSixSphereSouthPatch_contractible
  equatorMarking := standardSixSphereOverlapEquatorMarking

end SphereSixComplex
