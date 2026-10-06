module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Basic.Sign.Basic
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeZero
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Finset.Dedup
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeHomeomorphism
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMaps
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RadialHomotopy
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SpherePuncture
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ContractiblePair
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ContractibleCoverOne
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeFunctoriality
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereHomologyShift
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereHomologyOne
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ReducedZero
public import Mathlib.LinearAlgebra.Span.Basic
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.OneDimensionalSphere
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TwoPointReducedZero
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereRank

@[expose] public section

noncomputable section

open Metric Set Module

universe u w z v

namespace DifferentialGeometry.Topology

section

private theorem stereoInvFunAux_map
    {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E ≃ₗᵢ[ℝ] F) (v w : E) :
    stereoInvFunAux (A v) (A w) = A (stereoInvFunAux v w) := by
  simp only [stereoInvFunAux, A.norm_map, map_smul, map_add]

private theorem stereoInvFunAux_reflection
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] {v : E} (hv : v ∈ K) (w : E) :
    stereoInvFunAux v (K.reflection w) = K.reflection (stereoInvFunAux v w) := by
  simpa only [Submodule.reflection_mem_subspace_eq_self hv] using
    stereoInvFunAux_map K.reflection v w

private theorem reflection_mem_orthogonal_span
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] {v w : E}
    (hv : v ∈ K) (hw : w ∈ (ℝ ∙ v)ᗮ) : K.reflection w ∈ (ℝ ∙ v)ᗮ := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  have hinner := K.reflection.inner_map_map v w
  rw [Submodule.reflection_mem_subspace_eq_self hv] at hinner
  exact hinner.trans (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw)

private theorem spherePunctureHomeomorph_symm_reflection
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (v : sphere (0 : E) 1) (hv : (v : E) ∈ K) (w : (ℝ ∙ (v : E))ᗮ) :
    (((spherePunctureHomeomorph v).symm
        ⟨K.reflection (w : E), reflection_mem_orthogonal_span K hv w.property⟩).val : E) =
      K.reflection (((spherePunctureHomeomorph v).symm w).val : E) := by
  change stereoInvFunAux (v : E) (K.reflection (w : E)) =
    K.reflection (stereoInvFunAux (v : E) (w : E))
  exact stereoInvFunAux_reflection K hv (w : E)

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Submodule ℝ E) [K.HasOrthogonalProjection]

private def reflectionSphereHomeomorph : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 :=
  K.reflection.toHomeomorph.subtype (fun x => by
    change (x ∈ sphere (0 : E) 1) ↔ K.reflection x ∈ sphere (0 : E) 1
    simp only [mem_sphere, dist_zero_right, K.reflection.norm_map])

private def reflectionSpherePunctureHomeomorph
    (v : sphere (0 : E) 1) (hv : (v : E) ∈ K) :
    ({v}ᶜ : Set (sphere (0 : E) 1)) ≃ₜ ({v}ᶜ : Set (sphere (0 : E) 1)) :=
  (reflectionSphereHomeomorph K).subtype (fun x => by
    change (x ≠ v) ↔ reflectionSphereHomeomorph K x ≠ v
    have hfix : reflectionSphereHomeomorph K v = v :=
      Subtype.ext (Submodule.reflection_mem_subspace_eq_self hv)
    simpa only [hfix] using
      ((reflectionSphereHomeomorph K).injective.ne_iff :
        reflectionSphereHomeomorph K x ≠ reflectionSphereHomeomorph K v ↔ x ≠ v).symm)

private def reflectionSphereDoublePunctureHomeomorph
    (v : sphere (0 : E) 1) (hv : (v : E) ∈ K) :
    {x : ({-v}ᶜ : Set (sphere (0 : E) 1)) | x.val ≠ v} ≃ₜ
      {x : ({-v}ᶜ : Set (sphere (0 : E) 1)) | x.val ≠ v} :=
  (reflectionSpherePunctureHomeomorph K (-v) (K.neg_mem hv)).subtype (fun x => by
    change (x.val ≠ v) ↔ reflectionSphereHomeomorph K x.val ≠ v
    have hfix : reflectionSphereHomeomorph K v = v :=
      Subtype.ext (Submodule.reflection_mem_subspace_eq_self hv)
    simpa only [hfix] using
      ((reflectionSphereHomeomorph K).injective.ne_iff :
        reflectionSphereHomeomorph K x.val ≠ reflectionSphereHomeomorph K v ↔ x.val ≠ v).symm)

private def reflectionOrthogonalHyperplaneHomeomorph {v : E} (hv : v ∈ K) :
    (ℝ ∙ v)ᗮ ≃ₜ (ℝ ∙ v)ᗮ :=
  K.reflection.toHomeomorph.subtype (fun x => by
    change (x ∈ (ℝ ∙ v)ᗮ) ↔ K.reflection x ∈ (ℝ ∙ v)ᗮ
    constructor
    · exact reflection_mem_orthogonal_span K hv
    · intro hx
      simpa only [Submodule.reflection_reflection] using
        reflection_mem_orthogonal_span K hv hx)

private def reflectionOrthogonalPunctureHomeomorph {v : E} (hv : v ∈ K) :
    ({0}ᶜ : Set (ℝ ∙ v)ᗮ) ≃ₜ ({0}ᶜ : Set (ℝ ∙ v)ᗮ) :=
  (reflectionOrthogonalHyperplaneHomeomorph K hv).subtype (fun x => by
    change (x ≠ 0) ↔ reflectionOrthogonalHyperplaneHomeomorph K hv x ≠ 0
    have hzero : reflectionOrthogonalHyperplaneHomeomorph K hv 0 = 0 :=
      Subtype.ext (map_zero K.reflection)
    simpa only [hzero] using
      ((reflectionOrthogonalHyperplaneHomeomorph K hv).injective.ne_iff :
        reflectionOrthogonalHyperplaneHomeomorph K hv x ≠
          reflectionOrthogonalHyperplaneHomeomorph K hv 0 ↔ x ≠ 0).symm)

private theorem sphereDoublePunctureHomeomorph_symm_reflection
    (v : sphere (0 : E) 1) (hv : (v : E) ∈ K)
    (w : ({0}ᶜ : Set (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ)) :
    (sphereDoublePunctureHomeomorph v).symm
        (reflectionOrthogonalPunctureHomeomorph K (K.neg_mem hv) w) =
      reflectionSphereDoublePunctureHomeomorph K v hv
        ((sphereDoublePunctureHomeomorph v).symm w) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact spherePunctureHomeomorph_symm_reflection K (-v) (K.neg_mem hv) w.val

private theorem sphereDoublePunctureHomeomorph_reflection
    (v : sphere (0 : E) 1) (hv : (v : E) ∈ K) :
    (reflectionSphereDoublePunctureHomeomorph K v hv).trans
        (sphereDoublePunctureHomeomorph v) =
      (sphereDoublePunctureHomeomorph v).trans
        (reflectionOrthogonalPunctureHomeomorph K (K.neg_mem hv)) := by
  apply Homeomorph.ext
  intro x
  let p := sphereDoublePunctureHomeomorph v
  let r := reflectionSphereDoublePunctureHomeomorph K v hv
  let s := reflectionOrthogonalPunctureHomeomorph K (K.neg_mem hv)
  change p (r x) = s (p x)
  have h : p.symm (s (p x)) = r (p.symm (p x)) :=
    sphereDoublePunctureHomeomorph_symm_reflection K v hv (p x)
  have hx : r x = p.symm (s (p x)) :=
    (congrArg r (p.symm_apply_apply x)).symm.trans h.symm
  exact (congrArg p hx).trans (p.apply_symm_apply (s (p x)))

end

section

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

private theorem integralRelativeOpenExcisionIso_inv_natural (n : ℕ)
    (f : C(X, Y)) (A₁ B₁ : Set X) (A₂ B₂ : Set Y)
    (hA₁ : IsOpen A₁) (hB₁ : IsOpen B₁) (hc₁ : A₁ ∪ B₁ = univ)
    (hA₂ : IsOpen A₂) (hB₂ : IsOpen B₂) (hc₂ : A₂ ∪ B₂ = univ)
    (hfA : MapsTo f A₁ A₂) (hfB : MapsTo f B₁ B₂)
    (a : integralRelativeHomology n A₁) :
    let fB := singularPairRestriction f hfB
    let hfI : MapsTo fB (subspaceIntersection A₁ B₁) (subspaceIntersection A₂ B₂) :=
      fun _ hx => hfA hx
    (integralRelativeOpenExcisionIso n A₂ B₂ hA₂ hB₂ hc₂).inv.hom
        (integralRelativeHomologyMap n f hfA a) =
      integralRelativeHomologyMap n fB hfI
        ((integralRelativeOpenExcisionIso n A₁ B₁ hA₁ hB₁ hc₁).inv.hom a) := by
  let fB := singularPairRestriction f hfB
  let hfI : MapsTo fB (subspaceIntersection A₁ B₁) (subspaceIntersection A₂ B₂) :=
    fun _ hx => hfA hx
  let e₁ := (integralRelativeOpenExcisionIso n A₁ B₁ hA₁ hB₁ hc₁).toLinearEquiv
  let e₂ := (integralRelativeOpenExcisionIso n A₂ B₂ hA₂ hB₂ hc₂).toLinearEquiv
  have hcomm : (integralRelativeHomologyMap n f hfA).comp e₁.toLinearMap =
      e₂.toLinearMap.comp (integralRelativeHomologyMap n fB hfI) := by
    change (integralRelativeHomologyMap n f hfA).comp
        (integralRelativeHomologyMap n (singularSubspaceInclusion B₁)
          (subspaceIntersection_mapsTo A₁ B₁)) =
      (integralRelativeHomologyMap n (singularSubspaceInclusion B₂)
          (subspaceIntersection_mapsTo A₂ B₂)).comp (integralRelativeHomologyMap n fB hfI)
    rw [← integralRelativeHomologyMap_comp, ← integralRelativeHomologyMap_comp]
    rfl
  change e₂.symm (integralRelativeHomologyMap n f hfA a) =
    integralRelativeHomologyMap n fB hfI (e₁.symm a)
  apply e₂.injective
  simpa only [LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe] using LinearMap.congr_fun hcomm (e₁.symm a)

private theorem integralHomologyContractibleCoverEquiv_natural (n : ℕ)
    (f : C(X, Y)) (A₁ B₁ : Set X) (A₂ B₂ : Set Y)
    [ContractibleSpace A₁] [ContractibleSpace B₁]
    [ContractibleSpace A₂] [ContractibleSpace B₂]
    (hA₁ : IsOpen A₁) (hB₁ : IsOpen B₁) (hc₁ : A₁ ∪ B₁ = univ)
    (hA₂ : IsOpen A₂) (hB₂ : IsOpen B₂) (hc₂ : A₂ ∪ B₂ = univ)
    (hfA : MapsTo f A₁ A₂) (hfB : MapsTo f B₁ B₂)
    (a : integralSingularHomology (n + 2) X) :
    let fB := singularPairRestriction f hfB
    let hfI : MapsTo fB (subspaceIntersection A₁ B₁) (subspaceIntersection A₂ B₂) :=
      fun _ hx => hfA hx
    integralHomologyContractibleCoverEquiv n A₂ B₂ hA₂ hB₂ hc₂
        (integralSingularHomologyMap (n + 2) f a) =
      integralSingularHomologyMap (n + 1) (singularPairRestriction fB hfI)
        (integralHomologyContractibleCoverEquiv n A₁ B₁ hA₁ hB₁ hc₁ a) := by
  let fB := singularPairRestriction f hfB
  let hfI : MapsTo fB (subspaceIntersection A₁ B₁) (subspaceIntersection A₂ B₂) :=
    fun _ hx => hfA hx
  let e₁ := integralRelativeOpenExcisionIso (n + 2) A₁ B₁ hA₁ hB₁ hc₁
  let e₂ := integralRelativeOpenExcisionIso (n + 2) A₂ B₂ hA₂ hB₂ hc₂
  change integralRelativeConnecting (n + 1) (subspaceIntersection A₂ B₂)
      (e₂.inv.hom (integralAbsoluteToRelative (n + 2) A₂
        (integralSingularHomologyMap (n + 2) f a))) =
    integralSingularHomologyMap (n + 1) (singularPairRestriction fB hfI)
      (integralRelativeConnecting (n + 1) (subspaceIntersection A₁ B₁)
        (e₁.inv.hom (integralAbsoluteToRelative (n + 2) A₁ a)))
  have hnat : integralAbsoluteToRelative (n + 2) A₂
      (integralSingularHomologyMap (n + 2) f a) =
    integralRelativeHomologyMap (n + 2) f hfA (integralAbsoluteToRelative (n + 2) A₁ a) :=
    LinearMap.congr_fun (integralAbsoluteToRelative_natural (n + 2) f hfA) a
  rw [hnat]
  rw [integralRelativeOpenExcisionIso_inv_natural (n + 2) f A₁ B₁ A₂ B₂
    hA₁ hB₁ hc₁ hA₂ hB₂ hc₂ hfA hfB]
  exact (LinearMap.congr_fun (integralRelativeConnecting_natural (n + 1) fB hfI)
    (e₁.inv.hom (integralAbsoluteToRelative (n + 2) A₁ a))).symm

private theorem integralHomologyOneContractibleCoverEquiv_natural
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : C(X, Y)) (A₁ B₁ : Set X) (A₂ B₂ : Set Y)
    [ContractibleSpace A₁] [ContractibleSpace B₁]
    [ContractibleSpace A₂] [ContractibleSpace B₂]
    (hA₁ : IsOpen A₁) (hB₁ : IsOpen B₁) (hc₁ : A₁ ∪ B₁ = univ)
    (hA₂ : IsOpen A₂) (hB₂ : IsOpen B₂) (hc₂ : A₂ ∪ B₂ = univ)
    (hfA : MapsTo f A₁ A₂) (hfB : MapsTo f B₁ B₂)
    (a : integralSingularHomology 1 X) :
    let fB := singularPairRestriction f hfB
    let hfI : MapsTo fB (subspaceIntersection A₁ B₁) (subspaceIntersection A₂ B₂) :=
      fun _ hx => hfA hx
    (integralHomologyOneContractibleCoverEquiv A₂ B₂ hA₂ hB₂ hc₂
        (integralSingularHomologyMap 1 f a)).val =
      integralSingularHomologyMap 0 (singularPairRestriction fB hfI)
        (integralHomologyOneContractibleCoverEquiv A₁ B₁ hA₁ hB₁ hc₁ a).val := by
  let fB := singularPairRestriction f hfB
  let hfI : MapsTo fB (subspaceIntersection A₁ B₁) (subspaceIntersection A₂ B₂) :=
    fun _ hx => hfA hx
  let e₁ := integralRelativeOpenExcisionIso 1 A₁ B₁ hA₁ hB₁ hc₁
  let e₂ := integralRelativeOpenExcisionIso 1 A₂ B₂ hA₂ hB₂ hc₂
  change integralRelativeConnecting 0 (subspaceIntersection A₂ B₂)
      (e₂.inv.hom (integralAbsoluteToRelative 1 A₂ (integralSingularHomologyMap 1 f a))) =
    integralSingularHomologyMap 0 (singularPairRestriction fB hfI)
      (integralRelativeConnecting 0 (subspaceIntersection A₁ B₁)
        (e₁.inv.hom (integralAbsoluteToRelative 1 A₁ a)))
  have hnat : integralAbsoluteToRelative 1 A₂ (integralSingularHomologyMap 1 f a) =
    integralRelativeHomologyMap 1 f hfA (integralAbsoluteToRelative 1 A₁ a) :=
    LinearMap.congr_fun (integralAbsoluteToRelative_natural 1 f hfA) a
  rw [hnat]
  rw [integralRelativeOpenExcisionIso_inv_natural 1 f A₁ B₁ A₂ B₂
    hA₁ hB₁ hc₁ hA₂ hB₂ hc₂ hfA hfB]
  exact (LinearMap.congr_fun (integralRelativeConnecting_natural 0 fB hfI)
    (e₁.inv.hom (integralAbsoluteToRelative 1 A₁ a))).symm

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Submodule ℝ E) [K.HasOrthogonalProjection]

private def reflectionOrthogonalSphereHomeomorph {v : E} (hv : v ∈ K) :
    Metric.sphere (0 : (ℝ ∙ v)ᗮ) 1 ≃ₜ Metric.sphere (0 : (ℝ ∙ v)ᗮ) 1 :=
  (reflectionOrthogonalHyperplaneHomeomorph K hv).subtype (fun x => by
    simp only [Metric.mem_sphere, dist_zero_right]
    change (‖(x : E)‖ = 1) ↔ ‖K.reflection (x : E)‖ = 1
    rw [K.reflection.norm_map])

private theorem puncturedSpaceSphereHomotopyEquiv_reflection {v : E} (hv : v ∈ K) :
    (puncturedSpaceSphereHomotopyEquiv (ℝ ∙ v)ᗮ).toFun.comp
        (reflectionOrthogonalPunctureHomeomorph K hv) =
      ContinuousMap.comp (toContinuousMap (reflectionOrthogonalSphereHomeomorph K hv))
        (puncturedSpaceSphereHomotopyEquiv (ℝ ∙ v)ᗮ).toFun := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change ((puncturedSpaceSphereHomotopyEquiv (ℝ ∙ v)ᗮ).toFun
      (reflectionOrthogonalPunctureHomeomorph K hv x) : (ℝ ∙ v)ᗮ) =
    reflectionOrthogonalHyperplaneHomeomorph K hv
      ((puncturedSpaceSphereHomotopyEquiv (ℝ ∙ v)ᗮ).toFun x : (ℝ ∙ v)ᗮ)
  rw [puncturedSpaceSphereHomotopyEquiv_apply, puncturedSpaceSphereHomotopyEquiv_apply]
  have hnorm : ‖reflectionOrthogonalHyperplaneHomeomorph K hv x.val‖ = ‖x.val‖ :=
    K.reflection.norm_map (x.val : E)
  change ‖reflectionOrthogonalHyperplaneHomeomorph K hv x.val‖⁻¹ •
      reflectionOrthogonalHyperplaneHomeomorph K hv x.val =
    reflectionOrthogonalHyperplaneHomeomorph K hv (‖x.val‖⁻¹ • x.val)
  rw [hnorm]
  apply Subtype.ext
  exact (map_smul K.reflection ‖x.val‖⁻¹ (x.val : E)).symm

private theorem spherePoleIntersectionHomotopyEquiv_reflection
    (v : Metric.sphere (0 : E) 1) (hv : (v : E) ∈ K) :
    (spherePoleIntersectionHomotopyEquiv v).toFun.comp
        (toContinuousMap (reflectionSphereDoublePunctureHomeomorph K v hv)) =
      ContinuousMap.comp (toContinuousMap (reflectionOrthogonalSphereHomeomorph K (K.neg_mem hv)))
        (spherePoleIntersectionHomotopyEquiv v).toFun := by
  apply ContinuousMap.ext
  intro x
  have hchart := DFunLike.congr_fun (sphereDoublePunctureHomeomorph_reflection K v hv) x
  change sphereDoublePunctureHomeomorph v (reflectionSphereDoublePunctureHomeomorph K v hv x) =
    reflectionOrthogonalPunctureHomeomorph K (K.neg_mem hv)
      (sphereDoublePunctureHomeomorph v x) at hchart
  change (puncturedSpaceSphereHomotopyEquiv _).toFun
      (sphereDoublePunctureHomeomorph v (reflectionSphereDoublePunctureHomeomorph K v hv x)) =
    reflectionOrthogonalSphereHomeomorph K (K.neg_mem hv)
      ((puncturedSpaceSphereHomotopyEquiv _).toFun (sphereDoublePunctureHomeomorph v x))
  rw [hchart]
  exact DFunLike.congr_fun (puncturedSpaceSphereHomotopyEquiv_reflection K (K.neg_mem hv))
    (sphereDoublePunctureHomeomorph v x)

private theorem integralSpherePoleIntersectionHomologyEquiv_reflection (n : ℕ)
    (v : Metric.sphere (0 : E) 1) (hv : (v : E) ∈ K)
    (a : integralSingularHomology n
      (subspaceIntersection ({v}ᶜ : Set (Metric.sphere (0 : E) 1)) {-v}ᶜ)) :
    integralSingularHomologyHomotopyEquiv n (spherePoleIntersectionHomotopyEquiv v)
        (integralSingularHomologyMap n (toContinuousMap (reflectionSphereDoublePunctureHomeomorph K v hv)) a) =
      integralSingularHomologyMap n (toContinuousMap (reflectionOrthogonalSphereHomeomorph K (K.neg_mem hv)))
        (integralSingularHomologyHomotopyEquiv n (spherePoleIntersectionHomotopyEquiv v) a) := by
  have h := congrArg (integralSingularHomologyMap n)
    (spherePoleIntersectionHomotopyEquiv_reflection K v hv)
  have hleft := integralSingularHomologyMap_comp n
    (toContinuousMap (reflectionSphereDoublePunctureHomeomorph K v hv))
    (spherePoleIntersectionHomotopyEquiv v).toFun
  have hright := integralSingularHomologyMap_comp n
    (spherePoleIntersectionHomotopyEquiv v).toFun
    (toContinuousMap (reflectionOrthogonalSphereHomeomorph K (K.neg_mem hv)))
  exact LinearMap.congr_fun (hleft.symm.trans (h.trans hright)) a

private theorem integralSphereHomologyShiftEquiv_reflection (n : ℕ)
    (v : Metric.sphere (0 : E) 1) (hv : (v : E) ∈ K)
    (a : integralSingularHomology (n + 2) (Metric.sphere (0 : E) 1)) :
    integralSphereHomologyShiftEquiv n v
        (integralSingularHomologyMap (n + 2) (toContinuousMap (reflectionSphereHomeomorph K)) a) =
      integralSingularHomologyMap (n + 1) (toContinuousMap (reflectionOrthogonalSphereHomeomorph K (K.neg_mem hv)))
        (integralSphereHomologyShiftEquiv n v a) := by
  let := spherePuncture_contractible v
  let := spherePuncture_contractible (-v)
  have hfA : Set.MapsTo (toContinuousMap (reflectionSphereHomeomorph K))
      ({v}ᶜ : Set (Metric.sphere (0 : E) 1)) {v}ᶜ :=
    fun x hx => (reflectionSpherePunctureHomeomorph K v hv ⟨x, hx⟩).property
  have hfB : Set.MapsTo (toContinuousMap (reflectionSphereHomeomorph K))
      ({-v}ᶜ : Set (Metric.sphere (0 : E) 1)) {-v}ᶜ :=
    fun x hx => (reflectionSpherePunctureHomeomorph K (-v) (K.neg_mem hv) ⟨x, hx⟩).property
  let c := integralHomologyContractibleCoverEquiv n {v}ᶜ {-v}ᶜ
    isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v)
  have hcover := integralHomologyContractibleCoverEquiv_natural n
    (toContinuousMap (reflectionSphereHomeomorph K)) {v}ᶜ {-v}ᶜ {v}ᶜ {-v}ᶜ
    isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v)
    isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v) hfA hfB a
  change c (integralSingularHomologyMap (n + 2) (toContinuousMap (reflectionSphereHomeomorph K)) a) =
    integralSingularHomologyMap (n + 1) (toContinuousMap (reflectionSphereDoublePunctureHomeomorph K v hv))
      (c a) at hcover
  change integralSingularHomologyHomotopyEquiv (n + 1) (spherePoleIntersectionHomotopyEquiv v)
      (c (integralSingularHomologyMap (n + 2) (toContinuousMap (reflectionSphereHomeomorph K)) a)) =
    integralSingularHomologyMap (n + 1) (toContinuousMap (reflectionOrthogonalSphereHomeomorph K (K.neg_mem hv)))
      (integralSingularHomologyHomotopyEquiv (n + 1) (spherePoleIntersectionHomotopyEquiv v) (c a))
  rw [hcover]
  exact integralSpherePoleIntersectionHomologyEquiv_reflection K (n + 1) v hv (c a)

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem integralSphereHomologyOneReducedEquiv_apply_val
    [PathConnectedSpace (Metric.sphere (0 : E) 1)]
    (v : Metric.sphere (0 : E) 1) (a : integralSingularHomology 1 (Metric.sphere (0 : E) 1)) :
    (integralSphereHomologyOneReducedEquiv v a).val =
      integralSingularHomologyMap 0 (spherePoleIntersectionHomotopyEquiv v).toFun
        (integralSphereHomologyOneKernelEquiv v a).val := rfl

variable (K : Submodule ℝ E) [K.HasOrthogonalProjection]

private theorem integralSphereHomologyOneKernelEquiv_reflection
    [PathConnectedSpace (Metric.sphere (0 : E) 1)]
    (v : Metric.sphere (0 : E) 1) (hv : (v : E) ∈ K)
    (a : integralSingularHomology 1 (Metric.sphere (0 : E) 1)) :
    (integralSphereHomologyOneKernelEquiv v
        (integralSingularHomologyMap 1 (toContinuousMap (reflectionSphereHomeomorph K)) a)).val =
      integralSingularHomologyMap 0 (toContinuousMap (reflectionSphereDoublePunctureHomeomorph K v hv))
        (integralSphereHomologyOneKernelEquiv v a).val := by
  let := spherePuncture_contractible v
  let := spherePuncture_contractible (-v)
  have hfA : Set.MapsTo (toContinuousMap (reflectionSphereHomeomorph K))
      ({v}ᶜ : Set (Metric.sphere (0 : E) 1)) {v}ᶜ :=
    fun x hx => (reflectionSpherePunctureHomeomorph K v hv ⟨x, hx⟩).property
  have hfB : Set.MapsTo (toContinuousMap (reflectionSphereHomeomorph K))
      ({-v}ᶜ : Set (Metric.sphere (0 : E) 1)) {-v}ᶜ :=
    fun x hx => (reflectionSpherePunctureHomeomorph K (-v) (K.neg_mem hv) ⟨x, hx⟩).property
  exact integralHomologyOneContractibleCoverEquiv_natural
    (toContinuousMap (reflectionSphereHomeomorph K)) {v}ᶜ {-v}ᶜ {v}ᶜ {-v}ᶜ
    isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v)
    isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v) hfA hfB a

private theorem integralSphereHomologyOneReducedEquiv_reflection
    [PathConnectedSpace (Metric.sphere (0 : E) 1)]
    (v : Metric.sphere (0 : E) 1) (hv : (v : E) ∈ K)
    (a : integralSingularHomology 1 (Metric.sphere (0 : E) 1)) :
    (integralSphereHomologyOneReducedEquiv v
        (integralSingularHomologyMap 1 (toContinuousMap (reflectionSphereHomeomorph K)) a)).val =
      integralSingularHomologyMap 0 (toContinuousMap (reflectionOrthogonalSphereHomeomorph K (K.neg_mem hv)))
        (integralSphereHomologyOneReducedEquiv v a).val := by
  rw [integralSphereHomologyOneReducedEquiv_apply_val,
    integralSphereHomologyOneKernelEquiv_reflection K v hv,
    integralSphereHomologyOneReducedEquiv_apply_val]
  exact integralSpherePoleIntersectionHomologyEquiv_reflection K 0 v hv
    (integralSphereHomologyOneKernelEquiv v a).val

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem starProjection_mem_orthogonal_span
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] {v x : E}
    (hv : v ∈ K) (hx : x ∈ (ℝ ∙ v)ᗮ) : K.starProjection x ∈ (ℝ ∙ v)ᗮ := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  rw [← K.inner_starProjection_left_eq_right v x, Submodule.starProjection_eq_self_iff.mpr hv]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hx

private theorem comap_orthogonal_span_hasOrthogonalProjection
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] {v : E} (hv : v ∈ K) :
    (K.comap ((ℝ ∙ v)ᗮ).subtype).HasOrthogonalProjection := by
  constructor
  intro x
  refine ⟨⟨K.starProjection (x : E), starProjection_mem_orthogonal_span K hv x.property⟩,
    K.starProjection_apply_mem (x : E), ?_⟩
  intro y hy
  exact (Submodule.sub_starProjection_mem_orthogonal (K := K) (x : E)) (y : E) hy

private theorem starProjection_comap_orthogonal_span_apply
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] {v : E} (hv : v ∈ K)
    (x : (ℝ ∙ v)ᗮ) :
    letI := comap_orthogonal_span_hasOrthogonalProjection K hv
    ((K.comap ((ℝ ∙ v)ᗮ).subtype).starProjection x : E) = K.starProjection (x : E) := by
  let := comap_orthogonal_span_hasOrthogonalProjection K hv
  have h : (K.comap ((ℝ ∙ v)ᗮ).subtype).starProjection x =
      (⟨K.starProjection (x : E), starProjection_mem_orthogonal_span K hv x.property⟩ :
        (ℝ ∙ v)ᗮ) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact K.starProjection_apply_mem (x : E)
    · intro y hy
      exact Submodule.starProjection_inner_eq_zero (x : E) (y : E) hy
  exact congrArg (fun y : (ℝ ∙ v)ᗮ => (y : E)) h

private theorem reflection_comap_orthogonal_span_apply
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] {v : E} (hv : v ∈ K)
    (x : (ℝ ∙ v)ᗮ) :
    letI := comap_orthogonal_span_hasOrthogonalProjection K hv
    ((K.comap ((ℝ ∙ v)ᗮ).subtype).reflection x : E) = K.reflection (x : E) := by
  let := comap_orthogonal_span_hasOrthogonalProjection K hv
  simp only [Submodule.reflection_apply]
  change (2 : ℕ) • ((K.comap ((ℝ ∙ v)ᗮ).subtype).starProjection x : E) - (x : E) =
    (2 : ℕ) • K.starProjection (x : E) - (x : E)
  rw [starProjection_comap_orthogonal_span_apply K hv x]

private theorem finrank_comap_orthogonal_span_add_one
    (K : Submodule ℝ E) [FiniteDimensional ℝ K] {v : E} (hv : v ∈ K) (hvne : v ≠ 0) :
    Module.finrank ℝ (K.comap ((ℝ ∙ v)ᗮ).subtype) + 1 = Module.finrank ℝ K := by
  have h := Submodule.finrank_add_inf_finrank_orthogonal
    ((Submodule.span_singleton_le_iff_mem v K).mpr hv)
  rw [finrank_span_singleton hvne] at h
  have hm := Submodule.finrank_map_subtype_eq (ℝ ∙ v)ᗮ (K.comap ((ℝ ∙ v)ᗮ).subtype)
  rw [Submodule.map_comap_subtype] at hm
  rw [hm] at h
  omega

private theorem finrank_comap_orthogonal_span_codimension_one
    [FiniteDimensional ℝ E] (K : Submodule ℝ E) {v : E} (hv : v ∈ K) (hvne : v ≠ 0)
    (hK : Module.finrank ℝ K + 1 = Module.finrank ℝ E) :
    Module.finrank ℝ (K.comap ((ℝ ∙ v)ᗮ).subtype) + 1 = Module.finrank ℝ (ℝ ∙ v)ᗮ := by
  have hW := finrank_comap_orthogonal_span_add_one K hv hvne
  have hH := (ℝ ∙ v).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hvne] at hH
  omega

end

section

private theorem integralSingularHomologyMap_zero_eq_neg_of_swap
    {X : Type u} [TopologicalSpace X] (e : X ≃ Bool) (f : C(X, X))
    (hf : ∀ x, e (f x) = Bool.not (e x)) (a : integralReducedHomologyZero X) :
    integralSingularHomologyMap 0 f a.val = -a.val := by
  let p := integralZeroChainClass (integralVertexChain (e.symm false))
  let q := integralZeroChainClass (integralVertexChain (e.symm true))
  let s : ℤ →ₗ[ℤ] integralSingularHomology 0 X :=
    LinearMap.toSpanSingleton ℤ _ (p + q)
  have hvertex (x : X) :
      integralSingularHomologyMap 0 f (integralZeroChainClass (integralVertexChain x)) +
        integralZeroChainClass (integralVertexChain x) = p + q := by
    rw [integralZeroChainClass_map, integralVertexChain_map]
    obtain ⟨b, rfl⟩ := e.symm.surjective x
    have hfb : f (e.symm b) = e.symm (Bool.not b) := by
      apply e.injective
      simpa only [Equiv.apply_symm_apply] using hf (e.symm b)
    rw [hfb]
    cases b
    · exact add_comm _ _
    · rfl
  have hfactor :
      ((integralSingularHomologyMap 0 f + LinearMap.id).comp integralZeroChainClass) =
        (s.comp integralZeroAugmentation).comp integralZeroChainClass := by
    apply (integralSingularChainBasis 0 X).ext
    intro σ
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
      integralSingularChainBasis_apply]
    rw [integralSimplexChain_zero_vertex, integralZeroAugmentation_vertex]
    simpa only [s, LinearMap.toSpanSingleton_apply_one] using
      hvertex (TopCat.toSSetObj₀Equiv σ)
  obtain ⟨c, hc⟩ := integralZeroChainClass_surjective a.val
  have hzero : integralZeroAugmentation a.val = 0 := a.property
  have heq : integralSingularHomologyMap 0 f a.val + a.val = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
      hc, hzero, map_zero] using LinearMap.congr_fun hfactor c
  exact eq_neg_of_add_eq_zero_left heq

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def unitSphereNegation : C(sphere (0 : E) 1, sphere (0 : E) 1) :=
  ⟨fun x => -x, by fun_prop⟩

private theorem integralReducedZeroMap_oneDimSphere_neg
    (hd : finrank ℝ E = 1)
    (a : integralReducedHomologyZero (sphere (0 : E) 1)) :
    integralSingularHomologyMap 0 (unitSphereNegation (E := E)) a.val = -a.val := by
  let := Module.nontrivial_of_finrank_pos (show 0 < finrank ℝ E by omega)
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0)).mpr
    (show (0 : ℝ) ≤ 1 by norm_num)
  let e := oneDimUnitSphereEquivBool hd (⟨v, hv⟩ : sphere (0 : E) 1)
  apply integralSingularHomologyMap_zero_eq_neg_of_swap e unitSphereNegation _ a
  intro x
  obtain ⟨b, rfl⟩ := e.symm.surjective x
  have hneg : -(e.symm b) = e.symm (Bool.not b) := by
    change -(if b then -(⟨v, hv⟩ : sphere (0 : E) 1) else ⟨v, hv⟩) =
      if Bool.not b then -(⟨v, hv⟩ : sphere (0 : E) 1) else ⟨v, hv⟩
    cases b <;> simp
  change e (-(e.symm b)) = Bool.not (e (e.symm b))
  rw [hneg, e.apply_symm_apply, e.apply_symm_apply]

end

section

private theorem exists_unitSpherePoint_mem_submodule
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) (hK : 0 < finrank ℝ K) :
    ∃ v : sphere (0 : E) 1, (v : E) ∈ K := by
  let w := unitSpherePointOfFinrankPos (E := K) hK
  refine ⟨⟨w.val.val, ?_⟩, w.val.property⟩
  rw [mem_sphere, dist_zero_right]
  exact norm_eq_of_mem_sphere w

private theorem reflectionOrthogonalSphereHomeomorph_eq_native
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] {v : E} (hv : v ∈ K) :
    letI := comap_orthogonal_span_hasOrthogonalProjection K hv
    reflectionOrthogonalSphereHomeomorph K hv =
      reflectionSphereHomeomorph (K.comap ((ℝ ∙ v)ᗮ).subtype) := by
  let := comap_orthogonal_span_hasOrthogonalProjection K hv
  apply Homeomorph.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact (reflection_comap_orthogonal_span_apply K hv x.val).symm

private theorem reflectionSphereHomeomorph_bot_eq_neg
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    toContinuousMap (reflectionSphereHomeomorph (⊥ : Submodule ℝ E)) =
      unitSphereNegation (E := E) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun f : E ≃ₗᵢ[ℝ] E => f (x : E)) Submodule.reflection_bot

private theorem integralReducedZeroMap_reflection_of_finrank_one
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : finrank ℝ E = 1) (K : Submodule ℝ E)
    (hK : finrank ℝ K + 1 = finrank ℝ E)
    (a : integralReducedHomologyZero (sphere (0 : E) 1)) :
    integralSingularHomologyMap 0
      (toContinuousMap (reflectionSphereHomeomorph K)) a.val = -a.val := by
  have hKbot : K = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  rw [hKbot, reflectionSphereHomeomorph_bot_eq_neg]
  exact integralReducedZeroMap_oneDimSphere_neg hd a

private theorem integralSphereTopHomologyMap_reflection (n : ℕ) (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : finrank ℝ E = n + 2) (K : Submodule ℝ E)
    (hK : finrank ℝ K + 1 = finrank ℝ E)
    (a : integralSingularHomology (n + 1) (sphere (0 : E) 1)) :
    integralSingularHomologyMap (n + 1)
      (toContinuousMap (reflectionSphereHomeomorph K)) a = -a := by
  induction n generalizing E with
  | zero =>
      obtain ⟨v, hv⟩ := exists_unitSpherePoint_mem_submodule K (by omega)
      let := unitSphere_pathConnected_of_finrank (E := E) (by omega)
      let H := (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ
      let L := K.comap H.subtype
      have hdH : finrank ℝ H = 1 := unitSpherePoleHyperplane_finrank 1 hd (-v)
      have hvne : ((-v : sphere (0 : E) 1) : E) ≠ 0 := by
        intro hzero
        have hn := norm_eq_of_mem_sphere (-v)
        rw [hzero, norm_zero] at hn
        norm_num at hn
      have hL : finrank ℝ L + 1 = finrank ℝ H :=
        finrank_comap_orthogonal_span_codimension_one K (K.neg_mem hv) hvne hK
      let e := integralSphereHomologyOneReducedEquiv v
      apply e.injective
      apply Subtype.ext
      change (e (integralSingularHomologyMap 1
          (toContinuousMap (reflectionSphereHomeomorph K)) a)).val =
        (e (-a)).val
      rw [map_neg]
      change (e (integralSingularHomologyMap 1
          (toContinuousMap (reflectionSphereHomeomorph K)) a)).val =
        -(e a).val
      rw [integralSphereHomologyOneReducedEquiv_reflection K v hv,
        reflectionOrthogonalSphereHomeomorph_eq_native K (K.neg_mem hv)]
      exact integralReducedZeroMap_reflection_of_finrank_one hdH L hL (e a)
  | succ n ih =>
      obtain ⟨v, hv⟩ := exists_unitSpherePoint_mem_submodule K (by omega)
      let H := (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ
      let L := K.comap H.subtype
      have hdH : finrank ℝ H = n + 2 :=
        unitSpherePoleHyperplane_finrank (n + 2) (by omega) (-v)
      have hvne : ((-v : sphere (0 : E) 1) : E) ≠ 0 := by
        intro hzero
        have hn := norm_eq_of_mem_sphere (-v)
        rw [hzero, norm_zero] at hn
        norm_num at hn
      have hL : finrank ℝ L + 1 = finrank ℝ H :=
        finrank_comap_orthogonal_span_codimension_one K (K.neg_mem hv) hvne hK
      let e := integralSphereHomologyShiftEquiv n v
      apply e.injective
      rw [map_neg]
      change integralSphereHomologyShiftEquiv n v
          (integralSingularHomologyMap (n + 2)
            (toContinuousMap (reflectionSphereHomeomorph K)) a) = -e a
      rw [integralSphereHomologyShiftEquiv_reflection K n v hv,
        reflectionOrthogonalSphereHomeomorph_eq_native K (K.neg_mem hv)]
      exact ih H hdH L hL (e a)

end

section

private theorem reflection_mapsTo_pointComplement
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] :
    MapsTo (toContinuousMap K.reflection)
      ({0}ᶜ : Set E) ({0}ᶜ : Set E) := by
  intro x hx
  change K.reflection x ≠ 0
  change x ≠ 0 at hx
  exact fun h => hx (K.reflection.injective (h.trans (map_zero K.reflection).symm))

private theorem puncturedSpaceSphereHomotopyEquiv_reflection_ambient
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] :
    (puncturedSpaceSphereHomotopyEquiv E).toFun.comp
        (singularPairRestriction (toContinuousMap K.reflection)
          (reflection_mapsTo_pointComplement K)) =
      (toContinuousMap (reflectionSphereHomeomorph K)).comp
        (puncturedSpaceSphereHomotopyEquiv E).toFun := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change ((puncturedSpaceSphereHomotopyEquiv E).toFun
      (singularPairRestriction (toContinuousMap K.reflection)
        (reflection_mapsTo_pointComplement K) x) : E) =
    K.reflection ((puncturedSpaceSphereHomotopyEquiv E).toFun x : E)
  rw [puncturedSpaceSphereHomotopyEquiv_apply, puncturedSpaceSphereHomotopyEquiv_apply]
  change ‖K.reflection (x : E)‖⁻¹ • K.reflection (x : E) =
    K.reflection (‖(x : E)‖⁻¹ • (x : E))
  rw [K.reflection.norm_map, map_smul]

private theorem integralPuncturedSpaceSphereHomologyEquiv_reflection
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (n : ℕ)
    (a : integralSingularHomology n ({0}ᶜ : Set E)) :
    integralPuncturedSpaceSphereHomologyEquiv E n
        (integralSingularHomologyMap n
          (singularPairRestriction (toContinuousMap K.reflection)
            (reflection_mapsTo_pointComplement K)) a) =
      integralSingularHomologyMap n
        (toContinuousMap (reflectionSphereHomeomorph K))
        (integralPuncturedSpaceSphereHomologyEquiv E n a) := by
  have h := congrArg (integralSingularHomologyMap n)
    (puncturedSpaceSphereHomotopyEquiv_reflection_ambient K)
  rw [integralSingularHomologyMap_comp, integralSingularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

private theorem integralRelativeConnecting_injective_of_contractible
    {X : Type u} [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) (A : Set X) :
    Function.Injective (integralRelativeConnecting n A) := by
  cases n with
  | zero => exact integralRelativeConnecting_zero_injective A
  | succ n => exact (integralRelativeConnectingEquivOfContractible (n + 1) (by omega) A).injective

private theorem integralLocalTopHomologyMap_reflection (n : ℕ) (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : finrank ℝ E = n + 1) (K : Submodule ℝ E)
    (hK : finrank ℝ K + 1 = finrank ℝ E)
    (a : integralRelativeHomology (n + 1) ({0}ᶜ : Set E)) :
    integralRelativeHomologyMap (n + 1) (toContinuousMap K.reflection)
      (reflection_mapsTo_pointComplement K) a = -a := by
  apply integralRelativeConnecting_injective_of_contractible n ({0}ᶜ : Set E)
  rw [map_neg]
  have hnat : integralRelativeConnecting n ({0}ᶜ : Set E)
      (integralRelativeHomologyMap (n + 1) (toContinuousMap K.reflection)
        (reflection_mapsTo_pointComplement K) a) =
      integralSingularHomologyMap n
        (singularPairRestriction (toContinuousMap K.reflection)
          (reflection_mapsTo_pointComplement K))
        (integralRelativeConnecting n ({0}ᶜ : Set E) a) :=
    (LinearMap.congr_fun (integralRelativeConnecting_natural n
        (toContinuousMap K.reflection)
        (reflection_mapsTo_pointComplement K)) a).symm
  rw [hnat]
  apply (integralPuncturedSpaceSphereHomologyEquiv E n).injective
  rw [map_neg, integralPuncturedSpaceSphereHomologyEquiv_reflection K n]
  cases n with
  | zero =>
      let b := integralRelativeConnectingZeroKernelEquiv ({0}ᶜ : Set E) a
      let c := integralZeroMapKernelReducedEquiv (singularSubspaceInclusion ({0}ᶜ : Set E)) b
      let d := integralReducedZeroHomotopyEquiv (puncturedSpaceSphereHomotopyEquiv E) c
      exact integralReducedZeroMap_reflection_of_finrank_one hd K hK d
  | succ n =>
      exact integralSphereTopHomologyMap_reflection n E hd K hK
        (integralPuncturedSpaceSphereHomologyEquiv E (n + 1)
          (integralRelativeConnecting (n + 1) ({0}ᶜ : Set E) a))

end

section

private theorem integralRelativeHomologyMap_transvection
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E →L[ℝ] ℝ) (v : E) (hv : ℓ v = 0) (n : ℕ) :
    let A := ContinuousLinearMap.id ℝ E + ℓ.smulRight v
    let f : C(E, E) := ⟨A, A.continuous⟩
    ∃ hp : MapsTo f ({0}ᶜ : Set E) ({0}ᶜ : Set E),
      integralRelativeHomologyMap n f hp = LinearMap.id := by
  let A := ContinuousLinearMap.id ℝ E + ℓ.smulRight v
  let f : C(E, E) := ⟨A, A.continuous⟩
  let U : Set E := {0}ᶜ
  have havoid (t : unitInterval) (x : U) :
      (x : E) + ℓ (x : E) • ((t : ℝ) • v) ≠ 0 := by
    intro h
    have hℓ : ℓ (x : E) = 0 := by
      have hh := congrArg ℓ h
      simpa only [map_add, map_smul, hv, smul_zero, add_zero, map_zero] using hh
    apply x.property
    change (x : E) = 0
    simpa only [hℓ, zero_smul, add_zero] using h
  have hp : MapsTo f U U := by
    intro x hx
    simpa [f, A, U] using havoid 1 ⟨x, hx⟩
  refine ⟨hp, ?_⟩
  let H : (singularPairRestriction (ContinuousMap.id E) (fun _ hx => hx)).Homotopy
      (singularPairRestriction f hp) :=
    { toFun := fun p => ⟨(p.2 : E) + ℓ (p.2 : E) • ((p.1 : ℝ) • v), havoid p.1 p.2⟩
      continuous_toFun := by
        have hx : Continuous (fun p : unitInterval × U => (p.2 : E)) :=
          continuous_subtype_val.comp continuous_snd
        have ht : Continuous (fun p : unitInterval × U => (p.1 : ℝ)) :=
          continuous_subtype_val.comp continuous_fst
        exact (hx.add ((ℓ.continuous.comp hx).smul (ht.smul continuous_const))).subtype_mk _
      map_zero_left := by
        intro x
        apply Subtype.ext
        simp [singularPairRestriction]
      map_one_left := by
        intro x
        apply Subtype.ext
        simp [singularPairRestriction, f, A] }
  have heq : integralRelativeHomologyMap n f hp =
      integralRelativeHomologyMap n (ContinuousMap.id E) (fun _ hx => hx) := by
    cases n with
    | zero =>
      exact integralRelativeHomologyMap_zero_eq_of_joined f (ContinuousMap.id E) U U hp
        (fun _ hx => hx) (fun _ => ⟨PathConnectedSpace.somePath _ _⟩)
    | succ n =>
      let := integralSingularHomology_subsingleton_of_contractible (n + 1) (by omega) E
      exact (integralRelativeHomologyMap_eq_of_restriction_homotopic n
        (ContinuousMap.id E) f U U (fun _ hx => hx) hp ⟨H⟩).symm
  exact heq.trans (integralRelativeHomologyMap_id n U)

end

section

variable {ι : Type w} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private def matrixContinuousMap (M : Matrix ι ι ℝ) : C(ι → ℝ, ι → ℝ) :=
  ⟨M.mulVecLin, M.mulVecLin.continuous_of_finiteDimensional⟩

private theorem matrixContinuousMap_one :
    matrixContinuousMap (1 : Matrix ι ι ℝ) = ContinuousMap.id (ι → ℝ) := by
  apply ContinuousMap.ext
  intro x
  exact Matrix.one_mulVec x

omit [DecidableEq ι] in
private theorem matrixContinuousMap_mul (A B : Matrix ι ι ℝ) :
    matrixContinuousMap (A * B) = (matrixContinuousMap A).comp (matrixContinuousMap B) := by
  apply ContinuousMap.ext
  intro x
  exact (Matrix.mulVec_mulVec x A B).symm

private theorem matrixContinuousMap_mapsTo_puncture (M : Matrix ι ι ℝ)
    (hM : M.det ≠ 0) :
    MapsTo (matrixContinuousMap M) ({0}ᶜ : Set (ι → ℝ)) ({0}ᶜ : Set (ι → ℝ)) := by
  have hi : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hM))
  intro x hx
  change x ≠ 0 at hx
  change M.mulVec x ≠ 0
  intro hz
  exact hx (hi (hz.trans (Matrix.mulVec_zero M).symm))

private theorem transvection_toContinuousLinearMap (i j : ι) (c : ℝ) :
    (Matrix.transvection i j c).mulVecLin.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (ι → ℝ) +
        (ContinuousLinearMap.proj j).smulRight (Pi.single i c) := by
  apply ContinuousLinearMap.ext
  intro x
  change (Matrix.transvection i j c).mulVec x = x + x j • Pi.single i c
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  congr 1
  ext k
  by_cases hk : k = i
  · subst k
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    exact mul_comm c (x j)
  · simp only [Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero]

private theorem integralRelativeHomologyMap_matrix_transvection
    (i j : ι) (hij : i ≠ j) (c : ℝ) :
    ∃ hp : MapsTo (matrixContinuousMap (Matrix.transvection i j c))
        ({0}ᶜ : Set (ι → ℝ)) ({0}ᶜ : Set (ι → ℝ)),
      ∀ n : ℕ, integralRelativeHomologyMap n
        (matrixContinuousMap (Matrix.transvection i j c)) hp = LinearMap.id := by
  let ℓ : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  let v : ι → ℝ := Pi.single i c
  have hv : ℓ v = 0 := by
    change (Pi.single i c : ι → ℝ) j = 0
    simp only [Pi.single_eq_of_ne hij.symm]
  let A := ContinuousLinearMap.id ℝ (ι → ℝ) + ℓ.smulRight v
  let f : C(ι → ℝ, ι → ℝ) := ⟨A, A.continuous⟩
  have he : matrixContinuousMap (Matrix.transvection i j c) = f := by
    apply ContinuousMap.ext
    intro x
    exact congrArg (fun L : (ι → ℝ) →L[ℝ] (ι → ℝ) => L x)
      (transvection_toContinuousLinearMap i j c)
  rw [he]
  obtain ⟨hp, _⟩ := integralRelativeHomologyMap_transvection ℓ v hv 0
  exact ⟨hp, fun n => (integralRelativeHomologyMap_transvection ℓ v hv n).choose_spec⟩

private theorem integralRelativeHomologyMap_matrix_transvection_prod
    (L : List (Matrix.TransvectionStruct ι ℝ)) :
    ∃ hp : MapsTo (matrixContinuousMap (L.map Matrix.TransvectionStruct.toMatrix).prod)
        ({0}ᶜ : Set (ι → ℝ)) ({0}ᶜ : Set (ι → ℝ)),
      ∀ n : ℕ, integralRelativeHomologyMap n
        (matrixContinuousMap (L.map Matrix.TransvectionStruct.toMatrix).prod) hp =
          LinearMap.id := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, matrixContinuousMap_one]
    exact ⟨fun _ hx => hx, fun n => integralRelativeHomologyMap_id n _⟩
  | cons t L hL =>
    obtain ⟨hpL, hLmap⟩ := hL
    obtain ⟨hpt, htmap⟩ := integralRelativeHomologyMap_matrix_transvection t.i t.j t.hij t.c
    change MapsTo (matrixContinuousMap t.toMatrix)
      ({0}ᶜ : Set (ι → ℝ)) ({0}ᶜ : Set (ι → ℝ)) at hpt
    change ∀ n : ℕ, integralRelativeHomologyMap n (matrixContinuousMap t.toMatrix) hpt =
      LinearMap.id at htmap
    simp only [List.map_cons, List.prod_cons, matrixContinuousMap_mul]
    refine ⟨hpt.comp hpL, ?_⟩
    intro n
    rw [integralRelativeHomologyMap_comp n _ _ hpL hpt, hLmap n, htmap n]
    rfl

private theorem exists_diagonal_integralRelativeHomologyMap_eq_matrix
    (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) :
    ∃ D : ι → ℝ, (Matrix.diagonal D).det = M.det ∧
      ∃ (hpM : MapsTo (matrixContinuousMap M)
          ({0}ᶜ : Set (ι → ℝ)) ({0}ᶜ : Set (ι → ℝ)))
        (hpD : MapsTo (matrixContinuousMap (Matrix.diagonal D))
          ({0}ᶜ : Set (ι → ℝ)) ({0}ᶜ : Set (ι → ℝ))),
        ∀ n : ℕ, integralRelativeHomologyMap n (matrixContinuousMap M) hpM =
          integralRelativeHomologyMap n (matrixContinuousMap (Matrix.diagonal D)) hpD := by
  obtain ⟨L, R, D, hfactor⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hdet : (Matrix.diagonal D).det = M.det := by
    rw [hfactor]
    simp only [Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod, one_mul, mul_one]
  have hpM := matrixContinuousMap_mapsTo_puncture M hM
  have hpD := matrixContinuousMap_mapsTo_puncture (Matrix.diagonal D) (hdet.trans_ne hM)
  obtain ⟨hpL, hL⟩ := integralRelativeHomologyMap_matrix_transvection_prod L
  obtain ⟨hpR, hR⟩ := integralRelativeHomologyMap_matrix_transvection_prod R
  refine ⟨D, hdet, hpM, hpD, ?_⟩
  intro n
  have he : matrixContinuousMap M =
      ((matrixContinuousMap (L.map Matrix.TransvectionStruct.toMatrix).prod).comp
        (matrixContinuousMap (Matrix.diagonal D))).comp
          (matrixContinuousMap (R.map Matrix.TransvectionStruct.toMatrix).prod) := by
    rw [hfactor, matrixContinuousMap_mul, matrixContinuousMap_mul]
  have hcomp : integralRelativeHomologyMap n
      (((matrixContinuousMap (L.map Matrix.TransvectionStruct.toMatrix).prod).comp
        (matrixContinuousMap (Matrix.diagonal D))).comp
          (matrixContinuousMap (R.map Matrix.TransvectionStruct.toMatrix).prod))
      ((hpL.comp hpD).comp hpR) =
      integralRelativeHomologyMap n (matrixContinuousMap (Matrix.diagonal D)) hpD := by
    rw [integralRelativeHomologyMap_comp n
      (matrixContinuousMap (R.map Matrix.TransvectionStruct.toMatrix).prod)
      ((matrixContinuousMap (L.map Matrix.TransvectionStruct.toMatrix).prod).comp
        (matrixContinuousMap (Matrix.diagonal D))) hpR (hpL.comp hpD),
      integralRelativeHomologyMap_comp n (matrixContinuousMap (Matrix.diagonal D))
        (matrixContinuousMap (L.map Matrix.TransvectionStruct.toMatrix).prod) hpD hpL,
      hL n, hR n]
    rfl
  simpa only [← he] using hcomp

end

section

variable {κ : Type z} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
private def coordinateReflectionMatrix (i : κ) : Matrix κ κ ℝ :=
  Matrix.diagonal (fun j => if j = i then -1 else 1)

private theorem coordinate_reflection_det (i : κ) :
    (coordinateReflectionMatrix i).det = -1 := by
  rw [coordinateReflectionMatrix, Matrix.det_diagonal]
  exact Fintype.prod_ite_eq' i (fun _ => (-1 : ℝ))

private theorem coordinate_reflection_list_prod (L : List κ) (hL : L.Nodup) :
    (L.map coordinateReflectionMatrix).prod =
      Matrix.diagonal (fun j => if j ∈ L then (-1 : ℝ) else 1) := by
  induction L with
  | nil => simp only [List.map_nil, List.prod_nil, List.not_mem_nil, ↓reduceIte,
      Matrix.diagonal_one]
  | cons i L ih =>
      obtain ⟨hi, hL⟩ := List.nodup_cons.mp hL
      rw [List.map_cons, List.prod_cons, ih hL, coordinateReflectionMatrix,
        Matrix.diagonal_mul_diagonal]
      apply congrArg Matrix.diagonal
      funext j
      by_cases hj : j = i
      · subst j
        simp only [↓reduceIte, hi, List.mem_cons, true_or, mul_one]
      · simp only [hj, List.mem_cons, false_or, ↓reduceIte, one_mul]

private theorem coordinate_reflection_list_det (L : List κ) :
    (L.map coordinateReflectionMatrix).prod.det = (-1 : ℝ) ^ L.length := by
  induction L with
  | nil => simp only [List.map_nil, List.prod_nil, Matrix.det_one, List.length_nil, pow_zero]
  | cons i L ih =>
      rw [List.map_cons, List.prod_cons, Matrix.det_mul, coordinate_reflection_det, ih,
        List.length_cons, pow_succ']

private theorem coordinate_reflection_list_map (L : List κ) :
    matrixContinuousMap (L.map coordinateReflectionMatrix).prod =
      L.foldr (fun i f => (matrixContinuousMap (coordinateReflectionMatrix i)).comp f)
        (ContinuousMap.id (κ → ℝ)) := by
  induction L with
  | nil => exact matrixContinuousMap_one
  | cons i L ih =>
      rw [List.map_cons, List.prod_cons, matrixContinuousMap_mul, List.foldr_cons, ih]

private theorem diagonal_eq_abs_mul_reflections (D : κ → ℝ) (L : List κ)
    (hL : L.Nodup) (hm : ∀ i, i ∈ L ↔ D i < 0) :
    Matrix.diagonal D = Matrix.diagonal (fun i => |D i|) *
      (L.map coordinateReflectionMatrix).prod := by
  rw [coordinate_reflection_list_prod L hL, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  by_cases hi : D i < 0
  · simp only [(hm i).mpr hi, ↓reduceIte, abs_of_neg hi, mul_neg_one, neg_neg]
  · simp only [show i ∉ L from fun h => hi ((hm i).mp h), ↓reduceIte,
      abs_of_nonneg (le_of_not_gt hi), mul_one]

private theorem exists_diagonal_abs_reflection_factorization
    (D : κ → ℝ) (hD : (Matrix.diagonal D).det ≠ 0) :
    (∀ i, 0 < |D i|) ∧
      ∃ L : List κ, L.Nodup ∧ (∀ i, i ∈ L ↔ D i < 0) ∧
        Matrix.diagonal D = Matrix.diagonal (fun i => |D i|) *
          (L.map coordinateReflectionMatrix).prod ∧
        matrixContinuousMap (Matrix.diagonal D) =
          (matrixContinuousMap (Matrix.diagonal (fun i => |D i|))).comp
            (L.foldr
              (fun i f => (matrixContinuousMap (coordinateReflectionMatrix i)).comp f)
              (ContinuousMap.id (κ → ℝ))) ∧
        (Matrix.diagonal D).det =
          (∏ i, |D i|) * (-1 : ℝ) ^ L.length := by
  have hn : (∏ i, D i) ≠ 0 := by
    simpa only [Matrix.det_diagonal] using hD
  have hpos (i : κ) : 0 < |D i| :=
    abs_pos.mpr (Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ i))
  let L := (Finset.univ.filter (fun i => D i < 0)).toList
  have hL : L.Nodup := Finset.nodup_toList _
  have hm (i : κ) : i ∈ L ↔ D i < 0 := by
    simp only [L, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmatrix := diagonal_eq_abs_mul_reflections D L hL hm
  refine ⟨hpos, L, hL, hm, hmatrix, ?_, ?_⟩
  · rw [hmatrix, matrixContinuousMap_mul, coordinate_reflection_list_map]
  · rw [hmatrix, Matrix.det_mul, Matrix.det_diagonal, coordinate_reflection_list_det]

end

section

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

private theorem euclidean_coordinate_reflection_apply
    (i : ι) (x : EuclideanSpace ℝ ι) (j : ι) :
    ((ℝ ∙ EuclideanSpace.single i (1 : ℝ))ᗮ.reflection x) j =
      if j = i then -x j else x j := by
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul, PiLp.norm_single,
    norm_one, one_pow, div_one, PiLp.neg_apply, PiLp.sub_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul, nsmul_eq_mul]
  split_ifs with hj
  · subst j
    ring
  · ring

private theorem coordinateReflectionMatrix_conj_eq_reflection (i : ι) :
    (EuclideanSpace.equiv ι ℝ).symm.conjContinuousAlgEquiv
        (coordinateReflectionMatrix i).mulVecLin.toContinuousLinearMap =
      ((ℝ ∙ EuclideanSpace.single i (1 : ℝ))ᗮ.reflection.toContinuousLinearEquiv).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro j
  change (coordinateReflectionMatrix i).mulVec (fun k => x k) j =
    ((ℝ ∙ EuclideanSpace.single i (1 : ℝ))ᗮ.reflection x) j
  rw [coordinateReflectionMatrix, Matrix.mulVec_diagonal,
    euclidean_coordinate_reflection_apply]
  split_ifs <;> simp only [neg_one_mul, one_mul]

private theorem euclidean_coordinate_hyperplane_codimension_one (i : ι) :
    finrank ℝ (ℝ ∙ EuclideanSpace.single i (1 : ℝ))ᗮ + 1 =
      finrank ℝ (EuclideanSpace ℝ ι) := by
  have hi : EuclideanSpace.single i (1 : ℝ) ≠ 0 := by
    intro hzero
    have h := congrArg (fun x : EuclideanSpace ℝ ι => x i) hzero
    simp only [PiLp.single_eq_same, PiLp.zero_apply, one_ne_zero] at h
  have h := (ℝ ∙ EuclideanSpace.single i (1 : ℝ)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hi] at h
  omega

end

section

private theorem integralRelativeHomologyMap_conjContinuousAlgEquiv
    {E F : Type v} [AddCommGroup E] [AddCommGroup F]
    [Module ℝ E] [Module ℝ F] [TopologicalSpace E] [TopologicalSpace F]
    [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
    [ContinuousConstSMul ℝ E] [ContinuousConstSMul ℝ F]
    (e : E ≃L[ℝ] F) (A : E →L[ℝ] E)
    (hf : MapsTo (⟨A, A.continuous⟩ : C(E, E)) ({0}ᶜ : Set E) ({0}ᶜ : Set E)) (n : ℕ) :
    let g : C(F, F) := ⟨e.conjContinuousAlgEquiv A, (e.conjContinuousAlgEquiv A).continuous⟩
    ∃ (he : MapsTo e ({0}ᶜ : Set E) ({0}ᶜ : Set F))
      (he' : MapsTo e.symm ({0}ᶜ : Set F) ({0}ᶜ : Set E))
      (hg : MapsTo g ({0}ᶜ : Set F) ({0}ᶜ : Set F)),
      let I := integralRelativeHomologyHomeomorphIso n e.toHomeomorph {0}ᶜ {0}ᶜ he he'
      integralRelativeHomologyMap n g hg =
        I.hom.hom.comp ((integralRelativeHomologyMap n ⟨A, A.continuous⟩ hf).comp I.inv.hom) ∧
      ∀ s : ℤ, integralRelativeHomologyMap n ⟨A, A.continuous⟩ hf = s • LinearMap.id →
        integralRelativeHomologyMap n g hg = s • LinearMap.id := by
  let f : C(E, E) := ⟨A, A.continuous⟩
  let g : C(F, F) := ⟨e.conjContinuousAlgEquiv A, (e.conjContinuousAlgEquiv A).continuous⟩
  have he : MapsTo e ({0}ᶜ : Set E) ({0}ᶜ : Set F) := by
    intro x hx
    change x ≠ 0 at hx
    change e x ≠ 0
    exact fun h => hx (e.map_eq_zero_iff.mp h)
  have he' : MapsTo e.symm ({0}ᶜ : Set F) ({0}ᶜ : Set E) := by
    intro y hy
    change y ≠ 0 at hy
    change e.symm y ≠ 0
    exact fun h => hy (e.symm.map_eq_zero_iff.mp h)
  have hg : MapsTo g ({0}ᶜ : Set F) ({0}ᶜ : Set F) := he.comp (hf.comp he')
  let I := integralRelativeHomologyHomeomorphIso n e.toHomeomorph {0}ᶜ {0}ᶜ he he'
  have hconj : integralRelativeHomologyMap n g hg =
      I.hom.hom.comp ((integralRelativeHomologyMap n f hf).comp I.inv.hom) := by
    change integralRelativeHomologyMap n
      ((⟨e, e.continuous⟩ : C(E, F)).comp
        (f.comp (⟨e.symm, e.symm.continuous⟩ : C(F, E)))) (he.comp (hf.comp he')) =
      (integralRelativeHomologyMap n ⟨e, e.continuous⟩ he).comp
        ((integralRelativeHomologyMap n f hf).comp
          (integralRelativeHomologyMap n ⟨e.symm, e.symm.continuous⟩ he'))
    rw [integralRelativeHomologyMap_comp n
      (f.comp (⟨e.symm, e.symm.continuous⟩ : C(F, E)))
      (⟨e, e.continuous⟩ : C(E, F)) (hf.comp he') he,
      integralRelativeHomologyMap_comp n (⟨e.symm, e.symm.continuous⟩ : C(F, E)) f he' hf]
  have hcancel : I.hom.hom.comp I.inv.hom = LinearMap.id :=
    congrArg (fun k => k.hom) I.inv_hom_id
  refine ⟨he, he', hg, hconj, ?_⟩
  intro s hs
  change integralRelativeHomologyMap n f hf = s • LinearMap.id at hs
  rw [hconj, hs]
  apply LinearMap.ext
  intro x
  change I.hom.hom (s • I.inv.hom x) = s • x
  exact (map_zsmul I.hom.hom.toAddMonoidHom s (I.inv.hom x)).trans
    (congrArg (fun y => s • y) (DFunLike.congr_fun hcancel x))

end

section

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

private theorem coordinate_reflection_mapsTo_puncture (i : ι) :
    MapsTo (matrixContinuousMap (coordinateReflectionMatrix i))
      ({0}ᶜ : Set (ι → ℝ)) ({0}ᶜ : Set (ι → ℝ)) :=
  matrixContinuousMap_mapsTo_puncture (coordinateReflectionMatrix i)
    (by rw [coordinate_reflection_det]; norm_num)

private theorem integralRelativeHomologyMap_coordinate_reflection (i : ι) :
    integralRelativeHomologyMap (Fintype.card ι)
      (matrixContinuousMap (coordinateReflectionMatrix i))
      (coordinate_reflection_mapsTo_puncture i) = -LinearMap.id := by
  let E := EuclideanSpace ℝ ι
  let K : Submodule ℝ E := (ℝ ∙ EuclideanSpace.single i (1 : ℝ))ᗮ
  let R := K.reflection.toContinuousLinearEquiv.toContinuousLinearMap
  let e := EuclideanSpace.equiv ι ℝ
  let A := (coordinateReflectionMatrix i).mulVecLin.toContinuousLinearMap
  have hforward : e.symm.conjContinuousAlgEquiv A = R :=
    coordinateReflectionMatrix_conj_eq_reflection i
  have hback : e.conjContinuousAlgEquiv R = A := by
    calc
      e.conjContinuousAlgEquiv R =
          e.conjContinuousAlgEquiv (e.symm.conjContinuousAlgEquiv A) :=
        congrArg e.conjContinuousAlgEquiv hforward.symm
      _ = A := by
        rw [← ContinuousLinearEquiv.symm_conjContinuousAlgEquiv]
        exact e.conjContinuousAlgEquiv.apply_symm_apply A
  have hdim : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdim)
  have hR : integralRelativeHomologyMap (Fintype.card ι)
      (⟨R, R.continuous⟩ : C(E, E)) (reflection_mapsTo_pointComplement K) =
        (-1 : ℤ) • LinearMap.id := by
    rw [hn, neg_one_zsmul]
    apply LinearMap.ext
    intro a
    change integralRelativeHomologyMap (n + 1) (toContinuousMap K.reflection)
      (reflection_mapsTo_pointComplement K) a = -a
    exact integralLocalTopHomologyMap_reflection n E (by simpa only [E, finrank_euclideanSpace] using hn)
      K (euclidean_coordinate_hyperplane_codimension_one i) a
  obtain ⟨_, _, _, _, hscalar⟩ := integralRelativeHomologyMap_conjContinuousAlgEquiv
    e R (reflection_mapsTo_pointComplement K) (Fintype.card ι)
  let g : C(ι → ℝ, ι → ℝ) := ⟨e.conjContinuousAlgEquiv R, (e.conjContinuousAlgEquiv R).continuous⟩
  have hgmap : g = matrixContinuousMap (coordinateReflectionMatrix i) := by
    apply ContinuousMap.ext
    intro x
    exact congrArg (fun f : (ι → ℝ) →L[ℝ] (ι → ℝ) => f x) hback
  have hresult : ∀ hp : MapsTo g ({0}ᶜ : Set (ι → ℝ)) ({0}ᶜ : Set (ι → ℝ)),
      integralRelativeHomologyMap (Fintype.card ι) g hp = -LinearMap.id := by
    intro hp
    simpa only [neg_one_zsmul] using hscalar (-1) hR
  rw [hgmap] at hresult
  exact hresult (coordinate_reflection_mapsTo_puncture i)

end

section

private theorem integralRelativeHomologyMap_positive_diagonal
    {κ : Type z} [Fintype κ] [DecidableEq κ]
    (D : κ → ℝ) (hD : ∀ i, 0 < D i) :
    ∃ hp : MapsTo (matrixContinuousMap (Matrix.diagonal D))
        ({0}ᶜ : Set (κ → ℝ)) ({0}ᶜ : Set (κ → ℝ)),
      ∀ n : ℕ, integralRelativeHomologyMap n
        (matrixContinuousMap (Matrix.diagonal D)) hp = LinearMap.id := by
  let f := matrixContinuousMap (Matrix.diagonal D)
  let U : Set (κ → ℝ) := {0}ᶜ
  let a : unitInterval → κ → ℝ := fun t i => 1 - (t : ℝ) + (t : ℝ) * D i
  have ha (t : unitInterval) (i : κ) : 0 < a t i := by
    by_cases ht : (t : ℝ) = 0
    · simp only [a, ht, sub_zero, zero_mul, add_zero, zero_lt_one]
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr t.property.2) (mul_pos htpos (hD i))
  have havoid (t : unitInterval) (x : U) :
      (fun i => a t i * (x : κ → ℝ) i) ≠ 0 := by
    intro h
    apply x.property
    change (x : κ → ℝ) = 0
    funext i
    have hi : a t i * (x : κ → ℝ) i = 0 := congrFun h i
    exact (mul_eq_zero.mp hi).resolve_left (ha t i).ne'
  have hf (x : κ → ℝ) (i : κ) : f x i = D i * x i := Matrix.mulVec_diagonal D x i
  have hp : MapsTo f U U := by
    intro x hx
    change f x ≠ 0
    rw [(funext (hf x) : f x = (fun i => D i * x i))]
    simpa only [a, Set.Icc.coe_one, sub_self, one_mul, zero_add] using havoid 1 ⟨x, hx⟩
  let H : (singularPairRestriction (ContinuousMap.id (κ → ℝ)) (fun _ hx => hx)).Homotopy
      (singularPairRestriction f hp) :=
    { toFun := fun p => ⟨fun i => a p.1 i * (p.2 : κ → ℝ) i, havoid p.1 p.2⟩
      continuous_toFun := by
        have ht : Continuous (fun p : unitInterval × U => (p.1 : ℝ)) :=
          continuous_subtype_val.comp continuous_fst
        have hx : Continuous (fun p : unitInterval × U => (p.2 : κ → ℝ)) :=
          continuous_subtype_val.comp continuous_snd
        have hval : Continuous (fun p : unitInterval × U =>
            fun i => a p.1 i * (p.2 : κ → ℝ) i) := by
          apply continuous_pi
          intro i
          exact ((continuous_const.sub ht).add (ht.mul continuous_const)).mul
            ((continuous_apply i).comp hx)
        exact hval.subtype_mk _
      map_zero_left := by
        intro x
        apply Subtype.ext
        funext i
        simp [singularPairRestriction, a]
      map_one_left := by
        intro x
        apply Subtype.ext
        funext i
        change a 1 i * (x : κ → ℝ) i = f (x : κ → ℝ) i
        rw [hf]
        simp only [a, Set.Icc.coe_one, sub_self, one_mul, zero_add] }
  refine ⟨hp, ?_⟩
  intro n
  have heq : integralRelativeHomologyMap n f hp =
      integralRelativeHomologyMap n (ContinuousMap.id (κ → ℝ)) (fun _ hx => hx) := by
    cases n with
    | zero =>
      exact integralRelativeHomologyMap_zero_eq_of_joined f (ContinuousMap.id (κ → ℝ)) U U hp
        (fun _ hx => hx) (fun _ => ⟨PathConnectedSpace.somePath _ _⟩)
    | succ n =>
      let := integralSingularHomology_subsingleton_of_contractible (n + 1) (by omega) (κ → ℝ)
      exact (integralRelativeHomologyMap_eq_of_restriction_homotopic n
        (ContinuousMap.id (κ → ℝ)) f U U (fun _ hx => hx) hp ⟨H⟩).symm
  exact heq.trans (integralRelativeHomologyMap_id n U)

end

section

private theorem exists_reflection_product_integralRelativeHomologyMap_eq_matrix
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) :
    ∃ (L : List ι) (c : ℝ), L.Nodup ∧ 0 < c ∧ M.det = c * (-1 : ℝ) ^ L.length ∧
      ∃ (hpM : MapsTo (matrixContinuousMap M)
          ({0}ᶜ : Set (ι → ℝ)) ({0}ᶜ : Set (ι → ℝ)))
        (hpL : MapsTo (matrixContinuousMap (L.map coordinateReflectionMatrix).prod)
          ({0}ᶜ : Set (ι → ℝ)) ({0}ᶜ : Set (ι → ℝ))),
        ∀ n : ℕ, integralRelativeHomologyMap n (matrixContinuousMap M) hpM =
          integralRelativeHomologyMap n
            (matrixContinuousMap (L.map coordinateReflectionMatrix).prod) hpL := by
  obtain ⟨D, hdet, hpM, hpD, hD⟩ :=
    exists_diagonal_integralRelativeHomologyMap_eq_matrix M hM
  obtain ⟨habs, L, hL, _, hfactor, _, hdetfactor⟩ :=
    exists_diagonal_abs_reflection_factorization D (hdet.trans_ne hM)
  obtain ⟨hpA, hA⟩ := integralRelativeHomologyMap_positive_diagonal (fun i => |D i|) habs
  have hdetL : (L.map coordinateReflectionMatrix).prod.det ≠ (0 : ℝ) := by
    rw [coordinate_reflection_list_det]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hpL := matrixContinuousMap_mapsTo_puncture (L.map coordinateReflectionMatrix).prod hdetL
  refine ⟨L, ∏ i, |D i|, hL, Finset.prod_pos (fun i _ => habs i),
    hdet.symm.trans hdetfactor, hpM, hpL, ?_⟩
  intro n
  apply (hD n).trans
  have hcomp : integralRelativeHomologyMap n
      ((matrixContinuousMap (Matrix.diagonal (fun i => |D i|))).comp
        (matrixContinuousMap (L.map coordinateReflectionMatrix).prod)) (hpA.comp hpL) =
      integralRelativeHomologyMap n
        (matrixContinuousMap (L.map coordinateReflectionMatrix).prod) hpL := by
    rw [integralRelativeHomologyMap_comp n
      (matrixContinuousMap (L.map coordinateReflectionMatrix).prod)
      (matrixContinuousMap (Matrix.diagonal (fun i => |D i|))) hpL hpA, hA n]
    rfl
  simpa only [← matrixContinuousMap_mul, ← hfactor] using hcomp

end

section

private theorem integralRelativeHomologyMap_coordinate_reflection_prod
    {ι : Type u} [Fintype ι] [DecidableEq ι] (L : List ι) :
    ∃ hp : MapsTo (matrixContinuousMap (L.map coordinateReflectionMatrix).prod)
        ({0}ᶜ : Set (ι → ℝ)) ({0}ᶜ : Set (ι → ℝ)),
      integralRelativeHomologyMap (Fintype.card ι)
        (matrixContinuousMap (L.map coordinateReflectionMatrix).prod) hp =
          ((-1 : ℤ) ^ L.length) • LinearMap.id := by
  induction L with
  | nil =>
      simp only [List.map_nil, List.prod_nil, matrixContinuousMap_one,
        List.length_nil, pow_zero, one_smul]
      exact ⟨fun _ hx => hx, integralRelativeHomologyMap_id _ _⟩
  | cons i L ih =>
      obtain ⟨hpL, hL⟩ := ih
      have hpi := coordinate_reflection_mapsTo_puncture i
      simp only [List.map_cons, List.prod_cons, matrixContinuousMap_mul, List.length_cons]
      refine ⟨hpi.comp hpL, ?_⟩
      rw [integralRelativeHomologyMap_comp _ _ _ hpL hpi,
        integralRelativeHomologyMap_coordinate_reflection, hL]
      apply LinearMap.ext
      intro a
      change -(((-1 : ℤ) ^ L.length) • a) = ((-1 : ℤ) ^ (L.length + 1)) • a
      rw [pow_succ', mul_smul, neg_one_zsmul]

private theorem integralRelativeHomologyMap_matrix_eq_det_sign
    {ι : Type u} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) :
    ∃ hp : MapsTo (matrixContinuousMap M)
        ({0}ᶜ : Set (ι → ℝ)) ({0}ᶜ : Set (ι → ℝ)),
      integralRelativeHomologyMap (Fintype.card ι) (matrixContinuousMap M) hp =
        (SignType.sign M.det : ℤ) • LinearMap.id := by
  obtain ⟨L, c, _, hc, hdet, hpM, hpL, hmap⟩ :=
    exists_reflection_product_integralRelativeHomologyMap_eq_matrix M hM
  obtain ⟨_, hL⟩ := integralRelativeHomologyMap_coordinate_reflection_prod L
  have hs : (SignType.sign M.det : ℤ) = (-1 : ℤ) ^ L.length := by
    rw [hdet, sign_mul, sign_pos hc, one_mul, sign_pow,
      sign_neg (show (-1 : ℝ) < 0 by norm_num), SignType.coe_pow, SignType.coe_neg_one]
  refine ⟨hpM, (hmap _).trans ?_⟩
  rw [hL, hs]

end

section

theorem integralRelativeHomologyMap_linearEquiv_eq_det_sign
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E ≃L[ℝ] E) :
    integralRelativeHomologyMap (Module.finrank ℝ E) (toContinuousMap A)
      (show MapsTo A ({0}ᶜ : Set E) ({0}ᶜ : Set E) from
        fun _ hx h => hx (A.injective (h.trans (map_zero A).symm))) =
      (SignType.sign (LinearMap.det A.toLinearMap) : ℤ) • LinearMap.id := by
  let ι := Module.Free.ChooseBasisIndex ℝ E
  let b : Basis ι ℝ E := Module.Free.chooseBasis ℝ E
  let e := b.equivFunL
  let M : Matrix ι ι ℝ := LinearMap.toMatrix b b A.toLinearMap
  let B := M.mulVecLin.toContinuousLinearMap
  have hdim : Fintype.card ι = Module.finrank ℝ E := (Module.finrank_eq_card_basis b).symm
  have hdet : M.det = LinearMap.det A.toLinearMap := LinearMap.det_toMatrix b A.toLinearMap
  have hM : M.det ≠ 0 := hdet.trans_ne A.toLinearEquiv.isUnit_det'.ne_zero
  obtain ⟨hpM, hmatrix⟩ := integralRelativeHomologyMap_matrix_eq_det_sign M hM
  rw [hdim, hdet] at hmatrix
  have hconj : e.symm.conjContinuousAlgEquiv B = A.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    apply e.injective
    change e (e.symm (M.mulVec (e x))) = e (A x)
    rw [e.apply_symm_apply]
    exact LinearMap.toMatrix_mulVec_repr b b A.toLinearMap x
  obtain ⟨_, _, _, _, hscalar⟩ := integralRelativeHomologyMap_conjContinuousAlgEquiv
    e.symm B hpM (Module.finrank ℝ E)
  let g : C(E, E) := ⟨e.symm.conjContinuousAlgEquiv B, (e.symm.conjContinuousAlgEquiv B).continuous⟩
  have hgmap : g = toContinuousMap A := by
    apply ContinuousMap.ext
    intro x
    exact congrArg (fun f : E →L[ℝ] E => f x) hconj
  have hresult : ∀ hp : MapsTo g ({0}ᶜ : Set E) ({0}ᶜ : Set E),
      integralRelativeHomologyMap (Module.finrank ℝ E) g hp =
        (SignType.sign (LinearMap.det A.toLinearMap) : ℤ) • LinearMap.id := by
    intro hp
    exact hscalar _ hmatrix
  rw [hgmap] at hresult
  exact hresult _

end

end DifferentialGeometry.Topology
