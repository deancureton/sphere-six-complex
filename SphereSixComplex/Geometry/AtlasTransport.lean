module

public import SphereSixComplex.ComplexStructure

/-!
# Transporting manifold atlases

This file provides a charted-space construction whose transition functions are unchanged when an
atlas is transported through a homeomorphism.
-/

@[expose] public section

open Set OpenPartialHomeomorph Manifold
open scoped ContDiff Manifold

namespace SphereSixComplex

universe u v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type w} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

/-- Transport a charted-space structure through a homeomorphism. -/
@[instance_reducible]
public def transportChartedSpace [ChartedSpace H M] (h : M ≃ₜ N) :
    ChartedSpace H N where
  atlas := (fun e ↦ h.symm.toOpenPartialHomeomorph.trans e) '' atlas H M
  chartAt x := h.symm.toOpenPartialHomeomorph.trans (chartAt H (h.symm x))
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨chartAt H (h.symm x), chart_mem_atlas H (h.symm x), rfl⟩

/-- Composing the model atlas commutes with transporting the manifold atlas. -/
public theorem comp_transportChartedSpace {H' : Type*} [TopologicalSpace H']
    (cModel : ChartedSpace H H') (cM : ChartedSpace H' M) (h : M ≃ₜ N) :
    @ChartedSpace.comp H inferInstance H' inferInstance N inferInstance cModel
      (@transportChartedSpace H' inferInstance M N inferInstance inferInstance cM h) =
    @transportChartedSpace H inferInstance M N inferInstance inferInstance
      (@ChartedSpace.comp H inferInstance H' inferInstance M inferInstance cModel cM) h := by
  apply ChartedSpace.ext
  · ext e
    constructor
    · rintro ⟨e', ⟨c, hc, rfl⟩, d, hd, rfl⟩
      refine ⟨c.trans d, ⟨c, hc, d, hd, rfl⟩, ?_⟩
      rw [trans_assoc]
    · rintro ⟨e', ⟨c, hc, d, hd, rfl⟩, rfl⟩
      refine ⟨h.symm.toOpenPartialHomeomorph.trans c, ⟨c, hc, rfl⟩, d, hd, ?_⟩
      rw [trans_assoc]
  · funext x
    change
      (h.symm.toOpenPartialHomeomorph.trans (chartAt H' (h.symm x))).trans (chartAt H _) =
        h.symm.toOpenPartialHomeomorph.trans ((chartAt H' (h.symm x)).trans (chartAt H _))
    exact trans_assoc _ _ _

/-- Transporting a manifold atlas through a homeomorphism preserves its structure groupoid. -/
public theorem isManifold_transportChartedSpace [ChartedSpace H M]
    [IsManifold I n M] (h : M ≃ₜ N) :
    @IsManifold 𝕜 _ E _ _ H _ I n N _ (transportChartedSpace h) := by
  let cN : ChartedSpace H N := transportChartedSpace h
  let hG : @HasGroupoid H _ N _ cN (contDiffGroupoid n I) := by
    refine ⟨?_⟩
    rintro e e' ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    rw [trans_symm_eq_symm_trans_symm, trans_assoc,
      ← Homeomorph.symm_toOpenPartialHomeomorph, Homeomorph.symm_symm]
    rw [← trans_assoc h.toOpenPartialHomeomorph h.symm.toOpenPartialHomeomorph c']
    rw [← Homeomorph.trans_toOpenPartialHomeomorph, Homeomorph.self_trans_symm,
      Homeomorph.refl_toOpenPartialHomeomorph, refl_trans]
    exact (contDiffGroupoid n I).compatible hc hc'
  exact @IsManifold.mk' 𝕜 _ E _ _ H _ I n N _ cN hG

/-- A homeomorphism is a diffeomorphism to the charted space obtained by transporting the source
atlas along it. -/
public noncomputable def transportDiffeomorph [ChartedSpace H M] [IsManifold I n M]
    (h : M ≃ₜ N) :
    @Diffeomorph 𝕜 _ E _ _ E _ _ H _ H _ I I M inferInstance inferInstance N inferInstance
      (transportChartedSpace h) n := by
  letI cN : ChartedSpace H N := transportChartedSpace h
  letI mN : IsManifold I n N := isManifold_transportChartedSpace h
  have hlocal : ChartedSpace.LiftPropOn
      (contDiffGroupoid n I).IsLocalStructomorphWithinAt (⇑h) univ := by
    intro x _
    refine ⟨h.continuous.continuousWithinAt, ?_⟩
    intro _
    let e := (OpenPartialHomeomorph.refl H).restr (chartAt H x).target
    refine ⟨e, ?_, ?_, ?_⟩
    · exact closedUnderRestriction' (contDiffGroupoid n I).id_mem (chartAt H x).open_target
    · intro z hz
      change (chartAt H (h.symm (h x))) (h.symm (h ((chartAt H x).symm z))) = z
      simp only [h.symm_apply_apply]
      simp only [e, OpenPartialHomeomorph.restr_source,
        (chartAt H x).open_target.interior_eq] at hz
      exact (chartAt H x).right_inv hz.2.2
    · simp only [e, OpenPartialHomeomorph.restr_source,
        (chartAt H x).open_target.interior_eq]
      exact ⟨by simp, mem_chart_target H x⟩
  have hsmooth :=
    (isLocalStructomorphOn_contDiffGroupoid_iff h.toOpenPartialHomeomorph).1 hlocal
  refine
    { toEquiv := h.toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · rw [← contMDiffOn_univ]
    change ContMDiffOn I I n (⇑h) univ
    have hsmooth' := hsmooth.1
    change ContMDiffOn I I n (⇑h) univ at hsmooth'
    exact hsmooth'
  · rw [← contMDiffOn_univ]
    change ContMDiffOn I I n (⇑h.symm) univ
    have hsmooth' := hsmooth.2
    change ContMDiffOn I I n (⇑h.symm) univ at hsmooth'
    exact hsmooth'

/-- The topological part of admitting a complex manifold structure. -/
public def AdmitsTopologicalComplexStructure (M : Type*) [TopologicalSpace M] : Prop :=
  ∃ c : ChartedSpace ComplexModel M,
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel inferInstance
      𝓘(ℂ, ComplexModel) ∞ M inferInstance c

/-- A complex manifold structure transports through any homeomorphism. -/
public theorem admitsTopologicalComplexStructure_of_homeomorph [ChartedSpace ComplexModel M]
    [IsManifold 𝓘(ℂ, ComplexModel) ∞ M] (h : M ≃ₜ N) :
    AdmitsTopologicalComplexStructure N := by
  exact ⟨transportChartedSpace h, isManifold_transportChartedSpace h⟩

/-- The property of admitting a topological complex structure is invariant under homeomorphism. -/
public theorem AdmitsTopologicalComplexStructure.homeomorph (hM : AdmitsTopologicalComplexStructure M)
    (h : M ≃ₜ N) : AdmitsTopologicalComplexStructure N := by
  obtain ⟨c, hc⟩ := hM
  exact
    ⟨@transportChartedSpace ComplexModel inferInstance M N inferInstance inferInstance c h,
      @isManifold_transportChartedSpace ℂ inferInstance ComplexModel inferInstance inferInstance
        ComplexModel inferInstance 𝓘(ℂ, ComplexModel) ∞ M N inferInstance inferInstance c hc h⟩

/-- Passing to the underlying real atlas commutes with transport. -/
public theorem underlyingRealChartedSpace_transport (c : ChartedSpace ComplexModel M)
    (h : M ≃ₜ N) :
    underlyingRealChartedSpace (transportChartedSpace h : ChartedSpace ComplexModel N) =
      @transportChartedSpace RealModel inferInstance M N inferInstance inferInstance
        (underlyingRealChartedSpace c) h := by
  exact comp_transportChartedSpace complexModelRealChartedSpace c h

/-- Smooth compatibility transports along a diffeomorphism of the specified real atlases. -/
public theorem smoothlyCompatible_transport_diffeomorph
    [standardM : ChartedSpace RealModel M] [standardN : ChartedSpace RealModel N]
    (c : ChartedSpace ComplexModel M)
    (realManifold :
      @IsManifold ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
        𝓘(ℝ, RealModel) ∞ M inferInstance (underlyingRealChartedSpace c))
    (hc : SmoothlyCompatible standardM c)
    (d :
      @Diffeomorph ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
        inferInstance RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel)
        𝓘(ℝ, RealModel) M inferInstance standardM N inferInstance standardN ∞) :
    SmoothlyCompatible standardN
      (@transportChartedSpace ComplexModel inferInstance M N inferInstance inferInstance c
        d.toHomeomorph) := by
  unfold SmoothlyCompatible at hc ⊢
  obtain ⟨q⟩ := hc
  rw [underlyingRealChartedSpace_transport]
  let h : M ≃ₜ N := d.toHomeomorph
  let cReal : ChartedSpace RealModel M := underlyingRealChartedSpace c
  let t := @transportDiffeomorph ℝ inferInstance RealModel inferInstance inferInstance RealModel
    inferInstance 𝓘(ℝ, RealModel) ∞ M N inferInstance inferInstance cReal realManifold h
  let tsymm := @Diffeomorph.symm ℝ inferInstance RealModel inferInstance inferInstance RealModel
    inferInstance inferInstance RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel)
    𝓘(ℝ, RealModel) M inferInstance (underlyingRealChartedSpace c) N inferInstance
    (transportChartedSpace h) ∞ t
  let qd := @Diffeomorph.trans ℝ inferInstance RealModel inferInstance inferInstance RealModel
    inferInstance inferInstance RealModel inferInstance inferInstance RealModel inferInstance
    RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel)
    𝓘(ℝ, RealModel) M inferInstance (underlyingRealChartedSpace c) M inferInstance standardM N
    inferInstance standardN ∞ q d
  let result :
      @Diffeomorph ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
        inferInstance RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel)
        𝓘(ℝ, RealModel) N inferInstance (transportChartedSpace h) N inferInstance standardN ∞ :=
    @Diffeomorph.trans ℝ inferInstance RealModel inferInstance inferInstance RealModel
      inferInstance inferInstance RealModel inferInstance inferInstance RealModel inferInstance
      RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel)
      𝓘(ℝ, RealModel) N inferInstance (transportChartedSpace h) M inferInstance
      (underlyingRealChartedSpace c) N inferInstance standardN ∞ tsymm qd
  exact ⟨result⟩

/-- A complex manifold whose underlying real atlas is diffeomorphic to a specified target atlas
transports to a complex structure compatible with that target atlas. -/
public theorem admitsComplexStructure_of_diffeomorph
    [standardN : ChartedSpace RealModel N] (c : ChartedSpace ComplexModel M)
    (complexManifold :
      @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
        inferInstance 𝓘(ℂ, ComplexModel) ∞ M inferInstance c)
    (realManifold :
      @IsManifold ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
        𝓘(ℝ, RealModel) ∞ M inferInstance (underlyingRealChartedSpace c))
    (d :
      @Diffeomorph ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
        inferInstance RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel)
        𝓘(ℝ, RealModel) M inferInstance (underlyingRealChartedSpace c) N inferInstance standardN
        ∞) :
    AdmitsComplexStructure N := by
  let h : M ≃ₜ N := @Diffeomorph.toHomeomorph ℝ inferInstance RealModel inferInstance
    inferInstance RealModel inferInstance inferInstance RealModel inferInstance RealModel
    inferInstance 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) M inferInstance
    (underlyingRealChartedSpace c) N inferInstance standardN ∞ d
  let cN : ChartedSpace ComplexModel N := transportChartedSpace h
  refine ⟨cN, ?_, ?_⟩
  · exact @isManifold_transportChartedSpace ℂ inferInstance ComplexModel inferInstance
      inferInstance ComplexModel inferInstance 𝓘(ℂ, ComplexModel) ∞ M N inferInstance
      inferInstance c complexManifold h
  · unfold SmoothlyCompatible
    rw [show underlyingRealChartedSpace cN =
      @transportChartedSpace RealModel inferInstance M N inferInstance inferInstance
        (underlyingRealChartedSpace c) h from underlyingRealChartedSpace_transport c h]
    let cReal : ChartedSpace RealModel M := underlyingRealChartedSpace c
    let t := @transportDiffeomorph ℝ inferInstance RealModel inferInstance inferInstance RealModel
      inferInstance 𝓘(ℝ, RealModel) ∞ M N inferInstance inferInstance cReal realManifold h
    let tsymm := @Diffeomorph.symm ℝ inferInstance RealModel inferInstance inferInstance RealModel
      inferInstance inferInstance RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel)
      𝓘(ℝ, RealModel) M inferInstance (underlyingRealChartedSpace c) N inferInstance
      (transportChartedSpace h) ∞ t
    let result := @Diffeomorph.trans ℝ inferInstance RealModel inferInstance inferInstance
      RealModel inferInstance inferInstance RealModel inferInstance inferInstance RealModel
      inferInstance RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel)
      𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) N inferInstance (transportChartedSpace h) M
      inferInstance (underlyingRealChartedSpace c) N inferInstance standardN ∞ tsymm d
    exact ⟨result⟩

end SphereSixComplex
