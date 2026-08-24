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

/-- Re-express an atlas on a normed vector-space model through a continuous linear equivalence. -/
@[instance_reducible]
public noncomputable def linearRechart
    {V V' : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup V'] [NormedSpace 𝕜 V'] [ChartedSpace V M]
    (L : V ≃L[𝕜] V') : ChartedSpace V' M := by
  let cV : ChartedSpace V' V := transportChartedSpace L.symm.toHomeomorph
  let _ : ChartedSpace V' V := cV
  exact ChartedSpace.comp V' V M

/-- A recharted local chart is the original chart followed by the linear coordinate change. -/
public theorem linearRechart_chartAt
    {V V' : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup V'] [NormedSpace 𝕜 V'] [c : ChartedSpace V M]
    (L : V ≃L[𝕜] V') (x : M) :
    @chartAt V' inferInstance M inferInstance (linearRechart L) x =
      (chartAt V x).trans L.toHomeomorph.toOpenPartialHomeomorph := by
  change (chartAt V x).trans
      (L.toHomeomorph.toOpenPartialHomeomorph.trans
        (chartAt V' (L (chartAt V x x)))) =
    (chartAt V x).trans L.toHomeomorph.toOpenPartialHomeomorph
  rw [chartAt_self_eq, trans_refl]

/-- The identity map is smooth from an atlas to its linear recharting. -/
public theorem contMDiff_id_linearRechart
    {V V' : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup V'] [NormedSpace 𝕜 V'] [c : ChartedSpace V M]
    (L : V ≃L[𝕜] V') :
    @ContMDiff 𝕜 inferInstance V inferInstance inferInstance V inferInstance
      𝓘(𝕜, V) M inferInstance c V' inferInstance inferInstance V' inferInstance
      𝓘(𝕜, V') M inferInstance (linearRechart L) n id := by
  let _ : ChartedSpace V' M := linearRechart L
  intro x
  change ContMDiffWithinAt 𝓘(𝕜, V) 𝓘(𝕜, V') n id univ x
  rw [contMDiffWithinAt_iff']
  constructor
  · exact continuousAt_id.continuousWithinAt
  · apply L.contDiff.contDiffWithinAt.congr_of_mem (fun y hy ↦ ?_) (by simp)
    simp only [Function.comp_apply, id_eq, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id]
    rw [linearRechart_chartAt]
    change L ((chartAt V x) ((chartAt V x).symm y)) = L y
    have hy' : y ∈ (chartAt V x).target := by
      simpa [extChartAt_target] using hy.1
    exact congrArg L ((chartAt V x).right_inv hy')

/-- The identity map is smooth from a linear recharting back to the original atlas. -/
public theorem contMDiff_id_linearRechart_symm
    {V V' : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup V'] [NormedSpace 𝕜 V'] [c : ChartedSpace V M]
    (L : V ≃L[𝕜] V') :
    @ContMDiff 𝕜 inferInstance V' inferInstance inferInstance V' inferInstance
      𝓘(𝕜, V') M inferInstance (linearRechart L) V inferInstance inferInstance V
      inferInstance 𝓘(𝕜, V) M inferInstance c n id := by
  let _ : ChartedSpace V' M := linearRechart L
  intro x
  change ContMDiffWithinAt 𝓘(𝕜, V') 𝓘(𝕜, V) n id univ x
  rw [contMDiffWithinAt_iff']
  constructor
  · exact continuousAt_id.continuousWithinAt
  · apply L.symm.contDiff.contDiffWithinAt.congr_of_mem (fun y hy ↦ ?_) (by simp)
    simp only [Function.comp_apply, id_eq, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id]
    rw [linearRechart_chartAt]
    have hy' : y ∈
        ((chartAt V x).trans L.toHomeomorph.toOpenPartialHomeomorph).target := by
      have hyt := hy.1
      rw [extChartAt_target] at hyt
      simpa [linearRechart_chartAt] using hyt
    have hright :=
      ((chartAt V x).trans L.toHomeomorph.toOpenPartialHomeomorph).right_inv hy'
    have hright' := congrArg L.symm hright
    change L.symm
        (L ((chartAt V x)
          (((chartAt V x).trans L.toHomeomorph.toOpenPartialHomeomorph).symm y))) =
      L.symm y at hright'
    simpa only [L.symm_apply_apply] using hright'

/-- The identity equivalence is a diffeomorphism between an atlas and its linear recharting. -/
public noncomputable def linearRechartDiffeomorph
    {V V' : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup V'] [NormedSpace 𝕜 V'] [c : ChartedSpace V M]
    [IsManifold 𝓘(𝕜, V) n M] (L : V ≃L[𝕜] V') :
    let _ : ChartedSpace V' M := linearRechart L
    @Diffeomorph 𝕜 inferInstance V inferInstance inferInstance V' inferInstance inferInstance
      V inferInstance V' inferInstance 𝓘(𝕜, V) 𝓘(𝕜, V') M inferInstance c M
      inferInstance inferInstance n := by
  let _ : ChartedSpace V' M := linearRechart L
  exact
    { toEquiv := Equiv.refl M
      contMDiff_toFun := contMDiff_id_linearRechart L
      contMDiff_invFun := contMDiff_id_linearRechart_symm L }

/-- Linear recharting preserves the manifold structure and differentiability order. -/
public theorem isManifold_linearRechart
    {V V' : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup V'] [NormedSpace 𝕜 V'] [ChartedSpace V M]
    [IsManifold 𝓘(𝕜, V) n M] (L : V ≃L[𝕜] V') :
    @IsManifold 𝕜 inferInstance V' inferInstance inferInstance V' inferInstance
      𝓘(𝕜, V') n M inferInstance (linearRechart L) := by
  let cV : ChartedSpace V' V := transportChartedSpace L.symm.toHomeomorph
  let _ : ChartedSpace V' V := cV
  let mV : IsManifold 𝓘(𝕜, V') n V :=
    isManifold_transportChartedSpace L.symm.toHomeomorph
  let _ : IsManifold 𝓘(𝕜, V') n V := mV
  let cM : ChartedSpace V' M := ChartedSpace.comp V' V M
  change @IsManifold 𝕜 inferInstance V' inferInstance inferInstance V' inferInstance
    𝓘(𝕜, V') n M inferInstance cM
  let _ : ChartedSpace V' M := cM
  have smooth_rechart (f : V → V) (s : Set V)
      (hf : ContMDiffOn 𝓘(𝕜, V) 𝓘(𝕜, V) n f s) :
      ContMDiffOn 𝓘(𝕜, V') 𝓘(𝕜, V') n f s := by
    have hfcd : ContDiffOn 𝕜 n f s := contMDiffOn_iff_contDiffOn.mp hf
    have hpre : ContDiffOn 𝕜 n (fun z : V' ↦ f (L.symm z)) (L.symm ⁻¹' s) :=
      hfcd.comp L.symm.contDiff.contDiffOn (mapsTo_preimage _ _)
    have hmid : ContDiffOn 𝕜 n (fun z : V' ↦ L (f (L.symm z))) (L.symm ⁻¹' s) :=
      L.contDiff.comp_contDiffOn hpre
    have hmidM : ContMDiffOn 𝓘(𝕜, V') 𝓘(𝕜, V') n
        (fun z : V' ↦ L (f (L.symm z))) (L.symm ⁻¹' s) :=
      contMDiffOn_iff_contDiffOn.mpr hmid
    let d : V' ≃ₘ^n⟮𝓘(𝕜, V'), 𝓘(𝕜, V')⟯ V :=
      transportDiffeomorph L.symm.toHomeomorph
    have hds : ContMDiffOn 𝓘(𝕜, V') 𝓘(𝕜, V') n (fun x : V ↦ L x) s :=
      d.symm.contMDiff.contMDiffOn
    have hcomp : ContMDiffOn 𝓘(𝕜, V') 𝓘(𝕜, V') n
        ((fun z : V' ↦ L (f (L.symm z))) ∘ fun x : V ↦ L x) s :=
      hmidM.comp hds (by
        intro x hx
        simp only [Set.mem_preimage]
        simpa using hx)
    have hd : ContMDiff 𝓘(𝕜, V') 𝓘(𝕜, V') n (fun z : V' ↦ L.symm z) :=
      d.contMDiff
    have hfinal : ContMDiffOn 𝓘(𝕜, V') 𝓘(𝕜, V') n
        ((fun z : V' ↦ L.symm z) ∘
          ((fun z : V' ↦ L (f (L.symm z))) ∘ fun x : V ↦ L x)) s :=
      hd.comp_contMDiffOn hcomp
    convert hfinal using 1
    funext x
    simp
  let hG : HasGroupoid M (contDiffGroupoid n 𝓘(𝕜, V')) := by
    refine StructureGroupoid.HasGroupoid.comp (contDiffGroupoid n 𝓘(𝕜, V)) ?_
    intro f hf
    rw [isLocalStructomorphOn_contDiffGroupoid_iff]
    exact ⟨smooth_rechart f f.source (contMDiffOn_of_mem_contDiffGroupoid hf),
      smooth_rechart f.symm f.target
        (contMDiffOn_of_mem_contDiffGroupoid
          ((contDiffGroupoid n 𝓘(𝕜, V)).symm hf))⟩
  exact @IsManifold.mk' 𝕜 inferInstance V' inferInstance inferInstance V' inferInstance
    𝓘(𝕜, V') n M inferInstance cM hG

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
