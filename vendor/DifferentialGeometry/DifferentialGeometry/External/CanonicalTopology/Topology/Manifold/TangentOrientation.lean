module

public import DifferentialGeometry.External.CanonicalTopology.LinearAlgebra.Orientation
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Data.Bundle

@[expose] public section

section
open Filter Module Set
open scoped Topology

universe u v w

namespace DifferentialGeometry.Topology

open Classical in
private theorem basis_orientation_eventually_eq
    {X : Type u} [TopologicalSpace X] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : X → Basis ι ℝ E) (x : X)
    (hb : ∀ i, ContinuousAt (fun y => b y i) x) :
    ∀ᶠ y in 𝓝 x, (b y).orientation = (b x).orientation := by
  classical
  let : FiniteDimensional ℝ E := (b x).finiteDimensional_of_finite
  have hmatrix : ContinuousAt (fun y => (b x).toMatrix (b y)) x := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    change ContinuousAt (fun y => (b x).coord i (b y j)) x
    exact ((b x).coord i).continuous_of_finiteDimensional.continuousAt.comp (hb j)
  have hdet : ContinuousAt (fun y => (b x).det (b y)) x := by
    simpa only [Basis.det_apply, Function.comp_def, id_eq] using
      continuous_id.matrix_det.continuousAt.comp hmatrix
  have hpos : 0 < (b x).det (b x) := by rw [Basis.det_self]; exact zero_lt_one
  filter_upwards [hdet.eventually (Ioi_mem_nhds hpos)] with y hy
  exact ((b x).orientation_eq_iff_det_pos (b y)).mpr hy |>.symm

end DifferentialGeometry.Topology

end

section
open Bundle Filter Module Set
open scoped Manifold Topology

universe u v w

namespace DifferentialGeometry.Topology

open Classical in
private theorem local_frame_tangent_orientation_eq_on_nhds
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (s : ι → (x : M) → TangentSpace 𝓘(ℝ, E) x) (U : Set M)
    (hs : IsLocalFrameOn 𝓘(ℝ, E) E 0 s U) (hU : IsOpen U) (p : M) (hp : p ∈ U) :
    ∃ (V : Set M) (hVU : V ⊆ U) (hVs : V ⊆ (chartAt E p).source),
      IsOpen V ∧ p ∈ V ∧ ∀ (x : M) (hx : x ∈ V),
        Orientation.map _
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              hVs hx)).toLinearEquiv (hs.toBasisAt (hVU hx)).orientation =
          Orientation.map _
            ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ p
              (by simpa only [TangentBundle.trivializationAt_baseSet] using
                mem_chart_source E p)).toLinearEquiv (hs.toBasisAt hp).orientation := by
  let T := U ∩ (chartAt E p).source
  have hT : IsOpen T := hU.inter (chartAt E p).open_source
  have hpT : p ∈ T := ⟨hp, mem_chart_source E p⟩
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p
  let A (x : M) (hx : x ∈ T) : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E :=
    e.continuousLinearEquivAt ℝ x
      (by simpa only [e, TangentBundle.trivializationAt_baseSet] using hx.2)
  let b₀ := (hs.toBasisAt hp).map (A p hpT).toLinearEquiv
  let b (x : M) : Basis ι ℝ E :=
    if hx : x ∈ T then (hs.toBasisAt hx.1).map (A x hx).toLinearEquiv else b₀
  have hb (i : ι) : ContinuousAt (fun x => b x i) p := by
    have hc := (FiberBundle.continuousAt_section E p).mp
      (hs.contMDiffAt hU hp i).continuousAt
    apply hc.congr_of_eventuallyEq
    filter_upwards [hT.mem_nhds hpT] with x hx
    simp only [b, dite_eq_left hx, Basis.map_apply, IsLocalFrameOn.toBasisAt_coe]
    rfl
  have hlocal := basis_orientation_eventually_eq b p hb
  have hmem : ∀ᶠ x in 𝓝 p, x ∈ T := hT.mem_nhds hpT
  obtain ⟨V, hV, hVo, hpV⟩ := eventually_nhds_iff.mp (hmem.and hlocal)
  refine ⟨V, fun x hx => (hV x hx).1.1, fun x hx => (hV x hx).1.2, hVo, hpV, ?_⟩
  intro x hx
  have heq := (hV x hx).2
  simpa only [b, dite_eq_left (hV x hx).1, dite_eq_left hpT, Basis.orientation_map, A, e] using heq

open Classical in
theorem tangent_orientation_locality_of_local_frames
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) ι)
    (hframes : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∃ s : ι → (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ∃ hs : IsLocalFrameOn 𝓘(ℝ, E) E 0 s U,
          ∀ (x : M) (hx : x ∈ U), (hs.toBasisAt hx).orientation = o x) :
    ∀ p : M, ∃ (U : Set M) (hUs : U ⊆ (chartAt E p).source),
      IsOpen U ∧ p ∈ U ∧ ∀ (x : M) (hx : x ∈ U),
        Orientation.map _
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              hUs hx)).toLinearEquiv (o x) =
          Orientation.map _
            ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ p
              (by simpa only [TangentBundle.trivializationAt_baseSet] using
                mem_chart_source E p)).toLinearEquiv (o p) := by
  intro p
  obtain ⟨U, hU, hp, s, hs, ho⟩ := hframes p
  obtain ⟨V, hVU, hVs, hV, hpV, hlocal⟩ :=
    local_frame_tangent_orientation_eq_on_nhds s U hs hU p hp
  refine ⟨V, hVs, hV, hpV, ?_⟩
  intro x hx
  simpa only [ho x (hVU hx), ho p hp] using hlocal x hx

end DifferentialGeometry.Topology

end

section
open Bundle Filter Module Set
open scoped Manifold Topology

universe u v w

namespace DifferentialGeometry.Topology

open Classical in
private theorem orientation_map_eventually_eq
    {X : Type u} [TopologicalSpace X] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type w} [Finite ι]
    (b : Basis ι ℝ E) (A : X → E ≃L[ℝ] E) (x : X)
    (hA : ContinuousAt (fun y => (A y : E →L[ℝ] E)) x)
    (ω : Orientation ℝ E ι) :
    ∀ᶠ y in 𝓝 x, Orientation.map ι (A y).toLinearEquiv ω =
      Orientation.map ι (A x).toLinearEquiv ω := by
  let : Fintype ι := Fintype.ofFinite ι
  have hb (i : ι) : ContinuousAt (fun y => (b.map (A y).toLinearEquiv) i) x := by
    change ContinuousAt (fun y => (A y : E →L[ℝ] E) (b i)) x
    exact hA.clm_apply continuousAt_const
  have h := basis_orientation_eventually_eq (fun y => b.map (A y).toLinearEquiv) x hb
  rcases b.orientation_eq_or_eq_neg ω with hω | hω
  · filter_upwards [h] with y hy
    simpa only [hω, Basis.orientation_map] using hy
  · filter_upwards [h] with y hy
    simpa only [hω, Orientation.map_neg, Basis.orientation_map] using congrArg Neg.neg hy

end DifferentialGeometry.Topology
end

section
noncomputable section

open Bundle Set
open scoped Manifold Topology

universe u v w

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]

open Classical in
private def tangentChartFiberEquiv (p x : M) : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E :=
  if hx : x ∈ (chartAt E p).source then
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)
  else
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ x
      (by simpa only [TangentBundle.trivializationAt_baseSet] using mem_chart_source E x)

variable {ι : Type w} [TopologicalSpace (Orientation ℝ E ι)]

private def tangentOrientationPretrivialization (p : M) :
    Pretrivialization (Orientation ℝ E ι)
      (TotalSpace.proj : TotalSpace (Orientation ℝ E ι)
        (fun x : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) ι) → M) :=
  let A (x : M) := Orientation.map ι (tangentChartFiberEquiv p x).toLinearEquiv
  { toFun := fun z => (z.proj, A z.proj z.2)
    invFun := fun y => ⟨y.1, (A y.1).symm y.2⟩
    source := TotalSpace.proj ⁻¹' (chartAt E p).source
    target := (chartAt E p).source ×ˢ univ
    map_source' := fun _ hz => ⟨hz, mem_univ _⟩
    map_target' := fun _ hy => hy.1
    left_inv' := by
      rintro ⟨x, ω⟩ _
      exact congrArg (fun v => (⟨x, v⟩ : TotalSpace (Orientation ℝ E ι)
        (fun y : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) y) ι)))
          ((A x).symm_apply_apply ω)
    right_inv' := by
      rintro ⟨x, ω⟩ _
      exact Prod.ext rfl ((A x).apply_symm_apply ω)
    open_target := (chartAt E p).open_source.prod isOpen_univ
    baseSet := (chartAt E p).source
    open_baseSet := (chartAt E p).open_source
    source_eq := rfl
    target_eq := rfl
    proj_toFun := fun _ _ => rfl }

private theorem tangentOrientationPretrivialization_baseSet (p : M) :
    (tangentOrientationPretrivialization (E := E) (ι := ι) p).baseSet = (chartAt E p).source := rfl

open Classical in
private theorem tangentOrientationPretrivialization_apply
    (p x : M) (hx : x ∈ (chartAt E p).source)
    (ω : Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) ι) :
    tangentOrientationPretrivialization p ⟨x, ω⟩ =
      (x, Orientation.map ι
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
          (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).toLinearEquiv ω) := by
  change (x, Orientation.map ι (tangentChartFiberEquiv p x).toLinearEquiv ω) = _
  rw [tangentChartFiberEquiv, dite_eq_left hx]

open Classical in
private theorem tangentOrientationPretrivialization_symm_apply
    (p x : M) (hx : x ∈ (chartAt E p).source) (ω : Orientation ℝ E ι) :
    (tangentOrientationPretrivialization p).toPartialEquiv.symm (x, ω) =
      (⟨x, Orientation.map ι
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
          (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).symm.toLinearEquiv
          ω⟩ : TotalSpace (Orientation ℝ E ι)
            (fun y : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) y) ι)) := by
  change (⟨x, (Orientation.map ι (tangentChartFiberEquiv p x).toLinearEquiv).symm ω⟩ :
    TotalSpace (Orientation ℝ E ι)
      (fun y : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) y) ι)) = _
  rw [Orientation.map_symm, tangentChartFiberEquiv, dite_eq_left hx,
    ContinuousLinearEquiv.toLinearEquiv_symm]

end DifferentialGeometry.Topology

end
end

section
open Bundle Filter Module Set
open scoped Manifold Topology

universe u v w

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]

open Classical in
private theorem tangentOrientationPretrivialization_change_apply
    {ι : Type w} [TopologicalSpace (Orientation ℝ E ι)]
    (p q x : M) (hx : x ∈ (chartAt E p).source ∩ (chartAt E q).source)
    (ω : Orientation ℝ E ι) :
    tangentOrientationPretrivialization q
        ((tangentOrientationPretrivialization p).toPartialEquiv.symm (x, ω)) =
      (x, Orientation.map ι
        (((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).coordChangeL ℝ
          (trivializationAt E (TangentSpace 𝓘(ℝ, E)) q) x).toLinearEquiv) ω) := by
  rw [tangentOrientationPretrivialization_symm_apply p x hx.1,
    tangentOrientationPretrivialization_apply q x hx.2]
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p
  let f := trivializationAt E (TangentSpace 𝓘(ℝ, E)) q
  have hx' : x ∈ e.baseSet ∩ f.baseSet := by
    simpa only [e, f, TangentBundle.trivializationAt_baseSet] using hx
  refine congrArg (Prod.mk x) ?_
  change Orientation.map ι (f.continuousLinearEquivAt ℝ x hx'.2).toLinearEquiv
    (Orientation.map ι (e.continuousLinearEquivAt ℝ x hx'.1).symm.toLinearEquiv ω) = _
  rw [← DifferentialGeometry.orientation_map_trans]
  change Orientation.map ι
    ((e.continuousLinearEquivAt ℝ x hx'.1).symm.trans
      (f.continuousLinearEquivAt ℝ x hx'.2)).toLinearEquiv ω = _
  rw [Trivialization.comp_continuousLinearEquivAt_eq_coord_change e f hx']

open Classical in
private theorem tangent_orientation_coordChange_continuousOn
    {ι : Type w} [Finite ι] [TopologicalSpace (Orientation ℝ E ι)]
    [DiscreteTopology (Orientation ℝ E ι)] (b : Basis ι ℝ E) (p q : M) :
    ContinuousOn (fun z : M × Orientation ℝ E ι =>
      (z.1, Orientation.map ι
        (((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).coordChangeL ℝ
          (trivializationAt E (TangentSpace 𝓘(ℝ, E)) q) z.1).toLinearEquiv) z.2))
      (((chartAt E p).source ∩ (chartAt E q).source) ×ˢ univ) := by
  intro z hz
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p
  let f := trivializationAt E (TangentSpace 𝓘(ℝ, E)) q
  have hx : z.1 ∈ e.baseSet ∩ f.baseSet := by
    simpa only [e, f, TangentBundle.trivializationAt_baseSet] using hz.1
  have hA : ContinuousAt (fun x => (e.coordChangeL ℝ f x : E →L[ℝ] E)) z.1 :=
    (continuousOn_coordChange ℝ e f).continuousAt
      ((e.open_baseSet.inter f.open_baseSet).mem_nhds hx)
  have hlocal := orientation_map_eventually_eq b (e.coordChangeL ℝ f) z.1 hA z.2
  have hcont : ContinuousAt
      (fun x => Orientation.map ι (e.coordChangeL ℝ f x).toLinearEquiv z.2) z.1 :=
    continuousAt_const.congr_of_eventuallyEq hlocal
  have hjoint : ContinuousAt
      (fun y : M × Orientation ℝ E ι =>
        Orientation.map ι (e.coordChangeL ℝ f y.1).toLinearEquiv y.2) z :=
    continuousAt_prod_of_discrete_right.mpr hcont
  exact (continuousAt_fst.prodMk hjoint).continuousWithinAt

open Classical in
private theorem tangentOrientationPretrivialization_continuous_change
    {ι : Type w} [Finite ι] [TopologicalSpace (Orientation ℝ E ι)]
    [DiscreteTopology (Orientation ℝ E ι)] (b : Basis ι ℝ E) (p q : M) :
    ContinuousOn
      (tangentOrientationPretrivialization (E := E) (ι := ι) q ∘
        (tangentOrientationPretrivialization (E := E) (ι := ι) p).toPartialEquiv.symm)
      ((tangentOrientationPretrivialization (E := E) (ι := ι) p).target ∩
        (tangentOrientationPretrivialization (E := E) (ι := ι) p).toPartialEquiv.symm ⁻¹'
          (tangentOrientationPretrivialization (E := E) (ι := ι) q).source) := by
  rw [Pretrivialization.target_inter_preimage_symm_source_eq,
    tangentOrientationPretrivialization_baseSet, tangentOrientationPretrivialization_baseSet,
    Set.inter_comm (chartAt E q).source (chartAt E p).source]
  apply (tangent_orientation_coordChange_continuousOn b p q).congr
  intro z hz
  exact tangentOrientationPretrivialization_change_apply p q z.1 hz.1 z.2

open Classical in
private theorem tangentOrientationPretrivialization_continuous_transition
    [FiniteDimensional ℝ E]
    [TopologicalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E)))]
    [DiscreteTopology (Orientation ℝ E (Fin (Module.finrank ℝ E)))] (p q : M) :
    ContinuousOn
      (tangentOrientationPretrivialization (E := E) (ι := Fin (Module.finrank ℝ E)) q ∘
        (tangentOrientationPretrivialization (E := E)
          (ι := Fin (Module.finrank ℝ E)) p).toPartialEquiv.symm)
      ((tangentOrientationPretrivialization (E := E)
          (ι := Fin (Module.finrank ℝ E)) p).target ∩
        (tangentOrientationPretrivialization (E := E)
          (ι := Fin (Module.finrank ℝ E)) p).toPartialEquiv.symm ⁻¹'
          (tangentOrientationPretrivialization (E := E)
            (ι := Fin (Module.finrank ℝ E)) q).source) :=
  tangentOrientationPretrivialization_continuous_change (Module.finBasis ℝ E) p q

end DifferentialGeometry.Topology
end

section
noncomputable section

open Bundle Set
open scoped Manifold Topology

universe u v

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]

section

variable [TopologicalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E)))]
  [DiscreteTopology (Orientation ℝ E (Fin (Module.finrank ℝ E)))]
  [∀ x : M, TopologicalSpace (Orientation ℝ (TangentSpace 𝓘(ℝ, E) x)
    (Fin (Module.finrank ℝ E)))]
  [∀ x : M, DiscreteTopology (Orientation ℝ (TangentSpace 𝓘(ℝ, E) x)
    (Fin (Module.finrank ℝ E)))]

private def tangentOrientationFiberPrebundle :
    FiberPrebundle (Orientation ℝ E (Fin (Module.finrank ℝ E)))
      (fun x : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E))) where
  pretrivializationAtlas := range
    (tangentOrientationPretrivialization (E := E) (ι := Fin (Module.finrank ℝ E)))
  pretrivializationAt := tangentOrientationPretrivialization (E := E)
    (ι := Fin (Module.finrank ℝ E))
  mem_base_pretrivializationAt := mem_chart_source E
  pretrivialization_mem_atlas := mem_range_self
  continuous_trivChange := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact tangentOrientationPretrivialization_continuous_transition (E := E) q p
  totalSpaceMk_isInducing := by
    intro x
    change Topology.IsInducing (fun ω =>
      (x, Orientation.map (Fin (Module.finrank ℝ E))
        (tangentChartFiberEquiv (E := E) x x).toLinearEquiv ω))
    exact Topology.isInducing_const_prod.mpr
      (Orientation.map (Fin (Module.finrank ℝ E))
        (tangentChartFiberEquiv (E := E) x x).toLinearEquiv).toHomeomorphOfDiscrete.isInducing

end

@[instance_reducible]
private def tangentOrientationCoverTopology :
    TopologicalSpace (TotalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E)))
      (fun x : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)))) := by
  let : TopologicalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E))) := ⊥
  let : DiscreteTopology (Orientation ℝ E (Fin (Module.finrank ℝ E))) :=
    discreteTopology_bot _
  let : ∀ x : M, TopologicalSpace (Orientation ℝ (TangentSpace 𝓘(ℝ, E) x)
      (Fin (Module.finrank ℝ E))) := fun _ => ⊥
  let : ∀ x : M, DiscreteTopology (Orientation ℝ (TangentSpace 𝓘(ℝ, E) x)
      (Fin (Module.finrank ℝ E))) := fun _ => discreteTopology_bot _
  exact (tangentOrientationFiberPrebundle (E := E) (M := M)).totalSpaceTopology

private theorem tangentOrientationCoverTopology_isCoveringMap :
    @IsCoveringMap
      (TotalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E)))
        (fun x : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E))))
      M (tangentOrientationCoverTopology (E := E) (M := M)) _ TotalSpace.proj := by
  let : TopologicalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E))) := ⊥
  let : DiscreteTopology (Orientation ℝ E (Fin (Module.finrank ℝ E))) :=
    discreteTopology_bot _
  let : ∀ x : M, TopologicalSpace (Orientation ℝ (TangentSpace 𝓘(ℝ, E) x)
      (Fin (Module.finrank ℝ E))) := fun _ => ⊥
  let : ∀ x : M, DiscreteTopology (Orientation ℝ (TangentSpace 𝓘(ℝ, E) x)
      (Fin (Module.finrank ℝ E))) := fun _ => discreteTopology_bot _
  let P := tangentOrientationFiberPrebundle (E := E) (M := M)
  let : TopologicalSpace (TotalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E)))
      (fun x : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) x)
        (Fin (Module.finrank ℝ E)))) := P.totalSpaceTopology
  let : FiberBundle (Orientation ℝ E (Fin (Module.finrank ℝ E)))
      (fun x : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) x)
        (Fin (Module.finrank ℝ E))) := P.toFiberBundle
  change @IsCoveringMap
    (TotalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E)))
      (fun x : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E))))
    M P.totalSpaceTopology _ TotalSpace.proj
  exact FiberBundle.isCoveringMap

end DifferentialGeometry.Topology

end
end

section
open Bundle
open scoped Manifold Topology

universe u v

namespace DifferentialGeometry.Topology

private theorem existsUnique_tangent_orientation_cover_section
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [SimplyConnectedSpace M] (p : M)
    (ω : Orientation ℝ (TangentSpace 𝓘(ℝ, E) p) (Fin (Module.finrank ℝ E))) :
    let : TopologicalSpace (TotalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E)))
      (fun x : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)))) :=
        tangentOrientationCoverTopology (E := E) (M := M)
    ∃! s : C(M, TotalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E)))
        (fun x : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)))),
      s p = ⟨p, ω⟩ ∧ TotalSpace.proj ∘ s = id := by
  let : TopologicalSpace (TotalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (fun x : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)))) :=
      tangentOrientationCoverTopology (E := E) (M := M)
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  exact IsCoveringMap.existsUnique_continuousMap_lifts
    (tangentOrientationCoverTopology_isCoveringMap (E := E) (M := M))
    (ContinuousMap.id M) p ⟨p, ω⟩ rfl

end DifferentialGeometry.Topology
end

section
open Bundle Filter Set
open scoped Manifold Topology

universe u v

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]

private theorem exists_continuous_tangent_orientation_of_simplyConnected
    [SimplyConnectedSpace M] (p : M)
    (ω : Orientation ℝ (TangentSpace 𝓘(ℝ, E) p) (Fin (Module.finrank ℝ E))) :
    ∃ o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)),
      o p = ω ∧ @Continuous M
        (TotalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E)))
          (fun x : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E))))
        _ (tangentOrientationCoverTopology (E := E) (M := M)) (fun x => ⟨x, o x⟩) := by
  let : TopologicalSpace (TotalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (fun x : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)))) :=
      tangentOrientationCoverTopology (E := E) (M := M)
  obtain ⟨s, ⟨hp, hs⟩, _⟩ := existsUnique_tangent_orientation_cover_section p ω
  have hproj (x : M) : (s x).proj = x := congrFun hs x
  let o (x : M) : Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)) :=
    cast (congrArg (fun y => Orientation ℝ (TangentSpace 𝓘(ℝ, E) y)
      (Fin (Module.finrank ℝ E))) (hproj x)) (s x).2
  have heq (x : M) : (⟨x, o x⟩ : TotalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E)))
      (fun y : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) y)
        (Fin (Module.finrank ℝ E)))) = s x :=
    (TotalSpace.mk_cast (F := Orientation ℝ E (Fin (Module.finrank ℝ E)))
      (E := fun y : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) y)
        (Fin (Module.finrank ℝ E))) (hproj x) (s x).2).trans (TotalSpace.eta (s x))
  refine ⟨o, (TotalSpace.mk_injective p) ((heq p).trans hp), ?_⟩
  exact s.continuous.congr (fun x => (heq x).symm)

private theorem tangent_orientation_locality_of_continuous_cover_section
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)))
    (ho : @Continuous M
      (TotalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E)))
        (fun x : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E))))
      _ (tangentOrientationCoverTopology (E := E) (M := M)) (fun x => ⟨x, o x⟩)) :
    ∀ p : M, ∃ (U : Set M) (hUs : U ⊆ (chartAt E p).source),
      IsOpen U ∧ p ∈ U ∧ ∀ (x : M) (hx : x ∈ U),
        Orientation.map _
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              hUs hx)).toLinearEquiv (o x) =
          Orientation.map _
            ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ p
              (by simpa only [TangentBundle.trivializationAt_baseSet] using
                mem_chart_source E p)).toLinearEquiv (o p) := by
  let : TopologicalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E))) := ⊥
  let : DiscreteTopology (Orientation ℝ E (Fin (Module.finrank ℝ E))) :=
    discreteTopology_bot _
  let : ∀ x : M, TopologicalSpace (Orientation ℝ (TangentSpace 𝓘(ℝ, E) x)
    (Fin (Module.finrank ℝ E))) := fun _ => ⊥
  let : ∀ x : M, DiscreteTopology (Orientation ℝ (TangentSpace 𝓘(ℝ, E) x)
    (Fin (Module.finrank ℝ E))) := fun _ => discreteTopology_bot _
  let P := tangentOrientationFiberPrebundle (E := E) (M := M)
  let : TopologicalSpace (TotalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (fun x : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)))) :=
      P.totalSpaceTopology
  change Continuous (fun x => (⟨x, o x⟩ : TotalSpace
    (Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (fun y : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) y)
      (Fin (Module.finrank ℝ E))))) at ho
  intro p
  let e := P.trivializationOfMemPretrivializationAtlas (P.pretrivialization_mem_atlas p)
  let f := fun x : M => (e ⟨x, o x⟩).2
  have hc : ContinuousAt f p := by
    have he := e.toOpenPartialHomeomorph.continuousAt
      (show (⟨p, o p⟩ : TotalSpace (Orientation ℝ E (Fin (Module.finrank ℝ E)))
        (fun y : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) y)
          (Fin (Module.finrank ℝ E)))) ∈ e.source from mem_chart_source E p)
    have hs : ContinuousAt (fun x : M => (⟨x, o x⟩ : TotalSpace
        (Orientation ℝ E (Fin (Module.finrank ℝ E)))
        (fun y : M => Orientation ℝ (TangentSpace 𝓘(ℝ, E) y)
          (Fin (Module.finrank ℝ E))))) p := ho.continuousAt
    have hcomp : ContinuousAt (fun x : M => e ⟨x, o x⟩) p :=
      he.comp_of_eq hs rfl
    exact continuous_snd.continuousAt.comp hcomp
  have hlocal : ∀ᶠ x in 𝓝 p, f x = f p :=
    hc.eventually ((isOpen_discrete {f p}).mem_nhds (mem_singleton (f p)))
  have hmem : ∀ᶠ x in 𝓝 p, x ∈ (chartAt E p).source := chart_source_mem_nhds E p
  obtain ⟨U, hU, hUo, hpU⟩ := eventually_nhds_iff.mp (hmem.and hlocal)
  refine ⟨U, fun x hx => (hU x hx).1, hUo, hpU, ?_⟩
  intro x hx
  have hcoord (y : M) (hy : y ∈ (chartAt E p).source) :
      f y = Orientation.map _
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ y
          (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)).toLinearEquiv
            (o y) := by
    exact congrArg Prod.snd (tangentOrientationPretrivialization_apply p y hy (o y))
  exact (hcoord x (hU x hx).1).symm.trans
    ((hU x hx).2.trans (hcoord p (mem_chart_source E p)))

theorem exists_tangent_orientation_locality_of_simplyConnected
    [SimplyConnectedSpace M] (p : M)
    (ω : Orientation ℝ (TangentSpace 𝓘(ℝ, E) p) (Fin (Module.finrank ℝ E))) :
    ∃ o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)),
      o p = ω ∧ ∀ q : M, ∃ (U : Set M) (hUs : U ⊆ (chartAt E q).source),
        IsOpen U ∧ q ∈ U ∧ ∀ (x : M) (hx : x ∈ U),
          Orientation.map _
            ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) q).continuousLinearEquivAt ℝ x
              (by simpa only [TangentBundle.trivializationAt_baseSet] using
                hUs hx)).toLinearEquiv (o x) =
            Orientation.map _
              ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) q).continuousLinearEquivAt ℝ q
                (by simpa only [TangentBundle.trivializationAt_baseSet] using
                  mem_chart_source E q)).toLinearEquiv (o q) := by
  obtain ⟨o, hp, ho⟩ := exists_continuous_tangent_orientation_of_simplyConnected p ω
  exact ⟨o, hp, tangent_orientation_locality_of_continuous_cover_section o ho⟩

end DifferentialGeometry.Topology
end
