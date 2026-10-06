module

public import DifferentialGeometry.Topology.Morse.NormalForm.Manifold
public import DifferentialGeometry.Bundle.TangentSpace
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

@[expose] public section

namespace DifferentialGeometry.Topology.Morse

open Manifold Set
open scoped Manifold ContDiff

noncomputable section


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}

omit [FiniteDimensional ℝ E] in
theorem portPrivate_3bb32062_exists_vector_of_fderiv_ne_zero (g : E → ℝ) (y : E)
    (h : fderiv ℝ g y ≠ 0) :
    ∃ v : E, (fderiv ℝ g y) v ≠ 0 := by
  by_contra! hv
  apply h
  ext v
  exact hv v

omit [FiniteDimensional ℝ E] in
theorem portPrivate_3bb32062_chartRep_contDiffOn (I : ModelWithCorners ℝ E H)
    [IsManifold I ∞ M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (x₀ : M) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => f ((extChartAt I x₀).symm y))
      (extChartAt I x₀).target := by
  have hc : ContMDiffOn I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f Set.univ := by
    intro x hx
    exact hf x
  have hcsub : ContMDiffOn I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (chartAt H x₀).source :=
    hc.mono (by intro x hx; trivial)
  have hc' : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀ '' (chartAt H x₀).source) :=
    (contMDiffOn_iff_source_of_mem_maximalAtlas (I := I) (I' := 𝓘(ℝ, ℝ))
    (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (e := chartAt H x₀) (IsManifold.chart_mem_maximalAtlas x₀)
    (s := (chartAt H x₀).source) (hs := by intro x hx; exact hx)).1 hcsub
  have hcd : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ (extChartAt I x₀).symm)
      (extChartAt I x₀ '' (chartAt H x₀).source) :=
    (contMDiffOn_iff_contDiffOn).1 hc'
  have hrange : extChartAt I x₀ '' (chartAt H x₀).source = (extChartAt I x₀).target := by
    exact (OpenPartialHomeomorph.extend_target_eq_image_source (f := chartAt H x₀) (I := I)).symm
  rw [show (fun y : E => f ((extChartAt I x₀).symm y)) = f ∘ (extChartAt I x₀).symm by rfl]
  rwa [← hrange]

omit [FiniteDimensional ℝ E] in
theorem tangentTrivializationAt_apply (I : ModelWithCorners ℝ E H)
    [IsManifold I ∞ M] (x₀ x : M)
    (hx : x ∈ (extChartAt I x₀).source) (v : TangentSpace I x) :
    (trivializationAt E (TangentSpace I) x₀ ⟨x, v⟩).2 =
      tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E))
        (extChartAt I x₀ x) ((mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x) v) := by
  have hxsrc : x ∈ (chartAt H x₀).source := by
    rwa [extChartAt_source (I := I) (x := x₀)] at hx
  have hmd : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x₀) x :=
    mdifferentiableAt_extChartAt hxsrc
  have htriv :
      (trivializationAt E (TangentSpace I) x₀ ⟨x, v⟩).2 =
        fderivWithin ℝ
          (writtenInExtChartAt I 𝓘(ℝ, E) x (extChartAt I x₀)) (range I)
          (extChartAt I x x) (tangentSpaceModelContinuousLinearEquiv (I := I) x v) := by
    rw [TangentBundle.trivializationAt_apply]
    rfl
  rw [htriv]
  have hmf :
      tangentLinearMapToModel (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x) =
        fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ, E) x (extChartAt I x₀))
          (range I) (extChartAt I x x) :=
    congrArg (fun A => tangentLinearMapToModel A) hmd.mfderiv
  have hmfv := DFunLike.congr_fun hmf
    (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
  simpa only [tangentLinearMapToModel_apply,
    ContinuousLinearEquiv.symm_apply_apply] using hmfv.symm

omit [FiniteDimensional ℝ E] in
theorem localUnitSpeedVectorField_at_noncritical (I : ModelWithCorners ℝ E H)
    [I.Boundaryless] [IsManifold I ∞ M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    {x₀ : M} (hcrit : ¬ IsCriticalPointAt I f x₀) :
    ∃ v₀ : E,
      (fderiv ℝ (fun y : E => f ((extChartAt I x₀).symm y)) (extChartAt I x₀ x₀)) v₀ ≠ 0 ∧
      ∃ W : (x : M) → TangentSpace I x,
        ∀ x ∈ (extChartAt I x₀).source,
          (fderiv ℝ (fun y : E => f ((extChartAt I x₀).symm y)) (extChartAt I x₀ x)) v₀ ≠ 0 →
          tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E))
              (extChartAt I x₀ x)
              ((mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x) (W x)) =
              -(((fderiv ℝ (fun y : E => f ((extChartAt I x₀).symm y))
                  (extChartAt I x₀ x)) v₀)⁻¹) • v₀ ∧
          (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (W x)) = -1 := by
  have hgOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => f ((extChartAt I x₀).symm y))
      (extChartAt I x₀).target := portPrivate_3bb32062_chartRep_contDiffOn I f hf x₀
  have hmemx₀ : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (mem_extChartAt_source x₀)
  have hcritChart : fderiv ℝ (fun y : E => f ((extChartAt I x₀).symm y))
      (extChartAt I x₀ x₀) ≠ 0 := by
    have hiff := isCriticalPointAt_iff_chart_fderiv (I := I) (f := f) hf (p := x₀)
    intro hz
    exact hcrit (hiff.2 hz)
  rcases portPrivate_3bb32062_exists_vector_of_fderiv_ne_zero (fun y : E => f ((extChartAt I x₀).symm y))
    (extChartAt I x₀ x₀) hcritChart with ⟨v₀, hv₀⟩
  let e : PartialEquiv M E := extChartAt I x₀
  let g : E → ℝ := fun y => f (e.symm y)
  let a : M → ℝ := fun x => (fderiv ℝ g (e x)) (v₀)
  let W : (x : M) → TangentSpace I x := fun x =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
      (tangentSpaceModelContinuousLinearEquiv (I := I) (e.symm (e x))
        ((mfderivWithin 𝓘(ℝ, E) I e.symm (range I) (e x))
          ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) (e x)).symm
            (-(a x)⁻¹ • v₀))))
  refine ⟨v₀, ?_, W, ?_⟩
  · simpa [g, e] using hv₀
  intro x hx hane
  have hane_g : (fderiv ℝ g (e x)) (v₀) ≠ 0 := by
    simpa [g, e] using hane
  have hepx : e.symm (e x) = x := e.left_inv hx
  have hmemx : e x ∈ (extChartAt I x₀).target := e.map_source hx
  have hmdg := ((hgOn (e x) hmemx).contDiffAt ((isOpen_extChartAt_target x₀).mem_nhds hmemx)).differentiableAt
    (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have hxsrc : x ∈ (chartAt H x₀).source := by
    rwa [extChartAt_source (I := I) (x := x₀)] at hx
  have hmdchart := (contMDiffAt_extChartAt' (I := I)
    (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := x₀) hxsrc).mdifferentiableAt (by norm_num)
  have hcomp := mfderiv_comp (x := x) (g := g) (f := e) (hg := hmdg.mdifferentiableAt) (hf := hmdchart)
  have hfuneq : (fun y : M => f y) =ᶠ[nhds x] (fun y : M => g (e y)) := by
    have hsrcopen : IsOpen e.source := isOpen_extChartAt_source x₀
    exact Filter.eventuallyEq_of_mem (by simpa [e] using (hsrcopen.mem_nhds hx))
      (fun y hy => congrArg f (e.left_inv hy).symm)
  have heq := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) hfuneq
  have hge : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g (e x) = fderiv ℝ g (e x) := by
    exact (mfderiv_eq_fderiv (𝕜 := ℝ) (E := E) (E' := ℝ) (f := g) (x := e x))
  have hid := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x₀)
    (y := e x) (by simpa [e] using hmemx)
  have hidRaw :
      (mfderiv I 𝓘(ℝ, E) e (e.symm (e x))).comp
          (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) (e x)) =
        ContinuousLinearMap.id ℝ
          (TangentSpace 𝓘(ℝ, E) (e x)) := by
    simpa [e] using hid
  have hidModel :
      tangentLinearMapToModel
          ((mfderiv I 𝓘(ℝ, E) e (e.symm (e x))).comp
            (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) (e x))) =
        (1 : E →L[ℝ] E) :=
    congrArg (fun A => tangentLinearMapToModel A) hidRaw
  have hidapplyRaw : ∀ w : E,
      tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E))
          (e (e.symm (e x)))
        ((mfderiv I 𝓘(ℝ, E) e (e.symm (e x)))
          ((mfderivWithin 𝓘(ℝ, E) I e.symm (range I) (e x))
            ((tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(ℝ, E)) (e x)).symm w))) = w := by
    intro w
    have hw := DFunLike.congr_fun hidModel w
    calc
      _ = tangentLinearMapToModel
          ((mfderiv I 𝓘(ℝ, E) e (e.symm (e x))).comp
            (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) (e x))) w := by
          rw [tangentLinearMapToModel_apply, ContinuousLinearMap.comp_apply]
      _ = (1 : E →L[ℝ] E) w := hw
      _ = w := by rfl
  rw [hepx] at hidapplyRaw
  have hchartW :
      tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) (e x)
          ((mfderiv I 𝓘(ℝ, E) e x) (W x)) =
        -(a x)⁻¹ • (v₀ : E) := by
    dsimp only [W]
    rw [hepx]
    simpa only [ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.symm_apply_apply] using
      hidapplyRaw (-(a x)⁻¹ • (v₀ : E))
  have hfinal : (fderiv ℝ g (e x)) (-(a x)⁻¹ • (v₀ : E)) = -1 := by
    rw [(fderiv ℝ g (e x)).map_smul]
    rw [smul_eq_mul]
    have haval : (fderiv ℝ g (e x)) (v₀) = a x := by
      dsimp [a]
    rw [← haval]
    field_simp [hane_g]
  have heqModel := congrArg (fun A => tangentLinearMapToModel A) heq
  have hcompModel := congrArg (fun A => tangentLinearMapToModel A) hcomp
  have hgeModel :
      tangentLinearMapToModel
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g (e x)) =
        fderiv ℝ g (e x) :=
    congrArg (fun A => tangentLinearMapToModel A) hge
  have hmain :
      tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ)) (f x)
          ((mfderiv I 𝓘(ℝ, ℝ) f x) (W x)) = -1 := by
    let wx := tangentSpaceModelContinuousLinearEquiv (I := I) x (W x)
    calc
      _ = tangentLinearMapToModel (mfderiv I 𝓘(ℝ, ℝ) f x) wx := by
        rw [tangentLinearMapToModel_apply]
        simp [wx]
      _ = tangentLinearMapToModel
          (mfderiv I 𝓘(ℝ, ℝ) (fun y => g (e y)) x) wx :=
        DFunLike.congr_fun heqModel wx
      _ = tangentLinearMapToModel
          ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g (e x)).comp
            (mfderiv I 𝓘(ℝ, E) e x)) wx :=
        DFunLike.congr_fun hcompModel wx
      _ = tangentLinearMapToModel
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g (e x))
            (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) (e x)
              ((mfderiv I 𝓘(ℝ, E) e x) (W x))) := by
        rw [tangentLinearMapToModel_apply, tangentLinearMapToModel_apply,
          ContinuousLinearMap.comp_apply]
        simp [wx]
      _ = fderiv ℝ g (e x)
          (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) (e x)
            ((mfderiv I 𝓘(ℝ, E) e x) (W x))) := by
        rw [hgeModel]
      _ = -1 := by
        rw [hchartW]
        exact hfinal
  have hts : (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (W x)) =
      tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ)) (f x)
        ((mfderiv I 𝓘(ℝ, ℝ) f x) (W x)) := by
    rfl
  constructor
  · change
      tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) (e x)
          ((mfderiv I 𝓘(ℝ, E) e x) (W x)) =
        -(((fderiv ℝ (fun y : E => f (e.symm y)) (e x))
          (v₀))⁻¹) •
          (v₀ : E)
    simpa only [a, g] using hchartW
  · rw [hts]
    exact hmain

omit [FiniteDimensional ℝ E] in
theorem exists_open_unitSpeedVectorField_at_noncritical (I : ModelWithCorners ℝ E H)
    [I.Boundaryless] [IsManifold I ∞ M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    {x₀ : M} (hcrit : ¬ IsCriticalPointAt I f x₀) :
    ∃ (U : Set M), x₀ ∈ U ∧ IsOpen U ∧
      ∃ W : (x : M) → TangentSpace I x,
        (∀ x ∈ U, (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (W x)) = -1) ∧
        ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
          (fun x : M => (⟨x, W x⟩ : TangentBundle I M)) U := by
  rcases localUnitSpeedVectorField_at_noncritical I f hf hcrit with ⟨v₀, hv₀, W, hW⟩
  let p : M → ℝ := fun x => (fderiv ℝ (fun y : E => f ((extChartAt I x₀).symm y))
    (extChartAt I x₀ x)) (v₀)
  have hgOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => f ((extChartAt I x₀).symm y))
      (extChartAt I x₀).target := portPrivate_3bb32062_chartRep_contDiffOn I f hf x₀
  have hcont : ContinuousOn p (extChartAt I x₀).source := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ (fun y : E => f ((extChartAt I x₀).symm y)))
        (extChartAt I x₀).target :=
      hgOn.fderiv_of_isOpen (isOpen_extChartAt_target x₀)
        (by
          change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hcontfd : ContinuousOn (fderiv ℝ (fun y : E => f ((extChartAt I x₀).symm y)))
        (extChartAt I x₀).target := hfd.continuousOn
    have hconte : ContinuousOn (extChartAt I x₀) (extChartAt I x₀).source := by
      simpa [extChartAt_source (I := I) (x := x₀)] using
        (contMDiffOn_extChartAt (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
          (x := x₀)).continuousOn
    have hcomp' : ContinuousOn (fun x : M =>
        (fderiv ℝ (fun y : E => f ((extChartAt I x₀).symm y))) (extChartAt I x₀ x))
        (extChartAt I x₀).source :=
      hcontfd.comp hconte (by intro x hx; exact (extChartAt I x₀).map_source hx)
    have happly : Continuous (fun L : (E →L[ℝ] ℝ) => L (v₀)) :=
      (ContinuousLinearMap.apply ℝ ℝ (v₀) : (E →L[ℝ] ℝ) →L[ℝ] ℝ).cont
    simpa [p, Function.comp_def] using (happly.comp_continuousOn hcomp')
  have hmem : x₀ ∈ (extChartAt I x₀).source := mem_extChartAt_source x₀
  have hne₀ : p x₀ ≠ 0 := by
    simpa [p] using hv₀
  have hV : {x : M | p x ≠ 0} ∈ nhds x₀ := by
    have hcontAt : ContinuousAt p x₀ :=
      (hcont x₀ hmem).continuousAt ((isOpen_extChartAt_source x₀).mem_nhds hmem)
    exact hcontAt.preimage_mem_nhds (isOpen_ne.mem_nhds hne₀)
  rcases mem_nhds_iff.mp hV with ⟨V, hVsub, hVopen, hVx₀⟩
  let U : Set M := V ∩ (extChartAt I x₀).source
  have hUopen : IsOpen U := hVopen.inter (isOpen_extChartAt_source x₀)
  refine ⟨U, ?_, hUopen, W, ?_, ?_⟩
  · exact ⟨hVx₀, hmem⟩
  · intro x hx
    have hxV : x ∈ V := hx.1
    have hpx : p x ≠ 0 := hVsub hxV
    exact (hW x hx.2 (by simpa [p] using hpx)).2
  · intro x hx
    have hmd' : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => (⟨x, W x⟩ : TangentBundle I M)) x := by
      rw [Bundle.Trivialization.contMDiffAt_section_iff (e := trivializationAt E (TangentSpace I) x₀)]
      · have hfib : (fun y : M => (trivializationAt E (TangentSpace I) x₀ ⟨y, W y⟩).2) =ᶠ[nhds x]
            (fun y : M => -((fderiv ℝ (fun z : E => f ((extChartAt I x₀).symm z)) (extChartAt I x₀ y))
                (v₀))⁻¹ • (v₀ : E)) := by
          exact Filter.eventuallyEq_of_mem (hUopen.mem_nhds hx) (fun y hy => by
            rw [tangentTrivializationAt_apply I x₀ y hy.2 (W y)]
            exact (hW y hy.2 (by
              have hyV : y ∈ V := hy.1
              have hpy : p y ≠ 0 := hVsub hyV
              simpa [p] using hpy)).1)
        have hc : ContMDiffAt I 𝓘(ℝ, E) ∞
            (fun y : M => -((fderiv ℝ (fun z : E => f ((extChartAt I x₀).symm z)) (extChartAt I x₀ y))
                (v₀))⁻¹ • (v₀ : E)) x := by
          have hxU : x ∈ U := hx
          have hxVx : x ∈ V ∧ x ∈ (chartAt H x₀).source := by
            simpa [U, extChartAt_source (I := I) (x := x₀)] using hxU
          have hxsrc : x ∈ (chartAt H x₀).source := hxVx.2
          have hmemz : extChartAt I x₀ x ∈ (extChartAt I x₀).target :=
            (extChartAt I x₀).map_source hx.2
          have hpart : ContDiffAt ℝ ∞ (fun z : E =>
              (fderiv ℝ (fun w : E => f ((extChartAt I x₀).symm w)) z) (v₀))
              (extChartAt I x₀ x) := by
            have hfd : ContDiffOn ℝ ∞ (fderiv ℝ (fun w : E => f ((extChartAt I x₀).symm w)))
                (extChartAt I x₀).target :=
              ((contDiffOn_infty_iff_fderiv_of_isOpen (isOpen_extChartAt_target x₀)).1
                hgOn).2
            have hc' : ContDiffOn ℝ ∞ (fun z : E =>
                (fderiv ℝ (fun w : E => f ((extChartAt I x₀).symm w)) z) (v₀))
                (extChartAt I x₀).target :=
              hfd.clm_apply (contDiffOn_const : ContDiffOn ℝ ∞
                (fun _ : E => (v₀ : E)) (extChartAt I x₀).target)
            exact (hc' (extChartAt I x₀ x) hmemz).contDiffAt ((isOpen_extChartAt_target x₀).mem_nhds hmemz)
          have hne : (fderiv ℝ (fun w : E => f ((extChartAt I x₀).symm w)) (extChartAt I x₀ x))
              (v₀) ≠ 0 := by
            simpa [p] using hVsub hx.1
          have hF : ContDiffAt ℝ ∞ (fun t : ℝ => -t⁻¹ • (v₀ : E)) (p x) := by
            have hinv : ContDiffAt ℝ ∞ (fun t : ℝ => t⁻¹) (p x) := by
              exact ContDiffAt.inv (contDiffAt_id : ContDiffAt ℝ ∞ (fun t : ℝ => t) (p x)) (by
                dsimp [p]
                exact hne)
            have hlin : (fun c : ℝ => c • (v₀ : E)) =
                ((1 : ℝ →L[ℝ] ℝ).smulRight (v₀ : E) : ℝ →L[ℝ] E) := by
              funext c
              simp [ContinuousLinearMap.smulRight_apply]
            have hsmul : ContDiffAt ℝ ∞ (fun c : ℝ => c • (v₀ : E)) (-(p x)⁻¹) := by
              rw [hlin]
              exact ((1 : ℝ →L[ℝ] ℝ).smulRight (v₀ : E) : ℝ →L[ℝ] E).contDiff.contDiffAt
            exact (ContDiffAt.comp (x := p x) (g := fun c : ℝ => c • (v₀ : E))
              (f := fun t : ℝ => -t⁻¹) (hg := hsmul) (hf := hinv.neg))
          have hcomp' : ContDiffAt ℝ ∞ (fun z : E =>
              -((fderiv ℝ (fun w : E => f ((extChartAt I x₀).symm w)) z) (v₀))⁻¹ •
                (v₀ : E)) (extChartAt I x₀ x) := by
            have hz : (fun z : E =>
                -((fderiv ℝ (fun w : E => f ((extChartAt I x₀).symm w)) z) (v₀))⁻¹ •
                  (v₀ : E)) =
                (fun t : ℝ => -t⁻¹ • (v₀ : E)) ∘
                  (fun z : E => (fderiv ℝ (fun w : E => f ((extChartAt I x₀).symm w)) z)
                    (v₀)) := by
              funext z
              rfl
            rw [hz]
            exact hF.comp (extChartAt I x₀ x) hpart
          have heq : (fun z : E =>
              -((fderiv ℝ (fun w : E => f ((extChartAt I x₀).symm w))
                  (extChartAt I x₀ ((extChartAt I x₀).symm z))) (v₀))⁻¹ •
                (v₀ : E)) =ᶠ[nhds (extChartAt I x₀ x)]
              (fun z : E => -((fderiv ℝ (fun w : E => f ((extChartAt I x₀).symm w)) z)
                  (v₀))⁻¹ • (v₀ : E)) := by
            exact Filter.eventuallyEq_of_mem
              ((isOpen_extChartAt_target x₀).mem_nhds hmemz) (fun z hz => by
                have hz' : (extChartAt I x₀) ((extChartAt I x₀).symm z) = z :=
                  (extChartAt I x₀).right_inv hz
                change -((fderiv ℝ (fun w : E => f ((extChartAt I x₀).symm w))
                    (extChartAt I x₀ ((extChartAt I x₀).symm z))) (v₀))⁻¹ •
                      (v₀ : E) =
                    -((fderiv ℝ (fun w : E => f ((extChartAt I x₀).symm w)) z)
                      (v₀))⁻¹ • (v₀ : E)
                rw [hz'])
          have hcdComposed : ContDiffAt ℝ ∞ ((fun y : M =>
              -((fderiv ℝ (fun z : E => f ((extChartAt I x₀).symm z)) (extChartAt I x₀ y))
                  (v₀))⁻¹ • (v₀ : E)) ∘ (extChartAt I x₀).symm)
              (extChartAt I x₀ x) := by
            exact ContDiffAt.congr_of_eventuallyEq hcomp' heq
          have hmdComposed : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
              ((fun y : M => -((fderiv ℝ (fun z : E => f ((extChartAt I x₀).symm z)) (extChartAt I x₀ y))
                  (v₀))⁻¹ • (v₀ : E)) ∘ (extChartAt I x₀).symm)
              (range I) (extChartAt I x₀ x) := by
            exact (contMDiffWithinAt_iff_contDiffWithinAt.mpr hcdComposed.contDiffWithinAt)
          rw [contMDiffAt_iff_source_of_mem_source (x := x₀) (x' := x) hxsrc]
          exact hmdComposed
        exact ContMDiffAt.congr_of_eventuallyEq hc hfib
      · simpa [U] using hx.2
    exact hmd'.contMDiffWithinAt (s := U)

theorem exists_unitSpeedVectorField_on_compact (I : ModelWithCorners ℝ E H)
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (K : Set M)
    (hcompact : IsCompact K)
    (hregular : ∀ x ∈ K, ¬ IsCriticalPointAt I f x) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => (⟨x, V x⟩ : TangentBundle I M)) ∧
      IsCompact (tsupport V) ∧
      (∀ x ∈ K,
        (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) = -1) ∧
      (∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) ∧
        (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) ≤ 0) := by
  let K : Set M := K
  have hpts : ∀ x : K, ∃ U : Set M, x.1 ∈ U ∧ IsOpen U ∧ ∃ W : (x : M) → TangentSpace I x,
      (∀ y ∈ U, (NormedSpace.fromTangentSpace (f y)) ((mfderiv I 𝓘(ℝ, ℝ) f y) (W y)) = -1) ∧
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => (⟨y, W y⟩ : TangentBundle I M)) U :=
    fun x => exists_open_unitSpeedVectorField_at_noncritical I f hf (hregular x x.2)
  choose U hUmem hUopen W hWdf hWsec using hpts
  have hKclosed : IsClosed K := hcompact.isClosed
  have _ : LocallyCompactSpace H := I.locallyCompactSpace
  have _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  rcases exists_open_between_and_isCompact_closure hcompact isOpen_univ (subset_univ K)
    with ⟨W₀, hW₀open, hKW₀, hW₀cl, hW₀compact⟩
  let U' : K → Set M := fun x => U x ∩ W₀
  have hU'mem : ∀ x : K, x.1 ∈ U' x := fun x => ⟨hUmem x, hKW₀ x.2⟩
  have hU'open : ∀ x : K, IsOpen (U' x) := fun x => (hUopen x).inter hW₀open
  have hcov : K ⊆ ⋃ x : K, U' x := by
    intro y hy
    exact Set.mem_iUnion_of_mem ⟨y, hy⟩ (hU'mem ⟨y, hy⟩)
  rcases SmoothPartitionOfUnity.exists_isSubordinate (I := I) (s := K) (U := U')
    (hs := hKclosed) (ho := hU'open) (hU := hcov) with ⟨ρ, hρsub⟩
  let V : (x : M) → TangentSpace I x := fun y => ∑ᶠ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y)
  have hdfsum : ∀ y : M,
      (NormedSpace.fromTangentSpace (f y)) ((mfderiv I 𝓘(ℝ, ℝ) f y) (V y)) =
        -(∑ᶠ x : K, (ρ x y : ℝ)) := by
    intro y
    let L : TangentSpace I y →L[ℝ] ℝ :=
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f y) : TangentSpace 𝓘(ℝ, ℝ) (f y) →L[ℝ] ℝ).comp
        (mfderiv I 𝓘(ℝ, ℝ) f y)
    have hVdef : (NormedSpace.fromTangentSpace (f y)) ((mfderiv I 𝓘(ℝ, ℝ) f y) (V y)) = L (V y) := by
      simp [L]
    rw [hVdef]
    have hfinSupportρ : Function.HasFiniteSupport (fun x : K => ρ x y) := by
      have hlf : LocallyFinite (fun x : K => {z : M | ρ x z ≠ 0}) := ρ.locallyFinite
      have hlfy := hlf y
      rcases hlfy with ⟨N, hN, hfinN⟩
      have hsub : (Function.support fun x : K => ρ x y) ⊆
          {x : K | ((fun x : K => {z : M | ρ x z ≠ 0}) x ∩ N).Nonempty} := by
        intro x hx
        rw [Function.support] at hx
        exact ⟨y, ⟨hx, mem_of_mem_nhds hN⟩⟩
      exact Set.Finite.subset hfinN hsub
    have hfinSupport : Function.HasFiniteSupport (fun x : K => ρ x y • W x y) := by
      exact Set.Finite.subset hfinSupportρ (by intro x hx; exact fun hρ0 => hx (by simp [hρ0]))
    have hlin : L (V y) = ∑ᶠ x : K, L (ρ x y • W x y) := by
      dsimp [V]
      have hmap := (AddMonoidHom.map_finsum (g := (L : TangentSpace I y →+ ℝ)) (hf := hfinSupport))
      simpa using hmap
    rw [hlin]
    have hterm : ∀ x : K, L (ρ x y • W x y) = ρ x y • L (W x y) := by
      intro x
      rw [map_smul]
    have hrew : (∑ᶠ x : K, L (ρ x y • W x y)) = ∑ᶠ x : K, ρ x y • (-1 : ℝ) := by
      apply finsum_congr
      intro x
      rw [hterm x]
      by_cases hyU : y ∈ U' x
      · have hdf := hWdf x y hyU.1
        have hLval : L (W x y) = -1 := by
          dsimp [L]
          simpa using hdf
        rw [hLval]
      · have hρ0 : ρ x y = 0 := by
          have hts' : y ∉ tsupport (ρ x) := fun h => hyU (hρsub x h)
          have hnot : y ∉ Function.support (ρ x) := fun hs => hts' (subset_closure hs)
          by_contra h
          exact hnot (by simpa [Function.support] using h)
        simp [hρ0]
    rw [hrew]
    have hsum : (∑ᶠ x : K, ρ x y • (-1 : ℝ)) = -(∑ᶠ x : K, (ρ x y : ℝ)) := by
      have hsmul' : (∑ᶠ x : K, ρ x y • (-1 : ℝ)) = (∑ᶠ x : K, ρ x y) • (-1 : ℝ) := by
        exact (finsum_smul' hfinSupportρ (-1 : ℝ)).symm
      rw [hsmul']
      simp
    exact hsum
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · have hsummand : ∀ x : K, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => (⟨y, ρ x y • W x y⟩ : TangentBundle I M)) := by
      intro x
      have hcoerce : (ρ x : M → ℝ) = (ρ x).1 := rfl
      have hρOn : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (ρ x : M → ℝ) (U' x) := by
        have hc' : ContMDiffOn I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ρ x : M → ℝ) Set.univ := by
          simpa [hcoerce] using (ρ x).property.contMDiffOn
        exact (hc'.mono (subset_univ _)).of_le le_rfl
      exact (ContMDiffOn.smul_section_of_tsupport (u := U' x) hρOn (hU'open x) (hρsub x)
        ((hWsec x).mono (by intro y hy; exact hy.1)))
    have hfin : LocallyFinite (fun x : K => {y : M | ρ x y • W x y ≠ 0}) := by
      exact ρ.locallyFinite.subset (fun x => by
        intro y hy
        have hρy : ρ x y ≠ 0 := by
          intro hρ0
          apply hy
          simp [hρ0]
        exact hρy)
    simpa [V] using (ContMDiff.finsum_section_of_locallyFinite hfin hsummand)
  · have hmem : ∀ y, y ∈ Function.support V → y ∈ ⋃ x : K, tsupport (ρ x) := by
      intro y hy
      by_contra hnot
      have hy' : V y ≠ 0 := hy
      apply hy'
      have hall : ∀ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y) = 0 := by
        intro x
        by_contra hx
        apply hnot
        exact Set.mem_iUnion.mpr ⟨x, subset_closure (by
          intro hρ0
          apply hx
          simp [hρ0])⟩
      have hV0 : (∑ᶠ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y)) = 0 :=
        finsum_eq_zero_of_forall_eq_zero hall
      simpa [V] using hV0
    have hsupp₀ : Function.support V ⊆ W₀ := by
      intro y hy
      rcases Set.mem_iUnion.mp (hmem y hy) with ⟨x, hx⟩
      exact (hρsub x hx).2
    have hts : tsupport V ⊆ closure W₀ := closure_mono hsupp₀
    exact hW₀compact.of_isClosed_subset (isClosed_tsupport V) hts
  · intro y hy
    rw [hdfsum y]
    have hs1 : (∑ᶠ x : K, ρ x y) = 1 := ρ.sum_eq_one hy
    rw [hs1]
  · intro y
    rw [hdfsum y]
    have hnonneg : 0 ≤ ∑ᶠ x : K, (ρ x y : ℝ) := finsum_nonneg (fun x => ρ.nonneg x y)
    have hle1 : (∑ᶠ x : K, (ρ x y : ℝ)) ≤ 1 := ρ.sum_le_one y
    constructor <;> linarith

theorem exists_unitSpeedVectorField_on_strip (I : ModelWithCorners ℝ E H)
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (a b : ℝ)
    (hcompact : IsCompact (f ⁻¹' Set.Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => (⟨x, V x⟩ : TangentBundle I M)) ∧
      IsCompact (tsupport V) ∧
      (∀ x ∈ f ⁻¹' Set.Icc a b,
        (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) = -1) ∧
      (∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) ∧
        (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) ≤ 0) := by
  let K : Set M := f ⁻¹' Set.Icc a b
  have hpts : ∀ x : K, ∃ U : Set M, x.1 ∈ U ∧ IsOpen U ∧ ∃ W : (x : M) → TangentSpace I x,
      (∀ y ∈ U, (NormedSpace.fromTangentSpace (f y)) ((mfderiv I 𝓘(ℝ, ℝ) f y) (W y)) = -1) ∧
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => (⟨y, W y⟩ : TangentBundle I M)) U :=
    fun x => exists_open_unitSpeedVectorField_at_noncritical I f hf (hregular x x.2)
  choose U hUmem hUopen W hWdf hWsec using hpts
  have hKclosed : IsClosed K := hcompact.isClosed
  have _ : LocallyCompactSpace H := I.locallyCompactSpace
  have _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  rcases exists_open_between_and_isCompact_closure hcompact isOpen_univ (subset_univ K)
    with ⟨W₀, hW₀open, hKW₀, hW₀cl, hW₀compact⟩
  let U' : K → Set M := fun x => U x ∩ W₀
  have hU'mem : ∀ x : K, x.1 ∈ U' x := fun x => ⟨hUmem x, hKW₀ x.2⟩
  have hU'open : ∀ x : K, IsOpen (U' x) := fun x => (hUopen x).inter hW₀open
  have hcov : K ⊆ ⋃ x : K, U' x := by
    intro y hy
    exact Set.mem_iUnion_of_mem ⟨y, hy⟩ (hU'mem ⟨y, hy⟩)
  rcases SmoothPartitionOfUnity.exists_isSubordinate (I := I) (s := K) (U := U')
    (hs := hKclosed) (ho := hU'open) (hU := hcov) with ⟨ρ, hρsub⟩
  let V : (x : M) → TangentSpace I x := fun y => ∑ᶠ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y)
  have hdfsum : ∀ y : M,
      (NormedSpace.fromTangentSpace (f y)) ((mfderiv I 𝓘(ℝ, ℝ) f y) (V y)) =
        -(∑ᶠ x : K, (ρ x y : ℝ)) := by
    intro y
    let L : TangentSpace I y →L[ℝ] ℝ :=
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f y) : TangentSpace 𝓘(ℝ, ℝ) (f y) →L[ℝ] ℝ).comp
        (mfderiv I 𝓘(ℝ, ℝ) f y)
    have hVdef : (NormedSpace.fromTangentSpace (f y)) ((mfderiv I 𝓘(ℝ, ℝ) f y) (V y)) = L (V y) := by
      simp [L]
    rw [hVdef]
    have hfinSupportρ : Function.HasFiniteSupport (fun x : K => ρ x y) := by
      have hlf : LocallyFinite (fun x : K => {z : M | ρ x z ≠ 0}) := ρ.locallyFinite
      have hlfy := hlf y
      rcases hlfy with ⟨N, hN, hfinN⟩
      have hsub : (Function.support fun x : K => ρ x y) ⊆
          {x : K | ((fun x : K => {z : M | ρ x z ≠ 0}) x ∩ N).Nonempty} := by
        intro x hx
        rw [Function.support] at hx
        exact ⟨y, ⟨hx, mem_of_mem_nhds hN⟩⟩
      exact Set.Finite.subset hfinN hsub
    have hfinSupport : Function.HasFiniteSupport (fun x : K => ρ x y • W x y) := by
      exact Set.Finite.subset hfinSupportρ (by intro x hx; exact fun hρ0 => hx (by simp [hρ0]))
    have hlin : L (V y) = ∑ᶠ x : K, L (ρ x y • W x y) := by
      dsimp [V]
      have hmap := (AddMonoidHom.map_finsum (g := (L : TangentSpace I y →+ ℝ)) (hf := hfinSupport))
      simpa using hmap
    rw [hlin]
    have hterm : ∀ x : K, L (ρ x y • W x y) = ρ x y • L (W x y) := by
      intro x
      rw [map_smul]
    have hrew : (∑ᶠ x : K, L (ρ x y • W x y)) = ∑ᶠ x : K, ρ x y • (-1 : ℝ) := by
      apply finsum_congr
      intro x
      rw [hterm x]
      by_cases hyU : y ∈ U' x
      · have hdf := hWdf x y hyU.1
        have hLval : L (W x y) = -1 := by
          dsimp [L]
          simpa using hdf
        rw [hLval]
      · have hρ0 : ρ x y = 0 := by
          have hts' : y ∉ tsupport (ρ x) := fun h => hyU (hρsub x h)
          have hnot : y ∉ Function.support (ρ x) := fun hs => hts' (subset_closure hs)
          by_contra h
          exact hnot (by simpa [Function.support] using h)
        simp [hρ0]
    rw [hrew]
    have hsum : (∑ᶠ x : K, ρ x y • (-1 : ℝ)) = -(∑ᶠ x : K, (ρ x y : ℝ)) := by
      have hsmul' : (∑ᶠ x : K, ρ x y • (-1 : ℝ)) = (∑ᶠ x : K, ρ x y) • (-1 : ℝ) := by
        exact (finsum_smul' hfinSupportρ (-1 : ℝ)).symm
      rw [hsmul']
      simp
    exact hsum
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · have hsummand : ∀ x : K, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => (⟨y, ρ x y • W x y⟩ : TangentBundle I M)) := by
      intro x
      have hcoerce : (ρ x : M → ℝ) = (ρ x).1 := rfl
      have hρOn : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (ρ x : M → ℝ) (U' x) := by
        have hc' : ContMDiffOn I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ρ x : M → ℝ) Set.univ := by
          simpa [hcoerce] using (ρ x).property.contMDiffOn
        exact (hc'.mono (subset_univ _)).of_le le_rfl
      exact (ContMDiffOn.smul_section_of_tsupport (u := U' x) hρOn (hU'open x) (hρsub x)
        ((hWsec x).mono (by intro y hy; exact hy.1)))
    have hfin : LocallyFinite (fun x : K => {y : M | ρ x y • W x y ≠ 0}) := by
      exact ρ.locallyFinite.subset (fun x => by
        intro y hy
        have hρy : ρ x y ≠ 0 := by
          intro hρ0
          apply hy
          simp [hρ0]
        exact hρy)
    simpa [V] using (ContMDiff.finsum_section_of_locallyFinite hfin hsummand)
  · have hmem : ∀ y, y ∈ Function.support V → y ∈ ⋃ x : K, tsupport (ρ x) := by
      intro y hy
      by_contra hnot
      have hy' : V y ≠ 0 := hy
      apply hy'
      have hall : ∀ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y) = 0 := by
        intro x
        by_contra hx
        apply hnot
        exact Set.mem_iUnion.mpr ⟨x, subset_closure (by
          intro hρ0
          apply hx
          simp [hρ0])⟩
      have hV0 : (∑ᶠ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y)) = 0 :=
        finsum_eq_zero_of_forall_eq_zero hall
      simpa [V] using hV0
    have hsupp₀ : Function.support V ⊆ W₀ := by
      intro y hy
      rcases Set.mem_iUnion.mp (hmem y hy) with ⟨x, hx⟩
      exact (hρsub x hx).2
    have hts : tsupport V ⊆ closure W₀ := closure_mono hsupp₀
    exact hW₀compact.of_isClosed_subset (isClosed_tsupport V) hts
  · intro y hy
    rw [hdfsum y]
    have hs1 : (∑ᶠ x : K, ρ x y) = 1 := ρ.sum_eq_one hy
    rw [hs1]
  · intro y
    rw [hdfsum y]
    have hnonneg : 0 ≤ ∑ᶠ x : K, (ρ x y : ℝ) := finsum_nonneg (fun x => ρ.nonneg x y)
    have hle1 : (∑ᶠ x : K, (ρ x y : ℝ)) ≤ 1 := ρ.sum_le_one y
    constructor <;> linarith

end

end DifferentialGeometry.Topology.Morse
