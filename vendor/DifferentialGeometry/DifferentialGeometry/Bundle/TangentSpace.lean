module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

@[expose] public section

namespace DifferentialGeometry

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def tangentSpaceModelContinuousLinearEquiv (x : M) : TangentSpace I x ≃L[𝕜] E := by
  unfold TangentSpace
  exact ContinuousLinearEquiv.refl 𝕜 E

theorem tangentSpaceModelContinuousLinearEquiv_apply (x : M)
    (v : TangentSpace I x) : tangentSpaceModelContinuousLinearEquiv (I := I) x v = v := by
  rfl

theorem tangentSpaceModelContinuousLinearEquiv_symm_apply (x : M) (v : E) :
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v = v := by
  rfl

noncomputable def tangentLinearMapToModel
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} (A : TangentSpace I x →L[𝕜] TangentSpace I' y) : E →L[𝕜] E' :=
  (tangentSpaceModelContinuousLinearEquiv (I := I') y).toContinuousLinearMap.comp
    (A.comp (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.toContinuousLinearMap)

theorem tangentLinearMapToModel_apply
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} (A : TangentSpace I x →L[𝕜] TangentSpace I' y) (v : E) :
    tangentLinearMapToModel A v =
      tangentSpaceModelContinuousLinearEquiv (I := I') y
        (A ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v)) := by
  rfl

theorem tangentLinearMapToModel_comp
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
    {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
    {x : M} {y : M'} {z : M''}
    (A : TangentSpace I x →L[𝕜] TangentSpace I' y)
    (B : TangentSpace I'' z →L[𝕜] TangentSpace I x) :
    tangentLinearMapToModel (A.comp B) =
      (tangentLinearMapToModel A).comp (tangentLinearMapToModel B) := by
  ext v
  rfl

theorem tangentLinearMapToModel_injective
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} :
    Function.Injective
      (tangentLinearMapToModel (I := I) (I' := I') (x := x) (y := y)) := by
  intro A B h
  apply ContinuousLinearMap.ext
  intro v
  apply (tangentSpaceModelContinuousLinearEquiv (I := I') y).injective
  have hv := DFunLike.congr_fun h
    (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
  simpa only [tangentLinearMapToModel_apply,
    ContinuousLinearEquiv.symm_apply_apply] using hv

noncomputable def tangentLinearMapOfModel
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} (A : E →L[𝕜] E') :
    TangentSpace I x →L[𝕜] TangentSpace I' y :=
  (tangentSpaceModelContinuousLinearEquiv (I := I') y).symm.toContinuousLinearMap.comp
    (A.comp (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap)

theorem tangentLinearMapToModel_ofModel
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} (A : E →L[𝕜] E') :
    tangentLinearMapToModel (tangentLinearMapOfModel (I := I) (I' := I')
      (x := x) (y := y) A) = A := by
  ext v
  rfl

theorem tangentLinearMapOfModel_toModel
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} (A : TangentSpace I x →L[𝕜] TangentSpace I' y) :
    tangentLinearMapOfModel (I := I) (I' := I') (x := x) (y := y)
      (tangentLinearMapToModel A) = A := by
  apply tangentLinearMapToModel_injective
  rw [tangentLinearMapToModel_ofModel]

theorem ModelWithCorners.hasMFDerivAt_model (I : ModelWithCorners 𝕜 E H) {x : H} :
    HasMFDerivAt I 𝓘(𝕜, E) I x
      (tangentLinearMapOfModel (I := I) (I' := 𝓘(𝕜, E))
        (x := x) (y := I x) (ContinuousLinearMap.id 𝕜 E)) := by
  refine ⟨I.continuousAt, ?_⟩
  exact (hasFDerivWithinAt_id (𝕜 := 𝕜) (I x) _).congr'
    I.rightInvOn (Set.mem_range_self x)

theorem ModelWithCorners.hasMFDerivWithinAt_model
    (I : ModelWithCorners 𝕜 E H) {s : Set H} {x : H} :
    HasMFDerivWithinAt I 𝓘(𝕜, E) I s x
      (tangentLinearMapOfModel (I := I) (I' := 𝓘(𝕜, E))
        (x := x) (y := I x) (ContinuousLinearMap.id 𝕜 E)) :=
  (ModelWithCorners.hasMFDerivAt_model I).hasMFDerivWithinAt

noncomputable def tangentLinearMapCodomainToModel
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'}
    (A : TangentSpace I x →L[𝕜] TangentSpace I' y) :
    TangentSpace I x →L[𝕜] E' :=
  (tangentSpaceModelContinuousLinearEquiv (I := I') y).toContinuousLinearMap.comp A

theorem tangentLinearMapCodomainToModel_apply
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'}
    (A : TangentSpace I x →L[𝕜] TangentSpace I' y) (v : TangentSpace I x) :
    tangentLinearMapCodomainToModel A v =
      tangentSpaceModelContinuousLinearEquiv (I := I') y (A v) := by
  rfl

theorem tangentLinearMapCodomainToModel_injective
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} :
    Function.Injective
      (tangentLinearMapCodomainToModel (I := I) (I' := I') (x := x) (y := y)) := by
  intro A B h
  apply ContinuousLinearMap.ext
  intro v
  apply (tangentSpaceModelContinuousLinearEquiv (I := I') y).injective
  exact DFunLike.congr_fun h v

theorem tangentLinearMapCodomainToModel_zero
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {x : M} {y : M'} :
    tangentLinearMapCodomainToModel
        (0 : TangentSpace I x →L[𝕜] TangentSpace I' y) = 0 := by
  ext v
  rfl

noncomputable def modelLinearMapToTangent
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {A : E →L[𝕜] E'} {x : E} {y : E'} :
    TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E') y :=
  (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E')) y).symm.toContinuousLinearMap.comp
    (A.comp (tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(𝕜, E)) x).toContinuousLinearMap)

theorem tangentLinearMapToModel_modelLinearMapToTangent
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {A : E →L[𝕜] E'} {x : E} {y : E'} :
    tangentLinearMapToModel
        (modelLinearMapToTangent (x := x) (y := y) (A := A)) = A := by
  ext v
  rfl

theorem modelLinearMapToTangent_toSpanSingleton
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {x : 𝕜} {y : E'} (w : E') :
    modelLinearMapToTangent (x := x) (y := y)
        (A := ContinuousLinearMap.toSpanSingleton 𝕜 w) =
      ContinuousLinearMap.smulRight
        (tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(𝕜, 𝕜)) x).toContinuousLinearMap
        ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E')) y).symm w) := by
  rfl

theorem HasFDerivWithinAt.hasMFDerivWithinAt_model
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {f : E → E'} {s : Set E} {x : E} {A : E →L[𝕜] E'}
    (h : HasFDerivWithinAt f A s x) :
    HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x
      (modelLinearMapToTangent (x := x) (y := f x) (A := A)) := by
  have hraw := h.hasMFDerivWithinAt
  refine hraw.congr_mfderiv ?_
  apply tangentLinearMapToModel_injective
  rw [tangentLinearMapToModel_modelLinearMapToTangent]
  ext v
  rfl

theorem HasFDerivAt.hasMFDerivAt_model
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {f : E → E'} {x : E} {A : E →L[𝕜] E'}
    (h : HasFDerivAt f A x) :
    HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x
      (modelLinearMapToTangent (x := x) (y := f x) (A := A)) :=
  hasMFDerivWithinAt_univ.mp
    (HasFDerivWithinAt.hasMFDerivWithinAt_model
      (s := Set.univ) h.hasFDerivWithinAt)

theorem HasMFDerivWithinAt.hasFDerivWithinAt_model
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {f : E → E'} {s : Set E} {x : E}
    {A : TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E') (f x)}
    (h : HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x A) :
    HasFDerivWithinAt f (tangentLinearMapToModel A) s x := by
  let : NormedAddCommGroup (TangentSpace 𝓘(𝕜, E) x) :=
    inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace 𝕜 (TangentSpace 𝓘(𝕜, E) x) := {
    norm_smul_le a b := by
      change ‖a • (show E from b)‖ ≤ ‖a‖ * ‖(show E from b)‖
      exact norm_smul_le a (show E from b) }
  let : NormedAddCommGroup (TangentSpace 𝓘(𝕜, E') (f x)) :=
    inferInstanceAs (NormedAddCommGroup E')
  let : NormedSpace 𝕜 (TangentSpace 𝓘(𝕜, E') (f x)) := {
    norm_smul_le a b := by
      change ‖a • (show E' from b)‖ ≤ ‖a‖ * ‖(show E' from b)‖
      exact norm_smul_le a (show E' from b) }
  let eIn := tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E)) x
  let eOut := tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E')) (f x)
  have hraw := h.hasFDerivWithinAt
  have hout := eOut.hasFDerivAt.comp_hasFDerivWithinAt x hraw
  have hin : HasFDerivWithinAt (eIn.symm : E → TangentSpace 𝓘(𝕜, E) x)
      eIn.symm.toContinuousLinearMap s x :=
    eIn.symm.hasFDerivAt.hasFDerivWithinAt
  have hboth := hout.comp x hin (by
    intro y hy
    exact hy)
  convert hboth using 1
  · ext v
    rfl
  · ext v
    rfl

theorem HasMFDerivAt.hasFDerivAt_model
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {f : E → E'} {x : E}
    {A : TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E') (f x)}
    (h : HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x A) :
    HasFDerivAt f (tangentLinearMapToModel A) x :=
  (HasMFDerivWithinAt.hasFDerivWithinAt_model
    (s := Set.univ) h.hasMFDerivWithinAt).hasFDerivAt_of_univ

noncomputable def tangentBilinearFormToModel [hI : IsManifold I 1 M] (x : M)
    (A : TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜) :
    E →L[𝕜] E →L[𝕜] 𝕜 := by
  let _ := hI
  letI : NormedAddCommGroup (TangentSpace I x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace 𝕜 (TangentSpace I x) := ‹NormedSpace 𝕜 E›
  exact (((A.comp (tangentSpaceModelContinuousLinearEquiv
      (I := I) x).symm.toContinuousLinearMap).flip.comp
    (tangentSpaceModelContinuousLinearEquiv
      (I := I) x).symm.toContinuousLinearMap).flip)

theorem tangentBilinearFormToModel_apply [IsManifold I 1 M] (x : M)
    (A : TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜) (v w : E) :
    tangentBilinearFormToModel (I := I) x A v w =
      A ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm w) := by
  rfl

noncomputable def constantModelVectorField (v : E) (x : E) : TangentSpace 𝓘(𝕜, E) x :=
  (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E)) x).symm v

theorem constantModelVectorField_apply (v x : E) :
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E)) x
        (constantModelVectorField v x) = v := by
  exact (tangentSpaceModelContinuousLinearEquiv
    (I := 𝓘(𝕜, E)) x).apply_symm_apply v

theorem mvfderiv_apply_eq_fderivWithin_writtenInExtChartAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : M → F} {x : M} (hf : MDifferentiableAt I 𝓘(𝕜, F) f x)
    (v : TangentSpace I x) :
    mvfderiv I f x v =
      fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, F) x f) (Set.range I)
        (extChartAt I x x) (tangentSpaceModelContinuousLinearEquiv (I := I) x v) := by
  rw [hf.mvfderiv]
  rfl

theorem mvfderivWithin_model_apply_eq_fderivWithin
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {s : Set E} {x : E}
    (v : TangentSpace 𝓘(𝕜, E) x) :
    mvfderivWithin 𝓘(𝕜, E) f s x v =
      fderivWithin 𝕜 f s x
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E)) x v) := by
  rw [mvfderivWithin_eq_fderivWithin]
  rfl

theorem mvfderiv_model_apply_eq_fderiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {x : E} (v : TangentSpace 𝓘(𝕜, E) x) :
    mvfderiv 𝓘(𝕜, E) f x v =
      fderiv 𝕜 f x
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E)) x v) := by
  rw [← mvfderivWithin_univ, mvfderivWithin_model_apply_eq_fderivWithin,
    fderivWithin_univ]

open Bundle Manifold in
open scoped ContDiff in
theorem contMDiff_tangentFiber [IsManifold I 1 M] {n : ℕ∞ω} (p : M) :
    ContMDiff 𝓘(𝕜, E) I.tangent n (fun v : E => (⟨p, v⟩ : TangentBundle I M)) := by
  intro v
  rw [contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_const, ?_⟩
  have hp : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H p
  have heq : (fun w : E => (trivializationAt E (TangentSpace I) p
      (⟨p, w⟩ : TangentBundle I M)).2) =
      (trivializationAt E (TangentSpace I) p).continuousLinearMapAt 𝕜 p := by
    funext w
    exact (congrFun ((trivializationAt E (TangentSpace I) p).coe_linearMapAt_of_mem
      (R := 𝕜) hp) w).symm
  change ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n (fun w : E =>
    (trivializationAt E (TangentSpace I) p (⟨p, w⟩ : TangentBundle I M)).2) v
  rw [heq]
  exact (show E →L[𝕜] E from
    (trivializationAt E (TangentSpace I) p).continuousLinearMapAt 𝕜 p).contMDiff.contMDiffAt

end DifferentialGeometry
