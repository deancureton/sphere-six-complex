module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineGlobalEnteringSheets

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex SphereSixComplex.Topology SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.GlobalTorusFamily

public noncomputable def affineMarkedMidpoint (A : PaperAnalyticData) :
    RegularBase (U := A.modular.modularParameter.toTriangleUniformization) :=
  A.affineNamedStripLift.lift affineStripMidpoint

public theorem affineMarkedMidpoint_projects (A : PaperAnalyticData) :
    A.regularCoordinate A.affineMarkedMidpoint =
      twicePuncturedComplexBasepoint := by
  change A.regularCoordinate (A.affineNamedStripLift.lift _) = _
  apply Subtype.ext
  rw [A.affineNamedStripLift.lift_coordinate]
  rfl

public noncomputable def affineMarkedLoopDeck (A : PaperAnalyticData)
    (γ : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint) : Delta :=
  letI := A.regularBaseDeckAction
  (A.regularCoordinate_isQuotientCoveringMap.fundamentalGroupToMulOpposite
    ⟨A.affineMarkedMidpoint, A.affineMarkedMidpoint_projects⟩
    (Path.Homotopic.Quotient.mk γ)).unop

public theorem exists_affineMarkedLoopLift (A : PaperAnalyticData)
    (γ : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint) :
    ∃ L : Path A.affineMarkedMidpoint
      (regularSourceEquiv (A.affineMarkedLoopDeck γ) A.affineMarkedMidpoint),
      ∀ t, A.regularCoordinate (L t) = γ t := by
  let _ := A.regularBaseDeckAction
  let hp := A.regularCoordinate_isQuotientCoveringMap
  let e : A.regularCoordinate ⁻¹' {twicePuncturedComplexBasepoint} :=
    ⟨A.affineMarkedMidpoint, A.affineMarkedMidpoint_projects⟩
  let d := A.affineMarkedLoopDeck γ
  let e' := hp.toPermFiber twicePuncturedComplexBasepoint d e
  have hm : hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) e = e' := by
    apply Subtype.ext
    exact (hp.unop_fundamentalGroupToMulOpposite_smul
      (e := e) (γ := Path.Homotopic.Quotient.mk γ)).symm
  let p : C(RegularBase (U := A.modular.modularParameter.toTriangleUniformization),
      regularCoordinateBase) :=
    ⟨A.regularCoordinate, A.regularCoordinate_isLocalHomeomorph.continuous⟩
  obtain ⟨L, hL⟩ := IsCoveringMap.exists_path_lift_of_monodromy_eq
    (p := p) hp.isCoveringMap γ e e' hm
  exact ⟨L, fun t ↦ congrArg (fun p : Path _ _ ↦ p t) hL⟩

public noncomputable def affineMarkedLoopLift (A : PaperAnalyticData)
    (γ : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint) :
    Path A.affineMarkedMidpoint
      (regularSourceEquiv (A.affineMarkedLoopDeck γ) A.affineMarkedMidpoint) :=
  (A.exists_affineMarkedLoopLift γ).choose

public theorem affineMarkedLoopLift_projects (A : PaperAnalyticData)
    (γ : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint) (t : unitInterval) :
    A.regularCoordinate (A.affineMarkedLoopLift γ t) = γ t :=
  (A.exists_affineMarkedLoopLift γ).choose_spec t

public theorem affineMarkedZeroLift_mem_left (A : PaperAnalyticData)
    (t : unitInterval) :
    A.regularCoordinate
      (A.affineMarkedLoopLift twicePuncturedClockwiseZeroMeridian t) ∈
        twicePuncturedComplexLeft := by
  rw [A.affineMarkedLoopLift_projects]
  exact twicePuncturedClockwiseZeroPoint_mem_left t

public theorem affineMarkedOneLift_mem_right (A : PaperAnalyticData)
    (t : unitInterval) :
    A.regularCoordinate
      (A.affineMarkedLoopLift twicePuncturedClockwiseOneMeridian t) ∈
        twicePuncturedComplexRight := by
  rw [A.affineMarkedLoopLift_projects]
  exact twicePuncturedClockwiseOnePoint_mem_right t

end SphereSixComplex.Geometry.PaperAnalyticData
