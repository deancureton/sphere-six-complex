module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineStripMidpoint
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineGlobalEnteringSheets
public import SphereSixComplex.Paper.Topology.PaperEllipticOuterDeckCoordinateNaturality

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex SphereSixComplex.Topology SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.GlobalTorusFamily

public noncomputable def sectionSevenAffineMarkedMidpoint (A : PaperAnalyticData) :
    RegularBase (U := A.modular.modularParameter.toTriangleUniformization) :=
  A.sectionSevenAffineNamedStripLift.lift sectionSevenAffineStripMidpoint

public theorem sectionSevenAffineMarkedMidpoint_projects (A : PaperAnalyticData) :
    A.regularCoordinate A.sectionSevenAffineMarkedMidpoint =
      twicePuncturedComplexBasepoint := by
  change A.regularCoordinate (A.sectionSevenAffineNamedStripLift.lift _) = _
  apply Subtype.ext
  rw [A.sectionSevenAffineNamedStripLift.lift_coordinate]
  rfl

public noncomputable def sectionSevenAffineMarkedLoopDeck (A : PaperAnalyticData)
    (γ : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint) : Delta :=
  letI := A.regularBaseDeckAction
  (A.regularCoordinate_isQuotientCoveringMap.fundamentalGroupToMulOpposite
    ⟨A.sectionSevenAffineMarkedMidpoint, A.sectionSevenAffineMarkedMidpoint_projects⟩
    (Path.Homotopic.Quotient.mk γ)).unop

public theorem exists_sectionSevenAffineMarkedLoopLift (A : PaperAnalyticData)
    (γ : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint) :
    ∃ L : Path A.sectionSevenAffineMarkedMidpoint
      (regularSourceEquiv (A.sectionSevenAffineMarkedLoopDeck γ) A.sectionSevenAffineMarkedMidpoint),
      ∀ t, A.regularCoordinate (L t) = γ t := by
  let _ := A.regularBaseDeckAction
  let hp := A.regularCoordinate_isQuotientCoveringMap
  let e : A.regularCoordinate ⁻¹' {twicePuncturedComplexBasepoint} :=
    ⟨A.sectionSevenAffineMarkedMidpoint, A.sectionSevenAffineMarkedMidpoint_projects⟩
  let d := A.sectionSevenAffineMarkedLoopDeck γ
  let e' := hp.toPermFiber twicePuncturedComplexBasepoint d e
  have hm : hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) e = e' := by
    apply Subtype.ext
    exact (hp.unop_fundamentalGroupToMulOpposite_smul
      (e := e) (γ := Path.Homotopic.Quotient.mk γ)).symm
  let p : C(RegularBase (U := A.modular.modularParameter.toTriangleUniformization),
      RegularCoordinateBase) :=
    ⟨A.regularCoordinate, A.regularCoordinate_isLocalHomeomorph.continuous⟩
  obtain ⟨L, hL⟩ := IsCoveringMap.exists_path_lift_of_monodromy_eq
    (p := p) hp.isCoveringMap γ e e' hm
  exact ⟨L, fun t ↦ congrArg (fun p : Path _ _ ↦ p t) hL⟩

public noncomputable def sectionSevenAffineMarkedLoopLift (A : PaperAnalyticData)
    (γ : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint) :
    Path A.sectionSevenAffineMarkedMidpoint
      (regularSourceEquiv (A.sectionSevenAffineMarkedLoopDeck γ) A.sectionSevenAffineMarkedMidpoint) :=
  (A.exists_sectionSevenAffineMarkedLoopLift γ).choose

public theorem sectionSevenAffineMarkedLoopLift_projects (A : PaperAnalyticData)
    (γ : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint) (t : unitInterval) :
    A.regularCoordinate (A.sectionSevenAffineMarkedLoopLift γ t) = γ t :=
  (A.exists_sectionSevenAffineMarkedLoopLift γ).choose_spec t

public theorem sectionSevenAffineMarkedZeroLift_mem_left (A : PaperAnalyticData)
    (t : unitInterval) :
    A.regularCoordinate
      (A.sectionSevenAffineMarkedLoopLift twicePuncturedClockwiseZeroMeridian t) ∈
        twicePuncturedComplexLeft := by
  rw [A.sectionSevenAffineMarkedLoopLift_projects]
  exact twicePuncturedClockwiseZeroPoint_mem_left t

public theorem sectionSevenAffineMarkedOneLift_mem_right (A : PaperAnalyticData)
    (t : unitInterval) :
    A.regularCoordinate
      (A.sectionSevenAffineMarkedLoopLift twicePuncturedClockwiseOneMeridian t) ∈
        twicePuncturedComplexRight := by
  rw [A.sectionSevenAffineMarkedLoopLift_projects]
  exact twicePuncturedClockwiseOnePoint_mem_right t

end SphereSixComplex.Geometry.PaperAnalyticData
