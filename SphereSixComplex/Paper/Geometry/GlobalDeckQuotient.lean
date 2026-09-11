module

public import SphereSixComplex.Paper.Geometry.GlobalDeckSmoothness
import all SphereSixComplex.Paper.Geometry.TorusFamily

/-!
# The structural quotient bridge for the global deck action

Freeness and proper discontinuity of the lifted action follow from the corresponding properties
on the base by projection.  Together with smoothness of every lifted deck map, these hypotheses
give the orbit quotient its complex-manifold structure and make the quotient projection locally
biholomorphic.
-/

open scoped Manifold

namespace SphereSixComplex.Geometry.GlobalTorusFamily

open Topology SphereSixComplex.TriangleGroup SphereSixComplex.Periods
open SphereSixComplex.Geometry SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily SphereSixComplex.Geometry.TorusFamily

public noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)


/-- Proper discontinuity of the source action on the base, stated directly by the compact-set
criterion. -/
@[expose] public def SourceActionProperlyDiscontinuous : Prop :=
  ∀ {K L : Set UpperHalfPlane}, IsCompact K → IsCompact L →
    Set.Finite {g : Delta |
      (((fun z : UpperHalfPlane ↦ U.sourceAction g • z) '' K) ∩ L).Nonempty}





/-- A locally biholomorphic varying-torus projection descends smooth lifted deck maps to smooth
deck maps of the torus family.  The required local-diffeomorphism hypothesis is already the
conclusion of `AnalyticTorusFamily.totalSpace_isManifold_and_projection_isLocalDiffeomorph`. -/
public theorem familyDeckMap_contMDiff_of_projection_isLocalDiffeomorph
    (n : WithTop ℕ∞)
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold globalDeckTotalModel n (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel n
      (projection (parameterMap F))) (g : Delta) :
    ContMDiff globalDeckTotalModel globalDeckTotalModel n (familyDeckMap F g) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    let π : UpperHalfPlane × ComplexTwoSpace → TotalSpace (parameterMap F) :=
      projection (parameterMap F)
    let s := (hprojection p).localInverse
    have hs : ContMDiffAt globalDeckTotalModel globalDeckTotalModel n s (π p) :=
      (hprojection p).localInverse_contMDiffAt
    have hsp : s (π p) = p :=
      (hprojection p).localInverse_left_inv (hprojection p).localInverse_mem_target
    have hdeck : ContMDiffAt globalDeckTotalModel globalDeckTotalModel n
        (deckMap F g ∘ s) (π p) :=
      (deckMap_contMDiff F g n).contMDiffAt.comp (π p) hs
    have hrhs : ContMDiffAt globalDeckTotalModel globalDeckTotalModel n
        (π ∘ deckMap F g ∘ s) (π p) :=
      (hprojection (deckMap F g p)).contMDiffAt.comp_of_eq hdeck (by simp [hsp])
    have hright := (hprojection p).localInverse_eventuallyEq_right
    have hevent : Filter.EventuallyEq (nhds (π p)) (familyDeckMap F g)
        (π ∘ deckMap F g ∘ s) := by
      filter_upwards [hright] with x hx
      calc
        familyDeckMap F g x = familyDeckMap F g (π (s x)) := congrArg _ hx.symm
        _ = π (deckMap F g (s x)) := familyDeckMap_mk F g (s x)
    exact hrhs.congr_of_eventuallyEq hevent

end

end SphereSixComplex.Geometry.GlobalTorusFamily
