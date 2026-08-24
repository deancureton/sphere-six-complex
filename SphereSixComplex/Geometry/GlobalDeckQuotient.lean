module

public import SphereSixComplex.Geometry.GlobalDeckSmoothness
public import SphereSixComplex.Geometry.Quotient
import all SphereSixComplex.Geometry.TorusFamily

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

/-- Freeness of the triangle-group action on the source base, stated without installing a global
typeclass instance depending on `U`. -/
public def SourceActionFree : Prop :=
  ∀ g h : Delta, ∀ z : UpperHalfPlane,
    U.sourceAction g • z = U.sourceAction h • z → g = h

/-- Proper discontinuity of the source action on the base, stated directly by the compact-set
criterion. -/
@[expose] public def SourceActionProperlyDiscontinuous : Prop :=
  ∀ {K L : Set UpperHalfPlane}, IsCompact K → IsCompact L →
    Set.Finite {g : Delta |
      (((fun z : UpperHalfPlane ↦ U.sourceAction g • z) '' K) ∩ L).Nonempty}

/-- Base freeness implies freeness of the lifted deck action. -/
public theorem deckAction_isCancelSMul_of_sourceActionFree
    (hfree : SourceActionFree (U := U)) :
    letI := deckAction F
    IsCancelSMul Delta (UpperHalfPlane × ComplexTwoSpace) := by
  let _ := deckAction F
  refine ⟨?_⟩
  intro g h p hgh
  apply hfree g h p.1
  exact congrArg Prod.fst hgh

/-- Base proper discontinuity implies proper discontinuity of the lifted action.  The compact
sets upstairs are projected to compact subsets of the base. -/
public theorem deckAction_properlyDiscontinuous_of_source
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := deckAction F
    ProperlyDiscontinuousSMul Delta (UpperHalfPlane × ComplexTwoSpace) := by
  let _ := deckAction F
  refine ⟨?_⟩
  intro K L hK hL
  have hKbase : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hLbase : IsCompact (Prod.fst '' L) := hL.image continuous_fst
  apply (hproper hKbase hLbase).subset
  intro g hg
  rcases hg with ⟨q, ⟨p, hpK, hpq⟩, hqL⟩
  refine ⟨q.1, ?_, ⟨q, hqL, rfl⟩⟩
  refine ⟨p.1, ⟨p, hpK, rfl⟩, ?_⟩
  change U.sourceAction g • p.1 = q.1
  exact congrArg Prod.fst hpq

/-- Smoothness of all lifted deck maps supplies continuity of the deck action. -/
public theorem deckAction_continuousConstSMul :
    letI := deckAction F
    ContinuousConstSMul Delta (UpperHalfPlane × ComplexTwoSpace) := by
  let _ := deckAction F
  refine ⟨fun g ↦ ?_⟩
  exact (deckMap_contMDiff F g 0).continuous

/-- Under precisely freeness and proper discontinuity of the source action, the lifted orbit
quotient is a complex manifold and its projection is a local complex diffeomorphism. -/
public theorem globalDeckOrbitQuotient_isManifold_and_projection_isLocalDiffeomorph
    (n : WithTop ℕ∞) (hfree : SourceActionFree (U := U))
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := deckAction F
    letI := deckAction_isCancelSMul_of_sourceActionFree F hfree
    letI := deckAction_properlyDiscontinuous_of_source F hproper
    letI := deckAction_continuousConstSMul F
    IsManifold GlobalDeckTotalModel n
        (OrbitQuotient (M := UpperHalfPlane × ComplexTwoSpace) (G := Delta)) ∧
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
        (quotientProjection (M := UpperHalfPlane × ComplexTwoSpace) (G := Delta)) := by
  let _ := deckAction F
  let _ : IsCancelSMul Delta (UpperHalfPlane × ComplexTwoSpace) :=
    deckAction_isCancelSMul_of_sourceActionFree F hfree
  let _ : ProperlyDiscontinuousSMul Delta (UpperHalfPlane × ComplexTwoSpace) :=
    deckAction_properlyDiscontinuous_of_source F hproper
  let _ : ContinuousConstSMul Delta (UpperHalfPlane × ComplexTwoSpace) :=
    deckAction_continuousConstSMul F
  exact orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    GlobalDeckTotalModel n (fun g ↦ deckMap_contMDiff F g n)

/-- A locally biholomorphic varying-torus projection descends smooth lifted deck maps to smooth
deck maps of the torus family.  The required local-diffeomorphism hypothesis is already the
conclusion of `AnalyticTorusFamily.totalSpace_isManifold_and_projection_isLocalDiffeomorph`. -/
public theorem familyDeckMap_contMDiff_of_projection_isLocalDiffeomorph
    (n : WithTop ℕ∞)
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel n (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) (g : Delta) :
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n (familyDeckMap F g) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    let π : UpperHalfPlane × ComplexTwoSpace → TotalSpace (parameterMap F) :=
      projection (parameterMap F)
    let s := (hprojection p).localInverse
    have hs : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel n s (π p) :=
      (hprojection p).localInverse_contMDiffAt
    have hsp : s (π p) = p :=
      (hprojection p).localInverse_left_inv (hprojection p).localInverse_mem_target
    have hdeck : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel n
        (deckMap F g ∘ s) (π p) :=
      (deckMap_contMDiff F g n).contMDiffAt.comp (π p) hs
    have hrhs : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel n
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
