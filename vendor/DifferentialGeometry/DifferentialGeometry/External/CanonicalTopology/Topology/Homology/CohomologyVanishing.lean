module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainHomotopy
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexBasis
public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.Topology.Homotopy.Contractible

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite

universe u

namespace DifferentialGeometry.Topology

private theorem dual_alternating_exactAt (A : ModuleCat.{u} ℤ) (n : ℕ) (hn : n ≠ 0) :
    ((((linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
      (.up ℕ)).obj (ChainComplex.alternatingConst.obj A).op).ExactAt n := by
  let F := (linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients
  let K := (F.mapHomologicalComplex (.up ℕ)).obj (ChainComplex.alternatingConst.obj A).op
  change K.ExactAt n
  have hin : K.d (n - 1) n = if Even n then 𝟙 (F.obj (op A)) else 0 := by
    change F.map ((if n - 1 + 1 = n then if Even n then 𝟙 A else 0 else 0).op) = _
    rw [ite_eq_left (by omega)]
    split_ifs <;> simp
  have hout : K.d n (n + 1) = if Even (n + 1) then 𝟙 (F.obj (op A)) else 0 := by
    change F.map ((if n + 1 = n + 1 then if Even (n + 1) then 𝟙 A else 0 else 0).op) = _
    rw [ite_eq_left rfl]
    split_ifs <;> simp
  rw [HomologicalComplex.exactAt_iff' K (n - 1) n (n + 1)
    ((ComplexShape.up ℕ).prev_eq' (by change n - 1 + 1 = n; omega))
    ((ComplexShape.up ℕ).next_eq' rfl), ShortComplex.moduleCat_exact_iff]
  intro x hx
  by_cases he : Even n
  · refine ⟨x, ?_⟩
    change K.d (n - 1) n x = x
    rw [hin, ite_eq_left he]
    rfl
  · change K.d n (n + 1) x = 0 at hx
    rw [hout, ite_eq_left (Nat.even_add_one.mpr he)] at hx
    change x = 0 at hx
    refine ⟨0, ?_⟩
    change K.d (n - 1) n 0 = x
    rw [map_zero]
    exact hx.symm

theorem integralSingularCohomology_subsingleton_of_totallyDisconnectedSpace
    (X : Type u) [TopologicalSpace X] [TotallyDisconnectedSpace X]
    (n : ℕ) (hn : n ≠ 0) : Subsingleton (integralSingularCohomology n X) := by
  let F := (linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients
  let e := singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
    (ModuleCat.{u} ℤ) integralSingularCoefficients (TopCat.of X)
  let e' := (F.mapHomologicalComplex (.up ℕ)).mapIso
    ((HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)).mapIso e.op) ≪≫
      integralSingularCochainsDualIso X
  apply ModuleCat.isZero_iff_subsingleton.mp
  exact ((dual_alternating_exactAt _ n hn).of_iso e').isZero_homology

theorem integralSingularCohomology_subsingleton_of_contractibleSpace
    (X : Type u) [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) : Subsingleton (integralSingularCohomology n X) := by
  obtain ⟨p, hp⟩ := id_nullhomotopic X
  let Y := PUnit.{u + 1}
  let _ : Subsingleton (integralSingularCohomology n Y) :=
    integralSingularCohomology_subsingleton_of_totallyDisconnectedSpace Y n hn
  let f : ContinuousMap X Y := ContinuousMap.const X PUnit.unit
  let g : ContinuousMap Y X := ContinuousMap.const Y p
  have hcomp : g.comp f = ContinuousMap.const X p := rfl
  have he := integralSingularCohomologyMap_eq_of_homotopic hp n
  rw [integralSingularCohomologyMap_id] at he
  have hc := integralSingularCohomologyMap_comp n f g
  rw [hcomp, ← he] at hc
  have hz (α : integralSingularCohomology n X) : α = 0 := by
    have ha := LinearMap.congr_fun hc α
    change α = integralSingularCohomologyMap n f (integralSingularCohomologyMap n g α) at ha
    rw [Subsingleton.elim (integralSingularCohomologyMap n g α) 0, map_zero] at ha
    exact ha
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

theorem integralSingularCohomology_subsingleton_of_isEmpty
    (X : Type u) [TopologicalSpace X] [IsEmpty X] (n : ℕ) :
    Subsingleton (integralSingularCohomology n X) := by
  have hs : Subsingleton (integralSingularCochain n X) := by
    refine ⟨fun φ ψ => (integralSingularChainBasis n X).ext fun σ => ?_⟩
    exact isEmptyElim (integralSingularSimplexEquiv n X σ
      (Convexity.StdSimplex.single 0))
  apply ModuleCat.isZero_iff_subsingleton.mp
  apply HomologicalComplex.ExactAt.isZero_homology
  exact ((integralSingularCochains X).sc n).exact_of_isZero_X₂
    (ModuleCat.isZero_iff_subsingleton.mpr hs)

end DifferentialGeometry.Topology

end
