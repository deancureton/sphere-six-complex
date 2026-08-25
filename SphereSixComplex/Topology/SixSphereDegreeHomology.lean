module

public import SphereSixComplex.Topology.OrientedSmoothHomotopySphere
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# Degree from top integral homology

This file constructs the degree laws for self-homotopy equivalences of `S⁶` from an additive
identification `H₆(S⁶; ℤ) ≃ ℤ`.  The only geometric calculation left as input is that the analytic
antipodal map acts by `-1` on the selected generator.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory ContinuousMap

namespace SphereSixComplex

/-- The endomorphism of top integral singular homology induced by a continuous self-map of the
standard six-sphere. -/
public noncomputable def sixSphereTopIntegralHomologyMap
    (f : C(SixSphere, SixSphere)) :
    IntegralSingularHomology 6 SixSphere →+ IntegralSingularHomology 6 SixSphere :=
  (((singularHomologyFunctor AddCommGrpCat 6).obj (AddCommGrpCat.of ℤ)).map
    (TopCat.ofHom f)).hom

/-- Degree computed on a chosen top-homology generator. -/
public noncomputable def sixSphereHomologicalDegree
    (orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ)
    (f : C(SixSphere, SixSphere)) : ℤ :=
  orientation (sixSphereTopIntegralHomologyMap f (orientation.symm 1))

/-- An additive endomorphism of `ℤ` is multiplication by its value at one. -/
public theorem intAddHom_apply_eq_mul_apply_one (f : ℤ →+ ℤ) (z : ℤ) :
    f z = z * f 1 := by
  calc
    f z = f (z • (1 : ℤ)) := by simp
    _ = z • f 1 := f.map_zsmul z 1
    _ = z * f 1 := by simp

/-- Homotopic self-maps have the same top-homology map. -/
public theorem sixSphereTopIntegralHomologyMap_eq_of_homotopic
    {f g : C(SixSphere, SixSphere)} (h : f.Homotopic g) :
    sixSphereTopIntegralHomologyMap f = sixSphereTopIntegralHomologyMap g := by
  let F := (singularHomologyFunctor AddCommGrpCat 6).obj (AddCommGrpCat.of ℤ)
  have hcat : F.map (TopCat.ofHom f) = F.map (TopCat.ofHom g) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      h.some (AddCommGrpCat.of ℤ) 6
  exact congrArg (fun u : F.obj (TopCat.of SixSphere) ⟶
    F.obj (TopCat.of SixSphere) ↦ u.hom) hcat

/-- Homological degree is invariant under homotopy. -/
public theorem sixSphereHomologicalDegree_eq_of_homotopic
    (orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ)
    {f g : C(SixSphere, SixSphere)} (h : f.Homotopic g) :
    sixSphereHomologicalDegree orientation f =
      sixSphereHomologicalDegree orientation g := by
  rw [sixSphereHomologicalDegree, sixSphereHomologicalDegree,
    sixSphereTopIntegralHomologyMap_eq_of_homotopic h]

/-- The identity self-map has degree one. -/
public theorem sixSphereHomologicalDegree_id
    (orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ) :
    sixSphereHomologicalDegree orientation (ContinuousMap.id SixSphere) = 1 := by
  change orientation
    (sixSphereTopIntegralHomologyMap (ContinuousMap.id SixSphere)
      (orientation.symm 1)) = 1
  have hmap : sixSphereTopIntegralHomologyMap (ContinuousMap.id SixSphere) =
      AddMonoidHom.id _ := by
    let F := (singularHomologyFunctor AddCommGrpCat 6).obj (AddCommGrpCat.of ℤ)
    change (F.map (𝟙 (TopCat.of SixSphere))).hom = _
    calc
      (F.map (𝟙 (TopCat.of SixSphere))).hom =
          ((𝟙 (F.obj (TopCat.of SixSphere))) :
            F.obj (TopCat.of SixSphere) ⟶ F.obj (TopCat.of SixSphere)).hom :=
        congrArg (fun u : F.obj (TopCat.of SixSphere) ⟶
          F.obj (TopCat.of SixSphere) ↦ u.hom) (F.map_id _)
      _ = AddMonoidHom.id _ := rfl
  rw [hmap]
  exact orientation.apply_symm_apply 1

/-- Degree is multiplicative under composition. -/
public theorem sixSphereHomologicalDegree_comp
    (orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ)
    (f g : C(SixSphere, SixSphere)) :
    sixSphereHomologicalDegree orientation (g.comp f) =
      sixSphereHomologicalDegree orientation f *
        sixSphereHomologicalDegree orientation g := by
  let H := IntegralSingularHomology 6 SixSphere
  let F := (singularHomologyFunctor AddCommGrpCat 6).obj (AddCommGrpCat.of ℤ)
  let fH : H →+ H := sixSphereTopIntegralHomologyMap f
  let gH : H →+ H := sixSphereTopIntegralHomologyMap g
  let fZ : ℤ →+ ℤ := orientation.toAddMonoidHom.comp
    (fH.comp orientation.symm.toAddMonoidHom)
  let gZ : ℤ →+ ℤ := orientation.toAddMonoidHom.comp
    (gH.comp orientation.symm.toAddMonoidHom)
  have hcomp : sixSphereTopIntegralHomologyMap (g.comp f) = gH.comp fH := by
    apply AddMonoidHom.ext
    intro z
    change (F.map (TopCat.ofHom (g.comp f))).hom z = _
    have hfg : TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g := rfl
    rw [hfg, Functor.map_comp]
    rfl
  have hf (z : ℤ) : orientation (fH (orientation.symm z)) =
      z * sixSphereHomologicalDegree orientation f := by
    change fZ z = z * fZ 1
    exact intAddHom_apply_eq_mul_apply_one fZ z
  have hg (z : ℤ) : orientation (gH (orientation.symm z)) =
      z * sixSphereHomologicalDegree orientation g := by
    change gZ z = z * gZ 1
    exact intAddHom_apply_eq_mul_apply_one gZ z
  rw [sixSphereHomologicalDegree, hcomp]
  have hf1 := hf 1
  have hgdeg := hg (sixSphereHomologicalDegree orientation f)
  rw [one_mul] at hf1
  rw [← hf1, orientation.symm_apply_apply] at hgdeg
  exact hgdeg.trans (congrArg
    (fun z : ℤ => z * sixSphereHomologicalDegree orientation g) hf1)

/-- The remaining input for the degree package: top homology is infinite cyclic and the antipodal
map sends the selected generator to its negative. -/
public structure SixSphereTopHomologyOrientation where
  orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ
  antipodal_degree : sixSphereHomologicalDegree orientation
    OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun = -1

/-- The homological construction supplies all fields of `SixSphereDegreeTheory`. -/
public noncomputable def SixSphereTopHomologyOrientation.toDegreeTheory
    (O : SixSphereTopHomologyOrientation) :
    OrientedMarkedSmoothHomotopySixSphere.SixSphereDegreeTheory where
  degree e := sixSphereHomologicalDegree O.orientation e.toFun
  degree_refl := sixSphereHomologicalDegree_id O.orientation
  degree_trans f g := by
    exact sixSphereHomologicalDegree_comp O.orientation f.toFun g.toFun
  degree_eq_one_or_neg_one f := by
    let a := sixSphereHomologicalDegree O.orientation f.toFun
    let b := sixSphereHomologicalDegree O.orientation f.invFun
    have hab : a * b = 1 := by
      rw [← sixSphereHomologicalDegree_comp]
      exact (sixSphereHomologicalDegree_eq_of_homotopic O.orientation f.left_inv).trans
        (sixSphereHomologicalDegree_id O.orientation)
    exact Int.eq_one_or_neg_one_of_mul_eq_one hab
  degree_antipodal := O.antipodal_degree
  degree_homotopic f g h :=
    sixSphereHomologicalDegree_eq_of_homotopic O.orientation h

end SphereSixComplex
