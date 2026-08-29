module

public import SphereSixComplex.Topology.EstablishedAffineVanKampen
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Mapping-torus fundamental-group relations

The cylinder homotopy proves the conjugation relation in the mapping-torus fundamental group.
The remaining universal-property fields in `establishedMappingTorusFundamentalGroupUP` require
identifying the van Kampen groupoid colimit for the disconnected overlap with an HNN extension.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped ContinuousMap

namespace SphereSixComplex

private theorem conjugate_of_groupoid_naturality
    {X : Type*} [TopologicalSpace X] {x y : X}
    (A : FundamentalGroup X x) (B : FundamentalGroup X y)
    (E : Path.Homotopic.Quotient x y) (D : Path.Homotopic.Quotient y x)
    (h : A ≫ E = E ≫ B) :
    let M : FundamentalGroup X x := E ≫ D
    M * A * M⁻¹ = (Groupoid.inv D ≫ (B ≫ D) : FundamentalGroup X x) := by
  dsimp
  change Groupoid.inv (E ≫ D) ≫ (A ≫ (E ≫ D)) =
    Groupoid.inv D ≫ (B ≫ D)
  rw [Groupoid.inv_eq_inv, IsIso.inv_comp]
  rw [← Groupoid.inv_eq_inv, ← Groupoid.inv_eq_inv]
  simp only [Category.assoc]
  rw [← Category.assoc A E, h]
  simp

/-- The mapping-torus cylinder is a homotopy from the fiber inclusion to its monodromy twist. -/
public def circleMappingTorusCylinderHomotopy {F : Type} [TopologicalSpace F]
    (phi : F ≃ₜ F) :
    ContinuousMap.Homotopy
      (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi))
      ((finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)).comp
        ⟨phi, phi.continuous⟩) where
  toFun p :=
    Quotient.mk (finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ phi))
      ((), (p.1, p.2))
  continuous_toFun := continuous_quot_mk.comp
    (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))
  map_zero_left y := rfl
  map_one_left y := by
    apply Quotient.sound
    apply Relation.EqvGen.rel
    exact Or.inr (Or.inr ⟨by simp, by simp, rfl⟩)

/-- Naturality along the mapping-torus cylinder. -/
public theorem circleMappingTorusFiberHom_trans_edge
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F)
    (a : FundamentalGroup F x) :
    (circleMappingTorusFiberHom phi x a).trans
        (Path.Homotopic.Quotient.mk (circleMappingTorusEdgePath phi x)) =
      (Path.Homotopic.Quotient.mk (circleMappingTorusEdgePath phi x)).trans
        (FundamentalGroup.map
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)) (phi x)
          (FundamentalGroup.map ⟨phi, phi.continuous⟩ x a)) := by
  have h := (FundamentalGroupoidFunctor.homotopicMapsNatIso
    (circleMappingTorusCylinderHomotopy phi)).naturality a
  have hmap1 :
      (FundamentalGroupoid.map
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi))).map a =
        circleMappingTorusFiberHom phi x a := rfl
  have hedge :
      (FundamentalGroupoidFunctor.homotopicMapsNatIso
        (circleMappingTorusCylinderHomotopy phi)).app (FundamentalGroupoid.mk x) =
        Path.Homotopic.Quotient.mk (circleMappingTorusEdgePath phi x) := rfl
  have hmap2 :
      (FundamentalGroupoid.map
        ((finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)).comp
          ⟨phi, phi.continuous⟩)).map a =
        FundamentalGroup.map
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)) (phi x)
          (FundamentalGroup.map ⟨phi, phi.continuous⟩ x a) := by
    induction a using Quotient.ind
    rfl
  rw [hmap1, hedge, hmap2] at h
  exact h

private theorem circleMappingTorusFiberHom_monodromy
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F)
    (delta : Path (phi x) x) (a : FundamentalGroup F x) :
    circleMappingTorusFiberHom phi x (mappingTorusMonodromyHom phi x delta a) =
      (Path.Homotopic.Quotient.mk
        (delta.map (finiteBouquetMappingTorusFiberInclusion
          (fun _ : Unit ↦ phi)).continuous)).symm.trans
        ((FundamentalGroup.map
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)) (phi x)
          (FundamentalGroup.map ⟨phi, phi.continuous⟩ x a)).trans
        (Path.Homotopic.Quotient.mk
          (delta.map (finiteBouquetMappingTorusFiberInclusion
            (fun _ : Unit ↦ phi)).continuous))) := by
  have hmono : mappingTorusMonodromyHom phi x delta a =
      (Path.Homotopic.Quotient.mk delta).symm.trans
        ((FundamentalGroup.map ⟨phi, phi.continuous⟩ x a).trans
          (Path.Homotopic.Quotient.mk delta)) := rfl
  rw [hmono]
  change
    ((Path.Homotopic.Quotient.mk delta).symm.trans
      ((FundamentalGroup.map ⟨phi, phi.continuous⟩ x a).trans
        (Path.Homotopic.Quotient.mk delta))).map
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)) = _
  change (FundamentalGroupoid.map
      (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi))).map
      (Groupoid.inv (Path.Homotopic.Quotient.mk delta) ≫
        ((FundamentalGroup.map ⟨phi, phi.continuous⟩ x a) ≫
          Path.Homotopic.Quotient.mk delta)) =
    Groupoid.inv ((FundamentalGroupoid.map
      (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi))).map
        (Path.Homotopic.Quotient.mk delta)) ≫
      ((FundamentalGroupoid.map
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi))).map
          (FundamentalGroup.map ⟨phi, phi.continuous⟩ x a) ≫
        (FundamentalGroupoid.map
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi))).map
            (Path.Homotopic.Quotient.mk delta))
  rw [Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, Functor.map_comp,
    Functor.map_comp, Functor.map_inv]

/-- The geometric meridian conjugates fiber loops by mapping-torus monodromy. -/
public theorem circleMappingTorus_conjugate
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F)
    (delta : Path (phi x) x) (a : FundamentalGroup F x) :
    circleMappingTorusMeridian phi x delta * circleMappingTorusFiberHom phi x a *
        (circleMappingTorusMeridian phi x delta)⁻¹ =
      circleMappingTorusFiberHom phi x (mappingTorusMonodromyHom phi x delta a) := by
  let E : Path.Homotopic.Quotient
      (circleMappingTorusBase phi x) (circleMappingTorusBase phi (phi x)) :=
    Path.Homotopic.Quotient.mk (circleMappingTorusEdgePath phi x)
  let D : Path.Homotopic.Quotient
      (circleMappingTorusBase phi (phi x)) (circleMappingTorusBase phi x) :=
    Path.Homotopic.Quotient.mk
      (delta.map (finiteBouquetMappingTorusFiberInclusion
        (fun _ : Unit ↦ phi)).continuous)
  let A : FundamentalGroup (CircleMappingTorus phi) (circleMappingTorusBase phi x) :=
    circleMappingTorusFiberHom phi x a
  let B : FundamentalGroup (CircleMappingTorus phi) (circleMappingTorusBase phi (phi x)) :=
    FundamentalGroup.map
      (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)) (phi x)
      (FundamentalGroup.map ⟨phi, phi.continuous⟩ x a)
  have hedge : A ≫ E = E ≫ B :=
    circleMappingTorusFiberHom_trans_edge phi x a
  have hmeridian : circleMappingTorusMeridian phi x delta = E ≫ D := rfl
  have hmonodromy :
      circleMappingTorusFiberHom phi x (mappingTorusMonodromyHom phi x delta a) =
        Groupoid.inv D ≫ (B ≫ D) :=
    circleMappingTorusFiberHom_monodromy phi x delta a
  rw [hmeridian, hmonodromy]
  exact conjugate_of_groupoid_naturality A B E D hedge

end SphereSixComplex
