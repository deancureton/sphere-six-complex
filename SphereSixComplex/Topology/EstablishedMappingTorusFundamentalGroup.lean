module

public import SphereSixComplex.Topology.EstablishedAffineVanKampen
public import SphereSixComplex.Topology.CircleMappingTorusOpenCoverHomotopyEquivalences
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.GroupTheory.HNNExtension

/-!
# Mapping-torus fundamental-group relations

The cylinder homotopy proves the conjugation relation in the mapping-torus fundamental group.
The mapping-torus universal property is reduced to the bijectivity of the canonical map from its
HNN extension.  This isolates the missing disconnected-overlap computation as a single precise
input.
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

public theorem homeomorph_fundamentalGroupMap_bijective
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    Function.Bijective (FundamentalGroup.map ⟨phi, phi.continuous⟩ x) := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv phi.toHomotopyEquiv
  exact e.fullyFaithfulFunctor.map_bijective _ _

public noncomputable def mappingTorusMonodromyEquiv
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x) :
    FundamentalGroup F x ≃* FundamentalGroup F x :=
  MulEquiv.ofBijective (mappingTorusMonodromyHom phi x delta)
    ((FundamentalGroup.fundamentalGroupMulEquivOfPath delta).bijective.comp
      (homeomorph_fundamentalGroupMap_bijective phi x))

public def topMulEquiv {G : Type} [Group G] (e : G ≃* G) :
    (⊤ : Subgroup G) ≃* (⊤ : Subgroup G) where
  toFun a := ⟨e a.1, Set.mem_univ _⟩
  invFun a := ⟨e.symm a.1, Set.mem_univ _⟩
  left_inv a := by ext; exact e.symm_apply_apply a.1
  right_inv a := by ext; exact e.apply_symm_apply a.1
  map_mul' a b := by ext; exact e.map_mul a.1 b.1

public abbrev MappingTorusHNN
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x) :=
  HNNExtension (FundamentalGroup F x) ⊤ ⊤
    (topMulEquiv (mappingTorusMonodromyEquiv phi x delta))

public noncomputable def mappingTorusHNNToFundamentalGroup
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x) :
    MappingTorusHNN phi x delta →*
      FundamentalGroup (CircleMappingTorus phi) (circleMappingTorusBase phi x) :=
  HNNExtension.lift (circleMappingTorusFiberHom phi x)
    (circleMappingTorusMeridian phi x delta) (by
      intro a
      calc
        circleMappingTorusMeridian phi x delta * circleMappingTorusFiberHom phi x a.1 =
            (circleMappingTorusMeridian phi x delta * circleMappingTorusFiberHom phi x a.1 *
              (circleMappingTorusMeridian phi x delta)⁻¹) *
                circleMappingTorusMeridian phi x delta := by
              rw [mul_assoc, inv_mul_cancel, mul_one]
        _ = circleMappingTorusFiberHom phi x
              (mappingTorusMonodromyHom phi x delta a.1) *
                circleMappingTorusMeridian phi x delta := by
              rw [circleMappingTorus_conjugate]
        _ = circleMappingTorusFiberHom phi x
              ((topMulEquiv (mappingTorusMonodromyEquiv phi x delta)) a :
                FundamentalGroup F x) * circleMappingTorusMeridian phi x delta := by
              rfl)

public noncomputable def mappingTorusHNNLift
    {F H : Type} [TopologicalSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a, t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    MappingTorusHNN phi x delta →* H :=
  HNNExtension.lift f t (by
    intro a
    calc
      t * f a.1 = (t * f a.1 * t⁻¹) * t := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = f (mappingTorusMonodromyHom phi x delta a.1) * t := by rw [h]
      _ = f ((topMulEquiv (mappingTorusMonodromyEquiv phi x delta)) a :
          FundamentalGroup F x) * t := by
        rfl)

public noncomputable def mappingTorusFundamentalGroupUP_of_bijective
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (hbij : Function.Bijective (mappingTorusHNNToFundamentalGroup phi x delta)) :
    MappingTorusFundamentalGroupUP phi x delta := by
  let e : MappingTorusHNN phi x delta ≃*
      FundamentalGroup (CircleMappingTorus phi) (circleMappingTorusBase phi x) :=
    MulEquiv.ofBijective (mappingTorusHNNToFundamentalGroup phi x delta) hbij
  refine
    { conjugate := circleMappingTorus_conjugate phi x delta
      lift := fun f t h => (mappingTorusHNNLift phi x delta f t h).comp e.symm.toMonoidHom
      lift_fiber := ?_
      lift_meridian := ?_
      hom_ext := ?_ }
  · intro H _ f t h a
    change mappingTorusHNNLift phi x delta f t h
      (e.symm (circleMappingTorusFiberHom phi x a)) = f a
    have he : e (HNNExtension.of a) = circleMappingTorusFiberHom phi x a := by
      change mappingTorusHNNToFundamentalGroup phi x delta (HNNExtension.of a) = _
      simp [mappingTorusHNNToFundamentalGroup]
    rw [← he, e.symm_apply_apply]
    exact HNNExtension.lift_of _ _ _ _
  · intro H _ f t h
    change mappingTorusHNNLift phi x delta f t h
      (e.symm (circleMappingTorusMeridian phi x delta)) = t
    have he : e HNNExtension.t = circleMappingTorusMeridian phi x delta := by
      change mappingTorusHNNToFundamentalGroup phi x delta HNNExtension.t = _
      simp [mappingTorusHNNToFundamentalGroup]
    rw [← he, e.symm_apply_apply]
    exact HNNExtension.lift_t _ _ _
  · intro H _ f g hf ht
    apply MonoidHom.ext
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    have heq : f.comp e.toMonoidHom = g.comp e.toMonoidHom := by
      apply HNNExtension.hom_ext
      · ext a
        exact hf a
      · change f (e HNNExtension.t) = g (e HNNExtension.t)
        change f (mappingTorusHNNToFundamentalGroup phi x delta HNNExtension.t) =
          g (mappingTorusHNNToFundamentalGroup phi x delta HNNExtension.t)
        simpa [mappingTorusHNNToFundamentalGroup] using ht
    exact DFunLike.congr_fun heq w

/-- The HNN comparison is bijective whenever the mapping-torus fundamental group has the
corresponding universal property. -/
public theorem mappingTorusHNNToFundamentalGroup_bijective_of_up
    {F : Type} [TopologicalSpace F]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (P : MappingTorusFundamentalGroupUP phi x delta) :
    Function.Bijective (mappingTorusHNNToFundamentalGroup phi x delta) := by
  let rel : ∀ a : FundamentalGroup F x,
      (HNNExtension.t : MappingTorusHNN phi x delta) *
          HNNExtension.of a * HNNExtension.t⁻¹ =
        HNNExtension.of (mappingTorusMonodromyHom phi x delta a) := by
    intro a
    symm
    exact HNNExtension.equiv_eq_conj
      (φ := topMulEquiv (mappingTorusMonodromyEquiv phi x delta))
      (⟨a, Subgroup.mem_top a⟩ : (⊤ : Subgroup (FundamentalGroup F x)))
  let inv : FundamentalGroup (CircleMappingTorus phi) (circleMappingTorusBase phi x) →*
      MappingTorusHNN phi x delta :=
    P.lift HNNExtension.of HNNExtension.t rel
  have hleft : inv.comp (mappingTorusHNNToFundamentalGroup phi x delta) =
      MonoidHom.id (MappingTorusHNN phi x delta) := by
    apply HNNExtension.hom_ext
    · ext a
      change inv (circleMappingTorusFiberHom phi x a) = HNNExtension.of a
      exact P.lift_fiber HNNExtension.of HNNExtension.t rel a
    · simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      rw [show mappingTorusHNNToFundamentalGroup phi x delta HNNExtension.t =
          circleMappingTorusMeridian phi x delta by
        simp [mappingTorusHNNToFundamentalGroup]]
      exact P.lift_meridian HNNExtension.of HNNExtension.t rel
  have hright : (mappingTorusHNNToFundamentalGroup phi x delta).comp inv =
      MonoidHom.id
        (FundamentalGroup (CircleMappingTorus phi) (circleMappingTorusBase phi x)) := by
    apply P.hom_ext
    · intro a
      change mappingTorusHNNToFundamentalGroup phi x delta
          (inv (circleMappingTorusFiberHom phi x a)) =
        circleMappingTorusFiberHom phi x a
      rw [P.lift_fiber HNNExtension.of HNNExtension.t rel]
      simp [mappingTorusHNNToFundamentalGroup]
    · change mappingTorusHNNToFundamentalGroup phi x delta
          (inv (circleMappingTorusMeridian phi x delta)) =
        circleMappingTorusMeridian phi x delta
      rw [P.lift_meridian HNNExtension.of HNNExtension.t rel]
      simp [mappingTorusHNNToFundamentalGroup]
  constructor
  · intro a b hab
    calc
      a = (inv.comp (mappingTorusHNNToFundamentalGroup phi x delta)) a := by
        rw [hleft]
        rfl
      _ = (inv.comp (mappingTorusHNNToFundamentalGroup phi x delta)) b := congrArg inv hab
      _ = b := by
        rw [hleft]
        rfl
  · intro y
    exact ⟨inv y, DFunLike.congr_fun hright y⟩

/-- The canonical HNN comparison is bijective.  This is the precise disconnected-overlap
computation required beyond Mathlib's fundamental-groupoid van Kampen theorem. -/
public axiom establishedMappingTorusHNNToFundamentalGroup_bijective
    {F : Type} [TopologicalSpace F] [PathConnectedSpace F]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x) :
    Function.Bijective (mappingTorusHNNToFundamentalGroup phi x delta)

/-- The standard HNN-extension presentation of the fundamental group of a mapping torus. -/
public noncomputable def establishedMappingTorusFundamentalGroupUP
    {F : Type} [TopologicalSpace F] [PathConnectedSpace F]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x) :
    MappingTorusFundamentalGroupUP phi x delta :=
  mappingTorusFundamentalGroupUP_of_bijective phi x delta
    (establishedMappingTorusHNNToFundamentalGroup_bijective phi x delta)

end SphereSixComplex
