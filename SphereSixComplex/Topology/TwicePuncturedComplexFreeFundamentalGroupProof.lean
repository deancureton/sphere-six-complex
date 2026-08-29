module

public import SphereSixComplex.Topology.TwicePuncturedComplexFundamentalGroupGeneration

/-!
# The canonical free-group presentation map for the twice-punctured plane

The two marked clockwise meridians define a canonical map from the free group on two generators
to the based fundamental group.  The existing based van Kampen generation theorem proves that
this map is surjective.  Injectivity is the remaining relation-free part of the usual van Kampen
calculation.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace
open scoped FundamentalGroupoid

universe u v w

namespace SphereSixComplex.Topology.TwicePuncturedComplex

/-- Inclusion of the intersection of two subspaces into the first subspace. -/
public def intersectionToLeft {X : Type*} [TopologicalSpace X] (U V : Set X) :
    C((U ∩ V : Set X), U) where
  toFun x := ⟨x, x.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Inclusion of the intersection of two subspaces into the second subspace. -/
public def intersectionToRight {X : Type*} [TopologicalSpace X] (U V : Set X) :
    C((U ∩ V : Set X), V) where
  toFun x := ⟨x, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private abbrev ConnectorTarget (_G : Type u) := ULift.{u} PUnit

private instance {_G : Type u} [Group _G] : Category.{u} (ConnectorTarget _G) where
  Hom _ _ := _G
  id _ := 1
  comp f g := g * f
  comp_id := one_mul
  id_comp := mul_one
  assoc f g h := (mul_assoc h g f).symm

private instance {_G : Type u} [Group _G] : Groupoid.{u} (ConnectorTarget _G) where
  inv f := f⁻¹
  inv_comp := fun f ↦ mul_inv_cancel f
  comp_inv := fun f ↦ inv_mul_cancel f

private noncomputable def connectorFunctor
    {C : Type u} [Groupoid.{u} C] (base : C) {G : Type u} [Group G]
    (connector : ∀ x : C, base ⟶ x) (f : End base →* G) :
    C ⥤ ConnectorTarget G where
  obj _ := ULift.up PUnit.unit
  map {x y} p := f (connector x ≫ p ≫ Groupoid.inv (connector y))
  map_id := by
    intro x
    change f (connector x ≫ 𝟙 x ≫ Groupoid.inv (connector x)) = 1
    simp only [Groupoid.inv_eq_inv, Category.id_comp, IsIso.hom_inv_id]
    exact map_one f
  map_comp := by
    intro x y z p q
    change f (connector x ≫ (p ≫ q) ≫ Groupoid.inv (connector z)) =
      f (connector y ≫ q ≫ Groupoid.inv (connector z)) *
        f (connector x ≫ p ≫ Groupoid.inv (connector y))
    rw [← map_mul]
    simp only [Groupoid.inv_eq_inv, End.mul_def, Category.assoc,
      IsIso.inv_hom_id_assoc]

private theorem precomp_connectorFunctor
    {C D : Type u} [Groupoid.{u} C] [Groupoid.{u} D]
    (F : C ⥤ D) (base : C) {G : Type u} [Group G]
    (sourceConnector : ∀ x : C, base ⟶ x)
    (targetConnector : ∀ y : D, F.obj base ⟶ y)
    (hconnector :
      ∀ x, targetConnector (F.obj x) = F.map (sourceConnector x))
    (f : End (F.obj base) →* G) :
    F ⋙ connectorFunctor (F.obj base) targetConnector f =
      connectorFunctor base sourceConnector (f.comp (F.mapEnd base)) := by
  refine CategoryTheory.Functor.ext
    (F := F ⋙ connectorFunctor (F.obj base) targetConnector f)
    (G := connectorFunctor base sourceConnector (f.comp (F.mapEnd base)))
    (fun _ ↦ rfl) (h_map := ?_)
  intro x y p
  dsimp [connectorFunctor]
  rw [hconnector x, hconnector y]
  simp only [Groupoid.inv_eq_inv, Category.id_comp, Category.comp_id]
  rw [← Functor.map_inv]
  rw [← F.map_comp, ← F.map_comp]
  rfl

private noncomputable def rawSetConnector
    {X : Type u} [TopologicalSpace X] {S : Set X}
    (hS : IsPathConnected S) (base x : S) :
    FundamentalGroupoid.mk base ⟶ FundamentalGroupoid.mk x :=
  ⟦(hS.joinedIn base base.2 x x.2).joined_subtype.somePath⟧

private noncomputable def setConnector
    {X : Type u} [TopologicalSpace X] {S : Set X}
    (hS : IsPathConnected S) (base x : S) :
    FundamentalGroupoid.mk base ⟶ FundamentalGroupoid.mk x :=
  Groupoid.inv (rawSetConnector hS base base) ≫ rawSetConnector hS base x

private theorem setConnector_self
    {X : Type u} [TopologicalSpace X] {S : Set X}
    (hS : IsPathConnected S) (base : S) :
    setConnector hS base base = 𝟙 _ := by
  simp [setConnector, Groupoid.inv_eq_inv]

private theorem map_connector_transport
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) {base : C} (connector : ∀ x : C, base ⟶ x)
    {x y : C} (e : x = y) :
    F.map (connector x) ≫ eqToHom (congrArg F.obj e) =
      F.map (connector y) := by
  subst y
  simp

private noncomputable def leftConnector
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (base : (U ∩ V : Set X))
    (hUPath : IsPathConnected U) (hInterPath : IsPathConnected (U ∩ V))
    (z : FundamentalGroupoid U) :
    (FundamentalGroupoid.map (intersectionToLeft U V)).obj
        (FundamentalGroupoid.mk base) ⟶ z := by
  classical
  by_cases hz : (z.as : X) ∈ V
  · let zInter : (U ∩ V : Set X) := ⟨z.as, z.as.2, hz⟩
    let e : (FundamentalGroupoid.map (intersectionToLeft U V)).obj
        (FundamentalGroupoid.mk zInter) = z := by
      cases z
      congr
    exact (FundamentalGroupoid.map (intersectionToLeft U V)).map
      (setConnector hInterPath base zInter) ≫ eqToHom e
  · let ebase : (FundamentalGroupoid.map (intersectionToLeft U V)).obj
        (FundamentalGroupoid.mk base) =
        FundamentalGroupoid.mk (intersectionToLeft U V base) := by
      rfl
    exact eqToHom ebase ≫
      setConnector hUPath (intersectionToLeft U V base) z.as

private noncomputable def rightConnector
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (base : (U ∩ V : Set X))
    (hVPath : IsPathConnected V) (hInterPath : IsPathConnected (U ∩ V))
    (z : FundamentalGroupoid V) :
    (FundamentalGroupoid.map (intersectionToRight U V)).obj
        (FundamentalGroupoid.mk base) ⟶ z := by
  classical
  by_cases hz : (z.as : X) ∈ U
  · let zInter : (U ∩ V : Set X) := ⟨z.as, hz, z.as.2⟩
    let e : (FundamentalGroupoid.map (intersectionToRight U V)).obj
        (FundamentalGroupoid.mk zInter) = z := by
      cases z
      congr
    exact (FundamentalGroupoid.map (intersectionToRight U V)).map
      (setConnector hInterPath base zInter) ≫ eqToHom e
  · let ebase : (FundamentalGroupoid.map (intersectionToRight U V)).obj
        (FundamentalGroupoid.mk base) =
        FundamentalGroupoid.mk (intersectionToRight U V base) := by
      rfl
    exact eqToHom ebase ≫
      setConnector hVPath (intersectionToRight U V base) z.as

private theorem leftConnector_inter
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (base : (U ∩ V : Set X))
    (hUPath : IsPathConnected U) (hInterPath : IsPathConnected (U ∩ V))
    (x : FundamentalGroupoid (U ∩ V : Set X)) :
    leftConnector U V base hUPath hInterPath
        ((FundamentalGroupoid.map (intersectionToLeft U V)).obj x) =
      (FundamentalGroupoid.map (intersectionToLeft U V)).map
        (setConnector hInterPath base x.as) := by
  rcases x with ⟨x⟩
  simp only [leftConnector]
  split
  · rename_i hx
    let xInter : (U ∩ V : Set X) := ⟨x, x.2.1, hx⟩
    have e : xInter = x := Subtype.ext (by rfl)
    let connector : ∀ z : FundamentalGroupoid (U ∩ V : Set X),
        FundamentalGroupoid.mk base ⟶ z :=
      fun z ↦ setConnector hInterPath base z.as
    exact map_connector_transport
      (FundamentalGroupoid.map (intersectionToLeft U V)) connector
      (congrArg FundamentalGroupoid.mk e)
  · rename_i hx
    exact (hx x.2.2).elim

private theorem rightConnector_inter
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (base : (U ∩ V : Set X))
    (hVPath : IsPathConnected V) (hInterPath : IsPathConnected (U ∩ V))
    (x : FundamentalGroupoid (U ∩ V : Set X)) :
    rightConnector U V base hVPath hInterPath
        ((FundamentalGroupoid.map (intersectionToRight U V)).obj x) =
      (FundamentalGroupoid.map (intersectionToRight U V)).map
        (setConnector hInterPath base x.as) := by
  rcases x with ⟨x⟩
  simp only [rightConnector]
  split
  · rename_i hx
    let xInter : (U ∩ V : Set X) := ⟨x, hx, x.2.2⟩
    have e : xInter = x := Subtype.ext (by rfl)
    let connector : ∀ z : FundamentalGroupoid (U ∩ V : Set X),
        FundamentalGroupoid.mk base ⟶ z :=
      fun z ↦ setConnector hInterPath base z.as
    exact map_connector_transport
      (FundamentalGroupoid.map (intersectionToRight U V)) connector
      (congrArg FundamentalGroupoid.mk e)
  · rename_i hx
    exact (hx x.2.1).elim

private theorem restrictedConnectorFunctors_eq
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (base : (U ∩ V : Set X))
    (hUPath : IsPathConnected U) (hVPath : IsPathConnected V)
    (hInterPath : IsPathConnected (U ∩ V))
    {G : Type u} [Group G]
    (fU : FundamentalGroup U (intersectionToLeft U V base) →* G)
    (fV : FundamentalGroup V (intersectionToRight U V base) →* G)
    (hagree :
      fU.comp (FundamentalGroup.map (intersectionToLeft U V) base) =
        fV.comp (FundamentalGroup.map (intersectionToRight U V) base)) :
    FundamentalGroupoid.map (intersectionToLeft U V) ⋙
        connectorFunctor
          ((FundamentalGroupoid.map (intersectionToLeft U V)).obj
            (FundamentalGroupoid.mk base))
          (leftConnector U V base hUPath hInterPath) fU =
      FundamentalGroupoid.map (intersectionToRight U V) ⋙
        connectorFunctor
          ((FundamentalGroupoid.map (intersectionToRight U V)).obj
            (FundamentalGroupoid.mk base))
          (rightConnector U V base hVPath hInterPath) fV := by
  let sourceConnector :
      ∀ x : FundamentalGroupoid (U ∩ V : Set X),
        FundamentalGroupoid.mk base ⟶ x :=
    fun x ↦ setConnector hInterPath base x.as
  calc
    FundamentalGroupoid.map (intersectionToLeft U V) ⋙
        connectorFunctor
          ((FundamentalGroupoid.map (intersectionToLeft U V)).obj
            (FundamentalGroupoid.mk base))
          (leftConnector U V base hUPath hInterPath) fU =
      connectorFunctor (FundamentalGroupoid.mk base) sourceConnector
        (fU.comp ((FundamentalGroupoid.map
          (intersectionToLeft U V)).mapEnd (FundamentalGroupoid.mk base))) :=
      precomp_connectorFunctor
        (FundamentalGroupoid.map (intersectionToLeft U V))
        (FundamentalGroupoid.mk base) sourceConnector
        (leftConnector U V base hUPath hInterPath)
        (leftConnector_inter U V base hUPath hInterPath) fU
    _ = connectorFunctor (FundamentalGroupoid.mk base) sourceConnector
        (fV.comp ((FundamentalGroupoid.map
          (intersectionToRight U V)).mapEnd (FundamentalGroupoid.mk base))) := by
      rw [show
        fU.comp ((FundamentalGroupoid.map
          (intersectionToLeft U V)).mapEnd (FundamentalGroupoid.mk base)) =
        fV.comp ((FundamentalGroupoid.map
          (intersectionToRight U V)).mapEnd (FundamentalGroupoid.mk base)) from
        hagree]
    _ = FundamentalGroupoid.map (intersectionToRight U V) ⋙
        connectorFunctor
          ((FundamentalGroupoid.map (intersectionToRight U V)).obj
            (FundamentalGroupoid.mk base))
          (rightConnector U V base hVPath hInterPath) fV :=
      (precomp_connectorFunctor
        (FundamentalGroupoid.map (intersectionToRight U V))
        (FundamentalGroupoid.mk base) sourceConnector
        (rightConnector U V base hVPath hInterPath)
        (rightConnector_inter U V base hVPath hInterPath) fV).symm

private theorem pairwise_id_single {ι : Type u} (i : ι) :
    (CategoryTheory.Pairwise.Hom.id_single i :
      CategoryTheory.Pairwise.single i ⟶ CategoryTheory.Pairwise.single i) =
        𝟙 (CategoryTheory.Pairwise.single i : CategoryTheory.Pairwise ι) := by
  rfl

private theorem pairwise_id_pair {ι : Type u} (i j : ι) :
    (CategoryTheory.Pairwise.Hom.id_pair i j :
      CategoryTheory.Pairwise.pair i j ⟶ CategoryTheory.Pairwise.pair i j) =
        𝟙 (CategoryTheory.Pairwise.pair i j : CategoryTheory.Pairwise ι) := by
  rfl

private noncomputable def pairwiseCoconeOfCompatible
    {ι : Type v} {C : Type u} [Category.{w} C]
    (D : CategoryTheory.Pairwise ι ⥤ C) (T : C)
    (F : ∀ i : ι, D.obj (.single i) ⟶ T)
    (hF : ∀ i j,
      D.map (.left i j) ≫ F i = D.map (.right i j) ≫ F j) :
    CategoryTheory.Limits.Cocone D where
  pt := T
  ι.app
    | .single i => F i
    | .pair i j => D.map (.left i j) ≫ F i
  ι.naturality := by
    intro a b f
    exact CategoryTheory.Pairwise.Hom.rec
      (fun i => by
        rw [pairwise_id_single i]
        simp)
      (fun i j => by
        rw [pairwise_id_pair i j]
        simp)
      (fun i j => by
        dsimp
        simp)
      (fun i j => by
        dsimp
        simpa using (hF i j).symm)
      f

private def twoOpenCover
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hUOpen : IsOpen U) (hVOpen : IsOpen V) :
    Bool → Opens (TopCat.of X)
  | false => ⟨U, hUOpen⟩
  | true => ⟨V, hVOpen⟩

private def swapIntersection
    {X : Type u} [TopologicalSpace X] (U V : Set X) :
    C((V ∩ U : Set X), (U ∩ V : Set X)) where
  toFun x := ⟨x, x.2.2, x.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private theorem reverse_restrictedConnectorFunctors_eq
    {X : Type u} [TopologicalSpace X] (U V : Set X)
    {T : Type u} [Groupoid.{u} T]
    (FU : FundamentalGroupoid U ⥤ T)
    (FV : FundamentalGroupoid V ⥤ T)
    (h :
      FundamentalGroupoid.map (intersectionToLeft U V) ⋙ FU =
        FundamentalGroupoid.map (intersectionToRight U V) ⋙ FV) :
    FundamentalGroupoid.map (intersectionToLeft V U) ⋙ FV =
      FundamentalGroupoid.map (intersectionToRight V U) ⋙ FU := by
  have h' := congrArg
    (fun K => FundamentalGroupoid.map (swapIntersection U V) ⋙ K) h
  change
    FundamentalGroupoid.map (swapIntersection U V) ⋙
        (FundamentalGroupoid.map (intersectionToLeft U V) ⋙ FU) =
      FundamentalGroupoid.map (swapIntersection U V) ⋙
        (FundamentalGroupoid.map (intersectionToRight U V) ⋙ FV) at h'
  rw [← Functor.assoc, ← FundamentalGroupoid.map_comp,
    ← Functor.assoc, ← FundamentalGroupoid.map_comp] at h'
  have hleft :
      (intersectionToLeft U V).comp (swapIntersection U V) =
        intersectionToRight V U := by
    ext x
    rfl
  have hright :
      (intersectionToRight U V).comp (swapIntersection U V) =
        intersectionToLeft V U := by
    ext x
    rfl
  rw [hleft, hright] at h'
  exact h'.symm

private theorem twoOpenVanKampenCocone_isColimit
    {X : Type u} [TopologicalSpace X]
    (cover : Bool → Opens (TopCat.of X)) :
    Nonempty (CategoryTheory.Limits.IsColimit
      ((πₒ (TopCat.of X)).mapCocone
        (CategoryTheory.Pairwise.cocone cover))) := by
  have hsheaf :=
    FundamentalGroupoid.isSheaf_op_opensToGrpd (X := TopCat.of X)
  rcases hsheaf.isSheafPairwiseIntersections cover with ⟨h⟩
  let e :
      (((πₒ (TopCat.of X)).mapCocone
        (CategoryTheory.Pairwise.cocone cover)).op) ≅
          ((πₒ (TopCat.of X)).op.mapCone
            (CategoryTheory.Pairwise.cocone cover).op) :=
    Functor.mapCoconeOp
      (G := πₒ (TopCat.of X))
      (t := CategoryTheory.Pairwise.cocone cover)
  exact ⟨CategoryTheory.Limits.isColimitOfOp
    ((CategoryTheory.Limits.IsLimit.equivIsoLimit e).symm h)⟩

private noncomputable def twoOpenTargetCocone
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    {T : Type u} [Groupoid.{u} T]
    (FU : FundamentalGroupoid U ⥤ T)
    (FV : FundamentalGroupoid V ⥤ T)
    (h :
      FundamentalGroupoid.map (intersectionToLeft U V) ⋙ FU =
        FundamentalGroupoid.map (intersectionToRight U V) ⋙ FV) :
    CategoryTheory.Limits.Cocone
      (CategoryTheory.Pairwise.diagram
        (twoOpenCover U V hUOpen hVOpen) ⋙ πₒ (TopCat.of X)) := by
  let D := CategoryTheory.Pairwise.diagram
    (twoOpenCover U V hUOpen hVOpen) ⋙ πₒ (TopCat.of X)
  let localFunctor : ∀ i : Bool, D.obj (.single i) ⟶ Grpd.of T := fun i => by
    cases i
    · exact FU
    · exact FV
  apply pairwiseCoconeOfCompatible D (Grpd.of T) localFunctor
  intro i j
  cases i <;> cases j
  · change FundamentalGroupoid.map (intersectionToLeft U U) ⋙ FU =
      FundamentalGroupoid.map (intersectionToRight U U) ⋙ FU
    have e : intersectionToLeft U U = intersectionToRight U U := by
      ext x
      rfl
    rw [e]
  · change FundamentalGroupoid.map (intersectionToLeft U V) ⋙ FU =
      FundamentalGroupoid.map (intersectionToRight U V) ⋙ FV
    exact h
  · change FundamentalGroupoid.map (intersectionToLeft V U) ⋙ FV =
      FundamentalGroupoid.map (intersectionToRight V U) ⋙ FU
    exact reverse_restrictedConnectorFunctors_eq U V FU FV h
  · change FundamentalGroupoid.map (intersectionToLeft V V) ⋙ FV =
      FundamentalGroupoid.map (intersectionToRight V V) ⋙ FV
    have e : intersectionToLeft V V = intersectionToRight V V := by
      ext x
      rfl
    rw [e]

private def toTwoOpenCover
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    C(X, ↑(iSup (twoOpenCover U V hUOpen hVOpen))) where
  toFun x := ⟨x, by
    rw [Opens.mem_iSup]
    by_cases hx : x ∈ U
    · exact ⟨false, hx⟩
    · have hx' : x ∈ U ∪ V := by
        rw [hcover]
        exact Set.mem_univ x
      exact ⟨true, hx'.resolve_left hx⟩⟩
  continuous_toFun := continuous_id.subtype_mk _

private theorem twoOpenCover_left_leg
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    FundamentalGroupoid.map
        (PaperVanKampenFourPieceCover.subsetInclusion U) ⋙
      FundamentalGroupoid.map
        (toTwoOpenCover U V hUOpen hVOpen hcover) =
      ((πₒ (TopCat.of X)).mapCocone
        (CategoryTheory.Pairwise.cocone
          (twoOpenCover U V hUOpen hVOpen))).ι.app (.single false) := by
  rw [← FundamentalGroupoid.map_comp]
  congr 1

private theorem twoOpenCover_right_leg
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    FundamentalGroupoid.map
        (PaperVanKampenFourPieceCover.subsetInclusion V) ⋙
      FundamentalGroupoid.map
        (toTwoOpenCover U V hUOpen hVOpen hcover) =
      ((πₒ (TopCat.of X)).mapCocone
        (CategoryTheory.Pairwise.cocone
          (twoOpenCover U V hUOpen hVOpen))).ι.app (.single true) := by
  rw [← FundamentalGroupoid.map_comp]
  congr 1

/-- The existence part of the based Seifert--van Kampen universal property for an open
two-set cover: compatible homomorphisms from the two local fundamental groups extend to the
ambient fundamental group. -/
public axiom fundamentalGroupOpenUnion_lift
    {X : Type*} [TopologicalSpace X]
    (U V : Set X) (base : X)
    (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (hbaseU : base ∈ U) (hbaseV : base ∈ V)
    (hUPath : IsPathConnected U) (hVPath : IsPathConnected V)
    (hInterPath : IsPathConnected (U ∩ V))
    {G : Type*} [Group G]
    (fU : FundamentalGroup U (⟨base, hbaseU⟩ : U) →* G)
    (fV : FundamentalGroup V (⟨base, hbaseV⟩ : V) →* G)
    (hagree :
      fU.comp (FundamentalGroup.map (intersectionToLeft U V)
        (⟨base, hbaseU, hbaseV⟩ : (U ∩ V : Set X))) =
      fV.comp (FundamentalGroup.map (intersectionToRight U V)
        (⟨base, hbaseU, hbaseV⟩ : (U ∩ V : Set X)))) :
    ∃ f : FundamentalGroup X base →* G,
      f.comp (FundamentalGroup.map
        (PaperVanKampenFourPieceCover.subsetInclusion U)
        (⟨base, hbaseU⟩ : U)) = fU ∧
      f.comp (FundamentalGroup.map
        (PaperVanKampenFourPieceCover.subsetInclusion V)
        (⟨base, hbaseV⟩ : V)) = fV

/-- The based Seifert--van Kampen free-product consequence for two open sets with contractible
overlap, specialized only to the case where both vertex groups have a selected integral
coordinate.  Mathlib currently provides the fundamental-groupoid colimit theorem but not this
based-group extraction. -/
public theorem freeTwoGeneratorLift_injective_of_open_union
    {X : Type*} [TopologicalSpace X]
    (U V : Set X) (base : X)
    (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (hbaseU : base ∈ U) (hbaseV : base ∈ V)
    (hUPath : IsPathConnected U) (hVPath : IsPathConnected V)
    (hInter : ContractibleSpace ↑(U ∩ V : Set X))
    (u : FundamentalGroup U (⟨base, hbaseU⟩ : U))
    (v : FundamentalGroup V (⟨base, hbaseV⟩ : V))
    (hUCoordinate : Function.Bijective (fun n : ℤ ↦ u ^ n))
    (hVCoordinate : Function.Bijective (fun n : ℤ ↦ v ^ n)) :
    Function.Injective
      (FreeGroup.lift fun i : Fin 2 ↦
        if i = 0 then
          FundamentalGroup.map
            (PaperVanKampenFourPieceCover.subsetInclusion U)
            (⟨base, hbaseU⟩ : U) u
        else
          FundamentalGroup.map
            (PaperVanKampenFourPieceCover.subsetInclusion V)
            (⟨base, hbaseV⟩ : V) v) := by
  unfold PaperVanKampenFourPieceCover.subsetInclusion
  let _ : ContractibleSpace ↑(U ∩ V : Set X) := hInter
  let _ : SimplyConnectedSpace ↑(U ∩ V : Set X) :=
    SimplyConnectedSpace.ofContractible _
  have hInterPath : IsPathConnected (U ∩ V) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hUZPow : Function.Bijective
      (zpowersHom (FundamentalGroup U (⟨base, hbaseU⟩ : U)) u) := by
    constructor
    · intro m n hmn
      exact hUCoordinate.1 hmn
    · intro x
      obtain ⟨n, rfl⟩ := hUCoordinate.2 x
      exact ⟨Multiplicative.ofAdd n, rfl⟩
  have hVZPow : Function.Bijective
      (zpowersHom (FundamentalGroup V (⟨base, hbaseV⟩ : V)) v) := by
    constructor
    · intro m n hmn
      exact hVCoordinate.1 hmn
    · intro x
      obtain ⟨n, rfl⟩ := hVCoordinate.2 x
      exact ⟨Multiplicative.ofAdd n, rfl⟩
  let uEquiv : Multiplicative ℤ ≃* FundamentalGroup U (⟨base, hbaseU⟩ : U) :=
    MulEquiv.ofBijective (zpowersHom _ u) hUZPow
  let vEquiv : Multiplicative ℤ ≃* FundamentalGroup V (⟨base, hbaseV⟩ : V) :=
    MulEquiv.ofBijective (zpowersHom _ v) hVZPow
  let fU : FundamentalGroup U (⟨base, hbaseU⟩ : U) →* FreeGroup (Fin 2) :=
    (zpowersHom _ (FreeGroup.of 0)).comp uEquiv.symm.toMonoidHom
  let fV : FundamentalGroup V (⟨base, hbaseV⟩ : V) →* FreeGroup (Fin 2) :=
    (zpowersHom _ (FreeGroup.of 1)).comp vEquiv.symm.toMonoidHom
  have hagree :
      fU.comp (FundamentalGroup.map (intersectionToLeft U V)
        (⟨base, hbaseU, hbaseV⟩ : (U ∩ V : Set X))) =
      fV.comp (FundamentalGroup.map (intersectionToRight U V)
        (⟨base, hbaseU, hbaseV⟩ : (U ∩ V : Set X))) := by
    unfold intersectionToLeft intersectionToRight
    apply MonoidHom.ext
    intro x
    rw [show x = 1 from Subsingleton.elim _ _]
    exact (map_one _).trans (map_one _).symm
  obtain ⟨r, hrU, hrV⟩ :=
    fundamentalGroupOpenUnion_lift U V base hUOpen hVOpen hcover hbaseU hbaseV
      hUPath hVPath hInterPath fU fV hagree
  unfold PaperVanKampenFourPieceCover.subsetInclusion at hrU hrV
  let mapU : FundamentalGroup U (⟨base, hbaseU⟩ : U) →* FundamentalGroup X base :=
    FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) (⟨base, hbaseU⟩ : U)
  let mapV : FundamentalGroup V (⟨base, hbaseV⟩ : V) →* FundamentalGroup X base :=
    FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)) (⟨base, hbaseV⟩ : V)
  change r.comp mapU = fU at hrU
  change r.comp mapV = fV at hrV
  let L : FreeGroup (Fin 2) →* FundamentalGroup X base :=
    FreeGroup.lift fun i : Fin 2 ↦ if i = 0 then mapU u else mapV v
  have huEquiv : uEquiv.symm u = Multiplicative.ofAdd 1 := by
    rw [MulEquiv.symm_apply_eq]
    simp [uEquiv]
  have hvEquiv : vEquiv.symm v = Multiplicative.ofAdd 1 := by
    rw [MulEquiv.symm_apply_eq]
    simp [vEquiv]
  have hleft : Function.LeftInverse r L := by
    intro x
    change (r.comp L) x = x
    simpa only [FreeGroup.lift_of_apply] using
      (FreeGroup.lift_unique (f := FreeGroup.of) (r.comp L) (fun i ↦ by
        by_cases hi : i = 0
        · subst i
          simp only [MonoidHom.comp_apply, L, FreeGroup.lift_apply_of, ↓reduceIte]
          rw [show r (mapU u) = fU u by exact DFunLike.congr_fun hrU u]
          simp [fU, huEquiv]
        · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi
          subst i
          simp only [MonoidHom.comp_apply, L, FreeGroup.lift_apply_of, one_ne_zero,
            ↓reduceIte]
          rw [show r (mapV v) = fV v by exact DFunLike.congr_fun hrV v]
          simp [fV, hvEquiv]) (x := x))
  simpa [L, mapU, mapV] using hleft.injective

/-- The canonical map from the free group on two generators to the fundamental group, sending the
first generator to the clockwise meridian about zero and the second to the clockwise meridian
about one. -/
public def markedMeridianHom :
    FreeGroup (Fin 2) →*
      FundamentalGroup TwicePuncturedComplex twicePuncturedComplexBasepoint :=
  FreeGroup.lift fun i ↦ if i = 0 then zeroMeridianClass else oneMeridianClass

@[simp]
public theorem markedMeridianHom_first :
    markedMeridianHom (FreeGroup.of 0) = zeroMeridianClass := by
  simp [markedMeridianHom]

@[simp]
public theorem markedMeridianHom_second :
    markedMeridianHom (FreeGroup.of 1) = oneMeridianClass := by
  simp [markedMeridianHom]

/-- The two-piece based van Kampen generation theorem is exactly surjectivity of the canonical
free-group presentation map. -/
public theorem markedMeridianHom_surjective :
    Function.Surjective markedMeridianHom := by
  unfold markedMeridianHom
  apply FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr
  have hrange :
      Set.range (fun i : Fin 2 ↦ if i = 0 then zeroMeridianClass else oneMeridianClass) =
        {zeroMeridianClass, oneMeridianClass} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  rw [hrange, markedMeridians_generate]

private theorem complexExpClockwiseGenerator_zpow_injective :
    Function.Injective (fun n : ℤ ↦
      (MulOpposite.op
        (Multiplicative.ofAdd (complexExpDeckMultiple (-1))) :
          (Multiplicative ComplexExpDeckGroup)ᵐᵒᵖ) ^ n) := by
  intro m n h
  have h' := congrArg (fun x : (Multiplicative ComplexExpDeckGroup)ᵐᵒᵖ ↦
    (((MulOpposite.unop x).toAdd : ComplexExpDeckGroup) : ℂ).im) h
  simp [complexExpDeckMultiple] at h'
  exact_mod_cast h'

private theorem leftMeridian_zpow_bijective :
    Function.Bijective (fun n : ℤ ↦
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          twicePuncturedClockwiseZeroMeridianInLeft)) ^ n) := by
  constructor
  · intro m n h
    apply complexExpClockwiseGenerator_zpow_injective
    have h' := congrArg twicePuncturedComplexLeftFundamentalGroupEquiv h
    simpa only [map_zpow,
      twicePuncturedComplexLeftFundamentalGroupEquiv_meridian] using h'
  · intro x
    have hx : x ∈ Subgroup.closure
        ({Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridianInLeft} :
          Set (FundamentalGroup twicePuncturedComplexLeft
            twicePuncturedComplexLeftBasepoint)) := by
      rw [leftFundamentalGroup_generated_by_meridian]
      trivial
    rw [Subgroup.mem_closure_singleton] at hx
    exact hx

private theorem rightMeridian_zpow_bijective :
    Function.Bijective (fun n : ℤ ↦
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          twicePuncturedClockwiseOneMeridianInRight)) ^ n) := by
  constructor
  · intro m n h
    apply complexExpClockwiseGenerator_zpow_injective
    have h' := congrArg twicePuncturedComplexRightFundamentalGroupEquiv h
    simpa only [map_zpow,
      twicePuncturedComplexRightFundamentalGroupEquiv_meridian] using h'
  · intro x
    have hx : x ∈ Subgroup.closure
        ({Path.Homotopic.Quotient.mk twicePuncturedClockwiseOneMeridianInRight} :
          Set (FundamentalGroup twicePuncturedComplexRight
            twicePuncturedComplexRightBasepoint)) := by
      rw [rightFundamentalGroup_generated_by_meridian]
      trivial
    rw [Subgroup.mem_closure_singleton] at hx
    exact hx

/-- The canonical presentation by the two actual clockwise meridians is relation-free. -/
public theorem establishedMarkedMeridianHom_injective :
    Function.Injective markedMeridianHom := by
  let hInter : ContractibleSpace
      ↑(twicePuncturedComplexLeft ∩ twicePuncturedComplexRight :
        Set TwicePuncturedComplex) :=
    twicePuncturedComplexOverlap_contractible
  exact freeTwoGeneratorLift_injective_of_open_union
    twicePuncturedComplexLeft twicePuncturedComplexRight
    twicePuncturedComplexBasepoint
    twicePuncturedComplexLeft_isOpen twicePuncturedComplexRight_isOpen
    twicePuncturedComplexLeft_union_right
    twicePuncturedComplexBasepoint_mem_left
    twicePuncturedComplexBasepoint_mem_right
    left_isPathConnected right_isPathConnected hInter
    (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridianInLeft))
    (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk twicePuncturedClockwiseOneMeridianInRight))
    leftMeridian_zpow_bijective rightMeridian_zpow_bijective

/-- Once injectivity of the canonical presentation map is supplied, the generator-preserving
fundamental-group equivalence is immediate. -/
public noncomputable def markedMeridianMulEquiv
    (hinj : Function.Injective markedMeridianHom) :
    FreeGroup (Fin 2) ≃*
      FundamentalGroup TwicePuncturedComplex twicePuncturedComplexBasepoint :=
  MulEquiv.ofBijective markedMeridianHom ⟨hinj, markedMeridianHom_surjective⟩

end TwicePuncturedComplex
end Topology
end SphereSixComplex

end

end
