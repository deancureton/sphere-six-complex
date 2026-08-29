module

public import SphereSixComplex.Topology.WangHomologyPresentationProof
public import SphereSixComplex.Topology.EstablishedAffineVanKampen
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.IsColimit

@[expose] public section

open Set ContinuousMap CategoryTheory TopologicalSpace
open scoped FundamentalGroupoid

noncomputable section

namespace SphereSixComplex

open IntegralMayerVietoris

def circleMappingTorusVertexOpen
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    Opens (CircleMappingTorus phi) :=
  ⟨vertexPiece (fun _ : Unit ↦ phi), isOpen_vertexPiece _⟩

def circleMappingTorusEdgeOpen
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    Opens (CircleMappingTorus phi) :=
  ⟨edgePiece (fun _ : Unit ↦ phi), isOpen_edgePiece _⟩

def circleMappingTorusVanKampenCover
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    Set (Opens (CircleMappingTorus phi)) :=
  {U | U ≤ circleMappingTorusVertexOpen phi ∨
    U ≤ circleMappingTorusEdgeOpen phi}

public theorem circleMappingTorusVanKampenCover_covers
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    ∀ y : CircleMappingTorus phi, ∃ U : Opens (CircleMappingTorus phi),
      U ∈ circleMappingTorusVanKampenCover phi ∧ y ∈ U := by
  intro y
  by_cases hy : y ∈ vertexPiece (fun _ : Unit ↦ phi)
  · exact ⟨circleMappingTorusVertexOpen phi, Or.inl le_rfl, hy⟩
  · refine ⟨circleMappingTorusEdgeOpen phi, Or.inr le_rfl, ?_⟩
    have h : y ∈ vertexPiece (fun _ : Unit ↦ phi) ∪
        edgePiece (fun _ : Unit ↦ phi) := by
      rw [vertexPiece_union_edgePiece]
      exact Set.mem_univ y
    exact h.resolve_left hy

public theorem circleMappingTorusVanKampenCover_finiteIntersections
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    ∀ s : Finset (Opens (CircleMappingTorus phi)), s.Nonempty →
      (∀ U ∈ s, U ∈ circleMappingTorusVanKampenCover phi) →
      s.inf (fun U : Opens (CircleMappingTorus phi) => U) ∈
        circleMappingTorusVanKampenCover phi := by
  intro s hs hmem
  obtain ⟨U, hU⟩ := hs
  rcases hmem U hU with hUvertex | hUedge
  · exact Or.inl ((Finset.inf_le hU).trans hUvertex)
  · exact Or.inr ((Finset.inf_le hU).trans hUedge)

def singleObjGaugeFunctor {C : Type*} [Category C] {H : Type*} [Group H]
    (B : C ⥤ SingleObj H) (g : C → H) : C ⥤ SingleObj H where
  obj _ := SingleObj.star H
  map {x y} p := g y * B.map p * (g x)⁻¹
  map_id x := by
    rw [B.map_id]
    change g x * 1 * (g x)⁻¹ = 1
    simp
  map_comp {x y z} p q := by
    change g z * B.map (p ≫ q) * (g x)⁻¹ =
      (g z * B.map q * (g y)⁻¹) * (g y * B.map p * (g x)⁻¹)
    rw [B.map_comp]
    change g z * (B.map q * B.map p) * (g x)⁻¹ =
      (g z * B.map q * (g y)⁻¹) * (g y * B.map p * (g x)⁻¹)
    group

def singleObjGaugeNatIso {C : Type*} [Category C] {H : Type*} [Group H]
    (B : C ⥤ SingleObj H) (g : C → H) :
    B ≅ singleObjGaugeFunctor B g :=
  NatIso.ofComponents
    (fun x => Iso.mk (g x) ((g x)⁻¹) (by
      change (g x)⁻¹ * g x = 1
      simp)
      (by
        change g x * (g x)⁻¹ = 1
        simp))
    (by
      intro x y p
      change g y * B.map p =
        (g y * B.map p * (g x)⁻¹) * g x
      group)

def groupoidSingleObjNatIsoOfBase
    {C : Type*} [Groupoid C] {H : Type*} [Group H]
    (A B : C ⥤ SingleObj H) (b : C)
    (hconn : ∀ y : C, Nonempty (b ⟶ y)) (u : H)
    (hu : ∀ a : b ⟶ b, A.map a ≫ u = u ≫ B.map a) :
    A ≅ B := by
  let q : ∀ y : C, b ⟶ y := fun y => Classical.choice (hconn y)
  let c : C → H := fun y => B.map (q y) * u * (A.map (q y))⁻¹
  refine NatIso.ofComponents (fun y => Iso.mk (c y) ((c y)⁻¹) ?_ ?_) ?_
  · change (c y)⁻¹ * c y = 1
    simp
  · change c y * (c y)⁻¹ = 1
    simp
  · intro y z p
    change c z * A.map p = B.map p * c y
    have h := hu (q y ≫ p ≫ Groupoid.inv (q z))
    change u * A.map (q y ≫ p ≫ Groupoid.inv (q z)) =
      B.map (q y ≫ p ≫ Groupoid.inv (q z)) * u at h
    rw [A.map_comp, A.map_comp, B.map_comp, B.map_comp] at h
    simp only [SingleObj.comp_as_mul] at h
    rw [Groupoid.inv_eq_inv, A.map_inv, B.map_inv] at h
    simp only [SingleObj.inv_as_inv] at h
    dsimp [c]
    calc
      B.map (q z) * u * (A.map (q z))⁻¹ * A.map p =
          B.map (q z) *
            (u * (A.map (q z))⁻¹ * A.map p * A.map (q y)) *
              (A.map (q y))⁻¹ := by group
      _ = B.map (q z) *
            ((B.map (q z))⁻¹ * B.map p * B.map (q y) * u) *
              (A.map (q y))⁻¹ := by
            have h' : u * (A.map (q z))⁻¹ * A.map p * A.map (q y) =
                (B.map (q z))⁻¹ * B.map p * B.map (q y) * u := by
              simpa only [mul_assoc] using h
            exact congrArg
              (fun w : H => B.map (q z) * w * (A.map (q y))⁻¹) h'
      _ = B.map p * (B.map (q y) * u * (A.map (q y))⁻¹) := by group

theorem groupoidSingleObjNatIsoOfBase_app_base
    {C : Type*} [Groupoid C] {H : Type*} [Group H]
    (A B : C ⥤ SingleObj H) (b : C)
    (hconn : ∀ y : C, Nonempty (b ⟶ y)) (u : H)
    (hu : ∀ a : b ⟶ b, A.map a ≫ u = u ≫ B.map a) :
    (groupoidSingleObjNatIsoOfBase A B b hconn u hu).hom.app b = u := by
  let q : ∀ y : C, b ⟶ y := fun y => Classical.choice (hconn y)
  have hq := hu (q b)
  change u * A.map (q b) = B.map (q b) * u at hq
  change B.map (q b) * u * (A.map (q b))⁻¹ = u
  rw [← hq]
  group

def fundamentalGroupoidBasedFunctor
    {X H : Type*} [TopologicalSpace X] [PathConnectedSpace X] [Group H]
    (x : X) (f : FundamentalGroup X x →* H) :
    FundamentalGroupoid X ⥤ SingleObj H where
  obj _ := SingleObj.star H
  map {y z} p :=
    f (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y.as) ≫ p ≫
      Groupoid.inv
        (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x z.as)))
  map_id y := by
    rw [SingleObj.id_as_one]
    have h :
        Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y.as) ≫ 𝟙 y ≫
            Groupoid.inv
              (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y.as)) =
          𝟙 (FundamentalGroupoid.mk x) := by simp
    rw [h]
    exact f.map_one
  map_comp {y z w} p q := by
    rw [SingleObj.comp_as_mul]
    change f (_ ≫ (p ≫ q) ≫ _) = f (_ ≫ q ≫ _) * f (_ ≫ p ≫ _)
    rw [← f.map_mul]
    congr 1
    change _ ≫ (p ≫ q) ≫ _ = (_ ≫ p ≫ _) ≫ (_ ≫ q ≫ _)
    simp

def circleMappingTorusHighGauge
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H) : H :=
  (f (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x (phi x)) ≫
      Path.Homotopic.Quotient.mk delta))⁻¹ * t *
    f (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x))

public theorem fundamentalGroupoidBasedFunctor_high_intertwining
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a))
    (a : FundamentalGroup F x) :
    (fundamentalGroupoidBasedFunctor x f).map a ≫
        circleMappingTorusHighGauge phi x delta f t =
      circleMappingTorusHighGauge phi x delta f t ≫
        (fundamentalGroupoidBasedFunctor x f).map
          ((FundamentalGroupoid.map (phi : C(F, F))).map a) := by
  let p₀ : FundamentalGroup F x :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x)
  let s : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (phi x) :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x (phi x))
  let e : FundamentalGroupoid.mk (phi x) ⟶ FundamentalGroupoid.mk x :=
    Path.Homotopic.Quotient.mk delta
  let d : FundamentalGroup F x := s ≫ e
  let b : FundamentalGroup F (phi x) :=
    FundamentalGroup.map (phi : C(F, F)) x a
  have hedge :
      Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x) ≫ a ≫
          Groupoid.inv
            (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x)) =
        p₀⁻¹ * a * p₀ := by
    rfl
  have hhigh :
      s ≫ b ≫ Groupoid.inv s =
        d⁻¹ * mappingTorusMonodromyHom phi x delta a * d := by
    change s ≫ b ≫ Groupoid.inv s =
      (s ≫ e) ≫ (Groupoid.inv e ≫ b ≫ e) ≫ Groupoid.inv (s ≫ e)
    rw [Groupoid.inv_eq_inv e, Groupoid.inv_eq_inv (s ≫ e), IsIso.inv_comp]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [Groupoid.inv_eq_inv]
  change circleMappingTorusHighGauge phi x delta f t *
      f (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x) ≫ a ≫
        Groupoid.inv
          (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x))) =
    f (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x (phi x)) ≫
        (FundamentalGroupoid.map (phi : C(F, F))).map a ≫
          Groupoid.inv
            (Path.Homotopic.Quotient.mk
              (PathConnectedSpace.somePath x (phi x)))) *
      circleMappingTorusHighGauge phi x delta f t
  change circleMappingTorusHighGauge phi x delta f t *
      f (p₀ ≫ a ≫ Groupoid.inv p₀) =
    f (s ≫ b ≫ Groupoid.inv s) * circleMappingTorusHighGauge phi x delta f t
  rw [hedge, hhigh, map_mul, map_mul, map_mul, map_mul]
  dsimp [circleMappingTorusHighGauge, d, p₀, s, e]
  rw [map_inv, ← h a]
  group
  rw [map_zpow]

def sumInrContinuousMap {X : Type*} [TopologicalSpace X] : C(X, X ⊕ X) :=
  ⟨Sum.inr, continuous_inr⟩

def sumInlContinuousMap {X : Type*} [TopologicalSpace X] : C(X, X ⊕ X) :=
  ⟨Sum.inl, continuous_inl⟩

def sumFoldContinuousMap {X : Type*} [TopologicalSpace X] : C(X ⊕ X, X) :=
  ⟨Sum.elim id id, continuous_id.sumElim continuous_id⟩

public theorem fundamentalGroupoid_map_comp_apply
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x y : X}
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    (FundamentalGroupoid.map g).map ((FundamentalGroupoid.map f).map p) =
      (FundamentalGroupoid.map (g.comp f)).map p := by
  induction p using Quotient.ind with
  | _ p => rfl

public theorem fundamentalGroupoid_sumInr_map_bijective
    {X : Type*} [TopologicalSpace X] (x y : X) :
    Function.Bijective
      ((FundamentalGroupoid.map (sumInrContinuousMap (X := X))).map :
        (FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) →
          (FundamentalGroupoid.mk (Sum.inr x) ⟶
            FundamentalGroupoid.mk (Sum.inr y))) := by
  constructor
  · intro p q hpq
    have h := congrArg
      (fun r => (FundamentalGroupoid.map (sumFoldContinuousMap (X := X))).map r) hpq
    induction p using Quotient.ind with
    | _ p =>
      induction q using Quotient.ind with
      | _ q => exact h
  · intro p
    induction p using Quotient.ind with
    | _ p =>
      have hpconn : IsConnected (Set.range p) :=
        isConnected_range p.continuous
      have hprange : Set.range p ⊆ Set.range (Sum.inr : X → X ⊕ X) := by
        rcases Sum.isConnected_iff.mp hpconn with ⟨s, hs, hrange⟩ | ⟨s, hs, hrange⟩
        · exfalso
          have htarget : Sum.inr y ∈ Set.range p := by
            refine ⟨1, ?_⟩
            simpa [sumInrContinuousMap] using p.target
          rw [hrange] at htarget
          obtain ⟨z, -, hz⟩ := htarget
          cases hz
        · rw [hrange]
          exact Set.image_subset_range _ _
      let q : Path x y :=
        { toFun := fun t => Sum.elim id id (p t)
          continuous_toFun := (sumFoldContinuousMap (X := X)).continuous.comp p.continuous
          source' := by
            simpa [sumInrContinuousMap] using
              congrArg (Sum.elim id id) p.source
          target' := by
            simpa [sumInrContinuousMap] using
              congrArg (Sum.elim id id) p.target }
      refine ⟨Path.Homotopic.Quotient.mk q, ?_⟩
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      obtain ⟨z, hz⟩ := hprange ⟨t, rfl⟩
      change Sum.inr (Sum.elim id id (p t)) = p t
      rw [← hz]
      rfl

public theorem fundamentalGroupoid_sumInl_map_bijective
    {X : Type*} [TopologicalSpace X] (x y : X) :
    Function.Bijective
      ((FundamentalGroupoid.map (sumInlContinuousMap (X := X))).map :
        (FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) →
          (FundamentalGroupoid.mk (Sum.inl x) ⟶
            FundamentalGroupoid.mk (Sum.inl y))) := by
  constructor
  · intro p q hpq
    have h := congrArg
      (fun r => (FundamentalGroupoid.map (sumFoldContinuousMap (X := X))).map r) hpq
    induction p using Quotient.ind with
    | _ p =>
      induction q using Quotient.ind with
      | _ q => exact h
  · intro p
    induction p using Quotient.ind with
    | _ p =>
      have hpconn : IsConnected (Set.range p) :=
        isConnected_range p.continuous
      have hprange : Set.range p ⊆ Set.range (Sum.inl : X → X ⊕ X) := by
        rcases Sum.isConnected_iff.mp hpconn with ⟨s, hs, hrange⟩ | ⟨s, hs, hrange⟩
        · rw [hrange]
          exact Set.image_subset_range _ _
        · exfalso
          have hsource : Sum.inl x ∈ Set.range p := by
            refine ⟨0, ?_⟩
            simpa [sumInlContinuousMap] using p.source
          rw [hrange] at hsource
          obtain ⟨z, -, hz⟩ := hsource
          cases hz
      let q : Path x y :=
        { toFun := fun t => Sum.elim id id (p t)
          continuous_toFun := (sumFoldContinuousMap (X := X)).continuous.comp p.continuous
          source' := by
            simpa [sumInlContinuousMap] using
              congrArg (Sum.elim id id) p.source
          target' := by
            simpa [sumInlContinuousMap] using
              congrArg (Sum.elim id id) p.target }
      refine ⟨Path.Homotopic.Quotient.mk q, ?_⟩
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      obtain ⟨z, hz⟩ := hprange ⟨t, rfl⟩
      change Sum.inl (Sum.elim id id (p t)) = p t
      rw [← hz]
      rfl

private theorem fundamentalGroupoid_sum_inl_inr_false
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y)
    (p : FundamentalGroupoid.mk (Sum.inl x) ⟶ FundamentalGroupoid.mk (Sum.inr y)) :
    False := by
  induction p using Quotient.ind with
  | _ p =>
    have hpconn : IsConnected (Set.range p) := isConnected_range p.continuous
    rcases Sum.isConnected_iff.mp hpconn with ⟨s, hs, hrange⟩ | ⟨s, hs, hrange⟩
    · have htarget : Sum.inr y ∈ Set.range p := by
        refine ⟨1, ?_⟩
        exact p.target
      rw [hrange] at htarget
      obtain ⟨z, -, hz⟩ := htarget
      cases hz
    · have hsource : Sum.inl x ∈ Set.range p := by
        refine ⟨0, ?_⟩
        exact p.source
      rw [hrange] at hsource
      obtain ⟨z, -, hz⟩ := hsource
      cases hz

private theorem fundamentalGroupoid_sum_inr_inl_false
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y)
    (p : FundamentalGroupoid.mk (Sum.inr y) ⟶ FundamentalGroupoid.mk (Sum.inl x)) :
    False := by
  exact fundamentalGroupoid_sum_inl_inr_false x y (Groupoid.inv p)

def fundamentalGroupoidNatIsoSum
    {X H : Type*} [TopologicalSpace X] [Group H]
    (A B : FundamentalGroupoid (X ⊕ X) ⥤ SingleObj H)
    (leftIso : FundamentalGroupoid.map
        (sumInlContinuousMap (X := X)) ⋙ A ≅
      FundamentalGroupoid.map (sumInlContinuousMap (X := X)) ⋙ B)
    (rightIso : FundamentalGroupoid.map
        (sumInrContinuousMap (X := X)) ⋙ A ≅
      FundamentalGroupoid.map (sumInrContinuousMap (X := X)) ⋙ B) :
    A ≅ B :=
  NatIso.ofComponents
    (fun z => match z.as with
      | Sum.inl x => leftIso.app (FundamentalGroupoid.mk x)
      | Sum.inr y => rightIso.app (FundamentalGroupoid.mk y))
    (by
      rintro ⟨x | y⟩ ⟨x' | y'⟩ p
      · obtain ⟨q, rfl⟩ := (fundamentalGroupoid_sumInl_map_bijective x x').2 p
        exact leftIso.hom.naturality q
      · exact (fundamentalGroupoid_sum_inl_inr_false x y' p).elim
      · exact (fundamentalGroupoid_sum_inr_inl_false x' y p).elim
      · obtain ⟨q, rfl⟩ := (fundamentalGroupoid_sumInr_map_bijective y y').2 p
        exact rightIso.hom.naturality q)

def unitProdHomeomorph {X : Type} [TopologicalSpace X] : Unit × X ≃ₜ X where
  toFun p := p.2
  invFun x := ((), x)
  left_inv p := by cases p.1; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_snd
  continuous_invFun := continuous_const.prodMk continuous_id

def disjointOpenUnionHomeomorph
    {X : Type} [TopologicalSpace X] (s t : Set X)
    (hs : IsOpen s) (ht : IsOpen t) (hdisj : Disjoint s t) :
    s ⊕ t ≃ₜ ↥(s ∪ t) := by
  classical
  let e : s ⊕ t ≃ ↥(s ∪ t) := (Equiv.Set.union hdisj).symm
  have hleft : e ∘ Sum.inl = fun x : s => (⟨x, Or.inl x.2⟩ : ↥(s ∪ t)) := by
    funext x
    apply Subtype.ext
    rfl
  have hright : e ∘ Sum.inr = fun x : t => (⟨x, Or.inr x.2⟩ : ↥(s ∪ t)) := by
    funext x
    apply Subtype.ext
    rfl
  exact e.toHomeomorphOfContinuousOpen
    (continuous_sum_dom.mpr ⟨by
      rw [hleft]
      exact continuous_subtype_val.subtype_mk _, by
      rw [hright]
      exact continuous_subtype_val.subtype_mk _⟩)
    (isOpenMap_sum.mpr ⟨by
      change IsOpenMap (e ∘ Sum.inl)
      rw [hleft]
      exact hs.isOpenMap_subtype_val.subtype_mk _, by
      change IsOpenMap (e ∘ Sum.inr)
      rw [hright]
      exact ht.isOpenMap_subtype_val.subtype_mk _⟩)

def homotopySum
    {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    {f₀ f₁ : C(X, X')} {g₀ g₁ : C(Y, Y')}
    (hf : Homotopy f₀ f₁) (hg : Homotopy g₀ g₁) :
    Homotopy
      ⟨Sum.map f₀ g₀, f₀.continuous.sumMap g₀.continuous⟩
      ⟨Sum.map f₁ g₁, f₁.continuous.sumMap g₁.continuous⟩ where
  toFun q := match q.2 with
    | Sum.inl x => Sum.inl (hf (q.1, x))
    | Sum.inr y => Sum.inr (hg (q.1, y))
  continuous_toFun := by
    convert ((continuous_inl.comp hf.continuous).sumElim
      (continuous_inr.comp hg.continuous)).comp
        (Homeomorph.prodSumDistrib).continuous using 1
    funext q
    rcases q with ⟨t, z⟩
    cases z <;> rfl
  map_zero_left z := by
    cases z with
    | inl x => exact congrArg Sum.inl (hf.map_zero_left x)
    | inr y => exact congrArg Sum.inr (hg.map_zero_left y)
  map_one_left z := by
    cases z with
    | inl x => exact congrArg Sum.inl (hf.map_one_left x)
    | inr y => exact congrArg Sum.inr (hg.map_one_left y)

def homotopyEquivSum
    {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (e : HomotopyEquiv X X') (f : HomotopyEquiv Y Y') :
    HomotopyEquiv (X ⊕ Y) (X' ⊕ Y') where
  toFun := ⟨Sum.map e.toFun f.toFun, e.toFun.continuous.sumMap f.toFun.continuous⟩
  invFun := ⟨Sum.map e.invFun f.invFun, e.invFun.continuous.sumMap f.invFun.continuous⟩
  left_inv := by
    rcases e.left_inv with ⟨he⟩
    rcases f.left_inv with ⟨hf⟩
    refine ⟨(homotopySum he hf).cast ?_ ?_⟩
    · ext z
      cases z <;> rfl
    · ext z
      cases z <;> rfl
  right_inv := by
    rcases e.right_inv with ⟨he⟩
    rcases f.right_inv with ⟨hf⟩
    refine ⟨(homotopySum he hf).cast ?_ ?_⟩
    · ext z
      cases z <;> rfl
    · ext z
      cases z <;> rfl

public theorem overlapBand_eq_lowBand_union_highBand :
    overlapBand = lowBand ∪ highBand :=
  Set.Subset.antisymm overlapBand_subset_union
    (Set.union_subset lowBand_subset_overlapBand highBand_subset_overlapBand)

def lowHighOverlapBandHomeomorph :
    lowBand ⊕ highBand ≃ₜ overlapBand :=
  (disjointOpenUnionHomeomorph lowBand highBand
    (isOpen_openBand _ _) (isOpen_openBand _ _) disjoint_lowBand_highBand).trans
      (Homeomorph.setCongr overlapBand_eq_lowBand_union_highBand.symm)

/-- For a circle mapping torus, the edge piece deformation-retracts to its midpoint fibre. -/
public def circleMappingTorusEdgePieceHomotopyEquiv
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    HomotopyEquiv F ↥(edgePiece (fun _ : Unit ↦ phi)) :=
  ((fiberBandProdHomotopyEquiv (F := F) uHalf_mem_edgeOpenBand).trans
    unitProdHomeomorph.symm.toHomotopyEquiv).trans
      (bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand
        (fun _ h ↦ h)).toHomotopyEquiv

@[simp]
public theorem circleMappingTorusEdgePieceHomotopyEquiv_toFun
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    (circleMappingTorusEdgePieceHomotopyEquiv phi).toFun x =
      edgePt (fun _ : Unit ↦ phi) () x :=
  rfl

@[simp]
public theorem circleMappingTorusEdgePieceHomotopyEquiv_invFun_edgeLowPt
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    (circleMappingTorusEdgePieceHomotopyEquiv phi).invFun
        (edgeLowPt (fun _ : Unit ↦ phi) () x) = x :=
  by
    rw [show edgeLowPt (fun _ : Unit ↦ phi) () x =
      bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand (fun _ h ↦ h)
        ((), ⟨uQuarter, uQuarter_mem_edgeBand⟩, x) by rfl]
    change
      (fiberBandProdHomotopyEquiv uHalf_mem_edgeOpenBand).invFun
        (unitProdHomeomorph
          ((bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand (fun _ h ↦ h)).symm
            ((bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand (fun _ h ↦ h))
              ((), ⟨uQuarter, uQuarter_mem_edgeBand⟩, x)))) = x
    rw [Homeomorph.symm_apply_apply]
    rfl

@[simp]
public theorem circleMappingTorusEdgePieceHomotopyEquiv_invFun_edgeHighPt
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    (circleMappingTorusEdgePieceHomotopyEquiv phi).invFun
        (edgeHighPt (fun _ : Unit ↦ phi) () x) = x :=
  by
    rw [show edgeHighPt (fun _ : Unit ↦ phi) () x =
      bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand (fun _ h ↦ h)
        ((), ⟨uThreeQuarters, uThreeQuarters_mem_edgeBand⟩, x) by rfl]
    change
      (fiberBandProdHomotopyEquiv uHalf_mem_edgeOpenBand).invFun
        (unitProdHomeomorph
          ((bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand (fun _ h ↦ h)).symm
            ((bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand (fun _ h ↦ h))
              ((), ⟨uThreeQuarters, uThreeQuarters_mem_edgeBand⟩, x)))) = x
    rw [Homeomorph.symm_apply_apply]
    rfl

/-- The overlap of the two standard circle-mapping-torus pieces deformation-retracts to its
low and high fibre components. -/
public def circleMappingTorusOverlapHomotopyEquiv
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    HomotopyEquiv (F ⊕ F)
      ↥(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi)) :=
  (((((homotopyEquivSum
      (fiberBandProdHomotopyEquiv (F := F) uQuarter_mem_lowBand)
      (fiberBandProdHomotopyEquiv (F := F) uThreeQuarters_mem_highBand)).trans
        Homeomorph.sumProdDistrib.symm.toHomotopyEquiv).trans
      (lowHighOverlapBandHomeomorph.prodCongr
        (Homeomorph.refl F)).toHomotopyEquiv).trans
    unitProdHomeomorph.symm.toHomotopyEquiv).trans
      (bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_overlapBand
        overlapBand_subset_edgeBand).toHomotopyEquiv).trans
    (overlapHomeo (fun _ : Unit ↦ phi)).toHomotopyEquiv

@[simp]
public theorem circleMappingTorusOverlapHomotopyEquiv_toFun_inl
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    (circleMappingTorusOverlapHomotopyEquiv phi).toFun (Sum.inl x) =
      overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand () x := by
  rfl

@[simp]
public theorem circleMappingTorusOverlapHomotopyEquiv_toFun_inr
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    (circleMappingTorusOverlapHomotopyEquiv phi).toFun (Sum.inr x) =
      overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand () x := by
  rfl

public theorem circleMappingTorusOverlapLow_edgeRetract
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    (circleMappingTorusEdgePieceHomotopyEquiv phi).invFun.comp
        ((interToRight (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi))).comp
            ((circleMappingTorusOverlapHomotopyEquiv phi).toFun.comp
              (sumInlContinuousMap (X := F)))) =
      ContinuousMap.id F := by
  ext x
  exact circleMappingTorusEdgePieceHomotopyEquiv_invFun_edgeLowPt phi x

public theorem circleMappingTorusOverlapLow_vertexRetract
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    (vertexRetract (fun _ : Unit ↦ phi)).comp
        ((interToLeft (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi))).comp
            ((circleMappingTorusOverlapHomotopyEquiv phi).toFun.comp
              (sumInlContinuousMap (X := F)))) =
      ContinuousMap.id F := by
  ext x
  change vertexRetract (fun _ : Unit ↦ phi)
      (vertexLowPt (fun _ : Unit ↦ phi) () x) = x
  exact congrArg (fun g : C(F, F) => g x)
    (vertexRetract_comp_vertexLowPt (fun _ : Unit ↦ phi) ())

public theorem circleMappingTorusOverlapLow_intertwining
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (f : FundamentalGroup F x →* H)
    (a : FundamentalGroup F x) :
    (fundamentalGroupoidBasedFunctor x f).map
          ((FundamentalGroupoid.map
            ((circleMappingTorusEdgePieceHomotopyEquiv phi).invFun.comp
              ((interToRight (vertexPiece (fun _ : Unit ↦ phi))
                (edgePiece (fun _ : Unit ↦ phi))).comp
                  ((circleMappingTorusOverlapHomotopyEquiv phi).toFun.comp
                    (sumInlContinuousMap (X := F)))))).map a) ≫ (1 : H) =
      (1 : H) ≫
        (fundamentalGroupoidBasedFunctor x f).map
          ((FundamentalGroupoid.map
            ((vertexRetract (fun _ : Unit ↦ phi)).comp
              ((interToLeft (vertexPiece (fun _ : Unit ↦ phi))
                (edgePiece (fun _ : Unit ↦ phi))).comp
                  ((circleMappingTorusOverlapHomotopyEquiv phi).toFun.comp
                    (sumInlContinuousMap (X := F)))))).map a) := by
  rw [circleMappingTorusOverlapLow_edgeRetract,
    circleMappingTorusOverlapLow_vertexRetract]
  rw [show FundamentalGroupoid.map (ContinuousMap.id F) = 𝟭 _ from
    FundamentalGroupoid.map_id]
  change (1 : H) * _ = _ * (1 : H)
  simp

public theorem circleMappingTorusOverlapHigh_edgeRetract
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    (circleMappingTorusEdgePieceHomotopyEquiv phi).invFun.comp
        ((interToRight (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi))).comp
            ((circleMappingTorusOverlapHomotopyEquiv phi).toFun.comp
              (sumInrContinuousMap (X := F)))) =
      ContinuousMap.id F := by
  ext x
  exact circleMappingTorusEdgePieceHomotopyEquiv_invFun_edgeHighPt phi x

public theorem circleMappingTorusOverlapHigh_vertexRetract
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    (vertexRetract (fun _ : Unit ↦ phi)).comp
        ((interToLeft (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi))).comp
            ((circleMappingTorusOverlapHomotopyEquiv phi).toFun.comp
              (sumInrContinuousMap (X := F)))) =
      (phi : C(F, F)) := by
  ext x
  change vertexRetract (fun _ : Unit ↦ phi)
      (vertexHighPt (fun _ : Unit ↦ phi) () x) = phi x
  exact congrArg (fun f : C(F, F) => f x)
    (vertexRetract_comp_vertexHighPt (fun _ : Unit ↦ phi) ())

public theorem circleMappingTorusOverlapHigh_intertwining
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a))
    (a : FundamentalGroup F x) :
    (fundamentalGroupoidBasedFunctor x f).map
          ((FundamentalGroupoid.map
            ((circleMappingTorusEdgePieceHomotopyEquiv phi).invFun.comp
              ((interToRight (vertexPiece (fun _ : Unit ↦ phi))
                (edgePiece (fun _ : Unit ↦ phi))).comp
                  ((circleMappingTorusOverlapHomotopyEquiv phi).toFun.comp
                    (sumInrContinuousMap (X := F)))))).map a) ≫
        circleMappingTorusHighGauge phi x delta f t =
      circleMappingTorusHighGauge phi x delta f t ≫
        (fundamentalGroupoidBasedFunctor x f).map
          ((FundamentalGroupoid.map
            ((vertexRetract (fun _ : Unit ↦ phi)).comp
              ((interToLeft (vertexPiece (fun _ : Unit ↦ phi))
                (edgePiece (fun _ : Unit ↦ phi))).comp
                  ((circleMappingTorusOverlapHomotopyEquiv phi).toFun.comp
                    (sumInrContinuousMap (X := F)))))).map a) := by
  rw [circleMappingTorusOverlapHigh_edgeRetract,
    circleMappingTorusOverlapHigh_vertexRetract]
  rw [show FundamentalGroupoid.map (ContinuousMap.id F) = 𝟭 _ from
    FundamentalGroupoid.map_id]
  exact fundamentalGroupoidBasedFunctor_high_intertwining phi x delta f t h a

public theorem circleMappingTorusOverlapHigh_intertwining_at_mapped_object
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a))
    (a :
      (FundamentalGroupoid.map
        (circleMappingTorusOverlapHomotopyEquiv phi).toFun).obj
          (FundamentalGroupoid.mk (Sum.inr x)) ⟶
      (FundamentalGroupoid.map
        (circleMappingTorusOverlapHomotopyEquiv phi).toFun).obj
          (FundamentalGroupoid.mk (Sum.inr x))) :
    (fundamentalGroupoidBasedFunctor x f).map
          ((FundamentalGroupoid.map
            ((circleMappingTorusEdgePieceHomotopyEquiv phi).invFun.comp
              (interToRight (vertexPiece (fun _ : Unit ↦ phi))
                (edgePiece (fun _ : Unit ↦ phi))))).map a) ≫
        circleMappingTorusHighGauge phi x delta f t =
      circleMappingTorusHighGauge phi x delta f t ≫
        (fundamentalGroupoidBasedFunctor x f).map
          ((FundamentalGroupoid.map
            ((vertexRetract (fun _ : Unit ↦ phi)).comp
              (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
                (edgePiece (fun _ : Unit ↦ phi))))).map a) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (circleMappingTorusOverlapHomotopyEquiv phi)
  have hsurj : Function.Surjective
      ((FundamentalGroupoid.map
        (circleMappingTorusOverlapHomotopyEquiv phi).toFun).map :
          (FundamentalGroupoid.mk (Sum.inr x) ⟶ FundamentalGroupoid.mk (Sum.inr x)) →
          _) := by
    exact E.fullyFaithfulFunctor.map_bijective
      (FundamentalGroupoid.mk (Sum.inr x)) (FundamentalGroupoid.mk (Sum.inr x)) |>.2
  obtain ⟨q, hq⟩ := hsurj a
  obtain ⟨p, hp⟩ :=
    (fundamentalGroupoid_sumInr_map_bijective x x).2 q
  change circleMappingTorusHighGauge phi x delta f t * _ =
    _ * circleMappingTorusHighGauge phi x delta f t
  rw [← hq, ← hp]
  have hpIntertwining :=
    circleMappingTorusOverlapHigh_intertwining phi x delta f t h p
  change circleMappingTorusHighGauge phi x delta f t * _ =
    _ * circleMappingTorusHighGauge phi x delta f t at hpIntertwining
  convert hpIntertwining using 1 <;> induction p using Quotient.ind <;> rfl

public theorem circleMappingTorusOverlapHigh_intertwining_all
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a))
    (a : FundamentalGroup
      ↥(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi))
        (overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand () x)) :
    (fundamentalGroupoidBasedFunctor x f).map
          ((FundamentalGroupoid.map
            ((circleMappingTorusEdgePieceHomotopyEquiv phi).invFun.comp
              (interToRight (vertexPiece (fun _ : Unit ↦ phi))
                (edgePiece (fun _ : Unit ↦ phi))))).map a) ≫
        circleMappingTorusHighGauge phi x delta f t =
      circleMappingTorusHighGauge phi x delta f t ≫
        (fundamentalGroupoidBasedFunctor x f).map
          ((FundamentalGroupoid.map
            ((vertexRetract (fun _ : Unit ↦ phi)).comp
              (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
                (edgePiece (fun _ : Unit ↦ phi))))).map a) := by
  exact circleMappingTorusOverlapHigh_intertwining_at_mapped_object
    phi x delta f t h a

def circleMappingTorusOverlapPullbackNatIso
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    FundamentalGroupoid.map (circleMappingTorusOverlapHomotopyEquiv phi).toFun ⋙
          FundamentalGroupoid.map
            ((circleMappingTorusEdgePieceHomotopyEquiv phi).invFun.comp
              (interToRight (vertexPiece (fun _ : Unit ↦ phi))
                (edgePiece (fun _ : Unit ↦ phi)))) ⋙
          fundamentalGroupoidBasedFunctor x f ≅
      FundamentalGroupoid.map (circleMappingTorusOverlapHomotopyEquiv phi).toFun ⋙
          FundamentalGroupoid.map
            ((vertexRetract (fun _ : Unit ↦ phi)).comp
              (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
                (edgePiece (fun _ : Unit ↦ phi)))) ⋙
          fundamentalGroupoidBasedFunctor x f := by
  let edgeFunctor :=
    FundamentalGroupoid.map (circleMappingTorusOverlapHomotopyEquiv phi).toFun ⋙
      FundamentalGroupoid.map
        ((circleMappingTorusEdgePieceHomotopyEquiv phi).invFun.comp
          (interToRight (vertexPiece (fun _ : Unit ↦ phi))
            (edgePiece (fun _ : Unit ↦ phi)))) ⋙
      fundamentalGroupoidBasedFunctor x f
  let vertexFunctor :=
    FundamentalGroupoid.map (circleMappingTorusOverlapHomotopyEquiv phi).toFun ⋙
      FundamentalGroupoid.map
        ((vertexRetract (fun _ : Unit ↦ phi)).comp
          (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
            (edgePiece (fun _ : Unit ↦ phi)))) ⋙
      fundamentalGroupoidBasedFunctor x f
  let hconn : ∀ y : FundamentalGroupoid F,
      Nonempty (FundamentalGroupoid.mk x ⟶ y) := fun y =>
    ⟨Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y.as)⟩
  let leftIso : FundamentalGroupoid.map (sumInlContinuousMap (X := F)) ⋙ edgeFunctor ≅
      FundamentalGroupoid.map (sumInlContinuousMap (X := F)) ⋙ vertexFunctor :=
    groupoidSingleObjNatIsoOfBase _ _ (FundamentalGroupoid.mk x) hconn 1 (by
      intro a
      have ha := circleMappingTorusOverlapLow_intertwining phi x f a
      convert ha using 1 <;> induction a using Quotient.ind <;> rfl)
  let rightIso : FundamentalGroupoid.map (sumInrContinuousMap (X := F)) ⋙ edgeFunctor ≅
      FundamentalGroupoid.map (sumInrContinuousMap (X := F)) ⋙ vertexFunctor :=
    groupoidSingleObjNatIsoOfBase _ _ (FundamentalGroupoid.mk x) hconn
      (circleMappingTorusHighGauge phi x delta f t) (by
        intro a
        have ha := circleMappingTorusOverlapHigh_intertwining_at_mapped_object
          phi x delta f t h
            ((FundamentalGroupoid.map
              (circleMappingTorusOverlapHomotopyEquiv phi).toFun).map
                ((FundamentalGroupoid.map (sumInrContinuousMap (X := F))).map a))
        convert ha using 1 <;> induction a using Quotient.ind <;> rfl)
  exact fundamentalGroupoidNatIsoSum edgeFunctor vertexFunctor leftIso rightIso

public theorem circleMappingTorusOverlapPullbackNatIso_app_inr
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    (circleMappingTorusOverlapPullbackNatIso phi x delta f t h).hom.app
        (FundamentalGroupoid.mk (Sum.inr x)) =
      circleMappingTorusHighGauge phi x delta f t := by
  unfold circleMappingTorusOverlapPullbackNatIso
  apply groupoidSingleObjNatIsoOfBase_app_base
  intro a
  have ha := circleMappingTorusOverlapHigh_intertwining_at_mapped_object
    phi x delta f t h
      ((FundamentalGroupoid.map
        (circleMappingTorusOverlapHomotopyEquiv phi).toFun).map
          ((FundamentalGroupoid.map (sumInrContinuousMap (X := F))).map a))
  convert ha using 1 <;> induction a using Quotient.ind <;> rfl

public theorem circleMappingTorusOverlapPullbackNatIso_app_inl
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    (circleMappingTorusOverlapPullbackNatIso phi x delta f t h).hom.app
        (FundamentalGroupoid.mk (Sum.inl x)) = 1 := by
  unfold circleMappingTorusOverlapPullbackNatIso
  apply groupoidSingleObjNatIsoOfBase_app_base
  intro a
  have ha := circleMappingTorusOverlapLow_intertwining phi x f a
  convert ha using 1 <;> induction a using Quotient.ind <;> rfl

def natIsoOfWhiskerEquivalence
    {C D E : Type*} [Category C] [Category D] [Category E]
    (e : C ≌ D) (A B : D ⥤ E) (α : e.functor ⋙ A ≅ e.functor ⋙ B) :
    A ≅ B :=
  (Functor.leftUnitor A).symm |>.trans
    ((Functor.isoWhiskerRight e.counitIso.symm A).trans
      ((Functor.associator e.inverse e.functor A).trans
        ((Functor.isoWhiskerLeft e.inverse α).trans
          ((Functor.associator e.inverse e.functor B).symm.trans
            ((Functor.isoWhiskerRight e.counitIso B).trans
              (Functor.leftUnitor B))))))

theorem natIsoOfWhiskerEquivalence_app_obj
    {C D E : Type*} [Category C] [Category D] [Category E]
    (e : C ≌ D) (A B : D ⥤ E) (α : e.functor ⋙ A ≅ e.functor ⋙ B)
    (c : C) :
    (natIsoOfWhiskerEquivalence e A B α).hom.app (e.functor.obj c) =
      α.hom.app c := by
  dsimp [natIsoOfWhiskerEquivalence]
  simp only [Category.id_comp, Category.comp_id]
  rw [e.counitInv_app_functor]
  rw [← Category.assoc]
  change ((e.functor ⋙ A).map (e.unit.app c) ≫ α.hom.app _) ≫ _ = _
  rw [α.hom.naturality]
  change (α.hom.app c ≫ B.map (e.functor.map (e.unit.app c))) ≫
    B.map (e.counitIso.hom.app (e.functor.obj c)) = α.hom.app c
  rw [Category.assoc, ← B.map_comp, e.functor_unit_comp, B.map_id]
  exact Category.comp_id _

def circleMappingTorusOverlapNatIso
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    FundamentalGroupoid.map
          ((circleMappingTorusEdgePieceHomotopyEquiv phi).invFun.comp
            (interToRight (vertexPiece (fun _ : Unit ↦ phi))
              (edgePiece (fun _ : Unit ↦ phi)))) ⋙
        fundamentalGroupoidBasedFunctor x f ≅
      FundamentalGroupoid.map
          ((vertexRetract (fun _ : Unit ↦ phi)).comp
            (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
              (edgePiece (fun _ : Unit ↦ phi)))) ⋙
        fundamentalGroupoidBasedFunctor x f := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (circleMappingTorusOverlapHomotopyEquiv phi)
  exact natIsoOfWhiskerEquivalence e _ _
    (circleMappingTorusOverlapPullbackNatIso phi x delta f t h)

public theorem circleMappingTorusOverlapNatIso_app_low
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    (circleMappingTorusOverlapNatIso phi x delta f t h).hom.app
        (FundamentalGroupoid.mk
          (overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand () x)) = 1 := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (circleMappingTorusOverlapHomotopyEquiv phi)
  have happ := natIsoOfWhiskerEquivalence_app_obj e _ _
    (circleMappingTorusOverlapPullbackNatIso phi x delta f t h)
      (FundamentalGroupoid.mk (Sum.inl x))
  rw [circleMappingTorusOverlapPullbackNatIso_app_inl phi x delta f t h] at happ
  let α := circleMappingTorusOverlapNatIso phi x delta f t h
  have hobj : e.functor.obj (FundamentalGroupoid.mk (Sum.inl x)) =
      FundamentalGroupoid.mk
        (overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand () x) := by
    change FundamentalGroupoid.mk
        ((circleMappingTorusOverlapHomotopyEquiv phi).toFun (Sum.inl x)) = _
    rw [circleMappingTorusOverlapHomotopyEquiv_toFun_inl]
  have htransport := congrArg (fun z => (α.hom.app z : H)) hobj
  calc
    (α.hom.app (FundamentalGroupoid.mk
        (overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand () x)) : H) =
        α.hom.app (e.functor.obj (FundamentalGroupoid.mk (Sum.inl x))) := htransport.symm
    _ = 1 := by simpa only [α, e, circleMappingTorusOverlapNatIso] using happ

public theorem circleMappingTorusOverlapNatIso_app_high
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    (circleMappingTorusOverlapNatIso phi x delta f t h).hom.app
        (FundamentalGroupoid.mk
          (overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand () x)) =
      circleMappingTorusHighGauge phi x delta f t := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (circleMappingTorusOverlapHomotopyEquiv phi)
  have happ := natIsoOfWhiskerEquivalence_app_obj e _ _
    (circleMappingTorusOverlapPullbackNatIso phi x delta f t h)
      (FundamentalGroupoid.mk (Sum.inr x))
  rw [circleMappingTorusOverlapPullbackNatIso_app_inr phi x delta f t h] at happ
  let α := circleMappingTorusOverlapNatIso phi x delta f t h
  have hobj : e.functor.obj (FundamentalGroupoid.mk (Sum.inr x)) =
      FundamentalGroupoid.mk
        (overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand () x) := by
    change FundamentalGroupoid.mk
        ((circleMappingTorusOverlapHomotopyEquiv phi).toFun (Sum.inr x)) = _
    rw [circleMappingTorusOverlapHomotopyEquiv_toFun_inr]
  have htransport := congrArg (fun z => (α.hom.app z : H)) hobj
  calc
    (α.hom.app (FundamentalGroupoid.mk
        (overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand () x)) : H) =
        α.hom.app (e.functor.obj (FundamentalGroupoid.mk (Sum.inr x))) := htransport.symm
    _ = circleMappingTorusHighGauge phi x delta f t := by
      simpa only [α, e, circleMappingTorusOverlapNatIso] using happ

def circleMappingTorusEdgeGauge
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a))
    (y : FundamentalGroupoid ↥(edgePiece (fun _ : Unit ↦ phi))) : H := by
  classical
  exact if hy : y.as.1 ∈ vertexPiece (fun _ : Unit ↦ phi) then
      (circleMappingTorusOverlapNatIso phi x delta f t h).hom.app
        (FundamentalGroupoid.mk ⟨y.as.1, hy, y.as.2⟩)
    else 1

public theorem circleMappingTorusEdgeGauge_low
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    circleMappingTorusEdgeGauge phi x delta f t h
        (FundamentalGroupoid.mk (edgeLowPt (fun _ : Unit ↦ phi) () x)) = 1 := by
  classical
  let w := overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand () x
  have hw : (edgeLowPt (fun _ : Unit ↦ phi) () x).1 ∈
      vertexPiece (fun _ : Unit ↦ phi) := w.2.1
  unfold circleMappingTorusEdgeGauge
  rw [dite_eq_left hw]
  change ((circleMappingTorusOverlapNatIso phi x delta f t h).hom.app
      (FundamentalGroupoid.mk
        ⟨(edgeLowPt (fun _ : Unit ↦ phi) () x).1, hw,
          (edgeLowPt (fun _ : Unit ↦ phi) () x).2⟩) : H) = 1
  have hpt :
      (⟨(edgeLowPt (fun _ : Unit ↦ phi) () x).1, hw,
          (edgeLowPt (fun _ : Unit ↦ phi) () x).2⟩ :
        ↥(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi))) = w := by
    apply Subtype.ext
    rfl
  rw [hpt]
  exact circleMappingTorusOverlapNatIso_app_low phi x delta f t h

public theorem circleMappingTorusEdgeGauge_high
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    circleMappingTorusEdgeGauge phi x delta f t h
        (FundamentalGroupoid.mk (edgeHighPt (fun _ : Unit ↦ phi) () x)) =
      circleMappingTorusHighGauge phi x delta f t := by
  classical
  let w := overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand () x
  have hw : (edgeHighPt (fun _ : Unit ↦ phi) () x).1 ∈
      vertexPiece (fun _ : Unit ↦ phi) := w.2.1
  unfold circleMappingTorusEdgeGauge
  rw [dite_eq_left hw]
  change ((circleMappingTorusOverlapNatIso phi x delta f t h).hom.app
      (FundamentalGroupoid.mk
        ⟨(edgeHighPt (fun _ : Unit ↦ phi) () x).1, hw,
          (edgeHighPt (fun _ : Unit ↦ phi) () x).2⟩) : H) =
      circleMappingTorusHighGauge phi x delta f t
  have hpt :
      (⟨(edgeHighPt (fun _ : Unit ↦ phi) () x).1, hw,
          (edgeHighPt (fun _ : Unit ↦ phi) () x).2⟩ :
        ↥(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi))) = w := by
    apply Subtype.ext
    rfl
  rw [hpt]
  exact circleMappingTorusOverlapNatIso_app_high phi x delta f t h

def circleMappingTorusStrictifiedEdgeFunctor
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    FundamentalGroupoid ↥(edgePiece (fun _ : Unit ↦ phi)) ⥤ SingleObj H :=
  singleObjGaugeFunctor
    (FundamentalGroupoid.map (circleMappingTorusEdgePieceHomotopyEquiv phi).invFun ⋙
      fundamentalGroupoidBasedFunctor x f)
    (circleMappingTorusEdgeGauge phi x delta f t h)

public theorem circleMappingTorusStrictifiedEdgeFunctor_restrict
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    FundamentalGroupoid.map
          (interToRight (vertexPiece (fun _ : Unit ↦ phi))
            (edgePiece (fun _ : Unit ↦ phi))) ⋙
        circleMappingTorusStrictifiedEdgeFunctor phi x delta f t h =
      FundamentalGroupoid.map
          ((vertexRetract (fun _ : Unit ↦ phi)).comp
            (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
              (edgePiece (fun _ : Unit ↦ phi)))) ⋙
        fundamentalGroupoidBasedFunctor x f := by
  fapply CategoryTheory.Functor.hext
  · intro y
    rfl
  intro y z p
  have hnaturality :=
    (circleMappingTorusOverlapNatIso phi x delta f t h).hom.naturality p
  have hgauge (w : FundamentalGroupoid
      ↥(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi))) :
      circleMappingTorusEdgeGauge phi x delta f t h
          ((FundamentalGroupoid.map
            (interToRight (vertexPiece (fun _ : Unit ↦ phi))
              (edgePiece (fun _ : Unit ↦ phi)))).obj w) =
        (circleMappingTorusOverlapNatIso phi x delta f t h).hom.app w := by
    classical
    unfold circleMappingTorusEdgeGauge
    have hw :
        ((FundamentalGroupoid.map
          (interToRight (vertexPiece (fun _ : Unit ↦ phi))
            (edgePiece (fun _ : Unit ↦ phi)))).obj w).as.1 ∈
          vertexPiece (fun _ : Unit ↦ phi) := w.as.2.1
    rw [dite_eq_left hw]
    congr 2
  apply heq_of_eq
  change
    circleMappingTorusEdgeGauge phi x delta f t h
          ((FundamentalGroupoid.map
            (interToRight (vertexPiece (fun _ : Unit ↦ phi))
              (edgePiece (fun _ : Unit ↦ phi)))).obj z) *
        (fundamentalGroupoidBasedFunctor x f).map
          ((FundamentalGroupoid.map
            (circleMappingTorusEdgePieceHomotopyEquiv phi).invFun).map
              ((FundamentalGroupoid.map
                (interToRight (vertexPiece (fun _ : Unit ↦ phi))
                  (edgePiece (fun _ : Unit ↦ phi)))).map p)) *
        (circleMappingTorusEdgeGauge phi x delta f t h
          ((FundamentalGroupoid.map
            (interToRight (vertexPiece (fun _ : Unit ↦ phi))
              (edgePiece (fun _ : Unit ↦ phi)))).obj y))⁻¹ =
      (fundamentalGroupoidBasedFunctor x f).map
        ((FundamentalGroupoid.map
          ((vertexRetract (fun _ : Unit ↦ phi)).comp
            (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
              (edgePiece (fun _ : Unit ↦ phi))))).map p)
  change _ * _ = _ * _ at hnaturality
  have hkey :
      (circleMappingTorusOverlapNatIso phi x delta f t h).hom.app z *
          (fundamentalGroupoidBasedFunctor x f).map
            ((FundamentalGroupoid.map
              (circleMappingTorusEdgePieceHomotopyEquiv phi).invFun).map
                ((FundamentalGroupoid.map
                  (interToRight (vertexPiece (fun _ : Unit ↦ phi))
                    (edgePiece (fun _ : Unit ↦ phi)))).map p)) =
        (fundamentalGroupoidBasedFunctor x f).map
            ((FundamentalGroupoid.map
              ((vertexRetract (fun _ : Unit ↦ phi)).comp
                (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
                  (edgePiece (fun _ : Unit ↦ phi))))).map p) *
          (circleMappingTorusOverlapNatIso phi x delta f t h).hom.app y := by
    convert hnaturality using 1 <;> induction p using Quotient.ind <;> rfl
  rw [hgauge y, hgauge z]
  rw [hkey]
  group

private theorem circleMappingTorus_pairwise_id_single {ι : Type*} (i : ι) :
    (CategoryTheory.Pairwise.Hom.id_single i :
      CategoryTheory.Pairwise.single i ⟶ CategoryTheory.Pairwise.single i) =
        𝟙 (CategoryTheory.Pairwise.single i : CategoryTheory.Pairwise ι) := by
  rfl

private theorem circleMappingTorus_pairwise_id_pair {ι : Type*} (i j : ι) :
    (CategoryTheory.Pairwise.Hom.id_pair i j :
      CategoryTheory.Pairwise.pair i j ⟶ CategoryTheory.Pairwise.pair i j) =
        𝟙 (CategoryTheory.Pairwise.pair i j : CategoryTheory.Pairwise ι) := by
  rfl

noncomputable def circleMappingTorusPairwiseCoconeOfCompatible
    {ι C : Type*} [Category C]
    (D : CategoryTheory.Pairwise ι ⥤ C) (T : C)
    (F : ∀ i : ι, D.obj (.single i) ⟶ T)
    (hF : ∀ i j, D.map (.left i j) ≫ F i = D.map (.right i j) ≫ F j) :
    CategoryTheory.Limits.Cocone D where
  pt := T
  ι.app
    | .single i => F i
    | .pair i j => D.map (.left i j) ≫ F i
  ι.naturality := by
    intro a b p
    exact CategoryTheory.Pairwise.Hom.rec
      (fun i => by
        rw [circleMappingTorus_pairwise_id_single i]
        simp)
      (fun i j => by
        rw [circleMappingTorus_pairwise_id_pair i j]
        simp)
      (fun _ _ => by
        dsimp
        simp)
      (fun i j => by
        dsimp
        simpa using (hF i j).symm)
      p

def circleMappingTorusPairwiseCover
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    Bool → Opens (CircleMappingTorus phi)
  | false => circleMappingTorusVertexOpen phi
  | true => circleMappingTorusEdgeOpen phi

private def circleMappingTorusSwapIntersection
    {X : Type*} [TopologicalSpace X] (U V : Set X) :
    C((V ∩ U : Set X), (U ∩ V : Set X)) where
  toFun x := ⟨x, x.2.2, x.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

theorem circleMappingTorus_reverse_restricted_eq
    {X : Type} [TopologicalSpace X] (U V : Set X)
    {T : Type} [Groupoid T]
    (FU : FundamentalGroupoid U ⥤ T) (FV : FundamentalGroupoid V ⥤ T)
    (h : FundamentalGroupoid.map (interToLeft U V) ⋙ FU =
      FundamentalGroupoid.map (interToRight U V) ⋙ FV) :
    FundamentalGroupoid.map (interToLeft V U) ⋙ FV =
      FundamentalGroupoid.map (interToRight V U) ⋙ FU := by
  have h' := congrArg
    (fun K => FundamentalGroupoid.map (circleMappingTorusSwapIntersection U V) ⋙ K) h
  change
    FundamentalGroupoid.map (circleMappingTorusSwapIntersection U V) ⋙
        (FundamentalGroupoid.map (interToLeft U V) ⋙ FU) =
      FundamentalGroupoid.map (circleMappingTorusSwapIntersection U V) ⋙
        (FundamentalGroupoid.map (interToRight U V) ⋙ FV) at h'
  rw [← Functor.assoc, ← FundamentalGroupoid.map_comp,
    ← Functor.assoc, ← FundamentalGroupoid.map_comp] at h'
  have hleft : (interToLeft U V).comp (circleMappingTorusSwapIntersection U V) =
      interToRight V U := by
    ext x
    rfl
  have hright : (interToRight U V).comp (circleMappingTorusSwapIntersection U V) =
      interToLeft V U := by
    ext x
    rfl
  rw [hleft, hright] at h'
  exact h'.symm

noncomputable def circleMappingTorusTargetCocone
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    CategoryTheory.Limits.Cocone
      (CategoryTheory.Pairwise.diagram (circleMappingTorusPairwiseCover phi) ⋙
        FundamentalGroupoid.opensToGrpd
          (TopCat.of (CircleMappingTorus phi))) := by
  let D := CategoryTheory.Pairwise.diagram (circleMappingTorusPairwiseCover phi) ⋙
    FundamentalGroupoid.opensToGrpd (TopCat.of (CircleMappingTorus phi))
  let vertexFunctor : FundamentalGroupoid
        ↥(vertexPiece (fun _ : Unit ↦ phi)) ⥤ SingleObj H :=
    FundamentalGroupoid.map (vertexRetract (fun _ : Unit ↦ phi)) ⋙
      fundamentalGroupoidBasedFunctor x f
  let edgeFunctor : FundamentalGroupoid
        ↥(edgePiece (fun _ : Unit ↦ phi)) ⥤ SingleObj H :=
    circleMappingTorusStrictifiedEdgeFunctor phi x delta f t h
  let localFunctor : ∀ i : Bool, D.obj (.single i) ⟶ Grpd.of (SingleObj H) := fun i => by
    cases i
    · exact vertexFunctor
    · exact edgeFunctor
  apply circleMappingTorusPairwiseCoconeOfCompatible D (Grpd.of (SingleObj H)) localFunctor
  intro i j
  cases i <;> cases j
  · change FundamentalGroupoid.map
        (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
          (vertexPiece (fun _ : Unit ↦ phi))) ⋙ vertexFunctor =
      FundamentalGroupoid.map
        (interToRight (vertexPiece (fun _ : Unit ↦ phi))
          (vertexPiece (fun _ : Unit ↦ phi))) ⋙ vertexFunctor
    congr 2

  · change FundamentalGroupoid.map
        (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi))) ⋙ vertexFunctor =
      FundamentalGroupoid.map
        (interToRight (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi))) ⋙ edgeFunctor
    simpa only [vertexFunctor, edgeFunctor, ← Functor.assoc,
      ← FundamentalGroupoid.map_comp] using
        (circleMappingTorusStrictifiedEdgeFunctor_restrict phi x delta f t h).symm
  · apply circleMappingTorus_reverse_restricted_eq
      (vertexPiece (fun _ : Unit ↦ phi)) (edgePiece (fun _ : Unit ↦ phi))
      vertexFunctor edgeFunctor
    simpa only [vertexFunctor, edgeFunctor, ← Functor.assoc,
      ← FundamentalGroupoid.map_comp] using
        (circleMappingTorusStrictifiedEdgeFunctor_restrict phi x delta f t h).symm
  · change FundamentalGroupoid.map
        (interToLeft (edgePiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi))) ⋙ edgeFunctor =
      FundamentalGroupoid.map
        (interToRight (edgePiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi))) ⋙ edgeFunctor
    congr 2

@[simp]
public theorem circleMappingTorusTargetCocone_pt
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    (circleMappingTorusTargetCocone phi x delta f t h).pt =
      Grpd.of (SingleObj H) := rfl

noncomputable def circleMappingTorusVanKampenCocone
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :=
  (FundamentalGroupoid.opensToGrpd (TopCat.of (CircleMappingTorus phi))).mapCocone
    (CategoryTheory.Pairwise.cocone (circleMappingTorusPairwiseCover phi))

public theorem circleMappingTorusVanKampenCocone_isColimit
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    Nonempty (CategoryTheory.Limits.IsColimit
      (circleMappingTorusVanKampenCocone phi)) := by
  have hsheaf := FundamentalGroupoid.isSheaf_op_opensToGrpd
    (X := TopCat.of (CircleMappingTorus phi))
  rcases hsheaf.isSheafPairwiseIntersections
      (circleMappingTorusPairwiseCover phi) with ⟨h⟩
  let e :
      ((circleMappingTorusVanKampenCocone phi).op) ≅
        ((FundamentalGroupoid.opensToGrpd
          (TopCat.of (CircleMappingTorus phi))).op.mapCone
            (CategoryTheory.Pairwise.cocone
              (circleMappingTorusPairwiseCover phi)).op) :=
    Functor.mapCoconeOp
      (G := FundamentalGroupoid.opensToGrpd
        (TopCat.of (CircleMappingTorus phi)))
      (t := CategoryTheory.Pairwise.cocone
        (circleMappingTorusPairwiseCover phi))
  exact ⟨CategoryTheory.Limits.isColimitOfOp
    ((CategoryTheory.Limits.IsLimit.equivIsoLimit e).symm h)⟩

noncomputable def circleMappingTorusVanKampenIsColimit
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    CategoryTheory.Limits.IsColimit (circleMappingTorusVanKampenCocone phi) :=
  (circleMappingTorusVanKampenCocone_isColimit phi).some

def circleMappingTorusToPairwiseCover
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    C(CircleMappingTorus phi,
      ↑(iSup (circleMappingTorusPairwiseCover phi))) where
  toFun y := ⟨y, by
    rw [Opens.mem_iSup]
    by_cases hy : y ∈ vertexPiece (fun _ : Unit ↦ phi)
    · exact ⟨false, hy⟩
    · have hy' : y ∈ vertexPiece (fun _ : Unit ↦ phi) ∪
          edgePiece (fun _ : Unit ↦ phi) := by
        rw [vertexPiece_union_edgePiece]
        exact Set.mem_univ y
      exact ⟨true, hy'.resolve_left hy⟩⟩
  continuous_toFun := continuous_id.subtype_mk _

noncomputable def circleMappingTorusVanKampenDescFunctor
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    FundamentalGroupoid
        ↑(iSup (circleMappingTorusPairwiseCover phi)) ⥤ SingleObj H :=
  (circleMappingTorusVanKampenIsColimit phi).desc
    (circleMappingTorusTargetCocone phi x delta f t h)

noncomputable def circleMappingTorusVanKampenLiftFunctor
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    FundamentalGroupoid (CircleMappingTorus phi) ⥤ SingleObj H :=
  FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) ⋙
    circleMappingTorusVanKampenDescFunctor phi x delta f t h

public theorem circleMappingTorusVanKampenLiftFunctor_vertex
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    FundamentalGroupoid.map
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(vertexPiece (fun _ : Unit ↦ phi)), CircleMappingTorus phi)) ⋙
        circleMappingTorusVanKampenLiftFunctor phi x delta f t h =
      FundamentalGroupoid.map (vertexRetract (fun _ : Unit ↦ phi)) ⋙
        fundamentalGroupoidBasedFunctor x f := by
  let P := circleMappingTorusVanKampenIsColimit phi
  have hleg :
      FundamentalGroupoid.map
            (⟨Subtype.val, continuous_subtype_val⟩ :
              C(↥(vertexPiece (fun _ : Unit ↦ phi)), CircleMappingTorus phi)) ⋙
          FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) =
        (circleMappingTorusVanKampenCocone phi).ι.app (.single false) := by
    rw [← FundamentalGroupoid.map_comp]
    congr 1
  have hfac := P.fac (circleMappingTorusTargetCocone phi x delta f t h) (.single false)
  change
    (circleMappingTorusVanKampenCocone phi).ι.app (.single false) ⋙
        circleMappingTorusVanKampenDescFunctor phi x delta f t h =
      FundamentalGroupoid.map (vertexRetract (fun _ : Unit ↦ phi)) ⋙
        fundamentalGroupoidBasedFunctor x f at hfac
  rw [← hleg] at hfac
  change
    (FundamentalGroupoid.map
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(vertexPiece (fun _ : Unit ↦ phi)), CircleMappingTorus phi)) ⋙
        FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi)) ⋙
          circleMappingTorusVanKampenDescFunctor phi x delta f t h =
      FundamentalGroupoid.map (vertexRetract (fun _ : Unit ↦ phi)) ⋙
        fundamentalGroupoidBasedFunctor x f at hfac
  simpa only [circleMappingTorusVanKampenLiftFunctor, Functor.assoc] using hfac

public theorem circleMappingTorusVanKampenLiftFunctor_edge
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    FundamentalGroupoid.map
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(edgePiece (fun _ : Unit ↦ phi)), CircleMappingTorus phi)) ⋙
        circleMappingTorusVanKampenLiftFunctor phi x delta f t h =
      circleMappingTorusStrictifiedEdgeFunctor phi x delta f t h := by
  let P := circleMappingTorusVanKampenIsColimit phi
  have hleg :
      FundamentalGroupoid.map
            (⟨Subtype.val, continuous_subtype_val⟩ :
              C(↥(edgePiece (fun _ : Unit ↦ phi)), CircleMappingTorus phi)) ⋙
          FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) =
        (circleMappingTorusVanKampenCocone phi).ι.app (.single true) := by
    rw [← FundamentalGroupoid.map_comp]
    congr 1
  have hfac := P.fac (circleMappingTorusTargetCocone phi x delta f t h) (.single true)
  change
    (circleMappingTorusVanKampenCocone phi).ι.app (.single true) ⋙
        circleMappingTorusVanKampenDescFunctor phi x delta f t h =
      circleMappingTorusStrictifiedEdgeFunctor phi x delta f t h at hfac
  rw [← hleg] at hfac
  change
    (FundamentalGroupoid.map
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(edgePiece (fun _ : Unit ↦ phi)), CircleMappingTorus phi)) ⋙
        FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi)) ⋙
          circleMappingTorusVanKampenDescFunctor phi x delta f t h =
      circleMappingTorusStrictifiedEdgeFunctor phi x delta f t h at hfac
  simpa only [circleMappingTorusVanKampenLiftFunctor, Functor.assoc] using hfac

public theorem circleMappingTorusVanKampenLiftFunctor_fiber
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    FundamentalGroupoid.map
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)) ⋙
        circleMappingTorusVanKampenLiftFunctor phi x delta f t h =
      fundamentalGroupoidBasedFunctor x f := by
  have hv := congrArg
    (fun K => FundamentalGroupoid.map
        (vertexFiberInclusion (fun _ : Unit ↦ phi)) ⋙ K)
    (circleMappingTorusVanKampenLiftFunctor_vertex phi x delta f t h)
  simp only [← Functor.assoc, ← FundamentalGroupoid.map_comp] at hv
  have hleft :
      (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(vertexPiece (fun _ : Unit ↦ phi)), CircleMappingTorus phi)).comp
          (vertexFiberInclusion (fun _ : Unit ↦ phi)) =
        finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi) := by
    ext y
    rfl
  have hright :
      (vertexRetract (fun _ : Unit ↦ phi)).comp
          (vertexFiberInclusion (fun _ : Unit ↦ phi)) = ContinuousMap.id F := by
    ext y
    exact vertexRetract_vertexFiberInclusion (fun _ : Unit ↦ phi) y
  rw [hleft, hright] at hv
  have hid : FundamentalGroupoid.map (ContinuousMap.id F) =
      𝟭 (FundamentalGroupoid F) := by
    fapply CategoryTheory.Functor.hext
    · intro y
      rfl
    · intro y z p
      induction p using Quotient.ind
      rfl
  rw [hid, Functor.id_comp] at hv
  exact hv

def circleMappingTorusBaseGauge
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (x : F) (f : FundamentalGroup F x →* H) : H :=
  f (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x))

noncomputable def circleMappingTorusNormalizedLiftFunctor
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    FundamentalGroupoid (CircleMappingTorus phi) ⥤ SingleObj H :=
  singleObjGaugeFunctor
    (circleMappingTorusVanKampenLiftFunctor phi x delta f t h)
    (fun _ => circleMappingTorusBaseGauge x f)

noncomputable def circleMappingTorusVanKampenLift
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    FundamentalGroup (CircleMappingTorus phi) (circleMappingTorusBase phi x) →* H where
  toFun a := (circleMappingTorusNormalizedLiftFunctor phi x delta f t h).map a
  map_one' := by
    change (circleMappingTorusNormalizedLiftFunctor phi x delta f t h).map (𝟙 _) = 𝟙 _
    exact (circleMappingTorusNormalizedLiftFunctor phi x delta f t h).map_id _
  map_mul' a b := by
    change (circleMappingTorusNormalizedLiftFunctor phi x delta f t h).map (b ≫ a) =
      (circleMappingTorusNormalizedLiftFunctor phi x delta f t h).map b ≫
        (circleMappingTorusNormalizedLiftFunctor phi x delta f t h).map a
    exact (circleMappingTorusNormalizedLiftFunctor phi x delta f t h).map_comp b a

public theorem circleMappingTorusVanKampenLift_fiber
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a))
    (a : FundamentalGroup F x) :
    circleMappingTorusVanKampenLift phi x delta f t h
        (circleMappingTorusFiberHom phi x a) = f a := by
  have hf := congrArg (fun K => K.map a)
    (circleMappingTorusVanKampenLiftFunctor_fiber phi x delta f t h)
  change
    (circleMappingTorusVanKampenLiftFunctor phi x delta f t h).map
        (circleMappingTorusFiberHom phi x a) =
      (fundamentalGroupoidBasedFunctor x f).map a at hf
  change
    circleMappingTorusBaseGauge x f *
        (circleMappingTorusVanKampenLiftFunctor phi x delta f t h).map
          (circleMappingTorusFiberHom phi x a) *
      (circleMappingTorusBaseGauge x f)⁻¹ = f a
  rw [hf]
  change
    circleMappingTorusBaseGauge x f *
        f (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x) ≫ a ≫
          Groupoid.inv
            (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x))) *
      (circleMappingTorusBaseGauge x f)⁻¹ = f a
  unfold circleMappingTorusBaseGauge
  let p₀ : FundamentalGroup F x :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x)
  have hp :
      Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x) ≫ a ≫
          Groupoid.inv
            (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x)) =
        p₀⁻¹ * a * p₀ := rfl
  rw [hp, f.map_mul, f.map_mul, f.map_inv]
  dsimp [p₀]
  group

end SphereSixComplex
