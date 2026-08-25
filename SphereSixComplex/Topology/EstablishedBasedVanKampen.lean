module

public import SphereSixComplex.Topology.ConcreteVanKampen
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Existence
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.RecoveredSubgroup
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed

/-!
# Based generator extraction from groupoid van Kampen

Mathlib proves the fundamental-groupoid colimit theorem for open covers. This module isolates the
standard based-group consequence: after choosing connector paths, generators for the local
fundamental groups generate the fundamental group of the covered space.
-/

@[expose] public section

noncomputable section

open Set Topology CategoryTheory TauCeti TauCeti.UniversalCover
open scoped ContinuousMap

namespace SphereSixComplex.Topology
namespace PaperVanKampenFourPieceCover

variable {Y : Type*} [TopologicalSpace Y] {base : Y}

/-- Inclusion of a subspace into its ambient space. -/
public def subsetInclusion (U : Set Y) : C(U, Y) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The central-piece fundamental group mapped to the ambient base point. -/
public def coreFundamentalGroupMap (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup D.core ⟨base, D.base_mem_core⟩ →* FundamentalGroup Y base :=
  FundamentalGroup.map (subsetInclusion D.core) ⟨base, D.base_mem_core⟩

/-- The cusp-piece fundamental group, transported to the ambient base along its connector. -/
public def cuspFundamentalGroupMap (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup D.cusp ⟨D.cuspPoint, D.cuspPoint_mem.2⟩ →* FundamentalGroup Y base :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath D.cuspConnector.symm).toMonoidHom.comp
    (FundamentalGroup.map (subsetInclusion D.cusp) ⟨D.cuspPoint, D.cuspPoint_mem.2⟩)

/-- The order-three filling fundamental group, transported to the ambient base. -/
public def ellipticThreeFundamentalGroupMap (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup D.ellipticThree
        ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem.2⟩ →*
      FundamentalGroup Y base :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      D.ellipticThreeConnector.symm).toMonoidHom.comp
    (FundamentalGroup.map (subsetInclusion D.ellipticThree)
      ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem.2⟩)

/-- The order-four filling fundamental group, transported to the ambient base. -/
public def ellipticFourFundamentalGroupMap (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup D.ellipticFour
        ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem.2⟩ →*
      FundamentalGroup Y base :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      D.ellipticFourConnector.symm).toMonoidHom.comp
    (FundamentalGroup.map (subsetInclusion D.ellipticFour)
      ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem.2⟩)

/-- Inclusion of the cusp overlap into the cusp piece. -/
public def cuspOverlapToPiece (D : PaperVanKampenFourPieceCover base) :
    C((D.core ∩ D.cusp : Set Y), D.cusp) where
  toFun x := ⟨x, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Inclusion of the order-three overlap into its filling piece. -/
public def ellipticThreeOverlapToPiece (D : PaperVanKampenFourPieceCover base) :
    C((D.core ∩ D.ellipticThree : Set Y), D.ellipticThree) where
  toFun x := ⟨x, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Inclusion of the order-four overlap into its filling piece. -/
public def ellipticFourOverlapToPiece (D : PaperVanKampenFourPieceCover base) :
    C((D.core ∩ D.ellipticFour : Set Y), D.ellipticFour) where
  toFun x := ⟨x, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The map on fundamental groups from the cusp overlap to the cusp filling. -/
public def cuspOverlapFundamentalGroupMap (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup (D.core ∩ D.cusp : Set Y) ⟨D.cuspPoint, D.cuspPoint_mem⟩ →*
      FundamentalGroup D.cusp ⟨D.cuspPoint, D.cuspPoint_mem.2⟩ :=
  FundamentalGroup.map D.cuspOverlapToPiece ⟨D.cuspPoint, D.cuspPoint_mem⟩

/-- The map on fundamental groups from the order-three overlap to its filling. -/
public def ellipticThreeOverlapFundamentalGroupMap
    (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup (D.core ∩ D.ellipticThree : Set Y)
        ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem⟩ →*
      FundamentalGroup D.ellipticThree
        ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem.2⟩ :=
  FundamentalGroup.map D.ellipticThreeOverlapToPiece
    ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem⟩

/-- The map on fundamental groups from the order-four overlap to its filling. -/
public def ellipticFourOverlapFundamentalGroupMap
    (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup (D.core ∩ D.ellipticFour : Set Y)
        ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem⟩ →*
      FundamentalGroup D.ellipticFour
        ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem.2⟩ :=
  FundamentalGroup.map D.ellipticFourOverlapToPiece
    ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem⟩

/-- Basepoint transport along a path is natural in the space. -/
public theorem map_fundamentalGroupMulEquivOfPath {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {x₀ x₁ : A} (p : Path x₀ x₁) (γ : FundamentalGroup A x₀) :
    FundamentalGroup.map f x₁ (FundamentalGroup.fundamentalGroupMulEquivOfPath p γ) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)
        (FundamentalGroup.map f x₀ γ) := by
  show (FundamentalGroupoid.map f).map
      (((Groupoid.isoEquivHom _ _).symm (Path.Homotopic.Quotient.mk p)).conj γ) = _
  show (FundamentalGroupoid.map f).map _ = _
  simp only [Iso.conj_apply, Groupoid.isoEquivHom_symm_apply_inv,
    Groupoid.isoEquivHom_symm_apply_hom, Functor.map_comp]
  show _ = ((Groupoid.isoEquivHom _ _).symm
      (Path.Homotopic.Quotient.mk (p.map f.continuous))).conj
      ((FundamentalGroupoid.map f).map γ)
  simp only [Iso.conj_apply, Groupoid.isoEquivHom_symm_apply_inv,
    Groupoid.isoEquivHom_symm_apply_hom]
  congr 1
  rw [Functor.map_inv]
  exact (Groupoid.inv_eq_inv _).symm

/-- Functoriality of the induced map on fundamental groups. -/
public theorem map_map {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C)) (x : A) (γ : FundamentalGroup A x) :
    FundamentalGroup.map g (f x) (FundamentalGroup.map f x γ) =
      FundamentalGroup.map (g.comp f) x γ :=
  (Path.Homotopic.Quotient.map_comp (p := γ) (f := f) (g := g)).symm

/-- Inclusion of an overlap into the core. -/
public def overlapToCore (D : PaperVanKampenFourPieceCover base) (P : Set Y) :
    C((D.core ∩ P : Set Y), D.core) where
  toFun x := ⟨x, x.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- A connector that stays in the core, viewed as a path in the core. -/
public def connectorInCore (D : PaperVanKampenFourPieceCover base) {pt : Y}
    (conn : Path base pt) (hconn : ∀ t, conn t ∈ D.core) (hpt : pt ∈ D.core) :
    Path (⟨base, D.base_mem_core⟩ : D.core) ⟨pt, hpt⟩ where
  toFun t := ⟨conn t, hconn t⟩
  continuous_toFun := conn.continuous.subtype_mk _
  source' := by simp
  target' := by simp

/-- Loops of a piece that come from its overlap with the core, transported to the base point along
a connector inside the core, already lie in the image of the core. -/
public theorem transport_mem_range_core (D : PaperVanKampenFourPieceCover base) {P : Set Y} {pt : Y}
    (hpt : pt ∈ D.core ∩ P) (conn : Path base pt) (hconn : ∀ t, conn t ∈ D.core)
    (y : FundamentalGroup (D.core ∩ P : Set Y) ⟨pt, hpt⟩) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath conn.symm)
        (FundamentalGroup.map (subsetInclusion P) ⟨pt, hpt.2⟩
          (FundamentalGroup.map
            (⟨fun z : (D.core ∩ P : Set Y) ↦ (⟨z, z.2.2⟩ : P), by fun_prop⟩ :
              C((D.core ∩ P : Set Y), P)) ⟨pt, hpt⟩ y)) ∈
      D.coreFundamentalGroupMap.range := by
  classical
  set connCore : Path (⟨base, D.base_mem_core⟩ : D.core) ⟨pt, hpt.1⟩ :=
    D.connectorInCore conn hconn hpt.1 with hconnCore
  refine ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPath connCore.symm)
    (FundamentalGroup.map (D.overlapToCore P) ⟨pt, hpt⟩ y), ?_⟩
  have hnat := map_fundamentalGroupMulEquivOfPath (subsetInclusion D.core) connCore.symm
    (FundamentalGroup.map (D.overlapToCore P) ⟨pt, hpt⟩ y)
  have hpath : (connCore.symm.map (subsetInclusion D.core).continuous) = conn.symm := by
    ext t
    rfl
  show FundamentalGroup.map (subsetInclusion D.core) _
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath connCore.symm) _) = _
  rw [hnat, hpath]
  congr 1
  have h1 : FundamentalGroup.map (subsetInclusion D.core) ⟨pt, hpt.1⟩
      (FundamentalGroup.map (D.overlapToCore P) ⟨pt, hpt⟩ y)
      = FundamentalGroup.map ((subsetInclusion D.core).comp (D.overlapToCore P)) ⟨pt, hpt⟩ y :=
    map_map _ _ _ _
  have h2 : FundamentalGroup.map (subsetInclusion P) ⟨pt, hpt.2⟩
      (FundamentalGroup.map
        (⟨fun z : (D.core ∩ P : Set Y) ↦ (⟨z, z.2.2⟩ : P), by fun_prop⟩ :
          C((D.core ∩ P : Set Y), P)) ⟨pt, hpt⟩ y)
      = FundamentalGroup.map ((subsetInclusion P).comp
          ⟨fun z : (D.core ∩ P : Set Y) ↦ (⟨z, z.2.2⟩ : P), by fun_prop⟩) ⟨pt, hpt⟩ y :=
    map_map _ _ _ _
  rw [h1, h2]
  congr 1

/-! ## Van Kampen generation via the covering attached to `H`

A subgroup containing the images of the four local fundamental groups is everything. The proof is
the classical covering-space one rather than a path subdivision: for a locally nice ambient space
the subgroup `H` is realised by a covering `q : Q → Y` whose recovered subgroup is exactly `H`, the
hypotheses let each of the four pieces be lifted through `q`, the four lifts agree on the overlaps
because those are path-connected, and the glued section forces `q_*` to be onto, i.e. `H = ⊤`.
-/

/-- Transport along a path and along its reverse are mutually inverse. -/
public theorem transport_symm_transport {x₀ x₁ : Y} (τ : Path x₀ x₁) (γ : FundamentalGroup Y x₁) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath τ)
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath τ.symm) γ) = γ := by
  have hiso : ((Groupoid.isoEquivHom (FundamentalGroupoid.mk x₁) (FundamentalGroupoid.mk x₀)).symm
        (Path.Homotopic.Quotient.mk τ.symm)) =
      ((Groupoid.isoEquivHom (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.mk x₁)).symm
        (Path.Homotopic.Quotient.mk τ)).symm := by
    apply Iso.ext
    rfl
  show ((Groupoid.isoEquivHom (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.mk x₁)).symm
      (Path.Homotopic.Quotient.mk τ)).conj
      (((Groupoid.isoEquivHom (FundamentalGroupoid.mk x₁) (FundamentalGroupoid.mk x₀)).symm
        (Path.Homotopic.Quotient.mk τ.symm)).conj γ) = γ
  rw [hiso]
  exact Iso.self_symm_conj _ _

/-- Changing the base lift along a path in the total space conjugates the recovered subgroup. -/
public theorem range_map_le_of_path {Q : Type*} [TopologicalSpace Q] (q : C(Q, Y))
    {e₀ e₁ : Q} (σ : Path e₀ e₁) (γ : FundamentalGroup Y (q e₁))
    (hγ : (FundamentalGroup.fundamentalGroupMulEquivOfPath (σ.map q.continuous)).symm γ ∈
      (FundamentalGroup.map q e₀).range) :
    γ ∈ (FundamentalGroup.map q e₁).range := by
  obtain ⟨δ, hδ⟩ := hγ
  refine ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPath σ) δ, ?_⟩
  rw [map_fundamentalGroupMulEquivOfPath, hδ]
  exact (FundamentalGroup.fundamentalGroupMulEquivOfPath (σ.map q.continuous)).apply_symm_apply γ

section Covering

variable [LocallyPathConnectedSpace Y] [PathConnectedSpace Y]
  [SemilocallySimplyConnectedSpace Y] (D : PaperVanKampenFourPieceCover base)

/-- A lift of a piece inclusion into the covering attached to `H`. -/
public theorem exists_lift (H : Subgroup (FundamentalGroup Y base)) {P : Set Y} (hPopen : IsOpen P)
    (hP : IsPathConnected P) {pt : Y} (hpt : pt ∈ P)
    (f₀ : SubgroupQuotient base H) (hf₀ : subgroupQuotientProj base H f₀ = pt)
    (hle : (FundamentalGroup.map (subsetInclusion P) (⟨pt, hpt⟩ : P)).range ≤
      (FundamentalGroup.mapOfEq
        (⟨subgroupQuotientProj base H, continuous_subgroupQuotientProj base H⟩ :
          C(SubgroupQuotient base H, Y)) hf₀).range) :
    ∃ g : C(P, SubgroupQuotient base H), g ⟨pt, hpt⟩ = f₀ ∧
      ∀ z : P, subgroupQuotientProj base H (g z) = z := by
  have _ : PathConnectedSpace P := isPathConnected_iff_pathConnectedSpace.mp hP
  have _ : LocallyPathConnectedSpace P := hPopen.locallyPathConnectedSpace
  obtain ⟨g, ⟨hg₀, hgcomp⟩, -⟩ :=
    IsCoveringMap.existsUnique_continuousMap_comp_eq_of_range_le
      (p := (subsetInclusion P : C(P, Y))) (q := subgroupQuotientProj base H)
      (e₀ := (⟨pt, hpt⟩ : P)) (f₀ := f₀) (x := pt)
      (subsetInclusion P).continuous (isCoveringMap_subgroupQuotientProj base H) rfl hf₀
      (by
        have h := hle
        rw [← TauCeti.FundamentalGroup.mapOfEq_rfl (x := (⟨pt, hpt⟩ : P))
          (subsetInclusion P)] at h
        exact h)
  exact ⟨g, hg₀, fun z => congrFun hgcomp z⟩

/-- Transporting the base lift along a path moves the recovered subgroup accordingly. -/
public theorem mem_range_mapOfEq_of_path {Q : Type*} [TopologicalSpace Q] (q : C(Q, Y))
    {e₀ e₁ : Q} (σ : Path e₀ e₁) {y₀ y₁ : Y} (h₀ : q e₀ = y₀) (h₁ : q e₁ = y₁)
    (τ : Path y₀ y₁) (hτ : ∀ t, τ t = q (σ t)) (γ : FundamentalGroup Y y₁)
    (hγ : (FundamentalGroup.fundamentalGroupMulEquivOfPath τ.symm) γ ∈
      (FundamentalGroup.mapOfEq q h₀).range) :
    γ ∈ (FundamentalGroup.mapOfEq q h₁).range := by
  subst h₀
  subst h₁
  rw [TauCeti.FundamentalGroup.mapOfEq_rfl] at hγ ⊢
  have hpath : σ.map q.continuous = τ := by
    ext t
    exact (hτ t).symm
  refine range_map_le_of_path q σ γ ?_
  rw [hpath]
  obtain ⟨δ, hδ⟩ := hγ
  refine ⟨δ, ?_⟩
  rw [hδ]
  exact (((FundamentalGroup.fundamentalGroupMulEquivOfPath τ).symm_apply_eq).mpr
    (transport_symm_transport τ γ).symm).symm

/-- The four pieces of the cover, indexed. -/
public def piece (D : PaperVanKampenFourPieceCover base) : Fin 4 → Set Y
  | 0 => D.core
  | 1 => D.cusp
  | 2 => D.ellipticThree
  | 3 => D.ellipticFour

public theorem isOpen_piece (D : PaperVanKampenFourPieceCover base) (i : Fin 4) :
    IsOpen (D.piece i) := by
  fin_cases i
  exacts [D.core_isOpen, D.cusp_isOpen, D.ellipticThree_isOpen, D.ellipticFour_isOpen]

public theorem piece_covers (D : PaperVanKampenFourPieceCover base) (y : Y) :
    ∃ i, D.piece i ∈ nhds y := by
  have hy : y ∈ D.core ∪ D.cusp ∪ D.ellipticThree ∪ D.ellipticFour := by
    rw [D.covers]; trivial
  rcases hy with ((hy | hy) | hy) | hy
  · exact ⟨0, (D.core_isOpen).mem_nhds hy⟩
  · exact ⟨1, (D.cusp_isOpen).mem_nhds hy⟩
  · exact ⟨2, (D.ellipticThree_isOpen).mem_nhds hy⟩
  · exact ⟨3, (D.ellipticFour_isOpen).mem_nhds hy⟩

/-- The filling lifts agree with the core lift on the overlap. -/
public theorem lift_agree {Q : Type*} [TopologicalSpace Q] (q : C(Q, Y))
    (hq : IsCoveringMap q) {P : Set Y} (hP : IsPathConnected (D.core ∩ P))
    (sCore : C(D.core, Q)) (sP : C(P, Q))
    (hsCore : ∀ z : D.core, q (sCore z) = z) (hsP : ∀ z : P, q (sP z) = z)
    {pt : Y} (hpt : pt ∈ D.core ∩ P)
    (hagree : sCore ⟨pt, hpt.1⟩ = sP ⟨pt, hpt.2⟩)
    (x : Y) (hx : x ∈ D.core ∩ P) :
    sCore ⟨x, hx.1⟩ = sP ⟨x, hx.2⟩ := by
  have _ : PathConnectedSpace (D.core ∩ P : Set Y) :=
    isPathConnected_iff_pathConnectedSpace.mp hP
  set g₁ : (D.core ∩ P : Set Y) → Q := fun z => sCore ⟨z, z.2.1⟩ with hg₁
  set g₂ : (D.core ∩ P : Set Y) → Q := fun z => sP ⟨z, z.2.2⟩ with hg₂
  have hcont₁ : Continuous g₁ := sCore.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hcont₂ : Continuous g₂ := sP.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hcomp : q ∘ g₁ = q ∘ g₂ := by
    funext z
    simp only [Function.comp_apply, hg₁, hg₂, hsCore, hsP]
  have := hq.eq_of_comp_eq hcont₁ hcont₂ hcomp ⟨pt, hpt⟩ hagree
  exact congrFun this ⟨x, hx⟩

/-- The identity induces the identity on the fundamental group, so its image is everything. -/
public theorem range_map_id : (FundamentalGroup.map (ContinuousMap.id Y) base).range = ⊤ := by
  rw [MonoidHom.range_eq_top]
  intro γ
  refine ⟨γ, ?_⟩
  show Path.Homotopic.Quotient.map γ (ContinuousMap.id Y) = γ
  induction γ using Quotient.ind with
  | _ g =>
    apply Path.Homotopic.Quotient.eq.mpr
    exact ⟨Path.Homotopy.refl _⟩

/-- A filling lift agreeing with the core lift at the connector's endpoint. -/
public theorem exists_filling_lift (H : Subgroup (FundamentalGroup Y base))
    (sCore : C(D.core, SubgroupQuotient base H))
    (hsCoreBase : sCore ⟨base, D.base_mem_core⟩ = SubgroupQuotient.basepoint base H)
    (hsCore : ∀ z : D.core, subgroupQuotientProj base H (sCore z) = z)
    {hbase : (⟨subgroupQuotientProj base H, continuous_subgroupQuotientProj base H⟩ :
        C(SubgroupQuotient base H, Y)) (SubgroupQuotient.basepoint base H) = base}
    (hH : (FundamentalGroup.mapOfEq
      (⟨subgroupQuotientProj base H, continuous_subgroupQuotientProj base H⟩ :
        C(SubgroupQuotient base H, Y)) hbase).range = H)
    {P : Set Y} (hPopen : IsOpen P) (hP : IsPathConnected P) {pt : Y} (hpt : pt ∈ D.core ∩ P)
    (conn : Path base pt) (hconn : ∀ t, conn t ∈ D.core)
    (hle : ((FundamentalGroup.fundamentalGroupMulEquivOfPath conn.symm).toMonoidHom.comp
        (FundamentalGroup.map (subsetInclusion P) (⟨pt, hpt.2⟩ : P))).range ≤ H) :
    ∃ g : C(P, SubgroupQuotient base H), g ⟨pt, hpt.2⟩ = sCore ⟨pt, hpt.1⟩ ∧
      ∀ z : P, subgroupQuotientProj base H (g z) = z := by
  refine exists_lift H hPopen hP hpt.2 (sCore ⟨pt, hpt.1⟩) (hsCore ⟨pt, hpt.1⟩) ?_
  rintro γ ⟨x, rfl⟩
  refine mem_range_mapOfEq_of_path
    (⟨subgroupQuotientProj base H, continuous_subgroupQuotientProj base H⟩ :
      C(SubgroupQuotient base H, Y))
    (((D.connectorInCore conn hconn hpt.1).map sCore.continuous).cast hsCoreBase.symm rfl)
    hbase (hsCore ⟨pt, hpt.1⟩) conn ?_ _ ?_
  · intro t
    exact (hsCore ⟨conn t, hconn t⟩).symm
  · rw [hH]
    exact hle ⟨x, rfl⟩

/-- Van Kampen generation for the paper's four-piece star, for a locally nice ambient space. -/
public theorem localFundamentalGroupImages_generate'
    (H : Subgroup (FundamentalGroup Y base))
    (hcore : D.coreFundamentalGroupMap.range ≤ H)
    (hcusp : D.cuspFundamentalGroupMap.range ≤ H)
    (hthree : D.ellipticThreeFundamentalGroupMap.range ≤ H)
    (hfour : D.ellipticFourFundamentalGroupMap.range ≤ H) :
    H = ⊤ := by
  classical
  set q : C(SubgroupQuotient base H, Y) :=
    ⟨subgroupQuotientProj base H, continuous_subgroupQuotientProj base H⟩ with hqdef
  have hq : IsCoveringMap (subgroupQuotientProj base H) :=
    isCoveringMap_subgroupQuotientProj base H
  have hbase : subgroupQuotientProj base H (SubgroupQuotient.basepoint base H) = base :=
    subgroupQuotientProj_basepoint base H
  have hrange : (FundamentalGroup.mapOfEq q hbase).range = H :=
    range_mapOfEq_subgroupQuotientProj base H
  -- the lift over the core
  obtain ⟨sCore, hsCoreBase, hsCore⟩ :=
    exists_lift H D.core_isOpen D.core_pathConnected D.base_mem_core
      (SubgroupQuotient.basepoint base H) hbase (by rw [hrange]; exact hcore)
  obtain ⟨sCusp, hsCuspPt, hsCusp⟩ :=
    exists_filling_lift D H sCore hsCoreBase hsCore hrange D.cusp_isOpen D.cusp_pathConnected
      D.cuspPoint_mem D.cuspConnector D.cuspConnector_mem hcusp
  obtain ⟨sThree, hsThreePt, hsThree⟩ :=
    exists_filling_lift D H sCore hsCoreBase hsCore hrange D.ellipticThree_isOpen
      D.ellipticThree_pathConnected D.ellipticThreePoint_mem D.ellipticThreeConnector
      D.ellipticThreeConnector_mem hthree
  obtain ⟨sFour, hsFourPt, hsFour⟩ :=
    exists_filling_lift D H sCore hsCoreBase hsCore hrange D.ellipticFour_isOpen
      D.ellipticFour_pathConnected D.ellipticFourPoint_mem D.ellipticFourConnector
      D.ellipticFourConnector_mem hfour
  set φ : ∀ i : Fin 4, C(D.piece i, SubgroupQuotient base H) := fun i =>
    match i with
    | 0 => sCore
    | 1 => sCusp
    | 2 => sThree
    | 3 => sFour
    with hφdef
  have hsec : ∀ (i : Fin 4) (z : D.piece i),
      subgroupQuotientProj base H (φ i z) = z := by
    intro i z
    fin_cases i
    exacts [hsCore z, hsCusp z, hsThree z, hsFour z]
  have hφ : ∀ (i j : Fin 4) (x : Y) (hxi : x ∈ D.piece i) (hxj : x ∈ D.piece j),
      φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩ := by
    have hAgreeCusp : ∀ (z : Y) (hz : z ∈ D.core ∩ D.cusp),
        sCore ⟨z, hz.1⟩ = sCusp ⟨z, hz.2⟩ := fun z hz =>
      lift_agree D q hq D.cusp_overlap_pathConnected sCore sCusp hsCore hsCusp
        D.cuspPoint_mem hsCuspPt.symm z hz
    have hAgreeThree : ∀ (z : Y) (hz : z ∈ D.core ∩ D.ellipticThree),
        sCore ⟨z, hz.1⟩ = sThree ⟨z, hz.2⟩ := fun z hz =>
      lift_agree D q hq D.ellipticThree_overlap_pathConnected sCore sThree hsCore hsThree
        D.ellipticThreePoint_mem hsThreePt.symm z hz
    have hAgreeFour : ∀ (z : Y) (hz : z ∈ D.core ∩ D.ellipticFour),
        sCore ⟨z, hz.1⟩ = sFour ⟨z, hz.2⟩ := fun z hz =>
      lift_agree D q hq D.ellipticFour_overlap_pathConnected sCore sFour hsCore hsFour
        D.ellipticFourPoint_mem hsFourPt.symm z hz
    intro i j x hxi hxj
    fin_cases i <;> fin_cases j
    · rfl
    · exact hAgreeCusp x ⟨hxi, hxj⟩
    · exact hAgreeThree x ⟨hxi, hxj⟩
    · exact hAgreeFour x ⟨hxi, hxj⟩
    · exact (hAgreeCusp x ⟨hxj, hxi⟩).symm
    · rfl
    · exact absurd hxj (Set.disjoint_left.mp D.cusp_disjoint_ellipticThree hxi)
    · exact absurd hxj (Set.disjoint_left.mp D.cusp_disjoint_ellipticFour hxi)
    · exact (hAgreeThree x ⟨hxj, hxi⟩).symm
    · exact absurd hxi (Set.disjoint_left.mp D.cusp_disjoint_ellipticThree hxj)
    · rfl
    · exact absurd hxj (Set.disjoint_left.mp D.ellipticThree_disjoint_ellipticFour hxi)
    · exact (hAgreeFour x ⟨hxj, hxi⟩).symm
    · exact absurd hxi (Set.disjoint_left.mp D.cusp_disjoint_ellipticFour hxj)
    · exact absurd hxi (Set.disjoint_left.mp D.ellipticThree_disjoint_ellipticFour hxj)
    · rfl
  set sec : C(Y, SubgroupQuotient base H) :=
    ContinuousMap.liftCover D.piece φ hφ D.piece_covers with hsecdef
  have hsecComp : ∀ x : Y, subgroupQuotientProj base H (sec x) = x := by
    intro x
    obtain ⟨i, hi⟩ := D.piece_covers x
    have hx : x ∈ D.piece i := mem_of_mem_nhds hi
    have hval : sec x = φ i ⟨x, hx⟩ :=
      ContinuousMap.liftCover_coe (S := D.piece) (φ := φ) (hφ := hφ) (hS := D.piece_covers)
        (i := i) ⟨x, hx⟩
    rw [hval]
    exact hsec i ⟨x, hx⟩
  have hsecBase : sec base = SubgroupQuotient.basepoint base H := by
    have hx : base ∈ D.piece 0 := D.base_mem_core
    have hval : sec base = φ 0 ⟨base, hx⟩ :=
      ContinuousMap.liftCover_coe (S := D.piece) (φ := φ) (hφ := hφ) (hS := D.piece_covers)
        (i := 0) ⟨base, hx⟩
    rw [hval]
    exact hsCoreBase
  have hiff := IsCoveringMap.exists_continuousMap_comp_eq_iff_range_le
      (p := (id : Y → Y)) (q := subgroupQuotientProj base H) (e₀ := base)
      (f₀ := SubgroupQuotient.basepoint base H) continuous_id hq rfl hbase
  have hle : (FundamentalGroup.mapOfEq (⟨id, continuous_id⟩ : C(Y, Y)) rfl).range ≤
      (FundamentalGroup.mapOfEq
        (⟨subgroupQuotientProj base H, continuous_subgroupQuotientProj base H⟩ :
          C(SubgroupQuotient base H, Y)) hbase).range :=
    hiff.mp ⟨sec, hsecBase, funext hsecComp⟩
  rw [TauCeti.FundamentalGroup.mapOfEq_rfl] at hle
  have htop : (FundamentalGroup.map (⟨id, continuous_id⟩ : C(Y, Y)) base).range = ⊤ :=
    range_map_id
  rw [htop] at hle
  exact top_le_iff.mp (le_trans hle (le_of_eq hrange))

/-- A subgroup containing the images of the four local fundamental groups is the whole ambient
fundamental group. This is the based-group generator consequence of groupoid van Kampen. -/
public theorem localFundamentalGroupImages_generate
    (H : Subgroup (FundamentalGroup Y base))
    (hcore : D.coreFundamentalGroupMap.range ≤ H)
    (hcusp : D.cuspFundamentalGroupMap.range ≤ H)
    (hthree : D.ellipticThreeFundamentalGroupMap.range ≤ H)
    (hfour : D.ellipticFourFundamentalGroupMap.range ≤ H) :
    H = ⊤ :=
  D.localFundamentalGroupImages_generate' H hcore hcusp hthree hfour

end Covering

/-- If every filling fundamental group is generated by its overlap with the core, the core
inclusion surjects on the fundamental group of the four-piece star.

This is a consequence of the van Kampen generation statement above rather than a separate input:
the overlap loops, and the connectors used to move them to the base point, all lie in the core, so
each filling's image is already contained in the image of the core. -/
public theorem coreFundamentalGroupMap_surjective_of_overlap_surjective
    [LocallyPathConnectedSpace Y] [PathConnectedSpace Y] [SemilocallySimplyConnectedSpace Y]
    (D : PaperVanKampenFourPieceCover base)
    (hcusp : Function.Surjective D.cuspOverlapFundamentalGroupMap)
    (hthree : Function.Surjective D.ellipticThreeOverlapFundamentalGroupMap)
    (hfour : Function.Surjective D.ellipticFourOverlapFundamentalGroupMap) :
    Function.Surjective D.coreFundamentalGroupMap := by
  rw [← MonoidHom.range_eq_top]
  refine localFundamentalGroupImages_generate D _ le_rfl ?_ ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hcusp x
    exact D.transport_mem_range_core D.cuspPoint_mem D.cuspConnector D.cuspConnector_mem y
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hthree x
    exact D.transport_mem_range_core D.ellipticThreePoint_mem D.ellipticThreeConnector
      D.ellipticThreeConnector_mem y
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hfour x
    exact D.transport_mem_range_core D.ellipticFourPoint_mem D.ellipticFourConnector
      D.ellipticFourConnector_mem y

end PaperVanKampenFourPieceCover
end SphereSixComplex.Topology

end
