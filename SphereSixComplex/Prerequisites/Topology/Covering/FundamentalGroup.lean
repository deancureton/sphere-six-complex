module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Existence
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.RecoveredSubgroup
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed

@[expose] public section
noncomputable section
open Set Topology CategoryTheory TauCeti TauCeti.UniversalCover
open scoped ContinuousMap
namespace SphereSixComplex.CoveringSpace
variable {Y : Type*} [TopologicalSpace Y] {base : Y}

/-- Inclusion of a subspace into its ambient space. -/
public def subsetInclusion (U : Set Y) : C(U, Y) :=
  ⟨Subtype.val, continuous_subtype_val⟩

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

variable [LocallyPathConnectedSpace Y] [PathConnectedSpace Y]
  [SemilocallySimplyConnectedSpace Y]

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

end SphereSixComplex.CoveringSpace
end
end
