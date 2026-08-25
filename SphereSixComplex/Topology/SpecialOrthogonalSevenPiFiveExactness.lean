module

public import SphereSixComplex.Topology.SpecialOrthogonalSevenRelativeTransport
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# Exactness at `π₅(SO(7))` for the first-column Stiefel sequence

This file packages the maps on fifth homotopy groups induced by
`SO(6) → SO(7) → S⁶` and proves exactness at the middle term.  The easy inclusion follows from
the constant composite.  For the reverse inclusion, the relative five-cube transport theorem
deforms a representative into the standard fiber, which is identified explicitly with `SO(6)`.
-/

@[expose] public section

noncomputable section

open ContinuousMap Matrix Set Topology
open scoped Classical MatrixGroups RealInnerProductSpace Topology Topology.Homotopy unitInterval

namespace SphereSixComplex.SpecialOrthogonalSevenStiefel

@[simp] public theorem stabilize_one : stabilize (1 : SO6) = (1 : SO7) := by
  apply Subtype.ext
  change Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0
        (1 : Matrix (Fin 6) (Fin 6) ℝ)) = 1
  rw [Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

@[simp] public theorem stabilizeMap_one : stabilizeMap (1 : SO6) = (1 : SO7) :=
  stabilize_one

@[simp] public theorem firstColumnMap_one :
    firstColumnMap (1 : SO7) = firstColumn (1 : SO7) := rfl

/-- Stabilization on fifth homotopy groups. -/
public def stabilizePiFive :
    HomotopyGroup.Pi 5 SO6 (1 : SO6) →*
      HomotopyGroup.Pi 5 SO7 (1 : SO7) :=
  HomotopyGroup.mapHom stabilizeMap stabilizeMap_one

/-- The map on fifth homotopy groups induced by the first-column projection. -/
public def firstColumnPiFive :
    HomotopyGroup.Pi 5 SO7 (1 : SO7) →*
      HomotopyGroup.Pi 5 Sphere6 (firstColumn (1 : SO7)) :=
  HomotopyGroup.mapHom firstColumnMap firstColumnMap_one

public theorem firstColumnMap_comp_stabilizeMap :
    firstColumnMap.comp stabilizeMap =
      ContinuousMap.const SO6 (firstColumn (1 : SO7)) := by
  apply ContinuousMap.ext
  intro Q
  exact firstColumn_stabilize Q

public theorem firstColumnPiFive_stabilizePiFive
    (a : HomotopyGroup.Pi 5 SO6 (1 : SO6)) :
    firstColumnPiFive (stabilizePiFive a) = 1 := by
  change HomotopyGroup.map firstColumnMap firstColumnMap_one
      (HomotopyGroup.map stabilizeMap stabilizeMap_one a) = 1
  rw [HomotopyGroup.map_comp_apply]
  rw [HomotopyGroup.map_congr firstColumnMap_comp_stabilizeMap]
  exact HomotopyGroup.map_continuousMap_const_apply_eq_one
    (N := Fin 5) (x := (1 : SO6)) (firstColumn (1 : SO7)) rfl a

public theorem range_stabilizePiFive_le_ker_firstColumnPiFive :
    Set.range stabilizePiFive ⊆ {a | firstColumnPiFive a = 1} := by
  rintro _ ⟨a, rfl⟩
  exact firstColumnPiFive_stabilizePiFive a

/-- A representative whose first-column loop is nullhomotopic can be deformed into the standard
fiber and hence comes from `SO(6)`. -/
public theorem exists_stabilized_representative
    (f : Ω^ (Fin 5) SO7 (1 : SO7))
    (hf : GenLoop.Homotopic (GenLoop.map firstColumnMap firstColumnMap_one f)
      (_root_.GenLoop.const : Ω^ (Fin 5) Sphere6 (firstColumn (1 : SO7)))) :
    ∃ g : Ω^ (Fin 5) SO6 (1 : SO6),
      GenLoop.Homotopic f (GenLoop.map stabilizeMap stabilizeMap_one g) := by
  let b₀ : C(Cube5, Sphere6) :=
    (GenLoop.map firstColumnMap firstColumnMap_one f).1
  let b₁ : C(Cube5, Sphere6) :=
    (_root_.GenLoop.const : Ω^ (Fin 5) Sphere6 (firstColumn (1 : SO7))).1
  obtain ⟨e₁, he₁, hfe₁⟩ := fiveCubeStiefelRelativeTransport hf f.1 rfl
  let K := hfe₁.some
  let e₁Fiber : C(Cube5, StandardFiber) :=
    ⟨fun x ↦ ⟨e₁ x, ContinuousMap.congr_fun he₁ x⟩,
      continuous_induced_rng.mpr e₁.continuous⟩
  let gMap : C(Cube5, SO6) :=
    ⟨fun x ↦ lowerSpecialOrthogonal (e₁Fiber x),
      continuous_lowerSpecialOrthogonal.comp e₁Fiber.continuous⟩
  have he₁_boundary (x : Cube5) (hx : x ∈ Cube.boundary (Fin 5)) :
      e₁ x = (1 : SO7) := by
    calc
      e₁ x = K ((1 : I), x) := (K.apply_one x).symm
      _ = f x := K.eq_fst 1 hx
      _ = 1 := _root_.GenLoop.boundary f x hx
  have hstabilize_gMap (x : Cube5) : stabilize (gMap x) = e₁ x := by
    exact congr_arg Subtype.val
      (stabilizeFiber_lowerSpecialOrthogonal (e₁Fiber x))
  let g : Ω^ (Fin 5) SO6 (1 : SO6) := ⟨gMap, by
    intro x hx
    apply stabilizeFiber_injective
    apply Subtype.ext
    change stabilize (gMap x) = stabilize (1 : SO6)
    rw [hstabilize_gMap x, he₁_boundary x hx, stabilize_one]⟩
  let e₁Loop : Ω^ (Fin 5) SO7 (1 : SO7) :=
    ⟨e₁, he₁_boundary⟩
  have hmap : GenLoop.map stabilizeMap stabilizeMap_one g = e₁Loop := by
    apply _root_.GenLoop.ext
    intro x
    exact hstabilize_gMap x
  refine ⟨g, ?_⟩
  rw [hmap]
  exact ⟨K⟩

public theorem ker_firstColumnPiFive_le_range_stabilizePiFive :
    {a | firstColumnPiFive a = 1} ⊆ Set.range stabilizePiFive := by
  intro a ha
  induction a using Quotient.inductionOn with
  | h f =>
      have hmap_mk : firstColumnPiFive (⟦f⟧ :
          HomotopyGroup.Pi 5 SO7 (1 : SO7)) =
          (⟦GenLoop.map firstColumnMap firstColumnMap_one f⟧ :
            HomotopyGroup.Pi 5 Sphere6 (firstColumn (1 : SO7))) := rfl
      have ha' : (⟦GenLoop.map firstColumnMap firstColumnMap_one f⟧ :
          HomotopyGroup.Pi 5 Sphere6 (firstColumn (1 : SO7))) =
          ⟦(_root_.GenLoop.const :
            Ω^ (Fin 5) Sphere6 (firstColumn (1 : SO7)))⟧ :=
        (hmap_mk.symm.trans ha).trans _root_.HomotopyGroup.one_def
      have hrel : GenLoop.Homotopic
          (GenLoop.map firstColumnMap firstColumnMap_one f)
          (_root_.GenLoop.const :
            Ω^ (Fin 5) Sphere6 (firstColumn (1 : SO7))) :=
        Quotient.exact ha'
      obtain ⟨g, hfg⟩ := exists_stabilized_representative f hrel
      refine ⟨⟦g⟧, ?_⟩
      exact Quotient.sound hfg.symm

public theorem range_stabilizePiFive_eq_ker_firstColumnPiFive :
    Set.range stabilizePiFive = {a | firstColumnPiFive a = 1} :=
  Set.Subset.antisymm range_stabilizePiFive_le_ker_firstColumnPiFive
    ker_firstColumnPiFive_le_range_stabilizePiFive

/-- Exactness at `π₅(SO(7))` for the first-column Stiefel sequence. -/
public theorem stabilizePiFive_range_eq_firstColumnPiFive_ker :
    stabilizePiFive.range = firstColumnPiFive.ker := by
  ext a
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  exact Set.ext_iff.mp range_stabilizePiFive_eq_ker_firstColumnPiFive a

end SphereSixComplex.SpecialOrthogonalSevenStiefel
