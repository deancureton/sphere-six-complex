module

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyConnecting
public import DifferentialGeometry.Topology.Homology.SmallChains.Union
public import DifferentialGeometry.Topology.Homology.SmallChains.QuasiIso

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial
noncomputable section
universe u
namespace DifferentialGeometry.Homology

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)
  (X : TopCat.{u}) (s t : Set X)

theorem MayerVietoris.twoSetFamily_open (hs : IsOpen s) (ht : IsOpen t) :
    ∀ b, IsOpen (twoSetFamily X s t b) := by
  intro b
  cases b
  · exact ht
  · exact hs

theorem MayerVietoris.twoSetFamily_cover (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) :
    ∀ x : X, ∃ b, x ∈ twoSetFamily X s t b := by
  intro x
  rcases hcover x with h | h
  · exact ⟨true, h⟩
  · exact ⟨false, h⟩

def singularMayerVietorisConnectingMap
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex R).homology (n + 1) ⟶
      ((TopCat.toSSet.obj (TopCat.of (s ∩ t : Set X))).chainComplex R).homology n :=
  (smallChainHomologyIso X (twoSetFamily X s t) R
    (MayerVietoris.twoSetFamily_open X s t hs ht) (MayerVietoris.twoSetFamily_cover X s t hcover) (n + 1)).inv ≫
      (subspaceSmallShortExact X s t R).δ (n + 1) n (by simp)

@[simp]
theorem small_inclusion_singularMayerVietorisConnectingMap
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    HomologicalComplex.homologyMap (smallChainMap X (twoSetFamily X s t) R) (n + 1) ≫
      singularMayerVietorisConnectingMap R X s t hs ht hcover n =
      (subspaceSmallShortExact X s t R).δ (n + 1) n (by simp) := by
  change (smallChainHomologyIso X (twoSetFamily X s t) R
      (MayerVietoris.twoSetFamily_open X s t hs ht) (MayerVietoris.twoSetFamily_cover X s t hcover) (n + 1)).hom ≫
    ((smallChainHomologyIso X (twoSetFamily X s t) R
      (MayerVietoris.twoSetFamily_open X s t hs ht) (MayerVietoris.twoSetFamily_cover X s t hcover) (n + 1)).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc]

private theorem chain_biprod_component_ext
    {K L : ChainComplex (ModuleCat.{u} k) ℕ} (n : ℕ) (z w : (K ⊞ L).X n)
    (hfst : (biprod.fst : K ⊞ L ⟶ K).f n z = (biprod.fst : K ⊞ L ⟶ K).f n w)
    (hsnd : (biprod.snd : K ⊞ L ⟶ L).f n z = (biprod.snd : K ⊞ L ⟶ L).f n w) :
    z = w := by
  have hz := congrArg (fun f : (K ⊞ L).X n ⟶ (K ⊞ L).X n => f z)
    (HomologicalComplex.biprod_total_f K L n)
  have hw := congrArg (fun f : (K ⊞ L).X n ⟶ (K ⊞ L).X n => f w)
    (HomologicalComplex.biprod_total_f K L n)
  change (biprod.inl : K ⟶ K ⊞ L).f n ((biprod.fst : K ⊞ L ⟶ K).f n z) +
    (biprod.inr : L ⟶ K ⊞ L).f n ((biprod.snd : K ⊞ L ⟶ L).f n z) = z at hz
  change (biprod.inl : K ⟶ K ⊞ L).f n ((biprod.fst : K ⊞ L ⟶ K).f n w) +
    (biprod.inr : L ⟶ K ⊞ L).f n ((biprod.snd : K ⊞ L ⟶ L).f n w) = w at hw
  rw [hfst, hsnd] at hz
  exact hz.symm.trans hw

theorem singularMayerVietorisConnectingMap_representative
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ)
    (c : LinearMap.ker ((subspaceSmallShortComplex X s t R).X₃.sc (n + 1)).g.hom)
    (a : ((TopCat.toSSet.obj (TopCat.of s)).chainComplex R).X (n + 1))
    (b : ((TopCat.toSSet.obj (TopCat.of t)).chainComplex R).X (n + 1))
    (hc : (SSet.chainComplexMap (firstSubspaceToSmall X s t) R).f (n + 1) a +
      (SSet.chainComplexMap (secondSubspaceToSmall X s t) R).f (n + 1) b = c.val)
    (z : LinearMap.ker ((subspaceSmallShortComplex X s t R).X₁.sc n).g.hom)
    (ha : (SSet.chainComplexMap (TopCat.toSSet.map
        (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) R).f n z.val =
      ((TopCat.toSSet.obj (TopCat.of s)).chainComplex R).d (n + 1) n a)
    (hb : -(SSet.chainComplexMap (TopCat.toSSet.map
        (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right))) R).f n z.val =
      ((TopCat.toSSet.obj (TopCat.of t)).chainComplex R).d (n + 1) n b) :
    singularMayerVietorisConnectingMap R X s t hs ht hcover n
      (HomologicalComplex.homologyMap (smallChainMap X (twoSetFamily X s t) R) (n + 1)
        (DifferentialGeometry.Topology.moduleHomologyClass
          ((subspaceSmallShortComplex X s t R).X₃.sc (n + 1)) c)) =
      DifferentialGeometry.Topology.moduleHomologyClass
        ((subspaceSmallShortComplex X s t R).X₁.sc n) z := by
  let K := (TopCat.toSSet.obj (TopCat.of s)).chainComplex R
  let L := (TopCat.toSSet.obj (TopCat.of t)).chainComplex R
  let w : (K ⊞ L).X (n + 1) :=
    (biprod.inl : K ⟶ K ⊞ L).f (n + 1) a +
      (biprod.inr : L ⟶ K ⊞ L).f (n + 1) b
  have hw : (subspaceSmallShortComplex X s t R).g.f (n + 1) w = c.val := by
    dsimp [w, subspaceSmallShortComplex, DifferentialGeometry.ShortComplex.pushoutShortComplex]
    simp only [map_add, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
      biprod.inl_desc, biprod.inr_desc]
    exact hc
  have hd : (subspaceSmallShortComplex X s t R).f.f n z.val =
      (K ⊞ L).d (n + 1) n w := by
    apply chain_biprod_component_ext n
    · have hl := congrArg (fun f => f.f n z.val)
        (biprod.lift_fst
          (SSet.chainComplexMap (TopCat.toSSet.map
            (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) R)
          (-(SSet.chainComplexMap (TopCat.toSSet.map
            (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right))) R)))
      change (biprod.fst : K ⊞ L ⟶ K).f n
          ((subspaceSmallShortComplex X s t R).f.f n z.val) = _ at hl
      rw [hl, ha]
      have hm := congrArg (fun f => f w) ((biprod.fst : K ⊞ L ⟶ K).comm (n + 1) n)
      change K.d (n + 1) n ((biprod.fst : K ⊞ L ⟶ K).f (n + 1) w) = _ at hm
      simp only [ModuleCat.comp_apply] at hm
      rw [← hm]
      congr 1
      dsimp [w]
      simp [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f]
    · have hl := congrArg (fun f => f.f n z.val)
        (biprod.lift_snd
          (SSet.chainComplexMap (TopCat.toSSet.map
            (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) R)
          (-(SSet.chainComplexMap (TopCat.toSSet.map
            (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right))) R)))
      change (biprod.snd : K ⊞ L ⟶ L).f n
          ((subspaceSmallShortComplex X s t R).f.f n z.val) = _ at hl
      rw [hl]
      change -(SSet.chainComplexMap (TopCat.toSSet.map
        (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right))) R).f n z.val = _
      rw [hb]
      have hm := congrArg (fun f => f w) ((biprod.snd : K ⊞ L ⟶ L).comm (n + 1) n)
      change L.d (n + 1) n ((biprod.snd : K ⊞ L ⟶ L).f (n + 1) w) = _ at hm
      simp only [ModuleCat.comp_apply] at hm
      rw [← hm]
      congr 1
      dsimp [w]
      simp [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f]
  have h := congrArg (fun f => f (DifferentialGeometry.Topology.moduleHomologyClass
    ((subspaceSmallShortComplex X s t R).X₃.sc (n + 1)) c))
    (small_inclusion_singularMayerVietorisConnectingMap R X s t hs ht hcover n)
  exact h.trans (DifferentialGeometry.Topology.moduleHomologyClass_connecting
    (subspaceSmallShortExact X s t R) (n + 1) n (by simp) c w hw z hd)

end DifferentialGeometry.Homology
