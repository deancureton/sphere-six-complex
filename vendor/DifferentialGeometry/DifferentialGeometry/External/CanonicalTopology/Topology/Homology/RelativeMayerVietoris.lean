module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TwoSetSmallChains
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainCokernelElements
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeFunctoriality
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeVanishing

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private def integralTwoSetQuotientChains (A B : Set X) :
    ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  cokernel (integralSingularSmallInclusion (twoSetCover A B))

private def integralRelativeToTwoSetQuotient (A B : Set X) (i : Bool) :
    integralRelativeChains (twoSetCover A B i) ⟶ integralTwoSetQuotientChains A B :=
  cokernel.desc _ (cokernel.π (integralSingularSmallInclusion (twoSetCover A B))) (by
    erw [← integralSingularChainToSmall_inclusion (twoSetCover A B) i, Category.assoc,
      cokernel.condition, comp_zero])

private theorem integralRelativeToTwoSetQuotient_π (A B : Set X) (i : Bool) :
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion (twoSetCover A B i))) ≫
      integralRelativeToTwoSetQuotient A B i =
      cokernel.π (integralSingularSmallInclusion (twoSetCover A B)) :=
  cokernel.π_desc _ _ _

private def integralRelativeIntersectionDiagonal (A B : Set X) :
    integralRelativeChains (A ∩ B) ⟶ integralRelativeChains A ⊞ integralRelativeChains B :=
  biprod.lift
    (integralRelativeChainMap (.id X) (show MapsTo (ContinuousMap.id X) (A ∩ B) A from
      fun _ h => h.1))
    (integralRelativeChainMap (.id X) (show MapsTo (ContinuousMap.id X) (A ∩ B) B from
      fun _ h => h.2))

private def integralRelativeTwoSetDifference (A B : Set X) :
    integralRelativeChains A ⊞ integralRelativeChains B ⟶ integralTwoSetQuotientChains A B :=
  biprod.desc (integralRelativeToTwoSetQuotient A B false)
    (-integralRelativeToTwoSetQuotient A B true)

private theorem integralRelativeIntersectionDiagonal_comp_difference (A B : Set X) :
    integralRelativeIntersectionDiagonal A B ≫ integralRelativeTwoSetDifference A B = 0 := by
  let π₀ : integralSingularChains X ⟶ integralRelativeChains (A ∩ B) :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion (A ∩ B)))
  let πA : integralSingularChains X ⟶ integralRelativeChains A :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))
  let πB : integralSingularChains X ⟶ integralRelativeChains B :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion B))
  let πS : integralSingularChains X ⟶ integralTwoSetQuotientChains A B :=
    cokernel.π (integralSingularSmallInclusion (twoSetCover A B))
  let f : integralRelativeChains (A ∩ B) ⟶ integralRelativeChains A :=
    integralRelativeChainMap (ContinuousMap.id X) (show A ∩ B ⊆ A from inter_subset_left)
  let g : integralRelativeChains (A ∩ B) ⟶ integralRelativeChains B :=
    integralRelativeChainMap (ContinuousMap.id X) (show A ∩ B ⊆ B from inter_subset_right)
  let qA : integralRelativeChains A ⟶ integralTwoSetQuotientChains A B :=
    integralRelativeToTwoSetQuotient A B false
  let qB : integralRelativeChains B ⟶ integralTwoSetQuotientChains A B :=
    integralRelativeToTwoSetQuotient A B true
  have hf : π₀ ≫ f = πA := by
    have h := integralRelativeChainMap_π (ContinuousMap.id X)
      (show A ∩ B ⊆ A from inter_subset_left)
    rw [integralSingularChainMap_id, Category.id_comp] at h
    exact h
  have hg : π₀ ≫ g = πB := by
    have h := integralRelativeChainMap_π (ContinuousMap.id X)
      (show A ∩ B ⊆ B from inter_subset_right)
    rw [integralSingularChainMap_id, Category.id_comp] at h
    exact h
  have hA : π₀ ≫ (f ≫ qA) = πS := by
    calc
      π₀ ≫ (f ≫ qA) = (π₀ ≫ f) ≫ qA := (Category.assoc _ _ _).symm
      _ = πA ≫ qA := congrArg (fun k => k ≫ qA) hf
      _ = πS := integralRelativeToTwoSetQuotient_π A B false
  have hB : π₀ ≫ (g ≫ qB) = πS := by
    calc
      π₀ ≫ (g ≫ qB) = (π₀ ≫ g) ≫ qB := (Category.assoc _ _ _).symm
      _ = πB ≫ qB := congrArg (fun k => k ≫ qB) hg
      _ = πS := integralRelativeToTwoSetQuotient_π A B true
  let : Epi π₀ := inferInstanceAs
    (Epi (cokernel.π (integralSingularChainMap (singularSubspaceInclusion (A ∩ B)))))
  have heq : f ≫ qA = g ≫ qB := (cancel_epi π₀).mp (hA.trans hB.symm)
  change biprod.lift f g ≫ biprod.desc qA (-qB) = 0
  rw [biprod.lift_desc, Preadditive.comp_neg, heq, add_neg_cancel]

private def integralRelativeTwoSetSequence (A B : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (integralRelativeIntersectionDiagonal A B)
    (integralRelativeTwoSetDifference A B)
    (integralRelativeIntersectionDiagonal_comp_difference A B)

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem integralRelativeProjection_eq_zero_iff (n : ℕ) (A : Set X)
    (c : (integralSingularChains X).X n) :
    (cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))).f n c = 0 ↔
      c ∈ integralSingularChainsIn n A := by
  rw [chainCokernelπ_eq_zero_iff, integralSingularChainsIn_eq_range]
  rfl

private theorem integralRelativeRestriction_projection (n : ℕ) (A B : Set X) (hAB : A ⊆ B)
    (c : (integralSingularChains X).X n) :
    (integralRelativeChainMap (ContinuousMap.id X) hAB).f n
      ((cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))).f n c) =
      (cokernel.π (integralSingularChainMap (singularSubspaceInclusion B))).f n c := by
  have h := integralRelativeChainMap_π (ContinuousMap.id X) hAB
  rw [integralSingularChainMap_id, Category.id_comp] at h
  exact congrArg (fun f : integralSingularChains X ⟶ integralRelativeChains B => f.f n c) h

private theorem integralRelativeToTwoSetQuotient_projection (n : ℕ) (A B : Set X) (i : Bool)
    (c : (integralSingularChains X).X n) :
    (integralRelativeToTwoSetQuotient A B i).f n
      ((cokernel.π (integralSingularChainMap (singularSubspaceInclusion (twoSetCover A B i)))).f n c) =
      (cokernel.π (integralSingularSmallInclusion (twoSetCover A B))).f n c :=
  congrArg (fun f : integralSingularChains X ⟶ integralTwoSetQuotientChains A B => f.f n c)
    (integralRelativeToTwoSetQuotient_π A B i)

private theorem integralTwoSetProjection_eq_zero_iff (n : ℕ) (A B : Set X)
    (c : (integralSingularChains X).X n) :
    (cokernel.π (integralSingularSmallInclusion (twoSetCover A B))).f n c = 0 ↔
      c ∈ integralSingularSmallChains n (twoSetCover A B) := by
  rw [chainCokernelπ_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    change b.val = c at hb
    exact hb ▸ b.property
  · intro hc
    exact ⟨⟨c, hc⟩, rfl⟩

private theorem chain_biprod_component_ext
    {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (n : ℕ) (z w : (K ⊞ L).X n)
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

private theorem integralRelativeIntersectionDiagonal_fst (n : ℕ) (A B : Set X)
    (c : (integralRelativeChains (A ∩ B)).X n) :
    (biprod.fst : integralRelativeChains A ⊞ integralRelativeChains B ⟶ integralRelativeChains A).f n
      ((integralRelativeIntersectionDiagonal A B).f n c) =
      (integralRelativeChainMap (ContinuousMap.id X) (show A ∩ B ⊆ A from inter_subset_left)).f n c :=
  congrArg (fun f : integralRelativeChains (A ∩ B) ⟶ integralRelativeChains A => f.f n c)
    (biprod.lift_fst _ _)

private theorem integralRelativeIntersectionDiagonal_snd (n : ℕ) (A B : Set X)
    (c : (integralRelativeChains (A ∩ B)).X n) :
    (biprod.snd : integralRelativeChains A ⊞ integralRelativeChains B ⟶ integralRelativeChains B).f n
      ((integralRelativeIntersectionDiagonal A B).f n c) =
      (integralRelativeChainMap (ContinuousMap.id X) (show A ∩ B ⊆ B from inter_subset_right)).f n c :=
  congrArg (fun f : integralRelativeChains (A ∩ B) ⟶ integralRelativeChains B => f.f n c)
    (biprod.lift_snd _ _)

private theorem integralRelativeTwoSetDifference_apply (n : ℕ) (A B : Set X)
    (z : (integralRelativeChains A ⊞ integralRelativeChains B).X n) :
    (integralRelativeTwoSetDifference A B).f n z =
      (integralRelativeToTwoSetQuotient A B false).f n
        ((biprod.fst : integralRelativeChains A ⊞ integralRelativeChains B ⟶ integralRelativeChains A).f n z) -
      (integralRelativeToTwoSetQuotient A B true).f n
        ((biprod.snd : integralRelativeChains A ⊞ integralRelativeChains B ⟶ integralRelativeChains B).f n z) := by
  have h : integralRelativeTwoSetDifference A B =
      biprod.fst ≫ integralRelativeToTwoSetQuotient A B false -
      biprod.snd ≫ integralRelativeToTwoSetQuotient A B true := by
    change biprod.desc (integralRelativeToTwoSetQuotient A B false)
      (-integralRelativeToTwoSetQuotient A B true) = _
    rw [biprod.desc_eq, Preadditive.comp_neg, ← sub_eq_add_neg]
  exact congrArg (fun f : integralRelativeChains A ⊞ integralRelativeChains B ⟶
    integralTwoSetQuotientChains A B => f.f n z) h

private theorem integralRelativeIntersectionDiagonal_injective (n : ℕ) (A B : Set X) :
    Function.Injective ((integralRelativeIntersectionDiagonal A B).f n) := by
  apply (injective_iff_map_eq_zero ((integralRelativeIntersectionDiagonal A B).f n).hom).mpr
  intro z hz
  obtain ⟨c, rfl⟩ := chainCokernelπ_surjective
    (integralSingularChainMap (singularSubspaceInclusion (A ∩ B))) n z
  let π₀ : integralSingularChains X ⟶ integralRelativeChains (A ∩ B) :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion (A ∩ B)))
  let πA : integralSingularChains X ⟶ integralRelativeChains A :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))
  let πB : integralSingularChains X ⟶ integralRelativeChains B :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion B))
  change (integralRelativeIntersectionDiagonal A B).f n
    (π₀.f n c) = 0 at hz
  let pA : integralRelativeChains A ⊞ integralRelativeChains B ⟶ integralRelativeChains A := biprod.fst
  let pB : integralRelativeChains A ⊞ integralRelativeChains B ⟶ integralRelativeChains B := biprod.snd
  have hA : πA.f n c = 0 := by
    calc
      πA.f n c = (integralRelativeChainMap (ContinuousMap.id X)
          (show A ∩ B ⊆ A from inter_subset_left)).f n (π₀.f n c) :=
        (integralRelativeRestriction_projection n (A ∩ B) A inter_subset_left c).symm
      _ = pA.f n ((integralRelativeIntersectionDiagonal A B).f n (π₀.f n c)) :=
        (integralRelativeIntersectionDiagonal_fst n A B (π₀.f n c)).symm
      _ = pA.f n 0 := congrArg (fun w => pA.f n w) hz
      _ = 0 := map_zero (pA.f n).hom
  have hB : πB.f n c = 0 := by
    calc
      πB.f n c = (integralRelativeChainMap (ContinuousMap.id X)
          (show A ∩ B ⊆ B from inter_subset_right)).f n (π₀.f n c) :=
        (integralRelativeRestriction_projection n (A ∩ B) B inter_subset_right c).symm
      _ = pB.f n ((integralRelativeIntersectionDiagonal A B).f n (π₀.f n c)) :=
        (integralRelativeIntersectionDiagonal_snd n A B (π₀.f n c)).symm
      _ = pB.f n 0 := congrArg (fun w => pB.f n w) hz
      _ = 0 := map_zero (pB.f n).hom
  apply (integralRelativeProjection_eq_zero_iff n (A ∩ B) c).mpr
  rw [integralSingularChainsIn_inter]
  exact ⟨(integralRelativeProjection_eq_zero_iff n A c).mp hA,
    (integralRelativeProjection_eq_zero_iff n B c).mp hB⟩

private theorem integralRelativeTwoSetDifference_surjective (n : ℕ) (A B : Set X) :
    Function.Surjective ((integralRelativeTwoSetDifference A B).f n) := by
  intro z
  obtain ⟨c, rfl⟩ := chainCokernelπ_surjective
    (integralSingularSmallInclusion (twoSetCover A B)) n z
  refine ⟨(biprod.inl : integralRelativeChains A ⟶
    integralRelativeChains A ⊞ integralRelativeChains B).f n
      ((cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))).f n c), ?_⟩
  have h := congrArg (fun f : integralRelativeChains A ⟶ integralTwoSetQuotientChains A B => f.f n
    ((cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))).f n c))
    (biprod.inl_desc (integralRelativeToTwoSetQuotient A B false)
      (-integralRelativeToTwoSetQuotient A B true))
  exact h.trans (integralRelativeToTwoSetQuotient_projection n A B false c)

private theorem integralRelativeTwoSetSequence_exact (n : ℕ) (A B : Set X)
    (z : (integralRelativeChains A ⊞ integralRelativeChains B).X n)
    (hz : (integralRelativeTwoSetDifference A B).f n z = 0) :
    ∃ c : (integralRelativeChains (A ∩ B)).X n,
      (integralRelativeIntersectionDiagonal A B).f n c = z := by
  obtain ⟨a, ha⟩ := chainCokernelπ_surjective
    (integralSingularChainMap (singularSubspaceInclusion A)) n
    ((biprod.fst : integralRelativeChains A ⊞ integralRelativeChains B ⟶ integralRelativeChains A).f n z)
  obtain ⟨b, hb⟩ := chainCokernelπ_surjective
    (integralSingularChainMap (singularSubspaceInclusion B)) n
    ((biprod.snd : integralRelativeChains A ⊞ integralRelativeChains B ⟶ integralRelativeChains B).f n z)
  rw [integralRelativeTwoSetDifference_apply, ← ha, ← hb,
    integralRelativeToTwoSetQuotient_projection, integralRelativeToTwoSetQuotient_projection] at hz
  let πS : integralSingularChains X ⟶ integralTwoSetQuotientChains A B :=
    cokernel.π (integralSingularSmallInclusion (twoSetCover A B))
  change πS.f n a - πS.f n b = 0 at hz
  have hsmall : (cokernel.π (integralSingularSmallInclusion (twoSetCover A B))).f n (a - b) = 0 :=
    (map_sub (πS.f n).hom a b).trans hz
  rw [integralTwoSetProjection_eq_zero_iff, integralSingularTwoSetSmallChains_eq,
    Submodule.mem_sup] at hsmall
  obtain ⟨s, hs, t, ht, hst⟩ := hsmall
  have hc : a - s = b + t := by
    calc
      a - s = b + (a - b) - s := by abel
      _ = b + (s + t) - s := by rw [hst]
      _ = b + t := by abel
  let π₀ : integralSingularChains X ⟶ integralRelativeChains (A ∩ B) :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion (A ∩ B)))
  let πA : integralSingularChains X ⟶ integralRelativeChains A :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))
  let πB : integralSingularChains X ⟶ integralRelativeChains B :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion B))
  have hs0 : πA.f n s = 0 := (integralRelativeProjection_eq_zero_iff n A s).mpr hs
  have ht0 : πB.f n t = 0 := (integralRelativeProjection_eq_zero_iff n B t).mpr ht
  refine ⟨π₀.f n (a - s), ?_⟩
  apply chain_biprod_component_ext n
  · calc
      _ = (integralRelativeChainMap (ContinuousMap.id X)
          (show A ∩ B ⊆ A from inter_subset_left)).f n (π₀.f n (a - s)) :=
        integralRelativeIntersectionDiagonal_fst n A B (π₀.f n (a - s))
      _ = πA.f n (a - s) := integralRelativeRestriction_projection n (A ∩ B) A inter_subset_left (a - s)
      _ = πA.f n a - πA.f n s := map_sub (πA.f n).hom a s
      _ = πA.f n a := by rw [hs0, sub_zero]
      _ = _ := ha
  · calc
      _ = (integralRelativeChainMap (ContinuousMap.id X)
          (show A ∩ B ⊆ B from inter_subset_right)).f n (π₀.f n (a - s)) :=
        integralRelativeIntersectionDiagonal_snd n A B (π₀.f n (a - s))
      _ = πB.f n (a - s) := integralRelativeRestriction_projection n (A ∩ B) B inter_subset_right (a - s)
      _ = πB.f n (b + t) := congrArg (fun c => πB.f n c) hc
      _ = πB.f n b + πB.f n t := map_add (πB.f n).hom b t
      _ = πB.f n b := by rw [ht0, add_zero]
      _ = _ := hb

private theorem integralRelativeTwoSetSequence_shortExact (A B : Set X) :
    (integralRelativeTwoSetSequence A B).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    exact integralRelativeTwoSetSequence_exact n A B
  · exact (ModuleCat.mono_iff_injective _).mpr (integralRelativeIntersectionDiagonal_injective n A B)
  · exact (ModuleCat.epi_iff_surjective _).mpr (integralRelativeTwoSetDifference_surjective n A B)

private theorem integralRelativeTwoSetHomology_exact (n : ℕ) (A B : Set X) :
    Function.Exact
      (HomologicalComplex.homologyMap (integralRelativeIntersectionDiagonal A B) n).hom
      (HomologicalComplex.homologyMap (integralRelativeTwoSetDifference A B) n).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeTwoSetSequence_shortExact A B).homology_exact₂ n)

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private def twoSetSubspaceCover (A B : Set X) : Bool → Set ↥(A ∪ B) :=
  twoSetCover (subspaceIntersection A (A ∪ B)) (subspaceIntersection B (A ∪ B))

private theorem integralTwoSetSmallMap_mem (n : ℕ) (A B : Set X)
    (c : integralSingularSmallChains n (twoSetSubspaceCover A B)) :
    (integralSingularChainMap (singularSubspaceInclusion (A ∪ B))).f n c.val ∈
      integralSingularSmallChains n (twoSetCover A B) := by
  have h : integralSingularSmallChains n (twoSetSubspaceCover A B) ≤
      Submodule.comap
        ((integralSingularChainMap (singularSubspaceInclusion (A ∪ B))).f n).hom
        (integralSingularSmallChains n (twoSetCover A B)) := by
    apply iSup_le
    intro i b hb
    apply Submodule.mem_iSup_of_mem i
    apply integralSingularChainsIn_map n (singularSubspaceInclusion (A ∪ B)) _ hb
    cases i <;> exact fun _ hz => hz
  exact h c.property

private def integralTwoSetSmallMap (A B : Set X) :
    integralSingularSmallComplex (twoSetSubspaceCover A B) ⟶
      integralSingularSmallComplex (twoSetCover A B) where
  f n := ModuleCat.ofHom
    (((integralSingularChainMap (singularSubspaceInclusion (A ∪ B))).f n).hom.restrict
      (fun c hc => integralTwoSetSmallMap_mem n A B ⟨c, hc⟩))
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun f : (integralSingularChains ↥(A ∪ B)).X n ⟶
      (integralSingularChains X).X m => f c.val)
        ((integralSingularChainMap (singularSubspaceInclusion (A ∪ B))).comm n m)

private theorem integralTwoSetSmallMap_inclusion (A B : Set X) :
    integralTwoSetSmallMap A B ≫ integralSingularSmallInclusion (twoSetCover A B) =
      integralSingularSmallInclusion (twoSetSubspaceCover A B) ≫
        integralSingularChainMap (singularSubspaceInclusion (A ∪ B)) := rfl

private theorem integralTwoSetSmallMap_isIso (A B : Set X) : IsIso (integralTwoSetSmallMap A B) := by
  have hf (n : ℕ) : IsIso ((integralTwoSetSmallMap A B).f n) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro c d h
      apply Subtype.ext
      apply integralSingularChainInclusion_injective n (A ∪ B)
      exact congrArg Subtype.val h
    · intro z
      obtain ⟨a, b, hab⟩ := integralSingularTwoSetSmallChains_decompose n A B z
      let fA : C(A, ↥(A ∪ B)) :=
        ⟨fun x => ⟨x.val, Or.inl x.property⟩, continuous_subtype_val.subtype_mk _⟩
      let fB : C(B, ↥(A ∪ B)) :=
        ⟨fun x => ⟨x.val, Or.inr x.property⟩, continuous_subtype_val.subtype_mk _⟩
      have hA : (integralSingularChainMap fA).f n a ∈
          integralSingularSmallChains n (twoSetSubspaceCover A B) := by
        apply Submodule.mem_iSup_of_mem false
        apply integralSingularChainsIn_map n fA
          (show MapsTo fA univ (subspaceIntersection A (A ∪ B)) from fun x _ => x.property)
        rw [integralSingularChainsIn_univ]
        exact Submodule.mem_top
      have hB : (integralSingularChainMap fB).f n b ∈
          integralSingularSmallChains n (twoSetSubspaceCover A B) := by
        apply Submodule.mem_iSup_of_mem true
        apply integralSingularChainsIn_map n fB
          (show MapsTo fB univ (subspaceIntersection B (A ∪ B)) from fun x _ => x.property)
        rw [integralSingularChainsIn_univ]
        exact Submodule.mem_top
      refine ⟨⟨(integralSingularChainMap fA).f n a + (integralSingularChainMap fB).f n b,
        (integralSingularSmallChains n (twoSetSubspaceCover A B)).add_mem hA hB⟩, ?_⟩
      apply Subtype.ext
      change (integralSingularChainMap (singularSubspaceInclusion (A ∪ B))).f n
        ((integralSingularChainMap fA).f n a + (integralSingularChainMap fB).f n b) = z.val
      rw [map_add]
      have hFA : integralSingularChainMap fA ≫
          integralSingularChainMap (singularSubspaceInclusion (A ∪ B)) =
          integralSingularChainMap (singularSubspaceInclusion A) := by
        rw [← integralSingularChainMap_comp]
        rfl
      have hFB : integralSingularChainMap fB ≫
          integralSingularChainMap (singularSubspaceInclusion (A ∪ B)) =
          integralSingularChainMap (singularSubspaceInclusion B) := by
        rw [← integralSingularChainMap_comp]
        rfl
      have ha := congrArg (fun f : integralSingularChains A ⟶ integralSingularChains X => f.f n a) hFA
      have hb := congrArg (fun f : integralSingularChains B ⟶ integralSingularChains X => f.f n b) hFB
      exact (congrArg₂ (· + ·) ha hb).trans hab
  let := hf
  exact HomologicalComplex.Hom.isIso_of_components _

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private def integralTwoSetSmallToUnion (A B : Set X) :
    integralSingularSmallComplex (twoSetCover A B) ⟶ integralSingularChains ↥(A ∪ B) := by
  let := integralTwoSetSmallMap_isIso A B
  exact (asIso (integralTwoSetSmallMap A B)).inv ≫
    integralSingularSmallInclusion (twoSetSubspaceCover A B)

private theorem integralTwoSetSmallToUnion_comp_inclusion (A B : Set X) :
    integralTwoSetSmallToUnion A B ≫
      integralSingularChainMap (singularSubspaceInclusion (A ∪ B)) =
      integralSingularSmallInclusion (twoSetCover A B) := by
  let F := integralTwoSetSmallMap A B
  let : IsIso F := integralTwoSetSmallMap_isIso A B
  have hleft : F ≫ integralTwoSetSmallToUnion A B =
      integralSingularSmallInclusion (twoSetSubspaceCover A B) := by
    change (asIso F).hom ≫ ((asIso F).inv ≫
      integralSingularSmallInclusion (twoSetSubspaceCover A B)) = _
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  apply (cancel_epi F).mp
  calc
    F ≫ (integralTwoSetSmallToUnion A B ≫
        integralSingularChainMap (singularSubspaceInclusion (A ∪ B))) =
        (F ≫ integralTwoSetSmallToUnion A B) ≫
          integralSingularChainMap (singularSubspaceInclusion (A ∪ B)) :=
      (Category.assoc _ _ _).symm
    _ = integralSingularSmallInclusion (twoSetSubspaceCover A B) ≫
        integralSingularChainMap (singularSubspaceInclusion (A ∪ B)) :=
      congrArg (fun f => f ≫ integralSingularChainMap (singularSubspaceInclusion (A ∪ B))) hleft
    _ = F ≫ integralSingularSmallInclusion (twoSetCover A B) :=
      (integralTwoSetSmallMap_inclusion A B).symm

private theorem integralTwoSetSmallToUnion_quasiIso (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    QuasiIso (integralTwoSetSmallToUnion A B) := by
  have hopen : ∀ i, IsOpen (twoSetSubspaceCover A B i) := by
    intro i
    cases i with
    | false => exact hA.preimage continuous_subtype_val
    | true => exact hB.preimage continuous_subtype_val
  have hcover : ∀ x : ↥(A ∪ B), ∃ i, x ∈ twoSetSubspaceCover A B i := by
    intro x
    rcases x.property with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  let := integralTwoSetSmallMap_isIso A B
  let := integralSingularSmallInclusion_quasiIso (twoSetSubspaceCover A B) hopen hcover
  change QuasiIso ((asIso (integralTwoSetSmallMap A B)).inv ≫
    integralSingularSmallInclusion (twoSetSubspaceCover A B))
  infer_instance

private def integralTwoSetQuotientComparison (A B : Set X) :
    integralTwoSetQuotientChains A B ⟶ integralRelativeChains (A ∪ B) :=
  cokernel.map (integralSingularSmallInclusion (twoSetCover A B))
    (integralSingularChainMap (singularSubspaceInclusion (A ∪ B)))
    (integralTwoSetSmallToUnion A B) (𝟙 (integralSingularChains X))
    ((Category.comp_id _).trans (integralTwoSetSmallToUnion_comp_inclusion A B).symm)

private theorem integralTwoSetQuotientComparison_π (A B : Set X) :
    cokernel.π (integralSingularSmallInclusion (twoSetCover A B)) ≫
      integralTwoSetQuotientComparison A B =
      cokernel.π (integralSingularChainMap (singularSubspaceInclusion (A ∪ B))) := by
  exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)

private theorem integralTwoSetQuotientComparison_quasiIso (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) : QuasiIso (integralTwoSetQuotientComparison A B) := by
  let S := ShortComplex.mk (integralSingularSmallInclusion (twoSetCover A B))
    (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact :=
    { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel _)
      mono_f := integralSingularSmallInclusion_mono (twoSetCover A B)
      epi_g := inferInstanceAs (Epi (cokernel.π (integralSingularSmallInclusion (twoSetCover A B)))) }
  let φ : S ⟶ integralRelativeChainSequence (A ∪ B) :=
    { τ₁ := integralTwoSetSmallToUnion A B
      τ₂ := 𝟙 (integralSingularChains X)
      τ₃ := integralTwoSetQuotientComparison A B
      comm₁₂ := (integralTwoSetSmallToUnion_comp_inclusion A B).trans (Category.comp_id _).symm
      comm₂₃ := (cokernel.π_desc _ _ _).symm }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hS
    (integralRelativeChainSequence_shortExact (A ∪ B))
    (integralTwoSetSmallToUnion_quasiIso A B hA hB)
    (inferInstanceAs (QuasiIso (𝟙 (integralSingularChains X))))

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory CategoryTheory.Limits Set HomologicalComplex

universe u

namespace DifferentialGeometry.Topology

private theorem homologyMap_comp_apply
    {K L M : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L) (g : L ⟶ M)
    (n : ℕ) (a : K.homology n) :
    homologyMap g n (homologyMap f n a) = homologyMap (f ≫ g) n a :=
  congrArg (fun h : K.homology n ⟶ M.homology n => h a) (homologyMap_comp f g n).symm

private theorem homology_biprod_fst_pair
    (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ)
    (a : K.homology n) (b : L.homology n) :
    homologyMap (biprod.fst : K ⊞ L ⟶ K) n
      (homologyMap (biprod.inl : K ⟶ K ⊞ L) n a +
        homologyMap (biprod.inr : L ⟶ K ⊞ L) n b) = a := by
  rw [map_add, homologyMap_comp_apply, homologyMap_comp_apply,
    biprod.inl_fst, biprod.inr_fst, homologyMap_id, homologyMap_zero]
  exact add_zero a

private theorem homology_biprod_snd_pair
    (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ)
    (a : K.homology n) (b : L.homology n) :
    homologyMap (biprod.snd : K ⊞ L ⟶ L) n
      (homologyMap (biprod.inl : K ⟶ K ⊞ L) n a +
        homologyMap (biprod.inr : L ⟶ K ⊞ L) n b) = b := by
  rw [map_add, homologyMap_comp_apply, homologyMap_comp_apply,
    biprod.inl_snd, biprod.inr_snd, homologyMap_id, homologyMap_zero]
  exact zero_add b

private theorem homology_biprod_desc_pair
    {K L M : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ M) (g : L ⟶ M)
    (n : ℕ) (a : K.homology n) (b : L.homology n) :
    homologyMap (biprod.desc f g) n
      (homologyMap (biprod.inl : K ⟶ K ⊞ L) n a +
        homologyMap (biprod.inr : L ⟶ K ⊞ L) n b) =
      homologyMap f n a + homologyMap g n b := by
  rw [map_add, homologyMap_comp_apply, homologyMap_comp_apply,
    biprod.inl_desc, biprod.inr_desc]

variable {X : Type u} [TopologicalSpace X]

private theorem integralRelativeToTwoSetQuotient_comp_comparison (A B : Set X) (i : Bool) :
    integralRelativeToTwoSetQuotient A B i ≫ integralTwoSetQuotientComparison A B =
      integralRelativeChainMap (ContinuousMap.id X)
        (show twoSetCover A B i ⊆ A ∪ B from by
          cases i
          · exact subset_union_left
          · exact subset_union_right) := by
  let πi : integralSingularChains X ⟶ integralRelativeChains (twoSetCover A B i) :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion (twoSetCover A B i)))
  let πS : integralSingularChains X ⟶ integralTwoSetQuotientChains A B :=
    cokernel.π (integralSingularSmallInclusion (twoSetCover A B))
  let πU : integralSingularChains X ⟶ integralRelativeChains (A ∪ B) :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion (A ∪ B)))
  have hi : twoSetCover A B i ⊆ A ∪ B := by
    cases i
    · exact subset_union_left
    · exact subset_union_right
  let r : integralRelativeChains (twoSetCover A B i) ⟶ integralRelativeChains (A ∪ B) :=
    integralRelativeChainMap (ContinuousMap.id X) hi
  have hr : πi ≫ r = πU := by
    have h := integralRelativeChainMap_π (ContinuousMap.id X) hi
    rw [integralSingularChainMap_id, Category.id_comp] at h
    exact h
  let : Epi πi := inferInstanceAs
    (Epi (cokernel.π (integralSingularChainMap (singularSubspaceInclusion (twoSetCover A B i)))))
  apply (cancel_epi πi).mp
  calc
    πi ≫ (integralRelativeToTwoSetQuotient A B i ≫ integralTwoSetQuotientComparison A B) =
        (πi ≫ integralRelativeToTwoSetQuotient A B i) ≫ integralTwoSetQuotientComparison A B :=
      (Category.assoc _ _ _).symm
    _ = πS ≫ integralTwoSetQuotientComparison A B :=
      congrArg (fun f => f ≫ integralTwoSetQuotientComparison A B)
        (integralRelativeToTwoSetQuotient_π A B i)
    _ = πU := integralTwoSetQuotientComparison_π A B
    _ = πi ≫ r := hr.symm

theorem exists_relative_homology_inter_class (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B)
    (a : integralRelativeHomology n A) (b : integralRelativeHomology n B)
    (hab : integralRelativeHomologyMap n (ContinuousMap.id X)
        (show A ⊆ A ∪ B from subset_union_left) a =
      integralRelativeHomologyMap n (ContinuousMap.id X)
        (show B ⊆ A ∪ B from subset_union_right) b) :
    ∃ c : integralRelativeHomology n (A ∩ B),
      integralRelativeHomologyMap n (ContinuousMap.id X)
          (show A ∩ B ⊆ A from inter_subset_left) c = a ∧
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show A ∩ B ⊆ B from inter_subset_right) c = b := by
  let K := integralRelativeChains A
  let L := integralRelativeChains B
  let z : (K ⊞ L).homology n :=
    homologyMap (biprod.inl : K ⟶ K ⊞ L) n a +
      homologyMap (biprod.inr : L ⟶ K ⊞ L) n b
  let qA : K ⟶ integralTwoSetQuotientChains A B := integralRelativeToTwoSetQuotient A B false
  let qB : L ⟶ integralTwoSetQuotientChains A B := integralRelativeToTwoSetQuotient A B true
  let δ := integralRelativeTwoSetDifference A B
  let ρ := integralTwoSetQuotientComparison A B
  let : QuasiIso ρ := integralTwoSetQuotientComparison_quasiIso A B hA hB
  have hpair : homologyMap δ n z = homologyMap qA n a - homologyMap qB n b := by
    have h := homology_biprod_desc_pair qA (-qB) n a b
    rw [homologyMap_neg] at h
    change homologyMap δ n z =
      (homologyMap qA n).hom a + (-homologyMap qB n).hom b at h
    rw [ModuleCat.hom_neg, LinearMap.neg_apply] at h
    simpa only [sub_eq_add_neg] using h
  have hzero : homologyMap δ n z = 0 := by
    apply (ModuleCat.mono_iff_injective (homologyMap ρ n)).mp inferInstance
    rw [hpair, map_sub, map_zero, homologyMap_comp_apply, homologyMap_comp_apply]
    rw [integralRelativeToTwoSetQuotient_comp_comparison,
      integralRelativeToTwoSetQuotient_comp_comparison]
    exact sub_eq_zero.mpr hab
  obtain ⟨c, hc⟩ := (integralRelativeTwoSetHomology_exact n A B z).mp hzero
  refine ⟨c, ?_, ?_⟩
  · have h := congrArg (fun v => homologyMap (biprod.fst : K ⊞ L ⟶ K) n v) hc
    rw [homologyMap_comp_apply] at h
    have hfst : integralRelativeIntersectionDiagonal A B ≫ (biprod.fst : K ⊞ L ⟶ K) =
        integralRelativeChainMap (ContinuousMap.id X) (show A ∩ B ⊆ A from inter_subset_left) :=
      biprod.lift_fst _ _
    rw [hfst] at h
    exact h.trans (homology_biprod_fst_pair K L n a b)
  · have h := congrArg (fun v => homologyMap (biprod.snd : K ⊞ L ⟶ L) n v) hc
    rw [homologyMap_comp_apply] at h
    have hsnd : integralRelativeIntersectionDiagonal A B ≫ (biprod.snd : K ⊞ L ⟶ L) =
        integralRelativeChainMap (ContinuousMap.id X) (show A ∩ B ⊆ B from inter_subset_right) :=
      biprod.lift_snd _ _
    rw [hsnd] at h
    exact h.trans (homology_biprod_snd_pair K L n a b)

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory CategoryTheory.Limits Set HomologicalComplex

universe u

namespace DifferentialGeometry.Topology

private theorem homology_biprod_pair_projections
    (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) (v : (K ⊞ L).homology n) :
    homologyMap (biprod.inl : K ⟶ K ⊞ L) n
        (homologyMap (biprod.fst : K ⊞ L ⟶ K) n v) +
      homologyMap (biprod.inr : L ⟶ K ⊞ L) n
        (homologyMap (biprod.snd : K ⊞ L ⟶ L) n v) = v := by
  have h := congrArg (fun f : K ⊞ L ⟶ K ⊞ L => homologyMap f n)
    (biprod.total (X := K) (Y := L))
  rw [homologyMap_add, homologyMap_comp, homologyMap_comp, homologyMap_id] at h
  exact congrArg (fun f : (K ⊞ L).homology n ⟶ (K ⊞ L).homology n => f v) h

variable {X : Type u} [TopologicalSpace X]

private theorem integralRelativeIntersectionDiagonal_homology_injective
    (n : ℕ) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    [Subsingleton (integralRelativeHomology (n + 1) (A ∪ B))] :
    Function.Injective (homologyMap (integralRelativeIntersectionDiagonal A B) n) := by
  let ρ := integralTwoSetQuotientComparison A B
  let : QuasiIso ρ := integralTwoSetQuotientComparison_quasiIso A B hA hB
  have hρ : Function.Injective (homologyMap ρ (n + 1)) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  let : Subsingleton ((integralTwoSetQuotientChains A B).homology (n + 1)) :=
    ⟨fun a b => hρ (Subsingleton.elim _ _)⟩
  let : Subsingleton ((integralRelativeTwoSetSequence A B).X₃.homology (n + 1)) :=
    inferInstanceAs (Subsingleton ((integralTwoSetQuotientChains A B).homology (n + 1)))
  have hS := integralRelativeTwoSetSequence_shortExact A B
  let d := hS.δ (n + 1) n (by simp)
  have hexact : Function.Exact d.hom
      (homologyMap (integralRelativeIntersectionDiagonal A B) n).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₁ (n + 1) n (by simp))
  apply (LinearMap.injective_iff_eq_zero_of_exact hexact).mpr
  apply LinearMap.ext
  intro a
  have ha : a = 0 := Subsingleton.elim _ _
  exact (congrArg d.hom ha).trans (map_zero d.hom)

theorem relative_homology_inter_eq_of_restrictions_eq
    (n : ℕ) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    [Subsingleton (integralRelativeHomology (n + 1) (A ∪ B))]
    (c d : integralRelativeHomology n (A ∩ B))
    (hfst : integralRelativeHomologyMap n (ContinuousMap.id X)
        (show A ∩ B ⊆ A from inter_subset_left) c =
      integralRelativeHomologyMap n (ContinuousMap.id X)
        (show A ∩ B ⊆ A from inter_subset_left) d)
    (hsnd : integralRelativeHomologyMap n (ContinuousMap.id X)
        (show A ∩ B ⊆ B from inter_subset_right) c =
      integralRelativeHomologyMap n (ContinuousMap.id X)
        (show A ∩ B ⊆ B from inter_subset_right) d) : c = d := by
  let K := integralRelativeChains A
  let L := integralRelativeChains B
  let f := integralRelativeIntersectionDiagonal A B
  have hp : f ≫ (biprod.fst : K ⊞ L ⟶ K) =
      integralRelativeChainMap (ContinuousMap.id X) (show A ∩ B ⊆ A from inter_subset_left) :=
    biprod.lift_fst _ _
  have hq : f ≫ (biprod.snd : K ⊞ L ⟶ L) =
      integralRelativeChainMap (ContinuousMap.id X) (show A ∩ B ⊆ B from inter_subset_right) :=
    biprod.lift_snd _ _
  have hp' : homologyMap (biprod.fst : K ⊞ L ⟶ K) n (homologyMap f n c) =
      homologyMap (biprod.fst : K ⊞ L ⟶ K) n (homologyMap f n d) := by
    rw [homologyMap_comp_apply, homologyMap_comp_apply, hp]
    exact hfst
  have hq' : homologyMap (biprod.snd : K ⊞ L ⟶ L) n (homologyMap f n c) =
      homologyMap (biprod.snd : K ⊞ L ⟶ L) n (homologyMap f n d) := by
    rw [homologyMap_comp_apply, homologyMap_comp_apply, hq]
    exact hsnd
  apply integralRelativeIntersectionDiagonal_homology_injective n A B hA hB
  have h := homology_biprod_pair_projections K L n (homologyMap f n c)
  rw [hp', hq'] at h
  exact h.symm.trans (homology_biprod_pair_projections K L n (homologyMap f n d))

theorem exists_unique_relative_homology_inter_class (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B)
    [Subsingleton (integralRelativeHomology (n + 1) (A ∪ B))]
    (a : integralRelativeHomology n A) (b : integralRelativeHomology n B)
    (hab : integralRelativeHomologyMap n (ContinuousMap.id X)
        (show A ⊆ A ∪ B from subset_union_left) a =
      integralRelativeHomologyMap n (ContinuousMap.id X)
        (show B ⊆ A ∪ B from subset_union_right) b) :
    ∃! c : integralRelativeHomology n (A ∩ B),
      integralRelativeHomologyMap n (ContinuousMap.id X)
          (show A ∩ B ⊆ A from inter_subset_left) c = a ∧
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show A ∩ B ⊆ B from inter_subset_right) c = b := by
  obtain ⟨c, hc, hd⟩ := exists_relative_homology_inter_class n A B hA hB a b hab
  refine ⟨c, ⟨hc, hd⟩, ?_⟩
  intro d hd'
  exact relative_homology_inter_eq_of_restrictions_eq n A B hA hB d c
    (hd'.1.trans hc.symm) (hd'.2.trans hd.symm)

end DifferentialGeometry.Topology

end

noncomputable section

open Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem exists_relative_homology_union_class (n : ℕ) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L)
    (a : integralRelativeHomology n Kᶜ) (b : integralRelativeHomology n Lᶜ)
    (hab : integralRelativeHomologyMap n (ContinuousMap.id X)
        (show Kᶜ ⊆ (K ∩ L)ᶜ from compl_subset_compl.mpr inter_subset_left) a =
      integralRelativeHomologyMap n (ContinuousMap.id X)
        (show Lᶜ ⊆ (K ∩ L)ᶜ from compl_subset_compl.mpr inter_subset_right) b) :
    ∃ c : integralRelativeHomology n (K ∪ L)ᶜ,
      integralRelativeHomologyMap n (ContinuousMap.id X)
          (show (K ∪ L)ᶜ ⊆ Kᶜ from compl_subset_compl.mpr subset_union_left) c = a ∧
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show (K ∪ L)ᶜ ⊆ Lᶜ from compl_subset_compl.mpr subset_union_right) c = b := by
  have aux (C D : Set X) (hC : C = Kᶜ ∩ Lᶜ) (hD : D = Kᶜ ∪ Lᶜ)
      (hCK : MapsTo (ContinuousMap.id X) C Kᶜ)
      (hCL : MapsTo (ContinuousMap.id X) C Lᶜ)
      (hKD : MapsTo (ContinuousMap.id X) Kᶜ D)
      (hLD : MapsTo (ContinuousMap.id X) Lᶜ D)
      (h : integralRelativeHomologyMap n (ContinuousMap.id X) hKD a =
        integralRelativeHomologyMap n (ContinuousMap.id X) hLD b) :
      ∃ c : integralRelativeHomology n C,
        integralRelativeHomologyMap n (ContinuousMap.id X) hCK c = a ∧
          integralRelativeHomologyMap n (ContinuousMap.id X) hCL c = b := by
    subst C
    subst D
    exact exists_relative_homology_inter_class n Kᶜ Lᶜ
      hK.isOpen_compl hL.isOpen_compl a b h
  exact aux (K ∪ L)ᶜ (K ∩ L)ᶜ (compl_union K L) (compl_inter K L)
    (fun _ hx hk => hx (Or.inl hk)) (fun _ hx hl => hx (Or.inr hl))
    (fun _ hx hkl => hx hkl.1) (fun _ hx hkl => hx hkl.2) hab

theorem exists_relative_homology_disjoint_union_class (n : ℕ) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (hKL : Disjoint K L)
    (a : integralRelativeHomology n Kᶜ) (b : integralRelativeHomology n Lᶜ) :
    ∃ c : integralRelativeHomology n (K ∪ L)ᶜ,
      integralRelativeHomologyMap n (ContinuousMap.id X)
          (show (K ∪ L)ᶜ ⊆ Kᶜ from compl_subset_compl.mpr subset_union_left) c = a ∧
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show (K ∪ L)ᶜ ⊆ Lᶜ from compl_subset_compl.mpr subset_union_right) c = b := by
  have hI : K ∩ L = ∅ := disjoint_iff_inter_eq_empty.mp hKL
  have : Subsingleton (integralRelativeHomology n (K ∩ L)ᶜ) := by
    rw [hI]
    simpa only [compl_empty] using
      integralRelativeHomology_univ_subsingleton (X := X) n
  exact exists_relative_homology_union_class n K L hK hL a b (Subsingleton.elim _ _)

end DifferentialGeometry.Topology

end
