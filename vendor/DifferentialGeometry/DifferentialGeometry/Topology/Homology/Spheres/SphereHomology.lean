module

public import DifferentialGeometry.Topology.Homology.SingularPair
public import DifferentialGeometry.Topology.Homology.Naturality
public import DifferentialGeometry.Topology.Homology.MayerVietoris.MayerVietoris
public import DifferentialGeometry.Topology.Homology.Spheres.SphereTopology

@[expose] public section

open CategoryTheory Limits HomologicalComplex AlgebraicTopology
open scoped ContinuousMap

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

section MVone

variable {X : TopCat.{u}} {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

abbrev antiDiag : R ⟶ R ⊞ R := biprod.lift (𝟙 R) (-𝟙 R)

instance mono_antiDiag : Mono (antiDiag R) :=
  mono_of_mono_fac (biprod.lift_fst (𝟙 R) (-𝟙 R))

lemma mvOpenLift_comp_biprodMap_ε :
    mvOpenLift R X U V 0 ≫ biprod.map (ε R (TopCat.of U)) (ε R (TopCat.of V)) =
      ε R (TopCat.of (U ∩ V : Set X)) ≫ antiDiag R := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst, ← Category.assoc, mvOpenLift_fst, Category.assoc,
      biprod.lift_fst, Category.comp_id]
    exact ε_natural' R _
  · rw [Category.assoc, biprod.map_snd, ← Category.assoc, mvOpenLift_snd, Category.assoc,
      biprod.lift_snd, Preadditive.comp_neg, Category.comp_id]
    exact (Preadditive.neg_comp _ _).trans (congrArg Neg.neg (ε_natural' R _))

@[reassoc (attr := simp)]
lemma mvOpenδ_comp_ε :
    mvOpenδ R hU hV hUV 0 ≫ ε R (TopCat.of (U ∩ V : Set X)) = 0 := by
  have h1 : ε R (TopCat.of (U ∩ V : Set X)) =
      (ε R (TopCat.of (U ∩ V : Set X)) ≫ antiDiag R) ≫ biprod.fst := by
    rw [Category.assoc, biprod.lift_fst, Category.comp_id]
  rw [h1, ← mvOpenLift_comp_biprodMap_ε, ← Category.assoc, ← Category.assoc,
    mvOpenδ_mvOpenLift, zero_comp, zero_comp]

def mvOpenδred : singularHomology R X 1 ⟶ reducedHomologyZero R (TopCat.of (U ∩ V : Set X)) :=
  kernel.lift _ (mvOpenδ R hU hV hUV 0) (mvOpenδ_comp_ε R hU hV hUV)

@[reassoc (attr := simp)]
lemma mvOpenδred_ι :
    mvOpenδred R hU hV hUV ≫ reducedHomologyZeroInclusion R (TopCat.of (U ∩ V : Set X)) = mvOpenδ R hU hV hUV 0 :=
  kernel.lift_ι _ _ _

theorem mono_mvOpenδred (hU' : IsZero (singularHomology R (TopCat.of U) 1)) (hV' : IsZero (singularHomology R (TopCat.of V) 1)) :
    Mono (mvOpenδred R hU hV hUV) :=
  haveI := mono_mvOpenδ R hU hV hUV 0 hU' hV'
  mono_of_mono_fac (mvOpenδred_ι R hU hV hUV)

theorem epi_mvOpenδred [IsIso (ε R (TopCat.of U))] [IsIso (ε R (TopCat.of V))] :
    Epi (mvOpenδred R hU hV hUV) := by
  have hex := exact_kernelLift₂₃ (mayerVietoris_exact₁ R hU hV hUV 0)
    (ε R (TopCat.of (U ∩ V : Set X))) (biprod.map (ε R (TopCat.of U)) (ε R (TopCat.of V)))
    (antiDiag R) (mvOpenLift_comp_biprodMap_ε R)
  have hz : IsZero (kernel (biprod.map (ε R (TopCat.of U)) (ε R (TopCat.of V)))) := by
    have : IsIso (biprod.map (ε R (TopCat.of U)) (ε R (TopCat.of V))) :=
      inferInstanceAs
        (IsIso (biprod.mapIso (asIso (ε R (TopCat.of U))) (asIso (ε R (TopCat.of V)))).hom)
    exact (isZero_zero _).of_iso (kernel.ofMono _)
  exact hex.epi_f (hz.eq_zero_of_tgt _)

theorem isIso_mvOpenδred [ContractibleSpace U] [ContractibleSpace V] :
    IsIso (mvOpenδred R hU hV hUV) :=
  haveI := mono_mvOpenδred R hU hV hUV (isZero_of_contractible R U 1 one_ne_zero)
    (isZero_of_contractible R V 1 one_ne_zero)
  haveI := epi_mvOpenδred R hU hV hUV
  isIso_of_mono_of_epi _

def mvOpenδredIso [ContractibleSpace U] [ContractibleSpace V] :
    singularHomology R X 1 ≅ reducedHomologyZero R (TopCat.of (U ∩ V : Set X)) :=
  @asIso _ _ _ _ _ (isIso_mvOpenδred R hU hV hUV)

end MVone

section split

variable (X : TopCat.{u})

abbrev εShortComplex : ShortComplex (ModuleCat.{u} ℤ) :=
  ShortComplex.mk (reducedHomologyZeroInclusion R X) (ε R X) (reducedHomologyZeroInclusion_ε R X)

lemma εShortComplex_exact : (εShortComplex R X).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (ε R X))

variable [Nonempty X]

def ptMap : TopCat.of PUnit.{u + 1} ⟶ X :=
  TopCat.ofHom ⟨fun _ => Classical.arbitrary X, continuous_const⟩

instance isIso_ε_pt : IsIso (ε R (TopCat.of PUnit.{u + 1})) :=
  isIso_ε_of_contractible R PUnit.{u + 1}

def εSection : R ⟶ singularHomology R X 0 := inv (ε R (TopCat.of PUnit.{u + 1})) ≫ singularHomologyMap R (ptMap X) 0

@[reassoc (attr := simp)]
lemma εSection_ε : εSection R X ≫ ε R X = 𝟙 R := by
  rw [εSection, Category.assoc, ε_natural, IsIso.inv_hom_id]

def εSplitting : (εShortComplex R X).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _ (εShortComplex_exact R X) (εSection R X)
    (εSection_ε R X) (inferInstance : Mono (reducedHomologyZeroInclusion R X))

def singularHomologyZeroIsoReducedBiprod : singularHomology R X 0 ≅ reducedHomologyZero R X ⊞ R :=
  (εSplitting R X).isoBinaryBiproduct

lemma singularHomologyZeroIsoReducedBiprod_hom_snd : (singularHomologyZeroIsoReducedBiprod R X).hom ≫ biprod.snd = ε R X :=
  biprod.lift_snd _ _

lemma inl_singularHomologyZeroIsoReducedBiprod_inv : biprod.inl ≫ (singularHomologyZeroIsoReducedBiprod R X).inv = reducedHomologyZeroInclusion R X :=
  biprod.inl_desc _ _

end split

namespace Sphere

abbrev liftedSphere (n : ℕ) : TopCat.{u} := TopCat.of (ULift.{u} (unitSphere n))

def uliftSetHomeomorph {Y : Type} [TopologicalSpace Y] (A : Set Y) :
    ↥(ULift.down ⁻¹' A : Set (ULift.{u} Y)) ≃ₜ ↥A :=
  Homeomorph.ulift.sets rfl

abbrev liftedNorthPoleComplement (n : ℕ) : Set (ULift.{u} (unitSphere n)) := ULift.down ⁻¹' {northPole n}ᶜ

abbrev liftedSouthPoleComplement (n : ℕ) : Set (ULift.{u} (unitSphere n)) := ULift.down ⁻¹' {southPole n}ᶜ

lemma isOpen_liftedNorthPoleComplement (n : ℕ) : IsOpen (liftedNorthPoleComplement.{u} n) :=
  (isOpen_compl_singleton (northPole n)).preimage continuous_uliftDown

lemma isOpen_liftedSouthPoleComplement (n : ℕ) : IsOpen (liftedSouthPoleComplement.{u} n) :=
  (isOpen_compl_singleton (southPole n)).preimage continuous_uliftDown

lemma liftedNorthPoleComplement_union_liftedSouthPoleComplement_eq_univ (n : ℕ) : liftedNorthPoleComplement.{u} n ∪ liftedSouthPoleComplement.{u} n = Set.univ := by
  rw [← Set.preimage_union, cover, Set.preimage_univ]

instance contractibleSpace_liftedNorthPoleComplement (n : ℕ) : ContractibleSpace (liftedNorthPoleComplement.{u} n) :=
  (uliftSetHomeomorph _).contractibleSpace

instance contractibleSpace_liftedSouthPoleComplement (n : ℕ) : ContractibleSpace (liftedSouthPoleComplement.{u} n) :=
  (uliftSetHomeomorph _).contractibleSpace

def liftedEquatorHomotopyEquiv (n : ℕ) : ↥(liftedNorthPoleComplement.{u} (n + 1) ∩ liftedSouthPoleComplement.{u} (n + 1)) ≃ₕ ULift.{u} (unitSphere n) :=
  (uliftSetHomeomorph (({northPole (n + 1)}ᶜ : Set (unitSphere (n + 1))) ∩ {southPole (n + 1)}ᶜ)).toHomotopyEquiv.trans
    ((equatorHomotopyEquiv n).trans Homeomorph.ulift.symm.toHomotopyEquiv)

instance pathConnectedSpace_ulift_succ (n : ℕ) : PathConnectedSpace (ULift.{u} (unitSphere (n + 1))) :=
  Homeomorph.ulift.symm.pathConnectedSpace

instance totallyDisconnectedSpace_ulift_zero : TotallyDisconnectedSpace (ULift.{u} (unitSphere 0)) :=
  inferInstance

theorem isZero_singularHomology_sphere_zero (k : ℕ) (hk : k ≠ 0) : IsZero (singularHomology R (liftedSphere.{u} 0) k) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ k R (liftedSphere.{u} 0) hk

def reducedHomologyZeroLiftedZeroSphereIso : reducedHomologyZero R (liftedSphere.{u} 0) ≅ R :=
  reducedHomologyZeroIsoOfTwoPoints R (liftedSphere.{u} 0) ⟨northPole 0⟩ ⟨southPole 0⟩
    (fun h => northPole_ne_southPole 0 (congrArg ULift.down h))
    (fun z => by
      rcases eq_northPole_or_eq_southPole_zero z.down with h | h
      · exact Or.inl (ULift.ext h)
      · exact Or.inr (ULift.ext h))

instance nonempty_ulift_sphere (n : ℕ) : Nonempty (ULift.{u} (unitSphere n)) := ⟨⟨northPole n⟩⟩

def singularHomologyZeroLiftedZeroSphereIso : singularHomology R (liftedSphere.{u} 0) 0 ≅ R ⊞ R :=
  singularHomologyZeroIsoReducedBiprod R (liftedSphere.{u} 0) ≪≫ biprod.mapIso (reducedHomologyZeroLiftedZeroSphereIso R) (Iso.refl R)

def singularHomologyLiftedSphereSuccIso (n k : ℕ) : singularHomology R (liftedSphere.{u} (n + 1)) (k + 2) ≅ singularHomology R (liftedSphere.{u} n) (k + 1) :=
  mvOpenBoundaryIsoOfContractible R (isOpen_liftedNorthPoleComplement (n + 1)) (isOpen_liftedSouthPoleComplement (n + 1)) (liftedNorthPoleComplement_union_liftedSouthPoleComplement_eq_univ (n + 1))
    (k + 1) k.succ_ne_zero ≪≫ homologyIso R (liftedEquatorHomotopyEquiv n) (k + 1)

def singularHomologyOneLiftedSphereSuccIso (n : ℕ) : singularHomology R (liftedSphere.{u} (n + 1)) 1 ≅ reducedHomologyZero R (liftedSphere.{u} n) :=
  mvOpenδredIso R (isOpen_liftedNorthPoleComplement (n + 1)) (isOpen_liftedSouthPoleComplement (n + 1)) (liftedNorthPoleComplement_union_liftedSouthPoleComplement_eq_univ (n + 1)) ≪≫
    reducedHomologyZeroIso R (liftedEquatorHomotopyEquiv n)

theorem isZero_reducedHomologyZero_sphere_succ (n : ℕ) : IsZero (reducedHomologyZero R (liftedSphere.{u} (n + 1))) :=
  isZero_reducedHomologyZero_of_pathConnected R (liftedSphere.{u} (n + 1))

instance isIso_ε_sphere_succ (n : ℕ) : IsIso (ε R (liftedSphere.{u} (n + 1))) :=
  isIso_ε_of_pathConnected R (liftedSphere.{u} (n + 1))

def singularHomologyZeroLiftedSphereSuccIso (n : ℕ) : singularHomology R (liftedSphere.{u} (n + 1)) 0 ≅ R :=
  asIso (ε R (liftedSphere.{u} (n + 1)))

theorem homology_sphere_aux (n : ℕ) :
    (∀ k, k ≠ n → k ≠ 0 → IsZero (singularHomology R (liftedSphere.{u} n) k)) ∧
      (n ≠ 0 → Nonempty (singularHomology R (liftedSphere.{u} n) n ≅ R)) := by
  induction n with
  | zero => exact ⟨fun k _ hk => isZero_singularHomology_sphere_zero R k hk, fun h => absurd rfl h⟩
  | succ n ih =>
    refine ⟨fun k hk hk0 => ?_, fun _ => ?_⟩
    · obtain _ | _ | k := k
      · exact absurd rfl hk0
      · have hn : n ≠ 0 := by omega
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        have e := singularHomologyOneLiftedSphereSuccIso R (m + 1)
        exact (isZero_reducedHomologyZero_sphere_succ R m).of_iso e
      · have e := singularHomologyLiftedSphereSuccIso R n k
        exact (ih.1 (k + 1) (by omega) (by omega)).of_iso e
    · obtain _ | n := n
      · exact ⟨singularHomologyOneLiftedSphereSuccIso R 0 ≪≫ reducedHomologyZeroLiftedZeroSphereIso R⟩
      · obtain ⟨e⟩ := ih.2 n.succ_ne_zero
        exact ⟨singularHomologyLiftedSphereSuccIso R (n + 1) n ≪≫ e⟩

theorem isZero_singularHomology_sphere (n k : ℕ) (hk : k ≠ n) (hk0 : k ≠ 0) : IsZero (singularHomology R (liftedSphere.{u} n) k) :=
  (homology_sphere_aux R n).1 k hk hk0

def singularHomologyTopLiftedSphereIso (n : ℕ) (hn : n ≠ 0) : singularHomology R (liftedSphere.{u} n) n ≅ R :=
  Classical.choice ((homology_sphere_aux R n).2 hn)

def singularHomologyZeroLiftedSphereIso (n : ℕ) (hn : n ≠ 0) : singularHomology R (liftedSphere.{u} n) 0 ≅ R :=
  match n, hn with
  | m + 1, _ => singularHomologyZeroLiftedSphereSuccIso R m

theorem isZero_reducedHomologyZero_sphere (n : ℕ) (hn : n ≠ 0) : IsZero (reducedHomologyZero R (liftedSphere.{u} n)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact isZero_reducedHomologyZero_sphere_succ R m

theorem homology_sphere (n k : ℕ) :
    (k = n → n ≠ 0 → Nonempty (singularHomology R (liftedSphere.{u} n) k ≅ R)) ∧
      (k ≠ n → k ≠ 0 → IsZero (singularHomology R (liftedSphere.{u} n) k)) ∧
      (n ≠ 0 → Nonempty (singularHomology R (liftedSphere.{u} n) 0 ≅ R)) ∧
      (n = 0 → Nonempty (reducedHomologyZero R (liftedSphere.{u} 0) ≅ R)) ∧
      (n = 0 → Nonempty (singularHomology R (liftedSphere.{u} 0) 0 ≅ R ⊞ R)) ∧
      (n ≠ 0 → IsZero (reducedHomologyZero R (liftedSphere.{u} n))) :=
  ⟨fun hk hn => by subst hk; exact ⟨singularHomologyTopLiftedSphereIso R k hn⟩, isZero_singularHomology_sphere R n k,
    fun hn => ⟨singularHomologyZeroLiftedSphereIso R n hn⟩, fun _ => ⟨reducedHomologyZeroLiftedZeroSphereIso R⟩, fun _ => ⟨singularHomologyZeroLiftedZeroSphereIso R⟩,
    isZero_reducedHomologyZero_sphere R n⟩

def homologyIsoSphere {M : Type u} [TopologicalSpace M] {n : ℕ} (e : M ≃ₕ unitSphere n) (k : ℕ) :
    singularHomology R (TopCat.of M) k ≅ singularHomology R (liftedSphere.{u} n) k :=
  homologyIso R (e.trans Homeomorph.ulift.symm.toHomotopyEquiv) k

def reducedHomologyZeroIsoOfHomotopyEquivSphere {M : Type u} [TopologicalSpace M] {n : ℕ} (e : M ≃ₕ unitSphere n) :
    reducedHomologyZero R (TopCat.of M) ≅ reducedHomologyZero R (liftedSphere.{u} n) :=
  reducedHomologyZeroIso R (e.trans Homeomorph.ulift.symm.toHomotopyEquiv)

theorem isZero_singularHomology_of_homotopyEquiv_sphere {M : Type u} [TopologicalSpace M] {n : ℕ}
    (e : M ≃ₕ unitSphere n) (k : ℕ) (hk : k ≠ n) (hk0 : k ≠ 0) : IsZero (singularHomology R (TopCat.of M) k) :=
  (isZero_singularHomology_sphere R n k hk hk0).of_iso (homologyIsoSphere R e k)

def singularHomologyTopIsoOfHomotopyEquivSphere {M : Type u} [TopologicalSpace M] {n : ℕ}
    (e : M ≃ₕ unitSphere n) (hn : n ≠ 0) : singularHomology R (TopCat.of M) n ≅ R :=
  homologyIsoSphere R e n ≪≫ singularHomologyTopLiftedSphereIso R n hn

def singularHomologyZeroIsoOfHomotopyEquivSphere {M : Type u} [TopologicalSpace M] {n : ℕ}
    (e : M ≃ₕ unitSphere n) (hn : n ≠ 0) : singularHomology R (TopCat.of M) 0 ≅ R :=
  homologyIsoSphere R e 0 ≪≫ singularHomologyZeroLiftedSphereIso R n hn

theorem isZero_reducedHomologyZero_of_homotopyEquiv_sphere {M : Type u} [TopologicalSpace M] {n : ℕ}
    (e : M ≃ₕ unitSphere n) (hn : n ≠ 0) : IsZero (reducedHomologyZero R (TopCat.of M)) :=
  (isZero_reducedHomologyZero_sphere R n hn).of_iso (reducedHomologyZeroIsoOfHomotopyEquivSphere R e)

def reducedHomologyZeroIsoOfHomotopyEquivZeroSphere {M : Type u} [TopologicalSpace M]
    (e : M ≃ₕ unitSphere 0) : reducedHomologyZero R (TopCat.of M) ≅ R :=
  reducedHomologyZeroIsoOfHomotopyEquivSphere R e ≪≫ reducedHomologyZeroLiftedZeroSphereIso R

def singularHomologyZeroIsoOfHomotopyEquivZeroSphere {M : Type u} [TopologicalSpace M]
    (e : M ≃ₕ unitSphere 0) : singularHomology R (TopCat.of M) 0 ≅ R ⊞ R :=
  homologyIsoSphere R e 0 ≪≫ singularHomologyZeroLiftedZeroSphereIso R

section univZero

variable (R₀ : ModuleCat.{0} ℤ)

def singularHomologyUliftIso (n k : ℕ) : singularHomology R₀ (TopCat.of (unitSphere n)) k ≅ singularHomology R₀ (liftedSphere.{0} n) k :=
  homologyIsoSphere R₀ (ContinuousMap.HomotopyEquiv.refl (unitSphere n)) k

theorem isZero_singularHomology_unitSphere (n k : ℕ) (hk : k ≠ n) (hk0 : k ≠ 0) :
    IsZero (singularHomology R₀ (TopCat.of (unitSphere n)) k) :=
  isZero_singularHomology_of_homotopyEquiv_sphere R₀ (ContinuousMap.HomotopyEquiv.refl (unitSphere n)) k hk hk0

def singularHomologyTopUnitSphereIso (n : ℕ) (hn : n ≠ 0) : singularHomology R₀ (TopCat.of (unitSphere n)) n ≅ R₀ :=
  singularHomologyTopIsoOfHomotopyEquivSphere R₀ (ContinuousMap.HomotopyEquiv.refl (unitSphere n)) hn

def singularHomologyZeroUnitSphereIso (n : ℕ) (hn : n ≠ 0) : singularHomology R₀ (TopCat.of (unitSphere n)) 0 ≅ R₀ :=
  singularHomologyZeroIsoOfHomotopyEquivSphere R₀ (ContinuousMap.HomotopyEquiv.refl (unitSphere n)) hn

theorem isZero_reducedHomologyZero_unitSphere (n : ℕ) (hn : n ≠ 0) : IsZero (reducedHomologyZero R₀ (TopCat.of (unitSphere n))) :=
  isZero_reducedHomologyZero_of_homotopyEquiv_sphere R₀ (ContinuousMap.HomotopyEquiv.refl (unitSphere n)) hn

def reducedHomologyZeroUnitZeroSphereIso : reducedHomologyZero R₀ (TopCat.of (unitSphere 0)) ≅ R₀ :=
  reducedHomologyZeroIsoOfHomotopyEquivZeroSphere R₀ (ContinuousMap.HomotopyEquiv.refl (unitSphere 0))

def singularHomologyZeroUnitZeroSphereIso : singularHomology R₀ (TopCat.of (unitSphere 0)) 0 ≅ R₀ ⊞ R₀ :=
  singularHomologyZeroIsoOfHomotopyEquivZeroSphere R₀ (ContinuousMap.HomotopyEquiv.refl (unitSphere 0))

def integralHomologyTopUnitSphereIso (n : ℕ) (hn : n ≠ 0) : singularHomology integerCoefficients (TopCat.of (unitSphere n)) n ≅ integerCoefficients :=
  singularHomologyTopUnitSphereIso integerCoefficients n hn

end univZero

end Sphere

end DifferentialGeometry.Topology.SingularPair
