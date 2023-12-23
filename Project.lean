import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Iso
import Mathlib.GroupTheory.Index


/-
In this document we will prove the following:
Let G be a group, F: (G-FSet) -> FSet, be the functor forgetting the G-action
  Then Aut(F) is equal to the profinite completion of G.

-/

/-
 [] Define the profinite completion of a group G
    (*) Define N := Set of Normal Subgroups of G of finite index
    (*) Define Π_N G/N
    (*) Put a group structure on Π_N G/N
    (*) Construct profinite completion of G as subgroup of Π_N G/N
    (*) Put the topology on the profinite completion
  [] Show the universal prop of the profinite completion
    () Define ι : G →* Ghat
    () Define lift
    () Show ι∘lift = f
    () Show uniqueness
 [] Show equivalence of cat between G-FSet and Ĝ-FSet
    () Show that f : G ⟶* Perm(X) is a continuous map
    () Then it follows from the universal property 
 [] Lemma that says G →* Perm(X) is a continuous group homomorphism
 [] Equivalence of categories between G-FSet and G^-FSet
 [*] Def Aut(F) and Aut(F^), where F & F^ are the respec. forgetful functors 
 [] Induced isomorphism between Aut(F) → Aut(F^)

-/


open CategoryTheory

universe u

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D] (F : C ⥤ D)
variable {G : Type} [Group G]
noncomputable section 

/- I need to put give an instance of TopologicalSpace on G, by putting the discrete topology on it. Then I should be able to define the TopGroupCat 
in a similarly to how TopCat and GroupCat are defined.
-/

instance : TopologicalSpace G := ⊥

instance : TopologicalGroup G where
  continuous_mul := sorry
  continuous_inv := sorry


/-
I'll try to do an explicit version of the Profinite completion, from the definition here https://en.wikipedia.org/wiki/Profinite_group#Profinite_completion
Since trying to definite through limits

-/

structure ProfiniteCompletion (G : Type) [Group G] [TopologicalSpace G] [TopologicalGroup G] where 
  X : Type
  Gpinst : Group X
  Topinst : TopologicalSpace X 
  ι : G →* X
  lift : ∀ (Y : Type) [Group Y] [TopologicalSpace Y] [TopologicalGroup Y], (G →* Y) → (X →* Y)
  ι_lift : 
    ∀ (Y : Type) [Group Y] [TopologicalSpace Y] [TopologicalGroup Y]
    (f : G →* Y)
    (hf : Continuous f),
    (lift Y f)∘ ι = f
  unique : 
    ∀ (Y : Type) [Group Y] [TopologicalSpace Y] [TopologicalGroup Y]
    (f g : X →* Y)
    (hf : Continuous f)
    (hg : Continuous g),
    f ∘ ι = g ∘ ι → f = g


/-
Defining the product of G/N over normal groups N such that [G:N] < ∞, and giving it a group structure.
-/


def ProdGOverN (G: Type) [Group G] : Type := (H : Subgroup G) → (hH: Subgroup.Normal H) → (hf: 0< H.index) → G ⧸ H

instance : Group (ProdGOverN G) where
  mul a b := fun H hH hf => (a H hH hf) * (b H hH hf) 
  mul_assoc := sorry
  one := fun H hH hf => 1
  one_mul := sorry
  mul_one := sorry
  inv a := fun H hH hf => (a H hH hf)⁻¹
  mul_left_inv := sorry


/- 
  Profinite completion is a subgroup of ProdGOverN, such that for all M≤N we have (g N hN hf) ⧸ M = g M hM hf
-/

def inc {G: Type} [Group G] (M : Subgroup G) (_ : Subgroup.Normal M) : G →* G⧸M where
  toFun x := QuotientGroup.mk x
  map_one' := by simp only [OneMemClass.coe_one, QuotientGroup.mk_one]
  map_mul' := by simp only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid, QuotientGroup.mk_mul,
    Subtype.forall, implies_true, forall_const]

def MtoKer {G: Type} [Group G] (N M : Subgroup G) [M.Normal] (f : G→* G⧸M) (HL : N≤M) : N ≤ f.ker := sorry

def incQ {G: Type} [Group G] (N M : Subgroup G) (_ : Subgroup.Normal N) (hM : Subgroup.Normal M) (HL : N≤M) : G⧸N →* G⧸M 
  := QuotientGroup.lift N (inc M hM) (MtoKer _ _ _ HL)

def Ghat (G: Type) [Group G] : Subgroup (ProdGOverN G) where
  carrier := {g | ∀ (N M : Subgroup G) (hN : Subgroup.Normal N) 
  (hM : Subgroup.Normal M) (hf : 0 < N.index) (mf : 0 < M.index) (HL : N≤M), 
  (incQ _ _ hN hM HL (g N hN hf)) = (g M hM mf) }
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

/-
  The topology on Ghat is the product topology, where G is given the discrete topology. 
-/
instance : (TopologicalSpace (Ghat G)) := inferInstance

def ιG {G: Type} [Group G] : G →* (Ghat G) where
  toFun x := {
    val := fun H hH hf => QuotientGroup.mk x
    property := by
      intro N M hN hM hf mf HL
      dsimp
      congr
      done
  }
  map_one' := by
    simp only [QuotientGroup.mk_one, Subgroup.mk_eq_one_iff]
    congr
  map_mul' := by
    intro x y
    simp only [QuotientGroup.mk_mul]
    congr



/-
For some reason, I can't find the category of G-Sets, let alone G-FSets. So I'll define them myself.
-/

/-
Let X be a G-Set, then G embeds in Perm(X), this lemma will just say that this map is indeed a continuous homomorphism
in order to use the universal property of G^ in the follow proof of the equivalence of categories.
-/
lemma ContinuousEmb (G X: Type) [Group G] [TopologicalSpace G] :
  G = G := rfl

/-
There is an equivalence of categories between G-FSets and G^⁻FSets.

Now it would be useful to find where the definiton of G-FSet is in mathlib....

-/
def GFsetEquivGCFset {G : Type} [Group G] [TopologicalSpace G] :
  G = G := rfl

--- After this, the rest should just be computation.

/- 
Definition of the automorphism group of a functor. 

-/

instance : Mul (NatTrans F F) where
  mul a b := NatTrans.vcomp a b

local notation "Aut(F)" => MulAut (NatTrans F F)



/-
Just a sanity check that everything is working fine.

lemma test (f g : Aut(F)) :
  (f*g)⁻¹ = g⁻¹*f⁻¹ := by
    simp only [mul_inv_rev]

-/


/-
Show that the two automorphism groups of the functors are isomorphic 

-/

def AutIso {G : Type} [Group G] [TopologicalSpace G] :
  G ≃ G := by
    rfl
    





