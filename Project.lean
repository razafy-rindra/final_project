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
    () Put a group structure on Π_N G/N
    () Construct profinite completion of G as subgroup of Π_N G/N
    () put the topology on the profinite completion
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
This is the collection of Normal Subgroups of G with finite index. 
-/

def FinIndexNormal (G: Type) [Group G] : Set (Subgroup G):= {H |H.Normal ∧ 0 < H.index }

/-
Defining the Π (H : FinIndexNormal) G/H
-/

def ProdGOverN (G: Type) [Group G] [TopologicalSpace G] [TopologicalGroup G] : Type := (H : FinIndexNormal G) → G ⧸ (H : Subgroup G)



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
    





