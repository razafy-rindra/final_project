import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Iso
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Category.Profinite.Basic
/-
# In this document we will prove the following:

*Let G be a group, F: (G-FSet) -> FSet, be the functor forgetting the G-action, then Aut(F) is equal to the profinite completion of G.*

## What is left to do?

  [] Show the universal prop of the profinite completion
    (*) Define ι : G →* Ghat
    () Define lift
    () Show ι∘lift = f
    () Show uniqueness
 [] Show equivalence of cat between G-FSet and Ĝ-FSet
    () Show that f : G ⟶* Perm(X) is a continuous map
    () Then it follows from the universal property 
 [] Lemma that says G →* Perm(X) is a continuous group homomorphism
 [] Equivalence of categories between G-FSet and G^-FSet 
 [] Induced isomorphism between Aut(F) → Aut(F^)

-/


open CategoryTheory

universe u

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D] (F : C ⥤ D)
variable {G : Type} [Group G]
noncomputable section 

/- 
# Preamble

Put a topology on G
-/

instance : TopologicalSpace G := ⊥

instance : DiscreteTopology G where
  eq_bot := by rfl

instance : TopologicalGroup G where
  continuous_mul := by
    apply continuous_of_discreteTopology
  continuous_inv := by
    apply continuous_of_discreteTopology


/-
# The Profinite Completion

We will give an explicit definition of the Profinite completion, the definition through limits seem to be more of a pain to go through.

## The Profinite Completion is definied as a subgroup of Π_N G/N (where [G:N]<∞) such that (g mod N) mod M = g mod M for all N≤M

## The universal property is given by the following commutative diagram

Ghat -∃! fhat---> Y
|                 |
ι                 =
|                 |
G ---f----------> Y

Where Y is any profinite group (i.e. compact, totally disconnected, Haussdorf, topological group) and f is a continuous homomorphism.
*See the definition here https://en.wikipedia.org/wiki/Profinite_group#Profinite_completion*
-/


structure ProfiniteCompletion (G : Type) [Group G] [TopologicalSpace G] [TopologicalGroup G] where 
  X : Type
  Gpinst : Group X
  Topinst : TopologicalSpace X 
  ι : G →* X
  lift : ∀ (Y : Type) [Group Y] [TopologicalSpace Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] [TopologicalGroup Y] 
    (f: G →* Y)
    (hf : Continuous f), (X →* Y)
  ι_lift : 
    ∀ (Y : Type) [Group Y] [TopologicalSpace Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] [TopologicalGroup Y]
    (f : G →* Y)
    (hf : Continuous f),
    (lift Y f hf)∘ ι = f
  unique : 
    ∀ (Y : Type) [Group Y] [TopologicalSpace Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] [TopologicalGroup Y]
    (f g : X →* Y)
    (hf : Continuous f)
    (hg : Continuous g),
    f ∘ ι = g ∘ ι → f = g

/-
Defining Π G/N over normal groups N such that [G:N] < ∞, and giving it a group structure.
-/
def ProdGOverN (G: Type) [Group G] : Type := (H : Subgroup G) → (hH: Subgroup.Normal H) → (hf: 0< H.index) → G ⧸ H

instance : Mul (ProdGOverN G) where
  mul a b := fun H hH hf => (a H hH hf) * (b H hH hf) 

instance : One (ProdGOverN G) where
  one := fun _ _ _ => 1

instance : Inv (ProdGOverN G) where
  inv a := fun H hH hf => (a H hH hf)⁻¹


instance : Group (ProdGOverN G) where
  mul_assoc := by
    intro a b c
    
    sorry
  one_mul := by
    intro a
    sorry
  mul_one := sorry
  mul_left_inv := sorry


/- 
  Profinite completion is a subgroup of ProdGOverN, such that for all M≤N we have (g N hN hf) ⧸ M = g M hM hf
-/

def inc {G: Type} [Group G] (M : Subgroup G) (_ : Subgroup.Normal M) : G →* G⧸M where
  toFun x := QuotientGroup.mk x
  map_one' := by simp only [OneMemClass.coe_one, QuotientGroup.mk_one]
  map_mul' := by simp only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid, QuotientGroup.mk_mul,
    Subtype.forall, implies_true, forall_const]

def MtoKer {G: Type} [Group G] (N M : Subgroup G) [M.Normal] (f : G→* G⧸M) (HL : N≤M) : N ≤ f.ker := by
  intro x h 
  change f x = 1
  
  sorry

def incQ {G: Type} [Group G] (N M : Subgroup G) (_ : Subgroup.Normal N) (hM : Subgroup.Normal M) (HL : N≤M) : G⧸N →* G⧸M 
  := QuotientGroup.lift N (inc M hM) (MtoKer _ _ _ HL)


/-
  The underlying group structure of the profinite completion.
-/
def X (G: Type) [Group G] : Subgroup (ProdGOverN G) where
  carrier := {g | ∀ (N M : Subgroup G) (hN : Subgroup.Normal N) 
  (hM : Subgroup.Normal M) (hf : 0 < N.index) (mf : 0 < M.index) (HL : N≤M), 
  (incQ _ _ hN hM HL (g N hN hf)) = (g M hM mf) }
  mul_mem' := by 
    simp only [Set.mem_setOf_eq]
    intro a b g1 g2 N M hN hM hf mf HL
    
    sorry
  one_mem' := sorry
  inv_mem' := sorry

/-
  The topology on Ghat is the product topology, where G is given the discrete topology. 
-/
instance : (TopologicalSpace (X G)) := inferInstance
instance : (TopologicalGroup (X G)) := inferInstance

/-
  The inclusion homomorphism ιG : G →* Ghat
-/
def ιG {G: Type} [Group G] : G →* (X G) where
  toFun x := {
    val := fun H _ _ => QuotientGroup.mk x
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


def lift (Y : Type) {G : Type} [Group G] [Group Y] [TopologicalSpace Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] [TopologicalGroup Y] 
    (f: G →* Y)
    (hf : Continuous f) : ((X G) →* Y) where
      toFun := sorry
      map_one' := sorry
      map_mul' := sorry
    
def Ghat : ProfiniteCompletion G where
  X := X G
  Gpinst := inferInstance
  Topinst := inferInstance
  ι := ιG
  lift Y _ _ _ _  _ f hf := lift Y f hf 
  ι_lift := by
    intro Y _ _ _ _ _ f hf
    dsimp
    ext
    simp
    sorry -- I need the definition of lift!
  unique := by
    intro Y _ _ _ _ _ f hf cf chf e 
    -- probably show this by using the fact that im(ιG) is dense in Ghat?
    sorry
    

/-
For some reason, I can't find the category of G-Sets, let alone G-FSets. So I'll define them myself? Maybe they have another name.
-/


/- 
# Definition of the automorphism group of a functor. 

Aut(F) = {μ : F→F | μ is a natural transformation} 
-/

instance : Mul (NatTrans F F) where
  mul a b := NatTrans.vcomp a b

local notation "Aut(F)" => MulAut (NatTrans F F)




/-
  The rest of this document consists of placeholder lemma's/defintions 
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
Show that the two automorphism groups of the functors are isomorphic 

-/

def AutIso {G : Type} [Group G] [TopologicalSpace G] :
  G ≃ G := by
    rfl
    





