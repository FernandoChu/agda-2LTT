# Matching objects

```agda
module category-theory.matching-objectsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.cones-precategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.precategory-of-functorsᵉ
open import category-theory.precategoriesᵉ
open import category-theory.constant-functorsᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.limits-precategoriesᵉ
open import category-theory.right-extensions-precategoriesᵉ
open import category-theory.right-kan-extensions-precategoriesᵉ
open import category-theory.terminal-categoryᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ
open import category-theory.inverse-precategoriesᵉ
open import category-theory.reduced-coslice-precategoryᵉ

open import elementary-number-theory.inequality-natural-numbersᵉ

open import foundation.raising-universe-levelsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.function-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.category-of-setsᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
```

</details>

## Idea



## Definitions

```agda
module _
  {l1 l2 : Level} (C : Precategoryᵉ l1 l2)
  (X : functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)))
  (z : obj-Precategoryᵉ C)
  where

  diagram-matching-object :
    functor-Precategoryᵉ
    ( Reduced-Coslice-Precategoryᵉ C z)
    ( Set-Precategoryᵉ (l1 ⊔ l2))
  diagram-matching-object =
    comp-functor-Precategoryᵉ
    ( Reduced-Coslice-Precategoryᵉ C z)
    ( C)
    ( Set-Precategoryᵉ (l1 ⊔ l2))
    ( X)
    ( forgetful-functor-Reduced-Coslice-Precategoryᵉ C z)

  matching-object :
    limit-Precategoryᵉ
      ( Reduced-Coslice-Precategoryᵉ C z)
      ( Set-Precategoryᵉ (l1 ⊔ l2))
      ( diagram-matching-object)
  matching-object =
    limit-Set-Precategoryᵉ
      ( Reduced-Coslice-Precategoryᵉ C z)
      ( diagram-matching-object)

  cone-matching-object :
    cone-Precategoryᵉ
      ( Reduced-Coslice-Precategoryᵉ C z)
      ( Set-Precategoryᵉ (l1 ⊔ l2 ⊔ l2))
      ( diagram-matching-object)
  cone-matching-object =
    cone-limit-Set-Precategoryᵉ
      ( Reduced-Coslice-Precategoryᵉ C z)
      ( diagram-matching-object)

  vertex-matching-object : Setᵉ (l1 ⊔ l2)
  vertex-matching-object =
    vertex-limit-Set-Precategoryᵉ
      ( Reduced-Coslice-Precategoryᵉ C z)
      ( diagram-matching-object)

  type-vertex-matching-object : UUᵉ (l1 ⊔ l2)
  type-vertex-matching-object =
    type-vertex-limit-Set-Precategoryᵉ
      ( Reduced-Coslice-Precategoryᵉ C z)
      ( diagram-matching-object)

  component-matching-object :
    (x : obj-Precategoryᵉ (Reduced-Coslice-Precategoryᵉ C z)) →
    hom-Precategoryᵉ
      (Set-Precategoryᵉ (l1 ⊔ l2 ⊔ l2))
      ( vertex-matching-object)
      ( obj-functor-Precategoryᵉ
        ( Reduced-Coslice-Precategoryᵉ C z)
        ( Set-Precategoryᵉ (l1 ⊔ l2 ⊔ l2))
        ( diagram-matching-object)
        ( x))
  component-matching-object =
    component-limit-Set-Precategoryᵉ
      ( Reduced-Coslice-Precategoryᵉ C z)
      ( diagram-matching-object)
```

The matching functor `M⁻z : [C , Set] → Set`

```agda
module _
  {l1 l2 : Level} (C : Precategoryᵉ l1 l2)
  where

  -- From Yˣz to the matching functor on X
  induced-cone-hom-matching-functor :
    (z : obj-Precategoryᵉ C)
    {Y : functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2))}
    {X : functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2))}
    (p : natural-transformation-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)) Y X) →
    cone-Precategoryᵉ
      ( Reduced-Coslice-Precategoryᵉ C z)
      ( Set-Precategoryᵉ (l1 ⊔ l2))
      ( diagram-matching-object C X z)
  induced-cone-hom-matching-functor z {Y} {X} p =
    make-cone-Precategoryᵉ
      ( Reduced-Coslice-Precategoryᵉ C z)
      ( Set-Precategoryᵉ (l1 ⊔ l2))
      ( diagram-matching-object C X z)
      ( vertex-matching-object C Y z)
      ( λ f →
        hom-family-natural-transformation-Precategoryᵉ
          ( C) (Set-Precategoryᵉ (l1 ⊔ l2)) Y X p
          ( cod-obj-Reduced-Coslice-Precategoryᵉ C z f) ∘ᵉ
        component-matching-object C Y z f)
      ( λ {f} {g} h → lemma f g h)
   where
    module _
      (f  : obj-Precategoryᵉ (Reduced-Coslice-Precategoryᵉ C z))
      (g  : obj-Precategoryᵉ (Reduced-Coslice-Precategoryᵉ C z))
      (h  : hom-Precategoryᵉ (Reduced-Coslice-Precategoryᵉ C z) f g)
      where

      a = cod-obj-Reduced-Coslice-Precategoryᵉ C z f
      b = cod-obj-Reduced-Coslice-Precategoryᵉ C z g
      τf = component-matching-object C Y z f
      τg = component-matching-object C Y z g
      Pa = pr1ᵉ p a
      Pb = pr1ᵉ p b
      Xh = pr1ᵉ (pr2ᵉ X) (pr1ᵉ h)
      Yh = pr1ᵉ (pr2ᵉ Y) (pr1ᵉ h)
      eq1 : Xh ∘ᵉ Pa ＝ᵉ Pb ∘ᵉ Yh
      eq1 =  pr2ᵉ p (pr1ᵉ h)
      eq2 : τg ＝ᵉ Yh ∘ᵉ τf
      eq2 = naturality-cone-Precategoryᵉ
             ( Reduced-Coslice-Precategoryᵉ C z)
             ( Set-Precategoryᵉ (l1 ⊔ l2 ⊔ l2))
             ( diagram-matching-object C Y z)
             ( cone-matching-object C Y z) h
      lemma : Pb ∘ᵉ τg ＝ᵉ Xh ∘ᵉ Pa ∘ᵉ τf
      lemma = apᵉ (Pb ∘ᵉ_) eq2 ∙ᵉ apᵉ (_∘ᵉ τf) (invᵉ (eq1))

  hom-matching-functor :
    (Y : functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)))
    (X : functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)))
    (p : natural-transformation-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)) Y X)
    (z : obj-Precategoryᵉ C) →
    type-vertex-matching-object C Y z →
    type-vertex-matching-object C X z
  hom-matching-functor Y X p z =
      hom-cone-limit-Precategoryᵉ
      ( Reduced-Coslice-Precategoryᵉ C z)
      ( Set-Precategoryᵉ (l1 ⊔ l2))
      ( diagram-matching-object C X z)
      ( matching-object C X z)
      ( induced-cone-hom-matching-functor z {Y} {X} p)

  matching-functor :
    (z : obj-Precategoryᵉ C) →
    functor-Precategoryᵉ
      (functor-precategory-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)))
      (Set-Precategoryᵉ (l1 ⊔ l2))
  pr1ᵉ (matching-functor z) X = vertex-matching-object C X z
  pr1ᵉ (pr2ᵉ (matching-functor z)) {X} {Y} p = hom-matching-functor X Y p z
  pr1ᵉ (pr2ᵉ (pr2ᵉ (matching-functor z))) {X} {Y} {Z} φ ψ =
    eq-htpyᵉ λ τ →
      eq-htpy-hom-family-natural-transformation-Precategoryᵉ
        ( Reduced-Coslice-Precategoryᵉ C z)
        ( Set-Precategoryᵉ (l1 ⊔ l2))
        ( constant-functor-Precategoryᵉ
          ( Reduced-Coslice-Precategoryᵉ C z)
          ( Set-Precategoryᵉ (l1 ⊔ l2))
        ( raise-unit-Setᵉ (l1 ⊔ l2)))
        ( diagram-matching-object C Z z) _ _
        ( λ f → eq-htpyᵉ λ { (map-raiseᵉ starᵉ) → reflᵉ})
  pr2ᵉ (pr2ᵉ (pr2ᵉ (matching-functor z))) X =
    eq-htpyᵉ λ τ →
      eq-htpy-hom-family-natural-transformation-Precategoryᵉ
        ( Reduced-Coslice-Precategoryᵉ C z)
        ( Set-Precategoryᵉ (l1 ⊔ l2))
        ( constant-functor-Precategoryᵉ
          ( Reduced-Coslice-Precategoryᵉ C z)
          ( Set-Precategoryᵉ (l1 ⊔ l2))
        ( raise-unit-Setᵉ (l1 ⊔ l2)))
        ( diagram-matching-object C X z) _ _
        ( λ f → eq-htpyᵉ λ { (map-raiseᵉ starᵉ) → reflᵉ})
```

### The natural transformation `(-)z → M⁻z`

```agda
  induced-cone-hom-family-matching-natural-transformation :
    (X : functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)))
    (z : obj-Precategoryᵉ C) →
    cone-Precategoryᵉ
      ( Reduced-Coslice-Precategoryᵉ C z)
      ( Set-Precategoryᵉ (l1 ⊔ l2))
      ( diagram-matching-object C X z)
  induced-cone-hom-family-matching-natural-transformation X z =
     make-cone-Precategoryᵉ
      ( Reduced-Coslice-Precategoryᵉ C z)
      ( Set-Precategoryᵉ (l1 ⊔ l2))
      ( diagram-matching-object C X z)
      ( obj-functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)) X z)
      ( λ f → hom-functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2))
        ( X)
        ( hom-obj-Reduced-Coslice-Precategoryᵉ C z f))
      λ {f} {g} h → invᵉ
        ( apᵉ
          ( hom-functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)) X)
          ( invᵉ (pr2ᵉ h))) ∙ᵉ
        ( preserves-comp-functor-Precategoryᵉ
          ( C)
          ( Set-Precategoryᵉ (l1 ⊔ l2))
          ( X)
          ( pr1ᵉ h)
          ( pr2ᵉ (pr1ᵉ f)))

  hom-family-matching-natural-transformation :
    (X : functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)))
    (z : obj-Precategoryᵉ C) →
    type-Setᵉ
      ( obj-functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)) X z) →
    type-vertex-matching-object C X z
  hom-family-matching-natural-transformation X z =
      hom-cone-limit-Precategoryᵉ
      ( Reduced-Coslice-Precategoryᵉ C z)
      ( Set-Precategoryᵉ (l1 ⊔ l2))
      ( diagram-matching-object C X z)
      ( matching-object C X z)
      ( induced-cone-hom-family-matching-natural-transformation X z)

  matching-natural-transformation :
    (z : obj-Precategoryᵉ C) →
    natural-transformation-Precategoryᵉ
      ( functor-precategory-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)))
      ( Set-Precategoryᵉ (l1 ⊔ l2))
      ( ev-functor-Precategoryᵉ
        ( C)
        ( Set-Precategoryᵉ (l1 ⊔ l2))
        ( z ))
      ( matching-functor z)
  pr1ᵉ (matching-natural-transformation z) X =
    hom-family-matching-natural-transformation X z
  pr2ᵉ (matching-natural-transformation z) {Y} {X} p =
    eq-htpyᵉ λ τ →
      eq-htpy-hom-family-natural-transformation-Precategoryᵉ
        ( Reduced-Coslice-Precategoryᵉ C z)
        ( Set-Precategoryᵉ (l1 ⊔ l2))
        ( constant-functor-Precategoryᵉ
          ( Reduced-Coslice-Precategoryᵉ C z)
          ( Set-Precategoryᵉ (l1 ⊔ l2))
        ( raise-unit-Setᵉ (l1 ⊔ l2)))
        ( diagram-matching-object C X z) _ _
        ( λ f → eq-htpyᵉ λ { (map-raiseᵉ starᵉ) →
          (htpy-eqᵉ (invᵉ (pr2ᵉ p (pr2ᵉ (pr1ᵉ f)))) τ)})
```
