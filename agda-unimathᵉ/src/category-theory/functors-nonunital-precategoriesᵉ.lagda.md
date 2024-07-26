# Functors between nonunital precategories

```agda
module category-theory.functors-nonunital-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-set-magmoidsᵉ
open import category-theory.maps-set-magmoidsᵉ
open import category-theory.nonunital-precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **functor**ᵉ fromᵉ aᵉ [precategory](category-theory.precategories.mdᵉ) `C`ᵉ to aᵉ
precategoryᵉ `D`ᵉ consistsᵉ ofᵉ:

-ᵉ aᵉ mapᵉ `F₀ᵉ : Cᵉ → D`ᵉ onᵉ objects,ᵉ
-ᵉ aᵉ mapᵉ `F₁ᵉ : homᵉ xᵉ yᵉ → homᵉ (F₀ᵉ xᵉ) (F₀ᵉ y)`ᵉ onᵉ morphisms,ᵉ suchᵉ thatᵉ theᵉ followingᵉ
  identityᵉ holdsᵉ:
-ᵉ `F₁ᵉ (gᵉ ∘ᵉ fᵉ) = F₁ᵉ gᵉ ∘ᵉ F₁ᵉ f`.ᵉ

## Definition

### functors between nonunital precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Nonunital-Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Nonunital-Precategoryᵉ l3ᵉ l4ᵉ)
  where

  functor-Nonunital-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  functor-Nonunital-Precategoryᵉ =
    functor-Set-Magmoidᵉ
      ( set-magmoid-Nonunital-Precategoryᵉ Cᵉ)
      ( set-magmoid-Nonunital-Precategoryᵉ Dᵉ)

  obj-functor-Nonunital-Precategoryᵉ :
    functor-Nonunital-Precategoryᵉ →
    obj-Nonunital-Precategoryᵉ Cᵉ →
    obj-Nonunital-Precategoryᵉ Dᵉ
  obj-functor-Nonunital-Precategoryᵉ = pr1ᵉ

  hom-functor-Nonunital-Precategoryᵉ :
    (Fᵉ : functor-Nonunital-Precategoryᵉ) →
    {xᵉ yᵉ : obj-Nonunital-Precategoryᵉ Cᵉ} →
    (fᵉ : hom-Nonunital-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    hom-Nonunital-Precategoryᵉ Dᵉ
      ( obj-functor-Nonunital-Precategoryᵉ Fᵉ xᵉ)
      ( obj-functor-Nonunital-Precategoryᵉ Fᵉ yᵉ)
  hom-functor-Nonunital-Precategoryᵉ Fᵉ = pr1ᵉ (pr2ᵉ Fᵉ)

  map-functor-Nonunital-Precategoryᵉ :
    functor-Nonunital-Precategoryᵉ →
    map-Set-Magmoidᵉ
      ( set-magmoid-Nonunital-Precategoryᵉ Cᵉ)
      ( set-magmoid-Nonunital-Precategoryᵉ Dᵉ)
  pr1ᵉ (map-functor-Nonunital-Precategoryᵉ Fᵉ) =
    obj-functor-Nonunital-Precategoryᵉ Fᵉ
  pr2ᵉ (map-functor-Nonunital-Precategoryᵉ Fᵉ) =
    hom-functor-Nonunital-Precategoryᵉ Fᵉ

  preserves-comp-functor-Nonunital-Precategoryᵉ :
    (Fᵉ : functor-Nonunital-Precategoryᵉ)
    {xᵉ yᵉ zᵉ : obj-Nonunital-Precategoryᵉ Cᵉ}
    (gᵉ : hom-Nonunital-Precategoryᵉ Cᵉ yᵉ zᵉ)
    (fᵉ : hom-Nonunital-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    ( hom-functor-Nonunital-Precategoryᵉ Fᵉ
      ( comp-hom-Nonunital-Precategoryᵉ Cᵉ gᵉ fᵉ)) ＝ᵉ
    ( comp-hom-Nonunital-Precategoryᵉ Dᵉ
      ( hom-functor-Nonunital-Precategoryᵉ Fᵉ gᵉ)
      ( hom-functor-Nonunital-Precategoryᵉ Fᵉ fᵉ))
  preserves-comp-functor-Nonunital-Precategoryᵉ = pr2ᵉ ∘ᵉ pr2ᵉ
```

## Examples

### The identity nonunital functor

Thereᵉ isᵉ anᵉ identityᵉ functorᵉ onᵉ anyᵉ nonunitalᵉ precategory.ᵉ

```agda
id-functor-Nonunital-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Nonunital-Precategoryᵉ l1ᵉ l2ᵉ) →
  functor-Nonunital-Precategoryᵉ Cᵉ Cᵉ
id-functor-Nonunital-Precategoryᵉ Cᵉ =
  id-functor-Set-Magmoidᵉ (set-magmoid-Nonunital-Precategoryᵉ Cᵉ)
```

### Composition of nonunital functors

Anyᵉ twoᵉ compatibleᵉ nonunitalᵉ functorsᵉ canᵉ beᵉ composedᵉ to aᵉ newᵉ nonunitalᵉ
functor.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Aᵉ : Nonunital-Precategoryᵉ l1ᵉ l2ᵉ)
  (Bᵉ : Nonunital-Precategoryᵉ l3ᵉ l4ᵉ)
  (Cᵉ : Nonunital-Precategoryᵉ l5ᵉ l6ᵉ)
  (Gᵉ : functor-Nonunital-Precategoryᵉ Bᵉ Cᵉ)
  (Fᵉ : functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ)
  where

  obj-comp-functor-Nonunital-Precategoryᵉ :
    obj-Nonunital-Precategoryᵉ Aᵉ → obj-Nonunital-Precategoryᵉ Cᵉ
  obj-comp-functor-Nonunital-Precategoryᵉ =
    obj-functor-Nonunital-Precategoryᵉ Bᵉ Cᵉ Gᵉ ∘ᵉ
    obj-functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ Fᵉ

  hom-comp-functor-Nonunital-Precategoryᵉ :
    {xᵉ yᵉ : obj-Nonunital-Precategoryᵉ Aᵉ} →
    hom-Nonunital-Precategoryᵉ Aᵉ xᵉ yᵉ →
    hom-Nonunital-Precategoryᵉ Cᵉ
      ( obj-comp-functor-Nonunital-Precategoryᵉ xᵉ)
      ( obj-comp-functor-Nonunital-Precategoryᵉ yᵉ)
  hom-comp-functor-Nonunital-Precategoryᵉ =
    hom-functor-Nonunital-Precategoryᵉ Bᵉ Cᵉ Gᵉ ∘ᵉ
    hom-functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ Fᵉ

  map-comp-functor-Nonunital-Precategoryᵉ :
    map-Set-Magmoidᵉ
      ( set-magmoid-Nonunital-Precategoryᵉ Aᵉ)
      ( set-magmoid-Nonunital-Precategoryᵉ Cᵉ)
  pr1ᵉ map-comp-functor-Nonunital-Precategoryᵉ =
    obj-comp-functor-Nonunital-Precategoryᵉ
  pr2ᵉ map-comp-functor-Nonunital-Precategoryᵉ =
    hom-comp-functor-Nonunital-Precategoryᵉ

  preserves-comp-comp-functor-Nonunital-Precategoryᵉ =
    preserves-comp-comp-functor-Set-Magmoidᵉ
      ( set-magmoid-Nonunital-Precategoryᵉ Aᵉ)
      ( set-magmoid-Nonunital-Precategoryᵉ Bᵉ)
      ( set-magmoid-Nonunital-Precategoryᵉ Cᵉ)
      ( Gᵉ) (Fᵉ)

  comp-functor-Nonunital-Precategoryᵉ : functor-Nonunital-Precategoryᵉ Aᵉ Cᵉ
  comp-functor-Nonunital-Precategoryᵉ =
    comp-functor-Set-Magmoidᵉ
      ( set-magmoid-Nonunital-Precategoryᵉ Aᵉ)
      ( set-magmoid-Nonunital-Precategoryᵉ Bᵉ)
      ( set-magmoid-Nonunital-Precategoryᵉ Cᵉ)
      ( Gᵉ) (Fᵉ)
```

## Properties

### Extensionality of functors between nonunital precategories

#### Equality of functors is equality of underlying maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Nonunital-Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Nonunital-Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Nonunital-Precategoryᵉ Cᵉ Dᵉ)
  where

  equiv-eq-map-eq-functor-Nonunital-Precategoryᵉ :
    ( Fᵉ ＝ᵉ Gᵉ) ≃ᵉ
    ( map-functor-Nonunital-Precategoryᵉ Cᵉ Dᵉ Fᵉ ＝ᵉ
      map-functor-Nonunital-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
  equiv-eq-map-eq-functor-Nonunital-Precategoryᵉ =
    equiv-eq-map-eq-functor-Set-Magmoidᵉ
      ( set-magmoid-Nonunital-Precategoryᵉ Cᵉ)
      ( set-magmoid-Nonunital-Precategoryᵉ Dᵉ)
      ( Fᵉ) (Gᵉ)

  eq-map-eq-functor-Nonunital-Precategoryᵉ :
    ( Fᵉ ＝ᵉ Gᵉ) →
    ( map-functor-Nonunital-Precategoryᵉ Cᵉ Dᵉ Fᵉ ＝ᵉ
      map-functor-Nonunital-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
  eq-map-eq-functor-Nonunital-Precategoryᵉ =
    map-equivᵉ equiv-eq-map-eq-functor-Nonunital-Precategoryᵉ

  eq-eq-map-functor-Nonunital-Precategoryᵉ :
    ( map-functor-Nonunital-Precategoryᵉ Cᵉ Dᵉ Fᵉ ＝ᵉ
      map-functor-Nonunital-Precategoryᵉ Cᵉ Dᵉ Gᵉ) →
    ( Fᵉ ＝ᵉ Gᵉ)
  eq-eq-map-functor-Nonunital-Precategoryᵉ =
    map-inv-equivᵉ equiv-eq-map-eq-functor-Nonunital-Precategoryᵉ

  is-section-eq-eq-map-functor-Nonunital-Precategoryᵉ :
    eq-map-eq-functor-Nonunital-Precategoryᵉ ∘ᵉ
    eq-eq-map-functor-Nonunital-Precategoryᵉ ~ᵉ
    idᵉ
  is-section-eq-eq-map-functor-Nonunital-Precategoryᵉ =
    is-section-map-inv-equivᵉ equiv-eq-map-eq-functor-Nonunital-Precategoryᵉ

  is-retraction-eq-eq-map-functor-Nonunital-Precategoryᵉ :
    eq-eq-map-functor-Nonunital-Precategoryᵉ ∘ᵉ
    eq-map-eq-functor-Nonunital-Precategoryᵉ ~ᵉ
    idᵉ
  is-retraction-eq-eq-map-functor-Nonunital-Precategoryᵉ =
    is-retraction-map-inv-equivᵉ equiv-eq-map-eq-functor-Nonunital-Precategoryᵉ
```

### Categorical laws for nonunital functor composition

#### Unit laws for nonunital functor composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Nonunital-Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Nonunital-Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Nonunital-Precategoryᵉ Cᵉ Dᵉ)
  where

  left-unit-law-comp-functor-Nonunital-Precategoryᵉ :
    comp-functor-Nonunital-Precategoryᵉ Cᵉ Dᵉ Dᵉ
      ( id-functor-Nonunital-Precategoryᵉ Dᵉ) (Fᵉ) ＝ᵉ
    Fᵉ
  left-unit-law-comp-functor-Nonunital-Precategoryᵉ =
    eq-eq-map-functor-Nonunital-Precategoryᵉ Cᵉ Dᵉ _ _ reflᵉ

  right-unit-law-comp-functor-Nonunital-Precategoryᵉ :
    comp-functor-Nonunital-Precategoryᵉ Cᵉ Cᵉ Dᵉ
      ( Fᵉ) (id-functor-Nonunital-Precategoryᵉ Cᵉ) ＝ᵉ
    Fᵉ
  right-unit-law-comp-functor-Nonunital-Precategoryᵉ = reflᵉ
```

#### Associativity of functor composition

```agda
module _
  {l1ᵉ l1'ᵉ l2ᵉ l2'ᵉ l3ᵉ l3'ᵉ l4ᵉ l4'ᵉ : Level}
  (Aᵉ : Nonunital-Precategoryᵉ l1ᵉ l1'ᵉ)
  (Bᵉ : Nonunital-Precategoryᵉ l2ᵉ l2'ᵉ)
  (Cᵉ : Nonunital-Precategoryᵉ l3ᵉ l3'ᵉ)
  (Dᵉ : Nonunital-Precategoryᵉ l4ᵉ l4'ᵉ)
  (Fᵉ : functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ)
  (Gᵉ : functor-Nonunital-Precategoryᵉ Bᵉ Cᵉ)
  (Hᵉ : functor-Nonunital-Precategoryᵉ Cᵉ Dᵉ)
  where

  associative-comp-functor-Nonunital-Precategoryᵉ :
    comp-functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ Dᵉ
      ( comp-functor-Nonunital-Precategoryᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ) (Fᵉ) ＝ᵉ
    comp-functor-Nonunital-Precategoryᵉ Aᵉ Cᵉ Dᵉ
      ( Hᵉ) (comp-functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ)
  associative-comp-functor-Nonunital-Precategoryᵉ =
    eq-eq-map-functor-Nonunital-Precategoryᵉ Aᵉ Dᵉ _ _ reflᵉ
```

#### Mac Lane pentagon for nonunital functor composition

```text
    (I(GH))Fᵉ ----ᵉ I((GH)Fᵉ)
          /ᵉ        \ᵉ
         /ᵉ          \ᵉ
  ((IH)G)Fᵉ          I(H(GFᵉ))
          \ᵉ        /ᵉ
            \ᵉ    /ᵉ
           (IH)(GFᵉ)
```

Theᵉ proofᵉ remainsᵉ to beᵉ formalized.ᵉ

```text
module _
  {l1ᵉ l1'ᵉ l2ᵉ l2'ᵉ l3ᵉ l3'ᵉ l4ᵉ l4'ᵉ : Level}
  (Aᵉ : Nonunital-Precategoryᵉ l1ᵉ l1'ᵉ)
  (Bᵉ : Nonunital-Precategoryᵉ l2ᵉ l2'ᵉ)
  (Cᵉ : Nonunital-Precategoryᵉ l3ᵉ l3'ᵉ)
  (Dᵉ : Nonunital-Precategoryᵉ l4ᵉ l4'ᵉ)
  (Eᵉ : Nonunital-Precategoryᵉ l4ᵉ l4'ᵉ)
  (Fᵉ : functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ)
  (Gᵉ : functor-Nonunital-Precategoryᵉ Bᵉ Cᵉ)
  (Hᵉ : functor-Nonunital-Precategoryᵉ Cᵉ Dᵉ)
  (Iᵉ : functor-Nonunital-Precategoryᵉ Dᵉ Eᵉ)
  where

  mac-lane-pentagon-comp-functor-Nonunital-Precategoryᵉ :
    coherence-pentagon-identificationsᵉ
      { xᵉ =
        comp-functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ Eᵉ
        ( comp-functor-Nonunital-Precategoryᵉ Bᵉ Dᵉ Eᵉ Iᵉ
          ( comp-functor-Nonunital-Precategoryᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ))
        ( Fᵉ)}
      { comp-functor-Nonunital-Precategoryᵉ Aᵉ Dᵉ Eᵉ Iᵉ
        ( comp-functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ Dᵉ
          ( comp-functor-Nonunital-Precategoryᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ)
          ( Fᵉ))}
      { comp-functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ Eᵉ
        ( comp-functor-Nonunital-Precategoryᵉ Bᵉ Cᵉ Eᵉ
          ( comp-functor-Nonunital-Precategoryᵉ Cᵉ Dᵉ Eᵉ Iᵉ Hᵉ)
          ( Gᵉ))
        ( Fᵉ)}
      { comp-functor-Nonunital-Precategoryᵉ Aᵉ Dᵉ Eᵉ
        ( Iᵉ)
        ( comp-functor-Nonunital-Precategoryᵉ Aᵉ Cᵉ Dᵉ
          ( Hᵉ)
          ( comp-functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ))}
      { comp-functor-Nonunital-Precategoryᵉ Aᵉ Cᵉ Eᵉ
        ( comp-functor-Nonunital-Precategoryᵉ Cᵉ Dᵉ Eᵉ Iᵉ Hᵉ)
        ( comp-functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ)}
      ( associative-comp-functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ Dᵉ Eᵉ
        ( Fᵉ) (comp-functor-Nonunital-Precategoryᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ) (Iᵉ))
      ( apᵉ
        ( λ pᵉ → comp-functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ Eᵉ pᵉ Fᵉ)
        ( invᵉ (associative-comp-functor-Nonunital-Precategoryᵉ Bᵉ Cᵉ Dᵉ Eᵉ Gᵉ Hᵉ Iᵉ)))
      ( apᵉ
        ( λ pᵉ → comp-functor-Nonunital-Precategoryᵉ Aᵉ Dᵉ Eᵉ Iᵉ pᵉ)
        ( associative-comp-functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ))
      ( associative-comp-functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ Cᵉ Eᵉ
        ( Fᵉ) (Gᵉ) (comp-functor-Nonunital-Precategoryᵉ Cᵉ Dᵉ Eᵉ Iᵉ Hᵉ))
      ( invᵉ
        ( associative-comp-functor-Nonunital-Precategoryᵉ Aᵉ Cᵉ Dᵉ Eᵉ
          (comp-functor-Nonunital-Precategoryᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ) Hᵉ Iᵉ))
  mac-lane-pentagon-comp-functor-Nonunital-Precategoryᵉ = {!!ᵉ}
```

## External links

-ᵉ [semifunctor](https://ncatlab.org/nlab/show/semifunctorᵉ) atᵉ $n$Labᵉ