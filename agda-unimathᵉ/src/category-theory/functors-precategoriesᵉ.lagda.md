# Functors between precategories

```agda
module category-theory.functors-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-set-magmoidsᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.maps-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **functor**ᵉ fromᵉ aᵉ [precategory](category-theory.precategories.mdᵉ) `C`ᵉ to aᵉ
precategoryᵉ `D`ᵉ consistsᵉ ofᵉ:

-ᵉ aᵉ mapᵉ `F₀ᵉ : Cᵉ → D`ᵉ onᵉ objects,ᵉ
-ᵉ aᵉ mapᵉ `F₁ᵉ : homᵉ xᵉ yᵉ → homᵉ (F₀ᵉ xᵉ) (F₀ᵉ y)`ᵉ onᵉ morphisms,ᵉ suchᵉ thatᵉ theᵉ followingᵉ
  identitiesᵉ holdᵉ:
-ᵉ `F₁ᵉ id_xᵉ = id_(F₀ᵉ x)`,ᵉ
-ᵉ `F₁ᵉ (gᵉ ∘ᵉ fᵉ) = F₁ᵉ gᵉ ∘ᵉ F₁ᵉ f`.ᵉ

## Definition

### The predicate on maps between precategories of being a functor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  preserves-comp-hom-prop-map-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  preserves-comp-hom-prop-map-Precategoryᵉ =
    preserves-comp-hom-prop-map-Set-Magmoidᵉ
      ( set-magmoid-Precategoryᵉ Cᵉ)
      ( set-magmoid-Precategoryᵉ Dᵉ)
      (Fᵉ)

  preserves-comp-hom-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  preserves-comp-hom-map-Precategoryᵉ =
    type-Propᵉ preserves-comp-hom-prop-map-Precategoryᵉ

  is-prop-preserves-comp-hom-map-Precategoryᵉ :
    is-propᵉ preserves-comp-hom-map-Precategoryᵉ
  is-prop-preserves-comp-hom-map-Precategoryᵉ =
    is-prop-type-Propᵉ preserves-comp-hom-prop-map-Precategoryᵉ

  preserves-id-hom-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l4ᵉ)
  preserves-id-hom-map-Precategoryᵉ =
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    ( hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ (id-hom-Precategoryᵉ Cᵉ {xᵉ})) ＝ᵉ
    ( id-hom-Precategoryᵉ Dᵉ {obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ})

  is-prop-preserves-id-hom-map-Precategoryᵉ :
    is-propᵉ preserves-id-hom-map-Precategoryᵉ
  is-prop-preserves-id-hom-map-Precategoryᵉ =
    is-prop-Πᵉ
      ( λ xᵉ →
        is-set-hom-Precategoryᵉ Dᵉ
          ( obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
          ( obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
          ( hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ (id-hom-Precategoryᵉ Cᵉ {xᵉ}))
          ( id-hom-Precategoryᵉ Dᵉ {obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ}))

  preserves-id-hom-prop-map-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l4ᵉ)
  pr1ᵉ preserves-id-hom-prop-map-Precategoryᵉ =
    preserves-id-hom-map-Precategoryᵉ
  pr2ᵉ preserves-id-hom-prop-map-Precategoryᵉ =
    is-prop-preserves-id-hom-map-Precategoryᵉ

  is-functor-prop-map-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-functor-prop-map-Precategoryᵉ =
    product-Propᵉ
      preserves-comp-hom-prop-map-Precategoryᵉ
      preserves-id-hom-prop-map-Precategoryᵉ

  is-functor-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-functor-map-Precategoryᵉ = type-Propᵉ is-functor-prop-map-Precategoryᵉ

  is-prop-is-functor-map-Precategoryᵉ :
    is-propᵉ is-functor-map-Precategoryᵉ
  is-prop-is-functor-map-Precategoryᵉ =
    is-prop-type-Propᵉ is-functor-prop-map-Precategoryᵉ

  preserves-comp-is-functor-map-Precategoryᵉ :
    is-functor-map-Precategoryᵉ → preserves-comp-hom-map-Precategoryᵉ
  preserves-comp-is-functor-map-Precategoryᵉ = pr1ᵉ

  preserves-id-is-functor-map-Precategoryᵉ :
    is-functor-map-Precategoryᵉ → preserves-id-hom-map-Precategoryᵉ
  preserves-id-is-functor-map-Precategoryᵉ = pr2ᵉ
```

### functors between precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  functor-Precategoryᵉ =
    Σᵉ ( obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ)
      ( λ F₀ᵉ →
        Σᵉ ( {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
            (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
            hom-Precategoryᵉ Dᵉ (F₀ᵉ xᵉ) (F₀ᵉ yᵉ))
          ( λ F₁ᵉ → is-functor-map-Precategoryᵉ Cᵉ Dᵉ (F₀ᵉ ,ᵉ F₁ᵉ)))

  obj-functor-Precategoryᵉ :
    functor-Precategoryᵉ → obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ
  obj-functor-Precategoryᵉ = pr1ᵉ

  hom-functor-Precategoryᵉ :
    (Fᵉ : functor-Precategoryᵉ) →
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    hom-Precategoryᵉ Dᵉ
      ( obj-functor-Precategoryᵉ Fᵉ xᵉ)
      ( obj-functor-Precategoryᵉ Fᵉ yᵉ)
  hom-functor-Precategoryᵉ Fᵉ = pr1ᵉ (pr2ᵉ Fᵉ)

  map-functor-Precategoryᵉ : functor-Precategoryᵉ → map-Precategoryᵉ Cᵉ Dᵉ
  pr1ᵉ (map-functor-Precategoryᵉ Fᵉ) = obj-functor-Precategoryᵉ Fᵉ
  pr2ᵉ (map-functor-Precategoryᵉ Fᵉ) = hom-functor-Precategoryᵉ Fᵉ

  is-functor-functor-Precategoryᵉ :
    (Fᵉ : functor-Precategoryᵉ) →
    is-functor-map-Precategoryᵉ Cᵉ Dᵉ (map-functor-Precategoryᵉ Fᵉ)
  is-functor-functor-Precategoryᵉ = pr2ᵉ ∘ᵉ pr2ᵉ

  preserves-comp-functor-Precategoryᵉ :
    (Fᵉ : functor-Precategoryᵉ) {xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ}
    (gᵉ : hom-Precategoryᵉ Cᵉ yᵉ zᵉ) (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    ( hom-functor-Precategoryᵉ Fᵉ (comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ)) ＝ᵉ
    ( comp-hom-Precategoryᵉ Dᵉ
      ( hom-functor-Precategoryᵉ Fᵉ gᵉ)
      ( hom-functor-Precategoryᵉ Fᵉ fᵉ))
  preserves-comp-functor-Precategoryᵉ Fᵉ =
    preserves-comp-is-functor-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Fᵉ)
      ( is-functor-functor-Precategoryᵉ Fᵉ)

  preserves-id-functor-Precategoryᵉ :
    (Fᵉ : functor-Precategoryᵉ) (xᵉ : obj-Precategoryᵉ Cᵉ) →
    ( hom-functor-Precategoryᵉ Fᵉ (id-hom-Precategoryᵉ Cᵉ {xᵉ})) ＝ᵉ
    ( id-hom-Precategoryᵉ Dᵉ {obj-functor-Precategoryᵉ Fᵉ xᵉ})
  preserves-id-functor-Precategoryᵉ Fᵉ =
    preserves-id-is-functor-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Fᵉ)
      ( is-functor-functor-Precategoryᵉ Fᵉ)
```

## Examples

### The identity functor

Thereᵉ isᵉ anᵉ identityᵉ functorᵉ onᵉ anyᵉ precategory.ᵉ

```agda
id-functor-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) → functor-Precategoryᵉ Cᵉ Cᵉ
pr1ᵉ (id-functor-Precategoryᵉ Cᵉ) = idᵉ
pr1ᵉ (pr2ᵉ (id-functor-Precategoryᵉ Cᵉ)) = idᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (id-functor-Precategoryᵉ Cᵉ))) gᵉ fᵉ = reflᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (id-functor-Precategoryᵉ Cᵉ))) xᵉ = reflᵉ
```

### Composition of functors

Anyᵉ twoᵉ compatibleᵉ functorsᵉ canᵉ beᵉ composedᵉ to aᵉ newᵉ functor.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Aᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Bᵉ : Precategoryᵉ l3ᵉ l4ᵉ) (Cᵉ : Precategoryᵉ l5ᵉ l6ᵉ)
  (Gᵉ : functor-Precategoryᵉ Bᵉ Cᵉ) (Fᵉ : functor-Precategoryᵉ Aᵉ Bᵉ)
  where

  obj-comp-functor-Precategoryᵉ : obj-Precategoryᵉ Aᵉ → obj-Precategoryᵉ Cᵉ
  obj-comp-functor-Precategoryᵉ =
    obj-functor-Precategoryᵉ Bᵉ Cᵉ Gᵉ ∘ᵉ obj-functor-Precategoryᵉ Aᵉ Bᵉ Fᵉ

  hom-comp-functor-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Aᵉ} →
    hom-Precategoryᵉ Aᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Cᵉ
      ( obj-comp-functor-Precategoryᵉ xᵉ)
      ( obj-comp-functor-Precategoryᵉ yᵉ)
  hom-comp-functor-Precategoryᵉ =
    hom-functor-Precategoryᵉ Bᵉ Cᵉ Gᵉ ∘ᵉ hom-functor-Precategoryᵉ Aᵉ Bᵉ Fᵉ

  map-comp-functor-Precategoryᵉ : map-Precategoryᵉ Aᵉ Cᵉ
  pr1ᵉ map-comp-functor-Precategoryᵉ = obj-comp-functor-Precategoryᵉ
  pr2ᵉ map-comp-functor-Precategoryᵉ = hom-comp-functor-Precategoryᵉ

  preserves-comp-comp-functor-Precategoryᵉ :
    preserves-comp-hom-map-Precategoryᵉ Aᵉ Cᵉ map-comp-functor-Precategoryᵉ
  preserves-comp-comp-functor-Precategoryᵉ gᵉ fᵉ =
    ( apᵉ
      ( hom-functor-Precategoryᵉ Bᵉ Cᵉ Gᵉ)
      ( preserves-comp-functor-Precategoryᵉ Aᵉ Bᵉ Fᵉ gᵉ fᵉ)) ∙ᵉ
    ( preserves-comp-functor-Precategoryᵉ Bᵉ Cᵉ Gᵉ
      ( hom-functor-Precategoryᵉ Aᵉ Bᵉ Fᵉ gᵉ)
      ( hom-functor-Precategoryᵉ Aᵉ Bᵉ Fᵉ fᵉ))

  preserves-id-comp-functor-Precategoryᵉ :
    preserves-id-hom-map-Precategoryᵉ Aᵉ Cᵉ map-comp-functor-Precategoryᵉ
  preserves-id-comp-functor-Precategoryᵉ xᵉ =
    ( apᵉ
      ( hom-functor-Precategoryᵉ Bᵉ Cᵉ Gᵉ)
      ( preserves-id-functor-Precategoryᵉ Aᵉ Bᵉ Fᵉ xᵉ)) ∙ᵉ
    ( preserves-id-functor-Precategoryᵉ Bᵉ Cᵉ Gᵉ
      ( obj-functor-Precategoryᵉ Aᵉ Bᵉ Fᵉ xᵉ))

  comp-functor-Precategoryᵉ : functor-Precategoryᵉ Aᵉ Cᵉ
  pr1ᵉ comp-functor-Precategoryᵉ = obj-comp-functor-Precategoryᵉ
  pr1ᵉ (pr2ᵉ comp-functor-Precategoryᵉ) =
    hom-functor-Precategoryᵉ Bᵉ Cᵉ Gᵉ ∘ᵉ hom-functor-Precategoryᵉ Aᵉ Bᵉ Fᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ comp-functor-Precategoryᵉ)) =
    preserves-comp-comp-functor-Precategoryᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ comp-functor-Precategoryᵉ)) =
    preserves-id-comp-functor-Precategoryᵉ
```

## Properties

### Extensionality of functors between precategories

#### Equality of functors is equality of underlying maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  equiv-eq-map-eq-functor-Precategoryᵉ :
    (Fᵉ ＝ᵉ Gᵉ) ≃ᵉ (map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ ＝ᵉ map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
  equiv-eq-map-eq-functor-Precategoryᵉ =
    equiv-ap-embᵉ
      ( comp-embᵉ
        ( emb-subtypeᵉ (is-functor-prop-map-Precategoryᵉ Cᵉ Dᵉ))
        ( emb-equivᵉ
          ( inv-associative-Σᵉ
            ( obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ)
            ( λ F₀ᵉ →
              { xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
              hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
              hom-Precategoryᵉ Dᵉ (F₀ᵉ xᵉ) (F₀ᵉ yᵉ))
            ( pr1ᵉ ∘ᵉ is-functor-prop-map-Precategoryᵉ Cᵉ Dᵉ))))

  eq-map-eq-functor-Precategoryᵉ :
    (Fᵉ ＝ᵉ Gᵉ) → (map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ ＝ᵉ map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
  eq-map-eq-functor-Precategoryᵉ =
    map-equivᵉ equiv-eq-map-eq-functor-Precategoryᵉ

  eq-eq-map-functor-Precategoryᵉ :
    (map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ ＝ᵉ map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ) → (Fᵉ ＝ᵉ Gᵉ)
  eq-eq-map-functor-Precategoryᵉ =
    map-inv-equivᵉ equiv-eq-map-eq-functor-Precategoryᵉ

  is-section-eq-eq-map-functor-Precategoryᵉ :
    eq-map-eq-functor-Precategoryᵉ ∘ᵉ eq-eq-map-functor-Precategoryᵉ ~ᵉ idᵉ
  is-section-eq-eq-map-functor-Precategoryᵉ =
    is-section-map-inv-equivᵉ equiv-eq-map-eq-functor-Precategoryᵉ

  is-retraction-eq-eq-map-functor-Precategoryᵉ :
    eq-eq-map-functor-Precategoryᵉ ∘ᵉ eq-map-eq-functor-Precategoryᵉ ~ᵉ idᵉ
  is-retraction-eq-eq-map-functor-Precategoryᵉ =
    is-retraction-map-inv-equivᵉ equiv-eq-map-eq-functor-Precategoryᵉ
```

#### Equality of functors is homotopy of underlying maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  htpy-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-functor-Precategoryᵉ =
    htpy-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  equiv-htpy-eq-functor-Precategoryᵉ : (Fᵉ ＝ᵉ Gᵉ) ≃ᵉ htpy-functor-Precategoryᵉ
  equiv-htpy-eq-functor-Precategoryᵉ =
    ( equiv-htpy-eq-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)) ∘eᵉ
    ( equiv-eq-map-eq-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)

  htpy-eq-functor-Precategoryᵉ : Fᵉ ＝ᵉ Gᵉ → htpy-functor-Precategoryᵉ
  htpy-eq-functor-Precategoryᵉ =
    map-equivᵉ equiv-htpy-eq-functor-Precategoryᵉ

  eq-htpy-functor-Precategoryᵉ : htpy-functor-Precategoryᵉ → Fᵉ ＝ᵉ Gᵉ
  eq-htpy-functor-Precategoryᵉ =
    map-inv-equivᵉ equiv-htpy-eq-functor-Precategoryᵉ

  is-section-eq-htpy-functor-Precategoryᵉ :
    htpy-eq-functor-Precategoryᵉ ∘ᵉ eq-htpy-functor-Precategoryᵉ ~ᵉ idᵉ
  is-section-eq-htpy-functor-Precategoryᵉ =
    is-section-map-inv-equivᵉ equiv-htpy-eq-functor-Precategoryᵉ

  is-retraction-eq-htpy-functor-Precategoryᵉ :
    eq-htpy-functor-Precategoryᵉ ∘ᵉ htpy-eq-functor-Precategoryᵉ ~ᵉ idᵉ
  is-retraction-eq-htpy-functor-Precategoryᵉ =
    is-retraction-map-inv-equivᵉ equiv-htpy-eq-functor-Precategoryᵉ
```

### Functors preserve isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  where

  hom-inv-preserves-is-iso-functor-Precategoryᵉ :
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    is-iso-Precategoryᵉ Cᵉ fᵉ →
    hom-Precategoryᵉ Dᵉ
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ)
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
  hom-inv-preserves-is-iso-functor-Precategoryᵉ fᵉ is-iso-fᵉ =
    hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ (hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ)

  is-right-inv-preserves-is-iso-functor-Precategoryᵉ :
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    (is-iso-fᵉ : is-iso-Precategoryᵉ Cᵉ fᵉ) →
    comp-hom-Precategoryᵉ Dᵉ
      ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ)
      ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ (hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ)) ＝ᵉ
    id-hom-Precategoryᵉ Dᵉ
  is-right-inv-preserves-is-iso-functor-Precategoryᵉ fᵉ is-iso-fᵉ =
    ( invᵉ
      ( preserves-comp-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
        ( fᵉ)
        ( hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ))) ∙ᵉ
    ( apᵉ
      ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( is-section-hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ)) ∙ᵉ
    ( preserves-id-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ)

  is-left-inv-preserves-is-iso-functor-Precategoryᵉ :
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    (is-iso-fᵉ : is-iso-Precategoryᵉ Cᵉ fᵉ) →
    comp-hom-Precategoryᵉ Dᵉ
      ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ (hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ))
      ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ) ＝ᵉ
    id-hom-Precategoryᵉ Dᵉ
  is-left-inv-preserves-is-iso-functor-Precategoryᵉ fᵉ is-iso-fᵉ =
    ( invᵉ
      ( preserves-comp-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
        ( hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ)
        ( fᵉ))) ∙ᵉ
    ( apᵉ
      ( hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( is-retraction-hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ)) ∙ᵉ
    ( preserves-id-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)

  preserves-is-iso-functor-Precategoryᵉ :
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    is-iso-Precategoryᵉ Cᵉ fᵉ →
    is-iso-Precategoryᵉ Dᵉ (hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ)
  pr1ᵉ (preserves-is-iso-functor-Precategoryᵉ fᵉ is-iso-fᵉ) =
    hom-inv-preserves-is-iso-functor-Precategoryᵉ fᵉ is-iso-fᵉ
  pr1ᵉ (pr2ᵉ (preserves-is-iso-functor-Precategoryᵉ fᵉ is-iso-fᵉ)) =
    is-right-inv-preserves-is-iso-functor-Precategoryᵉ fᵉ is-iso-fᵉ
  pr2ᵉ (pr2ᵉ (preserves-is-iso-functor-Precategoryᵉ fᵉ is-iso-fᵉ)) =
    is-left-inv-preserves-is-iso-functor-Precategoryᵉ fᵉ is-iso-fᵉ

  preserves-iso-functor-Precategoryᵉ :
    iso-Precategoryᵉ Cᵉ xᵉ yᵉ →
    iso-Precategoryᵉ Dᵉ
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ)
  pr1ᵉ (preserves-iso-functor-Precategoryᵉ fᵉ) =
    hom-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ (hom-iso-Precategoryᵉ Cᵉ fᵉ)
  pr2ᵉ (preserves-iso-functor-Precategoryᵉ fᵉ) =
    preserves-is-iso-functor-Precategoryᵉ
      ( hom-iso-Precategoryᵉ Cᵉ fᵉ)
      ( is-iso-iso-Precategoryᵉ Cᵉ fᵉ)
```

### Categorical laws for functor composition

#### Unit laws for functor composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  left-unit-law-comp-functor-Precategoryᵉ :
    comp-functor-Precategoryᵉ Cᵉ Dᵉ Dᵉ (id-functor-Precategoryᵉ Dᵉ) Fᵉ ＝ᵉ Fᵉ
  left-unit-law-comp-functor-Precategoryᵉ =
    eq-eq-map-functor-Precategoryᵉ Cᵉ Dᵉ _ _ reflᵉ

  right-unit-law-comp-functor-Precategoryᵉ :
    comp-functor-Precategoryᵉ Cᵉ Cᵉ Dᵉ Fᵉ (id-functor-Precategoryᵉ Cᵉ) ＝ᵉ Fᵉ
  right-unit-law-comp-functor-Precategoryᵉ = reflᵉ
```

#### Associativity of functor composition

```agda
module _
  {l1ᵉ l1'ᵉ l2ᵉ l2'ᵉ l3ᵉ l3'ᵉ l4ᵉ l4'ᵉ : Level}
  (Aᵉ : Precategoryᵉ l1ᵉ l1'ᵉ)
  (Bᵉ : Precategoryᵉ l2ᵉ l2'ᵉ)
  (Cᵉ : Precategoryᵉ l3ᵉ l3'ᵉ)
  (Dᵉ : Precategoryᵉ l4ᵉ l4'ᵉ)
  (Fᵉ : functor-Precategoryᵉ Aᵉ Bᵉ)
  (Gᵉ : functor-Precategoryᵉ Bᵉ Cᵉ)
  (Hᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  associative-comp-functor-Precategoryᵉ :
    comp-functor-Precategoryᵉ Aᵉ Bᵉ Dᵉ (comp-functor-Precategoryᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ) Fᵉ ＝ᵉ
    comp-functor-Precategoryᵉ Aᵉ Cᵉ Dᵉ Hᵉ (comp-functor-Precategoryᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ)
  associative-comp-functor-Precategoryᵉ =
    eq-eq-map-functor-Precategoryᵉ Aᵉ Dᵉ _ _ reflᵉ
```

#### Mac Lane pentagon for functor composition

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
  (Aᵉ : Precategoryᵉ l1ᵉ l1'ᵉ)
  (Bᵉ : Precategoryᵉ l2ᵉ l2'ᵉ)
  (Cᵉ : Precategoryᵉ l3ᵉ l3'ᵉ)
  (Dᵉ : Precategoryᵉ l4ᵉ l4'ᵉ)
  (Eᵉ : Precategoryᵉ l4ᵉ l4'ᵉ)
  (Fᵉ : functor-Precategoryᵉ Aᵉ Bᵉ)
  (Gᵉ : functor-Precategoryᵉ Bᵉ Cᵉ)
  (Hᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (Iᵉ : functor-Precategoryᵉ Dᵉ Eᵉ)
  where

  mac-lane-pentagon-comp-functor-Precategoryᵉ :
    coherence-pentagon-identificationsᵉ
      { xᵉ =
        comp-functor-Precategoryᵉ Aᵉ Bᵉ Eᵉ
        ( comp-functor-Precategoryᵉ Bᵉ Dᵉ Eᵉ Iᵉ
          ( comp-functor-Precategoryᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ))
        ( Fᵉ)}
      { comp-functor-Precategoryᵉ Aᵉ Dᵉ Eᵉ Iᵉ
        ( comp-functor-Precategoryᵉ Aᵉ Bᵉ Dᵉ
          ( comp-functor-Precategoryᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ)
          ( Fᵉ))}
      { comp-functor-Precategoryᵉ Aᵉ Bᵉ Eᵉ
        ( comp-functor-Precategoryᵉ Bᵉ Cᵉ Eᵉ
          ( comp-functor-Precategoryᵉ Cᵉ Dᵉ Eᵉ Iᵉ Hᵉ)
          ( Gᵉ))
        ( Fᵉ)}
      { comp-functor-Precategoryᵉ Aᵉ Dᵉ Eᵉ
        ( Iᵉ)
        ( comp-functor-Precategoryᵉ Aᵉ Cᵉ Dᵉ
          ( Hᵉ)
          ( comp-functor-Precategoryᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ))}
      { comp-functor-Precategoryᵉ Aᵉ Cᵉ Eᵉ
        ( comp-functor-Precategoryᵉ Cᵉ Dᵉ Eᵉ Iᵉ Hᵉ)
        ( comp-functor-Precategoryᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ)}
      ( associative-comp-functor-Precategoryᵉ Aᵉ Bᵉ Dᵉ Eᵉ
        ( Fᵉ) (comp-functor-Precategoryᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ) (Iᵉ))
      ( apᵉ
        ( λ pᵉ → comp-functor-Precategoryᵉ Aᵉ Bᵉ Eᵉ pᵉ Fᵉ)
        ( invᵉ (associative-comp-functor-Precategoryᵉ Bᵉ Cᵉ Dᵉ Eᵉ Gᵉ Hᵉ Iᵉ)))
      ( apᵉ
        ( λ pᵉ → comp-functor-Precategoryᵉ Aᵉ Dᵉ Eᵉ Iᵉ pᵉ)
        ( associative-comp-functor-Precategoryᵉ Aᵉ Bᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ))
      ( associative-comp-functor-Precategoryᵉ Aᵉ Bᵉ Cᵉ Eᵉ
        ( Fᵉ) (Gᵉ) (comp-functor-Precategoryᵉ Cᵉ Dᵉ Eᵉ Iᵉ Hᵉ))
      ( invᵉ
        ( associative-comp-functor-Precategoryᵉ Aᵉ Cᵉ Dᵉ Eᵉ
          (comp-functor-Precategoryᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ) Hᵉ Iᵉ))
  mac-lane-pentagon-comp-functor-Precategoryᵉ = {!!ᵉ}
```

## See also

-ᵉ [Theᵉ precategoryᵉ ofᵉ functorsᵉ andᵉ naturalᵉ transformationsᵉ betweenᵉ precategories](category-theory.precategory-of-functors.mdᵉ)

## References

{{#bibliographyᵉ}} {{#referenceᵉ UF13ᵉ}} {{#referenceᵉ AKS15ᵉ}}

## External links

-ᵉ [Functors](https://1lab.dev/Cat.Base.html#functorsᵉ) atᵉ 1labᵉ