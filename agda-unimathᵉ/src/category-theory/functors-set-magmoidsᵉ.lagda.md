# Functors between set-magmoids

```agda
module category-theory.functors-set-magmoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.maps-set-magmoidsᵉ
open import category-theory.set-magmoidsᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **functorᵉ betweenᵉ [set-magmoids](category-theory.set-magmoids.md)**ᵉ isᵉ aᵉ
familyᵉ ofᵉ mapsᵉ onᵉ theᵉ hom-[sets](foundation-core.sets.mdᵉ) thatᵉ preserveᵉ theᵉ
[compositionᵉ operation](category-theory.composition-operations-on-binary-families-of-sets.md).ᵉ

Theseᵉ objectsᵉ serveᵉ asᵉ ourᵉ startingᵉ pointᵉ in theᵉ studyᵉ ofᵉ
[stucture](foundation.structure.md)-preservingᵉ mapsᵉ ofᵉ
[categories](category-theory.categories.md).ᵉ Indeed,ᵉ categoriesᵉ formᵉ aᵉ
[subtype](foundation-core.subtypes.mdᵉ) ofᵉ set-magmoids,ᵉ althoughᵉ functorsᵉ ofᵉ
set-magmoidsᵉ do notᵉ automaticallyᵉ preserveᵉ identity-morphisms.ᵉ

## Definitions

### The predicate of being a functor of set-magmoids

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ) (Bᵉ : Set-Magmoidᵉ l3ᵉ l4ᵉ)
  (F₀ᵉ : obj-Set-Magmoidᵉ Aᵉ → obj-Set-Magmoidᵉ Bᵉ)
  (F₁ᵉ :
    {xᵉ yᵉ : obj-Set-Magmoidᵉ Aᵉ} →
    hom-Set-Magmoidᵉ Aᵉ xᵉ yᵉ → hom-Set-Magmoidᵉ Bᵉ (F₀ᵉ xᵉ) (F₀ᵉ yᵉ))
  where

  preserves-comp-hom-Set-Magmoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  preserves-comp-hom-Set-Magmoidᵉ =
    {xᵉ yᵉ zᵉ : obj-Set-Magmoidᵉ Aᵉ}
    (gᵉ : hom-Set-Magmoidᵉ Aᵉ yᵉ zᵉ) (fᵉ : hom-Set-Magmoidᵉ Aᵉ xᵉ yᵉ) →
    F₁ᵉ (comp-hom-Set-Magmoidᵉ Aᵉ gᵉ fᵉ) ＝ᵉ comp-hom-Set-Magmoidᵉ Bᵉ (F₁ᵉ gᵉ) (F₁ᵉ fᵉ)

  is-prop-preserves-comp-hom-Set-Magmoidᵉ :
    is-propᵉ preserves-comp-hom-Set-Magmoidᵉ
  is-prop-preserves-comp-hom-Set-Magmoidᵉ =
    is-prop-iterated-implicit-Πᵉ 3
      ( λ xᵉ yᵉ zᵉ →
        is-prop-iterated-Πᵉ 2
          ( λ gᵉ fᵉ →
            is-set-hom-Set-Magmoidᵉ Bᵉ (F₀ᵉ xᵉ) (F₀ᵉ zᵉ)
              ( F₁ᵉ (comp-hom-Set-Magmoidᵉ Aᵉ gᵉ fᵉ))
              ( comp-hom-Set-Magmoidᵉ Bᵉ (F₁ᵉ gᵉ) (F₁ᵉ fᵉ))))

  preserves-comp-hom-prop-Set-Magmoidᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ preserves-comp-hom-prop-Set-Magmoidᵉ =
    preserves-comp-hom-Set-Magmoidᵉ
  pr2ᵉ preserves-comp-hom-prop-Set-Magmoidᵉ =
    is-prop-preserves-comp-hom-Set-Magmoidᵉ
```

### The predicate on maps of set-magmoids of being a functor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ) (Bᵉ : Set-Magmoidᵉ l3ᵉ l4ᵉ)
  (Fᵉ : map-Set-Magmoidᵉ Aᵉ Bᵉ)
  where

  preserves-comp-hom-prop-map-Set-Magmoidᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  preserves-comp-hom-prop-map-Set-Magmoidᵉ =
    preserves-comp-hom-prop-Set-Magmoidᵉ Aᵉ Bᵉ
      ( obj-map-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ)
      ( hom-map-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ)

  preserves-comp-hom-map-Set-Magmoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  preserves-comp-hom-map-Set-Magmoidᵉ =
    type-Propᵉ preserves-comp-hom-prop-map-Set-Magmoidᵉ

  is-prop-preserves-comp-hom-map-Set-Magmoidᵉ :
    is-propᵉ preserves-comp-hom-map-Set-Magmoidᵉ
  is-prop-preserves-comp-hom-map-Set-Magmoidᵉ =
    is-prop-type-Propᵉ preserves-comp-hom-prop-map-Set-Magmoidᵉ
```

### The type of functors between set-magmoids

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ) (Bᵉ : Set-Magmoidᵉ l3ᵉ l4ᵉ)
  where

  functor-Set-Magmoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  functor-Set-Magmoidᵉ =
    Σᵉ ( obj-Set-Magmoidᵉ Aᵉ → obj-Set-Magmoidᵉ Bᵉ)
      ( λ F₀ᵉ →
        Σᵉ ( {xᵉ yᵉ : obj-Set-Magmoidᵉ Aᵉ} →
            hom-Set-Magmoidᵉ Aᵉ xᵉ yᵉ → hom-Set-Magmoidᵉ Bᵉ (F₀ᵉ xᵉ) (F₀ᵉ yᵉ))
          ( preserves-comp-hom-Set-Magmoidᵉ Aᵉ Bᵉ F₀ᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ) (Bᵉ : Set-Magmoidᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Set-Magmoidᵉ Aᵉ Bᵉ)
  where

  obj-functor-Set-Magmoidᵉ : obj-Set-Magmoidᵉ Aᵉ → obj-Set-Magmoidᵉ Bᵉ
  obj-functor-Set-Magmoidᵉ = pr1ᵉ Fᵉ

  hom-functor-Set-Magmoidᵉ :
    {xᵉ yᵉ : obj-Set-Magmoidᵉ Aᵉ} →
    (fᵉ : hom-Set-Magmoidᵉ Aᵉ xᵉ yᵉ) →
    hom-Set-Magmoidᵉ Bᵉ
      ( obj-functor-Set-Magmoidᵉ xᵉ)
      ( obj-functor-Set-Magmoidᵉ yᵉ)
  hom-functor-Set-Magmoidᵉ = pr1ᵉ (pr2ᵉ Fᵉ)

  map-functor-Set-Magmoidᵉ : map-Set-Magmoidᵉ Aᵉ Bᵉ
  pr1ᵉ map-functor-Set-Magmoidᵉ = obj-functor-Set-Magmoidᵉ
  pr2ᵉ map-functor-Set-Magmoidᵉ = hom-functor-Set-Magmoidᵉ

  preserves-comp-functor-Set-Magmoidᵉ :
    {xᵉ yᵉ zᵉ : obj-Set-Magmoidᵉ Aᵉ}
    (gᵉ : hom-Set-Magmoidᵉ Aᵉ yᵉ zᵉ)
    (fᵉ : hom-Set-Magmoidᵉ Aᵉ xᵉ yᵉ) →
    ( hom-functor-Set-Magmoidᵉ
      ( comp-hom-Set-Magmoidᵉ Aᵉ gᵉ fᵉ)) ＝ᵉ
    ( comp-hom-Set-Magmoidᵉ Bᵉ
      ( hom-functor-Set-Magmoidᵉ gᵉ)
      ( hom-functor-Set-Magmoidᵉ fᵉ))
  preserves-comp-functor-Set-Magmoidᵉ = pr2ᵉ (pr2ᵉ Fᵉ)
```

### The identity functor on a set-magmoid

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ)
  where

  id-functor-Set-Magmoidᵉ : functor-Set-Magmoidᵉ Aᵉ Aᵉ
  pr1ᵉ id-functor-Set-Magmoidᵉ = idᵉ
  pr1ᵉ (pr2ᵉ id-functor-Set-Magmoidᵉ) = idᵉ
  pr2ᵉ (pr2ᵉ id-functor-Set-Magmoidᵉ) gᵉ fᵉ = reflᵉ
```

### Composition of functors on set-magmoids

Anyᵉ twoᵉ compatibleᵉ functorsᵉ canᵉ beᵉ composedᵉ to aᵉ newᵉ functor.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ)
  (Bᵉ : Set-Magmoidᵉ l3ᵉ l4ᵉ)
  (Cᵉ : Set-Magmoidᵉ l5ᵉ l6ᵉ)
  (Gᵉ : functor-Set-Magmoidᵉ Bᵉ Cᵉ)
  (Fᵉ : functor-Set-Magmoidᵉ Aᵉ Bᵉ)
  where

  obj-comp-functor-Set-Magmoidᵉ : obj-Set-Magmoidᵉ Aᵉ → obj-Set-Magmoidᵉ Cᵉ
  obj-comp-functor-Set-Magmoidᵉ =
    obj-functor-Set-Magmoidᵉ Bᵉ Cᵉ Gᵉ ∘ᵉ obj-functor-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ

  hom-comp-functor-Set-Magmoidᵉ :
    {xᵉ yᵉ : obj-Set-Magmoidᵉ Aᵉ} →
    hom-Set-Magmoidᵉ Aᵉ xᵉ yᵉ →
    hom-Set-Magmoidᵉ Cᵉ
      ( obj-comp-functor-Set-Magmoidᵉ xᵉ)
      ( obj-comp-functor-Set-Magmoidᵉ yᵉ)
  hom-comp-functor-Set-Magmoidᵉ =
    hom-functor-Set-Magmoidᵉ Bᵉ Cᵉ Gᵉ ∘ᵉ hom-functor-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ

  map-comp-functor-Set-Magmoidᵉ : map-Set-Magmoidᵉ Aᵉ Cᵉ
  pr1ᵉ map-comp-functor-Set-Magmoidᵉ = obj-comp-functor-Set-Magmoidᵉ
  pr2ᵉ map-comp-functor-Set-Magmoidᵉ = hom-comp-functor-Set-Magmoidᵉ

  preserves-comp-comp-functor-Set-Magmoidᵉ :
    preserves-comp-hom-Set-Magmoidᵉ Aᵉ Cᵉ
      obj-comp-functor-Set-Magmoidᵉ
      hom-comp-functor-Set-Magmoidᵉ
  preserves-comp-comp-functor-Set-Magmoidᵉ gᵉ fᵉ =
    ( apᵉ
      ( hom-functor-Set-Magmoidᵉ Bᵉ Cᵉ Gᵉ)
      ( preserves-comp-functor-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ gᵉ fᵉ)) ∙ᵉ
    ( preserves-comp-functor-Set-Magmoidᵉ Bᵉ Cᵉ Gᵉ
      ( hom-functor-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ gᵉ)
      ( hom-functor-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ fᵉ))

  comp-functor-Set-Magmoidᵉ : functor-Set-Magmoidᵉ Aᵉ Cᵉ
  pr1ᵉ comp-functor-Set-Magmoidᵉ = obj-comp-functor-Set-Magmoidᵉ
  pr1ᵉ (pr2ᵉ comp-functor-Set-Magmoidᵉ) =
    hom-functor-Set-Magmoidᵉ Bᵉ Cᵉ Gᵉ ∘ᵉ hom-functor-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ
  pr2ᵉ (pr2ᵉ comp-functor-Set-Magmoidᵉ) = preserves-comp-comp-functor-Set-Magmoidᵉ
```

## Properties

### Extensionality of functors between set-magmoids

#### Equality of functors is equality of underlying maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ) (Bᵉ : Set-Magmoidᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Set-Magmoidᵉ Aᵉ Bᵉ)
  where

  equiv-eq-map-eq-functor-Set-Magmoidᵉ :
    (Fᵉ ＝ᵉ Gᵉ) ≃ᵉ (map-functor-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ ＝ᵉ map-functor-Set-Magmoidᵉ Aᵉ Bᵉ Gᵉ)
  equiv-eq-map-eq-functor-Set-Magmoidᵉ =
    equiv-ap-embᵉ
      ( comp-embᵉ
        ( emb-subtypeᵉ
          ( preserves-comp-hom-prop-map-Set-Magmoidᵉ Aᵉ Bᵉ))
        ( emb-equivᵉ
          ( inv-associative-Σᵉ
            ( obj-Set-Magmoidᵉ Aᵉ → obj-Set-Magmoidᵉ Bᵉ)
            ( λ F₀ᵉ →
              { xᵉ yᵉ : obj-Set-Magmoidᵉ Aᵉ} →
              hom-Set-Magmoidᵉ Aᵉ xᵉ yᵉ →
              hom-Set-Magmoidᵉ Bᵉ (F₀ᵉ xᵉ) (F₀ᵉ yᵉ))
            ( preserves-comp-hom-map-Set-Magmoidᵉ Aᵉ Bᵉ))))

  eq-map-eq-functor-Set-Magmoidᵉ :
    Fᵉ ＝ᵉ Gᵉ → map-functor-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ ＝ᵉ map-functor-Set-Magmoidᵉ Aᵉ Bᵉ Gᵉ
  eq-map-eq-functor-Set-Magmoidᵉ = map-equivᵉ equiv-eq-map-eq-functor-Set-Magmoidᵉ

  eq-eq-map-functor-Set-Magmoidᵉ :
    map-functor-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ ＝ᵉ map-functor-Set-Magmoidᵉ Aᵉ Bᵉ Gᵉ → Fᵉ ＝ᵉ Gᵉ
  eq-eq-map-functor-Set-Magmoidᵉ =
    map-inv-equivᵉ equiv-eq-map-eq-functor-Set-Magmoidᵉ

  is-section-eq-eq-map-functor-Set-Magmoidᵉ :
    eq-map-eq-functor-Set-Magmoidᵉ ∘ᵉ eq-eq-map-functor-Set-Magmoidᵉ ~ᵉ idᵉ
  is-section-eq-eq-map-functor-Set-Magmoidᵉ =
    is-section-map-inv-equivᵉ equiv-eq-map-eq-functor-Set-Magmoidᵉ

  is-retraction-eq-eq-map-functor-Set-Magmoidᵉ :
    eq-eq-map-functor-Set-Magmoidᵉ ∘ᵉ eq-map-eq-functor-Set-Magmoidᵉ ~ᵉ idᵉ
  is-retraction-eq-eq-map-functor-Set-Magmoidᵉ =
    is-retraction-map-inv-equivᵉ equiv-eq-map-eq-functor-Set-Magmoidᵉ
```

### Categorical laws for functor composition

#### Unit laws for functor composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ) (Bᵉ : Set-Magmoidᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Set-Magmoidᵉ Aᵉ Bᵉ)
  where

  left-unit-law-comp-functor-Set-Magmoidᵉ :
    comp-functor-Set-Magmoidᵉ Aᵉ Bᵉ Bᵉ (id-functor-Set-Magmoidᵉ Bᵉ) Fᵉ ＝ᵉ Fᵉ
  left-unit-law-comp-functor-Set-Magmoidᵉ =
    eq-eq-map-functor-Set-Magmoidᵉ Aᵉ Bᵉ _ _ reflᵉ

  right-unit-law-comp-functor-Set-Magmoidᵉ :
    comp-functor-Set-Magmoidᵉ Aᵉ Aᵉ Bᵉ Fᵉ (id-functor-Set-Magmoidᵉ Aᵉ) ＝ᵉ Fᵉ
  right-unit-law-comp-functor-Set-Magmoidᵉ = reflᵉ
```

#### Associativity of functor composition

```agda
module _
  {l1ᵉ l1'ᵉ l2ᵉ l2'ᵉ l3ᵉ l3'ᵉ l4ᵉ l4'ᵉ : Level}
  (Aᵉ : Set-Magmoidᵉ l1ᵉ l1'ᵉ)
  (Bᵉ : Set-Magmoidᵉ l2ᵉ l2'ᵉ)
  (Cᵉ : Set-Magmoidᵉ l3ᵉ l3'ᵉ)
  (Dᵉ : Set-Magmoidᵉ l4ᵉ l4'ᵉ)
  (Fᵉ : functor-Set-Magmoidᵉ Aᵉ Bᵉ)
  (Gᵉ : functor-Set-Magmoidᵉ Bᵉ Cᵉ)
  (Hᵉ : functor-Set-Magmoidᵉ Cᵉ Dᵉ)
  where

  associative-comp-functor-Set-Magmoidᵉ :
    comp-functor-Set-Magmoidᵉ Aᵉ Bᵉ Dᵉ (comp-functor-Set-Magmoidᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ) Fᵉ ＝ᵉ
    comp-functor-Set-Magmoidᵉ Aᵉ Cᵉ Dᵉ Hᵉ (comp-functor-Set-Magmoidᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ)
  associative-comp-functor-Set-Magmoidᵉ =
    eq-eq-map-functor-Set-Magmoidᵉ Aᵉ Dᵉ _ _ reflᵉ
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
  (Aᵉ : Set-Magmoidᵉ l1ᵉ l1'ᵉ)
  (Bᵉ : Set-Magmoidᵉ l2ᵉ l2'ᵉ)
  (Cᵉ : Set-Magmoidᵉ l3ᵉ l3'ᵉ)
  (Dᵉ : Set-Magmoidᵉ l4ᵉ l4'ᵉ)
  (Eᵉ : Set-Magmoidᵉ l4ᵉ l4'ᵉ)
  (Fᵉ : functor-Set-Magmoidᵉ Aᵉ Bᵉ)
  (Gᵉ : functor-Set-Magmoidᵉ Bᵉ Cᵉ)
  (Hᵉ : functor-Set-Magmoidᵉ Cᵉ Dᵉ)
  (Iᵉ : functor-Set-Magmoidᵉ Dᵉ Eᵉ)
  where

  mac-lane-pentagon-comp-functor-Set-Magmoidᵉ :
    coherence-pentagon-identificationsᵉ
      { xᵉ =
        comp-functor-Set-Magmoidᵉ Aᵉ Bᵉ Eᵉ
        ( comp-functor-Set-Magmoidᵉ Bᵉ Dᵉ Eᵉ Iᵉ
          ( comp-functor-Set-Magmoidᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ))
        ( Fᵉ)}
      { comp-functor-Set-Magmoidᵉ Aᵉ Dᵉ Eᵉ Iᵉ
        ( comp-functor-Set-Magmoidᵉ Aᵉ Bᵉ Dᵉ
          ( comp-functor-Set-Magmoidᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ)
          ( Fᵉ))}
      { comp-functor-Set-Magmoidᵉ Aᵉ Bᵉ Eᵉ
        ( comp-functor-Set-Magmoidᵉ Bᵉ Cᵉ Eᵉ
          ( comp-functor-Set-Magmoidᵉ Cᵉ Dᵉ Eᵉ Iᵉ Hᵉ)
          ( Gᵉ))
        ( Fᵉ)}
      { comp-functor-Set-Magmoidᵉ Aᵉ Dᵉ Eᵉ
        ( Iᵉ)
        ( comp-functor-Set-Magmoidᵉ Aᵉ Cᵉ Dᵉ
          ( Hᵉ)
          ( comp-functor-Set-Magmoidᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ))}
      { comp-functor-Set-Magmoidᵉ Aᵉ Cᵉ Eᵉ
        ( comp-functor-Set-Magmoidᵉ Cᵉ Dᵉ Eᵉ Iᵉ Hᵉ)
        ( comp-functor-Set-Magmoidᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ)}
      ( associative-comp-functor-Set-Magmoidᵉ Aᵉ Bᵉ Dᵉ Eᵉ
        ( Fᵉ) (comp-functor-Set-Magmoidᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ) (Iᵉ))
      ( apᵉ
        ( λ pᵉ → comp-functor-Set-Magmoidᵉ Aᵉ Bᵉ Eᵉ pᵉ Fᵉ)
        ( invᵉ (associative-comp-functor-Set-Magmoidᵉ Bᵉ Cᵉ Dᵉ Eᵉ Gᵉ Hᵉ Iᵉ)))
      ( apᵉ
        ( λ pᵉ → comp-functor-Set-Magmoidᵉ Aᵉ Dᵉ Eᵉ Iᵉ pᵉ)
        ( associative-comp-functor-Set-Magmoidᵉ Aᵉ Bᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ))
      ( associative-comp-functor-Set-Magmoidᵉ Aᵉ Bᵉ Cᵉ Eᵉ
        ( Fᵉ) (Gᵉ) (comp-functor-Set-Magmoidᵉ Cᵉ Dᵉ Eᵉ Iᵉ Hᵉ))
      ( invᵉ
        ( associative-comp-functor-Set-Magmoidᵉ Aᵉ Cᵉ Dᵉ Eᵉ
          (comp-functor-Set-Magmoidᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ) Hᵉ Iᵉ))
  mac-lane-pentagon-comp-functor-Set-Magmoidᵉ = {!!ᵉ}
```