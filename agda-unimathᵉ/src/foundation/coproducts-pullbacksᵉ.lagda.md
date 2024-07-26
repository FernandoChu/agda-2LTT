# Coproducts of pullbacks

```agda
module foundation.coproducts-pullbacksᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-coproduct-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.pullbacksᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.universal-property-pullbacksᵉ
```

</details>

## Idea

Givenᵉ twoᵉ
[commutingᵉ squaresᵉ ofᵉ maps](foundation-core.commuting-squares-of-maps.md),ᵉ

```text
    Cᵉ ------>ᵉ Bᵉ                  C'ᵉ ----->ᵉ B'ᵉ
    |         |                  |         |
    |         |  gᵉ     andᵉ       |         | g'ᵉ
    ∨ᵉ         ∨ᵉ                  ∨ᵉ         ∨ᵉ
    Aᵉ ------>ᵉ Xᵉ                  A'ᵉ ----->ᵉ X',ᵉ
         fᵉ                            f'ᵉ
```

thenᵉ theirᵉ coproductᵉ

```text
  Cᵉ +ᵉ C'ᵉ ---->ᵉ Bᵉ +ᵉ B'ᵉ
    |            |
    |            | gᵉ +ᵉ g'ᵉ
    ∨ᵉ            ∨ᵉ
  Aᵉ +ᵉ A'ᵉ ---->ᵉ Xᵉ +ᵉ X'ᵉ
         fᵉ +ᵉ f'ᵉ
```

isᵉ aᵉ [pullback](foundation-core.pullbacks.mdᵉ) ifᵉ eachᵉ summandᵉ is.ᵉ

## Definitions

### Coproduct cones

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ} {C'ᵉ : UUᵉ l4'ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (f'ᵉ : A'ᵉ → X'ᵉ) (g'ᵉ : B'ᵉ → X'ᵉ)
  where

  coproduct-coneᵉ :
    coneᵉ fᵉ gᵉ Cᵉ → coneᵉ f'ᵉ g'ᵉ C'ᵉ →
    coneᵉ (map-coproductᵉ fᵉ f'ᵉ) (map-coproductᵉ gᵉ g'ᵉ) (Cᵉ +ᵉ C'ᵉ)
  pr1ᵉ (coproduct-coneᵉ (pᵉ ,ᵉ qᵉ ,ᵉ Hᵉ) (p'ᵉ ,ᵉ q'ᵉ ,ᵉ H'ᵉ)) = map-coproductᵉ pᵉ p'ᵉ
  pr1ᵉ (pr2ᵉ (coproduct-coneᵉ (pᵉ ,ᵉ qᵉ ,ᵉ Hᵉ) (p'ᵉ ,ᵉ q'ᵉ ,ᵉ H'ᵉ))) = map-coproductᵉ qᵉ q'ᵉ
  pr2ᵉ (pr2ᵉ (coproduct-coneᵉ (pᵉ ,ᵉ qᵉ ,ᵉ Hᵉ) (p'ᵉ ,ᵉ q'ᵉ ,ᵉ H'ᵉ))) =
    ( inv-htpyᵉ (preserves-comp-map-coproductᵉ pᵉ fᵉ p'ᵉ f'ᵉ)) ∙hᵉ
    ( htpy-map-coproductᵉ Hᵉ H'ᵉ) ∙hᵉ
    ( preserves-comp-map-coproductᵉ qᵉ gᵉ q'ᵉ g'ᵉ)
```

## Properties

### Computing the standard pullback of a coproduct

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (f'ᵉ : A'ᵉ → X'ᵉ) (g'ᵉ : B'ᵉ → X'ᵉ)
  where

  inl-map-standard-pullback-coproductᵉ :
    standard-pullbackᵉ fᵉ gᵉ →
    standard-pullbackᵉ (map-coproductᵉ fᵉ f'ᵉ) (map-coproductᵉ gᵉ g'ᵉ)
  pr1ᵉ (inl-map-standard-pullback-coproductᵉ (xᵉ ,ᵉ yᵉ ,ᵉ pᵉ)) = inlᵉ xᵉ
  pr1ᵉ (pr2ᵉ (inl-map-standard-pullback-coproductᵉ (xᵉ ,ᵉ yᵉ ,ᵉ pᵉ))) = inlᵉ yᵉ
  pr2ᵉ (pr2ᵉ (inl-map-standard-pullback-coproductᵉ (xᵉ ,ᵉ yᵉ ,ᵉ pᵉ))) = apᵉ inlᵉ pᵉ

  inr-map-standard-pullback-coproductᵉ :
    standard-pullbackᵉ f'ᵉ g'ᵉ →
    standard-pullbackᵉ (map-coproductᵉ fᵉ f'ᵉ) (map-coproductᵉ gᵉ g'ᵉ)
  pr1ᵉ (inr-map-standard-pullback-coproductᵉ (xᵉ ,ᵉ yᵉ ,ᵉ pᵉ)) = inrᵉ xᵉ
  pr1ᵉ (pr2ᵉ (inr-map-standard-pullback-coproductᵉ (xᵉ ,ᵉ yᵉ ,ᵉ pᵉ))) = inrᵉ yᵉ
  pr2ᵉ (pr2ᵉ (inr-map-standard-pullback-coproductᵉ (xᵉ ,ᵉ yᵉ ,ᵉ pᵉ))) = apᵉ inrᵉ pᵉ

  map-standard-pullback-coproductᵉ :
    standard-pullbackᵉ fᵉ gᵉ +ᵉ standard-pullbackᵉ f'ᵉ g'ᵉ →
    standard-pullbackᵉ (map-coproductᵉ fᵉ f'ᵉ) (map-coproductᵉ gᵉ g'ᵉ)
  map-standard-pullback-coproductᵉ (inlᵉ vᵉ) =
    inl-map-standard-pullback-coproductᵉ vᵉ
  map-standard-pullback-coproductᵉ (inrᵉ uᵉ) =
    inr-map-standard-pullback-coproductᵉ uᵉ

  map-inv-standard-pullback-coproductᵉ :
    standard-pullbackᵉ (map-coproductᵉ fᵉ f'ᵉ) (map-coproductᵉ gᵉ g'ᵉ) →
    standard-pullbackᵉ fᵉ gᵉ +ᵉ standard-pullbackᵉ f'ᵉ g'ᵉ
  map-inv-standard-pullback-coproductᵉ (inlᵉ xᵉ ,ᵉ inlᵉ yᵉ ,ᵉ pᵉ) =
    inlᵉ (xᵉ ,ᵉ yᵉ ,ᵉ is-injective-inlᵉ pᵉ)
  map-inv-standard-pullback-coproductᵉ (inrᵉ xᵉ ,ᵉ inrᵉ yᵉ ,ᵉ pᵉ) =
    inrᵉ (xᵉ ,ᵉ yᵉ ,ᵉ is-injective-inrᵉ pᵉ)

  is-section-map-inv-standard-pullback-coproductᵉ :
    is-sectionᵉ
      ( map-standard-pullback-coproductᵉ)
      ( map-inv-standard-pullback-coproductᵉ)
  is-section-map-inv-standard-pullback-coproductᵉ (inlᵉ xᵉ ,ᵉ inlᵉ yᵉ ,ᵉ pᵉ) =
    eq-pair-eq-fiberᵉ (eq-pair-eq-fiberᵉ (is-section-is-injective-inlᵉ pᵉ))
  is-section-map-inv-standard-pullback-coproductᵉ (inrᵉ xᵉ ,ᵉ inrᵉ yᵉ ,ᵉ pᵉ) =
    eq-pair-eq-fiberᵉ (eq-pair-eq-fiberᵉ (is-section-is-injective-inrᵉ pᵉ))

  is-retraction-map-inv-standard-pullback-coproductᵉ :
    is-retractionᵉ
      ( map-standard-pullback-coproductᵉ)
      ( map-inv-standard-pullback-coproductᵉ)
  is-retraction-map-inv-standard-pullback-coproductᵉ (inlᵉ (xᵉ ,ᵉ yᵉ ,ᵉ pᵉ)) =
    apᵉ
      ( inlᵉ)
      ( eq-pair-eq-fiberᵉ (eq-pair-eq-fiberᵉ (is-retraction-is-injective-inlᵉ pᵉ)))
  is-retraction-map-inv-standard-pullback-coproductᵉ (inrᵉ (xᵉ ,ᵉ yᵉ ,ᵉ pᵉ)) =
    apᵉ
      ( inrᵉ)
      ( eq-pair-eq-fiberᵉ (eq-pair-eq-fiberᵉ (is-retraction-is-injective-inrᵉ pᵉ)))

  abstract
    is-equiv-map-standard-pullback-coproductᵉ :
      is-equivᵉ map-standard-pullback-coproductᵉ
    is-equiv-map-standard-pullback-coproductᵉ =
      is-equiv-is-invertibleᵉ
        map-inv-standard-pullback-coproductᵉ
        is-section-map-inv-standard-pullback-coproductᵉ
        is-retraction-map-inv-standard-pullback-coproductᵉ

  compute-standard-pullback-coproductᵉ :
    standard-pullbackᵉ fᵉ gᵉ +ᵉ standard-pullbackᵉ f'ᵉ g'ᵉ ≃ᵉ
    standard-pullbackᵉ (map-coproductᵉ fᵉ f'ᵉ) (map-coproductᵉ gᵉ g'ᵉ)
  compute-standard-pullback-coproductᵉ =
    map-standard-pullback-coproductᵉ ,ᵉ is-equiv-map-standard-pullback-coproductᵉ
```

### The gap map of a coproduct computes as a coproduct of gap maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (f'ᵉ : A'ᵉ → X'ᵉ) (g'ᵉ : B'ᵉ → X'ᵉ)
  where

  triangle-map-standard-pullback-coproductᵉ :
    {l4ᵉ l4'ᵉ : Level} {Cᵉ : UUᵉ l4ᵉ} {C'ᵉ : UUᵉ l4'ᵉ}
    (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ f'ᵉ g'ᵉ C'ᵉ) →
    coherence-triangle-mapsᵉ
      ( gapᵉ
        ( map-coproductᵉ fᵉ f'ᵉ)
        ( map-coproductᵉ gᵉ g'ᵉ)
        ( coproduct-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ))
      ( map-standard-pullback-coproductᵉ fᵉ gᵉ f'ᵉ g'ᵉ)
      ( map-coproductᵉ (gapᵉ fᵉ gᵉ cᵉ) (gapᵉ f'ᵉ g'ᵉ c'ᵉ))
  triangle-map-standard-pullback-coproductᵉ cᵉ c'ᵉ (inlᵉ _) =
    eq-pair-eq-fiberᵉ (eq-pair-eq-fiberᵉ right-unitᵉ)
  triangle-map-standard-pullback-coproductᵉ cᵉ c'ᵉ (inrᵉ _) =
    eq-pair-eq-fiberᵉ (eq-pair-eq-fiberᵉ right-unitᵉ)
```

### Coproducts of pullbacks are pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ} {C'ᵉ : UUᵉ l4'ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (f'ᵉ : A'ᵉ → X'ᵉ) (g'ᵉ : B'ᵉ → X'ᵉ)
  where

  abstract
    is-pullback-coproduct-is-pullbackᵉ :
      (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ f'ᵉ g'ᵉ C'ᵉ) →
      is-pullbackᵉ fᵉ gᵉ cᵉ →
      is-pullbackᵉ f'ᵉ g'ᵉ c'ᵉ →
      is-pullbackᵉ
        ( map-coproductᵉ fᵉ f'ᵉ)
        ( map-coproductᵉ gᵉ g'ᵉ)
        ( coproduct-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ)
    is-pullback-coproduct-is-pullbackᵉ cᵉ c'ᵉ is-pb-cᵉ is-pb-c'ᵉ =
      is-equiv-left-map-triangleᵉ
        ( gapᵉ
          ( map-coproductᵉ fᵉ f'ᵉ)
          ( map-coproductᵉ gᵉ g'ᵉ)
          ( coproduct-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ))
        ( map-standard-pullback-coproductᵉ fᵉ gᵉ f'ᵉ g'ᵉ)
        ( map-coproductᵉ (gapᵉ fᵉ gᵉ cᵉ) (gapᵉ f'ᵉ g'ᵉ c'ᵉ))
        ( triangle-map-standard-pullback-coproductᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ)
        ( is-equiv-map-coproductᵉ is-pb-cᵉ is-pb-c'ᵉ)
        ( is-equiv-map-standard-pullback-coproductᵉ fᵉ gᵉ f'ᵉ g'ᵉ)
```

### Coproducts of cones that satisfy the universal property of pullbacks satisfy the universal property of pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {X'ᵉ : UUᵉ l3'ᵉ} {C'ᵉ : UUᵉ l4'ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (f'ᵉ : A'ᵉ → X'ᵉ) (g'ᵉ : B'ᵉ → X'ᵉ)
  where

  abstract
    universal-property-pullback-coproduct-universal-property-pullbackᵉ :
      (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ f'ᵉ g'ᵉ C'ᵉ) →
      universal-property-pullbackᵉ fᵉ gᵉ cᵉ →
      universal-property-pullbackᵉ f'ᵉ g'ᵉ c'ᵉ →
      universal-property-pullbackᵉ
        ( map-coproductᵉ fᵉ f'ᵉ)
        ( map-coproductᵉ gᵉ g'ᵉ)
        ( coproduct-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ)
    universal-property-pullback-coproduct-universal-property-pullbackᵉ
      cᵉ c'ᵉ up-pb-cᵉ up-pb-c'ᵉ =
      universal-property-pullback-is-pullbackᵉ
        ( map-coproductᵉ fᵉ f'ᵉ)
        ( map-coproductᵉ gᵉ g'ᵉ)
        ( coproduct-coneᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ)
        ( is-pullback-coproduct-is-pullbackᵉ fᵉ gᵉ f'ᵉ g'ᵉ cᵉ c'ᵉ
          ( is-pullback-universal-property-pullbackᵉ fᵉ gᵉ cᵉ up-pb-cᵉ)
          ( is-pullback-universal-property-pullbackᵉ f'ᵉ g'ᵉ c'ᵉ up-pb-c'ᵉ))
```

## Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}