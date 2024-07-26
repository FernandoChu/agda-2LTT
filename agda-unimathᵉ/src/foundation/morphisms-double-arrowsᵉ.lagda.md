# Morphisms of double arrows

```agda
module foundation.morphisms-double-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-arrowsᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "morphismᵉ ofᵉ doubleᵉ arrows"ᵉ Disambiguation="betweenᵉ types"ᵉ Agda=hom-double-arrowᵉ}}
fromᵉ aᵉ [doubleᵉ arrow](foundation.double-arrows.mdᵉ) `f,ᵉ gᵉ : Aᵉ → B`ᵉ to aᵉ doubleᵉ
arrowᵉ `h,ᵉ kᵉ : Xᵉ → Y`ᵉ isᵉ aᵉ pairᵉ ofᵉ mapsᵉ `iᵉ : Aᵉ → X`ᵉ andᵉ `jᵉ : Bᵉ → Y`,ᵉ suchᵉ thatᵉ
theᵉ squaresᵉ

```text
           iᵉ                   iᵉ
     Aᵉ -------->ᵉ Xᵉ       Aᵉ -------->ᵉ Xᵉ
     |           |       |           |
   fᵉ |           | hᵉ   gᵉ |           | kᵉ
     |           |       |           |
     ∨ᵉ           ∨ᵉ       ∨ᵉ           ∨ᵉ
     Bᵉ -------->ᵉ Yᵉ       Bᵉ -------->ᵉ Yᵉ
           jᵉ                   jᵉ
```

[commute](foundation-core.commuting-squares-of-maps.md).ᵉ Theᵉ mapᵉ `i`ᵉ isᵉ referredᵉ
to asᵉ theᵉ _domainᵉ map_,ᵉ andᵉ theᵉ `j`ᵉ asᵉ theᵉ _codomainᵉ map_.ᵉ

Alternatively,ᵉ aᵉ morphismᵉ ofᵉ doubleᵉ arrowsᵉ isᵉ aᵉ pairᵉ ofᵉ
[morphismsᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ) `fᵉ → h`ᵉ andᵉ `gᵉ → k`ᵉ thatᵉ
shareᵉ theᵉ underlyingᵉ maps.ᵉ

## Definitions

### Morphisms of double arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) (a'ᵉ : double-arrowᵉ l3ᵉ l4ᵉ)
  where

  left-coherence-hom-double-arrowᵉ :
    (domain-double-arrowᵉ aᵉ → domain-double-arrowᵉ a'ᵉ) →
    (codomain-double-arrowᵉ aᵉ → codomain-double-arrowᵉ a'ᵉ) →
    UUᵉ (l1ᵉ ⊔ l4ᵉ)
  left-coherence-hom-double-arrowᵉ hAᵉ hBᵉ =
    coherence-square-mapsᵉ
      ( hAᵉ)
      ( left-map-double-arrowᵉ aᵉ)
      ( left-map-double-arrowᵉ a'ᵉ)
      ( hBᵉ)

  right-coherence-hom-double-arrowᵉ :
    (domain-double-arrowᵉ aᵉ → domain-double-arrowᵉ a'ᵉ) →
    (codomain-double-arrowᵉ aᵉ → codomain-double-arrowᵉ a'ᵉ) →
    UUᵉ (l1ᵉ ⊔ l4ᵉ)
  right-coherence-hom-double-arrowᵉ hAᵉ hBᵉ =
    coherence-square-mapsᵉ
      ( hAᵉ)
      ( right-map-double-arrowᵉ aᵉ)
      ( right-map-double-arrowᵉ a'ᵉ)
      ( hBᵉ)

  hom-double-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-double-arrowᵉ =
    Σᵉ ( domain-double-arrowᵉ aᵉ → domain-double-arrowᵉ a'ᵉ)
      ( λ hAᵉ →
        Σᵉ ( codomain-double-arrowᵉ aᵉ → codomain-double-arrowᵉ a'ᵉ)
          ( λ hBᵉ →
            left-coherence-hom-double-arrowᵉ hAᵉ hBᵉ ×ᵉ
            right-coherence-hom-double-arrowᵉ hAᵉ hBᵉ))
```

### Components of a morphism of double arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) (a'ᵉ : double-arrowᵉ l3ᵉ l4ᵉ)
  (hᵉ : hom-double-arrowᵉ aᵉ a'ᵉ)
  where

  domain-map-hom-double-arrowᵉ : domain-double-arrowᵉ aᵉ → domain-double-arrowᵉ a'ᵉ
  domain-map-hom-double-arrowᵉ = pr1ᵉ hᵉ

  codomain-map-hom-double-arrowᵉ :
    codomain-double-arrowᵉ aᵉ → codomain-double-arrowᵉ a'ᵉ
  codomain-map-hom-double-arrowᵉ = pr1ᵉ (pr2ᵉ hᵉ)

  left-square-hom-double-arrowᵉ :
    left-coherence-hom-double-arrowᵉ aᵉ a'ᵉ
      ( domain-map-hom-double-arrowᵉ)
      ( codomain-map-hom-double-arrowᵉ)
  left-square-hom-double-arrowᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ hᵉ))

  left-hom-arrow-hom-double-arrowᵉ :
    hom-arrowᵉ (left-map-double-arrowᵉ aᵉ) (left-map-double-arrowᵉ a'ᵉ)
  pr1ᵉ left-hom-arrow-hom-double-arrowᵉ =
    domain-map-hom-double-arrowᵉ
  pr1ᵉ (pr2ᵉ left-hom-arrow-hom-double-arrowᵉ) =
    codomain-map-hom-double-arrowᵉ
  pr2ᵉ (pr2ᵉ left-hom-arrow-hom-double-arrowᵉ) =
    left-square-hom-double-arrowᵉ

  right-square-hom-double-arrowᵉ :
    right-coherence-hom-double-arrowᵉ aᵉ a'ᵉ
      ( domain-map-hom-double-arrowᵉ)
      ( codomain-map-hom-double-arrowᵉ)
  right-square-hom-double-arrowᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ hᵉ))

  right-hom-arrow-hom-double-arrowᵉ :
    hom-arrowᵉ (right-map-double-arrowᵉ aᵉ) (right-map-double-arrowᵉ a'ᵉ)
  pr1ᵉ right-hom-arrow-hom-double-arrowᵉ =
    domain-map-hom-double-arrowᵉ
  pr1ᵉ (pr2ᵉ right-hom-arrow-hom-double-arrowᵉ) =
    codomain-map-hom-double-arrowᵉ
  pr2ᵉ (pr2ᵉ right-hom-arrow-hom-double-arrowᵉ) =
    right-square-hom-double-arrowᵉ
```

### The identity morphism of double arrows

```agda
module _
  {l1ᵉ l2ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ)
  where

  id-hom-double-arrowᵉ : hom-double-arrowᵉ aᵉ aᵉ
  pr1ᵉ id-hom-double-arrowᵉ = idᵉ
  pr1ᵉ (pr2ᵉ id-hom-double-arrowᵉ) = idᵉ
  pr2ᵉ (pr2ᵉ id-hom-double-arrowᵉ) = (refl-htpyᵉ ,ᵉ refl-htpyᵉ)
```

### Composition of morphisms of double arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) (bᵉ : double-arrowᵉ l3ᵉ l4ᵉ) (cᵉ : double-arrowᵉ l5ᵉ l6ᵉ)
  (gᵉ : hom-double-arrowᵉ bᵉ cᵉ) (fᵉ : hom-double-arrowᵉ aᵉ bᵉ)
  where

  domain-map-comp-hom-double-arrowᵉ :
    domain-double-arrowᵉ aᵉ → domain-double-arrowᵉ cᵉ
  domain-map-comp-hom-double-arrowᵉ =
    domain-map-hom-double-arrowᵉ bᵉ cᵉ gᵉ ∘ᵉ domain-map-hom-double-arrowᵉ aᵉ bᵉ fᵉ

  codomain-map-comp-hom-double-arrowᵉ :
    codomain-double-arrowᵉ aᵉ → codomain-double-arrowᵉ cᵉ
  codomain-map-comp-hom-double-arrowᵉ =
    codomain-map-hom-double-arrowᵉ bᵉ cᵉ gᵉ ∘ᵉ codomain-map-hom-double-arrowᵉ aᵉ bᵉ fᵉ

  left-square-comp-hom-double-arrowᵉ :
    left-coherence-hom-double-arrowᵉ aᵉ cᵉ
      ( domain-map-comp-hom-double-arrowᵉ)
      ( codomain-map-comp-hom-double-arrowᵉ)
  left-square-comp-hom-double-arrowᵉ =
    coh-comp-hom-arrowᵉ
      ( left-map-double-arrowᵉ aᵉ)
      ( left-map-double-arrowᵉ bᵉ)
      ( left-map-double-arrowᵉ cᵉ)
      ( left-hom-arrow-hom-double-arrowᵉ bᵉ cᵉ gᵉ)
      ( left-hom-arrow-hom-double-arrowᵉ aᵉ bᵉ fᵉ)

  right-square-comp-hom-double-arrowᵉ :
    right-coherence-hom-double-arrowᵉ aᵉ cᵉ
      ( domain-map-comp-hom-double-arrowᵉ)
      ( codomain-map-comp-hom-double-arrowᵉ)
  right-square-comp-hom-double-arrowᵉ =
    coh-comp-hom-arrowᵉ
      ( right-map-double-arrowᵉ aᵉ)
      ( right-map-double-arrowᵉ bᵉ)
      ( right-map-double-arrowᵉ cᵉ)
      ( right-hom-arrow-hom-double-arrowᵉ bᵉ cᵉ gᵉ)
      ( right-hom-arrow-hom-double-arrowᵉ aᵉ bᵉ fᵉ)

  comp-hom-double-arrowᵉ : hom-double-arrowᵉ aᵉ cᵉ
  pr1ᵉ comp-hom-double-arrowᵉ =
    domain-map-comp-hom-double-arrowᵉ
  pr1ᵉ (pr2ᵉ comp-hom-double-arrowᵉ) =
    codomain-map-comp-hom-double-arrowᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ comp-hom-double-arrowᵉ)) =
    left-square-comp-hom-double-arrowᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ comp-hom-double-arrowᵉ)) =
    right-square-comp-hom-double-arrowᵉ
```