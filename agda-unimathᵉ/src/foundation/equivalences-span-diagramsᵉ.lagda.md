# Equivalences of span diagrams

```agda
module foundation.equivalences-span-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-arrowsᵉ
open import foundation.equivalences-spansᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.morphisms-span-diagramsᵉ
open import foundation.morphisms-spansᵉ
open import foundation.operations-spansᵉ
open import foundation.propositionsᵉ
open import foundation.span-diagramsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Anᵉ {{#conceptᵉ "equivalenceᵉ ofᵉ spanᵉ diagrams"ᵉ Agda=equiv-span-diagramᵉ}} fromᵉ aᵉ
[spanᵉ diagram](foundation.span-diagrams.mdᵉ) `Aᵉ <-f-ᵉ Sᵉ -g->ᵉ B`ᵉ to aᵉ spanᵉ diagramᵉ
`Cᵉ <-h-ᵉ Tᵉ -k->ᵉ D`ᵉ consistsᵉ ofᵉ [equivalences](foundation-core.equivalences.mdᵉ)
`uᵉ : Aᵉ ≃ᵉ C`,ᵉ `vᵉ : Bᵉ ≃ᵉ D`,ᵉ andᵉ `wᵉ : Sᵉ ≃ᵉ T`ᵉ [equipped](foundation.structure.mdᵉ)
with twoᵉ [homotopies](foundation-core.homotopies.mdᵉ) witnessingᵉ thatᵉ theᵉ diagramᵉ

```text
         fᵉ       gᵉ
    Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
    |        |        |
  uᵉ |        | wᵉ      | vᵉ
    ∨ᵉ        ∨ᵉ        ∨ᵉ
    Cᵉ <-----ᵉ Tᵉ ----->ᵉ Dᵉ
         hᵉ       kᵉ
```

[commutes](foundation-core.commuting-squares-of-maps.md).ᵉ

## Definitions

### The predicate of being an equivalence of span diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ) (𝒯ᵉ : span-diagramᵉ l4ᵉ l5ᵉ l6ᵉ)
  (fᵉ : hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ)
  where

  is-equiv-prop-hom-span-diagramᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  is-equiv-prop-hom-span-diagramᵉ =
    product-Propᵉ
      ( is-equiv-Propᵉ (map-domain-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ fᵉ))
      ( product-Propᵉ
        ( is-equiv-Propᵉ (map-codomain-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ fᵉ))
        ( is-equiv-Propᵉ (spanning-map-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ fᵉ)))

  is-equiv-hom-span-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  is-equiv-hom-span-diagramᵉ = type-Propᵉ is-equiv-prop-hom-span-diagramᵉ

  is-prop-is-equiv-hom-span-diagramᵉ : is-propᵉ is-equiv-hom-span-diagramᵉ
  is-prop-is-equiv-hom-span-diagramᵉ =
    is-prop-type-Propᵉ is-equiv-prop-hom-span-diagramᵉ
```

### Equivalences of span diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ) (𝒯ᵉ : span-diagramᵉ l4ᵉ l5ᵉ l6ᵉ)
  where

  equiv-span-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  equiv-span-diagramᵉ =
    Σᵉ ( domain-span-diagramᵉ 𝒮ᵉ ≃ᵉ domain-span-diagramᵉ 𝒯ᵉ)
      ( λ eᵉ →
        Σᵉ ( codomain-span-diagramᵉ 𝒮ᵉ ≃ᵉ codomain-span-diagramᵉ 𝒯ᵉ)
          ( λ fᵉ →
            equiv-spanᵉ
              ( concat-spanᵉ (span-span-diagramᵉ 𝒮ᵉ) (map-equivᵉ eᵉ) (map-equivᵉ fᵉ))
              ( span-span-diagramᵉ 𝒯ᵉ)))

  module _
    (eᵉ : equiv-span-diagramᵉ)
    where

    equiv-domain-equiv-span-diagramᵉ :
      domain-span-diagramᵉ 𝒮ᵉ ≃ᵉ domain-span-diagramᵉ 𝒯ᵉ
    equiv-domain-equiv-span-diagramᵉ = pr1ᵉ eᵉ

    map-domain-equiv-span-diagramᵉ :
      domain-span-diagramᵉ 𝒮ᵉ → domain-span-diagramᵉ 𝒯ᵉ
    map-domain-equiv-span-diagramᵉ = map-equivᵉ equiv-domain-equiv-span-diagramᵉ

    is-equiv-map-domain-equiv-span-diagramᵉ :
      is-equivᵉ map-domain-equiv-span-diagramᵉ
    is-equiv-map-domain-equiv-span-diagramᵉ =
      is-equiv-map-equivᵉ equiv-domain-equiv-span-diagramᵉ

    equiv-codomain-equiv-span-diagramᵉ :
      codomain-span-diagramᵉ 𝒮ᵉ ≃ᵉ codomain-span-diagramᵉ 𝒯ᵉ
    equiv-codomain-equiv-span-diagramᵉ = pr1ᵉ (pr2ᵉ eᵉ)

    map-codomain-equiv-span-diagramᵉ :
      codomain-span-diagramᵉ 𝒮ᵉ → codomain-span-diagramᵉ 𝒯ᵉ
    map-codomain-equiv-span-diagramᵉ =
      map-equivᵉ equiv-codomain-equiv-span-diagramᵉ

    is-equiv-map-codomain-equiv-span-diagramᵉ :
      is-equivᵉ map-codomain-equiv-span-diagramᵉ
    is-equiv-map-codomain-equiv-span-diagramᵉ =
      is-equiv-map-equivᵉ equiv-codomain-equiv-span-diagramᵉ

    equiv-span-equiv-span-diagramᵉ :
      equiv-spanᵉ
        ( concat-spanᵉ
          ( span-span-diagramᵉ 𝒮ᵉ)
          ( map-domain-equiv-span-diagramᵉ)
          ( map-codomain-equiv-span-diagramᵉ))
        ( span-span-diagramᵉ 𝒯ᵉ)
    equiv-span-equiv-span-diagramᵉ =
      pr2ᵉ (pr2ᵉ eᵉ)

    spanning-equiv-equiv-span-diagramᵉ :
      spanning-type-span-diagramᵉ 𝒮ᵉ ≃ᵉ spanning-type-span-diagramᵉ 𝒯ᵉ
    spanning-equiv-equiv-span-diagramᵉ =
      equiv-equiv-spanᵉ
        ( concat-spanᵉ
          ( span-span-diagramᵉ 𝒮ᵉ)
          ( map-domain-equiv-span-diagramᵉ)
          ( map-codomain-equiv-span-diagramᵉ))
        ( span-span-diagramᵉ 𝒯ᵉ)
        ( equiv-span-equiv-span-diagramᵉ)

    spanning-map-equiv-span-diagramᵉ :
      spanning-type-span-diagramᵉ 𝒮ᵉ → spanning-type-span-diagramᵉ 𝒯ᵉ
    spanning-map-equiv-span-diagramᵉ =
      map-equiv-spanᵉ
        ( concat-spanᵉ
          ( span-span-diagramᵉ 𝒮ᵉ)
          ( map-domain-equiv-span-diagramᵉ)
          ( map-codomain-equiv-span-diagramᵉ))
        ( span-span-diagramᵉ 𝒯ᵉ)
        ( equiv-span-equiv-span-diagramᵉ)

    is-equiv-spanning-map-equiv-span-diagramᵉ :
      is-equivᵉ spanning-map-equiv-span-diagramᵉ
    is-equiv-spanning-map-equiv-span-diagramᵉ =
      is-equiv-equiv-spanᵉ
        ( concat-spanᵉ
          ( span-span-diagramᵉ 𝒮ᵉ)
          ( map-domain-equiv-span-diagramᵉ)
          ( map-codomain-equiv-span-diagramᵉ))
        ( span-span-diagramᵉ 𝒯ᵉ)
        ( equiv-span-equiv-span-diagramᵉ)

    left-square-equiv-span-diagramᵉ :
      coherence-square-mapsᵉ
        ( spanning-map-equiv-span-diagramᵉ)
        ( left-map-span-diagramᵉ 𝒮ᵉ)
        ( left-map-span-diagramᵉ 𝒯ᵉ)
        ( map-domain-equiv-span-diagramᵉ)
    left-square-equiv-span-diagramᵉ =
      left-triangle-equiv-spanᵉ
        ( concat-spanᵉ
          ( span-span-diagramᵉ 𝒮ᵉ)
          ( map-domain-equiv-span-diagramᵉ)
          ( map-codomain-equiv-span-diagramᵉ))
        ( span-span-diagramᵉ 𝒯ᵉ)
        ( equiv-span-equiv-span-diagramᵉ)

    equiv-left-arrow-equiv-span-diagramᵉ :
      equiv-arrowᵉ (left-map-span-diagramᵉ 𝒮ᵉ) (left-map-span-diagramᵉ 𝒯ᵉ)
    pr1ᵉ equiv-left-arrow-equiv-span-diagramᵉ =
      spanning-equiv-equiv-span-diagramᵉ
    pr1ᵉ (pr2ᵉ equiv-left-arrow-equiv-span-diagramᵉ) =
      equiv-domain-equiv-span-diagramᵉ
    pr2ᵉ (pr2ᵉ equiv-left-arrow-equiv-span-diagramᵉ) =
      left-square-equiv-span-diagramᵉ

    right-square-equiv-span-diagramᵉ :
      coherence-square-mapsᵉ
        ( spanning-map-equiv-span-diagramᵉ)
        ( right-map-span-diagramᵉ 𝒮ᵉ)
        ( right-map-span-diagramᵉ 𝒯ᵉ)
        ( map-codomain-equiv-span-diagramᵉ)
    right-square-equiv-span-diagramᵉ =
      right-triangle-equiv-spanᵉ
        ( concat-spanᵉ
          ( span-span-diagramᵉ 𝒮ᵉ)
          ( map-domain-equiv-span-diagramᵉ)
          ( map-codomain-equiv-span-diagramᵉ))
        ( span-span-diagramᵉ 𝒯ᵉ)
        ( equiv-span-equiv-span-diagramᵉ)

    equiv-right-arrow-equiv-span-diagramᵉ :
      equiv-arrowᵉ (right-map-span-diagramᵉ 𝒮ᵉ) (right-map-span-diagramᵉ 𝒯ᵉ)
    pr1ᵉ equiv-right-arrow-equiv-span-diagramᵉ =
      spanning-equiv-equiv-span-diagramᵉ
    pr1ᵉ (pr2ᵉ equiv-right-arrow-equiv-span-diagramᵉ) =
      equiv-codomain-equiv-span-diagramᵉ
    pr2ᵉ (pr2ᵉ equiv-right-arrow-equiv-span-diagramᵉ) =
      right-square-equiv-span-diagramᵉ

    hom-span-equiv-span-diagramᵉ :
      hom-spanᵉ
        ( concat-spanᵉ
          ( span-span-diagramᵉ 𝒮ᵉ)
          ( map-domain-equiv-span-diagramᵉ)
          ( map-codomain-equiv-span-diagramᵉ))
        ( span-span-diagramᵉ 𝒯ᵉ)
    hom-span-equiv-span-diagramᵉ =
      hom-equiv-spanᵉ
        ( concat-spanᵉ
          ( span-span-diagramᵉ 𝒮ᵉ)
          ( map-domain-equiv-span-diagramᵉ)
          ( map-codomain-equiv-span-diagramᵉ))
        ( span-span-diagramᵉ 𝒯ᵉ)
        ( equiv-span-equiv-span-diagramᵉ)

    hom-equiv-span-diagramᵉ : hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ
    pr1ᵉ hom-equiv-span-diagramᵉ = map-domain-equiv-span-diagramᵉ
    pr1ᵉ (pr2ᵉ hom-equiv-span-diagramᵉ) = map-codomain-equiv-span-diagramᵉ
    pr2ᵉ (pr2ᵉ hom-equiv-span-diagramᵉ) = hom-span-equiv-span-diagramᵉ

    is-equiv-equiv-span-diagramᵉ :
      is-equiv-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ hom-equiv-span-diagramᵉ
    pr1ᵉ is-equiv-equiv-span-diagramᵉ =
      is-equiv-map-domain-equiv-span-diagramᵉ
    pr1ᵉ (pr2ᵉ is-equiv-equiv-span-diagramᵉ) =
      is-equiv-map-codomain-equiv-span-diagramᵉ
    pr2ᵉ (pr2ᵉ is-equiv-equiv-span-diagramᵉ) =
      is-equiv-spanning-map-equiv-span-diagramᵉ

    compute-equiv-span-diagramᵉ :
      Σᵉ (hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ) (is-equiv-hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ) ≃ᵉ
      equiv-span-diagramᵉ
    compute-equiv-span-diagramᵉ =
      ( equiv-totᵉ
        ( λ eᵉ →
          ( equiv-totᵉ
            ( λ fᵉ →
              compute-equiv-spanᵉ
                ( concat-spanᵉ
                  ( span-span-diagramᵉ 𝒮ᵉ)
                  ( map-equivᵉ eᵉ)
                  ( map-equivᵉ fᵉ))
                ( span-span-diagramᵉ 𝒯ᵉ))) ∘eᵉ
          ( interchange-Σ-Σᵉ _))) ∘eᵉ
      ( interchange-Σ-Σᵉ _)
```

### The identity equivalence of span diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  id-equiv-span-diagramᵉ : equiv-span-diagramᵉ 𝒮ᵉ 𝒮ᵉ
  pr1ᵉ id-equiv-span-diagramᵉ = id-equivᵉ
  pr1ᵉ (pr2ᵉ id-equiv-span-diagramᵉ) = id-equivᵉ
  pr2ᵉ (pr2ᵉ id-equiv-span-diagramᵉ) = id-equiv-spanᵉ (span-span-diagramᵉ 𝒮ᵉ)
```

## Properties

### Extensionality of span diagrams

Equalityᵉ ofᵉ spanᵉ diagramsᵉ isᵉ equivalentᵉ to equivalencesᵉ ofᵉ spanᵉ diagrams.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  equiv-eq-span-diagramᵉ :
    (𝒯ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ) → 𝒮ᵉ ＝ᵉ 𝒯ᵉ → equiv-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ
  equiv-eq-span-diagramᵉ 𝒯ᵉ reflᵉ = id-equiv-span-diagramᵉ 𝒮ᵉ

  is-torsorial-equiv-span-diagramᵉ :
    is-torsorialᵉ (equiv-span-diagramᵉ 𝒮ᵉ)
  is-torsorial-equiv-span-diagramᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ (domain-span-diagramᵉ 𝒮ᵉ))
      ( domain-span-diagramᵉ 𝒮ᵉ ,ᵉ id-equivᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-equivᵉ (codomain-span-diagramᵉ 𝒮ᵉ))
        ( codomain-span-diagramᵉ 𝒮ᵉ ,ᵉ id-equivᵉ)
        ( is-torsorial-equiv-spanᵉ (span-span-diagramᵉ 𝒮ᵉ)))

  is-equiv-equiv-eq-span-diagramᵉ :
    (𝒯ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ) → is-equivᵉ (equiv-eq-span-diagramᵉ 𝒯ᵉ)
  is-equiv-equiv-eq-span-diagramᵉ =
    fundamental-theorem-idᵉ is-torsorial-equiv-span-diagramᵉ equiv-eq-span-diagramᵉ

  extensionality-span-diagramᵉ :
    (𝒯ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ) → (𝒮ᵉ ＝ᵉ 𝒯ᵉ) ≃ᵉ equiv-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ
  pr1ᵉ (extensionality-span-diagramᵉ 𝒯ᵉ) = equiv-eq-span-diagramᵉ 𝒯ᵉ
  pr2ᵉ (extensionality-span-diagramᵉ 𝒯ᵉ) = is-equiv-equiv-eq-span-diagramᵉ 𝒯ᵉ

  eq-equiv-span-diagramᵉ :
    (𝒯ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ) → equiv-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ → 𝒮ᵉ ＝ᵉ 𝒯ᵉ
  eq-equiv-span-diagramᵉ 𝒯ᵉ = map-inv-equivᵉ (extensionality-span-diagramᵉ 𝒯ᵉ)
```