# Pairs of distinct elements

```agda
module foundation.pairs-of-distinct-elementsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Pairsᵉ ofᵉ distinctᵉ elementsᵉ in aᵉ typeᵉ `A`ᵉ consistᵉ ofᵉ twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ ofᵉ
`A`ᵉ equippedᵉ with anᵉ elementᵉ ofᵉ typeᵉ `xᵉ ≠ᵉ y`.ᵉ

## Definition

```agda
pair-of-distinct-elementsᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
pair-of-distinct-elementsᵉ Aᵉ =
  Σᵉ Aᵉ (λ xᵉ → Σᵉ Aᵉ (λ yᵉ → xᵉ ≠ᵉ yᵉ))

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (pᵉ : pair-of-distinct-elementsᵉ Aᵉ)
  where

  first-pair-of-distinct-elementsᵉ : Aᵉ
  first-pair-of-distinct-elementsᵉ = pr1ᵉ pᵉ

  second-pair-of-distinct-elementsᵉ : Aᵉ
  second-pair-of-distinct-elementsᵉ = pr1ᵉ (pr2ᵉ pᵉ)

  distinction-pair-of-distinct-elementsᵉ :
    first-pair-of-distinct-elementsᵉ ≠ᵉ second-pair-of-distinct-elementsᵉ
  distinction-pair-of-distinct-elementsᵉ = pr2ᵉ (pr2ᵉ pᵉ)
```

## Properties

### Characterization of the identity type of the type of pairs of distinct elements

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  Eq-pair-of-distinct-elementsᵉ :
    (pᵉ qᵉ : pair-of-distinct-elementsᵉ Aᵉ) → UUᵉ lᵉ
  Eq-pair-of-distinct-elementsᵉ pᵉ qᵉ =
    (first-pair-of-distinct-elementsᵉ pᵉ ＝ᵉ first-pair-of-distinct-elementsᵉ qᵉ) ×ᵉ
    (second-pair-of-distinct-elementsᵉ pᵉ ＝ᵉ second-pair-of-distinct-elementsᵉ qᵉ)

  refl-Eq-pair-of-distinct-elementsᵉ :
    (pᵉ : pair-of-distinct-elementsᵉ Aᵉ) → Eq-pair-of-distinct-elementsᵉ pᵉ pᵉ
  pr1ᵉ (refl-Eq-pair-of-distinct-elementsᵉ pᵉ) = reflᵉ
  pr2ᵉ (refl-Eq-pair-of-distinct-elementsᵉ pᵉ) = reflᵉ

  Eq-eq-pair-of-distinct-elementsᵉ :
    (pᵉ qᵉ : pair-of-distinct-elementsᵉ Aᵉ) →
    pᵉ ＝ᵉ qᵉ → Eq-pair-of-distinct-elementsᵉ pᵉ qᵉ
  Eq-eq-pair-of-distinct-elementsᵉ pᵉ .pᵉ reflᵉ =
    refl-Eq-pair-of-distinct-elementsᵉ pᵉ

  is-torsorial-Eq-pair-of-distinct-elementsᵉ :
    (pᵉ : pair-of-distinct-elementsᵉ Aᵉ) →
    is-torsorialᵉ (Eq-pair-of-distinct-elementsᵉ pᵉ)
  is-torsorial-Eq-pair-of-distinct-elementsᵉ pᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-Idᵉ (first-pair-of-distinct-elementsᵉ pᵉ))
      ( pairᵉ (first-pair-of-distinct-elementsᵉ pᵉ) reflᵉ)
      ( is-torsorial-Eq-subtypeᵉ
        ( is-torsorial-Idᵉ (second-pair-of-distinct-elementsᵉ pᵉ))
        ( λ xᵉ → is-prop-negᵉ)
        ( second-pair-of-distinct-elementsᵉ pᵉ)
        ( reflᵉ)
        ( distinction-pair-of-distinct-elementsᵉ pᵉ))

  is-equiv-Eq-eq-pair-of-distinct-elementsᵉ :
    (pᵉ qᵉ : pair-of-distinct-elementsᵉ Aᵉ) →
    is-equivᵉ (Eq-eq-pair-of-distinct-elementsᵉ pᵉ qᵉ)
  is-equiv-Eq-eq-pair-of-distinct-elementsᵉ pᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-Eq-pair-of-distinct-elementsᵉ pᵉ)
      ( Eq-eq-pair-of-distinct-elementsᵉ pᵉ)

  eq-Eq-pair-of-distinct-elementsᵉ :
    {pᵉ qᵉ : pair-of-distinct-elementsᵉ Aᵉ} →
    first-pair-of-distinct-elementsᵉ pᵉ ＝ᵉ first-pair-of-distinct-elementsᵉ qᵉ →
    second-pair-of-distinct-elementsᵉ pᵉ ＝ᵉ second-pair-of-distinct-elementsᵉ qᵉ →
    pᵉ ＝ᵉ qᵉ
  eq-Eq-pair-of-distinct-elementsᵉ {pᵉ} {qᵉ} αᵉ βᵉ =
    map-inv-is-equivᵉ (is-equiv-Eq-eq-pair-of-distinct-elementsᵉ pᵉ qᵉ) (pairᵉ αᵉ βᵉ)
```

### Equivalences map pairs of distinct elements to pairs of distinct elements

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  map-equiv-pair-of-distinct-elementsᵉ :
    pair-of-distinct-elementsᵉ Aᵉ → pair-of-distinct-elementsᵉ Bᵉ
  pr1ᵉ (map-equiv-pair-of-distinct-elementsᵉ pᵉ) =
    map-equivᵉ eᵉ (first-pair-of-distinct-elementsᵉ pᵉ)
  pr1ᵉ (pr2ᵉ (map-equiv-pair-of-distinct-elementsᵉ pᵉ)) =
    map-equivᵉ eᵉ (second-pair-of-distinct-elementsᵉ pᵉ)
  pr2ᵉ (pr2ᵉ (map-equiv-pair-of-distinct-elementsᵉ pᵉ)) qᵉ =
    distinction-pair-of-distinct-elementsᵉ pᵉ
      ( is-injective-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) qᵉ)

  map-inv-equiv-pair-of-distinct-elementsᵉ :
    pair-of-distinct-elementsᵉ Bᵉ → pair-of-distinct-elementsᵉ Aᵉ
  pr1ᵉ (map-inv-equiv-pair-of-distinct-elementsᵉ qᵉ) =
    map-inv-equivᵉ eᵉ (first-pair-of-distinct-elementsᵉ qᵉ)
  pr1ᵉ (pr2ᵉ (map-inv-equiv-pair-of-distinct-elementsᵉ qᵉ)) =
    map-inv-equivᵉ eᵉ (second-pair-of-distinct-elementsᵉ qᵉ)
  pr2ᵉ (pr2ᵉ (map-inv-equiv-pair-of-distinct-elementsᵉ qᵉ)) pᵉ =
    distinction-pair-of-distinct-elementsᵉ qᵉ
      ( is-injective-is-equivᵉ (is-equiv-map-inv-equivᵉ eᵉ) pᵉ)

  is-section-map-inv-equiv-pair-of-distinct-elementsᵉ :
    (qᵉ : pair-of-distinct-elementsᵉ Bᵉ) →
    ( map-equiv-pair-of-distinct-elementsᵉ
      ( map-inv-equiv-pair-of-distinct-elementsᵉ qᵉ)) ＝ᵉ
    ( qᵉ)
  is-section-map-inv-equiv-pair-of-distinct-elementsᵉ qᵉ =
    eq-Eq-pair-of-distinct-elementsᵉ
      ( is-section-map-inv-equivᵉ eᵉ (first-pair-of-distinct-elementsᵉ qᵉ))
      ( is-section-map-inv-equivᵉ eᵉ (second-pair-of-distinct-elementsᵉ qᵉ))

  is-retraction-map-inv-equiv-pair-of-distinct-elementsᵉ :
    (pᵉ : pair-of-distinct-elementsᵉ Aᵉ) →
    ( map-inv-equiv-pair-of-distinct-elementsᵉ
      ( map-equiv-pair-of-distinct-elementsᵉ pᵉ)) ＝ᵉ
    ( pᵉ)
  is-retraction-map-inv-equiv-pair-of-distinct-elementsᵉ pᵉ =
    eq-Eq-pair-of-distinct-elementsᵉ
      ( is-retraction-map-inv-equivᵉ eᵉ (first-pair-of-distinct-elementsᵉ pᵉ))
      ( is-retraction-map-inv-equivᵉ eᵉ (second-pair-of-distinct-elementsᵉ pᵉ))

  is-equiv-map-equiv-pair-of-distinct-elementsᵉ :
    is-equivᵉ map-equiv-pair-of-distinct-elementsᵉ
  is-equiv-map-equiv-pair-of-distinct-elementsᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-equiv-pair-of-distinct-elementsᵉ
      is-section-map-inv-equiv-pair-of-distinct-elementsᵉ
      is-retraction-map-inv-equiv-pair-of-distinct-elementsᵉ

  equiv-pair-of-distinct-elementsᵉ :
    pair-of-distinct-elementsᵉ Aᵉ ≃ᵉ pair-of-distinct-elementsᵉ Bᵉ
  pr1ᵉ equiv-pair-of-distinct-elementsᵉ = map-equiv-pair-of-distinct-elementsᵉ
  pr2ᵉ equiv-pair-of-distinct-elementsᵉ =
    is-equiv-map-equiv-pair-of-distinct-elementsᵉ
```

### Embeddings map pairs of distinct elements to pairs of distinct elements

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ↪ᵉ Bᵉ)
  where

  emb-pair-of-distinct-elementsᵉ :
    pair-of-distinct-elementsᵉ Aᵉ ↪ᵉ pair-of-distinct-elementsᵉ Bᵉ
  emb-pair-of-distinct-elementsᵉ =
    emb-Σᵉ
      ( λ xᵉ → Σᵉ Bᵉ (λ yᵉ → xᵉ ≠ᵉ yᵉ))
      ( eᵉ)
      ( λ xᵉ →
        emb-Σᵉ
          ( λ yᵉ → map-embᵉ eᵉ xᵉ ≠ᵉ yᵉ)
          ( eᵉ)
          ( λ _ → emb-equivᵉ (equiv-negᵉ (equiv-ap-embᵉ eᵉ))))

  map-emb-pair-of-distinct-elementsᵉ :
    pair-of-distinct-elementsᵉ Aᵉ → pair-of-distinct-elementsᵉ Bᵉ
  map-emb-pair-of-distinct-elementsᵉ =
    map-embᵉ emb-pair-of-distinct-elementsᵉ

  is-emb-map-emb-pair-of-distinct-elementsᵉ :
    is-embᵉ map-emb-pair-of-distinct-elementsᵉ
  is-emb-map-emb-pair-of-distinct-elementsᵉ =
    is-emb-map-embᵉ emb-pair-of-distinct-elementsᵉ
```