# Faithful maps

```agda
module foundation.faithful-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-mapsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.setsᵉ
open import foundation-core.truncated-mapsᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Sinceᵉ weᵉ sometimesᵉ thinkᵉ ofᵉ typesᵉ asᵉ ∞-groupoids,ᵉ with theᵉ groupoidᵉ structureᵉ
providedᵉ implicitlyᵉ byᵉ theᵉ identityᵉ typeᵉ andᵉ itsᵉ inductionᵉ principle,ᵉ weᵉ canᵉ
thinkᵉ ofᵉ mapsᵉ asᵉ functorsᵉ ofᵉ ∞-groupoids.ᵉ Weᵉ borrowᵉ someᵉ terminologyᵉ ofᵉ
functors,ᵉ andᵉ callᵉ aᵉ mapᵉ faithfulᵉ ifᵉ itᵉ inducesᵉ embeddingsᵉ onᵉ identityᵉ types.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-faithfulᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-faithfulᵉ fᵉ = (xᵉ yᵉ : Aᵉ) → is-embᵉ (apᵉ fᵉ {xᵉ} {yᵉ})

faithful-mapᵉ : {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
faithful-mapᵉ Aᵉ Bᵉ = Σᵉ (Aᵉ → Bᵉ) is-faithfulᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  map-faithful-mapᵉ : faithful-mapᵉ Aᵉ Bᵉ → Aᵉ → Bᵉ
  map-faithful-mapᵉ = pr1ᵉ

  is-faithful-map-faithful-mapᵉ :
    (fᵉ : faithful-mapᵉ Aᵉ Bᵉ) → is-faithfulᵉ (map-faithful-mapᵉ fᵉ)
  is-faithful-map-faithful-mapᵉ = pr2ᵉ

  emb-ap-faithful-mapᵉ :
    (fᵉ : faithful-mapᵉ Aᵉ Bᵉ) {xᵉ yᵉ : Aᵉ} →
    (xᵉ ＝ᵉ yᵉ) ↪ᵉ (map-faithful-mapᵉ fᵉ xᵉ ＝ᵉ map-faithful-mapᵉ fᵉ yᵉ)
  pr1ᵉ (emb-ap-faithful-mapᵉ fᵉ {xᵉ} {yᵉ}) = apᵉ (map-faithful-mapᵉ fᵉ)
  pr2ᵉ (emb-ap-faithful-mapᵉ fᵉ {xᵉ} {yᵉ}) = is-faithful-map-faithful-mapᵉ fᵉ xᵉ yᵉ

  is-faithful-is-embᵉ : {fᵉ : Aᵉ → Bᵉ} → is-embᵉ fᵉ → is-faithfulᵉ fᵉ
  is-faithful-is-embᵉ {fᵉ} Hᵉ xᵉ yᵉ = is-emb-is-equivᵉ (Hᵉ xᵉ yᵉ)

  faithful-map-embᵉ : (Aᵉ ↪ᵉ Bᵉ) → faithful-mapᵉ Aᵉ Bᵉ
  pr1ᵉ (faithful-map-embᵉ fᵉ) = map-embᵉ fᵉ
  pr2ᵉ (faithful-map-embᵉ fᵉ) = is-faithful-is-embᵉ (is-emb-map-embᵉ fᵉ)

  is-faithful-is-equivᵉ : {fᵉ : Aᵉ → Bᵉ} → is-equivᵉ fᵉ → is-faithfulᵉ fᵉ
  is-faithful-is-equivᵉ Hᵉ = is-faithful-is-embᵉ (is-emb-is-equivᵉ Hᵉ)

  faithful-map-equivᵉ : (Aᵉ ≃ᵉ Bᵉ) → faithful-mapᵉ Aᵉ Bᵉ
  pr1ᵉ (faithful-map-equivᵉ eᵉ) = map-equivᵉ eᵉ
  pr2ᵉ (faithful-map-equivᵉ eᵉ) = is-faithful-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)

  emb-apᵉ : (fᵉ : Aᵉ ↪ᵉ Bᵉ) (xᵉ yᵉ : Aᵉ) → (xᵉ ＝ᵉ yᵉ) ↪ᵉ (map-embᵉ fᵉ xᵉ ＝ᵉ map-embᵉ fᵉ yᵉ)
  pr1ᵉ (emb-apᵉ fᵉ xᵉ yᵉ) = apᵉ (map-embᵉ fᵉ) {xᵉ} {yᵉ}
  pr2ᵉ (emb-apᵉ fᵉ xᵉ yᵉ) = is-faithful-is-embᵉ (is-emb-map-embᵉ fᵉ) xᵉ yᵉ
```

## Examples

### The identity map is faithful

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  id-faithful-mapᵉ : faithful-mapᵉ Aᵉ Aᵉ
  id-faithful-mapᵉ = faithful-map-embᵉ id-embᵉ

  is-faithful-id-faithful-mapᵉ : is-faithfulᵉ (idᵉ {Aᵉ = Aᵉ})
  is-faithful-id-faithful-mapᵉ = is-faithful-map-faithful-mapᵉ id-faithful-mapᵉ
```

### Any `0`-map is faithful

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  is-0-map-is-faithfulᵉ : is-faithfulᵉ fᵉ → is-0-mapᵉ fᵉ
  is-0-map-is-faithfulᵉ Hᵉ =
    is-trunc-map-is-trunc-map-apᵉ neg-one-𝕋ᵉ fᵉ
      ( λ xᵉ yᵉ → is-prop-map-is-embᵉ (Hᵉ xᵉ yᵉ))

  is-faithful-is-0-mapᵉ : is-0-mapᵉ fᵉ → is-faithfulᵉ fᵉ
  is-faithful-is-0-mapᵉ Hᵉ xᵉ yᵉ =
    is-emb-is-prop-mapᵉ (is-trunc-map-ap-is-trunc-mapᵉ neg-one-𝕋ᵉ fᵉ Hᵉ xᵉ yᵉ)
```

## Properties

### The projection map of a family of sets is faithful

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  abstract
    is-faithful-pr1ᵉ :
      {Bᵉ : Aᵉ → UUᵉ l2ᵉ} → ((xᵉ : Aᵉ) → is-setᵉ (Bᵉ xᵉ)) → is-faithfulᵉ (pr1ᵉ {Bᵉ = Bᵉ})
    is-faithful-pr1ᵉ Hᵉ = is-faithful-is-0-mapᵉ (is-0-map-pr1ᵉ Hᵉ)

  pr1-faithful-mapᵉ :
    (Bᵉ : Aᵉ → Setᵉ l2ᵉ) → faithful-mapᵉ (Σᵉ Aᵉ (λ xᵉ → type-Setᵉ (Bᵉ xᵉ))) Aᵉ
  pr1ᵉ (pr1-faithful-mapᵉ Bᵉ) = pr1ᵉ
  pr2ᵉ (pr1-faithful-mapᵉ Bᵉ) = is-faithful-pr1ᵉ (λ xᵉ → is-set-type-Setᵉ (Bᵉ xᵉ))
```

### Faithful maps are closed under homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ gᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ)
  where

  abstract
    is-faithful-htpyᵉ : is-faithfulᵉ gᵉ → is-faithfulᵉ fᵉ
    is-faithful-htpyᵉ Kᵉ =
      is-faithful-is-0-mapᵉ (is-0-map-htpyᵉ Hᵉ (is-0-map-is-faithfulᵉ Kᵉ))
```

### Faithful maps are closed under composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  where

  abstract
    is-faithful-compᵉ :
      (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) →
      is-faithfulᵉ gᵉ → is-faithfulᵉ hᵉ → is-faithfulᵉ (gᵉ ∘ᵉ hᵉ)
    is-faithful-compᵉ gᵉ hᵉ is-faithful-gᵉ is-faithful-hᵉ =
      is-faithful-is-0-mapᵉ
        ( is-0-map-compᵉ gᵉ hᵉ
          ( is-0-map-is-faithfulᵉ is-faithful-gᵉ)
          ( is-0-map-is-faithfulᵉ is-faithful-hᵉ))

  abstract
    is-faithful-left-map-triangleᵉ :
      (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ)) →
      is-faithfulᵉ gᵉ → is-faithfulᵉ hᵉ → is-faithfulᵉ fᵉ
    is-faithful-left-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ is-faithful-gᵉ is-faithful-hᵉ =
      is-faithful-is-0-mapᵉ
        ( is-0-map-left-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ
          ( is-0-map-is-faithfulᵉ is-faithful-gᵉ)
          ( is-0-map-is-faithfulᵉ is-faithful-hᵉ))
```

### If a composite is faithful, then its right factor is faithful

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  where

  is-faithful-right-factorᵉ :
    (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) →
    is-faithfulᵉ gᵉ → is-faithfulᵉ (gᵉ ∘ᵉ hᵉ) → is-faithfulᵉ hᵉ
  is-faithful-right-factorᵉ gᵉ hᵉ is-faithful-gᵉ is-faithful-ghᵉ =
    is-faithful-is-0-mapᵉ
      ( is-0-map-right-factorᵉ gᵉ hᵉ
        ( is-0-map-is-faithfulᵉ is-faithful-gᵉ)
        ( is-0-map-is-faithfulᵉ is-faithful-ghᵉ))

  is-faithful-top-map-triangleᵉ :
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ)) →
    is-faithfulᵉ gᵉ → is-faithfulᵉ fᵉ → is-faithfulᵉ hᵉ
  is-faithful-top-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ is-faithful-gᵉ is-faithful-fᵉ =
    is-faithful-is-0-mapᵉ
      ( is-0-map-top-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ
        ( is-0-map-is-faithfulᵉ is-faithful-gᵉ)
        ( is-0-map-is-faithfulᵉ is-faithful-fᵉ))
```

### The map on total spaces induced by a family of truncated maps is truncated

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ}
  where

  is-faithful-totᵉ : ((xᵉ : Aᵉ) → is-faithfulᵉ (fᵉ xᵉ)) → is-faithfulᵉ (totᵉ fᵉ)
  is-faithful-totᵉ Hᵉ =
    is-faithful-is-0-mapᵉ (is-0-map-totᵉ (λ xᵉ → is-0-map-is-faithfulᵉ (Hᵉ xᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  tot-faithful-mapᵉ :
    ((xᵉ : Aᵉ) → faithful-mapᵉ (Bᵉ xᵉ) (Cᵉ xᵉ)) → faithful-mapᵉ (Σᵉ Aᵉ Bᵉ) (Σᵉ Aᵉ Cᵉ)
  pr1ᵉ (tot-faithful-mapᵉ fᵉ) = totᵉ (λ xᵉ → map-faithful-mapᵉ (fᵉ xᵉ))
  pr2ᵉ (tot-faithful-mapᵉ fᵉ) =
    is-faithful-totᵉ (λ xᵉ → is-faithful-map-faithful-mapᵉ (fᵉ xᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  module _
    {fᵉ : Aᵉ → Bᵉ} (Cᵉ : Bᵉ → UUᵉ l3ᵉ)
    where

    abstract
      is-faithful-map-Σ-map-baseᵉ :
        is-faithfulᵉ fᵉ → is-faithfulᵉ (map-Σ-map-baseᵉ fᵉ Cᵉ)
      is-faithful-map-Σ-map-baseᵉ Hᵉ =
        is-faithful-is-0-mapᵉ
          ( is-0-map-map-Σ-map-baseᵉ Cᵉ (is-0-map-is-faithfulᵉ Hᵉ))

  faithful-map-Σ-faithful-map-baseᵉ :
    (fᵉ : faithful-mapᵉ Aᵉ Bᵉ) (Cᵉ : Bᵉ → UUᵉ l3ᵉ) →
    faithful-mapᵉ (Σᵉ Aᵉ (λ aᵉ → Cᵉ (map-faithful-mapᵉ fᵉ aᵉ))) (Σᵉ Bᵉ Cᵉ)
  pr1ᵉ (faithful-map-Σ-faithful-map-baseᵉ fᵉ Cᵉ) =
    map-Σ-map-baseᵉ (map-faithful-mapᵉ fᵉ) Cᵉ
  pr2ᵉ (faithful-map-Σ-faithful-map-baseᵉ fᵉ Cᵉ) =
    is-faithful-map-Σ-map-baseᵉ Cᵉ (is-faithful-map-faithful-mapᵉ fᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  (Dᵉ : Bᵉ → UUᵉ l4ᵉ) {fᵉ : Aᵉ → Bᵉ} {gᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ → Dᵉ (fᵉ xᵉ)}
  where

  is-faithful-map-Σᵉ :
    is-faithfulᵉ fᵉ → ((xᵉ : Aᵉ) → is-faithfulᵉ (gᵉ xᵉ)) → is-faithfulᵉ (map-Σᵉ Dᵉ fᵉ gᵉ)
  is-faithful-map-Σᵉ Hᵉ Kᵉ =
    is-faithful-is-0-mapᵉ
      ( is-0-map-map-Σᵉ Dᵉ
        ( is-0-map-is-faithfulᵉ Hᵉ)
        ( λ xᵉ → is-0-map-is-faithfulᵉ (Kᵉ xᵉ)))
```