# `0`-Connected types

```agda
module foundation.0-connected-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.fiber-inclusionsᵉ
open import foundation.functoriality-set-truncationᵉ
open import foundation.inhabited-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.set-truncationsᵉ
open import foundation.setsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-contractible-typesᵉ
open import foundation.universal-property-unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.precomposition-functionsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.truncated-mapsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ saidᵉ to beᵉ connectedᵉ ifᵉ itsᵉ typeᵉ ofᵉ connectedᵉ components,ᵉ i.e.,ᵉ itsᵉ
setᵉ truncation,ᵉ isᵉ contractible.ᵉ

```agda
is-0-connected-Propᵉ : {lᵉ : Level} → UUᵉ lᵉ → Propᵉ lᵉ
is-0-connected-Propᵉ Aᵉ = is-contr-Propᵉ (type-trunc-Setᵉ Aᵉ)

is-0-connectedᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
is-0-connectedᵉ Aᵉ = type-Propᵉ (is-0-connected-Propᵉ Aᵉ)

is-prop-is-0-connectedᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → is-propᵉ (is-0-connectedᵉ Aᵉ)
is-prop-is-0-connectedᵉ Aᵉ = is-prop-type-Propᵉ (is-0-connected-Propᵉ Aᵉ)

abstract
  is-inhabited-is-0-connectedᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-0-connectedᵉ Aᵉ → is-inhabitedᵉ Aᵉ
  is-inhabited-is-0-connectedᵉ {lᵉ} {Aᵉ} Cᵉ =
    apply-universal-property-trunc-Set'ᵉ
      ( centerᵉ Cᵉ)
      ( set-Propᵉ (trunc-Propᵉ Aᵉ))
      ( unit-trunc-Propᵉ)

abstract
  mere-eq-is-0-connectedᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-0-connectedᵉ Aᵉ → (xᵉ yᵉ : Aᵉ) → mere-eqᵉ xᵉ yᵉ
  mere-eq-is-0-connectedᵉ {Aᵉ = Aᵉ} Hᵉ xᵉ yᵉ =
    apply-effectiveness-unit-trunc-Setᵉ (eq-is-contrᵉ Hᵉ)

abstract
  is-0-connected-mere-eqᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (aᵉ : Aᵉ) →
    ((xᵉ : Aᵉ) → mere-eqᵉ aᵉ xᵉ) → is-0-connectedᵉ Aᵉ
  is-0-connected-mere-eqᵉ {lᵉ} {Aᵉ} aᵉ eᵉ =
    pairᵉ
      ( unit-trunc-Setᵉ aᵉ)
      ( apply-dependent-universal-property-trunc-Set'ᵉ
        ( λ xᵉ → set-Propᵉ (Id-Propᵉ (trunc-Setᵉ Aᵉ) (unit-trunc-Setᵉ aᵉ) xᵉ))
        ( λ xᵉ → apply-effectiveness-unit-trunc-Set'ᵉ (eᵉ xᵉ)))

abstract
  is-0-connected-mere-eq-is-inhabitedᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
    is-inhabitedᵉ Aᵉ → ((xᵉ yᵉ : Aᵉ) → mere-eqᵉ xᵉ yᵉ) → is-0-connectedᵉ Aᵉ
  is-0-connected-mere-eq-is-inhabitedᵉ Hᵉ Kᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( is-0-connected-Propᵉ _)
      ( λ aᵉ → is-0-connected-mere-eqᵉ aᵉ (Kᵉ aᵉ))

is-0-connected-is-surjective-pointᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) →
  is-surjectiveᵉ (pointᵉ aᵉ) → is-0-connectedᵉ Aᵉ
is-0-connected-is-surjective-pointᵉ aᵉ Hᵉ =
  is-0-connected-mere-eqᵉ aᵉ
    ( λ xᵉ →
      apply-universal-property-trunc-Propᵉ
        ( Hᵉ xᵉ)
        ( mere-eq-Propᵉ aᵉ xᵉ)
        ( λ uᵉ → unit-trunc-Propᵉ (pr2ᵉ uᵉ)))

abstract
  is-surjective-point-is-0-connectedᵉ :
    {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) →
    is-0-connectedᵉ Aᵉ → is-surjectiveᵉ (pointᵉ aᵉ)
  is-surjective-point-is-0-connectedᵉ aᵉ Hᵉ xᵉ =
    apply-universal-property-trunc-Propᵉ
      ( mere-eq-is-0-connectedᵉ Hᵉ aᵉ xᵉ)
      ( trunc-Propᵉ (fiberᵉ (pointᵉ aᵉ) xᵉ))
      ( λ where reflᵉ → unit-trunc-Propᵉ (starᵉ ,ᵉ reflᵉ))

is-trunc-map-ev-point-is-connectedᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (aᵉ : Aᵉ) →
  is-0-connectedᵉ Aᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) Bᵉ →
  is-trunc-mapᵉ kᵉ (ev-point'ᵉ aᵉ {Bᵉ})
is-trunc-map-ev-point-is-connectedᵉ kᵉ {Aᵉ} {Bᵉ} aᵉ Hᵉ Kᵉ =
  is-trunc-map-compᵉ kᵉ
    ( ev-point'ᵉ starᵉ {Bᵉ})
    ( precompᵉ (pointᵉ aᵉ) Bᵉ)
    ( is-trunc-map-is-equivᵉ kᵉ
      ( universal-property-contr-is-contrᵉ starᵉ is-contr-unitᵉ Bᵉ))
    ( is-trunc-map-precomp-Π-is-surjectiveᵉ kᵉ
      ( is-surjective-point-is-0-connectedᵉ aᵉ Hᵉ)
      ( λ _ → (Bᵉ ,ᵉ Kᵉ)))

equiv-dependent-universal-property-is-0-connectedᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) → is-0-connectedᵉ Aᵉ →
  ( {lᵉ : Level} (Pᵉ : Aᵉ → Propᵉ lᵉ) →
    ((xᵉ : Aᵉ) → type-Propᵉ (Pᵉ xᵉ)) ≃ᵉ type-Propᵉ (Pᵉ aᵉ))
equiv-dependent-universal-property-is-0-connectedᵉ aᵉ Hᵉ Pᵉ =
  ( equiv-universal-property-unitᵉ (type-Propᵉ (Pᵉ aᵉ))) ∘eᵉ
  ( equiv-dependent-universal-property-surjection-is-surjectiveᵉ
    ( pointᵉ aᵉ)
    ( is-surjective-point-is-0-connectedᵉ aᵉ Hᵉ)
    ( Pᵉ))

apply-dependent-universal-property-is-0-connectedᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) → is-0-connectedᵉ Aᵉ →
  {lᵉ : Level} (Pᵉ : Aᵉ → Propᵉ lᵉ) → type-Propᵉ (Pᵉ aᵉ) → (xᵉ : Aᵉ) → type-Propᵉ (Pᵉ xᵉ)
apply-dependent-universal-property-is-0-connectedᵉ aᵉ Hᵉ Pᵉ =
  map-inv-equivᵉ (equiv-dependent-universal-property-is-0-connectedᵉ aᵉ Hᵉ Pᵉ)

abstract
  is-surjective-fiber-inclusionᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    is-0-connectedᵉ Aᵉ → (aᵉ : Aᵉ) → is-surjectiveᵉ (fiber-inclusionᵉ Bᵉ aᵉ)
  is-surjective-fiber-inclusionᵉ {Bᵉ = Bᵉ} Cᵉ aᵉ (xᵉ ,ᵉ bᵉ) =
    apply-universal-property-trunc-Propᵉ
      ( mere-eq-is-0-connectedᵉ Cᵉ aᵉ xᵉ)
      ( trunc-Propᵉ (fiberᵉ (fiber-inclusionᵉ Bᵉ aᵉ) (xᵉ ,ᵉ bᵉ)))
      ( λ where reflᵉ → unit-trunc-Propᵉ (bᵉ ,ᵉ reflᵉ))

abstract
  mere-eq-is-surjective-fiber-inclusionᵉ :
    {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) →
    ({lᵉ : Level} (Bᵉ : Aᵉ → UUᵉ lᵉ) → is-surjectiveᵉ (fiber-inclusionᵉ Bᵉ aᵉ)) →
    (xᵉ : Aᵉ) → mere-eqᵉ aᵉ xᵉ
  mere-eq-is-surjective-fiber-inclusionᵉ aᵉ Hᵉ xᵉ =
    apply-universal-property-trunc-Propᵉ
      ( Hᵉ (λ xᵉ → unitᵉ) (xᵉ ,ᵉ starᵉ))
      ( mere-eq-Propᵉ aᵉ xᵉ)
      ( λ uᵉ → unit-trunc-Propᵉ (apᵉ pr1ᵉ (pr2ᵉ uᵉ)))

abstract
  is-0-connected-is-surjective-fiber-inclusionᵉ :
    {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) →
    ({lᵉ : Level} (Bᵉ : Aᵉ → UUᵉ lᵉ) → is-surjectiveᵉ (fiber-inclusionᵉ Bᵉ aᵉ)) →
    is-0-connectedᵉ Aᵉ
  is-0-connected-is-surjective-fiber-inclusionᵉ aᵉ Hᵉ =
    is-0-connected-mere-eqᵉ aᵉ (mere-eq-is-surjective-fiber-inclusionᵉ aᵉ Hᵉ)

is-0-connected-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (Aᵉ ≃ᵉ Bᵉ) → is-0-connectedᵉ Bᵉ → is-0-connectedᵉ Aᵉ
is-0-connected-equivᵉ eᵉ = is-contr-equivᵉ _ (equiv-trunc-Setᵉ eᵉ)

is-0-connected-equiv'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (Aᵉ ≃ᵉ Bᵉ) → is-0-connectedᵉ Aᵉ → is-0-connectedᵉ Bᵉ
is-0-connected-equiv'ᵉ eᵉ = is-0-connected-equivᵉ (inv-equivᵉ eᵉ)
```

### `0-connected` types are closed under cartesian products

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : UUᵉ l2ᵉ)
  (p1ᵉ : is-0-connectedᵉ Xᵉ) (p2ᵉ : is-0-connectedᵉ Yᵉ)
  where

  is-0-connected-productᵉ : is-0-connectedᵉ (Xᵉ ×ᵉ Yᵉ)
  is-0-connected-productᵉ =
    is-contr-equivᵉ
      ( type-trunc-Setᵉ Xᵉ ×ᵉ type-trunc-Setᵉ Yᵉ)
      ( equiv-distributive-trunc-product-Setᵉ Xᵉ Yᵉ)
      ( is-contr-productᵉ p1ᵉ p2ᵉ)
```

### A contractible type is `0`-connected

```agda
is-0-connected-is-contrᵉ :
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) →
  is-contrᵉ Xᵉ → is-0-connectedᵉ Xᵉ
is-0-connected-is-contrᵉ Xᵉ pᵉ =
  is-contr-equivᵉ Xᵉ (inv-equivᵉ (equiv-unit-trunc-Setᵉ (Xᵉ ,ᵉ is-set-is-contrᵉ pᵉ))) pᵉ
```