# The universal property of the unit type

```agda
module foundation.universal-property-unit-typeᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.diagonal-maps-of-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-contractible-typesᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.constant-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.precomposition-functionsᵉ
```

</details>

## Idea

Theᵉ universalᵉ propertyᵉ ofᵉ theᵉ unitᵉ typeᵉ characterizesᵉ mapsᵉ outᵉ ofᵉ theᵉ unitᵉ type.ᵉ
Similarly,ᵉ theᵉ dependentᵉ universalᵉ propertyᵉ ofᵉ theᵉ unitᵉ typeᵉ characterizesᵉ
dependentᵉ functionsᵉ outᵉ ofᵉ theᵉ unitᵉ type.ᵉ

Inᵉ `foundation.contractible-types`ᵉ weᵉ haveᵉ alreadᵉ provenᵉ relatedᵉ universalᵉ
propertiesᵉ ofᵉ contractibleᵉ types.ᵉ

## Properties

```agda
ev-starᵉ :
  {lᵉ : Level} (Pᵉ : unitᵉ → UUᵉ lᵉ) → ((xᵉ : unitᵉ) → Pᵉ xᵉ) → Pᵉ starᵉ
ev-starᵉ Pᵉ fᵉ = fᵉ starᵉ

ev-star'ᵉ :
  {lᵉ : Level} (Yᵉ : UUᵉ lᵉ) → (unitᵉ → Yᵉ) → Yᵉ
ev-star'ᵉ Yᵉ = ev-starᵉ (λ tᵉ → Yᵉ)

abstract
  dependent-universal-property-unitᵉ :
    {lᵉ : Level} (Pᵉ : unitᵉ → UUᵉ lᵉ) → is-equivᵉ (ev-starᵉ Pᵉ)
  dependent-universal-property-unitᵉ =
    dependent-universal-property-contr-is-contrᵉ starᵉ is-contr-unitᵉ

equiv-dependent-universal-property-unitᵉ :
  {lᵉ : Level} (Pᵉ : unitᵉ → UUᵉ lᵉ) → ((xᵉ : unitᵉ) → Pᵉ xᵉ) ≃ᵉ Pᵉ starᵉ
pr1ᵉ (equiv-dependent-universal-property-unitᵉ Pᵉ) = ev-starᵉ Pᵉ
pr2ᵉ (equiv-dependent-universal-property-unitᵉ Pᵉ) =
  dependent-universal-property-unitᵉ Pᵉ

abstract
  universal-property-unitᵉ :
    {lᵉ : Level} (Yᵉ : UUᵉ lᵉ) → is-equivᵉ (ev-star'ᵉ Yᵉ)
  universal-property-unitᵉ Yᵉ = dependent-universal-property-unitᵉ (λ tᵉ → Yᵉ)

equiv-universal-property-unitᵉ :
  {lᵉ : Level} (Yᵉ : UUᵉ lᵉ) → (unitᵉ → Yᵉ) ≃ᵉ Yᵉ
pr1ᵉ (equiv-universal-property-unitᵉ Yᵉ) = ev-star'ᵉ Yᵉ
pr2ᵉ (equiv-universal-property-unitᵉ Yᵉ) = universal-property-unitᵉ Yᵉ

inv-equiv-universal-property-unitᵉ :
  {lᵉ : Level} (Yᵉ : UUᵉ lᵉ) → Yᵉ ≃ᵉ (unitᵉ → Yᵉ)
inv-equiv-universal-property-unitᵉ Yᵉ =
  inv-equivᵉ (equiv-universal-property-unitᵉ Yᵉ)

abstract
  is-equiv-point-is-contrᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (xᵉ : Xᵉ) →
    is-contrᵉ Xᵉ → is-equivᵉ (pointᵉ xᵉ)
  is-equiv-point-is-contrᵉ xᵉ is-contr-Xᵉ =
    is-equiv-is-contrᵉ (pointᵉ xᵉ) is-contr-unitᵉ is-contr-Xᵉ

abstract
  is-equiv-point-universal-property-unitᵉ :
    {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (xᵉ : Xᵉ) →
    ({l2ᵉ : Level} (Yᵉ : UUᵉ l2ᵉ) → is-equivᵉ (λ (fᵉ : Xᵉ → Yᵉ) → fᵉ xᵉ)) →
    is-equivᵉ (pointᵉ xᵉ)
  is-equiv-point-universal-property-unitᵉ Xᵉ xᵉ Hᵉ =
    is-equiv-is-equiv-precompᵉ
      ( pointᵉ xᵉ)
      ( λ Yᵉ →
        is-equiv-right-factorᵉ
          ( ev-star'ᵉ Yᵉ)
          ( precompᵉ (pointᵉ xᵉ) Yᵉ)
          ( universal-property-unitᵉ Yᵉ)
          ( Hᵉ Yᵉ))

abstract
  universal-property-unit-is-equiv-pointᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (xᵉ : Xᵉ) →
    is-equivᵉ (pointᵉ xᵉ) →
    ({l2ᵉ : Level} (Yᵉ : UUᵉ l2ᵉ) → is-equivᵉ (λ (fᵉ : Xᵉ → Yᵉ) → fᵉ xᵉ))
  universal-property-unit-is-equiv-pointᵉ xᵉ is-equiv-pointᵉ Yᵉ =
    is-equiv-compᵉ
      ( ev-star'ᵉ Yᵉ)
      ( precompᵉ (pointᵉ xᵉ) Yᵉ)
      ( is-equiv-precomp-is-equivᵉ (pointᵉ xᵉ) is-equiv-pointᵉ Yᵉ)
      ( universal-property-unitᵉ Yᵉ)

abstract
  universal-property-unit-is-contrᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (xᵉ : Xᵉ) →
    is-contrᵉ Xᵉ →
    ({l2ᵉ : Level} (Yᵉ : UUᵉ l2ᵉ) → is-equivᵉ (λ (fᵉ : Xᵉ → Yᵉ) → fᵉ xᵉ))
  universal-property-unit-is-contrᵉ xᵉ is-contr-Xᵉ =
    universal-property-unit-is-equiv-pointᵉ xᵉ
      ( is-equiv-point-is-contrᵉ xᵉ is-contr-Xᵉ)

abstract
  is-equiv-diagonal-exponential-is-equiv-pointᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (xᵉ : Xᵉ) →
    is-equivᵉ (pointᵉ xᵉ) →
    ({l2ᵉ : Level} (Yᵉ : UUᵉ l2ᵉ) → is-equivᵉ (diagonal-exponentialᵉ Yᵉ Xᵉ))
  is-equiv-diagonal-exponential-is-equiv-pointᵉ xᵉ is-equiv-pointᵉ Yᵉ =
    is-equiv-is-sectionᵉ
      ( universal-property-unit-is-equiv-pointᵉ xᵉ is-equiv-pointᵉ Yᵉ)
      ( refl-htpyᵉ)
```