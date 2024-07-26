# Localizations at maps

```agda
module orthogonal-factorization-systems.localizations-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.local-typesᵉ
open import orthogonal-factorization-systems.localizations-subuniversesᵉ
```

</details>

## Idea

Letᵉ `f`ᵉ beᵉ aᵉ mapᵉ ofᵉ typeᵉ `Aᵉ → B`ᵉ andᵉ let `X`ᵉ beᵉ aᵉ type.ᵉ Theᵉ **localization**ᵉ ofᵉ
`X`ᵉ atᵉ `f`,ᵉ orᵉ **`f`-localization**,ᵉ isᵉ anᵉ
`f`[-local](orthogonal-factorization-systems.local-types.mdᵉ) typeᵉ `Y`ᵉ togetherᵉ
with aᵉ mapᵉ `ηᵉ : Xᵉ → Y`ᵉ with theᵉ propertyᵉ thatᵉ everyᵉ typeᵉ thatᵉ isᵉ `f`-localᵉ isᵉ
alsoᵉ `η`-local.ᵉ

## Definition

### The predicate of being a localization at a map

```agda
is-localizationᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (l5ᵉ : Level)
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  (Xᵉ : UUᵉ l3ᵉ) (Yᵉ : UUᵉ l4ᵉ) (ηᵉ : Xᵉ → Yᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ lsuc l5ᵉ)
is-localizationᵉ l5ᵉ fᵉ Xᵉ Yᵉ ηᵉ =
  ( is-localᵉ fᵉ Yᵉ) ×ᵉ
  ( (Zᵉ : UUᵉ l5ᵉ) → is-localᵉ fᵉ Zᵉ → is-localᵉ ηᵉ Zᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {ηᵉ : Xᵉ → Yᵉ}
  (is-localization-Yᵉ : is-localizationᵉ l5ᵉ fᵉ Xᵉ Yᵉ ηᵉ)
  where

  is-local-is-localizationᵉ : is-localᵉ fᵉ Yᵉ
  is-local-is-localizationᵉ = pr1ᵉ is-localization-Yᵉ
```

### The type of localizations of a type with respect to a map

```agda
localizationᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (l4ᵉ l5ᵉ : Level)
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  (Xᵉ : UUᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ lsuc l4ᵉ ⊔ lsuc l5ᵉ)
localizationᵉ l4ᵉ l5ᵉ fᵉ Xᵉ =
  Σᵉ (UUᵉ l4ᵉ) (λ Yᵉ → Σᵉ (Xᵉ → Yᵉ) (is-localizationᵉ l5ᵉ fᵉ Xᵉ Yᵉ))
```

## Properties

### Localizations at a map are localizations at a subuniverse

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  (Xᵉ : UUᵉ l3ᵉ) (Yᵉ : UUᵉ l4ᵉ) (ηᵉ : Xᵉ → Yᵉ)
  where

  is-subuniverse-localization-is-localizationᵉ :
    is-localizationᵉ l4ᵉ fᵉ Xᵉ Yᵉ ηᵉ →
    is-subuniverse-localizationᵉ (is-local-Propᵉ fᵉ) Xᵉ Yᵉ
  pr1ᵉ (is-subuniverse-localization-is-localizationᵉ is-localization-Yᵉ) =
    pr1ᵉ is-localization-Yᵉ
  pr1ᵉ (pr2ᵉ (is-subuniverse-localization-is-localizationᵉ is-localization-Yᵉ)) = ηᵉ
  pr2ᵉ (pr2ᵉ (is-subuniverse-localization-is-localizationᵉ is-localization-Yᵉ))
    Zᵉ is-local-Zᵉ =
      pr2ᵉ is-localization-Yᵉ Zᵉ is-local-Zᵉ
```

Itᵉ remainsᵉ to constructᵉ aᵉ converse.ᵉ

## References

{{#bibliographyᵉ}} {{#referenceᵉ RSS20ᵉ}} {{#referenceᵉ Rij19ᵉ}}