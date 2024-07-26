# Localizations at subuniverses

```agda
module orthogonal-factorization-systems.localizations-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.local-typesᵉ
```

</details>

## Idea

Letᵉ `P`ᵉ beᵉ aᵉ [subuniverse](foundation.subuniverses.md).ᵉ Givenᵉ aᵉ typeᵉ `X`,ᵉ itsᵉ
**localization**ᵉ atᵉ `P`,ᵉ orᵉ **`P`-localization**,ᵉ isᵉ aᵉ typeᵉ `Y`ᵉ in `P`ᵉ andᵉ aᵉ mapᵉ
`ηᵉ : Xᵉ → Y`ᵉ suchᵉ thatᵉ everyᵉ typeᵉ in `P`ᵉ isᵉ
`η`[-local](orthogonal-factorization-systems.local-types.md).ᵉ I.e.ᵉ forᵉ everyᵉ `Z`ᵉ
in `P`,ᵉ theᵉ [precompositionᵉ map](foundation-core.function-types.mdᵉ)

```text
  _∘ᵉ ηᵉ : (Yᵉ → Zᵉ) → (Xᵉ → Zᵉ)
```

isᵉ anᵉ [equivalence](foundation-core.equivalences.md).ᵉ

## Definition

### The predicate of being a localization at a subuniverse

```agda
is-subuniverse-localizationᵉ :
  {l1ᵉ l2ᵉ lPᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ lPᵉ) →
  UUᵉ l2ᵉ → UUᵉ l1ᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ lPᵉ)
is-subuniverse-localizationᵉ {l1ᵉ} {l2ᵉ} Pᵉ Xᵉ Yᵉ =
  ( is-in-subuniverseᵉ Pᵉ Yᵉ) ×ᵉ
  ( Σᵉ ( Xᵉ → Yᵉ)
      ( λ ηᵉ → (Zᵉ : UUᵉ l1ᵉ) → is-in-subuniverseᵉ Pᵉ Zᵉ → is-localᵉ ηᵉ Zᵉ))
```

```agda
module _
  {l1ᵉ l2ᵉ lPᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ lPᵉ) {Xᵉ : UUᵉ l2ᵉ} {Yᵉ : UUᵉ l1ᵉ}
  (is-localization-Yᵉ : is-subuniverse-localizationᵉ Pᵉ Xᵉ Yᵉ)
  where

  is-in-subuniverse-is-subuniverse-localizationᵉ : is-in-subuniverseᵉ Pᵉ Yᵉ
  is-in-subuniverse-is-subuniverse-localizationᵉ = pr1ᵉ is-localization-Yᵉ

  unit-is-subuniverse-localizationᵉ : Xᵉ → Yᵉ
  unit-is-subuniverse-localizationᵉ = pr1ᵉ (pr2ᵉ is-localization-Yᵉ)

  is-local-at-unit-is-in-subuniverse-is-subuniverse-localizationᵉ :
    (Zᵉ : UUᵉ l1ᵉ) → is-in-subuniverseᵉ Pᵉ Zᵉ →
    is-localᵉ unit-is-subuniverse-localizationᵉ Zᵉ
  is-local-at-unit-is-in-subuniverse-is-subuniverse-localizationᵉ =
    pr2ᵉ (pr2ᵉ is-localization-Yᵉ)
```

### The type of localizations at a subuniverse

```agda
subuniverse-localizationᵉ :
  {l1ᵉ l2ᵉ lPᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ lPᵉ) → UUᵉ l2ᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ lPᵉ)
subuniverse-localizationᵉ {l1ᵉ} Pᵉ Xᵉ = Σᵉ (UUᵉ l1ᵉ) (is-subuniverse-localizationᵉ Pᵉ Xᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ lPᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ lPᵉ)
  {Xᵉ : UUᵉ l2ᵉ} (Lᵉ : subuniverse-localizationᵉ Pᵉ Xᵉ)
  where

  type-subuniverse-localizationᵉ : UUᵉ l1ᵉ
  type-subuniverse-localizationᵉ = pr1ᵉ Lᵉ

  is-subuniverse-localization-subuniverse-localizationᵉ :
    is-subuniverse-localizationᵉ Pᵉ Xᵉ type-subuniverse-localizationᵉ
  is-subuniverse-localization-subuniverse-localizationᵉ = pr2ᵉ Lᵉ

  is-in-subuniverse-subuniverse-localizationᵉ :
    is-in-subuniverseᵉ Pᵉ type-subuniverse-localizationᵉ
  is-in-subuniverse-subuniverse-localizationᵉ =
    is-in-subuniverse-is-subuniverse-localizationᵉ Pᵉ
      ( is-subuniverse-localization-subuniverse-localizationᵉ)

  unit-subuniverse-localizationᵉ : Xᵉ → type-subuniverse-localizationᵉ
  unit-subuniverse-localizationᵉ =
    unit-is-subuniverse-localizationᵉ Pᵉ
      ( is-subuniverse-localization-subuniverse-localizationᵉ)

  is-local-at-unit-is-in-subuniverse-subuniverse-localizationᵉ :
    (Zᵉ : UUᵉ l1ᵉ) →
    is-in-subuniverseᵉ Pᵉ Zᵉ → is-localᵉ unit-subuniverse-localizationᵉ Zᵉ
  is-local-at-unit-is-in-subuniverse-subuniverse-localizationᵉ =
    is-local-at-unit-is-in-subuniverse-is-subuniverse-localizationᵉ Pᵉ
      ( is-subuniverse-localization-subuniverse-localizationᵉ)
```

## Properties

### There is at most one `P`-localization

Thisᵉ isᵉ Propositionᵉ 5.1.2ᵉ in _Classifyingᵉ Types_,ᵉ andᵉ remainsᵉ to beᵉ formalized.ᵉ

## See also

-ᵉ [Localizationsᵉ atᵉ maps](orthogonal-factorization-systems.localizations-maps.mdᵉ)

## References

{{#bibliographyᵉ}} {{#referenceᵉ RSS20ᵉ}} {{#referenceᵉ Rij19ᵉ}}