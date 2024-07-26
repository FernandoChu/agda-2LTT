# Sorial type families

```agda
module foundation.sorial-type-familiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Theᵉ notionᵉ ofᵉ _sorialᵉ typeᵉ familyᵉ_ isᵉ aᵉ generalizationᵉ ofᵉ theᵉ notionᵉ ofᵉ
[torsorialᵉ typeᵉ family](foundation.torsorial-type-families.md).ᵉ Recallᵉ thatᵉ ifᵉ aᵉ
typeᵉ familyᵉ `E`ᵉ overᵉ aᵉ [pointedᵉ type](structured-types.pointed-types.mdᵉ) `B`ᵉ isᵉ
torsorial,ᵉ thenᵉ weᵉ obtainᵉ in aᵉ canonicalᵉ way,ᵉ forᵉ eachᵉ `xᵉ : B`ᵉ anᵉ actionᵉ

```text
  Eᵉ xᵉ → (Eᵉ ptᵉ ≃ᵉ Eᵉ xᵉ)
```

Aᵉ **sorialᵉ typeᵉ family**ᵉ isᵉ aᵉ typeᵉ familyᵉ `E`ᵉ overᵉ aᵉ pointedᵉ typeᵉ `B`ᵉ forᵉ whichᵉ
weᵉ haveᵉ suchᵉ anᵉ action.ᵉ

## Definitions

### Sorial type families

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Bᵉ : Pointed-Typeᵉ l1ᵉ) (Eᵉ : type-Pointed-Typeᵉ Bᵉ → UUᵉ l2ᵉ)
  where

  is-sorial-family-of-typesᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-sorial-family-of-typesᵉ =
    (xᵉ : type-Pointed-Typeᵉ Bᵉ) → Eᵉ xᵉ → (Eᵉ (point-Pointed-Typeᵉ Bᵉ) ≃ᵉ Eᵉ xᵉ)
```