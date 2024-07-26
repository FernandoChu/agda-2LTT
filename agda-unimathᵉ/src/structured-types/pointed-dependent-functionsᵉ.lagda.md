# Pointed dependent functions

```agda
module structured-types.pointed-dependent-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-families-of-typesᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ pointedᵉ dependentᵉ functionᵉ ofᵉ aᵉ pointedᵉ familyᵉ `B`ᵉ overᵉ `A`ᵉ isᵉ aᵉ dependentᵉ
functionᵉ ofᵉ theᵉ underlyingᵉ familyᵉ takingᵉ theᵉ baseᵉ pointᵉ ofᵉ `A`ᵉ to theᵉ baseᵉ pointᵉ
ofᵉ `B`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ)
  where

  pointed-Πᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  pointed-Πᵉ =
    fiberᵉ
      ( ev-pointᵉ (point-Pointed-Typeᵉ Aᵉ) {fam-Pointed-Famᵉ Aᵉ Bᵉ})
      ( point-Pointed-Famᵉ Aᵉ Bᵉ)

  Π∗ᵉ = pointed-Πᵉ
```

**Note**ᵉ: theᵉ subscriptᵉ asteriskᵉ symbolᵉ usedᵉ forᵉ theᵉ pointedᵉ dependentᵉ functionᵉ
typeᵉ `Π∗`,ᵉ andᵉ pointedᵉ typeᵉ constructionsᵉ in general,ᵉ isᵉ theᵉ
[asteriskᵉ operator](https://codepoints.net/U+2217ᵉ) `∗`ᵉ (agda-inputᵉ: `\ast`),ᵉ notᵉ
theᵉ [asterisk](https://codepoints.net/U+002Aᵉ) `*`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ}
  where

  function-pointed-Πᵉ :
    pointed-Πᵉ Aᵉ Bᵉ → (xᵉ : type-Pointed-Typeᵉ Aᵉ) → fam-Pointed-Famᵉ Aᵉ Bᵉ xᵉ
  function-pointed-Πᵉ = pr1ᵉ

  preserves-point-function-pointed-Πᵉ :
    (fᵉ : pointed-Πᵉ Aᵉ Bᵉ) →
    Idᵉ (function-pointed-Πᵉ fᵉ (point-Pointed-Typeᵉ Aᵉ)) (point-Pointed-Famᵉ Aᵉ Bᵉ)
  preserves-point-function-pointed-Πᵉ = pr2ᵉ
```