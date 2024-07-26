# Pointed dependent pair types

```agda
module structured-types.pointed-dependent-pair-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-families-of-typesᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ pointedᵉ typeᵉ `(Aᵉ ,ᵉ a)`ᵉ andᵉ aᵉ pointedᵉ familyᵉ overᵉ itᵉ `(Bᵉ ,ᵉ b)`,ᵉ thenᵉ theᵉ
dependentᵉ pairᵉ typeᵉ `Σᵉ Aᵉ B`ᵉ isᵉ againᵉ canonicallyᵉ pointedᵉ atᵉ `(aᵉ ,ᵉ b)`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  where

  Σ-Pointed-Typeᵉ :
    (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ) → Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (Σ-Pointed-Typeᵉ (Aᵉ ,ᵉ aᵉ) (Bᵉ ,ᵉ bᵉ)) = Σᵉ Aᵉ Bᵉ
  pr2ᵉ (Σ-Pointed-Typeᵉ (Aᵉ ,ᵉ aᵉ) (Bᵉ ,ᵉ bᵉ)) = aᵉ ,ᵉ bᵉ

  Σ∗ᵉ = Σ-Pointed-Typeᵉ
```

**Note**ᵉ: theᵉ subscriptᵉ asteriskᵉ symbolᵉ usedᵉ forᵉ theᵉ pointedᵉ dependentᵉ pairᵉ typeᵉ
`Σ∗`,ᵉ andᵉ pointedᵉ typeᵉ constructionsᵉ in general,ᵉ isᵉ theᵉ
[asteriskᵉ operator](https://codepoints.net/U+2217ᵉ) `∗`ᵉ (agda-inputᵉ: `\ast`),ᵉ notᵉ
theᵉ [asterisk](https://codepoints.net/U+002Aᵉ) `*`.ᵉ