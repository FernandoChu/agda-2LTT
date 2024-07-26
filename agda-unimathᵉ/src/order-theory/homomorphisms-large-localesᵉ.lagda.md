# Homomorphisms of large locales

```agda
module order-theory.homomorphisms-large-localesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.homomorphisms-large-framesᵉ
open import order-theory.large-localesᵉ
```

</details>

## Idea

Aᵉ **homomorphismᵉ ofᵉ largeᵉ locales**ᵉ fromᵉ `K`ᵉ to `L`ᵉ isᵉ aᵉ
[frameᵉ homomorphism](order-theory.homomorphisms-large-frames.mdᵉ) fromᵉ `L`ᵉ to
`K`.ᵉ

## Definition

```agda
module _
  {αKᵉ αLᵉ : Level → Level} {βKᵉ βLᵉ : Level → Level → Level} {γᵉ : Level}
  (Kᵉ : Large-Localeᵉ αKᵉ βKᵉ γᵉ) (Lᵉ : Large-Localeᵉ αLᵉ βLᵉ γᵉ)
  where

  hom-Large-Localeᵉ : UUωᵉ
  hom-Large-Localeᵉ = hom-Large-Frameᵉ Lᵉ Kᵉ

  module _
    (fᵉ : hom-Large-Localeᵉ)
    where

    map-hom-Large-Localeᵉ :
      {l1ᵉ : Level} → type-Large-Localeᵉ Lᵉ l1ᵉ → type-Large-Localeᵉ Kᵉ l1ᵉ
    map-hom-Large-Localeᵉ = map-hom-Large-Frameᵉ Lᵉ Kᵉ fᵉ

    preserves-order-hom-Large-Localeᵉ :
      {l1ᵉ l2ᵉ : Level}
      (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ) (yᵉ : type-Large-Localeᵉ Lᵉ l2ᵉ) →
      leq-Large-Localeᵉ Lᵉ xᵉ yᵉ →
      leq-Large-Localeᵉ Kᵉ (map-hom-Large-Localeᵉ xᵉ) (map-hom-Large-Localeᵉ yᵉ)
    preserves-order-hom-Large-Localeᵉ = preserves-order-hom-Large-Frameᵉ Lᵉ Kᵉ fᵉ

    preserves-meets-hom-Large-Localeᵉ :
      {l1ᵉ l2ᵉ : Level}
      (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ) (yᵉ : type-Large-Localeᵉ Lᵉ l2ᵉ) →
      map-hom-Large-Localeᵉ (meet-Large-Localeᵉ Lᵉ xᵉ yᵉ) ＝ᵉ
      meet-Large-Localeᵉ Kᵉ (map-hom-Large-Localeᵉ xᵉ) (map-hom-Large-Localeᵉ yᵉ)
    preserves-meets-hom-Large-Localeᵉ = preserves-meets-hom-Large-Frameᵉ Lᵉ Kᵉ fᵉ

    preserves-top-hom-Large-Localeᵉ :
      map-hom-Large-Localeᵉ (top-Large-Localeᵉ Lᵉ) ＝ᵉ top-Large-Localeᵉ Kᵉ
    preserves-top-hom-Large-Localeᵉ = preserves-top-hom-Large-Frameᵉ Lᵉ Kᵉ fᵉ

    preserves-sup-hom-Large-Localeᵉ :
      {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Localeᵉ Lᵉ l2ᵉ) →
      map-hom-Large-Localeᵉ (sup-Large-Localeᵉ Lᵉ xᵉ) ＝ᵉ
      sup-Large-Localeᵉ Kᵉ (λ iᵉ → map-hom-Large-Localeᵉ (xᵉ iᵉ))
    preserves-sup-hom-Large-Localeᵉ = preserves-sup-hom-Large-Frameᵉ fᵉ
```