# Morphisms of magmas

```agda
module structured-types.morphisms-magmasᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.magmasᵉ
```

</details>

## Idea

Aᵉ morphismᵉ ofᵉ magmasᵉ fromᵉ `M`ᵉ to `N`ᵉ isᵉ aᵉ mapᵉ betweenᵉ theirᵉ underlyingᵉ typeᵉ thatᵉ
preservesᵉ theᵉ binaryᵉ operationᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Magmaᵉ l1ᵉ) (Nᵉ : Magmaᵉ l2ᵉ)
  where

  preserves-mul-Magmaᵉ : (type-Magmaᵉ Mᵉ → type-Magmaᵉ Nᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-mul-Magmaᵉ fᵉ =
    (xᵉ yᵉ : type-Magmaᵉ Mᵉ) → Idᵉ (fᵉ (mul-Magmaᵉ Mᵉ xᵉ yᵉ)) (mul-Magmaᵉ Nᵉ (fᵉ xᵉ) (fᵉ yᵉ))

  hom-Magmaᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Magmaᵉ = Σᵉ (type-Magmaᵉ Mᵉ → type-Magmaᵉ Nᵉ) preserves-mul-Magmaᵉ

  map-hom-Magmaᵉ : hom-Magmaᵉ → type-Magmaᵉ Mᵉ → type-Magmaᵉ Nᵉ
  map-hom-Magmaᵉ = pr1ᵉ

  preserves-mul-map-hom-Magmaᵉ :
    (fᵉ : hom-Magmaᵉ) → preserves-mul-Magmaᵉ (map-hom-Magmaᵉ fᵉ)
  preserves-mul-map-hom-Magmaᵉ = pr2ᵉ
```