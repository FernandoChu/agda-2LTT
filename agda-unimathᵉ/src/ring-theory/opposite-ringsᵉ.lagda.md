# Opposite rings

```agda
module ring-theory.opposite-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Idea

Theᵉ oppositeᵉ ofᵉ aᵉ ringᵉ Rᵉ isᵉ aᵉ ringᵉ with theᵉ sameᵉ underlyingᵉ abelianᵉ group,ᵉ butᵉ
with multiplicationᵉ givenᵉ byᵉ `x·yᵉ :=ᵉ yx`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  op-Ringᵉ : Ringᵉ lᵉ
  pr1ᵉ op-Ringᵉ = ab-Ringᵉ Rᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ op-Ringᵉ)) = mul-Ring'ᵉ Rᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ op-Ringᵉ)) xᵉ yᵉ zᵉ = invᵉ (associative-mul-Ringᵉ Rᵉ zᵉ yᵉ xᵉ)
  pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ op-Ringᵉ))) = one-Ringᵉ Rᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ op-Ringᵉ)))) = right-unit-law-mul-Ringᵉ Rᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ op-Ringᵉ)))) = left-unit-law-mul-Ringᵉ Rᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ op-Ringᵉ))) xᵉ yᵉ zᵉ = right-distributive-mul-add-Ringᵉ Rᵉ yᵉ zᵉ xᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ op-Ringᵉ))) xᵉ yᵉ zᵉ = left-distributive-mul-add-Ringᵉ Rᵉ zᵉ xᵉ yᵉ
```