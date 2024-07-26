# Codiagonal maps of types

```agda
module foundation.codiagonal-maps-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.coproduct-typesᵉ
```

</details>

## Idea

Theᵉ codiagonalᵉ mapᵉ `∇ᵉ : Aᵉ +ᵉ Aᵉ → A`ᵉ ofᵉ `A`ᵉ isᵉ theᵉ mapᵉ thatᵉ projectsᵉ `Aᵉ +ᵉ A`ᵉ ontoᵉ
`A`.ᵉ

## Definitions

```agda
module _
  { l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ)
  where

  codiagonalᵉ : Aᵉ +ᵉ Aᵉ → Aᵉ
  codiagonalᵉ (inlᵉ aᵉ) = aᵉ
  codiagonalᵉ (inrᵉ aᵉ) = aᵉ
```