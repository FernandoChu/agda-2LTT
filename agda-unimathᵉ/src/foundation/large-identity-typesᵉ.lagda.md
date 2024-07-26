# Large identity types

```agda
module foundation.large-identity-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
```

</details>

## Definition

```agda
module _
  {Aᵉ : UUωᵉ}
  where

  data Idωᵉ (xᵉ : Aᵉ) : Aᵉ → UUωᵉ where
    reflωᵉ : Idωᵉ xᵉ xᵉ

  _＝ωᵉ_ : Aᵉ → Aᵉ → UUωᵉ
  (aᵉ ＝ωᵉ bᵉ) = Idωᵉ aᵉ bᵉ
```