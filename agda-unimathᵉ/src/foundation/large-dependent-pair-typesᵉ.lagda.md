# Large dependent pair types

```agda
module foundation.large-dependent-pair-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Whenᵉ `B`ᵉ isᵉ aᵉ familyᵉ ofᵉ largeᵉ typesᵉ overᵉ `A`,ᵉ thenᵉ weᵉ canᵉ formᵉ theᵉ largeᵉ typeᵉ ofᵉ
pairsᵉ `pairωᵉ aᵉ b`ᵉ consistingᵉ ofᵉ anᵉ elementᵉ `aᵉ : A`ᵉ andᵉ anᵉ elementᵉ `bᵉ : Bᵉ a`.ᵉ
Suchᵉ pairsᵉ areᵉ calledᵉ dependentᵉ pairs,ᵉ sinceᵉ theᵉ typeᵉ ofᵉ theᵉ secondᵉ componentᵉ
dependsᵉ onᵉ theᵉ firstᵉ component.ᵉ

## Definition

```agda
record Σωᵉ (Aᵉ : UUωᵉ) (Bᵉ : Aᵉ → UUωᵉ) : UUωᵉ where
  constructor pairωᵉ
  field
    prω1ᵉ : Aᵉ
    prω2ᵉ : Bᵉ prω1ᵉ

open Σωᵉ public

infixr 3 _,ωᵉ_
pattern _,ωᵉ_ aᵉ bᵉ = pairωᵉ aᵉ bᵉ
```

### Families on dependent pair types

```agda
module _
  {lᵉ : Level} {Aᵉ : UUωᵉ} {Bᵉ : Aᵉ → UUωᵉ}
  where

  fam-Σωᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ lᵉ) → Σωᵉ Aᵉ Bᵉ → UUᵉ lᵉ
  fam-Σωᵉ Cᵉ (pairωᵉ xᵉ yᵉ) = Cᵉ xᵉ yᵉ
```