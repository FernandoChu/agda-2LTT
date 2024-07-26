# Deloopable H-spaces

```agda
module higher-group-theory.deloopable-h-spacesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-groupsᵉ

open import structured-types.equivalences-h-spacesᵉ
open import structured-types.h-spacesᵉ
```

</details>

## Idea

Considerᵉ anᵉ [H-space](structured-types.h-spaces.mdᵉ) with underlyingᵉ
[pointedᵉ type](structured-types.pointed-types.mdᵉ) `(Xᵉ ,ᵉ *)`ᵉ andᵉ with
multiplicationᵉ `μ`ᵉ satisfyingᵉ

```text
   left-unit-lawᵉ : (xᵉ : Xᵉ) → μᵉ *ᵉ xᵉ ＝ᵉ xᵉ
  right-unit-lawᵉ : (xᵉ : Xᵉ) → μᵉ xᵉ *ᵉ ＝ᵉ xᵉ
    coh-unit-lawᵉ : left-unit-lawᵉ *ᵉ ＝ᵉ right-unit-lawᵉ *.ᵉ
```

Aᵉ {{#conceptᵉ "delooping"ᵉ Disambiguation="H-space"ᵉ Agda=delooping-H-Spaceᵉ}} ofᵉ
theᵉ H-spaceᵉ `X`ᵉ consistsᵉ ofᵉ anᵉ [∞-group](higher-group-theory.higher-groups.mdᵉ)
`G`ᵉ andᵉ anᵉ [equivalenceᵉ ofᵉ H-spaces](structured-types.equivalences-h-spaces.mdᵉ)

```text
  Xᵉ ≃ᵉ h-space-∞-Groupᵉ G.ᵉ
```

## Definitions

### Deloopings of H-spaces of a given universe level

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : H-Spaceᵉ l1ᵉ)
  where

  delooping-H-Space-Levelᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  delooping-H-Space-Levelᵉ =
    Σᵉ (∞-Groupᵉ l2ᵉ) (λ Gᵉ → equiv-H-Spaceᵉ Aᵉ (h-space-∞-Groupᵉ Gᵉ))
```

### Deloopings of H-spaces

```agda
module _
  {l1ᵉ : Level} (Aᵉ : H-Spaceᵉ l1ᵉ)
  where

  delooping-H-Spaceᵉ : UUᵉ (lsuc l1ᵉ)
  delooping-H-Spaceᵉ = delooping-H-Space-Levelᵉ l1ᵉ Aᵉ
```

## See also

-ᵉ [Deloopableᵉ groups](higher-group-theory.deloopable-groups.mdᵉ)