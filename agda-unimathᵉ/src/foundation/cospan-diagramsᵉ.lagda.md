# Cospan diagrams

```agda
module foundation.cospan-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cospansᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "cospanᵉ diagram"ᵉ Agda=cospan-diagramᵉ}} consistsᵉ ofᵉ twoᵉ typesᵉ `A`ᵉ
andᵉ `B`ᵉ andᵉ aᵉ [cospan](foundation.cospans.mdᵉ) `Aᵉ -f->ᵉ Xᵉ <-g-ᵉ B`ᵉ betweenᵉ them.ᵉ

## Definitions

```agda
cospan-diagramᵉ :
  (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
cospan-diagramᵉ l1ᵉ l2ᵉ l3ᵉ =
  Σᵉ (UUᵉ l1ᵉ) (λ Aᵉ → Σᵉ (UUᵉ l2ᵉ) (cospanᵉ l3ᵉ Aᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (cᵉ : cospan-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  left-type-cospan-diagramᵉ : UUᵉ l1ᵉ
  left-type-cospan-diagramᵉ = pr1ᵉ cᵉ

  right-type-cospan-diagramᵉ : UUᵉ l2ᵉ
  right-type-cospan-diagramᵉ = pr1ᵉ (pr2ᵉ cᵉ)

  cospan-cospan-diagramᵉ :
    cospanᵉ l3ᵉ left-type-cospan-diagramᵉ right-type-cospan-diagramᵉ
  cospan-cospan-diagramᵉ = pr2ᵉ (pr2ᵉ cᵉ)
```