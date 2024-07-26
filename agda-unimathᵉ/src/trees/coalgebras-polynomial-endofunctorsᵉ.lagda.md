# Coalgebras of polynomial endofunctors

```agda
module trees.coalgebras-polynomial-endofunctorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import trees.polynomial-endofunctorsᵉ
```

</details>

## Idea

**Coalgebras**ᵉ forᵉ polynomialᵉ endofunctorsᵉ areᵉ typesᵉ `X`ᵉ equippedᵉ with aᵉ
functionᵉ

```text
  Xᵉ → Σᵉ (aᵉ : A),ᵉ Bᵉ aᵉ → Xᵉ
```

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (lᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  coalgebra-polynomial-endofunctorᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
  coalgebra-polynomial-endofunctorᵉ =
    Σᵉ (UUᵉ lᵉ) (λ Xᵉ → Xᵉ → type-polynomial-endofunctorᵉ Aᵉ Bᵉ Xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ)
  where

  type-coalgebra-polynomial-endofunctorᵉ : UUᵉ l3ᵉ
  type-coalgebra-polynomial-endofunctorᵉ = pr1ᵉ Xᵉ

  structure-coalgebra-polynomial-endofunctorᵉ :
    type-coalgebra-polynomial-endofunctorᵉ →
    type-polynomial-endofunctorᵉ Aᵉ Bᵉ type-coalgebra-polynomial-endofunctorᵉ
  structure-coalgebra-polynomial-endofunctorᵉ = pr2ᵉ Xᵉ

  shape-coalgebra-polynomial-endofunctorᵉ :
    type-coalgebra-polynomial-endofunctorᵉ → Aᵉ
  shape-coalgebra-polynomial-endofunctorᵉ xᵉ =
    pr1ᵉ (structure-coalgebra-polynomial-endofunctorᵉ xᵉ)

  component-coalgebra-polynomial-endofunctorᵉ :
    (xᵉ : type-coalgebra-polynomial-endofunctorᵉ) →
    Bᵉ (shape-coalgebra-polynomial-endofunctorᵉ xᵉ) →
    type-coalgebra-polynomial-endofunctorᵉ
  component-coalgebra-polynomial-endofunctorᵉ xᵉ =
    pr2ᵉ (structure-coalgebra-polynomial-endofunctorᵉ xᵉ)
```