# Algebras for polynomial endofunctors

```agda
module trees.algebras-polynomial-endofunctorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import trees.polynomial-endofunctorsᵉ
```

</details>

## Idea

Givenᵉ aᵉ polynomialᵉ endofunctorᵉ `Pᵉ Aᵉ B`,ᵉ anᵉ **algebra**ᵉ forᵉ `Pᵉ Aᵉ B`ᵉ conisistsᵉ ofᵉ
aᵉ typeᵉ `X`ᵉ andᵉ aᵉ mapᵉ `Pᵉ Aᵉ Bᵉ Xᵉ → X`.ᵉ

## Definitions

### Algebras for polynomial endofunctors

```agda
algebra-polynomial-endofunctorᵉ :
  (lᵉ : Level) {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
  UUᵉ (lsuc lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
algebra-polynomial-endofunctorᵉ lᵉ Aᵉ Bᵉ =
  Σᵉ (UUᵉ lᵉ) (λ Xᵉ → type-polynomial-endofunctorᵉ Aᵉ Bᵉ Xᵉ → Xᵉ)

type-algebra-polynomial-endofunctorᵉ :
  {lᵉ l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  algebra-polynomial-endofunctorᵉ lᵉ Aᵉ Bᵉ → UUᵉ lᵉ
type-algebra-polynomial-endofunctorᵉ Xᵉ = pr1ᵉ Xᵉ

structure-algebra-polynomial-endofunctorᵉ :
  {lᵉ l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : algebra-polynomial-endofunctorᵉ lᵉ Aᵉ Bᵉ) →
  type-polynomial-endofunctorᵉ Aᵉ Bᵉ (type-algebra-polynomial-endofunctorᵉ Xᵉ) →
  type-algebra-polynomial-endofunctorᵉ Xᵉ
structure-algebra-polynomial-endofunctorᵉ Xᵉ = pr2ᵉ Xᵉ
```