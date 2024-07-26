# The elementhood relation on coalgebras of polynomial endofunctors

```agda
module trees.elementhood-relation-coalgebras-polynomial-endofunctorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
open import graph-theory.walks-directed-graphsᵉ

open import trees.coalgebras-polynomial-endofunctorsᵉ
```

</details>

## Idea

Givenᵉ twoᵉ elementsᵉ `xᵉ yᵉ : X`ᵉ in theᵉ underlyingᵉ typeᵉ ofᵉ aᵉ coalgebraᵉ ofᵉ aᵉ
polynomialᵉ endofunctor,ᵉ Weᵉ sayᵉ thatᵉ **`x`ᵉ isᵉ anᵉ elementᵉ ofᵉ `y`**,ᵉ i.e.,ᵉ `xᵉ ∈ᵉ y`,ᵉ
ifᵉ thereᵉ isᵉ anᵉ elementᵉ `bᵉ : Bᵉ (shapeᵉ y)`ᵉ equippedᵉ with anᵉ identificationᵉ
`componentᵉ yᵉ bᵉ ＝ᵉ x`.ᵉ Noteᵉ thatᵉ thisᵉ elementhoodᵉ relationᵉ ofᵉ anᵉ arbitraryᵉ
coalgebraᵉ needᵉ notᵉ beᵉ irreflexive.ᵉ

Byᵉ theᵉ elementhoodᵉ relationᵉ onᵉ coalgebrasᵉ weᵉ obtainᵉ forᵉ eachᵉ coalgebraᵉ aᵉ
directedᵉ graph.ᵉ

## Definition

```agda
infixl 6 is-element-of-coalgebra-polynomial-endofunctorᵉ

is-element-of-coalgebra-polynomial-endofunctorᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ)
  (xᵉ yᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
is-element-of-coalgebra-polynomial-endofunctorᵉ Xᵉ xᵉ yᵉ =
  fiberᵉ (component-coalgebra-polynomial-endofunctorᵉ Xᵉ yᵉ) xᵉ

syntax
  is-element-of-coalgebra-polynomial-endofunctorᵉ Xᵉ xᵉ yᵉ = xᵉ ∈ᵉ yᵉ in-coalgebraᵉ Xᵉ
```

### The graph of a coalgebra for a polynomial endofunctor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ)
  where

  graph-coalgebra-polynomial-endofunctorᵉ :
    Directed-Graphᵉ l3ᵉ (l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ graph-coalgebra-polynomial-endofunctorᵉ =
    type-coalgebra-polynomial-endofunctorᵉ Xᵉ
  pr2ᵉ graph-coalgebra-polynomial-endofunctorᵉ xᵉ yᵉ =
    xᵉ ∈ᵉ yᵉ in-coalgebraᵉ Xᵉ

  walk-coalgebra-polynomial-endofunctorᵉ :
    (xᵉ yᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  walk-coalgebra-polynomial-endofunctorᵉ =
    walk-Directed-Graphᵉ graph-coalgebra-polynomial-endofunctorᵉ

  concat-walk-coalgebra-polynomial-endofunctorᵉ :
    {xᵉ yᵉ zᵉ : type-coalgebra-polynomial-endofunctorᵉ Xᵉ} →
    walk-coalgebra-polynomial-endofunctorᵉ xᵉ yᵉ →
    walk-coalgebra-polynomial-endofunctorᵉ yᵉ zᵉ →
    walk-coalgebra-polynomial-endofunctorᵉ xᵉ zᵉ
  concat-walk-coalgebra-polynomial-endofunctorᵉ =
    concat-walk-Directed-Graphᵉ graph-coalgebra-polynomial-endofunctorᵉ
```