# Induction principles on W-types

```agda
module trees.induction-w-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import trees.elementhood-relation-w-typesᵉ
open import trees.inequality-w-typesᵉ
open import trees.w-typesᵉ
```

</details>

## Idea

Thereᵉ areᵉ severalᵉ inductionᵉ principlesᵉ onᵉ W-types,ᵉ besidedᵉ theᵉ inductionᵉ
principleᵉ thatᵉ eachᵉ W-typeᵉ comesᵉ equippedᵉ with byᵉ definition.ᵉ Theᵉ firstᵉ isᵉ anᵉ
inductionᵉ principleᵉ formulatedᵉ with respectᵉ to theᵉ elementhoodᵉ relationᵉ onᵉ
W-types.ᵉ Theᵉ secondᵉ isᵉ aᵉ strongᵉ inductionᵉ principle,ᵉ analogousᵉ to theᵉ strongᵉ
inductionᵉ principleᵉ forᵉ theᵉ naturalᵉ numbers.ᵉ

## Properties

### Induction principle with respect to the elementhood relation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  □-∈-𝕎ᵉ : (𝕎ᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ) → (𝕎ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ))
  □-∈-𝕎ᵉ Pᵉ xᵉ = (yᵉ : 𝕎ᵉ Aᵉ Bᵉ) → (yᵉ ∈-𝕎ᵉ xᵉ) → Pᵉ yᵉ

  η-□-∈-𝕎ᵉ :
    (Pᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ) → ((xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → Pᵉ xᵉ) → ((xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-∈-𝕎ᵉ Pᵉ xᵉ)
  η-□-∈-𝕎ᵉ Pᵉ fᵉ xᵉ yᵉ eᵉ = fᵉ yᵉ

  ε-□-∈-𝕎ᵉ :
    (Pᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ) (hᵉ : (yᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-∈-𝕎ᵉ Pᵉ yᵉ → Pᵉ yᵉ) →
    ((xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-∈-𝕎ᵉ Pᵉ xᵉ) → (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → Pᵉ xᵉ
  ε-□-∈-𝕎ᵉ Pᵉ hᵉ fᵉ xᵉ = hᵉ xᵉ (fᵉ xᵉ)

  ind-□-∈-𝕎ᵉ :
    (Pᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ) (hᵉ : (yᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-∈-𝕎ᵉ Pᵉ yᵉ → Pᵉ yᵉ) →
    (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-∈-𝕎ᵉ Pᵉ xᵉ
  ind-□-∈-𝕎ᵉ Pᵉ hᵉ (tree-𝕎ᵉ xᵉ αᵉ) .(αᵉ bᵉ) (pairᵉ bᵉ reflᵉ) =
    hᵉ (αᵉ bᵉ) (ind-□-∈-𝕎ᵉ Pᵉ hᵉ (αᵉ bᵉ))

  compute-□-∈-𝕎ᵉ :
    (Pᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ) (hᵉ : (yᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-∈-𝕎ᵉ Pᵉ yᵉ → Pᵉ yᵉ) →
    (xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ) (eᵉ : yᵉ ∈-𝕎ᵉ xᵉ) →
    ind-□-∈-𝕎ᵉ Pᵉ hᵉ xᵉ yᵉ eᵉ ＝ᵉ hᵉ yᵉ (ind-□-∈-𝕎ᵉ Pᵉ hᵉ yᵉ)
  compute-□-∈-𝕎ᵉ Pᵉ hᵉ (tree-𝕎ᵉ xᵉ αᵉ) .(αᵉ bᵉ) (pairᵉ bᵉ reflᵉ) = reflᵉ

  ind-∈-𝕎ᵉ :
    (Pᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ) (hᵉ : (yᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-∈-𝕎ᵉ Pᵉ yᵉ → Pᵉ yᵉ) →
    (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → Pᵉ xᵉ
  ind-∈-𝕎ᵉ Pᵉ hᵉ = ε-□-∈-𝕎ᵉ Pᵉ hᵉ (ind-□-∈-𝕎ᵉ Pᵉ hᵉ)

  compute-∈-𝕎ᵉ :
    (Pᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ) (hᵉ : (yᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-∈-𝕎ᵉ Pᵉ yᵉ → Pᵉ yᵉ) →
    (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → ind-∈-𝕎ᵉ Pᵉ hᵉ xᵉ ＝ᵉ hᵉ xᵉ (λ yᵉ eᵉ → ind-∈-𝕎ᵉ Pᵉ hᵉ yᵉ)
  compute-∈-𝕎ᵉ Pᵉ hᵉ xᵉ =
    apᵉ (hᵉ xᵉ) (eq-htpyᵉ (eq-htpyᵉ ∘ᵉ compute-□-∈-𝕎ᵉ Pᵉ hᵉ xᵉ))
```

### Strong induction for W-types

#### We define an operation `□-𝕎` that acts on families over `𝕎 A B`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Pᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ)
  where

  □-𝕎ᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  □-𝕎ᵉ xᵉ = (yᵉ : 𝕎ᵉ Aᵉ Bᵉ) → (yᵉ <-𝕎ᵉ xᵉ) → Pᵉ yᵉ
```

#### The unit of □-𝕎 takes sections of P to sections of □-𝕎 P

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Pᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ}
  where

  unit-□-𝕎ᵉ : ((xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → Pᵉ xᵉ) → ((xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-𝕎ᵉ Pᵉ xᵉ)
  unit-□-𝕎ᵉ fᵉ xᵉ yᵉ pᵉ = fᵉ yᵉ
```

#### The reflector (counit) of □-𝕎 is dual, with an extra hypothesis

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Pᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ}
  where

  reflect-□-𝕎ᵉ :
    ((xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-𝕎ᵉ Pᵉ xᵉ → Pᵉ xᵉ) →
    ((xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-𝕎ᵉ Pᵉ xᵉ) → ((xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → Pᵉ xᵉ)
  reflect-□-𝕎ᵉ hᵉ fᵉ xᵉ = hᵉ xᵉ (fᵉ xᵉ)
```

#### The strong induction principle for W-types

Weᵉ firstᵉ proveᵉ anᵉ intermediateᵉ inductionᵉ principleᵉ with computationᵉ rule,ᵉ where
weᵉ obtainᵉ sectionsᵉ ofᵉ □-𝕎ᵉ P.ᵉ

```agda
  □-strong-ind-𝕎ᵉ :
    ((xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-𝕎ᵉ Pᵉ xᵉ → Pᵉ xᵉ) → (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-𝕎ᵉ Pᵉ xᵉ
  □-strong-ind-𝕎ᵉ hᵉ (tree-𝕎ᵉ xᵉ αᵉ) .(αᵉ bᵉ) (le-∈-𝕎ᵉ (pairᵉ bᵉ reflᵉ)) =
    hᵉ (αᵉ bᵉ) (□-strong-ind-𝕎ᵉ hᵉ (αᵉ bᵉ))
  □-strong-ind-𝕎ᵉ hᵉ (tree-𝕎ᵉ xᵉ αᵉ) yᵉ (propagate-le-𝕎ᵉ (pairᵉ bᵉ reflᵉ) Kᵉ) =
    □-strong-ind-𝕎ᵉ hᵉ (αᵉ bᵉ) yᵉ Kᵉ

  □-strong-compute-𝕎ᵉ :
    (hᵉ : (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-𝕎ᵉ Pᵉ xᵉ → Pᵉ xᵉ)
    (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) (yᵉ : 𝕎ᵉ Aᵉ Bᵉ) (pᵉ : yᵉ <-𝕎ᵉ xᵉ) →
    □-strong-ind-𝕎ᵉ hᵉ xᵉ yᵉ pᵉ ＝ᵉ hᵉ yᵉ (□-strong-ind-𝕎ᵉ hᵉ yᵉ)
  □-strong-compute-𝕎ᵉ hᵉ (tree-𝕎ᵉ xᵉ αᵉ) .(αᵉ bᵉ) (le-∈-𝕎ᵉ (pairᵉ bᵉ reflᵉ)) =
    reflᵉ
  □-strong-compute-𝕎ᵉ hᵉ (tree-𝕎ᵉ xᵉ αᵉ) yᵉ (propagate-le-𝕎ᵉ (pairᵉ bᵉ reflᵉ) Kᵉ) =
    □-strong-compute-𝕎ᵉ hᵉ (αᵉ bᵉ) yᵉ Kᵉ
```

Nowᵉ weᵉ proveᵉ theᵉ actualᵉ inductionᵉ principleᵉ with computationᵉ rule,ᵉ where weᵉ
obtainᵉ sectionsᵉ ofᵉ P.ᵉ

```agda
strong-ind-𝕎ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Pᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ) →
  ((xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-𝕎ᵉ Pᵉ xᵉ → Pᵉ xᵉ) → (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → Pᵉ xᵉ
strong-ind-𝕎ᵉ Pᵉ hᵉ = reflect-□-𝕎ᵉ hᵉ (□-strong-ind-𝕎ᵉ hᵉ)

strong-compute-𝕎ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Pᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ) →
  (hᵉ : (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → □-𝕎ᵉ Pᵉ xᵉ → Pᵉ xᵉ) (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) →
  strong-ind-𝕎ᵉ Pᵉ hᵉ xᵉ ＝ᵉ hᵉ xᵉ (unit-□-𝕎ᵉ (strong-ind-𝕎ᵉ Pᵉ hᵉ) xᵉ)
strong-compute-𝕎ᵉ Pᵉ hᵉ xᵉ =
  apᵉ (hᵉ xᵉ) (eq-htpyᵉ (λ yᵉ → eq-htpyᵉ (λ pᵉ → □-strong-compute-𝕎ᵉ hᵉ xᵉ yᵉ pᵉ)))
```

### There are no infinitely descending sequences in a W-types

```agda
no-infinite-descent-𝕎ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  (fᵉ : ℕᵉ → 𝕎ᵉ Aᵉ Bᵉ) → ¬ᵉ ((nᵉ : ℕᵉ) → (fᵉ (succ-ℕᵉ nᵉ) <-𝕎ᵉ (fᵉ nᵉ)))
no-infinite-descent-𝕎ᵉ {Aᵉ = Aᵉ} {Bᵉ} fᵉ =
  strong-ind-𝕎ᵉ
    ( λ xᵉ → (fᵉ : ℕᵉ → 𝕎ᵉ Aᵉ Bᵉ) (pᵉ : fᵉ zero-ℕᵉ ＝ᵉ xᵉ) →
            ¬ᵉ ((nᵉ : ℕᵉ) → (fᵉ (succ-ℕᵉ nᵉ)) <-𝕎ᵉ (fᵉ nᵉ)))
    ( λ xᵉ IHᵉ fᵉ pᵉ Hᵉ →
      IHᵉ
        ( fᵉ 1ᵉ)
        ( trᵉ (λ tᵉ → (fᵉ 1ᵉ) <-𝕎ᵉ tᵉ) pᵉ (Hᵉ zero-ℕᵉ))
        ( fᵉ ∘ᵉ succ-ℕᵉ)
        ( reflᵉ)
        ( λ nᵉ → Hᵉ (succ-ℕᵉ nᵉ)))
    ( fᵉ zero-ℕᵉ)
    ( fᵉ)
    ( reflᵉ)
```