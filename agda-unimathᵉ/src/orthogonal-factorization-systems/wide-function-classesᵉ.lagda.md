# Wide function classes

```agda
module orthogonal-factorization-systems.wide-function-classesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.function-classesᵉ
```

</details>

## Idea

Weᵉ sayᵉ aᵉ
[(smallᵉ) functionᵉ class](orthogonal-factorization-systems.function-classes.mdᵉ)
isᵉ **wide**ᵉ ifᵉ itᵉ containsᵉ allᵉ [equivalences](foundation-core.equivalences.mdᵉ)
andᵉ isᵉ compositionᵉ closed.ᵉ Thisᵉ meansᵉ itᵉ isᵉ morallyᵉ aᵉ wideᵉ sub-∞-categoryᵉ ofᵉ theᵉ
∞-categoryᵉ ofᵉ typesᵉ atᵉ aᵉ fixedᵉ universeᵉ level.ᵉ

## Definition

### The predicate on small function classes of being wide

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : function-classᵉ l1ᵉ l1ᵉ l2ᵉ)
  where

  is-wide-function-classᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  is-wide-function-classᵉ =
    ( has-equivalences-function-classᵉ Pᵉ) ×ᵉ
    ( is-closed-under-composition-function-classᵉ Pᵉ)

  is-wide-function-class-Propᵉ : Propᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  is-wide-function-class-Propᵉ =
    product-Propᵉ
      ( has-equivalences-function-class-Propᵉ Pᵉ)
      ( is-closed-under-composition-function-class-Propᵉ Pᵉ)

  is-prop-is-wide-function-classᵉ : is-propᵉ is-wide-function-classᵉ
  is-prop-is-wide-function-classᵉ = is-prop-type-Propᵉ is-wide-function-class-Propᵉ

  has-equivalences-is-wide-function-classᵉ :
    is-wide-function-classᵉ → has-equivalences-function-classᵉ Pᵉ
  has-equivalences-is-wide-function-classᵉ = pr1ᵉ

  is-closed-under-composition-is-wide-function-classᵉ :
    is-wide-function-classᵉ → is-closed-under-composition-function-classᵉ Pᵉ
  is-closed-under-composition-is-wide-function-classᵉ = pr2ᵉ
```

### The type of small wide function classes

```agda
wide-function-classᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
wide-function-classᵉ l1ᵉ l2ᵉ =
  Σᵉ (function-classᵉ l1ᵉ l1ᵉ l2ᵉ) (is-wide-function-classᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : wide-function-classᵉ l1ᵉ l2ᵉ)
  where

  function-class-wide-function-classᵉ : function-classᵉ l1ᵉ l1ᵉ l2ᵉ
  function-class-wide-function-classᵉ = pr1ᵉ Pᵉ

  is-wide-wide-function-classᵉ :
    is-wide-function-classᵉ function-class-wide-function-classᵉ
  is-wide-wide-function-classᵉ = pr2ᵉ Pᵉ

  has-equivalences-wide-function-classᵉ :
    has-equivalences-function-classᵉ function-class-wide-function-classᵉ
  has-equivalences-wide-function-classᵉ =
    has-equivalences-is-wide-function-classᵉ
      ( function-class-wide-function-classᵉ)
      ( is-wide-wide-function-classᵉ)

  is-closed-under-composition-wide-function-classᵉ :
    is-closed-under-composition-function-classᵉ
      ( function-class-wide-function-classᵉ)
  is-closed-under-composition-wide-function-classᵉ =
    is-closed-under-composition-is-wide-function-classᵉ
      ( function-class-wide-function-classᵉ)
      ( is-wide-wide-function-classᵉ)
```