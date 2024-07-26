# Wide global function classes

```agda
module orthogonal-factorization-systems.wide-global-function-classesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.function-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.function-classesᵉ
open import orthogonal-factorization-systems.global-function-classesᵉ
```

</details>

## Idea

Weᵉ sayᵉ aᵉ
[globalᵉ functionᵉ class](orthogonal-factorization-systems.function-classes.mdᵉ) isᵉ
**wide**ᵉ ifᵉ itᵉ containsᵉ allᵉ [equivalences](foundation-core.equivalences.mdᵉ) andᵉ
isᵉ compositionᵉ closed.ᵉ Thisᵉ meansᵉ itᵉ isᵉ morallyᵉ aᵉ wideᵉ sub-∞-categoryᵉ ofᵉ theᵉ
∞-categoryᵉ ofᵉ types.ᵉ

## Definition

```agda
record wide-global-function-classᵉ (βᵉ : Level → Level → Level) : UUωᵉ where
  field

    global-function-class-wide-global-function-classᵉ :
      global-function-classᵉ βᵉ

    has-equivalences-wide-global-function-classᵉ :
      has-equivalences-global-function-classᵉ
        global-function-class-wide-global-function-classᵉ

    is-closed-under-composition-wide-global-function-classᵉ :
      is-closed-under-composition-global-function-classᵉ
        global-function-class-wide-global-function-classᵉ

open wide-global-function-classᵉ public

function-class-wide-global-function-classᵉ :
  {βᵉ : Level → Level → Level} (Pᵉ : wide-global-function-classᵉ βᵉ) →
  {l1ᵉ l2ᵉ : Level} → function-classᵉ l1ᵉ l2ᵉ (βᵉ l1ᵉ l2ᵉ)
function-class-wide-global-function-classᵉ Pᵉ =
  function-class-global-function-classᵉ
    ( global-function-class-wide-global-function-classᵉ Pᵉ)

type-wide-global-function-classᵉ :
  {βᵉ : Level → Level → Level} (Pᵉ : wide-global-function-classᵉ βᵉ)
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (βᵉ l1ᵉ l2ᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
type-wide-global-function-classᵉ Pᵉ =
  type-function-classᵉ (function-class-wide-global-function-classᵉ Pᵉ)

module _
  {βᵉ : Level → Level → Level} (Pᵉ : wide-global-function-classᵉ βᵉ)
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-in-wide-global-function-classᵉ : (Aᵉ → Bᵉ) → UUᵉ (βᵉ l1ᵉ l2ᵉ)
  is-in-wide-global-function-classᵉ =
    is-in-function-classᵉ (function-class-wide-global-function-classᵉ Pᵉ)

  is-prop-is-in-wide-global-function-classᵉ :
    (fᵉ : Aᵉ → Bᵉ) → is-propᵉ (is-in-wide-global-function-classᵉ fᵉ)
  is-prop-is-in-wide-global-function-classᵉ =
    is-prop-is-in-function-classᵉ (function-class-wide-global-function-classᵉ Pᵉ)

  inclusion-wide-global-function-classᵉ :
    type-wide-global-function-classᵉ Pᵉ Aᵉ Bᵉ → Aᵉ → Bᵉ
  inclusion-wide-global-function-classᵉ =
    inclusion-function-classᵉ (function-class-wide-global-function-classᵉ Pᵉ)

  is-emb-inclusion-wide-global-function-classᵉ :
    is-embᵉ inclusion-wide-global-function-classᵉ
  is-emb-inclusion-wide-global-function-classᵉ =
    is-emb-inclusion-function-classᵉ
      ( function-class-wide-global-function-classᵉ Pᵉ)

  emb-wide-global-function-classᵉ :
    type-wide-global-function-classᵉ Pᵉ Aᵉ Bᵉ ↪ᵉ (Aᵉ → Bᵉ)
  emb-wide-global-function-classᵉ =
    emb-function-classᵉ (function-class-wide-global-function-classᵉ Pᵉ)
```