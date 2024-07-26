# `0`-acyclic types

```agda
module synthetic-homotopy-theory.0-acyclic-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.inhabited-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.truncation-levelsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.0-acyclic-mapsᵉ
open import synthetic-homotopy-theory.truncated-acyclic-mapsᵉ
open import synthetic-homotopy-theory.truncated-acyclic-typesᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ **`0`-acyclic**ᵉ ifᵉ itsᵉ
[suspension](synthetic-homotopy-theory.suspensions-of-types.mdᵉ) isᵉ
[`0`-connected](foundation.0-connected-types.md).ᵉ

Weᵉ canᵉ characterizeᵉ theᵉ `0`-acyclicᵉ typesᵉ asᵉ theᵉ
[inhabitedᵉ types](foundation.inhabited-types.md).ᵉ

## Definition

### The predicate of being a `0`-acyclic type

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  is-0-acyclic-Propᵉ : Propᵉ lᵉ
  is-0-acyclic-Propᵉ = is-truncated-acyclic-Propᵉ zero-𝕋ᵉ Aᵉ

  is-0-acyclicᵉ : UUᵉ lᵉ
  is-0-acyclicᵉ = type-Propᵉ is-0-acyclic-Propᵉ

  is-prop-is-0-acyclicᵉ : is-propᵉ is-0-acyclicᵉ
  is-prop-is-0-acyclicᵉ = is-prop-type-Propᵉ is-0-acyclic-Propᵉ
```

## Properties

### A type is `0`-acyclic if and only if it is inhabited

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-inhabited-is-0-acyclicᵉ : is-0-acyclicᵉ Aᵉ → is-inhabitedᵉ Aᵉ
  is-inhabited-is-0-acyclicᵉ acᵉ =
    map-trunc-Propᵉ
      ( pr1ᵉ)
      ( is-surjective-is-0-acyclic-mapᵉ
        ( terminal-mapᵉ Aᵉ)
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclicᵉ Aᵉ acᵉ)
        ( starᵉ))

  is-0-acyclic-is-inhabitedᵉ : is-inhabitedᵉ Aᵉ → is-0-acyclicᵉ Aᵉ
  is-0-acyclic-is-inhabitedᵉ hᵉ =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-mapᵉ Aᵉ
      ( is-0-acyclic-map-is-surjectiveᵉ
        ( terminal-mapᵉ Aᵉ)
        ( λ uᵉ →
          map-trunc-Propᵉ
            (λ aᵉ → (aᵉ ,ᵉ (contractionᵉ is-contr-unitᵉ uᵉ)))
            ( hᵉ)))
```

## See also

-ᵉ [`k`-acyclicᵉ types](synthetic-homotopy-theory.truncated-acyclic-types.mdᵉ)
-ᵉ [Acyclicᵉ types](synthetic-homotopy-theory.acyclic-types.mdᵉ)