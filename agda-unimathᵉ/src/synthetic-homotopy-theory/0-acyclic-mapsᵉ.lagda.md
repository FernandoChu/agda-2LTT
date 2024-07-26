# `0`-acyclic maps

```agda
module synthetic-homotopy-theory.0-acyclic-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.epimorphisms-with-respect-to-setsᵉ
open import foundation.propositionsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.truncated-acyclic-mapsᵉ
```

</details>

## Idea

Aᵉ **`0`-acyclicᵉ map**ᵉ isᵉ aᵉ mapᵉ whoseᵉ [fibers](foundation-core.fibers-of-maps.mdᵉ)
areᵉ [`0`-acyclicᵉ types](synthetic-homotopy-theory.0-acyclic-types.md),ᵉ meaningᵉ
thatᵉ theirᵉ [suspension](synthetic-homotopy-theory.suspensions-of-types.mdᵉ) isᵉ
[`0`-connected](foundation.0-connected-types.md).ᵉ

Weᵉ canᵉ characterizeᵉ theᵉ `0`-acyclicᵉ mapsᵉ asᵉ theᵉ
[surjectiveᵉ maps](foundation.surjective-maps.md).ᵉ

## Definition

### The predicate of being a `0`-acyclic map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-0-acyclic-map-Propᵉ : (Aᵉ → Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-0-acyclic-map-Propᵉ = is-truncated-acyclic-map-Propᵉ (zero-𝕋ᵉ)

  is-0-acyclic-mapᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-0-acyclic-mapᵉ fᵉ = type-Propᵉ (is-0-acyclic-map-Propᵉ fᵉ)

  is-prop-is-0-acyclic-mapᵉ :
    (fᵉ : Aᵉ → Bᵉ) → is-propᵉ (is-0-acyclic-mapᵉ fᵉ)
  is-prop-is-0-acyclic-mapᵉ fᵉ =
    is-prop-type-Propᵉ (is-0-acyclic-map-Propᵉ fᵉ)
```

## Properties

### A map is `0`-acyclic if and only if it is surjective

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-surjective-is-0-acyclic-mapᵉ :
    is-0-acyclic-mapᵉ fᵉ → is-surjectiveᵉ fᵉ
  is-surjective-is-0-acyclic-mapᵉ acᵉ =
    is-surjective-is-epimorphism-Setᵉ
      ( is-epimorphism-is-truncated-acyclic-map-Truncated-Typeᵉ fᵉ acᵉ)

  is-0-acyclic-map-is-surjectiveᵉ :
    is-surjectiveᵉ fᵉ → is-0-acyclic-mapᵉ fᵉ
  is-0-acyclic-map-is-surjectiveᵉ sᵉ =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Typeᵉ fᵉ
      ( is-epimorphism-is-surjective-Setᵉ sᵉ)
```

## See also

-ᵉ [Acyclicᵉ maps](synthetic-homotopy-theory.acyclic-maps.mdᵉ)
-ᵉ [`k`-acyclicᵉ maps](synthetic-homotopy-theory.truncated-acyclic-maps.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to truncatedᵉ types](foundation.epimorphisms-with-respect-to-truncated-types.mdᵉ)