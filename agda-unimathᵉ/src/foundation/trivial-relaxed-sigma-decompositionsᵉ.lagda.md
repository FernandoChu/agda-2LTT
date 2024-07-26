# Trivial relaxed Σ-decompositions

```agda
module foundation.trivial-relaxed-sigma-decompositionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.relaxed-sigma-decompositionsᵉ
open import foundation.transposition-identifications-along-equivalencesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
```

</details>

## Idea

Aᵉ relaxedᵉ Σ-decompositionᵉ isᵉ saidᵉ to beᵉ **trivial**ᵉ ifᵉ itsᵉ indexingᵉ typeᵉ isᵉ
contractible.ᵉ

## Definitions

### The predicate of being a trivial relaxed Σ-decomposition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Dᵉ : Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  is-trivial-relaxed-Σ-decomposition-Propᵉ : Propᵉ l2ᵉ
  is-trivial-relaxed-Σ-decomposition-Propᵉ =
    is-contr-Propᵉ (indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ)

  is-trivial-Relaxed-Σ-Decompositionᵉ : UUᵉ l2ᵉ
  is-trivial-Relaxed-Σ-Decompositionᵉ =
    type-Propᵉ is-trivial-relaxed-Σ-decomposition-Propᵉ
```

### The trivial relaxed Σ-decomposition

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ)
  where

  trivial-Relaxed-Σ-Decompositionᵉ : Relaxed-Σ-Decompositionᵉ l2ᵉ l1ᵉ Aᵉ
  pr1ᵉ (trivial-Relaxed-Σ-Decompositionᵉ) = raise-unitᵉ l2ᵉ
  pr1ᵉ (pr2ᵉ (trivial-Relaxed-Σ-Decompositionᵉ)) xᵉ = Aᵉ
  pr2ᵉ (pr2ᵉ (trivial-Relaxed-Σ-Decompositionᵉ)) =
    inv-left-unit-law-Σ-is-contrᵉ
      ( is-contr-raise-unitᵉ)
      ( raise-starᵉ)

is-trivial-trivial-Relaxed-Σ-Decompositionᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  is-trivial-Relaxed-Σ-Decompositionᵉ (trivial-Relaxed-Σ-Decompositionᵉ l2ᵉ Aᵉ)
is-trivial-trivial-Relaxed-Σ-Decompositionᵉ = is-contr-raise-unitᵉ
```

## Propositions

### Any trivial relaxed Σ-decomposition is equivalent to the standard trivial relaxed Σ-decomposition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Dᵉ : Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  ( is-trivialᵉ : is-trivial-Relaxed-Σ-Decompositionᵉ Dᵉ)
  where

  equiv-trivial-is-trivial-Relaxed-Σ-Decompositionᵉ :
    equiv-Relaxed-Σ-Decompositionᵉ Dᵉ (trivial-Relaxed-Σ-Decompositionᵉ l4ᵉ Aᵉ)
  pr1ᵉ equiv-trivial-is-trivial-Relaxed-Σ-Decompositionᵉ =
    ( map-equivᵉ (compute-raise-unitᵉ l4ᵉ) ∘ᵉ
      terminal-mapᵉ (indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ) ,ᵉ
      is-equiv-compᵉ
        ( map-equivᵉ (compute-raise-unitᵉ l4ᵉ))
        ( terminal-mapᵉ (indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ))
        ( is-equiv-terminal-map-is-contrᵉ is-trivialᵉ)
        ( is-equiv-map-equivᵉ ( compute-raise-unitᵉ l4ᵉ)))
  pr1ᵉ (pr2ᵉ equiv-trivial-is-trivial-Relaxed-Σ-Decompositionᵉ) xᵉ =
    ( inv-equivᵉ (matching-correspondence-Relaxed-Σ-Decompositionᵉ Dᵉ)) ∘eᵉ
    ( inv-left-unit-law-Σ-is-contrᵉ is-trivialᵉ xᵉ)
  pr2ᵉ (pr2ᵉ equiv-trivial-is-trivial-Relaxed-Σ-Decompositionᵉ) aᵉ =
    eq-pair-eq-fiberᵉ
      ( map-inv-eq-transpose-equivᵉ
        ( inv-equivᵉ (matching-correspondence-Relaxed-Σ-Decompositionᵉ Dᵉ))
        ( reflᵉ))
```

### The type of all trivial relaxed Σ-decompositions is contractible

```agda
is-contr-type-trivial-Relaxed-Σ-Decompositionᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  is-contrᵉ
    ( type-subtypeᵉ (is-trivial-relaxed-Σ-decomposition-Propᵉ {l1ᵉ} {l2ᵉ} {l1ᵉ} {Aᵉ}))
pr1ᵉ ( is-contr-type-trivial-Relaxed-Σ-Decompositionᵉ {l1ᵉ} {l2ᵉ} {Aᵉ}) =
  ( trivial-Relaxed-Σ-Decompositionᵉ l2ᵉ Aᵉ ,ᵉ
    is-trivial-trivial-Relaxed-Σ-Decompositionᵉ {l1ᵉ} {l2ᵉ} {Aᵉ})
pr2ᵉ ( is-contr-type-trivial-Relaxed-Σ-Decompositionᵉ {l1ᵉ} {l2ᵉ} {Aᵉ}) Dᵉ =
    eq-type-subtypeᵉ
      ( is-trivial-relaxed-Σ-decomposition-Propᵉ)
      ( invᵉ
        ( eq-equiv-Relaxed-Σ-Decompositionᵉ
          ( pr1ᵉ Dᵉ)
          ( trivial-Relaxed-Σ-Decompositionᵉ l2ᵉ Aᵉ)
          ( equiv-trivial-is-trivial-Relaxed-Σ-Decompositionᵉ (pr1ᵉ Dᵉ) (pr2ᵉ Dᵉ))))
```