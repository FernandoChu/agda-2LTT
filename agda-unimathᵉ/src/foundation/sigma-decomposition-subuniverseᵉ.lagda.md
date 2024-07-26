# Σ-decompositions of types into types in a subuniverse

```agda
module foundation.sigma-decomposition-subuniverseᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.relaxed-sigma-decompositionsᵉ
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Considerᵉ aᵉ subuniverseᵉ `P`ᵉ andᵉ aᵉ typeᵉ `A`ᵉ in `P`.ᵉ Aᵉ **Σ-decomposition**ᵉ ofᵉ `A`ᵉ
intoᵉ typesᵉ in `P`ᵉ consistsᵉ ofᵉ aᵉ typeᵉ `X`ᵉ in `P`ᵉ andᵉ aᵉ familyᵉ `Y`ᵉ ofᵉ typesᵉ in `P`ᵉ
indexedᵉ overᵉ `X`,ᵉ equippedᵉ with anᵉ equivalenceᵉ

```text
  Aᵉ ≃ᵉ Σᵉ Xᵉ Y.ᵉ
```

## Definition

### The predicate of being a Σ-decomposition in a subuniverse

```agda
is-in-subuniverse-Σ-Decompositionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) {Aᵉ : UUᵉ l3ᵉ} →
  Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-in-subuniverse-Σ-Decompositionᵉ Pᵉ Dᵉ =
  ( is-in-subuniverseᵉ Pᵉ (indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ)) ×ᵉ
  ( ( xᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ) →
    ( is-in-subuniverseᵉ Pᵉ (cotype-Relaxed-Σ-Decompositionᵉ Dᵉ xᵉ)))
```

### Σ-decompositions in a subuniverse

```agda
Σ-Decomposition-Subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) →
  type-subuniverseᵉ Pᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
Σ-Decomposition-Subuniverseᵉ Pᵉ Aᵉ =
  Σᵉ ( type-subuniverseᵉ Pᵉ)
    ( λ Xᵉ →
      Σᵉ ( fam-subuniverseᵉ Pᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ))
        ( λ Yᵉ →
          inclusion-subuniverseᵉ Pᵉ Aᵉ ≃ᵉ
          Σᵉ ( inclusion-subuniverseᵉ Pᵉ Xᵉ)
            ( λ xᵉ → inclusion-subuniverseᵉ Pᵉ (Yᵉ xᵉ))))

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Aᵉ : type-subuniverseᵉ Pᵉ)
  (Dᵉ : Σ-Decomposition-Subuniverseᵉ Pᵉ Aᵉ)
  where

  subuniverse-indexing-type-Σ-Decomposition-Subuniverseᵉ : type-subuniverseᵉ Pᵉ
  subuniverse-indexing-type-Σ-Decomposition-Subuniverseᵉ = pr1ᵉ Dᵉ

  indexing-type-Σ-Decomposition-Subuniverseᵉ : UUᵉ l1ᵉ
  indexing-type-Σ-Decomposition-Subuniverseᵉ =
    inclusion-subuniverseᵉ Pᵉ
      subuniverse-indexing-type-Σ-Decomposition-Subuniverseᵉ

  is-in-subuniverse-indexing-type-Σ-Decomposition-Subuniverseᵉ :
    type-Propᵉ (Pᵉ indexing-type-Σ-Decomposition-Subuniverseᵉ)
  is-in-subuniverse-indexing-type-Σ-Decomposition-Subuniverseᵉ =
    pr2ᵉ subuniverse-indexing-type-Σ-Decomposition-Subuniverseᵉ

  subuniverse-cotype-Σ-Decomposition-Subuniverseᵉ :
    fam-subuniverseᵉ Pᵉ indexing-type-Σ-Decomposition-Subuniverseᵉ
  subuniverse-cotype-Σ-Decomposition-Subuniverseᵉ = pr1ᵉ (pr2ᵉ Dᵉ)

  cotype-Σ-Decomposition-Subuniverseᵉ :
    (indexing-type-Σ-Decomposition-Subuniverseᵉ → UUᵉ l1ᵉ)
  cotype-Σ-Decomposition-Subuniverseᵉ Xᵉ =
    inclusion-subuniverseᵉ Pᵉ (subuniverse-cotype-Σ-Decomposition-Subuniverseᵉ Xᵉ)

  is-in-subuniverse-cotype-Σ-Decomposition-Subuniverseᵉ :
    ((xᵉ : indexing-type-Σ-Decomposition-Subuniverseᵉ) →
    type-Propᵉ (Pᵉ (cotype-Σ-Decomposition-Subuniverseᵉ xᵉ)))
  is-in-subuniverse-cotype-Σ-Decomposition-Subuniverseᵉ xᵉ =
    pr2ᵉ (subuniverse-cotype-Σ-Decomposition-Subuniverseᵉ xᵉ)

  matching-correspondence-Σ-Decomposition-Subuniverseᵉ :
    inclusion-subuniverseᵉ Pᵉ Aᵉ ≃ᵉ
    Σᵉ ( indexing-type-Σ-Decomposition-Subuniverseᵉ)
      ( λ xᵉ → cotype-Σ-Decomposition-Subuniverseᵉ xᵉ)
  matching-correspondence-Σ-Decomposition-Subuniverseᵉ = pr2ᵉ (pr2ᵉ Dᵉ)
```

## Properties

### The type of Σ-decompositions in a subuniverse is equivalent to the total space of `is-in-subuniverse-Σ-Decomposition`

```agda
map-equiv-total-is-in-subuniverse-Σ-Decompositionᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Aᵉ : type-subuniverseᵉ Pᵉ) →
  Σ-Decomposition-Subuniverseᵉ Pᵉ Aᵉ →
  Σᵉ ( Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ (inclusion-subuniverseᵉ Pᵉ Aᵉ))
    ( is-in-subuniverse-Σ-Decompositionᵉ Pᵉ)
map-equiv-total-is-in-subuniverse-Σ-Decompositionᵉ Pᵉ Aᵉ Dᵉ =
  ( indexing-type-Σ-Decomposition-Subuniverseᵉ Pᵉ Aᵉ Dᵉ ,ᵉ
    ( cotype-Σ-Decomposition-Subuniverseᵉ Pᵉ Aᵉ Dᵉ ,ᵉ
      matching-correspondence-Σ-Decomposition-Subuniverseᵉ Pᵉ Aᵉ Dᵉ)) ,ᵉ
  ( is-in-subuniverse-indexing-type-Σ-Decomposition-Subuniverseᵉ Pᵉ Aᵉ Dᵉ ,ᵉ
    is-in-subuniverse-cotype-Σ-Decomposition-Subuniverseᵉ Pᵉ Aᵉ Dᵉ)

map-inv-equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-Subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Aᵉ : type-subuniverseᵉ Pᵉ) →
  Σᵉ ( Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ (inclusion-subuniverseᵉ Pᵉ Aᵉ))
    ( is-in-subuniverse-Σ-Decompositionᵉ Pᵉ) →
  Σ-Decomposition-Subuniverseᵉ Pᵉ Aᵉ
map-inv-equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-Subuniverseᵉ Pᵉ Aᵉ Xᵉ =
  ( ( indexing-type-Relaxed-Σ-Decompositionᵉ (pr1ᵉ Xᵉ) ,ᵉ (pr1ᵉ (pr2ᵉ Xᵉ))) ,ᵉ
    ( (λ xᵉ → cotype-Relaxed-Σ-Decompositionᵉ (pr1ᵉ Xᵉ) xᵉ ,ᵉ pr2ᵉ (pr2ᵉ Xᵉ) xᵉ) ,ᵉ
      matching-correspondence-Relaxed-Σ-Decompositionᵉ (pr1ᵉ Xᵉ)))

equiv-total-is-in-subuniverse-Σ-Decompositionᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Aᵉ : type-subuniverseᵉ Pᵉ) →
  ( Σ-Decomposition-Subuniverseᵉ Pᵉ Aᵉ) ≃ᵉ
  ( Σᵉ ( Relaxed-Σ-Decompositionᵉ l1ᵉ l1ᵉ (inclusion-subuniverseᵉ Pᵉ Aᵉ))
      ( is-in-subuniverse-Σ-Decompositionᵉ Pᵉ))
pr1ᵉ (equiv-total-is-in-subuniverse-Σ-Decompositionᵉ Pᵉ Aᵉ) =
  map-equiv-total-is-in-subuniverse-Σ-Decompositionᵉ Pᵉ Aᵉ
pr2ᵉ (equiv-total-is-in-subuniverse-Σ-Decompositionᵉ Pᵉ Aᵉ) =
  is-equiv-is-invertibleᵉ
    ( map-inv-equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-Subuniverseᵉ Pᵉ Aᵉ)
    ( refl-htpyᵉ)
    ( refl-htpyᵉ)
```