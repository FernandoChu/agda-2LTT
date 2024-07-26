# Π-decompositions of types into types in a subuniverse

```agda
module foundation.pi-decompositions-subuniverseᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.pi-decompositionsᵉ
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Considerᵉ aᵉ subuniverseᵉ `P`ᵉ andᵉ aᵉ typeᵉ `A`ᵉ in `P`.ᵉ Aᵉ **Π-decomposition**ᵉ ofᵉ `A`ᵉ
intoᵉ typesᵉ in `P`ᵉ consistsᵉ ofᵉ aᵉ typeᵉ `X`ᵉ in `P`ᵉ andᵉ aᵉ familyᵉ `Y`ᵉ ofᵉ typesᵉ in `P`ᵉ
indexedᵉ overᵉ `X`,ᵉ equippedᵉ with anᵉ equivalenceᵉ

```text
  Aᵉ ≃ᵉ Πᵉ Xᵉ Y.ᵉ
```

## Definition

### The predicate of being a Π-decomposition in a subuniverse

```agda
is-in-subuniverse-Π-Decompositionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) {Aᵉ : UUᵉ l3ᵉ} →
  Π-Decompositionᵉ l1ᵉ l1ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-in-subuniverse-Π-Decompositionᵉ Pᵉ Dᵉ =
  ( is-in-subuniverseᵉ Pᵉ (indexing-type-Π-Decompositionᵉ Dᵉ)) ×ᵉ
  ( ( xᵉ : indexing-type-Π-Decompositionᵉ Dᵉ) →
    ( is-in-subuniverseᵉ Pᵉ (cotype-Π-Decompositionᵉ Dᵉ xᵉ)))
```

### Π-decompositions in a subuniverse

```agda
Π-Decomposition-Subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) →
  type-subuniverseᵉ Pᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
Π-Decomposition-Subuniverseᵉ Pᵉ Aᵉ =
  Σᵉ ( type-subuniverseᵉ Pᵉ)
    ( λ Xᵉ →
      Σᵉ ( fam-subuniverseᵉ Pᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ))
        ( λ Yᵉ →
          inclusion-subuniverseᵉ Pᵉ Aᵉ ≃ᵉ
          Πᵉ ( inclusion-subuniverseᵉ Pᵉ Xᵉ)
            ( λ xᵉ → inclusion-subuniverseᵉ Pᵉ (Yᵉ xᵉ))))

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Aᵉ : type-subuniverseᵉ Pᵉ)
  (Dᵉ : Π-Decomposition-Subuniverseᵉ Pᵉ Aᵉ)
  where

  subuniverse-indexing-type-Π-Decomposition-Subuniverseᵉ : type-subuniverseᵉ Pᵉ
  subuniverse-indexing-type-Π-Decomposition-Subuniverseᵉ = pr1ᵉ Dᵉ

  indexing-type-Π-Decomposition-Subuniverseᵉ : UUᵉ l1ᵉ
  indexing-type-Π-Decomposition-Subuniverseᵉ =
    inclusion-subuniverseᵉ Pᵉ
      subuniverse-indexing-type-Π-Decomposition-Subuniverseᵉ

  is-in-subuniverse-indexing-type-Π-Decomposition-Subuniverseᵉ :
    type-Propᵉ (Pᵉ indexing-type-Π-Decomposition-Subuniverseᵉ)
  is-in-subuniverse-indexing-type-Π-Decomposition-Subuniverseᵉ =
    pr2ᵉ subuniverse-indexing-type-Π-Decomposition-Subuniverseᵉ

  subuniverse-cotype-Π-Decomposition-Subuniverseᵉ :
    fam-subuniverseᵉ Pᵉ indexing-type-Π-Decomposition-Subuniverseᵉ
  subuniverse-cotype-Π-Decomposition-Subuniverseᵉ = pr1ᵉ (pr2ᵉ Dᵉ)

  cotype-Π-Decomposition-Subuniverseᵉ :
    (indexing-type-Π-Decomposition-Subuniverseᵉ → UUᵉ l1ᵉ)
  cotype-Π-Decomposition-Subuniverseᵉ Xᵉ =
    inclusion-subuniverseᵉ Pᵉ (subuniverse-cotype-Π-Decomposition-Subuniverseᵉ Xᵉ)

  is-in-subuniverse-cotype-Π-Decomposition-Subuniverseᵉ :
    ((xᵉ : indexing-type-Π-Decomposition-Subuniverseᵉ) →
    type-Propᵉ (Pᵉ (cotype-Π-Decomposition-Subuniverseᵉ xᵉ)))
  is-in-subuniverse-cotype-Π-Decomposition-Subuniverseᵉ xᵉ =
    pr2ᵉ (subuniverse-cotype-Π-Decomposition-Subuniverseᵉ xᵉ)

  matching-correspondence-Π-Decomposition-Subuniverseᵉ :
    inclusion-subuniverseᵉ Pᵉ Aᵉ ≃ᵉ
    Πᵉ ( indexing-type-Π-Decomposition-Subuniverseᵉ)
      ( cotype-Π-Decomposition-Subuniverseᵉ)
  matching-correspondence-Π-Decomposition-Subuniverseᵉ = pr2ᵉ (pr2ᵉ Dᵉ)
```

## Properties

### The type of Π-decompositions in a subuniverse is equivalent to the total space of `is-in-subuniverse-Π-Decomposition`

```agda
map-equiv-total-is-in-subuniverse-Π-Decompositionᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Aᵉ : type-subuniverseᵉ Pᵉ) →
  Π-Decomposition-Subuniverseᵉ Pᵉ Aᵉ →
  Σᵉ ( Π-Decompositionᵉ l1ᵉ l1ᵉ (inclusion-subuniverseᵉ Pᵉ Aᵉ))
    ( is-in-subuniverse-Π-Decompositionᵉ Pᵉ)
map-equiv-total-is-in-subuniverse-Π-Decompositionᵉ Pᵉ Aᵉ Dᵉ =
  ( indexing-type-Π-Decomposition-Subuniverseᵉ Pᵉ Aᵉ Dᵉ ,ᵉ
    ( cotype-Π-Decomposition-Subuniverseᵉ Pᵉ Aᵉ Dᵉ ,ᵉ
      matching-correspondence-Π-Decomposition-Subuniverseᵉ Pᵉ Aᵉ Dᵉ)) ,ᵉ
  ( is-in-subuniverse-indexing-type-Π-Decomposition-Subuniverseᵉ Pᵉ Aᵉ Dᵉ ,ᵉ
    is-in-subuniverse-cotype-Π-Decomposition-Subuniverseᵉ Pᵉ Aᵉ Dᵉ)

map-inv-equiv-Π-Decomposition-Π-Decomposition-Subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Aᵉ : type-subuniverseᵉ Pᵉ) →
  Σᵉ ( Π-Decompositionᵉ l1ᵉ l1ᵉ (inclusion-subuniverseᵉ Pᵉ Aᵉ))
    ( is-in-subuniverse-Π-Decompositionᵉ Pᵉ) →
  Π-Decomposition-Subuniverseᵉ Pᵉ Aᵉ
map-inv-equiv-Π-Decomposition-Π-Decomposition-Subuniverseᵉ Pᵉ Aᵉ Xᵉ =
  ( ( indexing-type-Π-Decompositionᵉ (pr1ᵉ Xᵉ) ,ᵉ (pr1ᵉ (pr2ᵉ Xᵉ))) ,ᵉ
    ( (λ xᵉ → cotype-Π-Decompositionᵉ (pr1ᵉ Xᵉ) xᵉ ,ᵉ pr2ᵉ (pr2ᵉ Xᵉ) xᵉ) ,ᵉ
      matching-correspondence-Π-Decompositionᵉ (pr1ᵉ Xᵉ)))

equiv-total-is-in-subuniverse-Π-Decompositionᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Aᵉ : type-subuniverseᵉ Pᵉ) →
  ( Π-Decomposition-Subuniverseᵉ Pᵉ Aᵉ) ≃ᵉ
  ( Σᵉ ( Π-Decompositionᵉ l1ᵉ l1ᵉ (inclusion-subuniverseᵉ Pᵉ Aᵉ))
      ( is-in-subuniverse-Π-Decompositionᵉ Pᵉ))
pr1ᵉ (equiv-total-is-in-subuniverse-Π-Decompositionᵉ Pᵉ Aᵉ) =
  map-equiv-total-is-in-subuniverse-Π-Decompositionᵉ Pᵉ Aᵉ
pr2ᵉ (equiv-total-is-in-subuniverse-Π-Decompositionᵉ Pᵉ Aᵉ) =
  is-equiv-is-invertibleᵉ
    ( map-inv-equiv-Π-Decomposition-Π-Decomposition-Subuniverseᵉ Pᵉ Aᵉ)
    ( refl-htpyᵉ)
    ( refl-htpyᵉ)
```