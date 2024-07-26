# Unlabeled structures of finite species

```agda
module species.unlabeled-structures-speciesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-typesᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ **unlabeledᵉ `F`-structures**ᵉ ofᵉ orderᵉ `n`ᵉ ofᵉ aᵉ
[species](species.species-of-types.mdᵉ) `F`ᵉ isᵉ theᵉ typeᵉ ofᵉ
[sets](foundation-core.sets.mdᵉ) `X`ᵉ ofᵉ sizeᵉ `n`ᵉ equippedᵉ with anᵉ `F`-structure.ᵉ
Twoᵉ unlabeledᵉ `F`-structuresᵉ ofᵉ orderᵉ `n`ᵉ areᵉ consideredᵉ to beᵉ theᵉ sameᵉ ifᵉ theᵉ
underlyingᵉ setsᵉ areᵉ isomorphicᵉ andᵉ theᵉ `F`-structureᵉ ofᵉ theᵉ firstᵉ transportsᵉ
alongᵉ thisᵉ isomorphismᵉ to theᵉ `F`-structureᵉ ofᵉ theᵉ second.ᵉ Itᵉ willᵉ automaticallyᵉ
followᵉ fromᵉ theᵉ [univalenceᵉ axiom](foundation.univalence.mdᵉ) thatᵉ theᵉ
[identityᵉ type](foundation-core.identity-types.mdᵉ) ofᵉ theᵉ typeᵉ ofᵉ unlabeledᵉ
`F`-structuresᵉ ofᵉ orderᵉ `n`ᵉ capturesᵉ thisᵉ idea.ᵉ

## Definitions

### Unlabeled structures of a species

```agda
unlabeled-structure-species-typesᵉ :
  {l1ᵉ l2ᵉ : Level} (Fᵉ : species-typesᵉ l1ᵉ l2ᵉ) → ℕᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
unlabeled-structure-species-typesᵉ {l1ᵉ} {l2ᵉ} Fᵉ nᵉ =
  Σᵉ (UU-Finᵉ l1ᵉ nᵉ) (λ Xᵉ → Fᵉ (type-UU-Finᵉ nᵉ Xᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Fᵉ : species-typesᵉ l1ᵉ l2ᵉ) {kᵉ : ℕᵉ}
  (Xᵉ : unlabeled-structure-species-typesᵉ Fᵉ kᵉ)
  where

  type-of-cardinality-unlabeled-structure-species-typesᵉ : UU-Finᵉ l1ᵉ kᵉ
  type-of-cardinality-unlabeled-structure-species-typesᵉ = pr1ᵉ Xᵉ

  type-unlabeled-structure-species-typesᵉ : UUᵉ l1ᵉ
  type-unlabeled-structure-species-typesᵉ =
    type-UU-Finᵉ kᵉ type-of-cardinality-unlabeled-structure-species-typesᵉ

  has-cardinality-type-unlabeled-structure-species-typesᵉ :
    has-cardinalityᵉ kᵉ type-unlabeled-structure-species-typesᵉ
  has-cardinality-type-unlabeled-structure-species-typesᵉ =
    has-cardinality-type-UU-Finᵉ
      kᵉ
      type-of-cardinality-unlabeled-structure-species-typesᵉ

  finite-type-unlabeled-structure-species-typesᵉ : 𝔽ᵉ l1ᵉ
  finite-type-unlabeled-structure-species-typesᵉ =
    finite-type-UU-Finᵉ kᵉ type-of-cardinality-unlabeled-structure-species-typesᵉ

  structure-unlabeled-structure-species-typesᵉ :
    Fᵉ type-unlabeled-structure-species-typesᵉ
  structure-unlabeled-structure-species-typesᵉ = pr2ᵉ Xᵉ
```

### Equivalences of unlabeled structures of a species

Thisᵉ remainsᵉ to beᵉ defined.ᵉ
[#741](https://github.com/UniMath/agda-unimath/issues/741ᵉ)