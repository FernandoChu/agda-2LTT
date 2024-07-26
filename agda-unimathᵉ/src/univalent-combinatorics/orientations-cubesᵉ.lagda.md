# Orientations of cubes

```agda
module univalent-combinatorics.orientations-cubesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.iterating-functionsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.cubesᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.function-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Definition

```agda
orientation-cubeᵉ : {kᵉ : ℕᵉ} → cubeᵉ kᵉ → UUᵉ (lzeroᵉ)
orientation-cubeᵉ {kᵉ} Xᵉ =
  Σᵉ ( vertex-cubeᵉ kᵉ Xᵉ → Finᵉ 2ᵉ)
    ( λ hᵉ →
      ( xᵉ yᵉ : vertex-cubeᵉ kᵉ Xᵉ) →
        Idᵉ
          ( iterateᵉ
            ( number-of-elements-is-finiteᵉ
              ( is-finite-Σᵉ
                ( is-finite-dim-cubeᵉ kᵉ Xᵉ)
                ( λ dᵉ →
                  is-finite-function-typeᵉ
                    ( is-finite-eqᵉ
                      ( has-decidable-equality-is-finiteᵉ
                        ( is-finite-axis-cubeᵉ kᵉ Xᵉ dᵉ))
                    { xᵉ dᵉ}
                    { yᵉ dᵉ})
                    ( is-finite-emptyᵉ))))
            ( succ-Finᵉ 2ᵉ)
            ( hᵉ xᵉ))
          ( hᵉ yᵉ))
```