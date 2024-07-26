# Cubes

```agda
module univalent-combinatorics.cubesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.complements-isolated-elementsᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Definitions

### Cubes

```agda
cubeᵉ : ℕᵉ → UUᵉ (lsuc lzero)
cubeᵉ kᵉ = Σᵉ (UU-Finᵉ lzero kᵉ) (λ Xᵉ → type-UU-Finᵉ kᵉ Xᵉ → UU-Finᵉ lzero 2ᵉ)

module _
  (kᵉ : ℕᵉ) (Xᵉ : cubeᵉ kᵉ)
  where

  dim-cube-UU-Finᵉ : UU-Finᵉ lzero kᵉ
  dim-cube-UU-Finᵉ = pr1ᵉ Xᵉ

  dim-cubeᵉ : UUᵉ lzero
  dim-cubeᵉ = type-UU-Finᵉ kᵉ dim-cube-UU-Finᵉ

  has-cardinality-dim-cubeᵉ : has-cardinalityᵉ kᵉ dim-cubeᵉ
  has-cardinality-dim-cubeᵉ = pr2ᵉ dim-cube-UU-Finᵉ

  has-finite-cardinality-dim-cubeᵉ : has-finite-cardinalityᵉ dim-cubeᵉ
  has-finite-cardinality-dim-cubeᵉ =
    pairᵉ kᵉ (pr2ᵉ dim-cube-UU-Finᵉ)

  is-finite-dim-cubeᵉ : is-finiteᵉ dim-cubeᵉ
  is-finite-dim-cubeᵉ =
    is-finite-has-finite-cardinalityᵉ has-finite-cardinality-dim-cubeᵉ

  axis-cube-UU-2ᵉ : dim-cubeᵉ → UU-Finᵉ lzero 2
  axis-cube-UU-2ᵉ = pr2ᵉ Xᵉ

  axis-cubeᵉ : dim-cubeᵉ → UUᵉ lzero
  axis-cubeᵉ dᵉ = type-UU-Finᵉ 2 (axis-cube-UU-2ᵉ dᵉ)

  has-cardinality-axis-cubeᵉ : (dᵉ : dim-cubeᵉ) → has-cardinalityᵉ 2 (axis-cubeᵉ dᵉ)
  has-cardinality-axis-cubeᵉ dᵉ = pr2ᵉ (axis-cube-UU-2ᵉ dᵉ)

  has-finite-cardinality-axis-cubeᵉ :
    (dᵉ : dim-cubeᵉ) → has-finite-cardinalityᵉ (axis-cubeᵉ dᵉ)
  has-finite-cardinality-axis-cubeᵉ dᵉ =
    pairᵉ 2 (has-cardinality-axis-cubeᵉ dᵉ)

  is-finite-axis-cubeᵉ : (dᵉ : dim-cubeᵉ) → is-finiteᵉ (axis-cubeᵉ dᵉ)
  is-finite-axis-cubeᵉ dᵉ =
    is-finite-has-cardinalityᵉ 2 (has-cardinality-axis-cubeᵉ dᵉ)

  vertex-cubeᵉ : UUᵉ lzero
  vertex-cubeᵉ = (dᵉ : dim-cubeᵉ) → axis-cubeᵉ dᵉ
```

### The standard cube

```agda
dim-standard-cube-UU-Finᵉ : (kᵉ : ℕᵉ) → UU-Finᵉ lzero kᵉ
dim-standard-cube-UU-Finᵉ kᵉ = Fin-UU-Fin'ᵉ kᵉ

dim-standard-cubeᵉ : ℕᵉ → UUᵉ lzero
dim-standard-cubeᵉ kᵉ = type-UU-Finᵉ kᵉ (dim-standard-cube-UU-Finᵉ kᵉ)

axis-standard-cube-UU-Finᵉ : (kᵉ : ℕᵉ) → dim-standard-cubeᵉ kᵉ → UU-Finᵉ lzero 2
axis-standard-cube-UU-Finᵉ kᵉ dᵉ = Fin-UU-Fin'ᵉ 2

axis-standard-cubeᵉ : (kᵉ : ℕᵉ) → dim-standard-cubeᵉ kᵉ → UUᵉ lzero
axis-standard-cubeᵉ kᵉ dᵉ = type-UU-Finᵉ 2 (axis-standard-cube-UU-Finᵉ kᵉ dᵉ)

standard-cubeᵉ : (kᵉ : ℕᵉ) → cubeᵉ kᵉ
standard-cubeᵉ kᵉ =
  pairᵉ (dim-standard-cube-UU-Finᵉ kᵉ) (axis-standard-cube-UU-Finᵉ kᵉ)

{-ᵉ
mere-equiv-standard-cubeᵉ :
  {kᵉ : ℕᵉ} (Xᵉ : cubeᵉ kᵉ) → type-trunc-Propᵉ (equiv-cubeᵉ (standard-cubeᵉ kᵉ) Xᵉ)
mere-equiv-standard-cubeᵉ {kᵉ} (pairᵉ (pairᵉ Xᵉ Hᵉ) Yᵉ) =
  apply-universal-property-trunc-Propᵉ Hᵉ
    ( trunc-Propᵉ (equiv-cubeᵉ (standard-cubeᵉ kᵉ) (pairᵉ (pairᵉ Xᵉ Hᵉ) Yᵉ)))
    ( λ eᵉ →
      {!ᵉ finite-choice-countᵉ (pairᵉ kᵉ eᵉ) ?!ᵉ})
-ᵉ}
```

### Faces of cubes

```agda
face-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ : cubeᵉ (succ-ℕᵉ kᵉ)) (dᵉ : dim-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ)
  (aᵉ : axis-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ dᵉ) → cubeᵉ kᵉ
pr1ᵉ (face-cubeᵉ kᵉ Xᵉ dᵉ aᵉ) =
  complement-element-UU-Finᵉ kᵉ (pairᵉ (dim-cube-UU-Finᵉ (succ-ℕᵉ kᵉ) Xᵉ) dᵉ)
pr2ᵉ (face-cubeᵉ kᵉ Xᵉ dᵉ aᵉ) d'ᵉ =
  axis-cube-UU-2ᵉ (succ-ℕᵉ kᵉ) Xᵉ
    ( inclusion-complement-element-UU-Finᵉ kᵉ
      ( pairᵉ (dim-cube-UU-Finᵉ (succ-ℕᵉ kᵉ) Xᵉ) dᵉ) d'ᵉ)
```