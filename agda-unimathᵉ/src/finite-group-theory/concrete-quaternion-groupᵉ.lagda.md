# The concrete quaternion group

```agda
module finite-group-theory.concrete-quaternion-groupᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.isolated-elementsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.complements-isolated-elementsᵉ
open import univalent-combinatorics.cubesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.equivalences-cubesᵉ
```

</details>

## Definition

```agda
equiv-face-cubeᵉ :
  (kᵉ : ℕᵉ) (Xᵉ Yᵉ : cubeᵉ (succ-ℕᵉ kᵉ)) (eᵉ : equiv-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ Yᵉ)
  (dᵉ : dim-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ) (aᵉ : axis-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ dᵉ) →
  equiv-cubeᵉ kᵉ
    ( face-cubeᵉ kᵉ Xᵉ dᵉ aᵉ)
    ( face-cubeᵉ kᵉ Yᵉ
      ( map-dim-equiv-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ Yᵉ eᵉ dᵉ)
      ( map-axis-equiv-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ Yᵉ eᵉ dᵉ aᵉ))
equiv-face-cubeᵉ kᵉ Xᵉ Yᵉ eᵉ dᵉ aᵉ =
  pairᵉ
    ( equiv-complement-element-UU-Finᵉ kᵉ
      ( pairᵉ (dim-cube-UU-Finᵉ (succ-ℕᵉ kᵉ) Xᵉ) dᵉ)
      ( pairᵉ
        ( dim-cube-UU-Finᵉ (succ-ℕᵉ kᵉ) Yᵉ)
        ( map-dim-equiv-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ Yᵉ eᵉ dᵉ))
      ( dim-equiv-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ Yᵉ eᵉ)
      ( reflᵉ))
    ( λ d'ᵉ →
      ( equiv-trᵉ
        ( axis-cubeᵉ (succ-ℕᵉ kᵉ) Yᵉ)
        ( invᵉ
          ( natural-inclusion-equiv-complement-isolated-elementᵉ
            ( dim-equiv-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ Yᵉ eᵉ)
            ( pairᵉ dᵉ
              ( λ zᵉ →
                has-decidable-equality-has-cardinalityᵉ
                  ( succ-ℕᵉ kᵉ)
                  ( has-cardinality-dim-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ)
                  ( dᵉ)
                  ( zᵉ)))
            ( pairᵉ
              ( map-dim-equiv-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ Yᵉ eᵉ dᵉ)
              ( λ zᵉ →
                has-decidable-equality-has-cardinalityᵉ
                  ( succ-ℕᵉ kᵉ)
                  ( has-cardinality-dim-cubeᵉ (succ-ℕᵉ kᵉ) Yᵉ)
                  ( map-dim-equiv-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ Yᵉ eᵉ dᵉ)
                  ( zᵉ)))
            ( reflᵉ)
            ( d'ᵉ)))) ∘eᵉ
      ( axis-equiv-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ Yᵉ eᵉ
        ( inclusion-complement-element-UU-Finᵉ kᵉ
          ( pairᵉ (dim-cube-UU-Finᵉ (succ-ℕᵉ kᵉ) Xᵉ) dᵉ) d'ᵉ)))

cube-with-labeled-facesᵉ :
  (kᵉ : ℕᵉ) → UUᵉ (lsuc lzero)
cube-with-labeled-facesᵉ kᵉ =
  Σᵉ ( cubeᵉ (succ-ℕᵉ kᵉ))
    ( λ Xᵉ →
      (dᵉ : dim-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ) (aᵉ : axis-cubeᵉ (succ-ℕᵉ kᵉ) Xᵉ dᵉ) →
      labelling-cubeᵉ kᵉ (face-cubeᵉ kᵉ Xᵉ dᵉ aᵉ))

cube-cube-with-labeled-facesᵉ :
  (kᵉ : ℕᵉ) → cube-with-labeled-facesᵉ kᵉ → cubeᵉ (succ-ℕᵉ kᵉ)
cube-cube-with-labeled-facesᵉ kᵉ Xᵉ = pr1ᵉ Xᵉ

labelling-faces-cube-with-labeled-facesᵉ :
  (kᵉ : ℕᵉ) (Xᵉ : cube-with-labeled-facesᵉ kᵉ)
  (dᵉ : dim-cubeᵉ (succ-ℕᵉ kᵉ) (cube-cube-with-labeled-facesᵉ kᵉ Xᵉ))
  (aᵉ : axis-cubeᵉ (succ-ℕᵉ kᵉ) (cube-cube-with-labeled-facesᵉ kᵉ Xᵉ) dᵉ) →
  labelling-cubeᵉ kᵉ (face-cubeᵉ kᵉ (cube-cube-with-labeled-facesᵉ kᵉ Xᵉ) dᵉ aᵉ)
labelling-faces-cube-with-labeled-facesᵉ kᵉ Xᵉ = pr2ᵉ Xᵉ

equiv-cube-with-labeled-facesᵉ :
  {kᵉ : ℕᵉ} (Xᵉ Yᵉ : cube-with-labeled-facesᵉ kᵉ) → UUᵉ lzero
equiv-cube-with-labeled-facesᵉ {kᵉ} Xᵉ Yᵉ =
  Σᵉ ( equiv-cubeᵉ (succ-ℕᵉ kᵉ)
      ( cube-cube-with-labeled-facesᵉ kᵉ Xᵉ)
      ( cube-cube-with-labeled-facesᵉ kᵉ Yᵉ))
    ( λ eᵉ → ( dᵉ : dim-cubeᵉ (succ-ℕᵉ kᵉ) (cube-cube-with-labeled-facesᵉ kᵉ Xᵉ))
            ( aᵉ : axis-cubeᵉ (succ-ℕᵉ kᵉ) (cube-cube-with-labeled-facesᵉ kᵉ Xᵉ) dᵉ) →
            htpy-equiv-cubeᵉ kᵉ
              ( standard-cubeᵉ kᵉ)
              ( face-cubeᵉ kᵉ
                ( cube-cube-with-labeled-facesᵉ kᵉ Yᵉ)
                ( map-dim-equiv-cubeᵉ (succ-ℕᵉ kᵉ)
                  ( cube-cube-with-labeled-facesᵉ kᵉ Xᵉ)
                  ( cube-cube-with-labeled-facesᵉ kᵉ Yᵉ)
                  ( eᵉ)
                  ( dᵉ))
                ( map-axis-equiv-cubeᵉ (succ-ℕᵉ kᵉ)
                  ( cube-cube-with-labeled-facesᵉ kᵉ Xᵉ)
                  ( cube-cube-with-labeled-facesᵉ kᵉ Yᵉ)
                  eᵉ dᵉ aᵉ))
              ( comp-equiv-cubeᵉ kᵉ
                ( standard-cubeᵉ kᵉ)
                ( face-cubeᵉ kᵉ (pr1ᵉ Xᵉ) dᵉ aᵉ)
                ( face-cubeᵉ kᵉ (pr1ᵉ Yᵉ)
                  ( map-dim-equiv-cubeᵉ (succ-ℕᵉ kᵉ) (pr1ᵉ Xᵉ) (pr1ᵉ Yᵉ) eᵉ dᵉ)
                  ( map-axis-equiv-cubeᵉ (succ-ℕᵉ kᵉ) (pr1ᵉ Xᵉ) (pr1ᵉ Yᵉ) eᵉ dᵉ aᵉ))
                ( equiv-face-cubeᵉ kᵉ (pr1ᵉ Xᵉ) (pr1ᵉ Yᵉ) eᵉ dᵉ aᵉ)
                ( labelling-faces-cube-with-labeled-facesᵉ kᵉ Xᵉ dᵉ aᵉ))
              ( labelling-faces-cube-with-labeled-facesᵉ kᵉ Yᵉ
                ( map-dim-equiv-cubeᵉ (succ-ℕᵉ kᵉ)
                  ( cube-cube-with-labeled-facesᵉ kᵉ Xᵉ)
                  ( cube-cube-with-labeled-facesᵉ kᵉ Yᵉ)
                  eᵉ dᵉ)
                ( map-axis-equiv-cubeᵉ (succ-ℕᵉ kᵉ)
                  ( cube-cube-with-labeled-facesᵉ kᵉ Xᵉ)
                  ( cube-cube-with-labeled-facesᵉ kᵉ Yᵉ)
                  eᵉ dᵉ aᵉ)))
```