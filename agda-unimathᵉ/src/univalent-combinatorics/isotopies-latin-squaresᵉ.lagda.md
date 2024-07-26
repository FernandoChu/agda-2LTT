# Isotopies of Latin squares

```agda
module univalent-combinatorics.isotopies-latin-squaresᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.latin-squaresᵉ
```

</details>

## Idea

Anᵉ isotopyᵉ ofᵉ latinᵉ squaresᵉ fromᵉ `L`ᵉ to `K`ᵉ consistsᵉ ofᵉ equivalencesᵉ ofᵉ theᵉ
rows,ᵉ columns,ᵉ andᵉ symbolsᵉ preservingᵉ theᵉ multiplicationᵉ tables.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Lᵉ : Latin-Squareᵉ l1ᵉ l2ᵉ l3ᵉ) (Kᵉ : Latin-Squareᵉ l4ᵉ l5ᵉ l6ᵉ)
  where

  isotopy-Latin-Squareᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  isotopy-Latin-Squareᵉ =
    Σᵉ ( row-Latin-Squareᵉ Lᵉ ≃ᵉ row-Latin-Squareᵉ Kᵉ)
      ( λ e-rowᵉ →
        Σᵉ ( column-Latin-Squareᵉ Lᵉ ≃ᵉ column-Latin-Squareᵉ Kᵉ)
          ( λ e-columnᵉ →
            Σᵉ ( symbol-Latin-Squareᵉ Lᵉ ≃ᵉ symbol-Latin-Squareᵉ Kᵉ)
              ( λ e-symbolᵉ →
                ( xᵉ : row-Latin-Squareᵉ Lᵉ) (yᵉ : column-Latin-Squareᵉ Lᵉ) →
                Idᵉ
                  ( map-equivᵉ e-symbolᵉ (mul-Latin-Squareᵉ Lᵉ xᵉ yᵉ))
                  ( mul-Latin-Squareᵉ Kᵉ
                    ( map-equivᵉ e-rowᵉ xᵉ)
                    ( map-equivᵉ e-columnᵉ yᵉ)))))
```