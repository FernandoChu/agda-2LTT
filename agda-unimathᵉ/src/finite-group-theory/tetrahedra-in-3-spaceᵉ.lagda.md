# Tetrahedra in `3`-dimensional space

```agda
module finite-group-theory.tetrahedra-in-3-spaceᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.2-element-decidable-subtypesᵉ
open import univalent-combinatorics.cyclic-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ tetrahedraᵉ in 3-dimensionalᵉ spaceᵉ isᵉ aᵉ typeᵉ ofᵉ tetrahedraᵉ thatᵉ canᵉ
beᵉ rotated,ᵉ butᵉ notᵉ reflected.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ symmetryᵉ groupᵉ ofᵉ theᵉ
tetrahedraᵉ in 3-dimensionalᵉ spaceᵉ isᵉ theᵉ alternatingᵉ groupᵉ `A₄`.ᵉ

Noteᵉ thatᵉ anyᵉ rotationᵉ ofᵉ aᵉ tetrahedronᵉ in 3-spaceᵉ inducesᵉ aᵉ rotationᵉ onᵉ theᵉ setᵉ
ofᵉ opposingᵉ pairsᵉ ofᵉ edges.ᵉ Thereᵉ areᵉ threeᵉ suchᵉ pairsᵉ ofᵉ edges.ᵉ

## Definition

```agda
tetrahedron-in-3-spaceᵉ : UUᵉ (lsuc lzero)
tetrahedron-in-3-spaceᵉ =
  Σᵉ ( UU-Finᵉ lzero 4ᵉ)
    ( λ Xᵉ →
      cyclic-structureᵉ 3
        ( Σᵉ ( 2-Element-Decidable-Subtypeᵉ lzero
              ( 2-Element-Decidable-Subtypeᵉ lzero
                ( type-UU-Finᵉ 4 Xᵉ)))
            ( λ Qᵉ →
              (xᵉ : type-UU-Finᵉ 4 Xᵉ) →
              is-emptyᵉ
                ( (Pᵉ : type-2-Element-Decidable-Subtypeᵉ Qᵉ) →
                  is-in-2-Element-Decidable-Subtypeᵉ
                    (pr1ᵉ Pᵉ)
                    ( xᵉ)))))

module _
  (Tᵉ : tetrahedron-in-3-spaceᵉ)
  where

  vertex-tetrahedron-in-3-spaceᵉ : UUᵉ lzero
  vertex-tetrahedron-in-3-spaceᵉ = type-UU-Finᵉ 4 (pr1ᵉ Tᵉ)

  cyclic-structure-tetrahedron-in-3-spaceᵉ :
    cyclic-structureᵉ 3
      ( Σᵉ ( 2-Element-Decidable-Subtypeᵉ lzero
            ( 2-Element-Decidable-Subtypeᵉ lzero
              ( vertex-tetrahedron-in-3-spaceᵉ)))
          ( λ Qᵉ →
            (xᵉ : vertex-tetrahedron-in-3-spaceᵉ) →
            is-emptyᵉ
              ( (Pᵉ : type-2-Element-Decidable-Subtypeᵉ Qᵉ) →
                is-in-2-Element-Decidable-Subtypeᵉ
                  (pr1ᵉ Pᵉ)
                  ( xᵉ))))
  cyclic-structure-tetrahedron-in-3-spaceᵉ = pr2ᵉ Tᵉ
```