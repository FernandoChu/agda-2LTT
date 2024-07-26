# Morphisms of descent data of the circle

```agda
module synthetic-homotopy-theory.morphisms-descent-data-circleᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.morphisms-types-equipped-with-automorphismsᵉ

open import synthetic-homotopy-theory.descent-circleᵉ
```

</details>

## Idea

Givenᵉ twoᵉ [descentᵉ data](synthetic-homotopy-theory.descent-circle.mdᵉ) `(A,e)`ᵉ
andᵉ `(B,f)`ᵉ overᵉ theᵉ
[circle](synthetic-homotopy-theory.circle.md)`,ᵉ aᵉ **morphism**ᵉ `h`ofᵉ descentᵉ data between`(A,ᵉ
e)`and`(B,ᵉ f)`isᵉ aᵉ map`h`from`A`to`B`ᵉ suchᵉ thatᵉ theᵉ squareᵉ

```text
      hᵉ
  Aᵉ ----->ᵉ Bᵉ
  |        |
 e|ᵉ        |fᵉ
  ∨ᵉ        ∨ᵉ
  Aᵉ ----->ᵉ Bᵉ
      hᵉ
```

[commutes](foundation.commuting-squares-of-maps.md).ᵉ

## Definitions

### Morphisms of descent data for the circle

```agda
hom-descent-data-circleᵉ :
  { l1ᵉ l2ᵉ : Level}
  ( Pᵉ : descent-data-circleᵉ l1ᵉ) (Qᵉ : descent-data-circleᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
hom-descent-data-circleᵉ = hom-Type-With-Automorphismᵉ

module _
  { l1ᵉ l2ᵉ : Level} (Pᵉ : descent-data-circleᵉ l1ᵉ) (Qᵉ : descent-data-circleᵉ l2ᵉ)
  ( hᵉ : hom-descent-data-circleᵉ Pᵉ Qᵉ)
  where

  map-hom-descent-data-circleᵉ :
    type-descent-data-circleᵉ Pᵉ → type-descent-data-circleᵉ Qᵉ
  map-hom-descent-data-circleᵉ =
    map-hom-Type-With-Automorphismᵉ Pᵉ Qᵉ hᵉ

  coherence-square-hom-descent-data-circleᵉ :
    coherence-square-mapsᵉ
      ( map-hom-descent-data-circleᵉ)
      ( map-descent-data-circleᵉ Pᵉ)
      ( map-descent-data-circleᵉ Qᵉ)
      ( map-hom-descent-data-circleᵉ)
  coherence-square-hom-descent-data-circleᵉ =
    coherence-square-hom-Type-With-Automorphismᵉ Pᵉ Qᵉ hᵉ
```