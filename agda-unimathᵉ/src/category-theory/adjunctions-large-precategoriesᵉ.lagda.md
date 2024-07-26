# Adjunctions between large precategories

```agda
module category-theory.adjunctions-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.natural-transformations-functors-large-precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Letᵉ `C`ᵉ andᵉ `D`ᵉ beᵉ twoᵉ
[largeᵉ precategories](category-theory.large-precategories.md).ᵉ Twoᵉ
[functors](category-theory.functors-large-precategories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ andᵉ
`Gᵉ : Dᵉ → C`ᵉ constituteᵉ anᵉ **adjointᵉ pair**ᵉ ifᵉ

-ᵉ forᵉ eachᵉ pairᵉ ofᵉ objectsᵉ `X`ᵉ in `C`ᵉ andᵉ `Y`ᵉ in `D`,ᵉ thereᵉ isᵉ anᵉ
  [equivalence](foundation-core.equivalences.mdᵉ)
  `ϕᵉ Xᵉ Yᵉ : homᵉ (Fᵉ Xᵉ) Yᵉ ≃ᵉ homᵉ Xᵉ (Gᵉ Y)`ᵉ suchᵉ thatᵉ
-ᵉ forᵉ everyᵉ pairᵉ ofᵉ morhpismsᵉ `fᵉ : X₂ᵉ → X₁`ᵉ andᵉ `gᵉ : Y₁ᵉ → Y₂`ᵉ theᵉ followingᵉ
  squareᵉ commutesᵉ:

```text
                       ϕᵉ X₁ᵉ Y₁ᵉ
        homᵉ (Fᵉ X₁ᵉ) Y₁ᵉ -------->ᵉ homᵉ X₁ᵉ (Gᵉ Y₁ᵉ)
              |                       |
  gᵉ ∘ᵉ -ᵉ ∘ᵉ Fᵉ fᵉ |                       | Gᵉ gᵉ ∘ᵉ -ᵉ ∘ᵉ fᵉ
              |                       |
              ∨ᵉ                       ∨ᵉ
        homᵉ (Fᵉ X₂ᵉ) Y₂ᵉ -------->ᵉ homᵉ X₂ᵉ (Gᵉ Y₂ᵉ)
                       ϕᵉ X₂ᵉ Y₂ᵉ
```

Inᵉ thisᵉ caseᵉ weᵉ sayᵉ thatᵉ `F`ᵉ isᵉ **leftᵉ adjoint**ᵉ to `G`ᵉ andᵉ `G`ᵉ isᵉ **rightᵉ
adjoint**ᵉ to `F`,ᵉ andᵉ writeᵉ thisᵉ asᵉ `Fᵉ ⊣ᵉ G`.ᵉ

**Note:**ᵉ Theᵉ directionᵉ ofᵉ theᵉ equivalenceᵉ `ϕᵉ Xᵉ Y`ᵉ isᵉ chosenᵉ in suchᵉ aᵉ wayᵉ thatᵉ
itᵉ oftenᵉ coincidesᵉ with theᵉ directionᵉ ofᵉ theᵉ naturalᵉ map.ᵉ Forᵉ example,ᵉ in theᵉ
[abelianizationᵉ adjunction](group-theory.abelianization-groups.md),ᵉ theᵉ naturalᵉ
candidateᵉ forᵉ anᵉ equivalenceᵉ isᵉ givenᵉ byᵉ precompositionᵉ

```text
  -ᵉ ∘ᵉ ηᵉ : homᵉ (abelianization-Groupᵉ Gᵉ) Aᵉ → homᵉ Gᵉ (group-Abᵉ Aᵉ)
```

byᵉ theᵉ unitᵉ ofᵉ theᵉ adjunction.ᵉ

## Definition

### The predicate of being an adjoint pair of functors

```agda
module _
  {αCᵉ αDᵉ γFᵉ γGᵉ : Level → Level}
  {βCᵉ βDᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ)
  (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  (Fᵉ : functor-Large-Precategoryᵉ γFᵉ Cᵉ Dᵉ)
  (Gᵉ : functor-Large-Precategoryᵉ γGᵉ Dᵉ Cᵉ)
  where

  family-of-equivalences-adjoint-pair-Large-Precategoryᵉ : UUωᵉ
  family-of-equivalences-adjoint-pair-Large-Precategoryᵉ =
    {l1ᵉ l2ᵉ : Level} (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ)
    (Yᵉ : obj-Large-Precategoryᵉ Dᵉ l2ᵉ) →
    hom-Large-Precategoryᵉ Dᵉ (obj-functor-Large-Precategoryᵉ Fᵉ Xᵉ) Yᵉ ≃ᵉ
    hom-Large-Precategoryᵉ Cᵉ Xᵉ (obj-functor-Large-Precategoryᵉ Gᵉ Yᵉ)

  naturality-family-of-equivalences-adjoint-pair-Large-Precategoryᵉ :
    family-of-equivalences-adjoint-pair-Large-Precategoryᵉ → UUωᵉ
  naturality-family-of-equivalences-adjoint-pair-Large-Precategoryᵉ eᵉ =
    { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    { X1ᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
    { X2ᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
    { Y1ᵉ : obj-Large-Precategoryᵉ Dᵉ l3ᵉ}
    { Y2ᵉ : obj-Large-Precategoryᵉ Dᵉ l4ᵉ}
    ( fᵉ : hom-Large-Precategoryᵉ Cᵉ X2ᵉ X1ᵉ)
    ( gᵉ : hom-Large-Precategoryᵉ Dᵉ Y1ᵉ Y2ᵉ) →
    coherence-square-mapsᵉ
      ( map-equivᵉ (eᵉ X1ᵉ Y1ᵉ))
      ( λ hᵉ →
        comp-hom-Large-Precategoryᵉ Dᵉ
          ( comp-hom-Large-Precategoryᵉ Dᵉ gᵉ hᵉ)
          ( hom-functor-Large-Precategoryᵉ Fᵉ fᵉ))
      ( λ hᵉ →
        comp-hom-Large-Precategoryᵉ Cᵉ
          ( comp-hom-Large-Precategoryᵉ Cᵉ
            ( hom-functor-Large-Precategoryᵉ Gᵉ gᵉ)
            ( hᵉ))
          ( fᵉ))
      ( map-equivᵉ (eᵉ X2ᵉ Y2ᵉ))

  record is-adjoint-pair-Large-Precategoryᵉ : UUωᵉ
    where
    field
      equiv-is-adjoint-pair-Large-Precategoryᵉ :
        family-of-equivalences-adjoint-pair-Large-Precategoryᵉ
      naturality-equiv-is-adjoint-pair-Large-Precategoryᵉ :
        naturality-family-of-equivalences-adjoint-pair-Large-Precategoryᵉ
          equiv-is-adjoint-pair-Large-Precategoryᵉ

  open is-adjoint-pair-Large-Precategoryᵉ public

  map-equiv-is-adjoint-pair-Large-Precategoryᵉ :
    (Hᵉ : is-adjoint-pair-Large-Precategoryᵉ) {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) (Yᵉ : obj-Large-Precategoryᵉ Dᵉ l2ᵉ) →
    hom-Large-Precategoryᵉ Dᵉ (obj-functor-Large-Precategoryᵉ Fᵉ Xᵉ) Yᵉ →
    hom-Large-Precategoryᵉ Cᵉ Xᵉ (obj-functor-Large-Precategoryᵉ Gᵉ Yᵉ)
  map-equiv-is-adjoint-pair-Large-Precategoryᵉ Hᵉ Xᵉ Yᵉ =
    map-equivᵉ (equiv-is-adjoint-pair-Large-Precategoryᵉ Hᵉ Xᵉ Yᵉ)

  inv-equiv-is-adjoint-pair-Large-Precategoryᵉ :
    (Hᵉ : is-adjoint-pair-Large-Precategoryᵉ) {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) (Yᵉ : obj-Large-Precategoryᵉ Dᵉ l2ᵉ) →
    hom-Large-Precategoryᵉ Cᵉ Xᵉ (obj-functor-Large-Precategoryᵉ Gᵉ Yᵉ) ≃ᵉ
    hom-Large-Precategoryᵉ Dᵉ (obj-functor-Large-Precategoryᵉ Fᵉ Xᵉ) Yᵉ
  inv-equiv-is-adjoint-pair-Large-Precategoryᵉ Hᵉ Xᵉ Yᵉ =
    inv-equivᵉ (equiv-is-adjoint-pair-Large-Precategoryᵉ Hᵉ Xᵉ Yᵉ)

  map-inv-equiv-is-adjoint-pair-Large-Precategoryᵉ :
    (Hᵉ : is-adjoint-pair-Large-Precategoryᵉ) {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) (Yᵉ : obj-Large-Precategoryᵉ Dᵉ l2ᵉ) →
    hom-Large-Precategoryᵉ Cᵉ Xᵉ (obj-functor-Large-Precategoryᵉ Gᵉ Yᵉ) →
    hom-Large-Precategoryᵉ Dᵉ (obj-functor-Large-Precategoryᵉ Fᵉ Xᵉ) Yᵉ
  map-inv-equiv-is-adjoint-pair-Large-Precategoryᵉ Hᵉ Xᵉ Yᵉ =
    map-inv-equivᵉ (equiv-is-adjoint-pair-Large-Precategoryᵉ Hᵉ Xᵉ Yᵉ)

  naturality-inv-equiv-is-adjoint-pair-Large-Precategoryᵉ :
    ( Hᵉ : is-adjoint-pair-Large-Precategoryᵉ)
    { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    { X1ᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
    { X2ᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
    { Y1ᵉ : obj-Large-Precategoryᵉ Dᵉ l3ᵉ}
    { Y2ᵉ : obj-Large-Precategoryᵉ Dᵉ l4ᵉ}
    ( fᵉ : hom-Large-Precategoryᵉ Cᵉ X2ᵉ X1ᵉ)
    ( gᵉ : hom-Large-Precategoryᵉ Dᵉ Y1ᵉ Y2ᵉ) →
    coherence-square-mapsᵉ
      ( map-inv-equiv-is-adjoint-pair-Large-Precategoryᵉ Hᵉ X1ᵉ Y1ᵉ)
      ( λ hᵉ →
        comp-hom-Large-Precategoryᵉ Cᵉ
          ( comp-hom-Large-Precategoryᵉ Cᵉ (hom-functor-Large-Precategoryᵉ Gᵉ gᵉ) hᵉ)
          ( fᵉ))
      ( λ hᵉ →
        comp-hom-Large-Precategoryᵉ Dᵉ
          ( comp-hom-Large-Precategoryᵉ Dᵉ gᵉ hᵉ)
          ( hom-functor-Large-Precategoryᵉ Fᵉ fᵉ))
      ( map-inv-equiv-is-adjoint-pair-Large-Precategoryᵉ Hᵉ X2ᵉ Y2ᵉ)
  naturality-inv-equiv-is-adjoint-pair-Large-Precategoryᵉ
    Hᵉ {X1ᵉ = X1ᵉ} {X2ᵉ} {Y1ᵉ} {Y2ᵉ} fᵉ gᵉ =
    horizontal-inv-equiv-coherence-square-mapsᵉ
      ( equiv-is-adjoint-pair-Large-Precategoryᵉ Hᵉ X1ᵉ Y1ᵉ)
      ( λ hᵉ →
        comp-hom-Large-Precategoryᵉ Dᵉ
          ( comp-hom-Large-Precategoryᵉ Dᵉ gᵉ hᵉ)
          ( hom-functor-Large-Precategoryᵉ Fᵉ fᵉ))
      ( λ hᵉ →
        comp-hom-Large-Precategoryᵉ Cᵉ
          ( comp-hom-Large-Precategoryᵉ Cᵉ
            ( hom-functor-Large-Precategoryᵉ Gᵉ gᵉ)
            ( hᵉ))
          ( fᵉ))
      ( equiv-is-adjoint-pair-Large-Precategoryᵉ Hᵉ X2ᵉ Y2ᵉ)
      ( naturality-equiv-is-adjoint-pair-Large-Precategoryᵉ Hᵉ fᵉ gᵉ)
```

### The predicate of being a left adjoint

```agda
module _
  {αCᵉ αDᵉ γFᵉ γGᵉ : Level → Level}
  {βCᵉ βDᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ)
  (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  (Gᵉ : functor-Large-Precategoryᵉ γGᵉ Dᵉ Cᵉ)
  (Fᵉ : functor-Large-Precategoryᵉ γFᵉ Cᵉ Dᵉ)
  where

  is-left-adjoint-functor-Large-Precategoryᵉ : UUωᵉ
  is-left-adjoint-functor-Large-Precategoryᵉ =
    is-adjoint-pair-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
```

### The predicate of being a right adjoint

```agda
module _
  {αCᵉ αDᵉ γFᵉ γGᵉ : Level → Level}
  {βCᵉ βDᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ)
  (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  (Fᵉ : functor-Large-Precategoryᵉ γFᵉ Cᵉ Dᵉ)
  (Gᵉ : functor-Large-Precategoryᵉ γGᵉ Dᵉ Cᵉ)
  where

  is-right-adjoint-functor-Large-Precategoryᵉ : UUωᵉ
  is-right-adjoint-functor-Large-Precategoryᵉ =
    is-adjoint-pair-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
```

### Adjunctions of large precategories

```agda
module _
  {αCᵉ αDᵉ : Level → Level}
  {βCᵉ βDᵉ : Level → Level → Level}
  (γᵉ δᵉ : Level → Level)
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ)
  (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  where

  record Adjunction-Large-Precategoryᵉ : UUωᵉ where
    field
      left-adjoint-Adjunction-Large-Precategoryᵉ :
        functor-Large-Precategoryᵉ γᵉ Cᵉ Dᵉ
      right-adjoint-Adjunction-Large-Precategoryᵉ :
        functor-Large-Precategoryᵉ δᵉ Dᵉ Cᵉ
      is-adjoint-pair-Adjunction-Large-Precategoryᵉ :
        is-adjoint-pair-Large-Precategoryᵉ Cᵉ Dᵉ
          left-adjoint-Adjunction-Large-Precategoryᵉ
          right-adjoint-Adjunction-Large-Precategoryᵉ

  open Adjunction-Large-Precategoryᵉ public

module _
  {αCᵉ αDᵉ : Level → Level}
  {βCᵉ βDᵉ : Level → Level → Level}
  {γᵉ δᵉ : Level → Level}
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ)
  (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  (FGᵉ : Adjunction-Large-Precategoryᵉ γᵉ δᵉ Cᵉ Dᵉ)
  where

  obj-left-adjoint-Adjunction-Large-Precategoryᵉ :
    {lᵉ : Level} → obj-Large-Precategoryᵉ Cᵉ lᵉ → obj-Large-Precategoryᵉ Dᵉ (γᵉ lᵉ)
  obj-left-adjoint-Adjunction-Large-Precategoryᵉ =
    obj-functor-Large-Precategoryᵉ
      ( left-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)

  hom-left-adjoint-Adjunction-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
    {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ} →
    hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ →
    hom-Large-Precategoryᵉ Dᵉ
      ( obj-left-adjoint-Adjunction-Large-Precategoryᵉ Xᵉ)
      ( obj-left-adjoint-Adjunction-Large-Precategoryᵉ Yᵉ)
  hom-left-adjoint-Adjunction-Large-Precategoryᵉ =
    hom-functor-Large-Precategoryᵉ
      ( left-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)

  preserves-id-left-adjoint-Adjunction-Large-Precategoryᵉ :
    {l1ᵉ : Level} (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) →
    hom-left-adjoint-Adjunction-Large-Precategoryᵉ
      ( id-hom-Large-Precategoryᵉ Cᵉ {Xᵉ = Xᵉ}) ＝ᵉ
    id-hom-Large-Precategoryᵉ Dᵉ
  preserves-id-left-adjoint-Adjunction-Large-Precategoryᵉ Xᵉ =
    preserves-id-functor-Large-Precategoryᵉ
      ( left-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)

  obj-right-adjoint-Adjunction-Large-Precategoryᵉ :
    {l1ᵉ : Level} → obj-Large-Precategoryᵉ Dᵉ l1ᵉ → obj-Large-Precategoryᵉ Cᵉ (δᵉ l1ᵉ)
  obj-right-adjoint-Adjunction-Large-Precategoryᵉ =
    obj-functor-Large-Precategoryᵉ
      ( right-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)

  hom-right-adjoint-Adjunction-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {Xᵉ : obj-Large-Precategoryᵉ Dᵉ l1ᵉ}
    {Yᵉ : obj-Large-Precategoryᵉ Dᵉ l2ᵉ} →
    hom-Large-Precategoryᵉ Dᵉ Xᵉ Yᵉ →
    hom-Large-Precategoryᵉ Cᵉ
      ( obj-right-adjoint-Adjunction-Large-Precategoryᵉ Xᵉ)
      ( obj-right-adjoint-Adjunction-Large-Precategoryᵉ Yᵉ)
  hom-right-adjoint-Adjunction-Large-Precategoryᵉ =
    hom-functor-Large-Precategoryᵉ
      ( right-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)

  preserves-id-right-adjoint-Adjunction-Large-Precategoryᵉ :
    {lᵉ : Level}
    (Yᵉ : obj-Large-Precategoryᵉ Dᵉ lᵉ) →
    hom-right-adjoint-Adjunction-Large-Precategoryᵉ
      ( id-hom-Large-Precategoryᵉ Dᵉ {Xᵉ = Yᵉ}) ＝ᵉ
    id-hom-Large-Precategoryᵉ Cᵉ
  preserves-id-right-adjoint-Adjunction-Large-Precategoryᵉ Yᵉ =
    preserves-id-functor-Large-Precategoryᵉ
      ( right-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)

  equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ)
    (Yᵉ : obj-Large-Precategoryᵉ Dᵉ l2ᵉ) →
    hom-Large-Precategoryᵉ Dᵉ
      ( obj-left-adjoint-Adjunction-Large-Precategoryᵉ Xᵉ)
      ( Yᵉ) ≃ᵉ
    hom-Large-Precategoryᵉ Cᵉ
      ( Xᵉ)
      ( obj-right-adjoint-Adjunction-Large-Precategoryᵉ Yᵉ)
  equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ =
    equiv-is-adjoint-pair-Large-Precategoryᵉ
      ( is-adjoint-pair-Adjunction-Large-Precategoryᵉ FGᵉ)

  map-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ)
    (Yᵉ : obj-Large-Precategoryᵉ Dᵉ l2ᵉ) →
    hom-Large-Precategoryᵉ Dᵉ
      ( obj-left-adjoint-Adjunction-Large-Precategoryᵉ Xᵉ)
      ( Yᵉ) →
    hom-Large-Precategoryᵉ Cᵉ
      ( Xᵉ)
      ( obj-right-adjoint-Adjunction-Large-Precategoryᵉ Yᵉ)
  map-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ =
    map-equiv-is-adjoint-pair-Large-Precategoryᵉ Cᵉ Dᵉ
      ( left-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)
      ( right-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)
      ( is-adjoint-pair-Adjunction-Large-Precategoryᵉ FGᵉ)

  naturality-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {X1ᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
    {X2ᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
    {Y1ᵉ : obj-Large-Precategoryᵉ Dᵉ l3ᵉ}
    {Y2ᵉ : obj-Large-Precategoryᵉ Dᵉ l4ᵉ}
    (fᵉ : hom-Large-Precategoryᵉ Cᵉ X2ᵉ X1ᵉ)
    (gᵉ : hom-Large-Precategoryᵉ Dᵉ Y1ᵉ Y2ᵉ) →
    coherence-square-mapsᵉ
      ( map-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ X1ᵉ Y1ᵉ)
      ( λ hᵉ →
        comp-hom-Large-Precategoryᵉ Dᵉ
          ( comp-hom-Large-Precategoryᵉ Dᵉ gᵉ hᵉ)
          ( hom-left-adjoint-Adjunction-Large-Precategoryᵉ fᵉ))
      ( λ hᵉ →
        comp-hom-Large-Precategoryᵉ Cᵉ
          ( comp-hom-Large-Precategoryᵉ Cᵉ
            ( hom-right-adjoint-Adjunction-Large-Precategoryᵉ gᵉ)
            ( hᵉ))
          ( fᵉ))
      ( map-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ X2ᵉ Y2ᵉ)
  naturality-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ =
    naturality-equiv-is-adjoint-pair-Large-Precategoryᵉ
      ( is-adjoint-pair-Adjunction-Large-Precategoryᵉ FGᵉ)

  inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ)
    (Yᵉ : obj-Large-Precategoryᵉ Dᵉ l2ᵉ) →
    hom-Large-Precategoryᵉ Cᵉ
      ( Xᵉ)
      ( obj-right-adjoint-Adjunction-Large-Precategoryᵉ Yᵉ) ≃ᵉ
    hom-Large-Precategoryᵉ Dᵉ
      ( obj-left-adjoint-Adjunction-Large-Precategoryᵉ Xᵉ)
      ( Yᵉ)
  inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ Xᵉ Yᵉ =
    inv-equivᵉ (equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ Xᵉ Yᵉ)

  map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ)
    (Yᵉ : obj-Large-Precategoryᵉ Dᵉ l2ᵉ) →
    hom-Large-Precategoryᵉ Cᵉ
      ( Xᵉ)
      ( obj-right-adjoint-Adjunction-Large-Precategoryᵉ Yᵉ) →
    hom-Large-Precategoryᵉ Dᵉ
      ( obj-left-adjoint-Adjunction-Large-Precategoryᵉ Xᵉ)
      ( Yᵉ)
  map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ Xᵉ Yᵉ =
    map-inv-equivᵉ (equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ Xᵉ Yᵉ)

  naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {X1ᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
    {X2ᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
    {Y1ᵉ : obj-Large-Precategoryᵉ Dᵉ l3ᵉ}
    {Y2ᵉ : obj-Large-Precategoryᵉ Dᵉ l4ᵉ}
    (fᵉ : hom-Large-Precategoryᵉ Cᵉ X2ᵉ X1ᵉ)
    (gᵉ : hom-Large-Precategoryᵉ Dᵉ Y1ᵉ Y2ᵉ) →
    coherence-square-mapsᵉ
      ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ X1ᵉ Y1ᵉ)
      ( λ hᵉ →
        comp-hom-Large-Precategoryᵉ Cᵉ
          ( comp-hom-Large-Precategoryᵉ Cᵉ
            ( hom-right-adjoint-Adjunction-Large-Precategoryᵉ gᵉ)
            ( hᵉ))
          ( fᵉ))
      ( λ hᵉ →
        comp-hom-Large-Precategoryᵉ Dᵉ
          ( comp-hom-Large-Precategoryᵉ Dᵉ gᵉ hᵉ)
          ( hom-left-adjoint-Adjunction-Large-Precategoryᵉ fᵉ))
      ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ X2ᵉ Y2ᵉ)
  naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ =
    naturality-inv-equiv-is-adjoint-pair-Large-Precategoryᵉ Cᵉ Dᵉ
      ( left-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)
      ( right-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)
      ( is-adjoint-pair-Adjunction-Large-Precategoryᵉ FGᵉ)
```

### The unit of an adjunction

Givenᵉ anᵉ adjointᵉ pairᵉ `Fᵉ ⊣ᵉ G`,ᵉ weᵉ constructᵉ aᵉ naturalᵉ transformationᵉ
`ηᵉ : idᵉ → Gᵉ ∘ᵉ F`ᵉ calledᵉ theᵉ **unit**ᵉ ofᵉ theᵉ adjunction.ᵉ

```agda
module _
  {αCᵉ αDᵉ : Level → Level} {βCᵉ βDᵉ : Level → Level → Level} {γᵉ δᵉ : Level → Level}
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ) (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  (FGᵉ : Adjunction-Large-Precategoryᵉ γᵉ δᵉ Cᵉ Dᵉ)
  where

  hom-unit-Adjunction-Large-Precategoryᵉ :
    family-of-morphisms-functor-Large-Precategoryᵉ Cᵉ Cᵉ
      ( id-functor-Large-Precategoryᵉ Cᵉ)
      ( comp-functor-Large-Precategoryᵉ Cᵉ Dᵉ Cᵉ
        ( right-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)
        ( left-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ))
  hom-unit-Adjunction-Large-Precategoryᵉ Xᵉ =
    map-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ Xᵉ
      ( obj-left-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ Xᵉ)
      ( id-hom-Large-Precategoryᵉ Dᵉ)

  naturality-unit-Adjunction-Large-Precategoryᵉ :
    naturality-family-of-morphisms-functor-Large-Precategoryᵉ Cᵉ Cᵉ
      ( id-functor-Large-Precategoryᵉ Cᵉ)
      ( comp-functor-Large-Precategoryᵉ Cᵉ Dᵉ Cᵉ
        ( right-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)
        ( left-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ))
      ( hom-unit-Adjunction-Large-Precategoryᵉ)
  naturality-unit-Adjunction-Large-Precategoryᵉ {Xᵉ = Xᵉ} {Yᵉ} fᵉ =
    invᵉ
      ( ( invᵉ
          ( left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ
            ( comp-hom-Large-Precategoryᵉ Cᵉ
              ( hom-unit-Adjunction-Large-Precategoryᵉ
                ( Yᵉ))
              ( fᵉ)))) ∙ᵉ
        ( apᵉ
          ( comp-hom-Large-Precategory'ᵉ Cᵉ
            ( comp-hom-Large-Precategoryᵉ Cᵉ
              ( hom-unit-Adjunction-Large-Precategoryᵉ
                ( Yᵉ))
              ( fᵉ)))
          ( invᵉ
            ( preserves-id-right-adjoint-Adjunction-Large-Precategoryᵉ
              ( Cᵉ)
              ( Dᵉ)
              ( FGᵉ)
              ( obj-left-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ Yᵉ)))) ∙ᵉ
        ( invᵉ
          ( associative-comp-hom-Large-Precategoryᵉ Cᵉ
            ( hom-right-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ
              ( id-hom-Large-Precategoryᵉ Dᵉ))
            ( map-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ
              Cᵉ Dᵉ FGᵉ Yᵉ
              ( obj-left-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ Yᵉ)
              ( id-hom-Large-Precategoryᵉ Dᵉ))
            ( fᵉ))) ∙ᵉ
        ( invᵉ
          ( naturality-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ
            Cᵉ Dᵉ FGᵉ fᵉ
            ( id-hom-Large-Precategoryᵉ Dᵉ)
            ( id-hom-Large-Precategoryᵉ Dᵉ))) ∙ᵉ
        ( apᵉ
          ( map-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ Xᵉ
            ( obj-left-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ Yᵉ))
          ( ( associative-comp-hom-Large-Precategoryᵉ Dᵉ
              ( id-hom-Large-Precategoryᵉ Dᵉ)
              ( id-hom-Large-Precategoryᵉ Dᵉ)
              ( hom-left-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ fᵉ)) ∙ᵉ
            ( left-unit-law-comp-hom-Large-Precategoryᵉ Dᵉ
              ( comp-hom-Large-Precategoryᵉ Dᵉ
                ( id-hom-Large-Precategoryᵉ Dᵉ)
                ( hom-left-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ fᵉ))) ∙ᵉ
            ( left-unit-law-comp-hom-Large-Precategoryᵉ Dᵉ
              ( hom-left-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ fᵉ)) ∙ᵉ
            ( invᵉ
              ( right-unit-law-comp-hom-Large-Precategoryᵉ Dᵉ
                ( hom-left-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ fᵉ))) ∙ᵉ
            ( invᵉ
              ( right-unit-law-comp-hom-Large-Precategoryᵉ Dᵉ
                ( comp-hom-Large-Precategoryᵉ Dᵉ
                  ( hom-left-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ fᵉ)
                  ( id-hom-Large-Precategoryᵉ Dᵉ)))) ∙ᵉ
            ( apᵉ
              ( comp-hom-Large-Precategoryᵉ Dᵉ
                ( comp-hom-Large-Precategoryᵉ Dᵉ
                  ( hom-left-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ fᵉ)
                  ( id-hom-Large-Precategoryᵉ Dᵉ)))
              ( invᵉ
                ( preserves-id-left-adjoint-Adjunction-Large-Precategoryᵉ
                  Cᵉ Dᵉ FGᵉ Xᵉ)))) ∙ᵉ
          ( naturality-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ
            Cᵉ Dᵉ FGᵉ
            ( id-hom-Large-Precategoryᵉ Cᵉ)
            ( hom-left-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ fᵉ)
            ( id-hom-Large-Precategoryᵉ Dᵉ)) ∙ᵉ
          ( right-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ
            ( comp-hom-Large-Precategoryᵉ Cᵉ
              ( hom-right-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ
                ( hom-left-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ fᵉ))
              ( hom-unit-Adjunction-Large-Precategoryᵉ
                ( Xᵉ))))))

  unit-Adjunction-Large-Precategoryᵉ :
    natural-transformation-Large-Precategoryᵉ Cᵉ Cᵉ
      ( id-functor-Large-Precategoryᵉ Cᵉ)
      ( comp-functor-Large-Precategoryᵉ Cᵉ Dᵉ Cᵉ
        ( right-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)
        ( left-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ))
  hom-natural-transformation-Large-Precategoryᵉ
    unit-Adjunction-Large-Precategoryᵉ =
    hom-unit-Adjunction-Large-Precategoryᵉ
  naturality-natural-transformation-Large-Precategoryᵉ
    unit-Adjunction-Large-Precategoryᵉ =
    naturality-unit-Adjunction-Large-Precategoryᵉ
```

### The counit of an adjunction

Givenᵉ anᵉ adjointᵉ pairᵉ `Fᵉ ⊣ᵉ G`,ᵉ weᵉ constructᵉ aᵉ naturalᵉ transformationᵉ
`εᵉ : Fᵉ ∘ᵉ Gᵉ → id`ᵉ calledᵉ theᵉ **counit**ᵉ ofᵉ theᵉ adjunction.ᵉ

```agda
module _
  {αCᵉ αDᵉ : Level → Level} {βCᵉ βDᵉ : Level → Level → Level} {γᵉ δᵉ : Level → Level}
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ) (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  (FGᵉ : Adjunction-Large-Precategoryᵉ γᵉ δᵉ Cᵉ Dᵉ)
  where

  hom-counit-Adjunction-Large-Precategoryᵉ :
    family-of-morphisms-functor-Large-Precategoryᵉ Dᵉ Dᵉ
      ( comp-functor-Large-Precategoryᵉ Dᵉ Cᵉ Dᵉ
        ( left-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)
        ( right-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ))
      ( id-functor-Large-Precategoryᵉ Dᵉ)
  hom-counit-Adjunction-Large-Precategoryᵉ Yᵉ =
    map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ
      ( obj-right-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ Yᵉ)
      ( Yᵉ)
      ( id-hom-Large-Precategoryᵉ Cᵉ)

  naturality-counit-Adjunction-Large-Precategoryᵉ :
    naturality-family-of-morphisms-functor-Large-Precategoryᵉ Dᵉ Dᵉ
      ( comp-functor-Large-Precategoryᵉ Dᵉ Cᵉ Dᵉ
        ( left-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)
        ( right-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ))
      ( id-functor-Large-Precategoryᵉ Dᵉ)
      ( hom-counit-Adjunction-Large-Precategoryᵉ)
  naturality-counit-Adjunction-Large-Precategoryᵉ {Xᵉ = Xᵉ} {Yᵉ = Yᵉ} fᵉ =
    invᵉ
      ( ( invᵉ
          ( left-unit-law-comp-hom-Large-Precategoryᵉ Dᵉ
            ( comp-hom-Large-Precategoryᵉ Dᵉ
              ( hom-counit-Adjunction-Large-Precategoryᵉ
                ( Yᵉ))
              ( hom-left-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ
                ( hom-right-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ fᵉ))))) ∙ᵉ
        ( invᵉ
          ( associative-comp-hom-Large-Precategoryᵉ Dᵉ
            ( id-hom-Large-Precategoryᵉ Dᵉ)
            ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ
              ( obj-right-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ Yᵉ)
              ( Yᵉ)
              ( id-hom-Large-Precategoryᵉ Cᵉ))
            ( hom-left-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ
              ( hom-right-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ fᵉ)))) ∙ᵉ
        ( invᵉ
          ( naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ
            ( Cᵉ)
            ( Dᵉ)
            ( FGᵉ)
            ( hom-right-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ fᵉ)
            ( id-hom-Large-Precategoryᵉ Dᵉ)
            ( id-hom-Large-Precategoryᵉ Cᵉ))) ∙ᵉ
        ( apᵉ
          ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ
            ( obj-right-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ Xᵉ)
            ( Yᵉ))
          ( ( apᵉ
              ( comp-hom-Large-Precategory'ᵉ Cᵉ
                ( hom-right-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ fᵉ))
              ( ( right-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ
                  ( hom-right-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ
                    ( id-hom-Large-Precategoryᵉ Dᵉ))) ∙ᵉ
                ( preserves-id-right-adjoint-Adjunction-Large-Precategoryᵉ
                  Cᵉ Dᵉ FGᵉ Yᵉ))) ∙ᵉ
            ( left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ
              ( hom-right-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ fᵉ)) ∙ᵉ
            ( ( invᵉ
                ( right-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ
                  ( hom-right-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ fᵉ))) ∙ᵉ
              ( invᵉ
                ( right-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ
                  ( comp-hom-Large-Precategoryᵉ Cᵉ
                    ( hom-right-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ fᵉ)
                    ( id-hom-Large-Precategoryᵉ Cᵉ)))))) ∙ᵉ
        ( naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ
          ( FGᵉ)
          ( id-hom-Large-Precategoryᵉ Cᵉ)
            ( fᵉ)
            ( id-hom-Large-Precategoryᵉ Cᵉ)) ∙ᵉ
          ( apᵉ
            ( comp-hom-Large-Precategoryᵉ
              ( Dᵉ)
              ( comp-hom-Large-Precategoryᵉ Dᵉ fᵉ
                ( hom-counit-Adjunction-Large-Precategoryᵉ
                  ( Xᵉ))))
            ( preserves-id-left-adjoint-Adjunction-Large-Precategoryᵉ
              ( Cᵉ)
              ( Dᵉ)
              ( FGᵉ)
              ( obj-right-adjoint-Adjunction-Large-Precategoryᵉ Cᵉ Dᵉ FGᵉ Xᵉ))) ∙ᵉ
          ( right-unit-law-comp-hom-Large-Precategoryᵉ Dᵉ
            ( comp-hom-Large-Precategoryᵉ Dᵉ fᵉ
              ( hom-counit-Adjunction-Large-Precategoryᵉ
                ( Xᵉ))))))

  counit-Adjunction-Large-Precategoryᵉ :
    natural-transformation-Large-Precategoryᵉ Dᵉ Dᵉ
      ( comp-functor-Large-Precategoryᵉ Dᵉ Cᵉ Dᵉ
        ( left-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ)
        ( right-adjoint-Adjunction-Large-Precategoryᵉ FGᵉ))
      ( id-functor-Large-Precategoryᵉ Dᵉ)
  hom-natural-transformation-Large-Precategoryᵉ
    counit-Adjunction-Large-Precategoryᵉ =
    hom-counit-Adjunction-Large-Precategoryᵉ
  naturality-natural-transformation-Large-Precategoryᵉ
    counit-Adjunction-Large-Precategoryᵉ =
    naturality-counit-Adjunction-Large-Precategoryᵉ
```