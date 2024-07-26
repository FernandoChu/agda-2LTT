# Adjunctions between large categories

```agda
module category-theory.adjunctions-large-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.adjunctions-large-precategoriesᵉ
open import category-theory.functors-large-categoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.natural-transformations-functors-large-categoriesᵉ

open import foundation.commuting-squares-of-mapsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Letᵉ `C`ᵉ andᵉ `D`ᵉ beᵉ twoᵉ [largeᵉ categories](category-theory.large-categories.md).ᵉ
Twoᵉ [functors](category-theory.functors-large-categories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ andᵉ
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
  (Cᵉ : Large-Categoryᵉ αCᵉ βCᵉ)
  (Dᵉ : Large-Categoryᵉ αDᵉ βDᵉ)
  (Fᵉ : functor-Large-Categoryᵉ γFᵉ Cᵉ Dᵉ)
  (Gᵉ : functor-Large-Categoryᵉ γGᵉ Dᵉ Cᵉ)
  where

  family-of-equivalences-adjoint-pair-Large-Categoryᵉ : UUωᵉ
  family-of-equivalences-adjoint-pair-Large-Categoryᵉ =
    family-of-equivalences-adjoint-pair-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  naturality-family-of-equivalences-adjoint-pair-Large-Categoryᵉ :
    family-of-equivalences-adjoint-pair-Large-Categoryᵉ → UUωᵉ
  naturality-family-of-equivalences-adjoint-pair-Large-Categoryᵉ =
    naturality-family-of-equivalences-adjoint-pair-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  is-adjoint-pair-Large-Categoryᵉ : UUωᵉ
  is-adjoint-pair-Large-Categoryᵉ =
    is-adjoint-pair-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  equiv-is-adjoint-pair-Large-Categoryᵉ :
    is-adjoint-pair-Large-Categoryᵉ →
    family-of-equivalences-adjoint-pair-Large-Categoryᵉ
  equiv-is-adjoint-pair-Large-Categoryᵉ =
    equiv-is-adjoint-pair-Large-Precategoryᵉ

  naturality-equiv-is-adjoint-pair-Large-Categoryᵉ :
    (Hᵉ : is-adjoint-pair-Large-Categoryᵉ) →
    naturality-family-of-equivalences-adjoint-pair-Large-Categoryᵉ
      ( equiv-is-adjoint-pair-Large-Precategoryᵉ Hᵉ)
  naturality-equiv-is-adjoint-pair-Large-Categoryᵉ =
    naturality-equiv-is-adjoint-pair-Large-Precategoryᵉ

  map-equiv-is-adjoint-pair-Large-Categoryᵉ :
    (Hᵉ : is-adjoint-pair-Large-Categoryᵉ) {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ) (Yᵉ : obj-Large-Categoryᵉ Dᵉ l2ᵉ) →
    hom-Large-Categoryᵉ Dᵉ (obj-functor-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Xᵉ) Yᵉ →
    hom-Large-Categoryᵉ Cᵉ Xᵉ (obj-functor-Large-Categoryᵉ Dᵉ Cᵉ Gᵉ Yᵉ)
  map-equiv-is-adjoint-pair-Large-Categoryᵉ =
    map-equiv-is-adjoint-pair-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  inv-equiv-is-adjoint-pair-Large-Categoryᵉ :
    (Hᵉ : is-adjoint-pair-Large-Categoryᵉ) {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ) (Yᵉ : obj-Large-Categoryᵉ Dᵉ l2ᵉ) →
    hom-Large-Categoryᵉ Cᵉ Xᵉ (obj-functor-Large-Categoryᵉ Dᵉ Cᵉ Gᵉ Yᵉ) ≃ᵉ
    hom-Large-Categoryᵉ Dᵉ (obj-functor-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Xᵉ) Yᵉ
  inv-equiv-is-adjoint-pair-Large-Categoryᵉ =
    inv-equiv-is-adjoint-pair-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  map-inv-equiv-is-adjoint-pair-Large-Categoryᵉ :
    (Hᵉ : is-adjoint-pair-Large-Categoryᵉ) {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ) (Yᵉ : obj-Large-Categoryᵉ Dᵉ l2ᵉ) →
    hom-Large-Categoryᵉ Cᵉ Xᵉ (obj-functor-Large-Categoryᵉ Dᵉ Cᵉ Gᵉ Yᵉ) →
    hom-Large-Categoryᵉ Dᵉ (obj-functor-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Xᵉ) Yᵉ
  map-inv-equiv-is-adjoint-pair-Large-Categoryᵉ =
    map-inv-equiv-is-adjoint-pair-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  naturality-inv-equiv-is-adjoint-pair-Large-Categoryᵉ :
    ( Hᵉ : is-adjoint-pair-Large-Categoryᵉ)
    { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    { X1ᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ}
    { X2ᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
    { Y1ᵉ : obj-Large-Categoryᵉ Dᵉ l3ᵉ}
    { Y2ᵉ : obj-Large-Categoryᵉ Dᵉ l4ᵉ}
    ( fᵉ : hom-Large-Categoryᵉ Cᵉ X2ᵉ X1ᵉ)
    ( gᵉ : hom-Large-Categoryᵉ Dᵉ Y1ᵉ Y2ᵉ) →
    coherence-square-mapsᵉ
      ( map-inv-equiv-is-adjoint-pair-Large-Categoryᵉ Hᵉ X1ᵉ Y1ᵉ)
      ( λ hᵉ →
        comp-hom-Large-Categoryᵉ Cᵉ
          ( comp-hom-Large-Categoryᵉ Cᵉ (hom-functor-Large-Categoryᵉ Dᵉ Cᵉ Gᵉ gᵉ) hᵉ)
          ( fᵉ))
      ( λ hᵉ →
        comp-hom-Large-Categoryᵉ Dᵉ
          ( comp-hom-Large-Categoryᵉ Dᵉ gᵉ hᵉ)
          ( hom-functor-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ fᵉ))
      ( map-inv-equiv-is-adjoint-pair-Large-Categoryᵉ Hᵉ X2ᵉ Y2ᵉ)
  naturality-inv-equiv-is-adjoint-pair-Large-Categoryᵉ =
    naturality-inv-equiv-is-adjoint-pair-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
```

### The predicate of being a left adjoint

```agda
module _
  {αCᵉ αDᵉ γFᵉ γGᵉ : Level → Level}
  {βCᵉ βDᵉ : Level → Level → Level}
  {Cᵉ : Large-Categoryᵉ αCᵉ βCᵉ}
  {Dᵉ : Large-Categoryᵉ αDᵉ βDᵉ}
  (Gᵉ : functor-Large-Categoryᵉ γGᵉ Dᵉ Cᵉ)
  (Fᵉ : functor-Large-Categoryᵉ γFᵉ Cᵉ Dᵉ)
  where

  is-left-adjoint-functor-Large-Categoryᵉ : UUωᵉ
  is-left-adjoint-functor-Large-Categoryᵉ =
    is-adjoint-pair-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
```

### The predicate of being a right adjoint

```agda
module _
  {αCᵉ αDᵉ γFᵉ γGᵉ : Level → Level}
  {βCᵉ βDᵉ : Level → Level → Level}
  {Cᵉ : Large-Categoryᵉ αCᵉ βCᵉ}
  {Dᵉ : Large-Categoryᵉ αDᵉ βDᵉ}
  (Fᵉ : functor-Large-Categoryᵉ γFᵉ Cᵉ Dᵉ)
  (Gᵉ : functor-Large-Categoryᵉ γGᵉ Dᵉ Cᵉ)
  where

  is-right-adjoint-functor-Large-Categoryᵉ : UUωᵉ
  is-right-adjoint-functor-Large-Categoryᵉ =
    is-adjoint-pair-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
```

### Adjunctions of large precategories

```agda
module _
  {αCᵉ αDᵉ : Level → Level}
  {βCᵉ βDᵉ : Level → Level → Level}
  (γᵉ δᵉ : Level → Level)
  (Cᵉ : Large-Categoryᵉ αCᵉ βCᵉ)
  (Dᵉ : Large-Categoryᵉ αDᵉ βDᵉ)
  where

  Adjunction-Large-Categoryᵉ : UUωᵉ
  Adjunction-Large-Categoryᵉ =
    Adjunction-Large-Precategoryᵉ γᵉ δᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)

module _
  {αCᵉ αDᵉ : Level → Level}
  {βCᵉ βDᵉ : Level → Level → Level}
  {γᵉ δᵉ : Level → Level}
  (Cᵉ : Large-Categoryᵉ αCᵉ βCᵉ)
  (Dᵉ : Large-Categoryᵉ αDᵉ βDᵉ)
  (Fᵉ : Adjunction-Large-Categoryᵉ γᵉ δᵉ Cᵉ Dᵉ)
  where

  left-adjoint-Adjunction-Large-Categoryᵉ :
    functor-Large-Categoryᵉ γᵉ Cᵉ Dᵉ
  left-adjoint-Adjunction-Large-Categoryᵉ =
    left-adjoint-Adjunction-Large-Precategoryᵉ Fᵉ

  right-adjoint-Adjunction-Large-Categoryᵉ :
    functor-Large-Categoryᵉ δᵉ Dᵉ Cᵉ
  right-adjoint-Adjunction-Large-Categoryᵉ =
    right-adjoint-Adjunction-Large-Precategoryᵉ Fᵉ

  is-adjoint-pair-Adjunction-Large-Categoryᵉ :
    is-adjoint-pair-Large-Categoryᵉ Cᵉ Dᵉ
      ( left-adjoint-Adjunction-Large-Categoryᵉ)
      ( right-adjoint-Adjunction-Large-Categoryᵉ)
  is-adjoint-pair-Adjunction-Large-Categoryᵉ =
    is-adjoint-pair-Adjunction-Large-Precategoryᵉ Fᵉ

  obj-left-adjoint-Adjunction-Large-Categoryᵉ :
    {lᵉ : Level} → obj-Large-Categoryᵉ Cᵉ lᵉ → obj-Large-Categoryᵉ Dᵉ (γᵉ lᵉ)
  obj-left-adjoint-Adjunction-Large-Categoryᵉ =
    obj-left-adjoint-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  hom-left-adjoint-Adjunction-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ}
    {Yᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ} →
    hom-Large-Categoryᵉ Cᵉ Xᵉ Yᵉ →
    hom-Large-Categoryᵉ Dᵉ
      ( obj-left-adjoint-Adjunction-Large-Categoryᵉ Xᵉ)
      ( obj-left-adjoint-Adjunction-Large-Categoryᵉ Yᵉ)
  hom-left-adjoint-Adjunction-Large-Categoryᵉ =
    hom-left-adjoint-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  preserves-id-left-adjoint-Adjunction-Large-Categoryᵉ :
    {l1ᵉ : Level}
    (Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ) →
    hom-left-adjoint-Adjunction-Large-Categoryᵉ
      ( id-hom-Large-Categoryᵉ Cᵉ {Xᵉ = Xᵉ}) ＝ᵉ
    id-hom-Large-Categoryᵉ Dᵉ
  preserves-id-left-adjoint-Adjunction-Large-Categoryᵉ =
    preserves-id-left-adjoint-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  obj-right-adjoint-Adjunction-Large-Categoryᵉ :
    {l1ᵉ : Level} → obj-Large-Categoryᵉ Dᵉ l1ᵉ → obj-Large-Categoryᵉ Cᵉ (δᵉ l1ᵉ)
  obj-right-adjoint-Adjunction-Large-Categoryᵉ =
    obj-right-adjoint-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  hom-right-adjoint-Adjunction-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {Xᵉ : obj-Large-Categoryᵉ Dᵉ l1ᵉ}
    {Yᵉ : obj-Large-Categoryᵉ Dᵉ l2ᵉ} →
    hom-Large-Categoryᵉ Dᵉ Xᵉ Yᵉ →
    hom-Large-Categoryᵉ Cᵉ
      ( obj-right-adjoint-Adjunction-Large-Categoryᵉ Xᵉ)
      ( obj-right-adjoint-Adjunction-Large-Categoryᵉ Yᵉ)
  hom-right-adjoint-Adjunction-Large-Categoryᵉ =
    hom-right-adjoint-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  preserves-id-right-adjoint-Adjunction-Large-Categoryᵉ :
    {lᵉ : Level}
    (Yᵉ : obj-Large-Categoryᵉ Dᵉ lᵉ) →
    hom-right-adjoint-Adjunction-Large-Categoryᵉ
      ( id-hom-Large-Categoryᵉ Dᵉ {Xᵉ = Yᵉ}) ＝ᵉ
    id-hom-Large-Categoryᵉ Cᵉ
  preserves-id-right-adjoint-Adjunction-Large-Categoryᵉ =
    preserves-id-right-adjoint-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  equiv-is-adjoint-pair-Adjunction-Large-Categoryᵉ :
    family-of-equivalences-adjoint-pair-Large-Categoryᵉ Cᵉ Dᵉ
      ( left-adjoint-Adjunction-Large-Categoryᵉ)
      ( right-adjoint-Adjunction-Large-Categoryᵉ)
  equiv-is-adjoint-pair-Adjunction-Large-Categoryᵉ =
    equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  map-equiv-is-adjoint-pair-Adjunction-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ)
    (Yᵉ : obj-Large-Categoryᵉ Dᵉ l2ᵉ) →
    hom-Large-Categoryᵉ Dᵉ
      ( obj-left-adjoint-Adjunction-Large-Categoryᵉ Xᵉ)
      ( Yᵉ) →
    hom-Large-Categoryᵉ Cᵉ
      ( Xᵉ)
      ( obj-right-adjoint-Adjunction-Large-Categoryᵉ Yᵉ)
  map-equiv-is-adjoint-pair-Adjunction-Large-Categoryᵉ =
    map-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  naturality-equiv-is-adjoint-pair-Adjunction-Large-Categoryᵉ :
    naturality-family-of-equivalences-adjoint-pair-Large-Categoryᵉ Cᵉ Dᵉ
      ( left-adjoint-Adjunction-Large-Categoryᵉ)
      ( right-adjoint-Adjunction-Large-Categoryᵉ)
      ( equiv-is-adjoint-pair-Adjunction-Large-Categoryᵉ)
  naturality-equiv-is-adjoint-pair-Adjunction-Large-Categoryᵉ =
    naturality-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  inv-equiv-is-adjoint-pair-Adjunction-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ)
    (Yᵉ : obj-Large-Categoryᵉ Dᵉ l2ᵉ) →
    hom-Large-Categoryᵉ Cᵉ
      ( Xᵉ)
      ( obj-right-adjoint-Adjunction-Large-Categoryᵉ Yᵉ) ≃ᵉ
    hom-Large-Categoryᵉ Dᵉ
      ( obj-left-adjoint-Adjunction-Large-Categoryᵉ Xᵉ)
      ( Yᵉ)
  inv-equiv-is-adjoint-pair-Adjunction-Large-Categoryᵉ =
    inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  map-inv-equiv-is-adjoint-pair-Adjunction-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ)
    (Yᵉ : obj-Large-Categoryᵉ Dᵉ l2ᵉ) →
    hom-Large-Categoryᵉ Cᵉ
      ( Xᵉ)
      ( obj-right-adjoint-Adjunction-Large-Categoryᵉ Yᵉ) →
    hom-Large-Categoryᵉ Dᵉ
      ( obj-left-adjoint-Adjunction-Large-Categoryᵉ Xᵉ)
      ( Yᵉ)
  map-inv-equiv-is-adjoint-pair-Adjunction-Large-Categoryᵉ =
    map-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Categoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {X1ᵉ : obj-Large-Categoryᵉ Cᵉ l1ᵉ}
    {X2ᵉ : obj-Large-Categoryᵉ Cᵉ l2ᵉ}
    {Y1ᵉ : obj-Large-Categoryᵉ Dᵉ l3ᵉ}
    {Y2ᵉ : obj-Large-Categoryᵉ Dᵉ l4ᵉ}
    (fᵉ : hom-Large-Categoryᵉ Cᵉ X2ᵉ X1ᵉ)
    (gᵉ : hom-Large-Categoryᵉ Dᵉ Y1ᵉ Y2ᵉ) →
    coherence-square-mapsᵉ
      ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Categoryᵉ X1ᵉ Y1ᵉ)
      ( λ hᵉ →
        comp-hom-Large-Categoryᵉ Cᵉ
          ( comp-hom-Large-Categoryᵉ Cᵉ
            ( hom-right-adjoint-Adjunction-Large-Categoryᵉ gᵉ)
            ( hᵉ))
          ( fᵉ))
      ( λ hᵉ →
        comp-hom-Large-Categoryᵉ Dᵉ
          ( comp-hom-Large-Categoryᵉ Dᵉ gᵉ hᵉ)
          ( hom-left-adjoint-Adjunction-Large-Categoryᵉ fᵉ))
      ( map-inv-equiv-is-adjoint-pair-Adjunction-Large-Categoryᵉ X2ᵉ Y2ᵉ)
  naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Categoryᵉ =
    naturality-inv-equiv-is-adjoint-pair-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
```

### The unit of an adjunction

Givenᵉ anᵉ adjointᵉ pairᵉ `Fᵉ ⊣ᵉ G`,ᵉ weᵉ constructᵉ aᵉ naturalᵉ transformationᵉ
`ηᵉ : idᵉ → Gᵉ ∘ᵉ F`ᵉ calledᵉ theᵉ **unit**ᵉ ofᵉ theᵉ adjunction.ᵉ

```agda
module _
  {αCᵉ αDᵉ : Level → Level} {βCᵉ βDᵉ : Level → Level → Level} {γᵉ δᵉ : Level → Level}
  (Cᵉ : Large-Categoryᵉ αCᵉ βCᵉ) (Dᵉ : Large-Categoryᵉ αDᵉ βDᵉ)
  (Fᵉ : Adjunction-Large-Categoryᵉ γᵉ δᵉ Cᵉ Dᵉ)
  where

  hom-unit-Adjunction-Large-Categoryᵉ :
    family-of-morphisms-functor-Large-Categoryᵉ Cᵉ Cᵉ
      ( id-functor-Large-Categoryᵉ Cᵉ)
      ( comp-functor-Large-Categoryᵉ Cᵉ Dᵉ Cᵉ
        ( right-adjoint-Adjunction-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ)
        ( left-adjoint-Adjunction-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ))
  hom-unit-Adjunction-Large-Categoryᵉ =
    hom-unit-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  naturality-unit-Adjunction-Large-Categoryᵉ :
    naturality-family-of-morphisms-functor-Large-Categoryᵉ Cᵉ Cᵉ
      ( id-functor-Large-Categoryᵉ Cᵉ)
      ( comp-functor-Large-Categoryᵉ Cᵉ Dᵉ Cᵉ
        ( right-adjoint-Adjunction-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ)
        ( left-adjoint-Adjunction-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ))
      ( hom-unit-Adjunction-Large-Categoryᵉ)
  naturality-unit-Adjunction-Large-Categoryᵉ =
    naturality-unit-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  unit-Adjunction-Large-Categoryᵉ :
    natural-transformation-Large-Categoryᵉ Cᵉ Cᵉ
      ( id-functor-Large-Categoryᵉ Cᵉ)
      ( comp-functor-Large-Categoryᵉ Cᵉ Dᵉ Cᵉ
        ( right-adjoint-Adjunction-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ)
        ( left-adjoint-Adjunction-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ))
  unit-Adjunction-Large-Categoryᵉ =
    unit-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
```

### The counit of an adjunction

Givenᵉ anᵉ adjointᵉ pairᵉ `Fᵉ ⊣ᵉ G`,ᵉ weᵉ constructᵉ aᵉ naturalᵉ transformationᵉ
`εᵉ : Fᵉ ∘ᵉ Gᵉ → id`ᵉ calledᵉ theᵉ **counit**ᵉ ofᵉ theᵉ adjunction.ᵉ

```agda
module _
  {αCᵉ αDᵉ : Level → Level} {βCᵉ βDᵉ : Level → Level → Level} {γᵉ δᵉ : Level → Level}
  (Cᵉ : Large-Categoryᵉ αCᵉ βCᵉ) (Dᵉ : Large-Categoryᵉ αDᵉ βDᵉ)
  (Fᵉ : Adjunction-Large-Categoryᵉ γᵉ δᵉ Cᵉ Dᵉ)
  where

  hom-counit-Adjunction-Large-Categoryᵉ :
    family-of-morphisms-functor-Large-Categoryᵉ Dᵉ Dᵉ
      ( comp-functor-Large-Categoryᵉ Dᵉ Cᵉ Dᵉ
        ( left-adjoint-Adjunction-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ)
        ( right-adjoint-Adjunction-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ))
      ( id-functor-Large-Categoryᵉ Dᵉ)
  hom-counit-Adjunction-Large-Categoryᵉ =
    hom-counit-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  naturality-counit-Adjunction-Large-Categoryᵉ :
    naturality-family-of-morphisms-functor-Large-Categoryᵉ Dᵉ Dᵉ
      ( comp-functor-Large-Categoryᵉ Dᵉ Cᵉ Dᵉ
        ( left-adjoint-Adjunction-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ)
        ( right-adjoint-Adjunction-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ))
      ( id-functor-Large-Categoryᵉ Dᵉ)
      ( hom-counit-Adjunction-Large-Categoryᵉ)
  naturality-counit-Adjunction-Large-Categoryᵉ =
    naturality-counit-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  counit-Adjunction-Large-Categoryᵉ :
    natural-transformation-Large-Categoryᵉ Dᵉ Dᵉ
      ( comp-functor-Large-Categoryᵉ Dᵉ Cᵉ Dᵉ
        ( left-adjoint-Adjunction-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ)
        ( right-adjoint-Adjunction-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ))
      ( id-functor-Large-Categoryᵉ Dᵉ)
  counit-Adjunction-Large-Categoryᵉ =
    counit-Adjunction-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
```