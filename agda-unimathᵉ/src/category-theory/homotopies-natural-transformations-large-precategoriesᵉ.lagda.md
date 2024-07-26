# Homotopies of natural transformations in large precategories

```agda
module category-theory.homotopies-natural-transformations-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.natural-transformations-functors-large-precategoriesᵉ

open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Twoᵉ
[naturalᵉ transformations](category-theory.natural-transformations-functors-large-precategories.mdᵉ)
`αᵉ βᵉ : Fᵉ ⇒ᵉ G`ᵉ areᵉ **homotopic**ᵉ ifᵉ forᵉ everyᵉ objectᵉ `x`ᵉ thereᵉ isᵉ anᵉ
[identification](foundation-core.identity-types.mdᵉ) `αᵉ xᵉ ＝ᵉ βᵉ x`.ᵉ

Inᵉ `UUω`ᵉ theᵉ usualᵉ identityᵉ typeᵉ isᵉ notᵉ available.ᵉ Ifᵉ itᵉ were,ᵉ weᵉ wouldᵉ beᵉ ableᵉ
to characterizeᵉ theᵉ identityᵉ typeᵉ ofᵉ naturalᵉ transformationsᵉ fromᵉ `F`ᵉ to `G`ᵉ asᵉ
theᵉ typeᵉ ofᵉ homotopiesᵉ ofᵉ naturalᵉ transformations.ᵉ

## Definitions

### Homotopies of natural transformations

```agda
module _
  {αCᵉ αDᵉ γFᵉ γGᵉ : Level → Level} {βCᵉ βDᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ) (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  {Fᵉ : functor-Large-Precategoryᵉ γFᵉ Cᵉ Dᵉ}
  {Gᵉ : functor-Large-Precategoryᵉ γGᵉ Cᵉ Dᵉ}
  where

  htpy-natural-transformation-Large-Precategoryᵉ :
    (σᵉ τᵉ : natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) → UUωᵉ
  htpy-natural-transformation-Large-Precategoryᵉ σᵉ τᵉ =
    { lᵉ : Level} (Xᵉ : obj-Large-Precategoryᵉ Cᵉ lᵉ) →
    ( hom-natural-transformation-Large-Precategoryᵉ σᵉ Xᵉ) ＝ᵉ
    ( hom-natural-transformation-Large-Precategoryᵉ τᵉ Xᵉ)
```

### The reflexivity homotopy

```agda
module _
  {αCᵉ αDᵉ γFᵉ γGᵉ : Level → Level} {βCᵉ βDᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ) (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  {Fᵉ : functor-Large-Precategoryᵉ γFᵉ Cᵉ Dᵉ}
  {Gᵉ : functor-Large-Precategoryᵉ γGᵉ Cᵉ Dᵉ}
  where

  refl-htpy-natural-transformation-Large-Precategoryᵉ :
    (αᵉ : natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    htpy-natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ αᵉ αᵉ
  refl-htpy-natural-transformation-Large-Precategoryᵉ αᵉ = refl-htpyᵉ
```

### Concatenation of homotopies

Aᵉ homotopyᵉ fromᵉ `α`ᵉ to `β`ᵉ canᵉ beᵉ concatenatedᵉ with aᵉ homotopyᵉ fromᵉ `β`ᵉ to `γ`ᵉ
to formᵉ aᵉ homotopyᵉ fromᵉ `α`ᵉ to `γ`.ᵉ Theᵉ concatenationᵉ isᵉ associative.ᵉ

```agda
module _
  {αCᵉ αDᵉ γFᵉ γGᵉ : Level → Level} {βCᵉ βDᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ) (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  {Fᵉ : functor-Large-Precategoryᵉ γFᵉ Cᵉ Dᵉ}
  {Gᵉ : functor-Large-Precategoryᵉ γGᵉ Cᵉ Dᵉ}
  where

  concat-htpy-natural-transformation-Large-Precategoryᵉ :
    (σᵉ τᵉ υᵉ : natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    htpy-natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ σᵉ τᵉ →
    htpy-natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ τᵉ υᵉ →
    htpy-natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ σᵉ υᵉ
  concat-htpy-natural-transformation-Large-Precategoryᵉ σᵉ τᵉ υᵉ Hᵉ Kᵉ = Hᵉ ∙hᵉ Kᵉ

  associative-concat-htpy-natural-transformation-Large-Precategoryᵉ :
    (σᵉ τᵉ υᵉ ϕᵉ : natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
    (Hᵉ : htpy-natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ σᵉ τᵉ)
    (Kᵉ : htpy-natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ τᵉ υᵉ)
    (Lᵉ : htpy-natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ υᵉ ϕᵉ) →
    {lᵉ : Level} (Xᵉ : obj-Large-Precategoryᵉ Cᵉ lᵉ) →
    ( concat-htpy-natural-transformation-Large-Precategoryᵉ σᵉ υᵉ ϕᵉ
      ( concat-htpy-natural-transformation-Large-Precategoryᵉ σᵉ τᵉ υᵉ Hᵉ Kᵉ)
      ( Lᵉ)
      ( Xᵉ)) ＝ᵉ
    ( concat-htpy-natural-transformation-Large-Precategoryᵉ σᵉ τᵉ ϕᵉ
      ( Hᵉ)
      ( concat-htpy-natural-transformation-Large-Precategoryᵉ τᵉ υᵉ ϕᵉ Kᵉ Lᵉ)
      ( Xᵉ))
  associative-concat-htpy-natural-transformation-Large-Precategoryᵉ
    σᵉ τᵉ υᵉ ϕᵉ Hᵉ Kᵉ Lᵉ =
    assoc-htpyᵉ Hᵉ Kᵉ Lᵉ
```