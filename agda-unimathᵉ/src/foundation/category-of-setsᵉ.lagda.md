# The category of sets

```agda
module foundation.category-of-setsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.isomorphisms-in-large-precategoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.isomorphisms-of-setsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Theᵉ **categoryᵉ ofᵉ [sets](foundation-core.sets.md)**ᵉ consistsᵉ ofᵉ setsᵉ andᵉ
functions.ᵉ Thereᵉ isᵉ aᵉ [category](category-theory.categories.mdᵉ) ofᵉ setsᵉ forᵉ eachᵉ
universeᵉ level,ᵉ andᵉ thereᵉ isᵉ aᵉ
[largeᵉ category](category-theory.large-categories.mdᵉ) ofᵉ sets.ᵉ

## Definitions

### The large precategory of sets

```agda
Set-Large-Precategoryᵉ : Large-Precategoryᵉ lsuc (_⊔ᵉ_)
obj-Large-Precategoryᵉ Set-Large-Precategoryᵉ = Setᵉ
hom-set-Large-Precategoryᵉ Set-Large-Precategoryᵉ = hom-set-Setᵉ
comp-hom-Large-Precategoryᵉ Set-Large-Precategoryᵉ gᵉ fᵉ = gᵉ ∘ᵉ fᵉ
id-hom-Large-Precategoryᵉ Set-Large-Precategoryᵉ = idᵉ
involutive-eq-associative-comp-hom-Large-Precategoryᵉ Set-Large-Precategoryᵉ
  hᵉ gᵉ fᵉ =
  reflⁱᵉ
left-unit-law-comp-hom-Large-Precategoryᵉ Set-Large-Precategoryᵉ fᵉ = reflᵉ
right-unit-law-comp-hom-Large-Precategoryᵉ Set-Large-Precategoryᵉ fᵉ = reflᵉ
```

### The large category of sets

```agda
id-iso-Setᵉ :
  {lᵉ : Level} {Xᵉ : obj-Large-Precategoryᵉ Set-Large-Precategoryᵉ lᵉ} →
  iso-Large-Precategoryᵉ Set-Large-Precategoryᵉ Xᵉ Xᵉ
id-iso-Setᵉ {lᵉ} {Xᵉ} = id-iso-Large-Precategoryᵉ (Set-Large-Precategoryᵉ) {lᵉ} {Xᵉ}

iso-eq-Setᵉ :
  {lᵉ : Level} (Xᵉ Yᵉ : obj-Large-Precategoryᵉ Set-Large-Precategoryᵉ lᵉ) →
  Xᵉ ＝ᵉ Yᵉ → iso-Large-Precategoryᵉ Set-Large-Precategoryᵉ Xᵉ Yᵉ
iso-eq-Setᵉ = iso-eq-Large-Precategoryᵉ Set-Large-Precategoryᵉ

is-large-category-Set-Large-Precategoryᵉ :
  is-large-category-Large-Precategoryᵉ Set-Large-Precategoryᵉ
is-large-category-Set-Large-Precategoryᵉ {lᵉ} Xᵉ =
  fundamental-theorem-idᵉ
    ( is-contr-equiv'ᵉ
      ( Σᵉ (Setᵉ lᵉ) (equiv-Setᵉ Xᵉ))
      ( equiv-totᵉ (equiv-iso-equiv-Setᵉ Xᵉ))
      ( is-torsorial-equiv-Setᵉ Xᵉ))
    ( iso-eq-Setᵉ Xᵉ)

Set-Large-Categoryᵉ : Large-Categoryᵉ lsuc (_⊔ᵉ_)
large-precategory-Large-Categoryᵉ Set-Large-Categoryᵉ = Set-Large-Precategoryᵉ
is-large-category-Large-Categoryᵉ Set-Large-Categoryᵉ =
  is-large-category-Set-Large-Precategoryᵉ
```

### The precategory of small sets

```agda
Set-Precategoryᵉ : (lᵉ : Level) → Precategoryᵉ (lsuc lᵉ) lᵉ
Set-Precategoryᵉ = precategory-Large-Precategoryᵉ Set-Large-Precategoryᵉ
```

### The category of small sets

Theᵉ precategoryᵉ ofᵉ setsᵉ andᵉ functionsᵉ in aᵉ givenᵉ universeᵉ isᵉ aᵉ category.ᵉ

```agda
Set-Categoryᵉ : (lᵉ : Level) → Categoryᵉ (lsuc lᵉ) lᵉ
Set-Categoryᵉ = category-Large-Categoryᵉ Set-Large-Categoryᵉ

is-category-Set-Precategoryᵉ :
  (lᵉ : Level) → is-category-Precategoryᵉ (Set-Precategoryᵉ lᵉ)
is-category-Set-Precategoryᵉ lᵉ =
  is-category-Categoryᵉ (Set-Categoryᵉ lᵉ)
```

## Comments

Sinceᵉ setsᵉ areᵉ equivalentᵉ to theirᵉ set-truncations,ᵉ theᵉ categoryᵉ ofᵉ setsᵉ formsᵉ aᵉ
[fullᵉ subprecategory](category-theory.full-large-subprecategories.mdᵉ) ofᵉ theᵉ
homotopyᵉ precategoryᵉ ofᵉ types.ᵉ

## See also

-ᵉ [Presheafᵉ categories](category-theory.presheaf-categories.mdᵉ)

## External links

-ᵉ [Set](https://ncatlab.org/nlab/show/Setᵉ) atᵉ $n$Labᵉ
-ᵉ [Categoryᵉ ofᵉ sets](https://en.wikipedia.org/wiki/Category_of_setsᵉ) atᵉ
  Wikipediaᵉ