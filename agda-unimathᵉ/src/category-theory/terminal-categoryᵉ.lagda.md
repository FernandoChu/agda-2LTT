# The terminal category

```agda
module category-theory.terminal-categoryᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.constant-functorsᵉ
open import category-theory.functors-categoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.gaunt-categoriesᵉ
open import category-theory.isomorphisms-in-categoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.preunivalent-categoriesᵉ
open import category-theory.strict-categoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **terminalᵉ category**ᵉ isᵉ theᵉ [category](category-theory.categories.mdᵉ) with
oneᵉ objectᵉ andᵉ onlyᵉ theᵉ identityᵉ onᵉ thatᵉ object.ᵉ Thisᵉ categoryᵉ
[represents](category-theory.representable-functors-categories.mdᵉ) objects.ᵉ

## Definition

### The objects and hom-sets of the terminal category

```agda
obj-terminal-Categoryᵉ : UUᵉ lzero
obj-terminal-Categoryᵉ = unitᵉ

hom-set-terminal-Categoryᵉ :
  obj-terminal-Categoryᵉ → obj-terminal-Categoryᵉ → Setᵉ lzero
hom-set-terminal-Categoryᵉ _ _ = unit-Setᵉ

hom-terminal-Categoryᵉ :
  obj-terminal-Categoryᵉ → obj-terminal-Categoryᵉ → UUᵉ lzero
hom-terminal-Categoryᵉ xᵉ yᵉ = type-Setᵉ (hom-set-terminal-Categoryᵉ xᵉ yᵉ)
```

### The underlying precategory of the terminal category

```agda
comp-hom-terminal-Categoryᵉ :
  {xᵉ yᵉ zᵉ : obj-terminal-Categoryᵉ} →
  hom-terminal-Categoryᵉ yᵉ zᵉ →
  hom-terminal-Categoryᵉ xᵉ yᵉ →
  hom-terminal-Categoryᵉ xᵉ zᵉ
comp-hom-terminal-Categoryᵉ _ _ = starᵉ

associative-comp-hom-terminal-Categoryᵉ :
  {xᵉ yᵉ zᵉ wᵉ : obj-terminal-Categoryᵉ} →
  (hᵉ : hom-terminal-Categoryᵉ zᵉ wᵉ)
  (gᵉ : hom-terminal-Categoryᵉ yᵉ zᵉ)
  (fᵉ : hom-terminal-Categoryᵉ xᵉ yᵉ) →
  comp-hom-terminal-Categoryᵉ {xᵉ} (comp-hom-terminal-Categoryᵉ {yᵉ} hᵉ gᵉ) fᵉ ＝ᵉ
  comp-hom-terminal-Categoryᵉ {xᵉ} hᵉ (comp-hom-terminal-Categoryᵉ {xᵉ} gᵉ fᵉ)
associative-comp-hom-terminal-Categoryᵉ hᵉ gᵉ fᵉ = reflᵉ

id-hom-terminal-Categoryᵉ :
  {xᵉ : obj-terminal-Categoryᵉ} → hom-terminal-Categoryᵉ xᵉ xᵉ
id-hom-terminal-Categoryᵉ = starᵉ

left-unit-law-comp-hom-terminal-Categoryᵉ :
  {xᵉ yᵉ : obj-terminal-Categoryᵉ} →
  (fᵉ : hom-terminal-Categoryᵉ xᵉ yᵉ) →
  comp-hom-terminal-Categoryᵉ {xᵉ} (id-hom-terminal-Categoryᵉ {yᵉ}) fᵉ ＝ᵉ fᵉ
left-unit-law-comp-hom-terminal-Categoryᵉ fᵉ = reflᵉ

right-unit-law-comp-hom-terminal-Categoryᵉ :
  {xᵉ yᵉ : obj-terminal-Categoryᵉ} →
  (fᵉ : hom-terminal-Categoryᵉ xᵉ yᵉ) →
  comp-hom-terminal-Categoryᵉ {xᵉ} fᵉ (id-hom-terminal-Categoryᵉ {xᵉ}) ＝ᵉ fᵉ
right-unit-law-comp-hom-terminal-Categoryᵉ fᵉ = reflᵉ

terminal-Precategoryᵉ : Precategoryᵉ lzero lzero
terminal-Precategoryᵉ =
  make-Precategoryᵉ
    ( obj-terminal-Categoryᵉ)
    ( hom-set-terminal-Categoryᵉ)
    ( comp-hom-terminal-Categoryᵉ)
    ( λ xᵉ → id-hom-terminal-Categoryᵉ {xᵉ})
    ( associative-comp-hom-terminal-Categoryᵉ)
    ( left-unit-law-comp-hom-terminal-Categoryᵉ)
    ( right-unit-law-comp-hom-terminal-Categoryᵉ)
```

### The terminal category

```agda
is-category-terminal-Categoryᵉ :
  is-category-Precategoryᵉ terminal-Precategoryᵉ
is-category-terminal-Categoryᵉ xᵉ yᵉ =
  is-equiv-is-contrᵉ
    ( iso-eq-Precategoryᵉ terminal-Precategoryᵉ xᵉ yᵉ)
    ( is-prop-unitᵉ xᵉ yᵉ)
    ( is-contr-Σᵉ is-contr-unitᵉ starᵉ
      ( is-proof-irrelevant-is-propᵉ
        ( is-prop-is-iso-Precategoryᵉ terminal-Precategoryᵉ starᵉ)
        ( starᵉ ,ᵉ reflᵉ ,ᵉ reflᵉ)))

terminal-Categoryᵉ : Categoryᵉ lzero lzero
pr1ᵉ terminal-Categoryᵉ = terminal-Precategoryᵉ
pr2ᵉ terminal-Categoryᵉ = is-category-terminal-Categoryᵉ
```

### The terminal preunivalent category

```agda
is-preunivalent-terminal-Categoryᵉ :
  is-preunivalent-Precategoryᵉ terminal-Precategoryᵉ
is-preunivalent-terminal-Categoryᵉ =
  is-preunivalent-category-Categoryᵉ terminal-Categoryᵉ

terminal-Preunivalent-Categoryᵉ : Preunivalent-Categoryᵉ lzero lzero
terminal-Preunivalent-Categoryᵉ =
  preunivalent-category-Categoryᵉ terminal-Categoryᵉ
```

### The terminal strict category

```agda
is-strict-category-terminal-Categoryᵉ :
  is-strict-category-Precategoryᵉ terminal-Precategoryᵉ
is-strict-category-terminal-Categoryᵉ = is-set-unitᵉ

terminal-Strict-Categoryᵉ : Strict-Categoryᵉ lzero lzero
pr1ᵉ terminal-Strict-Categoryᵉ = terminal-Precategoryᵉ
pr2ᵉ terminal-Strict-Categoryᵉ = is-strict-category-terminal-Categoryᵉ
```

### The terminal gaunt category

```agda
is-gaunt-terminal-Categoryᵉ : is-gaunt-Categoryᵉ terminal-Categoryᵉ
is-gaunt-terminal-Categoryᵉ _ _ =
  is-prop-Σᵉ is-prop-unitᵉ (λ _ → is-prop-is-iso-Categoryᵉ terminal-Categoryᵉ starᵉ)

terminal-Gaunt-Categoryᵉ : Gaunt-Categoryᵉ lzero lzero
pr1ᵉ terminal-Gaunt-Categoryᵉ = terminal-Categoryᵉ
pr2ᵉ terminal-Gaunt-Categoryᵉ = is-gaunt-terminal-Categoryᵉ
```

### Points in categories

Usingᵉ theᵉ terminalᵉ categoryᵉ asᵉ theᵉ representingᵉ categoryᵉ ofᵉ objects,ᵉ weᵉ canᵉ
define,ᵉ givenᵉ anᵉ objectᵉ in aᵉ categoryᵉ `xᵉ ∈ᵉ C`,ᵉ theᵉ _pointᵉ_ atᵉ `x`ᵉ asᵉ theᵉ
[constantᵉ functor](category-theory.constant-functors.mdᵉ) fromᵉ theᵉ terminalᵉ
categoryᵉ to `C`ᵉ atᵉ `x`.ᵉ

```agda
point-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (xᵉ : obj-Precategoryᵉ Cᵉ) →
  functor-Precategoryᵉ terminal-Precategoryᵉ Cᵉ
point-Precategoryᵉ = constant-functor-Precategoryᵉ terminal-Precategoryᵉ

point-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (xᵉ : obj-Categoryᵉ Cᵉ) →
  functor-Categoryᵉ terminal-Categoryᵉ Cᵉ
point-Categoryᵉ Cᵉ = point-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

## Properties

### The terminal category represents objects

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-equiv-point-Precategoryᵉ : is-equivᵉ (point-Precategoryᵉ Cᵉ)
  is-equiv-point-Precategoryᵉ =
    is-equiv-is-invertibleᵉ
      ( λ Fᵉ → obj-functor-Precategoryᵉ terminal-Precategoryᵉ Cᵉ Fᵉ starᵉ)
      ( λ Fᵉ →
        eq-htpy-functor-Precategoryᵉ terminal-Precategoryᵉ Cᵉ _ Fᵉ
          ( ( refl-htpyᵉ) ,ᵉ
            ( λ _ →
              apᵉ
                ( λ fᵉ → comp-hom-Precategoryᵉ Cᵉ fᵉ (id-hom-Precategoryᵉ Cᵉ))
                ( preserves-id-functor-Precategoryᵉ terminal-Precategoryᵉ Cᵉ Fᵉ
                  ( starᵉ)))))
      ( refl-htpyᵉ)

  equiv-point-Precategoryᵉ :
    obj-Precategoryᵉ Cᵉ ≃ᵉ functor-Precategoryᵉ terminal-Precategoryᵉ Cᵉ
  pr1ᵉ equiv-point-Precategoryᵉ = point-Precategoryᵉ Cᵉ
  pr2ᵉ equiv-point-Precategoryᵉ = is-equiv-point-Precategoryᵉ

  inv-equiv-point-Precategoryᵉ :
    functor-Precategoryᵉ terminal-Precategoryᵉ Cᵉ ≃ᵉ obj-Precategoryᵉ Cᵉ
  inv-equiv-point-Precategoryᵉ = inv-equivᵉ equiv-point-Precategoryᵉ
```

Itᵉ remainsᵉ to showᵉ functorialityᵉ ofᵉ `point-Precategory`.ᵉ

### The terminal category is terminal

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  terminal-functor-Precategoryᵉ : functor-Precategoryᵉ Cᵉ terminal-Precategoryᵉ
  terminal-functor-Precategoryᵉ =
    constant-functor-Precategoryᵉ Cᵉ terminal-Precategoryᵉ starᵉ

  uniqueness-terminal-functor-Precategoryᵉ :
    (Fᵉ : functor-Precategoryᵉ Cᵉ terminal-Precategoryᵉ) →
    terminal-functor-Precategoryᵉ ＝ᵉ Fᵉ
  uniqueness-terminal-functor-Precategoryᵉ Fᵉ =
    eq-htpy-functor-Precategoryᵉ
      ( Cᵉ)
      ( terminal-Precategoryᵉ)
      ( terminal-functor-Precategoryᵉ)
      ( Fᵉ)
      ( refl-htpyᵉ ,ᵉ refl-htpyᵉ)

  is-contr-functor-terminal-Precategoryᵉ :
    is-contrᵉ (functor-Precategoryᵉ Cᵉ terminal-Precategoryᵉ)
  pr1ᵉ is-contr-functor-terminal-Precategoryᵉ =
    terminal-functor-Precategoryᵉ
  pr2ᵉ is-contr-functor-terminal-Precategoryᵉ =
    uniqueness-terminal-functor-Precategoryᵉ
```

## See also

-ᵉ [Theᵉ initialᵉ category](category-theory.initial-category.mdᵉ)

## External links

-ᵉ [Terminalᵉ category](https://1lab.dev/Cat.Instances.Shape.Terminal.htmlᵉ) atᵉ
  1labᵉ
-ᵉ [Terminalᵉ category](https://ncatlab.org/nlab/show/terminal+categoryᵉ) atᵉ $n$Labᵉ

Aᵉ wikidataᵉ identifierᵉ wasᵉ notᵉ availableᵉ forᵉ thisᵉ concept.ᵉ