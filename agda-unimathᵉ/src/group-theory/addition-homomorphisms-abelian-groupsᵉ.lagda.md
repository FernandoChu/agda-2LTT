# Pointwise addition of morphisms of abelian groups

```agda
module group-theory.addition-homomorphisms-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-abelian-groupsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Morphismsᵉ ofᵉ abelianᵉ groupsᵉ canᵉ beᵉ addedᵉ pointwise.ᵉ Thisᵉ operationᵉ turnsᵉ eachᵉ
hom-setᵉ ofᵉ abelianᵉ groupsᵉ intoᵉ anᵉ abelianᵉ group.ᵉ Moreover,ᵉ compositionᵉ ofᵉ
abelianᵉ groupsᵉ distributesᵉ overᵉ additionᵉ fromᵉ theᵉ leftᵉ andᵉ fromᵉ theᵉ right.ᵉ

## Definition

### The abelian group of homomorphisms between two abelian groups

#### Pointwise operations on morphisms between abelian groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  add-hom-Abᵉ :
    hom-Abᵉ Aᵉ Bᵉ → hom-Abᵉ Aᵉ Bᵉ → hom-Abᵉ Aᵉ Bᵉ
  pr1ᵉ (add-hom-Abᵉ fᵉ gᵉ) xᵉ = add-Abᵉ Bᵉ (map-hom-Abᵉ Aᵉ Bᵉ fᵉ xᵉ) (map-hom-Abᵉ Aᵉ Bᵉ gᵉ xᵉ)
  pr2ᵉ (add-hom-Abᵉ fᵉ gᵉ) {xᵉ} {yᵉ} =
    ( ap-add-Abᵉ Bᵉ
      ( preserves-add-hom-Abᵉ Aᵉ Bᵉ fᵉ)
      ( preserves-add-hom-Abᵉ Aᵉ Bᵉ gᵉ)) ∙ᵉ
    ( interchange-add-add-Abᵉ Bᵉ
      ( map-hom-Abᵉ Aᵉ Bᵉ fᵉ xᵉ)
      ( map-hom-Abᵉ Aᵉ Bᵉ fᵉ yᵉ)
      ( map-hom-Abᵉ Aᵉ Bᵉ gᵉ xᵉ)
      ( map-hom-Abᵉ Aᵉ Bᵉ gᵉ yᵉ))

  zero-hom-Abᵉ : hom-Abᵉ Aᵉ Bᵉ
  pr1ᵉ zero-hom-Abᵉ xᵉ = zero-Abᵉ Bᵉ
  pr2ᵉ zero-hom-Abᵉ = invᵉ (left-unit-law-add-Abᵉ Bᵉ (zero-Abᵉ Bᵉ))

  neg-hom-Abᵉ : hom-Abᵉ Aᵉ Bᵉ → hom-Abᵉ Aᵉ Bᵉ
  pr1ᵉ (neg-hom-Abᵉ fᵉ) xᵉ = neg-Abᵉ Bᵉ (map-hom-Abᵉ Aᵉ Bᵉ fᵉ xᵉ)
  pr2ᵉ (neg-hom-Abᵉ fᵉ) {xᵉ} {yᵉ} =
    ( apᵉ (neg-Abᵉ Bᵉ) (preserves-add-hom-Abᵉ Aᵉ Bᵉ fᵉ)) ∙ᵉ
    ( distributive-neg-add-Abᵉ Bᵉ (map-hom-Abᵉ Aᵉ Bᵉ fᵉ xᵉ) (map-hom-Abᵉ Aᵉ Bᵉ fᵉ yᵉ))
```

#### Associativity of pointwise addition of morphisms of abelian groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  associative-add-hom-Abᵉ :
    (fᵉ gᵉ hᵉ : hom-Abᵉ Aᵉ Bᵉ) →
    add-hom-Abᵉ Aᵉ Bᵉ (add-hom-Abᵉ Aᵉ Bᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    add-hom-Abᵉ Aᵉ Bᵉ fᵉ (add-hom-Abᵉ Aᵉ Bᵉ gᵉ hᵉ)
  associative-add-hom-Abᵉ fᵉ gᵉ hᵉ =
    eq-htpy-hom-Abᵉ Aᵉ Bᵉ
      ( λ xᵉ →
        associative-add-Abᵉ Bᵉ
          ( map-hom-Abᵉ Aᵉ Bᵉ fᵉ xᵉ)
          ( map-hom-Abᵉ Aᵉ Bᵉ gᵉ xᵉ)
          ( map-hom-Abᵉ Aᵉ Bᵉ hᵉ xᵉ))
```

#### Commutativity of pointwise addition of morphisms of abelian groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  commutative-add-hom-Abᵉ :
    (fᵉ gᵉ : hom-Abᵉ Aᵉ Bᵉ) → add-hom-Abᵉ Aᵉ Bᵉ fᵉ gᵉ ＝ᵉ add-hom-Abᵉ Aᵉ Bᵉ gᵉ fᵉ
  commutative-add-hom-Abᵉ fᵉ gᵉ =
    eq-htpy-hom-Abᵉ Aᵉ Bᵉ
      ( λ xᵉ → commutative-add-Abᵉ Bᵉ (map-hom-Abᵉ Aᵉ Bᵉ fᵉ xᵉ) (map-hom-Abᵉ Aᵉ Bᵉ gᵉ xᵉ))
```

#### Unit laws for pointwise addition of morphisms of abelian groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  left-unit-law-add-hom-Abᵉ :
    (fᵉ : hom-Abᵉ Aᵉ Bᵉ) → add-hom-Abᵉ Aᵉ Bᵉ (zero-hom-Abᵉ Aᵉ Bᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-add-hom-Abᵉ fᵉ =
    eq-htpy-hom-Abᵉ Aᵉ Bᵉ (λ xᵉ → left-unit-law-add-Abᵉ Bᵉ (map-hom-Abᵉ Aᵉ Bᵉ fᵉ xᵉ))

  right-unit-law-add-hom-Abᵉ :
    (fᵉ : hom-Abᵉ Aᵉ Bᵉ) → add-hom-Abᵉ Aᵉ Bᵉ fᵉ (zero-hom-Abᵉ Aᵉ Bᵉ) ＝ᵉ fᵉ
  right-unit-law-add-hom-Abᵉ fᵉ =
    eq-htpy-hom-Abᵉ Aᵉ Bᵉ (λ xᵉ → right-unit-law-add-Abᵉ Bᵉ (map-hom-Abᵉ Aᵉ Bᵉ fᵉ xᵉ))
```

#### Inverse laws for pointwise addition of morphisms of abelian groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  left-inverse-law-add-hom-Abᵉ :
    (fᵉ : hom-Abᵉ Aᵉ Bᵉ) →
    add-hom-Abᵉ Aᵉ Bᵉ (neg-hom-Abᵉ Aᵉ Bᵉ fᵉ) fᵉ ＝ᵉ zero-hom-Abᵉ Aᵉ Bᵉ
  left-inverse-law-add-hom-Abᵉ fᵉ =
    eq-htpy-hom-Abᵉ Aᵉ Bᵉ (λ xᵉ → left-inverse-law-add-Abᵉ Bᵉ (map-hom-Abᵉ Aᵉ Bᵉ fᵉ xᵉ))

  right-inverse-law-add-hom-Abᵉ :
    (fᵉ : hom-Abᵉ Aᵉ Bᵉ) →
    add-hom-Abᵉ Aᵉ Bᵉ fᵉ (neg-hom-Abᵉ Aᵉ Bᵉ fᵉ) ＝ᵉ zero-hom-Abᵉ Aᵉ Bᵉ
  right-inverse-law-add-hom-Abᵉ fᵉ =
    eq-htpy-hom-Abᵉ Aᵉ Bᵉ (λ xᵉ → right-inverse-law-add-Abᵉ Bᵉ (map-hom-Abᵉ Aᵉ Bᵉ fᵉ xᵉ))
```

#### `hom G H` is an abelian group

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  semigroup-hom-Abᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ semigroup-hom-Abᵉ = hom-set-Abᵉ Aᵉ Bᵉ
  pr1ᵉ (pr2ᵉ semigroup-hom-Abᵉ) = add-hom-Abᵉ Aᵉ Bᵉ
  pr2ᵉ (pr2ᵉ semigroup-hom-Abᵉ) = associative-add-hom-Abᵉ Aᵉ Bᵉ

  group-hom-Abᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ group-hom-Abᵉ = semigroup-hom-Abᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ group-hom-Abᵉ)) = zero-hom-Abᵉ Aᵉ Bᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ group-hom-Abᵉ))) = left-unit-law-add-hom-Abᵉ Aᵉ Bᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ group-hom-Abᵉ))) = right-unit-law-add-hom-Abᵉ Aᵉ Bᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ group-hom-Abᵉ)) = neg-hom-Abᵉ Aᵉ Bᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ group-hom-Abᵉ))) = left-inverse-law-add-hom-Abᵉ Aᵉ Bᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ group-hom-Abᵉ))) = right-inverse-law-add-hom-Abᵉ Aᵉ Bᵉ

  ab-hom-Abᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ ab-hom-Abᵉ = group-hom-Abᵉ
  pr2ᵉ ab-hom-Abᵉ = commutative-add-hom-Abᵉ Aᵉ Bᵉ
```

## Properties

### Distributivity of composition over pointwise addition of morphisms of abelian groups

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ) (Cᵉ : Abᵉ l3ᵉ)
  where

  left-distributive-comp-add-hom-Abᵉ :
    (hᵉ : hom-Abᵉ Bᵉ Cᵉ) (fᵉ gᵉ : hom-Abᵉ Aᵉ Bᵉ) →
    comp-hom-Abᵉ Aᵉ Bᵉ Cᵉ hᵉ (add-hom-Abᵉ Aᵉ Bᵉ fᵉ gᵉ) ＝ᵉ
    add-hom-Abᵉ Aᵉ Cᵉ (comp-hom-Abᵉ Aᵉ Bᵉ Cᵉ hᵉ fᵉ) (comp-hom-Abᵉ Aᵉ Bᵉ Cᵉ hᵉ gᵉ)
  left-distributive-comp-add-hom-Abᵉ hᵉ fᵉ gᵉ =
    eq-htpy-hom-Abᵉ Aᵉ Cᵉ (λ xᵉ → preserves-add-hom-Abᵉ Bᵉ Cᵉ hᵉ)

  right-distributive-comp-add-hom-Abᵉ :
    (gᵉ hᵉ : hom-Abᵉ Bᵉ Cᵉ) (fᵉ : hom-Abᵉ Aᵉ Bᵉ) →
    comp-hom-Abᵉ Aᵉ Bᵉ Cᵉ (add-hom-Abᵉ Bᵉ Cᵉ gᵉ hᵉ) fᵉ ＝ᵉ
    add-hom-Abᵉ Aᵉ Cᵉ (comp-hom-Abᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ) (comp-hom-Abᵉ Aᵉ Bᵉ Cᵉ hᵉ fᵉ)
  right-distributive-comp-add-hom-Abᵉ gᵉ hᵉ fᵉ =
    eq-htpy-hom-Abᵉ Aᵉ Cᵉ (λ xᵉ → reflᵉ)
```

### Evaluation at an element is a group homomorphism `hom A B → A`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ) (aᵉ : type-Abᵉ Aᵉ)
  where

  ev-element-hom-Abᵉ : hom-Abᵉ Aᵉ Bᵉ → type-Abᵉ Bᵉ
  ev-element-hom-Abᵉ fᵉ = map-hom-Abᵉ Aᵉ Bᵉ fᵉ aᵉ

  preserves-add-ev-element-hom-Abᵉ :
    (fᵉ gᵉ : hom-Abᵉ Aᵉ Bᵉ) →
    ev-element-hom-Abᵉ (add-hom-Abᵉ Aᵉ Bᵉ fᵉ gᵉ) ＝ᵉ
    add-Abᵉ Bᵉ (ev-element-hom-Abᵉ fᵉ) (ev-element-hom-Abᵉ gᵉ)
  preserves-add-ev-element-hom-Abᵉ fᵉ gᵉ = reflᵉ

  hom-ev-element-hom-Abᵉ : hom-Abᵉ (ab-hom-Abᵉ Aᵉ Bᵉ) Bᵉ
  pr1ᵉ hom-ev-element-hom-Abᵉ = ev-element-hom-Abᵉ
  pr2ᵉ hom-ev-element-hom-Abᵉ {xᵉ} {yᵉ} = preserves-add-ev-element-hom-Abᵉ xᵉ yᵉ
```