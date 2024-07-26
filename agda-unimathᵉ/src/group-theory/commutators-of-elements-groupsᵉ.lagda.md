# Commutators of elements in groups

```agda
module group-theory.commutators-of-elements-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commuting-elements-groupsᵉ
open import group-theory.conjugationᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
```

</details>

## Idea

Theᵉ **commutator**ᵉ ofᵉ twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ ofᵉ aᵉ
[group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ definedᵉ to beᵉ theᵉ elementᵉ
`[x,yᵉ] = (xy)(yx)⁻¹`.ᵉ Theᵉ commutatorᵉ ofᵉ twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ isᵉ equalᵉ to theᵉ
unitᵉ ifᵉ andᵉ onlyᵉ ifᵉ `x`ᵉ andᵉ `y`ᵉ commute.ᵉ

## Definition

### The commutator operation

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  commutator-Groupᵉ : type-Groupᵉ Gᵉ → type-Groupᵉ Gᵉ → type-Groupᵉ Gᵉ
  commutator-Groupᵉ xᵉ yᵉ = right-div-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) (mul-Groupᵉ Gᵉ yᵉ xᵉ)
```

## Properties

### The commutator of `x` and `y` is the unit element if and only `x` and `y` commute

**Proof:**ᵉ Byᵉ transposingᵉ identificationsᵉ alongᵉ theᵉ groupᵉ operation,ᵉ weᵉ haveᵉ anᵉ
[equivalence](foundation.equivalences.mdᵉ) `(xyᵉ ＝ᵉ yxᵉ) ≃ᵉ ((xy)(yx)⁻¹ᵉ ＝ᵉ e)`.ᵉ

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  is-unit-commutator-commute-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    commute-Groupᵉ Gᵉ xᵉ yᵉ → is-unit-Groupᵉ Gᵉ (commutator-Groupᵉ Gᵉ xᵉ yᵉ)
  is-unit-commutator-commute-Groupᵉ xᵉ yᵉ Hᵉ =
    is-unit-right-div-eq-Groupᵉ Gᵉ Hᵉ

  commute-is-unit-commutator-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    is-unit-Groupᵉ Gᵉ (commutator-Groupᵉ Gᵉ xᵉ yᵉ) → commute-Groupᵉ Gᵉ xᵉ yᵉ
  commute-is-unit-commutator-Groupᵉ xᵉ yᵉ Hᵉ =
    eq-is-unit-right-div-Groupᵉ Gᵉ Hᵉ
```

### The inverse of the commutator `[x,y]` is `[y,x]`

**Proof:**ᵉ Sinceᵉ `(uv⁻¹)⁻¹ᵉ ＝ᵉ vu⁻¹`ᵉ forᵉ anyᵉ twoᵉ elementsᵉ `u,vᵉ : G`ᵉ itᵉ followsᵉ
thatᵉ `((xy)(yx)⁻¹)⁻¹ᵉ ＝ᵉ (yx)(xy)⁻¹`.ᵉ

```agda
  inv-commutator-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    inv-Groupᵉ Gᵉ (commutator-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ commutator-Groupᵉ Gᵉ yᵉ xᵉ
  inv-commutator-Groupᵉ xᵉ yᵉ =
    inv-right-div-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) (mul-Groupᵉ Gᵉ yᵉ xᵉ)
```

### Conjugation distributes over the commutator

**Proof:**ᵉ Theᵉ proofᵉ isᵉ aᵉ simpleᵉ computation,ᵉ using theᵉ factᵉ thatᵉ conjugationᵉ
distributesᵉ overᵉ multiplicationᵉ andᵉ preservesᵉ inversesᵉ:

```text
  u(xy)(yx)⁻¹u⁻¹ᵉ
  ＝ᵉ u(xy)u⁻¹u(yx)⁻¹u⁻¹ᵉ
  ＝ᵉ ((uxu⁻¹)(uyu⁻¹))(u(yx)u⁻¹)⁻¹ᵉ
  ＝ᵉ ((uxu⁻¹)(uyu⁻¹))((uyu⁻¹)(uxu⁻¹))⁻¹.ᵉ
```

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  distributive-conjugation-commutator-Groupᵉ :
    (uᵉ xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    conjugation-Groupᵉ Gᵉ uᵉ (commutator-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    commutator-Groupᵉ Gᵉ (conjugation-Groupᵉ Gᵉ uᵉ xᵉ) (conjugation-Groupᵉ Gᵉ uᵉ yᵉ)
  distributive-conjugation-commutator-Groupᵉ uᵉ xᵉ yᵉ =
    ( distributive-conjugation-mul-Groupᵉ Gᵉ uᵉ _ _) ∙ᵉ
    ( ap-mul-Groupᵉ Gᵉ
      ( distributive-conjugation-mul-Groupᵉ Gᵉ uᵉ xᵉ yᵉ)
      ( ( conjugation-inv-Groupᵉ Gᵉ uᵉ _) ∙ᵉ
        ( apᵉ (inv-Groupᵉ Gᵉ) (distributive-conjugation-mul-Groupᵉ Gᵉ uᵉ yᵉ xᵉ))))
```

### Group homomorphisms preserve commutators

**Proof:**ᵉ Considerᵉ aᵉ [groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ)
`fᵉ : Gᵉ → H`ᵉ andᵉ twoᵉ elementsᵉ `xᵉ yᵉ : G`.ᵉ Thenᵉ weᵉ calculateᵉ

```text
  f([x,yᵉ]) ≐ᵉ f((xy)(yx)⁻¹ᵉ)
           = f(xy)f(yx)⁻¹ᵉ
           = (f(x)f(y))(f(y)f(x))⁻¹ᵉ
           ≐ᵉ [f(x),f(y)].ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  preserves-commutator-hom-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (commutator-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    commutator-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ) (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ yᵉ)
  preserves-commutator-hom-Groupᵉ =
    ( preserves-right-div-hom-Groupᵉ Gᵉ Hᵉ fᵉ) ∙ᵉ
    ( ap-right-div-Groupᵉ Hᵉ
      ( preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
      ( preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ))
```

## External links

-ᵉ [Commutator](https://www.wikidata.org/wiki/Q2989763ᵉ) atᵉ Wikidataᵉ
-ᵉ [Commutator](https://en.wikipedia.org/wiki/Commutator#Group_theoryᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [Commutator](https://mathworld.wolfram.com/Commutator.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ
-ᵉ [Groupᵉ commutator](https://ncatlab.org/nlab/show/group+commutatorᵉ) atᵉ $n$Labᵉ