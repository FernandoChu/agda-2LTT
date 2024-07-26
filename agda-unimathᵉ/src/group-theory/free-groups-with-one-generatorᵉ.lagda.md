# Free groups with one generator

```agda
module group-theory.free-groups-with-one-generatorᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.group-of-integersᵉ
open import elementary-number-theory.integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.integer-powers-of-elements-groupsᵉ

open import structured-types.initial-pointed-type-equipped-with-automorphismᵉ
```

</details>

## Idea

Aᵉ groupᵉ `F`ᵉ equippedᵉ with anᵉ elementᵉ `xᵉ : F`ᵉ isᵉ saidᵉ to satisfyᵉ theᵉ universalᵉ
propertyᵉ ofᵉ theᵉ freeᵉ groupᵉ with oneᵉ generatorᵉ ifᵉ forᵉ everyᵉ groupᵉ `G`ᵉ theᵉ mapᵉ

```text
  hom-Groupᵉ Fᵉ Gᵉ → type-Groupᵉ Gᵉ
```

givenᵉ byᵉ `hᵉ ↦ᵉ hᵉ x`ᵉ isᵉ anᵉ equivalence.ᵉ Theᵉ groupᵉ ofᵉ integersᵉ isᵉ aᵉ freeᵉ groupᵉ with
oneᵉ generator.ᵉ

## Definitions

```agda
ev-element-hom-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (gᵉ : type-Groupᵉ Gᵉ) →
  hom-Groupᵉ Gᵉ Hᵉ → type-Groupᵉ Hᵉ
ev-element-hom-Groupᵉ Gᵉ Hᵉ gᵉ fᵉ = map-hom-Groupᵉ Gᵉ Hᵉ fᵉ gᵉ

is-free-group-with-one-generatorᵉ :
  {l1ᵉ : Level} (Fᵉ : Groupᵉ l1ᵉ) (xᵉ : type-Groupᵉ Fᵉ) → UUωᵉ
is-free-group-with-one-generatorᵉ Fᵉ xᵉ =
  {l2ᵉ : Level} (Gᵉ : Groupᵉ l2ᵉ) → is-equivᵉ (ev-element-hom-Groupᵉ Fᵉ Gᵉ xᵉ)
```

## Properties

### The group of integers is the free group with one generator

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) (gᵉ : type-Groupᵉ Gᵉ)
  where

  map-hom-element-Groupᵉ : ℤᵉ → type-Groupᵉ Gᵉ
  map-hom-element-Groupᵉ kᵉ = integer-power-Groupᵉ Gᵉ kᵉ gᵉ

  preserves-unit-hom-element-Groupᵉ :
    map-hom-element-Groupᵉ zero-ℤᵉ ＝ᵉ unit-Groupᵉ Gᵉ
  preserves-unit-hom-element-Groupᵉ = integer-power-zero-Groupᵉ Gᵉ gᵉ

  preserves-mul-map-hom-element-Groupᵉ :
    (xᵉ yᵉ : ℤᵉ) →
    ( map-hom-element-Groupᵉ (xᵉ +ℤᵉ yᵉ)) ＝ᵉ
    ( mul-Groupᵉ Gᵉ (map-hom-element-Groupᵉ xᵉ) (map-hom-element-Groupᵉ yᵉ))
  preserves-mul-map-hom-element-Groupᵉ =
    distributive-integer-power-add-Groupᵉ Gᵉ gᵉ

  hom-element-Groupᵉ : hom-Groupᵉ ℤ-Groupᵉ Gᵉ
  pr1ᵉ hom-element-Groupᵉ = map-hom-element-Groupᵉ
  pr2ᵉ hom-element-Groupᵉ {xᵉ} {yᵉ} = preserves-mul-map-hom-element-Groupᵉ xᵉ yᵉ

  htpy-hom-element-Groupᵉ :
    (hᵉ : hom-Groupᵉ ℤ-Groupᵉ Gᵉ) → map-hom-Groupᵉ ℤ-Groupᵉ Gᵉ hᵉ one-ℤᵉ ＝ᵉ gᵉ →
    htpy-hom-Groupᵉ ℤ-Groupᵉ Gᵉ hom-element-Groupᵉ hᵉ
  htpy-hom-element-Groupᵉ hᵉ pᵉ =
    htpy-map-ℤ-Pointed-Type-With-Autᵉ
      ( pointed-type-Groupᵉ Gᵉ ,ᵉ equiv-mul-Groupᵉ Gᵉ gᵉ)
      ( pairᵉ
        ( map-hom-Groupᵉ ℤ-Groupᵉ Gᵉ hᵉ)
        ( pairᵉ
          ( preserves-unit-hom-Groupᵉ ℤ-Groupᵉ Gᵉ hᵉ)
          ( λ xᵉ →
            ( apᵉ
              ( map-hom-Groupᵉ ℤ-Groupᵉ Gᵉ hᵉ)
              ( is-left-add-one-succ-ℤᵉ xᵉ)) ∙ᵉ
            ( preserves-mul-hom-Groupᵉ ℤ-Groupᵉ Gᵉ hᵉ) ∙ᵉ
            ( apᵉ ( mul-Group'ᵉ Gᵉ (map-hom-Groupᵉ ℤ-Groupᵉ Gᵉ hᵉ xᵉ)) pᵉ))))

  is-torsorial-hom-element-Groupᵉ :
    is-torsorialᵉ (λ hᵉ → map-hom-Groupᵉ ℤ-Groupᵉ Gᵉ hᵉ one-ℤᵉ ＝ᵉ gᵉ)
  pr1ᵉ (pr1ᵉ is-torsorial-hom-element-Groupᵉ) =
    hom-element-Groupᵉ
  pr2ᵉ (pr1ᵉ is-torsorial-hom-element-Groupᵉ) =
    right-unit-law-mul-Groupᵉ Gᵉ gᵉ
  pr2ᵉ is-torsorial-hom-element-Groupᵉ (hᵉ ,ᵉ pᵉ) =
    eq-type-subtypeᵉ
      ( λ fᵉ → Id-Propᵉ (set-Groupᵉ Gᵉ) (map-hom-Groupᵉ ℤ-Groupᵉ Gᵉ fᵉ one-ℤᵉ) gᵉ)
      ( eq-htpy-hom-Groupᵉ ℤ-Groupᵉ Gᵉ
        ( htpy-hom-element-Groupᵉ hᵉ pᵉ))

abstract
  is-free-group-with-one-generator-ℤᵉ :
    is-free-group-with-one-generatorᵉ ℤ-Groupᵉ one-ℤᵉ
  is-free-group-with-one-generator-ℤᵉ Gᵉ =
    is-equiv-is-contr-mapᵉ (is-torsorial-hom-element-Groupᵉ Gᵉ)
```