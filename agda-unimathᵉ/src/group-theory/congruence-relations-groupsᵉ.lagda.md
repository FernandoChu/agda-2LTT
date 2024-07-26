# Congruence relations on groups

```agda
module group-theory.congruence-relations-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.binary-transportᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.congruence-relations-semigroupsᵉ
open import group-theory.conjugationᵉ
open import group-theory.groupsᵉ
```

</details>

## Idea

Aᵉ congruenceᵉ relationᵉ onᵉ aᵉ groupᵉ `G`ᵉ isᵉ anᵉ equivalenceᵉ relationᵉ `≡`ᵉ onᵉ `G`ᵉ suchᵉ
thatᵉ forᵉ everyᵉ `x1ᵉ x2ᵉ y1ᵉ y2ᵉ : G`ᵉ suchᵉ thatᵉ `x1ᵉ ≡ᵉ x2`ᵉ andᵉ `y1ᵉ ≡ᵉ y2`ᵉ weᵉ haveᵉ
`x1ᵉ ·ᵉ y1ᵉ ≡ᵉ x2ᵉ ·ᵉ y2`.ᵉ

## Definition

```agda
is-congruence-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  equivalence-relationᵉ l2ᵉ (type-Groupᵉ Gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-congruence-Groupᵉ Gᵉ Rᵉ =
  is-congruence-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) Rᵉ

congruence-Groupᵉ :
  {lᵉ : Level} (l2ᵉ : Level) (Gᵉ : Groupᵉ lᵉ) → UUᵉ (lᵉ ⊔ lsuc l2ᵉ)
congruence-Groupᵉ l2ᵉ Gᵉ =
  Σᵉ (equivalence-relationᵉ l2ᵉ (type-Groupᵉ Gᵉ)) (is-congruence-Groupᵉ Gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Rᵉ : congruence-Groupᵉ l2ᵉ Gᵉ)
  where

  equivalence-relation-congruence-Groupᵉ : equivalence-relationᵉ l2ᵉ (type-Groupᵉ Gᵉ)
  equivalence-relation-congruence-Groupᵉ = pr1ᵉ Rᵉ

  prop-congruence-Groupᵉ : Relation-Propᵉ l2ᵉ (type-Groupᵉ Gᵉ)
  prop-congruence-Groupᵉ =
    prop-equivalence-relationᵉ equivalence-relation-congruence-Groupᵉ

  sim-congruence-Groupᵉ : (xᵉ yᵉ : type-Groupᵉ Gᵉ) → UUᵉ l2ᵉ
  sim-congruence-Groupᵉ =
    sim-equivalence-relationᵉ equivalence-relation-congruence-Groupᵉ

  is-prop-sim-congruence-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → is-propᵉ (sim-congruence-Groupᵉ xᵉ yᵉ)
  is-prop-sim-congruence-Groupᵉ =
    is-prop-sim-equivalence-relationᵉ equivalence-relation-congruence-Groupᵉ

  concatenate-eq-sim-congruence-Groupᵉ :
    {x1ᵉ x2ᵉ yᵉ : type-Groupᵉ Gᵉ} →
    x1ᵉ ＝ᵉ x2ᵉ → sim-congruence-Groupᵉ x2ᵉ yᵉ → sim-congruence-Groupᵉ x1ᵉ yᵉ
  concatenate-eq-sim-congruence-Groupᵉ reflᵉ Hᵉ = Hᵉ

  concatenate-sim-eq-congruence-Groupᵉ :
    {xᵉ y1ᵉ y2ᵉ : type-Groupᵉ Gᵉ} →
    sim-congruence-Groupᵉ xᵉ y1ᵉ → y1ᵉ ＝ᵉ y2ᵉ → sim-congruence-Groupᵉ xᵉ y2ᵉ
  concatenate-sim-eq-congruence-Groupᵉ Hᵉ reflᵉ = Hᵉ

  concatenate-eq-sim-eq-congruence-Groupᵉ :
    {x1ᵉ x2ᵉ y1ᵉ y2ᵉ : type-Groupᵉ Gᵉ} → x1ᵉ ＝ᵉ x2ᵉ →
    sim-congruence-Groupᵉ x2ᵉ y1ᵉ →
    y1ᵉ ＝ᵉ y2ᵉ → sim-congruence-Groupᵉ x1ᵉ y2ᵉ
  concatenate-eq-sim-eq-congruence-Groupᵉ reflᵉ Hᵉ reflᵉ = Hᵉ

  refl-congruence-Groupᵉ : is-reflexiveᵉ sim-congruence-Groupᵉ
  refl-congruence-Groupᵉ =
    refl-equivalence-relationᵉ equivalence-relation-congruence-Groupᵉ

  symmetric-congruence-Groupᵉ : is-symmetricᵉ sim-congruence-Groupᵉ
  symmetric-congruence-Groupᵉ =
    symmetric-equivalence-relationᵉ equivalence-relation-congruence-Groupᵉ

  equiv-symmetric-congruence-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    sim-congruence-Groupᵉ xᵉ yᵉ ≃ᵉ sim-congruence-Groupᵉ yᵉ xᵉ
  equiv-symmetric-congruence-Groupᵉ xᵉ yᵉ =
    equiv-symmetric-equivalence-relationᵉ equivalence-relation-congruence-Groupᵉ

  transitive-congruence-Groupᵉ :
    is-transitiveᵉ sim-congruence-Groupᵉ
  transitive-congruence-Groupᵉ =
    transitive-equivalence-relationᵉ equivalence-relation-congruence-Groupᵉ

  mul-congruence-Groupᵉ :
    is-congruence-Groupᵉ Gᵉ equivalence-relation-congruence-Groupᵉ
  mul-congruence-Groupᵉ = pr2ᵉ Rᵉ

  left-mul-congruence-Groupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) {yᵉ zᵉ : type-Groupᵉ Gᵉ} →
    sim-congruence-Groupᵉ yᵉ zᵉ →
    sim-congruence-Groupᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) (mul-Groupᵉ Gᵉ xᵉ zᵉ)
  left-mul-congruence-Groupᵉ xᵉ Hᵉ =
    mul-congruence-Groupᵉ (refl-congruence-Groupᵉ xᵉ) Hᵉ

  right-mul-congruence-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} → sim-congruence-Groupᵉ xᵉ yᵉ →
    (zᵉ : type-Groupᵉ Gᵉ) →
    sim-congruence-Groupᵉ (mul-Groupᵉ Gᵉ xᵉ zᵉ) (mul-Groupᵉ Gᵉ yᵉ zᵉ)
  right-mul-congruence-Groupᵉ Hᵉ zᵉ =
    mul-congruence-Groupᵉ Hᵉ (refl-congruence-Groupᵉ zᵉ)

  conjugation-congruence-Groupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) {yᵉ zᵉ : type-Groupᵉ Gᵉ} →
    sim-congruence-Groupᵉ yᵉ zᵉ →
    sim-congruence-Groupᵉ
      ( conjugation-Groupᵉ Gᵉ xᵉ yᵉ)
      ( conjugation-Groupᵉ Gᵉ xᵉ zᵉ)
  conjugation-congruence-Groupᵉ xᵉ Hᵉ =
    right-mul-congruence-Groupᵉ
      ( left-mul-congruence-Groupᵉ xᵉ Hᵉ) (inv-Groupᵉ Gᵉ xᵉ)

  conjugation-congruence-Group'ᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) {yᵉ zᵉ : type-Groupᵉ Gᵉ} →
    sim-congruence-Groupᵉ yᵉ zᵉ →
    sim-congruence-Groupᵉ
      ( conjugation-Group'ᵉ Gᵉ xᵉ yᵉ)
      ( conjugation-Group'ᵉ Gᵉ xᵉ zᵉ)
  conjugation-congruence-Group'ᵉ xᵉ Hᵉ =
    right-mul-congruence-Groupᵉ
      ( left-mul-congruence-Groupᵉ (inv-Groupᵉ Gᵉ xᵉ) Hᵉ)
      ( xᵉ)

  sim-right-div-unit-congruence-Groupᵉ : (xᵉ yᵉ : type-Groupᵉ Gᵉ) → UUᵉ l2ᵉ
  sim-right-div-unit-congruence-Groupᵉ xᵉ yᵉ =
    sim-congruence-Groupᵉ (right-div-Groupᵉ Gᵉ xᵉ yᵉ) (unit-Groupᵉ Gᵉ)

  map-sim-right-div-unit-congruence-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    sim-congruence-Groupᵉ xᵉ yᵉ → sim-right-div-unit-congruence-Groupᵉ xᵉ yᵉ
  map-sim-right-div-unit-congruence-Groupᵉ {xᵉ} {yᵉ} Hᵉ =
    concatenate-sim-eq-congruence-Groupᵉ
      ( right-mul-congruence-Groupᵉ Hᵉ (inv-Groupᵉ Gᵉ yᵉ))
      ( right-inverse-law-mul-Groupᵉ Gᵉ yᵉ)

  map-inv-sim-right-div-unit-congruence-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    sim-right-div-unit-congruence-Groupᵉ xᵉ yᵉ → sim-congruence-Groupᵉ xᵉ yᵉ
  map-inv-sim-right-div-unit-congruence-Groupᵉ {xᵉ} {yᵉ} Hᵉ =
    concatenate-eq-sim-eq-congruence-Groupᵉ
      ( invᵉ
        ( ( associative-mul-Groupᵉ Gᵉ xᵉ (inv-Groupᵉ Gᵉ yᵉ) yᵉ) ∙ᵉ
          ( apᵉ (mul-Groupᵉ Gᵉ xᵉ) (left-inverse-law-mul-Groupᵉ Gᵉ yᵉ)) ∙ᵉ
          ( right-unit-law-mul-Groupᵉ Gᵉ xᵉ)))
      ( right-mul-congruence-Groupᵉ Hᵉ yᵉ)
      ( left-unit-law-mul-Groupᵉ Gᵉ yᵉ)

  sim-left-div-unit-congruence-Groupᵉ : (xᵉ yᵉ : type-Groupᵉ Gᵉ) → UUᵉ l2ᵉ
  sim-left-div-unit-congruence-Groupᵉ xᵉ yᵉ =
    sim-congruence-Groupᵉ (left-div-Groupᵉ Gᵉ xᵉ yᵉ) (unit-Groupᵉ Gᵉ)

  map-sim-left-div-unit-congruence-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    sim-congruence-Groupᵉ xᵉ yᵉ → sim-left-div-unit-congruence-Groupᵉ xᵉ yᵉ
  map-sim-left-div-unit-congruence-Groupᵉ {xᵉ} {yᵉ} Hᵉ =
    symmetric-congruence-Groupᵉ
      (unit-Groupᵉ Gᵉ)
      (mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ) yᵉ)
      ( concatenate-eq-sim-congruence-Groupᵉ
        ( invᵉ (left-inverse-law-mul-Groupᵉ Gᵉ xᵉ))
        ( left-mul-congruence-Groupᵉ (inv-Groupᵉ Gᵉ xᵉ) Hᵉ))

  map-inv-sim-left-div-unit-congruence-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    sim-left-div-unit-congruence-Groupᵉ xᵉ yᵉ → sim-congruence-Groupᵉ xᵉ yᵉ
  map-inv-sim-left-div-unit-congruence-Groupᵉ {xᵉ} {yᵉ} Hᵉ =
    binary-trᵉ
      ( sim-congruence-Groupᵉ)
      ( right-unit-law-mul-Groupᵉ Gᵉ xᵉ)
      ( is-section-left-div-Groupᵉ Gᵉ xᵉ yᵉ)
      ( symmetric-congruence-Groupᵉ
        ( mul-Groupᵉ Gᵉ xᵉ (left-div-Groupᵉ Gᵉ xᵉ yᵉ))
        ( mul-Groupᵉ Gᵉ xᵉ (unit-Groupᵉ Gᵉ))
        ( left-mul-congruence-Groupᵉ xᵉ Hᵉ))

  inv-congruence-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    sim-congruence-Groupᵉ xᵉ yᵉ →
    sim-congruence-Groupᵉ (inv-Groupᵉ Gᵉ xᵉ) (inv-Groupᵉ Gᵉ yᵉ)
  inv-congruence-Groupᵉ {xᵉ} {yᵉ} Hᵉ =
    concatenate-eq-sim-eq-congruence-Groupᵉ
      ( invᵉ
        ( ( associative-mul-Groupᵉ Gᵉ
            ( inv-Groupᵉ Gᵉ xᵉ)
            ( yᵉ)
            ( inv-Groupᵉ Gᵉ yᵉ)) ∙ᵉ
          ( apᵉ
            ( mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ))
            ( right-inverse-law-mul-Groupᵉ Gᵉ yᵉ)) ∙ᵉ
          ( right-unit-law-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ))))
      ( symmetric-congruence-Groupᵉ _ _
        ( right-mul-congruence-Groupᵉ
          ( left-mul-congruence-Groupᵉ (inv-Groupᵉ Gᵉ xᵉ) Hᵉ)
          ( inv-Groupᵉ Gᵉ yᵉ)))
      ( ( apᵉ
          ( mul-Group'ᵉ Gᵉ (inv-Groupᵉ Gᵉ yᵉ))
          ( left-inverse-law-mul-Groupᵉ Gᵉ xᵉ)) ∙ᵉ
        ( left-unit-law-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ yᵉ)))
```

## Properties

### Characterizing equality of congruence relations on groups

```agda
relate-same-elements-congruence-Groupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  congruence-Groupᵉ l2ᵉ Gᵉ → congruence-Groupᵉ l3ᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
relate-same-elements-congruence-Groupᵉ Gᵉ =
  relate-same-elements-congruence-Semigroupᵉ (semigroup-Groupᵉ Gᵉ)

refl-relate-same-elements-congruence-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Rᵉ : congruence-Groupᵉ l2ᵉ Gᵉ) →
  relate-same-elements-congruence-Groupᵉ Gᵉ Rᵉ Rᵉ
refl-relate-same-elements-congruence-Groupᵉ Gᵉ =
  refl-relate-same-elements-congruence-Semigroupᵉ (semigroup-Groupᵉ Gᵉ)

is-torsorial-relate-same-elements-congruence-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Rᵉ : congruence-Groupᵉ l2ᵉ Gᵉ) →
  is-torsorialᵉ (relate-same-elements-congruence-Groupᵉ Gᵉ Rᵉ)
is-torsorial-relate-same-elements-congruence-Groupᵉ Gᵉ =
  is-torsorial-relate-same-elements-congruence-Semigroupᵉ
    ( semigroup-Groupᵉ Gᵉ)

relate-same-elements-eq-congruence-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Groupᵉ l2ᵉ Gᵉ) →
  Rᵉ ＝ᵉ Sᵉ → relate-same-elements-congruence-Groupᵉ Gᵉ Rᵉ Sᵉ
relate-same-elements-eq-congruence-Groupᵉ Gᵉ =
  relate-same-elements-eq-congruence-Semigroupᵉ (semigroup-Groupᵉ Gᵉ)

is-equiv-relate-same-elements-eq-congruence-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Groupᵉ l2ᵉ Gᵉ) →
  is-equivᵉ (relate-same-elements-eq-congruence-Groupᵉ Gᵉ Rᵉ Sᵉ)
is-equiv-relate-same-elements-eq-congruence-Groupᵉ Gᵉ =
  is-equiv-relate-same-elements-eq-congruence-Semigroupᵉ
    ( semigroup-Groupᵉ Gᵉ)

extensionality-congruence-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Groupᵉ l2ᵉ Gᵉ) →
  (Rᵉ ＝ᵉ Sᵉ) ≃ᵉ relate-same-elements-congruence-Groupᵉ Gᵉ Rᵉ Sᵉ
extensionality-congruence-Groupᵉ Gᵉ =
  extensionality-congruence-Semigroupᵉ (semigroup-Groupᵉ Gᵉ)

eq-relate-same-elements-congruence-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Groupᵉ l2ᵉ Gᵉ) →
  relate-same-elements-congruence-Groupᵉ Gᵉ Rᵉ Sᵉ → Rᵉ ＝ᵉ Sᵉ
eq-relate-same-elements-congruence-Groupᵉ Gᵉ =
  eq-relate-same-elements-congruence-Semigroupᵉ (semigroup-Groupᵉ Gᵉ)
```