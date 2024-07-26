# Congruence relations on abelian groups

```agda
module group-theory.congruence-relations-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.congruence-relations-groupsᵉ
```

</details>

## Idea

Aᵉ congruenceᵉ relationᵉ onᵉ anᵉ abelianᵉ groupᵉ `A`ᵉ isᵉ aᵉ congruenceᵉ relationᵉ onᵉ theᵉ
underlyingᵉ groupᵉ ofᵉ `A`.ᵉ

## Definition

```agda
is-congruence-Abᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) →
  equivalence-relationᵉ l2ᵉ (type-Abᵉ Aᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-congruence-Abᵉ Aᵉ = is-congruence-Groupᵉ (group-Abᵉ Aᵉ)

congruence-Abᵉ : {lᵉ : Level} (l2ᵉ : Level) (Aᵉ : Abᵉ lᵉ) → UUᵉ (lᵉ ⊔ lsuc l2ᵉ)
congruence-Abᵉ l2ᵉ Aᵉ = congruence-Groupᵉ l2ᵉ (group-Abᵉ Aᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Rᵉ : congruence-Abᵉ l2ᵉ Aᵉ)
  where

  equivalence-relation-congruence-Abᵉ : equivalence-relationᵉ l2ᵉ (type-Abᵉ Aᵉ)
  equivalence-relation-congruence-Abᵉ =
    equivalence-relation-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  prop-congruence-Abᵉ : Relation-Propᵉ l2ᵉ (type-Abᵉ Aᵉ)
  prop-congruence-Abᵉ = prop-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  sim-congruence-Abᵉ : (xᵉ yᵉ : type-Abᵉ Aᵉ) → UUᵉ l2ᵉ
  sim-congruence-Abᵉ = sim-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  is-prop-sim-congruence-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) → is-propᵉ (sim-congruence-Abᵉ xᵉ yᵉ)
  is-prop-sim-congruence-Abᵉ =
    is-prop-sim-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  concatenate-eq-sim-congruence-Abᵉ :
    {x1ᵉ x2ᵉ yᵉ : type-Abᵉ Aᵉ} →
    x1ᵉ ＝ᵉ x2ᵉ → sim-congruence-Abᵉ x2ᵉ yᵉ → sim-congruence-Abᵉ x1ᵉ yᵉ
  concatenate-eq-sim-congruence-Abᵉ =
    concatenate-eq-sim-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  concatenate-sim-eq-congruence-Abᵉ :
    {xᵉ y1ᵉ y2ᵉ : type-Abᵉ Aᵉ} →
    sim-congruence-Abᵉ xᵉ y1ᵉ → y1ᵉ ＝ᵉ y2ᵉ → sim-congruence-Abᵉ xᵉ y2ᵉ
  concatenate-sim-eq-congruence-Abᵉ =
    concatenate-sim-eq-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  concatenate-eq-sim-eq-congruence-Abᵉ :
    {x1ᵉ x2ᵉ y1ᵉ y2ᵉ : type-Abᵉ Aᵉ} → x1ᵉ ＝ᵉ x2ᵉ →
    sim-congruence-Abᵉ x2ᵉ y1ᵉ →
    y1ᵉ ＝ᵉ y2ᵉ → sim-congruence-Abᵉ x1ᵉ y2ᵉ
  concatenate-eq-sim-eq-congruence-Abᵉ =
    concatenate-eq-sim-eq-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  refl-congruence-Abᵉ : is-reflexiveᵉ sim-congruence-Abᵉ
  refl-congruence-Abᵉ = refl-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  symmetric-congruence-Abᵉ : is-symmetricᵉ sim-congruence-Abᵉ
  symmetric-congruence-Abᵉ = symmetric-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  equiv-symmetric-congruence-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    sim-congruence-Abᵉ xᵉ yᵉ ≃ᵉ sim-congruence-Abᵉ yᵉ xᵉ
  equiv-symmetric-congruence-Abᵉ =
    equiv-symmetric-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  transitive-congruence-Abᵉ :
    is-transitiveᵉ sim-congruence-Abᵉ
  transitive-congruence-Abᵉ = transitive-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  add-congruence-Abᵉ : is-congruence-Abᵉ Aᵉ equivalence-relation-congruence-Abᵉ
  add-congruence-Abᵉ = mul-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  left-add-congruence-Abᵉ :
    (xᵉ : type-Abᵉ Aᵉ) {yᵉ zᵉ : type-Abᵉ Aᵉ} →
    sim-congruence-Abᵉ yᵉ zᵉ →
    sim-congruence-Abᵉ (add-Abᵉ Aᵉ xᵉ yᵉ) (add-Abᵉ Aᵉ xᵉ zᵉ)
  left-add-congruence-Abᵉ = left-mul-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  right-add-congruence-Abᵉ :
    {xᵉ yᵉ : type-Abᵉ Aᵉ} → sim-congruence-Abᵉ xᵉ yᵉ →
    (zᵉ : type-Abᵉ Aᵉ) →
    sim-congruence-Abᵉ (add-Abᵉ Aᵉ xᵉ zᵉ) (add-Abᵉ Aᵉ yᵉ zᵉ)
  right-add-congruence-Abᵉ = right-mul-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  conjugation-congruence-Abᵉ :
    (xᵉ : type-Abᵉ Aᵉ) {yᵉ zᵉ : type-Abᵉ Aᵉ} → sim-congruence-Abᵉ yᵉ zᵉ →
    sim-congruence-Abᵉ (conjugation-Abᵉ Aᵉ xᵉ yᵉ) (conjugation-Abᵉ Aᵉ xᵉ zᵉ)
  conjugation-congruence-Abᵉ =
    conjugation-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  conjugation-congruence-Ab'ᵉ :
    (xᵉ : type-Abᵉ Aᵉ) {yᵉ zᵉ : type-Abᵉ Aᵉ} →
    sim-congruence-Abᵉ yᵉ zᵉ →
    sim-congruence-Abᵉ
      ( conjugation-Ab'ᵉ Aᵉ xᵉ yᵉ)
      ( conjugation-Ab'ᵉ Aᵉ xᵉ zᵉ)
  conjugation-congruence-Ab'ᵉ =
    conjugation-congruence-Group'ᵉ (group-Abᵉ Aᵉ) Rᵉ

  sim-right-subtraction-zero-congruence-Abᵉ : (xᵉ yᵉ : type-Abᵉ Aᵉ) → UUᵉ l2ᵉ
  sim-right-subtraction-zero-congruence-Abᵉ =
    sim-right-div-unit-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  map-sim-right-subtraction-zero-congruence-Abᵉ :
    {xᵉ yᵉ : type-Abᵉ Aᵉ} → sim-congruence-Abᵉ xᵉ yᵉ →
    sim-right-subtraction-zero-congruence-Abᵉ xᵉ yᵉ
  map-sim-right-subtraction-zero-congruence-Abᵉ =
    map-sim-right-div-unit-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  map-inv-sim-right-subtraction-zero-congruence-Abᵉ :
    {xᵉ yᵉ : type-Abᵉ Aᵉ} →
    sim-right-subtraction-zero-congruence-Abᵉ xᵉ yᵉ → sim-congruence-Abᵉ xᵉ yᵉ
  map-inv-sim-right-subtraction-zero-congruence-Abᵉ =
    map-inv-sim-right-div-unit-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  sim-left-subtraction-zero-congruence-Abᵉ : (xᵉ yᵉ : type-Abᵉ Aᵉ) → UUᵉ l2ᵉ
  sim-left-subtraction-zero-congruence-Abᵉ =
    sim-left-div-unit-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  map-sim-left-subtraction-zero-congruence-Abᵉ :
    {xᵉ yᵉ : type-Abᵉ Aᵉ} → sim-congruence-Abᵉ xᵉ yᵉ →
    sim-left-subtraction-zero-congruence-Abᵉ xᵉ yᵉ
  map-sim-left-subtraction-zero-congruence-Abᵉ =
    map-sim-left-div-unit-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  map-inv-sim-left-subtraction-zero-congruence-Abᵉ :
    {xᵉ yᵉ : type-Abᵉ Aᵉ} → sim-left-subtraction-zero-congruence-Abᵉ xᵉ yᵉ →
    sim-congruence-Abᵉ xᵉ yᵉ
  map-inv-sim-left-subtraction-zero-congruence-Abᵉ =
    map-inv-sim-left-div-unit-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  neg-congruence-Abᵉ :
    {xᵉ yᵉ : type-Abᵉ Aᵉ} → sim-congruence-Abᵉ xᵉ yᵉ →
    sim-congruence-Abᵉ (neg-Abᵉ Aᵉ xᵉ) (neg-Abᵉ Aᵉ yᵉ)
  neg-congruence-Abᵉ = inv-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ
```

## Properties

### Characterizing equality of congruence relations on groups

```agda
relate-same-elements-congruence-Abᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) →
  congruence-Abᵉ l2ᵉ Aᵉ → congruence-Abᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
relate-same-elements-congruence-Abᵉ Aᵉ =
  relate-same-elements-congruence-Groupᵉ (group-Abᵉ Aᵉ)

refl-relate-same-elements-congruence-Abᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Rᵉ : congruence-Abᵉ l2ᵉ Aᵉ) →
  relate-same-elements-congruence-Abᵉ Aᵉ Rᵉ Rᵉ
refl-relate-same-elements-congruence-Abᵉ Aᵉ =
  refl-relate-same-elements-congruence-Groupᵉ (group-Abᵉ Aᵉ)

is-torsorial-relate-same-elements-congruence-Abᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Rᵉ : congruence-Abᵉ l2ᵉ Aᵉ) →
  is-torsorialᵉ (relate-same-elements-congruence-Abᵉ Aᵉ Rᵉ)
is-torsorial-relate-same-elements-congruence-Abᵉ Aᵉ =
  is-torsorial-relate-same-elements-congruence-Groupᵉ (group-Abᵉ Aᵉ)

relate-same-elements-eq-congruence-Abᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Abᵉ l2ᵉ Aᵉ) →
  Rᵉ ＝ᵉ Sᵉ → relate-same-elements-congruence-Abᵉ Aᵉ Rᵉ Sᵉ
relate-same-elements-eq-congruence-Abᵉ Aᵉ =
  relate-same-elements-eq-congruence-Groupᵉ (group-Abᵉ Aᵉ)

is-equiv-relate-same-elements-eq-congruence-Abᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Abᵉ l2ᵉ Aᵉ) →
  is-equivᵉ (relate-same-elements-eq-congruence-Abᵉ Aᵉ Rᵉ Sᵉ)
is-equiv-relate-same-elements-eq-congruence-Abᵉ Aᵉ =
  is-equiv-relate-same-elements-eq-congruence-Groupᵉ (group-Abᵉ Aᵉ)

extensionality-congruence-Abᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Abᵉ l2ᵉ Aᵉ) →
  (Rᵉ ＝ᵉ Sᵉ) ≃ᵉ relate-same-elements-congruence-Abᵉ Aᵉ Rᵉ Sᵉ
extensionality-congruence-Abᵉ Aᵉ =
  extensionality-congruence-Groupᵉ (group-Abᵉ Aᵉ)

eq-relate-same-elements-congruence-Abᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Abᵉ l2ᵉ Aᵉ) →
  relate-same-elements-congruence-Abᵉ Aᵉ Rᵉ Sᵉ → Rᵉ ＝ᵉ Sᵉ
eq-relate-same-elements-congruence-Abᵉ Aᵉ =
  eq-relate-same-elements-congruence-Groupᵉ (group-Abᵉ Aᵉ)
```