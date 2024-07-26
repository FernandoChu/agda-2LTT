# Congruence relations on rings

```agda
module ring-theory.congruence-relations-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.congruence-relations-abelian-groupsᵉ
open import group-theory.congruence-relations-monoidsᵉ

open import ring-theory.congruence-relations-semiringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Aᵉ congruenceᵉ relationᵉ onᵉ aᵉ ringᵉ `R`ᵉ isᵉ aᵉ congruenceᵉ relationᵉ onᵉ theᵉ underlyingᵉ
semiringᵉ ofᵉ `R`.ᵉ

## Definition

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  is-congruence-Ringᵉ :
    {l2ᵉ : Level} → congruence-Abᵉ l2ᵉ (ab-Ringᵉ Rᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-congruence-Ringᵉ = is-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  is-congruence-equivalence-relation-Ringᵉ :
    {l2ᵉ : Level} (Sᵉ : equivalence-relationᵉ l2ᵉ (type-Ringᵉ Rᵉ)) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-congruence-equivalence-relation-Ringᵉ Sᵉ =
    is-congruence-equivalence-relation-Semiringᵉ (semiring-Ringᵉ Rᵉ) Sᵉ

congruence-Ringᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Rᵉ : Ringᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
congruence-Ringᵉ l2ᵉ Rᵉ = congruence-Semiringᵉ l2ᵉ (semiring-Ringᵉ Rᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : congruence-Ringᵉ l2ᵉ Rᵉ)
  where

  congruence-ab-congruence-Ringᵉ : congruence-Abᵉ l2ᵉ (ab-Ringᵉ Rᵉ)
  congruence-ab-congruence-Ringᵉ =
    congruence-additive-monoid-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ) Sᵉ

  equivalence-relation-congruence-Ringᵉ : equivalence-relationᵉ l2ᵉ (type-Ringᵉ Rᵉ)
  equivalence-relation-congruence-Ringᵉ =
    equivalence-relation-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ) Sᵉ

  prop-congruence-Ringᵉ : Relation-Propᵉ l2ᵉ (type-Ringᵉ Rᵉ)
  prop-congruence-Ringᵉ = prop-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ) Sᵉ

  sim-congruence-Ringᵉ : (xᵉ yᵉ : type-Ringᵉ Rᵉ) → UUᵉ l2ᵉ
  sim-congruence-Ringᵉ = sim-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ) Sᵉ

  is-prop-sim-congruence-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) → is-propᵉ (sim-congruence-Ringᵉ xᵉ yᵉ)
  is-prop-sim-congruence-Ringᵉ =
    is-prop-sim-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ) Sᵉ

  concatenate-eq-sim-congruence-Ringᵉ :
    {x1ᵉ x2ᵉ yᵉ : type-Ringᵉ Rᵉ} →
    x1ᵉ ＝ᵉ x2ᵉ → sim-congruence-Ringᵉ x2ᵉ yᵉ → sim-congruence-Ringᵉ x1ᵉ yᵉ
  concatenate-eq-sim-congruence-Ringᵉ reflᵉ Hᵉ = Hᵉ

  concatenate-sim-eq-congruence-Ringᵉ :
    {xᵉ y1ᵉ y2ᵉ : type-Ringᵉ Rᵉ} →
    sim-congruence-Ringᵉ xᵉ y1ᵉ → y1ᵉ ＝ᵉ y2ᵉ → sim-congruence-Ringᵉ xᵉ y2ᵉ
  concatenate-sim-eq-congruence-Ringᵉ Hᵉ reflᵉ = Hᵉ

  concatenate-sim-eq-sim-congruence-Ringᵉ :
    {x1ᵉ x2ᵉ y1ᵉ y2ᵉ : type-Ringᵉ Rᵉ} →
    x1ᵉ ＝ᵉ x2ᵉ → sim-congruence-Ringᵉ x2ᵉ y1ᵉ →
    y1ᵉ ＝ᵉ y2ᵉ → sim-congruence-Ringᵉ x1ᵉ y2ᵉ
  concatenate-sim-eq-sim-congruence-Ringᵉ reflᵉ Hᵉ reflᵉ = Hᵉ

  refl-congruence-Ringᵉ :
    is-reflexive-Relation-Propᵉ prop-congruence-Ringᵉ
  refl-congruence-Ringᵉ = refl-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ) Sᵉ

  symmetric-congruence-Ringᵉ :
    is-symmetric-Relation-Propᵉ prop-congruence-Ringᵉ
  symmetric-congruence-Ringᵉ = symmetric-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ) Sᵉ

  equiv-symmetric-congruence-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    sim-congruence-Ringᵉ xᵉ yᵉ ≃ᵉ sim-congruence-Ringᵉ yᵉ xᵉ
  equiv-symmetric-congruence-Ringᵉ =
    equiv-symmetric-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ) Sᵉ

  transitive-congruence-Ringᵉ :
    is-transitive-Relation-Propᵉ prop-congruence-Ringᵉ
  transitive-congruence-Ringᵉ =
    transitive-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ) Sᵉ

  add-congruence-Ringᵉ :
    is-congruence-Abᵉ (ab-Ringᵉ Rᵉ) equivalence-relation-congruence-Ringᵉ
  add-congruence-Ringᵉ = add-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ) Sᵉ

  left-add-congruence-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) {yᵉ zᵉ : type-Ringᵉ Rᵉ} →
    sim-congruence-Ringᵉ yᵉ zᵉ →
    sim-congruence-Ringᵉ (add-Ringᵉ Rᵉ xᵉ yᵉ) (add-Ringᵉ Rᵉ xᵉ zᵉ)
  left-add-congruence-Ringᵉ =
    left-add-congruence-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( congruence-ab-congruence-Ringᵉ)

  right-add-congruence-Ringᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → sim-congruence-Ringᵉ xᵉ yᵉ →
    (zᵉ : type-Ringᵉ Rᵉ) →
    sim-congruence-Ringᵉ (add-Ringᵉ Rᵉ xᵉ zᵉ) (add-Ringᵉ Rᵉ yᵉ zᵉ)
  right-add-congruence-Ringᵉ =
    right-add-congruence-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( congruence-ab-congruence-Ringᵉ)

  sim-right-subtraction-zero-congruence-Ringᵉ : (xᵉ yᵉ : type-Ringᵉ Rᵉ) → UUᵉ l2ᵉ
  sim-right-subtraction-zero-congruence-Ringᵉ =
    sim-right-subtraction-zero-congruence-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( congruence-ab-congruence-Ringᵉ)

  map-sim-right-subtraction-zero-congruence-Ringᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → sim-congruence-Ringᵉ xᵉ yᵉ →
    sim-right-subtraction-zero-congruence-Ringᵉ xᵉ yᵉ
  map-sim-right-subtraction-zero-congruence-Ringᵉ =
    map-sim-right-subtraction-zero-congruence-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( congruence-ab-congruence-Ringᵉ)

  map-inv-sim-right-subtraction-zero-congruence-Ringᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} →
    sim-right-subtraction-zero-congruence-Ringᵉ xᵉ yᵉ → sim-congruence-Ringᵉ xᵉ yᵉ
  map-inv-sim-right-subtraction-zero-congruence-Ringᵉ =
    map-inv-sim-right-subtraction-zero-congruence-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( congruence-ab-congruence-Ringᵉ)

  sim-left-subtraction-zero-congruence-Ringᵉ : (xᵉ yᵉ : type-Ringᵉ Rᵉ) → UUᵉ l2ᵉ
  sim-left-subtraction-zero-congruence-Ringᵉ =
    sim-left-subtraction-zero-congruence-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( congruence-ab-congruence-Ringᵉ)

  map-sim-left-subtraction-zero-congruence-Ringᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → sim-congruence-Ringᵉ xᵉ yᵉ →
    sim-left-subtraction-zero-congruence-Ringᵉ xᵉ yᵉ
  map-sim-left-subtraction-zero-congruence-Ringᵉ =
    map-sim-left-subtraction-zero-congruence-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( congruence-ab-congruence-Ringᵉ)

  map-inv-sim-left-subtraction-zero-congruence-Ringᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → sim-left-subtraction-zero-congruence-Ringᵉ xᵉ yᵉ →
    sim-congruence-Ringᵉ xᵉ yᵉ
  map-inv-sim-left-subtraction-zero-congruence-Ringᵉ =
    map-inv-sim-left-subtraction-zero-congruence-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( congruence-ab-congruence-Ringᵉ)

  neg-congruence-Ringᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → sim-congruence-Ringᵉ xᵉ yᵉ →
    sim-congruence-Ringᵉ (neg-Ringᵉ Rᵉ xᵉ) (neg-Ringᵉ Rᵉ yᵉ)
  neg-congruence-Ringᵉ =
    neg-congruence-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( congruence-ab-congruence-Ringᵉ)

  mul-congruence-Ringᵉ :
    is-congruence-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( equivalence-relation-congruence-Ringᵉ)
  mul-congruence-Ringᵉ = pr2ᵉ Sᵉ

  left-mul-congruence-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) {yᵉ zᵉ : type-Ringᵉ Rᵉ} →
    sim-congruence-Ringᵉ yᵉ zᵉ →
    sim-congruence-Ringᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ) (mul-Ringᵉ Rᵉ xᵉ zᵉ)
  left-mul-congruence-Ringᵉ xᵉ Hᵉ =
    mul-congruence-Ringᵉ (refl-congruence-Ringᵉ xᵉ) Hᵉ

  right-mul-congruence-Ringᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → sim-congruence-Ringᵉ xᵉ yᵉ →
    (zᵉ : type-Ringᵉ Rᵉ) →
    sim-congruence-Ringᵉ (mul-Ringᵉ Rᵉ xᵉ zᵉ) (mul-Ringᵉ Rᵉ yᵉ zᵉ)
  right-mul-congruence-Ringᵉ Hᵉ zᵉ =
    mul-congruence-Ringᵉ Hᵉ (refl-congruence-Ringᵉ zᵉ)

construct-congruence-Ringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) →
  (Sᵉ : equivalence-relationᵉ l2ᵉ (type-Ringᵉ Rᵉ)) →
  is-congruence-Abᵉ (ab-Ringᵉ Rᵉ) Sᵉ →
  is-congruence-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ) Sᵉ →
  congruence-Ringᵉ l2ᵉ Rᵉ
pr1ᵉ (pr1ᵉ (construct-congruence-Ringᵉ Rᵉ Sᵉ Hᵉ Kᵉ)) = Sᵉ
pr2ᵉ (pr1ᵉ (construct-congruence-Ringᵉ Rᵉ Sᵉ Hᵉ Kᵉ)) = Hᵉ
pr2ᵉ (construct-congruence-Ringᵉ Rᵉ Sᵉ Hᵉ Kᵉ) = Kᵉ
```

## Properties

### Characterizing equality of congruence relations of rings

```agda
relate-same-elements-congruence-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) →
  congruence-Ringᵉ l2ᵉ Rᵉ → congruence-Ringᵉ l3ᵉ Rᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
relate-same-elements-congruence-Ringᵉ Rᵉ =
  relate-same-elements-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ)

refl-relate-same-elements-congruence-Ringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : congruence-Ringᵉ l2ᵉ Rᵉ) →
  relate-same-elements-congruence-Ringᵉ Rᵉ Sᵉ Sᵉ
refl-relate-same-elements-congruence-Ringᵉ Rᵉ =
  refl-relate-same-elements-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ)

is-torsorial-relate-same-elements-congruence-Ringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : congruence-Ringᵉ l2ᵉ Rᵉ) →
  is-torsorialᵉ (relate-same-elements-congruence-Ringᵉ Rᵉ Sᵉ)
is-torsorial-relate-same-elements-congruence-Ringᵉ Rᵉ =
  is-torsorial-relate-same-elements-congruence-Semiringᵉ
    ( semiring-Ringᵉ Rᵉ)

relate-same-elements-eq-congruence-Ringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ Tᵉ : congruence-Ringᵉ l2ᵉ Rᵉ) →
  Sᵉ ＝ᵉ Tᵉ → relate-same-elements-congruence-Ringᵉ Rᵉ Sᵉ Tᵉ
relate-same-elements-eq-congruence-Ringᵉ Rᵉ =
  relate-same-elements-eq-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ)

is-equiv-relate-same-elements-eq-congruence-Ringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ Tᵉ : congruence-Ringᵉ l2ᵉ Rᵉ) →
  is-equivᵉ (relate-same-elements-eq-congruence-Ringᵉ Rᵉ Sᵉ Tᵉ)
is-equiv-relate-same-elements-eq-congruence-Ringᵉ Rᵉ =
  is-equiv-relate-same-elements-eq-congruence-Semiringᵉ
    ( semiring-Ringᵉ Rᵉ)

extensionality-congruence-Ringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ Tᵉ : congruence-Ringᵉ l2ᵉ Rᵉ) →
  (Sᵉ ＝ᵉ Tᵉ) ≃ᵉ relate-same-elements-congruence-Ringᵉ Rᵉ Sᵉ Tᵉ
extensionality-congruence-Ringᵉ Rᵉ =
  extensionality-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ)

eq-relate-same-elements-congruence-Ringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ Tᵉ : congruence-Ringᵉ l2ᵉ Rᵉ) →
  relate-same-elements-congruence-Ringᵉ Rᵉ Sᵉ Tᵉ → Sᵉ ＝ᵉ Tᵉ
eq-relate-same-elements-congruence-Ringᵉ Rᵉ =
  eq-relate-same-elements-congruence-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```