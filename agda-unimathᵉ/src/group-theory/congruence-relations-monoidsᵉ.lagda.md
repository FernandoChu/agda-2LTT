# Congruence relations on monoids

```agda
module group-theory.congruence-relations-monoidsᵉ where
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

open import group-theory.congruence-relations-semigroupsᵉ
open import group-theory.monoidsᵉ
```

</details>

## Idea

Aᵉ congruenceᵉ relationᵉ onᵉ aᵉ monoidᵉ `M`ᵉ isᵉ aᵉ congruenceᵉ relationᵉ onᵉ theᵉ underlyingᵉ
semigroupᵉ ofᵉ `M`.ᵉ

## Definition

```agda
is-congruence-prop-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) →
  equivalence-relationᵉ l2ᵉ (type-Monoidᵉ Mᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-congruence-prop-Monoidᵉ Mᵉ = is-congruence-prop-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)

is-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) →
  equivalence-relationᵉ l2ᵉ (type-Monoidᵉ Mᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-congruence-Monoidᵉ Mᵉ Rᵉ =
  is-congruence-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ) Rᵉ

is-prop-is-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ)
  (Rᵉ : equivalence-relationᵉ l2ᵉ (type-Monoidᵉ Mᵉ)) →
  is-propᵉ (is-congruence-Monoidᵉ Mᵉ Rᵉ)
is-prop-is-congruence-Monoidᵉ Mᵉ =
  is-prop-is-congruence-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)

congruence-Monoidᵉ : {lᵉ : Level} (l2ᵉ : Level) (Mᵉ : Monoidᵉ lᵉ) → UUᵉ (lᵉ ⊔ lsuc l2ᵉ)
congruence-Monoidᵉ l2ᵉ Mᵉ =
  Σᵉ (equivalence-relationᵉ l2ᵉ (type-Monoidᵉ Mᵉ)) (is-congruence-Monoidᵉ Mᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ : congruence-Monoidᵉ l2ᵉ Mᵉ)
  where

  equivalence-relation-congruence-Monoidᵉ :
    equivalence-relationᵉ l2ᵉ (type-Monoidᵉ Mᵉ)
  equivalence-relation-congruence-Monoidᵉ = pr1ᵉ Rᵉ

  prop-congruence-Monoidᵉ : Relation-Propᵉ l2ᵉ (type-Monoidᵉ Mᵉ)
  prop-congruence-Monoidᵉ =
    prop-equivalence-relationᵉ equivalence-relation-congruence-Monoidᵉ

  sim-congruence-Monoidᵉ : (xᵉ yᵉ : type-Monoidᵉ Mᵉ) → UUᵉ l2ᵉ
  sim-congruence-Monoidᵉ =
    sim-equivalence-relationᵉ equivalence-relation-congruence-Monoidᵉ

  is-prop-sim-congruence-Monoidᵉ :
    (xᵉ yᵉ : type-Monoidᵉ Mᵉ) → is-propᵉ (sim-congruence-Monoidᵉ xᵉ yᵉ)
  is-prop-sim-congruence-Monoidᵉ =
    is-prop-sim-equivalence-relationᵉ equivalence-relation-congruence-Monoidᵉ

  concatenate-sim-eq-congruence-Monoidᵉ :
    {xᵉ yᵉ zᵉ : type-Monoidᵉ Mᵉ} → sim-congruence-Monoidᵉ xᵉ yᵉ → yᵉ ＝ᵉ zᵉ →
    sim-congruence-Monoidᵉ xᵉ zᵉ
  concatenate-sim-eq-congruence-Monoidᵉ Hᵉ reflᵉ = Hᵉ

  concatenate-eq-sim-congruence-Monoidᵉ :
    {xᵉ yᵉ zᵉ : type-Monoidᵉ Mᵉ} → xᵉ ＝ᵉ yᵉ → sim-congruence-Monoidᵉ yᵉ zᵉ →
    sim-congruence-Monoidᵉ xᵉ zᵉ
  concatenate-eq-sim-congruence-Monoidᵉ reflᵉ Hᵉ = Hᵉ

  concatenate-eq-sim-eq-congruence-Monoidᵉ :
    {xᵉ yᵉ zᵉ wᵉ : type-Monoidᵉ Mᵉ} → xᵉ ＝ᵉ yᵉ → sim-congruence-Monoidᵉ yᵉ zᵉ →
    zᵉ ＝ᵉ wᵉ → sim-congruence-Monoidᵉ xᵉ wᵉ
  concatenate-eq-sim-eq-congruence-Monoidᵉ reflᵉ Hᵉ reflᵉ = Hᵉ

  refl-congruence-Monoidᵉ : is-reflexiveᵉ sim-congruence-Monoidᵉ
  refl-congruence-Monoidᵉ =
    refl-equivalence-relationᵉ equivalence-relation-congruence-Monoidᵉ

  symmetric-congruence-Monoidᵉ : is-symmetricᵉ sim-congruence-Monoidᵉ
  symmetric-congruence-Monoidᵉ =
    symmetric-equivalence-relationᵉ equivalence-relation-congruence-Monoidᵉ

  equiv-symmetric-congruence-Monoidᵉ :
    (xᵉ yᵉ : type-Monoidᵉ Mᵉ) →
    sim-congruence-Monoidᵉ xᵉ yᵉ ≃ᵉ sim-congruence-Monoidᵉ yᵉ xᵉ
  equiv-symmetric-congruence-Monoidᵉ xᵉ yᵉ =
    equiv-symmetric-equivalence-relationᵉ equivalence-relation-congruence-Monoidᵉ

  transitive-congruence-Monoidᵉ : is-transitiveᵉ sim-congruence-Monoidᵉ
  transitive-congruence-Monoidᵉ =
    transitive-equivalence-relationᵉ equivalence-relation-congruence-Monoidᵉ

  mul-congruence-Monoidᵉ :
    is-congruence-Monoidᵉ Mᵉ equivalence-relation-congruence-Monoidᵉ
  mul-congruence-Monoidᵉ = pr2ᵉ Rᵉ
```

## Properties

### Extensionality of the type of congruence relations on a monoid

```agda
relate-same-elements-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ : congruence-Monoidᵉ l2ᵉ Mᵉ)
  (Sᵉ : congruence-Monoidᵉ l3ᵉ Mᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
relate-same-elements-congruence-Monoidᵉ Mᵉ =
  relate-same-elements-congruence-Semigroupᵉ
    ( semigroup-Monoidᵉ Mᵉ)

refl-relate-same-elements-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ : congruence-Monoidᵉ l2ᵉ Mᵉ) →
  relate-same-elements-congruence-Monoidᵉ Mᵉ Rᵉ Rᵉ
refl-relate-same-elements-congruence-Monoidᵉ Mᵉ =
  refl-relate-same-elements-congruence-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)

is-torsorial-relate-same-elements-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ : congruence-Monoidᵉ l2ᵉ Mᵉ) →
  is-torsorialᵉ (relate-same-elements-congruence-Monoidᵉ Mᵉ Rᵉ)
is-torsorial-relate-same-elements-congruence-Monoidᵉ Mᵉ =
  is-torsorial-relate-same-elements-congruence-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)

relate-same-elements-eq-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Monoidᵉ l2ᵉ Mᵉ) →
  Rᵉ ＝ᵉ Sᵉ → relate-same-elements-congruence-Monoidᵉ Mᵉ Rᵉ Sᵉ
relate-same-elements-eq-congruence-Monoidᵉ Mᵉ =
  relate-same-elements-eq-congruence-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)

is-equiv-relate-same-elements-eq-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Monoidᵉ l2ᵉ Mᵉ) →
  is-equivᵉ (relate-same-elements-eq-congruence-Monoidᵉ Mᵉ Rᵉ Sᵉ)
is-equiv-relate-same-elements-eq-congruence-Monoidᵉ Mᵉ =
  is-equiv-relate-same-elements-eq-congruence-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)

extensionality-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Monoidᵉ l2ᵉ Mᵉ) →
  (Rᵉ ＝ᵉ Sᵉ) ≃ᵉ relate-same-elements-congruence-Monoidᵉ Mᵉ Rᵉ Sᵉ
extensionality-congruence-Monoidᵉ Mᵉ =
  extensionality-congruence-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)

eq-relate-same-elements-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Monoidᵉ l2ᵉ Mᵉ) →
  relate-same-elements-congruence-Monoidᵉ Mᵉ Rᵉ Sᵉ → Rᵉ ＝ᵉ Sᵉ
eq-relate-same-elements-congruence-Monoidᵉ Mᵉ =
  eq-relate-same-elements-congruence-Semigroupᵉ
    ( semigroup-Monoidᵉ Mᵉ)
```