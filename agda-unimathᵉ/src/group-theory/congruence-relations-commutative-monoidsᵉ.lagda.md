# Congruence relations on commutative monoids

```agda
module group-theory.congruence-relations-commutative-monoidsᵉ where
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

open import group-theory.commutative-monoidsᵉ
open import group-theory.congruence-relations-monoidsᵉ
```

</details>

## Idea

Aᵉ congruenceᵉ relationᵉ onᵉ aᵉ commutativeᵉ monoidᵉ `M`ᵉ isᵉ aᵉ congruenceᵉ relationᵉ onᵉ
theᵉ underlyingᵉ monoidᵉ ofᵉ `M`.ᵉ

## Definition

```agda
is-congruence-prop-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ) →
  equivalence-relationᵉ l2ᵉ (type-Commutative-Monoidᵉ Mᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-congruence-prop-Commutative-Monoidᵉ Mᵉ =
  is-congruence-prop-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

is-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ) →
  equivalence-relationᵉ l2ᵉ (type-Commutative-Monoidᵉ Mᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-congruence-Commutative-Monoidᵉ Mᵉ =
  is-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

is-prop-is-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ : equivalence-relationᵉ l2ᵉ (type-Commutative-Monoidᵉ Mᵉ)) →
  is-propᵉ (is-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ)
is-prop-is-congruence-Commutative-Monoidᵉ Mᵉ =
  is-prop-is-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

congruence-Commutative-Monoidᵉ :
  {lᵉ : Level} (l2ᵉ : Level) (Mᵉ : Commutative-Monoidᵉ lᵉ) → UUᵉ (lᵉ ⊔ lsuc l2ᵉ)
congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ =
  congruence-Monoidᵉ l2ᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ : congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ)
  where

  equivalence-relation-congruence-Commutative-Monoidᵉ :
    equivalence-relationᵉ l2ᵉ (type-Commutative-Monoidᵉ Mᵉ)
  equivalence-relation-congruence-Commutative-Monoidᵉ =
    equivalence-relation-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Rᵉ

  prop-congruence-Commutative-Monoidᵉ :
    Relation-Propᵉ l2ᵉ (type-Commutative-Monoidᵉ Mᵉ)
  prop-congruence-Commutative-Monoidᵉ =
    prop-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Rᵉ

  sim-congruence-Commutative-Monoidᵉ : (xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ) → UUᵉ l2ᵉ
  sim-congruence-Commutative-Monoidᵉ =
    sim-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Rᵉ

  is-prop-sim-congruence-Commutative-Monoidᵉ :
    (xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ) →
    is-propᵉ (sim-congruence-Commutative-Monoidᵉ xᵉ yᵉ)
  is-prop-sim-congruence-Commutative-Monoidᵉ =
    is-prop-sim-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Rᵉ

  concatenate-sim-eq-congruence-Commutative-Monoidᵉ :
    {xᵉ yᵉ zᵉ : type-Commutative-Monoidᵉ Mᵉ} →
    sim-congruence-Commutative-Monoidᵉ xᵉ yᵉ → yᵉ ＝ᵉ zᵉ →
    sim-congruence-Commutative-Monoidᵉ xᵉ zᵉ
  concatenate-sim-eq-congruence-Commutative-Monoidᵉ =
    concatenate-sim-eq-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Rᵉ

  concatenate-eq-sim-congruence-Commutative-Monoidᵉ :
    {xᵉ yᵉ zᵉ : type-Commutative-Monoidᵉ Mᵉ} → xᵉ ＝ᵉ yᵉ →
    sim-congruence-Commutative-Monoidᵉ yᵉ zᵉ →
    sim-congruence-Commutative-Monoidᵉ xᵉ zᵉ
  concatenate-eq-sim-congruence-Commutative-Monoidᵉ =
    concatenate-eq-sim-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Rᵉ

  concatenate-eq-sim-eq-congruence-Commutative-Monoidᵉ :
    {xᵉ yᵉ zᵉ wᵉ : type-Commutative-Monoidᵉ Mᵉ} → xᵉ ＝ᵉ yᵉ →
    sim-congruence-Commutative-Monoidᵉ yᵉ zᵉ →
    zᵉ ＝ᵉ wᵉ → sim-congruence-Commutative-Monoidᵉ xᵉ wᵉ
  concatenate-eq-sim-eq-congruence-Commutative-Monoidᵉ =
    concatenate-eq-sim-eq-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Rᵉ

  refl-congruence-Commutative-Monoidᵉ :
    is-reflexiveᵉ sim-congruence-Commutative-Monoidᵉ
  refl-congruence-Commutative-Monoidᵉ =
    refl-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Rᵉ

  symmetric-congruence-Commutative-Monoidᵉ :
    is-symmetricᵉ sim-congruence-Commutative-Monoidᵉ
  symmetric-congruence-Commutative-Monoidᵉ =
    symmetric-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Rᵉ

  equiv-symmetric-congruence-Commutative-Monoidᵉ :
    (xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ) →
    sim-congruence-Commutative-Monoidᵉ xᵉ yᵉ ≃ᵉ
    sim-congruence-Commutative-Monoidᵉ yᵉ xᵉ
  equiv-symmetric-congruence-Commutative-Monoidᵉ =
    equiv-symmetric-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Rᵉ

  transitive-congruence-Commutative-Monoidᵉ :
    is-transitiveᵉ sim-congruence-Commutative-Monoidᵉ
  transitive-congruence-Commutative-Monoidᵉ =
    transitive-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Rᵉ

  mul-congruence-Commutative-Monoidᵉ :
    is-congruence-Commutative-Monoidᵉ Mᵉ
      equivalence-relation-congruence-Commutative-Monoidᵉ
  mul-congruence-Commutative-Monoidᵉ =
    mul-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Rᵉ
```

## Properties

### Extensionality of the type of congruence relations on a monoid

```agda
relate-same-elements-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ : congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ)
  (Sᵉ : congruence-Commutative-Monoidᵉ l3ᵉ Mᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
relate-same-elements-congruence-Commutative-Monoidᵉ Mᵉ =
  relate-same-elements-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

refl-relate-same-elements-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ : congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ) →
  relate-same-elements-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Rᵉ
refl-relate-same-elements-congruence-Commutative-Monoidᵉ Mᵉ =
  refl-relate-same-elements-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

is-torsorial-relate-same-elements-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ : congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ) →
  is-torsorialᵉ (relate-same-elements-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ)
is-torsorial-relate-same-elements-congruence-Commutative-Monoidᵉ Mᵉ =
  is-torsorial-relate-same-elements-congruence-Monoidᵉ
    ( monoid-Commutative-Monoidᵉ Mᵉ)

relate-same-elements-eq-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ Sᵉ : congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ) →
  Rᵉ ＝ᵉ Sᵉ → relate-same-elements-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Sᵉ
relate-same-elements-eq-congruence-Commutative-Monoidᵉ Mᵉ =
  relate-same-elements-eq-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

is-equiv-relate-same-elements-eq-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ Sᵉ : congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ) →
  is-equivᵉ (relate-same-elements-eq-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Sᵉ)
is-equiv-relate-same-elements-eq-congruence-Commutative-Monoidᵉ Mᵉ =
  is-equiv-relate-same-elements-eq-congruence-Monoidᵉ
    ( monoid-Commutative-Monoidᵉ Mᵉ)

extensionality-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ Sᵉ : congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ) →
  (Rᵉ ＝ᵉ Sᵉ) ≃ᵉ relate-same-elements-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Sᵉ
extensionality-congruence-Commutative-Monoidᵉ Mᵉ =
  extensionality-congruence-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

eq-relate-same-elements-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ Sᵉ : congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ) →
  relate-same-elements-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Sᵉ → Rᵉ ＝ᵉ Sᵉ
eq-relate-same-elements-congruence-Commutative-Monoidᵉ Mᵉ =
  eq-relate-same-elements-congruence-Monoidᵉ
    ( monoid-Commutative-Monoidᵉ Mᵉ)
```