# Congruence relations on semirings

```agda
module ring-theory.congruence-relations-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.congruence-relations-monoidsᵉ

open import ring-theory.semiringsᵉ
```

</details>

## Idea

Aᵉ congruenceᵉ relationᵉ onᵉ aᵉ semiringᵉ `R`ᵉ isᵉ aᵉ congruenceᵉ relationᵉ onᵉ theᵉ
underlyingᵉ additiveᵉ monoidᵉ ofᵉ `R`ᵉ whichᵉ isᵉ alsoᵉ aᵉ congruenceᵉ relationᵉ onᵉ theᵉ
multiplicativeᵉ monoidᵉ ofᵉ `R`.ᵉ

## Definition

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ)
  where

  is-congruence-Semiringᵉ :
    {l2ᵉ : Level}
    (Sᵉ : congruence-Monoidᵉ l2ᵉ (additive-monoid-Semiringᵉ Rᵉ)) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-congruence-Semiringᵉ Sᵉ =
    is-congruence-Monoidᵉ
      ( multiplicative-monoid-Semiringᵉ Rᵉ)
      ( equivalence-relation-congruence-Monoidᵉ (additive-monoid-Semiringᵉ Rᵉ) Sᵉ)

  is-prop-is-congruence-Semiringᵉ :
    {l2ᵉ : Level} (Sᵉ : congruence-Monoidᵉ l2ᵉ (additive-monoid-Semiringᵉ Rᵉ)) →
    is-propᵉ (is-congruence-Semiringᵉ Sᵉ)
  is-prop-is-congruence-Semiringᵉ Sᵉ =
    is-prop-is-congruence-Monoidᵉ
      ( multiplicative-monoid-Semiringᵉ Rᵉ)
      ( equivalence-relation-congruence-Monoidᵉ (additive-monoid-Semiringᵉ Rᵉ) Sᵉ)

  is-congruence-equivalence-relation-Semiringᵉ :
    {l2ᵉ : Level} (Sᵉ : equivalence-relationᵉ l2ᵉ (type-Semiringᵉ Rᵉ)) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-congruence-equivalence-relation-Semiringᵉ Sᵉ =
    ( is-congruence-Monoidᵉ (additive-monoid-Semiringᵉ Rᵉ) Sᵉ) ×ᵉ
    ( is-congruence-Monoidᵉ (multiplicative-monoid-Semiringᵉ Rᵉ) Sᵉ)

congruence-Semiringᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Rᵉ : Semiringᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
congruence-Semiringᵉ l2ᵉ Rᵉ =
  Σᵉ ( congruence-Monoidᵉ l2ᵉ (additive-monoid-Semiringᵉ Rᵉ))
    ( is-congruence-Semiringᵉ Rᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Sᵉ : congruence-Semiringᵉ l2ᵉ Rᵉ)
  where

  congruence-additive-monoid-congruence-Semiringᵉ :
    congruence-Monoidᵉ l2ᵉ (additive-monoid-Semiringᵉ Rᵉ)
  congruence-additive-monoid-congruence-Semiringᵉ = pr1ᵉ Sᵉ

  equivalence-relation-congruence-Semiringᵉ :
    equivalence-relationᵉ l2ᵉ (type-Semiringᵉ Rᵉ)
  equivalence-relation-congruence-Semiringᵉ =
    equivalence-relation-congruence-Monoidᵉ
      ( additive-monoid-Semiringᵉ Rᵉ)
      ( congruence-additive-monoid-congruence-Semiringᵉ)

  prop-congruence-Semiringᵉ : Relation-Propᵉ l2ᵉ (type-Semiringᵉ Rᵉ)
  prop-congruence-Semiringᵉ =
    prop-congruence-Monoidᵉ
      ( additive-monoid-Semiringᵉ Rᵉ)
      ( congruence-additive-monoid-congruence-Semiringᵉ)

  sim-congruence-Semiringᵉ : (xᵉ yᵉ : type-Semiringᵉ Rᵉ) → UUᵉ l2ᵉ
  sim-congruence-Semiringᵉ =
    sim-congruence-Monoidᵉ
      ( additive-monoid-Semiringᵉ Rᵉ)
      ( congruence-additive-monoid-congruence-Semiringᵉ)

  is-prop-sim-congruence-Semiringᵉ :
    (xᵉ yᵉ : type-Semiringᵉ Rᵉ) → is-propᵉ (sim-congruence-Semiringᵉ xᵉ yᵉ)
  is-prop-sim-congruence-Semiringᵉ =
    is-prop-sim-congruence-Monoidᵉ
      ( additive-monoid-Semiringᵉ Rᵉ)
      ( congruence-additive-monoid-congruence-Semiringᵉ)

  refl-congruence-Semiringᵉ :
    is-reflexiveᵉ sim-congruence-Semiringᵉ
  refl-congruence-Semiringᵉ =
    refl-congruence-Monoidᵉ
      ( additive-monoid-Semiringᵉ Rᵉ)
      ( congruence-additive-monoid-congruence-Semiringᵉ)

  symmetric-congruence-Semiringᵉ :
    is-symmetricᵉ sim-congruence-Semiringᵉ
  symmetric-congruence-Semiringᵉ =
    symmetric-congruence-Monoidᵉ
      ( additive-monoid-Semiringᵉ Rᵉ)
      ( congruence-additive-monoid-congruence-Semiringᵉ)

  equiv-symmetric-congruence-Semiringᵉ :
    (xᵉ yᵉ : type-Semiringᵉ Rᵉ) →
    sim-congruence-Semiringᵉ xᵉ yᵉ ≃ᵉ sim-congruence-Semiringᵉ yᵉ xᵉ
  equiv-symmetric-congruence-Semiringᵉ =
    equiv-symmetric-congruence-Monoidᵉ
      ( additive-monoid-Semiringᵉ Rᵉ)
      ( congruence-additive-monoid-congruence-Semiringᵉ)

  transitive-congruence-Semiringᵉ :
    is-transitiveᵉ sim-congruence-Semiringᵉ
  transitive-congruence-Semiringᵉ =
    transitive-congruence-Monoidᵉ
      ( additive-monoid-Semiringᵉ Rᵉ)
      ( congruence-additive-monoid-congruence-Semiringᵉ)

  add-congruence-Semiringᵉ :
    is-congruence-Monoidᵉ
      ( additive-monoid-Semiringᵉ Rᵉ)
      ( equivalence-relation-congruence-Semiringᵉ)
  add-congruence-Semiringᵉ =
    mul-congruence-Monoidᵉ
      ( additive-monoid-Semiringᵉ Rᵉ)
      ( congruence-additive-monoid-congruence-Semiringᵉ)

  mul-congruence-Semiringᵉ :
    is-congruence-Monoidᵉ
      ( multiplicative-monoid-Semiringᵉ Rᵉ)
      ( equivalence-relation-congruence-Semiringᵉ)
  mul-congruence-Semiringᵉ = pr2ᵉ Sᵉ

construct-congruence-Semiringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) →
  (Sᵉ : equivalence-relationᵉ l2ᵉ (type-Semiringᵉ Rᵉ)) →
  is-congruence-Monoidᵉ (additive-monoid-Semiringᵉ Rᵉ) Sᵉ →
  is-congruence-Monoidᵉ (multiplicative-monoid-Semiringᵉ Rᵉ) Sᵉ →
  congruence-Semiringᵉ l2ᵉ Rᵉ
pr1ᵉ (pr1ᵉ (construct-congruence-Semiringᵉ Rᵉ Sᵉ Hᵉ Kᵉ)) = Sᵉ
pr2ᵉ (pr1ᵉ (construct-congruence-Semiringᵉ Rᵉ Sᵉ Hᵉ Kᵉ)) = Hᵉ
pr2ᵉ (construct-congruence-Semiringᵉ Rᵉ Sᵉ Hᵉ Kᵉ) = Kᵉ
```

## Properties

### Characterizing equality of congruence relations of semirings

```agda
relate-same-elements-congruence-Semiringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) →
  congruence-Semiringᵉ l2ᵉ Rᵉ → congruence-Semiringᵉ l3ᵉ Rᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
relate-same-elements-congruence-Semiringᵉ Rᵉ Sᵉ Tᵉ =
  relate-same-elements-equivalence-relationᵉ
    ( equivalence-relation-congruence-Semiringᵉ Rᵉ Sᵉ)
    ( equivalence-relation-congruence-Semiringᵉ Rᵉ Tᵉ)

refl-relate-same-elements-congruence-Semiringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Sᵉ : congruence-Semiringᵉ l2ᵉ Rᵉ) →
  relate-same-elements-congruence-Semiringᵉ Rᵉ Sᵉ Sᵉ
refl-relate-same-elements-congruence-Semiringᵉ Rᵉ Sᵉ =
  refl-relate-same-elements-equivalence-relationᵉ
    ( equivalence-relation-congruence-Semiringᵉ Rᵉ Sᵉ)

is-torsorial-relate-same-elements-congruence-Semiringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Sᵉ : congruence-Semiringᵉ l2ᵉ Rᵉ) →
  is-torsorialᵉ (relate-same-elements-congruence-Semiringᵉ Rᵉ Sᵉ)
is-torsorial-relate-same-elements-congruence-Semiringᵉ Rᵉ Sᵉ =
  is-torsorial-Eq-subtypeᵉ
    ( is-torsorial-relate-same-elements-congruence-Monoidᵉ
      ( additive-monoid-Semiringᵉ Rᵉ)
      ( congruence-additive-monoid-congruence-Semiringᵉ Rᵉ Sᵉ))
    ( is-prop-is-congruence-Semiringᵉ Rᵉ)
    ( congruence-additive-monoid-congruence-Semiringᵉ Rᵉ Sᵉ)
    ( refl-relate-same-elements-congruence-Semiringᵉ Rᵉ Sᵉ)
    ( mul-congruence-Semiringᵉ Rᵉ Sᵉ)

relate-same-elements-eq-congruence-Semiringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Sᵉ Tᵉ : congruence-Semiringᵉ l2ᵉ Rᵉ) →
  Sᵉ ＝ᵉ Tᵉ → relate-same-elements-congruence-Semiringᵉ Rᵉ Sᵉ Tᵉ
relate-same-elements-eq-congruence-Semiringᵉ Rᵉ Sᵉ .Sᵉ reflᵉ =
  refl-relate-same-elements-congruence-Semiringᵉ Rᵉ Sᵉ

is-equiv-relate-same-elements-eq-congruence-Semiringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Sᵉ Tᵉ : congruence-Semiringᵉ l2ᵉ Rᵉ) →
  is-equivᵉ (relate-same-elements-eq-congruence-Semiringᵉ Rᵉ Sᵉ Tᵉ)
is-equiv-relate-same-elements-eq-congruence-Semiringᵉ Rᵉ Sᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-relate-same-elements-congruence-Semiringᵉ Rᵉ Sᵉ)
      ( relate-same-elements-eq-congruence-Semiringᵉ Rᵉ Sᵉ)

extensionality-congruence-Semiringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Sᵉ Tᵉ : congruence-Semiringᵉ l2ᵉ Rᵉ) →
  (Sᵉ ＝ᵉ Tᵉ) ≃ᵉ relate-same-elements-congruence-Semiringᵉ Rᵉ Sᵉ Tᵉ
pr1ᵉ (extensionality-congruence-Semiringᵉ Rᵉ Sᵉ Tᵉ) =
  relate-same-elements-eq-congruence-Semiringᵉ Rᵉ Sᵉ Tᵉ
pr2ᵉ (extensionality-congruence-Semiringᵉ Rᵉ Sᵉ Tᵉ) =
  is-equiv-relate-same-elements-eq-congruence-Semiringᵉ Rᵉ Sᵉ Tᵉ

eq-relate-same-elements-congruence-Semiringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Sᵉ Tᵉ : congruence-Semiringᵉ l2ᵉ Rᵉ) →
  relate-same-elements-congruence-Semiringᵉ Rᵉ Sᵉ Tᵉ → Sᵉ ＝ᵉ Tᵉ
eq-relate-same-elements-congruence-Semiringᵉ Rᵉ Sᵉ Tᵉ =
  map-inv-equivᵉ (extensionality-congruence-Semiringᵉ Rᵉ Sᵉ Tᵉ)
```