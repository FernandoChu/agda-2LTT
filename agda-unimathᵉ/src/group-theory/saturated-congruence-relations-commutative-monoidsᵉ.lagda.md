# Saturated congruence relations on commutative monoids

```agda
module group-theory.saturated-congruence-relations-commutative-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.congruence-relations-commutative-monoidsᵉ
```

</details>

## Idea

Forᵉ anyᵉ commutativeᵉ monoidᵉ `M`,ᵉ theᵉ typeᵉ ofᵉ normalᵉ submonoidsᵉ isᵉ aᵉ retractᵉ ofᵉ
theᵉ typeᵉ ofᵉ congruenceᵉ relationsᵉ onᵉ `M`.ᵉ Aᵉ congruenceᵉ relationᵉ onᵉ `M`ᵉ isᵉ saidᵉ to
beᵉ **saturated**ᵉ ifᵉ itᵉ isᵉ in theᵉ imageᵉ ofᵉ theᵉ inclusionᵉ ofᵉ theᵉ normalᵉ submonoidsᵉ
ofᵉ `M`ᵉ intoᵉ theᵉ congruenceᵉ relationsᵉ onᵉ `M`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ : congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ)
  where

  is-saturated-prop-congruence-Commutative-Monoidᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-saturated-prop-congruence-Commutative-Monoidᵉ =
    Π-Propᵉ
      ( type-Commutative-Monoidᵉ Mᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( type-Commutative-Monoidᵉ Mᵉ)
          ( λ yᵉ →
            function-Propᵉ
              ( (uᵉ : type-Commutative-Monoidᵉ Mᵉ) →
                ( sim-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ
                  ( mul-Commutative-Monoidᵉ Mᵉ uᵉ xᵉ)
                  ( unit-Commutative-Monoidᵉ Mᵉ)) ↔ᵉ
                ( sim-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ
                  ( mul-Commutative-Monoidᵉ Mᵉ uᵉ yᵉ)
                  ( unit-Commutative-Monoidᵉ Mᵉ)))
              ( prop-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ xᵉ yᵉ)))

  is-saturated-congruence-Commutative-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-saturated-congruence-Commutative-Monoidᵉ =
    type-Propᵉ is-saturated-prop-congruence-Commutative-Monoidᵉ

  is-prop-is-saturated-congruence-Commutative-Monoidᵉ :
    is-propᵉ is-saturated-congruence-Commutative-Monoidᵉ
  is-prop-is-saturated-congruence-Commutative-Monoidᵉ =
    is-prop-type-Propᵉ is-saturated-prop-congruence-Commutative-Monoidᵉ

saturated-congruence-Commutative-Monoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Commutative-Monoidᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
saturated-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ =
  Σᵉ ( congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ)
    ( is-saturated-congruence-Commutative-Monoidᵉ Mᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ : saturated-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ)
  where

  congruence-saturated-congruence-Commutative-Monoidᵉ :
    congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ
  congruence-saturated-congruence-Commutative-Monoidᵉ = pr1ᵉ Rᵉ

  is-saturated-saturated-congruence-Commutative-Monoidᵉ :
    is-saturated-congruence-Commutative-Monoidᵉ Mᵉ
      congruence-saturated-congruence-Commutative-Monoidᵉ
  is-saturated-saturated-congruence-Commutative-Monoidᵉ = pr2ᵉ Rᵉ

  equivalence-relation-saturated-congruence-Commutative-Monoidᵉ :
    equivalence-relationᵉ l2ᵉ (type-Commutative-Monoidᵉ Mᵉ)
  equivalence-relation-saturated-congruence-Commutative-Monoidᵉ =
    equivalence-relation-congruence-Commutative-Monoidᵉ Mᵉ
      congruence-saturated-congruence-Commutative-Monoidᵉ

  prop-saturated-congruence-Commutative-Monoidᵉ :
    Relation-Propᵉ l2ᵉ (type-Commutative-Monoidᵉ Mᵉ)
  prop-saturated-congruence-Commutative-Monoidᵉ =
    prop-congruence-Commutative-Monoidᵉ Mᵉ
      congruence-saturated-congruence-Commutative-Monoidᵉ

  sim-saturated-congruence-Commutative-Monoidᵉ :
    (xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ) → UUᵉ l2ᵉ
  sim-saturated-congruence-Commutative-Monoidᵉ =
    sim-congruence-Commutative-Monoidᵉ Mᵉ
      congruence-saturated-congruence-Commutative-Monoidᵉ

  is-prop-sim-saturated-congruence-Commutative-Monoidᵉ :
    (xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ) →
      is-propᵉ (sim-saturated-congruence-Commutative-Monoidᵉ xᵉ yᵉ)
  is-prop-sim-saturated-congruence-Commutative-Monoidᵉ =
    is-prop-sim-congruence-Commutative-Monoidᵉ Mᵉ
      congruence-saturated-congruence-Commutative-Monoidᵉ

  concatenate-sim-eq-saturated-congruence-Commutative-Monoidᵉ :
    {xᵉ yᵉ zᵉ : type-Commutative-Monoidᵉ Mᵉ} →
    sim-saturated-congruence-Commutative-Monoidᵉ xᵉ yᵉ → yᵉ ＝ᵉ zᵉ →
    sim-saturated-congruence-Commutative-Monoidᵉ xᵉ zᵉ
  concatenate-sim-eq-saturated-congruence-Commutative-Monoidᵉ =
    concatenate-sim-eq-congruence-Commutative-Monoidᵉ Mᵉ
      congruence-saturated-congruence-Commutative-Monoidᵉ

  concatenate-eq-sim-saturated-congruence-Commutative-Monoidᵉ :
    {xᵉ yᵉ zᵉ : type-Commutative-Monoidᵉ Mᵉ} → xᵉ ＝ᵉ yᵉ →
    sim-saturated-congruence-Commutative-Monoidᵉ yᵉ zᵉ →
    sim-saturated-congruence-Commutative-Monoidᵉ xᵉ zᵉ
  concatenate-eq-sim-saturated-congruence-Commutative-Monoidᵉ =
    concatenate-eq-sim-congruence-Commutative-Monoidᵉ Mᵉ
      congruence-saturated-congruence-Commutative-Monoidᵉ

  concatenate-eq-sim-eq-saturated-congruence-Commutative-Monoidᵉ :
    {xᵉ yᵉ zᵉ wᵉ : type-Commutative-Monoidᵉ Mᵉ} → xᵉ ＝ᵉ yᵉ →
    sim-saturated-congruence-Commutative-Monoidᵉ yᵉ zᵉ →
    zᵉ ＝ᵉ wᵉ → sim-saturated-congruence-Commutative-Monoidᵉ xᵉ wᵉ
  concatenate-eq-sim-eq-saturated-congruence-Commutative-Monoidᵉ =
    concatenate-eq-sim-eq-congruence-Commutative-Monoidᵉ Mᵉ
      congruence-saturated-congruence-Commutative-Monoidᵉ

  refl-saturated-congruence-Commutative-Monoidᵉ :
    is-reflexiveᵉ sim-saturated-congruence-Commutative-Monoidᵉ
  refl-saturated-congruence-Commutative-Monoidᵉ =
    refl-congruence-Commutative-Monoidᵉ Mᵉ
    congruence-saturated-congruence-Commutative-Monoidᵉ

  symmetric-saturated-congruence-Commutative-Monoidᵉ :
    is-symmetricᵉ sim-saturated-congruence-Commutative-Monoidᵉ
  symmetric-saturated-congruence-Commutative-Monoidᵉ =
    symmetric-congruence-Commutative-Monoidᵉ Mᵉ
    congruence-saturated-congruence-Commutative-Monoidᵉ

  equiv-symmetric-saturated-congruence-Commutative-Monoidᵉ :
    (xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ) →
    sim-saturated-congruence-Commutative-Monoidᵉ xᵉ yᵉ ≃ᵉ
    sim-saturated-congruence-Commutative-Monoidᵉ yᵉ xᵉ
  equiv-symmetric-saturated-congruence-Commutative-Monoidᵉ =
    equiv-symmetric-congruence-Commutative-Monoidᵉ Mᵉ
    congruence-saturated-congruence-Commutative-Monoidᵉ

  transitive-saturated-congruence-Commutative-Monoidᵉ :
    is-transitiveᵉ sim-saturated-congruence-Commutative-Monoidᵉ
  transitive-saturated-congruence-Commutative-Monoidᵉ =
    transitive-congruence-Commutative-Monoidᵉ Mᵉ
      congruence-saturated-congruence-Commutative-Monoidᵉ

  mul-saturated-congruence-Commutative-Monoidᵉ :
    is-congruence-Commutative-Monoidᵉ Mᵉ
      equivalence-relation-saturated-congruence-Commutative-Monoidᵉ
  mul-saturated-congruence-Commutative-Monoidᵉ =
    mul-congruence-Commutative-Monoidᵉ Mᵉ
      congruence-saturated-congruence-Commutative-Monoidᵉ
```

## Properties

### Extensionality of the type of saturated congruence relations on a commutative monoid

```agda
relate-same-elements-saturated-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ : saturated-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ)
  (Sᵉ : saturated-congruence-Commutative-Monoidᵉ l3ᵉ Mᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
relate-same-elements-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Sᵉ =
  relate-same-elements-congruence-Commutative-Monoidᵉ Mᵉ
    ( congruence-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ)
    ( congruence-saturated-congruence-Commutative-Monoidᵉ Mᵉ Sᵉ)

refl-relate-same-elements-saturated-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ : saturated-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ) →
  relate-same-elements-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Rᵉ
refl-relate-same-elements-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ =
  refl-relate-same-elements-congruence-Commutative-Monoidᵉ Mᵉ
    ( congruence-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ)

is-torsorial-relate-same-elements-saturated-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ : saturated-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ) →
  is-torsorialᵉ
    ( relate-same-elements-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ)
is-torsorial-relate-same-elements-saturated-congruence-Commutative-Monoidᵉ
  Mᵉ Rᵉ =
  is-torsorial-Eq-subtypeᵉ
    ( is-torsorial-relate-same-elements-congruence-Commutative-Monoidᵉ Mᵉ
      ( congruence-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ))
    ( is-prop-is-saturated-congruence-Commutative-Monoidᵉ Mᵉ)
    ( congruence-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ)
    ( refl-relate-same-elements-congruence-Commutative-Monoidᵉ Mᵉ
      ( congruence-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ))
    ( is-saturated-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ)

relate-same-elements-eq-saturated-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ Sᵉ : saturated-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ) →
  Rᵉ ＝ᵉ Sᵉ → relate-same-elements-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Sᵉ
relate-same-elements-eq-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ .Rᵉ reflᵉ =
  refl-relate-same-elements-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ

is-equiv-relate-same-elements-eq-saturated-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ Sᵉ : saturated-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ) →
  is-equivᵉ
    ( relate-same-elements-eq-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Sᵉ)
is-equiv-relate-same-elements-eq-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ =
  fundamental-theorem-idᵉ
    ( is-torsorial-relate-same-elements-saturated-congruence-Commutative-Monoidᵉ
      ( Mᵉ)
      ( Rᵉ))
    ( relate-same-elements-eq-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ)

extensionality-saturated-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ Sᵉ : saturated-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ) →
  (Rᵉ ＝ᵉ Sᵉ) ≃ᵉ relate-same-elements-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Sᵉ
pr1ᵉ (extensionality-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Sᵉ) =
  relate-same-elements-eq-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Sᵉ
pr2ᵉ (extensionality-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Sᵉ) =
  is-equiv-relate-same-elements-eq-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Sᵉ

eq-relate-same-elements-saturated-congruence-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ Sᵉ : saturated-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ) →
  relate-same-elements-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Sᵉ → Rᵉ ＝ᵉ Sᵉ
eq-relate-same-elements-saturated-congruence-Commutative-Monoidᵉ
  Mᵉ Rᵉ Sᵉ =
  map-inv-equivᵉ (extensionality-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Sᵉ)
```

## See also

-ᵉ Notᵉ everyᵉ congruenceᵉ relationᵉ onᵉ aᵉ commutativeᵉ monoidᵉ isᵉ saturated.ᵉ Forᵉ anᵉ
  example,ᵉ seeᵉ theᵉ commutativeᵉ monoidᵉ
  [`ℕ-Max`](elementary-number-theory.monoid-of-natural-numbers-with-maximum.md).ᵉ