# Saturated congruence relations on monoids

```agda
module group-theory.saturated-congruence-relations-monoidsᵉ where
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

open import group-theory.congruence-relations-monoidsᵉ
open import group-theory.monoidsᵉ
```

</details>

## Idea

Forᵉ anyᵉ monoidᵉ `M`,ᵉ theᵉ typeᵉ ofᵉ normalᵉ submonoidsᵉ isᵉ aᵉ retractᵉ ofᵉ theᵉ typeᵉ ofᵉ
congruenceᵉ relationsᵉ onᵉ `M`.ᵉ Aᵉ congruenceᵉ relationᵉ onᵉ `M`ᵉ isᵉ saidᵉ to beᵉ
**saturated**ᵉ ifᵉ itᵉ isᵉ in theᵉ imageᵉ ofᵉ theᵉ inclusionᵉ ofᵉ theᵉ normalᵉ submonoidsᵉ ofᵉ
`M`ᵉ intoᵉ theᵉ congruenceᵉ relationsᵉ onᵉ `M`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ : congruence-Monoidᵉ l2ᵉ Mᵉ)
  where

  is-saturated-prop-congruence-Monoidᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-saturated-prop-congruence-Monoidᵉ =
    Π-Propᵉ
      ( type-Monoidᵉ Mᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( type-Monoidᵉ Mᵉ)
          ( λ yᵉ →
            function-Propᵉ
              ( (uᵉ vᵉ : type-Monoidᵉ Mᵉ) →
                ( sim-congruence-Monoidᵉ Mᵉ Rᵉ
                  ( mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ uᵉ xᵉ) vᵉ)
                  ( unit-Monoidᵉ Mᵉ)) ↔ᵉ
                ( sim-congruence-Monoidᵉ Mᵉ Rᵉ
                  ( mul-Monoidᵉ Mᵉ (mul-Monoidᵉ Mᵉ uᵉ yᵉ) vᵉ)
                  ( unit-Monoidᵉ Mᵉ)))
              ( prop-congruence-Monoidᵉ Mᵉ Rᵉ xᵉ yᵉ)))

  is-saturated-congruence-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-saturated-congruence-Monoidᵉ = type-Propᵉ is-saturated-prop-congruence-Monoidᵉ

  is-prop-is-saturated-congruence-Monoidᵉ :
    is-propᵉ is-saturated-congruence-Monoidᵉ
  is-prop-is-saturated-congruence-Monoidᵉ =
    is-prop-type-Propᵉ is-saturated-prop-congruence-Monoidᵉ

saturated-congruence-Monoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Monoidᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
saturated-congruence-Monoidᵉ l2ᵉ Mᵉ =
  Σᵉ ( congruence-Monoidᵉ l2ᵉ Mᵉ)
    ( is-saturated-congruence-Monoidᵉ Mᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ : saturated-congruence-Monoidᵉ l2ᵉ Mᵉ)
  where

  congruence-saturated-congruence-Monoidᵉ : congruence-Monoidᵉ l2ᵉ Mᵉ
  congruence-saturated-congruence-Monoidᵉ = pr1ᵉ Rᵉ

  is-saturated-saturated-congruence-Monoidᵉ :
    is-saturated-congruence-Monoidᵉ Mᵉ congruence-saturated-congruence-Monoidᵉ
  is-saturated-saturated-congruence-Monoidᵉ = pr2ᵉ Rᵉ

  equivalence-relation-saturated-congruence-Monoidᵉ :
    equivalence-relationᵉ l2ᵉ (type-Monoidᵉ Mᵉ)
  equivalence-relation-saturated-congruence-Monoidᵉ =
    equivalence-relation-congruence-Monoidᵉ Mᵉ
      ( congruence-saturated-congruence-Monoidᵉ)

  prop-saturated-congruence-Monoidᵉ : Relation-Propᵉ l2ᵉ (type-Monoidᵉ Mᵉ)
  prop-saturated-congruence-Monoidᵉ =
    prop-congruence-Monoidᵉ Mᵉ congruence-saturated-congruence-Monoidᵉ

  sim-saturated-congruence-Monoidᵉ : (xᵉ yᵉ : type-Monoidᵉ Mᵉ) → UUᵉ l2ᵉ
  sim-saturated-congruence-Monoidᵉ =
    sim-congruence-Monoidᵉ Mᵉ congruence-saturated-congruence-Monoidᵉ

  is-prop-sim-saturated-congruence-Monoidᵉ :
    (xᵉ yᵉ : type-Monoidᵉ Mᵉ) → is-propᵉ (sim-saturated-congruence-Monoidᵉ xᵉ yᵉ)
  is-prop-sim-saturated-congruence-Monoidᵉ =
    is-prop-sim-congruence-Monoidᵉ Mᵉ congruence-saturated-congruence-Monoidᵉ

  concatenate-sim-eq-saturated-congruence-Monoidᵉ :
    {xᵉ yᵉ zᵉ : type-Monoidᵉ Mᵉ} →
    sim-saturated-congruence-Monoidᵉ xᵉ yᵉ → yᵉ ＝ᵉ zᵉ →
    sim-saturated-congruence-Monoidᵉ xᵉ zᵉ
  concatenate-sim-eq-saturated-congruence-Monoidᵉ =
    concatenate-sim-eq-congruence-Monoidᵉ Mᵉ
      congruence-saturated-congruence-Monoidᵉ

  concatenate-eq-sim-saturated-congruence-Monoidᵉ :
    {xᵉ yᵉ zᵉ : type-Monoidᵉ Mᵉ} →
    xᵉ ＝ᵉ yᵉ → sim-saturated-congruence-Monoidᵉ yᵉ zᵉ →
    sim-saturated-congruence-Monoidᵉ xᵉ zᵉ
  concatenate-eq-sim-saturated-congruence-Monoidᵉ =
    concatenate-eq-sim-congruence-Monoidᵉ Mᵉ
      congruence-saturated-congruence-Monoidᵉ

  concatenate-eq-sim-eq-saturated-congruence-Monoidᵉ :
    {xᵉ yᵉ zᵉ wᵉ : type-Monoidᵉ Mᵉ} →
    xᵉ ＝ᵉ yᵉ → sim-saturated-congruence-Monoidᵉ yᵉ zᵉ →
    zᵉ ＝ᵉ wᵉ → sim-saturated-congruence-Monoidᵉ xᵉ wᵉ
  concatenate-eq-sim-eq-saturated-congruence-Monoidᵉ =
    concatenate-eq-sim-eq-congruence-Monoidᵉ Mᵉ
      congruence-saturated-congruence-Monoidᵉ

  refl-saturated-congruence-Monoidᵉ :
    is-reflexiveᵉ sim-saturated-congruence-Monoidᵉ
  refl-saturated-congruence-Monoidᵉ =
    refl-congruence-Monoidᵉ Mᵉ congruence-saturated-congruence-Monoidᵉ

  symmetric-saturated-congruence-Monoidᵉ :
    is-symmetricᵉ sim-saturated-congruence-Monoidᵉ
  symmetric-saturated-congruence-Monoidᵉ =
    symmetric-congruence-Monoidᵉ Mᵉ congruence-saturated-congruence-Monoidᵉ

  equiv-symmetric-saturated-congruence-Monoidᵉ :
    (xᵉ yᵉ : type-Monoidᵉ Mᵉ) →
    sim-saturated-congruence-Monoidᵉ xᵉ yᵉ ≃ᵉ sim-saturated-congruence-Monoidᵉ yᵉ xᵉ
  equiv-symmetric-saturated-congruence-Monoidᵉ =
    equiv-symmetric-congruence-Monoidᵉ Mᵉ congruence-saturated-congruence-Monoidᵉ

  transitive-saturated-congruence-Monoidᵉ :
    is-transitiveᵉ sim-saturated-congruence-Monoidᵉ
  transitive-saturated-congruence-Monoidᵉ =
    transitive-congruence-Monoidᵉ Mᵉ congruence-saturated-congruence-Monoidᵉ

  mul-saturated-congruence-Monoidᵉ :
    is-congruence-Monoidᵉ Mᵉ equivalence-relation-saturated-congruence-Monoidᵉ
  mul-saturated-congruence-Monoidᵉ =
    mul-congruence-Monoidᵉ Mᵉ congruence-saturated-congruence-Monoidᵉ
```

## Properties

### Extensionality of the type of saturated congruence relations on a monoid

```agda
relate-same-elements-saturated-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ)
  (Rᵉ : saturated-congruence-Monoidᵉ l2ᵉ Mᵉ)
  (Sᵉ : saturated-congruence-Monoidᵉ l3ᵉ Mᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
relate-same-elements-saturated-congruence-Monoidᵉ Mᵉ Rᵉ Sᵉ =
  relate-same-elements-congruence-Monoidᵉ Mᵉ
    ( congruence-saturated-congruence-Monoidᵉ Mᵉ Rᵉ)
    ( congruence-saturated-congruence-Monoidᵉ Mᵉ Sᵉ)

refl-relate-same-elements-saturated-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ : saturated-congruence-Monoidᵉ l2ᵉ Mᵉ) →
  relate-same-elements-saturated-congruence-Monoidᵉ Mᵉ Rᵉ Rᵉ
refl-relate-same-elements-saturated-congruence-Monoidᵉ Mᵉ Rᵉ =
  refl-relate-same-elements-congruence-Monoidᵉ Mᵉ
    ( congruence-saturated-congruence-Monoidᵉ Mᵉ Rᵉ)

is-torsorial-relate-same-elements-saturated-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ : saturated-congruence-Monoidᵉ l2ᵉ Mᵉ) →
  is-torsorialᵉ (relate-same-elements-saturated-congruence-Monoidᵉ Mᵉ Rᵉ)
is-torsorial-relate-same-elements-saturated-congruence-Monoidᵉ Mᵉ Rᵉ =
  is-torsorial-Eq-subtypeᵉ
    ( is-torsorial-relate-same-elements-congruence-Monoidᵉ Mᵉ
      ( congruence-saturated-congruence-Monoidᵉ Mᵉ Rᵉ))
    ( is-prop-is-saturated-congruence-Monoidᵉ Mᵉ)
    ( congruence-saturated-congruence-Monoidᵉ Mᵉ Rᵉ)
    ( refl-relate-same-elements-congruence-Monoidᵉ Mᵉ
      ( congruence-saturated-congruence-Monoidᵉ Mᵉ Rᵉ))
    ( is-saturated-saturated-congruence-Monoidᵉ Mᵉ Rᵉ)

relate-same-elements-eq-saturated-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ Sᵉ : saturated-congruence-Monoidᵉ l2ᵉ Mᵉ) →
  Rᵉ ＝ᵉ Sᵉ → relate-same-elements-saturated-congruence-Monoidᵉ Mᵉ Rᵉ Sᵉ
relate-same-elements-eq-saturated-congruence-Monoidᵉ Mᵉ Rᵉ .Rᵉ reflᵉ =
  refl-relate-same-elements-saturated-congruence-Monoidᵉ Mᵉ Rᵉ

is-equiv-relate-same-elements-eq-saturated-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ Sᵉ : saturated-congruence-Monoidᵉ l2ᵉ Mᵉ) →
  is-equivᵉ (relate-same-elements-eq-saturated-congruence-Monoidᵉ Mᵉ Rᵉ Sᵉ)
is-equiv-relate-same-elements-eq-saturated-congruence-Monoidᵉ Mᵉ Rᵉ =
  fundamental-theorem-idᵉ
    ( is-torsorial-relate-same-elements-saturated-congruence-Monoidᵉ Mᵉ Rᵉ)
    ( relate-same-elements-eq-saturated-congruence-Monoidᵉ Mᵉ Rᵉ)

extensionality-saturated-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ Sᵉ : saturated-congruence-Monoidᵉ l2ᵉ Mᵉ) →
  (Rᵉ ＝ᵉ Sᵉ) ≃ᵉ relate-same-elements-saturated-congruence-Monoidᵉ Mᵉ Rᵉ Sᵉ
pr1ᵉ (extensionality-saturated-congruence-Monoidᵉ Mᵉ Rᵉ Sᵉ) =
  relate-same-elements-eq-saturated-congruence-Monoidᵉ Mᵉ Rᵉ Sᵉ
pr2ᵉ (extensionality-saturated-congruence-Monoidᵉ Mᵉ Rᵉ Sᵉ) =
  is-equiv-relate-same-elements-eq-saturated-congruence-Monoidᵉ Mᵉ Rᵉ Sᵉ

eq-relate-same-elements-saturated-congruence-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Rᵉ Sᵉ : saturated-congruence-Monoidᵉ l2ᵉ Mᵉ) →
  relate-same-elements-saturated-congruence-Monoidᵉ Mᵉ Rᵉ Sᵉ → Rᵉ ＝ᵉ Sᵉ
eq-relate-same-elements-saturated-congruence-Monoidᵉ Mᵉ Rᵉ Sᵉ =
  map-inv-equivᵉ (extensionality-saturated-congruence-Monoidᵉ Mᵉ Rᵉ Sᵉ)
```

## See also

-ᵉ Notᵉ everyᵉ congruenceᵉ relationᵉ onᵉ aᵉ monoidᵉ isᵉ saturated.ᵉ Forᵉ anᵉ example,ᵉ seeᵉ
  theᵉ monoidᵉ
  [`ℕ-Max`](elementary-number-theory.monoid-of-natural-numbers-with-maximum.md).ᵉ