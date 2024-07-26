# Congruence relations on semigroups

```agda
module group-theory.congruence-relations-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.semigroupsᵉ
```

</details>

## Idea

Aᵉ congruenceᵉ relationᵉ onᵉ aᵉ semigroupᵉ `G`ᵉ isᵉ anᵉ equivalenceᵉ relationᵉ `≡`ᵉ onᵉ `G`ᵉ
suchᵉ thatᵉ forᵉ everyᵉ `x1ᵉ x2ᵉ y1ᵉ y2ᵉ : G`ᵉ suchᵉ thatᵉ `x1ᵉ ≡ᵉ x2`ᵉ andᵉ `y1ᵉ ≡ᵉ y2`ᵉ weᵉ haveᵉ
`x1ᵉ ·ᵉ y1ᵉ ≡ᵉ x2ᵉ ·ᵉ y2`.ᵉ

## Definition

```agda
is-congruence-prop-Semigroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) →
  equivalence-relationᵉ l2ᵉ (type-Semigroupᵉ Gᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-congruence-prop-Semigroupᵉ Gᵉ Rᵉ =
  implicit-Π-Propᵉ
    ( type-Semigroupᵉ Gᵉ)
    ( λ x1ᵉ →
      implicit-Π-Propᵉ
        ( type-Semigroupᵉ Gᵉ)
        ( λ x2ᵉ →
          implicit-Π-Propᵉ
            ( type-Semigroupᵉ Gᵉ)
            ( λ y1ᵉ →
              implicit-Π-Propᵉ
                ( type-Semigroupᵉ Gᵉ)
                ( λ y2ᵉ →
                  function-Propᵉ
                    ( sim-equivalence-relationᵉ Rᵉ x1ᵉ x2ᵉ)
                    ( function-Propᵉ
                      ( sim-equivalence-relationᵉ Rᵉ y1ᵉ y2ᵉ)
                      ( prop-equivalence-relationᵉ Rᵉ
                        ( mul-Semigroupᵉ Gᵉ x1ᵉ y1ᵉ)
                        ( mul-Semigroupᵉ Gᵉ x2ᵉ y2ᵉ)))))))

is-congruence-Semigroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) →
  equivalence-relationᵉ l2ᵉ (type-Semigroupᵉ Gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-congruence-Semigroupᵉ Gᵉ Rᵉ =
  type-Propᵉ (is-congruence-prop-Semigroupᵉ Gᵉ Rᵉ)

is-prop-is-congruence-Semigroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ)
  (Rᵉ : equivalence-relationᵉ l2ᵉ (type-Semigroupᵉ Gᵉ)) →
  is-propᵉ (is-congruence-Semigroupᵉ Gᵉ Rᵉ)
is-prop-is-congruence-Semigroupᵉ Gᵉ Rᵉ =
  is-prop-type-Propᵉ (is-congruence-prop-Semigroupᵉ Gᵉ Rᵉ)

congruence-Semigroupᵉ :
  {lᵉ : Level} (l2ᵉ : Level) (Gᵉ : Semigroupᵉ lᵉ) → UUᵉ (lᵉ ⊔ lsuc l2ᵉ)
congruence-Semigroupᵉ l2ᵉ Gᵉ =
  Σᵉ (equivalence-relationᵉ l2ᵉ (type-Semigroupᵉ Gᵉ)) (is-congruence-Semigroupᵉ Gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Rᵉ : congruence-Semigroupᵉ l2ᵉ Gᵉ)
  where

  equivalence-relation-congruence-Semigroupᵉ :
    equivalence-relationᵉ l2ᵉ (type-Semigroupᵉ Gᵉ)
  equivalence-relation-congruence-Semigroupᵉ = pr1ᵉ Rᵉ

  prop-congruence-Semigroupᵉ : Relation-Propᵉ l2ᵉ (type-Semigroupᵉ Gᵉ)
  prop-congruence-Semigroupᵉ =
    prop-equivalence-relationᵉ equivalence-relation-congruence-Semigroupᵉ

  sim-congruence-Semigroupᵉ : (xᵉ yᵉ : type-Semigroupᵉ Gᵉ) → UUᵉ l2ᵉ
  sim-congruence-Semigroupᵉ =
    sim-equivalence-relationᵉ equivalence-relation-congruence-Semigroupᵉ

  is-prop-sim-congruence-Semigroupᵉ :
    (xᵉ yᵉ : type-Semigroupᵉ Gᵉ) → is-propᵉ (sim-congruence-Semigroupᵉ xᵉ yᵉ)
  is-prop-sim-congruence-Semigroupᵉ =
    is-prop-sim-equivalence-relationᵉ equivalence-relation-congruence-Semigroupᵉ

  refl-congruence-Semigroupᵉ : is-reflexiveᵉ sim-congruence-Semigroupᵉ
  refl-congruence-Semigroupᵉ =
    refl-equivalence-relationᵉ equivalence-relation-congruence-Semigroupᵉ

  symmetric-congruence-Semigroupᵉ : is-symmetricᵉ sim-congruence-Semigroupᵉ
  symmetric-congruence-Semigroupᵉ =
    symmetric-equivalence-relationᵉ equivalence-relation-congruence-Semigroupᵉ

  equiv-symmetric-congruence-Semigroupᵉ :
    (xᵉ yᵉ : type-Semigroupᵉ Gᵉ) →
    sim-congruence-Semigroupᵉ xᵉ yᵉ ≃ᵉ sim-congruence-Semigroupᵉ yᵉ xᵉ
  equiv-symmetric-congruence-Semigroupᵉ xᵉ yᵉ =
    equiv-symmetric-equivalence-relationᵉ
      ( equivalence-relation-congruence-Semigroupᵉ)

  transitive-congruence-Semigroupᵉ : is-transitiveᵉ sim-congruence-Semigroupᵉ
  transitive-congruence-Semigroupᵉ =
    transitive-equivalence-relationᵉ equivalence-relation-congruence-Semigroupᵉ

  mul-congruence-Semigroupᵉ :
    is-congruence-Semigroupᵉ Gᵉ equivalence-relation-congruence-Semigroupᵉ
  mul-congruence-Semigroupᵉ = pr2ᵉ Rᵉ
```

## Properties

### Characterizing equality of congruences of semigroups

```agda
relate-same-elements-congruence-Semigroupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) →
  congruence-Semigroupᵉ l2ᵉ Gᵉ → congruence-Semigroupᵉ l3ᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
relate-same-elements-congruence-Semigroupᵉ Gᵉ Rᵉ Sᵉ =
  relate-same-elements-equivalence-relationᵉ
    ( equivalence-relation-congruence-Semigroupᵉ Gᵉ Rᵉ)
    ( equivalence-relation-congruence-Semigroupᵉ Gᵉ Sᵉ)

refl-relate-same-elements-congruence-Semigroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Rᵉ : congruence-Semigroupᵉ l2ᵉ Gᵉ) →
  relate-same-elements-congruence-Semigroupᵉ Gᵉ Rᵉ Rᵉ
refl-relate-same-elements-congruence-Semigroupᵉ Gᵉ Rᵉ =
  refl-relate-same-elements-equivalence-relationᵉ
    ( equivalence-relation-congruence-Semigroupᵉ Gᵉ Rᵉ)

is-torsorial-relate-same-elements-congruence-Semigroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Rᵉ : congruence-Semigroupᵉ l2ᵉ Gᵉ) →
  is-torsorialᵉ (relate-same-elements-congruence-Semigroupᵉ Gᵉ Rᵉ)
is-torsorial-relate-same-elements-congruence-Semigroupᵉ Gᵉ Rᵉ =
  is-torsorial-Eq-subtypeᵉ
    ( is-torsorial-relate-same-elements-equivalence-relationᵉ
      ( equivalence-relation-congruence-Semigroupᵉ Gᵉ Rᵉ))
    ( is-prop-is-congruence-Semigroupᵉ Gᵉ)
    ( equivalence-relation-congruence-Semigroupᵉ Gᵉ Rᵉ)
    ( refl-relate-same-elements-congruence-Semigroupᵉ Gᵉ Rᵉ)
    ( mul-congruence-Semigroupᵉ Gᵉ Rᵉ)

relate-same-elements-eq-congruence-Semigroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Semigroupᵉ l2ᵉ Gᵉ) →
  Rᵉ ＝ᵉ Sᵉ → relate-same-elements-congruence-Semigroupᵉ Gᵉ Rᵉ Sᵉ
relate-same-elements-eq-congruence-Semigroupᵉ Gᵉ Rᵉ .Rᵉ reflᵉ =
  refl-relate-same-elements-congruence-Semigroupᵉ Gᵉ Rᵉ

is-equiv-relate-same-elements-eq-congruence-Semigroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Semigroupᵉ l2ᵉ Gᵉ) →
  is-equivᵉ (relate-same-elements-eq-congruence-Semigroupᵉ Gᵉ Rᵉ Sᵉ)
is-equiv-relate-same-elements-eq-congruence-Semigroupᵉ Gᵉ Rᵉ =
  fundamental-theorem-idᵉ
    ( is-torsorial-relate-same-elements-congruence-Semigroupᵉ Gᵉ Rᵉ)
    ( relate-same-elements-eq-congruence-Semigroupᵉ Gᵉ Rᵉ)

extensionality-congruence-Semigroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Semigroupᵉ l2ᵉ Gᵉ) →
  (Rᵉ ＝ᵉ Sᵉ) ≃ᵉ relate-same-elements-congruence-Semigroupᵉ Gᵉ Rᵉ Sᵉ
pr1ᵉ (extensionality-congruence-Semigroupᵉ Gᵉ Rᵉ Sᵉ) =
  relate-same-elements-eq-congruence-Semigroupᵉ Gᵉ Rᵉ Sᵉ
pr2ᵉ (extensionality-congruence-Semigroupᵉ Gᵉ Rᵉ Sᵉ) =
  is-equiv-relate-same-elements-eq-congruence-Semigroupᵉ Gᵉ Rᵉ Sᵉ

eq-relate-same-elements-congruence-Semigroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Rᵉ Sᵉ : congruence-Semigroupᵉ l2ᵉ Gᵉ) →
  relate-same-elements-congruence-Semigroupᵉ Gᵉ Rᵉ Sᵉ → Rᵉ ＝ᵉ Sᵉ
eq-relate-same-elements-congruence-Semigroupᵉ Gᵉ Rᵉ Sᵉ =
  map-inv-equivᵉ (extensionality-congruence-Semigroupᵉ Gᵉ Rᵉ Sᵉ)
```