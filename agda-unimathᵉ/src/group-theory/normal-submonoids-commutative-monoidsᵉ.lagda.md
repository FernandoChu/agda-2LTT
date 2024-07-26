# Normal submonoids of commutative monoids

```agda
module group-theory.normal-submonoids-commutative-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.congruence-relations-commutative-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.saturated-congruence-relations-commutative-monoidsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.submonoids-commutative-monoidsᵉ
open import group-theory.subsets-commutative-monoidsᵉ
```

</details>

## Idea

Aᵉ normalᵉ submonoidᵉ `N`ᵉ ofᵉ ofᵉ aᵉ commutativeᵉ monoidᵉ `M`ᵉ isᵉ aᵉ submonoidᵉ thatᵉ
correspondsᵉ uniquelyᵉ to aᵉ saturatedᵉ congruenceᵉ relationᵉ `~`ᵉ onᵉ `M`ᵉ consistingᵉ ofᵉ
theᵉ elementsᵉ congruentᵉ to `1`.ᵉ Thisᵉ isᵉ theᵉ caseᵉ ifᵉ andᵉ onlyᵉ ifᵉ forᵉ allᵉ `xᵉ : M`ᵉ
andᵉ `uᵉ : N`ᵉ weᵉ haveᵉ

```text
  xuᵉ ∈ᵉ Nᵉ → xᵉ ∈ᵉ Nᵉ
```

## Definitions

### Normal submonoids of commutative monoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ) (Nᵉ : Commutative-Submonoidᵉ l2ᵉ Mᵉ)
  where

  is-normal-prop-Commutative-Submonoidᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-normal-prop-Commutative-Submonoidᵉ =
    Π-Propᵉ
      ( type-Commutative-Monoidᵉ Mᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( type-Commutative-Monoidᵉ Mᵉ)
          ( λ uᵉ →
            function-Propᵉ
              ( is-in-Commutative-Submonoidᵉ Mᵉ Nᵉ uᵉ)
              ( function-Propᵉ
                ( is-in-Commutative-Submonoidᵉ Mᵉ Nᵉ
                  ( mul-Commutative-Monoidᵉ Mᵉ xᵉ uᵉ))
                ( subset-Commutative-Submonoidᵉ Mᵉ Nᵉ xᵉ))))

  is-normal-Commutative-Submonoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-normal-Commutative-Submonoidᵉ =
    type-Propᵉ is-normal-prop-Commutative-Submonoidᵉ

  is-prop-is-normal-Commutative-Submonoidᵉ :
    is-propᵉ is-normal-Commutative-Submonoidᵉ
  is-prop-is-normal-Commutative-Submonoidᵉ =
    is-prop-type-Propᵉ is-normal-prop-Commutative-Submonoidᵉ

Normal-Commutative-Submonoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → Commutative-Monoidᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ =
  Σᵉ (Commutative-Submonoidᵉ l2ᵉ Mᵉ) (is-normal-Commutative-Submonoidᵉ Mᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Nᵉ : Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ)
  where

  submonoid-Normal-Commutative-Submonoidᵉ : Commutative-Submonoidᵉ l2ᵉ Mᵉ
  submonoid-Normal-Commutative-Submonoidᵉ = pr1ᵉ Nᵉ

  is-normal-Normal-Commutative-Submonoidᵉ :
    is-normal-Commutative-Submonoidᵉ Mᵉ submonoid-Normal-Commutative-Submonoidᵉ
  is-normal-Normal-Commutative-Submonoidᵉ = pr2ᵉ Nᵉ

  subset-Normal-Commutative-Submonoidᵉ : subtypeᵉ l2ᵉ (type-Commutative-Monoidᵉ Mᵉ)
  subset-Normal-Commutative-Submonoidᵉ =
    subset-Commutative-Submonoidᵉ Mᵉ submonoid-Normal-Commutative-Submonoidᵉ

  is-submonoid-Normal-Commutative-Submonoidᵉ :
    is-submonoid-subset-Commutative-Monoidᵉ Mᵉ subset-Normal-Commutative-Submonoidᵉ
  is-submonoid-Normal-Commutative-Submonoidᵉ =
    is-submonoid-Commutative-Submonoidᵉ Mᵉ submonoid-Normal-Commutative-Submonoidᵉ

  is-in-Normal-Commutative-Submonoidᵉ : type-Commutative-Monoidᵉ Mᵉ → UUᵉ l2ᵉ
  is-in-Normal-Commutative-Submonoidᵉ =
    is-in-Commutative-Submonoidᵉ Mᵉ submonoid-Normal-Commutative-Submonoidᵉ

  is-prop-is-in-Normal-Commutative-Submonoidᵉ :
    (xᵉ : type-Commutative-Monoidᵉ Mᵉ) →
    is-propᵉ (is-in-Normal-Commutative-Submonoidᵉ xᵉ)
  is-prop-is-in-Normal-Commutative-Submonoidᵉ =
    is-prop-is-in-Commutative-Submonoidᵉ Mᵉ
      submonoid-Normal-Commutative-Submonoidᵉ

  is-closed-under-eq-Normal-Commutative-Submonoidᵉ :
    {xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ} →
    is-in-Normal-Commutative-Submonoidᵉ xᵉ → (xᵉ ＝ᵉ yᵉ) →
    is-in-Normal-Commutative-Submonoidᵉ yᵉ
  is-closed-under-eq-Normal-Commutative-Submonoidᵉ =
    is-closed-under-eq-subtypeᵉ subset-Normal-Commutative-Submonoidᵉ

  is-closed-under-eq-Normal-Commutative-Submonoid'ᵉ :
    {xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ} → is-in-Normal-Commutative-Submonoidᵉ yᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-Normal-Commutative-Submonoidᵉ xᵉ
  is-closed-under-eq-Normal-Commutative-Submonoid'ᵉ =
    is-closed-under-eq-subtype'ᵉ subset-Normal-Commutative-Submonoidᵉ

  type-Normal-Commutative-Submonoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Normal-Commutative-Submonoidᵉ =
    type-Commutative-Submonoidᵉ Mᵉ submonoid-Normal-Commutative-Submonoidᵉ

  is-set-type-Normal-Commutative-Submonoidᵉ :
    is-setᵉ type-Normal-Commutative-Submonoidᵉ
  is-set-type-Normal-Commutative-Submonoidᵉ =
    is-set-type-Commutative-Submonoidᵉ Mᵉ submonoid-Normal-Commutative-Submonoidᵉ

  set-Normal-Commutative-Submonoidᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Normal-Commutative-Submonoidᵉ =
    set-Commutative-Submonoidᵉ Mᵉ submonoid-Normal-Commutative-Submonoidᵉ

  inclusion-Normal-Commutative-Submonoidᵉ :
    type-Normal-Commutative-Submonoidᵉ → type-Commutative-Monoidᵉ Mᵉ
  inclusion-Normal-Commutative-Submonoidᵉ =
    inclusion-Commutative-Submonoidᵉ Mᵉ submonoid-Normal-Commutative-Submonoidᵉ

  ap-inclusion-Normal-Commutative-Submonoidᵉ :
    (xᵉ yᵉ : type-Normal-Commutative-Submonoidᵉ) → xᵉ ＝ᵉ yᵉ →
    inclusion-Normal-Commutative-Submonoidᵉ xᵉ ＝ᵉ
    inclusion-Normal-Commutative-Submonoidᵉ yᵉ
  ap-inclusion-Normal-Commutative-Submonoidᵉ =
    ap-inclusion-Commutative-Submonoidᵉ Mᵉ submonoid-Normal-Commutative-Submonoidᵉ

  is-in-submonoid-inclusion-Normal-Commutative-Submonoidᵉ :
    (xᵉ : type-Normal-Commutative-Submonoidᵉ) →
    is-in-Normal-Commutative-Submonoidᵉ
      ( inclusion-Normal-Commutative-Submonoidᵉ xᵉ)
  is-in-submonoid-inclusion-Normal-Commutative-Submonoidᵉ =
    is-in-submonoid-inclusion-Commutative-Submonoidᵉ Mᵉ
      submonoid-Normal-Commutative-Submonoidᵉ

  contains-unit-Normal-Commutative-Submonoidᵉ :
    is-in-Normal-Commutative-Submonoidᵉ (unit-Commutative-Monoidᵉ Mᵉ)
  contains-unit-Normal-Commutative-Submonoidᵉ =
    contains-unit-Commutative-Submonoidᵉ Mᵉ submonoid-Normal-Commutative-Submonoidᵉ

  unit-Normal-Commutative-Submonoidᵉ : type-Normal-Commutative-Submonoidᵉ
  unit-Normal-Commutative-Submonoidᵉ =
    unit-Commutative-Submonoidᵉ Mᵉ submonoid-Normal-Commutative-Submonoidᵉ

  is-closed-under-multiplication-Normal-Commutative-Submonoidᵉ :
    {xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ} →
    is-in-Normal-Commutative-Submonoidᵉ xᵉ →
    is-in-Normal-Commutative-Submonoidᵉ yᵉ →
    is-in-Normal-Commutative-Submonoidᵉ (mul-Commutative-Monoidᵉ Mᵉ xᵉ yᵉ)
  is-closed-under-multiplication-Normal-Commutative-Submonoidᵉ =
    is-closed-under-multiplication-Commutative-Submonoidᵉ Mᵉ
      submonoid-Normal-Commutative-Submonoidᵉ

  mul-Normal-Commutative-Submonoidᵉ :
    (xᵉ yᵉ : type-Normal-Commutative-Submonoidᵉ) →
    type-Normal-Commutative-Submonoidᵉ
  mul-Normal-Commutative-Submonoidᵉ =
    mul-Commutative-Submonoidᵉ Mᵉ submonoid-Normal-Commutative-Submonoidᵉ

  associative-mul-Normal-Commutative-Submonoidᵉ :
    (xᵉ yᵉ zᵉ : type-Normal-Commutative-Submonoidᵉ) →
    ( mul-Normal-Commutative-Submonoidᵉ
      ( mul-Normal-Commutative-Submonoidᵉ xᵉ yᵉ)
      ( zᵉ)) ＝ᵉ
    ( mul-Normal-Commutative-Submonoidᵉ xᵉ
      ( mul-Normal-Commutative-Submonoidᵉ yᵉ zᵉ))
  associative-mul-Normal-Commutative-Submonoidᵉ =
    associative-mul-Commutative-Submonoidᵉ Mᵉ
      submonoid-Normal-Commutative-Submonoidᵉ

  semigroup-Normal-Commutative-Submonoidᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-Normal-Commutative-Submonoidᵉ =
    semigroup-Commutative-Submonoidᵉ Mᵉ submonoid-Normal-Commutative-Submonoidᵉ

  left-unit-law-mul-Normal-Commutative-Submonoidᵉ :
    (xᵉ : type-Normal-Commutative-Submonoidᵉ) →
    mul-Normal-Commutative-Submonoidᵉ unit-Normal-Commutative-Submonoidᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Normal-Commutative-Submonoidᵉ =
    left-unit-law-mul-Commutative-Submonoidᵉ Mᵉ
      submonoid-Normal-Commutative-Submonoidᵉ

  right-unit-law-mul-Normal-Commutative-Submonoidᵉ :
    (xᵉ : type-Normal-Commutative-Submonoidᵉ) →
    mul-Normal-Commutative-Submonoidᵉ xᵉ unit-Normal-Commutative-Submonoidᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Normal-Commutative-Submonoidᵉ =
    right-unit-law-mul-Commutative-Submonoidᵉ Mᵉ
      submonoid-Normal-Commutative-Submonoidᵉ

  commutative-mul-Normal-Commutative-Submonoidᵉ :
    (xᵉ yᵉ : type-Normal-Commutative-Submonoidᵉ) →
    mul-Normal-Commutative-Submonoidᵉ xᵉ yᵉ ＝ᵉ
    mul-Normal-Commutative-Submonoidᵉ yᵉ xᵉ
  commutative-mul-Normal-Commutative-Submonoidᵉ =
    commutative-mul-Commutative-Submonoidᵉ Mᵉ
      submonoid-Normal-Commutative-Submonoidᵉ

  monoid-Normal-Commutative-Submonoidᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  monoid-Normal-Commutative-Submonoidᵉ =
    monoid-Commutative-Submonoidᵉ Mᵉ submonoid-Normal-Commutative-Submonoidᵉ

  commutative-monoid-Normal-Commutative-Submonoidᵉ :
    Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  commutative-monoid-Normal-Commutative-Submonoidᵉ =
    commutative-monoid-Commutative-Submonoidᵉ Mᵉ
      submonoid-Normal-Commutative-Submonoidᵉ
```

## Properties

### Extensionality of the type of all normal submonoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Nᵉ : Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ)
  where

  has-same-elements-Normal-Commutative-Submonoidᵉ :
    {l3ᵉ : Level} → Normal-Commutative-Submonoidᵉ l3ᵉ Mᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-Normal-Commutative-Submonoidᵉ Kᵉ =
    has-same-elements-Commutative-Submonoidᵉ Mᵉ
      ( submonoid-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ)
      ( submonoid-Normal-Commutative-Submonoidᵉ Mᵉ Kᵉ)

  extensionality-Normal-Commutative-Submonoidᵉ :
    (Kᵉ : Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ) →
    (Nᵉ ＝ᵉ Kᵉ) ≃ᵉ has-same-elements-Normal-Commutative-Submonoidᵉ Kᵉ
  extensionality-Normal-Commutative-Submonoidᵉ =
    extensionality-type-subtypeᵉ
      ( is-normal-prop-Commutative-Submonoidᵉ Mᵉ)
      ( is-normal-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ)
      ( λ xᵉ → (idᵉ ,ᵉ idᵉ))
      ( extensionality-Commutative-Submonoidᵉ Mᵉ
        ( submonoid-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ))

  eq-has-same-elements-Normal-Commutative-Submonoidᵉ :
    (Kᵉ : Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ) →
    has-same-elements-Normal-Commutative-Submonoidᵉ Kᵉ → Nᵉ ＝ᵉ Kᵉ
  eq-has-same-elements-Normal-Commutative-Submonoidᵉ Kᵉ =
    map-inv-equivᵉ (extensionality-Normal-Commutative-Submonoidᵉ Kᵉ)
```

### The congruence relation of a normal submonoid

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Mᵉ : Commutative-Monoidᵉ l1ᵉ) (Nᵉ : Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ)
  where

  rel-congruence-Normal-Commutative-Submonoidᵉ :
    Relation-Propᵉ (l1ᵉ ⊔ l2ᵉ) (type-Commutative-Monoidᵉ Mᵉ)
  rel-congruence-Normal-Commutative-Submonoidᵉ xᵉ yᵉ =
    Π-Propᵉ
      ( type-Commutative-Monoidᵉ Mᵉ)
      ( λ uᵉ →
        iff-Propᵉ
          ( subset-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ
            ( mul-Commutative-Monoidᵉ Mᵉ uᵉ xᵉ))
          ( subset-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ
            ( mul-Commutative-Monoidᵉ Mᵉ uᵉ yᵉ)))

  sim-congruence-Normal-Commutative-Submonoidᵉ :
    (xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  sim-congruence-Normal-Commutative-Submonoidᵉ xᵉ yᵉ =
    type-Propᵉ (rel-congruence-Normal-Commutative-Submonoidᵉ xᵉ yᵉ)

  refl-congruence-Normal-Commutative-Submonoidᵉ :
    is-reflexiveᵉ sim-congruence-Normal-Commutative-Submonoidᵉ
  pr1ᵉ (refl-congruence-Normal-Commutative-Submonoidᵉ _ _) = idᵉ
  pr2ᵉ (refl-congruence-Normal-Commutative-Submonoidᵉ _ _) = idᵉ

  symmetric-congruence-Normal-Commutative-Submonoidᵉ :
    is-symmetricᵉ sim-congruence-Normal-Commutative-Submonoidᵉ
  pr1ᵉ (symmetric-congruence-Normal-Commutative-Submonoidᵉ _ _ Hᵉ uᵉ) = pr2ᵉ (Hᵉ uᵉ)
  pr2ᵉ (symmetric-congruence-Normal-Commutative-Submonoidᵉ _ _ Hᵉ uᵉ) = pr1ᵉ (Hᵉ uᵉ)

  transitive-congruence-Normal-Commutative-Submonoidᵉ :
    is-transitiveᵉ sim-congruence-Normal-Commutative-Submonoidᵉ
  transitive-congruence-Normal-Commutative-Submonoidᵉ _ _ _ Hᵉ Kᵉ uᵉ =
    (Hᵉ uᵉ) ∘iffᵉ (Kᵉ uᵉ)

  equivalence-relation-congruence-Normal-Commutative-Submonoidᵉ :
    equivalence-relationᵉ (l1ᵉ ⊔ l2ᵉ) (type-Commutative-Monoidᵉ Mᵉ)
  pr1ᵉ equivalence-relation-congruence-Normal-Commutative-Submonoidᵉ =
    rel-congruence-Normal-Commutative-Submonoidᵉ
  pr1ᵉ (pr2ᵉ equivalence-relation-congruence-Normal-Commutative-Submonoidᵉ) =
    refl-congruence-Normal-Commutative-Submonoidᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-congruence-Normal-Commutative-Submonoidᵉ)) =
    symmetric-congruence-Normal-Commutative-Submonoidᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-congruence-Normal-Commutative-Submonoidᵉ)) =
    transitive-congruence-Normal-Commutative-Submonoidᵉ

  is-congruence-congruence-Normal-Commutative-Submonoidᵉ :
    is-congruence-Commutative-Monoidᵉ Mᵉ
      equivalence-relation-congruence-Normal-Commutative-Submonoidᵉ
  pr1ᵉ
    ( is-congruence-congruence-Normal-Commutative-Submonoidᵉ
      {xᵉ} {x'ᵉ} {yᵉ} {y'ᵉ} Hᵉ Kᵉ uᵉ)
    ( Lᵉ) =
    is-closed-under-eq-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ
      ( forward-implicationᵉ
        ( Kᵉ (mul-Commutative-Monoidᵉ Mᵉ uᵉ x'ᵉ))
        ( is-closed-under-eq-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ
          ( forward-implicationᵉ
            ( Hᵉ (mul-Commutative-Monoidᵉ Mᵉ uᵉ yᵉ))
            ( is-closed-under-eq-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ Lᵉ
              ( ( invᵉ (associative-mul-Commutative-Monoidᵉ Mᵉ uᵉ xᵉ yᵉ)) ∙ᵉ
                ( right-swap-mul-Commutative-Monoidᵉ Mᵉ uᵉ xᵉ yᵉ))))
          ( right-swap-mul-Commutative-Monoidᵉ Mᵉ uᵉ yᵉ x'ᵉ)))
      ( associative-mul-Commutative-Monoidᵉ Mᵉ uᵉ x'ᵉ y'ᵉ)
  pr2ᵉ
    ( is-congruence-congruence-Normal-Commutative-Submonoidᵉ
      {xᵉ} {x'ᵉ} {yᵉ} {y'ᵉ} Hᵉ Kᵉ uᵉ)
    ( Lᵉ) =
    is-closed-under-eq-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ
      ( backward-implicationᵉ
        ( Kᵉ (mul-Commutative-Monoidᵉ Mᵉ uᵉ xᵉ))
        ( is-closed-under-eq-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ
          ( backward-implicationᵉ
            ( Hᵉ (mul-Commutative-Monoidᵉ Mᵉ uᵉ y'ᵉ))
            ( is-closed-under-eq-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ Lᵉ
              ( ( invᵉ (associative-mul-Commutative-Monoidᵉ Mᵉ uᵉ x'ᵉ y'ᵉ)) ∙ᵉ
                ( right-swap-mul-Commutative-Monoidᵉ Mᵉ uᵉ x'ᵉ y'ᵉ))))
          ( right-swap-mul-Commutative-Monoidᵉ Mᵉ uᵉ y'ᵉ xᵉ)))
      ( associative-mul-Commutative-Monoidᵉ Mᵉ uᵉ xᵉ yᵉ)

  congruence-Normal-Commutative-Submonoidᵉ :
    congruence-Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ
  pr1ᵉ congruence-Normal-Commutative-Submonoidᵉ =
    equivalence-relation-congruence-Normal-Commutative-Submonoidᵉ
  pr2ᵉ congruence-Normal-Commutative-Submonoidᵉ =
    is-congruence-congruence-Normal-Commutative-Submonoidᵉ
```

### The normal submonoid obtained from a congruence relation

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ : congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ)
  where

  subset-normal-submonoid-congruence-Commutative-Monoidᵉ :
    subtypeᵉ l2ᵉ (type-Commutative-Monoidᵉ Mᵉ)
  subset-normal-submonoid-congruence-Commutative-Monoidᵉ xᵉ =
    prop-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ xᵉ (unit-Commutative-Monoidᵉ Mᵉ)

  is-in-normal-submonoid-congruence-Commutative-Monoidᵉ :
    type-Commutative-Monoidᵉ Mᵉ → UUᵉ l2ᵉ
  is-in-normal-submonoid-congruence-Commutative-Monoidᵉ =
    is-in-subtypeᵉ subset-normal-submonoid-congruence-Commutative-Monoidᵉ

  contains-unit-normal-submonoid-congruence-Commutative-Monoidᵉ :
    is-in-normal-submonoid-congruence-Commutative-Monoidᵉ
      ( unit-Commutative-Monoidᵉ Mᵉ)
  contains-unit-normal-submonoid-congruence-Commutative-Monoidᵉ =
    refl-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ (unit-Commutative-Monoidᵉ Mᵉ)

  is-closed-under-multiplication-normal-submonoid-congruence-Commutative-Monoidᵉ :
    is-closed-under-multiplication-subset-Commutative-Monoidᵉ Mᵉ
      subset-normal-submonoid-congruence-Commutative-Monoidᵉ
  is-closed-under-multiplication-normal-submonoid-congruence-Commutative-Monoidᵉ
    xᵉ yᵉ Hᵉ Kᵉ =
    concatenate-sim-eq-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ
      ( mul-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ Hᵉ Kᵉ)
      ( left-unit-law-mul-Commutative-Monoidᵉ Mᵉ (unit-Commutative-Monoidᵉ Mᵉ))

  submonoid-congruence-Commutative-Monoidᵉ : Commutative-Submonoidᵉ l2ᵉ Mᵉ
  pr1ᵉ submonoid-congruence-Commutative-Monoidᵉ =
    subset-normal-submonoid-congruence-Commutative-Monoidᵉ
  pr1ᵉ (pr2ᵉ submonoid-congruence-Commutative-Monoidᵉ) =
    contains-unit-normal-submonoid-congruence-Commutative-Monoidᵉ
  pr2ᵉ (pr2ᵉ submonoid-congruence-Commutative-Monoidᵉ) =
    is-closed-under-multiplication-normal-submonoid-congruence-Commutative-Monoidᵉ

  is-normal-submonoid-congruence-Commutative-Monoidᵉ :
    is-normal-Commutative-Submonoidᵉ Mᵉ submonoid-congruence-Commutative-Monoidᵉ
  is-normal-submonoid-congruence-Commutative-Monoidᵉ xᵉ uᵉ Hᵉ Kᵉ =
    transitive-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ
      ( xᵉ)
      ( mul-Commutative-Monoidᵉ Mᵉ xᵉ uᵉ)
      ( unit-Commutative-Monoidᵉ Mᵉ)
      ( Kᵉ)
      ( symmetric-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ
        ( mul-Commutative-Monoidᵉ Mᵉ xᵉ uᵉ)
        ( xᵉ)
        ( concatenate-sim-eq-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ
          ( mul-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ
            ( refl-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ xᵉ)
            ( Hᵉ))
          ( right-unit-law-mul-Commutative-Monoidᵉ Mᵉ xᵉ)))

  normal-submonoid-congruence-Commutative-Monoidᵉ :
    Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ
  pr1ᵉ normal-submonoid-congruence-Commutative-Monoidᵉ =
    submonoid-congruence-Commutative-Monoidᵉ
  pr2ᵉ normal-submonoid-congruence-Commutative-Monoidᵉ =
    is-normal-submonoid-congruence-Commutative-Monoidᵉ
```

### The normal submonoid obtained from the congruence relation of a normal submonoid has the same elements as the original normal submonoid

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Mᵉ : Commutative-Monoidᵉ l1ᵉ) (Nᵉ : Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ)
  where

  has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoidᵉ :
    has-same-elements-Normal-Commutative-Submonoidᵉ Mᵉ
      ( normal-submonoid-congruence-Commutative-Monoidᵉ Mᵉ
        ( congruence-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ))
      ( Nᵉ)
  pr1ᵉ
    ( has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoidᵉ
      xᵉ)
    ( Hᵉ) =
    is-closed-under-eq-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ
      ( backward-implicationᵉ
        ( Hᵉ (unit-Commutative-Monoidᵉ Mᵉ))
        ( is-closed-under-eq-Normal-Commutative-Submonoid'ᵉ Mᵉ Nᵉ
          ( contains-unit-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ)
          ( left-unit-law-mul-Commutative-Monoidᵉ Mᵉ
            ( unit-Commutative-Monoidᵉ Mᵉ))))
      ( left-unit-law-mul-Commutative-Monoidᵉ Mᵉ xᵉ)
  pr1ᵉ
    ( pr2ᵉ
      ( has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoidᵉ
        ( xᵉ))
      ( Hᵉ)
      ( uᵉ))
    ( Kᵉ) =
    is-closed-under-eq-Normal-Commutative-Submonoid'ᵉ Mᵉ Nᵉ
      ( is-normal-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ uᵉ xᵉ Hᵉ Kᵉ)
      ( right-unit-law-mul-Commutative-Monoidᵉ Mᵉ uᵉ)
  pr2ᵉ
    ( pr2ᵉ
      ( has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoidᵉ
        ( xᵉ))
      ( Hᵉ)
      ( uᵉ))
    ( Kᵉ) =
    is-closed-under-multiplication-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ
      ( is-closed-under-eq-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ Kᵉ
        ( right-unit-law-mul-Commutative-Monoidᵉ Mᵉ uᵉ))
      ( Hᵉ)
```

### The congruence relation of a normal submonoid is saturated

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Mᵉ : Commutative-Monoidᵉ l1ᵉ) (Nᵉ : Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ)
  where

  is-saturated-congruence-Normal-Commutative-Submonoidᵉ :
    is-saturated-congruence-Commutative-Monoidᵉ Mᵉ
      ( congruence-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ)
  is-saturated-congruence-Normal-Commutative-Submonoidᵉ xᵉ yᵉ Hᵉ uᵉ =
    ( ( has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoidᵉ
        ( Mᵉ)
        ( Nᵉ)
        ( mul-Commutative-Monoidᵉ Mᵉ uᵉ yᵉ)) ∘iffᵉ
      ( Hᵉ uᵉ)) ∘iffᵉ
    ( inv-iffᵉ
      ( has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoidᵉ
        ( Mᵉ)
        ( Nᵉ)
        ( mul-Commutative-Monoidᵉ Mᵉ uᵉ xᵉ)))

  saturated-congruence-Normal-Commutative-Submonoidᵉ :
    saturated-congruence-Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ
  pr1ᵉ saturated-congruence-Normal-Commutative-Submonoidᵉ =
    congruence-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ
  pr2ᵉ saturated-congruence-Normal-Commutative-Submonoidᵉ =
    is-saturated-congruence-Normal-Commutative-Submonoidᵉ
```

### The congruence relation of the normal submonoid associated to a congruence relation relates the same elements as the original congruence relation

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Mᵉ : Commutative-Monoidᵉ l1ᵉ) (Rᵉ : saturated-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ)
  where

  normal-submonoid-saturated-congruence-Commutative-Monoidᵉ :
    Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ
  normal-submonoid-saturated-congruence-Commutative-Monoidᵉ =
    normal-submonoid-congruence-Commutative-Monoidᵉ Mᵉ
      ( congruence-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ)

  relate-same-elements-congruence-normal-submonoid-saturated-congruence-Commutative-Monoidᵉ :
    relate-same-elements-saturated-congruence-Commutative-Monoidᵉ Mᵉ
      ( saturated-congruence-Normal-Commutative-Submonoidᵉ Mᵉ
        ( normal-submonoid-saturated-congruence-Commutative-Monoidᵉ))
      ( Rᵉ)
  pr1ᵉ
    ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Commutative-Monoidᵉ
      ( xᵉ)
      ( yᵉ))
    ( Hᵉ) =
    is-saturated-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ xᵉ yᵉ Hᵉ
  pr1ᵉ
    ( pr2ᵉ
      ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Commutative-Monoidᵉ
        ( xᵉ)
        ( yᵉ))
      ( Hᵉ)
      ( uᵉ)) Kᵉ =
    transitive-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ
      ( mul-Commutative-Monoidᵉ Mᵉ uᵉ yᵉ)
      ( mul-Commutative-Monoidᵉ Mᵉ uᵉ xᵉ)
      ( unit-Commutative-Monoidᵉ Mᵉ)
      ( Kᵉ)
      ( mul-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ
        ( refl-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ uᵉ)
        ( symmetric-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ xᵉ yᵉ Hᵉ))
  pr2ᵉ
    ( pr2ᵉ
      ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Commutative-Monoidᵉ
        ( xᵉ)
        ( yᵉ))
      ( Hᵉ)
      ( uᵉ)) Kᵉ =
    transitive-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ
      ( mul-Commutative-Monoidᵉ Mᵉ uᵉ xᵉ)
      ( mul-Commutative-Monoidᵉ Mᵉ uᵉ yᵉ)
      ( unit-Commutative-Monoidᵉ Mᵉ)
      ( Kᵉ)
      ( mul-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ
        ( refl-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ uᵉ)
        ( Hᵉ))
```

### The type of normal submonoids of `M` is a retract of the type of congruence relations of `M`

```agda
is-section-congruence-Normal-Commutative-Submonoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Nᵉ : Normal-Commutative-Submonoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ) →
  ( normal-submonoid-congruence-Commutative-Monoidᵉ Mᵉ
    ( congruence-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ)) ＝ᵉ
  ( Nᵉ)
is-section-congruence-Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ Nᵉ =
  eq-has-same-elements-Normal-Commutative-Submonoidᵉ Mᵉ
    ( normal-submonoid-congruence-Commutative-Monoidᵉ Mᵉ
      ( congruence-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ))
    ( Nᵉ)
    ( has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoidᵉ
      Mᵉ Nᵉ)

normal-submonoid-retract-of-congruence-Commutative-Monoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Commutative-Monoidᵉ l1ᵉ) →
  ( Normal-Commutative-Submonoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ) retract-ofᵉ
  ( congruence-Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ)
pr1ᵉ (normal-submonoid-retract-of-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ) =
  congruence-Normal-Commutative-Submonoidᵉ Mᵉ
pr1ᵉ (pr2ᵉ (normal-submonoid-retract-of-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ)) =
  normal-submonoid-congruence-Commutative-Monoidᵉ Mᵉ
pr2ᵉ (pr2ᵉ (normal-submonoid-retract-of-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ)) =
  is-section-congruence-Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ
```

### The type of normal submonoids of `M` is equivalent to the type of saturated congruence relations on `M`

```agda
is-section-saturated-congruence-Normal-Commutative-Submonoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Nᵉ : Normal-Commutative-Submonoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ) →
  ( normal-submonoid-saturated-congruence-Commutative-Monoidᵉ Mᵉ
    ( saturated-congruence-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ)) ＝ᵉ
  ( Nᵉ)
is-section-saturated-congruence-Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ Nᵉ =
  eq-has-same-elements-Normal-Commutative-Submonoidᵉ Mᵉ
    ( normal-submonoid-saturated-congruence-Commutative-Monoidᵉ Mᵉ
      ( saturated-congruence-Normal-Commutative-Submonoidᵉ Mᵉ Nᵉ))
    ( Nᵉ)
    ( has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoidᵉ
      Mᵉ Nᵉ)

is-retraction-saturated-congruence-Normal-Commutative-Submonoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Rᵉ : saturated-congruence-Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ) →
  ( saturated-congruence-Normal-Commutative-Submonoidᵉ Mᵉ
    ( normal-submonoid-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ)) ＝ᵉ
  ( Rᵉ)
is-retraction-saturated-congruence-Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ Rᵉ =
  eq-relate-same-elements-saturated-congruence-Commutative-Monoidᵉ
    ( Mᵉ)
    ( saturated-congruence-Normal-Commutative-Submonoidᵉ Mᵉ
      ( normal-submonoid-saturated-congruence-Commutative-Monoidᵉ Mᵉ Rᵉ))
    ( Rᵉ)
    ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Commutative-Monoidᵉ
      ( Mᵉ)
      ( Rᵉ))

is-equiv-normal-submonoid-saturated-congruence-Commutative-Monoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Commutative-Monoidᵉ l1ᵉ) →
  is-equivᵉ
    ( normal-submonoid-saturated-congruence-Commutative-Monoidᵉ {l2ᵉ = l1ᵉ ⊔ l2ᵉ} Mᵉ)
is-equiv-normal-submonoid-saturated-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ =
  is-equiv-is-invertibleᵉ
    ( saturated-congruence-Normal-Commutative-Submonoidᵉ Mᵉ)
    ( is-section-saturated-congruence-Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ)
    ( is-retraction-saturated-congruence-Normal-Commutative-Submonoidᵉ l2ᵉ Mᵉ)

equiv-normal-submonoid-saturated-congruence-Commutative-Monoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Commutative-Monoidᵉ l1ᵉ) →
  saturated-congruence-Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ ≃ᵉ
  Normal-Commutative-Submonoidᵉ (l1ᵉ ⊔ l2ᵉ) Mᵉ
pr1ᵉ (equiv-normal-submonoid-saturated-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ) =
  normal-submonoid-saturated-congruence-Commutative-Monoidᵉ Mᵉ
pr2ᵉ (equiv-normal-submonoid-saturated-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ) =
  is-equiv-normal-submonoid-saturated-congruence-Commutative-Monoidᵉ l2ᵉ Mᵉ
```