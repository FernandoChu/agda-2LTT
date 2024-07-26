# Binary relations

```agda
module foundation.binary-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.subtypesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.negationᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Aᵉ **binaryᵉ relation**ᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ familyᵉ ofᵉ typesᵉ `Rᵉ xᵉ y`ᵉ dependingᵉ onᵉ
twoᵉ variablesᵉ `xᵉ yᵉ : A`.ᵉ Inᵉ theᵉ specialᵉ caseᵉ where eachᵉ `Rᵉ xᵉ y`ᵉ isᵉ aᵉ
[proposition](foundation-core.propositions.md),ᵉ weᵉ sayᵉ thatᵉ theᵉ relationᵉ isᵉ
valuedᵉ in propositions.ᵉ Thus,ᵉ weᵉ takeᵉ aᵉ generalᵉ relationᵉ to meanᵉ aᵉ
_proof-relevantᵉ_ relation.ᵉ

## Definition

### Relations valued in types

```agda
Relationᵉ : {l1ᵉ : Level} (lᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc lᵉ)
Relationᵉ lᵉ Aᵉ = Aᵉ → Aᵉ → UUᵉ lᵉ

total-space-Relationᵉ :
  {l1ᵉ lᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → Relationᵉ lᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ lᵉ)
total-space-Relationᵉ {Aᵉ = Aᵉ} Rᵉ = Σᵉ (Aᵉ ×ᵉ Aᵉ) λ (aᵉ ,ᵉ a'ᵉ) → Rᵉ aᵉ a'ᵉ
```

### Relations valued in propositions

```agda
Relation-Propᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
Relation-Propᵉ lᵉ Aᵉ = Aᵉ → Aᵉ → Propᵉ lᵉ

type-Relation-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → Relation-Propᵉ l2ᵉ Aᵉ → Relationᵉ l2ᵉ Aᵉ
type-Relation-Propᵉ Rᵉ xᵉ yᵉ = pr1ᵉ (Rᵉ xᵉ yᵉ)

is-prop-type-Relation-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relation-Propᵉ l2ᵉ Aᵉ) →
  (xᵉ yᵉ : Aᵉ) → is-propᵉ (type-Relation-Propᵉ Rᵉ xᵉ yᵉ)
is-prop-type-Relation-Propᵉ Rᵉ xᵉ yᵉ = pr2ᵉ (Rᵉ xᵉ yᵉ)

total-space-Relation-Propᵉ :
  {lᵉ : Level} {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → Relation-Propᵉ lᵉ Aᵉ → UUᵉ (lᵉ ⊔ l1ᵉ)
total-space-Relation-Propᵉ {Aᵉ = Aᵉ} Rᵉ =
  Σᵉ (Aᵉ ×ᵉ Aᵉ) λ (aᵉ ,ᵉ a'ᵉ) → type-Relation-Propᵉ Rᵉ aᵉ a'ᵉ
```

### The predicate of being a reflexive relation

Aᵉ relationᵉ `R`ᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to beᵉ **reflexive**ᵉ ifᵉ itᵉ comesᵉ equippedᵉ
with aᵉ functionᵉ `(xᵉ : Aᵉ) → Rᵉ xᵉ x`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  is-reflexiveᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-reflexiveᵉ = (xᵉ : Aᵉ) → Rᵉ xᵉ xᵉ
```

### The predicate of being a reflexive relation valued in propositions

Aᵉ relationᵉ `R`ᵉ onᵉ aᵉ typeᵉ `A`ᵉ valuedᵉ in propositionsᵉ isᵉ saidᵉ to beᵉ **reflexive**ᵉ
ifᵉ itsᵉ underlyingᵉ relationᵉ isᵉ reflexiveᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relation-Propᵉ l2ᵉ Aᵉ)
  where

  is-reflexive-Relation-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-reflexive-Relation-Propᵉ = is-reflexiveᵉ (type-Relation-Propᵉ Rᵉ)

  is-prop-is-reflexive-Relation-Propᵉ : is-propᵉ is-reflexive-Relation-Propᵉ
  is-prop-is-reflexive-Relation-Propᵉ =
    is-prop-Πᵉ (λ xᵉ → is-prop-type-Relation-Propᵉ Rᵉ xᵉ xᵉ)
```

### The predicate of being a symmetric relation

Aᵉ relationᵉ `R`ᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to beᵉ **symmetric**ᵉ ifᵉ itᵉ comesᵉ equippedᵉ
with aᵉ functionᵉ `(xᵉ yᵉ : Aᵉ) → Rᵉ xᵉ yᵉ → Rᵉ yᵉ x`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  is-symmetricᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-symmetricᵉ = (xᵉ yᵉ : Aᵉ) → Rᵉ xᵉ yᵉ → Rᵉ yᵉ xᵉ
```

### The predicate of being a symmetric relation valued in propositions

Aᵉ relationᵉ `R`ᵉ onᵉ aᵉ typeᵉ `A`ᵉ valuedᵉ in propositionsᵉ isᵉ saidᵉ to beᵉ **symmetric**ᵉ
ifᵉ itsᵉ underlyingᵉ relationᵉ isᵉ symmetric.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relation-Propᵉ l2ᵉ Aᵉ)
  where

  is-symmetric-Relation-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-symmetric-Relation-Propᵉ = is-symmetricᵉ (type-Relation-Propᵉ Rᵉ)

  is-prop-is-symmetric-Relation-Propᵉ : is-propᵉ is-symmetric-Relation-Propᵉ
  is-prop-is-symmetric-Relation-Propᵉ =
    is-prop-iterated-Πᵉ 3
      ( λ xᵉ yᵉ rᵉ → is-prop-type-Relation-Propᵉ Rᵉ yᵉ xᵉ)
```

### The predicate of being a transitive relation

Aᵉ relationᵉ `R`ᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to beᵉ **transitive**ᵉ ifᵉ itᵉ comesᵉ equippedᵉ
with aᵉ functionᵉ `(xᵉ yᵉ zᵉ : Aᵉ) → Rᵉ yᵉ zᵉ → Rᵉ xᵉ yᵉ → Rᵉ xᵉ z`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  is-transitiveᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-transitiveᵉ = (xᵉ yᵉ zᵉ : Aᵉ) → Rᵉ yᵉ zᵉ → Rᵉ xᵉ yᵉ → Rᵉ xᵉ zᵉ
```

### The predicate of being a transitive relation valued in propositions

Aᵉ relationᵉ `R`ᵉ onᵉ aᵉ typeᵉ `A`ᵉ valuedᵉ in propositionsᵉ isᵉ saidᵉ to beᵉ **transitive**ᵉ
ifᵉ itsᵉ underlyingᵉ relationᵉ isᵉ transitive.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relation-Propᵉ l2ᵉ Aᵉ)
  where

  is-transitive-Relation-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-transitive-Relation-Propᵉ = is-transitiveᵉ (type-Relation-Propᵉ Rᵉ)

  is-prop-is-transitive-Relation-Propᵉ : is-propᵉ is-transitive-Relation-Propᵉ
  is-prop-is-transitive-Relation-Propᵉ =
    is-prop-iterated-Πᵉ 3
      ( λ xᵉ yᵉ zᵉ →
        is-prop-function-typeᵉ
          ( is-prop-function-typeᵉ (is-prop-type-Relation-Propᵉ Rᵉ xᵉ zᵉ)))
```

### The predicate of being an irreflexive relation

Aᵉ relationᵉ `R`ᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to beᵉ **irreflexive**ᵉ ifᵉ itᵉ comesᵉ equippedᵉ
with aᵉ functionᵉ `(xᵉ : Aᵉ) → ¬ᵉ (Rᵉ xᵉ y)`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  is-irreflexiveᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-irreflexiveᵉ = (xᵉ : Aᵉ) → ¬ᵉ (Rᵉ xᵉ xᵉ)
```

### The predicate of being an asymmetric relation

Aᵉ relationᵉ `R`ᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to beᵉ **asymmetric**ᵉ ifᵉ itᵉ comesᵉ equippedᵉ
with aᵉ functionᵉ `(xᵉ yᵉ : Aᵉ) → Rᵉ xᵉ yᵉ → ¬ᵉ (Rᵉ yᵉ x)`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  is-asymmetricᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-asymmetricᵉ = (xᵉ yᵉ : Aᵉ) → Rᵉ xᵉ yᵉ → ¬ᵉ (Rᵉ yᵉ xᵉ)
```

### The predicate of being an antisymmetric relation

Aᵉ relationᵉ `R`ᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to beᵉ **antisymmetric**ᵉ ifᵉ itᵉ comesᵉ
equippedᵉ with aᵉ functionᵉ `(xᵉ yᵉ : Aᵉ) → Rᵉ xᵉ yᵉ → Rᵉ yᵉ xᵉ → xᵉ ＝ᵉ y`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  is-antisymmetricᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-antisymmetricᵉ = (xᵉ yᵉ : Aᵉ) → Rᵉ xᵉ yᵉ → Rᵉ yᵉ xᵉ → xᵉ ＝ᵉ yᵉ
```

### The predicate of being an antisymmetric relation valued in propositions

Aᵉ relationᵉ `R`ᵉ onᵉ aᵉ typeᵉ `A`ᵉ valuedᵉ in propositionsᵉ isᵉ saidᵉ to beᵉ
**antisymmetric**ᵉ ifᵉ itsᵉ underlyingᵉ relationᵉ isᵉ antisymmetric.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relation-Propᵉ l2ᵉ Aᵉ)
  where

  is-antisymmetric-Relation-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-antisymmetric-Relation-Propᵉ = is-antisymmetricᵉ (type-Relation-Propᵉ Rᵉ)
```

## Properties

### Characterization of equality of binary relations

```agda
equiv-Relationᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  Relationᵉ l2ᵉ Aᵉ → Relationᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
equiv-Relationᵉ {Aᵉ = Aᵉ} Rᵉ Sᵉ = (xᵉ yᵉ : Aᵉ) → Rᵉ xᵉ yᵉ ≃ᵉ Sᵉ xᵉ yᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  id-equiv-Relationᵉ : equiv-Relationᵉ Rᵉ Rᵉ
  id-equiv-Relationᵉ xᵉ yᵉ = id-equivᵉ

  is-torsorial-equiv-Relationᵉ :
    is-torsorialᵉ (equiv-Relationᵉ Rᵉ)
  is-torsorial-equiv-Relationᵉ =
    is-torsorial-Eq-Πᵉ
      ( λ xᵉ → is-torsorial-Eq-Πᵉ (λ yᵉ → is-torsorial-equivᵉ (Rᵉ xᵉ yᵉ)))

  equiv-eq-Relationᵉ : (Sᵉ : Relationᵉ l2ᵉ Aᵉ) → (Rᵉ ＝ᵉ Sᵉ) → equiv-Relationᵉ Rᵉ Sᵉ
  equiv-eq-Relationᵉ .Rᵉ reflᵉ = id-equiv-Relationᵉ

  is-equiv-equiv-eq-Relationᵉ :
    (Sᵉ : Relationᵉ l2ᵉ Aᵉ) → is-equivᵉ (equiv-eq-Relationᵉ Sᵉ)
  is-equiv-equiv-eq-Relationᵉ =
    fundamental-theorem-idᵉ is-torsorial-equiv-Relationᵉ equiv-eq-Relationᵉ

  extensionality-Relationᵉ : (Sᵉ : Relationᵉ l2ᵉ Aᵉ) → (Rᵉ ＝ᵉ Sᵉ) ≃ᵉ equiv-Relationᵉ Rᵉ Sᵉ
  pr1ᵉ (extensionality-Relationᵉ Sᵉ) = equiv-eq-Relationᵉ Sᵉ
  pr2ᵉ (extensionality-Relationᵉ Sᵉ) = is-equiv-equiv-eq-Relationᵉ Sᵉ

  eq-equiv-Relationᵉ : (Sᵉ : Relationᵉ l2ᵉ Aᵉ) → equiv-Relationᵉ Rᵉ Sᵉ → (Rᵉ ＝ᵉ Sᵉ)
  eq-equiv-Relationᵉ Sᵉ = map-inv-equivᵉ (extensionality-Relationᵉ Sᵉ)
```

### Characterization of equality of prop-valued binary relations

```agda
relates-same-elements-Relation-Propᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Rᵉ : Relation-Propᵉ l2ᵉ Aᵉ) (Sᵉ : Relation-Propᵉ l3ᵉ Aᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
relates-same-elements-Relation-Propᵉ {Aᵉ = Aᵉ} Rᵉ Sᵉ =
  (xᵉ : Aᵉ) → has-same-elements-subtypeᵉ (Rᵉ xᵉ) (Sᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relation-Propᵉ l2ᵉ Aᵉ)
  where

  refl-relates-same-elements-Relation-Propᵉ :
    relates-same-elements-Relation-Propᵉ Rᵉ Rᵉ
  refl-relates-same-elements-Relation-Propᵉ xᵉ =
    refl-has-same-elements-subtypeᵉ (Rᵉ xᵉ)

  is-torsorial-relates-same-elements-Relation-Propᵉ :
    is-torsorialᵉ (relates-same-elements-Relation-Propᵉ Rᵉ)
  is-torsorial-relates-same-elements-Relation-Propᵉ =
    is-torsorial-Eq-Πᵉ (λ xᵉ → is-torsorial-has-same-elements-subtypeᵉ (Rᵉ xᵉ))

  relates-same-elements-eq-Relation-Propᵉ :
    (Sᵉ : Relation-Propᵉ l2ᵉ Aᵉ) →
    (Rᵉ ＝ᵉ Sᵉ) → relates-same-elements-Relation-Propᵉ Rᵉ Sᵉ
  relates-same-elements-eq-Relation-Propᵉ .Rᵉ reflᵉ =
    refl-relates-same-elements-Relation-Propᵉ

  is-equiv-relates-same-elements-eq-Relation-Propᵉ :
    (Sᵉ : Relation-Propᵉ l2ᵉ Aᵉ) →
    is-equivᵉ (relates-same-elements-eq-Relation-Propᵉ Sᵉ)
  is-equiv-relates-same-elements-eq-Relation-Propᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-relates-same-elements-Relation-Propᵉ
      relates-same-elements-eq-Relation-Propᵉ

  extensionality-Relation-Propᵉ :
    (Sᵉ : Relation-Propᵉ l2ᵉ Aᵉ) →
    (Rᵉ ＝ᵉ Sᵉ) ≃ᵉ relates-same-elements-Relation-Propᵉ Rᵉ Sᵉ
  pr1ᵉ (extensionality-Relation-Propᵉ Sᵉ) =
    relates-same-elements-eq-Relation-Propᵉ Sᵉ
  pr2ᵉ (extensionality-Relation-Propᵉ Sᵉ) =
    is-equiv-relates-same-elements-eq-Relation-Propᵉ Sᵉ

  eq-relates-same-elements-Relation-Propᵉ :
    (Sᵉ : Relation-Propᵉ l2ᵉ Aᵉ) →
    relates-same-elements-Relation-Propᵉ Rᵉ Sᵉ → (Rᵉ ＝ᵉ Sᵉ)
  eq-relates-same-elements-Relation-Propᵉ Sᵉ =
    map-inv-equivᵉ (extensionality-Relation-Propᵉ Sᵉ)
```

### Asymmetric relations are irreflexive

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  is-irreflexive-is-asymmetricᵉ : is-asymmetricᵉ Rᵉ → is-irreflexiveᵉ Rᵉ
  is-irreflexive-is-asymmetricᵉ Hᵉ xᵉ rᵉ = Hᵉ xᵉ xᵉ rᵉ rᵉ
```

### Asymmetric relations are antisymmetric

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  is-antisymmetric-is-asymmetricᵉ : is-asymmetricᵉ Rᵉ → is-antisymmetricᵉ Rᵉ
  is-antisymmetric-is-asymmetricᵉ Hᵉ xᵉ yᵉ rᵉ sᵉ = ex-falsoᵉ (Hᵉ xᵉ yᵉ rᵉ sᵉ)
```

## See also

-ᵉ [Largeᵉ binaryᵉ relations](foundation.large-binary-relations.mdᵉ)