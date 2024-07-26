# Equivalence relations

```agda
module foundation-core.equivalence-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.inhabited-subtypesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Anᵉ equivalenceᵉ relationᵉ isᵉ aᵉ relationᵉ valuedᵉ in propositions,ᵉ whichᵉ isᵉ
reflexive,symmetric,ᵉ andᵉ transitive.ᵉ

## Definition

```agda
is-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relation-Propᵉ l2ᵉ Aᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-equivalence-relationᵉ Rᵉ =
  is-reflexive-Relation-Propᵉ Rᵉ ×ᵉ
  is-symmetric-Relation-Propᵉ Rᵉ ×ᵉ
  is-transitive-Relation-Propᵉ Rᵉ

equivalence-relationᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
equivalence-relationᵉ lᵉ Aᵉ = Σᵉ (Relation-Propᵉ lᵉ Aᵉ) is-equivalence-relationᵉ

prop-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → equivalence-relationᵉ l2ᵉ Aᵉ → Relation-Propᵉ l2ᵉ Aᵉ
prop-equivalence-relationᵉ = pr1ᵉ

sim-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → equivalence-relationᵉ l2ᵉ Aᵉ → Aᵉ → Aᵉ → UUᵉ l2ᵉ
sim-equivalence-relationᵉ Rᵉ = type-Relation-Propᵉ (prop-equivalence-relationᵉ Rᵉ)

abstract
  is-prop-sim-equivalence-relationᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) (xᵉ yᵉ : Aᵉ) →
    is-propᵉ (sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ)
  is-prop-sim-equivalence-relationᵉ Rᵉ =
    is-prop-type-Relation-Propᵉ (prop-equivalence-relationᵉ Rᵉ)

is-prop-is-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relation-Propᵉ l2ᵉ Aᵉ) →
  is-propᵉ (is-equivalence-relationᵉ Rᵉ)
is-prop-is-equivalence-relationᵉ Rᵉ =
  is-prop-productᵉ
    ( is-prop-is-reflexive-Relation-Propᵉ Rᵉ)
    ( is-prop-productᵉ
      ( is-prop-is-symmetric-Relation-Propᵉ Rᵉ)
      ( is-prop-is-transitive-Relation-Propᵉ Rᵉ))

is-equivalence-relation-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → Relation-Propᵉ l2ᵉ Aᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (is-equivalence-relation-Propᵉ Rᵉ) = is-equivalence-relationᵉ Rᵉ
pr2ᵉ (is-equivalence-relation-Propᵉ Rᵉ) = is-prop-is-equivalence-relationᵉ Rᵉ

is-equivalence-relation-prop-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) →
  is-equivalence-relationᵉ (prop-equivalence-relationᵉ Rᵉ)
is-equivalence-relation-prop-equivalence-relationᵉ Rᵉ = pr2ᵉ Rᵉ

refl-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) →
  is-reflexiveᵉ (sim-equivalence-relationᵉ Rᵉ)
refl-equivalence-relationᵉ Rᵉ =
  pr1ᵉ (is-equivalence-relation-prop-equivalence-relationᵉ Rᵉ)

symmetric-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) →
  is-symmetricᵉ (sim-equivalence-relationᵉ Rᵉ)
symmetric-equivalence-relationᵉ Rᵉ =
  pr1ᵉ (pr2ᵉ (is-equivalence-relation-prop-equivalence-relationᵉ Rᵉ))

transitive-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) → is-transitiveᵉ (sim-equivalence-relationᵉ Rᵉ)
transitive-equivalence-relationᵉ Rᵉ =
  pr2ᵉ (pr2ᵉ (is-equivalence-relation-prop-equivalence-relationᵉ Rᵉ))

inhabited-subtype-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  equivalence-relationᵉ l2ᵉ Aᵉ → Aᵉ → inhabited-subtypeᵉ l2ᵉ Aᵉ
pr1ᵉ (inhabited-subtype-equivalence-relationᵉ Rᵉ xᵉ) = prop-equivalence-relationᵉ Rᵉ xᵉ
pr2ᵉ (inhabited-subtype-equivalence-relationᵉ Rᵉ xᵉ) =
  unit-trunc-Propᵉ (xᵉ ,ᵉ refl-equivalence-relationᵉ Rᵉ xᵉ)
```

## Properties

### Symmetry induces equivalences `R(x,y) ≃ R(y,x)`

```agda
iff-symmetric-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) {xᵉ yᵉ : Aᵉ} →
  sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ ↔ᵉ sim-equivalence-relationᵉ Rᵉ yᵉ xᵉ
pr1ᵉ (iff-symmetric-equivalence-relationᵉ Rᵉ) =
  symmetric-equivalence-relationᵉ Rᵉ _ _
pr2ᵉ (iff-symmetric-equivalence-relationᵉ Rᵉ) =
  symmetric-equivalence-relationᵉ Rᵉ _ _

equiv-symmetric-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) {xᵉ yᵉ : Aᵉ} →
  sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ ≃ᵉ sim-equivalence-relationᵉ Rᵉ yᵉ xᵉ
equiv-symmetric-equivalence-relationᵉ Rᵉ =
  equiv-iff'ᵉ
    ( prop-equivalence-relationᵉ Rᵉ _ _)
    ( prop-equivalence-relationᵉ Rᵉ _ _)
    ( iff-symmetric-equivalence-relationᵉ Rᵉ)
```

### Transitivity induces equivalences `R(y,z) ≃ R(x,z)`

```agda
iff-transitive-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) {xᵉ yᵉ zᵉ : Aᵉ} →
  sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ →
  (sim-equivalence-relationᵉ Rᵉ yᵉ zᵉ ↔ᵉ sim-equivalence-relationᵉ Rᵉ xᵉ zᵉ)
pr1ᵉ (iff-transitive-equivalence-relationᵉ Rᵉ rᵉ) sᵉ =
  transitive-equivalence-relationᵉ Rᵉ _ _ _ sᵉ rᵉ
pr2ᵉ (iff-transitive-equivalence-relationᵉ Rᵉ rᵉ) sᵉ =
  transitive-equivalence-relationᵉ Rᵉ _ _ _
    ( sᵉ)
    ( symmetric-equivalence-relationᵉ Rᵉ _ _ rᵉ)

equiv-transitive-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) {xᵉ yᵉ zᵉ : Aᵉ} →
  sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ →
  (sim-equivalence-relationᵉ Rᵉ yᵉ zᵉ ≃ᵉ sim-equivalence-relationᵉ Rᵉ xᵉ zᵉ)
equiv-transitive-equivalence-relationᵉ Rᵉ rᵉ =
  equiv-iff'ᵉ
    ( prop-equivalence-relationᵉ Rᵉ _ _)
    ( prop-equivalence-relationᵉ Rᵉ _ _)
    ( iff-transitive-equivalence-relationᵉ Rᵉ rᵉ)
```

### Transitivity induces equivalences `R(x,y) ≃ R(x,z)`

```agda
iff-transitive-equivalence-relation'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) {xᵉ yᵉ zᵉ : Aᵉ} →
  sim-equivalence-relationᵉ Rᵉ yᵉ zᵉ →
  (sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ ↔ᵉ sim-equivalence-relationᵉ Rᵉ xᵉ zᵉ)
pr1ᵉ (iff-transitive-equivalence-relation'ᵉ Rᵉ rᵉ) =
  transitive-equivalence-relationᵉ Rᵉ _ _ _ rᵉ
pr2ᵉ (iff-transitive-equivalence-relation'ᵉ Rᵉ rᵉ) =
  transitive-equivalence-relationᵉ Rᵉ _ _ _
    ( symmetric-equivalence-relationᵉ Rᵉ _ _ rᵉ)

equiv-transitive-equivalence-relation'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) {xᵉ yᵉ zᵉ : Aᵉ} →
  sim-equivalence-relationᵉ Rᵉ yᵉ zᵉ →
  (sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ ≃ᵉ sim-equivalence-relationᵉ Rᵉ xᵉ zᵉ)
equiv-transitive-equivalence-relation'ᵉ Rᵉ rᵉ =
  equiv-iff'ᵉ
    ( prop-equivalence-relationᵉ Rᵉ _ _)
    ( prop-equivalence-relationᵉ Rᵉ _ _)
    ( iff-transitive-equivalence-relation'ᵉ Rᵉ rᵉ)
```

## Examples

### The indiscrete equivalence relation on a type

```agda
indiscrete-equivalence-relationᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → equivalence-relationᵉ lzero Aᵉ
pr1ᵉ (indiscrete-equivalence-relationᵉ Aᵉ) xᵉ yᵉ = unit-Propᵉ
pr1ᵉ (pr2ᵉ (indiscrete-equivalence-relationᵉ Aᵉ)) _ = starᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (indiscrete-equivalence-relationᵉ Aᵉ))) _ _ _ = starᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (indiscrete-equivalence-relationᵉ Aᵉ))) _ _ _ _ _ = starᵉ

raise-indiscrete-equivalence-relationᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → equivalence-relationᵉ l2ᵉ Aᵉ
pr1ᵉ (raise-indiscrete-equivalence-relationᵉ lᵉ Aᵉ) xᵉ yᵉ = raise-unit-Propᵉ lᵉ
pr1ᵉ (pr2ᵉ (raise-indiscrete-equivalence-relationᵉ lᵉ Aᵉ)) _ = raise-starᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (raise-indiscrete-equivalence-relationᵉ lᵉ Aᵉ))) _ _ _ = raise-starᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (raise-indiscrete-equivalence-relationᵉ lᵉ Aᵉ))) _ _ _ _ _ =
  raise-starᵉ
```