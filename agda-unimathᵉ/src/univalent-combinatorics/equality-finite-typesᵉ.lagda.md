# Equality in finite types

```agda
module univalent-combinatorics.equality-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.decidable-equalityᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.decidable-propositionsᵉ
open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Anyᵉ finiteᵉ typeᵉ isᵉ aᵉ setᵉ becauseᵉ itᵉ isᵉ merelyᵉ equivalentᵉ to aᵉ standardᵉ finiteᵉ
type.ᵉ Moreover,ᵉ anyᵉ finiteᵉ typeᵉ hasᵉ decidableᵉ equality.ᵉ Inᵉ particular,ᵉ thisᵉ
impliesᵉ thatᵉ theᵉ typeᵉ ofᵉ identificationsᵉ betweenᵉ anyᵉ twoᵉ elementsᵉ in aᵉ finiteᵉ
typeᵉ isᵉ finite.ᵉ

## Properties

### Any finite type has decidable equality

```agda
has-decidable-equality-is-finiteᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → is-finiteᵉ Xᵉ → has-decidable-equalityᵉ Xᵉ
has-decidable-equality-is-finiteᵉ {l1ᵉ} {Xᵉ} is-finite-Xᵉ =
  apply-universal-property-trunc-Propᵉ is-finite-Xᵉ
    ( has-decidable-equality-Propᵉ Xᵉ)
    ( λ eᵉ →
      has-decidable-equality-equiv'ᵉ
        ( equiv-countᵉ eᵉ)
        ( has-decidable-equality-Finᵉ (number-of-elements-countᵉ eᵉ)))
```

### Any type of finite cardinality has decidable equality

```agda
has-decidable-equality-has-cardinalityᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (kᵉ : ℕᵉ) →
  has-cardinalityᵉ kᵉ Xᵉ → has-decidable-equalityᵉ Xᵉ
has-decidable-equality-has-cardinalityᵉ {l1ᵉ} {Xᵉ} kᵉ Hᵉ =
  apply-universal-property-trunc-Propᵉ Hᵉ
    ( has-decidable-equality-Propᵉ Xᵉ)
    ( λ eᵉ → has-decidable-equality-equiv'ᵉ eᵉ (has-decidable-equality-Finᵉ kᵉ))
```

### The type of identifications between any two elements in a finite type is finite

```agda
abstract
  is-finite-eqᵉ :
    {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} →
    has-decidable-equalityᵉ Xᵉ → {xᵉ yᵉ : Xᵉ} → is-finiteᵉ (Idᵉ xᵉ yᵉ)
  is-finite-eqᵉ dᵉ {xᵉ} {yᵉ} = is-finite-countᵉ (count-eqᵉ dᵉ xᵉ yᵉ)

is-finite-eq-𝔽ᵉ :
  {lᵉ : Level} → (Xᵉ : 𝔽ᵉ lᵉ) {xᵉ yᵉ : type-𝔽ᵉ Xᵉ} → is-finiteᵉ (xᵉ ＝ᵉ yᵉ)
is-finite-eq-𝔽ᵉ Xᵉ =
  is-finite-eqᵉ (has-decidable-equality-is-finiteᵉ (is-finite-type-𝔽ᵉ Xᵉ))

Id-𝔽ᵉ : {lᵉ : Level} → (Xᵉ : 𝔽ᵉ lᵉ) (xᵉ yᵉ : type-𝔽ᵉ Xᵉ) → 𝔽ᵉ lᵉ
pr1ᵉ (Id-𝔽ᵉ Xᵉ xᵉ yᵉ) = Idᵉ xᵉ yᵉ
pr2ᵉ (Id-𝔽ᵉ Xᵉ xᵉ yᵉ) = is-finite-eq-𝔽ᵉ Xᵉ
```