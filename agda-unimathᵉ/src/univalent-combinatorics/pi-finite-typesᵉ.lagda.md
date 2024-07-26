# π-finite types

```agda
module univalent-combinatorics.pi-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.0-connected-typesᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.constant-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.equality-coproduct-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fiber-inclusionsᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-set-truncationᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.maybeᵉ
open import foundation.mere-equalityᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.set-truncationsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-coproduct-typesᵉ
open import foundation.universal-property-empty-typeᵉ
open import foundation.universal-property-unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import univalent-combinatorics.cartesian-product-typesᵉ
open import univalent-combinatorics.coproduct-typesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.dependent-function-typesᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.distributivity-of-set-truncation-over-finite-productsᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.finitely-presented-typesᵉ
open import univalent-combinatorics.function-typesᵉ
open import univalent-combinatorics.image-of-mapsᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ `π_n`-finiteᵉ ifᵉ itᵉ hasᵉ finitelyᵉ manyᵉ connectedᵉ componentsᵉ andᵉ allᵉ ofᵉ
itsᵉ homotopyᵉ groupsᵉ upᵉ to levelᵉ `n`ᵉ atᵉ allᵉ baseᵉ pointsᵉ areᵉ finite.ᵉ

## Definition

### Locally finite types

```agda
is-locally-finite-Propᵉ :
  {lᵉ : Level} → UUᵉ lᵉ → Propᵉ lᵉ
is-locally-finite-Propᵉ Aᵉ =
  Π-Propᵉ Aᵉ (λ xᵉ → Π-Propᵉ Aᵉ (λ yᵉ → is-finite-Propᵉ (Idᵉ xᵉ yᵉ)))

is-locally-finiteᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
is-locally-finiteᵉ Aᵉ = type-Propᵉ (is-locally-finite-Propᵉ Aᵉ)

is-prop-is-locally-finiteᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → is-propᵉ (is-locally-finiteᵉ Aᵉ)
is-prop-is-locally-finiteᵉ Aᵉ = is-prop-type-Propᵉ (is-locally-finite-Propᵉ Aᵉ)
```

### Truncated π-finite types

```agda
is-truncated-π-finite-Propᵉ : {lᵉ : Level} (kᵉ : ℕᵉ) → UUᵉ lᵉ → Propᵉ lᵉ
is-truncated-π-finite-Propᵉ zero-ℕᵉ Xᵉ = is-finite-Propᵉ Xᵉ
is-truncated-π-finite-Propᵉ (succ-ℕᵉ kᵉ) Xᵉ =
  product-Propᵉ
    ( is-finite-Propᵉ (type-trunc-Setᵉ Xᵉ))
    ( Π-Propᵉ Xᵉ
      ( λ xᵉ → Π-Propᵉ Xᵉ (λ yᵉ → is-truncated-π-finite-Propᵉ kᵉ (Idᵉ xᵉ yᵉ))))

is-truncated-π-finiteᵉ : {lᵉ : Level} (kᵉ : ℕᵉ) → UUᵉ lᵉ → UUᵉ lᵉ
is-truncated-π-finiteᵉ kᵉ Aᵉ =
  type-Propᵉ (is-truncated-π-finite-Propᵉ kᵉ Aᵉ)
```

### Types with finitely many connected components

```agda
has-finite-connected-components-Propᵉ : {lᵉ : Level} → UUᵉ lᵉ → Propᵉ lᵉ
has-finite-connected-components-Propᵉ Aᵉ =
  is-finite-Propᵉ (type-trunc-Setᵉ Aᵉ)

has-finite-connected-componentsᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
has-finite-connected-componentsᵉ Aᵉ =
  type-Propᵉ (has-finite-connected-components-Propᵉ Aᵉ)

number-of-connected-componentsᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → has-finite-connected-componentsᵉ Xᵉ → ℕᵉ
number-of-connected-componentsᵉ Hᵉ = number-of-elements-is-finiteᵉ Hᵉ

mere-equiv-number-of-connected-componentsᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (Hᵉ : has-finite-connected-componentsᵉ Xᵉ) →
  mere-equivᵉ
    ( Finᵉ (number-of-connected-componentsᵉ Hᵉ))
    ( type-trunc-Setᵉ Xᵉ)
mere-equiv-number-of-connected-componentsᵉ Hᵉ =
  mere-equiv-is-finiteᵉ Hᵉ
```

### π-finite types

```agda
is-π-finite-Propᵉ : {lᵉ : Level} (kᵉ : ℕᵉ) → UUᵉ lᵉ → Propᵉ lᵉ
is-π-finite-Propᵉ zero-ℕᵉ Xᵉ = has-finite-connected-components-Propᵉ Xᵉ
is-π-finite-Propᵉ (succ-ℕᵉ kᵉ) Xᵉ =
  product-Propᵉ
    ( is-π-finite-Propᵉ zero-ℕᵉ Xᵉ)
    ( Π-Propᵉ Xᵉ (λ xᵉ → Π-Propᵉ Xᵉ (λ yᵉ → is-π-finite-Propᵉ kᵉ (Idᵉ xᵉ yᵉ))))

is-π-finiteᵉ : {lᵉ : Level} (kᵉ : ℕᵉ) → UUᵉ lᵉ → UUᵉ lᵉ
is-π-finiteᵉ kᵉ Xᵉ = type-Propᵉ (is-π-finite-Propᵉ kᵉ Xᵉ)

is-prop-is-π-finiteᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : UUᵉ lᵉ) → is-propᵉ (is-π-finiteᵉ kᵉ Xᵉ)
is-prop-is-π-finiteᵉ kᵉ Xᵉ =
  is-prop-type-Propᵉ (is-π-finite-Propᵉ kᵉ Xᵉ)

π-Finiteᵉ : (lᵉ : Level) (kᵉ : ℕᵉ) → UUᵉ (lsuc lᵉ)
π-Finiteᵉ lᵉ kᵉ = Σᵉ (UUᵉ lᵉ) (is-π-finiteᵉ kᵉ)

type-π-Finiteᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) → π-Finiteᵉ lᵉ kᵉ → UUᵉ lᵉ
type-π-Finiteᵉ kᵉ = pr1ᵉ

is-π-finite-type-π-Finiteᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Aᵉ : π-Finiteᵉ lᵉ kᵉ) →
  is-π-finiteᵉ kᵉ (type-π-Finiteᵉ {lᵉ} kᵉ Aᵉ)
is-π-finite-type-π-Finiteᵉ kᵉ = pr2ᵉ
```

## Properties

### Locally finite types are closed under equivalences

```agda
is-locally-finite-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
  is-locally-finiteᵉ Bᵉ → is-locally-finiteᵉ Aᵉ
is-locally-finite-equivᵉ eᵉ fᵉ xᵉ yᵉ =
  is-finite-equiv'ᵉ (equiv-apᵉ eᵉ xᵉ yᵉ) (fᵉ (map-equivᵉ eᵉ xᵉ) (map-equivᵉ eᵉ yᵉ))

is-locally-finite-equiv'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
  is-locally-finiteᵉ Aᵉ → is-locally-finiteᵉ Bᵉ
is-locally-finite-equiv'ᵉ eᵉ = is-locally-finite-equivᵉ (inv-equivᵉ eᵉ)
```

### Types with decidable equality are locally finite

```agda
is-locally-finite-has-decidable-equalityᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → has-decidable-equalityᵉ Aᵉ → is-locally-finiteᵉ Aᵉ
is-locally-finite-has-decidable-equalityᵉ dᵉ xᵉ yᵉ = is-finite-eqᵉ dᵉ
```

### Any proposition is locally finite

```agda
is-locally-finite-is-propᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-propᵉ Aᵉ → is-locally-finiteᵉ Aᵉ
is-locally-finite-is-propᵉ Hᵉ xᵉ yᵉ = is-finite-is-contrᵉ (Hᵉ xᵉ yᵉ)
```

### Any contractible type is locally finite

```agda
is-locally-finite-is-contrᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-contrᵉ Aᵉ → is-locally-finiteᵉ Aᵉ
is-locally-finite-is-contrᵉ Hᵉ =
  is-locally-finite-is-propᵉ (is-prop-is-contrᵉ Hᵉ)

is-locally-finite-unitᵉ : is-locally-finiteᵉ unitᵉ
is-locally-finite-unitᵉ = is-locally-finite-is-contrᵉ is-contr-unitᵉ
```

### Any empty type is locally finite

```agda
is-locally-finite-is-emptyᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-emptyᵉ Aᵉ → is-locally-finiteᵉ Aᵉ
is-locally-finite-is-emptyᵉ Hᵉ = is-locally-finite-is-propᵉ (λ xᵉ → ex-falsoᵉ (Hᵉ xᵉ))

is-locally-finite-emptyᵉ : is-locally-finiteᵉ emptyᵉ
is-locally-finite-emptyᵉ = is-locally-finite-is-emptyᵉ idᵉ
```

### π-finite types are closed under equivalences

```agda
is-π-finite-equivᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
  is-π-finiteᵉ kᵉ Bᵉ → is-π-finiteᵉ kᵉ Aᵉ
is-π-finite-equivᵉ zero-ℕᵉ eᵉ Hᵉ =
  is-finite-equiv'ᵉ (equiv-trunc-Setᵉ eᵉ) Hᵉ
pr1ᵉ (is-π-finite-equivᵉ (succ-ℕᵉ kᵉ) eᵉ Hᵉ) = is-π-finite-equivᵉ zero-ℕᵉ eᵉ (pr1ᵉ Hᵉ)
pr2ᵉ (is-π-finite-equivᵉ (succ-ℕᵉ kᵉ) eᵉ Hᵉ) aᵉ bᵉ =
  is-π-finite-equivᵉ kᵉ
    ( equiv-apᵉ eᵉ aᵉ bᵉ)
    ( pr2ᵉ Hᵉ (map-equivᵉ eᵉ aᵉ) (map-equivᵉ eᵉ bᵉ))

is-π-finite-equiv'ᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
  is-π-finiteᵉ kᵉ Aᵉ → is-π-finiteᵉ kᵉ Bᵉ
is-π-finite-equiv'ᵉ kᵉ eᵉ = is-π-finite-equivᵉ kᵉ (inv-equivᵉ eᵉ)
```

### The empty type is π-finite

```agda
is-π-finite-emptyᵉ : (kᵉ : ℕᵉ) → is-π-finiteᵉ kᵉ emptyᵉ
is-π-finite-emptyᵉ zero-ℕᵉ =
  is-finite-equivᵉ equiv-unit-trunc-empty-Setᵉ is-finite-emptyᵉ
pr1ᵉ (is-π-finite-emptyᵉ (succ-ℕᵉ kᵉ)) = is-π-finite-emptyᵉ zero-ℕᵉ
pr2ᵉ (is-π-finite-emptyᵉ (succ-ℕᵉ kᵉ)) = ind-emptyᵉ

empty-π-Finiteᵉ : (kᵉ : ℕᵉ) → π-Finiteᵉ lzero kᵉ
pr1ᵉ (empty-π-Finiteᵉ kᵉ) = emptyᵉ
pr2ᵉ (empty-π-Finiteᵉ kᵉ) = is-π-finite-emptyᵉ kᵉ
```

### Any empty type is π-finite

```agda
is-π-finite-is-emptyᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} → is-emptyᵉ Aᵉ → is-π-finiteᵉ kᵉ Aᵉ
is-π-finite-is-emptyᵉ zero-ℕᵉ fᵉ =
  is-finite-is-emptyᵉ (is-empty-trunc-Setᵉ fᵉ)
pr1ᵉ (is-π-finite-is-emptyᵉ (succ-ℕᵉ kᵉ) fᵉ) = is-π-finite-is-emptyᵉ zero-ℕᵉ fᵉ
pr2ᵉ (is-π-finite-is-emptyᵉ (succ-ℕᵉ kᵉ) fᵉ) aᵉ = ex-falsoᵉ (fᵉ aᵉ)
```

### Any contractible type is π-finite

```agda
is-π-finite-is-contrᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} → is-contrᵉ Aᵉ → is-π-finiteᵉ kᵉ Aᵉ
is-π-finite-is-contrᵉ zero-ℕᵉ Hᵉ =
  is-finite-is-contrᵉ (is-contr-trunc-Setᵉ Hᵉ)
pr1ᵉ (is-π-finite-is-contrᵉ (succ-ℕᵉ kᵉ) Hᵉ) = is-π-finite-is-contrᵉ zero-ℕᵉ Hᵉ
pr2ᵉ (is-π-finite-is-contrᵉ (succ-ℕᵉ kᵉ) Hᵉ) xᵉ yᵉ =
  is-π-finite-is-contrᵉ kᵉ ( is-prop-is-contrᵉ Hᵉ xᵉ yᵉ)
```

### The unit type is π-finite

```agda
is-π-finite-unitᵉ :
  (kᵉ : ℕᵉ) → is-π-finiteᵉ kᵉ unitᵉ
is-π-finite-unitᵉ kᵉ = is-π-finite-is-contrᵉ kᵉ is-contr-unitᵉ

unit-π-Finiteᵉ : (kᵉ : ℕᵉ) → π-Finiteᵉ lzero kᵉ
pr1ᵉ (unit-π-Finiteᵉ kᵉ) = unitᵉ
pr2ᵉ (unit-π-Finiteᵉ kᵉ) = is-π-finite-unitᵉ kᵉ
```

### Coproducts of π-finite types are π-finite

```agda
is-π-finite-coproductᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-π-finiteᵉ kᵉ Aᵉ → is-π-finiteᵉ kᵉ Bᵉ →
  is-π-finiteᵉ kᵉ (Aᵉ +ᵉ Bᵉ)
is-π-finite-coproductᵉ zero-ℕᵉ Hᵉ Kᵉ =
  is-finite-equiv'ᵉ
    ( equiv-distributive-trunc-coproduct-Setᵉ _ _)
    ( is-finite-coproductᵉ Hᵉ Kᵉ)
pr1ᵉ (is-π-finite-coproductᵉ (succ-ℕᵉ kᵉ) Hᵉ Kᵉ) =
  is-π-finite-coproductᵉ zero-ℕᵉ (pr1ᵉ Hᵉ) (pr1ᵉ Kᵉ)
pr2ᵉ (is-π-finite-coproductᵉ (succ-ℕᵉ kᵉ) Hᵉ Kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) =
  is-π-finite-equivᵉ kᵉ
    ( compute-eq-coproduct-inl-inlᵉ xᵉ yᵉ)
    ( pr2ᵉ Hᵉ xᵉ yᵉ)
pr2ᵉ (is-π-finite-coproductᵉ (succ-ℕᵉ kᵉ) Hᵉ Kᵉ) (inlᵉ xᵉ) (inrᵉ yᵉ) =
  is-π-finite-equivᵉ kᵉ
    ( compute-eq-coproduct-inl-inrᵉ xᵉ yᵉ)
    ( is-π-finite-emptyᵉ kᵉ)
pr2ᵉ (is-π-finite-coproductᵉ (succ-ℕᵉ kᵉ) Hᵉ Kᵉ) (inrᵉ xᵉ) (inlᵉ yᵉ) =
  is-π-finite-equivᵉ kᵉ
    ( compute-eq-coproduct-inr-inlᵉ xᵉ yᵉ)
    ( is-π-finite-emptyᵉ kᵉ)
pr2ᵉ (is-π-finite-coproductᵉ (succ-ℕᵉ kᵉ) Hᵉ Kᵉ) (inrᵉ xᵉ) (inrᵉ yᵉ) =
  is-π-finite-equivᵉ kᵉ
    ( compute-eq-coproduct-inr-inrᵉ xᵉ yᵉ)
    ( pr2ᵉ Kᵉ xᵉ yᵉ)

coproduct-π-Finiteᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) →
  π-Finiteᵉ l1ᵉ kᵉ → π-Finiteᵉ l2ᵉ kᵉ → π-Finiteᵉ (l1ᵉ ⊔ l2ᵉ) kᵉ
pr1ᵉ (coproduct-π-Finiteᵉ kᵉ Aᵉ Bᵉ) = (type-π-Finiteᵉ kᵉ Aᵉ +ᵉ type-π-Finiteᵉ kᵉ Bᵉ)
pr2ᵉ (coproduct-π-Finiteᵉ kᵉ Aᵉ Bᵉ) =
  is-π-finite-coproductᵉ kᵉ
    ( is-π-finite-type-π-Finiteᵉ kᵉ Aᵉ)
    ( is-π-finite-type-π-Finiteᵉ kᵉ Bᵉ)
```

### `Maybe A` of any π-finite type `A` is π-finite

```agda
Maybe-π-Finiteᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) → π-Finiteᵉ lᵉ kᵉ → π-Finiteᵉ lᵉ kᵉ
Maybe-π-Finiteᵉ kᵉ Aᵉ =
  coproduct-π-Finiteᵉ kᵉ Aᵉ (unit-π-Finiteᵉ kᵉ)

is-π-finite-Maybeᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} →
  is-π-finiteᵉ kᵉ Aᵉ → is-π-finiteᵉ kᵉ (Maybeᵉ Aᵉ)
is-π-finite-Maybeᵉ kᵉ Hᵉ =
  is-π-finite-coproductᵉ kᵉ Hᵉ (is-π-finite-unitᵉ kᵉ)
```

### Any stanadard finite type is π-finite

```agda
is-π-finite-Finᵉ :
  (kᵉ nᵉ : ℕᵉ) → is-π-finiteᵉ kᵉ (Finᵉ nᵉ)
is-π-finite-Finᵉ kᵉ zero-ℕᵉ =
  is-π-finite-emptyᵉ kᵉ
is-π-finite-Finᵉ kᵉ (succ-ℕᵉ nᵉ) =
  is-π-finite-Maybeᵉ kᵉ (is-π-finite-Finᵉ kᵉ nᵉ)

Fin-π-Finiteᵉ : (kᵉ : ℕᵉ) (nᵉ : ℕᵉ) → π-Finiteᵉ lzero kᵉ
pr1ᵉ (Fin-π-Finiteᵉ kᵉ nᵉ) = Finᵉ nᵉ
pr2ᵉ (Fin-π-Finiteᵉ kᵉ nᵉ) = is-π-finite-Finᵉ kᵉ nᵉ
```

### Any type equipped with a counting is π-finite

```agda
is-π-finite-countᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} → countᵉ Aᵉ → is-π-finiteᵉ kᵉ Aᵉ
is-π-finite-countᵉ kᵉ (nᵉ ,ᵉ eᵉ) =
  is-π-finite-equiv'ᵉ kᵉ eᵉ (is-π-finite-Finᵉ kᵉ nᵉ)
```

### Any finite type is π-finite

```agda
is-π-finite-is-finiteᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} → is-finiteᵉ Aᵉ → is-π-finiteᵉ kᵉ Aᵉ
is-π-finite-is-finiteᵉ kᵉ {Aᵉ} Hᵉ =
  apply-universal-property-trunc-Propᵉ Hᵉ
    ( is-π-finite-Propᵉ kᵉ Aᵉ)
    ( is-π-finite-countᵉ kᵉ)

π-finite-𝔽ᵉ : {lᵉ : Level} (kᵉ : ℕᵉ) → 𝔽ᵉ lᵉ → π-Finiteᵉ lᵉ kᵉ
pr1ᵉ (π-finite-𝔽ᵉ kᵉ Aᵉ) = type-𝔽ᵉ Aᵉ
pr2ᵉ (π-finite-𝔽ᵉ kᵉ Aᵉ) = is-π-finite-is-finiteᵉ kᵉ (is-finite-type-𝔽ᵉ Aᵉ)
```

### Any 0-connected type has finitely many connected components

```agda
has-finite-connected-components-is-0-connectedᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
  is-0-connectedᵉ Aᵉ → has-finite-connected-componentsᵉ Aᵉ
has-finite-connected-components-is-0-connectedᵉ Cᵉ =
  is-finite-is-contrᵉ Cᵉ
```

### The type of all `n`-element types in `UU l` is π-finite

```agda
is-π-finite-UU-Finᵉ :
  {lᵉ : Level} (kᵉ nᵉ : ℕᵉ) → is-π-finiteᵉ kᵉ (UU-Finᵉ lᵉ nᵉ)
is-π-finite-UU-Finᵉ zero-ℕᵉ nᵉ =
  has-finite-connected-components-is-0-connectedᵉ
    ( is-0-connected-UU-Finᵉ nᵉ)
pr1ᵉ (is-π-finite-UU-Finᵉ (succ-ℕᵉ kᵉ) nᵉ) = is-π-finite-UU-Finᵉ zero-ℕᵉ nᵉ
pr2ᵉ (is-π-finite-UU-Finᵉ (succ-ℕᵉ kᵉ) nᵉ) xᵉ yᵉ =
  is-π-finite-equivᵉ kᵉ
    ( equiv-equiv-eq-UU-Finᵉ nᵉ xᵉ yᵉ)
    ( is-π-finite-is-finiteᵉ kᵉ
      ( is-finite-≃ᵉ
        ( is-finite-has-finite-cardinalityᵉ (nᵉ ,ᵉ (pr2ᵉ xᵉ)))
        ( is-finite-has-finite-cardinalityᵉ (nᵉ ,ᵉ (pr2ᵉ yᵉ)))))

is-finite-has-finite-connected-componentsᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
  is-setᵉ Aᵉ → has-finite-connected-componentsᵉ Aᵉ → is-finiteᵉ Aᵉ
is-finite-has-finite-connected-componentsᵉ Hᵉ =
  is-finite-equiv'ᵉ (equiv-unit-trunc-Setᵉ (ᵉ_ ,ᵉ Hᵉ))

has-finite-connected-components-is-π-finiteᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} →
  is-π-finiteᵉ kᵉ Aᵉ → has-finite-connected-componentsᵉ Aᵉ
has-finite-connected-components-is-π-finiteᵉ zero-ℕᵉ Hᵉ = Hᵉ
has-finite-connected-components-is-π-finiteᵉ (succ-ℕᵉ kᵉ) Hᵉ = pr1ᵉ Hᵉ

is-π-finite-is-π-finite-succ-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} →
  is-π-finiteᵉ (succ-ℕᵉ kᵉ) Aᵉ → is-π-finiteᵉ kᵉ Aᵉ
is-π-finite-is-π-finite-succ-ℕᵉ zero-ℕᵉ Hᵉ =
  has-finite-connected-components-is-π-finiteᵉ 1 Hᵉ
pr1ᵉ (is-π-finite-is-π-finite-succ-ℕᵉ (succ-ℕᵉ kᵉ) Hᵉ) =
  has-finite-connected-components-is-π-finiteᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) Hᵉ
pr2ᵉ (is-π-finite-is-π-finite-succ-ℕᵉ (succ-ℕᵉ kᵉ) Hᵉ) xᵉ yᵉ =
  is-π-finite-is-π-finite-succ-ℕᵉ kᵉ (pr2ᵉ Hᵉ xᵉ yᵉ)

is-π-finite-one-is-π-finite-succ-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} →
  is-π-finiteᵉ (succ-ℕᵉ kᵉ) Aᵉ → is-π-finiteᵉ 1 Aᵉ
is-π-finite-one-is-π-finite-succ-ℕᵉ zero-ℕᵉ Hᵉ = Hᵉ
is-π-finite-one-is-π-finite-succ-ℕᵉ (succ-ℕᵉ kᵉ) Hᵉ =
  is-π-finite-one-is-π-finite-succ-ℕᵉ kᵉ
    ( is-π-finite-is-π-finite-succ-ℕᵉ (succ-ℕᵉ kᵉ) Hᵉ)

is-finite-is-π-finiteᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} → is-setᵉ Aᵉ →
  is-π-finiteᵉ kᵉ Aᵉ → is-finiteᵉ Aᵉ
is-finite-is-π-finiteᵉ kᵉ Hᵉ Kᵉ =
  is-finite-equiv'ᵉ
    ( equiv-unit-trunc-Setᵉ (ᵉ_ ,ᵉ Hᵉ))
    ( has-finite-connected-components-is-π-finiteᵉ kᵉ Kᵉ)

is-truncated-π-finite-is-π-finiteᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} → is-truncᵉ (truncation-level-ℕᵉ kᵉ) Aᵉ →
  is-π-finiteᵉ kᵉ Aᵉ → is-truncated-π-finiteᵉ kᵉ Aᵉ
is-truncated-π-finite-is-π-finiteᵉ zero-ℕᵉ Hᵉ Kᵉ =
  is-finite-is-π-finiteᵉ zero-ℕᵉ Hᵉ Kᵉ
pr1ᵉ (is-truncated-π-finite-is-π-finiteᵉ (succ-ℕᵉ kᵉ) Hᵉ Kᵉ) = pr1ᵉ Kᵉ
pr2ᵉ (is-truncated-π-finite-is-π-finiteᵉ (succ-ℕᵉ kᵉ) Hᵉ Kᵉ) xᵉ yᵉ =
  is-truncated-π-finite-is-π-finiteᵉ kᵉ (Hᵉ xᵉ yᵉ) (pr2ᵉ Kᵉ xᵉ yᵉ)

is-π-finite-is-truncated-π-finiteᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} →
  is-truncated-π-finiteᵉ kᵉ Aᵉ → is-π-finiteᵉ kᵉ Aᵉ
is-π-finite-is-truncated-π-finiteᵉ zero-ℕᵉ Hᵉ =
  is-finite-equivᵉ
    ( equiv-unit-trunc-Setᵉ (ᵉ_ ,ᵉ (is-set-is-finiteᵉ Hᵉ)))
    ( Hᵉ)
pr1ᵉ (is-π-finite-is-truncated-π-finiteᵉ (succ-ℕᵉ kᵉ) Hᵉ) = pr1ᵉ Hᵉ
pr2ᵉ (is-π-finite-is-truncated-π-finiteᵉ (succ-ℕᵉ kᵉ) Hᵉ) xᵉ yᵉ =
  is-π-finite-is-truncated-π-finiteᵉ kᵉ (pr2ᵉ Hᵉ xᵉ yᵉ)
```

### Proposition 1.5

#### The dependent product of locally finite types

```agda
is-locally-finite-productᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-locally-finiteᵉ Aᵉ → is-locally-finiteᵉ Bᵉ → is-locally-finiteᵉ (Aᵉ ×ᵉ Bᵉ)
is-locally-finite-productᵉ fᵉ gᵉ xᵉ yᵉ =
  is-finite-equivᵉ
    ( equiv-eq-pairᵉ xᵉ yᵉ)
    ( is-finite-productᵉ (fᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ)) (gᵉ (pr2ᵉ xᵉ) (pr2ᵉ yᵉ)))

is-locally-finite-Π-Finᵉ :
  {l1ᵉ : Level} (kᵉ : ℕᵉ) {Bᵉ : Finᵉ kᵉ → UUᵉ l1ᵉ} →
  ((xᵉ : Finᵉ kᵉ) → is-locally-finiteᵉ (Bᵉ xᵉ)) →
  is-locally-finiteᵉ ((xᵉ : Finᵉ kᵉ) → Bᵉ xᵉ)
is-locally-finite-Π-Finᵉ {l1ᵉ} zero-ℕᵉ {Bᵉ} fᵉ =
  is-locally-finite-is-contrᵉ (dependent-universal-property-empty'ᵉ Bᵉ)
is-locally-finite-Π-Finᵉ {l1ᵉ} (succ-ℕᵉ kᵉ) {Bᵉ} fᵉ =
  is-locally-finite-equivᵉ
    ( equiv-dependent-universal-property-coproductᵉ Bᵉ)
    ( is-locally-finite-productᵉ
      ( is-locally-finite-Π-Finᵉ kᵉ (λ xᵉ → fᵉ (inlᵉ xᵉ)))
      ( is-locally-finite-equivᵉ
        ( equiv-dependent-universal-property-unitᵉ (Bᵉ ∘ᵉ inrᵉ))
        ( fᵉ (inrᵉ starᵉ))))

is-locally-finite-Π-countᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} → countᵉ Aᵉ →
  ((xᵉ : Aᵉ) → is-locally-finiteᵉ (Bᵉ xᵉ)) → is-locally-finiteᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)
is-locally-finite-Π-countᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} (kᵉ ,ᵉ eᵉ) gᵉ =
  is-locally-finite-equivᵉ
    ( equiv-precomp-Πᵉ eᵉ Bᵉ)
    ( is-locally-finite-Π-Finᵉ kᵉ (λ xᵉ → gᵉ (map-equivᵉ eᵉ xᵉ)))

is-locally-finite-Πᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} → is-finiteᵉ Aᵉ →
  ((xᵉ : Aᵉ) → is-locally-finiteᵉ (Bᵉ xᵉ)) → is-locally-finiteᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)
is-locally-finite-Πᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} fᵉ gᵉ =
  apply-universal-property-trunc-Propᵉ fᵉ
    ( is-locally-finite-Propᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ))
    ( λ eᵉ → is-locally-finite-Π-countᵉ eᵉ gᵉ)
```

#### Finite products of π-finite types

```agda
is-π-finite-Πᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  is-finiteᵉ Aᵉ → ((aᵉ : Aᵉ) → is-π-finiteᵉ kᵉ (Bᵉ aᵉ)) →
  is-π-finiteᵉ kᵉ ((aᵉ : Aᵉ) → Bᵉ aᵉ)
is-π-finite-Πᵉ zero-ℕᵉ {Aᵉ} {Bᵉ} Hᵉ Kᵉ =
  is-finite-equiv'ᵉ
    ( equiv-distributive-trunc-Π-is-finite-Setᵉ Bᵉ Hᵉ)
    ( is-finite-Πᵉ Hᵉ Kᵉ)
pr1ᵉ (is-π-finite-Πᵉ (succ-ℕᵉ kᵉ) Hᵉ Kᵉ) = is-π-finite-Πᵉ zero-ℕᵉ Hᵉ (λ aᵉ → pr1ᵉ (Kᵉ aᵉ))
pr2ᵉ (is-π-finite-Πᵉ (succ-ℕᵉ kᵉ) Hᵉ Kᵉ) fᵉ gᵉ =
  is-π-finite-equivᵉ kᵉ
    ( equiv-funextᵉ)
    ( is-π-finite-Πᵉ kᵉ Hᵉ (λ aᵉ → pr2ᵉ (Kᵉ aᵉ) (fᵉ aᵉ) (gᵉ aᵉ)))

π-Finite-Πᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) (Aᵉ : 𝔽ᵉ l1ᵉ) (Bᵉ : type-𝔽ᵉ Aᵉ → π-Finiteᵉ l2ᵉ kᵉ) →
  π-Finiteᵉ (l1ᵉ ⊔ l2ᵉ) kᵉ
pr1ᵉ (π-Finite-Πᵉ kᵉ Aᵉ Bᵉ) =
  (xᵉ : type-𝔽ᵉ Aᵉ) → (type-π-Finiteᵉ kᵉ (Bᵉ xᵉ))
pr2ᵉ (π-Finite-Πᵉ kᵉ Aᵉ Bᵉ) =
  is-π-finite-Πᵉ kᵉ
    ( is-finite-type-𝔽ᵉ Aᵉ)
    ( λ xᵉ → is-π-finite-type-π-Finiteᵉ kᵉ (Bᵉ xᵉ))
```

### Proposition 1.6

```agda
is-locally-finite-Σᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  is-locally-finiteᵉ Aᵉ → ((xᵉ : Aᵉ) → is-locally-finiteᵉ (Bᵉ xᵉ)) →
  is-locally-finiteᵉ (Σᵉ Aᵉ Bᵉ)
is-locally-finite-Σᵉ {Bᵉ = Bᵉ} Hᵉ Kᵉ (xᵉ ,ᵉ yᵉ) (x'ᵉ ,ᵉ y'ᵉ) =
  is-finite-equiv'ᵉ
    ( equiv-pair-eq-Σᵉ (xᵉ ,ᵉ yᵉ) (x'ᵉ ,ᵉ y'ᵉ))
    ( is-finite-Σᵉ (Hᵉ xᵉ x'ᵉ) (λ pᵉ → Kᵉ x'ᵉ (trᵉ Bᵉ pᵉ yᵉ) y'ᵉ))
```

### Proposition 1.7

```agda
has-finite-connected-components-Σ-is-0-connectedᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  is-0-connectedᵉ Aᵉ → is-π-finiteᵉ 1 Aᵉ →
  ((xᵉ : Aᵉ) → has-finite-connected-componentsᵉ (Bᵉ xᵉ)) →
  has-finite-connected-componentsᵉ (Σᵉ Aᵉ Bᵉ)
has-finite-connected-components-Σ-is-0-connectedᵉ {Aᵉ = Aᵉ} {Bᵉ} Cᵉ Hᵉ Kᵉ =
  apply-universal-property-trunc-Propᵉ
    ( is-inhabited-is-0-connectedᵉ Cᵉ)
    ( is-π-finite-Propᵉ zero-ℕᵉ (Σᵉ Aᵉ Bᵉ))
    ( αᵉ)
  where
  αᵉ : Aᵉ → is-π-finiteᵉ zero-ℕᵉ (Σᵉ Aᵉ Bᵉ)
  αᵉ aᵉ =
    is-finite-codomainᵉ
      ( Kᵉ aᵉ)
      ( is-surjective-map-trunc-Setᵉ
        ( fiber-inclusionᵉ Bᵉ aᵉ)
        ( is-surjective-fiber-inclusionᵉ Cᵉ aᵉ))
      ( apply-dependent-universal-property-trunc-Set'ᵉ
        ( λ xᵉ →
          set-Propᵉ
            ( Π-Propᵉ
              ( type-trunc-Setᵉ (Σᵉ Aᵉ Bᵉ))
              ( λ yᵉ → is-decidable-Propᵉ (Id-Propᵉ (trunc-Setᵉ (Σᵉ Aᵉ Bᵉ)) xᵉ yᵉ))))
        ( βᵉ))
    where
    βᵉ : (xᵉ : Σᵉ Aᵉ Bᵉ) (vᵉ : type-trunc-Setᵉ (Σᵉ Aᵉ Bᵉ)) →
        is-decidableᵉ (Idᵉ (unit-trunc-Setᵉ xᵉ) vᵉ)
    βᵉ (xᵉ ,ᵉ yᵉ) =
      apply-dependent-universal-property-trunc-Set'ᵉ
        ( λ uᵉ →
          set-Propᵉ
            ( is-decidable-Propᵉ
              ( Id-Propᵉ (trunc-Setᵉ (Σᵉ Aᵉ Bᵉ)) (unit-trunc-Setᵉ (xᵉ ,ᵉ yᵉ)) uᵉ)))
        ( γᵉ)
      where
      γᵉ : (vᵉ : Σᵉ Aᵉ Bᵉ) →
          is-decidableᵉ (Idᵉ (unit-trunc-Setᵉ (xᵉ ,ᵉ yᵉ)) (unit-trunc-Setᵉ vᵉ))
      γᵉ (x'ᵉ ,ᵉ y'ᵉ) =
        is-decidable-equivᵉ
          ( is-effective-unit-trunc-Setᵉ
            ( Σᵉ Aᵉ Bᵉ)
            ( xᵉ ,ᵉ yᵉ)
            ( x'ᵉ ,ᵉ y'ᵉ))
          ( apply-universal-property-trunc-Propᵉ
            ( mere-eq-is-0-connectedᵉ Cᵉ aᵉ xᵉ)
            ( is-decidable-Propᵉ
              ( mere-eq-Propᵉ (xᵉ ,ᵉ yᵉ) (x'ᵉ ,ᵉ y'ᵉ)))
              ( δᵉ))
        where
        δᵉ : Idᵉ aᵉ xᵉ → is-decidableᵉ (mere-eqᵉ (xᵉ ,ᵉ yᵉ) (x'ᵉ ,ᵉ y'ᵉ))
        δᵉ reflᵉ =
          apply-universal-property-trunc-Propᵉ
            ( mere-eq-is-0-connectedᵉ Cᵉ aᵉ x'ᵉ)
            ( is-decidable-Propᵉ
              ( mere-eq-Propᵉ (aᵉ ,ᵉ yᵉ) (x'ᵉ ,ᵉ y'ᵉ)))
            ( εᵉ)
          where
          εᵉ : Idᵉ aᵉ x'ᵉ → is-decidableᵉ (mere-eqᵉ (xᵉ ,ᵉ yᵉ) (x'ᵉ ,ᵉ y'ᵉ))
          εᵉ reflᵉ =
            is-decidable-equivᵉ eᵉ
              ( is-decidable-type-trunc-Prop-is-finiteᵉ
                ( is-finite-Σᵉ
                  ( pr2ᵉ Hᵉ aᵉ aᵉ)
                  ( λ ωᵉ → is-finite-is-decidable-Propᵉ (Pᵉ ωᵉ) (dᵉ ωᵉ))))
            where
            ℙᵉ : is-contrᵉ
                ( Σᵉ ( hom-Setᵉ (trunc-Setᵉ (Idᵉ aᵉ aᵉ)) (Prop-Setᵉ _))
                    ( λ hᵉ →
                      ( λ a₁ᵉ → hᵉ (unit-trunc-Setᵉ a₁ᵉ)) ~ᵉ
                      ( λ ω₁ᵉ → trunc-Propᵉ (Idᵉ (trᵉ Bᵉ ω₁ᵉ yᵉ) y'ᵉ))))
            ℙᵉ = universal-property-trunc-Setᵉ
                ( Idᵉ aᵉ aᵉ)
                ( Prop-Setᵉ _)
                ( λ ωᵉ → trunc-Propᵉ (Idᵉ (trᵉ Bᵉ ωᵉ yᵉ) y'ᵉ))
            Pᵉ : type-trunc-Setᵉ (Idᵉ aᵉ aᵉ) → Propᵉ _
            Pᵉ = pr1ᵉ (centerᵉ ℙᵉ)
            compute-Pᵉ :
              ( ωᵉ : Idᵉ aᵉ aᵉ) →
              type-Propᵉ (Pᵉ (unit-trunc-Setᵉ ωᵉ)) ≃ᵉ
              type-trunc-Propᵉ (Idᵉ (trᵉ Bᵉ ωᵉ yᵉ) y'ᵉ)
            compute-Pᵉ ωᵉ = equiv-eqᵉ (apᵉ pr1ᵉ (pr2ᵉ (centerᵉ ℙᵉ) ωᵉ))
            dᵉ : (tᵉ : type-trunc-Setᵉ (Idᵉ aᵉ aᵉ)) → is-decidableᵉ (type-Propᵉ (Pᵉ tᵉ))
            dᵉ = apply-dependent-universal-property-trunc-Set'ᵉ
                ( λ tᵉ → set-Propᵉ (is-decidable-Propᵉ (Pᵉ tᵉ)))
                ( λ ωᵉ →
                  is-decidable-equiv'ᵉ
                    ( inv-equivᵉ (compute-Pᵉ ωᵉ))
                    ( is-decidable-equiv'ᵉ
                      ( is-effective-unit-trunc-Setᵉ (Bᵉ aᵉ) (trᵉ Bᵉ ωᵉ yᵉ) y'ᵉ)
                      ( has-decidable-equality-is-finiteᵉ
                        ( Kᵉ aᵉ)
                        ( unit-trunc-Setᵉ (trᵉ Bᵉ ωᵉ yᵉ))
                        ( unit-trunc-Setᵉ y'ᵉ))))
            fᵉ : type-hom-Propᵉ
                ( trunc-Propᵉ (Σᵉ (type-trunc-Setᵉ (Idᵉ aᵉ aᵉ)) (type-Propᵉ ∘ᵉ Pᵉ)))
                ( mere-eq-Propᵉ {Aᵉ = Σᵉ Aᵉ Bᵉ} (aᵉ ,ᵉ yᵉ) (aᵉ ,ᵉ y'ᵉ))
            fᵉ tᵉ = apply-universal-property-trunc-Propᵉ tᵉ
                    ( mere-eq-Propᵉ (aᵉ ,ᵉ yᵉ) (aᵉ ,ᵉ y'ᵉ))
                      λ (uᵉ ,ᵉ vᵉ) →
                      apply-dependent-universal-property-trunc-Set'ᵉ
                        ( λ u'ᵉ →
                          hom-set-Setᵉ
                            ( set-Propᵉ (Pᵉ u'ᵉ))
                            ( set-Propᵉ
                              ( mere-eq-Propᵉ (aᵉ ,ᵉ yᵉ) (aᵉ ,ᵉ y'ᵉ))))
                        ( λ ωᵉ v'ᵉ →
                          apply-universal-property-trunc-Propᵉ
                            ( map-equivᵉ (compute-Pᵉ ωᵉ) v'ᵉ)
                            ( mere-eq-Propᵉ (aᵉ ,ᵉ yᵉ) (aᵉ ,ᵉ y'ᵉ))
                            ( λ pᵉ → unit-trunc-Propᵉ (eq-pair-Σᵉ ωᵉ pᵉ)))
                        ( uᵉ)
                        ( vᵉ)
            eᵉ : mere-eqᵉ {Aᵉ = Σᵉ Aᵉ Bᵉ} (aᵉ ,ᵉ yᵉ) (aᵉ ,ᵉ y'ᵉ) ≃ᵉ
                type-trunc-Propᵉ (Σᵉ (type-trunc-Setᵉ (Idᵉ aᵉ aᵉ)) (type-Propᵉ ∘ᵉ Pᵉ))
            eᵉ = equiv-iffᵉ
                  ( mere-eq-Propᵉ (aᵉ ,ᵉ yᵉ) (aᵉ ,ᵉ y'ᵉ))
                  ( trunc-Propᵉ (Σᵉ (type-trunc-Setᵉ (Idᵉ aᵉ aᵉ)) (type-Propᵉ ∘ᵉ Pᵉ)))
                  ( λ tᵉ →
                    apply-universal-property-trunc-Propᵉ tᵉ
                      ( trunc-Propᵉ _)
                      ( ( λ ( ωᵉ ,ᵉ rᵉ) →
                          unit-trunc-Propᵉ
                            ( ( unit-trunc-Setᵉ ωᵉ) ,ᵉ
                              ( map-inv-equivᵉ
                                ( compute-Pᵉ ωᵉ)
                                ( unit-trunc-Propᵉ rᵉ)))) ∘ᵉ
                        ( pair-eq-Σᵉ)))
                  ( fᵉ)
```

### Proposition 1.8

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : A1ᵉ +ᵉ A2ᵉ → Bᵉ) (eᵉ : (A1ᵉ +ᵉ A2ᵉ) ≃ᵉ type-trunc-Setᵉ Bᵉ)
  (Hᵉ : (unit-trunc-Setᵉ ∘ᵉ fᵉ) ~ᵉ map-equivᵉ eᵉ)
  where

  map-is-coproduct-codomainᵉ : (imᵉ (fᵉ ∘ᵉ inlᵉ) +ᵉ imᵉ (fᵉ ∘ᵉ inrᵉ)) → Bᵉ
  map-is-coproduct-codomainᵉ = rec-coproductᵉ pr1ᵉ pr1ᵉ

  triangle-is-coproduct-codomainᵉ :
    ( ( map-is-coproduct-codomainᵉ) ∘ᵉ
      ( map-coproductᵉ (map-unit-imᵉ (fᵉ ∘ᵉ inlᵉ)) (map-unit-imᵉ (fᵉ ∘ᵉ inrᵉ)))) ~ᵉ fᵉ
  triangle-is-coproduct-codomainᵉ (inlᵉ xᵉ) = reflᵉ
  triangle-is-coproduct-codomainᵉ (inrᵉ xᵉ) = reflᵉ

  abstract
    is-emb-map-is-coproduct-codomainᵉ : is-embᵉ map-is-coproduct-codomainᵉ
    is-emb-map-is-coproduct-codomainᵉ =
      is-emb-coproductᵉ
        ( is-emb-inclusion-subtypeᵉ (λ bᵉ → trunc-Propᵉ _))
        ( is-emb-inclusion-subtypeᵉ (λ bᵉ → trunc-Propᵉ _))
        ( λ (b1ᵉ ,ᵉ uᵉ) (b2ᵉ ,ᵉ vᵉ) →
          apply-universal-property-trunc-Propᵉ uᵉ
            ( function-Propᵉ _ empty-Propᵉ)
            ( λ where
              ( xᵉ ,ᵉ reflᵉ) →
                apply-universal-property-trunc-Propᵉ vᵉ
                  ( function-Propᵉ _ empty-Propᵉ)
                  ( λ where
                    ( yᵉ ,ᵉ reflᵉ) rᵉ →
                      is-empty-eq-coproduct-inl-inrᵉ xᵉ yᵉ
                        ( is-injective-is-equivᵉ
                          ( is-equiv-map-equivᵉ eᵉ)
                          ( ( invᵉ (Hᵉ (inlᵉ xᵉ))) ∙ᵉ
                            ( apᵉ unit-trunc-Setᵉ rᵉ) ∙ᵉ
                            ( Hᵉ (inrᵉ yᵉ)))))))

  is-surjective-map-is-coproduct-codomainᵉ :
    is-surjectiveᵉ map-is-coproduct-codomainᵉ
  is-surjective-map-is-coproduct-codomainᵉ bᵉ =
    apply-universal-property-trunc-Propᵉ
      ( apply-effectiveness-unit-trunc-Setᵉ
        ( invᵉ (is-section-map-inv-equivᵉ eᵉ (unit-trunc-Setᵉ bᵉ)) ∙ᵉ invᵉ (Hᵉ aᵉ)))
      ( trunc-Propᵉ (fiberᵉ map-is-coproduct-codomainᵉ bᵉ))
      ( λ pᵉ →
        unit-trunc-Propᵉ
          ( ( map-coproductᵉ (map-unit-imᵉ (fᵉ ∘ᵉ inlᵉ)) (map-unit-imᵉ (fᵉ ∘ᵉ inrᵉ)) aᵉ) ,ᵉ
            ( triangle-is-coproduct-codomainᵉ aᵉ ∙ᵉ invᵉ pᵉ)))
    where
    aᵉ = map-inv-equivᵉ eᵉ (unit-trunc-Setᵉ bᵉ)

  is-coproduct-codomainᵉ : (imᵉ (fᵉ ∘ᵉ inlᵉ) +ᵉ imᵉ (fᵉ ∘ᵉ inrᵉ)) ≃ᵉ Bᵉ
  pr1ᵉ is-coproduct-codomainᵉ = map-is-coproduct-codomainᵉ
  pr2ᵉ is-coproduct-codomainᵉ =
    is-equiv-is-emb-is-surjectiveᵉ
      is-surjective-map-is-coproduct-codomainᵉ
      is-emb-map-is-coproduct-codomainᵉ

is-0-connected-unitᵉ : is-0-connectedᵉ unitᵉ
is-0-connected-unitᵉ =
  is-contr-equiv'ᵉ unitᵉ equiv-unit-trunc-unit-Setᵉ is-contr-unitᵉ

abstract
  is-contr-imᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) {fᵉ : Aᵉ → type-Setᵉ Bᵉ}
    (aᵉ : Aᵉ) (Hᵉ : fᵉ ~ᵉ constᵉ Aᵉ (fᵉ aᵉ)) → is-contrᵉ (imᵉ fᵉ)
  pr1ᵉ (is-contr-imᵉ Bᵉ {fᵉ} aᵉ Hᵉ) = map-unit-imᵉ fᵉ aᵉ
  pr2ᵉ (is-contr-imᵉ Bᵉ {fᵉ} aᵉ Hᵉ) (xᵉ ,ᵉ uᵉ) =
    apply-dependent-universal-property-trunc-Propᵉ
      ( λ vᵉ → Id-Propᵉ (im-Setᵉ Bᵉ fᵉ) (map-unit-imᵉ fᵉ aᵉ) (xᵉ ,ᵉ vᵉ))
      ( uᵉ)
      ( λ where
        ( a'ᵉ ,ᵉ reflᵉ) →
          eq-Eq-imᵉ fᵉ (map-unit-imᵉ fᵉ aᵉ) (map-unit-imᵉ fᵉ a'ᵉ) (invᵉ (Hᵉ a'ᵉ)))

abstract
  is-0-connected-imᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-0-connectedᵉ Aᵉ → is-0-connectedᵉ (imᵉ fᵉ)
  is-0-connected-imᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} fᵉ Cᵉ =
    apply-universal-property-trunc-Propᵉ
      ( is-inhabited-is-0-connectedᵉ Cᵉ)
      ( is-contr-Propᵉ _)
      ( λ aᵉ →
        is-contr-equiv'ᵉ
          ( imᵉ (map-trunc-Setᵉ fᵉ))
          ( equiv-trunc-im-Setᵉ fᵉ)
          ( is-contr-imᵉ
            ( trunc-Setᵉ Bᵉ)
            ( unit-trunc-Setᵉ aᵉ)
            ( apply-dependent-universal-property-trunc-Set'ᵉ
              ( λ xᵉ →
                set-Propᵉ
                  ( Id-Propᵉ
                    ( trunc-Setᵉ Bᵉ)
                    ( map-trunc-Setᵉ fᵉ xᵉ)
                    ( map-trunc-Setᵉ fᵉ (unit-trunc-Setᵉ aᵉ))))
              ( λ a'ᵉ →
                apply-universal-property-trunc-Propᵉ
                  ( mere-eq-is-0-connectedᵉ Cᵉ a'ᵉ aᵉ)
                  ( Id-Propᵉ
                    ( trunc-Setᵉ Bᵉ)
                    ( map-trunc-Setᵉ fᵉ (unit-trunc-Setᵉ a'ᵉ))
                    ( map-trunc-Setᵉ fᵉ (unit-trunc-Setᵉ aᵉ)))
                  ( λ where reflᵉ → reflᵉ)))))

is-0-connected-im-unitᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (fᵉ : unitᵉ → Aᵉ) → is-0-connectedᵉ (imᵉ fᵉ)
is-0-connected-im-unitᵉ fᵉ =
  is-0-connected-imᵉ fᵉ is-0-connected-unitᵉ

abstract
  has-finite-connected-components-Σ'ᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    (kᵉ : ℕᵉ) → (Finᵉ kᵉ ≃ᵉ (type-trunc-Setᵉ Aᵉ)) →
    ((xᵉ yᵉ : Aᵉ) → has-finite-connected-componentsᵉ (Idᵉ xᵉ yᵉ)) →
    ((xᵉ : Aᵉ) → has-finite-connected-componentsᵉ (Bᵉ xᵉ)) →
    has-finite-connected-componentsᵉ (Σᵉ Aᵉ Bᵉ)
  has-finite-connected-components-Σ'ᵉ zero-ℕᵉ eᵉ Hᵉ Kᵉ =
    is-π-finite-is-emptyᵉ zero-ℕᵉ
      ( is-empty-is-empty-trunc-Setᵉ (map-inv-equivᵉ eᵉ) ∘ᵉ pr1ᵉ)
  has-finite-connected-components-Σ'ᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} (succ-ℕᵉ kᵉ) eᵉ Hᵉ Kᵉ =
    apply-universal-property-trunc-Propᵉ
      ( has-presentation-of-cardinality-has-cardinality-componentsᵉ
        ( succ-ℕᵉ kᵉ)
        ( unit-trunc-Propᵉ eᵉ))
      ( has-finite-connected-components-Propᵉ (Σᵉ Aᵉ Bᵉ))
      ( αᵉ)
    where
    αᵉ : Σᵉ (Finᵉ (succ-ℕᵉ kᵉ) → Aᵉ) (λ fᵉ → is-equivᵉ (unit-trunc-Setᵉ ∘ᵉ fᵉ)) →
        has-finite-connected-componentsᵉ (Σᵉ Aᵉ Bᵉ)
    αᵉ (fᵉ ,ᵉ Eηfᵉ) =
      is-finite-equivᵉ
        ( equiv-trunc-Setᵉ gᵉ)
        ( is-finite-equiv'ᵉ
          ( equiv-distributive-trunc-coproduct-Setᵉ
            ( Σᵉ (imᵉ (fᵉ ∘ᵉ inlᵉ)) (Bᵉ ∘ᵉ pr1ᵉ))
            ( Σᵉ (imᵉ (fᵉ ∘ᵉ inrᵉ)) (Bᵉ ∘ᵉ pr1ᵉ)))
          ( is-finite-coproductᵉ
            ( has-finite-connected-components-Σ'ᵉ kᵉ
              ( hᵉ)
              ( λ xᵉ yᵉ →
                is-finite-equiv'ᵉ
                  ( equiv-trunc-Setᵉ
                    ( equiv-ap-embᵉ
                      ( pr1ᵉ ,ᵉ is-emb-inclusion-subtypeᵉ ( λ uᵉ → trunc-Propᵉ _))))
                  ( Hᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ)))
              ( λ xᵉ → Kᵉ (pr1ᵉ xᵉ)))
            ( has-finite-connected-components-Σ-is-0-connectedᵉ
              ( is-0-connected-imᵉ (fᵉ ∘ᵉ inrᵉ) is-0-connected-unitᵉ)
              ( ( is-finite-is-contrᵉ
                  ( is-0-connected-imᵉ (fᵉ ∘ᵉ inrᵉ) is-0-connected-unitᵉ)) ,ᵉ
                ( λ xᵉ yᵉ →
                  is-π-finite-equivᵉ zero-ℕᵉ
                    ( equiv-Eq-eq-imᵉ (fᵉ ∘ᵉ inrᵉ) xᵉ yᵉ)
                    ( Hᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ))))
              ( λ xᵉ → Kᵉ (pr1ᵉ xᵉ)))))
      where
      gᵉ : ((Σᵉ (imᵉ (fᵉ ∘ᵉ inlᵉ)) (Bᵉ ∘ᵉ pr1ᵉ)) +ᵉ (Σᵉ (imᵉ (fᵉ ∘ᵉ inrᵉ)) (Bᵉ ∘ᵉ pr1ᵉ))) ≃ᵉ
          Σᵉ Aᵉ Bᵉ
      gᵉ = ( equiv-Σᵉ Bᵉ
            ( is-coproduct-codomainᵉ fᵉ
              ( unit-trunc-Setᵉ ∘ᵉ fᵉ ,ᵉ Eηfᵉ)
              ( refl-htpyᵉ))
            ( λ { (inlᵉ xᵉ) → id-equivᵉ ; (inrᵉ xᵉ) → id-equivᵉ})) ∘eᵉ
          ( inv-equivᵉ
            ( right-distributive-Σ-coproductᵉ
              ( imᵉ (fᵉ ∘ᵉ inlᵉ))
              ( imᵉ (fᵉ ∘ᵉ inrᵉ))
              ( rec-coproductᵉ (Bᵉ ∘ᵉ pr1ᵉ) (Bᵉ ∘ᵉ pr1ᵉ))))
      iᵉ : Finᵉ kᵉ → type-trunc-Setᵉ (imᵉ (fᵉ ∘ᵉ inlᵉ))
      iᵉ = unit-trunc-Setᵉ ∘ᵉ map-unit-imᵉ (fᵉ ∘ᵉ inlᵉ)
      is-surjective-iᵉ : is-surjectiveᵉ iᵉ
      is-surjective-iᵉ =
        is-surjective-compᵉ
          ( is-surjective-unit-trunc-Setᵉ (imᵉ (fᵉ ∘ᵉ inlᵉ)))
          ( is-surjective-map-unit-imᵉ (fᵉ ∘ᵉ inlᵉ))
      is-emb-iᵉ : is-embᵉ iᵉ
      is-emb-iᵉ =
        is-emb-top-map-triangleᵉ
          ( (unit-trunc-Setᵉ ∘ᵉ fᵉ) ∘ᵉ inlᵉ)
          ( inclusion-trunc-im-Setᵉ (fᵉ ∘ᵉ inlᵉ))
          ( iᵉ)
          ( ( inv-htpyᵉ (naturality-unit-trunc-Setᵉ (inclusion-imᵉ (fᵉ ∘ᵉ inlᵉ)))) ·rᵉ
            ( map-unit-imᵉ (fᵉ ∘ᵉ inlᵉ)))
          ( is-emb-inclusion-trunc-im-Setᵉ (fᵉ ∘ᵉ inlᵉ))
          ( is-emb-compᵉ
            ( unit-trunc-Setᵉ ∘ᵉ fᵉ)
            ( inlᵉ)
            ( is-emb-is-equivᵉ Eηfᵉ)
            ( is-emb-inlᵉ (Finᵉ kᵉ) unitᵉ))
      hᵉ : Finᵉ kᵉ ≃ᵉ type-trunc-Setᵉ (imᵉ (fᵉ ∘ᵉ inlᵉ))
      hᵉ = iᵉ ,ᵉ (is-equiv-is-emb-is-surjectiveᵉ is-surjective-iᵉ is-emb-iᵉ)

has-finite-connected-components-Σᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} → is-π-finiteᵉ 1 Aᵉ →
  ((xᵉ : Aᵉ) → has-finite-connected-componentsᵉ (Bᵉ xᵉ)) →
  has-finite-connected-componentsᵉ (Σᵉ Aᵉ Bᵉ)
has-finite-connected-components-Σᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} Hᵉ Kᵉ =
  apply-universal-property-trunc-Propᵉ
    ( pr1ᵉ Hᵉ)
    ( has-finite-connected-components-Propᵉ (Σᵉ Aᵉ Bᵉ))
    ( λ (kᵉ ,ᵉ eᵉ) → has-finite-connected-components-Σ'ᵉ kᵉ eᵉ (λ xᵉ yᵉ → pr2ᵉ Hᵉ xᵉ yᵉ) Kᵉ)

abstract
  is-π-finite-Σᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    is-π-finiteᵉ (succ-ℕᵉ kᵉ) Aᵉ → ((xᵉ : Aᵉ) → is-π-finiteᵉ kᵉ (Bᵉ xᵉ)) →
    is-π-finiteᵉ kᵉ (Σᵉ Aᵉ Bᵉ)
  is-π-finite-Σᵉ zero-ℕᵉ {Aᵉ} {Bᵉ} Hᵉ Kᵉ = has-finite-connected-components-Σᵉ Hᵉ Kᵉ
  pr1ᵉ (is-π-finite-Σᵉ (succ-ℕᵉ kᵉ) Hᵉ Kᵉ) =
    has-finite-connected-components-Σᵉ
      ( is-π-finite-one-is-π-finite-succ-ℕᵉ (succ-ℕᵉ kᵉ) Hᵉ)
      ( λ xᵉ →
        has-finite-connected-components-is-π-finiteᵉ (succ-ℕᵉ kᵉ) (Kᵉ xᵉ))
  pr2ᵉ (is-π-finite-Σᵉ (succ-ℕᵉ kᵉ) Hᵉ Kᵉ) (xᵉ ,ᵉ uᵉ) (yᵉ ,ᵉ vᵉ) =
    is-π-finite-equivᵉ kᵉ
      ( equiv-pair-eq-Σᵉ (xᵉ ,ᵉ uᵉ) (yᵉ ,ᵉ vᵉ))
      ( is-π-finite-Σᵉ kᵉ
        ( pr2ᵉ Hᵉ xᵉ yᵉ)
        ( λ where reflᵉ → pr2ᵉ (Kᵉ xᵉ) uᵉ vᵉ))

π-Finite-Σᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) (Aᵉ : π-Finiteᵉ l1ᵉ (succ-ℕᵉ kᵉ))
  (Bᵉ : (xᵉ : type-π-Finiteᵉ (succ-ℕᵉ kᵉ) Aᵉ) → π-Finiteᵉ l2ᵉ kᵉ) →
  π-Finiteᵉ (l1ᵉ ⊔ l2ᵉ) kᵉ
pr1ᵉ (π-Finite-Σᵉ kᵉ Aᵉ Bᵉ) =
  Σᵉ (type-π-Finiteᵉ (succ-ℕᵉ kᵉ) Aᵉ) (λ xᵉ → type-π-Finiteᵉ kᵉ (Bᵉ xᵉ))
pr2ᵉ (π-Finite-Σᵉ kᵉ Aᵉ Bᵉ) =
  is-π-finite-Σᵉ kᵉ
    ( is-π-finite-type-π-Finiteᵉ (succ-ℕᵉ kᵉ) Aᵉ)
    ( λ xᵉ → is-π-finite-type-π-Finiteᵉ kᵉ (Bᵉ xᵉ))
```