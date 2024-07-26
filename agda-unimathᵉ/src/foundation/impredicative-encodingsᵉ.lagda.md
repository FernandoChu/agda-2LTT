# Impredicative encodings of the logical operations

```agda
module foundation.impredicative-encodingsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunctionᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.disjunctionᵉ
open import foundation.empty-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.homotopiesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universal-quantificationᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.coproduct-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
```

</details>

## Idea

Byᵉ universallyᵉ quantifyingᵉ overᵉ allᵉ
[propositions](foundation-core.propositions.mdᵉ) in aᵉ universe,ᵉ weᵉ canᵉ defineᵉ allᵉ
theᵉ logicalᵉ operations.ᵉ Theᵉ ideaᵉ isᵉ to useᵉ theᵉ factᵉ thatᵉ anyᵉ propositionᵉ `P`ᵉ isᵉ
[equivalent](foundation.logical-equivalences.mdᵉ) to theᵉ propositionᵉ
`(Qᵉ : Propᵉ lᵉ) → (Pᵉ ⇒ᵉ Qᵉ) ⇒ᵉ Q`,ᵉ whichᵉ canᵉ beᵉ thoughtᵉ ofᵉ asᵉ theᵉ leastᵉ propositionᵉ
`Q`ᵉ containingᵉ `P`.ᵉ

### The impredicative encoding of the propositional truncation

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  impredicative-trunc-Propᵉ : Propᵉ (lsuc lᵉ)
  impredicative-trunc-Propᵉ =
    ∀'ᵉ (Propᵉ lᵉ) (λ Qᵉ → function-Propᵉ (Aᵉ → type-Propᵉ Qᵉ) Qᵉ)

  type-impredicative-trunc-Propᵉ : UUᵉ (lsuc lᵉ)
  type-impredicative-trunc-Propᵉ =
    type-Propᵉ impredicative-trunc-Propᵉ

  map-impredicative-trunc-Propᵉ :
    type-trunc-Propᵉ Aᵉ → type-impredicative-trunc-Propᵉ
  map-impredicative-trunc-Propᵉ =
    map-universal-property-trunc-Propᵉ
      ( impredicative-trunc-Propᵉ)
      ( λ xᵉ Qᵉ fᵉ → fᵉ xᵉ)

  map-inv-impredicative-trunc-Propᵉ :
    type-impredicative-trunc-Propᵉ → type-trunc-Propᵉ Aᵉ
  map-inv-impredicative-trunc-Propᵉ Hᵉ =
    Hᵉ (trunc-Propᵉ Aᵉ) unit-trunc-Propᵉ

  equiv-impredicative-trunc-Propᵉ :
    type-trunc-Propᵉ Aᵉ ≃ᵉ type-impredicative-trunc-Propᵉ
  equiv-impredicative-trunc-Propᵉ =
    equiv-iffᵉ
      ( trunc-Propᵉ Aᵉ)
      ( impredicative-trunc-Propᵉ)
      ( map-impredicative-trunc-Propᵉ)
      ( map-inv-impredicative-trunc-Propᵉ)
```

### The impredicative encoding of conjunction

```agda
module _
  {l1ᵉ l2ᵉ : Level} (P1ᵉ : Propᵉ l1ᵉ) (P2ᵉ : Propᵉ l2ᵉ)
  where

  impredicative-conjunction-Propᵉ : Propᵉ (lsuc (l1ᵉ ⊔ l2ᵉ))
  impredicative-conjunction-Propᵉ =
    ∀'ᵉ (Propᵉ (l1ᵉ ⊔ l2ᵉ)) (λ Qᵉ → (P1ᵉ ⇒ᵉ P2ᵉ ⇒ᵉ Qᵉ) ⇒ᵉ Qᵉ)

  type-impredicative-conjunction-Propᵉ : UUᵉ (lsuc (l1ᵉ ⊔ l2ᵉ))
  type-impredicative-conjunction-Propᵉ =
    type-Propᵉ impredicative-conjunction-Propᵉ

  map-product-impredicative-conjunction-Propᵉ :
    type-conjunction-Propᵉ P1ᵉ P2ᵉ → type-impredicative-conjunction-Propᵉ
  map-product-impredicative-conjunction-Propᵉ (p1ᵉ ,ᵉ p2ᵉ) Qᵉ fᵉ = fᵉ p1ᵉ p2ᵉ

  map-inv-product-impredicative-conjunction-Propᵉ :
    type-impredicative-conjunction-Propᵉ → type-conjunction-Propᵉ P1ᵉ P2ᵉ
  map-inv-product-impredicative-conjunction-Propᵉ Hᵉ = Hᵉ (P1ᵉ ∧ᵉ P2ᵉ) pairᵉ

  equiv-product-impredicative-conjunction-Propᵉ :
    type-conjunction-Propᵉ P1ᵉ P2ᵉ ≃ᵉ type-impredicative-conjunction-Propᵉ
  equiv-product-impredicative-conjunction-Propᵉ =
    equiv-iffᵉ
      ( P1ᵉ ∧ᵉ P2ᵉ)
      ( impredicative-conjunction-Propᵉ)
      ( map-product-impredicative-conjunction-Propᵉ)
      ( map-inv-product-impredicative-conjunction-Propᵉ)
```

### The impredicative encoding of disjunction

```agda
module _
  {l1ᵉ l2ᵉ : Level} (P1ᵉ : Propᵉ l1ᵉ) (P2ᵉ : Propᵉ l2ᵉ)
  where

  impredicative-disjunction-Propᵉ : Propᵉ (lsuc (l1ᵉ ⊔ l2ᵉ))
  impredicative-disjunction-Propᵉ =
    ∀'ᵉ (Propᵉ (l1ᵉ ⊔ l2ᵉ)) (λ Qᵉ → (P1ᵉ ⇒ᵉ Qᵉ) ⇒ᵉ (P2ᵉ ⇒ᵉ Qᵉ) ⇒ᵉ Qᵉ)

  type-impredicative-disjunction-Propᵉ : UUᵉ (lsuc (l1ᵉ ⊔ l2ᵉ))
  type-impredicative-disjunction-Propᵉ =
    type-Propᵉ impredicative-disjunction-Propᵉ

  map-impredicative-disjunction-Propᵉ :
    type-disjunction-Propᵉ P1ᵉ P2ᵉ → type-impredicative-disjunction-Propᵉ
  map-impredicative-disjunction-Propᵉ =
    map-universal-property-trunc-Propᵉ
      ( impredicative-disjunction-Propᵉ)
      ( rec-coproductᵉ (λ xᵉ Qᵉ f1ᵉ f2ᵉ → f1ᵉ xᵉ) (λ yᵉ Qᵉ f1ᵉ f2ᵉ → f2ᵉ yᵉ))

  map-inv-impredicative-disjunction-Propᵉ :
    type-impredicative-disjunction-Propᵉ → type-disjunction-Propᵉ P1ᵉ P2ᵉ
  map-inv-impredicative-disjunction-Propᵉ Hᵉ =
    Hᵉ (P1ᵉ ∨ᵉ P2ᵉ) (inl-disjunctionᵉ) (inr-disjunctionᵉ)

  equiv-impredicative-disjunction-Propᵉ :
    type-disjunction-Propᵉ P1ᵉ P2ᵉ ≃ᵉ type-impredicative-disjunction-Propᵉ
  equiv-impredicative-disjunction-Propᵉ =
    equiv-iffᵉ
      ( P1ᵉ ∨ᵉ P2ᵉ)
      ( impredicative-disjunction-Propᵉ)
      ( map-impredicative-disjunction-Propᵉ)
      ( map-inv-impredicative-disjunction-Propᵉ)
```

### The impredicative encoding of the empty type

```agda
impredicative-empty-Propᵉ : Propᵉ (lsuc lzero)
impredicative-empty-Propᵉ = ∀'ᵉ (Propᵉ lzero) (λ Pᵉ → Pᵉ)

type-impredicative-empty-Propᵉ : UUᵉ (lsuc lzero)
type-impredicative-empty-Propᵉ = type-Propᵉ impredicative-empty-Propᵉ

is-empty-impredicative-empty-Propᵉ :
  is-emptyᵉ type-impredicative-empty-Propᵉ
is-empty-impredicative-empty-Propᵉ eᵉ = eᵉ empty-Propᵉ

equiv-impredicative-empty-Propᵉ :
  emptyᵉ ≃ᵉ type-impredicative-empty-Propᵉ
equiv-impredicative-empty-Propᵉ =
  equiv-is-emptyᵉ idᵉ is-empty-impredicative-empty-Propᵉ
```

### The impredicative encoding of negation

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  impredicative-neg-Propᵉ : Propᵉ (lsuc lᵉ)
  impredicative-neg-Propᵉ =
    Π-Propᵉ (Propᵉ lᵉ) (λ Qᵉ → function-Propᵉ Aᵉ Qᵉ)

  type-impredicative-neg-Propᵉ : UUᵉ (lsuc lᵉ)
  type-impredicative-neg-Propᵉ = type-Propᵉ impredicative-neg-Propᵉ

  map-impredicative-neg-Propᵉ : ¬ᵉ Aᵉ → type-impredicative-neg-Propᵉ
  map-impredicative-neg-Propᵉ fᵉ Qᵉ aᵉ = ex-falsoᵉ (fᵉ aᵉ)

  map-inv-impredicative-neg-Propᵉ : type-impredicative-neg-Propᵉ → ¬ᵉ Aᵉ
  map-inv-impredicative-neg-Propᵉ Hᵉ aᵉ = Hᵉ (neg-type-Propᵉ Aᵉ) aᵉ aᵉ

  equiv-impredicative-neg-Propᵉ : ¬ᵉ Aᵉ ≃ᵉ type-impredicative-neg-Propᵉ
  equiv-impredicative-neg-Propᵉ =
    equiv-iffᵉ
      ( neg-type-Propᵉ Aᵉ)
      ( impredicative-neg-Propᵉ)
      ( map-impredicative-neg-Propᵉ)
      ( map-inv-impredicative-neg-Propᵉ)
```

### The impredicative encoding of existential quantification

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Aᵉ → Propᵉ l2ᵉ)
  where

  impredicative-exists-Propᵉ : Propᵉ (lsuc (l1ᵉ ⊔ l2ᵉ))
  impredicative-exists-Propᵉ =
    ∀'ᵉ (Propᵉ (l1ᵉ ⊔ l2ᵉ)) (λ Qᵉ → (∀'ᵉ Aᵉ (λ xᵉ → Pᵉ xᵉ ⇒ᵉ Qᵉ)) ⇒ᵉ Qᵉ)

  type-impredicative-exists-Propᵉ : UUᵉ (lsuc (l1ᵉ ⊔ l2ᵉ))
  type-impredicative-exists-Propᵉ =
    type-Propᵉ impredicative-exists-Propᵉ

  map-impredicative-exists-Propᵉ :
    existsᵉ Aᵉ Pᵉ → type-impredicative-exists-Propᵉ
  map-impredicative-exists-Propᵉ =
    map-universal-property-trunc-Propᵉ
      ( impredicative-exists-Propᵉ)
      ( ind-Σᵉ (λ xᵉ yᵉ Qᵉ hᵉ → hᵉ xᵉ yᵉ))

  map-inv-impredicative-exists-Propᵉ :
    type-impredicative-exists-Propᵉ → existsᵉ Aᵉ Pᵉ
  map-inv-impredicative-exists-Propᵉ Hᵉ =
    Hᵉ (∃ᵉ Aᵉ Pᵉ) (λ xᵉ yᵉ → unit-trunc-Propᵉ (xᵉ ,ᵉ yᵉ))

  equiv-impredicative-exists-Propᵉ :
    existsᵉ Aᵉ Pᵉ ≃ᵉ type-impredicative-exists-Propᵉ
  equiv-impredicative-exists-Propᵉ =
    equiv-iffᵉ
      ( ∃ᵉ Aᵉ Pᵉ)
      ( impredicative-exists-Propᵉ)
      ( map-impredicative-exists-Propᵉ)
      ( map-inv-impredicative-exists-Propᵉ)
```

### The impredicative encoding of the based identity type of a set

```agda
module _
  {lᵉ : Level} (Aᵉ : Setᵉ lᵉ) (aᵉ xᵉ : type-Setᵉ Aᵉ)
  where

  impredicative-based-id-Propᵉ : Propᵉ (lsuc lᵉ)
  impredicative-based-id-Propᵉ = ∀'ᵉ (type-Setᵉ Aᵉ → Propᵉ lᵉ) (λ Qᵉ → Qᵉ aᵉ ⇒ᵉ Qᵉ xᵉ)

  type-impredicative-based-id-Propᵉ : UUᵉ (lsuc lᵉ)
  type-impredicative-based-id-Propᵉ = type-Propᵉ impredicative-based-id-Propᵉ

  map-impredicative-based-id-Propᵉ :
    aᵉ ＝ᵉ xᵉ → type-impredicative-based-id-Propᵉ
  map-impredicative-based-id-Propᵉ reflᵉ Qᵉ pᵉ = pᵉ

  map-inv-impredicative-based-id-Propᵉ :
    type-impredicative-based-id-Propᵉ → aᵉ ＝ᵉ xᵉ
  map-inv-impredicative-based-id-Propᵉ Hᵉ = Hᵉ (Id-Propᵉ Aᵉ aᵉ) reflᵉ

  equiv-impredicative-based-id-Propᵉ :
    (aᵉ ＝ᵉ xᵉ) ≃ᵉ type-impredicative-based-id-Propᵉ
  equiv-impredicative-based-id-Propᵉ =
    equiv-iffᵉ
      ( Id-Propᵉ Aᵉ aᵉ xᵉ)
      ( impredicative-based-id-Propᵉ)
      ( map-impredicative-based-id-Propᵉ)
      ( map-inv-impredicative-based-id-Propᵉ)
```

### The impredicative encoding of Martin-Löf's identity type of a set

```agda
module _
  {lᵉ : Level} (Aᵉ : Setᵉ lᵉ) (xᵉ yᵉ : type-Setᵉ Aᵉ)
  where

  impredicative-id-Propᵉ : Propᵉ (lsuc lᵉ)
  impredicative-id-Propᵉ =
    ∀'ᵉ
      ( type-Setᵉ Aᵉ → type-Setᵉ Aᵉ → Propᵉ lᵉ)
      ( λ Qᵉ → (∀'ᵉ (type-Setᵉ Aᵉ) (λ aᵉ → Qᵉ aᵉ aᵉ)) ⇒ᵉ Qᵉ xᵉ yᵉ)

  type-impredicative-id-Propᵉ : UUᵉ (lsuc lᵉ)
  type-impredicative-id-Propᵉ = type-Propᵉ impredicative-id-Propᵉ

  map-impredicative-id-Propᵉ :
    xᵉ ＝ᵉ yᵉ → type-impredicative-id-Propᵉ
  map-impredicative-id-Propᵉ reflᵉ Qᵉ rᵉ = rᵉ xᵉ

  map-inv-impredicative-id-Propᵉ :
    type-impredicative-id-Propᵉ → xᵉ ＝ᵉ yᵉ
  map-inv-impredicative-id-Propᵉ Hᵉ = Hᵉ (Id-Propᵉ Aᵉ) (refl-htpyᵉ)

  equiv-impredicative-id-Propᵉ :
    (xᵉ ＝ᵉ yᵉ) ≃ᵉ type-impredicative-id-Propᵉ
  equiv-impredicative-id-Propᵉ =
    equiv-iffᵉ
      ( Id-Propᵉ Aᵉ xᵉ yᵉ)
      ( impredicative-id-Propᵉ)
      ( map-impredicative-id-Propᵉ)
      ( map-inv-impredicative-id-Propᵉ)
```

## Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}

## External links

-ᵉ [Constructingᵉ coproductᵉ typesᵉ andᵉ booleanᵉ typesᵉ fromᵉ universes](https://mathoverflow.net/questions/457904/constructing-coproduct-types-and-boolean-types-from-universesᵉ)
  atᵉ mathoverflowᵉ