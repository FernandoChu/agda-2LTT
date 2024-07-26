# Apartness relations

```agda
module foundation.apartness-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.disjunctionᵉ
open import foundation.existential-quantificationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universal-quantificationᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.negationᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Anᵉ **apartnessᵉ relation**ᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ
[relation](foundation.binary-relations.mdᵉ) `R`ᵉ whichᵉ isᵉ

-ᵉ **Antireflexive:**ᵉ Forᵉ anyᵉ `aᵉ : A`ᵉ weᵉ haveᵉ `¬ᵉ (Rᵉ aᵉ a)`ᵉ
-ᵉ **Symmetric:**ᵉ Forᵉ anyᵉ `aᵉ bᵉ : A`ᵉ weᵉ haveᵉ `Rᵉ aᵉ bᵉ → Rᵉ bᵉ a`ᵉ
-ᵉ **Cotransitive:**ᵉ Forᵉ anyᵉ `aᵉ bᵉ cᵉ : A`ᵉ weᵉ haveᵉ `Rᵉ aᵉ bᵉ → Rᵉ aᵉ cᵉ ∨ᵉ Rᵉ bᵉ c`.ᵉ

Theᵉ ideaᵉ ofᵉ anᵉ apartnessᵉ relationᵉ `R`ᵉ isᵉ thatᵉ `Rᵉ aᵉ b`ᵉ holdsᵉ ifᵉ youᵉ canᵉ
positivelyᵉ establishᵉ aᵉ differenceᵉ betweenᵉ `a`ᵉ andᵉ `b`.ᵉ Forᵉ example,ᵉ twoᵉ subsetsᵉ
`A`ᵉ andᵉ `B`ᵉ ofᵉ aᵉ typeᵉ `X`ᵉ areᵉ apartᵉ ifᵉ weᵉ canᵉ findᵉ anᵉ elementᵉ thatᵉ isᵉ in theᵉ
[symmetricᵉ difference](foundation.symmetric-difference.mdᵉ) ofᵉ `A`ᵉ andᵉ `B`.ᵉ

## Definitions

### Apartness relations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Aᵉ → Aᵉ → Propᵉ l2ᵉ)
  where

  is-antireflexiveᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-antireflexiveᵉ = (aᵉ : Aᵉ) → ¬ᵉ (type-Propᵉ (Rᵉ aᵉ aᵉ))

  is-consistentᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-consistentᵉ = (aᵉ bᵉ : Aᵉ) → (aᵉ ＝ᵉ bᵉ) → ¬ᵉ (type-Propᵉ (Rᵉ aᵉ bᵉ))

  is-cotransitive-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-cotransitive-Propᵉ =
    ∀'ᵉ Aᵉ (λ aᵉ → ∀'ᵉ Aᵉ (λ bᵉ → ∀'ᵉ Aᵉ (λ cᵉ → Rᵉ aᵉ bᵉ ⇒ᵉ (Rᵉ aᵉ cᵉ ∨ᵉ Rᵉ bᵉ cᵉ))))

  is-cotransitiveᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-cotransitiveᵉ = type-Propᵉ is-cotransitive-Propᵉ

  is-apartness-relationᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-apartness-relationᵉ =
    ( is-antireflexiveᵉ) ×ᵉ
    ( is-symmetricᵉ (λ xᵉ yᵉ → type-Propᵉ (Rᵉ xᵉ yᵉ))) ×ᵉ
    ( is-cotransitiveᵉ)

Apartness-Relationᵉ : {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Apartness-Relationᵉ l2ᵉ Aᵉ =
  Σᵉ (Relation-Propᵉ l2ᵉ Aᵉ) (is-apartness-relationᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Apartness-Relationᵉ l2ᵉ Aᵉ)
  where

  rel-Apartness-Relationᵉ : Aᵉ → Aᵉ → Propᵉ l2ᵉ
  rel-Apartness-Relationᵉ = pr1ᵉ Rᵉ

  apart-Apartness-Relationᵉ : Aᵉ → Aᵉ → UUᵉ l2ᵉ
  apart-Apartness-Relationᵉ xᵉ yᵉ = type-Propᵉ (rel-Apartness-Relationᵉ xᵉ yᵉ)

  antirefl-Apartness-Relationᵉ : is-antireflexiveᵉ rel-Apartness-Relationᵉ
  antirefl-Apartness-Relationᵉ = pr1ᵉ (pr2ᵉ Rᵉ)

  consistent-Apartness-Relationᵉ : is-consistentᵉ rel-Apartness-Relationᵉ
  consistent-Apartness-Relationᵉ xᵉ .xᵉ reflᵉ =
    antirefl-Apartness-Relationᵉ xᵉ

  symmetric-Apartness-Relationᵉ : is-symmetricᵉ apart-Apartness-Relationᵉ
  symmetric-Apartness-Relationᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Rᵉ))

  cotransitive-Apartness-Relationᵉ : is-cotransitiveᵉ rel-Apartness-Relationᵉ
  cotransitive-Apartness-Relationᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ Rᵉ))
```

### Types equipped with apartness relation

```agda
Type-With-Apartnessᵉ :
  (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Type-With-Apartnessᵉ l1ᵉ l2ᵉ =
  Σᵉ (UUᵉ l1ᵉ) (Apartness-Relationᵉ l2ᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Type-With-Apartnessᵉ l1ᵉ l2ᵉ)
  where

  type-Type-With-Apartnessᵉ : UUᵉ l1ᵉ
  type-Type-With-Apartnessᵉ = pr1ᵉ Aᵉ

  apartness-relation-Type-With-Apartnessᵉ :
    Apartness-Relationᵉ l2ᵉ type-Type-With-Apartnessᵉ
  apartness-relation-Type-With-Apartnessᵉ = pr2ᵉ Aᵉ

  rel-apart-Type-With-Apartnessᵉ : Relation-Propᵉ l2ᵉ type-Type-With-Apartnessᵉ
  rel-apart-Type-With-Apartnessᵉ =
    rel-Apartness-Relationᵉ apartness-relation-Type-With-Apartnessᵉ

  apart-Type-With-Apartnessᵉ :
    (xᵉ yᵉ : type-Type-With-Apartnessᵉ) → UUᵉ l2ᵉ
  apart-Type-With-Apartnessᵉ =
    apart-Apartness-Relationᵉ apartness-relation-Type-With-Apartnessᵉ

  antirefl-apart-Type-With-Apartnessᵉ :
    is-antireflexiveᵉ rel-apart-Type-With-Apartnessᵉ
  antirefl-apart-Type-With-Apartnessᵉ =
    antirefl-Apartness-Relationᵉ apartness-relation-Type-With-Apartnessᵉ

  consistent-apart-Type-With-Apartnessᵉ :
    is-consistentᵉ rel-apart-Type-With-Apartnessᵉ
  consistent-apart-Type-With-Apartnessᵉ =
    consistent-Apartness-Relationᵉ apartness-relation-Type-With-Apartnessᵉ

  symmetric-apart-Type-With-Apartnessᵉ :
    is-symmetricᵉ apart-Type-With-Apartnessᵉ
  symmetric-apart-Type-With-Apartnessᵉ =
    symmetric-Apartness-Relationᵉ apartness-relation-Type-With-Apartnessᵉ

  cotransitive-apart-Type-With-Apartnessᵉ :
    is-cotransitiveᵉ rel-apart-Type-With-Apartnessᵉ
  cotransitive-apart-Type-With-Apartnessᵉ =
    cotransitive-Apartness-Relationᵉ apartness-relation-Type-With-Apartnessᵉ
```

### Apartness on the type of functions into a type with an apartness relation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : Type-With-Apartnessᵉ l2ᵉ l3ᵉ)
  where

  rel-apart-function-into-Type-With-Apartnessᵉ :
    Relation-Propᵉ (l1ᵉ ⊔ l3ᵉ) (Xᵉ → type-Type-With-Apartnessᵉ Yᵉ)
  rel-apart-function-into-Type-With-Apartnessᵉ fᵉ gᵉ =
    ∃ᵉ Xᵉ (λ xᵉ → rel-apart-Type-With-Apartnessᵉ Yᵉ (fᵉ xᵉ) (gᵉ xᵉ))

  apart-function-into-Type-With-Apartnessᵉ :
    Relationᵉ (l1ᵉ ⊔ l3ᵉ) (Xᵉ → type-Type-With-Apartnessᵉ Yᵉ)
  apart-function-into-Type-With-Apartnessᵉ fᵉ gᵉ =
    type-Propᵉ (rel-apart-function-into-Type-With-Apartnessᵉ fᵉ gᵉ)

  is-prop-apart-function-into-Type-With-Apartnessᵉ :
    (fᵉ gᵉ : Xᵉ → type-Type-With-Apartnessᵉ Yᵉ) →
    is-propᵉ (apart-function-into-Type-With-Apartnessᵉ fᵉ gᵉ)
  is-prop-apart-function-into-Type-With-Apartnessᵉ fᵉ gᵉ =
    is-prop-type-Propᵉ (rel-apart-function-into-Type-With-Apartnessᵉ fᵉ gᵉ)
```

## Properties

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : Type-With-Apartnessᵉ l2ᵉ l3ᵉ)
  where

  is-antireflexive-apart-function-into-Type-With-Apartnessᵉ :
    is-antireflexiveᵉ (rel-apart-function-into-Type-With-Apartnessᵉ Xᵉ Yᵉ)
  is-antireflexive-apart-function-into-Type-With-Apartnessᵉ fᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( empty-Propᵉ)
      ( λ (xᵉ ,ᵉ aᵉ) → antirefl-apart-Type-With-Apartnessᵉ Yᵉ (fᵉ xᵉ) aᵉ)

  is-symmetric-apart-function-into-Type-With-Apartnessᵉ :
    is-symmetricᵉ (apart-function-into-Type-With-Apartnessᵉ Xᵉ Yᵉ)
  is-symmetric-apart-function-into-Type-With-Apartnessᵉ fᵉ gᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( rel-apart-function-into-Type-With-Apartnessᵉ Xᵉ Yᵉ gᵉ fᵉ)
      ( λ (xᵉ ,ᵉ aᵉ) →
        unit-trunc-Propᵉ
          ( xᵉ ,ᵉ symmetric-apart-Type-With-Apartnessᵉ Yᵉ (fᵉ xᵉ) (gᵉ xᵉ) aᵉ))

  abstract
    is-cotransitive-apart-function-into-Type-With-Apartnessᵉ :
      is-cotransitiveᵉ (rel-apart-function-into-Type-With-Apartnessᵉ Xᵉ Yᵉ)
    is-cotransitive-apart-function-into-Type-With-Apartnessᵉ fᵉ gᵉ hᵉ Hᵉ =
      apply-universal-property-trunc-Propᵉ Hᵉ
        ( disjunction-Propᵉ
          ( rel-apart-function-into-Type-With-Apartnessᵉ Xᵉ Yᵉ fᵉ hᵉ)
          ( rel-apart-function-into-Type-With-Apartnessᵉ Xᵉ Yᵉ gᵉ hᵉ))
        ( λ (xᵉ ,ᵉ aᵉ) →
          apply-universal-property-trunc-Propᵉ
            ( cotransitive-apart-Type-With-Apartnessᵉ Yᵉ (fᵉ xᵉ) (gᵉ xᵉ) (hᵉ xᵉ) aᵉ)
            ( disjunction-Propᵉ
              ( rel-apart-function-into-Type-With-Apartnessᵉ Xᵉ Yᵉ fᵉ hᵉ)
              ( rel-apart-function-into-Type-With-Apartnessᵉ Xᵉ Yᵉ gᵉ hᵉ))
            ( λ where
              ( inlᵉ bᵉ) → inl-disjunctionᵉ (intro-existsᵉ xᵉ bᵉ)
              ( inrᵉ bᵉ) → inr-disjunctionᵉ (intro-existsᵉ xᵉ bᵉ)))

  exp-Type-With-Apartnessᵉ : Type-With-Apartnessᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l3ᵉ)
  pr1ᵉ exp-Type-With-Apartnessᵉ = Xᵉ → type-Type-With-Apartnessᵉ Yᵉ
  pr1ᵉ (pr2ᵉ exp-Type-With-Apartnessᵉ) =
    rel-apart-function-into-Type-With-Apartnessᵉ Xᵉ Yᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ exp-Type-With-Apartnessᵉ)) =
    is-antireflexive-apart-function-into-Type-With-Apartnessᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ exp-Type-With-Apartnessᵉ))) =
    is-symmetric-apart-function-into-Type-With-Apartnessᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ exp-Type-With-Apartnessᵉ))) =
    is-cotransitive-apart-function-into-Type-With-Apartnessᵉ
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ MRR88ᵉ}}