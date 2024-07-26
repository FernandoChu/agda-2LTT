# Tight apartness relations

```agda
module foundation.tight-apartness-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relationsᵉ
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.negationᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Aᵉ [relation](foundation.binary-relations.mdᵉ) `R`ᵉ isᵉ saidᵉ to beᵉ **tight**ᵉ ifᵉ forᵉ
everyᵉ `xᵉ yᵉ : A`ᵉ weᵉ haveᵉ `¬ᵉ (Rᵉ xᵉ yᵉ) → (xᵉ ＝ᵉ y)`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Aᵉ → Aᵉ → Propᵉ l2ᵉ)
  where

  is-tightᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-tightᵉ = (xᵉ yᵉ : Aᵉ) → ¬ᵉ (type-Propᵉ (Rᵉ xᵉ yᵉ)) → xᵉ ＝ᵉ yᵉ

  is-tight-apartness-relationᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-tight-apartness-relationᵉ =
    is-apartness-relationᵉ Rᵉ ×ᵉ is-tightᵉ

is-tight-Apartness-Relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Apartness-Relationᵉ l2ᵉ Aᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-tight-Apartness-Relationᵉ Rᵉ = is-tightᵉ (rel-Apartness-Relationᵉ Rᵉ)

Tight-Apartness-Relationᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Tight-Apartness-Relationᵉ l2ᵉ Aᵉ =
  Σᵉ (Apartness-Relationᵉ l2ᵉ Aᵉ) (is-tight-Apartness-Relationᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Tight-Apartness-Relationᵉ l2ᵉ Aᵉ)
  where

  apartness-relation-Tight-Apartness-Relationᵉ :
    Apartness-Relationᵉ l2ᵉ Aᵉ
  apartness-relation-Tight-Apartness-Relationᵉ = pr1ᵉ Rᵉ

  is-tight-apartness-relation-Tight-Apartness-Relationᵉ :
    is-tight-Apartness-Relationᵉ apartness-relation-Tight-Apartness-Relationᵉ
  is-tight-apartness-relation-Tight-Apartness-Relationᵉ = pr2ᵉ Rᵉ
```

### Types with tight apartness

```agda
Type-With-Tight-Apartnessᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Type-With-Tight-Apartnessᵉ l1ᵉ l2ᵉ =
  Σᵉ ( Type-With-Apartnessᵉ l1ᵉ l2ᵉ)
    ( λ Xᵉ → is-tightᵉ (rel-apart-Type-With-Apartnessᵉ Xᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Type-With-Tight-Apartnessᵉ l1ᵉ l2ᵉ)
  where

  type-with-apartness-Type-With-Tight-Apartnessᵉ : Type-With-Apartnessᵉ l1ᵉ l2ᵉ
  type-with-apartness-Type-With-Tight-Apartnessᵉ = pr1ᵉ Xᵉ

  type-Type-With-Tight-Apartnessᵉ : UUᵉ l1ᵉ
  type-Type-With-Tight-Apartnessᵉ =
    type-Type-With-Apartnessᵉ type-with-apartness-Type-With-Tight-Apartnessᵉ

  rel-apart-Type-With-Tight-Apartnessᵉ :
    Relation-Propᵉ l2ᵉ type-Type-With-Tight-Apartnessᵉ
  rel-apart-Type-With-Tight-Apartnessᵉ =
    rel-apart-Type-With-Apartnessᵉ type-with-apartness-Type-With-Tight-Apartnessᵉ

  apart-Type-With-Tight-Apartnessᵉ :
    Relationᵉ l2ᵉ type-Type-With-Tight-Apartnessᵉ
  apart-Type-With-Tight-Apartnessᵉ =
    apart-Type-With-Apartnessᵉ type-with-apartness-Type-With-Tight-Apartnessᵉ

  is-tight-apart-Type-With-Tight-Apartnessᵉ :
    is-tightᵉ rel-apart-Type-With-Tight-Apartnessᵉ
  is-tight-apart-Type-With-Tight-Apartnessᵉ = pr2ᵉ Xᵉ
```

## Properties

### The apartness relation of functions into a type with tight apartness is tight

```agda
is-tight-apartness-function-into-Type-With-Tight-Apartnessᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Yᵉ : Type-With-Tight-Apartnessᵉ l2ᵉ l3ᵉ) →
  is-tightᵉ
    ( rel-apart-function-into-Type-With-Apartnessᵉ Xᵉ
      ( type-with-apartness-Type-With-Tight-Apartnessᵉ Yᵉ))
is-tight-apartness-function-into-Type-With-Tight-Apartnessᵉ Yᵉ fᵉ gᵉ Hᵉ =
  eq-htpyᵉ
    ( λ xᵉ →
      is-tight-apart-Type-With-Tight-Apartnessᵉ Yᵉ
        ( fᵉ xᵉ)
        ( gᵉ xᵉ)
        ( λ uᵉ → Hᵉ ( unit-trunc-Propᵉ (xᵉ ,ᵉ uᵉ))))

exp-Type-With-Tight-Apartnessᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) → Type-With-Tight-Apartnessᵉ l2ᵉ l3ᵉ →
  Type-With-Tight-Apartnessᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l3ᵉ)
pr1ᵉ (exp-Type-With-Tight-Apartnessᵉ Xᵉ Yᵉ) =
  exp-Type-With-Apartnessᵉ Xᵉ (type-with-apartness-Type-With-Tight-Apartnessᵉ Yᵉ)
pr2ᵉ (exp-Type-With-Tight-Apartnessᵉ Xᵉ Yᵉ) =
  is-tight-apartness-function-into-Type-With-Tight-Apartnessᵉ Yᵉ
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ MRR88ᵉ}}