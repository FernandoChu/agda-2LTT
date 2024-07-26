# Countable sets

```agda
module set-theory.countable-setsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.type-arithmetic-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-subtypesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-coproduct-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.maybeᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.setsᵉ
open import foundation.shifting-sequencesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.identity-typesᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ setᵉ `X`ᵉ isᵉ saidᵉ to beᵉ countableᵉ ifᵉ thereᵉ isᵉ aᵉ surjectiveᵉ mapᵉ `fᵉ : ℕᵉ → Xᵉ +ᵉ 1`.ᵉ
Equivalently,ᵉ aᵉ setᵉ `X`ᵉ isᵉ countableᵉ ifᵉ thereᵉ isᵉ aᵉ surjectiveᵉ mapᵉ
`fᵉ : type-decidable-subsetᵉ Pᵉ → X`ᵉ forᵉ someᵉ decidableᵉ subsetᵉ `P`ᵉ ofᵉ `X`.ᵉ

## Definition

### First definition of countable types

```agda
module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ)
  where

  enumerationᵉ : UUᵉ lᵉ
  enumerationᵉ = Σᵉ (ℕᵉ → Maybeᵉ (type-Setᵉ Xᵉ)) is-surjectiveᵉ

  map-enumerationᵉ : enumerationᵉ → (ℕᵉ → Maybeᵉ (type-Setᵉ Xᵉ))
  map-enumerationᵉ Eᵉ = pr1ᵉ Eᵉ

  is-surjective-map-enumerationᵉ :
    (Eᵉ : enumerationᵉ) → is-surjectiveᵉ (map-enumerationᵉ Eᵉ)
  is-surjective-map-enumerationᵉ Eᵉ = pr2ᵉ Eᵉ

  is-countable-Propᵉ : Propᵉ lᵉ
  is-countable-Propᵉ =
    ∃ᵉ (ℕᵉ → Maybeᵉ (type-Setᵉ Xᵉ)) (is-surjective-Propᵉ)

  is-countableᵉ : UUᵉ lᵉ
  is-countableᵉ = type-Propᵉ (is-countable-Propᵉ)

  is-prop-is-countableᵉ : is-propᵉ is-countableᵉ
  is-prop-is-countableᵉ = is-prop-type-Propᵉ is-countable-Propᵉ
```

### Second definition of countable types

```agda
module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ)
  where

  decidable-subprojection-ℕᵉ : UUᵉ (lsuc lᵉ ⊔ lᵉ)
  decidable-subprojection-ℕᵉ =
    Σᵉ ( decidable-subtypeᵉ lᵉ ℕᵉ)
      ( λ Pᵉ → type-decidable-subtypeᵉ Pᵉ ↠ᵉ type-Setᵉ Xᵉ)

  is-countable-Prop'ᵉ : Propᵉ (lsuc lᵉ ⊔ lᵉ)
  is-countable-Prop'ᵉ =
    exists-structure-Propᵉ
      ( decidable-subtypeᵉ lᵉ ℕᵉ)
      ( λ Pᵉ → type-decidable-subtypeᵉ Pᵉ ↠ᵉ type-Setᵉ Xᵉ)

  is-countable'ᵉ : UUᵉ (lsuc lᵉ ⊔ lᵉ)
  is-countable'ᵉ = type-Propᵉ is-countable-Prop'ᵉ

  is-prop-is-countable'ᵉ : is-propᵉ is-countable'ᵉ
  is-prop-is-countable'ᵉ = is-prop-type-Propᵉ is-countable-Prop'ᵉ
```

### Third definition of countable types

Ifᵉ aᵉ setᵉ `X`ᵉ isᵉ inhabited,ᵉ thenᵉ itᵉ isᵉ countableᵉ ifᵉ andᵉ onlyᵉ ifᵉ thereᵉ isᵉ aᵉ
surjectiveᵉ mapᵉ `fᵉ : ℕᵉ → X`.ᵉ Letᵉ usᵉ callᵉ theᵉ latterᵉ asᵉ "directlyᵉ countable".ᵉ

```agda
is-directly-countable-Propᵉ : {lᵉ : Level} → Setᵉ lᵉ → Propᵉ lᵉ
is-directly-countable-Propᵉ Xᵉ =
  ∃ᵉ (ℕᵉ → type-Setᵉ Xᵉ) (is-surjective-Propᵉ)

is-directly-countableᵉ : {lᵉ : Level} → Setᵉ lᵉ → UUᵉ lᵉ
is-directly-countableᵉ Xᵉ = type-Propᵉ (is-directly-countable-Propᵉ Xᵉ)

is-prop-is-directly-countableᵉ :
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) → is-propᵉ (is-directly-countableᵉ Xᵉ)
is-prop-is-directly-countableᵉ Xᵉ = is-prop-type-Propᵉ
  (is-directly-countable-Propᵉ Xᵉ)

module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) (aᵉ : type-Setᵉ Xᵉ)
  where

  is-directly-countable-is-countableᵉ :
    is-countableᵉ Xᵉ → is-directly-countableᵉ Xᵉ
  is-directly-countable-is-countableᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( is-directly-countable-Propᵉ Xᵉ)
      ( λ Pᵉ →
        unit-trunc-Propᵉ
          ( pairᵉ
            ( fᵉ ∘ᵉ (pr1ᵉ Pᵉ))
            ( is-surjective-compᵉ is-surjective-fᵉ (pr2ᵉ Pᵉ))))
    where
    fᵉ : Maybeᵉ (type-Setᵉ Xᵉ) → type-Setᵉ Xᵉ
    fᵉ (inlᵉ xᵉ) = xᵉ
    fᵉ (inrᵉ starᵉ) = aᵉ

    is-surjective-fᵉ : is-surjectiveᵉ fᵉ
    is-surjective-fᵉ xᵉ = unit-trunc-Propᵉ (pairᵉ (inlᵉ xᵉ) reflᵉ)

  abstract
    is-countable-is-directly-countableᵉ :
      is-directly-countableᵉ Xᵉ → is-countableᵉ Xᵉ
    is-countable-is-directly-countableᵉ Hᵉ =
      apply-universal-property-trunc-Propᵉ Hᵉ
        ( is-countable-Propᵉ Xᵉ)
        ( λ Pᵉ →
          unit-trunc-Propᵉ
            ( ( λ where
                zero-ℕᵉ → inrᵉ starᵉ
                (succ-ℕᵉ nᵉ) → inlᵉ ((shift-ℕᵉ aᵉ (pr1ᵉ Pᵉ)) nᵉ)) ,ᵉ
              ( λ where
                ( inlᵉ xᵉ) →
                  apply-universal-property-trunc-Propᵉ (pr2ᵉ Pᵉ xᵉ)
                    ( trunc-Propᵉ (fiberᵉ _ (inlᵉ xᵉ)))
                    ( λ (nᵉ ,ᵉ pᵉ) →
                      unit-trunc-Propᵉ
                        ( succ-ℕᵉ (succ-ℕᵉ nᵉ) ,ᵉ apᵉ inlᵉ pᵉ))
                ( inrᵉ starᵉ) → unit-trunc-Propᵉ (zero-ℕᵉ ,ᵉ reflᵉ))))
```

## Properties

### The two definitions of countability are equivalent

First,ᵉ weᵉ willᵉ proveᵉ `is-countableᵉ Xᵉ → is-countable'ᵉ X`.ᵉ

```agda
module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ)
  where

  decidable-subprojection-ℕ-enumerationᵉ :
    enumerationᵉ Xᵉ → decidable-subprojection-ℕᵉ Xᵉ
  pr1ᵉ (pr1ᵉ (decidable-subprojection-ℕ-enumerationᵉ (fᵉ ,ᵉ Hᵉ)) nᵉ) =
    fᵉ nᵉ ≠ᵉ inrᵉ starᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (decidable-subprojection-ℕ-enumerationᵉ (fᵉ ,ᵉ Hᵉ)) nᵉ)) =
    is-prop-negᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (decidable-subprojection-ℕ-enumerationᵉ (fᵉ ,ᵉ Hᵉ)) nᵉ)) =
    is-decidable-is-not-exception-Maybeᵉ (fᵉ nᵉ)
  pr1ᵉ (pr2ᵉ (decidable-subprojection-ℕ-enumerationᵉ (fᵉ ,ᵉ Hᵉ))) (nᵉ ,ᵉ pᵉ) =
    value-is-not-exception-Maybeᵉ (fᵉ nᵉ) pᵉ
  pr2ᵉ (pr2ᵉ (decidable-subprojection-ℕ-enumerationᵉ (fᵉ ,ᵉ Hᵉ))) xᵉ =
    apply-universal-property-trunc-Propᵉ (Hᵉ (inlᵉ xᵉ))
      ( trunc-Propᵉ (fiberᵉ _ xᵉ))
      ( λ (nᵉ ,ᵉ pᵉ) →
        unit-trunc-Propᵉ
          ( ( nᵉ ,ᵉ is-not-exception-is-value-Maybeᵉ (fᵉ nᵉ) (xᵉ ,ᵉ invᵉ pᵉ)) ,ᵉ
            ( is-injective-inlᵉ
              ( ( eq-is-not-exception-Maybeᵉ
                ( fᵉ nᵉ)
                ( is-not-exception-is-value-Maybeᵉ
                  ( fᵉ nᵉ) (xᵉ ,ᵉ invᵉ pᵉ))) ∙ᵉ
              ( pᵉ)))))

  is-countable'-is-countableᵉ :
    is-countableᵉ Xᵉ → is-countable'ᵉ Xᵉ
  is-countable'-is-countableᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( is-countable-Prop'ᵉ Xᵉ)
      ( λ Eᵉ → unit-trunc-Propᵉ (decidable-subprojection-ℕ-enumerationᵉ Eᵉ))
```

Second,ᵉ weᵉ willᵉ proveᵉ `is-countable'ᵉ Xᵉ → is-countableᵉ X`.ᵉ

```agda
cases-map-decidable-subtype-ℕᵉ :
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) →
  ( Pᵉ : decidable-subtypeᵉ lᵉ ℕᵉ) →
  ( fᵉ : type-decidable-subtypeᵉ Pᵉ → type-Setᵉ Xᵉ) →
  ( (nᵉ : ℕᵉ) → is-decidableᵉ (pr1ᵉ (Pᵉ nᵉ)) ->ᵉ Maybeᵉ (type-Setᵉ Xᵉ))
cases-map-decidable-subtype-ℕᵉ Xᵉ Pᵉ fᵉ nᵉ (inlᵉ xᵉ) = inlᵉ (fᵉ (nᵉ ,ᵉ xᵉ))
cases-map-decidable-subtype-ℕᵉ Xᵉ Pᵉ fᵉ nᵉ (inrᵉ xᵉ) = inrᵉ starᵉ

module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ)
  ( Pᵉ : decidable-subtypeᵉ lᵉ ℕᵉ)
  ( fᵉ : type-decidable-subtypeᵉ Pᵉ → type-Setᵉ Xᵉ)
  where

  shift-decidable-subtype-ℕᵉ : decidable-subtypeᵉ lᵉ ℕᵉ
  shift-decidable-subtype-ℕᵉ zero-ℕᵉ =
    ( raise-emptyᵉ lᵉ) ,ᵉ
    ( is-prop-raise-emptyᵉ ,ᵉ
      ( inrᵉ (is-empty-raise-emptyᵉ)))
  shift-decidable-subtype-ℕᵉ (succ-ℕᵉ nᵉ) = Pᵉ nᵉ

  map-shift-decidable-subtype-ℕᵉ :
    type-decidable-subtypeᵉ shift-decidable-subtype-ℕᵉ → type-Setᵉ Xᵉ
  map-shift-decidable-subtype-ℕᵉ (zero-ℕᵉ ,ᵉ map-raiseᵉ ())
  map-shift-decidable-subtype-ℕᵉ (succ-ℕᵉ nᵉ ,ᵉ pᵉ) = fᵉ (nᵉ ,ᵉ pᵉ)

  map-enumeration-decidable-subprojection-ℕᵉ : ℕᵉ → Maybeᵉ (type-Setᵉ Xᵉ)
  map-enumeration-decidable-subprojection-ℕᵉ nᵉ =
    cases-map-decidable-subtype-ℕᵉ
      ( Xᵉ)
      ( shift-decidable-subtype-ℕᵉ)
      ( map-shift-decidable-subtype-ℕᵉ)
      ( nᵉ)
      (pr2ᵉ (pr2ᵉ (shift-decidable-subtype-ℕᵉ nᵉ)))

  abstract
    is-surjective-map-enumeration-decidable-subprojection-ℕᵉ :
      ( is-surjectiveᵉ fᵉ) →
      ( is-surjectiveᵉ map-enumeration-decidable-subprojection-ℕᵉ)
    is-surjective-map-enumeration-decidable-subprojection-ℕᵉ Hᵉ (inlᵉ xᵉ) =
      ( apply-universal-property-trunc-Propᵉ (Hᵉ xᵉ)
        ( trunc-Propᵉ (fiberᵉ map-enumeration-decidable-subprojection-ℕᵉ (inlᵉ xᵉ)))
        ( λ where
          ( ( nᵉ ,ᵉ sᵉ) ,ᵉ reflᵉ) →
            unit-trunc-Propᵉ
              ( ( succ-ℕᵉ nᵉ) ,ᵉ
                ( apᵉ
                  ( cases-map-decidable-subtype-ℕᵉ Xᵉ
                    ( shift-decidable-subtype-ℕᵉ)
                    ( map-shift-decidable-subtype-ℕᵉ)
                    (succ-ℕᵉ nᵉ))
                  ( pr1ᵉ
                    ( is-prop-is-decidableᵉ (pr1ᵉ (pr2ᵉ (Pᵉ nᵉ)))
                      ( pr2ᵉ (pr2ᵉ (Pᵉ nᵉ)))
                      ( inlᵉ sᵉ)))))))
    is-surjective-map-enumeration-decidable-subprojection-ℕᵉ Hᵉ (inrᵉ starᵉ) =
      ( unit-trunc-Propᵉ (0ᵉ ,ᵉ reflᵉ))

module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ)
  where

  enumeration-decidable-subprojection-ℕᵉ :
    decidable-subprojection-ℕᵉ Xᵉ → enumerationᵉ Xᵉ
  enumeration-decidable-subprojection-ℕᵉ (Pᵉ ,ᵉ (fᵉ ,ᵉ Hᵉ)) =
    ( map-enumeration-decidable-subprojection-ℕᵉ Xᵉ Pᵉ fᵉ) ,ᵉ
    ( is-surjective-map-enumeration-decidable-subprojection-ℕᵉ Xᵉ Pᵉ fᵉ Hᵉ)

  is-countable-is-countable'ᵉ :
    is-countable'ᵉ Xᵉ → is-countableᵉ Xᵉ
  is-countable-is-countable'ᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( is-countable-Propᵉ Xᵉ)
      ( λ Dᵉ →
        ( unit-trunc-Propᵉ (enumeration-decidable-subprojection-ℕᵉ Dᵉ)))
```

## Useful Lemmas

Thereᵉ isᵉ aᵉ surjectionᵉ fromᵉ `(Maybeᵉ Aᵉ +ᵉ Maybeᵉ B)`ᵉ to `Maybeᵉ (Aᵉ +ᵉ B)`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  map-maybe-coproductᵉ : (Maybeᵉ Aᵉ +ᵉ Maybeᵉ Bᵉ) → Maybeᵉ (Aᵉ +ᵉ Bᵉ)
  map-maybe-coproductᵉ (inlᵉ (inlᵉ xᵉ)) = inlᵉ (inlᵉ xᵉ)
  map-maybe-coproductᵉ (inlᵉ (inrᵉ starᵉ)) = inrᵉ starᵉ
  map-maybe-coproductᵉ (inrᵉ (inlᵉ xᵉ)) = inlᵉ (inrᵉ xᵉ)
  map-maybe-coproductᵉ (inrᵉ (inrᵉ starᵉ)) = inrᵉ starᵉ

  is-surjective-map-maybe-coproductᵉ : is-surjectiveᵉ map-maybe-coproductᵉ
  is-surjective-map-maybe-coproductᵉ (inlᵉ (inlᵉ xᵉ)) =
    unit-trunc-Propᵉ ((inlᵉ (inlᵉ xᵉ)) ,ᵉ reflᵉ)
  is-surjective-map-maybe-coproductᵉ (inlᵉ (inrᵉ xᵉ)) =
    unit-trunc-Propᵉ ((inrᵉ (inlᵉ xᵉ)) ,ᵉ reflᵉ)
  is-surjective-map-maybe-coproductᵉ (inrᵉ starᵉ) =
    unit-trunc-Propᵉ ((inlᵉ (inrᵉ starᵉ)) ,ᵉ reflᵉ)
```

Thereᵉ isᵉ aᵉ surjectionᵉ fromᵉ `(Maybeᵉ Aᵉ ×ᵉ Maybeᵉ B)`ᵉ to `Maybeᵉ (Aᵉ ×ᵉ B)`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  map-maybe-productᵉ : (Maybeᵉ Aᵉ ×ᵉ Maybeᵉ Bᵉ) → Maybeᵉ (Aᵉ ×ᵉ Bᵉ)
  map-maybe-productᵉ (inlᵉ aᵉ ,ᵉ inlᵉ bᵉ) = inlᵉ (aᵉ ,ᵉ bᵉ)
  map-maybe-productᵉ (inlᵉ aᵉ ,ᵉ inrᵉ starᵉ) = inrᵉ starᵉ
  map-maybe-productᵉ (inrᵉ starᵉ ,ᵉ inlᵉ bᵉ) = inrᵉ starᵉ
  map-maybe-productᵉ (inrᵉ starᵉ ,ᵉ inrᵉ starᵉ) = inrᵉ starᵉ

  is-surjective-map-maybe-productᵉ : is-surjectiveᵉ map-maybe-productᵉ
  is-surjective-map-maybe-productᵉ (inlᵉ (aᵉ ,ᵉ bᵉ)) =
    unit-trunc-Propᵉ ((inlᵉ aᵉ ,ᵉ inlᵉ bᵉ) ,ᵉ reflᵉ)
  is-surjective-map-maybe-productᵉ (inrᵉ starᵉ) =
    unit-trunc-Propᵉ ((inrᵉ starᵉ ,ᵉ inrᵉ starᵉ) ,ᵉ reflᵉ)
```

## Examples

Theᵉ setᵉ ofᵉ naturalᵉ numbersᵉ ℕᵉ isᵉ itselfᵉ countable.ᵉ

```agda
abstract
  is-countable-ℕᵉ : is-countableᵉ ℕ-Setᵉ
  is-countable-ℕᵉ =
    unit-trunc-Propᵉ
      ( ( λ where
          zero-ℕᵉ → inrᵉ starᵉ
          (succ-ℕᵉ nᵉ) → inlᵉ nᵉ) ,ᵉ
        ( λ where
          ( inlᵉ nᵉ) → unit-trunc-Propᵉ (succ-ℕᵉ nᵉ ,ᵉ reflᵉ)
          ( inrᵉ starᵉ) → unit-trunc-Propᵉ (zero-ℕᵉ ,ᵉ reflᵉ)))
```

Theᵉ emptyᵉ setᵉ isᵉ countable.ᵉ

```agda
is-countable-emptyᵉ : is-countableᵉ empty-Setᵉ
is-countable-emptyᵉ =
  is-countable-is-countable'ᵉ
    ( empty-Setᵉ)
    ( unit-trunc-Propᵉ ((λ _ → empty-Decidable-Propᵉ) ,ᵉ (λ ()) ,ᵉ (λ ())))
```

Theᵉ unitᵉ setᵉ isᵉ countable.ᵉ

```agda
abstract
  is-countable-unitᵉ : is-countableᵉ unit-Setᵉ
  is-countable-unitᵉ =
    unit-trunc-Propᵉ
      ( ( λ where
          zero-ℕᵉ → inlᵉ starᵉ
          (succ-ℕᵉ xᵉ) → inrᵉ starᵉ) ,ᵉ
        ( λ where
          ( inlᵉ starᵉ) → unit-trunc-Propᵉ (0ᵉ ,ᵉ reflᵉ)
          ( inrᵉ starᵉ) → unit-trunc-Propᵉ (1ᵉ ,ᵉ reflᵉ)))
```

Ifᵉ `X`ᵉ andᵉ `Y`ᵉ areᵉ countableᵉ sets,ᵉ thenᵉ soᵉ isᵉ theirᵉ coproductᵉ `Xᵉ +ᵉ Y`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Setᵉ l1ᵉ) (Yᵉ : Setᵉ l2ᵉ)
  where

  is-countable-coproductᵉ :
    is-countableᵉ Xᵉ → is-countableᵉ Yᵉ → is-countableᵉ (coproduct-Setᵉ Xᵉ Yᵉ)
  is-countable-coproductᵉ Hᵉ H'ᵉ =
    apply-twice-universal-property-trunc-Propᵉ H'ᵉ Hᵉ
      ( is-countable-Propᵉ (coproduct-Setᵉ Xᵉ Yᵉ))
      ( λ h'ᵉ hᵉ →
        ( unit-trunc-Propᵉ
          ( pairᵉ
            ( map-maybe-coproductᵉ ∘ᵉ
              ( map-coproductᵉ (pr1ᵉ hᵉ) (pr1ᵉ h'ᵉ) ∘ᵉ map-ℕ-to-ℕ+ℕᵉ))
            ( is-surjective-compᵉ
              ( is-surjective-map-maybe-coproductᵉ)
              ( is-surjective-compᵉ
                ( is-surjective-map-coproductᵉ (pr2ᵉ hᵉ) (pr2ᵉ h'ᵉ))
                ( is-surjective-is-equivᵉ (is-equiv-map-ℕ-to-ℕ+ℕᵉ)))))))
```

Ifᵉ `X`ᵉ andᵉ `Y`ᵉ areᵉ countableᵉ sets,ᵉ thenᵉ soᵉ isᵉ theirᵉ coproductᵉ `Xᵉ ×ᵉ Y`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Setᵉ l1ᵉ) (Yᵉ : Setᵉ l2ᵉ)
  where

  is-countable-productᵉ :
    is-countableᵉ Xᵉ → is-countableᵉ Yᵉ → is-countableᵉ (product-Setᵉ Xᵉ Yᵉ)
  is-countable-productᵉ Hᵉ H'ᵉ =
    apply-twice-universal-property-trunc-Propᵉ H'ᵉ Hᵉ
      ( is-countable-Propᵉ (product-Setᵉ Xᵉ Yᵉ))
      ( λ h'ᵉ hᵉ →
        ( unit-trunc-Propᵉ
          ( pairᵉ
            ( map-maybe-productᵉ ∘ᵉ
              ( map-productᵉ (pr1ᵉ hᵉ) (pr1ᵉ h'ᵉ) ∘ᵉ map-ℕ-to-ℕ×ℕᵉ))
            ( is-surjective-compᵉ
              ( is-surjective-map-maybe-productᵉ)
              ( is-surjective-compᵉ
                ( is-surjective-map-productᵉ (pr2ᵉ hᵉ) (pr2ᵉ h'ᵉ))
                ( is-surjective-is-equivᵉ (is-equiv-map-ℕ-to-ℕ×ℕᵉ)))))))
```

Inᵉ particular,ᵉ theᵉ setsᵉ ℕᵉ +ᵉ ℕ,ᵉ ℕᵉ ×ᵉ ℕ,ᵉ andᵉ ℤᵉ areᵉ countable.ᵉ

```agda
is-countable-ℕ+ℕᵉ : is-countableᵉ (coproduct-Setᵉ ℕ-Setᵉ ℕ-Setᵉ)
is-countable-ℕ+ℕᵉ =
  is-countable-coproductᵉ ℕ-Setᵉ ℕ-Setᵉ is-countable-ℕᵉ is-countable-ℕᵉ

is-countable-ℕ×ℕᵉ : is-countableᵉ (product-Setᵉ ℕ-Setᵉ ℕ-Setᵉ)
is-countable-ℕ×ℕᵉ =
  is-countable-productᵉ ℕ-Setᵉ ℕ-Setᵉ is-countable-ℕᵉ is-countable-ℕᵉ

is-countable-ℤᵉ : is-countableᵉ (ℤ-Setᵉ)
is-countable-ℤᵉ =
  is-countable-coproductᵉ (ℕ-Setᵉ) (coproduct-Setᵉ unit-Setᵉ ℕ-Setᵉ)
    ( is-countable-ℕᵉ)
    ( is-countable-coproductᵉ (unit-Setᵉ) (ℕ-Setᵉ)
      ( is-countable-unitᵉ) (is-countable-ℕᵉ))
```

Allᵉ standartᵉ finiteᵉ setsᵉ areᵉ countable.ᵉ

```agda
is-countable-Fin-Setᵉ : (nᵉ : ℕᵉ) → is-countableᵉ (Fin-Setᵉ nᵉ)
is-countable-Fin-Setᵉ zero-ℕᵉ = is-countable-emptyᵉ
is-countable-Fin-Setᵉ (succ-ℕᵉ nᵉ) =
  is-countable-coproductᵉ (Fin-Setᵉ nᵉ) (unit-Setᵉ)
    ( is-countable-Fin-Setᵉ nᵉ) (is-countable-unitᵉ)
```