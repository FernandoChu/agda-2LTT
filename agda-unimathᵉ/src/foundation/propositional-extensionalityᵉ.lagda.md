# Propositional extensionality

```agda
module foundation.propositional-extensionalityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negationᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.univalenceᵉ
open import foundation.univalent-type-familiesᵉ
open import foundation.universal-property-contractible-typesᵉ
open import foundation.universal-property-empty-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

{{#conceptᵉ "Propositionalᵉ extensionality"ᵉ Agda=propositional-extensionalityᵉ}}
characterizesᵉ [identifications](foundation-core.identity-types.mdᵉ) ofᵉ
[propositions](foundation-core.propositions.md).ᵉ Itᵉ assertsᵉ thatᵉ forᵉ anyᵉ twoᵉ
propositionsᵉ `P`ᵉ andᵉ `Q`,ᵉ weᵉ haveᵉ `(Pᵉ ＝ᵉ Qᵉ) ≃ᵉ (Pᵉ ⇔ᵉ Q)`.ᵉ

**Note.**ᵉ Whileᵉ weᵉ deriveᵉ propositionalᵉ extensionalityᵉ fromᵉ theᵉ
[univalenceᵉ axiom](foundation-core.univalence.md),ᵉ itᵉ isᵉ aᵉ strictlyᵉ weakerᵉ
principle,ᵉ meaningᵉ thatᵉ theᵉ principleᵉ ofᵉ propositionalᵉ extensionalityᵉ doesᵉ notᵉ
implyᵉ univalence.ᵉ

## Properties

### Propositional extensionality

```agda
module _
  {l1ᵉ : Level}
  where

  abstract
    is-torsorial-iffᵉ :
      (Pᵉ : Propᵉ l1ᵉ) → is-torsorialᵉ (λ (Qᵉ : Propᵉ l1ᵉ) → type-Propᵉ Pᵉ ↔ᵉ type-Propᵉ Qᵉ)
    is-torsorial-iffᵉ Pᵉ =
      is-contr-equivᵉ
        ( Σᵉ (Propᵉ l1ᵉ) (λ Qᵉ → type-Propᵉ Pᵉ ≃ᵉ type-Propᵉ Qᵉ))
        ( equiv-totᵉ (equiv-equiv-iffᵉ Pᵉ))
        ( is-torsorial-Eq-subtypeᵉ
          ( is-torsorial-equivᵉ (type-Propᵉ Pᵉ))
          ( is-prop-is-propᵉ)
          ( type-Propᵉ Pᵉ)
          ( id-equivᵉ)
          ( is-prop-type-Propᵉ Pᵉ))

  abstract
    is-equiv-iff-eqᵉ : (Pᵉ Qᵉ : Propᵉ l1ᵉ) → is-equivᵉ (iff-eqᵉ {l1ᵉ} {Pᵉ} {Qᵉ})
    is-equiv-iff-eqᵉ Pᵉ =
      fundamental-theorem-idᵉ (is-torsorial-iffᵉ Pᵉ) (λ Qᵉ → iff-eqᵉ {Pᵉ = Pᵉ} {Qᵉ})

  propositional-extensionalityᵉ :
    (Pᵉ Qᵉ : Propᵉ l1ᵉ) → (Pᵉ ＝ᵉ Qᵉ) ≃ᵉ (type-Propᵉ Pᵉ ↔ᵉ type-Propᵉ Qᵉ)
  pr1ᵉ (propositional-extensionalityᵉ Pᵉ Qᵉ) = iff-eqᵉ
  pr2ᵉ (propositional-extensionalityᵉ Pᵉ Qᵉ) = is-equiv-iff-eqᵉ Pᵉ Qᵉ

  eq-iff'ᵉ : (Pᵉ Qᵉ : Propᵉ l1ᵉ) → type-Propᵉ Pᵉ ↔ᵉ type-Propᵉ Qᵉ → Pᵉ ＝ᵉ Qᵉ
  eq-iff'ᵉ Pᵉ Qᵉ = map-inv-is-equivᵉ (is-equiv-iff-eqᵉ Pᵉ Qᵉ)

  eq-iffᵉ :
    {Pᵉ Qᵉ : Propᵉ l1ᵉ} →
    (type-Propᵉ Pᵉ → type-Propᵉ Qᵉ) → (type-Propᵉ Qᵉ → type-Propᵉ Pᵉ) → Pᵉ ＝ᵉ Qᵉ
  eq-iffᵉ {Pᵉ} {Qᵉ} fᵉ gᵉ = eq-iff'ᵉ Pᵉ Qᵉ (pairᵉ fᵉ gᵉ)

  eq-equiv-Propᵉ :
    {Pᵉ Qᵉ : Propᵉ l1ᵉ} → type-Propᵉ Pᵉ ≃ᵉ type-Propᵉ Qᵉ → Pᵉ ＝ᵉ Qᵉ
  eq-equiv-Propᵉ eᵉ =
    eq-iffᵉ (map-equivᵉ eᵉ) (map-inv-equivᵉ eᵉ)

  equiv-eq-Propᵉ :
    {Pᵉ Qᵉ : Propᵉ l1ᵉ} → Pᵉ ＝ᵉ Qᵉ → type-Propᵉ Pᵉ ≃ᵉ type-Propᵉ Qᵉ
  equiv-eq-Propᵉ {Pᵉ} reflᵉ = id-equivᵉ

  is-torsorial-equiv-Propᵉ :
    (Pᵉ : Propᵉ l1ᵉ) → is-torsorialᵉ (λ Qᵉ → type-Propᵉ Pᵉ ≃ᵉ type-Propᵉ Qᵉ)
  is-torsorial-equiv-Propᵉ Pᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (Propᵉ l1ᵉ) (λ Qᵉ → type-Propᵉ Pᵉ ↔ᵉ type-Propᵉ Qᵉ))
      ( equiv-totᵉ (equiv-equiv-iffᵉ Pᵉ))
      ( is-torsorial-iffᵉ Pᵉ)
```

### The type of propositions is a set

```agda
is-set-type-Propᵉ : {lᵉ : Level} → is-setᵉ (Propᵉ lᵉ)
is-set-type-Propᵉ Pᵉ Qᵉ =
  is-prop-equivᵉ
    ( propositional-extensionalityᵉ Pᵉ Qᵉ)
    ( is-prop-iff-Propᵉ Pᵉ Qᵉ)

Prop-Setᵉ : (lᵉ : Level) → Setᵉ (lsuc lᵉ)
pr1ᵉ (Prop-Setᵉ lᵉ) = Propᵉ lᵉ
pr2ᵉ (Prop-Setᵉ lᵉ) = is-set-type-Propᵉ
```

### The canonical type family over `Prop` is univalent

```agda
is-univalent-type-Propᵉ : {lᵉ : Level} → is-univalentᵉ (type-Propᵉ {lᵉ})
is-univalent-type-Propᵉ Pᵉ =
  fundamental-theorem-idᵉ
    ( is-torsorial-equiv-Propᵉ Pᵉ)
    ( λ Qᵉ → equiv-trᵉ type-Propᵉ)
```

### The type of true propositions is contractible

```agda
abstract
  is-torsorial-true-Propᵉ :
    {l1ᵉ : Level} → is-torsorialᵉ (λ (Pᵉ : Propᵉ l1ᵉ) → type-Propᵉ Pᵉ)
  is-torsorial-true-Propᵉ {l1ᵉ} =
    is-contr-equivᵉ
      ( Σᵉ (Propᵉ l1ᵉ) (λ Pᵉ → raise-unitᵉ l1ᵉ ↔ᵉ type-Propᵉ Pᵉ))
      ( equiv-totᵉ
        ( λ Pᵉ →
          inv-equivᵉ
            ( ( equiv-universal-property-contrᵉ
                ( raise-starᵉ)
                ( is-contr-raise-unitᵉ)
                ( type-Propᵉ Pᵉ)) ∘eᵉ
              ( right-unit-law-product-is-contrᵉ
                ( is-contr-Πᵉ
                  ( λ _ →
                    is-proof-irrelevant-is-propᵉ
                      ( is-prop-raise-unitᵉ)
                      ( raise-starᵉ)))))))
      ( is-torsorial-iffᵉ (raise-unit-Propᵉ l1ᵉ))
```

### The type of false propositions is contractible

```agda
abstract
  is-torsorial-false-Propᵉ :
    {l1ᵉ : Level} → is-torsorialᵉ (λ (Pᵉ : Propᵉ l1ᵉ) → ¬ᵉ (type-Propᵉ Pᵉ))
  is-torsorial-false-Propᵉ {l1ᵉ} =
    is-contr-equivᵉ
      ( Σᵉ (Propᵉ l1ᵉ) (λ Pᵉ → raise-emptyᵉ l1ᵉ ↔ᵉ type-Propᵉ Pᵉ))
      ( equiv-totᵉ
        ( λ Pᵉ →
          inv-equivᵉ
            ( ( inv-equivᵉ
                ( equiv-postcompᵉ (type-Propᵉ Pᵉ) (compute-raiseᵉ l1ᵉ emptyᵉ))) ∘eᵉ
              ( left-unit-law-product-is-contrᵉ
                ( universal-property-empty-is-emptyᵉ
                  ( raise-emptyᵉ l1ᵉ)
                  ( is-empty-raise-emptyᵉ)
                  ( type-Propᵉ Pᵉ))))))
      ( is-torsorial-iffᵉ (raise-empty-Propᵉ l1ᵉ))
```

## Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}

## External links

-ᵉ [propositionalᵉ extensionality](https://ncatlab.org/nlab/show/propositional+extensionalityᵉ)
  atᵉ $n$Lab.ᵉ