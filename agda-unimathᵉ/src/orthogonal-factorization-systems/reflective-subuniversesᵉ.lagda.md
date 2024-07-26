# Reflective subuniverses

```agda
module orthogonal-factorization-systems.reflective-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.retractionsᵉ
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.local-typesᵉ
open import orthogonal-factorization-systems.localizations-subuniversesᵉ
open import orthogonal-factorization-systems.modal-inductionᵉ
open import orthogonal-factorization-systems.modal-operatorsᵉ
open import orthogonal-factorization-systems.modal-subuniverse-inductionᵉ
```

</details>

## Idea

Aᵉ **reflectiveᵉ subuniverse**ᵉ isᵉ aᵉ [subuniverse](foundation.subuniverses.mdᵉ) `P`ᵉ
togetherᵉ with aᵉ reflectingᵉ operatorᵉ `○ᵉ : UUᵉ → UU`ᵉ thatᵉ takeᵉ valuesᵉ in `P`,ᵉ andᵉ aᵉ
[modalᵉ unit](orthogonal-factorization-systems.modal-operators.mdᵉ) `Aᵉ → ○ᵉ A`ᵉ forᵉ
allᵉ [smallᵉ types](foundation-core.small-types.mdᵉ) `A`,ᵉ with theᵉ propertyᵉ thatᵉ
theᵉ typesᵉ in `P`ᵉ areᵉ [local](orthogonal-factorization-systems.local-types.mdᵉ) atᵉ
theᵉ modalᵉ unitᵉ forᵉ everyᵉ `A`.ᵉ Henceᵉ theᵉ modalᵉ typesᵉ with respectᵉ to `○`ᵉ areᵉ
preciselyᵉ theᵉ typesᵉ in theᵉ reflectiveᵉ subuniverse.ᵉ

## Definitions

### The predicate on subuniverses of being reflective

```agda
is-reflective-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
is-reflective-subuniverseᵉ {l1ᵉ} Pᵉ =
  Σᵉ ( operator-modalityᵉ l1ᵉ l1ᵉ)
    ( λ ○ᵉ →
      Σᵉ ( unit-modalityᵉ ○ᵉ)
        ( λ unit-○ᵉ →
          ( (Xᵉ : UUᵉ l1ᵉ) → is-in-subuniverseᵉ Pᵉ (○ᵉ Xᵉ)) ×ᵉ
          ( (Xᵉ Yᵉ : UUᵉ l1ᵉ) → is-in-subuniverseᵉ Pᵉ Xᵉ → is-localᵉ (unit-○ᵉ {Yᵉ}) Xᵉ)))
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (is-reflective-Pᵉ : is-reflective-subuniverseᵉ Pᵉ)
  where

  operator-is-reflective-subuniverseᵉ : operator-modalityᵉ l1ᵉ l1ᵉ
  operator-is-reflective-subuniverseᵉ = pr1ᵉ is-reflective-Pᵉ

  unit-is-reflective-subuniverseᵉ :
    unit-modalityᵉ (operator-is-reflective-subuniverseᵉ)
  unit-is-reflective-subuniverseᵉ = pr1ᵉ (pr2ᵉ is-reflective-Pᵉ)

  is-in-subuniverse-operator-type-is-reflective-subuniverseᵉ :
    (Xᵉ : UUᵉ l1ᵉ) →
    is-in-subuniverseᵉ Pᵉ (operator-is-reflective-subuniverseᵉ Xᵉ)
  is-in-subuniverse-operator-type-is-reflective-subuniverseᵉ =
    pr1ᵉ (pr2ᵉ (pr2ᵉ is-reflective-Pᵉ))

  is-local-is-in-subuniverse-is-reflective-subuniverseᵉ :
    (Xᵉ Yᵉ : UUᵉ l1ᵉ) →
    is-in-subuniverseᵉ Pᵉ Xᵉ →
    is-localᵉ (unit-is-reflective-subuniverseᵉ {Yᵉ}) Xᵉ
  is-local-is-in-subuniverse-is-reflective-subuniverseᵉ =
    pr2ᵉ (pr2ᵉ (pr2ᵉ is-reflective-Pᵉ))
```

### The type of reflective subuniverses

```agda
reflective-subuniverseᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
reflective-subuniverseᵉ l1ᵉ l2ᵉ =
  Σᵉ (subuniverseᵉ l1ᵉ l2ᵉ) (is-reflective-subuniverseᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : reflective-subuniverseᵉ l1ᵉ l2ᵉ)
  where

  subuniverse-reflective-subuniverseᵉ : subuniverseᵉ l1ᵉ l2ᵉ
  subuniverse-reflective-subuniverseᵉ = pr1ᵉ Pᵉ

  is-in-reflective-subuniverseᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ
  is-in-reflective-subuniverseᵉ =
    is-in-subuniverseᵉ subuniverse-reflective-subuniverseᵉ

  inclusion-reflective-subuniverseᵉ :
    type-subuniverseᵉ (subuniverse-reflective-subuniverseᵉ) → UUᵉ l1ᵉ
  inclusion-reflective-subuniverseᵉ =
    inclusion-subuniverseᵉ subuniverse-reflective-subuniverseᵉ

  is-reflective-subuniverse-reflective-subuniverseᵉ :
    is-reflective-subuniverseᵉ (subuniverse-reflective-subuniverseᵉ)
  is-reflective-subuniverse-reflective-subuniverseᵉ = pr2ᵉ Pᵉ

  operator-reflective-subuniverseᵉ : operator-modalityᵉ l1ᵉ l1ᵉ
  operator-reflective-subuniverseᵉ =
    operator-is-reflective-subuniverseᵉ
      ( subuniverse-reflective-subuniverseᵉ)
      ( is-reflective-subuniverse-reflective-subuniverseᵉ)

  unit-reflective-subuniverseᵉ :
    unit-modalityᵉ (operator-reflective-subuniverseᵉ)
  unit-reflective-subuniverseᵉ =
    unit-is-reflective-subuniverseᵉ
      ( subuniverse-reflective-subuniverseᵉ)
      ( is-reflective-subuniverse-reflective-subuniverseᵉ)

  is-in-subuniverse-operator-type-reflective-subuniverseᵉ :
    ( Xᵉ : UUᵉ l1ᵉ) →
    is-in-subuniverseᵉ
      ( subuniverse-reflective-subuniverseᵉ)
      ( operator-reflective-subuniverseᵉ Xᵉ)
  is-in-subuniverse-operator-type-reflective-subuniverseᵉ =
    is-in-subuniverse-operator-type-is-reflective-subuniverseᵉ
      ( subuniverse-reflective-subuniverseᵉ)
      ( is-reflective-subuniverse-reflective-subuniverseᵉ)

  is-local-is-in-subuniverse-reflective-subuniverseᵉ :
    ( Xᵉ Yᵉ : UUᵉ l1ᵉ) →
    is-in-subuniverseᵉ subuniverse-reflective-subuniverseᵉ Xᵉ →
    is-localᵉ (unit-reflective-subuniverseᵉ {Yᵉ}) Xᵉ
  is-local-is-in-subuniverse-reflective-subuniverseᵉ =
    is-local-is-in-subuniverse-is-reflective-subuniverseᵉ
      ( subuniverse-reflective-subuniverseᵉ)
      ( is-reflective-subuniverse-reflective-subuniverseᵉ)
```

## Properties

### Reflective subuniverses are subuniverses that have all localizations

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (is-reflective-Pᵉ : is-reflective-subuniverseᵉ Pᵉ)
  where

  has-all-localizations-is-reflective-subuniverseᵉ :
    (Aᵉ : UUᵉ l1ᵉ) → subuniverse-localizationᵉ Pᵉ Aᵉ
  pr1ᵉ (has-all-localizations-is-reflective-subuniverseᵉ Aᵉ) =
    operator-is-reflective-subuniverseᵉ Pᵉ is-reflective-Pᵉ Aᵉ
  pr1ᵉ (pr2ᵉ (has-all-localizations-is-reflective-subuniverseᵉ Aᵉ)) =
    is-in-subuniverse-operator-type-is-reflective-subuniverseᵉ
      Pᵉ is-reflective-Pᵉ Aᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (has-all-localizations-is-reflective-subuniverseᵉ Aᵉ))) =
    unit-is-reflective-subuniverseᵉ Pᵉ is-reflective-Pᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (has-all-localizations-is-reflective-subuniverseᵉ Aᵉ)))
    Xᵉ is-in-subuniverse-Xᵉ =
      is-local-is-in-subuniverse-is-reflective-subuniverseᵉ
        Pᵉ is-reflective-Pᵉ Xᵉ Aᵉ is-in-subuniverse-Xᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Lᵉ : (Aᵉ : UUᵉ l1ᵉ) → subuniverse-localizationᵉ Pᵉ Aᵉ)
  where

  is-reflective-has-all-localizations-subuniverseᵉ :
    is-reflective-subuniverseᵉ Pᵉ
  pr1ᵉ is-reflective-has-all-localizations-subuniverseᵉ Aᵉ =
    type-subuniverse-localizationᵉ Pᵉ (Lᵉ Aᵉ)
  pr1ᵉ (pr2ᵉ is-reflective-has-all-localizations-subuniverseᵉ) {Aᵉ} =
    unit-subuniverse-localizationᵉ Pᵉ (Lᵉ Aᵉ)
  pr1ᵉ (pr2ᵉ (pr2ᵉ is-reflective-has-all-localizations-subuniverseᵉ)) Aᵉ =
    is-in-subuniverse-subuniverse-localizationᵉ Pᵉ (Lᵉ Aᵉ)
  pr2ᵉ (pr2ᵉ (pr2ᵉ is-reflective-has-all-localizations-subuniverseᵉ))
    Aᵉ Bᵉ is-in-subuniverse-Aᵉ =
    is-local-at-unit-is-in-subuniverse-subuniverse-localizationᵉ
      Pᵉ (Lᵉ Bᵉ) Aᵉ is-in-subuniverse-Aᵉ
```

## Recursion for reflective subuniverses

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (is-reflective-Pᵉ : is-reflective-subuniverseᵉ Pᵉ)
  where

  rec-modality-is-reflective-subuniverseᵉ :
    rec-modalityᵉ (unit-is-reflective-subuniverseᵉ Pᵉ is-reflective-Pᵉ)
  rec-modality-is-reflective-subuniverseᵉ {Xᵉ} {Yᵉ} =
    map-inv-is-equivᵉ
      ( is-local-is-in-subuniverse-is-reflective-subuniverseᵉ
        ( Pᵉ)
        ( is-reflective-Pᵉ)
        ( operator-is-reflective-subuniverseᵉ Pᵉ is-reflective-Pᵉ Yᵉ)
        ( Xᵉ)
        ( is-in-subuniverse-operator-type-is-reflective-subuniverseᵉ
          ( Pᵉ)
          ( is-reflective-Pᵉ)
          ( Yᵉ)))

  map-is-reflective-subuniverseᵉ :
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} → (Xᵉ → Yᵉ) →
    operator-is-reflective-subuniverseᵉ Pᵉ is-reflective-Pᵉ Xᵉ →
    operator-is-reflective-subuniverseᵉ Pᵉ is-reflective-Pᵉ Yᵉ
  map-is-reflective-subuniverseᵉ =
    ap-map-rec-modalityᵉ
      ( unit-is-reflective-subuniverseᵉ Pᵉ is-reflective-Pᵉ)
      ( rec-modality-is-reflective-subuniverseᵉ)

  strong-rec-subuniverse-is-reflective-subuniverseᵉ :
    strong-rec-subuniverse-modalityᵉ
      ( unit-is-reflective-subuniverseᵉ Pᵉ is-reflective-Pᵉ)
  strong-rec-subuniverse-is-reflective-subuniverseᵉ =
    strong-rec-subuniverse-rec-modalityᵉ
      ( unit-is-reflective-subuniverseᵉ Pᵉ is-reflective-Pᵉ)
      ( rec-modality-is-reflective-subuniverseᵉ)

  rec-subuniverse-is-reflective-subuniverseᵉ :
    rec-subuniverse-modalityᵉ (unit-is-reflective-subuniverseᵉ Pᵉ is-reflective-Pᵉ)
  rec-subuniverse-is-reflective-subuniverseᵉ =
    rec-subuniverse-rec-modalityᵉ
      ( unit-is-reflective-subuniverseᵉ Pᵉ is-reflective-Pᵉ)
      ( rec-modality-is-reflective-subuniverseᵉ)
```

## See also

-ᵉ [Σ-closedᵉ reflectiveᵉ subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.mdᵉ)
-ᵉ [Localizationsᵉ with respectᵉ to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.mdᵉ)

## References

{{#bibliographyᵉ}} {{#referenceᵉ UF13ᵉ}} {{#referenceᵉ RSS20ᵉ}} {{#referenceᵉ Rij19ᵉ}}