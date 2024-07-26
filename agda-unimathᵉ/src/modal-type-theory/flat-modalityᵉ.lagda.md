# The flat modality

```agda
{-# OPTIONSᵉ --cohesionᵉ --flat-splitᵉ #-}

module modal-type-theory.flat-modalityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **flatᵉ modality**ᵉ isᵉ anᵉ axiomatizedᵉ comonadicᵉ modalityᵉ weᵉ adjoinᵉ to ourᵉ typeᵉ
theoryᵉ byᵉ useᵉ ofᵉ _crispᵉ typeᵉ theory_.ᵉ

## Definition

### The flat operator on types

```agda
data ♭ᵉ {@♭ᵉ lᵉ : Level} (@♭ᵉ Aᵉ : UUᵉ lᵉ) : UUᵉ lᵉ where
  cons-flatᵉ : @♭ᵉ Aᵉ → ♭ᵉ Aᵉ
```

### The flat counit

```agda
counit-crispᵉ : {@♭ᵉ lᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ lᵉ} → @♭ᵉ Aᵉ → Aᵉ
counit-crispᵉ xᵉ = xᵉ

counit-flatᵉ : {@♭ᵉ lᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ lᵉ} → ♭ᵉ Aᵉ → Aᵉ
counit-flatᵉ (cons-flatᵉ xᵉ) = counit-crispᵉ xᵉ
```

### Flat dependent elimination

```agda
ind-flatᵉ :
  {@♭ᵉ l1ᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ l1ᵉ} {l2ᵉ : Level} (Cᵉ : ♭ᵉ Aᵉ → UUᵉ l2ᵉ) →
  ((@♭ᵉ uᵉ : Aᵉ) → Cᵉ (cons-flatᵉ uᵉ)) →
  (xᵉ : ♭ᵉ Aᵉ) → Cᵉ xᵉ
ind-flatᵉ Cᵉ fᵉ (cons-flatᵉ xᵉ) = fᵉ xᵉ

crisp-ind-flatᵉ :
  {@♭ᵉ l1ᵉ : Level} {l2ᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ l1ᵉ} (Cᵉ : @♭ᵉ ♭ᵉ Aᵉ → UUᵉ l2ᵉ) →
  ((@♭ᵉ uᵉ : Aᵉ) → Cᵉ (cons-flatᵉ uᵉ)) → (@♭ᵉ xᵉ : ♭ᵉ Aᵉ) → Cᵉ xᵉ
crisp-ind-flatᵉ Cᵉ fᵉ (cons-flatᵉ xᵉ) = fᵉ xᵉ
```

### Flat elimination

```agda
rec-flatᵉ :
  {@♭ᵉ l1ᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ l1ᵉ} {l2ᵉ : Level} (Cᵉ : UUᵉ l2ᵉ) →
  ((@♭ᵉ uᵉ : Aᵉ) → Cᵉ) → (xᵉ : ♭ᵉ Aᵉ) → Cᵉ
rec-flatᵉ Cᵉ = ind-flatᵉ (λ _ → Cᵉ)

crisp-rec-flatᵉ :
  {@♭ᵉ l1ᵉ : Level} {l2ᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ l1ᵉ} (Cᵉ : UUᵉ l2ᵉ) →
  ((@♭ᵉ uᵉ : Aᵉ) → Cᵉ) → (@♭ᵉ xᵉ : ♭ᵉ Aᵉ) → Cᵉ
crisp-rec-flatᵉ Cᵉ = crisp-ind-flatᵉ (λ _ → Cᵉ)
```

### Flat action on maps

```agda
module _
  {@♭ᵉ l1ᵉ l2ᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ l1ᵉ} {@♭ᵉ Bᵉ : UUᵉ l2ᵉ}
  where

  ap-flatᵉ : @♭ᵉ (Aᵉ → Bᵉ) → (♭ᵉ Aᵉ → ♭ᵉ Bᵉ)
  ap-flatᵉ fᵉ (cons-flatᵉ xᵉ) = cons-flatᵉ (fᵉ xᵉ)

  ap-crisp-flatᵉ : @♭ᵉ (@♭ᵉ Aᵉ → Bᵉ) → (♭ᵉ Aᵉ → ♭ᵉ Bᵉ)
  ap-crisp-flatᵉ fᵉ (cons-flatᵉ xᵉ) = cons-flatᵉ (fᵉ xᵉ)

  coap-flatᵉ : (♭ᵉ Aᵉ → ♭ᵉ Bᵉ) → (@♭ᵉ Aᵉ → Bᵉ)
  coap-flatᵉ fᵉ xᵉ = counit-flatᵉ (fᵉ (cons-flatᵉ xᵉ))

  is-crisp-retraction-coap-flatᵉ :
    (@♭ᵉ fᵉ : @♭ᵉ Aᵉ → Bᵉ) → coap-flatᵉ (ap-crisp-flatᵉ fᵉ) ＝ᵉ fᵉ
  is-crisp-retraction-coap-flatᵉ _ = reflᵉ
```

## Properties

### Crisp assumptions are weaker

```agda
crispenᵉ :
  {@♭ᵉ l1ᵉ l2ᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ l1ᵉ} {Pᵉ : Aᵉ → UUᵉ l2ᵉ} →
  ((xᵉ : Aᵉ) → Pᵉ xᵉ) → ((@♭ᵉ xᵉ : Aᵉ) → Pᵉ xᵉ)
crispenᵉ fᵉ xᵉ = fᵉ xᵉ
```

### The flat modality is idempotent

```agda
module _
  {@♭ᵉ lᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ lᵉ}
  where

  is-crisp-section-cons-flatᵉ : (@♭ᵉ xᵉ : Aᵉ) → counit-flatᵉ (cons-flatᵉ xᵉ) ＝ᵉ xᵉ
  is-crisp-section-cons-flatᵉ _ = reflᵉ

  is-crisp-retraction-cons-flatᵉ : (@♭ᵉ xᵉ : ♭ᵉ Aᵉ) → cons-flatᵉ (counit-flatᵉ xᵉ) ＝ᵉ xᵉ
  is-crisp-retraction-cons-flatᵉ (cons-flatᵉ _) = reflᵉ
```

```agda
module _
  {@♭ᵉ lᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ lᵉ}
  where

  map-flat-counit-flatᵉ : ♭ᵉ (♭ᵉ Aᵉ) → ♭ᵉ Aᵉ
  map-flat-counit-flatᵉ (cons-flatᵉ xᵉ) = xᵉ

  diagonal-flatᵉ : ♭ᵉ Aᵉ → ♭ᵉ (♭ᵉ Aᵉ)
  diagonal-flatᵉ (cons-flatᵉ xᵉ) = cons-flatᵉ (cons-flatᵉ xᵉ)

  is-section-flat-counit-flatᵉ :
    diagonal-flatᵉ ∘ᵉ map-flat-counit-flatᵉ ~ᵉ idᵉ
  is-section-flat-counit-flatᵉ (cons-flatᵉ (cons-flatᵉ _)) = reflᵉ

  is-retraction-flat-counit-flatᵉ :
    map-flat-counit-flatᵉ ∘ᵉ diagonal-flatᵉ ~ᵉ idᵉ
  is-retraction-flat-counit-flatᵉ (cons-flatᵉ _) = reflᵉ

  section-flat-counit-flatᵉ : sectionᵉ map-flat-counit-flatᵉ
  pr1ᵉ section-flat-counit-flatᵉ = diagonal-flatᵉ
  pr2ᵉ section-flat-counit-flatᵉ = is-retraction-flat-counit-flatᵉ

  retraction-flat-counit-flatᵉ : retractionᵉ map-flat-counit-flatᵉ
  pr1ᵉ retraction-flat-counit-flatᵉ = diagonal-flatᵉ
  pr2ᵉ retraction-flat-counit-flatᵉ = is-section-flat-counit-flatᵉ

  is-equiv-flat-counit-flatᵉ : is-equivᵉ map-flat-counit-flatᵉ
  pr1ᵉ is-equiv-flat-counit-flatᵉ = section-flat-counit-flatᵉ
  pr2ᵉ is-equiv-flat-counit-flatᵉ = retraction-flat-counit-flatᵉ

  equiv-flat-counit-flatᵉ : ♭ᵉ (♭ᵉ Aᵉ) ≃ᵉ ♭ᵉ Aᵉ
  pr1ᵉ equiv-flat-counit-flatᵉ = map-flat-counit-flatᵉ
  pr2ᵉ equiv-flat-counit-flatᵉ = is-equiv-flat-counit-flatᵉ

  inv-equiv-flat-counit-flatᵉ : ♭ᵉ Aᵉ ≃ᵉ ♭ᵉ (♭ᵉ Aᵉ)
  inv-equiv-flat-counit-flatᵉ = inv-equivᵉ equiv-flat-counit-flatᵉ
```

## See also

-ᵉ Inᵉ [theᵉ flat-sharpᵉ adjunction](modal-type-theory.flat-sharp-adjunction.mdᵉ) weᵉ
  postulate thatᵉ theᵉ flatᵉ modalityᵉ isᵉ leftᵉ adjointᵉ to theᵉ
  [sharpᵉ modality](modal-type-theory.sharp-modality.md).ᵉ
-ᵉ [Flatᵉ discreteᵉ types](modal-type-theory.flat-discrete-types.mdᵉ) forᵉ typesᵉ thatᵉ
  areᵉ flatᵉ modal.ᵉ

## References

{{#bibliographyᵉ}} {{#referenceᵉ Shu18ᵉ}} {{#referenceᵉ Dlicata335/Cohesion-Agdaᵉ}}