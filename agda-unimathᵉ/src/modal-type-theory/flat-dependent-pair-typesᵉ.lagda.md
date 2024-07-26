# Flat dependent pair types

```agda
{-# OPTIONSᵉ --cohesionᵉ --flat-splitᵉ #-}

module modal-type-theory.flat-dependent-pair-typesᵉ where
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

open import modal-type-theory.flat-modalityᵉ
```

</details>

## Idea

Weᵉ studyᵉ interactionsᵉ betweenᵉ theᵉ
[flatᵉ modality](modal-type-theory.flat-modality.mdᵉ) andᵉ
[dependentᵉ pairᵉ types](foundation.dependent-pair-types.md).ᵉ

## Definitions

```agda
Σ-♭ᵉ : {@♭ᵉ l1ᵉ l2ᵉ : Level} (@♭ᵉ Aᵉ : UUᵉ l1ᵉ) (@♭ᵉ Bᵉ : Aᵉ → UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
Σ-♭ᵉ Aᵉ Bᵉ = Σᵉ (♭ᵉ Aᵉ) (λ where (cons-flatᵉ xᵉ) → ♭ᵉ (Bᵉ xᵉ))
```

## Properties

### Flat distributes over Σ-types

```agda
module _
  {@♭ᵉ l1ᵉ l2ᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ l1ᵉ} {@♭ᵉ Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  map-distributive-flat-Σᵉ : ♭ᵉ (Σᵉ Aᵉ Bᵉ) → Σ-♭ᵉ Aᵉ Bᵉ
  pr1ᵉ (map-distributive-flat-Σᵉ (cons-flatᵉ (xᵉ ,ᵉ yᵉ))) = cons-flatᵉ xᵉ
  pr2ᵉ (map-distributive-flat-Σᵉ (cons-flatᵉ (xᵉ ,ᵉ yᵉ))) = cons-flatᵉ yᵉ

  map-inv-distributive-flat-Σᵉ : Σ-♭ᵉ Aᵉ Bᵉ → ♭ᵉ (Σᵉ Aᵉ Bᵉ)
  map-inv-distributive-flat-Σᵉ (cons-flatᵉ xᵉ ,ᵉ cons-flatᵉ yᵉ) = cons-flatᵉ (xᵉ ,ᵉ yᵉ)

  is-section-distributive-flat-Σᵉ :
    (map-inv-distributive-flat-Σᵉ ∘ᵉ map-distributive-flat-Σᵉ) ~ᵉ idᵉ
  is-section-distributive-flat-Σᵉ (cons-flatᵉ _) = reflᵉ

  is-retraction-distributive-flat-Σᵉ :
    (map-distributive-flat-Σᵉ ∘ᵉ map-inv-distributive-flat-Σᵉ) ~ᵉ idᵉ
  is-retraction-distributive-flat-Σᵉ (cons-flatᵉ _ ,ᵉ cons-flatᵉ _) = reflᵉ

  section-distributive-flat-Σᵉ : sectionᵉ map-distributive-flat-Σᵉ
  pr1ᵉ section-distributive-flat-Σᵉ = map-inv-distributive-flat-Σᵉ
  pr2ᵉ section-distributive-flat-Σᵉ = is-retraction-distributive-flat-Σᵉ

  retraction-distributive-flat-Σᵉ : retractionᵉ map-distributive-flat-Σᵉ
  pr1ᵉ retraction-distributive-flat-Σᵉ = map-inv-distributive-flat-Σᵉ
  pr2ᵉ retraction-distributive-flat-Σᵉ = is-section-distributive-flat-Σᵉ

  is-equiv-distributive-flat-Σᵉ : is-equivᵉ map-distributive-flat-Σᵉ
  pr1ᵉ is-equiv-distributive-flat-Σᵉ = section-distributive-flat-Σᵉ
  pr2ᵉ is-equiv-distributive-flat-Σᵉ = retraction-distributive-flat-Σᵉ

  equiv-distributive-flat-Σᵉ : ♭ᵉ (Σᵉ Aᵉ Bᵉ) ≃ᵉ Σ-♭ᵉ Aᵉ Bᵉ
  pr1ᵉ equiv-distributive-flat-Σᵉ = map-distributive-flat-Σᵉ
  pr2ᵉ equiv-distributive-flat-Σᵉ = is-equiv-distributive-flat-Σᵉ

  inv-equiv-distributive-flat-Σᵉ : Σ-♭ᵉ Aᵉ Bᵉ ≃ᵉ ♭ᵉ (Σᵉ Aᵉ Bᵉ)
  inv-equiv-distributive-flat-Σᵉ = inv-equivᵉ equiv-distributive-flat-Σᵉ
```

## See also

-ᵉ [Flatᵉ discreteᵉ types](modal-type-theory.flat-discrete-types.mdᵉ) forᵉ typesᵉ thatᵉ
  areᵉ flatᵉ modal.ᵉ

## References

{{#bibliographyᵉ}} {{#referenceᵉ Shu18ᵉ}} {{#referenceᵉ Dlicata335/Cohesion-Agdaᵉ}}