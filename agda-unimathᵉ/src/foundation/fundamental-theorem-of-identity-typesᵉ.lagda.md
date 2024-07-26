# The fundamental theorem of identity types

```agda
module foundation.fundamental-theorem-of-identity-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.families-of-equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.retracts-of-typesᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Theᵉ _fundamentalᵉ theoremᵉ ofᵉ identityᵉ typesᵉ_ providesᵉ aᵉ wayᵉ to characterizeᵉ
[identityᵉ types](foundation-core.identity-types.md).ᵉ Itᵉ usesᵉ theᵉ factᵉ thatᵉ aᵉ
familyᵉ ofᵉ mapsᵉ `fᵉ : (xᵉ : Aᵉ) → aᵉ ＝ᵉ xᵉ → Bᵉ x`ᵉ isᵉ aᵉ familyᵉ ofᵉ
[equivalences](foundation-core.equivalences.mdᵉ) ifᵉ andᵉ onlyᵉ ifᵉ itᵉ inducesᵉ anᵉ
equivalenceᵉ `Σᵉ Aᵉ (Idᵉ aᵉ) → Σᵉ Aᵉ B`ᵉ onᵉ
[totalᵉ spaces](foundation.dependent-pair-types.md).ᵉ Noteᵉ thatᵉ theᵉ totalᵉ spaceᵉ
`Σᵉ Aᵉ (Idᵉ a)`ᵉ isᵉ [contractible](foundation-core.contractible-types.md).ᵉ
Therefore,ᵉ anyᵉ mapᵉ `Σᵉ Aᵉ (Idᵉ aᵉ) → Σᵉ Aᵉ B`ᵉ isᵉ anᵉ equivalenceᵉ ifᵉ andᵉ onlyᵉ ifᵉ `Σᵉ Aᵉ B`ᵉ
isᵉ contractible.ᵉ Typeᵉ familiesᵉ `B`ᵉ ofᵉ whichᵉ theᵉ totalᵉ spaceᵉ `Σᵉ Aᵉ B`ᵉ isᵉ
contractibleᵉ areᵉ alsoᵉ calledᵉ
[torsorial](foundation-core.torsorial-type-families.md).ᵉ Theᵉ statementᵉ ofᵉ theᵉ
fundamentalᵉ theoremᵉ ofᵉ identityᵉ typesᵉ isᵉ thereforeᵉ:

**Fundamentalᵉ theoremᵉ ofᵉ identityᵉ types.**ᵉ Considerᵉ aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ aᵉ
typeᵉ `A`,ᵉ andᵉ considerᵉ anᵉ elementᵉ `aᵉ : A`.ᵉ Thenᵉ theᵉ followingᵉ areᵉ
[logicallyᵉ equivalent](foundation.logical-equivalences.mdᵉ):

1.ᵉ Anyᵉ familyᵉ ofᵉ mapsᵉ `fᵉ : (xᵉ : Aᵉ) → aᵉ ＝ᵉ xᵉ → Bᵉ x`ᵉ isᵉ aᵉ familyᵉ ofᵉ equivalences.ᵉ
2.ᵉ Theᵉ typeᵉ familyᵉ `B`ᵉ isᵉ torsorial.ᵉ

## Theorem

### The fundamental theorem of identity types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {aᵉ : Aᵉ}
  where

  abstract
    fundamental-theorem-idᵉ :
      is-torsorialᵉ Bᵉ → (fᵉ : (xᵉ : Aᵉ) → aᵉ ＝ᵉ xᵉ → Bᵉ xᵉ) → is-fiberwise-equivᵉ fᵉ
    fundamental-theorem-idᵉ is-contr-ABᵉ fᵉ =
      is-fiberwise-equiv-is-equiv-totᵉ
        ( is-equiv-is-contrᵉ (totᵉ fᵉ) (is-torsorial-Idᵉ aᵉ) is-contr-ABᵉ)

  abstract
    fundamental-theorem-id'ᵉ :
      (fᵉ : (xᵉ : Aᵉ) → aᵉ ＝ᵉ xᵉ → Bᵉ xᵉ) → is-fiberwise-equivᵉ fᵉ → is-torsorialᵉ Bᵉ
    fundamental-theorem-id'ᵉ fᵉ is-fiberwise-equiv-fᵉ =
      is-contr-is-equiv'ᵉ
        ( Σᵉ Aᵉ (Idᵉ aᵉ))
        ( totᵉ fᵉ)
        ( is-equiv-tot-is-fiberwise-equivᵉ is-fiberwise-equiv-fᵉ)
        ( is-torsorial-Idᵉ aᵉ)
```

## Corollaries

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (aᵉ : Aᵉ) (bᵉ : Bᵉ aᵉ)
  where

  abstract
    fundamental-theorem-id-Jᵉ :
      is-torsorialᵉ Bᵉ → is-fiberwise-equivᵉ (ind-Idᵉ aᵉ (λ xᵉ pᵉ → Bᵉ xᵉ) bᵉ)
    fundamental-theorem-id-Jᵉ is-contr-ABᵉ =
      fundamental-theorem-idᵉ is-contr-ABᵉ (ind-Idᵉ aᵉ (λ xᵉ pᵉ → Bᵉ xᵉ) bᵉ)

  abstract
    fundamental-theorem-id-J'ᵉ :
      is-fiberwise-equivᵉ (ind-Idᵉ aᵉ (λ xᵉ pᵉ → Bᵉ xᵉ) bᵉ) → is-torsorialᵉ Bᵉ
    fundamental-theorem-id-J'ᵉ Hᵉ =
      is-contr-is-equiv'ᵉ
        ( Σᵉ Aᵉ (Idᵉ aᵉ))
        ( totᵉ (ind-Idᵉ aᵉ (λ xᵉ pᵉ → Bᵉ xᵉ) bᵉ))
        ( is-equiv-tot-is-fiberwise-equivᵉ Hᵉ)
        ( is-torsorial-Idᵉ aᵉ)
```

### Retracts of the identity type are equivalent to the identity type

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (aᵉ : Aᵉ)
  where

  abstract
    fundamental-theorem-id-retractionᵉ :
      (iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → aᵉ ＝ᵉ xᵉ) →
      ((xᵉ : Aᵉ) → retractionᵉ (iᵉ xᵉ)) →
      is-fiberwise-equivᵉ iᵉ
    fundamental-theorem-id-retractionᵉ iᵉ Rᵉ =
      is-fiberwise-equiv-is-equiv-totᵉ
        ( is-equiv-is-contrᵉ (totᵉ iᵉ)
          ( is-contr-retract-ofᵉ
            ( Σᵉ _ (λ yᵉ → aᵉ ＝ᵉ yᵉ))
            ( ( totᵉ iᵉ) ,ᵉ
              ( totᵉ (λ xᵉ → pr1ᵉ (Rᵉ xᵉ))) ,ᵉ
              ( ( inv-htpyᵉ (preserves-comp-totᵉ iᵉ (pr1ᵉ ∘ᵉ Rᵉ))) ∙hᵉ
                ( tot-htpyᵉ (pr2ᵉ ∘ᵉ Rᵉ)) ∙hᵉ
                ( tot-idᵉ Bᵉ)))
            ( is-torsorial-Idᵉ aᵉ))
          ( is-torsorial-Idᵉ aᵉ))

    fundamental-theorem-id-retractᵉ :
      (Rᵉ : (xᵉ : Aᵉ) → (Bᵉ xᵉ) retract-ofᵉ (aᵉ ＝ᵉ xᵉ)) →
      is-fiberwise-equivᵉ (inclusion-retractᵉ ∘ᵉ Rᵉ)
    fundamental-theorem-id-retractᵉ Rᵉ =
      fundamental-theorem-id-retractionᵉ
        ( inclusion-retractᵉ ∘ᵉ Rᵉ)
        ( retraction-retractᵉ ∘ᵉ Rᵉ)
```

### The fundamental theorem of identity types, using sections

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (aᵉ : Aᵉ)
  where

  abstract
    fundamental-theorem-id-sectionᵉ :
      (fᵉ : (xᵉ : Aᵉ) → aᵉ ＝ᵉ xᵉ → Bᵉ xᵉ) →
      ((xᵉ : Aᵉ) → sectionᵉ (fᵉ xᵉ)) →
      is-fiberwise-equivᵉ fᵉ
    fundamental-theorem-id-sectionᵉ fᵉ section-fᵉ xᵉ =
      is-equiv-is-equiv-sectionᵉ
        ( fᵉ xᵉ)
        ( section-fᵉ xᵉ)
        ( fundamental-theorem-id-retractionᵉ
          ( aᵉ)
          ( λ xᵉ → map-sectionᵉ (fᵉ xᵉ) (section-fᵉ xᵉ))
          ( λ xᵉ → (fᵉ xᵉ ,ᵉ is-section-map-sectionᵉ (fᵉ xᵉ) (section-fᵉ xᵉ)))
          ( xᵉ))
```

## See also

-ᵉ Anᵉ extensionᵉ ofᵉ theᵉ fundamentalᵉ theoremᵉ ofᵉ identityᵉ typesᵉ isᵉ formalizedᵉ in
  [`foundation.regensburg-extension-fundamental-theorem-of-identity-types`](foundation.regensburg-extension-fundamental-theorem-of-identity-types.md).ᵉ