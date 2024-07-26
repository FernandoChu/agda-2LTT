# Localizations of rings

```agda
module ring-theory.localizations-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.homomorphisms-ringsᵉ
open import ring-theory.invertible-elements-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.subsets-ringsᵉ
```

</details>

## Localization at a specific element

Weᵉ introduceᵉ homomorphismsᵉ thatᵉ invertᵉ specificᵉ elements.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (R1ᵉ : Ringᵉ l1ᵉ) (R2ᵉ : Ringᵉ l2ᵉ) (xᵉ : type-Ringᵉ R1ᵉ)
  (fᵉ : hom-Ringᵉ R1ᵉ R2ᵉ)
  where

  inverts-element-hom-Ringᵉ : UUᵉ l2ᵉ
  inverts-element-hom-Ringᵉ =
    is-invertible-element-Ringᵉ R2ᵉ (map-hom-Ringᵉ R1ᵉ R2ᵉ fᵉ xᵉ)

  is-prop-inverts-element-hom-Ringᵉ : is-propᵉ inverts-element-hom-Ringᵉ
  is-prop-inverts-element-hom-Ringᵉ =
    is-prop-is-invertible-element-Ringᵉ R2ᵉ (map-hom-Ringᵉ R1ᵉ R2ᵉ fᵉ xᵉ)

  inverts-element-hom-ring-Propᵉ : Propᵉ l2ᵉ
  pr1ᵉ inverts-element-hom-ring-Propᵉ = inverts-element-hom-Ringᵉ
  pr2ᵉ inverts-element-hom-ring-Propᵉ = is-prop-inverts-element-hom-Ringᵉ

inv-inverts-element-hom-Ringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (xᵉ : type-Ringᵉ Rᵉ)
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) → inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ → type-Ringᵉ Sᵉ
inv-inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ Hᵉ = pr1ᵉ Hᵉ

is-left-inverse-inv-inverts-element-hom-Ringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (xᵉ : type-Ringᵉ Rᵉ)
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) (Hᵉ : inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ) →
  Idᵉ
    ( mul-Ringᵉ Sᵉ
      ( inv-inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ Hᵉ)
      ( map-hom-Ringᵉ Rᵉ Sᵉ fᵉ xᵉ))
    ( one-Ringᵉ Sᵉ)
is-left-inverse-inv-inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ Hᵉ = pr2ᵉ (pr2ᵉ Hᵉ)

is-right-inverse-inv-inverts-element-hom-Ringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (xᵉ : type-Ringᵉ Rᵉ)
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) (Hᵉ : inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ) →
  Idᵉ
    ( mul-Ringᵉ Sᵉ
      ( map-hom-Ringᵉ Rᵉ Sᵉ fᵉ xᵉ)
      ( inv-inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ Hᵉ))
    ( one-Ringᵉ Sᵉ)
is-right-inverse-inv-inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ Hᵉ = pr1ᵉ (pr2ᵉ Hᵉ)
```

```agda
inverts-element-comp-hom-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Tᵉ : Ringᵉ l3ᵉ)
  (xᵉ : type-Ringᵉ Rᵉ) (gᵉ : hom-Ringᵉ Sᵉ Tᵉ) (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) →
  inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ →
  inverts-element-hom-Ringᵉ Rᵉ Tᵉ xᵉ (comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ gᵉ fᵉ)
inverts-element-comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ xᵉ gᵉ fᵉ Hᵉ =
  pairᵉ
    ( map-hom-Ringᵉ Sᵉ Tᵉ gᵉ (inv-inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ Hᵉ))
    ( pairᵉ
      ( ( invᵉ (preserves-mul-hom-Ringᵉ Sᵉ Tᵉ gᵉ)) ∙ᵉ
        ( ( apᵉ
            ( map-hom-Ringᵉ Sᵉ Tᵉ gᵉ)
            ( is-right-inverse-inv-inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ Hᵉ)) ∙ᵉ
          ( preserves-one-hom-Ringᵉ Sᵉ Tᵉ gᵉ)))
      ( ( invᵉ (preserves-mul-hom-Ringᵉ Sᵉ Tᵉ gᵉ)) ∙ᵉ
        ( ( apᵉ
            ( map-hom-Ringᵉ Sᵉ Tᵉ gᵉ)
            ( is-left-inverse-inv-inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ Hᵉ)) ∙ᵉ
          ( preserves-one-hom-Ringᵉ Sᵉ Tᵉ gᵉ))))
```

### The universal property of the localization of a ring at a single element

```agda
precomp-universal-property-localization-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Tᵉ : Ringᵉ l3ᵉ) (xᵉ : type-Ringᵉ Rᵉ)
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) (Hᵉ : inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ) →
  hom-Ringᵉ Sᵉ Tᵉ → Σᵉ (hom-Ringᵉ Rᵉ Tᵉ) (inverts-element-hom-Ringᵉ Rᵉ Tᵉ xᵉ)
pr1ᵉ (precomp-universal-property-localization-Ringᵉ Rᵉ Sᵉ Tᵉ xᵉ fᵉ Hᵉ gᵉ) =
  comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ gᵉ fᵉ
pr2ᵉ (precomp-universal-property-localization-Ringᵉ Rᵉ Sᵉ Tᵉ xᵉ fᵉ Hᵉ gᵉ) =
  inverts-element-comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ xᵉ gᵉ fᵉ Hᵉ

universal-property-localization-Ringᵉ :
  (lᵉ : Level) {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (xᵉ : type-Ringᵉ Rᵉ)
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) → inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ →
  UUᵉ (lsuc lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
universal-property-localization-Ringᵉ lᵉ Rᵉ Sᵉ xᵉ fᵉ Hᵉ =
  (Tᵉ : Ringᵉ lᵉ) →
  is-equivᵉ (precomp-universal-property-localization-Ringᵉ Rᵉ Sᵉ Tᵉ xᵉ fᵉ Hᵉ)

unique-extension-universal-property-localization-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Tᵉ : Ringᵉ l3ᵉ) (xᵉ : type-Ringᵉ Rᵉ)
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) (Hᵉ : inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ) →
  universal-property-localization-Ringᵉ l3ᵉ Rᵉ Sᵉ xᵉ fᵉ Hᵉ →
  (hᵉ : hom-Ringᵉ Rᵉ Tᵉ) (Kᵉ : inverts-element-hom-Ringᵉ Rᵉ Tᵉ xᵉ hᵉ) →
  is-contrᵉ
    ( Σᵉ ( hom-Ringᵉ Sᵉ Tᵉ)
        ( λ gᵉ → htpy-hom-Ringᵉ Rᵉ Tᵉ (comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ gᵉ fᵉ) hᵉ))
unique-extension-universal-property-localization-Ringᵉ Rᵉ Sᵉ Tᵉ xᵉ fᵉ Hᵉ up-fᵉ hᵉ Kᵉ =
  is-contr-equiv'ᵉ
    ( fiberᵉ
      ( precomp-universal-property-localization-Ringᵉ Rᵉ Sᵉ Tᵉ xᵉ fᵉ Hᵉ)
      ( pairᵉ hᵉ Kᵉ))
    ( equiv-totᵉ ( λ gᵉ →
      ( extensionality-hom-Ringᵉ Rᵉ Tᵉ (comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ gᵉ fᵉ) hᵉ) ∘eᵉ
      ( extensionality-type-subtype'ᵉ
        ( inverts-element-hom-ring-Propᵉ Rᵉ Tᵉ xᵉ)
        ( precomp-universal-property-localization-Ringᵉ Rᵉ Sᵉ Tᵉ xᵉ fᵉ Hᵉ gᵉ)
        ( pairᵉ hᵉ Kᵉ))))
    ( is-contr-map-is-equivᵉ (up-fᵉ Tᵉ) (pairᵉ hᵉ Kᵉ))

center-unique-extension-universal-property-localization-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Tᵉ : Ringᵉ l3ᵉ) (xᵉ : type-Ringᵉ Rᵉ)
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) (Hᵉ : inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ) →
  universal-property-localization-Ringᵉ l3ᵉ Rᵉ Sᵉ xᵉ fᵉ Hᵉ →
  (hᵉ : hom-Ringᵉ Rᵉ Tᵉ) (Kᵉ : inverts-element-hom-Ringᵉ Rᵉ Tᵉ xᵉ hᵉ) →
  Σᵉ (hom-Ringᵉ Sᵉ Tᵉ) (λ gᵉ → htpy-hom-Ringᵉ Rᵉ Tᵉ (comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ gᵉ fᵉ) hᵉ)
center-unique-extension-universal-property-localization-Ringᵉ
  Rᵉ Sᵉ Tᵉ xᵉ fᵉ Hᵉ up-fᵉ hᵉ Kᵉ =
  centerᵉ
    ( unique-extension-universal-property-localization-Ringᵉ
      Rᵉ Sᵉ Tᵉ xᵉ fᵉ Hᵉ up-fᵉ hᵉ Kᵉ)

map-universal-property-localization-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Tᵉ : Ringᵉ l3ᵉ) (xᵉ : type-Ringᵉ Rᵉ)
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) (Hᵉ : inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ) →
  universal-property-localization-Ringᵉ l3ᵉ Rᵉ Sᵉ xᵉ fᵉ Hᵉ →
  (hᵉ : hom-Ringᵉ Rᵉ Tᵉ) (Kᵉ : inverts-element-hom-Ringᵉ Rᵉ Tᵉ xᵉ hᵉ) →
  hom-Ringᵉ Sᵉ Tᵉ
map-universal-property-localization-Ringᵉ Rᵉ Sᵉ Tᵉ xᵉ fᵉ Hᵉ up-fᵉ hᵉ Kᵉ =
  pr1ᵉ ( center-unique-extension-universal-property-localization-Ringᵉ
        Rᵉ Sᵉ Tᵉ xᵉ fᵉ Hᵉ up-fᵉ hᵉ Kᵉ)

htpy-universal-property-localization-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Tᵉ : Ringᵉ l3ᵉ) (xᵉ : type-Ringᵉ Rᵉ)
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) (Hᵉ : inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ) →
  (up-fᵉ : universal-property-localization-Ringᵉ l3ᵉ Rᵉ Sᵉ xᵉ fᵉ Hᵉ) →
  (hᵉ : hom-Ringᵉ Rᵉ Tᵉ) (Kᵉ : inverts-element-hom-Ringᵉ Rᵉ Tᵉ xᵉ hᵉ) →
  htpy-hom-Ringᵉ
    ( Rᵉ)
    ( Tᵉ)
    ( comp-hom-Ringᵉ
      ( Rᵉ)
      ( Sᵉ)
      ( Tᵉ)
      ( map-universal-property-localization-Ringᵉ Rᵉ Sᵉ Tᵉ xᵉ fᵉ Hᵉ up-fᵉ hᵉ Kᵉ)
      ( fᵉ))
    ( hᵉ)
htpy-universal-property-localization-Ringᵉ Rᵉ Sᵉ Tᵉ xᵉ fᵉ Hᵉ up-fᵉ hᵉ Kᵉ =
  pr2ᵉ ( center-unique-extension-universal-property-localization-Ringᵉ
        Rᵉ Sᵉ Tᵉ xᵉ fᵉ Hᵉ up-fᵉ hᵉ Kᵉ)
```

### The type of localizations of a ring $R$ at an element $x$ is contractible

```agda
{-ᵉ
is-equiv-up-localization-up-localization-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Tᵉ : Ringᵉ l3ᵉ) (xᵉ : type-Ringᵉ Rᵉ)
  (fᵉ : hom-set-Ringᵉ Rᵉ Sᵉ) (inverts-fᵉ : inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ) →
  (gᵉ : hom-set-Ringᵉ Rᵉ Tᵉ) (inverts-gᵉ : inverts-element-hom-Ringᵉ Rᵉ Tᵉ xᵉ gᵉ) →
  (hᵉ : hom-set-Ringᵉ Sᵉ Tᵉ) (Hᵉ : htpy-hom-Ringᵉ Rᵉ Tᵉ (comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ hᵉ fᵉ) gᵉ) →
  ({lᵉ : Level} → universal-property-localization-Ringᵉ lᵉ Rᵉ Sᵉ xᵉ fᵉ inverts-fᵉ) →
  ({lᵉ : Level} → universal-property-localization-Ringᵉ lᵉ Rᵉ Tᵉ xᵉ gᵉ inverts-gᵉ) →
  is-iso-Ringᵉ Sᵉ Tᵉ hᵉ
is-equiv-up-localization-up-localization-Ringᵉ
  Rᵉ Sᵉ Tᵉ xᵉ fᵉ inverts-fᵉ gᵉ inverts-gᵉ hᵉ Hᵉ up-fᵉ up-gᵉ = {!is-iso-is-equiv-hom-Ring!ᵉ}
-ᵉ}
```

## Localization at a subset of a ring

```agda
inverts-subset-hom-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Pᵉ : subset-Ringᵉ l3ᵉ Rᵉ) →
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
inverts-subset-hom-Ringᵉ Rᵉ Sᵉ Pᵉ fᵉ =
  (xᵉ : type-Ringᵉ Rᵉ) (pᵉ : type-Propᵉ (Pᵉ xᵉ)) → inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ

is-prop-inverts-subset-hom-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Pᵉ : subset-Ringᵉ l3ᵉ Rᵉ) →
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) → is-propᵉ (inverts-subset-hom-Ringᵉ Rᵉ Sᵉ Pᵉ fᵉ)
is-prop-inverts-subset-hom-Ringᵉ Rᵉ Sᵉ Pᵉ fᵉ =
  is-prop-Πᵉ (λ xᵉ → is-prop-Πᵉ (λ pᵉ → is-prop-inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ))

inv-inverts-subset-hom-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Pᵉ : subset-Ringᵉ l3ᵉ Rᵉ)
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) (Hᵉ : inverts-subset-hom-Ringᵉ Rᵉ Sᵉ Pᵉ fᵉ)
  (xᵉ : type-Ringᵉ Rᵉ) (pᵉ : type-Propᵉ (Pᵉ xᵉ)) → type-Ringᵉ Sᵉ
inv-inverts-subset-hom-Ringᵉ Rᵉ Sᵉ Pᵉ fᵉ Hᵉ xᵉ pᵉ =
  inv-inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ (Hᵉ xᵉ pᵉ)

is-left-inverse-inv-inverts-subset-hom-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Pᵉ : subset-Ringᵉ l3ᵉ Rᵉ)
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) (Hᵉ : inverts-subset-hom-Ringᵉ Rᵉ Sᵉ Pᵉ fᵉ)
  (xᵉ : type-Ringᵉ Rᵉ) (pᵉ : type-Propᵉ (Pᵉ xᵉ)) →
  Idᵉ
    ( mul-Ringᵉ Sᵉ
      ( inv-inverts-subset-hom-Ringᵉ Rᵉ Sᵉ Pᵉ fᵉ Hᵉ xᵉ pᵉ)
      ( map-hom-Ringᵉ Rᵉ Sᵉ fᵉ xᵉ))
    ( one-Ringᵉ Sᵉ)
is-left-inverse-inv-inverts-subset-hom-Ringᵉ Rᵉ Sᵉ Pᵉ fᵉ Hᵉ xᵉ pᵉ =
  is-left-inverse-inv-inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ (Hᵉ xᵉ pᵉ)

is-right-inverse-inv-inverts-subset-hom-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Pᵉ : subset-Ringᵉ l3ᵉ Rᵉ)
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) (Hᵉ : inverts-subset-hom-Ringᵉ Rᵉ Sᵉ Pᵉ fᵉ)
  (xᵉ : type-Ringᵉ Rᵉ) (pᵉ : type-Propᵉ (Pᵉ xᵉ)) →
  Idᵉ
    ( mul-Ringᵉ Sᵉ
      ( map-hom-Ringᵉ Rᵉ Sᵉ fᵉ xᵉ)
      ( inv-inverts-subset-hom-Ringᵉ Rᵉ Sᵉ Pᵉ fᵉ Hᵉ xᵉ pᵉ))
    ( one-Ringᵉ Sᵉ)
is-right-inverse-inv-inverts-subset-hom-Ringᵉ Rᵉ Sᵉ Pᵉ fᵉ Hᵉ xᵉ pᵉ =
  is-right-inverse-inv-inverts-element-hom-Ringᵉ Rᵉ Sᵉ xᵉ fᵉ (Hᵉ xᵉ pᵉ)

inverts-subset-comp-hom-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Tᵉ : Ringᵉ l3ᵉ)
  (Pᵉ : subset-Ringᵉ l4ᵉ Rᵉ) (gᵉ : hom-Ringᵉ Sᵉ Tᵉ) (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) →
  inverts-subset-hom-Ringᵉ Rᵉ Sᵉ Pᵉ fᵉ →
  inverts-subset-hom-Ringᵉ Rᵉ Tᵉ Pᵉ (comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ gᵉ fᵉ)
inverts-subset-comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ Pᵉ gᵉ fᵉ Hᵉ xᵉ pᵉ =
  inverts-element-comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ xᵉ gᵉ fᵉ (Hᵉ xᵉ pᵉ)
```

### The universal property of the localization of a ring at a subset

```agda
precomp-universal-property-localization-subset-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Tᵉ : Ringᵉ l3ᵉ)
  (Pᵉ : subset-Ringᵉ l4ᵉ Rᵉ) →
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) (Hᵉ : inverts-subset-hom-Ringᵉ Rᵉ Sᵉ Pᵉ fᵉ) →
  hom-Ringᵉ Sᵉ Tᵉ → Σᵉ (hom-Ringᵉ Rᵉ Tᵉ) (inverts-subset-hom-Ringᵉ Rᵉ Tᵉ Pᵉ)
pr1ᵉ (precomp-universal-property-localization-subset-Ringᵉ Rᵉ Sᵉ Tᵉ Pᵉ fᵉ Hᵉ gᵉ) =
  comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ gᵉ fᵉ
pr2ᵉ (precomp-universal-property-localization-subset-Ringᵉ Rᵉ Sᵉ Tᵉ Pᵉ fᵉ Hᵉ gᵉ) =
  inverts-subset-comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ Pᵉ gᵉ fᵉ Hᵉ

universal-property-localization-subset-Ringᵉ :
  (lᵉ : Level) {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ)
  (Pᵉ : subset-Ringᵉ l3ᵉ Rᵉ) (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) →
  inverts-subset-hom-Ringᵉ Rᵉ Sᵉ Pᵉ fᵉ → UUᵉ (lsuc lᵉ ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
universal-property-localization-subset-Ringᵉ lᵉ Rᵉ Sᵉ Pᵉ fᵉ Hᵉ =
  (Tᵉ : Ringᵉ lᵉ) →
  is-equivᵉ (precomp-universal-property-localization-subset-Ringᵉ Rᵉ Sᵉ Tᵉ Pᵉ fᵉ Hᵉ)
```