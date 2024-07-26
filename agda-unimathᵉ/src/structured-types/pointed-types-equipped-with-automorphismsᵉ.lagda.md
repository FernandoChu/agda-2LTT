# Pointed types equipped with automorphisms

```agda
module structured-types.pointed-types-equipped-with-automorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.automorphismsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ pointedᵉ typeᵉ equippedᵉ with anᵉ automorphismᵉ isᵉ aᵉ pairᵉ consistingᵉ ofᵉ aᵉ pointedᵉ
typeᵉ `A`ᵉ andᵉ anᵉ automorphismᵉ onᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `A`.ᵉ Theᵉ baseᵉ pointᵉ isᵉ
notᵉ requiredᵉ to beᵉ preserved.ᵉ

## Definitions

### Types equipped with an automorphism

```agda
Pointed-Type-With-Autᵉ :
  (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Pointed-Type-With-Autᵉ lᵉ =
  Σᵉ (Pointed-Typeᵉ lᵉ) (λ Xᵉ → Autᵉ (type-Pointed-Typeᵉ Xᵉ))

module _
  {lᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ lᵉ)
  where

  pointed-type-Pointed-Type-With-Autᵉ : Pointed-Typeᵉ lᵉ
  pointed-type-Pointed-Type-With-Autᵉ = pr1ᵉ Xᵉ

  type-Pointed-Type-With-Autᵉ : UUᵉ lᵉ
  type-Pointed-Type-With-Autᵉ =
    type-Pointed-Typeᵉ pointed-type-Pointed-Type-With-Autᵉ

  point-Pointed-Type-With-Autᵉ : type-Pointed-Type-With-Autᵉ
  point-Pointed-Type-With-Autᵉ =
    point-Pointed-Typeᵉ pointed-type-Pointed-Type-With-Autᵉ

  aut-Pointed-Type-With-Autᵉ : Autᵉ type-Pointed-Type-With-Autᵉ
  aut-Pointed-Type-With-Autᵉ = pr2ᵉ Xᵉ

  map-aut-Pointed-Type-With-Autᵉ :
    type-Pointed-Type-With-Autᵉ → type-Pointed-Type-With-Autᵉ
  map-aut-Pointed-Type-With-Autᵉ = map-equivᵉ aut-Pointed-Type-With-Autᵉ

  map-inv-aut-Pointed-Type-With-Autᵉ :
    type-Pointed-Type-With-Autᵉ → type-Pointed-Type-With-Autᵉ
  map-inv-aut-Pointed-Type-With-Autᵉ = map-inv-equivᵉ aut-Pointed-Type-With-Autᵉ

  is-section-map-inv-aut-Pointed-Type-With-Autᵉ :
    (map-aut-Pointed-Type-With-Autᵉ ∘ᵉ map-inv-aut-Pointed-Type-With-Autᵉ) ~ᵉ idᵉ
  is-section-map-inv-aut-Pointed-Type-With-Autᵉ =
    is-section-map-inv-equivᵉ aut-Pointed-Type-With-Autᵉ

  is-retraction-map-inv-aut-Pointed-Type-With-Autᵉ :
    (map-inv-aut-Pointed-Type-With-Autᵉ ∘ᵉ map-aut-Pointed-Type-With-Autᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-aut-Pointed-Type-With-Autᵉ =
    is-retraction-map-inv-equivᵉ aut-Pointed-Type-With-Autᵉ
```

### Morphisms of pointed types with automorphisms

```agda
hom-Pointed-Type-With-Autᵉ :
  {l1ᵉ l2ᵉ : Level} →
  Pointed-Type-With-Autᵉ l1ᵉ → Pointed-Type-With-Autᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
hom-Pointed-Type-With-Autᵉ {l1ᵉ} {l2ᵉ} Xᵉ Yᵉ =
  Σᵉ ( type-Pointed-Type-With-Autᵉ Xᵉ → type-Pointed-Type-With-Autᵉ Yᵉ)
    ( λ fᵉ →
      (fᵉ (point-Pointed-Type-With-Autᵉ Xᵉ) ＝ᵉ point-Pointed-Type-With-Autᵉ Yᵉ) ×ᵉ
      ( ( fᵉ ∘ᵉ (map-aut-Pointed-Type-With-Autᵉ Xᵉ)) ~ᵉ
        ( (map-aut-Pointed-Type-With-Autᵉ Yᵉ) ∘ᵉ fᵉ)))

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ l1ᵉ) (Yᵉ : Pointed-Type-With-Autᵉ l2ᵉ)
  (fᵉ : hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ)
  where

  map-hom-Pointed-Type-With-Autᵉ :
    type-Pointed-Type-With-Autᵉ Xᵉ → type-Pointed-Type-With-Autᵉ Yᵉ
  map-hom-Pointed-Type-With-Autᵉ = pr1ᵉ fᵉ

  preserves-point-map-hom-Pointed-Type-With-Autᵉ :
    ( map-hom-Pointed-Type-With-Autᵉ (point-Pointed-Type-With-Autᵉ Xᵉ)) ＝ᵉ
    ( point-Pointed-Type-With-Autᵉ Yᵉ)
  preserves-point-map-hom-Pointed-Type-With-Autᵉ = pr1ᵉ (pr2ᵉ fᵉ)

  preserves-aut-map-hom-Pointed-Type-With-Autᵉ :
    ( map-hom-Pointed-Type-With-Autᵉ ∘ᵉ map-aut-Pointed-Type-With-Autᵉ Xᵉ) ~ᵉ
    ( ( map-aut-Pointed-Type-With-Autᵉ Yᵉ) ∘ᵉ map-hom-Pointed-Type-With-Autᵉ)
  preserves-aut-map-hom-Pointed-Type-With-Autᵉ = pr2ᵉ (pr2ᵉ fᵉ)
```

## Properties

### Characterization of the identity type of morphisms of pointed types with automorphisms

```agda
htpy-hom-Pointed-Type-With-Autᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ l1ᵉ)
  (Yᵉ : Pointed-Type-With-Autᵉ l2ᵉ) (h1ᵉ h2ᵉ : hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
htpy-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ h2ᵉ =
  Σᵉ ( map-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ
      ~ᵉ map-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h2ᵉ)
    ( λ Hᵉ →
      ( ( preserves-point-map-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ) ＝ᵉ
        ( ( Hᵉ (point-Pointed-Type-With-Autᵉ Xᵉ)) ∙ᵉ
          ( preserves-point-map-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h2ᵉ))) ×ᵉ
      ( ( xᵉ : type-Pointed-Type-With-Autᵉ Xᵉ) →
        ( ( ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ xᵉ) ∙ᵉ
            ( apᵉ (map-aut-Pointed-Type-With-Autᵉ Yᵉ) (Hᵉ xᵉ))) ＝ᵉ
          ( ( Hᵉ (map-aut-Pointed-Type-With-Autᵉ Xᵉ xᵉ)) ∙ᵉ
            ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h2ᵉ xᵉ)))))

refl-htpy-hom-Pointed-Type-With-Autᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ l1ᵉ)
  (Yᵉ : Pointed-Type-With-Autᵉ l2ᵉ) (hᵉ : hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ) →
  htpy-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ hᵉ hᵉ
refl-htpy-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ hᵉ =
  pairᵉ refl-htpyᵉ (pairᵉ reflᵉ (λ xᵉ → right-unitᵉ))

htpy-hom-Pointed-Type-With-Aut-eqᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ l1ᵉ)
  (Yᵉ : Pointed-Type-With-Autᵉ l2ᵉ) (h1ᵉ h2ᵉ : hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ) →
  h1ᵉ ＝ᵉ h2ᵉ → htpy-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ h2ᵉ
htpy-hom-Pointed-Type-With-Aut-eqᵉ Xᵉ Yᵉ h1ᵉ .h1ᵉ reflᵉ =
  refl-htpy-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ

is-torsorial-htpy-hom-Pointed-Type-With-Autᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ l1ᵉ)
  (Yᵉ : Pointed-Type-With-Autᵉ l2ᵉ) (h1ᵉ : hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ) →
  is-torsorialᵉ (htpy-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ)
is-torsorial-htpy-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ =
  is-torsorial-Eq-structureᵉ
    ( is-torsorial-htpyᵉ (map-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ))
    ( pairᵉ (map-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ) refl-htpyᵉ)
    ( is-torsorial-Eq-structureᵉ
      ( is-torsorial-Idᵉ
        ( preserves-point-map-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ))
      ( pairᵉ (preserves-point-map-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ) reflᵉ)
      ( is-contr-equiv'ᵉ
        ( Σᵉ ( ( xᵉ : type-Pointed-Type-With-Autᵉ Xᵉ) →
              ( map-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ
                ( map-aut-Pointed-Type-With-Autᵉ Xᵉ xᵉ)) ＝ᵉ
              ( map-aut-Pointed-Type-With-Autᵉ Yᵉ
                ( map-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ xᵉ)))
            ( λ aut-h2ᵉ →
              ( xᵉ : type-Pointed-Type-With-Autᵉ Xᵉ) →
              preserves-aut-map-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ xᵉ ＝ᵉ aut-h2ᵉ xᵉ))
        ( equiv-totᵉ (equiv-concat-htpyᵉ right-unit-htpyᵉ))
        ( is-torsorial-htpyᵉ
          ( preserves-aut-map-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ))))

is-equiv-htpy-hom-Pointed-Type-With-Autᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ l1ᵉ)
  (Yᵉ : Pointed-Type-With-Autᵉ l2ᵉ) (h1ᵉ h2ᵉ : hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ) →
  is-equivᵉ (htpy-hom-Pointed-Type-With-Aut-eqᵉ Xᵉ Yᵉ h1ᵉ h2ᵉ)
is-equiv-htpy-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ =
  fundamental-theorem-idᵉ
    ( is-torsorial-htpy-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ)
    ( htpy-hom-Pointed-Type-With-Aut-eqᵉ Xᵉ Yᵉ h1ᵉ)

eq-htpy-hom-Pointed-Type-With-Autᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Type-With-Autᵉ l1ᵉ)
  (Yᵉ : Pointed-Type-With-Autᵉ l2ᵉ) (h1ᵉ h2ᵉ : hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ) →
  htpy-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ h2ᵉ → h1ᵉ ＝ᵉ h2ᵉ
eq-htpy-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ h2ᵉ =
  map-inv-is-equivᵉ (is-equiv-htpy-hom-Pointed-Type-With-Autᵉ Xᵉ Yᵉ h1ᵉ h2ᵉ)
```