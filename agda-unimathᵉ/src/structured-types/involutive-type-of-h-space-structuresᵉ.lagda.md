# The involutive type of H-space structures on a pointed type

```agda
module structured-types.involutive-type-of-h-space-structuresᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-transportᵉ
open import foundation.constant-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.symmetric-identity-typesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.constant-pointed-mapsᵉ
open import structured-types.pointed-typesᵉ

open import univalent-combinatorics.2-element-typesᵉ
```

</details>

## Idea

Weᵉ constructᵉ theᵉ **involutiveᵉ typeᵉ ofᵉ H-spaceᵉ structures**ᵉ onᵉ aᵉ pointedᵉ type.ᵉ

## Definition

### The involutive type of H-space structures on a pointed type

```agda
h-space-Involutive-Typeᵉ :
  {l1ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Xᵉ : 2-Element-Typeᵉ lzero) → UUᵉ l1ᵉ
h-space-Involutive-Typeᵉ Aᵉ Xᵉ =
  Σᵉ ( (type-2-Element-Typeᵉ Xᵉ → type-Pointed-Typeᵉ Aᵉ) → type-Pointed-Typeᵉ Aᵉ)
    ( λ μᵉ →
      Σᵉ ( ( fᵉ : type-2-Element-Typeᵉ Xᵉ → type-Pointed-Typeᵉ Aᵉ) →
          ( xᵉ : type-2-Element-Typeᵉ Xᵉ) →
          ( pᵉ : fᵉ xᵉ ＝ᵉ point-Pointed-Typeᵉ Aᵉ) →
          μᵉ fᵉ ＝ᵉ fᵉ (map-swap-2-Element-Typeᵉ Xᵉ xᵉ))
        ( λ νᵉ →
          symmetric-Idᵉ
            ( ( Xᵉ) ,ᵉ
              ( λ xᵉ →
                νᵉ ( map-constant-pointed-mapᵉ (type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ) Aᵉ)
                  ( xᵉ)
                  ( reflᵉ)))))
```

## Properties

### Characterization of equality in the involutive type of H-space structures on a pointed type

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Xᵉ : 2-Element-Typeᵉ lzero)
  where

  htpy-h-space-Involutive-Typeᵉ :
    (μᵉ μ'ᵉ : h-space-Involutive-Typeᵉ Aᵉ Xᵉ) → UUᵉ l1ᵉ
  htpy-h-space-Involutive-Typeᵉ μᵉ μ'ᵉ =
    Σᵉ ( (fᵉ : type-2-Element-Typeᵉ Xᵉ → type-Pointed-Typeᵉ Aᵉ) → pr1ᵉ μᵉ fᵉ ＝ᵉ pr1ᵉ μ'ᵉ fᵉ)
      ( λ Hᵉ →
        Σᵉ ( ( fᵉ : type-2-Element-Typeᵉ Xᵉ → type-Pointed-Typeᵉ Aᵉ) →
            ( xᵉ : type-2-Element-Typeᵉ Xᵉ) →
            ( pᵉ : fᵉ xᵉ ＝ᵉ point-Pointed-Typeᵉ Aᵉ) →
            pr1ᵉ (pr2ᵉ μᵉ) fᵉ xᵉ pᵉ ＝ᵉ (Hᵉ fᵉ ∙ᵉ pr1ᵉ (pr2ᵉ μ'ᵉ) fᵉ xᵉ pᵉ))
          ( λ Kᵉ →
            Eq-symmetric-Idᵉ
              ( ( Xᵉ) ,ᵉ
                ( λ xᵉ →
                  ( Hᵉ ( map-constant-pointed-mapᵉ
                        ( type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ)
                        ( Aᵉ))) ∙ᵉ
                  ( pr1ᵉ
                    ( pr2ᵉ μ'ᵉ)
                    ( map-constant-pointed-mapᵉ (type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ) Aᵉ)
                    ( xᵉ)
                    ( reflᵉ))))
              ( tr-symmetric-Idᵉ
                ( ( Xᵉ) ,ᵉ
                  ( λ xᵉ →
                    pr1ᵉ
                      ( pr2ᵉ μᵉ)
                      ( map-constant-pointed-mapᵉ (type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ) Aᵉ)
                      ( xᵉ)
                      ( reflᵉ)))
                ( ( Xᵉ) ,ᵉ
                  ( λ xᵉ →
                    ( Hᵉ ( map-constant-pointed-mapᵉ
                          ( type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ)
                          ( Aᵉ))) ∙ᵉ
                    ( pr1ᵉ
                      ( pr2ᵉ μ'ᵉ)
                      ( map-constant-pointed-mapᵉ (type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ) Aᵉ)
                        ( xᵉ)
                        ( reflᵉ))))
                ( id-equivᵉ)
                ( λ xᵉ →
                  Kᵉ ( map-constant-pointed-mapᵉ (type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ) Aᵉ)
                    ( xᵉ)
                    ( reflᵉ))
                ( pr2ᵉ (pr2ᵉ μᵉ)))
              ( map-equiv-symmetric-Idᵉ
                ( equiv-concatᵉ
                  ( Hᵉ ( constᵉ
                        ( type-2-Element-Typeᵉ Xᵉ)
                        ( point-Pointed-Typeᵉ Aᵉ)))
                  ( point-Pointed-Typeᵉ Aᵉ))
                ( ( Xᵉ) ,ᵉ
                  ( λ xᵉ →
                    pr1ᵉ
                      ( pr2ᵉ μ'ᵉ)
                      ( map-constant-pointed-mapᵉ (type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ) Aᵉ)
                      ( xᵉ)
                      ( reflᵉ)))
                ( pr2ᵉ (pr2ᵉ μ'ᵉ)))))

  refl-htpy-h-space-Involutive-Typeᵉ :
    (μᵉ : h-space-Involutive-Typeᵉ Aᵉ Xᵉ) → htpy-h-space-Involutive-Typeᵉ μᵉ μᵉ
  pr1ᵉ (refl-htpy-h-space-Involutive-Typeᵉ (μᵉ ,ᵉ unit-laws-μᵉ ,ᵉ coh-μᵉ)) fᵉ = reflᵉ
  pr1ᵉ
    ( pr2ᵉ (refl-htpy-h-space-Involutive-Typeᵉ (μᵉ ,ᵉ unit-laws-μᵉ ,ᵉ coh-μᵉ))) fᵉ xᵉ pᵉ =
    reflᵉ
  pr1ᵉ
    ( pr2ᵉ (pr2ᵉ (refl-htpy-h-space-Involutive-Typeᵉ (μᵉ ,ᵉ unit-laws-μᵉ ,ᵉ coh-μᵉ)))) =
    reflᵉ
  pr2ᵉ
    ( pr2ᵉ
      ( pr2ᵉ (refl-htpy-h-space-Involutive-Typeᵉ (μᵉ ,ᵉ unit-laws-μᵉ ,ᵉ coh-μᵉ)))) xᵉ =
    ( ( compute-pr2-tr-symmetric-Idᵉ
        ( ( Xᵉ) ,ᵉ
          ( λ xᵉ →
            unit-laws-μᵉ
              ( map-constant-pointed-mapᵉ (type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ) Aᵉ)
              ( xᵉ)
              ( reflᵉ)))
        ( ( Xᵉ) ,ᵉ
          ( λ xᵉ →
            unit-laws-μᵉ
              ( map-constant-pointed-mapᵉ (type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ) Aᵉ)
              ( xᵉ)
              ( reflᵉ)))
        ( id-equivᵉ)
        ( λ yᵉ → reflᵉ)
        ( λ yᵉ → pr2ᵉ coh-μᵉ yᵉ)
        ( xᵉ)) ∙ᵉ
      ( right-unitᵉ)) ∙ᵉ
    ( invᵉ (ap-idᵉ (pr2ᵉ coh-μᵉ xᵉ)))

  is-torsorial-htpy-h-space-Involutive-Typeᵉ :
    ( μᵉ : h-space-Involutive-Typeᵉ Aᵉ Xᵉ) →
    is-torsorialᵉ (htpy-h-space-Involutive-Typeᵉ μᵉ)
  is-torsorial-htpy-h-space-Involutive-Typeᵉ (μᵉ ,ᵉ νᵉ ,ᵉ ρᵉ) =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ μᵉ)
      ( μᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-Eq-Πᵉ
          ( λ fᵉ → is-torsorial-Eq-Πᵉ (λ xᵉ → is-torsorial-htpyᵉ (νᵉ fᵉ xᵉ))))
        ( νᵉ ,ᵉ (λ fᵉ xᵉ pᵉ → reflᵉ))
        ( is-contr-equivᵉ
          ( Σᵉ ( symmetric-Idᵉ
                ( ( Xᵉ) ,ᵉ
                  ( λ xᵉ →
                    νᵉ ( map-constant-pointed-mapᵉ (type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ) Aᵉ)
                      ( xᵉ)
                      ( reflᵉ))))
              ( Eq-symmetric-Idᵉ
                ( ( Xᵉ) ,ᵉ
                  ( λ xᵉ →
                    νᵉ ( map-constant-pointed-mapᵉ (type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ) Aᵉ)
                      ( xᵉ)
                      ( reflᵉ)))
                ( ρᵉ)))
          ( equiv-totᵉ
            ( λ αᵉ →
              equiv-binary-trᵉ
                ( Eq-symmetric-Idᵉ
                  ( ( Xᵉ) ,ᵉ
                    ( λ xᵉ →
                      νᵉ ( map-constant-pointed-mapᵉ
                          ( type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ)
                          ( Aᵉ))
                        ( xᵉ)
                        ( reflᵉ))))
                ( refl-Eq-unordered-pair-tr-symmetric-Idᵉ
                  ( ( Xᵉ) ,ᵉ
                    ( λ xᵉ →
                      νᵉ ( map-constant-pointed-mapᵉ
                          ( type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ)
                          ( Aᵉ))
                        ( xᵉ)
                        ( reflᵉ)))
                  ( ρᵉ))
                ( id-equiv-symmetric-Idᵉ
                  ( ( Xᵉ) ,ᵉ
                    ( λ xᵉ →
                      νᵉ ( map-constant-pointed-mapᵉ
                          ( type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ)
                          ( Aᵉ))
                        ( xᵉ)
                        ( reflᵉ)))
                  ( αᵉ))))
          ( is-torsorial-Eq-symmetric-Idᵉ
            ( ( Xᵉ) ,ᵉ
              ( λ xᵉ →
                νᵉ ( map-constant-pointed-mapᵉ (type-2-Element-Typeᵉ Xᵉ ,ᵉ xᵉ) Aᵉ)
                  ( xᵉ)
                  ( reflᵉ)))
            ( ρᵉ))))

  htpy-eq-h-space-Involutive-Typeᵉ :
    (μᵉ μ'ᵉ : h-space-Involutive-Typeᵉ Aᵉ Xᵉ) →
    (μᵉ ＝ᵉ μ'ᵉ) → htpy-h-space-Involutive-Typeᵉ μᵉ μ'ᵉ
  htpy-eq-h-space-Involutive-Typeᵉ μᵉ .μᵉ reflᵉ =
    refl-htpy-h-space-Involutive-Typeᵉ μᵉ

  is-equiv-htpy-eq-h-space-Involutive-Typeᵉ :
    (μᵉ μ'ᵉ : h-space-Involutive-Typeᵉ Aᵉ Xᵉ) →
    is-equivᵉ (htpy-eq-h-space-Involutive-Typeᵉ μᵉ μ'ᵉ)
  is-equiv-htpy-eq-h-space-Involutive-Typeᵉ μᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-h-space-Involutive-Typeᵉ μᵉ)
      ( htpy-eq-h-space-Involutive-Typeᵉ μᵉ)

  extensionality-h-space-Involutive-Typeᵉ :
    (μᵉ μ'ᵉ : h-space-Involutive-Typeᵉ Aᵉ Xᵉ) →
    (μᵉ ＝ᵉ μ'ᵉ) ≃ᵉ htpy-h-space-Involutive-Typeᵉ μᵉ μ'ᵉ
  pr1ᵉ (extensionality-h-space-Involutive-Typeᵉ μᵉ μ'ᵉ) =
    htpy-eq-h-space-Involutive-Typeᵉ μᵉ μ'ᵉ
  pr2ᵉ (extensionality-h-space-Involutive-Typeᵉ μᵉ μ'ᵉ) =
    is-equiv-htpy-eq-h-space-Involutive-Typeᵉ μᵉ μ'ᵉ

  eq-htpy-h-space-Involutive-Typeᵉ :
    (μᵉ μ'ᵉ : h-space-Involutive-Typeᵉ Aᵉ Xᵉ) →
    htpy-h-space-Involutive-Typeᵉ μᵉ μ'ᵉ → μᵉ ＝ᵉ μ'ᵉ
  eq-htpy-h-space-Involutive-Typeᵉ μᵉ μ'ᵉ =
    map-inv-equivᵉ (extensionality-h-space-Involutive-Typeᵉ μᵉ μ'ᵉ)
```