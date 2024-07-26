# Free loops

```agda
module synthetic-homotopy-theory.free-loopsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.constant-type-familiesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **freeᵉ loop**ᵉ in aᵉ typeᵉ `X`ᵉ consistsᵉ ofᵉ aᵉ pointᵉ `xᵉ : X`ᵉ andᵉ anᵉ
[identification](foundation.identity-types.mdᵉ) `xᵉ ＝ᵉ x`.ᵉ Theᵉ typeᵉ ofᵉ freeᵉ loopsᵉ
in `X`ᵉ isᵉ [equivalent](foundation-core.equivalences.mdᵉ) to theᵉ typeᵉ ofᵉ mapsᵉ
`𝕊¹ᵉ → X`.ᵉ

## Definitions

### Free loops

```agda
free-loopᵉ : {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) → UUᵉ l1ᵉ
free-loopᵉ Xᵉ = Σᵉ Xᵉ (λ xᵉ → xᵉ ＝ᵉ xᵉ)

module _
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ}
  where

  base-free-loopᵉ : free-loopᵉ Xᵉ → Xᵉ
  base-free-loopᵉ = pr1ᵉ

  loop-free-loopᵉ : (αᵉ : free-loopᵉ Xᵉ) → base-free-loopᵉ αᵉ ＝ᵉ base-free-loopᵉ αᵉ
  loop-free-loopᵉ = pr2ᵉ
```

### Free dependent loops

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (αᵉ : free-loopᵉ Xᵉ) (Pᵉ : Xᵉ → UUᵉ l2ᵉ)
  where

  free-dependent-loopᵉ : UUᵉ l2ᵉ
  free-dependent-loopᵉ =
    Σᵉ ( Pᵉ (base-free-loopᵉ αᵉ)) (λ p₀ᵉ → trᵉ Pᵉ (loop-free-loopᵉ αᵉ) p₀ᵉ ＝ᵉ p₀ᵉ)

  base-free-dependent-loopᵉ : free-dependent-loopᵉ → Pᵉ (base-free-loopᵉ αᵉ)
  base-free-dependent-loopᵉ = pr1ᵉ

  loop-free-dependent-loopᵉ :
    (βᵉ : free-dependent-loopᵉ) →
    ( trᵉ Pᵉ (loop-free-loopᵉ αᵉ) (base-free-dependent-loopᵉ βᵉ)) ＝ᵉ
    ( base-free-dependent-loopᵉ βᵉ)
  loop-free-dependent-loopᵉ = pr2ᵉ
```

## Properties

### Characterization of the identity type of the type of free loops

```agda
module _
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ}
  where

  Eq-free-loopᵉ : (αᵉ α'ᵉ : free-loopᵉ Xᵉ) → UUᵉ l1ᵉ
  Eq-free-loopᵉ (pairᵉ xᵉ αᵉ) α'ᵉ =
    Σᵉ (Idᵉ xᵉ (base-free-loopᵉ α'ᵉ)) (λ pᵉ → Idᵉ (αᵉ ∙ᵉ pᵉ) (pᵉ ∙ᵉ (loop-free-loopᵉ α'ᵉ)))

  refl-Eq-free-loopᵉ : (αᵉ : free-loopᵉ Xᵉ) → Eq-free-loopᵉ αᵉ αᵉ
  pr1ᵉ (refl-Eq-free-loopᵉ (pairᵉ xᵉ αᵉ)) = reflᵉ
  pr2ᵉ (refl-Eq-free-loopᵉ (pairᵉ xᵉ αᵉ)) = right-unitᵉ

  Eq-eq-free-loopᵉ : (αᵉ α'ᵉ : free-loopᵉ Xᵉ) → Idᵉ αᵉ α'ᵉ → Eq-free-loopᵉ αᵉ α'ᵉ
  Eq-eq-free-loopᵉ αᵉ .αᵉ reflᵉ = refl-Eq-free-loopᵉ αᵉ

  abstract
    is-torsorial-Eq-free-loopᵉ :
      (αᵉ : free-loopᵉ Xᵉ) → is-torsorialᵉ (Eq-free-loopᵉ αᵉ)
    is-torsorial-Eq-free-loopᵉ (pairᵉ xᵉ αᵉ) =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-Idᵉ xᵉ)
        ( pairᵉ xᵉ reflᵉ)
        ( is-contr-is-equiv'ᵉ
          ( Σᵉ (Idᵉ xᵉ xᵉ) (λ α'ᵉ → Idᵉ αᵉ α'ᵉ))
          ( totᵉ (λ α'ᵉ αᵉ → right-unitᵉ ∙ᵉ αᵉ))
          ( is-equiv-tot-is-fiberwise-equivᵉ
            ( λ α'ᵉ → is-equiv-concatᵉ right-unitᵉ α'ᵉ))
          ( is-torsorial-Idᵉ αᵉ))

  abstract
    is-equiv-Eq-eq-free-loopᵉ :
      (αᵉ α'ᵉ : free-loopᵉ Xᵉ) → is-equivᵉ (Eq-eq-free-loopᵉ αᵉ α'ᵉ)
    is-equiv-Eq-eq-free-loopᵉ αᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-Eq-free-loopᵉ αᵉ)
        ( Eq-eq-free-loopᵉ αᵉ)
```

### Characterization of the identity type of free dependent loops

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (αᵉ : free-loopᵉ Xᵉ) (Pᵉ : Xᵉ → UUᵉ l2ᵉ)
  where

  Eq-free-dependent-loopᵉ : (pᵉ p'ᵉ : free-dependent-loopᵉ αᵉ Pᵉ) → UUᵉ l2ᵉ
  Eq-free-dependent-loopᵉ (pairᵉ yᵉ pᵉ) p'ᵉ =
    Σᵉ ( Idᵉ yᵉ (base-free-dependent-loopᵉ αᵉ Pᵉ p'ᵉ))
      ( λ qᵉ →
        ( pᵉ ∙ᵉ qᵉ) ＝ᵉ
        ( ( apᵉ (trᵉ Pᵉ (loop-free-loopᵉ αᵉ)) qᵉ) ∙ᵉ
          ( loop-free-dependent-loopᵉ αᵉ Pᵉ p'ᵉ)))

  refl-Eq-free-dependent-loopᵉ :
    (pᵉ : free-dependent-loopᵉ αᵉ Pᵉ) → Eq-free-dependent-loopᵉ pᵉ pᵉ
  pr1ᵉ (refl-Eq-free-dependent-loopᵉ (pairᵉ yᵉ pᵉ)) = reflᵉ
  pr2ᵉ (refl-Eq-free-dependent-loopᵉ (pairᵉ yᵉ pᵉ)) = right-unitᵉ

  Eq-free-dependent-loop-eqᵉ :
    ( pᵉ p'ᵉ : free-dependent-loopᵉ αᵉ Pᵉ) → Idᵉ pᵉ p'ᵉ → Eq-free-dependent-loopᵉ pᵉ p'ᵉ
  Eq-free-dependent-loop-eqᵉ pᵉ .pᵉ reflᵉ = refl-Eq-free-dependent-loopᵉ pᵉ

  abstract
    is-torsorial-Eq-free-dependent-loopᵉ :
      ( pᵉ : free-dependent-loopᵉ αᵉ Pᵉ) → is-torsorialᵉ (Eq-free-dependent-loopᵉ pᵉ)
    is-torsorial-Eq-free-dependent-loopᵉ (pairᵉ yᵉ pᵉ) =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-Idᵉ yᵉ)
        ( pairᵉ yᵉ reflᵉ)
        ( is-contr-is-equiv'ᵉ
          ( Σᵉ (Idᵉ (trᵉ Pᵉ (loop-free-loopᵉ αᵉ) yᵉ) yᵉ) (λ p'ᵉ → Idᵉ pᵉ p'ᵉ))
          ( totᵉ (λ p'ᵉ αᵉ → right-unitᵉ ∙ᵉ αᵉ))
          ( is-equiv-tot-is-fiberwise-equivᵉ
            ( λ p'ᵉ → is-equiv-concatᵉ right-unitᵉ p'ᵉ))
          ( is-torsorial-Idᵉ pᵉ))

  abstract
    is-equiv-Eq-free-dependent-loop-eqᵉ :
      (pᵉ p'ᵉ : free-dependent-loopᵉ αᵉ Pᵉ) →
      is-equivᵉ (Eq-free-dependent-loop-eqᵉ pᵉ p'ᵉ)
    is-equiv-Eq-free-dependent-loop-eqᵉ pᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-Eq-free-dependent-loopᵉ pᵉ)
        ( Eq-free-dependent-loop-eqᵉ pᵉ)

  eq-Eq-free-dependent-loopᵉ :
    (pᵉ p'ᵉ : free-dependent-loopᵉ αᵉ Pᵉ) →
    Eq-free-dependent-loopᵉ pᵉ p'ᵉ → Idᵉ pᵉ p'ᵉ
  eq-Eq-free-dependent-loopᵉ pᵉ p'ᵉ =
    map-inv-is-equivᵉ (is-equiv-Eq-free-dependent-loop-eqᵉ pᵉ p'ᵉ)
```

### The type of free dependent loops in a constant family of types is equivalent to the type of ordinary free loops

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (αᵉ : free-loopᵉ Xᵉ) (Yᵉ : UUᵉ l2ᵉ)
  where

  compute-free-dependent-loop-constant-type-familyᵉ :
    free-loopᵉ Yᵉ ≃ᵉ free-dependent-loopᵉ αᵉ (λ xᵉ → Yᵉ)
  compute-free-dependent-loop-constant-type-familyᵉ =
    equiv-totᵉ
      ( λ yᵉ → equiv-concatᵉ (tr-constant-type-familyᵉ (loop-free-loopᵉ αᵉ) yᵉ) yᵉ)

  map-compute-free-dependent-loop-constant-type-familyᵉ :
    free-loopᵉ Yᵉ → free-dependent-loopᵉ αᵉ (λ xᵉ → Yᵉ)
  map-compute-free-dependent-loop-constant-type-familyᵉ =
    map-equivᵉ compute-free-dependent-loop-constant-type-familyᵉ
```