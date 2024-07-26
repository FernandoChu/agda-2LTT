# Codiagonals of maps

```agda
module synthetic-homotopy-theory.codiagonals-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.suspension-structuresᵉ
open import synthetic-homotopy-theory.suspensions-of-typesᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Theᵉ **codiagonal**ᵉ ofᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ theᵉ uniqueᵉ mapᵉ `∇ᵉ fᵉ : Bᵉ ⊔_Aᵉ Bᵉ → B`ᵉ
equippedᵉ with [homotopies](foundation-core.homotopies.mdᵉ)

```text
  Hᵉ : ∇ᵉ fᵉ ∘ᵉ inlᵉ ~ᵉ idᵉ
  Kᵉ : ∇ᵉ fᵉ ∘ᵉ inrᵉ ~ᵉ idᵉ
  Lᵉ : (Hᵉ ·rᵉ fᵉ) ~ᵉ (∇ᵉ fᵉ ·lᵉ glueᵉ) ∙hᵉ (Kᵉ ·rᵉ fᵉ)
```

Theᵉ [fibers](foundation-core.fibers-of-maps.mdᵉ) ofᵉ theᵉ codiagonalᵉ areᵉ equivalentᵉ
to theᵉ [suspensions](synthetic-homotopy-theory.suspensions-of-types.mdᵉ) ofᵉ theᵉ
fibersᵉ ofᵉ `f`.ᵉ

## Definitions

### The codiagonal of a map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  cocone-codiagonal-mapᵉ : coconeᵉ fᵉ fᵉ Bᵉ
  pr1ᵉ cocone-codiagonal-mapᵉ = idᵉ
  pr1ᵉ (pr2ᵉ cocone-codiagonal-mapᵉ) = idᵉ
  pr2ᵉ (pr2ᵉ cocone-codiagonal-mapᵉ) = refl-htpyᵉ

  codiagonal-mapᵉ : pushoutᵉ fᵉ fᵉ → Bᵉ
  codiagonal-mapᵉ = cogapᵉ fᵉ fᵉ cocone-codiagonal-mapᵉ

  compute-inl-codiagonal-mapᵉ :
    codiagonal-mapᵉ ∘ᵉ inl-pushoutᵉ fᵉ fᵉ ~ᵉ idᵉ
  compute-inl-codiagonal-mapᵉ =
    compute-inl-cogapᵉ fᵉ fᵉ cocone-codiagonal-mapᵉ

  compute-inr-codiagonal-mapᵉ :
    codiagonal-mapᵉ ∘ᵉ inr-pushoutᵉ fᵉ fᵉ ~ᵉ idᵉ
  compute-inr-codiagonal-mapᵉ =
    compute-inr-cogapᵉ fᵉ fᵉ cocone-codiagonal-mapᵉ

  compute-glue-codiagonal-mapᵉ :
    statement-coherence-htpy-coconeᵉ fᵉ fᵉ
      ( cocone-mapᵉ fᵉ fᵉ (cocone-pushoutᵉ fᵉ fᵉ) codiagonal-mapᵉ)
      ( cocone-codiagonal-mapᵉ)
      ( compute-inl-codiagonal-mapᵉ)
      ( compute-inr-codiagonal-mapᵉ)
  compute-glue-codiagonal-mapᵉ =
    compute-glue-cogapᵉ fᵉ fᵉ cocone-codiagonal-mapᵉ
```

## Properties

### The codiagonal is the fiberwise suspension

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (bᵉ : Bᵉ)
  where

  universal-property-suspension-cocone-fiberᵉ :
    {lᵉ : Level} →
    Σᵉ ( coconeᵉ
        ( terminal-mapᵉ (fiberᵉ fᵉ bᵉ))
        ( terminal-mapᵉ (fiberᵉ fᵉ bᵉ))
        ( fiberᵉ (codiagonal-mapᵉ fᵉ) bᵉ))
      ( universal-property-pushout-Levelᵉ lᵉ
        ( terminal-mapᵉ (fiberᵉ fᵉ bᵉ))
        ( terminal-mapᵉ (fiberᵉ fᵉ bᵉ)))
  universal-property-suspension-cocone-fiberᵉ =
    universal-property-pushout-cogap-fiber-up-to-equivᵉ fᵉ fᵉ
      ( cocone-codiagonal-mapᵉ fᵉ)
      ( bᵉ)
      ( fiberᵉ fᵉ bᵉ)
      ( unitᵉ)
      ( unitᵉ)
      ( inv-equivᵉ
        ( terminal-mapᵉ (fiberᵉ idᵉ bᵉ) ,ᵉ
        ( is-equiv-terminal-map-is-contrᵉ (is-torsorial-Id'ᵉ bᵉ))))
      ( inv-equivᵉ
        ( terminal-mapᵉ (fiberᵉ idᵉ bᵉ) ,ᵉ
          ( is-equiv-terminal-map-is-contrᵉ (is-torsorial-Id'ᵉ bᵉ))))
      ( id-equivᵉ)
      ( terminal-mapᵉ (fiberᵉ fᵉ bᵉ))
      ( terminal-mapᵉ (fiberᵉ fᵉ bᵉ))
      ( λ _ → eq-is-contrᵉ (is-torsorial-Id'ᵉ bᵉ))
      ( λ _ → eq-is-contrᵉ (is-torsorial-Id'ᵉ bᵉ))

  suspension-cocone-fiberᵉ :
    suspension-coconeᵉ (fiberᵉ fᵉ bᵉ) (fiberᵉ (codiagonal-mapᵉ fᵉ) bᵉ)
  suspension-cocone-fiberᵉ =
    pr1ᵉ (universal-property-suspension-cocone-fiberᵉ {lzeroᵉ})

  universal-property-suspension-fiberᵉ :
    universal-property-pushoutᵉ
      ( terminal-mapᵉ (fiberᵉ fᵉ bᵉ))
      ( terminal-mapᵉ (fiberᵉ fᵉ bᵉ))
      ( suspension-cocone-fiberᵉ)
  universal-property-suspension-fiberᵉ =
    pr2ᵉ universal-property-suspension-cocone-fiberᵉ

  fiber-codiagonal-map-suspension-fiberᵉ :
    suspensionᵉ (fiberᵉ fᵉ bᵉ) → fiberᵉ (codiagonal-mapᵉ fᵉ) bᵉ
  fiber-codiagonal-map-suspension-fiberᵉ =
    cogap-suspension'ᵉ suspension-cocone-fiberᵉ

  is-equiv-fiber-codiagonal-map-suspension-fiberᵉ :
    is-equivᵉ fiber-codiagonal-map-suspension-fiberᵉ
  is-equiv-fiber-codiagonal-map-suspension-fiberᵉ =
    is-equiv-up-pushout-up-pushoutᵉ
      ( terminal-mapᵉ (fiberᵉ fᵉ bᵉ))
      ( terminal-mapᵉ (fiberᵉ fᵉ bᵉ))
      ( cocone-suspensionᵉ (fiberᵉ fᵉ bᵉ))
      ( suspension-cocone-fiberᵉ)
      ( cogap-suspension'ᵉ (suspension-cocone-fiberᵉ))
      ( htpy-cocone-map-universal-property-pushoutᵉ
        ( terminal-mapᵉ (fiberᵉ fᵉ bᵉ))
        ( terminal-mapᵉ (fiberᵉ fᵉ bᵉ))
        ( cocone-suspensionᵉ (fiberᵉ fᵉ bᵉ))
        ( up-suspension'ᵉ (fiberᵉ fᵉ bᵉ))
        ( suspension-cocone-fiberᵉ))
      ( up-suspension'ᵉ (fiberᵉ fᵉ bᵉ))
      ( universal-property-suspension-fiberᵉ)

  equiv-fiber-codiagonal-map-suspension-fiberᵉ :
    suspensionᵉ (fiberᵉ fᵉ bᵉ) ≃ᵉ fiberᵉ (codiagonal-mapᵉ fᵉ) bᵉ
  pr1ᵉ equiv-fiber-codiagonal-map-suspension-fiberᵉ =
    fiber-codiagonal-map-suspension-fiberᵉ
  pr2ᵉ equiv-fiber-codiagonal-map-suspension-fiberᵉ =
    is-equiv-fiber-codiagonal-map-suspension-fiberᵉ
```