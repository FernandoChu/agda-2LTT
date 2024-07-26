# Epimorphisms

```agda
module foundation.epimorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.sectionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.codiagonals-of-mapsᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ saidᵉ to beᵉ anᵉ **epimorphism**ᵉ ifᵉ theᵉ precompositionᵉ
functionᵉ

```text
  -ᵉ ∘ᵉ fᵉ : (Bᵉ → Xᵉ) → (Aᵉ → Xᵉ)
```

isᵉ anᵉ [embedding](foundation-core.embeddings.mdᵉ) forᵉ everyᵉ typeᵉ `X`.ᵉ

## Definitions

### Epimorphisms with respect to a specified universe

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-epimorphism-Levelᵉ : (lᵉ : Level) → (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
  is-epimorphism-Levelᵉ lᵉ fᵉ = (Xᵉ : UUᵉ lᵉ) → is-embᵉ (precompᵉ fᵉ Xᵉ)
```

### Epimorphisms

```agda
  is-epimorphismᵉ : (Aᵉ → Bᵉ) → UUωᵉ
  is-epimorphismᵉ fᵉ = {lᵉ : Level} → is-epimorphism-Levelᵉ lᵉ fᵉ
```

## Properties

### The codiagonal of an epimorphism is an equivalence

Ifᵉ theᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ epi,ᵉ thenᵉ theᵉ commutativeᵉ squareᵉ

```text
        fᵉ
    Aᵉ ----->ᵉ Bᵉ
    |        |
  fᵉ |        | idᵉ
    ∨ᵉ      ⌜ᵉ ∨ᵉ
    Bᵉ ----->ᵉ Bᵉ
        idᵉ
```

isᵉ aᵉ pushoutᵉ square.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Xᵉ : UUᵉ l3ᵉ)
  where

  is-equiv-diagonal-into-fibers-precomp-is-epimorphismᵉ :
    is-epimorphismᵉ fᵉ → is-equivᵉ (diagonal-into-fibers-precompᵉ fᵉ Xᵉ)
  is-equiv-diagonal-into-fibers-precomp-is-epimorphismᵉ eᵉ =
    is-equiv-map-section-familyᵉ
      ( λ gᵉ → (gᵉ ,ᵉ reflᵉ))
      ( λ gᵉ →
        is-proof-irrelevant-is-propᵉ
          ( is-prop-map-is-embᵉ (eᵉ Xᵉ) (gᵉ ∘ᵉ fᵉ))
          ( gᵉ ,ᵉ reflᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  universal-property-pushout-is-epimorphismᵉ :
    is-epimorphismᵉ fᵉ →
    universal-property-pushoutᵉ fᵉ fᵉ (cocone-codiagonal-mapᵉ fᵉ)
  universal-property-pushout-is-epimorphismᵉ eᵉ Xᵉ =
    is-equiv-compᵉ
      ( map-equivᵉ (compute-total-fiber-precompᵉ fᵉ Xᵉ))
      ( diagonal-into-fibers-precompᵉ fᵉ Xᵉ)
      ( is-equiv-diagonal-into-fibers-precomp-is-epimorphismᵉ fᵉ Xᵉ eᵉ)
      ( is-equiv-map-equivᵉ (compute-total-fiber-precompᵉ fᵉ Xᵉ))
```

Ifᵉ theᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ epi,ᵉ thenᵉ itsᵉ codiagonalᵉ isᵉ anᵉ equivalence.ᵉ

```agda
  is-equiv-codiagonal-map-is-epimorphismᵉ :
    is-epimorphismᵉ fᵉ → is-equivᵉ (codiagonal-mapᵉ fᵉ)
  is-equiv-codiagonal-map-is-epimorphismᵉ eᵉ =
    is-equiv-up-pushout-up-pushoutᵉ fᵉ fᵉ
      ( cocone-pushoutᵉ fᵉ fᵉ)
      ( cocone-codiagonal-mapᵉ fᵉ)
      ( codiagonal-mapᵉ fᵉ)
      ( compute-inl-codiagonal-mapᵉ fᵉ ,ᵉ
        compute-inr-codiagonal-mapᵉ fᵉ ,ᵉ
        compute-glue-codiagonal-mapᵉ fᵉ)
      ( up-pushoutᵉ fᵉ fᵉ)
      ( universal-property-pushout-is-epimorphismᵉ eᵉ)

  is-pushout-is-epimorphismᵉ :
    is-epimorphismᵉ fᵉ → is-pushoutᵉ fᵉ fᵉ (cocone-codiagonal-mapᵉ fᵉ)
  is-pushout-is-epimorphismᵉ = is-equiv-codiagonal-map-is-epimorphismᵉ
```

### A map is an epimorphism if its codiagonal is an equivalence

```agda
  is-epimorphism-universal-property-pushout-Levelᵉ :
    {lᵉ : Level} →
    universal-property-pushout-Levelᵉ lᵉ fᵉ fᵉ (cocone-codiagonal-mapᵉ fᵉ) →
    is-epimorphism-Levelᵉ lᵉ fᵉ
  is-epimorphism-universal-property-pushout-Levelᵉ up-cᵉ Xᵉ =
    is-emb-is-contr-fibers-valuesᵉ
      ( precompᵉ fᵉ Xᵉ)
      ( λ gᵉ →
        is-contr-equivᵉ
          ( Σᵉ (Bᵉ → Xᵉ) (λ hᵉ → coherence-square-mapsᵉ fᵉ fᵉ hᵉ gᵉ))
          ( compute-fiber-precompᵉ fᵉ Xᵉ gᵉ)
          ( is-contr-fam-is-equiv-map-section-familyᵉ
            ( λ hᵉ →
              ( vertical-map-coconeᵉ fᵉ fᵉ
                ( cocone-mapᵉ fᵉ fᵉ (cocone-codiagonal-mapᵉ fᵉ) hᵉ)) ,ᵉ
              ( coherence-square-coconeᵉ fᵉ fᵉ
                ( cocone-mapᵉ fᵉ fᵉ (cocone-codiagonal-mapᵉ fᵉ) hᵉ)))
            ( up-cᵉ Xᵉ)
            ( gᵉ)))

  is-epimorphism-universal-property-pushoutᵉ :
    universal-property-pushoutᵉ fᵉ fᵉ (cocone-codiagonal-mapᵉ fᵉ) →
    is-epimorphismᵉ fᵉ
  is-epimorphism-universal-property-pushoutᵉ up-cᵉ =
    is-epimorphism-universal-property-pushout-Levelᵉ up-cᵉ

  is-epimorphism-is-equiv-codiagonal-mapᵉ :
    is-equivᵉ (codiagonal-mapᵉ fᵉ) → is-epimorphismᵉ fᵉ
  is-epimorphism-is-equiv-codiagonal-mapᵉ eᵉ =
    is-epimorphism-universal-property-pushoutᵉ
      ( up-pushout-up-pushout-is-equivᵉ fᵉ fᵉ
        ( cocone-pushoutᵉ fᵉ fᵉ)
        ( cocone-codiagonal-mapᵉ fᵉ)
        ( codiagonal-mapᵉ fᵉ)
        ( htpy-cocone-map-universal-property-pushoutᵉ fᵉ fᵉ
          ( cocone-pushoutᵉ fᵉ fᵉ)
          ( up-pushoutᵉ fᵉ fᵉ)
          ( cocone-codiagonal-mapᵉ fᵉ))
        ( eᵉ)
        ( up-pushoutᵉ fᵉ fᵉ))

  is-epimorphism-is-pushoutᵉ :
    is-pushoutᵉ fᵉ fᵉ (cocone-codiagonal-mapᵉ fᵉ) → is-epimorphismᵉ fᵉ
  is-epimorphism-is-pushoutᵉ = is-epimorphism-is-equiv-codiagonal-mapᵉ
```

### The class of epimorphisms is closed under composition and has the right cancellation property

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ)
  where

  is-epimorphism-compᵉ :
    is-epimorphismᵉ gᵉ → is-epimorphismᵉ fᵉ → is-epimorphismᵉ (gᵉ ∘ᵉ fᵉ)
  is-epimorphism-compᵉ egᵉ efᵉ Xᵉ =
    is-emb-compᵉ (precompᵉ fᵉ Xᵉ) (precompᵉ gᵉ Xᵉ) (efᵉ Xᵉ) (egᵉ Xᵉ)

  is-epimorphism-left-factorᵉ :
    is-epimorphismᵉ (gᵉ ∘ᵉ fᵉ) → is-epimorphismᵉ fᵉ → is-epimorphismᵉ gᵉ
  is-epimorphism-left-factorᵉ ecᵉ efᵉ Xᵉ =
    is-emb-right-factorᵉ (precompᵉ fᵉ Xᵉ) (precompᵉ gᵉ Xᵉ) (efᵉ Xᵉ) (ecᵉ Xᵉ)
```

## See also

-ᵉ [Acyclicᵉ maps](synthetic-homotopy-theory.acyclic-maps.mdᵉ)
-ᵉ [Dependentᵉ epimorphisms](foundation.dependent-epimorphisms.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to sets](foundation.epimorphisms-with-respect-to-sets.mdᵉ)
-ᵉ [Epimorphismsᵉ with respectᵉ to truncatedᵉ types](foundation.epimorphisms-with-respect-to-truncated-types.mdᵉ)