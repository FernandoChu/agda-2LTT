# Quasicoherently idempotent maps

```agda
module foundation.quasicoherently-idempotent-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-typesᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.idempotent-mapsᵉ
open import foundation.identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-higher-homotopies-compositionᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.setsᵉ

open import synthetic-homotopy-theory.circleᵉ
open import synthetic-homotopy-theory.loop-homotopy-circleᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "quasicoherentlyᵉ idempotentᵉ map"ᵉ Disambiguation="onᵉ aᵉ type"ᵉ Agda=is-quasicoherently-idempotentᵉ}}
isᵉ aᵉ mapᵉ `fᵉ : Aᵉ → A`ᵉ [equipped](foundation.structure.mdᵉ) with aᵉ
[homotopy](foundation-core.homotopies.mdᵉ) `Iᵉ : fᵉ ∘ᵉ fᵉ ~ᵉ f`ᵉ witnessingᵉ thatᵉ `f`ᵉ isᵉ
[idempotent](foundation.idempotent-maps.md),ᵉ andᵉ aᵉ coherenceᵉ

```text
  fᵉ ·lᵉ Iᵉ ~ᵉ Iᵉ ·rᵉ f.ᵉ
```

Whileᵉ thisᵉ data isᵉ notᵉ enoughᵉ to captureᵉ aᵉ fullyᵉ coherentᵉ idempotentᵉ map,ᵉ itᵉ isᵉ
sufficientᵉ forᵉ showingᵉ thatᵉ `f`ᵉ canᵉ beᵉ madeᵉ to beᵉ fullyᵉ coherent.ᵉ Thisᵉ isᵉ in
contrastᵉ to [idempotentᵉ maps](foundation.idempotent-maps.md),ᵉ whichᵉ mayᵉ in
generalᵉ failᵉ to beᵉ coherent.ᵉ

**Terminology.**ᵉ Ourᵉ definitionᵉ ofᵉ aᵉ _quasicoherentlyᵉ idempotentᵉ mapᵉ_
correspondsᵉ to theᵉ definitionᵉ ofᵉ aᵉ _quasiidempotentᵉ mapᵉ_ in {{#citeᵉ Shu17ᵉ}} andᵉ
{{#citeᵉ Shu14SplittingIdempotents}}.ᵉ

## Definitions

### The structure of quasicoherent idempotence on maps

```agda
quasicoherence-is-idempotentᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (fᵉ : Aᵉ → Aᵉ) → fᵉ ∘ᵉ fᵉ ~ᵉ fᵉ → UUᵉ lᵉ
quasicoherence-is-idempotentᵉ fᵉ Iᵉ = fᵉ ·lᵉ Iᵉ ~ᵉ Iᵉ ·rᵉ fᵉ

is-quasicoherently-idempotentᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → (Aᵉ → Aᵉ) → UUᵉ lᵉ
is-quasicoherently-idempotentᵉ fᵉ =
  Σᵉ (fᵉ ∘ᵉ fᵉ ~ᵉ fᵉ) (quasicoherence-is-idempotentᵉ fᵉ)

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ : Aᵉ → Aᵉ} (Hᵉ : is-quasicoherently-idempotentᵉ fᵉ)
  where

  is-idempotent-is-quasicoherently-idempotentᵉ : is-idempotentᵉ fᵉ
  is-idempotent-is-quasicoherently-idempotentᵉ = pr1ᵉ Hᵉ

  coh-is-quasicoherently-idempotentᵉ :
    quasicoherence-is-idempotentᵉ fᵉ
      ( is-idempotent-is-quasicoherently-idempotentᵉ)
  coh-is-quasicoherently-idempotentᵉ = pr2ᵉ Hᵉ
```

### The type of quasicoherently idempotent maps

```agda
quasicoherently-idempotent-mapᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → UUᵉ lᵉ
quasicoherently-idempotent-mapᵉ Aᵉ = Σᵉ (Aᵉ → Aᵉ) (is-quasicoherently-idempotentᵉ)

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (Hᵉ : quasicoherently-idempotent-mapᵉ Aᵉ)
  where

  map-quasicoherently-idempotent-mapᵉ : Aᵉ → Aᵉ
  map-quasicoherently-idempotent-mapᵉ = pr1ᵉ Hᵉ

  is-quasicoherently-idempotent-quasicoherently-idempotent-mapᵉ :
    is-quasicoherently-idempotentᵉ map-quasicoherently-idempotent-mapᵉ
  is-quasicoherently-idempotent-quasicoherently-idempotent-mapᵉ = pr2ᵉ Hᵉ

  is-idempotent-quasicoherently-idempotent-mapᵉ :
    is-idempotentᵉ map-quasicoherently-idempotent-mapᵉ
  is-idempotent-quasicoherently-idempotent-mapᵉ =
    is-idempotent-is-quasicoherently-idempotentᵉ
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-mapᵉ)

  coh-quasicoherently-idempotent-mapᵉ :
    quasicoherence-is-idempotentᵉ
      ( map-quasicoherently-idempotent-mapᵉ)
      ( is-idempotent-quasicoherently-idempotent-mapᵉ)
  coh-quasicoherently-idempotent-mapᵉ =
    coh-is-quasicoherently-idempotentᵉ
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-mapᵉ)

  idempotent-map-quasicoherently-idempotent-mapᵉ : idempotent-mapᵉ Aᵉ
  idempotent-map-quasicoherently-idempotent-mapᵉ =
    ( map-quasicoherently-idempotent-mapᵉ ,ᵉ
      is-idempotent-quasicoherently-idempotent-mapᵉ)
```

## Properties

### The identity function is quasicoherently idempotent

Inᵉ fact,ᵉ anyᵉ idempotenceᵉ witnessᵉ ofᵉ theᵉ identityᵉ functionᵉ isᵉ quasicoherent.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (Hᵉ : is-idempotentᵉ (idᵉ {Aᵉ = Aᵉ}))
  where

  quasicoherence-is-idempotent-idᵉ :
    quasicoherence-is-idempotentᵉ idᵉ Hᵉ
  quasicoherence-is-idempotent-idᵉ = left-unit-law-left-whisker-compᵉ Hᵉ

  is-quasicoherently-idempotent-is-idempotent-idᵉ :
    is-quasicoherently-idempotentᵉ (idᵉ {Aᵉ = Aᵉ})
  is-quasicoherently-idempotent-is-idempotent-idᵉ =
    ( Hᵉ ,ᵉ quasicoherence-is-idempotent-idᵉ)

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-quasicoherently-idempotent-idᵉ :
    is-quasicoherently-idempotentᵉ (idᵉ {Aᵉ = Aᵉ})
  is-quasicoherently-idempotent-idᵉ =
    is-quasicoherently-idempotent-is-idempotent-idᵉ refl-htpyᵉ
```

### Being quasicoherently idempotent on a set is a property

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (is-set-Aᵉ : is-setᵉ Aᵉ) (fᵉ : Aᵉ → Aᵉ)
  where

  is-prop-quasicoherence-is-idempotent-is-setᵉ :
    (Iᵉ : fᵉ ∘ᵉ fᵉ ~ᵉ fᵉ) → is-propᵉ (quasicoherence-is-idempotentᵉ fᵉ Iᵉ)
  is-prop-quasicoherence-is-idempotent-is-setᵉ Iᵉ =
    is-prop-Πᵉ
      ( λ xᵉ →
        is-set-is-propᵉ
          ( is-set-Aᵉ ((fᵉ ∘ᵉ fᵉ ∘ᵉ fᵉ) xᵉ) ((fᵉ ∘ᵉ fᵉ) xᵉ))
          ( (fᵉ ·lᵉ Iᵉ) xᵉ)
          ( (Iᵉ ·rᵉ fᵉ) xᵉ))

  is-prop-is-quasicoherently-idempotent-is-setᵉ :
    is-propᵉ (is-quasicoherently-idempotentᵉ fᵉ)
  is-prop-is-quasicoherently-idempotent-is-setᵉ =
    is-prop-Σᵉ
      ( is-prop-is-idempotent-is-setᵉ is-set-Aᵉ fᵉ)
      ( is-prop-quasicoherence-is-idempotent-is-setᵉ)

  is-quasicoherently-idempotent-is-set-Propᵉ : Propᵉ lᵉ
  is-quasicoherently-idempotent-is-set-Propᵉ =
    ( is-quasicoherently-idempotentᵉ fᵉ ,ᵉ
      is-prop-is-quasicoherently-idempotent-is-setᵉ)

module _
  {lᵉ : Level} (Aᵉ : Setᵉ lᵉ) (fᵉ : type-Setᵉ Aᵉ → type-Setᵉ Aᵉ)
  where

  is-prop-is-quasicoherently-idempotent-Setᵉ :
    is-propᵉ (is-quasicoherently-idempotentᵉ fᵉ)
  is-prop-is-quasicoherently-idempotent-Setᵉ =
    is-prop-is-quasicoherently-idempotent-is-setᵉ (is-set-type-Setᵉ Aᵉ) fᵉ

  is-quasicoherently-idempotent-prop-Setᵉ : Propᵉ lᵉ
  is-quasicoherently-idempotent-prop-Setᵉ =
    ( is-quasicoherently-idempotentᵉ fᵉ ,ᵉ
      is-prop-is-quasicoherently-idempotent-Setᵉ)
```

### Being quasicoherently idempotent is generally not a property

Notᵉ evenᵉ forᵉ [1-types](foundation.1-types.mdᵉ): considerᵉ theᵉ identityᵉ functionᵉ onᵉ
theᵉ [circle](synthetic-homotopy-theory.circle.mdᵉ)

```text
  idᵉ : 𝕊¹ᵉ → 𝕊¹.ᵉ
```

Twoᵉ distinctᵉ witnessesᵉ thatᵉ itᵉ isᵉ idempotentᵉ areᵉ givenᵉ byᵉ `tᵉ ↦ᵉ refl`ᵉ andᵉ
`tᵉ ↦ᵉ loop`.ᵉ Bothᵉ ofᵉ theseᵉ areᵉ quasicoherent,ᵉ becauseᵉ

```text
  quasicoherence-is-idempotentᵉ idᵉ Iᵉ ≐ᵉ (idᵉ ·lᵉ Iᵉ ~ᵉ Iᵉ ·rᵉ idᵉ) ≃ᵉ (Iᵉ ~ᵉ I).ᵉ
```

```agda
is-not-prop-is-quasicoherently-idempotent-id-𝕊¹ᵉ :
  ¬ᵉ (is-propᵉ (is-quasicoherently-idempotentᵉ (idᵉ {Aᵉ = 𝕊¹ᵉ})))
is-not-prop-is-quasicoherently-idempotent-id-𝕊¹ᵉ Hᵉ =
  nonequal-Πᵉ
    ( loop-htpy-𝕊¹ᵉ)
    ( refl-htpyᵉ)
    ( base-𝕊¹ᵉ)
    ( is-not-refl-ev-base-loop-htpy-𝕊¹ᵉ)
    ( apᵉ pr1ᵉ
      ( eq-is-propᵉ Hᵉ
        { is-quasicoherently-idempotent-is-idempotent-idᵉ loop-htpy-𝕊¹ᵉ}
        { is-quasicoherently-idempotent-is-idempotent-idᵉ refl-htpyᵉ}))
```

### Idempotent maps on sets are quasicoherently idempotent

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (is-set-Aᵉ : is-setᵉ Aᵉ) {fᵉ : Aᵉ → Aᵉ}
  where

  is-quasicoherently-idempotent-is-idempotent-is-setᵉ :
    is-idempotentᵉ fᵉ → is-quasicoherently-idempotentᵉ fᵉ
  pr1ᵉ (is-quasicoherently-idempotent-is-idempotent-is-setᵉ Iᵉ) = Iᵉ
  pr2ᵉ (is-quasicoherently-idempotent-is-idempotent-is-setᵉ Iᵉ) xᵉ =
    eq-is-propᵉ (is-set-Aᵉ ((fᵉ ∘ᵉ fᵉ ∘ᵉ fᵉ) xᵉ) ((fᵉ ∘ᵉ fᵉ) xᵉ))
```

### If `i` and `r` form an inclusion-retraction pair, then `i ∘ r` is quasicoherently idempotent

Thisᵉ statementᵉ canᵉ beᵉ foundᵉ asᵉ partᵉ ofᵉ theᵉ proofᵉ ofᵉ Lemmaᵉ 3.6ᵉ in
{{#citeᵉ Shu17}}.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (iᵉ : Bᵉ → Aᵉ) (rᵉ : Aᵉ → Bᵉ) (Hᵉ : is-retractionᵉ iᵉ rᵉ)
  where

  quasicoherence-is-idempotent-inclusion-retractionᵉ :
    quasicoherence-is-idempotentᵉ
      ( iᵉ ∘ᵉ rᵉ)
      ( is-idempotent-inclusion-retractionᵉ iᵉ rᵉ Hᵉ)
  quasicoherence-is-idempotent-inclusion-retractionᵉ =
    ( inv-preserves-comp-left-whisker-compᵉ iᵉ rᵉ (iᵉ ·lᵉ Hᵉ ·rᵉ rᵉ)) ∙hᵉ
    ( double-whisker-comp²ᵉ
      ( iᵉ)
      ( preserves-comp-left-whisker-compᵉ rᵉ iᵉ Hᵉ ∙hᵉ inv-coh-htpy-idᵉ Hᵉ)
      ( rᵉ))

  is-quasicoherently-idempotent-inclusion-retractionᵉ :
    is-quasicoherently-idempotentᵉ (iᵉ ∘ᵉ rᵉ)
  is-quasicoherently-idempotent-inclusion-retractionᵉ =
    ( is-idempotent-inclusion-retractionᵉ iᵉ rᵉ Hᵉ ,ᵉ
      quasicoherence-is-idempotent-inclusion-retractionᵉ)
```

### Quasicoherent idempotence is preserved by homotopies

Thisᵉ factᵉ doesᵉ notᵉ explicitlyᵉ appearᵉ in {{#citeᵉ Shu17ᵉ}} althoughᵉ itᵉ isᵉ
implicitlyᵉ usedᵉ in Lemmaᵉ 3.6.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ gᵉ : Aᵉ → Aᵉ} (Fᵉ : is-quasicoherently-idempotentᵉ fᵉ)
  where

  abstract
    quasicoherence-is-idempotent-htpyᵉ :
      (Hᵉ : gᵉ ~ᵉ fᵉ) →
      quasicoherence-is-idempotentᵉ gᵉ
        ( is-idempotent-htpyᵉ
          ( is-idempotent-is-quasicoherently-idempotentᵉ Fᵉ)
          ( Hᵉ))
    quasicoherence-is-idempotent-htpyᵉ Hᵉ =
      homotopy-reasoningᵉ
      ( gᵉ ·lᵉ is-idempotent-htpyᵉ Iᵉ Hᵉ)
      ~ᵉ ( Hᵉ ·rᵉ (gᵉ ∘ᵉ gᵉ)) ∙hᵉ
        ( fᵉ ·lᵉ (gᵉ ·lᵉ Hᵉ ∙hᵉ Hᵉ ·rᵉ fᵉ ∙hᵉ Iᵉ ∙hᵉ inv-htpyᵉ Hᵉ)) ∙hᵉ
        ( inv-htpyᵉ (Hᵉ ·rᵉ gᵉ))
      byᵉ
      ( right-transpose-htpy-concatᵉ
        ( gᵉ ·lᵉ is-idempotent-htpyᵉ Iᵉ Hᵉ)
        ( Hᵉ ·rᵉ gᵉ)
        ( Hᵉ ·rᵉ (gᵉ ∘ᵉ gᵉ) ∙hᵉ (fᵉ ·lᵉ (gᵉ ·lᵉ Hᵉ ∙hᵉ Hᵉ ·rᵉ fᵉ ∙hᵉ Iᵉ ∙hᵉ inv-htpyᵉ Hᵉ)))
        ( inv-htpyᵉ (nat-htpyᵉ Hᵉ ∘ᵉ (gᵉ ·lᵉ Hᵉ ∙hᵉ Hᵉ ·rᵉ fᵉ ∙hᵉ Iᵉ ∙hᵉ inv-htpyᵉ Hᵉ))))
      ~ᵉ gᵉ ·lᵉ Hᵉ ·rᵉ gᵉ ∙hᵉ Hᵉ ·rᵉ (fᵉ ∘ᵉ gᵉ) ∙hᵉ Iᵉ ·rᵉ gᵉ ∙hᵉ inv-htpyᵉ (Hᵉ ·rᵉ gᵉ)
      byᵉ
      ( ap-concat-htpy'ᵉ
        ( inv-htpyᵉ (Hᵉ ·rᵉ gᵉ))
        ( ( ap-concat-htpyᵉ
            ( Hᵉ ·rᵉ ((gᵉ ∘ᵉ gᵉ)))
            ( ( distributive-left-whisker-comp-concatᵉ fᵉ
                ( gᵉ ·lᵉ Hᵉ ∙hᵉ Hᵉ ·rᵉ fᵉ ∙hᵉ Iᵉ)
                ( inv-htpyᵉ Hᵉ)) ∙hᵉ
              ( ap-concat-htpy'ᵉ
                ( fᵉ ·lᵉ inv-htpyᵉ Hᵉ)
                ( ( distributive-left-whisker-comp-concatᵉ fᵉ
                    ( gᵉ ·lᵉ Hᵉ ∙hᵉ Hᵉ ·rᵉ fᵉ)
                    ( Iᵉ)) ∙hᵉ
                  ( ap-binary-concat-htpyᵉ
                    ( distributive-left-whisker-comp-concatᵉ fᵉ (gᵉ ·lᵉ Hᵉ) (Hᵉ ·rᵉ fᵉ))
                    ( coh-is-quasicoherently-idempotentᵉ Fᵉ)))) ∙hᵉ
              ( assoc-htpyᵉ
                ( fᵉ ·lᵉ gᵉ ·lᵉ Hᵉ ∙hᵉ fᵉ ·lᵉ Hᵉ ·rᵉ fᵉ)
                ( Iᵉ ·rᵉ fᵉ)
                ( fᵉ ·lᵉ inv-htpyᵉ Hᵉ)) ∙hᵉ
              ( ap-concat-htpyᵉ
                ( fᵉ ·lᵉ gᵉ ·lᵉ Hᵉ ∙hᵉ fᵉ ·lᵉ Hᵉ ·rᵉ fᵉ)
                ( nat-htpyᵉ Iᵉ ∘ᵉ inv-htpyᵉ Hᵉ)) ∙hᵉ
              ( inv-htpyᵉ
                ( assoc-htpyᵉ
                  ( fᵉ ·lᵉ gᵉ ·lᵉ Hᵉ ∙hᵉ fᵉ ·lᵉ Hᵉ ·rᵉ fᵉ)
                  ( (fᵉ ∘ᵉ fᵉ) ·lᵉ inv-htpyᵉ Hᵉ)
                  ( Iᵉ ·rᵉ gᵉ))))) ∙hᵉ
          ( inv-htpyᵉ
            ( assoc-htpyᵉ
              ( Hᵉ ·rᵉ (gᵉ ∘ᵉ gᵉ))
              ( fᵉ ·lᵉ gᵉ ·lᵉ Hᵉ ∙hᵉ fᵉ ·lᵉ Hᵉ ·rᵉ fᵉ ∙hᵉ (fᵉ ∘ᵉ fᵉ) ·lᵉ inv-htpyᵉ Hᵉ)
              ( Iᵉ ·rᵉ gᵉ))) ∙hᵉ
          ( ap-concat-htpy'ᵉ
            ( Iᵉ ·rᵉ gᵉ)
            ( ( ap-concat-htpyᵉ
                ( Hᵉ ·rᵉ (gᵉ ∘ᵉ gᵉ))
                ( ap-concat-htpy'ᵉ
                  ( (fᵉ ∘ᵉ fᵉ) ·lᵉ inv-htpyᵉ Hᵉ)
                  ( ( ap-concat-htpy'ᵉ
                      ( fᵉ ·lᵉ Hᵉ ·rᵉ fᵉ)
                      ( preserves-comp-left-whisker-compᵉ fᵉ gᵉ Hᵉ)) ∙hᵉ
                    ( inv-htpyᵉ (nat-htpyᵉ (fᵉ ·lᵉ Hᵉ) ∘ᵉ Hᵉ))) ∙hᵉ
                  ( ap-concat-htpyᵉ
                    ( fᵉ ·lᵉ Hᵉ ·rᵉ gᵉ ∙hᵉ (fᵉ ∘ᵉ fᵉ) ·lᵉ Hᵉ)
                    ( left-whisker-inv-htpyᵉ (fᵉ ∘ᵉ fᵉ) Hᵉ)) ∙hᵉ
                  ( is-retraction-inv-concat-htpy'ᵉ
                    ( (fᵉ ∘ᵉ fᵉ) ·lᵉ Hᵉ)
                    ( fᵉ ·lᵉ Hᵉ ·rᵉ gᵉ)))) ∙hᵉ
              ( nat-htpyᵉ Hᵉ ∘ᵉ (Hᵉ ·rᵉ gᵉ))))))
      where
        Iᵉ : is-idempotentᵉ fᵉ
        Iᵉ = is-idempotent-is-quasicoherently-idempotentᵉ Fᵉ

  is-quasicoherently-idempotent-htpyᵉ :
    gᵉ ~ᵉ fᵉ → is-quasicoherently-idempotentᵉ gᵉ
  pr1ᵉ (is-quasicoherently-idempotent-htpyᵉ Hᵉ) =
    is-idempotent-htpyᵉ
      ( is-idempotent-is-quasicoherently-idempotentᵉ Fᵉ)
      ( Hᵉ)
  pr2ᵉ (is-quasicoherently-idempotent-htpyᵉ Hᵉ) =
    quasicoherence-is-idempotent-htpyᵉ Hᵉ

  is-quasicoherently-idempotent-inv-htpyᵉ :
    fᵉ ~ᵉ gᵉ → is-quasicoherently-idempotentᵉ gᵉ
  pr1ᵉ (is-quasicoherently-idempotent-inv-htpyᵉ Hᵉ) =
    is-idempotent-htpyᵉ
      ( is-idempotent-is-quasicoherently-idempotentᵉ Fᵉ)
      ( inv-htpyᵉ Hᵉ)
  pr2ᵉ (is-quasicoherently-idempotent-inv-htpyᵉ Hᵉ) =
    quasicoherence-is-idempotent-htpyᵉ (inv-htpyᵉ Hᵉ)
```

### Realigning the coherence of a quasicoherent idempotence proof

Givenᵉ aᵉ quasicoherentlyᵉ idempotentᵉ mapᵉ `f`,ᵉ anyᵉ otherᵉ idempotenceᵉ homotopyᵉ
`Iᵉ : fᵉ ∘ᵉ fᵉ ~ᵉ f`ᵉ thatᵉ isᵉ homotopicᵉ to theᵉ coherentᵉ oneᵉ isᵉ alsoᵉ coherent.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ : Aᵉ → Aᵉ}
  (Fᵉ : is-quasicoherently-idempotentᵉ fᵉ)
  (Iᵉ : fᵉ ∘ᵉ fᵉ ~ᵉ fᵉ)
  where

  quasicoherence-is-idempotent-is-idempotent-htpyᵉ :
    is-idempotent-is-quasicoherently-idempotentᵉ Fᵉ ~ᵉ Iᵉ →
    quasicoherence-is-idempotentᵉ fᵉ Iᵉ
  quasicoherence-is-idempotent-is-idempotent-htpyᵉ αᵉ =
    ( left-whisker-comp²ᵉ fᵉ (inv-htpyᵉ αᵉ)) ∙hᵉ
    ( coh-is-quasicoherently-idempotentᵉ Fᵉ) ∙hᵉ
    ( right-whisker-comp²ᵉ αᵉ fᵉ)

  quasicoherence-is-idempotent-is-idempotent-inv-htpyᵉ :
    Iᵉ ~ᵉ is-idempotent-is-quasicoherently-idempotentᵉ Fᵉ →
    quasicoherence-is-idempotentᵉ fᵉ Iᵉ
  quasicoherence-is-idempotent-is-idempotent-inv-htpyᵉ αᵉ =
    ( left-whisker-comp²ᵉ fᵉ αᵉ) ∙hᵉ
    ( coh-is-quasicoherently-idempotentᵉ Fᵉ) ∙hᵉ
    ( right-whisker-comp²ᵉ (inv-htpyᵉ αᵉ) fᵉ)

  is-quasicoherently-idempotent-is-idempotent-htpyᵉ :
    is-idempotent-is-quasicoherently-idempotentᵉ Fᵉ ~ᵉ Iᵉ →
    is-quasicoherently-idempotentᵉ fᵉ
  is-quasicoherently-idempotent-is-idempotent-htpyᵉ αᵉ =
    ( Iᵉ ,ᵉ quasicoherence-is-idempotent-is-idempotent-htpyᵉ αᵉ)

  is-quasicoherently-idempotent-is-idempotent-inv-htpyᵉ :
    Iᵉ ~ᵉ is-idempotent-is-quasicoherently-idempotentᵉ Fᵉ →
    is-quasicoherently-idempotentᵉ fᵉ
  is-quasicoherently-idempotent-is-idempotent-inv-htpyᵉ αᵉ =
    ( Iᵉ ,ᵉ quasicoherence-is-idempotent-is-idempotent-inv-htpyᵉ αᵉ)
```

### Not every idempotent map is quasicoherently idempotent

Toᵉ beᵉ clear,ᵉ whatᵉ weᵉ areᵉ askingᵉ forᵉ isᵉ anᵉ idempotentᵉ mapᵉ `f`,ᵉ suchᵉ thatᵉ _noᵉ_
idempotenceᵉ homotopyᵉ `fᵉ ∘ᵉ fᵉ ~ᵉ f`ᵉ isᵉ quasicoherent.ᵉ Aᵉ counterexampleᵉ canᵉ beᵉ
constructedᵉ using theᵉ [cantorᵉ space](set-theory.cantor-space.md),ᵉ seeᵉ Sectionᵉ 4
ofᵉ {{#citeᵉ Shu17ᵉ}} forᵉ moreᵉ details.ᵉ

## See also

-ᵉ Inᵉ [`foundation.split-idempotent-maps`](foundation.split-idempotent-maps.mdᵉ)
  weᵉ showᵉ thatᵉ everyᵉ quasicoherentlyᵉ idempotentᵉ mapᵉ splits.ᵉ Moreover,ᵉ itᵉ isᵉ trueᵉ
  thatᵉ splitᵉ idempotentᵉ mapsᵉ areᵉ aᵉ retractᵉ ofᵉ quasicoherentᵉ idempotentᵉ maps.ᵉ

## References

{{#bibliographyᵉ}} {{#referenceᵉ Shu17ᵉ}} {{#referenceᵉ Shu14SplittingIdempotentsᵉ}}