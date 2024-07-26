# Split idempotent maps

```agda
module foundation.split-idempotent-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-higher-identifications-functionsᵉ
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fixed-points-endofunctionsᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.idempotent-mapsᵉ
open import foundation.inverse-sequential-diagramsᵉ
open import foundation.path-algebraᵉ
open import foundation.quasicoherently-idempotent-mapsᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.sequential-limitsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
open import foundation.weakly-constant-mapsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-homotopiesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.small-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Anᵉ endomapᵉ `fᵉ : Aᵉ → A`ᵉ isᵉ
{{#conceptᵉ "splitᵉ idempotent"ᵉ Disambiguation="mapᵉ ofᵉ types"ᵉ Agda=is-split-idempotentᵉ}}
ifᵉ thereᵉ isᵉ aᵉ typeᵉ `B`ᵉ andᵉ anᵉ inclusion-retractionᵉ pairᵉ `iᵉ ,ᵉ r`ᵉ displayingᵉ `B`ᵉ
asᵉ aᵉ [retract](foundation-core.retracts-of-types.mdᵉ) ofᵉ `A`,ᵉ andᵉ suchᵉ thatᵉ
`Hᵉ : iᵉ ∘ᵉ rᵉ ~ᵉ f`.ᵉ Inᵉ otherᵉ words,ᵉ ifᵉ weᵉ haveᵉ aᵉ commutativeᵉ diagramᵉ

```text
           fᵉ
       Aᵉ ---->ᵉ Aᵉ
      ∧ᵉ \ᵉ     ∧ᵉ
   iᵉ /ᵉ   \rᵉ  /ᵉ iᵉ
    /ᵉ     ∨ᵉ /ᵉ
  Bᵉ ======ᵉ B.ᵉ
```

Observeᵉ thatᵉ splitᵉ idempotentᵉ mapsᵉ areᵉ indeedᵉ
[idempotent](foundation.idempotent-maps.md),ᵉ asᵉ witnessedᵉ byᵉ theᵉ compositeᵉ

```text
       (H◽H)⁻¹ᵉ            iRrᵉ        Hᵉ
  fᵉ ∘ᵉ fᵉ  ~ᵉ  iᵉ ∘ᵉ rᵉ ∘ᵉ iᵉ ∘ᵉ rᵉ  ~ᵉ  iᵉ ∘ᵉ rᵉ  ~ᵉ  fᵉ
```

where `Hᵉ : iᵉ ∘ᵉ rᵉ ~ᵉ f`ᵉ andᵉ `Rᵉ : rᵉ ∘ᵉ iᵉ ~ᵉ id`.ᵉ

Oneᵉ importantᵉ factᵉ aboutᵉ splitᵉ idempotentᵉ mapsᵉ isᵉ thatᵉ everyᵉ
[quasicoherentlyᵉ idempotentᵉ map](foundation.quasicoherently-idempotent-maps.mdᵉ)
splits,ᵉ andᵉ conversely,ᵉ everyᵉ splitᵉ idempotentᵉ mapᵉ isᵉ quasicoherentlyᵉ
idempotent.ᵉ Inᵉ fact,ᵉ theᵉ typeᵉ ofᵉ proofsᵉ ofᵉ splitᵉ idempotenceᵉ forᵉ anᵉ endomapᵉ `f`ᵉ
isᵉ aᵉ retractᵉ ofᵉ theᵉ typeᵉ ofᵉ proofsᵉ ofᵉ quasicoherentᵉ idempotence.ᵉ

## Definitions

### The structure on a map of being split idempotent

```agda
is-split-idempotentᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) {Aᵉ : UUᵉ l1ᵉ} → (Aᵉ → Aᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
is-split-idempotentᵉ l2ᵉ {Aᵉ} fᵉ =
  Σᵉ ( UUᵉ l2ᵉ)
    ( λ Bᵉ →
      Σᵉ ( Bᵉ retract-ofᵉ Aᵉ)
        ( λ Rᵉ → inclusion-retractᵉ Rᵉ ∘ᵉ map-retraction-retractᵉ Rᵉ ~ᵉ fᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {fᵉ : Aᵉ → Aᵉ} (Hᵉ : is-split-idempotentᵉ l2ᵉ fᵉ)
  where

  splitting-type-is-split-idempotentᵉ : UUᵉ l2ᵉ
  splitting-type-is-split-idempotentᵉ = pr1ᵉ Hᵉ

  retract-is-split-idempotentᵉ :
    splitting-type-is-split-idempotentᵉ retract-ofᵉ Aᵉ
  retract-is-split-idempotentᵉ = pr1ᵉ (pr2ᵉ Hᵉ)

  inclusion-is-split-idempotentᵉ : splitting-type-is-split-idempotentᵉ → Aᵉ
  inclusion-is-split-idempotentᵉ =
    inclusion-retractᵉ retract-is-split-idempotentᵉ

  map-retraction-is-split-idempotentᵉ :
    Aᵉ → splitting-type-is-split-idempotentᵉ
  map-retraction-is-split-idempotentᵉ =
    map-retraction-retractᵉ retract-is-split-idempotentᵉ

  retraction-is-split-idempotentᵉ :
    retractionᵉ inclusion-is-split-idempotentᵉ
  retraction-is-split-idempotentᵉ =
    retraction-retractᵉ retract-is-split-idempotentᵉ

  is-retraction-map-retraction-is-split-idempotentᵉ :
    is-retractionᵉ
      ( inclusion-is-split-idempotentᵉ)
      ( map-retraction-is-split-idempotentᵉ)
  is-retraction-map-retraction-is-split-idempotentᵉ =
    is-retraction-map-retraction-retractᵉ retract-is-split-idempotentᵉ

  htpy-is-split-idempotentᵉ :
    inclusion-is-split-idempotentᵉ ∘ᵉ map-retraction-is-split-idempotentᵉ ~ᵉ
    fᵉ
  htpy-is-split-idempotentᵉ = pr2ᵉ (pr2ᵉ Hᵉ)
```

### The type of split idempotent maps on a type

```agda
split-idempotent-mapᵉ : {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
split-idempotent-mapᵉ l2ᵉ Aᵉ = Σᵉ (Aᵉ → Aᵉ) (is-split-idempotentᵉ l2ᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Hᵉ : split-idempotent-mapᵉ l2ᵉ Aᵉ)
  where

  map-split-idempotent-mapᵉ : Aᵉ → Aᵉ
  map-split-idempotent-mapᵉ = pr1ᵉ Hᵉ

  is-split-idempotent-split-idempotent-mapᵉ :
    is-split-idempotentᵉ l2ᵉ map-split-idempotent-mapᵉ
  is-split-idempotent-split-idempotent-mapᵉ = pr2ᵉ Hᵉ

  splitting-type-split-idempotent-mapᵉ : UUᵉ l2ᵉ
  splitting-type-split-idempotent-mapᵉ =
    splitting-type-is-split-idempotentᵉ
      ( is-split-idempotent-split-idempotent-mapᵉ)

  retract-split-idempotent-mapᵉ :
    splitting-type-split-idempotent-mapᵉ retract-ofᵉ Aᵉ
  retract-split-idempotent-mapᵉ =
    retract-is-split-idempotentᵉ is-split-idempotent-split-idempotent-mapᵉ

  inclusion-split-idempotent-mapᵉ : splitting-type-split-idempotent-mapᵉ → Aᵉ
  inclusion-split-idempotent-mapᵉ =
    inclusion-is-split-idempotentᵉ is-split-idempotent-split-idempotent-mapᵉ

  map-retraction-split-idempotent-mapᵉ : Aᵉ → splitting-type-split-idempotent-mapᵉ
  map-retraction-split-idempotent-mapᵉ =
    map-retraction-is-split-idempotentᵉ
      ( is-split-idempotent-split-idempotent-mapᵉ)

  retraction-split-idempotent-mapᵉ : retractionᵉ inclusion-split-idempotent-mapᵉ
  retraction-split-idempotent-mapᵉ =
    retraction-is-split-idempotentᵉ is-split-idempotent-split-idempotent-mapᵉ

  is-retraction-map-retraction-split-idempotent-mapᵉ :
    is-retractionᵉ
      ( inclusion-split-idempotent-mapᵉ)
      ( map-retraction-split-idempotent-mapᵉ)
  is-retraction-map-retraction-split-idempotent-mapᵉ =
    is-retraction-map-retraction-is-split-idempotentᵉ
      ( is-split-idempotent-split-idempotent-mapᵉ)

  htpy-split-idempotent-mapᵉ :
    inclusion-split-idempotent-mapᵉ ∘ᵉ map-retraction-split-idempotent-mapᵉ ~ᵉ
    map-split-idempotent-mapᵉ
  htpy-split-idempotent-mapᵉ =
    htpy-is-split-idempotentᵉ is-split-idempotent-split-idempotent-mapᵉ
```

## Properties

### Split idempotence is closed under homotopies of functions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {fᵉ gᵉ : Aᵉ → Aᵉ}
  (Hᵉ : fᵉ ~ᵉ gᵉ)
  (Sᵉ : is-split-idempotentᵉ l3ᵉ fᵉ)
  where

  is-split-idempotent-htpyᵉ : is-split-idempotentᵉ l3ᵉ gᵉ
  is-split-idempotent-htpyᵉ =
    ( splitting-type-is-split-idempotentᵉ Sᵉ ,ᵉ
      retract-is-split-idempotentᵉ Sᵉ ,ᵉ
      htpy-is-split-idempotentᵉ Sᵉ ∙hᵉ Hᵉ)
```

### Split idempotence is closed under equivalences of splitting types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Aᵉ}
  (Hᵉ : is-split-idempotentᵉ l3ᵉ fᵉ)
  (eᵉ : Bᵉ ≃ᵉ splitting-type-is-split-idempotentᵉ Hᵉ)
  where

  inclusion-is-split-idempotent-equiv-splitting-typeᵉ : Bᵉ → Aᵉ
  inclusion-is-split-idempotent-equiv-splitting-typeᵉ =
    inclusion-is-split-idempotentᵉ Hᵉ ∘ᵉ map-equivᵉ eᵉ

  map-retraction-is-split-idempotent-equiv-splitting-typeᵉ : Aᵉ → Bᵉ
  map-retraction-is-split-idempotent-equiv-splitting-typeᵉ =
    map-inv-equivᵉ eᵉ ∘ᵉ map-retraction-is-split-idempotentᵉ Hᵉ

  htpy-is-split-idempotent-equiv-splitting-typeᵉ :
    inclusion-is-split-idempotent-equiv-splitting-typeᵉ ∘ᵉ
    map-retraction-is-split-idempotent-equiv-splitting-typeᵉ ~ᵉ
    fᵉ
  htpy-is-split-idempotent-equiv-splitting-typeᵉ =
    ( double-whisker-compᵉ
      ( inclusion-is-split-idempotentᵉ Hᵉ)
      ( is-section-map-section-map-equivᵉ eᵉ)
      ( map-retraction-is-split-idempotentᵉ Hᵉ)) ∙hᵉ
    ( htpy-is-split-idempotentᵉ Hᵉ)

  is-split-idempotent-equiv-splitting-typeᵉ :
    is-split-idempotentᵉ l2ᵉ fᵉ
  is-split-idempotent-equiv-splitting-typeᵉ =
    ( Bᵉ ,ᵉ
      comp-retractᵉ (retract-is-split-idempotentᵉ Hᵉ) (retract-equivᵉ eᵉ) ,ᵉ
      htpy-is-split-idempotent-equiv-splitting-typeᵉ)
```

### The splitting type of a split idempotent map is essentially unique

Thisᵉ isᵉ Lemmaᵉ 3.4ᵉ in {{#citeᵉ Shu17}}.ᵉ Noteᵉ thatᵉ itᵉ doesᵉ notᵉ requireᵉ anyᵉ
postulates.ᵉ

**Proof.**ᵉ Givenᵉ twoᵉ splittingsᵉ ofᵉ anᵉ endomapᵉ `fᵉ : Aᵉ → A`,ᵉ with
inclusion-retractionᵉ pairsᵉ `iᵉ ,ᵉ r`ᵉ andᵉ `i'ᵉ ,ᵉ r'`,ᵉ weᵉ getᵉ mutualᵉ inverseᵉ mapsᵉ
betweenᵉ theᵉ splittingᵉ typesᵉ

```text
  r'ᵉ ∘ᵉ iᵉ : Bᵉ → B'ᵉ    andᵉ    rᵉ ∘ᵉ i'ᵉ : B'ᵉ → B.ᵉ
```

Theᵉ computationᵉ thatᵉ theyᵉ formᵉ mutualᵉ inversesᵉ isᵉ straightforwardᵉ:

```text
                   rR'iᵉ        Rᵉ
  rᵉ ∘ᵉ i'ᵉ ∘ᵉ r'ᵉ ∘ᵉ iᵉ   ~ᵉ   rᵉ ∘ᵉ iᵉ  ~ᵉ  id.ᵉ
```

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {fᵉ : Aᵉ → Aᵉ}
  where

  map-essentially-unique-splitting-type-is-split-idempotentᵉ :
    {l2ᵉ l3ᵉ : Level}
    (Hᵉ : is-split-idempotentᵉ l2ᵉ fᵉ)
    (H'ᵉ : is-split-idempotentᵉ l3ᵉ fᵉ) →
    splitting-type-is-split-idempotentᵉ Hᵉ →
    splitting-type-is-split-idempotentᵉ H'ᵉ
  map-essentially-unique-splitting-type-is-split-idempotentᵉ Hᵉ H'ᵉ =
    map-retraction-is-split-idempotentᵉ H'ᵉ ∘ᵉ
    inclusion-is-split-idempotentᵉ Hᵉ

  is-fibered-involution-essentially-unique-splitting-type-is-split-idempotent'ᵉ :
    {l2ᵉ l3ᵉ : Level}
    (Hᵉ : is-split-idempotentᵉ l2ᵉ fᵉ)
    (H'ᵉ : is-split-idempotentᵉ l3ᵉ fᵉ) →
    is-sectionᵉ
      ( map-essentially-unique-splitting-type-is-split-idempotentᵉ Hᵉ H'ᵉ)
      ( map-essentially-unique-splitting-type-is-split-idempotentᵉ H'ᵉ Hᵉ)
  is-fibered-involution-essentially-unique-splitting-type-is-split-idempotent'ᵉ
    Hᵉ H'ᵉ =
    ( map-retraction-is-split-idempotentᵉ H'ᵉ ·lᵉ
      ( ( htpy-is-split-idempotentᵉ Hᵉ) ∙hᵉ
        ( inv-htpyᵉ (htpy-is-split-idempotentᵉ H'ᵉ))) ·rᵉ
      inclusion-is-split-idempotentᵉ H'ᵉ) ∙hᵉ
    ( horizontal-concat-htpyᵉ
      ( is-retraction-map-retraction-is-split-idempotentᵉ H'ᵉ)
      ( is-retraction-map-retraction-is-split-idempotentᵉ H'ᵉ))

  is-equiv-map-essentially-unique-splitting-type-is-split-idempotentᵉ :
    {l2ᵉ l3ᵉ : Level}
    (Hᵉ : is-split-idempotentᵉ l2ᵉ fᵉ)
    (H'ᵉ : is-split-idempotentᵉ l3ᵉ fᵉ) →
    is-equivᵉ
      ( map-essentially-unique-splitting-type-is-split-idempotentᵉ Hᵉ H'ᵉ)
  is-equiv-map-essentially-unique-splitting-type-is-split-idempotentᵉ Hᵉ H'ᵉ =
    is-equiv-is-invertibleᵉ
      ( map-essentially-unique-splitting-type-is-split-idempotentᵉ H'ᵉ Hᵉ)
      ( is-fibered-involution-essentially-unique-splitting-type-is-split-idempotent'ᵉ
        ( Hᵉ)
        ( H'ᵉ))
      ( is-fibered-involution-essentially-unique-splitting-type-is-split-idempotent'ᵉ
        ( H'ᵉ)
        ( Hᵉ))

  essentially-unique-splitting-type-is-split-idempotentᵉ :
    {l2ᵉ l3ᵉ : Level}
    (Hᵉ : is-split-idempotentᵉ l2ᵉ fᵉ)
    (H'ᵉ : is-split-idempotentᵉ l3ᵉ fᵉ) →
    splitting-type-is-split-idempotentᵉ Hᵉ ≃ᵉ
    splitting-type-is-split-idempotentᵉ H'ᵉ
  essentially-unique-splitting-type-is-split-idempotentᵉ Hᵉ H'ᵉ =
    ( map-essentially-unique-splitting-type-is-split-idempotentᵉ Hᵉ H'ᵉ ,ᵉ
      is-equiv-map-essentially-unique-splitting-type-is-split-idempotentᵉ
        ( Hᵉ)
        ( H'ᵉ))
```

### The type of split idempotent maps on `A` is equivalent to retracts of `A`

Noteᵉ thatᵉ theᵉ proofᵉ reliesᵉ onᵉ theᵉ
[functionᵉ extensionality](foundation.function-extensionality.mdᵉ) axiom.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  compute-split-idempotent-mapᵉ : split-idempotent-mapᵉ l2ᵉ Aᵉ ≃ᵉ retractsᵉ l2ᵉ Aᵉ
  compute-split-idempotent-mapᵉ =
    equivalence-reasoningᵉ
    Σᵉ ( Aᵉ → Aᵉ)
      ( λ fᵉ →
        Σᵉ ( UUᵉ l2ᵉ)
          ( λ Bᵉ →
            Σᵉ ( Bᵉ retract-ofᵉ Aᵉ)
              ( λ (iᵉ ,ᵉ rᵉ ,ᵉ Rᵉ) → iᵉ ∘ᵉ rᵉ ~ᵉ fᵉ)))
    ≃ᵉ Σᵉ (Aᵉ → Aᵉ) (λ fᵉ → (Σᵉ (retractsᵉ l2ᵉ Aᵉ) (λ (Bᵉ ,ᵉ iᵉ ,ᵉ rᵉ ,ᵉ Rᵉ) → iᵉ ∘ᵉ rᵉ ~ᵉ fᵉ)))
    byᵉ
      equiv-totᵉ
        ( λ fᵉ →
          inv-associative-Σᵉ
            ( UUᵉ l2ᵉ)
            ( _retract-ofᵉ Aᵉ)
            ( λ (Bᵉ ,ᵉ iᵉ ,ᵉ rᵉ ,ᵉ Rᵉ) → iᵉ ∘ᵉ rᵉ ~ᵉ fᵉ))
    ≃ᵉ Σᵉ (retractsᵉ l2ᵉ Aᵉ) (λ (Bᵉ ,ᵉ iᵉ ,ᵉ rᵉ ,ᵉ Rᵉ) → Σᵉ (Aᵉ → Aᵉ) (λ fᵉ → iᵉ ∘ᵉ rᵉ ~ᵉ fᵉ))
    byᵉ equiv-left-swap-Σᵉ
    ≃ᵉ retractsᵉ l2ᵉ Aᵉ
    byᵉ equiv-pr1ᵉ (λ (Bᵉ ,ᵉ iᵉ ,ᵉ rᵉ ,ᵉ Rᵉ) → is-torsorial-htpyᵉ (iᵉ ∘ᵉ rᵉ))
```

### Characterizing equality of split idempotence structures

Weᵉ characterizeᵉ equalityᵉ ofᵉ witnessesᵉ thatᵉ anᵉ endomapᵉ `f`ᵉ isᵉ splitᵉ idempotentᵉ asᵉ
equivalencesᵉ ofᵉ splittingᵉ typesᵉ suchᵉ thatᵉ theᵉ evidentᵉ retractsᵉ areᵉ homotopic.ᵉ Inᵉ
particular,ᵉ thisᵉ characterizationᵉ reliesᵉ onᵉ theᵉ univalenceᵉ axiom.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {fᵉ : Aᵉ → Aᵉ}
  where

  coherence-equiv-is-split-idempotentᵉ :
    {l3ᵉ : Level}
    (Rᵉ : is-split-idempotentᵉ l2ᵉ fᵉ)
    (Sᵉ : is-split-idempotentᵉ l3ᵉ fᵉ) →
    (eᵉ :
      splitting-type-is-split-idempotentᵉ Rᵉ ≃ᵉ
      splitting-type-is-split-idempotentᵉ Sᵉ)
    ( Hᵉ :
      htpy-retractᵉ
        ( retract-is-split-idempotentᵉ Rᵉ)
        ( comp-retractᵉ (retract-is-split-idempotentᵉ Sᵉ) (retract-equivᵉ eᵉ))) →
    UUᵉ l1ᵉ
  coherence-equiv-is-split-idempotentᵉ Rᵉ Sᵉ eᵉ Hᵉ =
    htpy-is-split-idempotentᵉ Rᵉ ~ᵉ
    horizontal-concat-htpyᵉ (pr1ᵉ Hᵉ) (pr1ᵉ (pr2ᵉ Hᵉ)) ∙hᵉ
    htpy-is-split-idempotent-equiv-splitting-typeᵉ Sᵉ eᵉ

  equiv-is-split-idempotentᵉ :
    {l3ᵉ : Level}
    (Rᵉ : is-split-idempotentᵉ l2ᵉ fᵉ)
    (Sᵉ : is-split-idempotentᵉ l3ᵉ fᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  equiv-is-split-idempotentᵉ Rᵉ Sᵉ =
    Σᵉ ( splitting-type-is-split-idempotentᵉ Rᵉ ≃ᵉ
        splitting-type-is-split-idempotentᵉ Sᵉ)
      ( λ eᵉ →
        Σᵉ ( htpy-retractᵉ
            ( retract-is-split-idempotentᵉ Rᵉ)
            ( comp-retractᵉ
              ( retract-is-split-idempotentᵉ Sᵉ)
              ( retract-equivᵉ eᵉ)))
          ( coherence-equiv-is-split-idempotentᵉ Rᵉ Sᵉ eᵉ))

  id-equiv-is-split-idempotentᵉ :
    (Rᵉ : is-split-idempotentᵉ l2ᵉ fᵉ) → equiv-is-split-idempotentᵉ Rᵉ Rᵉ
  id-equiv-is-split-idempotentᵉ Rᵉ =
    ( ( id-equivᵉ) ,ᵉ
      ( refl-htpyᵉ ,ᵉ
        refl-htpyᵉ ,ᵉ
        ( inv-htpyᵉ
          ( left-unit-law-left-whisker-compᵉ
            ( is-retraction-map-retraction-is-split-idempotentᵉ Rᵉ)) ∙hᵉ
          inv-htpy-right-unit-htpyᵉ)) ,ᵉ
      ( refl-htpyᵉ))

  equiv-eq-is-split-idempotentᵉ :
    (Rᵉ Sᵉ : is-split-idempotentᵉ l2ᵉ fᵉ) →
    Rᵉ ＝ᵉ Sᵉ → equiv-is-split-idempotentᵉ Rᵉ Sᵉ
  equiv-eq-is-split-idempotentᵉ Rᵉ .Rᵉ reflᵉ =
    id-equiv-is-split-idempotentᵉ Rᵉ

  abstract
    is-torsorial-equiv-is-split-idempotentᵉ :
      (Rᵉ : is-split-idempotentᵉ l2ᵉ fᵉ) →
      is-torsorialᵉ (equiv-is-split-idempotentᵉ {l2ᵉ} Rᵉ)
    is-torsorial-equiv-is-split-idempotentᵉ Rᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-equivᵉ (splitting-type-is-split-idempotentᵉ Rᵉ))
        ( splitting-type-is-split-idempotentᵉ Rᵉ ,ᵉ id-equivᵉ)
        ( is-torsorial-Eq-structureᵉ
          ( is-contr-equivᵉ
            ( Σᵉ ( (splitting-type-is-split-idempotentᵉ Rᵉ) retract-ofᵉ Aᵉ)
                ( htpy-retractᵉ (retract-is-split-idempotentᵉ Rᵉ)))
            ( equiv-totᵉ
              ( λ Sᵉ →
                equiv-totᵉ
                  ( λ Iᵉ →
                    equiv-totᵉ
                    ( λ Jᵉ →
                      equiv-concat-htpy'ᵉ
                        ( is-retraction-map-retraction-is-split-idempotentᵉ
                          ( Rᵉ))
                        ( ap-concat-htpyᵉ
                          ( horizontal-concat-htpyᵉ Jᵉ Iᵉ)
                          ( right-unit-htpyᵉ ∙hᵉ
                            left-unit-law-left-whisker-compᵉ
                              ( is-retraction-map-retraction-retractᵉ Sᵉ)))))))
            ( is-torsorial-htpy-retractᵉ (retract-is-split-idempotentᵉ Rᵉ)))
          ( ( retract-is-split-idempotentᵉ Rᵉ) ,ᵉ
            ( ( refl-htpyᵉ) ,ᵉ
              ( refl-htpyᵉ) ,ᵉ
              ( inv-htpyᵉ
                ( left-unit-law-left-whisker-compᵉ
                  ( is-retraction-map-retraction-is-split-idempotentᵉ Rᵉ)) ∙hᵉ
              inv-htpy-right-unit-htpyᵉ)))
          ( is-torsorial-htpyᵉ (htpy-is-split-idempotentᵉ Rᵉ)))

  is-equiv-equiv-eq-is-split-idempotentᵉ :
    (Rᵉ Sᵉ : is-split-idempotentᵉ l2ᵉ fᵉ) →
    is-equivᵉ (equiv-eq-is-split-idempotentᵉ Rᵉ Sᵉ)
  is-equiv-equiv-eq-is-split-idempotentᵉ Rᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-equiv-is-split-idempotentᵉ Rᵉ)
      ( equiv-eq-is-split-idempotentᵉ Rᵉ)

  equiv-equiv-eq-is-split-idempotentᵉ :
    (Rᵉ Sᵉ : is-split-idempotentᵉ l2ᵉ fᵉ) →
    (Rᵉ ＝ᵉ Sᵉ) ≃ᵉ equiv-is-split-idempotentᵉ Rᵉ Sᵉ
  equiv-equiv-eq-is-split-idempotentᵉ Rᵉ Sᵉ =
    ( equiv-eq-is-split-idempotentᵉ Rᵉ Sᵉ ,ᵉ
      is-equiv-equiv-eq-is-split-idempotentᵉ Rᵉ Sᵉ)

  eq-equiv-is-split-idempotentᵉ :
    (Rᵉ Sᵉ : is-split-idempotentᵉ l2ᵉ fᵉ) →
    equiv-is-split-idempotentᵉ Rᵉ Sᵉ → Rᵉ ＝ᵉ Sᵉ
  eq-equiv-is-split-idempotentᵉ Rᵉ Sᵉ =
    map-inv-is-equivᵉ (is-equiv-equiv-eq-is-split-idempotentᵉ Rᵉ Sᵉ)
```

### Split idempotent maps are idempotent

Thisᵉ isᵉ Lemmaᵉ 3.3ᵉ in {{#citeᵉ Shu17}}.ᵉ

**Proof.**ᵉ Givenᵉ aᵉ splitᵉ idempotentᵉ mapᵉ `f`ᵉ with splittingᵉ `Rᵉ : rᵉ ∘ᵉ iᵉ ~ᵉ id`ᵉ andᵉ
homotopyᵉ `Hᵉ : iᵉ ∘ᵉ rᵉ ~ᵉ f`,ᵉ thenᵉ `f`ᵉ isᵉ idempotentᵉ viaᵉ theᵉ followingᵉ witnessᵉ

```text
       (H◽H)⁻¹ᵉ            iRrᵉ        Hᵉ
  fᵉ ∘ᵉ fᵉ  ~ᵉ  iᵉ ∘ᵉ rᵉ ∘ᵉ iᵉ ∘ᵉ rᵉ  ~ᵉ  iᵉ ∘ᵉ rᵉ  ~ᵉ  f.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {fᵉ : Aᵉ → Aᵉ} (Hᵉ : is-split-idempotentᵉ l2ᵉ fᵉ)
  where

  is-idempotent-is-split-idempotentᵉ : is-idempotentᵉ fᵉ
  is-idempotent-is-split-idempotentᵉ =
    is-idempotent-inv-htpyᵉ
      ( is-idempotent-inclusion-retractionᵉ
        ( inclusion-is-split-idempotentᵉ Hᵉ)
        ( map-retraction-is-split-idempotentᵉ Hᵉ)
        ( is-retraction-map-retraction-is-split-idempotentᵉ Hᵉ))
      ( htpy-is-split-idempotentᵉ Hᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Hᵉ : split-idempotent-mapᵉ l2ᵉ Aᵉ)
  where

  is-idempotent-split-idempotent-mapᵉ :
    is-idempotentᵉ (map-split-idempotent-mapᵉ Hᵉ)
  is-idempotent-split-idempotent-mapᵉ =
    is-idempotent-is-split-idempotentᵉ
      ( is-split-idempotent-split-idempotent-mapᵉ Hᵉ)
```

### Split idempotent maps are quasicoherently idempotent

Thisᵉ isᵉ Lemmaᵉ 3.6ᵉ in {{#citeᵉ Shu17}}.ᵉ

**Proof.**ᵉ Inclusion-retractionᵉ compositesᵉ areᵉ quasicoherentlyᵉ idempotent,ᵉ soᵉ
sinceᵉ quasicoherentlyᵉ idempotentᵉ mapsᵉ areᵉ closedᵉ underᵉ homotopyᵉ weᵉ areᵉ done.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {fᵉ : Aᵉ → Aᵉ} (Hᵉ : is-split-idempotentᵉ l2ᵉ fᵉ)
  where

  abstract
    quasicoherence-is-idempotent-is-split-idempotentᵉ :
      quasicoherence-is-idempotentᵉ fᵉ
        ( is-idempotent-is-split-idempotentᵉ Hᵉ)
    quasicoherence-is-idempotent-is-split-idempotentᵉ =
      quasicoherence-is-idempotent-is-idempotent-htpyᵉ
        ( is-quasicoherently-idempotent-inv-htpyᵉ
          ( is-quasicoherently-idempotent-inclusion-retractionᵉ
            ( inclusion-is-split-idempotentᵉ Hᵉ)
            ( map-retraction-is-split-idempotentᵉ Hᵉ)
            (is-retraction-map-retraction-is-split-idempotentᵉ Hᵉ))
          ( htpy-is-split-idempotentᵉ Hᵉ))
        ( is-idempotent-is-split-idempotentᵉ Hᵉ)
        ( ap-concat-htpyᵉ _ (inv-inv-htpyᵉ (htpy-is-split-idempotentᵉ Hᵉ)))

  is-quasicoherently-idempotent-is-split-idempotentᵉ :
    is-quasicoherently-idempotentᵉ fᵉ
  is-quasicoherently-idempotent-is-split-idempotentᵉ =
    ( is-idempotent-is-split-idempotentᵉ Hᵉ ,ᵉ
      quasicoherence-is-idempotent-is-split-idempotentᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Hᵉ : split-idempotent-mapᵉ l2ᵉ Aᵉ)
  where

  is-quasicoherently-idempotent-split-idempotent-mapᵉ :
    is-quasicoherently-idempotentᵉ (map-split-idempotent-mapᵉ Hᵉ)
  is-quasicoherently-idempotent-split-idempotent-mapᵉ =
    is-quasicoherently-idempotent-is-split-idempotentᵉ
      ( is-split-idempotent-split-idempotent-mapᵉ Hᵉ)
```

### Every idempotent map on a set splits

Thisᵉ isᵉ Theoremᵉ 3.7ᵉ ofᵉ {{#citeᵉ Shu17}}.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ : Aᵉ → Aᵉ}
  (is-set-Aᵉ : is-setᵉ Aᵉ) (Hᵉ : is-idempotentᵉ fᵉ)
  where

  splitting-type-is-split-idempotent-is-idempotent-is-setᵉ : UUᵉ lᵉ
  splitting-type-is-split-idempotent-is-idempotent-is-setᵉ =
    fixed-pointᵉ fᵉ

  inclusion-is-split-idempotent-is-idempotent-is-setᵉ :
    splitting-type-is-split-idempotent-is-idempotent-is-setᵉ → Aᵉ
  inclusion-is-split-idempotent-is-idempotent-is-setᵉ = pr1ᵉ

  map-retraction-is-split-idempotent-is-idempotent-is-setᵉ :
    Aᵉ → splitting-type-is-split-idempotent-is-idempotent-is-setᵉ
  map-retraction-is-split-idempotent-is-idempotent-is-setᵉ xᵉ = (fᵉ xᵉ ,ᵉ Hᵉ xᵉ)

  is-retraction-map-retraction-is-split-idempotent-is-idempotent-is-setᵉ :
    is-retractionᵉ
      ( inclusion-is-split-idempotent-is-idempotent-is-setᵉ)
      ( map-retraction-is-split-idempotent-is-idempotent-is-setᵉ)
  is-retraction-map-retraction-is-split-idempotent-is-idempotent-is-setᵉ
    (xᵉ ,ᵉ pᵉ) =
    eq-pair-Σᵉ pᵉ (eq-is-propᵉ (is-set-Aᵉ (fᵉ xᵉ) xᵉ))

  retraction-is-split-idempotent-is-idempotent-is-setᵉ :
    retractionᵉ (inclusion-is-split-idempotent-is-idempotent-is-setᵉ)
  retraction-is-split-idempotent-is-idempotent-is-setᵉ =
    ( map-retraction-is-split-idempotent-is-idempotent-is-setᵉ ,ᵉ
      is-retraction-map-retraction-is-split-idempotent-is-idempotent-is-setᵉ)

  retract-is-split-idempotent-is-idempotent-is-setᵉ :
    splitting-type-is-split-idempotent-is-idempotent-is-setᵉ retract-ofᵉ Aᵉ
  retract-is-split-idempotent-is-idempotent-is-setᵉ =
    ( inclusion-is-split-idempotent-is-idempotent-is-setᵉ ,ᵉ
      retraction-is-split-idempotent-is-idempotent-is-setᵉ)

  htpy-is-split-idempotent-is-idempotent-is-setᵉ :
    inclusion-is-split-idempotent-is-idempotent-is-setᵉ ∘ᵉ
    map-retraction-is-split-idempotent-is-idempotent-is-setᵉ ~ᵉ
    fᵉ
  htpy-is-split-idempotent-is-idempotent-is-setᵉ = refl-htpyᵉ

  is-split-idempotent-is-idempotent-is-setᵉ : is-split-idempotentᵉ lᵉ fᵉ
  is-split-idempotent-is-idempotent-is-setᵉ =
    ( splitting-type-is-split-idempotent-is-idempotent-is-setᵉ ,ᵉ
      retract-is-split-idempotent-is-idempotent-is-setᵉ ,ᵉ
      htpy-is-split-idempotent-is-idempotent-is-setᵉ)
```

### Weakly constant idempotent maps split

Thisᵉ isᵉ Theoremᵉ 3.9ᵉ ofᵉ {{#citeᵉ Shu17}}.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ : Aᵉ → Aᵉ}
  (Hᵉ : is-idempotentᵉ fᵉ) (Wᵉ : is-weakly-constantᵉ fᵉ)
  where

  splitting-type-is-split-idempotent-is-weakly-constant-is-idempotentᵉ :
    UUᵉ lᵉ
  splitting-type-is-split-idempotent-is-weakly-constant-is-idempotentᵉ =
    fixed-pointᵉ fᵉ

  inclusion-is-split-idempotent-is-weakly-constant-is-idempotentᵉ :
    splitting-type-is-split-idempotent-is-weakly-constant-is-idempotentᵉ →
    Aᵉ
  inclusion-is-split-idempotent-is-weakly-constant-is-idempotentᵉ = pr1ᵉ

  map-retraction-is-split-idempotent-is-weakly-constant-is-idempotentᵉ :
    Aᵉ →
    splitting-type-is-split-idempotent-is-weakly-constant-is-idempotentᵉ
  map-retraction-is-split-idempotent-is-weakly-constant-is-idempotentᵉ xᵉ =
    ( fᵉ xᵉ ,ᵉ Hᵉ xᵉ)

  is-retraction-map-retraction-is-split-idempotent-is-weakly-constant-is-idempotentᵉ :
    is-retractionᵉ
      ( inclusion-is-split-idempotent-is-weakly-constant-is-idempotentᵉ)
      ( map-retraction-is-split-idempotent-is-weakly-constant-is-idempotentᵉ)
  is-retraction-map-retraction-is-split-idempotent-is-weakly-constant-is-idempotentᵉ
    _ =
    eq-is-propᵉ (is-prop-fixed-point-is-weakly-constantᵉ Wᵉ)

  retraction-is-split-idempotent-is-weakly-constant-is-idempotentᵉ :
    retractionᵉ
      ( inclusion-is-split-idempotent-is-weakly-constant-is-idempotentᵉ)
  retraction-is-split-idempotent-is-weakly-constant-is-idempotentᵉ =
    ( map-retraction-is-split-idempotent-is-weakly-constant-is-idempotentᵉ ,ᵉ
      is-retraction-map-retraction-is-split-idempotent-is-weakly-constant-is-idempotentᵉ)

  retract-is-split-idempotent-is-weakly-constant-is-idempotentᵉ :
    retractᵉ
      ( Aᵉ)
      ( splitting-type-is-split-idempotent-is-weakly-constant-is-idempotentᵉ)
  retract-is-split-idempotent-is-weakly-constant-is-idempotentᵉ =
    ( inclusion-is-split-idempotent-is-weakly-constant-is-idempotentᵉ ,ᵉ
      retraction-is-split-idempotent-is-weakly-constant-is-idempotentᵉ)

  htpy-is-split-idempotent-is-weakly-constant-is-idempotentᵉ :
    inclusion-is-split-idempotent-is-weakly-constant-is-idempotentᵉ ∘ᵉ
    map-retraction-is-split-idempotent-is-weakly-constant-is-idempotentᵉ ~ᵉ
    fᵉ
  htpy-is-split-idempotent-is-weakly-constant-is-idempotentᵉ = refl-htpyᵉ

  is-split-idempotent-is-weakly-constant-is-idempotentᵉ :
    is-split-idempotentᵉ lᵉ fᵉ
  is-split-idempotent-is-weakly-constant-is-idempotentᵉ =
    ( splitting-type-is-split-idempotent-is-weakly-constant-is-idempotentᵉ ,ᵉ
      retract-is-split-idempotent-is-weakly-constant-is-idempotentᵉ ,ᵉ
      htpy-is-split-idempotent-is-weakly-constant-is-idempotentᵉ)
```

### Quasicoherently idempotent maps split

Thisᵉ isᵉ Theoremᵉ 5.3ᵉ ofᵉ {{#citeᵉ Shu17}}.ᵉ

Asᵉ perᵉ Remarkᵉ 5.4ᵉ {{#citeᵉ Shu17}},ᵉ theᵉ inclusionᵉ ofᵉ `A`ᵉ intoᵉ theᵉ splittingᵉ typeᵉ
canᵉ beᵉ constructedᵉ forᵉ anyᵉ endofunctionᵉ `f`.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (fᵉ : Aᵉ → Aᵉ)
  where

  inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent'ᵉ :
    inverse-sequential-diagramᵉ lᵉ
  inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent'ᵉ =
    ( (λ _ → Aᵉ) ,ᵉ (λ _ → fᵉ))

  splitting-type-is-quasicoherently-idempotent'ᵉ : UUᵉ lᵉ
  splitting-type-is-quasicoherently-idempotent'ᵉ =
    standard-sequential-limitᵉ
      ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent'ᵉ)

  inclusion-splitting-type-is-quasicoherently-idempotent'ᵉ :
    splitting-type-is-quasicoherently-idempotent'ᵉ → Aᵉ
  inclusion-splitting-type-is-quasicoherently-idempotent'ᵉ (aᵉ ,ᵉ αᵉ) = aᵉ 0
```

Moreover,ᵉ againᵉ byᵉ Remarkᵉ 5.4ᵉ {{#citeᵉ Shu17}},ᵉ givenᵉ onlyᵉ theᵉ idempotenceᵉ
homotopyᵉ `fᵉ ∘ᵉ fᵉ ~ᵉ f`,ᵉ weᵉ canᵉ constructᵉ theᵉ converseᵉ mapᵉ to thisᵉ inclusionᵉ andᵉ
showᵉ thatᵉ thisᵉ givesᵉ aᵉ factorizationᵉ ofᵉ `f`.ᵉ Indeed,ᵉ thisᵉ factorizationᵉ isᵉ
strict.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ : Aᵉ → Aᵉ}
  (Iᵉ : is-idempotentᵉ fᵉ)
  where

  map-retraction-splitting-type-is-quasicoherently-idempotent'ᵉ :
    Aᵉ → splitting-type-is-quasicoherently-idempotent'ᵉ fᵉ
  map-retraction-splitting-type-is-quasicoherently-idempotent'ᵉ xᵉ =
    ( (λ _ → fᵉ xᵉ) ,ᵉ (λ _ → invᵉ (Iᵉ xᵉ)))

  htpy-is-split-idempotent-is-quasicoherently-idempotent'ᵉ :
    inclusion-splitting-type-is-quasicoherently-idempotent'ᵉ fᵉ ∘ᵉ
    map-retraction-splitting-type-is-quasicoherently-idempotent'ᵉ ~ᵉ
    fᵉ
  htpy-is-split-idempotent-is-quasicoherently-idempotent'ᵉ = refl-htpyᵉ
```

However,ᵉ to showᵉ thatᵉ theseᵉ mapsᵉ formᵉ anᵉ inclusion-retractionᵉ pair,ᵉ weᵉ useᵉ theᵉ
coherenceᵉ ofᵉ quasicoherentᵉ idempotentsᵉ asᵉ wellᵉ asᵉ theᵉ functionᵉ extensionalityᵉ
axiom.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ : Aᵉ → Aᵉ}
  (Hᵉ : is-quasicoherently-idempotentᵉ fᵉ)
  where

  inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotentᵉ :
    inverse-sequential-diagramᵉ lᵉ
  inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotentᵉ =
    inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent'ᵉ
      ( fᵉ)

  splitting-type-is-quasicoherently-idempotentᵉ : UUᵉ lᵉ
  splitting-type-is-quasicoherently-idempotentᵉ =
    splitting-type-is-quasicoherently-idempotent'ᵉ fᵉ

  inclusion-splitting-type-is-quasicoherently-idempotentᵉ :
    splitting-type-is-quasicoherently-idempotentᵉ → Aᵉ
  inclusion-splitting-type-is-quasicoherently-idempotentᵉ =
    inclusion-splitting-type-is-quasicoherently-idempotent'ᵉ fᵉ

  map-retraction-splitting-type-is-quasicoherently-idempotentᵉ :
    Aᵉ → splitting-type-is-quasicoherently-idempotentᵉ
  map-retraction-splitting-type-is-quasicoherently-idempotentᵉ =
    map-retraction-splitting-type-is-quasicoherently-idempotent'ᵉ
      ( is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ)

  htpy-is-split-idempotent-is-quasicoherently-idempotentᵉ :
    inclusion-splitting-type-is-quasicoherently-idempotentᵉ ∘ᵉ
    map-retraction-splitting-type-is-quasicoherently-idempotentᵉ ~ᵉ
    fᵉ
  htpy-is-split-idempotent-is-quasicoherently-idempotentᵉ =
    htpy-is-split-idempotent-is-quasicoherently-idempotent'ᵉ
      ( is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ)
```

Now,ᵉ to constructᵉ theᵉ desiredᵉ retractingᵉ homotopyᵉ

```text
  rᵉ ∘ᵉ iᵉ ~ᵉ idᵉ
```

weᵉ subdivideᵉ theᵉ problemᵉ intoᵉ two.ᵉ First,ᵉ weᵉ showᵉ thatᵉ shiftingᵉ theᵉ sequenceᵉ andᵉ
whiskeringᵉ byᵉ `fᵉ ∘ᵉ f`ᵉ isᵉ homotopicᵉ to theᵉ identityᵉ

```text
  ((fᵉ (fᵉ a₍₋₎₊₁ᵉ)) ,ᵉ (fᵉ ∘ᵉ fᵉ) ·lᵉ α₍₋₎₊₁ᵉ) ~ᵉ (aᵉ ,ᵉ α).ᵉ
```

```agda
  shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ :
    standard-sequential-limitᵉ
      ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotentᵉ) →
    standard-sequential-limitᵉ
      ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotentᵉ)
  shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ (aᵉ ,ᵉ αᵉ) =
    ((fᵉ ∘ᵉ fᵉ ∘ᵉ aᵉ ∘ᵉ succ-ℕᵉ) ,ᵉ ( (fᵉ ∘ᵉ fᵉ) ·lᵉ (αᵉ ∘ᵉ succ-ℕᵉ)))

  htpy-sequence-shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ :
    ((aᵉ ,ᵉ αᵉ) :
      standard-sequential-limitᵉ
        ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotentᵉ)) →
    fᵉ ∘ᵉ fᵉ ∘ᵉ aᵉ ∘ᵉ succ-ℕᵉ ~ᵉ aᵉ
  htpy-sequence-shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ
    ( aᵉ ,ᵉ αᵉ) nᵉ =
    is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ (aᵉ (succ-ℕᵉ nᵉ)) ∙ᵉ invᵉ (αᵉ nᵉ)

  abstract
    htpy-coherence-shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ :
      (xᵉ :
        standard-sequential-limitᵉ
          ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotentᵉ)) →
      coherence-Eq-standard-sequential-limitᵉ
        ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotentᵉ)
        ( shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ xᵉ)
        ( xᵉ)
        ( htpy-sequence-shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ
          ( xᵉ))
    htpy-coherence-shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ
      ( aᵉ ,ᵉ αᵉ) nᵉ =
      ( apᵉ
        ( apᵉ (fᵉ ∘ᵉ fᵉ) (αᵉ (succ-ℕᵉ nᵉ)) ∙ᵉ_)
        ( ( ap-concatᵉ fᵉ
            ( is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ
              ( aᵉ (second-succ-ℕᵉ nᵉ)))
            ( invᵉ (αᵉ (succ-ℕᵉ nᵉ)))) ∙ᵉ
          ( apᵉ
            ( _∙ᵉ apᵉ fᵉ (invᵉ (αᵉ (succ-ℕᵉ nᵉ))))
            ( coh-is-quasicoherently-idempotentᵉ Hᵉ
              ( aᵉ (second-succ-ℕᵉ nᵉ)))))) ∙ᵉ
      ( invᵉ
        ( assocᵉ
          ( apᵉ (fᵉ ∘ᵉ fᵉ) (αᵉ (succ-ℕᵉ nᵉ)))
          ( is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ
            ( fᵉ (aᵉ (second-succ-ℕᵉ nᵉ))))
          ( apᵉ fᵉ (invᵉ (αᵉ (succ-ℕᵉ nᵉ)))))) ∙ᵉ
      ( apᵉ
        ( _∙ᵉ apᵉ fᵉ (invᵉ (αᵉ (succ-ℕᵉ nᵉ))))
        ( invᵉ
          ( nat-htpyᵉ
            ( is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ)
            ( αᵉ (succ-ℕᵉ nᵉ))))) ∙ᵉ
      ( assocᵉ
        ( is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ (aᵉ (succ-ℕᵉ nᵉ)))
        ( apᵉ fᵉ (αᵉ (succ-ℕᵉ nᵉ)))
        ( apᵉ fᵉ (invᵉ (αᵉ (succ-ℕᵉ nᵉ))))) ∙ᵉ
      ( apᵉ
        ( is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ (aᵉ (succ-ℕᵉ nᵉ)) ∙ᵉ_)
        ( ( invᵉ (ap-concatᵉ fᵉ (αᵉ (succ-ℕᵉ nᵉ)) (invᵉ (αᵉ (succ-ℕᵉ nᵉ))))) ∙ᵉ
          ( ap²ᵉ fᵉ (right-invᵉ (αᵉ (succ-ℕᵉ nᵉ)))) ∙ᵉ
          invᵉ (left-invᵉ (αᵉ nᵉ)))) ∙ᵉ
      ( invᵉ
        ( assocᵉ
          ( is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ (aᵉ (succ-ℕᵉ nᵉ)))
          ( invᵉ (αᵉ nᵉ))
          ( αᵉ nᵉ)))

  compute-shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ :
    shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ ~ᵉ idᵉ
  compute-shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ
    xᵉ =
    eq-Eq-standard-sequential-limitᵉ
      ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotentᵉ)
      ( shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ xᵉ)
      ( xᵉ)
      ( ( htpy-sequence-shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ
          xᵉ) ,ᵉ
        ( htpy-coherence-shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ
          xᵉ))
```

Thenᵉ weᵉ showᵉ thatᵉ `rᵉ ∘ᵉ i`ᵉ isᵉ homotopicᵉ to thisᵉ operation.ᵉ Thisᵉ timeᵉ weᵉ proceedᵉ
byᵉ inductionᵉ onᵉ `n`.ᵉ

```agda
  htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ :
    ( (aᵉ ,ᵉ αᵉ) :
      standard-sequential-limitᵉ
        ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent'ᵉ
          ( fᵉ))) →
    ( λ _ →
      fᵉ (inclusion-splitting-type-is-quasicoherently-idempotentᵉ (aᵉ ,ᵉ αᵉ))) ~ᵉ
    ( fᵉ ∘ᵉ fᵉ ∘ᵉ aᵉ ∘ᵉ succ-ℕᵉ)
  htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ
    ( aᵉ ,ᵉ αᵉ) 0 = apᵉ fᵉ (αᵉ 0ᵉ)
  htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ
    ( aᵉ ,ᵉ αᵉ) (succ-ℕᵉ nᵉ) =
    ( htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ
      ( aᵉ ,ᵉ αᵉ) nᵉ) ∙ᵉ
    ( is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ (aᵉ (succ-ℕᵉ nᵉ))) ∙ᵉ
    ( apᵉ fᵉ (αᵉ (succ-ℕᵉ nᵉ)))

  abstract
    htpy-coherence-compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ :
      ((aᵉ ,ᵉ αᵉ) :
        standard-sequential-limitᵉ
          ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotentᵉ)) →
      coherence-square-homotopiesᵉ
        ( htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ
          ( aᵉ ,ᵉ αᵉ))
        ( λ nᵉ →
          invᵉ
            ( is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ
              ( inclusion-splitting-type-is-quasicoherently-idempotentᵉ
                ( aᵉ ,ᵉ αᵉ))))
        ( λ nᵉ → apᵉ (fᵉ ∘ᵉ fᵉ) (αᵉ (succ-ℕᵉ nᵉ)))
        ( λ nᵉ →
          apᵉ fᵉ
            ( ( htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ
                ( aᵉ ,ᵉ αᵉ)
                ( nᵉ)) ∙ᵉ
              ( is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ
                ( aᵉ (succ-ℕᵉ nᵉ))) ∙ᵉ
              ( apᵉ fᵉ (αᵉ (succ-ℕᵉ nᵉ)))))
    htpy-coherence-compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ
      ( aᵉ ,ᵉ αᵉ) 0 =
      ( apᵉ
        ( invᵉ (is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ (aᵉ 0ᵉ)) ∙ᵉ_)
        ( ( ap-concatᵉ fᵉ
            ( apᵉ fᵉ (αᵉ 0ᵉ) ∙ᵉ
              is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ (aᵉ 1ᵉ))
            ( apᵉ fᵉ (αᵉ 1ᵉ))) ∙ᵉ
          ( ap-binaryᵉ (_∙ᵉ_)
            ( ap-concatᵉ fᵉ
              ( apᵉ fᵉ (αᵉ 0ᵉ))
              ( is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ (aᵉ 1ᵉ)))
            ( invᵉ (ap-compᵉ fᵉ fᵉ (αᵉ 1ᵉ)))))) ∙ᵉ
      ( invᵉ
          ( assocᵉ
            ( invᵉ (is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ (aᵉ 0ᵉ)))
            ( apᵉ fᵉ (apᵉ fᵉ (αᵉ 0ᵉ)) ∙ᵉ
              apᵉ fᵉ (is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ (aᵉ 1ᵉ)))
            ( apᵉ (fᵉ ∘ᵉ fᵉ) (αᵉ 1ᵉ)))) ∙ᵉ
      ( apᵉ
        ( _∙ᵉ apᵉ (fᵉ ∘ᵉ fᵉ) (αᵉ 1ᵉ))
        ( apᵉ
          ( invᵉ (is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ (aᵉ 0ᵉ)) ∙ᵉ_)
          ( ( ap-binaryᵉ (_∙ᵉ_)
              ( invᵉ (ap-compᵉ fᵉ fᵉ (αᵉ 0ᵉ)))
              ( coh-is-quasicoherently-idempotentᵉ Hᵉ (aᵉ 1ᵉ))) ∙ᵉ
            ( invᵉ
              ( nat-htpyᵉ
                ( is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ) (αᵉ 0ᵉ)))) ∙ᵉ
          ( is-retraction-inv-concatᵉ
            ( is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ (aᵉ 0ᵉ))
            ( apᵉ fᵉ (αᵉ 0ᵉ)))))
```

Forᵉ theᵉ inductive stepᵉ weᵉ fillᵉ theᵉ followingᵉ diagramᵉ asᵉ prescribed,ᵉ in theᵉ
notationᵉ ofᵉ {{#citeᵉ Shu17ᵉ}}:

```text
              ξₙ₊₁ᵉ               Iᵉ aₙ₊₁ᵉ             fᵉ (αₙ₊₁)⁻¹ᵉ
    fᵉ a₀ᵉ ------------>ᵉ fᵉ (fᵉ aₙ₊₁ᵉ) --->ᵉ fᵉ aₙ₊₁ᵉ -------------------->ᵉ fᵉ (fᵉ aₙ₊₂ᵉ)
     |                    |                  [nat-htpyᵉ]  ___refl___/ᵉ   |
  (I⁻¹ᵉ a₀ᵉ)    [Ξₙᵉ]        |       Iᵉ (fᵉ aₙ₊₂ᵉ)            /ᵉ         (fᵉ ∘ᵉ f)(αₙ₊₂ᵉ)
     ∨ᵉ                    ∨ᵉ         ------>ᵉ           /ᵉ                ∨ᵉ
  fᵉ (fᵉ a₀ᵉ) -------->ᵉ fᵉ (fᵉ (fᵉ aₙ₊₂ᵉ))   [Jᵉ]   fᵉ (fᵉ aₙ₊₂ᵉ) ---------->ᵉ fᵉ (fᵉ (fᵉ aₙ₊₃ᵉ))
     (fᵉ (ξₙᵉ ∙ᵉ Iᵉ aₙ₊₁ᵉ ∙ᵉ fᵉ αₙ₊₁ᵉ))     ------>ᵉ           (fᵉ ∘ᵉ fᵉ) (αₙ₊₂ᵉ)
                                  fᵉ (Iᵉ aₙ₊₂ᵉ)
```

where theᵉ symbolsᵉ translateᵉ to codeᵉ asᵉ followsᵉ:

```text
Iᵉ = is-idempotent-is-quasicoherently-idempotentᵉ Hᵉ
Jᵉ = coh-is-quasicoherently-idempotentᵉ Hᵉ
ξᵉ = htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ (aᵉ ,ᵉ αᵉ)
Ξᵉ = htpy-coherence-compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ (aᵉ ,ᵉ α).ᵉ
```

Note,ᵉ in particular,ᵉ thatᵉ theᵉ left-handᵉ squareᵉ isᵉ theᵉ inductive hypothesis.ᵉ

```agda
    htpy-coherence-compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ
      ( aᵉ ,ᵉ αᵉ) (succ-ℕᵉ nᵉ) =
      ( apᵉ
        ( invᵉ (Iᵉ (aᵉ 0ᵉ)) ∙ᵉ_)
        ( ( ap-concatᵉ fᵉ
            ( ξᵉ (succ-ℕᵉ nᵉ) ∙ᵉ Iᵉ (aᵉ (second-succ-ℕᵉ nᵉ)))
            ( apᵉ fᵉ (αᵉ (second-succ-ℕᵉ nᵉ)))) ∙ᵉ
          ( ap-binaryᵉ (_∙ᵉ_)
            ( ap-concatᵉ fᵉ (ξᵉ (succ-ℕᵉ nᵉ)) (Iᵉ (aᵉ (second-succ-ℕᵉ nᵉ))))
            ( invᵉ (ap-compᵉ fᵉ fᵉ (αᵉ (second-succ-ℕᵉ nᵉ))))))) ∙ᵉ
      ( invᵉ
        ( assocᵉ
          ( invᵉ (Iᵉ (aᵉ 0ᵉ)))
          ( apᵉ fᵉ
            ( ξᵉ nᵉ ∙ᵉ
              Iᵉ (aᵉ (succ-ℕᵉ nᵉ)) ∙ᵉ
              apᵉ fᵉ (αᵉ (succ-ℕᵉ nᵉ))) ∙ᵉ
              apᵉ fᵉ (Iᵉ (aᵉ (second-succ-ℕᵉ nᵉ))))
          ( apᵉ (fᵉ ∘ᵉ fᵉ) (αᵉ (second-succ-ℕᵉ nᵉ))))) ∙ᵉ
      ( apᵉ
        ( _∙ᵉ apᵉ (fᵉ ∘ᵉ fᵉ) (αᵉ (second-succ-ℕᵉ nᵉ)))
        ( ( invᵉ
            ( assocᵉ
              ( invᵉ (Iᵉ (aᵉ 0ᵉ)))
              ( apᵉ fᵉ (ξᵉ nᵉ ∙ᵉ Iᵉ (aᵉ (succ-ℕᵉ nᵉ)) ∙ᵉ apᵉ fᵉ (αᵉ (succ-ℕᵉ nᵉ))))
              ( apᵉ fᵉ (Iᵉ (aᵉ (second-succ-ℕᵉ nᵉ)))))) ∙ᵉ
          ( apᵉ
            ( _∙ᵉ apᵉ fᵉ (Iᵉ ( aᵉ (second-succ-ℕᵉ nᵉ))))
            ( htpy-coherence-compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ
              ( aᵉ ,ᵉ αᵉ)
              ( nᵉ))) ∙ᵉ
          ( assocᵉ
              ( ξᵉ nᵉ)
              ( apᵉ (fᵉ ∘ᵉ fᵉ) (αᵉ (succ-ℕᵉ nᵉ)))
              ( apᵉ fᵉ (Iᵉ (aᵉ (second-succ-ℕᵉ nᵉ))))) ∙ᵉ
          ( apᵉ
            ( ξᵉ nᵉ ∙ᵉ_)
            ( apᵉ
              ( apᵉ (fᵉ ∘ᵉ fᵉ) (αᵉ (succ-ℕᵉ nᵉ)) ∙ᵉ_)
              ( coh-is-quasicoherently-idempotentᵉ Hᵉ
                ( aᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))) ∙ᵉ
            ( invᵉ (nat-htpyᵉ Iᵉ (αᵉ (succ-ℕᵉ nᵉ)))))) ∙ᵉ
          ( invᵉ (assocᵉ (ξᵉ nᵉ) (Iᵉ (aᵉ (succ-ℕᵉ nᵉ))) (apᵉ fᵉ (αᵉ (succ-ℕᵉ nᵉ)))))))
      where
        ξᵉ :
          ( λ _ →
            fᵉ ( inclusion-splitting-type-is-quasicoherently-idempotentᵉ
                ( aᵉ ,ᵉ αᵉ))) ~ᵉ
          ( fᵉ ∘ᵉ fᵉ ∘ᵉ aᵉ ∘ᵉ succ-ℕᵉ)
        ξᵉ =
          htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ
            ( aᵉ ,ᵉ αᵉ)
        Iᵉ : is-idempotentᵉ fᵉ
        Iᵉ = pr1ᵉ Hᵉ
```

Nowᵉ itᵉ onlyᵉ remainsᵉ to putᵉ itᵉ allᵉ together.ᵉ

```agda
  abstract
    compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ :
      map-retraction-splitting-type-is-quasicoherently-idempotentᵉ ∘ᵉ
      inclusion-splitting-type-is-quasicoherently-idempotentᵉ ~ᵉ
      shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ
    compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ
      xᵉ =
      eq-Eq-standard-sequential-limitᵉ
        ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotentᵉ)
        ( map-retraction-splitting-type-is-quasicoherently-idempotentᵉ
          ( inclusion-splitting-type-is-quasicoherently-idempotentᵉ xᵉ))
        ( shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ
          ( xᵉ))
        ( htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ
            ( xᵉ) ,ᵉ
          htpy-coherence-compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ
            ( xᵉ))

  is-retraction-map-retraction-splitting-type-is-quasicoherently-idempotentᵉ :
    is-retractionᵉ
      ( inclusion-splitting-type-is-quasicoherently-idempotentᵉ)
      ( map-retraction-splitting-type-is-quasicoherently-idempotentᵉ)
  is-retraction-map-retraction-splitting-type-is-quasicoherently-idempotentᵉ =
    compute-retraction-splitting-type-is-quasicoherently-idempotentᵉ ∙hᵉ
    compute-shift-retraction-splitting-type-is-quasicoherently-idempotentᵉ

  retraction-splitting-type-is-quasicoherently-idempotentᵉ :
    retractionᵉ (inclusion-splitting-type-is-quasicoherently-idempotentᵉ)
  retraction-splitting-type-is-quasicoherently-idempotentᵉ =
    ( map-retraction-splitting-type-is-quasicoherently-idempotentᵉ ,ᵉ
      is-retraction-map-retraction-splitting-type-is-quasicoherently-idempotentᵉ)

  retract-splitting-type-is-quasicoherently-idempotentᵉ :
    splitting-type-is-quasicoherently-idempotentᵉ retract-ofᵉ Aᵉ
  retract-splitting-type-is-quasicoherently-idempotentᵉ =
    ( inclusion-splitting-type-is-quasicoherently-idempotentᵉ ,ᵉ
      retraction-splitting-type-is-quasicoherently-idempotentᵉ)

  splitting-is-quasicoherently-idempotentᵉ : retractsᵉ lᵉ Aᵉ
  splitting-is-quasicoherently-idempotentᵉ =
    ( splitting-type-is-quasicoherently-idempotentᵉ ,ᵉ
      retract-splitting-type-is-quasicoherently-idempotentᵉ)

  is-split-idempotent-is-quasicoherently-idempotentᵉ :
    is-split-idempotentᵉ lᵉ fᵉ
  is-split-idempotent-is-quasicoherently-idempotentᵉ =
    ( splitting-type-is-quasicoherently-idempotentᵉ ,ᵉ
      retract-splitting-type-is-quasicoherently-idempotentᵉ ,ᵉ
      htpy-is-split-idempotent-is-quasicoherently-idempotentᵉ)
```

Weᵉ record theseᵉ sameᵉ factsᵉ forᵉ theᵉ bundledᵉ data ofᵉ aᵉ quasicoherentlyᵉ idempotentᵉ
mapᵉ onᵉ `A`.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (fᵉ : quasicoherently-idempotent-mapᵉ Aᵉ)
  where

  splitting-type-quasicoherently-idempotent-mapᵉ : UUᵉ lᵉ
  splitting-type-quasicoherently-idempotent-mapᵉ =
    splitting-type-is-quasicoherently-idempotentᵉ
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-mapᵉ fᵉ)

  inclusion-splitting-type-quasicoherently-idempotent-mapᵉ :
    splitting-type-quasicoherently-idempotent-mapᵉ → Aᵉ
  inclusion-splitting-type-quasicoherently-idempotent-mapᵉ =
    inclusion-splitting-type-is-quasicoherently-idempotentᵉ
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-mapᵉ fᵉ)

  map-retraction-splitting-type-quasicoherently-idempotent-mapᵉ :
    Aᵉ → splitting-type-quasicoherently-idempotent-mapᵉ
  map-retraction-splitting-type-quasicoherently-idempotent-mapᵉ =
    map-retraction-splitting-type-is-quasicoherently-idempotentᵉ
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-mapᵉ fᵉ)

  is-retraction-map-retraction-splitting-type-quasicoherently-idempotent-mapᵉ :
    is-retractionᵉ
      ( inclusion-splitting-type-quasicoherently-idempotent-mapᵉ)
      ( map-retraction-splitting-type-quasicoherently-idempotent-mapᵉ)
  is-retraction-map-retraction-splitting-type-quasicoherently-idempotent-mapᵉ =
    is-retraction-map-retraction-splitting-type-is-quasicoherently-idempotentᵉ
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-mapᵉ fᵉ)

  retraction-splitting-type-quasicoherently-idempotent-mapᵉ :
    retractionᵉ (inclusion-splitting-type-quasicoherently-idempotent-mapᵉ)
  retraction-splitting-type-quasicoherently-idempotent-mapᵉ =
    retraction-splitting-type-is-quasicoherently-idempotentᵉ
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-mapᵉ fᵉ)

  retract-splitting-type-quasicoherently-idempotent-mapᵉ :
    splitting-type-quasicoherently-idempotent-mapᵉ retract-ofᵉ Aᵉ
  retract-splitting-type-quasicoherently-idempotent-mapᵉ =
    retract-splitting-type-is-quasicoherently-idempotentᵉ
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-mapᵉ fᵉ)

  splitting-quasicoherently-idempotent-mapᵉ : retractsᵉ lᵉ Aᵉ
  splitting-quasicoherently-idempotent-mapᵉ =
    splitting-is-quasicoherently-idempotentᵉ
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-mapᵉ fᵉ)

  htpy-is-split-idempotent-quasicoherently-idempotent-mapᵉ :
    inclusion-splitting-type-quasicoherently-idempotent-mapᵉ ∘ᵉ
    map-retraction-splitting-type-quasicoherently-idempotent-mapᵉ ~ᵉ
    map-quasicoherently-idempotent-mapᵉ fᵉ
  htpy-is-split-idempotent-quasicoherently-idempotent-mapᵉ =
    htpy-is-split-idempotent-is-quasicoherently-idempotentᵉ
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-mapᵉ fᵉ)

  is-split-idempotent-quasicoherently-idempotent-mapᵉ :
    is-split-idempotentᵉ lᵉ (map-quasicoherently-idempotent-mapᵉ fᵉ)
  is-split-idempotent-quasicoherently-idempotent-mapᵉ =
    is-split-idempotent-is-quasicoherently-idempotentᵉ
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-mapᵉ fᵉ)
```

### If a map is split idempotent at any universe level, it is split idempotent at its own universe level

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {fᵉ : Aᵉ → Aᵉ} (Sᵉ : is-split-idempotentᵉ l2ᵉ fᵉ)
  where

  is-small-split-idempotent-is-split-idempotentᵉ :
    is-split-idempotentᵉ l1ᵉ fᵉ
  is-small-split-idempotent-is-split-idempotentᵉ =
    is-split-idempotent-is-quasicoherently-idempotentᵉ
      ( is-quasicoherently-idempotent-is-split-idempotentᵉ Sᵉ)
```

### Small types are closed under retracts

<!-- TODO: move this somewhere more fitting. Currently moving it to foundation.small-types introduces cyclic dependencies -->

Thisᵉ isᵉ Theoremᵉ 2.13ᵉ ofᵉ {{#citeᵉ dJE23}}.ᵉ Note,ᵉ in particular,ᵉ thatᵉ itᵉ doesᵉ notᵉ
relyᵉ onᵉ univalence.ᵉ

**Proof:**ᵉ Assumeᵉ givenᵉ anᵉ inclusion-retractionᵉ pairᵉ `iᵉ ,ᵉ r`ᵉ thatᵉ displaysᵉ `B`ᵉ
asᵉ aᵉ retractᵉ ofᵉ theᵉ smallᵉ typeᵉ `A`.ᵉ Byᵉ essentialᵉ uniquenessᵉ ofᵉ splittingᵉ types,ᵉ
`B`ᵉ isᵉ equivalentᵉ to everyᵉ otherᵉ splittingᵉ typeᵉ ofᵉ `iᵉ ∘ᵉ r`.ᵉ Now,ᵉ anotherᵉ
splittingᵉ typeᵉ ofᵉ `iᵉ ∘ᵉ r`ᵉ isᵉ theᵉ splittingᵉ typeᵉ asᵉ constructedᵉ forᵉ theᵉ witnessᵉ

```text
  is-split-idempotent-is-quasicoherently-idempotentᵉ
    ( is-quasicoherently-idempotent-inclusion-retractionᵉ iᵉ rᵉ ...),ᵉ
```

andᵉ thisᵉ isᵉ aᵉ smallᵉ sequentialᵉ limit.ᵉ Henceᵉ `B`ᵉ isᵉ equivalentᵉ to aᵉ smallᵉ type,ᵉ
andᵉ soᵉ isᵉ itselfᵉ small.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-small-retract'ᵉ : Bᵉ retract-ofᵉ Aᵉ → is-smallᵉ l1ᵉ Bᵉ
  pr1ᵉ (is-small-retract'ᵉ Rᵉ) =
    splitting-type-is-quasicoherently-idempotent'ᵉ
      ( inclusion-retractᵉ Rᵉ ∘ᵉ map-retraction-retractᵉ Rᵉ)
  pr2ᵉ (is-small-retract'ᵉ Rᵉ) =
    essentially-unique-splitting-type-is-split-idempotentᵉ
      ( Bᵉ ,ᵉ Rᵉ ,ᵉ refl-htpyᵉ)
      ( is-split-idempotent-is-quasicoherently-idempotentᵉ
        ( is-quasicoherently-idempotent-inclusion-retractionᵉ
          ( inclusion-retractᵉ Rᵉ)
          ( map-retraction-retractᵉ Rᵉ)
          ( is-retraction-map-retraction-retractᵉ Rᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-small-retractᵉ : is-smallᵉ l3ᵉ Aᵉ → Bᵉ retract-ofᵉ Aᵉ → is-smallᵉ l3ᵉ Bᵉ
  is-small-retractᵉ is-small-Aᵉ rᵉ =
    is-small-retract'ᵉ
      ( comp-retractᵉ (retract-equivᵉ (equiv-is-smallᵉ is-small-Aᵉ)) rᵉ)
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ Shu17ᵉ}} {{#referenceᵉ Shu14SplittingIdempotentsᵉ}}