# Infinitely coherent equivalences

```agda
{-# OPTIONSᵉ --guardednessᵉ --lossy-unificationᵉ #-}

module foundation.infinitely-coherent-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.transposition-identifications-along-equivalencesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ {{#conceptᵉ "infinitelyᵉ coherentᵉ equivalence"ᵉ Agda=_≃∞ᵉ_}} `eᵉ : Aᵉ ≃∞ᵉ B`ᵉ fromᵉ
`A`ᵉ to `B`ᵉ consistsᵉ ofᵉ mapsᵉ

```text
  fᵉ : Aᵉ → Bᵉ
  gᵉ : Bᵉ → Aᵉ
```

andᵉ forᵉ eachᵉ `xᵉ : A`ᵉ andᵉ `yᵉ : B`ᵉ anᵉ infinitelyᵉ coherentᵉ equivalenceᵉ

```text
  ∞-equiv-transpose-eq-∞-equivᵉ : (fᵉ xᵉ ＝ᵉ yᵉ) ≃∞ᵉ (xᵉ ＝ᵉ gᵉ y).ᵉ
```

Sinceᵉ thisᵉ definitionᵉ isᵉ infinite,ᵉ itᵉ followsᵉ thatᵉ forᵉ anyᵉ `xᵉ : A`ᵉ andᵉ `yᵉ : B`ᵉ
weᵉ haveᵉ mapsᵉ

```text
  f'ᵉ : (fᵉ xᵉ ＝ᵉ yᵉ) → (xᵉ ＝ᵉ gᵉ yᵉ)
  g'ᵉ : (xᵉ ＝ᵉ gᵉ yᵉ) → (fᵉ xᵉ ＝ᵉ yᵉ)
```

andᵉ forᵉ eachᵉ `pᵉ : fᵉ xᵉ ＝ᵉ y`ᵉ andᵉ `qᵉ : gᵉ yᵉ ＝ᵉ x`ᵉ anᵉ infinitelyᵉ coherentᵉ
equivalenceᵉ

```text
∞-equiv-transpose-eq-∞-equivᵉ : (f'ᵉ pᵉ ＝ᵉ qᵉ) ≃∞ᵉ (pᵉ ＝ᵉ g'ᵉ q).ᵉ
```

Inᵉ particular,ᵉ weᵉ haveᵉ identificationsᵉ

```text
  invᵉ (f'ᵉ xᵉ (fᵉ xᵉ) reflᵉ) : xᵉ = gᵉ (fᵉ xᵉ)
        g'ᵉ yᵉ (gᵉ yᵉ) reflᵉ : fᵉ (gᵉ yᵉ) ＝ᵉ y,ᵉ
```

whichᵉ areᵉ theᵉ usualᵉ homotopiesᵉ witnessingᵉ thatᵉ `g`ᵉ isᵉ aᵉ retractionᵉ andᵉ aᵉ sectionᵉ
ofᵉ `f`.ᵉ Byᵉ infinitelyᵉ imposingᵉ theᵉ structureᵉ ofᵉ aᵉ coherentᵉ equivalence,ᵉ weᵉ haveᵉ
statedᵉ anᵉ infiniteᵉ hierarchyᵉ ofᵉ coherenceᵉ conditions.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ
infiniteᵉ conditionᵉ onᵉ infinitelyᵉ coherentᵉ equivalencesᵉ isᵉ aᵉ wayᵉ ofᵉ statingᵉ
infiniteᵉ coherenceᵉ forᵉ equivalences.ᵉ

Beingᵉ anᵉ infinitelyᵉ coherentᵉ equivalenceᵉ isᵉ anᵉ inverseᵉ sequentialᵉ limitᵉ ofᵉ theᵉ
diagramᵉ

```text
  ... --->ᵉ is-finitely-coherent-equivalenceᵉ 1 fᵉ --->ᵉ is-finitely-coherent-equivalenceᵉ 0 f.ᵉ
```

## Definitions

### The predicate of being an infinitely coherent equivalence

```agda
record is-∞-equivᵉ
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  where
  coinductiveᵉ
  field
    map-inv-is-∞-equivᵉ : Bᵉ → Aᵉ
    map-transpose-is-∞-equivᵉ :
      (xᵉ : Aᵉ) (yᵉ : Bᵉ) → fᵉ xᵉ ＝ᵉ yᵉ → xᵉ ＝ᵉ map-inv-is-∞-equivᵉ yᵉ
    is-∞-equiv-map-transpose-is-∞-equivᵉ :
      (xᵉ : Aᵉ) (yᵉ : Bᵉ) → is-∞-equivᵉ (map-transpose-is-∞-equivᵉ xᵉ yᵉ)

open is-∞-equivᵉ public
```

### Infinitely coherent equivalences

```agda
record
  ∞-equivᵉ
    {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  where
  coinductiveᵉ
  field
    map-∞-equivᵉ : Aᵉ → Bᵉ
    map-inv-∞-equivᵉ : Bᵉ → Aᵉ
    ∞-equiv-transpose-eq-∞-equivᵉ :
      (xᵉ : Aᵉ) (yᵉ : Bᵉ) → ∞-equivᵉ (map-∞-equivᵉ xᵉ ＝ᵉ yᵉ) (xᵉ ＝ᵉ map-inv-∞-equivᵉ yᵉ)

open ∞-equivᵉ public

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  infix 6 _≃∞ᵉ_

  _≃∞ᵉ_ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  _≃∞ᵉ_ = ∞-equivᵉ Aᵉ Bᵉ

∞-equiv-is-∞-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} → is-∞-equivᵉ fᵉ → Aᵉ ≃∞ᵉ Bᵉ
map-∞-equivᵉ (∞-equiv-is-∞-equivᵉ {fᵉ = fᵉ} Hᵉ) = fᵉ
map-inv-∞-equivᵉ (∞-equiv-is-∞-equivᵉ Hᵉ) = map-inv-is-∞-equivᵉ Hᵉ
∞-equiv-transpose-eq-∞-equivᵉ (∞-equiv-is-∞-equivᵉ Hᵉ) xᵉ yᵉ =
  ∞-equiv-is-∞-equivᵉ (is-∞-equiv-map-transpose-is-∞-equivᵉ Hᵉ xᵉ yᵉ)

map-transpose-eq-∞-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃∞ᵉ Bᵉ) →
  (xᵉ : Aᵉ) (yᵉ : Bᵉ) → (map-∞-equivᵉ eᵉ xᵉ ＝ᵉ yᵉ) → (xᵉ ＝ᵉ map-inv-∞-equivᵉ eᵉ yᵉ)
map-transpose-eq-∞-equivᵉ eᵉ xᵉ yᵉ =
  map-∞-equivᵉ (∞-equiv-transpose-eq-∞-equivᵉ eᵉ xᵉ yᵉ)

is-∞-equiv-∞-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃∞ᵉ Bᵉ) →
  is-∞-equivᵉ (map-∞-equivᵉ eᵉ)
map-inv-is-∞-equivᵉ (is-∞-equiv-∞-equivᵉ eᵉ) =
  map-inv-∞-equivᵉ eᵉ
map-transpose-is-∞-equivᵉ (is-∞-equiv-∞-equivᵉ eᵉ) =
  map-transpose-eq-∞-equivᵉ eᵉ
is-∞-equiv-map-transpose-is-∞-equivᵉ (is-∞-equiv-∞-equivᵉ eᵉ) xᵉ yᵉ =
  is-∞-equiv-∞-equivᵉ (∞-equiv-transpose-eq-∞-equivᵉ eᵉ xᵉ yᵉ)

is-∞-equiv-map-transpose-eq-∞-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃∞ᵉ Bᵉ) (xᵉ : Aᵉ) (yᵉ : Bᵉ) →
  is-∞-equivᵉ (map-transpose-eq-∞-equivᵉ eᵉ xᵉ yᵉ)
is-∞-equiv-map-transpose-eq-∞-equivᵉ eᵉ xᵉ yᵉ =
  is-∞-equiv-∞-equivᵉ (∞-equiv-transpose-eq-∞-equivᵉ eᵉ xᵉ yᵉ)
```

### Infinitely coherent identity equivalences

```agda
is-∞-equiv-idᵉ : {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-∞-equivᵉ (idᵉ {Aᵉ = Aᵉ})
map-inv-is-∞-equivᵉ is-∞-equiv-idᵉ = idᵉ
map-transpose-is-∞-equivᵉ is-∞-equiv-idᵉ xᵉ yᵉ = idᵉ
is-∞-equiv-map-transpose-is-∞-equivᵉ is-∞-equiv-idᵉ xᵉ yᵉ = is-∞-equiv-idᵉ

id-∞-equivᵉ : {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → Aᵉ ≃∞ᵉ Aᵉ
id-∞-equivᵉ = ∞-equiv-is-∞-equivᵉ is-∞-equiv-idᵉ
```

### Composition of infinitely coherent equivalences

```agda
is-∞-equiv-compᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {gᵉ : Bᵉ → Cᵉ} {fᵉ : Aᵉ → Bᵉ}
  (Gᵉ : is-∞-equivᵉ gᵉ)
  (Fᵉ : is-∞-equivᵉ fᵉ) →
  is-∞-equivᵉ (gᵉ ∘ᵉ fᵉ)
map-inv-is-∞-equivᵉ (is-∞-equiv-compᵉ Gᵉ Fᵉ) =
  map-inv-is-∞-equivᵉ Fᵉ ∘ᵉ map-inv-is-∞-equivᵉ Gᵉ
map-transpose-is-∞-equivᵉ (is-∞-equiv-compᵉ Gᵉ Fᵉ) xᵉ zᵉ pᵉ =
  map-transpose-is-∞-equivᵉ Fᵉ xᵉ _ (map-transpose-is-∞-equivᵉ Gᵉ _ zᵉ pᵉ)
is-∞-equiv-map-transpose-is-∞-equivᵉ (is-∞-equiv-compᵉ Gᵉ Fᵉ) xᵉ zᵉ =
  is-∞-equiv-compᵉ
    ( is-∞-equiv-map-transpose-is-∞-equivᵉ Fᵉ xᵉ _)
    ( is-∞-equiv-map-transpose-is-∞-equivᵉ Gᵉ _ zᵉ)

comp-∞-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} →
  Bᵉ ≃∞ᵉ Cᵉ → Aᵉ ≃∞ᵉ Bᵉ → Aᵉ ≃∞ᵉ Cᵉ
comp-∞-equivᵉ fᵉ eᵉ =
  ∞-equiv-is-∞-equivᵉ
    ( is-∞-equiv-compᵉ (is-∞-equiv-∞-equivᵉ fᵉ) (is-∞-equiv-∞-equivᵉ eᵉ))
```

### Infinitely coherent equivalences obtained from equivalences

Sinceᵉ
[transposingᵉ identificationsᵉ alongᵉ anᵉ equivalence](foundation.transposition-identifications-along-equivalences.mdᵉ)
isᵉ anᵉ equivalence,ᵉ itᵉ followsᵉ immediatelyᵉ thatᵉ equivalencesᵉ areᵉ infinitelyᵉ
coherentᵉ equivalences.ᵉ Thisᵉ argumentᵉ doesᵉ notᵉ requireᵉ
[functionᵉ extensionality](foundation.function-extensionality.md).ᵉ

```agda
is-∞-equiv-is-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} →
  is-equivᵉ fᵉ → is-∞-equivᵉ fᵉ
map-inv-is-∞-equivᵉ (is-∞-equiv-is-equivᵉ Hᵉ) =
  map-inv-is-equivᵉ Hᵉ
map-transpose-is-∞-equivᵉ (is-∞-equiv-is-equivᵉ Hᵉ) xᵉ yᵉ =
  map-eq-transpose-equivᵉ (ᵉ_ ,ᵉ Hᵉ)
is-∞-equiv-map-transpose-is-∞-equivᵉ (is-∞-equiv-is-equivᵉ Hᵉ) xᵉ yᵉ =
  is-∞-equiv-is-equivᵉ (is-equiv-map-equivᵉ (eq-transpose-equivᵉ (ᵉ_ ,ᵉ Hᵉ) xᵉ yᵉ))

∞-equiv-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → Aᵉ ≃ᵉ Bᵉ → Aᵉ ≃∞ᵉ Bᵉ
∞-equiv-equivᵉ eᵉ =
  ∞-equiv-is-∞-equivᵉ (is-∞-equiv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ))
```

## Properties

### Any map homotopic to an infinitely coherent equivalence is an infinitely coherent equivalence

```agda
is-∞-equiv-htpyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ gᵉ : Aᵉ → Bᵉ} →
  fᵉ ~ᵉ gᵉ →
  is-∞-equivᵉ fᵉ → is-∞-equivᵉ gᵉ
map-inv-is-∞-equivᵉ (is-∞-equiv-htpyᵉ Hᵉ Kᵉ) =
  map-inv-is-∞-equivᵉ Kᵉ
map-transpose-is-∞-equivᵉ (is-∞-equiv-htpyᵉ Hᵉ Kᵉ) xᵉ yᵉ =
  map-transpose-is-∞-equivᵉ Kᵉ xᵉ yᵉ ∘ᵉ concatᵉ (Hᵉ xᵉ) _
is-∞-equiv-map-transpose-is-∞-equivᵉ (is-∞-equiv-htpyᵉ Hᵉ Kᵉ) xᵉ yᵉ =
  is-∞-equiv-compᵉ
    ( is-∞-equiv-map-transpose-is-∞-equivᵉ Kᵉ xᵉ yᵉ)
    ( is-∞-equiv-is-equivᵉ (is-equiv-concatᵉ (Hᵉ xᵉ) _))
```

### Homotopies of elements of type `is-∞-equiv f`

Considerᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ considerᵉ twoᵉ elementsᵉ

```text
  Hᵉ Kᵉ : is-∞-equivᵉ f.ᵉ
```

Aᵉ {{#conceptᵉ "homotopyᵉ ofᵉ elmentsᵉ ofᵉ typeᵉ `is-∞-equiv`"ᵉ Agda=htpy-is-∞-equivᵉ}}
fromᵉ `Hᵉ :=ᵉ (hᵉ ,ᵉ sᵉ ,ᵉ H')`ᵉ to `Kᵉ :=ᵉ (kᵉ ,ᵉ tᵉ ,ᵉ K')`ᵉ consistsᵉ ofᵉ aᵉ homotopyᵉ

```text
  α₀ᵉ : hᵉ ~ᵉ k,ᵉ
```

forᵉ eachᵉ `xᵉ : A`ᵉ andᵉ `yᵉ : B`ᵉ aᵉ homotopyᵉ `α₁`ᵉ witnessingᵉ thatᵉ theᵉ triangleᵉ

```text
               (fᵉ xᵉ = yᵉ)
              /ᵉ         \ᵉ
       sᵉ xᵉ yᵉ /ᵉ           \ᵉ tᵉ xᵉ yᵉ
            /ᵉ             \ᵉ
           ∨ᵉ               ∨ᵉ
  (xᵉ = hᵉ yᵉ) -------------->ᵉ (xᵉ = kᵉ yᵉ)
             pᵉ ↦ᵉ pᵉ ∙ᵉ α₀ᵉ yᵉ
```

commutes,ᵉ andᵉ finallyᵉ aᵉ homotopyᵉ ofᵉ elementsᵉ ofᵉ typeᵉ

```text
  is-infinitely-coherent-equivalenceᵉ
    ( is-∞-equiv-htpyᵉ α₁ᵉ
      ( is-∞-equiv-compᵉ
        ( is-∞-equiv-is-equivᵉ
          ( is-equiv-concat'ᵉ _ (α₀ᵉ yᵉ)))
        ( H'ᵉ xᵉ yᵉ))
    ( K'ᵉ xᵉ y).ᵉ
```

Inᵉ otherᵉ words,ᵉ thereᵉ areᵉ byᵉ theᵉ previousᵉ data twoᵉ witnessesᵉ ofᵉ theᵉ factᵉ thatᵉ
`tᵉ xᵉ y`ᵉ isᵉ anᵉ infinitelyᵉ coherentᵉ equivalence.ᵉ Theᵉ secondᵉ (easiestᵉ) elementᵉ isᵉ
theᵉ givenᵉ elementᵉ `K'ᵉ xᵉ y`.ᵉ Theᵉ firstᵉ elementᵉ isᵉ fromᵉ theᵉ homotopyᵉ witnessingᵉ
thatᵉ theᵉ aboveᵉ triangleᵉ commutes.ᵉ Onᵉ theᵉ leftᵉ weᵉ composeᵉ twoᵉ infinitelyᵉ coherentᵉ
equivalences,ᵉ whichᵉ resultsᵉ in anᵉ infinitelyᵉ coherentᵉ equivalence,ᵉ andᵉ theᵉ
elementᵉ witnessingᵉ thatᵉ theᵉ compositeᵉ isᵉ anᵉ infinitelyᵉ coherentᵉ equivalenceᵉ
transportsᵉ alongᵉ theᵉ homotopyᵉ to aᵉ newᵉ elementᵉ witnessingᵉ thatᵉ `tᵉ xᵉ y`ᵉ isᵉ anᵉ
infinitelyᵉ coherentᵉ equivalence.ᵉ

```agda
record
  htpy-is-∞-equivᵉ
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
    (Hᵉ Kᵉ : is-∞-equivᵉ fᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  where
  coinductiveᵉ
  field
    htpy-map-inv-htpy-is-∞-equivᵉ :
      map-inv-is-∞-equivᵉ Hᵉ ~ᵉ map-inv-is-∞-equivᵉ Kᵉ
    htpy-map-transpose-htpy-is-∞-equivᵉ :
      (xᵉ : Aᵉ) (yᵉ : Bᵉ) →
      coherence-triangle-mapsᵉ
        ( map-transpose-is-∞-equivᵉ Kᵉ xᵉ yᵉ)
        ( concat'ᵉ _ (htpy-map-inv-htpy-is-∞-equivᵉ yᵉ))
        ( map-transpose-is-∞-equivᵉ Hᵉ xᵉ yᵉ)
    infinitely-htpy-htpy-is-∞-equivᵉ :
      (xᵉ : Aᵉ) (yᵉ : Bᵉ) →
      htpy-is-∞-equivᵉ
        ( map-transpose-is-∞-equivᵉ Kᵉ xᵉ yᵉ)
        ( is-∞-equiv-htpyᵉ
          ( inv-htpyᵉ (htpy-map-transpose-htpy-is-∞-equivᵉ xᵉ yᵉ))
          ( is-∞-equiv-compᵉ
            ( is-∞-equiv-is-equivᵉ (is-equiv-concat'ᵉ _ _))
            ( is-∞-equiv-map-transpose-is-∞-equivᵉ Hᵉ xᵉ yᵉ)))
        ( is-∞-equiv-map-transpose-is-∞-equivᵉ Kᵉ xᵉ yᵉ)
```

### Being an infinitely coherent equivalence implies being an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  is-equiv-is-∞-equivᵉ : is-∞-equivᵉ fᵉ → is-equivᵉ fᵉ
  is-equiv-is-∞-equivᵉ Hᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-is-∞-equivᵉ Hᵉ)
      ( λ yᵉ →
        map-inv-is-∞-equivᵉ (is-∞-equiv-map-transpose-is-∞-equivᵉ Hᵉ _ yᵉ) reflᵉ)
      ( λ xᵉ → invᵉ (map-transpose-is-∞-equivᵉ Hᵉ xᵉ (fᵉ xᵉ) reflᵉ))
```

### Computing the type `is-∞-equiv f`

```agda
type-compute-is-∞-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-compute-is-∞-equivᵉ {Aᵉ = Aᵉ} {Bᵉ} fᵉ =
  Σᵉ (Bᵉ → Aᵉ) (λ gᵉ → (xᵉ : Aᵉ) (yᵉ : Bᵉ) → Σᵉ ((fᵉ xᵉ ＝ᵉ yᵉ) → (xᵉ ＝ᵉ gᵉ yᵉ)) is-∞-equivᵉ)

map-compute-is-∞-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  type-compute-is-∞-equivᵉ fᵉ → is-∞-equivᵉ fᵉ
map-inv-is-∞-equivᵉ (map-compute-is-∞-equivᵉ fᵉ Hᵉ) =
  pr1ᵉ Hᵉ
map-transpose-is-∞-equivᵉ (map-compute-is-∞-equivᵉ fᵉ Hᵉ) xᵉ yᵉ =
  pr1ᵉ (pr2ᵉ Hᵉ xᵉ yᵉ)
is-∞-equiv-map-transpose-is-∞-equivᵉ (map-compute-is-∞-equivᵉ fᵉ Hᵉ) xᵉ yᵉ =
  pr2ᵉ (pr2ᵉ Hᵉ xᵉ yᵉ)

map-inv-compute-is-∞-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-∞-equivᵉ fᵉ → type-compute-is-∞-equivᵉ fᵉ
pr1ᵉ (map-inv-compute-is-∞-equivᵉ fᵉ Hᵉ) =
  map-inv-is-∞-equivᵉ Hᵉ
pr1ᵉ (pr2ᵉ (map-inv-compute-is-∞-equivᵉ fᵉ Hᵉ) xᵉ yᵉ) =
  map-transpose-is-∞-equivᵉ Hᵉ xᵉ yᵉ
pr2ᵉ (pr2ᵉ (map-inv-compute-is-∞-equivᵉ fᵉ Hᵉ) xᵉ yᵉ) =
  is-∞-equiv-map-transpose-is-∞-equivᵉ Hᵉ xᵉ yᵉ
```

### Being an infinitely coherent equivalence is a property

```text
is-prop-is-∞-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-propᵉ (is-∞-equivᵉ fᵉ)
is-prop-is-∞-equivᵉ = {!!ᵉ}
```