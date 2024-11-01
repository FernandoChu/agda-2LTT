# Equivalences

```agda
module foundation-core.equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.coherently-invertible-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.invertible-mapsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
```

</details>

## Idea

An **equivalence** is a map that has a [section](foundation-core.sections.md)
and a (separate) [retraction](foundation-core.retractions.md). This condition is
also called being **biinvertible**.

The condition of biinvertibility may look odd: Why not say that an equivalence
is a map that has a [2-sided inverse](foundation-core.invertible-maps.md)? The
reason is that the condition of invertibility is
[structure](foundation.structure.md), whereas the condition of being
biinvertible is a [property](foundation-core.propositions.md). To quickly see
this: if `f` is an equivalence, then it has up to
[homotopy](foundation-core.homotopies.md) only one section, and it has up to
homotopy only one retraction.

## Definition

### The predicate of being an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-equivᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-equivᵉ fᵉ = sectionᵉ fᵉ ×ᵉ retractionᵉ fᵉ
```

### Components of a proof of equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} (Hᵉ : is-equivᵉ fᵉ)
  where

  section-is-equivᵉ : sectionᵉ fᵉ
  section-is-equivᵉ = pr1ᵉ Hᵉ

  retraction-is-equivᵉ : retractionᵉ fᵉ
  retraction-is-equivᵉ = pr2ᵉ Hᵉ

  map-section-is-equivᵉ : Bᵉ → Aᵉ
  map-section-is-equivᵉ = map-sectionᵉ fᵉ section-is-equivᵉ

  map-retraction-is-equivᵉ : Bᵉ → Aᵉ
  map-retraction-is-equivᵉ = map-retractionᵉ fᵉ retraction-is-equivᵉ

  is-section-map-section-is-equivᵉ : is-sectionᵉ fᵉ map-section-is-equivᵉ
  is-section-map-section-is-equivᵉ = is-section-map-sectionᵉ fᵉ section-is-equivᵉ

  is-retraction-map-retraction-is-equivᵉ :
    is-retractionᵉ fᵉ map-retraction-is-equivᵉ
  is-retraction-map-retraction-is-equivᵉ =
    is-retraction-map-retractionᵉ fᵉ retraction-is-equivᵉ
```

### Equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  equivᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equivᵉ = Σᵉ (Aᵉ → Bᵉ) is-equivᵉ

infix 6 _≃ᵉ_

_≃ᵉ_ : {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
Aᵉ ≃ᵉ Bᵉ = equivᵉ Aᵉ Bᵉ
```

### Components of an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  map-equivᵉ : Aᵉ → Bᵉ
  map-equivᵉ = pr1ᵉ eᵉ

  is-equiv-map-equivᵉ : is-equivᵉ map-equivᵉ
  is-equiv-map-equivᵉ = pr2ᵉ eᵉ

  section-map-equivᵉ : sectionᵉ map-equivᵉ
  section-map-equivᵉ = section-is-equivᵉ is-equiv-map-equivᵉ

  map-section-map-equivᵉ : Bᵉ → Aᵉ
  map-section-map-equivᵉ = map-sectionᵉ map-equivᵉ section-map-equivᵉ

  is-section-map-section-map-equivᵉ :
    is-sectionᵉ map-equivᵉ map-section-map-equivᵉ
  is-section-map-section-map-equivᵉ =
    is-section-map-sectionᵉ map-equivᵉ section-map-equivᵉ

  retraction-map-equivᵉ : retractionᵉ map-equivᵉ
  retraction-map-equivᵉ = retraction-is-equivᵉ is-equiv-map-equivᵉ

  map-retraction-map-equivᵉ : Bᵉ → Aᵉ
  map-retraction-map-equivᵉ = map-retractionᵉ map-equivᵉ retraction-map-equivᵉ

  is-retraction-map-retraction-map-equivᵉ :
    is-retractionᵉ map-equivᵉ map-retraction-map-equivᵉ
  is-retraction-map-retraction-map-equivᵉ =
    is-retraction-map-retractionᵉ map-equivᵉ retraction-map-equivᵉ
```

### The identity equivalence

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-equiv-idᵉ : is-equivᵉ (idᵉ {lᵉ} {Aᵉ})
  pr1ᵉ (pr1ᵉ is-equiv-idᵉ) = idᵉ
  pr2ᵉ (pr1ᵉ is-equiv-idᵉ) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ is-equiv-idᵉ) = idᵉ
  pr2ᵉ (pr2ᵉ is-equiv-idᵉ) = refl-htpyᵉ

  id-equivᵉ : Aᵉ ≃ᵉ Aᵉ
  pr1ᵉ id-equivᵉ = idᵉ
  pr2ᵉ id-equivᵉ = is-equiv-idᵉ
```

## Properties

### A map is invertible if and only if it is an equivalence

**Proof:** It is clear that if a map is
[invertible](foundation-core.invertible-maps.md), then it is also biinvertible,
and hence an equivalence.

For the converse, suppose that `f : A → B` is an equivalence with section
`g : B → A` equipped with `G : f ∘ g ~ id`, and retraction `h : B → A` equipped
with `H : h ∘ f ~ id`. We claim that the map `g : B → A` is also a retraction.
To see this, we concatenate the following homotopies

```text
         H⁻¹ ·r g ·r f                  h ·l G ·r f           H
  g ∘ h ---------------> h ∘ f ∘ g ∘ f -------------> h ∘ f -----> id.
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  is-equiv-is-invertible'ᵉ : is-invertibleᵉ fᵉ → is-equivᵉ fᵉ
  is-equiv-is-invertible'ᵉ (gᵉ ,ᵉ Hᵉ ,ᵉ Kᵉ) = ((gᵉ ,ᵉ Hᵉ) ,ᵉ (gᵉ ,ᵉ Kᵉ))

  is-equiv-is-invertibleᵉ :
    (gᵉ : Bᵉ → Aᵉ) (Hᵉ : fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ) (Kᵉ : gᵉ ∘ᵉ fᵉ ~ᵉ idᵉ) → is-equivᵉ fᵉ
  is-equiv-is-invertibleᵉ gᵉ Hᵉ Kᵉ = is-equiv-is-invertible'ᵉ (gᵉ ,ᵉ Hᵉ ,ᵉ Kᵉ)

  is-retraction-map-section-is-equivᵉ :
    (Hᵉ : is-equivᵉ fᵉ) → is-retractionᵉ fᵉ (map-section-is-equivᵉ Hᵉ)
  is-retraction-map-section-is-equivᵉ Hᵉ =
    ( ( inv-htpyᵉ
        ( ( is-retraction-map-retraction-is-equivᵉ Hᵉ) ·rᵉ
          ( map-section-is-equivᵉ Hᵉ ∘ᵉ fᵉ))) ∙hᵉ
      ( map-retraction-is-equivᵉ Hᵉ ·lᵉ is-section-map-section-is-equivᵉ Hᵉ ·rᵉ fᵉ)) ∙hᵉ
    ( is-retraction-map-retraction-is-equivᵉ Hᵉ)

  is-invertible-is-equivᵉ : is-equivᵉ fᵉ → is-invertibleᵉ fᵉ
  pr1ᵉ (is-invertible-is-equivᵉ Hᵉ) = map-section-is-equivᵉ Hᵉ
  pr1ᵉ (pr2ᵉ (is-invertible-is-equivᵉ Hᵉ)) = is-section-map-section-is-equivᵉ Hᵉ
  pr2ᵉ (pr2ᵉ (is-invertible-is-equivᵉ Hᵉ)) = is-retraction-map-section-is-equivᵉ Hᵉ
```

### Coherently invertible maps are equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  is-equiv-is-coherently-invertibleᵉ :
    is-coherently-invertibleᵉ fᵉ → is-equivᵉ fᵉ
  is-equiv-is-coherently-invertibleᵉ Hᵉ =
    is-equiv-is-invertible'ᵉ (is-invertible-is-coherently-invertibleᵉ Hᵉ)

  is-equiv-is-transpose-coherently-invertibleᵉ :
    is-transpose-coherently-invertibleᵉ fᵉ → is-equivᵉ fᵉ
  is-equiv-is-transpose-coherently-invertibleᵉ Hᵉ =
    is-equiv-is-invertible'ᵉ
      ( is-invertible-is-transpose-coherently-invertibleᵉ Hᵉ)
```

The following maps are not simple constructions and should not be computed with.
Therefore, we mark them as `abstract`.

```agda
  abstract
    is-coherently-invertible-is-equivᵉ :
      is-equivᵉ fᵉ → is-coherently-invertibleᵉ fᵉ
    is-coherently-invertible-is-equivᵉ =
      is-coherently-invertible-is-invertibleᵉ ∘ᵉ is-invertible-is-equivᵉ

  abstract
    is-transpose-coherently-invertible-is-equivᵉ :
      is-equivᵉ fᵉ → is-transpose-coherently-invertibleᵉ fᵉ
    is-transpose-coherently-invertible-is-equivᵉ =
      is-transpose-coherently-invertible-is-invertibleᵉ ∘ᵉ is-invertible-is-equivᵉ
```

### Structure obtained from being coherently invertible

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} (Hᵉ : is-equivᵉ fᵉ)
  where

  map-inv-is-equivᵉ : Bᵉ → Aᵉ
  map-inv-is-equivᵉ = pr1ᵉ (is-invertible-is-equivᵉ Hᵉ)

  is-section-map-inv-is-equivᵉ : is-sectionᵉ fᵉ map-inv-is-equivᵉ
  is-section-map-inv-is-equivᵉ =
    is-section-map-inv-is-coherently-invertible-is-invertibleᵉ
      ( is-invertible-is-equivᵉ Hᵉ)

  is-retraction-map-inv-is-equivᵉ : is-retractionᵉ fᵉ map-inv-is-equivᵉ
  is-retraction-map-inv-is-equivᵉ =
    is-retraction-map-inv-is-coherently-invertible-is-invertibleᵉ
      ( is-invertible-is-equivᵉ Hᵉ)

  coherence-map-inv-is-equivᵉ :
    coherence-is-coherently-invertibleᵉ fᵉ
      ( map-inv-is-equivᵉ)
      ( is-section-map-inv-is-equivᵉ)
      ( is-retraction-map-inv-is-equivᵉ)
  coherence-map-inv-is-equivᵉ =
    coh-is-coherently-invertible-is-invertibleᵉ (is-invertible-is-equivᵉ Hᵉ)

  is-equiv-map-inv-is-equivᵉ : is-equivᵉ map-inv-is-equivᵉ
  is-equiv-map-inv-is-equivᵉ =
    is-equiv-is-invertibleᵉ fᵉ
      ( is-retraction-map-inv-is-equivᵉ)
      ( is-section-map-inv-is-equivᵉ)
```

### The inverse of an equivalence is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  map-inv-equivᵉ : Bᵉ → Aᵉ
  map-inv-equivᵉ = map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)

  is-section-map-inv-equivᵉ : is-sectionᵉ (map-equivᵉ eᵉ) map-inv-equivᵉ
  is-section-map-inv-equivᵉ = is-section-map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)

  is-retraction-map-inv-equivᵉ : is-retractionᵉ (map-equivᵉ eᵉ) map-inv-equivᵉ
  is-retraction-map-inv-equivᵉ =
    is-retraction-map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)

  coherence-map-inv-equivᵉ :
    coherence-is-coherently-invertibleᵉ
      ( map-equivᵉ eᵉ)
      ( map-inv-equivᵉ)
      ( is-section-map-inv-equivᵉ)
      ( is-retraction-map-inv-equivᵉ)
  coherence-map-inv-equivᵉ =
    coherence-map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)

  is-equiv-map-inv-equivᵉ : is-equivᵉ map-inv-equivᵉ
  is-equiv-map-inv-equivᵉ = is-equiv-map-inv-is-equivᵉ (is-equiv-map-equivᵉ eᵉ)

  inv-equivᵉ : Bᵉ ≃ᵉ Aᵉ
  pr1ᵉ inv-equivᵉ = map-inv-equivᵉ
  pr2ᵉ inv-equivᵉ = is-equiv-map-inv-equivᵉ
```

### The 3-for-2 property of equivalences

The **3-for-2 property** of equivalences asserts that for any
[commuting triangle](foundation-core.commuting-triangles-of-maps.md) of maps

```text
       h
  A ------> B
   \       /
   f\     /g
     \   /
      ∨ ∨
       X,
```

if two of the three maps are equivalences, then so is the third.

We also record special cases of the 3-for-2 property of equivalences, where we
only assume maps `g : B → X` and `h : A → B`. In this special case, we set
`f := g ∘ h` and the triangle commutes by `refl-htpy`.

[André Joyal](https://en.wikipedia.org/wiki/André_Joyal) proposed calling this
property the 3-for-2 property, despite most mathematicians calling it the
_2-out-of-3 property_. The story goes that on the produce market is is common to
advertise a discount as "3-for-2". If you buy two apples, then you get the third
for free. Similarly, if you prove that two maps in a commuting triangle are
equivalences, then you get the third for free.

#### The left map in a commuting triangle is an equivalence if the other two maps are equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Tᵉ : fᵉ ~ᵉ gᵉ ∘ᵉ hᵉ)
  where

  abstract
    is-equiv-left-map-triangleᵉ : is-equivᵉ hᵉ → is-equivᵉ gᵉ → is-equivᵉ fᵉ
    pr1ᵉ (is-equiv-left-map-triangleᵉ Hᵉ Gᵉ) =
      section-left-map-triangleᵉ fᵉ gᵉ hᵉ Tᵉ
        ( section-is-equivᵉ Hᵉ)
        ( section-is-equivᵉ Gᵉ)
    pr2ᵉ (is-equiv-left-map-triangleᵉ Hᵉ Gᵉ) =
      retraction-left-map-triangleᵉ fᵉ gᵉ hᵉ Tᵉ
        ( retraction-is-equivᵉ Gᵉ)
        ( retraction-is-equivᵉ Hᵉ)
```

#### The right map in a commuting triangle is an equivalence if the other two maps are equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ ∘ᵉ hᵉ)
  where

  abstract
    is-equiv-right-map-triangleᵉ :
      is-equivᵉ fᵉ → is-equivᵉ hᵉ → is-equivᵉ gᵉ
    is-equiv-right-map-triangleᵉ
      ( section-fᵉ ,ᵉ retraction-fᵉ)
      ( (shᵉ ,ᵉ is-section-shᵉ) ,ᵉ retraction-hᵉ) =
        ( pairᵉ
          ( section-right-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ section-fᵉ)
          ( retraction-left-map-triangleᵉ gᵉ fᵉ shᵉ
            ( inv-htpyᵉ
              ( ( Hᵉ ·rᵉ map-sectionᵉ hᵉ (shᵉ ,ᵉ is-section-shᵉ)) ∙hᵉ
                ( gᵉ ·lᵉ is-section-map-sectionᵉ hᵉ (shᵉ ,ᵉ is-section-shᵉ))))
            ( retraction-fᵉ)
            ( hᵉ ,ᵉ is-section-shᵉ)))
```

#### If the left and right maps in a commuting triangle are equivalences, then the top map is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ ∘ᵉ hᵉ)
  where

  section-is-equiv-top-map-triangleᵉ :
    is-equivᵉ gᵉ → is-equivᵉ fᵉ → sectionᵉ hᵉ
  section-is-equiv-top-map-triangleᵉ Gᵉ Fᵉ =
    section-left-map-triangleᵉ hᵉ
      ( map-retraction-is-equivᵉ Gᵉ)
      ( fᵉ)
      ( inv-htpyᵉ
        ( ( map-retractionᵉ gᵉ (retraction-is-equivᵉ Gᵉ) ·lᵉ Hᵉ) ∙hᵉ
          ( is-retraction-map-retractionᵉ gᵉ (retraction-is-equivᵉ Gᵉ) ·rᵉ hᵉ)))
      ( section-is-equivᵉ Fᵉ)
      ( gᵉ ,ᵉ is-retraction-map-retraction-is-equivᵉ Gᵉ)

  map-section-is-equiv-top-map-triangleᵉ :
    is-equivᵉ gᵉ → is-equivᵉ fᵉ → Bᵉ → Aᵉ
  map-section-is-equiv-top-map-triangleᵉ Gᵉ Fᵉ =
    map-sectionᵉ hᵉ (section-is-equiv-top-map-triangleᵉ Gᵉ Fᵉ)

  abstract
    is-equiv-top-map-triangleᵉ :
      is-equivᵉ gᵉ → is-equivᵉ fᵉ → is-equivᵉ hᵉ
    is-equiv-top-map-triangleᵉ
      ( section-gᵉ ,ᵉ (rgᵉ ,ᵉ is-retraction-rgᵉ))
      ( section-fᵉ ,ᵉ retraction-fᵉ) =
      ( pairᵉ
        ( section-left-map-triangleᵉ hᵉ rgᵉ fᵉ
          ( inv-htpyᵉ
            ( ( map-retractionᵉ gᵉ (rgᵉ ,ᵉ is-retraction-rgᵉ) ·lᵉ Hᵉ) ∙hᵉ
              ( is-retraction-map-retractionᵉ gᵉ (rgᵉ ,ᵉ is-retraction-rgᵉ) ·rᵉ hᵉ)))
          ( section-fᵉ)
          ( gᵉ ,ᵉ is-retraction-rgᵉ))
        ( retraction-top-map-triangleᵉ fᵉ gᵉ hᵉ Hᵉ retraction-fᵉ))
```

#### Composites of equivalences are equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  where

  is-equiv-compᵉ :
    (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) → is-equivᵉ hᵉ → is-equivᵉ gᵉ → is-equivᵉ (gᵉ ∘ᵉ hᵉ)
  pr1ᵉ (is-equiv-compᵉ gᵉ hᵉ (shᵉ ,ᵉ rhᵉ) (sgᵉ ,ᵉ rgᵉ)) = section-compᵉ gᵉ hᵉ shᵉ sgᵉ
  pr2ᵉ (is-equiv-compᵉ gᵉ hᵉ (shᵉ ,ᵉ rhᵉ) (sgᵉ ,ᵉ rgᵉ)) = retraction-compᵉ gᵉ hᵉ rgᵉ rhᵉ

  comp-equivᵉ : Bᵉ ≃ᵉ Xᵉ → Aᵉ ≃ᵉ Bᵉ → Aᵉ ≃ᵉ Xᵉ
  pr1ᵉ (comp-equivᵉ gᵉ hᵉ) = map-equivᵉ gᵉ ∘ᵉ map-equivᵉ hᵉ
  pr2ᵉ (comp-equivᵉ gᵉ hᵉ) = is-equiv-compᵉ (pr1ᵉ gᵉ) (pr1ᵉ hᵉ) (pr2ᵉ hᵉ) (pr2ᵉ gᵉ)

  infixr 15 _∘eᵉ_
  _∘eᵉ_ : Bᵉ ≃ᵉ Xᵉ → Aᵉ ≃ᵉ Bᵉ → Aᵉ ≃ᵉ Xᵉ
  _∘eᵉ_ = comp-equivᵉ
```

#### If a composite and its right factor are equivalences, then so is its left factor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  where

  is-equiv-left-factorᵉ :
    (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) →
    is-equivᵉ (gᵉ ∘ᵉ hᵉ) → is-equivᵉ hᵉ → is-equivᵉ gᵉ
  is-equiv-left-factorᵉ gᵉ hᵉ is-equiv-ghᵉ is-equiv-hᵉ =
      is-equiv-right-map-triangleᵉ (gᵉ ∘ᵉ hᵉ) gᵉ hᵉ refl-htpyᵉ is-equiv-ghᵉ is-equiv-hᵉ
```

#### If a composite and its left factor are equivalences, then so is its right factor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  where

  is-equiv-right-factorᵉ :
    (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) →
    is-equivᵉ gᵉ → is-equivᵉ (gᵉ ∘ᵉ hᵉ) → is-equivᵉ hᵉ
  is-equiv-right-factorᵉ gᵉ hᵉ is-equiv-gᵉ is-equiv-ghᵉ =
    is-equiv-top-map-triangleᵉ (gᵉ ∘ᵉ hᵉ) gᵉ hᵉ refl-htpyᵉ is-equiv-gᵉ is-equiv-ghᵉ
```

### Equivalences are closed under homotopies

We show that if `f ~ g`, then `f` is an equivalence if and only if `g` is an
equivalence. Furthermore, we show that if `f` and `g` are homotopic equivaleces,
then their inverses are also homotopic.

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-equiv-htpyᵉ :
      {fᵉ : Aᵉ → Bᵉ} (gᵉ : Aᵉ → Bᵉ) → fᵉ ~ᵉ gᵉ → is-equivᵉ gᵉ → is-equivᵉ fᵉ
    pr1ᵉ (pr1ᵉ (is-equiv-htpyᵉ gᵉ Gᵉ ((hᵉ ,ᵉ Hᵉ) ,ᵉ (kᵉ ,ᵉ Kᵉ)))) = hᵉ
    pr2ᵉ (pr1ᵉ (is-equiv-htpyᵉ gᵉ Gᵉ ((hᵉ ,ᵉ Hᵉ) ,ᵉ (kᵉ ,ᵉ Kᵉ)))) = (Gᵉ ·rᵉ hᵉ) ∙hᵉ Hᵉ
    pr1ᵉ (pr2ᵉ (is-equiv-htpyᵉ gᵉ Gᵉ ((hᵉ ,ᵉ Hᵉ) ,ᵉ (kᵉ ,ᵉ Kᵉ)))) = kᵉ
    pr2ᵉ (pr2ᵉ (is-equiv-htpyᵉ gᵉ Gᵉ ((hᵉ ,ᵉ Hᵉ) ,ᵉ (kᵉ ,ᵉ Kᵉ)))) = (kᵉ ·lᵉ Gᵉ) ∙hᵉ Kᵉ

  is-equiv-htpy-equivᵉ : {fᵉ : Aᵉ → Bᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) → fᵉ ~ᵉ map-equivᵉ eᵉ → is-equivᵉ fᵉ
  is-equiv-htpy-equivᵉ eᵉ Hᵉ = is-equiv-htpyᵉ (map-equivᵉ eᵉ) Hᵉ (is-equiv-map-equivᵉ eᵉ)

  abstract
    is-equiv-htpy'ᵉ : (fᵉ : Aᵉ → Bᵉ) {gᵉ : Aᵉ → Bᵉ} → fᵉ ~ᵉ gᵉ → is-equivᵉ fᵉ → is-equivᵉ gᵉ
    is-equiv-htpy'ᵉ fᵉ Hᵉ = is-equiv-htpyᵉ fᵉ (inv-htpyᵉ Hᵉ)

  is-equiv-htpy-equiv'ᵉ : (eᵉ : Aᵉ ≃ᵉ Bᵉ) {gᵉ : Aᵉ → Bᵉ} → map-equivᵉ eᵉ ~ᵉ gᵉ → is-equivᵉ gᵉ
  is-equiv-htpy-equiv'ᵉ eᵉ Hᵉ =
    is-equiv-htpy'ᵉ (map-equivᵉ eᵉ) Hᵉ (is-equiv-map-equivᵉ eᵉ)

  htpy-map-inv-is-equivᵉ :
    {fᵉ gᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) (Fᵉ : is-equivᵉ fᵉ) (Gᵉ : is-equivᵉ gᵉ) →
    map-inv-is-equivᵉ Fᵉ ~ᵉ map-inv-is-equivᵉ Gᵉ
  htpy-map-inv-is-equivᵉ Hᵉ Fᵉ Gᵉ =
    htpy-map-inv-is-invertibleᵉ Hᵉ
      ( is-invertible-is-equivᵉ Fᵉ)
      ( is-invertible-is-equivᵉ Gᵉ)
```

### Any retraction of an equivalence is an equivalence

```agda
abstract
  is-equiv-is-retractionᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ} →
    is-equivᵉ fᵉ → (gᵉ ∘ᵉ fᵉ) ~ᵉ idᵉ → is-equivᵉ gᵉ
  is-equiv-is-retractionᵉ {Aᵉ = Aᵉ} {fᵉ = fᵉ} {gᵉ = gᵉ} is-equiv-fᵉ Hᵉ =
    is-equiv-right-map-triangleᵉ idᵉ gᵉ fᵉ (inv-htpyᵉ Hᵉ) is-equiv-idᵉ is-equiv-fᵉ
```

### Any section of an equivalence is an equivalence

```agda
abstract
  is-equiv-is-sectionᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ} →
    is-equivᵉ fᵉ → fᵉ ∘ᵉ gᵉ ~ᵉ idᵉ → is-equivᵉ gᵉ
  is-equiv-is-sectionᵉ {Bᵉ = Bᵉ} {fᵉ = fᵉ} {gᵉ = gᵉ} is-equiv-fᵉ Hᵉ =
    is-equiv-top-map-triangleᵉ idᵉ fᵉ gᵉ (inv-htpyᵉ Hᵉ) is-equiv-fᵉ is-equiv-idᵉ
```

### If a section of `f` is an equivalence, then `f` is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-equiv-is-equiv-sectionᵉ :
      (sᵉ : sectionᵉ fᵉ) → is-equivᵉ (map-sectionᵉ fᵉ sᵉ) → is-equivᵉ fᵉ
    is-equiv-is-equiv-sectionᵉ (gᵉ ,ᵉ Gᵉ) Sᵉ = is-equiv-is-retractionᵉ Sᵉ Gᵉ
```

### If a retraction of `f` is an equivalence, then `f` is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-equiv-is-equiv-retractionᵉ :
      (rᵉ : retractionᵉ fᵉ) → is-equivᵉ (map-retractionᵉ fᵉ rᵉ) → is-equivᵉ fᵉ
    is-equiv-is-equiv-retractionᵉ (gᵉ ,ᵉ Gᵉ) Rᵉ = is-equiv-is-sectionᵉ Rᵉ Gᵉ
```

### Any section of an equivalence is homotopic to its inverse

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  htpy-map-inv-equiv-sectionᵉ :
    (fᵉ : sectionᵉ (map-equivᵉ eᵉ)) → map-inv-equivᵉ eᵉ ~ᵉ map-sectionᵉ (map-equivᵉ eᵉ) fᵉ
  htpy-map-inv-equiv-sectionᵉ (fᵉ ,ᵉ Hᵉ) =
    (map-inv-equivᵉ eᵉ ·lᵉ inv-htpyᵉ Hᵉ) ∙hᵉ (is-retraction-map-inv-equivᵉ eᵉ ·rᵉ fᵉ)
```

### Any retraction of an equivalence is homotopic to its inverse

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  htpy-map-inv-equiv-retractionᵉ :
    (fᵉ : retractionᵉ (map-equivᵉ eᵉ)) →
    map-inv-equivᵉ eᵉ ~ᵉ map-retractionᵉ (map-equivᵉ eᵉ) fᵉ
  htpy-map-inv-equiv-retractionᵉ (fᵉ ,ᵉ Hᵉ) =
    (inv-htpyᵉ Hᵉ ·rᵉ map-inv-equivᵉ eᵉ) ∙hᵉ (fᵉ ·lᵉ is-section-map-inv-equivᵉ eᵉ)
```

### Equivalences in commuting squares

```agda
is-equiv-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  {fᵉ : Aᵉ → Bᵉ} {gᵉ : Xᵉ → Yᵉ} (iᵉ : Aᵉ ≃ᵉ Xᵉ) (jᵉ : Bᵉ ≃ᵉ Yᵉ)
  (Hᵉ : (map-equivᵉ jᵉ ∘ᵉ fᵉ) ~ᵉ (gᵉ ∘ᵉ map-equivᵉ iᵉ)) → is-equivᵉ gᵉ → is-equivᵉ fᵉ
is-equiv-equivᵉ {fᵉ = fᵉ} {gᵉ} iᵉ jᵉ Hᵉ Kᵉ =
  is-equiv-right-factorᵉ
    ( map-equivᵉ jᵉ)
    ( fᵉ)
    ( is-equiv-map-equivᵉ jᵉ)
    ( is-equiv-left-map-triangleᵉ
      ( map-equivᵉ jᵉ ∘ᵉ fᵉ)
      ( gᵉ)
      ( map-equivᵉ iᵉ)
      ( Hᵉ)
      ( is-equiv-map-equivᵉ iᵉ)
      ( Kᵉ))

is-equiv-equiv'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  {fᵉ : Aᵉ → Bᵉ} {gᵉ : Xᵉ → Yᵉ} (iᵉ : Aᵉ ≃ᵉ Xᵉ) (jᵉ : Bᵉ ≃ᵉ Yᵉ)
  (Hᵉ : (map-equivᵉ jᵉ ∘ᵉ fᵉ) ~ᵉ (gᵉ ∘ᵉ map-equivᵉ iᵉ)) → is-equivᵉ fᵉ → is-equivᵉ gᵉ
is-equiv-equiv'ᵉ {fᵉ = fᵉ} {gᵉ} iᵉ jᵉ Hᵉ Kᵉ =
  is-equiv-left-factorᵉ
    ( gᵉ)
    ( map-equivᵉ iᵉ)
    ( is-equiv-left-map-triangleᵉ
      ( gᵉ ∘ᵉ map-equivᵉ iᵉ)
      ( map-equivᵉ jᵉ)
      ( fᵉ)
      ( inv-htpyᵉ Hᵉ)
      ( Kᵉ)
      ( is-equiv-map-equivᵉ jᵉ))
    ( is-equiv-map-equivᵉ iᵉ)
```

We will assume a commuting square

```text
        h
    A -----> C
    |        |
  f |        | g
    ∨        ∨
    B -----> D
        i
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Cᵉ → Dᵉ) (hᵉ : Aᵉ → Cᵉ) (iᵉ : Bᵉ → Dᵉ) (Hᵉ : (iᵉ ∘ᵉ fᵉ) ~ᵉ (gᵉ ∘ᵉ hᵉ))
  where

  abstract
    is-equiv-top-is-equiv-left-squareᵉ :
      is-equivᵉ iᵉ → is-equivᵉ fᵉ → is-equivᵉ gᵉ → is-equivᵉ hᵉ
    is-equiv-top-is-equiv-left-squareᵉ Eiᵉ Efᵉ Egᵉ =
      is-equiv-top-map-triangleᵉ (iᵉ ∘ᵉ fᵉ) gᵉ hᵉ Hᵉ Egᵉ (is-equiv-compᵉ iᵉ fᵉ Efᵉ Eiᵉ)

  abstract
    is-equiv-top-is-equiv-bottom-squareᵉ :
      is-equivᵉ fᵉ → is-equivᵉ gᵉ → is-equivᵉ iᵉ → is-equivᵉ hᵉ
    is-equiv-top-is-equiv-bottom-squareᵉ Efᵉ Egᵉ Eiᵉ =
      is-equiv-top-map-triangleᵉ (iᵉ ∘ᵉ fᵉ) gᵉ hᵉ Hᵉ Egᵉ (is-equiv-compᵉ iᵉ fᵉ Efᵉ Eiᵉ)

  abstract
    is-equiv-bottom-is-equiv-top-squareᵉ :
      is-equivᵉ fᵉ → is-equivᵉ gᵉ → is-equivᵉ hᵉ → is-equivᵉ iᵉ
    is-equiv-bottom-is-equiv-top-squareᵉ Efᵉ Egᵉ Ehᵉ =
      is-equiv-left-factorᵉ iᵉ fᵉ
        ( is-equiv-left-map-triangleᵉ (iᵉ ∘ᵉ fᵉ) gᵉ hᵉ Hᵉ Ehᵉ Egᵉ)
        ( Efᵉ)

  abstract
    is-equiv-left-is-equiv-right-squareᵉ :
      is-equivᵉ hᵉ → is-equivᵉ iᵉ → is-equivᵉ gᵉ → is-equivᵉ fᵉ
    is-equiv-left-is-equiv-right-squareᵉ Ehᵉ Eiᵉ Egᵉ =
      is-equiv-right-factorᵉ iᵉ fᵉ Eiᵉ
        ( is-equiv-left-map-triangleᵉ (iᵉ ∘ᵉ fᵉ) gᵉ hᵉ Hᵉ Ehᵉ Egᵉ)

  abstract
    is-equiv-right-is-equiv-left-squareᵉ :
      is-equivᵉ hᵉ → is-equivᵉ iᵉ → is-equivᵉ fᵉ → is-equivᵉ gᵉ
    is-equiv-right-is-equiv-left-squareᵉ Ehᵉ Eiᵉ Efᵉ =
      is-equiv-right-map-triangleᵉ (iᵉ ∘ᵉ fᵉ) gᵉ hᵉ Hᵉ (is-equiv-compᵉ iᵉ fᵉ Efᵉ Eiᵉ) Ehᵉ
```

### Equivalences are embeddings

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-emb-is-equivᵉ :
      {fᵉ : Aᵉ → Bᵉ} → is-equivᵉ fᵉ → (xᵉ yᵉ : Aᵉ) → is-equivᵉ (apᵉ fᵉ {xᵉ} {yᵉ})
    is-emb-is-equivᵉ Hᵉ xᵉ yᵉ =
      is-equiv-is-invertible'ᵉ
        ( is-invertible-ap-is-coherently-invertibleᵉ
          ( is-coherently-invertible-is-equivᵉ Hᵉ))

  equiv-apᵉ :
    (eᵉ : Aᵉ ≃ᵉ Bᵉ) (xᵉ yᵉ : Aᵉ) → (xᵉ ＝ᵉ yᵉ) ≃ᵉ (map-equivᵉ eᵉ xᵉ ＝ᵉ map-equivᵉ eᵉ yᵉ)
  pr1ᵉ (equiv-apᵉ eᵉ xᵉ yᵉ) = apᵉ (map-equivᵉ eᵉ)
  pr2ᵉ (equiv-apᵉ eᵉ xᵉ yᵉ) = is-emb-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) xᵉ yᵉ

  map-inv-equiv-apᵉ :
    (eᵉ : Aᵉ ≃ᵉ Bᵉ) (xᵉ yᵉ : Aᵉ) → map-equivᵉ eᵉ xᵉ ＝ᵉ map-equivᵉ eᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  map-inv-equiv-apᵉ eᵉ xᵉ yᵉ = map-inv-equivᵉ (equiv-apᵉ eᵉ xᵉ yᵉ)
```

## Equivalence reasoning

Equivalences can be constructed by equational reasoning in the following way:

```text
equivalence-reasoning
  X ≃ Y by equiv-1
    ≃ Z by equiv-2
    ≃ V by equiv-3
```

The equivalence constructed in this way is `equiv-1 ∘e (equiv-2 ∘e equiv-3)`,
i.e., the equivivalence is associated fully to the right.

**Note.** In situations where it is important to have precise control over an
equivalence or its inverse, it is often better to avoid making use of
equivalence reasoning. For example, since many of the entries proving that a map
is an equivalence are marked as `abstract` in agda-unimath, the inverse of an
equivalence often does not compute to any map that one might expect the inverse
to be. If inverses of equivalences are used in equivalence reasoning, this
results in a composed equivalence that also does not compute to any expected
underlying map.

Even if a proof by equivalence reasoning is clear to the human reader,
constructing equivalences by hand by constructing maps back and forth and two
homotopies witnessing that they are mutual inverses is often the most
straigtforward solution that gives the best expected computational behavior of
the constructed equivalence. In particular, if the underlying map or its inverse
are noteworthy maps, it is good practice to define them directly rather than as
underlying maps of equivalences constructed by equivalence reasoning.

```agda
infixl 1 equivalence-reasoningᵉ_
infixl 0 step-equivalence-reasoningᵉ

equivalence-reasoningᵉ_ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) → Xᵉ ≃ᵉ Xᵉ
equivalence-reasoningᵉ Xᵉ = id-equivᵉ

step-equivalence-reasoningᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
  (Xᵉ ≃ᵉ Yᵉ) → (Zᵉ : UUᵉ l3ᵉ) → (Yᵉ ≃ᵉ Zᵉ) → (Xᵉ ≃ᵉ Zᵉ)
step-equivalence-reasoningᵉ eᵉ Zᵉ fᵉ = fᵉ ∘eᵉ eᵉ

syntax step-equivalence-reasoningᵉ eᵉ Zᵉ fᵉ = eᵉ ≃ᵉ Zᵉ byᵉ fᵉ
```

## See also

- For the notion of coherently invertible maps, also known as half-adjoint
  equivalences, see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
- For the notion of finitely coherent equivalence, see
  [`foundation.finitely-coherent-equivalence`)(foundation.finitely-coherent-equivalence.md).
- For the notion of finitely coherently invertible map, see
  [`foundation.finitely-coherently-invertible-map`)(foundation.finitely-coherently-invertible-map.md).
- For the notion of infinitely coherent equivalence, see
  [`foundation.infinitely-coherent-equivalences`](foundation.infinitely-coherent-equivalences.md).

### Table of files about function types, composition, and equivalences

{{#include tables/composition.md}}
