# Joins of maps

```agda
module synthetic-homotopy-theory.joins-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Considerᵉ twoᵉ mapsᵉ `fᵉ : Aᵉ → X`ᵉ andᵉ `gᵉ : Bᵉ → X`ᵉ with aᵉ commonᵉ codomain.ᵉ Theᵉ
**join**ᵉ `fᵉ *ᵉ g`ᵉ ofᵉ `f`ᵉ andᵉ `g`ᵉ isᵉ definedᵉ asᵉ theᵉ
[cogapᵉ map](synthetic-homotopy-theory.pushouts.mdᵉ) ofᵉ theᵉ
[pullbackᵉ square](foundation.pullbacks.mdᵉ)

```text
             π₂ᵉ
   Aᵉ ×_Xᵉ Bᵉ ----->ᵉ Bᵉ
     | ⌟ᵉ          |
  π₁ᵉ |            | gᵉ
     ∨ᵉ            ∨ᵉ
     Aᵉ --------->ᵉ X.ᵉ
           fᵉ
```

Weᵉ oftenᵉ writeᵉ `Aᵉ *_Xᵉ B`ᵉ forᵉ theᵉ domainᵉ ofᵉ theᵉ fiberwiseᵉ join.ᵉ Inᵉ otherᵉ words,ᵉ
theᵉ cogapᵉ mapᵉ ofᵉ anyᵉ cartesianᵉ squareᵉ

```text
        jᵉ
    Aᵉ ----->ᵉ Xᵉ
    | ⌟ᵉ      |
  fᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ
        iᵉ
```

isᵉ theᵉ joinᵉ ofᵉ `i`ᵉ andᵉ `g`.ᵉ Theᵉ joinᵉ ofᵉ mapsᵉ isᵉ alsoᵉ calledᵉ theᵉ **fiberwiseᵉ
join**ᵉ becauseᵉ forᵉ eachᵉ `xᵉ : X`ᵉ weᵉ haveᵉ anᵉ
[equivalence](foundation-core.equivalences.mdᵉ)

```text
  fiberᵉ (fᵉ *ᵉ gᵉ) xᵉ ≃ᵉ (fiberᵉ fᵉ xᵉ) *ᵉ (fiberᵉ gᵉ xᵉ)
```

fromᵉ theᵉ [fiber](foundation-core.fibers-of-maps.mdᵉ) ofᵉ `fᵉ *ᵉ g`ᵉ to theᵉ
[join](synthetic-homotopy-theory.joins-of-types.mdᵉ) ofᵉ theᵉ fibersᵉ ofᵉ `f`ᵉ andᵉ
`g`.ᵉ Inᵉ otherᵉ words,ᵉ thereᵉ isᵉ aᵉ
[commutingᵉ triangle](foundation.commuting-triangles-of-maps.mdᵉ)

```text
            ≃ᵉ
   Aᵉ *_Xᵉ Bᵉ -->ᵉ Σᵉ (xᵉ : X),ᵉ (fiberᵉ fᵉ xᵉ) *ᵉ (fiberᵉ gᵉ xᵉ)
        \ᵉ       /ᵉ
         \ᵉ     /ᵉ
          \ᵉ   /ᵉ
           ∨ᵉ ∨ᵉ
            X.ᵉ
```

in whichᵉ theᵉ topᵉ mapᵉ isᵉ anᵉ equivalence.ᵉ Theᵉ joinᵉ ofᵉ mapsᵉ isᵉ relatedᵉ to theᵉ
[pushout-product](synthetic-homotopy-theory.pushout-products.md),ᵉ becauseᵉ itᵉ
fitsᵉ in aᵉ [pullbackᵉ diagram](foundation.pullbacks.mdᵉ)

```text
      Aᵉ *_Xᵉ Bᵉ ------>ᵉ (Xᵉ ×ᵉ Bᵉ) ⊔_{Aᵉ ×ᵉ Bᵉ} (Aᵉ ×ᵉ Xᵉ)
        | ⌟ᵉ                   |
  fᵉ *ᵉ gᵉ |                     | fᵉ □ᵉ gᵉ
        ∨ᵉ                     ∨ᵉ
        Xᵉ ---------------->ᵉ Xᵉ ×ᵉ X.ᵉ
                 Δᵉ
```

Aᵉ secondᵉ wayᵉ in whichᵉ theᵉ pushout-productᵉ isᵉ relatedᵉ to theᵉ joinᵉ ofᵉ maps,ᵉ isᵉ
thatᵉ thereᵉ isᵉ aᵉ commutingᵉ triangleᵉ

```text
                              ≃ᵉ
  (Xᵉ ×ᵉ Bᵉ) ⊔_{Aᵉ ×ᵉ Bᵉ} (Aᵉ ×ᵉ Xᵉ) ---->ᵉ (Aᵉ ×ᵉ Yᵉ) *_{Xᵉ ×ᵉ Yᵉ} (Xᵉ ×ᵉ Bᵉ)
                        \ᵉ           /ᵉ
                   fᵉ □ᵉ gᵉ \ᵉ         /ᵉ (fᵉ ×ᵉ idᵉ) *ᵉ (idᵉ ×ᵉ gᵉ)
                          \ᵉ       /ᵉ
                           ∨ᵉ     ∨ᵉ
                            Xᵉ ×ᵉ Yᵉ
```

Thisᵉ isᵉ anᵉ immediateᵉ consequenceᵉ ofᵉ theᵉ factᵉ thatᵉ theᵉ ambientᵉ squareᵉ ofᵉ theᵉ
pushout-productᵉ isᵉ cartesian,ᵉ andᵉ thereforeᵉ itsᵉ cogapᵉ mapᵉ isᵉ theᵉ joinᵉ ofᵉ theᵉ twoᵉ
terminalᵉ mapsᵉ in theᵉ square.ᵉ

## Definitions

### The join of maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  domain-join-mapsᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  domain-join-mapsᵉ =
    pushoutᵉ
      ( vertical-map-standard-pullbackᵉ {fᵉ = fᵉ} {gᵉ = gᵉ})
      ( horizontal-map-standard-pullbackᵉ {fᵉ = fᵉ} {gᵉ = gᵉ})

  cocone-join-mapsᵉ :
    coconeᵉ
      ( vertical-map-standard-pullbackᵉ {fᵉ = fᵉ} {gᵉ = gᵉ})
      ( horizontal-map-standard-pullbackᵉ {fᵉ = fᵉ} {gᵉ = gᵉ})
      ( Xᵉ)
  pr1ᵉ cocone-join-mapsᵉ = fᵉ
  pr1ᵉ (pr2ᵉ cocone-join-mapsᵉ) = gᵉ
  pr2ᵉ (pr2ᵉ cocone-join-mapsᵉ) = coherence-square-standard-pullbackᵉ

  abstract
    uniqueness-join-mapsᵉ :
      is-contrᵉ
        ( Σᵉ ( domain-join-mapsᵉ → Xᵉ)
            ( λ hᵉ →
              htpy-coconeᵉ
                ( vertical-map-standard-pullbackᵉ)
                ( horizontal-map-standard-pullbackᵉ)
                ( cocone-mapᵉ
                  ( vertical-map-standard-pullbackᵉ)
                  ( horizontal-map-standard-pullbackᵉ)
                  ( cocone-pushoutᵉ
                    ( vertical-map-standard-pullbackᵉ)
                    ( horizontal-map-standard-pullbackᵉ))
                  ( hᵉ))
                ( cocone-join-mapsᵉ)))
    uniqueness-join-mapsᵉ =
      uniqueness-map-universal-property-pushoutᵉ
        ( vertical-map-standard-pullbackᵉ)
        ( horizontal-map-standard-pullbackᵉ)
        ( cocone-pushoutᵉ
          ( vertical-map-standard-pullbackᵉ)
          ( horizontal-map-standard-pullbackᵉ))
        ( up-pushoutᵉ _ _)
        ( cocone-join-mapsᵉ)

  abstract
    join-mapsᵉ : domain-join-mapsᵉ → Xᵉ
    join-mapsᵉ = pr1ᵉ (centerᵉ uniqueness-join-mapsᵉ)

    compute-inl-join-mapsᵉ : join-mapsᵉ ∘ᵉ inl-pushoutᵉ _ _ ~ᵉ fᵉ
    compute-inl-join-mapsᵉ = pr1ᵉ (pr2ᵉ (centerᵉ uniqueness-join-mapsᵉ))

    compute-inr-join-mapsᵉ : join-mapsᵉ ∘ᵉ inr-pushoutᵉ _ _ ~ᵉ gᵉ
    compute-inr-join-mapsᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ (centerᵉ uniqueness-join-mapsᵉ)))

    compute-glue-join-mapsᵉ :
      statement-coherence-htpy-coconeᵉ
        ( vertical-map-standard-pullbackᵉ)
        ( horizontal-map-standard-pullbackᵉ)
        ( cocone-mapᵉ
          ( vertical-map-standard-pullbackᵉ)
          ( horizontal-map-standard-pullbackᵉ)
          ( cocone-pushoutᵉ
            ( vertical-map-standard-pullbackᵉ)
            ( horizontal-map-standard-pullbackᵉ))
          ( join-mapsᵉ))
        ( cocone-join-mapsᵉ)
        ( compute-inl-join-mapsᵉ)
        ( compute-inr-join-mapsᵉ)
    compute-glue-join-mapsᵉ =
      pr2ᵉ (pr2ᵉ (pr2ᵉ (centerᵉ uniqueness-join-mapsᵉ)))
```

## External links

-ᵉ [Joinᵉ ofᵉ maps](https://ncatlab.org/nlab/show/join+of+mapsᵉ) atᵉ theᵉ $n$Labᵉ