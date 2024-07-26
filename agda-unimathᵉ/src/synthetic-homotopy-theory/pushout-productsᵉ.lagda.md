# Pushout-products

```agda
module synthetic-homotopy-theory.pushout-productsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Considerᵉ twoᵉ mapsᵉ `fᵉ : Aᵉ → X`ᵉ andᵉ `gᵉ : Bᵉ → Y`.ᵉ Theᵉ **pushout-product**ᵉ `fᵉ □ᵉ g`ᵉ
ofᵉ `f`ᵉ andᵉ `g`ᵉ isᵉ definedᵉ asᵉ theᵉ
[cogapᵉ map](synthetic-homotopy-theory.pushouts.mdᵉ) ofᵉ theᵉ
[commutingᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ)

```text
              fᵉ ×ᵉ idᵉ
       Aᵉ ×ᵉ Bᵉ -------->ᵉ Xᵉ ×ᵉ Bᵉ
         |               |
  idᵉ ×ᵉ gᵉ |      Hᵉ ⇗ᵉ      | idᵉ ×ᵉ gᵉ
         ∨ᵉ               ∨ᵉ
       Aᵉ ×ᵉ Yᵉ -------->ᵉ Xᵉ ×ᵉ Y.ᵉ
              fᵉ ×ᵉ idᵉ
```

Inᵉ otherᵉ words,ᵉ theᵉ pushout-productᵉ isᵉ theᵉ uniqueᵉ mapᵉ

```text
  fᵉ □ᵉ gᵉ : (Xᵉ ×ᵉ Bᵉ) ⊔_{Aᵉ ×ᵉ Bᵉ} (Aᵉ ×ᵉ Yᵉ) → Xᵉ ×ᵉ Yᵉ
```

equippedᵉ with [homotopies](foundation-core.homotopies.mdᵉ)

```text
  Kᵉ : (fᵉ □ᵉ gᵉ) ∘ᵉ inlᵉ ~ᵉ fᵉ ×ᵉ idᵉ
  Lᵉ : (fᵉ □ᵉ gᵉ) ∘ᵉ inrᵉ ~ᵉ idᵉ ×ᵉ gᵉ
```

andᵉ aᵉ homotopyᵉ `M`ᵉ witnessingᵉ thatᵉ theᵉ
[squareᵉ ofᵉ homotopies](foundation.commuting-squares-of-homotopies.mdᵉ)

```text
                                 Kᵉ ·rᵉ (idᵉ ×ᵉ gᵉ)
       (fᵉ □ᵉ gᵉ) ∘ᵉ inlᵉ ∘ᵉ (idᵉ ×ᵉ gᵉ) --------------->ᵉ (fᵉ ×ᵉ idᵉ) ∘ᵉ (idᵉ ×ᵉ gᵉ)
                  |                                       |
  (fᵉ □ᵉ gᵉ) ·lᵉ glueᵉ |                                       | Hᵉ
                  |                                       |
                  ∨ᵉ                                       ∨ᵉ
       (fᵉ □ᵉ gᵉ) ∘ᵉ inrᵉ ∘ᵉ (fᵉ ×ᵉ idᵉ) --------------->ᵉ (idᵉ ×ᵉ gᵉ) ∘ᵉ (fᵉ ×ᵉ idᵉ)
                                 Lᵉ ·rᵉ (fᵉ ×ᵉ idᵉ)
```

commutes.ᵉ Theᵉ pushout-productsᵉ isᵉ oftenᵉ calledᵉ theᵉ **fiberwiseᵉ join**,ᵉ becauseᵉ
forᵉ eachᵉ `(xᵉ ,ᵉ yᵉ) : Xᵉ ×ᵉ Y`ᵉ weᵉ haveᵉ anᵉ
[equivalence](foundation-core.equivalences.mdᵉ)

```text
  fiberᵉ (fᵉ □ᵉ gᵉ) (xᵉ ,ᵉ yᵉ) ≃ᵉ (fiberᵉ fᵉ xᵉ) *ᵉ (fiberᵉ gᵉ y).ᵉ
```

fromᵉ theᵉ [fibers](foundation-core.fibers-of-maps.mdᵉ) ofᵉ `fᵉ □ᵉ g`ᵉ to theᵉ
[join](synthetic-homotopy-theory.joins-of-types.mdᵉ) ofᵉ theᵉ fibersᵉ ofᵉ `f`ᵉ andᵉ
`g`.ᵉ

Thereᵉ isᵉ anᵉ "adjointᵉ relation"ᵉ betweenᵉ theᵉ pushout-productᵉ andᵉ theᵉ
[pullback-hom](orthogonal-factorization-systems.pullback-hom.mdᵉ): Forᵉ anyᵉ threeᵉ
mapsᵉ `f`,ᵉ `g`,ᵉ andᵉ `h`ᵉ weᵉ haveᵉ aᵉ [homotopy](foundation-core.homotopies.mdᵉ)

```text
  ⟨fᵉ □ᵉ gᵉ ,ᵉ h⟩ᵉ ~ᵉ ⟨fᵉ ,ᵉ ⟨gᵉ ,ᵉ h⟩⟩.ᵉ
```

## Definitions

### The pushout-product

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ)
  where

  domain-pushout-productᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  domain-pushout-productᵉ =
    pushoutᵉ (map-productᵉ idᵉ gᵉ) (map-productᵉ fᵉ idᵉ)

  cocone-pushout-productᵉ : coconeᵉ (map-productᵉ idᵉ gᵉ) (map-productᵉ fᵉ idᵉ) (Xᵉ ×ᵉ Yᵉ)
  pr1ᵉ cocone-pushout-productᵉ = map-productᵉ fᵉ idᵉ
  pr1ᵉ (pr2ᵉ cocone-pushout-productᵉ) = map-productᵉ idᵉ gᵉ
  pr2ᵉ (pr2ᵉ cocone-pushout-productᵉ) = coherence-square-map-productᵉ fᵉ gᵉ

  abstract
    uniqueness-pushout-productᵉ :
      is-contrᵉ
        ( Σᵉ ( domain-pushout-productᵉ → Xᵉ ×ᵉ Yᵉ)
            ( λ hᵉ →
              htpy-coconeᵉ
                ( map-productᵉ idᵉ gᵉ)
                ( map-productᵉ fᵉ idᵉ)
                ( cocone-mapᵉ
                  ( map-productᵉ idᵉ gᵉ)
                  ( map-productᵉ fᵉ idᵉ)
                  ( cocone-pushoutᵉ (map-productᵉ idᵉ gᵉ) (map-productᵉ fᵉ idᵉ))
                  ( hᵉ))
                ( cocone-pushout-productᵉ)))
    uniqueness-pushout-productᵉ =
      uniqueness-map-universal-property-pushoutᵉ
        ( map-productᵉ idᵉ gᵉ)
        ( map-productᵉ fᵉ idᵉ)
        ( cocone-pushoutᵉ (map-productᵉ idᵉ gᵉ) (map-productᵉ fᵉ idᵉ))
        ( up-pushoutᵉ (map-productᵉ idᵉ gᵉ) (map-productᵉ fᵉ idᵉ))
        ( cocone-pushout-productᵉ)

  abstract
    pushout-productᵉ : domain-pushout-productᵉ → Xᵉ ×ᵉ Yᵉ
    pushout-productᵉ = pr1ᵉ (centerᵉ uniqueness-pushout-productᵉ)

    compute-inl-pushout-productᵉ :
      pushout-productᵉ ∘ᵉ inl-pushoutᵉ (map-productᵉ idᵉ gᵉ) (map-productᵉ fᵉ idᵉ) ~ᵉ
      map-productᵉ fᵉ idᵉ
    compute-inl-pushout-productᵉ =
      pr1ᵉ (pr2ᵉ (centerᵉ uniqueness-pushout-productᵉ))

    compute-inr-pushout-productᵉ :
      pushout-productᵉ ∘ᵉ inr-pushoutᵉ (map-productᵉ idᵉ gᵉ) (map-productᵉ fᵉ idᵉ) ~ᵉ
      map-productᵉ idᵉ gᵉ
    compute-inr-pushout-productᵉ =
      pr1ᵉ (pr2ᵉ (pr2ᵉ (centerᵉ uniqueness-pushout-productᵉ)))

    compute-glue-pushout-productᵉ :
      statement-coherence-htpy-coconeᵉ
        ( map-productᵉ idᵉ gᵉ)
        ( map-productᵉ fᵉ idᵉ)
        ( cocone-mapᵉ
          ( map-productᵉ idᵉ gᵉ)
          ( map-productᵉ fᵉ idᵉ)
          ( cocone-pushoutᵉ (map-productᵉ idᵉ gᵉ) (map-productᵉ fᵉ idᵉ))
          ( pushout-productᵉ))
        ( cocone-pushout-productᵉ)
        ( compute-inl-pushout-productᵉ)
        ( compute-inr-pushout-productᵉ)
    compute-glue-pushout-productᵉ =
      pr2ᵉ (pr2ᵉ (pr2ᵉ (centerᵉ uniqueness-pushout-productᵉ)))
```

## See also

-ᵉ [Theᵉ dependentᵉ pushout-product](synthetic-homotopy-theory.dependent-pushout-products.mdᵉ)

## External links

-ᵉ [Pushout-product](https://ncatlab.org/nlab/show/pushout-productᵉ) atᵉ $n$labᵉ

Aᵉ wikidataᵉ identifierᵉ forᵉ thisᵉ conceptᵉ isᵉ notᵉ available.ᵉ