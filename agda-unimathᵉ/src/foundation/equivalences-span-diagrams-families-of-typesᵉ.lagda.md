# Equivalences of span diagrams on families of types

```agda
module foundation.equivalences-span-diagrams-families-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-spans-families-of-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.operations-spans-families-of-typesᵉ
open import foundation.span-diagrams-families-of-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ
{{#conceptᵉ "equivalenceᵉ ofᵉ spanᵉ diagramsᵉ onᵉ familiesᵉ ofᵉ types"ᵉ Agda=equiv-span-diagram-type-familyᵉ}}
fromᵉ aᵉ [span](foundation.spans-families-of-types.mdᵉ) `(Aᵉ ,ᵉ s)`ᵉ ofᵉ familiesᵉ ofᵉ
typesᵉ indexedᵉ byᵉ aᵉ typeᵉ `I`ᵉ to aᵉ spanᵉ `(Bᵉ ,ᵉ t)`ᵉ indexedᵉ byᵉ `I`ᵉ consistsᵉ ofᵉ aᵉ
[familyᵉ ofᵉ equivalences](foundation-core.families-of-equivalences.mdᵉ)
`hᵉ : Aᵢᵉ ≃ᵉ Bᵢ`,ᵉ andᵉ anᵉ equivalenceᵉ `eᵉ : Sᵉ ≃ᵉ T`ᵉ
[equipped](foundation.structure.mdᵉ) with aᵉ familyᵉ ofᵉ
[homotopies](foundation-core.homotopies.mdᵉ) witnessingᵉ thatᵉ theᵉ squareᵉ

```text
         eᵉ
     Sᵉ ----->ᵉ Tᵉ
     |        |
  fᵢᵉ |        | gᵢᵉ
     ∨ᵉ        ∨ᵉ
     Aᵢᵉ ---->ᵉ Bᵢᵉ
         hᵉ
```

[commutes](foundation-core.commuting-squares-of-maps.mdᵉ) forᵉ eachᵉ `iᵉ : I`.ᵉ

## Definitions

### Equivalences of span diagrams on families of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
  (Sᵉ : span-diagram-type-familyᵉ l2ᵉ l3ᵉ Iᵉ)
  (Tᵉ : span-diagram-type-familyᵉ l4ᵉ l5ᵉ Iᵉ)
  where

  equiv-span-diagram-type-familyᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  equiv-span-diagram-type-familyᵉ =
    Σᵉ ( (iᵉ : Iᵉ) →
        family-span-diagram-type-familyᵉ Sᵉ iᵉ ≃ᵉ
        family-span-diagram-type-familyᵉ Tᵉ iᵉ)
      ( λ eᵉ →
        equiv-span-type-familyᵉ
          ( concat-span-hom-family-of-typesᵉ
            ( span-span-diagram-type-familyᵉ Sᵉ)
            ( λ iᵉ → map-equivᵉ (eᵉ iᵉ)))
          ( span-span-diagram-type-familyᵉ Tᵉ))

  module _
    (eᵉ : equiv-span-diagram-type-familyᵉ)
    where

    equiv-family-equiv-span-diagram-type-familyᵉ :
      (iᵉ : Iᵉ) →
      family-span-diagram-type-familyᵉ Sᵉ iᵉ ≃ᵉ
      family-span-diagram-type-familyᵉ Tᵉ iᵉ
    equiv-family-equiv-span-diagram-type-familyᵉ = pr1ᵉ eᵉ

    map-family-equiv-span-diagram-type-familyᵉ :
      (iᵉ : Iᵉ) →
      family-span-diagram-type-familyᵉ Sᵉ iᵉ →
      family-span-diagram-type-familyᵉ Tᵉ iᵉ
    map-family-equiv-span-diagram-type-familyᵉ iᵉ =
      map-equivᵉ (equiv-family-equiv-span-diagram-type-familyᵉ iᵉ)

    equiv-span-equiv-span-diagram-type-familyᵉ :
      equiv-span-type-familyᵉ
        ( concat-span-hom-family-of-typesᵉ
          ( span-span-diagram-type-familyᵉ Sᵉ)
          ( map-family-equiv-span-diagram-type-familyᵉ))
        ( span-span-diagram-type-familyᵉ Tᵉ)
    equiv-span-equiv-span-diagram-type-familyᵉ = pr2ᵉ eᵉ

    spanning-equiv-equiv-span-diagram-type-familyᵉ :
      spanning-type-span-diagram-type-familyᵉ Sᵉ ≃ᵉ
      spanning-type-span-diagram-type-familyᵉ Tᵉ
    spanning-equiv-equiv-span-diagram-type-familyᵉ =
      equiv-equiv-span-type-familyᵉ
        ( concat-span-hom-family-of-typesᵉ
          ( span-span-diagram-type-familyᵉ Sᵉ)
          ( map-family-equiv-span-diagram-type-familyᵉ))
        ( span-span-diagram-type-familyᵉ Tᵉ)
        ( equiv-span-equiv-span-diagram-type-familyᵉ)

    spanning-map-equiv-span-diagram-type-familyᵉ :
      spanning-type-span-diagram-type-familyᵉ Sᵉ →
      spanning-type-span-diagram-type-familyᵉ Tᵉ
    spanning-map-equiv-span-diagram-type-familyᵉ =
      map-equivᵉ spanning-equiv-equiv-span-diagram-type-familyᵉ

    coherence-square-equiv-span-diagram-type-familyᵉ :
      (iᵉ : Iᵉ) →
      coherence-square-mapsᵉ
        ( spanning-map-equiv-span-diagram-type-familyᵉ)
        ( map-span-diagram-type-familyᵉ Sᵉ iᵉ)
        ( map-span-diagram-type-familyᵉ Tᵉ iᵉ)
        ( map-family-equiv-span-diagram-type-familyᵉ iᵉ)
    coherence-square-equiv-span-diagram-type-familyᵉ =
      triangle-equiv-span-type-familyᵉ
        ( concat-span-hom-family-of-typesᵉ
          ( span-span-diagram-type-familyᵉ Sᵉ)
          ( map-family-equiv-span-diagram-type-familyᵉ))
        ( span-span-diagram-type-familyᵉ Tᵉ)
        ( equiv-span-equiv-span-diagram-type-familyᵉ)
```

### Identity equivalences of spans diagrams on families of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {𝒮ᵉ : span-diagram-type-familyᵉ l2ᵉ l3ᵉ Iᵉ}
  where

  id-equiv-span-diagram-type-familyᵉ :
    equiv-span-diagram-type-familyᵉ 𝒮ᵉ 𝒮ᵉ
  pr1ᵉ id-equiv-span-diagram-type-familyᵉ iᵉ = id-equivᵉ
  pr1ᵉ (pr2ᵉ id-equiv-span-diagram-type-familyᵉ) = id-equivᵉ
  pr2ᵉ (pr2ᵉ id-equiv-span-diagram-type-familyᵉ) iᵉ = refl-htpyᵉ
```

## See also

-ᵉ [Equivalencesᵉ ofᵉ spansᵉ onᵉ familiesᵉ ofᵉ types](foundation.equivalences-spans-families-of-types.mdᵉ)