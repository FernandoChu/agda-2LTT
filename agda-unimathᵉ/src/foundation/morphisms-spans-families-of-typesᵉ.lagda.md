# Morphisms of spans on families of types

```agda
module foundation.morphisms-spans-families-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-homotopiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.spans-families-of-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Considerᵉ twoᵉ [spans](foundation.spans-families-of-types.mdᵉ) `𝒮ᵉ :=ᵉ (Sᵉ ,ᵉ f)`ᵉ andᵉ
`𝒯ᵉ :=ᵉ (Tᵉ ,ᵉ g)`ᵉ onᵉ aᵉ familyᵉ ofᵉ typesᵉ `Aᵉ : Iᵉ → 𝒰`.ᵉ Aᵉ
{{#conceptᵉ "morphism"ᵉ Disambiguation="spanᵉ onᵉ aᵉ familyᵉ ofᵉ types"ᵉ Agda=hom-span-type-familyᵉ}}
fromᵉ `𝒮`ᵉ to `𝒯`ᵉ consistsᵉ ofᵉ aᵉ mapᵉ `hᵉ : Sᵉ → T`ᵉ andᵉ aᵉ
[homotopy](foundation-core.homotopies.mdᵉ) witnessingᵉ thatᵉ theᵉ triangleᵉ

```text
        hᵉ
    Sᵉ ---->ᵉ Tᵉ
     \ᵉ     /ᵉ
  fᵉ iᵉ \ᵉ   /ᵉ gᵉ iᵉ
       ∨ᵉ ∨ᵉ
       Aᵉ iᵉ
```

[commutes](foundation-core.commuting-triangles-of-maps.mdᵉ) forᵉ everyᵉ `iᵉ : I`.ᵉ

## Definitions

### Morphisms of spans on families of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ}
  (𝒮ᵉ : span-type-familyᵉ l3ᵉ Aᵉ) (𝒯ᵉ : span-type-familyᵉ l4ᵉ Aᵉ)
  where

  hom-span-type-familyᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-span-type-familyᵉ =
    Σᵉ ( spanning-type-span-type-familyᵉ 𝒮ᵉ →
        spanning-type-span-type-familyᵉ 𝒯ᵉ)
      ( λ hᵉ →
        (iᵉ : Iᵉ) →
        coherence-triangle-mapsᵉ
          ( map-span-type-familyᵉ 𝒮ᵉ iᵉ)
          ( map-span-type-familyᵉ 𝒯ᵉ iᵉ)
          ( hᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ}
  (𝒮ᵉ : span-type-familyᵉ l3ᵉ Aᵉ) (𝒯ᵉ : span-type-familyᵉ l4ᵉ Aᵉ)
  (hᵉ : hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ)
  where

  map-hom-span-type-familyᵉ :
    spanning-type-span-type-familyᵉ 𝒮ᵉ →
    spanning-type-span-type-familyᵉ 𝒯ᵉ
  map-hom-span-type-familyᵉ = pr1ᵉ hᵉ

  coherence-triangle-hom-span-type-familyᵉ :
    (iᵉ : Iᵉ) →
    coherence-triangle-mapsᵉ
      ( map-span-type-familyᵉ 𝒮ᵉ iᵉ)
      ( map-span-type-familyᵉ 𝒯ᵉ iᵉ)
      ( map-hom-span-type-familyᵉ)
  coherence-triangle-hom-span-type-familyᵉ =
    pr2ᵉ hᵉ
```

### Homotopies of morphisms of spans on families of types

Considerᵉ twoᵉ spansᵉ `𝒮ᵉ :=ᵉ (Sᵉ ,ᵉ f)`ᵉ andᵉ `𝒯ᵉ :=ᵉ (Tᵉ ,ᵉ g)`ᵉ onᵉ aᵉ familyᵉ ofᵉ typesᵉ
`Aᵉ : Iᵉ → 𝒰`,ᵉ andᵉ considerᵉ twoᵉ morphismsᵉ `(hᵉ ,ᵉ H)`ᵉ andᵉ `(kᵉ ,ᵉ K)`ᵉ betweenᵉ them.ᵉ Aᵉ
{{#conceptᵉ "homotopy"ᵉ Disambiguation="morphismᵉ betweenᵉ spansᵉ onᵉ familiesᵉ ofᵉ types"ᵉ Agda=htpy-hom-span-type-familyᵉ}}
isᵉ aᵉ pairᵉ `(αᵉ ,ᵉ β)`ᵉ consistingᵉ ofᵉ aᵉ homotopyᵉ

```text
  αᵉ : hᵉ ~ᵉ kᵉ
```

andᵉ aᵉ familyᵉ `β`ᵉ ofᵉ homotopiesᵉ witnessingᵉ thatᵉ theᵉ triangleᵉ

```text
              fᵉ iᵉ
             /ᵉ   \ᵉ
        Hᵉ iᵉ /ᵉ βᵉ iᵉ \ᵉ Kᵉ iᵉ
           ∨ᵉ       ∨ᵉ
  (gᵉ iᵉ ∘ᵉ hᵉ) ------>ᵉ (gᵉ iᵉ ∘ᵉ kᵉ)
            gᵉ iᵉ ·ᵉ αᵉ
```

commutesᵉ forᵉ eachᵉ `iᵉ : I`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ}
  (𝒮ᵉ : span-type-familyᵉ l3ᵉ Aᵉ) (𝒯ᵉ : span-type-familyᵉ l4ᵉ Aᵉ)
  (hᵉ kᵉ : hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ)
  where

  coherence-htpy-hom-span-type-familyᵉ :
    map-hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ hᵉ ~ᵉ map-hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ kᵉ →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  coherence-htpy-hom-span-type-familyᵉ αᵉ =
    (iᵉ : Iᵉ) →
    coherence-triangle-homotopies'ᵉ
      ( coherence-triangle-hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ kᵉ iᵉ)
      ( map-span-type-familyᵉ 𝒯ᵉ iᵉ ·lᵉ αᵉ)
      ( coherence-triangle-hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ hᵉ iᵉ)

  htpy-hom-span-type-familyᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-hom-span-type-familyᵉ =
    Σᵉ ( map-hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ hᵉ ~ᵉ map-hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ kᵉ)
      ( coherence-htpy-hom-span-type-familyᵉ)

  module _
    (αᵉ : htpy-hom-span-type-familyᵉ)
    where

    htpy-htpy-hom-span-type-familyᵉ :
      map-hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ hᵉ ~ᵉ map-hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ kᵉ
    htpy-htpy-hom-span-type-familyᵉ = pr1ᵉ αᵉ

    coh-htpy-hom-span-type-familyᵉ :
      coherence-htpy-hom-span-type-familyᵉ htpy-htpy-hom-span-type-familyᵉ
    coh-htpy-hom-span-type-familyᵉ = pr2ᵉ αᵉ
```

### The reflexivity homotopy on a morphism of spans on families of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ}
  (𝒮ᵉ : span-type-familyᵉ l3ᵉ Aᵉ) (𝒯ᵉ : span-type-familyᵉ l4ᵉ Aᵉ)
  (hᵉ : hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ)
  where

  refl-htpy-hom-span-type-familyᵉ :
    htpy-hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ hᵉ hᵉ
  pr1ᵉ refl-htpy-hom-span-type-familyᵉ = refl-htpyᵉ
  pr2ᵉ refl-htpy-hom-span-type-familyᵉ iᵉ = right-unit-htpyᵉ
```

## Properties

### Characterization of identifications of morphisms of spans on families of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ}
  (𝒮ᵉ : span-type-familyᵉ l3ᵉ Aᵉ) (𝒯ᵉ : span-type-familyᵉ l4ᵉ Aᵉ)
  (hᵉ : hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ)
  where

  htpy-eq-hom-span-type-familyᵉ :
    (kᵉ : hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ) →
    hᵉ ＝ᵉ kᵉ → htpy-hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ hᵉ kᵉ
  htpy-eq-hom-span-type-familyᵉ .hᵉ reflᵉ =
    refl-htpy-hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ hᵉ

  is-torsorial-htpy-hom-span-type-familyᵉ :
    is-torsorialᵉ (htpy-hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ hᵉ)
  is-torsorial-htpy-hom-span-type-familyᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ _)
      ( map-hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ hᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-Eq-Πᵉ (λ iᵉ → is-torsorial-htpyᵉ _))

  is-equiv-htpy-eq-hom-span-type-familyᵉ :
    (kᵉ : hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ) →
    is-equivᵉ (htpy-eq-hom-span-type-familyᵉ kᵉ)
  is-equiv-htpy-eq-hom-span-type-familyᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-hom-span-type-familyᵉ)
      ( htpy-eq-hom-span-type-familyᵉ)

  extensionality-hom-span-type-familyᵉ :
    (kᵉ : hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ) →
    (hᵉ ＝ᵉ kᵉ) ≃ᵉ htpy-hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ hᵉ kᵉ
  pr1ᵉ (extensionality-hom-span-type-familyᵉ kᵉ) =
    htpy-eq-hom-span-type-familyᵉ kᵉ
  pr2ᵉ (extensionality-hom-span-type-familyᵉ kᵉ) =
    is-equiv-htpy-eq-hom-span-type-familyᵉ kᵉ

  eq-htpy-hom-span-type-familyᵉ :
    (kᵉ : hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ) →
    htpy-hom-span-type-familyᵉ 𝒮ᵉ 𝒯ᵉ hᵉ kᵉ → hᵉ ＝ᵉ kᵉ
  eq-htpy-hom-span-type-familyᵉ kᵉ =
    map-inv-equivᵉ (extensionality-hom-span-type-familyᵉ kᵉ)
```