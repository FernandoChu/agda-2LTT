# Equivalences of spans of families of types

```agda
module foundation.equivalences-spans-families-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.morphisms-spans-families-of-typesᵉ
open import foundation.spans-families-of-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Anᵉ
{{#conceptᵉ "equivalenceᵉ ofᵉ spansᵉ onᵉ aᵉ familyᵉ ofᵉ types"ᵉ Agda=equiv-span-type-familyᵉ}}
fromᵉ aᵉ [span](foundation.spans-families-of-types.mdᵉ) `s`ᵉ onᵉ `Aᵉ : Iᵉ → 𝒰`ᵉ to aᵉ
spanᵉ `t`ᵉ onᵉ `A`ᵉ consistsᵉ ofᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ)
`eᵉ : Sᵉ ≃ᵉ T`ᵉ [equipped](foundation.structure.mdᵉ) with aᵉ familyᵉ ofᵉ
[homotopies](foundation-core.homotopies.mdᵉ) witnessingᵉ thatᵉ theᵉ triangleᵉ

```text
      eᵉ
  Sᵉ ---->ᵉ Tᵉ
   \ᵉ     /ᵉ
    \ᵉ   /ᵉ
     ∨ᵉ ∨ᵉ
      Aᵢᵉ
```

[commutes](foundation.commuting-triangles-of-maps.mdᵉ) forᵉ eachᵉ `iᵉ : I`.ᵉ

## Definitions

### Equivalences of spans of families of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ}
  (Sᵉ : span-type-familyᵉ l3ᵉ Aᵉ) (Tᵉ : span-type-familyᵉ l4ᵉ Aᵉ)
  where

  equiv-span-type-familyᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  equiv-span-type-familyᵉ =
    Σᵉ ( spanning-type-span-type-familyᵉ Sᵉ ≃ᵉ
        spanning-type-span-type-familyᵉ Tᵉ)
      ( λ eᵉ →
        (iᵉ : Iᵉ) →
        coherence-triangle-mapsᵉ
          ( map-span-type-familyᵉ Sᵉ iᵉ)
          ( map-span-type-familyᵉ Tᵉ iᵉ)
          ( map-equivᵉ eᵉ))

  module _
    (eᵉ : equiv-span-type-familyᵉ)
    where

    equiv-equiv-span-type-familyᵉ :
      spanning-type-span-type-familyᵉ Sᵉ ≃ᵉ
      spanning-type-span-type-familyᵉ Tᵉ
    equiv-equiv-span-type-familyᵉ = pr1ᵉ eᵉ

    map-equiv-span-type-familyᵉ :
      spanning-type-span-type-familyᵉ Sᵉ →
      spanning-type-span-type-familyᵉ Tᵉ
    map-equiv-span-type-familyᵉ = map-equivᵉ equiv-equiv-span-type-familyᵉ

    is-equiv-equiv-span-type-familyᵉ :
      is-equivᵉ map-equiv-span-type-familyᵉ
    is-equiv-equiv-span-type-familyᵉ =
      is-equiv-map-equivᵉ equiv-equiv-span-type-familyᵉ

    triangle-equiv-span-type-familyᵉ :
      (iᵉ : Iᵉ) →
      coherence-triangle-mapsᵉ
        ( map-span-type-familyᵉ Sᵉ iᵉ)
        ( map-span-type-familyᵉ Tᵉ iᵉ)
        ( map-equiv-span-type-familyᵉ)
    triangle-equiv-span-type-familyᵉ = pr2ᵉ eᵉ

    hom-equiv-span-type-familyᵉ : hom-span-type-familyᵉ Sᵉ Tᵉ
    pr1ᵉ hom-equiv-span-type-familyᵉ = map-equiv-span-type-familyᵉ
    pr2ᵉ hom-equiv-span-type-familyᵉ = triangle-equiv-span-type-familyᵉ
```

### Identity equivalences of spans of families of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ}
  {Sᵉ : span-type-familyᵉ l3ᵉ Aᵉ}
  where

  id-equiv-span-type-familyᵉ : equiv-span-type-familyᵉ Sᵉ Sᵉ
  pr1ᵉ id-equiv-span-type-familyᵉ = id-equivᵉ
  pr2ᵉ id-equiv-span-type-familyᵉ iᵉ = refl-htpyᵉ
```

## Properties

### Characterizing the identity type of the type of spans of families of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} (Sᵉ : span-type-familyᵉ l3ᵉ Aᵉ)
  where

  equiv-eq-span-type-familyᵉ :
    (Tᵉ : span-type-familyᵉ l3ᵉ Aᵉ) → Sᵉ ＝ᵉ Tᵉ → equiv-span-type-familyᵉ Sᵉ Tᵉ
  equiv-eq-span-type-familyᵉ .Sᵉ reflᵉ = id-equiv-span-type-familyᵉ

  is-torsorial-equiv-span-type-familyᵉ :
    is-torsorialᵉ (equiv-span-type-familyᵉ Sᵉ)
  is-torsorial-equiv-span-type-familyᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ _)
      ( spanning-type-span-type-familyᵉ Sᵉ ,ᵉ id-equivᵉ)
      ( is-torsorial-Eq-Πᵉ (λ iᵉ → is-torsorial-htpyᵉ _))

  is-equiv-equiv-eq-span-type-familyᵉ :
    (Tᵉ : span-type-familyᵉ l3ᵉ Aᵉ) → is-equivᵉ (equiv-eq-span-type-familyᵉ Tᵉ)
  is-equiv-equiv-eq-span-type-familyᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-equiv-span-type-familyᵉ)
      ( equiv-eq-span-type-familyᵉ)

  extensionality-span-type-familyᵉ :
    (Tᵉ : span-type-familyᵉ l3ᵉ Aᵉ) → (Sᵉ ＝ᵉ Tᵉ) ≃ᵉ equiv-span-type-familyᵉ Sᵉ Tᵉ
  pr1ᵉ (extensionality-span-type-familyᵉ Tᵉ) =
    equiv-eq-span-type-familyᵉ Tᵉ
  pr2ᵉ (extensionality-span-type-familyᵉ Tᵉ) =
    is-equiv-equiv-eq-span-type-familyᵉ Tᵉ

  eq-equiv-span-type-familyᵉ :
    (Tᵉ : span-type-familyᵉ l3ᵉ Aᵉ) → equiv-span-type-familyᵉ Sᵉ Tᵉ → Sᵉ ＝ᵉ Tᵉ
  eq-equiv-span-type-familyᵉ Tᵉ =
    map-inv-equivᵉ (extensionality-span-type-familyᵉ Tᵉ)
```

## See also

-ᵉ [Equivalencesᵉ ofᵉ spanᵉ diagramsᵉ onᵉ familiesᵉ ofᵉ types](foundation.equivalences-span-diagrams-families-of-types.mdᵉ)