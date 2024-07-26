# Morphisms of binary relations

```agda
module foundation.morphisms-binary-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-homotopiesᵉ
open import foundation.binary-relationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Aᵉ **morphism**ᵉ ofᵉ [binaryᵉ relations](foundation.binary-relations.mdᵉ) `R`ᵉ andᵉ `S`ᵉ
onᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ familyᵉ ofᵉ mapsᵉ `Rᵉ xᵉ yᵉ → Sᵉ xᵉ y`ᵉ forᵉ everyᵉ pairᵉ `xᵉ yᵉ : A`.ᵉ

## Definition

### Morphisms of binary relations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  hom-Relationᵉ : Relationᵉ l2ᵉ Aᵉ → Relationᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  hom-Relationᵉ Rᵉ Sᵉ = (xᵉ yᵉ : Aᵉ) → Rᵉ xᵉ yᵉ → Sᵉ xᵉ yᵉ
```

## Properties

### Characterization of equality of morphisms of binary relations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Rᵉ : Relationᵉ l2ᵉ Aᵉ} {Sᵉ : Relationᵉ l3ᵉ Aᵉ}
  where

  htpy-hom-Relationᵉ : (fᵉ gᵉ : hom-Relationᵉ Rᵉ Sᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  htpy-hom-Relationᵉ = binary-htpyᵉ

  extensionality-hom-Relationᵉ :
    (fᵉ gᵉ : hom-Relationᵉ Rᵉ Sᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ binary-htpyᵉ fᵉ gᵉ
  extensionality-hom-Relationᵉ = extensionality-binary-Πᵉ

  htpy-eq-hom-Relationᵉ :
    (fᵉ gᵉ : hom-Relationᵉ Rᵉ Sᵉ) → (fᵉ ＝ᵉ gᵉ) → binary-htpyᵉ fᵉ gᵉ
  htpy-eq-hom-Relationᵉ = binary-htpy-eqᵉ

  eq-htpy-hom-Relationᵉ :
    (fᵉ gᵉ : hom-Relationᵉ Rᵉ Sᵉ) → binary-htpyᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-Relationᵉ = eq-binary-htpyᵉ
```

## See also

-ᵉ [Largeᵉ binaryᵉ relations](foundation.large-binary-relations.mdᵉ)