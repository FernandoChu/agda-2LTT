# Coproducts of species of types

```agda
module species.coproducts-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.universal-property-coproduct-typesᵉ
open import foundation.universe-levelsᵉ

open import species.morphisms-species-of-typesᵉ
open import species.species-of-typesᵉ
```

</details>

## Idea

Theᵉ coproductᵉ ofᵉ twoᵉ speciesᵉ ofᵉ typesᵉ `F`ᵉ andᵉ `G`ᵉ isᵉ theᵉ pointwiseᵉ coproduct.ᵉ

## Definition

### Coproduct on objects

```agda
coproduct-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Fᵉ : species-typesᵉ l1ᵉ l2ᵉ) (Gᵉ : species-typesᵉ l1ᵉ l3ᵉ) →
  species-typesᵉ l1ᵉ (l2ᵉ ⊔ l3ᵉ)
coproduct-species-typesᵉ Fᵉ Gᵉ Xᵉ = Fᵉ Xᵉ +ᵉ Gᵉ Xᵉ
```

## Universal properties

Proofᵉ ofᵉ (hom-species-typesᵉ (species-types-coproductᵉ Fᵉ Gᵉ) Hᵉ) ≃ᵉ
((hom-species-typesᵉ Fᵉ Hᵉ) ×ᵉ (hom-species-typesᵉ Gᵉ H)).ᵉ

```agda
equiv-universal-property-coproduct-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Fᵉ : species-typesᵉ l1ᵉ l2ᵉ)
  (Gᵉ : species-typesᵉ l1ᵉ l3ᵉ)
  (Hᵉ : species-typesᵉ l1ᵉ l4ᵉ) →
  hom-species-typesᵉ (coproduct-species-typesᵉ Fᵉ Gᵉ) Hᵉ ≃ᵉ
  ((hom-species-typesᵉ Fᵉ Hᵉ) ×ᵉ (hom-species-typesᵉ Gᵉ Hᵉ))
equiv-universal-property-coproduct-species-typesᵉ Fᵉ Gᵉ Hᵉ =
  ( distributive-Π-Σᵉ) ∘eᵉ
  ( equiv-Π-equiv-familyᵉ (λ Xᵉ → equiv-universal-property-coproductᵉ (Hᵉ Xᵉ)))
```