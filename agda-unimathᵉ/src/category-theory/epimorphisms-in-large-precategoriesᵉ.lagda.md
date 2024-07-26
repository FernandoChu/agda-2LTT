# Epimorphism in large precategories

```agda
module category-theory.epimorphisms-in-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategoriesᵉ
open import category-theory.large-precategoriesᵉ

open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ morphismᵉ `fᵉ : xᵉ → y`ᵉ isᵉ aᵉ epimorphismᵉ ifᵉ wheneverᵉ weᵉ haveᵉ twoᵉ morphismsᵉ
`gᵉ hᵉ : yᵉ → w`ᵉ suchᵉ thatᵉ `gᵉ ∘ᵉ fᵉ = hᵉ ∘ᵉ f`,ᵉ thenᵉ in factᵉ `gᵉ = h`.ᵉ Theᵉ wayᵉ to stateᵉ
thisᵉ in Homotopyᵉ Typeᵉ Theoryᵉ isᵉ to sayᵉ thatᵉ precompositionᵉ byᵉ `f`ᵉ isᵉ anᵉ
embedding.ᵉ

## Definition

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level)
  (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) (Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ)
  (fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  is-epi-prop-Large-Precategoryᵉ : Propᵉ (αᵉ l3ᵉ ⊔ βᵉ l1ᵉ l3ᵉ ⊔ βᵉ l2ᵉ l3ᵉ)
  is-epi-prop-Large-Precategoryᵉ =
    Π-Propᵉ
      ( obj-Large-Precategoryᵉ Cᵉ l3ᵉ)
      ( λ Zᵉ → is-emb-Propᵉ (λ gᵉ → comp-hom-Large-Precategoryᵉ Cᵉ {Zᵉ = Zᵉ} gᵉ fᵉ))

  is-epi-Large-Precategoryᵉ : UUᵉ (αᵉ l3ᵉ ⊔ βᵉ l1ᵉ l3ᵉ ⊔ βᵉ l2ᵉ l3ᵉ)
  is-epi-Large-Precategoryᵉ = type-Propᵉ is-epi-prop-Large-Precategoryᵉ

  is-prop-is-epi-Large-Precategoryᵉ : is-propᵉ is-epi-Large-Precategoryᵉ
  is-prop-is-epi-Large-Precategoryᵉ =
    is-prop-type-Propᵉ is-epi-prop-Large-Precategoryᵉ
```

## Properties

### Isomorphisms are epimorphisms

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level)
  (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) (Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ)
  (fᵉ : iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  is-epi-iso-Large-Precategoryᵉ :
    is-epi-Large-Precategoryᵉ Cᵉ l3ᵉ Xᵉ Yᵉ (hom-iso-Large-Precategoryᵉ Cᵉ fᵉ)
  is-epi-iso-Large-Precategoryᵉ Zᵉ =
    is-emb-is-equivᵉ (is-equiv-precomp-hom-iso-Large-Precategoryᵉ Cᵉ fᵉ Zᵉ)
```