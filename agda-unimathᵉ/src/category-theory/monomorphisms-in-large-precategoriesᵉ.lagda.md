# Monomorphisms in large precategories

```agda
module category-theory.monomorphisms-in-large-precategoriesᵉ where
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

Aᵉ morphismᵉ `fᵉ : xᵉ → y`ᵉ isᵉ aᵉ monomorphismᵉ ifᵉ wheneverᵉ weᵉ haveᵉ twoᵉ morphismsᵉ
`gᵉ hᵉ : wᵉ → x`ᵉ suchᵉ thatᵉ `fᵉ ∘ᵉ gᵉ = fᵉ ∘ᵉ h`,ᵉ thenᵉ in factᵉ `gᵉ = h`.ᵉ Theᵉ wayᵉ to stateᵉ
thisᵉ in Homotopyᵉ Typeᵉ Theoryᵉ isᵉ to sayᵉ thatᵉ postcompositionᵉ byᵉ `f`ᵉ isᵉ anᵉ
embedding.ᵉ

## Definition

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level)
  (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) (Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ)
  (fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  is-mono-prop-Large-Precategoryᵉ : Propᵉ (αᵉ l3ᵉ ⊔ βᵉ l3ᵉ l1ᵉ ⊔ βᵉ l3ᵉ l2ᵉ)
  is-mono-prop-Large-Precategoryᵉ =
    Π-Propᵉ
      ( obj-Large-Precategoryᵉ Cᵉ l3ᵉ)
      ( λ Zᵉ → is-emb-Propᵉ (comp-hom-Large-Precategoryᵉ Cᵉ {Xᵉ = Zᵉ} fᵉ))

  is-mono-Large-Precategoryᵉ : UUᵉ (αᵉ l3ᵉ ⊔ βᵉ l3ᵉ l1ᵉ ⊔ βᵉ l3ᵉ l2ᵉ)
  is-mono-Large-Precategoryᵉ = type-Propᵉ is-mono-prop-Large-Precategoryᵉ

  is-prop-is-mono-Large-Precategoryᵉ : is-propᵉ is-mono-Large-Precategoryᵉ
  is-prop-is-mono-Large-Precategoryᵉ =
    is-prop-type-Propᵉ is-mono-prop-Large-Precategoryᵉ
```

## Properties

### Isomorphisms are monomorphisms

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ) {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level)
  (Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ) (Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ)
  (fᵉ : iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
  where

  is-mono-iso-Large-Precategoryᵉ :
    is-mono-Large-Precategoryᵉ Cᵉ l3ᵉ Xᵉ Yᵉ (hom-iso-Large-Precategoryᵉ Cᵉ fᵉ)
  is-mono-iso-Large-Precategoryᵉ Zᵉ =
    is-emb-is-equivᵉ (is-equiv-postcomp-hom-iso-Large-Precategoryᵉ Cᵉ fᵉ Zᵉ)
```