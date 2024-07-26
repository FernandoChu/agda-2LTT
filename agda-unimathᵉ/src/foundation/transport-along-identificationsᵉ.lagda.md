# Transport along identifications

```agda
module foundation.transport-along-identificationsᵉ where

open import foundation-core.transport-along-identificationsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`,ᵉ anᵉ
[identification](foundation-core.identity-types.mdᵉ) `pᵉ : xᵉ ＝ᵉ y`ᵉ in `A`ᵉ andᵉ anᵉ
elementᵉ `bᵉ : Bᵉ x`,ᵉ weᵉ canᵉ
[**transport**](foundation-core.transport-along-identifications.mdᵉ) theᵉ elementᵉ
`b`ᵉ alongᵉ theᵉ identificationᵉ `p`ᵉ to obtainᵉ anᵉ elementᵉ `trᵉ Bᵉ pᵉ bᵉ : Bᵉ y`.ᵉ

Theᵉ factᵉ thatᵉ `trᵉ Bᵉ p`ᵉ isᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) isᵉ
recordedᵉ onᵉ thisᵉ page.ᵉ

## Properties

### Transport is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) {xᵉ yᵉ : Aᵉ}
  where

  inv-trᵉ : xᵉ ＝ᵉ yᵉ → Bᵉ yᵉ → Bᵉ xᵉ
  inv-trᵉ pᵉ = trᵉ Bᵉ (invᵉ pᵉ)

  is-retraction-inv-trᵉ : (pᵉ : xᵉ ＝ᵉ yᵉ) → inv-trᵉ pᵉ ∘ᵉ trᵉ Bᵉ pᵉ ~ᵉ idᵉ
  is-retraction-inv-trᵉ reflᵉ bᵉ = reflᵉ

  is-section-inv-trᵉ : (pᵉ : xᵉ ＝ᵉ yᵉ) → trᵉ Bᵉ pᵉ ∘ᵉ inv-trᵉ pᵉ ~ᵉ idᵉ
  is-section-inv-trᵉ reflᵉ bᵉ = reflᵉ

  is-equiv-trᵉ : (pᵉ : xᵉ ＝ᵉ yᵉ) → is-equivᵉ (trᵉ Bᵉ pᵉ)
  is-equiv-trᵉ pᵉ =
    is-equiv-is-invertibleᵉ
      ( inv-trᵉ pᵉ)
      ( is-section-inv-trᵉ pᵉ)
      ( is-retraction-inv-trᵉ pᵉ)

  equiv-trᵉ : xᵉ ＝ᵉ yᵉ → Bᵉ xᵉ ≃ᵉ Bᵉ yᵉ
  pr1ᵉ (equiv-trᵉ pᵉ) = trᵉ Bᵉ pᵉ
  pr2ᵉ (equiv-trᵉ pᵉ) = is-equiv-trᵉ pᵉ
```

### Transporting along `refl` is the identity equivalence

```agda
equiv-tr-reflᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) {xᵉ : Aᵉ} →
  equiv-trᵉ Bᵉ reflᵉ ＝ᵉ id-equivᵉ {Aᵉ = Bᵉ xᵉ}
equiv-tr-reflᵉ Bᵉ = reflᵉ
```

### Computing transport of loops

```agda
tr-loopᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {a0ᵉ a1ᵉ : Aᵉ} (pᵉ : a0ᵉ ＝ᵉ a1ᵉ) (qᵉ : a0ᵉ ＝ᵉ a0ᵉ) →
  trᵉ (λ yᵉ → yᵉ ＝ᵉ yᵉ) pᵉ qᵉ ＝ᵉ (invᵉ pᵉ ∙ᵉ qᵉ) ∙ᵉ pᵉ
tr-loopᵉ reflᵉ qᵉ = invᵉ right-unitᵉ
```