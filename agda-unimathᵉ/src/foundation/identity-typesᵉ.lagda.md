# Identity types

```agda
module foundation.identity-typesᵉ where

open import foundation-core.identity-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.commuting-pentagons-of-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Theᵉ equalityᵉ relationᵉ onᵉ aᵉ typeᵉ isᵉ aᵉ reflexiveᵉ relation,ᵉ with theᵉ universalᵉ
propertyᵉ thatᵉ itᵉ mapsᵉ uniquelyᵉ intoᵉ anyᵉ otherᵉ reflexiveᵉ relation.ᵉ Inᵉ typeᵉ
theory,ᵉ weᵉ introduceᵉ theᵉ identityᵉ typeᵉ asᵉ anᵉ inductive familyᵉ ofᵉ types,ᵉ where
theᵉ inductionᵉ principleᵉ canᵉ beᵉ understoodᵉ asᵉ expressingᵉ thatᵉ theᵉ identityᵉ typeᵉ
isᵉ theᵉ leastᵉ reflexiveᵉ relation.ᵉ

## Table of files directly related to identity types

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ identityᵉ typesᵉ andᵉ operationsᵉ onᵉ
identificationsᵉ in arbitraryᵉ types.ᵉ

{{#includeᵉ tables/identity-types.mdᵉ}}

## Properties

### The Mac Lane pentagon for identity types

```agda
mac-lane-pentagonᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ dᵉ eᵉ : Aᵉ}
  (pᵉ : aᵉ ＝ᵉ bᵉ) (qᵉ : bᵉ ＝ᵉ cᵉ) (rᵉ : cᵉ ＝ᵉ dᵉ) (sᵉ : dᵉ ＝ᵉ eᵉ) →
  let α₁ᵉ = (apᵉ (_∙ᵉ sᵉ) (assocᵉ pᵉ qᵉ rᵉ))
      α₂ᵉ = (assocᵉ pᵉ (qᵉ ∙ᵉ rᵉ) sᵉ)
      α₃ᵉ = (apᵉ (pᵉ ∙ᵉ_) (assocᵉ qᵉ rᵉ sᵉ))
      α₄ᵉ = (assocᵉ (pᵉ ∙ᵉ qᵉ) rᵉ sᵉ)
      α₅ᵉ = (assocᵉ pᵉ qᵉ (rᵉ ∙ᵉ sᵉ))
  in
    coherence-pentagon-identificationsᵉ α₁ᵉ α₄ᵉ α₂ᵉ α₅ᵉ α₃ᵉ
mac-lane-pentagonᵉ reflᵉ reflᵉ reflᵉ reflᵉ = reflᵉ
```

### The groupoidal operations on identity types are equivalences

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  abstract
    is-equiv-invᵉ : (xᵉ yᵉ : Aᵉ) → is-equivᵉ (λ (pᵉ : xᵉ ＝ᵉ yᵉ) → invᵉ pᵉ)
    is-equiv-invᵉ xᵉ yᵉ = is-equiv-is-invertibleᵉ invᵉ inv-invᵉ inv-invᵉ

  equiv-invᵉ : (xᵉ yᵉ : Aᵉ) → (xᵉ ＝ᵉ yᵉ) ≃ᵉ (yᵉ ＝ᵉ xᵉ)
  pr1ᵉ (equiv-invᵉ xᵉ yᵉ) = invᵉ
  pr2ᵉ (equiv-invᵉ xᵉ yᵉ) = is-equiv-invᵉ xᵉ yᵉ

  abstract
    is-equiv-concatᵉ :
      {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (zᵉ : Aᵉ) → is-equivᵉ (concatᵉ pᵉ zᵉ)
    is-equiv-concatᵉ pᵉ zᵉ =
      is-equiv-is-invertibleᵉ
        ( inv-concatᵉ pᵉ zᵉ)
        ( is-section-inv-concatᵉ pᵉ)
        ( is-retraction-inv-concatᵉ pᵉ)

  abstract
    is-equiv-inv-concatᵉ :
      {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (zᵉ : Aᵉ) → is-equivᵉ (inv-concatᵉ pᵉ zᵉ)
    is-equiv-inv-concatᵉ pᵉ zᵉ =
      is-equiv-is-invertibleᵉ
        ( concatᵉ pᵉ zᵉ)
        ( is-retraction-inv-concatᵉ pᵉ)
        ( is-section-inv-concatᵉ pᵉ)

  equiv-concatᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (zᵉ : Aᵉ) → (yᵉ ＝ᵉ zᵉ) ≃ᵉ (xᵉ ＝ᵉ zᵉ)
  pr1ᵉ (equiv-concatᵉ pᵉ zᵉ) = concatᵉ pᵉ zᵉ
  pr2ᵉ (equiv-concatᵉ pᵉ zᵉ) = is-equiv-concatᵉ pᵉ zᵉ

  equiv-inv-concatᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (zᵉ : Aᵉ) → (xᵉ ＝ᵉ zᵉ) ≃ᵉ (yᵉ ＝ᵉ zᵉ)
  pr1ᵉ (equiv-inv-concatᵉ pᵉ zᵉ) = inv-concatᵉ pᵉ zᵉ
  pr2ᵉ (equiv-inv-concatᵉ pᵉ zᵉ) = is-equiv-inv-concatᵉ pᵉ zᵉ

  map-equiv-concat-equivᵉ :
    {xᵉ x'ᵉ : Aᵉ} → ((yᵉ : Aᵉ) → (xᵉ ＝ᵉ yᵉ) ≃ᵉ (x'ᵉ ＝ᵉ yᵉ)) → (x'ᵉ ＝ᵉ xᵉ)
  map-equiv-concat-equivᵉ {xᵉ} eᵉ = map-equivᵉ (eᵉ xᵉ) reflᵉ

  is-section-equiv-concatᵉ :
    {xᵉ x'ᵉ : Aᵉ} → map-equiv-concat-equivᵉ {xᵉ} {x'ᵉ} ∘ᵉ equiv-concatᵉ ~ᵉ idᵉ
  is-section-equiv-concatᵉ reflᵉ = reflᵉ

  abstract
    is-retraction-equiv-concatᵉ :
      {xᵉ x'ᵉ : Aᵉ} → equiv-concatᵉ ∘ᵉ map-equiv-concat-equivᵉ {xᵉ} {x'ᵉ} ~ᵉ idᵉ
    is-retraction-equiv-concatᵉ eᵉ =
      eq-htpyᵉ (λ yᵉ → eq-htpy-equivᵉ (λ where reflᵉ → right-unitᵉ))

  abstract
    is-equiv-map-equiv-concat-equivᵉ :
      {xᵉ x'ᵉ : Aᵉ} → is-equivᵉ (map-equiv-concat-equivᵉ {xᵉ} {x'ᵉ})
    is-equiv-map-equiv-concat-equivᵉ =
      is-equiv-is-invertibleᵉ
        ( equiv-concatᵉ)
        ( is-section-equiv-concatᵉ)
        ( is-retraction-equiv-concatᵉ)

  equiv-concat-equivᵉ :
    {xᵉ x'ᵉ : Aᵉ} → ((yᵉ : Aᵉ) → (xᵉ ＝ᵉ yᵉ) ≃ᵉ (x'ᵉ ＝ᵉ yᵉ)) ≃ᵉ (x'ᵉ ＝ᵉ xᵉ)
  pr1ᵉ equiv-concat-equivᵉ = map-equiv-concat-equivᵉ
  pr2ᵉ equiv-concat-equivᵉ = is-equiv-map-equiv-concat-equivᵉ

  abstract
    is-equiv-concat'ᵉ :
      (xᵉ : Aᵉ) {yᵉ zᵉ : Aᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ) → is-equivᵉ (concat'ᵉ xᵉ qᵉ)
    is-equiv-concat'ᵉ xᵉ qᵉ =
      is-equiv-is-invertibleᵉ
        ( inv-concat'ᵉ xᵉ qᵉ)
        ( is-section-inv-concat'ᵉ qᵉ)
        ( is-retraction-inv-concat'ᵉ qᵉ)

  abstract
    is-equiv-inv-concat'ᵉ :
      (xᵉ : Aᵉ) {yᵉ zᵉ : Aᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ) → is-equivᵉ (inv-concat'ᵉ xᵉ qᵉ)
    is-equiv-inv-concat'ᵉ xᵉ qᵉ =
      is-equiv-is-invertibleᵉ
        ( concat'ᵉ xᵉ qᵉ)
        ( is-retraction-inv-concat'ᵉ qᵉ)
        ( is-section-inv-concat'ᵉ qᵉ)

  equiv-concat'ᵉ :
    (xᵉ : Aᵉ) {yᵉ zᵉ : Aᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ) → (xᵉ ＝ᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ zᵉ)
  pr1ᵉ (equiv-concat'ᵉ xᵉ qᵉ) = concat'ᵉ xᵉ qᵉ
  pr2ᵉ (equiv-concat'ᵉ xᵉ qᵉ) = is-equiv-concat'ᵉ xᵉ qᵉ

  equiv-inv-concat'ᵉ :
    (xᵉ : Aᵉ) {yᵉ zᵉ : Aᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ) → (xᵉ ＝ᵉ zᵉ) ≃ᵉ (xᵉ ＝ᵉ yᵉ)
  pr1ᵉ (equiv-inv-concat'ᵉ xᵉ qᵉ) = inv-concat'ᵉ xᵉ qᵉ
  pr2ᵉ (equiv-inv-concat'ᵉ xᵉ qᵉ) = is-equiv-inv-concat'ᵉ xᵉ qᵉ

is-binary-equiv-concatᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} →
  is-binary-equivᵉ (λ (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) → pᵉ ∙ᵉ qᵉ)
pr1ᵉ (is-binary-equiv-concatᵉ {xᵉ = xᵉ}) qᵉ = is-equiv-concat'ᵉ xᵉ qᵉ
pr2ᵉ (is-binary-equiv-concatᵉ {zᵉ = zᵉ}) pᵉ = is-equiv-concatᵉ pᵉ zᵉ

equiv-binary-concatᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ} → (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : zᵉ ＝ᵉ wᵉ) →
  (yᵉ ＝ᵉ zᵉ) ≃ᵉ (xᵉ ＝ᵉ wᵉ)
equiv-binary-concatᵉ {xᵉ = xᵉ} {zᵉ = zᵉ} pᵉ qᵉ =
  (equiv-concat'ᵉ xᵉ qᵉ) ∘eᵉ (equiv-concatᵉ pᵉ zᵉ)

convert-eq-valuesᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ gᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ)
  (xᵉ yᵉ : Aᵉ) → (fᵉ xᵉ ＝ᵉ fᵉ yᵉ) ≃ᵉ (gᵉ xᵉ ＝ᵉ gᵉ yᵉ)
convert-eq-valuesᵉ {fᵉ = fᵉ} {gᵉ} Hᵉ xᵉ yᵉ =
  ( equiv-concat'ᵉ (gᵉ xᵉ) (Hᵉ yᵉ)) ∘eᵉ (equiv-concatᵉ (invᵉ (Hᵉ xᵉ)) (fᵉ yᵉ))

module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  is-section-is-injective-concatᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {qᵉ rᵉ : yᵉ ＝ᵉ zᵉ} (sᵉ : (pᵉ ∙ᵉ qᵉ) ＝ᵉ (pᵉ ∙ᵉ rᵉ)) →
    apᵉ (concatᵉ pᵉ zᵉ) (is-injective-concatᵉ pᵉ sᵉ) ＝ᵉ sᵉ
  is-section-is-injective-concatᵉ reflᵉ reflᵉ = reflᵉ

  cases-is-section-is-injective-concat'ᵉ :
    {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (sᵉ : pᵉ ＝ᵉ qᵉ) →
    ( apᵉ
      ( concat'ᵉ xᵉ reflᵉ)
      ( is-injective-concat'ᵉ reflᵉ (right-unitᵉ ∙ᵉ (sᵉ ∙ᵉ invᵉ right-unitᵉ)))) ＝ᵉ
    ( right-unitᵉ ∙ᵉ (sᵉ ∙ᵉ invᵉ right-unitᵉ))
  cases-is-section-is-injective-concat'ᵉ {pᵉ = reflᵉ} reflᵉ = reflᵉ

  is-section-is-injective-concat'ᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (rᵉ : yᵉ ＝ᵉ zᵉ) {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (sᵉ : (pᵉ ∙ᵉ rᵉ) ＝ᵉ (qᵉ ∙ᵉ rᵉ)) →
    apᵉ (concat'ᵉ xᵉ rᵉ) (is-injective-concat'ᵉ rᵉ sᵉ) ＝ᵉ sᵉ
  is-section-is-injective-concat'ᵉ reflᵉ sᵉ =
    ( apᵉ (λ uᵉ → apᵉ (concat'ᵉ _ reflᵉ) (is-injective-concat'ᵉ reflᵉ uᵉ)) (invᵉ αᵉ)) ∙ᵉ
    ( ( cases-is-section-is-injective-concat'ᵉ
        ( invᵉ right-unitᵉ ∙ᵉ (sᵉ ∙ᵉ right-unitᵉ))) ∙ᵉ
      ( αᵉ))
    where
    αᵉ :
      ( ( right-unitᵉ) ∙ᵉ
        ( ( invᵉ right-unitᵉ ∙ᵉ (sᵉ ∙ᵉ right-unitᵉ)) ∙ᵉ
          ( invᵉ right-unitᵉ))) ＝ᵉ
      ( sᵉ)
    αᵉ =
      ( apᵉ
        ( concatᵉ right-unitᵉ _)
        ( ( assocᵉ (invᵉ right-unitᵉ) (sᵉ ∙ᵉ right-unitᵉ) (invᵉ right-unitᵉ)) ∙ᵉ
          ( ( apᵉ
              ( concatᵉ (invᵉ right-unitᵉ) _)
              ( ( assocᵉ sᵉ right-unitᵉ (invᵉ right-unitᵉ)) ∙ᵉ
                ( ( apᵉ (concatᵉ sᵉ _) (right-invᵉ right-unitᵉ)) ∙ᵉ
                  ( right-unitᵉ))))))) ∙ᵉ
      ( ( invᵉ (assocᵉ right-unitᵉ (invᵉ right-unitᵉ) sᵉ)) ∙ᵉ
        ( ( apᵉ (concat'ᵉ _ sᵉ) (right-invᵉ right-unitᵉ))))
```

### Applying the right unit law on one side of a higher identification is an equivalence

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ}
  where

  equiv-right-unitᵉ : (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : xᵉ ＝ᵉ yᵉ) → (pᵉ ＝ᵉ qᵉ) ≃ᵉ (pᵉ ∙ᵉ reflᵉ ＝ᵉ qᵉ)
  equiv-right-unitᵉ pᵉ = equiv-concatᵉ right-unitᵉ

  equiv-right-unit'ᵉ : (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : xᵉ ＝ᵉ yᵉ) → (pᵉ ＝ᵉ qᵉ ∙ᵉ reflᵉ) ≃ᵉ (pᵉ ＝ᵉ qᵉ)
  equiv-right-unit'ᵉ pᵉ qᵉ = equiv-concat'ᵉ pᵉ right-unitᵉ
```

### Reassociating one side of a higher identification is an equivalence

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ uᵉ : Aᵉ}
  where

  equiv-concat-assocᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : zᵉ ＝ᵉ uᵉ) (sᵉ : xᵉ ＝ᵉ uᵉ) →
    ((pᵉ ∙ᵉ qᵉ) ∙ᵉ rᵉ ＝ᵉ sᵉ) ≃ᵉ (pᵉ ∙ᵉ (qᵉ ∙ᵉ rᵉ) ＝ᵉ sᵉ)
  equiv-concat-assocᵉ pᵉ qᵉ rᵉ = equiv-concatᵉ (invᵉ (assocᵉ pᵉ qᵉ rᵉ))

  equiv-concat-assoc'ᵉ :
    (sᵉ : xᵉ ＝ᵉ uᵉ) (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : zᵉ ＝ᵉ uᵉ) →
    (sᵉ ＝ᵉ (pᵉ ∙ᵉ qᵉ) ∙ᵉ rᵉ) ≃ᵉ (sᵉ ＝ᵉ pᵉ ∙ᵉ (qᵉ ∙ᵉ rᵉ))
  equiv-concat-assoc'ᵉ sᵉ pᵉ qᵉ rᵉ = equiv-concat'ᵉ sᵉ (assocᵉ pᵉ qᵉ rᵉ)
```

### Transposing inverses is an equivalence

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ}
  where

  abstract
    is-equiv-left-transpose-eq-concatᵉ :
      (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : xᵉ ＝ᵉ zᵉ) →
      is-equivᵉ (left-transpose-eq-concatᵉ pᵉ qᵉ rᵉ)
    is-equiv-left-transpose-eq-concatᵉ reflᵉ qᵉ rᵉ = is-equiv-idᵉ

  equiv-left-transpose-eq-concatᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : xᵉ ＝ᵉ zᵉ) →
    ((pᵉ ∙ᵉ qᵉ) ＝ᵉ rᵉ) ≃ᵉ (qᵉ ＝ᵉ ((invᵉ pᵉ) ∙ᵉ rᵉ))
  pr1ᵉ (equiv-left-transpose-eq-concatᵉ pᵉ qᵉ rᵉ) = left-transpose-eq-concatᵉ pᵉ qᵉ rᵉ
  pr2ᵉ (equiv-left-transpose-eq-concatᵉ pᵉ qᵉ rᵉ) =
    is-equiv-left-transpose-eq-concatᵉ pᵉ qᵉ rᵉ

  equiv-left-transpose-eq-concat'ᵉ :
    (pᵉ : xᵉ ＝ᵉ zᵉ) (qᵉ : xᵉ ＝ᵉ yᵉ) (rᵉ : yᵉ ＝ᵉ zᵉ) →
    (pᵉ ＝ᵉ qᵉ ∙ᵉ rᵉ) ≃ᵉ (invᵉ qᵉ ∙ᵉ pᵉ ＝ᵉ rᵉ)
  equiv-left-transpose-eq-concat'ᵉ pᵉ qᵉ rᵉ =
    equiv-invᵉ _ _ ∘eᵉ equiv-left-transpose-eq-concatᵉ qᵉ rᵉ pᵉ ∘eᵉ equiv-invᵉ _ _

  left-transpose-eq-concat'ᵉ :
    (pᵉ : xᵉ ＝ᵉ zᵉ) (qᵉ : xᵉ ＝ᵉ yᵉ) (rᵉ : yᵉ ＝ᵉ zᵉ) →
    pᵉ ＝ᵉ qᵉ ∙ᵉ rᵉ → invᵉ qᵉ ∙ᵉ pᵉ ＝ᵉ rᵉ
  left-transpose-eq-concat'ᵉ pᵉ qᵉ rᵉ =
    map-equivᵉ (equiv-left-transpose-eq-concat'ᵉ pᵉ qᵉ rᵉ)

  abstract
    is-equiv-right-transpose-eq-concatᵉ :
      (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : xᵉ ＝ᵉ zᵉ) →
      is-equivᵉ (right-transpose-eq-concatᵉ pᵉ qᵉ rᵉ)
    is-equiv-right-transpose-eq-concatᵉ pᵉ reflᵉ rᵉ =
      is-equiv-compᵉ
        ( concat'ᵉ pᵉ (invᵉ right-unitᵉ))
        ( concatᵉ (invᵉ right-unitᵉ) rᵉ)
        ( is-equiv-concatᵉ (invᵉ right-unitᵉ) rᵉ)
        ( is-equiv-concat'ᵉ pᵉ (invᵉ right-unitᵉ))

  equiv-right-transpose-eq-concatᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : xᵉ ＝ᵉ zᵉ) →
    (pᵉ ∙ᵉ qᵉ ＝ᵉ rᵉ) ≃ᵉ (pᵉ ＝ᵉ rᵉ ∙ᵉ invᵉ qᵉ)
  pr1ᵉ (equiv-right-transpose-eq-concatᵉ pᵉ qᵉ rᵉ) = right-transpose-eq-concatᵉ pᵉ qᵉ rᵉ
  pr2ᵉ (equiv-right-transpose-eq-concatᵉ pᵉ qᵉ rᵉ) =
    is-equiv-right-transpose-eq-concatᵉ pᵉ qᵉ rᵉ

  equiv-right-transpose-eq-concat'ᵉ :
    (pᵉ : xᵉ ＝ᵉ zᵉ) (qᵉ : xᵉ ＝ᵉ yᵉ) (rᵉ : yᵉ ＝ᵉ zᵉ) →
    (pᵉ ＝ᵉ qᵉ ∙ᵉ rᵉ) ≃ᵉ (pᵉ ∙ᵉ invᵉ rᵉ ＝ᵉ qᵉ)
  equiv-right-transpose-eq-concat'ᵉ pᵉ qᵉ rᵉ =
    equiv-invᵉ qᵉ (pᵉ ∙ᵉ invᵉ rᵉ) ∘eᵉ
    equiv-right-transpose-eq-concatᵉ qᵉ rᵉ pᵉ ∘eᵉ
    equiv-invᵉ pᵉ (qᵉ ∙ᵉ rᵉ)

  right-transpose-eq-concat'ᵉ :
    (pᵉ : xᵉ ＝ᵉ zᵉ) (qᵉ : xᵉ ＝ᵉ yᵉ) (rᵉ : yᵉ ＝ᵉ zᵉ) →
    pᵉ ＝ᵉ qᵉ ∙ᵉ rᵉ → pᵉ ∙ᵉ invᵉ rᵉ ＝ᵉ qᵉ
  right-transpose-eq-concat'ᵉ pᵉ qᵉ rᵉ =
    map-equivᵉ (equiv-right-transpose-eq-concat'ᵉ pᵉ qᵉ rᵉ)
```

### Computation of fibers of families of maps out of the identity type

Weᵉ showᵉ thatᵉ `fiberᵉ (fᵉ xᵉ) yᵉ ≃ᵉ ((*ᵉ ,ᵉ fᵉ *ᵉ reflᵉ) ＝ᵉ (xᵉ ,ᵉ y))`ᵉ forᵉ everyᵉ `xᵉ : A`ᵉ andᵉ
`yᵉ : Bᵉ x`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {aᵉ : Aᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ) (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ)
  where

  map-compute-fiber-map-out-of-identity-typeᵉ :
    fiberᵉ (fᵉ xᵉ) yᵉ → ((aᵉ ,ᵉ fᵉ aᵉ reflᵉ) ＝ᵉ (xᵉ ,ᵉ yᵉ))
  map-compute-fiber-map-out-of-identity-typeᵉ (reflᵉ ,ᵉ reflᵉ) = reflᵉ

  map-inv-compute-fiber-map-out-of-identity-typeᵉ :
    ((aᵉ ,ᵉ fᵉ aᵉ reflᵉ) ＝ᵉ (xᵉ ,ᵉ yᵉ)) → fiberᵉ (fᵉ xᵉ) yᵉ
  map-inv-compute-fiber-map-out-of-identity-typeᵉ reflᵉ =
    reflᵉ ,ᵉ reflᵉ

  is-section-map-inv-compute-fiber-map-out-of-identity-typeᵉ :
    map-compute-fiber-map-out-of-identity-typeᵉ ∘ᵉ
    map-inv-compute-fiber-map-out-of-identity-typeᵉ ~ᵉ idᵉ
  is-section-map-inv-compute-fiber-map-out-of-identity-typeᵉ reflᵉ = reflᵉ

  is-retraction-map-inv-compute-fiber-map-out-of-identity-typeᵉ :
    map-inv-compute-fiber-map-out-of-identity-typeᵉ ∘ᵉ
    map-compute-fiber-map-out-of-identity-typeᵉ ~ᵉ idᵉ
  is-retraction-map-inv-compute-fiber-map-out-of-identity-typeᵉ (reflᵉ ,ᵉ reflᵉ) =
    reflᵉ

  is-equiv-map-compute-fiber-map-out-of-identity-typeᵉ :
    is-equivᵉ map-compute-fiber-map-out-of-identity-typeᵉ
  is-equiv-map-compute-fiber-map-out-of-identity-typeᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-compute-fiber-map-out-of-identity-typeᵉ
      is-section-map-inv-compute-fiber-map-out-of-identity-typeᵉ
      is-retraction-map-inv-compute-fiber-map-out-of-identity-typeᵉ

  compute-fiber-map-out-of-identity-typeᵉ :
    fiberᵉ (fᵉ xᵉ) yᵉ ≃ᵉ ((aᵉ ,ᵉ fᵉ aᵉ reflᵉ) ＝ᵉ (xᵉ ,ᵉ yᵉ))
  pr1ᵉ compute-fiber-map-out-of-identity-typeᵉ =
    map-compute-fiber-map-out-of-identity-typeᵉ
  pr2ᵉ compute-fiber-map-out-of-identity-typeᵉ =
    is-equiv-map-compute-fiber-map-out-of-identity-typeᵉ
```