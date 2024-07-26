# The universal property of booleans

```agda
module foundation.universal-property-booleansᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleansᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

```agda
ev-true-falseᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → (fᵉ : boolᵉ → Aᵉ) → Aᵉ ×ᵉ Aᵉ
ev-true-falseᵉ Aᵉ fᵉ = pairᵉ (fᵉ trueᵉ) (fᵉ falseᵉ)

map-universal-property-boolᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
  Aᵉ ×ᵉ Aᵉ → (boolᵉ → Aᵉ)
map-universal-property-boolᵉ (pairᵉ xᵉ yᵉ) trueᵉ = xᵉ
map-universal-property-boolᵉ (pairᵉ xᵉ yᵉ) falseᵉ = yᵉ

abstract
  is-section-map-universal-property-boolᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
    ((ev-true-falseᵉ Aᵉ) ∘ᵉ map-universal-property-boolᵉ) ~ᵉ idᵉ
  is-section-map-universal-property-boolᵉ (pairᵉ xᵉ yᵉ) =
    eq-pairᵉ reflᵉ reflᵉ

abstract
  is-retraction-map-universal-property-bool'ᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (fᵉ : boolᵉ → Aᵉ) →
    (map-universal-property-boolᵉ (ev-true-falseᵉ Aᵉ fᵉ)) ~ᵉ fᵉ
  is-retraction-map-universal-property-bool'ᵉ fᵉ trueᵉ = reflᵉ
  is-retraction-map-universal-property-bool'ᵉ fᵉ falseᵉ = reflᵉ

abstract
  is-retraction-map-universal-property-boolᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
    (map-universal-property-boolᵉ ∘ᵉ (ev-true-falseᵉ Aᵉ)) ~ᵉ idᵉ
  is-retraction-map-universal-property-boolᵉ fᵉ =
    eq-htpyᵉ (is-retraction-map-universal-property-bool'ᵉ fᵉ)

abstract
  universal-property-boolᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
    is-equivᵉ (λ (fᵉ : boolᵉ → Aᵉ) → pairᵉ (fᵉ trueᵉ) (fᵉ falseᵉ))
  universal-property-boolᵉ Aᵉ =
    is-equiv-is-invertibleᵉ
      map-universal-property-boolᵉ
      is-section-map-universal-property-boolᵉ
      is-retraction-map-universal-property-boolᵉ

ev-trueᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → (boolᵉ → Aᵉ) → Aᵉ
ev-trueᵉ fᵉ = fᵉ trueᵉ

triangle-ev-trueᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
  ev-trueᵉ ~ᵉ pr1ᵉ ∘ᵉ ev-true-falseᵉ Aᵉ
triangle-ev-trueᵉ Aᵉ = refl-htpyᵉ

{-ᵉ
aut-bool-boolᵉ :
  boolᵉ → (boolᵉ ≃ᵉ boolᵉ)
aut-bool-boolᵉ trueᵉ = id-equivᵉ
aut-bool-boolᵉ falseᵉ = equiv-neg-𝟚ᵉ

bool-aut-boolᵉ :
  (boolᵉ ≃ᵉ boolᵉ) → boolᵉ
bool-aut-boolᵉ eᵉ = map-equivᵉ eᵉ trueᵉ

decide-true-falseᵉ :
  (bᵉ : boolᵉ) → coproductᵉ (bᵉ ＝ᵉ trueᵉ) (bᵉ ＝ᵉ falseᵉ)
decide-true-falseᵉ trueᵉ = inlᵉ reflᵉ
decide-true-falseᵉ falseᵉ = inrᵉ reflᵉ

eq-falseᵉ :
  (bᵉ : boolᵉ) → (bᵉ ≠ᵉ trueᵉ) → (bᵉ ＝ᵉ falseᵉ)
eq-falseᵉ trueᵉ pᵉ = ind-emptyᵉ (pᵉ reflᵉ)
eq-falseᵉ falseᵉ pᵉ = reflᵉ

eq-trueᵉ :
  (bᵉ : boolᵉ) → bᵉ ≠ᵉ falseᵉ → bᵉ ＝ᵉ trueᵉ
eq-trueᵉ trueᵉ pᵉ = reflᵉ
eq-trueᵉ falseᵉ pᵉ = ind-emptyᵉ (pᵉ reflᵉ)

Eq-𝟚-eqᵉ : (xᵉ yᵉ : boolᵉ) → xᵉ ＝ᵉ yᵉ → Eq-𝟚ᵉ xᵉ yᵉ
Eq-𝟚-eqᵉ xᵉ .xᵉ reflᵉ = reflexive-Eq-𝟚ᵉ xᵉ

eq-false-equiv'ᵉ :
  (eᵉ : boolᵉ ≃ᵉ boolᵉ) → map-equivᵉ eᵉ trueᵉ ＝ᵉ trueᵉ →
  is-decidableᵉ (map-equivᵉ eᵉ falseᵉ ＝ᵉ falseᵉ) → map-equivᵉ eᵉ falseᵉ ＝ᵉ falseᵉ
eq-false-equiv'ᵉ eᵉ pᵉ (inlᵉ qᵉ) = qᵉ
eq-false-equiv'ᵉ eᵉ pᵉ (inrᵉ xᵉ) =
  ind-emptyᵉ
    ( Eq-𝟚-eqᵉ trueᵉ falseᵉ
      ( apᵉ pr1ᵉ
        ( eq-is-contr'ᵉ
          ( is-contr-map-is-equivᵉ (is-equiv-map-equivᵉ eᵉ) trueᵉ)
          ( pairᵉ trueᵉ pᵉ)
          ( pairᵉ falseᵉ (eq-trueᵉ (map-equivᵉ eᵉ falseᵉ) xᵉ)))))
-ᵉ}
```