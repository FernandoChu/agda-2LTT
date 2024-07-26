# W-types

```agda
module trees.w-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.setsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import trees.algebras-polynomial-endofunctorsᵉ
open import trees.coalgebras-polynomial-endofunctorsᵉ
open import trees.morphisms-algebras-polynomial-endofunctorsᵉ
open import trees.polynomial-endofunctorsᵉ
```

</details>

## Idea

Considerᵉ aᵉ typeᵉ `A`ᵉ equippedᵉ with aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`.ᵉ Theᵉ typeᵉ `W`ᵉ
generatedᵉ inductivelyᵉ byᵉ aᵉ constructor `Bᵉ xᵉ → W`ᵉ forᵉ eachᵉ `xᵉ : A`ᵉ isᵉ calledᵉ theᵉ
**W-type**ᵉ `Wᵉ Aᵉ B`ᵉ ofᵉ `B`.ᵉ Theᵉ elementsᵉ ofᵉ `A`ᵉ canᵉ beᵉ thoughtᵉ ofᵉ asᵉ symbolsᵉ forᵉ
theᵉ constructorsᵉ ofᵉ `Wᵉ Aᵉ B`,ᵉ andᵉ theᵉ functionsᵉ `Bᵉ xᵉ → Wᵉ Aᵉ B`ᵉ areᵉ theᵉ
constructors.ᵉ Theᵉ elementsᵉ ofᵉ `Wᵉ Aᵉ B`ᵉ canᵉ beᵉ thoughtᵉ ofᵉ asᵉ well-foundedᵉ trees.ᵉ

## Definition

```agda
data 𝕎ᵉ {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ) where
  tree-𝕎ᵉ : (xᵉ : Aᵉ) (αᵉ : Bᵉ xᵉ → 𝕎ᵉ Aᵉ Bᵉ) → 𝕎ᵉ Aᵉ Bᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  shape-𝕎ᵉ : 𝕎ᵉ Aᵉ Bᵉ → Aᵉ
  shape-𝕎ᵉ (tree-𝕎ᵉ xᵉ αᵉ) = xᵉ

  component-𝕎ᵉ : (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → Bᵉ (shape-𝕎ᵉ xᵉ) → 𝕎ᵉ Aᵉ Bᵉ
  component-𝕎ᵉ (tree-𝕎ᵉ xᵉ αᵉ) = αᵉ

  η-𝕎ᵉ : (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → tree-𝕎ᵉ (shape-𝕎ᵉ xᵉ) (component-𝕎ᵉ xᵉ) ＝ᵉ xᵉ
  η-𝕎ᵉ (tree-𝕎ᵉ xᵉ αᵉ) = reflᵉ
```

### W-types as algebras for a polynomial endofunctor

```agda
structure-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  type-polynomial-endofunctorᵉ Aᵉ Bᵉ (𝕎ᵉ Aᵉ Bᵉ) → 𝕎ᵉ Aᵉ Bᵉ
structure-𝕎-Algᵉ (pairᵉ xᵉ αᵉ) = tree-𝕎ᵉ xᵉ αᵉ

𝕎-Algᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
  algebra-polynomial-endofunctorᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ Bᵉ
𝕎-Algᵉ Aᵉ Bᵉ = pairᵉ (𝕎ᵉ Aᵉ Bᵉ) structure-𝕎-Algᵉ
```

### W-types as coalgebras for a polynomial endofunctor

```agda
𝕎-Coalgᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
  coalgebra-polynomial-endofunctorᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ Bᵉ
pr1ᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ) = 𝕎ᵉ Aᵉ Bᵉ
pr1ᵉ (pr2ᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ) xᵉ) = shape-𝕎ᵉ xᵉ
pr2ᵉ (pr2ᵉ (𝕎-Coalgᵉ Aᵉ Bᵉ) xᵉ) = component-𝕎ᵉ xᵉ
```

## Properties

### The elements of the form `tree-𝕎 x α` where `B x` is an empty type are called the constants of `W A B`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  constant-𝕎ᵉ : (xᵉ : Aᵉ) → is-emptyᵉ (Bᵉ xᵉ) → 𝕎ᵉ Aᵉ Bᵉ
  constant-𝕎ᵉ xᵉ hᵉ = tree-𝕎ᵉ xᵉ (ex-falsoᵉ ∘ᵉ hᵉ)

  is-constant-𝕎ᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ l2ᵉ
  is-constant-𝕎ᵉ xᵉ = is-emptyᵉ (Bᵉ (shape-𝕎ᵉ xᵉ))
```

### If each `B x` is inhabited, then the type `W A B` is empty

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  is-empty-𝕎ᵉ : ((xᵉ : Aᵉ) → type-trunc-Propᵉ (Bᵉ xᵉ)) → is-emptyᵉ (𝕎ᵉ Aᵉ Bᵉ)
  is-empty-𝕎ᵉ Hᵉ (tree-𝕎ᵉ xᵉ αᵉ) =
    apply-universal-property-trunc-Propᵉ
      ( Hᵉ xᵉ)
      ( empty-Propᵉ)
      ( λ yᵉ → is-empty-𝕎ᵉ Hᵉ (αᵉ yᵉ))
```

### Equality of W-types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  Eq-𝕎ᵉ : 𝕎ᵉ Aᵉ Bᵉ → 𝕎ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  Eq-𝕎ᵉ (tree-𝕎ᵉ xᵉ αᵉ) (tree-𝕎ᵉ yᵉ βᵉ) =
    Σᵉ (xᵉ ＝ᵉ yᵉ) (λ pᵉ → (zᵉ : Bᵉ xᵉ) → Eq-𝕎ᵉ (αᵉ zᵉ) (βᵉ (trᵉ Bᵉ pᵉ zᵉ)))

  refl-Eq-𝕎ᵉ : (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → Eq-𝕎ᵉ wᵉ wᵉ
  refl-Eq-𝕎ᵉ (tree-𝕎ᵉ xᵉ αᵉ) = pairᵉ reflᵉ (λ zᵉ → refl-Eq-𝕎ᵉ (αᵉ zᵉ))

  center-total-Eq-𝕎ᵉ : (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → Σᵉ (𝕎ᵉ Aᵉ Bᵉ) (Eq-𝕎ᵉ wᵉ)
  center-total-Eq-𝕎ᵉ wᵉ = pairᵉ wᵉ (refl-Eq-𝕎ᵉ wᵉ)

  aux-total-Eq-𝕎ᵉ :
    (xᵉ : Aᵉ) (αᵉ : Bᵉ xᵉ → 𝕎ᵉ Aᵉ Bᵉ) →
    Σᵉ (Bᵉ xᵉ → 𝕎ᵉ Aᵉ Bᵉ) (λ βᵉ → (yᵉ : Bᵉ xᵉ) → Eq-𝕎ᵉ (αᵉ yᵉ) (βᵉ yᵉ)) →
    Σᵉ (𝕎ᵉ Aᵉ Bᵉ) (Eq-𝕎ᵉ (tree-𝕎ᵉ xᵉ αᵉ))
  aux-total-Eq-𝕎ᵉ xᵉ αᵉ (pairᵉ βᵉ eᵉ) = pairᵉ (tree-𝕎ᵉ xᵉ βᵉ) (pairᵉ reflᵉ eᵉ)

  contraction-total-Eq-𝕎ᵉ :
    (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) (tᵉ : Σᵉ (𝕎ᵉ Aᵉ Bᵉ) (Eq-𝕎ᵉ wᵉ)) → center-total-Eq-𝕎ᵉ wᵉ ＝ᵉ tᵉ
  contraction-total-Eq-𝕎ᵉ
    ( tree-𝕎ᵉ xᵉ αᵉ) (pairᵉ (tree-𝕎ᵉ .xᵉ βᵉ) (pairᵉ reflᵉ eᵉ)) =
    apᵉ
      ( ( aux-total-Eq-𝕎ᵉ xᵉ αᵉ) ∘ᵉ
        ( map-distributive-Π-Σᵉ
          { Aᵉ = Bᵉ xᵉ}
          { Bᵉ = λ yᵉ → 𝕎ᵉ Aᵉ Bᵉ}
          { Cᵉ = λ yᵉ → Eq-𝕎ᵉ (αᵉ yᵉ)}))
      { xᵉ = λ yᵉ → pairᵉ (αᵉ yᵉ) (refl-Eq-𝕎ᵉ (αᵉ yᵉ))}
      { yᵉ = λ yᵉ → pairᵉ (βᵉ yᵉ) (eᵉ yᵉ)}
      ( eq-htpyᵉ (λ yᵉ → contraction-total-Eq-𝕎ᵉ (αᵉ yᵉ) (pairᵉ (βᵉ yᵉ) (eᵉ yᵉ))))

  is-torsorial-Eq-𝕎ᵉ : (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → is-torsorialᵉ (Eq-𝕎ᵉ wᵉ)
  is-torsorial-Eq-𝕎ᵉ wᵉ =
    pairᵉ (center-total-Eq-𝕎ᵉ wᵉ) (contraction-total-Eq-𝕎ᵉ wᵉ)

  Eq-𝕎-eqᵉ : (vᵉ wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → vᵉ ＝ᵉ wᵉ → Eq-𝕎ᵉ vᵉ wᵉ
  Eq-𝕎-eqᵉ vᵉ .vᵉ reflᵉ = refl-Eq-𝕎ᵉ vᵉ

  is-equiv-Eq-𝕎-eqᵉ : (vᵉ wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → is-equivᵉ (Eq-𝕎-eqᵉ vᵉ wᵉ)
  is-equiv-Eq-𝕎-eqᵉ vᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-Eq-𝕎ᵉ vᵉ)
      ( Eq-𝕎-eqᵉ vᵉ)

  eq-Eq-𝕎ᵉ : (vᵉ wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → Eq-𝕎ᵉ vᵉ wᵉ → vᵉ ＝ᵉ wᵉ
  eq-Eq-𝕎ᵉ vᵉ wᵉ = map-inv-is-equivᵉ (is-equiv-Eq-𝕎-eqᵉ vᵉ wᵉ)

  equiv-Eq-𝕎-eqᵉ : (vᵉ wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → (vᵉ ＝ᵉ wᵉ) ≃ᵉ Eq-𝕎ᵉ vᵉ wᵉ
  equiv-Eq-𝕎-eqᵉ vᵉ wᵉ = pairᵉ (Eq-𝕎-eqᵉ vᵉ wᵉ) (is-equiv-Eq-𝕎-eqᵉ vᵉ wᵉ)

  is-trunc-𝕎ᵉ : (kᵉ : 𝕋ᵉ) → is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) (𝕎ᵉ Aᵉ Bᵉ)
  is-trunc-𝕎ᵉ kᵉ is-trunc-Aᵉ (tree-𝕎ᵉ xᵉ αᵉ) (tree-𝕎ᵉ yᵉ βᵉ) =
    is-trunc-is-equivᵉ kᵉ
      ( Eq-𝕎ᵉ (tree-𝕎ᵉ xᵉ αᵉ) (tree-𝕎ᵉ yᵉ βᵉ))
      ( Eq-𝕎-eqᵉ (tree-𝕎ᵉ xᵉ αᵉ) (tree-𝕎ᵉ yᵉ βᵉ))
      ( is-equiv-Eq-𝕎-eqᵉ (tree-𝕎ᵉ xᵉ αᵉ) (tree-𝕎ᵉ yᵉ βᵉ))
      ( is-trunc-Σᵉ
        ( is-trunc-Aᵉ xᵉ yᵉ)
        ( λ pᵉ → is-trunc-Πᵉ kᵉ
          ( λ zᵉ →
            is-trunc-is-equiv'ᵉ kᵉ
            ( αᵉ zᵉ ＝ᵉ βᵉ (trᵉ Bᵉ pᵉ zᵉ))
            ( Eq-𝕎-eqᵉ (αᵉ zᵉ) (βᵉ (trᵉ Bᵉ pᵉ zᵉ)))
            ( is-equiv-Eq-𝕎-eqᵉ (αᵉ zᵉ) (βᵉ (trᵉ Bᵉ pᵉ zᵉ)))
            ( is-trunc-𝕎ᵉ kᵉ is-trunc-Aᵉ (αᵉ zᵉ) (βᵉ (trᵉ Bᵉ pᵉ zᵉ))))))

  is-set-𝕎ᵉ : is-setᵉ Aᵉ → is-setᵉ (𝕎ᵉ Aᵉ Bᵉ)
  is-set-𝕎ᵉ = is-trunc-𝕎ᵉ neg-one-𝕋ᵉ
```

### The structure map of the algebra `𝕎 A B` is an equivalence

```agda
map-inv-structure-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  𝕎ᵉ Aᵉ Bᵉ → type-polynomial-endofunctorᵉ Aᵉ Bᵉ (𝕎ᵉ Aᵉ Bᵉ)
map-inv-structure-𝕎-Algᵉ (tree-𝕎ᵉ xᵉ αᵉ) = pairᵉ xᵉ αᵉ

is-section-map-inv-structure-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  (structure-𝕎-Algᵉ {Bᵉ = Bᵉ} ∘ᵉ map-inv-structure-𝕎-Algᵉ {Bᵉ = Bᵉ}) ~ᵉ idᵉ
is-section-map-inv-structure-𝕎-Algᵉ (tree-𝕎ᵉ xᵉ αᵉ) = reflᵉ

is-retraction-map-inv-structure-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  (map-inv-structure-𝕎-Algᵉ {Bᵉ = Bᵉ} ∘ᵉ structure-𝕎-Algᵉ {Bᵉ = Bᵉ}) ~ᵉ idᵉ
is-retraction-map-inv-structure-𝕎-Algᵉ (pairᵉ xᵉ αᵉ) = reflᵉ

is-equiv-structure-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  is-equivᵉ (structure-𝕎-Algᵉ {Bᵉ = Bᵉ})
is-equiv-structure-𝕎-Algᵉ =
  is-equiv-is-invertibleᵉ
    map-inv-structure-𝕎-Algᵉ
    is-section-map-inv-structure-𝕎-Algᵉ
    is-retraction-map-inv-structure-𝕎-Algᵉ

equiv-structure-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  type-polynomial-endofunctorᵉ Aᵉ Bᵉ (𝕎ᵉ Aᵉ Bᵉ) ≃ᵉ 𝕎ᵉ Aᵉ Bᵉ
equiv-structure-𝕎-Algᵉ =
  pairᵉ structure-𝕎-Algᵉ is-equiv-structure-𝕎-Algᵉ

is-equiv-map-inv-structure-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  is-equivᵉ (map-inv-structure-𝕎-Algᵉ {Bᵉ = Bᵉ})
is-equiv-map-inv-structure-𝕎-Algᵉ =
  is-equiv-is-invertibleᵉ
    structure-𝕎-Algᵉ
    is-retraction-map-inv-structure-𝕎-Algᵉ
    is-section-map-inv-structure-𝕎-Algᵉ

inv-equiv-structure-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  𝕎ᵉ Aᵉ Bᵉ ≃ᵉ type-polynomial-endofunctorᵉ Aᵉ Bᵉ (𝕎ᵉ Aᵉ Bᵉ)
inv-equiv-structure-𝕎-Algᵉ =
  pairᵉ map-inv-structure-𝕎-Algᵉ is-equiv-map-inv-structure-𝕎-Algᵉ
```

### W-types are initial algebras for polynomial endofunctors

```agda
map-hom-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : algebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ) →
  𝕎ᵉ Aᵉ Bᵉ → type-algebra-polynomial-endofunctorᵉ Xᵉ
map-hom-𝕎-Algᵉ Xᵉ (tree-𝕎ᵉ xᵉ αᵉ) =
  structure-algebra-polynomial-endofunctorᵉ Xᵉ
    ( pairᵉ xᵉ (λ yᵉ → map-hom-𝕎-Algᵉ Xᵉ (αᵉ yᵉ)))

structure-hom-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : algebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ) →
  ( (map-hom-𝕎-Algᵉ Xᵉ) ∘ᵉ structure-𝕎-Algᵉ) ~ᵉ
  ( ( structure-algebra-polynomial-endofunctorᵉ Xᵉ) ∘ᵉ
    ( map-polynomial-endofunctorᵉ Aᵉ Bᵉ (map-hom-𝕎-Algᵉ Xᵉ)))
structure-hom-𝕎-Algᵉ Xᵉ (pairᵉ xᵉ αᵉ) = reflᵉ

hom-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : algebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ) →
  hom-algebra-polynomial-endofunctorᵉ (𝕎-Algᵉ Aᵉ Bᵉ) Xᵉ
hom-𝕎-Algᵉ Xᵉ = pairᵉ (map-hom-𝕎-Algᵉ Xᵉ) (structure-hom-𝕎-Algᵉ Xᵉ)

htpy-htpy-hom-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : algebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ) →
  (fᵉ : hom-algebra-polynomial-endofunctorᵉ (𝕎-Algᵉ Aᵉ Bᵉ) Xᵉ) →
  map-hom-𝕎-Algᵉ Xᵉ ~ᵉ
  map-hom-algebra-polynomial-endofunctorᵉ (𝕎-Algᵉ Aᵉ Bᵉ) Xᵉ fᵉ
htpy-htpy-hom-𝕎-Algᵉ {Aᵉ = Aᵉ} {Bᵉ} Xᵉ fᵉ (tree-𝕎ᵉ xᵉ αᵉ) =
  ( apᵉ
    ( λ tᵉ → structure-algebra-polynomial-endofunctorᵉ Xᵉ (pairᵉ xᵉ tᵉ))
    ( eq-htpyᵉ (λ zᵉ → htpy-htpy-hom-𝕎-Algᵉ Xᵉ fᵉ (αᵉ zᵉ)))) ∙ᵉ
  ( invᵉ
    ( structure-hom-algebra-polynomial-endofunctorᵉ (𝕎-Algᵉ Aᵉ Bᵉ) Xᵉ fᵉ
      ( pairᵉ xᵉ αᵉ)))

compute-structure-htpy-hom-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : algebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ) (xᵉ : Aᵉ) (αᵉ : Bᵉ xᵉ → 𝕎ᵉ Aᵉ Bᵉ)
  {fᵉ : 𝕎ᵉ Aᵉ Bᵉ → type-algebra-polynomial-endofunctorᵉ Xᵉ} →
  (Hᵉ : map-hom-𝕎-Algᵉ Xᵉ ~ᵉ fᵉ) →
  ( apᵉ
    ( structure-algebra-polynomial-endofunctorᵉ Xᵉ)
    ( htpy-polynomial-endofunctorᵉ Aᵉ Bᵉ Hᵉ (pairᵉ xᵉ αᵉ))) ＝ᵉ
  ( apᵉ
    ( λ tᵉ → structure-algebra-polynomial-endofunctorᵉ Xᵉ (pairᵉ xᵉ tᵉ))
    ( htpy-postcompᵉ (Bᵉ xᵉ) Hᵉ αᵉ))
compute-structure-htpy-hom-𝕎-Algᵉ {Aᵉ = Aᵉ} {Bᵉ} Xᵉ xᵉ αᵉ =
  ind-htpyᵉ
    ( map-hom-𝕎-Algᵉ Xᵉ)
    ( λ fᵉ Hᵉ →
      ( apᵉ
        ( structure-algebra-polynomial-endofunctorᵉ Xᵉ)
        ( htpy-polynomial-endofunctorᵉ Aᵉ Bᵉ Hᵉ (pairᵉ xᵉ αᵉ))) ＝ᵉ
      ( apᵉ
        ( λ tᵉ → structure-algebra-polynomial-endofunctorᵉ Xᵉ (pairᵉ xᵉ tᵉ))
        ( htpy-postcompᵉ (Bᵉ xᵉ) Hᵉ αᵉ)))
    ( apᵉ
      ( apᵉ (pr2ᵉ Xᵉ))
      ( coh-refl-htpy-polynomial-endofunctorᵉ Aᵉ Bᵉ
        ( map-hom-𝕎-Algᵉ Xᵉ)
        ( pairᵉ xᵉ αᵉ)) ∙ᵉ
    ( invᵉ
      ( apᵉ
        ( apᵉ (λ tᵉ → pr2ᵉ Xᵉ (pairᵉ xᵉ tᵉ)))
        ( eq-htpy-refl-htpyᵉ (map-hom-𝕎-Algᵉ Xᵉ ∘ᵉ αᵉ)))))

structure-htpy-hom-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : algebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ) →
  (fᵉ : hom-algebra-polynomial-endofunctorᵉ (𝕎-Algᵉ Aᵉ Bᵉ) Xᵉ) →
  ( structure-hom-𝕎-Algᵉ Xᵉ ∙hᵉ
    ( ( structure-algebra-polynomial-endofunctorᵉ Xᵉ) ·lᵉ
      ( htpy-polynomial-endofunctorᵉ Aᵉ Bᵉ (htpy-htpy-hom-𝕎-Algᵉ Xᵉ fᵉ)))) ~ᵉ
  ( ( (htpy-htpy-hom-𝕎-Algᵉ Xᵉ fᵉ) ·rᵉ structure-𝕎-Algᵉ {Bᵉ = Bᵉ}) ∙hᵉ
    ( structure-hom-algebra-polynomial-endofunctorᵉ (𝕎-Algᵉ Aᵉ Bᵉ) Xᵉ fᵉ))
structure-htpy-hom-𝕎-Algᵉ {Aᵉ = Aᵉ} {Bᵉ} Xᵉ (pairᵉ fᵉ μ-fᵉ) (pairᵉ xᵉ αᵉ) =
  ( ( ( compute-structure-htpy-hom-𝕎-Algᵉ Xᵉ xᵉ αᵉ
        ( htpy-htpy-hom-𝕎-Algᵉ Xᵉ (pairᵉ fᵉ μ-fᵉ))) ∙ᵉ
      ( invᵉ right-unitᵉ)) ∙ᵉ
    ( apᵉ
      ( concatᵉ
        ( apᵉ
          ( λ tᵉ → pr2ᵉ Xᵉ (pairᵉ xᵉ tᵉ))
          ( eq-htpyᵉ (htpy-htpy-hom-𝕎-Algᵉ Xᵉ (pairᵉ fᵉ μ-fᵉ) ·rᵉ αᵉ)))
        ( pr2ᵉ Xᵉ (map-polynomial-endofunctorᵉ Aᵉ Bᵉ fᵉ (pairᵉ xᵉ αᵉ))))
      ( invᵉ (left-invᵉ ( μ-fᵉ (pairᵉ xᵉ αᵉ)))))) ∙ᵉ
  ( invᵉ
    ( assocᵉ
      ( apᵉ
        ( λ tᵉ → pr2ᵉ Xᵉ (pairᵉ xᵉ tᵉ))
        ( eq-htpyᵉ (htpy-htpy-hom-𝕎-Algᵉ Xᵉ (pairᵉ fᵉ μ-fᵉ) ·rᵉ αᵉ)))
      ( invᵉ (μ-fᵉ (pairᵉ xᵉ αᵉ)))
      ( μ-fᵉ (pairᵉ xᵉ αᵉ))))

htpy-hom-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : algebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ) →
  (fᵉ : hom-algebra-polynomial-endofunctorᵉ (𝕎-Algᵉ Aᵉ Bᵉ) Xᵉ) →
  htpy-hom-algebra-polynomial-endofunctorᵉ (𝕎-Algᵉ Aᵉ Bᵉ) Xᵉ (hom-𝕎-Algᵉ Xᵉ) fᵉ
htpy-hom-𝕎-Algᵉ Xᵉ fᵉ =
  pairᵉ (htpy-htpy-hom-𝕎-Algᵉ Xᵉ fᵉ) (structure-htpy-hom-𝕎-Algᵉ Xᵉ fᵉ)

is-initial-𝕎-Algᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : algebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ) →
  is-contrᵉ (hom-algebra-polynomial-endofunctorᵉ (𝕎-Algᵉ Aᵉ Bᵉ) Xᵉ)
is-initial-𝕎-Algᵉ {Aᵉ = Aᵉ} {Bᵉ} Xᵉ =
  pairᵉ
    ( hom-𝕎-Algᵉ Xᵉ)
    ( λ fᵉ →
      eq-htpy-hom-algebra-polynomial-endofunctorᵉ (𝕎-Algᵉ Aᵉ Bᵉ) Xᵉ (hom-𝕎-Algᵉ Xᵉ) fᵉ
        ( htpy-hom-𝕎-Algᵉ Xᵉ fᵉ))
```