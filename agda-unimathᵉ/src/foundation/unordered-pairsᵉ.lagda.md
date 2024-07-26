# Unordered pairs of elements in a type

```agda
module foundation.unordered-pairsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.type-arithmetic-dependent-function-typesᵉ
open import foundation.universal-property-contractible-typesᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.precomposition-dependent-functionsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.torsorial-type-familiesᵉ

open import univalent-combinatorics.2-element-typesᵉ
open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
open import univalent-combinatorics.universal-property-standard-finite-typesᵉ
```

</details>

## Idea

Anᵉ unorderedᵉ pairᵉ ofᵉ elementsᵉ in aᵉ typeᵉ `A`ᵉ consistsᵉ ofᵉ aᵉ 2-elementᵉ typeᵉ `X`ᵉ andᵉ
aᵉ mapᵉ `Xᵉ → A`.ᵉ

## Definition

### The definition of unordered pairs

```agda
unordered-pairᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → UUᵉ (lsuc lzero ⊔ lᵉ)
unordered-pairᵉ Aᵉ = Σᵉ (2-Element-Typeᵉ lzero) (λ Xᵉ → type-2-Element-Typeᵉ Xᵉ → Aᵉ)
```

### Immediate structure on the type of unordered pairs

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (pᵉ : unordered-pairᵉ Aᵉ)
  where

  2-element-type-unordered-pairᵉ : 2-Element-Typeᵉ lzero
  2-element-type-unordered-pairᵉ = pr1ᵉ pᵉ

  type-unordered-pairᵉ : UUᵉ lzero
  type-unordered-pairᵉ = type-2-Element-Typeᵉ 2-element-type-unordered-pairᵉ

  has-two-elements-type-unordered-pairᵉ : has-two-elementsᵉ type-unordered-pairᵉ
  has-two-elements-type-unordered-pairᵉ =
    has-two-elements-type-2-Element-Typeᵉ 2-element-type-unordered-pairᵉ

  is-set-type-unordered-pairᵉ : is-setᵉ type-unordered-pairᵉ
  is-set-type-unordered-pairᵉ =
    is-set-mere-equiv'ᵉ has-two-elements-type-unordered-pairᵉ (is-set-Finᵉ 2ᵉ)

  has-decidable-equality-type-unordered-pairᵉ :
    has-decidable-equalityᵉ type-unordered-pairᵉ
  has-decidable-equality-type-unordered-pairᵉ =
    has-decidable-equality-mere-equiv'ᵉ
      has-two-elements-type-unordered-pairᵉ
      ( has-decidable-equality-Finᵉ 2ᵉ)

  element-unordered-pairᵉ : type-unordered-pairᵉ → Aᵉ
  element-unordered-pairᵉ = pr2ᵉ pᵉ

  other-element-unordered-pairᵉ : type-unordered-pairᵉ → Aᵉ
  other-element-unordered-pairᵉ xᵉ =
    element-unordered-pairᵉ
      ( map-swap-2-Element-Typeᵉ 2-element-type-unordered-pairᵉ xᵉ)
```

### The predicate of being in an unodered pair

```agda
is-in-unordered-pair-Propᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (pᵉ : unordered-pairᵉ Aᵉ) (aᵉ : Aᵉ) → Propᵉ lᵉ
is-in-unordered-pair-Propᵉ pᵉ aᵉ =
  exists-structure-Propᵉ
    ( type-unordered-pairᵉ pᵉ)
    ( λ xᵉ → element-unordered-pairᵉ pᵉ xᵉ ＝ᵉ aᵉ)

is-in-unordered-pairᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (pᵉ : unordered-pairᵉ Aᵉ) (aᵉ : Aᵉ) → UUᵉ lᵉ
is-in-unordered-pairᵉ pᵉ aᵉ = type-Propᵉ (is-in-unordered-pair-Propᵉ pᵉ aᵉ)

is-prop-is-in-unordered-pairᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (pᵉ : unordered-pairᵉ Aᵉ) (aᵉ : Aᵉ) →
  is-propᵉ (is-in-unordered-pairᵉ pᵉ aᵉ)
is-prop-is-in-unordered-pairᵉ pᵉ aᵉ =
  is-prop-type-Propᵉ (is-in-unordered-pair-Propᵉ pᵉ aᵉ)
```

### The condition of being a self-pairing

```agda
is-selfpairing-unordered-pairᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (pᵉ : unordered-pairᵉ Aᵉ) → UUᵉ lᵉ
is-selfpairing-unordered-pairᵉ pᵉ =
  (xᵉ yᵉ : type-unordered-pairᵉ pᵉ) →
  type-trunc-Propᵉ (element-unordered-pairᵉ pᵉ xᵉ ＝ᵉ element-unordered-pairᵉ pᵉ yᵉ)
```

### Standard unordered pairs

Anyᵉ twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ in aᵉ typeᵉ `A`ᵉ defineᵉ aᵉ standardᵉ unorderedᵉ pairᵉ

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ : Aᵉ)
  where

  element-standard-unordered-pairᵉ : Finᵉ 2 → Aᵉ
  element-standard-unordered-pairᵉ =
    map-inv-ev-zero-one-Fin-two-ℕᵉ (λ _ → Aᵉ) (xᵉ ,ᵉ yᵉ)

  standard-unordered-pairᵉ : unordered-pairᵉ Aᵉ
  pr1ᵉ standard-unordered-pairᵉ = Fin-UU-Fin'ᵉ 2
  pr2ᵉ standard-unordered-pairᵉ = element-standard-unordered-pairᵉ

  other-element-standard-unordered-pairᵉ : Finᵉ 2 → Aᵉ
  other-element-standard-unordered-pairᵉ (inlᵉ (inrᵉ _)) = yᵉ
  other-element-standard-unordered-pairᵉ (inrᵉ _) = xᵉ

  compute-other-element-standard-unordered-pairᵉ :
    (uᵉ : Finᵉ 2ᵉ) →
    other-element-unordered-pairᵉ standard-unordered-pairᵉ uᵉ ＝ᵉ
    other-element-standard-unordered-pairᵉ uᵉ
  compute-other-element-standard-unordered-pairᵉ (inlᵉ (inrᵉ xᵉ)) =
    apᵉ element-standard-unordered-pairᵉ (compute-swap-Fin-two-ℕᵉ (inlᵉ (inrᵉ xᵉ)))
  compute-other-element-standard-unordered-pairᵉ (inrᵉ xᵉ) =
    apᵉ element-standard-unordered-pairᵉ (compute-swap-Fin-two-ℕᵉ (inrᵉ xᵉ))
```

## Properties

### Extensionality of unordered pairs

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  Eq-unordered-pairᵉ : (pᵉ qᵉ : unordered-pairᵉ Aᵉ) → UUᵉ l1ᵉ
  Eq-unordered-pairᵉ pᵉ qᵉ =
    Σᵉ ( type-unordered-pairᵉ pᵉ ≃ᵉ type-unordered-pairᵉ qᵉ)
      ( λ eᵉ →
        coherence-triangle-mapsᵉ
          ( element-unordered-pairᵉ pᵉ)
          ( element-unordered-pairᵉ qᵉ)
          ( map-equivᵉ eᵉ))

  refl-Eq-unordered-pairᵉ : (pᵉ : unordered-pairᵉ Aᵉ) → Eq-unordered-pairᵉ pᵉ pᵉ
  pr1ᵉ (refl-Eq-unordered-pairᵉ (pairᵉ Xᵉ pᵉ)) = id-equiv-UU-Finᵉ {kᵉ = 2ᵉ} Xᵉ
  pr2ᵉ (refl-Eq-unordered-pairᵉ (pairᵉ Xᵉ pᵉ)) = refl-htpyᵉ

  Eq-eq-unordered-pairᵉ :
    (pᵉ qᵉ : unordered-pairᵉ Aᵉ) → pᵉ ＝ᵉ qᵉ → Eq-unordered-pairᵉ pᵉ qᵉ
  Eq-eq-unordered-pairᵉ pᵉ .pᵉ reflᵉ = refl-Eq-unordered-pairᵉ pᵉ

  is-torsorial-Eq-unordered-pairᵉ :
    (pᵉ : unordered-pairᵉ Aᵉ) →
    is-torsorialᵉ (Eq-unordered-pairᵉ pᵉ)
  is-torsorial-Eq-unordered-pairᵉ (pairᵉ Xᵉ pᵉ) =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equiv-UU-Finᵉ {kᵉ = 2ᵉ} Xᵉ)
      ( pairᵉ Xᵉ (id-equiv-UU-Finᵉ {kᵉ = 2ᵉ} Xᵉ))
      ( is-torsorial-htpyᵉ pᵉ)

  is-equiv-Eq-eq-unordered-pairᵉ :
    (pᵉ qᵉ : unordered-pairᵉ Aᵉ) → is-equivᵉ (Eq-eq-unordered-pairᵉ pᵉ qᵉ)
  is-equiv-Eq-eq-unordered-pairᵉ pᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-Eq-unordered-pairᵉ pᵉ)
      ( Eq-eq-unordered-pairᵉ pᵉ)

  extensionality-unordered-pairᵉ :
    (pᵉ qᵉ : unordered-pairᵉ Aᵉ) → (pᵉ ＝ᵉ qᵉ) ≃ᵉ Eq-unordered-pairᵉ pᵉ qᵉ
  pr1ᵉ (extensionality-unordered-pairᵉ pᵉ qᵉ) = Eq-eq-unordered-pairᵉ pᵉ qᵉ
  pr2ᵉ (extensionality-unordered-pairᵉ pᵉ qᵉ) = is-equiv-Eq-eq-unordered-pairᵉ pᵉ qᵉ

  eq-Eq-unordered-pair'ᵉ :
    (pᵉ qᵉ : unordered-pairᵉ Aᵉ) → Eq-unordered-pairᵉ pᵉ qᵉ → pᵉ ＝ᵉ qᵉ
  eq-Eq-unordered-pair'ᵉ pᵉ qᵉ =
    map-inv-is-equivᵉ (is-equiv-Eq-eq-unordered-pairᵉ pᵉ qᵉ)

  eq-Eq-unordered-pairᵉ :
    (pᵉ qᵉ : unordered-pairᵉ Aᵉ)
    (eᵉ : type-unordered-pairᵉ pᵉ ≃ᵉ type-unordered-pairᵉ qᵉ) →
    (element-unordered-pairᵉ pᵉ ~ᵉ (element-unordered-pairᵉ qᵉ ∘ᵉ map-equivᵉ eᵉ)) →
    (pᵉ ＝ᵉ qᵉ)
  eq-Eq-unordered-pairᵉ pᵉ qᵉ eᵉ Hᵉ = eq-Eq-unordered-pair'ᵉ pᵉ qᵉ (pairᵉ eᵉ Hᵉ)

  is-retraction-eq-Eq-unordered-pairᵉ :
    (pᵉ qᵉ : unordered-pairᵉ Aᵉ) →
    (eq-Eq-unordered-pair'ᵉ pᵉ qᵉ ∘ᵉ Eq-eq-unordered-pairᵉ pᵉ qᵉ) ~ᵉ idᵉ
  is-retraction-eq-Eq-unordered-pairᵉ pᵉ qᵉ =
    is-retraction-map-inv-is-equivᵉ (is-equiv-Eq-eq-unordered-pairᵉ pᵉ qᵉ)

  is-section-eq-Eq-unordered-pairᵉ :
    (pᵉ qᵉ : unordered-pairᵉ Aᵉ) →
    ( Eq-eq-unordered-pairᵉ pᵉ qᵉ ∘ᵉ eq-Eq-unordered-pair'ᵉ pᵉ qᵉ) ~ᵉ idᵉ
  is-section-eq-Eq-unordered-pairᵉ pᵉ qᵉ =
    is-section-map-inv-is-equivᵉ (is-equiv-Eq-eq-unordered-pairᵉ pᵉ qᵉ)

  eq-Eq-refl-unordered-pairᵉ :
    (pᵉ : unordered-pairᵉ Aᵉ) → eq-Eq-unordered-pairᵉ pᵉ pᵉ id-equivᵉ refl-htpyᵉ ＝ᵉ reflᵉ
  eq-Eq-refl-unordered-pairᵉ pᵉ = is-retraction-eq-Eq-unordered-pairᵉ pᵉ pᵉ reflᵉ
```

### Induction on equality of unordered pairs

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (pᵉ : unordered-pairᵉ Aᵉ)
  (Bᵉ : (qᵉ : unordered-pairᵉ Aᵉ) → Eq-unordered-pairᵉ pᵉ qᵉ → UUᵉ l2ᵉ)
  where

  ev-refl-Eq-unordered-pairᵉ :
    ((qᵉ : unordered-pairᵉ Aᵉ) (eᵉ : Eq-unordered-pairᵉ pᵉ qᵉ) → Bᵉ qᵉ eᵉ) →
    Bᵉ pᵉ (refl-Eq-unordered-pairᵉ pᵉ)
  ev-refl-Eq-unordered-pairᵉ fᵉ = fᵉ pᵉ (refl-Eq-unordered-pairᵉ pᵉ)

  triangle-ev-refl-Eq-unordered-pairᵉ :
    coherence-triangle-mapsᵉ
      ( ev-pointᵉ (pᵉ ,ᵉ refl-Eq-unordered-pairᵉ pᵉ))
      ( ev-refl-Eq-unordered-pairᵉ)
      ( ev-pairᵉ)
  triangle-ev-refl-Eq-unordered-pairᵉ = refl-htpyᵉ

  abstract
    is-equiv-ev-refl-Eq-unordered-pairᵉ : is-equivᵉ ev-refl-Eq-unordered-pairᵉ
    is-equiv-ev-refl-Eq-unordered-pairᵉ =
      is-equiv-right-map-triangleᵉ
        ( ev-pointᵉ (pᵉ ,ᵉ refl-Eq-unordered-pairᵉ pᵉ))
        ( ev-refl-Eq-unordered-pairᵉ)
        ( ev-pairᵉ)
        ( triangle-ev-refl-Eq-unordered-pairᵉ)
        ( dependent-universal-property-contr-is-contrᵉ
          ( pᵉ ,ᵉ refl-Eq-unordered-pairᵉ pᵉ)
          ( is-torsorial-Eq-unordered-pairᵉ pᵉ)
          ( λ uᵉ → Bᵉ (pr1ᵉ uᵉ) (pr2ᵉ uᵉ)))
        ( is-equiv-ev-pairᵉ)

  abstract
    is-contr-map-ev-refl-Eq-unordered-pairᵉ :
      is-contr-mapᵉ ev-refl-Eq-unordered-pairᵉ
    is-contr-map-ev-refl-Eq-unordered-pairᵉ =
      is-contr-map-is-equivᵉ is-equiv-ev-refl-Eq-unordered-pairᵉ

  abstract
    ind-Eq-unordered-pairᵉ :
      Bᵉ pᵉ (refl-Eq-unordered-pairᵉ pᵉ) →
      ((qᵉ : unordered-pairᵉ Aᵉ) (eᵉ : Eq-unordered-pairᵉ pᵉ qᵉ) → Bᵉ qᵉ eᵉ)
    ind-Eq-unordered-pairᵉ uᵉ =
      pr1ᵉ (centerᵉ (is-contr-map-ev-refl-Eq-unordered-pairᵉ uᵉ))

    compute-refl-ind-Eq-unordered-pairᵉ :
      (uᵉ : Bᵉ pᵉ (refl-Eq-unordered-pairᵉ pᵉ)) →
      ind-Eq-unordered-pairᵉ uᵉ pᵉ (refl-Eq-unordered-pairᵉ pᵉ) ＝ᵉ uᵉ
    compute-refl-ind-Eq-unordered-pairᵉ uᵉ =
      pr2ᵉ (centerᵉ (is-contr-map-ev-refl-Eq-unordered-pairᵉ uᵉ))
```

### Inverting extensional equality of unordered pairs

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (pᵉ qᵉ : unordered-pairᵉ Aᵉ)
  where

  inv-Eq-unordered-pairᵉ :
    Eq-unordered-pairᵉ pᵉ qᵉ → Eq-unordered-pairᵉ qᵉ pᵉ
  pr1ᵉ (inv-Eq-unordered-pairᵉ (eᵉ ,ᵉ Hᵉ)) = inv-equivᵉ eᵉ
  pr2ᵉ (inv-Eq-unordered-pairᵉ (eᵉ ,ᵉ Hᵉ)) =
    coherence-triangle-maps-inv-topᵉ
      ( element-unordered-pairᵉ pᵉ)
      ( element-unordered-pairᵉ qᵉ)
      ( eᵉ)
      ( Hᵉ)
```

### Mere equality of unordered pairs

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  mere-Eq-unordered-pair-Propᵉ : (pᵉ qᵉ : unordered-pairᵉ Aᵉ) → Propᵉ l1ᵉ
  mere-Eq-unordered-pair-Propᵉ pᵉ qᵉ = trunc-Propᵉ (Eq-unordered-pairᵉ pᵉ qᵉ)

  mere-Eq-unordered-pairᵉ : (pᵉ qᵉ : unordered-pairᵉ Aᵉ) → UUᵉ l1ᵉ
  mere-Eq-unordered-pairᵉ pᵉ qᵉ = type-Propᵉ (mere-Eq-unordered-pair-Propᵉ pᵉ qᵉ)

  is-prop-mere-Eq-unordered-pairᵉ :
    (pᵉ qᵉ : unordered-pairᵉ Aᵉ) → is-propᵉ (mere-Eq-unordered-pairᵉ pᵉ qᵉ)
  is-prop-mere-Eq-unordered-pairᵉ pᵉ qᵉ =
    is-prop-type-Propᵉ (mere-Eq-unordered-pair-Propᵉ pᵉ qᵉ)

  refl-mere-Eq-unordered-pairᵉ :
    (pᵉ : unordered-pairᵉ Aᵉ) → mere-Eq-unordered-pairᵉ pᵉ pᵉ
  refl-mere-Eq-unordered-pairᵉ pᵉ =
    unit-trunc-Propᵉ (refl-Eq-unordered-pairᵉ pᵉ)
```

### A standard unordered pair `{x,y}` is equal to the standard unordered pair `{y,x}`

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ : Aᵉ)
  where

  swap-standard-unordered-pairᵉ :
    Eq-unordered-pairᵉ
      ( standard-unordered-pairᵉ xᵉ yᵉ)
      ( standard-unordered-pairᵉ yᵉ xᵉ)
  pr1ᵉ swap-standard-unordered-pairᵉ = equiv-succ-Finᵉ 2
  pr2ᵉ swap-standard-unordered-pairᵉ (inlᵉ (inrᵉ _)) = reflᵉ
  pr2ᵉ swap-standard-unordered-pairᵉ (inrᵉ _) = reflᵉ

  is-commutative-standard-unordered-pairᵉ :
    standard-unordered-pairᵉ xᵉ yᵉ ＝ᵉ standard-unordered-pairᵉ yᵉ xᵉ
  is-commutative-standard-unordered-pairᵉ =
    eq-Eq-unordered-pair'ᵉ
      ( standard-unordered-pairᵉ xᵉ yᵉ)
      ( standard-unordered-pairᵉ yᵉ xᵉ)
      ( swap-standard-unordered-pairᵉ)
```

### Dependent universal property of pointed unordered pairs

Weᵉ willᵉ constructᵉ anᵉ equivalenceᵉ

```text
  ((pᵉ : unordered-pairᵉ Aᵉ) (iᵉ : typeᵉ pᵉ) → Bᵉ pᵉ iᵉ) ≃ᵉ ((xᵉ yᵉ : Aᵉ) → Bᵉ {x,yᵉ} 0ᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Bᵉ : (pᵉ : unordered-pairᵉ Aᵉ) → type-unordered-pairᵉ pᵉ → UUᵉ l2ᵉ)
  where

  ev-pointed-unordered-pairᵉ :
    ((pᵉ : unordered-pairᵉ Aᵉ) (iᵉ : type-unordered-pairᵉ pᵉ) → Bᵉ pᵉ iᵉ) →
    ((xᵉ yᵉ : Aᵉ) → Bᵉ (standard-unordered-pairᵉ xᵉ yᵉ) (zero-Finᵉ 1ᵉ))
  ev-pointed-unordered-pairᵉ fᵉ xᵉ yᵉ =
    fᵉ (standard-unordered-pairᵉ xᵉ yᵉ) (zero-Finᵉ 1ᵉ)

  abstract
    dependent-universal-property-pointed-unordered-pairsᵉ :
      is-equivᵉ ev-pointed-unordered-pairᵉ
    dependent-universal-property-pointed-unordered-pairsᵉ =
      is-equiv-compᵉ
        ( λ fᵉ xᵉ yᵉ →
          fᵉ (Fin-UU-Fin'ᵉ 2ᵉ) (element-standard-unordered-pairᵉ xᵉ yᵉ) (zero-Finᵉ 1ᵉ))
        ( ev-pairᵉ)
        ( is-equiv-ev-pairᵉ)
        ( is-equiv-compᵉ
          ( λ fᵉ xᵉ yᵉ →
            fᵉ ( Fin-UU-Fin'ᵉ 2ᵉ)
              ( zero-Finᵉ 1ᵉ)
              ( element-standard-unordered-pairᵉ xᵉ yᵉ))
          ( map-Πᵉ (λ Iᵉ → swap-Πᵉ))
          ( is-equiv-map-Π-is-fiberwise-equivᵉ
            ( λ Iᵉ → is-equiv-swap-Πᵉ))
          ( is-equiv-compᵉ
            ( λ fᵉ xᵉ yᵉ → fᵉ (element-standard-unordered-pairᵉ xᵉ yᵉ))
            ( λ fᵉ → fᵉ (Fin-UU-Fin'ᵉ 2ᵉ) (zero-Finᵉ 1ᵉ))
            ( dependent-universal-property-identity-system-type-2-Element-Typeᵉ
              ( Fin-UU-Fin'ᵉ 2ᵉ)
              ( zero-Finᵉ 1ᵉ)
              ( λ Iᵉ iᵉ → (aᵉ : type-2-Element-Typeᵉ Iᵉ → Aᵉ) → Bᵉ (Iᵉ ,ᵉ aᵉ) iᵉ))
            ( is-equiv-compᵉ
              ( ev-pairᵉ)
              ( precomp-Πᵉ
                ( λ xyᵉ → element-standard-unordered-pairᵉ (pr1ᵉ xyᵉ) (pr2ᵉ xyᵉ))
                ( λ gᵉ → Bᵉ (Fin-UU-Fin'ᵉ 2 ,ᵉ gᵉ) (zero-Finᵉ 1ᵉ)))
              ( is-equiv-precomp-Π-is-equivᵉ
                ( is-equiv-map-inv-dependent-universal-proeprty-Fin-two-ℕᵉ
                  ( λ _ → Aᵉ))
                ( λ gᵉ → Bᵉ (Fin-UU-Fin'ᵉ 2 ,ᵉ gᵉ) (zero-Finᵉ 1ᵉ)))
              ( is-equiv-ev-pairᵉ))))

  equiv-dependent-universal-property-pointed-unordered-pairsᵉ :
    ((pᵉ : unordered-pairᵉ Aᵉ) (iᵉ : type-unordered-pairᵉ pᵉ) → Bᵉ pᵉ iᵉ) ≃ᵉ
    ((xᵉ yᵉ : Aᵉ) → Bᵉ (standard-unordered-pairᵉ xᵉ yᵉ) (zero-Finᵉ 1ᵉ))
  pr1ᵉ equiv-dependent-universal-property-pointed-unordered-pairsᵉ =
    ev-pointed-unordered-pairᵉ
  pr2ᵉ equiv-dependent-universal-property-pointed-unordered-pairsᵉ =
    dependent-universal-property-pointed-unordered-pairsᵉ
```

### Functoriality of unordered pairs

```agda
map-unordered-pairᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  unordered-pairᵉ Aᵉ → unordered-pairᵉ Bᵉ
pr1ᵉ (map-unordered-pairᵉ fᵉ pᵉ) = 2-element-type-unordered-pairᵉ pᵉ
pr2ᵉ (map-unordered-pairᵉ fᵉ pᵉ) = fᵉ ∘ᵉ element-unordered-pairᵉ pᵉ

preserves-comp-map-unordered-pairᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ) →
  map-unordered-pairᵉ (gᵉ ∘ᵉ fᵉ) ~ᵉ (map-unordered-pairᵉ gᵉ ∘ᵉ map-unordered-pairᵉ fᵉ)
preserves-comp-map-unordered-pairᵉ gᵉ fᵉ pᵉ = reflᵉ

preserves-id-map-unordered-pairᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  map-unordered-pairᵉ (idᵉ {Aᵉ = Aᵉ}) ~ᵉ idᵉ
preserves-id-map-unordered-pairᵉ = refl-htpyᵉ

htpy-unordered-pairᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ gᵉ : Aᵉ → Bᵉ} →
  (fᵉ ~ᵉ gᵉ) → (map-unordered-pairᵉ fᵉ ~ᵉ map-unordered-pairᵉ gᵉ)
htpy-unordered-pairᵉ {fᵉ = fᵉ} {gᵉ = gᵉ} Hᵉ (pairᵉ Xᵉ pᵉ) =
  eq-Eq-unordered-pairᵉ
    ( map-unordered-pairᵉ fᵉ (pairᵉ Xᵉ pᵉ))
    ( map-unordered-pairᵉ gᵉ (pairᵉ Xᵉ pᵉ))
    ( id-equivᵉ)
    ( Hᵉ ·rᵉ pᵉ)

preserves-refl-htpy-unordered-pairᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  htpy-unordered-pairᵉ (refl-htpyᵉ {fᵉ = fᵉ}) ~ᵉ refl-htpyᵉ
preserves-refl-htpy-unordered-pairᵉ fᵉ pᵉ =
  is-retraction-eq-Eq-unordered-pairᵉ
    ( map-unordered-pairᵉ fᵉ pᵉ)
    ( map-unordered-pairᵉ fᵉ pᵉ)
    ( reflᵉ)

equiv-unordered-pairᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (Aᵉ ≃ᵉ Bᵉ) → (unordered-pairᵉ Aᵉ ≃ᵉ unordered-pairᵉ Bᵉ)
equiv-unordered-pairᵉ eᵉ = equiv-totᵉ (λ Xᵉ → equiv-postcompᵉ (type-UU-Finᵉ 2 Xᵉ) eᵉ)

map-equiv-unordered-pairᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (Aᵉ ≃ᵉ Bᵉ) → (unordered-pairᵉ Aᵉ → unordered-pairᵉ Bᵉ)
map-equiv-unordered-pairᵉ eᵉ = map-equivᵉ (equiv-unordered-pairᵉ eᵉ)

is-equiv-map-equiv-unordered-pairᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (eᵉ : Aᵉ ≃ᵉ Bᵉ) → is-equivᵉ (map-equiv-unordered-pairᵉ eᵉ)
is-equiv-map-equiv-unordered-pairᵉ eᵉ =
  is-equiv-map-equivᵉ (equiv-unordered-pairᵉ eᵉ)

element-equiv-standard-unordered-pairᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) (xᵉ yᵉ : Aᵉ) →
  ( map-equivᵉ eᵉ ∘ᵉ element-standard-unordered-pairᵉ xᵉ yᵉ) ~ᵉ
  ( element-standard-unordered-pairᵉ (map-equivᵉ eᵉ xᵉ) (map-equivᵉ eᵉ yᵉ))
element-equiv-standard-unordered-pairᵉ eᵉ xᵉ yᵉ (inlᵉ (inrᵉ _)) = reflᵉ
element-equiv-standard-unordered-pairᵉ eᵉ xᵉ yᵉ (inrᵉ _) = reflᵉ

equiv-standard-unordered-pairᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) (xᵉ yᵉ : Aᵉ) →
  map-equiv-unordered-pairᵉ eᵉ (standard-unordered-pairᵉ xᵉ yᵉ) ＝ᵉ
  standard-unordered-pairᵉ (map-equivᵉ eᵉ xᵉ) (map-equivᵉ eᵉ yᵉ)
equiv-standard-unordered-pairᵉ eᵉ xᵉ yᵉ =
  eq-Eq-unordered-pairᵉ
    ( map-equiv-unordered-pairᵉ eᵉ (standard-unordered-pairᵉ xᵉ yᵉ))
    ( standard-unordered-pairᵉ (map-equivᵉ eᵉ xᵉ) (map-equivᵉ eᵉ yᵉ))
    ( id-equivᵉ)
    ( element-equiv-standard-unordered-pairᵉ eᵉ xᵉ yᵉ)

id-equiv-unordered-pairᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → map-equiv-unordered-pairᵉ (id-equivᵉ {Aᵉ = Aᵉ}) ~ᵉ idᵉ
id-equiv-unordered-pairᵉ = refl-htpyᵉ

element-id-equiv-standard-unordered-pairᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (xᵉ yᵉ : Aᵉ) →
  element-equiv-standard-unordered-pairᵉ (id-equivᵉ {Aᵉ = Aᵉ}) xᵉ yᵉ ~ᵉ refl-htpyᵉ
element-id-equiv-standard-unordered-pairᵉ xᵉ yᵉ (inlᵉ (inrᵉ _)) = reflᵉ
element-id-equiv-standard-unordered-pairᵉ xᵉ yᵉ (inrᵉ _) = reflᵉ

id-equiv-standard-unordered-pairᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (xᵉ yᵉ : Aᵉ) →
  equiv-standard-unordered-pairᵉ id-equivᵉ xᵉ yᵉ ＝ᵉ reflᵉ
id-equiv-standard-unordered-pairᵉ xᵉ yᵉ =
  ( apᵉ
    ( eq-Eq-unordered-pairᵉ
      ( standard-unordered-pairᵉ xᵉ yᵉ)
      ( standard-unordered-pairᵉ xᵉ yᵉ)
      ( id-equivᵉ))
    ( eq-htpyᵉ (element-id-equiv-standard-unordered-pairᵉ xᵉ yᵉ))) ∙ᵉ
  ( eq-Eq-refl-unordered-pairᵉ (standard-unordered-pairᵉ xᵉ yᵉ))

unordered-distinct-pairᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → UUᵉ (lsuc lzero ⊔ lᵉ)
unordered-distinct-pairᵉ Aᵉ =
  Σᵉ (UU-Finᵉ lzero 2ᵉ) (λ Xᵉ → pr1ᵉ Xᵉ ↪ᵉ Aᵉ)
```

### Every unordered pair is merely equal to a standard unordered pair

```agda
abstract
  is-surjective-standard-unordered-pairᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (pᵉ : unordered-pairᵉ Aᵉ) →
    type-trunc-Propᵉ
      ( Σᵉ Aᵉ (λ xᵉ → Σᵉ Aᵉ (λ yᵉ → standard-unordered-pairᵉ xᵉ yᵉ ＝ᵉ pᵉ)))
  is-surjective-standard-unordered-pairᵉ (Iᵉ ,ᵉ aᵉ) =
    apply-universal-property-trunc-Propᵉ
      ( has-two-elements-type-2-Element-Typeᵉ Iᵉ)
      ( trunc-Propᵉ
        ( Σᵉ _ (λ xᵉ → Σᵉ _ (λ yᵉ → standard-unordered-pairᵉ xᵉ yᵉ ＝ᵉ (Iᵉ ,ᵉ aᵉ)))))
      ( λ eᵉ →
        unit-trunc-Propᵉ
          ( aᵉ (map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ)) ,ᵉ
            aᵉ (map-equivᵉ eᵉ (one-Finᵉ 1ᵉ)) ,ᵉ
            eq-Eq-unordered-pairᵉ
              ( standard-unordered-pairᵉ _ _)
              ( Iᵉ ,ᵉ aᵉ)
              ( eᵉ)
              ( λ where
                ( inlᵉ (inrᵉ _)) → reflᵉ
                ( inrᵉ _) → reflᵉ)))
```

### For every unordered pair `p` and every element `i` in its underlying type, `p` is equal to a standard unordered pair

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (pᵉ : unordered-pairᵉ Aᵉ) (iᵉ : type-unordered-pairᵉ pᵉ)
  where

  compute-standard-unordered-pair-element-unordered-pairᵉ :
    Eq-unordered-pairᵉ
      ( standard-unordered-pairᵉ
        ( element-unordered-pairᵉ pᵉ iᵉ)
        ( other-element-unordered-pairᵉ pᵉ iᵉ))
      ( pᵉ)
  pr1ᵉ compute-standard-unordered-pair-element-unordered-pairᵉ =
    equiv-point-2-Element-Typeᵉ
      ( 2-element-type-unordered-pairᵉ pᵉ)
      ( iᵉ)
  pr2ᵉ compute-standard-unordered-pair-element-unordered-pairᵉ (inlᵉ (inrᵉ _)) =
    apᵉ
      ( element-unordered-pairᵉ pᵉ)
      ( invᵉ
        ( compute-map-equiv-point-2-Element-Typeᵉ
          ( 2-element-type-unordered-pairᵉ pᵉ)
          ( iᵉ)))
  pr2ᵉ compute-standard-unordered-pair-element-unordered-pairᵉ (inrᵉ _) =
    apᵉ
      ( element-unordered-pairᵉ pᵉ)
      ( invᵉ
        ( compute-map-equiv-point-2-Element-Type'ᵉ
          ( 2-element-type-unordered-pairᵉ pᵉ)
          ( iᵉ)))

  eq-compute-standard-unordered-pair-element-unordered-pairᵉ :
    standard-unordered-pairᵉ
      ( element-unordered-pairᵉ pᵉ iᵉ)
      ( other-element-unordered-pairᵉ pᵉ iᵉ) ＝ᵉ pᵉ
  eq-compute-standard-unordered-pair-element-unordered-pairᵉ =
    eq-Eq-unordered-pair'ᵉ
      ( standard-unordered-pairᵉ
        ( element-unordered-pairᵉ pᵉ iᵉ)
        ( other-element-unordered-pairᵉ pᵉ iᵉ))
      ( pᵉ)
      ( compute-standard-unordered-pair-element-unordered-pairᵉ)
```