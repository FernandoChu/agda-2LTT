# Equivalences of spans

```agda
module foundation.equivalences-spansᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.morphisms-spansᵉ
open import foundation.spansᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.operations-spansᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "equivalenceᵉ ofᵉ spans"ᵉ Agda=equiv-spanᵉ}} fromᵉ aᵉ
[span](foundation.spans.mdᵉ) `Aᵉ <-f-ᵉ Sᵉ -g->ᵉ B`ᵉ to aᵉ spanᵉ `Aᵉ <-h-ᵉ Tᵉ -k->ᵉ B`ᵉ
consistsᵉ ofᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) `wᵉ : Sᵉ ≃ᵉ T`ᵉ
[equipped](foundation.structure.mdᵉ) with twoᵉ
[homotopies](foundation-core.homotopies.mdᵉ) witnessingᵉ thatᵉ theᵉ diagramᵉ

```text
             Sᵉ
           /ᵉ | \ᵉ
        fᵉ /ᵉ  |  \ᵉ hᵉ
         ∨ᵉ   |   ∨ᵉ
        Aᵉ    |wᵉ   Bᵉ
         ∧ᵉ   |   ∧ᵉ
        hᵉ \ᵉ  |  /ᵉ kᵉ
           \ᵉ ∨ᵉ /ᵉ
             Tᵉ
```

[commutes](foundation.commuting-triangles-of-maps.md).ᵉ

## Definitions

### The predicate of being an equivalence of spans

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (sᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ) (tᵉ : spanᵉ l4ᵉ Aᵉ Bᵉ)
  where

  is-equiv-hom-spanᵉ : hom-spanᵉ sᵉ tᵉ → UUᵉ (l3ᵉ ⊔ l4ᵉ)
  is-equiv-hom-spanᵉ fᵉ = is-equivᵉ (map-hom-spanᵉ sᵉ tᵉ fᵉ)
```

### Equivalences of spans

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (sᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ) (tᵉ : spanᵉ l4ᵉ Aᵉ Bᵉ)
  where

  left-coherence-equiv-spanᵉ :
    (spanning-type-spanᵉ sᵉ ≃ᵉ spanning-type-spanᵉ tᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  left-coherence-equiv-spanᵉ eᵉ =
    left-coherence-hom-spanᵉ sᵉ tᵉ (map-equivᵉ eᵉ)

  right-coherence-equiv-spanᵉ :
    (spanning-type-spanᵉ sᵉ ≃ᵉ spanning-type-spanᵉ tᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  right-coherence-equiv-spanᵉ eᵉ =
    right-coherence-hom-spanᵉ sᵉ tᵉ (map-equivᵉ eᵉ)

  coherence-equiv-spanᵉ :
    (spanning-type-spanᵉ sᵉ ≃ᵉ spanning-type-spanᵉ tᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  coherence-equiv-spanᵉ eᵉ = coherence-hom-spanᵉ sᵉ tᵉ (map-equivᵉ eᵉ)

  equiv-spanᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  equiv-spanᵉ =
    Σᵉ ( spanning-type-spanᵉ sᵉ ≃ᵉ spanning-type-spanᵉ tᵉ) coherence-equiv-spanᵉ

  equiv-equiv-spanᵉ : equiv-spanᵉ → spanning-type-spanᵉ sᵉ ≃ᵉ spanning-type-spanᵉ tᵉ
  equiv-equiv-spanᵉ = pr1ᵉ

  map-equiv-spanᵉ : equiv-spanᵉ → spanning-type-spanᵉ sᵉ → spanning-type-spanᵉ tᵉ
  map-equiv-spanᵉ eᵉ = map-equivᵉ (equiv-equiv-spanᵉ eᵉ)

  left-triangle-equiv-spanᵉ :
    (eᵉ : equiv-spanᵉ) → left-coherence-hom-spanᵉ sᵉ tᵉ (map-equiv-spanᵉ eᵉ)
  left-triangle-equiv-spanᵉ eᵉ = pr1ᵉ (pr2ᵉ eᵉ)

  right-triangle-equiv-spanᵉ :
    (eᵉ : equiv-spanᵉ) → right-coherence-hom-spanᵉ sᵉ tᵉ (map-equiv-spanᵉ eᵉ)
  right-triangle-equiv-spanᵉ eᵉ = pr2ᵉ (pr2ᵉ eᵉ)

  hom-equiv-spanᵉ : equiv-spanᵉ → hom-spanᵉ sᵉ tᵉ
  pr1ᵉ (hom-equiv-spanᵉ eᵉ) = map-equiv-spanᵉ eᵉ
  pr1ᵉ (pr2ᵉ (hom-equiv-spanᵉ eᵉ)) = left-triangle-equiv-spanᵉ eᵉ
  pr2ᵉ (pr2ᵉ (hom-equiv-spanᵉ eᵉ)) = right-triangle-equiv-spanᵉ eᵉ

  is-equiv-equiv-spanᵉ :
    (eᵉ : equiv-spanᵉ) → is-equiv-hom-spanᵉ sᵉ tᵉ (hom-equiv-spanᵉ eᵉ)
  is-equiv-equiv-spanᵉ eᵉ = is-equiv-map-equivᵉ (equiv-equiv-spanᵉ eᵉ)

  compute-equiv-spanᵉ :
    Σᵉ (hom-spanᵉ sᵉ tᵉ) (is-equiv-hom-spanᵉ sᵉ tᵉ) ≃ᵉ equiv-spanᵉ
  compute-equiv-spanᵉ = equiv-right-swap-Σᵉ
```

### The identity equivalence on a span

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  id-equiv-spanᵉ : (sᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ) → equiv-spanᵉ sᵉ sᵉ
  pr1ᵉ (id-equiv-spanᵉ sᵉ) = id-equivᵉ
  pr1ᵉ (pr2ᵉ (id-equiv-spanᵉ sᵉ)) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ (id-equiv-spanᵉ sᵉ)) = refl-htpyᵉ
```

## Properties

### Extensionality of spans

Equalityᵉ ofᵉ spansᵉ isᵉ equivalentᵉ to equivalencesᵉ ofᵉ spans.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  equiv-eq-spanᵉ : (sᵉ tᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ) → sᵉ ＝ᵉ tᵉ → equiv-spanᵉ sᵉ tᵉ
  equiv-eq-spanᵉ sᵉ .sᵉ reflᵉ = id-equiv-spanᵉ sᵉ

  is-torsorial-equiv-spanᵉ : (sᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ) → is-torsorialᵉ (equiv-spanᵉ sᵉ)
  is-torsorial-equiv-spanᵉ sᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ (spanning-type-spanᵉ sᵉ))
      ( spanning-type-spanᵉ sᵉ ,ᵉ id-equivᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ (left-map-spanᵉ sᵉ))
        ( left-map-spanᵉ sᵉ ,ᵉ refl-htpyᵉ)
        ( is-torsorial-htpyᵉ (right-map-spanᵉ sᵉ)))

  is-equiv-equiv-eq-spanᵉ : (cᵉ dᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ) → is-equivᵉ (equiv-eq-spanᵉ cᵉ dᵉ)
  is-equiv-equiv-eq-spanᵉ cᵉ =
    fundamental-theorem-idᵉ (is-torsorial-equiv-spanᵉ cᵉ) (equiv-eq-spanᵉ cᵉ)

  extensionality-spanᵉ : (cᵉ dᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ) → (cᵉ ＝ᵉ dᵉ) ≃ᵉ (equiv-spanᵉ cᵉ dᵉ)
  pr1ᵉ (extensionality-spanᵉ cᵉ dᵉ) = equiv-eq-spanᵉ cᵉ dᵉ
  pr2ᵉ (extensionality-spanᵉ cᵉ dᵉ) = is-equiv-equiv-eq-spanᵉ cᵉ dᵉ

  eq-equiv-spanᵉ : (cᵉ dᵉ : spanᵉ l3ᵉ Aᵉ Bᵉ) → equiv-spanᵉ cᵉ dᵉ → cᵉ ＝ᵉ dᵉ
  eq-equiv-spanᵉ cᵉ dᵉ = map-inv-equivᵉ (extensionality-spanᵉ cᵉ dᵉ)
```