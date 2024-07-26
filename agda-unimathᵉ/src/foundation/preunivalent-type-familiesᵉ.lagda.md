# Preunivalent type families

```agda
module foundation.preunivalent-type-familiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-mapsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalence-injective-type-familiesᵉ
open import foundation.faithful-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.preunivalenceᵉ
open import foundation.retractionsᵉ
open import foundation.setsᵉ
open import foundation.subuniversesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.univalenceᵉ
```

</details>

## Idea

Aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "preunivalent"ᵉ Disambiguation="typeᵉ family"ᵉ Agda=is-preunivalentᵉ}} ifᵉ
theᵉ mapᵉ

```text
  equiv-trᵉ Bᵉ : xᵉ ＝ᵉ yᵉ → Bᵉ xᵉ ≃ᵉ Bᵉ yᵉ
```

isᵉ anᵉ [embedding](foundation-core.embeddings.mdᵉ) forᵉ everyᵉ `xᵉ yᵉ : A`.ᵉ

## Definition

```agda
is-preunivalentᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → (Aᵉ → UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-preunivalentᵉ {Aᵉ = Aᵉ} Bᵉ = (xᵉ yᵉ : Aᵉ) → is-embᵉ (λ (pᵉ : xᵉ ＝ᵉ yᵉ) → equiv-trᵉ Bᵉ pᵉ)
```

## Properties

### The preunivalence axiom states that the identity family `id : 𝒰 → 𝒰` is preunivalent

```agda
is-preunivalent-UUᵉ :
  (lᵉ : Level) → is-preunivalentᵉ (idᵉ {Aᵉ = UUᵉ lᵉ})
is-preunivalent-UUᵉ lᵉ = preunivalenceᵉ
```

### Assuming the preunivalence axiom, type families are preunivalent if and only if they are faithful as maps

**Proof:**ᵉ Weᵉ haveᵉ theᵉ
[commutingᵉ triangleᵉ ofᵉ maps](foundation-core.commuting-triangles-of-maps.mdᵉ)

```text
                apᵉ Bᵉ
       (xᵉ ＝ᵉ yᵉ) ----->ᵉ (Bᵉ xᵉ ＝ᵉ Bᵉ yᵉ)
           \ᵉ               /ᵉ
            \ᵉ             /ᵉ
  equiv-trᵉ Bᵉ \ᵉ           /ᵉ equiv-eqᵉ
              ∨ᵉ         ∨ᵉ
              (Bᵉ xᵉ ≃ᵉ Bᵉ yᵉ)
```

where theᵉ rightᵉ edgeᵉ isᵉ anᵉ embeddingᵉ byᵉ theᵉ
[preunivalenceᵉ axiom](foundation.preunivalence.md).ᵉ Hence,ᵉ theᵉ topᵉ mapᵉ isᵉ anᵉ
embeddingᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ leftᵉ mapᵉ is.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  abstract
    is-faithful-is-preunivalentᵉ :
      is-preunivalentᵉ Bᵉ → is-faithfulᵉ Bᵉ
    is-faithful-is-preunivalentᵉ Uᵉ xᵉ yᵉ =
      is-emb-top-map-triangleᵉ
        ( equiv-trᵉ Bᵉ)
        ( equiv-eqᵉ)
        ( apᵉ Bᵉ)
        ( λ where reflᵉ → reflᵉ)
        ( preunivalenceᵉ (Bᵉ xᵉ) (Bᵉ yᵉ))
        ( Uᵉ xᵉ yᵉ)

    is-preunivalent-is-faithfulᵉ :
      is-faithfulᵉ Bᵉ → is-preunivalentᵉ Bᵉ
    is-preunivalent-is-faithfulᵉ is-faithful-Bᵉ xᵉ yᵉ =
      is-emb-left-map-triangleᵉ
        ( equiv-trᵉ Bᵉ)
        ( equiv-eqᵉ)
        ( apᵉ Bᵉ)
        ( λ where reflᵉ → reflᵉ)
        ( preunivalenceᵉ (Bᵉ xᵉ) (Bᵉ yᵉ))
        ( is-faithful-Bᵉ xᵉ yᵉ)

    is-0-map-is-preunivalentᵉ :
      is-preunivalentᵉ Bᵉ → is-0-mapᵉ Bᵉ
    is-0-map-is-preunivalentᵉ Uᵉ =
      is-0-map-is-faithfulᵉ (is-faithful-is-preunivalentᵉ Uᵉ)

    is-preunivalent-is-0-mapᵉ :
      is-0-mapᵉ Bᵉ → is-preunivalentᵉ Bᵉ
    is-preunivalent-is-0-mapᵉ Hᵉ =
      is-preunivalent-is-faithfulᵉ (is-faithful-is-0-mapᵉ Hᵉ)
```

### Families of sets are preunivalent if `equiv-tr` is fiberwise injective

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (is-set-Bᵉ : (xᵉ : Aᵉ) → is-setᵉ (Bᵉ xᵉ))
  where

  is-preunivalent-is-injective-equiv-tr-is-setᵉ :
    ((xᵉ yᵉ : Aᵉ) → is-injectiveᵉ (equiv-trᵉ Bᵉ {xᵉ} {yᵉ})) →
    is-preunivalentᵉ Bᵉ
  is-preunivalent-is-injective-equiv-tr-is-setᵉ is-inj-Bᵉ xᵉ yᵉ =
    is-emb-is-injectiveᵉ
      ( is-set-equiv-is-setᵉ (is-set-Bᵉ xᵉ) (is-set-Bᵉ yᵉ))
      ( is-inj-Bᵉ xᵉ yᵉ)

  is-preunivalent-retraction-equiv-tr-is-setᵉ :
    ((xᵉ yᵉ : Aᵉ) → retractionᵉ (equiv-trᵉ Bᵉ {xᵉ} {yᵉ})) →
    is-preunivalentᵉ Bᵉ
  is-preunivalent-retraction-equiv-tr-is-setᵉ Rᵉ =
    is-preunivalent-is-injective-equiv-tr-is-setᵉ
      ( λ xᵉ yᵉ → is-injective-retractionᵉ (equiv-trᵉ Bᵉ) (Rᵉ xᵉ yᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → Setᵉ l2ᵉ)
  where

  is-preunivalent-is-injective-equiv-tr-Setᵉ :
    ((xᵉ yᵉ : Aᵉ) → is-injectiveᵉ (equiv-trᵉ (type-Setᵉ ∘ᵉ Bᵉ) {xᵉ} {yᵉ})) →
    is-preunivalentᵉ (type-Setᵉ ∘ᵉ Bᵉ)
  is-preunivalent-is-injective-equiv-tr-Setᵉ =
    is-preunivalent-is-injective-equiv-tr-is-setᵉ
      ( type-Setᵉ ∘ᵉ Bᵉ)
      ( is-set-type-Setᵉ ∘ᵉ Bᵉ)

  is-preunivalent-retraction-equiv-tr-Setᵉ :
    ((xᵉ yᵉ : Aᵉ) → retractionᵉ (equiv-trᵉ (type-Setᵉ ∘ᵉ Bᵉ) {xᵉ} {yᵉ})) →
    is-preunivalentᵉ (type-Setᵉ ∘ᵉ Bᵉ)
  is-preunivalent-retraction-equiv-tr-Setᵉ =
    is-preunivalent-retraction-equiv-tr-is-setᵉ
      ( type-Setᵉ ∘ᵉ Bᵉ)
      ( is-set-type-Setᵉ ∘ᵉ Bᵉ)
```

### Inclusions of subuniverses into the universe are preunivalent

**Note.**ᵉ Theseᵉ proofsᵉ relyᵉ onᵉ essentialᵉ useᵉ ofᵉ theᵉ preunivalenceᵉ axiom.ᵉ

```agda
is-preunivalent-projection-Type-With-Set-Elementᵉ :
  {l1ᵉ l2ᵉ : Level} (Sᵉ : UUᵉ l1ᵉ → Setᵉ l2ᵉ) →
  is-preunivalentᵉ (pr1ᵉ {Aᵉ = UUᵉ l1ᵉ} {Bᵉ = type-Setᵉ ∘ᵉ Sᵉ})
is-preunivalent-projection-Type-With-Set-Elementᵉ Sᵉ =
  is-preunivalent-is-0-mapᵉ (is-0-map-pr1ᵉ (is-set-type-Setᵉ ∘ᵉ Sᵉ))

is-preunivalent-inclusion-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Sᵉ : subuniverseᵉ l1ᵉ l2ᵉ) →
  is-preunivalentᵉ (inclusion-subuniverseᵉ Sᵉ)
is-preunivalent-inclusion-subuniverseᵉ Sᵉ =
  is-preunivalent-projection-Type-With-Set-Elementᵉ (set-Propᵉ ∘ᵉ Sᵉ)
```

## See also

-ᵉ [Univalentᵉ typeᵉ families](foundation.univalent-type-families.mdᵉ)
-ᵉ [Transport-splitᵉ typeᵉ families](foundation.transport-split-type-families.mdᵉ)
-ᵉ Theᵉ [standardᵉ finiteᵉ types](univalent-combinatorics.standard-finite-types.mdᵉ)
  isᵉ aᵉ typeᵉ familyᵉ whichᵉ isᵉ preunivalentᵉ butᵉ notᵉ univalent.ᵉ