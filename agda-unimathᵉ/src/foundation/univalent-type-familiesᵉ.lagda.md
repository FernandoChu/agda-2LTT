# Univalent type families

```agda
module foundation.univalent-type-familiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-systemsᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subuniversesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-identity-systemsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "univalent"ᵉ Disambiguation="typeᵉ family"ᵉ Agda=is-univalentᵉ}} ifᵉ theᵉ
mapᵉ

```text
  equiv-trᵉ Bᵉ : xᵉ ＝ᵉ yᵉ → Bᵉ xᵉ ≃ᵉ Bᵉ yᵉ
```

isᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) forᵉ everyᵉ `xᵉ yᵉ : A`.ᵉ Byᵉ
[theᵉ univalenceᵉ axiom](foundation-core.univalence.md),ᵉ thisᵉ isᵉ equivalentᵉ to theᵉ
typeᵉ familyᵉ `B`ᵉ beingᵉ anᵉ [embedding](foundation-core.embeddings.mdᵉ) consideredᵉ
asᵉ aᵉ map.ᵉ

## Definition

### The predicate on type families of being univalent

```agda
is-univalentᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → (Aᵉ → UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-univalentᵉ {Aᵉ = Aᵉ} Bᵉ = (xᵉ yᵉ : Aᵉ) → is-equivᵉ (λ (pᵉ : xᵉ ＝ᵉ yᵉ) → equiv-trᵉ Bᵉ pᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  is-prop-is-univalentᵉ : is-propᵉ (is-univalentᵉ Bᵉ)
  is-prop-is-univalentᵉ =
    is-prop-iterated-Πᵉ 2 (λ xᵉ yᵉ → is-property-is-equivᵉ (equiv-trᵉ Bᵉ))

  is-univalent-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ is-univalent-Propᵉ = is-univalentᵉ Bᵉ
  pr2ᵉ is-univalent-Propᵉ = is-prop-is-univalentᵉ
```

### Univalent type families

```agda
univalent-type-familyᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
univalent-type-familyᵉ l2ᵉ Aᵉ = Σᵉ (Aᵉ → UUᵉ l2ᵉ) is-univalentᵉ
```

## Properties

### The univalence axiom states that the identity family `id : 𝒰 → 𝒰` is univalent

```agda
is-univalent-UUᵉ :
  (lᵉ : Level) → is-univalentᵉ (idᵉ {Aᵉ = UUᵉ lᵉ})
is-univalent-UUᵉ lᵉ = univalenceᵉ
```

### Assuming the univalence axiom, type families are univalent if and only if they are embeddings as maps

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

where theᵉ rightᵉ edgeᵉ isᵉ anᵉ equivalenceᵉ byᵉ theᵉ univalenceᵉ axiom.ᵉ Hence,ᵉ theᵉ topᵉ
mapᵉ isᵉ anᵉ equivalenceᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ leftᵉ mapᵉ is.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  abstract
    is-emb-is-univalentᵉ :
      is-univalentᵉ Bᵉ → is-embᵉ Bᵉ
    is-emb-is-univalentᵉ Uᵉ xᵉ yᵉ =
      is-equiv-top-map-triangleᵉ
        ( equiv-trᵉ Bᵉ)
        ( equiv-eqᵉ)
        ( apᵉ Bᵉ)
        ( λ where reflᵉ → reflᵉ)
        ( univalenceᵉ (Bᵉ xᵉ) (Bᵉ yᵉ))
        ( Uᵉ xᵉ yᵉ)

    is-univalent-is-embᵉ :
      is-embᵉ Bᵉ → is-univalentᵉ Bᵉ
    is-univalent-is-embᵉ is-emb-Bᵉ xᵉ yᵉ =
      is-equiv-left-map-triangleᵉ
        ( equiv-trᵉ Bᵉ)
        ( equiv-eqᵉ)
        ( apᵉ Bᵉ)
        ( λ where reflᵉ → reflᵉ)
        ( is-emb-Bᵉ xᵉ yᵉ)
        ( univalenceᵉ (Bᵉ xᵉ) (Bᵉ yᵉ))
```

### Univalent type families satisfy equivalence induction

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Uᵉ : is-univalentᵉ Bᵉ)
  where

  is-torsorial-fam-equiv-is-univalentᵉ :
    {xᵉ : Aᵉ} → is-torsorialᵉ (λ yᵉ → Bᵉ xᵉ ≃ᵉ Bᵉ yᵉ)
  is-torsorial-fam-equiv-is-univalentᵉ {xᵉ} =
    fundamental-theorem-id'ᵉ (λ yᵉ → equiv-trᵉ Bᵉ) (Uᵉ xᵉ)

  dependent-universal-property-identity-system-fam-equiv-is-univalentᵉ :
    {xᵉ : Aᵉ} →
    dependent-universal-property-identity-systemᵉ (λ yᵉ → Bᵉ xᵉ ≃ᵉ Bᵉ yᵉ) id-equivᵉ
  dependent-universal-property-identity-system-fam-equiv-is-univalentᵉ {xᵉ} =
    dependent-universal-property-identity-system-is-torsorialᵉ
      ( id-equivᵉ)
      ( is-torsorial-fam-equiv-is-univalentᵉ {xᵉ})
```

### Inclusions of subuniverses into the universe are univalent

**Note.**ᵉ Thisᵉ proofᵉ reliesᵉ onᵉ essentialᵉ useᵉ ofᵉ theᵉ univalenceᵉ axiom.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Sᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  where

  is-univalent-inclusion-subuniverseᵉ : is-univalentᵉ (inclusion-subuniverseᵉ Sᵉ)
  is-univalent-inclusion-subuniverseᵉ =
    is-univalent-is-embᵉ (is-emb-inclusion-subuniverseᵉ Sᵉ)
```

## See also

-ᵉ [Preunivalentᵉ typeᵉ families](foundation.preunivalent-type-families.mdᵉ)
-ᵉ [Transport-splitᵉ typeᵉ families](foundation.transport-split-type-families.mdᵉ):
  Byᵉ aᵉ corollaryᵉ ofᵉ
  [theᵉ fundamentalᵉ theoremᵉ ofᵉ identityᵉ types](foundation.fundamental-theorem-of-identity-types.md),ᵉ
  `equiv-trᵉ B`ᵉ isᵉ aᵉ
  [fiberwiseᵉ equivalence](foundation-core.families-of-equivalences.mdᵉ) asᵉ soonᵉ
  asᵉ itᵉ admitsᵉ aᵉ fiberwiseᵉ [section](foundation-core.sections.md).ᵉ