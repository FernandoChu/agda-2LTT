# Cospans of types

```agda
module foundation.cospansᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "cospan"ᵉ Disambiguation="types"ᵉ Agda=cospanᵉ}} fromᵉ `A`ᵉ to `B`ᵉ
consistsᵉ ofᵉ aᵉ typeᵉ `X`ᵉ andᵉ mapsᵉ `fᵉ : Aᵉ → X`ᵉ andᵉ `gᵉ : Bᵉ → X`,ᵉ asᵉ indicatedᵉ in theᵉ
diagramᵉ

```text
      fᵉ         gᵉ
  Aᵉ ----->ᵉ Xᵉ <-----ᵉ Bᵉ
```

Weᵉ disambiguateᵉ betweenᵉ cospansᵉ andᵉ
[cospanᵉ diagrams](foundation.cospan-diagrams.md).ᵉ Weᵉ considerᵉ aᵉ cospanᵉ fromᵉ `A`ᵉ
to `B`ᵉ aᵉ morphismᵉ fromᵉ `A`ᵉ to `B`ᵉ in theᵉ categoryᵉ ofᵉ typesᵉ andᵉ cospansᵉ betweenᵉ
them,ᵉ whereasᵉ weᵉ considerᵉ cospanᵉ diagramsᵉ to beᵉ _objectsᵉ_ in theᵉ categoryᵉ ofᵉ
diagramsᵉ ofᵉ typesᵉ ofᵉ theᵉ formᵉ `*ᵉ <----ᵉ *ᵉ ---->ᵉ *`.ᵉ Conceptuallyᵉ thereᵉ isᵉ aᵉ
subtle,ᵉ butᵉ importantᵉ distinctionᵉ betweenᵉ cospansᵉ andᵉ cospanᵉ diagrams.ᵉ Cospanᵉ
diagramsᵉ areᵉ moreᵉ suitableᵉ forᵉ functorialᵉ operationsᵉ thatᵉ takeᵉ "cospans"ᵉ asᵉ
input,ᵉ butᵉ forᵉ whichᵉ theᵉ functorialᵉ actionᵉ takesᵉ aᵉ naturalᵉ transformation,ᵉ i.e.,ᵉ
aᵉ morphismᵉ ofᵉ cospanᵉ diagrams,ᵉ asᵉ input.ᵉ Examplesᵉ ofᵉ thisᵉ kindᵉ includeᵉ
[pullbacks](foundation.pullbacks.md).ᵉ

## Definitions

### Cospans

```agda
cospanᵉ :
  {l1ᵉ l2ᵉ : Level} (lᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
cospanᵉ lᵉ Aᵉ Bᵉ =
  Σᵉ (UUᵉ lᵉ) (λ Xᵉ → (Aᵉ → Xᵉ) ×ᵉ (Bᵉ → Xᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {lᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (cᵉ : cospanᵉ lᵉ Aᵉ Bᵉ)
  where

  codomain-cospanᵉ : UUᵉ lᵉ
  codomain-cospanᵉ = pr1ᵉ cᵉ

  left-map-cospanᵉ : Aᵉ → codomain-cospanᵉ
  left-map-cospanᵉ = pr1ᵉ (pr2ᵉ cᵉ)

  right-map-cospanᵉ : Bᵉ → codomain-cospanᵉ
  right-map-cospanᵉ = pr2ᵉ (pr2ᵉ cᵉ)
```

## See also

-ᵉ Theᵉ formalᵉ dualᵉ ofᵉ cospansᵉ isᵉ [spans](foundation.spans.md).ᵉ
-ᵉ [Pullbacks](foundation-core.pullbacks.mdᵉ) areᵉ limitsᵉ ofᵉ
  [cospanᵉ diagrams](foundation.cospan-diagrams.md).ᵉ

### Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}