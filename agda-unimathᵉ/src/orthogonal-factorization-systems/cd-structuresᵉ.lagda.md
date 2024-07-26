# Cd-structures

```agda
module orthogonal-factorization-systems.cd-structuresᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.morphisms-arrowsᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ _cd-structureᵉ_ onᵉ aᵉ [category](category-theory.categories.mdᵉ) consistsᵉ ofᵉ aᵉ
classᵉ `𝒟`ᵉ ofᵉ
{{#conceptᵉ "distinguishedᵉ squares"ᵉ Disambiguation="cd-structure"ᵉ Agda=is-distinguished-square-cd-structureᵉ}}

```text
        iᵉ
    Aᵉ ----->ᵉ Xᵉ
    |        |
  fᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Y.ᵉ
        jᵉ
```

Onᵉ thisᵉ pageᵉ weᵉ willᵉ considerᵉ _internalᵉ_ cd-structures,ᵉ i.e.,ᵉ cd-structureᵉ onᵉ
types.ᵉ Inᵉ otherᵉ words,ᵉ aᵉ {{#conceptᵉ "cd-structure"ᵉ Agda=cd-structureᵉ}} isᵉ aᵉ
familyᵉ ofᵉ [subtypes](foundation-core.subtypes.mdᵉ)

```text
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) → hom-arrowᵉ fᵉ gᵉ → Prop,ᵉ
```

where `hom-arrowᵉ fᵉ g`ᵉ isᵉ theᵉ typeᵉ ofᵉ
[morphismsᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ) fromᵉ `f`ᵉ to `g`.ᵉ

Theᵉ terminologyᵉ "cd-structure"ᵉ originatesᵉ fromᵉ theᵉ ideaᵉ thatᵉ aᵉ Grothendieckᵉ
topologyᵉ isᵉ _completelyᵉ decomposableᵉ_ ifᵉ itᵉ isᵉ generatedᵉ byᵉ coveringᵉ familiesᵉ
thatᵉ areᵉ givenᵉ asᵉ pairsᵉ ofᵉ mapsᵉ with aᵉ commonᵉ codomainᵉ thatᵉ fitᵉ in aᵉ
distinguishedᵉ square.ᵉ

## Definitions

### Cd-structures

```agda
module _
  (αᵉ : Level → Level → Level → Level → Level)
  where

  cd-structureᵉ : UUωᵉ
  cd-structureᵉ =
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} →
    (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) → subtypeᵉ (αᵉ l1ᵉ l2ᵉ l3ᵉ l4ᵉ) (hom-arrowᵉ fᵉ gᵉ)

  is-distinguished-square-cd-structureᵉ :
    (Σᵉ : cd-structureᵉ) →
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} →
    (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) → hom-arrowᵉ fᵉ gᵉ → UUᵉ (αᵉ l1ᵉ l2ᵉ l3ᵉ l4ᵉ)
  is-distinguished-square-cd-structureᵉ Σᵉ fᵉ gᵉ σᵉ =
    type-Propᵉ (Σᵉ fᵉ gᵉ σᵉ)
```

## Exernal links

-ᵉ [cd-structure](https://ncatlab.org/nlab/show/cd-structureᵉ) atᵉ theᵉ $n$Labᵉ

## References

{{#bibliographyᵉ}} {{#referenceᵉ Voe10ᵉ}}