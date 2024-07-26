# The endomorphism rings of abelian groups

```agda
module group-theory.endomorphism-rings-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.addition-homomorphisms-abelian-groupsᵉ
open import group-theory.homomorphisms-abelian-groupsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Idea

Forᵉ anyᵉ abelianᵉ groupᵉ $A$,ᵉ theᵉ setᵉ $\mathrm{hom}(A,A)$ᵉ ofᵉ morphismsᵉ ofᵉ abelianᵉ
groupsᵉ canᵉ beᵉ equippedᵉ with theᵉ structureᵉ ofᵉ aᵉ ring,ᵉ where additionᵉ isᵉ givenᵉ
pointwiseᵉ andᵉ multiplicationᵉ isᵉ givenᵉ byᵉ composition.ᵉ

## Definition

### The endomorphism ring on an abelian group

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  ab-endomorphism-ring-Abᵉ : Abᵉ lᵉ
  ab-endomorphism-ring-Abᵉ = ab-hom-Abᵉ Aᵉ Aᵉ

  endomorphism-ring-Abᵉ : Ringᵉ lᵉ
  pr1ᵉ endomorphism-ring-Abᵉ = ab-endomorphism-ring-Abᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ endomorphism-ring-Abᵉ)) = comp-hom-Abᵉ Aᵉ Aᵉ Aᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ endomorphism-ring-Abᵉ)) = associative-comp-hom-Abᵉ Aᵉ Aᵉ Aᵉ Aᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ endomorphism-ring-Abᵉ))) = id-hom-Abᵉ Aᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ endomorphism-ring-Abᵉ)))) =
    left-unit-law-comp-hom-Abᵉ Aᵉ Aᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ endomorphism-ring-Abᵉ)))) =
    right-unit-law-comp-hom-Abᵉ Aᵉ Aᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ endomorphism-ring-Abᵉ))) =
    left-distributive-comp-add-hom-Abᵉ Aᵉ Aᵉ Aᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ endomorphism-ring-Abᵉ))) =
    right-distributive-comp-add-hom-Abᵉ Aᵉ Aᵉ Aᵉ
```