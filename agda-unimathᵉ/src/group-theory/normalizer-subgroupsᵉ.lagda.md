# Normalizer subgroups

```agda
module group-theory.normalizer-subgroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.conjugationᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subsets-groupsᵉ
```

</details>

## Idea

Considerᵉ aᵉ [subgroup](group-theory.subgroups.mdᵉ) `H`ᵉ ofᵉ aᵉ
[group](group-theory.groups.mdᵉ) `G`.ᵉ Theᵉ **normalizerᵉ subgroup**ᵉ `Nᴳ(H)`ᵉ ofᵉ `G`ᵉ
isᵉ theᵉ largestᵉ subgroupᵉ ofᵉ `G`ᵉ ofᵉ whichᵉ `H`ᵉ isᵉ aᵉ
[normalᵉ subgroup](group-theory.normal-subgroups.md).ᵉ Theᵉ normalizerᵉ subgroupᵉ
consistsᵉ ofᵉ allᵉ elementsᵉ `gᵉ : G`ᵉ suchᵉ thatᵉ `hᵉ ∈ᵉ Hᵉ ⇔ᵉ (gh)g⁻¹ᵉ ∈ᵉ H`ᵉ forᵉ allᵉ
`hᵉ ∈ᵉ G`.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ normalizerᵉ subgroupᵉ consistsᵉ ofᵉ allᵉ elementsᵉ `g`ᵉ
suchᵉ thatᵉ `(gH)g⁻¹ᵉ ＝ᵉ H`.ᵉ

Theᵉ weakerᵉ conditionᵉ thatᵉ `(gH)g⁻¹ᵉ ⊆ᵉ H`ᵉ isᵉ
[notᵉ sufficient](https://math.stackexchange.com/q/107862ᵉ) in theᵉ caseᵉ ofᵉ
infiniteᵉ groups.ᵉ Inᵉ thisᵉ case,ᵉ theᵉ groupᵉ elementsᵉ satisfyingᵉ thisᵉ weakerᵉ
conditionᵉ mayᵉ notᵉ beᵉ closedᵉ underᵉ inverses.ᵉ

Noteᵉ: Theᵉ normalizerᵉ subgroupᵉ shouldᵉ notᵉ beᵉ confusedᵉ with theᵉ
[normalᵉ closure](group-theory.normal-closures-subgroups.mdᵉ) ofᵉ aᵉ subgroup,ᵉ orᵉ
with theᵉ [normalᵉ core](group-theory.normal-cores-subgroups.mdᵉ) ofᵉ aᵉ subgroup.ᵉ

## Definitions

### The universal property of the normalizer subgroup

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  (Nᵉ : Subgroupᵉ l3ᵉ Gᵉ)
  where

  is-normalizer-Subgroupᵉ : UUωᵉ
  is-normalizer-Subgroupᵉ =
    {lᵉ : Level} (Kᵉ : Subgroupᵉ lᵉ Gᵉ) →
    ( {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
      is-in-Subgroupᵉ Gᵉ Kᵉ xᵉ →
      is-in-Subgroupᵉ Gᵉ Hᵉ yᵉ →
      is-in-Subgroupᵉ Gᵉ Hᵉ (conjugation-Groupᵉ Gᵉ xᵉ yᵉ)) ↔ᵉ
    leq-Subgroupᵉ Gᵉ Kᵉ Nᵉ
```

### The construction of the normalizer subgroup

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  subset-normalizer-Subgroupᵉ : subset-Groupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
  subset-normalizer-Subgroupᵉ xᵉ =
    implicit-Π-Propᵉ
      ( type-Groupᵉ Gᵉ)
      ( λ yᵉ →
        iff-Propᵉ
          ( subset-Subgroupᵉ Gᵉ Hᵉ yᵉ)
          ( subset-Subgroupᵉ Gᵉ Hᵉ (conjugation-Groupᵉ Gᵉ xᵉ yᵉ)))

  is-in-normalizer-Subgroupᵉ : type-Groupᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-in-normalizer-Subgroupᵉ =
    is-in-subtypeᵉ subset-normalizer-Subgroupᵉ

  is-closed-under-eq-normalizer-Subgroupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    is-in-normalizer-Subgroupᵉ xᵉ → xᵉ ＝ᵉ yᵉ → is-in-normalizer-Subgroupᵉ yᵉ
  is-closed-under-eq-normalizer-Subgroupᵉ =
    is-closed-under-eq-subtypeᵉ subset-normalizer-Subgroupᵉ

  restrict-conjugation-Subgroupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) → is-in-normalizer-Subgroupᵉ xᵉ →
    type-Subgroupᵉ Gᵉ Hᵉ → type-Subgroupᵉ Gᵉ Hᵉ
  pr1ᵉ (restrict-conjugation-Subgroupᵉ xᵉ uᵉ (yᵉ ,ᵉ hᵉ)) = conjugation-Groupᵉ Gᵉ xᵉ yᵉ
  pr2ᵉ (restrict-conjugation-Subgroupᵉ xᵉ uᵉ (yᵉ ,ᵉ hᵉ)) = forward-implicationᵉ uᵉ hᵉ

  contains-unit-normalizer-Subgroupᵉ :
    contains-unit-subset-Groupᵉ Gᵉ subset-normalizer-Subgroupᵉ
  pr1ᵉ contains-unit-normalizer-Subgroupᵉ uᵉ =
    is-closed-under-eq-Subgroup'ᵉ Gᵉ Hᵉ uᵉ (compute-conjugation-unit-Groupᵉ Gᵉ _)
  pr2ᵉ contains-unit-normalizer-Subgroupᵉ uᵉ =
    is-closed-under-eq-Subgroupᵉ Gᵉ Hᵉ uᵉ (compute-conjugation-unit-Groupᵉ Gᵉ _)

  is-closed-under-multiplication-normalizer-Subgroupᵉ :
    is-closed-under-multiplication-subset-Groupᵉ Gᵉ subset-normalizer-Subgroupᵉ
  pr1ᵉ (is-closed-under-multiplication-normalizer-Subgroupᵉ {xᵉ} {yᵉ} uᵉ vᵉ) wᵉ =
    is-closed-under-eq-Subgroup'ᵉ Gᵉ Hᵉ
      ( forward-implicationᵉ uᵉ (forward-implicationᵉ vᵉ wᵉ))
      ( compute-conjugation-mul-Groupᵉ Gᵉ xᵉ yᵉ _)
  pr2ᵉ (is-closed-under-multiplication-normalizer-Subgroupᵉ {xᵉ} {yᵉ} uᵉ vᵉ) wᵉ =
    backward-implicationᵉ vᵉ
      ( backward-implicationᵉ uᵉ
        ( is-closed-under-eq-Subgroupᵉ Gᵉ Hᵉ wᵉ
          ( compute-conjugation-mul-Groupᵉ Gᵉ xᵉ yᵉ _)))

  is-closed-under-inverses-normalizer-Subgroupᵉ :
    is-closed-under-inverses-subset-Groupᵉ Gᵉ subset-normalizer-Subgroupᵉ
  pr1ᵉ (is-closed-under-inverses-normalizer-Subgroupᵉ {xᵉ} uᵉ {yᵉ}) hᵉ =
    backward-implicationᵉ uᵉ
      ( is-closed-under-eq-Subgroup'ᵉ Gᵉ Hᵉ hᵉ
        ( is-section-conjugation-inv-Groupᵉ Gᵉ xᵉ yᵉ))
  pr2ᵉ (is-closed-under-inverses-normalizer-Subgroupᵉ {xᵉ} uᵉ {yᵉ}) hᵉ =
    is-closed-under-eq-Subgroupᵉ Gᵉ Hᵉ
      ( forward-implicationᵉ uᵉ hᵉ)
      ( is-section-conjugation-inv-Groupᵉ Gᵉ xᵉ yᵉ)

  normalizer-Subgroupᵉ : Subgroupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
  pr1ᵉ normalizer-Subgroupᵉ =
    subset-normalizer-Subgroupᵉ
  pr1ᵉ (pr2ᵉ normalizer-Subgroupᵉ) =
    contains-unit-normalizer-Subgroupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ normalizer-Subgroupᵉ)) =
    is-closed-under-multiplication-normalizer-Subgroupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ normalizer-Subgroupᵉ)) =
    is-closed-under-inverses-normalizer-Subgroupᵉ

  forward-implication-is-normalizer-normalizer-Subgroupᵉ :
    {lᵉ : Level} (Kᵉ : Subgroupᵉ lᵉ Gᵉ) →
    ( {xᵉ yᵉ : type-Groupᵉ Gᵉ} → is-in-Subgroupᵉ Gᵉ Kᵉ xᵉ →
      is-in-Subgroupᵉ Gᵉ Hᵉ yᵉ →
      is-in-Subgroupᵉ Gᵉ Hᵉ (conjugation-Groupᵉ Gᵉ xᵉ yᵉ)) →
    leq-Subgroupᵉ Gᵉ Kᵉ normalizer-Subgroupᵉ
  pr1ᵉ (forward-implication-is-normalizer-normalizer-Subgroupᵉ Kᵉ uᵉ xᵉ kᵉ {yᵉ}) hᵉ =
    uᵉ kᵉ hᵉ
  pr2ᵉ (forward-implication-is-normalizer-normalizer-Subgroupᵉ Kᵉ uᵉ xᵉ kᵉ {yᵉ}) hᵉ =
    is-closed-under-eq-Subgroupᵉ Gᵉ Hᵉ
      ( uᵉ (is-closed-under-inverses-Subgroupᵉ Gᵉ Kᵉ {xᵉ} kᵉ) hᵉ)
      ( is-retraction-conjugation-inv-Groupᵉ Gᵉ xᵉ yᵉ)

  backward-implication-is-normalizer-normalizer-Subgroupᵉ :
    {lᵉ : Level} (Kᵉ : Subgroupᵉ lᵉ Gᵉ) → leq-Subgroupᵉ Gᵉ Kᵉ normalizer-Subgroupᵉ →
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} → is-in-Subgroupᵉ Gᵉ Kᵉ xᵉ →
    is-in-Subgroupᵉ Gᵉ Hᵉ yᵉ →
    is-in-Subgroupᵉ Gᵉ Hᵉ (conjugation-Groupᵉ Gᵉ xᵉ yᵉ)
  backward-implication-is-normalizer-normalizer-Subgroupᵉ Kᵉ uᵉ {xᵉ} {yᵉ} kᵉ hᵉ =
    forward-implicationᵉ (uᵉ xᵉ kᵉ) hᵉ

  is-normalizer-normalizer-Subgroupᵉ :
    is-normalizer-Subgroupᵉ Gᵉ Hᵉ normalizer-Subgroupᵉ
  pr1ᵉ (is-normalizer-normalizer-Subgroupᵉ Kᵉ) =
    forward-implication-is-normalizer-normalizer-Subgroupᵉ Kᵉ
  pr2ᵉ (is-normalizer-normalizer-Subgroupᵉ Kᵉ) =
    backward-implication-is-normalizer-normalizer-Subgroupᵉ Kᵉ
```

### The inclusion of `H` into its normalizer `Nᴳ(H)`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ) (Nᵉ : Subgroupᵉ l3ᵉ Gᵉ)
  (is-normalizer-G-H-Nᵉ : is-normalizer-Subgroupᵉ Gᵉ Hᵉ Nᵉ)
  where

  is-in-normalizer-is-in-type-Subgroupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) → is-in-Subgroupᵉ Gᵉ Hᵉ xᵉ → is-in-Subgroupᵉ Gᵉ Nᵉ xᵉ
  is-in-normalizer-is-in-type-Subgroupᵉ =
    forward-implicationᵉ
      ( is-normalizer-G-H-Nᵉ Hᵉ)
      ( λ x'ᵉ y'ᵉ →
        is-closed-under-multiplication-Subgroupᵉ Gᵉ Hᵉ
          ( is-closed-under-multiplication-Subgroupᵉ Gᵉ Hᵉ x'ᵉ y'ᵉ)
          ( is-closed-under-inverses-Subgroupᵉ Gᵉ Hᵉ x'ᵉ))

  inclusion-is-normalizer-Subgroupᵉ : type-Subgroupᵉ Gᵉ Hᵉ → type-Subgroupᵉ Gᵉ Nᵉ
  inclusion-is-normalizer-Subgroupᵉ = totᵉ is-in-normalizer-is-in-type-Subgroupᵉ

  hom-inclusion-is-normalizer-Subgroupᵉ :
    hom-Groupᵉ (group-Subgroupᵉ Gᵉ Hᵉ) (group-Subgroupᵉ Gᵉ Nᵉ)
  pr1ᵉ hom-inclusion-is-normalizer-Subgroupᵉ =
    inclusion-is-normalizer-Subgroupᵉ
  pr2ᵉ hom-inclusion-is-normalizer-Subgroupᵉ =
    eq-type-subtypeᵉ (subset-Subgroupᵉ Gᵉ Nᵉ) reflᵉ
```

## See also

-ᵉ [Centralizerᵉ subgroups](group-theory.centralizer-subgroups.mdᵉ)
-ᵉ [Normalᵉ closuresᵉ ofᵉ subgroups](group-theory.normal-closures-subgroups.mdᵉ)
-ᵉ [Normalᵉ coresᵉ ofᵉ subgroups](group-theory.normal-cores-subgroups.mdᵉ)

## External links

-ᵉ [normalizer](https://ncatlab.org/nlab/show/normalizerᵉ) atᵉ $n$Labᵉ
-ᵉ [Centralizerᵉ andᵉ normalizer](https://en.wikipedia.org/wiki/Centralizer_and_normalizerᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Normalizerᵉ ofᵉ aᵉ subgroup](https://groupprops.subwiki.org/wiki/Normalizer_of_a_subgroupᵉ)
  atᵉ Grouppropsᵉ