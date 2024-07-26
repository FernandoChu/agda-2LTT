# Epimorphisms in groups

```agda
module group-theory.epimorphisms-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.epimorphisms-in-large-precategoriesᵉ

open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.isomorphisms-groupsᵉ
open import group-theory.precategory-of-groupsᵉ
```

</details>

## Idea

Aᵉ [groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ) `fᵉ : Gᵉ → H`ᵉ isᵉ anᵉ
**epimorphism**ᵉ ifᵉ theᵉ precompositionᵉ functionᵉ

```text
  -ᵉ ∘ᵉ fᵉ : hom-set-Groupᵉ Hᵉ Kᵉ → hom-set-Groupᵉ Gᵉ Kᵉ
```

isᵉ anᵉ [embedding](foundation.embeddings.mdᵉ) forᵉ anyᵉ
[group](group-theory.groups.mdᵉ) `K`.ᵉ Inᵉ otherᵉ words,ᵉ `f`ᵉ isᵉ anᵉ epimorphismᵉ ifᵉ
forᵉ anyᵉ twoᵉ groupᵉ homomorphismsᵉ `gᵉ hᵉ : Hᵉ → K`ᵉ weᵉ haveᵉ thatᵉ `gᵉ ∘ᵉ fᵉ = hᵉ ∘ᵉ f`ᵉ
impliesᵉ `gᵉ = h`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Gᵉ : Groupᵉ l1ᵉ)
  (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  is-epi-prop-hom-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  is-epi-prop-hom-Groupᵉ =
    is-epi-prop-Large-Precategoryᵉ Group-Large-Precategoryᵉ l3ᵉ Gᵉ Hᵉ fᵉ

  is-epi-hom-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  is-epi-hom-Groupᵉ = type-Propᵉ is-epi-prop-hom-Groupᵉ

  is-prop-is-epi-hom-Groupᵉ : is-propᵉ is-epi-hom-Groupᵉ
  is-prop-is-epi-hom-Groupᵉ = is-prop-type-Propᵉ is-epi-prop-hom-Groupᵉ
```

## Properties

### Isomorphisms are epimorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Gᵉ : Groupᵉ l1ᵉ)
  (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : iso-Groupᵉ Gᵉ Hᵉ)
  where

  is-epi-iso-Groupᵉ : is-epi-hom-Groupᵉ l3ᵉ Gᵉ Hᵉ (hom-iso-Groupᵉ Gᵉ Hᵉ fᵉ)
  is-epi-iso-Groupᵉ =
    is-epi-iso-Large-Precategoryᵉ Group-Large-Precategoryᵉ l3ᵉ Gᵉ Hᵉ fᵉ
```

### A group homomorphism is surjective if and only if it is an epimorphism

**Proofᵉ using theᵉ lawᵉ ofᵉ excludedᵉ middle:**ᵉ Theᵉ forwardᵉ directionᵉ ofᵉ thisᵉ claimᵉ
isᵉ theᵉ easierᵉ ofᵉ theᵉ twoᵉ directions,ᵉ andᵉ thisᵉ partᵉ ofᵉ theᵉ proofᵉ doesn'tᵉ requireᵉ
theᵉ [lawᵉ ofᵉ excludedᵉ middle](foundation.law-of-excluded-middle.md).ᵉ Ifᵉ `f`ᵉ isᵉ
[surjective](foundation.surjective-maps.mdᵉ) andᵉ `gᵉ hᵉ : Hᵉ → K`ᵉ areᵉ twoᵉ groupᵉ
homomorphismsᵉ suchᵉ thatᵉ `gᵉ ∘ᵉ fᵉ ＝ᵉ hᵉ ∘ᵉ f`,ᵉ thenᵉ to showᵉ thatᵉ `gᵉ ＝ᵉ h`ᵉ itᵉ sufficesᵉ
to showᵉ thatᵉ `gᵉ yᵉ ＝ᵉ hᵉ y`ᵉ forᵉ anyᵉ `yᵉ : H`.ᵉ Sinceᵉ weᵉ areᵉ provingᵉ aᵉ
[proposition](foundation.propositions.mdᵉ) andᵉ `f`ᵉ isᵉ assumedᵉ to beᵉ surjective,ᵉ
weᵉ mayᵉ assumeᵉ `xᵉ : G`ᵉ equippedᵉ with anᵉ
[identification](foundation.identity-types.mdᵉ) `fᵉ xᵉ ＝ᵉ y`.ᵉ Itᵉ thereforeᵉ sufficesᵉ
to showᵉ thatᵉ `gᵉ (fᵉ xᵉ) ＝ᵉ hᵉ (fᵉ x)`,ᵉ whichᵉ wasᵉ assumed.ᵉ

Forᵉ theᵉ converse,ᵉ supposeᵉ thatᵉ `fᵉ : Gᵉ → H`ᵉ isᵉ anᵉ epimorphismᵉ andᵉ considerᵉ theᵉ
[imageᵉ subgroup](group-theory.images-of-group-homomorphisms.mdᵉ) `Iᵉ :=ᵉ imᵉ f`ᵉ ofᵉ
`H`.ᵉ Weᵉ firstᵉ showᵉ thatᵉ `I`ᵉ isᵉ [normal](group-theory.normal-subgroups.md),ᵉ andᵉ
thenᵉ weᵉ showᵉ thatᵉ `Iᵉ ＝ᵉ H`.ᵉ

Inᵉ orderᵉ to showᵉ thatᵉ `I`ᵉ isᵉ normal,ᵉ weᵉ wantᵉ to showᵉ thatᵉ `I`ᵉ hasᵉ onlyᵉ oneᵉ
conjugacyᵉ class,ᵉ namelyᵉ itself.ᵉ Considerᵉ theᵉ groupᵉ `K`ᵉ ofᵉ permutationsᵉ ofᵉ theᵉ
setᵉ ofᵉ [conjugate](group-theory.conjugation.mdᵉ)
[subgroups](group-theory.subgroups.mdᵉ) ofᵉ theᵉ subgroupᵉ `I`ᵉ ofᵉ `H`.ᵉ Thereᵉ isᵉ aᵉ
groupᵉ homomorphismᵉ `αᵉ : Hᵉ → K`ᵉ givenᵉ byᵉ `hᵉ ↦ᵉ Jᵉ ↦ᵉ hJh⁻¹`,ᵉ where `J`ᵉ rangesᵉ overᵉ
theᵉ conjugacyᵉ classesᵉ ofᵉ `I`.ᵉ Noticeᵉ thatᵉ `I`ᵉ itselfᵉ isᵉ aᵉ fixedᵉ pointᵉ ofᵉ theᵉ
conjugationᵉ operationᵉ `Jᵉ ↦ᵉ f(x)Jf(x)⁻¹`,ᵉ i.e.,ᵉ `I`ᵉ isᵉ aᵉ fixedᵉ pointᵉ ofᵉ
`α(f(x))`.ᵉ Weᵉ claimᵉ thatᵉ thereᵉ isᵉ anotherᵉ homomorphismᵉ `βᵉ : Hᵉ → K`ᵉ givenᵉ byᵉ
`hᵉ ↦ᵉ α(hᵉ) ∘ᵉ (Iᵉ h⁻¹Ih)`,ᵉ where weᵉ precomposeᵉ with theᵉ
[transposition](finite-group-theory.transpositions.mdᵉ) `(Iᵉ h⁻¹Ih)`.ᵉ Thisᵉ
transpositionᵉ isᵉ definedᵉ using theᵉ lawᵉ ofᵉ excludedᵉ middle.ᵉ However,ᵉ noteᵉ thatᵉ
`I`ᵉ isᵉ alwaysᵉ aᵉ fixedᵉ pointᵉ ofᵉ `β(h)`,ᵉ forᵉ anyᵉ `hᵉ : H`.ᵉ Furthermore,ᵉ weᵉ haveᵉ
`α(f(xᵉ)) ＝ᵉ β(f(x))`.ᵉ Thereforeᵉ itᵉ followsᵉ fromᵉ theᵉ assumptionᵉ thatᵉ `f`ᵉ isᵉ anᵉ
epimorphismᵉ thatᵉ `αᵉ ＝ᵉ β`.ᵉ Inᵉ otherᵉ words,ᵉ `I`ᵉ isᵉ aᵉ fixedᵉ pointᵉ ofᵉ anyᵉ
conjugationᵉ operationᵉ `Jᵉ ↦ᵉ hJh⁻¹`.ᵉ Weᵉ concludeᵉ thatᵉ `I`ᵉ isᵉ normal.ᵉ

Sinceᵉ `I`ᵉ isᵉ normal,ᵉ weᵉ mayᵉ considerᵉ theᵉ
[quotientᵉ group](group-theory.quotient-groups.mdᵉ) `H/I`.ᵉ Nowᵉ weᵉ observeᵉ thatᵉ theᵉ
quotientᵉ mapᵉ mapsᵉ `f(x)`ᵉ to theᵉ unitᵉ ofᵉ `H/I`.ᵉ Usingᵉ theᵉ assumptionᵉ thatᵉ `f`ᵉ isᵉ
anᵉ epimorphismᵉ onceᵉ more,ᵉ weᵉ concludeᵉ thatᵉ theᵉ quotientᵉ mapᵉ `Hᵉ → H/I`ᵉ isᵉ theᵉ
[trivialᵉ homomorphism](group-theory.trivial-group-homomorphisms.md).ᵉ Thereforeᵉ
itᵉ followsᵉ thatᵉ `Iᵉ ＝ᵉ H`.ᵉ Thisᵉ completesᵉ theᵉ proof.ᵉ