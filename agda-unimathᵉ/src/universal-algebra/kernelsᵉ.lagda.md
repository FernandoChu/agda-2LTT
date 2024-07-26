# Kernels of homomorphisms of algebras

```agda
module universal-algebra.kernelsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.functoriality-vectorsᵉ
open import linear-algebra.vectorsᵉ

open import universal-algebra.algebraic-theoriesᵉ
open import universal-algebra.algebras-of-theoriesᵉ
open import universal-algebra.congruencesᵉ
open import universal-algebra.homomorphisms-of-algebrasᵉ
open import universal-algebra.signaturesᵉ
```

</details>

## Idea

Theᵉ kernelᵉ ofᵉ aᵉ homomorphismᵉ `f`ᵉ ofᵉ algebrasᵉ isᵉ theᵉ congruenceᵉ relationᵉ givenᵉ byᵉ
`xᵉ ~ᵉ y`ᵉ iffᵉ `fᵉ xᵉ ~ᵉ fᵉ y`.ᵉ

## Definitions

```agda
module _
  { l1ᵉ : Level} ( Sgᵉ : signatureᵉ l1ᵉ)
  { l2ᵉ : Level} ( Thᵉ : Theoryᵉ Sgᵉ l2ᵉ)
  { l3ᵉ l4ᵉ : Level}
  ( Alg1ᵉ : Algebraᵉ Sgᵉ Thᵉ l3ᵉ)
  ( Alg2ᵉ : Algebraᵉ Sgᵉ Thᵉ l4ᵉ)
  ( Fᵉ : hom-Algebraᵉ Sgᵉ Thᵉ Alg1ᵉ Alg2ᵉ)
  where

  rel-prop-kernel-hom-Algebraᵉ :
    Relation-Propᵉ l4ᵉ (type-Algebraᵉ Sgᵉ Thᵉ Alg1ᵉ)
  pr1ᵉ (rel-prop-kernel-hom-Algebraᵉ xᵉ yᵉ) =
    map-hom-Algebraᵉ Sgᵉ Thᵉ Alg1ᵉ Alg2ᵉ Fᵉ xᵉ ＝ᵉ
      map-hom-Algebraᵉ Sgᵉ Thᵉ Alg1ᵉ Alg2ᵉ Fᵉ yᵉ
  pr2ᵉ (rel-prop-kernel-hom-Algebraᵉ xᵉ yᵉ) =
    is-set-Algebraᵉ Sgᵉ Thᵉ Alg2ᵉ _ _

  equivalence-relation-kernel-hom-Algebraᵉ :
    equivalence-relationᵉ l4ᵉ (type-Algebraᵉ Sgᵉ Thᵉ Alg1ᵉ)
  pr1ᵉ equivalence-relation-kernel-hom-Algebraᵉ =
    rel-prop-kernel-hom-Algebraᵉ
  pr1ᵉ (pr2ᵉ equivalence-relation-kernel-hom-Algebraᵉ) _ = reflᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-kernel-hom-Algebraᵉ)) _ _ = invᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-kernel-hom-Algebraᵉ)) _ _ _ fᵉ gᵉ = gᵉ ∙ᵉ fᵉ

  kernel-hom-Algebraᵉ :
    congruence-Algebraᵉ Sgᵉ Thᵉ Alg1ᵉ l4ᵉ
  pr1ᵉ kernel-hom-Algebraᵉ = equivalence-relation-kernel-hom-Algebraᵉ
  pr2ᵉ kernel-hom-Algebraᵉ opᵉ vᵉ v'ᵉ pᵉ =
    equational-reasoningᵉ
      fᵉ (is-model-set-Algebraᵉ Sgᵉ Thᵉ Alg1ᵉ opᵉ vᵉ)
      ＝ᵉ is-model-set-Algebraᵉ Sgᵉ Thᵉ Alg2ᵉ opᵉ (map-vecᵉ fᵉ vᵉ)
        byᵉ preserves-operations-hom-Algebraᵉ Sgᵉ Thᵉ Alg1ᵉ Alg2ᵉ Fᵉ opᵉ vᵉ
      ＝ᵉ is-model-set-Algebraᵉ Sgᵉ Thᵉ Alg2ᵉ opᵉ (map-vecᵉ fᵉ v'ᵉ)
        byᵉ
          apᵉ
            ( is-model-set-Algebraᵉ Sgᵉ Thᵉ Alg2ᵉ opᵉ)
            ( map-hom-Algebra-lemmaᵉ (pr2ᵉ Sgᵉ opᵉ) vᵉ v'ᵉ pᵉ)
      ＝ᵉ fᵉ (is-model-set-Algebraᵉ Sgᵉ Thᵉ Alg1ᵉ opᵉ v'ᵉ)
        byᵉ invᵉ (preserves-operations-hom-Algebraᵉ Sgᵉ Thᵉ Alg1ᵉ Alg2ᵉ Fᵉ opᵉ v'ᵉ)
    where
    fᵉ = map-hom-Algebraᵉ Sgᵉ Thᵉ Alg1ᵉ Alg2ᵉ Fᵉ
    map-hom-Algebra-lemmaᵉ :
      ( nᵉ : ℕᵉ) →
      ( vᵉ v'ᵉ : vecᵉ (type-Algebraᵉ Sgᵉ Thᵉ Alg1ᵉ) nᵉ) →
      ( relation-holds-all-vecᵉ Sgᵉ Thᵉ Alg1ᵉ
        equivalence-relation-kernel-hom-Algebraᵉ vᵉ v'ᵉ) →
      (map-vecᵉ fᵉ vᵉ) ＝ᵉ (map-vecᵉ fᵉ v'ᵉ)
    map-hom-Algebra-lemmaᵉ zero-ℕᵉ empty-vecᵉ empty-vecᵉ pᵉ = reflᵉ
    map-hom-Algebra-lemmaᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ vᵉ) (x'ᵉ ∷ᵉ v'ᵉ) (pᵉ ,ᵉ p'ᵉ) =
      ap-binaryᵉ (_∷ᵉ_) pᵉ (map-hom-Algebra-lemmaᵉ nᵉ vᵉ v'ᵉ p'ᵉ)
```