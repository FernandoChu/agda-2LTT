# Hatcher's acyclic type

```agda
module synthetic-homotopy-theory.hatchers-acyclic-typeᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.path-algebraᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.pointed-universal-property-contractible-typesᵉ

open import synthetic-homotopy-theory.acyclic-typesᵉ
open import synthetic-homotopy-theory.eckmann-hilton-argumentᵉ
open import synthetic-homotopy-theory.functoriality-loop-spacesᵉ
open import synthetic-homotopy-theory.loop-spacesᵉ
open import synthetic-homotopy-theory.powers-of-loopsᵉ
open import synthetic-homotopy-theory.suspensions-of-pointed-typesᵉ
open import synthetic-homotopy-theory.universal-property-suspensions-of-pointed-typesᵉ
```

</details>

## Idea

**Hatcher'sᵉ [acyclicᵉ type](synthetic-homotopy-theory.acyclic-types.md)**ᵉ isᵉ aᵉ
higherᵉ inductive typeᵉ [equipped](foundation.structure.mdᵉ) with aᵉ baseᵉ pointᵉ andᵉ
twoᵉ [loops](synthetic-homotopy-theory.loop-spaces.mdᵉ) `a`ᵉ andᵉ `b`,ᵉ andᵉ
[identifications](foundation.identity-types.mdᵉ) witnessingᵉ thatᵉ `a⁵ᵉ ＝ᵉ b³`ᵉ andᵉ
`b³ᵉ = (ab)²`.ᵉ Thisᵉ typeᵉ isᵉ acyclic,ᵉ becauseᵉ theᵉ structureᵉ onᵉ Hatcher'sᵉ acyclicᵉ
typeᵉ onᵉ anyᵉ loopᵉ spaceᵉ isᵉ [contractible](foundation.contractible-types.md).ᵉ

## Definitions

### The structure of Hatcher's acyclic type

```agda
structure-Hatcher-Acyclic-Typeᵉ : {lᵉ : Level} → Pointed-Typeᵉ lᵉ → UUᵉ lᵉ
structure-Hatcher-Acyclic-Typeᵉ Aᵉ =
  Σᵉ ( type-Ωᵉ Aᵉ)
    ( λ aᵉ →
      Σᵉ ( type-Ωᵉ Aᵉ)
        ( λ bᵉ →
          ( power-nat-Ωᵉ 5 Aᵉ aᵉ ＝ᵉ power-nat-Ωᵉ 3 Aᵉ bᵉ) ×ᵉ
          ( power-nat-Ωᵉ 3 Aᵉ bᵉ ＝ᵉ power-nat-Ωᵉ 2 Aᵉ (aᵉ ∙ᵉ bᵉ))))
```

### Algebras with the structure of Hatcher's acyclic type

```agda
algebra-Hatcher-Acyclic-Typeᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
algebra-Hatcher-Acyclic-Typeᵉ lᵉ =
  Σᵉ (Pointed-Typeᵉ lᵉ) structure-Hatcher-Acyclic-Typeᵉ
```

### Morphisms of types equipped with the structure of Hatcher's acyclic type

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  ((Aᵉ ,ᵉ a1ᵉ ,ᵉ a2ᵉ ,ᵉ r1ᵉ ,ᵉ r2ᵉ) : algebra-Hatcher-Acyclic-Typeᵉ l1ᵉ)
  ((Bᵉ ,ᵉ b1ᵉ ,ᵉ b2ᵉ ,ᵉ s1ᵉ ,ᵉ s2ᵉ) : algebra-Hatcher-Acyclic-Typeᵉ l2ᵉ)
  where

  is-hom-pointed-map-algebra-Hatcher-Acyclic-Typeᵉ : (Aᵉ →∗ᵉ Bᵉ) → UUᵉ l2ᵉ
  is-hom-pointed-map-algebra-Hatcher-Acyclic-Typeᵉ fᵉ =
    Σᵉ ( map-Ωᵉ fᵉ a1ᵉ ＝ᵉ b1ᵉ)
      ( λ uᵉ →
        Σᵉ ( map-Ωᵉ fᵉ a2ᵉ ＝ᵉ b2ᵉ)
          ( λ vᵉ →
            ( coherence-square-identificationsᵉ
              ( apᵉ (map-Ωᵉ fᵉ) r1ᵉ)
              ( map-power-nat-Ωᵉ 5 fᵉ a1ᵉ ∙ᵉ apᵉ (power-nat-Ωᵉ 5 Bᵉ) uᵉ)
              ( map-power-nat-Ωᵉ 3 fᵉ a2ᵉ ∙ᵉ apᵉ (power-nat-Ωᵉ 3 Bᵉ) vᵉ)
              ( s1ᵉ)) ×ᵉ
            ( coherence-square-identificationsᵉ
              ( apᵉ (map-Ωᵉ fᵉ) r2ᵉ)
              ( map-power-nat-Ωᵉ 3 fᵉ a2ᵉ ∙ᵉ apᵉ (power-nat-Ωᵉ 3 Bᵉ) vᵉ)
              ( ( map-power-nat-Ωᵉ 2 fᵉ (a1ᵉ ∙ᵉ a2ᵉ)) ∙ᵉ
                ( apᵉ
                  ( power-nat-Ωᵉ 2 Bᵉ)
                  ( ( preserves-mul-map-Ωᵉ fᵉ) ∙ᵉ
                    ( horizontal-concat-Id²ᵉ uᵉ vᵉ))))
              ( s2ᵉ))))

  hom-algebra-Hatcher-Acyclic-Typeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-algebra-Hatcher-Acyclic-Typeᵉ =
    Σᵉ ( Aᵉ →∗ᵉ Bᵉ) is-hom-pointed-map-algebra-Hatcher-Acyclic-Typeᵉ
```

### Initial Hatcher acyclic algebras

Oneᵉ characterizationᵉ ofᵉ Hatcher'sᵉ acyclicᵉ typeᵉ isᵉ throughᵉ itsᵉ universalᵉ propertyᵉ
asᵉ beingᵉ theᵉ initialᵉ Hatcherᵉ acyclicᵉ algebra.ᵉ

```agda
is-initial-algebra-Hatcher-Acyclic-Typeᵉ :
  {l1ᵉ : Level} (Aᵉ : algebra-Hatcher-Acyclic-Typeᵉ l1ᵉ) → UUωᵉ
is-initial-algebra-Hatcher-Acyclic-Typeᵉ Aᵉ =
  {lᵉ : Level} →
  (Bᵉ : algebra-Hatcher-Acyclic-Typeᵉ lᵉ) →
  is-contrᵉ (hom-algebra-Hatcher-Acyclic-Typeᵉ Aᵉ Bᵉ)
```

## Properties

### Characterization of identifications of Hatcher acyclic type structures

```agda
module _
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ) (sᵉ : structure-Hatcher-Acyclic-Typeᵉ Aᵉ)
  where

  Eq-structure-Hatcher-Acyclic-Typeᵉ :
    structure-Hatcher-Acyclic-Typeᵉ Aᵉ → UUᵉ lᵉ
  Eq-structure-Hatcher-Acyclic-Typeᵉ tᵉ =
    Σᵉ ( pr1ᵉ sᵉ ＝ᵉ pr1ᵉ tᵉ)
      ( λ pᵉ →
        Σᵉ ( pr1ᵉ (pr2ᵉ sᵉ) ＝ᵉ pr1ᵉ (pr2ᵉ tᵉ))
          ( λ qᵉ →
            ( ( pr1ᵉ (pr2ᵉ (pr2ᵉ sᵉ)) ∙ᵉ apᵉ (power-nat-Ωᵉ 3 Aᵉ) qᵉ) ＝ᵉ
              ( (apᵉ (power-nat-Ωᵉ 5 Aᵉ) pᵉ) ∙ᵉ pr1ᵉ (pr2ᵉ (pr2ᵉ tᵉ)))) ×ᵉ
            ( ( pr2ᵉ (pr2ᵉ (pr2ᵉ sᵉ)) ∙ᵉ
                apᵉ (power-nat-Ωᵉ 2 Aᵉ) (horizontal-concat-Id²ᵉ pᵉ qᵉ)) ＝ᵉ
              ( apᵉ (power-nat-Ωᵉ 3 Aᵉ) qᵉ ∙ᵉ pr2ᵉ (pr2ᵉ (pr2ᵉ tᵉ))))))

  refl-Eq-structure-Hatcher-Acyclic-Typeᵉ :
    Eq-structure-Hatcher-Acyclic-Typeᵉ sᵉ
  pr1ᵉ refl-Eq-structure-Hatcher-Acyclic-Typeᵉ = reflᵉ
  pr1ᵉ (pr2ᵉ refl-Eq-structure-Hatcher-Acyclic-Typeᵉ) = reflᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ refl-Eq-structure-Hatcher-Acyclic-Typeᵉ)) = right-unitᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ refl-Eq-structure-Hatcher-Acyclic-Typeᵉ)) = right-unitᵉ

  is-torsorial-Eq-structure-Hatcher-Acyclic-Typeᵉ :
    is-torsorialᵉ Eq-structure-Hatcher-Acyclic-Typeᵉ
  is-torsorial-Eq-structure-Hatcher-Acyclic-Typeᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-Idᵉ (pr1ᵉ sᵉ))
      ( pr1ᵉ sᵉ ,ᵉ reflᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-Idᵉ (pr1ᵉ (pr2ᵉ sᵉ)))
        ( pr1ᵉ (pr2ᵉ sᵉ) ,ᵉ reflᵉ)
        ( is-torsorial-Eq-structureᵉ
          ( is-torsorial-Idᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ sᵉ)) ∙ᵉ reflᵉ))
          ( pr1ᵉ (pr2ᵉ (pr2ᵉ sᵉ)) ,ᵉ right-unitᵉ)
          ( is-torsorial-Idᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ sᵉ)) ∙ᵉ reflᵉ))))

  Eq-eq-structure-Hatcher-Acyclic-Typeᵉ :
    (tᵉ : structure-Hatcher-Acyclic-Typeᵉ Aᵉ) →
    (sᵉ ＝ᵉ tᵉ) → Eq-structure-Hatcher-Acyclic-Typeᵉ tᵉ
  Eq-eq-structure-Hatcher-Acyclic-Typeᵉ .sᵉ reflᵉ =
    refl-Eq-structure-Hatcher-Acyclic-Typeᵉ

  is-equiv-Eq-eq-structure-Hatcher-Acyclic-Typeᵉ :
    (tᵉ : structure-Hatcher-Acyclic-Typeᵉ Aᵉ) →
    is-equivᵉ (Eq-eq-structure-Hatcher-Acyclic-Typeᵉ tᵉ)
  is-equiv-Eq-eq-structure-Hatcher-Acyclic-Typeᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-Eq-structure-Hatcher-Acyclic-Typeᵉ
      Eq-eq-structure-Hatcher-Acyclic-Typeᵉ

  extensionality-structure-Hatcher-Acyclic-Typeᵉ :
    (tᵉ : structure-Hatcher-Acyclic-Typeᵉ Aᵉ) →
    (sᵉ ＝ᵉ tᵉ) ≃ᵉ Eq-structure-Hatcher-Acyclic-Typeᵉ tᵉ
  pr1ᵉ (extensionality-structure-Hatcher-Acyclic-Typeᵉ tᵉ) =
    Eq-eq-structure-Hatcher-Acyclic-Typeᵉ tᵉ
  pr2ᵉ (extensionality-structure-Hatcher-Acyclic-Typeᵉ tᵉ) =
    is-equiv-Eq-eq-structure-Hatcher-Acyclic-Typeᵉ tᵉ

  eq-Eq-structure-Hatcher-Acyclic-Typeᵉ :
    (tᵉ : structure-Hatcher-Acyclic-Typeᵉ Aᵉ) →
    Eq-structure-Hatcher-Acyclic-Typeᵉ tᵉ → sᵉ ＝ᵉ tᵉ
  eq-Eq-structure-Hatcher-Acyclic-Typeᵉ tᵉ =
    map-inv-equivᵉ (extensionality-structure-Hatcher-Acyclic-Typeᵉ tᵉ)
```

### Loop spaces uniquely have the structure of a Hatcher acyclic type

```agda
module _
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ)
  where

  is-contr-structure-Hatcher-Acyclic-Type-Ωᵉ :
    is-contrᵉ (structure-Hatcher-Acyclic-Typeᵉ (Ωᵉ Aᵉ))
  is-contr-structure-Hatcher-Acyclic-Type-Ωᵉ =
    is-contr-equivᵉ
      ( Σᵉ (type-Ωᵉ (Ωᵉ Aᵉ)) (λ aᵉ → reflᵉ ＝ᵉ aᵉ))
      ( equiv-totᵉ
        ( λ aᵉ →
          ( ( inv-equivᵉ
              ( equiv-apᵉ
                ( equiv-concat'ᵉ (refl-Ωᵉ Aᵉ) (power-nat-Ωᵉ 5 (Ωᵉ Aᵉ) aᵉ))
                ( refl-Ωᵉ (Ωᵉ Aᵉ))
                ( aᵉ))) ∘eᵉ
            ( equiv-concat'ᵉ
              ( power-nat-Ωᵉ 5 (Ωᵉ Aᵉ) aᵉ)
              ( ( invᵉ (power-nat-mul-Ωᵉ 3 2 (Ωᵉ Aᵉ) aᵉ)) ∙ᵉ
                ( power-nat-succ-Ω'ᵉ 5 (Ωᵉ Aᵉ) aᵉ)))) ∘eᵉ
          ( ( ( left-unit-law-Σ-is-contrᵉ
                ( is-torsorial-Id'ᵉ (aᵉ ∙ᵉ aᵉ))
                ( aᵉ ∙ᵉ aᵉ ,ᵉ reflᵉ)) ∘eᵉ
              ( inv-associative-Σᵉ
                ( type-Ωᵉ (Ωᵉ Aᵉ))
                ( λ bᵉ → bᵉ ＝ᵉ (aᵉ ∙ᵉ aᵉ))
                ( λ bqᵉ →
                  power-nat-Ωᵉ 5 (Ωᵉ Aᵉ) aᵉ ＝ᵉ power-nat-Ωᵉ 3 (Ωᵉ Aᵉ) (pr1ᵉ bqᵉ)))) ∘eᵉ
            ( equiv-totᵉ
              ( λ bᵉ →
                ( commutative-productᵉ) ∘eᵉ
                ( equiv-productᵉ
                  ( id-equivᵉ)
                  ( ( ( inv-equivᵉ
                        ( equiv-apᵉ
                          ( equiv-concat'ᵉ (refl-Ωᵉ Aᵉ) (bᵉ ∙ᵉ bᵉ))
                          ( bᵉ)
                          ( aᵉ ∙ᵉ aᵉ))) ∘eᵉ
                      ( equiv-concatᵉ
                        ( invᵉ (power-nat-add-Ωᵉ 1 2 (Ωᵉ Aᵉ) bᵉ))
                        ( (aᵉ ∙ᵉ aᵉ) ∙ᵉ (bᵉ ∙ᵉ bᵉ)))) ∘eᵉ
                    ( equiv-concat'ᵉ
                      ( power-nat-Ωᵉ 3 (Ωᵉ Aᵉ) bᵉ)
                      ( interchange-concat-Ω²ᵉ aᵉ bᵉ aᵉ bᵉ)))))))))
        ( is-torsorial-Idᵉ reflᵉ)
```

### For a fixed pointed map, the `is-hom-pointed-map-algebra-Hatcher-Acyclic-Type` family is torsorial

Inᵉ provingᵉ this,ᵉ itᵉ isᵉ helpfulᵉ to considerᵉ anᵉ equivalentᵉ formulationᵉ ofᵉ
`is-hom-pointed-map-algebra-Hatcher-Acyclic-Type`ᵉ forᵉ whichᵉ
[torsoriality](foundation.torsorial-type-families.mdᵉ) isᵉ almostᵉ immediate.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  ((Aᵉ ,ᵉ a1ᵉ ,ᵉ a2ᵉ ,ᵉ r1ᵉ ,ᵉ r2ᵉ) : algebra-Hatcher-Acyclic-Typeᵉ l1ᵉ)
  ((Bᵉ ,ᵉ b1ᵉ ,ᵉ b2ᵉ ,ᵉ s1ᵉ ,ᵉ s2ᵉ) : algebra-Hatcher-Acyclic-Typeᵉ l2ᵉ)
  where

  is-hom-pointed-map-algebra-Hatcher-Acyclic-Type'ᵉ : (Aᵉ →∗ᵉ Bᵉ) → UUᵉ l2ᵉ
  is-hom-pointed-map-algebra-Hatcher-Acyclic-Type'ᵉ fᵉ =
    Σᵉ ( map-Ωᵉ fᵉ a1ᵉ ＝ᵉ b1ᵉ)
      ( λ uᵉ →
        Σᵉ ( map-Ωᵉ fᵉ a2ᵉ ＝ᵉ b2ᵉ)
          ( λ vᵉ →
            ( Idᵉ
              ( invᵉ (map-power-nat-Ωᵉ 5 fᵉ a1ᵉ ∙ᵉ apᵉ (power-nat-Ωᵉ 5 Bᵉ) uᵉ) ∙ᵉ
                ( apᵉ (map-Ωᵉ fᵉ) r1ᵉ ∙ᵉ
                  (map-power-nat-Ωᵉ 3 fᵉ a2ᵉ ∙ᵉ apᵉ (power-nat-Ωᵉ 3 Bᵉ) vᵉ)))
              ( s1ᵉ)) ×ᵉ
            ( Idᵉ
              ( invᵉ (map-power-nat-Ωᵉ 3 fᵉ a2ᵉ ∙ᵉ apᵉ (power-nat-Ωᵉ 3 Bᵉ) vᵉ) ∙ᵉ
                ( apᵉ (map-Ωᵉ fᵉ) r2ᵉ ∙ᵉ
                  ( ( map-power-nat-Ωᵉ 2 fᵉ (a1ᵉ ∙ᵉ a2ᵉ)) ∙ᵉ
                    ( apᵉ
                      ( power-nat-Ωᵉ 2 Bᵉ)
                      ( ( preserves-mul-map-Ωᵉ fᵉ) ∙ᵉ
                        ( horizontal-concat-Id²ᵉ uᵉ vᵉ))))))
              ( s2ᵉ))))

module _
  {l1ᵉ l2ᵉ : Level}
  ((Aᵉ ,ᵉ σᵉ) : algebra-Hatcher-Acyclic-Typeᵉ l1ᵉ)
  ((Bᵉ ,ᵉ τᵉ) : algebra-Hatcher-Acyclic-Typeᵉ l2ᵉ)
  where

  equiv-is-hom-pointed-map-algebra-Hatcher-Acyclic-Typeᵉ :
    (fᵉ : Aᵉ →∗ᵉ Bᵉ) →
    is-hom-pointed-map-algebra-Hatcher-Acyclic-Typeᵉ (Aᵉ ,ᵉ σᵉ) (Bᵉ ,ᵉ τᵉ) fᵉ ≃ᵉ
    is-hom-pointed-map-algebra-Hatcher-Acyclic-Type'ᵉ (Aᵉ ,ᵉ σᵉ) (Bᵉ ,ᵉ τᵉ) fᵉ
  equiv-is-hom-pointed-map-algebra-Hatcher-Acyclic-Typeᵉ fᵉ =
    equiv-totᵉ
      ( λ pᵉ →
        equiv-totᵉ
          ( λ qᵉ →
            equiv-productᵉ
              ( equiv-left-transpose-eq-concat'ᵉ _ _ _ ∘eᵉ equiv-invᵉ _ _)
              ( equiv-left-transpose-eq-concat'ᵉ _ _ _ ∘eᵉ equiv-invᵉ _ _)))

module _
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : Pointed-Typeᵉ l1ᵉ)
  (Bᵉ : Pointed-Typeᵉ l2ᵉ)
  (σ@(a1ᵉ ,ᵉ a2ᵉ ,ᵉ r1ᵉ ,ᵉ r2ᵉ) : structure-Hatcher-Acyclic-Typeᵉ Aᵉ)
  (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  is-torsorial-is-hom-pointed-map-algebra-Hatcher-Acyclic-Type'ᵉ :
    is-torsorialᵉ
      ( λ τᵉ →
        is-hom-pointed-map-algebra-Hatcher-Acyclic-Type'ᵉ (Aᵉ ,ᵉ σᵉ) (Bᵉ ,ᵉ τᵉ) fᵉ)
  is-torsorial-is-hom-pointed-map-algebra-Hatcher-Acyclic-Type'ᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-Idᵉ (map-Ωᵉ fᵉ a1ᵉ)) ((map-Ωᵉ fᵉ a1ᵉ) ,ᵉ reflᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-Idᵉ (map-Ωᵉ fᵉ a2ᵉ)) ((map-Ωᵉ fᵉ a2ᵉ) ,ᵉ reflᵉ)
        ( is-torsorial-Eq-structureᵉ
          ( is-torsorial-Idᵉ _)
          ( _ ,ᵉ reflᵉ)
          ( is-torsorial-Idᵉ _)))

  abstract
    is-torsorial-is-hom-pointed-map-algebra-Hatcher-Acyclic-Typeᵉ :
      is-torsorialᵉ
        ( λ τᵉ →
          is-hom-pointed-map-algebra-Hatcher-Acyclic-Typeᵉ (Aᵉ ,ᵉ σᵉ) (Bᵉ ,ᵉ τᵉ) fᵉ)
    is-torsorial-is-hom-pointed-map-algebra-Hatcher-Acyclic-Typeᵉ =
      is-contr-equivᵉ
        ( Σᵉ ( structure-Hatcher-Acyclic-Typeᵉ Bᵉ)
            ( λ τᵉ →
              is-hom-pointed-map-algebra-Hatcher-Acyclic-Type'ᵉ
                ( Aᵉ ,ᵉ σᵉ)
                ( Bᵉ ,ᵉ τᵉ)
                ( fᵉ)))
        ( equiv-totᵉ
          ( λ τᵉ →
            equiv-is-hom-pointed-map-algebra-Hatcher-Acyclic-Typeᵉ
              ( Aᵉ ,ᵉ σᵉ)
              ( Bᵉ ,ᵉ τᵉ)
              ( fᵉ)))
        ( is-torsorial-is-hom-pointed-map-algebra-Hatcher-Acyclic-Type'ᵉ)
```

### Characterization of pointed maps out of Hatcher's acyclic type

Forᵉ theᵉ initialᵉ Hatcherᵉ acyclicᵉ algebraᵉ `A`ᵉ andᵉ anyᵉ pointedᵉ typeᵉ `B`,ᵉ weᵉ exhibitᵉ
anᵉ equivalenceᵉ `(Aᵉ →∗ᵉ Bᵉ) ≃ᵉ structure-Hatcher-Acyclic-Typeᵉ B`.ᵉ

Weᵉ firstᵉ showᵉ thatᵉ forᵉ anyᵉ Hatcherᵉ acyclicᵉ algebraᵉ `A`ᵉ (soᵉ notᵉ necessarilyᵉ theᵉ
initialᵉ oneᵉ) andᵉ aᵉ pointedᵉ typeᵉ `B`,ᵉ aᵉ pointedᵉ mapᵉ `fᵉ : Aᵉ →∗ᵉ B`ᵉ inducesᵉ aᵉ
Hatcherᵉ acyclicᵉ structureᵉ onᵉ `B`.ᵉ Moreover,ᵉ with thisᵉ inducedᵉ structure,ᵉ theᵉ mapᵉ
`f`ᵉ becomesᵉ aᵉ homomorphismᵉ ofᵉ Hatcherᵉ acyclicᵉ algebras.ᵉ

```agda
module _
    {l1ᵉ l2ᵉ : Level}
    (Aᵉ : Pointed-Typeᵉ l1ᵉ)
    (Bᵉ : Pointed-Typeᵉ l2ᵉ)
    (σ@(a1ᵉ ,ᵉ a2ᵉ ,ᵉ r1ᵉ ,ᵉ r2ᵉ) : structure-Hatcher-Acyclic-Typeᵉ Aᵉ)
    where

  map-Ω-structure-Hatcher-Acyclic-Typeᵉ :
    (fᵉ : Aᵉ →∗ᵉ Bᵉ) →
    ( power-nat-Ωᵉ 5 Bᵉ (map-Ωᵉ fᵉ a1ᵉ) ＝ᵉ
      power-nat-Ωᵉ 3 Bᵉ (map-Ωᵉ fᵉ a2ᵉ)) ×ᵉ
    ( power-nat-Ωᵉ 3 Bᵉ (map-Ωᵉ fᵉ a2ᵉ) ＝ᵉ
      power-nat-Ωᵉ 2 Bᵉ (mul-Ωᵉ Bᵉ (map-Ωᵉ fᵉ a1ᵉ) (map-Ωᵉ fᵉ a2ᵉ)))
  pr1ᵉ (map-Ω-structure-Hatcher-Acyclic-Typeᵉ fᵉ) =
    invᵉ (map-power-nat-Ωᵉ 5 fᵉ a1ᵉ) ∙ᵉ (apᵉ (map-Ωᵉ fᵉ) r1ᵉ ∙ᵉ map-power-nat-Ωᵉ 3 fᵉ a2ᵉ)
  pr2ᵉ (map-Ω-structure-Hatcher-Acyclic-Typeᵉ fᵉ) =
    invᵉ (map-power-nat-Ωᵉ 3 fᵉ a2ᵉ) ∙ᵉ
    ( apᵉ (map-Ωᵉ fᵉ) r2ᵉ ∙ᵉ
      ( map-power-nat-Ωᵉ 2 fᵉ (a1ᵉ ∙ᵉ a2ᵉ) ∙ᵉ
        apᵉ (power-nat-Ωᵉ 2 Bᵉ) (preserves-mul-map-Ωᵉ fᵉ)))

  structure-Hatcher-Acyclic-Type-pointed-mapᵉ :
    (Aᵉ →∗ᵉ Bᵉ) → structure-Hatcher-Acyclic-Typeᵉ Bᵉ
  pr1ᵉ (structure-Hatcher-Acyclic-Type-pointed-mapᵉ fᵉ) = map-Ωᵉ fᵉ a1ᵉ
  pr1ᵉ (pr2ᵉ (structure-Hatcher-Acyclic-Type-pointed-mapᵉ fᵉ)) = map-Ωᵉ fᵉ a2ᵉ
  (pr2ᵉ (pr2ᵉ (structure-Hatcher-Acyclic-Type-pointed-mapᵉ fᵉ))) =
    map-Ω-structure-Hatcher-Acyclic-Typeᵉ fᵉ

  hom-algebra-Hatcher-Acyclic-Type-pointed-map'ᵉ :
    (fᵉ : Aᵉ →∗ᵉ Bᵉ) →
    is-hom-pointed-map-algebra-Hatcher-Acyclic-Type'ᵉ
      ( Aᵉ ,ᵉ σᵉ)
      ( Bᵉ ,ᵉ structure-Hatcher-Acyclic-Type-pointed-mapᵉ fᵉ)
      ( fᵉ)
  pr1ᵉ (hom-algebra-Hatcher-Acyclic-Type-pointed-map'ᵉ fᵉ) = reflᵉ
  pr1ᵉ (pr2ᵉ (hom-algebra-Hatcher-Acyclic-Type-pointed-map'ᵉ fᵉ)) = reflᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (hom-algebra-Hatcher-Acyclic-Type-pointed-map'ᵉ fᵉ))) =
    ap-binaryᵉ
      ( λ pᵉ qᵉ → invᵉ pᵉ ∙ᵉ (apᵉ (map-Ωᵉ fᵉ) r1ᵉ ∙ᵉ qᵉ))
      ( right-unitᵉ {pᵉ = map-power-nat-Ωᵉ 5 fᵉ a1ᵉ})
      ( right-unitᵉ)
  pr2ᵉ (pr2ᵉ (pr2ᵉ (hom-algebra-Hatcher-Acyclic-Type-pointed-map'ᵉ fᵉ))) =
    ap-binaryᵉ
      ( λ pᵉ qᵉ →
        invᵉ pᵉ ∙ᵉ
        ( apᵉ (map-Ωᵉ fᵉ) r2ᵉ ∙ᵉ
          ( map-power-nat-Ωᵉ 2 fᵉ (a1ᵉ ∙ᵉ a2ᵉ) ∙ᵉ apᵉ (power-nat-Ωᵉ 2 Bᵉ) qᵉ)))
      ( right-unitᵉ {pᵉ = map-power-nat-Ωᵉ 3 fᵉ a2ᵉ})
      ( right-unitᵉ {pᵉ = preserves-mul-map-Ωᵉ fᵉ})

  hom-algebra-Hatcher-Acyclic-Type-pointed-mapᵉ :
    (fᵉ : Aᵉ →∗ᵉ Bᵉ) →
    is-hom-pointed-map-algebra-Hatcher-Acyclic-Typeᵉ
      ( Aᵉ ,ᵉ σᵉ)
      ( Bᵉ ,ᵉ structure-Hatcher-Acyclic-Type-pointed-mapᵉ fᵉ)
      ( fᵉ)
  hom-algebra-Hatcher-Acyclic-Type-pointed-mapᵉ fᵉ =
    map-inv-equivᵉ
      ( equiv-is-hom-pointed-map-algebra-Hatcher-Acyclic-Typeᵉ
        ( Aᵉ ,ᵉ σᵉ)
        ( Bᵉ ,ᵉ structure-Hatcher-Acyclic-Type-pointed-mapᵉ fᵉ)
        ( fᵉ))
      ( hom-algebra-Hatcher-Acyclic-Type-pointed-map'ᵉ fᵉ)

  is-equiv-structure-Hatcher-Acyclic-Type-pointed-mapᵉ :
    is-initial-algebra-Hatcher-Acyclic-Typeᵉ (Aᵉ ,ᵉ σᵉ) →
    is-equivᵉ structure-Hatcher-Acyclic-Type-pointed-mapᵉ
  is-equiv-structure-Hatcher-Acyclic-Type-pointed-mapᵉ iᵉ =
    is-equiv-htpy-equivᵉ
      ( equivalence-reasoningᵉ
          Aᵉ →∗ᵉ Bᵉ
          ≃ᵉ Σᵉ ( Aᵉ →∗ᵉ Bᵉ)
              ( λ fᵉ →
                Σᵉ ( structure-Hatcher-Acyclic-Typeᵉ Bᵉ)
                  ( λ τᵉ →
                    is-hom-pointed-map-algebra-Hatcher-Acyclic-Typeᵉ
                      ( Aᵉ ,ᵉ σᵉ)
                      ( Bᵉ ,ᵉ τᵉ)
                      ( fᵉ)))
            byᵉ inv-right-unit-law-Σ-is-contrᵉ
              ( λ fᵉ →
                is-torsorial-is-hom-pointed-map-algebra-Hatcher-Acyclic-Typeᵉ
                  ( Aᵉ)
                  ( Bᵉ)
                  ( σᵉ)
                  ( fᵉ))
          ≃ᵉ Σᵉ ( structure-Hatcher-Acyclic-Typeᵉ Bᵉ)
              ( λ τᵉ → hom-algebra-Hatcher-Acyclic-Typeᵉ (Aᵉ ,ᵉ σᵉ) (Bᵉ ,ᵉ τᵉ))
            byᵉ equiv-left-swap-Σᵉ
          ≃ᵉ structure-Hatcher-Acyclic-Typeᵉ Bᵉ
            byᵉ equiv-pr1ᵉ (λ τᵉ → iᵉ (Bᵉ ,ᵉ τᵉ)))
      ( λ fᵉ →
        apᵉ
          ( pr1ᵉ)
          ( invᵉ
            ( contractionᵉ
              ( is-torsorial-is-hom-pointed-map-algebra-Hatcher-Acyclic-Typeᵉ Aᵉ Bᵉ
                ( σᵉ)
                ( fᵉ))
              ( structure-Hatcher-Acyclic-Type-pointed-mapᵉ fᵉ ,ᵉ
                hom-algebra-Hatcher-Acyclic-Type-pointed-mapᵉ fᵉ))))

  equiv-pointed-map-Hatcher-Acyclic-Typeᵉ :
    is-initial-algebra-Hatcher-Acyclic-Typeᵉ (Aᵉ ,ᵉ σᵉ) →
    (Aᵉ →∗ᵉ Bᵉ) ≃ᵉ structure-Hatcher-Acyclic-Typeᵉ Bᵉ
  pr1ᵉ (equiv-pointed-map-Hatcher-Acyclic-Typeᵉ iᵉ) =
    structure-Hatcher-Acyclic-Type-pointed-mapᵉ
  pr2ᵉ (equiv-pointed-map-Hatcher-Acyclic-Typeᵉ iᵉ) =
    is-equiv-structure-Hatcher-Acyclic-Type-pointed-mapᵉ iᵉ
```

### Hatcher's acyclic type is acyclic

**Proof:**ᵉ Forᵉ theᵉ Hatcherᵉ acyclicᵉ typeᵉ `A`,ᵉ andᵉ anyᵉ pointedᵉ typeᵉ `X`,ᵉ weᵉ haveᵉ

```text
 (Σᵉ Aᵉ →∗ᵉ Xᵉ) ≃ᵉ (Aᵉ →∗ᵉ Ωᵉ Xᵉ) ≃ᵉ structure-Hatcher-Acyclic-Typeᵉ (Ωᵉ X),ᵉ
```

where theᵉ firstᵉ equivalenceᵉ isᵉ theᵉ
[suspension-loopᵉ spaceᵉ adjunction](synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.md),ᵉ
theᵉ secondᵉ equivalenceᵉ wasᵉ justᵉ provenᵉ above,ᵉ andᵉ theᵉ latterᵉ typeᵉ isᵉ
contractible,ᵉ asᵉ shownᵉ byᵉ `is-contr-structure-Hatcher-Acyclic-Type-Ω`.ᵉ

Hence,ᵉ theᵉ suspensionᵉ `Σᵉ A`ᵉ ofᵉ `A`ᵉ satisfiesᵉ theᵉ
[universalᵉ propertyᵉ ofᵉ contractibleᵉ typesᵉ with respectᵉ to pointedᵉ typesᵉ andᵉ maps](structured-types.pointed-universal-property-contractible-types.md),ᵉ
andᵉ henceᵉ mustᵉ beᵉ contractible.ᵉ

```agda
module _
  {l1ᵉ : Level}
  ((Aᵉ ,ᵉ σᵉ) : algebra-Hatcher-Acyclic-Typeᵉ l1ᵉ)
  where

  is-acyclic-is-initial-algebra-Hatcher-Acyclic-Typeᵉ :
    is-initial-algebra-Hatcher-Acyclic-Typeᵉ (Aᵉ ,ᵉ σᵉ) →
    is-acyclicᵉ (type-Pointed-Typeᵉ Aᵉ)
  is-acyclic-is-initial-algebra-Hatcher-Acyclic-Typeᵉ iᵉ =
    is-contr-universal-property-contr-Pointed-Typeᵉ
      ( suspension-Pointed-Typeᵉ Aᵉ)
      ( λ Xᵉ →
        is-contr-equivᵉ
          ( structure-Hatcher-Acyclic-Typeᵉ (Ωᵉ Xᵉ))
          ( ( equiv-pointed-map-Hatcher-Acyclic-Typeᵉ Aᵉ (Ωᵉ Xᵉ) σᵉ iᵉ) ∘eᵉ
            ( equiv-transpose-suspension-loop-adjunctionᵉ Aᵉ Xᵉ))
          ( is-contr-structure-Hatcher-Acyclic-Type-Ωᵉ Xᵉ))
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}