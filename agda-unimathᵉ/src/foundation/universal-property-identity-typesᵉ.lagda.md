# The universal property of identity types

```agda
module foundation.universal-property-identity-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.full-subtypesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.preunivalenceᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.families-of-equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Theᵉ **universalᵉ propertyᵉ ofᵉ identityᵉ types**ᵉ characterizesᵉ familiesᵉ ofᵉ mapsᵉ outᵉ
ofᵉ theᵉ [identityᵉ type](foundation-core.identity-types.md).ᵉ Thisᵉ universalᵉ
propertyᵉ isᵉ alsoᵉ knownᵉ asᵉ theᵉ **typeᵉ theoreticᵉ Yonedaᵉ lemma**.ᵉ

## Theorem

```agda
ev-reflᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) {Bᵉ : (xᵉ : Aᵉ) → aᵉ ＝ᵉ xᵉ → UUᵉ l2ᵉ} →
  ((xᵉ : Aᵉ) (pᵉ : aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ pᵉ) → Bᵉ aᵉ reflᵉ
ev-reflᵉ aᵉ fᵉ = fᵉ aᵉ reflᵉ

ev-refl'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) {Bᵉ : (xᵉ : Aᵉ) → xᵉ ＝ᵉ aᵉ → UUᵉ l2ᵉ} →
  ((xᵉ : Aᵉ) (pᵉ : xᵉ ＝ᵉ aᵉ) → Bᵉ xᵉ pᵉ) → Bᵉ aᵉ reflᵉ
ev-refl'ᵉ aᵉ fᵉ = fᵉ aᵉ reflᵉ

abstract
  is-equiv-ev-reflᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ)
    {Bᵉ : (xᵉ : Aᵉ) → aᵉ ＝ᵉ xᵉ → UUᵉ l2ᵉ} → is-equivᵉ (ev-reflᵉ aᵉ {Bᵉ})
  is-equiv-ev-reflᵉ aᵉ =
    is-equiv-is-invertibleᵉ
      ( ind-Idᵉ aᵉ _)
      ( λ bᵉ → reflᵉ)
      ( λ fᵉ → eq-htpyᵉ
        ( λ xᵉ → eq-htpyᵉ
          ( ind-Idᵉ aᵉ
            ( λ x'ᵉ p'ᵉ → ind-Idᵉ aᵉ _ (fᵉ aᵉ reflᵉ) x'ᵉ p'ᵉ ＝ᵉ fᵉ x'ᵉ p'ᵉ)
            ( reflᵉ) xᵉ)))

equiv-ev-reflᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) {Bᵉ : (xᵉ : Aᵉ) → aᵉ ＝ᵉ xᵉ → UUᵉ l2ᵉ} →
  ((xᵉ : Aᵉ) (pᵉ : aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ pᵉ) ≃ᵉ (Bᵉ aᵉ reflᵉ)
pr1ᵉ (equiv-ev-reflᵉ aᵉ) = ev-reflᵉ aᵉ
pr2ᵉ (equiv-ev-reflᵉ aᵉ) = is-equiv-ev-reflᵉ aᵉ

equiv-ev-refl'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) {Bᵉ : (xᵉ : Aᵉ) → xᵉ ＝ᵉ aᵉ → UUᵉ l2ᵉ} →
  ((xᵉ : Aᵉ) (pᵉ : xᵉ ＝ᵉ aᵉ) → Bᵉ xᵉ pᵉ) ≃ᵉ Bᵉ aᵉ reflᵉ
equiv-ev-refl'ᵉ aᵉ {Bᵉ} =
  ( equiv-ev-reflᵉ aᵉ) ∘eᵉ
  ( equiv-Π-equiv-familyᵉ (λ xᵉ → equiv-precomp-Πᵉ (equiv-invᵉ aᵉ xᵉ) (Bᵉ xᵉ)))

is-equiv-ev-refl'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ)
  {Bᵉ : (xᵉ : Aᵉ) → xᵉ ＝ᵉ aᵉ → UUᵉ l2ᵉ} → is-equivᵉ (ev-refl'ᵉ aᵉ {Bᵉ})
is-equiv-ev-refl'ᵉ aᵉ = is-equiv-map-equivᵉ (equiv-ev-refl'ᵉ aᵉ)
```

### The type of fiberwise maps from `Id a` to a torsorial type family `B` is equivalent to the type of fiberwise equivalences

Noteᵉ thatᵉ theᵉ typeᵉ ofᵉ fiberwiseᵉ equivalencesᵉ isᵉ aᵉ
[subtype](foundation-core.subtypes.mdᵉ) ofᵉ theᵉ typeᵉ ofᵉ fiberwiseᵉ maps.ᵉ Byᵉ theᵉ
[fundamentalᵉ theoremᵉ ofᵉ identityᵉ types](foundation.fundamental-theorem-of-identity-types.md),ᵉ
itᵉ isᵉ aᵉ [fullᵉ subtype](foundation.full-subtypes.md),ᵉ henceᵉ itᵉ isᵉ equivalentᵉ to
theᵉ wholeᵉ typeᵉ ofᵉ fiberwiseᵉ maps.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (is-torsorial-Bᵉ : is-torsorialᵉ Bᵉ)
  where

  equiv-fam-map-fam-equiv-is-torsorialᵉ :
    ((xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) ≃ᵉ Bᵉ xᵉ) ≃ᵉ ((xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ)
  equiv-fam-map-fam-equiv-is-torsorialᵉ =
    ( equiv-inclusion-is-full-subtypeᵉ
      ( λ hᵉ → Π-Propᵉ Aᵉ (λ aᵉ → is-equiv-Propᵉ (hᵉ aᵉ)))
      ( fundamental-theorem-idᵉ is-torsorial-Bᵉ)) ∘eᵉ
    ( equiv-fiberwise-equiv-fam-equivᵉ _ _)
```

### `Id : A → (A → 𝒰)` is an embedding

Weᵉ firstᵉ showᵉ thatᵉ [theᵉ preunivalenceᵉ axiom](foundation.preunivalence.mdᵉ)
impliesᵉ thatᵉ theᵉ mapᵉ `Idᵉ : Aᵉ → (Aᵉ → 𝒰)`ᵉ isᵉ anᵉ
[embedding](foundation.embeddings.md).ᵉ Sinceᵉ theᵉ
[univalenceᵉ axiom](foundation.univalence.mdᵉ) impliesᵉ preunivalence,ᵉ itᵉ followsᵉ
thatᵉ `Idᵉ : Aᵉ → (Aᵉ → 𝒰)`ᵉ isᵉ anᵉ embeddingᵉ underᵉ theᵉ postulatesᵉ ofᵉ agda-unimath.ᵉ

#### Preunivalence implies that `Id : A → (A → 𝒰)` is an embedding

Theᵉ proofᵉ thatᵉ preunivalenceᵉ impliesᵉ thatᵉ `Idᵉ : Aᵉ → (Aᵉ → 𝒰)`ᵉ isᵉ anᵉ embeddingᵉ
proceedsᵉ viaᵉ theᵉ
[fundamentalᵉ theoremᵉ ofᵉ identityᵉ types](foundation.fundamental-theorem-of-identity-types.mdᵉ)
byᵉ showingᵉ thatᵉ theᵉ [fiber](foundation.fibers-of-maps.mdᵉ) ofᵉ `Id`ᵉ atᵉ `Idᵉ a`ᵉ isᵉ
[contractible](foundation.contractible-types.mdᵉ) forᵉ eachᵉ `aᵉ : A`.ᵉ Toᵉ seeᵉ this,ᵉ
weᵉ firstᵉ noteᵉ thatᵉ thisᵉ fiberᵉ hasᵉ anᵉ elementᵉ `(aᵉ ,ᵉ refl)`.ᵉ Thereforeᵉ itᵉ sufficesᵉ
to showᵉ thatᵉ thisᵉ fiberᵉ isᵉ aᵉ proposition.ᵉ Weᵉ do thisᵉ byᵉ constructingᵉ anᵉ
embeddingᵉ

```text
  fiberᵉ Idᵉ (Idᵉ aᵉ) ↪ᵉ Σᵉ Aᵉ (Idᵉ a).ᵉ
```

Sinceᵉ theᵉ codomainᵉ ofᵉ thisᵉ embeddingᵉ isᵉ contractible,ᵉ theᵉ claimᵉ follows.ᵉ Theᵉ
aboveᵉ embeddingᵉ isᵉ constructedᵉ asᵉ theᵉ compositeᵉ ofᵉ theᵉ followingᵉ embeddingsᵉ

```text
  Σᵉ (xᵉ : A),ᵉ Idᵉ xᵉ ＝ᵉ Idᵉ aᵉ
    ↪ᵉ Σᵉ (xᵉ : A),ᵉ (yᵉ : Aᵉ) → (xᵉ ＝ᵉ yᵉ) ＝ᵉ (aᵉ ＝ᵉ yᵉ)
    ↪ᵉ Σᵉ (xᵉ : A),ᵉ (yᵉ : Aᵉ) → (xᵉ ＝ᵉ yᵉ) ≃ᵉ (aᵉ ＝ᵉ yᵉ)
    ↪ᵉ Σᵉ (xᵉ : A),ᵉ Σᵉ (eᵉ : (yᵉ : Aᵉ) → (xᵉ ＝ᵉ yᵉ) → (aᵉ ＝ᵉ y)),ᵉ (yᵉ : Aᵉ) → is-equivᵉ (eᵉ yᵉ)
    ↪ᵉ Σᵉ (xᵉ : A),ᵉ (yᵉ : Aᵉ) → (xᵉ ＝ᵉ yᵉ) → (aᵉ ＝ᵉ yᵉ)
    ↪ᵉ Σᵉ (xᵉ : A),ᵉ aᵉ ＝ᵉ x.ᵉ
```

Inᵉ thisᵉ composite,ᵉ weᵉ usedᵉ preunivalenceᵉ atᵉ theᵉ secondᵉ step.ᵉ

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  (Lᵉ : (aᵉ xᵉ yᵉ : Aᵉ) → instance-preunivalenceᵉ (Idᵉ xᵉ yᵉ) (Idᵉ aᵉ yᵉ))
  where

  emb-fiber-Id-preunivalent-Idᵉ :
    (aᵉ : Aᵉ) → fiber'ᵉ Idᵉ (Idᵉ aᵉ) ↪ᵉ Σᵉ Aᵉ (Idᵉ aᵉ)
  emb-fiber-Id-preunivalent-Idᵉ aᵉ =
    comp-embᵉ
      ( comp-embᵉ
        ( emb-equivᵉ
          ( equiv-totᵉ
            ( λ xᵉ →
              ( equiv-ev-reflᵉ xᵉ) ∘eᵉ
              ( equiv-fam-map-fam-equiv-is-torsorialᵉ xᵉ (is-torsorial-Idᵉ aᵉ)))))
        ( emb-totᵉ
          ( λ xᵉ →
            comp-embᵉ
              ( emb-Πᵉ (λ yᵉ → _ ,ᵉ Lᵉ aᵉ xᵉ yᵉ))
              ( emb-equivᵉ equiv-funextᵉ))))
      ( emb-equivᵉ (inv-equivᵉ (equiv-fiberᵉ Idᵉ (Idᵉ aᵉ))))

  is-emb-Id-preunivalent-Idᵉ : is-embᵉ (Idᵉ {Aᵉ = Aᵉ})
  is-emb-Id-preunivalent-Idᵉ aᵉ =
    fundamental-theorem-idᵉ
      ( ( aᵉ ,ᵉ reflᵉ) ,ᵉ
        ( λ _ →
          is-injective-embᵉ
            ( emb-fiber-Id-preunivalent-Idᵉ aᵉ)
            ( eq-is-contrᵉ (is-torsorial-Idᵉ aᵉ))))
      ( λ _ → apᵉ Idᵉ)

module _
  (Lᵉ : preunivalence-axiomᵉ) {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  is-emb-Id-preunivalence-axiomᵉ : is-embᵉ (Idᵉ {Aᵉ = Aᵉ})
  is-emb-Id-preunivalence-axiomᵉ =
    is-emb-Id-preunivalent-Idᵉ Aᵉ (λ aᵉ xᵉ yᵉ → Lᵉ (Idᵉ xᵉ yᵉ) (Idᵉ aᵉ yᵉ))
```

#### `Id : A → (A → 𝒰)` is an embedding

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  is-emb-Idᵉ : is-embᵉ (Idᵉ {Aᵉ = Aᵉ})
  is-emb-Idᵉ = is-emb-Id-preunivalence-axiomᵉ preunivalenceᵉ Aᵉ
```

#### For any type family `B` over `A`, the type of pairs `(a , e)` consisting of `a : A` and a family of equivalences `e : (x : A) → (a ＝ x) ≃ B x` is a proposition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  is-proof-irrelevant-total-family-of-equivalences-Idᵉ :
    is-proof-irrelevantᵉ (Σᵉ Aᵉ (λ aᵉ → (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) ≃ᵉ Bᵉ xᵉ))
  is-proof-irrelevant-total-family-of-equivalences-Idᵉ (aᵉ ,ᵉ eᵉ) =
    is-contr-equivᵉ
      ( Σᵉ Aᵉ (λ bᵉ → (xᵉ : Aᵉ) → (bᵉ ＝ᵉ xᵉ) ≃ᵉ (aᵉ ＝ᵉ xᵉ)))
      ( equiv-totᵉ
        ( λ bᵉ →
          equiv-Π-equiv-familyᵉ
            ( λ xᵉ → equiv-postcomp-equivᵉ (inv-equivᵉ (eᵉ xᵉ)) (bᵉ ＝ᵉ xᵉ))))
      ( is-contr-equiv'ᵉ
        ( fiberᵉ Idᵉ (Idᵉ aᵉ))
        ( equiv-totᵉ
          ( λ bᵉ →
            equiv-Π-equiv-familyᵉ (λ xᵉ → equiv-univalenceᵉ) ∘eᵉ equiv-funextᵉ))
        ( is-proof-irrelevant-is-propᵉ
          ( is-prop-map-is-embᵉ (is-emb-Idᵉ Aᵉ) (Idᵉ aᵉ))
          ( aᵉ ,ᵉ reflᵉ)))

  is-prop-total-family-of-equivalences-Idᵉ :
    is-propᵉ (Σᵉ Aᵉ (λ aᵉ → (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) ≃ᵉ Bᵉ xᵉ))
  is-prop-total-family-of-equivalences-Idᵉ =
    is-prop-is-proof-irrelevantᵉ
      ( is-proof-irrelevant-total-family-of-equivalences-Idᵉ)
```

### The type of point-preserving fiberwise equivalences between `Id x` and a pointed torsorial type family is contractible

**Proof:**ᵉ Sinceᵉ `ev-refl`ᵉ isᵉ anᵉ equivalence,ᵉ itᵉ followsᵉ thatᵉ itsᵉ fibersᵉ areᵉ
contractible.ᵉ Explicitly,ᵉ givenᵉ aᵉ pointᵉ `bᵉ : Bᵉ a`,ᵉ theᵉ typeᵉ ofᵉ mapsᵉ
`hᵉ : (xᵉ : Aᵉ) → (aᵉ = xᵉ) → Bᵉ x`ᵉ suchᵉ thatᵉ `hᵉ aᵉ reflᵉ = b`ᵉ isᵉ contractible.ᵉ Butᵉ theᵉ
typeᵉ ofᵉ fiberwiseᵉ mapsᵉ isᵉ equivalentᵉ to theᵉ typeᵉ ofᵉ fiberwiseᵉ equivalences.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {aᵉ : Aᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (bᵉ : Bᵉ aᵉ)
  (is-torsorial-Bᵉ : is-torsorialᵉ Bᵉ)
  where

  abstract
    is-torsorial-pointed-fam-equiv-is-torsorialᵉ :
      is-torsorialᵉ
        ( λ (eᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) ≃ᵉ Bᵉ xᵉ) →
          map-equivᵉ (eᵉ aᵉ) reflᵉ ＝ᵉ bᵉ)
    is-torsorial-pointed-fam-equiv-is-torsorialᵉ =
      is-contr-equiv'ᵉ
        ( fiberᵉ (ev-reflᵉ aᵉ {Bᵉ = λ xᵉ _ → Bᵉ xᵉ}) bᵉ)
        ( equiv-Σᵉ _
          ( inv-equivᵉ
            ( equiv-fam-map-fam-equiv-is-torsorialᵉ aᵉ is-torsorial-Bᵉ))
          ( λ hᵉ →
            equiv-inv-concatᵉ
              ( invᵉ
                ( apᵉ
                  ( ev-reflᵉ aᵉ)
                  ( is-section-map-inv-equivᵉ
                    ( equiv-fam-map-fam-equiv-is-torsorialᵉ aᵉ is-torsorial-Bᵉ)
                    ( hᵉ))))
              ( bᵉ)))
        ( is-contr-map-is-equivᵉ
          ( is-equiv-ev-reflᵉ aᵉ)
          ( bᵉ))
```

## See also

-ᵉ Inᵉ
  [`foundation.torsorial-type-families`](foundation.torsorial-type-families.mdᵉ)
  weᵉ willᵉ showᵉ thatᵉ theᵉ fiberᵉ ofᵉ `Idᵉ : Aᵉ → (Aᵉ → 𝒰)`ᵉ atᵉ `Bᵉ : Aᵉ → 𝒰`ᵉ isᵉ equivalentᵉ
  to `is-torsorialᵉ B`.ᵉ

## References

-ᵉ Theᵉ factᵉ thatᵉ preunivalence,ᵉ orᵉ axiomᵉ L,ᵉ isᵉ sufficientᵉ to proveᵉ thatᵉ
  `Idᵉ : Aᵉ → (Aᵉ → 𝒰)`ᵉ isᵉ anᵉ embeddingᵉ wasᵉ firstᵉ observedᵉ andᵉ formalizedᵉ byᵉ Martínᵉ
  Escardó,ᵉ
  [https://www.cs.bham.ac.uk//~mhe/TypeTopology/UF.IdEmbedding.html](https://www.cs.bham.ac.uk//~mhe/TypeTopology/UF.IdEmbedding.html).ᵉ

{{#bibliographyᵉ}} {{#referenceᵉ TypeTopologyᵉ}}