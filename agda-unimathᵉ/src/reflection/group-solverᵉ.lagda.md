# Group solver

```agda
module reflection.group-solverᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ

open import linear-algebra.vectorsᵉ

open import lists.concatenation-listsᵉ
open import lists.functoriality-listsᵉ
open import lists.listsᵉ
open import lists.reversing-listsᵉ
```

</details>

## Idea

Thisᵉ module simplifiesᵉ groupᵉ expressions,ᵉ suchᵉ thatᵉ allᵉ itemsᵉ associateᵉ theᵉ sameᵉ
wayᵉ andᵉ removesᵉ unitsᵉ andᵉ inversesᵉ nextᵉ to theᵉ original.ᵉ

Theᵉ mainᵉ entry-pointᵉ isᵉ `solveExpr`ᵉ belowᵉ

```agda
data Inductive-Finᵉ : ℕᵉ → UUᵉ lzero where
  zero-Inductive-Finᵉ : {nᵉ : ℕᵉ} → Inductive-Finᵉ (succ-ℕᵉ nᵉ)
  succ-Inductive-Finᵉ : {nᵉ : ℕᵉ} → Inductive-Finᵉ nᵉ → Inductive-Finᵉ (succ-ℕᵉ nᵉ)

finEqᵉ : {nᵉ : ℕᵉ} → (aᵉ bᵉ : Inductive-Finᵉ nᵉ) → is-decidableᵉ (Idᵉ aᵉ bᵉ)
finEqᵉ zero-Inductive-Finᵉ zero-Inductive-Finᵉ = inlᵉ reflᵉ
finEqᵉ zero-Inductive-Finᵉ (succ-Inductive-Finᵉ bᵉ) = inrᵉ (λ ())
finEqᵉ (succ-Inductive-Finᵉ aᵉ) zero-Inductive-Finᵉ = inrᵉ (λ ())
finEqᵉ (succ-Inductive-Finᵉ aᵉ) (succ-Inductive-Finᵉ bᵉ) with finEqᵉ aᵉ bᵉ
... | inlᵉ eqᵉ = inlᵉ (apᵉ succ-Inductive-Finᵉ eqᵉ)
... | inrᵉ neqᵉ = inrᵉ (λ where reflᵉ → neqᵉ reflᵉ)

getVecᵉ : {nᵉ : ℕᵉ} {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → vecᵉ Aᵉ nᵉ → Inductive-Finᵉ nᵉ → Aᵉ
getVecᵉ (xᵉ ∷ᵉ vᵉ) zero-Inductive-Finᵉ = xᵉ
getVecᵉ (xᵉ ∷ᵉ vᵉ) (succ-Inductive-Finᵉ kᵉ) = getVecᵉ vᵉ kᵉ

data GroupSyntaxᵉ (nᵉ : ℕᵉ) : UUᵉ where
  gUnitᵉ : GroupSyntaxᵉ nᵉ
  gMulᵉ : GroupSyntaxᵉ nᵉ → GroupSyntaxᵉ nᵉ → GroupSyntaxᵉ nᵉ
  gInvᵉ : GroupSyntaxᵉ nᵉ → GroupSyntaxᵉ nᵉ
  innerᵉ : Inductive-Finᵉ nᵉ → GroupSyntaxᵉ nᵉ

data SimpleElemᵉ (nᵉ : ℕᵉ) : UUᵉ where
  inv-SEᵉ : Inductive-Finᵉ nᵉ → SimpleElemᵉ nᵉ
  pure-SEᵉ : Inductive-Finᵉ nᵉ → SimpleElemᵉ nᵉ

inv-SE'ᵉ : {nᵉ : ℕᵉ} → SimpleElemᵉ nᵉ → SimpleElemᵉ nᵉ
inv-SE'ᵉ (inv-SEᵉ kᵉ) = pure-SEᵉ kᵉ
inv-SE'ᵉ (pure-SEᵉ kᵉ) = inv-SEᵉ kᵉ

Simpleᵉ : (nᵉ : ℕᵉ) → UUᵉ
Simpleᵉ nᵉ = listᵉ (SimpleElemᵉ nᵉ)

module _ {nᵉ : ℕᵉ} where
  unquoteSimpleElemᵉ : SimpleElemᵉ nᵉ → GroupSyntaxᵉ nᵉ
  unquoteSimpleElemᵉ (inv-SEᵉ xᵉ) = gInvᵉ (innerᵉ xᵉ)
  unquoteSimpleElemᵉ (pure-SEᵉ xᵉ) = innerᵉ xᵉ

  unquoteSimpleNonEmptyᵉ : Simpleᵉ nᵉ → GroupSyntaxᵉ nᵉ → GroupSyntaxᵉ nᵉ
  unquoteSimpleNonEmptyᵉ nilᵉ xᵉ = xᵉ
  unquoteSimpleNonEmptyᵉ (consᵉ yᵉ xsᵉ) xᵉ =
    gMulᵉ (unquoteSimpleNonEmptyᵉ xsᵉ (unquoteSimpleElemᵉ yᵉ)) xᵉ

  unquoteSimpleᵉ : Simpleᵉ nᵉ → GroupSyntaxᵉ nᵉ
  unquoteSimpleᵉ nilᵉ = gUnitᵉ
  unquoteSimpleᵉ (consᵉ xᵉ xsᵉ) = unquoteSimpleNonEmptyᵉ xsᵉ (unquoteSimpleElemᵉ xᵉ)

  elim-inversesᵉ : SimpleElemᵉ nᵉ → Simpleᵉ nᵉ → Simpleᵉ nᵉ
  elim-inversesᵉ xᵉ nilᵉ = consᵉ xᵉ nilᵉ
  elim-inversesᵉ xi@(inv-SEᵉ xᵉ) yxs@(consᵉ (inv-SEᵉ yᵉ) xsᵉ) = consᵉ xiᵉ yxsᵉ
  elim-inversesᵉ xi@(inv-SEᵉ xᵉ) yxs@(consᵉ (pure-SEᵉ yᵉ) xsᵉ) with finEqᵉ xᵉ yᵉ
  ... | inlᵉ eqᵉ = xsᵉ
  ... | inrᵉ neqᵉ = consᵉ xiᵉ yxsᵉ
  elim-inversesᵉ xi@(pure-SEᵉ xᵉ) yxs@(consᵉ (inv-SEᵉ yᵉ) xsᵉ) with finEqᵉ xᵉ yᵉ
  ... | inlᵉ eqᵉ = xsᵉ
  ... | inrᵉ neqᵉ = consᵉ xiᵉ yxsᵉ
  elim-inversesᵉ xi@(pure-SEᵉ xᵉ) yxs@(consᵉ (pure-SEᵉ yᵉ) xsᵉ) = consᵉ xiᵉ yxsᵉ

  concat-simplifyᵉ : Simpleᵉ nᵉ → Simpleᵉ nᵉ → Simpleᵉ nᵉ
  concat-simplifyᵉ nilᵉ bᵉ = bᵉ
  concat-simplifyᵉ (consᵉ xᵉ aᵉ) bᵉ = elim-inversesᵉ xᵉ (concat-simplifyᵉ aᵉ bᵉ)

  simplifyGSᵉ : GroupSyntaxᵉ nᵉ → Simpleᵉ nᵉ
  simplifyGSᵉ gUnitᵉ = nilᵉ
  simplifyGSᵉ (gMulᵉ aᵉ bᵉ) = concat-simplifyᵉ (simplifyGSᵉ bᵉ) (simplifyGSᵉ aᵉ)
  simplifyGSᵉ (gInvᵉ aᵉ) = reverse-listᵉ (map-listᵉ inv-SE'ᵉ (simplifyGSᵉ aᵉ))
  --ᵉ simplifyGSᵉ (gInvᵉ aᵉ) = map-listᵉ inv-SE'ᵉ (reverse-listᵉ (simplifyGSᵉ aᵉ))
  simplifyGSᵉ (innerᵉ nᵉ) = consᵉ (pure-SEᵉ nᵉ) nilᵉ

  data GroupEqualityElemᵉ : GroupSyntaxᵉ nᵉ → GroupSyntaxᵉ nᵉ → UUᵉ where
    --ᵉ equivalenceᵉ relationᵉ
    xsym-GEᵉ :
      {xᵉ yᵉ : GroupSyntaxᵉ nᵉ} → GroupEqualityElemᵉ xᵉ yᵉ → GroupEqualityElemᵉ yᵉ xᵉ

    --ᵉ Variationsᵉ onᵉ apᵉ
    --ᵉ xap-gMulᵉ :
    --ᵉ   {xᵉ yᵉ zᵉ wᵉ : GroupSyntaxᵉ nᵉ} →
    --ᵉ   GroupEqualityElemᵉ xᵉ yᵉ → GroupEqualityElemᵉ zᵉ wᵉ →
    --ᵉ   GroupEqualityElemᵉ (gMulᵉ xᵉ zᵉ) (gMulᵉ yᵉ wᵉ)
    xap-gMul-lᵉ :
      {xᵉ yᵉ zᵉ : GroupSyntaxᵉ nᵉ} →
      GroupEqualityElemᵉ xᵉ yᵉ → GroupEqualityElemᵉ (gMulᵉ xᵉ zᵉ) (gMulᵉ yᵉ zᵉ)
    xap-gMul-rᵉ :
      {xᵉ yᵉ zᵉ : GroupSyntaxᵉ nᵉ} →
      GroupEqualityElemᵉ yᵉ zᵉ → GroupEqualityElemᵉ (gMulᵉ xᵉ yᵉ) (gMulᵉ xᵉ zᵉ)
    xap-gInvᵉ :
      {xᵉ yᵉ : GroupSyntaxᵉ nᵉ} →
      GroupEqualityElemᵉ xᵉ yᵉ → GroupEqualityElemᵉ (gInvᵉ xᵉ) (gInvᵉ yᵉ)

    --ᵉ Groupᵉ lawsᵉ
    xassoc-GEᵉ :
      (xᵉ yᵉ zᵉ : GroupSyntaxᵉ nᵉ) →
      GroupEqualityElemᵉ (gMulᵉ (gMulᵉ xᵉ yᵉ) zᵉ) (gMulᵉ xᵉ (gMulᵉ yᵉ zᵉ))
    xl-unitᵉ :
      (xᵉ : GroupSyntaxᵉ nᵉ) → GroupEqualityElemᵉ (gMulᵉ gUnitᵉ xᵉ) xᵉ
    xr-unitᵉ :
      (xᵉ : GroupSyntaxᵉ nᵉ) → GroupEqualityElemᵉ (gMulᵉ xᵉ gUnitᵉ) xᵉ
    xl-invᵉ :
      (xᵉ : GroupSyntaxᵉ nᵉ) → GroupEqualityElemᵉ (gMulᵉ (gInvᵉ xᵉ) xᵉ) gUnitᵉ
    xr-invᵉ :
      (xᵉ : GroupSyntaxᵉ nᵉ) → GroupEqualityElemᵉ (gMulᵉ xᵉ (gInvᵉ xᵉ)) gUnitᵉ

    --ᵉ Theoremsᵉ thatᵉ areᵉ provableᵉ fromᵉ theᵉ othersᵉ
    xinv-unit-GEᵉ :
      GroupEqualityElemᵉ (gInvᵉ gUnitᵉ) gUnitᵉ
    xinv-inv-GEᵉ :
      (xᵉ : GroupSyntaxᵉ nᵉ) → GroupEqualityElemᵉ (gInvᵉ (gInvᵉ xᵉ)) xᵉ
    xdistr-inv-mul-GEᵉ :
      (xᵉ yᵉ : GroupSyntaxᵉ nᵉ) →
      GroupEqualityElemᵉ (gInvᵉ (gMulᵉ xᵉ yᵉ)) (gMulᵉ (gInvᵉ yᵉ) (gInvᵉ xᵉ))

  data GroupEqualityᵉ : GroupSyntaxᵉ nᵉ → GroupSyntaxᵉ nᵉ → UUᵉ where
    refl-GEᵉ :
      {xᵉ : GroupSyntaxᵉ nᵉ} → GroupEqualityᵉ xᵉ xᵉ
    _∷GEᵉ_ :
      {xᵉ yᵉ zᵉ : GroupSyntaxᵉ nᵉ} →
      GroupEqualityElemᵉ xᵉ yᵉ → GroupEqualityᵉ yᵉ zᵉ → GroupEqualityᵉ xᵉ zᵉ

  infixr 10 _∷GEᵉ_

  module _ where
    --ᵉ equivalenceᵉ relationᵉ
    singleton-GEᵉ :
      {xᵉ yᵉ : GroupSyntaxᵉ nᵉ} → GroupEqualityElemᵉ xᵉ yᵉ → GroupEqualityᵉ xᵉ yᵉ
    singleton-GEᵉ xᵉ = xᵉ ∷GEᵉ refl-GEᵉ

    _∙GEᵉ_ :
      {xᵉ yᵉ zᵉ : GroupSyntaxᵉ nᵉ} →
      GroupEqualityᵉ xᵉ yᵉ → GroupEqualityᵉ yᵉ zᵉ → GroupEqualityᵉ xᵉ zᵉ
    refl-GEᵉ ∙GEᵉ bᵉ = bᵉ
    (xᵉ ∷GEᵉ aᵉ) ∙GEᵉ bᵉ = xᵉ ∷GEᵉ (aᵉ ∙GEᵉ bᵉ)
    infixr 15 _∙GEᵉ_

    sym-GEᵉ : {xᵉ yᵉ : GroupSyntaxᵉ nᵉ} → GroupEqualityᵉ xᵉ yᵉ → GroupEqualityᵉ yᵉ xᵉ
    sym-GEᵉ refl-GEᵉ = refl-GEᵉ
    sym-GEᵉ (aᵉ ∷GEᵉ asᵉ) = sym-GEᵉ asᵉ ∙GEᵉ singleton-GEᵉ (xsym-GEᵉ aᵉ)

    --ᵉ Variationsᵉ onᵉ apᵉ
    ap-gInvᵉ :
      {xᵉ yᵉ : GroupSyntaxᵉ nᵉ} →
      GroupEqualityᵉ xᵉ yᵉ → GroupEqualityᵉ (gInvᵉ xᵉ) (gInvᵉ yᵉ)
    ap-gInvᵉ refl-GEᵉ = refl-GEᵉ
    ap-gInvᵉ (aᵉ ∷GEᵉ asᵉ) = xap-gInvᵉ aᵉ ∷GEᵉ ap-gInvᵉ asᵉ

    ap-gMul-lᵉ :
      {xᵉ yᵉ zᵉ : GroupSyntaxᵉ nᵉ} →
      GroupEqualityᵉ xᵉ yᵉ → GroupEqualityᵉ (gMulᵉ xᵉ zᵉ) (gMulᵉ yᵉ zᵉ)
    ap-gMul-lᵉ refl-GEᵉ = refl-GEᵉ
    ap-gMul-lᵉ (xᵉ ∷GEᵉ xsᵉ) = xap-gMul-lᵉ xᵉ ∷GEᵉ ap-gMul-lᵉ xsᵉ

    ap-gMul-rᵉ :
      {xᵉ yᵉ zᵉ : GroupSyntaxᵉ nᵉ} →
      GroupEqualityᵉ yᵉ zᵉ → GroupEqualityᵉ (gMulᵉ xᵉ yᵉ) (gMulᵉ xᵉ zᵉ)
    ap-gMul-rᵉ refl-GEᵉ = refl-GEᵉ
    ap-gMul-rᵉ (xᵉ ∷GEᵉ xsᵉ) = xap-gMul-rᵉ xᵉ ∷GEᵉ ap-gMul-rᵉ xsᵉ

    ap-gMulᵉ :
      {xᵉ yᵉ zᵉ wᵉ : GroupSyntaxᵉ nᵉ} →
      GroupEqualityᵉ xᵉ yᵉ → GroupEqualityᵉ zᵉ wᵉ →
      GroupEqualityᵉ (gMulᵉ xᵉ zᵉ) (gMulᵉ yᵉ wᵉ)
    ap-gMulᵉ pᵉ qᵉ = ap-gMul-lᵉ pᵉ ∙GEᵉ ap-gMul-rᵉ qᵉ

    --ᵉ Groupᵉ lawsᵉ
    assoc-GEᵉ :
      (xᵉ yᵉ zᵉ : GroupSyntaxᵉ nᵉ) →
      GroupEqualityᵉ (gMulᵉ (gMulᵉ xᵉ yᵉ) zᵉ) (gMulᵉ xᵉ (gMulᵉ yᵉ zᵉ))
    assoc-GEᵉ xᵉ yᵉ zᵉ = singleton-GEᵉ (xassoc-GEᵉ xᵉ yᵉ zᵉ)

    l-unitᵉ :
      (xᵉ : GroupSyntaxᵉ nᵉ) → GroupEqualityᵉ (gMulᵉ gUnitᵉ xᵉ) xᵉ
    l-unitᵉ xᵉ = singleton-GEᵉ (xl-unitᵉ xᵉ)

    r-unitᵉ :
      (xᵉ : GroupSyntaxᵉ nᵉ) → GroupEqualityᵉ (gMulᵉ xᵉ gUnitᵉ) xᵉ
    r-unitᵉ xᵉ = singleton-GEᵉ (xr-unitᵉ xᵉ)

    l-invᵉ :
      (xᵉ : GroupSyntaxᵉ nᵉ) → GroupEqualityᵉ (gMulᵉ (gInvᵉ xᵉ) xᵉ) gUnitᵉ
    l-invᵉ xᵉ = singleton-GEᵉ (xl-invᵉ xᵉ)

    r-invᵉ :
      (xᵉ : GroupSyntaxᵉ nᵉ) → GroupEqualityᵉ (gMulᵉ xᵉ (gInvᵉ xᵉ)) gUnitᵉ
    r-invᵉ xᵉ = singleton-GEᵉ (xr-invᵉ xᵉ)

    --ᵉ Theoremsᵉ thatᵉ areᵉ provableᵉ fromᵉ theᵉ othersᵉ
    inv-unit-GEᵉ : GroupEqualityᵉ (gInvᵉ gUnitᵉ) gUnitᵉ
    inv-unit-GEᵉ = singleton-GEᵉ (xinv-unit-GEᵉ)

    inv-inv-GEᵉ : (xᵉ : GroupSyntaxᵉ nᵉ) → GroupEqualityᵉ (gInvᵉ (gInvᵉ xᵉ)) xᵉ
    inv-inv-GEᵉ xᵉ = singleton-GEᵉ (xinv-inv-GEᵉ xᵉ)

    distr-inv-mul-GEᵉ :
      (xᵉ yᵉ : GroupSyntaxᵉ nᵉ) →
      GroupEqualityᵉ (gInvᵉ (gMulᵉ xᵉ yᵉ)) (gMulᵉ (gInvᵉ yᵉ) (gInvᵉ xᵉ))
    distr-inv-mul-GEᵉ xᵉ yᵉ = singleton-GEᵉ (xdistr-inv-mul-GEᵉ xᵉ yᵉ)

  assoc-GE'ᵉ :
    (xᵉ yᵉ zᵉ : GroupSyntaxᵉ nᵉ) →
    GroupEqualityᵉ (gMulᵉ xᵉ (gMulᵉ yᵉ zᵉ)) (gMulᵉ (gMulᵉ xᵉ yᵉ) zᵉ)
  assoc-GE'ᵉ xᵉ yᵉ zᵉ = sym-GEᵉ (assoc-GEᵉ xᵉ yᵉ zᵉ)

  elim-inverses-remove-validᵉ :
    (bᵉ : listᵉ (SimpleElemᵉ nᵉ)) (wᵉ uᵉ : GroupSyntaxᵉ nᵉ) →
    GroupEqualityᵉ (gMulᵉ wᵉ uᵉ) gUnitᵉ →
    GroupEqualityᵉ
      ( gMulᵉ (unquoteSimpleNonEmptyᵉ bᵉ wᵉ) uᵉ)
      ( unquoteSimpleᵉ bᵉ)
  elim-inverses-remove-validᵉ nilᵉ wᵉ uᵉ eqᵉ = eqᵉ
  elim-inverses-remove-validᵉ (consᵉ xᵉ bᵉ) wᵉ uᵉ eqᵉ =
    assoc-GEᵉ _ _ _ ∙GEᵉ
    ap-gMul-rᵉ eqᵉ ∙GEᵉ
    r-unitᵉ _

  elim-inverses-validᵉ :
    (xᵉ : SimpleElemᵉ nᵉ) (bᵉ : Simpleᵉ nᵉ) →
    GroupEqualityᵉ
      ( gMulᵉ (unquoteSimpleᵉ bᵉ) (unquoteSimpleElemᵉ xᵉ))
      ( unquoteSimpleᵉ (elim-inversesᵉ xᵉ bᵉ))
  elim-inverses-validᵉ xᵉ nilᵉ = l-unitᵉ (unquoteSimpleElemᵉ xᵉ)
  elim-inverses-validᵉ (inv-SEᵉ xᵉ) (consᵉ (inv-SEᵉ yᵉ) bᵉ) = refl-GEᵉ
  elim-inverses-validᵉ (inv-SEᵉ xᵉ) (consᵉ (pure-SEᵉ yᵉ) bᵉ) with finEqᵉ xᵉ yᵉ
  ... | inlᵉ reflᵉ =
    elim-inverses-remove-validᵉ bᵉ (innerᵉ xᵉ) (gInvᵉ (innerᵉ xᵉ)) (r-invᵉ (innerᵉ xᵉ))
  ... | inrᵉ neqᵉ = refl-GEᵉ
  elim-inverses-validᵉ (pure-SEᵉ xᵉ) (consᵉ (inv-SEᵉ yᵉ) bᵉ) with finEqᵉ xᵉ yᵉ
  ... | inlᵉ reflᵉ =
    elim-inverses-remove-validᵉ bᵉ (gInvᵉ (innerᵉ xᵉ)) (innerᵉ xᵉ) (l-invᵉ (innerᵉ xᵉ))
  ... | inrᵉ neqᵉ = refl-GEᵉ
  elim-inverses-validᵉ (pure-SEᵉ xᵉ) (consᵉ (pure-SEᵉ yᵉ) bᵉ) = refl-GEᵉ

  concat-simplify-nonempty-validᵉ :
    (xᵉ : SimpleElemᵉ nᵉ) (aᵉ : listᵉ (SimpleElemᵉ nᵉ)) (bᵉ : Simpleᵉ nᵉ) →
    GroupEqualityᵉ
      ( gMulᵉ (unquoteSimpleᵉ bᵉ) (unquoteSimpleᵉ (consᵉ xᵉ aᵉ)))
      ( unquoteSimpleᵉ (concat-simplifyᵉ (consᵉ xᵉ aᵉ) bᵉ))
  concat-simplify-nonempty-validᵉ xᵉ nilᵉ bᵉ = elim-inverses-validᵉ xᵉ bᵉ
  concat-simplify-nonempty-validᵉ xᵉ (consᵉ yᵉ aᵉ) bᵉ =
    assoc-GE'ᵉ _ _ _ ∙GEᵉ
    ap-gMul-lᵉ (concat-simplify-nonempty-validᵉ yᵉ aᵉ bᵉ) ∙GEᵉ
    elim-inverses-validᵉ xᵉ (elim-inversesᵉ yᵉ (concat-simplifyᵉ aᵉ bᵉ))

  concat-simplify-validᵉ :
    (uᵉ wᵉ : Simpleᵉ nᵉ) →
    GroupEqualityᵉ
      ( gMulᵉ (unquoteSimpleᵉ wᵉ) (unquoteSimpleᵉ uᵉ))
      ( unquoteSimpleᵉ (concat-simplifyᵉ uᵉ wᵉ))
  concat-simplify-validᵉ nilᵉ bᵉ = r-unitᵉ (unquoteSimpleᵉ bᵉ)
  concat-simplify-validᵉ (consᵉ xᵉ aᵉ) bᵉ = concat-simplify-nonempty-validᵉ xᵉ aᵉ bᵉ

  inv-single-validᵉ :
    (wᵉ : SimpleElemᵉ nᵉ) →
    GroupEqualityᵉ
      ( gInvᵉ (unquoteSimpleElemᵉ wᵉ))
      ( unquoteSimpleElemᵉ (inv-SE'ᵉ wᵉ))
  inv-single-validᵉ (inv-SEᵉ xᵉ) = inv-inv-GEᵉ (innerᵉ xᵉ)
  inv-single-validᵉ (pure-SEᵉ xᵉ) = refl-GEᵉ

  gMul-concat-nonemptyᵉ :
    (wᵉ : GroupSyntaxᵉ nᵉ) (asᵉ bᵉ : Simpleᵉ nᵉ) →
    GroupEqualityᵉ
      ( gMulᵉ (unquoteSimpleᵉ bᵉ) (unquoteSimpleNonEmptyᵉ asᵉ wᵉ))
      ( unquoteSimpleNonEmptyᵉ (concat-listᵉ asᵉ bᵉ) wᵉ)
  gMul-concat-nonemptyᵉ wᵉ nilᵉ nilᵉ = l-unitᵉ wᵉ
  gMul-concat-nonemptyᵉ wᵉ nilᵉ (consᵉ xᵉ bᵉ) = refl-GEᵉ
  gMul-concat-nonemptyᵉ wᵉ (consᵉ xᵉ asᵉ) bᵉ =
    assoc-GE'ᵉ _ _ _ ∙GEᵉ
    ap-gMul-lᵉ (gMul-concat-nonemptyᵉ (unquoteSimpleElemᵉ xᵉ) asᵉ bᵉ)

  gMul-concat'ᵉ :
    (xsᵉ : Simpleᵉ nᵉ) (ysᵉ : Simpleᵉ nᵉ) →
    GroupEqualityᵉ
      ( gMulᵉ (unquoteSimpleᵉ ysᵉ) (unquoteSimpleᵉ xsᵉ))
      ( unquoteSimpleᵉ (concat-listᵉ xsᵉ ysᵉ))
  gMul-concat'ᵉ nilᵉ bsᵉ = r-unitᵉ _
  gMul-concat'ᵉ (consᵉ xᵉ asᵉ) bᵉ = gMul-concat-nonemptyᵉ (unquoteSimpleElemᵉ xᵉ) asᵉ bᵉ

  gMul-concat-1ᵉ :
    (xsᵉ : Simpleᵉ nᵉ) (xᵉ : SimpleElemᵉ nᵉ) →
    GroupEqualityᵉ
      ( gMulᵉ (unquoteSimpleElemᵉ xᵉ) (unquoteSimpleᵉ xsᵉ))
      ( unquoteSimpleᵉ (concat-listᵉ xsᵉ (consᵉ xᵉ nilᵉ)))
  gMul-concat-1ᵉ xsᵉ aᵉ = gMul-concat'ᵉ xsᵉ (consᵉ aᵉ nilᵉ)

  --ᵉ inv-simplify-valid'-nonemptyᵉ : (xᵉ : SimpleElemᵉ nᵉ) (xsᵉ : listᵉ (SimpleElemᵉ nᵉ)) →
  --ᵉ                               GroupEqualityᵉ (gInvᵉ (unquoteSimpleᵉ (consᵉ xᵉ xsᵉ)))
  --ᵉ                               (unquoteSimpleᵉ (reverse-listᵉ (map-listᵉ inv-SE'ᵉ (consᵉ xᵉ xsᵉ))))
  --ᵉ inv-simplify-valid'-nonemptyᵉ xᵉ nilᵉ = inv-single-validᵉ xᵉ
  --ᵉ inv-simplify-valid'-nonemptyᵉ xᵉ (consᵉ yᵉ xsᵉ) =
  --ᵉ   distr-inv-mul-GEᵉ (unquoteSimpleᵉ (consᵉ yᵉ xsᵉ)) (unquoteSimpleElemᵉ xᵉ) ∙GEᵉ
  --ᵉ   ap-gMulᵉ (inv-single-validᵉ xᵉ) (inv-simplify-valid'-nonemptyᵉ yᵉ xsᵉ) ∙GEᵉ
  --ᵉ   gMul-concat-1ᵉ (concat-listᵉ (reverse-listᵉ (map-listᵉ inv-SE'ᵉ xsᵉ)) (in-listᵉ (inv-SE'ᵉ yᵉ))) (inv-SE'ᵉ xᵉ)

  --ᵉ inv-simplify-valid'ᵉ : (wᵉ : listᵉ (SimpleElemᵉ nᵉ)) →
  --ᵉ                     GroupEqualityᵉ (gInvᵉ (unquoteSimpleᵉ wᵉ))
  --ᵉ                     (unquoteSimpleᵉ (reverse-listᵉ (map-listᵉ inv-SE'ᵉ wᵉ)))
  --ᵉ inv-simplify-valid'ᵉ nilᵉ = inv-unit-GEᵉ
  --ᵉ inv-simplify-valid'ᵉ (consᵉ xᵉ xsᵉ) =
  --ᵉ   inv-simplify-valid'-nonemptyᵉ xᵉ xsᵉ

  --ᵉ simplifyValidᵉ : (gᵉ : GroupSyntaxᵉ nᵉ) → GroupEqualityᵉ gᵉ (unquoteSimpleᵉ (simplifyGSᵉ gᵉ))
  --ᵉ simplifyValidᵉ gUnitᵉ = refl-GEᵉ
  --ᵉ simplifyValidᵉ (gMulᵉ aᵉ bᵉ) =
  --ᵉ   (ap-gMulᵉ (simplifyValidᵉ aᵉ) (simplifyValidᵉ bᵉ)) ∙GEᵉ
  --ᵉ   (concat-simplify-validᵉ (simplifyGSᵉ bᵉ) (simplifyGSᵉ aᵉ))
  --ᵉ simplifyValidᵉ (gInvᵉ gᵉ) = ap-gInvᵉ (simplifyValidᵉ gᵉ) ∙GEᵉ inv-simplify-valid'ᵉ (simplifyGSᵉ gᵉ)
  --ᵉ simplifyValidᵉ (innerᵉ _) = refl-GEᵉ

  Envᵉ : {lᵉ : Level} → ℕᵉ → UUᵉ lᵉ → UUᵉ lᵉ
  Envᵉ nᵉ Aᵉ = vecᵉ Aᵉ nᵉ

  module _
    {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
    where

    unQuoteGSᵉ : {nᵉ : ℕᵉ} → GroupSyntaxᵉ nᵉ → Envᵉ nᵉ (type-Groupᵉ Gᵉ) → type-Groupᵉ Gᵉ
    unQuoteGSᵉ gUnitᵉ eᵉ = unit-Groupᵉ Gᵉ
    unQuoteGSᵉ (gMulᵉ xᵉ yᵉ) eᵉ = mul-Groupᵉ Gᵉ (unQuoteGSᵉ xᵉ eᵉ) (unQuoteGSᵉ yᵉ eᵉ)
    unQuoteGSᵉ (gInvᵉ xᵉ) eᵉ = inv-Groupᵉ Gᵉ (unQuoteGSᵉ xᵉ eᵉ)
    unQuoteGSᵉ (innerᵉ xᵉ) eᵉ = getVecᵉ eᵉ xᵉ

    private
      --ᵉ Shorterᵉ namesᵉ to makeᵉ theᵉ proofsᵉ lessᵉ verboseᵉ
      _*ᵉ_ = mul-Groupᵉ Gᵉ
      infixl 40 _*ᵉ_
      _⁻¹ᵉ = inv-Groupᵉ Gᵉ
      infix 45 _⁻¹ᵉ
      unitᵉ = unit-Groupᵉ Gᵉ

    useGroupEqualityElemᵉ :
      {xᵉ yᵉ : GroupSyntaxᵉ nᵉ} (envᵉ : Envᵉ nᵉ (type-Groupᵉ Gᵉ)) →
      GroupEqualityElemᵉ xᵉ yᵉ → unQuoteGSᵉ xᵉ envᵉ ＝ᵉ unQuoteGSᵉ yᵉ envᵉ
    useGroupEqualityElemᵉ envᵉ (xsym-GEᵉ geᵉ) = invᵉ (useGroupEqualityElemᵉ envᵉ geᵉ)
    useGroupEqualityElemᵉ envᵉ (xap-gMul-lᵉ {zᵉ = zᵉ} ge'ᵉ) =
      apᵉ (_*ᵉ unQuoteGSᵉ zᵉ envᵉ) (useGroupEqualityElemᵉ envᵉ ge'ᵉ)
    useGroupEqualityElemᵉ envᵉ (xap-gMul-rᵉ {xᵉ = xᵉ} ge'ᵉ) =
      apᵉ (unQuoteGSᵉ xᵉ envᵉ *ᵉ_) (useGroupEqualityElemᵉ envᵉ ge'ᵉ)
    --ᵉ useGroupEqualityElemᵉ envᵉ (xap-gMulᵉ {yᵉ = yᵉ} {zᵉ = zᵉ} geᵉ ge'ᵉ) =
    --ᵉ                              apᵉ (_*ᵉ (unQuoteGSᵉ zᵉ envᵉ)) (useGroupEqualityElemᵉ envᵉ geᵉ)
    --ᵉ                              ∙ᵉ apᵉ (unQuoteGSᵉ yᵉ envᵉ *ᵉ_) (useGroupEqualityElemᵉ envᵉ ge'ᵉ)
    useGroupEqualityElemᵉ envᵉ (xap-gInvᵉ geᵉ) =
      apᵉ (inv-Groupᵉ Gᵉ) (useGroupEqualityElemᵉ envᵉ geᵉ)
    useGroupEqualityElemᵉ envᵉ (xassoc-GEᵉ xᵉ yᵉ zᵉ) = associative-mul-Groupᵉ Gᵉ _ _ _
    useGroupEqualityElemᵉ envᵉ (xl-unitᵉ _) = left-unit-law-mul-Groupᵉ Gᵉ _
    useGroupEqualityElemᵉ envᵉ (xr-unitᵉ _) = right-unit-law-mul-Groupᵉ Gᵉ _
    useGroupEqualityElemᵉ envᵉ (xl-invᵉ xᵉ) = left-inverse-law-mul-Groupᵉ Gᵉ _
    useGroupEqualityElemᵉ envᵉ (xr-invᵉ xᵉ) = right-inverse-law-mul-Groupᵉ Gᵉ _
    useGroupEqualityElemᵉ envᵉ xinv-unit-GEᵉ = inv-unit-Groupᵉ Gᵉ
    useGroupEqualityElemᵉ envᵉ (xinv-inv-GEᵉ xᵉ) = inv-inv-Groupᵉ Gᵉ (unQuoteGSᵉ xᵉ envᵉ)
    useGroupEqualityElemᵉ envᵉ (xdistr-inv-mul-GEᵉ xᵉ yᵉ) =
      distributive-inv-mul-Groupᵉ Gᵉ

    useGroupEqualityᵉ :
      {xᵉ yᵉ : GroupSyntaxᵉ nᵉ} (envᵉ : Envᵉ nᵉ (type-Groupᵉ Gᵉ)) →
      GroupEqualityᵉ xᵉ yᵉ → unQuoteGSᵉ xᵉ envᵉ ＝ᵉ unQuoteGSᵉ yᵉ envᵉ
    useGroupEqualityᵉ envᵉ refl-GEᵉ = reflᵉ
    useGroupEqualityᵉ envᵉ (xᵉ ∷GEᵉ refl-GEᵉ) = useGroupEqualityElemᵉ envᵉ xᵉ
    useGroupEqualityᵉ envᵉ (xᵉ ∷GEᵉ xs@(ᵉ_ ∷GEᵉ _)) =
      useGroupEqualityElemᵉ envᵉ xᵉ ∙ᵉ useGroupEqualityᵉ envᵉ xsᵉ

    --ᵉ simplifyExpressionᵉ :
    --ᵉ   (gᵉ : GroupSyntaxᵉ nᵉ) (envᵉ : Envᵉ nᵉ (type-Groupᵉ Gᵉ)) →
    --ᵉ   unQuoteGSᵉ gᵉ envᵉ ＝ᵉ unQuoteGSᵉ (unquoteSimpleᵉ (simplifyGSᵉ gᵉ)) envᵉ
    --ᵉ simplifyExpressionᵉ gᵉ envᵉ = useGroupEqualityᵉ envᵉ (simplifyValidᵉ gᵉ)

    --ᵉ Variadicᵉ functionsᵉ
    n-argsᵉ : (nᵉ : ℕᵉ) (Aᵉ Bᵉ : UUᵉ) → UUᵉ
    n-argsᵉ zero-ℕᵉ Aᵉ Bᵉ = Bᵉ
    n-argsᵉ (succ-ℕᵉ nᵉ) Aᵉ Bᵉ = Aᵉ → n-argsᵉ nᵉ Aᵉ Bᵉ
    map-n-argsᵉ :
      {Aᵉ A'ᵉ Bᵉ : UUᵉ} (nᵉ : ℕᵉ) → (A'ᵉ → Aᵉ) → n-argsᵉ nᵉ Aᵉ Bᵉ → n-argsᵉ nᵉ A'ᵉ Bᵉ
    map-n-argsᵉ zero-ℕᵉ fᵉ vᵉ = vᵉ
    map-n-argsᵉ (succ-ℕᵉ nᵉ) fᵉ vᵉ = λ xᵉ → map-n-argsᵉ nᵉ fᵉ (vᵉ (fᵉ xᵉ))
    apply-n-args-finᵉ : {Bᵉ : UUᵉ} (nᵉ : ℕᵉ) → n-argsᵉ nᵉ (Inductive-Finᵉ nᵉ) Bᵉ → Bᵉ
    apply-n-args-finᵉ zero-ℕᵉ fᵉ = fᵉ
    apply-n-args-finᵉ (succ-ℕᵉ nᵉ) fᵉ =
      apply-n-args-finᵉ
        ( nᵉ)
        ( map-n-argsᵉ nᵉ succ-Inductive-Finᵉ (fᵉ zero-Inductive-Finᵉ))
    apply-n-argsᵉ : {Bᵉ : UUᵉ} (nᵉ : ℕᵉ) → n-argsᵉ nᵉ (GroupSyntaxᵉ nᵉ) Bᵉ → Bᵉ
    apply-n-argsᵉ nᵉ fᵉ = apply-n-args-finᵉ nᵉ (map-n-argsᵉ nᵉ innerᵉ fᵉ)

    --ᵉ Aᵉ variationᵉ ofᵉ simplifyExpressionᵉ whichᵉ takesᵉ aᵉ functionᵉ fromᵉ theᵉ freeᵉ variablesᵉ to exprᵉ
    --ᵉ simplifyExprᵉ :
    --ᵉ   (envᵉ : Envᵉ nᵉ (type-Groupᵉ Gᵉ)) (gᵉ : n-argsᵉ nᵉ (GroupSyntaxᵉ nᵉ) (GroupSyntaxᵉ nᵉ)) →
    --ᵉ   unQuoteGSᵉ (apply-n-argsᵉ nᵉ gᵉ) envᵉ ＝ᵉ unQuoteGSᵉ (unquoteSimpleᵉ (simplifyGSᵉ (apply-n-argsᵉ nᵉ gᵉ))) envᵉ
    --ᵉ simplifyExprᵉ envᵉ gᵉ = simplifyExpressionᵉ (apply-n-argsᵉ nᵉ gᵉ) envᵉ
```

```text
private
    _*'ᵉ_ : {nᵉ : ℕᵉ} → GroupSyntaxᵉ nᵉ → GroupSyntaxᵉ nᵉ → GroupSyntaxᵉ nᵉ
    _*'ᵉ_ = gMulᵉ
    xᵉ : GroupSyntaxᵉ 2
    xᵉ = innerᵉ (zero-Inductive-Finᵉ)
    yᵉ : GroupSyntaxᵉ 2
    yᵉ = innerᵉ (succ-Inductive-Finᵉ zero-Inductive-Finᵉ)

    infixl 40 _*'ᵉ_
    ex1ᵉ : GroupEqualityᵉ {nᵉ = 2ᵉ} (gInvᵉ (xᵉ *'ᵉ yᵉ *'ᵉ gInvᵉ xᵉ *'ᵉ gInvᵉ yᵉ)) (yᵉ *'ᵉ xᵉ *'ᵉ gInvᵉ yᵉ *'ᵉ gInvᵉ xᵉ)
    ex1ᵉ = simplifyValidᵉ _

    ex2ᵉ : ∀ᵉ xᵉ yᵉ → (xᵉ *ᵉ yᵉ *ᵉ xᵉ ⁻¹ᵉ *ᵉ yᵉ ⁻¹ᵉ) ⁻¹ᵉ ＝ᵉ (yᵉ *ᵉ xᵉ *ᵉ yᵉ ⁻¹ᵉ *ᵉ xᵉ ⁻¹ᵉ)
    ex2ᵉ x'ᵉ y'ᵉ = simplifyExpressionᵉ (gInvᵉ (xᵉ *'ᵉ yᵉ *'ᵉ gInvᵉ xᵉ *'ᵉ gInvᵉ yᵉ)) (x'ᵉ ∷ᵉ y'ᵉ ∷ᵉ empty-vecᵉ)

    _ : UUᵉ
    --ᵉ _ = {!simplifyValidᵉ (yᵉ *'ᵉ (xᵉ *'ᵉ (gInvᵉ yᵉ *'ᵉ (gInvᵉ xᵉ *'ᵉ gUnit))))!ᵉ}
    _ = {!ex1!ᵉ}

    ex3ᵉ : ∀ᵉ xᵉ yᵉ → (xᵉ *ᵉ yᵉ) ⁻¹ᵉ ＝ᵉ (yᵉ ⁻¹ᵉ *ᵉ xᵉ ⁻¹ᵉ)
    ex3ᵉ x'ᵉ y'ᵉ = {!simplifyExpressionᵉ (gInvᵉ (xᵉ *'ᵉ yᵉ)) (x'ᵉ ∷ᵉ y'ᵉ ∷ᵉ empty-vec)!ᵉ}

    _ : GroupEqualityᵉ {nᵉ = 2ᵉ} (yᵉ *'ᵉ (xᵉ *'ᵉ (gInvᵉ yᵉ *'ᵉ (gInvᵉ xᵉ *'ᵉ gUnitᵉ)))) (yᵉ *'ᵉ (xᵉ *'ᵉ (gInvᵉ yᵉ *'ᵉ (gInvᵉ xᵉ *'ᵉ gUnitᵉ))))
    _ = {!simplifyValidᵉ (gInvᵉ xᵉ *'ᵉ xᵉ *'ᵉ y)!ᵉ}
    --ᵉ _ = {!simplifyValidᵉ (gUnitᵉ *'ᵉ gUnit)!ᵉ}
    --ᵉ _ = {!simplifyValidᵉ (xᵉ *'ᵉ gUnit)!ᵉ}
```