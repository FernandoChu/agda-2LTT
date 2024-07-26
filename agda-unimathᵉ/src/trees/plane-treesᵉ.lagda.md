# Plane trees

```agda
module trees.plane-treesᵉ where
```

<details><sumary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.maybeᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.universe-levelsᵉ

open import lists.listsᵉ

open import trees.full-binary-treesᵉ
open import trees.w-typesᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "planeᵉ tree"ᵉ Agda=plane-treeᵉ WD="orderedᵉ tree"ᵉ WDID=Q10396021ᵉ}} isᵉ
aᵉ finiteᵉ [directedᵉ tree](trees.directed-trees.mdᵉ) thatᵉ canᵉ beᵉ drawnᵉ onᵉ aᵉ planeᵉ
with theᵉ rootᵉ atᵉ theᵉ bottom,ᵉ andᵉ allᵉ branchesᵉ directedᵉ upwards.ᵉ Moreᵉ precisely,ᵉ
aᵉ planeᵉ treeᵉ consistsᵉ ofᵉ aᵉ rootᵉ andᵉ aᵉ familyᵉ ofᵉ planeᵉ treesᵉ indexedᵉ byᵉ aᵉ
[standardᵉ finiteᵉ type](univalent-combinatorics.standard-finite-types.md).ᵉ Planeᵉ
treesᵉ areᵉ alsoᵉ knownᵉ asᵉ _orderedᵉ trees_.ᵉ

Theᵉ typeᵉ ofᵉ planeᵉ treesᵉ canᵉ beᵉ definedᵉ in severalᵉ equivalentᵉ waysᵉ:

-ᵉ Theᵉ typeᵉ ofᵉ planeᵉ treesᵉ isᵉ theᵉ inductive typeᵉ with constructor

  ```text
    (nᵉ : ℕᵉ) → (Finᵉ nᵉ → plane-treeᵉ) → plane-tree.ᵉ
  ```

-ᵉ Theᵉ typeᵉ ofᵉ planeᵉ treesᵉ isᵉ theᵉ [W-type](trees.w-types.mdᵉ)

  ```text
    𝕎ᵉ ℕᵉ Fin.ᵉ
  ```

-ᵉ Theᵉ typeᵉ ofᵉ planeᵉ treesᵉ isᵉ theᵉ inductive typeᵉ with constructor

  ```text
    listᵉ plane-treeᵉ → plane-tree.ᵉ
  ```

Theᵉ typeᵉ ofᵉ planeᵉ treesᵉ isᵉ thereforeᵉ theᵉ leastᵉ fixedᵉ pointᵉ ofᵉ theᵉ
[list](lists.lists.mdᵉ) functorᵉ `Xᵉ ↦ᵉ listᵉ X`.ᵉ Inᵉ particular,ᵉ `plane-tree`ᵉ isᵉ theᵉ
leastᵉ fixedᵉ pointᵉ ofᵉ theᵉ functorᵉ

```text
  Xᵉ ↦ᵉ 1 +ᵉ plane-treeᵉ ×ᵉ X.ᵉ
```

Theᵉ leastᵉ fixedᵉ pointᵉ forᵉ thisᵉ functorᵉ coincidesᵉ with theᵉ leastᵉ fixedᵉ pointᵉ ofᵉ
theᵉ functorᵉ

```text
  Xᵉ ↦ᵉ 1 +ᵉ X².ᵉ
```

Thusᵉ weᵉ obtainᵉ anᵉ equivalenceᵉ

```text
  plane-treeᵉ ≃ᵉ full-binary-treeᵉ
```

fromᵉ theᵉ typeᵉ ofᵉ planeᵉ treesᵉ to theᵉ typeᵉ ofᵉ
[fullᵉ binaryᵉ trees](trees.full-binary-trees.md).ᵉ

## Definitions

### Plane trees

```agda
data plane-treeᵉ : UUᵉ lzero where
  make-plane-treeᵉ : {nᵉ : ℕᵉ} → (Finᵉ nᵉ → plane-treeᵉ) → plane-treeᵉ
```

### Plane trees as W-types

```agda
plane-tree-𝕎ᵉ : UUᵉ lzero
plane-tree-𝕎ᵉ = 𝕎ᵉ ℕᵉ Finᵉ
```

### Plane trees defined using lists

```agda
data listed-plane-treeᵉ : UUᵉ lzero where
  make-listed-plane-treeᵉ : listᵉ listed-plane-treeᵉ → listed-plane-treeᵉ
```

## Operations on plane trees

### The type of nodes, including leaves, of a plane tree

```agda
node-plane-treeᵉ : plane-treeᵉ → UUᵉ lzero
node-plane-treeᵉ (make-plane-treeᵉ {nᵉ} Tᵉ) =
  Maybeᵉ (Σᵉ (Finᵉ nᵉ) (λ iᵉ → node-plane-treeᵉ (Tᵉ iᵉ)))
```

### The root of a plane tree

```agda
root-plane-treeᵉ : (Tᵉ : plane-treeᵉ) → node-plane-treeᵉ Tᵉ
root-plane-treeᵉ (make-plane-treeᵉ Tᵉ) = exception-Maybeᵉ
```

## Properties

### The type of listed plane trees is equivalent to the type of lists of listed plane trees

```agda
unpack-listed-plane-treeᵉ : listed-plane-treeᵉ → listᵉ listed-plane-treeᵉ
unpack-listed-plane-treeᵉ (make-listed-plane-treeᵉ tᵉ) = tᵉ

is-section-unpack-listed-plane-treeᵉ :
  is-sectionᵉ make-listed-plane-treeᵉ unpack-listed-plane-treeᵉ
is-section-unpack-listed-plane-treeᵉ (make-listed-plane-treeᵉ tᵉ) = reflᵉ

is-retraction-unpack-listed-plane-treeᵉ :
  is-retractionᵉ make-listed-plane-treeᵉ unpack-listed-plane-treeᵉ
is-retraction-unpack-listed-plane-treeᵉ lᵉ = reflᵉ

is-equiv-make-listed-plane-treeᵉ :
  is-equivᵉ make-listed-plane-treeᵉ
is-equiv-make-listed-plane-treeᵉ =
  is-equiv-is-invertibleᵉ
    ( unpack-listed-plane-treeᵉ)
    ( is-section-unpack-listed-plane-treeᵉ)
    ( is-retraction-unpack-listed-plane-treeᵉ)

equiv-make-listed-plane-treeᵉ : listᵉ listed-plane-treeᵉ ≃ᵉ listed-plane-treeᵉ
pr1ᵉ equiv-make-listed-plane-treeᵉ = make-listed-plane-treeᵉ
pr2ᵉ equiv-make-listed-plane-treeᵉ = is-equiv-make-listed-plane-treeᵉ
```

### The type of listed plane trees is equivalent to the type of full binary trees

Sinceᵉ `plane-tree`ᵉ isᵉ inductivelyᵉ generatedᵉ byᵉ aᵉ constructor
`listᵉ plane-treeᵉ → plane-tree`,ᵉ weᵉ haveᵉ anᵉ
[equivalence](foundation-core.equivalences.mdᵉ)

```text
  listᵉ plane-treeᵉ ≃ᵉ plane-tree.ᵉ
```

Thisᵉ descriptionᵉ allowsᵉ usᵉ to obtainᵉ anᵉ equivalenceᵉ
`plane-treeᵉ ≃ᵉ full-binary-tree`ᵉ fromᵉ theᵉ typeᵉ ofᵉ planeᵉ treesᵉ to theᵉ typeᵉ ofᵉ
[fullᵉ binaryᵉ trees](trees.full-binary-trees.md).ᵉ Indeed,ᵉ byᵉ theᵉ aboveᵉ
equivalenceᵉ weᵉ canᵉ computeᵉ

```text
  plane-treeᵉ ≃ᵉ listᵉ plane-treeᵉ
             ≃ᵉ 1 +ᵉ plane-treeᵉ ×ᵉ listᵉ plane-treeᵉ
             ≃ᵉ 1 +ᵉ plane-tree²ᵉ
```

Onᵉ theᵉ otherᵉ hand,ᵉ theᵉ typeᵉ `full-binary-tree`ᵉ isᵉ aᵉ fixedᵉ pointᵉ forᵉ theᵉ
[polynomialᵉ endofunctor](trees.polynomial-endofunctors.mdᵉ)
`Xᵉ ↦ᵉ 1 +ᵉ full-binary-treeᵉ ×ᵉ X`,ᵉ sinceᵉ weᵉ haveᵉ equivalences.ᵉ

```text
  full-binary-treeᵉ ≃ᵉ 1 +ᵉ full-binary-tree²ᵉ
                   ≃ᵉ 1 +ᵉ full-binary-treeᵉ ×ᵉ full-binary-treeᵉ
```

Sinceᵉ `full-binary-tree`ᵉ isᵉ theᵉ leastᵉ fixedᵉ pointᵉ ofᵉ theᵉ polynomialᵉ endofunctorᵉ
`Xᵉ ↦ᵉ 1 +ᵉ X²`,ᵉ weᵉ obtainᵉ aᵉ `(1ᵉ +ᵉ X²)`-structureᵉ preservingᵉ mapᵉ

```text
  full-binary-treeᵉ → plane-tree.ᵉ
```

Likewise,ᵉ sinceᵉ `plane-tree`ᵉ isᵉ theᵉ leastᵉ fixedᵉ pointᵉ ofᵉ theᵉ endofunctorᵉ `list`,ᵉ
weᵉ obtainᵉ aᵉ `list`-structureᵉ preservingᵉ mapᵉ

```text
  plane-treeᵉ → full-binary-tree.ᵉ
```

Initialityᵉ ofᵉ bothᵉ `full-binary-tree`ᵉ andᵉ `plane-tree`ᵉ canᵉ thenᵉ beᵉ usedᵉ to showᵉ
thatᵉ theseᵉ twoᵉ mapsᵉ areᵉ inverseᵉ to eachᵉ other,ᵉ i.e.,ᵉ thatᵉ weᵉ obtainᵉ anᵉ
equivalenceᵉ

```text
  plane-treeᵉ ≃ᵉ full-binary-tree.ᵉ
```

```agda
full-binary-tree-listed-plane-treeᵉ : listed-plane-treeᵉ → full-binary-treeᵉ
full-binary-tree-listed-plane-treeᵉ (make-listed-plane-treeᵉ nilᵉ) =
  leaf-full-binary-treeᵉ
full-binary-tree-listed-plane-treeᵉ (make-listed-plane-treeᵉ (consᵉ Tᵉ lᵉ)) =
  join-full-binary-treeᵉ
    ( full-binary-tree-listed-plane-treeᵉ Tᵉ)
    ( full-binary-tree-listed-plane-treeᵉ (make-listed-plane-treeᵉ lᵉ))

listed-plane-tree-full-binary-treeᵉ : full-binary-treeᵉ → listed-plane-treeᵉ
listed-plane-tree-full-binary-treeᵉ leaf-full-binary-treeᵉ =
  make-listed-plane-treeᵉ nilᵉ
listed-plane-tree-full-binary-treeᵉ (join-full-binary-treeᵉ Sᵉ Tᵉ) =
  make-listed-plane-treeᵉ
    ( consᵉ
      ( listed-plane-tree-full-binary-treeᵉ Sᵉ)
      ( unpack-listed-plane-treeᵉ (listed-plane-tree-full-binary-treeᵉ Tᵉ)))

is-section-listed-plane-tree-full-binary-treeᵉ :
  is-sectionᵉ
    ( full-binary-tree-listed-plane-treeᵉ)
    ( listed-plane-tree-full-binary-treeᵉ)
is-section-listed-plane-tree-full-binary-treeᵉ leaf-full-binary-treeᵉ =
  reflᵉ
is-section-listed-plane-tree-full-binary-treeᵉ
  ( join-full-binary-treeᵉ Sᵉ Tᵉ) =
  ap-binaryᵉ
    ( join-full-binary-treeᵉ)
    ( is-section-listed-plane-tree-full-binary-treeᵉ Sᵉ)
    ( ( apᵉ
        ( full-binary-tree-listed-plane-treeᵉ)
        ( is-section-unpack-listed-plane-treeᵉ _)) ∙ᵉ
      ( is-section-listed-plane-tree-full-binary-treeᵉ Tᵉ))

is-retraction-listed-plane-tree-full-binary-treeᵉ :
  is-retractionᵉ
    ( full-binary-tree-listed-plane-treeᵉ)
    ( listed-plane-tree-full-binary-treeᵉ)
is-retraction-listed-plane-tree-full-binary-treeᵉ (make-listed-plane-treeᵉ nilᵉ) =
  reflᵉ
is-retraction-listed-plane-tree-full-binary-treeᵉ
  ( make-listed-plane-treeᵉ (consᵉ Tᵉ lᵉ)) =
  ( apᵉ
    ( make-listed-plane-treeᵉ)
    ( ap-binaryᵉ
      ( consᵉ)
      ( is-retraction-listed-plane-tree-full-binary-treeᵉ Tᵉ)
      ( apᵉ
        ( unpack-listed-plane-treeᵉ)
        ( is-retraction-listed-plane-tree-full-binary-treeᵉ
          ( make-listed-plane-treeᵉ lᵉ)))))

is-equiv-full-binary-tree-listed-plane-treeᵉ :
  is-equivᵉ full-binary-tree-listed-plane-treeᵉ
is-equiv-full-binary-tree-listed-plane-treeᵉ =
  is-equiv-is-invertibleᵉ
    ( listed-plane-tree-full-binary-treeᵉ)
    ( is-section-listed-plane-tree-full-binary-treeᵉ)
    ( is-retraction-listed-plane-tree-full-binary-treeᵉ)

equiv-full-binary-tree-listed-plane-treeᵉ :
  listed-plane-treeᵉ ≃ᵉ full-binary-treeᵉ
pr1ᵉ equiv-full-binary-tree-listed-plane-treeᵉ =
  full-binary-tree-listed-plane-treeᵉ
pr2ᵉ equiv-full-binary-tree-listed-plane-treeᵉ =
  is-equiv-full-binary-tree-listed-plane-treeᵉ
```