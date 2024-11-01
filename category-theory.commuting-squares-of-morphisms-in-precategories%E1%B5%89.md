# Commuting squares of morphisms in precategories

<pre class="Agda"><a id="60" class="Keyword">module</a> <a id="67" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html" class="Module">category-theory.commuting-squares-of-morphisms-in-precategoriesᵉ</a> <a id="132" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html" class="Module">category-theory.commuting-squares-of-morphisms-in-set-magmoidsᵉ</a>
<a id="264" class="Keyword">open</a> <a id="269" class="Keyword">import</a> <a id="276" href="category-theory.precategories%25E1%25B5%2589.html" class="Module">category-theory.precategoriesᵉ</a>

<a id="308" class="Keyword">open</a> <a id="313" class="Keyword">import</a> <a id="320" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
</pre>
</details>

## Idea

A square of morphisms

```text
  x ------> y
  |         |
  |         |
  ∨         ∨
  z ------> w
```

in a [precategory](category-theory.precategories.md) `C` is said to **commute**
if there is an [identification](foundation-core.identity-types.md) between both
composites:

```text
  bottom ∘ left ＝ right ∘ top.
```

## Definitions

<pre class="Agda"><a id="coherence-square-hom-Precategoryᵉ"></a><a id="721" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#721" class="Function">coherence-square-hom-Precategoryᵉ</a> <a id="755" class="Symbol">:</a>
  <a id="759" class="Symbol">{</a><a id="760" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#760" class="Bound">l1ᵉ</a> <a id="764" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#764" class="Bound">l2ᵉ</a> <a id="768" class="Symbol">:</a> <a id="770" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="775" class="Symbol">}</a> <a id="777" class="Symbol">(</a><a id="778" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#778" class="Bound">Cᵉ</a> <a id="781" class="Symbol">:</a> <a id="783" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="796" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#760" class="Bound">l1ᵉ</a> <a id="800" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#764" class="Bound">l2ᵉ</a><a id="803" class="Symbol">)</a> <a id="805" class="Symbol">{</a><a id="806" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#806" class="Bound">xᵉ</a> <a id="809" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#809" class="Bound">yᵉ</a> <a id="812" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#812" class="Bound">zᵉ</a> <a id="815" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#815" class="Bound">wᵉ</a> <a id="818" class="Symbol">:</a> <a id="820" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="837" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#778" class="Bound">Cᵉ</a><a id="839" class="Symbol">}</a>
  <a id="843" class="Symbol">(</a><a id="844" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#844" class="Bound">topᵉ</a> <a id="849" class="Symbol">:</a> <a id="851" href="category-theory.precategories%25E1%25B5%2589.html#4999" class="Function">hom-Precategoryᵉ</a> <a id="868" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#778" class="Bound">Cᵉ</a> <a id="871" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#806" class="Bound">xᵉ</a> <a id="874" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#809" class="Bound">yᵉ</a><a id="876" class="Symbol">)</a>
  <a id="880" class="Symbol">(</a><a id="881" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#881" class="Bound">leftᵉ</a> <a id="887" class="Symbol">:</a> <a id="889" href="category-theory.precategories%25E1%25B5%2589.html#4999" class="Function">hom-Precategoryᵉ</a> <a id="906" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#778" class="Bound">Cᵉ</a> <a id="909" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#806" class="Bound">xᵉ</a> <a id="912" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#812" class="Bound">zᵉ</a><a id="914" class="Symbol">)</a>
  <a id="918" class="Symbol">(</a><a id="919" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#919" class="Bound">rightᵉ</a> <a id="926" class="Symbol">:</a> <a id="928" href="category-theory.precategories%25E1%25B5%2589.html#4999" class="Function">hom-Precategoryᵉ</a> <a id="945" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#778" class="Bound">Cᵉ</a> <a id="948" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#809" class="Bound">yᵉ</a> <a id="951" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#815" class="Bound">wᵉ</a><a id="953" class="Symbol">)</a>
  <a id="957" class="Symbol">(</a><a id="958" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#958" class="Bound">bottomᵉ</a> <a id="966" class="Symbol">:</a> <a id="968" href="category-theory.precategories%25E1%25B5%2589.html#4999" class="Function">hom-Precategoryᵉ</a> <a id="985" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#778" class="Bound">Cᵉ</a> <a id="988" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#812" class="Bound">zᵉ</a> <a id="991" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#815" class="Bound">wᵉ</a><a id="993" class="Symbol">)</a> <a id="995" class="Symbol">→</a>
  <a id="999" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1003" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#764" class="Bound">l2ᵉ</a>
<a id="1007" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#721" class="Function">coherence-square-hom-Precategoryᵉ</a> <a id="1041" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#1041" class="Bound">Cᵉ</a> <a id="1044" class="Symbol">=</a>
  <a id="1048" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#680" class="Function">coherence-square-hom-Set-Magmoidᵉ</a> <a id="1082" class="Symbol">(</a><a id="1083" href="category-theory.precategories%25E1%25B5%2589.html#8559" class="Function">set-magmoid-Precategoryᵉ</a> <a id="1108" href="category-theory.commuting-squares-of-morphisms-in-precategories%25E1%25B5%2589.html#1041" class="Bound">Cᵉ</a><a id="1110" class="Symbol">)</a>
</pre>