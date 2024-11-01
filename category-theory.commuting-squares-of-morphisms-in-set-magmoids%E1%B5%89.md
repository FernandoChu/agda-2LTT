# Commuting squares of morphisms in set-magmoids

<pre class="Agda"><a id="59" class="Keyword">module</a> <a id="66" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html" class="Module">category-theory.commuting-squares-of-morphisms-in-set-magmoidsᵉ</a> <a id="130" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="category-theory.set-magmoids%25E1%25B5%2589.html" class="Module">category-theory.set-magmoidsᵉ</a>

<a id="229" class="Keyword">open</a> <a id="234" class="Keyword">import</a> <a id="241" href="foundation.identity-types%25E1%25B5%2589.html" class="Module">foundation.identity-typesᵉ</a>
<a id="268" class="Keyword">open</a> <a id="273" class="Keyword">import</a> <a id="280" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
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

in a [set-magmoid](category-theory.set-magmoids.md) `C` is said to **commute**
if there is an [identification](foundation-core.identity-types.md) between both
composites:

```text
  bottom ∘ left ＝ right ∘ top.
```

## Definitions

<pre class="Agda"><a id="coherence-square-hom-Set-Magmoidᵉ"></a><a id="680" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#680" class="Function">coherence-square-hom-Set-Magmoidᵉ</a> <a id="714" class="Symbol">:</a>
  <a id="718" class="Symbol">{</a><a id="719" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#719" class="Bound">l1ᵉ</a> <a id="723" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#723" class="Bound">l2ᵉ</a> <a id="727" class="Symbol">:</a> <a id="729" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="734" class="Symbol">}</a> <a id="736" class="Symbol">(</a><a id="737" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#737" class="Bound">Cᵉ</a> <a id="740" class="Symbol">:</a> <a id="742" href="category-theory.set-magmoids%25E1%25B5%2589.html#1566" class="Function">Set-Magmoidᵉ</a> <a id="755" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#719" class="Bound">l1ᵉ</a> <a id="759" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#723" class="Bound">l2ᵉ</a><a id="762" class="Symbol">)</a>
  <a id="766" class="Symbol">{</a><a id="767" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#767" class="Bound">xᵉ</a> <a id="770" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#770" class="Bound">yᵉ</a> <a id="773" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#773" class="Bound">zᵉ</a> <a id="776" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#776" class="Bound">wᵉ</a> <a id="779" class="Symbol">:</a> <a id="781" href="category-theory.set-magmoids%25E1%25B5%2589.html#1834" class="Function">obj-Set-Magmoidᵉ</a> <a id="798" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#737" class="Bound">Cᵉ</a><a id="800" class="Symbol">}</a>
  <a id="804" class="Symbol">(</a><a id="805" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#805" class="Bound">topᵉ</a> <a id="810" class="Symbol">:</a> <a id="812" href="category-theory.set-magmoids%25E1%25B5%2589.html#1997" class="Function">hom-Set-Magmoidᵉ</a> <a id="829" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#737" class="Bound">Cᵉ</a> <a id="832" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#767" class="Bound">xᵉ</a> <a id="835" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#770" class="Bound">yᵉ</a><a id="837" class="Symbol">)</a>
  <a id="841" class="Symbol">(</a><a id="842" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#842" class="Bound">leftᵉ</a> <a id="848" class="Symbol">:</a> <a id="850" href="category-theory.set-magmoids%25E1%25B5%2589.html#1997" class="Function">hom-Set-Magmoidᵉ</a> <a id="867" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#737" class="Bound">Cᵉ</a> <a id="870" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#767" class="Bound">xᵉ</a> <a id="873" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#773" class="Bound">zᵉ</a><a id="875" class="Symbol">)</a>
  <a id="879" class="Symbol">(</a><a id="880" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#880" class="Bound">rightᵉ</a> <a id="887" class="Symbol">:</a> <a id="889" href="category-theory.set-magmoids%25E1%25B5%2589.html#1997" class="Function">hom-Set-Magmoidᵉ</a> <a id="906" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#737" class="Bound">Cᵉ</a> <a id="909" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#770" class="Bound">yᵉ</a> <a id="912" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#776" class="Bound">wᵉ</a><a id="914" class="Symbol">)</a>
  <a id="918" class="Symbol">(</a><a id="919" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#919" class="Bound">bottomᵉ</a> <a id="927" class="Symbol">:</a> <a id="929" href="category-theory.set-magmoids%25E1%25B5%2589.html#1997" class="Function">hom-Set-Magmoidᵉ</a> <a id="946" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#737" class="Bound">Cᵉ</a> <a id="949" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#773" class="Bound">zᵉ</a> <a id="952" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#776" class="Bound">wᵉ</a><a id="954" class="Symbol">)</a> <a id="956" class="Symbol">→</a>
  <a id="960" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="964" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#723" class="Bound">l2ᵉ</a>
<a id="968" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#680" class="Function">coherence-square-hom-Set-Magmoidᵉ</a> <a id="1002" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1002" class="Bound">Cᵉ</a> <a id="1005" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1005" class="Bound">topᵉ</a> <a id="1010" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1010" class="Bound">leftᵉ</a> <a id="1016" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1016" class="Bound">rightᵉ</a> <a id="1023" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1023" class="Bound">bottomᵉ</a> <a id="1031" class="Symbol">=</a>
  <a id="1035" class="Symbol">(</a> <a id="1037" href="category-theory.set-magmoids%25E1%25B5%2589.html#2301" class="Function">comp-hom-Set-Magmoidᵉ</a> <a id="1059" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1002" class="Bound">Cᵉ</a> <a id="1062" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1023" class="Bound">bottomᵉ</a> <a id="1070" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1010" class="Bound">leftᵉ</a><a id="1075" class="Symbol">)</a> <a id="1077" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a>
  <a id="1082" class="Symbol">(</a> <a id="1084" href="category-theory.set-magmoids%25E1%25B5%2589.html#2301" class="Function">comp-hom-Set-Magmoidᵉ</a> <a id="1106" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1002" class="Bound">Cᵉ</a> <a id="1109" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1016" class="Bound">rightᵉ</a> <a id="1116" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1005" class="Bound">topᵉ</a><a id="1120" class="Symbol">)</a>
</pre>