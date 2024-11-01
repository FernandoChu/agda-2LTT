# Full maps between precategories

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="category-theory.full-maps-precategories%25E1%25B5%2589.html" class="Module">category-theory.full-maps-precategoriesᵉ</a> <a id="92" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="148" class="Keyword">open</a> <a id="153" class="Keyword">import</a> <a id="160" href="elementary-number-theory.natural-numbers%25E1%25B5%2589.html" class="Module">elementary-number-theory.natural-numbersᵉ</a>
<a id="202" class="Keyword">open</a> <a id="207" class="Keyword">import</a> <a id="214" href="category-theory.maps-precategories%25E1%25B5%2589.html" class="Module">category-theory.maps-precategoriesᵉ</a>
<a id="250" class="Keyword">open</a> <a id="255" class="Keyword">import</a> <a id="262" href="category-theory.precategories%25E1%25B5%2589.html" class="Module">category-theory.precategoriesᵉ</a>

<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="339" class="Keyword">open</a> <a id="344" class="Keyword">import</a> <a id="351" href="foundation.function-types%25E1%25B5%2589.html" class="Module">foundation.function-typesᵉ</a>
<a id="378" class="Keyword">open</a> <a id="383" class="Keyword">import</a> <a id="390" href="foundation.iterated-dependent-product-types%25E1%25B5%2589.html" class="Module">foundation.iterated-dependent-product-typesᵉ</a>
<a id="435" class="Keyword">open</a> <a id="440" class="Keyword">import</a> <a id="447" href="foundation.propositions%25E1%25B5%2589.html" class="Module">foundation.propositionsᵉ</a>
<a id="472" class="Keyword">open</a> <a id="477" class="Keyword">import</a> <a id="484" href="foundation.surjective-maps%25E1%25B5%2589.html" class="Module">foundation.surjective-mapsᵉ</a>
<a id="512" class="Keyword">open</a> <a id="517" class="Keyword">import</a> <a id="524" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
</pre>
</details>

## Idea

A [map](category-theory.maps-precategories.md) between
[precategories](category-theory.precategories.md) `C` and `D` is **full** if
it's a [surjection](foundation.surjective-maps.md) on
hom-[sets](foundation-core.sets.md).

## Definition

### The predicate on maps between precategories of being full

<pre class="Agda"><a id="888" class="Keyword">module</a> <a id="895" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#895" class="Module">_</a>
  <a id="899" class="Symbol">{</a><a id="900" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#900" class="Bound">l1ᵉ</a> <a id="904" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#904" class="Bound">l2ᵉ</a> <a id="908" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#908" class="Bound">l3ᵉ</a> <a id="912" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#912" class="Bound">l4ᵉ</a> <a id="916" class="Symbol">:</a> <a id="918" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="923" class="Symbol">}</a>
  <a id="927" class="Symbol">(</a><a id="928" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#928" class="Bound">Cᵉ</a> <a id="931" class="Symbol">:</a> <a id="933" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="946" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#900" class="Bound">l1ᵉ</a> <a id="950" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#904" class="Bound">l2ᵉ</a><a id="953" class="Symbol">)</a>
  <a id="957" class="Symbol">(</a><a id="958" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#958" class="Bound">Dᵉ</a> <a id="961" class="Symbol">:</a> <a id="963" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="976" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#908" class="Bound">l3ᵉ</a> <a id="980" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#912" class="Bound">l4ᵉ</a><a id="983" class="Symbol">)</a>
  <a id="987" class="Symbol">(</a><a id="988" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#988" class="Bound">Fᵉ</a> <a id="991" class="Symbol">:</a> <a id="993" href="category-theory.maps-precategories%25E1%25B5%2589.html#1332" class="Function">map-Precategoryᵉ</a> <a id="1010" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#928" class="Bound">Cᵉ</a> <a id="1013" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#958" class="Bound">Dᵉ</a><a id="1015" class="Symbol">)</a>
  <a id="1019" class="Keyword">where</a>

  <a id="1028" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1028" class="Function">is-full-map-Precategoryᵉ</a> <a id="1053" class="Symbol">:</a> <a id="1055" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1059" class="Symbol">(</a><a id="1060" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#900" class="Bound">l1ᵉ</a> <a id="1064" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1066" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#904" class="Bound">l2ᵉ</a> <a id="1070" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1072" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#912" class="Bound">l4ᵉ</a><a id="1075" class="Symbol">)</a>
  <a id="1079" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1028" class="Function">is-full-map-Precategoryᵉ</a> <a id="1104" class="Symbol">=</a>
    <a id="1110" class="Symbol">(</a><a id="1111" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1111" class="Bound">xᵉ</a> <a id="1114" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1114" class="Bound">yᵉ</a> <a id="1117" class="Symbol">:</a> <a id="1119" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="1136" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#928" class="Bound">Cᵉ</a><a id="1138" class="Symbol">)</a> <a id="1140" class="Symbol">→</a>
    <a id="1146" href="foundation.surjective-maps%25E1%25B5%2589.html#2409" class="Function">is-surjectiveᵉ</a> <a id="1161" class="Symbol">(</a><a id="1162" href="category-theory.maps-precategories%25E1%25B5%2589.html#1720" class="Function">hom-map-Precategoryᵉ</a> <a id="1183" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#928" class="Bound">Cᵉ</a> <a id="1186" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#958" class="Bound">Dᵉ</a> <a id="1189" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#988" class="Bound">Fᵉ</a> <a id="1192" class="Symbol">{</a><a id="1193" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1111" class="Bound">xᵉ</a><a id="1195" class="Symbol">}</a> <a id="1197" class="Symbol">{</a><a id="1198" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1114" class="Bound">yᵉ</a><a id="1200" class="Symbol">})</a>

  <a id="1206" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1206" class="Function">is-prop-is-full-map-Precategoryᵉ</a> <a id="1239" class="Symbol">:</a> <a id="1241" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="1250" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1028" class="Function">is-full-map-Precategoryᵉ</a>
  <a id="1277" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1206" class="Function">is-prop-is-full-map-Precategoryᵉ</a> <a id="1310" class="Symbol">=</a>
    <a id="1316" href="foundation.iterated-dependent-product-types%25E1%25B5%2589.html#5846" class="Function">is-prop-iterated-Πᵉ</a> <a id="1336" href="elementary-number-theory.natural-numbers%25E1%25B5%2589.html#892" class="Function">2ᵉ</a>
      <a id="1345" class="Symbol">(</a> <a id="1347" class="Symbol">λ</a> <a id="1349" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1349" class="Bound">xᵉ</a> <a id="1352" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1352" class="Bound">yᵉ</a> <a id="1355" class="Symbol">→</a> <a id="1357" href="foundation.surjective-maps%25E1%25B5%2589.html#2563" class="Function">is-prop-is-surjectiveᵉ</a> <a id="1380" class="Symbol">(</a><a id="1381" href="category-theory.maps-precategories%25E1%25B5%2589.html#1720" class="Function">hom-map-Precategoryᵉ</a> <a id="1402" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#928" class="Bound">Cᵉ</a> <a id="1405" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#958" class="Bound">Dᵉ</a> <a id="1408" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#988" class="Bound">Fᵉ</a> <a id="1411" class="Symbol">{</a><a id="1412" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1349" class="Bound">xᵉ</a><a id="1414" class="Symbol">}</a> <a id="1416" class="Symbol">{</a><a id="1417" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1352" class="Bound">yᵉ</a><a id="1419" class="Symbol">}))</a>

  <a id="1426" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1426" class="Function">is-full-prop-map-Precategoryᵉ</a> <a id="1456" class="Symbol">:</a> <a id="1458" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="1464" class="Symbol">(</a><a id="1465" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#900" class="Bound">l1ᵉ</a> <a id="1469" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1471" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#904" class="Bound">l2ᵉ</a> <a id="1475" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1477" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#912" class="Bound">l4ᵉ</a><a id="1480" class="Symbol">)</a>
  <a id="1484" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="1489" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1426" class="Function">is-full-prop-map-Precategoryᵉ</a> <a id="1519" class="Symbol">=</a> <a id="1521" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1028" class="Function">is-full-map-Precategoryᵉ</a>
  <a id="1548" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="1553" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1426" class="Function">is-full-prop-map-Precategoryᵉ</a> <a id="1583" class="Symbol">=</a> <a id="1585" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1206" class="Function">is-prop-is-full-map-Precategoryᵉ</a>
</pre>
### The type of full maps between two precategories

<pre class="Agda"><a id="1684" class="Keyword">module</a> <a id="1691" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1691" class="Module">_</a>
  <a id="1695" class="Symbol">{</a><a id="1696" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1696" class="Bound">l1ᵉ</a> <a id="1700" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1700" class="Bound">l2ᵉ</a> <a id="1704" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1704" class="Bound">l3ᵉ</a> <a id="1708" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1708" class="Bound">l4ᵉ</a> <a id="1712" class="Symbol">:</a> <a id="1714" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1719" class="Symbol">}</a>
  <a id="1723" class="Symbol">(</a><a id="1724" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1724" class="Bound">Cᵉ</a> <a id="1727" class="Symbol">:</a> <a id="1729" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="1742" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1696" class="Bound">l1ᵉ</a> <a id="1746" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1700" class="Bound">l2ᵉ</a><a id="1749" class="Symbol">)</a>
  <a id="1753" class="Symbol">(</a><a id="1754" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1754" class="Bound">Dᵉ</a> <a id="1757" class="Symbol">:</a> <a id="1759" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="1772" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1704" class="Bound">l3ᵉ</a> <a id="1776" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1708" class="Bound">l4ᵉ</a><a id="1779" class="Symbol">)</a>
  <a id="1783" class="Keyword">where</a>

  <a id="1792" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1792" class="Function">full-map-Precategoryᵉ</a> <a id="1814" class="Symbol">:</a> <a id="1816" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1820" class="Symbol">(</a><a id="1821" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1696" class="Bound">l1ᵉ</a> <a id="1825" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1827" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1700" class="Bound">l2ᵉ</a> <a id="1831" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1833" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1704" class="Bound">l3ᵉ</a> <a id="1837" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1839" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1708" class="Bound">l4ᵉ</a><a id="1842" class="Symbol">)</a>
  <a id="1846" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1792" class="Function">full-map-Precategoryᵉ</a> <a id="1868" class="Symbol">=</a>
    <a id="1874" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="1877" class="Symbol">(</a><a id="1878" href="category-theory.maps-precategories%25E1%25B5%2589.html#1332" class="Function">map-Precategoryᵉ</a> <a id="1895" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1724" class="Bound">Cᵉ</a> <a id="1898" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1754" class="Bound">Dᵉ</a><a id="1900" class="Symbol">)</a> <a id="1902" class="Symbol">(</a><a id="1903" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1028" class="Function">is-full-map-Precategoryᵉ</a> <a id="1928" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1724" class="Bound">Cᵉ</a> <a id="1931" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1754" class="Bound">Dᵉ</a><a id="1933" class="Symbol">)</a>

  <a id="1938" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1938" class="Function">map-full-map-Precategoryᵉ</a> <a id="1964" class="Symbol">:</a>
    <a id="1970" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1792" class="Function">full-map-Precategoryᵉ</a> <a id="1992" class="Symbol">→</a> <a id="1994" href="category-theory.maps-precategories%25E1%25B5%2589.html#1332" class="Function">map-Precategoryᵉ</a> <a id="2011" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1724" class="Bound">Cᵉ</a> <a id="2014" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1754" class="Bound">Dᵉ</a>
  <a id="2019" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1938" class="Function">map-full-map-Precategoryᵉ</a> <a id="2045" class="Symbol">=</a> <a id="2047" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a>

  <a id="2055" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2055" class="Function">is-full-full-map-Precategoryᵉ</a> <a id="2085" class="Symbol">:</a>
    <a id="2091" class="Symbol">(</a><a id="2092" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2092" class="Bound">Fᵉ</a> <a id="2095" class="Symbol">:</a> <a id="2097" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1792" class="Function">full-map-Precategoryᵉ</a><a id="2118" class="Symbol">)</a> <a id="2120" class="Symbol">→</a>
    <a id="2126" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1028" class="Function">is-full-map-Precategoryᵉ</a> <a id="2151" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1724" class="Bound">Cᵉ</a> <a id="2154" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1754" class="Bound">Dᵉ</a> <a id="2157" class="Symbol">(</a><a id="2158" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1938" class="Function">map-full-map-Precategoryᵉ</a> <a id="2184" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2092" class="Bound">Fᵉ</a><a id="2186" class="Symbol">)</a>
  <a id="2190" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2055" class="Function">is-full-full-map-Precategoryᵉ</a> <a id="2220" class="Symbol">=</a> <a id="2222" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a>

  <a id="2230" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2230" class="Function">obj-full-map-Precategoryᵉ</a> <a id="2256" class="Symbol">:</a>
    <a id="2262" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1792" class="Function">full-map-Precategoryᵉ</a> <a id="2284" class="Symbol">→</a> <a id="2286" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="2303" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1724" class="Bound">Cᵉ</a> <a id="2306" class="Symbol">→</a> <a id="2308" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="2325" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1754" class="Bound">Dᵉ</a>
  <a id="2330" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2230" class="Function">obj-full-map-Precategoryᵉ</a> <a id="2356" class="Symbol">=</a>
    <a id="2362" href="category-theory.maps-precategories%25E1%25B5%2589.html#1498" class="Function">obj-map-Precategoryᵉ</a> <a id="2383" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1724" class="Bound">Cᵉ</a> <a id="2386" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1754" class="Bound">Dᵉ</a> <a id="2389" href="foundation-core.function-types%25E1%25B5%2589.html#476" class="Function Operator">∘ᵉ</a> <a id="2392" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1938" class="Function">map-full-map-Precategoryᵉ</a>

  <a id="2421" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2421" class="Function">hom-full-map-Precategoryᵉ</a> <a id="2447" class="Symbol">:</a>
    <a id="2453" class="Symbol">(</a><a id="2454" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2454" class="Bound">Fᵉ</a> <a id="2457" class="Symbol">:</a> <a id="2459" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1792" class="Function">full-map-Precategoryᵉ</a><a id="2480" class="Symbol">)</a> <a id="2482" class="Symbol">{</a><a id="2483" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2483" class="Bound">xᵉ</a> <a id="2486" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2486" class="Bound">yᵉ</a> <a id="2489" class="Symbol">:</a> <a id="2491" href="category-theory.precategories%25E1%25B5%2589.html#4836" class="Function">obj-Precategoryᵉ</a> <a id="2508" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1724" class="Bound">Cᵉ</a><a id="2510" class="Symbol">}</a> <a id="2512" class="Symbol">→</a>
    <a id="2518" href="category-theory.precategories%25E1%25B5%2589.html#4999" class="Function">hom-Precategoryᵉ</a> <a id="2535" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1724" class="Bound">Cᵉ</a> <a id="2538" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2483" class="Bound">xᵉ</a> <a id="2541" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2486" class="Bound">yᵉ</a> <a id="2544" class="Symbol">→</a>
    <a id="2550" href="category-theory.precategories%25E1%25B5%2589.html#4999" class="Function">hom-Precategoryᵉ</a> <a id="2567" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1754" class="Bound">Dᵉ</a>
      <a id="2576" class="Symbol">(</a> <a id="2578" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2230" class="Function">obj-full-map-Precategoryᵉ</a> <a id="2604" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2454" class="Bound">Fᵉ</a> <a id="2607" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2483" class="Bound">xᵉ</a><a id="2609" class="Symbol">)</a>
      <a id="2617" class="Symbol">(</a> <a id="2619" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2230" class="Function">obj-full-map-Precategoryᵉ</a> <a id="2645" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2454" class="Bound">Fᵉ</a> <a id="2648" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2486" class="Bound">yᵉ</a><a id="2650" class="Symbol">)</a>
  <a id="2654" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#2421" class="Function">hom-full-map-Precategoryᵉ</a> <a id="2680" class="Symbol">=</a>
    <a id="2686" href="category-theory.maps-precategories%25E1%25B5%2589.html#1720" class="Function">hom-map-Precategoryᵉ</a> <a id="2707" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1724" class="Bound">Cᵉ</a> <a id="2710" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1754" class="Bound">Dᵉ</a> <a id="2713" href="foundation-core.function-types%25E1%25B5%2589.html#476" class="Function Operator">∘ᵉ</a> <a id="2716" href="category-theory.full-maps-precategories%25E1%25B5%2589.html#1938" class="Function">map-full-map-Precategoryᵉ</a>
</pre>