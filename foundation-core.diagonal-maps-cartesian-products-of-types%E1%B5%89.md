# Diagonal maps into cartesian products of types

<pre class="Agda"><a id="59" class="Keyword">module</a> <a id="66" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html" class="Module">foundation-core.diagonal-maps-cartesian-products-of-typesᵉ</a> <a id="125" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="181" class="Keyword">open</a> <a id="186" class="Keyword">import</a> <a id="193" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-functionsᵉ</a>
<a id="241" class="Keyword">open</a> <a id="246" class="Keyword">import</a> <a id="253" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="foundation.equality-cartesian-product-types%25E1%25B5%2589.html" class="Module">foundation.equality-cartesian-product-typesᵉ</a>
<a id="343" class="Keyword">open</a> <a id="348" class="Keyword">import</a> <a id="355" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="384" class="Keyword">open</a> <a id="389" class="Keyword">import</a> <a id="396" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html" class="Module">foundation-core.cartesian-product-typesᵉ</a>
<a id="437" class="Keyword">open</a> <a id="442" class="Keyword">import</a> <a id="449" href="foundation-core.equivalences%25E1%25B5%2589.html" class="Module">foundation-core.equivalencesᵉ</a>
<a id="479" class="Keyword">open</a> <a id="484" class="Keyword">import</a> <a id="491" href="foundation-core.fibers-of-maps%25E1%25B5%2589.html" class="Module">foundation-core.fibers-of-mapsᵉ</a>
<a id="523" class="Keyword">open</a> <a id="528" class="Keyword">import</a> <a id="535" href="foundation-core.function-types%25E1%25B5%2589.html" class="Module">foundation-core.function-typesᵉ</a>
<a id="567" class="Keyword">open</a> <a id="572" class="Keyword">import</a> <a id="579" href="foundation-core.homotopies%25E1%25B5%2589.html" class="Module">foundation-core.homotopiesᵉ</a>
<a id="607" class="Keyword">open</a> <a id="612" class="Keyword">import</a> <a id="619" href="foundation-core.identity-types%25E1%25B5%2589.html" class="Module">foundation-core.identity-typesᵉ</a>
<a id="651" class="Keyword">open</a> <a id="656" class="Keyword">import</a> <a id="663" href="foundation-core.propositions%25E1%25B5%2589.html" class="Module">foundation-core.propositionsᵉ</a>
<a id="693" class="Keyword">open</a> <a id="698" class="Keyword">import</a> <a id="705" href="foundation-core.retractions%25E1%25B5%2589.html" class="Module">foundation-core.retractionsᵉ</a>
<a id="734" class="Keyword">open</a> <a id="739" class="Keyword">import</a> <a id="746" href="foundation-core.sections%25E1%25B5%2589.html" class="Module">foundation-core.sectionsᵉ</a>
</pre>
</details>

## Idea

The
{{#concept "diagonal map" Disambiguation="of a type into its cartesian product" Agda=diagonal-product}}
that includes a type `A` into its
[cartesian product](foundation-core.cartesian-product-types.md) `A × A` is the
map that maps `x` to the pair `(x , x)`.

## Definition

<pre class="Agda"><a id="1084" class="Keyword">module</a> <a id="1091" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1091" class="Module">_</a>
  <a id="1095" class="Symbol">{</a><a id="1096" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1096" class="Bound">lᵉ</a> <a id="1099" class="Symbol">:</a> <a id="1101" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1106" class="Symbol">}</a> <a id="1108" class="Symbol">(</a><a id="1109" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1109" class="Bound">Aᵉ</a> <a id="1112" class="Symbol">:</a> <a id="1114" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1118" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1096" class="Bound">lᵉ</a><a id="1120" class="Symbol">)</a>
  <a id="1124" class="Keyword">where</a>

  <a id="1133" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1133" class="Function">diagonal-productᵉ</a> <a id="1151" class="Symbol">:</a> <a id="1153" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1109" class="Bound">Aᵉ</a> <a id="1156" class="Symbol">→</a> <a id="1158" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1109" class="Bound">Aᵉ</a> <a id="1161" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">×ᵉ</a> <a id="1164" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1109" class="Bound">Aᵉ</a>
  <a id="1169" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1133" class="Function">diagonal-productᵉ</a> <a id="1187" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1187" class="Bound">xᵉ</a> <a id="1190" class="Symbol">=</a> <a id="1192" class="Symbol">(</a><a id="1193" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1187" class="Bound">xᵉ</a> <a id="1196" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="1199" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1187" class="Bound">xᵉ</a><a id="1201" class="Symbol">)</a>
</pre>
## Properties

### The action on paths of a diagonal

<pre class="Agda"><a id="compute-ap-diagonal-productᵉ"></a><a id="1270" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1270" class="Function">compute-ap-diagonal-productᵉ</a> <a id="1299" class="Symbol">:</a>
  <a id="1303" class="Symbol">{</a><a id="1304" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1304" class="Bound">lᵉ</a> <a id="1307" class="Symbol">:</a> <a id="1309" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1314" class="Symbol">}</a> <a id="1316" class="Symbol">{</a><a id="1317" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1317" class="Bound">Aᵉ</a> <a id="1320" class="Symbol">:</a> <a id="1322" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1326" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1304" class="Bound">lᵉ</a><a id="1328" class="Symbol">}</a> <a id="1330" class="Symbol">{</a><a id="1331" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1331" class="Bound">xᵉ</a> <a id="1334" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1334" class="Bound">yᵉ</a> <a id="1337" class="Symbol">:</a> <a id="1339" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1317" class="Bound">Aᵉ</a><a id="1341" class="Symbol">}</a> <a id="1343" class="Symbol">(</a><a id="1344" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1344" class="Bound">pᵉ</a> <a id="1347" class="Symbol">:</a> <a id="1349" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1331" class="Bound">xᵉ</a> <a id="1352" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="1355" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1334" class="Bound">yᵉ</a><a id="1357" class="Symbol">)</a> <a id="1359" class="Symbol">→</a>
  <a id="1363" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="1367" class="Symbol">(</a><a id="1368" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1133" class="Function">diagonal-productᵉ</a> <a id="1386" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1317" class="Bound">Aᵉ</a><a id="1388" class="Symbol">)</a> <a id="1390" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1344" class="Bound">pᵉ</a> <a id="1393" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="1396" href="foundation.equality-cartesian-product-types%25E1%25B5%2589.html#1360" class="Function">eq-pairᵉ</a> <a id="1405" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1344" class="Bound">pᵉ</a> <a id="1408" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1344" class="Bound">pᵉ</a>
<a id="1411" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1270" class="Function">compute-ap-diagonal-productᵉ</a> <a id="1440" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a> <a id="1446" class="Symbol">=</a> <a id="1448" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a>
</pre>
### If the diagonal of `A` is an equivalence, then `A` is a proposition

<pre class="Agda"><a id="1540" class="Keyword">module</a> <a id="1547" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1547" class="Module">_</a>
  <a id="1551" class="Symbol">{</a><a id="1552" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1552" class="Bound">lᵉ</a> <a id="1555" class="Symbol">:</a> <a id="1557" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1562" class="Symbol">}</a> <a id="1564" class="Symbol">(</a><a id="1565" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1565" class="Bound">Aᵉ</a> <a id="1568" class="Symbol">:</a> <a id="1570" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1574" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1552" class="Bound">lᵉ</a><a id="1576" class="Symbol">)</a>
  <a id="1580" class="Keyword">where</a>

  <a id="1589" class="Keyword">abstract</a>
    <a id="1602" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1602" class="Function">is-prop-is-equiv-diagonal-productᵉ</a> <a id="1637" class="Symbol">:</a>
      <a id="1645" href="foundation-core.equivalences%25E1%25B5%2589.html#1553" class="Function">is-equivᵉ</a> <a id="1655" class="Symbol">(</a><a id="1656" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1133" class="Function">diagonal-productᵉ</a> <a id="1674" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1565" class="Bound">Aᵉ</a><a id="1676" class="Symbol">)</a> <a id="1678" class="Symbol">→</a> <a id="1680" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="1689" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1565" class="Bound">Aᵉ</a>
    <a id="1696" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1602" class="Function">is-prop-is-equiv-diagonal-productᵉ</a> <a id="1731" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1731" class="Bound">is-equiv-dᵉ</a> <a id="1743" class="Symbol">=</a>
      <a id="1751" href="foundation-core.propositions%25E1%25B5%2589.html#2312" class="Function">is-prop-all-elements-equalᵉ</a>
        <a id="1787" class="Symbol">(</a> <a id="1789" class="Symbol">λ</a> <a id="1791" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1791" class="Bound">xᵉ</a> <a id="1794" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1794" class="Bound">yᵉ</a> <a id="1797" class="Symbol">→</a>
          <a id="1809" class="Symbol">(</a> <a id="1811" href="foundation-core.identity-types%25E1%25B5%2589.html#6276" class="Function">invᵉ</a> <a id="1816" class="Symbol">(</a><a id="1817" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="1821" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="1826" class="Symbol">(</a><a id="1827" href="foundation-core.equivalences%25E1%25B5%2589.html#7470" class="Function">is-section-map-inv-is-equivᵉ</a> <a id="1856" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1731" class="Bound">is-equiv-dᵉ</a> <a id="1868" class="Symbol">(</a><a id="1869" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1791" class="Bound">xᵉ</a> <a id="1872" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="1875" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1794" class="Bound">yᵉ</a><a id="1877" class="Symbol">))))</a> <a id="1882" href="foundation-core.identity-types%25E1%25B5%2589.html#5906" class="Function Operator">∙ᵉ</a>
          <a id="1895" class="Symbol">(</a> <a id="1897" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="1901" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="1906" class="Symbol">(</a><a id="1907" href="foundation-core.equivalences%25E1%25B5%2589.html#7470" class="Function">is-section-map-inv-is-equivᵉ</a> <a id="1936" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1731" class="Bound">is-equiv-dᵉ</a> <a id="1948" class="Symbol">(</a><a id="1949" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1791" class="Bound">xᵉ</a> <a id="1952" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="1955" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1794" class="Bound">yᵉ</a><a id="1957" class="Symbol">))))</a>

  <a id="1965" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1965" class="Function">equiv-diagonal-product-is-propᵉ</a> <a id="1997" class="Symbol">:</a>
    <a id="2003" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="2012" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1565" class="Bound">Aᵉ</a> <a id="2015" class="Symbol">→</a> <a id="2017" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1565" class="Bound">Aᵉ</a> <a id="2020" href="foundation-core.equivalences%25E1%25B5%2589.html#2662" class="Function Operator">≃ᵉ</a> <a id="2023" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1565" class="Bound">Aᵉ</a> <a id="2026" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">×ᵉ</a> <a id="2029" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1565" class="Bound">Aᵉ</a>
  <a id="2034" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2039" class="Symbol">(</a><a id="2040" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1965" class="Function">equiv-diagonal-product-is-propᵉ</a> <a id="2072" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2072" class="Bound">is-prop-Aᵉ</a><a id="2082" class="Symbol">)</a> <a id="2084" class="Symbol">=</a>
    <a id="2090" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1133" class="Function">diagonal-productᵉ</a> <a id="2108" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1565" class="Bound">Aᵉ</a>
  <a id="2113" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2118" class="Symbol">(</a><a id="2119" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1965" class="Function">equiv-diagonal-product-is-propᵉ</a> <a id="2151" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2151" class="Bound">is-prop-Aᵉ</a><a id="2161" class="Symbol">)</a> <a id="2163" class="Symbol">=</a>
    <a id="2169" href="foundation-core.equivalences%25E1%25B5%2589.html#5107" class="Function">is-equiv-is-invertibleᵉ</a>
      <a id="2199" class="Symbol">(</a> <a id="2201" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a><a id="2205" class="Symbol">)</a>
      <a id="2213" class="Symbol">(</a> <a id="2215" class="Symbol">λ</a> <a id="2217" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2217" class="Bound">_</a> <a id="2219" class="Symbol">→</a> <a id="2221" href="foundation.equality-cartesian-product-types%25E1%25B5%2589.html#1360" class="Function">eq-pairᵉ</a> <a id="2230" class="Symbol">(</a><a id="2231" href="foundation-core.propositions%25E1%25B5%2589.html#2667" class="Function">eq-is-propᵉ</a> <a id="2243" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2151" class="Bound">is-prop-Aᵉ</a><a id="2253" class="Symbol">)</a> <a id="2255" class="Symbol">(</a><a id="2256" href="foundation-core.propositions%25E1%25B5%2589.html#2667" class="Function">eq-is-propᵉ</a> <a id="2268" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2151" class="Bound">is-prop-Aᵉ</a><a id="2278" class="Symbol">))</a>
      <a id="2287" class="Symbol">(</a> <a id="2289" class="Symbol">λ</a> <a id="2291" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2291" class="Bound">aᵉ</a> <a id="2294" class="Symbol">→</a> <a id="2296" href="foundation-core.propositions%25E1%25B5%2589.html#2667" class="Function">eq-is-propᵉ</a> <a id="2308" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2151" class="Bound">is-prop-Aᵉ</a><a id="2318" class="Symbol">)</a>
</pre>
### The fibers of the diagonal map

<pre class="Agda"><a id="2369" class="Keyword">module</a> <a id="2376" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2376" class="Module">_</a>
  <a id="2380" class="Symbol">{</a><a id="2381" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2381" class="Bound">lᵉ</a> <a id="2384" class="Symbol">:</a> <a id="2386" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2391" class="Symbol">}</a> <a id="2393" class="Symbol">(</a><a id="2394" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2394" class="Bound">Aᵉ</a> <a id="2397" class="Symbol">:</a> <a id="2399" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2403" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2381" class="Bound">lᵉ</a><a id="2405" class="Symbol">)</a>
  <a id="2409" class="Keyword">where</a>

  <a id="2418" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2418" class="Function">eq-fiber-diagonal-productᵉ</a> <a id="2445" class="Symbol">:</a>
    <a id="2451" class="Symbol">(</a><a id="2452" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2452" class="Bound">tᵉ</a> <a id="2455" class="Symbol">:</a> <a id="2457" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2394" class="Bound">Aᵉ</a> <a id="2460" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">×ᵉ</a> <a id="2463" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2394" class="Bound">Aᵉ</a><a id="2465" class="Symbol">)</a> <a id="2467" class="Symbol">→</a> <a id="2469" href="foundation-core.fibers-of-maps%25E1%25B5%2589.html#962" class="Function">fiberᵉ</a> <a id="2476" class="Symbol">(</a><a id="2477" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1133" class="Function">diagonal-productᵉ</a> <a id="2495" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2394" class="Bound">Aᵉ</a><a id="2497" class="Symbol">)</a> <a id="2499" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2452" class="Bound">tᵉ</a> <a id="2502" class="Symbol">→</a> <a id="2504" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2509" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2452" class="Bound">tᵉ</a> <a id="2512" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="2515" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2520" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2452" class="Bound">tᵉ</a>
  <a id="2525" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2418" class="Function">eq-fiber-diagonal-productᵉ</a> <a id="2552" class="Symbol">(</a><a id="2553" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2553" class="Bound">xᵉ</a> <a id="2556" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2559" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2559" class="Bound">yᵉ</a><a id="2561" class="Symbol">)</a> <a id="2563" class="Symbol">(</a><a id="2564" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2564" class="Bound">zᵉ</a> <a id="2567" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2570" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2570" class="Bound">αᵉ</a><a id="2572" class="Symbol">)</a> <a id="2574" class="Symbol">=</a> <a id="2576" href="foundation-core.identity-types%25E1%25B5%2589.html#6276" class="Function">invᵉ</a> <a id="2581" class="Symbol">(</a><a id="2582" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="2586" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2591" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2570" class="Bound">αᵉ</a><a id="2593" class="Symbol">)</a> <a id="2595" href="foundation-core.identity-types%25E1%25B5%2589.html#5906" class="Function Operator">∙ᵉ</a> <a id="2598" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="2602" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2607" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2570" class="Bound">αᵉ</a>

  <a id="2613" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2613" class="Function">fiber-diagonal-product-eqᵉ</a> <a id="2640" class="Symbol">:</a>
    <a id="2646" class="Symbol">(</a><a id="2647" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2647" class="Bound">tᵉ</a> <a id="2650" class="Symbol">:</a> <a id="2652" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2394" class="Bound">Aᵉ</a> <a id="2655" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">×ᵉ</a> <a id="2658" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2394" class="Bound">Aᵉ</a><a id="2660" class="Symbol">)</a> <a id="2662" class="Symbol">→</a> <a id="2664" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2669" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2647" class="Bound">tᵉ</a> <a id="2672" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="2675" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2680" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2647" class="Bound">tᵉ</a> <a id="2683" class="Symbol">→</a> <a id="2685" href="foundation-core.fibers-of-maps%25E1%25B5%2589.html#962" class="Function">fiberᵉ</a> <a id="2692" class="Symbol">(</a><a id="2693" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#1133" class="Function">diagonal-productᵉ</a> <a id="2711" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2394" class="Bound">Aᵉ</a><a id="2713" class="Symbol">)</a> <a id="2715" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2647" class="Bound">tᵉ</a>
  <a id="2720" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2613" class="Function">fiber-diagonal-product-eqᵉ</a> <a id="2747" class="Symbol">(</a><a id="2748" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2748" class="Bound">xᵉ</a> <a id="2751" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2754" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2754" class="Bound">yᵉ</a><a id="2756" class="Symbol">)</a> <a id="2758" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2758" class="Bound">βᵉ</a> <a id="2761" class="Symbol">=</a> <a id="2763" class="Symbol">(</a><a id="2764" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2748" class="Bound">xᵉ</a> <a id="2767" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2770" href="foundation.equality-cartesian-product-types%25E1%25B5%2589.html#1360" class="Function">eq-pairᵉ</a> <a id="2779" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a> <a id="2785" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2758" class="Bound">βᵉ</a><a id="2787" class="Symbol">)</a>

  <a id="2792" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2792" class="Function">is-section-fiber-diagonal-product-eqᵉ</a> <a id="2830" class="Symbol">:</a>
    <a id="2836" class="Symbol">(</a><a id="2837" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2837" class="Bound">tᵉ</a> <a id="2840" class="Symbol">:</a> <a id="2842" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2394" class="Bound">Aᵉ</a> <a id="2845" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">×ᵉ</a> <a id="2848" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2394" class="Bound">Aᵉ</a><a id="2850" class="Symbol">)</a> <a id="2852" class="Symbol">→</a>
    <a id="2858" href="foundation-core.sections%25E1%25B5%2589.html#1211" class="Function">is-sectionᵉ</a> <a id="2870" class="Symbol">(</a><a id="2871" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2418" class="Function">eq-fiber-diagonal-productᵉ</a> <a id="2898" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2837" class="Bound">tᵉ</a><a id="2900" class="Symbol">)</a> <a id="2902" class="Symbol">(</a><a id="2903" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2613" class="Function">fiber-diagonal-product-eqᵉ</a> <a id="2930" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2837" class="Bound">tᵉ</a><a id="2932" class="Symbol">)</a>
  <a id="2936" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2792" class="Function">is-section-fiber-diagonal-product-eqᵉ</a> <a id="2974" class="Symbol">(</a><a id="2975" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2975" class="Bound">xᵉ</a> <a id="2978" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2981" class="DottedPattern Symbol">.</a><a id="2982" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2975" class="DottedPattern Bound">xᵉ</a><a id="2984" class="Symbol">)</a> <a id="2986" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a> <a id="2992" class="Symbol">=</a> <a id="2994" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a>

  <a id="3003" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3003" class="Function">is-retraction-fiber-diagonal-product-eqᵉ</a> <a id="3044" class="Symbol">:</a>
    <a id="3050" class="Symbol">(</a><a id="3051" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3051" class="Bound">tᵉ</a> <a id="3054" class="Symbol">:</a> <a id="3056" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2394" class="Bound">Aᵉ</a> <a id="3059" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">×ᵉ</a> <a id="3062" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2394" class="Bound">Aᵉ</a><a id="3064" class="Symbol">)</a> <a id="3066" class="Symbol">→</a>
    <a id="3072" href="foundation-core.retractions%25E1%25B5%2589.html#806" class="Function">is-retractionᵉ</a> <a id="3087" class="Symbol">(</a><a id="3088" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2418" class="Function">eq-fiber-diagonal-productᵉ</a> <a id="3115" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3051" class="Bound">tᵉ</a><a id="3117" class="Symbol">)</a> <a id="3119" class="Symbol">(</a><a id="3120" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2613" class="Function">fiber-diagonal-product-eqᵉ</a> <a id="3147" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3051" class="Bound">tᵉ</a><a id="3149" class="Symbol">)</a>
  <a id="3153" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3003" class="Function">is-retraction-fiber-diagonal-product-eqᵉ</a> <a id="3194" class="DottedPattern Symbol">.(</a><a id="3196" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3207" class="DottedPattern Bound">zᵉ</a> <a id="3199" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="DottedPattern InductiveConstructor Operator">,ᵉ</a> <a id="3202" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3207" class="DottedPattern Bound">zᵉ</a><a id="3204" class="DottedPattern Symbol">)</a> <a id="3206" class="Symbol">(</a><a id="3207" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3207" class="Bound">zᵉ</a> <a id="3210" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="3213" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a><a id="3218" class="Symbol">)</a> <a id="3220" class="Symbol">=</a> <a id="3222" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a>

  <a id="3231" class="Keyword">abstract</a>
    <a id="3244" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3244" class="Function">is-equiv-eq-fiber-diagonal-productᵉ</a> <a id="3280" class="Symbol">:</a>
      <a id="3288" class="Symbol">(</a><a id="3289" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3289" class="Bound">tᵉ</a> <a id="3292" class="Symbol">:</a> <a id="3294" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2394" class="Bound">Aᵉ</a> <a id="3297" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">×ᵉ</a> <a id="3300" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2394" class="Bound">Aᵉ</a><a id="3302" class="Symbol">)</a> <a id="3304" class="Symbol">→</a> <a id="3306" href="foundation-core.equivalences%25E1%25B5%2589.html#1553" class="Function">is-equivᵉ</a> <a id="3316" class="Symbol">(</a><a id="3317" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2418" class="Function">eq-fiber-diagonal-productᵉ</a> <a id="3344" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3289" class="Bound">tᵉ</a><a id="3346" class="Symbol">)</a>
    <a id="3352" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3244" class="Function">is-equiv-eq-fiber-diagonal-productᵉ</a> <a id="3388" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3388" class="Bound">tᵉ</a> <a id="3391" class="Symbol">=</a>
      <a id="3399" href="foundation-core.equivalences%25E1%25B5%2589.html#5107" class="Function">is-equiv-is-invertibleᵉ</a>
        <a id="3431" class="Symbol">(</a> <a id="3433" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2613" class="Function">fiber-diagonal-product-eqᵉ</a> <a id="3460" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3388" class="Bound">tᵉ</a><a id="3462" class="Symbol">)</a>
        <a id="3472" class="Symbol">(</a> <a id="3474" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#2792" class="Function">is-section-fiber-diagonal-product-eqᵉ</a> <a id="3512" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3388" class="Bound">tᵉ</a><a id="3514" class="Symbol">)</a>
        <a id="3524" class="Symbol">(</a> <a id="3526" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3003" class="Function">is-retraction-fiber-diagonal-product-eqᵉ</a> <a id="3567" href="foundation-core.diagonal-maps-cartesian-products-of-types%25E1%25B5%2589.html#3388" class="Bound">tᵉ</a><a id="3569" class="Symbol">)</a>
</pre>