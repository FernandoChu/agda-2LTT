# Cofibrations

<pre class="Agda"><a id="25" class="Keyword">module</a> <a id="32" href="foundation-2LTT.cofibrations.html" class="Module">foundation-2LTT.cofibrations</a> <a id="61" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="117" class="Keyword">open</a> <a id="122" class="Keyword">import</a> <a id="129" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-dependent-functionsᵉ</a>
<a id="187" class="Keyword">open</a> <a id="192" class="Keyword">import</a> <a id="199" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-functionsᵉ</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="foundation.cartesian-product-types%25E1%25B5%2589.html" class="Module">foundation.cartesian-product-typesᵉ</a>
<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="foundation.dependent-identifications%25E1%25B5%2589.html" class="Module">foundation.dependent-identificationsᵉ</a>
<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="432" class="Keyword">open</a> <a id="437" class="Keyword">import</a> <a id="444" href="foundation.equality-dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.equality-dependent-pair-typesᵉ</a>
<a id="486" class="Keyword">open</a> <a id="491" class="Keyword">import</a> <a id="498" href="foundation.equivalences%25E1%25B5%2589.html" class="Module">foundation.equivalencesᵉ</a>
<a id="523" class="Keyword">open</a> <a id="528" class="Keyword">import</a> <a id="535" href="foundation.fibers-of-maps%25E1%25B5%2589.html" class="Module">foundation.fibers-of-mapsᵉ</a>
<a id="562" class="Keyword">open</a> <a id="567" class="Keyword">import</a> <a id="574" href="foundation.function-extensionality%25E1%25B5%2589.html" class="Module">foundation.function-extensionalityᵉ</a>
<a id="610" class="Keyword">open</a> <a id="615" class="Keyword">import</a> <a id="622" href="foundation.function-types%25E1%25B5%2589.html" class="Module">foundation.function-typesᵉ</a>
<a id="649" class="Keyword">open</a> <a id="654" class="Keyword">import</a> <a id="661" href="foundation.functoriality-dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.functoriality-dependent-pair-typesᵉ</a>
<a id="708" class="Keyword">open</a> <a id="713" class="Keyword">import</a> <a id="720" href="foundation.homotopies-morphisms-arrows%25E1%25B5%2589.html" class="Module">foundation.homotopies-morphisms-arrowsᵉ</a>
<a id="760" class="Keyword">open</a> <a id="765" class="Keyword">import</a> <a id="772" href="foundation.homotopies%25E1%25B5%2589.html" class="Module">foundation.homotopiesᵉ</a>
<a id="795" class="Keyword">open</a> <a id="800" class="Keyword">import</a> <a id="807" href="foundation.identity-types%25E1%25B5%2589.html" class="Module">foundation.identity-typesᵉ</a>
<a id="834" class="Keyword">open</a> <a id="839" class="Keyword">import</a> <a id="846" href="foundation.morphisms-arrows%25E1%25B5%2589.html" class="Module">foundation.morphisms-arrowsᵉ</a>
<a id="875" class="Keyword">open</a> <a id="880" class="Keyword">import</a> <a id="887" href="foundation.pi-decompositions%25E1%25B5%2589.html" class="Module">foundation.pi-decompositionsᵉ</a>
<a id="917" class="Keyword">open</a> <a id="922" class="Keyword">import</a> <a id="929" href="foundation.pullbacks%25E1%25B5%2589.html" class="Module">foundation.pullbacksᵉ</a>
<a id="951" class="Keyword">open</a> <a id="956" class="Keyword">import</a> <a id="963" href="foundation.retractions%25E1%25B5%2589.html" class="Module">foundation.retractionsᵉ</a>
<a id="987" class="Keyword">open</a> <a id="992" class="Keyword">import</a> <a id="999" href="foundation.sections%25E1%25B5%2589.html" class="Module">foundation.sectionsᵉ</a>
<a id="1020" class="Keyword">open</a> <a id="1025" class="Keyword">import</a> <a id="1032" href="foundation.standard-pullbacks%25E1%25B5%2589.html" class="Module">foundation.standard-pullbacksᵉ</a>
<a id="1063" class="Keyword">open</a> <a id="1068" class="Keyword">import</a> <a id="1075" href="foundation.transport-along-identifications%25E1%25B5%2589.html" class="Module">foundation.transport-along-identificationsᵉ</a>
<a id="1119" class="Keyword">open</a> <a id="1124" class="Keyword">import</a> <a id="1131" href="foundation.unit-type%25E1%25B5%2589.html" class="Module">foundation.unit-typeᵉ</a>
<a id="1153" class="Keyword">open</a> <a id="1158" class="Keyword">import</a> <a id="1165" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="1192" class="Keyword">open</a> <a id="1197" class="Keyword">import</a> <a id="1204" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="1233" class="Keyword">open</a> <a id="1238" class="Keyword">import</a> <a id="1245" href="foundation-2LTT.exotypes.html" class="Module">foundation-2LTT.exotypes</a>
<a id="1270" class="Keyword">open</a> <a id="1275" class="Keyword">import</a> <a id="1282" href="foundation-2LTT.fibrant-types.html" class="Module">foundation-2LTT.fibrant-types</a>
<a id="1312" class="Keyword">open</a> <a id="1317" class="Keyword">import</a> <a id="1324" href="foundation-2LTT.fibrations.html" class="Module">foundation-2LTT.fibrations</a>

<a id="1352" class="Keyword">open</a> <a id="1357" class="Keyword">import</a> <a id="1364" href="orthogonal-factorization-systems.pullback-hom%25E1%25B5%2589.html" class="Module">orthogonal-factorization-systems.pullback-homᵉ</a>
</pre>
</details>

## Definition

<pre class="Agda"><a id="1451" class="Keyword">module</a> <a id="1458" href="foundation-2LTT.cofibrations.html#1458" class="Module">_</a>
  <a id="1462" class="Symbol">{</a><a id="1463" href="foundation-2LTT.cofibrations.html#1463" class="Bound">l1</a> <a id="1466" href="foundation-2LTT.cofibrations.html#1466" class="Bound">l2</a> <a id="1469" class="Symbol">:</a> <a id="1471" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1476" class="Symbol">}</a> <a id="1478" class="Symbol">{</a><a id="1479" href="foundation-2LTT.cofibrations.html#1479" class="Bound">A</a> <a id="1481" class="Symbol">:</a> <a id="1483" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1487" href="foundation-2LTT.cofibrations.html#1463" class="Bound">l1</a><a id="1489" class="Symbol">}</a> <a id="1491" class="Symbol">{</a><a id="1492" href="foundation-2LTT.cofibrations.html#1492" class="Bound">B</a> <a id="1494" class="Symbol">:</a> <a id="1496" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1500" href="foundation-2LTT.cofibrations.html#1466" class="Bound">l2</a><a id="1502" class="Symbol">}</a> <a id="1504" class="Symbol">(</a><a id="1505" href="foundation-2LTT.cofibrations.html#1505" class="Bound">f</a> <a id="1507" class="Symbol">:</a> <a id="1509" href="foundation-2LTT.cofibrations.html#1479" class="Bound">A</a> <a id="1511" class="Symbol">→</a> <a id="1513" href="foundation-2LTT.cofibrations.html#1492" class="Bound">B</a><a id="1514" class="Symbol">)</a>
  <a id="1518" class="Keyword">where</a>

  <a id="1527" href="foundation-2LTT.cofibrations.html#1527" class="Function">is-cofibration</a> <a id="1542" class="Symbol">:</a> <a id="1544" class="Symbol">(</a><a id="1545" href="foundation-2LTT.cofibrations.html#1545" class="Bound">l</a> <a id="1547" class="Symbol">:</a> <a id="1549" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1554" class="Symbol">)</a> <a id="1556" class="Symbol">→</a> <a id="1558" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1562" class="Symbol">(</a><a id="1563" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1568" href="foundation-2LTT.cofibrations.html#1463" class="Bound">l1</a> <a id="1571" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1573" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1578" href="foundation-2LTT.cofibrations.html#1466" class="Bound">l2</a> <a id="1581" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1583" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1588" href="foundation-2LTT.cofibrations.html#1545" class="Bound">l</a><a id="1589" class="Symbol">)</a>
  <a id="1593" href="foundation-2LTT.cofibrations.html#1527" class="Function">is-cofibration</a> <a id="1608" href="foundation-2LTT.cofibrations.html#1608" class="Bound">l</a> <a id="1610" class="Symbol">=</a>
    <a id="1616" class="Symbol">((</a><a id="1618" href="foundation-2LTT.cofibrations.html#1618" class="Bound">Y</a> <a id="1620" class="Symbol">:</a> <a id="1622" href="foundation-2LTT.cofibrations.html#1492" class="Bound">B</a> <a id="1624" class="Symbol">→</a> <a id="1626" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1629" href="foundation-2LTT.cofibrations.html#1608" class="Bound">l</a><a id="1630" class="Symbol">)</a> <a id="1632" class="Symbol">→</a>
    <a id="1638" href="foundation-2LTT.fibrations.html#756" class="Function">is-fibration</a>
      <a id="1657" class="Symbol">(λ</a> <a id="1660" class="Symbol">(</a><a id="1661" href="foundation-2LTT.cofibrations.html#1661" class="Bound">g</a> <a id="1663" class="Symbol">:</a> <a id="1665" class="Symbol">(</a><a id="1666" href="foundation-2LTT.cofibrations.html#1666" class="Bound">b</a> <a id="1668" class="Symbol">:</a> <a id="1670" href="foundation-2LTT.cofibrations.html#1492" class="Bound">B</a><a id="1671" class="Symbol">)</a> <a id="1673" class="Symbol">→</a> <a id="1675" href="foundation-2LTT.cofibrations.html#1618" class="Bound">Y</a> <a id="1677" href="foundation-2LTT.cofibrations.html#1666" class="Bound">b</a><a id="1678" class="Symbol">)</a> <a id="1680" class="Symbol">→</a> <a id="1682" class="Symbol">(</a><a id="1683" href="foundation-2LTT.cofibrations.html#1661" class="Bound">g</a> <a id="1685" href="foundation-2LTT.exotypes.html#1089" class="Function Operator">∘ᶠᵉᵉ</a> <a id="1690" href="foundation-2LTT.cofibrations.html#1505" class="Bound">f</a><a id="1691" class="Symbol">)))</a> <a id="1695" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">×ᵉ</a>
    <a id="1702" class="Symbol">((</a><a id="1704" href="foundation-2LTT.cofibrations.html#1704" class="Bound">Y</a> <a id="1706" class="Symbol">:</a> <a id="1708" href="foundation-2LTT.cofibrations.html#1492" class="Bound">B</a> <a id="1710" class="Symbol">→</a> <a id="1712" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1715" href="foundation-2LTT.cofibrations.html#1608" class="Bound">l</a><a id="1716" class="Symbol">)</a> <a id="1718" class="Symbol">→</a>
    <a id="1724" class="Symbol">((</a><a id="1726" href="foundation-2LTT.cofibrations.html#1726" class="Bound">b</a> <a id="1728" class="Symbol">:</a> <a id="1730" href="foundation-2LTT.cofibrations.html#1492" class="Bound">B</a><a id="1731" class="Symbol">)</a> <a id="1733" class="Symbol">→</a> <a id="1735" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="1744" class="Symbol">(</a><a id="1745" href="foundation-2LTT.cofibrations.html#1704" class="Bound">Y</a> <a id="1747" href="foundation-2LTT.cofibrations.html#1726" class="Bound">b</a><a id="1748" class="Symbol">))</a> <a id="1751" class="Symbol">→</a>
    <a id="1757" href="foundation-2LTT.fibrations.html#846" class="Function">is-trivial-fibration</a>
      <a id="1784" class="Symbol">(λ</a> <a id="1787" class="Symbol">(</a><a id="1788" href="foundation-2LTT.cofibrations.html#1788" class="Bound">g</a> <a id="1790" class="Symbol">:</a> <a id="1792" class="Symbol">(</a><a id="1793" href="foundation-2LTT.cofibrations.html#1793" class="Bound">b</a> <a id="1795" class="Symbol">:</a> <a id="1797" href="foundation-2LTT.cofibrations.html#1492" class="Bound">B</a><a id="1798" class="Symbol">)</a> <a id="1800" class="Symbol">→</a> <a id="1802" href="foundation-2LTT.cofibrations.html#1704" class="Bound">Y</a> <a id="1804" href="foundation-2LTT.cofibrations.html#1793" class="Bound">b</a><a id="1805" class="Symbol">)</a> <a id="1807" class="Symbol">→</a> <a id="1809" class="Symbol">(</a><a id="1810" href="foundation-2LTT.cofibrations.html#1788" class="Bound">g</a> <a id="1812" href="foundation-2LTT.exotypes.html#1089" class="Function Operator">∘ᶠᵉᵉ</a> <a id="1817" href="foundation-2LTT.cofibrations.html#1505" class="Bound">f</a><a id="1818" class="Symbol">)))</a>

  <a id="1825" href="foundation-2LTT.cofibrations.html#1825" class="Function">is-cofibration&#39;</a> <a id="1841" class="Symbol">:</a> <a id="1843" class="Symbol">(</a><a id="1844" href="foundation-2LTT.cofibrations.html#1844" class="Bound">l3</a> <a id="1847" href="foundation-2LTT.cofibrations.html#1847" class="Bound">l4</a> <a id="1850" class="Symbol">:</a> <a id="1852" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1857" class="Symbol">)</a> <a id="1859" class="Symbol">→</a> <a id="1861" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1865" class="Symbol">(</a><a id="1866" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1871" class="Symbol">(</a><a id="1872" href="foundation-2LTT.cofibrations.html#1463" class="Bound">l1</a> <a id="1875" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1877" href="foundation-2LTT.cofibrations.html#1466" class="Bound">l2</a> <a id="1880" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1882" href="foundation-2LTT.cofibrations.html#1844" class="Bound">l3</a> <a id="1885" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1887" href="foundation-2LTT.cofibrations.html#1847" class="Bound">l4</a><a id="1889" class="Symbol">))</a>
  <a id="1894" href="foundation-2LTT.cofibrations.html#1825" class="Function">is-cofibration&#39;</a> <a id="1910" href="foundation-2LTT.cofibrations.html#1910" class="Bound">l3</a> <a id="1913" href="foundation-2LTT.cofibrations.html#1913" class="Bound">l4</a> <a id="1916" class="Symbol">=</a>
    <a id="1922" class="Symbol">{</a><a id="1923" href="foundation-2LTT.cofibrations.html#1923" class="Bound">X</a> <a id="1925" class="Symbol">:</a> <a id="1927" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1931" href="foundation-2LTT.cofibrations.html#1910" class="Bound">l3</a><a id="1933" class="Symbol">}</a> <a id="1935" class="Symbol">{</a><a id="1936" href="foundation-2LTT.cofibrations.html#1936" class="Bound">Y</a> <a id="1938" class="Symbol">:</a> <a id="1940" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1944" href="foundation-2LTT.cofibrations.html#1913" class="Bound">l4</a><a id="1946" class="Symbol">}</a> <a id="1948" class="Symbol">(</a><a id="1949" href="foundation-2LTT.cofibrations.html#1949" class="Bound">p</a> <a id="1951" class="Symbol">:</a> <a id="1953" href="foundation-2LTT.cofibrations.html#1936" class="Bound">Y</a> <a id="1955" class="Symbol">→</a> <a id="1957" href="foundation-2LTT.cofibrations.html#1923" class="Bound">X</a><a id="1958" class="Symbol">)</a> <a id="1960" class="Symbol">→</a>
    <a id="1966" class="Symbol">(</a><a id="1967" href="foundation-2LTT.fibrations.html#756" class="Function">is-fibration</a> <a id="1980" href="foundation-2LTT.cofibrations.html#1949" class="Bound">p</a> <a id="1982" class="Symbol">→</a> <a id="1984" href="foundation-2LTT.fibrations.html#756" class="Function">is-fibration</a> <a id="1997" class="Symbol">(</a><a id="1998" href="orthogonal-factorization-systems.pullback-hom%25E1%25B5%2589.html#5137" class="Function">pullback-homᵉ</a> <a id="2012" href="foundation-2LTT.cofibrations.html#1505" class="Bound">f</a> <a id="2014" href="foundation-2LTT.cofibrations.html#1949" class="Bound">p</a><a id="2015" class="Symbol">))</a> <a id="2018" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">×ᵉ</a>
    <a id="2025" class="Symbol">(</a><a id="2026" href="foundation-2LTT.fibrations.html#846" class="Function">is-trivial-fibration</a> <a id="2047" href="foundation-2LTT.cofibrations.html#1949" class="Bound">p</a> <a id="2049" class="Symbol">→</a> <a id="2051" href="foundation-2LTT.fibrations.html#846" class="Function">is-trivial-fibration</a> <a id="2072" class="Symbol">(</a><a id="2073" href="orthogonal-factorization-systems.pullback-hom%25E1%25B5%2589.html#5137" class="Function">pullback-homᵉ</a> <a id="2087" href="foundation-2LTT.cofibrations.html#1505" class="Bound">f</a> <a id="2089" href="foundation-2LTT.cofibrations.html#1949" class="Bound">p</a><a id="2090" class="Symbol">))</a>
</pre>
## Properties

<pre class="Agda"><a id="2121" class="Keyword">module</a> <a id="2128" href="foundation-2LTT.cofibrations.html#2128" class="Module">_</a>
  <a id="2132" class="Symbol">{</a><a id="2133" href="foundation-2LTT.cofibrations.html#2133" class="Bound">l1</a> <a id="2136" href="foundation-2LTT.cofibrations.html#2136" class="Bound">l2</a> <a id="2139" class="Symbol">:</a> <a id="2141" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2146" class="Symbol">}</a> <a id="2148" class="Symbol">{</a><a id="2149" href="foundation-2LTT.cofibrations.html#2149" class="Bound">A</a> <a id="2151" class="Symbol">:</a> <a id="2153" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2157" href="foundation-2LTT.cofibrations.html#2133" class="Bound">l1</a><a id="2159" class="Symbol">}</a> <a id="2161" class="Symbol">{</a><a id="2162" href="foundation-2LTT.cofibrations.html#2162" class="Bound">B</a> <a id="2164" class="Symbol">:</a> <a id="2166" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2170" href="foundation-2LTT.cofibrations.html#2136" class="Bound">l2</a><a id="2172" class="Symbol">}</a> <a id="2174" class="Symbol">(</a><a id="2175" href="foundation-2LTT.cofibrations.html#2175" class="Bound">f</a> <a id="2177" class="Symbol">:</a> <a id="2179" href="foundation-2LTT.cofibrations.html#2149" class="Bound">A</a> <a id="2181" class="Symbol">→</a> <a id="2183" href="foundation-2LTT.cofibrations.html#2162" class="Bound">B</a><a id="2184" class="Symbol">)</a>
  <a id="2188" class="Keyword">where</a>

  <a id="2197" href="foundation-2LTT.cofibrations.html#2197" class="Function">lemma319</a> <a id="2206" class="Symbol">:</a>
    <a id="2212" class="Symbol">{</a><a id="2213" href="foundation-2LTT.cofibrations.html#2213" class="Bound">l3</a> <a id="2216" class="Symbol">:</a> <a id="2218" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2223" class="Symbol">}</a> <a id="2225" class="Symbol">(</a><a id="2226" href="foundation-2LTT.cofibrations.html#2226" class="Bound">X</a> <a id="2228" class="Symbol">:</a> <a id="2230" href="foundation-2LTT.cofibrations.html#2162" class="Bound">B</a> <a id="2232" class="Symbol">→</a> <a id="2234" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2238" href="foundation-2LTT.cofibrations.html#2136" class="Bound">l2</a><a id="2240" class="Symbol">)</a> <a id="2242" class="Symbol">→</a>
    <a id="2248" href="foundation-core.pullbacks%25E1%25B5%2589.html#2234" class="Function">is-pullbackᵉ</a>
      <a id="2267" class="Symbol">(λ</a> <a id="2270" class="Symbol">(</a><a id="2271" href="foundation-2LTT.cofibrations.html#2271" class="Bound">x</a> <a id="2273" class="Symbol">:</a> <a id="2275" href="foundation.unit-type%25E1%25B5%2589.html#826" class="Record">unitᵉ</a><a id="2280" class="Symbol">)</a> <a id="2282" class="Symbol">→</a> <a id="2284" href="foundation-2LTT.cofibrations.html#2175" class="Bound">f</a><a id="2285" class="Symbol">)</a>
      <a id="2293" class="Symbol">(λ</a> <a id="2296" class="Symbol">(</a><a id="2297" href="foundation-2LTT.cofibrations.html#2297" class="Bound">f</a> <a id="2299" class="Symbol">:</a> <a id="2301" href="foundation-2LTT.cofibrations.html#2149" class="Bound">A</a> <a id="2303" class="Symbol">→</a> <a id="2305" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="2308" href="foundation-2LTT.cofibrations.html#2162" class="Bound">B</a> <a id="2310" href="foundation-2LTT.cofibrations.html#2226" class="Bound">X</a><a id="2311" class="Symbol">)</a> <a id="2313" class="Symbol">→</a> <a id="2315" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2320" href="foundation-core.function-types%25E1%25B5%2589.html#476" class="Function Operator">∘ᵉ</a> <a id="2323" href="foundation-2LTT.cofibrations.html#2297" class="Bound">f</a><a id="2324" class="Symbol">)</a>
      <a id="2332" class="Symbol">((λ</a> <a id="2336" href="foundation-2LTT.cofibrations.html#2336" class="Symbol">_</a> <a id="2338" class="Symbol">→</a> <a id="2340" href="foundation.unit-type%25E1%25B5%2589.html#873" class="InductiveConstructor">starᵉ</a><a id="2345" class="Symbol">)</a> <a id="2347" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a>
        <a id="2358" class="Symbol">(λ</a> <a id="2361" class="Symbol">(</a><a id="2362" href="foundation-2LTT.cofibrations.html#2362" class="Bound">g</a> <a id="2364" class="Symbol">:</a> <a id="2366" class="Symbol">(</a><a id="2367" href="foundation-2LTT.cofibrations.html#2367" class="Bound">a</a> <a id="2369" class="Symbol">:</a> <a id="2371" href="foundation-2LTT.cofibrations.html#2149" class="Bound">A</a><a id="2372" class="Symbol">)</a> <a id="2374" class="Symbol">→</a> <a id="2376" class="Symbol">(</a><a id="2377" href="foundation-2LTT.cofibrations.html#2226" class="Bound">X</a> <a id="2379" class="Symbol">(</a><a id="2380" href="foundation-2LTT.cofibrations.html#2175" class="Bound">f</a> <a id="2382" href="foundation-2LTT.cofibrations.html#2367" class="Bound">a</a><a id="2383" class="Symbol">)))</a> <a id="2387" href="foundation-2LTT.cofibrations.html#2387" class="Bound">a</a> <a id="2389" class="Symbol">→</a> <a id="2391" class="Symbol">(</a><a id="2392" href="foundation-2LTT.cofibrations.html#2175" class="Bound">f</a> <a id="2394" href="foundation-2LTT.cofibrations.html#2387" class="Bound">a</a> <a id="2396" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2399" href="foundation-2LTT.cofibrations.html#2362" class="Bound">g</a> <a id="2401" href="foundation-2LTT.cofibrations.html#2387" class="Bound">a</a><a id="2402" class="Symbol">))</a> <a id="2405" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a>
        <a id="2416" class="Symbol">(</a> <a id="2418" class="Symbol">λ</a> <a id="2420" href="foundation-2LTT.cofibrations.html#2420" class="Bound">g</a> <a id="2422" class="Symbol">→</a> <a id="2424" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a><a id="2429" class="Symbol">))</a>
  <a id="2434" href="foundation-2LTT.cofibrations.html#2197" class="Function">lemma319</a> <a id="2443" href="foundation-2LTT.cofibrations.html#2443" class="Bound">X</a> <a id="2445" class="Symbol">=</a>
    <a id="2451" href="foundation-core.equivalences%25E1%25B5%2589.html#5107" class="Function">is-equiv-is-invertibleᵉ</a>
      <a id="2481" class="Symbol">(λ</a> <a id="2484" class="Symbol">(</a><a id="2485" href="foundation.unit-type%25E1%25B5%2589.html#873" class="InductiveConstructor">starᵉ</a> <a id="2491" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2494" href="foundation-2LTT.cofibrations.html#2494" class="Bound">g</a> <a id="2496" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2499" href="foundation-2LTT.cofibrations.html#2499" class="Bound">p</a><a id="2500" class="Symbol">)</a> <a id="2502" href="foundation-2LTT.cofibrations.html#2502" class="Bound">a</a> <a id="2504" class="Symbol">→</a> <a id="2506" href="foundation-core.transport-along-identifications%25E1%25B5%2589.html#837" class="Function">trᵉ</a> <a id="2510" href="foundation-2LTT.cofibrations.html#2443" class="Bound">X</a> <a id="2512" class="Symbol">(</a><a id="2513" href="foundation-core.identity-types%25E1%25B5%2589.html#6276" class="Function">invᵉ</a> <a id="2518" class="Symbol">(</a><a id="2519" href="foundation.function-extensionality%25E1%25B5%2589.html#1919" class="Function">htpy-eqᵉ</a> <a id="2528" href="foundation-2LTT.cofibrations.html#2499" class="Bound">p</a> <a id="2530" href="foundation-2LTT.cofibrations.html#2502" class="Bound">a</a><a id="2531" class="Symbol">))</a> <a id="2534" class="Symbol">(</a><a id="2535" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2540" class="Symbol">(</a><a id="2541" href="foundation-2LTT.cofibrations.html#2494" class="Bound">g</a> <a id="2543" href="foundation-2LTT.cofibrations.html#2502" class="Bound">a</a><a id="2544" class="Symbol">)))</a>
      <a id="2554" class="Symbol">(λ</a> <a id="2557" class="Symbol">(</a><a id="2558" href="foundation.unit-type%25E1%25B5%2589.html#873" class="InductiveConstructor">starᵉ</a> <a id="2564" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2567" href="foundation-2LTT.cofibrations.html#2567" class="Bound">g</a> <a id="2569" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2572" href="foundation-2LTT.cofibrations.html#2572" class="Bound">p</a><a id="2573" class="Symbol">)</a> <a id="2575" class="Symbol">→</a>
        <a id="2585" href="foundation-core.equality-dependent-pair-types%25E1%25B5%2589.html#1845" class="Function">eq-pair-Σᵉ</a> <a id="2596" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a>
          <a id="2612" class="Symbol">(</a> <a id="2614" href="foundation-core.equality-dependent-pair-types%25E1%25B5%2589.html#1845" class="Function">eq-pair-Σᵉ</a>
            <a id="2637" class="Symbol">(</a> <a id="2639" href="foundation.function-extensionality%25E1%25B5%2589.html#4062" class="Postulate">eq-htpyᵉ</a>
              <a id="2662" class="Symbol">(λ</a> <a id="2665" href="foundation-2LTT.cofibrations.html#2665" class="Bound">a</a> <a id="2667" class="Symbol">→</a> <a id="2669" href="foundation-core.equality-dependent-pair-types%25E1%25B5%2589.html#1845" class="Function">eq-pair-Σᵉ</a> <a id="2680" class="Symbol">(</a><a id="2681" href="foundation.function-extensionality%25E1%25B5%2589.html#1919" class="Function">htpy-eqᵉ</a> <a id="2690" href="foundation-2LTT.cofibrations.html#2572" class="Bound">p</a> <a id="2692" href="foundation-2LTT.cofibrations.html#2665" class="Bound">a</a><a id="2693" class="Symbol">)</a> <a id="2695" class="Symbol">(</a><a id="2696" href="foundation-2LTT.cofibrations.html#2801" class="Function">helper</a> <a id="2703" class="Symbol">(</a><a id="2704" href="foundation.function-extensionality%25E1%25B5%2589.html#1919" class="Function">htpy-eqᵉ</a> <a id="2713" href="foundation-2LTT.cofibrations.html#2572" class="Bound">p</a> <a id="2715" href="foundation-2LTT.cofibrations.html#2665" class="Bound">a</a><a id="2716" class="Symbol">))))</a>
            <a id="2733" class="Symbol">(</a> <a id="2735" href="foundation-2LTT.exotypes.html#2561" class="Function">has-uip-exotypeᵉ</a> <a id="2752" class="Symbol">_</a> <a id="2754" class="Symbol">_</a> <a id="2756" class="Symbol">_</a> <a id="2758" class="Symbol">_</a> <a id="2760" class="Symbol">_)))</a>
      <a id="2771" class="Symbol">(λ</a> <a id="2774" href="foundation-2LTT.cofibrations.html#2774" class="Bound">g</a> <a id="2776" class="Symbol">→</a> <a id="2778" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a><a id="2783" class="Symbol">)</a>
    <a id="2789" class="Keyword">where</a>
      <a id="2801" href="foundation-2LTT.cofibrations.html#2801" class="Function">helper</a> <a id="2808" class="Symbol">:</a>
        <a id="2818" class="Symbol">{</a><a id="2819" href="foundation-2LTT.cofibrations.html#2819" class="Bound">x</a> <a id="2821" href="foundation-2LTT.cofibrations.html#2821" class="Bound">y</a> <a id="2823" class="Symbol">:</a> <a id="2825" href="foundation-2LTT.cofibrations.html#2162" class="Bound">B</a><a id="2826" class="Symbol">}</a> <a id="2828" class="Symbol">(</a><a id="2829" href="foundation-2LTT.cofibrations.html#2829" class="Bound">p</a> <a id="2831" class="Symbol">:</a> <a id="2833" href="foundation-2LTT.cofibrations.html#2821" class="Bound">y</a> <a id="2835" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="2838" href="foundation-2LTT.cofibrations.html#2819" class="Bound">x</a><a id="2839" class="Symbol">)</a> <a id="2841" class="Symbol">{</a><a id="2842" href="foundation-2LTT.cofibrations.html#2842" class="Bound">h</a> <a id="2844" class="Symbol">:</a> <a id="2846" href="foundation-2LTT.cofibrations.html#2443" class="Bound">X</a> <a id="2848" href="foundation-2LTT.cofibrations.html#2819" class="Bound">x</a><a id="2849" class="Symbol">}</a> <a id="2851" class="Symbol">→</a>
        <a id="2861" href="foundation-core.transport-along-identifications%25E1%25B5%2589.html#837" class="Function">trᵉ</a> <a id="2865" href="foundation-2LTT.cofibrations.html#2443" class="Bound">X</a> <a id="2867" href="foundation-2LTT.cofibrations.html#2829" class="Bound">p</a> <a id="2869" class="Symbol">(</a><a id="2870" href="foundation-core.transport-along-identifications%25E1%25B5%2589.html#837" class="Function">trᵉ</a> <a id="2874" href="foundation-2LTT.cofibrations.html#2443" class="Bound">X</a> <a id="2876" class="Symbol">(</a><a id="2877" href="foundation-core.identity-types%25E1%25B5%2589.html#6276" class="Function">invᵉ</a> <a id="2882" href="foundation-2LTT.cofibrations.html#2829" class="Bound">p</a><a id="2883" class="Symbol">)</a> <a id="2885" href="foundation-2LTT.cofibrations.html#2842" class="Bound">h</a><a id="2886" class="Symbol">)</a> <a id="2888" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="2891" href="foundation-2LTT.cofibrations.html#2842" class="Bound">h</a>
      <a id="2899" href="foundation-2LTT.cofibrations.html#2801" class="Function">helper</a> <a id="2906" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a> <a id="2912" class="Symbol">=</a> <a id="2914" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a>

  <a id="2923" class="Comment">-- is-cofibration-is-cofibration&#39; :</a>
  <a id="2961" class="Comment">--   is-cofibration&#39; f l2 l2 → is-cofibration f l2</a>
  <a id="3014" class="Comment">-- pr1ᵉ (is-cofibration-is-cofibration&#39; H) Y&#39; g =</a>
  <a id="3066" class="Comment">--   is-fibrant-equivᵉ (pr1ᵉ (H p) is-fibration-p diag) lemma</a>
  <a id="3130" class="Comment">--   where</a>
  <a id="3143" class="Comment">--     Y : UUᵉ (l2)</a>
  <a id="3165" class="Comment">--     Y = Σᵉ B (λ b → type-Fibrant-Type (Y&#39; b))</a>
  <a id="3216" class="Comment">--     p : Y → B</a>
  <a id="3235" class="Comment">--     p = pr1ᵉ</a>
  <a id="3253" class="Comment">--     g&#39; : A → Y</a>
  <a id="3273" class="Comment">--     g&#39; a = (f a ,ᵉ g a)</a>
  <a id="3302" class="Comment">--     is-fibration-p : is-fibration p</a>
  <a id="3343" class="Comment">--     is-fibration-p b =</a>
  <a id="3371" class="Comment">--       is-fibrant-equivᵉ</a>
  <a id="3400" class="Comment">--         (is-fibrant-Fibrant-Type (Y&#39; b))</a>
  <a id="3446" class="Comment">--         -- type-Fibrant-Type (Y&#39; b) ≃ᵉ fiberᵉ p b</a>
  <a id="3501" class="Comment">--         (inv-equiv-fiber-pr1ᵉ (type-Fibrant-Type ∘ᵉ Y&#39;) b)</a>
  <a id="3565" class="Comment">--     diag : hom-arrowᵉ f p</a>
  <a id="3596" class="Comment">--     diag = (g&#39; ,ᵉ idᵉ ,ᵉ λ _ → reflᵉ)</a>
  <a id="3639" class="Comment">--     lemma&#39; : fiberᵉ (pullback-homᵉ f p) diag →</a>
  <a id="3691" class="Comment">--       fiberᵉ (λ (g₁ : (b : B) → type-Fibrant-Type (Y&#39; b)) → g₁ ∘ᵉ f) g</a>
  <a id="3767" class="Comment">--     pr1ᵉ (lemma&#39; (h ,ᵉ e)) b = {!!}</a>
  <a id="3808" class="Comment">--     pr2ᵉ (lemma&#39; (h ,ᵉ e)) = {!!}</a>

  <a id="3848" class="Comment">--     lemma : fiberᵉ (pullback-homᵉ f p) diag ≃ᵉ</a>
  <a id="3900" class="Comment">--       fiberᵉ (λ (g₁ : (b : B) → type-Fibrant-Type (Y&#39; b)) → g₁ ∘ᵉ f) g</a>
  <a id="3976" class="Comment">--     lemma =</a>
  <a id="3993" class="Comment">--       pairᵉ</a>
  <a id="4010" class="Comment">--         (λ (h ,ᵉ e) → pairᵉ (λ b → {! pr1ᵉ (pr2ᵉ (htpy-eq-hom-arrowᵉ f p (pullback-homᵉ f pr1ᵉ h) diag e)) b!})  {!!})</a>
  <a id="4134" class="Comment">--         -- (λ (h ,ᵉ e) → pairᵉ (λ b → {!!})  {!!})</a>
  <a id="4190" class="Comment">--         {!!}</a>
  <a id="4208" class="Comment">-- pr2ᵉ (is-cofibration-is-cofibration&#39; H) = {!!}</a>

  <a id="4261" class="Comment">-- is-cofibration&#39;-is-cofibration :</a>
  <a id="4299" class="Comment">--   is-cofibration f l2 → is-cofibration&#39; f l2 l2</a>
  <a id="4352" class="Comment">-- pr1ᵉ (is-cofibration&#39;-is-cofibration H p) is-fibration-p (v ,ᵉ g ,ᵉ φ) =</a>
  <a id="4430" class="Comment">--   {!!}</a>
  <a id="4442" class="Comment">-- pr2ᵉ (is-cofibration&#39;-is-cofibration H p) = {!!}</a>
</pre>