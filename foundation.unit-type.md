# The unit type

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="foundation.unit-type.html" class="Module">foundation.unit-type</a> <a id="54" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="110" class="Keyword">open</a> <a id="115" class="Keyword">import</a> <a id="122" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="154" class="Keyword">open</a> <a id="159" class="Keyword">import</a> <a id="166" href="foundation.diagonal-maps-of-types.html" class="Module">foundation.diagonal-maps-of-types</a>
<a id="200" class="Keyword">open</a> <a id="205" class="Keyword">import</a> <a id="212" href="foundation.raising-universe-levels.html" class="Module">foundation.raising-universe-levels</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="287" class="Keyword">open</a> <a id="292" class="Keyword">import</a> <a id="299" href="foundation-core.constant-maps.html" class="Module">foundation-core.constant-maps</a>
<a id="329" class="Keyword">open</a> <a id="334" class="Keyword">import</a> <a id="341" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="376" class="Keyword">open</a> <a id="381" class="Keyword">import</a> <a id="388" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="417" class="Keyword">open</a> <a id="422" class="Keyword">import</a> <a id="429" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="460" class="Keyword">open</a> <a id="465" class="Keyword">import</a> <a id="472" href="foundation-core.injective-maps.html" class="Module">foundation-core.injective-maps</a>
<a id="503" class="Keyword">open</a> <a id="508" class="Keyword">import</a> <a id="515" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
<a id="544" class="Keyword">open</a> <a id="549" class="Keyword">import</a> <a id="556" href="foundation-core.sets.html" class="Module">foundation-core.sets</a>
<a id="577" class="Keyword">open</a> <a id="582" class="Keyword">import</a> <a id="589" href="foundation-core.truncated-types.html" class="Module">foundation-core.truncated-types</a>
<a id="621" class="Keyword">open</a> <a id="626" class="Keyword">import</a> <a id="633" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a>
</pre>
</details>

## Idea

The **unit type** is a type inductively generated by a single point.

## Definition

### The unit type

<pre class="Agda"><a id="805" class="Keyword">record</a> <a id="unit"></a><a id="812" href="foundation.unit-type.html#812" class="Record">unit</a> <a id="817" class="Symbol">:</a> <a id="819" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="822" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="828" class="Keyword">where</a>
  <a id="836" class="Keyword">instance</a> <a id="845" class="Keyword">constructor</a> <a id="star"></a><a id="857" href="foundation.unit-type.html#857" class="InductiveConstructor">star</a>

<a id="863" class="Symbol">{-#</a> <a id="867" class="Keyword">BUILTIN</a> <a id="875" class="Keyword">UNIT</a> <a id="880" href="foundation.unit-type.html#812" class="Record">unit</a> <a id="885" class="Symbol">#-}</a>
</pre>
### The induction principle of the unit type

<pre class="Agda"><a id="ind-unit"></a><a id="948" href="foundation.unit-type.html#948" class="Function">ind-unit</a> <a id="957" class="Symbol">:</a> <a id="959" class="Symbol">{</a><a id="960" href="foundation.unit-type.html#960" class="Bound">l</a> <a id="962" class="Symbol">:</a> <a id="964" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="969" class="Symbol">}</a> <a id="971" class="Symbol">{</a><a id="972" href="foundation.unit-type.html#972" class="Bound">P</a> <a id="974" class="Symbol">:</a> <a id="976" href="foundation.unit-type.html#812" class="Record">unit</a> <a id="981" class="Symbol">→</a> <a id="983" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="986" href="foundation.unit-type.html#960" class="Bound">l</a><a id="987" class="Symbol">}</a> <a id="989" class="Symbol">→</a> <a id="991" href="foundation.unit-type.html#972" class="Bound">P</a> <a id="993" href="foundation.unit-type.html#857" class="InductiveConstructor">star</a> <a id="998" class="Symbol">→</a> <a id="1000" class="Symbol">(</a><a id="1001" href="foundation.unit-type.html#1001" class="Bound">x</a> <a id="1003" class="Symbol">:</a> <a id="1005" href="foundation.unit-type.html#812" class="Record">unit</a><a id="1009" class="Symbol">)</a> <a id="1011" class="Symbol">→</a> <a id="1013" href="foundation.unit-type.html#972" class="Bound">P</a> <a id="1015" href="foundation.unit-type.html#1001" class="Bound">x</a>
<a id="1017" href="foundation.unit-type.html#948" class="Function">ind-unit</a> <a id="1026" href="foundation.unit-type.html#1026" class="Bound">p</a> <a id="1028" href="foundation.unit-type.html#857" class="InductiveConstructor">star</a> <a id="1033" class="Symbol">=</a> <a id="1035" href="foundation.unit-type.html#1026" class="Bound">p</a>
</pre>
### The terminal map out of a type

<pre class="Agda"><a id="1086" class="Keyword">module</a> <a id="1093" href="foundation.unit-type.html#1093" class="Module">_</a>
  <a id="1097" class="Symbol">{</a><a id="1098" href="foundation.unit-type.html#1098" class="Bound">l</a> <a id="1100" class="Symbol">:</a> <a id="1102" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1107" class="Symbol">}</a> <a id="1109" class="Symbol">(</a><a id="1110" href="foundation.unit-type.html#1110" class="Bound">A</a> <a id="1112" class="Symbol">:</a> <a id="1114" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1117" href="foundation.unit-type.html#1098" class="Bound">l</a><a id="1118" class="Symbol">)</a>
  <a id="1122" class="Keyword">where</a>

  <a id="1131" href="foundation.unit-type.html#1131" class="Function">terminal-map</a> <a id="1144" class="Symbol">:</a> <a id="1146" href="foundation.unit-type.html#1110" class="Bound">A</a> <a id="1148" class="Symbol">→</a> <a id="1150" href="foundation.unit-type.html#812" class="Record">unit</a>
  <a id="1157" href="foundation.unit-type.html#1131" class="Function">terminal-map</a> <a id="1170" class="Symbol">=</a> <a id="1172" href="foundation-core.constant-maps.html#472" class="Function">const</a> <a id="1178" href="foundation.unit-type.html#1110" class="Bound">A</a> <a id="1180" href="foundation.unit-type.html#857" class="InductiveConstructor">star</a>
</pre>
### Points as maps out of the unit type

<pre class="Agda"><a id="1239" class="Keyword">module</a> <a id="1246" href="foundation.unit-type.html#1246" class="Module">_</a>
  <a id="1250" class="Symbol">{</a><a id="1251" href="foundation.unit-type.html#1251" class="Bound">l</a> <a id="1253" class="Symbol">:</a> <a id="1255" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1260" class="Symbol">}</a> <a id="1262" class="Symbol">{</a><a id="1263" href="foundation.unit-type.html#1263" class="Bound">A</a> <a id="1265" class="Symbol">:</a> <a id="1267" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1270" href="foundation.unit-type.html#1251" class="Bound">l</a><a id="1271" class="Symbol">}</a>
  <a id="1275" class="Keyword">where</a>

  <a id="1284" href="foundation.unit-type.html#1284" class="Function">point</a> <a id="1290" class="Symbol">:</a> <a id="1292" href="foundation.unit-type.html#1263" class="Bound">A</a> <a id="1294" class="Symbol">→</a> <a id="1296" class="Symbol">(</a><a id="1297" href="foundation.unit-type.html#812" class="Record">unit</a> <a id="1302" class="Symbol">→</a> <a id="1304" href="foundation.unit-type.html#1263" class="Bound">A</a><a id="1305" class="Symbol">)</a>
  <a id="1309" href="foundation.unit-type.html#1284" class="Function">point</a> <a id="1315" class="Symbol">=</a> <a id="1317" href="foundation.diagonal-maps-of-types.html#1405" class="Function">diagonal-exponential</a> <a id="1338" href="foundation.unit-type.html#1263" class="Bound">A</a> <a id="1340" href="foundation.unit-type.html#812" class="Record">unit</a>
</pre>
### Raising the universe level of the unit type

<pre class="Agda"><a id="raise-unit"></a><a id="1407" href="foundation.unit-type.html#1407" class="Function">raise-unit</a> <a id="1418" class="Symbol">:</a> <a id="1420" class="Symbol">(</a><a id="1421" href="foundation.unit-type.html#1421" class="Bound">l</a> <a id="1423" class="Symbol">:</a> <a id="1425" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1430" class="Symbol">)</a> <a id="1432" class="Symbol">→</a> <a id="1434" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1437" href="foundation.unit-type.html#1421" class="Bound">l</a>
<a id="1439" href="foundation.unit-type.html#1407" class="Function">raise-unit</a> <a id="1450" href="foundation.unit-type.html#1450" class="Bound">l</a> <a id="1452" class="Symbol">=</a> <a id="1454" href="foundation.raising-universe-levels.html#997" class="Datatype">raise</a> <a id="1460" href="foundation.unit-type.html#1450" class="Bound">l</a> <a id="1462" href="foundation.unit-type.html#812" class="Record">unit</a>

<a id="raise-star"></a><a id="1468" href="foundation.unit-type.html#1468" class="Function">raise-star</a> <a id="1479" class="Symbol">:</a> <a id="1481" class="Symbol">{</a><a id="1482" href="foundation.unit-type.html#1482" class="Bound">l</a> <a id="1484" class="Symbol">:</a> <a id="1486" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1491" class="Symbol">}</a> <a id="1493" class="Symbol">→</a> <a id="1495" href="foundation.raising-universe-levels.html#997" class="Datatype">raise</a> <a id="1501" href="foundation.unit-type.html#1482" class="Bound">l</a> <a id="1503" href="foundation.unit-type.html#812" class="Record">unit</a>
<a id="1508" href="foundation.unit-type.html#1468" class="Function">raise-star</a> <a id="1519" class="Symbol">=</a> <a id="1521" href="foundation.raising-universe-levels.html#1062" class="InductiveConstructor">map-raise</a> <a id="1531" href="foundation.unit-type.html#857" class="InductiveConstructor">star</a>

<a id="raise-terminal-map"></a><a id="1537" href="foundation.unit-type.html#1537" class="Function">raise-terminal-map</a> <a id="1556" class="Symbol">:</a> <a id="1558" class="Symbol">{</a><a id="1559" href="foundation.unit-type.html#1559" class="Bound">l1</a> <a id="1562" href="foundation.unit-type.html#1562" class="Bound">l2</a> <a id="1565" class="Symbol">:</a> <a id="1567" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1572" class="Symbol">}</a> <a id="1574" class="Symbol">(</a><a id="1575" href="foundation.unit-type.html#1575" class="Bound">A</a> <a id="1577" class="Symbol">:</a> <a id="1579" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1582" href="foundation.unit-type.html#1559" class="Bound">l1</a><a id="1584" class="Symbol">)</a> <a id="1586" class="Symbol">→</a> <a id="1588" href="foundation.unit-type.html#1575" class="Bound">A</a> <a id="1590" class="Symbol">→</a> <a id="1592" href="foundation.unit-type.html#1407" class="Function">raise-unit</a> <a id="1603" href="foundation.unit-type.html#1562" class="Bound">l2</a>
<a id="1606" href="foundation.unit-type.html#1537" class="Function">raise-terminal-map</a> <a id="1625" class="Symbol">{</a><a id="1626" class="Argument">l2</a> <a id="1629" class="Symbol">=</a> <a id="1631" href="foundation.unit-type.html#1631" class="Bound">l2</a><a id="1633" class="Symbol">}</a> <a id="1635" href="foundation.unit-type.html#1635" class="Bound">A</a> <a id="1637" class="Symbol">=</a> <a id="1639" href="foundation-core.constant-maps.html#472" class="Function">const</a> <a id="1645" href="foundation.unit-type.html#1635" class="Bound">A</a> <a id="1647" href="foundation.unit-type.html#1468" class="Function">raise-star</a>

<a id="compute-raise-unit"></a><a id="1659" href="foundation.unit-type.html#1659" class="Function">compute-raise-unit</a> <a id="1678" class="Symbol">:</a> <a id="1680" class="Symbol">(</a><a id="1681" href="foundation.unit-type.html#1681" class="Bound">l</a> <a id="1683" class="Symbol">:</a> <a id="1685" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1690" class="Symbol">)</a> <a id="1692" class="Symbol">→</a> <a id="1694" href="foundation.unit-type.html#812" class="Record">unit</a> <a id="1699" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="1701" href="foundation.unit-type.html#1407" class="Function">raise-unit</a> <a id="1712" href="foundation.unit-type.html#1681" class="Bound">l</a>
<a id="1714" href="foundation.unit-type.html#1659" class="Function">compute-raise-unit</a> <a id="1733" href="foundation.unit-type.html#1733" class="Bound">l</a> <a id="1735" class="Symbol">=</a> <a id="1737" href="foundation.raising-universe-levels.html#1771" class="Function">compute-raise</a> <a id="1751" href="foundation.unit-type.html#1733" class="Bound">l</a> <a id="1753" href="foundation.unit-type.html#812" class="Record">unit</a>
</pre>
## Properties

### The unit type is contractible

<pre class="Agda"><a id="1821" class="Keyword">abstract</a>
  <a id="is-contr-unit"></a><a id="1832" href="foundation.unit-type.html#1832" class="Function">is-contr-unit</a> <a id="1846" class="Symbol">:</a> <a id="1848" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="1857" href="foundation.unit-type.html#812" class="Record">unit</a>
  <a id="1864" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1868" href="foundation.unit-type.html#1832" class="Function">is-contr-unit</a> <a id="1882" class="Symbol">=</a> <a id="1884" href="foundation.unit-type.html#857" class="InductiveConstructor">star</a>
  <a id="1891" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1895" href="foundation.unit-type.html#1832" class="Function">is-contr-unit</a> <a id="1909" href="foundation.unit-type.html#857" class="InductiveConstructor">star</a> <a id="1914" class="Symbol">=</a> <a id="1916" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
### Any contractible type is equivalent to the unit type

<pre class="Agda"><a id="1992" class="Keyword">module</a> <a id="1999" href="foundation.unit-type.html#1999" class="Module">_</a>
  <a id="2003" class="Symbol">{</a><a id="2004" href="foundation.unit-type.html#2004" class="Bound">l</a> <a id="2006" class="Symbol">:</a> <a id="2008" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2013" class="Symbol">}</a> <a id="2015" class="Symbol">{</a><a id="2016" href="foundation.unit-type.html#2016" class="Bound">A</a> <a id="2018" class="Symbol">:</a> <a id="2020" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2023" href="foundation.unit-type.html#2004" class="Bound">l</a><a id="2024" class="Symbol">}</a>
  <a id="2028" class="Keyword">where</a>

  <a id="2037" class="Keyword">abstract</a>
    <a id="2050" href="foundation.unit-type.html#2050" class="Function">is-equiv-terminal-map-is-contr</a> <a id="2081" class="Symbol">:</a>
      <a id="2089" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="2098" href="foundation.unit-type.html#2016" class="Bound">A</a> <a id="2100" class="Symbol">→</a> <a id="2102" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="2111" class="Symbol">(</a><a id="2112" href="foundation.unit-type.html#1131" class="Function">terminal-map</a> <a id="2125" href="foundation.unit-type.html#2016" class="Bound">A</a><a id="2126" class="Symbol">)</a>
    <a id="2132" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2136" class="Symbol">(</a><a id="2137" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2141" class="Symbol">(</a><a id="2142" href="foundation.unit-type.html#2050" class="Function">is-equiv-terminal-map-is-contr</a> <a id="2173" href="foundation.unit-type.html#2173" class="Bound">H</a><a id="2174" class="Symbol">))</a> <a id="2177" class="Symbol">=</a> <a id="2179" href="foundation.unit-type.html#948" class="Function">ind-unit</a> <a id="2188" class="Symbol">(</a><a id="2189" href="foundation-core.contractible-types.html#986" class="Function">center</a> <a id="2196" href="foundation.unit-type.html#2173" class="Bound">H</a><a id="2197" class="Symbol">)</a>
    <a id="2203" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2207" class="Symbol">(</a><a id="2208" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2212" class="Symbol">(</a><a id="2213" href="foundation.unit-type.html#2050" class="Function">is-equiv-terminal-map-is-contr</a> <a id="2244" href="foundation.unit-type.html#2244" class="Bound">H</a><a id="2245" class="Symbol">))</a> <a id="2248" class="Symbol">=</a> <a id="2250" href="foundation.unit-type.html#948" class="Function">ind-unit</a> <a id="2259" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
    <a id="2268" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2272" class="Symbol">(</a><a id="2273" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2277" class="Symbol">(</a><a id="2278" href="foundation.unit-type.html#2050" class="Function">is-equiv-terminal-map-is-contr</a> <a id="2309" href="foundation.unit-type.html#2309" class="Bound">H</a><a id="2310" class="Symbol">))</a> <a id="2313" href="foundation.unit-type.html#2313" class="Bound">x</a> <a id="2315" class="Symbol">=</a> <a id="2317" href="foundation-core.contractible-types.html#986" class="Function">center</a> <a id="2324" href="foundation.unit-type.html#2309" class="Bound">H</a>
    <a id="2330" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2334" class="Symbol">(</a><a id="2335" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2339" class="Symbol">(</a><a id="2340" href="foundation.unit-type.html#2050" class="Function">is-equiv-terminal-map-is-contr</a> <a id="2371" href="foundation.unit-type.html#2371" class="Bound">H</a><a id="2372" class="Symbol">))</a> <a id="2375" class="Symbol">=</a> <a id="2377" href="foundation-core.contractible-types.html#1324" class="Function">contraction</a> <a id="2389" href="foundation.unit-type.html#2371" class="Bound">H</a>

  <a id="2394" href="foundation.unit-type.html#2394" class="Function">equiv-unit-is-contr</a> <a id="2414" class="Symbol">:</a> <a id="2416" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="2425" href="foundation.unit-type.html#2016" class="Bound">A</a> <a id="2427" class="Symbol">→</a> <a id="2429" href="foundation.unit-type.html#2016" class="Bound">A</a> <a id="2431" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="2433" href="foundation.unit-type.html#812" class="Record">unit</a>
  <a id="2440" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2444" class="Symbol">(</a><a id="2445" href="foundation.unit-type.html#2394" class="Function">equiv-unit-is-contr</a> <a id="2465" href="foundation.unit-type.html#2465" class="Bound">H</a><a id="2466" class="Symbol">)</a> <a id="2468" class="Symbol">=</a> <a id="2470" href="foundation.unit-type.html#1131" class="Function">terminal-map</a> <a id="2483" href="foundation.unit-type.html#2016" class="Bound">A</a>
  <a id="2487" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2491" class="Symbol">(</a><a id="2492" href="foundation.unit-type.html#2394" class="Function">equiv-unit-is-contr</a> <a id="2512" href="foundation.unit-type.html#2512" class="Bound">H</a><a id="2513" class="Symbol">)</a> <a id="2515" class="Symbol">=</a> <a id="2517" href="foundation.unit-type.html#2050" class="Function">is-equiv-terminal-map-is-contr</a> <a id="2548" href="foundation.unit-type.html#2512" class="Bound">H</a>

  <a id="2553" class="Keyword">abstract</a>
    <a id="2566" href="foundation.unit-type.html#2566" class="Function">is-contr-is-equiv-terminal-map</a> <a id="2597" class="Symbol">:</a> <a id="2599" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="2608" class="Symbol">(</a><a id="2609" href="foundation.unit-type.html#1131" class="Function">terminal-map</a> <a id="2622" href="foundation.unit-type.html#2016" class="Bound">A</a><a id="2623" class="Symbol">)</a> <a id="2625" class="Symbol">→</a> <a id="2627" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="2636" href="foundation.unit-type.html#2016" class="Bound">A</a>
    <a id="2642" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2646" class="Symbol">(</a><a id="2647" href="foundation.unit-type.html#2566" class="Function">is-contr-is-equiv-terminal-map</a> <a id="2678" class="Symbol">((</a><a id="2680" href="foundation.unit-type.html#2680" class="Bound">g</a> <a id="2682" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2684" href="foundation.unit-type.html#2684" class="Bound">G</a><a id="2685" class="Symbol">)</a> <a id="2687" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2689" class="Symbol">(</a><a id="2690" href="foundation.unit-type.html#2690" class="Bound">h</a> <a id="2692" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2694" href="foundation.unit-type.html#2694" class="Bound">H</a><a id="2695" class="Symbol">)))</a> <a id="2699" class="Symbol">=</a> <a id="2701" href="foundation.unit-type.html#2690" class="Bound">h</a> <a id="2703" href="foundation.unit-type.html#857" class="InductiveConstructor">star</a>
    <a id="2712" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2716" class="Symbol">(</a><a id="2717" href="foundation.unit-type.html#2566" class="Function">is-contr-is-equiv-terminal-map</a> <a id="2748" class="Symbol">((</a><a id="2750" href="foundation.unit-type.html#2750" class="Bound">g</a> <a id="2752" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2754" href="foundation.unit-type.html#2754" class="Bound">G</a><a id="2755" class="Symbol">)</a> <a id="2757" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2759" class="Symbol">(</a><a id="2760" href="foundation.unit-type.html#2760" class="Bound">h</a> <a id="2762" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2764" href="foundation.unit-type.html#2764" class="Bound">H</a><a id="2765" class="Symbol">)))</a> <a id="2769" class="Symbol">=</a> <a id="2771" href="foundation.unit-type.html#2764" class="Bound">H</a>
</pre>
### The unit type is a proposition

<pre class="Agda"><a id="2822" class="Keyword">abstract</a>
  <a id="is-prop-unit"></a><a id="2833" href="foundation.unit-type.html#2833" class="Function">is-prop-unit</a> <a id="2846" class="Symbol">:</a> <a id="2848" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2856" href="foundation.unit-type.html#812" class="Record">unit</a>
  <a id="2863" href="foundation.unit-type.html#2833" class="Function">is-prop-unit</a> <a id="2876" class="Symbol">=</a> <a id="2878" href="foundation-core.contractible-types.html#7121" class="Function">is-prop-is-contr</a> <a id="2895" href="foundation.unit-type.html#1832" class="Function">is-contr-unit</a>

<a id="unit-Prop"></a><a id="2910" href="foundation.unit-type.html#2910" class="Function">unit-Prop</a> <a id="2920" class="Symbol">:</a> <a id="2922" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2927" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2933" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2937" href="foundation.unit-type.html#2910" class="Function">unit-Prop</a> <a id="2947" class="Symbol">=</a> <a id="2949" href="foundation.unit-type.html#812" class="Record">unit</a>
<a id="2954" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2958" href="foundation.unit-type.html#2910" class="Function">unit-Prop</a> <a id="2968" class="Symbol">=</a> <a id="2970" href="foundation.unit-type.html#2833" class="Function">is-prop-unit</a>
</pre>
### The unit type is a set

<pre class="Agda"><a id="3024" class="Keyword">abstract</a>
  <a id="is-set-unit"></a><a id="3035" href="foundation.unit-type.html#3035" class="Function">is-set-unit</a> <a id="3047" class="Symbol">:</a> <a id="3049" href="foundation-core.sets.html#795" class="Function">is-set</a> <a id="3056" href="foundation.unit-type.html#812" class="Record">unit</a>
  <a id="3063" href="foundation.unit-type.html#3035" class="Function">is-set-unit</a> <a id="3075" class="Symbol">=</a> <a id="3077" href="foundation-core.truncated-types.html#1979" class="Function">is-trunc-succ-is-trunc</a> <a id="3100" href="foundation-core.truncation-levels.html#628" class="Function">neg-one-𝕋</a> <a id="3110" href="foundation.unit-type.html#2833" class="Function">is-prop-unit</a>

<a id="unit-Set"></a><a id="3124" href="foundation.unit-type.html#3124" class="Function">unit-Set</a> <a id="3133" class="Symbol">:</a> <a id="3135" href="foundation-core.sets.html#870" class="Function">Set</a> <a id="3139" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="3145" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3149" href="foundation.unit-type.html#3124" class="Function">unit-Set</a> <a id="3158" class="Symbol">=</a> <a id="3160" href="foundation.unit-type.html#812" class="Record">unit</a>
<a id="3165" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3169" href="foundation.unit-type.html#3124" class="Function">unit-Set</a> <a id="3178" class="Symbol">=</a> <a id="3180" href="foundation.unit-type.html#3035" class="Function">is-set-unit</a>
</pre>
<pre class="Agda"><a id="3205" class="Keyword">abstract</a>
  <a id="is-contr-raise-unit"></a><a id="3216" href="foundation.unit-type.html#3216" class="Function">is-contr-raise-unit</a> <a id="3236" class="Symbol">:</a>
    <a id="3242" class="Symbol">{</a><a id="3243" href="foundation.unit-type.html#3243" class="Bound">l1</a> <a id="3246" class="Symbol">:</a> <a id="3248" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3253" class="Symbol">}</a> <a id="3255" class="Symbol">→</a> <a id="3257" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="3266" class="Symbol">(</a><a id="3267" href="foundation.unit-type.html#1407" class="Function">raise-unit</a> <a id="3278" href="foundation.unit-type.html#3243" class="Bound">l1</a><a id="3280" class="Symbol">)</a>
  <a id="3284" href="foundation.unit-type.html#3216" class="Function">is-contr-raise-unit</a> <a id="3304" class="Symbol">{</a><a id="3305" href="foundation.unit-type.html#3305" class="Bound">l1</a><a id="3307" class="Symbol">}</a> <a id="3309" class="Symbol">=</a>
    <a id="3315" href="foundation-core.contractible-types.html#2914" class="Function">is-contr-equiv&#39;</a> <a id="3331" href="foundation.unit-type.html#812" class="Record">unit</a> <a id="3336" class="Symbol">(</a><a id="3337" href="foundation.raising-universe-levels.html#1771" class="Function">compute-raise</a> <a id="3351" href="foundation.unit-type.html#3305" class="Bound">l1</a> <a id="3354" href="foundation.unit-type.html#812" class="Record">unit</a><a id="3358" class="Symbol">)</a> <a id="3360" href="foundation.unit-type.html#1832" class="Function">is-contr-unit</a>

<a id="3375" class="Keyword">abstract</a>
  <a id="is-prop-raise-unit"></a><a id="3386" href="foundation.unit-type.html#3386" class="Function">is-prop-raise-unit</a> <a id="3405" class="Symbol">:</a>
    <a id="3411" class="Symbol">{</a><a id="3412" href="foundation.unit-type.html#3412" class="Bound">l1</a> <a id="3415" class="Symbol">:</a> <a id="3417" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3422" class="Symbol">}</a> <a id="3424" class="Symbol">→</a> <a id="3426" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="3434" class="Symbol">(</a><a id="3435" href="foundation.unit-type.html#1407" class="Function">raise-unit</a> <a id="3446" href="foundation.unit-type.html#3412" class="Bound">l1</a><a id="3448" class="Symbol">)</a>
  <a id="3452" href="foundation.unit-type.html#3386" class="Function">is-prop-raise-unit</a> <a id="3471" class="Symbol">{</a><a id="3472" href="foundation.unit-type.html#3472" class="Bound">l1</a><a id="3474" class="Symbol">}</a> <a id="3476" class="Symbol">=</a>
    <a id="3482" href="foundation-core.propositions.html#4032" class="Function">is-prop-equiv&#39;</a> <a id="3497" class="Symbol">(</a><a id="3498" href="foundation.raising-universe-levels.html#1771" class="Function">compute-raise</a> <a id="3512" href="foundation.unit-type.html#3472" class="Bound">l1</a> <a id="3515" href="foundation.unit-type.html#812" class="Record">unit</a><a id="3519" class="Symbol">)</a> <a id="3521" href="foundation.unit-type.html#2833" class="Function">is-prop-unit</a>

<a id="raise-unit-Prop"></a><a id="3535" href="foundation.unit-type.html#3535" class="Function">raise-unit-Prop</a> <a id="3551" class="Symbol">:</a>
  <a id="3555" class="Symbol">(</a><a id="3556" href="foundation.unit-type.html#3556" class="Bound">l1</a> <a id="3559" class="Symbol">:</a> <a id="3561" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3566" class="Symbol">)</a> <a id="3568" class="Symbol">→</a> <a id="3570" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3575" href="foundation.unit-type.html#3556" class="Bound">l1</a>
<a id="3578" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3582" class="Symbol">(</a><a id="3583" href="foundation.unit-type.html#3535" class="Function">raise-unit-Prop</a> <a id="3599" href="foundation.unit-type.html#3599" class="Bound">l1</a><a id="3601" class="Symbol">)</a> <a id="3603" class="Symbol">=</a> <a id="3605" href="foundation.unit-type.html#1407" class="Function">raise-unit</a> <a id="3616" href="foundation.unit-type.html#3599" class="Bound">l1</a>
<a id="3619" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3623" class="Symbol">(</a><a id="3624" href="foundation.unit-type.html#3535" class="Function">raise-unit-Prop</a> <a id="3640" href="foundation.unit-type.html#3640" class="Bound">l1</a><a id="3642" class="Symbol">)</a> <a id="3644" class="Symbol">=</a> <a id="3646" href="foundation.unit-type.html#3386" class="Function">is-prop-raise-unit</a>

<a id="3666" class="Keyword">abstract</a>
  <a id="is-set-raise-unit"></a><a id="3677" href="foundation.unit-type.html#3677" class="Function">is-set-raise-unit</a> <a id="3695" class="Symbol">:</a>
    <a id="3701" class="Symbol">{</a><a id="3702" href="foundation.unit-type.html#3702" class="Bound">l1</a> <a id="3705" class="Symbol">:</a> <a id="3707" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3712" class="Symbol">}</a> <a id="3714" class="Symbol">→</a> <a id="3716" href="foundation-core.sets.html#795" class="Function">is-set</a> <a id="3723" class="Symbol">(</a><a id="3724" href="foundation.unit-type.html#1407" class="Function">raise-unit</a> <a id="3735" href="foundation.unit-type.html#3702" class="Bound">l1</a><a id="3737" class="Symbol">)</a>
  <a id="3741" href="foundation.unit-type.html#3677" class="Function">is-set-raise-unit</a> <a id="3759" class="Symbol">=</a> <a id="3761" href="foundation-core.truncated-types.html#1979" class="Function">is-trunc-succ-is-trunc</a> <a id="3784" href="foundation-core.truncation-levels.html#628" class="Function">neg-one-𝕋</a> <a id="3794" href="foundation.unit-type.html#3386" class="Function">is-prop-raise-unit</a>

<a id="raise-unit-Set"></a><a id="3814" href="foundation.unit-type.html#3814" class="Function">raise-unit-Set</a> <a id="3829" class="Symbol">:</a> <a id="3831" class="Symbol">(</a><a id="3832" href="foundation.unit-type.html#3832" class="Bound">l1</a> <a id="3835" class="Symbol">:</a> <a id="3837" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3842" class="Symbol">)</a> <a id="3844" class="Symbol">→</a> <a id="3846" href="foundation-core.sets.html#870" class="Function">Set</a> <a id="3850" href="foundation.unit-type.html#3832" class="Bound">l1</a>
<a id="3853" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3857" class="Symbol">(</a><a id="3858" href="foundation.unit-type.html#3814" class="Function">raise-unit-Set</a> <a id="3873" href="foundation.unit-type.html#3873" class="Bound">l1</a><a id="3875" class="Symbol">)</a> <a id="3877" class="Symbol">=</a> <a id="3879" href="foundation.unit-type.html#1407" class="Function">raise-unit</a> <a id="3890" href="foundation.unit-type.html#3873" class="Bound">l1</a>
<a id="3893" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3897" class="Symbol">(</a><a id="3898" href="foundation.unit-type.html#3814" class="Function">raise-unit-Set</a> <a id="3913" href="foundation.unit-type.html#3913" class="Bound">l1</a><a id="3915" class="Symbol">)</a> <a id="3917" class="Symbol">=</a> <a id="3919" href="foundation.unit-type.html#3677" class="Function">is-set-raise-unit</a>
</pre>
### All parallel maps into `unit` are equal

<pre class="Agda"><a id="3995" class="Keyword">module</a> <a id="4002" href="foundation.unit-type.html#4002" class="Module">_</a>
  <a id="4006" class="Symbol">{</a><a id="4007" href="foundation.unit-type.html#4007" class="Bound">l</a> <a id="4009" class="Symbol">:</a> <a id="4011" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4016" class="Symbol">}</a> <a id="4018" class="Symbol">{</a><a id="4019" href="foundation.unit-type.html#4019" class="Bound">A</a> <a id="4021" class="Symbol">:</a> <a id="4023" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4026" href="foundation.unit-type.html#4007" class="Bound">l</a><a id="4027" class="Symbol">}</a> <a id="4029" class="Symbol">{</a><a id="4030" href="foundation.unit-type.html#4030" class="Bound">f</a> <a id="4032" href="foundation.unit-type.html#4032" class="Bound">g</a> <a id="4034" class="Symbol">:</a> <a id="4036" href="foundation.unit-type.html#4019" class="Bound">A</a> <a id="4038" class="Symbol">→</a> <a id="4040" href="foundation.unit-type.html#812" class="Record">unit</a><a id="4044" class="Symbol">}</a>
  <a id="4048" class="Keyword">where</a>

  <a id="4057" href="foundation.unit-type.html#4057" class="Function">eq-map-into-unit</a> <a id="4074" class="Symbol">:</a> <a id="4076" href="foundation.unit-type.html#4030" class="Bound">f</a> <a id="4078" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4080" href="foundation.unit-type.html#4032" class="Bound">g</a>
  <a id="4084" href="foundation.unit-type.html#4057" class="Function">eq-map-into-unit</a> <a id="4101" class="Symbol">=</a> <a id="4103" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
### The map `point x` is injective for every `x`

<pre class="Agda"><a id="4171" class="Keyword">module</a> <a id="4178" href="foundation.unit-type.html#4178" class="Module">_</a>
  <a id="4182" class="Symbol">{</a><a id="4183" href="foundation.unit-type.html#4183" class="Bound">l</a> <a id="4185" class="Symbol">:</a> <a id="4187" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4192" class="Symbol">}</a> <a id="4194" class="Symbol">{</a><a id="4195" href="foundation.unit-type.html#4195" class="Bound">A</a> <a id="4197" class="Symbol">:</a> <a id="4199" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4202" href="foundation.unit-type.html#4183" class="Bound">l</a><a id="4203" class="Symbol">}</a> <a id="4205" class="Symbol">(</a><a id="4206" href="foundation.unit-type.html#4206" class="Bound">x</a> <a id="4208" class="Symbol">:</a> <a id="4210" href="foundation.unit-type.html#4195" class="Bound">A</a><a id="4211" class="Symbol">)</a>
  <a id="4215" class="Keyword">where</a>

  <a id="4224" href="foundation.unit-type.html#4224" class="Function">is-injective-point</a> <a id="4243" class="Symbol">:</a> <a id="4245" href="foundation-core.injective-maps.html#990" class="Function">is-injective</a> <a id="4258" class="Symbol">(</a><a id="4259" href="foundation.unit-type.html#1284" class="Function">point</a> <a id="4265" href="foundation.unit-type.html#4206" class="Bound">x</a><a id="4266" class="Symbol">)</a>
  <a id="4270" href="foundation.unit-type.html#4224" class="Function">is-injective-point</a> <a id="4289" class="Symbol">_</a> <a id="4291" class="Symbol">=</a> <a id="4293" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

  <a id="4301" href="foundation.unit-type.html#4301" class="Function">point-injection</a> <a id="4317" class="Symbol">:</a> <a id="4319" href="foundation-core.injective-maps.html#1136" class="Function">injection</a> <a id="4329" href="foundation.unit-type.html#812" class="Record">unit</a> <a id="4334" href="foundation.unit-type.html#4195" class="Bound">A</a>
  <a id="4338" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4342" href="foundation.unit-type.html#4301" class="Function">point-injection</a> <a id="4358" class="Symbol">=</a> <a id="4360" href="foundation.unit-type.html#1284" class="Function">point</a> <a id="4366" href="foundation.unit-type.html#4206" class="Bound">x</a>
  <a id="4370" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4374" href="foundation.unit-type.html#4301" class="Function">point-injection</a> <a id="4390" class="Symbol">=</a> <a id="4392" href="foundation.unit-type.html#4224" class="Function">is-injective-point</a>
</pre>