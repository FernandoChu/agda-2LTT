# The universal property of identity systems

<pre class="Agda"><a id="55" class="Keyword">module</a> <a id="62" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html" class="Module">foundation.universal-property-identity-systemsᵉ</a> <a id="110" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="166" class="Keyword">open</a> <a id="171" class="Keyword">import</a> <a id="178" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="211" class="Keyword">open</a> <a id="216" class="Keyword">import</a> <a id="223" href="foundation.identity-systems%25E1%25B5%2589.html" class="Module">foundation.identity-systemsᵉ</a>
<a id="252" class="Keyword">open</a> <a id="257" class="Keyword">import</a> <a id="264" href="foundation.universal-property-contractible-types%25E1%25B5%2589.html" class="Module">foundation.universal-property-contractible-typesᵉ</a>
<a id="314" class="Keyword">open</a> <a id="319" class="Keyword">import</a> <a id="326" href="foundation.universal-property-dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.universal-property-dependent-pair-typesᵉ</a>
<a id="378" class="Keyword">open</a> <a id="383" class="Keyword">import</a> <a id="390" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="419" class="Keyword">open</a> <a id="424" class="Keyword">import</a> <a id="431" href="foundation-core.contractible-types%25E1%25B5%2589.html" class="Module">foundation-core.contractible-typesᵉ</a>
<a id="467" class="Keyword">open</a> <a id="472" class="Keyword">import</a> <a id="479" href="foundation-core.equivalences%25E1%25B5%2589.html" class="Module">foundation-core.equivalencesᵉ</a>
<a id="509" class="Keyword">open</a> <a id="514" class="Keyword">import</a> <a id="521" href="foundation-core.identity-types%25E1%25B5%2589.html" class="Module">foundation-core.identity-typesᵉ</a>
<a id="553" class="Keyword">open</a> <a id="558" class="Keyword">import</a> <a id="565" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html" class="Module">foundation-core.torsorial-type-familiesᵉ</a>
</pre>
</details>

## Idea

A **(unary) identity system** on a type `A` equipped with a point `a : A`
consists of a type family `B` over `A` equipped with a point `b : B a` that
satisfies an induction principle analogous to the induction principle of the
[identity type](foundation.identity-types.md) at `a`. The
[dependent universal property of identity types](foundation.universal-property-identity-types.md)
also follows for identity systems.

## Definition

### The universal property of identity systems

<pre class="Agda"><a id="dependent-universal-property-identity-systemᵉ"></a><a id="1122" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1122" class="Function">dependent-universal-property-identity-systemᵉ</a> <a id="1168" class="Symbol">:</a>
  <a id="1172" class="Symbol">{</a><a id="1173" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1173" class="Bound">l1ᵉ</a> <a id="1177" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1177" class="Bound">l2ᵉ</a> <a id="1181" class="Symbol">:</a> <a id="1183" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1188" class="Symbol">}</a> <a id="1190" class="Symbol">{</a><a id="1191" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1191" class="Bound">Aᵉ</a> <a id="1194" class="Symbol">:</a> <a id="1196" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1200" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1173" class="Bound">l1ᵉ</a><a id="1203" class="Symbol">}</a> <a id="1205" class="Symbol">(</a><a id="1206" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1206" class="Bound">Bᵉ</a> <a id="1209" class="Symbol">:</a> <a id="1211" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1191" class="Bound">Aᵉ</a> <a id="1214" class="Symbol">→</a> <a id="1216" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1220" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1177" class="Bound">l2ᵉ</a><a id="1223" class="Symbol">)</a> <a id="1225" class="Symbol">{</a><a id="1226" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1226" class="Bound">aᵉ</a> <a id="1229" class="Symbol">:</a> <a id="1231" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1191" class="Bound">Aᵉ</a><a id="1233" class="Symbol">}</a> <a id="1235" class="Symbol">(</a><a id="1236" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1236" class="Bound">bᵉ</a> <a id="1239" class="Symbol">:</a> <a id="1241" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1206" class="Bound">Bᵉ</a> <a id="1244" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1226" class="Bound">aᵉ</a><a id="1246" class="Symbol">)</a> <a id="1248" class="Symbol">→</a> <a id="1250" href="Agda.Primitive.html#553" class="Primitive">UUωᵉ</a>
<a id="1255" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1122" class="Function">dependent-universal-property-identity-systemᵉ</a> <a id="1301" class="Symbol">{</a><a id="1302" class="Argument">Aᵉ</a> <a id="1305" class="Symbol">=</a> <a id="1307" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1307" class="Bound">Aᵉ</a><a id="1309" class="Symbol">}</a> <a id="1311" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1311" class="Bound">Bᵉ</a> <a id="1314" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1314" class="Bound">bᵉ</a> <a id="1317" class="Symbol">=</a>
  <a id="1321" class="Symbol">{</a><a id="1322" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1322" class="Bound">l3ᵉ</a> <a id="1326" class="Symbol">:</a> <a id="1328" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1333" class="Symbol">}</a> <a id="1335" class="Symbol">(</a><a id="1336" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1336" class="Bound">Pᵉ</a> <a id="1339" class="Symbol">:</a> <a id="1341" class="Symbol">(</a><a id="1342" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1342" class="Bound">xᵉ</a> <a id="1345" class="Symbol">:</a> <a id="1347" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1307" class="Bound">Aᵉ</a><a id="1349" class="Symbol">)</a> <a id="1351" class="Symbol">(</a><a id="1352" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1352" class="Bound">yᵉ</a> <a id="1355" class="Symbol">:</a> <a id="1357" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1311" class="Bound">Bᵉ</a> <a id="1360" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1342" class="Bound">xᵉ</a><a id="1362" class="Symbol">)</a> <a id="1364" class="Symbol">→</a> <a id="1366" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1370" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1322" class="Bound">l3ᵉ</a><a id="1373" class="Symbol">)</a> <a id="1375" class="Symbol">→</a>
  <a id="1379" href="foundation-core.equivalences%25E1%25B5%2589.html#1553" class="Function">is-equivᵉ</a> <a id="1389" class="Symbol">(</a><a id="1390" href="foundation.identity-systems%25E1%25B5%2589.html#1369" class="Function">ev-refl-identity-systemᵉ</a> <a id="1415" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1314" class="Bound">bᵉ</a> <a id="1418" class="Symbol">{</a><a id="1419" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1336" class="Bound">Pᵉ</a><a id="1421" class="Symbol">})</a>
</pre>
## Properties

### A type family satisfies the dependent universal property of identity systems if and only if it is torsorial

<pre class="Agda"><a id="1565" class="Keyword">module</a> <a id="1572" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1572" class="Module">_</a>
  <a id="1576" class="Symbol">{</a><a id="1577" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1577" class="Bound">l1ᵉ</a> <a id="1581" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1581" class="Bound">l2ᵉ</a> <a id="1585" class="Symbol">:</a> <a id="1587" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1592" class="Symbol">}</a> <a id="1594" class="Symbol">{</a><a id="1595" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1595" class="Bound">Aᵉ</a> <a id="1598" class="Symbol">:</a> <a id="1600" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1604" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1577" class="Bound">l1ᵉ</a><a id="1607" class="Symbol">}</a> <a id="1609" class="Symbol">{</a><a id="1610" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1610" class="Bound">Bᵉ</a> <a id="1613" class="Symbol">:</a> <a id="1615" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1595" class="Bound">Aᵉ</a> <a id="1618" class="Symbol">→</a> <a id="1620" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1624" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1581" class="Bound">l2ᵉ</a><a id="1627" class="Symbol">}</a> <a id="1629" class="Symbol">{</a><a id="1630" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1630" class="Bound">aᵉ</a> <a id="1633" class="Symbol">:</a> <a id="1635" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1595" class="Bound">Aᵉ</a><a id="1637" class="Symbol">}</a> <a id="1639" class="Symbol">(</a><a id="1640" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1640" class="Bound">bᵉ</a> <a id="1643" class="Symbol">:</a> <a id="1645" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1610" class="Bound">Bᵉ</a> <a id="1648" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1630" class="Bound">aᵉ</a><a id="1650" class="Symbol">)</a>
  <a id="1654" class="Keyword">where</a>

  <a id="1663" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1663" class="Function">dependent-universal-property-identity-system-is-torsorialᵉ</a> <a id="1722" class="Symbol">:</a>
    <a id="1728" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2479" class="Function">is-torsorialᵉ</a> <a id="1742" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1610" class="Bound">Bᵉ</a> <a id="1745" class="Symbol">→</a>
    <a id="1751" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1122" class="Function">dependent-universal-property-identity-systemᵉ</a> <a id="1797" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1610" class="Bound">Bᵉ</a> <a id="1800" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1640" class="Bound">bᵉ</a>
  <a id="1805" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1663" class="Function">dependent-universal-property-identity-system-is-torsorialᵉ</a>
    <a id="1868" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1868" class="Bound">Hᵉ</a> <a id="1871" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1871" class="Bound">Pᵉ</a> <a id="1874" class="Symbol">=</a>
    <a id="1880" href="foundation-core.equivalences%25E1%25B5%2589.html#14406" class="Function">is-equiv-left-factorᵉ</a>
      <a id="1908" class="Symbol">(</a> <a id="1910" href="foundation.identity-systems%25E1%25B5%2589.html#1369" class="Function">ev-refl-identity-systemᵉ</a> <a id="1935" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1640" class="Bound">bᵉ</a><a id="1937" class="Symbol">)</a>
      <a id="1945" class="Symbol">(</a> <a id="1947" href="foundation.dependent-pair-types%25E1%25B5%2589.html#1350" class="Function">ev-pairᵉ</a><a id="1955" class="Symbol">)</a>
      <a id="1963" class="Symbol">(</a> <a id="1965" href="foundation.universal-property-contractible-types%25E1%25B5%2589.html#3807" class="Function">dependent-universal-property-contr-is-contrᵉ</a>
        <a id="2018" class="Symbol">(</a> <a id="2020" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1630" class="Bound">aᵉ</a> <a id="2023" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2026" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1640" class="Bound">bᵉ</a><a id="2028" class="Symbol">)</a>
        <a id="2038" class="Symbol">(</a> <a id="2040" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1868" class="Bound">Hᵉ</a><a id="2042" class="Symbol">)</a>
        <a id="2052" class="Symbol">(</a> <a id="2054" class="Symbol">λ</a> <a id="2056" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2056" class="Bound">uᵉ</a> <a id="2059" class="Symbol">→</a> <a id="2061" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1871" class="Bound">Pᵉ</a> <a id="2064" class="Symbol">(</a><a id="2065" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2070" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2056" class="Bound">uᵉ</a><a id="2072" class="Symbol">)</a> <a id="2074" class="Symbol">(</a><a id="2075" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2080" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2056" class="Bound">uᵉ</a><a id="2082" class="Symbol">)))</a>
      <a id="2092" class="Symbol">(</a> <a id="2094" href="foundation.universal-property-dependent-pair-types%25E1%25B5%2589.html#942" class="Function">is-equiv-ev-pairᵉ</a><a id="2111" class="Symbol">)</a>

  <a id="2116" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2116" class="Function">equiv-dependent-universal-property-identity-system-is-torsorialᵉ</a> <a id="2181" class="Symbol">:</a>
    <a id="2187" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2479" class="Function">is-torsorialᵉ</a> <a id="2201" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1610" class="Bound">Bᵉ</a> <a id="2204" class="Symbol">→</a>
    <a id="2210" class="Symbol">{</a><a id="2211" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2211" class="Bound">lᵉ</a> <a id="2214" class="Symbol">:</a> <a id="2216" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2221" class="Symbol">}</a> <a id="2223" class="Symbol">{</a><a id="2224" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2224" class="Bound">Cᵉ</a> <a id="2227" class="Symbol">:</a> <a id="2229" class="Symbol">(</a><a id="2230" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2230" class="Bound">xᵉ</a> <a id="2233" class="Symbol">:</a> <a id="2235" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1595" class="Bound">Aᵉ</a><a id="2237" class="Symbol">)</a> <a id="2239" class="Symbol">→</a> <a id="2241" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1610" class="Bound">Bᵉ</a> <a id="2244" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2230" class="Bound">xᵉ</a> <a id="2247" class="Symbol">→</a> <a id="2249" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2253" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2211" class="Bound">lᵉ</a><a id="2255" class="Symbol">}</a> <a id="2257" class="Symbol">→</a>
    <a id="2263" class="Symbol">((</a><a id="2265" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2265" class="Bound">xᵉ</a> <a id="2268" class="Symbol">:</a> <a id="2270" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1595" class="Bound">Aᵉ</a><a id="2272" class="Symbol">)</a> <a id="2274" class="Symbol">(</a><a id="2275" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2275" class="Bound">yᵉ</a> <a id="2278" class="Symbol">:</a> <a id="2280" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1610" class="Bound">Bᵉ</a> <a id="2283" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2265" class="Bound">xᵉ</a><a id="2285" class="Symbol">)</a> <a id="2287" class="Symbol">→</a> <a id="2289" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2224" class="Bound">Cᵉ</a> <a id="2292" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2265" class="Bound">xᵉ</a> <a id="2295" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2275" class="Bound">yᵉ</a><a id="2297" class="Symbol">)</a> <a id="2299" href="foundation-core.equivalences%25E1%25B5%2589.html#2662" class="Function Operator">≃ᵉ</a> <a id="2302" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2224" class="Bound">Cᵉ</a> <a id="2305" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1630" class="Bound">aᵉ</a> <a id="2308" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1640" class="Bound">bᵉ</a>
  <a id="2313" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2318" class="Symbol">(</a><a id="2319" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2116" class="Function">equiv-dependent-universal-property-identity-system-is-torsorialᵉ</a> <a id="2384" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2384" class="Bound">Hᵉ</a><a id="2386" class="Symbol">)</a> <a id="2388" class="Symbol">=</a>
    <a id="2394" href="foundation.identity-systems%25E1%25B5%2589.html#1369" class="Function">ev-refl-identity-systemᵉ</a> <a id="2419" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1640" class="Bound">bᵉ</a>
  <a id="2424" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2429" class="Symbol">(</a><a id="2430" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2116" class="Function">equiv-dependent-universal-property-identity-system-is-torsorialᵉ</a> <a id="2495" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2495" class="Bound">Hᵉ</a><a id="2497" class="Symbol">)</a> <a id="2499" class="Symbol">=</a>
    <a id="2505" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1663" class="Function">dependent-universal-property-identity-system-is-torsorialᵉ</a> <a id="2564" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2495" class="Bound">Hᵉ</a> <a id="2567" class="Symbol">_</a>

  <a id="2572" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2572" class="Function">is-torsorial-dependent-universal-property-identity-systemᵉ</a> <a id="2631" class="Symbol">:</a>
    <a id="2637" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1122" class="Function">dependent-universal-property-identity-systemᵉ</a> <a id="2683" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1610" class="Bound">Bᵉ</a> <a id="2686" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1640" class="Bound">bᵉ</a> <a id="2689" class="Symbol">→</a>
    <a id="2695" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2479" class="Function">is-torsorialᵉ</a> <a id="2709" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1610" class="Bound">Bᵉ</a>
  <a id="2714" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2719" class="Symbol">(</a><a id="2720" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2572" class="Function">is-torsorial-dependent-universal-property-identity-systemᵉ</a> <a id="2779" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2779" class="Bound">Hᵉ</a><a id="2781" class="Symbol">)</a> <a id="2783" class="Symbol">=</a> <a id="2785" class="Symbol">(</a><a id="2786" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1630" class="Bound">aᵉ</a> <a id="2789" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2792" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1640" class="Bound">bᵉ</a><a id="2794" class="Symbol">)</a>
  <a id="2798" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2803" class="Symbol">(</a><a id="2804" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2572" class="Function">is-torsorial-dependent-universal-property-identity-systemᵉ</a> <a id="2863" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2863" class="Bound">Hᵉ</a><a id="2865" class="Symbol">)</a> <a id="2867" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2867" class="Bound">uᵉ</a> <a id="2870" class="Symbol">=</a>
    <a id="2876" href="foundation-core.equivalences%25E1%25B5%2589.html#7383" class="Function">map-inv-is-equivᵉ</a>
      <a id="2900" class="Symbol">(</a> <a id="2902" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2863" class="Bound">Hᵉ</a> <a id="2905" class="Symbol">(λ</a> <a id="2908" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2908" class="Bound">xᵉ</a> <a id="2911" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2911" class="Bound">yᵉ</a> <a id="2914" class="Symbol">→</a> <a id="2916" class="Symbol">(</a><a id="2917" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1630" class="Bound">aᵉ</a> <a id="2920" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2923" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1640" class="Bound">bᵉ</a><a id="2925" class="Symbol">)</a> <a id="2927" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="2930" class="Symbol">(</a><a id="2931" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2908" class="Bound">xᵉ</a> <a id="2934" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2937" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2911" class="Bound">yᵉ</a><a id="2939" class="Symbol">)))</a>
      <a id="2949" class="Symbol">(</a> <a id="2951" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a><a id="2956" class="Symbol">)</a>
      <a id="2964" class="Symbol">(</a> <a id="2966" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2971" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2867" class="Bound">uᵉ</a><a id="2973" class="Symbol">)</a>
      <a id="2981" class="Symbol">(</a> <a id="2983" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2988" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#2867" class="Bound">uᵉ</a><a id="2990" class="Symbol">)</a>
</pre>
### A type family satisfies the dependent universal property of identity systems if and only if it is an identity system

<pre class="Agda"><a id="3127" class="Keyword">module</a> <a id="3134" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3134" class="Module">_</a>
  <a id="3138" class="Symbol">{</a><a id="3139" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3139" class="Bound">l1ᵉ</a> <a id="3143" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3143" class="Bound">l2ᵉ</a> <a id="3147" class="Symbol">:</a> <a id="3149" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3154" class="Symbol">}</a> <a id="3156" class="Symbol">{</a><a id="3157" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3157" class="Bound">Aᵉ</a> <a id="3160" class="Symbol">:</a> <a id="3162" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3166" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3139" class="Bound">l1ᵉ</a><a id="3169" class="Symbol">}</a> <a id="3171" class="Symbol">{</a><a id="3172" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3172" class="Bound">Bᵉ</a> <a id="3175" class="Symbol">:</a> <a id="3177" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3157" class="Bound">Aᵉ</a> <a id="3180" class="Symbol">→</a> <a id="3182" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3186" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3143" class="Bound">l2ᵉ</a><a id="3189" class="Symbol">}</a> <a id="3191" class="Symbol">{</a><a id="3192" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3192" class="Bound">aᵉ</a> <a id="3195" class="Symbol">:</a> <a id="3197" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3157" class="Bound">Aᵉ</a><a id="3199" class="Symbol">}</a> <a id="3201" class="Symbol">(</a><a id="3202" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3202" class="Bound">bᵉ</a> <a id="3205" class="Symbol">:</a> <a id="3207" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3172" class="Bound">Bᵉ</a> <a id="3210" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3192" class="Bound">aᵉ</a><a id="3212" class="Symbol">)</a>
  <a id="3216" class="Keyword">where</a>

  <a id="3225" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3225" class="Function">dependent-universal-property-identity-system-is-identity-systemᵉ</a> <a id="3290" class="Symbol">:</a>
    <a id="3296" href="foundation.identity-systems%25E1%25B5%2589.html#2158" class="Function">is-identity-systemᵉ</a> <a id="3316" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3172" class="Bound">Bᵉ</a> <a id="3319" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3192" class="Bound">aᵉ</a> <a id="3322" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3202" class="Bound">bᵉ</a> <a id="3325" class="Symbol">→</a>
    <a id="3331" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1122" class="Function">dependent-universal-property-identity-systemᵉ</a> <a id="3377" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3172" class="Bound">Bᵉ</a> <a id="3380" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3202" class="Bound">bᵉ</a>
  <a id="3385" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3225" class="Function">dependent-universal-property-identity-system-is-identity-systemᵉ</a> <a id="3450" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3450" class="Bound">Hᵉ</a> <a id="3453" class="Symbol">=</a>
    <a id="3459" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1663" class="Function">dependent-universal-property-identity-system-is-torsorialᵉ</a> <a id="3518" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3202" class="Bound">bᵉ</a>
      <a id="3527" class="Symbol">(</a> <a id="3529" href="foundation.identity-systems%25E1%25B5%2589.html#3727" class="Function">is-torsorial-is-identity-systemᵉ</a> <a id="3562" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3192" class="Bound">aᵉ</a> <a id="3565" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3202" class="Bound">bᵉ</a> <a id="3568" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3450" class="Bound">Hᵉ</a><a id="3570" class="Symbol">)</a>

  <a id="3575" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3575" class="Function">is-identity-system-dependent-universal-property-identity-systemᵉ</a> <a id="3640" class="Symbol">:</a>
    <a id="3646" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#1122" class="Function">dependent-universal-property-identity-systemᵉ</a> <a id="3692" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3172" class="Bound">Bᵉ</a> <a id="3695" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3202" class="Bound">bᵉ</a> <a id="3698" class="Symbol">→</a>
    <a id="3704" href="foundation.identity-systems%25E1%25B5%2589.html#2158" class="Function">is-identity-systemᵉ</a> <a id="3724" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3172" class="Bound">Bᵉ</a> <a id="3727" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3192" class="Bound">aᵉ</a> <a id="3730" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3202" class="Bound">bᵉ</a>
  <a id="3735" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3575" class="Function">is-identity-system-dependent-universal-property-identity-systemᵉ</a> <a id="3800" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3800" class="Bound">Hᵉ</a> <a id="3803" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3803" class="Bound">Pᵉ</a> <a id="3806" class="Symbol">=</a>
    <a id="3812" href="foundation-core.equivalences%25E1%25B5%2589.html#1800" class="Function">section-is-equivᵉ</a> <a id="3830" class="Symbol">(</a><a id="3831" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3800" class="Bound">Hᵉ</a> <a id="3834" href="foundation.universal-property-identity-systems%25E1%25B5%2589.html#3803" class="Bound">Pᵉ</a><a id="3836" class="Symbol">)</a>
</pre>