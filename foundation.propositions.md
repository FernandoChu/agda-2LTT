# Propositions

<pre class="Agda"><a id="25" class="Keyword">module</a> <a id="32" href="foundation.propositions.html" class="Module">foundation.propositions</a> <a id="56" class="Keyword">where</a>

<a id="63" class="Keyword">open</a> <a id="68" class="Keyword">import</a> <a id="75" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a> <a id="104" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="161" class="Keyword">open</a> <a id="166" class="Keyword">import</a> <a id="173" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="203" class="Keyword">open</a> <a id="208" class="Keyword">import</a> <a id="215" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="291" class="Keyword">open</a> <a id="296" class="Keyword">import</a> <a id="303" href="foundation.retracts-of-types.html" class="Module">foundation.retracts-of-types</a>
<a id="332" class="Keyword">open</a> <a id="337" class="Keyword">import</a> <a id="344" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="372" class="Keyword">open</a> <a id="377" class="Keyword">import</a> <a id="384" href="foundation-core.embeddings.html" class="Module">foundation-core.embeddings</a>
<a id="411" class="Keyword">open</a> <a id="416" class="Keyword">import</a> <a id="423" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="452" class="Keyword">open</a> <a id="457" class="Keyword">import</a> <a id="464" href="foundation-core.truncated-types.html" class="Module">foundation-core.truncated-types</a>
<a id="496" class="Keyword">open</a> <a id="501" class="Keyword">import</a> <a id="508" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a>
</pre>
</details>

## Properties

### Propositions are `k+1`-truncated for any `k`

<pre class="Agda"><a id="632" class="Keyword">abstract</a>
  <a id="is-trunc-is-prop"></a><a id="643" href="foundation.propositions.html#643" class="Function">is-trunc-is-prop</a> <a id="660" class="Symbol">:</a>
    <a id="666" class="Symbol">{</a><a id="667" href="foundation.propositions.html#667" class="Bound">l</a> <a id="669" class="Symbol">:</a> <a id="671" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="676" class="Symbol">}</a> <a id="678" class="Symbol">(</a><a id="679" href="foundation.propositions.html#679" class="Bound">k</a> <a id="681" class="Symbol">:</a> <a id="683" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a><a id="684" class="Symbol">)</a> <a id="686" class="Symbol">{</a><a id="687" href="foundation.propositions.html#687" class="Bound">A</a> <a id="689" class="Symbol">:</a> <a id="691" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="694" href="foundation.propositions.html#667" class="Bound">l</a><a id="695" class="Symbol">}</a> <a id="697" class="Symbol">→</a> <a id="699" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="707" href="foundation.propositions.html#687" class="Bound">A</a> <a id="709" class="Symbol">→</a> <a id="711" href="foundation-core.truncated-types.html#1236" class="Function">is-trunc</a> <a id="720" class="Symbol">(</a><a id="721" href="foundation-core.truncation-levels.html#558" class="InductiveConstructor">succ-𝕋</a> <a id="728" href="foundation.propositions.html#679" class="Bound">k</a><a id="729" class="Symbol">)</a> <a id="731" href="foundation.propositions.html#687" class="Bound">A</a>
  <a id="735" href="foundation.propositions.html#643" class="Function">is-trunc-is-prop</a> <a id="752" href="foundation.propositions.html#752" class="Bound">k</a> <a id="754" href="foundation.propositions.html#754" class="Bound">is-prop-A</a> <a id="764" href="foundation.propositions.html#764" class="Bound">x</a> <a id="766" href="foundation.propositions.html#766" class="Bound">y</a> <a id="768" class="Symbol">=</a> <a id="770" href="foundation.contractible-types.html#4079" class="Function">is-trunc-is-contr</a> <a id="788" href="foundation.propositions.html#752" class="Bound">k</a> <a id="790" class="Symbol">(</a><a id="791" href="foundation.propositions.html#754" class="Bound">is-prop-A</a> <a id="801" href="foundation.propositions.html#764" class="Bound">x</a> <a id="803" href="foundation.propositions.html#766" class="Bound">y</a><a id="804" class="Symbol">)</a>

<a id="truncated-type-Prop"></a><a id="807" href="foundation.propositions.html#807" class="Function">truncated-type-Prop</a> <a id="827" class="Symbol">:</a> <a id="829" class="Symbol">{</a><a id="830" href="foundation.propositions.html#830" class="Bound">l</a> <a id="832" class="Symbol">:</a> <a id="834" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="839" class="Symbol">}</a> <a id="841" class="Symbol">(</a><a id="842" href="foundation.propositions.html#842" class="Bound">k</a> <a id="844" class="Symbol">:</a> <a id="846" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a><a id="847" class="Symbol">)</a> <a id="849" class="Symbol">→</a> <a id="851" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="856" href="foundation.propositions.html#830" class="Bound">l</a> <a id="858" class="Symbol">→</a> <a id="860" href="foundation-core.truncated-types.html#1534" class="Function">Truncated-Type</a> <a id="875" href="foundation.propositions.html#830" class="Bound">l</a> <a id="877" class="Symbol">(</a><a id="878" href="foundation-core.truncation-levels.html#558" class="InductiveConstructor">succ-𝕋</a> <a id="885" href="foundation.propositions.html#842" class="Bound">k</a><a id="886" class="Symbol">)</a>
<a id="888" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="892" class="Symbol">(</a><a id="893" href="foundation.propositions.html#807" class="Function">truncated-type-Prop</a> <a id="913" href="foundation.propositions.html#913" class="Bound">k</a> <a id="915" href="foundation.propositions.html#915" class="Bound">P</a><a id="916" class="Symbol">)</a> <a id="918" class="Symbol">=</a> <a id="920" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="930" href="foundation.propositions.html#915" class="Bound">P</a>
<a id="932" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="936" class="Symbol">(</a><a id="937" href="foundation.propositions.html#807" class="Function">truncated-type-Prop</a> <a id="957" href="foundation.propositions.html#957" class="Bound">k</a> <a id="959" href="foundation.propositions.html#959" class="Bound">P</a><a id="960" class="Symbol">)</a> <a id="962" class="Symbol">=</a> <a id="964" href="foundation.propositions.html#643" class="Function">is-trunc-is-prop</a> <a id="981" href="foundation.propositions.html#957" class="Bound">k</a> <a id="983" class="Symbol">(</a><a id="984" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1002" href="foundation.propositions.html#959" class="Bound">P</a><a id="1003" class="Symbol">)</a>
</pre>
### Propositions are closed under retracts

<pre class="Agda"><a id="1062" class="Keyword">module</a> <a id="1069" href="foundation.propositions.html#1069" class="Module">_</a>
  <a id="1073" class="Symbol">{</a><a id="1074" href="foundation.propositions.html#1074" class="Bound">l1</a> <a id="1077" href="foundation.propositions.html#1077" class="Bound">l2</a> <a id="1080" class="Symbol">:</a> <a id="1082" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1087" class="Symbol">}</a> <a id="1089" class="Symbol">{</a><a id="1090" href="foundation.propositions.html#1090" class="Bound">A</a> <a id="1092" class="Symbol">:</a> <a id="1094" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1097" href="foundation.propositions.html#1074" class="Bound">l1</a><a id="1099" class="Symbol">}</a> <a id="1101" class="Symbol">{</a><a id="1102" href="foundation.propositions.html#1102" class="Bound">B</a> <a id="1104" class="Symbol">:</a> <a id="1106" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1109" href="foundation.propositions.html#1077" class="Bound">l2</a><a id="1111" class="Symbol">}</a>
  <a id="1115" class="Keyword">where</a>

  <a id="1124" href="foundation.propositions.html#1124" class="Function">is-prop-retract-of</a> <a id="1143" class="Symbol">:</a> <a id="1145" href="foundation.propositions.html#1090" class="Bound">A</a> <a id="1147" href="foundation-core.retracts-of-types.html#1754" class="Function Operator">retract-of</a> <a id="1158" href="foundation.propositions.html#1102" class="Bound">B</a> <a id="1160" class="Symbol">→</a> <a id="1162" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1170" href="foundation.propositions.html#1102" class="Bound">B</a> <a id="1172" class="Symbol">→</a> <a id="1174" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1182" href="foundation.propositions.html#1090" class="Bound">A</a>
  <a id="1186" href="foundation.propositions.html#1124" class="Function">is-prop-retract-of</a> <a id="1205" class="Symbol">=</a> <a id="1207" href="foundation-core.truncated-types.html#3605" class="Function">is-trunc-retract-of</a>
</pre>
### If a type embeds into a proposition, then it is a proposition

<pre class="Agda"><a id="1307" class="Keyword">abstract</a>
  <a id="is-prop-is-emb"></a><a id="1318" href="foundation.propositions.html#1318" class="Function">is-prop-is-emb</a> <a id="1333" class="Symbol">:</a>
    <a id="1339" class="Symbol">{</a><a id="1340" href="foundation.propositions.html#1340" class="Bound">l1</a> <a id="1343" href="foundation.propositions.html#1343" class="Bound">l2</a> <a id="1346" class="Symbol">:</a> <a id="1348" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1353" class="Symbol">}</a> <a id="1355" class="Symbol">{</a><a id="1356" href="foundation.propositions.html#1356" class="Bound">A</a> <a id="1358" class="Symbol">:</a> <a id="1360" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1363" href="foundation.propositions.html#1340" class="Bound">l1</a><a id="1365" class="Symbol">}</a> <a id="1367" class="Symbol">{</a><a id="1368" href="foundation.propositions.html#1368" class="Bound">B</a> <a id="1370" class="Symbol">:</a> <a id="1372" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1375" href="foundation.propositions.html#1343" class="Bound">l2</a><a id="1377" class="Symbol">}</a> <a id="1379" class="Symbol">(</a><a id="1380" href="foundation.propositions.html#1380" class="Bound">f</a> <a id="1382" class="Symbol">:</a> <a id="1384" href="foundation.propositions.html#1356" class="Bound">A</a> <a id="1386" class="Symbol">→</a> <a id="1388" href="foundation.propositions.html#1368" class="Bound">B</a><a id="1389" class="Symbol">)</a> <a id="1391" class="Symbol">→</a>
    <a id="1397" href="foundation-core.embeddings.html#1086" class="Function">is-emb</a> <a id="1404" href="foundation.propositions.html#1380" class="Bound">f</a> <a id="1406" class="Symbol">→</a> <a id="1408" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1416" href="foundation.propositions.html#1368" class="Bound">B</a> <a id="1418" class="Symbol">→</a> <a id="1420" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1428" href="foundation.propositions.html#1356" class="Bound">A</a>
  <a id="1432" href="foundation.propositions.html#1318" class="Function">is-prop-is-emb</a> <a id="1447" class="Symbol">=</a> <a id="1449" href="foundation-core.truncated-types.html#5028" class="Function">is-trunc-is-emb</a> <a id="1465" href="foundation-core.truncation-levels.html#542" class="InductiveConstructor">neg-two-𝕋</a>

<a id="1476" class="Keyword">abstract</a>
  <a id="is-prop-emb"></a><a id="1487" href="foundation.propositions.html#1487" class="Function">is-prop-emb</a> <a id="1499" class="Symbol">:</a>
    <a id="1505" class="Symbol">{</a><a id="1506" href="foundation.propositions.html#1506" class="Bound">l1</a> <a id="1509" href="foundation.propositions.html#1509" class="Bound">l2</a> <a id="1512" class="Symbol">:</a> <a id="1514" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1519" class="Symbol">}</a> <a id="1521" class="Symbol">{</a><a id="1522" href="foundation.propositions.html#1522" class="Bound">A</a> <a id="1524" class="Symbol">:</a> <a id="1526" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1529" href="foundation.propositions.html#1506" class="Bound">l1</a><a id="1531" class="Symbol">}</a> <a id="1533" class="Symbol">{</a><a id="1534" href="foundation.propositions.html#1534" class="Bound">B</a> <a id="1536" class="Symbol">:</a> <a id="1538" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1541" href="foundation.propositions.html#1509" class="Bound">l2</a><a id="1543" class="Symbol">}</a> <a id="1545" class="Symbol">(</a><a id="1546" href="foundation.propositions.html#1546" class="Bound">f</a> <a id="1548" class="Symbol">:</a> <a id="1550" href="foundation.propositions.html#1522" class="Bound">A</a> <a id="1552" href="foundation-core.embeddings.html#1495" class="Function Operator">↪</a> <a id="1554" href="foundation.propositions.html#1534" class="Bound">B</a><a id="1555" class="Symbol">)</a> <a id="1557" class="Symbol">→</a> <a id="1559" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1567" href="foundation.propositions.html#1534" class="Bound">B</a> <a id="1569" class="Symbol">→</a> <a id="1571" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1579" href="foundation.propositions.html#1522" class="Bound">A</a>
  <a id="1583" href="foundation.propositions.html#1487" class="Function">is-prop-emb</a> <a id="1595" class="Symbol">=</a> <a id="1597" href="foundation-core.truncated-types.html#5294" class="Function">is-trunc-emb</a> <a id="1610" href="foundation-core.truncation-levels.html#542" class="InductiveConstructor">neg-two-𝕋</a>
</pre>
### Two equivalent types are equivalently propositions

<pre class="Agda"><a id="equiv-is-prop-equiv"></a><a id="1689" href="foundation.propositions.html#1689" class="Function">equiv-is-prop-equiv</a> <a id="1709" class="Symbol">:</a> <a id="1711" class="Symbol">{</a><a id="1712" href="foundation.propositions.html#1712" class="Bound">l1</a> <a id="1715" href="foundation.propositions.html#1715" class="Bound">l2</a> <a id="1718" class="Symbol">:</a> <a id="1720" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1725" class="Symbol">}</a> <a id="1727" class="Symbol">{</a><a id="1728" href="foundation.propositions.html#1728" class="Bound">A</a> <a id="1730" class="Symbol">:</a> <a id="1732" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1735" href="foundation.propositions.html#1712" class="Bound">l1</a><a id="1737" class="Symbol">}</a> <a id="1739" class="Symbol">{</a><a id="1740" href="foundation.propositions.html#1740" class="Bound">B</a> <a id="1742" class="Symbol">:</a> <a id="1744" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1747" href="foundation.propositions.html#1715" class="Bound">l2</a><a id="1749" class="Symbol">}</a> <a id="1751" class="Symbol">→</a>
  <a id="1755" href="foundation.propositions.html#1728" class="Bound">A</a> <a id="1757" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="1759" href="foundation.propositions.html#1740" class="Bound">B</a> <a id="1761" class="Symbol">→</a> <a id="1763" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1771" href="foundation.propositions.html#1728" class="Bound">A</a> <a id="1773" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="1775" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1783" href="foundation.propositions.html#1740" class="Bound">B</a>
<a id="1785" href="foundation.propositions.html#1689" class="Function">equiv-is-prop-equiv</a> <a id="1805" class="Symbol">{</a><a id="1806" class="Argument">A</a> <a id="1808" class="Symbol">=</a> <a id="1810" href="foundation.propositions.html#1810" class="Bound">A</a><a id="1811" class="Symbol">}</a> <a id="1813" class="Symbol">{</a><a id="1814" class="Argument">B</a> <a id="1816" class="Symbol">=</a> <a id="1818" href="foundation.propositions.html#1818" class="Bound">B</a><a id="1819" class="Symbol">}</a> <a id="1821" href="foundation.propositions.html#1821" class="Bound">e</a> <a id="1823" class="Symbol">=</a>
  <a id="1827" href="foundation.logical-equivalences.html#4644" class="Function">equiv-iff-is-prop</a>
    <a id="1849" class="Symbol">(</a> <a id="1851" href="foundation-core.propositions.html#9665" class="Function">is-prop-is-prop</a> <a id="1867" href="foundation.propositions.html#1810" class="Bound">A</a><a id="1868" class="Symbol">)</a>
    <a id="1874" class="Symbol">(</a> <a id="1876" href="foundation-core.propositions.html#9665" class="Function">is-prop-is-prop</a> <a id="1892" href="foundation.propositions.html#1818" class="Bound">B</a><a id="1893" class="Symbol">)</a>
    <a id="1899" class="Symbol">(</a> <a id="1901" href="foundation-core.propositions.html#4032" class="Function">is-prop-equiv&#39;</a> <a id="1916" href="foundation.propositions.html#1821" class="Bound">e</a><a id="1917" class="Symbol">)</a>
    <a id="1923" class="Symbol">(</a> <a id="1925" href="foundation-core.propositions.html#3677" class="Function">is-prop-equiv</a> <a id="1939" href="foundation.propositions.html#1821" class="Bound">e</a><a id="1940" class="Symbol">)</a>
</pre>
## See also

### Operations on propositions

There is a wide range of operations on propositions due to the rich structure of
intuitionistic logic. Below we give a structured overview of a notable selection
of such operations and their notation in the library.

The list is split into two sections, the first consists of operations that
generalize to arbitrary types and even sufficiently nice
[subuniverses](foundation.subuniverses.md), such as
$n$-[types](foundation-core.truncated-types.md).

| Name                                                        | Operator on types | Operator on propositions/subtypes |
| ----------------------------------------------------------- | ----------------- | --------------------------------- |
| [Dependent sum](foundation.dependent-pair-types.md)         | `Σ`               | `Σ-Prop`                          |
| [Dependent product](foundation.dependent-function-types.md) | `Π`               | `Π-Prop`                          |
| [Functions](foundation-core.function-types.md)              | `→`               | `⇒`                               |
| [Logical equivalence](foundation.logical-equivalences.md)   | `↔`               | `⇔`                               |
| [Product](foundation-core.cartesian-product-types.md)       | `×`               | `product-Prop`                    |
| [Join](synthetic-homotopy-theory.joins-of-types.md)         | `*`               | `join-Prop`                       |
| [Exclusive sum](foundation.exclusive-sum.md)                | `exclusive-sum`   | `exclusive-sum-Prop`              |
| [Coproduct](foundation-core.coproduct-types.md)             | `+`               | _N/A_                             |

Note that for many operations in the second section, there is an equivalent
operation on propositions in the first.

| Name                                                                         | Operator on types           | Operator on propositions/subtypes        |
| ---------------------------------------------------------------------------- | --------------------------- | ---------------------------------------- |
| [Initial object](foundation-core.empty-types.md)                             | `empty`                     | `empty-Prop`                             |
| [Terminal object](foundation.unit-type.md)                                   | `unit`                      | `unit-Prop`                              |
| [Existential quantification](foundation.existential-quantification.md)       | `exists-structure`          | `∃`                                      |
| [Unique existential quantification](foundation.uniqueness-quantification.md) | `uniquely-exists-structure` | `∃!`                                     |
| [Universal quantification](foundation.universal-quantification.md)           |                             | `∀'` (equivalent to `Π-Prop`)            |
| [Conjunction](foundation.conjunction.md)                                     |                             | `∧` (equivalent to `product-Prop`)       |
| [Disjunction](foundation.disjunction.md)                                     | `disjunction-type`          | `∨` (equivalent to `join-Prop`)          |
| [Exclusive disjunction](foundation.exclusive-disjunction.md)                 | `xor-type`                  | `⊻` (equivalent to `exclusive-sum-Prop`) |
| [Negation](foundation.negation.md)                                           | `¬`                         | `¬'`                                     |
| [Double negation](foundation.double-negation.md)                             | `¬¬`                        | `¬¬'`                                    |

We can also organize these operations by indexed and binary variants, giving us
the following table:

| Name                   | Binary | Indexed |
| ---------------------- | ------ | ------- |
| Product                | `×`    | `Π`     |
| Conjunction            | `∧`    | `∀'`    |
| Constructive existence | `+`    | `Σ`     |
| Existence              | `∨`    | `∃`     |
| Unique existence       | `⊻`    | `∃!`    |

### Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
