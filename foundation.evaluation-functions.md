# Evaluation of functions

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="foundation.evaluation-functions.html" class="Module">foundation.evaluation-functions</a> <a id="75" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="131" class="Keyword">open</a> <a id="136" class="Keyword">import</a> <a id="143" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="190" class="Keyword">open</a> <a id="195" class="Keyword">import</a> <a id="202" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="230" class="Keyword">open</a> <a id="235" class="Keyword">import</a> <a id="242" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
</pre>
</details>

## Idea

Consider a family of types `B` over `A` and let `a : A` be an element. The
{{#concept "evaluation function" Agda=ev}} at `a`

```text
  ev : ((x : A) → B x) → B a
```

is the map given by `f ↦ f a`, evaluating dependent functions at `a`.

## Definitions

### The evaluation function

<pre class="Agda"><a id="591" class="Keyword">module</a> <a id="598" href="foundation.evaluation-functions.html#598" class="Module">_</a>
  <a id="602" class="Symbol">{</a><a id="603" href="foundation.evaluation-functions.html#603" class="Bound">l1</a> <a id="606" href="foundation.evaluation-functions.html#606" class="Bound">l2</a> <a id="609" class="Symbol">:</a> <a id="611" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="616" class="Symbol">}</a> <a id="618" class="Symbol">{</a><a id="619" href="foundation.evaluation-functions.html#619" class="Bound">A</a> <a id="621" class="Symbol">:</a> <a id="623" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="626" href="foundation.evaluation-functions.html#603" class="Bound">l1</a><a id="628" class="Symbol">}</a> <a id="630" class="Symbol">{</a><a id="631" href="foundation.evaluation-functions.html#631" class="Bound">B</a> <a id="633" class="Symbol">:</a> <a id="635" href="foundation.evaluation-functions.html#619" class="Bound">A</a> <a id="637" class="Symbol">→</a> <a id="639" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="642" href="foundation.evaluation-functions.html#606" class="Bound">l2</a><a id="644" class="Symbol">}</a> <a id="646" class="Symbol">(</a><a id="647" href="foundation.evaluation-functions.html#647" class="Bound">a</a> <a id="649" class="Symbol">:</a> <a id="651" href="foundation.evaluation-functions.html#619" class="Bound">A</a><a id="652" class="Symbol">)</a>
  <a id="656" class="Keyword">where</a>

  <a id="665" href="foundation.evaluation-functions.html#665" class="Function">ev</a> <a id="668" class="Symbol">:</a> <a id="670" class="Symbol">((</a><a id="672" href="foundation.evaluation-functions.html#672" class="Bound">x</a> <a id="674" class="Symbol">:</a> <a id="676" href="foundation.evaluation-functions.html#619" class="Bound">A</a><a id="677" class="Symbol">)</a> <a id="679" class="Symbol">→</a> <a id="681" href="foundation.evaluation-functions.html#631" class="Bound">B</a> <a id="683" href="foundation.evaluation-functions.html#672" class="Bound">x</a><a id="684" class="Symbol">)</a> <a id="686" class="Symbol">→</a> <a id="688" href="foundation.evaluation-functions.html#631" class="Bound">B</a> <a id="690" href="foundation.evaluation-functions.html#647" class="Bound">a</a>
  <a id="694" href="foundation.evaluation-functions.html#665" class="Function">ev</a> <a id="697" href="foundation.evaluation-functions.html#697" class="Bound">f</a> <a id="699" class="Symbol">=</a> <a id="701" href="foundation.evaluation-functions.html#697" class="Bound">f</a> <a id="703" href="foundation.evaluation-functions.html#647" class="Bound">a</a>
</pre>
### The evaluation function with an explicit type family

<pre class="Agda"><a id="776" class="Keyword">module</a> <a id="783" href="foundation.evaluation-functions.html#783" class="Module">_</a>
  <a id="787" class="Symbol">{</a><a id="788" href="foundation.evaluation-functions.html#788" class="Bound">l1</a> <a id="791" href="foundation.evaluation-functions.html#791" class="Bound">l2</a> <a id="794" class="Symbol">:</a> <a id="796" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="801" class="Symbol">}</a> <a id="803" class="Symbol">{</a><a id="804" href="foundation.evaluation-functions.html#804" class="Bound">A</a> <a id="806" class="Symbol">:</a> <a id="808" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="811" href="foundation.evaluation-functions.html#788" class="Bound">l1</a><a id="813" class="Symbol">}</a> <a id="815" class="Symbol">(</a><a id="816" href="foundation.evaluation-functions.html#816" class="Bound">B</a> <a id="818" class="Symbol">:</a> <a id="820" href="foundation.evaluation-functions.html#804" class="Bound">A</a> <a id="822" class="Symbol">→</a> <a id="824" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="827" href="foundation.evaluation-functions.html#791" class="Bound">l2</a><a id="829" class="Symbol">)</a> <a id="831" class="Symbol">(</a><a id="832" href="foundation.evaluation-functions.html#832" class="Bound">a</a> <a id="834" class="Symbol">:</a> <a id="836" href="foundation.evaluation-functions.html#804" class="Bound">A</a><a id="837" class="Symbol">)</a>
  <a id="841" class="Keyword">where</a>

  <a id="850" href="foundation.evaluation-functions.html#850" class="Function">ev-dependent-function</a> <a id="872" class="Symbol">:</a> <a id="874" class="Symbol">((</a><a id="876" href="foundation.evaluation-functions.html#876" class="Bound">x</a> <a id="878" class="Symbol">:</a> <a id="880" href="foundation.evaluation-functions.html#804" class="Bound">A</a><a id="881" class="Symbol">)</a> <a id="883" class="Symbol">→</a> <a id="885" href="foundation.evaluation-functions.html#816" class="Bound">B</a> <a id="887" href="foundation.evaluation-functions.html#876" class="Bound">x</a><a id="888" class="Symbol">)</a> <a id="890" class="Symbol">→</a> <a id="892" href="foundation.evaluation-functions.html#816" class="Bound">B</a> <a id="894" href="foundation.evaluation-functions.html#832" class="Bound">a</a>
  <a id="898" href="foundation.evaluation-functions.html#850" class="Function">ev-dependent-function</a> <a id="920" class="Symbol">=</a> <a id="922" href="foundation.evaluation-functions.html#665" class="Function">ev</a> <a id="925" href="foundation.evaluation-functions.html#832" class="Bound">a</a>
</pre>
### The evaluation function for nondependent functions

<pre class="Agda"><a id="996" class="Keyword">module</a> <a id="1003" href="foundation.evaluation-functions.html#1003" class="Module">_</a>
  <a id="1007" class="Symbol">{</a><a id="1008" href="foundation.evaluation-functions.html#1008" class="Bound">l1</a> <a id="1011" href="foundation.evaluation-functions.html#1011" class="Bound">l2</a> <a id="1014" class="Symbol">:</a> <a id="1016" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1021" class="Symbol">}</a> <a id="1023" class="Symbol">{</a><a id="1024" href="foundation.evaluation-functions.html#1024" class="Bound">A</a> <a id="1026" class="Symbol">:</a> <a id="1028" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1031" href="foundation.evaluation-functions.html#1008" class="Bound">l1</a><a id="1033" class="Symbol">}</a> <a id="1035" class="Symbol">(</a><a id="1036" href="foundation.evaluation-functions.html#1036" class="Bound">B</a> <a id="1038" class="Symbol">:</a> <a id="1040" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1043" href="foundation.evaluation-functions.html#1011" class="Bound">l2</a><a id="1045" class="Symbol">)</a> <a id="1047" class="Symbol">(</a><a id="1048" href="foundation.evaluation-functions.html#1048" class="Bound">a</a> <a id="1050" class="Symbol">:</a> <a id="1052" href="foundation.evaluation-functions.html#1024" class="Bound">A</a><a id="1053" class="Symbol">)</a>
  <a id="1057" class="Keyword">where</a>

  <a id="1066" href="foundation.evaluation-functions.html#1066" class="Function">ev-function</a> <a id="1078" class="Symbol">:</a> <a id="1080" class="Symbol">(</a><a id="1081" href="foundation.evaluation-functions.html#1024" class="Bound">A</a> <a id="1083" class="Symbol">→</a> <a id="1085" href="foundation.evaluation-functions.html#1036" class="Bound">B</a><a id="1086" class="Symbol">)</a> <a id="1088" class="Symbol">→</a> <a id="1090" href="foundation.evaluation-functions.html#1036" class="Bound">B</a>
  <a id="1094" href="foundation.evaluation-functions.html#1066" class="Function">ev-function</a> <a id="1106" class="Symbol">=</a> <a id="1108" href="foundation.evaluation-functions.html#665" class="Function">ev</a> <a id="1111" href="foundation.evaluation-functions.html#1048" class="Bound">a</a>
</pre>
### The evaluation function of implicit functions

<pre class="Agda"><a id="1177" class="Keyword">module</a> <a id="1184" href="foundation.evaluation-functions.html#1184" class="Module">_</a>
  <a id="1188" class="Symbol">{</a><a id="1189" href="foundation.evaluation-functions.html#1189" class="Bound">l1</a> <a id="1192" href="foundation.evaluation-functions.html#1192" class="Bound">l2</a> <a id="1195" class="Symbol">:</a> <a id="1197" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1202" class="Symbol">}</a> <a id="1204" class="Symbol">{</a><a id="1205" href="foundation.evaluation-functions.html#1205" class="Bound">A</a> <a id="1207" class="Symbol">:</a> <a id="1209" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1212" href="foundation.evaluation-functions.html#1189" class="Bound">l1</a><a id="1214" class="Symbol">}</a> <a id="1216" class="Symbol">{</a><a id="1217" href="foundation.evaluation-functions.html#1217" class="Bound">B</a> <a id="1219" class="Symbol">:</a> <a id="1221" href="foundation.evaluation-functions.html#1205" class="Bound">A</a> <a id="1223" class="Symbol">→</a> <a id="1225" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1228" href="foundation.evaluation-functions.html#1192" class="Bound">l2</a><a id="1230" class="Symbol">}</a> <a id="1232" class="Symbol">(</a><a id="1233" href="foundation.evaluation-functions.html#1233" class="Bound">a</a> <a id="1235" class="Symbol">:</a> <a id="1237" href="foundation.evaluation-functions.html#1205" class="Bound">A</a><a id="1238" class="Symbol">)</a>
  <a id="1242" class="Keyword">where</a>

  <a id="1251" href="foundation.evaluation-functions.html#1251" class="Function">ev-implicit-function</a> <a id="1272" class="Symbol">:</a> <a id="1274" class="Symbol">({</a><a id="1276" href="foundation.evaluation-functions.html#1276" class="Bound">x</a> <a id="1278" class="Symbol">:</a> <a id="1280" href="foundation.evaluation-functions.html#1205" class="Bound">A</a><a id="1281" class="Symbol">}</a> <a id="1283" class="Symbol">→</a> <a id="1285" href="foundation.evaluation-functions.html#1217" class="Bound">B</a> <a id="1287" href="foundation.evaluation-functions.html#1276" class="Bound">x</a><a id="1288" class="Symbol">)</a> <a id="1290" class="Symbol">→</a> <a id="1292" href="foundation.evaluation-functions.html#1217" class="Bound">B</a> <a id="1294" href="foundation.evaluation-functions.html#1233" class="Bound">a</a>
  <a id="1298" href="foundation.evaluation-functions.html#1251" class="Function">ev-implicit-function</a> <a id="1319" href="foundation.evaluation-functions.html#1319" class="Bound">f</a> <a id="1321" class="Symbol">=</a> <a id="1323" href="foundation.evaluation-functions.html#1319" class="Bound">f</a> <a id="1325" class="Symbol">{</a><a id="1326" href="foundation.evaluation-functions.html#1233" class="Bound">a</a><a id="1327" class="Symbol">}</a>
</pre>
### The evaluation function of implicit functions, specified with an explicit type family

<pre class="Agda"><a id="1433" class="Keyword">module</a> <a id="1440" href="foundation.evaluation-functions.html#1440" class="Module">_</a>
  <a id="1444" class="Symbol">{</a><a id="1445" href="foundation.evaluation-functions.html#1445" class="Bound">l1</a> <a id="1448" href="foundation.evaluation-functions.html#1448" class="Bound">l2</a> <a id="1451" class="Symbol">:</a> <a id="1453" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1458" class="Symbol">}</a> <a id="1460" class="Symbol">{</a><a id="1461" href="foundation.evaluation-functions.html#1461" class="Bound">A</a> <a id="1463" class="Symbol">:</a> <a id="1465" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1468" href="foundation.evaluation-functions.html#1445" class="Bound">l1</a><a id="1470" class="Symbol">}</a> <a id="1472" class="Symbol">(</a><a id="1473" href="foundation.evaluation-functions.html#1473" class="Bound">B</a> <a id="1475" class="Symbol">:</a> <a id="1477" href="foundation.evaluation-functions.html#1461" class="Bound">A</a> <a id="1479" class="Symbol">→</a> <a id="1481" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1484" href="foundation.evaluation-functions.html#1448" class="Bound">l2</a><a id="1486" class="Symbol">)</a> <a id="1488" class="Symbol">(</a><a id="1489" href="foundation.evaluation-functions.html#1489" class="Bound">a</a> <a id="1491" class="Symbol">:</a> <a id="1493" href="foundation.evaluation-functions.html#1461" class="Bound">A</a><a id="1494" class="Symbol">)</a>
  <a id="1498" class="Keyword">where</a>

  <a id="1507" href="foundation.evaluation-functions.html#1507" class="Function">ev-implicit-function&#39;</a> <a id="1529" class="Symbol">:</a> <a id="1531" class="Symbol">({</a><a id="1533" href="foundation.evaluation-functions.html#1533" class="Bound">x</a> <a id="1535" class="Symbol">:</a> <a id="1537" href="foundation.evaluation-functions.html#1461" class="Bound">A</a><a id="1538" class="Symbol">}</a> <a id="1540" class="Symbol">→</a> <a id="1542" href="foundation.evaluation-functions.html#1473" class="Bound">B</a> <a id="1544" href="foundation.evaluation-functions.html#1533" class="Bound">x</a><a id="1545" class="Symbol">)</a> <a id="1547" class="Symbol">→</a> <a id="1549" href="foundation.evaluation-functions.html#1473" class="Bound">B</a> <a id="1551" href="foundation.evaluation-functions.html#1489" class="Bound">a</a>
  <a id="1555" href="foundation.evaluation-functions.html#1507" class="Function">ev-implicit-function&#39;</a> <a id="1577" class="Symbol">=</a> <a id="1579" href="foundation.evaluation-functions.html#1251" class="Function">ev-implicit-function</a> <a id="1600" href="foundation.evaluation-functions.html#1489" class="Bound">a</a>
</pre>
## See also

- The
  [action on identifications](foundation.action-on-identifications-functions.md)
  of the evaluation map is the function `a ↦ λ p → htpy-eq p a` defined in
  [Function extensionality](foundation.function-extensionality.md).