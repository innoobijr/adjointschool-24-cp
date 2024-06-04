<figure id="fig:enter-label-0">
    <img alt="" src="https://raw.githubusercontent.com/innoobijr/adjointschool-24-cp/main/img/context-0.png" style="width:80.0%" />
</figure>

Introduction

In this blog post we discuss the main (&#x2018;algebraic&#x2019;) ideas of term
rewriting and then discuss how it can be applied to term graph and
arbitrary graph (i.e. string diagrams) rewriting. Our group is
interested in the application of critical pairs for string diagram
rewriting. We read *Critical Pairs in Term Graph Rewriting* and given
the task before us wanted to understand the following question: if Plump
needed a new decision procedure for critical pairs on graph rewriting,
how would we know what we might need for string diagram rewriting? In
the this blog post we start at the root (pun intended) and work our way
up from term rewriting to rewriting on arbitrary graphs. The goal is to
understand, for example, why we can&#x2019;t just apply, without modification,
the ideas in Plump&#x2019;s paper to rewriting the *&#955;*-calculus.

Preliminaries

On theories, signatures, and terms

A theory can be thought as a &#x201C;finite or an infinite set of formulas
characterized by common grammatical rules, allowed functions and
predicates, and a domain of values"[^1] . First order logic is based on
the following four elements: variables, logical symbols (boolean
connectives and quantifiers), non-logical symbols (functions,
predicates, constants), and syntax (rules about constructing valid
formulas in the logic). Typically, a theory defines restrictions on the
non-logical symbols. This set of **non-logical symbols** is called the
**signature**. With a signature *&#931;*, A *&#931;*-formula is constructed using
only non-logical symbols from *&#931;*. A first-order *&#931;*- theory T consists
of a set of *&#931;*-sentences. In the case of rewriting systems, the only
logical symbol we care about is equality. Said differently, with
rewriting systems it makes sense to restrict not only the set of
non-logical symbols, but also logical symbols. Such a restriction exists
in the **equality logic**. It is a the quantifier-free fragment of FOL
with equality as the singular logical symbol.

**Definition 1**. *A *signature* *&#931;* consists of non-empty set of
*function symbols* each equipped with a fixed *arity*. The arity of a
function symbol *F* is a natural number, indicating the number of
arguments it is supposed to have. Nullary functions are allowed: these
are called *constant symbols*.A term is a strings of symbols from an
alphabet. consisting of the signature and a countably infinite set *Var*
of variables. The set of terms over *&#931;* is indicated as
&#119983;(*&#931;*,&#8198;*V**a**r*). All variables and functions are terms.*

On abstract reduction systems

More generally, we can view term rewriting systems as instances of an
abstract reduction system.

**Definition 2** (Abstract reduction system ).      An abstract reduction systems is a pair $(A, \rightarrow)$, where $\rightarrow$ is a binary relation on the set $A$, i.e $ \rightarrow  \subseteq A \times A$. 


In an abstract reduction system, we can view the relation &#8594; as
representing program evaluation
(*a*<sub>0</sub>&#8196;&#8594;&#8196;*a*<sub>1</sub>&#8943;*a*<sub>*n*</sub>) or expressing
identities (*a*<sub>0</sub>&#8196;&#8592;&#8196;*a*<sub>1</sub>&#8943;&#8196;&#8594;&#8196;*a*<sub>2</sub>&#8943;). The
former describes some directed computation from one element to another.
The latter implies the *reflexive transitive symmetric closure*
($\xleftrightarrow{\text{\*}}$): there exists some finite path the first
term to the second and vice versa. By closure we use the common
description : the *P* closure of *R* is the least set with the property
*P* which contains *R*. So the $\xleftrightarrow{\text{\*}}$ is the
least reflexive transitive symmetric relation which contains &#8594;. Given
two terms *x* and *y*, we say that *X* is **reducible** if and only if
there is a *y* such that *x*&#8196;&#8594;&#8196;*y*. *x* is in **normal form** if it is
not **reducible**. *y* is a **normal form** of *x* if y is in normal
form and there exist some finite path from *x* to *y*, i.e
$x \xrightarrow{\text{\*}} y$. *x* and *y* are **joinable** (*x*&#8196;&#8595;&#8196;*y*)
if there is a *z* such that
$x \xrightarrow{\text{\*}} z \xleftarrow{\text{\*}} y$.

**Definition 3**. *A reduction &#8594; is called:*

* terminating iff there is not infinite descending chain $x_0 \rightarrow x_1 \rightarrow \cdots$

* confluent [^2]  iff
$x \xrightarrow{\text{\*}} z \xleftarrow{\text{\*}} y \implies x\downarrow y$*

Whether a string, terms, or graph, rewriting system are mechanisms for
computing stepwise transformation of objects. A term rewriting systems
(TRS) is an abstract reduction system where the objects are first-order
terms and wher ethe reduction relation is presented as reduction rules
or rewrite rules. The canonical term rewriting systems were viewed as
decision procedures for proving the validity of equalities in
first-order equational theories.

Term rewriting and all that!

How do we know when any two arbitrary terms (from some grammar) are
equivalent and why should we care if any two terms are equivalent? One
approach to answer this question is start from both terms and search
exhaustively search until we find term in a set of finite paths that
&#x2019;generalizes&#x2019; the two term - a process akin to anti-unification. The
other would be to use a set of rules to reduce both terms to their
normal forms and then testing those normal forms are
joinable/equivalent - akin to unification. This is the task of
confluence tests. From this description, it seems clear that it is
difficult to prove confluence if our reductions steps never terminate.
Therefore it seems intuitive that termination is necessary to prove
confluence. This is in essence what we learn about term rewriting
systems: *confluence is undecidable for non-terminating term rewrite
systems*. However we find that in term graph rewriting, it is possible
to take a non-terminating term rewriting system and transform it into a
terminating term-graph rewrite system! For now, before we return to our
discussion on confluence, let&#x2019;s introduce term rewriting and term graph
rewriting more formally using the universal algebra we presented
above.  

**Definition 4** (Term Rewriting System). A rewrite or reduction rule is an identity $l \equiv r$ where $l$ is not a variable  and all the varialbles in $r$ are also in $l$. A term rewriting system is a set of a pairs consisting of the set of rewrite rules and a $\Sigma$ definition the non-logical symbols of the grammar. 


Context, overlaps, and critical pairs

In term rewriting, a position in a term $t$ detemines both a prefix of $t$, i.e holes  and the occurrence of the subterm with the prefix. The prefix of t that corresponds to p is denoted by $t[ ]_p$, the subterm  occurring at position $p$ by $t|_p$. When rewrites occur they occur in some context.


$$
\begin{array}[t]{ccc}
         t = f_{1}(g_{2}(a_{3})) & t[]_2=f_{1}(\Box(a_{3})) & t|_{2} = g \\
\end{array}
$$

**Definition 5** (Context). A context is a term containing zero, one or more occurrences of a special constant symbols $\Box$ denoting holes, a term over the extended signature $\Sigma \cup \lbrace \Box \rbrace$. If $C$ is a context containing exactly n holes, and $t_1,\cdots,t_n$ are terms, then $C[t_1,\cdots,t_n ]$ denotes the result of replacing the holes of $C$ from left to right by $t_1,\cdots,t_n$ . To distinguish between difference occurrence of a sub term in a term we adopt a definition of occurrence. We define an occurrence as the ordered pair $\langle s | C[] \rangle$. This uniquely determines the occurrence of $s$ in $C[s]$ with the one-hole context $C[]$. That is every occurrence of the sub-term can be replaced by a one-hold context. For a given term $s$ this new term $s^'$ with holes can be called the prefix of $s$.

**Definition 6** (Reduction Step).  A \textit{reduction step} according to the reduction rule $p: l \rightarrow r$ consists of contracting a redex within an arbitrary context: \[ C[l^\sigma] \xrightarrow[p]{} C[r^\sigma ] \]

Given a reduction rule *p*, an instance of *p* is obtained by applying a
substitution *&#963;*. The result is an *atomic reduction step*
$l^{\sigma} \xrightarrow{p} r^{\sigma}$. The left-hand side
*l*<sup>*&#963;*</sup> is called the **redex** and the right-hand side
*r*<sup>*&#963;*</sup> is called its **embedding**. A term may contain one or
more occurrences of a redex. A reduction step consists of *contracting*
a redex within an arbitrary context.

**Example 1**. Given rule $p : F(G(x),y) \rightarrow F(x, x)$ and substitution $\sigma : \lbrace x \rightarrow 0, y  \rightarrow G(x) \rbrace$, we get the following reduction step: \[ F(G(0), G(x)) \xrightarrow[p]{} F(0,0)\] with redex $F(G(0), G(x))$, and embedding $F(0,0)$. With a term $F(z, G(F(G(0), (G(x)))))$ and the contraction describe above, we get the following reduction step \[F(z, G(F(G(0), (G(x))))) \xrightarrow[p]{} F(z,G(F(0,0)))\] where the context is $F(z, G(\Box))$.


The contraction of redex can lead to some interesting and uninteresting
conflicts. Non-confluence can usually be attributed to the specific case
of conflicts : the overlapping of reductions. Remember that redexes
depends on some rewriting rule and some substitution of terms. In order
to understand if a TRS is confluent it is important to know when such
overlaps are harmful or harmless. In general, a redex is harmful it is
overlaps. The following example will illustrate this case:

**Example 2** (). Consider the TRS with the following rules:
\[ p_1 : F(G(x),y)  \rightarrow  x \]
\[ p_1 : G(a)  \rightarrow  b\]

The term $F(G(a), x)$ can be reduced in two ways: $F(G(a),x) \xrightarrow[p]{} a$ and $F(G(a),x) \xrightarrow[p]{} F(b,x)$, where terms $a$ and $F(b,x)$ are normal forms. The following TRS is not confluent as $a$ and $F(G(b,x))$ have no common reduct. The reductions rules and substitutions give use the two redexes: $F(G(a),x)$ and $G(a)$. Both redexes share the function symbol $G$ in both. This sharing means that a contraction using the second rule \textit{destroys} $G$ thus making it impossible to apply $p_1$.  Each of the left-hand side of the rules on matches (redex) expresses in many ways the \textit{context} of the rewriting. This say that the TRS does not support rewriting in arbitrary contexts in a way that preserves confluence. We need to find the redexes that cause these conflicts and use them to generate additional rules that allow us to reach a common reduction. This is known as completion or is the more operational contexts \textit{saturation}.
Again overlap result when symbols are shared between any two redexes. We do this by defining a \textit{pattern} of a redex as the fixed part of the left-hand side. The result is a \textif{prefix} of the redex where all its variables are left out, i,e a potential many-hole context. It is the context that is created by replacing all variables in the redex with holes.  So to be more precise, two redexs overlap when their patterns share a symbol occurrence. 


Redex considered harmful?

However, it is not the case that all overlaps of redexes are harmful.
Some overlaps may occur after one-step reductions, but may be unified
after a finite number of steps. This is the difference between
*confluence* and *local confluence*. Another way to say this is that
local confluence can also be a sufficient criterion for confluence of a
term rewriting system (TRS). This allow us to understand confluence of a
TRS by thinking of how overlapping redexes over a number of steps/paths
are contracted. From the definition described above this requires
considering how holes in context can be substituted to preserve the
pattern between two redexes. But there are potentially infinitely many
possible substitutions and infinitely many cases of redex overlaps
accordingly. Operationally, we need an efficient method of proving
confluence that doesn&#x2019;t require searching over the entire space of
substitutions. The idea here is to associate each pair of overlapping
redex rules with a more general cases of an overlap from which other
cases can be generated. In literature this is exactly where *critical
pairs*.

The key idea behind critical pairs is the following: all overlapping
redexes can be treated as substitution instances of some generate
pattern. Using our definition of confluence given in Section
<a href="#" data-reference-type="ref" data-reference="">5</a> on
abstract rewriting systems: a TRS is confluent if all of its critical
pairs are *joinable*.

**Definition 7** (critical pairs ). Let $p_i: l_i\rightarrow r_i$, $i = 1,2,$ be two rules whose variables have been renamed such that $\mathcal{V}ar(l_1,r_1)  \cap \mathcal{V}ar(l_2,r_2) = \emptyset$. A pair of one-step reductions  $\langle \theta r_{1}, \theta l_{1}[\theta r_2]_p \rangle$ is a **critical pair** if  


1.  Let $p \in \mathcal{P}os(l_1)$ such that $l_{1}|_{p}$ is not a variable

2.  $\theta$ be an maximum unifier of $l_{1}|_{p} =^{?} l_{2}$. 

This is a definition and constraint will come up again in confluence
decision procedures in term graph rewriting. But before we get into the
similarities let stalk a little but about the different between trees
and graphs as applied to terms rewriting.

Structure and Contents (from Trees to Graphs)

<figure id="fig:labelled-tree">
    <img alt="" src="https://raw.githubusercontent.com/innoobijr/adjointschool-24-cp/main/img/lab_with_iso.png" style="width:80.0%" />
</figure>


The structure of a term can be represented by visualizing it as a tree
where function symbols are nodes are arrows point to arguments of the
function. There is a function node with no arrows point to it: we call
this node the **root node**. Except these are not your simple trees. We
require trees with a labeling and numbering on nodes. The numbering give
is a terms **position** in the tree. Formally, the **position** is a
string over the alphabet of positive integers where the root position
(the root node) is the empty string. Labelling is necessary to
distinguish between similar (isomorphic) trees. This is all to say is
that our classical *tree* is just a labelled rooted undirected graph.
The tree as a data structure captures the content of a term in node
labels. Instead of labelling the arrows between nodes, our labeling
rests with the node. What this does is to leave all information about
the *content* and *structure* of terms in the nodes. We can distinguish
the two trees in Figure
<a href="#fig:labelled-tree" data-reference-type="ref"
data-reference="fig:labelled-tree">2</a>.b because testing for
equivalence is based on both its *position* and *node label*. However,
computationally this is an expensive representation of terms. In Figure
<a href="#fig:labelled-tree" data-reference-type="ref"
data-reference="fig:labelled-tree">2</a>.a we have a situation where we
have a duplicated term. It would be more efficient to just *share*
references to this term rather than duplicating it. But this simple
approach would be problematic in this model. This is because our node
label contains information on both the *content* and *structure* of the
terms. So even if we see the term *b* at multiple levels in our tree,
they are indeed not equivalent. This is because our test of equivalence
would have to take into account both the *p**o**s**i**t**i**o**n* and
the *n**o**d**e* label. In order to actually share references, we need
to decouple *s**t**r**u**c**t**u**r**e* from *c**o**n**t**e**n**t*. We
need to move information about the *position* to the graph level. In
this approach, our *p**o**s**i**t**i**o**n* or *numbering of nodes*
would now be attached to the arrows or edges. We would also need to
require that all isomorphic subtrees be replace by only óne&#x2019; amounting
to an equivalence class of nodes each considered as a node. This process
would turn our previously rooted undirected graph into a directed
acyclic graph. One of the really interesting things about moving from
the former to a DAG is that what were once previously non-terminating
TRS can now become terminating. This has noting to do with our signature
and everything to do with the choice of a DAG.

In the next section we discuss the paper by Detlef Plump called
*Critical pairs in term graph rewriting*. The goal of this paper is to
understand how much of the work describe above for critical pairs that
is used in term rewriting (with trees) can apply to rewriting on graphs.
Before we move on let just review some keys points.

1.  we are still working with first-order terms in a qualifier-free
    fragment of first-order logic: *equality logic*

2.  We&#x2019;ve moved from (simple trees) to graphs: Our signature has not
    changed just the data model used to represent terms

3.  Our use of a DAG allows the use of references to used instead of
    duplicated nodes. Although, we will need to generalize our graph by
    removing the restrict that each edge have only two vertices
    (endpoints). That is we need to move from just the generic graph to
    the hypergraph.

Algebraic graph transformation and Plump&#x2019;s (strong) joinability

There are two way of approaching graph rewriting. In many way they
mirror term rewriting (matching, deleting, copying). However as we
discussed above the context is different. Our context is not a *strings
with a holes* but *graphs with holes*. This can be best visualize in the
algebraic approach to graph transformation via *push-outs*. Push-outs
are to graphs what syntactic unification and contraction are to term
rewriting (on trees). We will define the push-out approach in a bit but
first a bit about hyperxgraphs. In the previous section, we highlighted
how we can move from trees to graphs (DAGs). For term graph rewriting,
we will generalize graph even further and use the notion of a
*hypergraph*. In a hypergraph unlike simple graphs, edge (called
hyperedges) can have multiple targets. The formal definition is as
follows:

**Definition 8** (Hypergraph ). *A hypergraph G over *&#931;*,&#8198;*X* is a
system
*G*&#8196;=&#8196;(*V*<sub>*G*</sub>,&#8198;*E*<sub>*G*</sub>,&#8198;*s*<sub>*G*</sub>,&#8198;*t*<sub>*G*</sub>,&#8198;*l*<sub>*G*</sub>)
where *V*<sub>*G*</sub>,&#8198;*E*<sub>*G*</sub> are finite sets of nodes
(vertices) and hyperedges,
*s*<sub>*G*</sub>&#8196;:&#8196;*E*<sub>*G*</sub>&#8196;&#8594;&#8196;*V*<sub>*G*</sub>,
*t*<sub>*G*</sub>&#8196;:&#8196;*E*<sub>*G*</sub>&#8196;&#8594;&#8196;*V*<sub>*G*</sub><sup>\*</sup>
are mappings that assign a source and a list of target nodes to each
hyperedge, and *l*<sub>*G*</sub>&#8196;:&#8196;*E*<sub>*G*</sub>&#8196;&#8594;&#8196;*&#931;*&#8197;&#8746;&#8197;*X* is a
labelling map such that
*a**r**i**t**y*(*l*<sub>*G*</sub>(*e*))&#8196;=&#8196;*l**e**n**g**t**h*(*t*<sub>*G*</sub>(*e*)).*

This again is a choice of implementation. Figure
<a href="#" data-reference-type="ref" data-reference="">5</a>
demonstrate what we&#x2019;ve done. With a hypergraph, we drop the restriction
that edges must have only two end points. To capture this structure, our
morphisms are also a bit different. Instead of relation two terms in a
trees, our morphisms are between graphs.

**Definition 9** (graph morphism). *A *graph morphism* *f*&#8196;:&#8196;*G*&#8196;&#8594;&#8196;*H*
between graphs *G* and *H* consists of two functions
*f*<sub>*V*</sub>&#8196;:&#8196;*V*<sub>*G*</sub>&#8196;&#8594;&#8196;*V*<sub>*H*</sub> and
*f*<sub>*E*</sub>&#8196;:&#8196;*E*<sub>*G*</sub>&#8196;&#8594;&#8196;*E*<sub>*H*</sub> that preserve
the labels and targets of nodes,
*l*<sub>*H*</sub>&#8197;&#8728;&#8197;*f*<sub>*E*</sub>&#8196;=&#8196;*l*<sub>*G*</sub> and
*t*<sub>*H*</sub>&#8197;&#8728;&#8197;*f*<sub>*E*</sub>&#8196;=&#8196;*f*<sub>*V*</sub><sup>\*</sup>&#8197;&#8728;&#8197;*t*<sub>*G*</sub>.
If this *f* is injective and surjective, then it is an *isomorphism* and
*G* and *H* are *isomorphic*.*

In the algebraic/categorical approach, working with isomorphism classes
of term graphs would cause us to lose access to nodes and edges.
Instead, Plump uses *standard term graphs* which represent their
isomorphism classes of of those node. In order to do this we introduce
the notion of *access path*. An access path for a node *v* in term graph
*G* is a possible empty sequence of labels representing a path from the
root to v. For example, the access path
&#10216;*i*<sub>1</sub>,&#8198;*i*<sub>2</sub>,&#8198;&#8901;*i*<sub>*n*</sub>&#10217; indicates that
following path exists
&#10216;*v*<sub>0</sub>*i*<sub>1</sub>,&#8198;*v*<sub>1</sub>,&#8198;*i*<sub>2</sub>,&#8198;*v*<sub>2</sub>,&#8198;&#8901;*i*<sub>*n*</sub>,&#8198;*v*&#10217;
where *v*<sub>0</sub>&#8196;=&#8196;*r**o**o**t* and *v*<sub>*n*</sub>&#8196;=&#8196;*v*. The
set of all access paths is denoted *A**c**c*(*v*). For every term graph
we can construct an isomorphic standard term graph by replacing each
node *v* with *A**c**c*(*v*) and modifying the edge set and the labeling
and target functions correspondingly. We will call a graph *H* a
*collasped* version of *G*, if there is a surjective graph morphism
*f*&#8196;:&#8196;*G*&#8196;&#8594;&#8196;*H* such that
*f*<sub>*v*</sub>(*r**o**o**t*<sub>*G*</sub>)&#8196;=&#8196;*r**o**o**t*<sub>*H*</sub>.
This is usually denoted &#8805; and the inverse (copying) is denoted as &#8804;
[^3]. A term graph is a tree if there is only a unique path from the
root to each other node and it is fully collapsed if and only if for all
nodes *v* and *w*, equality of the terms representing nodes*v* and *w*
implies that node *v* and *w* are equal.

<figure id="fig:enter-label">
<img alt="" src="https://raw.githubusercontent.com/innoobijr/adjointschool-24-cp/main/img/context.png" style="width:50.0%" />
</figure>

Using the definitions of term rewriting given in Section
<a href="#" data-reference-type="ref" data-reference="">5</a>, we will
now define term graph rewriting.

Instance, redex, and context

**Definition 10** ((Hyper-)graph Rewriting System). *A hypergraph
rewriting system &#10216;*&#931;*,&#8198;&#8475;&#10217; consists of a signature *&#931;* and a set of &#8475; of
rules over *&#931;*.*

When proving confluence in hypergraph goal is to find *isomorphic
graphs*. It is a view of confluence that considers hypergraphs
transformation "up to isomorphism".

**Lemma 1** (). *A hypergraph transformation systems &#10216;*&#931;*,&#8198;&#8475;&#10217; is
confluence (locally confluent) if and only if the relation &#8658;<sub>&#8475;</sub>
on isomorphism classes of hypergraphs over *&#931;* is confluent (locally
confluent). Additionally the system &#10216;*&#931;*,&#8198;&#8475;&#10217; is terminating if
&#8658;<sub>&#8475;</sub> is terminating.*

Using the same language we used for term rewriting, given a node *v* in
the term graph *G* and a term rewrite rule *l*&#8196;&#8594;&#8196;*r*, the pair
&#10216;*v*,,*l*&#8196;&#8594;&#8196;*r*&#10217; is our redex if the term subgraph at *v* in *G* is an
instance of *l*. While term rewriting systems have *reduction rules*, in
term graph rewriting we have similar ideas except in a new context. As
previously mentioned, in a graph system a rewrite rule is morphism
between (hyper-)graphs. These morphisms are mappings between the sets of
nodes and edges that they preserve sources, targets, and labels.
Similarly in term rewriting systems, we have reductions steps. In term
graph rewriting we have the corresponding graph transformations -
evaluations steps. Evaluation steps create *derivations*. When we apply
a rewrite rule to a graph, the core idea is to identify the subgraph
corresponding to the left-hand side of the rewrite, "cut it out",
replace it with the right-hand side graph, and then "glue" it back. This
is the ideas behind the *double pushout*.

The double push-out and duality of labeling and tracing

<figure id="fig:ex">
<img alt="" src="https://raw.githubusercontent.com/innoobijr/adjointschool-24-cp/main/img/dpo.png" style="width:50.0%" />
</figure>

<figure id="fig:rsteps">
<img src="Pictures/rsteps.png" alt="" style="width:8cm" />
</figure>

The double push-out (DPO) might be hard to follow at first. As an aid,
we&#x2019;ve include in Fig.<a href="#fig:ex" data-reference-type="ref"
data-reference="fig:ex">4</a> a visualize of the DPO approach that
capture the rewrite steps in Fig.
<a href="#fig:rsteps" data-reference-type="ref"
data-reference="fig:rsteps">5</a>. In the double push-out approach, our
rewriting rule *p* is a *span*
$\lozenge l \xleftarrow{l} \mathcal{D} \xrightarrow{r} \lozenge r$ of
morphisms that start from *gluing object* &#119967; and ends in the left-hand
side &#9674;*l* and right-hand side &#9674;*r*. Our *r**e**d**e**x* for the rule *p*
is a morphism *g*&#8196;:&#8196;&#9674;*l*&#8196;&#8594;&#8196;&#119970; for the left-hand into an intermediate
graph &#119970;. The push-out only exists if there is a *host object*
&#119970;<sub>1</sub> with a morphism *q* from our interface &#119967; that allows us to
recover the match and also embed our intermediate graph &#119970;. The match
reconstructed from two morphisms (*q* and *l*) is called the *pushout
complement* of (*l* and *g*). One way to think of this push out is once
we&#x2019;ve found a graph (&#119970;) that matched our left-hand side, this (sub)graph
that is created by removing the nodes and edges that match except for
those &#x2019;marked&#x2019; by the gluing object (our interface). If we for some
reason remove these nodes then it is impossible to complete the pushout.
There are two conditions the double push-out requires: the
identification and dangling condition. Essentially, these two boil down
to saying that the pushout complement must contain nodes in the image of
*g* and *l*. Figure <a href="#fig:ex" data-reference-type="ref"
data-reference="fig:ex">4</a> and
<a href="#fig:rsteps" data-reference-type="ref"
data-reference="fig:rsteps">5</a> show examples of a double-pushout
diagram. In Figure <a href="#fig:ex" data-reference-type="ref"
data-reference="fig:ex">4</a>, the rewriting step that is able to
complete the double-pushout is called a *direct derivation*.

**Definition 11** (Direct derivation). *Let G and H be hypergraphs,
$r: \langle L \hookleftarrow K \xrightarrow{\text{b}} R\rangle$ a rule
and *f*&#8196;:&#8196;*L*&#8196;&#8618;&#8196;*G* an injective hypergraph morphism. The G directly
derive H by r and f, denoted *G*&#8658;<sub>*r*,&#8198;*f*</sub>*H*, if there exisit
two pushouts of the following form.*

For a rule
$p : \lozenge l \xleftarrow{l} \mathcal{D} \xrightarrow{r} \lozenge r$,
a direct derivation can be written as
$\mathcal{G} \xRightarrow{p} \mathcal{H}$. What we call here a direct
derivation is equivalent to Plump&#x2019;s *evaluation step* . Plump discusses
two other types of operations: *folding* and *tracing*. The goal of the
former is to increase the level of sharing between edges that share the
same labels and terms. The latter, tracing, is a bit more involved.

Tracing semantics

<figure id="fig:labelling">
<img alt="" src="https://raw.githubusercontent.com/innoobijr/adjointschool-24-cp/main/img/labelling.png" style="width:80.0%" />
</figure>

In term rewriting and term graph rewriting, labeling allows us to '&#769;lift"
out rewrite rules into a context where each reduction step can now track
symbols and their occurrences through multiple derivations. This
labeling can be extended to arbitrary rewrite systems with the condition
that restrictions must to placed on the labelling to ensure that
identical arguments of a redex are labelled in the same way. Tracing is
the dual of labeling. While labeling records the history of a reduction
internally, tracing or tracking does so externally. A trace is a
relation on the positions of the source and target of a rewrite rule.
The idea is that as we step through a series of derivations (apply
rewrite rules) we keep track of the terms of the left-hand and
right-hand side. When reasoning over the label via trace there are three
parts we care about as we step through the trace: terms belonging to the
pattern of the contracted redex, terms disjoint with the redex, and
terms that are arguments to the redex.

We capture the following example of tracing and labeling from as a
pushout diagram in
Fig.<a href="#fig:labelling" data-reference-type="ref"
data-reference="fig:labelling">6</a> . In Fig.
<a href="#fig:labelling" data-reference-type="ref"
data-reference="fig:labelling">6</a>, we consider the rewrite rule
*f*(*a*,&#8198;*x*)&#8196;&#8594;&#8196;*f*(*f*(*x*,&#8198;*x*),&#8198;*a*) and the reduction step
*f*(*f*(*a*,&#8198;*a*),&#8198;*a*)&#8196;&#8594;&#8196;*f*(*f*(*f*(*a*,&#8198;*a*),&#8198;*a*),&#8198;*a*). Our goal is
to trace the thee *a*&#x2019;s that show up in original term - the left-hand
side of the reduction step. In the application graph (bottom-left) of
the pushout diagram, we label each a with a different letter (to
represent out coloring).
Fig.<a href="#fig:labelling" data-reference-type="ref"
data-reference="fig:labelling">6</a> show this result of this reduction
and lifting of rewrite rules: $f(f(a_{\color{blue}{b}},a_{\color{red}{r}}),a_{\color{green}{g}}) \rightarrow f(f(f(a_{\color{red}{r}},a_{\color{red}{r}}),a),a_{\color{green}{g}})$. We can observe the following in our trace: (1) $a_{\color{blue}{b}}$ belong to the contracted redex (top-left) but has no descendents, (2) $a_{\color{green}{g}}$ is disjoint eith the redex and is copied one, and (3) $a_{\color{red}{r}}$ is the redex argument (hole) and is copied twice. Additionally, there is one more $a$ with no label. It sourced from the original term, but from the pattern
in the embedding. It has no ancestors. The occurrences of a term traced
through derivations by a label are the *descendants* and the original
term is the *ancestor*.

**Definition 12** (Descendant and ancestor ). *Let *t* be a term in a
TRS &#8475; and let *f* be a function symbol occurring in *t*. We give *f* a
mark or *label* to be able to trace it during a sequence of rewrites.
For a unique label *b*, the labeled symbol *f* can be written as
*f*<sup>*b*</sup>. Consider the rewrite step $t \xrightarrow{s} t'$
obtained by the contraction of the redex *s* in *t*. As a result of the
contraction, all occurrences of *f* in *t*&#8242; which are labelled *b* are
the *d**e**s**c**e**n**d**e**n**t**s* of the original *f* in *t*. Given
the one-to-one correspondence between sub-terms and their head symbols,
descendants of redex can be found by tracing head symbols.*

In regards to rewriting, symbols can be partiioned into two classes:
those that trace to its target and does that dont. The symbols that
leave a trace are needed. The symbols which are needed then in essence
become the context for further reductions. Tracing provides verification
that positions in the target are originated with the source or are
created dynamically by some rule applications. Tracing is necessary for
the double pushout, particularly in the creation of the pushout
complement. Given this labeling-tracing duality, asking how it can be
useful in proving confluence of graph rewriting systems is somewhat
equivalent to demonstrating that the *dangling condition* and the
*identification condition* are necessary in completing the pushout.

Overlaps in the context and critical pairs

As we mentioned previously, overlaps occur. In the term rewriting
context, to ensure local confluence we needed to show that through a
finite number of derivations, our sub-graphs with conflicting reductions
have a common reduct. In the graph rewriting context we have similar
questions: (1) what is a &#x201C;harmful" overlap? and (2) what is a sufficient
criteria for proving joinability?

**Definition 13**. *(Critical pair) Let S be a term graph and $S \rightarrow U_i$ be an evaluation step for a rewrite rule $l_i \rightarrow r_i$ and a hypergraph morphism $g_i: \lozenge l_i \rightarrow S$ for i = 1, 2. Then $U_1 \leftarrow S \rightarrow U_2$ is a critical pair if: 
-    $S = g_1(\lozenge l_1) U g_2(\lozenge l_2)$ 
-   $g_1(e_1) \in g_2(\lozenge l_2)$ or  $g_2(e_2) \in g_1(\lozenge l_1)$, where $e_i$ is the edge outgoing from $root_{\lozenge l_i}$ for i = 1, 2

Moreover, $g_1 \neq g_2$ is required for the case $(l_1 \rightarrow r_1) = (l_2 \rightarrow r_2)$.

From the Critical Pair Lemma discussed in the Plump paper , we know that
a hypergraph rewriting system is locally confluent if all its critical
pairs are *strongly joinable*. So in addition to the decision procedure
for critical pairs, we require an additional qualification for term
graph rewriting called *strong joinability*.

**Definition 14** (Joinabiility ). A critical pair, $\Gamma: U_1 \Leftarrow S \Rightarrow U_2$ is \textit{joinable} if there are derivations $U_i \Rightarrow^{*} X_i$ for i = 1, 2, and an isomorphism $f: X_1 \rightarrow X_2$. Additionally $\Gamma$ is \textit{strongly joinable} if there exists for every node ins $S$ that can can be traced through derivations the following two condition:

- tr<sub>*S*&#8196;&#8658;&#8196;*U*<sub>1</sub>&#8658;<sup>\*</sup>*X*<sub>1</sub>(*v*)</sub> and tr<sub>*S*&#8196;&#8658;&#8196;*U*<sub>2</sub>&#8658;<sup>\*</sup>*X*<sub>2</sub>(*v*)</sub>

- *f*<sub>*V*</sub>(tr<sub>*S*&#8196;&#8658;&#8196;*U*<sub>1</sub>&#8658;<sup>\*</sup>*X*<sub>1</sub>(*v*)</sub>)&#8196;=&#8196;*t**r*<sub>*S*&#8196;&#8658;&#8196;*U*<sub>2</sub>&#8658;<sup>\*</sup>*X*<sub>2</sub>(*v*)</sub>


So there you have it! As long as our definition of joinabilty ensures
traces are consistent and compatible through derivations, then for a
terminating tern graph rewriting systems, strong joinability is
sufficient for (local) confluence. So we are settled, right? Maybe for
the case of term graphs, but for arbitrary graphs, confluence is,
unfortunately, undecidable.

**Theorem 1**. It is undecidable in general whether a finite,
terminating hypergraph rewriting system is confluent. A hypergraph
rewriting system is said to be finite if *&#931;*<sub>*V*</sub>,
*&#931;*<sub>*E*</sub> and *R* are finite.

We discuss why below.

The insufficiency of strong joinability

<figure id="fig:badjoin">
    <img alt="" src="https://raw.githubusercontent.com/innoobijr/adjointschool-24-cp/main/img/badjoin.png" style="width:80.0%" />
</figure>

To explain why, we will borrow an instructive example from . In
Fig.<a href="#fig:badjoin" data-reference-type="ref"
data-reference="fig:badjoin">7</a> we consider an graph transformation
system {*&#931;*,&#8198;*R*} with three rewrite rules:
*r*<sub>1</sub>,&#8198;*r*<sub>2</sub> and *r*<sub>3</sub>. Some inspection
will show that this system is terminating: the right-hand side removes
edges from the left. We can also show that it is confluent as there are
derivations which will reduce any overlaps to a common reduct (or
specifically structurally isomorphic graphs). That is, any overlap is
*joinable*. However despite this confluence, the two critical pairs in
Figure <a href="#fig:badjoin" data-reference-type="ref"
data-reference="fig:badjoin">7</a> are not *strong joinable*. In the
first,*c**p*<sub>1</sub>, applying *r*<sub>1</sub> give us two graphs in
normal form for which the ismorphism between them is not compatible with
their traces. By labeling the nodes, we have distinguish one isomorphic
graphs. Strong joinability require compatibility with traces. As a
result, the presense of critical pairs that are joinable implies that we
can report confluence, but the lack of strong joinability for at least
one pair implies that we cannot report confluence. Which is it? It seems
like neither is sufficient. In the previous section, we mentioned that
our signature has not change. Well, what happens if it does? To keep
thing minimally destructive, lets still remain in the domain of
first-order terms. Lets add *edge labels*. As you may surmise, our
"tracing" now have over *nodes* and *edges*. In Figure
<a href="#fig:badjoin" data-reference-type="ref"
data-reference="fig:badjoin">7</a>, *c**p*<sub>2</sub> is a critical
that results from rewriting a term with an edge label. In this case our
critcal pair is still joinable, but we lose confluence because our
definition of critical pairs did not account for compatibility with edge
labels. The core idea highlighted by Plump is that relatively harmless
*signature extensions* may not preserve confluence. We may need an even
*stronger* joinability that capture compatibility between node and edge
labels across derivations. This means that adding signture extensions
that are more &#x201C;destructive" will likely break our current decision
procedure for confluence. Specifically, there are two cases where our
current decision procedure for confluence on term graphs breaks down:
*variable binding* and *higher-order logics*. The former is related to
the question posed in the
Sec.<a href="#sec:intro" data-reference-type="ref"
data-reference="sec:intro">1</a>: why cant we just apply the ideas from
to rewriting the untyped *&#955;*-calculus?  

Critical pairs for arbitrary graphs

**Variable binding and higher-order rewriting.** First, let&#x2019;s revisit
the basic term writing system {*&#931;*,&#8198;&#8475;} but with a tiny signature
extension: (*t*<sub>1</sub> *t*<sub>2</sub>) and (*&#955;**x*.*t*). The first
is **application** and represents the application of a function
*t*<sub>1</sub> to an argument *t*<sub>2</sub>. The second is
**abstraction** and represent a function with a parameter *x* in the
body of *t*. In the lambda calculus, a variable *s* in a term *t* is
**bound** by the first *&#955;* above *s*. If there is no *&#955;**x* above then
the term is **free**. For the following term *t*&#8196;:=&#8196;*&#955;**x*.*y* the
clearest way to represent this as a a term graph is a two-node graph
with the root labeled *&#955;**x* and the child node labeled *y*. It is clear
that the notion of *variable binding* is not reflect in the structure of
this graph. Instead it is represented as the *content*. What has
happened is that that simple signature extension is not so simple. In
fact, binding requires *higher-order term rewriting* which require
expanding and rethinking many of the formulation for *first-order
rewriting*. Here are some resource on higher-order equational logics and
rewriting: .

**double pushout with interfaces (DPOI).** Okay I know we said that
confluence for finite, terminating hypergraph rewrite systems was
undecidable, but there may be a way at least for string diagrams. The
work of double pushout with interfaces (DPOI) introduces a new notion of
*path joinability* that relies on lifting critical pairs into arbitrary
contexts. So in this case using DPOI and most importantly equational
reasoning based on symmetric monoidal theories, we can show that string
diagram rewriting is decidable! Our colleague will discuss this a bit in
their blog post, but our one little bit is that DPOI seems like a double
pushout with a single pullback.

Conclusion

In term and string rewriting, confluence is decidable for terminating
systems requiring finding all critical terms *s* and and checking that
all critical pairs *t* and *u* in *t*&#8196;&#8592;&#8196;*s*&#8196;&#8594;&#8196;*u* reduce to a common
term or string. In the case of terminating graph-transformation systems,
confluence is undecidable (using critical pairs as a DP) unless certain
restrictions are applied. In this setting, join-ability of critical
pairs does not need to imply the confluence of a rewriting systems. That
is, there are confluent rewriting systems where are critical pairs are
not (strongly) joinable. (Strong) joinability is not a necessary
condition for confluence of a rewriting system and can be used a a
decision procedure for general (hyper-)graph rewriting systems.

[^1]: Example of theories include propositional logic, equality, linear
    arithmetic, bit vectors. These are examples of first-order (FOL)
    theories. We can also have higher-order theories

[^2]: *In the -calculus a similar property, the Church-Rosser property -
    was proved by Alonze Church and J. Barkley Rosser*

[^3]: both relations when proper are indicated as \< and \> respectively