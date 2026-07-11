# VS40 survey, section 6 (verbatim tex excerpt, lines 1381-1609)

\section{Descriptions of restricted type}\label{sec:restricted-type}

\subsection{Families of descriptions}

In this section we consider the restricted case: the sets (considered as descriptions, or statistical hypotheses) are taken from some family $\mathcal{A}$ that is fixed in advance.\footnote{One can also consider some class of probability distributions, but we restrict our attention to sets (uniform distributions).} (Elements of $\mathcal{A}$ are finite sets of binary strings.) Informally speaking, this means that we have some \emph{a priori} information about the black box that produces a given string: this string is obtained by a random choice in one of the $\mathcal{A}$-sets, but we do not know in which one.

Before we had no restrictions (the family $\mathcal{A}$ was the family of all finite sets). It turns out that the results obtained so far can be extended (sometimes with weaker bounds) to other families that satisfy some natural conditions. Let us formulate these conditions.

(1)~The family $\mathcal{A}$ is enumerable. This means that there exists an algorithm that prints elements of $\mathcal{A}$ as lists, with some separators (saying where one element of $\mathcal{A}$ ends and another one begins).

(2)~For every $n$ the family $\mathcal{A}$ contains the set $\mathbb{B}^n$ of all $n$-bit strings.

(3)~There exists some polynomial $p$ with the following property: for every $A\in\mathcal{A}$, for every natural $n$ and for every natural $c<\#A$ the set of all $n$-bit strings in $A$ can be covered by at most $p(n)\cdot\#A/c$ sets of cardinality at most $c$ from $\mathcal{A}$.

The last condition is a replacement for splitting: in general, we cannot split a set $A\in\mathcal{A}$ into pieces from $A$, but at least we can cover a set $A\in\mathcal{A}$ by smaller elements of $\mathcal{A}$ (of size at most $c$) with polynomial overhead in the number of pieces, compared to the required minimum $\#A/c$ (more precisely, we have to cover only $n$-bit elements of $A$).

We assume that some family $\mathcal{A}$ that has properties (1)--(3) is fixed. For a string $x$ we denote by $P_x^\mathcal{A}$ the set of pairs $( i,j)$ such that $x$ has $(i*j)$-description \emph{that belongs to $\mathcal{A}$}. The set $P_x^\mathcal{A}$ is a subset of $P_x$ defined earlier; the bigger $\mathcal{A}$ is, the bigger is $P_x^\mathcal{A}$. The full set $P_x$ is $P_x^\mathcal{A}$ for the family $\mathcal{A}$ that contains all finite sets.

For every string $x$ the set $P_x^\mathcal{A}$ has properties close to the properties of $P_x$ proved earlier.

\begin{proposition}\label{prop:a-family}
For every string $x$ of length $n$ the following is true:

\begin{enumerate}
    \item\label{a1} The set $P_x^\mathcal{A}$ contains a pair that is $O(\log n)$-close to $( 0,n)$.

    \item\label{a2} The set $P_x^\mathcal{A}$ contains a pair that is $O(1)$-close to $( \KS(x),0)$.

    \item\label{a3} The adaptation of Proposition~\ref{prop:description-shift} is true: if $( i,j)\in P_x^\mathcal{A}$, then $( i+k+O(\log n),j-k)$ also belongs to $P_x^\mathcal{A}$ for every $k\le j$. (Recall that $n$ is the length of $x$.)
    %
\end{enumerate}
\end{proposition}

\begin{proof}
\ref{a1}. The property (2) guarantees that the family $\mathcal{A}$ contains the set $\mathbb{B}^n$ that is an $(O(\log n)*n)$-description of $x$.

\ref{a2}.  The property (3) applied to $c=1$ and $A=\mathbb{B}^n$ says that every singleton belongs to $A$, therefore each string has $((\KS(x)+O(1))*0)$-description.

\ref{a3}. Assume that $x$ has $(i*j)$-description $A\in\mathcal{A}$. For a given $k$ we enumerate $\mathcal{A}$ until we find a family of $p(n)2^k$ sets of size $2^{-k}\#A$ (or less) in $\mathcal{A}$ that covers all strings of length $n$ in $A$. Such a family exists due to (3), and $p$ is the polynomial from~(3). The complexity of the set that covers $x$ does not exceed $i+k+O(\log n+\log k)$, since this set is determined by $A$, $n$, $k$ and the ordinal number of the set in the cover. We may assume without loss of generality that $k\le n$, otherwise $\{x\}$ can be used as $((i+k+O(\log n))*(j-k))$-description of $x$. So the term $O(\log k)$ can be omitted.
\end{proof}

For example, we may consider the family that consists of all ``cylinders'': for every $n$ and for every string $u$ of length at most $n$ we consider the set of all $n$-bit strings that have prefix $u$.  Obviously the family of all such sets (for all $n$ and $u$) satisfies the conditions (1)--(3).

We may also fix some bits of a string (not necessarily forming a prefix).  That is, for every string $z$ in ternary alphabet $\{0,1,*\}$ we consider the set of all bit strings that can be obtained from $z$ by replacing stars with some bits. This set contains $2^k$ strings, if $u$ has $k$ stars. The conditions (1)--(3) are fulfilled for this larger family, too.

A more interesting example is the family $\mathcal{A}$ formed by all balls in Hamming sense, i.e., the sets $B_{y,r}=\{x\mid  l(x)=l(y), d(x,y)\le r\}$. Here $l(u)$ is the length of binary string $u$, and $d(x,y)$ is the Hamming distance between two strings $x$ and $y$ of the same length. The parameter $r$ is called the \emph{radius} of the ball, and $y$ is its \emph{center}. Informally speaking, this means that the experimental data were obtained by changing at most $r$ bits in some string $y$ (and all possible changes are equally probable). This assumption could be reasonable if some string $y$ is sent via an unreliable channel. Both parameters $y$ and $r$ are not known to us in advance.

It turns out that the family of Hamming balls satisfies the conditions (1)--(3). This is not completely obvious. For example, these conditions imply that for every $n$ and for every $r\le n$ the set $\mathbb{B}^n$ of $n$-bit strings can be covered by $\poly(n)2^n/V$ Hamming balls of radius $r$, where $V$ stands for the cardinality of such a ball (i.e., $V=\binom{n}{0}+\ldots+\binom{n}{r}$), and $p$ is some polynomial. This can be shown by a probabilistic argument: take $N$ balls of radius $r$ whose centers are randomly chosen in $\mathbb{B}^n$. For a given $x\in\mathbb{B}^n$ the probability that $x$ is not covered by any of these balls equals $(1-V/2^n)^N < e^{-VN/2^n}$. For $N=n\ln 2\cdot 2^n/V$ this upper bound is $2^{-n}$, so for this $N$ the probability to leave some $x$ uncovered is less than~$1$. A similar argument can be used to prove (1)--(3) in the general case.

\begin{proposition}[\cite{vv10}]\label{prop:hamming-balls}
The family of all Hamming balls satisfies conditions (1)--(3) above.
\end{proposition}

\begin{proof}[Proof sketch]
Let $A$ be a ball of radius $a$ and let $c$ be a number less than $\#A$. We need to cover $A$ by balls of cardinality $c$ or less, using almost minimal number of balls, close to the lower bound $\#A/c$ up to a polynomial factor. Let us make some observations.

(1)~The set of all $n$-bit strings can be covered by two balls of radius $n/2$. So we can assume without loss of generality that $a\le n/2$, otherwise we can apply the probabilistic argument above.

(2)~Clearly the radius of covering balls should be maximal possible (to keep cardinality less than $c$); for this radius the cardinality of the ball equals $c$ up to polynomial factors, since the size of the ball increases at most by factor $n+1$ when its radius increases by $1$.

(3)~It is enough to cover spheres instead of balls (since every ball is a union of polynomially many spheres); it is also enough to consider the case when the radius of the sphere that we want to cover ($a$) is bigger than the radius of the covering ball ($b$), otherwise one ball is enough.

(4)~We will cover $a$-sphere by randomly chosen $b$-balls whose centers are uniformly taken at some distance $f$ from the center of $a$-sphere. (See below about the choice of $f$.) We use the same probabilistic argument as before (for the set of all strings). It is enough to show that for a $b$-ball whose center is at that distance, the polynomial fraction of points belong to $a$-sphere. Instead of $b$-balls we may consider $b$-spheres, the cardinality ratio is polynomial.

(5)~It remains to choose some $f$ with the following property:  if the center of a $b$-sphere $S$ is at a distance $f$ from the center of $a$-sphere $T$, then the polynomial fraction of $S$-points  belong to $T$. One can compute a suitable $f$ explicitly. In probabilistic terms we just change $f/n$-fraction of bits and then change random $b/n$ fraction of bits. The expected fraction of twice changed bits is, therefore, about $(f/n)(b/n)$, and the total fraction of changed bits is about $f/n+b/n-2(f/n)(b/n)$. So we need to write an equation saying that this expression is $a/n$ and the find the solution $f$. (Then one can perform the required estimate for binomial coefficients.)

However, one can avoid computations with the following probabilistic argument: start with $b$ changed bits, and then change all the bits one by one in a random order. At the end we hat $n-b$ changed bits, and $a$ is somewhere in between, so there is a moment where the number of changed bits is exactly $a$. And if the union of $n$ events covers the entire probability space, one of these events has probability at least $1/n$.
\end{proof}

When a family $\mathcal{A}$ is fixed, a natural question arises: does the restriction on models (when we consider only models in $\mathcal{A}$) changes the set $P_x$? Is it possible that a string has good models in general, but not in the restricted class? The answer is positive for the class of Hamming balls, as the following proposition shows.

\begin{proposition}\label{prop:hamming-gap}
Consider the family $\mathcal{A}$ that consists of all Hamming balls. For some positive $\varepsilon$ and for all sufficiently large $n$ there exists a string $x$ of length $n$ such that the distance between $P_x^\mathcal{A}$ and $P_x$ exceeds $\varepsilon n$.
\end{proposition}

\begin{proof}[Proof sketch]
Fix some $\alpha$ in $(0,1/2)$ and let $V$ be the cardinality of the Hamming ball of radius $\alpha n$. Find a set $E$ of cardinality $N=2^n/V$ such that every Hamming ball of radius $\alpha n$ contains at most $n$ points from $E$. This property is related to \emph{list decoding} in the coding theory. The existence of such a set can be proved by a probabilistic argument: $N$ randomly chosen $n$-bit strings have this property with positive probability. Indeed, the probability of a random point to be in $E$ is an inverse of the number of points, so the distribution is close to Poisson distribution with parameter~$1$, and tails decrease much faster that $2^{-n}$ needed.

Since $E$ with this property can be found by an exhaustive search, we can assume that $\KS(E)=O(\log n)$ and ignore the complexity of $E$ (as well as other $O(\log n)$ terms) in the sequel. Let $x$ be a random element in $E$, i.e., a string $x\in E$ of complexity about $\log\#E$.  The complexity of a ball $A$ of radius $\alpha n$ that contains $x$ is at least $\KS(x)$, since knowing such a ball and an ordinal number of $x$ in $A\cap E$, we can find $x$. Therefore $x$ does not have $(\log\#E,\log V)$-descriptions in $\mathcal A$. On the other hand, $x$ does have $(0,\log\#E)$-description if we do not require the description to be in $\mathcal A$; the set $E$ is such a description. The point $(\log\#E, \log V)$ is above the line $\KS(A)+\log\#A=\log\#E$, so $P_x^\mathcal A$ is significantly smaller than $P_x$.
\end{proof}

This construction gives a stochastic $x$ ($E$ is the corresponding model) that becomes maximally non-stochastic if we restrict ourselves to Hamming balls as descriptions (Figure~\ref{mdl-e-13}).

\begin{figure}
\begin{center}
\includegraphics[scale=1]{mdl-e-13.pdf}
\end{center}
\caption{Theorem~\ref{thm:improving-descriptions-1-gen} can be used (together with the argument above) to show that the border of the set $P_x^\mathcal{A}$ (shown in gray) consists of a vertical segment $\KS(A)=n-\log V$, $\log\#A\le \log V$, and the segment of slope $-1$ defined by $\KS(A)+\log\#A = n$, $\log V \le \log\#A$. The set $P_x$ contains also the hatched part.}\label{mdl-e-13}
\end{figure}

\subsection{Possible shapes of boundary curve}

Our next goal is to extend some results proven for non-restricted descriptions to the restricted case. Let $\mathcal{A}$ be a family that has properties (1)--(3). We prove a version of Theorem~\ref{stat-any-curve} where the precision (unfortunately) is significantly worse: $O(\sqrt{n\log n})$ instead of $O(\log n)$. Note that with this precision the term $O(m)$ (proportional to the complexity of the curve) that appeared in Theorem~\ref{stat-any-curve} is not needed. Indeed, if we draw the curve on the cell paper with cell size $\sqrt{n}$ or larger, then it touches only $O(\sqrt{n})$ cells, so it is determined by $O(\sqrt{n})$ bits with $O(\sqrt{n})$-precision, and we may assume without loss of generality that the complexity of the curve is $O(\sqrt{n})$.

\begin{thm}[\cite{vv10}]\label{thm:family-curve}
Let $k\le n$ be two integers and let $t_0>t_1>\ldots>t_k$ be a strictly decreasing sequence of integers such that $t_0\le n$ and $t_k=0$.. Then there exists a string $x$ of complexity $k+O(\sqrt{n\log n})$ and length $n+O(\log n)$ for which the distance between $P_x^\mathcal{A}$ and $T=\{( i,j) \mid (i\le k)\Rightarrow (j\ge t_i)\}$ is at most $O(\sqrt{n\log n})$.
\end{thm}

We will see later (Theorem~\ref{thm:improving-descriptions-1-gen}) that for every $x$ the boundary curve of $P_x^{\mathcal{A}}$ goes down at least with slope $-1$, as for the unrestricted case, so this theorem describes all possible shapes of the boundary curve.

\begin{proof}
     %
The proof is similar to the proof of Theorem~\ref{stat-any-curve}. Let us recall this proof first. We consider the string $x$ that is the lexicographically first string (of suitable length $n'$) that is not covered by any ``bad'' set, i.e., by any set of complexity at most $i$ and size at most $2^j$, where the pair $(i,j)$ is at the boundary of the set $T$. The length $n'$ is chosen in such a way that the total number of strings in all bad sets is strictly less than $2^{n'}$. On the other hand, we need ``good sets'' that cover $x$. For every boundary point $(i,j)$ we construct a set $A_{i,j}$ that contains $x$, has complexity close to $i$ and size $2^j$. The set $A_{i,j}$ is constructed in several attempts. Initially $A_{i,j}$ is the set of lexicographically first $2^j$ strings of length $n'$. Then we enumerate bad sets and delete all their elements from $A_{i,j}$. At some step $A_{i,j}$ may become empty; then we refill it with $2^j$ lexicographically first strings that are not in the bad sets (at the moment). By construction the final $A_{i,j}$ contains the first $x$ that is not in bad sets (since it is the case all the time). And the set $A_{i,j}$ can be described by the number of changes (plus some small information describing the process as a whole and the value of $j$). So it is crucial to have an upper bound for the number of changes. How do we get this bound? We note that when $A_{i,j}$ becomes empty, it is refilled again, and all the new elements should be covered by bad sets before the new change could happen. Two types of bad sets may appear: ``small'' ones (of size less than $2^j$) and ``large ones'' (of size at least $2^j$). The slope of the boundary line for $T$ guarantees that the total number of elements in all small bad sets does not exceed $2^{i+j}$ (up to a $\poly(n)$-factor), so they may make $A_{i,j}$ empty only $2^i$ times. And the number of large bad sets is $O(2^i)$, since the complexity of each is bounded by $i$. (More precisely, we count separately the number of changes for $A_{i,j}$ that are first changes after a large bad set appears, and the number of other changes.)

Can we use the same argument in our new situation? We can generate bad sets as before and have the same bounds for their sizes and the total number of their elements. So the length $n'$ of $x$ can be the same (in fact, almost the same, as we will need now  that the union of all bad sets is less than half of all strings of length $n'$, see below).  Note that we now may enumerate only bad sets in $\mathcal{A}$, since $\mathcal{A}$ is enumerable, but we do not even need this restriction. What we cannot do is to let $A_{i,j}$ to be the set of the first non-deleted elements: we need $A_{i,j}$ to be a set from $\mathcal{A}$.

So we now go in the other direction. Instead of choosing $x$ first and then finding suitable ``good'' $A_{i,j}$ that contain $x$, we construct the sets $A_{i,j}\in\mathcal{A}$ that change in time in such a way  that (1)~their intersection always contains some non-deleted element (an element that is not yet covered by bad sets); (2) each $A_{i,j}$ has not too many versions. The non-deleted element in their intersection (in the final state) is then chosen as $x$.

Unfortunately, we cannot do this for all points $(i,j)$ along the boundary curve. (This explains the loss of precision in the statement of the theorem.) Instead, we construct ``good'' sets only for some values of $j$. These values go down from $n$ to $0$ with step $\sqrt{n\log n}$. We select $N=\sqrt{n/\log n}$ points $(i_1,j_1),\ldots,(i_N,j_N)$ on the boundary of $T$; the first coordinates $i_1,\ldots,i_N$ form a non-decreasing sequence, and the second coordinates $j_1,\ldots,j_N$ split the range $n\ldots 0$ into (almost) equal intervals ($j_1=n$, $j_N=0$). Then we construct good sets of sizes at most $2^{j_1},\ldots,2^{j_N}$, and denote them by $A_1,\ldots,A_N$. All these sets belong to the family $\mathcal{A}$. We also let $A_0$ to be the set of all strings of length $n'=n+O(\log n)$; the choice of the constant in $O(\log n)$ will be discussed later.

Let us first describe the construction of $A_1,\ldots,A_N$ assuming that the set of deleted elements is fixed. (Then we discuss what to do when more elements are deleted.) We construct $A'$ inductively (first $A_1$, then $A_2$ etc.). As we have said, $\#A'\le 2^{j_s}$ (in particular, $A_N$ is a singleton), and we keep track of the ratio
   $$(\text{the number of non-deleted strings in $A_0\cap A_1\cap\ldots\cap A'$})/2^{j_s}.$$
For $s=0$ this ratio is at least $1/2$; this is obtained by a suitable choice of $n'$ (the union of all bad sets should cover at most half of all $n'$-bit strings). When constructing the next $A'$, we ensure that this ratio decreases only by $\poly(n)$-factor. How? Assume that $A_{s-1}$ is already constructed; its size is at most $2^{j_{s-1}}$. The condition $(3)$ for $\mathcal{A}$ guarantees that $A_{s-1}$ can be covered by $\mathcal{A}$-sets of size at most $2^{j_s}$, and we need about $2^{j_{s-1}-j_s}$ covering sets (up to $\poly(n)$-factor). Now we let $A'$ be the covering set that contains maximal number of non-deleted elements in $A_0\cap\ldots\cap A_{s-1}$. The ratio can decrease only by the same $\poly(n)$-factor. In this way we get
  $$(\text{the number of non-deleted strings in $A_0\cap A_1\cap\ldots\cap A'$})\ge \alpha^{-s}2^{j_s}/2,$$
where $\alpha$ stands for the $\poly(n)$-factor mentioned above.\footnote{Note that for the values of $s$ close to $N$ the right-hand side can be less than $1$; the inequality then claims just the existence of non-deleted elements. The induction step is still possible: non-deleted element is contained in one of the covering sets.}

Up to now we assumed that the set of deleted elements is fixed. What happens when more strings are deleted? The number of the non-deleted in $A_0\cap\ldots\cap A_{s}$ can decrease, and at some point and for some $s$ can become less than the declared threshold $\nu_s=\alpha^{-s} 2^{j_s}/2$. Then we can find minimal $s$ where this happens, and rebuild all the sets $A',A_{s+1},\ldots$ (for $A'$ the threshold is not crossed due to the minimality of $s$). In this way we update the sets $A'$ from time to time, replacing them (and all the consequent ones) by new versions when needed.

The problem with this construction is that the number of updates (different versions of each $A'$) can be too big. Imagine that after an update some element is deleted, and the threshold is crossed again. Then a new update is necessary, and after this update next deletion can trigger a new update, etc. To keep the number of updates reasonable, we agree that after the update \emph{for all the new sets $A_l$} (starting from $A'$) \emph{the number of non-deleted elements in $A_0\cap\ldots\cap A_l$ is twice bigger than the threshold $\nu_l=\alpha^{-l}2^{j_l}/2$}. This can be achieved if we make the factor $\alpha$ twice bigger: since for $A_{s-1}$ we have not crossed the threshold, for $A'$ we can guarantee the inequality with additional factor $2$.

Now let us prove the bound for the number of updates for some $A'$. These updates can be of two types: first, when $A'$ itself starts the update (being the minimal $s$ where the threshold is crossed); second, when the update is induced by one of the previous sets. Let us estimate the number of the updates of the first type. This update happens when the number of non-deleted elements (that was at least $2\nu_s$ immediately after the previous update of any kind) becomes less than $\nu_s$. This means that at least $\nu_s$ elements were deleted. How can this happen? One possibility is that a new bad set of complexity at most $i_s$ (``large bad set'') appears after the last update. This can happen at most $O(2^{i_s})$ times, since there is at most $O(2^i)$ objects of complexity at most $i$. The other possibility is the accumulation of elements deleted due to ``small'' bad sets, of complexity at least $i_s$ and of size at most $2^{j_s}$. The total number of such elements is bounded by $nO(2^{i_s+j_s})$, since the sum $i_l+j_l$ may only decrease as $l$, increases. So the number of updates of $A'$ not caused by large bad sets is bounded by
      $$ n O(2^{i_s+j_s}) /\nu_s  =\frac{O(n2^{i_s+j_s})}{\alpha^{-s}2^{j_s}} = O(n\alpha^s 2^{i_s})=2^{i_s+NO(\log n)}=2^{i_s+O(\sqrt{n\log n})}$$
(recall that $s\le N$, $\alpha=\poly(n)$, and $N\approx \sqrt{n/\log n}$). This bound remains valid if we take into account the induced updates (when the threshold is crossed for the preceding sets: there are at most $N\le n$ these sets, and additional factor $n$ is absorbed by $O$-notation).

We conclude that all the versions of $A'$ have complexity at most $i_s+O(\sqrt{n\log n})$, since each of them can be described by the version number plus the parameters of the generating process (we need to know $n$ and the boundary curve, whose complexity is $O(\sqrt{n})$ according to our assumption, see the discussion before the statement of the theorem). The same is true for the final version. It remains to take $x$ in the intersection of the final sets $A'$. (Recall that $A_N$ is  a singleton, so final $A_N$ is $\{x\}$.) Indeed, by construction this $x$ has no bad $(i*j)$-descriptions where $(i,j)$ is on the boundary of $T$. On the other hand, $x$ has good descriptions that are $O(\sqrt{n\log n})$-close to this boundary and whose vertical coordinates are $\sqrt{n\log n}$-apart. (Recall that the slope of the boundary guarantees that horizontal distance is less than the vertical distance.) Therefore the position of the boundary curve for $P_x^\mathcal{A}$ is determined with precision $O(\sqrt{n\log n})$, as required.\footnote{Now we see why $N$ was chosen to be $\sqrt{n/\log n}$: the bigger $N$ is, the more points on the curve we have, but then the number of versions of the good sets and their complexity increases, so we have some trade-off. The chosen value of $n$ balances these two sources of errors.}
      %
 \end{proof}

\begin{remark}\label{rem:family}
In this proof we may use bad sets not only from $\mathcal{A}$. Therefore, the set $P_x$ is also close to $T$ (and the same is true for for every family $\mathcal{B}$ that contains $\mathcal{A}$). It would be interesting to find out what are the possible combinations of $P_x$ and $P_x^\mathcal{A}$; as we have seen, it may happen that $P_x$ is maximal and $P_x^\mathcal{A}$ is minimal, but this does not say anything about other possible combinations.  \end{remark}

For the case of Hamming balls the statement of Theorem~\ref{thm:family-curve} has a natural interpretation. To find a simple ball of radius $r$ that contains a given string $x$ is the same as to find a simple string in a radius $r$ ball centered at $x$. So this theorem show the possible behavior of the ``approximation complexity'' function
$$
 r\mapsto \min \{\KS(x')\mid d(x,x')\le r\}
$$
where $d$ is Hamming distance. One should only rescale the vertical axis replacing the log-sizes of Hamming balls by their radii. The connection is described by the Shannon entropy function: a ball in $\mathbb{B}^n$ of radius $r$ has log-size about $nH(r/n)$ for $r\le n/2$, and has almost full size for $r\ge n/2$. For example, error correcting codes (in classical sense, or with list decoding) are example of strings where this function is almost a constant for small values of $r$: it is almost as easy to approximate a codeword as give it precisely (due to the possibility of error correction).

\subsection{Randomness and optimality deficiencies: restricted case}

Not all the results proved for unrestricted descriptions have natural counterparts in the restricted case. For example, one hardly can relate the set $P_x^\mathcal{A}$ with bounded-time complexity (is completely unclear how $\mathcal{A}$ could enter the picture). Still some results remain valid (but new and much more complicated proofs are needed). This is the case for Proposition~\ref{prop:description-shift} and~\ref{prop:improving-descriptions}.

Let again $\mathcal{A}$ be the class of descriptions that satisfies requirements (1)--(3).

\begin{thm}[\cite{vv10}]\label{thm:improving-descriptions-1-gen}
\leavevmode
\begin{itemize}
\item If a string $x$ of length $n$ has an $(i*j)$-description in $\mathcal{A}$, then it has $((i+d+O(\log n))*(j-d+O(\log n)))$-description in $\mathcal{A}$ for every $d\le j$.

\item Assume that $x$ is a string of length $n$ that has at least $2^k$ different $(i*j)$-descriptions in $\mathcal{A}$. Then it has $((i-k+O(\log n))*(j+O(\log n))$-description in $\mathcal{A}$.
\end{itemize}
\end{thm}

In fact, the second part uses only condition (1); it says that $\mathcal{A}$ is enumerable. The first part uses also (3). It can be combined with the second part to show that $x$ has also $((i+O(\log n))*(j-k+O(\log n))$-description in $\mathcal{A}$.
\smallskip

Though theorem \ref{thm:improving-descriptions-1-gen} looks like a technical statement, it has important consequences; it implies that the two approaches based on randomness and optimality deficiencies remain equivalent in the case of bounded class of descriptions. The proof technique can be also used to prove Epstein--Levin theorem~\cite{epstein-levin}, as explained in~\cite{shen-survey}; similar technique was used by A.~Milovanov in \cite{milovanov-stacs} where a common model for several strings is considered.

\begin{proof}
The first part is easy: having some $(i*j)$-description for $x$, we can search for a covering by the sets of right size that exists due to condition~(3); since $\mathcal{A}$ is enumerable, we can do it algorithmically until we find this covering. Then we select the first set in the covering that contains $x$; the bound for the complexity of this set is guaranteed by the size of the covering.

The proof of the second statement is much more interesting. In fact, there are two different proofs: one uses a probabilistic existence argument and the second is more explicit. But both of them start in the same way.

Let us enumerate all $(i*j)$-descriptions from $\mathcal A$, i.e., all finite sets that belong to $\mathcal A$, have cardinality at most $2^j$ and complexity at most $i$. For a fixed $n$, we start a selection process: some of the generated descriptions are marked (=selected) immediately after their generation. This process should satisfy the following requirements: (1)~at any moment every $n$-bit string $x$ that has at least $2^k$ descriptions (among enumerated ones) belongs to one of the marked descriptions; (2)~the total number of marked sets does not exceed $2^{i-k}p(n)$ for some polynomial~$p$. Note that for $i\ge n$ or $j\ge n$ the statement is trivial, so we may assume that $i$, $j$ (and therefore $k$) do not exceed $n$; this explains why the polynomial depends only on $n$.

If we have such a strategy (of logarithmic complexity), then the marked set containing $x$ will be the required description of complexity $i-k+O(\log n)$ and log-size $j$. Indeed, this marked set can be specified by its ordinal number in the list of marked sets, and this ordinal number has $i-k+O(\log n)$ bits.

So we need to construct a selection strategy of logarithmic complexity. We present two proofs: a probabilistic one and an explicit construction.

\textsc{Probabilistic proof}. First we consider a finite game that corresponds to our situation. Two players alternate, each makes $2^i$ moves. At each move the first player presents some set of $n$-bit strings, and the second player replies saying whether it \emph{marks} this set or not. The second player loses if after some moves the number of marked sets exceeds $2^{i-k+1}(n+1)\ln 2$ (this specific value follows from the argument below) or if there exists a string $x$ that belongs to $2^k$ sets of the first player but does not belong to any marked set.

Since this is a finite game with full information, one of the players has a winning strategy. We claim that the second player can win. If it is not the case, the first player has a winning strategy. We get a contradiction by showing that the second player has a \emph{probabilistic} strategy that wins with positive probability against any strategy of the first player. So we assume that some (deterministic) strategy of the first player is fixed, and consider the following simple probabilistic  strategy: every set $A$ presented by the first player is marked with probability $p=2^{-k}(n+1)\ln 2$.

The expected number of marked sets is $p2^i=2^{i-k}(n+1)\ln 2$. By Chebyshev's inequality, the number of marked set exceeds the expectation by a factor $2$ with probability less than $1/2$. So it is enough to show that the second bad case (after some move there exists $x$ that belongs to $2^k$ sets of the first player but does not belong to any marked set) happens with probability at most $1/2$.

For that, it is enough to show that for every fixed $x$ the probability of this bad event is at most $2^{-(n+1)}$, and then use the union bound.  The intuitive explanation is simple: if $x$ belongs to $2^k$ sets, the second player had (at least) $2^k$ chances to mark a set containing $x$ (when these $2^k$ sets were presented by the first player), and the probability to miss all these chances is at most $(1-p)^{2^k}$; the choice of $p$ guarantees that this probability is less than $1/2^{-(n+1)}$. Indeed, using the bound $(1-1/x)^x < 1/e$, it is easy to show that $(1-p)^{2^k} < e^{-(n+1)\ln 2}=2^{-(n+1)}$.

The pedantic reader would say that this argument is not formally correct, since the behavior of the first player (and the moment when next set containing $x$ is produced) depends on the moves of the second player, so we do not have independent events with probability $1-p$ each (as it is assumed in the computation).\footnote{The same problem appears if we observe a sequence of  independent coin tossings with probability of success $p$, select some trials (before they are actually performed, based on the information obtained so far), and ask for the probability of the event ``$t$ first selected trials were all unsuccessful''. This probability does not exceed $(1-p)^t$; it can be smaller if the total number of selected trials is less than $t$ with positive probability. This scheme was considered by von Mises when he defined random sequences using selection rules, so it should be familiar to algorithmic randomness people.}  The formal argument considers for each $t$ the event $R_t$: ``after some move of the second player the string $x$ belongs to at least $t$ sets provided by the first player, but does not belong to any marked set''. Then we prove by induction (over $t$) that the probability of $R_t$ does not exceed $(1-p)^t$. Indeed, it is easy to see that $R_t$ in a union of several disjoint subsets (depending on the events happening until the first player provides $t+1$ sets containing $x$), and $R_{t+1}$ is obtained by taking a $(1-p)$-fraction in each of them.

\textsc{Constructive proof}. We consider the same game, but now allow more sets to be marked (replacing the bound $2^{i-k+1}(n+1)\ln 2$ by a bigger bound $2^{i-k}i^2\ln 2$) and also allow the second player to mark sets that were produced earlier (not necessarily at the current move of the first player). The explicit winning strategy for the second player performs in parallel $i-k+\log i$ substrategies (indexed by the numbers $\log (2^k/i),\ldots,i$).

The substrategy number $s$ wakes up once in $2^s$ moves (when the number of moves made by the first player is a multiple of $2^s$).  It considers a family $S$ that consists of $2^s$ last sets produced by the first player, and the set $T$ that consists of all strings $x$ covered by at least $2^k/i$ sets from $S$. Then it selects and marks some elements in $S$ in such a way that all $x\in T$ are covered by one of the selected sets. It is done by a greedy algorithm: first take a set from $S$ that covers maximal part of $T$, then the set that covers maximal number of non-covered elements, etc. How many steps do we need to cover the entire $T$? Let us show that
    $$ (i/2^k)n 2^{s} \ln 2 $$
steps are enough. Indeed, every element of $T$ is covered by at least $2^k/i$ sets from $S$. Therefore, some set from $S$ covers at least $\#T2^k/(i2^s)$ elements, i.e., $2^{k-s}/i$-fraction of $T$. At the next step the non-covered part is multiplied by $(1-2^{k-s}/i)$ again, and after $in2^{s-k}\ln 2$ steps the number of non-covered elements is bounded by
    $$ \#T (1-2^{k-s}/i)^{in2^{s-k}\ln 2} < 2^n (1/e)^{n\ln 2} = 1,$$
therefore all elements of $T$ are covered. (Instead of a greedy algorithm one may use a probabilistic argument and show that randomly chosen $in2^{s-k}\ln 2$ sets from $S$ cover $T$ with positive probability; however, our goal is to construct an explicit strategy.)

Anyway, the number of sets selected by a substrategy number $s$, does not exceed
     $$ in2^{s-k}(\ln 2)2^{i-s} = in2^{i-k}\ln 2, $$
and we get at most $i^2 n 2^{i-k} \ln 2$ for all substrategies.

It remains to prove that after each move of the second player every string $x$ that belongs to $2^k$ or more sets of the first player, also belongs to some selected set. For $t$th move we consider the binary representation of $t$:
   $$t=2^{s_1}+2^{s_2}+\ldots, \text{ where } s_1>s_2>\ldots $$
Since $x$ does not belong to the sets selected by substrategies with numbers $s_1,s_2,\ldots$, the multiplicity of $x$ among the first $2^{s_1}$ sets is less than $2^k/i$, the multiplicity of $x$ among the next $2^{s_2}$ sets is also less than $2^k/i$, etc. For those $j$ with $2^{s_j}<2^k/i$ the multiplicity of $x$ among the respective portion of $2^{s_j}$ sets is obviously less than $2^k/i$. Therefore, we conclude that the total multiplicity of $x$ is less that $i\cdot 2^k/i=2^k$ sets of the first player and the second player does not need to care about~$x$. This finishes the explicit construction of the winning strategy.

Now we can assume without loss of generality that the winning strategy has complexity at most $O(\log(n+k+i+j))$. (In the probabilistic argument we have proved the existence of a winning strategy, but then we can perform the exhaustive search until we find one; the first strategy found will have small complexity.) Then we use this simple strategy to play with the enumeration of all $\mathcal{A}$-sets of complexity less than $i$ and size $2^j$ (or less). The selected sets can be described by their ordinal number (among the selected sets), so their complexity is bounded by $i-k$ (with logarithmic precision). Every string that has $2^k$ different $(i*j)$-descriptions in $\mathcal{A}$, will also have one among the selected sets, and that is what we need.
    %
\end{proof}

As before (for the unrestricted case), this result implies that descriptions with minimal parameters are simple with respect to the data string:
     %
\begin{thm}[\cite{vv10}]\label{thm:improving-descriptions-2-gen}
Let $\mathcal A$ be an enumerable family of finite sets. If a string $x$ of length $n$ has $(i*j)$-description $A\in\mathcal{A}$ such that $\KS(A\cnd x)\ge k$, then $x$ has a $((i-k+O(\log n))*(j+O(\log n)))$-description in $\mathcal{A}$. If the family $\mathcal{A}$ satisfies the condition $(3)$, then $x$ has also a $((i+O(\log n))*(j-k+O(\log n)))$-description in~$\mathcal{A}$.
\end{thm}

This gives us the same corollaries as in the unrestricted case:

\begin{corollary}
Let $\mathcal{A}$ be a family of finite sets that satisfies the conditions (1)--(3). Then for every string $x$ of length $n$ three statements
\begin{itemize}
\item there exists a set $A\in\mathcal{A}$ of complexity at most $\alpha$ with $d(x\cnd A)\le\beta$;
\item there exists a set $A\in\mathcal{A}$ of complexity at most $\alpha$ with $\delta(x,A)\le\beta$;
\item the point $(\alpha,\KS(x)-\alpha+\beta)$ belongs to $P_x^\mathcal{A}$
\end{itemize}
are equivalent with logarithmic precision (the constants before the logarithms depend on the choice of the set $\mathcal{A}$).
\end{corollary}

If we are interested in the uniform statements true for every enumerable family $\mathcal{A}$, the same arguments prove the following result:

\begin{proposition}
Let $\mathcal{A}$ be an arbitrary family of finite sets enumerated by some program $p$. Then for every $x$ of length $n$ the statements
\begin{itemize}
\item there exists a set $A\in\mathcal{A}$ such that $d(x\cnd A)\le \beta$;
\item there exists a set $A\in\mathcal{A}$ such that $\delta(x,A)\le\beta$
\end{itemize}
are equivalent up to $O(\KS(p)+\log\KS(A)+\log n+\log\log\#A)$-change in the parameters.
\end{proposition}

\ver{
\section{Strong models}\label{sec:strong-models}
