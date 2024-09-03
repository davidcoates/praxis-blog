---
layout: post
title:  "The Praxis Type System (Formal Specification)"
tags: praxis type-system affine-types linear-types
comments: true
---

*This post formally defines the type system introduced informally in the [previous post]({% post_url 2024-09-03-praxis-type-system %}).*
$$
\def\ref{\mathcal{\&}}
\def\view{\mathcal{?}}
\def\value{\mathcal{!}}
\newcommand{\label}[1]{\rm {\small #1}}
\newcommand{\type}[3]{A, #1 \vdash #2 \dashv #3}
$$

---
<br/>

# Kinds

In total we have introduced four new type operators:

* $$\ref{r}$$ - a reference variable
* $$\view{v}$$ - a view variable
* $$\ref{l}$$ - a reference label
* $$\value$$ - a value view

Since these are constructs at the type level, we need to consider their kinds.

The naive answer is to consider them all as having kind $$\text{Type} \rightarrow \text{Type}$$, since they are all applied to a type and the result is a type. However, this is insufficient, since in general it does not make sense to allow a type function to stand in for a reference or view. For example, $$\text{map}$$ would become:

$$\forall \: f \: v \: a \: b \mid \text{Functor} \: f. (v \: a \rightarrow b) \rightarrow v \: (f \: a) \rightarrow f \: b,$$

which is clearly not possible to implement generically for all $$v : \text{Type} \rightarrow \text{Type}$$.


Instead, references and views have their own special kinds, $$\text{Ref}$$ and $$\text{View}$$ respectively. Moreover, these kinds are assigned *syntactically*, in order to aid readability and avoid extensive ambiguity with inference. That is, $$\ref{a}$$ must have kind $$\text{Ref}$$, $$\view{a}$$ must have kind $$\text{View}$$, and $$a$$ must have some kind which is neither $$\text{Ref}$$ nor $$\text{View}$$ (e.g. $$\text{Type}$$, $$\text{Type} \rightarrow \text{Type}$$, or even $$\text{Ref} \rightarrow \text{View} \rightarrow \text{Type}$$).

This means we are abusing notation by having application (the space between types) mean different things depending on context:

* Application of a type function (e.g. $$a \: b$$) has kind $$(\kappa_1 \rightarrow \kappa_2) \rightarrow \kappa_1 \rightarrow \kappa_2$$.
* Taking a reference of a type (e.g. $$\ref{a} \: b$$) has kind $$\text{Ref} \rightarrow \text{Type} \rightarrow \text{Type}$$.
* Taking a view of a type (e.g. $$\view{a} \: b$$) has kind $$\text{View} \rightarrow \text{Type} \rightarrow \text{Type}$$.

For clarity I will use $$\star$$ for the latter two uses from here onwards.

With this in mind, we can now formally specify the kind judgement $$K \vdash \tau : \kappa$$, where $$K$$ is a kind context, $$\tau$$ is a type, and $$\kappa$$ is a kind:

$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$K \vdash \value :$ View}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$\tau : \kappa \in K$}
\UnaryInfC{$K \vdash \tau : \kappa$}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$K \vdash \sigma : \kappa_1 \rightarrow \kappa_2$}
\AxiomC{$K \vdash \tau : \kappa_1$}
\BinaryInfC{$K \vdash (\sigma \: \tau) : \kappa_2$}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$K \vdash \sigma : $ Ref}
\AxiomC{$K \vdash \tau :$ Type}
\BinaryInfC{$K \vdash (\sigma \star \tau) : $ Type}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$K \vdash \sigma :$ View}
\AxiomC{$K \vdash \tau :$ Type}
\BinaryInfC{$K \vdash (\sigma \star \tau) : $ Type}
\end{prooftree}
$$

<br/>

There is a slight problem here: references have kind $$\text{Ref}$$, but we wish to use them to instantiate both reference variables *and* view variables. This is rectified by an additional rule, which can be seen as a special case of coercive subkinding:

<br/>

$$
\begin{prooftree}
\AxiomC{$K \vdash \sigma : $ View $ \rightarrow \kappa$}
\AxiomC{$K \vdash \tau : $ Ref }
\BinaryInfC{$K \vdash (\sigma \star \tau) : \kappa$}
\end{prooftree}
$$

<br/>

# Normalisation

Recall that types are subject to *normalisation*. Let $$A \vdash C$$ mean the type constraint $$C$$ follows from the set of axioms $$A$$. Then normalisation is the reflexive transitive closure of $$\leadsto_A$$ defined below, where $$\omega$$ stands for any reference or view.

$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$(\value \star \tau) \leadsto_A \tau$}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$A \vdash$ Copy $\tau$}
\AxiomC{$\omega \neq \value$}
\BinaryInfC{$(\omega \star \tau) \leadsto_A \tau$}
\end{prooftree}
$$

<br/>

# Types

Instead of the usual typing judgement, we will use a judgement of the form:

$$\type{\Gamma}{e : \tau}{\Gamma'}$$

Here $$A$$ is a set of axioms, $$\Gamma$$ and $$\Gamma'$$ are both type contexts, $$e$$ is an expression and $$\tau$$ is a type. We think of $$\Gamma$$ as the *input* context and $$\Gamma'$$ as the *output* context, with $$\Gamma' \subseteq \Gamma$$. The idea is for the difference $$\Gamma' \setminus \Gamma$$ to be the affine variables that have been used in $$e$$, allowing us to keep track of where they are used to ensure they are not used more than once.

We can now define the core typing rules, simplified to consider only monomorphic types. Here we assume all type placeholders ($$\sigma$$, $$\tau$$, etc.) are fully normalised.

<br/>

$$
\begin{prooftree}
\AxiomC{$x : \tau \in \Gamma$}
\AxiomC{$A \nvdash$ Copy $\tau$}
\RightLabel{${\rm {\small VAR(AFFINE)}}$}
\BinaryInfC{$\type{\Gamma}{x : \tau}{\Gamma \setminus \{x\}}$}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$x : \tau \in \Gamma$}
\AxiomC{$A \vdash$ Copy $\tau$}
\RightLabel{${\rm {\small VAR(COPY)}}$}
\BinaryInfC{$\type{\Gamma}{x : \tau}{\Gamma}$}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$\type{\Gamma_1}{e_1 : \sigma}{\Gamma_2}$}
\AxiomC{$\type{\Gamma_2}{e_2 : \tau}{\Gamma_3}$}
\RightLabel{${\rm {\small PAIR}}$}
\BinaryInfC{$\type{\Gamma_1}{(e_1, e_2) : (\sigma, \tau)}{\Gamma_3}$}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$\mathbf{data} \: \tau = C_1 \: \sigma_1 \mid \cdots \mid C_n \: \sigma_n$}
\RightLabel{${\rm {\small CONS}}$}
\UnaryInfC{$\type{\Gamma}{C_i : \sigma_i \rightarrow \tau}{\Gamma}$}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$\type{\Gamma_1}{e_1 : \sigma \rightarrow \tau}{\Gamma_2}$}
\AxiomC{$\type{\Gamma_2}{e_2 : \sigma}{\Gamma_3}$}
\RightLabel{${\rm {\small APP}}$}
\BinaryInfC{$\type{\Gamma_1}{(e_1 \: e_2) : \tau}{\Gamma_3}$}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$\Gamma_{\text{Capture}} = \{ y : \rho \mid \mbox{Capture $\rho$ for $y : \rho \in \Gamma$} \}$}
\AxiomC{$\type{\Gamma_{\text{Capture}}, x : \sigma}{e : \tau}{\Gamma'}$}
\RightLabel{${\rm {\small ABS}}$}
\BinaryInfC{$\type{\Gamma}{(\lambda x : \sigma.\: e) : \sigma \rightarrow \tau}{\Gamma}$}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$\type{\Gamma_1}{e_1 : \sigma}{\Gamma_2}$}
\AxiomC{$\type{\Gamma_2, x : \sigma}{e_2 : \tau}{\Gamma_3}$}
\RightLabel{${\rm {\small LET}}$}
\BinaryInfC{$\type{\Gamma_1}{(\mathbf{let} \: x = e_1 \: \mathbf{in} \: e_2) : \tau}{\Gamma_3 \setminus \{x \}}$}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$\type{\Gamma_1, x : (\ref{l} \star \sigma)}{e : \tau}{\Gamma_2, x : (\ref{l} \star \sigma)}$}
\AxiomC{$\ref{l} \notin \tau$}
\RightLabel{${\rm {\small READ}}$}
\BinaryInfC{$\type{\Gamma_1, x : \sigma}{(\mathbf{read} \: x \: \mathbf{in} \: e) : \tau}{\Gamma_2, x : \sigma}$}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$\type{\Gamma_1}{e_1 : (\omega \star (\sigma_1, \sigma_2)) }{\Gamma_2}$}
\AxiomC{$\type{\Gamma_2, x : (\omega \star \sigma_1), y : (\omega \star \sigma_2) }{e_2 : \tau}{\Gamma_3}$}
\RightLabel{${\rm {\small UNPAIR}}$}
\BinaryInfC{$\type{\Gamma_1}{(\mathbf{let} \: (x, y) = e_1 \: \mathbf{in} \: e_2) : \tau}{\Gamma_3 \setminus \{x, y \}}$}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$\mathbf{data} \: \tau = C_1 \: \sigma_1 \mid \cdots \mid C_n \: \sigma_n$}
\AxiomC{$\type{\Gamma}{e : (\omega \star \tau)}{\Gamma'}$}
\AxiomC{$\type{\Gamma', x_1 : (\omega \star \sigma_1)}{e_1 : \rho}{\Gamma_1}$}
\noLine
\UnaryInfC{$\rlap{\dots}\phantom{\type{\Gamma', x_1 : (\omega \star \sigma_1)}{e_1 : \rho}{\Gamma_1}}$}
\noLine
\UnaryInfC{$\type{\Gamma', x_n : (\omega \star \sigma_n)}{e_n : \rho}{\Gamma_n}$}
\RightLabel{${\rm {\small CASE}}$}
\TrinaryInfC{$\type{\Gamma}{(\mathbf{case} \: e \: \mathbf{of} \: C_1 \: x_1 \rightarrow e_1 \mid \cdots \mid C_n \: x_n \rightarrow e_n) : \rho}{\bigcap_i} \Gamma_i$}
\end{prooftree}
$$

<br/>

