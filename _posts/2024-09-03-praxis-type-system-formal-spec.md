---
layout: post
title:  "The Praxis Type System (Formal Specification)"
tags: praxis type-system affine-types linear-types
comments: true
---

*This post formally defines the type system [introduced informally in the this post]({% post_url 2024-09-03-praxis-type-system %}).*
$$
\def\ref{\mathcal{\&}}
\def\view{\mathcal{?}}
\def\identity{\mathcal{@}}
\def\value{\mathcal{!}}
\newcommand{\label}[1]{\rm {\small #1}}
\newcommand{\type}[3]{A, #1 \vdash #2 \dashv #3}
$$

---
<br/>

# Type Operators

Type operators are defined as any of the following:
* the identity view $$\identity$$,
* a reference label $$\ref{l}$$,
* a reference variable $$\ref{r}$$,
* a view variable $$\view{v}$$,
* a set of any combination of the above.

The application of a type operator, which I'll denote using $$\star$$, is a construct distinct from (regular) type application.

In addition, the type system supports *value variables*, denoted $$\value{a}$$, which can only unify with types that do not have a top-level type operator application.

# Normalisation

Types are subject to *normalisation*. Let $$A \vdash C$$ mean the type constraint $$C$$ follows from the set of axioms $$A$$. Then normalisation is the reflexive transitive closure of $$\leadsto_A$$ defined below:

<br/>

$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$(\identity \star \tau) \leadsto_A \tau$}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$A \vdash$ Copy $\tau$}
\UnaryInfC{$(\omega \star \tau) \leadsto_A \tau$}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$ \omega_1 \star (\omega_2 \star \tau) \leadsto_A \{ \omega_1, \omega_2 \} \star \tau $}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\{ \} \leadsto_A \identity $}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$ \identity \in \{ \omega_1, \dots, \omega_n \} $}
\UnaryInfC{$\{ \omega_1, \dots, \omega_n \} \leadsto_A \{ \omega_1, \dots, \omega_n \} \setminus \{ \identity \} $}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$\omega_i = \{ \psi_1, \dots, \psi_m \} $}
\UnaryInfC{$\{ \omega_1, \dots, \omega_n \} \leadsto_A \{ \omega_1 \dots \omega_{i-1}, \psi_1, \dots, \psi_m, \omega_{i+1}, \dots, \omega_n \} $}
\end{prooftree}
$$

<br/>



# Kinds

We can now formally specify the kind judgement $$K \vdash \tau : \kappa$$, where $$K$$ is a kind context, $$\tau$$ is a type, and $$\kappa$$ is a kind. Here all types are taken as fully normalized.

<br/>

$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$K \vdash \identity :$ View}
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
\AxiomC{$K \vdash \omega_1 : \text{Ref}$}
\noLine
\UnaryInfC{$\rlap{\dots}\phantom{K \vdash \omega_n : \text{Ref}}$}
\noLine
\UnaryInfC{$K \vdash \omega_n : \text{Ref}$}
\AxiomC{$|\{ \omega_1, \dots, \omega_n \}| \geq 2$}
\BinaryInfC{$K \vdash \{ \omega_1, \dots, \omega_n \} : \text{Ref} $}
\end{prooftree}
$$

<br/>

$$
\begin{prooftree}
\AxiomC{$K \vdash \omega_1 : \kappa_1$}
\noLine
\UnaryInfC{$\rlap{\dots}\phantom{K \vdash \omega_n : \kappa_n}$}
\noLine
\UnaryInfC{$K \vdash \omega_n : \kappa_n$}
\AxiomC{$\{ \kappa_1, \dots, \kappa_n \} \subseteq \{ \text{Ref}, \text{View} \} $}
\AxiomC{$\{ \kappa_1, \dots, \kappa_n \} \neq \{ \text{Ref} \} $}
\AxiomC{$|\{ \omega_1, \dots, \omega_n \}| \geq 2$}
\QuaternaryInfC{$K \vdash \{ \omega_1, \dots, \omega_n \} : \text{View} $}
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

