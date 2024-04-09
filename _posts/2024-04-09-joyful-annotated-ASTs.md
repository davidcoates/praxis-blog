---
layout: post
title:  "Joyful Annotated ASTs"
tags: praxis-compiler haskell
comments: true
---

*This post is a deep dive into the Abstract Syntax Tree (AST) representation used by the Praxis compiler. This includes a novel Haskell technique, that I have called introspection, which provides a way to easily manipulate mutually recursive structures in ways which would otherwise be extremely cumbersome. It assumes familiarity with Haskell, including Functor, Applicative, and Traversable typeclasses.*

---
<br/>

# The Praxis AST
Let's dive straight in to a trimmed-down version of the AST representation used by the Praxis compiler:

{% highlight haskell %}
type Name = String

data Bind = Bind (Annotated Pat) (Annotated Exp)

data Decl = DeclRec [Annotated Decl]
          | DeclVar Name (Maybe (Annotated QType)) (Annotated Exp)

data Exp = Apply (Annotated Exp) (Annotated Exp)
         | Case (Annotated Exp) [(Annotated Pat, Annotated Exp)]
         | If (Annotated Exp) (Annotated Exp) (Annotated Exp)
         | Lambda (Annotated Pat) (Annotated Exp)
         | Let (Annotated Bind) (Annotated Exp)
         | Lit Lit
         | Pair (Annotated Exp) (Annotated Exp)
         | Unit
         | Var Name
         | Where (Annotated Exp) [Annotated Decl]

data Pat = PatAt Name (Annotated Pat)
         | PatHole
         | PatLit Lit
         | PatPair (Annotated Pat) (Annotated Pat)
         | PatUnit
         | PatVar Name

data Program = Program [Annotated Decl]

data Type = TyApply (Annotated Type) (Annotated Type)
          | TyFun (Annotated Type) (Annotated Type)
          | TyPair (Annotated Type) (Annotated Type)
          | TyUnit
          | TyVar Name
          | TyUni Name -- a unification variable (used for type inference)

data QTyVar = QTyVar Name

data QType = Forall [Annotated QTyVar] (Annotated Type)

data Kind = KindFun (Annotated Kind) (Annotated Kind)
          | KindType
          | KindUni Name -- a unification variable (used for kind inference)
{% endhighlight %}

For the moment let's ignore all the mentions of `Annotated`, which we'll look at in detail separately. It's enough to know that `Annotated a` means `a` with some extra information attached.

It's not important to understand all of the details, but looking at this representation should afford some insight to the basic structure of the Praxis language. We can see that a program (`Program`) is a list of declarations (`Decl`), and that a declaration is either a block of recursive declarations (`DeclRec`) or a variable (`DeclVar`) which has a name, an optional type signature (`QType`), and a defining expression (`Exp`). There are two flavours of types, `Type` for monomorphic types and `QType` for polymorphic types (the 'Q' standing for *quantified*). Finally, patterns (`Pat`) appear in certain expressions, such as `Case` expressions.

To make it easier to talk about, I'll refer to these types collectively as *terms*, so that `Exp` for example is one *category* of term. It's worth pausing here for a moment and appreciating just how intertwined the categories are. We'll see later how this makes even simple operations quite challenging.

<br/>
# Annotations

Now, let's take a look at `Annotated`:

{% highlight haskell %}

data Tag a b = a :< b

inflixl 6 :<

tag :: Functor f => (a -> f c) -> Tag a b -> f (Tag c b)
tag f (a :< x) = (:< x) <$> f a

value :: Functor f => (b -> f c) -> Tag a b -> f (Tag a c)
value f (a :< x) = (a :<) <$> f x

type family Annotation a where
  Annotation Exp      = Annotated Type
  Annotation Pat      = Annotated Type
  Annotation Type     = Annotated Kind
  Annotation a        = Void

type Annotated a = Tag (Source, Maybe (Annotation a)) a

source :: Functor f => (Source -> f Source) -> Annotated a -> f (Annotated a)
source = tag . first

annotation :: Functor f => (Maybe (Annotation a) -> f (Maybe (Annotation a))) -> Annotated a -> f (Annotated a)
annotation = tag . second
{% endhighlight %}

A few things are worth explaining here:

- `Tag` is simply a glorified pair with lenses `tag` and `value` to the first and second components (respectively).
- `Annotated a` is an `a` with a special type of tag, `(Source, Maybe (Annotation a))`. There are two utility lenses `source` and `annotation` to the tag components.
- `Source` (definition omitted) is a range of line and column numbers indicating the location of a substring in the source code. This is used purely for error messages.
- `Annotation a` is a type family which allows us to annotate different categories of terms with different types.

Although every term has a `Source`, only certain categories (`Exp`, `Pat`, and `Type`) have an `Annotation`. The annotation is wrapped in a `Maybe` since it may not be present depending on the stage of compilation[^1]. For example, `Exp` and `Pat` will only have their `Type` annotations set after the type inference stage.

It's worth mentioning that this approach is somewhat similar to *Trees that grow*[^2], but here our annotations only need depend on the category, not the individual constructors within a category. This is a major simplification that has proved to be sufficient for the Praxis compiler.


<br/>
# The Manipulation Problem

Let's look at one sort of manipulation we want to do to our terms: substitutions. To provide a motivated example, we'll look at substitutions in the context of type inference.

The goal of type inference is to set the type annotation of every expression and pattern in the program. This happens in two stages:

1. The first stage (*constraint generation*) traverses the program tree and annotates every expression with a type, however it is allowed to use *type unification variables* (α, β, ...) which each represent a concrete but as-yet unknown type. At the same time *constraints* are generated involving these unification variables, such as `α ~ β`, `α ~ (γ -> Bool)`, and `Integral γ`.

2. The second stage (*constraint solving*) attempts to resolve the unification variables by deduction from the set of generated constraints. When a unification variable is resolved, e.g. `β := (Int -> Bool)`, the unification variable (`β`) is replaced by the resolved type (`Int -> Bool`) throughout the program, and in all the generated constraints. Type inference is completed when all unification variables have been resolved.

Let's consider how we would apply a substitution `α := t` throughout a program. In essence we need to find all the types within the program, and for each of them apply the substitution. So, let's start with a function to apply the substitution to a type:

{% highlight haskell %}
subTyUniInType :: Name -> Type -> Annotated Type -> Annotated Type
subTyUniInType uni resolvedType (a :< ty) = (a :<) $ case ty of
  TyApply x y -> TyApply (subInType x) (subInType y)
  TyFun   x y -> TyFun   (subInType x) (subInType y)
  TyPair  x y -> TyPair  (subInType x) (subInType y)
  TyUnit      -> TyUnit
  TyVar   v   -> TyVar v
  TyUni   n
    | n == uni  -> resolvedType
    | otherwise -> TyUni n
  where subInType = subTyUniInType uni resolvedType
{% endhighlight %}

In other words, for a substitution `α := t`, `subTyUniInType` recursively descends through the type we want to apply the substitution to, leaving the annotation `a` as-is at each level, and replacing every occurence of `TyUni α` with `t`.

So far this may not seem too bad, but now let's write the substitution for programs proper. To do this we will keep in mind that types can appear in two places[^3]: the annotation of an expression and the annotation of a pattern.

{% highlight haskell %}
subTyUniInProgram :: Name -> Type -> Annotated Program -> Annotated Program
subTyUniInProgram uni resolvedType (a :< program) = (a :<) $ case program of
  Program decls -> Program (map subInDecl decls)
  where subInDecl = subTyUniInDecl uni resolvedType

subTyUniInDecl :: Name -> Type -> Annotated Decl -> Annotated Decl
subTyUniInDecl uni resolvedType (a :< decl) = (a :<) $ case decl of
  DeclRec decls              -> DeclRec (map subInDecl decls)
  DeclVar name signature exp -> DeclVar name signature (subInExp exp)
  where subInDecl = subTyUniInDecl uni resolvedType
        subInExp = subTyUniInExp uni resolvedType

subTyUniInExp :: Name -> Type -> Annotated Exp -> Annotated Exp
subTyUniInExp uni resolvedType (a :< exp) = (subInAnnotation a :<) $ case exp of
  Apply x y    -> Apply (subInExp x) (subInExp y)
  Case  x as   -> Case  (subInExp x) (map (\(p, y) -> (subInPat p, subInExp y)) as)
  If    x y z  -> If (subInExp x) (subInExp y) (subInExp z)
  Let   b x    -> Let (subInBind b) (subInExp x)
  Lit   l      -> Lit l
  Pair  x y    -> Pair (subInExp x) (subInExp y)
  Unit         -> Unit
  Var   v      -> Var v
  Where x ds   -> Where (subInExp x) (map subInDecl ds)
  where subInExp = subTyUniInExp uni resolvedType
        subInPat = subTyUniInPat uni resolvedType
        subInType = subTyUniInType uni resolvedType
        subInBind (a :< Bind p x) = (a :< Bind (subInPat p) (subInExp x))
        subInAnnotation (src, Just ty) = (src, Just (subInType ty))

subTyUniInPat :: Name -> Type -> Annotated Pat -> Annotated Pat
subTyUniInPat uni resolvedType (a :< pat) = (subInAnnotation a :<) $ case pat of
  PatAt   x y -> PatAt (subInPat x) (subInPat y)
  PatHole     -> PatHole
  PatLit  l   -> PatLit l
  PatPair x y -> PatPair (subInPat x) (subInPat y)
  PatUnit     -> PatUnit
  PatVar  v   -> PatVar v
  where subInPat = subTyUniInPat uni resolvedType
        subInType = subTyUniInType uni resolvedType
        subInAnnotation (src, Just ty) = (src, Just (subInType ty))
{% endhighlight %}

Now what if I told you that in addition to type inference, there is also kind inference, which operates in a similar way but using *kind unification variables*. For substitutions of these we'll need a similar set of functions `subKindUniInKind`, `subKindUniInProgram`, `subKindUniInDecl`, `subKindUniInExp`, `subKindUniInPat`, and `subKindUniInType`.

So our desire to implement just one simple manipulation results in a quadratic explosion of tedious category-specific functions. This many functions is not only a pain to write, it's also exceedingly easy to forget about a recursive case or forget to substite through an annotation. Suffice it to say this does not spark joy.

You may want to pause here and think if there are any alternatives that would let us solve our substitution requirement more easily. In the following sections we'll see that this can be done, and it can be done in a generic way which lets us perform countless other manipulations in just a handful of lines.


<br/>
# Introspection

The key idea is we need some way to abstract over the category of a term. Then, instead of needing functions for every category (i.e. from `Exp` to `Exp`, and from `Pat` to `Pat`, and so on), we can have one single function from term to term.

One simple solution is to have a `Term` type which is a union over all the categories, say:

{% highlight haskell %}
data Term = TermBind (Annotated Bind)
          | TermDecl (Annotated Decl)
          | TermExp (Annotated Exp)
          | TermPat (Annotated Pat)
          | TermProgram (Annotated Program)
          | TermType (Annotated Type)
          | TermQTyVar (Annotated QTyVar)
          | TermQType (Annotated QType)
          | TermKind (Annotated Kind)
{% endhighlight %}

This works, but we can do better. A weakness of this approach is that we lose the ability to express at the type level that a transformation preserves the category.

Instead, the approach used in the Praxis compiler is a `Term` typeclass. Then a category-preserving transformation is typed as `Term a => a -> a`. To implement the `Term` typeclass, we leverage GADTs:

{% highlight haskell %}
{-# LANGUAGE GADTs                     #-}

class Term a where
  witness :: I a
  -- To be continued...

data I a where
  IBind    :: I Bind
  IDecl    :: I Decl
  IExp     :: I Exp
  IPat     :: I Pat
  IProgram :: I Program
  IType    :: I Type
  IQType   :: I QType
  IQTyVar  :: I QTyVar
  IKind    :: I Kind

instance Term Bind where
  witness = IBind

instance Term Decl where
  witness = IDecl

instance Term Exp where
  witness = IExp

-- etc ...

{% endhighlight %}

This construction lets us perform case distinctions on the category of an arbitrary term. To see what this looks like practice, let's compare it to the `Term` type approach for lifting a function over `Exp` to a function over terms:

{% highlight haskell %}
-- Term type approach
liftExp :: (Exp -> Exp) -> Term -> Term
liftExp f x = case x of
  TermExp e -> TermExp (f e)
  _         -> x
{% endhighlight %}

{% highlight haskell %}
{-# LANGUAGE ScopedTypeVariables       #-}

-- Term typeclass approach
liftExp :: forall a. Term a => (Exp -> Exp) -> a -> a
liftExp x = case (witness :: I a) of
  IExp -> f x
  _    -> x
{% endhighlight %}

There are a few subtleties with the typeclass solution:
- The `a` in `witness :: I a` refers to the type of `x`, thanks to the *ScopedTypeVariables* extension.
- When the `IExp` pattern matches, Haskell deduces that `a ~ Exp` since `IExp :: I Exp`. This means we get to use `x :: Exp` in the body `f x`.

As alluded to earlier, here the typeclass approach gives us a type-checked guarantee that the category is preserved.


<br/>
# Traversals

An addition to the above, we require terms to implement traverse-like semantics. This will let us encapsulate the recursive structure of terms, allowing us to then succinctly write manipulations like substitutions.

{% highlight haskell %}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE TypeOperators             #-}

type Termformer f = forall a. Term a => Annotated a -> f (Annotated a)

class Term a where
  witness :: I a
  recurseTerm :: Applicative f => Termformer f -> a -> f a
  recurseAnnotation :: (Term a, Applicative f) => I a -> Termformer f -> Annotation a -> f (Annotation a)
{% endhighlight %}

We've added two functions:
- `recurseTerm` applies an applicative action to every subterm (of an unannotated term).
- `recurseAnnotation` applies an applicative action to every subterm in an annotation. This takes an additional `I a` argument which is needed to unambiguously determine `a` (since `Annotation` is non-injective).

These can be combined into a single `recurse` function which performs both actions:

{% highlight haskell %}
recurse :: forall a f. (Term a, Applicative f) => Termformer f -> Annotated a -> f (Annotated a)
recurse f ((src, ann) :< x) = (\ann x -> (src, ann) :< x) <$> traverse (recurseAnnotation (witness :: I a) f) ann <*> recurseTerm f x
{% endhighlight %}


Although the types of `recurseTerm` and `recurseAnnotation` may look quite scary, the implementations are quite straightforward in practice, following a similar pattern to a `Traversable`:

{% highlight haskell %}
-- Implementation of recurseAnnotation for terms with a Void annotation
trivial :: (Annotation a ~ Void, Term a, Applicative f) => I a -> Termformer f -> Annotation a -> f (Annotation a)
trivial _ _ = absurd

-- Helper for traversing a pair
pair :: (Term a, Term b) => Applicative f => Termformer f -> (Annotated a, Annotated b) -> f (Annotated a, Annotated b)
pair f (a, b) = (,) <$> f a <*> f b

-- Helper for traversing a list of pairs
pairs :: (Term a, Term b) => Applicative f => Termformer f -> [(Annotated a, Annotated b)] -> f [(Annotated a, Annotated b)]
pairs f = traverse (pair f)

instance Term Bind where
  witness = IBind
  recurseTerm f x = case x of
    Bind a b -> Bind <$> f a <*> f b
  recurseAnnotation = trivial

instance Term Decl where
  witness = IDecl
  recurseTerm f x = case x of
    DeclRec ds      -> DeclRec <$> traverse f ds
    DeclVar n t e   -> DeclVar n <$> traverse f t <*> f e
  recurseAnnotation = trivial

instance Term Exp where
  witness = IExp
  recurseTerm f x = case x of
    Apply a b       -> Apply <$> f a <*> f b
    Case a as       -> Case <$> f a <*> pairs f as
    If a b c        -> If <$> f a <*> f b <*> f c
    Lambda a b      -> Lambda <$> f a <*> f b
    Let a b         -> Let <$> f a <*> f b
    Lit l           -> pure (Lit l)
    Pair a b        -> Pair <$> f a <*> f b
    Unit            -> pure Unit
    Var n           -> pure (Var n)
    Where a bs      -> Where <$> f a <*> traverse f bs
  recurseAnnotation _ f x = f x -- Apply f to the Type annotation

-- etc ...
{% endhighlight %}


<br/>
# Manipulations Revisited

Finally, we can leverage the completed `Term` typeclass to write a generic substitution, using `Identity` as the applicative:

{% highlight haskell %}
sub :: forall a. Term a => (forall b. Term b => Annotated b -> Maybe (Annotated b)) -> Annotated a -> Annotated a
sub f x = case f x of
  Just y  -> y
  Nothing -> runIdentity $ recurse (Identity . sub f) x
{% endhighlight %}

For the original problem of wanting to substitute a type unification variable, we can call `sub` as follows:

{% highlight haskell %}
subTyUni :: Name -> Annotated Type -> Annotated a -> Annotated a
subTyUni uni resolvedType = sub f where
  f :: forall b. Term b => Annotated b -> Maybe (Annotated b)
  f x = case (witness :: I b) of
    IType -> case x of
      (_ :< TyUni n)
        | n == uni   -> Just resolvedType
      _              -> Nothing
    _     -> Nothing
{% endhighlight %}

We can write other manipulations too, for example summing over a monoidal action using `Const` as the applicative:

{% highlight haskell %}
sum :: forall a m. (Monoid m, Term a) => (forall b. Term b => b -> m) -> Annotated a -> m
sum f x = f (view value x) <> (getConst $ recurse (Const . sum f) x)
{% endhighlight %}

We can use this to check if a term contains any type unification variables, which tells us whether or not type inference is completed:

{% highlight haskell %}
containsTyUni :: Term a => Annotated a -> Bool
containsTyUni x = getAny (sum f x) where
  f :: forall b. Term b => b -> Any
  f x = case (witness :: I b) of
    IType -> case x of
      TyUni n -> Any True
      _       -> Any False
    _     -> Any False
{% endhighlight %}

That's all there is to know about the Praxis AST. May your trees by joyful :)

<br/>


---

[^1]: Instead of an optional annotation, early versions of the compiler included an additional `Stage` enum in the `Annotation` family. However this was removed as it had marginal benefit and made introspection significantly more complex.
[^2]: [Trees that grow][trees-that-grow]
[^3]: Types may also be present in `DeclVar`, but this is ignored for simplicity (and since the type is a user-provided type signature it won't contain any unification variables in practice).

[Term.hs]: https://github.com/davidcoates/praxis/blob/master/src/Term.hs
[trees-that-grow]: https://simon.peytonjones.org/trees-that-grow/

