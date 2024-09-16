---
layout: post
title:  "The Praxis Type System"
tags: praxis type-system affine-types linear-types
comments: true
---

*This post explains the main distinguishing features of the Praxis language's type system.*

---
<br/>

# Affine Types

Praxis has a type system which includes *affine types*. A value of an affine type is a value that must be used at most once. This is closely related to *linear types* whose values must be used exactly once. Both affine and linear type systems allow the use of destructive updates whilst maintaining purity. This allows us to combine the efficiency of strict mutable data structures (like an imperative language) with the reasoning power of immutability (like a pure functional language).

Let's start by looking at an example of an affine type in Praxis, a dynamic array:

```
new : forall a. (USize -> a, USize) -> Array a
set : forall a. (Array a, USize, a) -> Array a
operator (_ [ _ ] <- _) = set
```

```
xs = new (const False, 3) -- [False, False, False]
ys = xs[0] <- True -- [True, False, False]
```


A couple of things to note:
* `new` and `set` are functions (with implementations omitted) for creating and updating an array, respectively. In Praxis we tend to prefer uncurried functions over curried functions, for reasons that will be explained later on.
* `operator` is used to define a mixfix operator for `set`. Praxis has a unique system for defining associativity and precedence of user-defined operators, but we can ignore that for now.

The fact that `Array` is an affine type means we can interpret the latter snippet in two equivalent ways:
1. `xs` is a *mutable* array, and when it is destructively updated it is given a new name `ys`.
2. `xs` and `ys` are both *immutable* arrays. We can treat `xs` as immutable because the only way to observe a mutation of `xs` would be to read it after the update. This is not possible since that would mean using `xs` more than once.

<br/>
# References

Continuing with arrays, we naturally want to write a `get` function to read an element of an array at a given index. We might naively think of a function with the following signature:

```
get : (Array a, USize) -> a
operator (_ [ _ ]) = get
```

```
y0 = ys[0]
y1 = ys[1] -- Not allowed! ys has already been used.
```

There is a big problem here: After the first `get` call we have used `ys`, and so can't use it again. An array that you can only access once is not very useful! To remedy this, Praxis has *references*, which allow unlimited read-only access.

References are created using a *read* expression, where `read x in e` means to take the variable `x` as a reference within the expression body `e`. This comes with a few rules:

1. **Reference Type**  
If ordinarily `x : a`, then `x` is a reference with type `&l a` within `e`, where `&l` is a unique compiler-generated *reference label*.
   - *Note: References are not affine, so `x` may occur arbitrarily many times within `e`.*
2. **Reference Lifetime**  
The reference bound to `x` must not outlive the scope of `e`. Specifically, the reference label `&l` must not appear anywhere in the type of `e`.
   - *For example, neither `read x in x` nor `read x in (x, y)` are allowed.*
3. **Reads Before Use**  
Multiple read expressions of `x` are allowed, but none may occur after `x` is used.
4. **Syntax Sugar**  
When using `read` for a function call, like `read x in f x`, the syntax sugar `f &x` can be used. This also applies through tuples, so `read x in f (x, e)` can be written `f (&x, e)`.

Now using references and reads, we have:

```
get : forall &r a. (&r Array a, USize) -> &r a
operator (_ [ _ ]) = get
```

```
y0 = &ys[0] -- read ys in get (ys, 0)
y1 = &ys[1] -- read ys in get (ys, 1)
```

Here `&r` is a *reference variable*, which abstracts over *reference labels*. Note that applications of `&r` are right-associative, so `&r Array a` means `&r (Array a)`.

Since `get` is given a reference to an array, the element returned is also a reference. The same reference label is used to indicate that the lifetime of the element is coupled to the lifetime of the array. However, a reference of a non-affine type simplifies to the type itself. So in this example the return type `&r Bool` simplifies to `Bool`.


<br/>
# Comparisons with Rust

As a brief aside, for those familiar with Rust you may notice there is a similarity here to Rust's model of ownership and borrowing. One can think of the affine restriction in Praxis as being simlar to *ownership* in Rust, with only *immutable borrowing* allowed, and with reference labels analagous to *lifetime parameters*.

These concepts tend to have simpler but more restrictive semantics in Praxis compared to their Rust counterparts. This is because they are checked solely through the type checker as opposed to having a separate stage like Rust's borrow checker.

<br/>
# Views


Returning back to our example of arrays, let's take a look at what a "map" function looks like.

In fact, there are two ways we could think of typing map, one using values and the other using references:

```
map_value : forall a b. -> (a -> b) -> Array a -> Array b
```

```
map_reference : forall &r a b. -> (&r a -> b) ->  &r Array a -> Array b
```

These are both useful, for different situations:
* `map_value` takes ownership of the input array and this allows it to apply a transformation which takes ownership of the elements. In addition, the implementation may (subject to the sizes and alignments of `a` and `b`) reuse the underlying storage of the input array for the output array.
* `map_reference` operates on a reference to an array and so it is only allowed to apply a transformation which operates on references to the elements.


There are many other functions which, similar to map, could be written either using values or using references. Thankfully, Praxis provides a way to unify the two forms, using *views*:

```
map : forall ?v a b. -> (?v a -> b) ->  ?v Array a -> Array b
```

Here `?v` is a *view variable*, which can be either a reference or the *identity view* `@`, where `@ a ~ a`. Note that as with references, views are right-associative.

Views are a powerful tool to abstract over mutability; Instead of having to write a mutable and non-mutable version of the same function or structure (e.g. an iterator), we can write one unifying version using views.


<br/>
# Pattern Matching

Let's now take a break from arrays, to take a look at an implementation of `map` for a list:

```
data List a = Nil () | Cons (a, List a)

map : forall ?v a b. -> (?v a -> b) ->  ?v List a -> List b
map f = cases
  Nil ()       -> Nil ()
  Cons (x, xs) -> Cons (f x, map f xs)
```

*Note: `cases` is a function variant of `case`, i.e. `\x -> case x of ...`.*

If you are familiar with functional languages, then you should be able to see how `map` can be typed as:  
`forall a b. (a -> b) -> List a -> List b`.

The magic here is that `map` can *also* be typed as:  
`forall &r a b. (&r a -> b) -> &r List a -> List b`.

And moreover, *also* as the (most general) type:  
`forall ?v a b. (?v a -> b) -> ?v List a -> List b`.

The reason this works is because pattern matching plays nicely with views and references. When you pattern match a value, reference, or view, the components are made available as values, references, or views (respectively).

For a simpler example, consider pairs. When matched against the pattern `(x, y)`:
* A pair with type `(a, b)` yields `x : a` and `y : b`.
* A reference to a pair with type `&r (a, b)` yields `x : &r a` and `y : &r b`.
* A view of a pair with type `?v (a, b)` yields `x : ?v a` and `y : ?v b`.


<br/>
# Clone, Copy, Dispose, Capture

The type system contains four special constraints used to enforce affine semantics:

* `Clone a` requires `clone : forall &r. &r a -> a`. This is an explicit copy which affine types may or may not implement. It can have a trivial implementation (a bit-wise copy).

* `Copy a` requires `Clone a` and is the exact opposite of affine. When a variable with a `Copy` type is used more than once, it will be implicitly copied using `clone`.

* `Dispose a` requires `dispose : a -> ()`. This is invoked when an unused value goes out of scope. It can have a trivial implemtnation (a no-op). Currently all types in Praxis automatically implement `Dispose`, but the implementation may be overridden. In theory, *linear* types could be trivially added to Praxis by allowing `Dispose` to be unimplemented for some types.

* `Capture a` means that a value of type `a` may be safely captured in a function closure. It requires both `Copy a` and that `a` does not contain any references or views.


<br/>
# Closures

We'll finish with some notes on function closures.

Closures have a rather harsh requirement that captured variables must satisfy the aforementioned `Capture` constraint.

The reason is to keep function types simple:
* Captured variables must satisfy `Copy` so that all function types satisfy `Copy`.
* Captured variables must not include references, otherwise closures could be used to smuggle references out of `read`.

This explains why functions in Praxis are often uncurried - to avoid unnecessary closures that could fall foul of `Capture`.

As a final note, this preference against currying leads us to a different applicative operator, which corresponds neatly to the notion of a cartesian product:

```
prod : forall ?v ?w a b f | Cartesian f. (?v f a, ?w f b) -> f (?v a, ?w b)

operator (_ <*> _) = prod
```

<br/>

---

*For a formal specification of the type system, [see this post]({% post_url 2024-09-03-praxis-type-system-formal-spec %}).*


