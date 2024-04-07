---
layout: post
title:  "Joyful Annotated ASTs"
---
You’ll find this post in your `_posts` directory. Go ahead and edit it and re-build the site to see your changes. You can rebuild the site in many different ways, but the most common way is to run `jekyll serve`, which launches a web server and auto-regenerates your site when a file is updated.

Jekyll requires blog post files to be named according to the following format:

`YEAR-MONTH-DAY-title.MARKUP`

Where `YEAR` is a four-digit number, `MONTH` and `DAY` are both two-digit numbers, and `MARKUP` is the file extension representing the format used in the file. After that, include the necessary front matter. Take a look at the source for this post to get an idea about how it works.

Jekyll also offers powerful support for code snippets:

{% highlight haskell %}
type Name = String

data Bind = Bind (Annotated Pat) (Annotated Exp)
  deriving (Eq, Ord)

data Decl = DeclRec [Annotated Decl]
          | DeclTerm Name (Maybe (Annotated QType)) (Annotated Exp)
  deriving (Eq, Ord)

data Exp = Apply (Annotated Exp) (Annotated Exp)
         | Case (Annotated Exp) [(Annotated Pat, Annotated Exp)]
         | If (Annotated Exp) (Annotated Exp) (Annotated Exp)
         | Lambda (Annotated Pat) (Annotated Exp)
         | Let (Annotated Bind) (Annotated Exp)
         | Pair (Annotated Exp) (Annotated Exp)
         | Unit
         | Var Name
         | Where (Annotated Exp) [Annotated Decl]
  deriving (Eq, Ord)

data Pat = PatAt Name (Annotated Pat)
         | PatHole
         | PatLit Lit
         | PatPair (Annotated Pat) (Annotated Pat)
         | PatUnit
         | PatVar Name
  deriving (Eq, Ord)

data Program = Program [Annotated Decl]
  deriving (Eq, Ord)

data Type = TyApply (Annotated Type) (Annotated Type)
          | TyFun (Annotated Type) (Annotated Type)
          | TyPair (Annotated Type) (Annotated Type)
          | TyUnit
          | TyVar Name
  deriving (Eq, Ord)

data QTyVar = QTyVar Name
  deriving (Eq, Ord)

data QType = Forall [Annotated QTyVar] (Annotated Type)
  deriving (Eq, Ord)

data Kind = KindType
          | KindFun (Annotated Kind) (Annotated Kind)
{% endhighlight %}

Check out the [Jekyll docs][jekyll-docs] for more info on how to get the most out of Jekyll. File all bugs/feature requests at [Jekyll’s GitHub repo][jekyll-gh]. If you have questions, you can ask them on [Jekyll Talk][jekyll-talk].

[jekyll-docs]: https://jekyllrb.com/docs/home
[jekyll-gh]:   https://github.com/jekyll/jekyll
[jekyll-talk]: https://talk.jekyllrb.com/
