* Tasks
** DONE digest [[http://orgmode.org/worg/org-tutorials/orgtutorial_dto.html][org-mode tutorial]]
** DONE integrate [[https://gist.github.com/reetinder/4022989][literate haskell in org-mode]] (does not work, too old?)
** DONE describe the data Void <--> forall a . a isomorphism
** TODO open interpretation, e.g. circuit as Haskell function or VHDL module
** TODO rewind to the start of the presentation (block comments)

* Preliminaries

HOWTO: literate haskell in org-mode:
https://gist.github.com/reetinder/4022989

Highlight in org-mode:
(setq org-src-fontify-natively t)

* Finally-tagless representation

Let's consider the "finally" thingy first.

represent AST nodes with functions alone

our expression is "(3 + 4^2) * 2"

> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances
>   , GeneralizedNewtypeDeriving, MultiParamTypeClasses
>   , KindSignatures, GADTs, StandaloneDeriving #-}
> {-# LANGUAGE RankNTypes, LambdaCase, EmptyCase #-}
> import Prelude hiding ((**))
> p ** n = product $ replicate (fromInteger n) (toInteger p)

> -- {-
> plus, times, power :: Integer -> Integer -> Integer
> (plus, times, power) = ((+), (*), (**))

> infixl 8 `power`
> infixl 7 `times`
> infixl 6 `plus`

Constants are just themselves (for now)

Now manually transcribe our expression

> expr = (3 `plus` (4 `power` 2)) `times` 2

clearly we can just ask GHCi for the result:

*Main> expr
38

We can think of our AST being encoded by functions and the "evaluator"
just the identity:

> interpr'Integer = id

*Main> interpr'Integer expr
38

A very strange interpreter!

> -- -}

Background: 'invented' by Reynolds in the 1970's.

** First refinement of the idea

Let's make this a bit more useful.

> {-
> plus, times, power :: repr -> repr -> repr
> (plus, times, power) = (undefined, undefined, undefined)
> -}

Expr stays the same:

> -- expr = (3 `plus` (4 `power` 2)) `times` (2 :: Integer)

But of course evaluating it does not make lot of a sense:

*Main> expr
 *** Exception: Prelude.undefined

The representation type is so general it is totally useless!
So increase its utility by _restricting generality_.

Define a type class Arith:

> {-
> class Arith repr where
>   plus, times, power :: repr -> repr -> repr

and give it our first implementation for repr ~ Integer:

> instance Arith Integer where
>   plus = (+)
>   times = (*)
>   power = (**)

*Main> expr :: Integer
38

> -}

** Adding another interpretation

Just like the *evaluation* semantics above we can add a printing semantics
by overloading our vocabulary to yield a string representation.

But for this to work we cannot reuse our nullary Integers any more,
we need an injection into the representation:

> {-
> class Arith repr where
>   lit :: Integer -> repr
>   plus, times, power :: repr -> repr -> repr


> instance Arith String where
>   lit = show
>   plus a b = "(" ++ a ++ " + " ++ b ++ ")"
>   times a b = "(" ++ a ++ " * " ++ b ++ ")" -- dito
>   power a b = "(" ++ a ++ " ** " ++ b ++ ")" -- dito

> expr :: Arith a => a
> expr = (lit 3 `plus` (lit 4 `power` lit 2)) `times` lit 2

*Main> expr :: String
"((3 + (4 ** 2)) * 2)"


By adding a new type instance we can reinterpret our representation
in arbitrarily many ways.

Let's consider a pretty printer which passes context, i.e. the current
precedence level to eliminate superfluous parentheses:

#+begin_src literate-haskell
> --{-
> newtype Prec = P (Int -> String)

> instance Show Prec where
>   show (P f) = f 0

> instance Arith Prec where
>   lit i = P $ const $ show i
>   plus (P a) (P b) = P $ \p -> inner `parenIf` p > 6
>     where inner = a 6 ++ " + " ++ b 6
>   times (P a) (P b) = P $ \p -> inner `parenIf` p > 7
>     where inner = a 7 ++ " * " ++ b 7
>   power (P a) (P b) = P $ \p -> inner `parenIf` p > 8
>     where inner = a 8 ++ " ^ " ++ b 8

> parenIf s cond = if cond then "(" ++ s ++ ")" else s
> infix 1 `parenIf`
> -- -}
> -}
#+end_src

*Main> expr :: Prec
(3 + 4 ^ 2) * 2

The general pattern for passing in contextual information is by
employing a (newtype of a) function type for representation type.

** An Analysis

We could come up with diagrams or some other algorithm, e.g. an analysis:

Count operators in the expression tree

> newtype Count = C Int deriving (Num, Show)

> {-
> instance Arith Count where
>   lit _ = 0
>   plus (C a) (C b) = C (a + b + 1)
>   times = plus
>   power = plus
> -}

** Interlude

A "final" type

> type TotallyPoly = forall a . a

can be considered 100% entropy, while

> data Void -- no constructors

an "initial" type as 0% knowledge.

They are the same thing, as we can convert one to the other:

> p2v :: TotallyPoly -> Void
> p2v a = a

and back:

> v2p :: Void -> TotallyPoly
> v2p = \case {}

** Adding a Type System

So far we could only express terms in the numeric fragment,
let's add a conditional fragment.

Here we have a second data domain, the booleans:

> {-
> class Arith n => Cond n b where
>   cmp :: n -> n -> b
>   if' :: b -> x -> x -> (b, x)

> exprB :: (Cond a b) => (b, a)
> exprB = if' (lit 3 `cmp` (lit 4 :: Arith a => a)) expr (expr `plus` lit 1)
> -}

This results in tons of ambiguities, so we might try another approach:

Establish a little universe of types that parametrises the representation:

> class Arith' (repr :: * -> *) where
>   lit' :: Integer -> repr Integer
>   plus' :: repr Integer -> repr Integer -> repr Integer

> class Cond (repr :: * -> *) where
>   cmp :: repr Integer -> repr Integer -> repr Bool
>   if' :: repr Bool -> repr a -> repr a -> repr a

I re-(ab)used the Haskell types as our universe inhabitants here.

> expr' :: Arith' repr => repr Integer
> expr' = lit' 3 `plus'` lit' 5
> exprB :: (Arith' repr, Cond repr) => repr Integer
> exprB = if' (lit' 3 `cmp` lit' 4) expr' (expr' `plus'` lit' 1)

*** DONE : Add implementations

We can now interpret those terms in a bi-typed domain.

#+begin_src literate-haskell
> data E ty where
>   EI :: Integer -> E Integer
>   EB :: Bool -> E Bool

> deriving instance Show (E ty)

> instance Arith' E where
>   lit' = EI
>   plus' (EI a) (EI b) = EI $ a + b

> instance Cond E where
>   cmp (EI a) (EI b) = EB $ a == b
>   if' (EB c) th el = if c then th else el
#+end_src

Since the parameter (to =repr=) is always determined by the method signature,
the interpreter need not expect other constructors than what is stated above.
Our interpreter is /total/.

** Deriving a GADT mechanically

/GADTs/ are generalisations of ADTs (algebraic data types, sums-of-product types,
polynomial datatypes), whose constructors may have specialized result types.

Next we shall copy down all above class methods into our =Expr= GADT by
replacing =repr= by =Expr=:

> data Expr :: * -> * where
>   Lit :: Integer -> Expr Integer
>   Plus :: Expr Integer -> Expr Integer -> Expr Integer
>   Cmp :: Expr Integer -> Expr Integer -> Expr Bool
>   If :: Expr Bool -> Expr a -> Expr a -> Expr a

> deriving instance Show (Expr u)

/Note that we had to join the methods from two classes =Arith'= and =Cond= in one data type./

Then we can trivially make Expr an instance of the above classes:

*** Instances for GADT

#+begin_src literate-haskell
> instance Arith' Expr where
>   lit' = Lit
>   plus' = Plus
>
> instance Cond Expr where
>   cmp = Cmp
>   if' = If
#+end_src

*** Reifying the final-tagless form

Clearly we can convert any =Expr= to the final form by writing a conventional
interpreter:

#+begin_src literate-haskell
> expr2final :: (Arith' repr, Cond repr) => Expr a -> repr a
> expr2final (Lit i) = lit' i
> expr2final (e `Plus` e') = expr2final e `plus'` expr2final e'
> expr2final (e `Cmp` e') = expr2final e `cmp` expr2final e'
> expr2final (If c e e') = if' (expr2final c) (expr2final e) (expr2final e')
#+end_src

This closes our proof of isomorphism between GADTs and finally-tagless formulation.

* Summary: Pluripotent Representation

By using "lower-case" indentifiers we can define ASTs abstractly
with powerful potential specialisations. These do not stress the
type system and offer all the benefits of GADTs.

As such it can smoothly vary between shallow and deep embedding
of EDSLs and blur those terms. Lastly the isomorphism to initial
form ensures that one can break out any time and return back,
if wanted.

While some techniques are more awkward to encode in finally tagless
form, others arguably lend themselves to /cleaner/ (e.g. context-free)
implementations. This explicit passing of context suggests simple
/attribute grammar/ inherited attributes.

The finally-tagless representation has been suggested as an elegant
solution to the /expression problem/. The vocabulary is extensible
by adding new typeclasses, and new interpretations can be added in
the orthogonal dimension. Haskell's type system performs the bookkeeping
of arising constraints. Contrast this to the machinery of the /á la carte/
approach.

For an in-depth account of all the known techniques please refer
to [[http://okmij.org/ftp/tagless-final/course/#lecture][Oleg's lecture notes]].

[[http://www.haskellforall.com/2012/06/gadts.html][Tekmo's blog post]] (and related discussion) is great too.

* Closing Notes

A germ of these ideas already existed in

ghci>:t 3
3 :: Num a => a

and also in the monadic combinators =return= and ~(>>=)~, though
these only allow really limited programs to be written.

Also consider the analogy of
  + encoding information in data (RAM)
  + encode information in the control flow (PC).
